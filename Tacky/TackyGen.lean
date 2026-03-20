import AST.AST
import Tacky.Tacky
import Semantics.SymbolTable

/-
  IR generation pass: converts AST.Program → Tacky.Program.

  Chapter 18 additions:
    - `GenState` gains `typeTable` (struct/union layout map) so that `emitExp`
      can look up member offsets and types for `Dot`/`Arrow` expressions.
    - `emitExp` handles `Dot(base, member)` and `Arrow(ptr, member)`:
        Scalar member (Dot):   `CopyFromOffset(baseName, offset, dst)`
        Scalar member (Arrow): `AddPtr(ptr, 1, offset, addrTmp); Load(addrTmp, dst)`
        Aggregate member:      copy each scalar leaf via `emitAggregateCopyAt`/`emitAggregateLoadAt`
    - `Assignment(Dot ...)` and `Assignment(Arrow ...)` store into member fields.
    - `AddrOf(Dot ...)` and `AddrOf(Arrow ...)` compute the member address via `emitLvalAddr`.
    - `PostfixIncr`/`PostfixDecr` on Dot/Arrow members use load-increment-store via `emitLvalAddr`.
    - `BlockItem.SD` (struct/union declarations in blocks) passes through as no instructions.
    - `emitProgram` accepts a `TypeTable` parameter and handles `StructDecl` top-levels.

  Chapter 13 additions:
    - `emitExp` handles `Constant(.ConstDouble f)`: allocates a fresh name
      `.LfpC.N` for the float constant, records it in `floatConsts`, and
      returns `Val.Var ".LfpC.N"` (the constant lives in read-only data).
    - `Cast` now handles all conversions to/from `Double`:
        Int → Double  : `IntToDouble`
        Double → Int  : `DoubleToInt`
        UInt → Double : `UIntToDouble`
        Double → UInt : `DoubleToUInt`
        Long → Double : `IntToDouble` (via cvtsi2sdq — reused, CodeGen distinguishes by type)
        Double → Long : `DoubleToInt` (via cvttsd2siq — reused)
        ULong → Double: `ULongToDouble`
        Double → ULong: `DoubleToULong`
    - `GenState` gains `floatConsts` (name → value) and `needsNegZero`.
    - `emitProgram` returns `(Program, typeEnv, floatConsts, needsNegZero)`.

  Chapter 11 additions:
    - `emitExp` returns `(Val × AST.Typ × List Instruction)` so that each
      expression's type is available for inserting correct assembly instructions.
    - `makeTemporary` takes the type of the temporary being created and records
      it in the `typeEnv` map (name → type) threaded through generation.
    - Handles `AST.Exp.Cast`: emits `SignExtend` (Int→Long) or `Truncate`
      (Long→Int) as appropriate.
    - Handles typed constants: `ConstInt` → type `Int`, `ConstLong` → type `Long`.
    - `emitProgram` returns `(Program × List (String × AST.Typ))`, the second
      component being the `typeEnv` that the Driver uses to build the backend
      symbol table.
    - `StaticVariable` top-level items now carry the variable's AST.Typ.
    - The counter is global across all functions (unchanged).
-/

namespace Tacky

-- ---------------------------------------------------------------------------
-- Generation monad
-- ---------------------------------------------------------------------------

/-- State threaded through IR generation.
    `counter`:    unique name counter (same as before).
    `typeEnv`:    maps every temporary variable name (e.g. `"tmp.5"`) to its
                  scalar type, so the Driver can build the backend symbol table.
    `floatConsts`: (Chapter 13) maps float-constant labels (e.g. `".LfpC.5"`)
                  to their float values, for emission as read-only static data.
    `needsNegZero`: (Chapter 13) true when a double Negate instruction has been
                  emitted; the Driver will add the `.Lneg_zero` constant.
    `strConsts`:  (Chapter 16) maps string-literal labels (e.g. `".Lstr.5"`)
                  to their string contents, for emission as read-only `.rodata`.
    `typeTable`:  (Chapter 18) struct/union tag → layout, for member offset lookups. -/
private structure GenState where
  counter      : Nat
  typeEnv      : List (String × AST.Typ)
  floatConsts  : List (String × Float)
  needsNegZero : Bool
  strConsts    : List (String × String)  -- Chapter 16: label → raw string content
  typeTable    : Semantics.TypeTable     -- Chapter 18: struct/union layouts

private abbrev GenM := StateM GenState

/-- Allocate a fresh temporary of the given type, recording it in typeEnv. -/
private def makeTemporary (t : AST.Typ) : GenM String := do
  let s ← get
  let name := s!"tmp.{s.counter}"
  modify (fun st => { st with counter := st.counter + 1, typeEnv := (name, t) :: st.typeEnv })
  return name

private def makeLabel (base : String) : GenM String := do
  let s ← get
  -- Use s.counter (the PRE-modification value) as the unique suffix.
  -- Importantly, do NOT subtract 1: that was an off-by-one bug where counter
  -- values 0 and 1 both produced the label "base.0" (since Nat 0-1 = 0).
  modify (fun st => { st with counter := st.counter + 1 })
  return s!"{base}.{s.counter}"

/-- (Chapter 13) Intern a float constant: allocate a unique read-only label.
    Returns the label name to use as `Val.Var label`. -/
private def internFloat (f : Float) : GenM String := do
  let s ← get
  let label := s!".LfpC.{s.counter}"
  modify (fun st => { st with counter := st.counter + 1,
                               typeEnv := (label, .Double) :: st.typeEnv,
                               floatConsts := (label, f) :: st.floatConsts })
  return label

/-- (Chapter 16) Intern a string literal: allocate a unique read-only label.
    The string content (without null terminator) is stored in `strConsts`.
    Returns the label name to use as `Val.Var label`.
    The label represents an Array(Char, n+1) in `.rodata`; when its address is
    taken (via AddrOf), it yields `Pointer(Char)` — a C string pointer. -/
private def internString (s : String) : GenM String := do
  let st ← get
  let label := s!".Lstr.{st.counter}"
  let arrTyp := AST.Typ.Array .Char (s.length + 1)
  modify (fun state => { state with
    counter   := state.counter + 1,
    typeEnv   := (label, arrTyp) :: state.typeEnv,
    strConsts := (label, s) :: state.strConsts })
  return label

-- ---------------------------------------------------------------------------
-- Compound-assignment helpers (extra credit Chapter 14)
-- ---------------------------------------------------------------------------

/-- True iff `expr` contains a `Dereference ptrExp` sub-expression at any depth,
    looking through `Cast` wrappers.  Used to detect the compound-assignment
    pattern `*f() += e` which the parser desugars to
    `Assignment (Dereference f()) (Binary op (Dereference f()) e)`. -/
private def containsDeref (ptrExp : AST.Exp) : AST.Exp → Bool
  | .Dereference e   => e == ptrExp
  | .Cast _ e        => containsDeref ptrExp e
  | .Binary _ e1 e2  => containsDeref ptrExp e1 || containsDeref ptrExp e2
  | .Unary _ e       => containsDeref ptrExp e
  | _                => false

/-- Substitute every `Dereference ptrExp` sub-expression with `Var substName`,
    looking through `Cast` wrappers.  Used to rewrite the duplicated LHS
    in a compound assignment's RHS so that the pointer is only evaluated once. -/
private def substDeref (ptrExp : AST.Exp) (substName : String) : AST.Exp → AST.Exp
  | .Dereference e =>
      if e == ptrExp then .Var substName
      else .Dereference (substDeref ptrExp substName e)
  | .Cast t e        => .Cast t (substDeref ptrExp substName e)
  | .Binary op e1 e2 => .Binary op (substDeref ptrExp substName e1)
                                    (substDeref ptrExp substName e2)
  | .Unary op e      => .Unary op (substDeref ptrExp substName e)
  | e                => e

-- ---------------------------------------------------------------------------
-- Operator translation
-- ---------------------------------------------------------------------------

private def convertUnop : AST.UnaryOp → UnaryOp
  | .Complement => .Complement
  | .Negate     => .Negate
  | .Not        => .Not

private def convertBinop : AST.BinaryOp → BinaryOp
  | .Add           => .Add
  | .Subtract      => .Subtract
  | .Multiply      => .Multiply
  | .Divide        => .Divide
  | .Remainder     => .Remainder
  | .BitAnd        => .BitAnd
  | .BitOr         => .BitOr
  | .BitXor        => .BitXor
  | .ShiftLeft     => .ShiftLeft
  | .ShiftRight    => .ShiftRight
  | .Equal         => .Equal
  | .NotEqual      => .NotEqual
  | .LessThan      => .LessThan
  | .LessOrEqual   => .LessOrEqual
  | .GreaterThan   => .GreaterThan
  | .GreaterOrEqual => .GreaterOrEqual
  | _              => .Add   -- unreachable: And/Or handled via jumps

-- ---------------------------------------------------------------------------
-- Chapter 18: struct/union member lookup helper
-- ---------------------------------------------------------------------------

/-- Look up a struct/union member's type and byte offset in the TypeTable.
    Returns `(.Int, 0)` if the struct tag or member name is not found. -/
private def lookupMember (tt : Semantics.TypeTable) (tag : String) (member : String)
    : AST.Typ × Int :=
  match Semantics.lookupTypeTable tt tag with
  | none => (.Int, 0)
  | some sd =>
      match sd.members.find? (fun m => m.name == member) with
      | none   => (.Int, 0)
      | some m => (m.typ, (m.offset : Int))

-- ---------------------------------------------------------------------------
-- Chapter 18: aggregate copy helpers
-- ---------------------------------------------------------------------------

-- These helpers are INDEPENDENT of emitExp (they only recurse on themselves
-- and access GenState.typeTable) so they are defined here, before the
-- mutual block containing emitExp and emitLvalAddr.

/-- Return the size in bytes of `typ`, consulting the TypeTable for struct/union.
    AST.Typ.sizeOf returns 0 for Struct/Union; this helper gets the real value. -/
private partial def typeSizeOf (tt : Semantics.TypeTable) : AST.Typ → Nat
  | .Struct tag | .Union tag =>
      match Semantics.lookupTypeTable tt tag with
      | some sd => sd.size
      | none    => 0
  -- Array of struct/union: element size must be looked up from TypeTable, not AST.Typ.sizeOf
  -- (which returns 0 for Struct/Union).  Without this clause, Array(Union tag, n).sizeOf = 0.
  | .Array elem n => typeSizeOf tt elem * n
  | t => t.sizeOf

-- The six helpers below are mutually recursive:
--   emitTypedCopyAt  ↔ emitAggregateCopyAt
--   emitTypedLoadAt  ↔ emitAggregateLoadAt
--   emitTypedStoreAt ↔ emitAggregateStoreAt
-- Each "Typed" variant dispatches on the AST type, handling scalars, arrays,
-- and struct/union aggregates uniformly.  The "Aggregate" variants iterate the
-- members of a struct/union and delegate each member back to the Typed variant.
mutual

/-- Copy a value of any type from `srcName[srcOff]` to `dstName[dstOff]`.
    Dispatches to `emitAggregateCopyAt` for struct/union types and iterates
    element-by-element for array types. -/
private partial def emitTypedCopyAt
    (srcName dstName : String) (srcOff dstOff : Int) (typ : AST.Typ)
    : GenM (List Instruction) := do
  let st ← get
  match typ with
  | .Struct tag | .Union tag =>
      emitAggregateCopyAt srcName dstName srcOff dstOff tag
  | .Array elemTyp elemCount =>
      -- Copy each array element; look up struct element size from TypeTable.
      let elemSize := (typeSizeOf st.typeTable elemTyp : Int)
      (List.range elemCount).foldlM (fun acc (i : Nat) => do
        let off := (i : Int) * elemSize
        let instrs ← emitTypedCopyAt srcName dstName (srcOff + off) (dstOff + off) elemTyp
        return acc ++ instrs) []
  | _ =>
      -- Scalar leaf: CopyFromOffset into a typed temp, then CopyToOffset.
      let tmp := Val.Var (← makeTemporary typ)
      return [.CopyFromOffset srcName srcOff tmp,
              .CopyToOffset tmp dstName dstOff]

/-- Copy all fields of a struct/union from `srcName[srcBase..]` into
    `dstName[dstBase..]`, recursing into nested types via `emitTypedCopyAt`.
    Used for named-variable-to-named-variable aggregate copies. -/
private partial def emitAggregateCopyAt
    (srcName dstName : String) (srcBase dstBase : Int) (tag : String)
    : GenM (List Instruction) := do
  let s ← get
  match Semantics.lookupTypeTable s.typeTable tag with
  | none => return []
  | some sd =>
      sd.members.foldlM (fun acc m => do
        let srcOff := srcBase + (m.offset : Int)
        let dstOff := dstBase + (m.offset : Int)
        let instrs ← emitTypedCopyAt srcName dstName srcOff dstOff m.typ
        return acc ++ instrs) []

/-- Load a value of any type from memory at `baseAddr + memOff` into
    `dstName[dstOff]`.  Dispatches to `emitAggregateLoadAt` for struct/union
    and iterates element-by-element for array types.
    `memOff`: absolute byte offset from `baseAddr` (the source address in RAM).
    `dstOff`: absolute byte offset into `dstName`  (the destination on the stack). -/
private partial def emitTypedLoadAt
    (baseAddr : Val) (memOff dstOff : Int) (dstName : String) (typ : AST.Typ)
    : GenM (List Instruction) := do
  let st ← get
  match typ with
  | .Struct tag | .Union tag =>
      emitAggregateLoadAt baseAddr tag memOff dstOff dstName
  | .Array elemTyp elemCount =>
      let elemSize := (typeSizeOf st.typeTable elemTyp : Int)
      (List.range elemCount).foldlM (fun acc (i : Nat) => do
        let off := (i : Int) * elemSize
        let instrs ← emitTypedLoadAt baseAddr (memOff + off) (dstOff + off) dstName elemTyp
        return acc ++ instrs) []
  | _ =>
      -- Scalar: compute source address, Load, then CopyToOffset.
      let fieldTmp := Val.Var (← makeTemporary typ)
      if memOff == 0 then
        return [.Load baseAddr fieldTmp,
                .CopyToOffset fieldTmp dstName dstOff]
      else
        let fieldAddrTmp := Val.Var (← makeTemporary (.Pointer typ))
        return [.AddPtr baseAddr (.Constant 1) memOff fieldAddrTmp,
                .Load fieldAddrTmp fieldTmp,
                .CopyToOffset fieldTmp dstName dstOff]

/-- Load all fields of a struct/union from memory at `baseAddr + baseMemOff`
    into `dstName[baseDstOff..]`, iterating members via `emitTypedLoadAt`.
    `baseMemOff`: absolute byte offset from `baseAddr` to the struct's first byte.
    `baseDstOff`: absolute byte offset into `dstName`  where this struct is stored. -/
private partial def emitAggregateLoadAt
    (baseAddr : Val) (tag : String) (baseMemOff baseDstOff : Int) (dstName : String)
    : GenM (List Instruction) := do
  let s ← get
  match Semantics.lookupTypeTable s.typeTable tag with
  | none => return []
  | some sd =>
      sd.members.foldlM (fun acc m => do
        let memOff := baseMemOff + (m.offset : Int)
        let dstOff := baseDstOff + (m.offset : Int)
        let instrs ← emitTypedLoadAt baseAddr memOff dstOff dstName m.typ
        return acc ++ instrs) []

/-- Store a value of any type from `srcName[srcOff]` to memory at
    `baseAddr + memOff`.  Dispatches to `emitAggregateStoreAt` for aggregates
    and iterates element-by-element for array types.
    `memOff`: absolute byte offset from `baseAddr` (the destination in RAM).
    `srcOff`: absolute byte offset into `srcName`  (the source on the stack). -/
private partial def emitTypedStoreAt
    (baseAddr : Val) (memOff : Int) (srcName : String) (srcOff : Int) (typ : AST.Typ)
    : GenM (List Instruction) := do
  let st ← get
  match typ with
  | .Struct tag | .Union tag =>
      emitAggregateStoreAt baseAddr tag memOff srcOff srcName
  | .Array elemTyp elemCount =>
      let elemSize := (typeSizeOf st.typeTable elemTyp : Int)
      (List.range elemCount).foldlM (fun acc (i : Nat) => do
        let off := (i : Int) * elemSize
        let instrs ← emitTypedStoreAt baseAddr (memOff + off) srcName (srcOff + off) elemTyp
        return acc ++ instrs) []
  | _ =>
      -- Scalar: CopyFromOffset into typed temp, then Store to computed address.
      let fieldTmp := Val.Var (← makeTemporary typ)
      if memOff == 0 then
        return [.CopyFromOffset srcName srcOff fieldTmp,
                .Store fieldTmp baseAddr]
      else
        let fieldAddrTmp := Val.Var (← makeTemporary (.Pointer typ))
        return [.CopyFromOffset srcName srcOff fieldTmp,
                .AddPtr baseAddr (.Constant 1) memOff fieldAddrTmp,
                .Store fieldTmp fieldAddrTmp]

/-- Store all fields of a struct/union from `srcName[baseSrcOff..]` to memory
    at `baseAddr + baseMemOff`, iterating members via `emitTypedStoreAt`.
    `baseMemOff`: absolute byte offset from `baseAddr` to the struct's first byte.
    `baseSrcOff`: absolute byte offset into `srcName`  where this struct is stored. -/
private partial def emitAggregateStoreAt
    (baseAddr : Val) (tag : String) (baseMemOff baseSrcOff : Int) (srcName : String)
    : GenM (List Instruction) := do
  let s ← get
  match Semantics.lookupTypeTable s.typeTable tag with
  | none => return []
  | some sd =>
      sd.members.foldlM (fun acc m => do
        let memOff := baseMemOff + (m.offset : Int)
        let srcOff := baseSrcOff + (m.offset : Int)
        let instrs ← emitTypedStoreAt baseAddr memOff srcName srcOff m.typ
        return acc ++ instrs) []

end

-- ---------------------------------------------------------------------------
-- Expression lowering
-- ---------------------------------------------------------------------------

/-- Lower an AST expression to TACKY instructions.
    Returns `(result_val, result_type, instructions)`.

    Chapter 18:
    - `Dot(base, member)`: read a struct member.
        Scalar member of named base: `CopyFromOffset(baseName, offset, dst)`.
        Aggregate member: copy each scalar leaf via `emitAggregateCopyAt`.
    - `Arrow(ptr, member)`: read a member through a pointer.
        Scalar member: `AddPtr + Load`.
        Aggregate member: `AddPtr + Load` for each scalar leaf into a temp.
    - `Assignment(Dot ...)` / `Assignment(Arrow ...)`: store to member address.
    - `AddrOf(Dot ...)` / `AddrOf(Arrow ...)`: compute member address via `emitLvalAddr`.
    - `PostfixIncr`/`PostfixDecr` on Dot/Arrow: load old value, increment, store.

    Chapter 13:
    - `Constant(.ConstDouble f)` → intern `f` as a read-only static constant,
      return `Val.Var label` with type `Double`.
    - `Cast(.Double, e)` / `Cast(intTyp, doubleExpr)` → conversion instructions.
    - `Unary .Negate e` where `e : Double` → sets `needsNegZero` in state.

    Chapter 11:
    - `Constant(.ConstInt n)` → `(Constant n, Int, [])`
    - `Constant(.ConstLong n)` → `(Constant n, Long, [])`
    - `Cast(.Long, e)` where e : Int → emit `SignExtend`
    - `Cast(.Int, e)` where e : Long → emit `Truncate`
    - `Cast(t, e)` where e already has type t → identity (no instruction)
    - Binary relational operators always produce `Int` results (0 or 1).
    - Other binary operators produce the common type of their operands.
      (TypeCheck has already inserted Casts so operands have the same type.) -/
-- `partial def` requires that the return type be `Inhabited`.
-- Provide an explicit instance so Lean can compile the partial definition.
private instance : Inhabited (GenM (Val × AST.Typ × List Instruction)) :=
  ⟨fun s => ((Val.Constant 0, AST.Typ.Int, []), s)⟩

-- emitExp and emitLvalAddr are mutually recursive:
--   emitLvalAddr calls emitExp (for Dereference/Arrow/fallback inner exprs)
--   emitExp calls emitLvalAddr (for AddrOf/PostfixIncr/PostfixDecr on Dot/Arrow)
mutual

/-- Chapter 18: Compute the address (a TACKY Val holding a pointer) of an lvalue
    expression, returning `(ptrVal, pointeeTyp, instructions)`.
    Used by `AddrOf`, `PostfixIncr`, `PostfixDecr` on `Dot`/`Arrow` to avoid
    creating a copy (which would give the wrong address). -/
private partial def emitLvalAddr (st : Semantics.SymbolTable)
    : AST.Exp → GenM (Val × AST.Typ × List Instruction)
  | .Var name => do
      -- Named variable: GetAddress emits `leaq name, dst`
      let varTyp : AST.Typ := match Semantics.lookupSym st name with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let dst := Val.Var (← makeTemporary (.Pointer varTyp))
      return (dst, varTyp, [.GetAddress (.Var name) dst])
  | .Dereference inner => do
      -- *p is at address p — just evaluate p
      let (ptrVal, ptrTyp, instrs) ← emitExp st inner
      let valTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      return (ptrVal, valTyp, instrs)
  | .Dot base member => do
      -- s.member is at address (&s) + memberOffset
      let s ← get
      let (baseAddr, baseTyp, baseInstrs) ← emitLvalAddr st base
      let tag := match baseTyp with | .Struct t | .Union t => t | _ => ""
      let (memberTyp, memberOffset) := lookupMember s.typeTable tag member
      if memberOffset == 0 then
        return (baseAddr, memberTyp, baseInstrs)
      else
        let addrTmp := Val.Var (← makeTemporary (.Pointer memberTyp))
        return (addrTmp, memberTyp,
          baseInstrs ++ [.AddPtr baseAddr (.Constant 1) memberOffset addrTmp])
  | .Arrow ptr member => do
      -- p->member is at address p + memberOffset
      let s ← get
      let (ptrVal, ptrTyp, ptrInstrs) ← emitExp st ptr
      let structTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      let tag := match structTyp with | .Struct t | .Union t => t | _ => ""
      let (memberTyp, memberOffset) := lookupMember s.typeTable tag member
      if memberOffset == 0 then
        return (ptrVal, memberTyp, ptrInstrs)
      else
        let addrTmp := Val.Var (← makeTemporary (.Pointer memberTyp))
        return (addrTmp, memberTyp,
          ptrInstrs ++ [.AddPtr ptrVal (.Constant 1) memberOffset addrTmp])
  | other => do
      -- General fallback: evaluate the expression, then take its address.
      -- This handles function return values (struct stored in a named tmp).
      -- FixUp routes `Lea(Memory, Memory)` through R11 automatically.
      let (val, typ, instrs) ← emitExp st other
      let dst := Val.Var (← makeTemporary (.Pointer typ))
      return (dst, typ, instrs ++ [.GetAddress val dst])

private partial def emitExp (st : Semantics.SymbolTable) : AST.Exp → GenM (Val × AST.Typ × List Instruction)
  | .Constant (.ConstInt n)   => return (.Constant n, .Int,   [])
  | .Constant (.ConstLong n)  => return (.Constant n, .Long,  [])
  | .Constant (.ConstUInt n)  => return (.Constant n, .UInt,  [])  -- Chapter 12
  | .Constant (.ConstULong n) => return (.Constant n, .ULong, [])  -- Chapter 12
  | .Constant (.ConstDouble f) => do
      -- Chapter 13: float constants cannot be immediates; intern as a static label.
      let label ← internFloat f
      return (.Var label, .Double, [])
  -- Chapter 16: char constants — store as Constant(n) with char type
  | .Constant (.ConstChar n)   => return (.Constant n, .Char,  [])
  | .Constant (.ConstUChar n)  => return (.Constant n, .UChar, [])
  -- Chapter 16: string literal — intern as a read-only string constant in .rodata.
  -- The result Val is Var(label), type Array(Char, n+1).
  -- When AddrOf wraps this (array-to-pointer decay), GetAddress emits leaq label(%rip), dst.
  | .StringLiteral s => do
      let label ← internString s
      return (.Var label, .Array .Char (s.length + 1), [])
  | .Var v => do
      let t : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      return (.Var v, t, [])
  | .Cast targetTyp inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      if targetTyp == srcTyp then
        return (src, targetTyp, instrs)
      else
        let dst := Val.Var (← makeTemporary targetTyp)
        match targetTyp, srcTyp with
        -- ---- integer ↔ integer conversions (Ch11/Ch12) ----
        -- Widening sign-extend (signed int → wider signed or unsigned type)
        | .Long,  .Int  => return (dst, .Long,  instrs ++ [.SignExtend srcTyp src dst])
        | .ULong, .Int  => return (dst, .ULong, instrs ++ [.SignExtend srcTyp src dst])
        -- Widening zero-extend (unsigned int → wider type)
        | .Long,  .UInt => return (dst, .Long,  instrs ++ [.ZeroExtend srcTyp src dst])
        | .ULong, .UInt => return (dst, .ULong, instrs ++ [.ZeroExtend srcTyp src dst])
        -- Narrowing truncation (64-bit → 32-bit: keep lower 32 bits)
        | .Int,  .Long  => return (dst, .Int,  instrs ++ [.Truncate src dst])
        | .UInt, .Long  => return (dst, .UInt, instrs ++ [.Truncate src dst])
        | .Int,  .ULong => return (dst, .Int,  instrs ++ [.Truncate src dst])
        | .UInt, .ULong => return (dst, .UInt, instrs ++ [.Truncate src dst])
        -- ---- double ↔ integer conversions (Ch13) ----
        -- Signed integer → Double
        | .Double, .Int   => return (dst, .Double, instrs ++ [.IntToDouble  src dst])
        | .Double, .Long  => return (dst, .Double, instrs ++ [.IntToDouble  src dst])
        -- Unsigned integer → Double
        | .Double, .UInt  => return (dst, .Double, instrs ++ [.UIntToDouble  src dst])
        | .Double, .ULong => return (dst, .Double, instrs ++ [.ULongToDouble src dst])
        -- Double → Signed integer
        | .Int,    .Double => return (dst, .Int,  instrs ++ [.DoubleToInt  src dst])
        | .Long,   .Double => return (dst, .Long, instrs ++ [.DoubleToInt  src dst])
        -- Double → Unsigned integer
        | .UInt,   .Double => return (dst, .UInt,  instrs ++ [.DoubleToUInt  src dst])
        | .ULong,  .Double => return (dst, .ULong, instrs ++ [.DoubleToULong src dst])
        -- Chapter 14: pointer ↔ integer casts
        -- Integer → Pointer: sign-extend (Int), zero-extend (UInt), or copy (Long/ULong)
        | .Pointer _, .Int   => return (dst, targetTyp, instrs ++ [.SignExtend srcTyp src dst])
        | .Pointer _, .UInt  => return (dst, targetTyp, instrs ++ [.ZeroExtend srcTyp src dst])
        | .Pointer _, .Long  => return (dst, targetTyp, instrs ++ [.Copy src dst])
        | .Pointer _, .ULong => return (dst, targetTyp, instrs ++ [.Copy src dst])
        -- Pointer → Pointer (reinterpret cast between pointer types)
        | .Pointer _, .Pointer _ => return (dst, targetTyp, instrs ++ [.Copy src dst])
        -- Chapter 15: Array → Pointer (explicit cast, e.g. `(long *)arr` where arr : long[4]).
        -- An array variable used as a value must decay to a pointer to its first element.
        -- There are two sub-cases:
        --   (a) `arr` is an lvalue array variable → use GetAddress (`leaq arr, dst`).
        --   (b) The source is `Dereference(p)` where p : Pointer(Array).
        --       TackyGen's Dereference-of-array optimization returns (ptrVal, Array, instrs)
        --       WITHOUT emitting a Load — ptrVal is already the pointer to the array's first
        --       element (i.e. it IS the correct pointer value).  Applying GetAddress here would
        --       take the address of the *stack slot* holding ptrVal, which is wrong.
        --       Instead just Copy the pointer value into a typed temporary.
        | .Pointer _, .Array _ _ =>
            match inner with
            | .Dereference _ => return (dst, targetTyp, instrs ++ [.Copy src dst])
            | _              => return (dst, targetTyp, instrs ++ [.GetAddress src dst])
        -- Pointer → Integer: truncate (Pointer→Int/UInt, 64→32) or copy (Pointer→Long/ULong)
        | .Int,   .Pointer _ => return (dst, targetTyp, instrs ++ [.Truncate src dst])
        | .UInt,  .Pointer _ => return (dst, targetTyp, instrs ++ [.Truncate src dst])
        | .Long,  .Pointer _ => return (dst, targetTyp, instrs ++ [.Copy src dst])
        | .ULong, .Pointer _ => return (dst, targetTyp, instrs ++ [.Copy src dst])
        -- ---- Chapter 16: char ↔ integer conversions ----
        -- Char/SChar (signed byte) widening to wider types → sign-extend
        -- Pass srcTyp so CodeGen knows the source is Byte-sized even for constant operands.
        | .Int,   .Char | .Int,   .SChar => return (dst, targetTyp, instrs ++ [.SignExtend srcTyp src dst])
        | .Long,  .Char | .Long,  .SChar => return (dst, targetTyp, instrs ++ [.SignExtend srcTyp src dst])
        | .UInt,  .Char | .UInt,  .SChar => return (dst, targetTyp, instrs ++ [.SignExtend srcTyp src dst])
        | .ULong, .Char | .ULong, .SChar => return (dst, targetTyp, instrs ++ [.SignExtend srcTyp src dst])
        -- UChar (unsigned byte) widening to wider types → zero-extend
        | .Int,   .UChar => return (dst, targetTyp, instrs ++ [.ZeroExtend srcTyp src dst])
        | .Long,  .UChar => return (dst, targetTyp, instrs ++ [.ZeroExtend srcTyp src dst])
        | .UInt,  .UChar => return (dst, targetTyp, instrs ++ [.ZeroExtend srcTyp src dst])
        | .ULong, .UChar => return (dst, targetTyp, instrs ++ [.ZeroExtend srcTyp src dst])
        -- Wider integer → Char/SChar/UChar → truncate (keep lower 8 bits)
        | .Char,  .Int  | .Char,  .Long  | .Char,  .UInt  | .Char,  .ULong =>
            return (dst, targetTyp, instrs ++ [.Truncate src dst])
        | .SChar, .Int  | .SChar, .Long  | .SChar, .UInt  | .SChar, .ULong =>
            return (dst, targetTyp, instrs ++ [.Truncate src dst])
        | .UChar, .Int  | .UChar, .Long  | .UChar, .UInt  | .UChar, .ULong =>
            return (dst, targetTyp, instrs ++ [.Truncate src dst])
        -- Char/SChar ↔ UChar (same 8 bits, reinterpret): copy into new typed temp
        | .UChar, .Char  | .UChar, .SChar  => return (dst, targetTyp, instrs ++ [.Copy src dst])
        | .Char,  .UChar | .SChar, .UChar  => return (dst, targetTyp, instrs ++ [.Copy src dst])
        | .Char,  .SChar | .SChar, .Char   => return (dst, targetTyp, instrs ++ [.Copy src dst])
        -- Char/SChar → Double: sign-extend-to-int then convert (CodeGen handles byte src)
        | .Double, .Char | .Double, .SChar => return (dst, targetTyp, instrs ++ [.IntToDouble  src dst])
        -- UChar → Double: zero-extend-to-int then convert (CodeGen handles byte src)
        | .Double, .UChar => return (dst, targetTyp, instrs ++ [.UIntToDouble src dst])
        -- Double → Char/SChar: convert to int then truncate to byte (CodeGen handles byte dst)
        | .Char,  .Double | .SChar, .Double => return (dst, targetTyp, instrs ++ [.DoubleToInt  src dst])
        -- Double → UChar: convert to uint then truncate to byte (CodeGen handles byte dst)
        | .UChar, .Double => return (dst, targetTyp, instrs ++ [.DoubleToUInt src dst])
        -- Pointer → Char/SChar/UChar: truncate 64-bit pointer to byte
        | .Char,  .Pointer _ | .SChar, .Pointer _ | .UChar, .Pointer _ =>
            return (dst, targetTyp, instrs ++ [.Truncate src dst])
        -- Char/SChar → Pointer: sign-extend byte to 64-bit
        | .Pointer _, .Char | .Pointer _, .SChar =>
            return (dst, targetTyp, instrs ++ [.SignExtend srcTyp src dst])
        -- UChar → Pointer: zero-extend byte to 64-bit
        | .Pointer _, .UChar => return (dst, targetTyp, instrs ++ [.ZeroExtend srcTyp src dst])
        -- Same-size reinterpret (int↔uint or long↔ulong): copy into a new typed temporary
        | _, _ => return (dst, targetTyp, instrs ++ [.Copy src dst])
  | .Unary .Not inner => do
      let (src, _, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary .Int)
      return (dst, .Int, instrs ++ [.Unary .Not src dst])
  | .Unary .Negate inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary srcTyp)
      -- Chapter 13: double negation needs the neg-zero constant in the assembly
      if srcTyp == .Double then
        modify (fun s => { s with needsNegZero := true })
      return (dst, srcTyp, instrs ++ [.Unary .Negate src dst])
  | .Unary op inner => do
      let (src, srcTyp, instrs) ← emitExp st inner
      let dst := Val.Var (← makeTemporary srcTyp)
      return (dst, srcTyp, instrs ++ [.Unary (convertUnop op) src dst])
  | .Binary .And e1 e2 => do
      let falseLabel ← makeLabel "and_false"
      let endLabel   ← makeLabel "and_end"
      let (v1, _, instrs1) ← emitExp st e1
      let (v2, _, instrs2) ← emitExp st e2
      let result := Val.Var (← makeTemporary .Int)
      return (result, .Int,
        instrs1 ++ [.JumpIfZero v1 falseLabel] ++
        instrs2 ++ [.JumpIfZero v2 falseLabel,
                    .Copy (.Constant 1) result, .Jump endLabel,
                    .Label falseLabel, .Copy (.Constant 0) result,
                    .Label endLabel])
  | .Binary .Or e1 e2 => do
      let trueLabel  ← makeLabel "or_true"
      let endLabel   ← makeLabel "or_end"
      let (v1, _, instrs1) ← emitExp st e1
      let (v2, _, instrs2) ← emitExp st e2
      let result := Val.Var (← makeTemporary .Int)
      return (result, .Int,
        instrs1 ++ [.JumpIfNotZero v1 trueLabel] ++
        instrs2 ++ [.JumpIfNotZero v2 trueLabel,
                    .Copy (.Constant 0) result, .Jump endLabel,
                    .Label trueLabel, .Copy (.Constant 1) result,
                    .Label endLabel])
  | .Binary op e1 e2 => do
      let (src1, t1, instrs1) ← emitExp st e1
      let (src2, t2, instrs2) ← emitExp st e2
      -- Chapter 15: detect pointer arithmetic and emit AddPtr instead of Binary.
      -- TypeCheck ensures that if one side is a Pointer, the operation is + or -.
      -- Chapter 18: for pointer-to-struct/union, elemTyp.sizeOf returns 0 because the
      -- real size is in the TypeTable.  Use typeSizeOf (the GenM-aware helper) instead.
      let ptrElemScale : AST.Typ → GenM Int := fun elemTyp => do
        let s ← get
        return (typeSizeOf s.typeTable elemTyp : Int)
      match op, t1, t2 with
      | .Add, .Pointer elemTyp, _ => do
          -- ptr + int: AddPtr(ptr_val, idx_val, scale, dst)
          let scale ← ptrElemScale elemTyp
          let dst   := Val.Var (← makeTemporary t1)
          return (dst, t1, instrs1 ++ instrs2 ++ [.AddPtr src1 src2 scale dst])
      | .Add, _, .Pointer elemTyp => do
          -- int + ptr: commutative; put the pointer first
          let scale ← ptrElemScale elemTyp
          let dst   := Val.Var (← makeTemporary t2)
          return (dst, t2, instrs1 ++ instrs2 ++ [.AddPtr src2 src1 scale dst])
      | .Subtract, .Pointer elemTyp, .Pointer _ => do
          -- ptr - ptr: (ptr1 - ptr2) / elemSize → result type Long (ptrdiff_t)
          let scale   ← ptrElemScale elemTyp
          let diffTmp := Val.Var (← makeTemporary .Long)
          let dst     := Val.Var (← makeTemporary .Long)
          return (dst, .Long,
            instrs1 ++ instrs2 ++
            [.Binary .Subtract src1 src2 diffTmp,
             .Binary .Divide diffTmp (.Constant scale) dst])
      | .Subtract, .Pointer elemTyp, _ => do
          -- ptr - int: negate the index, then AddPtr(ptr, neg_idx, scale, dst)
          let scale  ← ptrElemScale elemTyp
          let negIdx := Val.Var (← makeTemporary t2)
          let dst    := Val.Var (← makeTemporary t1)
          return (dst, t1,
            instrs1 ++ instrs2 ++
            [.Unary .Negate src2 negIdx,
             .AddPtr src1 negIdx scale dst])
      | _, _, _ =>
          -- Regular arithmetic / bitwise / relational / shift
          let resultTyp : AST.Typ := match op with
            | .Equal | .NotEqual | .LessThan | .LessOrEqual
            | .GreaterThan | .GreaterOrEqual => .Int
            | .ShiftLeft | .ShiftRight => t1   -- type of left operand (C §6.5.7)
            | .And | .Or               => .Int
            | _                        => t1   -- arithmetic ops: t1 == t2 after TypeCheck
          let dst := Val.Var (← makeTemporary resultTyp)
          return (dst, resultTyp,
            instrs1 ++ instrs2 ++ [.Binary (convertBinop op) src1 src2 dst])
  | .Conditional cond e1 e2 => do
      let e2Label  ← makeLabel "ternary_else"
      let endLabel ← makeLabel "ternary_end"
      let (c,  _, condInstrs) ← emitExp st cond
      let (v1, t1, e1Instrs) ← emitExp st e1
      let (v2, _, e2Instrs)  ← emitExp st e2
      let result := Val.Var (← makeTemporary t1)
      return (result, t1,
        condInstrs ++ [.JumpIfZero c e2Label] ++
        e1Instrs ++ [.Copy v1 result, .Jump endLabel, .Label e2Label] ++
        e2Instrs ++ [.Copy v2 result, .Label endLabel])
  | .Assignment (.Var v) rhs => do
      let (result, _, instrs) ← emitExp st rhs
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      -- Chapter 18: struct/union copy via `Copy` instruction.
      -- CodeGen expands `Copy(ByteArray)` into chunk-by-chunk movq instructions.
      return (.Var v, varTyp, instrs ++ [.Copy result (.Var v)])
  -- Chapter 14: assignment through a pointer dereference: `*ptr = rhs`
  -- TypeCheck has already cast rhs to the pointed-to type.
  -- Extra credit: compound assignment `*f() += e` desugars to
  --   Assignment (Dereference (f())) (Binary op (Dereference (f())) e)
  -- where the LHS dereference appears TWICE.  We detect this by checking whether
  -- rhs contains Dereference(ptrExp), and if so, load the pointed-to value once
  -- into a fresh temporary and substitute it in the RHS to avoid double evaluation.
  | .Assignment (.Dereference ptrExp) rhs => do
      let (ptrVal, ptrTyp, ptrInstrs) ← emitExp st ptrExp
      -- The assignment result type is the pointed-to type
      let valTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      if containsDeref ptrExp rhs then
        -- Compound assignment: load *ptrVal once into substName, substitute in rhs
        let substName ← makeTemporary valTyp
        -- Extend the SymbolTable so that emitExp (Var substName) can look up its type
        let st' := Semantics.insertSym st substName { type := .Obj valTyp, attrs := .Local }
        let rhs' := substDeref ptrExp substName rhs
        let (rhsVal, _, rhsInstrs) ← emitExp st' rhs'
        return (rhsVal, valTyp,
          ptrInstrs ++ [.Load ptrVal (.Var substName)] ++ rhsInstrs ++ [.Store rhsVal ptrVal])
      else
        -- Plain assignment: emit rhs normally, no double evaluation
        let (rhsVal, _, rhsInstrs) ← emitExp st rhs
        -- When assigning through a pointer to a narrow type (e.g. char *p; *p = 'J'),
        -- the rhs may be a Constant (e.g. Constant 74).  `valAsmType(Constant 74)` returns
        -- Longword (since 74 fits in 32 bits), but the Store should only write 1 byte.
        -- Fix: route Constant operands through a typed temporary so the BST records the
        -- correct AsmType (Byte for Char/SChar/UChar), and CodeGen uses the right move width.
        let (storeVal, storeInstrs) ← match rhsVal with
          | .Constant _ =>
              let tmp := Val.Var (← makeTemporary valTyp)
              pure (tmp, [Instruction.Copy rhsVal tmp])
          | _ => pure (rhsVal, [])
        return (rhsVal, valTyp, ptrInstrs ++ rhsInstrs ++ storeInstrs ++ [.Store storeVal ptrVal])
  -- Chapter 18: assignment to a struct member via dot operator: `s.member = rhs`
  | .Assignment (.Dot base member) rhs => do
      let s ← get
      let (rhsVal, _, rhsInstrs) ← emitExp st rhs
      -- Compute the address of the member
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Dot base member)
      -- Store the rhs value into the member
      let storeInstrs ← match memberTyp with
        | .Struct innerTag | .Union innerTag =>
            -- Aggregate member: store each scalar field using AggregateStoreAt
            let rhsName := match rhsVal with | .Var n => n | .Constant _ => ""
            emitAggregateStoreAt memberAddr innerTag 0 0 rhsName
        | _ =>
            -- Scalar member: Store rhs to member address
            -- Route constants through a typed temp (for byte-sized members)
            let (storeVal, typedInstrs) ← match rhsVal with
              | .Constant _ =>
                  let tmp := Val.Var (← makeTemporary memberTyp)
                  pure (tmp, [Instruction.Copy rhsVal tmp])
              | _ => pure (rhsVal, [])
            pure (typedInstrs ++ [.Store storeVal memberAddr])
      return (rhsVal, memberTyp, rhsInstrs ++ addrInstrs ++ storeInstrs)
  -- Chapter 18: assignment to a struct member via arrow operator: `p->member = rhs`
  | .Assignment (.Arrow ptr member) rhs => do
      let s ← get
      let (rhsVal, _, rhsInstrs) ← emitExp st rhs
      -- Compute the address of the member through the pointer
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Arrow ptr member)
      -- Store rhs to the member address
      let storeInstrs ← match memberTyp with
        | .Struct innerTag | .Union innerTag =>
            let rhsName := match rhsVal with | .Var n => n | .Constant _ => ""
            emitAggregateStoreAt memberAddr innerTag 0 0 rhsName
        | _ =>
            let (storeVal, typedInstrs) ← match rhsVal with
              | .Constant _ =>
                  let tmp := Val.Var (← makeTemporary memberTyp)
                  pure (tmp, [Instruction.Copy rhsVal tmp])
              | _ => pure (rhsVal, [])
            pure (typedInstrs ++ [.Store storeVal memberAddr])
      return (rhsVal, memberTyp, rhsInstrs ++ addrInstrs ++ storeInstrs)
  | .Assignment _ _ => return (.Constant 0, .Int, [])
  | .PostfixIncr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      match varTyp with
      | .Pointer elemTyp => do
          -- Chapter 15: pointer increment advances by sizeof(*ptr), not by 1 byte.
          -- Chapter 18: for pointer-to-struct, look up the real size from the TypeTable.
          let s ← get
          let scale : Int := (typeSizeOf s.typeTable elemTyp : Int)
          return (.Var tmp, varTyp,
            [.Copy (.Var v) (.Var tmp),
             .AddPtr (.Var v) (.Constant 1) scale (.Var v)])
      | .Double => do
          let oneLabel ← internFloat 1.0
          return (.Var tmp, varTyp,
            [.Copy (.Var v) (.Var tmp),
             .Binary .Add (.Var v) (.Var oneLabel) (.Var v)])
      | _ =>
          return (.Var tmp, varTyp,
            [.Copy (.Var v) (.Var tmp),
             .Binary .Add (.Var v) (.Constant 1) (.Var v)])
  -- Chapter 14: postfix ++ through a pointer dereference: `(*p)++`
  -- Load the old value, save it, add 1 (or sizeof(*p) for pointer *p), store back,
  -- return the old value.
  | .PostfixIncr (.Dereference ptrExp) => do
      let (ptrVal, ptrTyp, ptrInstrs) ← emitExp st ptrExp
      let valTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      let loadedVal := Val.Var (← makeTemporary valTyp)
      let oldVal    := Val.Var (← makeTemporary valTyp)
      let s ← get
      let addInstrs : List Instruction :=
        match valTyp with
        | .Pointer elemTyp =>
            -- Chapter 15/18: (*p)++ where *p is a pointer — advance by element size
            -- Chapter 18: use typeSizeOf for struct/union pointer types
            [.AddPtr loadedVal (.Constant 1) (typeSizeOf s.typeTable elemTyp) loadedVal]
        | _ =>
            [.Binary .Add loadedVal (.Constant 1) loadedVal]
      return (oldVal, valTyp,
        ptrInstrs ++ [.Load ptrVal loadedVal, .Copy loadedVal oldVal] ++
        addInstrs ++ [.Store loadedVal ptrVal])
  -- Chapter 18: postfix ++ on a struct member: `s.member++` or `p->member++`
  -- Get the member address, load old value, increment, store back, return old value.
  | .PostfixIncr (.Dot base member) => do
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Dot base member)
      let loadedVal := Val.Var (← makeTemporary memberTyp)
      let oldVal    := Val.Var (← makeTemporary memberTyp)
      let s ← get
      let addInstrs : List Instruction :=
        match memberTyp with
        -- Chapter 18: use typeSizeOf for struct/union pointer types
        | .Pointer elemTyp => [.AddPtr loadedVal (.Constant 1) (typeSizeOf s.typeTable elemTyp) loadedVal]
        | _ => [.Binary .Add loadedVal (.Constant 1) loadedVal]
      return (oldVal, memberTyp,
        addrInstrs ++ [.Load memberAddr loadedVal, .Copy loadedVal oldVal] ++
        addInstrs ++ [.Store loadedVal memberAddr])
  | .PostfixIncr (.Arrow ptr member) => do
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Arrow ptr member)
      let loadedVal := Val.Var (← makeTemporary memberTyp)
      let oldVal    := Val.Var (← makeTemporary memberTyp)
      let s ← get
      let addInstrs : List Instruction :=
        match memberTyp with
        -- Chapter 18: use typeSizeOf for struct/union pointer types
        | .Pointer elemTyp => [.AddPtr loadedVal (.Constant 1) (typeSizeOf s.typeTable elemTyp) loadedVal]
        | _ => [.Binary .Add loadedVal (.Constant 1) loadedVal]
      return (oldVal, memberTyp,
        addrInstrs ++ [.Load memberAddr loadedVal, .Copy loadedVal oldVal] ++
        addInstrs ++ [.Store loadedVal memberAddr])
  | .PostfixIncr _ => return (.Constant 0, .Int, [])
  | .PostfixDecr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      match varTyp with
      | .Pointer elemTyp => do
          -- Chapter 15/18: pointer decrement advances by -sizeof(*ptr)
          -- Chapter 18: use typeSizeOf for struct/union pointer types
          let s ← get
          let scale : Int := typeSizeOf s.typeTable elemTyp
          return (.Var tmp, varTyp,
            [.Copy (.Var v) (.Var tmp),
             .AddPtr (.Var v) (.Constant (-1)) scale (.Var v)])
      | .Double => do
          let oneLabel ← internFloat 1.0
          return (.Var tmp, varTyp,
            [.Copy (.Var v) (.Var tmp),
             .Binary .Subtract (.Var v) (.Var oneLabel) (.Var v)])
      | _ =>
          return (.Var tmp, varTyp,
            [.Copy (.Var v) (.Var tmp),
             .Binary .Subtract (.Var v) (.Constant 1) (.Var v)])
  -- Chapter 14: postfix -- through a pointer dereference: `(*p)--`
  | .PostfixDecr (.Dereference ptrExp) => do
      let (ptrVal, ptrTyp, ptrInstrs) ← emitExp st ptrExp
      let valTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      let loadedVal := Val.Var (← makeTemporary valTyp)
      let oldVal    := Val.Var (← makeTemporary valTyp)
      let s ← get
      let subInstrs : List Instruction :=
        match valTyp with
        | .Pointer elemTyp =>
            -- Chapter 15/18: (*p)-- where *p is a pointer — decrement by element size
            -- Chapter 18: use typeSizeOf for struct/union pointer types
            [.AddPtr loadedVal (.Constant (-1)) (typeSizeOf s.typeTable elemTyp) loadedVal]
        | _ =>
            [.Binary .Subtract loadedVal (.Constant 1) loadedVal]
      return (oldVal, valTyp,
        ptrInstrs ++ [.Load ptrVal loadedVal, .Copy loadedVal oldVal] ++
        subInstrs ++ [.Store loadedVal ptrVal])
  -- Chapter 18: postfix -- on a struct member: `s.member--` or `p->member--`
  | .PostfixDecr (.Dot base member) => do
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Dot base member)
      let loadedVal := Val.Var (← makeTemporary memberTyp)
      let oldVal    := Val.Var (← makeTemporary memberTyp)
      let s ← get
      let subInstrs : List Instruction :=
        match memberTyp with
        -- Chapter 18: use typeSizeOf for struct/union pointer types
        | .Pointer elemTyp => [.AddPtr loadedVal (.Constant (-1)) (typeSizeOf s.typeTable elemTyp) loadedVal]
        | _ => [.Binary .Subtract loadedVal (.Constant 1) loadedVal]
      return (oldVal, memberTyp,
        addrInstrs ++ [.Load memberAddr loadedVal, .Copy loadedVal oldVal] ++
        subInstrs ++ [.Store loadedVal memberAddr])
  | .PostfixDecr (.Arrow ptr member) => do
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Arrow ptr member)
      let loadedVal := Val.Var (← makeTemporary memberTyp)
      let oldVal    := Val.Var (← makeTemporary memberTyp)
      let s ← get
      let subInstrs : List Instruction :=
        match memberTyp with
        -- Chapter 18: use typeSizeOf for struct/union pointer types
        | .Pointer elemTyp => [.AddPtr loadedVal (.Constant (-1)) (typeSizeOf s.typeTable elemTyp) loadedVal]
        | _ => [.Binary .Subtract loadedVal (.Constant 1) loadedVal]
      return (oldVal, memberTyp,
        addrInstrs ++ [.Load memberAddr loadedVal, .Copy loadedVal oldVal] ++
        subInstrs ++ [.Store loadedVal memberAddr])
  | .PostfixDecr _ => return (.Constant 0, .Int, [])
  -- Chapter 14: `&*e` cancels out — equivalent to just evaluating e (the pointer).
  -- This is important for correctness: `&*null_ptr` must NOT actually dereference.
  | .AddrOf (.Dereference inner) => do
      -- Optimization: &(*e) = e — no load/store, just return the pointer value.
      -- Chapter 15: if `inner` computes a Pointer(Array(T, n)), we adjust the type
      -- to Pointer(T) because in C, array decay means "pointer to first element."
      -- Concretely: for 2-D `a[i][j]`, the inner subscript gives a `Pointer(row-type)`,
      -- and AddrOf(Dereference(...)) on that row should give Pointer(element-type) for
      -- the next subscript level to use the correct element size as scale.
      let (ptrVal, ptrTyp, instrs) ← emitExp st inner
      let adjustedTyp : AST.Typ := match ptrTyp with
        | .Pointer (.Array elemT _) => .Pointer elemT  -- pointer-to-array → pointer-to-element
        | t                         => t
      return (ptrVal, adjustedTyp, instrs)
  -- Chapter 18: `&s.member` — compute address of member without creating a copy.
  -- Using emitLvalAddr avoids the incorrect &(copy-of-member) that the general
  -- AddrOf handler would produce.
  -- For array members: `&s.arr` gives `T(*)[n]` (pointer to the array), NOT `T*`.
  -- TypeCheck's subscript desugaring uses Cast(Pointer(T), arr) (not AddrOf) for decay,
  -- so AddrOf here correctly preserves the pointer-to-array type for expressions
  -- like `&s.arr + 1` which should advance by the full array size.
  | .AddrOf (.Dot base member) => do
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Dot base member)
      let ptrTyp : AST.Typ := .Pointer memberTyp   -- correct C semantics: &arr gives T(*)[n]
      return (memberAddr, ptrTyp, addrInstrs)
  -- Chapter 18: `&p->member` — compute address of member through pointer.
  -- Same correct pointer-to-array type (no decay) as for Dot above.
  | .AddrOf (.Arrow ptr member) => do
      let (memberAddr, memberTyp, addrInstrs) ← emitLvalAddr st (.Arrow ptr member)
      let ptrTyp : AST.Typ := .Pointer memberTyp   -- correct C semantics: no decay
      return (memberAddr, ptrTyp, addrInstrs)
  -- Chapter 14: address-of: `&e` allocates a pointer-typed temporary for the address.
  -- In C, `&arr` where `arr : T arr[n]` gives `T(*)[n]` (pointer to the array), not `T*`.
  -- TypeCheck's subscript desugaring uses Cast(Pointer(T), arr) for array decay (not AddrOf),
  -- so AddrOf here can correctly return Pointer(Array(T,n)) for explicit &arr expressions.
  | .AddrOf inner => do
      let (srcVal, srcTyp, instrs) ← emitExp st inner
      -- No decay: &arr gives Pointer(Array(T,n)), not Pointer(T).
      -- Subscript desugaring uses Cast(Pointer(elem), arr) instead, handled in the Cast case.
      let ptrTyp : AST.Typ := .Pointer srcTyp
      let dst := Val.Var (← makeTemporary ptrTyp)
      return (dst, ptrTyp, instrs ++ [.GetAddress srcVal dst])
  -- Chapter 14: dereference in rvalue context: `*ptr` loads from the pointer address.
  -- Chapter 15: if the pointed-to type is itself an array (e.g., `Pointer(int[4])`),
  -- we do NOT emit a Load — loading an entire array is not possible (arrays have no
  -- register representation).  Instead we keep the pointer value and report the array
  -- type; the outer AddrOf(Dereference) optimization will convert it back to a plain
  -- pointer-to-element for the next subscript level.
  | .Dereference inner => do
      let (ptrVal, ptrTyp, instrs) ← emitExp st inner
      let valTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      -- If valTyp is an array type, this Dereference is an intermediate expression
      -- (e.g. `a[i]` of a 2-D array before the outer subscript).  We return the
      -- POINTER itself (ptrVal) typed as valTyp — the AddrOf wrapper on top will see
      -- this array type and adjust accordingly. No Load is emitted here.
      if (match valTyp with | .Array _ _ => true | _ => false) then
        return (ptrVal, valTyp, instrs)
      -- Chapter 18: if the pointee type is a struct/union, we cannot use a scalar Load.
      -- Instead, load each field from memory at *ptrVal into a fresh aggregate temp.
      -- This is the rvalue analogue of the Arrow expression handler.
      match valTyp with
      | .Struct tag | .Union tag =>
          let tmpName ← makeTemporary valTyp
          let loadInstrs ← emitAggregateLoadAt ptrVal tag 0 0 tmpName
          return (.Var tmpName, valTyp, instrs ++ loadInstrs)
      | _ =>
          let dst := Val.Var (← makeTemporary valTyp)
          return (dst, valTyp, instrs ++ [.Load ptrVal dst])
  | .FunCall name args => do
      let argResults ← args.mapM (emitExp st)
      let argInstrs := argResults.foldl (fun acc (_, _, instrs) => acc ++ instrs) []
      let argVals   := argResults.map   (fun (v, _, _) => v)
      let retTyp : AST.Typ := match Semantics.lookupSym st name with
        | some { type := .Fun _ _ rt, .. } => rt
        | _ => .Int
      -- Chapter 17: void function calls have no destination — emit dst = none.
      -- The dummy Val.Constant 0 is returned from emitExp but will not be used
      -- (callers that use the result of a void call will be caught by TypeCheck).
      if retTyp == .Void then do
        return (.Constant 0, .Void, argInstrs ++ [.FunCall name argVals none])
      else do
        let dst := Val.Var (← makeTemporary retTyp)
        return (dst, retTyp, argInstrs ++ [.FunCall name argVals (some dst)])
  -- Chapter 18: `s.member` — read a struct/union member from a named variable.
  -- For scalar members: `CopyFromOffset(baseName, offset, dst)`.
  -- For aggregate members: copy each scalar leaf via `emitAggregateCopyAt`.
  -- For array members: return a pointer to the member (array decay).
  | .Dot base member => do
      let s ← get
      let (baseVal, baseTyp, baseInstrs) ← emitExp st base
      -- baseName: the TACKY variable name holding the struct (always a Var for struct types)
      let baseName := match baseVal with | .Var n => n | .Constant _ => ""
      let tag := match baseTyp with | .Struct t | .Union t => t | _ => ""
      let (memberTyp, memberOffset) := lookupMember s.typeTable tag member
      match memberTyp with
      | .Struct innerTag | .Union innerTag =>
          -- Aggregate member: create a fresh temp of this struct type, copy scalar fields into it.
          let tmpName ← makeTemporary memberTyp
          let copyInstrs ← emitAggregateCopyAt baseName tmpName memberOffset 0 innerTag
          return (.Var tmpName, memberTyp, baseInstrs ++ copyInstrs)
      | .Array elemTyp _ =>
          -- Array member: return the address of the array in the ORIGINAL struct location.
          -- We must use emitLvalAddr (not emitExp + GetAddress) to avoid taking the address
          -- of a stack copy of the struct (which would give the copy's address, not the
          -- original's).  For example, `p->s.arr` must not create a copy of `p->s` first.
          let (baseAddr, _, lvalInstrs) ← emitLvalAddr st base
          if memberOffset == 0 then
            return (baseAddr, .Pointer elemTyp, lvalInstrs)
          else
            let memberAddrTmp := Val.Var (← makeTemporary (.Pointer elemTyp))
            return (memberAddrTmp, .Pointer elemTyp,
              lvalInstrs ++ [.AddPtr baseAddr (.Constant 1) memberOffset memberAddrTmp])
      | _ =>
          -- Scalar member: CopyFromOffset(baseName, offset, dst).
          let dst := Val.Var (← makeTemporary memberTyp)
          return (dst, memberTyp, baseInstrs ++ [.CopyFromOffset baseName memberOffset dst])
  -- Chapter 18: `p->member` — read a struct/union member through a pointer.
  -- For scalar members: compute member address (AddPtr if offset ≠ 0), then Load.
  -- For aggregate members: load each scalar leaf into a fresh temp.
  -- For array members: return the member address as a pointer.
  | .Arrow ptr member => do
      let s ← get
      let (ptrVal, ptrTyp, ptrInstrs) ← emitExp st ptr
      let structTyp : AST.Typ := match ptrTyp with | .Pointer t => t | _ => .Int
      let tag := match structTyp with | .Struct t | .Union t => t | _ => ""
      let (memberTyp, memberOffset) := lookupMember s.typeTable tag member
      -- Compute address of the member: ptrVal + memberOffset
      let (memberAddr, memberAddrInstrs) ← do
        if memberOffset == 0 then
          pure (ptrVal, [])
        else do
          let addrTmp := Val.Var (← makeTemporary (.Pointer memberTyp))
          pure (addrTmp, [.AddPtr ptrVal (.Constant 1) memberOffset addrTmp])
      match memberTyp with
      | .Struct innerTag | .Union innerTag =>
          -- Aggregate member via pointer: load each scalar field into a fresh temp.
          let tmpName ← makeTemporary memberTyp
          let loadInstrs ← emitAggregateLoadAt memberAddr innerTag 0 0 tmpName
          return (.Var tmpName, memberTyp, ptrInstrs ++ memberAddrInstrs ++ loadInstrs)
      | .Array elemTyp _ =>
          -- Array member via pointer: the member address IS the array start.
          return (memberAddr, .Pointer elemTyp, ptrInstrs ++ memberAddrInstrs)
      | _ =>
          -- Scalar member via pointer: Load from member address.
          let dst := Val.Var (← makeTemporary memberTyp)
          return (dst, memberTyp,
            ptrInstrs ++ memberAddrInstrs ++ [.Load memberAddr dst])
  -- Chapter 15: Subscript is fully desugared by TypeCheck into Dereference(Binary.Add(...)).
  -- This case is unreachable in a well-typed program, but exhaustive matching requires it.
  | .Subscript _ _ => return (.Constant 0, .Int, [])
  -- Chapter 17: SizeOf/SizeOfT are fully evaluated at compile time in TypeCheck
  -- (replaced with ConstULong constants). These cases are unreachable in a well-typed program.
  | .SizeOf _  => return (.Constant 0, .ULong, [])
  | .SizeOfT _ => return (.Constant 0, .ULong, [])

end

-- ---------------------------------------------------------------------------
-- Statement and block-item lowering
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Initializer lowering (Chapter 15)
-- ---------------------------------------------------------------------------

/-- Chapter 15/18: emit CopyToOffset instructions for a compound initializer.
    Handles arrays (existing Ch15 behaviour) and struct/union types (Ch18).
    `varName`:    the root aggregate variable name.
    `arrTyp`:     the type of the current aggregate (array, struct, or union).
    `byteOffset`: starting byte offset within `varName` for this aggregate.
    `inits`:      the list of sub-initializers (TypeCheck has zero-padded them). -/
private partial def emitArrayInit (st : Semantics.SymbolTable) (varName : String)
    (arrTyp : AST.Typ) (byteOffset : Int) (inits : List AST.Initializer)
    : GenM (List Instruction) := do
  -- Helper to emit one scalar leaf initializer at a concrete byte offset.
  let emitScalar (e : AST.Exp) (absOff : Int) : GenM (List Instruction) := do
    let (val, typ, evalInstrs) ← emitExp st e
    let tmp ← makeTemporary typ
    -- Route through a typed temporary so CodeGen knows the correct AsmType
    -- (valAsmType on a raw Constant uses magnitude, which can misclassify
    -- small ULong/Long values as Longword).
    return (evalInstrs ++ [.Copy val (.Var tmp),
                            Instruction.CopyToOffset (.Var tmp) varName absOff])
  match arrTyp with
  | .Struct tag =>
      -- Chapter 18: struct compound initializer.
      -- TypeCheck has zero-padded `inits` to sd.members.length elements.
      -- Each init corresponds to the matching member; use member offsets from TypeTable.
      let state ← get
      match Semantics.lookupTypeTable state.typeTable tag with
      | none => return []
      | some sd =>
          (sd.members.zip inits).foldlM (fun acc (m, init) => do
            let memberOff := byteOffset + (m.offset : Int)
            let memberInstrs ← match init with
              | .SingleInit e => emitScalar e memberOff
              | .CompoundInit subInits =>
                  -- Nested aggregate member (nested struct/union or array member)
                  emitArrayInit st varName m.typ memberOff subInits
            return acc ++ memberInstrs) []
  | .Union tag =>
      -- Chapter 18: union compound initializer.
      -- TypeCheck ensures `inits` has exactly ONE element (for the first member).
      -- All union members alias the same bytes, so only the first member is written.
      let state ← get
      match Semantics.lookupTypeTable state.typeTable tag with
      | none => return []
      | some sd =>
          match sd.members.head?, inits.head? with
          | some m, some init => do
              let memberOff := byteOffset + (m.offset : Int)
              match init with
              | .SingleInit e => emitScalar e memberOff
              | .CompoundInit subInits =>
                  emitArrayInit st varName m.typ memberOff subInits
          | _, _ => return []
  | _ =>
      -- Array type (or scalar fallback): iterate at fixed element strides.
      let elemTyp : AST.Typ := match arrTyp with | .Array e _ => e | t => t
      -- For struct/union element types the stride comes from the TypeTable;
      -- for scalar types use sizeOf directly.
      let state ← get
      let elemSize : Int :=
        match elemTyp with
        | .Struct tag | .Union tag =>
            match Semantics.lookupTypeTable state.typeTable tag with
            | some sd => (sd.size : Int)
            | none    => 0
        | t => (t.sizeOf : Int)
      -- Lean 4 does not have `List.enum`; track the index in the accumulator.
      let (_, allInstrs) ← inits.foldlM (fun (acc : Int × List Instruction) init => do
        let (i, instrs) := acc
        let elemOffset := byteOffset + i * elemSize
        let elemInstrs ← match init with
          | .SingleInit e => emitScalar e elemOffset
          | .CompoundInit subInits =>
              -- Nested aggregate (e.g. a row of a 2-D array or a struct element)
              emitArrayInit st varName elemTyp elemOffset subInits
        return (i + 1, instrs ++ elemInstrs)) (0, [])
      return allInstrs

/-- Chapter 15: lower a local-variable initializer into TACKY instructions.
    - `SingleInit e` on a scalar variable: emit `Copy val (Var varName)`.
    - `CompoundInit inits` on an array variable: call `emitArrayInit` to
      emit one `CopyToOffset` per (leaf) element. -/
private def emitInitializer (st : Semantics.SymbolTable) (varName : String)
    (varTyp : AST.Typ) : AST.Initializer → GenM (List Instruction)
  | .SingleInit e => do
      let (val, _, instrs) ← emitExp st e
      return instrs ++ [.Copy val (.Var varName)]
  | .CompoundInit inits =>
      emitArrayInit st varName varTyp 0 inits

private def emitForInit (st : Semantics.SymbolTable) : AST.ForInit → GenM (List Instruction)
  | .InitExp none   => return []
  | .InitExp (some e) => do
      let (_, _, instrs) ← emitExp st e
      return instrs
  | .InitDecl decl =>
      match decl.init with
      | none   => return []
      | some init =>
          -- Chapter 15: initializer may be SingleInit (scalar) or CompoundInit (array)
          emitInitializer st decl.name decl.typ init

mutual

private partial def emitStatement (st : Semantics.SymbolTable) (funcName : String)
    : AST.Statement → GenM (List Instruction)
  -- Chapter 17: Return is now Option Exp — void functions use `Return none`.
  | .Return none => do
      -- `return;` in a void function: emit Return with no value.
      return [.Return none]
  | .Return (some e) => do
      let (v, _, instrs) ← emitExp st e
      return instrs ++ [.Return (some v)]
  | .Expression e => do
      let (_, _, instrs) ← emitExp st e
      return instrs
  | .If cond thenStmt none => do
      let endLabel ← makeLabel "if_end"
      let (c, _, condInstrs) ← emitExp st cond
      let thenInstrs ← emitStatement st funcName thenStmt
      return condInstrs ++ [.JumpIfZero c endLabel] ++ thenInstrs ++ [.Label endLabel]
  | .If cond thenStmt (some elseStmt) => do
      let elseLabel ← makeLabel "if_else"
      let endLabel  ← makeLabel "if_end"
      let (c, _, condInstrs) ← emitExp st cond
      let thenInstrs ← emitStatement st funcName thenStmt
      let elseInstrs ← emitStatement st funcName elseStmt
      return condInstrs ++ [.JumpIfZero c elseLabel] ++ thenInstrs ++
             [.Jump endLabel, .Label elseLabel] ++ elseInstrs ++ [.Label endLabel]
  | .Compound items => do
      let instrs ← items.foldlM (fun acc item => do
        return acc ++ (← emitBlockItem st funcName item)) []
      return instrs
  | .While cond body (some base) => do
      let cntLabel := "cnt_" ++ base
      let brkLabel := "brk_" ++ base
      let (c, _, condInstrs) ← emitExp st cond
      let bodyInstrs ← emitStatement st funcName body
      return [.Label cntLabel] ++ condInstrs ++ [.JumpIfZero c brkLabel] ++
             bodyInstrs ++ [.Jump cntLabel, .Label brkLabel]
  | .While _ _ none => return []
  | .DoWhile body cond (some base) => do
      let startLabel := "start_" ++ base
      let cntLabel   := "cnt_"   ++ base
      let brkLabel   := "brk_"   ++ base
      let bodyInstrs ← emitStatement st funcName body
      let (c, _, condInstrs) ← emitExp st cond
      return [.Label startLabel] ++ bodyInstrs ++ [.Label cntLabel] ++
             condInstrs ++ [.JumpIfNotZero c startLabel, .Label brkLabel]
  | .DoWhile _ _ none => return []
  | .For init cond post body (some base) => do
      let startLabel := "start_" ++ base
      let cntLabel   := "cnt_"   ++ base
      let brkLabel   := "brk_"   ++ base
      let initInstrs ← emitForInit st init
      let condInstrs ← match cond with
        | none   => pure []
        | some c => do
            let (v, _, instrs) ← emitExp st c
            pure (instrs ++ [.JumpIfZero v brkLabel])
      let bodyInstrs ← emitStatement st funcName body
      let postInstrs ← match post with
        | none   => pure []
        | some e => do
            let (_, _, instrs) ← emitExp st e
            pure instrs
      return initInstrs ++ [.Label startLabel] ++ condInstrs ++ bodyInstrs ++
             [.Label cntLabel] ++ postInstrs ++ [.Jump startLabel, .Label brkLabel]
  | .For _ _ _ _ none => return []
  | .Break (some base)    => return [.Jump ("brk_" ++ base)]
  | .Break none           => return []
  | .Continue (some base) => return [.Jump ("cnt_" ++ base)]
  | .Continue none        => return []
  | .Switch exp body (some base) cases => do
      let brkLabel := "brk_" ++ base
      let (v, vTyp, expInstrs) ← emitExp st exp
      let jumpTable ← cases.foldlM (fun acc (caseVal, caseLbl) => do
          match caseVal with
          | some n => do
              let caseConst := Val.Constant n
              let tmp := Val.Var (← makeTemporary .Int)
              pure (acc ++ [.Binary .Equal v caseConst tmp,
                            .JumpIfNotZero tmp caseLbl])
          | none => pure (acc ++ [.Jump caseLbl])) []
      let noDefault   := cases.all (fun (v, _) => v.isSome)
      let fallThrough := if noDefault then [Instruction.Jump brkLabel] else []
      let bodyInstrs ← emitStatement st funcName body
      return expInstrs ++ jumpTable ++ fallThrough ++ bodyInstrs ++ [.Label brkLabel]
  | .Switch _ _ none _ => return []
  | .Case _ body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement st funcName body)
  | .Case _ _ none => return []
  | .Default body (some lbl) => do
      return [.Label lbl] ++ (← emitStatement st funcName body)
  | .Default _ none => return []
  | .Labeled label stmt => do
      let stmtInstrs ← emitStatement st funcName stmt
      return [.Label (funcName ++ "." ++ label)] ++ stmtInstrs
  | .Goto label =>
      return [.Jump (funcName ++ "." ++ label)]
  | .Null => return []

private partial def emitBlockItem (st : Semantics.SymbolTable) (funcName : String)
    : AST.BlockItem → GenM (List Instruction)
  | .S stmt => emitStatement st funcName stmt
  | .D decl =>
      match decl.init with
      | none   => return []
      | some init =>
          -- Chapter 15: initializer may be SingleInit (scalar) or CompoundInit (array)
          emitInitializer st decl.name decl.typ init
  | .FD _ => return []
  -- Chapter 18: struct/union declaration inside a block — no instructions needed.
  -- The type information is already captured in the TypeTable (built by VarResolution).
  | .SD _ _ => return []

end

-- ---------------------------------------------------------------------------
-- Function and program emission
-- ---------------------------------------------------------------------------

private def emitFunctionDef (st : Semantics.SymbolTable) (f : AST.FunctionDef)
    (isGlobal : Bool) : GenM FunctionDef := do
  let paramNames := f.params.map (·.2)
  let body ← f.body.foldlM (fun acc item => do
    return acc ++ (← emitBlockItem st f.name item)) []
  -- Chapter 17: void functions get an implicit `return;` (no value).
  -- Non-void functions get an implicit `return 0;` (C §5.1.2.2.3: main returns 0;
  -- other non-void functions have undefined behavior if they fall off the end, but
  -- we emit 0 for safety).
  let implicitReturn : Instruction :=
    if f.retTyp == .Void then .Return none else .Return (some (.Constant 0))
  return { name := f.name, params := paramNames,
           body := body ++ [implicitReturn],
           global := isGlobal }

-- ---------------------------------------------------------------------------
-- Static variable initializer helpers (Chapter 15)
-- ---------------------------------------------------------------------------

/-- Chapter 15: produce `List StaticInit` for a zero-valued aggregate or scalar.
    Arrays use a single `ZeroInit(n)` entry for efficiency (emits `.zero n`).
    Chapter 16: char types use a single zero byte.
    Chapter 18: struct/union uses `ZeroInit(totalSize)` looked up from TypeTable. -/
private def zeroStaticInits (tt : Semantics.TypeTable) : AST.Typ → List StaticInit
  | .Int             => [.IntInit 0]
  | .Long            => [.LongInit 0]
  | .UInt            => [.UIntInit 0]
  | .ULong           => [.ULongInit 0]
  | .Double          => [.DoubleInit 0.0]
  | .Pointer _       => [.ULongInit 0]      -- null pointer = 0 (64-bit)
  | .Array elemTyp n => [.ZeroInit (elemTyp.sizeOf * n)]   -- .zero totalBytes
  | .Char | .SChar   => [.CharInit 0]       -- Chapter 16: 1-byte signed char
  | .UChar           => [.UCharInit 0]      -- Chapter 16: 1-byte unsigned char
  | .Void            => []                  -- Chapter 17: void has no data; unreachable in practice
  -- Chapter 18: struct/union — emit `.zero totalSize` using TypeTable for the size.
  | .Struct tag | .Union tag =>
      match Semantics.lookupTypeTable tt tag with
      | some sd => [.ZeroInit sd.size]
      | none    => [.ZeroInit 0]

/-- Convert a single scalar `SymbolTable.InitialValue` + type to one `StaticInit`.
    Used for non-array static variables.
    Chapter 16: char types use CharInit/UCharInit. -/
private def scalarInitToStaticInit (t : AST.Typ) (n : Int) : StaticInit :=
  match t with
  | .Int             => .IntInit n
  | .Long            => .LongInit n
  | .UInt            => .UIntInit n
  | .ULong           => .ULongInit n
  | .Pointer _       => .ULongInit n   -- pointer stored as 64-bit value
  | .Char | .SChar   => .CharInit n    -- Chapter 16: 1-byte signed char
  | .UChar           => .UCharInit n   -- Chapter 16: 1-byte unsigned char
  | _                => .IntInit n     -- shouldn't happen for non-double scalar

/-- Chapter 15: convert a `SymbolTable.InitialValue` to `List StaticInit`.
    Handles scalars, doubles, tentative (zero-initialized), and arrays.
    For array elements, recurses into the element type.
    Chapter 16: handles `StringInitial s` for char arrays.
    Chapter 18: handles struct/union types (zero-initialized via ZeroInit). -/
private partial def initValToStaticInits (tt : Semantics.TypeTable) (t : AST.Typ)
    : Semantics.InitialValue → GenM (List StaticInit)
  | .Initial n        => return [scalarInitToStaticInit t n]
  | .DoubleInitial f  => return [.DoubleInit f]
  | .Tentative        => return (zeroStaticInits tt t)    -- go to .bss
  | .NoInitializer    => return (zeroStaticInits tt t)    -- extern-only: treated as zero
  | .PointerInitial s => do
      -- Chapter 18: static char* member initialized with a string literal.
      -- Intern the string to get a StaticConstant label, then emit a .quad pointer.
      let label ← internString s
      return [.PointerInit label]
  | .ArrayInitial elemInits =>
      match t with
      | .Array e _ =>
          -- Existing array behavior: all elements share the same element type.
          elemInits.foldlM (fun acc iv => do
            let inits ← initValToStaticInits tt e iv
            return acc ++ inits) []
      | .Struct tag | .Union tag =>
          -- Chapter 18: struct/union with member-by-member `ArrayInitial` produced
          -- by `extractInitialValue`.  Each entry in `elemInits` corresponds to one
          -- struct/union member; use the TypeTable for offsets and padding.
          match Semantics.lookupTypeTable tt tag with
          | none => return []
          | some sd => do
              if tag.startsWith "union." then
                -- Union: only the first member's bytes are initialised;
                -- the rest are padded to the union's total size.
                match sd.members.head?, elemInits.head? with
                | some m, some iv => do
                    let memberSize   := typeSizeOf tt m.typ
                    let memberInits  ← initValToStaticInits tt m.typ iv
                    let trailing     :=
                      if sd.size > memberSize then [StaticInit.ZeroInit (sd.size - memberSize)] else []
                    return (memberInits ++ trailing)
                | _, _ => return (if sd.size > 0 then [StaticInit.ZeroInit sd.size] else [])
              else do
                -- Struct: emit each member at its declared offset,
                -- inserting ZeroInit for any inter-member padding gaps.
                let (finalOffset, structInits) ← (sd.members.zip elemInits).foldlM
                    (fun (acc : Nat × List StaticInit) (m, iv) => do
                      let (curOff, accInits) := acc
                      let memberOff  := m.offset
                      -- Pad any gap between end of previous member and start of this one.
                      let padInits   :=
                        if memberOff > curOff then [StaticInit.ZeroInit (memberOff - curOff)] else []
                      let memberInits ← initValToStaticInits tt m.typ iv
                      let newOff     := memberOff + typeSizeOf tt m.typ
                      return (newOff, accInits ++ padInits ++ memberInits)) (0, [])
                -- Trailing padding to reach the struct's total declared size.
                let trailing :=
                  if sd.size > finalOffset then [StaticInit.ZeroInit (sd.size - finalOffset)] else []
                return (structInits ++ trailing)
      | _ =>
          -- Scalar fallback (compound initializer on a scalar type; shouldn't occur).
          elemInits.foldlM (fun acc iv => do
            let inits ← initValToStaticInits tt t iv
            return acc ++ inits) []
  | .StringInitial s =>
      -- Chapter 16: char array initialized from a string literal.
      -- Emit StringInit + zero padding based on the array's declared size.
      let size := match t with | .Array _ n => n | _ => s.length + 1
      let hasNull := size > s.length
      let truncated := String.ofList (s.toList.take size)   -- truncate if array is smaller than string
      let padCount  := if size > s.length + 1 then size - s.length - 1 else 0
      let mainInit  := StaticInit.StringInit truncated hasNull
      let padInit   := if padCount > 0 then [StaticInit.ZeroInit padCount] else []
      return ([mainInit] ++ padInit)

/-- Collect static variable entries from the symbol table and emit them as
    TackyTopLevel.StaticVariable items (monadic to support PointerInitial).
    Chapter 15: init is now `List StaticInit` to support arrays.
    `NoInitializer` variables (pure `extern` declarations without a local definition)
    are skipped entirely — they must not produce any data section output, since the
    definition lives in another translation unit (or library).  Emitting a `.zero n`
    for a huge `extern` array would cause the assembler/OS to crash trying to
    reserve exabytes of address space.
    Chapter 18: `tt` is used to look up struct/union sizes for ZeroInit and PointerInitial. -/
private def emitStaticVars (symTable : Semantics.SymbolTable)
    (tt : Semantics.TypeTable) : GenM (List TackyTopLevel) := do
  let entries := symTable.filter fun (_, entry) =>
    match entry.type, entry.attrs with
    | .Obj _, .Static .NoInitializer _ => false  -- extern-only declaration: no local def
    | .Obj _, .Static _ _              => true
    | _, _                             => false
  entries.foldlM (fun acc (name, entry) => do
    match entry.type, entry.attrs with
    | .Obj t, .Static iv isGlobal =>
        let inits ← initValToStaticInits tt t iv
        return acc ++ [.StaticVariable name isGlobal t inits]
    | _, _ => return acc) []

/-- Entry point for the IR generation pass.
    Returns `(Program, typeEnv, floatConsts, needsNegZero, strConsts)`.
    Chapter 16: `strConsts` is a list of (label, content) for string literals;
    the Driver will create `AssemblyAST.StaticConstant` items for each.
    Chapter 18: `tt` is the TypeTable for struct/union layout lookups. -/
def emitProgram (p : AST.Program) (symTable : Semantics.SymbolTable)
    (initCounter : Nat := 0) (tt : Semantics.TypeTable := [])
    : Program × List (String × AST.Typ) × List (String × Float) × Bool × List (String × String) :=
  let astFuncs := p.topLevels.filterMap fun tl =>
    match tl with
    | .FunDef fd     => some fd
    | .FunDecl _     => none
    | .VarDecl _     => none
    | .StructDecl _ _ => none   -- Chapter 18: struct/union type declarations have no body
  let action : GenM (List TackyTopLevel) := do
    -- Emit function bodies.
    let funcItems ← astFuncs.foldlM (fun acc fd => do
      let isGlobal : Bool := match Semantics.lookupSym symTable fd.name with
        | some { attrs := .FunAttr _ g, .. } => g
        | _ => true
      let tackyFd ← emitFunctionDef symTable fd isGlobal
      return acc ++ [.Function tackyFd]) []
    -- Emit static variables inside the monad so PointerInitial can call internString.
    let staticItems ← emitStaticVars symTable tt
    return (funcItems ++ staticItems)
  let initState : GenState :=
    { counter := initCounter, typeEnv := [], floatConsts := [], needsNegZero := false,
      strConsts := [], typeTable := tt }
  let (allItems, finalState) := action.run initState
  ({ topLevels := allItems },
   finalState.typeEnv,
   finalState.floatConsts,
   finalState.needsNegZero,
   finalState.strConsts)

end Tacky
