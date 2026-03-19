import AST.AST
import Tacky.Tacky
import Semantics.SymbolTable

/-
  IR generation pass: converts AST.Program → Tacky.Program.

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
                  to their string contents, for emission as read-only `.rodata`. -/
private structure GenState where
  counter      : Nat
  typeEnv      : List (String × AST.Typ)
  floatConsts  : List (String × Float)
  needsNegZero : Bool
  strConsts    : List (String × String)  -- Chapter 16: label → raw string content

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
-- Expression lowering
-- ---------------------------------------------------------------------------

/-- Lower an AST expression to TACKY instructions.
    Returns `(result_val, result_type, instructions)`.

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
      match op, t1, t2 with
      | .Add, .Pointer elemTyp, _ => do
          -- ptr + int: AddPtr(ptr_val, idx_val, scale, dst)
          let scale := (elemTyp.sizeOf : Int)
          let dst   := Val.Var (← makeTemporary t1)
          return (dst, t1, instrs1 ++ instrs2 ++ [.AddPtr src1 src2 scale dst])
      | .Add, _, .Pointer elemTyp => do
          -- int + ptr: commutative; put the pointer first
          let scale := (elemTyp.sizeOf : Int)
          let dst   := Val.Var (← makeTemporary t2)
          return (dst, t2, instrs1 ++ instrs2 ++ [.AddPtr src2 src1 scale dst])
      | .Subtract, .Pointer elemTyp, .Pointer _ => do
          -- ptr - ptr: (ptr1 - ptr2) / elemSize → result type Long (ptrdiff_t)
          let scale   := (elemTyp.sizeOf : Int)
          let diffTmp := Val.Var (← makeTemporary .Long)
          let dst     := Val.Var (← makeTemporary .Long)
          return (dst, .Long,
            instrs1 ++ instrs2 ++
            [.Binary .Subtract src1 src2 diffTmp,
             .Binary .Divide diffTmp (.Constant scale) dst])
      | .Subtract, .Pointer elemTyp, _ => do
          -- ptr - int: negate the index, then AddPtr(ptr, neg_idx, scale, dst)
          let scale  := (elemTyp.sizeOf : Int)
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
  | .Assignment _ _ => return (.Constant 0, .Int, [])
  | .PostfixIncr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      match varTyp with
      | .Pointer elemTyp =>
          -- Chapter 15: pointer increment advances by sizeof(*ptr), not by 1 byte.
          -- Use AddPtr so CodeGen emits a scaled leaq instead of a raw addq $1.
          let scale : Int := elemTyp.sizeOf
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
      let addInstrs : List Instruction :=
        match valTyp with
        | .Pointer elemTyp =>
            -- Chapter 15: (*p)++ where *p is a pointer — advance by element size
            [.AddPtr loadedVal (.Constant 1) elemTyp.sizeOf loadedVal]
        | _ =>
            [.Binary .Add loadedVal (.Constant 1) loadedVal]
      return (oldVal, valTyp,
        ptrInstrs ++ [.Load ptrVal loadedVal, .Copy loadedVal oldVal] ++
        addInstrs ++ [.Store loadedVal ptrVal])
  | .PostfixIncr _ => return (.Constant 0, .Int, [])
  | .PostfixDecr (.Var v) => do
      let varTyp : AST.Typ := match Semantics.lookupSym st v with
        | some { type := .Obj t, .. } => t
        | _ => .Int
      let tmp ← makeTemporary varTyp
      match varTyp with
      | .Pointer elemTyp =>
          -- Chapter 15: pointer decrement advances by -sizeof(*ptr)
          let scale : Int := elemTyp.sizeOf
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
      let subInstrs : List Instruction :=
        match valTyp with
        | .Pointer elemTyp =>
            -- Chapter 15: (*p)-- where *p is a pointer — decrement by element size
            [.AddPtr loadedVal (.Constant (-1)) elemTyp.sizeOf loadedVal]
        | _ =>
            [.Binary .Subtract loadedVal (.Constant 1) loadedVal]
      return (oldVal, valTyp,
        ptrInstrs ++ [.Load ptrVal loadedVal, .Copy loadedVal oldVal] ++
        subInstrs ++ [.Store loadedVal ptrVal])
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
  -- Chapter 14: address-of: `&e` allocates a pointer-typed temporary for the address.
  -- Chapter 15: array-to-pointer decay — `&arr` where `arr : Array(T, n)` gives
  -- `Pointer(T)` (pointer to the first element), NOT `Pointer(Array(T, n))`.
  -- This is how TypeCheck encodes array decay via AddrOf when desugaring subscripts:
  --   arr[i]  →  Dereference(Binary(Add, AddrOf(arr), i))
  -- where AddrOf(arr) must have type Pointer(T) for the scale to be T.sizeOf (not
  -- Array(T,n).sizeOf which would be wrong and produce an invalid leaq scale).
  | .AddrOf inner => do
      let (srcVal, srcTyp, instrs) ← emitExp st inner
      -- For array types: decay to pointer-to-element, not pointer-to-array
      let ptrTyp : AST.Typ := match srcTyp with
        | .Array elemTyp _ => .Pointer elemTyp   -- decay: Array(T,n) → Pointer(T)
        | t                => .Pointer t          -- normal address-of
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
  -- Chapter 15: Subscript is fully desugared by TypeCheck into Dereference(Binary.Add(...)).
  -- This case is unreachable in a well-typed program, but exhaustive matching requires it.
  | .Subscript _ _ => return (.Constant 0, .Int, [])
  -- Chapter 17: SizeOf/SizeOfT are fully evaluated at compile time in TypeCheck
  -- (replaced with ConstULong constants). These cases are unreachable in a well-typed program.
  | .SizeOf _  => return (.Constant 0, .ULong, [])
  | .SizeOfT _ => return (.Constant 0, .ULong, [])

-- ---------------------------------------------------------------------------
-- Statement and block-item lowering
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Initializer lowering (Chapter 15)
-- ---------------------------------------------------------------------------

/-- Chapter 15: emit CopyToOffset instructions for a compound array initializer.
    Recurses into nested sub-initializers for multi-dimensional arrays.
    `varName`:    the root array variable name.
    `arrTyp`:     the type of the current aggregate (array of elemTyp).
    `byteOffset`: starting byte offset within `varName` for this aggregate.
    `inits`:      the list of sub-initializers (one per element). -/
private partial def emitArrayInit (st : Semantics.SymbolTable) (varName : String)
    (arrTyp : AST.Typ) (byteOffset : Int) (inits : List AST.Initializer)
    : GenM (List Instruction) := do
  let elemTyp  : AST.Typ := match arrTyp with | .Array e _ => e | t => t
  let elemSize : Int := elemTyp.sizeOf
  -- Lean 4 does not have `List.enum`; use `foldlM` with a manual counter instead.
  let (_, allInstrs) ← inits.foldlM (fun (acc : Int × List Instruction) init => do
    let (i, instrs) := acc
    let elemOffset := byteOffset + i * elemSize
    let elemInstrs ← match init with
      | .SingleInit e => do
          -- Leaf element: evaluate and store at the computed byte offset.
          -- IMPORTANT: if the result is a Constant, its AsmType is determined by
          -- magnitude alone in CodeGen (valAsmType), which misclassifies small
          -- ULong/Long values (e.g. 100ul → Longword instead of Quadword).
          -- To preserve the element type, always route through a typed temporary
          -- so that CodeGen can look up the correct AsmType from the backend sym table.
          let (val, typ, evalInstrs) ← emitExp st e
          let tmp ← makeTemporary typ
          -- Use `pure` (not `return`) so the result stays as `List Instruction`
          -- without accidentally returning from the outer foldlM callback.
          pure (evalInstrs ++ [.Copy val (.Var tmp),
                               Instruction.CopyToOffset (.Var tmp) varName elemOffset])
      | .CompoundInit subInits =>
          -- Nested aggregate (e.g. a row of a 2-D array)
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
    Chapter 16: char types use a single zero byte. -/
private def zeroStaticInits : AST.Typ → List StaticInit
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
    Chapter 16: handles `StringInitial s` for char arrays. -/
private def initValToStaticInits (t : AST.Typ)
    : Semantics.InitialValue → List StaticInit
  | .Initial n        => [scalarInitToStaticInit t n]
  | .DoubleInitial f  => [.DoubleInit f]
  | .Tentative        => zeroStaticInits t    -- go to .bss
  | .NoInitializer    => zeroStaticInits t    -- extern-only: treated as zero
  | .ArrayInitial elemInits =>
      let elemTyp := match t with | .Array e _ => e | et => et
      elemInits.foldl (fun acc iv => acc ++ initValToStaticInits elemTyp iv) []
  | .StringInitial s =>
      -- Chapter 16: char array initialized from a string literal.
      -- Emit StringInit + zero padding based on the array's declared size.
      let size := match t with | .Array _ n => n | _ => s.length + 1
      let hasNull := size > s.length
      let truncated := String.ofList (s.toList.take size)   -- truncate if array is smaller than string
      let padCount  := if size > s.length + 1 then size - s.length - 1 else 0
      let mainInit  := StaticInit.StringInit truncated hasNull
      let padInit   := if padCount > 0 then [StaticInit.ZeroInit padCount] else []
      [mainInit] ++ padInit

/-- Collect static variable entries from the symbol table and emit them as
    TackyTopLevel.StaticVariable items.
    Chapter 15: init is now `List StaticInit` to support arrays.
    `NoInitializer` variables (pure `extern` declarations without a local definition)
    are skipped entirely — they must not produce any data section output, since the
    definition lives in another translation unit (or library).  Emitting a `.zero n`
    for a huge `extern` array would cause the assembler/OS to crash trying to
    reserve exabytes of address space. -/
private def emitStaticVars (symTable : Semantics.SymbolTable) : List TackyTopLevel :=
  symTable.filterMap fun (name, entry) =>
    match entry.type, entry.attrs with
    | .Obj _, .Static .NoInitializer _ => none   -- extern-only declaration: no local def
    | .Obj t, .Static iv isGlobal =>
        let inits := initValToStaticInits t iv
        some (.StaticVariable name isGlobal t inits)
    | _, _ => none

/-- Entry point for the IR generation pass.
    Returns `(Program, typeEnv, floatConsts, needsNegZero, strConsts)`.
    Chapter 16: `strConsts` is a list of (label, content) for string literals;
    the Driver will create `AssemblyAST.StaticConstant` items for each. -/
def emitProgram (p : AST.Program) (symTable : Semantics.SymbolTable)
    (initCounter : Nat := 0)
    : Program × List (String × AST.Typ) × List (String × Float) × Bool × List (String × String) :=
  let astFuncs := p.topLevels.filterMap fun tl =>
    match tl with
    | .FunDef fd  => some fd
    | .FunDecl _  => none
    | .VarDecl _  => none
  let action : GenM (List TackyTopLevel) :=
    astFuncs.foldlM (fun acc fd => do
      let isGlobal : Bool := match Semantics.lookupSym symTable fd.name with
        | some { attrs := .FunAttr _ g, .. } => g
        | _ => true
      let tackyFd ← emitFunctionDef symTable fd isGlobal
      return acc ++ [.Function tackyFd]) []
  let initState : GenState :=
    { counter := initCounter, typeEnv := [], floatConsts := [], needsNegZero := false, strConsts := [] }
  let (funcItems, finalState) := action.run initState
  let staticItems := emitStaticVars symTable
  ({ topLevels := funcItems ++ staticItems },
   finalState.typeEnv,
   finalState.floatConsts,
   finalState.needsNegZero,
   finalState.strConsts)

end Tacky
