import AST.AST
import Semantics.SymbolTable

/-
  Semantic analysis pass: identifier resolution and symbol-table construction.
  Chapter 11 rewrite.

  Chapter 11 changes:
    - `IdentType.Obj(typ)` replaces the former plain `Int`, carrying the variable's
      declared scalar type (`Int` or `Long`).
    - `IdentType.Fun` now carries `(paramCount, paramTypes, retTyp)` so that the
      TypeCheck pass can look up function signatures.
    - `Declaration.typ` is used to set the symbol-table type for variables.
    - `FunctionDef.params` and `FunctionDecl.params` are now `List (Typ × String)`;
      the renamed param is added to the sym table with its declared type.
    - Static initializer constants may be `ConstInt` or `ConstLong`; both are
      accepted and stored as `Initial(n)` in the sym table.

  All other behaviour (renaming, linkage rules, conflict detection) is unchanged.
-/

namespace Semantics

/-- The monad used during identifier resolution: state + errors. -/
private abbrev VarM := StateT Nat (Except String)

-- ---------------------------------------------------------------------------
-- Identifier map types
-- ---------------------------------------------------------------------------

/-- Information stored per identifier in the IdentMap. -/
private inductive IdentInfo where
  | Var : String → IdentInfo         -- variable: unique renamed name
  | Fun : Nat → Bool → IdentInfo     -- function: param count, has definition?
  deriving Repr

/-- Entry for an identifier in the identifier map. -/
private structure IdentEntry where
  info        : IdentInfo
  fromCurrent : Bool
  hasLinkage  : Bool := false

private abbrev IdentMap := List (String × IdentEntry)

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

/-- Scoped tag map entry: maps an original tag name to a unique internal name.
    `fromCurrent` is true when the tag was defined in the current scope;
    it is cleared when entering a new inner scope (like identMap). -/
private structure TagEntry where
  uniqueName  : String
  fromCurrent : Bool

/-- Tag map: parallel to IdentMap but for struct/union tags.
    Associates original tag names (e.g. "struct.pair1") with unique internal
    names (e.g. "struct.pair1.3") and scope membership flags.
    Block-scope struct definitions get unique names; file-scope definitions
    are inserted into the TypeTable directly (no renaming needed). -/
private abbrev TagMap := List (String × TagEntry)

private structure VarState where
  counter   : Nat
  symTable  : SymbolTable
  typeTable : TypeTable   -- Chapter 18: struct/union tag → StructDef layout
  tagMap    : TagMap      -- Chapter 18: scoped struct/union tag name resolution

private abbrev VarM2 := StateT VarState (Except String)

private def makeUnique (original : String) : VarM2 String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  return s!"{original}.{s.counter}"

private def lookupIdent (identMap : IdentMap) (name : String) : Option IdentEntry :=
  match identMap.find? (fun p => p.1 == name) with
  | some (_, entry) => some entry
  | none            => none

/-- Clear all `fromCurrent` flags when entering an inner scope. -/
private def enterScope (identMap : IdentMap) : IdentMap :=
  identMap.map (fun (name, entry) => (name, { entry with fromCurrent := false }))

/-- Clear all `fromCurrent` flags in the tagMap when entering an inner block scope.
    This allows inner blocks to shadow outer-scope struct/union tag definitions. -/
private def enterTagScope (tagMap : TagMap) : TagMap :=
  tagMap.map (fun (name, entry) => (name, { entry with fromCurrent := false }))

/-- Extract just the parameter names from a typed param list. -/
private def paramNames (params : List (AST.Typ × String)) : List String :=
  params.map (·.2)

/-- Check that parameter names are unique. -/
private def checkUniqueParams (params : List (AST.Typ × String)) : Except String Unit := do
  let names := paramNames params
  let rec check : List String → Except String Unit
    | []     => .ok ()
    | p :: rest =>
        if rest.contains p then .error s!"Duplicate parameter name '{p}'"
        else check rest
  check names

-- ---------------------------------------------------------------------------
-- Symbol-table helpers
-- ---------------------------------------------------------------------------

private def addSym (name : String) (entry : SymbolEntry) : VarM2 Unit :=
  modify fun s => { s with symTable := insertSym s.symTable name entry }

private def getSym (name : String) : VarM2 (Option SymbolEntry) := do
  let s ← get
  return lookupSym s.symTable name

-- ---------------------------------------------------------------------------
-- Chapter 18: TypeTable helpers and struct/union layout computation
-- ---------------------------------------------------------------------------

/-- Insert a struct/union definition into the TypeTable in state. -/
private def addTypDef (tag : String) (sd : StructDef) : VarM2 Unit :=
  modify fun s => { s with typeTable := insertTypeTable s.typeTable tag sd }

/-- Look up a struct/union definition from the TypeTable in state. -/
private def getTypDef (tag : String) : VarM2 (Option StructDef) := do
  return lookupTypeTable (← get).typeTable tag

-- ---------------------------------------------------------------------------
-- Chapter 18: TagMap helpers for scoped struct/union tag name resolution
-- ---------------------------------------------------------------------------

/-- Look up an original tag name in the tagMap (from VarState). -/
private def lookupTag (tag : String) : VarM2 (Option TagEntry) := do
  return (← get).tagMap.find? (fun p => p.1 == tag) |>.map (·.2)

/-- Add a tag-to-uniqueName mapping to the tagMap in VarState. -/
private def addTag (tag : String) (uniqueName : String) : VarM2 Unit :=
  modify fun s =>
    let entry : TagEntry := { uniqueName, fromCurrent := true }
    { s with tagMap := (tag, entry) :: s.tagMap }

/-- Extract the raw name from a fully-qualified tag key like "struct.X" or "union.X". -/
private def tagBaseName (tag : String) : String :=
  if tag.startsWith "struct." then (tag.drop 7).toString
  else if tag.startsWith "union." then (tag.drop 6).toString
  else tag

/-- Return the opposite-kind tag key: "struct.X" → "union.X" and vice versa. -/
private def tagOpposite (tag : String) : String :=
  if tag.startsWith "struct." then "union." ++ tagBaseName tag
  else if tag.startsWith "union." then "struct." ++ tagBaseName tag
  else tag

/-- In C, struct tags and union tags share the same tag namespace (C §6.2.3).
    Declaring 'struct X' and 'union X' in the same scope is illegal.
    This function checks for such a conflict.
    `inCurrentScopeOnly`: if true, only flag a conflict when the opposite tag
    has fromCurrent=true (used for block-scope checks); if false, flag any
    presence of the opposite tag in the tagMap (used for file-scope checks). -/
private def checkTagKindConflict (tag : String) (inCurrentScopeOnly : Bool) : VarM2 Unit := do
  let otherTag := tagOpposite tag
  let tm := (← get).tagMap
  let conflict :=
    if inCurrentScopeOnly then tm.any (fun p => p.1 == otherTag && p.2.fromCurrent)
    else tm.any (fun p => p.1 == otherTag)
  if conflict then
    let base := tagBaseName tag
    let kind1 := if tag.startsWith "struct." then "struct" else "union"
    let kind2 := if kind1 == "struct" then "union" else "struct"
    throw s!"Conflicting tag declarations: '{kind1} {base}' conflicts with '{kind2} {base}' in the same scope"

/-- Resolve a type by replacing struct/union tags with their unique names from
    the current tagMap.  Called by resolveBlockItem on declared types, and by
    resolveExp on Cast/SizeOfT target types.
    Throws if a struct/union tag is not found in the tagMap — this catches uses
    of completely undeclared struct/union types (e.g. `sizeof(struct undecl)`).
    Also detects when the opposite-kind tag (e.g. 'union X') shadows the
    requested tag ('struct X') — in C, struct and union tags share a namespace,
    so a union tag in an inner scope prevents access to the outer struct tag. -/
private partial def resolveTyp (typ : AST.Typ) : VarM2 AST.Typ := do
  match typ with
  | .Struct tag =>
      let tm := (← get).tagMap
      let otherTag := tagOpposite tag
      -- Find positions in the tagMap (ordered most-recently-added first).
      -- A lower index = more recently declared (inner scope).
      let thisIdx  := tm.findIdx? (fun p => p.1 == tag)
      let otherIdx := tm.findIdx? (fun p => p.1 == otherTag)
      match thisIdx with
      | none => throw s!"Undeclared struct tag '{tag}'"
      | some si =>
          -- Check if the opposite-kind (union) tag was declared more recently.
          -- If the union appears at a lower index, it shadows the struct tag.
          if otherIdx.any (· < si) then
            let base := tagBaseName tag
            throw s!"'union {base}' in inner scope shadows 'struct {base}'"
          -- Retrieve the actual entry using find? (avoids Inhabited requirement).
          match tm.find? (fun p => p.1 == tag) with
          | some (_, e) => return .Struct e.uniqueName
          | none        => throw s!"Internal error: struct tag '{tag}' disappeared"
  | .Union tag =>
      let tm := (← get).tagMap
      let otherTag := tagOpposite tag
      let thisIdx  := tm.findIdx? (fun p => p.1 == tag)
      let otherIdx := tm.findIdx? (fun p => p.1 == otherTag)
      match thisIdx with
      | none => throw s!"Undeclared union tag '{tag}'"
      | some ui =>
          -- Check if the opposite-kind (struct) tag was declared more recently.
          if otherIdx.any (· < ui) then
            let base := tagBaseName tag
            throw s!"'struct {base}' in inner scope shadows 'union {base}'"
          match tm.find? (fun p => p.1 == tag) with
          | some (_, e) => return .Union e.uniqueName
          | none        => throw s!"Internal error: union tag '{tag}' disappeared"
  | .Array elem n => return .Array (← resolveTyp elem) n
  | .Pointer t    => return .Pointer (← resolveTyp t)
  | other         => return other

/-- Round `n` up to the nearest multiple of `align`. -/
private def alignUpVR (n : Nat) (align : Nat) : Nat :=
  if align == 0 then n else ((n + align - 1) / align) * align

/-- Return the size in bytes of a type, consulting the TypeTable for struct/union types.
    Returns `none` if the type is incomplete (e.g. `void`, or a struct with no definition). -/
private partial def typSizeVR (tt : TypeTable) : AST.Typ → Option Nat
  | .Int | .UInt           => some 4
  | .Long | .ULong         => some 8
  | .Double                => some 8
  | .Pointer _             => some 8
  | .Char | .SChar | .UChar => some 1
  | .Void                  => none  -- incomplete
  | .Array elem n          =>
      match typSizeVR tt elem with
      | some s => some (s * n)
      | none   => none
  | .Struct tag | .Union tag =>
      match lookupTypeTable tt tag with
      | some sd => some sd.size
      | none    => none  -- forward-declared but not yet defined

/-- Return the alignment in bytes of a type, consulting the TypeTable for struct/union types. -/
private partial def typAlignVR (tt : TypeTable) : AST.Typ → Nat
  | .Int | .UInt           => 4
  | .Long | .ULong         => 8
  | .Double                => 8
  | .Pointer _             => 8
  | .Char | .SChar | .UChar => 1
  | .Void                  => 1
  | .Array elem _          =>
      -- C standard: alignment of an array type equals the alignment of its element type.
      -- The 16-byte stack-slot alignment for large local arrays is an ABI/PseudoReplace
      -- concern, NOT a C-type property. Using 16 here inflates struct sizes (e.g.,
      -- `struct { char arr[19]; }` becomes 32 bytes instead of 19).
      typAlignVR tt elem
  | .Struct tag | .Union tag =>
      match lookupTypeTable tt tag with
      | some sd => sd.alignment
      | none    => 1

/-- Compute the `StructDef` layout for a struct or union given its member list.
    For a struct, members are laid out in order with appropriate padding.
    For a union, all members are at offset 0; the size is the largest member size
    padded to the overall alignment.
    Uses the current TypeTable (in state) to resolve member types. -/
private def computeStructLayout (members : List (AST.Typ × String)) (isUnion : Bool)
    : VarM2 StructDef := do
  let tt := (← get).typeTable
  -- Compute member sizes and alignments; reject void members.
  -- Check for duplicate member names.
  let memberNames := members.map (·.2)
  let rec checkDupNames : List String → VarM2 Unit
    | [] => pure ()
    | n :: rest =>
        if rest.contains n then throw s!"Duplicate member name '{n}' in struct/union"
        else checkDupNames rest
  checkDupNames memberNames
  let memberInfos : List (AST.Typ × String × Nat × Nat) ← members.mapM fun (typ, name) => do
    -- Validate that the member type is complete (incomplete struct/union/void members are illegal).
    if typ == .Void then
      throw s!"Struct/union member '{name}' has void type"
    let sz ← match typSizeVR tt typ with
      | some s => pure s
      | none   => throw s!"Struct/union member '{name}' has incomplete type"
    let al  := typAlignVR tt typ
    return (typ, name, sz, al)
  -- Overall struct/union alignment = max of all member alignments (minimum 1).
  let structAlign : Nat := memberInfos.foldl (fun acc (_, _, _, al) => Nat.max acc al) 1
  -- Layout: place each member at the next aligned offset.
  if isUnion then
    -- Union: all members at offset 0; overall size = largest member, padded to alignment.
    let maxSz : Nat := memberInfos.foldl (fun acc (_, _, sz, _) => Nat.max acc sz) 0
    let totalSize := alignUpVR maxSz structAlign
    let memberEntries : List MemberEntry := memberInfos.map fun (typ, name, _, _) =>
      { name, typ, offset := 0 }
    return { members := memberEntries, size := totalSize, alignment := structAlign }
  else
    -- Struct: sequential layout with alignment padding between members.
    let (memberEntries, finalOffset) : List MemberEntry × Nat := memberInfos.foldl
      (fun (acc : List MemberEntry × Nat) (typ, name, sz, al) =>
        let (entries, currentOffset) := acc
        let paddedOffset := alignUpVR currentOffset al
        (entries ++ [{ name, typ, offset := paddedOffset }], paddedOffset + sz))
      ([], 0)
    let totalSize := alignUpVR finalOffset structAlign
    return { members := memberEntries, size := totalSize, alignment := structAlign }

/-- Process a struct/union definition: compute its layout and insert it into the TypeTable.
    If the tag has already been defined, this is a redefinition error.
    If the tag only had a forward reference (no body yet), this fills it in.
    `tag`     = fully qualified tag name (e.g. "struct.S" or "union.U")
    `members` = the member list from the parser (type × name)
    `isUnion` = true for union, false for struct -/
private def processStructDef (tag : String) (members : List (AST.Typ × String))
    (isUnion : Bool) : VarM2 Unit := do
  -- Check for redefinition.
  let existing ← getTypDef tag
  match existing with
  | some _ => throw s!"Struct/union '{tag}' is defined more than once"
  | none   => pure ()
  -- Compute layout and insert.
  let sd ← computeStructLayout members isUnion
  addTypDef tag sd

-- ---------------------------------------------------------------------------
-- Helper: extract integer value from a constant expression (for static inits)
-- ---------------------------------------------------------------------------

/-- True for the three char variants: Char, SChar, UChar. -/
private def isCharType : AST.Typ → Bool
  | .Char | .SChar | .UChar => true
  | _                       => false

/-- Extract the raw integer value from a constant expression.
    Accepts integer literals and (via truncation) ConstDouble literals.
    C allows initializing `static int i = 4.9;` — the double is truncated
    towards zero to produce the integer value (here, 4). -/
private def extractConst : AST.Exp → Option Int
  | .Constant (.ConstInt n)    => some n
  | .Constant (.ConstLong n)   => some n
  | .Constant (.ConstUInt n)   => some n     -- Chapter 12
  | .Constant (.ConstULong n)  => some n     -- Chapter 12
  | .Constant (.ConstDouble f) =>            -- Chapter 13: implicit float→int truncation
      -- Truncation towards zero, matching C's (int)f cast semantics.
      -- For non-negative f: use UInt64 truncation, then promote to Int.
      -- For negative f: negate, truncate, negate result.
      -- NaN, ±Inf, and out-of-range produce 0 (undefined in C, 0 is safe).
      if f.isNaN || f.isInf then some 0
      else if f >= 0.0 then some (Float.toUInt64 f).toNat
      else some (-(Float.toUInt64 (-f)).toNat)
  | .Constant (.ConstChar n)   => some n     -- Chapter 16
  | .Constant (.ConstUChar n)  => some n     -- Chapter 16
  | _                          => none

/-- Extract the raw float value from a constant expression.
    Used for static double variable initializers (Chapter 13).
    Integer constants are implicitly converted to the nearest double
    using IEEE 754 hardware rounding (via UInt64.toFloat / Float.ofInt). -/
private def extractDoubleConst : AST.Exp → Option Float
  | .Constant (.ConstDouble f) => some f
  | .Constant (.ConstInt n)    => some (Float.ofInt n)    -- implicit int→double
  | .Constant (.ConstLong n)   => some (Float.ofInt n)    -- implicit long→double
  | .Constant (.ConstUInt n)   => some (Float.ofInt n)    -- implicit uint→double
  | .Constant (.ConstULong n)  => some (Float.ofInt n)    -- implicit ulong→double
  | .Constant (.ConstChar n)   => some (Float.ofInt n)    -- Chapter 16: implicit char→double
  | .Constant (.ConstUChar n)  => some (Float.ofInt n)    -- Chapter 16: implicit uchar→double
  | _                          => none

/-- Extract an `InitialValue` from a constant expression given the variable's (scalar) type.
    For integer types: wraps in `Initial(n)`.
    For `Double`:     wraps in `DoubleInitial(f)`.  (Chapter 13) -/
private def extractScalarInitialValue (varTyp : AST.Typ) (e : AST.Exp) : Option InitialValue :=
  match varTyp with
  | .Double =>
      match extractDoubleConst e with
      | some f => some (.DoubleInitial f)
      | none   => none
  | _ =>
      match extractConst e with
      | some n => some (.Initial n)
      | none   => none

-- `partial def zeroInitialValue` requires Lean to know that `InitialValue` is `Inhabited`
-- (needed so `partial` can produce a default value on non-termination).
private instance : Inhabited InitialValue := ⟨.Initial 0⟩

/-- Return the zero-valued `InitialValue` for any type (scalar, array, or struct/union).
    For arrays, recursively creates an `ArrayInitial` so that nested partial
    initializers are correctly zero-padded all the way down.
    Chapter 18: for struct/union types, creates `ArrayInitial` of per-member zeros.
    C §6.7.9p10: unlisted sub-aggregate elements are zero-initialized as if
    they had static storage duration. -/
private partial def zeroInitialValue (tt : TypeTable) : AST.Typ → InitialValue
  | .Double    => .DoubleInitial 0.0
  | .Array e n => .ArrayInitial (List.replicate n (zeroInitialValue tt e))
  | .Struct tag | .Union tag =>
      -- Chapter 18: zero each member according to the TypeTable layout.
      -- For a union, this produces one zero per member; `initValToStaticInits`
      -- knows to emit only the first member and then zero-pad to the union size.
      match lookupTypeTable tt tag with
      | some sd => .ArrayInitial (sd.members.map fun m => zeroInitialValue tt m.typ)
      | none    => .Initial 0   -- unknown struct: fall back to scalar zero
  | _          => .Initial 0  -- all integer/pointer/char types zero as 0

/-- Extract an `InitialValue` from an `Initializer` for a static variable.
    Handles both scalar `SingleInit` and array `CompoundInit`.
    Missing array elements are zero-initialized.
    Returns `none` if any element is not a constant expression.
    Chapter 16: `SingleInit(StringLiteral s)` for char array types → `StringInitial s`.
    Chapter 18: `CompoundInit` for struct/union types → `ArrayInitial` of member values. -/
private partial def extractInitialValue (tt : TypeTable) (varTyp : AST.Typ)
    : AST.Initializer → Option InitialValue
  | .SingleInit (.StringLiteral s) =>
      -- Chapter 16: string literal as char array initializer → StringInitial.
      -- Only valid for Array(Char/SChar/UChar, n).  All other types → type error.
      -- Chapter 18: string literal initializing a char* pointer → PointerInitial.
      match varTyp with
      | .Array elemTyp size =>
          if isCharType elemTyp then
            -- C §6.7.9p14: the string (including null terminator) must fit in the array.
            -- `s.length` is the number of non-null chars; +1 for the null terminator.
            -- Exception: `size = 0` means an unsized `char arr[] = "..."` declaration
            -- whose size will be filled in by `fixupCharArraySize` before we get here.
            if size > 0 && s.length > size then none   -- too long → signal error
            else some (.StringInitial s)
          else none
      | .Pointer elemTyp =>
          -- `static char *p = "hello"` or a struct member `char *msg = "text"`:
          -- store as PointerInitial; TackyGen will intern the string and emit `.quad label`.
          -- String literals have type `char *`, so only `Pointer Char` (plain char) is
          -- compatible; `Pointer SChar` and `Pointer UChar` are distinct types and
          -- cannot be implicitly initialized from a string literal.
          if elemTyp == .Char then some (.PointerInitial s)
          else none
      | _ => none
  | .SingleInit e =>
      -- Chapter 15: array types cannot be initialized with a scalar expression.
      -- Chapter 18: struct/union types also cannot be initialized with a scalar expression.
      -- Return `none` so the caller throws a meaningful error.
      match varTyp with
      | .Array _ _ | .Struct _ | .Union _ => none
      | _ => extractScalarInitialValue varTyp e
  | .CompoundInit inits =>
      match varTyp with
      | .Array elemTyp size =>
          -- Build an InitialValue per element; missing elements are zero
          let rec extractElems (remaining : List AST.Initializer) (idx : Nat)
              : Option (List InitialValue) :=
            -- If we've filled all array slots but there are extra initializers, that's an error.
            -- Return `none` to signal failure (caller will produce an appropriate error message).
            if idx >= size then
              if remaining.isEmpty then some [] else none
            else
              let elemInit := remaining.head?
              let ivOpt : Option InitialValue := match elemInit with
                | none    => some (zeroInitialValue tt elemTyp)  -- zero-pad
                | some ei => extractInitialValue tt elemTyp ei
              match ivOpt with
              | none    => none  -- non-constant element
              | some iv => match extractElems (remaining.tail) (idx + 1) with
                  | none     => none
                  | some rest => some (iv :: rest)
          match extractElems inits 0 with
          | some ivs => some (.ArrayInitial ivs)
          | none     => none
      -- Chapter 18: struct/union compound initializer.
      -- Struct: one InitialValue per member; missing members are zero-initialized.
      -- Struct: C §6.7.9: each member is initialized in order; missing members are zero-initialized.
      | .Struct tag =>
          match lookupTypeTable tt tag with
          | none => none   -- undefined struct; will be caught elsewhere
          | some sd =>
              let members := sd.members
              if inits.length > members.length then none
              else
                -- For each provided init, extract its InitialValue using the member type.
                -- Missing members default to the zero InitialValue for their type.
                let (result, _) := members.foldl (fun (acc : Option (List InitialValue) × List AST.Initializer)
                    m =>
                  let (ivs?, remaining) := acc
                  match ivs? with
                  | none => (none, remaining)  -- already failed
                  | some ivs =>
                      let (thisInit, rest) := match remaining with
                        | [] => (none, [])
                        | h :: t => (some h, t)
                      let iv := match thisInit with
                        | none      => some (zeroInitialValue tt m.typ)  -- zero missing members
                        | some init => extractInitialValue tt m.typ init
                      (iv.map (ivs ++ [·]), rest)) (some [], inits)
                result.map .ArrayInitial
      -- Union: C §6.7.9p17: only the FIRST member is initialized.
      -- At most one initializer element is allowed.  TackyGen's `initValToStaticInits`
      -- handles the trailing-bytes padding to the union's total size.
      | .Union tag =>
          match lookupTypeTable tt tag with
          | none => none   -- undefined union; will be caught elsewhere
          | some sd =>
              let members := sd.members
              -- Reject more than one initializer element.
              if inits.length > 1 then none
              else
                match members.head? with
                | none => some (.ArrayInitial [])   -- empty union (degenerate)
                | some firstMember =>
                    let firstIV := match inits.head? with
                      | none      => some (zeroInitialValue tt firstMember.typ)
                      | some init => extractInitialValue tt firstMember.typ init
                    firstIV.map (fun iv => .ArrayInitial [iv])
      | _ => none  -- compound init for non-array/non-struct type is a type error (caught in TypeCheck)

-- ---------------------------------------------------------------------------
-- Array-size inference for char arrays (Chapter 16)
-- ---------------------------------------------------------------------------

/-- For `char arr[] = "hello"` (Array(charTyp, 0) with SingleInit(StringLiteral s)),
    infer the array size as `s.length + 1` (for the null terminator).
    For all other declaration forms, the declaration is returned unchanged. -/
private def fixupCharArraySize (decl : AST.Declaration) : AST.Declaration :=
  match decl.typ, decl.init with
  | .Array elemTyp 0, some (.SingleInit (.StringLiteral s)) =>
      if isCharType elemTyp then
        { decl with typ := .Array elemTyp (s.length + 1) }
      else
        decl  -- non-char element type: leave as-is (will be caught by TypeCheck)
  | _, _ => decl

-- ---------------------------------------------------------------------------
-- File-scope variable declaration processing
-- ---------------------------------------------------------------------------

/-- Recursively check that no `Array` type in the type tree has an incomplete element type.
    C §6.7.5.2: "The element type shall not be an incomplete or function type."
    This must hold even if the array appears behind a pointer (e.g. `union u (*p)[3]`
    where `union u` is incomplete is illegal because the array element type is incomplete).
    Pointers to (plain) incomplete types are still allowed (e.g. `struct s *p`). -/
private partial def containsArrayOfIncomplete (tt : TypeTable) : AST.Typ → Bool
  | .Array elem _ =>
      -- The element type of an array must be complete.
      (typSizeVR tt elem).isNone || containsArrayOfIncomplete tt elem
  | .Pointer inner => containsArrayOfIncomplete tt inner  -- recurse inside pointer
  | _ => false

/-- Check that a type is complete (has a known size) for non-extern variable declarations.
    Pointers to incomplete types are allowed (pointer is always 8 bytes).
    Arrays of incomplete types, and incomplete struct/union values, are illegal. -/
private def requireCompleteVarType (tt : TypeTable) (name : String) (typ : AST.Typ) : VarM2 Unit := do
  match typSizeVR tt typ with
  | none   => throw s!"Variable '{name}' has incomplete type"
  | some _ =>
      -- Even if the top-level type has a known size (e.g. pointer), check that
      -- no nested array has an incomplete element type (C §6.7.5.2).
      if containsArrayOfIncomplete tt typ then
        throw s!"Variable '{name}' has an array type with incomplete element type"

/-- Process a file-scope variable declaration, applying linkage rules. -/
private def processFileScopeVar (decl : AST.Declaration) : VarM2 String := do
  -- Chapter 16: fix up array size for `char arr[] = "hello"` before type checks.
  let decl := fixupCharArraySize decl
  let name := decl.name
  let varType := decl.typ  -- Chapter 11: use declared type
  -- Chapter 18: get the TypeTable for struct/union initializer extraction.
  let tt := (← get).typeTable
  match decl.storageClass with
  | some .Extern => do
      if decl.init.isSome then
        throw s!"Variable '{name}' declared extern with an initializer at file scope"
      let existing ← getSym name
      match existing with
      | none =>
          addSym name { type := .Obj varType, attrs := .Static .NoInitializer true }
      | some { type := .Fun _ _ _, .. } =>
          throw s!"'{name}' was previously declared as a function"
      | some { type := existingType, .. } =>
          -- Chapter 11: extern declaration must agree with any existing type
          if existingType != .Obj varType then
            throw s!"Variable '{name}' declared with conflicting types"
          pure ()
      return name
  | some .Static => do
      -- Chapter 18: static (non-extern) variables must have complete types.
      requireCompleteVarType tt name varType
      let existing ← getSym name
      match existing with
      | some { type := .Fun _ _ _, .. } =>
          throw s!"'{name}' was previously declared as a function"
      | some { type := existingType, attrs := .Static _ true, .. } =>
          if existingType != .Obj varType then
            throw s!"Variable '{name}' declared with conflicting types"
          throw s!"Variable '{name}' declared with both internal and external linkage"
      | some { type := existingType, attrs := .Static init _, .. } =>
          if existingType != .Obj varType then
            throw s!"Variable '{name}' declared with conflicting types"
          match decl.init, init with
          | some _, .Initial _ | some _, .DoubleInitial _ | some _, .ArrayInitial _
          | some _, .StringInitial _ =>
              throw s!"Variable '{name}' has conflicting definitions"
          | some i, _ =>
              match extractInitialValue tt varType i with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv false }
              | none => throw s!"Initializer for static variable '{name}' must be a constant"
          | none, .Initial _ | none, .DoubleInitial _ | none, .ArrayInitial _
          | none, .StringInitial _ =>
              pure ()
          | none, _ =>
              pure ()
      | _ =>
          match decl.init with
          | some i =>
              match extractInitialValue tt varType i with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv false }
              | none => throw s!"Initializer for file-scope static variable '{name}' must be a constant"
          | none =>
              addSym name { type := .Obj varType, attrs := .Static .Tentative false }
      return name
  | none => do
      -- Chapter 18: non-extern variables must have complete types.
      requireCompleteVarType tt name varType
      let existing ← getSym name
      match existing with
      | some { type := .Fun _ _ _, .. } =>
          throw s!"'{name}' was previously declared as a function"
      | some { attrs := .Static _ false, .. } =>
          throw s!"Variable '{name}' declared with both internal and external linkage"
      | some { type := existingType, attrs := .Static init true, .. } =>
          if existingType != .Obj varType then
            throw s!"Variable '{name}' declared with conflicting types"
          match decl.init, init with
          | some _, .Initial _ | some _, .DoubleInitial _ | some _, .ArrayInitial _
          | some _, .StringInitial _ =>
              throw s!"Variable '{name}' has conflicting definitions"
          | some i, _ =>
              match extractInitialValue tt varType i with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv true }
              | none => throw s!"Initializer for file-scope variable '{name}' must be a constant"
          | none, .NoInitializer =>
              addSym name { type := .Obj varType, attrs := .Static .Tentative true }
          | none, _ =>
              pure ()
      | _ =>
          match decl.init with
          | some i =>
              match extractInitialValue tt varType i with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv true }
              | none => throw s!"Initializer for file-scope variable '{name}' must be a constant"
          | none =>
              addSym name { type := .Obj varType, attrs := .Static .Tentative true }
      return name

-- ---------------------------------------------------------------------------
-- File-scope function declaration processing
-- ---------------------------------------------------------------------------

/-- Compute the global flag for a file-scope function declaration.
    Returns the resolved `isGlobal` value. -/
private def processFileScopeFun (name : String) (paramCount : Nat)
    (paramTypes : List AST.Typ) (retTyp : AST.Typ) (isDef : Bool)
    (sc : Option AST.StorageClass) : VarM2 Bool := do
  let isStaticDecl := sc == some .Static
  let existing ← getSym name
  match existing with
  | some { type := .Obj _, .. } =>
      throw s!"'{name}' was previously declared as a variable"
  | some { type := .Fun existingCount existingParamTypes existingRetTyp,
           attrs := .FunAttr existingDefined existingGlobal } =>
      if existingCount != paramCount then
        throw s!"Conflicting declarations of '{name}': different parameter counts"
      -- Chapter 11: parameter types and return type must agree across all declarations
      if existingParamTypes != paramTypes || existingRetTyp != retTyp then
        throw s!"Conflicting declarations of '{name}': different types"
      if existingDefined && isDef then
        throw s!"Function '{name}' is defined more than once"
      if isStaticDecl && existingGlobal then
        throw s!"Conflicting linkage for function '{name}'"
      let isGlobal := if isStaticDecl then false else existingGlobal
      let newDefined := existingDefined || isDef
      addSym name { type := .Fun paramCount paramTypes retTyp, attrs := .FunAttr newDefined isGlobal }
      return isGlobal
  | _ =>
      let isGlobal := !isStaticDecl
      addSym name { type := .Fun paramCount paramTypes retTyp, attrs := .FunAttr isDef isGlobal }
      return isGlobal

-- ---------------------------------------------------------------------------
-- Expression resolution
-- ---------------------------------------------------------------------------

/-- Rename all variables in an expression according to `identMap`. -/
private def resolveExp (identMap : IdentMap) : AST.Exp → VarM2 AST.Exp
  | .Constant c       => return .Constant c
  | .StringLiteral s  => return .StringLiteral s  -- Chapter 16: no variables to rename
  | .Var v            => do
      match lookupIdent identMap v with
      | none => throw s!"Undeclared variable '{v}'"
      | some { info := .Fun _ _, .. } => throw s!"'{v}' is a function, not a variable"
      | some { info := .Var renamed, .. } => return .Var renamed
  | .Cast t e       => return .Cast (← resolveTyp t) (← resolveExp identMap e)
  | .Unary op e     => return .Unary op (← resolveExp identMap e)
  | .Binary op l r  => return .Binary op (← resolveExp identMap l) (← resolveExp identMap r)
  | .Assignment left right => do
      match left with
      | .Var _         => pure ()
      | .Dereference _ => pure ()   -- Chapter 14: dereference is a valid lvalue
      | .Subscript _ _ => pure ()   -- Chapter 15: subscript is a valid lvalue
      | .Dot _ _       => pure ()   -- Chapter 18: struct member access is a valid lvalue
      | .Arrow _ _     => pure ()   -- Chapter 18: pointer member access is a valid lvalue
      | _              => throw "Invalid lvalue in assignment"
      return .Assignment (← resolveExp identMap left) (← resolveExp identMap right)
  | .Conditional cond e1 e2 =>
      return .Conditional (← resolveExp identMap cond)
                          (← resolveExp identMap e1)
                          (← resolveExp identMap e2)
  | .PostfixIncr e  => do
      let e' ← resolveExp identMap e
      match e' with
      | .Var _         => return .PostfixIncr e'
      | .Dereference _ => return .PostfixIncr e'   -- Chapter 14: (*p)++
      | .Subscript _ _ => return .PostfixIncr e'   -- Chapter 15: a[i]++
      | .Dot _ _       => return .PostfixIncr e'   -- Chapter 18: s.x++
      | .Arrow _ _     => return .PostfixIncr e'   -- Chapter 18: p->x++
      | _              => throw "Invalid lvalue in postfix increment"
  | .PostfixDecr e  => do
      let e' ← resolveExp identMap e
      match e' with
      | .Var _         => return .PostfixDecr e'
      | .Dereference _ => return .PostfixDecr e'   -- Chapter 14: (*p)--
      | .Subscript _ _ => return .PostfixDecr e'   -- Chapter 15: a[i]--
      | .Dot _ _       => return .PostfixDecr e'   -- Chapter 18: s.x--
      | .Arrow _ _     => return .PostfixDecr e'   -- Chapter 18: p->x--
      | _              => throw "Invalid lvalue in postfix decrement"
  -- Chapter 14: address-of and dereference
  | .AddrOf e      => return .AddrOf      (← resolveExp identMap e)
  | .Dereference e => return .Dereference (← resolveExp identMap e)
  -- Chapter 15: array subscript — both sides resolved; subscript is an lvalue
  | .Subscript arr idx =>
      return .Subscript (← resolveExp identMap arr) (← resolveExp identMap idx)
  -- Chapter 17: sizeof — the inner expression/type need variable resolution on sub-expressions
  | .SizeOf e     => return .SizeOf  (← resolveExp identMap e)
  | .SizeOfT t    => return .SizeOfT (← resolveTyp t)  -- resolve struct tags in the type
  -- Chapter 18: member access operators.
  -- The member name is a field name, not a variable — no renaming needed.
  -- We only recurse into the struct expression to rename any variables it contains.
  | .Dot e member   => return .Dot   (← resolveExp identMap e) member
  | .Arrow e member => return .Arrow (← resolveExp identMap e) member
  | .FunCall f args => do
      match lookupIdent identMap f with
      | none => throw s!"Undeclared function '{f}'"
      | some { info := .Var _, .. } => throw s!"'{f}' is a variable, not a function"
      | some { info := .Fun paramCount _, .. } =>
          if args.length != paramCount then
            throw s!"Wrong number of arguments for '{f}': expected {paramCount}, got {args.length}"
          let args' ← args.mapM (resolveExp identMap)
          return .FunCall f args'

-- ---------------------------------------------------------------------------
-- Initializer resolution (must come after resolveExp)
-- ---------------------------------------------------------------------------

/-- Rename all variables in an initializer according to `identMap`.
    Chapter 15: recurses into `CompoundInit` lists for array initializers. -/
private def resolveInitializer (identMap : IdentMap) : AST.Initializer → VarM2 AST.Initializer
  | .SingleInit e    => return .SingleInit (← resolveExp identMap e)
  | .CompoundInit is => return .CompoundInit (← is.mapM (resolveInitializer identMap))

-- ---------------------------------------------------------------------------
-- Statement and block-item resolution (mutually recursive)
-- ---------------------------------------------------------------------------

mutual

private partial def resolveForInit (identMap : IdentMap) : AST.ForInit → VarM2 (AST.ForInit × IdentMap)
  | .InitExp eOpt => do
      let eOpt' ← eOpt.mapM (resolveExp identMap)
      return (.InitExp eOpt', identMap)
  | .InitDecl decl => do
      if decl.storageClass.isSome then
        throw s!"Storage class specifier in for-loop initializer for '{decl.name}'"
      let (identMap', renamed) ← declareLocalVar identMap decl.name decl.typ
      -- Chapter 15: resolve initializer (SingleInit or CompoundInit)
      let init' ← decl.init.mapM (resolveInitializer identMap')
      return (.InitDecl { decl with name := renamed, init := init', storageClass := none }, identMap')

private partial def resolveStatement (identMap : IdentMap) : AST.Statement → VarM2 AST.Statement
  -- Chapter 17: Return is now `Option Exp` — void functions use `Return none`
  | .Return none     => return .Return none
  | .Return (some e) => return .Return (some (← resolveExp identMap e))
  | .Expression e => return .Expression (← resolveExp identMap e)
  | .If cond thenStmt elseOpt => do
      let cond' ← resolveExp identMap cond
      let then' ← resolveStatement identMap thenStmt
      match elseOpt with
      | none         => return .If cond' then' none
      | some elseStmt => do
          let else' ← resolveStatement identMap elseStmt
          return .If cond' then' (some else')
  | .Compound items => do
      let innerMap := enterScope identMap
      -- Save tagMap before entering the block; restore after so block-scope
      -- struct tag definitions don't leak into the outer scope.
      let savedTagMap := (← get).tagMap
      -- Clear fromCurrent flags so outer-scope struct tags can be shadowed by new definitions.
      modify fun s => { s with tagMap := enterTagScope s.tagMap }
      let items'   ← resolveBlockItems innerMap items
      modify fun s => { s with tagMap := savedTagMap }
      return .Compound items'
  | .While cond body label => do
      return .While (← resolveExp identMap cond) (← resolveStatement identMap body) label
  | .DoWhile body cond label => do
      return .DoWhile (← resolveStatement identMap body) (← resolveExp identMap cond) label
  | .For init cond post body label => do
      let innerMap := enterScope identMap
      -- Save and restore tagMap for the for-loop scope (init may define struct tags).
      let savedTagMap := (← get).tagMap
      -- Clear fromCurrent flags so the for-loop header can shadow outer struct tags.
      modify fun s => { s with tagMap := enterTagScope s.tagMap }
      let (init', innerMap')   ← resolveForInit innerMap init
      let cond'                ← cond.mapM (resolveExp innerMap')
      let post'                ← post.mapM (resolveExp innerMap')
      let body'                ← resolveStatement innerMap' body
      modify fun s => { s with tagMap := savedTagMap }
      return .For init' cond' post' body' label
  | .Break label    => return .Break label
  | .Continue label => return .Continue label
  | .Switch exp body label cases => do
      return .Switch (← resolveExp identMap exp) (← resolveStatement identMap body) label cases
  | .Case n body label => do
      return .Case n (← resolveStatement identMap body) label
  | .Default body label => do
      return .Default (← resolveStatement identMap body) label
  | .Labeled label stmt => do
      return .Labeled label (← resolveStatement identMap stmt)
  | .Goto label => return .Goto label
  | .Null       => return .Null

private partial def resolveBlockItem (identMap : IdentMap) : AST.BlockItem → VarM2 (IdentMap × AST.BlockItem)
  | .S stmt => do
      let stmt' ← resolveStatement identMap stmt
      return (identMap, .S stmt')
  | .D decl => do
      -- Resolve struct tags in the declared type (e.g. `struct s x` where `s` was
      -- defined in this block scope and got a unique internal name).
      let decl := { decl with typ := ← resolveTyp decl.typ }
      match decl.storageClass with
      | some .Extern => do
          if decl.init.isSome then
            throw s!"Variable '{decl.name}' declared extern with an initializer at block scope"
          match lookupIdent identMap decl.name with
          | some { fromCurrent := true, hasLinkage := false, .. } =>
              throw s!"extern declaration of '{decl.name}' follows a local variable in the same scope"
          | _ => pure ()
          let existingSym ← getSym decl.name
          match existingSym with
          | none =>
              addSym decl.name { type := .Obj decl.typ, attrs := .Static .NoInitializer true }
          | some { type := .Fun _ _ _, .. } =>
              throw s!"'{decl.name}' was previously declared as a function"
          | some { type := existingType, .. } =>
              -- Chapter 11: block-scope extern must agree with any existing type
              if existingType != .Obj decl.typ then
                throw s!"Variable '{decl.name}' declared with conflicting types"
              pure ()
          let entry : IdentEntry := { info := .Var decl.name, fromCurrent := true, hasLinkage := true }
          let identMap' := (decl.name, entry) :: identMap
          return (identMap', .D { decl with name := decl.name })
      | some .Static => do
          -- Chapter 16: fix up array size for `static char arr[] = "hello"`.
          let decl := fixupCharArraySize decl
          match lookupIdent identMap decl.name with
          | some { fromCurrent := true, .. } =>
              throw s!"Duplicate declaration of '{decl.name}' in the same scope"
          | _ => pure ()
          -- Chapter 18: get TypeTable for struct/union initializer extraction.
          let tt := (← get).typeTable
          let initVal : InitialValue ← do
            match decl.init with
            | none   => pure .Tentative
            | some i =>
                -- Chapter 13/15/16/18: use extractInitialValue to support int, double, array, string, and struct constants
                match extractInitialValue tt decl.typ i with
                | some iv => pure iv
                | none    => throw s!"Initializer for static variable '{decl.name}' must be a constant"
          let renamed ← makeUnique decl.name
          addSym renamed { type := .Obj decl.typ, attrs := .Static initVal false }
          let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
          let identMap' := (decl.name, entry) :: identMap
          return (identMap', .D { decl with name := renamed, init := none })
      | none => do
          -- Chapter 16: fix up array size for `char arr[] = "hello"`.
          let decl := fixupCharArraySize decl
          let (identMap', renamed) ← declareLocalVar identMap decl.name decl.typ
          -- Chapter 15/16: resolve initializer (may be SingleInit or CompoundInit)
          let init' ← decl.init.mapM (resolveInitializer identMap')
          return (identMap', .D { name := renamed, typ := decl.typ, init := init', storageClass := none })
  | .FD funDecl => do
      if funDecl.storageClass == some .Static then
        throw s!"Static storage class on block-scope function declaration for '{funDecl.name}'"
      liftM (checkUniqueParams funDecl.params)
      -- Resolve struct tags in the return type and parameter types.
      let retTyp' ← resolveTyp funDecl.retTyp
      let params' ← funDecl.params.mapM fun (t, n) => do return (← resolveTyp t, n)
      let funDecl := { funDecl with retTyp := retTyp', params := params' }
      let paramTypes := funDecl.params.map (·.1)
      let identMap' ← declareFun identMap funDecl.name funDecl.params.length false false
      let existingSym ← getSym funDecl.name
      match existingSym with
      | none =>
          addSym funDecl.name { type := .Fun funDecl.params.length paramTypes funDecl.retTyp,
                                attrs := .FunAttr false true }
      | some { type := .Obj _, .. } =>
          throw s!"'{funDecl.name}' was previously declared as a variable"
      | some { type := .Fun _ existingParamTypes existingRetTyp, .. } =>
          -- Chapter 18: block-scope re-declarations must match existing param/return types.
          -- Since struct tags are renamed uniquely per scope, different-scoped structs with
          -- the same name produce different unique strings, correctly flagging conflicts.
          if existingParamTypes != paramTypes || existingRetTyp != funDecl.retTyp then
            throw s!"Conflicting declarations of '{funDecl.name}': different types"
      return (identMap', .FD { funDecl with storageClass := none })
  | .SD tag membersOpt => do
      -- Chapter 18: block-scope struct/union declaration.
      -- Block-scope definitions always get a unique internal name so that:
      --   (a) the same tag in different blocks/functions don't collide in the TypeTable
      --   (b) block-scope 'struct s' is a distinct type from file-scope 'struct s'
      --
      -- C §6.2.3: struct and union tags share the same tag namespace.
      -- Declaring 'struct X' in a scope where 'union X' (or vice versa) is already
      -- visible in the SAME scope is illegal.
      checkTagKindConflict tag (inCurrentScopeOnly := true)
      match membersOpt with
      | some members =>
          let isUnion := tag.startsWith "union."
          -- Check if there's already a tag entry from the CURRENT scope (fromCurrent=true).
          let existingCurrentEntry := (← get).tagMap.find? (fun p => p.1 == tag && p.2.fromCurrent)
          let uniqueTag ← match existingCurrentEntry with
            | some (_, { uniqueName, .. }) =>
                -- Already declared in the current scope: either completing a forward decl,
                -- or a redefinition error.
                match ← getTypDef uniqueName with
                | some _ =>
                    throw s!"Struct/union '{tag}' is defined more than once in the same scope"
                | none =>
                    -- Forward declaration in this scope not yet completed: complete it.
                    pure uniqueName
            | none =>
                -- No entry from current scope: fresh definition; generate a unique name.
                makeUnique tag
          -- Add tag → uniqueTag to tagMap BEFORE resolving member types.
          -- This allows self-referential structs like `struct s { struct s *next; }`.
          addTag tag uniqueTag
          -- Resolve member types (may reference this struct or other block-scope structs).
          let resolvedMembers ← members.mapM fun (t, n) => do
            let t' ← resolveTyp t; return (t', n)
          processStructDef uniqueTag resolvedMembers isUnion
          -- Emit the SD item with the unique tag name so TackyGen/CodeGen see the right name.
          return (identMap, .SD uniqueTag (some resolvedMembers))
      | none =>
          -- Forward declaration `struct tag;` in block scope.
          -- C scoping: creates a NEW distinct type in the current scope, separate from any
          -- outer-scope or file-scope 'struct tag'.
          let existingCurrentEntry := (← get).tagMap.find? (fun p => p.1 == tag && p.2.fromCurrent)
          match existingCurrentEntry with
          | some _ => pure ()   -- already declared in this scope; idempotent
          | none   =>
              -- No entry from current scope: generate a fresh unique name for this type.
              -- This type is incomplete until a corresponding body `struct tag { ... }` is seen.
              let uniqueTag ← makeUnique tag
              addTag tag uniqueTag
          return (identMap, .SD tag none)

private partial def resolveBlockItems (identMap : IdentMap) : List AST.BlockItem → VarM2 (List AST.BlockItem)
  | []           => return []
  | item :: rest => do
      let (identMap', item') ← resolveBlockItem identMap item
      let rest'              ← resolveBlockItems identMap' rest
      return item' :: rest'

/-- Declare a local automatic variable; allocate a unique name. -/
private partial def declareLocalVar (identMap : IdentMap) (name : String)
    (typ : AST.Typ) : VarM2 (IdentMap × String) := do
  match lookupIdent identMap name with
  | some { fromCurrent := true, .. } =>
      throw s!"Duplicate declaration of '{name}' in the same scope"
  | _ => pure ()
  let renamed ← makeUnique name
  addSym renamed { type := .Obj typ, attrs := .Local }
  let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
  return ((name, entry) :: identMap, renamed)

/-- Validate and register a function in the identifier map. -/
private partial def declareFun (identMap : IdentMap) (name : String) (paramCount : Nat)
    (isDef : Bool) (isGlobal : Bool) : VarM2 IdentMap := do
  match lookupIdent identMap name with
  | some { info := .Var _, fromCurrent, .. } =>
      if fromCurrent then
        throw s!"'{name}' was previously declared as a variable"
      let entry : IdentEntry := { info := .Fun paramCount isDef, fromCurrent := true }
      return (name, entry) :: identMap
  | some { info := .Fun existingCount existingDefined, .. } =>
      if existingCount != paramCount then
        throw s!"Conflicting declarations of '{name}': different parameter counts"
      if existingDefined && isDef then
        throw s!"Function '{name}' is defined more than once"
      let newDefined := existingDefined || isDef
      let identMap' := identMap.map fun (n, e) =>
        if n == name then
          (n, { e with info := .Fun existingCount newDefined, fromCurrent := isDef || e.fromCurrent })
        else
          (n, e)
      return identMap'
  | none =>
      let entry : IdentEntry := { info := .Fun paramCount isDef, fromCurrent := true }
      return (name, entry) :: identMap

end  -- mutual

-- ---------------------------------------------------------------------------
-- Function-level resolution
-- ---------------------------------------------------------------------------

/-- Rename parameters to unique names and resolve the function body.
    Chapter 11: parameters carry types; each renamed param is added to the
    symbol table as `Obj(typ)` so TypeCheck and backend can look up its type. -/
private def resolveFunctionDef (identMap : IdentMap) (f : AST.FunctionDef) : VarM2 AST.FunctionDef := do
  liftM (checkUniqueParams f.params)
  let innerMap := enterScope identMap
  -- Each function body gets its own tag scope so block-scope struct definitions
  -- in one function don't conflict with same-named definitions in another function.
  let savedTagMap := (← get).tagMap
  -- Clear fromCurrent flags in tagMap so the function body can shadow outer struct tags.
  modify fun s => { s with tagMap := enterTagScope s.tagMap }
  -- Rename each (typ, paramName) pair to a unique name
  let (innerMap', renamedParams) ← f.params.foldlM
    (fun (acc : IdentMap × List (AST.Typ × String)) (typ, paramName) => do
      let (m, names) := acc
      -- Resolve struct tags in the parameter type.
      let typ' ← resolveTyp typ
      let renamed ← makeUnique paramName
      -- Register renamed param in symbol table with its declared type
      addSym renamed { type := .Obj typ', attrs := .Local }
      let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
      let m' := (paramName, entry) :: m
      return (m', names ++ [(typ', renamed)]))
    (innerMap, [])
  -- Resolve struct tags in return type.
  let retTyp' ← resolveTyp f.retTyp
  let body' ← resolveBlockItems innerMap' f.body
  -- Restore the tag map to the state before this function (pop function scope).
  modify fun s => { s with tagMap := savedTagMap }
  return { f with retTyp := retTyp', params := renamedParams, body := body' }

-- ---------------------------------------------------------------------------
-- Top-level item resolution
-- ---------------------------------------------------------------------------

private def resolveTopLevel (identMap : IdentMap) : AST.TopLevel → VarM2 (IdentMap × AST.TopLevel)
  | .VarDecl decl => do
      -- Chapter 16: fix up array size for `char arr[] = "hello"` before processing.
      let decl := fixupCharArraySize decl
      -- Resolve struct tags in the variable type (validates they're declared in tagMap).
      let resolvedTyp ← resolveTyp decl.typ
      let decl := { decl with typ := resolvedTyp }
      let _ ← processFileScopeVar decl
      let entry : IdentEntry := { info := .Var decl.name, fromCurrent := true, hasLinkage := true }
      let identMap' :=
        if identMap.any (fun p => p.1 == decl.name) then
          identMap.map fun (n, e) => if n == decl.name then (n, { e with fromCurrent := true }) else (n, e)
        else
          (decl.name, entry) :: identMap
      -- Chapter 15/16: resolve initializer (SingleInit or CompoundInit)
      let init' ← decl.init.mapM (resolveInitializer identMap')
      return (identMap', .VarDecl { decl with init := init' })
  | .FunDecl fd => do
      liftM (checkUniqueParams fd.params)
      -- Resolve struct tags in parameter and return types (validates they're declared).
      let resolvedParams ← fd.params.mapM fun (t, n) => do return (← resolveTyp t, n)
      let resolvedRetTyp ← resolveTyp fd.retTyp
      let paramTypes := resolvedParams.map (·.1)
      let fd' := { fd with params := resolvedParams, retTyp := resolvedRetTyp }
      let _ ← processFileScopeFun fd'.name fd'.params.length paramTypes resolvedRetTyp false fd'.storageClass
      let identMap' ← declareFun identMap fd'.name fd'.params.length false true
      return (identMap', .FunDecl fd')
  | .FunDef fd => do
      liftM (checkUniqueParams fd.params)
      -- Resolve struct tags in parameter and return types (validates they're declared).
      -- Note: resolveFunctionDef also calls resolveTyp on params/retTyp (for the body),
      -- but we need the resolved types here for processFileScopeFun's type conflict check.
      let resolvedParams ← fd.params.mapM fun (t, n) => do return (← resolveTyp t, n)
      let resolvedRetTyp ← resolveTyp fd.retTyp
      let paramTypes := resolvedParams.map (·.1)
      let fd' := { fd with params := resolvedParams, retTyp := resolvedRetTyp }
      let _ ← processFileScopeFun fd'.name fd'.params.length paramTypes resolvedRetTyp true fd'.storageClass
      let identMap' ← declareFun identMap fd'.name fd'.params.length true true
      let fd'' ← resolveFunctionDef identMap' fd'
      return (identMap', .FunDef fd'')
  | .StructDecl tag membersOpt => do
      -- Chapter 18: file-scope struct/union type declaration.
      -- If `membersOpt = some members`, compute the layout and insert into TypeTable.
      -- If `membersOpt = none`, this is a forward declaration (forward reference only).
      --
      -- C §6.2.3: struct and union tags share the same tag namespace.
      -- Having both 'struct X' and 'union X' at file scope is illegal.
      -- Use inCurrentScopeOnly=false because all file-scope tags have fromCurrent=false.
      checkTagKindConflict tag (inCurrentScopeOnly := false)
      -- Add this tag to the tagMap FIRST so:
      --   (a) member types can reference the same tag (self-referential via pointer)
      --   (b) subsequent file-scope declarations can find it via resolveTyp
      -- File-scope tags use their original name (no renaming); fromCurrent=false so
      -- inner block-scope structs can shadow without hitting "defined more than once".
      let existingInMap := (← get).tagMap.any (fun p => p.1 == tag)
      if !existingInMap then
        modify fun s =>
          { s with tagMap := (tag, { uniqueName := tag, fromCurrent := false }) :: s.tagMap }
      match membersOpt with
      | some members =>
          let isUnion := tag.startsWith "union."
          -- Resolve any struct tags referenced in member types.
          -- Since we added the tag above, self-references like `struct s *next` will resolve.
          let resolvedMembers ← members.mapM fun (t, n) => do
            let t' ← resolveTyp t; return (t', n)
          processStructDef tag resolvedMembers isUnion
      | none => pure ()  -- forward declaration only
      return (identMap, .StructDecl tag membersOpt)

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

/-- Entry point for the identifier resolution pass.
    Returns the renamed program, the final counter value, the symbol table,
    and the type table (struct/union tag → layout).
    Chapter 18: TypeTable added to support struct/union type definitions. -/
def resolveProgram (p : AST.Program) : Except String (AST.Program × Nat × SymbolTable × TypeTable) := do
  let action : VarM2 AST.Program := do
    let (_, topLevels') ← p.topLevels.foldlM
      (fun (acc : IdentMap × List AST.TopLevel) item => do
        let (m, items) := acc
        let (m', item') ← resolveTopLevel m item
        return (m', items ++ [item']))
      ([], [])
    return { topLevels := topLevels' }
  let initState : VarState := { counter := 0, symTable := [], typeTable := [], tagMap := [] }
  match action.run initState with
  | .error msg                                          => .error msg
  | .ok (prog', { counter, symTable, typeTable, .. })  => .ok (prog', counter, symTable, typeTable)

end Semantics
