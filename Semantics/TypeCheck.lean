import AST.AST
import Semantics.SymbolTable

/-
  Type-checking pass for Chapter 11.

  This pass walks the AST (after VarResolution) and:
    1. Infers the type of every expression.
    2. Inserts explicit `Cast` nodes for all implicit widening and narrowing
       conversions that C mandates:
         - In a binary operation with mixed Int/Long operands, the narrower
           operand is widened to Long (usual arithmetic conversions).
         - In an assignment `x = expr`, the RHS is cast to the type of `x`.
         - In a function call, each argument is cast to the declared param type.
         - In a `return` statement, the expression is cast to the function's
           declared return type.
    3. Does NOT rename variables (VarResolution already did that).
    4. Does NOT validate linkage or scope (VarResolution already did that).

  After this pass every Binary node has operands of the same type, every
  Assignment has a correctly-typed RHS, and every Return has a correctly-typed
  expression.  The type of each AST expression can be computed deterministically
  from the AST structure and the symbol table.
-/

namespace Semantics

-- ---------------------------------------------------------------------------
-- Type helpers
-- ---------------------------------------------------------------------------

/-- True for the three char variants: Char, SChar, UChar. -/
private def isCharType : AST.Typ → Bool
  | .Char | .SChar | .UChar => true
  | _                       => false

/-- Integer promotion: char types (Char/SChar/UChar) promote to Int.
    Int can represent all values of signed char (-128..127) and unsigned char (0..255).
    C §6.3.1.1: "If an int can represent all values of the original type,
    the value is converted to an int; otherwise it is converted to unsigned int." -/
private def promoteChar : AST.Typ → AST.Typ
  | .Char | .SChar | .UChar => .Int
  | t                       => t

/-- Return the common type for a binary operation (C "usual arithmetic conversions").
    Chapter 16: char types (Char/SChar/UChar) promote to Int before comparison.
    Chapter 13: `Double` is a floating-point type and outranks all integer types.
    Chapter 12: extends to 4 types (Int, Long, UInt, ULong).
    Rules (C §6.3.1.8):
      0. Double beats all integer types.  (Ch13)
      1. Same type → that type.
      2. Both signed or both unsigned → wider type.
         Int  + Long  → Long;   UInt + ULong → ULong.
      3. Same rank, mixed sign → unsigned wins.
         Int  + UInt  → UInt;   Long + ULong → ULong.
      4. Unsigned rank > signed rank → unsigned wins.
         Int  + ULong → ULong;  UInt + Long  is handled by rule 5.
      5. Signed rank > unsigned rank AND signed can represent all unsigned values → signed.
         UInt + Long  → Long (Long can represent all UInt values [0, 2^32−1]).
      (Rule 6, converting both to unsigned of the signed type, is not reachable here.) -/
private def commonType (t1 t2 : AST.Typ) : AST.Typ :=
  -- Chapter 16: integer promotions — char types promote to Int first
  let t1 := promoteChar t1
  let t2 := promoteChar t2
  -- Chapter 13: Double outranks all integer types
  if t1 == .Double || t2 == .Double then .Double
  else if t1 == t2 then t1
  -- Same rank, mixed signedness: unsigned wins
  else if (t1 == .Int && t2 == .UInt) || (t1 == .UInt && t2 == .Int) then .UInt
  else if (t1 == .Long && t2 == .ULong) || (t1 == .ULong && t2 == .Long) then .ULong
  -- ULong is the widest integer type; wins over everything else
  else if t1 == .ULong || t2 == .ULong then .ULong
  -- Long beats Int and UInt (Long can represent all UInt values)
  else if t1 == .Long || t2 == .Long then .Long
  -- Remaining: Int + UInt handled above; shouldn't be reached
  else t1

/-- Wrap `e` in a `Cast` node only when the target type differs from `current`. -/
private def castTo (target : AST.Typ) (current : AST.Typ) (e : AST.Exp) : AST.Exp :=
  if target == current then e else .Cast target e

/-- Return true iff `e` is an integer null pointer constant (integer constant with value 0).
    In C, only integer constant expressions with value 0 are null pointer constants.
    Double 0.0 and integer variables (even if their runtime value is 0) are NOT.
    Chapter 16: ConstChar(0) and ConstUChar(0) are also null pointer constants. -/
private def isNullPtrConstant : AST.Exp → Bool
  | .Constant (.ConstInt n)   => n == 0
  | .Constant (.ConstLong n)  => n == 0
  | .Constant (.ConstUInt n)  => n == 0
  | .Constant (.ConstULong n) => n == 0
  | .Constant (.ConstChar n)  => n == 0   -- Chapter 16
  | .Constant (.ConstUChar n) => n == 0   -- Chapter 16
  | _                         => false

/-- True iff a type is a pointer type. -/
private def isPointerType : AST.Typ → Bool
  | .Pointer _ => true
  | _          => false

/-- True iff a type is an array type. -/
private def isArrayType : AST.Typ → Bool
  | .Array _ _ => true
  | _          => false

/-- True iff a type is an integer type (not pointer, array, or double).
    Chapter 16: char types (Char/SChar/UChar) are also integer types. -/
private def isIntegerType : AST.Typ → Bool
  | .Int | .Long | .UInt | .ULong => true
  | .Char | .SChar | .UChar       => true   -- Chapter 16
  | _                             => false

/-- True if the type contains an array with void element type (directly or nested).
    Chapter 17: arrays of incomplete type are illegal in C (C §6.2.5p22).
    Examples:
      `.Array .Void 3`                → true   (void[3])
      `.Pointer (.Array .Void 3)`     → true   (void(*)[3])
      `.Array (.Array .Void 4) 3`     → true   (void[3][4])
      `.Array .Int 3`                 → false  (int[3]) -/
private def containsVoidArray : AST.Typ → Bool
  | .Array .Void _  => true
  | .Array elem _   => containsVoidArray elem
  | .Pointer t      => containsVoidArray t
  | _               => false

/-- Array-to-pointer decay: if `e` has array type, wrap it in `AddrOf` to
    produce a pointer to the first element.  Other types pass through unchanged.
    This models C's implicit array→pointer conversion. -/
private def decayArray (e : AST.Exp) (t : AST.Typ) : AST.Exp × AST.Typ :=
  match t with
  | .Array elem _ => (.AddrOf e, .Pointer elem)
  | _             => (e, t)

/-- Truncate an integer value `n` to the signed 32-bit range [−2^31, 2^31−1].
    Used when a `case` constant appears in an `int`-controlled switch. -/
private def truncToInt32 (n : Int) : Int :=
  let modulus : Int := 4294967296  -- 2^32
  let r := n % modulus
  if r >= 2147483648 then r - modulus
  else if r < -2147483648 then r + modulus
  else r

/-- Truncate an integer value `n` to the unsigned 32-bit range [0, 2^32−1].
    Used when a `case` constant appears in an `unsigned int`-controlled switch. -/
private def truncToUInt32 (n : Int) : Int :=
  let modulus : Int := 4294967296  -- 2^32
  let r := n % modulus
  if r < 0 then r + modulus else r

-- truncateSwitchCases and truncateSwitchCasesItem are mutually recursive:
-- truncateSwitchCases calls truncateSwitchCasesItem for Compound items,
-- and truncateSwitchCasesItem calls truncateSwitchCases for Statement items.
mutual

/-- Walk a statement and apply `truncFn` to every `Case` value within this switch level.
    Stops recursing into nested `Switch` statements (their cases belong to them). -/
private partial def truncateSwitchCases (truncFn : Int → Int) : AST.Statement → AST.Statement
  | .Case n body lbl    => .Case (truncFn n) body lbl
  | .Default body lbl   => .Default body lbl
  | .Compound items     => .Compound (items.map (truncateSwitchCasesItem truncFn))
  | .If cond t eOpt     => .If cond (truncateSwitchCases truncFn t) (eOpt.map (truncateSwitchCases truncFn))
  | .While cond b lbl   => .While cond (truncateSwitchCases truncFn b) lbl
  | .DoWhile b cond lbl => .DoWhile (truncateSwitchCases truncFn b) cond lbl
  | .For init c p b lbl => .For init c p (truncateSwitchCases truncFn b) lbl
  | .Labeled lbl s      => .Labeled lbl (truncateSwitchCases truncFn s)
  -- Nested switch: stop — its cases belong to that inner switch
  | s@(.Switch ..)      => s
  | s                   => s

private partial def truncateSwitchCasesItem (truncFn : Int → Int) : AST.BlockItem → AST.BlockItem
  | .S s => .S (truncateSwitchCases truncFn s)
  | item => item

end

-- ---------------------------------------------------------------------------
-- Type-checking monad
-- ---------------------------------------------------------------------------

/-- The symbol table is read-only in this pass; use a plain `Except` for errors
    and thread the symbol table as a parameter rather than through state. -/
private abbrev TcM := Except String

-- ---------------------------------------------------------------------------
-- Expression type inference and cast insertion
-- ---------------------------------------------------------------------------

/-- The return type of `typeCheckExp`: the rewritten expression plus its type. -/
private abbrev TcResult := TcM (AST.Exp × AST.Typ)

/-- Implicit cast: like `castTo` but validates that the conversion is legal.
    Illegal implicit conversions (which require an explicit cast in C):
      - Double  → Pointer  (always illegal, even with explicit cast)
      - Pointer → Double   (always illegal, even with explicit cast)
      - Pointer A → Pointer B  (different pointee types, unless one side is void*)
      - Integer (non-null) → Pointer  (only integer constant 0 is a null pointer constant)
      - Pointer → Integer  (requires explicit cast)
    Chapter 17: `void *` is compatible with any data pointer type (C §6.3.2.3p1). -/
private def implicitCastTo (target : AST.Typ) (current : AST.Typ) (e : AST.Exp) : TcM AST.Exp := do
  if target == current then return e
  else match target, current with
  | .Pointer _, .Double =>
      throw "TypeCheck: cannot convert double to pointer (even with implicit cast)"
  | .Double, .Pointer _ =>
      throw "TypeCheck: cannot convert pointer to double (even with implicit cast)"
  -- Chapter 15: array-to-pointer decay (implicit).
  -- `int arr[N]` used where `int *` expected decays to `&arr[0]`.
  -- The `AddrOf(Var ...)` wrapper emits a `GetAddress` / leaq in TackyGen.
  | .Pointer elem, .Array arrElem _ =>
      if elem == arrElem then return (.AddrOf e)
      -- Chapter 17: array of T decays to T*, which is implicitly convertible to void*.
      else if elem == .Void then return (.AddrOf e)
      else throw s!"TypeCheck: array element type {repr arrElem} does not match pointer target {repr elem}"
  | _, .Array _ _ =>
      throw "TypeCheck: cannot implicitly convert an array to a non-pointer type"
  -- Chapter 17: void* ↔ any pointer type conversions are allowed implicitly (C §6.3.2.3p1).
  -- Any data pointer → void*: implicit conversion (the void* "forgets" the pointee type).
  | .Pointer .Void, .Pointer _ =>
      -- Non-void pointer → void*: always allowed (even if pointee types differ)
      return (.Cast target e)
  -- void* → any data pointer: allowed (C §6.3.2.3p1; the caller knows the real type)
  | .Pointer _, .Pointer .Void =>
      return (.Cast target e)
  | .Pointer _, .Pointer _ =>
      -- Both are non-void pointers but different pointee types: illegal implicit conversion
      throw "TypeCheck: cannot implicitly convert between different pointer types"
  | .Pointer _, _ =>
      -- Integer → pointer: only integer constant 0 (null pointer constant) is allowed
      if isNullPtrConstant e then return (.Cast target e)
      else throw "TypeCheck: cannot implicitly convert a non-null-pointer-constant to a pointer type (only integer constant 0 is a null pointer constant)"
  | _, .Pointer _ =>
      -- Pointer → integer: requires an explicit cast
      throw "TypeCheck: cannot implicitly convert a pointer to a non-pointer type"
  | _, .Void =>
      -- Chapter 17: void value cannot be used in assignment, argument, or return context.
      -- void is an incomplete type with no value representation.
      throw "TypeCheck: void value cannot be used in expression context (void is not a scalar type)"
  | _, _ =>
      -- Ordinary numeric conversions: delegate to castTo
      return (castTo target current e)

/-- Look up the declared type of a variable or function from the symbol table.
    Variables → `Obj(typ)` → return typ.
    Functions → use retTyp for calls. -/
private def lookupVarTyp (st : SymbolTable) (name : String) : TcM AST.Typ :=
  match lookupSym st name with
  | some { type := .Obj t, .. } => return t
  | some { type := .Fun _ _ _, .. } => throw s!"'{name}' is a function, not a variable"
  | none => throw s!"Undeclared identifier '{name}' in TypeCheck"

/-- Infer the type of an expression and insert implicit casts where needed.
    Returns the (possibly rewritten) expression and its type. -/
private def typeCheckExp (st : SymbolTable) : AST.Exp → TcResult
  -- Typed constants: preserve the constant's declared type
  | .Constant (.ConstInt n)    => return (.Constant (.ConstInt n),    .Int)
  | .Constant (.ConstLong n)   => return (.Constant (.ConstLong n),   .Long)
  | .Constant (.ConstUInt n)   => return (.Constant (.ConstUInt n),   .UInt)    -- Chapter 12
  | .Constant (.ConstULong n)  => return (.Constant (.ConstULong n),  .ULong)   -- Chapter 12
  | .Constant (.ConstDouble f) => return (.Constant (.ConstDouble f), .Double)  -- Chapter 13
  -- Chapter 16: char constants — type is Char (not promoted here; promotion happens at use site)
  | .Constant (.ConstChar n)   => return (.Constant (.ConstChar n),   .Char)
  | .Constant (.ConstUChar n)  => return (.Constant (.ConstUChar n),  .UChar)
  -- Chapter 16: string literal — type is Array(Char, n+1) (decays to Pointer(Char) in expression contexts)
  | .StringLiteral s => return (.StringLiteral s, .Array .Char (s.length + 1))
  -- Chapter 17: sizeof operator — evaluated at compile time to ConstULong(size in bytes).
  -- C §6.5.3.4: sizeof's result has type size_t which we treat as ULong (unsigned long).
  -- The operand expression is NOT evaluated (only its type matters), so we type-check
  -- to get the type, then replace the entire node with a constant.
  | .SizeOf inner => do
      -- Type-check the inner expression just to get its type (side effects not evaluated).
      let (_, innerTyp) ← typeCheckExp st inner
      -- C §6.5.3.4p1: sizeof cannot be applied to void type or function types.
      if innerTyp == .Void then
        throw "TypeCheck: sizeof cannot be applied to void type"
      -- C §6.4.4.4p10: character CONSTANT LITERALS (like `'a'`) have type `int`, not `char`.
      -- So `sizeof 'a' == sizeof(int) == 4`.
      -- By contrast, `sizeof c` where c is a `char` variable returns 1 (sizeof char).
      -- We detect character constant literals by inspecting the original AST node `inner`
      -- (not the typeChecked `inner'`, which is the same node with the same structure).
      let sizeTyp : AST.Typ := match inner with
        | .Constant (.ConstChar _) | .Constant (.ConstUChar _) => .Int   -- char constant → int
        | _ => innerTyp                                                    -- everything else: use actual type
      return (.Constant (.ConstULong (sizeTyp.sizeOf : Int)), .ULong)
  | .SizeOfT t => do
      -- C §6.5.3.4p1: sizeof cannot be applied to void type or function types.
      if t == .Void then
        throw "TypeCheck: sizeof cannot be applied to void type"
      -- Chapter 17: arrays of incomplete element type (e.g. void[3]) are also illegal.
      if containsVoidArray t then
        throw "TypeCheck: sizeof cannot be applied to an array of incomplete element type (void[N])"
      return (.Constant (.ConstULong (t.sizeOf : Int)), .ULong)
  -- Variable reference: look up type.
  -- Arrays remain as Array type here; decay to pointer happens via
  -- implicitCastTo when used in a rvalue/pointer context (e.g. assignment, function arg).
  | .Var v => do
      let t ← lookupVarTyp st v
      return (.Var v, t)
  -- Explicit cast: type-check inner, wrap in Cast.
  -- Chapter 14: casting between pointer and double is never allowed, even explicitly.
  | .Cast targetTyp inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- Chapter 17: target type cannot contain an array of void (e.g. `(void(*)[3])expr`).
      if containsVoidArray targetTyp then
        throw "TypeCheck: cast target type contains an array of incomplete element type (void[N])"
      match targetTyp, innerTyp with
      | .Pointer _, .Double =>
          throw "TypeCheck: cannot cast double to pointer"
      | .Double, .Pointer _ =>
          throw "TypeCheck: cannot cast pointer to double"
      -- Chapter 17: casting TO void is always allowed (discards the value).
      -- Casting FROM void to any non-void type is illegal (void has no scalar value).
      | .Void, _ =>
          -- Any expression → void: valid (suppress the value)
          return (.Cast .Void inner', .Void)
      | _, .Void =>
          throw "TypeCheck: cannot cast a void expression to a non-void type (void is not a scalar type)"
      | _, _ => return (.Cast targetTyp inner', targetTyp)
  -- Unary operators: the result type matches the operand type.
  -- Exception: logical NOT (!) always produces Int regardless of operand type.
  -- Chapter 13: bitwise complement (~) is not valid on Double.
  | .Unary .Not inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- Chapter 17: void is non-scalar; cannot be used with logical NOT
      if innerTyp == .Void then
        throw "TypeCheck: void type cannot be used with logical NOT (!)"
      -- C §6.3.2.1p3: array operand decays to pointer before applying !.
      -- This handles `!"string literal"` where the string has array type.
      let (inner', _) := decayArray inner' innerTyp
      -- Logical NOT always produces int (0 or 1)
      return (.Unary .Not inner', .Int)
  | .Unary .Complement inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- C §6.5.3.3: ~ requires integer operand; void, doubles, and pointers are not allowed
      if innerTyp == .Void then
        throw s!"TypeCheck: bitwise complement (~) is not valid on void"
      if innerTyp == .Double then
        throw s!"TypeCheck: bitwise complement (~) is not valid on a double"
      if isPointerType innerTyp then
        throw s!"TypeCheck: bitwise complement (~) is not valid on a pointer"
      -- Chapter 16: integer promotion — char types promote to Int before ~
      let (inner', innerTyp) :=
        if isCharType innerTyp then (.Cast .Int inner', .Int) else (inner', innerTyp)
      return (.Unary .Complement inner', innerTyp)
  -- Chapter 14: unary negation is not valid on a pointer or void
  | .Unary .Negate inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- Chapter 17: void is non-scalar; cannot negate void
      if innerTyp == .Void then
        throw s!"TypeCheck: unary negation (-) is not valid on void"
      if isPointerType innerTyp then
        throw s!"TypeCheck: unary negation (-) is not valid on a pointer"
      -- Chapter 16: integer promotion — char types promote to Int before unary -
      let (inner', innerTyp) :=
        if isCharType innerTyp then (.Cast .Int inner', .Int) else (inner', innerTyp)
      return (.Unary .Negate inner', innerTyp)
  -- (All UnaryOp constructors are handled above: Not, Complement, Negate)
  -- Binary operators: apply usual arithmetic conversions
  -- Exception: shift operators (<<, >>) use only the left operand's type.
  -- C §6.5.7: "The type of the result is that of the promoted left operand."
  -- The right operand is NOT subject to usual arithmetic conversions; the
  -- shift amount can have any integer type without affecting the result type.
  -- Chapter 13: shifts and bitwise ops (& | ^ %) are not valid on Double.
  | .Binary .ShiftLeft left right => do
      let (left',  leftTyp)  ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      -- Chapter 17: void is non-scalar; cannot be used as shift operand
      if leftTyp == .Void || rightTyp == .Void then
        throw s!"TypeCheck: void type cannot be used as operand of shift operator (<<)"
      if leftTyp == .Double then
        throw s!"TypeCheck: left operand of shift (<<) cannot be double"
      if rightTyp == .Double then
        throw s!"TypeCheck: right operand of shift (<<) cannot be double"
      -- Chapter 14: pointers are not valid shift operands
      if isPointerType leftTyp then
        throw s!"TypeCheck: left operand of shift (<<) cannot be a pointer"
      if isPointerType rightTyp then
        throw s!"TypeCheck: right operand of shift (<<) cannot be a pointer"
      -- Chapter 16: integer promotion — char types promote to Int (C §6.3.1.1)
      let (left', leftTyp) :=
        if isCharType leftTyp then (.Cast .Int left', .Int) else (left', leftTyp)
      return (.Binary .ShiftLeft left' right', leftTyp)
  | .Binary .ShiftRight left right => do
      let (left',  leftTyp)  ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      -- Chapter 17: void is non-scalar; cannot be used as shift operand
      if leftTyp == .Void || rightTyp == .Void then
        throw s!"TypeCheck: void type cannot be used as operand of shift operator (>>)"
      if leftTyp == .Double then
        throw s!"TypeCheck: left operand of shift (>>) cannot be double"
      if rightTyp == .Double then
        throw s!"TypeCheck: right operand of shift (>>) cannot be double"
      -- Chapter 14: pointers are not valid shift operands
      if isPointerType leftTyp then
        throw s!"TypeCheck: left operand of shift (>>) cannot be a pointer"
      if isPointerType rightTyp then
        throw s!"TypeCheck: right operand of shift (>>) cannot be a pointer"
      -- Chapter 16: integer promotion — char types promote to Int (C §6.3.1.1)
      let (left', leftTyp) :=
        if isCharType leftTyp then (.Cast .Int left', .Int) else (left', leftTyp)
      return (.Binary .ShiftRight left' right', leftTyp)
  -- Chapter 13: logical AND/OR — each operand is tested for truthiness
  -- independently; do NOT apply usual arithmetic conversions between them.
  -- The result is always Int (0 or 1).
  | .Binary .And left right => do
      let (left', leftTyp)   ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      -- Chapter 17: void is non-scalar and cannot be used with logical AND (&&)
      if leftTyp == .Void || rightTyp == .Void then
        throw "TypeCheck: void type cannot be used with logical AND (&&)"
      return (.Binary .And left' right', .Int)
  | .Binary .Or left right => do
      let (left', leftTyp)   ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      -- Chapter 17: void is non-scalar and cannot be used with logical OR (||)
      if leftTyp == .Void || rightTyp == .Void then
        throw "TypeCheck: void type cannot be used with logical OR (||)"
      return (.Binary .Or left' right', .Int)
  | .Binary op left right => do
      let (left', leftTyp)   ← typeCheckExp st left
      let (right', rightTyp) ← typeCheckExp st right
      -- Chapter 17: void is non-scalar and cannot be used as a binary operand.
      -- This check comes BEFORE array decay so that void[N] decaying to void* is
      -- not a surprise; void operands are always rejected here.
      if leftTyp == .Void then
        throw "TypeCheck: void type cannot be used as operand of binary expression"
      if rightTyp == .Void then
        throw "TypeCheck: void type cannot be used as operand of binary expression"
      -- Chapter 15: array-to-pointer decay in binary expression context.
      -- In C, an array used in an expression decays to a pointer to its first element.
      -- e.g. `arr + 2` where arr : int[3]  →  (&arr[0]) + 2 : int*
      -- This happens implicitly for all binary operators (most are illegal for pointers,
      -- but Add/Subtract allow pointer+int and ptr-ptr).
      let (left', leftTyp)   := decayArray left' leftTyp
      let (right', rightTyp) := decayArray right' rightTyp
      let isLeftPtr  := isPointerType leftTyp
      let isRightPtr := isPointerType rightTyp
      -- Chapter 14: equality/inequality with a pointer operand.
      -- Rules:
      --   Both pointers → must be same pointer type (otherwise error).
      --   Chapter 17: exception — void* can be compared to any data pointer (C §6.5.9p2).
      --   One pointer, one integer → integer must be a null pointer constant (value 0).
      --   One pointer, one double → always illegal.
      if (op == .Equal || op == .NotEqual) && (isLeftPtr || isRightPtr) then do
        if isLeftPtr && isRightPtr then do
          -- Both are pointers. Chapter 17: void* is comparable to any pointer type.
          -- C §6.5.9p2: "one operand is a pointer to void and the other is a pointer to
          -- an object type" is allowed.
          if leftTyp == rightTyp then
            return (.Binary op left' right', .Int)
          else if leftTyp == .Pointer .Void then
            -- left is void*, right is any pointer → cast right to void* for codegen
            return (.Binary op left' (.Cast leftTyp right'), .Int)
          else if rightTyp == .Pointer .Void then
            -- right is void*, left is any pointer → cast left to void* for codegen
            return (.Binary op (.Cast rightTyp left') right', .Int)
          else
            throw "TypeCheck: cannot compare pointers to different types"
        else if isLeftPtr then do
          -- LHS is pointer, RHS must be null pointer constant
          if rightTyp == .Double then
            throw "TypeCheck: cannot compare a pointer to a double"
          if !isNullPtrConstant right' then
            throw "TypeCheck: cannot compare a pointer to a non-null-pointer-constant integer (only integer constant 0 is allowed)"
          return (.Binary op left' (.Cast leftTyp right'), .Int)
        else do
          -- RHS is pointer, LHS must be null pointer constant
          if leftTyp == .Double then
            throw "TypeCheck: cannot compare a pointer to a double"
          if !isNullPtrConstant left' then
            throw "TypeCheck: cannot compare a non-null-pointer-constant integer to a pointer (only integer constant 0 is allowed)"
          return (.Binary op (.Cast rightTyp left') right', .Int)
      -- Chapter 14/15: arithmetic and bitwise operations on pointers.
      -- Chapter 15: pointer arithmetic (+/-) is now legal for pointer+int combinations.
      --   ptr + int → Pointer(elem)   (AddPtr in TackyGen)
      --   int + ptr → Pointer(elem)
      --   ptr - int → Pointer(elem)
      --   ptr - ptr → Long (ptrdiff_t, divided by element size in TackyGen)
      -- All other operations on pointers remain illegal.
      -- Chapter 17: void* pointer arithmetic is not allowed (void is an incomplete type).
      match op with
      | .Add =>
          if isLeftPtr && isRightPtr then
            throw s!"TypeCheck: cannot add two pointers"
          if isLeftPtr && isRightPtr == false then
            -- ptr + int: the right operand must be an integer (not double)
            if rightTyp == .Double then
              throw s!"TypeCheck: cannot add a pointer and a double"
            -- Chapter 17: void * arithmetic is not allowed
            if leftTyp == .Pointer .Void then
              throw s!"TypeCheck: pointer arithmetic is not allowed on void * (void is an incomplete type)"
            -- Result is the pointer type
            return (.Binary .Add left' right', leftTyp)
          if isRightPtr && isLeftPtr == false then
            -- int + ptr: the left operand must be an integer (not double)
            if leftTyp == .Double then
              throw s!"TypeCheck: cannot add a double and a pointer"
            -- Chapter 17: void * arithmetic is not allowed
            if rightTyp == .Pointer .Void then
              throw s!"TypeCheck: pointer arithmetic is not allowed on void * (void is an incomplete type)"
            -- Result is the pointer type
            return (.Binary .Add left' right', rightTyp)
          -- Otherwise: neither is a pointer, fall through to normal arithmetic
      | .Subtract =>
          if isLeftPtr && isRightPtr then
            -- ptr - ptr: both must have the same pointer type; result is Long (ptrdiff_t)
            if leftTyp != rightTyp then
              throw s!"TypeCheck: cannot subtract pointers of different types"
            -- Chapter 17: void * arithmetic is not allowed
            if leftTyp == .Pointer .Void then
              throw s!"TypeCheck: pointer arithmetic is not allowed on void * (void is an incomplete type)"
            return (.Binary .Subtract left' right', .Long)
          if isLeftPtr && !isRightPtr then
            -- ptr - int: right operand must be integer
            if rightTyp == .Double then
              throw s!"TypeCheck: cannot subtract a double from a pointer"
            -- Chapter 17: void * arithmetic is not allowed
            if leftTyp == .Pointer .Void then
              throw s!"TypeCheck: pointer arithmetic is not allowed on void * (void is an incomplete type)"
            return (.Binary .Subtract left' right', leftTyp)
          if !isLeftPtr && isRightPtr then
            throw s!"TypeCheck: cannot subtract a pointer from a non-pointer"
          -- Otherwise: neither is a pointer, fall through to normal arithmetic
      | .Multiply | .Divide | .Remainder | .BitAnd | .BitOr | .BitXor =>
          if isLeftPtr then
            throw s!"TypeCheck: pointer type cannot be used as operand of this operator"
          if isRightPtr then
            throw s!"TypeCheck: pointer type cannot be used as operand of this operator"
      | _ =>
          -- Chapter 15: relational operators (<, <=, >, >=) and any other operator.
          -- Pointer-to-pointer comparison of the SAME type is valid (ordering within array).
          -- Pointer-to-integer (any integer, including 0) is ALWAYS illegal for relational ops
          -- (unlike == and !=, where integer 0 is a null pointer constant and thus allowed).
          if isLeftPtr && isRightPtr then do
            if leftTyp != rightTyp then
              throw s!"TypeCheck: cannot compare pointers of different types with relational operator"
            -- same-type pointer comparison: allowed — fall through to produce Int result
          else if isLeftPtr || isRightPtr then
            throw s!"TypeCheck: relational operator cannot mix pointer and non-pointer operands"
      -- Usual arithmetic conversions: widen the narrower operand
      let common := commonType leftTyp rightTyp
      -- Chapter 13: reject bitwise operations and modulo on Double operands.
      -- These operations require integer types (C §6.5.10, §6.5.11, §6.5.12, §6.5.5).
      match op with
      | .Remainder =>
          if common == .Double then
            throw s!"TypeCheck: modulo (%) is not valid on double operands"
      | .BitAnd =>
          if common == .Double then
            throw s!"TypeCheck: bitwise AND (&) is not valid on double operands"
      | .BitOr =>
          if common == .Double then
            throw s!"TypeCheck: bitwise OR (|) is not valid on double operands"
      | .BitXor =>
          if common == .Double then
            throw s!"TypeCheck: bitwise XOR (^) is not valid on double operands"
      | _ => pure ()
      let left''  := castTo common leftTyp  left'
      let right'' := castTo common rightTyp right'
      -- Relational and equality operators always produce Int
      let resultTyp := match op with
        | .Equal | .NotEqual | .LessThan | .LessOrEqual
        | .GreaterThan | .GreaterOrEqual => .Int
        | _ => common
      return (.Binary op left'' right'', resultTyp)
  -- Assignment: RHS is cast to the type of the LHS variable
  | .Assignment (.Var lhsName) rhs => do
      let lhsTyp ← lookupVarTyp st lhsName
      -- Chapter 17: void variables cannot be assigned to (void is an incomplete type)
      if lhsTyp == .Void then
        throw s!"TypeCheck: cannot assign to variable '{lhsName}' which has void type"
      -- Chapter 15: arrays are not assignable in C (C §6.3.2.1)
      if isArrayType lhsTyp then
        throw s!"TypeCheck: cannot assign to '{lhsName}' which has array type (arrays are not assignable in C)"
      let (rhs', rhsTyp) ← typeCheckExp st rhs
      -- Chapter 14: use implicitCastTo to catch illegal pointer assignments
      let rhs'' ← implicitCastTo lhsTyp rhsTyp rhs'
      return (.Assignment (.Var lhsName) rhs'', lhsTyp)
  -- Chapter 14: assignment through a pointer dereference: `*ptr = rhs`
  | .Assignment (.Dereference ptrExp) rhs => do
      let (ptr', ptrTyp) ← typeCheckExp st ptrExp
      let (rhs', rhsTyp) ← typeCheckExp st rhs
      -- Chapter 15: apply array-to-pointer decay to the pointer expression.
      -- e.g. `*arr = 3` where arr : int[N] — arr decays to int* before dereferencing.
      let (ptr', ptrTyp) := decayArray ptr' ptrTyp
      match ptrTyp with
      | .Pointer t =>
          -- Chapter 17: cannot assign to a void lvalue (void is an incomplete type).
          -- Dereferencing a void* gives a void lvalue, which cannot be assigned to.
          if t == .Void then
            throw "TypeCheck: cannot assign to a void lvalue (dereferencing void * gives incomplete type)"
          -- Chapter 15: cannot assign to an array type, even through a pointer.
          -- e.g. `*ptr_to_array = arr` is illegal — arrays are not assignable in C.
          if isArrayType t then
            throw s!"TypeCheck: cannot assign to an array type through a pointer dereference (arrays are not assignable in C)"
          -- Chapter 14: use implicitCastTo to catch illegal pointer assignments
          let rhs'' ← implicitCastTo t rhsTyp rhs'
          return (.Assignment (.Dereference ptr') rhs'', t)
      | _ => throw s!"TypeCheck: cannot assign through a non-pointer value"
  -- Chapter 15: assignment through subscript `a[i] = rhs`
  -- Desugar the LHS subscript to a dereference, then handle as *ptr = rhs.
  | .Assignment (.Subscript arrExp idxExp) rhs => do
      -- Rewrite a[i] = rhs as *(a + i) = rhs; typeCheckExp on Subscript gives Dereference(...)
      let (lhs', lhsTyp) ← typeCheckExp st (.Subscript arrExp idxExp)
      -- Chapter 15: cannot assign to an array-typed subscript (e.g., dim2[0] = dim
      -- where dim2 : int[1][2] — the subscript has type int[2], which is an array).
      if isArrayType lhsTyp then
        throw s!"TypeCheck: cannot assign to an array type (arrays are not assignable in C)"
      let (rhs', rhsTyp) ← typeCheckExp st rhs
      -- lhs' should be Dereference(Binary.Add ...) with type = element type
      let rhs'' ← implicitCastTo lhsTyp rhsTyp rhs'
      return (.Assignment lhs' rhs'', lhsTyp)
  | .Assignment lhs _ =>
      throw s!"TypeCheck: invalid lvalue in assignment (should have been caught by VarResolution)"
  -- Conditional: both branches are widened to the common type.
  -- Chapter 14: if either branch is a pointer, both must be the same pointer type
  -- (or one must be a null pointer constant that can be cast to the other's type).
  -- Chapter 17: void * branches are compatible with any pointer type (result is void *).
  --             The condition must be scalar (not void).
  --             Both-void branches are valid; one-void + one-non-void is not.
  | .Conditional cond e1 e2 => do
      let (cond', condTyp) ← typeCheckExp st cond
      -- Chapter 17: the ternary condition must have scalar type (not void).
      if condTyp == .Void then
        throw "TypeCheck: void type cannot be used as conditional expression condition"
      let (e1', t1)     ← typeCheckExp st e1
      let (e2', t2)     ← typeCheckExp st e2
      -- Chapter 15: apply array-to-pointer decay to both branches.
      -- e.g. `flag ? arr : ptr` where arr is int[N] — arr decays to int*.
      let (e1', t1) := decayArray e1' t1
      let (e2', t2) := decayArray e2' t2
      let ptr1 := isPointerType t1
      let ptr2 := isPointerType t2
      if ptr1 || ptr2 then do
        if ptr1 && ptr2 then do
          -- Both are pointers. Chapter 17: void * is compatible with any pointer type.
          -- C §6.5.15p6: if both are pointers to compatible types or one is void*, result is void*.
          if t1 == t2 then
            let r : AST.Exp := .Conditional cond' e1' e2'
            return (r, t1)
          else if t1 == .Pointer .Void then
            -- left branch is void*, right is any pointer → cast right to void*
            let r : AST.Exp := .Conditional cond' e1' (.Cast t1 e2')
            return (r, t1)
          else if t2 == .Pointer .Void then
            -- right branch is void*, left is any pointer → cast left to void*
            let r : AST.Exp := .Conditional cond' (.Cast t2 e1') e2'
            return (r, t2)
          else throw "TypeCheck: ternary branches have incompatible pointer types"
        else if ptr1 then do
          -- e1 is pointer, e2 must be null pointer constant
          if !isNullPtrConstant e2' then
            throw "TypeCheck: cannot mix pointer and non-pointer types in ternary expression"
          let r : AST.Exp := .Conditional cond' e1' (.Cast t1 e2')
          return (r, t1)
        else do
          -- e2 is pointer, e1 must be null pointer constant
          if !isNullPtrConstant e1' then
            throw "TypeCheck: cannot mix pointer and non-pointer types in ternary expression"
          let r : AST.Exp := .Conditional cond' (.Cast t2 e1') e2'
          return (r, t2)
      else
        -- Chapter 17: ternary branches that are both void is valid (expression has type void).
        -- One-void + one-non-void is invalid (cannot mix void and non-void types).
        if (t1 == .Void) != (t2 == .Void) then
          throw "TypeCheck: ternary branches have incompatible types (cannot mix void and non-void branches)"
        let common := commonType t1 t2
        let e1'' := castTo common t1 e1'
        let e2'' := castTo common t2 e2'
        let r : AST.Exp := .Conditional cond' e1'' e2''
        return (r, common)
  -- Postfix increment/decrement: type of the variable
  | .PostfixIncr (.Var v) => do
      let t ← lookupVarTyp st v
      -- Chapter 17: postfix ++ on a void * pointer is not allowed
      if t == .Pointer .Void then
        throw s!"TypeCheck: postfix ++ is not allowed on void * (void is an incomplete type)"
      return (.PostfixIncr (.Var v), t)
  | .PostfixDecr (.Var v) => do
      let t ← lookupVarTyp st v
      -- Chapter 17: postfix -- on a void * pointer is not allowed
      if t == .Pointer .Void then
        throw s!"TypeCheck: postfix -- is not allowed on void * (void is an incomplete type)"
      return (.PostfixDecr (.Var v), t)
  -- Chapter 14: postfix ++/-- through a pointer dereference: `(*p)++`
  | .PostfixIncr (.Dereference ptrExp) => do
      let (ptr', ptrTyp) ← typeCheckExp st ptrExp
      match ptrTyp with
      | .Pointer t =>
          -- Chapter 17: cannot apply ++ to a void lvalue (dereferencing void * is incomplete)
          if t == .Void then
            throw "TypeCheck: postfix ++ on a void lvalue is not allowed (void is an incomplete type)"
          return (.PostfixIncr (.Dereference ptr'), t)
      | _ => throw s!"TypeCheck: postfix ++ requires a pointer dereference"
  | .PostfixDecr (.Dereference ptrExp) => do
      let (ptr', ptrTyp) ← typeCheckExp st ptrExp
      match ptrTyp with
      | .Pointer t =>
          -- Chapter 17: cannot apply -- to a void lvalue (dereferencing void * is incomplete)
          if t == .Void then
            throw "TypeCheck: postfix -- on a void lvalue is not allowed (void is an incomplete type)"
          return (.PostfixDecr (.Dereference ptr'), t)
      | _ => throw s!"TypeCheck: postfix -- requires a pointer dereference"
  -- Chapter 15: postfix ++/-- on array subscript: a[i]++
  | .PostfixIncr (.Subscript arrExp idxExp) => do
      let (lhs', lhsTyp) ← typeCheckExp st (.Subscript arrExp idxExp)
      return (.PostfixIncr lhs', lhsTyp)
  | .PostfixDecr (.Subscript arrExp idxExp) => do
      let (lhs', lhsTyp) ← typeCheckExp st (.Subscript arrExp idxExp)
      return (.PostfixDecr lhs', lhsTyp)
  | .PostfixIncr e | .PostfixDecr e =>
      throw s!"TypeCheck: invalid lvalue in postfix operator"
  -- Chapter 14: address-of operator: `&e` has type `Pointer(typeOf e)`.
  -- The operand must be an lvalue (Var, Dereference, Subscript, or StringLiteral).
  -- Note: &*e is valid (cancels out), handled in TackyGen as an optimization.
  -- Chapter 15: &arr where arr is an Array type gives Pointer(Array elem n), not Pointer(elem).
  -- Chapter 16: &"hello" is valid — string literals are lvalues in read-only data.
  | .AddrOf inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- Only lvalues are valid operands of &
      match inner' with
      | .Var _           => return (.AddrOf inner', .Pointer innerTyp)
      | .Dereference _   => return (.AddrOf inner', .Pointer innerTyp)
      | .Subscript _ _   => return (.AddrOf inner', .Pointer innerTyp)
      | .StringLiteral _ => return (.AddrOf inner', .Pointer innerTyp)   -- Chapter 16
      | _ => throw "TypeCheck: operand of address-of (&) must be an lvalue (variable, *expr, a[i], or string literal)"
  -- Chapter 14: dereference operator: `*e` has type `t` when `typeOf e = Pointer(t)`
  -- Chapter 15: apply array-to-pointer decay before the pointer check.
  -- e.g. `*(arr + 1)` where `arr : int[N]` — `arr + 1` produces a Pointer(int), OK.
  -- But also `**row_ptr` where `*row_ptr : Array(int, N)` — the inner result has
  -- Array type, which decays to a Pointer before the outer * is applied.
  | .Dereference inner => do
      let (inner', innerTyp) ← typeCheckExp st inner
      -- Decay: if `inner'` has array type, treat it as a pointer to the first element
      let (inner', innerTyp) := decayArray inner' innerTyp
      match innerTyp with
      | .Pointer t => return (.Dereference inner', t)
      | _ => throw s!"TypeCheck: cannot dereference a non-pointer type"
  -- Chapter 15: array subscript `a[i]` ≡ `*(a + i)`.
  -- The array (or pointer) `a` is decayed to a pointer, then `i` indexes it.
  -- The result type is the pointee type (an lvalue of element type).
  | .Subscript arrExp idxExp => do
      let (arr', arrTyp) ← typeCheckExp st arrExp
      let (idx', idxTyp) ← typeCheckExp st idxExp
      -- C §6.5.2.1: E1[E2] == *(E1 + E2), and subscript is commutative: E1[E2] == E2[E1].
      -- The pointer/array operand can be on EITHER side (e.g. `3[arr]` is valid: arr + 3).
      -- We track (ptrExpr, intExpr, intTyp) separately so we can:
      --   1. Validate intTyp is actually an integer type.
      --   2. Build `ptrExpr + intExpr` in the correct order.
      let (ptrExpr, intExpr, intTyp, elemTyp) ← match arrTyp, idxTyp with
        | .Array elem _, _  =>
            -- Left side is array: decay to pointer to first element; right is index
            pure (.AddrOf arr', idx', idxTyp, elem)
        | .Pointer elem, _  =>
            -- Left side is already a pointer (e.g. `p[i]`); right is index
            pure (arr', idx', idxTyp, elem)
        | _, .Array elem _  =>
            -- Right side is array (e.g. `3[arr]`): decay array to pointer; left is index
            pure (.AddrOf idx', arr', arrTyp, elem)
        | _, .Pointer elem  =>
            -- Right side is pointer (e.g. `0[ptr]` or `3[ptr]`): swap; left is index
            pure (idx', arr', arrTyp, elem)
        | _, _ =>
            throw s!"TypeCheck: subscript base must have pointer or array type, not {repr arrTyp} or {repr idxTyp}"
      -- Index must have integer type (not double, not pointer)
      if !isIntegerType intTyp then
        throw s!"TypeCheck: array subscript index must have integer type, got {repr intTyp}"
      -- Chapter 17: cannot subscript a pointer to void (incomplete element type has no size)
      if elemTyp == .Void then
        throw "TypeCheck: cannot subscript a pointer to void (void is an incomplete type, element has no size)"
      -- Desugar to *(ptrExpr + intExpr); pointer arithmetic is now legal (Ch15)
      let addExp := AST.Exp.Binary .Add ptrExpr intExpr
      return (.Dereference addExp, elemTyp)
  -- Function call: cast each argument to the declared parameter type
  | .FunCall fname args => do
      match lookupSym st fname with
      | none => throw s!"Undeclared function '{fname}'"
      | some { type := .Obj _, .. } => throw s!"'{fname}' is a variable, not a function"
      | some { type := .Fun _ paramTypes retTyp, .. } => do
          -- Type-check each argument and implicitly cast to the corresponding param type
          let typedArgs ← args.mapM (typeCheckExp st)
          -- Chapter 14: use implicitCastTo to catch illegal pointer/int conversions
          let castedArgs ← (typedArgs.zip paramTypes).mapM fun ((arg, argTyp), paramTyp) =>
            implicitCastTo paramTyp argTyp arg
          -- For extra args beyond paramTypes (shouldn't occur), keep as-is
          let allArgs := castedArgs ++ (typedArgs.drop paramTypes.length).map (·.1)
          return (.FunCall fname allArgs, retTyp)

-- ---------------------------------------------------------------------------
-- Initializer type-checking (must come after typeCheckExp)
-- ---------------------------------------------------------------------------

/-- Build a zero-valued initializer for the given type.
    C §6.7.9p10: elements not explicitly initialized are zero-initialized,
    as if they had static storage duration.
    For scalar types, emits the typed zero constant directly so that
    TackyGen can use the correct AsmType without needing an implicit cast.
    For array types, recursively creates a CompoundInit of zeros.
    Chapter 16: char types use ConstChar(0) / ConstUChar(0). -/
private def makeZeroInit : AST.Typ → AST.Initializer
  | .Int       => .SingleInit (.Constant (.ConstInt 0))
  | .Long      => .SingleInit (.Constant (.ConstLong 0))
  | .UInt      => .SingleInit (.Constant (.ConstUInt 0))
  | .ULong     => .SingleInit (.Constant (.ConstULong 0))
  | .Double    => .SingleInit (.Constant (.ConstDouble 0.0))
  | .Pointer _ => .SingleInit (.Constant (.ConstInt 0))  -- null pointer constant
  | .Array e n => .CompoundInit (List.replicate n (makeZeroInit e))
  | .Char | .SChar => .SingleInit (.Constant (.ConstChar 0))   -- Chapter 16
  | .UChar         => .SingleInit (.Constant (.ConstUChar 0))  -- Chapter 16
  | .Void          => .SingleInit (.Constant (.ConstInt 0))    -- Chapter 17: void cannot be zero-initialized; fallback

/-- Type-check an initializer for a variable of the given type.
    Chapter 15: `CompoundInit` is legal only for array types; each element
    is type-checked against the element type.
    Zero-pads the initializer list to the full array size (C §6.7.9p10).
    Chapter 16: `SingleInit(StringLiteral s)` for a char array is converted to
    a `CompoundInit` of ConstChar elements (with null terminator, zero-padded).
    `SingleInit(StringLiteral s)` for a pointer type decays to Pointer(Char). -/
private partial def typeCheckInitializer (st : SymbolTable) (varTyp : AST.Typ)
    : AST.Initializer → TcM AST.Initializer
  | .SingleInit (.StringLiteral s) => do
      -- Chapter 16: string literal initializer — special handling.
      match varTyp with
      | .Array elemTyp size =>
          -- String literal initializing a char array.
          if !isCharType elemTyp then
            throw s!"TypeCheck: string literal can only initialize a char array, not {repr varTyp}"
          -- Build a CompoundInit from the string characters.
          -- C §6.7.9p14: the null terminator is included if there is room.
          let chars := s.toList
          -- `mkChar c` constructs the appropriate typed constant for element type.
          let mkChar : Char → AST.Const := fun c =>
            match elemTyp with
            | .UChar => .ConstUChar (c.toNat : Int)
            | _      => .ConstChar  (c.toNat : Int)   -- Char or SChar
          let mkCharInit : Char → AST.Initializer := fun c =>
            .SingleInit (.Constant (mkChar c))
          -- C §6.7.9p14: the string (including null terminator) may not exceed the array size.
          -- `chars.length` is the number of non-null characters in the literal; the null
          -- terminator would bring it to `chars.length + 1`, so we error when that exceeds `size`.
          if chars.length > size then
            throw s!"TypeCheck: string initializer (length {chars.length + 1} with null) is too long for array of size {size}"
          -- Determine how many chars to store (truncate if array is smaller than string + null)
          let hasNull := size > chars.length       -- room for '\0'
          let storedChars := chars.take size       -- only first `size` chars (handles truncation)
          let charInits := storedChars.map mkCharInit
          let nullInit : List AST.Initializer :=
            if hasNull then [mkCharInit '\x00'] else []
          -- Zero-pad remaining elements after the null terminator
          let filledCount := storedChars.length + nullInit.length
          let padCount    := if size > filledCount then size - filledCount else 0
          let padInits    := List.replicate padCount (mkCharInit '\x00')
          return .CompoundInit (charInits ++ nullInit ++ padInits)
      | _ => do
          -- Non-array context: type-check as a regular string literal expression.
          -- This handles `char *p = "hello"` — the string literal decays to Pointer(Char).
          let (e', eTyp) ← typeCheckExp st (.StringLiteral s)
          let e'' ← implicitCastTo varTyp eTyp e'
          return .SingleInit e''
  | .SingleInit e => do
      let (e', eTyp) ← typeCheckExp st e
      -- Array types cannot be initialized with a scalar expression
      if isArrayType varTyp then
        throw s!"TypeCheck: cannot initialize an array with a scalar expression"
      let e'' ← implicitCastTo varTyp eTyp e'
      return .SingleInit e''
  | .CompoundInit inits => do
      match varTyp with
      | .Array elemTyp size =>
          -- C §6.7.9: the number of initializers cannot exceed the array size
          if inits.length > size then
            throw s!"TypeCheck: compound initializer has {inits.length} elements but array only has {size}"
          -- Zero-pad to the full array size (C §6.7.9p10: unlisted elements
          -- are zero-initialized as if they had static storage duration).
          let padded := inits ++ List.replicate (size - inits.length) (makeZeroInit elemTyp)
          let inits' ← padded.mapM (typeCheckInitializer st elemTyp)
          return .CompoundInit inits'
      | _ => throw s!"TypeCheck: compound initializer used for non-array type {repr varTyp}"

-- ---------------------------------------------------------------------------
-- Statement type-checking
-- ---------------------------------------------------------------------------

/-
  `typeCheckStmt`, `typeCheckForInit`, and `typeCheckBlockItem` are mutually
  recursive: `Compound` statements contain block items (`typeCheckBlockItem`),
  which may themselves be statements (`typeCheckStmt`), and `For` statements
  contain a for-init (`typeCheckForInit`).  We put all three in a `mutual`
  block so Lean accepts the forward references.
-/
mutual

/-- Type-check a statement, threading the current function's return type for
    `return` statements. -/
private partial def typeCheckStmt (st : SymbolTable) (retTyp : AST.Typ) : AST.Statement → TcM AST.Statement
  -- Chapter 17: Return is now Option Exp — void functions use `Return none`.
  | .Return none => do
      -- `return;` is only valid in void functions.
      if retTyp != .Void then
        throw s!"TypeCheck: `return;` (with no expression) is not valid in a function returning {repr retTyp}"
      return .Return none
  | .Return (some e) => do
      -- `return expr;` with a value.
      if retTyp == .Void then
        throw "TypeCheck: cannot return a value from a void function"
      let (e', eTyp) ← typeCheckExp st e
      -- Chapter 14: use implicitCastTo to catch illegal pointer return type conversions
      let e'' ← implicitCastTo retTyp eTyp e'
      return .Return (some e'')
  | .Expression e => do
      let (e', _) ← typeCheckExp st e
      return .Expression e'
  | .If cond thenStmt elseOpt => do
      let (cond', condTyp) ← typeCheckExp st cond
      -- Chapter 17: void is non-scalar and cannot be used as an if condition
      if condTyp == .Void then
        throw "TypeCheck: void type cannot be used as if condition"
      let then' ← typeCheckStmt st retTyp thenStmt
      let else' ← elseOpt.mapM (typeCheckStmt st retTyp)
      return .If cond' then' else'
  | .Compound items => do
      let items' ← items.mapM (typeCheckBlockItem st retTyp)
      return .Compound items'
  | .While cond body lbl => do
      let (cond', condTyp) ← typeCheckExp st cond
      -- Chapter 17: void is non-scalar and cannot be used as a while condition
      if condTyp == .Void then
        throw "TypeCheck: void type cannot be used as while condition"
      let body' ← typeCheckStmt st retTyp body
      return .While cond' body' lbl
  | .DoWhile body cond lbl => do
      let body' ← typeCheckStmt st retTyp body
      let (cond', condTyp) ← typeCheckExp st cond
      -- Chapter 17: void is non-scalar and cannot be used as a do-while condition
      if condTyp == .Void then
        throw "TypeCheck: void type cannot be used as do-while condition"
      return .DoWhile body' cond' lbl
  | .For init cond post body lbl => do
      let init' ← typeCheckForInit st init
      let cond' ← cond.mapM (fun e => do
        let (e', eTyp) ← typeCheckExp st e
        -- Chapter 17: void is non-scalar and cannot be used as a for loop condition
        if eTyp == .Void then throw "TypeCheck: void type cannot be used as for loop condition"
        return e')
      let post' ← post.mapM (fun e => do let (e', _) ← typeCheckExp st e; return e')
      let body' ← typeCheckStmt st retTyp body
      return .For init' cond' post' body' lbl
  | .Break lbl    => return .Break lbl
  | .Continue lbl => return .Continue lbl
  | .Switch exp body lbl cases => do
      let (exp', expTyp) ← typeCheckExp st exp
      -- C §6.8.4.2: the controlling expression must have integer type.
      -- Void, double, pointer, and array are not valid switch controlling expression types.
      if expTyp == .Void then
        throw s!"TypeCheck: switch controlling expression must have integer type, not void"
      if expTyp == .Double then
        throw s!"TypeCheck: switch controlling expression must have integer type, not double"
      if isPointerType expTyp then
        throw s!"TypeCheck: switch controlling expression must have integer type, not pointer"
      -- Chapter 15: arrays also cannot be used as switch controlling expression
      if isArrayType expTyp then
        throw s!"TypeCheck: switch controlling expression must have integer type, not array"
      let body' ← typeCheckStmt st retTyp body
      -- C §6.8.4.2p2: integer promotions are performed on the controlling expression.
      -- Char/SChar/UChar all promote to Int (C §6.3.1.1p2).
      -- We model this by inserting an explicit Cast to Int and treating the switch as Int-typed.
      let (exp'', expTyp') : AST.Exp × AST.Typ :=
        match expTyp with
        | .Char | .SChar | .UChar => (.Cast .Int exp', .Int)
        | _                       => (exp', expTyp)
      -- C §6.8.4.2: if the switch controlling expression has 32-bit type,
      -- truncate each case constant to that type's range.
      --   Int  switch → truncate to signed   int32 range.
      --   UInt switch → truncate to unsigned uint32 range.
      -- This must run BEFORE SwitchCollection validates for duplicates.
      let body'' := match expTyp' with
        | .Int  => truncateSwitchCases truncToInt32  body'
        | .UInt => truncateSwitchCases truncToUInt32 body'
        | _     => body'   -- Long/ULong: no truncation needed
      return .Switch exp'' body'' lbl cases
  | .Case n body lbl => do
      let body' ← typeCheckStmt st retTyp body
      return .Case n body' lbl
  | .Default body lbl => do
      let body' ← typeCheckStmt st retTyp body
      return .Default body' lbl
  | .Labeled lbl stmt => do
      let stmt' ← typeCheckStmt st retTyp stmt
      return .Labeled lbl stmt'
  | .Goto lbl => return .Goto lbl
  | .Null     => return .Null

/-- Type-check a `for` initializer: cast the initializer expression (if any)
    to match the declared variable type. -/
private partial def typeCheckForInit (st : SymbolTable) : AST.ForInit → TcM AST.ForInit
  | .InitExp eOpt => do
      let eOpt' ← eOpt.mapM (fun e => do let (e', _) ← typeCheckExp st e; return e')
      return .InitExp eOpt'
  | .InitDecl decl => do
      -- Chapter 15: use typeCheckInitializer (handles both scalar and compound inits)
      let init' ← decl.init.mapM (typeCheckInitializer st decl.typ)
      return .InitDecl { decl with init := init' }

/-- Type-check a block item: statements are recursed into; declaration
    initializers are cast to match the declared variable type; local function
    declarations are passed through unchanged. -/
private partial def typeCheckBlockItem (st : SymbolTable) (retTyp : AST.Typ) : AST.BlockItem → TcM AST.BlockItem
  | .S stmt => do
      let stmt' ← typeCheckStmt st retTyp stmt
      return .S stmt'
  | .D decl => do
      -- Chapter 17: reject void variable declarations and arrays of void element type.
      -- void is an incomplete type; local variables of void type are illegal in C.
      if decl.typ == .Void then
        throw s!"TypeCheck: cannot declare variable '{decl.name}' with void type (void is an incomplete type)"
      if containsVoidArray decl.typ then
        throw s!"TypeCheck: cannot declare variable '{decl.name}' with a type containing an array of void"
      -- Chapter 15: use typeCheckInitializer (handles scalar SingleInit and CompoundInit)
      let init' ← decl.init.mapM (typeCheckInitializer st decl.typ)
      return .D { decl with init := init' }
  | .FD fd => return .FD fd   -- local function declarations need no type-checking here

end

-- ---------------------------------------------------------------------------
-- Top-level type-checking
-- ---------------------------------------------------------------------------

/-- Type-check a function definition: type-check the body with the function's
    return type so that `return` statements are correctly cast. -/
private def typeCheckFunctionDef (st : SymbolTable) (f : AST.FunctionDef) : TcM AST.FunctionDef := do
  -- Chapter 17: reject void-typed named parameters.
  -- In C, `(void)` as the only parameter means "no parameters" (empty list after parsing);
  -- a named parameter `void x` is always illegal.
  for (paramTyp, paramName) in f.params do
    if paramTyp == .Void then
      throw s!"TypeCheck: parameter '{paramName}' cannot have void type (use (void) for empty parameter list)"
    if containsVoidArray paramTyp then
      throw s!"TypeCheck: parameter '{paramName}' type cannot contain an array of void"
  let body' ← f.body.mapM (typeCheckBlockItem st f.retTyp)
  return { f with body := body' }

/-- Entry point for the type-checking pass.
    Walks all top-level function definitions; variable declarations at file scope
    are checked (initializer cast) but otherwise unchanged. -/
def typeCheckProgram (p : AST.Program) (st : SymbolTable) : Except String AST.Program := do
  let topLevels' ← p.topLevels.mapM fun tl =>
    match tl with
    | .FunDef fd  => do
        let fd' ← typeCheckFunctionDef st fd
        return .FunDef fd'
    | .VarDecl decl => do
        -- Chapter 17: reject void variable declarations and arrays of void element type.
        -- extern/static void variables are also illegal (void is an incomplete type).
        if decl.typ == .Void then
          throw s!"TypeCheck: cannot declare variable '{decl.name}' with void type (void is an incomplete type)"
        if containsVoidArray decl.typ then
          throw s!"TypeCheck: cannot declare variable '{decl.name}' with a type containing an array of void"
        -- Chapter 15: use typeCheckInitializer (handles scalar and compound inits)
        let init' ← decl.init.mapM (typeCheckInitializer st decl.typ)
        return .VarDecl { decl with init := init' }
    | .FunDecl fd => do
        -- Chapter 17: reject void-typed named parameters in function declarations.
        -- Note: `(void)` as the sole parameter means "no parameters" and is parsed
        -- as an empty param list — those are not checked here.
        for (paramTyp, paramName) in fd.params do
          if paramTyp == .Void then
            throw s!"TypeCheck: parameter '{paramName}' cannot have void type (use (void) for empty parameter list)"
          if containsVoidArray paramTyp then
            throw s!"TypeCheck: parameter '{paramName}' type cannot contain an array of void"
        return .FunDecl fd
  return { p with topLevels := topLevels' }

end Semantics
