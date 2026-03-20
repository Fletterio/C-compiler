import AST.AST

/-
  Symbol table for Chapter 11: extended to carry type information.

  Chapter 11 additions:
    - `IdentType.Obj(typ)` replaces the former `IdentType.Int`: records the
      scalar type (`Int` or `Long`) of a variable.
    - `IdentType.Fun` now carries the parameter types and return type in
      addition to the parameter count, so that the TypeCheck pass can insert
      implicit casts at call sites and around return expressions.

  The symbol table is built during variable resolution and threaded through:
    - TypeCheck: uses param/return types to insert implicit Cast nodes.
    - TackyGen: determines function linkage and emits StaticVariable items.
    - PseudoReplace: distinguishes static variables (→ Data) from locals (→ Stack),
      and consults the backend symbol table for allocation size.
-/

namespace Semantics

/-- The declared type of an identifier.
    Chapter 11: `Obj(typ)` generalises the former plain `Int` case to carry
    the actual scalar type.  `Fun` carries param types and return type. -/
inductive IdentType where
  /-- A scalar variable of the given type (Int or Long). -/
  | Obj : AST.Typ → IdentType
  /-- A function: param count, param types (in order), and return type. -/
  | Fun : Nat → List AST.Typ → AST.Typ → IdentType
  deriving Repr, BEq

/-- Describes how a static-storage variable is initialised.

    Six cases:
      1. **Tentative**: declared at file scope without an initializer.
      2. **Initial(n)**: concrete integer initializer value.
      3. **DoubleInitial(f)**: concrete double initializer value.  (Chapter 13)
      4. **NoInitializer**: declared `extern`; no storage emitted here.
      5. **ArrayInitial(ivs)**: list of element init values for static arrays. (Chapter 15)
         Each element is itself an `InitialValue` (Initial, DoubleInitial, or Tentative=0).
      6. **StringInitial(s)**: a char array initialised from a string literal.  (Chapter 16)
         The string `s` contains the raw (unescaped) characters without the null terminator;
         the null byte is always appended. Used for `static char arr[] = "hello"`. -/
inductive InitialValue where
  | Tentative       : InitialValue
  | Initial         : Int   → InitialValue
  | DoubleInitial   : Float → InitialValue   -- Chapter 13: static double initializer
  | NoInitializer   : InitialValue
  | ArrayInitial    : List InitialValue → InitialValue  -- Chapter 15: static array initializer
  | StringInitial   : String → InitialValue  -- Chapter 16: char array init from string literal
  /-- Chapter 18: static char-pointer member initialized with a string literal.
      The String is the raw string content (without null terminator); TackyGen will
      intern it as a StaticConstant and emit a `.quad label` pointer initializer. -/
  | PointerInitial  : String → InitialValue
  deriving Repr, BEq

/-- Attributes attached to a symbol table entry. -/
inductive SymAttrs where
  /-- Automatic local variable (no linkage). -/
  | Local : SymAttrs
  /-- Static variable: init describes its initializer, global its linkage. -/
  | Static : InitialValue → Bool → SymAttrs
  /-- Function: defined is true when the body is present, global is linkage. -/
  | FunAttr : Bool → Bool → SymAttrs
  deriving Repr, BEq

/-- A single entry in the symbol table. -/
structure SymbolEntry where
  /-- The declared type (scalar object or function signature). -/
  type  : IdentType
  /-- Storage class and linkage attributes. -/
  attrs : SymAttrs
  deriving Repr, BEq

/-- The symbol table: an association list from string identifiers to entries. -/
abbrev SymbolTable := List (String × SymbolEntry)

/-- Look up a name in the symbol table. -/
def lookupSym (st : SymbolTable) (name : String) : Option SymbolEntry :=
  match st.find? (fun p => p.1 == name) with
  | some (_, e) => some e
  | none        => none

/-- Insert or update an entry in the symbol table.
    Updates in-place if the name already exists; prepends otherwise. -/
def insertSym (st : SymbolTable) (name : String) (entry : SymbolEntry) : SymbolTable :=
  if st.any (fun p => p.1 == name) then
    st.map fun (n, e) => if n == name then (n, entry) else (n, e)
  else
    (name, entry) :: st

-- ---------------------------------------------------------------------------
-- Chapter 18: Type table for struct/union definitions
-- ---------------------------------------------------------------------------

/-- A single member of a struct or union, with its byte offset from the start. -/
structure MemberEntry where
  name   : String   -- member name
  typ    : AST.Typ  -- member type
  offset : Nat      -- byte offset from start of struct/union
  deriving Repr, BEq

/-- The layout of a struct or union type.
    For structs: members are placed at increasing offsets with alignment padding.
    For unions:  all members have offset 0; size = max member size padded to alignment.
    `size`      is the total byte size (including trailing padding).
    `alignment` is the alignment requirement (maximum of all member alignments). -/
structure StructDef where
  members   : List MemberEntry
  size      : Nat
  alignment : Nat
  deriving Repr, BEq

/-- The type table maps internal struct/union tag names (e.g. "struct.Point") to
    their layout definitions.  Built by VarResolution and threaded through the
    entire compiler pipeline. -/
abbrev TypeTable := List (String × StructDef)

/-- Look up a struct/union tag in the type table. -/
def lookupTypeTable (tt : TypeTable) (tag : String) : Option StructDef :=
  match tt.find? (fun p => p.1 == tag) with
  | some (_, sd) => some sd
  | none         => none

/-- Insert or update a struct/union entry in the type table. -/
def insertTypeTable (tt : TypeTable) (tag : String) (sd : StructDef) : TypeTable :=
  if tt.any (fun p => p.1 == tag) then
    tt.map fun (n, e) => if n == tag then (n, sd) else (n, e)
  else
    (tag, sd) :: tt

end Semantics
