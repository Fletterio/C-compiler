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

    Three cases:
      1. **Tentative**: declared at file scope without an initializer.
      2. **Initial(n)**: concrete initializer value.
      3. **NoInitializer**: declared `extern`; no storage emitted here. -/
inductive InitialValue where
  | Tentative     : InitialValue
  | Initial       : Int → InitialValue
  | NoInitializer : InitialValue
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

end Semantics
