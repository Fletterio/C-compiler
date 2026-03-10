/-
  Symbol table for Chapter 10: file-scope variable declarations and
  storage-class specifiers.

  The symbol table maps each identifier (variable or function) to a
  `SymbolEntry` that records its type and attributes (linkage, initialization
  state, etc.).  It is built during variable resolution and threaded through
  the remainder of the compiler pipeline so that:

    - TackyGen can determine which file-scope variables to emit as
      `StaticVariable` top-level items (and which can be skipped because they
      are declared `extern` but not defined in this translation unit).
    - PseudoReplace can distinguish static variables (which should become
      RIP-relative `Data` operands) from automatic local variables (which
      become stack-frame `Stack` operands).
-/

namespace Semantics

/-- The declared type of an identifier: either a scalar integer variable or a
    function with a given number of parameters.  We only support `int` as the
    value type in this chapter, so the variable case carries no extra info. -/
inductive IdentType where
  /-- A scalar `int` variable. -/
  | Int : IdentType
  /-- A function with `n` parameters (each of type `int`). -/
  | Fun : Nat → IdentType
  deriving Repr, BEq

/-- Describes how a static-storage variable is initialised.

    Three cases arise:
      1. **Tentative**: declared at file scope without an initializer
         (`int x;`).  Multiple tentative definitions of the same name are
         permitted and collapse into a single zero-initialised variable.
      2. **Initial(n)**: declared (or defined) with a concrete initializer
         (`int x = 5;` or `static int x = 5;` inside a function).  Only one
         concrete definition per name is allowed.
      3. **NoInitializer**: declared `extern` without a definition in this
         translation unit (`extern int x;`).  The linker is expected to find
         a definition in another TU.  We emit no storage for this variable.
-/
inductive InitialValue where
  /-- No initializer given; zero-initialize (only one such variable is generated). -/
  | Tentative : InitialValue
  /-- Explicit integer initializer value. -/
  | Initial : Int → InitialValue
  /-- `extern` declaration; no storage emitted in this TU. -/
  | NoInitializer : InitialValue
  deriving Repr, BEq

/-- Attributes attached to a symbol table entry.

    Three categories:
      - **Local**: an automatic local variable (no linkage, allocated on the
        stack frame of its enclosing function).  We track these so that
        PseudoReplace can assign them stack slots rather than Data addresses.
      - **Static(init, global)**: a variable with static storage duration.
        `global = true` means external linkage (visible across TUs).
        `global = false` means internal linkage (visible only in this TU,
        i.e. declared `static`).
      - **FunAttr(defined, global)**: a function entry.
        `defined = true` means we have a definition (body) in this TU.
        `global` has the same meaning as for Static.
-/
inductive SymAttrs where
  /-- Automatic local variable (no linkage). -/
  | Local : SymAttrs
  /-- Static variable: `init` describes its initializer, `global` its linkage. -/
  | Static : InitialValue → Bool → SymAttrs
  /-- Function: `defined` is true when the body is present, `global` is linkage. -/
  | FunAttr : Bool → Bool → SymAttrs
  deriving Repr, BEq

/-- A single entry in the symbol table, pairing the identifier's declared type
    with its runtime/linkage attributes. -/
structure SymbolEntry where
  /-- The declared type (Int variable or Fun with param count). -/
  type  : IdentType
  /-- Storage class and linkage attributes. -/
  attrs : SymAttrs
  deriving Repr, BEq

/-- The symbol table itself: an association list from string identifiers to
    their `SymbolEntry`.  We use a list rather than a hash map because the
    number of top-level names is small and order-of-definition semantics are
    easy to implement correctly.

    Look-up is done with `List.find?` (returning the **first** matching pair),
    so prepending a new entry shadows an older one when both have the same key.
    However, for the global symbol table we always update in place (rather than
    shadowing) so that a single canonical entry exists per name.
-/
abbrev SymbolTable := List (String × SymbolEntry)

/-- Look up a name in the symbol table, returning `none` if absent. -/
def lookupSym (st : SymbolTable) (name : String) : Option SymbolEntry :=
  match st.find? (fun p => p.1 == name) with
  | some (_, e) => some e
  | none        => none

/-- Insert or update an entry in the symbol table.
    If `name` already appears, its entry is replaced in-place (preserving
    the position of the existing entry in the list so that the table order
    reflects the order in which names were first declared).
    If `name` is new, the entry is prepended. -/
def insertSym (st : SymbolTable) (name : String) (entry : SymbolEntry) : SymbolTable :=
  if st.any (fun p => p.1 == name) then
    st.map fun (n, e) => if n == name then (n, entry) else (n, e)
  else
    (name, entry) :: st

end Semantics
