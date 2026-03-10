import AST.AST
import Semantics.SymbolTable

/-
  Semantic analysis pass: identifier resolution and symbol-table construction.
  Chapter 10 rewrite.

  This pass performs:
    1. Validates that every variable and function is declared before use.
    2. Validates that function calls use function names (not variable names).
    3. Validates that variable references use variable names (not function names).
    4. Validates that assignment/increment/decrement lvalues are `Var` nodes.
    5. Validates parameter uniqueness (no duplicate param names).
    6. Validates that functions are not defined more than once.
    7. Validates argument counts at call sites.
    8. Renames local automatic variables to unique names (`<orig>.<n>`).
       File-scope variables and `extern` block-scope variables keep their
       original names (they must match across translation units).
       Local `static` variables are renamed (`<orig>.<n>`) to prevent clashes
       between two functions that each declare `static int x`.
    9. Builds a SymbolTable that records linkage and initialization info for
       every declared identifier.  This table is used by TackyGen (to emit
       StaticVariable entries) and by PseudoReplace (to map static variables to
       Data/RIP-relative operands rather than Stack slots).

  ## Identifier map

  The IdentMap maps source names to:
    - `Var(uniqueName)`: a local automatic or static variable (uniqueName is
      the renamed version used in TACKY/assembly).
    - `Fun(paramCount, defined)`: a function.

  The `fromCurrent` flag on each entry distinguishes declarations in the
  current scope (same-scope redeclaration is an error) from outer-scope entries
  (which may be shadowed).

  ## Linkage rules

  File-scope variable (no storage class or `extern`): external linkage.
  File-scope variable (`static`): internal linkage.
  File-scope variable (`extern`): takes on the linkage of any prior declaration
    of the same name; if none, external linkage but no storage emitted here.
  Block-scope variable (`static`): static storage, no linkage; renamed locally.
  Block-scope variable (`extern`): refers to the file-scope variable of the same
    name; not renamed; error if a non-linked local variable already exists in
    the same scope.
  Function (no SC or `extern`): external linkage.
  Function (`static`): internal linkage.
  Function (`static`) at block scope: error.

  ## Conflicts detected

  1.  Same name declared as both variable and function at file scope.
  2.  Two concrete definitions of the same file-scope variable.
  3.  Linkage conflict: `static int x` then `int x` (or vice versa).
  4.  `extern int x;` in a block when `x` was declared as a non-linked local
      variable in the same scope.
  5.  `static` storage class on a block-scope function declaration.
  6.  `extern` with an initializer.
  7.  Local `static` with a non-constant initializer.
  8.  Storage-class specifier in a `for`-loop initializer.
-/

namespace Semantics

/-- The monad used during identifier resolution: state (counter) + errors. -/
private abbrev VarM := StateT Nat (Except String)

-- ---------------------------------------------------------------------------
-- Identifier map types
-- ---------------------------------------------------------------------------

/-- Information stored for each identifier in the IdentMap.
    `Var`: a variable with its unique renamed name (as used in TACKY).
    `Fun`: a function with its parameter count and whether it has a body. -/
private inductive IdentInfo where
  | Var : String → IdentInfo              -- variable: unique name
  | Fun : Nat → Bool → IdentInfo          -- function: param count, has definition?
  deriving Repr

/-- Entry for an identifier in the identifier map.
    `info` is the identity information (variable or function).
    `fromCurrent` is `true` if the identifier was declared in the *current*
    scope (as opposed to an outer scope).  This flag lets us distinguish
    duplicate declarations (same scope, error) from shadowing (inner scope, allowed).
    `hasLinkage` is `true` if this is a variable declared with linkage
    (file-scope or `extern` block-scope).  Used to detect the error where
    `extern int x` follows a non-linked `int x` in the same scope. -/
private structure IdentEntry where
  info        : IdentInfo
  fromCurrent : Bool
  hasLinkage  : Bool := false   -- Chapter 10: true for extern/file-scope variables

/-- Association list mapping original identifier names to their `IdentEntry`.
    Updated as declarations are processed left to right. -/
private abbrev IdentMap := List (String × IdentEntry)

-- ---------------------------------------------------------------------------
-- State threaded through the pass
-- ---------------------------------------------------------------------------

/-- Full mutable state for the resolution pass.
    `counter`: source of unique names.
    `symTable`: growing symbol table, built as declarations are processed. -/
private structure VarState where
  counter  : Nat
  symTable : SymbolTable

private abbrev VarM2 := StateT VarState (Except String)

-- We work in VarM2 throughout.  Helper to allocate a unique name:

/-- Allocate a fresh unique name for `original`.
    Reads the current counter, increments it, and returns `"<original>.<n>"`. -/
private def makeUnique (original : String) : VarM2 String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  return s!"{original}.{s.counter}"

/-- Look up `name` in the identifier map, returning `none` if not found. -/
private def lookupIdent (identMap : IdentMap) (name : String) : Option IdentEntry :=
  match identMap.find? (fun p => p.1 == name) with
  | some (_, entry) => some entry
  | none            => none

/-- Produce a copy of `identMap` with all `fromCurrent` flags cleared.
    Used when entering an inner compound-statement scope: identifiers from
    outer scopes are still visible but may be shadowed by new declarations. -/
private def enterScope (identMap : IdentMap) : IdentMap :=
  identMap.map (fun (name, entry) => (name, { entry with fromCurrent := false }))

/-- Check that a list of parameter names contains no duplicates. -/
private def checkUniqueParams (params : List String) : Except String Unit := do
  let rec check : List String → Except String Unit
    | []     => .ok ()
    | p :: rest =>
        if rest.contains p then .error s!"Duplicate parameter name '{p}'"
        else check rest
  check params

-- ---------------------------------------------------------------------------
-- Symbol-table helpers
-- ---------------------------------------------------------------------------

/-- Add or update a symbol-table entry. -/
private def addSym (name : String) (entry : SymbolEntry) : VarM2 Unit :=
  modify fun s => { s with symTable := insertSym s.symTable name entry }

/-- Look up a name in the current symbol table. -/
private def getSym (name : String) : VarM2 (Option SymbolEntry) := do
  let s ← get
  return lookupSym s.symTable name

-- ---------------------------------------------------------------------------
-- File-scope variable declaration processing
-- ---------------------------------------------------------------------------

/-- Process a file-scope variable declaration, applying linkage rules and
    updating the symbol table.

    Rules (C11 §6.2.2):
    - No SC or `extern` → external linkage.
    - `static`          → internal linkage.
    - `extern`          → external linkage; no definition emitted if no initializer.

    Conflicts:
    - `static` then `extern` (or vice versa) in the same file → linkage conflict.
    - Two initializers for the same name → multiple definitions error.
    - `extern` with an initializer → error.
    Returns the (possibly renamed) name for use in the IdentMap (always the
    original name at file scope, since there is no renaming). -/
private def processFileScopeVar (decl : AST.Declaration) : VarM2 String := do
  let name := decl.name
  match decl.storageClass with
  | some .Extern => do
      -- `extern int x;` at file scope:
      -- Cannot have initializer
      if decl.init.isSome then
        throw s!"Variable '{name}' declared extern with an initializer at file scope"
      -- If already in symbol table, keep existing (extern never overwrites)
      let existing ← getSym name
      match existing with
      | none =>
          -- Not seen before: add as external, no initializer here
          addSym name { type := .Int, attrs := .Static .NoInitializer true }
      | some { type := .Fun _, .. } =>
          throw s!"'{name}' was previously declared as a function"
      | some _ =>
          -- Already declared: extern takes on existing linkage, no change
          pure ()
      return name
  | some .Static => do
      -- `static int x [= n];` at file scope → internal linkage
      let existing ← getSym name
      match existing with
      | some { type := .Fun _, .. } =>
          throw s!"'{name}' was previously declared as a function"
      | some { attrs := .Static _ true, .. } =>
          -- Previously declared with external linkage: conflict
          throw s!"Variable '{name}' declared with both internal and external linkage"
      | some { attrs := .Static init _, .. } =>
          -- Previously declared static (internal linkage): check for double definition
          match decl.init, init with
          | some e, .Initial _ =>
              match e with
              | .Constant n =>
                  throw s!"Variable '{name}' has conflicting definitions"
              | _ => throw s!"Variable '{name}' has conflicting definitions"
          | some e, _ =>
              match e with
              | .Constant n =>
                  addSym name { type := .Int, attrs := .Static (.Initial n) false }
              | _ => throw s!"Initializer for static variable '{name}' must be a constant"
          | none, .Initial _ =>
              -- Already has a concrete initializer: keep it (tentative ≤ concrete)
              pure ()
          | none, _ =>
              -- Both tentative: keep Tentative
              pure ()
      | _ =>
          -- Fresh declaration with internal linkage
          let initVal : InitialValue := match decl.init with
            | none   => .Tentative
            | some e => match e with
                        | .Constant n => .Initial n
                        | _           => -- non-constant init is an error
                            -- We'll produce a good error here:
                            .Tentative  -- placeholder; error thrown below
          match decl.init with
          | some (.Constant n) =>
              addSym name { type := .Int, attrs := .Static (.Initial n) false }
          | some _ =>
              throw s!"Initializer for file-scope static variable '{name}' must be a constant"
          | none =>
              addSym name { type := .Int, attrs := .Static .Tentative false }
      return name
  | none => do
      -- No storage class: external linkage
      let existing ← getSym name
      match existing with
      | some { type := .Fun _, .. } =>
          throw s!"'{name}' was previously declared as a function"
      | some { attrs := .Static _ false, .. } =>
          -- Previously declared static (internal linkage): conflict
          throw s!"Variable '{name}' declared with both internal and external linkage"
      | some { attrs := .Static init true, .. } =>
          -- Already external: check for double definition
          match decl.init, init with
          | some e, .Initial _ =>
              throw s!"Variable '{name}' has conflicting definitions"
          | some e, _ =>
              match e with
              | .Constant n =>
                  addSym name { type := .Int, attrs := .Static (.Initial n) true }
              | _ => throw s!"Initializer for file-scope variable '{name}' must be a constant"
          | none, .NoInitializer =>
              -- `extern int x;` was followed by a tentative definition: upgrade to Tentative.
              -- `NoInitializer` means only an extern reference was seen so far; a tentative
              -- definition (`int x;` with no initializer and no `extern`) provides storage.
              addSym name { type := .Int, attrs := .Static .Tentative true }
          | none, _ =>
              -- Concrete initializer already present or already Tentative: keep existing.
              pure ()
      | _ =>
          -- New external declaration
          match decl.init with
          | some (.Constant n) =>
              addSym name { type := .Int, attrs := .Static (.Initial n) true }
          | some _ =>
              throw s!"Initializer for file-scope variable '{name}' must be a constant"
          | none =>
              addSym name { type := .Int, attrs := .Static .Tentative true }
      return name

-- ---------------------------------------------------------------------------
-- File-scope function declaration processing
-- ---------------------------------------------------------------------------

/-- Compute the linkage (global Bool) for a top-level function declaration.
    Returns (isDef, global) based on the existing table and storage class. -/
private def processFileScopeFun (name : String) (paramCount : Nat) (isDef : Bool)
    (sc : Option AST.StorageClass) : VarM2 Bool := do
  -- Only explicit `static` forces internal linkage.
  -- `extern` or no specifier: take on existing linkage if visible; else external.
  let isStaticDecl := sc == some .Static
  let existing ← getSym name
  match existing with
  | some { type := .Int, .. } =>
      throw s!"'{name}' was previously declared as a variable"
  | some { type := .Fun existingCount, attrs := .FunAttr existingDefined existingGlobal } =>
      if existingCount != paramCount then
        throw s!"Conflicting declarations of '{name}': different parameter counts"
      if existingDefined && isDef then
        throw s!"Function '{name}' is defined more than once"
      -- Only a true linkage conflict: explicit `static` but prior was external.
      -- `extern`/no-SC on an internally-linked function takes on the existing linkage.
      if isStaticDecl && existingGlobal then
        throw s!"Conflicting linkage for function '{name}'"
      -- Take on existing linkage unless this is an explicit `static` declaration
      let isGlobal := if isStaticDecl then false else existingGlobal
      let newDefined := existingDefined || isDef
      addSym name { type := .Fun paramCount, attrs := .FunAttr newDefined isGlobal }
      return isGlobal
  | _ =>
      -- No prior declaration: external unless `static`
      let isGlobal := !isStaticDecl
      addSym name { type := .Fun paramCount, attrs := .FunAttr isDef isGlobal }
      return isGlobal

-- ---------------------------------------------------------------------------
-- Expression resolution
-- ---------------------------------------------------------------------------

/-- Rename all variables in an expression according to `identMap`.
    Also validates that:
    - `Var(v)` references declared variables (not undeclared or function names).
    - `FunCall(f, args)` references declared functions with the correct arg count.
    - Assignments and postfix operators target `Var` lvalues. -/
private def resolveExp (identMap : IdentMap) : AST.Exp → VarM2 AST.Exp
  | .Constant n     => return .Constant n
  | .Var v          => do
      match lookupIdent identMap v with
      | none => throw s!"Undeclared variable '{v}'"
      | some { info := .Fun _ _, .. } => throw s!"'{v}' is a function, not a variable"
      | some { info := .Var renamed, .. } => return .Var renamed
  | .Unary op e     => return .Unary op (← resolveExp identMap e)
  | .Binary op l r  => return .Binary op (← resolveExp identMap l) (← resolveExp identMap r)
  | .Assignment left right => do
      match left with
      | .Var _ => pure ()
      | _      => throw "Invalid lvalue in assignment"
      return .Assignment (← resolveExp identMap left) (← resolveExp identMap right)
  | .Conditional cond e1 e2 =>
      return .Conditional (← resolveExp identMap cond)
                          (← resolveExp identMap e1)
                          (← resolveExp identMap e2)
  | .PostfixIncr e  => do
      let e' ← resolveExp identMap e
      match e' with
      | .Var _ => return .PostfixIncr e'
      | _      => throw "Invalid lvalue in postfix increment"
  | .PostfixDecr e  => do
      let e' ← resolveExp identMap e
      match e' with
      | .Var _ => return .PostfixDecr e'
      | _      => throw "Invalid lvalue in postfix decrement"
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
-- Statement and block-item resolution (mutually recursive)
-- ---------------------------------------------------------------------------

mutual

/-- Resolve the initial clause of a `for` loop.
    Storage-class specifiers in a for-loop init are detected and rejected. -/
private partial def resolveForInit (identMap : IdentMap) : AST.ForInit → VarM2 (AST.ForInit × IdentMap)
  | .InitExp eOpt => do
      let eOpt' ← eOpt.mapM (resolveExp identMap)
      return (.InitExp eOpt', identMap)
  | .InitDecl decl => do
      -- Storage-class in for-loop initializer is illegal (C11 §6.8.5)
      if decl.storageClass.isSome then
        throw s!"Storage class specifier in for-loop initializer for '{decl.name}'"
      let (identMap', renamed) ← declareLocalVar identMap decl.name
      let init' ← decl.init.mapM (resolveExp identMap')
      return (.InitDecl { name := renamed, init := init', storageClass := none }, identMap')

/-- Resolve all variables in a statement. -/
private partial def resolveStatement (identMap : IdentMap) : AST.Statement → VarM2 AST.Statement
  | .Return e     => return .Return (← resolveExp identMap e)
  | .Expression e => return .Expression (← resolveExp identMap e)
  | .If cond thenStmt elseOpt => do
      let cond' ← resolveExp identMap cond
      let then' ← resolveStatement identMap thenStmt
      match elseOpt with
      | none =>
          return .If cond' then' none
      | some elseStmt => do
          let else' ← resolveStatement identMap elseStmt
          return .If cond' then' (some else')
  | .Compound items => do
      let innerMap := enterScope identMap
      let items'   ← resolveBlockItems innerMap items
      return .Compound items'
  | .While cond body label => do
      let cond' ← resolveExp identMap cond
      let body' ← resolveStatement identMap body
      return .While cond' body' label
  | .DoWhile body cond label => do
      let body' ← resolveStatement identMap body
      let cond' ← resolveExp identMap cond
      return .DoWhile body' cond' label
  | .For init cond post body label => do
      let innerMap             := enterScope identMap
      let (init', innerMap')   ← resolveForInit innerMap init
      let cond'                ← cond.mapM (resolveExp innerMap')
      let post'                ← post.mapM (resolveExp innerMap')
      let body'                ← resolveStatement innerMap' body
      return .For init' cond' post' body' label
  | .Break label    => return .Break label
  | .Continue label => return .Continue label
  | .Switch exp body label cases => do
      let exp'  ← resolveExp identMap exp
      let body' ← resolveStatement identMap body
      return .Switch exp' body' label cases
  | .Case n body label => do
      let body' ← resolveStatement identMap body
      return .Case n body' label
  | .Default body label => do
      let body' ← resolveStatement identMap body
      return .Default body' label
  | .Labeled label stmt => do
      let stmt' ← resolveStatement identMap stmt
      return .Labeled label stmt'
  | .Goto label => return .Goto label
  | .Null       => return .Null

/-- Resolve a single block item.

    For plain local variables (`int x [= e]`): allocate a unique name, add to
    IdentMap with `fromCurrent = true`, resolve the initializer.

    For `static` local variables (`static int x [= n]`): validate that the
    initializer (if present) is a constant, generate a unique name of the form
    `<orig>.<n>`, add a Static symbol-table entry, and map the original name to
    the unique name.

    For `extern` local variables (`extern int x`): the variable name is NOT
    renamed (it refers to the file-scope global).  Error if the variable was
    previously declared as a non-linked local in the same scope.  Error if an
    initializer is given.

    For local function declarations: validate linkage, register in IdentMap.
    A `static` storage class on a block-scope function declaration is an error. -/
private partial def resolveBlockItem (identMap : IdentMap) : AST.BlockItem → VarM2 (IdentMap × AST.BlockItem)
  | .S stmt => do
      let stmt' ← resolveStatement identMap stmt
      return (identMap, .S stmt')
  | .D decl => do
      match decl.storageClass with
      | some .Extern => do
          -- `extern int x;` at block scope
          if decl.init.isSome then
            throw s!"Variable '{decl.name}' declared extern with an initializer"
          -- Error if a non-linked local already occupies this name in the same scope
          match lookupIdent identMap decl.name with
          | some { fromCurrent := true, hasLinkage := false, .. } =>
              throw s!"extern declaration of '{decl.name}' follows a local variable in the same scope"
          | _ => pure ()
          -- Check the symbol table for existing entry
          let existingSym ← getSym decl.name
          match existingSym with
          | none =>
              -- Not declared at file scope; add as external, no local definition
              addSym decl.name { type := .Int, attrs := .Static .NoInitializer true }
          | some { type := .Fun _, .. } =>
              throw s!"'{decl.name}' was previously declared as a function"
          | some _ =>
              -- Already in table (file-scope or earlier extern); keep existing
              pure ()
          -- Map the name to itself (no renaming)
          let entry : IdentEntry := { info := .Var decl.name, fromCurrent := true, hasLinkage := true }
          let identMap' := (decl.name, entry) :: identMap
          return (identMap', .D { decl with name := decl.name })
      | some .Static => do
          -- `static int x [= n];` at block scope
          -- Validate that no name conflict exists in this scope (fromCurrent)
          match lookupIdent identMap decl.name with
          | some { fromCurrent := true, .. } =>
              throw s!"Duplicate declaration of '{decl.name}' in the same scope"
          | _ => pure ()
          -- Initializer must be a constant (or absent → zero)
          let initVal : InitialValue ← do
            match decl.init with
            | none               => pure InitialValue.Tentative
            | some (.Constant n) => pure (InitialValue.Initial n)
            | some _             => throw s!"Initializer for static variable '{decl.name}' must be a constant"
          -- Allocate a unique internal name for this static local
          let renamed ← makeUnique decl.name
          -- Add to symbol table with static attrs (not global since local static)
          addSym renamed { type := .Int, attrs := .Static initVal false }
          -- Map original name to the renamed unique name
          let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
          let identMap' := (decl.name, entry) :: identMap
          -- The AST declaration uses the renamed name (no initializer needed in body)
          return (identMap', .D { decl with name := renamed, init := none })
      | none => do
          -- Plain local automatic variable
          let (identMap', renamed) ← declareLocalVar identMap decl.name
          let init' ← decl.init.mapM (resolveExp identMap')
          return (identMap', .D { name := renamed, init := init', storageClass := none })
  | .FD funDecl => do
      -- Local function declaration
      if funDecl.storageClass == some .Static then
        throw s!"Static storage class on block-scope function declaration for '{funDecl.name}'"
      liftM (checkUniqueParams funDecl.params)
      let identMap' ← declareFun identMap funDecl.name funDecl.params.length false false
      -- Record in symbol table as external function (local extern decls are external)
      let existingSym ← getSym funDecl.name
      match existingSym with
      | none =>
          addSym funDecl.name { type := .Fun funDecl.params.length, attrs := .FunAttr false true }
      | some { type := .Int, .. } =>
          -- A file-scope variable with the same name → conflict
          throw s!"'{funDecl.name}' was previously declared as a variable"
      | _ => pure ()  -- already recorded by file-scope processing
      return (identMap', .FD { funDecl with storageClass := none })

/-- Resolve all block items in a block, threading the identifier map. -/
private partial def resolveBlockItems (identMap : IdentMap) : List AST.BlockItem → VarM2 (List AST.BlockItem)
  | []           => return []
  | item :: rest => do
      let (identMap', item') ← resolveBlockItem identMap item
      let rest'              ← resolveBlockItems identMap' rest
      return item' :: rest'

/-- Declare a plain local automatic variable.
    Validates no duplicate in the current scope (fromCurrent = true).
    Allocates a fresh unique name and returns the updated map. -/
private partial def declareLocalVar (identMap : IdentMap) (name : String) : VarM2 (IdentMap × String) := do
  match lookupIdent identMap name with
  | some { fromCurrent := true, hasLinkage := false, .. } =>
      throw s!"Duplicate declaration of '{name}' in the same scope"
  | some { fromCurrent := true, hasLinkage := true, .. } =>
      -- A linked variable (extern) in the same scope: also an error
      throw s!"Duplicate declaration of '{name}' in the same scope"
  | _ => pure ()
  let renamed ← makeUnique name
  -- Register in symbol table as a local (automatic) variable
  addSym renamed { type := .Int, attrs := .Local }
  let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
  return ((name, entry) :: identMap, renamed)

/-- Validate and register a function declaration in the identifier map.
    Checks compatibility with any existing entry.
    `isGlobal` is passed from the file-scope processing (for block-scope decls
    we always treat as external). -/
private partial def declareFun (identMap : IdentMap) (name : String) (paramCount : Nat) (isDef : Bool)
    (isGlobal : Bool) : VarM2 IdentMap := do
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
    Parameters are added to the scope (same level as function body scope).
    Redeclaring a parameter inside the function body is an error (same scope).
    Returns the updated FunctionDef with renamed params and resolved body. -/
private def resolveFunctionDef (identMap : IdentMap) (f : AST.FunctionDef) : VarM2 AST.FunctionDef := do
  liftM (checkUniqueParams f.params)
  let innerMap := enterScope identMap
  -- Rename each parameter to a unique name and add to the scope
  let (innerMap', renamedParams) ← f.params.foldlM
    (fun (acc : IdentMap × List String) paramName => do
      let (m, names) := acc
      let renamed ← makeUnique paramName
      -- Register parameter in symbol table as a local variable
      addSym renamed { type := .Int, attrs := .Local }
      let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
      let m' := (paramName, entry) :: m
      return (m', names ++ [renamed]))
    (innerMap, [])
  let body' ← resolveBlockItems innerMap' f.body
  return { f with params := renamedParams, body := body' }

-- ---------------------------------------------------------------------------
-- Top-level item resolution
-- ---------------------------------------------------------------------------

/-- Process a single top-level item.
    - `FunDecl`: validate params, register in map and symbol table.
    - `FunDef`: validate params, register, resolve body.
    - `VarDecl` (Chapter 10): apply linkage rules, update symbol table.
      File-scope variables are never renamed. -/
private def resolveTopLevel (identMap : IdentMap) : AST.TopLevel → VarM2 (IdentMap × AST.TopLevel)
  | .VarDecl decl => do
      -- File-scope variable: apply linkage rules, no renaming
      let _ ← processFileScopeVar decl
      -- Add to IdentMap as a variable (unique name = original name at file scope)
      let entry : IdentEntry := { info := .Var decl.name, fromCurrent := true, hasLinkage := true }
      -- We use map-update semantics: if already present, update fromCurrent
      let identMap' :=
        if identMap.any (fun p => p.1 == decl.name) then
          identMap.map fun (n, e) => if n == decl.name then (n, { e with fromCurrent := true }) else (n, e)
        else
          (decl.name, entry) :: identMap
      -- Resolve the initializer expression (for validation purposes, not renaming)
      let init' ← decl.init.mapM (resolveExp identMap')
      return (identMap', .VarDecl { decl with init := init' })
  | .FunDecl fd => do
      liftM (checkUniqueParams fd.params)
      let isGlobal ← processFileScopeFun fd.name fd.params.length false fd.storageClass
      let _ := isGlobal  -- used by symbol table already
      let identMap' ← declareFun identMap fd.name fd.params.length false true
      return (identMap', .FunDecl fd)
  | .FunDef fd => do
      liftM (checkUniqueParams fd.params)
      let isGlobal ← processFileScopeFun fd.name fd.params.length true fd.storageClass
      let _ := isGlobal
      let identMap' ← declareFun identMap fd.name fd.params.length true true
      let fd' ← resolveFunctionDef identMap' fd
      return (identMap', .FunDef fd')

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

/-- Entry point for the identifier resolution pass.
    Returns the renamed program, the final counter value (for TACKY generation),
    and the completed symbol table.
    Chapter 10: also builds and returns a SymbolTable that records linkage and
    initialization information for all declared names. -/
def resolveProgram (p : AST.Program) : Except String (AST.Program × Nat × SymbolTable) := do
  let action : VarM2 AST.Program := do
    let (_, topLevels') ← p.topLevels.foldlM
      (fun (acc : IdentMap × List AST.TopLevel) item => do
        let (m, items) := acc
        let (m', item') ← resolveTopLevel m item
        return (m', items ++ [item']))
      ([], [])
    return { topLevels := topLevels' }
  let initState : VarState := { counter := 0, symTable := [] }
  match action.run initState with
  | .error msg                            => .error msg
  | .ok (prog', { counter, symTable, .. }) => .ok (prog', counter, symTable)

end Semantics
