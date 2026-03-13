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

private structure VarState where
  counter  : Nat
  symTable : SymbolTable

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
-- Helper: extract integer value from a constant expression (for static inits)
-- ---------------------------------------------------------------------------

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
  | _                          => none

/-- Extract an `InitialValue` from a constant expression given the variable's type.
    For integer types: wraps in `Initial(n)`.
    For `Double`:     wraps in `DoubleInitial(f)`.  (Chapter 13) -/
private def extractInitialValue (varTyp : AST.Typ) (e : AST.Exp) : Option InitialValue :=
  match varTyp with
  | .Double =>
      match extractDoubleConst e with
      | some f => some (.DoubleInitial f)
      | none   => none
  | _ =>
      match extractConst e with
      | some n => some (.Initial n)
      | none   => none

-- ---------------------------------------------------------------------------
-- File-scope variable declaration processing
-- ---------------------------------------------------------------------------

/-- Process a file-scope variable declaration, applying linkage rules. -/
private def processFileScopeVar (decl : AST.Declaration) : VarM2 String := do
  let name := decl.name
  let varType := decl.typ  -- Chapter 11: use declared type
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
          | some e, .Initial _ | some e, .DoubleInitial _ =>
              match extractInitialValue varType e with
              | some _ => throw s!"Variable '{name}' has conflicting definitions"
              | none   => throw s!"Variable '{name}' has conflicting definitions"
          | some e, _ =>
              match extractInitialValue varType e with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv false }
              | none => throw s!"Initializer for static variable '{name}' must be a constant"
          | none, .Initial _ | none, .DoubleInitial _ =>
              pure ()
          | none, _ =>
              pure ()
      | _ =>
          match decl.init with
          | some e =>
              match extractInitialValue varType e with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv false }
              | none => throw s!"Initializer for file-scope static variable '{name}' must be a constant"
          | none =>
              addSym name { type := .Obj varType, attrs := .Static .Tentative false }
      return name
  | none => do
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
          | some _, .Initial _ | some _, .DoubleInitial _ =>
              throw s!"Variable '{name}' has conflicting definitions"
          | some e, _ =>
              match extractInitialValue varType e with
              | some iv =>
                  addSym name { type := .Obj varType, attrs := .Static iv true }
              | none => throw s!"Initializer for file-scope variable '{name}' must be a constant"
          | none, .NoInitializer =>
              addSym name { type := .Obj varType, attrs := .Static .Tentative true }
          | none, _ =>
              pure ()
      | _ =>
          match decl.init with
          | some e =>
              match extractInitialValue varType e with
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
  | .Constant c     => return .Constant c
  | .Var v          => do
      match lookupIdent identMap v with
      | none => throw s!"Undeclared variable '{v}'"
      | some { info := .Fun _ _, .. } => throw s!"'{v}' is a function, not a variable"
      | some { info := .Var renamed, .. } => return .Var renamed
  | .Cast t e       => return .Cast t (← resolveExp identMap e)
  | .Unary op e     => return .Unary op (← resolveExp identMap e)
  | .Binary op l r  => return .Binary op (← resolveExp identMap l) (← resolveExp identMap r)
  | .Assignment left right => do
      match left with
      | .Var _         => pure ()
      | .Dereference _ => pure ()   -- Chapter 14: dereference is a valid lvalue
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
      | _              => throw "Invalid lvalue in postfix increment"
  | .PostfixDecr e  => do
      let e' ← resolveExp identMap e
      match e' with
      | .Var _         => return .PostfixDecr e'
      | .Dereference _ => return .PostfixDecr e'   -- Chapter 14: (*p)--
      | _              => throw "Invalid lvalue in postfix decrement"
  -- Chapter 14: address-of and dereference
  | .AddrOf e      => return .AddrOf      (← resolveExp identMap e)
  | .Dereference e => return .Dereference (← resolveExp identMap e)
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

private partial def resolveForInit (identMap : IdentMap) : AST.ForInit → VarM2 (AST.ForInit × IdentMap)
  | .InitExp eOpt => do
      let eOpt' ← eOpt.mapM (resolveExp identMap)
      return (.InitExp eOpt', identMap)
  | .InitDecl decl => do
      if decl.storageClass.isSome then
        throw s!"Storage class specifier in for-loop initializer for '{decl.name}'"
      let (identMap', renamed) ← declareLocalVar identMap decl.name decl.typ
      let init' ← decl.init.mapM (resolveExp identMap')
      return (.InitDecl { decl with name := renamed, init := init', storageClass := none }, identMap')

private partial def resolveStatement (identMap : IdentMap) : AST.Statement → VarM2 AST.Statement
  | .Return e     => return .Return (← resolveExp identMap e)
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
      let items'   ← resolveBlockItems innerMap items
      return .Compound items'
  | .While cond body label => do
      return .While (← resolveExp identMap cond) (← resolveStatement identMap body) label
  | .DoWhile body cond label => do
      return .DoWhile (← resolveStatement identMap body) (← resolveExp identMap cond) label
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
      match decl.storageClass with
      | some .Extern => do
          if decl.init.isSome then
            throw s!"Variable '{decl.name}' declared extern with an initializer"
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
          match lookupIdent identMap decl.name with
          | some { fromCurrent := true, .. } =>
              throw s!"Duplicate declaration of '{decl.name}' in the same scope"
          | _ => pure ()
          let initVal : InitialValue ← do
            match decl.init with
            | none   => pure .Tentative
            | some e =>
                -- Chapter 13: use extractInitialValue to support both integer and double constants
                match extractInitialValue decl.typ e with
                | some iv => pure iv
                | none    => throw s!"Initializer for static variable '{decl.name}' must be a constant"
          let renamed ← makeUnique decl.name
          addSym renamed { type := .Obj decl.typ, attrs := .Static initVal false }
          let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
          let identMap' := (decl.name, entry) :: identMap
          return (identMap', .D { decl with name := renamed, init := none })
      | none => do
          let (identMap', renamed) ← declareLocalVar identMap decl.name decl.typ
          let init' ← decl.init.mapM (resolveExp identMap')
          return (identMap', .D { name := renamed, typ := decl.typ, init := init', storageClass := none })
  | .FD funDecl => do
      if funDecl.storageClass == some .Static then
        throw s!"Static storage class on block-scope function declaration for '{funDecl.name}'"
      liftM (checkUniqueParams funDecl.params)
      let paramTypes := funDecl.params.map (·.1)
      let identMap' ← declareFun identMap funDecl.name funDecl.params.length false false
      let existingSym ← getSym funDecl.name
      match existingSym with
      | none =>
          addSym funDecl.name { type := .Fun funDecl.params.length paramTypes funDecl.retTyp,
                                attrs := .FunAttr false true }
      | some { type := .Obj _, .. } =>
          throw s!"'{funDecl.name}' was previously declared as a variable"
      | _ => pure ()
      return (identMap', .FD { funDecl with storageClass := none })

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
  -- Rename each (typ, paramName) pair to a unique name
  let (innerMap', renamedParams) ← f.params.foldlM
    (fun (acc : IdentMap × List (AST.Typ × String)) (typ, paramName) => do
      let (m, names) := acc
      let renamed ← makeUnique paramName
      -- Register renamed param in symbol table with its declared type
      addSym renamed { type := .Obj typ, attrs := .Local }
      let entry : IdentEntry := { info := .Var renamed, fromCurrent := true, hasLinkage := false }
      let m' := (paramName, entry) :: m
      return (m', names ++ [(typ, renamed)]))
    (innerMap, [])
  let body' ← resolveBlockItems innerMap' f.body
  return { f with params := renamedParams, body := body' }

-- ---------------------------------------------------------------------------
-- Top-level item resolution
-- ---------------------------------------------------------------------------

private def resolveTopLevel (identMap : IdentMap) : AST.TopLevel → VarM2 (IdentMap × AST.TopLevel)
  | .VarDecl decl => do
      let _ ← processFileScopeVar decl
      let entry : IdentEntry := { info := .Var decl.name, fromCurrent := true, hasLinkage := true }
      let identMap' :=
        if identMap.any (fun p => p.1 == decl.name) then
          identMap.map fun (n, e) => if n == decl.name then (n, { e with fromCurrent := true }) else (n, e)
        else
          (decl.name, entry) :: identMap
      let init' ← decl.init.mapM (resolveExp identMap')
      return (identMap', .VarDecl { decl with init := init' })
  | .FunDecl fd => do
      liftM (checkUniqueParams fd.params)
      let paramTypes := fd.params.map (·.1)
      let _ ← processFileScopeFun fd.name fd.params.length paramTypes fd.retTyp false fd.storageClass
      let identMap' ← declareFun identMap fd.name fd.params.length false true
      return (identMap', .FunDecl fd)
  | .FunDef fd => do
      liftM (checkUniqueParams fd.params)
      let paramTypes := fd.params.map (·.1)
      let _ ← processFileScopeFun fd.name fd.params.length paramTypes fd.retTyp true fd.storageClass
      let identMap' ← declareFun identMap fd.name fd.params.length true true
      let fd' ← resolveFunctionDef identMap' fd
      return (identMap', .FunDef fd')

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

/-- Entry point for the identifier resolution pass.
    Returns the renamed program, the final counter value, and the symbol table. -/
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
