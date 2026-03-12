import Lexer.Lexer
import Parser.Parser
import Semantics.VarResolution
import Semantics.LoopLabeling
import Semantics.SwitchCollection
import Semantics.LabelResolution
import Semantics.TypeCheck
import Tacky.TackyGen
import AssemblyAST.CodeGen
import AssemblyAST.PseudoReplace
import AssemblyAST.FixUp
import Emission.Emit

namespace Driver

/-- Controls how far the compiler pipeline should proceed. -/
inductive Stage where
  | Lex
  | Parse
  | Validate
  | Tacky
  | Codegen
  | EmitAssembly
  | ObjectFile
  | Full
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Path helpers
-- ---------------------------------------------------------------------------

private def splitPath (path : String) : String × String :=
  let sep := if path.contains '\\' then "\\" else "/"
  let segments := path.splitOn sep
  match segments with
  | [] | [_] => ("", path)
  | _ =>
    let filename := segments.getLast!
    let dirParts := segments.dropLast
    (String.intercalate sep dirParts ++ sep, filename)

private def changeExtension (path : String) (newExt : String) : String :=
  let (dir, filename) := splitPath path
  let nameParts := filename.splitOn "."
  let stem := match nameParts with
    | [] | [_] => filename
    | parts    => String.intercalate "." parts.dropLast
  dir ++ stem ++ newExt

private def dropExtension (path : String) : String :=
  changeExtension path ""

-- ---------------------------------------------------------------------------
-- Shell helper
-- ---------------------------------------------------------------------------

private def runCmd (cmd : String) (args : Array String) (errPrefix : String) : IO Unit := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw (IO.userError s!"{errPrefix}:\n{out.stderr}")

-- ---------------------------------------------------------------------------
-- Backend symbol table construction
-- ---------------------------------------------------------------------------

/-- Convert an `AST.Typ` to the corresponding `AsmType`.
    Chapter 12: UInt → Longword, ULong → Quadword (same widths as signed). -/
private def asmTypeOf : AST.Typ → AssemblyAST.AsmType
  | .Int  | .UInt  => .Longword
  | .Long | .ULong => .Quadword

/-- True iff the type is a signed integer type. -/
private def isSignedTyp : AST.Typ → Bool
  | .Int | .Long   => true
  | .UInt | .ULong => false

/-- Build the backend symbol table from:
    1. The frontend symbol table (all declared variables and functions).
    2. The `typeEnv` from TackyGen (maps generated temporary names → types).

    For each frontend entry:
      - `Obj(typ)` with `Local` attrs   → `ObjEntry(asmType, false)`
      - `Obj(typ)` with `Static` attrs  → `ObjEntry(asmType, true)`
      - `Fun(_, _, retTyp)` with `FunAttr(isDef, _)` → `FunEntry(isDef, retAsmType)`

    For each typeEnv entry not already in the frontend sym table:
      → `ObjEntry(asmType, false)` (TACKY temporaries are always local) -/
private def buildBackendSymTable
    (frontendSt : Semantics.SymbolTable)
    (typeEnv    : List (String × AST.Typ))
    : AssemblyAST.BackendSymTable :=
  -- Convert frontend entries
  let fromFrontend : AssemblyAST.BackendSymTable :=
    frontendSt.filterMap fun (name, entry) =>
      match entry.type, entry.attrs with
      | .Obj typ, .Local =>
          some (name, .ObjEntry (asmTypeOf typ) (isSignedTyp typ) false)
      | .Obj typ, .Static _ _ =>
          some (name, .ObjEntry (asmTypeOf typ) (isSignedTyp typ) true)
      | .Fun _ _ retTyp, .FunAttr isDef _ =>
          some (name, .FunEntry isDef (asmTypeOf retTyp))
      | _, _ => none
  -- Add typeEnv entries for temporaries not in the frontend sym table
  let frontendNames := fromFrontend.map (·.1)
  let fromTypeEnv : AssemblyAST.BackendSymTable :=
    typeEnv.filterMap fun (name, typ) =>
      if frontendNames.contains name then none
      else some (name, .ObjEntry (asmTypeOf typ) (isSignedTyp typ) false)
  fromFrontend ++ fromTypeEnv

-- ---------------------------------------------------------------------------
-- Pipeline steps
-- ---------------------------------------------------------------------------

def preprocess (inputPath : String) : IO String := do
  let preprocessed := changeExtension inputPath ".i"
  runCmd "gcc" #["-E", "-P", inputPath, "-o", preprocessed] "Preprocessing failed"
  return preprocessed

/-- Run the compiler proper on the preprocessed file.

    Pipeline order:
      1. Lex      — tokenize
      2. Parse    — build AST
      3. Validate — VarResolution + LoopLabeling + SwitchCollection + LabelResolution
      4. TypeCheck (Chapter 11) — insert implicit Cast nodes, annotate types
      5. TACKY    — flatten to three-address code; returns (Program, typeEnv)
      6. BuildBST — build backend symbol table from frontend symtable + typeEnv
      7. Codegen (3 passes):
           a. TACKY → Assembly AST (pseudo registers)
           b. PseudoReplace (uses backend sym table for sizes/static decisions)
           c. FixUp (typed instruction fixups, large immediates, AllocateStack)
      8. Emit     — serialize to AT&T-syntax text -/
def compile (preprocessedPath : String) (stage : Stage) : IO (Option String) := do
  let contents ← IO.FS.readFile preprocessedPath
  -- Lex
  let tokens ←
    match Lexer.tokenize contents with
    | .ok tokens => pure tokens
    | .error msg => throw (IO.userError s!"Lex error: {msg}")
  if stage == .Lex then return none
  -- Parse
  let ast ←
    match Parser.parseProgram tokens with
    | .ok ast    => pure ast
    | .error msg => throw (IO.userError s!"Parse error: {msg}")
  if stage == .Parse then return none
  -- Variable/identifier resolution
  let (resolvedAst, initCounter, symTable) ←
    match Semantics.resolveProgram ast with
    | .ok r      => pure r
    | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  -- Loop labeling (assigns unique labels to loops, switches, cases, defaults)
  let resolvedAst ←
    match Semantics.labelLoops resolvedAst with
    | .ok p      => pure p
    | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  -- Chapter 11: Type-checking pass — inserts implicit Cast nodes and
  -- truncates switch case values to the switch expression's type.
  -- Must run BEFORE SwitchCollection so that duplicate detection sees
  -- the truncated values (e.g. `case 2^34:` in an int switch → `case 0:`).
  let resolvedAst ←
    match Semantics.typeCheckProgram resolvedAst symTable with
    | .ok p      => pure p
    | .error msg => throw (IO.userError s!"Type error: {msg}")
  -- Switch case collection (extra credit): validates case lists for duplicates.
  -- Runs after TypeCheck so duplicate detection works on truncated values.
  let resolvedAst ←
    match Semantics.collectSwitchCases resolvedAst with
    | .ok p      => pure p
    | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  if stage == .Validate then return none
  -- Label resolution (extra credit ch6)
  match Semantics.resolveLabels resolvedAst with
  | .ok ()     => pure ()
  | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  -- TACKY generation: returns (program, typeEnv); TypeCheck already ran above
  let (tacky, typeEnv) := Tacky.emitProgram resolvedAst symTable initCounter
  if stage == .Tacky then return none
  -- Build backend symbol table from frontend sym table + TACKY typeEnv
  let bst := buildBackendSymTable symTable typeEnv
  -- Assembly generation pass 1: TACKY → Assembly AST
  let asmAst := AssemblyAST.genProgram tacky bst
  -- Assembly generation pass 2: replace pseudoregisters
  let asmAst := AssemblyAST.replacePseudos asmAst bst
  -- Assembly generation pass 3: fix invalid instructions
  let asmAst := AssemblyAST.fixUp asmAst
  if stage == .Codegen then return none
  -- Emit assembly
  let assemblyPath := changeExtension preprocessedPath ".s"
  IO.FS.writeFile assemblyPath (Emission.emitProgram asmAst)
  return some assemblyPath

def assemble (assemblyPath : String) (outputPath : String) : IO Unit := do
  try
    runCmd "gcc" #[assemblyPath, "-o", outputPath] "Assembly/linking failed"
  catch e =>
    try IO.FS.removeFile assemblyPath catch _ => pure ()
    throw e
  try IO.FS.removeFile assemblyPath catch _ => pure ()

def assembleToObject (assemblyPath : String) (objectPath : String) : IO Unit := do
  try
    runCmd "gcc" #["-c", assemblyPath, "-o", objectPath] "Assembly to object failed"
  catch e =>
    try IO.FS.removeFile assemblyPath catch _ => pure ()
    throw e
  try IO.FS.removeFile assemblyPath catch _ => pure ()

def run (inputPath : String) (stage : Stage) : IO Unit := do
  let preprocessed ← preprocess inputPath
  let assemblyOpt ←
    try
      let asm ← compile preprocessed stage
      try IO.FS.removeFile preprocessed catch _ => pure ()
      pure asm
    catch e =>
      try IO.FS.removeFile preprocessed catch _ => pure ()
      throw e
  match stage, assemblyOpt with
  | .Full, some assemblyPath =>
    assemble assemblyPath (dropExtension inputPath)
  | .ObjectFile, some assemblyPath =>
    assembleToObject assemblyPath (changeExtension inputPath ".o")
  | _, _ =>
    pure ()

end Driver
