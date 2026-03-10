import Lexer.Lexer
import Parser.Parser
import Semantics.VarResolution
import Semantics.LoopLabeling
import Semantics.SwitchCollection
import Semantics.LabelResolution
import Tacky.TackyGen
import AssemblyAST.CodeGen
import AssemblyAST.PseudoReplace
import AssemblyAST.FixUp
import Emission.Emit

namespace Driver

/-- Controls how far the compiler pipeline should proceed.
    Each constructor corresponds to a command-line flag; the pipeline runs all
    stages up to and including the named one, then stops without producing
    any output file (except `EmitAssembly` and `Full`, which write files). -/
inductive Stage where
  | Lex           -- run only the lexer (--lex)
  | Parse         -- run lexer and parser (--parse)
  | Validate      -- run through semantic analysis (--validate)
  | Tacky         -- run through TACKY generation (--tacky)
  | Codegen       -- run through assembly generation (--codegen)
  | EmitAssembly  -- compile to assembly but do not assemble or link (-S)
  | ObjectFile    -- compile to object file but do not link (-c)
  | Full          -- complete compilation (default)
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Path helpers
-- ---------------------------------------------------------------------------

/-- Split `path` into its directory prefix (including trailing separator) and
    filename.  Detects Windows-style paths by the presence of `\\`.
    A path with no separator is treated as a bare filename in the current
    directory, returning `("", path)`. -/
private def splitPath (path : String) : String × String :=
  let sep := if path.contains '\\' then "\\" else "/"
  let segments := path.splitOn sep
  match segments with
  | [] | [_] => ("", path)
  | _ =>
    let filename := segments.getLast!
    let dirParts := segments.dropLast
    (String.intercalate sep dirParts ++ sep, filename)

/-- Return `path` with its extension replaced by `newExt`.
    `newExt` should include the leading dot (e.g. `".s"`).
    Pass `""` to strip the extension entirely.
    The stem is everything up to (but not including) the last `.` in the
    filename; if there is no `.`, the whole filename is the stem. -/
private def changeExtension (path : String) (newExt : String) : String :=
  let (dir, filename) := splitPath path
  let nameParts := filename.splitOn "."
  let stem := match nameParts with
    | [] | [_] => filename
    | parts    => String.intercalate "." parts.dropLast
  dir ++ stem ++ newExt

/-- Strip the extension from `path`, preserving the directory component.
    Used to derive the output executable path from the source file path. -/
private def dropExtension (path : String) : String :=
  changeExtension path ""

-- ---------------------------------------------------------------------------
-- Shell helper
-- ---------------------------------------------------------------------------

/-- Spawn `cmd` with `args` and wait for it to finish.
    If the process exits with a nonzero code, throws an `IO.Error` whose
    message is `errPrefix` followed by the process's stderr output. -/
private def runCmd (cmd : String) (args : Array String) (errPrefix : String) : IO Unit := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw (IO.userError s!"{errPrefix}:\n{out.stderr}")

-- ---------------------------------------------------------------------------
-- Pipeline steps
-- ---------------------------------------------------------------------------

/-- Step 1 — Run the C preprocessor on `inputPath` via GCC.
    The `-E` flag runs only the preprocessor; `-P` suppresses line-number
    directives.  The output is written to a `.i` file next to the source.
    Returns the path of that preprocessed file. -/
def preprocess (inputPath : String) : IO String := do
  let preprocessed := changeExtension inputPath ".i"
  runCmd "gcc" #["-E", "-P", inputPath, "-o", preprocessed] "Preprocessing failed"
  return preprocessed

/-- Step 2 — Run the compiler proper on the preprocessed file.
    Executes the full pipeline in order, returning early at whichever `stage`
    was requested.  Stages that do not emit a file return `none`; stages that
    write an assembly file return `some assemblyPath`.

    Pipeline order:
      1. Lex      — tokenize the source
      2. Parse    — build the AST (list of top-level items)
      3. Validate — identifier resolution (rename locals, reject invalid programs)
                    + loop labeling, switch collection, label resolution
      4. TACKY    — flatten nested expressions into three-address code
      5. Codegen (3 passes):
           a. TACKY → Assembly AST (with pseudoregisters)
           b. Replace pseudoregisters with stack slots or Data operands
           c. Insert AllocateStack (16-byte aligned); fix mem-to-mem instructions
      6. Emit     — serialise the assembly AST to AT&T-syntax text

    Chapter 10 changes:
      - resolveProgram now returns (Program, counter, SymbolTable).
      - emitProgram takes the SymbolTable to emit static variables and set
        the `global` flag on functions.
      - replacePseudos takes the SymbolTable to map static Pseudo → Data
        instead of Stack.
      - genProgram handles both Function and StaticVariable top-level items.
      - fixUp and emitProgram pass StaticVariable items through unchanged,
        emitting .data/.bss directives for them in the final output. -/
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
    | .ok ast   => pure ast
    | .error msg => throw (IO.userError s!"Parse error: {msg}")
  if stage == .Parse then return none
  -- Variable/identifier resolution: rename locals, validate function calls,
  -- reject undeclared/duplicate identifiers.
  -- Chapter 10: also builds a SymbolTable with linkage and init info.
  let (resolvedAst, initCounter, symTable) ←
    match Semantics.resolveProgram ast with
    | .ok r      => pure r
    | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  -- Loop labeling: annotate loops/switch/break/continue with unique IDs;
  -- rejects break/continue outside of loops (or switch for break).
  let resolvedAst ←
    match Semantics.labelLoops resolvedAst with
    | .ok p      => pure p
    | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  -- Switch case collection (extra credit): collect and validate case/default
  -- labels for each switch statement and attach them to the Switch AST node.
  let resolvedAst ←
    match Semantics.collectSwitchCases resolvedAst with
    | .ok p      => pure p
    | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  if stage == .Validate then return none
  -- Label resolution (extra credit ch6): validates goto targets and duplicate labels.
  match Semantics.resolveLabels resolvedAst with
  | .ok ()     => pure ()
  | .error msg => throw (IO.userError s!"Semantic error: {msg}")
  -- TACKY generation: flatten AST to three-address code.
  -- Chapter 10: takes the SymbolTable to determine function linkage and to
  -- emit StaticVariable top-level items from symbol table entries.
  let tacky := Tacky.emitProgram resolvedAst symTable initCounter
  if stage == .Tacky then return none
  -- Assembly generation pass 1: TACKY → Assembly AST (with pseudoregisters).
  -- Chapter 10: handles Function and StaticVariable top-level items.
  let asmAst := AssemblyAST.genProgram tacky
  -- Assembly generation pass 2: replace pseudoregisters with stack slots or Data.
  -- Chapter 10: consults the SymbolTable to map static variables to Data operands.
  let asmAst := AssemblyAST.replacePseudos asmAst symTable
  -- Assembly generation pass 3: insert AllocateStack (16-byte aligned),
  -- fix invalid instructions (mem-to-mem, Data-to-Data treated the same as Stack).
  let asmAst := AssemblyAST.fixUp asmAst
  if stage == .Codegen then return none
  -- Emit assembly: serialize assembly AST to AT&T-syntax text.
  -- Chapter 10: emits .text/.globl for functions and .data/.bss for static vars.
  let assemblyPath := changeExtension preprocessedPath ".s"
  IO.FS.writeFile assemblyPath (Emission.emitProgram asmAst)
  return some assemblyPath

/-- Step 3a — Assemble and link `assemblyPath` into an executable at `outputPath`.
    Delegates to GCC, which handles both assembly and linking in one step.
    Deletes the `.s` file afterwards regardless of whether linking succeeds,
    since keeping a partial assembly file around would be confusing. -/
def assemble (assemblyPath : String) (outputPath : String) : IO Unit := do
  try
    runCmd "gcc" #[assemblyPath, "-o", outputPath] "Assembly/linking failed"
  catch e =>
    try IO.FS.removeFile assemblyPath catch _ => pure ()
    throw e
  try IO.FS.removeFile assemblyPath catch _ => pure ()

/-- Step 3b — Assemble `assemblyPath` into an object file at `objectPath`
    without linking.  Uses `gcc -c`, which instructs GCC to stop after assembly.
    Deletes the `.s` file afterwards. -/
def assembleToObject (assemblyPath : String) (objectPath : String) : IO Unit := do
  try
    runCmd "gcc" #["-c", assemblyPath, "-o", objectPath] "Assembly to object failed"
  catch e =>
    try IO.FS.removeFile assemblyPath catch _ => pure ()
    throw e
  try IO.FS.removeFile assemblyPath catch _ => pure ()

-- ---------------------------------------------------------------------------
-- Top-level driver
-- ---------------------------------------------------------------------------

/-- Run the full compiler driver pipeline on the C source file at `inputPath`,
    stopping at `stage`.
    The preprocessed `.i` file is always deleted after `compile` returns,
    whether or not compilation succeeded.  The assembly `.s` file is deleted
    after linking in `Full` mode; in `EmitAssembly` mode it is kept as the
    final output. -/
def run (inputPath : String) (stage : Stage) : IO Unit := do
  -- Step 1: preprocess
  let preprocessed ← preprocess inputPath

  -- Step 2: compile (always delete the .i file afterwards)
  let assemblyOpt ←
    try
      let asm ← compile preprocessed stage
      try IO.FS.removeFile preprocessed catch _ => pure ()
      pure asm
    catch e =>
      try IO.FS.removeFile preprocessed catch _ => pure ()
      throw e

  -- Step 3: assemble/link/object depending on stage
  match stage, assemblyOpt with
  | .Full, some assemblyPath =>
    -- Full compilation: assemble + link into an executable
    assemble assemblyPath (dropExtension inputPath)
  | .ObjectFile, some assemblyPath =>
    -- Object file only: assemble into .o without linking
    assembleToObject assemblyPath (changeExtension inputPath ".o")
  | _, _ =>
    -- EmitAssembly keeps the .s file; Lex/Parse/Tacky/Codegen produce no output.
    pure ()

end Driver
