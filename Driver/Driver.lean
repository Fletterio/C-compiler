import Lexer.Lexer
import Parser.Parser
import AssemblyAST.CodeGen
import Emission.Emit

namespace Driver

/-- Controls how far the compiler pipeline should proceed. -/
inductive Stage where
  | Lex           -- run only the lexer (--lex)
  | Parse         -- run lexer and parser (--parse)
  | Codegen       -- run lexer, parser, and assembly generation (--codegen)
  | EmitAssembly  -- compile to assembly but do not assemble or link (-S)
  | Full          -- complete compilation (default)
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Path helpers
-- ---------------------------------------------------------------------------

/-- Split `path` into its directory prefix (including trailing separator) and filename. -/
private def splitPath (path : String) : String × String :=
  let sep := if path.contains '\\' then "\\" else "/"
  let segments := path.splitOn sep
  match segments with
  | [] | [_] => ("", path)
  | _ =>
    let filename := segments.getLast!
    let dirParts := segments.dropLast
    (String.intercalate sep dirParts ++ sep, filename)

/-- Return `path` with its extension replaced by `newExt` (include the leading dot, e.g. ".i").
    Pass `""` to strip the extension entirely. -/
private def changeExtension (path : String) (newExt : String) : String :=
  let (dir, filename) := splitPath path
  let nameParts := filename.splitOn "."
  let stem := match nameParts with
    | [] | [_] => filename
    | parts    => String.intercalate "." parts.dropLast
  dir ++ stem ++ newExt

/-- Strip the extension from `path`, preserving the directory component. -/
private def dropExtension (path : String) : String :=
  changeExtension path ""

-- ---------------------------------------------------------------------------
-- Shell helper
-- ---------------------------------------------------------------------------

/-- Run `cmd args`. Throw an `IO.Error` if the process exits with a nonzero
    code, including the captured stderr in the message. -/
private def runCmd (cmd : String) (args : Array String) (errPrefix : String) : IO Unit := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw (IO.userError s!"{errPrefix}:\n{out.stderr}")

-- ---------------------------------------------------------------------------
-- Pipeline steps
-- ---------------------------------------------------------------------------

/-- Step 1 — Preprocess `inputPath` with GCC, writing a `.i` file.
    Returns the path of the preprocessed file. -/
def preprocess (inputPath : String) : IO String := do
  let preprocessed := changeExtension inputPath ".i"
  runCmd "gcc" #["-E", "-P", inputPath, "-o", preprocessed] "Preprocessing failed"
  return preprocessed

/-- Step 2 — Compile `preprocessedPath` up to `stage` (stub).
    Returns `some assemblyPath` when an assembly file was emitted,
    or `none` for stages that produce no output file. -/
def compile (preprocessedPath : String) (stage : Stage) : IO (Option String) := do
  let contents ← IO.FS.readFile preprocessedPath
  -- Lex
  let _tokens ←
    match Lexer.tokenize contents with
    | .ok tokens => pure tokens
    | .error msg => throw (IO.userError s!"Lex error: {msg}")
  -- Parse
  let _ast ←
    match Parser.parseProgram _tokens with
    | .ok ast   => pure ast
    | .error msg => throw (IO.userError s!"Parse error: {msg}")
  -- Assembly generation
  let _asmAst := AssemblyAST.genProgram _ast
  match stage with
  | .Lex | .Parse | .Codegen =>
    return none
  | .EmitAssembly | .Full =>
    let assemblyPath := changeExtension preprocessedPath ".s"
    IO.FS.writeFile assemblyPath (Emission.emitProgram _asmAst)
    return some assemblyPath

/-- Step 3 — Assemble and link `assemblyPath`, writing the executable to
    `outputPath`. Deletes the assembly file when done (even on failure). -/
def assemble (assemblyPath : String) (outputPath : String) : IO Unit := do
  try
    runCmd "gcc" #[assemblyPath, "-o", outputPath] "Assembly/linking failed"
  catch e =>
    try IO.FS.removeFile assemblyPath catch _ => pure ()
    throw e
  try IO.FS.removeFile assemblyPath catch _ => pure ()

-- ---------------------------------------------------------------------------
-- Top-level driver
-- ---------------------------------------------------------------------------

/-- Run the full compiler driver pipeline on the C source file at `inputPath`,
    stopping at `stage`. -/
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

  -- Step 3: assemble/link (only for full compilation)
  match stage, assemblyOpt with
  | .Full, some assemblyPath =>
    assemble assemblyPath (dropExtension inputPath)
  | _, _ =>
    -- EmitAssembly keeps the .s file; Lex/Parse/Codegen produce no output.
    pure ()

end Driver
