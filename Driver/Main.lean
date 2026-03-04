import Driver.Driver

-- ---------------------------------------------------------------------------
-- Argument parsing
-- ---------------------------------------------------------------------------

structure Args where
  inputFile : String
  stage     : Driver.Stage

/-- Parse the command-line argument list into `Args`, or return an error
    message.  Exactly one positional argument (the source file) is required;
    at most one stage flag may be supplied.

    Recognised flags and their corresponding pipeline stages:
      --lex      → Stage.Lex
      --parse    → Stage.Parse
      --tacky    → Stage.Tacky
      --codegen  → Stage.Codegen
      -S         → Stage.EmitAssembly
      (none)     → Stage.Full

    Any unrecognised flag (starting with `-`) is treated as an error.
    Multiple positional arguments are also an error. -/
def parseArgs (args : List String) : Except String Args := do
  let mut inputFile : Option String := none
  let mut stage : Driver.Stage := .Full
  for arg in args do
    match arg with
    | "--lex"     => stage := .Lex
    | "--parse"   => stage := .Parse
    | "--tacky"   => stage := .Tacky
    | "--codegen" => stage := .Codegen
    | "-S"        => stage := .EmitAssembly
    | _ =>
      if arg.startsWith "-" then
        throw s!"Unknown option: {arg}"
      else if inputFile.isSome then
        throw "Too many arguments: expected a single source file"
      else
        inputFile := some arg
  match inputFile with
  | none   => throw "No input file specified"
  | some f => return { inputFile := f, stage }

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

/-- Program entry point.
    Parses command-line arguments, then runs the compiler driver.  Any error
    (from argument parsing or from the compiler pipeline) is printed to stderr
    and the process exits with code 1. -/
def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"Error: {msg}"
    IO.Process.exit 1
  | .ok { inputFile, stage } =>
    try
      Driver.run inputFile stage
    catch e =>
      IO.eprintln s!"Error: {e}"
      IO.Process.exit 1
