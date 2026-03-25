import Driver.Driver
import Tacky.Optimize

-- ---------------------------------------------------------------------------
-- Argument parsing
-- ---------------------------------------------------------------------------

structure Args where
  inputFile        : String
  stage            : Driver.Stage
  extraLinkerFlags : List String   -- e.g. ["-lm"] for math library (Chapter 13)
  optFlags         : Tacky.OptFlags  -- Chapter 19: optimization flags

/-- Parse the command-line argument list into `Args`, or return an error
    message.  Exactly one positional argument (the source file) is required;
    at most one stage flag may be supplied.

    Recognised pipeline stage flags:
      --lex      → Stage.Lex
      --parse    → Stage.Parse
      --validate → Stage.Validate
      --tacky    → Stage.Tacky
      --codegen  → Stage.Codegen
      -S         → Stage.EmitAssembly
      -c         → Stage.ObjectFile
      (none)     → Stage.Full

    Chapter 19 optimization flags (combinable):
      --fold-constants             → enable constant folding
      --eliminate-unreachable-code → enable unreachable code elimination
      --propagate-copies           → enable copy propagation
      --eliminate-dead-stores      → enable dead store elimination
      --optimize                   → enable all four passes

    Flags of the form `-l<name>` (e.g. `-lm`) are collected and passed
    through to the linker unchanged.

    Any other unrecognised flag (starting with `-`) is treated as an error.
    Multiple positional arguments are also an error. -/
def parseArgs (args : List String) : Except String Args := do
  let mut inputFile        : Option String  := none
  let mut stage            : Driver.Stage   := .Full
  let mut extraLinkerFlags : List String    := []
  let mut optFlags         : Tacky.OptFlags := {}
  for arg in args do
    match arg with
    | "--lex"      => stage := .Lex
    | "--parse"    => stage := .Parse
    | "--validate" => stage := .Validate
    | "--tacky"    => stage := .Tacky
    | "--codegen"  => stage := .Codegen
    | "-S"         => stage := .EmitAssembly
    | "-c"         => stage := .ObjectFile
    -- Chapter 19: optimization flags
    | "--fold-constants"             => optFlags := { optFlags with foldConstants        := true }
    | "--eliminate-unreachable-code" => optFlags := { optFlags with eliminateUnreachable := true }
    | "--propagate-copies"           => optFlags := { optFlags with propagateCopies      := true }
    | "--eliminate-dead-stores"      => optFlags := { optFlags with eliminateDeadStores  := true }
    | "--optimize"                   =>
        optFlags := { foldConstants := true, eliminateUnreachable := true,
                      propagateCopies := true, eliminateDeadStores := true }
    | _ =>
      if arg.startsWith "-l" then
        -- Linker library flags (e.g. -lm): pass through to gcc
        extraLinkerFlags := extraLinkerFlags ++ [arg]
      else if arg.startsWith "-" then
        throw s!"Unknown option: {arg}"
      else if inputFile.isSome then
        throw "Too many arguments: expected a single source file"
      else
        inputFile := some arg
  match inputFile with
  | none   => throw "No input file specified"
  | some f => return { inputFile := f, stage, extraLinkerFlags, optFlags }

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
  | .ok { inputFile, stage, extraLinkerFlags, optFlags } =>
    try
      Driver.run inputFile stage extraLinkerFlags optFlags
    catch e =>
      IO.eprintln s!"Error: {e}"
      IO.Process.exit 1
