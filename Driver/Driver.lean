import Lexer.Lexer
import Parser.Parser
import Semantics.VarResolution
import Semantics.LoopLabeling
import Semantics.SwitchCollection
import Semantics.LabelResolution
import Semantics.TypeCheck
import Tacky.TackyGen
import Tacky.Optimize
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
    Chapter 12: UInt → Longword, ULong → Quadword (same widths as signed).
    Chapter 13: Double → Double (8-byte, uses XMM registers).
    Chapter 14: Pointer → Quadword (pointers are 8-byte, like unsigned long).
    Chapter 15: Array(elem, n) → ByteArray(totalBytes, alignment) so that
      PseudoReplace can reserve the right amount of stack space.
    Chapter 18: Struct/Union → ByteArray(totalSize, alignment) looked up from TypeTable. -/
private def asmTypeOf (tt : Semantics.TypeTable) : AST.Typ → AssemblyAST.AsmType
  | .Int  | .UInt  => .Longword
  | .Long | .ULong => .Quadword
  | .Double        => .Double
  | .Pointer _     => .Quadword   -- Chapter 14: pointer is 8-byte
  | .Array elem n  =>             -- Chapter 15/18: array occupies totalBytes with alignment
      -- Chapter 18: for arrays of struct/union, elem.sizeOf returns 0 (structs have no
      -- statically-known size); look up the actual size from the TypeTable instead.
      let elemSize : Nat := match elem with
        | .Struct tag | .Union tag =>
            match Semantics.lookupTypeTable tt tag with
            | some sd => sd.size
            | none    => 0
        | _ => elem.sizeOf
      let totalBytes := elemSize * n
      -- Alignment: for struct/union elements, use the struct's alignment from TypeTable.
      -- For scalar elements, use the array's own alignOf (which handles the ≥16-byte rule).
      let elemAlign : Nat := match elem with
        | .Struct tag | .Union tag =>
            match Semantics.lookupTypeTable tt tag with
            | some sd => sd.alignment
            | none    => 1
        | _ => elem.alignOf
      -- Apply the ≥16-byte alignment rule: arrays of ≥16 bytes are 16-byte aligned.
      let alignment  := if totalBytes >= 16 then max elemAlign 16 else elemAlign
      .ByteArray totalBytes alignment
  | .Char | .SChar | .UChar => .Byte   -- Chapter 16: char types are 1-byte
  | .Void            => .Longword      -- Chapter 17: void has no AsmType; use Longword as sentinel
  -- Chapter 18: struct/union — look up size and alignment from the TypeTable.
  | .Struct tag | .Union tag =>
      match Semantics.lookupTypeTable tt tag with
      | some sd => .ByteArray sd.size sd.alignment
      | none    => .ByteArray 0 1

/-- True iff the type is a signed integer type.
    Double returns false (sign concept doesn't apply to IEEE 754 types).
    Chapter 14: Pointer returns false (treated as unsigned for code generation).
    Chapter 15: Array returns false (arrays are not scalars). -/
private def isSignedTyp : AST.Typ → Bool
  | .Int | .Long     => true
  | .UInt | .ULong   => false
  | .Double          => false
  | .Pointer _       => false   -- Chapter 14: pointers are unsigned
  | .Array _ _       => false   -- Chapter 15: arrays are aggregate types
  | .Char | .SChar   => true    -- Chapter 16: char and signed char are signed
  | .UChar           => false   -- Chapter 16: unsigned char is unsigned
  | .Void            => false   -- Chapter 17: void has no sign
  | .Struct _ | .Union _ => false   -- Chapter 18: aggregate types are not signed scalars

/-- Build the backend symbol table from:
    1. The frontend symbol table (all declared variables and functions).
    2. The `typeEnv` from TackyGen (maps generated temporary names → types).
    3. Chapter 13: `floatConsts` — float literal labels (`.LfpC.N`) that must be
       treated as static (isStatic = true) so PseudoReplace maps them to Data(name).

    For each frontend entry:
      - `Obj(typ)` with `Local` attrs   → `ObjEntry(asmType, false)`
      - `Obj(typ)` with `Static` attrs  → `ObjEntry(asmType, true)`
      - `Fun(_, _, retTyp)` with `FunAttr(isDef, _)` → `FunEntry(isDef, retAsmType)`

    For each typeEnv entry not already in the frontend sym table:
      → `ObjEntry(asmType, false)` (TACKY temporaries are always local)

    Float const labels override with `isStatic = true` (prepended, lookupBst finds first). -/
private def buildBackendSymTable
    (frontendSt  : Semantics.SymbolTable)
    (typeEnv     : List (String × AST.Typ))
    (tt          : Semantics.TypeTable := [])   -- Chapter 18: struct/union layouts
    (floatConsts : List (String × Float) := [])
    (strConsts   : List (String × String) := [])   -- Chapter 16
    : AssemblyAST.BackendSymTable :=
  -- Convert frontend entries
  let fromFrontend : AssemblyAST.BackendSymTable :=
    frontendSt.filterMap fun (name, entry) =>
      match entry.type, entry.attrs with
      | .Obj typ, .Local =>
          some (name, .ObjEntry (asmTypeOf tt typ) (isSignedTyp typ) false)
      | .Obj typ, .Static _ _ =>
          some (name, .ObjEntry (asmTypeOf tt typ) (isSignedTyp typ) true)
      | .Fun _ _ retTyp, .FunAttr isDef _ =>
          some (name, .FunEntry isDef (asmTypeOf tt retTyp))
      | _, _ => none
  -- Add typeEnv entries for temporaries not in the frontend sym table.
  -- Float constant labels from internFloat() are in typeEnv with type Double;
  -- they will be overridden below to have isStatic = true.
  let frontendNames := fromFrontend.map (·.1)
  let fromTypeEnv : AssemblyAST.BackendSymTable :=
    typeEnv.filterMap fun (name, typ) =>
      if frontendNames.contains name then none
      else some (name, .ObjEntry (asmTypeOf tt typ) (isSignedTyp typ) false)
  -- Chapter 13: float const labels must be static (RIP-relative Data operands).
  -- Prepend so lookupBst finds these first (overriding the isStatic=false entries
  -- that buildBackendSymTable would otherwise create from typeEnv).
  let floatConstBst : AssemblyAST.BackendSymTable :=
    floatConsts.map fun (name, _) => (name, .ObjEntry .Double false true)
  -- Chapter 16: string const labels must be static (RIP-relative Data operands).
  -- Each string literal label refers to a ByteArray(n+1, 1) in .rodata.
  let strConstBst : AssemblyAST.BackendSymTable :=
    strConsts.map fun (name, s) => (name, .ObjEntry (.ByteArray (s.length + 1) 1) false true)
  strConstBst ++ floatConstBst ++ fromFrontend ++ fromTypeEnv

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
def compile (preprocessedPath : String) (stage : Stage)
    (optFlags : Tacky.OptFlags := {}) : IO (Option String) := do
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
  -- Chapter 18: resolveProgram now returns a 4-tuple including the TypeTable
  -- (which maps struct/union tags to their layout: member offsets, size, alignment).
  let (resolvedAst, initCounter, symTable, typeTable) ←
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
    match Semantics.typeCheckProgram resolvedAst symTable typeTable with
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
  -- TACKY generation: returns (program, typeEnv, floatConsts, needsNegZero, strConsts)
  -- Chapter 13: floatConsts = list of (label, Float) for float literal constants;
  --             needsNegZero = true if any double negation was emitted (needs .Lneg_zero).
  -- Chapter 16: strConsts = list of (label, String) for string literal constants.
  -- Chapter 18: pass typeTable so TackyGen can look up struct/union member offsets.
  let (tacky, typeEnv, floatConsts, needsNegZero, strConsts) :=
    Tacky.emitProgram resolvedAst symTable initCounter typeTable
  -- Chapter 19: run optimization passes (constant folding, etc.) on the TACKY IR.
  -- optimizeProgram threads the typeEnv and floatConsts through all functions so that
  -- any new float constants produced by the optimizer are recorded in floatConsts/typeEnv
  -- and will be picked up by buildBackendSymTable and emitted as StaticConstant items.
  let (tacky, floatConsts, typeEnv) :=
    Tacky.optimizeProgram tacky optFlags typeEnv floatConsts
  if stage == .Tacky then return none
  -- Build backend symbol table from frontend sym table + TACKY typeEnv.
  -- Float const labels (in floatConsts) need isStatic = true so PseudoReplace maps
  -- them to Data(name) operands instead of stack slots.
  -- Chapter 16: string const labels (in strConsts) also need isStatic = true.
  -- Chapter 18: pass typeTable so asmTypeOf can compute ByteArray size/alignment for structs.
  let bst := buildBackendSymTable symTable typeEnv typeTable floatConsts strConsts
  -- Build the combined AST type map for CodeGen (used to classify struct arguments/returns
  -- by the System V AMD64 ABI rules).  Merges frontend symbol table Obj entries with
  -- the TACKY typeEnv (which adds generated temporaries).
  let frontendTypMap : List (String × AST.Typ) :=
    symTable.filterMap fun (name, entry) =>
      match entry.type with
      | .Obj t => some (name, t)
      | _      => none
  let typMap : List (String × AST.Typ) := frontendTypMap ++ typeEnv
  -- Assembly generation pass 1: TACKY → Assembly AST
  -- Chapter 18: pass typeTable and typMap for struct ABI classification.
  let asmAst := AssemblyAST.genProgram tacky bst typeTable typMap
  -- Assembly generation pass 2: replace pseudoregisters
  let asmAst := AssemblyAST.replacePseudos asmAst bst
  -- Assembly generation pass 3: fix invalid instructions
  let asmAst := AssemblyAST.fixUp asmAst
  -- Chapter 13: append StaticConstant items for float literals, neg-zero, and
  -- the ULong↔Double threshold constant.
  -- These must be appended AFTER fixUp (StaticConstants have no pseudo operands).
  -- Chapter 13: emit float literal constants in `.rodata` (one per unique float value).
  -- `StaticConstant` now takes `List StaticInit`; each float is a singleton list.
  let floatConstItems : List AssemblyAST.AsmTopLevel :=
    floatConsts.map fun (name, f) =>
      .StaticConstant name 8 [.DoubleInit f]
  let negZeroItems : List AssemblyAST.AsmTopLevel :=
    if needsNegZero then
      -- -0.0 IEEE 754 bit pattern: 0x8000000000000000 = sign bit only
      [.StaticConstant ".Lneg_zero" 16 [.LongInit (-9223372036854775808)]]
    else []
  -- Always emit the ULong threshold (2^63 = 0x43E0000000000000 as IEEE 754 double bits).
  -- CodeGen references .Lulong_thresh whenever DoubleToULong or ULongToDouble appears.
  -- Emitting unconditionally is safe: unused rodata is harmless.
  let threshItems : List AssemblyAST.AsmTopLevel :=
    [.StaticConstant ".Lulong_thresh" 8 [.ULongInit 4890909195324358656]]
  -- Chapter 16: emit StaticConstant items for string literals.
  -- Each string constant is a null-terminated char array in .rodata (alignment 1).
  -- The label (e.g. `.Lstr.5`) was allocated by TackyGen.internString.
  let strConstItems : List AssemblyAST.AsmTopLevel :=
    strConsts.map fun (name, s) =>
      .StaticConstant name 1 [.StringInit s true]
  let asmAst : AssemblyAST.Program :=
    { topLevels := asmAst.topLevels ++ floatConstItems ++ negZeroItems ++ threshItems ++ strConstItems }
  if stage == .Codegen then return none
  -- Emit assembly
  let assemblyPath := changeExtension preprocessedPath ".s"
  IO.FS.writeFile assemblyPath (Emission.emitProgram asmAst)
  return some assemblyPath

def assemble (assemblyPath : String) (outputPath : String)
    (extraLinkerFlags : List String := []) : IO Unit := do
  -- Pass any extra linker flags (e.g. -lm) after the output flag so GCC sees them.
  let extraArr := extraLinkerFlags.toArray
  try
    runCmd "gcc" (#[assemblyPath, "-o", outputPath] ++ extraArr) "Assembly/linking failed"
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

def run (inputPath : String) (stage : Stage)
    (extraLinkerFlags : List String := [])
    (optFlags : Tacky.OptFlags := {}) : IO Unit := do
  let preprocessed ← preprocess inputPath
  let assemblyOpt ←
    try
      let asm ← compile preprocessed stage optFlags
      try IO.FS.removeFile preprocessed catch _ => pure ()
      pure asm
    catch e =>
      try IO.FS.removeFile preprocessed catch _ => pure ()
      throw e
  match stage, assemblyOpt with
  | .Full, some assemblyPath =>
    assemble assemblyPath (dropExtension inputPath) extraLinkerFlags
  | .ObjectFile, some assemblyPath =>
    assembleToObject assemblyPath (changeExtension inputPath ".o")
  | _, _ =>
    pure ()

end Driver
