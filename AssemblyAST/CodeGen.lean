import Tacky.Tacky
import AssemblyAST.AssemblyAST
import Semantics.SymbolTable

/-
  Pass 1 of assembly generation: converts Tacky.Program → AssemblyAST.Program.

  Chapter 13 additions:
    - `valAsmType` returns `Double` for XMM-resident temporaries.
    - `emitParamCopies` counts integer and float parameters separately, using
      integer registers (DI/SI/DX/CX/R8/R9) for integer args and XMM0-XMM7
      for double args, per the System V AMD64 ABI.
    - `convertFunCall` likewise places double args in XMM regs and integer args
      in integer regs; retrieves the return value from XMM0 for double functions.
    - `convertInstruction` handles:
        IntToDouble / DoubleToInt  → Cvtsi2sd(Longword) / Cvttsd2si(Longword)
        UIntToDouble               → MovZeroExtend to 64-bit then Cvtsi2sd(Quadword)
        DoubleToUInt               → Cvttsd2si(Quadword) then truncate
        ULongToDouble              → two-step via testq/jns/shrq/orq/cvtsi2sdq/addsd
        DoubleToULong              → two-step via comisd/threshold/subsd/cvttsd2siq/xorq
        Double Unary .Negate       → Movsd to dst, Movsd neg-zero to XMM15, Xorpd
        Double relational ops      → Comisd + A/AE/B/BE/E/NE condition codes
        Double arithmetic          → Binary Double Add/Sub/Mult/DivDouble
        Return(double)             → Mov Double src XMM0
    - `StaticVariable` now carries `AST.Const` init; `convertStaticVar` handles
      `ConstDouble` → `StaticVariable` with `DoubleInit`.

  Chapter 12 additions:
    - `ZeroExtend` → `MovZeroExtend`.
    - Unsigned division uses `Div` (not `Idiv`) with DX zeroed.
    - Signed shift right uses `Sar`; unsigned uses `Shr`.
    - Relational ops use A/AE/B/BE condition codes for unsigned operands.

  System V AMD64 calling convention:
    - Integer args: %rdi, %rsi, %rdx, %rcx, %r8, %r9 (first 6; rest on stack)
    - Float args:   %xmm0..%xmm7 (first 8; rest on stack)
    - Counted SEPARATELY.  A call `f(int a, double b, int c)` passes:
        a → %rdi, b → %xmm0, c → %rsi.
    - Integer return: %rax; Double return: %xmm0.
-/

namespace AssemblyAST

/-- The six System V AMD64 integer argument registers in order. -/
private def intArgRegs : List Reg := [.DI, .SI, .DX, .CX, .R8, .R9]

/-- The eight System V AMD64 float/double argument registers in order. -/
private def xmmArgRegs : Array Reg := #[.XMM0, .XMM1, .XMM2, .XMM3, .XMM4, .XMM5, .XMM6, .XMM7]

private def convertUnop : Tacky.UnaryOp → UnaryOp
  | .Complement => .Not
  | .Negate     => .Neg
  | .Not        => .Not  -- unreachable: .Not is expanded separately

private def convertBinop : Tacky.BinaryOp → BinaryOp
  | .Add        => .Add
  | .Subtract   => .Sub
  | .Multiply   => .Mult
  | .BitAnd     => .And
  | .BitOr      => .Or
  | .BitXor     => .Xor
  | _           => .Add  -- Divide/Remainder/Shift/relational handled separately

/-- Condition codes for signed comparisons. -/
private def relCondCodeSigned : Tacky.BinaryOp → Option CondCode
  | .Equal          => some .E
  | .NotEqual       => some .NE
  | .LessThan       => some .L
  | .LessOrEqual    => some .LE
  | .GreaterThan    => some .G
  | .GreaterOrEqual => some .GE
  | _               => none

/-- Condition codes for unsigned comparisons (Chapter 12). -/
private def relCondCodeUnsigned : Tacky.BinaryOp → Option CondCode
  | .Equal          => some .E
  | .NotEqual       => some .NE
  | .LessThan       => some .B
  | .LessOrEqual    => some .BE
  | .GreaterThan    => some .A
  | .GreaterOrEqual => some .AE
  | _               => none

/-- Condition codes for double comparisons (Chapter 13).
    `comisd` sets CF, ZF, and PF; for NaN both CF=ZF=PF=1.

    IEEE 754 semantics:
      GT: CF=0 AND ZF=0 → .A  (NaN: CF=1 → A=false ✓)
      GE: CF=0          → .AE (NaN: CF=1 → AE=false ✓)
      LT: swap operands, then CF=0 AND ZF=0 → .A  (NaN: A=false ✓)
      LE: swap operands, then CF=0          → .AE (NaN: AE=false ✓)
      EQ and NE require a two-instruction sequence with the parity flag;
      they are not representable as a single CondCode. -/
private def relCondCodeDouble : Tacky.BinaryOp → Option CondCode
  | .GreaterThan    => some .A    -- above (CF=0, ZF=0); NaN→CF=1→false ✓
  | .GreaterOrEqual => some .AE   -- above or equal (CF=0); NaN→CF=1→false ✓
  | _               => none       -- all others need special handling

-- ---------------------------------------------------------------------------
-- Chapter 18: Struct/union calling convention helpers (System V AMD64 ABI)
-- ---------------------------------------------------------------------------

/-- Classification of a single "eightbyte" chunk of a struct/union argument or return.
    INTEGER: at least one non-double field → passed in a general-purpose register.
    SSE:     all fields are double → passed in an XMM register.
    MEMORY:  struct too large or misaligned → passed/returned on the stack. -/
private inductive EightbyteClass where
  | INTEGER : EightbyteClass
  | SSE     : EightbyteClass
  | MEMORY  : EightbyteClass
  deriving BEq

/-- Collect all leaf (non-struct) fields of a type with their byte offsets.
    Recursively expands struct members using the TypeTable.
    Returns a list of (globalByteOffset, leafType) pairs. -/
private partial def collectLeafFields (tt : Semantics.TypeTable) : AST.Typ → Nat → List (Nat × AST.Typ)
  | .Struct tag, baseOff =>
      match Semantics.lookupTypeTable tt tag with
      | none    => [(baseOff, .Struct tag)]   -- unknown tag: treat as single chunk
      | some sd =>
          sd.members.foldl (fun acc m =>
            acc ++ collectLeafFields tt m.typ (baseOff + m.offset)) []
  | .Union tag, baseOff =>
      match Semantics.lookupTypeTable tt tag with
      | none    => [(baseOff, .Union tag)]
      | some sd =>
          -- For unions, all members have offset 0; we just classify the first member
          -- (since all members overlap, the union is INTEGER unless ALL members are Double).
          sd.members.foldl (fun acc m =>
            acc ++ collectLeafFields tt m.typ baseOff) []
  | .Array elem n, baseOff =>
      (List.range n).foldl (fun acc i =>
        acc ++ collectLeafFields tt elem (baseOff + i * elem.sizeOf)) []
  | t, baseOff => [(baseOff, t)]

/-- Classify a single eightbyte chunk (fields at offsets `[lo, hi)` bytes).
    If all fields in the chunk are Double → SSE; otherwise → INTEGER. -/
private def classifyChunk (fields : List (Nat × AST.Typ)) (lo hi : Nat) : EightbyteClass :=
  let chunkFields := fields.filter fun (off, _) => off >= lo && off < hi
  if chunkFields.isEmpty then .INTEGER  -- no fields: treat as integer padding
  else if chunkFields.all (fun (_, t) => t == .Double) then .SSE
  else .INTEGER

/-- Classify a struct/union type for the System V AMD64 calling convention.
    Returns a list of eightbyte classes, one per 8-byte chunk of the struct.
    MEMORY is returned as a single-element list [MEMORY] for oversized structs. -/
private def classifyForABI (tt : Semantics.TypeTable) (typ : AST.Typ) (size : Nat)
    : List EightbyteClass :=
  -- Structs > 16 bytes always go to MEMORY (passed on the stack).
  if size > 16 then [.MEMORY]
  else
    let fields := collectLeafFields tt typ 0
    let c0 := classifyChunk fields 0 8
    if size <= 8 then [c0]
    else [c0, classifyChunk fields 8 16]

/-- Get the struct/union size from the TypeTable. Returns 0 if not found. -/
private def getTagSize (tt : Semantics.TypeTable) (tag : String) : Nat :=
  match Semantics.lookupTypeTable tt tag with
  | some sd => sd.size
  | none    => 0

/-- Get the struct/union alignment from the TypeTable. Returns 1 if not found. -/
private def getTagAlign (tt : Semantics.TypeTable) (tag : String) : Nat :=
  match Semantics.lookupTypeTable tt tag with
  | some sd => sd.alignment
  | none    => 1

private def convertVal : Tacky.Val → Operand
  | .Constant n => .Imm n
  | .Var id     => .Pseudo id

-- ---------------------------------------------------------------------------
-- Chapter 18: Partial-eightbyte safe load helper
-- ---------------------------------------------------------------------------

/-- Generate instructions to load exactly `rem` bytes (1–7) from a struct's
    last partial eightbyte, starting at byte offset `baseOff` within the named
    stack variable `varName`, into scratch register R10.  The high bytes of R10
    are zeroed.

    Motivation: for structs whose size is not a multiple of 8, the last eightbyte
    is only `rem` bytes wide.  A simple `movq [varName+baseOff]` would read 8
    bytes and potentially cross a page boundary (SIGSEGV).  Instead we load each
    byte individually (zero-extending to 64 bits), shift it into position, and OR
    it into the accumulator.

    Instruction sequence (one per byte, i ∈ [0, rem)):
      MovZeroExtend Byte Quadword [varName+(baseOff+i)] R11   -- R11 = byte[i] (zero-ext)
      Binary Quadword Sal (Imm i*8) R11                       -- R11 <<= i*8 (not for i=0)
      Binary Quadword Or R11 R10                              -- R10 |= R11

    Precondition: `rem ∈ {1..7}`.  Does nothing useful for `rem = 0`. -/
private def loadPartialEightbyte (varName : String) (baseOff : Int) (rem : Nat)
    : List Instruction :=
  [.Mov .Quadword (.Imm 0) (.Reg .R10)] ++
  (List.range rem).flatMap fun (i : Nat) =>
    let byteOff : Int := baseOff + (i : Int)
    let loadByte : Instruction :=
      .MovZeroExtend .Byte .Quadword (.PseudoMem varName byteOff) (.Reg .R11)
    let shiftLeft : List Instruction :=
      if i == 0 then []
      else [.Binary .Quadword .Sal (.Imm ((i * 8 : Nat) : Int)) (.Reg .R11)]
    let orIn : Instruction :=
      .Binary .Quadword .Or (.Reg .R11) (.Reg .R10)
    [loadByte] ++ shiftLeft ++ [orIn]

-- ---------------------------------------------------------------------------
-- Chapter 18: Type-map helpers for struct/union ABI classification
-- ---------------------------------------------------------------------------

/-- Look up the AST.Typ for a variable name from the combined type map.
    `typMap` merges the frontend SymbolTable (Obj entries, after VarResolution
    renaming) and the TackyGen `typeEnv` (generated temporaries).  Together
    they cover every TACKY variable name that may appear in struct contexts. -/
private def lookupAstTyp (typMap : List (String × AST.Typ)) (name : String) : Option AST.Typ :=
  match typMap.find? (fun p => p.1 == name) with
  | some (_, t) => some t
  | none        => none

/-- Extract the struct or union tag from a named variable's AST.Typ.
    Returns `none` for all non-struct / non-union types (scalars, arrays, etc.). -/
private def varStructTag (typMap : List (String × AST.Typ)) (name : String) : Option String :=
  match lookupAstTyp typMap name with
  | some (.Struct tag) | some (.Union tag) => some tag
  | _                                       => none

/-- Classify a Tacky.Val for the System V AMD64 ABI.
    Returns `none` if the value is not a struct/union.
    Returns `some classes` where each element classifies one 8-byte chunk:
      [.MEMORY] for oversized structs (> 16 bytes),
      [c0] or [c0, c1] for register-passable structs. -/
private def valABIClasses (tt : Semantics.TypeTable) (typMap : List (String × AST.Typ))
    (bst : BackendSymTable) (v : Tacky.Val) : Option (List EightbyteClass) :=
  match v with
  | .Var name =>
      match lookupBst bst name with
      | some (.ObjEntry (.ByteArray size _) _ _) =>
          -- Struct/union: classify using the TypeTable (if tag known) or INTEGER fallback
          let classes := match varStructTag typMap name with
            | some tag => classifyForABI tt (.Struct tag) size
            | none     =>
                -- Tag not found in typMap (shouldn't happen for well-typed programs).
                -- Fall back: size > 16 → MEMORY; else treat all eightbytes as INTEGER.
                if size > 16 then [.MEMORY]
                else List.replicate ((size + 7) / 8) .INTEGER
          some classes
      | _ => none
  | .Constant _ => none

/-- Look up the `AsmType` of a TACKY value from the backend symbol table. -/
private def valAsmType (bst : BackendSymTable) : Tacky.Val → AsmType
  | .Var id     => match lookupBst bst id with
                   | some (.ObjEntry t _ _) => t
                   | _                      => .Longword
  | .Constant n =>
      if n > 4294967295 || n < -2147483648 then .Quadword else .Longword

/-- True if the value has `Double` AsmType. -/
private def isDouble (bst : BackendSymTable) (v : Tacky.Val) : Bool :=
  valAsmType bst v == .Double

/-- Determine whether a TACKY value has a signed type (from the backend sym table).
    Constants are assumed signed; Double is neither signed nor unsigned. -/
private def valIsSigned (bst : BackendSymTable) : Tacky.Val → Bool
  | .Var id     => match lookupBst bst id with
                   | some (.ObjEntry _ isSigned _) => isSigned
                   | _                              => true
  | .Constant _ => true

/-- Determine the AsmType for a binary instruction from its operands.
    Prefers the type of Var operands over constants; looks at dst first. -/
private def instrAsmType (bst : BackendSymTable) (src dst : Tacky.Val) : AsmType :=
  match dst with
  | .Var id => match lookupBst bst id with
               | some (.ObjEntry t _ _) => t
               | _ => valAsmType bst src
  | .Constant _ => valAsmType bst src

/-- Determine the signedness for a binary instruction from its operands. -/
private def instrIsSigned (bst : BackendSymTable) (src dst : Tacky.Val) : Bool :=
  match dst with
  | .Var id => match lookupBst bst id with
               | some (.ObjEntry _ isSigned _) => isSigned
               | _ => valIsSigned bst src
  | .Constant _ => valIsSigned bst src

/-- Determine the AsmType for a comparison/relational instruction. -/
private def cmpAsmType (bst : BackendSymTable) (src1 src2 : Tacky.Val) : AsmType :=
  match src1, src2 with
  | .Var _, _  => valAsmType bst src1
  | _, .Var _  => valAsmType bst src2
  | _, _       =>
      if valAsmType bst src1 == .Quadword || valAsmType bst src2 == .Quadword
      then .Quadword else .Longword

private def cmpIsSigned (bst : BackendSymTable) (src1 src2 : Tacky.Val) : Bool :=
  match src1, src2 with
  | .Var _, _  => valIsSigned bst src1
  | _, .Var _  => valIsSigned bst src2
  | _, _       => valIsSigned bst src1

/-- Emit parameter-copy instructions at function entry.
    Chapter 13: counts integer and double parameters separately, using
    separate register banks per the System V AMD64 ABI.
    Chapter 18: struct/union parameters classified per ABI:
      - MEMORY class (> 16 bytes): struct bytes sit in consecutive 8-byte stack
        slots; copy each slot to the local variable's PseudoMem offsets.
      - Register class (≤ 16 bytes): each eightbyte goes to the next available
        integer or XMM register (spills to stack if registers exhausted).
    `startIntIdx`: 0 for normal functions; 1 for MEMORY-returning functions
    (because RDI is consumed by the hidden return-value pointer in that case). -/
private def emitParamCopies (params : List String) (bst : BackendSymTable)
    (tt : Semantics.TypeTable) (typMap : List (String × AST.Typ))
    (startIntIdx : Nat) : List Instruction :=
  let rec go (ps : List String) (intIdx floatIdx stackIdx : Nat) (acc : List Instruction)
      : List Instruction :=
    match ps with
    | [] => acc
    | p :: rest =>
        let asmT : AsmType := match lookupBst bst p with
          | some (.ObjEntry t _ _) => t
          | _                      => .Longword
        match asmT with
        | .ByteArray size _ =>
            -- Chapter 18: struct/union parameter — classify eightbytes for ABI
            let classes : List EightbyteClass :=
              match varStructTag typMap p with
              | some tag => classifyForABI tt (.Struct tag) size
              | none     =>
                  -- No struct tag found: fall back to INTEGER for all eightbytes.
                  if size > 16 then [.MEMORY]
                  else List.replicate ((size + 7) / 8) .INTEGER
            match classes with
            | [.MEMORY] =>
                -- MEMORY class: struct was pushed on the caller's stack.
                -- Each 8-byte chunk occupies one stack slot at increasing offsets.
                -- Copy each slot into the corresponding PseudoMem offset of the local var.
                let nChunks := (size + 7) / 8
                let copyInstrs := (List.range nChunks).map fun i =>
                  let stackOff : Int := ((stackIdx + i + 2) * 8 : Nat)
                  let elemOff  : Int := (i * 8 : Nat)
                  -- FixUp will split this mem-to-mem copy via R10.
                  .Mov .Quadword (.Memory .BP stackOff) (.PseudoMem p elemOff)
                go rest intIdx floatIdx (stackIdx + nChunks) (acc ++ copyInstrs)
            | _ =>
                -- Register class: ABI "all or nothing" rule — if there aren't enough
                -- registers for ALL eightbytes of this struct, pass the ENTIRE struct
                -- on the stack (do NOT split some eightbytes into regs and others onto stack).
                let intNeeded := classes.foldl (fun n c => if c == .INTEGER then n + 1 else n) 0
                let sseNeeded := classes.foldl (fun n c => if c == .SSE    then n + 1 else n) 0
                let intAvail  := 6 - intIdx
                let sseAvail  := 8 - floatIdx
                let allFitInRegs := intNeeded ≤ intAvail && sseNeeded ≤ sseAvail
                if !allFitInRegs then
                  -- Not enough registers: treat the entire struct as MEMORY-class.
                  -- Each 8-byte chunk occupies one stack slot; copy each into PseudoMem.
                  let nChunks := (size + 7) / 8
                  let copyInstrs := (List.range nChunks).map fun i =>
                    let stackOff : Int := ((stackIdx + i + 2) * 8 : Nat)
                    let elemOff  : Int := (i * 8 : Nat)
                    -- FixUp will split this mem-to-mem copy via R10.
                    .Mov .Quadword (.Memory .BP stackOff) (.PseudoMem p elemOff)
                  go rest intIdx floatIdx (stackIdx + nChunks) (acc ++ copyInstrs)
                else
                  -- All eightbytes fit in registers: assign each to the next int/XMM reg.
                  -- Use foldl with index tracked in the accumulator (Lean 4 has no List.enum).
                  let (copyInstrs, newIntIdx, newFloatIdx, newStackIdx, _) :=
                    classes.foldl
                      (fun (st : List Instruction × Nat × Nat × Nat × Nat) cls =>
                        let (instrs, iIdx, fIdx, sIdx, i) := st
                        let elemOff : Int := (i * 8 : Nat)
                        match cls with
                        | .INTEGER =>
                            let reg := intArgRegs.getD iIdx .DI
                            (instrs ++ [.Mov .Quadword (.Reg reg) (.PseudoMem p elemOff)],
                             iIdx + 1, fIdx, sIdx, i + 1)
                        | .SSE =>
                            let reg := xmmArgRegs.getD fIdx .XMM0
                            (instrs ++ [.Movsd (.Reg reg) (.PseudoMem p elemOff)],
                             iIdx, fIdx + 1, sIdx, i + 1)
                        | .MEMORY =>
                            -- Shouldn't appear in the register-class branch
                            (instrs, iIdx, fIdx, sIdx, i + 1))
                      ([], intIdx, floatIdx, stackIdx, 0)
                  go rest newIntIdx newFloatIdx newStackIdx (acc ++ copyInstrs)
        | .Double =>
            -- Scalar double parameter: use XMM register if available, else stack
            if floatIdx < 8 then
              let reg := xmmArgRegs.getD floatIdx .XMM0
              go rest intIdx (floatIdx + 1) stackIdx
                (acc ++ [.Movsd (.Reg reg) (.Pseudo p)])
            else
              let stackOff : Int := ((stackIdx + 2) * 8 : Nat)
              go rest intIdx floatIdx (stackIdx + 1)
                (acc ++ [.Movsd (.Memory .BP stackOff) (.Pseudo p)])
        | _ =>
            -- Integer/pointer/byte parameter: use integer register if available, else stack
            if intIdx < 6 then
              let reg := intArgRegs.getD intIdx .DI
              go rest (intIdx + 1) floatIdx stackIdx
                (acc ++ [.Mov asmT (.Reg reg) (.Pseudo p)])
            else
              let stackOff : Int := ((stackIdx + 2) * 8 : Nat)
              go rest intIdx floatIdx (stackIdx + 1)
                (acc ++ [.Mov asmT (.Memory .BP stackOff) (.Pseudo p)])
  go params startIntIdx 0 0 []

/-- Generate assembly for a TACKY FunCall instruction.
    Chapter 13: classifies each argument as integer or double, placing
    arguments into the appropriate register bank or the stack.
    Chapter 17: `dst` is now `Option Tacky.Val` — void calls have `none` and
    skip emitting the return-value move.
    Chapter 18: struct/union arguments classified per ABI.
      - MEMORY-class struct: push all 8-byte chunks onto the stack (high offset first,
        so chunk 0 ends up at the lowest stack address for the callee).
      - Register-class struct: each eightbyte goes to the next available int/XMM register.
    For MEMORY-class RETURN values: the callee expects a hidden pointer in RDI pointing
    to the caller's output buffer; we emit `leaq PseudoMem(dst, 0), %rdi` before
    the other integer register moves. -/
private def convertFunCall (name : String) (args : List Tacky.Val) (dst : Option Tacky.Val)
    (bst : BackendSymTable) (labelCounter : Nat)
    (tt : Semantics.TypeTable) (typMap : List (String × AST.Typ))
    : List Instruction × Nat :=
  -- Look up the callee's return AsmType
  let retAsmType : AsmType := match lookupBst bst name with
    | some (.FunEntry _ rt) => rt
    | _                     => .Longword
  -- Check whether the return value is a MEMORY-class struct (size > 16 bytes).
  -- If so, we must pass the address of the output buffer as a hidden first argument
  -- in RDI, and all other integer arguments start from RSI (intIdx = 1).
  let isMemReturn : Bool :=
    match retAsmType with
    | .ByteArray size _ => size > 16
    | _                 => false
  -- Starting integer register index: skip DI if it carries the hidden return pointer
  let initIntIdx := if isMemReturn then 1 else 0
  -- Hidden return-value pointer instruction (emitted before other int-reg moves)
  let hiddenPtrInstrs : List Instruction :=
    if isMemReturn then
      match dst with
      | some (.Var n) =>
          -- leaq PseudoMem(n, 0), %rdi — pass address of the local buffer as hidden arg
          [.Lea (.PseudoMem n 0) (.Reg .DI)]
      | _ => []
    else []
  -- Classify all arg eightbytes into three groups (in argument order):
  --   intRegItems : (Operand × AsmType × regIdx)  — move to integer register
  --   xmmRegItems : (Operand × regIdx)             — movsd to XMM register
  --   stackItems  : (Operand × isDouble)           — push to stack
  -- For structs we split into per-eightbyte PseudoMem operands before classifying.
  -- Classify all arg eightbytes into three groups, building instruction lists directly:
  --   intRegInstrs : List Instruction  — moves to integer arg registers (emitted before call)
  --   xmmRegInstrs : List Instruction  — movsd to XMM arg registers (emitted before call)
  --   stackSlots   : List (List Instruction)  — per-slot push sequences (reversed then emitted)
  --
  -- For partial struct eightbytes (struct size not a multiple of 8), we use
  -- loadPartialEightbyte to build the correct value in R10 byte-by-byte, avoiding
  -- any read past the struct boundary (which could SIGSEGV on a page boundary).
  -- The overlapping-movq approach is ONLY safe for WRITES (idempotent destination
  -- overlap); for READS into registers/stack it puts bytes at wrong positions.
  let initialAcc :=
    (([] : List Instruction),
     ([] : List Instruction),
     ([] : List (List Instruction)),
     initIntIdx, 0)
  let (intRegInstrs, xmmRegInstrs, stackSlots, _, _) :=
    args.foldl
      (fun acc arg =>
        let (ia, xa, sa, iIdx, xIdx) := acc
        let t := valAsmType bst arg
        match t with
        | .ByteArray size _ =>
            -- Chapter 18: struct/union argument — classify per ABI
            let varName : String := match arg with | .Var n => n | .Constant _ => ""
            let classes := match varStructTag typMap varName with
              | some tag => classifyForABI tt (.Struct tag) size
              | none     =>
                  if size > 16 then [.MEMORY]
                  else List.replicate ((size + 7) / 8) .INTEGER
            let nChunks := (size + 7) / 8
            let rem := size % 8
            match classes with
            | [.MEMORY] =>
                -- MEMORY class: push all 8-byte chunks to the stack.
                -- Chunks are added in order [0..nChunks-1]; the reverse-push loop
                -- will push chunk(last) first, so chunk(0) ends at the lowest address.
                -- For the last partial chunk (rem != 0), safely load `rem` bytes using
                -- loadPartialEightbyte (avoids reading past struct end at page boundary).
                let chunkSlots := (List.range nChunks).map fun i =>
                  if i == nChunks - 1 && rem != 0 then
                    -- Partial chunk: load byte-by-byte into R10, then push R10
                    let baseOff : Int := (nChunks - 1) * 8
                    loadPartialEightbyte varName baseOff rem ++
                    [.Push (.Reg .R10)]
                  else
                    -- Full 8-byte chunk: movq [var+off] → R10 → pushq R10
                    let off : Int := (i * 8 : Nat)
                    [.Mov .Quadword (.PseudoMem varName off) (.Reg .R10),
                     .Push (.Reg .R10)]
                (ia, xa, sa ++ chunkSlots, iIdx, xIdx)
            | _ =>
                -- Register class: check if ALL eightbytes fit in remaining registers.
                -- SysV ABI §3.2.3: "When two or more registers are needed, and only one
                -- is available, or no registers are available, the argument is passed
                -- in memory." This means we cannot split a struct across registers and
                -- stack — it must go entirely to registers or entirely to the stack.
                let intNeeded := classes.foldl (fun n c => if c == .INTEGER then n + 1 else n) 0
                let sseNeeded := classes.foldl (fun n c => if c == .SSE then n + 1 else n) 0
                let intAvail := 6 - iIdx
                let sseAvail := 8 - xIdx
                let allFitInRegs := intNeeded ≤ intAvail && sseNeeded ≤ sseAvail
                if !allFitInRegs then
                  -- Not enough registers for all eightbytes → entire struct goes to stack.
                  -- Push all chunks in order [0..nChunks-1] (reversed for right-to-left push).
                  let chunkSlots := (List.range nChunks).map fun i =>
                    if i == nChunks - 1 && rem != 0 then
                      let baseOff : Int := ((nChunks - 1) * 8 : Nat)
                      loadPartialEightbyte varName baseOff rem ++ [.Push (.Reg .R10)]
                    else
                      let off : Int := (i * 8 : Nat)
                      [.Mov .Quadword (.PseudoMem varName off) (.Reg .R10), .Push (.Reg .R10)]
                  (ia, xa, sa ++ chunkSlots, iIdx, xIdx)
                else
                  -- All eightbytes fit in registers: pass each one in its register.
                  -- For the last partial eightbyte, use loadPartialEightbyte to safely
                  -- read exactly `rem` bytes without crossing a page boundary.
                  let (ia2, xa2, sa2, iIdx2, xIdx2, _) :=
                    classes.foldl
                      (fun acc2 cls =>
                        let (ia', xa', sa', iIdx', xIdx', i) := acc2
                        let isPartial := i == nChunks - 1 && rem != 0
                        let fullOff : Int := (i * 8 : Nat)
                        let baseOff : Int := ((nChunks - 1) * 8 : Nat)
                        match cls with
                        | .INTEGER =>
                            let reg := intArgRegs.getD iIdx' .DI
                            let loadInstrs : List Instruction :=
                              if isPartial then
                                loadPartialEightbyte varName baseOff rem ++
                                [.Mov .Quadword (.Reg .R10) (.Reg reg)]
                              else
                                [.Mov .Quadword (.PseudoMem varName fullOff) (.Reg reg)]
                            (ia' ++ loadInstrs, xa', sa', iIdx' + 1, xIdx', i + 1)
                        | .SSE =>
                            -- SSE eightbytes are full doubles; no partial issue.
                            let reg := xmmArgRegs.getD xIdx' .XMM0
                            (ia', xa' ++ [.Movsd (.PseudoMem varName fullOff) (.Reg reg)],
                             sa', iIdx', xIdx' + 1, i + 1)
                        | .MEMORY => (ia', xa', sa', iIdx', xIdx', i + 1))
                      (ia, xa, sa, iIdx, xIdx, 0)
                  (ia2, xa2, sa2, iIdx2, xIdx2)
        | .Double =>
            -- Scalar double: XMM register if available, else stack
            if xIdx < 8 then
              let reg := xmmArgRegs.getD xIdx .XMM0
              (ia, xa ++ [.Movsd (convertVal arg) (.Reg reg)], sa, iIdx, xIdx + 1)
            else
              let pushSlot : List Instruction :=
                [.Mov .Quadword (convertVal arg) (.Reg .R10), .Push (.Reg .R10)]
              (ia, xa, sa ++ [pushSlot], iIdx, xIdx)
        | _ =>
            -- Scalar integer/pointer/byte: integer register if available, else stack
            if iIdx < 6 then
              let reg := intArgRegs.getD iIdx .DI
              (ia ++ [.Mov t (convertVal arg) (.Reg reg)], xa, sa, iIdx + 1, xIdx)
            else
              let pushSlot : List Instruction :=
                match convertVal arg with
                | .Reg r => [.Push (.Reg r)]
                | .Imm n => [.Push (.Imm n)]
                | op     =>
                    -- Use the correct-width read to avoid reading past the value's end
                    -- at page boundaries (e.g. an int near the end of a BSS page).
                    -- Byte: movzbl reads 1 byte and zero-extends to 32 bits (safe).
                    -- Longword: movl reads 4 bytes and zero-extends to 64 bits via %eax.
                    -- Quadword/Pointer: movq reads 8 bytes (always safe for 8-byte types).
                    let loadInstr : Instruction :=
                      if t == .Byte then .MovZeroExtend .Byte .Longword op (.Reg .AX)
                      else .Mov t op (.Reg .AX)
                    [loadInstr, .Push (.Reg .AX)]
              (ia, xa, sa ++ [pushSlot], iIdx, xIdx))
      initialAcc
  -- Stack padding: an odd number of 8-byte pushes leaves RSP misaligned (16-byte boundary).
  let stackPad : Int := if stackSlots.length % 2 == 1 then 8 else 0
  let padInstrs : List Instruction :=
    if stackPad != 0 then [.Binary .Quadword .Sub (.Imm stackPad) (.Reg .SP)] else []
  -- Push stack subargs in reverse order (right-to-left per the ABI).
  -- stackSlots was built in argument order; reversing gives last-to-first push order
  -- so that slot[0] ends up at the lowest stack address.
  let pushInstrs : List Instruction :=
    stackSlots.reverse.foldl (fun acc slotInstrs => acc ++ slotInstrs) []
  let deallocBytes : Int := stackSlots.length * 8 + stackPad
  let callInstr : List Instruction := [.Call name]
  let deallocInstrs : List Instruction :=
    if deallocBytes != 0 then
      [.Binary .Quadword .Add (.Imm deallocBytes) (.Reg .SP)]
    else []
  -- Retrieve the return value.
  -- Chapter 17: for void calls (dst = none), skip the return-value move entirely.
  -- Chapter 18: for struct returns:
  --   MEMORY class: the callee already wrote the result to our buffer; nothing to do.
  --   Register class: copy the eightbytes from AX/DX/XMM0/XMM1 into dst's PseudoMem slots.
  let retInstrs : List Instruction :=
    match dst with
    | none => []   -- void call: no return value to capture
    | some dstVal =>
        if isMemReturn then
          -- MEMORY return: result is already in the buffer we pointed RDI at; no copy needed
          []
        else
          match retAsmType with
          | .ByteArray size _ =>
              -- Register-class struct return: read eightbytes from AX/DX/XMM0/XMM1
              let dstName : String := match dstVal with | .Var n => n | .Constant _ => ""
              let classes := match varStructTag typMap dstName with
                | some tag => classifyForABI tt (.Struct tag) size
                | none     => List.replicate ((size + 7) / 8) .INTEGER
              -- Use foldl with index tracked in the accumulator (Lean 4 has no List.enum).
              let (instrs, _, _, _) := classes.foldl
                (fun (st : List Instruction × Nat × Nat × Nat) cls =>
                  let (is, intI, xmmI, i) := st
                  let off : Int := (i * 8 : Nat)
                  match cls with
                  | .INTEGER =>
                      -- Eightbyte 0 → RAX; eightbyte 1 → RDX
                      let reg := if intI == 0 then Reg.AX else Reg.DX
                      (is ++ [.Mov .Quadword (.Reg reg) (.PseudoMem dstName off)],
                       intI + 1, xmmI, i + 1)
                  | .SSE =>
                      -- Eightbyte 0 → XMM0; eightbyte 1 → XMM1
                      let reg := if xmmI == 0 then Reg.XMM0 else Reg.XMM1
                      (is ++ [.Movsd (.Reg reg) (.PseudoMem dstName off)],
                       intI, xmmI + 1, i + 1)
                  | .MEMORY => (is, intI, xmmI, i + 1))
                ([], 0, 0, 0)
              instrs
          | .Double => [.Movsd (.Reg .XMM0) (convertVal dstVal)]
          | _       => [.Mov retAsmType (.Reg .AX) (convertVal dstVal)]
  (padInstrs ++ hiddenPtrInstrs ++ intRegInstrs ++ xmmRegInstrs ++ pushInstrs ++
   callInstr ++ deallocInstrs ++ retInstrs, labelCounter)

/-- Generate the ULong → Double multi-instruction sequence.
    Uses the two-step trick for values > LONG_MAX:
      movq src, %r10
      testq %r10, %r10
      jns .Lnonneg_N
      movq %r10, %r11
      andl $1, %r11d         ; preserve the lowest bit
      shrq $1, %r10          ; unsigned right-shift
      orq %r11, %r10         ; restore lowest bit (prevents bias)
      cvtsi2sdq %r10, dst
      addsd dst, dst         ; multiply by 2 to correct for shift
      jmp .Ldone_N
    .Lnonneg_N:
      cvtsi2sdq %r10, dst
    .Ldone_N: -/
private def emitULongToDouble (src : Operand) (dst : Operand) (n : Nat)
    : List Instruction :=
  let nonnegLabel := s!".Lulongtod_nonneg.{n}"
  let doneLabel   := s!".Lulongtod_done.{n}"
  [.Mov .Quadword src (.Reg .R10),
   .Cmp .Quadword (.Imm 0) (.Reg .R10),
   .JmpCC .GE nonnegLabel,                   -- jns (GE with testq is "jns")
   -- Value > LONG_MAX: use the shift trick
   .Mov .Quadword (.Reg .R10) (.Reg .R11),
   .Binary .Longword .And (.Imm 1) (.Reg .R11),   -- andl $1, %r11d
   .Binary .Quadword .Shr (.Imm 1) (.Reg .R10),   -- shrq $1, %r10
   .Binary .Quadword .Or (.Reg .R11) (.Reg .R10),  -- orq %r11, %r10
   .Cvtsi2sd .Quadword (.Reg .R10) dst,
   .Binary .Double .Add dst dst,                    -- addsd dst, dst
   .Jmp doneLabel,
   .Label nonnegLabel,
   .Cvtsi2sd .Quadword (.Reg .R10) dst,
   .Label doneLabel]

/-- Generate the Double → ULong multi-instruction sequence.
    Uses a 2^63 threshold constant to handle values ≥ 2^63:
      comisd .Lulong_thresh(%rip), src
      jb .Lbelow_N
      movsd src, %xmm15             ; scratch copy
      subsd .Lulong_thresh(%rip), %xmm15
      cvttsd2siq %xmm15, dst
      movabsq $9223372036854775808, %r11   ; 2^63
      xorq %r11, dst
      jmp .Ldone_N
    .Lbelow_N:
      cvttsd2siq src, dst
    .Ldone_N: -/
private def emitDoubleToULong (src : Operand) (dst : Operand) (n : Nat)
    : List Instruction :=
  let belowLabel := s!".Ldtoull_below.{n}"
  let doneLabel  := s!".Ldtoull_done.{n}"
  let thresh     := Operand.Data ".Lulong_thresh" 0
  [.Comisd thresh src,                               -- comisd thresh, src: sets CF if src < thresh
   .JmpCC .B belowLabel,                             -- jb: CF=1 means src < thresh
   -- Value ≥ 2^63: subtract threshold, convert, add 2^63 back
   .Movsd src (.Reg .XMM15),
   .Binary .Double .Sub thresh (.Reg .XMM15),        -- subsd thresh, %xmm15
   .Cvttsd2si .Quadword (.Reg .XMM15) dst,
   .Mov .Quadword (.Imm (-9223372036854775808)) (.Reg .R11),  -- movabsq $2^63, %r11
   .Binary .Quadword .Xor (.Reg .R11) dst,
   .Jmp doneLabel,
   .Label belowLabel,
   .Cvttsd2si .Quadword src dst,
   .Label doneLabel]

/-- A stateful counter for generating unique label suffixes in ULong conversions. -/
private structure CgState where
  labelCtr : Nat

/-- Expand one TACKY instruction into typed assembly instructions.
    Returns a list of instructions and an updated label counter.
    Chapter 18: `isMemReturn` is true when the enclosing function returns a
    MEMORY-class struct (> 16 bytes), in which case:
      - At function entry (handled by convertFunctionDef): RDI is saved to
        Memory(BP, -8) as the hidden return-value pointer.
      - At Return: the struct is copied chunk-by-chunk to that hidden pointer
        address, then RAX is loaded with the pointer before Ret. -/
private def convertInstruction (instr : Tacky.Instruction) (bst : BackendSymTable)
    (ctr : Nat) (tt : Semantics.TypeTable) (typMap : List (String × AST.Typ))
    (isMemReturn : Bool) : List Instruction × Nat :=
  match instr with
  -- Chapter 17: Return is now Option Val — void functions emit just Ret.
  | .Return none =>
      ([.Ret], ctr)
  | .Return (some v) =>
      let t := valAsmType bst v
      if t == .Double then
        ([.Movsd (convertVal v) (.Reg .XMM0), .Ret], ctr)
      else
        match t with
        | .ByteArray size _ =>
            -- Chapter 18: struct/union return value
            let varName : String := match v with | .Var n => n | .Constant _ => ""
            if isMemReturn then
              -- MEMORY class: copy each 8-byte chunk of the struct to the hidden
              -- return-value buffer whose address is in Memory(BP, -8).
              -- Step 1: load hidden pointer from Memory(BP, -8) into R11.
              -- Step 2: for each chunk, movq PseudoMem(name, off), R10; movq R10, Memory(R11, off).
              -- Step 3: RAX = hidden pointer (callee must return it per ABI).
              -- Compute full and partial chunk counts.
              -- For the last partial chunk (rem != 0), use an overlapping read starting
              -- at (size-8) instead of ((nFull)*8).  All bytes in [size-8 .. size-1]
              -- are valid; this avoids reading past the struct end into an unmapped page.
              let nFull := size / 8
              let rem   := size % 8
              let fullInstrs := (List.range nFull).flatMap fun i =>
                let off : Int := (i * 8 : Nat)
                [.Mov .Quadword (.PseudoMem varName off) (.Reg .R10),
                 .Mov .Quadword (.Reg .R10) (.Memory .R11 off)]
              let tailInstrs : List Instruction :=
                if rem == 0 then []
                else
                  -- size > 16 (MEMORY class), so size - 8 >= 9; always safe to read 8 bytes here.
                  -- Bytes [size-8 .. size-9] overlap with the last full chunk in src but
                  -- will simply overwrite dst with the same values (idempotent).
                  let off : Int := (size : Int) - 8
                  [.Mov .Quadword (.PseudoMem varName off) (.Reg .R10),
                   .Mov .Quadword (.Reg .R10) (.Memory .R11 off)]
              let copyInstrs := fullInstrs ++ tailInstrs
              ([.Mov .Quadword (.Memory .BP (-8 : Int)) (.Reg .R11)] ++  -- load hidden ptr → R11
               copyInstrs ++
               [.Mov .Quadword (.Memory .BP (-8 : Int)) (.Reg .AX),     -- RAX = hidden ptr
                .Ret], ctr)
            else
              -- Register class (≤ 16 bytes): move each eightbyte to AX/DX or XMM0/XMM1
              -- per the ABI classification of the struct.
              let classes := match varStructTag typMap varName with
                | some tag => classifyForABI tt (.Struct tag) size
                | none     => List.replicate ((size + 7) / 8) .INTEGER
              -- Partial-chunk info: if the struct size is not a multiple of 8, the last
              -- eightbyte holds only `rem` bytes.  We must NOT use an overlapping movq
              -- (which reads bytes at wrong register positions); instead use
              -- loadPartialEightbyte to load exactly `rem` bytes into R10, then move R10.
              let nChunks := (size + 7) / 8
              let rem := size % 8
              -- Use foldl with index tracked in the accumulator (Lean 4 has no List.enum).
              let (retInstrs, _, _, _) := classes.foldl
                (fun (st : List Instruction × Nat × Nat × Nat) cls =>
                  let (is, intI, xmmI, i) := st
                  let isPartial := i == nChunks - 1 && rem != 0
                  let fullOff : Int := (i * 8 : Nat)
                  let baseOff : Int := ((nChunks - 1) * 8 : Nat)
                  match cls with
                  | .INTEGER =>
                      let reg := if intI == 0 then Reg.AX else Reg.DX
                      -- For partial last chunk: load byte-by-byte into R10 then move to reg.
                      -- For full chunks: direct movq into the target register.
                      let loadInstrs : List Instruction :=
                        if isPartial then
                          loadPartialEightbyte varName baseOff rem ++
                          [.Mov .Quadword (.Reg .R10) (.Reg reg)]
                        else
                          [.Mov .Quadword (.PseudoMem varName fullOff) (.Reg reg)]
                      (is ++ loadInstrs, intI + 1, xmmI, i + 1)
                  | .SSE =>
                      -- SSE eightbytes are always full doubles; no partial issue.
                      let reg := if xmmI == 0 then Reg.XMM0 else Reg.XMM1
                      (is ++ [.Movsd (.PseudoMem varName fullOff) (.Reg reg)],
                       intI, xmmI + 1, i + 1)
                  | .MEMORY => (is, intI, xmmI, i + 1))
                ([], 0, 0, 0)
              (retInstrs ++ [Instruction.Ret], ctr)
        | _ => ([.Mov t (convertVal v) (.Reg .AX), .Ret], ctr)
  | .SignExtend srcTyp src dst =>
      -- Chapter 16: SignExtend now carries the AST srcTyp so we can correctly determine
      -- the AsmType even for constant sources (where valAsmType always returns Longword).
      -- Convert AST.Typ → AsmType: Char/SChar → Byte; Int/UInt → Longword; Long/ULong → Quadword.
      let srcT := match srcTyp with
        | .Char | .SChar             => AsmType.Byte
        | .Int  | .UInt              => AsmType.Longword
        | _                          => AsmType.Quadword   -- Long, ULong, Pointer
      let dstT := valAsmType bst dst
      ([.Movsx srcT dstT (convertVal src) (convertVal dst)], ctr)
  | .Truncate src dst =>
      -- Chapter 16: dst may be Byte (char); emit Mov with the dst's AsmType.
      let dstT := valAsmType bst dst
      ([.Mov dstT (convertVal src) (convertVal dst)], ctr)
  | .ZeroExtend srcTyp src dst =>
      -- Chapter 16: ZeroExtend now carries the AST srcTyp (same reason as SignExtend).
      -- UChar → Byte; UInt → Longword; ULong/Pointer → Quadword.
      let srcT := match srcTyp with
        | .UChar                     => AsmType.Byte
        | .UInt                      => AsmType.Longword
        | _                          => AsmType.Quadword   -- ULong, Pointer
      let dstT := valAsmType bst dst
      ([.MovZeroExtend srcT dstT (convertVal src) (convertVal dst)], ctr)
  -- Chapter 13: integer ↔ double conversions (extended for Chapter 16 Byte type)
  | .IntToDouble src dst =>
      -- Chapter 16: char/schar src (Byte) must be sign-extended to Longword before cvtsi2sd.
      -- Long src (Quadword): cvtsi2sdq; Int src (Longword): cvtsi2sdl.
      let srcT := valAsmType bst src
      match srcT with
      | .Byte =>
          -- char → double: sign-extend byte to longword via R10, then convert
          ([.Movsx .Byte .Longword (convertVal src) (.Reg .R10),
            .Cvtsi2sd .Longword (.Reg .R10) (convertVal dst)], ctr)
      | .Quadword =>
          ([.Cvtsi2sd .Quadword (convertVal src) (convertVal dst)], ctr)
      | _ =>
          ([.Cvtsi2sd .Longword (convertVal src) (convertVal dst)], ctr)
  | .DoubleToInt src dst =>
      -- Chapter 16: char/schar dst (Byte): convert to Longword in R10, then movb R10→dst.
      let dstT := valAsmType bst dst
      match dstT with
      | .Byte =>
          ([.Cvttsd2si .Longword (convertVal src) (.Reg .R10),
            .Mov .Byte (.Reg .R10) (convertVal dst)], ctr)
      | .Quadword =>
          ([.Cvttsd2si .Quadword (convertVal src) (convertVal dst)], ctr)
      | _ =>
          ([.Cvttsd2si .Longword (convertVal src) (convertVal dst)], ctr)
  | .UIntToDouble src dst =>
      -- Chapter 16: uchar src (Byte): zero-extend byte to Quadword, then cvtsi2sdq.
      -- UInt src (Longword): zero-extend 32→64 bits via R10, then cvtsi2sdq.
      let srcT := valAsmType bst src
      match srcT with
      | .Byte =>
          ([.MovZeroExtend .Byte .Quadword (convertVal src) (.Reg .R10),
            .Cvtsi2sd .Quadword (.Reg .R10) (convertVal dst)], ctr)
      | _ =>
          ([.MovZeroExtend .Longword .Quadword (convertVal src) (.Reg .R10),
            .Cvtsi2sd .Quadword (.Reg .R10) (convertVal dst)], ctr)
  | .DoubleToUInt src dst =>
      -- Chapter 16: uchar dst (Byte): convert double→Quadword in R10, then movb R10→dst.
      -- UInt dst (Longword): convert double→Quadword in R10, truncate to Longword.
      let dstT := valAsmType bst dst
      match dstT with
      | .Byte =>
          ([.Cvttsd2si .Quadword (convertVal src) (.Reg .R10),
            .Mov .Byte (.Reg .R10) (convertVal dst)], ctr)
      | _ =>
          ([.Cvttsd2si .Quadword (convertVal src) (.Reg .R10),
            .Mov .Longword (.Reg .R10) (convertVal dst)], ctr)
  | .ULongToDouble src dst =>
      let instrs := emitULongToDouble (convertVal src) (convertVal dst) ctr
      (instrs, ctr + 1)
  | .DoubleToULong src dst =>
      let instrs := emitDoubleToULong (convertVal src) (convertVal dst) ctr
      (instrs, ctr + 1)
  | .Unary .Not src dst =>
      let srcT := valAsmType bst src
      if srcT == .Double then
        -- Double logical NOT (NaN-safe): result is 1 iff src == 0.0 (and not NaN).
        -- NaN is "truthy" so !NaN = 0.  `sete` alone is wrong: comisd with NaN
        -- sets ZF=1 AND PF=1, so `sete` would return 1.  Fix with setp+subl:
        --   sete dst    : dst = ZF   (1 for ==0 or NaN)
        --   setp R11    : R11 = PF   (1 for NaN)
        --   subl R11, dst : dst -= PF  (removes the NaN false-positive)
        ([.Xorpd (.Reg .XMM15) (.Reg .XMM15),
          .Comisd (.Reg .XMM15) (convertVal src),
          .Mov .Longword (.Imm 0) (.Reg .R11),   -- zero R11 before setp (setp only sets low byte)
          .SetCC .P  (.Reg .R11),
          .Mov .Longword (.Imm 0) (convertVal dst),
          .SetCC .E  (convertVal dst),
          .Binary .Longword .Sub (.Reg .R11) (convertVal dst)], ctr)
      else
        ([.Cmp srcT (.Imm 0) (convertVal src),
          .Mov .Longword (.Imm 0) (convertVal dst),
          .SetCC .E (convertVal dst)], ctr)
  | .Unary .Negate src dst =>
      let t := instrAsmType bst src dst
      if t == .Double then
        -- Double negation: XOR with -0.0 constant
        ([.Movsd (convertVal src) (convertVal dst),
          .Movsd (.Data ".Lneg_zero" 0) (.Reg .XMM15),
          .Xorpd (.Reg .XMM15) (convertVal dst)], ctr)
      else
        ([.Mov t (convertVal src) (convertVal dst),
          .Unary t .Neg (convertVal dst)], ctr)
  | .Unary op src dst =>
      let t := instrAsmType bst src dst
      ([.Mov t (convertVal src) (convertVal dst),
        .Unary t (convertUnop op) (convertVal dst)], ctr)
  | .Binary .Divide src1 src2 dst =>
      let t      := instrAsmType bst src1 dst
      if t == .Double then
        -- Double division: movsd src1, dst; divsd src2, dst
        ([.Movsd (convertVal src1) (convertVal dst),
          .Binary .Double .DivDouble (convertVal src2) (convertVal dst)], ctr)
      else
        let signed := instrIsSigned bst src1 dst
        if signed then
          ([.Mov t (convertVal src1) (.Reg .AX),
            .Cdq t,
            .Idiv t (convertVal src2),
            .Mov t (.Reg .AX) (convertVal dst)], ctr)
        else
          ([.Mov t (convertVal src1) (.Reg .AX),
            .Mov t (.Imm 0) (.Reg .DX),
            .Div t (convertVal src2),
            .Mov t (.Reg .AX) (convertVal dst)], ctr)
  | .Binary .Remainder src1 src2 dst =>
      let t      := instrAsmType bst src1 dst
      let signed := instrIsSigned bst src1 dst
      if signed then
        ([.Mov t (convertVal src1) (.Reg .AX),
          .Cdq t,
          .Idiv t (convertVal src2),
          .Mov t (.Reg .DX) (convertVal dst)], ctr)
      else
        ([.Mov t (convertVal src1) (.Reg .AX),
          .Mov t (.Imm 0) (.Reg .DX),
          .Div t (convertVal src2),
          .Mov t (.Reg .DX) (convertVal dst)], ctr)
  | .Binary .ShiftLeft src1 src2 dst =>
      let t := instrAsmType bst src1 dst
      ([.Mov t (convertVal src1) (convertVal dst),
        .Mov .Longword (convertVal src2) (.Reg .CX),
        .Binary t .Sal (.Reg .CX) (convertVal dst)], ctr)
  | .Binary .ShiftRight src1 src2 dst =>
      let t      := instrAsmType bst src1 dst
      let signed := instrIsSigned bst src1 dst
      let shiftOp := if signed then BinaryOp.Sar else BinaryOp.Shr
      ([.Mov t (convertVal src1) (convertVal dst),
        .Mov .Longword (convertVal src2) (.Reg .CX),
        .Binary t shiftOp (.Reg .CX) (convertVal dst)], ctr)
  | .Binary op src1 src2 dst =>
      -- Use cmpAsmType to detect Double: for relational ops, dst is always Int,
      -- so instrAsmType (which looks at dst) would incorrectly return Longword.
      -- cmpAsmType looks at src1/src2 first, which correctly gives Double.
      let operandT := cmpAsmType bst src1 src2
      if operandT == .Double then
        -- Double arithmetic or comparison
        match op with
        | .GreaterThan | .GreaterOrEqual =>
            -- GT: comisd src2, src1 → seta (CF=0 AND ZF=0); NaN→CF=1→false ✓
            -- GE: comisd src2, src1 → setae (CF=0);         NaN→CF=1→false ✓
            let cc := if op == .GreaterThan then CondCode.A else CondCode.AE
            ([.Comisd (convertVal src2) (convertVal src1),
              .Mov .Longword (.Imm 0) (convertVal dst),
              .SetCC cc (convertVal dst)], ctr)
        | .LessThan | .LessOrEqual =>
            -- LT: swap comisd operands → compare src2 against src1 → seta
            --     (src2 > src1 ↔ src1 < src2); NaN→CF=1→A=false ✓
            -- LE: swap operands → setae (src2 ≥ src1 ↔ src1 ≤ src2); NaN→false ✓
            let cc := if op == .LessThan then CondCode.A else CondCode.AE
            ([.Comisd (convertVal src1) (convertVal src2),  -- swapped!
              .Mov .Longword (.Imm 0) (convertVal dst),
              .SetCC cc (convertVal dst)], ctr)
        | .Equal =>
            -- EQ: ZF=1 AND PF=0 (PF=1 for NaN, so NaN gives wrong sete result).
            -- Fix: sete dst; setp R11; subl R11, dst
            --   NaN:  sete→1, setp→1, sub→0 ✓   (NaN ≠ anything)
            --   ==:   sete→1, setp→0, sub→1 ✓
            --   !=:   sete→0, setp→0, sub→0 ✓
            ([.Comisd (convertVal src2) (convertVal src1),
              .Mov .Longword (.Imm 0) (.Reg .R11),   -- zero R11 before setp (setp only sets low byte)
              .SetCC .P  (.Reg .R11),
              .Mov .Longword (.Imm 0) (convertVal dst),
              .SetCC .E  (convertVal dst),
              .Binary .Longword .Sub (.Reg .R11) (convertVal dst)], ctr)
        | .NotEqual =>
            -- NE: ZF=0 OR PF=1.
            -- Fix: setne dst; setp R11; orl R11, dst
            --   NaN:  setne→0 (ZF=1), setp→1, or→1 ✓   (NaN ≠ everything)
            --   ==:   setne→0, setp→0, or→0 ✓
            --   !=:   setne→1, setp→0, or→1 ✓
            ([.Comisd (convertVal src2) (convertVal src1),
              .Mov .Longword (.Imm 0) (.Reg .R11),   -- zero R11 before setp (setp only sets low byte)
              .SetCC .P  (.Reg .R11),
              .Mov .Longword (.Imm 0) (convertVal dst),
              .SetCC .NE (convertVal dst),
              .Binary .Longword .Or (.Reg .R11) (convertVal dst)], ctr)
        | _ =>
            -- Double arithmetic: movsd src1, dst; addsd/subsd/mulsd src2, dst
            let binop := match op with
              | .Add      => BinaryOp.Add
              | .Subtract => BinaryOp.Sub
              | .Multiply => BinaryOp.Mult
              | _         => BinaryOp.Add   -- shouldn't happen for double
            ([.Movsd (convertVal src1) (convertVal dst),
              .Binary .Double binop (convertVal src2) (convertVal dst)], ctr)
      else
        -- Integer relational or arithmetic
        let isSigned := cmpIsSigned bst src1 src2
        match (if isSigned then relCondCodeSigned op else relCondCodeUnsigned op) with
        | some cc =>
            let cmpT := cmpAsmType bst src1 src2
            ([.Cmp cmpT (convertVal src2) (convertVal src1),
              .Mov .Longword (.Imm 0) (convertVal dst),
              .SetCC cc (convertVal dst)], ctr)
        | none =>
            let asmT := instrAsmType bst src1 dst
            ([.Mov asmT (convertVal src1) (convertVal dst),
              .Binary asmT (convertBinop op) (convertVal src2) (convertVal dst)], ctr)
  | .Copy src dst =>
      let t := instrAsmType bst src dst
      if t == .Double then
        ([.Movsd (convertVal src) (convertVal dst)], ctr)
      else
        -- Chapter 18: struct/union copy — ByteArray type means we must copy chunk-by-chunk.
        -- We copy exactly `totalBytes` bytes using the largest available move widths:
        --   full 8-byte chunks (movq), then a 4-byte chunk (movl) if needed,
        --   then a 2-byte chunk (movw) if needed, then a 1-byte chunk (movb) if needed.
        -- This avoids writing past the struct's declared size, which is critical when
        -- the destination is a static global (no shadow-padding).
        -- Stack-allocated struct slots are given 8-byte-padded shadow space by
        -- PseudoReplace so a movq overwrite is also safe there.
        match t with
        | .ByteArray totalBytes _ =>
            let srcName := match src with | .Var n => n | .Constant _ => "_"
            let dstName := match dst with | .Var n => n | .Constant _ => "_"
            -- Full 8-byte chunks
            let nFull := totalBytes / 8
            let rem   := totalBytes % 8
            let fullInstrs : List Instruction := (List.range nFull).map fun i =>
              let off : Int := (i * 8 : Nat)
              .Mov .Quadword (.PseudoMem srcName off) (.PseudoMem dstName off)
            -- Trailing bytes: use Longword for 4-byte alignment, then Byte for each
            -- remaining byte (avoids adding a Word AsmType for the 2-byte case).
            let baseOff : Int := (nFull * 8 : Nat)
            let tailInstrs : List Instruction :=
              let (instrs, off) :=
                (if rem >= 4 then
                  ([.Mov .Longword (.PseudoMem srcName baseOff) (.PseudoMem dstName baseOff)],
                   baseOff + 4)
                else ([], baseOff))
              -- Copy remaining 0–3 bytes individually
              (List.range (rem % 4)).foldl (fun (st : List Instruction × Int) i =>
                let (is, o) := st
                (is ++ [.Mov .Byte (.PseudoMem srcName o) (.PseudoMem dstName o)], o + 1))
                (instrs, off) |>.1
            (fullInstrs ++ tailInstrs, ctr)
        | _ => ([.Mov t (convertVal src) (convertVal dst)], ctr)
  | .Jump target =>
      ([.Jmp target], ctr)
  | .JumpIfZero cond target =>
      let t := valAsmType bst cond
      if t == .Double then
        -- Double "is zero" check (NaN-safe):
        --   xorpd xmm15, xmm15      ; xmm15 = 0.0
        --   comisd xmm15, src       ; compare src with 0.0
        -- For NaN: ZF=CF=PF=1. A naive `je target` would jump for NaN too,
        -- which is wrong (NaN is "truthy"). We guard with jp:
        --   jp  .Lnan_skip.N        ; PF=1 → NaN → DON'T jump (non-zero)
        --   je  target              ; ZF=1, PF=0 → really zero → jump
        --   .Lnan_skip.N:
        let nanSkip := s!"nan_skip.{ctr}"
        ([.Xorpd (.Reg .XMM15) (.Reg .XMM15),
          .Comisd (.Reg .XMM15) (convertVal cond),
          .JmpCC .P nanSkip,
          .JmpCC .E target,
          .Label nanSkip], ctr + 1)
      else
        ([.Cmp t (.Imm 0) (convertVal cond), .JmpCC .E target], ctr)
  | .JumpIfNotZero cond target =>
      let t := valAsmType bst cond
      if t == .Double then
        -- Double "is non-zero" check (NaN-safe):
        --   xorpd xmm15, xmm15
        --   comisd xmm15, src
        --   jp  target    ; PF=1 → NaN → IS non-zero → jump
        --   jne target    ; ZF=0 → non-zero → jump
        -- (NaN: ZF=1 so jne doesn't trigger, but jp does; correct.)
        ([.Xorpd (.Reg .XMM15) (.Reg .XMM15),
          .Comisd (.Reg .XMM15) (convertVal cond),
          .JmpCC .P target,
          .JmpCC .NE target], ctr)
      else
        ([.Cmp t (.Imm 0) (convertVal cond), .JmpCC .NE target], ctr)
  | .Label name =>
      ([.Label name], ctr)
  | .FunCall name args dst =>
      convertFunCall name args dst bst ctr tt typMap
  -- Chapter 14: pointer operations -----------------------------------------------
  | .GetAddress src dst =>
      -- leaq src, dst: compute address of src (a stack slot) into dst
      ([.Lea (convertVal src) (convertVal dst)], ctr)
  | .Load ptr dst =>
      -- Load from memory address stored in ptr into dst.
      -- Step 1: move the pointer (64-bit address) into R10.
      -- Step 2: load from (%r10) into dst.
      -- Chapter 18: for ByteArray (struct/union) dst, copy chunk-by-chunk using R11
      -- as a scratch register:  movq off(%r10), %r11; movq %r11, PseudoMem(dst, off).
      -- This avoids emitting mem-to-mem moves with a ByteArray AsmType (which would panic).
      let dstT := valAsmType bst dst
      if dstT == .Double then
        ([.Mov .Quadword (convertVal ptr) (.Reg .R10),
          .Movsd (.Memory .R10 0) (convertVal dst)], ctr)
      else
        match dstT with
        | .ByteArray totalBytes _ =>
            -- Struct load: R10 = pointer; copy each chunk via R11.
            let dstName := match dst with | .Var n => n | .Constant _ => "_"
            let nFull := totalBytes / 8
            let rem   := totalBytes % 8
            let ptrInstr : Instruction := .Mov .Quadword (convertVal ptr) (.Reg .R10)
            -- Full 8-byte chunks: movq off(%r10), %r11; movq %r11, PseudoMem(dst, off)
            let fullInstrs : List Instruction := (List.range nFull).flatMap fun i =>
              let off : Int := (i * 8 : Nat)
              [.Mov .Quadword (.Memory .R10 off) (.Reg .R11),
               .Mov .Quadword (.Reg .R11) (.PseudoMem dstName off)]
            -- Trailing bytes (using Longword for 4-byte remainder, then Byte per remaining byte)
            let baseOff : Int := (nFull * 8 : Nat)
            let tailInstrs : List Instruction :=
              let (instrs, off) :=
                (if rem >= 4 then
                  ([.Mov .Longword (.Memory .R10 baseOff) (.Reg .R11),
                    .Mov .Longword (.Reg .R11) (.PseudoMem dstName baseOff)],
                   baseOff + 4)
                else ([], baseOff))
              (List.range (rem % 4)).foldl (fun (st : List Instruction × Int) i =>
                let (is, o) := st
                (is ++ [.Mov .Byte (.Memory .R10 o) (.Reg .R11),
                        .Mov .Byte (.Reg .R11) (.PseudoMem dstName o)], o + 1))
                (instrs, off) |>.1
            ([ptrInstr] ++ fullInstrs ++ tailInstrs, ctr)
        | _ =>
            ([.Mov .Quadword (convertVal ptr) (.Reg .R10),
              .Mov dstT (.Memory .R10 0) (convertVal dst)], ctr)
  | .Store src ptr =>
      -- Store src through the pointer address stored in ptr.
      -- Step 1: move the pointer (64-bit address) into R11.
      -- Step 2: store src into (%r11).
      -- Chapter 18: for ByteArray (struct/union) src, copy chunk-by-chunk using R10
      -- as a scratch register:  movq PseudoMem(src, off), %r10; movq %r10, off(%r11).
      -- This avoids emitting mem-to-mem moves with a ByteArray AsmType (which would panic).
      let srcT := valAsmType bst src
      if srcT == .Double then
        ([.Mov .Quadword (convertVal ptr) (.Reg .R11),
          .Movsd (convertVal src) (.Memory .R11 0)], ctr)
      else
        match srcT with
        | .ByteArray totalBytes _ =>
            -- Struct store: R11 = pointer; copy each chunk via R10.
            let srcName := match src with | .Var n => n | .Constant _ => "_"
            let nFull := totalBytes / 8
            let rem   := totalBytes % 8
            let ptrInstr : Instruction := .Mov .Quadword (convertVal ptr) (.Reg .R11)
            -- Full 8-byte chunks: movq PseudoMem(src, off), %r10; movq %r10, off(%r11)
            let fullInstrs : List Instruction := (List.range nFull).flatMap fun i =>
              let off : Int := (i * 8 : Nat)
              [.Mov .Quadword (.PseudoMem srcName off) (.Reg .R10),
               .Mov .Quadword (.Reg .R10) (.Memory .R11 off)]
            -- Trailing bytes
            let baseOff : Int := (nFull * 8 : Nat)
            let tailInstrs : List Instruction :=
              let (instrs, off) :=
                (if rem >= 4 then
                  ([.Mov .Longword (.PseudoMem srcName baseOff) (.Reg .R10),
                    .Mov .Longword (.Reg .R10) (.Memory .R11 baseOff)],
                   baseOff + 4)
                else ([], baseOff))
              (List.range (rem % 4)).foldl (fun (st : List Instruction × Int) i =>
                let (is, o) := st
                (is ++ [.Mov .Byte (.PseudoMem srcName o) (.Reg .R10),
                        .Mov .Byte (.Reg .R10) (.Memory .R11 o)], o + 1))
                (instrs, off) |>.1
            ([ptrInstr] ++ fullInstrs ++ tailInstrs, ctr)
        | _ =>
            ([.Mov .Quadword (convertVal ptr) (.Reg .R11),
              .Mov srcT (convertVal src) (.Memory .R11 0)], ctr)
  -- Chapter 15: pointer arithmetic -----------------------------------------------
  | .AddPtr ptr idx scale dst =>
      -- dst = ptr + idx * scale.  Lowers to:
      --   1. movq ptr, R11                     — load pointer into scratch reg
      --   2. movslq idx, R9 (or movq idx, R9)  — sign-extend/copy index to 64-bit
      --   3a. leaq (R11, R9, scale), dst        — if scale ∈ {1,2,4,8} (x86 addressing)
      --   3b. imulq $scale, R9; leaq (R11,R9,1) — otherwise (multi-dimensional arrays with
      --                                            element sizes like 12, 16, 20, 24, …)
      -- x86 `leaq (base, idx, scale)` only supports scale ∈ {1, 2, 4, 8}.
      -- For larger or non-power-of-2 scales (e.g. `int a[N][3]` → scale = 12),
      -- we multiply the index by the scale first using imulq, then use scale=1.
      let idxT := valAsmType bst idx
      let extendIdx : List Instruction :=
        if idxT == .Byte then
          -- Chapter 16: char index — sign-extend byte directly to 64-bit
          [.Movsx .Byte .Quadword (convertVal idx) (.Reg .R9)]
        else if idxT == .Longword then
          -- Int index — sign-extend 32-bit → 64-bit (handles negative indices correctly)
          [.Movsx .Longword .Quadword (convertVal idx) (.Reg .R9)]
        else
          -- Long/ULong/Pointer index — copy 64-bit directly
          [.Mov .Quadword (convertVal idx) (.Reg .R9)]
      let scaleInstrs : List Instruction :=
        if scale == 1 || scale == 2 || scale == 4 || scale == 8 then
          -- Valid leaq scale: use (base, idx, scale) addressing directly
          [.Lea (.Indexed .R11 .R9 scale) (convertVal dst)]
        else
          -- Scale not encodable in leaq: multiply first, then use scale=1
          [.Binary .Quadword .Mult (.Imm scale) (.Reg .R9),
           .Lea (.Indexed .R11 .R9 1) (convertVal dst)]
      ([.Mov .Quadword (convertVal ptr) (.Reg .R11)] ++
       extendIdx ++
       scaleInstrs, ctr)
  | .CopyToOffset src dstName offset =>
      -- Copy `src` to byte offset `offset` within aggregate variable `dstName`.
      -- PseudoReplace converts PseudoMem(dstName, offset) to Memory(BP, base + offset).
      let srcT := valAsmType bst src
      if srcT == .Double then
        ([.Movsd (convertVal src) (.PseudoMem dstName offset)], ctr)
      else
        match srcT with
        | .ByteArray totalBytes _ =>
            -- Chapter 18: struct-typed src (e.g. initializing an array element with a struct).
            -- Copy chunk-by-chunk from src into dstName at offset, using R10 as scratch.
            let srcName := match src with | .Var n => n | .Constant _ => "_"
            let nFull := totalBytes / 8
            let rem   := totalBytes % 8
            let fullInstrs : List Instruction := (List.range nFull).flatMap fun i =>
              let srcOff : Int := (i * 8 : Nat)
              let dstOff : Int := offset + srcOff
              [.Mov .Quadword (.PseudoMem srcName srcOff) (.Reg .R10),
               .Mov .Quadword (.Reg .R10) (.PseudoMem dstName dstOff)]
            let baseOff : Int := (nFull * 8 : Nat)
            let tailInstrs : List Instruction :=
              let (instrs, off) :=
                (if rem >= 4 then
                  ([.Mov .Longword (.PseudoMem srcName baseOff) (.Reg .R10),
                    .Mov .Longword (.Reg .R10) (.PseudoMem dstName (offset + baseOff))],
                   baseOff + 4)
                else ([], baseOff))
              (List.range (rem % 4)).foldl (fun (st : List Instruction × Int) i =>
                let (is, o) := st
                (is ++ [.Mov .Byte (.PseudoMem srcName o) (.Reg .R10),
                        .Mov .Byte (.Reg .R10) (.PseudoMem dstName (offset + o))], o + 1))
                (instrs, off) |>.1
            (fullInstrs ++ tailInstrs, ctr)
        | _ => ([.Mov srcT (convertVal src) (.PseudoMem dstName offset)], ctr)
  | .CopyFromOffset srcName offset dst =>
      -- Chapter 18: read one member from a struct/union variable.
      -- `CopyFromOffset(srcName, offset, dst)` reads the scalar value at byte `offset`
      -- within aggregate variable `srcName` into `dst`.
      -- PseudoReplace converts PseudoMem(srcName, offset) → Memory(BP, base + offset)
      -- for local vars, or → Data(srcName, offset) for static vars.
      let dstT := valAsmType bst dst
      if dstT == .Double then
        ([.Movsd (.PseudoMem srcName offset) (convertVal dst)], ctr)
      else
        ([.Mov dstT (.PseudoMem srcName offset) (convertVal dst)], ctr)

/-- Convert a TACKY function definition to assembly, threading the global label
    counter so that ULong↔Double branch labels are unique across all functions
    in the same compilation unit.
    Chapter 18: if the function returns a MEMORY-class struct (size > 16 bytes):
      - Save the hidden return-value pointer (RDI) at Memory(BP, -8) on entry.
      - Start emitParamCopies at intIdx = 1 (DI is occupied by the hidden pointer).
      - Pass isMemReturn = true to convertInstruction so the Return handler emits
        the struct-copy-to-hidden-pointer sequence. -/
private def convertFunctionDef (f : Tacky.FunctionDef) (bst : BackendSymTable) (initCtr : Nat)
    (tt : Semantics.TypeTable) (typMap : List (String × AST.Typ))
    : FunctionDef × Nat :=
  -- Determine if this function returns a MEMORY-class struct (size > 16 bytes).
  -- For ≤ 16 bytes, the struct is always register-returned (no MEMORY possible).
  let retAsmType : AsmType := match lookupBst bst f.name with
    | some (.FunEntry _ rt) => rt | _ => .Longword
  let isMemReturn : Bool :=
    match retAsmType with
    | .ByteArray size _ => size > 16
    | _                 => false
  -- If MEMORY return: emit movq %rdi, -8(%rbp) at function entry to save the
  -- hidden return-value pointer that the caller placed in RDI.
  let hiddenPtrSave : List Instruction :=
    if isMemReturn then
      [.Mov .Quadword (.Reg .DI) (.Memory .BP (-8 : Int))]
    else []
  -- Emit parameter copies; integer args start at index 1 if MEMORY return.
  let paramCopies := emitParamCopies f.params bst tt typMap (if isMemReturn then 1 else 0)
  let (bodyInstrs, finalCtr) := f.body.foldl (fun (acc : List Instruction × Nat) i =>
    let (instrs, ctr) := acc
    let (new, ctr') := convertInstruction i bst ctr tt typMap isMemReturn
    (instrs ++ new, ctr')) ([], initCtr)
  ({ name         := f.name,
     global       := f.global,
     params       := f.params,
     instructions := hiddenPtrSave ++ paramCopies ++ bodyInstrs,
     stackSize    := 0 },
   finalCtr)

/-- Chapter 15+16: convert one `Tacky.StaticInit` element to its `AssemblyAST.StaticInit`.
    The two types are structurally identical except for the namespace. -/
private def convertStaticInit : Tacky.StaticInit → StaticInit
  | .IntInit n      => .IntInit n
  | .LongInit n     => .LongInit n
  | .UIntInit n     => .UIntInit n
  | .ULongInit n    => .ULongInit n
  | .DoubleInit f   => .DoubleInit f
  | .ZeroInit n     => .ZeroInit n
  | .CharInit n     => .CharInit n       -- Chapter 16: 1-byte signed char (.byte)
  | .UCharInit n    => .UCharInit n      -- Chapter 16: 1-byte unsigned char (.byte)
  | .StringInit s b => .StringInit s b   -- Chapter 16: string bytes (.asciz/.ascii)
  | .PointerInit s  => .PointerInit s    -- Chapter 16: 8-byte pointer to label (.quad)

/-- Convert a TACKY StaticVariable (with a `List StaticInit`) to an assembly
    StaticVariable.  Determines alignment from the AST type.
    Chapter 18: struct/union alignment is looked up from the TypeTable. -/
private def convertStaticVar (name : String) (global : Bool) (typ : AST.Typ)
    (inits : List Tacky.StaticInit) (tt : Semantics.TypeTable) : AsmTopLevel :=
  -- Alignment: Int/UInt → 4; Char/SChar/UChar → 1; Array → array.alignOf;
  -- Struct/Union → TypeTable.alignment; everything else → 8
  let alignment : Nat := match typ with
    | .Int  | .UInt              => 4
    | .Char | .SChar | .UChar    => 1   -- Chapter 16: char types are 1-byte aligned
    | .Array elem n              =>
        if elem.sizeOf * n < 16 then elem.alignOf else 16
    | .Struct tag | .Union tag   =>     -- Chapter 18: struct/union alignment from TypeTable
        match Semantics.lookupTypeTable tt tag with
        | some sd => sd.alignment
        | none    => 8
    | _                          => 8
  let asmInits := inits.map convertStaticInit
  .StaticVariable name global alignment asmInits

/-- Entry point for pass 1: TACKY → Assembly AST with pseudoregisters.
    The label counter is threaded across all functions so that every
    ULong↔Double branch label is unique within the whole compilation unit.
    Chapter 18:
      `tt`      — TypeTable for struct/union layout (ABI classification + alignment).
      `typMap`  — combined map from variable/temp names to their AST.Typ, used to
                  look up the struct tag for a named variable so that `classifyForABI`
                  can determine per-eightbyte INTEGER/SSE classification. -/
def genProgram (p : Tacky.Program) (bst : BackendSymTable)
    (tt : Semantics.TypeTable) (typMap : List (String × AST.Typ)) : Program :=
  let (topLevels, _) := p.topLevels.foldl (fun (acc : List AsmTopLevel × Nat) tl =>
    let (tls, ctr) := acc
    match tl with
    | .Function fd =>
        let (asmFd, ctr') := convertFunctionDef fd bst ctr tt typMap
        (tls ++ [AsmTopLevel.Function asmFd], ctr')
    | .StaticVariable n g t inits =>
        (tls ++ [convertStaticVar n g t inits tt], ctr)
    | .StaticConstant n align inits =>
        -- Chapter 16: string constant items (`.Lstr.N`) from TackyGen flow through here.
        -- Convert each StaticInit variant; the alignment and name pass unchanged.
        let asmInits := inits.map convertStaticInit
        (tls ++ [AsmTopLevel.StaticConstant n align asmInits], ctr))
    ([], 0)
  { topLevels }

end AssemblyAST
