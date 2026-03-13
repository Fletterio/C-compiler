import Tacky.Tacky
import AssemblyAST.AssemblyAST

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

private def convertVal : Tacky.Val → Operand
  | .Constant n => .Imm n
  | .Var id     => .Pseudo id

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
    separate register banks per the System V AMD64 ABI. -/
private def emitParamCopies (params : List String) (bst : BackendSymTable) : List Instruction :=
  let rec go (ps : List String) (intIdx floatIdx stackIdx : Nat) (acc : List Instruction)
      : List Instruction :=
    match ps with
    | [] => acc
    | p :: rest =>
        let asmT : AsmType := match lookupBst bst p with
          | some (.ObjEntry t _ _) => t
          | _                      => .Longword
        match asmT with
        | .Double =>
            -- Float argument: use XMM register if available, else stack
            if floatIdx < 8 then
              let reg := xmmArgRegs.getD floatIdx .XMM0
              go rest intIdx (floatIdx + 1) stackIdx
                (acc ++ [.Movsd (.Reg reg) (.Pseudo p)])
            else
              let stackOff : Int := ((stackIdx + 2) * 8 : Nat)
              go rest intIdx floatIdx (stackIdx + 1)
                (acc ++ [.Movsd (.Stack stackOff) (.Pseudo p)])
        | _ =>
            -- Integer argument: use integer register if available, else stack
            if intIdx < 6 then
              let reg := intArgRegs.getD intIdx .DI
              go rest (intIdx + 1) floatIdx stackIdx
                (acc ++ [.Mov asmT (.Reg reg) (.Pseudo p)])
            else
              let stackOff : Int := ((stackIdx + 2) * 8 : Nat)
              go rest intIdx floatIdx (stackIdx + 1)
                (acc ++ [.Mov asmT (.Stack stackOff) (.Pseudo p)])
  go params 0 0 0 []

/-- Generate assembly for a TACKY FunCall instruction.
    Chapter 13: classifies each argument as integer or double, placing
    arguments into the appropriate register bank or the stack. -/
private def convertFunCall (name : String) (args : List Tacky.Val) (dst : Tacky.Val)
    (bst : BackendSymTable) (labelCounter : Nat) : List Instruction × Nat :=
  -- Classify args into int-reg, xmm-reg, and stack groups (preserving order)
  -- Count separately: first 6 non-double args → intArgRegs; first 8 double args → xmmArgRegs
  let (intRegArgs, xmmRegArgs, stackArgs, _, _) :=
    args.foldl
      (fun acc arg =>
        let (ia, xa, sa, iIdx, xIdx) := acc
        let t := valAsmType bst arg
        if t == .Double then
          if xIdx < 8 then (ia, xa ++ [(arg, xIdx)], sa, iIdx, xIdx + 1)
          else (ia, xa, sa ++ [arg], iIdx, xIdx + 1)
        else
          if iIdx < 6 then (ia ++ [(arg, iIdx)], xa, sa, iIdx + 1, xIdx)
          else (ia, xa, sa ++ [arg], iIdx + 1, xIdx))
      (([] : List (Tacky.Val × Nat)), ([] : List (Tacky.Val × Nat)),
       ([] : List Tacky.Val), 0, 0)
  -- Stack padding: push args right-to-left; odd count → 8-byte pad
  let stackPad : Int := if stackArgs.length % 2 == 1 then 8 else 0
  let padInstrs : List Instruction :=
    if stackPad != 0 then [.Binary .Quadword .Sub (.Imm stackPad) (.Reg .SP)] else []
  -- Move integer args into integer registers
  let intRegInstrs : List Instruction :=
    intRegArgs.map fun (arg, idx) =>
      let reg := intArgRegs.getD idx .DI
      let t   := valAsmType bst arg
      .Mov t (convertVal arg) (.Reg reg)
  -- Move double args into XMM registers
  let xmmRegInstrs : List Instruction :=
    xmmRegArgs.map fun (arg, idx) =>
      let reg := xmmArgRegs.getD idx .XMM0
      .Movsd (convertVal arg) (.Reg reg)
  -- Push stack args in reverse order
  let pushInstrs : List Instruction :=
    stackArgs.reverse.foldl (fun acc arg =>
      let op := convertVal arg
      let t  := valAsmType bst arg
      match t, op with
      | .Double, _ =>
          -- Push double via movq+pushq:
          --   1. movq op, %r10  — copy the raw 64-bit double bits into GP register
          --   2. pushq %r10     — decrement RSP and write to (%rsp)
          -- This avoids (%rsp) addressing, which our Stack(n) = n(%rbp) can't express.
          -- Note: at this stage (before register allocation), double operands are always
          -- memory (Stack/Data/Pseudo), so Mov .Quadword is safe (no XMM-to-GP needed).
          acc ++ [.Mov .Quadword op (.Reg .R10), .Push (.Reg .R10)]
      | _, .Reg _  => acc ++ [.Push op]
      | _, .Imm _  => acc ++ [.Push op]
      | _, _       => acc ++ [.Mov t op (.Reg .AX), .Push (.Reg .AX)]) []
  let deallocBytes : Int := stackArgs.length * 8 + stackPad
  let callInstr : List Instruction := [.Call name]
  let deallocInstrs : List Instruction :=
    if deallocBytes != 0 then
      [.Binary .Quadword .Add (.Imm deallocBytes) (.Reg .SP)]
    else []
  -- Retrieve return value
  let retAsmType : AsmType := match lookupBst bst name with
    | some (.FunEntry _ rt) => rt
    | _                     => .Longword
  let retInstrs : List Instruction :=
    if retAsmType == .Double then
      [.Movsd (.Reg .XMM0) (convertVal dst)]
    else
      [.Mov retAsmType (.Reg .AX) (convertVal dst)]
  (padInstrs ++ intRegInstrs ++ xmmRegInstrs ++ pushInstrs ++
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
  let thresh     := Operand.Data ".Lulong_thresh"
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
    Returns a list of instructions and an updated label counter. -/
private def convertInstruction (instr : Tacky.Instruction) (bst : BackendSymTable)
    (ctr : Nat) : List Instruction × Nat :=
  match instr with
  | .Return v =>
      let t := valAsmType bst v
      if t == .Double then
        ([.Movsd (convertVal v) (.Reg .XMM0), .Ret], ctr)
      else
        ([.Mov t (convertVal v) (.Reg .AX), .Ret], ctr)
  | .SignExtend src dst =>
      ([.Movsx (convertVal src) (convertVal dst)], ctr)
  | .Truncate src dst =>
      ([.Mov .Longword (convertVal src) (convertVal dst)], ctr)
  | .ZeroExtend src dst =>
      ([.MovZeroExtend (convertVal src) (convertVal dst)], ctr)
  -- Chapter 13: integer ↔ double conversions
  | .IntToDouble src dst =>
      -- For Long src: use Quadword; for Int src: use Longword
      let srcT := valAsmType bst src
      let intT := if srcT == .Quadword then .Quadword else .Longword
      ([.Cvtsi2sd intT (convertVal src) (convertVal dst)], ctr)
  | .DoubleToInt src dst =>
      let dstT := valAsmType bst dst
      let intT := if dstT == .Quadword then .Quadword else .Longword
      ([.Cvttsd2si intT (convertVal src) (convertVal dst)], ctr)
  | .UIntToDouble src dst =>
      -- Zero-extend UInt (32-bit) to 64-bit via MovZeroExtend into R10,
      -- then cvtsi2sdq R10, dst
      ([.MovZeroExtend (convertVal src) (.Reg .R10),
        .Cvtsi2sd .Quadword (.Reg .R10) (convertVal dst)], ctr)
  | .DoubleToUInt src dst =>
      -- Convert double to Long (Quadword), then truncate to Int (Longword)
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
          .Movsd (.Data ".Lneg_zero") (.Reg .XMM15),
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
        ([.Mov t (convertVal src) (convertVal dst)], ctr)
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
      convertFunCall name args dst bst ctr

/-- Convert a TACKY function definition to assembly, threading the global label
    counter so that ULong↔Double branch labels are unique across all functions
    in the same compilation unit. -/
private def convertFunctionDef (f : Tacky.FunctionDef) (bst : BackendSymTable) (initCtr : Nat)
    : FunctionDef × Nat :=
  let paramCopies := emitParamCopies f.params bst
  let (bodyInstrs, finalCtr) := f.body.foldl (fun (acc : List Instruction × Nat) i =>
    let (instrs, ctr) := acc
    let (new, ctr') := convertInstruction i bst ctr
    (instrs ++ new, ctr')) ([], initCtr)
  ({ name         := f.name,
     global       := f.global,
     params       := f.params,
     instructions := paramCopies ++ bodyInstrs,
     stackSize    := 0 },
   finalCtr)

/-- Convert a typed TACKY StaticVariable to an assembly StaticVariable.
    Chapter 13: handles `ConstDouble` init. -/
private def convertStaticVar (name : String) (global : Bool) (typ : AST.Typ) (init : AST.Const)
    : AsmTopLevel :=
  match init with
  | .ConstInt n    => .StaticVariable name global 4 (.IntInit n)
  | .ConstLong n   => .StaticVariable name global 8 (.LongInit n)
  | .ConstUInt n   => .StaticVariable name global 4 (.UIntInit n)
  | .ConstULong n  => .StaticVariable name global 8 (.ULongInit n)
  | .ConstDouble f => .StaticVariable name global 8 (.DoubleInit f)

/-- Entry point for pass 1: TACKY → Assembly AST with pseudoregisters.
    The label counter is threaded across all functions so that every
    ULong↔Double branch label is unique within the whole compilation unit. -/
def genProgram (p : Tacky.Program) (bst : BackendSymTable) : Program :=
  let (topLevels, _) := p.topLevels.foldl (fun (acc : List AsmTopLevel × Nat) tl =>
    let (tls, ctr) := acc
    match tl with
    | .Function fd =>
        let (asmFd, ctr') := convertFunctionDef fd bst ctr
        (tls ++ [AsmTopLevel.Function asmFd], ctr')
    | .StaticVariable n g t i =>
        (tls ++ [convertStaticVar n g t i], ctr))
    ([], 0)
  { topLevels }

end AssemblyAST
