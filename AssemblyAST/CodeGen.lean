import Tacky.Tacky
import AssemblyAST.AssemblyAST

/-
  Pass 1 of assembly generation: converts Tacky.Program → AssemblyAST.Program.

  Chapter 11 additions:
    - Takes a `BackendSymTable` as an additional parameter.
    - All instructions are now typed: `Mov(AsmType, ...)`, `Binary(AsmType, ...)`, etc.
    - `lookupAsmType`: looks up the `AsmType` of a `Tacky.Val` from the backend sym table.
    - `SignExtend` TACKY instruction → `Movsx` assembly instruction.
    - `Truncate` TACKY instruction → `Mov(Longword, ...)` assembly instruction.
    - `emitParamCopies`: consults the backend sym table to determine the Mov type.
    - `convertFunCall`: uses `Binary(Quadword, Add/Sub, ...)` instead of the
      removed `AllocateStack`/`DeallocateStack`; retrieves the function's
      return AsmType from the backend sym table.
    - `StaticVariable(n, g, t, i)` → `AsmTopLevel.StaticVariable(n, g, align, init)`.

  Conversion table:
    TACKY instruction              Assembly instructions
    ─────────────────────────────────────────────────────────────────────
    Return(val)                    Mov(retTyp, val, Reg(AX))
                                   Ret
    SignExtend(src, dst)           Movsx(src, dst)
    Truncate(src, dst)             Mov(Longword, src, dst)
    Unary(Not, src, dst)           Cmp(t, Imm(0), src)
                                   Mov(t, Imm(0), dst)
                                   SetCC(E, dst)
    Unary(op, src, dst)            Mov(t, src, dst)
                                   Unary(t, op, dst)
    Binary(Divide, s1, s2, dst)    Mov(t, s1, Reg(AX))
                                   Cdq(t)
                                   Idiv(t, s2)
                                   Mov(t, Reg(AX), dst)
    Binary(Remainder, s1, s2, dst) Mov(t, s1, Reg(AX))
                                   Cdq(t)
                                   Idiv(t, s2)
                                   Mov(t, Reg(DX), dst)
    Binary(ShiftLeft, s1, s2, dst) Mov(t, s1, dst)
                                   Mov(Longword, s2, Reg(CX))
                                   Binary(t, Sal, Reg(CX), dst)
    Binary(ShiftRight, s1, s2, dst) same but Sar
    Binary(relational, ...)        Cmp(t, s2, s1)
                                   Mov(Longword, Imm(0), dst)
                                   SetCC(cc, dst)
    Binary(op, s1, s2, dst)        Mov(t, s1, dst)
                                   Binary(t, op, s2, dst)
    FunCall(name, args, dst)       [see convertFunCall]
-/

namespace AssemblyAST

/-- The six System V AMD64 argument registers in order. -/
private def argRegs : List Reg := [.DI, .SI, .DX, .CX, .R8, .R9]

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
  | .Equal          => some .E    -- equality is same for signed/unsigned
  | .NotEqual       => some .NE
  | .LessThan       => some .B    -- below
  | .LessOrEqual    => some .BE   -- below or equal
  | .GreaterThan    => some .A    -- above
  | .GreaterOrEqual => some .AE   -- above or equal
  | _               => none

private def convertVal : Tacky.Val → Operand
  | .Constant n => .Imm n
  | .Var id     => .Pseudo id

/-- Look up the `AsmType` of a TACKY value from the backend symbol table.
    - `Var(id)`: look up in bst; default to `Longword` if not found.
    - `Constant n`: Quadword if `n` doesn't fit in a signed 32-bit integer AND
      also doesn't fit in an unsigned 32-bit integer (> UINT_MAX).
      Values in (INT_MAX, UINT_MAX] might be UInt (Longword) — use Longword for them. -/
private def valAsmType (bst : BackendSymTable) : Tacky.Val → AsmType
  | .Var id     => match lookupBst bst id with
                   | some (.ObjEntry t _ _) => t
                   | _                      => .Longword
  | .Constant n =>
      -- Values that don't fit in 64-bit unsigned (impossible in practice) → Quadword
      -- Values that don't fit in uint32 (> 2^32−1 or < 0 negatives) → Quadword
      -- Values in [0, 2^32-1] → Longword (could be signed or unsigned 32-bit)
      if n > 4294967295 || n < -2147483648 then .Quadword else .Longword

/-- Determine whether a TACKY value has a signed type (from the backend sym table).
    Constants are assumed signed; named variables check the `isSigned` flag.  -/
private def valIsSigned (bst : BackendSymTable) : Tacky.Val → Bool
  | .Var id     => match lookupBst bst id with
                   | some (.ObjEntry _ isSigned _) => isSigned
                   | _                              => true   -- default: signed
  | .Constant _ => true  -- bare integer constants are treated as signed

/-- Determine the AsmType for a binary instruction from its operands.
    Prefers the type of Var operands over constants; looks at dst first. -/
private def instrAsmType (bst : BackendSymTable) (src dst : Tacky.Val) : AsmType :=
  match dst with
  | .Var id => match lookupBst bst id with
               | some (.ObjEntry t _ _) => t
               | _ => valAsmType bst src
  | .Constant _ => valAsmType bst src

/-- Determine the signedness for a binary instruction from its operands.
    Uses the destination first (mirrors instrAsmType). -/
private def instrIsSigned (bst : BackendSymTable) (src dst : Tacky.Val) : Bool :=
  match dst with
  | .Var id => match lookupBst bst id with
               | some (.ObjEntry _ isSigned _) => isSigned
               | _ => valIsSigned bst src
  | .Constant _ => valIsSigned bst src

/-- Determine the AsmType for a comparison/relational instruction.
    The comparison must use the type of the *operands* (not the result, which
    is always Int for relational ops).
    Chapter 12: prefers Var operand types over constant types (avoids
    misinterpreting large UInt constants as Quadword). -/
private def cmpAsmType (bst : BackendSymTable) (src1 src2 : Tacky.Val) : AsmType :=
  -- Prefer Var-based types; constants may be ambiguous in sign/size.
  match src1, src2 with
  | .Var _, _  => valAsmType bst src1
  | _, .Var _  => valAsmType bst src2
  | _, _       =>
      if valAsmType bst src1 == .Quadword || valAsmType bst src2 == .Quadword
      then .Quadword else .Longword

/-- Determine signedness for a comparison.  Uses the same operand priority as cmpAsmType. -/
private def cmpIsSigned (bst : BackendSymTable) (src1 src2 : Tacky.Val) : Bool :=
  match src1, src2 with
  | .Var _, _  => valIsSigned bst src1
  | _, .Var _  => valIsSigned bst src2
  | _, _       => valIsSigned bst src1

/-- Emit parameter-copy instructions at function entry.
    Consults the backend sym table to choose the correct Mov type for each param. -/
private def emitParamCopies (params : List String) (bst : BackendSymTable) : List Instruction :=
  let indexed : List (Nat × String) := (List.range params.length).zip params
  indexed.map fun (i, paramName) =>
    let t : AsmType := match lookupBst bst paramName with
      | some (.ObjEntry asmT _ _) => asmT
      | _                         => .Longword
    let dst := Operand.Pseudo paramName
    if i < 6 then
      let argRegsArr : Array Reg := #[.DI, .SI, .DX, .CX, .R8, .R9]
      let reg := argRegsArr.getD i .DI
      .Mov t (.Reg reg) dst
    else
      -- Stack argument: at 16(%rbp), 24(%rbp), etc. (8-byte slots in the caller frame)
      let stackOffset : Int := ((i - 6 + 2) * 8 : Nat)
      .Mov t (.Stack stackOffset) dst

/-- Generate assembly for a TACKY FunCall instruction.
    Chapter 11 changes:
    - Padding via `Binary(Quadword, Sub, Imm(8), Reg(SP))` instead of `AllocateStack`.
    - Dealloc via `Binary(Quadword, Add, Imm(n), Reg(SP))` instead of `DeallocateStack`.
    - Return value `Mov` uses the function's `retAsmType` from the backend sym table. -/
private def convertFunCall (name : String) (args : List Tacky.Val) (dst : Tacky.Val)
    (bst : BackendSymTable) : List Instruction :=
  -- Keep the original Tacky.Val list so we can query each arg's AsmType below.
  let regArgVals  := args.take 6
  let stackArgVals := args.drop 6
  let stackPad : Int := if stackArgVals.length % 2 == 1 then 8 else 0
  -- Padding: subq $8, %rsp (instead of AllocateStack)
  let padInstrs : List Instruction :=
    if stackPad != 0 then
      [.Binary .Quadword .Sub (.Imm stackPad) (.Reg .SP)]
    else []
  -- Move register args into argument registers, using each arg's declared AsmType.
  -- For Var args, valAsmType consults the backend sym table (Longword vs Quadword).
  -- For Constant args, valAsmType returns Longword, which is correct for int literals;
  -- large long constants are fixed up later by FixUp (Push) or are valid movabsq.
  let regInstrs : List Instruction :=
    (regArgVals.zip argRegs).map fun (arg, reg) =>
      let t := valAsmType bst arg
      .Mov t (convertVal arg) (.Reg reg)
  -- Push stack args in reverse order; for memory operands, load through AX
  -- using the operand's actual AsmType to avoid reading past the variable boundary.
  let pushInstrs : List Instruction :=
    stackArgVals.reverse.foldl (fun acc arg =>
      let op := convertVal arg
      let t  := valAsmType bst arg
      match op with
      | .Reg _  => acc ++ [.Push op]
      | .Imm _  => acc ++ [.Push op]
      | _       => acc ++ [.Mov t op (.Reg .AX), .Push (.Reg .AX)]) []
  let deallocBytes : Int := stackArgVals.length * 8 + stackPad
  let callInstr : List Instruction := [.Call name]
  -- Dealloc: addq $n, %rsp (instead of DeallocateStack)
  let deallocInstrs : List Instruction :=
    if deallocBytes != 0 then
      [.Binary .Quadword .Add (.Imm deallocBytes) (.Reg .SP)]
    else []
  -- Retrieve return value; use the function's return type from backend sym table
  let retAsmType : AsmType := match lookupBst bst name with
    | some (.FunEntry _ rt) => rt
    | _                     => .Longword   -- default: int-returning
  let retInstrs : List Instruction := [.Mov retAsmType (.Reg .AX) (convertVal dst)]
  padInstrs ++ regInstrs ++ pushInstrs ++ callInstr ++ deallocInstrs ++ retInstrs

/-- Expand one TACKY instruction into typed assembly instructions. -/
private def convertInstruction (instr : Tacky.Instruction) (bst : BackendSymTable)
    : List Instruction :=
  match instr with
  | .Return v =>
      -- Determine the Mov type from the return value
      let t := valAsmType bst v
      [.Mov t (convertVal v) (.Reg .AX), .Ret]
  | .SignExtend src dst =>
      -- movslq: sign-extend 32-bit int to 64-bit long/ulong
      [.Movsx (convertVal src) (convertVal dst)]
  | .Truncate src dst =>
      -- movl: copy low 32 bits (truncation; upper 32 bits discarded)
      [.Mov .Longword (convertVal src) (convertVal dst)]
  | .ZeroExtend src dst =>
      -- Chapter 12: zero-extend 32-bit uint to 64-bit long/ulong
      -- On x86-64, movl to a 32-bit register automatically zeros the upper 32 bits.
      [.MovZeroExtend (convertVal src) (convertVal dst)]
  | .Unary .Not src dst =>
      -- Logical NOT: cmp $0, src (using src's type); movl $0, dst; sete dst.
      -- The dst is always Int (result of !expr is 0 or 1), so use Longword for
      -- the Mov and SetCC.  The CMP must use the src's type (could be Quadword
      -- for a long operand — e.g. `!l` where l = 2^60 has non-zero upper bits).
      let srcT := valAsmType bst src
      [.Cmp srcT (.Imm 0) (convertVal src),
       .Mov .Longword (.Imm 0) (convertVal dst),
       .SetCC .E (convertVal dst)]
  | .Unary op src dst =>
      let t := instrAsmType bst src dst
      [.Mov t (convertVal src) (convertVal dst),
       .Unary t (convertUnop op) (convertVal dst)]
  | .Binary .Divide src1 src2 dst =>
      let t      := instrAsmType bst src1 dst
      let signed := instrIsSigned bst src1 dst
      if signed then
        -- Signed division: sign-extend AX into DX:AX via cdq/cqo, then idiv
        [.Mov t (convertVal src1) (.Reg .AX),
         .Cdq t,
         .Idiv t (convertVal src2),
         .Mov t (.Reg .AX) (convertVal dst)]
      else
        -- Unsigned division (Chapter 12): zero DX (no sign-extend), then div
        [.Mov t (convertVal src1) (.Reg .AX),
         .Mov t (.Imm 0) (.Reg .DX),
         .Div t (convertVal src2),
         .Mov t (.Reg .AX) (convertVal dst)]
  | .Binary .Remainder src1 src2 dst =>
      let t      := instrAsmType bst src1 dst
      let signed := instrIsSigned bst src1 dst
      if signed then
        [.Mov t (convertVal src1) (.Reg .AX),
         .Cdq t,
         .Idiv t (convertVal src2),
         .Mov t (.Reg .DX) (convertVal dst)]
      else
        [.Mov t (convertVal src1) (.Reg .AX),
         .Mov t (.Imm 0) (.Reg .DX),
         .Div t (convertVal src2),
         .Mov t (.Reg .DX) (convertVal dst)]
  | .Binary .ShiftLeft src1 src2 dst =>
      let t := instrAsmType bst src1 dst
      -- Shift count must be in %cl or be an immediate
      [.Mov t (convertVal src1) (convertVal dst),
       .Mov .Longword (convertVal src2) (.Reg .CX),
       .Binary t .Sal (.Reg .CX) (convertVal dst)]
  | .Binary .ShiftRight src1 src2 dst =>
      let t      := instrAsmType bst src1 dst
      let signed := instrIsSigned bst src1 dst
      -- Signed → arithmetic shift right (sar); unsigned → logical shift right (shr)
      let shiftOp := if signed then BinaryOp.Sar else BinaryOp.Shr
      [.Mov t (convertVal src1) (convertVal dst),
       .Mov .Longword (convertVal src2) (.Reg .CX),
       .Binary t shiftOp (.Reg .CX) (convertVal dst)]
  | .Binary op src1 src2 dst =>
      let isSigned := cmpIsSigned bst src1 src2
      match (if isSigned then relCondCodeSigned op else relCondCodeUnsigned op) with
      | some cc =>
          -- Relational: compare src1 and src2; result is always Int, but the
          -- comparison instruction must use the operands' type (could be Quadword
          -- even though the result is Int).  Use cmpAsmType to pick the wider type.
          -- Chapter 12: use unsigned condition codes (A/AE/B/BE) for unsigned operands.
          let t := cmpAsmType bst src1 src2
          [.Cmp t (convertVal src2) (convertVal src1),
           .Mov .Longword (.Imm 0) (convertVal dst),
           .SetCC cc (convertVal dst)]
      | none =>
          let t := instrAsmType bst src1 dst
          [.Mov t (convertVal src1) (convertVal dst),
           .Binary t (convertBinop op) (convertVal src2) (convertVal dst)]
  | .Copy src dst =>
      let t := instrAsmType bst src dst
      [.Mov t (convertVal src) (convertVal dst)]
  | .Jump target =>
      [.Jmp target]
  | .JumpIfZero cond target =>
      let t := valAsmType bst cond
      [.Cmp t (.Imm 0) (convertVal cond), .JmpCC .E target]
  | .JumpIfNotZero cond target =>
      let t := valAsmType bst cond
      [.Cmp t (.Imm 0) (convertVal cond), .JmpCC .NE target]
  | .Label name =>
      [.Label name]
  | .FunCall name args dst =>
      convertFunCall name args dst bst

/-- Convert a TACKY function definition to assembly. -/
private def convertFunctionDef (f : Tacky.FunctionDef) (bst : BackendSymTable) : FunctionDef :=
  let paramCopies := emitParamCopies f.params bst
  let bodyInstrs := f.body.foldl (fun acc i => acc ++ convertInstruction i bst) []
  { name         := f.name,
    global       := f.global,
    params       := f.params,
    instructions := paramCopies ++ bodyInstrs,
    stackSize    := 0 }

/-- Convert a typed TACKY StaticVariable to an assembly StaticVariable.
    Chapter 11: sets alignment (4 for Int, 8 for Long) and typed init.
    Chapter 12: adds UInt (align 4, UIntInit) and ULong (align 8, ULongInit). -/
private def convertStaticVar (name : String) (global : Bool) (typ : AST.Typ) (init : Int)
    : AsmTopLevel :=
  match typ with
  | .Int   => .StaticVariable name global 4 (.IntInit init)
  | .Long  => .StaticVariable name global 8 (.LongInit init)
  | .UInt  => .StaticVariable name global 4 (.UIntInit init)   -- Chapter 12
  | .ULong => .StaticVariable name global 8 (.ULongInit init)  -- Chapter 12

/-- Entry point for pass 1: TACKY → Assembly AST with pseudoregisters. -/
def genProgram (p : Tacky.Program) (bst : BackendSymTable) : Program :=
  let topLevels := p.topLevels.map fun tl =>
    match tl with
    | .Function fd                  => AsmTopLevel.Function (convertFunctionDef fd bst)
    | .StaticVariable n g t i       => convertStaticVar n g t i
  { topLevels }

end AssemblyAST
