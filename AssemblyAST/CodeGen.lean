import Tacky.Tacky
import AssemblyAST.AssemblyAST

/-
  Pass 1 of assembly generation: converts Tacky.Program → AssemblyAST.Program.
  Temporary variables are kept as Pseudo operands; they are replaced with
  concrete stack locations in pass 2 (PseudoReplace).

  Chapter 9 additions:
    - Parameter-copy instructions are emitted at function entry.
      The first 6 parameters are passed in DI, SI, DX, CX, R8, R9.
      Additional parameters are on the stack at 16(%rbp), 24(%rbp), etc.
    - FunCall TACKY instruction is lowered to:
        1. Move each register argument to the appropriate argument register.
        2. Push each stack argument (in reverse order).
        3. Padding if odd number of stack args (for 16-byte alignment).
        4. Call instruction.
        5. DeallocateStack to reclaim arg space.
        6. Move AX to destination.

  Conversion tables (Tables 3-3 through 3-6, updated):

    TACKY top-level         Assembly top-level
    ─────────────────────────────────────────────────────
    Program(funcs)           Program(funcs)
    Function(name,params,body)  Function(name,params,instructions,stackSize=0)

    TACKY instruction              Assembly instructions
    ──────────────────────────────────────────────────────────────
    Return(val)                    Mov(val, Reg(AX))
                                   Ret
    Unary(op, src, dst)            Mov(src, dst)
                                   Unary(op, dst)
    Binary(Divide, s1, s2, dst)    Mov(s1, Reg(AX))
                                   Cdq
                                   Idiv(s2)
                                   Mov(Reg(AX), dst)
    Binary(Remainder, s1, s2, dst) Mov(s1, Reg(AX))
                                   Cdq
                                   Idiv(s2)
                                   Mov(Reg(DX), dst)
    Binary(op, s1, s2, dst)        Mov(s1, dst)
                                   Binary(op, s2, dst)
    FunCall(name, args, dst)       [padding if odd stack args]
                                   [Move register args to DI/SI/DX/CX/R8/R9]
                                   [Push stack args in reverse]
                                   Call(name)
                                   [DeallocateStack if stack args]
                                   Mov(Reg(AX), dst)
-/

namespace AssemblyAST

/-- The six integer argument registers in System V AMD64 calling convention order.
    First argument → DI, second → SI, third → DX, fourth → CX,
    fifth → R8, sixth → R9. -/
private def argRegs : List Reg := [.DI, .SI, .DX, .CX, .R8, .R9]

/-- Map a TACKY unary operator to its assembly equivalent.
    `Complement` (bitwise NOT `~`) becomes `Not` (the `notl` instruction).
    `Negate` (arithmetic negation `-`) becomes `Neg` (the `negl` instruction).
    `Not` is handled separately in `convertInstruction` via `Cmp`+`SetCC`;
    this arm is a fallback that should never be reached. -/
private def convertUnop : Tacky.UnaryOp → UnaryOp
  | .Complement => .Not
  | .Negate     => .Neg
  | .Not        => .Not  -- unreachable: .Not is expanded in convertInstruction

/-- Map a TACKY binary operator to its assembly equivalent.
    Not called for Divide, Remainder, ShiftLeft, ShiftRight, or any relational
    operator; those are handled by dedicated arms in `convertInstruction`. -/
private def convertBinop : Tacky.BinaryOp → BinaryOp
  | .Add        => .Add
  | .Subtract   => .Sub
  | .Multiply   => .Mult
  | .BitAnd     => .And
  | .BitOr      => .Or
  | .BitXor     => .Xor
  | _           => .Add  -- unreachable: Divide/Remainder/Shift/relational handled separately

/-- Map a TACKY relational binary operator to the corresponding condition code.
    Returns `none` for non-relational operators (handled elsewhere). -/
private def relCondCode : Tacky.BinaryOp → Option CondCode
  | .Equal          => some .E
  | .NotEqual       => some .NE
  | .LessThan       => some .L
  | .LessOrEqual    => some .LE
  | .GreaterThan    => some .G
  | .GreaterOrEqual => some .GE
  | _               => none

/-- Map a TACKY value to an assembly operand.
    `Constant(n)` becomes an immediate `Imm(n)`.
    `Var(id)` becomes a `Pseudo(id)` pseudoregister, which pass 2 will later
    replace with a concrete `Stack` address. -/
private def convertVal : Tacky.Val → Operand
  | .Constant n => .Imm n
  | .Var id     => .Pseudo id

/-- Generate parameter-copy instructions for a function definition.
    At function entry, the calling convention places arguments as follows:
      - params[0] in DI (first argument register)
      - params[1] in SI
      - params[2] in DX
      - params[3] in CX
      - params[4] in R8
      - params[5] in R9
      - params[6] at 16(%rbp)  (first stack argument; +8 past saved RBP)
      - params[7] at 24(%rbp)
      - params[8] at 32(%rbp)
      - etc.
    We emit `movl` instructions to copy from each location into the pseudo
    variable named for the parameter.  PseudoReplace will later assign the
    pseudo a stack slot in the current frame. -/
private def emitParamCopies (params : List String) : List Instruction :=
  -- Enumerate parameters with their index (0-based) by pairing with a range
  let indexed : List (Nat × String) := (List.range params.length).zip params
  indexed.map fun (i, paramName) =>
    let dst := Operand.Pseudo paramName
    if i < 6 then
      -- Register argument: copy from the appropriate arg register
      -- argRegs has 6 elements; i < 6 is guaranteed by the outer if condition.
      -- Use array indexing for O(1) access.
      let argRegsArr : Array Reg := #[.DI, .SI, .DX, .CX, .R8, .R9]
      let reg := argRegsArr.getD i .DI
      .Mov (.Reg reg) dst
    else
      -- Stack argument: callers push extras at 16(%rbp), 24(%rbp), etc.
      -- The layout is: return address at 8(%rbp), saved RBP at 0(%rbp),
      -- so the first stack argument is at 16(%rbp), second at 24(%rbp), etc.
      let stackOffset : Int := ((i - 6 + 2) * 8 : Nat)
      .Mov (.Stack stackOffset) dst

/-- Generate assembly instructions for a TACKY FunCall instruction.
    Implements the System V AMD64 calling convention:
      1. If there are an odd number of stack arguments, emit AllocateStack(8)
         as padding so RSP is 16-byte aligned when `call` executes.
      2. Emit Mov instructions for each register argument (first 6).
      3. Emit Push instructions for each stack argument, in REVERSE order.
      4. Emit Call(name).
      5. Emit DeallocateStack if there were any stack args (includes padding).
      6. Emit Mov(AX, dst) to retrieve the return value.

    Note: for stack arguments that are already Reg or Imm operands, we can
    push them directly.  For memory (Stack) operands, we must load into AX
    first (x86 does not allow `pushq mem` in general; more importantly, the
    calling convention requires the pushed value to be the full 8-byte word,
    whereas our values are 32-bit and would need zero/sign extension). -/
private def convertFunCall (name : String) (args : List Tacky.Val) (dst : Tacky.Val)
    : List Instruction :=
  let argOps    := args.map convertVal
  -- Split into register args (first 6) and stack args (rest)
  let regArgs   := (argOps.zip argRegs).take 6   -- pairs (operand, reg)
  let stackArgs := if argOps.length <= 6 then [] else argOps.drop 6
  -- Padding: if stack arg count is odd, add 8 bytes so RSP stays 16-byte aligned.
  -- (After function prologue, RSP is 16-byte aligned; each push decrements by 8.)
  let stackPad  : Int := if stackArgs.length % 2 == 1 then 8 else 0
  let padInstrs : List Instruction :=
    if stackPad != 0 then [.AllocateStack stackPad] else []
  -- Move register arguments into their respective argument registers
  let regInstrs : List Instruction :=
    regArgs.map fun (op, reg) => .Mov op (.Reg reg)
  -- Push stack arguments in reverse order (last arg pushed first)
  -- If the operand is already a register or immediate, push directly.
  -- If it's a stack/pseudo memory operand, copy to AX first, then push.
  let pushInstrs : List Instruction :=
    stackArgs.reverse.foldl (fun acc op =>
      match op with
      | .Reg _  => acc ++ [.Push op]
      | .Imm _  => acc ++ [.Push op]
      | _       =>
          -- Load into AX (scratch) then push the 64-bit register
          acc ++ [.Mov op (.Reg .AX), .Push (.Reg .AX)]) []
  -- Amount to deallocate: stack args (8 bytes each) + padding
  let deallocBytes : Int := stackArgs.length * 8 + stackPad
  let callInstr : List Instruction := [.Call name]
  let deallocInstrs : List Instruction :=
    if deallocBytes != 0 then [.DeallocateStack deallocBytes] else []
  -- Retrieve return value from AX
  let retInstrs : List Instruction := [.Mov (.Reg .AX) (convertVal dst)]
  padInstrs ++ regInstrs ++ pushInstrs ++ callInstr ++ deallocInstrs ++ retInstrs

/-- Expand one TACKY instruction into a list of assembly instructions.

    `Return(v)`: move the return value into EAX, then emit `Ret`.

    `Unary(Not, src, dst)`: logical NOT via `cmpl $0, src` (sets ZF if zero),
    then `movl $0, dst` (clears dst without touching flags), then `sete dst`.

    `Unary(op, src, dst)`: copy `src` to `dst`, then apply `op` in-place.

    `Binary(Divide/Remainder, ...)`: sign-extend dividend into EDX:EAX via
    `cdq`, then `idivl`; result is in EAX (quotient) or EDX (remainder).

    `Binary(ShiftLeft/ShiftRight, ...)`: move count into ECX, then shift dst
    in-place using `%cl` (the low byte of ECX).

    `Binary(relational, src1, src2, dst)`: `cmpl src2, src1` (computes
    src1−src2, sets RFLAGS), zero dst, then `set<cc> dst` (writes one byte).

    `Binary(op, s1, s2, dst)`: copy s1 to dst, then apply op(s2, dst).

    `Copy(src, dst)`: single `movl`.

    `Jump/JumpIfZero/JumpIfNotZero/Label`: lower directly to assembly
    control-flow instructions.

    `FunCall(name, args, dst)`: lower to calling-convention sequence. -/
private def convertInstruction : Tacky.Instruction → List Instruction
  | .Return v =>
      [.Mov (convertVal v) (.Reg .AX), .Ret]
  | .Unary .Not src dst =>
      -- Logical NOT: ZF=1 iff src==0, so sete dst gives 1 when src is false.
      [.Cmp (.Imm 0) (convertVal src),
       .Mov (.Imm 0) (convertVal dst),
       .SetCC .E (convertVal dst)]
  | .Unary op src dst =>
      [.Mov (convertVal src) (convertVal dst),
       .Unary (convertUnop op) (convertVal dst)]
  | .Binary .Divide src1 src2 dst =>
      [.Mov (convertVal src1) (.Reg .AX),
       .Cdq,
       .Idiv (convertVal src2),
       .Mov (.Reg .AX) (convertVal dst)]
  | .Binary .Remainder src1 src2 dst =>
      [.Mov (convertVal src1) (.Reg .AX),
       .Cdq,
       .Idiv (convertVal src2),
       .Mov (.Reg .DX) (convertVal dst)]
  | .Binary .ShiftLeft src1 src2 dst =>
      -- x64 shift instructions require the count in %cl or as an immediate.
      -- We always route through CX: move the count into ECX, then shift using %cl.
      [.Mov (convertVal src1) (convertVal dst),
       .Mov (convertVal src2) (.Reg .CX),
       .Binary .Sal (.Reg .CX) (convertVal dst)]
  | .Binary .ShiftRight src1 src2 dst =>
      [.Mov (convertVal src1) (convertVal dst),
       .Mov (convertVal src2) (.Reg .CX),
       .Binary .Sar (.Reg .CX) (convertVal dst)]
  | .Binary op src1 src2 dst =>
      match relCondCode op with
      | some cc =>
          -- cmpl src2, src1 computes src1−src2 and sets RFLAGS.
          -- Zero dst first (set<cc> only writes one byte), then write result.
          [.Cmp (convertVal src2) (convertVal src1),
           .Mov (.Imm 0) (convertVal dst),
           .SetCC cc (convertVal dst)]
      | none =>
          [.Mov (convertVal src1) (convertVal dst),
           .Binary (convertBinop op) (convertVal src2) (convertVal dst)]
  -- Copy is a direct value transfer: lower to Mov.
  | .Copy src dst =>
      [.Mov (convertVal src) (convertVal dst)]
  -- Control flow: lower directly to assembly equivalents.
  | .Jump target =>
      [.Jmp target]
  | .JumpIfZero cond target =>
      [.Cmp (.Imm 0) (convertVal cond), .JmpCC .E target]
  | .JumpIfNotZero cond target =>
      [.Cmp (.Imm 0) (convertVal cond), .JmpCC .NE target]
  | .Label name =>
      [.Label name]
  -- Chapter 9: function call
  | .FunCall name args dst =>
      convertFunCall name args dst

/-- Convert a TACKY function body to an assembly function definition.
    Emits parameter-copy instructions at the top (before the body), then
    expands each TACKY instruction into assembly instructions.
    The `stackSize` field is initialized to 0; PseudoReplace will fill it in. -/
private def convertFunctionDef (f : Tacky.FunctionDef) : FunctionDef :=
  -- Parameter copies: move from calling-convention locations to pseudo variables
  let paramCopies := emitParamCopies f.params
  -- Body: expand each TACKY instruction
  let bodyInstrs := f.body.foldl (fun acc i => acc ++ convertInstruction i) []
  { name         := f.name,
    params       := f.params,
    instructions := paramCopies ++ bodyInstrs,
    stackSize    := 0 }

/-- Entry point for pass 1.
    Converts a complete TACKY program to an assembly program with
    pseudoregister operands still present.
    Chapter 9: processes all function definitions in the program. -/
def genProgram (p : Tacky.Program) : Program :=
  { funcs := p.funcs.map convertFunctionDef }

end AssemblyAST
