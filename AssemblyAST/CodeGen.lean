import Tacky.Tacky
import AssemblyAST.AssemblyAST

/-
  Pass 1 of assembly generation: converts Tacky.Program → AssemblyAST.Program.
  Temporary variables are kept as Pseudo operands; they are replaced with
  concrete stack locations in pass 2 (PseudoReplace).

  Conversion tables (Tables 3-3 through 3-6):

    TACKY top-level         Assembly top-level
    ─────────────────────────────────────────────────────
    Program(func)           Program(func)
    Function(name, body)    Function(name, instructions)

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

    TACKY operator          Assembly operator
    ─────────────────────────────────────────
    Complement              Not
    Negate                  Neg
    Add                     Add
    Subtract                Sub
    Multiply                Mult
    BitAnd                  And
    BitOr                   Or
    BitXor                  Xor
    ShiftLeft               Sal  (count always via Reg(CX) → %cl)
    ShiftRight              Sar  (count always via Reg(CX) → %cl)

    TACKY operand           Assembly operand
    ─────────────────────────────────────────
    Constant(int)           Imm(int)
    Var(identifier)         Pseudo(identifier)
-/

namespace AssemblyAST

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
    control-flow instructions. -/
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

/-- Convert a TACKY function body to an assembly function definition.
    Each TACKY instruction may expand to multiple assembly instructions, so
    `convertInstruction` is mapped over the body and the results are
    concatenated in order with `foldl`. -/
private def convertFunctionDef (f : Tacky.FunctionDef) : FunctionDef :=
  { name := f.name,
    instructions := f.body.foldl (fun acc i => acc ++ convertInstruction i) [] }

/-- Entry point for pass 1.
    Converts a complete TACKY program to an assembly program with
    pseudoregister operands still present. -/
def genProgram (p : Tacky.Program) : Program :=
  { func := convertFunctionDef p.func }

end AssemblyAST
