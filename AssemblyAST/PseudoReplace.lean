import AssemblyAST.AssemblyAST

/-
  Pass 2 of assembly generation: replace every Pseudo operand with a Stack
  operand at a unique offset from RBP.

  Each distinct pseudoregister is assigned to a 4-byte slot on the stack,
  starting at -4(%rbp) and growing downward: -4, -8, -12, …
  The same identifier always maps to the same slot.

  Chapter 9: each function is processed independently, with its own fresh
  pseudo-to-stack map and its own stack byte count.  The resulting stack size
  is stored in the `FunctionDef.stackSize` field so that FixUp can use it.

  The new `Push` and `DeallocateStack` instructions are also handled:
    - `Push(Pseudo(id))` → `Push(Stack(offset))`
    - `DeallocateStack` has no operands: returned as-is.
    - `Call` has no operands: returned as-is.
-/

namespace AssemblyAST

/-- Mutable state threaded through the pseudo-replacement pass for ONE function.
    `map` is an association list from pseudoregister name to its assigned stack
    offset.  `maxBytes` tracks the total bytes allocated so far; the next slot
    will be at offset `-(maxBytes + 4)`. -/
private structure ReplState where
  map      : List (String × Int)  -- pseudoregister id → stack offset
  maxBytes : Nat                   -- bytes allocated so far

/-- The initial replacement state: no pseudoregisters mapped, nothing allocated. -/
private def ReplState.empty : ReplState := { map := [], maxBytes := 0 }

/-- Look up `id` in the state's map.  If found, return the existing offset.
    If not found, allocate the next 4-byte slot (offset = -(maxBytes + 4)),
    record the mapping, and return the new offset.
    This guarantees that every occurrence of the same pseudoregister is
    replaced with exactly the same stack address. -/
private def ReplState.getOrInsert (s : ReplState) (id : String) : ReplState × Int :=
  match s.map.find? (fun p => p.1 == id) with
  | some (_, offset) => (s, offset)
  | none =>
      let bytes  := s.maxBytes + 4
      let offset : Int := -(bytes : Int)
      ({ map := s.map ++ [(id, offset)], maxBytes := bytes }, offset)

/-- Replace a single operand if it is a `Pseudo`.
    Non-pseudo operands are returned unchanged together with the unmodified
    state, so this function is safe to call on any operand. -/
private def replaceOp (s : ReplState) : Operand → ReplState × Operand
  | .Pseudo id => let (s', off) := s.getOrInsert id; (s', .Stack off)
  | op         => (s, op)

/-- Replace all `Pseudo` operands in a single instruction.
    `Mov` and `Binary` each have two operands, both of which may be pseudos.
    `Unary` and `Idiv` each have one operand.
    `Push` has one operand (new in Chapter 9).
    `Ret`, `Cdq`, `AllocateStack`, `DeallocateStack`, and `Call` carry no
    pseudo operands and are returned as-is.
    Returns the updated state together with the rewritten instruction wrapped
    in a list (to keep a uniform return type with other passes that may expand
    one instruction into several). -/
private def replaceInstr (s : ReplState) : Instruction → ReplState × List Instruction
  | .Mov src dst =>
      let (s, src') := replaceOp s src
      let (s, dst') := replaceOp s dst
      (s, [.Mov src' dst'])
  | .Unary op operand =>
      let (s, op') := replaceOp s operand
      (s, [.Unary op op'])
  | .Binary op src dst =>
      let (s, src') := replaceOp s src
      let (s, dst') := replaceOp s dst
      (s, [.Binary op src' dst'])
  | .Idiv operand =>
      let (s, op') := replaceOp s operand
      (s, [.Idiv op'])
  | .Cmp src dst =>
      let (s, src') := replaceOp s src
      let (s, dst') := replaceOp s dst
      (s, [.Cmp src' dst'])
  | .SetCC cc operand =>
      let (s, op') := replaceOp s operand
      (s, [.SetCC cc op'])
  | .Push operand =>
      -- Chapter 9: Push may have a Pseudo operand; replace it.
      let (s, op') := replaceOp s operand
      (s, [.Push op'])
  | instr => (s, [instr])  -- Ret, Cdq, AllocateStack, DeallocateStack, Call, Jmp, etc.

/-- Replace pseudoregisters in a single function definition.
    Processes the instruction list with a fresh ReplState, then stores the
    resulting stack size in the FunctionDef.stackSize field. -/
private def replaceFunctionDef (f : FunctionDef) : FunctionDef :=
  let (finalState, instrs) :=
    f.instructions.foldl
      (fun (acc : ReplState × List Instruction) instr =>
        let (s, out) := acc
        let (s', new) := replaceInstr s instr
        (s', out ++ new))
      (ReplState.empty, [])
  { f with instructions := instrs, stackSize := finalState.maxBytes }

/-- Entry point for pass 2.
    Chapter 9: processes each function independently.
    Each function gets its own fresh pseudo map and stack byte count.
    The stack size is stored in `FunctionDef.stackSize` for pass 3 (FixUp). -/
def replacePseudos (p : Program) : Program :=
  { p with funcs := p.funcs.map replaceFunctionDef }

end AssemblyAST
