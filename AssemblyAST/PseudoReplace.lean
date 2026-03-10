import AssemblyAST.AssemblyAST
import Semantics.SymbolTable

/-
  Pass 2 of assembly generation: replace every Pseudo operand with a concrete
  operand — either a Stack slot or a Data (RIP-relative) operand.

  Chapter 9: each function processed independently with its own stack map.

  Chapter 10 additions:
    - Takes the global `SymbolTable` built by VarResolution.
    - When a Pseudo operand is encountered for the first time, we check the
      symbol table:
        - If the entry has `Static` attributes, it is a static variable; map
          it to `Data(name)` (RIP-relative address, no stack slot allocated).
        - Otherwise (Local attr or not found — TACKY temporaries are not in the
          symbol table), assign a new stack slot as before.
    - Static variables do NOT count toward the function's stack size.
    - `AsmTopLevel.StaticVariable` entries are passed through unchanged; they
      carry no instructions and need no pseudoregister replacement.
-/

namespace AssemblyAST

/-- Mutable state threaded through the pseudo-replacement pass for ONE function.
    `map` is an association list from pseudoregister name to its assigned stack
    offset or Data label.
    `maxBytes` tracks the total bytes of stack space allocated so far; the next
    stack slot will be at offset `-(maxBytes + 4)`. -/
private structure ReplState where
  /-- Map from pseudo name to the concrete operand it was assigned. -/
  map      : List (String × Operand)
  /-- Total stack bytes allocated so far (for Stack-assigned pseudos only). -/
  maxBytes : Nat

/-- The initial replacement state: no pseudoregisters mapped, nothing allocated. -/
private def ReplState.empty : ReplState := { map := [], maxBytes := 0 }

/-- Look up or assign a concrete operand for `id`.
    Consults the symbol table first:
      - Static attribute → map to `Data(id)` (no stack allocation).
      - Otherwise → assign next 4-byte stack slot.
    If `id` already has a mapping from a previous occurrence, return it directly. -/
private def ReplState.getOrInsert (s : ReplState) (id : String)
    (symTable : Semantics.SymbolTable) : ReplState × Operand :=
  -- Check if we already assigned an operand for this pseudo
  match s.map.find? (fun p => p.1 == id) with
  | some (_, op) => (s, op)
  | none =>
      -- Check the symbol table to determine storage duration
      let isStatic : Bool := match Semantics.lookupSym symTable id with
        | some { attrs := .Static _ _, .. } => true
        | _                                 => false
      if isStatic then
        -- Static variable: use RIP-relative Data operand, no stack space needed
        let op := Operand.Data id
        ({ s with map := s.map ++ [(id, op)] }, op)
      else
        -- Automatic variable or TACKY temporary: assign a 4-byte stack slot
        let bytes  := s.maxBytes + 4
        let offset : Int := -(bytes : Int)
        let op := Operand.Stack offset
        ({ map := s.map ++ [(id, op)], maxBytes := bytes }, op)

/-- Replace a single operand if it is a `Pseudo`.
    Non-pseudo operands are returned unchanged together with the unmodified state.
    Chapter 10: consults the symbol table to decide Stack vs. Data. -/
private def replaceOp (s : ReplState) (symTable : Semantics.SymbolTable) : Operand → ReplState × Operand
  | .Pseudo id => s.getOrInsert id symTable
  | op         => (s, op)

/-- Replace all `Pseudo` operands in a single instruction.
    Chapter 10: passes `symTable` to `replaceOp` for static vs. local decisions.
    All instruction shapes handled:
    - Two-operand: Mov, Binary, Cmp (both src and dst may be pseudo)
    - One-operand: Unary, Idiv, SetCC, Push
    - No operand: Ret, Cdq, AllocateStack, DeallocateStack, Call, Jmp, JmpCC, Label
    Returns the updated state plus the rewritten instruction list. -/
private def replaceInstr (s : ReplState) (symTable : Semantics.SymbolTable)
    : Instruction → ReplState × List Instruction
  | .Mov src dst =>
      let (s, src') := replaceOp s symTable src
      let (s, dst') := replaceOp s symTable dst
      (s, [.Mov src' dst'])
  | .Unary op operand =>
      let (s, op') := replaceOp s symTable operand
      (s, [.Unary op op'])
  | .Binary op src dst =>
      let (s, src') := replaceOp s symTable src
      let (s, dst') := replaceOp s symTable dst
      (s, [.Binary op src' dst'])
  | .Idiv operand =>
      let (s, op') := replaceOp s symTable operand
      (s, [.Idiv op'])
  | .Cmp src dst =>
      let (s, src') := replaceOp s symTable src
      let (s, dst') := replaceOp s symTable dst
      (s, [.Cmp src' dst'])
  | .SetCC cc operand =>
      let (s, op') := replaceOp s symTable operand
      (s, [.SetCC cc op'])
  | .Push operand =>
      -- Chapter 9: Push may have a Pseudo operand; replace it.
      let (s, op') := replaceOp s symTable operand
      (s, [.Push op'])
  | instr => (s, [instr])  -- Ret, Cdq, AllocateStack, DeallocateStack, Call, Jmp, etc.

/-- Replace pseudoregisters in a single function definition.
    Processes the instruction list with a fresh ReplState, then stores the
    resulting stack size (only from Stack-allocated pseudos) in stackSize. -/
private def replaceFunctionDef (f : FunctionDef) (symTable : Semantics.SymbolTable) : FunctionDef :=
  let (finalState, instrs) :=
    f.instructions.foldl
      (fun (acc : ReplState × List Instruction) instr =>
        let (s, out) := acc
        let (s', new) := replaceInstr s symTable instr
        (s', out ++ new))
      (ReplState.empty, [])
  { f with instructions := instrs, stackSize := finalState.maxBytes }

/-- Entry point for pass 2.
    Chapter 10: takes the global symbol table.
    - `AsmTopLevel.Function(fd)`: processes each function independently with a
      fresh pseudo map and stack byte count.
    - `AsmTopLevel.StaticVariable(...)`: passed through unchanged (no
      pseudoregisters in static variable definitions). -/
def replacePseudos (p : Program) (symTable : Semantics.SymbolTable) : Program :=
  let topLevels := p.topLevels.map fun tl =>
    match tl with
    | .Function fd           => AsmTopLevel.Function (replaceFunctionDef fd symTable)
    | sv@(.StaticVariable ..) => sv  -- no instructions, nothing to replace
  { topLevels }

end AssemblyAST
