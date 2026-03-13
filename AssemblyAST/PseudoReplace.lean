import AssemblyAST.AssemblyAST

/-
  Pass 2 of assembly generation: replace Pseudo operands with concrete operands.

  Chapter 13 changes:
    - `Double` AsmType → 8-byte stack slot, 8-byte aligned (same size as Quadword).
    - New instructions handled (operand replacement only — FixUp handles constraints):
        `Movsd(src, dst)`, `Xorpd(src, dst)`, `Comisd(src, dst)`
        `Cvtsi2sd(t, src, dst)`, `Cvttsd2si(t, src, dst)`
    - `StaticConstant` items pass through unchanged (like `StaticVariable`).

  Chapter 11 changes:
    - Now consults the `BackendSymTable` (instead of the frontend SymbolTable).
    - Stack slot size is determined by `AsmType`:
        `Longword` → 4 bytes, 4-byte aligned
        `Quadword` → 8 bytes, 8-byte aligned
    - Static variables are still mapped to `Data(name)` (RIP-relative).
    - `Movsx` instruction is handled (both src and dst may be pseudo).
    - `AllocateStack`/`DeallocateStack` no longer exist; `Binary(Quadword, Sub/Add, ...)`
      with `Reg(SP)` are passed through unchanged (no pseudo operands there).
-/

namespace AssemblyAST

/-- Mutable state threaded through pseudo-replacement for one function.
    `map`:      association list from pseudo name to its assigned concrete operand.
    `maxBytes`: total bytes of stack allocated so far (grows by 4 or 8 per slot). -/
private structure ReplState where
  map      : List (String × Operand)
  maxBytes : Nat

private def ReplState.empty : ReplState := { map := [], maxBytes := 0 }

/-- Round `n` up to a multiple of `align`. -/
private def alignUp (n : Nat) (align : Nat) : Nat :=
  ((n + align - 1) / align) * align

/-- Look up or assign a concrete operand for `id`.
    Consults the backend sym table:
      - `ObjEntry(_, _, true)` → static variable/constant → `Data(id)`.
      - `ObjEntry(Quadword, _, false)` → local long/ulong → next 8-byte stack slot.
      - `ObjEntry(Double, _, false)`   → local double → next 8-byte stack slot (Chapter 13).
      - Not found or `ObjEntry(Longword, ...)` → 4-byte slot. -/
private def ReplState.getOrInsert (s : ReplState) (id : String)
    (bst : BackendSymTable) : ReplState × Operand :=
  match s.map.find? (fun p => p.1 == id) with
  | some (_, op) => (s, op)
  | none =>
      match lookupBst bst id with
      | some (.ObjEntry _ _ true) =>
          -- Static variable or read-only constant: RIP-relative Data operand
          let op := Operand.Data id
          ({ s with map := s.map ++ [(id, op)] }, op)
      | some (.ObjEntry .Quadword _ false) | some (.ObjEntry .Double _ false) =>
          -- Local long/ulong/double (8-byte): align maxBytes to 8, then allocate 8 bytes
          let aligned := alignUp s.maxBytes 8
          let bytes   := aligned + 8
          let offset  : Int := -(bytes : Int)
          let op      := Operand.Stack offset
          ({ map := s.map ++ [(id, op)], maxBytes := bytes }, op)
      | _ =>
          -- Local int (4-byte) or unknown temporary: 4-byte slot
          let bytes  := s.maxBytes + 4
          let offset : Int := -(bytes : Int)
          let op     := Operand.Stack offset
          ({ map := s.map ++ [(id, op)], maxBytes := bytes }, op)

private def replaceOp (s : ReplState) (bst : BackendSymTable) : Operand → ReplState × Operand
  | .Pseudo id => s.getOrInsert id bst
  | op         => (s, op)

/-- Replace all Pseudo operands in a single instruction.
    Chapter 11: handles all typed instruction variants and Movsx.
    Chapter 13: handles Movsd, Cvtsi2sd, Cvttsd2si, Xorpd, Comisd. -/
private def replaceInstr (s : ReplState) (bst : BackendSymTable)
    : Instruction → ReplState × List Instruction
  | .Mov t src dst =>
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Mov t src' dst'])
  | .Movsd src dst =>
      -- Chapter 13: scalar double move; FixUp handles mem-to-mem constraint
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Movsd src' dst'])
  | .Movsx src dst =>
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Movsx src' dst'])
  | .MovZeroExtend src dst =>
      -- Chapter 12: zero-extend 32-bit uint to 64-bit (FixUp handles memory dst)
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.MovZeroExtend src' dst'])
  | .Unary t op operand =>
      let (s, op') := replaceOp s bst operand
      (s, [.Unary t op op'])
  | .Binary t op src dst =>
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Binary t op src' dst'])
  | .Idiv t operand =>
      let (s, op') := replaceOp s bst operand
      (s, [.Idiv t op'])
  | .Div t operand =>
      -- Chapter 12: unsigned division (same pseudo-replacement logic as Idiv)
      let (s, op') := replaceOp s bst operand
      (s, [.Div t op'])
  | .Cmp t src dst =>
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Cmp t src' dst'])
  | .SetCC cc operand =>
      let (s, op') := replaceOp s bst operand
      (s, [.SetCC cc op'])
  | .Push operand =>
      let (s, op') := replaceOp s bst operand
      (s, [.Push op'])
  -- Chapter 13: floating-point instructions -------------------------
  | .Cvtsi2sd t src dst =>
      -- Convert integer to double; FixUp handles mem dst constraint
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Cvtsi2sd t src' dst'])
  | .Cvttsd2si t src dst =>
      -- Truncate double to integer; FixUp handles mem dst constraint
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Cvttsd2si t src' dst'])
  | .Xorpd src dst =>
      -- XOR packed doubles (double negation); FixUp handles mem-to-mem
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Xorpd src' dst'])
  | .Comisd src dst =>
      -- Compare doubles; FixUp handles mem-to-mem (src must be reg or mem, dst must be reg)
      let (s, src') := replaceOp s bst src
      let (s, dst') := replaceOp s bst dst
      (s, [.Comisd src' dst'])
  | instr => (s, [instr])  -- Ret, Cdq, Jmp, JmpCC, Label, Call pass through

/-- Replace pseudoregisters in a single function definition. -/
private def replaceFunctionDef (f : FunctionDef) (bst : BackendSymTable) : FunctionDef :=
  let (finalState, instrs) :=
    f.instructions.foldl
      (fun (acc : ReplState × List Instruction) instr =>
        let (s, out) := acc
        let (s', new) := replaceInstr s bst instr
        (s', out ++ new))
      (ReplState.empty, [])
  { f with instructions := instrs, stackSize := finalState.maxBytes }

/-- Entry point for pass 2.
    Processes each `AsmTopLevel.Function`.
    `StaticVariable` and `StaticConstant` items pass through unchanged. -/
def replacePseudos (p : Program) (bst : BackendSymTable) : Program :=
  let topLevels := p.topLevels.map fun tl =>
    match tl with
    | .Function fd              => AsmTopLevel.Function (replaceFunctionDef fd bst)
    | sv@(.StaticVariable ..)   => sv
    | sc@(.StaticConstant ..)   => sc   -- Chapter 13: read-only float constants pass through
  { topLevels }

end AssemblyAST
