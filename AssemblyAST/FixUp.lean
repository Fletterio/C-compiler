import AssemblyAST.AssemblyAST

/-
  Pass 3 of assembly generation: fix invalid instruction encodings.

  Chapter 11 changes:
    - All instructions now carry `AsmType`; fix-up rules apply to each typed variant.
    - Stack-frame allocation is now `Binary(Quadword, Sub, Imm(n), Reg(SP))` rather
      than the removed `AllocateStack`; FixUp still inserts this instruction.
    - `Movsx` fix-ups:
        a. Source is `Imm`: load into R10 (Longword) first, then Movsx.
        b. Destination is memory (Stack/Data): Movsx to R11, then Mov(Quadword) to mem.
    - Large immediate fix-ups (Quadword instructions only):
        `Binary(Quadword, op, Imm(n), dst)` where n doesn't fit in int32:
          → `Mov(Quadword, Imm(n), Reg(R10))`, `Binary(Quadword, op, Reg(R10), dst)`
        `Cmp(Quadword, Imm(n), dst)` with large n:
          → `Mov(Quadword, Imm(n), Reg(R10))`, `Cmp(Quadword, Reg(R10), dst)`
        `Mov(Quadword, Imm(n), dst)` with n not fitting in int32 AND dst is memory:
          → `Mov(Quadword, Imm(n), Reg(R10))`, `Mov(Quadword, Reg(R10), dst)`
          (GAS accepts `movq $large, %reg` as `movabsq` when targeting a register,
           but not for memory destinations.)
    - mem-to-mem fix-ups now check both `Stack` and `Data` as memory operands.
    - `Binary(Quadword, Mult, src, mem)`: must go through R11.

  R10 is the scratch register for source fix-ups.
  R11 is the scratch register for destination fix-ups.
-/

namespace AssemblyAST

private def roundUp16 (n : Int) : Int :=
  ((n + 15) / 16) * 16

private def isMem : Operand → Bool
  | .Stack _ => true
  | .Data _  => true
  | _        => false

/-- True if `n` fits in a signed 32-bit integer. -/
private def fitsInInt32 (n : Int) : Bool :=
  n >= -2147483648 && n <= 2147483647

/-- Rewrite a single instruction to fix invalid encodings.
    Returns a list (usually singleton; multi-element when a split is needed). -/
private def fixInstr : Instruction → List Instruction
  -- ----------------------------------------------------------------
  -- Mov: mem-to-mem split; large Quadword immediate to memory
  -- ----------------------------------------------------------------
  | .Mov t src dst =>
      -- Large quadword immediate to memory: must go through R10
      if t == .Quadword then
        match src, dst with
        | .Imm n, _ =>
            if !fitsInInt32 n && isMem dst then
              [.Mov .Quadword (.Imm n) (.Reg .R10),
               .Mov .Quadword (.Reg .R10) dst]
            else if isMem src && isMem dst then
              [.Mov t src (.Reg .R10), .Mov t (.Reg .R10) dst]
            else
              [.Mov t src dst]
        | _, _ =>
            if isMem src && isMem dst then
              [.Mov t src (.Reg .R10), .Mov t (.Reg .R10) dst]
            else
              [.Mov t src dst]
      else
        -- Longword: just mem-to-mem split
        if isMem src && isMem dst then
          [.Mov t src (.Reg .R10), .Mov t (.Reg .R10) dst]
        else
          [.Mov t src dst]
  -- ----------------------------------------------------------------
  -- Movsx: sign-extend int to long
  --   Invalid: Imm source, or memory destination
  -- ----------------------------------------------------------------
  | .Movsx src dst =>
      match src, dst with
      | .Imm _, _ =>
          -- Load Imm into R10 (as 32-bit), then sign-extend to dst
          if isMem dst then
            [.Mov .Longword src (.Reg .R10),
             .Movsx (.Reg .R10) (.Reg .R11),
             .Mov .Quadword (.Reg .R11) dst]
          else
            [.Mov .Longword src (.Reg .R10),
             .Movsx (.Reg .R10) dst]
      | _, _ =>
          if isMem dst then
            -- Memory destination: go through R11
            [.Movsx src (.Reg .R11),
             .Mov .Quadword (.Reg .R11) dst]
          else
            [.Movsx src dst]
  -- ----------------------------------------------------------------
  -- Idiv: operand cannot be an immediate
  -- ----------------------------------------------------------------
  | .Idiv t (.Imm n) =>
      [.Mov t (.Imm n) (.Reg .R10), .Idiv t (.Reg .R10)]
  -- ----------------------------------------------------------------
  -- Binary: mem-to-mem, large Quadword immediate, Mult mem-dst
  -- ----------------------------------------------------------------
  | .Binary t op src dst =>
      -- Large immediate in a Quadword Binary: move to R10 first
      let (src, extraInstrs) : Operand × List Instruction :=
        match src with
        | .Imm n =>
            if t == .Quadword && !fitsInInt32 n then
              (.Reg .R10, [.Mov .Quadword (.Imm n) (.Reg .R10)])
            else
              (src, [])
        | _ => (src, [])
      match op with
      | .Mult =>
          -- imulq cannot use a memory destination
          if isMem dst then
            extraInstrs ++
            [.Mov t dst (.Reg .R11),
             .Binary t .Mult src (.Reg .R11),
             .Mov t (.Reg .R11) dst]
          else
            extraInstrs ++ [.Binary t .Mult src dst]
      | _ =>
          -- Add/Sub/And/Or/Xor/Sal/Sar: cannot use two memory operands
          if isMem src && isMem dst then
            extraInstrs ++
            [.Mov t src (.Reg .R10), .Binary t op (.Reg .R10) dst]
          else
            extraInstrs ++ [.Binary t op src dst]
  -- ----------------------------------------------------------------
  -- Cmp: multiple constraints must all be fixed in one pass
  --   1. dst (AT&T second operand) cannot be an Imm  → move to R11
  --   2. src Imm that doesn't fit in int32 (Quadword) → move to R10
  --   3. Both src and dst cannot be memory (stack/data)
  --
  -- We fix all three in one pass because fixInstr results are NOT
  -- re-processed, so a partial fix that leaves a large-immediate src
  -- would survive to the assembler.
  -- ----------------------------------------------------------------
  | .Cmp t src dst =>
      -- Step 1: fix src large-immediate into R10 if needed
      let (src', srcPre) : Operand × List Instruction :=
        match src with
        | .Imm n =>
            if t == .Quadword && !fitsInInt32 n then
              (.Reg .R10, [.Mov .Quadword (.Imm n) (.Reg .R10)])
            else
              (src, [])
        | _ => (src, [])
      -- Step 2: fix dst Imm into R11 (cmp dst cannot be any immediate)
      let (dst', dstPre) : Operand × List Instruction :=
        match dst with
        | .Imm n =>
            if t == .Quadword && !fitsInInt32 n then
              (.Reg .R11, [.Mov .Quadword (.Imm n) (.Reg .R11)])
            else
              (.Reg .R11, [.Mov t (.Imm n) (.Reg .R11)])
        | _ => (dst, [])
      -- Step 3: fix mem-to-mem (after the above may have changed src')
      let finalInstrs :=
        if isMem src' && isMem dst' then
          [.Mov t src' (.Reg .R10), .Cmp t (.Reg .R10) dst']
        else
          [.Cmp t src' dst']
      srcPre ++ dstPre ++ finalInstrs
  -- ----------------------------------------------------------------
  -- Push: immediate larger than int32 is illegal for pushq
  --   pushq $large  → movq $large, %r10; pushq %r10
  -- ----------------------------------------------------------------
  | .Push (.Imm n) =>
      if !fitsInInt32 n then
        [.Mov .Quadword (.Imm n) (.Reg .R10), .Push (.Reg .R10)]
      else
        [.Push (.Imm n)]
  -- All other instructions need no fix-up
  | instr => [instr]

/-- Fix up a single function definition.
    Inserts the stack-frame allocation instruction at the top:
      `Binary(Quadword, Sub, Imm(rounded), Reg(SP))`
    (replaces the former `AllocateStack`). -/
private def fixFunctionDef (f : FunctionDef) : FunctionDef :=
  let rounded := roundUp16 f.stackSize
  let fixed := f.instructions.foldl (fun acc i => acc ++ fixInstr i) []
  -- Prepend subq $n, %rsp to allocate the stack frame
  let allocInstr := Instruction.Binary .Quadword .Sub (.Imm rounded) (.Reg .SP)
  { f with instructions := allocInstr :: fixed }

/-- Entry point for pass 3. -/
def fixUp (p : Program) : Program :=
  let topLevels := p.topLevels.map fun tl =>
    match tl with
    | .Function fd            => AsmTopLevel.Function (fixFunctionDef fd)
    | sv@(.StaticVariable ..) => sv
  { topLevels }

end AssemblyAST
