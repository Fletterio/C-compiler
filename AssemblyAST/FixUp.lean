import AssemblyAST.AssemblyAST

/-
  Pass 3 of assembly generation: fix invalid instruction encodings.

  Chapter 13 additions:
    - `Movsd(src, dst)`: one operand must be an XMM register (no mem-to-mem).
        Both memory → `Movsd(src, XMM14); Movsd(XMM14, dst)`.
    - `Cvtsi2sd(t, src, dst)`: dst must be an XMM register.
        dst is memory → `Cvtsi2sd(t, src, XMM14); Movsd(XMM14, dst)`.
    - `Cvttsd2si(t, src, dst)`: dst must be an integer register.
        dst is memory → `Cvttsd2si(t, src, R11); Mov(t, R11, dst)`.
    - `Xorpd(src, dst)`: dst must be an XMM register; src can be XMM or m128.
        dst is memory → `Movsd(dst, XMM14); Xorpd(src, XMM14); Movsd(XMM14, dst)`.
    - `Comisd(src, dst)`: dst must be an XMM register; src can be XMM or m64.
        dst is memory → `Movsd(dst, XMM14); Comisd(src, XMM14)`.
    - `StaticConstant` passes through unchanged.
    - XMM14 serves as the XMM scratch register (analogous to R10/R11 for integers).

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

  R10  is the scratch integer register for source fix-ups.
  R11  is the scratch integer register for destination fix-ups.
  XMM14 is the scratch XMM register for double fix-ups.
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
  -- Div (unsigned): same constraint as Idiv — operand cannot be an immediate
  -- ----------------------------------------------------------------
  | .Div t (.Imm n) =>
      [.Mov t (.Imm n) (.Reg .R10), .Div t (.Reg .R10)]
  -- ----------------------------------------------------------------
  -- MovZeroExtend: zero-extend 32-bit uint to 64-bit (Chapter 12)
  --   If dst is memory, we can't movl directly (only 4 bytes written).
  --   Fix: movl src, R11d (zero-extends R11 to 64 bits), then movq R11, dst.
  --   If dst is a register, movl to the 32-bit register naturally zero-extends.
  -- ----------------------------------------------------------------
  | .MovZeroExtend src dst =>
      if isMem dst then
        [.Mov .Longword src (.Reg .R11),
         .Mov .Quadword (.Reg .R11) dst]
      else
        [.MovZeroExtend src dst]
  -- ----------------------------------------------------------------
  -- Binary: mem-to-mem, large Quadword immediate, Mult mem-dst
  -- Chapter 13: Double binary ops (addsd/subsd/mulsd/divsd) require
  -- XMM registers; dst cannot be memory. Route through XMM14 if needed.
  -- ----------------------------------------------------------------
  | .Binary t op src dst =>
      if t == .Double then
        -- Double arithmetic: dst must be an XMM register.
        -- If dst is memory, load into XMM14, operate, store back.
        -- src can be XMM or m64, so memory src is fine after fixing dst.
        if isMem dst then
          [.Movsd dst (.Reg .XMM14),
           .Binary .Double op src (.Reg .XMM14),
           .Movsd (.Reg .XMM14) dst]
        else
          [.Binary .Double op src dst]
      else
        -- Integer binary ops
        -- Large immediate in a Quadword Binary: move to R10 first
        let (src', extraInstrs) : Operand × List Instruction :=
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
               .Binary t .Mult src' (.Reg .R11),
               .Mov t (.Reg .R11) dst]
            else
              extraInstrs ++ [.Binary t .Mult src' dst]
        | _ =>
            -- Add/Sub/And/Or/Xor/Sal/Sar/Shr: cannot use two memory operands
            if isMem src' && isMem dst then
              extraInstrs ++
              [.Mov t src' (.Reg .R10), .Binary t op (.Reg .R10) dst]
            else
              extraInstrs ++ [.Binary t op src' dst]
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
  -- ----------------------------------------------------------------
  -- Chapter 13: Movsd — one operand must be an XMM register
  --   Both memory → route through XMM14
  -- ----------------------------------------------------------------
  | .Movsd src dst =>
      if isMem src && isMem dst then
        [.Movsd src (.Reg .XMM14), .Movsd (.Reg .XMM14) dst]
      else
        [.Movsd src dst]
  -- ----------------------------------------------------------------
  -- Chapter 13: Cvtsi2sd — dst must be an XMM register; src cannot be an immediate
  --   src is Imm     → load into R10 (integer register) first
  --   dst is memory  → convert to XMM14, then store
  -- ----------------------------------------------------------------
  | .Cvtsi2sd t src dst =>
      -- Step 1: fix immediate source (cvtsi2sd cannot encode an immediate operand)
      let (src', srcPre) : Operand × List Instruction :=
        match src with
        | .Imm _ => (.Reg .R10, [.Mov t src (.Reg .R10)])
        | _      => (src, [])
      -- Step 2: fix memory destination
      if isMem dst then
        srcPre ++ [.Cvtsi2sd t src' (.Reg .XMM14), .Movsd (.Reg .XMM14) dst]
      else
        srcPre ++ [.Cvtsi2sd t src' dst]
  -- ----------------------------------------------------------------
  -- Chapter 13: Cvttsd2si — dst must be an integer register
  --   dst is memory → convert to R11, then store
  -- ----------------------------------------------------------------
  | .Cvttsd2si t src dst =>
      if isMem dst then
        [.Cvttsd2si t src (.Reg .R11), .Mov t (.Reg .R11) dst]
      else
        [.Cvttsd2si t src dst]
  -- ----------------------------------------------------------------
  -- Chapter 13: Xorpd — dst must be an XMM register; src is XMM (neg-zero reg)
  --   dst is memory → load dst into XMM14, xorpd, then store back
  -- ----------------------------------------------------------------
  | .Xorpd src dst =>
      if isMem dst then
        [.Movsd dst (.Reg .XMM14),
         .Xorpd src (.Reg .XMM14),
         .Movsd (.Reg .XMM14) dst]
      else
        [.Xorpd src dst]
  -- ----------------------------------------------------------------
  -- Chapter 13: Comisd — dst must be an XMM register; src can be XMM or m64
  --   dst is memory → load dst into XMM14 first
  -- ----------------------------------------------------------------
  | .Comisd src dst =>
      if isMem dst then
        [.Movsd dst (.Reg .XMM14), .Comisd src (.Reg .XMM14)]
      else
        [.Comisd src dst]
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

/-- Entry point for pass 3.
    `StaticVariable` and `StaticConstant` pass through unchanged. -/
def fixUp (p : Program) : Program :=
  let topLevels := p.topLevels.map fun tl =>
    match tl with
    | .Function fd            => AsmTopLevel.Function (fixFunctionDef fd)
    | sv@(.StaticVariable ..) => sv
    | sc@(.StaticConstant ..) => sc   -- Chapter 13: read-only constants pass through
  { topLevels }

end AssemblyAST
