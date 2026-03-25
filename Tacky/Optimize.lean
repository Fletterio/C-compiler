import Tacky.Tacky
import AST.AST

/-
  Chapter 19: TACKY optimization passes.

  Currently implemented:
    1. Constant Folding (`--fold-constants`)
       - Folds Unary/Binary/JumpIfZero/JumpIfNotZero/type-conversion instructions
         whose operands are all known compile-time constants (integer or double).
       - Maintains a within-pass "constant map" so that folded Copy(Constant, Var x)
         assignments are propagated to subsequent instructions that use Var x as a source,
         enabling chains like `DoubleToInt → Truncate` to fully fold in a single pass.
       - Double constants are represented as Val.Var ".LfpC.N" (static labels); the
         optimizer interns newly-folded double results as Val.Var ".LfpO.N" (optimizer
         labels) and records them in floatConsts / typeEnv for the Driver.
       - Division by zero and out-of-range shifts are NOT folded (undefined behavior).
       - Double → integer conversions that are out of range are NOT folded (UB).
       - Repeats until the body reaches a fixed point (no change between passes).

  Stubs (to be implemented in later chapters):
    2. Unreachable Code Elimination (`--eliminate-unreachable-code`)
    3. Copy Propagation          (`--propagate-copies`)
    4. Dead Store Elimination    (`--eliminate-dead-stores`)

  CLI flag `--optimize` enables all four passes.
-/

namespace Tacky

-- ---------------------------------------------------------------------------
-- Optimization flags
-- ---------------------------------------------------------------------------

/-- Controls which TACKY optimization passes are enabled. -/
structure OptFlags where
  foldConstants        : Bool := false
  eliminateUnreachable : Bool := false
  propagateCopies      : Bool := false
  eliminateDeadStores  : Bool := false
  deriving Repr, BEq

-- ---------------------------------------------------------------------------
-- Integer wrapping helpers (two's-complement ranges)
-- ---------------------------------------------------------------------------

/-- Wrap to signed 8-bit range [-128, 127]. -/
private def wrapInt8 (n : Int) : Int :=
  let m : Int := 256
  let r := ((n % m) + m) % m
  if r >= 128 then r - m else r

/-- Wrap to unsigned 8-bit range [0, 255]. -/
private def wrapUInt8 (n : Int) : Int :=
  let m : Int := 256
  ((n % m) + m) % m

/-- Wrap to signed 32-bit range [-2^31, 2^31-1]. -/
private def wrapInt32 (n : Int) : Int :=
  let m : Int := 4294967296
  let r := ((n % m) + m) % m
  if r >= 2147483648 then r - m else r

/-- Wrap to unsigned 32-bit range [0, 2^32-1]. -/
private def wrapUInt32 (n : Int) : Int :=
  let m : Int := 4294967296
  ((n % m) + m) % m

/-- Wrap to signed 64-bit range [-2^63, 2^63-1]. -/
private def wrapInt64 (n : Int) : Int :=
  let m : Int := 18446744073709551616
  let r := ((n % m) + m) % m
  if r >= 9223372036854775808 then r - m else r

/-- Wrap to unsigned 64-bit range [0, 2^64-1]. -/
private def wrapUInt64 (n : Int) : Int :=
  let m : Int := 18446744073709551616
  ((n % m) + m) % m

/-- Wrap an integer to the canonical range for the given AST type. -/
private def wrapForType : AST.Typ → Int → Int
  | .Int           => wrapInt32
  | .UInt          => wrapUInt32
  | .Long          => wrapInt64
  | .ULong         => wrapUInt64
  | .Char | .SChar => wrapInt8
  | .UChar         => wrapUInt8
  | _              => id   -- Double, Pointer, Struct, etc. — not integer scalars

-- ---------------------------------------------------------------------------
-- Integer arithmetic helpers (C semantics)
-- ---------------------------------------------------------------------------

/-- Truncation division (toward zero), matching C's `/` for signed integers.
    For non-negative operands this matches Lean's default `Int` division. -/
private def tdiv (a b : Int) : Int :=
  let absA := if a < 0 then -a else a
  let absB := if b < 0 then -b else b
  let q : Int := absA / absB
  if (a < 0) != (b < 0) then -q else q

/-- Truncation remainder (C-style `%` semantics): sign matches dividend `a`. -/
private def tmod (a b : Int) : Int := a - b * tdiv a b

/-- Arithmetic (signed) right shift: equivalent to floor division by 2^shift. -/
private def arithmeticShiftRight (n : Int) (shift : Nat) : Int :=
  if shift == 0 then n
  else
    let d : Int := (2 : Int) ^ shift
    let q := tdiv n d
    if n < 0 && tmod n d != 0 then q - 1 else q

-- ---------------------------------------------------------------------------
-- Bitwise operations on Int (using Nat as the bit-level substrate)
-- ---------------------------------------------------------------------------

/-- Convert a signed integer `n` of `bits` width to its two's-complement
    Nat representation (always in [0, 2^bits - 1]). -/
private def toUNat (bits : Nat) (n : Int) : Nat :=
  (match bits with
   | 8  => wrapUInt8  n
   | 32 => wrapUInt32 n
   | _  => wrapUInt64 n).toNat   -- Int.toNat is 0 for negative, identity for non-negative;
                                  -- wrapUIntN always returns non-negative, so this is safe.

/-- Bitwise AND of two integer values, at the given two's-complement `bits` width.
    Result is a non-negative Int in [0, 2^bits - 1] (unsigned representation).
    We route through UInt64 since that has well-defined bitwise operators. -/
private def intBitAnd (bits : Nat) (a b : Int) : Int :=
  let a64 : UInt64 := (toUNat bits a).toUInt64
  let b64 : UInt64 := (toUNat bits b).toUInt64
  Int.ofNat (a64 &&& b64).toNat

/-- Bitwise OR of two integer values (same convention as intBitAnd). -/
private def intBitOr (bits : Nat) (a b : Int) : Int :=
  let a64 : UInt64 := (toUNat bits a).toUInt64
  let b64 : UInt64 := (toUNat bits b).toUInt64
  Int.ofNat (a64 ||| b64).toNat

/-- Bitwise XOR of two integer values (same convention as intBitAnd). -/
private def intBitXor (bits : Nat) (a b : Int) : Int :=
  let a64 : UInt64 := (toUNat bits a).toUInt64
  let b64 : UInt64 := (toUNat bits b).toUInt64
  Int.ofNat (a64 ^^^ b64).toNat

-- ---------------------------------------------------------------------------
-- Constant folding state
-- ---------------------------------------------------------------------------

/-- State threaded through the constant folding pass for one function body.

    `typeEnv`     — maps every variable name to its AST type; used to determine the
                    wrapping width for Truncate, Binary, etc.
    `floatConsts` — maps static float-constant labels (`.LfpC.N`, `.LfpO.N`) to their
                    Float values; used to recognise double constants in Val.Var form.
    `counter`     — allocates new optimizer float labels `.LfpO.K`.
    `constVarMap` — within-pass constant map: after folding to Copy(constVal, Var x),
                    records x → constVal so subsequent instructions reading Var x can
                    substitute the constant directly (enabling fold chains like
                    DoubleToInt → Truncate to fully fold in a single pass).
                    Cleared at every Label instruction (conservative: labels are potential
                    jump targets whose predecessors we don't track). -/
private structure FoldState where
  typeEnv     : List (String × AST.Typ)
  floatConsts : List (String × Float)
  counter     : Nat
  constVarMap : List (String × Val)

private abbrev FoldM := StateM FoldState

-- ---------------------------------------------------------------------------
-- FoldM helpers
-- ---------------------------------------------------------------------------

/-- Look up the AST type for the destination Val. -/
private def dstTyp (dst : Val) : FoldM (Option AST.Typ) := do
  match dst with
  | .Var name =>
      let st ← get
      return st.typeEnv.findSome? fun (n, t) => if n == name then some t else none
  | _ => return none

/-- Look up a Float value for a Val:
    - If v = Var lbl and lbl is a float const label: return its Float.
    - If v = Var x and x maps to Var lbl in constVarMap, and lbl is a float const: return it.
    - Otherwise: none. -/
private def lookupFloat (v : Val) : FoldM (Option Float) := do
  let st ← get
  let findFloat (lbl : String) : Option Float :=
    st.floatConsts.findSome? fun (n, f) => if n == lbl then some f else none
  match v with
  | .Var name =>
      -- Direct: is name a float const label?
      match findFloat name with
      | some f => return some f
      | none   =>
          -- Indirect: does constVarMap say name → some float label?
          let mapped := st.constVarMap.findSome? fun (n, cv) =>
            if n == name then some cv else none
          match mapped with
          | some mappedVal =>
              match mappedVal with
              | .Var lbl => return findFloat lbl
              | _        => return none
          | none => return none
  | _ => return none

/-- Substitute constants for a Val using constVarMap. -/
private def substVal (v : Val) : FoldM Val := do
  match v with
  | .Var name =>
      let st ← get
      match st.constVarMap.findSome? fun (n, cv) => if n == name then some cv else none with
      | some cv => return cv
      | none    => return v
  | _ => return v

/-- Invalidate a destination variable in constVarMap (it has been overwritten). -/
private def invalidateDst (dst : Val) : FoldM Unit :=
  match dst with
  | .Var name =>
      modify fun st => { st with constVarMap := st.constVarMap.filter fun (n, _) => n != name }
  | _ => pure ()

/-- Record that `dst` (a Val.Var) has been assigned `src` as a constant value.
    Only records if `src` is a compile-time constant (Val.Constant or a float const label).
    If `src` is not a known constant, removes `dst` from the map instead.

    Crucially, when `src` is a Val.Constant, the integer is wrapped to the destination
    variable's type before being stored.  Without this, a same-size reinterpret cast
    (e.g. UInt 4294967196 → Int) would leave the raw unsigned bit pattern in the map,
    causing subsequent equality comparisons to use 4294967196 ≠ -100 even though the
    two values are identical in two's-complement. -/
private def recordConst (dst : Val) (src : Val) : FoldM Unit := do
  match dst with
  | .Var dstName =>
      let st ← get
      -- Produce the canonical constant to store (if src is trackable), or none.
      let trackableSrc : Option Val := match src with
        | .Constant n =>
            -- Wrap `n` to the declared type of `dstName` so that subsequent uses
            -- of this tracked constant compare with the correctly-typed value.
            -- Example: Constant(4294967196) for an Int var → Constant(-100).
            let tOpt := st.typeEnv.findSome? fun (nm, t) => if nm == dstName then some t else none
            let wrapped := match tOpt with | some t => wrapForType t n | none => n
            some (.Constant wrapped)
        | .Var lbl =>
            -- Float const labels are trackable as-is.
            if st.floatConsts.any fun (nm, _) => nm == lbl then some src
            else
              -- Transitive tracking: if `lbl` is already known to be a
              -- constant (or float-const label) in constVarMap, propagate
              -- that constant to `dstName` as well.
              -- This handles chains like `Copy(3, a); Copy(a, b)` — we
              -- track `b → 3` even when we don't substitute in Copy sources.
              match st.constVarMap.findSome? fun (n, cv) =>
                    if n == lbl then some cv else none with
              | some (Val.Constant n) =>
                  -- Wrap to dst's declared type
                  let tOpt := st.typeEnv.findSome? fun (nm, t) =>
                    if nm == dstName then some t else none
                  some (Val.Constant (match tOpt with | some t => wrapForType t n | none => n))
              | some floatLbl => some floatLbl   -- float-const label; keep as-is
              | none          => none
      match trackableSrc with
      | some wrappedSrc =>
          modify fun s =>
            { s with constVarMap :=
                (dstName, wrappedSrc) :: s.constVarMap.filter fun (nm, _) => nm != dstName }
      | none =>
          -- Not a constant: remove any stale entry so stale facts don't survive
          modify fun s =>
            { s with constVarMap := s.constVarMap.filter fun (nm, _) => nm != dstName }
  | _ => pure ()

/-- Intern a new float constant produced by the optimizer.
    Uses the `.LfpO.` prefix to avoid collisions with TackyGen's `.LfpC.N` labels.
    NaN deduplication: all NaN values share a single label (they have the same bit pattern
    on x86 and IEEE 754 does not distinguish between NaN payloads here), so
    `0.0/0.0` computed at two different call sites gets a single `.LfpO.N` label. -/
private def internFoldedFloat (f : Float) : FoldM Val := do
  let st ← get
  -- For NaN: reuse any existing NaN label (all NaNs are the same canonical bit pattern
  -- for our purposes, so 0.0/0.0 at two call sites gets one label).
  -- For non-NaN: match by exact IEEE 754 bit pattern (NOT by == equality) so that
  -- 0.0 (bits=0x0000…0000) and -0.0 (bits=0x8000…0000) are treated as distinct.
  -- Using `==` would collapse them because IEEE 754 defines 0.0 == -0.0.
  let existing := st.floatConsts.findSome? fun (nm, fv) =>
    if f.isNaN && fv.isNaN then some nm
    else if !f.isNaN && !fv.isNaN && f.toBits == fv.toBits then some nm
    else none
  match existing with
  | some lbl => return .Var lbl
  | none =>
      let label := s!".LfpO.{st.counter}"
      set { st with
        counter     := st.counter + 1
        typeEnv     := (label, .Double) :: st.typeEnv
        floatConsts := (label, f) :: st.floatConsts }
      return .Var label

-- ---------------------------------------------------------------------------
-- Instruction substitution
-- ---------------------------------------------------------------------------

/-- Substitute known-constant Vals for source variables using constVarMap.
    Only substitutes in instructions where:
      (a) We will try to fold the instruction (enabling fold chains), OR
      (b) CodeGen determines the instruction width from the DESTINATION (not the source),
          so losing the source's type is harmless.
    We deliberately do NOT substitute in:
      • Pointer/address operands (Load ptr, Store ptr, GetAddress src, AddPtr ptr):
        substituting a constant for a pointer variable would produce wrong or crashing code.
      • CopyToOffset src / Store src: CodeGen uses valAsmType(src) to pick the instruction
        width; substituting a constant loses the type (e.g. Long → Longword) and emits
        a narrower store (movl instead of movq) for struct members.
      • FunCall args / AddPtr idx: arg passing uses valAsmType to select the register size;
        same type-loss problem. -/
private def substInstr (instr : Instruction) : FoldM Instruction := do
  match instr with
  -- Instructions we fold (or whose CodeGen is safe w.r.t. constant type):
  | .Unary op src dst          => return .Unary op (← substVal src) dst
  | .Binary op s1 s2 dst       => return .Binary op (← substVal s1) (← substVal s2) dst
  -- Do NOT substitute in Copy sources via constVarMap: substituting
  -- Var → Constant here would destroy the variable-to-variable copy
  -- relationship that copy propagation needs to detect (e.g. x = y on
  -- all paths, even when y's concrete value differs per path).
  -- Instead, `recordConst` handles transitive constant tracking so that
  -- later arithmetic/comparison instructions still see the folded constant.
  | .Copy src dst              => return .Copy src dst
  | .JumpIfZero v t            => return .JumpIfZero (← substVal v) t
  | .JumpIfNotZero v t         => return .JumpIfNotZero (← substVal v) t
  | .SignExtend ty src dst     => return .SignExtend ty (← substVal src) dst
  | .ZeroExtend ty src dst     => return .ZeroExtend ty (← substVal src) dst
  | .Truncate src dst          => return .Truncate (← substVal src) dst
  | .IntToDouble src dst       => return .IntToDouble (← substVal src) dst
  | .DoubleToInt src dst       => return .DoubleToInt (← substVal src) dst
  | .UIntToDouble src dst      => return .UIntToDouble (← substVal src) dst
  | .DoubleToUInt src dst      => return .DoubleToUInt (← substVal src) dst
  | .ULongToDouble src dst     => return .ULongToDouble (← substVal src) dst
  | .DoubleToULong src dst     => return .DoubleToULong (← substVal src) dst
  -- Return: substitute constants.  CodeGen now uses funRetAsmType (not valAsmType)
  -- when the return value is a Val.Constant, so the instruction size is correct.
  | .Return (some v)           => return .Return (some (← substVal v))
  | .Return none               => return .Return none
  -- Instructions where substitution is UNSAFE (type-loss causes wrong instruction width):
  | .Load ptr dst              => return .Load ptr dst        -- ptr is an address
  | .Store src ptr             => return instr                -- src width from valAsmType is wrong
  | .GetAddress src dst        => return .GetAddress src dst  -- src is being addressed, not read
  | .CopyToOffset src dn off   => return instr                -- src width from valAsmType is wrong
  | .FunCall fn args dst       => return instr                -- arg widths from valAsmType wrong
  | .AddPtr ptr idx sc dst     => return instr                -- ptr is address; idx width wrong
  | _                          => return instr   -- Jump, Label, Return none, CopyFromOffset, etc.

-- ---------------------------------------------------------------------------
-- Core fold: try to constant-fold a single (already-substituted) instruction
-- ---------------------------------------------------------------------------

/-- Try to constant-fold a single instruction whose operands have already been
    substituted from constVarMap.
    Returns `some replacements` if folding succeeded; `none` if not.
    An empty replacement list means the instruction is dead (e.g. a conditional
    jump that is never taken). -/
private def foldOne (instr : Instruction) : FoldM (Option (List Instruction)) := do
  match instr with

  -- ── Integer Unary ────────────────────────────────────────────────────────
  | .Unary op (.Constant n) dst =>
      let tOpt ← dstTyp dst
      let rOpt : Option Int := match op with
        | .Complement => some (-1 - n)   -- two's-complement NOT = -(n+1)
        | .Negate     => some (-n)
        | .Not        => some (if n == 0 then 1 else 0)
      match rOpt with
      | none   => return none
      | some r =>
          let w := match tOpt with | some t => wrapForType t r | none => r
          return some [.Copy (.Constant w) dst]

  -- ── Double Unary ─────────────────────────────────────────────────────────
  | .Unary op src dst =>
      let fOpt ← lookupFloat src
      match fOpt with
      | none   => return none
      | some f =>
          match op with
          | .Negate =>
              let v ← internFoldedFloat (-f)
              return some [.Copy v dst]
          | .Not =>
              -- IEEE 754: -0.0 == 0.0, so both are "zero" (falsy)
              return some [.Copy (.Constant (if f == 0.0 then 1 else 0)) dst]
          | .Complement => return none   -- bitwise NOT undefined for Double

  -- ── Integer Binary ───────────────────────────────────────────────────────
  | .Binary op (.Constant a) (.Constant b) dst =>
      let tOpt ← dstTyp dst
      let unsigned : Bool :=
        match tOpt with
        | some (.UInt) | some (.ULong) | some (.UChar) => true
        | _ => false
      let bits : Nat :=
        match tOpt with
        | some (.Long) | some (.ULong) => 64
        | some (.Char) | some (.SChar) | some (.UChar) => 8
        | _ => 32
      -- Guard: division by zero → UB, don't fold
      let isDivByZero := (op == .Divide || op == .Remainder) && b == 0
      -- Guard: shift amount outside [0, bits) → UB, don't fold
      let shiftOob : Bool := match op with
        | .ShiftLeft | .ShiftRight => b < 0 || b >= (bits : Int)
        | _ => false
      if isDivByZero || shiftOob then return none
      let rOpt : Option Int := match op with
        | .Add        => some (a + b)
        | .Subtract   => some (a - b)
        | .Multiply   => some (a * b)
        | .Divide     => some (tdiv a b)     -- C semantics: truncation toward zero
        | .Remainder  => some (tmod a b)     -- C semantics: sign follows dividend
        | .BitAnd     => some (intBitAnd bits a b)
        | .BitOr      => some (intBitOr  bits a b)
        | .BitXor     => some (intBitXor bits a b)
        | .ShiftLeft  => some (a * (2 : Int) ^ b.toNat)
        | .ShiftRight =>
            if unsigned then
              -- Logical right shift: T-div = floor for non-negative a
              some (tdiv a ((2 : Int) ^ b.toNat))
            else
              -- Arithmetic right shift = floor division by 2^shift
              some (arithmeticShiftRight a b.toNat)
        | .Equal          => some (if a == b then 1 else 0)
        | .NotEqual       => some (if a != b then 1 else 0)
        | .LessThan       => some (if a < b then 1 else 0)
        | .LessOrEqual    => some (if a <= b then 1 else 0)
        | .GreaterThan    => some (if a > b then 1 else 0)
        | .GreaterOrEqual => some (if a >= b then 1 else 0)
      match rOpt with
      | none   => return none
      | some r =>
          let w := match tOpt with | some t => wrapForType t r | none => r
          return some [.Copy (.Constant w) dst]

  -- ── Double Binary ────────────────────────────────────────────────────────
  | .Binary op src1 src2 dst =>
      let f1Opt ← lookupFloat src1
      let f2Opt ← lookupFloat src2
      match f1Opt, f2Opt with
      | some f1, some f2 =>
          -- Arithmetic: result is another double
          let arith : Option Float := match op with
            | .Add      => some (f1 + f2)
            | .Subtract => some (f1 - f2)
            | .Multiply => some (f1 * f2)
            | .Divide   => some (f1 / f2)
            | _         => none
          match arith with
          | some r =>
              let v ← internFoldedFloat r
              return some [.Copy v dst]
          | none =>
              -- Relational: result is an integer (0 or 1)
              let cmp : Option Int := match op with
                | .Equal          => some (if f1 == f2 then 1 else 0)
                | .NotEqual       => some (if f1 != f2 then 1 else 0)
                | .LessThan       => some (if f1 < f2 then 1 else 0)
                | .LessOrEqual    => some (if f1 <= f2 then 1 else 0)
                | .GreaterThan    => some (if f1 > f2 then 1 else 0)
                | .GreaterOrEqual => some (if f1 >= f2 then 1 else 0)
                | _               => none
              match cmp with
              | some r => return some [.Copy (.Constant r) dst]
              | none   => return none
      | _, _ => return none

  -- ── Conditional jumps on integer constant ────────────────────────────────
  | .JumpIfZero (.Constant n) target =>
      return some (if n == 0 then [.Jump target] else [])
  | .JumpIfNotZero (.Constant n) target =>
      return some (if n != 0 then [.Jump target] else [])

  -- ── Conditional jumps on double constant ─────────────────────────────────
  | .JumpIfZero src target =>
      let fOpt ← lookupFloat src
      match fOpt with
      | some f => return some (if f == 0.0 then [.Jump target] else [])
      | none   => return none
  | .JumpIfNotZero src target =>
      let fOpt ← lookupFloat src
      match fOpt with
      | some f => return some (if f != 0.0 then [.Jump target] else [])
      | none   => return none

  -- ── SignExtend: sign-extend Int or Char constant to Long ─────────────────
  | .SignExtend srcTyp (.Constant n) dst =>
      -- Wrap to src width (gets the correct signed bit pattern), then sign-extend to 64-bit
      let signed   := wrapForType srcTyp n
      let extended := wrapInt64 signed
      return some [.Copy (.Constant extended) dst]

  -- ── ZeroExtend: zero-extend UInt or UChar constant to ULong ──────────────
  | .ZeroExtend srcTyp (.Constant n) dst =>
      let zeroed : Int := match srcTyp with
        | .UChar => wrapUInt8 n
        | .UInt  => wrapUInt32 n
        | _      => n   -- already non-negative
      return some [.Copy (.Constant zeroed) dst]

  -- ── Truncate: truncate Long/ULong constant to a shorter type ─────────────
  | .Truncate (.Constant n) dst =>
      let tOpt ← dstTyp dst
      let truncated := match tOpt with | some t => wrapForType t n | none => wrapInt32 n
      return some [.Copy (.Constant truncated) dst]

  -- ── Integer → Double ─────────────────────────────────────────────────────
  | .IntToDouble (.Constant n) dst =>
      -- Float.ofInt is arbitrary-precision; correctly rounds to nearest representable double.
      -- Used for both Int→Double and Long→Double (TackyGen uses the same instruction).
      let v ← internFoldedFloat (Float.ofInt n)
      return some [.Copy v dst]

  | .UIntToDouble (.Constant n) dst =>
      -- n is a non-negative Lean Int representing an unsigned 32-bit value.
      let v ← internFoldedFloat (Float.ofInt n)
      return some [.Copy v dst]

  | .ULongToDouble (.Constant n) dst =>
      -- n is a non-negative Lean Int representing an unsigned 64-bit value (0..2^64-1).
      -- For large values (>2^63-1), n is a large positive Int; Float.ofInt rounds correctly.
      let v ← internFoldedFloat (Float.ofInt n)
      return some [.Copy v dst]

  -- ── Double → Integer (guarded against out-of-range / UB) ─────────────────
  | .DoubleToInt src dst =>
      -- Handles both Double→Int (32-bit) and Double→Long (64-bit); CodeGen distinguishes
      -- by BST type.  We use the dst typeEnv entry to select the correct range.
      let fOpt ← lookupFloat src
      match fOpt with
      | none   => return none
      | some f =>
          if f.isNaN || f.isInf then return none
          let tOpt ← dstTyp dst
          -- Valid truncation range: the mathematical truncation must fit in the type.
          let (lo, hi) : Float × Float := match tOpt with
            | some .Long => (-9223372036854775809.0, 9223372036854775808.0)
            | _          => (-2147483649.0,          2147483648.0)
          if f <= lo || f >= hi then return none   -- out of range → UB, don't fold
          let intVal : Int :=
            if f >= 0.0 then (Float.toUInt64 f).toNat
            else -((Float.toUInt64 (-f)).toNat)
          let w := match tOpt with | some t => wrapForType t intVal | none => wrapInt32 intVal
          return some [.Copy (.Constant w) dst]

  | .DoubleToUInt src dst =>
      -- Double → UInt (32-bit unsigned): valid range [0, 2^32)
      let fOpt ← lookupFloat src
      match fOpt with
      | none   => return none
      | some f =>
          if f.isNaN || f.isInf || f < 0.0 || f >= 4294967296.0 then return none
          let v : Int := (Float.toUInt64 f).toNat
          return some [.Copy (.Constant (wrapUInt32 v)) dst]

  | .DoubleToULong src dst =>
      -- Double → ULong (64-bit unsigned): valid range [0, 2^64)
      let fOpt ← lookupFloat src
      match fOpt with
      | none   => return none
      | some f =>
          if f.isNaN || f.isInf || f < 0.0 || f >= 18446744073709551616.0 then return none
          -- For f in [0, 2^63): Float.toUInt64 gives the exact ULong value.
          -- For f in [2^63, 2^64): subtract 2^63, convert, add 2^63 back.
          let v : Int :=
            if f < 9223372036854775808.0 then (Float.toUInt64 f).toNat
            else
              let shifted := Float.toUInt64 (f - 9223372036854775808.0)
              (shifted.toNat : Int) + 9223372036854775808
          return some [.Copy (.Constant (wrapUInt64 v)) dst]

  -- ── No fold possible ─────────────────────────────────────────────────────
  | _ => return none

-- ---------------------------------------------------------------------------
-- Per-instruction processing: substitute → fold → update constVarMap
-- ---------------------------------------------------------------------------

/-- Extract the destination Val from an instruction (if it has one). -/
private def instrDst (instr : Instruction) : Option Val :=
  match instr with
  | .Unary _ _ dst | .Binary _ _ _ dst | .Copy _ dst => some dst
  | .SignExtend _ _ dst | .ZeroExtend _ _ dst | .Truncate _ dst => some dst
  | .IntToDouble _ dst | .DoubleToInt _ dst | .UIntToDouble _ dst => some dst
  | .DoubleToUInt _ dst | .ULongToDouble _ dst | .DoubleToULong _ dst => some dst
  | .Load _ dst | .GetAddress _ dst | .AddPtr _ _ _ dst | .CopyFromOffset _ _ dst => some dst
  | .FunCall _ _ (some dst) => some dst
  | _ => none

/-- Process one instruction through constant folding:
    1. At Label: clear constVarMap (conservative for jump targets).
    2. At Store / FunCall: clear constVarMap (alias safety — see note below).
    3. Invalidate the destination variable (it's being overwritten).
    4. Substitute constants for source variables from constVarMap.
    5. Try to fold the substituted instruction.
    6. Update constVarMap for any Copy(constVal, Var) results.

    Note on alias safety:
    A `Store src ptr` writes through a pointer to some unknown memory location.
    Without alias analysis we cannot know which variable `ptr` aliases, so we
    must conservatively assume any tracked variable could have been modified and
    clear the entire constVarMap.  The same applies to `FunCall`: the callee may
    read/write any variable it has a pointer to (globals, stack vars passed by
    reference). -/
private def processInstr (instr : Instruction) : FoldM (List Instruction) := do
  -- Step 1: labels clear the constant map
  match instr with
  | .Label _ =>
      modify fun st => { st with constVarMap := [] }
      return [instr]
  | _ => pure ()
  -- Step 2: stores and calls invalidate the whole map (alias safety)
  match instr with
  | .Store _ _ | .FunCall _ _ _ =>
      modify fun st => { st with constVarMap := [] }
  | _ => pure ()
  -- Step 2: invalidate the destination so stale facts don't persist
  match instrDst instr with
  | some dst => invalidateDst dst
  | none     => pure ()
  -- Step 3: substitute constants for source variables
  let instrS ← substInstr instr
  -- Step 4: try to fold
  let foldedOpt ← foldOne instrS
  match foldedOpt with
  | some replacements =>
      -- Step 5: update constVarMap for any Copy(constVal, Var dst) in the replacements
      for ri in replacements do
        match ri with
        | .Copy src dst => recordConst dst src
        | _ => pure ()
      return replacements
  | none =>
      -- Not foldable: emit the substituted instruction; if it is a Copy, track it
      match instrS with
      | .Copy src dst => recordConst dst src
      | _ => pure ()
      return [instrS]

-- ---------------------------------------------------------------------------
-- Constant folding pass over a function body
-- ---------------------------------------------------------------------------

/-- Run one constant-folding pass over `body`. Returns the rewritten body. -/
private def constantFoldingPass (body : List Instruction) : FoldM (List Instruction) := do
  let mut result : List Instruction := []
  for instr in body do
    let instrs ← processInstr instr
    result := result ++ instrs
  return result

-- ---------------------------------------------------------------------------
-- Unreachable Code Elimination
-- ---------------------------------------------------------------------------

/-- Drop non-Label instructions that appear after an unconditional transfer of
    control (Return or Jump) without an intervening Label.  Such instructions
    are syntactically unreachable: no fall-through can reach them, and they
    carry no label that could be a jump target.

    Labels are always kept even when they appear in the "dead zone" after a
    jump; they may still be targets of jumps from other live blocks and will be
    pruned by `removeOrphanLabels` if not. -/
private def removeAfterUncondJump (body : List Instruction) : List Instruction :=
  (body.foldl fun (acc : List Instruction × Bool) instr =>
    let (out, dead) := acc
    match instr with
    | .Label _ =>
        -- A Label always survives and resets the dead zone.
        (out ++ [instr], false)
    | .Return _ | .Jump _ =>
        -- Unconditional transfer: emit (if live) and enter dead zone.
        if dead then (out, true) else (out ++ [instr], true)
    | _ =>
        -- Any other instruction: skip if dead, keep if live.
        if dead then (out, true) else (out ++ [instr], false)
  ) ([], false) |>.1

/-- Collect all label names that are the explicit target of a Jump,
    JumpIfZero, or JumpIfNotZero instruction anywhere in `instrs`. -/
private def collectJumpTargets (instrs : List Instruction) : List String :=
  instrs.flatMap fun i => match i with
    | .Jump lbl | .JumpIfZero _ lbl | .JumpIfNotZero _ lbl => [lbl]
    | _ => []

/-- Remove Label instructions that are not the target of any jump in the
    current body.  After removal the instructions following the orphaned label
    (up to the next surviving label) will be dead and will be cleaned up by
    `removeAfterUncondJump` on the next iteration of the fixed-point loop. -/
private def removeOrphanLabels (body : List Instruction) : List Instruction :=
  let targets := collectJumpTargets body
  body.filter fun i => match i with
    | .Label lbl => targets.any fun t => t == lbl
    | _ => true

/-- Remove jump instructions whose target is the immediately following
    instruction.  Handles all three jump flavours:
      • `Jump lbl`           — unconditional: the jump is truly a no-op.
      • `JumpIfZero _ lbl`   — conditional: both the taken and not-taken
        paths land on the same instruction, so the test is irrelevant.
      • `JumpIfNotZero _ lbl` — same reasoning as JumpIfZero.
    A jump instruction at index i is useless when body[i+1] is `Label lbl`
    and `lbl` is the jump target. -/
private def removeUselessJumps (body : List Instruction) : List Instruction :=
  -- Walk the list pairwise.  A jump is useless if its target equals the
  -- label name of the immediately following instruction.
  let isUselessJump (instr : Instruction) (rest : List Instruction) : Bool :=
    let nextLbl : Option String := match rest with
      | (Instruction.Label lbl) :: _ => some lbl
      | _ => none
    match instr, nextLbl with
    | .Jump lbl,             some nl => lbl == nl
    | .JumpIfZero _ lbl,     some nl => lbl == nl
    | .JumpIfNotZero _ lbl,  some nl => lbl == nl
    | _, _                           => false
  -- Iterate: if current instruction is a useless jump, skip it.
  -- Use fuel-based recursion for termination.
  let rec go : Nat → List Instruction → List Instruction
    | 0,    instrs           => instrs   -- fuel exhausted (shouldn't happen)
    | _,    []               => []
    | fuel, (i :: rest) =>
        if isUselessJump i rest
        then go (fuel - 1) rest          -- drop the useless jump
        else i :: go (fuel - 1) rest
  go body.length body

/-- Compute the set of instruction indices (0-based) that are reachable from
    instruction 0 via the control-flow graph.

    Each instruction is a CFG node; edges are:
      • Non-control-flow instruction i → i+1   (fall-through)
      • Label i → i+1                          (a Label is a no-op; fall-through)
      • Jump i → target                        (no fall-through)
      • JumpIfZero/JumpIfNotZero i → i+1 AND target  (conditional; two successors)
      • Return i → (none)

    The reachable set grows monotonically; we iterate at most n times (where n
    is the body length) to guarantee convergence.  This correctly handles
    self-referential dead loops (every block has a predecessor within the loop,
    but no block in the loop is reachable from outside it). -/
private def reachableIndices (body : List Instruction) : List Nat :=
  let n     := body.length
  let iBody := (List.range n).zip body  -- List (Nat × Instruction)

  -- Build label name → instruction index map
  let lblIdx : List (String × Nat) := iBody.filterMap fun (i, instr) =>
    match instr with | .Label lbl => some (lbl, i) | _ => none
  let findLbl (lbl : String) : Option Nat :=
    lblIdx.findSome? fun (l, i) => if l == lbl then some i else none

  -- Successors of instruction i
  let succs (i : Nat) (instr : Instruction) : List Nat :=
    match instr with
    | .Return _                            => []
    | .Jump lbl                            => (findLbl lbl).toList
    | .JumpIfZero _ lbl | .JumpIfNotZero _ lbl =>
        (if i + 1 < n then [i + 1] else []) ++ (findLbl lbl).toList
    | _                                    => if i + 1 < n then [i + 1] else []

  -- One propagation step: extend the reachable set with successors of all
  -- currently-reachable instructions that are not yet in the set.
  let step (reach : List Nat) : List Nat :=
    let novel := reach.flatMap fun i =>
      match iBody.find? fun (j, _) => j == i with
      | some (_, instr) => (succs i instr).filter fun j => !(reach.any (· == j))
      | none            => []
    reach ++ novel

  -- Iterate n times starting from {0} (instruction 0 is always reachable)
  (List.range n).foldl (fun r _ => step r) [0]

/-- One pass of unreachable-code elimination.
      1. CFG reachability: drop any instruction whose index is not reachable from
         instruction 0.  This handles dead code after Return, self-referential
         dead loops, and dead branches — even when every dead block has a
         predecessor within the dead cluster.
      2. `removeOrphanLabels`: drop Label instructions that no surviving jump
         targets (labels reachable only by fall-through are no-ops).
      3. `removeUselessJumps`: drop jump instructions whose target is the
         immediately-following label.

    The outer fixed-point loop in `oneOptIter` re-runs this pass until the body
    stabilises (e.g. removing a useless jump may orphan a label, which on the
    next pass causes its block to be dropped). -/
private def unreachableCodeElim (body : List Instruction) : List Instruction :=
  let reach := reachableIndices body
  let indexedBody := (List.range body.length).zip body
  let kept  := indexedBody.filterMap fun (i, instr) =>
    if reach.any (· == i) then some instr else none
  removeUselessJumps (removeOrphanLabels kept)

-- ---------------------------------------------------------------------------
-- Copy Propagation
-- ---------------------------------------------------------------------------

/-  Algorithm (forward data-flow, Section 19.3):

    A "copy" is a pair (x, v) meaning "variable x currently holds value v"
    where v is either a Val.Var (another variable) or a Val.Constant.

    copyin(entry block)  = {}
    copyin(other block B) = ∩ { copyout(P) | P predecessor of B }
    copyout(B) = gen(B) ∪ (copyin(B) \ kill(B))
      where gen/kill are computed by walking B sequentially from copyin.

    Invariant kept the same as constant-folding for safety:
      • Store(_,_)   → kill ALL copies (alias safety, no alias analysis)
      • FunCall(_,_,_) → kill copies for static variables only
        (local variables cannot be aliased by a call)
      • Any assignment to x → kill all copies (x, _) and (y, x) for all y.

    Substitution rules: same as substInstr in constant folding — do NOT
    substitute in Store src, FunCall args, AddPtr, CopyToOffset src, GetAddress.
    For Return (some v): substitute freely now that CodeGen uses funRetAsmType
    for constants.
-/

/-- A copy set maps variable names to their known values (Var or Constant). -/
private abbrev CopySet := List (String × Val)

/-- Check whether two CopySet entries are equal. -/
private def copyEq (a b : String × Val) : Bool :=
  a.1 == b.1 && a.2 == b.2

/-- Intersection of two copy sets: keep only copies present in BOTH sets. -/
private def meetCopies (a b : CopySet) : CopySet :=
  a.filter fun e => b.any fun e2 => copyEq e e2

/-- Substitute a Val using a CopySet, following chains of copies.
    For example, if cs = {(x → Var y), (y → Constant 20)}, then
    cpSubstVal cs (Var x) = Constant 20 (two hops: x → y → 20).
    Chain depth is bounded to 20 to prevent infinite loops.
    This chained lookup preserves Var→Var relationships in the copy set
    (we record direct copies in cpTransfer) while still enabling constant
    propagation through chains of Var→Var copies. -/
private def cpSubstVal (cs : CopySet) (v : Val) : Val :=
  (List.range 20).foldl
    (fun acc _ =>
      match acc with
      | .Var name =>
          cs.findSome? (fun (n, cv) => if n == name then some cv else none) |>.getD acc
      | _ => acc)
    v

/-- Sign-normalize a constant index for AddPtr.
    Copy propagation stores constants with wrapForType semantics: Int/UInt values
    are stored as values in [0, 2^32-1] using the unsigned representation.  When
    such a constant is used as an AddPtr index in 64-bit code, it must first be
    sign-extended from 32 bits to 64 bits — exactly as `movslq` does for Longword
    variables.  This function applies that sign extension based on the declared type
    of the original Var that was substituted, preventing the constant from being
    misinterpreted as a large positive offset. -/
private def signNormAddPtrIdx (typeEnv : List (String × AST.Typ))
    (origVar : String) (n : Int) : Int :=
  match typeEnv.findSome? fun (nm, t) => if nm == origVar then some t else none with
  | some AST.Typ.Int | some AST.Typ.UInt  =>
      -- 32-bit type: sign-extend to 64-bit (same as movslq would do).
      -- wrapUInt32 stored values in [0, 2^32-1]; values ≥ 2^31 represent negative ints.
      wrapInt32 n
  | some AST.Typ.Char | some AST.Typ.SChar | some AST.Typ.UChar =>
      -- 8-bit type: sign-extend to 64-bit.
      wrapInt8 n
  | _ =>
      -- Long, ULong, Pointer, etc.: no sign extension; use value as-is.
      n

/-- Apply copy substitution to an instruction (same safety rules as substInstr).
    `typeEnv` is needed only for the AddPtr case to sign-normalize constants. -/
private def cpSubstInstr (cs : CopySet) (typeEnv : List (String × AST.Typ))
    (instr : Instruction) : Instruction :=
  let sub := cpSubstVal cs
  match instr with
  | .Unary op src dst          => .Unary op (sub src) dst
  | .Binary op s1 s2 dst       => .Binary op (sub s1) (sub s2) dst
  | .Copy src dst              => .Copy (sub src) dst
  | .JumpIfZero v t            => .JumpIfZero (sub v) t
  | .JumpIfNotZero v t         => .JumpIfNotZero (sub v) t
  | .SignExtend ty src dst      => .SignExtend ty (sub src) dst
  | .ZeroExtend ty src dst      => .ZeroExtend ty (sub src) dst
  | .Truncate src dst          => .Truncate (sub src) dst
  | .IntToDouble src dst       => .IntToDouble (sub src) dst
  | .DoubleToInt src dst       => .DoubleToInt (sub src) dst
  | .UIntToDouble src dst      => .UIntToDouble (sub src) dst
  | .DoubleToUInt src dst      => .DoubleToUInt (sub src) dst
  | .ULongToDouble src dst     => .ULongToDouble (sub src) dst
  | .DoubleToULong src dst     => .DoubleToULong (sub src) dst
  | .Return (some v)           => .Return (some (sub v))
  -- FunCall: propagate into arguments; be careful with Var→Constant for 64-bit types.
  -- CodeGen determines the argument's register width from `valAsmType(arg)`.  For a
  -- Var, BST lookup returns the declared type (e.g. Quadword for `long`).  For a
  -- Constant(n), valAsmType returns Longword when n fits in [-2^31, 2^31-1], so a
  -- Long/ULong variable holding a small negative value would incorrectly get
  -- `movl $n, %esi` (32-bit) instead of `movq $n, %rsi` (64-bit).
  -- Safety rule: allow Var→Constant only when the original variable's type is NOT
  -- Long or ULong (i.e., 32-bit or smaller — valAsmType(Constant(n)) = Longword is fine).
  | .FunCall fn args dst       =>
      let subArg (v : Val) : Val :=
        let w := cpSubstVal cs v
        match v, w with
        | .Var origName, .Constant _ =>
            -- Var→Constant: safe unless original var is Long or ULong (64-bit type)
            let origTyp := typeEnv.findSome? fun (n, t) => if n == origName then some t else none
            match origTyp with
            | some AST.Typ.Long | some AST.Typ.ULong => v  -- 64-bit: keep original Var
            | _ => w  -- 32-bit or unknown: safe to use constant
        | _, .Var _ => w   -- Var→Var: always safe
        | _, _      => v   -- already a constant, no substitution needed
      .FunCall fn (args.map subArg) dst
  -- AddPtr index: safe to substitute constants here because CodeGen special-cases
  -- a Constant index (computing offset = n*scale at compile time).  However, we
  -- must sign-normalize the constant: wrapUInt32/wrapInt32 may have stored a UInt
  -- value in the unsigned range [2^31, 2^32-1] which must be reinterpreted as its
  -- signed 32-bit value (-5 etc.) before scaling. signNormAddPtrIdx handles this.
  | .AddPtr ptr idx sc dst     =>
      let substIdx := sub idx
      let normalizedIdx := match idx, substIdx with
        | .Var name, .Constant n =>
            -- Constant was substituted for a variable: sign-normalize based on type.
            Val.Constant (signNormAddPtrIdx typeEnv name n)
        | _, _ => substIdx   -- Var→Var or idx was already a Constant
      .AddPtr ptr normalizedIdx sc dst
  -- Store src: CodeGen uses valAsmType(src) to pick the instruction width (e.g.
  -- movb vs movl vs movq).  Substituting a narrow-typed Var with a Constant loses
  -- the type, causing valAsmType(Constant n) = Longword for small n regardless of
  -- the true type.  Exclude Long, ULong (Quadword needed), and Char/SChar/UChar
  -- (Byte needed) from Var→Constant substitution so the typed Var is preserved.
  | .Store src ptr =>
      let srcW := let w := sub src
                  match src, w with
                  | .Var origName, .Constant _ =>
                      let origTyp := typeEnv.findSome? fun (n, t) => if n == origName then some t else none
                      match origTyp with
                      | some AST.Typ.Long  | some AST.Typ.ULong  => src  -- 64-bit: movl instead of movq
                      | some AST.Typ.Char  | some AST.Typ.SChar
                      | some AST.Typ.UChar                        => src  -- 8-bit:  movl instead of movb
                      | _ => w
                  | _, .Var _ => w
                  | _, _ => src
      .Store srcW ptr
  -- CopyToOffset src: same reasoning — CodeGen uses valAsmType(src) for width.
  -- Exclude Long/ULong and Char/SChar/UChar from Var→Constant substitution.
  | .CopyToOffset src dstName off =>
      let srcW := let w := sub src
                  match src, w with
                  | .Var origName, .Constant _ =>
                      let origTyp := typeEnv.findSome? fun (n, t) => if n == origName then some t else none
                      match origTyp with
                      | some AST.Typ.Long  | some AST.Typ.ULong  => src  -- 64-bit
                      | some AST.Typ.Char  | some AST.Typ.SChar
                      | some AST.Typ.UChar                        => src  -- 8-bit
                      | _ => w
                  | _, .Var _ => w
                  | _, _ => src
      .CopyToOffset srcW dstName off
  -- CopyFromOffset: substitute the source aggregate name if a Var→Var copy is known.
  -- For example, if cs has (glob → Var loc), then CopyFromOffset "glob" off dst
  -- becomes CopyFromOffset "loc" off dst, allowing the glob→loc copy to be later
  -- removed by DSE if glob is no longer read.
  -- Only Var→Var is safe: Var→Constant would produce an invalid aggregate name.
  | .CopyFromOffset srcName off dst =>
      let substSrc := cpSubstVal cs (.Var srcName)
      let safeSrcName := match substSrc with
          | .Var newName => newName   -- Var→Var: safe substitution
          | _            => srcName   -- Var→Constant or not found: keep original
      .CopyFromOffset safeSrcName off dst
  -- Load ptr: substitute only Var→Var (same semantics as CopyFromOffset above).
  -- Var→Constant is unsafe (Constants are integer values, not memory addresses).
  -- For example, if cs has (glob → Var loc), Load (Var glob) dst becomes
  -- Load (Var loc) dst, enabling DSE to remove the earlier glob = loc assignment
  -- (once glob is no longer read).
  | .Load ptr dst =>
      let substPtr := cpSubstVal cs ptr
      let safePtr := match ptr, substPtr with
          | .Var _, .Var _ => substPtr  -- Var→Var: safe
          | _, _           => ptr        -- keep original otherwise
      .Load safePtr dst
  -- GetAddress src: do NOT substitute (would change the variable whose address is taken).
  | _                          => instr

/-- Kill all copies that involve variable `x` (as LHS or as RHS). -/
private def killVar (cs : CopySet) (x : String) : CopySet :=
  cs.filter fun (lhs, rhs) =>
    lhs != x && !(match rhs with | .Var rName => rName == x | _ => false)

/-- Update a CopySet after seeing instruction `instr`, given `staticVars` and
    `addrTakenVars` (local variables whose address was taken via GetAddress).
    - Assignment to x: kill all copies involving x, then add (x, src) if it's
      a Copy of a Var or Constant.
    - Store: kill everything (alias safety).
    - FunCall: kill copies involving static vars AND address-taken locals
      (both can be read or written by the callee through stored pointers). -/
private def cpTransfer (cs : CopySet) (instr : Instruction)
    (staticVars : List String) (addrTakenVars : List String) : CopySet :=
  match instr with
  | .Store _ _ =>
      -- A Store writes through a pointer; without full alias analysis we do
      -- not know which variable the pointer targets.  However, only variables
      -- whose address was taken (addrTakenVars) or that are globally visible
      -- (staticVars) can be aliased through a stored pointer in C.  Local
      -- variables whose address was never passed out of the function cannot be
      -- reached this way.  Kill copies involving those aliasable variables and
      -- leave all others intact.
      cs.filter fun (lhs, rhs) =>
        let aliasable := staticVars ++ addrTakenVars
        !(aliasable.any (· == lhs)) &&
        !(match rhs with | .Var rName => aliasable.any (· == rName) | _ => false)
  | .FunCall _ _ dst =>
      -- Kill copies involving static variables (callee may read/write any static).
      -- Kill copies involving address-taken locals (may be aliased via stored ptrs).
      -- Also kill the copy for the destination variable (overwritten by return value).
      let dstName : Option String := match dst with
        | some (.Var n) => some n
        | _             => none
      let killedVars := staticVars ++ addrTakenVars
      let afterKill := cs.filter fun (lhs, rhs) =>
        !(killedVars.any (· == lhs)) &&
        !(match rhs with | .Var rName => killedVars.any (· == rName) | _ => false)
      match dstName with
      | some n => killVar afterKill n
      | none   => afterKill
  | .Copy src dst =>
      -- Kill stale copies for dst, then record the new DIRECT copy.
      -- We record the PRE-SUBSTITUTION source (the original Var or Constant)
      -- rather than the transitively-substituted value.  This preserves
      -- Var→Var relationships like (x → Var y) at join points even when y has
      -- different concrete values on different paths (e.g. y=20 in one branch
      -- and y=100 in another).  cpSubstVal follows chains when performing
      -- substitution at use sites, so downstream constants are still reached.
      let dstName := match dst with | .Var n => n | .Constant _ => ""
      if dstName == "" then cs
      else
        let cs1 := killVar cs dstName
        match src with
        | .Var srcName  => (dstName, .Var srcName) :: cs1
        | .Constant n   => (dstName, .Constant n) :: cs1
  | .CopyToOffset _ targetName _ =>
      -- CopyToOffset partially writes to an aggregate variable.
      -- Although it does not FULLY overwrite the aggregate (DSE treats it as a
      -- partial write — see dseDefSet), it DOES change the aggregate's value.
      -- Any copy of the form (x → Var targetName) or (targetName → y) is now stale:
      -- e.g. if we had `s1 = s2; s2.x = 5;`, the copy (s1 → s2) must be killed
      -- because s2 changed and s1.x may now differ from s2.x.
      killVar cs targetName
  | instr =>
      -- For any other instruction that defines a variable, kill that variable.
      match instrDst instr with
      | some (.Var dstName) => killVar cs dstName
      | _                   => cs

/-- True for instructions that end a basic block (branches and returns). -/
private def isBranchInstr : Instruction → Bool
  | .Jump _ | .JumpIfZero _ _ | .JumpIfNotZero _ _ | .Return _ => true
  | _ => false

/-- Split a function body into basic blocks.
    A new block starts at:
      1. instruction 0 (the entry),
      2. every `Label` instruction (a potential jump target), and
      3. every instruction immediately following a branch (Jump/JumpIfZero/
         JumpIfNotZero/Return) — the fall-through successor of a conditional
         branch may have no label in TACKY.
    Returns a list of blocks; each block is (optLabelName, instructions).
    `optLabelName` is `some lbl` when the block's first instruction is
    `Label lbl`, `none` for unlabeled blocks. -/
private def splitBlocks (body : List Instruction)
    : List (Option String × List Instruction) :=
  -- State: accumulated blocks, current block's label, current block's instrs,
  --        and whether the previous instruction was a branch (so the next
  --        instruction must start a new block even without a label).
  let (blocks, curLbl, cur, _) := body.foldl
    (fun (acc : List (Option String × List Instruction) × Option String ×
                List Instruction × Bool) instr =>
      let (blks, curLbl, cur, afterBranch) := acc
      match instr with
      | .Label lbl =>
          -- Flush current block (if non-empty) then start a labeled block.
          let blks1 := if cur.isEmpty then blks else blks ++ [(curLbl, cur)]
          (blks1, some lbl, [.Label lbl], false)
      | _ =>
          if afterBranch then
            -- Previous instruction was a branch; flush and start new block.
            let blks1 := if cur.isEmpty then blks else blks ++ [(curLbl, cur)]
            (blks1, none, [instr], isBranchInstr instr)
          else
            (blks, curLbl, cur ++ [instr], isBranchInstr instr))
    ([], none, [], false)
  -- Flush last block.
  if cur.isEmpty then blocks else blocks ++ [(curLbl, cur)]

/-- Compute predecessor block indices for each block.
    A block at index `j` is a predecessor of block `i` if:
      (a) j = i - 1 and block j does not end with Return or unconditional Jump, OR
      (b) block j ends with a Jump/JumpIfZero/JumpIfNotZero targeting block i's label. -/
private def computePredecessors (blocks : List (Option String × List Instruction))
    : List (List Nat) :=
  let n := blocks.length
  let blockLabel (i : Nat) : Option String :=
    match blocks[i]? with
    | some (some lbl, _) => some lbl
    | _                  => none
  let blockLastInstr (i : Nat) : Option Instruction :=
    match blocks[i]? with
    | some (_, instrs) => instrs.getLast?
    | none             => none
  -- For each block i, collect all j that are predecessors.
  -- NOTE: j == i is allowed when block j ends with a back-edge jump to its
  -- own label (e.g. `JumpIfNotZero(cond, start_loop)` inside block
  -- `start_loop`).  Fall-through self-loops (j+1 == j) cannot arise in
  -- well-formed TACKY, so the normal logic handles this correctly without a
  -- j==i guard.
  (List.range n).map fun i =>
    (List.range n).filter fun j =>
      match blockLastInstr j with
      | none => j + 1 == i   -- empty block: fall-through
      | some last =>
          match last with
          | .Return _ => false
          | .Jump lbl => blockLabel i == some lbl
          | .JumpIfZero _ lbl | .JumpIfNotZero _ lbl =>
              blockLabel i == some lbl || j + 1 == i
          | _ => j + 1 == i   -- fall-through

/-- Run one full copy-propagation pass over a function body.
    Uses forward data-flow to compute copyin for each block, then applies
    cpSubstInstr within each block starting from its copyin set.

    `staticVars`    — program-level static/global variable names; copies
                      involving these are killed at every FunCall site.
    `addrTakenVars` — local variables whose address was taken in this function
                      body (GetAddress src); these can be aliased through stored
                      pointers, so their copies are also killed at FunCall sites. -/
private def copyPropagation (body : List Instruction)
    (staticVars : List String) (typeEnv : List (String × AST.Typ)) : List Instruction :=
  if body.isEmpty then body
  else
    -- Collect local variables whose address is taken in this body.
    -- A GetAddress(Var name, _) means `name` can be aliased from now on.
    let addrTakenVars : List String := body.filterMap fun instr =>
      match instr with
      | .GetAddress (.Var name) _ => some name
      | _                         => none
    let blocks := splitBlocks body
    let n := blocks.length
    let preds := computePredecessors blocks
    -- copyin.(i) = {} initially for all blocks (conservative: top = empty set
    -- means "no copies known"; meet is intersection so start with universe).
    -- Actually for the forward analysis, start all non-entry blocks with the
    -- "all copies" universe — we represent this as `none` (meaning "not yet
    -- initialized") vs `some cs` (meaning a known set).
    -- Iterate to fixed point (at most n rounds).
    -- copyoutSets.(i) : Option CopySet (none = not yet computed)
    let initCopyouts : Array (Option CopySet) := (List.replicate n none).toArray

    -- Compute copyout for block i given copyin cs.
    let computeCopyout (i : Nat) (cs : CopySet) : CopySet :=
      match blocks[i]? with
      | none => cs
      | some (_, instrs) =>
          instrs.foldl (fun c instr => cpTransfer c instr staticVars addrTakenVars) cs

    -- One iteration: for each block, compute copyin from predecessors' copyouts,
    -- then recompute copyout. Return updated copyouts and whether anything changed.
    let oneIter (copyouts : Array (Option CopySet))
        : Array (Option CopySet) × Bool :=
      (List.range n).foldl
        (fun (acc : Array (Option CopySet) × Bool) i =>
          let (cos, changed) := acc
          -- copyin(entry) = {}; copyin(other) = ∩ predecessor copyouts
          let copyin : CopySet :=
            if i == 0 then []
            else
              let predList := preds[i]?.getD []
              -- Collect copyouts of all predecessors that have been computed.
              let predCos : List CopySet := predList.filterMap fun j =>
                Option.join (cos[j]?)
              match predCos with
              | []        => []   -- no computed predecessors yet → conservative empty
              | [one]     => one
              | first :: rest => rest.foldl meetCopies first
          let newCopyout := computeCopyout i copyin
          let oldCopyout : Option CopySet := Option.join (cos[i]?)
          let nowChanged := match oldCopyout with
            | none    => true
            | some old => !(newCopyout.all fun e => old.any fun e2 => copyEq e e2) ||
                          !(old.all fun e => newCopyout.any fun e2 => copyEq e e2)
          (cos.set! i (some newCopyout), changed || nowChanged))
        (copyouts, false)

    -- Run to fixed point (fuel = n + 1 iterations suffices for a DAG; loops
    -- may need more but n rounds always converges for monotone analyses).
    let finalCopyouts : Array (Option CopySet) :=
      (List.range (n + 1)).foldl
        (fun cos _ =>
          let (cos', _) := oneIter cos
          cos')
        initCopyouts

    -- Compute copyin for each block from final copyouts.
    let copyin (i : Nat) : CopySet :=
      if i == 0 then []
      else
        let predList := preds[i]?.getD []
        let predCos : List CopySet := predList.filterMap fun j =>
          Option.join (finalCopyouts[j]?)
        match predCos with
        | []        => []
        | [one]     => one
        | first :: rest => rest.foldl meetCopies first

    -- Apply substitution to each block using its copyin.
    -- Also drop redundant copies: after substitution, if Copy(v, Var dst) is emitted
    -- and either v == Var dst (self-copy) or the current copy set already maps dst → v,
    -- the instruction is a no-op and can be safely removed.
    let newBlocks := (List.range n).map fun i =>
      match blocks[i]? with
      | none => []
      | some (_, instrs) =>
          let (rewritten, _) := instrs.foldl
            (fun (acc : List Instruction × CopySet) instr =>
              let (out, cs) := acc
              let instrS := cpSubstInstr cs typeEnv instr
              -- For Copy instructions: update the copy set using the ORIGINAL (pre-substitution)
              -- instruction so that Var→Var relationships survive.  When cpSubstInstr converts
              -- `Copy y x` (y → Constant 20) into `Copy (Constant 20) x`, using the substituted
              -- instruction for cpTransfer would record (x → Constant 20), losing the `x = y`
              -- relationship needed at join points.  Using the original instruction instead
              -- records (x → Var y), which meetCopies can intersect across branches.
              -- For all other instructions, use the substituted form so the copy set accurately
              -- reflects the post-substitution state.
              let cs1 :=
                match instr with
                | .Copy _ _ => cpTransfer cs instr  staticVars addrTakenVars
                | _          => cpTransfer cs instrS staticVars addrTakenVars
              -- Detect redundant copies: Copy(v, Var dstName) where dst already = v.
              let isRedundantCopy : Bool := match instrS with
                | .Copy src (.Var dstName) =>
                    -- Self-copy (v = Var dstName) OR copyin already has dstName → v.
                    src == .Var dstName ||
                    cs.any fun (lhs, rhs) => lhs == dstName && rhs == src
                | _ => false
              if isRedundantCopy
              then (out, cs1)          -- skip the instruction, keep updated cs
              else (out ++ [instrS], cs1))
            ([], copyin i)
          rewritten

    -- Reassemble the flat body, then remove any useless jumps that copy propagation
    -- may have introduced (e.g. JumpIfZero(cond, lbl) immediately before Label(lbl)
    -- after a redundant copy in the if-body was eliminated).
    removeUselessJumps (newBlocks.foldl (· ++ ·) [])

-- ---------------------------------------------------------------------------
-- Dead Store Elimination (DSE) — backward liveness analysis
-- ---------------------------------------------------------------------------

/-- Variables read by a Val (only Var has a name; Constants have none). -/
private def valVarNames : Val → List String
  | .Var name => [name]
  | _         => []

/-- Collect global/extern variable names referenced in a function body.
    In the TACKY IR, variable naming conventions are:
      - Global C variables keep their original C names (e.g., "x", "glob") — no dot.
      - Local variables are renamed by VarResolution to "name.N" (always have a dot).
      - TackyGen temporaries are named "tmp.N" (always have a dot).
    Therefore any TACKY Var name without a '.' character must be a global variable.
    This catches `extern`-declared variables that TackyGen did not emit as
    StaticVariable top-levels (NoInitializer entries are skipped). -/
private def collectExternVars (body : List Instruction) : List String :=
  -- Collect all Var names anywhere in the body (both src and dst positions)
  let allVars : List String := body.flatMap fun instr =>
    match instr with
    | .Copy s d              => valVarNames s ++ valVarNames d
    | .Binary _ s1 s2 d      => valVarNames s1 ++ valVarNames s2 ++ valVarNames d
    | .Unary _ s d           => valVarNames s ++ valVarNames d
    | .SignExtend _ s d       => valVarNames s ++ valVarNames d
    | .ZeroExtend _ s d      => valVarNames s ++ valVarNames d
    | .Truncate s d          => valVarNames s ++ valVarNames d
    | .IntToDouble s d       => valVarNames s ++ valVarNames d
    | .DoubleToInt s d       => valVarNames s ++ valVarNames d
    | .UIntToDouble s d      => valVarNames s ++ valVarNames d
    | .DoubleToUInt s d      => valVarNames s ++ valVarNames d
    | .ULongToDouble s d     => valVarNames s ++ valVarNames d
    | .DoubleToULong s d     => valVarNames s ++ valVarNames d
    | .Return (some v)       => valVarNames v
    | .JumpIfZero v _        => valVarNames v
    | .JumpIfNotZero v _     => valVarNames v
    | .FunCall _ args dst    => args.flatMap valVarNames ++
                                  (match dst with | some d => valVarNames d | none => [])
    | .Store s p             => valVarNames s ++ valVarNames p
    | .Load p d              => valVarNames p ++ valVarNames d
    | .GetAddress s d        => valVarNames s ++ valVarNames d
    | .CopyToOffset s nm _   => valVarNames s ++ [nm]
    | .CopyFromOffset nm _ d => [nm] ++ valVarNames d
    | .AddPtr p i _ d        => valVarNames p ++ valVarNames i ++ valVarNames d
    | _                      => []
  -- A name with no '.' is a global/extern variable (not a local or temp)
  (allVars.filter fun n => !n.contains '.').eraseDups

/-- Union of two live sets (no duplicates).  O(n*m) but n is small. -/
private def liveUnion (a b : List String) : List String :=
  a ++ b.filter fun v => !a.contains v

/-- Remove a list of variable names from a live set. -/
private def liveRemove (ls : List String) (kill : List String) : List String :=
  ls.filter fun v => !kill.contains v

/-- Variables whose VALUES are read by an instruction.
    "use" set for backward liveness analysis.

    Key rules:
    - `GetAddress(src, dst)`: takes the ADDRESS of src — src's VALUE is not read.
      The test `getaddr_doesnt_gen` confirms this: GetAddress does NOT generate src.
    - `Load(ptr, dst)`:  reading through a pointer may read any addr-taken local variable.
      So all addrTakenVars are added to the use set.
    - `FunCall(...)`: callee may read any static variable or addr-taken local,
      so all of those are added to the use set.
    - `Return(v)`: at function exit, all static variables are live (other code may
      observe them), so staticVars are added to the use set. -/
private def dseUseSet (instr : Instruction)
    (staticVars addrTakenVars : List String) : List String :=
  match instr with
  | .Copy src _                       => valVarNames src
  | .Binary _ s1 s2 _                 => valVarNames s1 ++ valVarNames s2
  | .Unary _ src _                    => valVarNames src
  | .SignExtend _ src _               => valVarNames src
  | .ZeroExtend _ src _               => valVarNames src
  | .Truncate src _                   => valVarNames src
  | .IntToDouble src _                => valVarNames src
  | .DoubleToInt src _                => valVarNames src
  | .UIntToDouble src _               => valVarNames src
  | .DoubleToUInt src _               => valVarNames src
  | .ULongToDouble src _              => valVarNames src
  | .DoubleToULong src _              => valVarNames src
  | .Return (some v)                  => valVarNames v ++ staticVars
  | .Return none                      => staticVars
  | .JumpIfZero v _ | .JumpIfNotZero v _ => valVarNames v
  | .FunCall _ args _                 =>
      args.flatMap valVarNames ++ staticVars ++ addrTakenVars
  | .Store src ptr                    => valVarNames src ++ valVarNames ptr
  | .Load ptr _                       =>
      -- A Load through a pointer may be a load from any addr-taken variable
      valVarNames ptr ++ addrTakenVars
  | .GetAddress _ _                   => []   -- address taken ≠ value read
  | .CopyToOffset src _ _             => valVarNames src
  | .CopyFromOffset srcName _ _       => [srcName]
  | .AddPtr ptr idx _ _               => valVarNames ptr ++ valVarNames idx
  | _                                 => []   -- Label, Jump: no reads

/-- Variables FULLY OVERWRITTEN (killed) by an instruction.
    A partial write (CopyToOffset) does NOT kill the destination aggregate.
    FunCall kills the return-value variable AND all static/addr-taken variables
    (callee may write any of them through stored pointers). -/
private def dseDefSet (instr : Instruction)
    (staticVars addrTakenVars : List String) : List String :=
  match instr with
  | .Copy _ (.Var x)
  | .Binary _ _ _ (.Var x)
  | .Unary _ _ (.Var x)
  | .SignExtend _ _ (.Var x)          => [x]
  | .ZeroExtend _ _ (.Var x)          => [x]
  | .Truncate _ (.Var x)              => [x]
  | .IntToDouble _ (.Var x)           => [x]
  | .DoubleToInt _ (.Var x)           => [x]
  | .UIntToDouble _ (.Var x)          => [x]
  | .DoubleToUInt _ (.Var x)          => [x]
  | .ULongToDouble _ (.Var x)         => [x]
  | .DoubleToULong _ (.Var x)         => [x]
  | .Load _ (.Var x)                  => [x]
  | .GetAddress _ (.Var x)            => [x]
  | .CopyFromOffset _ _ (.Var x)      => [x]
  | .AddPtr _ _ _ (.Var x)            => [x]
  | .FunCall _ _ (some (.Var x))      => [x] ++ staticVars ++ addrTakenVars
  | .FunCall _ _ _                    => staticVars ++ addrTakenVars
  -- Store: writes through pointer, not to a named variable
  -- CopyToOffset: partial write, does NOT kill the aggregate (copytooffset_doesnt_kill test)
  | _                                 => []

/-- Backward transfer for one instruction:
    livein = use ∪ (liveout - def).
    If the instruction was ELIMINATED (dead), don't update the live set
    (the caller sets update=false to skip the transfer). -/
private def dseTransfer1 (liveout : List String) (instr : Instruction)
    (staticVars addrTakenVars : List String) : List String :=
  let useVars := dseUseSet instr staticVars addrTakenVars
  let defVars := dseDefSet instr staticVars addrTakenVars
  liveUnion useVars (liveRemove liveout defVars)

/-- Backward transfer for a whole block (fold from last instruction to first). -/
private def dseTransferBlock (liveout : List String) (instrs : List Instruction)
    (staticVars addrTakenVars : List String) : List String :=
  instrs.foldr
    (fun instr live => dseTransfer1 live instr staticVars addrTakenVars)
    liveout

/-- True if `instr` is a dead store given the live set AFTER it.
    An instruction is a dead store if it writes to variable x and x is not live.
    Exception: FunCall is never a dead store (it has observable side effects even
    if the return value is dead).  Store is never a dead store (writes to memory
    visible to other functions). -/
private def isDseDeadStore (instr : Instruction) (liveAfter : List String) : Bool :=
  match instr with
  | .Copy _ (.Var x)
  | .Binary _ _ _ (.Var x)
  | .Unary _ _ (.Var x)
  | .SignExtend _ _ (.Var x) | .ZeroExtend _ _ (.Var x)
  | .Truncate _ (.Var x)
  | .IntToDouble _ (.Var x) | .DoubleToInt _ (.Var x)
  | .UIntToDouble _ (.Var x) | .DoubleToUInt _ (.Var x)
  | .ULongToDouble _ (.Var x) | .DoubleToULong _ (.Var x)
  | .Load _ (.Var x)
  | .GetAddress _ (.Var x)
  | .CopyFromOffset _ _ (.Var x)
  | .AddPtr _ _ _ (.Var x)
      => !liveAfter.contains x
  | .CopyToOffset _ dstName _ =>
      -- Partial write: dead if the aggregate is not live after
      !liveAfter.contains dstName
  | _ => false   -- FunCall, Store, control flow, Label: never dead stores

/-- Compute equal liveness sets (bag equality via mutual subset check). -/
private def liveEq (a b : List String) : Bool :=
  a.all b.contains && b.all a.contains

/-- Run the dead-store-elimination pass over a function body.
    Uses backward liveness analysis (iterative dataflow) to determine which
    writes are dead, then removes those instructions.

    Algorithm:
    1. Split body into basic blocks.
    2. Compute block successors (transposed predecessor graph).
    3. Initialize livein[i] = {} for all blocks.
    4. Iterate: for each block, compute liveout = union of successor liveins,
       then compute livein = dseTransferBlock(liveout, instrs).
       Repeat until fixed point (at most n+1 rounds).
    5. Elimination pass: process each block backward, eliminating dead stores.
       When an instruction is eliminated, skip its transfer (so subsequent
       instructions in the same backward scan can also become dead).

    `staticVars` — program-wide static variable names.  These are live at every
    function exit and at every FunCall site (callee may read/write them). -/
private def deadStoreElim (body : List Instruction) (staticVars : List String)
    : List Instruction :=
  if body.isEmpty then body
  else
    -- Collect local variables whose address is taken
    let addrTakenVars : List String := body.filterMap fun instr =>
      match instr with
      | .GetAddress (.Var name) _ => some name
      | _                         => none
    let blocks := splitBlocks body
    let n := blocks.length
    let preds := computePredecessors blocks
    -- Compute successors: succs[i] = {j | i ∈ preds[j]}
    let succs : Array (List Nat) :=
      Array.mk ((List.range n).map fun i =>
        (List.range n).filter fun j =>
          (preds.getD j []).contains i)
    -- Backward data-flow: iterate until fixed point.
    -- We maintain livein[i] = dseTransferBlock(liveout[i], block[i]).
    -- liveout[i] = union(livein[j] for j in succs[i]).
    -- Initialize: livein[i] = {} for all i.
    let initLivein : Array (List String) := Array.mk (List.replicate n [])
    -- One full iteration: recompute all livein values from current livein.
    let oneIter (liveinArr : Array (List String))
        : Array (List String) × Bool :=
      (List.range n).foldl
        (fun (acc : Array (List String) × Bool) i =>
          let (arr, changed) := acc
          -- liveout(i) = union of livein of all successors
          let liveout := (succs.getD i []).foldl
            (fun lo j => liveUnion lo (arr.getD j [])) []
          -- livein(i) = backward transfer through block(i)
          let blockInstrs := (blocks.getD i (none, [])).2
          let newLivein := dseTransferBlock liveout blockInstrs staticVars addrTakenVars
          let oldLivein := arr.getD i []
          let nowChanged := !liveEq oldLivein newLivein
          (arr.set! i newLivein, changed || nowChanged))
        (liveinArr, false)
    -- Run to fixed point (n + 1 iterations always converges for monotone analyses)
    let finalLivein : Array (List String) :=
      (List.range (n + 1)).foldl
        (fun arr _ => (oneIter arr).1)
        initLivein
    -- Compute final liveout for each block (needed for elimination pass)
    let finalLiveout : Array (List String) :=
      Array.mk ((List.range n).map fun i =>
        (succs.getD i []).foldl
          (fun lo j => liveUnion lo (finalLivein.getD j [])) [])
    -- Elimination pass: for each block, process instructions backward.
    -- When we eliminate an instruction, we do NOT apply its transfer to the
    -- live set — this lets cascade eliminations happen within one pass.
    let newBlocks := (List.range n).map fun i =>
      match blocks[i]? with
      | none => []
      | some (_, instrs) =>
          let blockLiveout := finalLiveout.getD i []
          -- Backward scan: collect (isDead, instr) pairs
          let (_, annotated) :=
            instrs.foldr
              (fun instr (live, acc) =>
                let dead := isDseDeadStore instr live
                -- If dead: skip the transfer (don't propagate its use/def)
                let newLive := if dead then live
                               else dseTransfer1 live instr staticVars addrTakenVars
                (newLive, (dead, instr) :: acc))
              (blockLiveout, [])
          -- Keep only non-dead instructions
          annotated.filterMap fun (dead, instr) =>
            if dead then none else some instr
    newBlocks.foldl (· ++ ·) []

-- ---------------------------------------------------------------------------
-- Per-function optimization loop (Listing 19-6)
-- ---------------------------------------------------------------------------

/-- Run one full iteration of the optimization pipeline on `body`.
    `staticVars` is the list of all program-level static variable names; used by
    copy propagation to decide which copies to kill at FunCall sites. -/
private def oneOptIter
    (flags : OptFlags) (body : List Instruction) (st : FoldState)
    (staticVars : List String)
    : List Instruction × FoldState :=
  -- Reset within-pass constant map at the start of each iteration
  let st1 := { st with constVarMap := [] }
  -- Pass 1: constant folding
  let (body1, st2) :=
    if flags.foldConstants
    then Id.run (StateT.run (constantFoldingPass body) st1)
    else (body, st1)
  -- Pass 2: unreachable code elimination
  let body2 := if flags.eliminateUnreachable then unreachableCodeElim body1 else body1
  -- Pass 3: copy propagation
  let body3 := if flags.propagateCopies then copyPropagation body2 staticVars st2.typeEnv else body2
  -- Pass 4: dead store elimination
  let body4 := if flags.eliminateDeadStores then deadStoreElim body3 staticVars else body3
  (body4, st2)

/-- Repeat optimization passes until a fixed point (body unchanged) or fuel runs out. -/
private def optimizeFunBody
    (flags : OptFlags) (body : List Instruction) (initSt : FoldState)
    (staticVars : List String)
    : List Instruction × FoldState :=
  if !flags.foldConstants && !flags.eliminateUnreachable &&
     !flags.propagateCopies && !flags.eliminateDeadStores
  then (body, initSt)
  else
    -- Use Nat-indexed iteration for termination
    let loop : Nat → List Instruction → FoldState → List Instruction × FoldState :=
      fun fuel body st =>
        Nat.rec
          -- fuel = 0: stop
          (fun body st => (body, st))
          -- fuel = k+1: run one iteration, check fixed point
          (fun _k ih body st =>
            let oldBody := body
            let (newBody, newSt) := oneOptIter flags body st staticVars
            if newBody == oldBody then (newBody, newSt)
            else ih newBody newSt)
          fuel body st
    loop 100 body initSt

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

/-- Optimize all functions in the TACKY program according to `flags`.

    Threads the FoldState (typeEnv, floatConsts, counter) through all functions
    so that float constant labels allocated by the optimizer are globally unique
    and accumulated into the returned floatConsts / typeEnv lists.

    Returns (optimizedProgram, updatedFloatConsts, updatedTypeEnv) where the updated
    lists have new optimizer-generated float constants prepended. -/
def optimizeProgram
    (prog        : Program)
    (flags       : OptFlags)
    (typeEnv     : List (String × AST.Typ))
    (floatConsts : List (String × Float))
    : Program × List (String × Float) × List (String × AST.Typ) :=
  if !flags.foldConstants && !flags.eliminateUnreachable &&
     !flags.propagateCopies && !flags.eliminateDeadStores
  then (prog, floatConsts, typeEnv)
  else
    -- Collect all static variable names from the program's top-level declarations.
    -- Copy propagation uses this list to kill copies of static vars at FunCall sites,
    -- since a called function may read or write any static variable.
    let staticVars : List String := prog.topLevels.filterMap fun tl =>
      match tl with
      | .StaticVariable name _ _ _ => some name
      | .StaticConstant name _ _   => some name
      | _                          => none
    let initSt : FoldState := { typeEnv, floatConsts, counter := 0, constVarMap := [] }
    let (newTopLevels, finalSt) :=
      prog.topLevels.foldl (fun acc tl =>
        let (tls, st) := acc
        match tl with
        | .Function f =>
            -- Merge program-level staticVars with any external variables
            -- referenced in this function that weren't emitted as StaticVariable
            -- (e.g., `extern int x;` declarations have no TACKY top-level entry).
            let externVars := collectExternVars f.body
            let allStaticVars := (staticVars ++ externVars).eraseDups
            let (newBody, newSt) := optimizeFunBody flags f.body st allStaticVars
            (tls ++ [.Function { f with body := newBody }], newSt)
        | other =>
            (tls ++ [other], st)
      ) ([], initSt)
    ({ topLevels := newTopLevels }, finalSt.floatConsts, finalSt.typeEnv)

end Tacky
