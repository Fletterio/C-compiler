import AST.AST

/-
  Semantic analysis pass (extra credit): label resolution.

  This pass validates labeled statements and goto statements within each
  function:
    1. No two labeled statements in the same function may share a label name.
    2. Every goto must target a label that is defined somewhere in the same
       function body.

  Labels in C are function-scoped, so this pass collects every label in the
  entire function body (regardless of nesting) before checking goto targets.

  The pass does not modify the AST — it only validates it, returning `()`
  on success or an error message on failure.
-/

namespace Semantics

/-
  `collectLabelsStmt` and `collectLabelsItem` are mutually recursive through
  `Compound`: a compound statement contains block items, which may be
  statements with labels.  Same mutual recursion applies to `checkGotosStmt`
  and `checkGotosItem`.  All four are `partial` to allow Lean to accept the
  definitions without structural termination proofs.
-/
mutual

/-- Collect all label names defined in a statement (recursively).
    Recurses into every sub-statement so that labels nested inside loops,
    switches, and compounds are all visible to `goto` statements anywhere
    in the same function. -/
private partial def collectLabelsStmt : AST.Statement → List String
  | .Labeled label stmt => label :: collectLabelsStmt stmt
  | .If _ thenStmt elseOpt =>
      let thenLabels := collectLabelsStmt thenStmt
      let elseLabels := match elseOpt with | none => [] | some s => collectLabelsStmt s
      thenLabels ++ elseLabels
  | .Compound items => items.foldl (fun acc i => acc ++ collectLabelsItem i) []
  | .While _ body _   => collectLabelsStmt body
  | .DoWhile body _ _ => collectLabelsStmt body
  | .For _ _ _ body _ => collectLabelsStmt body
  | .Switch _ body _ _ => collectLabelsStmt body
  | .Case _ body _    => collectLabelsStmt body
  | .Default body _   => collectLabelsStmt body
  | _ => []

/-- Collect all label names defined in a block item. -/
private partial def collectLabelsItem : AST.BlockItem → List String
  | .S stmt => collectLabelsStmt stmt
  | .D _    => []

end

/-- Fail if any label name appears more than once in the list. -/
private def checkDuplicates : List String → Except String Unit
  | [] => .ok ()
  | l :: rest =>
      if rest.contains l then .error s!"Duplicate label '{l}'"
      else checkDuplicates rest

mutual

/-- Check that all goto targets in a statement are in `defined`.
    Recurses into all sub-statements so that goto targets inside loops and
    switch bodies are also validated. -/
private partial def checkGotosStmt (defined : List String) : AST.Statement → Except String Unit
  | .Goto target =>
      if defined.contains target then .ok ()
      else .error s!"goto to undefined label '{target}'"
  | .Labeled _ stmt => checkGotosStmt defined stmt
  | .If _ thenStmt none => checkGotosStmt defined thenStmt
  | .If _ thenStmt (some elseStmt) => do
      checkGotosStmt defined thenStmt
      checkGotosStmt defined elseStmt
  | .Compound items => do
      let _ ← items.mapM (fun i => checkGotosItem defined i)
      return ()
  | .While _ body _    => checkGotosStmt defined body
  | .DoWhile body _ _  => checkGotosStmt defined body
  | .For _ _ _ body _  => checkGotosStmt defined body
  | .Switch _ body _ _ => checkGotosStmt defined body
  | .Case _ body _     => checkGotosStmt defined body
  | .Default body _    => checkGotosStmt defined body
  | _ => .ok ()

/-- Check that all goto targets in a block item are in `defined`. -/
private partial def checkGotosItem (defined : List String) : AST.BlockItem → Except String Unit
  | .S stmt => checkGotosStmt defined stmt
  | .D _    => .ok ()

end

/-- Entry point for the label resolution pass.
    Collects all labels in the function body, checks for duplicates, then
    verifies that all goto targets exist. -/
def resolveLabels (p : AST.Program) : Except String Unit := do
  let f := p.func
  let labels := f.body.foldl (fun acc i => acc ++ collectLabelsItem i) []
  checkDuplicates labels
  let _ ← f.body.mapM (fun i => checkGotosItem labels i)
  return ()

end Semantics
