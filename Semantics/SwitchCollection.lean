import AST.AST

/-
  Semantic analysis pass (extra credit): switch case collection.

  After the loop-labeling pass has assigned unique labels to every `case` and
  `default` statement, this pass:

    1. Traverses the AST looking for `Switch` nodes.
    2. For each switch, collects all `Case` and `Default` statements that
       directly belong to it (recursing into if/while/compound bodies, but
       *not* into nested `Switch` bodies, which have their own case lists).
    3. Validates that no integer value appears more than once and that there is
       at most one `default` clause.
    4. Attaches the collected `List (Option Int × String)` to the `Switch` node
       so TACKY generation can emit the comparison jump table.

  Chapter 9: updated to process all function definitions in the program.

  This pass must run *after* the loop-labeling pass because it depends on
  `Case` and `Default` nodes already having their unique labels filled in.
-/

namespace Semantics

/-- A single entry in a switch's case list.
    `(some n, lbl)` represents `case n:` jumping to `lbl`.
    `(none, lbl)` represents `default:` jumping to `lbl`. -/
private abbrev CaseEntry := Option Int × String

/-
  `collectCasesFromStmt` and `collectCasesFromItem` are mutually recursive
  through `Compound`.
-/
mutual

/-- Collect case entries from a statement that is part of a switch body.
    Recurses into sub-statements (if, while, do, for, compound, labeled) but
    stops at nested `Switch` nodes, whose cases belong to that inner switch. -/
private partial def collectCasesFromStmt : AST.Statement → Except String (List CaseEntry)
  | .Case n body (some lbl) => do
      let inner ← collectCasesFromStmt body
      return (some n, lbl) :: inner
  | .Case _ _ none       =>
      .error "internal error: Case has no label — loop labeling must run first"
  | .Default body (some lbl) => do
      let inner ← collectCasesFromStmt body
      return (none, lbl) :: inner
  | .Default _ none       =>
      .error "internal error: Default has no label — loop labeling must run first"
  | .Switch _ _ _ _   => return []   -- nested switch: its cases belong to it, not us
  | .Compound items => do
      let lists ← items.mapM collectCasesFromItem
      return lists.foldl (· ++ ·) []
  | .If _ t none     => collectCasesFromStmt t
  | .If _ t (some e) => do
      let tE ← collectCasesFromStmt t
      let eE ← collectCasesFromStmt e
      return tE ++ eE
  | .While _ b _   => collectCasesFromStmt b
  | .DoWhile b _ _ => collectCasesFromStmt b
  | .For _ _ _ b _ => collectCasesFromStmt b
  | .Labeled _ s   => collectCasesFromStmt s
  | _              => return []

/-- Collect case entries from a block item. -/
private partial def collectCasesFromItem : AST.BlockItem → Except String (List CaseEntry)
  | .S stmt => collectCasesFromStmt stmt
  | .D _    => return []
  | .FD _   => return []

end

/-- Validate that a case list contains no duplicate integer values and at most
    one `default` clause.  The loop-labeling pass guarantees every entry has
    a valid label, so only value uniqueness is checked here. -/
private def validateCases (entries : List CaseEntry) : Except String Unit := do
  let defaults := entries.filter (fun (v, _) => v.isNone)
  if defaults.length > 1 then
    throw "duplicate default case in switch statement"
  let values := entries.filterMap (fun (v, _) => v)
  let rec checkDup : List Int → Except String Unit
    | []      => .ok ()
    | n :: rest =>
        if rest.contains n then .error s!"duplicate case value {n} in switch statement"
        else checkDup rest
  checkDup values

/-
  `processSwitchesStmt` and `processSwitchesItem` are mutually recursive
  through `Compound`.
-/
mutual

/-- Traverse a statement, processing all `Switch` nodes found within it.
    For each switch:
      1. Recursively process nested switches in the body first.
      2. Collect and validate the case list from the (now-processed) body.
      3. Attach the case list to the switch node. -/
private partial def processSwitchesStmt : AST.Statement → Except String AST.Statement
  | .Switch exp body lbl _ => do
      let body'  ← processSwitchesStmt body     -- handle nested switches first
      let cases  ← collectCasesFromStmt body'
      validateCases cases
      return .Switch exp body' lbl cases
  | .If cond t eOpt => do
      let t' ← processSwitchesStmt t
      match eOpt with
      | none   => return .If cond t' none
      | some e => return .If cond t' (some (← processSwitchesStmt e))
  | .Compound items => do
      let items' ← items.mapM processSwitchesItem
      return .Compound items'
  | .While cond body lbl => do
      return .While cond (← processSwitchesStmt body) lbl
  | .DoWhile body cond lbl => do
      return .DoWhile (← processSwitchesStmt body) cond lbl
  | .For init cond post body lbl => do
      return .For init cond post (← processSwitchesStmt body) lbl
  | .Labeled label s => do
      return .Labeled label (← processSwitchesStmt s)
  | .Case n body lbl => do
      return .Case n (← processSwitchesStmt body) lbl
  | .Default body lbl => do
      return .Default (← processSwitchesStmt body) lbl
  | stmt => return stmt

/-- Traverse a block item, processing switch nodes. -/
private partial def processSwitchesItem : AST.BlockItem → Except String AST.BlockItem
  | .S stmt => return .S (← processSwitchesStmt stmt)
  | item    => return item

end

/-- Entry point for the switch case collection pass.
    Chapter 9: traverses ALL function definitions in the program.
    Collects and validates case lists for every `switch` statement in each
    function, and attaches the lists to the AST nodes.
    Must be called *after* the loop-labeling pass. -/
def collectSwitchCases (p : AST.Program) : Except String AST.Program := do
  let topLevels' ← p.topLevels.mapM fun tl =>
    match tl with
    | .FunDef fd => do
        let body' ← fd.body.mapM processSwitchesItem
        return AST.TopLevel.FunDef { fd with body := body' }
    | .FunDecl fd =>
        -- Declarations have no body: skip
        return AST.TopLevel.FunDecl fd
    | .VarDecl vd =>
        -- Chapter 10: file-scope variable declarations have no body
        return AST.TopLevel.VarDecl vd
  return { p with topLevels := topLevels' }

end Semantics
