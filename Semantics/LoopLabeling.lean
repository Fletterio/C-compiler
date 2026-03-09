import AST.AST

/-
  Semantic analysis pass: loop labeling.

  This pass traverses the AST and annotates every loop, `break`, `continue`,
  `switch`, `case`, and `default` statement with a unique string ID:

  - Each loop (`while`, `do`, `for`) and each `switch` statement receives a
    fresh ID stored in its `Option String` field.  From this ID, TACKY
    generation derives concrete break and continue labels:
      break label    = "brk_" ++ id   (e.g. "brk_loop.5")
      continue label = "cnt_" ++ id   (e.g. "cnt_loop.5")

  - Each `break` statement is annotated with the ID of its innermost enclosing
    loop *or* switch.  Each `continue` statement is annotated with the ID of
    its innermost enclosing *loop* only (not switch, because `continue` inside
    a switch without an enclosing loop is a semantic error).

  - Each `case` and `default` statement receives its own fresh ID stored in
    its `Option String` field; TACKY generation uses this as a jump target.
    The collected `(value, label)` list is NOT populated here; that is done by
    the subsequent switch-case-collection pass.

  Chapter 9: the pass processes ALL function definitions in the program,
  maintaining a GLOBAL counter across functions so that labels in different
  functions have different numbers (e.g. "loop.0" in foo, "loop.1" in bar).
  This prevents label conflicts and satisfies the label naming scheme test.

  The pass reports an error if:
    - A `break` statement appears outside any loop or switch.
    - A `continue` statement appears outside any loop.
-/

namespace Semantics

/-- The monad for loop labeling: state counter (for generating unique IDs)
    together with error reporting (for misplaced break/continue). -/
private abbrev LabelM := StateT Nat (Except String)

/-- Generate a fresh label base string `"<base>.<n>"`. -/
private def makeLabelBase (base : String) : LabelM String := do
  let n ← get
  modify (· + 1)
  return s!"{base}.{n}"

/-
  `labelStatement` and `labelBlockItem` are mutually recursive because
  `Compound` statements contain block items which may themselves be statements.
-/
mutual

/-- Annotate a statement with loop labels.
    `breakLbl`: the ID base of the innermost enclosing loop or switch — used to
                annotate `break` statements.
    `contLbl`:  the ID base of the innermost enclosing *loop* (never a switch)
                — used to annotate `continue` statements.
    `switchLbl`: the ID base of the innermost enclosing switch — used to
                 validate `case` and `default` statements.
    When a new loop is entered, both `breakLbl` and `contLbl` are updated to
    the new loop's ID.  When a switch is entered, only `breakLbl` is updated
    (so `continue` still refers to the surrounding loop, if any). -/
private partial def labelStatement
    (stmt      : AST.Statement)
    (breakLbl  : Option String)   -- innermost loop-or-switch ID (for break)
    (contLbl   : Option String)   -- innermost loop ID (for continue)
    (switchLbl : Option String)   -- innermost enclosing switch ID (for case/default validation)
    : LabelM AST.Statement := do
  match stmt with
  | .Break _ =>
      match breakLbl with
      | none   => throw "break statement outside of loop or switch"
      | some l => return .Break (some l)
  | .Continue _ =>
      match contLbl with
      | none   => throw "continue statement outside of loop"
      | some l => return .Continue (some l)
  -- while loop: generate an ID, then recurse with it as both break and continue target
  | .While cond body _ => do
      let base  ← makeLabelBase "loop"
      let body' ← labelStatement body (some base) (some base) switchLbl
      return .While cond body' (some base)
  -- do-while loop: same structure as while
  | .DoWhile body cond _ => do
      let base  ← makeLabelBase "loop"
      let body' ← labelStatement body (some base) (some base) switchLbl
      return .DoWhile body' cond (some base)
  -- for loop: same structure as while
  | .For init cond post body _ => do
      let base  ← makeLabelBase "loop"
      let body' ← labelStatement body (some base) (some base) switchLbl
      return .For init cond post body' (some base)
  -- switch: generates a new break target, but continues still go to the enclosing loop
  | .Switch exp body _ _ => do
      let base  ← makeLabelBase "switch"
      let body' ← labelStatement body (some base) contLbl (some base)
      return .Switch exp body' (some base) []   -- cases filled by SwitchCollection
  -- case: must appear inside a switch; each gets a unique jump label
  | .Case n body _ => do
      match switchLbl with
      | none   => throw "case statement outside of switch"
      | some _ =>
          let caseBase ← makeLabelBase "case"
          let body'    ← labelStatement body breakLbl contLbl switchLbl
          return .Case n body' (some caseBase)
  -- default: must appear inside a switch
  | .Default body _ => do
      match switchLbl with
      | none   => throw "default statement outside of switch"
      | some _ =>
          let defBase ← makeLabelBase "default"
          let body'   ← labelStatement body breakLbl contLbl switchLbl
          return .Default body' (some defBase)
  -- if: recurse into both branches, propagating the same break/continue targets
  | .If cond thenStmt elseOpt => do
      let then' ← labelStatement thenStmt breakLbl contLbl switchLbl
      match elseOpt with
      | none =>
          return .If cond then' none
      | some elseStmt => do
          let else' ← labelStatement elseStmt breakLbl contLbl switchLbl
          return .If cond then' (some else')
  -- compound: recurse into each block item
  | .Compound items => do
      let items' ← items.mapM (fun i => labelBlockItem i breakLbl contLbl switchLbl)
      return .Compound items'
  -- labeled statement: recurse into the body
  | .Labeled label body => do
      let body' ← labelStatement body breakLbl contLbl switchLbl
      return .Labeled label body'
  -- statements with no sub-statements: return unchanged
  | .Return _ | .Expression _ | .Goto _ | .Null => return stmt

/-- Annotate a block item with loop labels by delegating to `labelStatement`
    for statement items; declaration items are returned unchanged.
    Chapter 9: `FD` (local function declaration) items are also returned as-is. -/
private partial def labelBlockItem
    (item      : AST.BlockItem)
    (breakLbl  : Option String)
    (contLbl   : Option String)
    (switchLbl : Option String)
    : LabelM AST.BlockItem := do
  match item with
  | .S stmt => return .S (← labelStatement stmt breakLbl contLbl switchLbl)
  | .D _    => return item
  | .FD _   => return item

end

/-- Label loops within a single function's body, using the given counter state.
    Returns the annotated body and the updated counter state. -/
private def labelFunctionBody (body : List AST.BlockItem) : LabelM (List AST.BlockItem) := do
  body.mapM (fun item => labelBlockItem item none none none)

/-- Entry point for the loop labeling pass.
    Processes all function definitions in the program sequentially, maintaining
    a GLOBAL counter across all functions.  This ensures that labels in different
    functions have different numbers, preventing conflicts.
    Returns an error if a `break` or `continue` appears outside an appropriate
    enclosing statement. -/
def labelLoops (p : AST.Program) : Except String AST.Program := do
  -- Process all top-level items with a single shared counter
  let action : LabelM (List AST.TopLevel) :=
    p.topLevels.mapM fun tl =>
      match tl with
      | .FunDef fd => do
          let body' ← labelFunctionBody fd.body
          return .FunDef { fd with body := body' }
      | .FunDecl fd =>
          -- Declarations have no body: skip them
          return .FunDecl fd
  match action.run 0 with
  | .error msg         => .error msg
  | .ok (topLevels', _) => .ok { p with topLevels := topLevels' }

end Semantics
