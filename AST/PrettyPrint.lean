import AST.AST

namespace AST

private def ind (depth : Nat) : String :=
  String.mk (List.replicate (depth * 2) ' ')

def Exp.prettyPrint (e : Exp) (depth : Nat := 0) : String :=
  match e with
  | .Constant n => s!"{ind depth}Constant({n})"

def Statement.prettyPrint (s : Statement) (depth : Nat := 0) : String :=
  match s with
  | .Return e =>
    s!"{ind depth}Return(\n{e.prettyPrint (depth + 1)}\n{ind depth})"

def FunctionDef.prettyPrint (f : FunctionDef) (depth : Nat := 0) : String :=
  let body := f.body.prettyPrint (depth + 2)
  s!"{ind depth}Function(\n{ind (depth+1)}name=\"{f.name}\",\n{ind (depth+1)}body={body}\n{ind depth})"

def Program.prettyPrint (p : Program) : String :=
  s!"Program(\n{p.func.prettyPrint 1}\n)"

end AST
