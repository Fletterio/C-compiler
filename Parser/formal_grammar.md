# Formal Grammar — Chapter 2

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented in Chapter 2.

```
<program>    ::= <function>

<function>   ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"

<statement>  ::= "return" <exp> ";"

<exp>        ::= <int> | <unop> <exp> | "(" <exp> ")"

<unop>       ::= "-" | "~"

<identifier> ::= ? An identifier token ?

<int>        ::= ? A constant token ?
```

## Conventions

- Symbols wrapped in `<angle brackets>` are **non-terminals** (correspond 1-to-1 with AST nodes in `AST.lean`).
- Symbols wrapped in `"quotes"` are **terminal tokens** (keywords or punctuation).
- Symbols wrapped in `? question marks ?` are terminals whose values vary (identifier names, integer values).

## Notes

- The `<exp>` rule is recursive: a unary expression `<unop> <exp>` contains another `<exp>`, allowing arbitrarily nested operations like `-(~(-~-(-4)))`.
- Parentheses `"(" <exp> ")"` have no corresponding AST node — they affect grouping only. `1`, `(1)`, and `((((1))))` all produce the same `Constant(1)` node.
- The decrement operator `--` does not appear in this grammar; the parser must reject it.
