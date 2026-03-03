# Formal Grammar — Chapter 1

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented in Chapter 1.

```
<program>    ::= <function>

<function>   ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"

<statement>  ::= "return" <exp> ";"

<exp>        ::= <int>

<identifier> ::= ? An identifier token ?

<int>        ::= ? A constant token ?
```

## Conventions

- Symbols wrapped in `<angle brackets>` are **non-terminals** (correspond 1-to-1 with AST nodes in `AST.lean`).
- Symbols wrapped in `"quotes"` are **terminal tokens** (keywords or punctuation).
- Symbols wrapped in `? question marks ?` are terminals whose values vary (identifier names, integer values).
