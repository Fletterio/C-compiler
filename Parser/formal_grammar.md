# Formal Grammar — Chapter 4

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented in Chapter 4.

```
<program>    ::= <function>

<function>   ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"

<statement>  ::= "return" <exp> ";"

<exp>        ::= <factor> | <exp> <binop> <exp>

<factor>     ::= <int> | <unop> <factor> | "(" <exp> ")"

<binop>      ::= "-" | "+" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>"
             | "&&" | "||" | "==" | "!=" | "<" | "<=" | ">" | ">="

<unop>       ::= "-" | "~" | "!"

<identifier> ::= ? An identifier token ?

<int>        ::= ? A constant token ?
```

## Conventions

- Symbols wrapped in `<angle brackets>` are **non-terminals** (correspond 1-to-1 with AST nodes in `AST.lean`).
- Symbols wrapped in `"quotes"` are **terminal tokens** (keywords or punctuation).
- Symbols wrapped in `? question marks ?` are terminals whose values vary (identifier names, integer values).

## Notes

- `<exp>` is parsed using **precedence climbing** rather than a directly recursive descent grammar.  The ambiguous `<exp> <binop> <exp>` rule is resolved by associativity and precedence (high to low):
  - `*`, `/`, `%` → 50 (multiplicative)
  - `+`, `-` → 45 (additive)
  - `<<`, `>>` → 40 (shift)
  - `<`, `<=`, `>`, `>=` → 35 (relational)
  - `==`, `!=` → 30 (equality)
  - `&` → 25 (bitwise AND)
  - `^` → 20 (bitwise XOR)
  - `|` → 15 (bitwise OR)
  - `&&` → 10 (logical AND)
  - `||` → 5 (logical OR)
  - All binary operators are **left-associative**: `1 - 2 - 3` parses as `(1 - 2) - 3`.
- `<factor>` handles unary operators and atoms; it is the highest-priority form.  Unary `-` and `~` apply to a `<factor>`, not a full `<exp>`, so they always bind more tightly than any binary operator.
- Parentheses `"(" <exp> ")"` have no corresponding AST node — they affect grouping only.
- The decrement operator `--` does not appear in this grammar; the parser will reject it.
