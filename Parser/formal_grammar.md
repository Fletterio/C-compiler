# Formal Grammar — Chapter 8

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented in Chapter 8.

```
<program>     ::= <function>

<function>    ::= "int" <identifier> "(" "void" ")" "{" <block-item>* "}"

<block-item>  ::= <statement> | <declaration>

<declaration> ::= "int" <identifier> [ "=" <exp> ] ";"

<statement>   ::= "return" <exp> ";"
                | <exp> ";"
                | "if" "(" <exp> ")" <statement> [ "else" <statement> ]
                | "{" <block-item>* "}"
                | "while" "(" <exp> ")" <statement>
                | "do" <statement> "while" "(" <exp> ")" ";"
                | "for" "(" <for-init> [ <exp> ] ";" [ <exp> ] ")" <statement>
                | "break" ";"
                | "continue" ";"
                | "switch" "(" <exp> ")" <statement>       (extra credit)
                | "case" <int> ":" <statement>              (extra credit)
                | "default" ":" <statement>                 (extra credit)
                | "goto" <identifier> ";"                   (extra credit ch6)
                | <identifier> ":" <statement>              (extra credit ch6)
                | ";"

<for-init>    ::= <declaration>
                | [ <exp> ] ";"

<exp>         ::= <factor>
                | <exp> <binop> <exp>
                | <exp> "?" <exp> ":" <exp>
                | <exp> <assign-op> <exp>

<factor>      ::= <int> | <identifier>
                | <unop> <factor>
                | "++" <factor> | "--" <factor>
                | <factor> "++" | <factor> "--"
                | "(" <exp> ")"

<binop>       ::= "-" | "+" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>"
              | "&&" | "||" | "==" | "!=" | "<" | "<=" | ">" | ">="

<assign-op>   ::= "=" | "+=" | "-=" | "*=" | "/=" | "%="
              | "&=" | "|=" | "^=" | "<<=" | ">>="

<unop>        ::= "-" | "~" | "!"

<identifier>  ::= ? An identifier token ?

<int>         ::= ? A constant token ?
```

## Conventions

- Symbols wrapped in `<angle brackets>` are **non-terminals**.
- Symbols wrapped in `"quotes"` are **terminal tokens**.
- Symbols wrapped in `? question marks ?` are terminals whose values vary.

## Notes

- `<exp>` is parsed using **precedence climbing**. Precedence table (high to low):
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
  - `?` → 3 (ternary conditional; **right-associative**; middle subexp has prec 0)
  - `=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=` → 1 (assignment; **right-associative**)
  - All other binary operators are **left-associative**.
- The ternary `?:` operator is parsed like a right-associative binary operator where the "operator" is `"?" <exp> ":"`. The middle subexpression between `?` and `:` is parsed at precedence 0 (any expression, including assignments).
- **Dangling-else** is resolved greedily: an `else` always binds to the nearest enclosing `if`.
- Lvalue validity (left side of `=`, and operand of `++`/`--`) is enforced in the variable resolution pass.
- **`for` loop scoping**: a variable declared in `<for-init>` is scoped to the entire loop (condition, post expression, and body), but not visible outside the loop.
- **Loop labeling**: the semantic analysis pass (after variable resolution) annotates every loop, `break`, `continue`, `switch`, `case`, and `default` with a unique ID.  `break` may appear inside any loop or `switch`; `continue` may only appear inside a loop.
- **Switch case collection** (extra credit): a separate pass after loop labeling collects the `case`/`default` entries for each `switch` and validates that no case value is duplicated and there is at most one `default`.
- **`case` expressions** must be integer constants (literal `<int>` or negated `<int>`).
- **Labeled statements** (`label:`) and **`goto`** are extra credit from Chapter 6. Labels are function-scoped.
- The `goto` target and labeled-statement disambiguation uses one token of lookahead: `<identifier> ":"` → label, otherwise → expression statement.
