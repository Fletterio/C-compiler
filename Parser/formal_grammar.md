# Formal Grammar — Chapter 9

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented in Chapter 9.

```
<program>     ::= { <function-declaration> }

<function-declaration> ::= "int" <identifier> "(" <param-list> ")" ( ";" | <block> )

<param-list>  ::= "void"
                | "int" <identifier> { "," "int" <identifier> }

<block>       ::= "{" { <block-item> } "}"

<block-item>  ::= <statement> | <variable-declaration> | <function-declaration>

<variable-declaration> ::= "int" <identifier> [ "=" <exp> ] ";"

<statement>   ::= "return" <exp> ";"
                | <exp> ";"
                | "if" "(" <exp> ")" <statement> [ "else" <statement> ]
                | <block>
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

<for-init>    ::= <variable-declaration>
                | [ <exp> ] ";"

<exp>         ::= <factor>
                | <exp> <binop> <exp>
                | <exp> "?" <exp> ":" <exp>
                | <exp> <assign-op> <exp>

<factor>      ::= <int>
                | <identifier> "(" <arg-list> ")"
                | <identifier>
                | <unop> <factor>
                | "++" <factor> | "--" <factor>
                | <factor> "++" | <factor> "--"
                | "(" <exp> ")"

<arg-list>    ::= [ <exp> { "," <exp> } ]

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
- `{ x }` denotes zero or more repetitions of `x`.
- `[ x ]` denotes zero or one occurrence of `x` (optional).

## Chapter 9 Changes

- `<program>` is now a sequence of `<function-declaration>` items (previously exactly one function).
- `<function-declaration>` may end with `;` (prototype) or `<block>` (definition).
- `<param-list>` replaces the former `"void"` placeholder: it is either `"void"` or a non-empty list of `int`-typed parameters.
- `<block-item>` now includes `<function-declaration>` for local function declarations inside function bodies.  Local function **definitions** (with a body) are a parse error inside another function.
- `<factor>` now recognises function calls: `<identifier> "(" <arg-list> ")"`.
- `<arg-list>` is the list of argument expressions, separated by commas.  No trailing comma is allowed.

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
- Function calls (`identifier "(" arg-list ")"`) are recognised in `parseFactor` by one token of lookahead: `Identifier` followed by `(` is a call.
- The ternary `?:` operator is parsed like a right-associative binary operator where the "operator" is `"?" <exp> ":"`. The middle subexpression between `?` and `:` is parsed at precedence 0 (any expression, including assignments).
- **Dangling-else** is resolved greedily: an `else` always binds to the nearest enclosing `if`.
- Lvalue validity (left side of `=`, and operand of `++`/`--`) is enforced in the variable resolution pass.
- **`for` loop scoping**: a variable declared in `<for-init>` is scoped to the entire loop (condition, post expression, and body), but not visible outside the loop.
- **Loop labeling**: the semantic analysis pass (after variable resolution) annotates every loop, `break`, `continue`, `switch`, `case`, and `default` with a unique ID.  A **global counter** is used across all functions so label IDs are unique program-wide.  `break` may appear inside any loop or `switch`; `continue` may only appear inside a loop.
- **Switch case collection** (extra credit): a separate pass after loop labeling collects the `case`/`default` entries for each `switch` and validates that no case value is duplicated and there is at most one `default`.
- **`case` expressions** must be integer constants (literal `<int>` or negated `<int>`).
- **Labeled statements** (`label:`) and **`goto`** are extra credit from Chapter 6. Labels are function-scoped; cross-function gotos are detected as errors.
- The **System V AMD64 calling convention** is used: the first 6 integer arguments are passed in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`, `%r9` (in order). Additional arguments are passed on the stack. The return value is in `%rax`.
- **Stack alignment**: before every `call` instruction, `%rsp` must be 16-byte aligned. The compiler ensures this by rounding the local stack frame to a multiple of 16, and adding padding when an odd number of arguments are passed on the stack.
- **`@PLT` suffix**: on Linux, calls to functions not defined in the current translation unit use the `@PLT` suffix for position-independent code compatibility.
