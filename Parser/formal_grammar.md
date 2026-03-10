# Formal Grammar — Chapter 10

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented in Chapter 10.

```
<program>     ::= { <declaration> }

<declaration> ::= <function-declaration>
                | <variable-declaration>

<function-declaration> ::= [ <storage-class> ] "int" [ <storage-class> ]
                           <identifier> "(" <param-list> ")" ( ";" | <block> )

<variable-declaration> ::= [ <storage-class> ] "int" [ <storage-class> ]
                           <identifier> [ "=" <exp> ] ";"

<storage-class> ::= "static" | "extern"

<param-list>  ::= "void"
                | "int" <identifier> { "," "int" <identifier> }

<block>       ::= "{" { <block-item> } "}"

<block-item>  ::= <statement> | <variable-declaration> | <function-declaration>

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

## Chapter 10 Changes

- `<program>` is now a sequence of `<declaration>` items: either function
  declarations/definitions or file-scope variable declarations.
- `<declaration>` adds an optional `<storage-class>` specifier (`static` or
  `extern`) that may appear before or after the `int` type keyword.
- `<variable-declaration>` at file scope becomes a top-level item.  At block
  scope it is still a `<block-item>`.
- `<function-declaration>` and `<variable-declaration>` both accept an optional
  storage-class specifier.  The parser accepts both orderings (`static int x`
  and `int static x`) and rejects invalid combinations in the semantic pass.

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
- **`for` loop scoping**: a variable declared in `<for-init>` is scoped to the entire loop (condition, post expression, and body), but not visible outside the loop.  Storage-class specifiers in a `for`-loop initializer are a semantic error.
- **Loop labeling**: the semantic analysis pass (after variable resolution) annotates every loop, `break`, `continue`, `switch`, `case`, and `default` with a unique ID.  A **global counter** is used across all functions so label IDs are unique program-wide.
- **Switch case collection** (extra credit): a separate pass after loop labeling collects the `case`/`default` entries for each `switch` and validates that no case value is duplicated and there is at most one `default`.
- **`case` expressions** must be integer constants (literal `<int>` or negated `<int>`).
- **Labeled statements** (`label:`) and **`goto`** are extra credit from Chapter 6. Labels are function-scoped; cross-function gotos are detected as errors.
- **Storage-class specifiers** (Chapter 10):
  - `static` at file scope → internal linkage (symbol not visible outside the TU).
  - `extern` at file scope → external linkage; no storage emitted if no initializer.
  - `static` at block scope → static storage duration, no linkage; variable renamed to `<orig>.<n>` internally.
  - `extern` at block scope → refers to the file-scope variable of the same name; variable is NOT renamed.
  - `static` on a block-scope function declaration → semantic error.
  - `extern` with an initializer → semantic error.
  - Storage-class in a `for`-loop initializer → semantic error.
- **Static variables**: file-scope variables with static storage are placed in `.data` (nonzero initializer) or `.bss` (zero/absent initializer) in the emitted assembly.  They are accessed via RIP-relative addressing (`name(%rip)`).
- **The System V AMD64 calling convention** is used: the first 6 integer arguments are passed in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`, `%r9` (in order). Additional arguments are passed on the stack. The return value is in `%rax`.
- **Stack alignment**: before every `call` instruction, `%rsp` must be 16-byte aligned.
- **`@PLT` suffix**: on Linux, calls to functions not defined in the current translation unit use the `@PLT` suffix for position-independent code compatibility.
