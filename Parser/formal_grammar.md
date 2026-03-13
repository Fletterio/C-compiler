# Formal Grammar — Chapter 14

Extended Backus-Naur Form (EBNF) grammar for the C subset implemented through Chapter 14.

```
<program>     ::= { <declaration> }

<declaration> ::= <function-declaration>
                | <variable-declaration>

<function-declaration> ::= <decl-spec>+ <declarator> "(" <param-list> ")" ( ";" | <block> )
                         | <decl-spec>+ <fun-declarator> ( ";" | <block> )

<variable-declaration> ::= <decl-spec>+ <var-declarator> [ "=" <exp> ] ";"

<decl-spec>     ::= <type-spec> | <storage-class>

<type-spec>     ::= "int" | "long" | "unsigned" | "signed" | "double"
                  (One or more type specifiers form a type; see type-spec rules below.
                   "double" is standalone and cannot be combined with other type keywords.)

<storage-class> ::= "static" | "extern"

<declarator>    ::= "*" <declarator>                   (Chapter 14: pointer declarator)
                  | "(" <declarator> ")"               (Chapter 14: parenthesized declarator)
                  | <identifier>

<var-declarator>  ::= <declarator>
                    (same as <declarator> but may not contain inline function params)

<fun-declarator>  ::= "*" <fun-declarator>             (pointer to function)
                    | "(" <fun-declarator> ")"         (parenthesized fun-declarator)
                    | <identifier> "(" <param-list> ")"  (inline params in declarator)
                    | "(" <declarator> ")" "(" <param-list> ")"  (params follow paren group)

<abstract-declarator> ::= "*" <abstract-declarator>?  (Chapter 14: pointer abstract decl)
                         | "(" <abstract-declarator> ")"  (parenthesized abstract decl)
                         | ε                           (empty — no identifier)
                  (Used in cast expressions, e.g. `(unsigned long (*))` → Pointer(ULong))

<param-list>  ::= "void"
                | <param> { "," <param> }
                  (Note: storage-class specifiers are NOT allowed in parameter types)

<param>       ::= <type-spec>+ <declarator>            (Chapter 14: typed + declarator)

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
                | <long>                               (Chapter 11: long constant, e.g. 100l)
                | <uint>                               (Chapter 12: unsigned int constant, e.g. 42u)
                | <ulong>                              (Chapter 12: unsigned long constant, e.g. 42ul)
                | <double>                             (Chapter 13: double constant, e.g. 3.14, 1e10)
                | "(" <type-spec>+ <abstract-declarator> ")" <factor>  (Chapter 14: cast with pointer type)
                | "*" <factor>                         (Chapter 14: dereference, e.g. *ptr)
                | "&" <factor>                         (Chapter 14: address-of, e.g. &x)
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

<int>         ::= ? A constant token (decimal integer literal without suffix) ?
<long>        ::= ? A long constant token (decimal integer literal with l/L suffix, or
                    a decimal constant too large to fit in a signed 32-bit int) ?
<uint>        ::= ? An unsigned int constant token (decimal integer literal with u/U suffix,
                    value ≤ UINT_MAX = 4294967295; larger values become <ulong>) ?
<ulong>       ::= ? An unsigned long constant token (decimal integer literal with ul/lu/UL/LU
                    suffix, or a u/U-suffixed constant whose value exceeds UINT_MAX) ?
```

## Conventions

- Symbols wrapped in `<angle brackets>` are **non-terminals**.
- Symbols wrapped in `"quotes"` are **terminal tokens**.
- Symbols wrapped in `? question marks ?` are terminals whose values vary.
- `{ x }` denotes zero or more repetitions of `x`.
- `[ x ]` denotes zero or one occurrence of `x` (optional).

## Chapter 14 Changes

- **`Pointer` type**: `int *`, `long **`, `double *`, etc. are now valid types.  A pointer type
  is written as a base type followed by one or more `*` tokens.  Pointer size is 8 bytes (Quadword),
  treated like `unsigned long` for code generation.
- **`AddrOf` (`&`)** and **`Dereference` (`*`)** unary operators added to `<factor>`.
  These bind tighter than binary operators (same precedence group as other unary operators).
- **Declarators**: declarations now use a general `<declarator>` grammar instead of a bare
  `<identifier>`.  A declarator is one of:
  - `*` declarator  — pointer to the base type (e.g. `int *p`, `double **pp`)
  - `(` declarator `)` — parenthesized declarator (e.g. `int(*p)`, `long(*(lp))`)
  - `identifier` — plain identifier
  - `identifier (params)` — inline function parameters inside the declarator
  - `(declarator) (params)` — params applied to a parenthesized declarator (left-recursive)
- **Abstract declarators** (for cast expressions): same grammar without the identifier.
  e.g. `(unsigned long (*))` → `Pointer(ULong)`, `(double (*(*(*)))))` → nested pointer.
- **Null pointer constants**: only integer constant expressions with value 0 may be implicitly
  converted to a pointer type.  `0`, `0L`, `0U`, `0UL` are null pointer constants; variables and
  doubles are not.
- **Type checking for pointers**:
  - Pointer ↔ double conversions are always illegal (even explicit casts).
  - Pointer ↔ integer conversions require an explicit cast (except null pointer constants).
  - Pointers of different pointee types cannot be implicitly converted to each other.
  - Arithmetic/bitwise/shift/complement/negate operators reject pointer operands.
  - Equality (`==`, `!=`) between a pointer and an integer is only legal if the integer
    is a null pointer constant; comparing two pointers requires identical pointee types.
  - `switch` rejects pointer controlling expressions.
- **`&*e` optimization**: `AddrOf(Dereference(e))` evaluates to `e` without performing a
  dereference (so `&*null_ptr` does not crash).
- **Compound assignment through pointer**: `*f() += expr` evaluates `f()` only once by caching
  the pointer in a temporary before loading and storing through it.

## Chapter 12 Changes

- **`unsigned int` and `unsigned long` types**: `unsigned` (or `unsigned int`) and `unsigned long`
  (or `unsigned long int`, `long unsigned`, etc.) are now valid type specifiers.
- **`signed` keyword**: `signed int` = `int`; `signed long` = `long`. The `signed` keyword may
  appear alone or alongside `int`/`long` in any order. Combining `signed` and `unsigned` is an error.
- **Type-specifier combinations** (any order; one of each category):
  - `int`, `signed`, `signed int`, `int signed` → `Int`
  - `long`, `signed long`, `long int`, `int long`, `long signed`, etc. → `Long`
  - `unsigned`, `unsigned int`, `int unsigned` → `UInt`
  - `unsigned long`, `long unsigned`, `unsigned long int`, `long unsigned int`, etc. → `ULong`
- **Unsigned integer constants**: `u`/`U` suffix → `unsigned int` (or `unsigned long` if > UINT_MAX);
  `ul`/`lu`/`UL`/`LU`/`uL`/`lU`/`Ul`/`Lu` suffix → `unsigned long`.
- **Usual arithmetic conversions** (for Ch12): `ULong` > `Long` > `UInt` > `Int` in rank order.
  When mixing signed and unsigned operands:
  - `Int + UInt` → `UInt`; `Int + Long` → `Long`; `Int + ULong` → `ULong`
  - `UInt + Long` → `Long`; `UInt + ULong` → `ULong`; `Long + ULong` → `ULong`
- **Same-size reinterpretation casts** (`Int↔UInt`, `Long↔ULong`): a `Copy` instruction is
  emitted to a fresh typed temp so the backend sym table reflects the correct signedness.
- **Unsigned division** (`/`, `%` on unsigned types): uses x86 `div` instruction (not `idiv`);
  DX must be zeroed first (via `movl/movq $0, %edx/%rdx`).
- **Logical shift right** (`>>` on unsigned types): uses `shr` (not `sar`).
- **Unsigned comparisons**: condition codes A/AE/B/BE (above/below) for unsigned relational ops.
- **Switch controlling expression** can be `unsigned int`: case constants are truncated modulo 2^32
  without sign-extension (so `case 4294967295u:` is a valid unsigned int case).
- **`parseType`** (for casts/parameters) delegates to `parseDeclSpecs` but rejects storage-class
  specifiers; must be defined AFTER `parseDeclSpecs` in the source.

## Chapter 11 Changes

- **`long` type**: `long` (or `int long` / `long int`) is now a valid type specifier.
  - `long` variables occupy 8 bytes (Quadword); `int` variables occupy 4 bytes (Longword).
  - Type specifiers and storage-class specifiers may appear in **any order** in a declaration
    (`int static long x`, `static int long x`, `long static x` are all equivalent).
- **Long constants**: integer literals with an `l` or `L` suffix have type `long`.
  Decimal constants without a suffix that exceed `INT_MAX` (2 147 483 647) are
  automatically given type `long` (C §6.4.4.1).
- **Explicit casts**: `(int) expr` and `(long) expr` cast expressions to the named type.
- **Implicit conversions** (inserted by the type-checking pass):
  - Binary `+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`: usual arithmetic conversions — the
    narrower operand is sign-extended to the wider type.
  - Shift operators `<<`, `>>`: the result type is that of the **left** operand; the
    right operand is NOT subject to usual arithmetic conversions.
  - Relational/equality/logical operators: always produce `int` (0 or 1).
  - Assignment, return, function-call arguments: the value is cast to the target type.
- **Switch case truncation**: when the switch controlling expression has type `int`, each
  `case` constant is converted to `int` (wraparound modulo 2^32). This is done by the
  type-checking pass so that duplicate detection (SwitchCollection) operates on the
  already-truncated values.
- **Pipeline order** (Ch11): VarResolution → LoopLabeling → TypeCheck → SwitchCollection
  → LabelResolution → TackyGen → CodeGen → PseudoReplace → FixUp → Emit.

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
