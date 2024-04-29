# Goal

Simphony code is valid Rust code _(assuming that used types, functions and constants are imported)_.

Writing sum values as `Either<A, B>` instead of `A + B` might seem pointless or verbose.

However, using syntax that is already familiar every Rust developer out there will make it a lot easier to use Simphony.

Rust has everything we need for Simplicity, so let's define a subset of Rust—called Simphony—that translates to Simplicity.

# [Structural Types](https://en.wikipedia.org/wiki/Structural_type_system)

| Type           | Description                  | Values     | Description                  |
|----------------|------------------------------|------------|------------------------------|
| `()`           | Unit type                    | `()`       | Unit value                   |
| `Either<A, B>` | Sum of types `A` and `B`     | `Left(a)`  | Left value of `a`            |
|                |                              | `Right(b)` | Right value of `b`           |
| `(A, B)`       | Product of types `A` and `B` | `(a, b)`   | Product value of `a` and `b` |

Simfony currently adopts Simplicity's type system of units, sum and products. Simfony units are equivalent to Simplicity units, Simfony sums to Simplicity sum, and Simfony products to Simplicity products.

# Expressions

Expressions return values. Every expression has a translation into Simplicity.

## None literal

`()` is an expression

> Return the unit value.

## Product constructor

If `a` is an expression

If `b` is an expression

Then `(a, b)` is an expression

> Wrap the output of `a` and of `b` in a product value.

## Left constructor

If `a` is an expression

Then `Left(a)` is an expression

> Wrap the output of `a` in a left value.

## Right constructor

If `b` is an expression

Then `Right(b)` is an expression

> Wrap the output of `b` in a right value.

## Variable

If `v` is a variable name

Then `v` is an expression

> Return the value of variable `v`.

## Witness value

If `name` is a witness name

Then `witness("name")` is an expression

> Return the witness value under the name `name`.

The value is undefined at commit time and supplied at redeem time via a separate file.

## Jet

If `j` is the name of a jet

If `e` is an expression

Then `jet_j(e)` is an expression

> Take the output of `e` as input to jet `j` and return the jet's output.

## Block

If `s1`, ..., `sN` are statements

If `e` is an expression

Then `{s1; ...; sN; e}` is an expression

> Execute statements `s1` to `sN` in a local scope and return output of expression `e`.

## Chain

If `a` is an expression

If `b` is an expression

Then `a; b` is an expression

> Run `a` and `b` in parallel, ignore the output of `a` and return the output of `b`.

## Match

If `a` is an expression

If `b` is an expression

If `c` is an expression

If `x` is a variable name

If `y` is a variable name

Then `match a { Left(x) => b, Right(y) => c, }` is an expression

> If `a` returns a left value, then bind this value to `x` and return the output of `b`.
>
> If `b` returns a right value, then bind this value to `y` and return the output of `c`.

## Left unwrap

If `b` is an expression

Then `b.unwrap_left()` is an expression

> If `b` returns a left value, then return this value.
>
> If `b` returns a right value, then fail.

## Right unwrap

If `c` is an expression

Then `c.unwrap_right()` is an expression

> If `c` returns a left value, then fail.
>
> If `c` returns a right value, then return this value.

# Statements

Statements are components of a [block](https://github.com/BlockstreamResearch/simfony/blob/master/doc/new-syntax.md#block).

Every expression is a statement. Additionally, there are let statements.

## [Pattern Matching](https://doc.rust-lang.org/book/ch18-00-patterns.html)

We use patterns to match values against the structure of a type.

If `v` is a variable name

Then `v` is a pattern

> The variable pattern binds the value to the variable.

`_` is a pattern

> The ignore pattern does nothing.

If `p1` is a pattern

If `p2` is a pattern.

Then `(p1, p2)` is a pattern

> The product pattern splits product values. The first component is matched against pattern `p1` and the second component is matched against pattern `p2`.

## Let statement

If `p` is a pattern

If `T` is a type

If `a` is an expression

If `b` is an expression

Then `let p: T = a; b` is an expression

> Bind the output of `a` to the variables in `p` and return the output of `b`.

`T` is a type which is checked at compile time. Omit `T` to disable the check:

Then `let p = a; b` is an expression

# Macro Types

| Type           | Equivalent to    | Description                  | Values                                |
|----------------|------------------|------------------------------|---------------------------------------|
| `Option<A>`    | `Either<(), A>`  | Option of type `A`           | `None`, `Some(a)`                     |
| `bool`         | `Either<(), ()>` | Boolean                      | `false`, `true`                       |
| `u1`           | `Either<(), ()>` | 1-bit unsigned integer       | `0`, `1`                              |
| `u2`           | `(u1, u1)`       | 2-bit unsigned integer       | `0`, `1`, `2`, `3`                    |
| `u4`           | `(u2, u2)`       | 4-bit unsigned integer       | `0`, `1`, ..., `15`                   |
| `u8`           | `(u4, u4)`       | 8-bit unsigned integer       | `0`, `1`, ..., `255`                  |
| `u16`          | `(u8, u8)`       | 16-bit unsigned integer      | `0`, `1`, ..., `65535`                |
| `u32`          | `(u16, u16)`     | 32-bit unsigned integer      | `0`, `1`, ..., `4294967295`           |
| `u64`          | `(u32, u32)`     | 64-bit unsigned integer      | `0`, `1`, ..., `18446744073709551615` |
| `u128`         | `(u64, u64)`     | 128-bit unsigned integer     | strings of 32 hex digits              |
| `u256`         | `(u128, u128)`   | 256-bit unsigned integer     | strings of 64 hex digits              |

Simfony supports only structural types, i.e., units, sums and products. We provide support for familar types like Boolean and unsigned integers via type macros that are resolved to structural types during compilation.

For instance, `bool` is equivalent to the sum `Either<(), ()>` of two units. `bool` values are actually `Either<(), ()>` values. `bool` can be used anywhere `Either<(), ()>` can be used.

# Macro Expressions

We provide expressions that work on type macros. These macro expressions are resolved to equivalent expressions during compilation.

## Bit string literal

If `s` is a bit string of 2^n bits

Then `0bs` is an expression

> Return the given bit string.

We translate bit string literals using word jets because this is more compact.

> Translated as `word(0bs)`.

## Byte string literal

If `s` is a hex string of 2^n digits

Then `0xs` is an expression

> Return the given byte string.

We translate byte string literals using word jets because this is more compact.

> Translated as `word(0xs)`.

## Integer literal (u1 | u2 | u4 | u8 | u16 | u32 | u64)

If `n` is a decimal string in range of the integer type (u1 | u2 | u4 | u8 | u16 | u32 | u64)

Then `n` is an expression

> Return the given integer.

Integer literals are not available for `u128` and `u256`. Use byte string literals.

> Equivalent to `word(0xs)` where `s` is the hex encoding for integer `n`.

## None constructor

`None` is an expression

> Return the null value.

> Equivalent to `Left(())`.

## Some constructor

If `b` is an expression

Then `Some(b)` is an expression

> Wrap the output of `b` in a some value.

> Equivalent to `Right(b)`.

_(We might want to add compiler checks that the output type is indeed 𝟙 + B and not A + B for some A ≠ 𝟙.)_

## False constructor

`false` is an expression

> Return the false value.

> Equivalent to `Left(())`.

## True constructor

`true` is an expression

> Return the true value.

> Equivalent to `Right(())`.

## Option match

If `a` is an expression

If `b` is an expression

If `c` is an expression

If `y` is a variable name

Then `match a { None => b, Some(y) => c, }` is an expression

> If `a` returns a none value, then return the output of `b`.
>
> If `b` returns a some value, then bind this value to `y` and return the output of `c`.

> Equivalent to `match a { Left(_) => b, Right(y) => c, }`.

## Some unwrap

If `c` is an expression

Then `c.unwrap()` is an expression

> If `c` returns a none value, then fail.
>
> If `c` returns a some value, then return this value.

> Equivalent to `c.unwrap_right()`.

## Boolean match

If `a` is an expression

If `b` is an expression

If `c` is an expression

Then `match a { false => b, true => c, }` is an expression

> If `a` returns a false value, then return the output of `b`.
>
> If `b` returns a true value, then return the output of `c`.

> Equivalent to `match a { Left(_) => b, Right(_) => c, }`.
