# Nominal Types

| Type                 | Equivalent to                      | Description                          | Values                          |
|----------------------|------------------------------------|--------------------------------------|---------------------------------|
| `[A; 1]`             | `A`                                | Array of size one                    | `[a]`                           |
| `[A; 2*N]`           | `([A;N], [A;N])`                   | Array of size 2*N where N > 0        | `[a, b, ..., z]`                |
| `[A; 2*N+1]`         | `([A;N+1], [A;N])`                 | Array of size 2*N+1 where N > 0      | `[a, b, ..., z]`                |
| `List<A; 2>`         | `Option<A>`                        | List of less than 2 elements         | `list!()`, `list!(a)`           |
| `List<A; 2^(N + 1)>` | `(Option<[A; 2^N]>, List<A; 2^N>)` | List of less than 2^(N + 1) elements | `list()`, `list!(a, b, ..., z)` |

## Array

An array of type `[A; N]` holds exactly `N` values of type `A`. The array length `N` must be positive: 1, 2, 3, 4, 5, ...

We use arrays when we know exactly how many elements we need to process.

An array is structurally equivalent to a balanced binary tree of element values.

## List

A list of type `List<A; N>` holds between 0 and N - 1 values (inclusive). The length bound `N` must be a power of two greater one: 2, 4, 8, 16, 32, ... The actual list length can be any number below the bound.

We use lists when we don't know how many elements we need to process. Unused parts of the list don't take up space on the blockchain.

Internally, a list splits its elements into _blocks_. Each block is as long as a power of two: 1, 2, 4, 8, 16, ... Take the number of elements of a list as a binary number. For every power of two, there is a bit that is true or false. The true bits show the blocks that the list uses.

| List                    | Blocks                        |
|-------------------------|-------------------------------|
| `[a]`                   | `[a]`                         |
| `[a, b]`                | `[a, b]`                      |
| `[a, b, c]`             | `[a, b]` `[c]`                |
| `[a, b, c, d]`          | `[a, b, c, d]`                |
| `[a, b, c, d, e]`       | `[a, b, c, d]` `[e]`          |
| `[a, b, c, d, e, f]`    | `[a, b, c, d]` `[e, f]`       |
| `[a, b, c, d, e, f, g]` | `[a, b, c, d]` `[e, f]` `[g]` |

# Expressions

## Array constructor

If `a1`, ..., `aN` are expressions

Then `[a1, ..., aN]` is an expression

> Wrap output of `a1`, ..., `aN` in an array.

## List constructor

If `a1`, ..., `aN` are expressions

Then `list![a1, ..., aN]` is an expression

> Wrap output of `a1`, ..., `aN` in a list.

Note that lists are immutable, like everything in Simphony. To modify a list, you need to create a new one.

## List fold without context

If `lst` is an expression

If `acc` is an expression

If `f` is a function name

Then `fold(lst, acc, f)` is an expression

> Execute function `f(element, accumulator) → accumulator` on all elements of `lst`, using `acc` as initial accumulator. Return the final accumulator.

## List fold with context

If `lst` is an expression

If `acc` is an expression

If `ctx` is an expression

If `f` is a function name

Then `fold(lst, acc, ctx f)` is an expression

> Execute function `f(element, accumulator, context) → accumulator` on all elements of `lst`, using `acc` as initial accumulator and `ctx` as readonly context. Return the final accumulator.

## For-while loop without context

If `N` is a power _of a power_ of two: 2, 4, 16, 256, 65536, ...

If `acc` is an expression

If `f` is a function name

Then `forWhile::<N>(acc, f)` is an expression

> Execute function `f(counter, accumulator) → accumulator` for counter values from zero to the maximum, using `acc` as initial accumulator. Return the final accumulator.

The counter is always as wide as it has to be to count all loop iterations. In other words, the counter width is the binary logarithm of the number of iterations.

| Number of iterations | Counter width |
|----------------------|---------------|
| 2 = 2¹               | 1 bit         |
| 4 = 2²               | 2 bits        |
| 16 = 2⁴              | 4 bits        |
| 256 = 2⁸             | 8 bits        |
| 65536 = 2¹⁶          | 16 bits       |

## For-while loop with context

If `N` is a power _of a power_ of two: 2, 4, 16, 256, 65536, ...

If `acc` is an expression

If `ctx` is an expression

If `f` is a function name

Then `forWhile::<N>(acc, ctx, f)` is an expression

> Execute function `f(counter, context, accumulator) → accumulator` for counter values from zero to the maximum, using `acc` as initial accumulator and `ctx` as readonly context. Return the final accumulator.

# Statements

## Function declaration

If `f` is a function name

If `p1`, ..., `pN` are variable identifiers

If `e` is an expression

Then `fn f(p1, ..., pN) -> e` is a function declaration

> Declare function `f` with parameters `p1` to `pN`. Take expression `e` as function body.
