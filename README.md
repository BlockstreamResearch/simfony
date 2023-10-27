A high level DSL for Simplicity. This is a work in progress and is not yet ready for production use. The language is designed to be simple and easy to use. It is inspired by rust syntax and is statically typed. The syntax will be extended in the future to support more features.

**Please do note that the new language is under active development, and is not ready for production use**

## Simplicity's need for high level DSL

Simplicity introduces a groundbreaking low-level programming language and machine model meticulously crafted for blockchain-based smart contracts. The primary goal is to provide a streamlined and comprehensible foundation that facilitates static analysis and encourages reasoning through formal methods. While the elegance of the language itself is distilled into something as succinct as fitting onto a T-shirt, it's important to note that the simplicity of the language doesn't directly equate to simplicity in the development process. This project revolves around demystifying and simplifying the complexities involved in this ecosystem.

The distinguishing aspects that set Simplicity apart from conventional programming languages are:

- **Distinct Programming Paradigm**: The Simplicity programming model requires a paradigm shift from conventional programming. It hinges on reasoning about programs in a functional sense with a focus on combinators. This intricacy surpasses even popular functional languages like Haskell, with its own unique challenges.
- **Exceptional Low-Level Nature**: Unlike high-level languages such as JavaScript or Python, Simplicity operates at an extremely low level, resembling assembly languages. This design choice enables easier reasoning about the formal semantics of programs, but is really work on directly.


## s-lang

s-lang is a high level DSL that compiles to Simplicity. It is designed to be a simple, easy to use language that is familiar to developers. It is a work in progress and is not yet ready for production use.

**Please do note that the new language is under active development, which implies the existence of bugs and several incomplete features.**

The DSL's purpose is to make programming in Simplicity accessible even to developers who have no prior familiarity with it. It is designed to be a simple, easy to use language based on Javascript that is familiar to developers. This does not produce the most efficient Simplicity code, and attempts to do no optimizations. Future versions of the compiler will attempt to optimize the code.

## Installation

The compiler is written in rust and can be installed using cargo.

```bash
git clone https://github.com/sanket1729/s-lang.git
cd s-lang
cargo build
./target/debug/simpc <prog.simpl> <sig.wit>
```

Optionally, you can also install the compiler using cargo.

```bash
cargo install --path .
```

## Usage

The compiler takes two arguments, the first is the path to the s-lang program, and the second is the path to the witness json file. The compiler outputs the Simplicity program to stdout.

Test out your installation by running the following command.
```bash
./target/debug/s-lang examples/program.simpl examples/witness.json
```

## Language Syntax

The language syntax is inspired by Javascript. The language is statically typed, and in most cases, the type of every variable is inferred by the compiler. The language is whitespace insensitive, and semicolons are mandatory. The syntax will be extended in the future to support more features.

### Variables:

Variables are declared using the `let` keyword. The type of the variable is inferred by the compiler. The type of the variable can be specified by using the `:` operator.

```javascript
let x : u32 = 1;
```

### Constants:

- `()`: The unit value. This is the only value of type `𝟙`(also referred as unit type).
- `0xs`: A 256 bit hex string. s is a hex string containing exactly 64 characters.
- `NUM : TYPE`: A number of type `TYPE` where `TYPE` is desribed below.

```javascript
let x : u32 = 1;
let y : u1 = 0;
let pk : u256 = 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef;
```

### Types:

Every simplicity expression has a type. The type of a variable is usually inferred by the compiler. But for constants, the type usually needs to be specified. The following are the types supported by the language.

- `u1`: The type of booleans. It has two values, `0` and `1`.
- `u2`: The type of 2 bit unsigned integers. It has four values, `0`, `1`, `2` and `3`.
- `u4`: The type of 4 bit unsigned integers.
- `u8`: The type of 8 bit unsigned integers.
- `u16`: The type of 16 bit unsigned integers.
- `u32`: The type of 32 bit unsigned integers.
- `u64`: The type of 64 bit unsigned integers.
- `u256`: The type of 256 bit unsigned integers.

## Expressions:

Expressions are the building blocks of the language. Every expression has a type. The following are the expressions supported by the language.

- `v`: A variable.
- `()`: The unit value. This is the only value of type `𝟙`(also referred as unit type).
- `0xs`: A 256 bit hex string. s is a hex string containing exactly 64 characters.
- `0bs`: A 256 bit binary string. s is a binary string containing exactly 256 characters.
- `wit_name`: A witness of called `name`. The value are typically not available at program commitment time. The value for these are provided in the witness json file at spend time. The key for the value is the `name` of the witness.
- `jet_j(expr1, expr2, ..)`: A jet with name `j` with parameters `expr1`, `expr2`. The source type of the jet is `expr1 x (expr2 x (expr3 x ..))`. Jets with unit source type can be called without any parameters.
- `(expr1, expr2)`: A pair of expressions.
- `{statement1; statement2; expr}`: A block expression. The type of the block expression is the type of the last statement.
- `assertl(expr)`: Assert that the expression is left sum type. If the expression `expr` is of type `A + B`. Then the expression `assertl(expr)` is of type `A`. This is similar to unwrapping a `Result` in rust.
- `assertr(expr)`: Assert that the expression is right sum type. If the expression `expr` is of type `A + B`. Then the expression `assertr(expr)` is of type `B`. This is similar to unwrapping a `Result` in rust.


For example, the below program computes the maximum of two 32 bit unsigned integers. The jet `jet_max32` computes the maximum of two 32 bit unsigned integers. The jet `jet_verify` verifies that the first argument

```rust
let wit_max; /* Declare a witness variable named max*/
let a: u32 = 1; /* Declare a variable named a of type u32 */
let b: u32 = 2; /* Declare a variable named b of type u32 */
let c = jet_max_32(a, b); /*Compute the max of a and b and save it in c.*/
let cmp = jet_eq_32(c, wit_max); /* Check that the input witness is same as c*/
jet_verify(cmp); /*Assert that the comparison is true*/
/*The same expression can also be inlined as*/
jet_verify(jet_eq_32(jet_max_32(a, b), wit_max));
```
The witness file for the above program is as follows. Note that the file has a single key `max` because the witness variable is named `wit_max`.

```json
{
    "max": "00000002"
}
```

## Statements:

The following are the statements supported by the language.

- `let v = expr;`: A variable declaration. The type of the variable is inferred by the compiler.
- `let v : TYPE = expr;`: A variable declaration. The type of the variable is `TYPE`.
- `let (v1, v2) = expr;`: A variable declaration. The type of the variable is inferred by the compiler. The expression must evaluate to a pair.
- `jet_name(expr)`: A jet call.

```rust
let wit_sig;
let pk : u256 = <pk>;
let msg: u256 = <msg>;
jet_bip0340_verify(pk, msg, wit_sig);
```

## Jets:

All supported jets in s-lang can be found in documentation. The documentation can be generated using the following command.

```bash
cargo doc --open
```
The catalogue of jets can be found in
target/doc/simplicity/jet/enum.Elements.html.

## Examples

Scoped variables work like in regular programming languages. See other examples in the `example_progs` directory.

```rust
let v1 = {
    let v2 = {
        let v7 : u32 = 10;
        let v3 = {
            let v4 : u32 = 2;
            let v5 : u32 = 3;
            jet_verify(jet_eq_32(v7, 10)); /* Can use upper scope variables here.*/
            let v7 : u32 = 7; /* Can also shadow the upper scope here.*/
            jet_max_32(jet_max_32(v4, v5),v7) /* Rust like, missing ; here is the return type of expression.*/
        };
        jet_verify(jet_eq_32(v7, 10)); /* Upper scope is same just like regular Programming languages*/
        jet_min_32(v7, v3) /*Return value of v2 block*/
    };
    v2
};
jet_verify(jet_eq_32(7, v1));
```



An emulation of CTV in simplicity.

```rust
/* This program is an emulation of CTV using simplicity */
/* Instead of specifying the template hash as in BIP CTV,
we require the user to specify all the components of the sighash
that they want to commit.*/
/* Supporting scriptsighash requires conditional that we don't yet support.*/

let sha2_ctx = jet_sha_256_ctx_8_init();
let sha2_ctx = jet_sha_256_ctx_8_add_4(sha2_ctx, jet_version());
let sha2_ctx = jet_sha_256_ctx_8_add_4(sha2_ctx, jet_lock_time());
let sha2_ctx = jet_sha_256_ctx_8_add_4(sha2_ctx, jet_num_inputs());
let sha2_ctx = jet_sha_256_ctx_8_add_32(sha2_ctx, jet_input_sequences_hash());
let sha2_ctx = jet_sha_256_ctx_8_add_4(sha2_ctx, jet_num_outputs());
let sha2_ctx = jet_sha_256_ctx_8_add_32(sha2_ctx, jet_outputs_hash());
let sha2_ctx = jet_sha_256_ctx_8_add_4(sha2_ctx, jet_current_index());
let ctv_hash : u256 = jet_sha_256_ctx_8_finalize(sha2_ctx);

let expected_hash : u256 = 0x126a5c6e2d95fdf8fa0ac2927803de62fbca645527f514e523ac1d3d39afcc68;
assert(jet_eq_256(ctv_hash, expected_hash));
```
