# P-adic numbers

[![crate](https://img.shields.io/crates/v/padic.svg)](https://crates.io/crates/padic)
[![documentation](https://docs.rs/padic/badge.svg)](https://docs.rs/padic)
[![minimum rustc 1.31](https://img.shields.io/badge/rustc-1.31+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)

A collection of tools for p-adic numbers in Rust.

This includes a p-adic type and a rational type.

## Status

This library is currently in development. It is not yet ready for use.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
padic = "0.1.1"
```

## From rational number to p-adic number

- Reduce ratio to lowest terms
- Convert ratio into a list of tuples of prime factors and their exponents
- Retrieve p-adic norm
- Retrieve p-adic absolute value
- Compute p-adic expansion

## Helpers functions

- Prime factors with multiplicity (a: i64 / b: i64) -> Vec<(prime: u64, exp: u64)>
- Greatest common divisor (Stein's algorithm)
- Modular multiplicative inverse

## TODOs

- [x] Extract sign information to transform ratio into a tuple of unsigned integer variables
- [x] Reduce ratio to lowest terms using GCD (Stein's algorithm)
- [x] Prime decomposition returning vector of (prime, exponent) tuples.
- [x] P-adic valuation of rational number
- [x] P-adic norm of rational number
- [ ] P-adic expansion of rational number
- [ ] Convert p-adic expansion into rational number
- [ ] Basic operations for p-adic numbers

## License

MIT
