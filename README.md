# P-adic numbers

[![crate](https://img.shields.io/crates/v/padic.svg)](https://crates.io/crates/padic)
[![documentation](https://docs.rs/padic/badge.svg)](https://docs.rs/padic)
[![minimum rustc 1.31](https://img.shields.io/badge/rustc-1.31+-red.svg)](https://rust-lang.github.io/rfcs/2495-min-rust-version.html)

A collection of tools for p-adic numbers in Rust.

This includes a p-adic type and a rational type.

P-adic notation for the expansion is currently left to right.

## Status

This library is currently in development and might be unstable.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
padic = "0.1.6"
```

```rust
use padic::Ratio;
let ratio = Ratio::new(2, 5);
let padic = ratio.to_padic(3, 12);
assert_eq!(padic.valuation, 0);
assert_eq!(padic.expansion, vec![1, 1, 2, 1, 0, 1, 2, 1, 0, 1, 2, 1]);
assert_eq!(padic.expansion_cycle(), [1, 2, 1, 0]);
assert_eq!(padic.to_string(), "... 1 2 1 0 1 2 1 0 1 2 1 1");
```

## Helpers functions

- Prime factors with multiplicity (a: i64 / b: i64) -> Vec<(prime: u64, exp: u64)>
- Extended Euclidean algorithm with Bezout coefficients
- Modular multiplicative inverse
- Double cursor window cycle detection for repeating digits in p-adic expansion

## Resources

- <https://en.wikipedia.org/wiki/P-adic_number>
- <https://www.cut-the-knot.org/blue/p-adicExpansion.shtml>

## TODOs

### Ratio

- [x] Extract sign information to transform ratio into a tuple of unsigned integer variables
- [x] Reduce ratio to lowest terms using extended Euclidean algorithm
- [x] Basic arithmetic operations for rational numbers
- [x] Implement extended greatest common divisor to extract Bezout coefficients
- [x] Modular multiplicative inverse using EGCD

### P-adic

- [x] Prime decomposition returning vector of (prime, exponent) tuples.
- [x] P-adic valuation of rational number
- [x] P-adic norm of rational number
- [x] P-adic expansion of rational number with given precision
- [x] P-adic string representation with given precision and given valuation
- [x] Cyclic detection in p-adic expansion (Sliding window algorithm)
- [ ] P-adic arithmetic operations
- [ ] Convert p-adic expansion into rational number

### Bugs / Features

- [ ] If the valuation is larger than the precision, the expansion is not correct
- [ ] If the precision is lower than the cycle length, the cycle is not detected

## License

MIT
