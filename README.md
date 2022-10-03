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
padic = "0.1.4"
```

```rust
use padic::Ratio;
let ratio = Ratio::new(1, 3);
let padic = r.to_padic(5, 6);
assert_eq!(padic.valuation, 0);
assert_eq!(padic.expansion, vec![3, 1, 3, 1, 3, 2]);
assert_eq!(padic.to_string(), "...3 1 3 1 3 2");
```

## Helpers functions

- Prime factors with multiplicity (a: i64 / b: i64) -> Vec<(prime: u64, exp: u64)>
- Greatest common divisor (Stein's algorithm)
- Modular multiplicative inverse

## Resources

- <https://en.wikipedia.org/wiki/P-adic_number>
- <https://www.cut-the-knot.org/blue/p-adicExpansion.shtml>

## TODOs

### Ratio

- [x] Extract sign information to transform ratio into a tuple of unsigned integer variables
- [x] Reduce ratio to lowest terms using GCD (Stein's algorithm)
- [x] Basic arithmetic operations for rational numbers
- [x] Modular multiplicative inverse
- [ ] Implement extended greatest common divisor to extract Bezout coefficients

### P-adic

- [x] Prime decomposition returning vector of (prime, exponent) tuples.
- [x] P-adic valuation of rational number
- [x] P-adic norm of rational number
- [x] P-adic expansion of rational number with given precision
- [x] P-adic string representation with given precision and given valuation
- [ ] P-adic arithmetic operations
- [ ] Cyclic detection in p-adic expansion
- [ ] Convert p-adic expansion into rational number
- [ ] Basic operations for p-adic numbers

### Bugs

- [ ] If the valuation is larger than the precision, the expansion is not correct

## License

MIT
