# P-adic numbers

Library for working with p-adic numbers in Rust.

## Status

This library is currently in development. It is not yet ready for use.

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
