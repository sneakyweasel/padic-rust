use std::cmp::{max, min};

mod ratio {
    #[derive(PartialEq, Debug)]
    pub struct Ratio {
        n: u64,
        d: u64,
        sign: bool,
    }

    #[derive(PartialEq, Debug)]
    pub struct Padic {
        v: u64,
        d: Vec<i64>,
    }

    // RATIO IMPLEMENTATION

    impl Ratio {
        // Constructors
        fn new(n: i64, d: i64) -> Ratio {
            if d == 0 {
                panic!("Division by zero");
            }
            let sign = n * d >= 0;
            let gcd = gcd(n as u64, d as u64);
            Ratio {
                n: (n.abs() as u64 / gcd) as u64,
                d: (d.abs() as u64 / gcd) as u64,
                sign: sign,
            }
        }

        // Prime factorization with multiplicity
        fn prime_factors_with_multiplicity(&self) -> Vec<(u64, i64)> {
            let fact_n = prime_factors_with_multiplicity(self.n);
            let fact_d = prime_factors_with_multiplicity(self.d);
            // Get the union of the two sets of prime factors
            let primes = fact_n
                .iter()
                .map(|&(p, _)| p)
                .chain(fact_d.iter().map(|&(p, _)| p))
                .collect::<Vec<u64>>();
            let mut result: Vec<(u64, i64)> = Vec::new();
            // Loop over the union of the two sets of prime factors and substract their exponents
            for prime in &primes {
                let mut pow_n = 0;
                let mut pow_d = 0;
                for &(p, pow) in fact_n.iter() {
                    if p == *prime {
                        pow_n = pow;
                    }
                }
                for &(p, pow) in fact_d.iter() {
                    if p == *prime {
                        pow_d = pow;
                    }
                }
                let diff = pow_n - pow_d;
                // Discard prime factors with exponent 0
                if diff != 0 {
                    result.push((*prime, diff));
                }
            }
            return result;
        }

        // Overloaded operators
        fn to_string(&self) -> String {
            let mut s = String::new();
            if !&self.sign {
                s.push('-');
            }
            s.push_str(&self.n.to_string());
            s.push('/');
            s.push_str(&self.d.to_string());
            s
        }

        // Convert ratio to p-adic number
        fn into_padic(q: Ratio, prime: u64, precision: u64, debug: bool) -> Padic {
            let num = q.n;
            let denom = q.d;

            // Validate input
            if num > AMX || denom > AMX {
                panic!("Ratio too large");
            }
            if prime < 2 || prime > PMAX {
                panic!("Prime out of range");
            }
            if precision < 1 {
                panic!("Precision out of range");
            }
            if debug {
                println!("Rational to p-adic conversion");
                println!("  Ratio: {}/{}", num, denom);
                println!("  Prime: {}", prime);
                println!("  Precision: {}", precision);
            }

            // Initialize padic number
            let padic = Padic {
                v: 0,
                d: vec![0; EMX],
            };
            return padic;
        }
    }
}

// HELPER FUNCTIONS

// Greatest common denominator - Stein's algorithm
// https://rosettacode.org/wiki/Greatest_common_divisor#Rust
pub fn gcd(a: u64, b: u64) -> u64 {
    match ((a, b), (a & 1, b & 1)) {
        ((x, y), _) if x == y => y,
        ((0, x), _) | ((x, 0), _) => x,
        ((x, y), (0, 1)) | ((y, x), (1, 0)) => gcd(x >> 1, y),
        ((x, y), (0, 0)) => gcd(x >> 1, y >> 1) << 1,
        ((x, y), (1, 1)) => {
            let (x, y) = (min(x, y), max(x, y));
            gcd((y - x) >> 1, x)
        }
        _ => unreachable!(),
    }
}

// Generate tuples of (prime, exponent) for a given number
pub fn prime_factors_with_multiplicity(num: u64) -> Vec<(u64, i64)> {
    let mut factors = vec![];
    let mut n = num;
    let mut d = 2;
    while n > 1 {
        let mut count = 0;
        while n % d == 0 {
            count += 1;
            n /= d;
        }
        if count > 0 {
            factors.push((d, count));
        }
        d += 1;
        if d * d > n {
            if n > 1 {
                factors.push((n, 1));
            }
            break;
        }
    }
    factors
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_test() {
        assert_eq!(gcd(6, 3), 3);
        assert_eq!(gcd(12, 4), 4);
    }

    #[test]
    fn ratio_prime_decomposition_test() {
        let ratio1 = Ratio::new(2, 15);
        let ratio_prime_factors1 = ratio1.prime_factors_with_multiplicity();
        assert_eq!(ratio_prime_factors1, vec![(2, 1), (3, -1), (5, -1)]);
        let ratio2 = Ratio::new(-35, 7);
        let ratio_prime_factors2 = ratio2.prime_factors_with_multiplicity();
        assert_eq!(ratio_prime_factors2, vec![(5, 1)]);
    }

    #[test]
    fn ratio_creation_test() {
        let ratio1 = Ratio::new(21, 12);
        let test_ratio = Ratio {
            n: 7,
            d: 4,
            sign: true,
        };
        assert_eq!(ratio1, test_ratio);
        let ratio2 = Ratio::new(-21, -12);
        let test_ratio = Ratio {
            n: 7,
            d: 4,
            sign: true,
        };
        assert_eq!(ratio2, test_ratio);
    }
}
