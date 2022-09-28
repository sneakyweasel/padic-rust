#![forbid(unsafe_code)]
//! # P-adic numbers
//!
//! `padic` is a collection of utilities to convert and manipulate p-adic numbers.

use std::cmp::{max, min};
use std::fmt;

//---------------------
// CONSTANTS
//---------------------

const MAX_ARG: u64 = 1048576; // Argument maximum
const MAX_P: u64 = 32749; // Maximum prime < 2^15

//---------------------
// STRUCTS
//---------------------

#[derive(PartialEq, Clone, Debug)]
/// Rational number struct with numerator, denominator and sign.
pub struct Ratio {
    /// Numerator
    pub numer: u64,
    /// Denominator
    pub denom: u64,
    /// Sign (-1 or +1)
    pub sign: i64,
}

#[derive(PartialEq, Clone, Debug)]
/// p-adic number struct with valuation, decimal expansion and prime.
pub struct Padic {
    pub valuation: i64,
    pub expansion: Vec<u64>,
    prime: u64,
}

#[allow(dead_code)]
impl Ratio {
    /// Returns a ratio with numerator and denominator reduced to lowest terms.
    ///
    /// # Arguments
    ///
    /// * `num` - A signed integer numerator.
    /// * `denom` - A signed integer denominator.
    ///
    /// # Example
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, 4);
    /// assert_eq!(r.num, 1);
    /// ```
    pub fn new(n: i64, d: i64) -> Ratio {
        if d == 0 {
            panic!("Division by zero");
        }
        let mut sign = 1;
        if n * d < 0 {
            sign = -1;
        }
        let gcd = gcd(n.abs() as u64, d.abs() as u64);
        Ratio {
            numer: (n.abs() as u64 / gcd) as u64,
            denom: (d.abs() as u64 / gcd) as u64,
            sign: sign,
        }
    }

    /// Returns the sum of two rational numbers
    ///
    /// # Arguments
    ///
    /// * `b` - Another ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let a = Ratio::new(-2, 5);
    /// let b = Ratio::new(3, 5);
    /// assert_eq!(a.add(b), Ratio::new(1, 5));
    /// ```
    pub fn add(&self, b: Ratio) -> Ratio {
        let n = self.sign * self.numer as i64 * b.denom as i64
            + b.sign * self.denom as i64 * b.numer as i64;
        let d = self.denom as i64 * b.denom as i64;
        Ratio::new(n, d)
    }

    /// Returns the multiplication of two rational numbers
    ///
    /// # Arguments
    ///
    /// * `b` - Another ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let a = Ratio::new(-2, 5);
    /// let b = Ratio::new(3, 5);
    /// assert_eq!(a.mul(b), Ratio::new(-6, 25));
    /// ```
    pub fn mul(&self, b: Ratio) -> Ratio {
        let n = self.sign * b.sign * self.numer as i64 * b.numer as i64;
        let d = self.denom as i64 * b.denom as i64;
        Ratio::new(n, d)
    }

    /// Returns the prime factors with multiplicity of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, 15);
    /// assert_eq!(r.prime_factors(), vec![(2, 1), (3, -1), (5, -1)]);
    /// ```
    pub fn prime_factors(&self) -> Vec<(u64, i64)> {
        let fact_n = prime_factors(self.numer);
        let fact_d = prime_factors(self.denom);
        // Get the union of the two sets of prime factors
        let primes = fact_n
            .iter()
            .map(|&(p, _)| p)
            .chain(fact_d.iter().map(|&(p, _)| p))
            .collect::<Vec<u64>>();
        let mut result: Vec<(u64, i64)> = Vec::new();
        // Loop over the union of the two sets of prime factors and subtract their exponents
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

    /// Returns the float representation of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, 4);
    /// assert_eq!(r.to_float(), 0.5);
    /// ```
    pub fn to_float(&self) -> f64 {
        self.sign as f64 * (self.numer as f64 / self.denom as f64)
    }

    /// Returns the string representation of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, -4);
    /// assert_eq!(r.to_string(), "-1/2");
    /// ```
    pub fn to_string(&self) -> String {
        let mut s = String::new();
        if self.sign == -1 {
            s.push('-');
        }
        s.push_str(&self.numer.to_string());
        s.push('/');
        s.push_str(&self.denom.to_string());
        s
    }

    /// Returns the p-adic valuation of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(71, 9);
    /// assert_eq!(r.padic_valuation(3), -2);
    /// ```
    pub fn padic_valuation(&self, prime: u64) -> i64 {
        if is_prime(prime) == false {
            panic!("{} is not a prime", prime);
        }
        for &(p, pow) in &self.prime_factors() {
            if p == prime {
                return pow;
            }
        }
        return 0;
    }

    /// Returns the p-adic absolute value of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(71, 9);
    /// assert_eq!(r.padic_absolute(3), Ratio::new(9, 1));
    /// ```
    pub fn padic_absolute(&self, prime: u64) -> Ratio {
        if is_prime(prime) == false {
            panic!("{} is not a prime", prime);
        }
        let valuation = self.padic_valuation(prime);
        let exp = prime.pow((valuation.abs()) as u32);
        if self.numer == 0 {
            return Ratio::new(0, 1);
        } else if valuation < 0 {
            return Ratio::new(exp as i64, 1);
        } else {
            return Ratio::new(1, exp as i64);
        }
    }

    /// Convert the ratio into a p-adic number.
    ///
    /// Info: <https://math.stackexchange.com/a/1187037>
    ///
    /// # Arguments
    ///
    /// * `prime` - A prime number.
    /// * `precision` - A positive integer.
    ///
    /// # Examples

    /// 3-adic expansion of 2/5 with precision of 5 -> 1,1,2,1,0
    ///
    /// * +2/5 = 1 - 3 * 1/5
    /// * -1/5 = 1 - 3 * 2/5
    /// * -2/5 = 2 - 3 * 4/5
    /// * -4/5 = 1 - 3 * 3/5
    /// * -3/5 = 0 - 3 * 1/5
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, 5);
    /// let p = r.to_padic(3, 5);
    /// assert_eq!(p.expansion, vec![1, 1, 2, 1, 0]);
    /// ```
    pub fn to_padic(&self, prime: u64, precision: u64) -> Padic {
        // Validate input
        if self.numer > MAX_ARG || self.denom > MAX_ARG as u64 {
            panic!("Ratio too large");
        }
        if prime < 2 || prime > MAX_P {
            panic!("Prime out of range");
        }
        if is_prime(prime) == false {
            panic!("{} is not a prime", prime);
        }
        if precision < 1 {
            panic!("Precision out of range");
        }

        // Get the p-adic absolute value of the ratio
        let mut expansion = vec![0; precision as usize];

        let mut digit;
        let mut ratio = self.clone();
        for i in 0..precision as usize {
            digit = ratio.next_digit(prime).0;
            ratio = ratio.next_digit(prime).1;
            expansion[i] = digit;
        }

        // Initialize padic number
        return Padic {
            valuation: self.padic_valuation(prime),
            expansion: expansion,
            prime: prime,
        };
    }

    /// Returns the next digit of the p-adic expansion.
    ///
    /// # Arguments
    ///
    /// * `prime` - A prime number.
    ///
    /// ```
    /// use padic::Ratio;
    /// let a = Ratio::new(2, 5);
    /// assert_eq!(a.next_digit(3), (1, Ratio::new(-1, 5)));
    /// ```
    pub fn next_digit(&self, prime: u64) -> (u64, Ratio) {
        let p_ratio = Ratio::new(prime as i64, 1);
        for digit in 0..prime {
            let d_ratio = Ratio::new(digit as i64, 1);

            for num in 1..=self.denom {
                let num_ratio = Ratio::new(-(num as i64), self.denom as i64);
                let result1 = p_ratio.mul(num_ratio.clone());
                let result2 = d_ratio.add(result1.clone());
                if result2 == *self {
                    // println!("{} = {} - {} * {}", self, digit, prime, num_ratio);
                    return (digit, num_ratio);
                }
            }
        }
        panic!("P-adic expansion next digit computation error.")
    }
}

impl fmt::Display for Ratio {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

//---------------------
// HELPER FUNCTIONS
//---------------------

/// Exponent of prime in number
///
/// # Arguments
/// * `num` - A positive integer.
/// * `prime` - An prime number.
///
/// # Examples
/// ```
/// use padic::exp_prime;
/// let exp = exp_prime(5, 3);
/// assert_eq!(exp, 2);
/// ```
pub fn exp_prime(num: i64, prime: u64) -> i64 {
    if is_prime(prime) == false {
        panic!("{} is not a prime", prime);
    }
    let mut exp = 0;
    let mut num = num;
    while num % (prime as i64) != 0 {
        exp += 1;
        num /= prime as i64;
    }
    return exp;
}

/// Greatest common denominator - Stein's algorithm
/// <https://rosettacode.org/wiki/Greatest_common_divisor#Rust>
///
/// # Arguments
/// * `a` - A positive integer.
/// * `b` - A positive integer.
///
/// # Examples
///
/// ```
/// use padic::gcd;
/// assert_eq!(gcd(6, 3), 3);
/// assert_eq!(gcd(12, 4), 4);
/// ```
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

/// Returns a vector of (prime, exponent) tuples for a given number prime factorization.
/// <https://rosettacode.org/wiki/Prime_decomposition#Rust>
///
/// # Arguments
/// * `num` - A positive integer.
///
/// # Examples
/// ```
/// use padic::prime_factors;
/// let factors = prime_factors(60);
/// assert_eq!(factors, vec![(2, 2), (3, 1), (5, 1)]);
/// ```
pub fn prime_factors(num: u64) -> Vec<(u64, i64)> {
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

/// Returns modular multiplicative inverse of a number.
/// <https://rosettacode.org/wiki/Modular_inverse#Rust>
///
/// # Arguments
///
/// * `a` - A positive integer.
/// * `modulo` - A positive integer.
///
/// # Examples
///
/// ```
/// use padic::mod_inv;
/// assert_eq!(mod_inv(42, 2017), 1969);
/// ```
pub fn mod_inv(a: i64, modulo: i64) -> i64 {
    if gcd(a as u64, modulo as u64) != 1 {
        panic!("modular inverse does not exist");
    }
    let mut mn = (modulo, a);
    let mut xy = (0, 1);

    while mn.1 != 0 {
        xy = (xy.1, xy.0 - (mn.0 / mn.1) * xy.1);
        mn = (mn.1, mn.0 % mn.1);
    }

    while xy.0 < 0 {
        xy.0 += modulo;
    }
    xy.0
}

/// Check if number is prime.
/// <https://rosettacode.org/wiki/Primality_by_trial_division#Rust>
///
/// # Arguments
/// * `num` - A positive integer.
///
/// # Examples
/// ```
/// use padic::is_prime;
/// assert_eq!(is_prime(5), true);
/// assert_eq!(is_prime(6), false);
/// ```
pub fn is_prime(num: u64) -> bool {
    if num < 2 {
        return false;
    }
    if num == 2 {
        return true;
    }
    if num % 2 == 0 {
        return false;
    }
    let mut i = 3;
    while i * i <= num {
        if num % i == 0 {
            return false;
        }
        i += 2;
    }
    return true;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_padic_test() {
        let r = Ratio::new(2, 5);
        let p = r.to_padic(3, 10);
        assert_eq!(p.valuation, 0);
        assert_eq!(p.expansion, vec![1, 1, 2, 1, 0, 1, 2, 1, 0, 1]);
    }

    #[test]
    fn valuation_test() {
        let ratio = Ratio::new(140, 297);
        assert_eq!(ratio.padic_valuation(2), 2);
        assert_eq!(ratio.padic_valuation(3), -3);
        assert_eq!(ratio.padic_valuation(5), 1);
        assert_eq!(ratio.padic_valuation(7), 1);
        assert_eq!(ratio.padic_valuation(11), -1);
    }

    #[test]
    fn norm_test() {
        let ratio = Ratio::new(140, 297);
        assert_eq!(ratio.padic_absolute(2), Ratio::new(1, 4));
        assert_eq!(ratio.padic_absolute(3), Ratio::new(27, 1));
        assert_eq!(ratio.padic_absolute(5), Ratio::new(1, 5));
        assert_eq!(ratio.padic_absolute(11), Ratio::new(11, 1));
    }

    #[test]
    fn exp_prime_test() {
        let exp = exp_prime(5, 3);
        assert_eq!(exp, 2);
    }

    #[test]
    fn ratio_prime_decomposition_test() {
        let ratio1 = Ratio::new(2, 15);
        let ratio_prime_factors1 = ratio1.prime_factors();
        assert_eq!(ratio_prime_factors1, vec![(2, 1), (3, -1), (5, -1)]);
        let ratio2 = Ratio::new(-35, 7);
        let ratio_prime_factors2 = ratio2.prime_factors();
        assert_eq!(ratio_prime_factors2, vec![(5, 1)]);
    }

    #[test]
    fn ratio_creation_test() {
        let ratio1 = Ratio::new(21, 12);
        let test_ratio = Ratio {
            numer: 7,
            denom: 4,
            sign: 1,
        };
        assert_eq!(ratio1, test_ratio);
        let ratio2 = Ratio::new(-21, -12);
        let test_ratio = Ratio {
            numer: 7,
            denom: 4,
            sign: 1,
        };
        assert_eq!(ratio2, test_ratio);
    }

    #[test]
    fn ratio_float_test() {
        let ratio1 = Ratio::new(-9, 2);
        assert_eq!(ratio1.to_float(), -4.5);
    }

    #[test]
    fn ratio_string_test() {
        let ratio1 = Ratio::new(-9, 2);
        assert_eq!(ratio1.to_string(), "-9/2");
    }
}
