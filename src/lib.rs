#![warn(clippy::all, clippy::pedantic)]
#![allow(
    clippy::missing_docs_in_private_items,
    clippy::implicit_return,
    clippy::shadow_reuse,
    clippy::print_stdout,
    clippy::wildcard_enum_match_arm,
    clippy::else_if_without_else
)]
#![forbid(unsafe_code)]

//! # P-adic numbers
//!
//! `padic` is a collection of utilities to convert and manipulate p-adic numbers.

use std::fmt;

//---------------------
// CONSTANTS
//---------------------

const MAX_ARG: usize = 1_048_576; // Argument maximum
const MAX_P: usize = 32_749; // Maximum prime < 2^15

//---------------------
// STRUCTS
//---------------------

#[derive(PartialEq, Eq, Clone, Debug)]
/// p-adic number struct with valuation, decimal expansion and prime.
pub struct Padic {
    pub valuation: isize,
    pub expansion: Vec<usize>,
    prime: usize,
}

impl fmt::Display for Padic {
    /// Returns a formatted string representing the padic expansion
    ///
    /// # Example
    ///
    /// ```
    /// use padic::Ratio;
    /// let ratio_zero = Ratio::new(1, 3);
    /// assert_eq!(ratio_zero.to_padic(5, 6).to_string(), "... 3 1 3 1 3 2");
    /// let ratio_plus = Ratio::new(25, 3);
    /// assert_eq!(ratio_plus.to_padic(5, 6).to_string(), "... 3 1 3 2 0 0");
    /// let ratio_minus = Ratio::new(1, 75);
    /// assert_eq!(ratio_minus.to_padic(5, 6).to_string(), "... 1 3 1 , 3 2");
    /// ```
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut expansion: Vec<String> = self
            .expansion
            .clone()
            .iter()
            .map(|&d| d.to_string())
            .collect();

        if self.valuation < 0 {
            expansion.insert(-self.valuation as usize, ",".to_string());
            expansion.pop();
        }

        if self.valuation > 0 {
            for _i in 0..self.valuation {
                expansion.insert(0, "0".to_string());
                expansion.pop();
            }
        }
        expansion.reverse();
        let str = "... ".to_string() + expansion.join(" ").trim_end();
        fmt.write_str(&str)
    }
}

#[allow(dead_code)]
impl Padic {
    /// Create new padic number
    ///
    /// # Example
    ///
    /// ```
    /// use padic::Padic;
    /// let padic = Padic::new(1, vec!(1, 1, 2, 2), 5);
    /// assert_eq!(padic.valuation, 1);
    /// ```
    ///
    /// # Panics
    ///
    /// Will panic if the provided prime is not prime
    #[must_use]
    pub fn new(valuation: isize, expansion: Vec<usize>, prime: usize) -> Padic {
        assert!(is_prime(prime), "Prime provided {} is not prime.", prime);
        Padic {
            valuation,
            expansion,
            prime,
        }
    }

    /// Returns a vector of the digits of the p-adic expansion cycle
    /// Might be empty if the p-adic expansion precision is too small
    ///
    /// # Example
    ///
    /// ```
    /// use padic::Ratio;
    /// let ratio = Ratio::new(2, 5);
    /// let padic = ratio.to_padic(3, 12);
    /// println!("{:?}", padic.expansion);
    /// println!("{:?}", padic.to_string());
    /// assert_eq!(padic.expansion_cycle(), vec![1, 2, 1, 0]);
    /// ```
    #[must_use]
    pub fn expansion_cycle(&self) -> Vec<usize> {
        let (offset, size) = cycle_detection(&self.expansion);
        self.expansion[offset..offset + size].to_vec()
    }

    /// Add two padic numbers
    /// Currently only implemented for same valuation and precision
    ///
    /// # Example
    ///
    /// ```
    /// use padic::Padic;
    /// let padic1 = Padic::new(0, vec!(1, 1, 2, 4), 5);
    /// let padic2 = Padic::new(0, vec!(2, 2, 4, 3), 5);
    /// let padic3 = padic1.add(&padic2);
    /// assert_eq!(padic3.expansion, vec!(3, 3, 1, 3));
    /// ```
    ///
    /// # Panics
    ///
    /// Will panic if valuations are different
    /// Will panic if primes are different
    #[must_use]
    pub fn add(&self, b: &Padic) -> Padic {
        let a = self.clone();
        assert!(
            a.valuation == b.valuation,
            "Different valuation not implemented yet."
        );
        assert!(
            a.prime == b.prime,
            "Can't add padic numbers with different primes: {} & {}",
            a.prime,
            b.prime
        );

        let mut expansion = Vec::new();
        let mut carry = 0;
        for i in 0..a.expansion.len() {
            let sum = a.expansion[i] + b.expansion[i] + carry;
            println!(
                "{} + {} + {} = {}",
                a.expansion[i], b.expansion[i], carry, sum
            );
            if sum >= a.prime {
                carry = 1;
                expansion.push(sum - a.prime);
            } else {
                carry = 0;
                expansion.push(sum);
            }
        }
        Padic::new(a.valuation, expansion, a.prime)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
/// Rational number struct with numerator, denominator and sign.
pub struct Ratio {
    /// Numerator
    pub numer: usize,
    /// Denominator
    pub denom: usize,
    /// Sign (-1 or +1)
    pub sign: isize,
}

impl fmt::Display for Ratio {
    /// Returns the string representation of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, -4);
    /// assert_eq!(r.to_string(), "-1/2");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        if self.sign == -1 {
            s.push('-');
        }
        s.push_str(&self.numer.to_string());
        s.push('/');
        s.push_str(&self.denom.to_string());
        f.write_str(&s)
    }
}

#[allow(dead_code)]
impl Ratio {
    /// Returns a ratio with numerator and denominator reduced to lowest terms.
    ///
    /// # Arguments
    ///
    /// * `numer` - A signed integer numerator.
    /// * `denom` - A signed integer denominator.
    ///
    /// # Example
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, 4);
    /// assert_eq!(r.numer, 1);
    /// ```
    ///
    /// # Panics
    ///
    /// Will panic if there's a division by zero.
    #[must_use]
    pub fn new(numer: isize, denom: isize) -> Ratio {
        assert!(denom != 0, "Division by zero");
        let mut sign = 1;
        if numer * denom < 0 {
            sign = -1;
        }
        let (gcd, _, _) = egcd(numer.abs(), denom.abs());
        Ratio {
            numer: (numer.abs() / gcd) as usize,
            denom: (denom.abs() / gcd) as usize,
            sign,
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
    /// assert_eq!(a.add(&b), Ratio::new(1, 5));
    /// ```
    #[must_use]
    pub fn add(&self, b: &Ratio) -> Ratio {
        let n = self.sign * self.numer as isize * b.denom as isize
            + b.sign * self.denom as isize * b.numer as isize;
        let d = self.denom as isize * b.denom as isize;
        Ratio::new(n, d)
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
    /// assert_eq!(a.sub(&b), Ratio::new(-1, 1));
    /// ```
    #[must_use]
    pub fn sub(&self, b: &Ratio) -> Ratio {
        let n = self.sign * self.numer as isize * b.denom as isize
            - b.sign * self.denom as isize * b.numer as isize;
        let d = self.denom as isize * b.denom as isize;
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
    /// assert_eq!(a.mul(&b), Ratio::new(-6, 25));
    /// ```
    #[must_use]
    pub fn mul(&self, b: &Ratio) -> Ratio {
        let n = self.sign * b.sign * self.numer as isize * b.numer as isize;
        let d = self.denom as isize * b.denom as isize;
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
    /// assert_eq!(a.div(&b), Ratio::new(-2, 3));
    /// ```
    #[must_use]
    pub fn div(&self, b: &Ratio) -> Ratio {
        let n = self.sign * b.sign * self.numer as isize * b.denom as isize;
        let d = self.denom as isize * b.numer as isize;
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
    #[must_use]
    pub fn prime_factors(&self) -> Vec<(usize, isize)> {
        let fact_n = prime_factors(self.numer);
        let fact_d = prime_factors(self.denom);
        // Get the union of the two sets of prime factors
        let primes = fact_n
            .iter()
            .map(|&(p, _)| p)
            .chain(fact_d.iter().map(|&(p, _)| p))
            .collect::<Vec<usize>>();
        let mut result: Vec<(usize, isize)> = Vec::new();
        // Loop over the union of the two sets of prime factors and subtract their exponents
        for prime in &primes {
            let mut pow_n = 0;
            let mut pow_d = 0;
            for &(p, pow) in &fact_n {
                if p == *prime {
                    pow_n = pow;
                }
            }
            for &(p, pow) in &fact_d {
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
        result
    }

    /// Returns the prime factors with multiplicity of the ratio.
    ///
    /// # Examples
    ///
    /// ```
    /// use padic::Ratio;
    /// let r = Ratio::new(2, 45);
    /// let r = Ratio::new(18, 5);
    /// assert_eq!(r.without_prime(3), Ratio::new(2, 5));
    /// assert_eq!(r.without_prime(3), Ratio::new(2, 5));
    /// ```
    #[must_use]
    pub fn without_prime(&self, prime: usize) -> Ratio {
        let mut numer = self.numer;
        let mut denom = self.denom;

        while numer % prime == 0 {
            numer /= prime;
        }
        while denom % prime == 0 {
            denom /= prime;
        }
        Ratio::new(self.sign * numer as isize, denom as isize)
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
    #[must_use]
    pub fn to_float(&self) -> f64 {
        self.sign as f64 * (self.numer as f64 / self.denom as f64)
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
    ///
    /// # Panics
    /// Will panic if prime is not prime
    #[must_use]
    pub fn padic_valuation(&self, prime: usize) -> isize {
        assert!(is_prime(prime), "{} is not a prime", prime);
        for &(p, pow) in &self.prime_factors() {
            if p == prime {
                return pow;
            }
        }
        0
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
    ///
    /// # Panics
    /// Will panic if prime is not prime
    #[must_use]
    pub fn padic_absolute(&self, prime: usize) -> Ratio {
        assert!(is_prime(prime), "{} is not a prime", prime);
        let valuation = self.padic_valuation(prime);
        let exp = prime.pow((valuation.abs()).try_into().unwrap());
        if self.numer == 0 {
            Ratio::new(0, 1)
        } else if valuation < 0 {
            Ratio::new(exp as isize, 1)
        } else {
            Ratio::new(1, exp as isize)
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
    ///
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
    /// let r = Ratio::new(2, 45);
    /// let p = r.to_padic(3, 5);
    /// assert_eq!(p.expansion, vec![1, 1, 2, 1, 0]);
    /// ```
    ///
    /// # Panics
    ///
    /// Will panic if ratio numbers are too high
    /// Will panic if the prime is out of range
    /// Will panic if the prime is not prime
    /// Will panic if the precision is too small
    #[must_use]
    pub fn to_padic(&self, prime: usize, precision: usize) -> Padic {
        // Validate input
        assert!(
            !(self.numer > MAX_ARG || self.denom > MAX_ARG as usize),
            "Ratio too large"
        );
        assert!((2..=MAX_P).contains(&prime), "Prime out of range");
        assert!(is_prime(prime), "{} is not a prime", prime);
        assert!(precision > 0, "Precision must be positive");

        // Get the p-adic absolute value of the ratio
        let valuation = self.padic_valuation(prime);
        let mut expansion = vec![0; precision as usize];

        let mut digit;
        let mut ratio = self.without_prime(prime);
        for i in 0..precision {
            digit = ratio.next_digit(prime).0;
            ratio = ratio.next_digit(prime).1;
            expansion[i as usize] = digit;
        }

        // Initialize padic number
        Padic {
            valuation,
            expansion,
            prime,
        }
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
    ///
    /// # Panics
    /// Will panic if a value isn't returned
    #[must_use]
    pub fn next_digit(&self, prime: usize) -> (usize, Ratio) {
        let p_ratio = Ratio::new(prime as isize, 1);
        for digit in 0..=prime {
            let d_ratio = Ratio::new(digit as isize, 1);

            for num in 1..=self.denom {
                let num_ratio = Ratio::new(-(num as isize), self.denom as isize);

                let result = d_ratio.add(&p_ratio.mul(&num_ratio));
                if result == *self {
                    return (digit, num_ratio);
                }
            }
        }
        panic!("Next digit computation error.")
    }
}

//---------------------
// HELPER FUNCTIONS
//---------------------

/// Extended Euclidean algorithm with Bezout's coefficients
/// <https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm>
/// Bezout coefficients: a*x + b*y == gcd(a,b)
///
/// # Arguments
///
/// * `a` - A positive integer.
/// * `b` - A positive integer.
///
/// # Examples
///
/// ```
/// use padic::egcd;
/// assert_eq!(egcd(26, 3), (1, -1, 9));
/// assert_eq!(egcd(3, 26), (1, 9, -1));
/// ```
#[must_use]
pub fn egcd(a: isize, b: isize) -> (isize, isize, isize) {
    match (a, b) {
        (0, _) => (b, 0, 1),
        (_, 0) => (a, 1, 0),
        _ => {
            let quotient = b / a;
            let remainder = b % a;
            let (gcd, x, y) = egcd(remainder, a);
            (gcd, y - quotient * x, x)
        }
    }
}

/// Returns modular multiplicative inverse of a number.
/// <https://rosettacode.org/wiki/Modular_inverse#Rust>
///
/// # Arguments
///
/// * `num` - A positive integer.
/// * `modulo` - A positive integer.
///
/// # Examples
///
/// ```
/// use padic::mod_inv;
/// assert_eq!(mod_inv(42, 2017), Some(1969));
/// ```
#[must_use]
pub fn mod_inv(num: isize, modulo: isize) -> Option<isize> {
    let (gcd, x, _) = egcd(num, modulo);

    match gcd {
        1 => Some(x.rem_euclid(modulo)),
        _ => None,
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
#[must_use]
pub fn prime_factors(num: usize) -> Vec<(usize, isize)> {
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
#[must_use]
pub fn is_prime(num: usize) -> bool {
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
    true
}

/// Double cursor window cycle detection algorithm.
/// <https://rosettacode.org/wiki/Cycle_detection>
/// <https://en.wikipedia.org/wiki/Cycle_detection>
///
/// # Arguments
///
/// * `vector` - a potentially repeating usize vector.
///
/// # Examples
///
/// ```
/// use padic::cycle_detection;
/// let arr = &[0, 1, 2, 3, 1, 2, 3, 1, 2];
/// assert_eq!(cycle_detection(arr), (1, 3));
/// let arr = &[0, 1, 2, 1, 2, 1, 2, 3, 2];
/// assert_eq!(cycle_detection(arr), (0, 0));
/// ```
#[must_use]
pub fn cycle_detection(vector: &[usize]) -> (usize, usize) {
    // Increasing offset
    for offset in 0..vector.len() / 2 {
        let slice = &vector[offset..].to_vec();
        // Increasing window size
        for size in 1..slice.len() / 2 {
            let window: &Vec<usize> = &slice[0..size].to_vec();
            let repetitions = (slice.len() / size) + 1;
            let mut repeated: Vec<usize> = vec![];
            // Create repeated window array
            for _ in 0..repetitions {
                repeated.extend(window);
            }
            repeated = repeated[0..slice.len()].to_vec();
            // Check if repeated window matches slice
            if repeated == *slice {
                return (offset, size);
            }
        }
    }
    (0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratio_to_padic_default_test() {
        let r = Ratio::new(2, 5);
        let p = r.to_padic(3, 10);
        assert_eq!(p.valuation, 0);
        assert_eq!(p.expansion, vec![1, 1, 2, 1, 0, 1, 2, 1, 0, 1]);
    }

    #[test]
    fn ratio_to_padic_val_none_test() {
        let r = Ratio::new(1, 3);
        let p = r.to_padic(5, 10);
        assert_eq!(p.valuation, 0);
        assert_eq!(p.expansion, vec![2, 3, 1, 3, 1, 3, 1, 3, 1, 3]);
    }

    #[test]
    fn ratio_to_padic_val_two_test() {
        let r = Ratio::new(25, 3);
        let p = r.to_padic(5, 10);
        assert_eq!(p.valuation, 2);
        assert_eq!(p.expansion, vec![2, 3, 1, 3, 1, 3, 1, 3, 1, 3]);
    }

    #[test]
    fn ratio_to_padic_val_minus_two_test() {
        let r = Ratio::new(1, 75);
        let p = r.to_padic(5, 10);
        assert_eq!(p.valuation, -2);
        assert_eq!(p.expansion, vec![2, 3, 1, 3, 1, 3, 1, 3, 1, 3]);
    }

    //  {2, 1, 2, 4, 1, 1},
    //  {4, 1, 2, 4, 3, 1},
    //  {4, 1, 2, 5, 3, 1},
    //  {4, 9, 5, 4, 8, 9},
    //  {26, 25, 5, 4, -109, 125},
    //  {49, 2, 7, 6, -4851, 2},
    //  {-9, 5, 3, 8, 27, 7},
    //  {5, 19, 2, 12, -101, 384},
    //  /* two decadic pairs */
    //  {2, 7, 10, 7, -1, 7},
    //  {34, 21, 10, 9, -39034, 791},
    //  /* familiar digits */
    //  {11, 4, 2, 43, 679001, 207},
    //  {-8, 9, 23, 9, 302113, 92},
    //  {-22, 7, 3, 23, 46071, 379},
    //  {-22, 7, 32749, 3, 46071, 379},
    //  {35, 61, 5, 20, 9400, 109},
    //  {-101, 109, 61, 7, 583376, 6649},
    //  {-25, 26, 7, 13, 5571, 137},
    //  {1, 4, 7, 11, 9263, 2837},
    //  {122, 407, 7, 11, -517, 1477},
    //  /* more subtle */
    //  {5, 8, 7, 11, 353, 30809},

    #[test]
    fn ratio_padic_valuation_test() {
        let ratio = Ratio::new(140, 297);
        assert_eq!(ratio.padic_valuation(2), 2);
        assert_eq!(ratio.padic_valuation(3), -3);
        assert_eq!(ratio.padic_valuation(5), 1);
        assert_eq!(ratio.padic_valuation(7), 1);
        assert_eq!(ratio.padic_valuation(11), -1);
    }

    #[test]
    fn ratio_padic_absolute_test() {
        let ratio = Ratio::new(140, 297);
        assert_eq!(ratio.padic_absolute(2), Ratio::new(1, 4));
        assert_eq!(ratio.padic_absolute(3), Ratio::new(27, 1));
        assert_eq!(ratio.padic_absolute(5), Ratio::new(1, 5));
        assert_eq!(ratio.padic_absolute(11), Ratio::new(11, 1));
    }

    #[test]
    fn ratio_prime_factors_test() {
        let ratio1 = Ratio::new(2, 15);
        let ratio_prime_factors1 = ratio1.prime_factors();
        assert_eq!(ratio_prime_factors1, vec![(2, 1), (3, -1), (5, -1)]);
        let ratio2 = Ratio::new(-35, 7);
        let ratio_prime_factors2 = ratio2.prime_factors();
        assert_eq!(ratio_prime_factors2, vec![(5, 1)]);
    }

    #[test]
    fn ratio_new_test() {
        let ratio1 = Ratio::new(-21, -12);
        let test_ratio = Ratio {
            numer: 7,
            denom: 4,
            sign: 1,
        };
        assert_eq!(ratio1, test_ratio);
    }

    #[test]
    fn ratio_to_string_test() {
        let ratio1 = Ratio::new(-9, 2);
        assert_eq!(ratio1.to_string(), "-9/2");
    }
}
