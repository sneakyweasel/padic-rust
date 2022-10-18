#![forbid(unsafe_code)]
//! # P-adic numbers
//!
//! `padic` is a collection of utilities to convert and manipulate p-adic numbers.

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
/// p-adic number struct with valuation, decimal expansion and prime.
pub struct Padic {
    pub valuation: i64,
    pub expansion: Vec<u64>,
    prime: u64,
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
    pub fn new(valuation: i64, expansion: Vec<u64>, prime: u64) -> Padic {
        if !is_prime(prime) {
            panic!("Prime provided {} is not prime.", prime);
        }
        Padic {
            valuation: valuation,
            expansion: expansion,
            prime: prime,
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
    /// assert_eq!(0, 4);
    /// ```
    pub fn expansion_cycle(&self) -> Vec<u64> {
        let (offset, size) = cycle_detection(self.expansion.clone());
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
    /// let padic3 = padic1.add(padic2);
    /// assert_eq!(padic3.expansion, vec!(3, 3, 1, 3));
    /// ```
    pub fn add(&self, b: Padic) -> Padic {
        let a = self.clone();
        if a.valuation != b.valuation {
            panic!("Different valuation not implemented yet.");
        }
        if a.prime != b.prime {
            panic!(
                "Can't add padic numbers with different primes: {} & {}",
                a.prime, b.prime
            );
        }
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
    pub fn to_string(&self) -> String {
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
        "... ".to_string() + &expansion.join(" ").to_string().trim_end().to_string()
    }
}

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
    pub fn new(numer: i64, denom: i64) -> Ratio {
        if denom == 0 {
            panic!("Division by zero");
        }
        let mut sign = 1;
        if numer * denom < 0 {
            sign = -1;
        }
        let (gcd, _, _) = egcd(numer.abs(), denom.abs());
        Ratio {
            numer: (numer.abs() / gcd) as u64,
            denom: (denom.abs() / gcd) as u64,
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
    /// assert_eq!(a.sub(b), Ratio::new(-1, 1));
    /// ```
    pub fn sub(&self, b: Ratio) -> Ratio {
        let n = self.sign * self.numer as i64 * b.denom as i64
            - b.sign * self.denom as i64 * b.numer as i64;
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
    /// assert_eq!(a.div(b), Ratio::new(-2, 3));
    /// ```
    pub fn div(&self, b: Ratio) -> Ratio {
        let n = self.sign * b.sign * self.numer as i64 * b.denom as i64;
        let d = self.denom as i64 * b.numer as i64;
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
    pub fn without_prime(&self, prime: u64) -> Ratio {
        let mut numer = self.numer;
        let mut denom = self.denom;

        while numer % prime == 0 {
            numer /= prime
        }
        while denom % prime == 0 {
            denom /= prime
        }
        Ratio::new(self.sign * numer as i64, denom as i64)
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
        return Padic {
            valuation: valuation,
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
        for digit in 0..=prime {
            let d_ratio = Ratio::new(digit as i64, 1);

            for num in 1..=self.denom {
                let num_ratio = Ratio::new(-(num as i64), self.denom as i64);

                let result = d_ratio.add(p_ratio.mul(num_ratio.clone()));
                if result == *self {
                    return (digit, num_ratio);
                }
            }
        }
        panic!("Next digit computation error.")
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
/// assert_eq!(egcd(3, 5), (1, -1, 9));
/// assert_eq!(egcd(26, 3), (1, -1, 9));
/// assert_eq!(egcd(3, 26), (1, 9, -1));
/// ```
pub fn egcd(a: i64, b: i64) -> (i64, i64, i64) {
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
pub fn mod_inv(num: i64, modulo: i64) -> Option<i64> {
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

/// Double cursor window cycle detection algorithm.
/// <https://rosettacode.org/wiki/Cycle_detection>
/// <https://en.wikipedia.org/wiki/Cycle_detection>
///
/// # Arguments
///
/// * `vector` - a potentially repeating u64 vector.
///
/// # Examples
///
/// ```
/// use padic::cycle_detection;
/// let arr = vec![0, 1, 2, 3, 1, 2, 3, 1, 2];
/// assert_eq!(cycle_detection(arr), (1, 3));
/// let arr = vec![0, 1, 2, 1, 2, 1, 2, 3, 2];
/// assert_eq!(cycle_detection(arr), (0, 0));
/// ```
pub fn cycle_detection(vector: Vec<u64>) -> (usize, usize) {
    // Increasing offset
    for offset in 0..vector.len() / 2 {
        let slice = &vector[offset..].to_vec();
        // Increasing window size
        for size in 1..slice.len() / 2 {
            let window: &Vec<u64> = &slice[0..size].to_vec();
            let repetitions = (slice.len() / size) + 1;
            let mut repeated: Vec<u64> = vec![];
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
    fn ratio_to_float_test() {
        let ratio1 = Ratio::new(-9, 2);
        assert_eq!(ratio1.to_float(), -4.5);
    }

    #[test]
    fn ratio_to_string_test() {
        let ratio1 = Ratio::new(-9, 2);
        assert_eq!(ratio1.to_string(), "-9/2");
    }
}
