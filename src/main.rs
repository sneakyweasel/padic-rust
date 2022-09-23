// https://rosettacode.org/wiki/P-Adic_numbers,_basic

mod ratio;

fn main() {
    let ratio = ratio::Ratio::new(2, 15);
    println!("Ratio: {}", ratio);
    println!("Prime factors: {:?}", ratio.prime_factors());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratio_import_test() {
        let r = ratio::Ratio::new(1, 2);
        assert_eq!(r.to_string(), "1/2");
    }
}
