use num_bigint::BigInt;
use num_rational::BigRational;

use crate::big_float::BigFloat;

// We don't want to use BigRational for this, since BigRational seems to
// GCD/Euclid's algorithm with every operation, and the whole goal here is to
// extract the results of a single Euclid's algorithm.
#[derive(Clone)]
pub struct ContinuedFraction {
    pub numerator: BigInt,
    pub denominator: BigInt,
}

impl ContinuedFraction {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Self {
        ContinuedFraction { numerator, denominator }
    }
    pub fn from_float(value: BigFloat) -> Self {
        if value.exponent < 0 {
            let mut denominator = BigFloat {
                mantissa: BigInt::from(1),
                exponent: 0,
            };
            denominator.adjust_exponent(value.exponent);
            ContinuedFraction {
                numerator: value.mantissa,
                denominator: denominator.mantissa,
            }
        } else {
            ContinuedFraction {
                numerator: value.with_exponent(0).mantissa,
                denominator: BigInt::from(1),
            }
        }
    }
}

impl Iterator for ContinuedFraction {
    type Item = i32;
    fn next(self: &mut ContinuedFraction) -> Option<i32> {
        use num_traits::Zero;
        use num_integer::Integer;
        if self.numerator.is_zero() || self.denominator.is_zero() {
            return None;
        }

        let (wholepart, remainder) = BigInt::div_rem(&self.numerator, &self.denominator);
        let prev_denominator = std::mem::replace(&mut self.denominator, remainder);
        self.numerator = prev_denominator;

        let result = wholepart.try_into().unwrap();
        Some(result)
    }
}

pub fn collect_continued_fraction(terms: &[i32]) -> BigRational {
    // Initialize to 1/0, so that x + 1/(n/d) becomes x + 0/1
    let mut n = BigInt::from(1);
    let mut d = BigInt::from(0);
    for x in terms.iter().rev() {
        // x + 1/(n/d) = x + d/n = (x*n + d)/n
        // let's do
        // d += x * n;
        // swap(n, d);
        d += x * &n;
        std::mem::swap(&mut n, &mut d);
    }

    BigRational::new_raw(n, d)
}

pub fn simplify_fraction(x: ContinuedFraction) -> BigRational {
    let terms: Vec<i32> = x.collect();
    let mut max_index: usize = 1;
    for i in 2..terms.len() {
        if terms[i] > terms[max_index] {
            max_index = i;
        }
    }
    if max_index == 1 {
        collect_continued_fraction(&terms)
    } else {
        let (head, _) = terms.split_at(max_index);

        collect_continued_fraction(head)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frac() {
        let iter = ContinuedFraction::from_float(BigFloat::from(12.1234));
        let terms: Vec<i32> = iter.collect();
        // the 226995948 is the floating point error. The terms before that
        // give 12.1234 exactly.
        assert_eq!(terms, vec![12, 8, 9, 1, 1, 1, 3, 1, 1, 1, 1, 226995948, 2,
                   1, 5, 1, 2, 4]);
    }

    #[test]
    fn test_collect() {
        let iter = ContinuedFraction::from_float(BigFloat::from(12.1234));
        let terms: Vec<i32> = iter.clone().collect();
        let rat = collect_continued_fraction(&terms);
        let rat_expected = BigRational::new(iter.numerator.clone(), iter.denominator.clone());
        assert_eq!(rat, rat_expected);
    }

    #[test]
    fn test_simplify() {
        let iter = ContinuedFraction::from_float(BigFloat::from(12.1234));

        // Simplify the fraction by removing the largest (thus least
        // contributing) term. Ironically this just strips off the floating
        // point error, and recovers 121234/10000 as a fraction. (Or half of
        // this.)
        let simplified = simplify_fraction(iter);
        let expected = collect_continued_fraction(&[12, 8, 9, 1, 1, 1, 3, 1, 1, 1, 1]);
        println!("Value: {}", expected);
        assert_eq!(&simplified, &expected);
    }
}

