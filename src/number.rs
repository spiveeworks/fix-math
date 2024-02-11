use num_bigint::BigInt;

use crate::big_float::BigFloat;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frac() {
        let iter = ContinuedFraction::from_float(BigFloat::from(12.1234));
        let terms: Vec<i32> = iter.collect();
        assert_eq!(terms, vec![12, 8, 9, 1, 1, 1, 3, 1, 1, 1, 1, 226995948, 2,
                   1, 5, 1, 2, 4]);
    }
}

