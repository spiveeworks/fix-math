use num_bigint::BigUint;
use num_rational::BigRational;

#[derive(PartialEq, Eq)]
pub struct Decimal {
    pub is_negative: bool,
    pub wholepart: BigUint,
    pub nonrecurring: String,
    pub recurring: String,
}

impl std::fmt::Display for Decimal {
    fn fmt(self: &Decimal, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.is_negative {
            write!(f, "-")?;
        }
        write!(f, "{}", self.wholepart)?;
        if self.nonrecurring.is_empty() && self.recurring.is_empty() {
            return Ok(());
        }

        write!(f, ".{}", self.nonrecurring)?;
        if !self.recurring.is_empty() {
            write!(f, "{{{}}}", self.recurring)?;
        }

        Ok(())
    }
}

impl Decimal {
    pub fn calculate(x: &BigRational) -> Self {
        use num_traits::Signed;
        use num_traits::Zero;
        use num_integer::Integer;

        let is_negative = x.is_negative();
        let mut n = x.numer().abs().to_biguint().unwrap();
        let d = x.denom().to_biguint().unwrap();
        let (wholepart, remainder) = BigUint::div_rem(&n, &d);
        n = remainder;

        // Offsets at which given n values were first encountered, so
        // we can detect loops.
        use std::collections::HashMap;
        let mut offsets = HashMap::new();

        let mut digits = String::new();
        while !n.is_zero() && !offsets.contains_key(&n) {
            // Store the offset that n was encountered at, but only after
            // calculating the next digit, since storing it will consume the
            // value.
            let (digit, remainder) = BigUint::div_rem(&(&n * 10 as u8), &d);
            offsets.insert(n, digits.len());

            // The remainder will be the new value of n.
            n = remainder;

            // Convert the digit to a char and push it.
            let digit_scalar = digit.try_into().unwrap();
            let c = char::from_digit(digit_scalar, 10).unwrap();
            digits.push(c);
        }
        if n.is_zero() {
            Decimal {
                is_negative,
                wholepart,
                nonrecurring: digits,
                recurring: String::new(),
            }
        } else {
            let (nrec, rec) = digits.split_at(offsets[&n]);
            Decimal {
                is_negative,
                wholepart,
                nonrecurring: String::from(nrec),
                recurring: String::from(rec),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn test_display() {
        let x = Decimal {
            is_negative: false,
            wholepart: BigUint::from(12 as u32),
            nonrecurring: String::from("55"),
            recurring: String::from("01"),
        };
        assert_eq!(format!("{}", x), "12.55{01}");

        let y = Decimal {
            is_negative: true,
            wholepart: BigUint::from(0 as u32),
            nonrecurring: String::from("7"),
            recurring: String::from(""),
        };
        assert_eq!(format!("{}", y), "-0.7");

        let z = Decimal {
            is_negative: false,
            wholepart: BigUint::from(895 as u32),
            nonrecurring: String::from(""),
            recurring: String::from(""),
        };
        assert_eq!(format!("{}", z), "895");
    }

    #[test]
    fn test_calculate() {
        let calc_decimal = |n, d| {
            let r = BigRational::new(BigInt::from(n), BigInt::from(d));
            Decimal::calculate(&r)
        };
        assert_eq!(format!("{}", calc_decimal(1, 3)), "0.{3}");
        assert_eq!(format!("{}", calc_decimal(-1, 3)), "-0.{3}");
        assert_eq!(format!("{}", calc_decimal(3, 4)), "0.75");
        assert_eq!(format!("{}", calc_decimal(109, 90)), "1.2{1}");
    }
}

