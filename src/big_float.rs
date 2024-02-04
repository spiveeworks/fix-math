use num_bigint::BigInt;

#[derive(Clone, Debug)]
pub struct BigFloat {
    pub mantissa: BigInt,
    pub exponent: i64,
}

impl BigFloat {
    pub fn adjust_exponent(self: &mut BigFloat, new_exponent: i64) {
        let exp_change = new_exponent - self.exponent;
        if exp_change >= 0 {
            // If exp_change is positive, then we want to make the exponent
            // bigger, while representing the same value. (Though precision
            // will be lost.) This means making the mantissa smaller, i.e.
            // right shifting it.
            self.mantissa >>= exp_change;
        } else {
            // If exp_change is negative then we have to explicitly left shift
            // instead, because BigInt will crash if you shift left with a
            // negative.
            self.mantissa <<= -exp_change;
        }
    }

    pub fn with_exponent(mut self: BigFloat, new_exponent: i64) -> BigFloat {
        self.adjust_exponent(new_exponent);
        self
    }
}

// Based on the code from num_traits.
fn integer_decode_f64(f: f64) -> (i64, i16) {
    let bits: u64 = f.to_bits();

    let mut exponent: i16 = ((bits >> 52) & 0x7ff) as i16;

    let mut mantissa;
    if exponent == 0 {
        mantissa = ((bits & 0xfffffffffffff) << 1) as i64;
    } else {
        mantissa = ((bits & 0xfffffffffffff) | 0x10000000000000) as i64;
    };
    if bits >> 63 == 1 {
        mantissa = -mantissa;
    }

    // Exponent bias + mantissa shift
    exponent -= 1023 + 52;
    (mantissa, exponent)
}

impl From<f64> for BigFloat {
    fn from(value: f64) -> BigFloat {
        let (mantissa, exponent) = integer_decode_f64(value);
        BigFloat {
            mantissa: BigInt::from(mantissa),
            exponent: exponent as i64,
        }
    }
}

impl std::fmt::Display for BigFloat {
    fn fmt(self: &BigFloat, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use num_traits::sign::Signed;
        // Print and then remove the sign.
        if self.mantissa.is_negative() {
            write!(f, "-")?;
        }
        // Strip the sign, and make a copy in the process.
        let mantissa = self.mantissa.abs().to_biguint().unwrap();

        // Now display the fractional part, if any.
        if self.exponent >= 0 {
            // Positive exponent, just calculate the integer and display that.
            write!(f, "{}", mantissa << self.exponent)?;
        } else {
            // I hate this library.
            use num_traits::One;

            // First display the whole part and a period.
            write!(f, "{}", &mantissa >> -self.exponent)?;
            write!(f, ".")?;

            // Now the fractional part.
            let unit = num_bigint::BigUint::one() << -self.exponent;
            let mut remainder = self.mantissa.abs().to_biguint().unwrap();
            remainder %= &unit;
            // Stop printing once the next three digits would all be zero.
            let cutoff = &unit >> 10;
            while &remainder > &cutoff {
                // Calculate one digit and print it.
                remainder *= 10 as u8;
                let digit = &remainder >> -self.exponent;
                write!(f, "{}", digit)?;

                remainder %= &unit;
            }
        }
        Ok(())
    }
}

impl std::ops::AddAssign for BigFloat {
    fn add_assign(self: &mut BigFloat, mut other: BigFloat) {
        // The smaller the exponent, the more accuracy we need. Use the
        // smallest exponent.
        if other.exponent <= self.exponent {
            self.adjust_exponent(other.exponent);
            self.mantissa += other.mantissa;
        } else {
            other.adjust_exponent(self.exponent);
            self.mantissa += other.mantissa;
        }
    }
}

impl std::ops::AddAssign<&BigFloat> for BigFloat {
    fn add_assign(self: &mut BigFloat, other: &BigFloat) {
        // The smaller the exponent, the more accuracy we need. Use the
        // smallest exponent.
        if other.exponent <= self.exponent {
            self.adjust_exponent(other.exponent);
            self.mantissa += &other.mantissa;
        } else {
            let adjusted = other.clone().with_exponent(self.exponent);
            self.mantissa += adjusted.mantissa;
        }
    }
}

impl<'a, 'b> std::ops::Add<&'b BigFloat> for &'a BigFloat {
    type Output = BigFloat;
    fn add(self: &'a BigFloat, other: &'b BigFloat) -> BigFloat {
        let mut copy = self.clone();
        copy += other;

        copy
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn addition() {
        let x = BigFloat::from(0.5);
        let y = BigFloat::from(-12.0);
        let sum = &x + &y;
        assert_eq!(sum.exponent, x.exponent);
        // -11.5, so -23 in .1 fixed point arithmetic, which we can then
        // convert to a .53 fixed point number by shifting left a further 52.
        assert_eq!(sum.mantissa, BigInt::from(-23) << -x.exponent-1);
    }
}

