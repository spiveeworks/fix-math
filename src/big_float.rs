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
        self.exponent = new_exponent;
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
            use num_traits::Zero;
            use num_traits::One;

            // First display the whole part and a period.
            write!(f, "{}", &mantissa >> -self.exponent)?;

            // Now the fractional part.
            let unit = num_bigint::BigUint::one() << -self.exponent;
            let mut remainder = self.mantissa.abs().to_biguint().unwrap();
            remainder %= &unit;
            let digits = std::cmp::max(4, (-self.exponent) * 3 / 10 + 1);
            // let mut cutoff = num_bigint::BigUint::from(0 as u8);
            let mut drawn_separator = false;
            for _ in 0..digits {
                if remainder.is_zero() {
                    break;
                }
                // Calculate one digit and print it.
                remainder *= 10 as u8;
                // cutoff *= 10 as u8;
                let digit = &remainder >> -self.exponent;
                if !drawn_separator {
                    write!(f, ".")?;
                    drawn_separator = true;
                }
                write!(f, "{}", digit)?;

                remainder %= &unit;
            }
        }
        Ok(())
    }
}

// The easiest float operations are of course the multiplicative ones.
impl<'b> std::ops::MulAssign<&'b BigFloat> for BigFloat {
    fn mul_assign(self: &mut BigFloat, other: &'b BigFloat) {
        self.mantissa *= &other.mantissa;
        self.exponent += other.exponent;
    }
}

impl std::ops::Mul<BigFloat> for BigFloat {
    type Output = BigFloat;
    fn mul(mut self: BigFloat, other: BigFloat) -> BigFloat {
        /* Is it possible that we could prefer one or the other? The biggest
           one in memory, say? */
        self *= &other;
        self
    }
}

impl<'b> std::ops::Mul<&'b BigFloat> for BigFloat {
    type Output = BigFloat;
    fn mul(mut self: BigFloat, other: &'b BigFloat) -> BigFloat {
        self *= other;
        self
    }
}

impl<'a> std::ops::Mul<BigFloat> for &'a BigFloat {
    type Output = BigFloat;
    fn mul(self: &'a BigFloat, mut other: BigFloat) -> BigFloat {
        other *= self;
        other
    }
}

impl<'a, 'b> std::ops::Mul<&'b BigFloat> for &'a BigFloat {
    type Output = BigFloat;
    fn mul(self: &'a BigFloat, other: &'b BigFloat) -> BigFloat {
        let mut a = self.clone();
        a *= other;
        a
    }
}

impl<'b> std::ops::DivAssign<&'b BigFloat> for BigFloat {
    fn div_assign(self: &mut BigFloat, other: &'b BigFloat) {
        self.mantissa /= &other.mantissa;
        self.exponent -= other.exponent;
    }
}

impl std::ops::Neg for BigFloat {
    type Output = BigFloat;
    fn neg(self: BigFloat) -> BigFloat {
        BigFloat {
            mantissa: -self.mantissa,
            exponent: self.exponent,
        }
    }
}

// From here on we need to be able to match precisions (think of this like
// finding a common denominator) in order to combine pairs of values. For this
// we utilize clone-on-write pointers, so we can modify one or the other, and
// then continue down a single code path.
struct Cow<'a>(std::borrow::Cow<'a, BigFloat>);

impl<'a> From<BigFloat> for Cow<'a> {
    fn from(it: BigFloat) -> Self {
        Cow(std::borrow::Cow::Owned(it))
    }
}

impl<'a> From<&'a BigFloat> for Cow<'a> {
    fn from(it: &'a BigFloat) -> Self {
        Cow(std::borrow::Cow::Borrowed(it))
    }
}

fn match_precisions(a: &mut Cow, b: &mut Cow) {
    // The smaller the exponent, the more accuracy we need. Use the smallest
    // exponent.
    if a.0.exponent > b.0.exponent {
        a.0.to_mut().adjust_exponent(b.0.exponent);
    } else if a.0.exponent < b.0.exponent {
        b.0.to_mut().adjust_exponent(a.0.exponent);
    }
}

fn match_precisions_mut(a: &mut BigFloat, b: &mut Cow) {
    if a.exponent > b.0.exponent {
        a.adjust_exponent(b.0.exponent);
    } else if a.exponent < b.0.exponent {
        b.0.to_mut().adjust_exponent(a.exponent);
    }
}

fn cow_eq(mut a: Cow, mut b: Cow) -> bool {
    match_precisions(&mut a, &mut b);
    a.0.mantissa == b.0.mantissa
}

fn cow_cmp(mut a: Cow, mut b: Cow) -> std::cmp::Ordering {
    match_precisions(&mut a, &mut b);
    Ord::cmp(&a.0.mantissa, &b.0.mantissa)
}

impl PartialEq<BigFloat> for BigFloat {
    fn eq(self: &BigFloat, other: &BigFloat) -> bool {
        cow_eq(Cow::from(self), Cow::from(other))
    }
}

impl Eq for BigFloat { }

impl PartialOrd for BigFloat {
    fn partial_cmp(self: &BigFloat, other: &BigFloat)
        -> Option<std::cmp::Ordering>
    {
        Some(cow_cmp(Cow::from(self), Cow::from(other)))
    }
}

impl Ord for BigFloat {
    fn cmp(self: &BigFloat, other: &BigFloat) -> std::cmp::Ordering {
        cow_cmp(Cow::from(self), Cow::from(other))
    }
}

fn cow_mantissa<'a>(a: Cow<'a>) -> std::borrow::Cow<'a, BigInt> {
    match a.0 {
        std::borrow::Cow::Owned(it) =>
            std::borrow::Cow::Owned(it.mantissa),
        std::borrow::Cow::Borrowed(it) =>
            std::borrow::Cow::Borrowed(&it.mantissa),
    }
}

// Take two cows, and extract an owned version of one or the other. This allows
// us to do things like match_precisions, and then do a destructive but
// symmetric operation to whichever one we have
// already modified.
fn maybe_swap<'a>(a: Cow<'a>, b: Cow<'a>) -> (BigFloat, Cow<'a>, bool) {
    if let Cow(std::borrow::Cow::Owned(it)) = a {
        (it, b, false)
    } else if let Cow(std::borrow::Cow::Owned(it)) = b {
        (it, a, true)
    } else {
        (a.0.into_owned(), b, false)
    }
}

fn match_precisions_maybe_swap<'a>(mut a: Cow<'a>, mut b: Cow<'a>) -> (BigInt, std::borrow::Cow<'a, BigInt>, i64, bool) {
    match_precisions(&mut a, &mut b);
    let (a, b, swapped) = maybe_swap(a, b);

    (a.mantissa, cow_mantissa(b), a.exponent, swapped)
}

fn cow_add(a: Cow, b: Cow) -> BigFloat {
    let (mut a, b, exp, _) = match_precisions_maybe_swap(a, b);
    a += &*b;
    BigFloat {
        mantissa: a,
        exponent: exp,
    }
}

fn cow_add_assign(a: &mut BigFloat, mut b: Cow) {
    match_precisions_mut(a, &mut b);
    a.mantissa += &b.0.mantissa;
}

impl<'b> std::ops::AddAssign<&'b BigFloat> for BigFloat {
    fn add_assign(self: &mut BigFloat, other: &'b BigFloat) {
        cow_add_assign(self, Cow::from(other));
    }
}

impl std::ops::AddAssign<BigFloat> for BigFloat {
    fn add_assign(self: &mut BigFloat, other: BigFloat) {
        cow_add_assign(self, Cow::from(other));
    }
}

impl<'a, 'b> std::ops::Add<&'b BigFloat> for &'a BigFloat {
    type Output = BigFloat;
    fn add(self: &'a BigFloat, other: &'b BigFloat) -> BigFloat {
        cow_add(Cow::from(self), Cow::from(other))
    }
}

fn cow_sub(a: Cow, b: Cow) -> BigFloat {
    let (mut a, b, exp, swapped) = match_precisions_maybe_swap(a, b);
    a -= &*b;
    if swapped {
        a = -a;
    }
    BigFloat {
        mantissa: a,
        exponent: exp,
    }
}

fn cow_sub_assign(a: &mut BigFloat, mut b: Cow) {
    match_precisions_mut(a, &mut b);
    a.mantissa -= &b.0.mantissa;
}

impl<'b> std::ops::SubAssign<&'b BigFloat> for BigFloat {
    fn sub_assign(self: &mut BigFloat, other: &'b BigFloat) {
        cow_sub_assign(self, Cow::from(other));
    }
}

impl std::ops::SubAssign<BigFloat> for BigFloat {
    fn sub_assign(self: &mut BigFloat, other: BigFloat) {
        cow_sub_assign(self, Cow::from(other));
    }
}

impl<'a, 'b> std::ops::Sub<&'b BigFloat> for &'a BigFloat {
    type Output = BigFloat;
    fn sub(self: &'a BigFloat, other: &'b BigFloat) -> BigFloat {
        cow_sub(Cow::from(self), Cow::from(other))
    }
}

impl<'b> std::ops::Sub<&'b BigFloat> for BigFloat {
    type Output = BigFloat;
    fn sub(self: BigFloat, other: &'b BigFloat) -> BigFloat {
        cow_sub(Cow::from(self), Cow::from(other))
    }
}

impl<'a> std::ops::Sub<BigFloat> for &'a BigFloat {
    type Output = BigFloat;
    fn sub(self: &'a BigFloat, other: BigFloat) -> BigFloat {
        cow_sub(Cow::from(self), Cow::from(other))
    }
}

impl std::ops::Sub for BigFloat {
    type Output = BigFloat;
    fn sub(self: BigFloat, other: BigFloat) -> BigFloat {
        cow_sub(Cow::from(self), Cow::from(other))
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

