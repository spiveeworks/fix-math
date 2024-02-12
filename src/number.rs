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
        let (n, d) = float_to_ratio(value);

        ContinuedFraction::new(n, d)
    }
}

fn float_to_ratio(value: BigFloat) -> (BigInt, BigInt) {
    if value.exponent < 0 {
        (value.mantissa, BigInt::from(1) << -value.exponent)
    } else {
        (value.mantissa << value.exponent, BigInt::from(1))
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

// gcd(100, 17) = 1
// so we should be able to find a linear combination that equals 1
// Euclid's alg goes
// 100 = 17 * 5 + 15
// 17 = 15 * 1 + 2
// 15 = 7 * 2 + 1
// therefore gcd(100, 17) = gcd(17, 15) = ... = 1
//
// but to collect linear combinations in a single pass, we could say
// 15 = 100 - 17 * 5
// 2 = 17 - 1 * (100 - 17 * 5) = 17 * 6 - 100 * 1
// 1 = 15 - 7 * 2 = (100 - 17 * 5) - 7 * (17 * 6 - 100 * 1)
//   = 8 * 100 - 47 * 17
// which is correct.
// So at each step we need the previous two terms, both as a linear combination
// of the first two terms we were given.

/*
struct EuclidsAlgIter {
    input_a: BigInt,
    input_b: BigInt,
    lc1: (BigInt, BigInt, BigInt), // lc1.0 = input_a * lc1.1 + input_b * lc1.2
    lc2: (BigInt, BigInt, BigInt), // similar
}
*/

pub fn euclids_alg(a: BigInt, b: BigInt) -> (BigInt, BigInt, BigInt) {
    use num_integer::Integer;
    use num_traits::Zero;

    // at all times lc.0 = a * lc.1 + b * lc.2, for both lc1 and lc2
    let mut lc1 = (a, BigInt::from(1), BigInt::from(0));
    let mut lc2 = (b, BigInt::from(0), BigInt::from(1));

    while !lc2.0.is_zero() {
        let (wholepart, remainder) = BigInt::div_rem(&lc1.0, &lc2.0);

        //    lc1.0 = wholepart * lc2.0 + remainder
        // => remainder = lc1.0 - wholepart * lc2.0
        //    = (a * lc1.1 + b * lc1.2) - wholepart * (a * lc2.1 + b * lc2.2)
        //    = a * (lc1.1 - wholepart * lc2.1) + b * (lc1.2 - wholepart * lc2.2)
        // so lc1.1 -= wholepart * lc2.1, and similar for .2,
        // and then swap them so that they stay in descending order.
        lc1.0 = remainder;
        lc1.1 -= &wholepart * &lc2.1;
        lc1.2 -= &wholepart * &lc2.2;
        std::mem::swap(&mut lc1, &mut lc2);
    }

    lc1
}

// But this does not help us enumerate simplified versions of fractions...
// [a; b, c, ...] = a + 1/[b; c, d, ...]
//    = (a * [b; c, d, ...] + 1)/[b; c, d, ...]
//    = (a * (b + 1/[c; d, ...]) + 1)/(b + 1/[c; d, ...])
//    = (a * b + 1 + a/[c; d, ...])/(b + 1/[c; d, ...])
//    = ((a * b + 1) * [c; d, ...] + a)/(b * [c; d, ...] + 1)
//    = ((a * b + 1) * (c + 1/[d; ...]))/(b * (c + 1/[d; ...]) + 1)
//    = ((a * b + 1) * c + (a * b + 1)/[d; ...])/(b * c + b/[d; ...] + 1)
//    = ((a * b * c + c) * [d; ...] + a * b + 1)/((b * c + 1) * [d; ...] + b)
//
// So the general pattern seems to be
// (w * [a; b, c, ...] + x)/(y * [a; b, c, ...] + z)
// = (w * (a + 1/[b; c, ...]) + x)/(y * (a + 1/[b; c, ...]) + z)
// = (w * a + x + w/[b; c, ...])/(y * a + z + y/[b; c, ...])
// = ((w * a + x) * [b; c, ...] + w)/((y * a + z) * [b; c, ...] + y)
//
// ...which is like Euclids, but we are adding instead of subtracting!
// Interesting!
//
// Okay and then if instead of [q; b, c, ...] we write n/d, and instead of
// [b; c, ...] we write d/r, where n = q * d + r, then each step looks like
// (w * (n/d) + x)/(y * (n/d) + z)
// = ((w * q + x) * (d/r) + w)/((y * q + z) * (d/r) + y)

pub struct SimplifiedFractionIter {
    nrem: BigInt, // n
    drem: BigInt, // d
    // numerator = frac_coeff * (nrem / drem) + const
    numerator_frac_coeff: BigInt,
    numerator_const: BigInt,
    // similar for denominator
    denominator_frac_coeff: BigInt,
    denominator_const: BigInt,
}

impl SimplifiedFractionIter {
    pub fn new(n: BigInt, d: BigInt) -> Self {
        // n / d = (1 * (n / d) + 0)/(0 * (n / d) + 1)
        SimplifiedFractionIter {
            nrem: n,
            drem: d,
            numerator_frac_coeff: BigInt::from(1),
            numerator_const: BigInt::from(0),
            denominator_frac_coeff: BigInt::from(0),
            denominator_const: BigInt::from(1),
        }
    }

    pub fn from_float(value: BigFloat) -> Self {
        let (n, d) = float_to_ratio(value);
        SimplifiedFractionIter::new(n, d)
    }
}

impl Iterator for SimplifiedFractionIter {
    type Item = BigRational;
    fn next(self: &mut SimplifiedFractionIter) -> Option<BigRational> {
        use num_traits::Zero;
        use num_integer::Integer;

        if self.drem.is_zero() {
            return None;
        }

        let (wholepart, remainder) = BigInt::div_rem(&self.nrem, &self.drem);
        let numapprox = &self.numerator_frac_coeff * &wholepart + &self.numerator_const;
        let denomapprox = &self.denominator_frac_coeff * &wholepart + &self.denominator_const;

        let prev = std::mem::replace(&mut self.numerator_frac_coeff, numapprox.clone());
        self.numerator_const = prev;

        let prev = std::mem::replace(&mut self.denominator_frac_coeff, denomapprox.clone());
        self.denominator_const = prev;

        self.nrem = std::mem::replace(&mut self.drem, remainder);

        Some(BigRational::new_raw(numapprox, denomapprox))
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

    #[test]
    fn test_euclids() {
        use num_traits::One;

        let a = BigInt::from(100);
        let b = BigInt::from(17);
        let (gcd, c1, c2) = euclids_alg(a.clone(), b.clone());
        assert_eq!(gcd, c1 * a + c2 * b);
        assert!(gcd.is_one());
    }

    #[test]
    fn test_simplify_iter() {
        use num_traits::Zero;
        use num_traits::Signed;

        let val = BigFloat::from(12.1234);
        let iter = SimplifiedFractionIter::from_float(val);
        let actual = BigRational::new(iter.nrem.clone(), iter.drem.clone());
        let frac = |n, d| BigRational::new(BigInt::from(n), BigInt::from(d));

        let mut prev_err = frac(1, 1);
        for next in iter {
            let err = BigRational::abs(&(next - &actual));
            assert!(err < prev_err);
            prev_err = err;
        }
        assert!(prev_err.is_zero());
    }
}

