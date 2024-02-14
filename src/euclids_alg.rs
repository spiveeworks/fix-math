use num_bigint::BigInt;
use num_rational::BigRational;

use crate::big_float::BigFloat;

// The most basic version of Euclid's algorithm calculates the greatest common
// divisor of two numbers.
pub fn gcd_slow(mut a: BigInt, mut b: BigInt) -> BigInt {
    use num_traits::Zero;

    while !b.is_zero() {
        let remainder = a % &b;
        a = std::mem::replace(&mut b, remainder);
    }

    a
}

// This can also be done using faster integer operations.
pub fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
    use num_traits::Zero;

    let a_binfactors = a.trailing_zeros().unwrap_or(0);
    let b_binfactors = b.trailing_zeros().unwrap_or(a_binfactors);
    let result_binfactors = std::cmp::min(a_binfactors, b_binfactors);

    a >>= a_binfactors;
    b >>= b_binfactors;

    loop {
        if a.is_zero() {
            return b << result_binfactors;
        }
        if b.is_zero() {
            return a << result_binfactors;
        }

        if a >= b {
            a -= &b;
            a >>= a.trailing_zeros().unwrap_or(0);
        } else {
            b -= &a;
            b >>= b.trailing_zeros().unwrap_or(0);
        }
    }
}

// Euclid's algorithm can also be used to calculate linear combinations of the
// original number that are equal to the GCD itself. This is useful in modular
// arithmetic for calculating inverses of numbers mod m when gcd(x, m) = 1.
//
// e.g. gcd(100, 17) = 1
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
// Sanity-checking this expression, it is indeed 1.
// So at each step we need the previous two terms, both as a linear combination
// of the first two terms we were given. Then we try to calculate the next term
// as a linear combination of the first two we were given.

// The more useful version of Euclid's algorithm, for calculating the greatest
// common divisor AND a linear combination of the inputs that equals this GCD.
pub fn linear_combination(a: BigInt, b: BigInt) -> (BigInt, BigInt, BigInt) {
    use num_integer::Integer;
    use num_traits::Zero;

    // at all times lc.0 = a * lc.1 + b * lc.2, for both lc1 and lc2
    let mut lc1 = (a, BigInt::from(1), BigInt::from(0));
    let mut lc2 = (b, BigInt::from(0), BigInt::from(1));

    while !lc2.0.is_zero() {
        // TODO: Can we implement this using the subtract and rshift operations
        // instead?
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

// An alternative use of Euclid's algorithm is calculating continued fractions.
// This is where we break a fraction up into a mixed fraction, a whole part and
// a fractional part, and then recursing on the reciprocal of the fractional
// part. In practice this means calculating a quotient and remainder at each
// step, swapping the remainder with the divisor, and repeating. This is just
// Euclid's algorithm again, but we output all of the quotients, instead of the
// final remainder.
//
// We can implement this as an iterator, and then rust people can do whatever
// they want with it, collect it into a list, or filter it some which way
// first.
#[derive(Clone)]
pub struct ContinuedFractionIter {
    // We don't want to use BigRational for this, since BigRational seems to
    // GCD/Euclid's algorithm with every operation, and the whole goal here is
    // to extract the results OF a single Euclid's algorithm.
    pub numerator: BigInt,
    pub denominator: BigInt,
}

impl ContinuedFractionIter {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Self {
        ContinuedFractionIter { numerator, denominator }
    }
    pub fn from_float(value: BigFloat) -> Self {
        let (n, d) = float_to_ratio(value);

        ContinuedFractionIter::new(n, d)
    }
}

fn float_to_ratio(value: BigFloat) -> (BigInt, BigInt) {
    if value.exponent < 0 {
        (value.mantissa, BigInt::from(1) << -value.exponent)
    } else {
        (value.mantissa << value.exponent, BigInt::from(1))
    }
}

impl Iterator for ContinuedFractionIter {
    type Item = i32;
    fn next(self: &mut ContinuedFractionIter) -> Option<i32> {
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

// Given a continued fraction we can calculate the actual ratio in question.
// This can be used on a subset of the continued fraction to get an
// approximation of the ratio.
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

// One funny use case for this is if a float literal or float calculation
// consists entirely of rational values and operations, then the continued
// fraction of the float result will be the continued fraction of the actual
// exact result, then a huuuuge number representing the tiny error introduced
// by representation, then some more junk to more exactly specify that
// representation error. By stripping off all the junk introduced by
// representation error, we can infer the exact value *from* the approximate
// value.
pub fn recover_rational_from_float(x: BigFloat) -> BigRational {
    let iter = ContinuedFractionIter::from_float(x);
    let terms: Vec<i32> = iter.collect();
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

// In fact, truncated continued fractions are useful for lots of things. Each
// truncation can be collected into an increasingly accurate rational
// approximation of the input, whether the input was originally a rational, a
// float, a float approximation of some irrational value, or a float
// approximation produced through measurement or numerical techniques. While
// the above functions are enough to calculate these approximations, it would
// be really nice to generate all of them in one pass, similar to how we the
// integer linear combinations in one pass earlier.
//
// Let's try an algebraic example, to see if there is some inductive form we
// can use as the state of an iterator.
// [a; b, c, ...] = a + 1/[b; c, d, ...]
//    = (a * [b; c, d, ...] + 1)/[b; c, d, ...]
//    = (a * (b + 1/[c; d, ...]) + 1)/(b + 1/[c; d, ...])
//    = (a * b + 1 + a/[c; d, ...])/(b + 1/[c; d, ...])
//    = ((a * b + 1) * [c; d, ...] + a)/(b * [c; d, ...] + 1)
//    = ((a * b + 1) * (c + 1/[d; ...]))/(b * (c + 1/[d; ...]) + 1)
//    = ((a * b + 1) * c + (a * b + 1)/[d; ...])/(b * c + b/[d; ...] + 1)
//    = ((a * b * c + c) * [d; ...] + a * b + 1)/((b * c + 1) * [d; ...] + b)
//
// The general pattern seems to be
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

pub struct RatApproxIter {
    // TODO: Store a generic I: Iterator<Item=i32> here, so that we can start
    // introducing more lazy continued fractions, like one for square roots,
    // logs, or maybe even pi and stuff.
    nrem: BigInt, // n
    drem: BigInt, // d
    // numerator = frac_coeff * (nrem / drem) + const
    numerator_frac_coeff: BigInt,
    numerator_const: BigInt,
    // similar for denominator
    denominator_frac_coeff: BigInt,
    denominator_const: BigInt,
}

impl RatApproxIter {
    pub fn new(n: BigInt, d: BigInt) -> Self {
        // n / d = (1 * (n / d) + 0)/(0 * (n / d) + 1)
        RatApproxIter {
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
        RatApproxIter::new(n, d)
    }
}

impl Iterator for RatApproxIter {
    type Item = BigRational;
    fn next(self: &mut RatApproxIter) -> Option<BigRational> {
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
    fn test_gcd() {
        let do_test = |a, b| {
            let result1 = gcd_slow(BigInt::from(a), BigInt::from(b));
            let result2 = gcd_slow(BigInt::from(a), BigInt::from(b));
            assert_eq!(result1, result2);
        };

        // Start with the hairy cases
        do_test(0, 0);
        do_test(0, 10);
        do_test(10, 0);

        do_test(100, 1000);
        do_test(3, 2);
        do_test(100, 51);
        do_test(12, 18);
    }

    #[test]
    fn test_euclids() {
        use num_traits::One;

        let a = BigInt::from(100);
        let b = BigInt::from(17);
        let (gcd, c1, c2) = linear_combination(a.clone(), b.clone());
        assert_eq!(gcd, c1 * a + c2 * b);
        assert!(gcd.is_one());
    }

    #[test]
    fn test_continued_fractions() {
        let n = BigInt::from(121234);
        let d = BigInt::from(10000);
        let iter = ContinuedFractionIter{
            numerator: n.clone(),
            denominator: d.clone(),
        };
        let terms: Vec<i32> = iter.collect();
        // the 226995948 is the floating point error. The terms before that
        // give 12.1234 exactly.
        assert_eq!(terms, vec![12, 8, 9, 1, 1, 1, 3, 1, 1, 2]);

        let rat = collect_continued_fraction(&terms);
        let rat_expected = BigRational::new(n, d);
        assert_eq!(rat, rat_expected);
    }

    #[test]
    fn test_simplify() {
        // Simplify the fraction by removing the largest (thus least
        // contributing) term. Ironically this just strips off the floating
        // point error, and recovers 121234/10000 as a fraction. (Or half of
        // this.)
        let simplified = recover_rational_from_float(BigFloat::from(12.1234));
        let expected = BigRational::new(BigInt::from(121234), BigInt::from(10000));
        println!("Value: {}", expected);
        assert_eq!(&simplified, &expected);
    }

    #[test]
    fn test_simplify_iter() {
        use num_traits::Zero;
        use num_traits::Signed;

        let val = BigFloat::from(12.1234);
        let iter = RatApproxIter::from_float(val);
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

