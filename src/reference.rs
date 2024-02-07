// Slow but arbitrarily accurate functions for sampling and finding
// approximations.

use crate::big_float::BigFloat;
use crate::bisect;

fn square(x: &BigFloat) -> BigFloat {
    let xx = BigFloat {
        mantissa: &x.mantissa * &x.mantissa,
        exponent: 2 * x.exponent,
    };
    return xx.with_exponent(x.exponent);
}

pub fn square_root(y: &BigFloat) -> BigFloat {
    use std::cmp::Ordering;
    if y < &BigFloat::from(0.0) {
        return BigFloat::from(0.0);
    }

    let xl;
    let xr;
    match std::cmp::Ord::cmp(y, &BigFloat::from(1.0)) {
        Ordering::Less => {
            xl = y.clone();
            xr = BigFloat::from(1.0).with_exponent(y.exponent);
        },
        Ordering::Equal => {
            return BigFloat::from(1.0);
        },
        Ordering::Greater => {
            xl = BigFloat::from(1.0).with_exponent(y.exponent);
            xr = y.clone();
        },
    }

    bisect::bisect(square, xl, xr, &y).unwrap()
}

pub fn reciprocol(y: &BigFloat) -> BigFloat {
    let mut val = BigFloat {
        mantissa: num_bigint::BigInt::from(1),
        exponent: 0,
    };
    val.adjust_exponent(2 * y.exponent);
    val /= y;
    val
}

pub fn invsqrt(y: &BigFloat) -> BigFloat {
    reciprocol(&square_root(y))
}

pub fn log2(y: &BigFloat) -> BigFloat {
    use num_traits::Signed;
    use num_bigint::BigInt;

    if !y.mantissa.is_positive() {
        panic!("Tried to take the log of {}.", y);
    }

    let ilog2 = y.mantissa.bits() as i64 - 1 + y.exponent;

    // Initialise the result to the integer log, so we can add fractional bits.
    let mut x = BigFloat {
        mantissa: BigInt::from(ilog2),
        exponent: 0,
    };
    if y.exponent >= 0 {
        // No fractional bits required, just return the whole part.
        return x;
    }

    // Multiply or divide by 2, ilog2 times, giving something in [1, 2).
    // Calculating the log of this will give us the fractional part of x.
    let mut y_shifted = y.clone();
    if ilog2 > 0 {
        y_shifted.mantissa >>= ilog2;
    } else if ilog2 < 0 {
        y_shifted.mantissa <<= -ilog2;
    }

    let mut two = BigFloat {
        mantissa: BigInt::from(2),
        exponent: 0,
    };
    two.adjust_exponent(y.exponent);

    while x.exponent > y.exponent {
        y_shifted = &y_shifted * &y_shifted;
        y_shifted.adjust_exponent(y.exponent);
        let next_bit_set = y_shifted > two;

        x.mantissa <<= 1;
        x.exponent -= 1;

        if next_bit_set {
            x.mantissa += 1;
            y_shifted.mantissa >>= 1;
        }
    }

    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_square_root() {
        let y = BigFloat::from(2.0).with_exponent(-256);

        let sqrt_y = square_root(&y);

        use num_traits::Signed;
        let err = &y - &square(&sqrt_y);
        assert!(
            err.mantissa.abs() < num_bigint::BigInt::from(4),
            "Error was too high: {}",
            err
        );
    }

    #[test]
    fn test_log_whole() {
        for i in -10..10 {
            let y = BigFloat {
                mantissa: num_bigint::BigInt::from(1) << 10,
                exponent: i,
            };
            let x = log2(&y);
            assert_eq!(x, BigFloat::from(i as f64 + 10.0));
        }
    }

    #[test]
    fn test_log_products() {
        use num_traits::Signed;

        for i in 1..20 {
            for j in 1..20 {
                let y1 = BigFloat::from(i as f64).with_exponent(-64);
                let y2 = BigFloat::from(j as f64).with_exponent(-64);
                let x1 = log2(&y1);
                let x2 = log2(&y2);
                let y12 = BigFloat::with_exponent(y1 * y2, -64);
                let x12 = log2(&y12);

                let mut error = &x1 + &x2 - &x12;
                error.mantissa = error.mantissa.abs();
                assert!(error.mantissa < num_bigint::BigInt::from(2), "Error was too high: {:?}.", error);
            }
        }
    }
}

