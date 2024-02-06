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

// Usable as the derivative of sqrt
pub fn half_invsqrt(y: &BigFloat) -> BigFloat {
    let mut invsqrt = invsqrt(y);
    invsqrt.exponent -= 1;
    invsqrt
}

// usable as the derivative of invsqrt
pub fn neg_half_invsqrt_cubed(y: &BigFloat) -> BigFloat {
    let invsqrt = invsqrt(y);
    let mut cubed = &invsqrt * &invsqrt * &invsqrt;

    cubed.exponent -= 1;
    -cubed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bisect() {
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
}

