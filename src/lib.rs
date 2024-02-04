pub mod big_float;
pub mod poly;

use big_float::BigFloat;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BisectionError {
    EndpointsEqual,
    EndpointsSameSide(std::cmp::Ordering),
}

pub fn bisect<F>(f: F, mut xl: BigFloat, mut xr: BigFloat, y: &BigFloat)
    -> Result<BigFloat, BisectionError>
        where F: Fn(&BigFloat) -> BigFloat
{
    use std::cmp::Ordering;

    let xorder = Ord::cmp(&xl, &xr);
    if xorder == Ordering::Greater {
        std::mem::swap(&mut xl, &mut xr);
    }

    let yl = f(&xl);
    let lorder = Ord::cmp(&yl, y);
    if lorder == Ordering::Equal {
        return Ok(xl);
    }

    let y2 = f(&xr);
    let rorder = Ord::cmp(&y2, y);
    if rorder == Ordering::Equal {
        return Ok(xr);
    }

    if xorder == Ordering::Equal {
        return Err(BisectionError::EndpointsEqual);
    }

    if lorder == rorder {
        return Err(BisectionError::EndpointsSameSide(lorder));
    }

    loop {
        let mut xm = &xl + &xr;
        xm.mantissa >>= 1;
        if &xm == &xl || &xm == &xr {
            return Ok(xl);
        }

        let ym = f(&xm);
        let morder = Ord::cmp(&ym, y);
        if morder == Ordering::Equal {
            return Ok(xm);
        }

        // Replace one of the endpoints and continue.
        if morder == lorder {
            xl = xm;
        } else {
            xr = xm;
        }
    }
}

pub fn test() {
    let x = big_float::BigFloat::from(-10.57);
    println!("{}", x);
}

#[cfg(test)]
mod tests {
    use super::*;
    fn square(x: &BigFloat) -> BigFloat {
        let xx = BigFloat {
            mantissa: &x.mantissa * &x.mantissa,
            exponent: 2 * x.exponent,
        };
        return xx.with_exponent(x.exponent);
    }

    #[test]
    fn do_test() {
        let y = BigFloat::from(2.0);

        let xl = BigFloat::from(1.0).with_exponent(-256);
        let xr = BigFloat::from(2.0).with_exponent(-256);
        let sqrt_y = bisect(square, xl, xr, &y).unwrap();
        println!("The square root of {} was calculated to be {}", y, sqrt_y);

        use num_traits::Signed;
        let err = &y - &square(&sqrt_y);
        assert!(
            err.mantissa.abs() < num_bigint::BigInt::from(4),
            "Error was too high: {}",
            err
        );
    }
}
