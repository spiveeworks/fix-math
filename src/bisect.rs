use crate::big_float::BigFloat;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BisectionError {
    EndpointsEqual,
    EndpointsSameSide(std::cmp::Ordering),
    MidpointBetween, // When searching for a turning point.
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
        println!("Error: f({}) = {}, and f({}) = {}, both on the same side of {}.", xl, yl, xr, y2, y);
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

// We would unit test the bisect function by getting it to calculate a square
// root or something, but why not do that in reference.rs where we can actually
// export the process of calculating square roots?

pub fn bisect_turning_point<F>(f: F, mut xl: BigFloat, mut xm: BigFloat, mut xr: BigFloat)
    -> Result<(BigFloat, BigFloat), BisectionError>
        where F: Fn(&BigFloat) -> BigFloat
{
    use std::cmp::Ordering;

    let xorder = Ord::cmp(&xl, &xr);
    if xorder == Ordering::Greater {
        std::mem::swap(&mut xl, &mut xr);
    } else if xorder == Ordering::Equal {
        return Err(BisectionError::EndpointsEqual);
    }

    let yl = f(&xl);
    let mut ym = f(&xm);
    let yr = f(&xr);
    let morder = Ord::cmp(&ym, &yl);
    if morder == Ordering::Equal {
        // e.g. yl = ym < yr, don't know where to look for a turning point
        return Err(BisectionError::MidpointBetween);
    }
    if Ord::cmp(&ym, &yr) != morder {
        // e.g. yl < ym <= yr, don't know where to look for a turning point
        return Err(BisectionError::MidpointBetween);
    }

    loop {
        let mut left = &xl + &xm;
        left.mantissa >>= 1;
        let ldistinct = left != xl && left != xm;
        if ldistinct {
            let y = f(&left);
            let yorder = Ord::cmp(&y, &ym);
            if yorder == morder {
                // above the peak, replace it, and use the old peak as the new
                // right endpoint, l left m r -> l left m
                xr = xm;
                xm = left;
                ym = y;
            } else {
                // below or at the peak, just bring the left endpoint in
                // l left m r -> left m r
                xl = left;
            }
        }

        let mut right = &xm + &xr;
        right.mantissa >>= 1;
        let rdistinct = right != xm && right != xr;
        if rdistinct {
            let y = f(&right);
            let yorder = Ord::cmp(&y, &ym);
            if yorder == morder {
                // above the peak, replace it, and use the old peak as the new
                // left endpoint, l m right r -> m right r
                xl = xm;
                xm = right;
                ym = y;
            } else {
                // below the peak, just bring the right endpoint in
                // l m right r -> l m right
                xr = right;
            }
        }

        if !ldistinct && !rdistinct {
            return Ok((xm, ym));
        }
        // else continue
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn square(x: &BigFloat) -> BigFloat {
        x * x
    }

    #[test]
    fn test_turning_point() {
        let xl = BigFloat::from(-5.0);
        let xm = BigFloat::from(1.0);
        let xr = BigFloat::from(2.0);
        let extremum = bisect_turning_point(square, xl, xm, xr);
        assert_eq!(extremum.unwrap(), (BigFloat::from(0.0), BigFloat::from(0.0)));
    }
}

