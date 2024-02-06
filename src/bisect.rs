use crate::big_float::BigFloat;

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
