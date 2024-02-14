pub mod big_float;
pub mod poly;

pub mod euclids_alg;
pub mod decimal;

pub mod bisect;
pub mod reference;

use big_float::BigFloat;
use poly::Polynomial;

pub fn remez<F>(
    f: F,
    xl: &BigFloat,
    xr: &BigFloat,
    order: usize,
    target_exponent: i64,
    iterations: u32
) -> Result<(Polynomial, BigFloat), bisect::BisectionError>
    where F: Fn(&BigFloat) -> BigFloat
{
    let mut sample_at = Vec::with_capacity(order + 2);
    {
        sample_at.push(xl.clone());

        let mut dx = xr - xl;
        // Just make sure there is *some* room for distinguishing the sample
        // points. This is a deliberately bad guess, so it doesn't matter if
        // there is representation error, as long as the sample points are
        // spaced apart at all.
        dx.adjust_exponent(dx.exponent - 8);
        dx.mantissa /= order + 1;

        let mut x = xl.clone();
        for _ in 0..order {
            x += &dx;
            sample_at.push(x.clone());
        }

        sample_at.push(xr.clone());
    }

    let zero = BigFloat{
        mantissa: num_bigint::BigInt::from(0),
        exponent: 0,
    };

    // Declare the results, for the loop to write out to.
    let mut polynomial = Polynomial{
        coefficients: Vec::new(),
        target_exponent: target_exponent
    };
    let mut worst_error = zero.clone();
    for _ in 0..iterations {
        // Evaluate the function at the specified points
        let mut points = Vec::with_capacity(order + 2);
        for x in sample_at {
            let y = f(&x);
            points.push((x, y));
        }

        // Calculate a polynomial with errors that alternate at these points
        polynomial = remez_interpolation(&points, target_exponent);
        println!("Polynomial: {}", polynomial);

        // Sample the error function, to find its extrema.
        // let err_fun = |x| poly::eval(&polynomial, x) - f(x);

        let mut extrema = Vec::with_capacity(order + 2);
        // Already declared outside of this loop.
        // let mut worst_error;
        let mut best_error;

        extrema.push(xl.clone());

        use num_traits::Signed;
        {
            let mut error = poly::eval(&polynomial, xl) - f(xl);
            error.mantissa = error.mantissa.abs();
            worst_error = error.clone();
            best_error = error;
        }

        for i in 0..order {
            let (new_x, mut error) = bisect::bisect_turning_point(
                |x| poly::eval(&polynomial, x) - f(x),
                points[i].0.clone(),
                points[i + 1].0.clone(),
                points[i + 2].0.clone(),
            )?;

            // Check the error value at this extremum.
            error.mantissa = error.mantissa.abs();
            if &error > &worst_error {
                worst_error = error.clone();
            }
            if &error < &best_error {
                best_error = error.clone();
            }

            // Store the location itself, to continue the algorithm.
            extrema.push(new_x);
        }

        extrema.push(xr.clone());
        {
            let mut error = poly::eval(&polynomial, xr) - f(xr);
            error.mantissa = error.mantissa.abs();
            if &error > &worst_error {
                worst_error = error.clone();
            }
            if &error < &best_error {
                best_error = error.clone();
            }
        }

        worst_error.adjust_exponent(target_exponent);
        best_error.adjust_exponent(target_exponent);

        // Repeat the process, using this iteration's extrema as the location
        // to put the errors next time.
        sample_at = extrema;

        println!("Iteration complete.");
        println!("Polynomial: {}", polynomial);
        println!("Worst error: {}", worst_error);
        println!("Best error: {}", best_error);
        println!("");
    }

    Ok((polynomial, worst_error))
}

// Interpolate n+1 points using a degree n polynomial that misses the sample
// points by equal and opposite amounts each time.
fn remez_interpolation(points: &[(BigFloat, BigFloat)], target_exponent: i64) -> Polynomial {
    let (last_point, most_points) = points
        .split_last()
        .expect("remez_interpolation cannot be called with an empty list of sample points.");
    let exact_interp = poly::interpolate(most_points, target_exponent);

    let mut alternating_sample = Vec::with_capacity(most_points.len());
    let mut sign = BigFloat{
        mantissa: num_bigint::BigInt::from(1),
        exponent: 0
    };
    for (x, _) in most_points {
        alternating_sample.push((x.clone(), sign.clone()));
        sign = -sign;
    }
    let alternating_interp = poly::interpolate(&alternating_sample, target_exponent);

    let (last_x, last_y) = last_point;
    // We want to set result = exact_interp + err * alternating_interp
    // this means eval(result, last_x) will be
    // eval(exact_interp, last_x) + err * eval(alternating_interp, last_x)
    // we want this to be equal to last_y + err * sign, so that the equal and
    // opposite errors are
    // sustained for all n+1 sample points, so *solve for err* using these two
    // equations. This error could end up being huge or tiny, depending on how
    // well the sample points themselves were chosen.
    let exact_actual = poly::eval(&exact_interp, last_x);
    let alternating_actual = poly::eval(&alternating_interp, last_x);
    // we want exact_actual + err * alternating_actual = last_y + err * sign
    // => err * (alternating_actual - sign) = last_y - exact_actual
    // => err = (last_y - exact_actual) / (alternating_actual - sign)
    let mut err = last_y - exact_actual;
    let sign_err = alternating_actual - sign;
    if sign_err.exponent < 0 {
        // add precision to required_value, since we lose precision the more
        // precise the divisor is.
        err.adjust_exponent(err.exponent + sign_err.exponent);
    }
    err /= &sign_err;

    // Now calculate exact_interp + err * alternating_interp using a mul_add
    let mut result = exact_interp;
    poly::mul_add_constant(&mut result, &alternating_interp, &err);
    result
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_remez_interpolation() {
        let expected = Polynomial {
            coefficients: vec![
                BigFloat::from(4.0),
                BigFloat::from(3.0),
                BigFloat::from(2.0),
                BigFloat::from(1.0),
            ],
            target_exponent: -32,
        };
        // Evaluate the polynomial at a few points, adding equal and opposite
        // error values as well, to use as sample points.
        let mut err = BigFloat::from(5.0);
        let mut points = Vec::with_capacity(expected.coefficients.len() + 1);
        for i in 0..(expected.coefficients.len() + 1) {
            let x = BigFloat::from(i as f64);
            // subtract err, so that when the remez interpolation overshoots by
            // err, it gets back to the actual polynomial we started with.
            let y = poly::eval(&expected, &x) - &err;
            points.push((x, y));

            err = -err;
        }

        // Try to recover the polynomial from these perturbed sample points.
        let actual = remez_interpolation(&points, expected.target_exponent);

        assert_eq!(actual.coefficients.len(), expected.coefficients.len());
        assert_eq!(actual.target_exponent, expected.target_exponent);

        use num_traits::Signed;
        for i in 0..actual.coefficients.len() {
            let actual_c = &actual.coefficients[i];
            let expected_c = &expected.coefficients[i];
            let mut error = actual_c - expected_c;
            error.mantissa = error.mantissa.abs();
            // When pretty-printed, the error has an extra two zeros than this,
            // (0002 instead of 01,) but we can't seem to tighten this
            // constraint much without it failing? Are we pretty-printing
            // wrong?
            assert!(error < BigFloat::from(0.00000001), "error: {}", error);
        }
    }

    #[test]
    fn test_remez_alg() {
        let cubic = Polynomial {
            coefficients: vec![
                BigFloat::from(4.0),
                BigFloat::from(-3.0),
                BigFloat::from(0.0),
                BigFloat::from(1.0),
            ],
            target_exponent: -32,
        };
        let xl = BigFloat::from(0.25);
        let xr = BigFloat::from(1.5);
        let iterations = 3;
        let (p, err) = remez(
            |x| poly::eval(&cubic, x),
            &xl, &xr,
            cubic.coefficients.len() - 2, // give us one term fewer than what we are putting in
            cubic.target_exponent, // keep the same output precision
            iterations
        ).unwrap();
        assert!(err < BigFloat::from(0.1), "We ran the Remez algorithm for {} iterations, and got an error value of {}.", iterations, err);

        use num_traits::Signed;
        let mut x = xl;
        let dx = BigFloat::from(0.01);
        while x <= xr {
            let expected = poly::eval(&cubic, &x);
            let actual = poly::eval(&p, &x);
            let mut this_err = actual - expected;
            this_err.mantissa = this_err.mantissa.abs();
            if this_err > err {
                let excess = &this_err - &err;
                println!("excess: {}", excess.mantissa);
                assert!(excess.mantissa < num_bigint::BigInt::from(16), "Error at {} was {}, which was worse than the reported worst-case error of {}.", x, this_err, err);
            }

            x += &dx;
        }
    }
}
