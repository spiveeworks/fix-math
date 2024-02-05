use num_bigint::BigInt;
use super::big_float::BigFloat;

#[derive(Debug, PartialEq)]
pub struct Polynomial {
    pub coefficients: Vec<BigFloat>,
    pub target_exponent: i64,
}

impl std::fmt::Display for Polynomial {
    fn fmt(self: &Polynomial, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use num_traits::Zero;

        let mut printed_something = false;
        for i in (0..self.coefficients.len()).rev() {
            let c = &self.coefficients[i];
            if !c.mantissa.is_zero() {
                if printed_something {
                    write!(f, " + ")?;
                }

                write!(f, "{}", c)?;
                if i == 1 {
                    write!(f, "*x")?;
                } else if i > 1 {
                    write!(f, "*x^{}", i)?;
                }

                printed_something = true;
            }
        }
        if !printed_something {
            write!(f, "0")?;
        }

        Ok(())
    }
}

pub fn eval(p: &Polynomial, x: &BigFloat) -> BigFloat {
    let mut y = BigFloat{
        mantissa: BigInt::from(0),
        exponent: 0,
    };
    for c in p.coefficients.iter().rev() {
        y *= x;
        y.adjust_exponent(p.target_exponent);
        y += c;
        y.adjust_exponent(p.target_exponent);
    }
    y
}

pub fn mul_add(out: &mut Polynomial, a: &Polynomial, b: &Polynomial) {
    for i in 0..a.coefficients.len() {
        for j in 0..b.coefficients.len() {
            let mut prod = &a.coefficients[i] * &b.coefficients[j];
            prod.adjust_exponent(out.target_exponent);
            if i + j < out.coefficients.len() {
                out.coefficients[i + j] += prod;
            } else {
                // Since we are counting up indices one at a time, indices that
                // aren't already here simply go on the end.
                out.coefficients.push(prod);
            }
        }
    }
}

pub fn mul_add_constant(out: &mut Polynomial, a: &Polynomial, b: &BigFloat) {
    for i in 0..a.coefficients.len() {
        let mut prod = &a.coefficients[i] * b;
        prod.adjust_exponent(out.target_exponent);
        if i < out.coefficients.len() {
            out.coefficients[i] += prod;
        } else {
            // Since we are counting up indices one at a time, indices that
            // aren't already here simply go on the end.
            out.coefficients.push(prod);
        }
    }
}

fn mul(a: &Polynomial, b: &Polynomial) -> Polynomial {
    let mut out = Polynomial {
        coefficients: Vec::with_capacity(a.coefficients.len() + b.coefficients.len() - 1),
        target_exponent: std::cmp::min(a.target_exponent, b.target_exponent),
    };

    mul_add(&mut out, a, b);

    out
}

impl<'a, 'b> std::ops::Mul<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;
    fn mul(self: &'a Polynomial, other: &'b Polynomial) -> Polynomial {
        mul(self, other)
    }
}

pub fn interpolate(points: &[(BigFloat, BigFloat)], target_exponent: i64) -> Polynomial {
    let one = BigFloat{
        mantissa: BigInt::from(1),
        exponent: 0,
    };

    // Polynomial that equals zero for all of the x values processed so far
    let mut zeroed = Polynomial {
        coefficients: Vec::new(),
        target_exponent: target_exponent
    };
    // Initialise to a non-zero constant, so that we can multiply in binomials.
    zeroed.coefficients.push(one.clone());

    // Polynomial that equals the desired value for all of the x values
    // processed so far
    let mut out = Polynomial {
        coefficients: Vec::with_capacity(points.len()),
        target_exponent: target_exponent,
    };

    for (x, y) in points {
        // Out currently passes through all the previously considered points,
        // but misses the current point by a certain amount.
        let current_height = eval(&out, &x);
        // Set required_value to be relative to what we already have.
        let mut required_value = y - &current_height;
        // Now if we had a polynomial that were zero at all the previously
        // considered points, but required_value at x, then we could add that
        // to our current polynomial, and continue to the next iteration of the
        // loop. To do this we rescale zeroed to whatever will give this
        // property.
        let actual_zeroed_height = eval(&zeroed, &x);
        if actual_zeroed_height.exponent < 0 {
            // add precision to required_value, since we lose precision the
            // more precise the divisor is.
            let new_exponent = required_value.exponent + actual_zeroed_height.exponent;
            required_value.adjust_exponent(new_exponent);
        }
        required_value /= &actual_zeroed_height;
        mul_add_constant(&mut out, &zeroed, &required_value);

        // Now update zeroed so that it is zero at this x value as well.
        let binomial = Polynomial {
            coefficients: vec![-x.clone(), one.clone()],
            target_exponent: zeroed.target_exponent,
        };
        zeroed = &zeroed * &binomial;

        // println!("Interpolated ({}, {}), polynomial = {}, zeroed = {}", x, y, out, zeroed);
    }

    out
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn eval_test() {
        let p = Polynomial {
            coefficients: vec![
                BigFloat::from(5.0),
                BigFloat::from(0.5),
                BigFloat::from(1.0),
            ],
            target_exponent: -64,
        };
        let x = BigFloat::from(10.0).with_exponent(p.target_exponent);
        let y = eval(&p, &x);
        let expected = BigFloat::from(10.0 * 10.0 + 0.5 * 10.0 + 5.0);
        assert_eq!(&y, &expected);
    }

    #[test]
    fn interpolate_test() {
        let expected = Polynomial {
            coefficients: vec![
                BigFloat::from(4.0),
                BigFloat::from(3.0),
                BigFloat::from(2.0),
                BigFloat::from(1.0),
            ],
            target_exponent: -32,
        };

        // Evaluate the polynomial at a few points, to use as sample points.
        let mut points = Vec::with_capacity(expected.coefficients.len());
        for i in 0..expected.coefficients.len() {
            let x = BigFloat::from(i as f64);
            let y = eval(&expected, &x);
            points.push((x, y));
        };

        // Try to recover the polynomial from its sample points.
        let actual = interpolate(&points, expected.target_exponent);

        assert_eq!(actual, expected);
    }
}
