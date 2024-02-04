use num_bigint::BigInt;
use super::big_float::BigFloat;

pub struct Polynomial {
    pub coefficients: Vec<BigFloat>,
    pub target_exponent: i64,
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
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
}
