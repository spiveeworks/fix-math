use fixlab::big_float::BigFloat;
use fixlab::remez;
use fixlab::reference;

fn main() {
    let precision = -32;

    /*
    let xl = BigFloat::from(0.5).with_exponent(precision);
    let xr = BigFloat::from(2.0).with_exponent(precision);
    let (p, err) = remez(
        reference::square_root,
        &xl, &xr,
        6,
        precision,
        5
    ).unwrap();
    */

    /*
    let xl = BigFloat::from(0.5).with_exponent(precision);
    let xr = BigFloat::from(2.0).with_exponent(precision);
    let (p, err) = remez(
        reference::invsqrt,
        &xl, &xr,
        6,
        precision,
        5
    ).unwrap();
    */

    let xl = BigFloat::from(1.0).with_exponent(precision);
    let xr = BigFloat::from(2.0).with_exponent(precision);
    let (p, err) = remez(
        reference::log2,
        &xl, &xr,
        6,
        precision,
        5
    ).unwrap();

    println!("Final polynomial: {}, error: {}", p, err);

    let val = BigFloat::from(12.1234).with_exponent(-256);
    let iter = fixlab::number::SimplifiedFractionIter::from_float(val);
    for val in iter {
        let mut as_float = BigFloat {
            mantissa: val.numer().clone(),
            exponent: 0,
        };
        as_float.adjust_exponent(-64);
        as_float.mantissa /= val.denom();
        println!("{} = {}", val, as_float);
    }
}
