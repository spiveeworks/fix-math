use fixlab::big_float::BigFloat;
use fixlab::remez;
use fixlab::reference;
use fixlab::euclids_alg;

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
    let iter = euclids_alg::RatApproxIter::from_float(val);
    for val in iter {
        println!("{} = {}", val, fixlab::decimal::Decimal::calculate(&val, 160));
    }
}
