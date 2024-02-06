use fixlab::big_float::BigFloat;
use fixlab::remez;
use fixlab::reference;

fn main() {
    let precision = -32;
    let xl = BigFloat::from(0.5).with_exponent(precision);
    let xr = BigFloat::from(2.0).with_exponent(precision);
    let (p, err) = remez(
        reference::square_root,
        reference::half_invsqrt,
        &xl, &xr,
        6,
        precision,
        5
    ).unwrap();

    println!("Final polynomial: {}, error: {}", p, err);
}
