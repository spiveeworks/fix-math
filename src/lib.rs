pub mod big_float;

pub fn test() {
    let x = big_float::BigFloat::from(-10.57);
    println!("{}", x);
}

#[test]
fn do_test() {
    test();
}
