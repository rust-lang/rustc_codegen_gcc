#![feature(const_option)]

use std::num::{NonZeroU8, NonZeroI8, NonZeroU16, NonZeroI16, NonZeroU32, NonZeroI32, NonZeroU64, NonZeroI64, NonZeroU128, NonZeroI128, NonZeroUsize, NonZeroIsize};

fn main() {
    /*test_float!(f64, f64, f64::INFINITY, f64::NEG_INFINITY, f64::NAN);
    ($modname: ident, $fty: ty, $inf: expr, $neginf: expr, $nan: expr) => {*/

    /*assert_eq!((0.0 as f64).min(0.0), 0.0);
    assert!((0.0 as f64).min(0.0).is_sign_positive());
    assert_eq!((-0.0 as f64).min(-0.0), -0.0);
    assert!((-0.0 as f64).min(-0.0).is_sign_negative());
    assert_eq!((9.0 as f64).min(9.0), 9.0);
    assert_eq!((-9.0 as f64).min(0.0), -9.0);
    assert_eq!((0.0 as f64).min(9.0), 0.0);
    assert!((0.0 as f64).min(9.0).is_sign_positive());
    assert_eq!((-0.0 as f64).min(9.0), -0.0);
    assert!((-0.0 as f64).min(9.0).is_sign_negative());*/

    //println!("{}", 9);
    //println!("{}", 9.0_f32);
    //assert_eq!(-9.0_f32, -9 as f32);

    //assert_eq!("1", format!("{:.0}", 1.0f64));
    //assert_eq!("9", format!("{:.0}", 9.4f64));
    //assert_eq!("10", format!("{:.0}", 9.9f64));
    //assert_eq!("9.8", format!("{:.1}", 9.849f64));
    //assert_eq!("9.9", format!("{:.1}", 9.851f64));
    //assert_eq!("1", format!("{:.0}", 0.5f64));

    //assert_eq!(2.3f32.copysign(-1.0), -2.3f32);
    /*let f = 9.4f32;
    println!("{}", f);*/
    //println!("{}", 9.4f32); // FIXME: this is using bytes_in_context(), but gives a wrong value.

    /*extern {
        //pub fn printf(format: *const i8, ...) -> i32;
        pub fn printf(format: *const i8, arg: f64) -> i32;
    }

    unsafe {
        printf(b"Num: %f\n\0" as *const _ as *const _, 9.4f64);
    }
    println!("{}", 9.4f64);*/

    // FIXME: the code seems to be the same when using an integer, but somehow, it doesn't work for
    // a float. Could it be related to the fact that floating-points use different registers?

    /*let f = 1234567.89f64;
    assert_eq!("1.23456789e6", format!("{:e}", f));
    println!("{:e}", f);
    println!("{:e}", 1234567.89f64);*/
    //assert_eq!("1.23456789e6", format!("{:e}", 1234567.89f64));
    /*assert_eq!("1.23456789e3", format!("{:e}", 1234.56789f64));
    assert_eq!("1.23456789E6", format!("{:E}", 1234567.89f64));
    assert_eq!("1.23456789E3", format!("{:E}", 1234.56789f64));
    assert_eq!("0.0", format!("{:?}", 0.0f64));
    assert_eq!("1.01", format!("{:?}", 1.01f64));*/

    /*assert_eq!((-0.0 as f64).min(-9.0), -9.0);
    assert_eq!((f64::INFINITY as f64).min(9.0), 9.0);
    assert_eq!((9.0 as f64).min(f64::INFINITY), 9.0);
    assert_eq!((f64::INFINITY as f64).min(-9.0), -9.0);
    assert_eq!((-9.0 as f64).min(f64::INFINITY), -9.0);
    assert_eq!((f64::NEG_INFINITY as f64).min(9.0), f64::NEG_INFINITY);
    assert_eq!((9.0 as f64).min(f64::NEG_INFINITY), f64::NEG_INFINITY);
    assert_eq!((f64::NEG_INFINITY as f64).min(-9.0), f64::NEG_INFINITY);
    assert_eq!((-9.0 as f64).min(f64::NEG_INFINITY), f64::NEG_INFINITY);*/
    // Cranelift fmin has NaN propagation
    //assert_eq!((f64::NAN as f64).min(9.0), 9.0);
    //assert_eq!((f64::NAN as f64).min(-9.0), -9.0);
    //assert_eq!((9.0 as f64).min(f64::NAN), 9.0);
    //assert_eq!((-9.0 as f64).min(f64::NAN), -9.0);
    //assert!((f64::NAN as f64).min(f64::NAN).is_nan());

    /*let max: f64 = f32::MAX.into();
    assert_eq!(max as f32, f32::MAX);
    assert!(max.is_normal());

    let min: f64 = f32::MIN.into();
    assert_eq!(min as f32, f32::MIN);
    assert!(min.is_normal());

    let min_positive: f64 = f32::MIN_POSITIVE.into();
    assert_eq!(min_positive as f32, f32::MIN_POSITIVE);
    assert!(min_positive.is_normal());

    let epsilon: f64 = f32::EPSILON.into();
    assert_eq!(epsilon as f32, f32::EPSILON);
    assert!(epsilon.is_normal());

    let zero: f64 = (0.0f32).into();
    assert_eq!(zero as f32, 0.0f32);
    assert!(zero.is_sign_positive());

    let neg_zero: f64 = (-0.0f32).into();
    assert_eq!(neg_zero as f32, -0.0f32);
    assert!(neg_zero.is_sign_negative());

    let infinity: f64 = f32::INFINITY.into();
    assert_eq!(infinity as f32, f32::INFINITY);
    assert!(infinity.is_infinite());
    assert!(infinity.is_sign_positive());

    let neg_infinity: f64 = f32::NEG_INFINITY.into();
    assert_eq!(neg_infinity as f32, f32::NEG_INFINITY);
    assert!(neg_infinity.is_infinite());
    assert!(neg_infinity.is_sign_negative());

    let nan: f64 = f32::NAN.into();
    assert!(nan.is_nan());*/

    /*use std::convert::TryFrom;

    /*let max = <i128>::MAX;
    let min = <i128>::MIN;*/
    let zero: i128 = 0;
    /*let t_max = <u64>::MAX;
    let t_min = <u64>::MIN;
    assert!(<u64 as TryFrom<i128>>::try_from(max).is_err());
    assert!(<u64 as TryFrom<i128>>::try_from(min).is_err());*/
    println!("{:?}", i128_to_u64(zero));
    assert_eq!(<u64 as TryFrom<i128>>::try_from(zero).unwrap(), zero as u64);
    /*assert_eq!(
        <u64 as TryFrom<i128>>::try_from(t_max as i128).unwrap(),
        t_max as u64
    );
    assert_eq!(
        <u64 as TryFrom<i128>>::try_from(t_min as i128).unwrap(),
        t_min as u64
    );*/
    */

        /*
    //let mut num = u128::MAX >> 20;
    //let mut num = u128::MAX;
    #[inline(never)]
    fn two() -> u128 {
        2
    }

    //let mut num = 340282366920938463463374607431768211455_u128 >> two();
    let mut num = 340282366920938463463374607431768211455_u128 >> 2;
    //let mut num = 340282366920938463463374607431768211455_u128;
    //let mut num = 10_u128 >> 2;
    const MASK: u128 = 0x80000000000000000000000000000000;
    for _ in 0..128 {
        if num & MASK == MASK {
            print!("1");
        }
        else {
            print!("0");
        }
        num <<= 1;
    }
    println!();
*/

    assert_eq!(NonZeroU8::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroI8::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroU16::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroI16::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroU32::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroI32::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroU64::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroI64::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroU128::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroI128::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroUsize::new(1).unwrap().trailing_zeros(), 0);
    assert_eq!(NonZeroIsize::new(1).unwrap().trailing_zeros(), 0);

    assert_eq!(NonZeroU8::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroI8::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroU16::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroI16::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroU32::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroI32::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroU64::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroI64::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroU128::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroI128::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroUsize::new(1 << 2).unwrap().trailing_zeros(), 2);
    assert_eq!(NonZeroIsize::new(1 << 2).unwrap().trailing_zeros(), 2);

    assert_eq!(NonZeroU8::new(1 << 7).unwrap().trailing_zeros(), 7);
    assert_eq!(NonZeroI8::new(1 << 7).unwrap().trailing_zeros(), 7);
    assert_eq!(NonZeroU16::new(1 << 15).unwrap().trailing_zeros(), 15);
    assert_eq!(NonZeroI16::new(1 << 15).unwrap().trailing_zeros(), 15);
    assert_eq!(NonZeroU32::new(1 << 31).unwrap().trailing_zeros(), 31);
    assert_eq!(NonZeroI32::new(1 << 31).unwrap().trailing_zeros(), 31);
    assert_eq!(NonZeroU64::new(1 << 63).unwrap().trailing_zeros(), 63);
    assert_eq!(NonZeroI64::new(1 << 63).unwrap().trailing_zeros(), 63);
    assert_eq!(NonZeroU128::new(1 << 127).unwrap().trailing_zeros(), 127);
    assert_eq!(NonZeroI128::new(1 << 127).unwrap().trailing_zeros(), 127);

    assert_eq!(
        NonZeroUsize::new(1 << (usize::BITS - 1)).unwrap().trailing_zeros(),
        usize::BITS - 1
    );
    assert_eq!(
        NonZeroIsize::new(1 << (usize::BITS - 1)).unwrap().trailing_zeros(),
        usize::BITS - 1
    );

    const TRAILING_ZEROS: u32 = NonZeroU16::new(1 << 2).unwrap().trailing_zeros();
    assert_eq!(TRAILING_ZEROS, 2);

    const A: u128 = 0b0101100;
    const B: u128 = 0b0100001;
    const C: u128 = 0b1111001;

    const _0: u128 = 0;
    const _1: u128 = !0;

    assert_eq!(u128::from_be(A.to_be()), A);
    assert_eq!(u128::from_be(B.to_be()), B);
    assert_eq!(u128::from_be(C.to_be()), C);
    assert_eq!(u128::from_be(_0), _0);
    assert_eq!(u128::from_be(_1), _1);
    assert_eq!(_0.to_be(), _0);
    assert_eq!(_1.to_be(), _1);
}
