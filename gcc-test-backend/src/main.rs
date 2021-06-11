fn main() {
    const A: i8 = 0b0101100;
    const B: i8 = 0b0100001;
    const C: i8 = 0b1111001;

    const _0: i8 = 0;
    const _1: i8 = !0;

    assert_eq!(A.rotate_left(6).rotate_right(2).rotate_right(4), A);
    assert_eq!(B.rotate_left(3).rotate_left(2).rotate_right(5), B);
    assert_eq!(C.rotate_left(6).rotate_right(2).rotate_right(4), C);

    /*fn rotate_left(x: u32, mut n: u32) -> u32 {
        //(x << n) | (x >> (-(n as i32) & 31))
        //println!("{}", 0 << 32);
        let second_shift = 32 - (n % 32);
        n %= 32;
        (x << n) | (x >> second_shift)
    }

    fn irotate_left(x: i32, mut n: u32) -> i32 {
        let x = x as u32;
        let second_shift = 32 - (n % 32);
        n %= 32;
        ((x << n) | (x >> second_shift)) as i32
    }

    assert_eq!(rotate_left(2, 48), 131072);
    assert_eq!(irotate_left(2, 48), 131072);
    assert_eq!(irotate_left(-2, 48), -65537);
    assert_eq!(irotate_left(_1, 124), _1);*/

    /*const _2: u32 = 0;
    assert_eq!(rotate_left(_2, 16), _2);
    assert_eq!(rotate_left(_2, 32), _2);
    assert_eq!(_2.rotate_left(32), _2);*/

    // Rotating these should make no difference
    //
    // We test using 124 bits because to ensure that overlong bit shifts do
    // not cause undefined behaviour. See #10183.
    assert_eq!(_0.rotate_left(124), _0);
    println!("{:b}", _1);
    assert_eq!(_1.rotate_left(124), _1);

    // Rotating by 0 should have no effect
    assert_eq!(A.rotate_left(0), A);
    assert_eq!(B.rotate_left(0), B);
    assert_eq!(C.rotate_left(0), C);
    // Rotating by a multiple of word size should also have no effect
    assert_eq!(A.rotate_left(128), A);
    assert_eq!(B.rotate_left(128), B);
    assert_eq!(C.rotate_left(128), C);
}
