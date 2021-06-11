#![feature(is_sorted)]

fn main() {
    let b: u16 = 42;
    assert_eq!(b, 42);
    let empty: [i32; 0] = [];

    assert!([1, 2, 2, 9].is_sorted());
    assert!(![1, 3, 2].is_sorted());
    assert!([42].is_sorted());
    assert!(empty.is_sorted());
    assert!(![0.0, 1.0, f32::NAN].is_sorted());
    assert!([-2, -1, 0, 3].is_sorted());
    assert!(![-2i32, -1, 0, 3].is_sorted_by_key(|n| n.abs()));
    assert!(!["c", "bb", "aaa"].is_sorted());
    assert!(["c", "bb", "aaa"].is_sorted_by_key(|s| s.len()));
}
