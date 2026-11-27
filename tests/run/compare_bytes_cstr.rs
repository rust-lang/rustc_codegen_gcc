// Compiler:
//
// Run-time:
//   status: 0

// At opt-level 2/3, CStr's length can reach compare_bytes with a signed GCC
// integer type. The memcmp builtin still requires its C size_t parameter type.
#[inline(never)]
unsafe fn compare(p: *const std::ffi::c_char) -> bool {
    std::ffi::CStr::from_ptr(p).to_bytes() == b"x".as_slice()
}

fn main() {
    for (bytes, expected) in [
        (b"x\0".as_slice(), true),
        (b"y\0".as_slice(), false),
        (b"\0".as_slice(), false),
        (b"xx\0".as_slice(), false),
        (b"\xff\0".as_slice(), false),
    ] {
        let bytes = std::hint::black_box(bytes);
        assert_eq!(unsafe { compare(bytes.as_ptr().cast()) }, expected);
    }
}
