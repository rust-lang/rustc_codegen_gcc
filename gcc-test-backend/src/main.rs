#![allow(deprecated)]

/*use deflate::deflate_bytes_conf;
use deflate::CompressionOptions;*/
//use deflate::DeflateState;

/*type T = String;
const N: usize = 2;

// fast
#[inline(always)]
pub fn example_a() -> [T; N] {
    Default::default()
}

// fast
pub fn example_b() -> [T; N] {
    unsafe {
        // ignore the UB for now
        let mut array: [T; N] = mem::uninitialized();
        for slot in &mut array {
            ptr::write(slot, T::default());
        }
        array
    }
}

// slow
pub fn example_c() -> [T; N] {
    let mut array: MaybeUninit<[T; N]> = MaybeUninit::uninit();
    unsafe {
        // ignore the UB for now
        // ordinarily would cast to &mut [MaybeUninit<T>; N]
        // but here we try to minimize difference from `b`
        let slots = &mut *array.as_mut_ptr();
        for slot in slots {
            ptr::write(slot, T::default());
        }
        array.assume_init()
    }
}*/

pub struct Node {
    value: u32,
    symbol: u16,
}

fn main() {
    //let mut result = vec![];
    //let state = DeflateState::new(CompressionOptions::high(), &mut result);
    //compress_data_dynamic_n(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], state, Flush::Finish);
    // TODO: determine exactly what are the parameters sent to vec.extend() to reproduce the issue.

    /*leaves.extend(vec![
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
        Node {
            value: 12,
            symbol: 42,
        },
    ]);

    println!("{}", leaves.capacity());*/


    let mut leaves: Vec<Node> = Vec::with_capacity(286);
    let frequencies/*: &[i32]*/ = &[526, 124, 128, 125, 107, 92, 84, 75, 88, 53, 63, 43, 54, 68, 56, 60, 38, 53, 37, 23, 36, 32, 21, 25, 20, 21, 27, 26, 16, 15, 20, 24, 22, 14, 12, 19, 19, 10, 15, 11, 13, 4, 15, 7, 6, 10, 10, 2, 1, 3, 3, 2, 2, 3, 2, 1, 1, 0, 0, 0, 2, 1, 0, 0, 0, 1, 3, 0, 1, 2, 3, 0, 2, 1, 4, 0, 1, 1, 1, 2, 2, 2, 3, 1, 1, 0, 0, 3, 0, 1, 0, 2, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 2, 1, 0, 2, 0, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 2, 0, 0, 1, 1, 0, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2, 1, 1, 2, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 2, 1, 2, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 4, 6, 3, 4, 8, 7, 2, 7, 6, 8, 5, 8, 8, 17, 11, 16, 10, 8, 7, 13, 9, 14, 18, 12, 10, 19, 12, 11, 17, 15, 13, 17, 14, 17, 23, 31, 44, 27, 25, 30, 18, 17, 20, 25, 72, 52, 55, 69, 87, 75, 1, 7754, 5054, 3016, 2120, 1790, 1263, 606, 602, 958, 783, 481, 333, 510, 392, 211, 177, 169, 89, 58, 70, 110, 56, 37, 52, 63, 38, 48, 13, 1373];
    let len = 10;
    unsafe {
        println!("&{:?}[10] = {:?}", frequencies.as_ptr(), frequencies.as_ptr().add(len));
    }
    /*leaves.extend(frequencies.iter().enumerate().filter_map(
            |(n, f)| if *f > 0 {
                Some(Node {
                    value: *f as u32,
                    symbol: n as u16,
                })
            } else {
                None
            },
    ));*/

    //println!("{}", vec[0]);

    //example_a();
    //example_b();
    //example_c();
}

//#![feature(maybe_uninit_slice)]

//use std::sync::atomic::{AtomicUsize, Ordering};

/*extern "C" {
    pub fn printf(format: *const i8, ...) -> i32;
}*/

/*static DEC_DIGITS_LUT: &[u8; 200] = b"0001020304050607080910111213141516171819\
      2021222324252627282930313233343536373839\
      4041424344454647484950515253545556575859\
      6061626364656667686970717273747576777879\
      8081828384858687888990919293949596979899";*/

/*use std::mem::MaybeUninit;
use std::ptr;*/

/*static CACHED_POW10: [(u64, i16, i16); 2] = [
    // (f, e, k)
    (0xe61acf033d1a45df, -1087, -308),
    (0xab70fe17c79ac6ca, -1060, -300),
];

//static array: [[u8; 4]; 1] = [[1, 2, 3, 4]];

static TUPLE: (u64, u64, u64) = (0xe61acf033d1a45df, 0xe61acf033d1a45df, 0xe61acf033d1a45df);*/

/*fn main() {
    assert_eq!(-128i8, (-128i8).saturating_sub(1));

    //println!("{}, {}, {}", TUPLE.0, TUPLE.1, TUPLE.2);

    //let tuple: (u64, u64, u64) = (0xe61acf033d1a45df, 0xe61acf033d1a45df, 0xe61acf033d1a45df);
    //println!("{}, {}, {}", tuple.0, tuple.1, tuple.2);

    /*println!("{}, {}, {}, {}", array[0][0], array[0][1], array[0][2], array[0][3]);*/

    /*println!("{}, {}, {}", CACHED_POW10[0].0, CACHED_POW10[0].1, CACHED_POW10[0].2);
    println!("{}, {}, {}", CACHED_POW10[1].0, CACHED_POW10[1].1, CACHED_POW10[1].2);*/
    //let arr = [10; 40];
    //let mut buf = [MaybeUninit::<u8>::uninit(); 40];
    //let buf_ptr = MaybeUninit::first_ptr_mut(&mut buf);

    /*let dec_digits_lut: [u8; 4] = [0, 1, 2, 3];
    let mut buf = [0, 1, 2, 3];
    let buf_ptr = buf.as_mut_ptr();
    //let lut_ptr = DEC_DIGITS_LUT.as_ptr();
    let lut_ptr = dec_digits_lut.as_ptr();

    //ptr::copy_nonoverlapping(lut_ptr.offset(d1), buf_ptr.offset(curr), 2);
    unsafe {
        // FIXME: it seems it doesn't take the size (0) into account.
        // Check if memcpy has alignment requirements.
        ptr::copy_nonoverlapping(lut_ptr, buf_ptr, 0)
    };*/

    //println!("{}", 42i8);

    /*let num = AtomicUsize::new(41);
    num.fetch_add(1, Ordering::SeqCst);
    //println!("{:?}", num.load(Ordering::SeqCst));
    unsafe {
        printf("%d\n\0" as *const str as *const i8, num.load(Ordering::SeqCst));
    }

    //println!("Hello, world!");
    unsafe {
        if 4u32.is_power_of_two() {
            printf("Is power of two\n\0" as *const str as *const i8);
        }
        else {
            printf("Is NOT power of two\n\0" as *const str as *const i8);
        }
    }

    unsafe {
        printf("Hello\n\0" as *const str as *const i8);

        let mut vec = vec![14];
        printf("%d\n\0" as *const str as *const i8, vec[0]);
        vec.push(10);
        printf("%d\n\0" as *const str as *const i8, vec[0]);
    }*/

    //vec.push(12);
    //println!("Hello, world!");
}*/

/*
// Adapted from rustc run-pass test suite

#![feature(no_core, arbitrary_self_types, box_syntax, linkage, unboxed_closures, core_intrinsics)]
#![feature(rustc_attrs)]

#![feature(start, lang_items)]
#![no_std]
//#![no_core]

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    unsafe {
        core::intrinsics::abort();
    }
}

/*extern crate depth1;*/
//extern crate mini_core;

//use mini_core::*;

/*macro_rules! assert_eq {
    ($l:expr, $r: expr) => {
        if $l != $r {
            panic(stringify!($l != $r));
        }
    }
}

struct Ptr<T: ?Sized>(Box<T>);

impl<T: ?Sized> Deref for Ptr<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T: Unsize<U> + ?Sized, U: ?Sized> CoerceUnsized<Ptr<U>> for Ptr<T> {}
impl<T: Unsize<U> + ?Sized, U: ?Sized> DispatchFromDyn<Ptr<U>> for Ptr<T> {}

struct Wrapper<T: ?Sized>(T);

impl<T: ?Sized> Deref for Wrapper<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: CoerceUnsized<U>, U> CoerceUnsized<Wrapper<U>> for Wrapper<T> {}
impl<T: DispatchFromDyn<U>, U> DispatchFromDyn<Wrapper<U>> for Wrapper<T> {}


trait Trait {
    // This method isn't object-safe yet. Unsized by-value `self` is object-safe (but not callable
    // without unsized_locals), but wrappers arond `Self` currently are not.
    // FIXME (mikeyhew) uncomment this when unsized rvalues object-safety is implemented
    // fn wrapper(self: Wrapper<Self>) -> i32;
    fn ptr_wrapper(self: Ptr<Wrapper<Self>>) -> i32;
    /*fn wrapper_ptr(self: Wrapper<Ptr<Self>>) -> i32;
    fn wrapper_ptr_wrapper(self: Wrapper<Ptr<Wrapper<Self>>>) -> i32;*/
}

impl Trait for i32 {
    fn ptr_wrapper(self: Ptr<Wrapper<Self>>) -> i32 {
        **self
    }
    /*fn wrapper_ptr(self: Wrapper<Ptr<Self>>) -> i32 {
        **self
    }
    fn wrapper_ptr_wrapper(self: Wrapper<Ptr<Wrapper<Self>>>) -> i32 {
        ***self
    }*/
}*/

/*fn max_value2(var: isize) -> i16 {
    var as i64 as i16
}*/

/*#[lang = "shr"]
pub trait Shr<Rhs = Self> {
    /// The resulting type after applying the `>>` operator.
    type Output;

    /// Performs the `>>` operation.
    fn shr(self, rhs: Rhs) -> Self::Output;
}

impl Shr<i32> for i32 {
    type Output = i32;

    fn shr(self, other: i32) -> i32 {
        self >> other
    }
}

fn max_value_dont_work(var: i32, var2: i32) -> u8 {
    var as u32 as u8
    //(var >> var2) as u8
    //var as u8
}

fn max_value(var: isize) -> u8 {
    var as usize as isize as i8 as u8
    /*let num = var as i32;
    let char = num as u8;
    char*/
}

struct Struct {
    field: isize,
}

static mut STRUCT: Struct = Struct {
    field: 0,
};

pub struct Struct2 {
    pub field1: &'static [u8],
    pub field2: i32,
}

unsafe impl Sync for Struct2 {}

pub static STRUCT2: Struct2 = Struct2 {
    field1: b"test",
    field2: 12,
};

//mod level1;

#[repr(C)]
enum c_void {
    _1,
    _2,
}*/

pub unsafe fn register_dtor(t: *mut u8, dtor: unsafe extern "C" fn(*mut u8)) {
    #[link(name="c")]
    extern "C" {
        #[linkage = "extern_weak"]
        static __dso_handle: *mut u8;
        // TODO: to fix this code, get the address of the global and cast it to the function type.
        // How can I know, though, if this is to be casted to a function type?
        #[linkage = "extern_weak"]
        static __cxa_thread_atexit_impl: *const core::ffi::c_void;
    }
    if !__cxa_thread_atexit_impl.is_null() {
        type F = unsafe extern "C" fn(
            dtor: unsafe extern "C" fn(*mut u8),
            arg: *mut u8,
            dso_handle: *mut u8,
        ) -> i32;
        core::mem::transmute::<*const core::ffi::c_void, F>(__cxa_thread_atexit_impl)(
            dtor,
            t,
            &__dso_handle as *const _ as *mut _,
        );
        return;
    }
}

/*#[lang = "generator_state"]
pub enum GeneratorState<Y, R> {
    Yielded(Y),
    Complete(R),
}

#[lang = "generator"]
pub trait Generator<R = ()> {
    type Yield;
    type Return;
    fn resume(self: Self, arg: R) -> GeneratorState<Self::Yield, Self::Return>;
}

#[lang = "fn"]
#[rustc_paren_sugar]
pub trait Fn<Args>: FnMut<Args> {
    /// Performs the call operation.
    extern "rust-call" fn call(&self, args: Args) -> Self::Output;
}*/

fn callback<F: Fn()>(func: F) {
    func();
}

/*fn print_stuff() {
    unsafe {
        mini_core::libc::puts("Hello\n\0" as *const str as *const u8);
    }
}*/

fn call_callback<F: Fn()>(func: F) {
    callback(func);
}

struct MyStruct {
}

impl MyStruct {
    /*fn call(&self) -> i32 {
        unsafe {
            mini_core::libc::puts("My struct\n\0" as *const str as *const u8);
        }
        0
    }*/
}

/*pub struct LocalKey {
    inner: unsafe fn() -> MyStruct,
}

impl LocalKey {
    fn call(&self) -> i32 {
        unsafe {
            let result = (self.inner)().call();
            result
        }
    }
}*/

use core::sync::atomic::{Ordering, AtomicUsize};

#[link(name = "c")]
extern "C" {
    pub fn printf(format: *const i8, ...) -> i32;
}

pub(crate) struct Slice {
    pub inner: [u8],
}

impl Slice {
    #[inline]
    fn from_u8_slice(s: &[u8]) -> &Slice {
        unsafe { core::mem::transmute(s) }
    }

    #[inline]
    fn as_bytes(&self) -> &[u8] {
        &self.inner
    }
}

pub struct OsStr {
    inner: Slice,
}

impl OsStr {
    #[inline]
    fn from_inner(inner: &Slice) -> &OsStr {
        unsafe { &*(inner as *const Slice as *const OsStr) }
    }

    #[inline]
    fn as_inner(&self) -> &Slice {
        &self.inner
    }

    #[inline]
    fn as_bytes(&self) -> &[u8] {
        &self.inner.inner
        //self.as_inner().as_bytes()
        //&self.as_inner().inner
    }
}

#[start]
fn main(argc: isize, _: *const *const u8) -> isize {
    let os_str = OsStr::from_inner(Slice::from_u8_slice(b"test\n\0"));
    let bytes = os_str.as_bytes();
    unsafe {
        printf(bytes.as_ptr() as *const i8);
    }

    /*let num = AtomicUsize::new(0);
    num.compare_and_swap(0, 10, Ordering::SeqCst);
    unsafe {
        printf("Hello %d\n\0" as *const str as *const i8, num.load(Ordering::SeqCst));
    }*/

    //callback(print_stuff);
    //call_callback(print_stuff);
    /*callback(|| {
        unsafe {
            mini_core::libc::puts("Hello\n\0" as *const str as *const u8);
        }
    });*/
    /*call_callback(|| {
        unsafe {
            mini_core::libc::puts("Hello2\n\0" as *const str as *const u8);
        }
    });*/

    /*let local = LocalKey {
        inner: || {
            print_stuff();
            MyStruct {}
        },
    };
    local.call();*/

    unsafe extern "C" fn dtor(var: *mut u8) {
    }

    let mut var = 0u8;
    unsafe {
        register_dtor(&mut var, dtor);
    }

    //let num = argc as i32;
    //let char = num as u8;
    //let char = max_value(123);
    //let char = max_value_dont_work(123, 2);
    //char as isize

    //use mini_core::libc::{printf, puts};

    /*unsafe { puts("test\n\0" as *const str as *const u8) };

    unsafe { printf("STRUCT2: %p\n\0" as *const str as *const i8, STRUCT2.field1) };
    unsafe { puts(STRUCT2.field1 as *const [u8] as *const u8) };
    // FIXME: constructors not called for other crates.
    // Potential solution would be to add global_with_initializer to libgccjit. Sounds complicated
    // as it would need a way to create compile-time values.
    //
    // Simpler for now could be to call the globalInit function of every crate.
    //
    // An alternate would be to add constructor functions to libgccjit.
    unsafe { printf("A_STATIC: %p\n\0" as *const str as *const i8, mini_core::STRUCT.field1) };
    unsafe { printf("STRUCT3: %d\n\0" as *const str as *const i8, level1::STRUCT3.field2) };
    unsafe { printf("STRUCT3: %p\n\0" as *const str as *const i8, level1::STRUCT3.field1) };

    unsafe { puts(level1::STRUCT3.field1 as *const [u8] as *const u8) };

    unsafe { printf("STRUCT4: %p\n\0" as *const str as *const i8, depth1::STRUCT4.field1) };
    unsafe { printf("STRUCT5: %p\n\0" as *const str as *const i8, depth1::STRUCT5.field1) };

    depth1::print_ptr();*/

    /*unsafe { puts("1\n\0" as *const str as *const u8) };
    let wrapper = Wrapper(5);
    unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, wrapper.0) };
    let wrapper = box Wrapper(6);
    unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, wrapper.0) };*/
    //let wrapper = Ptr(box Wrapper(7));
    /*unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, (wrapper.0).0) };
    unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, (*wrapper).0) };*/
    //unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, **wrapper) };
    //assert_eq!(wrapper.ptr_wrapper(), 7);
    //unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, wrapper.ptr_wrapper()) };

    //let pw = Ptr(box Wrapper(5)) as Ptr<Wrapper<dyn Trait>>;
    //unsafe { printf("wrapper: %d\n\0" as *const str as *const i8, pw.ptr_wrapper()) };
    //assert_eq!(pw.ptr_wrapper(), 5);

    //unsafe { puts("2\n\0" as *const str as *const u8) };

    /*let wp = Wrapper(Ptr(box 6)) as Wrapper<Ptr<dyn Trait>>;
    assert_eq!(wp.wrapper_ptr(), 6);

    unsafe { puts("3\n\0" as *const str as *const u8) };

    let wpw = Wrapper(Ptr(box Wrapper(7))) as Wrapper<Ptr<Wrapper<dyn Trait>>>;
    assert_eq!(wpw.wrapper_ptr_wrapper(), 7);

    unsafe { puts("4\n\0" as *const str as *const u8) };*/

    /*unsafe {
        STRUCT.field = argc;
        STRUCT.field
    }*/

    0
}
*/
