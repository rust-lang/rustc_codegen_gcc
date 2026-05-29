// Compiler:

#![crate_type = "lib"]
#![feature(f16)]

#[unsafe(no_mangle)]
pub extern "C" fn f16_identity(a: f16) -> f16 {
    a
}

#[unsafe(no_mangle)]
pub fn f16_to_f32(a: f16) -> f32 {
    a as f32
}

#[unsafe(no_mangle)]
pub fn f16_to_f64(a: f16) -> f64 {
    a as f64
}

#[unsafe(no_mangle)]
pub fn f16_to_i32(a: f16) -> i32 {
    a as i32
}

#[unsafe(no_mangle)]
pub fn f16_to_u32(a: f16) -> u32 {
    a as u32
}

#[unsafe(no_mangle)]
pub fn i32_to_f16(a: i32) -> f16 {
    a as f16
}

#[unsafe(no_mangle)]
pub fn u32_to_f16(a: u32) -> f16 {
    a as f16
}

#[unsafe(no_mangle)]
pub fn f32_to_f16(a: f32) -> f16 {
    a as f16
}

#[unsafe(no_mangle)]
pub fn f64_to_f16(a: f64) -> f16 {
    a as f16
}
