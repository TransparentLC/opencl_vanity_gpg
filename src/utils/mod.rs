mod args;
mod device;
mod hash_pattern;
mod vanity_secret_key;

use std::mem;

pub use args::*;
pub use device::DeviceList;
pub use hash_pattern::HashPattern;
pub use vanity_secret_key::VanitySecretKey;

/// Do SHA-1 padding manually
/// A SHA-1 block is 512 bit, so the output Vec<u32> length is a multiple of 16
pub fn manually_prepare_sha1(hashdata: Vec<u8>) -> Vec<u32> {
    // Length after padding
    // Fill with 0x80 0x00 ... to 448 mod 512 bit, which is 56 mod 64 bytes
    // plus u64's 8 bytes, the length is a multiple of 64
    let padded_length = hashdata.len() + (64 - ((hashdata.len() + 8) % 64)) + 8;
    let mut result_u8 = Vec::with_capacity(padded_length);
    result_u8.extend_from_slice(&hashdata);
    result_u8.push(0x80);
    result_u8.resize(padded_length, 0);

    // convert Vec<u8> to Vec<u32>
    // https://stackoverflow.com/questions/49690459/converting-a-vecu32-to-vecu8-in-place-and-with-minimal-overhead
    let mut result_u32 = unsafe {
        let ptr = result_u8.as_mut_ptr() as *mut u32;
        let length = result_u8.len() / 4;
        let capacity = result_u8.capacity() / 4;
        mem::forget(result_u8);
        Vec::from_raw_parts(ptr, length, capacity)
    };

    // assert_eq!(result_u32.len() % 16, 0);
    // SHA-1 uses big-endian words and length
    for pos in &mut result_u32 {
        *pos = pos.to_be();
    }

    let bit_length = hashdata.len() * 8;
    result_u32[padded_length / 4 - 1] = (bit_length) as u32;
    result_u32[padded_length / 4 - 2] = (bit_length >> 32) as u32;
    result_u32
}

pub fn format_number(v: impl Into<f64>) -> String {
    match Into::<f64>::into(v) {
        v if v >= 1e12f64 => {
            format!("{:.02}t", v / 1e12f64)
        }
        v if v >= 1e9f64 => {
            format!("{:.02}b", v / 1e9f64)
        }
        v if v >= 1e6f64 => {
            format!("{:.02}m", v / 1e6f64)
        }
        v if v >= 1e3f64 => {
            format!("{:.02}k", v / 1e3f64)
        }
        v => {
            format!("{v:.02}")
        }
    }
}
