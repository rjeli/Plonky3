//! Various simple utilities.

#![no_std]

use core::hint::unreachable_unchecked;

/// Computes `ceil(a / b)`. Assumes `a + b` does not overflow.
#[must_use]
pub const fn ceil_div_usize(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

/// Computes `ceil(log_2(n))`.
#[must_use]
pub fn log2_ceil_usize(n: usize) -> usize {
    (usize::BITS - n.saturating_sub(1).leading_zeros()) as usize
}

#[must_use]
pub fn log2_ceil_u64(n: u64) -> u64 {
    (u64::BITS - n.saturating_sub(1).leading_zeros()).into()
}

/// Computes `log_2(n)`
///
/// # Panics
/// Panics if `n` is not a power of two.
#[must_use]
#[inline]
pub fn log2_strict_usize(n: usize) -> usize {
    let res = n.trailing_zeros();
    assert_eq!(n.wrapping_shr(res), 1, "Not a power of two: {n}");
    res as usize
}

// Rotate left 1 bit, wrapping at `n` bits.
// This maps an index into an array to an index into its transpose.
pub fn transpose_index_bits(x: usize, n: usize) -> usize {
    let mask = (1 << (n - 1)) - 1;
    // top_bit | (bottom_bits << 1)
    (x >> (n - 1)) | ((x & mask) << 1)
}

/// Returns `[0, ..., N - 1]`.
#[must_use]
pub const fn indices_arr<const N: usize>() -> [usize; N] {
    let mut indices_arr = [0; N];
    let mut i = 0;
    while i < N {
        indices_arr[i] = i;
        i += 1;
    }
    indices_arr
}

#[inline(always)]
pub fn assume(p: bool) {
    debug_assert!(p);
    if !p {
        unsafe {
            unreachable_unchecked();
        }
    }
}

/// Try to force Rust to emit a branch. Example:
///
/// ```no_run
/// let x = 100;
/// if x > 20 {
///     println!("x is big!");
///     p3_util::branch_hint();
/// } else {
///     println!("x is small!");
/// }
/// ```
///
/// This function has no semantics. It is a hint only.
#[inline(always)]
pub fn branch_hint() {
    // NOTE: These are the currently supported assembly architectures. See the
    // [nightly reference](https://doc.rust-lang.org/nightly/reference/inline-assembly.html) for
    // the most up-to-date list.
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
        target_arch = "x86",
        target_arch = "x86_64",
    ))]
    unsafe {
        core::arch::asm!("", options(nomem, nostack, preserves_flags));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    use alloc::vec;
    use p3_matrix::{dense::RowMajorMatrix, MatrixTranspose};

    #[test]
    fn test_transpose_index_bits() {
        assert_eq!(transpose_index_bits(0b0, 1), 0b0);
        assert_eq!(transpose_index_bits(0b1, 1), 0b1);
        assert_eq!(transpose_index_bits(0b01, 2), 0b10);
        assert_eq!(transpose_index_bits(0b10, 2), 0b01);
        assert_eq!(transpose_index_bits(0b001, 3), 0b010);
        assert_eq!(transpose_index_bits(0b011, 3), 0b110);
        assert_eq!(transpose_index_bits(0b101, 3), 0b011);
        assert_eq!(transpose_index_bits(0b0110, 4), 0b1100);
        assert_eq!(transpose_index_bits(0b1010, 4), 0b0101);

        let x = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let n = log2_strict_usize(x.len());
        let xt = RowMajorMatrix::new(x.clone(), x.len() / 2)
            .transpose()
            .values;
        assert_eq!(&xt, &[0, 4, 1, 5, 2, 6, 3, 7]);
        for i in 0..x.len() {
            assert_eq!(x[i], xt[transpose_index_bits(i, n)]);
        }
    }
}
