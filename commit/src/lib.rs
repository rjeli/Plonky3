//! A framework for various (not necessarily hiding) cryptographic commitment schemes.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod adapters;
mod mmcs;
mod pcs;

pub use adapters::*;
pub use mmcs::*;
pub use pcs::*;
