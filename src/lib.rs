//! bpf_verifier_rs — Rust model of the BPF verifier scalar abstract domain.
//!
//! Models bpf-next's `tnum` × `cnum64` × `cnum32` reduced product domain
//! (@ a975094bf, 7.2-rc1 merge window) for soundness verification.
//! See `docs/MAPPING.md` for the C→Rust mapping.

pub mod cnum;
#[cfg(kani)]
pub mod proofs;
pub mod reduction;
pub mod tnum;
