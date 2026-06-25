//! Instruction-level transfer functions — the "transfer" half of Alexei's
//! "transfer + join" verifier (the join half is in state.rs / cnum union).
//!
//! A transfer models how one ALU instruction maps the abstract scalar state:
//! f#(insn): Scalar → Scalar. Soundness is the abstract-interpretation
//! contract — for concrete inputs in the operand states, the concrete result
//! lies in the output state:
//!   ∀ x∈γ(a), y∈γ(b):  f(x,y) ∈ γ(f#(a,b)).
//!
//! Each transfer applies the per-domain operation component-wise (tnum, cnum64,
//! cnum32). No post-transfer reduction here; that's reg_bounds_sync (reduction.rs),
//! which only tightens — soundness holds without it.

use crate::reduction::Scalar;

/// BPF_ADD on a 64-bit scalar (and its low 32-bit view).
pub fn scalar_add(a: Scalar, b: Scalar) -> Scalar {
    Scalar {
        var_off: a.var_off.add(b.var_off),
        r64: a.r64.add(b.r64),
        r32: a.r32.add(b.r32),
    }
}

/// BPF_SUB. cnum has no direct subtract; x - y = x + (-y) via negate.
pub fn scalar_sub(a: Scalar, b: Scalar) -> Scalar {
    Scalar {
        var_off: a.var_off.sub(b.var_off),
        r64: a.r64.add(b.r64.negate()),
        r32: a.r32.add(b.r32.negate()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnum::{Cnum32, Cnum64};
    use crate::state::scalar_contains;

    fn sc(lo: u64, hi: u64) -> Scalar {
        Scalar {
            var_off: crate::tnum::UNKNOWN,
            r64: Cnum64::from_urange(lo, hi),
            r32: Cnum32::from_urange(lo as u32, hi as u32),
        }
    }

    #[test]
    fn add_covers_concrete() {
        let a = sc(0, 10);
        let b = sc(100, 200);
        let r = scalar_add(a, b);
        // every x∈[0,10], y∈[100,200]: x+y ∈ r
        for x in [0u64, 5, 10] {
            for y in [100u64, 150, 200] {
                assert!(scalar_contains(&r, x.wrapping_add(y)), "{}+{}", x, y);
            }
        }
    }

    #[test]
    fn sub_covers_concrete() {
        let a = sc(100, 200);
        let b = sc(0, 10);
        let r = scalar_sub(a, b);
        for x in [100u64, 150, 200] {
            for y in [0u64, 5, 10] {
                assert!(scalar_contains(&r, x.wrapping_sub(y)), "{}-{}", x, y);
            }
        }
    }
}
