//! State equivalence — the ordering that justifies state pruning.
//!
//! Models the SCALAR_VALUE case of `regsafe` (states.c:506) and the membership
//! it relies on. `regsafe(old, cur)` answers "is it safe to prune cur because
//! old already covers it?" — which is sound exactly when γ(cur) ⊆ γ(old), i.e.
//! every concrete value the current register can hold was already explored.
//!
//! This is the ordering half of Alexei's "transfer + join" picture: the join
//! (merge_verifier_state, not yet in-tree) only makes sense over a domain whose
//! ⊑ is a sound partial order. Here we pin that down for the scalar domain.

use crate::cnum::{Cnum32, Cnum64};
use crate::reduction::Scalar;

/// γ membership: `v` is in the concretization of the scalar state iff it lies
/// in both range projections and agrees with the tnum's known bits.
pub fn scalar_contains(s: &Scalar, v: u64) -> bool {
    s.r64.contains(v)
        && s.r32.contains(v as u32)
        && (v & !s.var_off.mask) == s.var_off.value
}

/// SCALAR_VALUE case of `regsafe` (states.c:608), modulo precise/id bookkeeping:
///   `range_within(old, cur) && tnum_in(old.var_off, cur.var_off)`
/// range_within = cur's ranges are subsets of old's; tnum_in = cur's tnum is
/// contained in old's. Together: cur ⊑ old.
pub fn regsafe_scalar(old: &Scalar, cur: &Scalar) -> bool {
    Cnum64::is_subset(old.r64, cur.r64)       // cur.r64 ⊆ old.r64
        && Cnum32::is_subset(old.r32, cur.r32) // cur.r32 ⊆ old.r32
        && old.var_off.contains(cur.var_off)   // cur.var_off ⊆ old.var_off
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tnum::Tnum;

    fn scalar_const(v: u64) -> Scalar {
        Scalar {
            var_off: Tnum::const_(v),
            r64: Cnum64::from_urange(v, v),
            r32: Cnum32::from_urange(v as u32, v as u32),
        }
    }

    #[test]
    fn regsafe_reflexive() {
        let s = scalar_const(42);
        assert!(regsafe_scalar(&s, &s));
    }

    #[test]
    fn regsafe_wider_old_covers_narrow_cur() {
        // old = [0,100], cur = {50}. old should be safe-to-prune cur.
        let old = Scalar {
            var_off: crate::tnum::UNKNOWN,
            r64: Cnum64::from_urange(0, 100),
            r32: Cnum32::from_urange(0, 100),
        };
        let cur = scalar_const(50);
        assert!(regsafe_scalar(&old, &cur));
        // and the soundness direction holds concretely: 50 ∈ γ(cur) ⇒ 50 ∈ γ(old)
        assert!(scalar_contains(&cur, 50) && scalar_contains(&old, 50));
    }

    #[test]
    fn regsafe_rejects_when_cur_escapes_old() {
        let old = scalar_const(50);
        let cur = Scalar {
            var_off: crate::tnum::UNKNOWN,
            r64: Cnum64::from_urange(0, 100),
            r32: Cnum32::from_urange(0, 100),
        };
        // cur is wider than old → not safe to prune.
        assert!(!regsafe_scalar(&old, &cur));
    }
}
