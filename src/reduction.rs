//! Reduced-product reduction over (tnum × cnum64 × cnum32).
//!
//! Port of bpf-next `reg_bounds_sync` and its helpers (verifier.c:1973-2111).
//! This is the heart of the scalar domain. `reg_bounds_sync` runs
//! `__reg_deduce_bounds` twice (verifier.c:2081-2082); 9e5fcb003aec reduced
//! that from three to two and established two as the minimum pre-cnum (with the
//! verifier_bounds "cross sign boundary" selftest failing at one round). We
//! port it faithfully and expose a pass-parameterized variant (`normalize_n`)
//! to study convergence under the current cnum-based reduction.

use crate::cnum::{cnum32_from_cnum64, cnum64_cnum32_intersect, Cnum32, Cnum64};
use crate::tnum::Tnum;

/// Scalar register abstract state = reduced product of the three domains.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Scalar {
    pub var_off: Tnum, // bit-level
    pub r64: Cnum64,   // 64-bit range
    pub r32: Cnum32,   // 32-bit range
}

const S32_MIN_SX: u64 = (i32::MIN as i64) as u64; // 0xFFFFFFFF_80000000
const S32_MAX: u64 = i32::MAX as u64; //              0x00000000_7FFFFFFF
const S64_MIN: u64 = i64::MIN as u64; //              0x80000000_00000000
const S64_MAX: u64 = i64::MAX as u64; //              0x7FFFFFFF_FFFFFFFF

/// `cnum32_from_tnum` (verifier.c:1973). Signed if the sign bit is set/unknown.
pub fn cnum32_from_tnum(t: Tnum) -> Cnum32 {
    let t = t.subreg();
    if (t.mask & S32_MIN_SX) != 0 || (t.value & S32_MIN_SX) != 0 {
        Cnum32::from_srange(
            (t.value | (t.mask & S32_MIN_SX)) as u32 as i32,
            (t.value | (t.mask & S32_MAX)) as u32 as i32,
        )
    } else {
        Cnum32::from_urange(t.value as u32, (t.value | t.mask) as u32)
    }
}

/// `cnum64_from_tnum` (verifier.c:1985).
pub fn cnum64_from_tnum(t: Tnum) -> Cnum64 {
    if (t.mask & S64_MIN) != 0 || (t.value & S64_MIN) != 0 {
        Cnum64::from_srange(
            (t.value | (t.mask & S64_MIN)) as i64,
            (t.value | (t.mask & S64_MAX)) as i64,
        )
    } else {
        Cnum64::from_urange(t.value, t.value | t.mask)
    }
}

impl Scalar {
    fn reg_umin(&self) -> u64 {
        self.r64.umin()
    }
    fn reg_umax(&self) -> u64 {
        self.r64.umax()
    }

    /// `___mark_reg_known` — collapse to a constant in all three domains.
    fn mark_known(&mut self, v: u64) {
        self.var_off = Tnum::const_(v);
        self.r64 = Cnum64::from_urange(v, v);
        self.r32 = Cnum32::from_urange(v as u32, v as u32);
    }

    /// `__update_reg32_bounds`
    fn update_reg32_bounds(&mut self) {
        self.r32.intersect_with(cnum32_from_tnum(self.var_off));
    }

    /// `__update_reg64_bounds` — includes the single-value overlap inference
    /// (verifier.c:2008-2033) -- a hand-written corner worth checking.
    fn update_reg64_bounds(&mut self) {
        self.r64.intersect_with(cnum64_from_tnum(self.var_off));

        let umin = self.reg_umin();
        let umax = self.reg_umax();
        let tnum_next = self.var_off.step(umin);
        let umin_in_tnum = (umin & !self.var_off.mask) == self.var_off.value;
        let tmax = self.var_off.value | self.var_off.mask;

        if umin_in_tnum && tnum_next > umax {
            self.mark_known(umin);
        } else if !umin_in_tnum && tnum_next == tmax {
            self.mark_known(tmax);
        } else if !umin_in_tnum
            && tnum_next <= umax
            && self.var_off.step(tnum_next) > umax
        {
            self.mark_known(tnum_next);
        }
    }

    /// `__update_reg_bounds`
    fn update_reg_bounds(&mut self) {
        self.update_reg32_bounds();
        self.update_reg64_bounds();
    }

    /// `deduce_bounds_32_from_64`
    fn deduce_bounds_32_from_64(&mut self) {
        self.r32.intersect_with(cnum32_from_cnum64(self.r64));
    }

    /// `deduce_bounds_64_from_32`
    fn deduce_bounds_64_from_32(&mut self) {
        self.r64 = cnum64_cnum32_intersect(self.r64, self.r32);
    }

    /// `__reg_deduce_bounds` — one cross-width reduction pass.
    pub fn reg_deduce_bounds(&mut self) {
        self.deduce_bounds_32_from_64();
        self.deduce_bounds_64_from_32();
    }

    /// `__reg_bound_offset` — pull range knowledge back into the tnum.
    fn reg_bound_offset(&mut self) {
        let var64_off = self
            .var_off
            .intersect(Tnum::range(self.reg_umin(), self.reg_umax()));
        let var32_off = var64_off
            .subreg()
            .intersect(Tnum::range(self.r32.umin() as u64, self.r32.umax() as u64));
        self.var_off = var64_off.clear_subreg().or(var32_off);
    }

    /// `range_bounds_violation`
    pub fn range_bounds_violation(&self) -> bool {
        self.r32.is_empty() || self.r64.is_empty()
    }

    /// `reg_bounds_sync` (verifier.c:2073) — the production reduction.
    /// NOTE the **two** `reg_deduce_bounds` calls.
    pub fn reg_bounds_sync(&mut self) {
        if self.range_bounds_violation() {
            return;
        }
        self.update_reg_bounds();
        self.reg_deduce_bounds();
        self.reg_deduce_bounds(); // second pass; see header note on round count
        self.reg_bound_offset();
        self.update_reg_bounds();
    }

    /// Phase-B instrument: same as `reg_bounds_sync` but with `deduce_passes`
    /// cross-width reductions instead of the hard-coded 2. Returns the number
    /// of passes after which the state stopped changing (the empirical fixpoint
    /// distance), or `None` if it had not converged within `deduce_passes`.
    pub fn normalize_n(&mut self, deduce_passes: u32) -> Option<u32> {
        if self.range_bounds_violation() {
            return Some(0);
        }
        self.update_reg_bounds();
        let mut converged_at = None;
        for i in 0..deduce_passes {
            let before = *self;
            self.reg_deduce_bounds();
            if *self == before && converged_at.is_none() {
                converged_at = Some(i);
                break;
            }
        }
        self.reg_bound_offset();
        self.update_reg_bounds();
        converged_at
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unbounded() -> Scalar {
        Scalar {
            var_off: crate::tnum::UNKNOWN,
            r64: Cnum64::UNBOUNDED,
            r32: Cnum32::UNBOUNDED,
        }
    }

    #[test]
    fn sync_is_idempotent_on_const() {
        let mut s = unbounded();
        s.mark_known(42);
        let a = s;
        s.reg_bounds_sync();
        assert_eq!(s, a, "sync must not perturb a constant");
    }

    #[test]
    fn sync_tightens_from_tnum() {
        // var_off says low bits, range unbounded → sync should narrow ranges.
        let mut s = unbounded();
        s.var_off = Tnum::const_(0x100); // exactly 256
        s.reg_bounds_sync();
        assert_eq!(s.r64.umin(), 0x100);
        assert_eq!(s.r64.umax(), 0x100);
    }

    #[test]
    fn second_deduce_pass_can_still_change_state() {
        // Phase-B probe: does a single deduce pass ever fail to reach fixpoint?
        // Sweep a batch of constructed states and record convergence distance.
        let mut max_dist = 0u32;
        for hi in 0..64u64 {
            let mut s = unbounded();
            s.var_off = Tnum::range(hi << 8, (hi << 8) | 0xff);
            s.update_reg_bounds_pub();
            if let Some(d) = measure_fixpoint(&mut s, 8) {
                max_dist = max_dist.max(d);
            }
        }
        // We only assert the harness runs; the interesting number is printed.
        println!("max observed deduce fixpoint distance (sample) = {max_dist}");
    }

    // test-only helpers
    impl Scalar {
        fn update_reg_bounds_pub(&mut self) {
            self.update_reg_bounds();
        }
    }
    fn measure_fixpoint(s: &mut Scalar, cap: u32) -> Option<u32> {
        for i in 0..cap {
            let before = *s;
            s.reg_deduce_bounds();
            if *s == before {
                return Some(i);
            }
        }
        None
    }
}
