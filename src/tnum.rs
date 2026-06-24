//! tnum: tracked (tristate) numbers — bit-level abstract domain.
//!
//! 1:1 port of bpf-next `kernel/bpf/tnum.c` @ a975094bf (7.2-rc1).
//! Each bit is known (0/1) or unknown (x). `value` holds known bits,
//! `mask` marks unknown bits. Invariant: `value & mask == 0`.
//!
//! C unsigned arithmetic wraps by definition; Rust would panic in debug,
//! so every add/sub/shift that can overflow uses `wrapping_*`.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Tnum {
    pub value: u64,
    pub mask: u64,
}

#[inline]
const fn tnum(value: u64, mask: u64) -> Tnum {
    Tnum { value, mask }
}

/// A completely unknown value: `{0, -1}`.
pub const UNKNOWN: Tnum = Tnum { value: 0, mask: u64::MAX };

impl Tnum {
    pub const fn const_(value: u64) -> Tnum {
        tnum(value, 0)
    }

    /// `tnum_range(min, max)` — smallest tnum covering [min, max].
    pub fn range(min: u64, max: u64) -> Tnum {
        let chi = min ^ max;
        let bits = 64 - chi.leading_zeros(); // fls64(chi)
        // special case: 1ULL << 64 is undefined
        if bits > 63 {
            return UNKNOWN;
        }
        let delta = (1u64 << bits) - 1;
        tnum(min & !delta, delta)
    }

    pub fn lshift(self, shift: u8) -> Tnum {
        tnum(self.value << shift, self.mask << shift)
    }

    pub fn rshift(self, shift: u8) -> Tnum {
        tnum(self.value >> shift, self.mask >> shift)
    }

    pub fn arshift(self, min_shift: u8, insn_bitness: u8) -> Tnum {
        if insn_bitness == 32 {
            tnum(
                ((self.value as i32) >> min_shift) as u32 as u64,
                ((self.mask as i32) >> min_shift) as u32 as u64,
            )
        } else {
            tnum(
                ((self.value as i64) >> min_shift) as u64,
                ((self.mask as i64) >> min_shift) as u64,
            )
        }
    }

    pub fn add(self, b: Tnum) -> Tnum {
        let sm = self.mask.wrapping_add(b.mask);
        let sv = self.value.wrapping_add(b.value);
        let sigma = sm.wrapping_add(sv);
        let chi = sigma ^ sv;
        let mu = chi | self.mask | b.mask;
        tnum(sv & !mu, mu)
    }

    pub fn sub(self, b: Tnum) -> Tnum {
        let dv = self.value.wrapping_sub(b.value);
        let alpha = dv.wrapping_add(self.mask);
        let beta = dv.wrapping_sub(b.mask);
        let chi = alpha ^ beta;
        let mu = chi | self.mask | b.mask;
        tnum(dv & !mu, mu)
    }

    pub fn neg(self) -> Tnum {
        tnum(0, 0).sub(self)
    }

    pub fn and(self, b: Tnum) -> Tnum {
        let alpha = self.value | self.mask;
        let beta = b.value | b.mask;
        let v = self.value & b.value;
        tnum(v, alpha & beta & !v)
    }

    pub fn or(self, b: Tnum) -> Tnum {
        let v = self.value | b.value;
        let mu = self.mask | b.mask;
        tnum(v, mu & !v)
    }

    pub fn xor(self, b: Tnum) -> Tnum {
        let v = self.value ^ b.value;
        let mu = self.mask | b.mask;
        tnum(v & !mu, mu)
    }

    /// Long multiplication via union of partial accumulators (see C comment).
    pub fn mul(self, b: Tnum) -> Tnum {
        let mut a = self;
        let mut b = b;
        let mut acc = tnum(0, 0);
        while a.value != 0 || a.mask != 0 {
            if a.value & 1 != 0 {
                acc = acc.add(b);
            } else if a.mask & 1 != 0 {
                acc = acc.union(acc.add(b));
            }
            a = a.rshift(1);
            b = b.lshift(1);
        }
        acc
    }

    pub fn overlap(self, b: Tnum) -> bool {
        let mu = !self.mask & !b.mask;
        (self.value & mu) == (b.value & mu)
    }

    /// Disagreement (one known-1 vs known-0) yields known-1 for that bit.
    pub fn intersect(self, b: Tnum) -> Tnum {
        let v = self.value | b.value;
        let mu = self.mask & b.mask;
        tnum(v & !mu, mu)
    }

    /// Optimal over-approximation of the union of both concrete sets.
    pub fn union(self, b: Tnum) -> Tnum {
        let v = self.value & b.value;
        let mu = (self.value ^ b.value) | self.mask | b.mask;
        tnum(v & !mu, mu)
    }

    pub fn cast(self, size: u8) -> Tnum {
        let m = (1u64 << (size * 8)) - 1;
        tnum(self.value & m, self.mask & m)
    }

    pub fn is_aligned(self, size: u64) -> bool {
        if size == 0 {
            return true;
        }
        ((self.value | self.mask) & (size - 1)) == 0
    }

    /// `tnum_in(self, b)`: every value of `b` is a member of `self`.
    pub fn contains(self, b: Tnum) -> bool {
        if b.mask & !self.mask != 0 {
            return false;
        }
        let bv = b.value & !self.mask;
        self.value == bv
    }

    pub fn subreg(self) -> Tnum {
        self.cast(4)
    }

    pub fn clear_subreg(self) -> Tnum {
        self.rshift(32).lshift(32)
    }

    pub fn with_subreg(self, subreg: Tnum) -> Tnum {
        self.clear_subreg().or(subreg.subreg())
    }

    pub fn is_const(self) -> bool {
        self.mask == 0
    }

    pub fn subreg_is_const(self) -> bool {
        self.subreg().is_const()
    }

    /// `tnum_step(t, z)`: smallest member of `t` strictly greater than `z`,
    /// clamped to [tmin, tmax]. Used by the u64↔tnum bound deduction.
    pub fn step(self, z: u64) -> u64 {
        let tmax = self.value | self.mask;
        if z >= tmax {
            return tmax;
        }
        if z < self.value {
            return self.value;
        }
        let d = z - self.value;
        // fls64(x) = 0 if x == 0, else 64 - clz(x)
        let hi = d & !self.mask;
        let carry_mask = if hi == 0 { 0 } else { (1u64 << (64 - hi.leading_zeros())) - 1 };
        let filled = d | carry_mask | !self.mask;
        let inc = filled.wrapping_add(1) & self.mask;
        self.value | inc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Concretize a tnum over a small bit-width by brute force (for soundness checks).
    fn members(t: Tnum, bits: u32) -> Vec<u64> {
        let lim = 1u64 << bits;
        (0..lim).filter(|&v| (v & !t.mask) == (t.value & !t.mask) && (v & !((1u64<<bits)-1))==0).collect()
    }

    #[test]
    fn add_is_sound_over_8bits() {
        // For all concrete a,b in two tnums, (a+b) must be a member of tnum_add.
        let a = Tnum::range(0b0000, 0b0011); // {00xx}
        let b = Tnum::range(0b0100, 0b0101); // {010x}
        let r = a.add(b);
        for &x in &members(a, 8) {
            for &y in &members(b, 8) {
                let s = x.wrapping_add(y);
                assert!(r.contains(Tnum::const_(s)), "sum {s:#b} not in {r:?}");
            }
        }
    }

    #[test]
    fn contains_reflexive() {
        let t = Tnum::range(3, 9);
        assert!(t.contains(t));
    }

    #[test]
    fn const_roundtrip() {
        let c = Tnum::const_(0xdead_beef);
        assert!(c.is_const());
        assert_eq!(c.value, 0xdead_beef);
    }
}
