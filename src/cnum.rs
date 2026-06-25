//! cnum: circular number — range-level abstract domain.
//!
//! 1:1 port of bpf-next `kernel/bpf/cnum.c` + `cnum_defs.h` @ a975094bf.
//! A `cnum` is an arc on the integer circle: `base` is the first value,
//! `size` is the count of values *after* base (base excluded so the full
//! 0..UT_MAX range — 2^width values — fits in a width-bit `size`).
//!
//! Signed and unsigned ranges share one representation; an arc may cross
//! the UT_MAX/0 boundary (`urange_overflow`) or the ST_MAX/ST_MIN boundary
//! (`srange_overflow`). All arithmetic is wrapping, matching C.

macro_rules! define_cnum {
    ($name:ident, $ut:ty, $st:ty) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $name {
            pub base: $ut,
            pub size: $ut,
        }

        impl $name {
            pub const UNBOUNDED: $name = $name { base: 0, size: <$ut>::MAX };
            pub const EMPTY: $name = $name { base: <$ut>::MAX, size: <$ut>::MAX };

            pub fn from_urange(min: $ut, max: $ut) -> $name {
                $name { base: min, size: max.wrapping_sub(min) }
            }

            pub fn from_srange(min: $st, max: $st) -> $name {
                let size = (max as $ut).wrapping_sub(min as $ut);
                let base = if size == <$ut>::MAX { 0 } else { min as $ut };
                $name { base, size }
            }

            /// True if this cnum represents two unsigned ranges (crosses UT_MAX/0).
            #[inline]
            pub fn urange_overflow(self) -> bool {
                // base + size > UT_MAX, overflow-safe
                self.size > <$ut>::MAX - self.base
            }

            pub fn umin(self) -> $ut {
                if self.urange_overflow() { 0 } else { self.base }
            }

            pub fn umax(self) -> $ut {
                if self.urange_overflow() { <$ut>::MAX } else { self.base.wrapping_add(self.size) }
            }

            /// True if this cnum represents two signed ranges (crosses ST_MAX/ST_MIN).
            #[inline]
            pub fn srange_overflow(self) -> bool {
                self.contains(<$st>::MAX as $ut) && self.contains(<$st>::MIN as $ut)
            }

            pub fn smin(self) -> $st {
                if self.srange_overflow() {
                    <$st>::MIN
                } else {
                    ((self.base as $st)).min(self.base.wrapping_add(self.size) as $st)
                }
            }

            pub fn smax(self) -> $st {
                if self.srange_overflow() {
                    <$st>::MAX
                } else {
                    ((self.base as $st)).max(self.base.wrapping_add(self.size) as $st)
                }
            }

            pub fn is_empty(self) -> bool {
                self.base == Self::EMPTY.base && self.size == Self::EMPTY.size
            }

            pub fn is_const(self) -> bool {
                self.size == 0
            }

            pub fn contains(self, v: $ut) -> bool {
                if self.is_empty() {
                    return false;
                }
                if self.urange_overflow() {
                    v >= self.base || v <= self.base.wrapping_add(self.size)
                } else {
                    v >= self.base && v <= self.base.wrapping_add(self.size)
                }
            }

            fn normalize(mut self) -> $name {
                if self.size == <$ut>::MAX && self.base != 0 && self.base != (<$st>::MAX as $ut) {
                    self.base = 0;
                }
                self
            }

            pub fn add(self, b: $name) -> $name {
                if self.is_empty() || b.is_empty() {
                    return Self::EMPTY;
                }
                if self.size > <$ut>::MAX - b.size {
                    $name { base: 0, size: <$ut>::MAX }
                } else {
                    $name {
                        base: self.base.wrapping_add(b.base),
                        size: self.size.wrapping_add(b.size),
                    }
                    .normalize()
                }
            }

            pub fn negate(self) -> $name {
                if self.is_empty() {
                    return Self::EMPTY;
                }
                $name {
                    base: (self.base.wrapping_add(self.size)).wrapping_neg(),
                    size: self.size,
                }
                .normalize()
            }

            /// `is_subset(bigger, smaller)`: every member of `smaller` is in `bigger`.
            pub fn is_subset(bigger: $name, mut smaller: $name) -> bool {
                if smaller.is_empty() {
                    return true;
                }
                if bigger.is_empty() {
                    return false;
                }
                // rotate both arcs so 'bigger' starts at origin (no overflow)
                smaller.base = smaller.base.wrapping_sub(bigger.base);
                let bigger_size = bigger.size;
                if smaller.urange_overflow() && bigger_size < <$ut>::MAX {
                    return false;
                }
                smaller.base.wrapping_add(smaller.size) <= bigger_size
            }

            /// Possibly-empty intersection. If two sub-arcs intersect, over-approximates
            /// to the smaller of the two operands.
            pub fn intersect(mut a: $name, mut b: $name) -> $name {
                if a.is_empty() || b.is_empty() {
                    return Self::EMPTY;
                }
                if a.base > b.base {
                    core::mem::swap(&mut a, &mut b);
                }
                let dbase = b.base.wrapping_sub(a.base);
                let b1 = $name { base: dbase, size: b.size };
                if b1.urange_overflow() {
                    if b1.base <= a.size {
                        // two disjoint arcs: over-approximate to smaller operand
                        if a.size <= b.size { a } else { b }
                    } else {
                        // only b tail intersects a
                        $name {
                            base: a.base,
                            size: a.size.min(b1.base.wrapping_add(b1.size)),
                        }
                    }
                } else if a.size >= b1.base {
                    // single-arc intersection
                    $name {
                        base: b.base,
                        size: (a.size.wrapping_sub(dbase)).min(b.size),
                    }
                } else {
                    Self::EMPTY
                }
            }

            pub fn intersect_with(&mut self, src: $name) {
                *self = Self::intersect(*self, src);
            }

            /// Join (⊔): the smallest-ish arc covering γ(a) ∪ γ(b).
            /// Over-approximation (the exact union of two disjoint arcs is not an
            /// arc). Soundness is the contract; precision is best-effort.
            /// Design: docs/JOIN_DESIGN.md §1.
            pub fn union(a: $name, b: $name) -> $name {
                // case 1: bottom is the identity
                if a.is_empty() {
                    return b;
                }
                if b.is_empty() {
                    return a;
                }
                // case 2: containment (is_subset(big, small) = small ⊆ big)
                if Self::is_subset(a, b) {
                    return a; // b ⊆ a
                }
                if Self::is_subset(b, a) {
                    return b; // a ⊆ b
                }
                // case 3·4: build a candidate arc from each base reaching the
                // farthest endpoint clockwise, then VERIFY it actually covers
                // both via the (proven-sound) is_subset. A candidate that fails
                // (e.g. the other operand is an overflow arc the max-distance
                // misses) is discarded; if neither covers, fall back to ⊤.
                // This keeps soundness exact at the cost of precision on the
                // genuinely-two-arc cases. (docs/JOIN_DESIGN.md §1)
                let a_end = a.base.wrapping_add(a.size);
                let b_end = b.base.wrapping_add(b.size);
                let s1 = a
                    .size
                    .max(b.base.wrapping_sub(a.base))
                    .max(b_end.wrapping_sub(a.base));
                let s2 = b
                    .size
                    .max(a.base.wrapping_sub(b.base))
                    .max(a_end.wrapping_sub(b.base));
                let c1 = $name { base: a.base, size: s1 };
                let c2 = $name { base: b.base, size: s2 };
                let c1_ok = Self::is_subset(c1, a) && Self::is_subset(c1, b);
                let c2_ok = Self::is_subset(c2, a) && Self::is_subset(c2, b);
                match (c1_ok, c2_ok) {
                    (true, true) => if s1 <= s2 { c1 } else { c2 },
                    (true, false) => c1,
                    (false, true) => c2,
                    (false, false) => $name { base: 0, size: <$ut>::MAX }, // ⊤
                }
            }

            /// Widening (▽) for termination. Simple version: if the new value
            /// `b` is already inside `a` the iteration is stable → keep `a`;
            /// otherwise jump straight to ⊤. Any ascending chain x_{n+1}=x_n▽y
            /// stabilizes in ≤2 steps (⊤ is absorbing). Upper bound: a,b ⊑ a▽b.
            /// (docs/JOIN_DESIGN.md §2 — precise variant is future work.)
            pub fn widen(a: $name, b: $name) -> $name {
                if Self::is_subset(a, b) {
                    a // b ⊆ a, stable
                } else {
                    $name { base: 0, size: <$ut>::MAX } // ⊤
                }
            }
        }
    };
}

define_cnum!(Cnum32, u32, i32);
define_cnum!(Cnum64, u64, i64);

/// `cnum32_from_cnum64` — narrow a 64-bit arc to 32-bit.
pub fn cnum32_from_cnum64(c: Cnum64) -> Cnum32 {
    if c.is_empty() {
        return Cnum32::EMPTY;
    }
    if c.size >= u32::MAX as u64 {
        Cnum32 { base: 0, size: u32::MAX }
    } else {
        Cnum32 { base: c.base as u32, size: c.size as u32 }
    }
}

/// `cnum64_cnum32_intersect` — tighten a 64-bit arc `a` knowing `(u32)v ∈ b`
/// for every member v. 1:1 port of cnum.c:41-120. Wrapping matches C (the
/// `b1_max` u32 overflow is intentional per the C comment).
///
/// The densest case-analysis in the domain.
pub fn cnum64_cnum32_intersect(a: Cnum64, b: Cnum32) -> Cnum64 {
    let b1 = Cnum32 { base: b.base.wrapping_sub(a.base as u32), size: b.size };
    let mut t = a;

    if a.is_empty() || b.is_empty() {
        return Cnum64::EMPTY;
    }

    if b1.urange_overflow() {
        let b1_max = b1.base.wrapping_add(b1.size); // u32, intentional overflow
        let a_size32 = a.size as u32;
        if (a_size32 as u64) > (b1_max as u64) && a_size32 < b1.base {
            let d = (a_size32 as u64) - (b1_max as u64);
            t.size = t.size.wrapping_sub(d);
        }
        // else: no adjustment possible
    } else {
        if t.size < b1.base as u64 {
            return Cnum64::EMPTY;
        }
        t.base = t.base.wrapping_add(b1.base as u64);
        t.size = t.size.wrapping_sub(b1.base as u64);
        let b1_max = b1.base.wrapping_add(b1.size); // u32
        let a_size32 = a.size as u32;
        let d: u64 = if a_size32 < b1.base {
            (a_size32 as u64) + ((1u64 << 32) - b1_max as u64)
        } else if a_size32 >= b1_max {
            (a_size32 as u64) - (b1_max as u64)
        } else {
            0
        };
        if t.size < d {
            return Cnum64::EMPTY;
        }
        t.size = t.size.wrapping_sub(d);
    }
    t
}

#[cfg(test)]
mod tests {
    use super::*;

    // brute-force concretize a Cnum32 over an 8-bit subspace for soundness checks
    fn members8(c: Cnum32) -> Vec<u32> {
        (0u32..256).filter(|&v| c.contains(v)).collect()
    }

    #[test]
    fn from_urange_roundtrip() {
        let c = Cnum32::from_urange(10, 20);
        assert_eq!(c.umin(), 10);
        assert_eq!(c.umax(), 20);
        assert!(c.contains(15));
        assert!(!c.contains(21));
    }

    #[test]
    fn signed_wrap_repr() {
        // {U32_MAX, 1} == signed [-1, 0]
        let c = Cnum32 { base: u32::MAX, size: 1 };
        assert_eq!(c.smin(), -1);
        assert_eq!(c.smax(), 0);
    }

    #[test]
    fn add_is_sound_small() {
        let a = Cnum32::from_urange(3, 7);
        let b = Cnum32::from_urange(10, 12);
        let r = a.add(b);
        for x in members8(a) {
            for y in members8(b) {
                assert!(r.contains(x.wrapping_add(y)), "{}+{} not in {:?}", x, y, r);
            }
        }
    }

    #[test]
    fn subset_reflexive_and_empty() {
        let c = Cnum32::from_urange(5, 9);
        assert!(Cnum32::is_subset(c, c));
        assert!(Cnum32::is_subset(c, Cnum32::EMPTY));
        assert!(!Cnum32::is_subset(Cnum32::EMPTY, c));
    }

    #[test]
    fn intersect_basic() {
        let a = Cnum32::from_urange(0, 100);
        let b = Cnum32::from_urange(50, 200);
        let r = Cnum32::intersect(a, b);
        assert!(r.contains(50) && r.contains(100));
        assert!(!r.contains(150));
    }

    #[test]
    fn union_disjoint_covers_both() {
        let a = Cnum32::from_urange(0, 10);
        let b = Cnum32::from_urange(20, 30);
        let u = Cnum32::union(a, b);
        for v in [0u32, 5, 10, 20, 25, 30] {
            assert!(u.contains(v), "union must contain {v}: {u:?}");
        }
    }

    #[test]
    fn union_overlap_covers_both() {
        let a = Cnum32::from_urange(0, 50);
        let b = Cnum32::from_urange(40, 100);
        let u = Cnum32::union(a, b);
        for v in [0u32, 25, 45, 75, 100] {
            assert!(u.contains(v), "union must contain {v}: {u:?}");
        }
    }

    #[test]
    fn union_identity_and_idempotent() {
        let a = Cnum32::from_urange(5, 9);
        assert_eq!(Cnum32::union(a, a), a);
        assert_eq!(Cnum32::union(a, Cnum32::EMPTY), a);
        assert_eq!(Cnum32::union(Cnum32::EMPTY, a), a);
    }

    #[test]
    fn union_containment_returns_bigger() {
        let big = Cnum32::from_urange(0, 100);
        let small = Cnum32::from_urange(20, 30);
        assert_eq!(Cnum32::union(big, small), big);
        assert_eq!(Cnum32::union(small, big), big);
    }

    #[test]
    #[ignore] // diagnostic: find first soundness counterexample in a small space
    fn union_bruteforce_counterexample() {
        let n = 12u32;
        for ab in 0..n {
            for asz in 0..n {
                for bb in 0..n {
                    for bsz in 0..n {
                        let a = Cnum32 { base: ab, size: asz };
                        let b = Cnum32 { base: bb, size: bsz };
                        let u = Cnum32::union(a, b);
                        for v in 0..(2 * n) {
                            if (a.contains(v) || b.contains(v)) && !u.contains(v) {
                                panic!("CEX a={a:?} b={b:?} v={v} -> u={u:?}");
                            }
                        }
                    }
                }
            }
        }
    }
}
