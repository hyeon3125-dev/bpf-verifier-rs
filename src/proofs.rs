//! Kani symbolic proof harnesses — soundness of the abstract domain.
//!
//! Run with: `cargo kani` (requires `cargo kani setup`).
//! Each harness quantifies over the *entire* input space via `kani::any()`,
//! so a passing harness is a machine-checked soundness theorem, not a sample.
//!
//! Soundness statement for a transfer `f#` modeling concrete `f`:
//!   ∀ x ∈ γ(a), y ∈ γ(b):  f(x,y) ∈ γ(f#(a,b))
//! where γ (concretization) for a tnum is "x agrees with all known bits",
//! and for a cnum is "v lies on the arc".

#![cfg(kani)]

use crate::cnum::{Cnum32, Cnum64};
use crate::reduction::Scalar;
use crate::state::{regsafe_scalar, scalar_contains, scalar_join, State, NREG};
use crate::tnum::Tnum;

/// A symbolic, well-formed tnum (invariant: value & mask == 0).
fn any_tnum() -> Tnum {
    let value: u64 = kani::any();
    let mask: u64 = kani::any();
    kani::assume(value & mask == 0);
    Tnum { value, mask }
}

/// γ membership for tnum: every known bit of `t` matches `x`.
fn tnum_has(t: Tnum, x: u64) -> bool {
    (x & !t.mask) == t.value
}

#[kani::proof]
fn tnum_add_sound() {
    let a = any_tnum();
    let b = any_tnum();
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    kani::assume(tnum_has(a, x));
    kani::assume(tnum_has(b, y));
    let r = a.add(b);
    assert!(tnum_has(r, x.wrapping_add(y)));
}

#[kani::proof]
fn tnum_sub_sound() {
    let a = any_tnum();
    let b = any_tnum();
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    kani::assume(tnum_has(a, x));
    kani::assume(tnum_has(b, y));
    let r = a.sub(b);
    assert!(tnum_has(r, x.wrapping_sub(y)));
}

#[kani::proof]
fn tnum_and_sound() {
    let a = any_tnum();
    let b = any_tnum();
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    kani::assume(tnum_has(a, x));
    kani::assume(tnum_has(b, y));
    let r = a.and(b);
    assert!(tnum_has(r, x & y));
}

#[kani::proof]
fn tnum_or_sound() {
    let a = any_tnum();
    let b = any_tnum();
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    kani::assume(tnum_has(a, x));
    kani::assume(tnum_has(b, y));
    let r = a.or(b);
    assert!(tnum_has(r, x | y));
}

#[kani::proof]
fn tnum_xor_sound() {
    let a = any_tnum();
    let b = any_tnum();
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    kani::assume(tnum_has(a, x));
    kani::assume(tnum_has(b, y));
    let r = a.xor(b);
    assert!(tnum_has(r, x ^ y));
}

/// `tnum_in` (contains) must be sound: if `a.contains(b)` then every member
/// of `b` is a member of `a`.
#[kani::proof]
fn tnum_contains_sound() {
    let a = any_tnum();
    let b = any_tnum();
    let x: u64 = kani::any();
    kani::assume(a.contains(b));
    kani::assume(tnum_has(b, x));
    assert!(tnum_has(a, x));
}

// ---- cnum32: ordering is a sound partial order over concretization ----

fn any_cnum32() -> Cnum32 {
    let base: u32 = kani::any();
    let size: u32 = kani::any();
    Cnum32 { base, size }
}

/// `is_subset(bigger, smaller)` soundness: a member of `smaller` is in `bigger`.
#[kani::proof]
fn cnum32_subset_sound() {
    let bigger = any_cnum32();
    let smaller = any_cnum32();
    let v: u32 = kani::any();
    kani::assume(Cnum32::is_subset(bigger, smaller));
    kani::assume(smaller.contains(v));
    assert!(bigger.contains(v));
}

/// Reflexivity of the ordering (a non-empty arc is a subset of itself).
#[kani::proof]
fn cnum32_subset_reflexive() {
    let c = any_cnum32();
    kani::assume(!c.is_empty());
    assert!(Cnum32::is_subset(c, c));
}

/// `cnum64_cnum32_intersect` soundness: if v ∈ a and (u32)v ∈ b,
/// then v ∈ intersect(a, b). The densest case-analysis in the domain.
#[kani::proof]
fn cnum64_cnum32_intersect_sound() {
    let a = Cnum64 { base: kani::any(), size: kani::any() };
    let b = Cnum32 { base: kani::any(), size: kani::any() };
    let v: u64 = kani::any();
    kani::assume(a.contains(v));
    kani::assume(b.contains(v as u32));
    let t = crate::cnum::cnum64_cnum32_intersect(a, b);
    assert!(t.contains(v));
}

// ---- ② phase-B: is the second deduce pass ever necessary? ----

fn any_scalar() -> Scalar {
    Scalar {
        var_off: any_tnum(),
        r64: Cnum64 { base: kani::any(), size: kani::any() },
        r32: Cnum32 { base: kani::any(), size: kani::any() },
    }
}

/// Does one `__reg_deduce_bounds` pass reach the cross-width fixpoint? On the
/// current cnum-based reduction Kani says yes, over the entire modeled state
/// space.
///
/// Caveat: this is the *isolated* reduction. 9e5fcb003aec showed two rounds
/// were the minimum pre-cnum (verifier_bounds "cross sign boundary" fails at
/// one round), and the cnum refactor (256f0071f9b6) later reshaped the
/// sub-steps. So a SUCCESS here is an open question -- did cnum make the second
/// call in reg_bounds_sync() redundant, or does this isolated model miss the
/// cross-sign state? -- not a proof that removing it from the full verifier is
/// safe.
#[kani::proof]
fn deduce_one_pass_is_fixpoint() {
    let mut s1 = any_scalar();
    kani::assume(!s1.range_bounds_violation());
    let mut s2 = s1;
    s1.reg_deduce_bounds(); // 1 pass
    s2.reg_deduce_bounds();
    s2.reg_deduce_bounds(); // 2 passes
    assert!(s1 == s2, "second deduce pass changed the state");
}

// ---- state equivalence: pruning is sound (Phase 2 / Layer-1 ordering) ----

/// `regsafe(old, cur)` (SCALAR case) is sound: if old is deemed safe-to-prune
/// cur, then every concrete value cur can hold is already covered by old —
/// γ(cur) ⊆ γ(old). This is what licenses is_state_visited() pruning, and the
/// partial order the (future) join operator must respect.
#[kani::proof]
fn regsafe_scalar_sound() {
    let old = any_scalar();
    let cur = any_scalar();
    let v: u64 = kani::any();
    kani::assume(scalar_contains(&cur, v)); // v ∈ γ(cur)
    kani::assume(regsafe_scalar(&old, &cur)); // cur ⊑ old
    assert!(scalar_contains(&old, v)); // ⇒ v ∈ γ(old)
}

// ---- A: cnum join(union) soundness (Phase 2 / Layer-1 join operator) ----

/// `union(a,b)` is a sound join: every member of either operand is in the
/// result. γ(a) ∪ γ(b) ⊆ γ(union(a,b)). (docs/JOIN_DESIGN.md §1.4)
#[kani::proof]
fn cnum32_union_sound() {
    let a = Cnum32 { base: kani::any(), size: kani::any() };
    let b = Cnum32 { base: kani::any(), size: kani::any() };
    let v: u32 = kani::any();
    kani::assume(a.contains(v) || b.contains(v));
    assert!(Cnum32::union(a, b).contains(v));
}

/// `union(a,b)` is an upper bound: a ⊑ union and b ⊑ union.
#[kani::proof]
fn cnum32_union_upper_bound() {
    let a = Cnum32 { base: kani::any(), size: kani::any() };
    let b = Cnum32 { base: kani::any(), size: kani::any() };
    let u = Cnum32::union(a, b);
    assert!(Cnum32::is_subset(u, a)); // a ⊆ u
    assert!(Cnum32::is_subset(u, b)); // b ⊆ u
}

/// `widen(a,b)` is an upper bound (soundness of the widening operator):
/// a ⊑ a▽b and b ⊑ a▽b. (Termination is structural — see JOIN_DESIGN §2.)
#[kani::proof]
fn cnum32_widen_upper_bound() {
    let a = Cnum32 { base: kani::any(), size: kani::any() };
    let b = Cnum32 { base: kani::any(), size: kani::any() };
    let w = Cnum32::widen(a, b);
    assert!(Cnum32::is_subset(w, a)); // a ⊆ a▽b
    assert!(Cnum32::is_subset(w, b)); // b ⊆ a▽b
}

// ---- state-level join (merge_verifier_state model) ----

/// Reg-level join is sound across all three sub-domains at once:
/// v ∈ γ(a) ∨ v ∈ γ(b) ⇒ v ∈ γ(scalar_join(a,b)). (Also exercises tnum_union
/// soundness inside the reduced product.)
#[kani::proof]
fn scalar_join_sound() {
    let a = any_scalar();
    let b = any_scalar();
    let v: u64 = kani::any();
    kani::assume(scalar_contains(&a, v) || scalar_contains(&b, v));
    assert!(scalar_contains(&scalar_join(a, b), v));
}

/// State-level join (modeled merge_verifier_state) is sound: a concrete
/// register assignment in either input state is covered by the join. Lifts
/// reg-level soundness element-wise over the register file.
#[kani::proof]
fn state_join_sound() {
    let a = State { regs: [any_scalar(), any_scalar()] };
    let b = State { regs: [any_scalar(), any_scalar()] };
    let mut vals = [0u64; NREG];
    let mut i = 0;
    while i < NREG {
        vals[i] = kani::any();
        i += 1;
    }
    kani::assume(a.contains(vals) || b.contains(vals));
    assert!(State::join(a, b).contains(vals));
}

/// State-level pruning (modeled states_equal) is sound: if cur ⊑ old then every
/// concrete assignment cur can hold is already covered by old. Lifts regsafe
/// element-wise — this is what makes is_state_visited pruning safe at state level.
#[kani::proof]
fn state_regsafe_sound() {
    let old = State { regs: [any_scalar(), any_scalar()] };
    let cur = State { regs: [any_scalar(), any_scalar()] };
    let mut vals = [0u64; NREG];
    let mut i = 0;
    while i < NREG {
        vals[i] = kani::any();
        i += 1;
    }
    kani::assume(State::regsafe(&old, &cur)); // cur ⊑ old
    kani::assume(cur.contains(vals)); // vals ∈ γ(cur)
    assert!(old.contains(vals)); // ⇒ vals ∈ γ(old)
}
