# bpf_verifier_rs

A Rust model of the bpf-next verifier **scalar abstract domain**, built to
machine-check the domain's soundness and to probe one concrete question about
`reg_bounds_sync`. Tracks bpf-next `a975094bf` (7.2-rc1 merge window).

This is a *model for verification*, **not** a proposed verifier rewrite. The
security boundary (`regsafe`/`stacksafe` — "old-safe ⇒ cur-safe") stays in the
kernel; this crate only re-expresses the transfer/reduction math so it can be
checked by an SMT-backed tool (Kani/CBMC) and diffed against the real C.

## What it ports (1:1, from bpf-next)

| Rust | C source | domain |
|------|----------|--------|
| `src/tnum.rs` | `kernel/bpf/tnum.c` | tnum (known/unknown bits) |
| `src/cnum.rs` | `kernel/bpf/cnum.c` + `cnum_defs.h` | cnum32/64 (circular-number range) |
| `src/reduction.rs` | `verifier.c` `reg_bounds_sync` & helpers | reduced product + cross-width reduction |

## Claims (and what backs each)

1. **The Rust model is a sound abstraction.** 9 Kani harnesses
   (`src/proofs.rs`), each quantified over the *entire* input space via
   `kani::any()`, prove soundness of the tnum transfers (`add/sub/and/or/xor`),
   `tnum_in`, the cnum subset order, and `cnum64_cnum32_intersect`.
2. **The Rust port matches C.** `tests/differential.rs` links the *unmodified*
   kernel `tnum.c`+`cnum.c` (via userspace stubs, `diff/`) and fuzzes N=2000 ×
   11 ops → 0 mismatch. So (1) carries over to the C implementation.
3. **`__reg_deduce_bounds` is idempotent on this model.** Kani proves one pass
   reaches the cross-width-reduction fixpoint over all inputs. This is an *open
   question*, not a cleanup: 9e5fcb003aec established two rounds as the minimum
   pre-cnum (verifier_bounds "cross sign boundary" fails at one round), and the
   circular-number refactor (256f0071f9b6) later reshaped the sub-steps. Whether
   cnum made the second call in `reg_bounds_sync()` redundant, or the cross-sign
   case still needs it and this isolated model misses that state, needs the
   selftest run on a built kernel — not done here.

### What it does NOT claim
- Not a soundness proof of the *whole* verifier — only the scalar tnum/cnum
  transfer & reduction math modeled here.
- No over-conservative (false-reject) bug is claimed; none was found in this scope.
- The one-pass idempotence (claim 3) is on the modeled state space; whether it
  licenses removing the second call in the real verifier is the open question
  stated there, and needs a built-kernel selftest run, not done here.

## Verify it yourself

```sh
# Point BPF_NEXT at your bpf-next checkout (modeled against a975094bf) so the
# differential test can compile the real kernel tnum.c/cnum.c. Without it the
# differential self-skips; the Kani proofs and unit tests run regardless.
export BPF_NEXT=/path/to/bpf-next

./reproduce.sh          # 11 unit tests + differential (needs clang) + all 10 Kani proofs
# or piecemeal:
cargo test              # unit + differential (builds the C harness via diff/build.sh)
cargo kani --harness tnum_add_sound      # any single proof; needs `cargo kani setup`
```

The C↔Rust correspondence is given inline in each source file's header
comment (e.g. `src/cnum.rs` cites `cnum.c` / `cnum_defs.h`).
