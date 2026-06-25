#!/usr/bin/env bash
# Reproduce every claim in README.md. Exit non-zero on any failure.
#   - unit tests + differential (Rust vs unmodified kernel tnum.c/cnum.c)
#   - all 10 Kani soundness/idempotence proofs
#
# Requires: cargo, clang (for the differential C harness), and `cargo kani setup`
# already run (https://model-checking.github.io/kani/). Skips Kani with a notice
# if cargo-kani is absent.
set -euo pipefail
cd "$(dirname "$0")"

echo "== [1/2] unit tests + differential =="
cargo test

echo
echo "== [2/2] Kani proofs =="
if ! command -v cargo-kani >/dev/null 2>&1; then
	echo "SKIP: cargo-kani not found (run 'cargo install --locked kani-verifier && cargo kani setup')"
	exit 0
fi

HARNESSES=(
	tnum_add_sound tnum_sub_sound tnum_and_sound tnum_or_sound tnum_xor_sound
	tnum_contains_sound
	cnum32_subset_reflexive cnum32_subset_sound cnum64_cnum32_intersect_sound
	deduce_one_pass_is_fixpoint
	regsafe_scalar_sound
	cnum32_union_sound cnum32_union_upper_bound cnum32_widen_upper_bound
	scalar_join_sound state_join_sound state_regsafe_sound
)
for h in "${HARNESSES[@]}"; do
	printf '  %-32s ' "$h"
	# Capture first (don't pipe into grep -q: under `set -o pipefail` the early
	# grep exit SIGPIPEs cargo-kani and the pipeline reads as failed).
	out=$(cargo kani --harness "$h" 2>/dev/null || true)
	if printf '%s' "$out" | grep -q "VERIFICATION:- SUCCESSFUL"; then
		echo "SUCCESS"
	else
		echo "FAILED"; exit 1
	fi
done
echo
echo "All proofs SUCCESSFUL."
