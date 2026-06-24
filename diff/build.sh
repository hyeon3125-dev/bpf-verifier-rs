#!/usr/bin/env bash
# Build the differential harness against the real kernel tnum.c + cnum.c.
# Userspace stubs (diff/stub/linux/*) satisfy the kernel header deps; the
# .c files themselves are the genuine bpf-next sources, unmodified.
#
# Point BPF_NEXT at your bpf-next checkout (modeled against a975094bf):
#   BPF_NEXT=/path/to/bpf-next ./build.sh
# Falls back to the in-tree clone used during development.
set -euo pipefail
cd "$(dirname "$0")"
BPF=${BPF_NEXT:-../../bpf_selftest_gap_finder/bpf-next}
OUT=${1:-/tmp/diff_harness}

if [ ! -f "$BPF/kernel/bpf/cnum.c" ]; then
	echo "error: bpf-next not found at '$BPF'. Set BPF_NEXT=/path/to/bpf-next" >&2
	exit 1
fi

clang -Istub -std=gnu11 -w \
	harness.c \
	"$BPF/kernel/bpf/tnum.c" \
	"$BPF/kernel/bpf/cnum.c" \
	-o "$OUT"
echo "built: $OUT"
