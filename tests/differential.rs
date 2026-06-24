//! Differential test: Rust model vs the genuine kernel C (tnum.c + cnum.c),
//! linked through `diff/harness.c`. If these match over a large fuzzed batch,
//! the Rust port faithfully mirrors C — which lets the Kani soundness proofs
//! and the ② "2082 dead" result carry over to the kernel implementation.
//!
//! Builds the C harness via `diff/build.sh` (needs clang). Skips with a loud
//! message if the build fails (e.g. clang absent in CI).

use std::io::Write;
use std::process::{Command, Stdio};

use bpf_verifier_rs::cnum::{cnum32_from_cnum64, cnum64_cnum32_intersect, Cnum32, Cnum64};
use bpf_verifier_rs::tnum::Tnum;

const N: usize = 2000;
const HARNESS: &str = "/tmp/diff_harness_test";

/// Tiny deterministic LCG so both sides see identical inputs without a dep.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        // mix high bits down
        self.0 ^ (self.0 >> 29)
    }
}

fn build_harness() -> bool {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/diff");
    let status = Command::new("bash")
        .arg("build.sh")
        .arg(HARNESS)
        .current_dir(dir)
        .status();
    matches!(status, Ok(s) if s.success())
}

/// One Rust-side result line, matching the C harness output format.
fn rust_eval(op: &str, a: u64, b: u64, c: u64, d: u64) -> String {
    let tn = |v: u64, m: u64| Tnum { value: v & !m, mask: m };
    match op {
        "tnum_add" => {
            let r = tn(a, b).add(tn(c, d));
            format!("{} {}", r.value, r.mask)
        }
        "tnum_sub" => {
            let r = tn(a, b).sub(tn(c, d));
            format!("{} {}", r.value, r.mask)
        }
        "tnum_and" => {
            let r = tn(a, b).and(tn(c, d));
            format!("{} {}", r.value, r.mask)
        }
        "tnum_or" => {
            let r = tn(a, b).or(tn(c, d));
            format!("{} {}", r.value, r.mask)
        }
        "tnum_xor" => {
            let r = tn(a, b).xor(tn(c, d));
            format!("{} {}", r.value, r.mask)
        }
        "tnum_mul" => {
            let r = tn(a, b).mul(tn(c, d));
            format!("{} {}", r.value, r.mask)
        }
        "c64_isect" => {
            let r = Cnum64::intersect(Cnum64 { base: a, size: b }, Cnum64 { base: c, size: d });
            format!("{} {}", r.base, r.size)
        }
        "c64_add" => {
            let r = (Cnum64 { base: a, size: b }).add(Cnum64 { base: c, size: d });
            format!("{} {}", r.base, r.size)
        }
        "c64_subset" => {
            let r = Cnum64::is_subset(Cnum64 { base: a, size: b }, Cnum64 { base: c, size: d });
            format!("{}", if r { 1 } else { 0 })
        }
        "c32_from64" => {
            let r = cnum32_from_cnum64(Cnum64 { base: a, size: b });
            format!("{} {}", r.base, r.size)
        }
        "c64_c32" => {
            let r = cnum64_cnum32_intersect(
                Cnum64 { base: a, size: b },
                Cnum32 { base: c as u32, size: d as u32 },
            );
            format!("{} {}", r.base, r.size)
        }
        _ => unreachable!(),
    }
}

#[test]
fn rust_matches_c() {
    if !build_harness() {
        eprintln!("SKIP rust_matches_c: C harness build failed (clang missing?)");
        return;
    }

    let two_arg = [
        "tnum_add", "tnum_sub", "tnum_and", "tnum_or", "tnum_xor", "tnum_mul", "c64_isect",
        "c64_add", "c64_subset", "c64_c32",
    ];
    let one_arg = ["c32_from64"];

    // Build the batch: input lines + expected Rust outputs in lockstep.
    let mut input = String::new();
    let mut rust_out: Vec<String> = Vec::new();
    let mut rng = Lcg(0x1234_5678_9abc_def0);

    for _ in 0..N {
        for op in two_arg {
            let (mut a, b, mut c, d) = (rng.next(), rng.next(), rng.next(), rng.next());
            // tnum invariant: value & mask == 0. Normalize the *input* so both
            // C and Rust evaluate the identical well-formed tnum. cnum has no
            // such constraint (all base/size pairs are valid arcs).
            if op.starts_with("tnum") {
                a &= !b;
                c &= !d;
            }
            input.push_str(&format!("{op} {a} {b} {c} {d}\n"));
            rust_out.push(rust_eval(op, a, b, c, d));
        }
        for op in one_arg {
            let (a, b) = (rng.next(), rng.next());
            input.push_str(&format!("{op} {a} {b}\n"));
            rust_out.push(rust_eval(op, a, b, 0, 0));
        }
    }

    // Run the C harness once over the whole batch.
    let mut child = Command::new(HARNESS)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn harness");
    // Write stdin from a separate thread: the harness emits ~22k output lines,
    // which overflow the pipe buffer and would deadlock if we wrote and read on
    // the same thread (writer blocks on full stdout pipe, reader hasn't started).
    let mut stdin = child.stdin.take().unwrap();
    let input_for_writer = input.clone();
    let writer = std::thread::spawn(move || {
        stdin.write_all(input_for_writer.as_bytes()).unwrap();
        drop(stdin); // close → harness sees EOF
    });
    let out = child.wait_with_output().expect("harness output");
    writer.join().unwrap();
    assert!(out.status.success(), "harness exited non-zero");
    let c_out = String::from_utf8(out.stdout).unwrap();
    let c_lines: Vec<&str> = c_out.lines().collect();

    assert_eq!(
        c_lines.len(),
        rust_out.len(),
        "line count mismatch: C={} Rust={}",
        c_lines.len(),
        rust_out.len()
    );

    // Compare line by line; re-derive the op/args for diagnostics on mismatch.
    let mut mismatches = 0;
    for (i, (rl, cl)) in rust_out.iter().zip(c_lines.iter()).enumerate() {
        if rl != cl.trim() {
            mismatches += 1;
            if mismatches <= 5 {
                let input_line = input.lines().nth(i).unwrap_or("?");
                eprintln!("MISMATCH [{input_line}]  rust=[{rl}]  c=[{cl}]");
            }
        }
    }
    assert_eq!(mismatches, 0, "{mismatches} Rust/C mismatches (see stderr)");
}
