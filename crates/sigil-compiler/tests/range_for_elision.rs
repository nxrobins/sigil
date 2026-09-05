//! RANGE-FOR (RF-M2) — the Z3-free loop-variable bounds elision, proven on the
//! ACTUAL AIR output. `for v in 0..K { … arr[v] … }` with `K <= N` (K a literal
//! or `arr.len()` on `[T; N]`) elides the runtime bounds chain; EVERY deviation
//! keeps the trap floor. The oracle here is the lowered AIR itself: `TrapIf` is
//! emitted by exactly two sources in these fixtures — the index bounds check and
//! `trap_if`/`trap()` intrinsics (unused below) — so "AIR contains no TrapIf" ⇔
//! "the bounds check was elided", and its presence ⇔ the fail-closed floor.
//!
//! Semantic preservation (elided loops still compute identical values, straddling
//! ranges still trap at runtime) is exec-pinned in
//! crates/sigil-runtime/tests/range_for.rs.

use sigil_test_utils::pipeline::compile_or_panic;

/// True iff the compiled AIR contains ANY `TrapIf` (the runtime bounds check).
fn air_has_trap(src: &str) -> bool {
    let comp = compile_or_panic(src);
    format!("{:?}", comp.air).contains("TrapIf")
}

fn assert_elided(src: &str, label: &str) {
    assert!(
        !air_has_trap(src),
        "{label}: expected the bounds check ELIDED (no TrapIf in AIR)"
    );
}

fn assert_trap_floor(src: &str, label: &str) {
    assert!(
        air_has_trap(src),
        "{label}: expected the runtime-trap FLOOR (TrapIf present in AIR) — an \
         elision here would be UNSOUND"
    );
}

// ── Elides (the positive space: K <= N, bare loop var, clean body) ───────────

#[test]
fn elides_literal_bound_equal_to_size() {
    assert_elided(
        r#"
module m;
pub fn sum3(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "K == N literal",
    );
}

#[test]
fn elides_literal_bound_below_size() {
    assert_elided(
        r#"
module m;
pub fn sum2(a: [i64; 5]) -> i64 {
    let mut acc = 0;
    for i in 0..2 {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "K < N literal",
    );
}

#[test]
fn elides_len_bound_on_fixed_array() {
    // THE headline shape: `for i in 0..a.len() { a[i] }` — `len()` on `[T; N]`
    // resolves to the STATIC size (the ArrayLen intrinsic), so the whole loop
    // is checked at compile time and runs with zero runtime bounds overhead.
    assert_elided(
        r#"
module m;
pub fn sum_all(a: [i64; 4]) -> i64 {
    let mut acc = 0;
    for i in 0..a.len() {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "0..a.len() on [i64; 4]",
    );
}

#[test]
fn elides_write_path_too() {
    // `arr[i] = v` shares `index_base_and_bounds` with the read path — the
    // write's bounds check elides under the same fact.
    assert_elided(
        r#"
module m;
pub fn fill() -> i64 {
    let mut a = [0, 0, 0];
    for i in 0..3 {
        a[i] = i;
    }
    return a[2];
}
"#,
        "write path a[i] = v",
    );
}

#[test]
fn elides_smaller_array_with_smaller_bound() {
    // The fact is per-VARIABLE, the check per-ARRAY: `0..2` elides on BOTH a
    // `[i64;2]` and a `[i64;9]` (2 <= 2 and 2 <= 9).
    assert_elided(
        r#"
module m;
pub fn two(a: [i64; 2], b: [i64; 9]) -> i64 {
    let mut acc = 0;
    for i in 0..2 {
        acc = acc + a[i] + b[i];
    }
    return acc;
}
"#,
        "one fact, two arrays, both fit",
    );
}

// ── Keeps the trap floor (the fail-closed space — every gate refusal) ────────

#[test]
fn floor_when_bound_exceeds_size() {
    // 0..5 over [i64; 3]: iterations 0..2 are fine, 3..4 trap — a per-execution
    // T278 would be FALSE, an elision UNSOUND. The floor stays.
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..5 {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "K > N straddle",
    );
}

#[test]
fn floor_when_start_not_literal_zero() {
    // v1 Boring Limit: the fact requires a surface-literal `0` start.
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 1..3 {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "non-zero start",
    );
}

#[test]
fn floor_when_bound_is_a_variable() {
    // A runtime bound resolves no K — the loop still WORKS, the check stays.
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3], n: i64) -> i64 {
    let mut acc = 0;
    for i in 0..n {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "variable bound",
    );
}

#[test]
fn floor_when_len_is_of_a_different_larger_array() {
    // `0..b.len()` (K=9) indexing `a: [i64;3]` — the fact says v < 9, the
    // array needs v < 3: 9 <= 3 fails, floor stays. The fact/array pairing is
    // per-index-site, never by which array supplied the bound.
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3], b: [i64; 9]) -> i64 {
    let mut acc = 0;
    for i in 0..b.len() {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "len of a LARGER array",
    );
}

#[test]
fn floor_when_index_is_compound() {
    // `a[i + 0]` is not a bare Local — no stamp (the fragment-guard-free
    // discipline: no arithmetic reasoning, ever).
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        acc = acc + a[i + 0];
    }
    return acc;
}
"#,
        "compound index i + 0",
    );
}

#[test]
fn floor_when_let_shadows_loop_var() {
    // The pre-scan refuses the WHOLE loop's fact on ANY rebinding: the `a[i]`
    // BEFORE the shadowing let would be safe in isolation, but the fact is
    // all-or-nothing (no partial windows — the Boring Limit).
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        acc = acc + a[i];
        let i = 99;
        acc = acc + i;
    }
    return acc;
}
"#,
        "let-shadowed body",
    );
}

#[test]
fn floor_when_let_tuple_shadows_loop_var() {
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        let (i, j) = (0, 1);
        acc = acc + a[i] + j;
    }
    return acc;
}
"#,
        "LetTuple-shadowed body",
    );
}

#[test]
fn floor_when_match_binding_shadows_loop_var() {
    assert_trap_floor(
        r#"
module m;
pub enum Maybe { None, Some(i64) }
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        let m = Maybe::Some(1);
        match m {
            Maybe::Some(i) => {
                acc = acc + a[i];
            },
            Maybe::None => {
                acc = acc + 1;
            },
        }
    }
    return acc;
}
"#,
        "match-binding-shadowed body",
    );
}

#[test]
fn floor_when_nested_loop_reuses_name() {
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        for i in 0..2 {
            acc = acc + 1;
        }
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "nested same-name loop",
    );
}

#[test]
fn floor_inside_closure_body() {
    // The BARRIER: a closure body is a different function post-lambda-lifting;
    // the enclosing loop's fact must NOT be visible inside it, even when the
    // closure captures the array and uses the same variable NAME as its param.
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        let g = fn(i: i64) -> i64 {
            let b = [7, 8];
            return b[i];
        };
        acc = acc + g(1);
    }
    return acc;
}
"#,
        "index inside a closure body",
    );
}

#[test]
fn floor_on_slice_receiver() {
    // A slice has no static N — never elided (the shipped literal rule's
    // discipline, unchanged).
    assert_trap_floor(
        r#"
module m;
pub fn f(s: &[i64]) -> i64 {
    let mut acc = 0;
    for i in 0..2 {
        acc = acc + s[i];
    }
    return acc;
}
"#,
        "slice receiver",
    );
}

#[test]
fn nested_distinct_names_inner_and_outer_both_elide() {
    // Distinct names ⇒ both facts live; each index elides against its own var.
    assert_elided(
        r#"
module m;
pub fn f(a: [i64; 3], b: [i64; 4]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        for j in 0..4 {
            acc = acc + a[i] + b[j];
        }
    }
    return acc;
}
"#,
        "nested distinct names",
    );
}

// ── RF-M3: guard tightening (the composed interval) ──────────────────────────

#[test]
fn elides_under_narrowing_guard() {
    // 0..10 over [i64;5] straddles — but INSIDE `if i < 5` the composed
    // interval is [0,4] ⊆ [0,5): the guarded index elides. The guard itself
    // is the runtime check; the bounds check would be redundant.
    assert_elided(
        r#"
module m;
pub fn f(a: [i64; 5]) -> i64 {
    let mut acc = 0;
    for i in 0..10 {
        if i < 5 {
            acc = acc + a[i];
        }
    }
    return acc;
}
"#,
        "if i < 5 guard inside 0..10",
    );
}

#[test]
fn elides_under_eq_guard() {
    assert_elided(
        r#"
module m;
pub fn f(a: [i64; 5]) -> i64 {
    let mut acc = 0;
    for i in 0..10 {
        if i == 2 {
            acc = acc + a[i];
        }
    }
    return acc;
}
"#,
        "if i == 2 guard",
    );
}

#[test]
fn no_claim_on_contradictory_guards() {
    // [0,2] ∩ [7,9] = ∅ — the access is unreachable; no elision AND no T278
    // (a per-execution claim about code that never executes would be vacuous
    // either way; the boring answer is the floor).
    assert_trap_floor(
        r#"
module m;
pub fn f(a: [i64; 5]) -> i64 {
    let mut acc = 0;
    for i in 0..10 {
        if i < 3 {
            if i >= 7 {
                acc = acc + a[i];
            }
        }
    }
    return acc;
}
"#,
        "contradictory guards (empty interval)",
    );
}
