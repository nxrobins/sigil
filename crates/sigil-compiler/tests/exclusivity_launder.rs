//! DEF-2c PR-3 — alias-resolution hardening (the adversarial-launder suite).
//!
//! PR-1/2 wired the exclusivity gate; this suite proves the `alias_origin` resolver is
//! SOUND, not merely present:
//!
//!  * TRANSITIVE to the terminal root — a `let` chain `let y = x; let z = y` resolves `z`
//!    all the way back to `x` (NC-2c-3), so a multi-hop launder cannot smuggle one object
//!    to a frozen and a mutable parameter under different names.
//!  * WRITE-per-`let` — re-binding a name with a NON-aliasing RHS clears its stale alias
//!    (aliasing is non-monotone, UNLIKE the append-only `readonly_locals`), so a fresh
//!    shadow `let x = Box{}` over an aliasing `let x = p` does NOT keep aliasing `p`.
//!  * SCOPE-CORRECT — `alias_origin` is a flat tracker field, but a nested block's `let`
//!    shadow must not leak past the block (NC-2c-4). Tested in BOTH failure directions:
//!    an inner shadow that REMOVES an outer alias must not MASK a later outer conflict
//!    (under-reject = unsound); an inner shadow that ADDS an alias must not LEAK a
//!    spurious one (over-reject). Both are the block-scope analogue of the cloned `env`.

use sigil_compiler::compile_tool;

fn codes(src: &str) -> Vec<String> {
    match compile_tool(src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn has(src: &str, code: &str) -> bool {
    codes(src).iter().any(|c| c == code)
}

// `sink` reads `a` frozen and may mutate `b`. The conditional tests branch on an `i64`
// parameter (`if n > 0`) so no bool literal / extra binding is needed.
const PRELUDE: &str = "module tool;\n\
     record Box { v: i64 }\n\
     fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }\n";

const TOOL_MAIN: &str =
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0; }\n";

// ── transitivity: the multi-hop launder ──────────────────────────────────────────

#[test]
fn two_hop_launder_resolves_to_terminal_root_t255() {
    // `let y = x; let z = y` — `z` aliases `x` through TWO hops. `sink(x, z)` hands the
    // one object to the frozen `a` (as `x`) and the mutable `b` (as `z`); the resolver
    // must follow `z → y → x` to catch it. T255.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ let x: Box = Box {{ v: 1 }}; let y: Box = x; let z: Box = y; \
             let _r: i64 = sink(x, z); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn transitive_chain_to_distinct_object_is_clean() {
    // `y` aliases `x`; `z` is a FRESH box. `sink(y, z)` — frozen `y` (→ x), mutable fresh
    // `z` — distinct roots, no conflict. Proves the resolver doesn't over-match a chain.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ let x: Box = Box {{ v: 1 }}; let y: Box = x; let z: Box = Box {{ v: 2 }}; \
             let _r: i64 = sink(y, z); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── write-per-`let`: the fresh shadow clears a stale alias ─────────────────────────

#[test]
fn fresh_same_block_shadow_clears_alias_is_clean() {
    // `let x = p` makes `x` alias `p`; re-binding `let x = Box{}` (a fresh construct, not a
    // place) WRITES `x` to its own root — the stale alias is cleared, not inherited. So
    // `sink(p, x)` passes two DISTINCT objects → clean. (If the alias map were append-only
    // like `readonly_locals`, this would spuriously fire.)
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; let x: Box = p; let x: Box = Box {{ v: 2 }}; \
             let _r: i64 = sink(p, x); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── scope-correctness: a nested-block shadow must not leak (both directions) ───────

#[test]
fn inner_block_shadow_does_not_mask_outer_conflict_t255() {
    // THE under-reject guard. Outer `let x = p` aliases `p`; an inner-block `let x = Box{}`
    // REMOVES that alias WITHIN the `if`. After the block, the outer `x` still aliases `p`,
    // so `sink(p, x)` is a real conflict. Without scope-restore the inner removal would
    // leak and MASK it (a missed conflict — unsound); the restore reinstates `x → p`. T255.
    let src = format!(
        "{PRELUDE}\
         fn f(n: i64) -> i64 ! {{ Alloc }} {{ \
             let p: Box = Box {{ v: 1 }}; \
             let x: Box = p; \
             if n > 0 {{ let x: Box = Box {{ v: 2 }}; let _u: i64 = x.v; }} else {{ let _z: i64 = 0; }} \
             let _r: i64 = sink(p, x); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn inner_block_alias_does_not_leak_a_spurious_conflict_is_clean() {
    // THE over-reject guard (the mirror). Outer `x` is a FRESH box (not aliasing `p`); an
    // inner-block `let x = p` adds an alias scoped to the `if`. After the block the outer
    // `x` is still the fresh box, so `sink(p, x)` is clean. Without scope-restore the inner
    // `x → p` would leak and SPURIOUSLY fire T255. Clean.
    let src = format!(
        "{PRELUDE}\
         fn f(n: i64) -> i64 ! {{ Alloc }} {{ \
             let p: Box = Box {{ v: 1 }}; \
             let x: Box = Box {{ v: 2 }}; \
             if n > 0 {{ let x: Box = p; let _u: i64 = x.v; }} else {{ let _z: i64 = 0; }} \
             let _r: i64 = sink(p, x); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn doubly_nested_shadow_is_restored_at_each_scope_t255() {
    // Restoration holds at depth > 1: a shadow inside an inner `if` is restored when
    // control returns to the OUTER `if`, where `x` still aliases `p`. The `sink(p, x)`
    // call sits in the outer-if scope, after the inner-if closes. T255.
    let src = format!(
        "{PRELUDE}\
         fn f(n: i64) -> i64 ! {{ Alloc }} {{ \
             let p: Box = Box {{ v: 1 }}; \
             let x: Box = p; \
             if n > 0 {{ \
                 if n > 1 {{ let x: Box = Box {{ v: 9 }}; let _u: i64 = x.v; }} else {{ let _z: i64 = 0; }} \
                 let _r2: i64 = sink(p, x); \
             }} else {{ let _z2: i64 = 0; }} \
             return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}
