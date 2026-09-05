//! A capability cannot EVADE the ring-boundary checks (R001/R002) by hiding
//! inside a `Type::Tuple` or `Type::Fn` aggregate — the ring-isolation
//! companion to the `cap_aggregate_smuggle` suite (which pins the T183/T184/
//! T186/T242 aggregate gates).
//!
//! `ring_check.rs` carries its OWN two cap-detection walkers, independent of
//! `type_contains_cap`:
//!   * `is_owned_cap`  guards R001 ("outer ring cannot own capabilities") on
//!     outer-ring fn params / return types and outer-body `let` bindings.
//!   * `contains_cap_ref` guards R002 ("capability references cannot escape
//!     outer-ring functions") on outer-ring fn return types.
//!
//! Both recursed through `Named`/`Array`/`Slice` but FELL THROUGH (`_ => false`)
//! for `Type::Tuple` and `Type::Fn` — so a cap (R001) or a `&cap` (R002)
//! wrapped in a tuple element or a closure param/return slipped past the
//! check that exists to quarantine it (bug-hunt F005; same walker-gap class as
//! the historical `type_contains_cap` Tuple/Fn miss). Fixed by adding the
//! `Tuple` and `Fn` arms to both walkers (params AND return for `Fn`), plus the
//! missing `Array` arm to `contains_cap_ref`.
//!
//! Each REJECT case asserts the EXACT ring code fires; each LEGIT case asserts
//! the program still compiles cleanly — a cap-free tuple param or `Fn(i64)->i64`
//! return, and a borrowed `&Fuel` param, must remain legal (no false positives,
//! or the fix would have weakened the language rather than strengthened the
//! check).

use sigil_compiler::compile_named_module;

/// An outer-ring module header + a cap type. R001/R002 only fire in the
/// OUTER ring, so every fixture body is spliced into an `#[ring(outer)]`
/// module.
const PRELUDE: &str = "#[ring(outer)]\nmodule ext;\ncap type Fuel {}\n";

/// Compile `PRELUDE + body`; return the sorted, de-duplicated emitted codes
/// (empty = compiled cleanly).
fn codes(body: &str) -> Vec<String> {
    match compile_named_module("ring_smuggle.sigil", format!("{PRELUDE}{body}")) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut cs: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            cs.sort();
            cs.dedup();
            cs
        }
    }
}

fn assert_rejects_with(body: &str, code: &str) {
    let cs = codes(body);
    assert!(
        cs.iter().any(|c| c == code),
        "expected {code} for `{body}`, got {cs:?}"
    );
}

fn assert_clean(body: &str) {
    let cs = codes(body);
    assert!(
        cs.is_empty(),
        "expected clean compile for `{body}`, got {cs:?}"
    );
}

// ── R001: owned cap smuggled through a TUPLE / Fn slot ──────────────────────

#[test]
fn owned_cap_in_tuple_param_is_r001() {
    // `is_owned_cap` must descend into the tuple element.
    assert_rejects_with("fn f(p: (Fuel, i64)) -> i64 { return 0; }\n", "R001");
}

#[test]
fn owned_cap_in_nested_tuple_param_is_r001() {
    assert_rejects_with("fn f(p: ((Fuel, i64), i64)) -> i64 { return 0; }\n", "R001");
}

#[test]
fn owned_cap_in_tuple_return_is_r001() {
    assert_rejects_with("fn f() -> (Fuel, i64) { return f(); }\n", "R001");
}

#[test]
fn owned_cap_in_fn_return_slot_is_r001() {
    // `Fn(i64) -> Fuel` — calling the returned closure yields a fresh owned
    // cap; the `Fn` arm must check the RETURN slot, not just params.
    assert_rejects_with("fn f() -> Fn(i64) -> Fuel { return f(); }\n", "R001");
}

#[test]
fn owned_cap_in_fn_param_slot_is_r001() {
    // `Fn(Fuel) -> i64` — cap in the closure PARAMETER position.
    assert_rejects_with("fn f() -> Fn(Fuel) -> i64 { return f(); }\n", "R001");
}

#[test]
fn owned_cap_in_tuple_let_binding_is_r001() {
    // The outer-body `let` walker shares `is_owned_cap`.
    assert_rejects_with(
        "fn f() -> i64 { let b: (Fuel, i64) = mk(); return 0; }\n\
         fn mk() -> (Fuel, i64) { return mk(); }\n",
        "R001",
    );
}

// ── R002: cap REFERENCE smuggled out through a TUPLE / Fn / Array slot ───────

#[test]
fn cap_ref_in_tuple_return_is_r002() {
    // The canonical F005 evasion: `-> (&Fuel, i64)` escapes a `&Fuel`.
    assert_rejects_with(
        "fn escape(g: &Fuel) -> (&Fuel, i64) { return (g, 0); }\n",
        "R002",
    );
}

#[test]
fn cap_ref_in_fn_return_slot_is_r002() {
    assert_rejects_with(
        "fn escape() -> Fn(i64) -> &Fuel { return escape(); }\n",
        "R002",
    );
}

#[test]
fn cap_ref_in_array_return_is_r002() {
    // `contains_cap_ref` was missing the `Array` arm entirely.
    assert_rejects_with(
        "fn escape(g: &Fuel) -> [&Fuel; 1] { return [g]; }\n",
        "R002",
    );
}

#[test]
fn bare_cap_ref_return_caught_by_t253() {
    // Baseline: the un-wrapped `-> &Fuel` escape is caught even EARLIER, by the
    // type-check rule T253, so it never reaches R002. Crucially T253 shares the
    // same blind spot — it does NOT look inside a tuple/Fn/array — which is why
    // R002's walker is the UNIQUE live defense for the aggregate-wrapped escapes
    // above. This pins that the bare case stays rejected (by T253).
    assert_rejects_with("fn escape(g: &Fuel) -> &Fuel { return g; }\n", "T253");
}

// ── LEGIT: cap-free aggregates & borrows must still compile ─────────────────

#[test]
fn cap_free_tuple_param_is_legal() {
    assert_clean("fn ok(x: (i64, i64)) -> i64 { return 0; }\n");
}

#[test]
fn cap_free_fn_return_is_legal() {
    // The closure-returning workhorse — must stay legal in the outer ring.
    assert_clean("fn ok() -> Fn(i64) -> i64 { return ok(); }\n");
}

#[test]
fn borrowed_cap_param_is_legal() {
    // A `&Fuel` PARAM is a borrow, not owned (R001 bans owned) and R002 only
    // bans cap-refs in the RETURN — so an outer fn borrowing a cap is fine.
    assert_clean("fn ok(f: &Fuel) -> i64 { return 0; }\n");
}

#[test]
fn cap_free_tuple_of_refs_return_is_legal() {
    // Tuple of plain i64s returned — no cap anywhere, no false R002.
    assert_clean("fn ok(x: i64) -> (i64, i64) { return (x, x); }\n");
}
