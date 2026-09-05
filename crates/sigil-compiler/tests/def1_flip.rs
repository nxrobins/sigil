//! DEF-1 — the default-frozen flip proof suite (`bare ⇒ frozen`).
//!
//! Since the one-line `is_frozen` change (`matches!(self, ReadOnly | Default)`), a BARE
//! heap parameter is FROZEN — it carries exactly the callee-side promise `@ReadOnly` makes:
//! no mutation through it (T251), no leak to a mutable sink (T253), no co-alias with a `@Mut`
//! argument in one call (T255). `@Mut` is the explicit opt-up. Every gate auto-extended
//! through that single predicate, so this suite is the canonical statement of what the flip
//! means — and the cleanest proof of it is that the bare shapes assert the SAME diagnostics
//! as their `@ReadOnly` twins (the `readonly_compile` suite written with the annotation
//! removed): **bare ≡ `@ReadOnly` on every gate**.

use sigil_compiler::compile_tool;

/// Wrap `defs` in a `tool` module with a trivial `tool_main`, compile, return the codes
/// (empty = clean). Functions in `defs` are type-checked even when uncalled.
fn codes(defs: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n{defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return 0 - 1; }}\n"
    );
    match compile_tool(&src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn rejects(defs: &str, code: &str) -> bool {
    codes(defs).iter().any(|c| c == code)
}

fn compiles_clean(defs: &str) -> bool {
    codes(defs).is_empty()
}

const POINT: &str = "record Point { x: i64, y: i64 }\n";
const WRAP: &str = "record Wrap { inner: Point }\n";

// ── 1-2. WRITE gate (T251): a write THROUGH a bare frozen param ────────────────────

#[test]
fn bare_heap_param_field_store_is_t251() {
    // The headline: a bare record param is frozen, so a field store through it is rejected.
    assert!(rejects(
        &format!("{POINT}fn f(p: Point) -> i64 {{ p.x = 10; return p.x; }}"),
        "T251"
    ));
}

#[test]
fn bare_heap_param_index_store_is_t251() {
    // An index store through a bare array param is the same write-through → T251.
    assert!(rejects(
        "fn f(a: [i64; 4]) -> i64 { a[0] = 9; return a[0]; }",
        "T251"
    ));
}

// ── 3. ESCAPE gate (T253): a bare frozen param reaching a MUTABLE sink ──────────────

#[test]
fn bare_heap_param_into_mut_arg_is_t253() {
    // Passing a bare (frozen) value into a `@Mut` parameter re-widens authority → T253.
    assert!(rejects(
        &format!(
            "{POINT}fn sink(v: Point @Mut) -> i64 {{ return v.x; }}\n\
             fn f(p: Point) -> i64 {{ return sink(p); }}"
        ),
        "T253"
    ));
}

#[test]
fn bare_heap_param_returned_is_t253() {
    // Returning a bare (frozen) param hands the caller a mutable handle to it → T253.
    assert!(rejects(
        &format!("{POINT}fn f(p: Point) -> Point {{ return p; }}"),
        "T253"
    ));
}

#[test]
fn bare_heap_param_into_record_field_is_t253() {
    // Wrapping a bare (frozen) param into a mutable record field is the record-wrap launder.
    assert!(rejects(
        &format!(
            "{POINT}{WRAP}fn f(p: Point) -> i64 {{ let r: Wrap = Wrap {{ inner: p }}; return 0; }}"
        ),
        "T253"
    ));
}

#[test]
fn push_on_bare_vec_receiver_is_t253() {
    // Calling the `@Mut self` mutator `push` on a bare (frozen) Vec receiver → T253.
    assert!(rejects(
        "fn f(v: Vec<i64>) -> i64 ! { Alloc } { return v.push(1); }",
        "T253"
    ));
}

// ── 3b. The CLEAN attenuation control (NC-D2): bare → bare is fine ──────────────────

#[test]
fn bare_heap_param_into_bare_arg_is_clean() {
    // The corrected UP-2 case: both params are bare ⇒ both frozen, so passing one into the
    // other is frozen→frozen ATTENUATION — clean, NOT T253. (The escape needs a `@Mut` sink.)
    assert!(compiles_clean(&format!(
        "{POINT}fn reader(v: Point) -> i64 {{ return v.x; }}\n\
         fn f(p: Point) -> i64 {{ return reader(p); }}"
    )));
}

// ── 7. EXCLUSIVITY gate (T255): a bare frozen param + a @Mut arg aliasing one object ─

#[test]
fn bare_frozen_plus_mut_alias_is_t255() {
    // A bare (frozen) `a` and a `@Mut` `b` receiving the SAME object in one call → T255.
    // Pre-flip `a` was mutable and this was clean; the flip made `a` frozen.
    assert!(rejects(
        &format!(
            "{POINT}fn sink(a: Point, b: Point @Mut) -> i64 {{ return 0; }}\n\
             fn f() -> i64 ! {{ Alloc }} {{ let p: Point = Point {{ x: 1, y: 2 }}; \
                 return sink(p, p); }}"
        ),
        "T255"
    ));
}

// ── 8. The `@Mut` opt-up: the escape hatch still works ──────────────────────────────

#[test]
fn mut_opt_up_field_store_compiles() {
    // `@Mut` is the explicit-mutable opt-up — a field store through it compiles.
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @Mut) -> i64 {{ p.x = 10; return p.x; }}"
    )));
}

#[test]
fn mut_opt_up_survives_let_propagation() {
    // MI-2: `@Mut` survives `let`-aliasing — `let b = m` with `@Mut m` leaves `b` mutable
    // (readonly propagation flows only FROM frozen roots, never from a `@Mut` one), so
    // pushing through `b` compiles. The opt-up is not silently re-frozen by an alias.
    assert!(compiles_clean(
        "fn f(m: Vec<i64> @Mut) -> i64 ! { Alloc } { let b: Vec<i64> = m; return b.push(1); }"
    ));
}

// ── 9-10. The inert / read cases: the flip does NOT over-reject ─────────────────────

#[test]
fn bare_scalar_param_is_inert() {
    // A bare scalar param is inert under the flip: scalars are copied, never aliased, so
    // reading / arithmetic / passing one is always clean (a scalar can't root a place).
    assert!(compiles_clean(&format!(
        "{POINT}fn g(n: i64) -> i64 {{ return n; }}\n\
         fn f(n: i64) -> i64 {{ let m: i64 = n + 1; return g(m); }}"
    )));
}

#[test]
fn reading_through_a_bare_param_compiles() {
    // Reading through a bare (frozen) param is fine: a field READ returns an i64 COPY, and
    // the receiver-allowlisted `Vec` read surface (`get`/`len`) carries `@ReadOnly self`.
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point) -> i64 {{ return p.x; }}\n\
         fn g(v: Vec<i64>) -> i64 {{ return v.len(); }}"
    )));
}

// ── 12. The new trait-method contract ───────────────────────────────────────────────

#[test]
fn user_trait_impl_writing_self_is_t251() {
    // Pins the new contract for user `impl` methods: a bare `self` is frozen, so a `hash`
    // impl that writes `self.x` is rejected (T251) — it must declare `@Mut self` to mutate.
    assert!(rejects(
        "record R { x: i64 }\n\
         impl R { fn hash(self: R) -> i64 { self.x = 5; return self.x; } }",
        "T251"
    ));
}

// ── 13. bare ≡ @ReadOnly: the monotonicity / equivalence canary (NC-D4) ─────────────

#[test]
fn bare_is_equivalent_to_readonly_on_every_gate() {
    // The soundness statement in one test: for each gate, the bare shape and its explicit
    // `@ReadOnly` twin emit the SAME diagnostic. The flip made `Default` join `ReadOnly`
    // under `is_frozen`, so every `@ReadOnly` rejection now holds for its bare twin — the
    // rejection set only grew, by exactly the bare params (NC-D4 monotonicity).
    let pairs = [
        // (write gate T251) field store
        (
            format!("{POINT}fn f(p: Point @ReadOnly) -> i64 {{ p.x = 1; return 0; }}"),
            format!("{POINT}fn f(p: Point) -> i64 {{ p.x = 1; return 0; }}"),
            "T251",
        ),
        // (escape gate T253) return
        (
            format!("{POINT}fn f(p: Point @ReadOnly) -> Point {{ return p; }}"),
            format!("{POINT}fn f(p: Point) -> Point {{ return p; }}"),
            "T253",
        ),
        // (escape gate T253) record-wrap
        (
            format!(
                "{POINT}{WRAP}fn f(p: Point @ReadOnly) -> i64 {{ let r: Wrap = Wrap {{ inner: p }}; return 0; }}"
            ),
            format!(
                "{POINT}{WRAP}fn f(p: Point) -> i64 {{ let r: Wrap = Wrap {{ inner: p }}; return 0; }}"
            ),
            "T253",
        ),
    ];
    for (readonly_src, bare_src, code) in pairs {
        assert!(
            rejects(&readonly_src, code),
            "@ReadOnly twin must reject with {code}: {:?}",
            codes(&readonly_src)
        );
        assert!(
            rejects(&bare_src, code),
            "bare ≡ @ReadOnly — bare must ALSO reject with {code} post-flip: {:?}",
            codes(&bare_src)
        );
    }
}
