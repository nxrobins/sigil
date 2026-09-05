//! PR-1 of the mutation-as-capability epic — the `@ReadOnly` WRITE gate.
//!
//! NC-2: a write-THROUGH to a place rooted in a `@ReadOnly` parameter — a field
//! store, an index store, or ANY compound assignment — is rejected with T251.
//! The gate is op-agnostic (it reads the place, never the operator) and
//! fail-closed. NC-1 propagation: a `let b = p` makes `b` readonly too, so the
//! one-line `let b = p; b.x = 10` launder is caught. Reading a `@ReadOnly` value
//! (binding it, returning a field through it) is unaffected; a bare or `@Mut`
//! param is never gated (proving the gate engages on the annotation, not on all
//! stores).

use sigil_compiler::compile_tool;

/// Wrap `defs` in a module with a trivial `tool_main`, compile, and return the
/// diagnostic codes (empty = clean compile). Functions in `defs` are type-checked
/// even when unused, so the gate fires on a `fn f` body without a call site.
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

fn rejects_t251(defs: &str) -> bool {
    codes(defs).iter().any(|c| c == "T251")
}

/// PR-4: the non-blocking WARNING codes surfaced on a SUCCESSFUL compile (via
/// `CompileResult::warnings`). A program that errors returns `[]` here — a warning
/// test should also assert the program compiles clean (no error blocked it).
fn warning_codes(defs: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n{defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return 0 - 1; }}\n"
    );
    match compile_tool(&src) {
        Ok(result) => result
            .warnings
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
        Err(_) => Vec::new(),
    }
}

fn warns_t252(defs: &str) -> bool {
    warning_codes(defs).iter().any(|c| c == "T252")
}

fn compiles_clean(defs: &str) -> bool {
    codes(defs).is_empty()
}

const POINT: &str = "record Point { x: i64, y: i64 }\n";

// ── the WRITE gate: write-through to a @ReadOnly param → T251 ──────────────────

#[test]
fn field_store_through_readonly_is_t251() {
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ p.x = 10; return p.x; }}"
    )));
}

#[test]
fn compound_assignment_through_readonly_is_t251() {
    // NC-2: the gate is op-agnostic — `+=` is a write-through too.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ p.x += 1; return p.x; }}"
    )));
}

#[test]
fn index_store_through_readonly_is_t251() {
    assert!(rejects_t251(
        "fn f(a: [i64; 4] @ReadOnly) -> i64 { a[0] = 9; return 0; }"
    ));
}

#[test]
fn nested_field_store_through_readonly_is_t251() {
    // CM-1: `place_root_local` recurses to the root `o`, so a deep place doesn't
    // dodge the gate.
    let defs = "record Inner { v: i64 }\nrecord Outer { inner: Inner }\n\
        fn f(o: Outer @ReadOnly) -> i64 { o.inner.v = 5; return 0; }";
    assert!(rejects_t251(defs));
}

// ── NC-1 propagation: the local launder is caught ─────────────────────────────

#[test]
fn let_alias_launder_is_caught() {
    // The headline NC-1 fix: `let b = p` makes `b` readonly, so `b.x = 10` → T251.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ let b: Point = p; b.x = 10; return b.x; }}"
    )));
}

#[test]
fn two_hop_alias_launder_is_caught() {
    // Propagation is transitive across hops: p → b → c, then `c.x = 10` → T251.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ let b: Point = p; let c: Point = b; c.x = 10; return c.x; }}"
    )));
}

// ── positives: read / bind / return a field compiles clean ────────────────────

#[test]
fn reading_a_readonly_field_compiles() {
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ return p.x; }}"
    )));
}

#[test]
fn binding_and_reading_through_alias_compiles() {
    // `let b = p; return b.x` — reading through a readonly alias is fine.
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ let b: Point = p; return b.x; }}"
    )));
}

// ── negative controls: the gate engages on the annotation, not all stores ─────

#[test]
fn bare_param_field_store_is_t251() {
    // Since DEF-1, a bare param is FROZEN, so a field store through it is rejected
    // exactly like its `@ReadOnly` twin (`writing_a_field_through_readonly_is_t251`) —
    // bare ≡ `@ReadOnly` on the write gate. Mutation now requires `@Mut`.
    assert!(rejects_t251(&format!(
        "{POINT}fn f(p: Point) -> i64 {{ p.x = 10; return p.x; }}"
    )));
}

#[test]
fn mut_param_field_store_compiles() {
    // `@Mut` is explicitly mutable — a field store through it compiles (NC-4: @Mut
    // behaves like bare today).
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @Mut) -> i64 {{ p.x = 10; return p.x; }}"
    )));
}

// ── PR-2: the RETURN escape gate (T253) ───────────────────────────────────────

fn rejects_t253(defs: &str) -> bool {
    codes(defs).iter().any(|c| c == "T253")
}

#[test]
fn returning_a_readonly_alias_is_t253() {
    // The headline return-launder: `fn thaw(p @ReadOnly) -> Point { return p; }`
    // would hand the caller a mutable Point aliasing the readonly one.
    assert!(rejects_t253(&format!(
        "{POINT}fn thaw(p: Point @ReadOnly) -> Point {{ return p; }}"
    )));
}

#[test]
fn returning_a_propagated_alias_is_t253() {
    // Propagation reaches the return sink: `let b = p; return b`.
    assert!(rejects_t253(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> Point {{ let b: Point = p; return b; }}"
    )));
}

#[test]
fn returning_a_heap_field_alias_is_t253() {
    // A heap-typed field aliases the readonly object too (is_aliasable record).
    let defs = "record Inner { v: i64 }\nrecord Outer { inner: Inner }\n\
        fn f(o: Outer @ReadOnly) -> Inner { return o.inner; }";
    assert!(rejects_t253(defs));
}

#[test]
fn returning_a_primitive_field_copy_compiles() {
    // The critical positive: `return p.x` (an i64 COPY) is NOT an escape — getters
    // through a readonly value stay legal (`is_aliasable_type` excludes scalars).
    assert!(compiles_clean(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ return p.x; }}"
    )));
}

// ── PR-2b: the call-ARGUMENT escape gate — THE chokepoint (T253) ──────────────
//
// A value rooted in a `@ReadOnly` param, passed into a NON-`@ReadOnly`
// parameter, re-widens authority (the callee gets a mutable handle). NC-3: free
// and cross-module calls all route argument binding through one gate in
// `infer_call_expr`. Allowed (H6): mutable→`@ReadOnly` (freeze on entry) and
// readonly→readonly. A primitive-copy argument is never an escape.

#[test]
fn passing_readonly_to_mutable_param_is_t253() {
    // The canonical re-widen launder: `g` takes a `@Mut` Point, so passing a
    // `@ReadOnly` value into it would let `g` mutate the frozen object. (`@Mut`,
    // not bare, so the escape stays pinned across the DEF-1 default-frozen flip.)
    assert!(rejects_t253(&format!(
        "{POINT}fn g(v: Point @Mut) -> i64 {{ return v.x; }}\n\
         fn f(p: Point @ReadOnly) -> i64 {{ return g(p); }}"
    )));
}

#[test]
fn passing_propagated_alias_to_mutable_param_is_t253() {
    // NC-1: the let-bound alias `b` inherits readonly, so `g(b)` is the same escape.
    assert!(rejects_t253(&format!(
        "{POINT}fn g(v: Point @Mut) -> i64 {{ return v.x; }}\n\
         fn f(p: Point @ReadOnly) -> i64 {{ let b: Point = p; return g(b); }}"
    )));
}

#[test]
fn passing_readonly_to_readonly_param_compiles() {
    // readonly → readonly: authority is preserved, so the call is legal.
    assert!(compiles_clean(&format!(
        "{POINT}fn h(v: Point @ReadOnly) -> i64 {{ return v.x; }}\n\
         fn f(p: Point @ReadOnly) -> i64 {{ return h(p); }}"
    )));
}

#[test]
fn freezing_a_mutable_argument_on_entry_compiles() {
    // mutable → readonly (freeze on entry) is attenuation (H6), always allowed.
    assert!(compiles_clean(&format!(
        "{POINT}fn h(v: Point @ReadOnly) -> i64 {{ return v.x; }}\n\
         fn k(p: Point) -> i64 {{ return h(p); }}"
    )));
}

#[test]
fn passing_a_primitive_field_copy_as_argument_compiles() {
    // `g(p.x)` passes an i64 COPY — not an alias, so no authority escapes.
    assert!(compiles_clean(&format!(
        "{POINT}fn g(n: i64) -> i64 {{ return n; }}\n\
         fn f(p: Point @ReadOnly) -> i64 {{ return g(p.x); }}"
    )));
}

#[test]
fn passing_a_bare_value_to_a_mutable_param_compiles() {
    // The gate engages on the @ReadOnly annotation, not on all aliasing args:
    // a bare value flowing into a bare param is the ordinary mutable case.
    assert!(compiles_clean(&format!(
        "{POINT}fn g(v: Point) -> i64 {{ return v.x; }}\n\
         fn f(p: Point) -> i64 {{ return g(p); }}"
    )));
}

#[test]
fn readonly_enforced_in_generic_function_body() {
    // PR-2b mono-gap close: every `check_function_block` re-entry (incl. the
    // generic-monomorph path) now seeds `@ReadOnly` from the def's params, so a
    // generic fn enforces the gate in its body — `return x` aliases the readonly
    // param out of the (monomorphized-at-Point) function.
    assert!(rejects_t253(&format!(
        "{POINT}fn idret<T>(x: T @ReadOnly) -> T {{ return x; }}\n\
         fn caller(p: Point) -> Point {{ return idret(p); }}"
    )));
}

// ── PR-2c: the record-construct + assignment-RHS escape sinks (T253) ──────────
//
// Two more members of NC-1's closed sink-set. (a) record-construct: storing a
// readonly-rooted aliasable value into a (mutable) record field is the
// "record-wrap launder". (b) assignment-RHS: storing such a value into a place
// whose root is NOT readonly creates a mutable alias of the frozen object. Both
// reject with T253; primitive-copy and bare-value cases stay legal.

const WRAP: &str = "record Wrap { inner: Point }\n";
const BOXI: &str = "record Boxi { n: i64 }\n";

#[test]
fn record_wrap_launder_is_t253() {
    // `Wrap { inner: p }` aliases the readonly p into a fresh mutable record, from
    // which `r.inner.x = 10` could mutate it — the record-wrap launder.
    assert!(rejects_t253(&format!(
        "{POINT}{WRAP}fn f(p: Point @ReadOnly) -> i64 {{ let r: Wrap = Wrap {{ inner: p }}; return 0; }}"
    )));
}

#[test]
fn record_wrap_of_propagated_alias_is_t253() {
    // NC-1: the let-propagated alias `b` is readonly too, so wrapping it launders.
    assert!(rejects_t253(&format!(
        "{POINT}{WRAP}fn f(p: Point @ReadOnly) -> i64 {{ let b: Point = p; let r: Wrap = Wrap {{ inner: b }}; return 0; }}"
    )));
}

#[test]
fn record_wrap_of_primitive_field_compiles() {
    // `Boxi { n: p.x }` stores an i64 COPY — no alias escapes.
    assert!(compiles_clean(&format!(
        "{POINT}{BOXI}fn f(p: Point @ReadOnly) -> i64 {{ let r: Boxi = Boxi {{ n: p.x }}; return r.n; }}"
    )));
}

#[test]
fn record_wrap_of_bare_value_is_t253() {
    // Since DEF-1 a bare param is frozen, so wrapping it into a (mutable) record field is
    // the record-wrap launder → T253, exactly like its `@ReadOnly` twin
    // (`record_wrap_launder_is_t253`). bare ≡ `@ReadOnly` on the escape gate.
    assert!(rejects_t253(&format!(
        "{POINT}{WRAP}fn f(p: Point) -> i64 {{ let r: Wrap = Wrap {{ inner: p }}; return 0; }}"
    )));
}

#[test]
fn aliasing_readonly_into_mutable_field_is_t253() {
    // `q.inner = p` stores the readonly alias into a mutable field — escape.
    assert!(rejects_t253(&format!(
        "{POINT}{WRAP}fn f(p: Point @ReadOnly, q: Wrap @Mut) -> i64 {{ q.inner = p; return 0; }}"
    )));
}

#[test]
fn aliasing_readonly_into_mutable_local_is_t253() {
    // `q = p` re-points a mutable local to the frozen object. Reassignment is NOT a
    // propagate site (only `let` is), so it is an escape, not an inheritance.
    assert!(rejects_t253(&format!(
        "{POINT}fn f(p: Point @ReadOnly) -> i64 {{ let mut q: Point = Point {{ x: 1, y: 2 }}; q = p; return 0; }}"
    )));
}

#[test]
fn assigning_a_primitive_copy_into_a_mutable_field_compiles() {
    // `b.n = p.x` stores an i64 COPY — no alias, so no escape.
    assert!(compiles_clean(&format!(
        "{POINT}{BOXI}fn f(p: Point @ReadOnly, b: Boxi @Mut) -> i64 {{ b.n = p.x; return 0; }}"
    )));
}

// ── PR-3: method receivers + the stdlib read surface (T253) ───────────────────
//
// The LAST sink: a method call binds the receiver to the method's `self`. A
// plain-`self` MUTATOR called on a @ReadOnly receiver — or a readonly value
// passed into a mutable method/associated-fn arg — re-widens authority (T253).
// Read methods declare `@ReadOnly self`, so reading through a frozen collection
// stays legal. Vec/Map are ambiently injected by the `Vec<` / `Map<` triggers.

#[test]
fn pushing_to_a_readonly_vec_is_t253() {
    // `push` keeps a plain `self` (it mutates the shared header), so a frozen vec
    // cannot be pushed. (`! { Alloc }` keeps the only diagnostic the T253.)
    assert!(rejects_t253(
        "fn f(v: Vec<i64> @ReadOnly) -> i64 ! { Alloc } { return v.push(1); }"
    ));
}

#[test]
fn setting_a_readonly_vec_is_t253() {
    assert!(rejects_t253(
        "fn f(v: Vec<i64> @ReadOnly) -> i64 { return v.set(0, 9); }"
    ));
}

#[test]
fn reading_a_readonly_vec_compiles() {
    // `get` and `len` carry `@ReadOnly self`, so reads through a frozen vec are
    // legal (readonly receiver → readonly self).
    assert!(compiles_clean(
        "fn f(v: Vec<i64> @ReadOnly) -> i64 { let n: i64 = v.len(); return v.get(0); }"
    ));
}

#[test]
fn inserting_into_a_readonly_map_is_t253() {
    assert!(rejects_t253(
        "fn f(m: Map<str, i64> @ReadOnly) -> i64 ! { Alloc } { return m.insert(\"a\", 1); }"
    ));
}

#[test]
fn reading_a_readonly_map_compiles() {
    // `len` / `contains` / `get` all carry `@ReadOnly self` — and so do the
    // internal helpers (`find_slot`, `key_eq`) they call on `self`'s Vec fields.
    assert!(compiles_clean(
        "fn f(m: Map<str, i64> @ReadOnly) -> i64 { let b: bool = m.contains(\"a\"); let o: Option<i64> = m.get(\"a\"); return m.len(); }"
    ));
}

// ── PR-4: the T252 honesty lint on @ReadOnly reference/view params ────────────
//
// `@ReadOnly` on an aliasable reference/view (`&T` / `&[T]`) emits T252 — a
// non-blocking WARNING (SIGIL's first), surfaced via CompileResult.warnings. The
// program still compiles. By-value heap params (AG-11) are NOT linted.

#[test]
fn readonly_slice_param_warns_t252() {
    let defs = "fn f(s: &[i64] @ReadOnly) -> i64 { return 0; }";
    assert!(
        warns_t252(defs),
        "expected T252; warnings = {:?}",
        warning_codes(defs)
    );
    // The warning must NOT block compilation.
    assert!(
        compiles_clean(defs),
        "T252 is a warning, not an error — the program must still compile clean (no error codes)"
    );
}

#[test]
fn readonly_by_value_record_param_does_not_warn() {
    // AG-11: a by-value heap param (`Point`, `ref_kind == None`) carries the same
    // partial guarantee but is NOT per-site linted — no T252.
    let defs = format!("{POINT}fn f(p: Point @ReadOnly) -> i64 {{ return p.x; }}");
    assert!(!warns_t252(&defs));
    assert!(compiles_clean(&defs));
}

#[test]
fn bare_slice_param_does_not_warn() {
    // The lint engages on the @ReadOnly annotation, not on all reference params.
    assert!(!warns_t252("fn f(s: &[i64]) -> i64 { return 0; }"));
}

#[test]
fn mutating_a_bare_vec_is_t253() {
    // Since DEF-1 a bare `Vec` param is frozen, so calling the `@Mut self` mutator
    // `push` on it re-widens authority → T253. Mutation through a Vec param now needs
    // `@Mut` (the receiver-allowlisted read methods like `get`/`len` stay legal).
    assert!(rejects_t253(
        "fn f(v: Vec<i64>) -> i64 ! { Alloc } { return v.push(1); }"
    ));
}

const PT_IMPL: &str = "record Pt { x: i64, y: i64 }\n\
     impl Pt {\n\
         fn bump(self: Pt @Mut) -> i64 { self.x = self.x + 1; return self.x; }\n\
         fn read(self: Pt @ReadOnly) -> i64 { return self.x; }\n\
     }\n";

#[test]
fn calling_a_plain_self_user_method_on_readonly_is_t253() {
    // `bump` is a `@Mut self` mutator (its body writes `self.x`), so calling it on
    // a @ReadOnly receiver re-widens authority — the user-defined-method gate.
    assert!(rejects_t253(&format!(
        "{PT_IMPL}fn f(p: Pt @ReadOnly) -> i64 {{ return p.bump(); }}"
    )));
}

#[test]
fn calling_a_readonly_self_user_method_on_readonly_compiles() {
    // `read` declares `@ReadOnly self` — reading through the frozen receiver is fine.
    assert!(compiles_clean(&format!(
        "{PT_IMPL}fn f(p: Pt @ReadOnly) -> i64 {{ return p.read(); }}"
    )));
}

#[test]
fn passing_readonly_as_a_method_arg_is_t253() {
    // The method-ARG case (not the receiver): `q.store(p)` — the receiver `q` is
    // mutable (fine), but `store`'s `other` parameter is mutable and aliasable, so
    // passing the @ReadOnly `p` into it escapes. typed_args[1] aligns param[1].
    let defs = "record Pt { x: i64, y: i64 }\n\
         impl Pt {\n\
             fn store(self: Pt, other: Pt @Mut) -> i64 { return other.x; }\n\
         }\n";
    assert!(rejects_t253(&format!(
        "{defs}fn f(p: Pt @ReadOnly, q: Pt) -> i64 {{ return q.store(p); }}"
    )));
}
