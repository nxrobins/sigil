//! DEF-2c PR-1 — the call-site exclusivity gate (the AG-1 closure).
//!
//! A single call may not hand the SAME heap object to a FROZEN (`@ReadOnly`) parameter and a
//! MUTABLE (`@Mut`/bare) parameter: the mutable handle could mutate the object while the
//! callee holds it frozen, breaking the read-only view mid-execution (Rust's shared-XOR-
//! mutable property). This is the reachable core of AG-1 in SIGIL's single-threaded model.
//! Detected via `exclusivity_partition` over the resolved call signature + the `alias_origin`
//! map, emitted as **T255**.
//!
//! Soundness subtleties pinned here: frozen-ness is the PARAMETER's (a bare mutable local
//! passed to a `@ReadOnly` param is frozen on entry); a `let`-launder (`let y = x; f(x, y)`)
//! resolves back to its root; overlap is alias-resolved ROOT equality (same-root field paths
//! conservatively overlap, AG-2c-9); scalars and un-rooted args are inert.

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

// A `Box` record (heap, aliasable). `store` reads `a` frozen and may mutate `b`.
const PRELUDE: &str = "module tool;\n\
     record Box { v: i64 }\n\
     fn store(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }\n";

const TOOL_MAIN: &str =
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0; }\n";

// ── the conflict: one object to a frozen AND a mutable parameter → T255 ───────────

#[test]
fn same_place_to_frozen_and_mutable_is_t255() {
    // The canonical AG-1 case: `store(p, p)` passes one object as the frozen `a` and the
    // mutable `b`; mutating `b` would change `a` under the reader. T255.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; \
             let _x: i64 = store(p, p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn let_laundered_alias_to_frozen_and_mutable_is_t255() {
    // The launder defence: `let y = x` makes `y` alias `x`; `store(x, y)` then passes one
    // object to the frozen and the mutable param under DIFFERENT names. `alias_origin`
    // resolves `y → x`, so the overlap is caught. T255.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ let x: Box = Box {{ v: 1 }}; let y: Box = x; \
             let _z: i64 = store(x, y); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn mutable_parameter_first_still_conflicts() {
    // Order-independence (NC-2c-5): when the MUTABLE parameter comes first
    // (`store_rev(a @Mut, b @ReadOnly)`), an aliasing pair still fires. T255.
    let src = format!(
        "{PRELUDE}\
         fn store_rev(a: Box @Mut, b: Box @ReadOnly) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; \
             let _x: i64 = store_rev(p, p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn same_root_field_overlap_is_t255() {
    // Conservative over-rejection (AG-2c-9): a frozen whole `w` and a mutable field `w.inner`
    // share the root `w`, so they conservatively overlap (a field store could alias) → T255.
    let src = format!(
        "{PRELUDE}\
         record Wrap {{ inner: Box }}\n\
         fn fstore(a: Wrap @ReadOnly, b: Box @Mut) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ let w: Wrap = Wrap {{ inner: Box {{ v: 1 }} }}; \
             let _x: i64 = fstore(w, w.inner); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

// ── the non-conflicts: clean (compile to WASM) ────────────────────────────────────

#[test]
fn distinct_objects_to_frozen_and_mutable_is_clean() {
    // Two DIFFERENT objects (distinct roots) — no overlap, no conflict. Clean.
    let src = format!(
        "{PRELUDE}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; let q: Box = Box {{ v: 2 }}; \
             let _x: i64 = store(p, q); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn same_object_to_two_frozen_readers_is_clean() {
    // Two FROZEN readers of one object is fine — no mutation, no broken view. Clean.
    let src = format!(
        "{PRELUDE}\
         fn read2(a: Box @ReadOnly, b: Box @ReadOnly) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; \
             let _x: i64 = read2(p, p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn same_object_to_two_mutables_is_clean() {
    // Two MUTABLE handles to one object — no FROZEN view to break, so DEF-2c does not fire
    // (the shared-XOR-mutable conflict is frozen-vs-mutable, not mutable-vs-mutable). Clean.
    let src = format!(
        "{PRELUDE}\
         fn mut2(a: Box @Mut, b: Box @Mut) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Box = Box {{ v: 1 }}; \
             let _x: i64 = mut2(p, p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn scalar_co_arguments_are_inert() {
    // Scalars are COPIED, not aliased — passing one scalar to a frozen and a mutable scalar
    // parameter cannot create an alias, so the gate never fires (`is_aliasable_type` skips
    // them, NC-2c-6). Clean.
    let src = format!(
        "{PRELUDE}\
         fn scalars(a: i64 @ReadOnly, b: i64 @Mut) -> i64 {{ return 0; }}\n\
         fn f() -> i64 {{ let n: i64 = 5; let _x: i64 = scalars(n, n); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// ── PR-2: the method/receiver gate (receiver is `typed_args[0]`, self at param 0) ──

// A `Pt` record with methods spanning the frozen/mutable-self axis, plus a no-`self`
// associated constructor. `rstore` reads `self` frozen and may mutate `other`;
// `mstore` is the mutable-receiver reverse; `read2` is two frozen views; `readn`
// takes a scalar co-arg; `make` is the associated-fn (no receiver) frozen+mutable pair.
const PT: &str = "module tool;\n\
     record Pt { x: i64 }\n\
     impl Pt {\n\
         fn rstore(self: Pt @ReadOnly, other: Pt @Mut) -> i64 { return other.x; }\n\
         fn mstore(self: Pt @Mut, other: Pt @ReadOnly) -> i64 { return other.x; }\n\
         fn read2(self: Pt @ReadOnly, other: Pt @ReadOnly) -> i64 { return other.x; }\n\
         fn readn(self: Pt @ReadOnly, n: i64) -> i64 { return n; }\n\
         fn make(a: Pt @ReadOnly, b: Pt) -> i64 { return a.x; }\n\
     }\n";

#[test]
fn method_frozen_receiver_mutable_arg_same_object_is_t255() {
    // The receiver participates at index 0: `p.rstore(p)` hands `p` to the FROZEN
    // `self` (param 0) and the MUTABLE `other` (param 1) — mutating `other` would
    // change the frozen receiver under its own read. T255.
    let src = format!(
        "{PT}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Pt = Pt {{ x: 1 }}; \
             let _r: i64 = p.rstore(p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn method_mutable_receiver_frozen_arg_same_object_is_t255() {
    // The receiver-mutable reverse (NC-2c-5): `p.mstore(p)` hands `p` to the MUTABLE
    // `self` (param 0) and the FROZEN `other` (param 1). Still a conflict. T255.
    let src = format!(
        "{PT}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Pt = Pt {{ x: 1 }}; \
             let _r: i64 = p.mstore(p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn method_laundered_receiver_arg_is_t255() {
    // The launder through a method: `let y = p; p.rstore(y)` passes `p` (frozen self)
    // and its alias `y` (mutable other); `alias_origin` resolves `y → p`. T255.
    let src = format!(
        "{PT}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Pt = Pt {{ x: 1 }}; let y: Pt = p; \
             let _r: i64 = p.rstore(y); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn method_distinct_receiver_and_arg_is_clean() {
    // Different receiver and argument objects — no overlap. Clean.
    let src = format!(
        "{PT}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Pt = Pt {{ x: 1 }}; let q: Pt = Pt {{ x: 2 }}; \
             let _r: i64 = p.rstore(q); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn method_two_frozen_views_is_clean() {
    // Receiver and arg both reach FROZEN params (`read2`): two readers of one object,
    // no mutation, no broken view. Clean — proves the gate keys on frozen×MUTABLE.
    let src = format!(
        "{PT}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Pt = Pt {{ x: 1 }}; \
             let _r: i64 = p.read2(p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn method_read_with_scalar_arg_is_clean() {
    // The `v.get(i)`-shaped case: a read through a frozen receiver with an unrelated
    // SCALAR co-arg (`readn`) — the scalar is not aliasable, so no overlap. Clean.
    let src = format!(
        "{PT}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: Pt = Pt {{ x: 1 }}; \
             let _r: i64 = p.readn(5); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

// The associated-fn sink is reachable only for a GENERIC impl (`infer_associated_fn_call`;
// non-generic impl methods are not registered for dispatch-time mono). A generic `W<T>`
// with a no-`self` `make(a: W<T> @ReadOnly, b: W<T>)` exercises it — `make` mentions `T` so
// the type param binds from the args (an all-concrete signature would be T150 "can't infer").
const GENERIC_W: &str = "module tool;\n\
     record W<T> { v: T }\n\
     impl W<T> {\n\
         fn make(a: W<T> @ReadOnly, b: W<T> @Mut) -> i64 { return 0; }\n\
     }\n";

#[test]
fn associated_fn_frozen_and_mutable_same_object_is_t255() {
    // The associated-fn (no-`self`) sink, in the closed surface per NC-2c-1: a user
    // constructor `W::make(a @ReadOnly, b)` called `W::make(p, p)` hands one object to
    // a frozen and a mutable parameter. A conflict the call itself creates (no
    // pre-existing readonly local), so — unlike the T253 escape gate, which is absent
    // on this path — DEF-2c fires here. T255.
    let src = format!(
        "{GENERIC_W}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: W<i64> = W {{ v: 1 }}; \
             let _r: i64 = W::make(p, p); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(has(&src, "T255"), "got {:?}", codes(&src));
}

#[test]
fn associated_fn_distinct_objects_is_clean() {
    // Distinct objects into the same constructor — no overlap. Clean.
    let src = format!(
        "{GENERIC_W}\
         fn f() -> i64 ! {{ Alloc }} {{ let p: W<i64> = W {{ v: 1 }}; let q: W<i64> = W {{ v: 2 }}; \
             let _r: i64 = W::make(p, q); return 0; }}\n\
         {TOOL_MAIN}"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}
