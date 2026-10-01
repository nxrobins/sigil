//! The inner-ring effect-check exemption, pinned together with the fences that make it safe.
//!
//! `effect_check::check_effects` skips every module whose ring is `Inner` — and `Inner` is the
//! DEFAULT ring when no `#[ring]` attribute is written. So in an inner-ring module an undeclared
//! effect reaching a call, an `alloc` under an empty row, an effectful closure applied under an
//! empty row, and a `handle Unsafe` all compile clean, while byte-identical programs under
//! `#[ring(outer)]` reject with E001 / E001 / E001 / E002. That is a documented design decision
//! (effect_check.rs module doc; selfhost ET-EFF-5; SND-EFFECT-001), not a defect — but the reason
//! is narrower than "inner-ring code performs no effects". `alloc` IS an inner-ring primitive that
//! performs the registered `Alloc` effect; the probe below pins its exemption directly. The
//! defensible statement is that no inner-ring primitive performs an effect REACHING THE HOST.
//!
//! SCOPE of the exemption probes: the first two sections below are NON-GENERIC, and every
//! statement in them is about non-generic code. For non-generic code the exemption is confined to
//! the inner ring (an outer-ring fn placed AFTER an inner-ring module still fires E001; pinned
//! below). Two host-boundary fences carry the safety weight, and a third, weaker fence is pinned
//! beside them so its limits are not mistaken for coverage:
//!
//! * R003 — inner-ring code cannot call an `extern` (the host-effect primitive). LOAD-BEARING.
//! * R004 — inner-ring code cannot call an outer-ring wrapper directly (only `grant` crosses).
//!   LOAD-BEARING.
//! * E003 — an inner-ring free fn cannot NAME `FFI` / `Unsafe` in a declared row. NOT
//!   load-bearing: it does nothing about a `handle Unsafe` block in a row-less inner-ring fn
//!   (pinned clean below), and its validator walks free `FnDef` items only, so an inner-ring
//!   impl method may declare `Unsafe` outright.
//!
//! What the exemption costs: an inner-ring `alloc` is never charged to a declared row, so `Alloc`
//! in an inner-ring row is documentation rather than an enforced obligation; any bound on
//! inner-ring allocation is the runtime's, not this gate's.
//!
//! E001 HAS A SECOND EMITTER, AND IT IS RING-BLIND. The exemption above is a property of
//! `effect_check::check_effects` alone. `bind_and_check_effect_rows`
//! (`type_check/expressions/calls.rs`) also raises E001, from the TYPE-CHECK pass, which takes no
//! ring at all: it enforces row contravariance (`actual ⊆ concrete(formal) ∪ binding(row var)`) on
//! every Fn-typed formal of a GENERIC callee, because the generic call path has no
//! `type_compatible` argument loop to do it. The last section of this file pins that emitter and
//! its controls: an effectful closure passed to a generic callee's concrete `! { }` formal is
//! exactly {E001} in the inner ring, the outer ring and an explicit `#[ring(inner)]` alike, and
//! it is NOT the monomorph-routing path below — it still fires when every module in the program
//! is inner-ring, where routing to `modules[0]` would skip the effect check outright. A `handle`
//! at the call site does not silence it, and the non-generic twin is a type error (T071), never
//! E001. So no "E001 fires in ring X only" sentence is true of the code as a whole; the
//! ring-confinement statements in this file are about the effect checker's emitter.
//!
//! Generic code, owned elsewhere: monomorphized generic instances are FILED under `modules[0]`
//! regardless of their defining module. Before the governing-meet fix (p2b/routing, which owns
//! `effect_ring_routing.rs`) they were also CHECKED there, so with an inner-ring first module an
//! OUTER-ring generic escaped the effect check and R001 / R002, with an outer-ring first module
//! an inner-ring generic escaped R003, and each mirror rejected legal code. Each instance is now
//! checked under the meet of its definer and the modules whose scope resolved its names, but it
//! is still emitted in the filing module's ring, and the AIR-level placement gate refuses every
//! lowered call that crosses rings with R007 — so a mirror layout the meet accepts is refused at
//! emission until instances are emitted into their governing ring (issue #768). R004 and R006
//! never rode the routing. The section "Ring codes under monomorph routing" pins the RING-code
//! side in the integrated tree; the effect-check side is pinned in `effect_ring_routing.rs`.
//!
//! Failure direction: if a future inner-ring primitive performing a HOST effect were added, the
//! exemption would FAIL OPEN (the effect would reach the host with no row to charge it to). The
//! fence tests are what a change to that surface must first break.
//!
//! Every assertion is an exact code SET (sorted, deduplicated), never a containment check.

use sigil_compiler::compile_named_module;

/// Sorted, deduplicated diagnostic codes of one compile; empty means a clean compile.
fn codes_of(source: &str, label: &str) -> Vec<String> {
    match compile_named_module(
        format!("effect_ring_scope_{label}.sigil"),
        source.to_string(),
    ) {
        Ok(_) => Vec::new(),
        Err(err) => {
            let mut codes: Vec<String> = err
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
            codes.sort();
            codes.dedup();
            codes
        }
    }
}

fn assert_codes(source: &str, label: &str, expected: &[&str]) {
    let got = codes_of(source, label);
    let want: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
    assert_eq!(got, want, "exact code set for {label}");
}

/// The same program under the two rings: the inner ring compiles clean, the outer ring
/// rejects with exactly `outer_codes`. `body` follows the `module m;` line.
fn assert_ring_pair(body: &str, label: &str, outer_codes: &[&str]) {
    let inner = format!("module m;\n{body}");
    let outer = format!("#[ring(outer)]\nmodule m;\n{body}");
    assert_codes(&inner, &format!("{label}_inner"), &[]);
    assert_codes(&outer, &format!("{label}_outer"), outer_codes);
}

// ── The exemption ───────────────────────────────────────────────────

/// An undeclared effect reaching a direct call: inner {} vs outer {E001}.
#[test]
fn inner_ring_direct_call_is_exempt_outer_fires_e001() {
    assert_ring_pair(
        "effect NetIO;\n\
         fn expensive() -> i64 ! { NetIO } { return 0; }\n\
         fn boot() -> i64 ! {} { return expensive(); }\n",
        "direct_call",
        &["E001"],
    );
}

/// An effectful closure applied under an empty row: inner {} vs outer {E001}.
#[test]
fn inner_ring_closure_apply_is_exempt_outer_fires_e001() {
    assert_ring_pair(
        "effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn caller() -> i64 ! {} { let g = fn(x: i64) -> i64 { return logs(); }; return g(1); }\n",
        "closure_apply",
        &["E001"],
    );
}

/// `alloc` with `Alloc` registered but absent from the row: inner {} vs outer {E001}. This is
/// the counterexample to "the inner ring performs no effects": `alloc` performs a registered
/// effect in the inner ring and is simply not charged for it.
#[test]
fn inner_ring_alloc_is_exempt_outer_fires_e001() {
    assert_ring_pair(
        "effect Alloc;\n\
         fn f() -> i64 ! {} { let p: i64 = alloc(8); return p; }\n",
        "alloc",
        &["E001"],
    );
}

/// `handle Unsafe` in a non-`#[trusted]` module: inner {} vs outer {E002}.
#[test]
fn inner_ring_handle_unsafe_is_exempt_outer_fires_e002() {
    assert_ring_pair(
        "fn f() -> i64 ! {} {\n\
         \x20   handle Unsafe {\n\
         \x20       let _x: i64 = 1;\n\
         \x20   };\n\
         \x20   return 0;\n\
         }\n",
        "handle_unsafe",
        &["E002"],
    );
}

/// The default ring IS the inner ring: writing `#[ring(inner)]` explicitly changes nothing.
/// (A `pub` modifier is likewise still inner; the selfhost differential pins that bit.)
#[test]
fn explicit_ring_inner_matches_the_default_ring() {
    let body = "effect NetIO;\n\
                fn expensive() -> i64 ! { NetIO } { return 0; }\n\
                fn boot() -> i64 ! {} { return expensive(); }\n";
    assert_codes(
        &format!("#[ring(inner)]\nmodule m;\n{body}"),
        "explicit_inner",
        &[],
    );
    assert_codes(&format!("module m;\n{body}"), "default_inner", &[]);
}

/// Confinement (non-generic): the exemption keys on each function's own module ring, not on
/// the program's first module. A NON-generic outer-ring fn placed after an inner-ring module
/// still fires exactly {E001}. This is the control that separates the documented exemption
/// from the monomorph-routing gap (generic twins escaped here before the governing-meet fix;
/// `effect_ring_routing.rs` pins them at exactly {E001} now).
#[test]
fn outer_ring_nongeneric_fn_after_inner_module_still_fires_e001() {
    assert_codes(
        "module first;\n\
         fn dummy() -> i64 { return 0; }\n\
         #[ring(outer)]\n\
         module m;\n\
         effect NetIO;\n\
         fn expensive() -> i64 ! { NetIO } { return 0; }\n\
         fn boot() -> i64 ! {} { return expensive(); }\n",
        "nongeneric_inner_first",
        &["E001"],
    );
}

// ── The fences ──────────────────────────────────────────────────────

/// Host-boundary fence 1 (R003): an inner-ring module cannot declare-and-call an `extern` — the
/// primitive that performs a host effect. Exact set {R003}: nothing else fires first.
#[test]
fn inner_ring_extern_call_is_fenced_by_r003() {
    assert_codes(
        "module app;\n\
         extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
         fn boot() -> i64 ! {} { return fs_read(0, 0); }\n",
        "extern_call",
        &["R003"],
    );
}

/// Row-hygiene fence (E003), NOT load-bearing: an inner-ring FREE fn cannot declare the
/// privilege effects `FFI` / `Unsafe` in its row, so no inner free-fn row can NAME a host
/// effect. Exact set {E003}. Its two limits are pinned elsewhere in this file and recorded in
/// `tests/attack/KNOWN_GAPS.md`: a row-less inner-ring fn may still write `handle Unsafe`
/// (clean, above), and the validator walks free `FnDef` items only, so an inner-ring impl
/// method may declare `Unsafe` outright.
#[test]
fn inner_ring_privilege_row_is_fenced_by_e003() {
    assert_codes(
        "module m;\n\
         fn f() -> i64 ! { FFI, Unsafe } { return 0; }\n\
         fn boot() -> i64 ! {} { return f(); }\n",
        "privilege_row",
        &["E003"],
    );
}

/// Host-boundary fence 2 (R004): inner-ring code cannot reach host I/O through an outer-ring
/// wrapper by a direct cross-ring call; only `grant` crosses the boundary. Exact set {R004}: the
/// outer wrapper itself is legal (it is `#[trusted]` and declares its row), so nothing else fires.
#[test]
fn inner_to_outer_cross_ring_call_is_fenced_by_r004() {
    assert_codes(
        "#[ring(outer)] #[trusted]\n\
         module io;\n\
         effect FsIO;\n\
         extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
         pub fn read(p: i32, n: i32) -> i64 ! { FsIO, FFI, Unsafe } { return fs_read(p, n); }\n\
         module app;\n\
         use io;\n\
         fn boot() -> i64 ! {} { return io::read(0, 0); }\n",
        "cross_ring_call",
        &["R004"],
    );
}

// ── The SECOND E001 emitter: ring-blind, type-check, generic callees ─

/// An effectful closure passed to a generic callee whose Fn-typed formal carries a CONCRETE
/// empty row. `{RING}` is replaced by the module attribute line under test.
const GENERIC_CONCRETE_ROW: &str = "{RING}module app;\n\
     effect Log;\n\
     fn logs() -> i64 ! { Log } { return 0; }\n\
     fn h<T>(f: Fn(i64) -> i64 ! { }, x: T) -> i64 { return f(1); }\n\
     fn caller() -> i64 ! {} { return h(fn(x: i64) -> i64 { return logs(); }, 1); }\n";

fn with_ring(template: &str, ring_line: &str) -> String {
    template.replace("{RING}", ring_line)
}

/// The second emitter is RING-BLIND: byte-identical source is exactly {E001} under the default
/// (inner) ring, an explicit `#[ring(inner)]`, and `#[ring(outer)]`. Every other E001 pin in this
/// file is a ring PAIR ({} inner vs {E001} outer); this one is ring-invariant, because
/// `bind_and_check_effect_rows` runs in the type-check pass, which is given no ring.
#[test]
fn generic_callee_concrete_row_fires_e001_in_every_ring() {
    assert_codes(
        &with_ring(GENERIC_CONCRETE_ROW, ""),
        "generic_row_default_inner",
        &["E001"],
    );
    assert_codes(
        &with_ring(GENERIC_CONCRETE_ROW, "#[ring(inner)]\n"),
        "generic_row_explicit_inner",
        &["E001"],
    );
    assert_codes(
        &with_ring(GENERIC_CONCRETE_ROW, "#[ring(outer)]\n"),
        "generic_row_outer",
        &["E001"],
    );
}

/// The second emitter is not the monomorph-routing gap wearing a different hat. Routing files a
/// monomorph under `modules[0]`; here EVERY module is inner-ring, so that route ends in the
/// wholesale effect-check skip and could not produce E001. It is still exactly {E001}.
#[test]
fn generic_callee_e001_is_not_the_monomorph_routing_path() {
    assert_codes(
        &with_ring(
            &GENERIC_CONCRETE_ROW.replace(
                "module app;",
                "module first;\nfn dummy() -> i64 { return 0; }\nmodule app;",
            ),
            "",
        ),
        "generic_row_inner_first_inner",
        &["E001"],
    );
}

/// Control: the same generic callee with a PURE closure argument compiles clean. The emitter
/// keys on the argument's effect row, not on the callee being generic.
#[test]
fn generic_callee_pure_closure_argument_is_clean() {
    assert_codes(
        "module app;\n\
         effect Log;\n\
         fn no_effects() -> i64 ! { } { return 0; }\n\
         fn h<T>(f: Fn(i64) -> i64 ! { }, x: T) -> i64 { return f(1); }\n\
         fn caller() -> i64 ! {} { return h(fn(x: i64) -> i64 { return no_effects(); }, 1); }\n",
        "generic_row_pure_arg",
        &[],
    );
}

/// Control: with a row VARIABLE formal (`! { e }`) the same effectful closure is accepted — the
/// variable binds the actual's residual row, so the acceptance check `actual ⊆ concrete ∪
/// binding` holds by construction. It is the CONCRETE formal row that rejects, not genericity.
#[test]
fn generic_callee_row_variable_absorbs_the_effectful_argument() {
    assert_codes(
        "module app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<e, T>(f: Fn(i64) -> i64 ! { e }, x: T) -> i64 ! { e } { return f(1); }\n\
         fn caller() -> i64 ! { Log } { return h(fn(x: i64) -> i64 { return logs(); }, 1); }\n",
        "generic_row_variable_arg",
        &[],
    );
}

/// Control (boundary of the emitter): the NON-generic twin never reaches this code at all. The
/// non-generic call path enforces row contravariance through `type_compatible`, so the identical
/// shape is exactly {T071} — a type error, not an effect error — and it is ring-invariant too.
/// This is what separates "E001 from the type checker" from "E001 from the effect checker".
#[test]
fn nongeneric_callee_effectful_closure_argument_is_t071_not_e001() {
    let body = "module app;\n\
                effect Log;\n\
                fn logs() -> i64 ! { Log } { return 0; }\n\
                fn h(f: Fn(i64) -> i64 ! { }) -> i64 { return f(1); }\n\
                fn caller() -> i64 ! {} { return h(fn(x: i64) -> i64 { return logs(); }); }\n";
    assert_codes(body, "nongeneric_row_inner", &["T071"]);
    assert_codes(
        &format!("#[ring(outer)]\n{body}"),
        "nongeneric_row_outer",
        &["T071"],
    );
}

/// `handle Log { ... }` around the call does NOT silence the second emitter: it is a
/// signature-acceptance check on the ARGUMENT against the FORMAL's declared row, not the effect
/// checker's available-effect computation. Exactly {E001} with the handler in place.
#[test]
fn handle_at_the_call_site_does_not_silence_the_generic_row_check() {
    assert_codes(
        "module app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn h<T>(f: Fn(i64) -> i64 ! { }, x: T) -> i64 { return f(1); }\n\
         fn caller() -> i64 ! { Log } {\n\
         \x20   handle Log { let _r: i64 = h(fn(x: i64) -> i64 { return logs(); }, 1); };\n\
         \x20   return 0;\n\
         }\n",
        "generic_row_handled",
        &["E001"],
    );
}

// ── Ring codes under monomorph routing: the integrated verdicts ────
//
// History: on main `ae026aec`, `ring_check` keyed R001 / R002 / R003 on the ring of the module
// a function is FILED under, and a monomorphized generic instance is filed under `modules[0]`
// (`type_check/mod.rs`, the `else { 0 }` owner arm), not under its defining module. So an
// outer-ring generic after an inner-ring first module ESCAPED R001 / R002 (exactly `{}`), an
// inner-ring generic after an outer-ring first module escaped R003, and each mirror rejected
// legal code with the other ring's code. Measured shape of the class there (the CLI built from
// ae026aec, every generic against its non-generic twin in both first-module orders): R001
// (parameter, return, `let`; free fn and generic impl method), R002 and R003 escaped; R004
// (type-check, keyed on the DEFINING module's ring) and R006 (a module attribute) did not.
//
// Integrated tree: the governing-meet fix (p2b/routing, `effect_ring_routing.rs`) checks each
// instance under the meet of its definer and the modules whose scope resolved its names, so
// every escape pin below now equals its non-generic twin. Instances are still FILED (so
// emitted) under `modules[0]`, and the AIR-level placement gate from the two-ring index fix
// (`ring_check::check_air_ring_placement`) refuses every lowered call that crosses rings with
// R007. So each mirror pin — legal code whose generic is filed under a first module of the other
// ring — moved from the other ring's code to exactly {R007}: still a refusal of legal code, now
// fail-closed by design, until instances are emitted into their governing ring
// (issue #768; the author chose on 2026-10-01 to land the meet with these refusals). The
// meet's accept verdict on mirror layouts is pinned at the checker layer in
// `effect_ring_routing.rs`. The non-generic twins and the R004 / R006 pins did
// NOT move: they are the controls. `docs/SOUNDNESS_MATRIX.md` SND-RING-001 cites every test fn
// in this section by name via `@test:` (existence is enforced by `soundness_contract.rs`), so a
// rename ships with that row's update in the same commit.

/// An inner-ring first module, placed ahead of the module under test.
const FIRST_INNER: &str = "module first;\nfn dummy() -> i64 { return 0; }\n";
/// An outer-ring first module, placed ahead of the module under test.
const FIRST_OUTER: &str = "#[ring(outer)]\nmodule first;\nfn dummy() -> i64 { return 0; }\n";

/// Outer-ring module binding an OWNED cap in `g`. `{G}` is the signature of `g` under test.
/// `mk` is generic in both twins, so it rides the same routing and only `g` differs.
const R001_LET: &str = "#[ring(outer)]\nmodule app;\n\
     cap type Tool { use_tool }\n\
     fn mk<U>(u: U) -> Tool ! {} { return mk(u); }\n\
     {G} ! {} { let c: Tool = mk(x); return 0; }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// Outer-ring module whose `g` returns a closure type carrying a cap REFERENCE (the R002 channel
/// that reaches `ring_check`; a bare `-> &Tool` is pre-empted by a type error in both twins).
const R002_FN_RET: &str = "#[ring(outer)]\nmodule app;\n\
     cap type Tool { use_tool }\n\
     {G} { return f; }\n\
     fn use_it(f: Fn(i64) -> &Tool) -> i64 ! {} { let r: Fn(i64) -> &Tool = g(1, f); return 0; }\n";

/// Inner-ring module whose `g` calls an `extern`, result bound `@Internal` so no taint code
/// pre-empts.
const R003_EXTERN: &str = "module app;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     {G} { let r: i64 @Internal = fs_read(0, 0); return 0; }\n\
     fn boot() -> i64 { return g(1); }\n";

fn twin(template: &str, generic_sig: &str, nongeneric_sig: &str) -> (String, String) {
    (
        template.replace("{G}", generic_sig),
        template.replace("{G}", nongeneric_sig),
    )
}

/// R001 no longer escapes: with an inner-ring first module, an outer-ring generic binding an
/// owned cap is exactly {R001}, as its non-generic twin (main `ae026aec`: an exactly EMPTY set —
/// the escape). Alone (the outer module first) the generic is {R001} as well.
#[test]
fn ring_routing_r001_outer_generic_after_inner_first_module_matches_its_twin() {
    let (generic, nongeneric) = twin(R001_LET, "fn g<T>(x: T) -> i64", "fn g(x: i64) -> i64");
    assert_codes(
        &format!("{FIRST_INNER}{generic}"),
        "r001_generic_inner_first",
        &["R001"],
    );
    assert_codes(
        &format!("{FIRST_INNER}{nongeneric}"),
        "r001_nongeneric_inner_first",
        &["R001"],
    );
    assert_codes(&generic, "r001_generic_alone", &["R001"]);
    assert_codes(
        &format!("{FIRST_OUTER}{generic}"),
        "r001_generic_outer_first",
        &["R001"],
    );
}

/// R002 no longer escapes: an outer-ring generic returning a cap-reference-bearing closure type
/// after an inner-ring first module is exactly {R002}, as its non-generic twin (main `ae026aec`:
/// an exactly EMPTY set).
#[test]
fn ring_routing_r002_outer_generic_after_inner_first_module_matches_its_twin() {
    let (generic, nongeneric) = twin(
        R002_FN_RET,
        "fn g<T>(x: T, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool",
        "fn g(x: i64, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool",
    );
    assert_codes(
        &format!("{FIRST_INNER}{generic}"),
        "r002_generic_inner_first",
        &["R002"],
    );
    assert_codes(
        &format!("{FIRST_INNER}{nongeneric}"),
        "r002_nongeneric_inner_first",
        &["R002"],
    );
    assert_codes(&generic, "r002_generic_alone", &["R002"]);
}

/// R003 no longer escapes: with an OUTER-ring first module, an inner-ring generic calling an
/// `extern` is exactly {R003}, as its non-generic twin (main `ae026aec`: an exactly EMPTY set).
/// Alone (the inner module first) the generic is {R003} as well.
#[test]
fn ring_routing_r003_inner_generic_after_outer_first_module_matches_its_twin() {
    let (generic, nongeneric) = twin(R003_EXTERN, "fn g<T>(x: T) -> i64", "fn g(x: i64) -> i64");
    assert_codes(
        &format!("{FIRST_OUTER}{generic}"),
        "r003_generic_outer_first",
        &["R003"],
    );
    assert_codes(
        &format!("{FIRST_OUTER}{nongeneric}"),
        "r003_nongeneric_outer_first",
        &["R003"],
    );
    assert_codes(&generic, "r003_generic_alone", &["R003"]);
    assert_codes(
        &format!("{FIRST_INNER}{generic}"),
        "r003_generic_inner_first",
        &["R003"],
    );
}

/// The mirror direction is fail-CLOSED: legal code is rejected when its generic is filed under a
/// first module of the other ring. The meet accepts each of these (as their twins); the
/// emission gate refuses the cross-ring call into the misfiled instance, so an outer-ring
/// `#[trusted]` generic calling an `extern` after an inner-ring first module, and an inner-ring
/// generic returning a cap-reference closure type or owning a cap after an outer-ring first
/// module, are each exactly {R007} (twins: {}) until #768 emits instances into their governing
/// ring. Main `ae026aec` rejected them with the other ring's code: {R003}, {R002}, {R001}.
#[test]
fn ring_routing_mirror_direction_rejects_legal_generics() {
    let (generic, nongeneric) = twin(
        "#[ring(outer)] #[trusted]\nmodule app;\n\
         extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
         {G} ! { FFI, Unsafe } { let r: i64 @Internal = fs_read(0, 0); return 0; }\n\
         fn boot() -> i64 ! { FFI, Unsafe } { return g(1); }\n",
        "fn g<T>(x: T) -> i64",
        "fn g(x: i64) -> i64",
    );
    assert_codes(
        &format!("{FIRST_INNER}{generic}"),
        "mirror_r003_generic_inner_first",
        &["R007"],
    );
    assert_codes(
        &format!("{FIRST_INNER}{nongeneric}"),
        "mirror_r003_nongeneric_inner_first",
        &[],
    );

    let inner_fn_ret = R002_FN_RET.replace("#[ring(outer)]\nmodule app;", "module app;");
    let (generic, nongeneric) = twin(
        &inner_fn_ret,
        "fn g<T>(x: T, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool",
        "fn g(x: i64, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool",
    );
    assert_codes(
        &format!("{FIRST_OUTER}{generic}"),
        "mirror_r002_generic_outer_first",
        &["R007"],
    );
    assert_codes(
        &format!("{FIRST_OUTER}{nongeneric}"),
        "mirror_r002_nongeneric_outer_first",
        &[],
    );

    // `mk` is NON-generic here so it stays in its (inner) module and only `g` is re-filed.
    let (generic, nongeneric) = twin(
        "module app;\n\
         cap type Tool { use_tool }\n\
         fn mk(u: i64) -> Tool ! {} { return mk(u); }\n\
         {G} ! {} { let c: Tool = mk(1); return 0; }\n\
         fn boot() -> i64 ! {} { return g(1); }\n",
        "fn g<T>(x: T) -> i64",
        "fn g(x: i64) -> i64",
    );
    assert_codes(
        &format!("{FIRST_OUTER}{generic}"),
        "mirror_r001_generic_outer_first",
        &["R007"],
    );
    assert_codes(
        &format!("{FIRST_OUTER}{nongeneric}"),
        "mirror_r001_nongeneric_outer_first",
        &[],
    );
}

/// Controls that must NOT flip: R004 is raised by the type checker against the DEFINING module's
/// ring (`tracker.current_module_ring`), and R006 is a module-attribute check, so neither rides
/// the monomorph routing. A generic cross-ring caller is exactly {R004} and a generic in an
/// inner-ring `#[trusted]` module is exactly {R006}, identical to their non-generic twins, under
/// both first-module rings.
#[test]
fn ring_routing_r004_and_r006_do_not_escape_for_generics() {
    let r004 = "#[ring(outer)] #[trusted]\nmodule io;\neffect FsIO;\n\
                extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
                pub fn read(p: i32, n: i32) -> i64 ! { FsIO, FFI, Unsafe } { return fs_read(p, n); }\n\
                module app;\nuse io;\n\
                {G} { return io::read(0, 0); }\n\
                fn boot() -> i64 { return g(1); }\n";
    let r006 = "#[ring(inner)] #[trusted]\nmodule app;\n\
                {G} { return 0; }\n\
                fn boot() -> i64 { return g(1); }\n";
    for (template, code) in [(r004, "R004"), (r006, "R006")] {
        let (generic, nongeneric) = twin(template, "fn g<T>(x: T) -> i64", "fn g(x: i64) -> i64");
        for (first, order) in [(FIRST_INNER, "inner_first"), (FIRST_OUTER, "outer_first")] {
            assert_codes(
                &format!("{first}{generic}"),
                &format!("{code}_generic_{order}"),
                &[code],
            );
            assert_codes(
                &format!("{first}{nongeneric}"),
                &format!("{code}_nongeneric_{order}"),
                &[code],
            );
        }
    }
}

// ── SC-P4 anti-stub ─────────────────────────────────────────────────

/// The helper reports codes, not a constant: a planted outer-ring leak yields a non-empty
/// exact set, so an empty set from the inner-ring probes is an observation, not a stub.
#[test]
fn codes_of_detects_a_planted_leak() {
    let planted = "#[ring(outer)]\nmodule m;\n\
                   effect NetIO;\n\
                   fn expensive() -> i64 ! { NetIO } { return 0; }\n\
                   fn boot() -> i64 ! {} { return expensive(); }\n";
    assert_eq!(codes_of(planted, "anti_stub"), vec!["E001".to_string()]);
}
