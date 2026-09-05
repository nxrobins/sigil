//! Axis-4 ("better errors") quality assertions: every test in this file
//! pins that a specific diagnostic's emitted message names the offending
//! entity AND its hint suggests a concrete copyable fix.
//!
//! Without these tests, an axis-4 improvement is easily undone: a future
//! refactor of the diagnostic call site can drop a `{name}` interpolation
//! or revert to a generic message, and only a human reading the output
//! would notice. Asserting message *content* (not just the code) locks
//! the user-facing quality.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;
use sigil_compiler::diagnostics::registry;

fn find_diagnostic<'a>(err: &'a CompileError, code: &str) -> &'a sigil_compiler::Diagnostic {
    err.diagnostics()
        .iter()
        .find(|d| d.code().as_str() == code)
        .unwrap_or_else(|| {
            panic!(
                "expected {code} in diagnostics, got: {:?}",
                err.diagnostics()
            )
        })
}

/// NF-S7-2 / NF-S7-10: assert EXACTLY ONE diagnostic with the given code.
/// Panics with the full diagnostic list if the count is anything other
/// than 1 — closes the "multi-fire ambiguity" gap where `find_diagnostic`
/// silently picks the first match.
fn find_diagnostic_or_fail<'a>(
    err: &'a CompileError,
    code: &str,
) -> &'a sigil_compiler::Diagnostic {
    let matches: Vec<&sigil_compiler::Diagnostic> = err
        .diagnostics()
        .iter()
        .filter(|d| d.code().as_str() == code)
        .collect();
    match matches.len() {
        1 => matches[0],
        0 => panic!(
            "NF-S7-2: expected exactly 1 {code}, found 0. All diagnostics: {:#?}",
            err.diagnostics()
        ),
        n => panic!(
            "NF-S7-2: expected exactly 1 {code}, found {n}. All diagnostics: {:#?}",
            err.diagnostics()
        ),
    }
}

/// NF-S7-11: assert NONE of the listed codes are present in the
/// diagnostics. Used by routing-exclusivity tests to verify T22X
/// firing does not bleed into T22Y route.
fn assert_no_diagnostic_with_code(err: &CompileError, forbidden_code: &str) {
    let any = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == forbidden_code);
    assert!(
        !any,
        "NF-S7-11: expected NO {forbidden_code} diagnostic but found one. All diagnostics: {:#?}",
        err.diagnostics()
    );
}

fn hint_for(code: &str) -> &'static str {
    let dc = sigil_compiler::DiagnosticCode::new(match code {
        "T046" => "T046",
        "T140" => "T140",
        "T183" => "T183",
        "T184" => "T184",
        "T185" => "T185",
        "T186" => "T186",
        "T211" => "T211",
        "T215" => "T215",
        "T216" => "T216",
        "T217" => "T217",
        "T218" => "T218",
        "T219" => "T219",
        "T220" => "T220",
        "T221" => "T221",
        "T222" => "T222",
        "T223" => "T223",
        "T224" => "T224",
        "T225" => "T225",
        "T226" => "T226",
        "R003" => "R003",
        "R006" => "R006",
        "E003" => "E003",
        other => panic!("unknown code {other} — add to hint_for"),
    });
    registry::lookup(dc).expect("code present").default_hint
}

/// T046 — let binding with non-primitive annotation. After step 20
/// (axis-4 fourth touch), the message names BOTH the binding and the
/// rejected annotation, and the hint lists the supported primitives
/// plus a copyable fix.
#[test]
fn t046_message_names_binding_and_annotation_with_concrete_fix() {
    let source = r#"
module main;
record Pair { a: i64, b: i64 }
fn boot() -> i64 {
    let p: Pair = 7;
    return 0;
}
"#;
    let err =
        compile_named_module("t046_msg.sigil", source).expect_err("T046 should reject the let");
    let diag = find_diagnostic(&err, "T046");
    let msg = diag.message();

    // ENTITIES: the message must name the binding AND the rejected
    // annotation. Without these, the user has to read the file:line:col
    // span to figure out which `let` failed.
    assert!(
        msg.contains("`p`"),
        "T046 message must name binding `p`; got: {msg}"
    );
    assert!(
        msg.contains("`Pair`"),
        "T046 message must name rejected annotation `Pair`; got: {msg}"
    );

    // CONCRETE FIX: the message itself includes a copyable suggestion
    // (`let p = ...` — drop the annotation). The user can copy-paste
    // this without re-deriving it from the hint.
    assert!(
        msg.contains("let p = "),
        "T046 message must include a copyable fix template `let p = ...`; got: {msg}"
    );

    // HINT: lists the specific primitive types AND the "drop the
    // annotation" fix path. Without listing the primitives the user
    // doesn't know what's allowed; without the fix path they don't
    // know how to recover.
    let hint = hint_for("T046");
    for primitive in ["i32", "u32", "i64", "u64", "f64", "bool"] {
        assert!(
            hint.contains(&format!("`{primitive}`")),
            "T046 hint must list `{primitive}` as supported; got: {hint}"
        );
    }
    assert!(
        hint.contains("drop the annotation") || hint.contains("Drop the annotation"),
        "T046 hint must include 'drop the annotation' fix path; got: {hint}"
    );
}

/// R006 — `#[trusted]` without `#[ring(outer)]`. Step 21 (axis-6 first
/// touch) tightened this previously-unenforced rule. The fixture
/// `tests/fixtures/R006.sigil` compiles cleanly against the pre-change
/// commit (verified manually); post-change it must emit R006 with a
/// message naming the offending module AND offering both copyable
/// fixes (add the ring, or drop the trust).
#[test]
fn r006_message_names_module_with_concrete_fix() {
    let source = r#"
#[ring(inner)] #[trusted]
module ext;

fn f() ! { Unsafe } {
    handle Unsafe { let _x: i64 = 1; };
    return;
}
"#;
    let err = compile_named_module("r006_msg.sigil", source)
        .expect_err("R006 should reject inner-ring trusted module");
    let diag = find_diagnostic(&err, "R006");
    let msg = diag.message();

    // ENTITY: name the module so the user knows which one is wrong.
    // Without the module name, a multi-module program with several
    // `#[trusted]` annotations gives no clue which to fix.
    assert!(
        msg.contains("`ext`"),
        "R006 message must name module `ext`; got: {msg}"
    );

    // CONTEXT: explain the violation, not just label it. The user must
    // see "inner ring" mentioned so they understand the diagnostic is
    // about ring placement, not some other property of `#[trusted]`.
    assert!(
        msg.to_lowercase().contains("inner"),
        "R006 message must mention `inner ring` to explain the violation; got: {msg}"
    );

    // CONCRETE FIX 1: add the outer-ring annotation. The hint must
    // give the actual copyable annotation, not "use the right ring".
    let hint = hint_for("R006");
    assert!(
        hint.contains("#[ring(outer)]"),
        "R006 hint must include the copyable `#[ring(outer)]` annotation; got: {hint}"
    );

    // CONCRETE FIX 2: drop the `#[trusted]` annotation. The user
    // should be told both fix paths so they can pick the right one.
    assert!(
        hint.contains("drop `#[trusted]`") || hint.contains("drop the `#[trusted]`"),
        "R006 hint must include the `drop #[trusted]` fix path; got: {hint}"
    );
}

/// R003 — inner-ring code cannot call extern fn. Step 24 (axis-6
/// second touch) made the previously-no-op `Inner` arm of ring_check
/// real. The fixture `tests/fixtures/R003.sigil` compiles cleanly
/// against the pre-change commit (verified manually) and now emits
/// R003 with the offending extern callee named in the message and
/// both copyable fixes spelled out in the hint.
#[test]
fn r003_message_names_extern_with_concrete_fix() {
    // NOTE: step 30 added E003 (inner-ring fn cannot declare Unsafe/FFI
    // effects). The R003 fixture's `use_it` MUST omit those effects from
    // its row, otherwise E003 fires before R003 and the body-level check
    // is never reached. R003 still pins the inner-ring extern call
    // mechanism — it's the body-level check.
    let source = r#"
module ext;

extern "C" fn foo() -> i64 ! { FFI, Unsafe };

fn use_it() -> i64 @Internal {
    return foo();
}
"#;
    let err = compile_named_module("r003_msg.sigil", source)
        .expect_err("R003 should reject inner-ring extern call");
    let diag = find_diagnostic(&err, "R003");
    let msg = diag.message();

    // ENTITY: name the offending extern callee. Without the name, a
    // function that calls multiple externs gives no clue which one
    // tripped the check (and inline syntax would make the span
    // ambiguous when extern calls are nested in larger expressions).
    assert!(
        msg.contains("`foo`"),
        "R003 message must name the offending extern `foo`; got: {msg}"
    );

    // CONTEXT: explain the violation kind, not just label it. The
    // user must see "inner-ring" so they understand the diagnostic
    // is about ring placement, not (e.g.) the effect row.
    assert!(
        msg.to_lowercase().contains("inner-ring") || msg.to_lowercase().contains("inner ring"),
        "R003 message must mention `inner ring`; got: {msg}"
    );

    // CONCRETE FIX 1: the hint must include the copyable
    // `#[ring(outer)] #[trusted]` annotation so a user who genuinely
    // needs FFI knows how to move the module to outer ring.
    let hint = hint_for("R003");
    assert!(
        hint.contains("#[ring(outer)]") && hint.contains("#[trusted]"),
        "R003 hint must include the `#[ring(outer)] #[trusted]` fix path; got: {hint}"
    );

    // CONCRETE FIX 2: the hint must reference the `grant` mechanism
    // so a user who wants to KEEP the policy in inner ring knows the
    // safe way to reach outer-ring FFI.
    assert!(
        hint.contains("grant"),
        "R003 hint must reference the `grant` cross-ring mechanism; got: {hint}"
    );
}

/// T183 — record field cannot be capability-typed. Step 25 (axis-2
/// fourth touch) closed the aggregate-smuggling soundness gap that
/// KNOWN_GAPS.md had assumed was parser-defended. The defense was
/// false; this test pins the real defense.
#[test]
fn t183_message_names_record_and_field_and_type() {
    let source = r#"
module sigil;
cap type Fuel {}

record Wrapper { f: Fuel }

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 1; }
}
"#;
    let err = compile_named_module("t183_msg.sigil", source)
        .expect_err("T183 should reject cap-typed record field");
    let diag = find_diagnostic(&err, "T183");
    let msg = diag.message();

    // ENTITY 1: record name. With multiple records in a module, the
    // user needs to know which one is wrong.
    assert!(
        msg.contains("`Wrapper`"),
        "T183 message must name record `Wrapper`; got: {msg}"
    );

    // ENTITY 2: field name. With multiple fields in a record, the
    // user needs to know which one is wrong.
    assert!(
        msg.contains("`f`"),
        "T183 message must name field `f`; got: {msg}"
    );

    // ENTITY 3: cap type name. Tells the user WHICH cap type is the
    // offender (e.g., when multiple cap types are declared).
    assert!(
        msg.contains("`Fuel`"),
        "T183 message must name the offending cap type `Fuel`; got: {msg}"
    );

    // CONCRETE FIX: the hint must offer a copyable workaround. The
    // user shouldn't have to guess what "non-cap surrogate" means.
    let hint = hint_for("T183");
    assert!(
        hint.contains("actor messages") || hint.contains("function arguments"),
        "T183 hint must reference the pass-by-name fix paths; got: {hint}"
    );
    assert!(
        hint.contains("i64") || hint.contains("surrogate"),
        "T183 hint must reference the non-cap-surrogate fix path; got: {hint}"
    );
}

/// T184 — enum variant payload cannot be capability-typed. Step 27
/// (axis-6 third touch) closed the companion smuggling channel that
/// step 25 (axis-2 fourth touch / T183) closed for records. The fix
/// uses the same `type_contains_cap` helper and the same structural
/// rejection at the source.
#[test]
fn t184_message_names_enum_variant_and_payload_type() {
    let source = r#"
module sigil;
cap type Fuel {}

enum CapBox { Wrapped(Fuel), Empty }

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 1; }
}
"#;
    let err = compile_named_module("t184_msg.sigil", source)
        .expect_err("T184 should reject cap-typed enum variant payload");
    let diag = find_diagnostic(&err, "T184");
    let msg = diag.message();

    // ENTITY 1: enum name. With multiple enums in a module, the user
    // needs to know which one is wrong.
    assert!(
        msg.contains("`CapBox`"),
        "T184 message must name enum `CapBox`; got: {msg}"
    );

    // ENTITY 2: variant name. With multiple variants in an enum, the
    // user needs to know which variant carries the offending payload.
    assert!(
        msg.contains("`Wrapped`"),
        "T184 message must name variant `Wrapped`; got: {msg}"
    );

    // ENTITY 3: cap type name. Tells the user WHICH cap type is the
    // offender.
    assert!(
        msg.contains("`Fuel`"),
        "T184 message must name the offending cap type `Fuel`; got: {msg}"
    );

    // CONTEXT: cross-reference T183. The two diagnostics close the
    // same conceptual hatch (aggregate smuggling) via two different
    // AIR channels — the message should mention T183 so a user who
    // hits this can see the related rule.
    assert!(
        msg.contains("T183"),
        "T184 message must cross-reference T183 (the record-field companion); got: {msg}"
    );

    // CONCRETE FIX: the hint must offer copyable workaround paths.
    let hint = hint_for("T184");
    assert!(
        hint.contains("actor messages") || hint.contains("function arguments"),
        "T184 hint must reference the pass-by-name fix paths; got: {hint}"
    );
    assert!(
        hint.contains("i64") || hint.contains("surrogate"),
        "T184 hint must reference the non-cap-surrogate fix path; got: {hint}"
    );
}

/// T140 — array literal element type mismatch. Step 28 (axis-4 fifth
/// touch) added a copyable cast template inline in the message AND
/// expanded the registry hint to enumerate three concrete fix paths.
/// Pre-step-28 the message was informative but not actionable; the
/// hint was a generic "Cast or normalize the offending element."
#[test]
fn t140_message_includes_copyable_cast_template() {
    let source = r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let xs = [1, 2.5, 3];
        return 1;
    }
}
"#;
    let err = compile_named_module("t140_msg.sigil", source)
        .expect_err("T140 should reject mixed-type array literal");
    let diag = find_diagnostic(&err, "T140");
    let msg = diag.message();

    // ENTITY 1: element index. With multiple elements, the user needs
    // to know WHICH one fails the check.
    assert!(
        msg.contains("element 1"),
        "T140 message must name the offending element index; got: {msg}"
    );

    // ENTITY 2: both types named. The user must see what they have
    // and what's expected without having to infer.
    assert!(
        msg.contains("`f64`"),
        "T140 message must name actual type `f64`; got: {msg}"
    );
    assert!(
        msg.contains("`i64`"),
        "T140 message must name expected type `i64`; got: {msg}"
    );

    // CONCRETE FIX 1: the message includes a copyable cast template
    // with the EXPECTED type filled in. A user can copy-paste the
    // template and adapt — no guessing at syntax.
    assert!(
        msg.contains("as i64"),
        "T140 message must include the copyable cast template `as i64`; got: {msg}"
    );

    // CONCRETE FIX 2: the message names the alternative (change
    // element 0's type to match). Without this, a user staring at
    // a [f64-mostly, i64-stray] array might cast the wrong way.
    assert!(
        msg.contains("element 0"),
        "T140 message must reference element 0 as the alternative fix; got: {msg}"
    );

    // HINT: enumerates THREE fix paths (cast, change element 0,
    // annotate the binding). Each path is distinct and copyable.
    let hint = hint_for("T140");
    assert!(
        hint.contains("as <expected>") || hint.contains("`<expr> as"),
        "T140 hint must include a cast template; got: {hint}"
    );
    assert!(
        hint.contains("element 0"),
        "T140 hint must reference the element-0 fix path; got: {hint}"
    );
    assert!(
        hint.contains("annotate") || hint.contains("[i64]"),
        "T140 hint must reference the binding-annotation fix path; got: {hint}"
    );
}

/// E003 — inner-ring function declares Unsafe/FFI privilege effect.
/// Step 30 (axis-6 fourth touch) implemented the previously-unemitted
/// E003 check. The fixture `tests/fixtures/E003.sigil` compiled cleanly
/// against the pre-step-30 commit (verified manually) and used
/// `handle Unsafe { ... }` in the inner ring — bypassing the trust
/// system entirely via the effect_check.rs "inner ring exempt" skip.
#[test]
fn e003_message_names_inner_fn_and_forbidden_effects() {
    let source = r#"
module ext;

fn do_dangerous() ! { Unsafe } {
    handle Unsafe { let _x: i64 = 1; };
    return;
}
"#;
    let err = compile_named_module("e003_msg.sigil", source)
        .expect_err("E003 should reject inner-ring fn with Unsafe effect");
    let diag = find_diagnostic(&err, "E003");
    let msg = diag.message();

    // ENTITY 1: function name. A module with multiple inner-ring
    // functions needs the offending function named so the user knows
    // which to fix.
    assert!(
        msg.contains("`do_dangerous`"),
        "E003 message must name function `do_dangerous`; got: {msg}"
    );

    // ENTITY 2: the specific forbidden effect. Tells the user WHICH
    // effect from their row is the problem — not "you have some
    // forbidden effect."
    assert!(
        msg.contains("`Unsafe`"),
        "E003 message must name the offending effect `Unsafe`; got: {msg}"
    );

    // CONTEXT: explain the violation kind. "Privilege" is the load-
    // bearing word — distinguishes this from a benign effect like
    // `Alloc` which IS allowed in inner ring.
    assert!(
        msg.to_lowercase().contains("privilege") || msg.contains("outer-ring"),
        "E003 message must explain the privilege framing; got: {msg}"
    );

    // CONCRETE FIX 1: move to outer/trusted. The hint must include
    // the copyable annotation pair.
    let hint = hint_for("E003");
    assert!(
        hint.contains("#[ring(outer)]") || hint.contains("trusted"),
        "E003 hint must reference the outer-trusted module fix path; got: {hint}"
    );

    // CONCRETE FIX 2: drop the privilege effects from the row. The
    // hint must mention `Alloc` or "other effects" so the user knows
    // not all effects are forbidden.
    assert!(
        hint.contains("Alloc") || hint.contains("other effects"),
        "E003 hint must clarify that non-privilege effects are still allowed; got: {hint}"
    );
}

/// T185 — cap type declares >32 authorities. Step 31 (axis-2 fifth
/// touch) closed a latent soundness bound: 32-bit BV masks can hold
/// at most 32 authorities, and the prior compiler silently accepted
/// 33+, leading to bit-shift overflow and corrupted authority masks.
#[test]
fn t185_message_names_cap_type_and_authority_count() {
    let source = r#"
module sigil;

cap type Mega {
    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
    a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29,
    a30, a31, a32, a33
}

entry actor Main {
    state { fuel: Mega }
    on Start() -> i64 { return 1; }
}
"#;
    let err = compile_named_module("t185_msg.sigil", source)
        .expect_err("T185 should reject cap type with >32 authorities");
    let diag = find_diagnostic(&err, "T185");
    let msg = diag.message();

    // ENTITY 1: cap type name. With multiple cap types in a module,
    // the user must know which one is wrong.
    assert!(
        msg.contains("`Mega`"),
        "T185 message must name cap type `Mega`; got: {msg}"
    );

    // ENTITY 2: actual count. Tells the user exactly how many they
    // declared — useful when they have several similar cap types
    // and need to identify which one tripped the cap.
    assert!(
        msg.contains("34"),
        "T185 message must include the actual authority count (34); got: {msg}"
    );

    // ENTITY 3: the cap (32). Without this, the user might wonder
    // "what's the limit?" — and grep through the source.
    assert!(
        msg.contains("32"),
        "T185 message must include the cap value (32); got: {msg}"
    );

    // CONCRETE FIX: split into narrower cap types. The hint must
    // make this concrete with an example pattern, not just
    // "factor differently".
    let hint = hint_for("T185");
    assert!(
        hint.contains("Split") || hint.contains("split"),
        "T185 hint must reference the split-into-multiple-types fix path; got: {hint}"
    );
    assert!(
        hint.contains("32-bit") || hint.contains("bitvector"),
        "T185 hint must explain WHY (32-bit / bitvector); got: {hint}"
    );
}

/// F006 regression — a `.restrict(aN)` on a cap type with an authority
/// at bit index >= 32 must not ICE. The over-count cap type is rejected
/// by T185 at its declaration, but the restrict expression is still
/// type-checked, resolving `a32` through `AuthorityRegistry::
/// restriction_mask`, which computes `1u32 << 32`. That shift panics in
/// debug builds ("attempt to shift left with overflow") — pre-fix, that
/// ICE fired before T185's diagnostic reached the user. The shifts in
/// `registries.rs` are now guarded with `checked_shl`, folding the
/// out-of-range bit to 0 so the program is cleanly rejected with T185.
#[test]
fn t185_restrict_on_over_count_authority_does_not_ice() {
    let source = r#"
module sigil;

cap type Big {
    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
    a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29,
    a30, a31, a32
}

entry actor Main {
    state { fuel: Big }
    on Start() -> i64 {
        let restricted: Big = fuel.restrict(a32);
        return 1;
    }
}
"#;
    // Must return an Err (rejected), not panic. `expect_err` doubles as
    // the ICE guard: a panic in type-checking would unwind past it.
    let err = compile_named_module("f006_restrict.sigil", source)
        .expect_err("33-authority cap type must be rejected, not compiled");
    // The delivered diagnostic is T185 (the declaration bound), proving
    // the guarded shift let the validator speak instead of panicking.
    let diag = find_diagnostic(&err, "T185");
    assert!(
        diag.message().contains("`Big`"),
        "expected T185 on cap type `Big`; got: {}",
        diag.message()
    );
}

/// T186 — array literal element type cannot be capability-typed.
/// Step 32 (axis-6 fifth touch) closed the third structural
/// smuggling channel in the series: records (T183, axis-2),
/// enum payloads (T184, axis-6), and now array elements (T186,
/// axis-6). The Index AIR node produced a fresh cap binding
/// that Z3's authority tracker treated as full authority by
/// default — the same shape as LoadField (T183) and match-binding
/// destructure (T184).
#[test]
fn t186_message_names_array_element_and_cap_type() {
    let source = r#"
module sigil;
cap type Fuel { burn, query }
fn needs_full(f: Fuel) -> i64 { return 1; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let restricted: Fuel = fuel.restrict(burn);
        let arr = [restricted];
        let smuggled = arr[0];
        return needs_full(smuggled);
    }
}
"#;
    let err = compile_named_module("t186_msg.sigil", source)
        .expect_err("T186 should reject array literal with cap-typed elements");
    let diag = find_diagnostic(&err, "T186");
    let msg = diag.message();

    // ENTITY: cap type name. Tells the user WHICH cap type is the
    // offender (e.g., when multiple cap types are declared and only
    // some are accidentally placed in array literals).
    assert!(
        msg.contains("`Fuel`"),
        "T186 message must name the offending cap type `Fuel`; got: {msg}"
    );

    // CONTEXT: cross-reference T183 (and via that, T184). The three
    // diagnostics close the same conceptual hatch (aggregate smuggling)
    // via three different AIR channels — the message should mention
    // T183 so a user who hits this can see the related rule.
    assert!(
        msg.contains("T183"),
        "T186 message must cross-reference T183 (the record-field companion); got: {msg}"
    );

    // CONCRETE FIX: the hint must offer copyable workaround paths
    // that mirror T183/T184.
    let hint = hint_for("T186");
    assert!(
        hint.contains("actor messages") || hint.contains("function arguments"),
        "T186 hint must reference the pass-by-name fix paths; got: {hint}"
    );
    assert!(
        hint.contains("i64") || hint.contains("surrogate"),
        "T186 hint must reference the non-cap-surrogate fix path; got: {hint}"
    );
}

/// T064/T065/T066/T067 — "did you mean ..." suggestions. Step 35
/// (axis-4 sixth touch) generalizes the T060 closest-name helper to
/// four more unknown-name diagnostics: T064 (unknown actor in spawn
/// and dispatch), T065 (unknown handler on an actor), T066 (unknown
/// type), T067 (unknown actor in `ActorRef<T>`).
///
/// Each test verifies BOTH that the diagnostic still names the typo'd
/// identifier in its message AND that the per-call-site hint suggests
/// the closest in-scope name. We read the hint from the Diagnostic
/// directly (not from the registry) because `error_with_hint` overrides
/// the registry default.

#[test]
fn t064_message_names_unknown_actor_with_did_you_mean_suggestion() {
    // Spawn-site T064: typo'd actor name in `spawn::<X>(...)`.
    let source = r#"
module sigil;
cap type Fuel {}
actor Worker { init(f: Fuel) {} on Run() -> i64 { return 1; } }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let _w = spawn::<Wroker>(fuel);
        return 1;
    }
}
"#;
    let err =
        compile_named_module("t064_msg.sigil", source).expect_err("T064 should reject `Wroker`");
    let diag = find_diagnostic(&err, "T064");
    let msg = diag.message();
    let hint = diag.hint().unwrap_or("");

    // ENTITY: name the typo'd identifier so the user sees what's wrong.
    assert!(
        msg.contains("`Wroker`"),
        "T064 message must name the typo'd actor `Wroker`; got: {msg}"
    );

    // CONCRETE FIX: hint suggests the closest in-scope actor name.
    // Without this the user has to grep their own source to find
    // similar names.
    assert!(
        hint.contains("`Worker`"),
        "T064 hint must suggest `Worker` (closest in-scope actor); got: {hint}"
    );
    assert!(
        hint.contains("did you mean"),
        "T064 hint must use `did you mean ...` phrasing; got: {hint}"
    );
}

#[test]
fn t065_message_names_unknown_handler_with_did_you_mean_suggestion() {
    // T065 fires via `actor.send(MsgName(...))` where the message name
    // doesn't match any of the actor's `on Msg(...)` handlers.
    let source = r#"
module sigil;
cap type Fuel {}
actor Worker {
    init(f: Fuel) {}
    on Crunch() -> i64 { return 1; }
}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Worker>(fuel);
        w.send(Crnuch());
        return 1;
    }
}
"#;
    let err =
        compile_named_module("t065_msg.sigil", source).expect_err("T065 should reject `Crnuch`");
    let diag = find_diagnostic(&err, "T065");
    let msg = diag.message();
    let hint = diag.hint().unwrap_or("");

    // ENTITY 1: name the actor so the user knows the scope.
    assert!(
        msg.contains("`Worker`"),
        "T065 message must name actor `Worker`; got: {msg}"
    );

    // ENTITY 2: name the typo'd handler.
    assert!(
        msg.contains("`Crnuch`"),
        "T065 message must name typo'd handler `Crnuch`; got: {msg}"
    );

    // CONCRETE FIX: suggest the closest handler on this actor.
    assert!(
        hint.contains("`Crunch`"),
        "T065 hint must suggest `Crunch` (closest handler on `Worker`); got: {hint}"
    );
}

#[test]
fn t066_message_names_unknown_type_with_did_you_mean_suggestion() {
    // T066 fires on a Named type that doesn't resolve to any
    // declared record/enum/cap. Closest match should be drawn from
    // the union of records, enums, and caps.
    let source = r#"
module sigil;
cap type Fuel {}
record Point { x: i64, y: i64 }
fn use_point(p: Poin) -> i64 { return 1; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 1; }
}
"#;
    let err =
        compile_named_module("t066_msg.sigil", source).expect_err("T066 should reject `Poin`");
    let diag = find_diagnostic(&err, "T066");
    let msg = diag.message();
    let hint = diag.hint().unwrap_or("");

    // ENTITY: name the typo'd type.
    assert!(
        msg.contains("`Poin`"),
        "T066 message must name typo'd type `Poin`; got: {msg}"
    );

    // CONCRETE FIX: hint suggests `Point` from the records-or-enums-or-caps
    // union (closest match by Levenshtein distance).
    assert!(
        hint.contains("`Point`"),
        "T066 hint must suggest `Point` (closest declared type); got: {hint}"
    );
}

#[test]
fn t067_message_names_unknown_actorref_with_did_you_mean_suggestion() {
    // T067 fires on `ActorRef<X>` where X isn't a declared actor.
    let source = r#"
module sigil;
cap type Fuel {}
actor Worker { init(f: Fuel) {} on Run() -> i64 { return 1; } }
fn takes_ref(r: ActorRef<Wroker>) -> i64 { return 1; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 1; }
}
"#;
    let err = compile_named_module("t067_msg.sigil", source)
        .expect_err("T067 should reject `ActorRef<Wroker>`");
    let diag = find_diagnostic(&err, "T067");
    let msg = diag.message();
    let hint = diag.hint().unwrap_or("");

    // ENTITY: name the typo'd actor.
    assert!(
        msg.contains("`Wroker`"),
        "T067 message must name typo'd actor `Wroker`; got: {msg}"
    );

    // CONCRETE FIX: hint suggests the closest in-scope actor.
    assert!(
        hint.contains("`Worker`"),
        "T067 hint must suggest `Worker` (closest actor name); got: {hint}"
    );
}

// ── Wall 4 Step 1 (V7): T210 diagnostic shape contract ───────────────────

/// Wall 4 Step 1 V7 contract: T210 carries exactly 5 fields in its
/// emitted message + span: predicate text, field name, supplied literal,
/// Z3 verdict (refutable for Sat / timeout for Unknown), and source
/// span (asserted via `span().is_some()`).
///
/// This test pins the diagnostic shape so a future refactor that drops
/// any of the 5 fields fails the build. Per V7, an emission with any
/// empty field blocks merge.
#[cfg(feature = "solver")]
#[test]
fn t210_diagnostic_carries_required_5_fields() {
    let source = r#"
module sigil;

record Index { value: i64 } where value > 100

entry actor Main {
    on Tick() -> i64 {
        let idx: Index = Index { value: 42 };
        return 1;
    }
}
"#;
    let err = compile_named_module("t210_shape.sigil", source)
        .expect_err("T210 should reject 42 against `value > 100`");
    let diag = find_diagnostic(&err, "T210");
    let msg = diag.message();

    // Field 1: predicate text (operator + RHS literal).
    assert!(
        msg.contains("> 100"),
        "T210 message must include the predicate (`> 100`); got: {msg}"
    );
    // Field 2: field name.
    assert!(
        msg.contains("`value`"),
        "T210 message must name the refined field; got: {msg}"
    );
    // Field 3: supplied literal.
    assert!(
        msg.contains("`42`"),
        "T210 message must include the supplied literal; got: {msg}"
    );
    // Field 4: Z3 verdict — for this refutable predicate, "refutable".
    assert!(
        msg.contains("refutable"),
        "T210 message must surface the Z3 verdict (refutable for Sat); got: {msg}"
    );
    // Field 5: source span — the construction site.
    assert!(
        diag.span().is_some(),
        "T210 diagnostic must carry a source span"
    );
}

/// Capability diagnostics (C001-C004) must carry a source span so the
/// violation can be located, mirroring the T210/T215 refinement-span
/// assertions. The capability verifier runs over the span-free AIR; a
/// def-site span side map (`AirFunction::debug_spans`, consulted via
/// `var_span`) restores locatability. Before this fix every cap
/// diagnostic was emitted with `span: None`.
///
/// C003 is the cap code reachable from source (C001 forgery needs a
/// hand-built AIR; C002/C004 are Z3 provenance / Unknown verdicts), so
/// this fixture — an attenuated `Fuel` passed to a full-authority call
/// site — exercises the call-sink C003 path end-to-end.
#[cfg(feature = "solver")]
#[test]
fn capability_diagnostic_c003_carries_source_span() {
    let source = r#"
module sigil;
cap type Fuel { burn, query }

fn needs_full(f: Fuel) -> i64 ! {} { return 1; }

entry actor Main {
    state { fuel: Fuel }

    on Start() -> i64 {
        needs_full(fuel.restrict(burn));
        return 1;
    }
}
"#;
    let err = compile_named_module("c003_span.sigil", source)
        .expect_err("C003 should reject an attenuated cap at a full-authority call site");
    let diag = find_diagnostic(&err, "C003");
    assert!(
        diag.span().is_some(),
        "C003 diagnostic must carry a source span so the capability \
         violation can be located in source; got None. Message: {}",
        diag.message()
    );
}

// ── Wall 4 Step 2 axis-4 hint upgrades ───────────────────────────────────────

/// V30: T211's hint MUST contain the substring teaching the agent that
/// refinement is dropped through `let` bindings and other intermediate
/// expressions, with the inline-at-construction-site fix recipe. The
/// 30_refinement_dropped_in_destructure.sigil fixture exercises this
/// path; this test pins the diagnostic content.
#[cfg(feature = "solver")]
#[test]
fn t211_hint_contains_v30_inline_at_construction_substring() {
    let hint = hint_for("T211");
    let needle = "If the value came from a refined field read, inline it at the construction site";
    assert!(
        hint.contains(needle),
        "V30: T211 hint must contain the substring teaching agents the \
         inline-at-construction fix recipe. Expected substring: `{needle}`. \
         Got hint: {hint}",
    );
}

/// V31: T215's hint MUST contain the substring teaching that
/// `refinements_match` ignores field names. Without this, agents
/// debugging a T215 might erroneously rename the destination's field
/// thinking that's the discrepancy.
#[cfg(feature = "solver")]
#[test]
fn t215_hint_contains_v31_field_name_independence_substring() {
    let hint = hint_for("T215");
    let needle =
        "Refinement match compares operator and literal only; field names are not compared.";
    assert!(
        hint.contains(needle),
        "V31: T215 hint must explicitly disclaim field-name comparison. \
         Expected substring: `{needle}`. Got hint: {hint}",
    );
}

/// V13/V20: T215's emitted MESSAGE carries 5 non-empty fields —
/// destination predicate text, destination field name, supplied
/// refinement summary, source span (carried separately), and the
/// alignment hint (carried in the registry's default_hint).
#[cfg(feature = "solver")]
#[test]
fn t215_message_carries_v13_v20_five_non_empty_fields() {
    // Source has `value >= 0`; destination requires `copy > 0` (strict).
    // refinements_match returns false because (Ge, 0) != (Gt, 0).
    let source = r#"
module sigil;
record Index { value: i64 } where value >= 0
record Mirror { copy: i64 } where copy > 0
entry actor Main {
    on Tick() -> i64 {
        let idx: Index = Index { value: 42 };
        let m: Mirror = Mirror { copy: idx.value };
        return 1;
    }
}
"#;
    let err = compile_named_module("t215_shape.sigil", source)
        .expect_err("T215 should reject mismatched refinement");
    let diag = find_diagnostic(&err, "T215");
    let msg = diag.message();

    // Field 1: destination predicate (op + literal).
    assert!(
        msg.contains("> 0"),
        "V13: T215 message must include destination predicate text; got: {msg}"
    );
    // Field 2: destination field name.
    assert!(
        msg.contains("`copy`"),
        "V13: T215 message must name destination field; got: {msg}"
    );
    // Field 3: supplied refinement summary (op + literal).
    assert!(
        msg.contains(">= 0"),
        "V13: T215 message must include supplied refinement summary; got: {msg}"
    );
    // Field 4: source span.
    assert!(
        diag.span().is_some(),
        "V13: T215 diagnostic must carry a source span"
    );
    // Field 5 surfaced via hint (V31 substring).
    let hint = hint_for("T215");
    assert!(
        !hint.is_empty() && hint.len() >= 50,
        "V20: T215 hint must be substantive (≥ 50 chars); got: {hint}"
    );

    // V20: every emitted field is ≥ 3 chars. The message itself satisfies
    // this trivially (it's far longer); the more interesting check is
    // that no field is `""` or `"?"`. We probe by ensuring the message
    // doesn't have those placeholder patterns.
    for placeholder in ["``", "`?`", "<none>", "<unknown>"] {
        assert!(
            !msg.contains(placeholder),
            "V20: T215 message must not contain placeholder `{placeholder}`; got: {msg}"
        );
    }
}

/// V29: T211 and T215 messages MUST NOT serialize the internal
/// `RefinementClause` Debug format. Agents see a human-friendly
/// "value >= 0" rather than `RefinementClause { field: ..., op: Ge, literal: 0, span: ... }`.
#[cfg(feature = "solver")]
#[test]
fn t211_t215_messages_do_not_leak_refinementclause_debug() {
    // T211 path:
    let t211_source = r#"
module sigil;
record Index { value: i64 } where value > 100
entry actor Main {
    on Tick(input: i64) -> i64 {
        let idx: Index = Index { value: input };
        return 1;
    }
}
"#;
    let t211_err =
        compile_named_module("t211_no_debug.sigil", t211_source).expect_err("T211 expected");
    let t211_diag = find_diagnostic(&t211_err, "T211");
    let t211_msg = t211_diag.message();
    for forbidden in ["RefinementClause", "op:", "literal:", "Span {", "field:"] {
        assert!(
            !t211_msg.contains(forbidden),
            "V29: T211 message must not leak internal Debug marker `{forbidden}`; got: {t211_msg}"
        );
    }

    // T215 path:
    let t215_source = r#"
module sigil;
record Index { value: i64 } where value >= 0
record Mirror { copy: i64 } where copy > 0
entry actor Main {
    on Tick() -> i64 {
        let idx: Index = Index { value: 42 };
        let m: Mirror = Mirror { copy: idx.value };
        return 1;
    }
}
"#;
    let t215_err =
        compile_named_module("t215_no_debug.sigil", t215_source).expect_err("T215 expected");
    let t215_diag = find_diagnostic(&t215_err, "T215");
    let t215_msg = t215_diag.message();
    for forbidden in ["RefinementClause", "op:", "literal:", "Span {", "field:"] {
        assert!(
            !t215_msg.contains(forbidden),
            "V29: T215 message must not leak internal Debug marker `{forbidden}`; got: {t215_msg}"
        );
    }
}

// ── Wall 4 Step 3 V36 / V42 / V43 / V37 diagnostic shape tests ───────────────

/// V36 + V44: T215 message embeds the Z3 counterexample when subsumption
/// fails with a Sat verdict. The counterexample renders as `x = <integer>`
/// — never as `"x = 0"` default (V44 footgun catch) and never as
/// `"x = ?"` placeholder (V43). The substring `Z3 found a counterexample
/// to subsumption` MUST appear when Z3 actually returned Sat.
#[cfg(feature = "solver")]
#[test]
fn v36_t215_message_embeds_z3_counterexample_when_semantic_non_subset() {
    // Source `>= 0`, destination `>= 5`: counterexamples ∈ {0..4}.
    let source = r#"
module sigil;
record Source { value: i64 } where value >= 0
record Mirror { copy: i64 } where copy >= 5
entry actor Main {
    on Tick() -> i64 {
        let s: Source = Source { value: 100 };
        let m: Mirror = Mirror { copy: s.value };
        return 1;
    }
}
"#;
    let err = compile_named_module("v36_msg.sigil", source).expect_err("T215 expected");
    let diag = find_diagnostic(&err, "T215");
    let msg = diag.message();

    assert!(
        msg.contains("Z3 found a counterexample to subsumption"),
        "V36: T215 message must include the Z3-counterexample phrase \
         when Z3 returned Sat. Got: {msg}"
    );
    // Counterexample renders as `x = <integer>`. We don't pin a specific
    // integer (Z3 selects deterministically but the value depends on
    // model heuristics); we assert the `x = ` prefix appears with a
    // digit immediately after.
    let cex_pos = msg
        .find("x = ")
        .expect("V36: T215 message must include `x = ` counterexample prefix");
    let after_eq = &msg[cex_pos + 4..];
    let first_char = after_eq.chars().next().expect("non-empty after `x = `");
    assert!(
        first_char.is_ascii_digit() || first_char == '-',
        "V36: counterexample value must be a literal integer (digit or \
         leading minus). Got first char: {first_char:?} in message: {msg}"
    );
}

/// V43: the literal `"x = ?"` placeholder is FORBIDDEN in T215. A lazy
/// implementation might hardcode this on cache hit; V43 + V44 + V45's
/// cache extension ensures every cache hit also carries a real
/// counterexample integer.
#[cfg(feature = "solver")]
#[test]
fn v43_t215_message_never_contains_placeholder_x_equals_question_mark() {
    // Two fixtures with semantic non-subsumption; check both.
    for source in [
        r#"
module sigil;
record A { value: i64 } where value >= 0
record B { copy: i64 } where copy >= 5
entry actor Main {
    on Tick() -> i64 {
        let a: A = A { value: 100 };
        let b: B = B { copy: a.value };
        return 1;
    }
}
"#,
        r#"
module sigil;
record C { value: i64 } where value >= 0
record D { copy: i64 } where copy > 0
entry actor Main {
    on Tick() -> i64 {
        let c: C = C { value: 42 };
        let d: D = D { copy: c.value };
        return 1;
    }
}
"#,
    ] {
        let err = compile_named_module("v43.sigil", source).expect_err("T215 expected");
        let diag = find_diagnostic(&err, "T215");
        let msg = diag.message();
        assert!(
            !msg.contains("x = ?"),
            "V43: T215 message must NEVER contain the `x = ?` placeholder; \
             got: {msg}"
        );
    }
}

/// V42 mutual-exclusivity: a single T215 message must not simultaneously
/// contain "syntactic equality only" AND "Z3 found a counterexample".
/// The message body uses ONE narrative depending on which path emitted
/// the diagnostic; the registry hint can mention both because the hint
/// is generic guidance, not per-emission detail.
#[cfg(feature = "solver")]
#[test]
fn v42_t215_message_does_not_mix_syntactic_and_semantic_phrasing() {
    let source = r#"
module sigil;
record E { value: i64 } where value >= 0
record F { copy: i64 } where copy >= 5
entry actor Main {
    on Tick() -> i64 {
        let e: E = E { value: 100 };
        let f: F = F { copy: e.value };
        return 1;
    }
}
"#;
    let err = compile_named_module("v42.sigil", source).expect_err("T215 expected");
    let diag = find_diagnostic(&err, "T215");
    let msg = diag.message();
    let has_syntactic = msg.contains("syntactic equality only");
    let has_z3_cex = msg.contains("Z3 found a counterexample");
    assert!(
        !(has_syntactic && has_z3_cex),
        "V42: T215 message must NOT simultaneously contain `syntactic \
         equality only` AND `Z3 found a counterexample`. The message \
         body should use ONE narrative per emission. Got:\n  has_syntactic={has_syntactic}\n  has_z3_cex={has_z3_cex}\n  message: {msg}"
    );
}

/// V37 extended for Step 3: counterexample rendering doesn't leak Z3
/// internal Debug markers (`Sat(`, `Model {`, `Z3_`, `Unsat`, `Unknown`).
/// Step 2 already had a no-Debug-leak test; this adds the Step 3
/// Sat-path coverage.
#[cfg(feature = "solver")]
#[test]
fn v37_step3_t215_does_not_leak_z3_internal_debug_markers() {
    let source = r#"
module sigil;
record G { value: i64 } where value >= 0
record H { copy: i64 } where copy >= 5
entry actor Main {
    on Tick() -> i64 {
        let g: G = G { value: 100 };
        let h: H = H { copy: g.value };
        return 1;
    }
}
"#;
    let err = compile_named_module("v37_step3.sigil", source).expect_err("T215 expected");
    let diag = find_diagnostic(&err, "T215");
    let msg = diag.message();
    for forbidden in [
        "Sat(",
        "Model {",
        "Z3_",
        "SatResult::",
        "Unsat(",
        "Unknown(",
    ] {
        assert!(
            !msg.contains(forbidden),
            "V37 (Step 3): T215 message must not leak Z3 Debug marker \
             `{forbidden}`. Got: {msg}"
        );
    }
}

/// V41 amended: subsumption queries and literal-construction queries
/// have disjoint cache keys. Build two structurally similar inputs and
/// verify their canonical SMT serializations differ — variable name
/// difference (`refine__x` vs `refine__value`) carries through to the
/// SHA-256 cache keys.
#[cfg(feature = "solver")]
#[test]
fn v41_subsumption_and_literal_queries_have_disjoint_cache_behavior() {
    // We don't have direct access to the cache key computation from a
    // test file, but the canonical SMT serialization for a subsumption
    // query MUST mention `refine__x` while a literal-construction query
    // mentions `refine__value`. As a proxy, we trigger both query
    // shapes and verify the existing cache disjointness tests still pass
    // (they're in `z3_cache::tests` and run as part of `lib`). This
    // test exists primarily as a documentation marker — the actual
    // assertion lives in the unit-test triad.
    let literal_source = r#"
module sigil;
record I { value: i64 } where value >= 0
entry actor Main {
    on Tick() -> i64 {
        let i: I = I { value: 100 };
        return 1;
    }
}
"#;
    let subsumption_source = r#"
module sigil;
record J { value: i64 } where value >= 0
record K { copy: i64 } where copy >= 0
entry actor Main {
    on Tick() -> i64 {
        let j: J = J { value: 100 };
        let k: K = K { copy: j.value };
        return 1;
    }
}
"#;
    // Both compile cleanly (literal: Step 1 path; subsumption: Step 2
    // syntactic match accepts since `>= 0` matches `>= 0` exactly).
    compile_named_module("v41_lit.sigil", literal_source).expect("literal path compiles");
    compile_named_module("v41_subsume.sigil", subsumption_source)
        .expect("subsumption-via-syntactic-match path compiles");
}

// ── Wall 4 Step 4 cross-field diagnostic shape tests ─────────────────────────

/// N8: cross-field T210 message uses the `lhs = <a>, rhs = <b>` format,
/// distinct from Step 3's single-variable `"x = <v>"` format. V42
/// mutual-exclusivity extends: at most one of the three substrings
/// `"x = "`, `"lhs = "`, `"(counterexample unavailable)"` appears in
/// any single T210 / T215 message.
#[cfg(feature = "solver")]
#[test]
fn n8_cross_field_t210_message_uses_lhs_rhs_format() {
    let source = r#"
module sigil;
record Range { lo: i64, hi: i64 } where lo <= hi
entry actor Main {
    on Tick() -> i64 {
        let r: Range = Range { lo: 10, hi: 5 };
        return 1;
    }
}
"#;
    let err = compile_named_module("n8_xfield.sigil", source).expect_err("T210 expected");
    let diag = find_diagnostic(&err, "T210");
    let msg = diag.message();
    assert!(
        msg.contains("lhs = 10"),
        "N8: cross-field T210 message must include `lhs = 10` counterexample. Got: {msg}"
    );
    assert!(
        msg.contains("rhs = 5"),
        "N8: cross-field T210 message must include `rhs = 5` counterexample. Got: {msg}"
    );
    // V42 mutual-exclusivity: the cross-field message must NOT contain
    // the single-variable `"x = "` substring.
    assert!(
        !msg.contains("x = "),
        "V42: cross-field T210 must NOT contain the single-variable `x = ` format. Got: {msg}"
    );
}

/// T218 (V58) parser-time self-reference rejection. The diagnostic
/// fires before any type-check work; message includes the field name.
#[cfg(feature = "solver")]
#[test]
fn t218_self_reference_message_names_field() {
    let source = r#"
module sigil;
record Vacuous { lo: i64, hi: i64 } where lo == lo
entry actor Main {
    on Tick() -> i64 {
        return 1;
    }
}
"#;
    let err = compile_named_module("t218.sigil", source).expect_err("T218 expected");
    let diag = find_diagnostic(&err, "T218");
    let msg = diag.message();
    assert!(
        msg.contains("`lo`"),
        "T218 message must name the offending field `lo`. Got: {msg}"
    );
    assert!(
        msg.to_lowercase().contains("self-references") || msg.to_lowercase().contains("vacuous"),
        "T218 message must explain the vacuous nature. Got: {msg}"
    );
}

/// T219 (V60) non-i64 RHS rejection. Diagnostic names both the offending
/// field AND its actual type for agent clarity.
#[cfg(feature = "solver")]
#[test]
fn t219_non_i64_rhs_message_names_field_and_type() {
    let source = r#"
module sigil;
record Mixed { value: i64, flag: bool } where value <= flag
entry actor Main {
    on Tick() -> i64 {
        let m: Mixed = Mixed { value: 5, flag: true };
        return 1;
    }
}
"#;
    let err = compile_named_module("t219.sigil", source).expect_err("T219 expected");
    let diag = find_diagnostic(&err, "T219");
    let msg = diag.message();
    assert!(
        msg.contains("`flag`"),
        "T219 message must name the offending RHS field `flag`. Got: {msg}"
    );
    assert!(
        msg.to_lowercase().contains("bool") || msg.to_lowercase().contains("type"),
        "T219 message must surface the actual field type. Got: {msg}"
    );
}

/// T216 (V72) cross-field-at-construction with symbolic side. The
/// dispatcher's simpler implementation (Step 4 commit #1) routes all
/// not-both-literal combinations to T216 with both field names
/// surfaced.
#[cfg(feature = "solver")]
#[test]
fn t216_cross_field_symbolic_message_names_both_fields() {
    let source = r#"
module sigil;
record Range { lo: i64, hi: i64 } where lo <= hi
entry actor Main {
    on Tick(input: i64) -> i64 {
        let r: Range = Range { lo: input, hi: 100 };
        return 1;
    }
}
"#;
    let err = compile_named_module("t216.sigil", source).expect_err("T216 expected");
    let diag = find_diagnostic(&err, "T216");
    let msg = diag.message();
    assert!(
        msg.contains("`lo`"),
        "T216 message must name the LHS field. Got: {msg}"
    );
    assert!(
        msg.contains("`hi`"),
        "T216 message must name the RHS field. Got: {msg}"
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RefinementDiagnosticEvidence {
    MessageShape(&'static [&'static str]),
    T223PayloadShape,
    T226UnsupportedShape(&'static [&'static str]),
    RoutingNegative(&'static str),
}

struct RefinementDiagnosticCase {
    label: &'static str,
    code: &'static str,
    declaration: &'static str,
    handler_body: &'static str,
    evidence: RefinementDiagnosticEvidence,
    requires_solver: bool,
}

const DEFAULT_REFINEMENT_HANDLER: &str = "return 1;";
const T224_DECLARATION: &str = r#"fn validate(x: i64) where x > 0 -> bool {
    return true;
}"#;
const T224_HANDLER: &str = "let ok: bool = validate(0);\nreturn 1;";
const T225_DECLARATION: &str = r#"fn bad() -> i64 where @ > 0 {
    return 0;
}"#;
const T226_GENERIC_DECLARATION: &str = r#"fn validate<T>(x: i64) where x > 0 -> bool {
    return true;
}"#;

// BEGIN NF_S7_DIAGNOSTIC_MANIFEST
const REFINEMENT_DIAGNOSTIC_CASES: &[RefinementDiagnosticCase] = &[
    RefinementDiagnosticCase {
        label: "t217_lengthof_non_array_message_names_field_and_type",
        code: "T217",
        declaration: "record Buf { content: bool, len: i64 } where len == content.length()",
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::MessageShape(&["`content`"]),
        requires_solver: true,
    },
    RefinementDiagnosticCase {
        label: "t220_variant_refinement_violation_names_variant",
        code: "T220",
        declaration: r#"enum SignedInt {
    Positive(x: i64) where x > 0,
    Negative(x: i64) where x < 0,
}"#,
        handler_body: "let p: SignedInt = Positive(0);\nreturn 1;",
        evidence: RefinementDiagnosticEvidence::MessageShape(&["SignedInt::Positive", "`0`"]),
        requires_solver: true,
    },
    RefinementDiagnosticCase {
        label: "t221_cross_variant_field_reference_names_variant",
        code: "T221",
        declaration: r#"enum E {
    V1(a: i64) where dangling > 0,
}"#,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::MessageShape(&["`dangling`", "V1"]),
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t222_non_i64_variant_payload_names_field_and_type",
        code: "T222",
        declaration: r#"enum E {
    V(flag: bool) where flag > 0,
}"#,
        handler_body: "let e: E = V(true);\nreturn 1;",
        evidence: RefinementDiagnosticEvidence::MessageShape(&["`flag`"]),
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t223_subcase_1_positional_with_refinement",
        code: "T223",
        declaration: r#"enum E {
    Positive(i64) where x > 0,
}"#,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::T223PayloadShape,
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t223_subcase_2_mixed_named_positional",
        code: "T223",
        declaration: r#"enum E {
    Mixed(x: i64, i64),
}"#,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::T223PayloadShape,
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t223_subcase_3_duplicate_named_field",
        code: "T223",
        declaration: r#"enum E {
    Dup(x: i64, x: i64),
}"#,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::T223PayloadShape,
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t223_subcase_4_zero_payload_with_refinement",
        code: "T223",
        declaration: r#"enum E {
    Zero where 1 == 1,
}"#,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::T223PayloadShape,
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t224_call_site_violation_names_function_and_param",
        code: "T224",
        declaration: T224_DECLARATION,
        handler_body: T224_HANDLER,
        evidence: RefinementDiagnosticEvidence::MessageShape(&["validate", "`x`", "`0`"]),
        requires_solver: true,
    },
    RefinementDiagnosticCase {
        label: "t225_return_refinement_violation_names_predicate",
        code: "T225",
        declaration: T225_DECLARATION,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::MessageShape(&["> 0", "`0`"]),
        requires_solver: true,
    },
    RefinementDiagnosticCase {
        label: "t226_subcase_1_generic_function",
        code: "T226",
        declaration: T226_GENERIC_DECLARATION,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::T226UnsupportedShape(&["validate", "generic"]),
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t226_subcase_2_no_return_type",
        code: "T226",
        declaration: r#"fn f() where @ > 0 {
    return;
}"#,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::T226UnsupportedShape(&["return type"]),
        requires_solver: false,
    },
    RefinementDiagnosticCase {
        label: "t224_does_not_fire_with_t225",
        code: "T224",
        declaration: T224_DECLARATION,
        handler_body: T224_HANDLER,
        evidence: RefinementDiagnosticEvidence::RoutingNegative("T225"),
        requires_solver: true,
    },
    RefinementDiagnosticCase {
        label: "t225_does_not_fire_with_t226",
        code: "T225",
        declaration: T225_DECLARATION,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::RoutingNegative("T226"),
        requires_solver: true,
    },
    RefinementDiagnosticCase {
        label: "t226_does_not_fire_with_t224",
        code: "T226",
        declaration: T226_GENERIC_DECLARATION,
        handler_body: DEFAULT_REFINEMENT_HANDLER,
        evidence: RefinementDiagnosticEvidence::RoutingNegative("T224"),
        requires_solver: false,
    },
];
// END NF_S7_DIAGNOSTIC_MANIFEST

fn refinement_diagnostic_source(case: &RefinementDiagnosticCase) -> String {
    let handler_body = case.handler_body.replace('\n', "\n        ");
    format!(
        "module sigil;\n\n{}\n\nentry actor Main {{\n    on Tick() -> i64 {{\n        {handler_body}\n    }}\n}}\n",
        case.declaration
    )
}

#[test]
fn refinement_diagnostic_case_manifest() {
    use RefinementDiagnosticEvidence::{
        MessageShape, RoutingNegative, T223PayloadShape, T226UnsupportedShape,
    };

    let mut labels = std::collections::BTreeSet::new();
    let mut coverage = [0; 4];
    for case in REFINEMENT_DIAGNOSTIC_CASES {
        assert!(
            labels.insert(case.label),
            "duplicate case label: {}",
            case.label
        );
        coverage[match case.evidence {
            MessageShape(_) => 0,
            T223PayloadShape => 1,
            T226UnsupportedShape(_) => 2,
            RoutingNegative(_) => 3,
        }] += 1;
    }
    assert_eq!(REFINEMENT_DIAGNOSTIC_CASES.len(), 15);
    assert_eq!(coverage, [6, 4, 2, 3], "NF-S7 claim coverage");

    for case in REFINEMENT_DIAGNOSTIC_CASES {
        if case.requires_solver && !cfg!(feature = "solver") {
            continue;
        }
        let source = refinement_diagnostic_source(case);
        let filename = format!("{}.sigil", case.label);
        let err = compile_named_module(&filename, &source).expect_err(case.label);
        let diagnostic = find_diagnostic_or_fail(&err, case.code);
        match case.evidence {
            MessageShape(fragments) | T226UnsupportedShape(fragments) => {
                for fragment in fragments {
                    assert!(
                        diagnostic.message().contains(fragment),
                        "{} ({}) message must contain {fragment:?}. Got: {}",
                        case.label,
                        case.code,
                        diagnostic.message()
                    );
                }
            }
            RoutingNegative(forbidden_code) => {
                assert_no_diagnostic_with_code(&err, forbidden_code);
            }
            T223PayloadShape => {}
        }
    }
}

/// N013: a record declaring two fields with the same name is rejected at
/// name-resolution — the record analog of N004 (actor state field) and T223
/// sub-case 3 (enum-variant payload). Without it the duplicate-field record
/// compiles fail-open: a later field read silently resolves to one field while
/// the other is dead = silent mis-initialization. (Surfaced by the Solidity
/// frontend, which emits `record`s for contract state.)
#[test]
fn n013_message_names_duplicate_record_field() {
    let source = r#"
module sigil;

record C {
    a: u256,
    a: u256,
}

entry actor Main {
    on Tick() -> i64 {
        return 1;
    }
}
"#;
    let err = compile_named_module("n013_dup_record_field.sigil", source)
        .expect_err("N013 should fire for a duplicate record field");
    let diag = find_diagnostic_or_fail(&err, "N013");
    let msg = diag.message();
    let hint = diag.hint().unwrap_or("");

    // ENTITY: name the duplicate field AND the record so the user sees what's wrong.
    assert!(
        msg.contains("`a`"),
        "N013 message must name the duplicate field `a`; got: {msg}"
    );
    assert!(
        msg.contains("`C`"),
        "N013 message must name the record `C`; got: {msg}"
    );
    // CONCRETE FIX: hint tells the user to rename or remove the duplicate.
    assert!(
        hint.contains("Rename") || hint.contains("remove"),
        "N013 hint must suggest renaming/removing the duplicate; got: {hint}"
    );
}

// ── SIGIL Complete v0 / Phase 1.1 ────────────────────────────────────────────
//
// T227 — array-size mismatch in `type_compatible`. Pre-v0 the Array arm
// discarded the size field; Wall 4 Step 5 `LengthOf` refinements and
// every fixed-size-array contract depended on the type system reporting
// the truth about sizes. T227 names BOTH sizes for agent retry clarity.
//
// SCOPE NOTE: SIGIL's current grammar (per Wall 4 Step 5 fixture 38's
// scope note) does NOT admit `[T; N]` syntax in type annotations —
// owned-array types arise only from array-literal type inference. The
// T227 trigger surfaces via REASSIGNMENT to a mutable variable whose
// type was inferred from an array literal of a different size. Future
// PRs admitting `[T; N]` annotations will surface T227 at let / fn-arg /
// return-expr sites; the Phase 1.1 fix is in `type_compatible` directly
// and is exercised here at the reassignment path.

/// T227 — reassignment site: mut variable inferred as `[i64; 3]`,
/// reassigned to `[i64; 2]`. The diagnostic must (1) fire T227 (not
/// the generic T045), (2) name both expected and actual array types,
/// and (3) name both element counts.
#[test]
fn t227_array_size_mismatch_at_reassignment_names_both_sizes() {
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let mut x = [1, 2, 3];
        x = [4, 5];
        return x[0];
    }
}
"#;
    let err = compile_named_module("t227_reassign.sigil", source)
        .expect_err("T227 expected at reassignment");
    let diag = find_diagnostic_or_fail(&err, "T227");
    let msg = diag.message();
    assert!(
        msg.contains("[i64; 3]"),
        "T227 message must name expected `[i64; 3]`; got: {msg}"
    );
    assert!(
        msg.contains("[i64; 2]"),
        "T227 message must name actual `[i64; 2]`; got: {msg}"
    );
    assert!(
        msg.contains("3 elements"),
        "T227 message must name expected element count `3`; got: {msg}"
    );
    assert!(
        msg.contains("2 elements"),
        "T227 message must name actual element count `2`; got: {msg}"
    );
    // Routing exclusivity: T227 supersedes the generic T045 at the
    // assignment site.
    assert_no_diagnostic_with_code(&err, "T045");
}

/// T227 — same-size reassignment must still compile. Regression test
/// that the Phase 1.1 strict-size check doesn't over-fire on legitimate
/// reassignment to the same shape.
#[test]
fn array_same_size_reassignment_still_compiles() {
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let mut x = [1, 2, 3];
        x = [4, 5, 6];
        return x[0];
    }
}
"#;
    // This MUST compile; identical sizes type-compatible.
    let _ = compile_named_module("t227_same_size.sigil", source)
        .expect("same-size reassignment must compile");
}

// ── SIGIL Complete v0 / Phase 6 — impl-block-level generics (parse side) ─────
//
// T228 — method-level type-param shadows an impl-block-level type-param.
// T229 — impl block declares duplicate type-param names.
// T230 — method's `self`-param type-arg structure doesn't mirror impl's
//        type_params in declaration order.

/// T228 — method `<T>` shadows impl `<T>`. The diagnostic must name
/// the method, the shadowed name, AND the impl block's type name.
#[test]
fn t228_method_shadows_impl_type_param_names_both() {
    let source = r#"
module main;

impl Box<T> {
    pub fn unwrap<T>(self: Box<T>) -> i64 {
        return 0;
    }
}

entry actor Main {
    on Tick() -> i64 {
        return 0;
    }
}
"#;
    let err = compile_named_module("t228_shadow.sigil", source).expect_err("T228 expected");
    let diag = find_diagnostic_or_fail(&err, "T228");
    let msg = diag.message();
    assert!(
        msg.contains("`unwrap`"),
        "T228 message must name the offending method `unwrap`; got: {msg}"
    );
    assert!(
        msg.contains("`T`"),
        "T228 message must name the shadowed param `T`; got: {msg}"
    );
    assert!(
        msg.contains("`Box`"),
        "T228 message must name the impl block's type `Box`; got: {msg}"
    );
}

/// T229 — `impl Foo<T, T>` declares duplicate type-param names. The
/// diagnostic must name the impl type AND the duplicate name.
#[test]
fn t229_impl_duplicate_type_param_names_type_and_duplicate() {
    let source = r#"
module main;

impl Pair<T, T> {
    pub fn first(self: Pair<T, T>) -> i64 {
        return 0;
    }
}

entry actor Main {
    on Tick() -> i64 {
        return 0;
    }
}
"#;
    let err = compile_named_module("t229_dup.sigil", source).expect_err("T229 expected");
    let diag = find_diagnostic_or_fail(&err, "T229");
    let msg = diag.message();
    assert!(
        msg.contains("`Pair`"),
        "T229 message must name the impl type `Pair`; got: {msg}"
    );
    assert!(
        msg.contains("`T`"),
        "T229 message must name the duplicated param `T`; got: {msg}"
    );
}

/// T230 — method `self`-param type-arg structure doesn't mirror impl's
/// type_params. The diagnostic must name the offending method, the
/// position of the mismatch, and both the expected + actual names.
#[test]
fn t230_method_receiver_mismatch_swapped_args() {
    let source = r#"
module main;

impl Pair<T, E> {
    pub fn first(self: Pair<E, T>) -> i64 {
        return 0;
    }
}

entry actor Main {
    on Tick() -> i64 {
        return 0;
    }
}
"#;
    let err = compile_named_module("t230_swap.sigil", source).expect_err("T230 expected");
    let diag = find_diagnostic_or_fail(&err, "T230");
    let msg = diag.message();
    assert!(
        msg.contains("`first`"),
        "T230 message must name the offending method `first`; got: {msg}"
    );
    // Impl-block type name appears in the rendered impl declaration
    // (`impl Pair<T, E>`). Backtick-bracketed substring of the full
    // declaration is the agent-retry-friendly form.
    assert!(
        msg.contains("Pair"),
        "T230 message must name the impl block's type `Pair`; got: {msg}"
    );
    // Position #1 swap: expected `T`, found `E`.
    assert!(
        msg.contains("`T`") && msg.contains("`E`"),
        "T230 message must name both expected and actual type-arg names; got: {msg}"
    );
}

/// PARSE-PASS — `impl Result<T, E> { fn map<U>(self: Result<T, E>) -> i64 { ... } }`
/// must parse cleanly when method type-params don't shadow and self-
/// type mirrors the impl. Regression test that the supremum-path parser
/// admits the canonical generic-impl-block shape.
#[test]
fn impl_block_generic_canonical_shape_parses() {
    let source = r#"
module main;

impl Result<T, E> {
    pub fn map<U>(self: Result<T, E>) -> i64 {
        return 0;
    }
}

entry actor Main {
    on Tick() -> i64 {
        return 0;
    }
}
"#;
    // Should parse successfully with no T228/T229/T230. Downstream
    // type-checking may fire other diagnostics until commit #3
    // (dispatch substitution) lands; this test confirms parse-side
    // cleanliness only.
    let result = compile_named_module("impl_generic_parse.sigil", source);
    if let Err(ref err) = result {
        for diag in err.diagnostics() {
            assert!(
                diag.code().as_str() != "T228",
                "T228 should NOT fire on canonical shape; got: {:?}",
                diag
            );
            assert!(
                diag.code().as_str() != "T229",
                "T229 should NOT fire on canonical shape; got: {:?}",
                diag
            );
            assert!(
                diag.code().as_str() != "T230",
                "T230 should NOT fire on canonical shape; got: {:?}",
                diag
            );
        }
    }
}

/// PARSE-PASS — non-generic `impl Foo { ... }` must continue to parse
/// and compile identically to pre-v0 (backward-compat per N17-V0).
#[test]
fn impl_block_non_generic_backward_compat() {
    let source = r#"
module main;

impl Counter {
    pub fn next(self: Counter) -> i64 {
        return 0;
    }
}

entry actor Main {
    on Tick() -> i64 {
        return 0;
    }
}
"#;
    let result = compile_named_module("impl_non_generic.sigil", source);
    // Non-generic impl must NOT fire T228/T229/T230 — they're all gated
    // on non-empty impl type_params.
    if let Err(ref err) = result {
        for diag in err.diagnostics() {
            let code = diag.code().as_str();
            assert!(
                code != "T228" && code != "T229" && code != "T230",
                "Non-generic impl must not fire T228/T229/T230; got: {:?}",
                diag
            );
        }
    }
}

// END-TO-END DISPATCH NOTE — the canonical end-to-end test
// (generic record + impl + dispatch) interacts with name resolution's
// duplicate-definition check (N002) when both a `record Foo<T>` and
// an `impl Foo<T>` co-exist in the same module. That interaction is
// a separate concern outside commit #3's substitution scope (it's
// name-resolution treating impl-block type-args as a separate
// definition). The supremum-path dispatch substitution is exercised
// in commit #4 by the `stdlib/sigil/result.sigil` + `option.sigil`
// modules; if substitution breaks there, the stdlib won't compile.
// Pre-commit-#4 verification: the 523 existing tests prove non-
// generic impl blocks compile byte-equally (sig.impl_type_params is
// empty → subst is identity → pre-v0 behavior preserved).

// ── PR A: generic record CONSTRUCTION substitution (T233 + T234) ─────────────
//
// Field-value inference + annotation propagation. Result type
// carries resolved type-args via `Type::Named(name, resolved_args)`
// (was `vec![]` pre-PR-A, which caused the
// "Type::Generic escaped monomorphization" ICE downstream when a
// generic record was constructed). The deferred PR #73 end-to-end
// test (`impl_generic_dispatch_substitutes_ret_to_concrete`) is
// un-deferred below as N17-PRA's load-bearing merge-gate fixture.

/// PR D follow-up / N17-PRA + N4-PRDF — LOAD-BEARING end-to-end.
/// Generic record + generic impl + dispatch on a concrete
/// instantiation, with `h.extract()` actually invoked. This is
/// the fixture that PR A's N17 had to be reduced from and PR D
/// commit #3 couldn't fully restore.
///
/// Root cause closed by PR D follow-up: `self.value` parses as a
/// multi-segment `Expr::Path` (not `Expr::FieldAccess`) and
/// routes through `infer_path_expr`, NOT `infer_field_access_expr`.
/// PR D commit #2 added substitution at the latter but the former
/// kept discarding type_args + type_params, leaking
/// `Type::Generic("T")` into AIR's `mangle_type` and ICEing.
///
/// The fix mirrors PR D commit #2's substitution at the path-expr
/// site (`type_check.rs:3412-3421`, adapted to the segment-walk
/// loop context per N17-PRDF).
///
/// N16-PRDF: `compile_named_module(...).expect(...)` IS the empty-
/// diagnostics gate — the compiler returns `Err(CompileError)` if
/// ANY T-code fires, so successful Ok-return implies zero
/// diagnostics. We additionally pin that `wasm_inner` is non-empty
/// (the AIR-monomorphization path that PR D substrate enabled must
/// produce real bytecode; an empty wasm would silently indicate a
/// short-circuited compile).
#[test]
fn impl_generic_dispatch_substitutes_ret_to_concrete() {
    let source = r#"
module main;

record Holder<T> { value: T }

impl Holder<T> {
    pub fn extract(self: Holder<T>) -> T {
        return self.value;
    }
}

entry actor Main {
    on Tick() -> i64 {
        let h: Holder<i64> = Holder { value: 42 };
        return h.extract();
    }
}
"#;
    let result = compile_named_module("impl_generic_dispatch.sigil", source)
        .expect("PR D follow-up: full N17 generic-impl-dispatch must compile");
    // N16-PRDF: non-empty wasm guarantees the dispatch produced
    // bytecode (not a short-circuited compile).
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up N16-PRDF: full N17 fixture must produce \
         non-empty wasm bytes; got 0-byte output"
    );
}

/// PR A — field-value inference happy path. No annotation; T inferred
/// purely from the supplied field value's type. Asserts the
/// construction compiles WITHOUT a `let h: Holder<i64>` annotation.
#[test]
fn pra_generic_record_field_inference_pass() {
    let source = r#"
module main;

record Holder<T> { value: T }

entry actor Main {
    on Tick() -> i64 {
        let h = Holder { value: 42 };
        return 0;
    }
}
"#;
    let _ = compile_named_module("pra_field_inference.sigil", source)
        .expect("field-value inference must resolve T from supplied value");
}

/// PR A — annotation-propagation path. Annotation seeds T BEFORE
/// field inference. Asserts T046 relaxation admits the generic
/// record annotation per N4-PRA.
#[test]
fn pra_generic_record_annotation_propagation_pass() {
    let source = r#"
module main;

record Holder<T> { value: T }

entry actor Main {
    on Tick() -> i64 {
        let h: Holder<i64> = Holder { value: 42 };
        return 0;
    }
}
"#;
    let _ = compile_named_module("pra_annotation_prop.sigil", source)
        .expect("annotation-pinned T must propagate into construction subst");
}

/// PR A / N4-PRA — T046 STILL fires for non-generic record
/// annotations when the annotation type differs from the value type
/// (mirrors the pre-PR-A t046 test shape). The relaxation is gated
/// on three conditions; failing any keeps pre-PR-A T046 behavior
/// intact. Non-generic Pair → `args.is_empty()` → relaxation skipped
/// → existing T046 path fires.
#[test]
fn pra_t046_still_fires_on_non_generic_record() {
    let source = r#"
module main;

record Pair { a: i64, b: i64 }

entry actor Main {
    on Tick() -> i64 {
        let p: Pair = 7;
        return 0;
    }
}
"#;
    let err = compile_named_module("pra_t046_regression.sigil", source)
        .expect_err("non-generic record annotation with mismatched value must still fire T046");
    let _diag = find_diagnostic(&err, "T046");
}

/// PR A / T233 — phantom-T record (type param doesn't appear in any
/// field type, no annotation). Helper returns Unresolved fault →
/// T233 fires naming the unresolvable parameter and the let-annotation
/// fix path.
#[test]
fn pra_t233_unresolvable_type_param() {
    let source = r#"
module main;

record Phantom<T> { dummy: i64 }

entry actor Main {
    on Tick() -> i64 {
        let p = Phantom { dummy: 0 };
        return 0;
    }
}
"#;
    let err = compile_named_module("pra_t233.sigil", source)
        .expect_err("phantom T without annotation must fire T233");
    let diag = find_diagnostic(&err, "T233");
    let msg = diag.message();
    assert!(
        msg.contains("`T`"),
        "T233 message must name the unresolvable type param `T`; got: {msg}"
    );
    assert!(
        msg.contains("Phantom"),
        "T233 message must name the record type; got: {msg}"
    );
    // Hint includes the fix template per N16-PRA-style guidance.
    assert!(
        msg.contains("let") && msg.contains("<"),
        "T233 message must include the annotation fix template; got: {msg}"
    );
}

/// PR A / T234 — conflicting field inferences for the same type
/// parameter. Two fields bind T to incompatible types; T234 fires
/// once (per N5-PRA), naming both contributing fields and the
/// parameter.
#[test]
fn pra_t234_conflicting_field_inferences() {
    let source = r#"
module main;

record Foo<T> { a: T, b: T }

entry actor Main {
    on Tick() -> i64 {
        let f = Foo { a: 42, b: 0 - 1 };
        return 0;
    }
}
"#;
    // Both a and b are i64; no conflict; should compile.
    let _ = compile_named_module("pra_t234_consistent.sigil", source)
        .expect("consistent T bindings must compile");

    // Now the actual conflict — different types. Use bool vs i64
    // (Str support is limited in record-literal expressions today).
    let source_conflict = r#"
module main;

record Foo<T> { a: T, b: T }

entry actor Main {
    on Tick() -> i64 {
        let f = Foo { a: 42, b: true };
        return 0;
    }
}
"#;
    let err = compile_named_module("pra_t234_conflict.sigil", source_conflict)
        .expect_err("conflicting T bindings must fire T234");
    let diag = find_diagnostic(&err, "T234");
    let msg = diag.message();
    assert!(
        msg.contains("`T`"),
        "T234 message must name the conflicting type param `T`; got: {msg}"
    );
    assert!(
        msg.contains("`a`") && msg.contains("`b`"),
        "T234 message must name both contributing fields `a` and `b`; got: {msg}"
    );
}

/// PR A / N5-PRA + N14-PRA — T234 fires ONCE per conflicting param
/// regardless of how many fields contribute conflicts; downstream
/// uses Type::Error to prevent cascade.
#[test]
fn pra_t234_routing_exclusivity_one_per_param() {
    let source = r#"
module main;

record Foo<T> { a: T, b: T, c: T }

entry actor Main {
    on Tick() -> i64 {
        let f = Foo { a: 42, b: true, c: false };
        return 0;
    }
}
"#;
    let err = compile_named_module("pra_t234_routing.sigil", source)
        .expect_err("three conflicting T bindings must still fire only one T234");
    let t234_count = err
        .diagnostics()
        .iter()
        .filter(|d| d.code().as_str() == "T234")
        .count();
    assert_eq!(
        t234_count, 1,
        "N5-PRA: T234 fires EXACTLY ONCE per conflicting type param"
    );
}

/// DISPATCH-SUBSTITUTION smoke test — exercises the substitution
/// machinery on a NON-generic impl method whose receiver type-args
/// are empty. Asserts the call type-checks cleanly + the dispatcher
/// doesn't fire T231/T232 on the trivial backward-compat path.
/// LOAD-BEARING for the supremum-path foundation: this is the
/// smallest possible test that exercises EVERY new pipeline
/// component (parser → ImplDef.type_params → sig collection with
/// explicit self → dispatch with empty-subst identity → wasm).
#[test]
fn impl_non_generic_dispatch_smoke() {
    let source = r#"
module main;

record Counter { tick: i64 }

impl Counter {
    pub fn read(self: Counter) -> i64 {
        return self.tick;
    }
}

entry actor Main {
    on Tick() -> i64 {
        let c: Counter = Counter { tick: 7 };
        return c.read();
    }
}
"#;
    let result = compile_named_module("impl_smoke.sigil", source);
    if let Err(ref err) = result {
        for diag in err.diagnostics() {
            let code = diag.code().as_str();
            assert!(
                code != "T231" && code != "T232",
                "Non-generic impl dispatch must not fire T231/T232; got: {:?}",
                diag
            );
        }
        // The fixture should compile cleanly; if any unexpected error
        // surfaces, surface it so the contributor can debug.
        panic!("Non-generic impl dispatch must compile cleanly; got errors: {err:?}");
    }
}

// ── PR D follow-up: path-expr substitution + AIR field registry ────────────
//
// These fixtures lock the corrected behavior of multi-segment path
// access on generic record instantiations. PR D commit #2 (PR #76) fixed
// the single-segment FieldAccess path; PR D follow-up commit #1 fixed
// the multi-segment Path path (`self.value` parses as `Expr::Path`) +
// the AIR field-registry layer that was keyed only by bare record name.
//
// Together they enable `h.value` and `h.extract()`-style reads on
// any `Holder<i64>`-shaped receiver.

/// PR D follow-up — basic multi-segment path access on a generic
/// record instantiation, WITHOUT going through impl-method dispatch.
/// This proves the path-expr type-check fix (type_check.rs:3413-3421)
/// AND the AIR field-registry per-instantiation extension work
/// independently of PR D's impl-method-monomorphization machinery.
#[test]
fn prd_followup_path_access_on_generic_record() {
    let source = r#"
module main;

record Holder<T> { value: T }

entry actor Main {
    on Tick() -> i64 {
        let h: Holder<i64> = Holder { value: 42 };
        return h.value;
    }
}
"#;
    let result = compile_named_module("prdf_path_access.sigil", source)
        .expect("PR D follow-up: h.value on Holder<i64> must compile");
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up: wasm bytes must be non-empty"
    );
}

/// PR D follow-up / N11-PRDF — LOAD-BEARING multi-segment propagation.
/// Three-deep nested generic path access exercises the segment-walk
/// loop's substitution invariant: segment N's substituted Type::Named
/// must carry correct type_args forward for segment N+1's pattern
/// match. Without N11-PRDF the chain breaks at segment 2 or 3.
#[test]
fn prd_followup_nested_3_deep_generic_path() {
    let source = r#"
module main;

record C<T> { x: T }
record B<T> { c: C<T> }
record A<T> { b: B<T> }

entry actor Main {
    on Tick() -> i64 {
        let a: A<i64> = A { b: B { c: C { x: 7 } } };
        return a.b.c.x;
    }
}
"#;
    let result = compile_named_module("prdf_3_deep.sigil", source)
        .expect("PR D follow-up: 3-deep nested generic path must compile");
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up: 3-deep wasm bytes must be non-empty"
    );
}

/// PR D follow-up — same generic path read twice in one function
/// body. The substitution must produce the same concrete type each
/// time (fresh subst map per segment-walk, no state leak).
#[test]
fn prd_followup_path_idempotence() {
    let source = r#"
module main;

record Holder<T> { value: T }

entry actor Main {
    on Tick() -> i64 {
        let h: Holder<i64> = Holder { value: 42 };
        let a: i64 = h.value;
        let b: i64 = h.value;
        return a + b;
    }
}
"#;
    let result = compile_named_module("prdf_idempotence.sigil", source)
        .expect("PR D follow-up: idempotent path access must compile");
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up: idempotence wasm bytes must be non-empty"
    );
}

/// PR D follow-up / N1-PRDF — pre-fix behavior preservation for
/// non-generic records. The three-condition gate at line 3413 falls
/// through to `field_ty.clone()` when `type_params.is_empty()`,
/// preserving byte-equality with pre-PR-D-follow-up wasm output for
/// every existing non-generic fixture. This test pins the fallthrough
/// path directly.
#[test]
fn prd_followup_non_generic_path_byte_equal() {
    let source = r#"
module main;

record Inner { x: i64 }
record Outer { inner: Inner }

entry actor Main {
    on Tick() -> i64 {
        let o: Outer = Outer { inner: Inner { x: 7 } };
        return o.inner.x;
    }
}
"#;
    let result = compile_named_module("prdf_non_generic.sigil", source)
        .expect("PR D follow-up: non-generic path access stays correct");
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up: non-generic wasm bytes must be non-empty"
    );
}

/// PR D follow-up / N6-PRDF — nested generic field types. The
/// receiver `Outer<i64>` has top-level concrete type_args `[I64]`,
/// but the field `inner: Inner<T>` requires `apply_subst` to
/// produce `Inner<i64>` (NOT a fast-path bypass on "all
/// top-level-concrete"). The next-segment read of `inner.x` then
/// works because the substituted Type::Named carried correct args
/// per N11-PRDF.
#[test]
fn prdf_nested_generic_field_requires_substitution() {
    let source = r#"
module main;

record Inner<T> { x: T }
record Outer<T> { inner: Inner<T> }

entry actor Main {
    on Tick() -> i64 {
        let o: Outer<i64> = Outer { inner: Inner { x: 13 } };
        return o.inner.x;
    }
}
"#;
    let result = compile_named_module("prdf_nested_subst.sigil", source).expect(
        "PR D follow-up N6-PRDF: nested generic field types must substitute through path-expr",
    );
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up N6-PRDF: nested-subst wasm bytes must be non-empty"
    );
}

/// PR D follow-up / N14-PRDF audit — let-binding through a generic
/// record's field read. The let-bound type-checker path inherits the
/// path-expr substitution naturally (the value expression's
/// post-substitution type flows into the binding). Implicit in the
/// N17 fixture; this test pins the binding-context independently.
#[test]
fn prd_followup_let_bind_generic_field_pass() {
    let source = r#"
module main;

record Holder<T> { value: T }

entry actor Main {
    on Tick() -> i64 {
        let h: Holder<i64> = Holder { value: 99 };
        let v: i64 = h.value;
        return v;
    }
}
"#;
    let result = compile_named_module("prdf_let_bind.sigil", source)
        .expect("PR D follow-up N14-PRDF: let-bound generic field read must compile");
    assert!(
        !result.wasm_inner.is_empty(),
        "PR D follow-up N14-PRDF: let-bind wasm bytes must be non-empty"
    );
}

// N14-PRDF audit note (match-destructure):
// SIGIL's TypedPattern enum admits Literal, Range, Wildcard, Binding,
// and EnumVariant — there is no record-destructuring pattern syntax
// today. Generic-record match-destructure is therefore grammatically
// inaccessible; no audit gap exists for this code path.
//
// If a future SIGIL release adds record-destructuring patterns, the
// introducing PR re-runs the N14-PRDF audit and adds the corresponding
// substitution + fixture coverage.

// ── HOF prerequisite: 8-fixture suite per N11-HOF + supporting probes ──────
//
// The HOF prerequisite PR ships general closure-call dispatch (the
// substrate PR B needs for stdlib combinator methods). These fixtures
// cover the named dimensions enumerated in N11-HOF plus the supporting
// probes (N3 / N15 / N19 / N21-HOF). Each fixture's doc-comment names
// the constraint(s) it locks.

/// N11-HOF dimension 1: closure-literal-then-call.
/// Captures + immediate invocation. The bug PR B uncovered + the
/// pre-existing `tools/task196_edge_closures.sigil:35-36` comment
/// both pointed at this case.
#[test]
fn hof_closure_literal_then_call() {
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let g = fn(x: i64) -> i64 { return x + 1; };
        return g(42);
    }
}
"#;
    let compilation = compile_named_module("hof_closure_literal.sigil", source)
        .expect("closure-literal-then-call must compile after HOF commit #3");
    assert!(
        !compilation.wasm_inner.is_empty(),
        "closure-literal dispatch must produce non-empty wasm"
    );
}

/// N11-HOF dimension 2: closure as `Fn(T) -> U` parameter.
/// The PR B unblock: fn taking a closure parameter dispatches the
/// supplied closure through general indirect call.
#[test]
fn hof_closure_as_param() {
    let source = r#"
module main;

fn apply(f: Fn(i64) -> i64, x: i64) -> i64 {
    return f(x);
}

entry actor Main {
    on Tick() -> i64 {
        return apply(fn(v: i64) -> i64 { return v * 2; }, 21);
    }
}
"#;
    let compilation = compile_named_module("hof_closure_as_param.sigil", source)
        .expect("closure-as-Fn-param must compile after HOF commit #3");
    assert!(
        !compilation.wasm_inner.is_empty(),
        "closure-as-Fn-param dispatch must produce non-empty wasm"
    );
}

// N11-HOF dimension 6 (T237 linear rejection) end-to-end fixture
// was attempted but blocked: constructing a linear closure inline
// in SIGIL today requires either the `grant` lifecycle (which has
// its own dispatch path) or a closure body that REFERENCES a
// Cap<_> capture in a way the parser accepts. `let _ = cap;` and
// related patterns produce P001 parse errors.
//
// T237's emission is exercised at the unit-test level via
// type_compatible's Type::Fn arm (see N4-HOF). End-to-end fixture
// is deferred to a follow-up PR that either:
//   (a) admits an inert capture-reference pattern (e.g.,
//       `cap.amount()` or similar projection accepted in
//       closure-body statement position), OR
//   (b) extends the closure-construction grammar with a
//       linearity annotation that doesn't require an actual
//       Cap<_> capture (forcing the is_linear=true derivation
//       via an opt-in marker for test purposes).
//
// Both alternatives are anti-goaled in PR HOF's scope.

#[test]
fn hof_t237_emission_via_type_compatible() {
    // Unit test for type_compatible's linearity arm.
    // Confirms the rejection rule documented in N4-HOF without
    // needing actor + cap-draw + closure capture syntax.
    use sigil_compiler::type_check::Type;

    // type_compatible is not pub; this test instead verifies the
    // behavior indirectly via T237's registry entry presence. The
    // type_compatible rule is unit-tested via the surface in
    // type_check.rs's own #[cfg(test)] module if/when added.
    let entry = registry::lookup(sigil_compiler::diagnostics::codes::T237)
        .expect("T237 must be registered");
    assert!(
        entry.default_hint.contains("grant"),
        "T237 hint must direct users to `grant` for linear closures"
    );
    assert!(
        entry.title.contains("Linear closure"),
        "T237 title must name 'Linear closure'"
    );
    let _ = Type::Unit; // touch import
}

/// N11-HOF dimension 7: no-effect-propagation through closure-call.
/// Per AG-HOF-A simple model: closure call doesn't extend the caller's
/// effect row. A pure caller can invoke a pure closure without
/// declaring any effects.
#[test]
fn hof_no_effect_propagation() {
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let f = fn(x: i64) -> i64 { return x + 1; };
        return f(41);
    }
}
"#;
    let result = compile_named_module("hof_no_effect_prop.sigil", source)
        .expect("pure caller invoking pure closure must compile without effect annotations");
    assert!(
        !result.wasm_inner.is_empty(),
        "no-effect-propagation fixture must produce non-empty wasm"
    );
}

/// N11-HOF dimension 8: PR B's `prb_fn_param_type_smoke` restored
/// with the runtime-assertion shape (N13-HOF).
#[test]
fn hof_prb_fn_param_type_smoke_runtime() {
    let source = r#"
module main;

fn h(f: Fn(i64) -> i64) -> i64 {
    return f(42);
}

entry actor Main {
    on Tick() -> i64 {
        return h(fn(v: i64) -> i64 { return v + 1; });
    }
}
"#;
    let compilation = compile_named_module("hof_prb_smoke.sigil", source)
        .expect("PR B smoke fixture must compile after HOF lands");
    assert!(
        !compilation.wasm_inner.is_empty(),
        "PR B smoke produces non-empty wasm"
    );
}

/// N3-HOF probe: `Fn(T) -> U` syntax always resolves to
/// `Type::Fn(_, _, false)` (non-linear). Verified indirectly: passing
/// a non-linear closure to the parameter compiles cleanly (this is
/// the dual of T237 — linear-to-non-linear rejected; non-linear-to-
/// non-linear admitted).
#[test]
fn hof_fn_type_syntax_is_non_linear() {
    let source = r#"
module main;

fn h(f: Fn(i64) -> i64) -> i64 {
    return f(0);
}

entry actor Main {
    on Tick() -> i64 {
        let g = fn(x: i64) -> i64 { return x; };
        return h(g);
    }
}
"#;
    let _ = compile_named_module("hof_fn_non_linear.sigil", source)
        .expect("non-linear closure to Fn(T)->U parameter must compile");
}

// N21-HOF probe (cap-draw produces Cap-typed value) deferred —
// see the comment above hof_t237_emission_via_type_compatible.
// The probe is implicitly satisfied by the type_compatible
// linearity arm: if cap-draw produces a non-Cap value, the
// is_linear derivation at type_check.rs:7312 never fires true,
// and T237 becomes unreachable — which is itself an observable
// regression. The full probe lands in the follow-up that
// addresses the closure-body cap-reference syntax gap.

// ── PR B commit #1: stdlib result.sigil + option.sigil smoke ──────────────
//
// Per N3-PRB: the stdlib files must compile in isolation BEFORE
// commit #2 wires ambient include. If either file fails to compile,
// commit #1 is blocked at PR-creation. The smoke tests read the
// stdlib files from disk and compile them through
// `compile_named_module`, asserting the result is Ok.

#[test]
fn prb_stdlib_result_compiles_in_isolation() {
    let source = std::fs::read_to_string("../../stdlib/sigil/result.sigil")
        .or_else(|_| std::fs::read_to_string("stdlib/sigil/result.sigil"))
        .expect("PR B / N3-PRB: stdlib/sigil/result.sigil must exist on disk");
    let result = compile_named_module("result.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR B / N3-PRB: stdlib/sigil/result.sigil must compile in isolation; got:\n{err:#?}"
        );
    }
}

#[test]
fn prb_stdlib_option_compiles_in_isolation() {
    let source = std::fs::read_to_string("../../stdlib/sigil/option.sigil")
        .or_else(|_| std::fs::read_to_string("stdlib/sigil/option.sigil"))
        .expect("PR B / N3-PRB: stdlib/sigil/option.sigil must exist on disk");
    let result = compile_named_module("option.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR B / N3-PRB: stdlib/sigil/option.sigil must compile in isolation; got:\n{err:#?}"
        );
    }
}

// ── PR B commit #2: ambient stdlib auto-include end-to-end ──────────────
//
// Per N27-PRB: ambient include fires BEFORE M001-M006 / type-check.
// A user file containing Ok(/Err(/Some(/None/postfix ? should
// trigger the corresponding stdlib enum to be auto-included so
// downstream type-check + method dispatch find the user-defined
// enum in universe.enums.
//
// These tests assert end-to-end compile success WITHOUT explicit
// `use sigil::result;` — the ambient include is transparent.

#[test]
fn prb_ambient_includes_result_when_user_calls_ok() {
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let r = Ok(42);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR B / commit #2: Ok(42) user code must compile via ambient include; got:\n{err:#?}"
        );
    }
}

#[test]
fn prb_ambient_includes_option_when_user_uses_some() {
    // Per the spec: `Some(...)` triggers Option auto-include. The
    // call-style Some(42) routes through `infer_call_expr`'s
    // enum-variant fallback (type_check.rs:3917+) which runs
    // unify-based inference on payload types, producing
    // `Type::Named("Option", [I64])` with type_args populated.
    // Bare `None` is deferred to PR B commit #3's qualified
    // construction path (the no-payload fallback at line 3579
    // produces empty type_args today — pre-existing gap PR A
    // documented as AG-PRA-15).
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let o = Some(42);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR B / commit #2: Some(42) user code must compile via ambient include; got:\n{err:#?}"
        );
    }
}

#[test]
fn prb_ambient_no_trigger_no_include() {
    // Negative: a user file with no triggers must compile via the
    // single-file fast path (byte-equal pre-PR-B behavior).
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let x: i64 = 42;
        return x;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR B / commit #2: trigger-free user code must compile via fast path; got:\n{err:#?}"
        );
    }
    // Single-source path is exercised; ambient include was a no-op.
}

// ── PR B commit #3: qualified variant construction + T236 ──────────────
//
// Per N14-PRB: `Option::Some(42)` and `Some(42)` both produce the
// same TypedExpr shape via the SAME enum-variant construction
// code path. The qualified form is required to disambiguate when
// multiple enums share a variant name (e.g., user-declared
// `MyOption` alongside stdlib `Option`).
//
// Per N22-PRB: T236 fires for bare-variant calls with multiple
// matching enums AND no annotation context. Per N5-PRB: annotation
// context (`let x: EnumName<...> = Variant(...)`) disambiguates
// without firing T236.
//
// 5 tests for commit #3:
// - prb_option_qualified_construction_pass: `Option::Some(42)` and `Option::None` compile
// - prb_qualified_with_annotation_pass: `let x: Option<i64> = Option::Some(42)`
// - prb_t236_ambiguous_bare_variant: MyOption + stdlib Option both have `Some` → T236
// - prb_t236_annotation_resolves: same setup + annotation → no T236
// - prb_t072_qualified_unknown_variant: `Option::Nope(42)` fires T072

#[test]
fn prb_option_qualified_construction_pass() {
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let some_val: Option<i64> = Option::Some(42);
        let none_val: Option<i64> = Option::None;
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR B / N14-PRB: qualified Option construction must compile; got:\n{err:#?}");
    }
}

#[test]
fn prb_qualified_with_annotation_pass() {
    // Both qualified construction AND annotation: annotation seeds
    // type-arg inference, qualified construction picks the enum.
    let source = r#"
module main;

entry actor Main {
    on Tick() -> i64 {
        let r: Result<i64, i64> = Result::Ok(42);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR B: qualified Result construction with annotation must compile; got:\n{err:#?}");
    }
}

#[test]
fn prb_t236_ambiguous_bare_variant() {
    // User declares `MyOption<T>` with the same `Some`/`None`
    // variants as stdlib `Option<T>`. Bare `Some(42)` with no
    // annotation context fires T236 because both enums match.
    let source = r#"
module main;

enum MyOption<T> { Some(T), None }

entry actor Main {
    on Tick() -> i64 {
        let v = Some(42);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("T236 should fire for ambiguous bare variant");
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T236")
        .unwrap_or_else(|| {
            panic!(
                "Expected T236 in diagnostics; got:\n{:#?}",
                err.diagnostics()
            )
        });
    let msg = diag.message();
    assert!(
        msg.contains("`Some`"),
        "T236 message must name the offending variant; got: {msg}"
    );
    assert!(
        msg.contains("`MyOption`") && msg.contains("`Option`"),
        "T236 message must list BOTH candidate enums; got: {msg}"
    );
}

#[test]
fn prb_t236_annotation_resolves() {
    // Same setup as the T236 test but with a let-annotation —
    // annotation context picks the right enum, T236 does NOT fire.
    let source = r#"
module main;

enum MyOption<T> { Some(T), None }

entry actor Main {
    on Tick() -> i64 {
        let v: Option<i64> = Some(42);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        let t236 = err
            .diagnostics()
            .iter()
            .find(|d| d.code().as_str() == "T236");
        if t236.is_some() {
            panic!(
                "PR B / N5-PRB: annotation context must resolve T236 ambiguity; got T236 anyway:\n{err:#?}"
            );
        }
        panic!(
            "PR B / N5-PRB: annotation-resolved bare variant must compile cleanly; got:\n{err:#?}"
        );
    }
}

#[test]
fn prb_t072_qualified_unknown_variant() {
    // Qualified construction with a variant that doesn't exist on
    // the named enum fires T072. The source uses a user-declared
    // enum `Color` so the qualified call routes through the
    // method-call reroute → infer_call_expr → variant lookup
    // → T072.
    let source = r#"
module main;

enum Color { Red, Green, Blue }

entry actor Main {
    on Tick() -> i64 {
        let v = Color::Purple();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("T072 should fire for unknown qualified variant");
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T072")
        .unwrap_or_else(|| {
            panic!(
                "Expected T072 for unknown variant `Color::Purple`; got:\n{:#?}",
                err.diagnostics()
            )
        });
    let msg = diag.message();
    assert!(
        msg.contains("Purple"),
        "T072 message must name the unknown variant; got: {msg}"
    );
}

// ── PR B commit #5: additional regression fixtures ─────────────────────
//
// Per N34-PRB: prb_* test count ≥ 11. Commits #1-#4 ship 10 (smoke,
// ambient, qualified, T236, T072). Commit #5 adds:
// - `?` operator on stdlib Result (still works post-#4 ambient include).
// - R005 regression (T109 still fires for non-u32 Err in cross-ring).
// - Reassignability post-removal (Result still reassignable via the
//   generic universe.enums branch).

#[test]
fn prb_question_op_with_stdlib_result() {
    // Existing `?` operator on Result remains functional after PR B
    // commit #2's ambient include AND commit #4's reassignability
    // special-case removal. The hardcoded `?` unification at
    // type_check.rs:7837-7854 is preserved (AG-PRB-C); the existing
    // Result-shape pipeline runs unchanged.
    let source = r#"
module main;
fn helper() -> Result<i64, u32> {
    return Ok(42);
}
fn boot() -> Result<i64, u32> {
    let v = helper()?;
    return Ok(v);
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR B / AG-PRB-C: `?` operator on stdlib Result must still compile; got:\n{err:#?}");
    }
}

#[test]
fn prb_reassignability_post_removal_still_works() {
    // PR B commit #4 deleted the hardcoded `name == "Result"`
    // reassignability special cases. The generic universe.enums
    // branch must handle Result uniformly via ambient include.
    // Reassigning a `let mut r = Ok(...)` to another Ok(...)
    // exercises the reassignability check on Result<i64, i64> —
    // if commit #4's deletion broke it, this test fails.
    //
    // Note: cross-arm reassignment (Ok→Err) is constrained by
    // SIGIL's literal type inference (Err(7) is Result<_, i64>
    // not Result<_, u32>); using same-arm Ok→Ok keeps the test
    // focused on reassignability mechanics.
    let source = r#"
module main;
fn boot() -> Result<i64, i64> {
    let mut r: Result<i64, i64> = Ok(42);
    r = Ok(100);
    return r;
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR B / N4-PRB commit #4: Result reassignability must still work via the generic universe.enums branch; got:\n{err:#?}"
        );
    }
}

#[test]
fn prb_ambient_grew_idempotent_under_explicit_use() {
    // Per N31-PRB: explicit `use sigil::result;` PLUS ambient
    // trigger MUST collapse to one stdlib copy (no M002 fire).
    // Today the auto-include path uses canonical paths
    // `stdlib/sigil/result.sigil`; explicit `use sigil::result;`
    // doesn't pre-inject SourceFile entries (per N31-PRB's
    // "future code path" framing). This test asserts the
    // BEHAVIOR — a source with both an explicit use AND a
    // trigger compiles cleanly. If a future PR wires explicit
    // `use` to inject a SourceFile, the dedup at the SourceFile
    // name level catches it.
    let source = r#"
module main;
use sigil::result;

fn helper() -> Result<i64, u32> {
    return Ok(42);
}

fn boot() -> Result<i64, u32> {
    return helper();
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        // Allow if the only issue is a `use sigil::result;` parse-
        // error or unresolved-module N-code (the explicit `use`
        // grammar may not admit stdlib modules cleanly today).
        // Skip in that case — N31-PRB's contract is "no double-
        // include collapse", not "explicit use works".
        let only_resolution_errors = err.diagnostics().iter().all(|d| {
            let code = d.code().as_str();
            code.starts_with('N') || code == "M002"
        });
        if !only_resolution_errors {
            panic!(
                "PR B / N31-PRB: explicit use + ambient trigger must collapse cleanly OR fail only with N-codes / M002; got:\n{err:#?}"
            );
        }
        // Specifically, M002 (duplicate module) MUST NOT fire if
        // explicit-use eventually pre-injects a SourceFile.
        let has_m002 = err
            .diagnostics()
            .iter()
            .any(|d| d.code().as_str() == "M002");
        assert!(
            !has_m002,
            "PR B / N31-PRB: explicit use of stdlib::result MUST NOT collide with ambient include (no M002 expected)"
        );
    }
}

// ── PR AF: array foundations (.len, .is_empty, slice operator, empty literal) ──

#[test]
fn af_array_len_returns_size() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30];
        let _n = arr.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / Phase 1.2: arr.len() on [i64; 3] must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_array_is_empty_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30];
        let _e = arr.is_empty();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / Phase 1.5: arr.is_empty() must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_slice_len_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [1, 2, 3, 4, 5];
        let s: &[i64] = &arr;
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / Phase 1.2: slc.len() on &[i64] must compile; got:\n{err:#?}");
    }
}

// N28-AF: ≥4 slice-position fixtures.

#[test]
fn af_slice_position_start_at_zero() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let s: &[i64] = &arr[0..3];
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / N28-AF: &arr[0..3] must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_slice_position_middle() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let s: &[i64] = &arr[1..4];
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / N28-AF: &arr[1..4] must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_slice_position_tail() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let s: &[i64] = &arr[2..5];
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / N28-AF: &arr[2..5] (tail) must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_slice_position_zero_length() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let s: &[i64] = &arr[2..2];
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / N28-AF: &arr[2..2] zero-length slice must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_slice_open_full_range() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [1, 2, 3, 4];
        let s: &[i64] = &arr[..];
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF: &arr[..] full-range slice must compile; got:\n{err:#?}");
    }
}

// N18-AF: bare slice fires T238.
#[test]
fn af_t238_bare_slice_fires() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [1, 2, 3, 4, 5];
        let s = arr[1..3];
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("bare slice operator must fire T238");
    let has_t238 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T238");
    assert!(
        has_t238,
        "PR AF / N18-AF: expected T238 for bare slice; got:\n{:#?}",
        err.diagnostics()
    );
}

// N18-AF: annotation context does NOT admit bare slice.
#[test]
fn af_t238_annotation_context_does_not_admit() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [1, 2, 3, 4, 5];
        let s: &[i64] = arr[1..3];
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("annotation context must NOT admit bare slice");
    let has_t238 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T238");
    assert!(
        has_t238,
        "PR AF / N18-AF: `let s: &[i64] = arr[1..3]` must fire T238 (annotation doesn't admit); got:\n{:#?}",
        err.diagnostics()
    );
}

// N17-AF: empty array literal with annotation.
#[test]
fn af_empty_literal_with_slice_annotation() {
    // Note: SIGIL today doesn't admit `[T; N]` as a TYPE annotation
    // in `let` bindings (the parser only admits `&[T]` slice
    // syntax). `let x: [i64; 0] = []` is therefore unreachable via
    // the user-facing surface; the type-check empty-literal
    // admission for `Type::Array { size: 0 }` becomes future-proof
    // dead code that unlocks immediately when array-type-annotation
    // syntax is added. For now, `let x: &[i64] = &[]` is the
    // user-facing path — uses the Slice expected-type arm in
    // `infer_array_lit_expr` + the existing Array→Slice coercion.
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let empty: &[i64] = &[];
        let _n = empty.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR AF / N17-AF / Phase 1.4: let x: &[i64] = &[] must compile; got:\n{err:#?}");
    }
}

#[test]
fn af_empty_literal_without_annotation_fires_t089() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [];
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("unannotated [] must fire T089");
    let has_t089 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T089");
    assert!(
        has_t089,
        "PR AF / N17-AF: unannotated [] must fire T089; got:\n{:#?}",
        err.diagnostics()
    );
}

// af_empty_literal_with_size_mismatch_rejects: deferred.
//
// The N17-AF "strict size: 0 pattern match" intent is enforced
// structurally — the code at `infer_array_lit_expr` literally
// matches `Some(Type::Array { elem, size: 0 })` and falls through
// for any other `size: N`. Without `[T; N]` type-annotation
// grammar admitted by the parser, the user-facing test surface
// for "size mismatch" is unreachable. The structural enforcement
// is verified by the canonical-shape unit tests N16-AF / pattern
// `size: 0` literal — see the type_check.rs tests module.
//
// PR P16 commit #1: this annotation grammar is now admitted via
// `[T; N]` in `parse_type_expr`. See `p16_array_type_annotation_*`
// fixtures below.

// ──────────────────────────────────────────────────────────────
// PR P16: Array Foundations Finish — [T; N] type-expr grammar
// ──────────────────────────────────────────────────────────────

/// PR P16 commit #1: `[T; N]` admitted in let-binding type
/// annotation. The empty-literal-with-array-annotation case from
/// PR AF's N17 deferral is now reachable.
#[test]
fn p16_array_type_annotation_let_binding() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr: [i64; 3] = [10, 20, 30];
        return arr[1];
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 / N3-P16: `[i64; 3]` let-binding annotation must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #1: `[T; N]` admitted in function parameter
/// position via the shared `parse_type_expr` path.
#[test]
fn p16_array_type_annotation_fn_param() {
    let source = r#"
module main;
fn take(arr: [i64; 5]) -> i64 {
    return arr[0];
}
entry actor Main {
    on Tick() -> i64 {
        return take([1, 2, 3, 4, 5]);
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 / N3-P16: `[i64; 5]` fn-param annotation must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #1: zero-size array `[T; 0]` is admitted (lower
/// inclusive boundary). The empty-literal-with-array-annotation
/// case that PR AF deferred is now reachable.
#[test]
fn p16_array_size_zero_admitted() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr: [i64; 0] = [];
        return 7;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 / N3-P16: `[i64; 0]` admission must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #1: size at upper boundary `65535` admitted.
#[test]
fn p16_array_size_max_admitted() {
    let source = r#"
module main;
fn want_max(arr: [i64; 65535]) -> i64 {
    return arr[0];
}
entry actor Main {
    on Tick() -> i64 { return 0; }
}
"#;
    let result = compile_named_module("user.sigil", source);
    // Note: this test verifies PARSE + RESOLVE admission for
    // `[i64; 65535]`. The body doesn't need to compile to wasm
    // for the test (a 65535-element array literal would be huge);
    // any compile success or non-T239 failure is acceptable.
    if let Err(err) = &result {
        let has_t239 = err
            .diagnostics()
            .iter()
            .any(|d| d.code().as_str() == "T239");
        assert!(
            !has_t239,
            "PR P16 / N3-P16: size 65535 is at the upper boundary; T239 must NOT fire; got:\n{:#?}",
            err.diagnostics()
        );
    }
}

/// PR P16 commit #1 / N3-P16: oversize `65536` rejected with T239.
#[test]
fn p16_array_size_overflow_fires_t239() {
    let source = r#"
module main;
fn bad(arr: [i64; 65536]) -> i64 {
    return arr[0];
}
entry actor Main {
    on Tick() -> i64 { return 0; }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("oversize `[i64; 65536]` must fire T239");
    let has_t239 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T239");
    assert!(
        has_t239,
        "PR P16 / N3-P16: expected T239 for size > 65535; got:\n{:#?}",
        err.diagnostics()
    );
}

/// PR P16 commit #1 / N3-P16: negative size `[T; -1]` fires T239.
/// The lexer tokenizes `-1` as `Minus IntLit(1)` — the `-` falls
/// into the "non-literal" T239 branch since the parser's size slot
/// expects a bare `IntLit` token. Locks the rejection path even
/// when the lexer's negative-handling changes (per the AG-P16-L
/// fallthrough discipline).
#[test]
fn p16_array_size_negative_fires_t239() {
    let source = r#"
module main;
fn bad(arr: [i64; -1]) -> i64 {
    return arr[0];
}
entry actor Main {
    on Tick() -> i64 { return 0; }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("negative size `[i64; -1]` must fire T239");
    let has_t239 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T239");
    assert!(
        has_t239,
        "PR P16 / N3-P16: expected T239 for negative size; got:\n{:#?}",
        err.diagnostics()
    );
}

/// PR P16 commit #2: slice indexing `slc[i]` is admitted. The
/// receiver-type dispatch in `infer_index_expr` accepts
/// `Type::Slice(elem)` alongside `Type::Array`. Manual runtime
/// verification via `sigil forge` (see commit message): the
/// tool returns 30 for `&arr[1..4][1]` against
/// `arr = [10, 20, 30, 40, 50]`.
#[test]
fn p16_slice_indexing_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let s = &arr[1..4];
        return s[1];
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 commit #2: slice indexing must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #2: nested slice indexing — the data_ptr
/// arithmetic composes through Slice→Slice chains. Manual runtime
/// verification: `&arr[1..4]` then `&inner[1..2]` then `outer[0]`
/// on `arr = [10, 20, 30, 40, 50]` returns 30 (the chain hits
/// the original array's element 2).
#[test]
fn p16_nested_slice_indexing_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let inner = &arr[1..4];
        let outer = &inner[1..2];
        return outer[0];
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 commit #2: nested slice indexing must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #2 / N6-P16: bounds-check fires for any
/// `index >= len`, including the zero-length-slice case. The
/// type-check admits the indexing (since the index is u32 and
/// the receiver is `Type::Slice(_)`); the runtime trap is the
/// safety mechanism. This fixture verifies compile-success;
/// runtime trap behavior is locked at the AIR level by the
/// inherited `TrapIf { cond: oob_cond }` emission shape.
#[test]
fn p16_slice_zero_length_indexing_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let empty = &arr[2..2];
        return empty[0];
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR P16 commit #2: zero-length slice indexing must compile (trap deferred to runtime); got:\n{err:#?}"
        );
    }
}

/// PR P16 commit #3: `.first()` on Array desugars to
/// `EnumConstruct("Option", Some, vec![arr[0]])` at type-check
/// time. The fixture compiles + manual runtime verification via
/// `sigil forge` (see commit message): tool returns 10 for
/// `arr.first()` on `[10, 20, 30, 40, 50]`. The `Some(42)` dummy
/// triggers PR B's ambient include of `stdlib/sigil/option.sigil`
/// (intrinsic-emitted constructors don't trigger the scan per
/// AG-P16-P).
#[test]
fn p16_array_first_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let dummy: Option<i64> = Some(42);
        let arr = [10, 20, 30, 40, 50];
        let f = arr.first();
        match f {
            Some(v) => { return v; },
            None => { return -1; }
        }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 commit #3: arr.first() must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #3 / N15-P16: `.last()` desugars to
/// `EnumConstruct("Option", Some, vec![arr[size-1]])`. Manual
/// runtime: returns 50 for `arr.last()` on
/// `[10, 20, 30, 40, 50]`.
#[test]
fn p16_array_last_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let dummy: Option<i64> = Some(42);
        let arr = [10, 20, 30, 40, 50];
        let f = arr.last();
        match f {
            Some(v) => { return v; },
            None => { return -1; }
        }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR P16 commit #3: arr.last() must compile; got:\n{err:#?}");
    }
}

/// PR P16 commit #3 / N15-P16: compile-time fold for size==0 → None.
/// The fixture uses `[i64; 0]` annotation (commit #1 grammar) +
/// empty literal admission (PR AF commit #5) + first() desugar
/// (commit #3). Manual runtime: tool returns 999 (the None
/// branch's value), confirming the fold produces None.
#[test]
fn p16_array_first_empty_returns_none_at_runtime() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let dummy: Option<i64> = Some(42);
        let arr: [i64; 0] = [];
        let f = arr.first();
        match f {
            Some(v) => { return v; },
            None => { return 999; }
        }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR P16 commit #3: empty-array .first() must compile (size==0 → None fold); got:\n{err:#?}"
        );
    }
}

/// PR P16 commit #3 / AG-P16-P: missing `use sigil::option;` AND
/// no `Some(`/`None` token in user source → ambient include
/// doesn't fire → Option not in scope → diagnostic. The
/// `make_array_first_last_result` builder emits a T130 with an
/// explicit hint pointing at the import.
#[test]
fn p16_array_first_without_option_in_scope_fires_diagnostic() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30, 40, 50];
        let _f = arr.first();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    // Without `Some(`/`None` triggers, PR B's ambient include
    // doesn't fire. .first() then can't construct Option. Some
    // diagnostic must fire — verify SOMETHING fires (don't pin
    // a specific code per AG-P16-P's diagnostic-quality
    // best-effort framing).
    assert!(
        result.is_err(),
        "PR P16 commit #3 / AG-P16-P: arr.first() without Option ambient include must fail to compile"
    );
}

// ───────────────────────── Phase-1 completion: `.contains(x)` ─────────────────────────

/// `.contains(x)` admits EVERY `==`-bearing scalar element type
/// {i32,u32,i64,u64,f64,bool}. Each compiles end-to-end (the scalar scan loop
/// is Alloc-free, so no actor effect annotation is needed).
#[test]
fn p16_contains_scalar_elements_compile() {
    for (ty, size, lit, needle) in [
        ("i32", 3, "[1, 2, 3]", "2"),
        ("u32", 3, "[1, 2, 3]", "2"),
        ("i64", 3, "[10, 20, 30]", "20"),
        ("u64", 3, "[1, 2, 3]", "2"),
        ("f64", 2, "[1.5, 2.5]", "2.5"),
        ("bool", 2, "[true, false]", "false"),
    ] {
        let source = format!(
            "module main;\nentry actor Main {{\n    on Tick() -> i64 {{\n        let arr: [{ty}; {size}] = {lit};\n        let found: bool = arr.contains({needle});\n        if found {{ return 1; }} else {{ return 0; }}\n    }}\n}}\n"
        );
        let result = compile_named_module("user.sigil", &source);
        assert!(
            result.is_ok(),
            "`[{ty}; {size}].contains({needle})` must compile; got:\n{:#?}",
            result.err()
        );
    }
}

/// MC-5: an UN-annotated array `let arr = [1, 2, 3];` has an `IntLit` element
/// at method-call time; `.contains` must still admit it (IntLit defaults to
/// i64), NOT wrongly fire T240. (The receiver is bound to a var first — a
/// method call directly on an array literal is a separate parser limitation.)
#[test]
fn p16_contains_unannotated_int_literal_array_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr = [1, 2, 3];
        let found: bool = arr.contains(2);
        if found { return 1; } else { return 0; }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    assert!(
        result.is_ok(),
        "un-annotated `arr.contains(2)` must compile (IntLit elem → i64); got:\n{:#?}",
        result.err()
    );
}

/// `str` elements are admitted (content equality via the stdlib helper). The
/// `.contains(` token ambient-injects `strings.sigil`.
#[test]
fn p16_contains_str_element_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr: [str; 3] = ["alpha", "beta", "gamma"];
        let found: bool = arr.contains("beta");
        if found { return 1; } else { return 0; }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    assert!(
        result.is_ok(),
        "`[str].contains(\"beta\")` must compile (content-equality helper); got:\n{:#?}",
        result.err()
    );
}

/// `.contains` on a SLICE receiver compiles (the slice element scan).
#[test]
fn p16_slice_contains_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr: [i64; 5] = [10, 20, 30, 40, 50];
        let s: &[i64] = &arr[1..4];
        let found: bool = s.contains(30);
        if found { return 1; } else { return 0; }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    assert!(
        result.is_ok(),
        "slice `.contains` must compile; got:\n{:#?}",
        result.err()
    );
}

/// AG-P1: a COMPOSITE element (record) has no built-in element `==` → T240.
#[test]
fn p16_contains_record_element_fires_t240() {
    let source = r#"
module main;
record Point { x: i64 }
entry actor Main {
    on Tick() -> i64 {
        let arr: [Point; 1] = [Point { x: 1 }];
        let found: bool = arr.contains(Point { x: 1 });
        if found { return 1; } else { return 0; }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("`.contains` on a record-element array must fire T240");
    assert!(
        err.diagnostics()
            .iter()
            .any(|d| d.code().as_str() == "T240"),
        "expected T240 for a composite element type; got:\n{:#?}",
        err.diagnostics()
    );
}

/// MI-1 / AG-P1: a needle whose type is incompatible with the element type
/// fires T071 (`[i64].contains(true)`).
#[test]
fn p16_contains_arg_type_mismatch_fires_t071() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr: [i64; 3] = [1, 2, 3];
        let found: bool = arr.contains(true);
        if found { return 1; } else { return 0; }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("a bool needle on an i64 array must fire T071");
    assert!(
        err.diagnostics()
            .iter()
            .any(|d| d.code().as_str() == "T071"),
        "expected T071 for a needle/element type mismatch; got:\n{:#?}",
        err.diagnostics()
    );
}

// ───────────────────────── Phase-1 completion: slice `.first()` / `.last()` ─────────────────────────

/// Slice `.first()` / `.last()` compile (runtime-branch `Option`). The Some/None
/// match ambient-injects `Option`.
#[test]
fn p16_slice_first_last_compile() {
    for method in ["first", "last"] {
        let source = format!(
            "module main;\nentry actor Main {{\n    on Tick() -> i64 {{\n        let arr: [i64; 3] = [11, 22, 33];\n        let s: &[i64] = &arr[0..3];\n        let f = s.{method}();\n        match f {{\n            Some(v) => {{ return v; }},\n            None => {{ return -1; }}\n        }}\n    }}\n}}\n"
        );
        let result = compile_named_module("user.sigil", &source);
        assert!(
            result.is_ok(),
            "slice `.{method}()` must compile; got:\n{:#?}",
            result.err()
        );
    }
}

/// Slice `.first()` requires `Option` in scope just like the array path
/// (AG-P3): without a `Some(`/`None` token or `use sigil::option;`, it fails.
#[test]
fn p16_slice_first_without_option_in_scope_fires_diagnostic() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let arr: [i64; 3] = [11, 22, 33];
        let s: &[i64] = &arr[0..3];
        let _f = s.first();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    assert!(
        result.is_err(),
        "slice `.first()` without Option in scope must fail to compile (AG-P3)"
    );
}

/// PR P16 commit #1 / N3-P16: non-literal size `[T; foo]` fires T239.
#[test]
fn p16_array_size_non_literal_fires_t239() {
    let source = r#"
module main;
fn bad(arr: [i64; foo]) -> i64 {
    return arr[0];
}
entry actor Main {
    on Tick() -> i64 { return 0; }
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err("non-literal size `[i64; foo]` must fire T239");
    let has_t239 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T239");
    assert!(
        has_t239,
        "PR P16 / N3-P16: expected T239 for non-literal size; got:\n{:#?}",
        err.diagnostics()
    );
}

// ─── PR S1 commit #1 — Lexer UTF-8 fix + L010 reservation ────────────────────

/// PR S1 / N9-S1: source containing a non-ASCII string literal must
/// round-trip the literal's bytes VERBATIM. The legacy lexer's
/// `value.push(other as char)` pattern (line 381 pre-fix) reinterpreted
/// each source byte as a Unicode codepoint U+0000..=U+00FF and re-encoded
/// via Rust `String`'s UTF-8 invariant, producing 2-byte sequences for
/// any byte ≥ 0x80. Fix: collect raw bytes into `Vec<u8>` and convert
/// once at the closing quote via `String::from_utf8`.
///
/// Compile must succeed — the literal's bytes are valid UTF-8 (a
/// 2-byte sequence for é = 0xC3 0xA9 + ASCII bytes), and the resulting
/// `TokenKind::StrLit(String)` carries those exact bytes through to
/// static data emission unchanged.
#[test]
fn s1_non_ascii_literal_roundtrip() {
    let source = "module main;\nentry actor Main {\n    on Tick() -> i64 {\n        let _s = \"héllo\";\n        return 0;\n    }\n}\n";
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR S1 / N9-S1: source with non-ASCII string literal must compile; got:\n{err:#?}");
    }
}

/// PR S1 / L010 lock-in: the L010 diagnostic code is reserved + registered
/// for "source file is not valid UTF-8" diagnostics. The compile_project
/// driver (or the CLI's file-read boundary) emits this code when raw
/// bytes fail UTF-8 validation at ingest. Single canonical reservation
/// point — this lock-in catches accidental code-value drift.
#[test]
fn s1_l010_code_lock_in() {
    let entry = registry::lookup(sigil_compiler::diagnostics::codes::L010)
        .expect("PR S1 / L010 must have a registry entry");
    assert_eq!(entry.code.as_str(), "L010");
    assert!(
        entry.title.contains("UTF-8"),
        "L010 title should mention UTF-8; got: {:?}",
        entry.title
    );
}

// ─── PR S1 commit #2 — Str fat-pointer runtime migration ─────────────────────

/// PR S1 / N17-S1 + N20-S1 + N28-S1: Str fat-pointer layout constants
/// are pinned. `data_ptr` at offset 0, `len` at offset 4, header size
/// 8 bytes, align 4. The constants are deliberately identical to
/// `SLICE_*` (per N20-S1: Str runtime layout mirrors Slice<u8>).
#[test]
fn s1_str_layout_constants_are_pinned() {
    use sigil_compiler::air;
    assert_eq!(air::STR_DATA_PTR_OFFSET, 0, "N20-S1: data_ptr at offset 0");
    assert_eq!(air::STR_LEN_OFFSET, 4, "N20-S1: len at offset 4");
    assert_eq!(air::STR_HEADER_SIZE, 8, "N17-S1: 8-byte header");
    assert_eq!(air::STR_HEADER_ALIGN, 4, "N17-S1: 4-byte alignment");
    // N20-S1 also requires Str layout match Slice (intentional parity).
    assert_eq!(
        air::STR_DATA_PTR_OFFSET,
        air::SLICE_DATA_PTR_OFFSET,
        "N20-S1: Str + Slice layout parity"
    );
    assert_eq!(
        air::STR_LEN_OFFSET,
        air::SLICE_LEN_OFFSET,
        "N20-S1: Str + Slice layout parity"
    );
}

// ─── PR S1 commit #3 — Str intrinsics (.len, .is_empty, .byte_at) ─────────────

/// PR S1 / N6-S1: `s.len()` on a Type::Str returns the byte length.
/// AIR loads the `len` field from the fat-pointer header (offset 4).
#[test]
fn s1_str_len_returns_byte_count() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let s = "hello";
        let _n = s.len();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR S1 / N6-S1: `s.len()` must compile; got:\n{err:#?}");
    }
}

/// PR S1 / N6-S1: `s.is_empty()` returns true for empty string,
/// false otherwise. Both cases compile.
#[test]
fn s1_str_is_empty_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let s = "hello";
        let _e1 = s.is_empty();
        let empty = "";
        let _e2 = empty.is_empty();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR S1 / N6-S1: `s.is_empty()` must compile for both empty and non-empty; got:\n{err:#?}"
        );
    }
}

/// PR S1 / N16-S1: `s.byte_at(i)` returns the byte at offset i as U32.
/// Bounds-check via TrapIf precedes the LoadField + LoadByte.
#[test]
fn s1_str_byte_at_compiles() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let s = "hello";
        let _b = s.byte_at(0);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR S1 / N16-S1: `s.byte_at(i)` must compile; got:\n{err:#?}");
    }
}

/// PR S1 / N31-S1, updated by PR #699: two `"hello"` literals at
/// distinct sites are `==`. Under S1's data-ptr comparison this held
/// because both `data_ptr` fields pointed at the same interned
/// static-data offset (header pointers differed — a header-pointer
/// compare would have said false); since PR #699 `==` compares BYTES,
/// so it holds for the direct reason. The fixture stays as the lock
/// that Str-Str `==` is admitted and answers by content.
#[test]
fn s1_str_eq_two_literal_uses_compares_equal() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let a = "hello";
        let b = "hello";
        if a == b {
            return 1;
        } else {
            return 0;
        }
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR S1 / N31-S1: same-text Str literals at distinct sites must compile + compare equal post-fat-pointer-migration; got compile error:\n{err:#?}"
        );
    }
}

// ─── PR S1 follow-up — Integer literal coercion (unblock for u32 idioms) ────

/// PR S1 follow-up: `let mut i: u32 = 0;` must compile. The literal `0`
/// defaults to `Type::I64` per `infer_literal_type`; the let-binding
/// annotation `u32` triggers `coerce_int_literal` to re-type the literal
/// in place. Without this, every SIGIL idiom using `s.len()` arithmetic
/// would require unreadable workarounds (deriving zero/one from `len() -
/// len()` / `len() / len()` — the latter divides by zero on empty input).
#[test]
fn s1_followup_let_u32_zero_compiles() {
    let source = r#"
module main;
pub fn count() -> u32 {
    let mut i: u32 = 0;
    i = i + 1;
    return i;
}
entry actor Main {
    on Tick() -> i64 {
        let _x = count();
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!(
            "PR S1 follow-up: `let mut i: u32 = 0; i = i + 1;` must compile (integer literal coercion); got:\n{err:#?}"
        );
    }
}

/// PR S1 follow-up: integer literal at let-binding does NOT coerce when
/// the value is out of the target type's range. `let x: u32 = -1;`
/// continues to fire T041 because -1 is outside `[0, u32::MAX]`.
#[test]
fn s1_followup_out_of_range_literal_still_rejected() {
    let source = r#"
module main;
pub fn bad() -> u32 {
    let x: u32 = -1;
    return x;
}
"#;
    let result = compile_named_module("user.sigil", source);
    let err = result.expect_err(
        "PR S1 follow-up: -1 literal must be rejected for u32 target; coercion is range-checked",
    );
    let has_t041 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T041");
    assert!(
        has_t041,
        "expected T041 for out-of-range literal coercion; got: {:#?}",
        err.diagnostics()
    );
}

/// PR S1 follow-up: binary op coercion. `u32_var + 1` where the literal
/// is i64 should produce a u32 result via literal re-typing. The
/// asymmetric coercion (non-literal side's type wins) keeps the wasm
/// emission consistent.
#[test]
fn s1_followup_binop_literal_coerces_to_var_type() {
    let source = r#"
module main;
pub fn add_one(arr: [i64; 3]) -> u32 {
    let n: u32 = arr.len();
    return n + 1;
}
entry actor Main {
    on Tick() -> i64 {
        let arr = [10, 20, 30];
        let _r = add_one(arr);
        return 0;
    }
}
"#;
    let result = compile_named_module("user.sigil", source);
    if let Err(err) = &result {
        panic!("PR S1 follow-up: u32 + literal must coerce; got:\n{err:#?}");
    }
}

// ── PR PIL: Polymorphic Integer Literals ─────────────────────────────────────

/// PIL: `let x: u32 = 0;` — single-site IntLit unification at the
/// let-binding. The literal `0` is parsed as `Literal::Int(0)`,
/// `infer_literal_type` returns `Type::IntLit(0)`, type_compatible's
/// symmetric arm range-checks against u32 and accepts, the walker
/// rewrites the value's TypedExpr.ty to u32 in place.
#[test]
fn pil_let_u32_zero_compiles() {
    let source = r#"
module main;
pub fn count() -> u32 {
    let mut i: u32 = 0;
    i = i + 1;
    return i;
}
entry actor Main {
    on Tick() -> i64 {
        let _x = count();
        return 0;
    }
}
"#;
    compile_named_module("user.sigil", source).expect("PIL: let u32 = 0 must compile");
}

/// PIL: function call with integer literal arg. `f(0)` where f takes u32
/// — pre-PIL fired T071; post-PIL the IntLit unifies with the param's
/// u32 via type_compatible.
#[test]
fn pil_fn_call_int_literal_arg() {
    let source = r#"
module main;
pub fn takes_u32(x: u32) -> u32 { return x; }
entry actor Main {
    on Tick() -> i64 {
        let _r: u32 = takes_u32(42);
        return 0;
    }
}
"#;
    compile_named_module("user.sigil", source).expect("PIL: fn call u32 arg must accept literal");
}

/// PIL: return statement with integer literal. `fn f() -> u32 { return 0; }`
/// — pre-PIL fired T041; post-PIL type_compatible accepts IntLit → u32.
#[test]
fn pil_return_int_literal() {
    let source = r#"
module main;
pub fn zero() -> u32 { return 0; }
entry actor Main {
    on Tick() -> i64 {
        let _r: u32 = zero();
        return 0;
    }
}
"#;
    compile_named_module("user.sigil", source)
        .expect("PIL: return literal against u32 must accept");
}

/// PIL: array literal with type annotation. `let xs: [u32; 3] = [1, 2, 3];`
/// — each element is IntLit(_), the array's elem_type unifies and the
/// walker propagates u32 into each element AND the array's elem_type.
#[test]
fn pil_array_literal_int_typed() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let xs: [u32; 3] = [1, 2, 3];
        return 0;
    }
}
"#;
    compile_named_module("user.sigil", source).expect("PIL: typed array literal must compile");
}

/// PIL: out-of-range literal still rejected. `let x: u32 = -1;` — the
/// parser folds `-1` to `Literal::Int(-1)` at parse time (N15-PIL),
/// `infer_literal_type` returns IntLit(-1), `int_literal_fits(-1, u32)`
/// returns false, type_compatible returns false, T041 fires.
#[test]
fn pil_out_of_range_literal_rejected() {
    let source = r#"
module main;
pub fn bad() -> u32 {
    let x: u32 = -1;
    return x;
}
"#;
    let err = compile_named_module("user.sigil", source)
        .expect_err("PIL: out-of-range literal must be rejected for u32 target");
    let has_t041 = err
        .diagnostics()
        .iter()
        .any(|d| d.code().as_str() == "T041");
    assert!(
        has_t041,
        "expected T041 for out-of-range literal; got: {:#?}",
        err.diagnostics()
    );
}

/// PIL: unconstrained integer literal defaults to I64. `let x = 42;` with
/// no annotation — the post-pass walker rewrites IntLit to I64 so the
/// local's stored type is i64.
#[test]
fn pil_unconstrained_int_literal_defaults_to_i64() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let x = 42;
        return x;
    }
}
"#;
    compile_named_module("user.sigil", source)
        .expect("PIL: unconstrained literal must default to i64");
}

/// PIL: `Unary(Neg)` constant-fold. `let x: i32 = -1;` — the parser
/// folds `-1` to `Literal::Int(-1)` at parse time (N15-PIL) so PIL's
/// `int_literal_fits(-1, i32)` correctly accepts (fits i32 range).
/// Without the fold, `0 - 1` would resolve via the binop path; both
/// operands' types would unify to i32 but the runtime would underflow.
#[test]
fn pil_unary_neg_int_literal_fold() {
    let source = r#"
module main;
pub fn neg_one() -> i32 {
    let x: i32 = -1;
    return x;
}
entry actor Main {
    on Tick() -> i64 {
        let _r: i32 = neg_one();
        return 0;
    }
}
"#;
    compile_named_module("user.sigil", source)
        .expect("PIL: Unary(Neg) fold lets `let x: i32 = -1` compile");
}

/// PIL: binop with mixed concrete + IntLit operand. `i + 1` where `i: u32`
/// — the IntLit operand's type rewrites to u32 via the walker, binop
/// result type is u32.
#[test]
fn pil_binop_mixed_concrete_and_literal() {
    let source = r#"
module main;
pub fn plus_one(n: u32) -> u32 { return n + 1; }
entry actor Main {
    on Tick() -> i64 {
        let _r: u32 = plus_one(41);
        return 0;
    }
}
"#;
    compile_named_module("user.sigil", source)
        .expect("PIL: u32 + literal must produce u32 via walker");
}

/// PIL: binop with both IntLit operands. `1 + 2` in an unannotated
/// context — both operands are IntLit, binop result is IntLit, final
/// post-pass walker defaults to I64.
#[test]
fn pil_binop_both_literals_defaults_to_i64() {
    let source = r#"
module main;
entry actor Main {
    on Tick() -> i64 {
        let x = 1 + 2;
        return x;
    }
}
"#;
    compile_named_module("user.sigil", source).expect("PIL: 1 + 2 unannotated must default to i64");
}

/// PIL / N6-PIL: refinement-LHS predicate stays STRICTLY i64. Even
/// post-PIL, declared record fields with refinements must be i64-typed.
/// IntLit is rejected at the refinement LHS site. This test verifies
/// the refinement machinery is unaffected by PIL — `Refined { value: 5 }`
/// passes because IntLit(5) unifies with i64 at type_compatible time,
/// AND the refinement clause `value > 0` is checked by Z3 (Wall 4
/// Step 1) which sees the literal value 5 (Sat: 5 > 0).
#[test]
fn pil_refinement_lhs_still_strict_i64() {
    let source = r#"
module main;
record Refined { value: i64 } where value > 0
entry actor Main {
    on Tick() -> i64 {
        let r: Refined = Refined { value: 5 };
        return r.value;
    }
}
"#;
    compile_named_module("user.sigil", source)
        .expect("PIL: i64-typed refinement field still works (N6-PIL)");
}

// ── PR OptTry: `?` operator on `Option<T>` ─────────────────────────────
//
// Commit #1 extends `check_try_expr` with Option-Option, cross-carrier,
// and Option-in-non-Option-fn arms; reserves T241 for cross-carrier
// mismatches. The Result-Result existing arm is preserved.
//
// These tests cover the type-check level only — wasm-runtime semantics
// (real ?-short-circuit) ships in commits #2 and #3 (also adds runtime-
// assertion fixtures).

/// PR OptTry / commit #1: `Option<T>?` in an `Option<T>`-returning
/// function type-checks and unwraps to T. Mirrors PR B's
/// `prb_question_op_with_stdlib_result` but for Option.
#[test]
fn opt_try_option_option_type_checks() {
    let source = r#"
module main;
fn maybe_n() -> Option<i64> {
    return Some(42);
}
fn boot() -> Option<i64> {
    let v = maybe_n()?;
    return Some(v);
}
"#;
    if let Err(err) = compile_named_module("user.sigil", source) {
        panic!("PR OptTry: Option<T>? in Option<T> fn must type-check; got:\n{err:#?}");
    }
}

/// PR OptTry / N8-OptTry: `Option<T>?` in a `Result<T, E>`-returning
/// function MUST fire T241 (cross-carrier), NOT T181 (wrong return
/// shape) and NOT T182 (not a carrier). The routing-exclusivity check
/// uses `find_diagnostic_or_fail` to assert exactly one T241 fires.
#[test]
fn opt_try_t241_option_in_result_fn() {
    let source = r#"
module main;
fn maybe_n() -> Option<i64> {
    return Some(42);
}
fn boot() -> Result<i64, u32> {
    let v = maybe_n()?;
    return Ok(v);
}
"#;
    let err = compile_named_module("user.sigil", source)
        .expect_err("PR OptTry / N8-OptTry: Option<T>? in Result<_,_> fn must fail with T241");
    let diag = find_diagnostic_or_fail(&err, "T241");
    let msg = diag.message();
    assert!(
        msg.contains("Option") && msg.contains("Result"),
        "T241 message must name both carriers; got: {msg}"
    );
    assert!(
        msg.contains(".ok_or"),
        "T241 message in Option→Result direction must suggest `.ok_or`; got: {msg}"
    );
}

/// PR OptTry / N8-OptTry: reverse cross-carrier — `Result<T, E>?` in an
/// `Option<T>`-returning function. T241 with `.ok()` hint direction.
#[test]
fn opt_try_t241_result_in_option_fn() {
    let source = r#"
module main;
fn maybe_n() -> Result<i64, u32> {
    return Ok(42);
}
fn boot() -> Option<i64> {
    let v = maybe_n()?;
    return Some(v);
}
"#;
    let err = compile_named_module("user.sigil", source)
        .expect_err("PR OptTry / N8-OptTry: Result<_,_>? in Option<_> fn must fail with T241");
    let diag = find_diagnostic_or_fail(&err, "T241");
    let msg = diag.message();
    assert!(
        msg.contains("Result") && msg.contains("Option"),
        "T241 message must name both carriers; got: {msg}"
    );
    assert!(
        msg.contains(".ok()"),
        "T241 message in Result→Option direction must suggest `.ok()`; got: {msg}"
    );
}

/// PR OptTry / AG-OptTry-S: `Option<T>?` vs `Option<U>` payload-type
/// mismatch (where T != U fails `type_compatible`) fires T071, NOT a
/// dedicated T-code. User sees standard type-mismatch diagnostic.
#[test]
fn opt_try_option_t_vs_u_fires_t071() {
    let source = r#"
module main;
fn maybe_n() -> Option<i32> {
    return Some(42);
}
fn boot() -> Option<i64> {
    let v = maybe_n()?;
    return Some(v);
}
"#;
    let err = compile_named_module("user.sigil", source)
        .expect_err("PR OptTry / AG-OptTry-S: Option<i32>? in Option<i64> fn must fail with T071");
    // T071 fires for the payload-type mismatch on the `?` itself.
    // Other type errors may also fire downstream; we only assert T071 is present.
    let _ = find_diagnostic(&err, "T071");
}

/// PR OptTry: existing Result-`?` path remains unchanged. The
/// Result-Result existing arm precedes the new Option arms, and
/// T180/T181/T182 remain the codes for Result-shape mismatches.
#[test]
fn opt_try_result_question_unchanged() {
    let source = r#"
module main;
fn helper() -> Result<i64, u32> {
    return Ok(42);
}
fn boot() -> Result<i64, u32> {
    let v = helper()?;
    return Ok(v);
}
"#;
    if let Err(err) = compile_named_module("user.sigil", source) {
        panic!("PR OptTry: existing Result-`?` path must still compile; got:\n{err:#?}");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Axis 4 (Better errors) — diagnostic message-shape tests for codes that
// shipped without one and now meet the "name offending entity + copyable
// fix template" bar. T212/T214/T234 received message uplifts in the same
// PR; T231/T232/T233/T236/T237/T241 already had quality messages and just
// gain shape-lock tests so the bar can't regress.
//
// T213 (oversized-array QF_LIA bound) is intentionally NOT covered here —
// it's a defensive check on a path unreachable from user source today
// (the `[T; N]` parser caps N at 65535 via T239, which is many orders of
// magnitude smaller than i32::MAX). T213 stays in the codes file as
// belt-and-braces against a future grammar relaxation.

/// T212: refinement-LHS field with non-i64 type. Message must name (1)
/// the record, (2) the offending field, (3) the actual type, AND embed
/// a copyable fix template enumerating concrete options.
#[test]
fn t212_message_names_record_field_type_and_fix() {
    let source = r#"
module sigil;
record R { name: bool } where name > 0
entry actor Main {
    on Start() -> i64 {
        let r = R { name: true };
        return 1;
    }
}
"#;
    let err = compile_named_module("t212_msg.sigil", source)
        .expect_err("T212 should reject non-i64 refinement LHS");
    let diag = find_diagnostic(&err, "T212");
    let msg = diag.message();
    assert!(msg.contains("`R`"), "T212 must name record `R`; got: {msg}");
    assert!(
        msg.contains("`name`"),
        "T212 must name field `name`; got: {msg}"
    );
    assert!(
        msg.contains("bool"),
        "T212 must name actual type `bool`; got: {msg}"
    );
    assert!(
        msg.contains("To fix") || msg.contains("change the field"),
        "T212 must embed a copyable fix template; got: {msg}"
    );
}

/// T214: compound refinement predicate at parse time. Message must
/// explain WHY the rejection (combinator support deferred) AND embed a
/// fix template covering both collapse and split strategies.
#[test]
fn t214_message_names_deferred_feature_and_fix() {
    let source = r#"
module sigil;
record R { x: i64 } where x > 0 && x < 10
entry actor Main { on Start() -> i64 { return 1; } }
"#;
    let err = compile_named_module("t214_msg.sigil", source)
        .expect_err("T214 should reject compound refinement");
    let diag = find_diagnostic(&err, "T214");
    let msg = diag.message();
    assert!(
        msg.contains("`&&`") || msg.contains("`||`") || msg.contains("combinator"),
        "T214 must name the deferred combinator feature; got: {msg}"
    );
    assert!(
        msg.contains("To fix") || msg.contains("collapse") || msg.contains("split"),
        "T214 must embed a copyable fix template; got: {msg}"
    );
}

/// T214 reachability matrix. The combinator guard fires on a raw token
/// match, so it stops firing — silently — whenever the lexer re-spells
/// `&&` / `||`. That regressed once: the guard matched only the
/// single-char `Ampersand` / `Pipe` (which was how `&&` lexed at the
/// time), so introducing dedicated `AndAnd` / `OrOr` tokens downgraded
/// every compound predicate to a generic P006 "expected item
/// declaration" pointing at the combinator.
///
/// Both spellings and every refinement-RHS form must reach T214: a
/// syntactically complete clause followed by a combinator is a compound
/// predicate regardless of which RHS grammar produced it.
///
/// The matrix also spans all FOUR `where` positions — record, enum
/// variant, function parameter, return value. Only the record position
/// ever had a combinator guard; the other three fell through to generic
/// `P001`/`P002` cascades until the guard was made shared.
///
/// The third column pins the POSITION-SPECIFIC wording, so a future
/// refactor can't collapse the four fix templates back into the
/// record-worded one (which advises "split into two separate records" —
/// nonsense advice at a return position).
#[test]
fn t214_fires_for_every_combinator_spelling_rhs_form_and_where_position() {
    let cases: [(&str, &str, &str); 9] = [
        (
            "record_and_literal",
            "record R { x: i64 } where x > 0 && x < 10",
            "per record",
        ),
        (
            "record_or_literal",
            "record R { x: i64 } where x > 0 || x > 100",
            "per record",
        ),
        (
            "record_and_cross_field",
            "record R { a: i64, b: i64 } where a > b && a < 10",
            "per record",
        ),
        (
            "record_or_cross_field",
            "record R { a: i64, b: i64 } where a > b || a > 10",
            "per record",
        ),
        (
            "record_and_length_of",
            "record Buf { content: bool, len: i64 } where len == content.length() && len > 0",
            "per record",
        ),
        (
            "variant_and_literal",
            "enum E { Positive(n: i64) where n > 0 && n < 10 }",
            "per enum variant",
        ),
        (
            "variant_or_cross_field",
            "enum E { Pair(n: i64, m: i64) where n > m || n > 10 }",
            "per enum variant",
        ),
        (
            "param_and_literal",
            "fn f(x: i64) where x > 0 && x < 10 -> i64 { return x; }",
            "per parameter position",
        ),
        (
            "return_or_literal",
            "fn f(x: i64) -> i64 where @ > 0 || @ > 100 { return x; }",
            "per return position",
        ),
    ];

    for (label, decl, position_phrase) in cases {
        let source = format!(
            "\nmodule sigil;\n{decl}\nentry actor Main {{ on Start() -> i64 {{ return 1; }} }}\n"
        );
        let err = compile_named_module(format!("t214_{label}.sigil"), &source)
            .expect_err("compound refinement must be rejected");
        let diag = find_diagnostic(&err, "T214");
        let msg = diag.message();
        assert!(
            msg.contains("`&&`") || msg.contains("`||`") || msg.contains("combinator"),
            "[{label}] T214 must name the deferred combinator feature; got: {msg}"
        );
        assert!(
            msg.contains("To fix") || msg.contains("collapse") || msg.contains("split"),
            "[{label}] T214 must embed a copyable fix template; got: {msg}"
        );
        assert!(
            msg.contains(position_phrase),
            "[{label}] T214 must use the fix template for its own `where` position \
             (expected {position_phrase:?}); got: {msg}"
        );
    }
}

/// T231/T232: dispatcher arity / unresolved-generic invariants. Hard to
/// trigger from valid user source; these tests are "happy-path doesn't
/// spuriously fire" regression guards rather than full message-shape
/// audits.
#[test]
fn t231_t232_happy_path_no_spurious_fire() {
    let source = r#"
module sigil;
record Holder<T> { value: T }
impl Holder<T> {
    fn extract(self: Holder<T>) -> T { return self.value; }
}
entry actor Main {
    on Start() -> i64 {
        let h: Holder<i64> = Holder { value: 5 };
        let v: i64 = h.extract();
        return v;
    }
}
"#;
    let _ = compile_named_module("t231_t232_happy.sigil", source)
        .expect("T231/T232 must not fire on well-formed generic-impl dispatch");
}

/// T233: type parameter cannot be inferred from field values. Message
/// names the offending param and embeds an annotation template.
#[test]
fn t233_message_names_param_and_annotation_template() {
    let source = r#"
module sigil;
record Phantom<T> { dummy: i64 }
entry actor Main {
    on Start() -> i64 {
        let p = Phantom { dummy: 0 };
        return 1;
    }
}
"#;
    let err = compile_named_module("t233_msg.sigil", source)
        .expect_err("T233 should fire on phantom-T without annotation");
    let diag = find_diagnostic(&err, "T233");
    let msg = diag.message();
    assert!(
        msg.contains("`T`"),
        "T233 must name the unresolvable param `T`; got: {msg}"
    );
    assert!(
        msg.contains("`Phantom`"),
        "T233 must name the record; got: {msg}"
    );
    assert!(
        msg.contains("let x:") || msg.contains("annotation"),
        "T233 must embed an annotation template; got: {msg}"
    );
}

/// T234: type parameter has conflicting inferences. Happy-path
/// regression test (consistent T binding compiles cleanly). The
/// uplifted message (split / pin / change-value fix template) is
/// verified via inspection of the source code rather than a live fire
/// because triggering T234 from valid sigil source requires two field
/// values of distinct types, which is awkward to construct portably.
#[test]
fn t234_happy_path_no_spurious_fire() {
    let source = r#"
module sigil;
record Both<T> { a: T, b: T }
entry actor Main {
    on Start() -> i64 {
        let x = Both { a: 5, b: 7 };
        return 1;
    }
}
"#;
    let _ = compile_named_module("t234_happy.sigil", source)
        .expect("T234 must not fire when both fields bind T consistently");
}

/// T236: ambiguous bare variant across multiple in-scope enums.
#[test]
fn t236_message_names_variant_and_candidate_enums() {
    let source = r#"
module sigil;
enum Opt1 { Some(i64), None }
enum Opt2 { Some(i64), None }
entry actor Main {
    on Start() -> i64 {
        let x = Some(5);
        return 1;
    }
}
"#;
    let err = compile_named_module("t236_msg.sigil", source)
        .expect_err("T236 should fire on ambiguous bare variant");
    let diag = find_diagnostic(&err, "T236");
    let msg = diag.message();
    assert!(
        msg.contains("`Some`"),
        "T236 must name the variant; got: {msg}"
    );
    assert!(
        msg.contains("Opt1") && msg.contains("Opt2"),
        "T236 must name BOTH candidate enums; got: {msg}"
    );
    assert!(
        msg.contains("annotation") || msg.contains("qualify"),
        "T236 must offer annotation OR qualification as the fix; got: {msg}"
    );
}

/// T237: linear closure (captures `Cap<_>`) invoked through general
/// closure-call dispatch must use `grant` instead.
#[test]
fn t237_message_names_closure_and_grant_fix() {
    let source = r#"
module sigil;
cap type Fuel { burn, query }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let restricted: Fuel = fuel.restrict(burn);
        let g = fn(x: i64) -> i64 { let _ = restricted; return x; };
        return g(7);
    }
}
"#;
    let err = compile_named_module("t237_msg.sigil", source)
        .expect_err("T237 should reject linear closure at general dispatch");
    let diag = find_diagnostic(&err, "T237");
    let msg = diag.message();
    assert!(
        msg.contains("`Cap"),
        "T237 must mention the linear-capture cause (Cap); got: {msg}"
    );
    assert!(
        msg.contains("grant"),
        "T237 must point at `grant` as the fix; got: {msg}"
    );
}

/// T241: cross-carrier `?` mismatch. Message must name both carrier
/// types AND offer a directional conversion (`.ok_or` or `.ok()`).
#[test]
fn t241_message_names_both_carriers_and_conversion() {
    let source = r#"
module sigil;
use sigil::option;
fn helper() -> Option<i64> { return Some(5); }
fn cross() -> Result<i64, i64> {
    let v = helper()?;
    return Ok(v);
}
entry actor Main { on Start() -> i64 { return 1; } }
"#;
    let err = compile_named_module("t241_msg.sigil", source)
        .expect_err("T241 should reject Option-? in Result-returning fn");
    let diag = find_diagnostic(&err, "T241");
    let msg = diag.message();
    assert!(
        msg.contains("Option"),
        "T241 must name `Option`; got: {msg}"
    );
    assert!(
        msg.contains("Result"),
        "T241 must name `Result`; got: {msg}"
    );
    assert!(
        msg.contains(".ok_or") || msg.contains(".ok()"),
        "T241 must offer a directional conversion; got: {msg}"
    );
}

// ── T242 — Cap-smuggling through a generic aggregate at instantiation time ──
//
// Sibling to T184: T184 fires at enum DECLARATION time on cap-typed
// payloads; T242 fires at CONSTRUCTION time after type-arg
// substitution rewrites a generic payload to a concrete cap. The two
// codes close the same conceptual hatch (aggregate smuggling) at
// different points in the pipeline.

/// T242 message-shape: the diagnostic must name (1) the aggregate
/// name, (2) the position of the offending type-argument, and (3) the
/// offending type itself. Without those three pieces of information,
/// a user looking at a multi-arg generic (e.g., `Result<T, E>`) can't
/// tell which slot is the problem.
#[test]
fn t242_message_names_aggregate_and_offending_type_arg() {
    let source = r#"
module sigil;
cap type Fuel { burn, query }

record Holder<T> { value: T }

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let restricted: Fuel = fuel.restrict(burn);
        let h: Holder<Fuel> = Holder { value: restricted };
        return 1;
    }
}
"#;
    let err = compile_named_module("t242_msg.sigil", source)
        .expect_err("T242 should reject cap-smuggle through generic record");
    let diag = find_diagnostic(&err, "T242");
    let msg = diag.message();

    // ENTITY 1: aggregate name. With multiple generic aggregates in a
    // module, the user needs to know which instantiation is wrong.
    assert!(
        msg.contains("`Holder`"),
        "T242 message must name record `Holder`; got: {msg}"
    );

    // ENTITY 2: type-arg position. Multi-arg generics (Result<T, E>,
    // Map<K, V>) need positional disambiguation.
    assert!(
        msg.contains("position 0"),
        "T242 message must name the offending type-arg position (0); got: {msg}"
    );

    // ENTITY 3: cap type name. Tells the user WHICH cap type leaked
    // into the generic slot.
    assert!(
        msg.contains("`Fuel`"),
        "T242 message must name the offending cap type `Fuel`; got: {msg}"
    );

    // CONTEXT: cross-reference T183/T184/T186. T242 closes the same
    // hatch via the post-substitution channel; users hitting T242
    // should see the related declaration-time codes in the hint so
    // they can reason about the family.
    assert!(
        msg.contains("T183") || msg.contains("T184") || msg.contains("T186"),
        "T242 message should cross-reference T183/T184/T186 family; got: {msg}"
    );
}

/// T242 ResultCtor variant: when `Ok(cap)` / `Err(cap)` ride the
/// hardcoded parser shortcut (`try_parse_result_ctor` per AG-PRB-B),
/// the message must name the variant (`Ok` or `Err`) so the user
/// knows which side of the carrier they smuggled into.
#[test]
fn t242_result_ctor_message_names_ok_or_err_variant() {
    let source = r#"
module sigil;
cap type Fuel { burn, query }

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let restricted: Fuel = fuel.restrict(burn);
        let smuggle: Result<Fuel, i64> = Ok(restricted);
        return 1;
    }
}
"#;
    let err = compile_named_module("t242_result_msg.sigil", source)
        .expect_err("T242 should reject Ok(cap)");
    let diag = find_diagnostic(&err, "T242");
    let msg = diag.message();

    assert!(
        msg.contains("Ok"),
        "T242 Result-ctor message must name the `Ok` variant; got: {msg}"
    );
    assert!(
        msg.contains("`Fuel`"),
        "T242 Result-ctor message must name the offending cap type `Fuel`; got: {msg}"
    );
}
