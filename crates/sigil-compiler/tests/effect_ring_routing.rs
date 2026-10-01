//! BUG-5b: monomorphized generic instances must be effect- and ring-checked under
//! the MEET of the ring and trust of the module that DEFINED the generic and of
//! every module whose scope resolved names in the re-checked body — never under
//! whatever module happens to be `modules[0]`, and never under the definer alone.
//!
//! `type_check::mod`'s drain files every monomorphized instance under the first
//! module. `check_effects` skips `Ring::Inner` modules and `check_rings` keys R003
//! on the filing module's ring, so before this fix:
//!
//! * inner module first + an OUTER-ring generic `fn ident<T>(x: T) -> i64 ! {}`
//!   calling a `! { NetIO }` callee compiled clean (no E001) — the non-generic
//!   twin was rejected;
//! * the same shape through an FFI chain (`tool_main ! {}` -> generic `! {}` ->
//!   `! { FsIO, FFI, Unsafe }` -> extern) compiled clean AND issued a certificate;
//! * outer module first + an INNER-ring generic calling an extern compiled clean
//!   (no R003) — the non-generic twin was rejected.
//!
//! PR #654 fixed the identical misfiling for lambda-lifted closures only, on the
//! stated grounds that re-homing instances had "no security benefit". These tests
//! pin the instance half. The fix keeps instances FILED under `modules[0]` (the
//! SH-MONO emission-order pin; moving them moves the certified selfhost bytes)
//! but CHECKS each one under a recorded home (`TypedProgram::instance_homes`,
//! resolved by `governing_context` in both walks) that includes its generic's
//! DEFINER, not under its name prefix: a free-fn instance is named after the
//! CALLING module, so a `use`-imported generic would otherwise be checked under
//! the caller's trust alone (the E002 launder pinned below). Every expectation is an
//! EXACT code set; the non-generic twins are the SC-P4 controls proving each
//! detector fires on the same layout. Wasm ring PLACEMENT of an instance is
//! not claimed here — it still follows the filing module.
//!
//! Integrated with the two-ring index fix (p2b/tworing): `ring_check::check_air_ring_placement`,
//! the last gate before `wasm::emit`, refuses with R007 every lowered call whose callee is
//! emitted in the other ring. An instance is still FILED (so emitted) under `modules[0]`, so
//! on every layout below where the filing module's ring differs from the calling module's,
//! the full pipeline refuses the program with exactly {R007} whatever the meet decides — and
//! where the meet ACCEPTS, that refusal would hide its verdict. Those cases are pinned at two
//! layers: `checker_codes` (parse → resolve → type-check → the typed ring/effect/taint passes,
//! everything before AIR) keeps the meet's own verdict under test, and `codes` (the pipeline)
//! pins the {R007} refusal. The refusal stands until instances are emitted into their
//! governing ring (issue #768); the author decided on 2026-10-01 to land the meet with these
//! cases refused rather than wait for that.
//!
//! Round 2 routed closures lambda-lifted inside an instance body the same way (they
//! carry the CALLING module's name prefix, so wrapping the `handle Unsafe` in a
//! closure put it back under the caller's trust).
//!
//! Round 3 — the DEFINER ALONE is not the governing module. A generic FREE-FN
//! instance body is re-checked in the CALLING module's context
//! (`type_check/expressions/calls.rs`), so its callee names resolve in the
//! caller's scope; a generic IMPL-METHOD body takes its function sigs from its
//! definer but still falls back to the checked module's `use` scope. So "a
//! generic's body is its definer's code" is false, and granting it the definer's
//! privileges was fail-open: an inner-ring generic hid an outer caller's FFI chain
//! (certified), an untrusted outer caller discharged FFI through an inner generic's
//! `handle Unsafe`, a trusted generic's `handle Unsafe` ran an untrusted caller's
//! same-named helper, and an inner module reached an extern through an outer
//! generic. Each instance (and each closure lifted inside one) is now governed by
//! the MEET of its definer and every module whose scope resolved its names
//! (`TypedProgram::governing_context`): exempt from the effect walk only if ALL
//! are inner-ring, holding `handle Unsafe` authority only if ALL are trusted,
//! under each ring's restrictions if ANY is in that ring. The round-2 accept pins
//! for a generic instantiated from a DIFFERENT module are replaced by the meet's
//! verdicts below; a same-module instantiation keeps its non-generic twin's verdict.

use std::collections::BTreeSet;

use sigil_compiler::diagnostics::Severity;
use sigil_compiler::{
    CompileOptions, Diagnostic, compile_project, effect_check, name_resolution, parser, ring_check,
    source::SourceFile, taint_check, type_check,
};

/// Compile one source file (named after its first module, per M001) and return
/// the exact set of diagnostic codes; empty on acceptance.
fn codes(file: &str, src: &str) -> BTreeSet<String> {
    match compile_project(
        vec![SourceFile::new(file, src)],
        None,
        CompileOptions::default(),
    ) {
        Ok(_) => BTreeSet::new(),
        Err(e) => code_set(e.diagnostics()),
    }
}

fn code_set(diags: &[Diagnostic]) -> BTreeSet<String> {
    diags
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

/// The CHECKER layer alone, for the same single source file: parse → resolve →
/// type-check → the typed security passes in pipeline order (ring, effect, taint;
/// the first failing pass stops, as in `compile_project`). It stops before AIR
/// lowering, so it never reaches `ring_check::check_air_ring_placement` — the
/// emission gate whose R007 would otherwise hide the governing meet's verdict on a
/// layout whose instance is filed in another ring than its caller (#768). Its
/// reject verdicts agree with `codes` (anti-stub:
/// `checker_codes_reports_the_meets_rejections_and_stops_before_emission`).
fn checker_codes(file: &str, src: &str) -> BTreeSet<String> {
    let source = SourceFile::new(file, src);
    let (ast, parse_diags) = parser::parse(&source);
    assert!(
        !parse_diags.iter().any(|d| d.severity() == Severity::Error),
        "{file}: source must parse cleanly"
    );
    let resolved = match name_resolution::resolve(&ast) {
        Ok(resolved) => resolved,
        Err(diags) => return code_set(&diags),
    };
    let typed = match type_check::check_with_options(&resolved, &CompileOptions::default()) {
        Ok((typed, _registry)) => typed,
        Err(diags) => return code_set(&diags),
    };
    match ring_check::check_rings(&typed)
        .and_then(|()| effect_check::check_effects(&typed))
        .and_then(|()| taint_check::check_taints(&typed))
    {
        Ok(()) => BTreeSet::new(),
        Err(diags) => code_set(&diags),
    }
}

/// Pins one meet-ACCEPTED layout whose instance is filed in another ring than its
/// caller: the checker layer accepts it, and the pipeline refuses it at emission
/// with exactly {R007} (until #768 emits instances into their governing ring).
fn assert_meet_accepts_but_emission_refuses(file: &str, src: &str, label: &str) {
    assert_eq!(
        checker_codes(file, src),
        BTreeSet::new(),
        "{label}: the governing meet accepts"
    );
    assert_eq!(
        codes(file, src),
        set(&["R007"]),
        "{label}: the pipeline refuses the cross-ring instance call at emission (#768)"
    );
}

fn set(codes: &[&str]) -> BTreeSet<String> {
    codes.iter().map(|c| c.to_string()).collect()
}

/// An outer-ring module whose generic `ident<T>` declares an EMPTY row but calls a
/// `! { NetIO }` callee — an E001 leak inside a monomorphized instance.
const OUTER_GENERIC_FN_LEAK: &str = "#[ring(outer)]\nmodule m;\n\
     effect NetIO;\n\
     fn expensive() -> i64 ! { NetIO } { return 0; }\n\
     fn ident<T>(x: T) -> i64 ! {} { return expensive(); }\n\
     fn boot() -> i64 ! {} { return ident(1); }\n";

/// The same leak inside a generic impl method.
const OUTER_GENERIC_METHOD_LEAK: &str = "#[ring(outer)]\nmodule m;\n\
     effect NetIO;\n\
     fn expensive() -> i64 ! { NetIO } { return 0; }\n\
     record Box<T> { v: T }\n\
     impl Box<T> {\n\
         pub fn go(self: Box<T>) -> i64 ! {} { return expensive(); }\n\
     }\n\
     fn boot() -> i64 ! {} { let b: Box<i64> = Box { v: 1 }; return b.go(); }\n";

/// The non-generic twin of `OUTER_GENERIC_FN_LEAK` (the SC-P4 control).
const OUTER_NONGENERIC_LEAK: &str = "#[ring(outer)]\nmodule m;\n\
     effect NetIO;\n\
     fn expensive() -> i64 ! { NetIO } { return 0; }\n\
     fn boot() -> i64 ! {} { return expensive(); }\n";

/// An unrelated inner-ring module that sorts FIRST (the default ring: no attribute).
const INNER_FIRST: &str = "module first;\nfn dummy() -> i64 { return 0; }\n";

/// An unrelated outer-ring module that sorts FIRST.
const OUTER_FIRST: &str = "#[ring(outer)]\nmodule first;\nfn dummy() -> i64 { return 0; }\n";

/// An inner-ring module whose generic `g<T>` calls an extern directly (R003 in
/// the non-generic form).
const INNER_GENERIC_EXTERN: &str = "module app;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn g<T>(x: T, p: i32, n: i32) -> i64 { let r: i64 @Internal = fs_read(p, n); return 0; }\n\
     fn boot() -> i64 { return g(1, 0, 0); }\n";

/// The non-generic twin of `INNER_GENERIC_EXTERN` (the SC-P4 control).
const INNER_NONGENERIC_EXTERN: &str = "module app;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn g(p: i32, n: i32) -> i64 { let r: i64 @Internal = fs_read(p, n); return 0; }\n\
     fn boot() -> i64 { return g(0, 0); }\n";

/// An outer-ring trusted tool whose `tool_main ! {}` reaches a host `fs_read`
/// through a generic helper with an empty row.
const OUTER_FFI_CHAIN: &str = "#[ring(outer)] #[trusted]\nmodule tool;\n\
     effect FsIO;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn read(path: i32, path_len: i32) -> i64 ! { FsIO, FFI, Unsafe } { let r: i64 @Internal = fs_read(path, path_len); if r < 0 { trap(); } return 0; }\n\
     fn ident<T>(x: T, path: i32, path_len: i32) -> i64 ! {} { return read(path, path_len); }\n\
     pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! {} { return ident(1, input_ptr, input_len); }\n";

// ── Baselines: with the generic's own module first, the leak was always caught ──

#[test]
fn outer_generic_leak_is_flagged_when_definer_sorts_first() {
    assert_eq!(codes("m.sigil", OUTER_GENERIC_FN_LEAK), set(&["E001"]));
    assert_eq!(codes("m.sigil", OUTER_GENERIC_METHOD_LEAK), set(&["E001"]));
    assert_eq!(
        codes(
            "m.sigil",
            &format!("{OUTER_GENERIC_FN_LEAK}module second;\nfn dummy() -> i64 {{ return 0; }}\n")
        ),
        set(&["E001"]),
        "an inner module sorting SECOND never masked the leak"
    );
}

// ── BUG-5b, effect direction: an inner-ring module sorting FIRST ──────────────

/// REGRESSION: an inner-ring module sorting first must not exempt an outer-ring
/// generic FUNCTION's instance from effect checking. Before the fix: no
/// diagnostics at all.
#[test]
fn inner_first_outer_generic_fn_is_effect_checked() {
    let src = format!("{INNER_FIRST}{OUTER_GENERIC_FN_LEAK}");
    assert_eq!(codes("first.sigil", &src), set(&["E001"]));
}

/// REGRESSION: the same for an outer-ring generic IMPL METHOD's instance. Before
/// the fix: no diagnostics at all.
#[test]
fn inner_first_outer_generic_impl_method_is_effect_checked() {
    let src = format!("{INNER_FIRST}{OUTER_GENERIC_METHOD_LEAK}");
    assert_eq!(codes("first.sigil", &src), set(&["E001"]));
}

/// REGRESSION: the FFI chain (`tool_main ! {}` -> generic `! {}` -> `read ! { FsIO,
/// FFI, Unsafe }` -> extern) is rejected with exactly E001, so NO certificate can
/// be issued for it (a certificate exists only on the `Ok` arm of the compile).
/// Before the fix: accepted, certificate issued with `effects_required`
/// `[FFI, FsIO, Unsafe]` behind an empty `tool_main` row.
#[test]
fn inner_first_outer_ffi_chain_rejects_without_certificate() {
    let src = format!("{INNER_FIRST}{OUTER_FFI_CHAIN}");
    let result = compile_project(
        vec![SourceFile::new("first.sigil", &src)],
        None,
        CompileOptions::default(),
    );
    let err =
        result.expect_err("the FFI chain must be rejected — an Ok here would carry a certificate");
    let got: BTreeSet<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    assert_eq!(got, set(&["E001"]));
    // The control: the identical tool WITHOUT the inner module in front was always
    // rejected the same way.
    assert_eq!(codes("tool.sigil", OUTER_FFI_CHAIN), set(&["E001"]));
}

// ── BUG-5b, ring direction: an outer-ring module sorting FIRST ────────────────

/// REGRESSION: an outer-ring module sorting first must not let an inner-ring
/// generic's instance call an extern past R003. Before the fix: no diagnostics.
/// The expected set is exactly what the non-generic twin emits (measured, not
/// assumed — see `nongeneric_twins_prove_the_detectors_fire`).
#[test]
fn outer_first_inner_generic_extern_call_is_r003() {
    let src = format!("{OUTER_FIRST}{INNER_GENERIC_EXTERN}");
    assert_eq!(codes("first.sigil", &src), set(&["R003"]));
}

// ── SC-P4: the detectors fire on the same layouts for NON-generic code ────────

/// The non-generic twins compile under the SAME module layouts and are rejected
/// with the SAME exact sets — proving E001/R003 are live detectors on these
/// layouts and the generic escapes above were routing, not scope.
#[test]
fn nongeneric_twins_prove_the_detectors_fire() {
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{INNER_FIRST}{OUTER_NONGENERIC_LEAK}")
        ),
        set(&["E001"]),
        "inner-first + outer NON-generic leak"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{OUTER_FIRST}{INNER_NONGENERIC_EXTERN}")
        ),
        set(&["R003"]),
        "outer-first + inner NON-generic extern call"
    );
    assert_eq!(
        codes("app.sigil", INNER_NONGENERIC_EXTERN),
        set(&["R003"]),
        "inner NON-generic extern call, single module"
    );
}

// ── BUG-5b, trust direction: a `use`-imported generic instantiates under the CALLER's name ──

/// An UNTRUSTED outer module whose generic `danger<T>` uses `handle Unsafe`, instantiated
/// from a TRUSTED outer module via `use`. The instance is named `user::danger__i64` (the
/// calling module's prefix), so a drain that filed by name prefix alone would check the
/// untrusted body under the trusted caller and E002 would not fire.
const UNTRUSTED_GENERIC_HANDLE_UNSAFE: &str = "#[ring(outer)]\nmodule defs;\n\
     pub fn danger<T>(x: T) -> i64 ! {} { handle Unsafe { let _x: i64 = 1; }; return 0; }\n";

const TRUSTED_USER_OF_DEFS: &str = "#[ring(outer)] #[trusted]\nmodule user;\n\
     use sigil::defs;\n\
     fn boot() -> i64 ! {} { return danger(1); }\n";

/// REGRESSION (found while fixing the routing): the instance of an untrusted module's generic
/// is E002-checked under a meet that includes the DEFINER's trust, not under the trusted
/// caller's alone — exactly E002.
#[test]
fn use_imported_generic_is_checked_under_definer_trust() {
    let src = format!("{UNTRUSTED_GENERIC_HANDLE_UNSAFE}{TRUSTED_USER_OF_DEFS}");
    assert_eq!(codes("defs.sigil", &src), set(&["E002"]));
}

/// SC-P4 controls for the trust direction: the non-generic twin through the same `use`, and
/// the generic instantiated from its OWN untrusted module, are both exactly E002.
#[test]
fn nongeneric_and_same_module_twins_prove_e002_fires() {
    let nongeneric = "#[ring(outer)]\nmodule defs;\n\
         pub fn danger(x: i64) -> i64 ! {} { handle Unsafe { let _x: i64 = 1; }; return 0; }\n";
    assert_eq!(
        codes("defs.sigil", &format!("{nongeneric}{TRUSTED_USER_OF_DEFS}")),
        set(&["E002"]),
        "NON-generic untrusted `handle Unsafe` called from a trusted module via `use`"
    );
    let same_module = format!(
        "{UNTRUSTED_GENERIC_HANDLE_UNSAFE}fn boot() -> i64 ! {{}} {{ return danger(1); }}\n"
    );
    assert_eq!(
        codes("defs.sigil", &same_module),
        set(&["E002"]),
        "generic instantiated from its own untrusted module"
    );
}

/// A TRUSTED module's generic that uses `handle Unsafe`.
const TRUSTED_GENERIC_HANDLE_UNSAFE: &str = "#[ring(outer)] #[trusted]\nmodule defs;\n\
     pub fn danger<T>(x: T) -> i64 ! {} { handle Unsafe { let _x: i64 = 1; }; return 0; }\n";

const UNTRUSTED_USER_OF_DEFS: &str = "#[ring(outer)]\nmodule user;\n\
     use sigil::defs;\n\
     fn boot() -> i64 ! {} { return danger(1); }\n";

/// Round 3 (replaces round 1's accept pin): a TRUSTED module's generic `handle Unsafe`
/// instantiated from an UNTRUSTED module is exactly E002, in BOTH layouts — the instance's
/// callee names resolve in the untrusted caller's scope, so it holds trust only if both
/// are trusted. On main `ae026aec` the trusted-module-first layout was ACCEPTED (the
/// instance was filed under, and checked as, the trusted first module) — a behavior
/// change, deliberate: `caller_scope_helper_under_trusted_generic_handle_is_e002` shows
/// what that acceptance let run. Controls: the same generic from a TRUSTED caller is
/// accepted, so the rejection is the meet and not the body.
#[test]
fn trusted_generic_instantiated_from_untrusted_caller_is_e002() {
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{TRUSTED_GENERIC_HANDLE_UNSAFE}{UNTRUSTED_USER_OF_DEFS}")
        ),
        set(&["E002"]),
        "trusted definer first, untrusted caller"
    );
    assert_eq!(
        codes(
            "user.sigil",
            &format!("{UNTRUSTED_USER_OF_DEFS}{TRUSTED_GENERIC_HANDLE_UNSAFE}")
        ),
        set(&["E002"]),
        "untrusted caller first"
    );
    let trusted_user = UNTRUSTED_USER_OF_DEFS.replace(
        "#[ring(outer)]\nmodule user;",
        "#[ring(outer)] #[trusted]\nmodule user;",
    );
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{TRUSTED_GENERIC_HANDLE_UNSAFE}{trusted_user}")
        ),
        BTreeSet::new(),
        "control: both governing modules trusted -> accepted"
    );
}

/// The caller's own `helper` (which calls an extern) SHADOWS the trusted definer's
/// `helper` inside the generic's `handle Unsafe { handle FFI { .. } }`, because the free-fn
/// instance body resolves callee names in the CALLER's scope. With the definer's trust
/// alone (round 2) this was accepted in both layouts and the emitted instance called the
/// untrusted helper; on main the trusted-module-first layout was accepted too. Exactly
/// E002 in both layouts under the meet. Control: the same program with the caller
/// trusted is accepted, so E002 here is the trust meet.
const SHADOWING_USER: &str = "#[ring(outer)]\nmodule user;\n\
     use sigil::defs;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn helper() -> i64 ! { FFI, Unsafe } { let r: i64 @Internal = fs_read(0, 0); return 777; }\n\
     pub fn boot() -> i64 ! {} { return danger(1); }\n";

const SHADOWED_TRUSTED_DEFS: &str = "#[ring(outer)] #[trusted]\nmodule defs;\n\
     fn helper() -> i64 ! { FFI, Unsafe } { return 111; }\n\
     pub fn danger<T>(x: T) -> i64 ! {} { handle Unsafe { handle FFI { let r: i64 = helper(); }; }; return 0; }\n";

#[test]
fn caller_scope_helper_under_trusted_generic_handle_is_e002() {
    assert_eq!(
        codes(
            "user.sigil",
            &format!("{SHADOWING_USER}{SHADOWED_TRUSTED_DEFS}")
        ),
        set(&["E002"]),
        "untrusted caller first (review repro `shadow-userfirst`; main: E002)"
    );
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{SHADOWED_TRUSTED_DEFS}{SHADOWING_USER}")
        ),
        set(&["E002"]),
        "trusted definer first (main: accepted)"
    );
    let trusted_user = SHADOWING_USER.replace(
        "#[ring(outer)]\nmodule user;",
        "#[ring(outer)] #[trusted]\nmodule user;",
    );
    assert_eq!(
        codes(
            "user.sigil",
            &format!("{trusted_user}{SHADOWED_TRUSTED_DEFS}")
        ),
        BTreeSet::new(),
        "control: caller trusted too -> accepted"
    );
}

/// A generic IMPL METHOD takes its function sigs from its definer (CF-D9), but a name the
/// definer lacks still resolves through the CHECKED module's `use` scope: here the trusted
/// definer's `helper()` reaches the untrusted `evil::helper` (an FFI call) because the
/// untrusted caller imports `evil`. Accepted on main (definer first) and by round 2 (both
/// layouts); exactly E002 in both layouts under the meet. The NON-generic twin does not
/// even resolve (exactly T062) — the caller's scope is reachable only through the
/// monomorphized re-check.
const EVIL_HELPER: &str = "#[ring(outer)]\nmodule evil;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     pub fn helper() -> i64 ! { FFI, Unsafe } { let r: i64 @Internal = fs_read(0, 0); return 777; }\n";

const TRUSTED_GENERIC_METHOD_CALLS_HELPER: &str = "#[ring(outer)] #[trusted]\nmodule defs;\n\
     record Box<T> { v: T }\n\
     impl Box<T> {\n\
         pub fn go(self: Box<T>) -> i64 ! {} { handle Unsafe { handle FFI { let r: i64 = helper(); }; }; return 0; }\n\
     }\n";

const UNTRUSTED_USER_OF_BOX: &str = "#[ring(outer)]\nmodule user;\n\
     use sigil::defs;\n\
     use sigil::evil;\n\
     pub fn boot() -> i64 ! {} { let b: Box<i64> = Box { v: 1 }; return b.go(); }\n";

#[test]
fn impl_method_use_scope_fallback_is_governed_by_the_meet() {
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{TRUSTED_GENERIC_METHOD_CALLS_HELPER}{UNTRUSTED_USER_OF_BOX}{EVIL_HELPER}")
        ),
        set(&["E002"]),
        "trusted definer first (main: accepted)"
    );
    assert_eq!(
        codes(
            "user.sigil",
            &format!("{UNTRUSTED_USER_OF_BOX}{TRUSTED_GENERIC_METHOD_CALLS_HELPER}{EVIL_HELPER}")
        ),
        set(&["E002"]),
        "untrusted caller first (main: E002)"
    );
    let nongeneric_defs = TRUSTED_GENERIC_METHOD_CALLS_HELPER
        .replace("record Box<T> { v: T }", "record Box { v: i64 }")
        .replace("impl Box<T>", "impl Box")
        .replace("self: Box<T>", "self: Box");
    let nongeneric_user = UNTRUSTED_USER_OF_BOX.replace("Box<i64>", "Box");
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{nongeneric_defs}{nongeneric_user}{EVIL_HELPER}")
        ),
        set(&["T062"]),
        "the non-generic twin resolves `helper` in its own module only"
    );
}

// ── SC-P4 for the checker layer: `checker_codes` is a detector, not a stub ────

/// The empty sets `checker_codes` reports for the meet's accepts below are
/// observations: on the reject layouts the meet decides, it reports exactly the
/// pipeline's set (E001 from the effect walk, R003 from the ring walk, T062 from
/// the type checker), and on a meet-accepted cross-ring layout it reports nothing
/// where the pipeline reports exactly {R007} — the one gate it does not run.
#[test]
fn checker_codes_reports_the_meets_rejections_and_stops_before_emission() {
    for (file, src, expected) in [
        (
            "first.sigil",
            format!("{INNER_FIRST}{OUTER_GENERIC_FN_LEAK}"),
            "E001",
        ),
        (
            "first.sigil",
            format!("{OUTER_FIRST}{INNER_GENERIC_EXTERN}"),
            "R003",
        ),
        (
            "first.sigil",
            format!(
                "{OUTER_NET_CALLER}{}",
                INNER_GENERIC_CALLS_CALLER_NET.replace("fn g<T>(x: T)", "fn g(x: i64)")
            ),
            "T062",
        ),
    ] {
        assert_eq!(checker_codes(file, &src), set(&[expected]), "checker layer");
        assert_eq!(codes(file, &src), set(&[expected]), "pipeline agrees");
    }
    let cross_ring_accept = format!("{OUTER_FIRST}{INNER_DEFINER_GENERIC_LEAK}");
    assert_eq!(
        checker_codes("first.sigil", &cross_ring_accept),
        BTreeSet::new()
    );
    assert_eq!(codes("first.sigil", &cross_ring_accept), set(&["R007"]));
}

// ── Accept: routing must not over-reject ──────────────────────────────────────

/// An outer-ring generic that DECLARES the effect it uses is accepted by the meet
/// with the inner module first — the fix rejects only the leak, not the layout. The
/// instance is filed under the inner first module while its caller `boot` is outer,
/// so the pipeline refuses the program at emission with exactly {R007} (#768).
#[test]
fn outer_generic_declaring_its_effect_is_accepted() {
    let src = format!(
        "{INNER_FIRST}#[ring(outer)]\nmodule m;\n\
         effect NetIO;\n\
         fn expensive() -> i64 ! {{ NetIO }} {{ return 0; }}\n\
         fn ident<T>(x: T) -> i64 ! {{ NetIO }} {{ return expensive(); }}\n\
         fn boot() -> i64 ! {{ NetIO }} {{ return ident(1); }}\n"
    );
    assert_meet_accepts_but_emission_refuses("first.sigil", &src, "outer generic declaring NetIO");
}

// ── The MIRROR layout: an INNER-ring definer with an outer module sorting first ──
//
// Round 2 pinned an ACCEPT here on the grounds that "a generic's body is its
// definer's code". Round 3: that holds only when the generic is instantiated from
// its OWN module — then every governing module is the inner definer, the meet
// exempts the instance exactly as it exempts the non-generic twin, and main's
// rejection was an artifact of filing the instance under an unrelated outer
// module. Instantiated from an OUTER module, the instance body resolves names in
// the outer caller's scope and is walked: the review repros below (an FFI chain,
// FFI discharged by an untrusted caller through an inner generic's `handle
// Unsafe`) were accepted by round 2 and are pinned as rejects. The outer-ring
// definer on the same layout is the SC-P4 control proving E001/E002 are live.
// The same-module exemption is the meet's verdict (pinned at the checker layer);
// the instance is filed under the outer first module, so the pipeline refuses the
// program at emission with exactly {R007} until #768.

/// An INNER-ring (default) module whose generic leaks `NetIO` past an empty row,
/// instantiated from its own module, with an unrelated outer-ring module first.
const INNER_DEFINER_GENERIC_LEAK: &str = "module app;\n\
     effect NetIO;\n\
     fn expensive() -> i64 ! { NetIO } { return 0; }\n\
     fn g<T>(x: T) -> i64 ! {} { return expensive(); }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// The non-generic twin of `INNER_DEFINER_GENERIC_LEAK`.
const INNER_DEFINER_NONGENERIC_LEAK: &str = "module app;\n\
     effect NetIO;\n\
     fn expensive() -> i64 ! { NetIO } { return 0; }\n\
     fn g(x: i64) -> i64 ! {} { return expensive(); }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// An INNER-ring module whose generic uses `handle Unsafe`, instantiated from its
/// own module, with an outer-ring module first.
const INNER_DEFINER_GENERIC_UNSAFE: &str = "module app;\n\
     fn g<T>(x: T) -> i64 ! {} { handle Unsafe { let _x: i64 = 1; }; return 0; }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// The non-generic twin of `INNER_DEFINER_GENERIC_UNSAFE`.
const INNER_DEFINER_NONGENERIC_UNSAFE: &str = "module app;\n\
     fn g(x: i64) -> i64 ! {} { handle Unsafe { let _x: i64 = 1; }; return 0; }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// An inner-ring generic `g<T>` that calls a function it does not define — the
/// name resolves only in an OUTER caller's scope.
const INNER_GENERIC_CALLS_CALLER_NET: &str = "module app;\n\
     fn g<T>(x: T) -> i64 { return net(); }\n";

/// The outer-ring caller of `INNER_GENERIC_CALLS_CALLER_NET`, sorting first.
const OUTER_NET_CALLER: &str = "#[ring(outer)]\nmodule first;\n\
     effect NetIO;\n\
     fn net() -> i64 ! { NetIO } { return 0; }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// Review repro `inner-gen-ffi-chain`: a trusted outer tool's `tool_main ! {}`
/// reaches its own `read ! { FsIO, FFI, Unsafe }` through an INNER-ring generic
/// whose body names `read` (resolved in the tool's scope).
const TOOL_THROUGH_INNER_GENERIC: &str = "#[ring(outer)] #[trusted]\nmodule tool;\n\
     effect FsIO;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn read(path: i32, path_len: i32) -> i64 ! { FsIO, FFI, Unsafe } { let r: i64 @Internal = fs_read(path, path_len); if r < 0 { trap(); } return 0; }\n\
     pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! {} { return g(1, input_ptr, input_len); }\n\
     module app;\n\
     fn g<T>(x: T, p: i32, n: i32) -> i64 { return read(p, n); }\n";

/// Round 3 (replaces round 2's unconditional accept): an inner-ring generic is exempt
/// from the effect walk only when EVERY governing module is inner. Same-module
/// instantiation: exempt under the meet, as its non-generic twin (main rejected it
/// with E001 — a filing artifact); the pipeline refuses it at emission with exactly
/// {R007} (instance filed in the outer ring, #768). Outer caller: walked, exactly E001
/// (review repro `inner-gen-calls-outer-net`; round 2 accepted, main E001). The FFI
/// chain through an inner generic: exactly E001, so no certificate (round 2 accepted
/// AND certified; main E001). SC-P4: the outer-ring definer on the same layout is E001.
#[test]
fn inner_ring_generic_leak_is_exempt_only_when_every_governing_module_is_inner() {
    assert_meet_accepts_but_emission_refuses(
        "first.sigil",
        &format!("{OUTER_FIRST}{INNER_DEFINER_GENERIC_LEAK}"),
        "inner definer instantiated from its own inner module: exempt",
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{OUTER_FIRST}{INNER_DEFINER_NONGENERIC_LEAK}")
        ),
        BTreeSet::new(),
        "the non-generic twin is exempt too"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{OUTER_NET_CALLER}{INNER_GENERIC_CALLS_CALLER_NET}")
        ),
        set(&["E001"]),
        "inner definer, OUTER caller: walked under the meet"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!(
                "{OUTER_NET_CALLER}{}",
                INNER_GENERIC_CALLS_CALLER_NET.replace("fn g<T>(x: T)", "fn g(x: i64)")
            )
        ),
        set(&["T062"]),
        "its non-generic twin does not even resolve `net` — the caller's scope is \
         reachable only through the monomorphized re-check"
    );
    let result = compile_project(
        vec![SourceFile::new("tool.sigil", TOOL_THROUGH_INNER_GENERIC)],
        None,
        CompileOptions::default(),
    );
    let err = result.expect_err(
        "the FFI chain through an inner generic must be rejected — an Ok would carry a certificate",
    );
    let got: BTreeSet<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    assert_eq!(got, set(&["E001"]), "FFI chain through an inner generic");
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{OUTER_FIRST}{OUTER_GENERIC_FN_LEAK}")
        ),
        set(&["E001"]),
        "SC-P4: move the SAME generic leak to an OUTER-ring definer and E001 fires"
    );
}

/// An inner-ring generic that discharges FFI and Unsafe around `rd`, a name only
/// its OUTER, UNTRUSTED caller defines.
const INNER_GENERIC_HANDLES_CALLER_FFI: &str = "module app;\n\
     fn g<T>(x: T, p: i32, n: i32) -> i64 { handle Unsafe { handle FFI { let r: i64 = rd(p, n); }; }; return 0; }\n";

/// The untrusted outer caller of `INNER_GENERIC_HANDLES_CALLER_FFI`.
const UNTRUSTED_FFI_CALLER: &str = "#[ring(outer)]\nmodule first;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn rd(p: i32, n: i32) -> i64 ! { FFI, Unsafe } { let r: i64 @Internal = fs_read(p, n); return 0; }\n\
     pub fn boot(p: i32, n: i32) -> i64 ! {} { return g(1, p, n); }\n";

/// Round 3 (replaces round 2's unconditional accept): an inner-ring generic's `handle
/// Unsafe` holds authority only when every governing module is inner (exempt) — never
/// for an outer caller, which is untrusted here. Same-module instantiation: exempt under
/// the meet, as its twin (main E002 — a filing artifact); the pipeline refuses it at
/// emission with exactly {R007} (instance filed in the outer ring, #768). Outer
/// untrusted caller: exactly E002. Review repro `untrusted-ffi-via-inner-gen`: an
/// untrusted module discharging FFI through the inner generic is exactly E002 in BOTH
/// layouts (round 2 accepted both; main accepted the inner-module-first layout).
/// SC-P4: the outer-ring definer on the same layout is E002.
#[test]
fn inner_ring_generic_handle_unsafe_is_exempt_only_when_every_governing_module_is_inner() {
    assert_meet_accepts_but_emission_refuses(
        "first.sigil",
        &format!("{OUTER_FIRST}{INNER_DEFINER_GENERIC_UNSAFE}"),
        "inner definer instantiated from its own inner module: exempt",
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{OUTER_FIRST}{INNER_DEFINER_NONGENERIC_UNSAFE}")
        ),
        BTreeSet::new(),
        "the non-generic twin is exempt too"
    );
    let inner_generic_unsafe = "module app;\n\
         fn g<T>(x: T) -> i64 { handle Unsafe { let _x: i64 = 1; }; return 0; }\n";
    let untrusted_outer_caller = "#[ring(outer)]\nmodule first;\n\
         fn boot() -> i64 ! {} { return g(1); }\n";
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{untrusted_outer_caller}{inner_generic_unsafe}")
        ),
        set(&["E002"]),
        "inner definer, untrusted OUTER caller"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{UNTRUSTED_FFI_CALLER}{INNER_GENERIC_HANDLES_CALLER_FFI}")
        ),
        set(&["E002"]),
        "untrusted caller first"
    );
    assert_eq!(
        codes(
            "app.sigil",
            &format!("{INNER_GENERIC_HANDLES_CALLER_FFI}{UNTRUSTED_FFI_CALLER}")
        ),
        set(&["E002"]),
        "inner definer first (main: accepted)"
    );
    let outer_definer =
        INNER_DEFINER_GENERIC_UNSAFE.replace("module app;", "#[ring(outer)]\nmodule app;");
    assert_eq!(
        codes("first.sigil", &format!("{OUTER_FIRST}{outer_definer}")),
        set(&["E002"]),
        "SC-P4: move the SAME generic `handle Unsafe` to an OUTER-ring definer and E002 fires"
    );
}

/// An outer-ring trusted generic calling `fs_read`, a name only its INNER-ring
/// caller declares (as an extern).
const OUTER_GENERIC_CALLS_CALLER_EXTERN: &str = "#[ring(outer)] #[trusted]\nmodule defs;\n\
     pub fn og<T>(x: T, p: i32, n: i32) -> i64 ! { FFI, Unsafe } { let r: i64 @Internal = fs_read(p, n); return 0; }\n";

/// The inner-ring caller of `OUTER_GENERIC_CALLS_CALLER_EXTERN`.
const INNER_EXTERN_CALLER: &str = "module app;\n\
     extern \"C\" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn boot() -> i64 { return og(1, 0, 0); }\n";

/// Round 3, ring consumer: an inner module reaches an extern by routing it through an
/// outer generic whose body resolves the extern in the inner caller's scope. With the
/// definer's ring alone (round 2) the outer rules applied and it was accepted in both
/// layouts (main accepted the outer-definer-first layout). Under the meet the instance
/// straddles both rings and gets both rule sets: exactly R003 in both layouts. SC-P4:
/// `nongeneric_twins_prove_the_detectors_fire` pins R003 live for inner extern calls.
#[test]
fn outer_generic_resolving_an_inner_callers_extern_is_r003() {
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{OUTER_GENERIC_CALLS_CALLER_EXTERN}{INNER_EXTERN_CALLER}")
        ),
        set(&["R003"]),
        "outer definer first (main: accepted)"
    );
    assert_eq!(
        codes(
            "app.sigil",
            &format!("{INNER_EXTERN_CALLER}{OUTER_GENERIC_CALLS_CALLER_EXTERN}")
        ),
        set(&["R003"]),
        "inner caller first (main: R003)"
    );
}

// ── Round 3, ring consumer: R001 and R002 ride the same governing context ─────
//
// `ring_check` keys R001 and R002 (the outer-ring cap rules) on the same
// `governing_context` as R003, so an outer-ring generic's instance filed under an
// inner-ring `modules[0]` no longer escapes them, and an inner-ring generic
// instantiated from its OWN inner module (every governing module inner) no longer
// picks up the outer rules from an unrelated outer first module. Measured against
// main `ae026aec`: the generic rows below were `{}` and `{R001}`/`{R002}` there
// respectively (a filing artifact); under the meet each now equals its non-generic
// twin. The inner-ring same-module rows are filed under the OUTER first module, so
// the pipeline refuses them at emission with exactly {R007} (#768); the meet's
// accept verdict for them is pinned at the checker layer.

/// Outer-ring module binding an OWNED cap in `g` (R001's `let` channel). `mk` is
/// generic in both twins so only `g` differs between them.
const R001_OWNED_LET: &str = "#[ring(outer)]\nmodule app;\n\
     cap type Tool { use_tool }\n\
     fn mk<U>(u: U) -> Tool ! {} { return mk(u); }\n\
     {G} ! {} { let c: Tool = mk(x); return 0; }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

/// Outer-ring module whose `g` returns a closure type carrying a cap REFERENCE (the
/// R002 channel that reaches `ring_check`).
const R002_REF_RET: &str = "#[ring(outer)]\nmodule app;\n\
     cap type Tool { use_tool }\n\
     {G} { return f; }\n\
     fn use_it(f: Fn(i64) -> &Tool) -> i64 ! {} { let r: Fn(i64) -> &Tool = g(1, f); return 0; }\n";

/// Inner-ring module owning a cap in `g`; `mk` is NON-generic so only `g` is an
/// instance.
const INNER_OWNED_LET: &str = "module app;\n\
     cap type Tool { use_tool }\n\
     fn mk(u: i64) -> Tool ! {} { return mk(u); }\n\
     {G} ! {} { let c: Tool = mk(1); return 0; }\n\
     fn boot() -> i64 ! {} { return g(1); }\n";

#[test]
fn outer_ring_cap_rules_follow_the_governing_context_for_generics() {
    let with = |template: &str, sig: &str| template.replace("{G}", sig);
    let (gen_sig, twin_sig) = ("fn g<T>(x: T) -> i64", "fn g(x: i64) -> i64");
    let (gen_ref, twin_ref) = (
        "fn g<T>(x: T, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool",
        "fn g(x: i64, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool",
    );
    // Reject direction: an inner-ring first module no longer hides the outer rules.
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{INNER_FIRST}{}", with(R001_OWNED_LET, gen_sig))
        ),
        set(&["R001"]),
        "outer generic owning a cap, inner module first (main: accepted)"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{INNER_FIRST}{}", with(R001_OWNED_LET, twin_sig))
        ),
        set(&["R001"]),
        "SC-P4: the non-generic twin on the same layout"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{INNER_FIRST}{}", with(R002_REF_RET, gen_ref))
        ),
        set(&["R002"]),
        "outer generic returning a cap-reference type, inner module first (main: accepted)"
    );
    assert_eq!(
        codes(
            "first.sigil",
            &format!("{INNER_FIRST}{}", with(R002_REF_RET, twin_ref))
        ),
        set(&["R002"]),
        "SC-P4: the non-generic twin on the same layout"
    );
    // Same-module instantiation of an inner-ring generic: every governing module is
    // inner, so the outer rules do not apply — exactly the non-generic twin's verdict
    // at the checker layer. The instance is filed under the outer first module, so
    // the pipeline refuses it at emission with exactly {R007} (#768); the non-generic
    // twin, emitted in its own inner module, is accepted end to end.
    let inner_ref = R002_REF_RET.replace("#[ring(outer)]\nmodule app;", "module app;");
    for (label, generic, twin) in [
        (
            "inner generic owning a cap, outer module first (main: R001)",
            with(INNER_OWNED_LET, gen_sig),
            with(INNER_OWNED_LET, twin_sig),
        ),
        (
            "inner generic returning a cap-reference type, outer module first (main: R002)",
            with(&inner_ref, gen_ref),
            with(&inner_ref, twin_ref),
        ),
    ] {
        assert_meet_accepts_but_emission_refuses(
            "first.sigil",
            &format!("{OUTER_FIRST}{generic}"),
            label,
        );
        assert_eq!(
            codes("first.sigil", &format!("{OUTER_FIRST}{twin}")),
            BTreeSet::new(),
            "{label}: the non-generic twin agrees"
        );
    }
    // The meet: an inner-ring generic instantiated from an OUTER module straddles
    // both rings and gets the outer rules too. `mk` is generic here so it resolves
    // program-wide from the caller's scope (a free-fn instance body resolves its
    // names in the CALLER's scope, so a non-generic `mk` is T062 there — measured,
    // below). With the inner definer sorting first, main `ae026aec` filed each
    // instance under the inner module and ACCEPTED both programs; with the outer
    // caller first, main's filing happened to agree with the meet. Controls: the
    // same generic instantiated from its OWN inner module is accepted, an outer
    // `let` of the cap-reference closure type WITHOUT the instance is accepted, and
    // the non-generic twins do not resolve at all (exactly T062) — the outer
    // caller's scope is reachable only through the monomorphized re-check.
    let inner_mk_generic = "module app;\n\
         cap type Tool { use_tool }\n\
         fn mk<U>(u: U) -> Tool ! {} { return mk(u); }\n\
         fn g<T>(x: T) -> i64 { let c: Tool = mk(x); return 0; }\n";
    let outer_caller = "#[ring(outer)]\nmodule first;\n\
         fn boot() -> i64 ! {} { return g(1); }\n";
    let own_caller = "fn boot() -> i64 { return g(1); }\n";
    assert_eq!(
        codes("app.sigil", &format!("{inner_mk_generic}{outer_caller}")),
        set(&["R001"]),
        "inner generic owning a cap, OUTER caller, inner definer first (main: accepted)"
    );
    assert_eq!(
        codes("first.sigil", &format!("{outer_caller}{inner_mk_generic}")),
        set(&["R001"]),
        "inner generic owning a cap, OUTER caller, caller first (main: R001)"
    );
    assert_eq!(
        codes("app.sigil", &format!("{inner_mk_generic}{own_caller}")),
        BTreeSet::new(),
        "control: the same generic instantiated from its own inner module is accepted"
    );
    assert_eq!(
        codes(
            "app.sigil",
            &format!(
                "{}{outer_caller}",
                inner_mk_generic.replace("fn g<T>(x: T)", "fn g(x: i64)")
            )
        ),
        set(&["T062"]),
        "the non-generic twin does not resolve from the outer caller"
    );
    let inner_ref_generic = "module app;\n\
         cap type Tool { use_tool }\n\
         fn g<T>(x: T, f: Fn(i64) -> &Tool) -> Fn(i64) -> &Tool { return f; }\n";
    let outer_use_it = "#[ring(outer)]\nmodule first;\n\
         fn use_it(f: Fn(i64) -> &Tool) -> i64 ! {} { let r: Fn(i64) -> &Tool = g(1, f); return 0; }\n";
    assert_eq!(
        codes("app.sigil", &format!("{inner_ref_generic}{outer_use_it}")),
        set(&["R002"]),
        "inner generic returning a cap-reference type, OUTER caller, inner definer first \
         (main: accepted)"
    );
    assert_eq!(
        codes(
            "app.sigil",
            &format!(
                "{inner_ref_generic}{}",
                outer_use_it.replace("g(1, f)", "f")
            )
        ),
        BTreeSet::new(),
        "control: the outer `let` of the cap-reference closure type without the instance"
    );
    assert_eq!(
        codes(
            "app.sigil",
            &format!(
                "{}{outer_use_it}",
                inner_ref_generic.replace("fn g<T>(x: T, f", "fn g(x: i64, f")
            )
        ),
        set(&["T062"]),
        "the non-generic twin does not resolve from the outer caller"
    );
}

// ── Round 2: a closure lifted inside an instance follows the INSTANCE's home ──
//
// A lambda-lifted closure is named `{module being checked}::__closure_N` and
// re-homed by that prefix at the drain (PR #654). A free-fn instance body is
// re-checked in the CALLING module's context, so a closure lifted inside one
// carries the CALLER's prefix — and before round 2 it was checked under the
// caller's ring and trust alone: wrapping the `handle Unsafe` in a closure
// laundered an untrusted definer's code through a trusted caller.
// `instance_homes` records the enclosing instance's home for closures lifted
// inside an instance body — since round 3 the meet of definer and resolving
// scopes; FILING is unchanged (the closure's signature lives in the type section
// of the module it is emitted from).

/// The `Fn`-taking helper both closure programs apply their closure through.
const APPLY_HELPER: &str = "pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n";

/// An UNTRUSTED module's generic that wraps `handle Unsafe` in a closure.
const UNTRUSTED_GENERIC_CLOSURE_UNSAFE: &str = "#[ring(outer)]\nmodule defs;\n\
     pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
     pub fn danger<T>(x: T) -> i64 ! {} { return h(fn(y: i64) -> i64 { handle Unsafe { let _x: i64 = 1; }; return 0; }); }\n";

/// REGRESSION (round 2): the closure is the untrusted module's code wherever the
/// generic is instantiated — exactly E002, matching the non-generic twin (the meet
/// includes the untrusted definer). Before round 2 (and on the pre-routing
/// compiler): accepted, because the closure was named `user::__closure_N` and
/// checked under the TRUSTED caller alone.
#[test]
fn closure_lifted_in_an_instance_is_checked_under_definer_trust() {
    let src = format!("{UNTRUSTED_GENERIC_CLOSURE_UNSAFE}{TRUSTED_USER_OF_DEFS}");
    assert_eq!(codes("defs.sigil", &src), set(&["E002"]));
}

/// SC-P4 controls for the closure trust direction: the non-generic twin (whose
/// closure always carried the definer's prefix) and the generic instantiated from
/// its OWN untrusted module are both exactly E002 — so E002 is a live detector
/// through a closure on this layout.
#[test]
fn closure_trust_twins_prove_e002_fires_through_a_closure() {
    let nongeneric = format!(
        "#[ring(outer)]\nmodule defs;\n{APPLY_HELPER}\
         pub fn danger(x: i64) -> i64 ! {{}} {{ return h(fn(y: i64) -> i64 {{ handle Unsafe {{ let _x: i64 = 1; }}; return 0; }}); }}\n"
    );
    assert_eq!(
        codes("defs.sigil", &format!("{nongeneric}{TRUSTED_USER_OF_DEFS}")),
        set(&["E002"]),
        "NON-generic untrusted closure `handle Unsafe` called from a trusted module"
    );
    let same_module = format!(
        "{UNTRUSTED_GENERIC_CLOSURE_UNSAFE}fn boot() -> i64 ! {{}} {{ return danger(1); }}\n"
    );
    assert_eq!(
        codes("defs.sigil", &same_module),
        set(&["E002"]),
        "generic with the closure instantiated from its own untrusted module"
    );
}

/// Round 3 (replaces round 2's accept pin): a TRUSTED module's generic that wraps
/// `handle Unsafe` in a closure, instantiated from an UNTRUSTED module, is exactly
/// E002 — the closure is lifted while the instance body is re-checked in the untrusted
/// caller's scope, so it holds trust only if both are trusted (main `ae026aec`: E002
/// as well, so no behavior change against main). Its NON-generic twin is accepted: a
/// non-generic body resolves only in its own trusted module. The generic/non-generic
/// verdicts differ here BY DESIGN of the fail-closed meet; re-checking free-fn
/// instances in the definer's scope (SR-019's follow-up) is what would reunite them.
#[test]
fn trusted_generic_closure_instantiated_from_untrusted_caller_is_e002() {
    let trusted_defs = format!(
        "#[ring(outer)] #[trusted]\nmodule defs;\n{APPLY_HELPER}\
         pub fn danger<T>(x: T) -> i64 ! {{}} {{ return h(fn(y: i64) -> i64 {{ handle Unsafe {{ let _x: i64 = 1; }}; return 0; }}); }}\n"
    );
    let untrusted_user = "#[ring(outer)]\nmodule user;\n\
         use sigil::defs;\n\
         fn boot() -> i64 ! {} { return danger(1); }\n";
    assert_eq!(
        codes("defs.sigil", &format!("{trusted_defs}{untrusted_user}")),
        set(&["E002"]),
        "trusted definer, untrusted caller: the meet is untrusted"
    );
    let nongeneric = format!(
        "#[ring(outer)] #[trusted]\nmodule defs;\n{APPLY_HELPER}\
         pub fn danger(x: i64) -> i64 ! {{}} {{ return h(fn(y: i64) -> i64 {{ handle Unsafe {{ let _x: i64 = 1; }}; return 0; }}); }}\n"
    );
    assert_eq!(
        codes("defs.sigil", &format!("{nongeneric}{untrusted_user}")),
        BTreeSet::new(),
        "the non-generic twin resolves only in its own trusted module: accepted"
    );
}

// ── The remaining round-2 review repros: trust borrowed from a TRUSTED caller ──
//
// Each program below was ACCEPTED by main `ae026aec` and is exactly E002 on this
// branch: an untrusted module's `handle Unsafe` (bare, in a nested closure, or in a
// closure lifted AFTER a nested instance's re-check) ran with the authority of a
// trusted module that either sorted first (main filed the instance under it) or
// was the caller whose name prefix the lifted closure carries. The non-generic
// twins are the SC-P4 controls: E002 fires on the same layouts without generics.

/// An UNTRUSTED module's generic whose `handle Unsafe` sits two closures deep.
const UNTRUSTED_GENERIC_NESTED_CLOSURE: &str = "#[ring(outer)]\nmodule defs;\n\
     pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
     pub fn danger<T>(x: T) -> i64 ! {} { return h(fn(y: i64) -> i64 { return h(fn(z: i64) -> i64 { handle Unsafe { let _x: i64 = 1; }; return 0; }); }); }\n";

/// A TRUSTED module whose pure generic `tg` is instantiated INSIDE the untrusted
/// generic below, immediately before that generic lifts its closure.
const TRUSTED_TG: &str = "#[ring(outer)] #[trusted]\nmodule tr;\n\
     pub fn tg<T>(x: T) -> i64 ! {} { return 0; }\n";

/// An UNTRUSTED generic that instantiates `tr::tg`, THEN lifts a closure holding
/// `handle Unsafe`: the closure must get `danger`'s home back, not `tg`'s.
const UNTRUSTED_GENERIC_AFTER_NESTED_INSTANCE: &str = "#[ring(outer)]\nmodule defs;\n\
     pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
     pub fn danger<T>(x: T) -> i64 ! {} { let a: i64 = tg(x); return h(fn(y: i64) -> i64 { handle Unsafe { let _x: i64 = 1; }; return 0; }); }\n";

/// Review repro `shadow`: the trusted definer sorts FIRST; the untrusted caller's
/// own `helper` shadows the definer's inside the generic's `handle Unsafe`.
const SHADOW_TRUSTED_DEFS_FIRST: &str = "#[ring(outer)] #[trusted]\nmodule defs;\n\
     fn helper() -> i64 ! { Unsafe } { return 111; }\n\
     pub fn danger<T>(x: T) -> i64 ! {} { handle Unsafe { let r: i64 = helper(); }; return 0; }\n\
     #[ring(outer)]\nmodule user;\n\
     use sigil::defs;\n\
     fn helper() -> i64 ! { Unsafe } { return 777; }\n\
     pub fn boot() -> i64 ! {} { return danger(1); }\n";

#[test]
fn review_repros_borrowing_a_trusted_modules_authority_are_e002() {
    assert_eq!(
        codes(
            "user.sigil",
            &format!("{TRUSTED_USER_OF_DEFS}{UNTRUSTED_GENERIC_HANDLE_UNSAFE}")
        ),
        set(&["E002"]),
        "review repro `e002-userfirst`: trusted caller first (main: accepted)"
    );
    assert_eq!(
        codes(
            "defs.sigil",
            &format!("{UNTRUSTED_GENERIC_NESTED_CLOSURE}{TRUSTED_USER_OF_DEFS}")
        ),
        set(&["E002"]),
        "review repro `nested-closure` (main: accepted)"
    );
    assert_eq!(
        codes(
            "tr.sigil",
            &format!("{TRUSTED_TG}{UNTRUSTED_GENERIC_AFTER_NESTED_INSTANCE}{TRUSTED_USER_OF_DEFS}")
        ),
        set(&["E002"]),
        "review repro `nested-instance-restore` (main: accepted)"
    );
    assert_eq!(
        codes("defs.sigil", SHADOW_TRUSTED_DEFS_FIRST),
        set(&["E002"]),
        "review repro `shadow`: trusted definer first (main: accepted)"
    );
    // SC-P4: the non-generic twins of the first three are E002 on the same layouts.
    let degeneric = |src: &str| src.replace("danger<T>(x: T)", "danger(x: i64)");
    assert_eq!(
        codes(
            "user.sigil",
            &format!(
                "{TRUSTED_USER_OF_DEFS}{}",
                degeneric(UNTRUSTED_GENERIC_HANDLE_UNSAFE)
            )
        ),
        set(&["E002"]),
        "control: `e002-userfirst` without generics"
    );
    assert_eq!(
        codes(
            "defs.sigil",
            &format!(
                "{}{TRUSTED_USER_OF_DEFS}",
                degeneric(UNTRUSTED_GENERIC_NESTED_CLOSURE)
            )
        ),
        set(&["E002"]),
        "control: `nested-closure` without generics"
    );
    assert_eq!(
        codes(
            "tr.sigil",
            &format!(
                "{TRUSTED_TG}{}{TRUSTED_USER_OF_DEFS}",
                degeneric(UNTRUSTED_GENERIC_AFTER_NESTED_INSTANCE)
            )
        ),
        set(&["E002"]),
        "control: `nested-instance-restore` without generics"
    );
}

// ── Scope of the accept direction: the ring-blind second E001 emitter ─────────
//
// `governing_context` is consulted by `check_effects` and `check_rings` only. The
// other E001 emitter, `bind_and_check_effect_rows` (`type_check/expressions/calls.rs`),
// runs in the TYPE-CHECK pass at a generic call site and reads no module at all —
// no ring, no trust — so routing can neither enable nor suppress it. The inner-ring
// exemption pinned above (every governing module inner) is therefore an exemption
// from `check_effects` ONLY: a generic call inside such a generic that passes an
// effectful closure to a concrete empty-row formal still rejects, exactly as its
// non-generic twin does (measured identical on main `ae026aec`, rounds 1-2 and
// round 3).

/// An INNER-ring definer whose generic `g<T>` passes a `Log`-performing closure to
/// a generic callee's concrete `! { }` formal. `{BODY}` is the closure body.
const INNER_DEFINER_GENERIC_ROW_ARG: &str = "module app;\n\
     effect Log;\n\
     fn logit() -> i64 ! { Log } { return 0; }\n\
     fn take<T>(f: Fn(i64) -> i64 ! { }, x: T) -> i64 { return f(1); }\n\
     fn g<T>(x: T) -> i64 { return take(fn(y: i64) -> i64 { {BODY} }, x); }\n\
     fn boot() -> i64 { return g(1); }\n";

/// The inner-ring exemption does not reach the ring-blind row check: with an outer
/// module first, the inner-ring definer's generic (instantiated from its own inner
/// module, so every governing module is inner) is exactly {E001}, as is its
/// non-generic twin; the pure-closure control on the same layout is accepted by
/// every checker (pinned at the checker layer), so the rejection is the closure's
/// row and not the layout. End to end that control is refused at emission with
/// exactly {R007}: its instances are filed under the outer first module (#768).
#[test]
fn inner_ring_definer_accept_does_not_reach_the_ring_blind_row_check() {
    let effectful = INNER_DEFINER_GENERIC_ROW_ARG.replace("{BODY}", "return logit();");
    assert_eq!(
        codes("first.sigil", &format!("{OUTER_FIRST}{effectful}")),
        set(&["E001"]),
        "inner-ring definer, generic: the call-site row check fires regardless of routing"
    );
    let twin = effectful.replace("fn g<T>(x: T)", "fn g(x: i64)");
    assert_eq!(
        codes("first.sigil", &format!("{OUTER_FIRST}{twin}")),
        set(&["E001"]),
        "the non-generic twin agrees"
    );
    let pure = INNER_DEFINER_GENERIC_ROW_ARG.replace("{BODY}", "return y;");
    assert_meet_accepts_but_emission_refuses(
        "first.sigil",
        &format!("{OUTER_FIRST}{pure}"),
        "control: a pure closure on the same layout",
    );
}

// ── KNOWN GAP (not closed here): generic free fns resolve program-wide ────────
//
// A generic free fn is looked up by BARE NAME in a program-wide table
// (`universe.generic_fns`), before and independently of `use` scope and the R004
// cross-ring rule. So an inner-ring module can call an outer-ring module's pure
// generic directly — no `use`, no `grant` — where the non-generic twin is exactly
// T062 without `use` and exactly R004 with it. The meet above bounds what such an
// instance may DO (it is walked, untrusted and under both rings' rules — see
// `outer_generic_resolving_an_inner_callers_extern_is_r003`); it does not make the
// call itself legal-by-construction. Recorded in `tests/attack/KNOWN_GAPS.md`
// ("Generic functions resolve by bare name across modules"). This pin measures the gap
// as it stands in the integrated tree; it is expected to FAIL when the gap is
// closed, and the fix must replace it with the rejecting verdicts.
//
// The gap is a CHECKER-layer gap, pinned with `checker_codes`: no checker rejects
// the call. End to end, the layout with the outer definer first files the instance
// in the OUTER ring while its caller is inner, so the emission gate refuses it with
// exactly {R007} (main `ae026aec` accepted it); that refusal is a by-product of
// filing, not a closed gap, and it would lift with #768. With the inner caller first
// the instance is filed in the caller's own ring and the pipeline accepts the call
// outright — the gap's end-to-end witness.

const OUTER_PURE_GENERIC: &str = "#[ring(outer)]\nmodule defs;\n\
     pub fn og<T>(x: T) -> i64 ! {} { return 7; }\n";

const INNER_CALLER_OF_OG: &str = "module app;\n\
     fn boot() -> i64 { return og(1); }\n";

#[test]
fn known_gap_generic_free_fn_call_bypasses_use_and_r004() {
    assert_meet_accepts_but_emission_refuses(
        "defs.sigil",
        &format!("{OUTER_PURE_GENERIC}{INNER_CALLER_OF_OG}"),
        "KNOWN GAP: inner module calls an outer generic with no `use` and no grant",
    );
    let with_use = INNER_CALLER_OF_OG.replace("module app;\n", "module app;\nuse sigil::defs;\n");
    assert_meet_accepts_but_emission_refuses(
        "defs.sigil",
        &format!("{OUTER_PURE_GENERIC}{with_use}"),
        "KNOWN GAP: with `use`, still no cross-ring rejection by any checker",
    );
    assert_eq!(
        codes(
            "app.sigil",
            &format!("{INNER_CALLER_OF_OG}{OUTER_PURE_GENERIC}")
        ),
        BTreeSet::new(),
        "KNOWN GAP, end to end: inner caller first, the instance is filed in its ring"
    );
    let nongeneric = OUTER_PURE_GENERIC.replace("og<T>(x: T)", "og(x: i64)");
    assert_eq!(
        codes("defs.sigil", &format!("{nongeneric}{INNER_CALLER_OF_OG}")),
        set(&["T062"]),
        "control: the non-generic twin without `use` does not resolve"
    );
    assert_eq!(
        codes("defs.sigil", &format!("{nongeneric}{with_use}")),
        set(&["R004"]),
        "control: the non-generic twin with `use` is a cross-ring call"
    );
}
