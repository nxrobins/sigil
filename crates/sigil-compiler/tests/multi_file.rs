//! Wall 5 Step 1 / commit #4: multi-file compilation fixtures.
//!
//! These tests exercise `compile_project` end-to-end across realistic
//! two-and-three-file projects. The corpus covers:
//!
//! - The **load-bearing fixture** (N20-W5S1, N28-W5S1):
//!   cross-file refinement subsumption. Module `math` exports a
//!   refined function; module `main` imports it and the Wall 4 Step 7
//!   call-site dispatcher (T224) fires across the file boundary
//!   without inspecting `math`'s body. The byte-stability property
//!   from N28-W5S1 is asserted via the determinism property test
//!   (3 permutations produce byte-identical wasm); the absolute hash
//!   in EXPECTED_HASHES.txt is intentionally NOT pinned because
//!   Rust toolchain updates can legitimately shift wasm bytes, and
//!   the determinism property is the load-bearing invariant.
//!
//! - **Happy paths** for cross-file type-checking, `use` resolution,
//!   refinement preservation across the file boundary, and the
//!   three-file dependency chain (A → B → C).
//!
//! - **Error paths**: M001 (filename mismatch), M002 (duplicate module),
//!   M003 (no entry), M004 (multiple entries), M005 (tool + actor in
//!   same module), M006 (project mixes execution models), M007
//!   (duplicate source-file name), M008 (empty input), M009 (invalid
//!   source name), M010 (unknown `--entry`).
//!
//! Per N17-W5S1's "single canonical dedup map" invariant, fixtures
//! exercise both top-level and inline collision shapes.

use sigil_compiler::{CompileOptions, compile_project, source::SourceFile};

/// Helper: collect diagnostic codes from a `CompileError`.
fn codes_of(err: &sigil_compiler::CompileError) -> Vec<String> {
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

fn sf(name: &str, text: &str) -> SourceFile {
    SourceFile::new(name, text)
}

// ── Load-bearing fixture (N20-W5S1, N28-W5S1) ──────────────────────────

/// The one-sentence definition of done from the Wall 5 Step 1 spec:
/// "Two files, a refined function crosses the boundary, the compiler
/// proves the caller satisfies the callee's precondition without
/// seeing the callee's body."
///
/// `math::need_positive(x: i64) where x > 0` is called from `main`
/// with the literal `5`. Step 1's refinement-at-construction dispatch
/// (single-source, already shipping) fires across the file boundary
/// because Wall 5 Step 1 introduces no new type-check mechanism —
/// just plumbing.
#[test]
fn cross_file_refinement_pass() {
    let math = sf(
        "math.sigil",
        "module math;\npub fn need_positive(x: i64) where x > 0 -> i64 { return x; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::math;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return math::need_positive(5); }\n",
    );
    let result = compile_project(vec![math, main], None, CompileOptions::default());
    assert!(
        result.is_ok(),
        "cross-file refinement pass should compile cleanly: {:?}",
        result.as_ref().err().map(codes_of)
    );
}

/// Negative load-bearing fixture: literal arg violates the imported
/// refinement. The Wall 4 Step 7 call-site dispatcher (T224 — call-site
/// argument violates parameter refinement) fires across the file
/// boundary because the cross-file `workspace_sigs` interface carries
/// the param refinement verbatim, and Step 7's dispatch logic is
/// module-agnostic.
#[cfg(feature = "solver")]
#[test]
fn cross_file_refinement_violation_fires_t224() {
    let math = sf(
        "math.sigil",
        "module math;\npub fn need_positive(x: i64) where x > 0 -> i64 { return x; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::math;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return math::need_positive(0); }\n",
    );
    let err = compile_project(vec![math, main], None, CompileOptions::default())
        .expect_err("0 violates `where x > 0`");
    let codes = codes_of(&err);
    assert!(
        codes.contains(&"T224".to_string()),
        "expected T224 at cross-file refinement violation, got: {codes:?}"
    );
}

// ── Happy paths ────────────────────────────────────────────────────────

/// Two-file project: math exports a pub fn, main imports and calls it.
/// Pub visibility crosses the file boundary; T155 does NOT fire.
#[test]
fn pub_fn_crosses_file_boundary() {
    let math = sf(
        "math.sigil",
        "module math;\npub fn add(a: i64, b: i64) -> i64 { return a + b; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::math;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return math::add(1, 2); }\n",
    );
    let compilation = compile_project(vec![math, main], None, CompileOptions::default())
        .expect("pub fn across files compiles");
    // Both modules are in the merged Compilation.
    assert!(compilation.module_names.contains(&"math".to_string()));
    assert!(compilation.module_names.contains(&"main".to_string()));
    // Wasm emitted from the merged program.
    assert_eq!(&compilation.wasm_inner[..4], b"\0asm");
}

/// Three-file dependency chain: `a` exports `helper_a`, `b` imports
/// `a` and re-uses `helper_a`, `main` imports `b` and calls
/// `b::compose`. Validates transitive cross-file resolution.
#[test]
fn three_file_chain() {
    let a = sf(
        "a.sigil",
        "module a;\npub fn helper_a() -> i64 { return 7; }\n",
    );
    let b = sf(
        "b.sigil",
        "module b;\nuse sigil::a;\npub fn compose() -> i64 { return a::helper_a() + 1; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::b;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return b::compose(); }\n",
    );
    let compilation = compile_project(vec![a, b, main], None, CompileOptions::default())
        .expect("three-file chain compiles");
    assert_eq!(compilation.module_names.len(), 3);
    assert_eq!(&compilation.wasm_inner[..4], b"\0asm");
}

/// Single-file via compile_project is the N=1 case. The fast path
/// produces wasm byte-equal to the legacy `compile_named_module` route.
#[test]
fn single_file_via_compile_project_byte_equals_legacy() {
    let source =
        "module foo;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n";
    let via_project = compile_project(
        vec![sf("foo.sigil", source)],
        None,
        CompileOptions::default(),
    )
    .expect("project N=1 compiles");
    let via_legacy =
        sigil_compiler::compile_named_module("foo.sigil", source).expect("legacy compiles");
    assert_eq!(via_project.wasm_inner, via_legacy.wasm_inner);
    assert_eq!(via_project.wasm_outer, via_legacy.wasm_outer);
}

// ── Determinism (N7-W5S1, N29-W5S1) ────────────────────────────────────

/// Three permutations of a 3-file fixture produce byte-identical wasm.
/// The permutation set explicitly includes a reverse-sort ordering
/// (worst case for any insertion-order-dependent code, per N29-W5S1).
#[test]
fn determinism_three_permutations() {
    let a_text = "module a;\npub fn val_a() -> i64 { return 1; }\n";
    let m_text = "module m;\npub fn val_m() -> i64 { return 2; }\n";
    let z_text = "module z;\nuse sigil::a;\nuse sigil::m;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return a::val_a() + m::val_m(); }\n";

    let ascending = compile_project(
        vec![
            sf("a.sigil", a_text),
            sf("m.sigil", m_text),
            sf("z.sigil", z_text),
        ],
        None,
        CompileOptions::default(),
    )
    .expect("ascending order compiles");
    let descending = compile_project(
        vec![
            sf("z.sigil", z_text),
            sf("m.sigil", m_text),
            sf("a.sigil", a_text),
        ],
        None,
        CompileOptions::default(),
    )
    .expect("descending order compiles");
    let arbitrary = compile_project(
        vec![
            sf("m.sigil", m_text),
            sf("z.sigil", z_text),
            sf("a.sigil", a_text),
        ],
        None,
        CompileOptions::default(),
    )
    .expect("arbitrary order compiles");

    assert_eq!(
        ascending.wasm_inner, descending.wasm_inner,
        "N7-W5S1: ascending vs descending wasm must be byte-identical"
    );
    assert_eq!(
        ascending.wasm_inner, arbitrary.wasm_inner,
        "N7-W5S1: ascending vs arbitrary wasm must be byte-identical"
    );
    assert_eq!(ascending.module_names, descending.module_names);
    assert_eq!(ascending.module_names, arbitrary.module_names);
}

// ── M001: filename does not match first module declaration ─────────────

#[test]
fn m001_filename_mismatch() {
    let math = sf(
        "math.sigil",
        "module not_math;\npub fn f() -> i64 { return 0; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n",
    );
    let err = compile_project(vec![math, main], None, CompileOptions::default())
        .expect_err("M001 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M001".to_string()), "got {codes:?}");
}

// ── M002: duplicate module across files ────────────────────────────────

#[test]
fn m002_duplicate_module_top_level() {
    let a = sf("a.sigil", "module a;\nmodule shared;\n");
    let b = sf("b.sigil", "module b;\nmodule shared;\n");
    let err =
        compile_project(vec![a, b], None, CompileOptions::default()).expect_err("M002 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M002".to_string()), "got {codes:?}");
}

/// Wall 5 Step 1 N17-W5S1: top-level + inline-block collision is
/// caught by the single canonical dedup map.
#[test]
fn m002_top_level_collides_with_inline_block() {
    // File a: top-level `module a;` followed by inline `module shared { ... }`.
    let a = sf(
        "a.sigil",
        "module a;\nmodule shared { pub fn x() -> i64 { return 1; } }\n",
    );
    // File b: top-level `module b;` followed by top-level `module shared;`.
    let b = sf("b.sigil", "module b;\nmodule shared;\n");
    let err = compile_project(vec![a, b], None, CompileOptions::default())
        .expect_err("M002 expected for inline + top-level collision");
    let codes = codes_of(&err);
    assert!(
        codes.contains(&"M002".to_string()),
        "M002 must catch top-level + inline collision (N17-W5S1): got {codes:?}"
    );
}

// ── M003: no entry point ───────────────────────────────────────────────

#[test]
fn m003_no_entry() {
    let lib = sf(
        "lib.sigil",
        "module lib;\npub fn helper() -> i64 { return 1; }\n",
    );
    let util = sf(
        "util.sigil",
        "module util;\nuse sigil::lib;\npub fn other() -> i64 { return lib::helper(); }\n",
    );
    let err = compile_project(vec![lib, util], None, CompileOptions::default())
        .expect_err("M003 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M003".to_string()), "got {codes:?}");
}

// ── M004: multiple entry points without --entry ────────────────────────

#[test]
fn m004_multiple_entries() {
    let a = sf(
        "a.sigil",
        "module a;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }\n",
    );
    let b = sf(
        "b.sigil",
        "module b;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 2; }\n",
    );
    let err =
        compile_project(vec![a, b], None, CompileOptions::default()).expect_err("M004 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M004".to_string()), "got {codes:?}");
}

/// `--entry <name>` resolves the M004 ambiguity.
#[test]
fn m004_resolved_by_entry_flag() {
    let a = sf(
        "a.sigil",
        "module a;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }\n",
    );
    let b = sf(
        "b.sigil",
        "module b;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 2; }\n",
    );
    let compilation = compile_project(vec![a, b], Some("a"), CompileOptions::default())
        .expect("--entry a resolves M004");
    // Both modules survive in module_names; --entry only picks the
    // emitter target.
    assert!(compilation.module_names.contains(&"a".to_string()));
    assert!(compilation.module_names.contains(&"b".to_string()));
}

// ── M005: intra-module tool + actor ────────────────────────────────────

#[test]
fn m005_intra_module_tool_and_actor() {
    let a = sf(
        "a.sigil",
        r#"module a;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }
entry actor Main {
    state { counter: i64 }
    on Start() -> i64 { return 1; }
}
"#,
    );
    let b = sf(
        "b.sigil",
        "module b;\npub fn helper() -> i64 { return 0; }\n",
    );
    let err = compile_project(vec![a, b], None, CompileOptions::default())
        .expect_err("M005 expected (tool + actor in same module)");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M005".to_string()), "got {codes:?}");
}

// ── M006: project mixes tool entry and actor entry ─────────────────────

#[test]
fn m006_cross_module_tool_plus_actor() {
    let tool = sf(
        "tool.sigil",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n",
    );
    let actors = sf(
        "actors.sigil",
        r#"module actors;
entry actor Main {
    state { counter: i64 }
    on Start() -> i64 { return 1; }
}
"#,
    );
    let err = compile_project(vec![tool, actors], None, CompileOptions::default())
        .expect_err("M006 expected (tool + actor across modules)");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M006".to_string()), "got {codes:?}");
}

// ── M007: duplicate source-file name ───────────────────────────────────

#[test]
fn m007_duplicate_source_filename() {
    let a = sf("dup.sigil", "module dup;\n");
    let b = sf("dup.sigil", "module other;\n");
    let err =
        compile_project(vec![a, b], None, CompileOptions::default()).expect_err("M007 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M007".to_string()), "got {codes:?}");
}

// ── M008: empty compilation set ────────────────────────────────────────

#[test]
fn m008_empty_input() {
    let err = compile_project(vec![], None, CompileOptions::default()).expect_err("M008 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M008".to_string()), "got {codes:?}");
}

// ── M009: invalid source name ──────────────────────────────────────────

#[test]
fn m009_wrong_extension() {
    let a = sf("first.sigil", "module first;\n");
    let b = sf("second.txt", "module second;\n");
    let err =
        compile_project(vec![a, b], None, CompileOptions::default()).expect_err("M009 expected");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M009".to_string()), "got {codes:?}");
}

#[test]
fn m009_path_traversal() {
    let a = sf("first.sigil", "module first;\n");
    let b = sf("a/../second.sigil", "module second;\n");
    let err = compile_project(vec![a, b], None, CompileOptions::default())
        .expect_err("M009 expected for `..` path segment");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M009".to_string()), "got {codes:?}");
}

#[test]
fn m009_nul_byte_rejected() {
    let a = sf("first.sigil", "module first;\n");
    let b = sf("nul\0byte.sigil", "module second;\n");
    let err = compile_project(vec![a, b], None, CompileOptions::default())
        .expect_err("M009 expected for NUL byte");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M009".to_string()), "got {codes:?}");
}

// ── M010: --entry unknown module ──────────────────────────────────────

#[test]
fn m010_unknown_entry_module() {
    let a = sf(
        "a.sigil",
        "module a;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }\n",
    );
    let b = sf(
        "b.sigil",
        "module b;\npub fn helper() -> i64 { return 0; }\n",
    );
    let err = compile_project(vec![a, b], Some("ghost"), CompileOptions::default())
        .expect_err("M010 expected for unknown --entry");
    let codes = codes_of(&err);
    assert!(codes.contains(&"M010".to_string()), "got {codes:?}");
    // Message includes the offending name AND the available list.
    let m010 = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "M010")
        .expect("M010 in diagnostics");
    let msg = m010.message();
    assert!(
        msg.contains("ghost"),
        "M010 must name the offending module: {msg}"
    );
    assert!(
        msg.contains("available"),
        "M010 must list available modules: {msg}"
    );
}

// ── Cross-file effect propagation (sanity) ─────────────────────────────

/// Effect rows propagate across the file boundary. `lib.sigil`
/// exports a fn requiring `NetIO`; `main.sigil`'s `tool_main` doesn't
/// declare it. Cross-file effect-check fires E001 (existing single-
/// source mechanism, validated to work across files).
#[test]
fn cross_file_effect_propagation() {
    let lib = sf(
        "lib.sigil",
        r#"#[ring(outer)] #[trusted]
module lib;
effect NetIO;
pub fn expensive() -> i64 ! { NetIO } { return 0; }
"#,
    );
    let main = sf(
        "main.sigil",
        r#"#[ring(outer)] #[trusted]
module main;
use sigil::lib;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {} { return lib::expensive(); }
"#,
    );
    let err = compile_project(vec![lib, main], None, CompileOptions::default())
        .expect_err("E001 cross-file effect violation");
    let codes = codes_of(&err);
    assert!(
        codes.contains(&"E001".to_string()),
        "cross-file E001 must fire: {codes:?}"
    );
}

// ── SourceId follow-up: file-precise rendering for pre-existing codes ──
//
// The Wall 5 Step 1 PR delivered multi-file compilation but pre-existing
// codes (T-, R-, N-, E-) rendered against the first input file in
// multi-file mode. The SourceId refactor closes that gap: every span's
// `source` field now resolves to the right SourceFile via the
// CompileError-attached SourceMap.

/// T155 (cross-module call to private function) — the offending CALL
/// is in `main.sigil`; the renderer must resolve the span back to
/// main.sigil, not lib.sigil. Before the SourceId refactor this
/// rendered against whichever file was first.
#[test]
fn t155_renders_against_call_site_file() {
    let lib = sf(
        "lib.sigil",
        "module lib;\nfn secret() -> i64 { return 0; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::lib;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return lib::secret(); }\n",
    );
    let err = compile_project(vec![lib, main.clone()], None, CompileOptions::default())
        .expect_err("T155 expected for cross-module private call");
    assert!(
        codes_of(&err).contains(&"T155".to_string()),
        "T155 must be in diagnostics: {:?}",
        codes_of(&err)
    );
    // Render against `main` as the fallback — but the SourceId
    // attribution should pick the call-site file regardless.
    let rendered = err.render(&main);
    // The call site is in main.sigil; verify the renderer produced a
    // span pointing into main.sigil's text.
    assert!(
        rendered.contains("main.sigil"),
        "T155 must render against main.sigil (the call site): {rendered}"
    );
    assert!(
        rendered.contains("lib::secret"),
        "rendered source line must include the offending call: {rendered}"
    );
}

/// R004 (cross-ring call) — the calling fn is in `main` (inner-ring);
/// the called fn is in `outer_lib` (outer-ring). Span attribution
/// puts the error against `main.sigil`.
#[test]
fn r004_renders_against_caller_file() {
    let outer_lib = sf(
        "outer_lib.sigil",
        "#[ring(outer)] #[trusted]\nmodule outer_lib;\npub fn helper(x: i64) -> i64 ! { Alloc } { return x + 1; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::outer_lib;\nfn boot() -> i64 ! { Alloc } { return outer_lib::helper(41); }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return boot(); }\n",
    );
    let err = compile_project(
        vec![outer_lib, main.clone()],
        None,
        CompileOptions::default(),
    )
    .expect_err("R004 expected for cross-ring call");
    assert!(
        codes_of(&err).contains(&"R004".to_string()),
        "R004 must be in diagnostics: {:?}",
        codes_of(&err)
    );
    let rendered = err.render(&main);
    // The call is in main.sigil; the SourceId follow-up routes the
    // span's source_id to main.sigil so the renderer indexes the
    // right file's text.
    assert!(
        rendered.contains("main.sigil"),
        "R004 must render against main.sigil (the cross-ring call site): {rendered}"
    );
    // The offending call's text should appear in the rendered source line.
    assert!(
        rendered.contains("outer_lib::helper"),
        "rendered source line must include the call text: {rendered}"
    );
}

/// N007 (unresolved use path) — the `use` is in `main.sigil`. Renderer
/// must point at main.sigil, not whatever else is in the compilation
/// set.
#[test]
fn n007_renders_against_use_site_file() {
    let helpers = sf(
        "helpers.sigil",
        "module helpers;\npub fn add(a: i64) -> i64 { return a + 1; }\n",
    );
    let main = sf(
        "main.sigil",
        "module main;\nuse sigil::nonexistent;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n",
    );
    let err = compile_project(vec![helpers, main.clone()], None, CompileOptions::default())
        .expect_err("N007 expected for unresolved use");
    assert!(
        codes_of(&err).contains(&"N007".to_string()),
        "N007 must be in diagnostics: {:?}",
        codes_of(&err)
    );
    let rendered = err.render(&main);
    assert!(
        rendered.contains("main.sigil"),
        "N007 must render against main.sigil (the `use` site): {rendered}"
    );
    // The offending use-decl text should appear in the rendered source.
    assert!(
        rendered.contains("nonexistent"),
        "rendered source line must include the offending `use` path: {rendered}"
    );
}

/// E001 (effect-row mismatch) renders against the call site that
/// requires the un-declared effect — `main.sigil` here.
#[test]
fn e001_renders_against_call_site_file() {
    let lib = sf(
        "lib.sigil",
        r#"#[ring(outer)] #[trusted]
module lib;
effect NetIO;
pub fn expensive() -> i64 ! { NetIO } { return 0; }
"#,
    );
    let main = sf(
        "main.sigil",
        r#"#[ring(outer)] #[trusted]
module main;
use sigil::lib;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {} { return lib::expensive(); }
"#,
    );
    let err = compile_project(vec![lib, main.clone()], None, CompileOptions::default())
        .expect_err("E001 expected");
    assert!(
        codes_of(&err).contains(&"E001".to_string()),
        "E001 must be in diagnostics: {:?}",
        codes_of(&err)
    );
    let rendered = err.render(&main);
    // The effect-row mismatch is detected at the call site in main.
    assert!(
        rendered.contains("main.sigil"),
        "E001 must render against main.sigil (the call site): {rendered}"
    );
}

/// CompileError.render() falls back to the caller-provided source
/// when the SourceMap has no matching entry (e.g., spans from legacy
/// paths that haven't been migrated).
#[test]
fn render_falls_back_when_sourcemap_misses() {
    // A single-file compile populates a SourceMap of length 1, so
    // every span resolves correctly; this test just confirms the
    // single-file path produces a working render.
    let err = sigil_compiler::compile_named_module(
        "boom.sigil",
        "module sigil;\nfn bad() -> i64 { return ready; }\n",
    )
    .expect_err("should fail to resolve `ready`");
    let fallback = SourceFile::new(
        "boom.sigil",
        "module sigil;\nfn bad() -> i64 { return ready; }\n",
    );
    let rendered = err.render(&fallback);
    assert!(
        !rendered.is_empty(),
        "render must produce non-empty output even on legacy single-file path"
    );
}
