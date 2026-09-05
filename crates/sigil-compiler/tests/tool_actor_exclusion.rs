//! M011 — a tool project must declare no actors (RTC-NOOP slice 2).
//!
//! A compilation that declares `pub fn tool_main` targets the ephemeral forge,
//! which cannot run actors. Any `actor` definition (entry OR non-entry) is dead
//! code whose `send`/`spawn`/capability machinery traps in the forge (RTC-NOOP
//! slice 1). The gate is the true-north compile-time signal: an agent who writes
//! a tool with stray actor code gets an in-loop error, not a clean compile of
//! inert machinery.
//!
//! The gate lives at `compile_ast_with_options`, the single convergence point
//! both the single-file and multi-file paths traverse — so it catches the
//! single-file fast path (`sigil check <one.sigil>`, the primary agent case)
//! that M001–M006 bypass entirely. See docs/specs/runtime-differential-census.md.

use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, compile_named_module, compile_project};

fn codes_of(err: &sigil_compiler::CompileError) -> Vec<String> {
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_owned())
        .collect()
}

/// Compile a single source through the single-file fast path (what
/// `sigil check <file>` and `compile_named_module` use).
fn single(src: &str) -> Result<sigil_compiler::Compilation, sigil_compiler::CompileError> {
    compile_named_module("probe.sigil", src)
}

/// Compile a genuine multi-file project (>=2 sources) through the multi-file
/// path where M001–M006 run.
fn multi(
    files: &[(&str, &str)],
) -> Result<sigil_compiler::Compilation, sigil_compiler::CompileError> {
    let sources: Vec<SourceFile> = files
        .iter()
        .map(|(name, text)| SourceFile::new(*name, *text))
        .collect();
    compile_project(sources, None, CompileOptions::default())
}

const TOOL_MOD: &str =
    "module toolm;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n";
const NONENTRY_ACTOR_MOD: &str = "module helper;\ncap type Fuel {}\nactor Worker {\n    init(fuel: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\n";

// ── REJECT: M011 fires wherever a tool project carries an actor ─────────────

#[test]
fn reject_single_file_tool_plus_nonentry_actor() {
    // P1: the #1 agent case — one file, tool_main + a non-entry actor. The
    // single-file fast path bypasses M005/M006; only M011 (at the convergence)
    // catches it.
    let src = "module tool;\npub fn tool_main(a: i64, b: i64) -> i64 { return 0; }\ncap type Fuel {}\nactor Worker {\n    init(fuel: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\n";
    let err = single(src).expect_err("tool + non-entry actor must be rejected");
    assert!(
        codes_of(&err).contains(&"M011".to_string()),
        "expected M011, got {:?}",
        codes_of(&err)
    );
}

#[test]
fn reject_multi_file_tool_plus_nonentry_actor() {
    // P2: two files, tool module + non-entry actor module. Non-entry actors are
    // invisible to M005/M006's `is_entry_actor`; M011 catches the mix.
    let err = multi(&[
        ("toolm.sigil", TOOL_MOD),
        ("helper.sigil", NONENTRY_ACTOR_MOD),
    ])
    .expect_err("multi-file tool + non-entry actor must be rejected");
    assert!(
        codes_of(&err).contains(&"M011".to_string()),
        "expected M011, got {:?}",
        codes_of(&err)
    );
}

#[test]
fn reject_tool_plus_actor_that_spawns() {
    // P7: the machinery rides along — a tool project whose actor `init` calls
    // spawn (one of the six forge-trapping ops). Dead relative to tool_main, so
    // trapping (slice 1) is invisible; the compile gate is the real signal.
    let src = "module tool;\npub fn tool_main(a: i64, b: i64) -> i64 { return 0; }\ncap type Fuel {}\nactor Boss {\n    init(fuel: Fuel) { let child = spawn::<Worker>(fuel); }\n    on Go() -> i64 { return 0; }\n}\nactor Worker {\n    init(fuel: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\n";
    let err = single(src).expect_err("tool + actor that spawns must be rejected");
    assert!(
        codes_of(&err).contains(&"M011".to_string()),
        "expected M011, got {:?}",
        codes_of(&err)
    );
}

#[test]
fn reject_single_file_tool_plus_entry_actor() {
    // The single-file hole M005 never sees: tool_main + a valid `entry actor
    // Main` in ONE file. M005/M006 are bypassed on the single-file path; M011
    // rejects it (X-G3: entry flag ignored).
    let src = "module tool;\npub fn tool_main(a: i64, b: i64) -> i64 { return 0; }\ncap type Fuel {}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { return 1; }\n}\n";
    let err = single(src).expect_err("tool + entry actor in one file must be rejected");
    assert!(
        codes_of(&err).contains(&"M011".to_string()),
        "expected M011, got {:?}",
        codes_of(&err)
    );
}

// ── ACCEPT: the gate keys strictly on tool_main presence ────────────────────

#[test]
fn accept_lone_nonentry_actor_no_tool() {
    // P6 boundary: a non-entry actor with NO tool_main is not a tool project.
    // It must stay accepted (a library / actor artifact), never M011.
    let src = "module main;\ncap type Fuel {}\nactor Worker {\n    init(fuel: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\n";
    assert!(
        single(src).is_ok(),
        "lone non-entry actor must compile: {:?}",
        single(src).err().as_ref().map(codes_of)
    );
}

#[test]
fn accept_tool_with_actor_in_a_comment() {
    // X-G2: detection is AST-based. A pure tool whose comment/string contains
    // the word "actor" must still compile — no source-text scanning.
    let src = "module tool;\n// this tool does not define an actor, honest\npub fn tool_main(a: i64, b: i64) -> i64 {\n    let actor_count = 0;\n    return actor_count;\n}\n";
    assert!(
        single(src).is_ok(),
        "a tool with 'actor' only in a comment/identifier must compile: {:?}",
        single(src).err().as_ref().map(codes_of)
    );
}

#[test]
fn accept_actor_project_entry_plus_worker() {
    // An actor project (entry actor + a non-entry helper it spawns) has no
    // tool_main, so the gate never touches it. Mirrors spawn_send_demo.sigil.
    let src = "module tool;\ncap type WorkerAuth {}\nactor Worker {\n    init(auth: WorkerAuth) {}\n    on Ping(payload: i64) -> i64 { return payload; }\n}\nentry actor Main {\n    state { auth: WorkerAuth }\n    on Start() -> i64 {\n        let _w = spawn::<Worker>(auth);\n        return 1;\n    }\n}\n";
    assert!(
        single(src).is_ok(),
        "actor project must compile: {:?}",
        single(src).err().as_ref().map(codes_of)
    );
}

#[test]
fn accept_converted_slot_aggregation_demo_file() {
    // Anti-drift (X-G6): the real tools/slot_aggregation_demo.sigil — converted
    // from a tool+dead-actor mix to an actor project — must `sigil check`
    // clean, exactly as the CI tools/ compile-sweep runs it. This asserts the
    // fixture was repaired, not skip-listed.
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tools/slot_aggregation_demo.sigil"
    );
    let src = std::fs::read_to_string(path).expect("read slot_aggregation_demo.sigil");
    assert!(
        single(&src).is_ok(),
        "converted demo must compile clean: {:?}",
        single(&src).err().as_ref().map(codes_of)
    );
}

// ── CONSERVATION (X-G4): M005/M006 still win in the multi-file entry case ────

#[test]
fn conservation_multi_file_intramodule_entry_actor_still_m005() {
    // tool_main + `entry actor Main` in the SAME module, across a genuine
    // multi-file project: M005 fires first (pre-convergence) and returns — M011
    // must NOT shadow it.
    let files = &[
        (
            "a.sigil",
            "module a;\npub fn tool_main(x: i64, y: i64) -> i64 { return 0; }\ncap type Fuel {}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { return 1; }\n}\n",
        ),
        (
            "b.sigil",
            "module b;\npub fn helper() -> i64 { return 7; }\n",
        ),
    ];
    let err = multi(files).expect_err("intra-module tool+entry-actor must be rejected");
    let cs = codes_of(&err);
    assert!(
        cs.contains(&"M005".to_string()),
        "expected M005, got {cs:?}"
    );
    assert!(
        !cs.contains(&"M011".to_string()),
        "M011 must not shadow M005, got {cs:?}"
    );
}

#[test]
fn conservation_multi_file_crossmodule_entry_actor_still_m006() {
    // tool_main in one module, `entry actor Main` in another: M006 fires first.
    let files = &[
        (
            "toolm.sigil",
            "module toolm;\npub fn tool_main(x: i64, y: i64) -> i64 { return 0; }\n",
        ),
        (
            "act.sigil",
            "module act;\ncap type Fuel {}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { return 1; }\n}\n",
        ),
    ];
    let err = multi(files).expect_err("cross-module tool+entry-actor must be rejected");
    let cs = codes_of(&err);
    assert!(
        cs.contains(&"M006".to_string()),
        "expected M006, got {cs:?}"
    );
    assert!(
        !cs.contains(&"M011".to_string()),
        "M011 must not shadow M006, got {cs:?}"
    );
}
