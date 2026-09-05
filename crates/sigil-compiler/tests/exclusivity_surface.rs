//! DEF-2c call-surface completeness contract.
//!
//! Every call that binds aliasable arguments must route through
//! `exclusivity_partition`. The closed surface has three owners in
//! the expression-inference subsystem:
//!
//!   1. `finish_resolved_call_expr` — free and cross-module calls.
//!   2. `infer_user_method_expr` — true methods, with `self` at parameter index zero.
//!   3. `infer_associated_fn_call` — no-`self` associated fn (generic-impl constructor).
//!
//! Closures carry no per-parameter mutability, and record construction is an escape sink
//! rather than an exclusivity sink. Structural and behavioral checks below pin the surface.

use std::fs;
use std::path::PathBuf;

use sigil_compiler::compile_named_module;

// ── the structural contract: the gate sits at EXACTLY the closed set ──────────────

fn expressions_source() -> String {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/type_check");
    let mut paths = vec![root.join("expressions.rs")];
    paths.extend(
        fs::read_dir(root.join("expressions"))
            .expect("read type_check/expressions directory")
            .map(|entry| entry.expect("read expression module entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "rs")),
    );
    paths.sort();

    paths
        .iter()
        .map(|path| fs::read_to_string(path).expect("read expression inference source"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Strip `//` line comments so a commented-out or merely-described call is not counted —
/// only LIVE `exclusivity_partition(` invocations are. (Same naive line-strip as
/// `quarantine_grep.rs`; the gate sites carry no `//` inside a string literal.)
fn strip_line_comments(src: &str) -> String {
    src.lines()
        .map(|line| match line.find("//") {
            Some(i) => &line[..i],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn exclusivity_gate_sites_are_exactly_the_closed_set() {
    let code = strip_line_comments(&expressions_source());
    let sites = code.matches("exclusivity_partition(").count();
    assert_eq!(
        sites, 3,
        "DEF-2c NC-2c-1 (the closed sink set): the call-site exclusivity gate must be invoked \
         at EXACTLY the closed call surface — `finish_resolved_call_expr` (free and cross-module), \
         `infer_user_method_expr` (true method + receiver), and `infer_associated_fn_call` \
         (associated fn). Found {sites} live `exclusivity_partition(` call sites in the \
         expression-inference subsystem (expected 3). If you added or removed a call-resolution path, \
         re-audit whether it can hand aliasable arguments to a frozen + mutable parameter pair, \
         gate it with `exclusivity_partition` if so, and update this count — do NOT just bump the \
         number."
    );
}

// ── behavioral: the qualified / cross-module resolution flavor fires the gate ──────

fn codes(name: &str, source: &str) -> Vec<String> {
    match compile_named_module(name, source) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn has(name: &str, source: &str, code: &str) -> bool {
    codes(name, source).iter().any(|c| c == code)
}

#[test]
fn qualified_self_module_call_is_gated_t255() {
    // A `module::fn(args)` qualified call routes through the cross-module dispatch machinery
    // (it "resolves as a same-module call") into the same `Found(sig)` arm the free call
    // uses — so the gate fires on an aliasing frozen + mutable pair. T255.
    let source = "\
module main;
record Box { v: i64 }
fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }
fn f() -> i64 ! { Alloc } { let p: Box = Box { v: 1 }; return main::sink(p, p); }
";
    assert!(
        has("qualified.sigil", source, "T255"),
        "got {:?}",
        codes("qualified.sigil", source)
    );
}

#[test]
fn qualified_self_module_call_distinct_is_clean() {
    // The control: distinct objects through the qualified call — no conflict.
    let source = "\
module main;
record Box { v: i64 }
fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }
fn f() -> i64 ! { Alloc } { let p: Box = Box { v: 1 }; let q: Box = Box { v: 2 }; return main::sink(p, q); }
";
    assert!(
        codes("qualified_ok.sigil", source).is_empty(),
        "got {:?}",
        codes("qualified_ok.sigil", source)
    );
}

#[test]
fn cross_module_call_is_gated_t255() {
    // The genuine cross-module flavor: `helpers::sink` resolves to a `pub fn` in another
    // module via `use sigil::helpers`, landing in `CrossModuleResolution::Found(sig)` — the
    // exact arm the gate guards. An aliasing pair across the module boundary still fires. T255.
    let source = "\
module helpers;
record Box { v: i64 }
pub fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }

module main;
use sigil::helpers;
fn f() -> i64 ! { Alloc } { let p: Box = Box { v: 1 }; return helpers::sink(p, p); }
";
    assert!(
        has("xmod.sigil", source, "T255"),
        "got {:?}",
        codes("xmod.sigil", source)
    );
}

#[test]
fn cross_module_call_distinct_is_clean() {
    // The cross-module control: distinct objects → clean across the boundary.
    let source = "\
module helpers;
record Box { v: i64 }
pub fn sink(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }

module main;
use sigil::helpers;
fn f() -> i64 ! { Alloc } { let p: Box = Box { v: 1 }; let q: Box = Box { v: 2 }; return helpers::sink(p, q); }
";
    assert!(
        codes("xmod_ok.sigil", source).is_empty(),
        "got {:?}",
        codes("xmod_ok.sigil", source)
    );
}
