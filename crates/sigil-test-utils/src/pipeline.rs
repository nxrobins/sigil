//! Pipeline helpers: drive a SIGIL source snippet through the
//! production compiler stages and surface the intermediate
//! representations for snapshot tests.
//!
//! The standard production entry point
//! ([`sigil_compiler::compile_module`]) returns a single
//! [`sigil_compiler::Compilation`] containing the AST and the AIR
//! (post-memory-lowering, post-fuel-insertion). For Pillar 2 we want
//! the **type-checker output** ([`sigil_compiler::type_check::TypedProgram`])
//! too, which production [`Compilation`] doesn't expose.
//!
//! [`typecheck_or_panic`] runs `parser::parse` → `name_resolution::resolve`
//! → `type_check::check_with_options` and hands back the TypedProgram.
//! [`compile_or_panic`] is a thin error-panicking wrapper over
//! [`sigil_compiler::compile_module`] for the AIR and WASM snapshots.
//!
//! Both helpers `panic!` with a formatted diagnostic on any pipeline
//! error so a failing snapshot test points at the macro invocation
//! site rather than at a buried `Result::unwrap()`.

use sigil_compiler::CompileOptions;
use sigil_compiler::air_capability_v2::obligations::AirCapabilityWorkload;
use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check::TypedProgram;
use sigil_compiler::type_check_v2::obligations::RefinementWorkload;
use sigil_compiler::{
    Compilation, CompileError, air, air_capability_v2, compile_module, compile_named_module,
    compile_tool, name_resolution, parser, type_check, type_check_v2,
};

/// Run a SIGIL source string through parse → name-resolution →
/// type-check and return the [`TypedProgram`]. Panics on any
/// diagnostic-error.
///
/// Use from snapshot tests that want to assert on the type-checker's
/// output before the rest of the compilation pipeline runs.
pub fn typecheck_or_panic(src: &str) -> TypedProgram {
    let source = SourceFile::new("<typecheck_or_panic snippet>", src);
    let (ast, parse_diags) = parser::parse(&source);
    panic_if_errors("parser::parse", &parse_diags, src);
    let resolved = name_resolution::resolve(&ast).unwrap_or_else(|diags| {
        panic_if_errors("name_resolution::resolve", &diags, src);
        unreachable!("panic_if_errors returns only on empty error list")
    });
    let (typed, _authority_registry) =
        type_check::check_with_options(&resolved, &CompileOptions::default()).unwrap_or_else(
            |diags| {
                panic_if_errors("type_check::check_with_options", &diags, src);
                unreachable!("panic_if_errors returns only on empty error list")
            },
        );
    typed
}

/// Run a SIGIL source string through the full production compile
/// pipeline and return the resulting [`Compilation`]. Panics on any
/// diagnostic-error.
///
/// Wrapper over [`sigil_compiler::compile_named_module`] that surfaces
/// errors as panics suitable for snapshot tests.
pub fn compile_or_panic(src: &str) -> Compilation {
    compile_named_module("<compile_or_panic snippet>", src).unwrap_or_else(|err| {
        panic_with_compile_error(&err, src);
    })
}

/// Return diagnostic codes in compiler emission order, preserving duplicates.
pub fn compile_error_codes(error: &CompileError) -> Vec<String> {
    error
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str().to_owned())
        .collect()
}

/// Compile a tool and return its diagnostic codes, or an empty vector on success.
pub fn compile_tool_codes(src: &str) -> Vec<String> {
    compile_tool(src)
        .err()
        .map(|error| compile_error_codes(&error))
        .unwrap_or_default()
}

/// Compile a module and return its diagnostic codes, or an empty vector on success.
pub fn compile_module_codes(src: &str) -> Vec<String> {
    compile_module(src)
        .err()
        .map(|error| compile_error_codes(&error))
        .unwrap_or_default()
}

/// Pillar 3 entry point: run a SIGIL source string through parse →
/// name-resolution → type-check → v2 workload collection.
///
/// Returns one of three shapes:
///
///   * `Ok(WorkloadResult { ... })` — type-check succeeded; both
///     workloads are populated (potentially empty) and any collector-
///     emitted diagnostics ride alongside.
///   * `Err(WorkloadFailure::Parse(diags))` — parser rejected the
///     source. The workload collector requires a TypedProgram, which
///     requires a successful parse.
///   * `Err(WorkloadFailure::TypeCheck(diags))` — parser succeeded
///     but name-resolution or type-check rejected the source. Common
///     for the UNSAFE variants of cve_corpus fixtures, which are
///     SUPPOSED to be rejected.
///
/// The Result-of-enum shape lets the snapshot harness produce a
/// readable placeholder (`<TYPE_CHECK_FAILED: [T155, T199]>`) for
/// fixtures the type-checker rejects, instead of skipping them
/// entirely. Skipping would hide a regression where type-check
/// stopped rejecting a known-bad pattern; the placeholder snapshot
/// catches that.
pub fn collect_workloads_or_skip(src: &str) -> Result<WorkloadResult, WorkloadFailure> {
    let source = SourceFile::new("<workload snippet>", src);
    let (ast, parse_diags) = parser::parse(&source);
    let parse_errors: Vec<Diagnostic> = parse_diags
        .into_iter()
        .filter(|d| d.severity() == Severity::Error)
        .collect();
    if !parse_errors.is_empty() {
        return Err(WorkloadFailure::Parse(parse_errors));
    }

    let resolved = match name_resolution::resolve(&ast) {
        Ok(r) => r,
        Err(diags) => return Err(WorkloadFailure::TypeCheck(diags)),
    };

    let (typed, authority_registry) =
        match type_check::check_with_options(&resolved, &CompileOptions::default()) {
            Ok(pair) => pair,
            Err(diags) => return Err(WorkloadFailure::TypeCheck(diags)),
        };

    // Refinement workload: from the type_check_v2 Pure collector (works
    // off the TypedProgram).
    let (refine_diags, refine_workload) =
        type_check_v2::collect_workloads_for_test(&resolved, &typed);

    // AIR-capability workload: from the air_capability_v2 Pure collector,
    // which needs a lowered AirProgram. Lowering is infallible
    // (air::lower returns AirProgram directly), so any fixture that
    // type-checks reaches the collector.
    let air = air::lower(&typed);
    let (cap_diags, cap_workload) =
        air_capability_v2::collect_air_capability_workload_for_test(&air, &authority_registry);

    Ok(WorkloadResult {
        refine_diags,
        refine_workload,
        cap_diags,
        cap_workload,
    })
}

/// Result of [`collect_workloads_or_skip`] on a fixture that
/// successfully type-checks. Carries both raw workloads plus their
/// collector-stage diagnostics.
///
/// `refine_*` come from the `type_check_v2` Pure collector (over the
/// TypedProgram); `cap_*` come from the `air_capability_v2` Pure
/// collector (over the lowered AirProgram). `refine_diags` can be
/// non-empty on success (e.g. T211 for unrefined-symbolic returns);
/// `cap_diags` is currently always empty (the AIR-cap collector emits
/// no standalone diagnostics — every obligation carries its own
/// `on_violated`).
#[derive(Debug)]
pub struct WorkloadResult {
    pub refine_diags: Vec<Diagnostic>,
    pub refine_workload: RefinementWorkload,
    pub cap_diags: Vec<Diagnostic>,
    pub cap_workload: AirCapabilityWorkload,
}

/// Reason a fixture's workloads couldn't be collected.
#[derive(Debug)]
pub enum WorkloadFailure {
    /// Parser rejected the source. Carries the parse-stage errors.
    Parse(Vec<Diagnostic>),
    /// Parser succeeded but name-resolution or type-check rejected.
    /// Carries the type-check-stage errors (the union of name-res
    /// and type-check, treated identically).
    TypeCheck(Vec<Diagnostic>),
}

impl WorkloadFailure {
    /// Produce a stable, snapshotable summary like
    /// `<TYPE_CHECK_FAILED: [T155, T199]>`. Sorted, deduplicated codes
    /// for cross-run stability.
    pub fn summary(&self) -> String {
        let (label, diags) = match self {
            WorkloadFailure::Parse(d) => ("PARSE_FAILED", d),
            WorkloadFailure::TypeCheck(d) => ("TYPE_CHECK_FAILED", d),
        };
        let mut codes: Vec<&'static str> = diags
            .iter()
            .filter(|d| d.severity() == Severity::Error)
            .map(|d| d.code().as_str())
            .collect();
        codes.sort_unstable();
        codes.dedup();
        format!("<{label}: {codes:?}>")
    }
}

// ── Internal helpers ──────────────────────────────────────────────────────

fn panic_if_errors(stage: &str, diagnostics: &[Diagnostic], src: &str) {
    let errors: Vec<&Diagnostic> = diagnostics
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .collect();
    if !errors.is_empty() {
        let formatted: Vec<String> = errors
            .iter()
            .map(|d| format!("  - {}: {}", d.code().as_str(), d.message()))
            .collect();
        panic!(
            "pipeline::{stage}: snippet produced {n} error(s):\n{joined}\n\n\
             Original snippet:\n{src}",
            n = errors.len(),
            joined = formatted.join("\n"),
        );
    }
}

fn panic_with_compile_error(err: &CompileError, src: &str) -> ! {
    let formatted: Vec<String> = err
        .diagnostics()
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| format!("  - {}: {}", d.code().as_str(), d.message()))
        .collect();
    panic!(
        "pipeline::compile_or_panic: full-pipeline compile failed with \
         {n} error(s):\n{joined}\n\nOriginal snippet:\n{src}",
        n = formatted.len(),
        joined = formatted.join("\n"),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    const MINIMAL: &str = "module demo;\npub fn answer() -> i64 {\n    return 42;\n}\n";
    const MINIMAL_TOOL: &str = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n    return 0;\n}\n";

    #[test]
    fn typecheck_or_panic_returns_typed_program() {
        let typed = typecheck_or_panic(MINIMAL);
        assert_eq!(typed.modules.len(), 1, "expected one module");
        assert_eq!(typed.modules[0].name, "demo");
    }

    #[test]
    fn compile_or_panic_returns_full_compilation() {
        let comp = compile_or_panic(MINIMAL);
        assert!(!comp.wasm_inner.is_empty(), "expected non-empty WASM");
        assert_eq!(comp.module_names, vec!["demo".to_string()]);
        assert!(
            !comp.air.functions.is_empty(),
            "expected at least one AIR function"
        );
    }

    #[test]
    #[should_panic(expected = "compile_or_panic: full-pipeline compile failed")]
    fn compile_or_panic_panics_on_type_error() {
        // `1 + true` — int + bool, type mismatch.
        compile_or_panic("module bad;\npub fn f() -> i64 {\n    return 1 + true;\n}\n");
    }

    #[test]
    #[should_panic(expected = "pipeline::parser::parse")]
    fn typecheck_or_panic_panics_on_parse_error() {
        typecheck_or_panic("module @@@ broken !!!");
    }

    #[test]
    fn compile_code_helpers_distinguish_valid_and_invalid_sources() {
        assert!(compile_tool_codes(MINIMAL_TOOL).is_empty());
        assert!(!compile_tool_codes("module broken;").is_empty());
        assert!(compile_module_codes(MINIMAL).is_empty());
        assert!(
            !compile_module_codes("module broken; pub fn wrong() -> i64 { return true; }")
                .is_empty()
        );
    }

    proptest! {
        #[test]
        fn compile_tool_codes_match_direct_compiler_mapping(source in ".{0,120}") {
            let expected = sigil_compiler::compile_tool(&source)
                .err()
                .map(|error| {
                    error
                        .diagnostics()
                        .iter()
                        .map(|diagnostic| diagnostic.code().as_str().to_owned())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            prop_assert_eq!(compile_tool_codes(&source), expected);
        }
    }
}
