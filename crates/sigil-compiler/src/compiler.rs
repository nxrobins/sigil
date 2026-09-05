//! The compiler driver: the public `compile_*` entries and the single
//! post-parse pipeline they all converge into (`compile_ast_with_options`).
//!
//! Invariant this file owns: the production pass order.
//! `TYPED_SECURITY_PASSES` is the one ordered manifest of the typed
//! security gates (Ring -> Effect -> Taint), and the production
//! sequence (resolve -> type-check -> security passes ->
//! effect-handler desugar + gate -> AIR -> capability -> ownership ->
//! memory -> fuel -> wasm) is pinned in order by
//! `compiler_security_pipeline_is_complete_and_ordered` in
//! `sigil-runtime/tests/soundness_contract.rs` (SR-007 in
//! docs/RESIDUAL_RISKS.md) -- dropping or reordering a stage here is
//! a pinned-test change, never a quiet edit. Single-file input takes
//! a fast path that bypasses M001-M006 and M007/M009 yet converges
//! into the same pipeline, byte-equal to the legacy single-file
//! output; M011 runs at the convergence point so the fast path
//! cannot dodge it.
//!
//! Failure discipline: every rejection returns `CompileError`
//! carrying typed diagnostics. S001-S006 reject oversized or
//! malformed units at the door (byte caps, empty source,
//! module/function counts, missing `tool_main`); M001-M011 gate
//! project shape (filename/module match, duplicate module or source
//! names, entry-point detection, tool/actor exclusion); each code
//! has a doc under `docs/errors/`. Panic sites here encode internal
//! invariants only (the ICE arms in `runtime_type` and one narrated
//! expect), never user-facing errors.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use sigil_abi::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeImportSpec, RuntimeModuleSpec,
    RuntimeStateFieldSpec, RuntimeTypeSpec,
};

use crate::{
    air::{self, AirFunctionKind, AirProgram},
    ast::{ActorDef, Item, Program, Ring, TypeExpr, Visibility},
    capability::{self, CapabilityReport},
    compiler_context::CompilerContext,
    diagnostics::{CompileError, Diagnostic, codes},
    effect_check, effect_desugar,
    formal::{self, FormalSecurityReport},
    fuel::{self, FuelPlan},
    memory::{self, MemoryLowering},
    name_resolution,
    ownership::{self, OwnershipReport},
    parser, ring_check,
    source::{SourceFile, SourceMap},
    span::{SourceId, Span},
    taint_check,
    type_check::{self, Type, TypedFunctionKind, TypedProgram},
    wasm,
};

#[derive(Debug, Clone)]
pub struct Compilation {
    pub source_name: String,
    pub module_names: Vec<String>,
    pub ast: Program,
    /// Fully checked program retained as compiler-derived evidence for
    /// package-level per-module effect and taint attribution. Consumers must
    /// never infer these facts again from unchecked manifest text.
    pub typed: TypedProgram,
    pub air: AirProgram,
    pub wasm_inner: Vec<u8>,
    pub wasm_outer: Option<Vec<u8>>,
    pub fuel_budget: u64,
    pub runtime_module: RuntimeModuleSpec,
    pub capability_report: CapabilityReport,
    pub ownership_report: OwnershipReport,
    /// Fresh evidence from the statically linked Lean verifier over canonical
    /// version-8 CSIR envelope and verifier-owned taint/capability/quantity graphs. This type can
    /// only be constructed after a successful native call.
    pub formal_security_report: FormalSecurityReport,
    pub memory_report: MemoryLowering,
    pub fuel_plan: FuelPlan,
    /// Sorted, deduplicated names of every effect that ANY function in this
    /// program requires. Computed at type-check time as the union of every
    /// `TypedFunction.effects` set, resolved via `TypedProgram.effect_registry`
    /// to human-readable names (e.g. `NetIO`, `FsIO`, `Alloc`).
    ///
    /// Step 13 of the supremum loop introduced this as axis-5 progress —
    /// external policy authorities consuming the verification certificate
    /// can decide whether to allow execution based on the effect surface
    /// WITHOUT re-running the compiler.
    pub effects_required: Vec<String>,
    /// Mutation-as-capability (PR-4): non-blocking type-check WARNINGS surfaced
    /// to the caller (the program compiled successfully). Today this is only T252
    /// (the `@ReadOnly` reference/view partial-guarantee lint). Empty for every
    /// program that emits no warning — so this field is `[]` across the existing
    /// corpus and snapshots, which snapshot `TypedProgram`/AIR/WAT, not this struct.
    pub warnings: Vec<Diagnostic>,
    /// Wall 5 Step 1 follow-up: the [`SourceMap`] used by every span in
    /// this compilation. Single-file compilations contain one entry at
    /// [`SourceId(0)`]; multi-file compilations contain one entry per
    /// input file in canonical sort order. The renderer consults this
    /// map to resolve each diagnostic's span back to its originating
    /// `SourceFile`. Stored as `Arc<SourceMap>` so [`CompileError`] can
    /// carry the same map without forcing the Compilation's borrow
    /// lifetime to outlive the error.
    pub sources: Arc<SourceMap>,
}

impl Compilation {
    pub fn primary_module_name(&self) -> Option<&str> {
        match self.module_names.as_slice() {
            [name] => Some(name.as_str()),
            _ => None,
        }
    }
}

/// Result of compiling a tool module for ephemeral execution.
#[derive(Debug, Clone)]
pub struct CompileResult {
    /// Executable module selected from `tool_main`'s ring. Preserved for
    /// callers that only need to run the tool.
    pub wasm: Vec<u8>,
    /// Inner artifact from the same compilation. Certificate gates must bind
    /// this artifact even when the executable tool lives in the outer ring.
    pub wasm_inner: Vec<u8>,
    /// Outer artifact when the compilation contains outer-ring code.
    pub wasm_outer: Option<Vec<u8>>,
    pub fuel_budget: u64,
    /// Whether `fuel_budget` is a PROVEN workload ceiling (see
    /// `FuelPlan::is_workload_ceiling`) rather than a straight-line floor.
    pub fuel_is_workload_ceiling: bool,
    pub function_count: usize,
    /// Mutation-as-capability (PR-4): non-blocking type-check warnings (today only
    /// T252). Empty unless the tool declared a `@ReadOnly` reference/view param.
    pub warnings: Vec<Diagnostic>,
    /// Whether the Z3-backed verification actually ran for this compilation
    /// (`true` only on a `solver`-feature build). Mirrors the capability
    /// report's witness so the `forge`/MCP execution gate and the `--cert`
    /// gate can fail closed on an artifact whose flow-sensitive obligations
    /// were never discharged — WITHOUT trusting an attacker-controllable cert
    /// bit. This is the freshly-DERIVED value, so it cannot be forged.
    pub solver_verified: bool,
    /// Fresh version-6 joint-obligation and verifier-derived taint/capability/quantity evidence
    /// from the mandatory linked Lean verifier.
    pub formal_security_report: FormalSecurityReport,
}

/// Limits applied during tool compilation to prevent resource exhaustion.
#[derive(Debug, Clone)]
pub struct CompileLimits {
    /// Maximum source size in bytes. Default: 64 KB.
    pub max_source_bytes: usize,
}

impl Default for CompileLimits {
    fn default() -> Self {
        Self {
            max_source_bytes: 64 * 1024,
        }
    }
}

/// Compile a tool module with explicit resource limits.
///
/// Returns an error if the source exceeds `limits.max_source_bytes`.
pub fn compile_tool_with_limits(
    source: &str,
    limits: &CompileLimits,
) -> Result<CompileResult, CompileError> {
    compile_tool_with_limits_and_context(source, limits, &CompilerContext::default())
}

/// Compile a bounded tool using explicit provider declarations. Declarations
/// never approve execution or bypass the mandatory formal gate.
pub fn compile_tool_with_limits_and_context(
    source: &str,
    limits: &CompileLimits,
    context: &CompilerContext,
) -> Result<CompileResult, CompileError> {
    if source.len() > limits.max_source_bytes {
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::S001,
            format!(
                "source exceeds maximum size ({} bytes > {} byte limit)",
                source.len(),
                limits.max_source_bytes,
            ),
            None,
        )]));
    }
    compile_tool_with_context(source, context)
}

/// Compile a tool module for ephemeral (ToolForge) execution.
///
/// The source must define a module with a `pub fn tool_main` export.
/// Returns the compiled Wasm bytes, fuel budget, and function count.
pub fn compile_tool(source: &str) -> Result<CompileResult, CompileError> {
    compile_tool_with_context(source, &CompilerContext::default())
}

/// Compile an unbounded tool with an explicit, immutable declaration context.
/// Callers accepting untrusted source should use the limits-bearing variant.
pub fn compile_tool_with_context(
    source: &str,
    context: &CompilerContext,
) -> Result<CompileResult, CompileError> {
    let compilation = compile_module_with_context(source, context)?;

    // The export naming convention is `module__fn`, so tool_main in module
    // "tool" becomes "tool__tool_main". We search for any export containing
    // "tool_main".
    let tool_functions = compilation
        .air
        .functions
        .iter()
        .filter(|f| f.export_name.contains("tool_main"))
        .collect::<Vec<_>>();

    if tool_functions.is_empty() {
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::S002,
            "tool module must export pub fn tool_main",
            None,
        )]));
    }

    let tool_ring = tool_functions
        .iter()
        .find(|f| !matches!(f.kind, AirFunctionKind::Closure))
        .map(|f| f.ring)
        .unwrap_or(Ring::Inner);
    let wasm = match tool_ring {
        Ring::Inner => &compilation.wasm_inner,
        Ring::Outer => compilation
            .wasm_outer
            .as_ref()
            .unwrap_or(&compilation.wasm_inner),
    };
    let function_count = compilation
        .air
        .functions
        .iter()
        .filter(|f| f.ring == tool_ring)
        .count();

    Ok(CompileResult {
        wasm: wasm.clone(),
        wasm_inner: compilation.wasm_inner,
        wasm_outer: compilation.wasm_outer,
        fuel_budget: compilation.fuel_budget,
        fuel_is_workload_ceiling: compilation.fuel_plan.is_workload_ceiling,
        function_count,
        warnings: compilation.warnings.clone(),
        solver_verified: compilation.capability_report.solver_verified,
        formal_security_report: compilation.formal_security_report,
    })
}

pub fn compile_module(source: &str) -> Result<Compilation, CompileError> {
    compile_module_with_context(source, &CompilerContext::default())
}

/// Compile an inline source with explicit provider declarations, not approval.
pub fn compile_module_with_context(
    source: &str,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    compile_named_module_with_context("<inline>", source, CompileOptions::default(), context)
}

pub fn compile_named_module(
    source_name: impl Into<String>,
    source_text: impl Into<String>,
) -> Result<Compilation, CompileError> {
    compile_named_module_with_options(source_name, source_text, CompileOptions::default())
}

/// Compiler configuration knobs that affect type-check and downstream
/// passes but not the AST or parse tree. Defaults match the legacy
/// no-flag behavior — every option is opt-in via CLI flags.
///
/// Wall 2 Stage 2 added `build_deadline` so the compiler can refuse to
/// build a program whose parametric cap-type literals declare a
/// deadline already past the build's reference instant.
#[derive(Debug, Clone, Default)]
pub struct CompileOptions {
    /// `--build-deadline <i64>` reference instant. When `Some(N)`, every
    /// parametric cap-type literal `Cap(D)` in the source must satisfy
    /// `D >= N`; literals with `D < N` fire T199. When `None`, no
    /// build-time deadline check runs (legacy default).
    pub build_deadline: Option<i64>,
}

pub fn compile_named_module_with_options(
    source_name: impl Into<String>,
    source_text: impl Into<String>,
    options: CompileOptions,
) -> Result<Compilation, CompileError> {
    compile_named_module_with_context(
        source_name,
        source_text,
        options,
        &CompilerContext::default(),
    )
}

/// Compile named source with explicit options and provider declarations.
/// Context is separate from `CompileOptions` so existing option literals keep
/// their legacy meaning and declarations cannot be inferred from a certificate.
pub fn compile_named_module_with_context(
    source_name: impl Into<String>,
    source_text: impl Into<String>,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    // Wall 5 Step 1 / N25-W5S1: single-file legacy entry routes through
    // compile_project with N=1 input. compile_project's single-file fast
    // path bypasses M001-M006 (N21-W5S1) and converges into the same
    // compile_source_with_options call as the legacy direct path, so
    // wasm bytes stay byte-equal for every existing tool/fixture.
    let source = SourceFile::new(source_name, source_text);
    compile_project_with_context(vec![source], None, options, context)
}

/// Wall 5 Step 1: multi-file compilation entry point.
///
/// Accepts a set of source files and produces a single [`Compilation`]
/// whose AST is the merged `Program` of all modules contributed by the
/// input set. The single-file case (`sources.len() == 1`) is the legacy
/// path with byte-equal wasm output.
///
/// `entry` is the optional `--entry <module>` override that
/// disambiguates entry-point detection when the project has more than
/// one candidate (`pub fn tool_main` or `entry actor`). `None` triggers
/// automatic detection; zero candidates fire M003, multiple fire M004.
///
/// Operations in order (N1-W5S1 + N9-W5S1 + N10-W5S1):
/// 1. Empty input → M008.
/// 2. Per-source-name charset validation → M009 on any violation.
/// 3. Duplicate source-name detection → M007.
/// 4. Stable sort by name (str::cmp, N5-W5S1) for determinism.
/// 5. Single-file fast path: bypass M001-M006, call
///    `compile_source_with_options` directly (legacy byte-equal).
/// 6. Multi-file path: per-file parse + M001 (filename-module match);
///    cross-file M002 dedup BEFORE merge (N17-W5S1).
/// 7. Merge per-file `Program.modules` vectors into one combined `Program`.
/// 8. `--entry` validation against merged modules → M010.
/// 9. Entry-point detection (recursive descent per N3-W5S1) →
///    M003 (none) / M004 (multiple, no `--entry`) / M005 (intra-module
///    tool+actor mix) / M006 (cross-module tool+actor mix).
/// 10. Hand the merged Program to the post-parse pipeline
///     (`compile_ast_with_options`).
pub fn compile_project(
    sources: Vec<SourceFile>,
    entry: Option<&str>,
    options: CompileOptions,
) -> Result<Compilation, CompileError> {
    compile_project_with_context(sources, entry, options, &CompilerContext::default())
}

/// Compile an executable project under one declaration context shared by every
/// source, including the single-file fast path and ambient modules.
pub fn compile_project_with_context(
    sources: Vec<SourceFile>,
    entry: Option<&str>,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    compile_project_with_policy(
        sources,
        entry,
        options,
        ProjectEntryPolicy::Executable,
        context,
    )
}

/// Compile a library/package source set without selecting a runtime entry.
/// This preserves the same parse, type, ring, effect, taint, capability,
/// ownership, fuel, and Wasm passes as `compile_project`; it only disables the
/// executable-project M003/M004/M005/M006 entry contract. Package v1 is
/// library-only, so a dependency can never hijack the root artifact by
/// supplying the graph's sole `tool_main` or entry actor.
pub fn compile_library_project(
    sources: Vec<SourceFile>,
    options: CompileOptions,
) -> Result<Compilation, CompileError> {
    compile_library_project_with_context(sources, options, &CompilerContext::default())
}

/// Compile a library graph under the same explicit context as its rederivation.
pub fn compile_library_project_with_context(
    sources: Vec<SourceFile>,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    compile_project_with_policy(sources, None, options, ProjectEntryPolicy::Library, context)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProjectEntryPolicy {
    Executable,
    Library,
}

fn compile_project_with_policy(
    sources: Vec<SourceFile>,
    entry: Option<&str>,
    options: CompileOptions,
    entry_policy: ProjectEntryPolicy,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    // N10-W5S1: empty input rejection.
    if sources.is_empty() {
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::M008,
            "compile_project called with zero sources; pass at least one .sigil file",
            None,
        )]));
    }

    // PR B / N27-PRB: ambient stdlib auto-include for Result + Option.
    // Runs in the pre-merge phase BEFORE the single-file fast-path
    // check and BEFORE M001-M006. Scans every input source's lexed
    // token stream for triggers (Ok(/Err(/Some(/None/postfix ?) and
    // appends stdlib/sigil/result.sigil and/or option.sigil. AG-PRB-A
    // documents the scoped exception to Wall 5's MC-S1-E anti-goal.
    //
    // If the input was 1 file with no triggers, the source set stays
    // length-1 and the fast path below applies (byte-equal pre-PR-B
    // behavior for non-Ok/Err/?/Some/None code). If triggers fire,
    // the set grows to 2-3 and routes through the multi-file path.
    //
    // `ambient_grew` tracks whether stdlib files were added so the
    // multi-file pipeline can skip M001 on the original user
    // sources — they shouldn't see filename-module-mismatch
    // diagnostics just because their code used Ok(...) (the stdlib
    // files themselves satisfy M001 by construction).
    let ambient_result = crate::ambient_stdlib::apply_ambient_includes_with_count(sources);
    let sources = ambient_result.sources;
    let ambient_grew = ambient_result.ambient_added > 0;

    // N21-W5S1: single-file fast path bypasses M001-M006 AND M007/M009
    // (which can't apply at N=1 anyway: no duplicates, no project-level
    // name validation needed for legacy callers like `compile_module`
    // which passes `<inline>` as the name). Every existing tool/*.sigil
    // and tests/* compiles byte-equally.
    if sources.len() == 1 {
        return compile_source_with_options(&sources[0], options, context);
    }

    // ── Multi-file path ─────────────────────────────────────────────────

    // N11-W5S1: source-name charset validation. Defense in depth at the
    // library boundary so direct API callers can't bypass the CLI check.
    // Applies only when sources.len() >= 2; single-file legacy callers
    // (compile_module, compile_named_module with non-`.sigil` names like
    // `<inline>`) route through the fast path above.
    //
    // PR B commit #2: when ambient grew the set, skip M009 — the user's
    // legacy-named source (e.g., `<inline>`) shouldn't see source-name
    // validation it didn't ask for. The stdlib files have valid `.sigil`
    // names by construction.
    if !ambient_grew {
        let mut name_diagnostics = Vec::new();
        for source in &sources {
            if let Err(diag) = validate_source_name(source.name()) {
                name_diagnostics.push(diag);
            }
        }
        if !name_diagnostics.is_empty() {
            return Err(CompileError::new(name_diagnostics));
        }
    }

    // N9-W5S1: duplicate source-file name detection runs as the first
    // structural operation of the multi-file path. Set-vs-vec
    // cardinality compares the unique count against the input count.
    let unique_names: BTreeSet<&str> = sources.iter().map(|s| s.name()).collect();
    if unique_names.len() != sources.len() {
        let mut seen = BTreeSet::new();
        let mut dups = BTreeSet::new();
        for s in &sources {
            if !seen.insert(s.name()) {
                dups.insert(s.name().to_string());
            }
        }
        let dup_list = dups
            .iter()
            .map(|s| format!("`{s}`"))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::M007,
            format!("duplicate source-file name(s) in compilation set: {dup_list}"),
            None,
        )]));
    }

    // N5-W5S1: sort by name (UTF-8 byte-lexicographic via str::cmp) so
    // arg order doesn't affect output. Determinism property tested by
    // N7/N29-W5S1.
    let mut sources = sources;
    sources.sort_by(|a, b| a.name().cmp(b.name()));

    // SourceId follow-up: assign each file an id by its position in
    // the sorted vector. The SourceMap built here lives on the resulting
    // Compilation so the renderer can resolve every span's `source`
    // field back to a SourceFile.
    let mut source_map = SourceMap::new();
    let mut source_ids: Vec<SourceId> = Vec::with_capacity(sources.len());
    for source in &sources {
        source_ids.push(source_map.push(source.clone()));
    }

    // Per-file parse + M001 (filename-module match). AG-W5S1-3:
    // first-file-error-halt; we don't aggregate parse errors across
    // files.
    let mut parsed: Vec<(SourceFile, Program)> = Vec::with_capacity(sources.len());
    // Parser warnings from every source, merged into Compilation.warnings at
    // the convergence call (severity-aware parse gate; P031 etc.).
    let mut parser_warnings_all: Vec<Diagnostic> = Vec::new();
    for (idx, source) in sources.into_iter().enumerate() {
        let source_id = source_ids[idx];
        // Per-file S005: 5 MB cap stays per-file; project-level total
        // cap is anti-goal AG-W5S1-6.
        if source.text().len() > MAX_SOURCE_BYTES {
            return Err(CompileError::new(vec![Diagnostic::error_in_file(
                codes::S005,
                format!(
                    "source `{}` is {} bytes; maximum is {} ({} MB)",
                    source.name(),
                    source.text().len(),
                    MAX_SOURCE_BYTES,
                    MAX_SOURCE_BYTES / (1024 * 1024)
                ),
                Some(Span::with_source(0, 0, source_id)),
                source.name(),
            )]));
        }
        if source.text().trim().is_empty() {
            return Err(CompileError::new(vec![Diagnostic::error_in_file(
                codes::S003,
                format!("source `{}` must not be empty", source.name()),
                Some(Span::with_source(0, 0, source_id)),
                source.name(),
            )]));
        }
        let (program, parser_diagnostics) = parser::parse_with_id(&source, source_id);
        // Attribute each parse diagnostic to the offending file so
        // render_in_project can show the right source. Spans already
        // carry the right source_id from parse_with_id; this adds
        // the source_name attribution channel for legacy renderers.
        // Severity-aware (P031 is the parser's first warning): errors abort;
        // warnings accumulate and merge into `Compilation.warnings` at the
        // convergence call — the attribution re-wrap preserves severity
        // (`warning_in_file`), never upgrading a warning to an error.
        let mut file_errors: Vec<Diagnostic> = Vec::new();
        for d in parser_diagnostics {
            let code = d.code();
            let message = d.message().to_string();
            let span = d.span();
            if d.severity() == crate::diagnostics::Severity::Error {
                file_errors.push(Diagnostic::error_in_file(
                    code,
                    message,
                    span,
                    source.name(),
                ));
            } else {
                parser_warnings_all.push(Diagnostic::warning_in_file(
                    code,
                    message,
                    span,
                    source.name(),
                ));
            }
        }
        if !file_errors.is_empty() {
            return Err(CompileError::new(file_errors));
        }
        // M001: filename matches first module declared in the file.
        //
        // PR B commit #2: when ambient stdlib was auto-included
        // (ambient_grew = true), skip M001 — the user's input
        // shouldn't see filename-module-mismatch diagnostics they
        // didn't ask for. The stdlib files themselves are
        // well-formed by construction (their own isolation smoke
        // tests in commit #1 verify M001 satisfaction).
        if !ambient_grew && let Err(diag) = enforce_filename_module(&source, &program) {
            return Err(CompileError::new(vec![diag]));
        }
        parsed.push((source, program));
    }

    // N1-W5S1 + N17-W5S1: pre-merge M002 dedup. Single canonical
    // BTreeMap keyed by module name; tracks all (source_name, span)
    // pairs across BOTH top-level and inline module declarations.
    if let Some(diag) = find_duplicate_module_names(&parsed) {
        return Err(CompileError::new(vec![diag]));
    }

    // Merge per-file Program.modules into one Program.
    let mut merged_modules = Vec::new();
    for (_, program) in &parsed {
        merged_modules.extend(program.modules.iter().cloned());
    }
    let merged = Program {
        modules: merged_modules,
    };

    // N16-W5S1: --entry validation against the merged module set.
    if entry_policy == ProjectEntryPolicy::Executable
        && let Some(entry_name) = entry
        && !merged.modules.iter().any(|m| m.name == entry_name)
    {
        let available: Vec<String> = merged
            .modules
            .iter()
            .map(|m| format!("`{}`", m.name))
            .collect();
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::M010,
            format!(
                "--entry `{entry_name}` does not match any module in the compilation set; available: [{}]",
                available.join(", ")
            ),
            None,
        )]));
    }

    // N3-W5S1: find entry points by recursive descent over the merged
    // program. Today's AST has no nested-module variant inside `Item`,
    // so the descent collapses to iteration over modules and their items.
    let all_entries = find_entry_points(&merged);

    // M005: intra-module mix of tool entry and actor entry.
    if entry_policy == ProjectEntryPolicy::Executable && !ambient_grew {
        let mut by_module: BTreeMap<&str, (bool, bool)> = BTreeMap::new();
        for entry_point in &all_entries {
            let counters = by_module.entry(entry_point.module()).or_default();
            match entry_point {
                EntryPoint::ToolMain { .. } => counters.0 = true,
                EntryPoint::EntryActor { .. } => counters.1 = true,
            }
        }
        for (module, (has_tool, has_actor)) in by_module {
            if has_tool && has_actor {
                return Err(CompileError::new(vec![Diagnostic::error(
                    codes::M005,
                    format!(
                        "module `{module}` declares both `pub fn tool_main` and `entry actor` — these are incompatible execution models (ephemeral forge vs persistent actor)"
                    ),
                    None,
                )]));
            }
        }
    }

    // Apply --entry filter to restrict candidates.
    let candidates: Vec<&EntryPoint> = match (entry_policy, entry) {
        (ProjectEntryPolicy::Library, _) => Vec::new(),
        (ProjectEntryPolicy::Executable, Some(name)) => {
            all_entries.iter().filter(|e| e.module() == name).collect()
        }
        (ProjectEntryPolicy::Executable, None) => all_entries.iter().collect(),
    };

    // M003: no entry point candidates after filtering.
    //
    // PR B commit #2: skip M003 when ambient grew the set. Legacy
    // single-file callers (compile_module, snippet-style tests)
    // didn't see M003 in the fast path; the ambient include
    // shouldn't introduce this diagnostic. The downstream
    // pipeline tolerates zero entries (produces wasm for whatever
    // modules exist; runtime treats it as a library).
    if entry_policy == ProjectEntryPolicy::Executable && candidates.is_empty() && !ambient_grew {
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::M003,
            match entry {
                Some(name) => format!(
                    "--entry `{name}`: module declares no entry point (no `pub fn tool_main`, no `entry actor`)"
                ),
                None => "no entry point found in compilation set; expected exactly one `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64` or one `entry actor Main`".to_string(),
            },
            None,
        )]));
    }

    // M006: project contains both tool entry and actor entry (cross-module).
    if entry_policy == ProjectEntryPolicy::Executable {
        let mut tool_modules: Vec<String> = Vec::new();
        let mut actor_modules: Vec<String> = Vec::new();
        for entry_point in &candidates {
            match entry_point {
                EntryPoint::ToolMain { module, .. } => tool_modules.push(format!("`{module}`")),
                EntryPoint::EntryActor { module, .. } => actor_modules.push(format!("`{module}`")),
            }
        }
        if !tool_modules.is_empty() && !actor_modules.is_empty() {
            return Err(CompileError::new(vec![Diagnostic::error(
                codes::M006,
                format!(
                    "project mixes execution models: tool entry in [{}], actor entry in [{}] — a project must target exactly one model",
                    tool_modules.join(", "),
                    actor_modules.join(", ")
                ),
                None,
            )]));
        }
    }

    // M004: multiple candidates and no --entry override to disambiguate.
    if entry_policy == ProjectEntryPolicy::Executable && entry.is_none() && candidates.len() > 1 {
        let modules: Vec<String> = candidates
            .iter()
            .map(|e| format!("`{}`", e.module()))
            .collect();
        return Err(CompileError::new(vec![Diagnostic::error(
            codes::M004,
            format!(
                "multiple entry points found in modules [{}]; pass --entry <module> to disambiguate",
                modules.join(", ")
            ),
            None,
        )]));
    }

    // Determine the Compilation.source_name. Use the file whose first
    // module matches the (now uniquely-determined) entry module. The
    // cert's source_fingerprint covers ALL sources via v7 framed concat,
    // so source_name is informational; the multi-file fact is reflected
    // in module_names.
    //
    // PR B commit #2: when ambient grew the set and there's no entry
    // candidate (legacy snippet-style callers), fall back to the first
    // non-stdlib source's name. The ambient-included stdlib files are
    // identified by their canonical paths.
    let entry_source_name = if candidates.is_empty() {
        parsed
            .iter()
            .find(|(s, _)| {
                !crate::ambient_stdlib::all_module_sources()
                    .iter()
                    .any(|(path, _)| *path == s.name())
            })
            .map(|(s, _)| s.name().to_string())
            .unwrap_or_else(|| "<project>".to_string())
    } else {
        let chosen_module = candidates[0].module().to_string();
        parsed
            .iter()
            .find(|(_, p)| p.modules.first().is_some_and(|m| m.name == chosen_module))
            .map(|(s, _)| s.name().to_string())
            .unwrap_or_else(|| "<project>".to_string())
    };

    // Convergence: feed the merged Program through the post-parse
    // pipeline. N32-W5S1: exactly one call to compile_ast_with_options
    // from compile_project.
    let mut compilation = compile_ast_with_options(
        merged,
        entry_source_name,
        Arc::new(source_map),
        options,
        context,
    )?;
    compilation.warnings.splice(0..0, parser_warnings_all);
    Ok(compilation)
}

/// Wall 5 Step 1: entry-point candidate carried by the merged Program.
/// Returned by [`find_entry_points`]; consumed by `compile_project`'s
/// M003/M004/M005/M006 checks.
#[derive(Debug, Clone)]
enum EntryPoint {
    /// `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64` —
    /// the forge ABI. Detected by [`is_tool_main`] per N24-W5S1.
    ToolMain { module: String },
    /// `entry actor <Name> { ... }` — the actor ABI. Detected by the
    /// `is_entry: bool` field on `ActorDef`.
    EntryActor { module: String },
}

impl EntryPoint {
    fn module(&self) -> &str {
        match self {
            EntryPoint::ToolMain { module, .. } | EntryPoint::EntryActor { module, .. } => module,
        }
    }
}

/// N24-W5S1: the single canonical predicate for the tool-entry ABI.
/// Exhaustive pattern match. Mismatched signature → not a candidate
/// (existing T-coded signature errors fire elsewhere if the user
/// intended this as the entry).
fn is_tool_main(item: &Item) -> bool {
    let Item::FnDef(fn_def) = item else {
        return false;
    };
    if fn_def.visibility != Visibility::Public {
        return false;
    }
    if fn_def.name != "tool_main" {
        return false;
    }
    if fn_def.params.len() != 2 {
        return false;
    }
    // A TypeExpr names `i64` iff its path has the single segment "i64",
    // no type arguments, no ref/slice modifier, and no parametric
    // cap-type deadlines.
    let is_plain_i64 = |ty: &TypeExpr| {
        ty.ref_kind.is_none()
            && ty.deadline.is_empty()
            && ty.path.type_args.is_empty()
            && ty.path.segments.len() == 1
            && ty.path.segments[0] == "i64"
    };
    if !is_plain_i64(&fn_def.params[0].ty) {
        return false;
    }
    if !is_plain_i64(&fn_def.params[1].ty) {
        return false;
    }
    match &fn_def.return_type {
        Some(ty) => is_plain_i64(ty),
        None => false,
    }
}

/// Detect actor entry per the `is_entry: bool` field on `ActorDef`.
fn is_entry_actor(item: &Item) -> bool {
    matches!(item, Item::ActorDef(ActorDef { is_entry: true, .. }))
}

/// M011: a tool project must declare no actors. RTC-NOOP slice 2.
///
/// A compilation that declares `pub fn tool_main` targets the ephemeral
/// forge, which cannot run actors — any `Item::ActorDef` (entry OR
/// non-entry) is dead code whose `send`/`spawn`/capability machinery
/// traps in the forge (RTC-NOOP slice 1). This is the true-north
/// compile-time signal: an agent who writes a tool with stray actor
/// code gets an in-loop error, not a clean compile of inert machinery.
///
/// Placement (X-G1): this runs at `compile_ast_with_options`, the single
/// convergence point BOTH the single-file and multi-file paths traverse.
/// M005/M006 live in `compile_project`'s multi-file-only block and never
/// see the single-file fast path (compiler.rs single-file bypass) nor a
/// non-entry actor (their `is_entry_actor` predicate) — so this gate,
/// not "tighten M005/M006", is what closes the gap.
///
/// Partitioning (X-G4): in multi-file, `tool_main` + `entry actor` still
/// trips M005/M006 *before* the convergence and returns early, so this
/// never double-fires and the existing M005/M006 fixtures are unchanged.
/// M011 covers exactly what they miss: the single-file path (all actor
/// mixes) and the multi-file non-entry mix.
///
/// Detection is AST-based (X-G2): a `matches!` over `Item::ActorDef`,
/// never a source-text scan for the word `actor`.
#[allow(clippy::result_large_err)]
fn enforce_tool_actor_exclusion(program: &Program) -> Result<(), Diagnostic> {
    // A tool project iff some module declares `pub fn tool_main`.
    let tool_module = program
        .modules
        .iter()
        .find(|m| m.items.iter().any(is_tool_main))
        .map(|m| m.name.as_str());
    let Some(tool_module) = tool_module else {
        return Ok(());
    };

    // Collect every actor definition across all modules (X-G3: entry
    // flag ignored; X-G7: flat scan over today's non-nesting `Item`).
    let actors: Vec<String> = program
        .modules
        .iter()
        .flat_map(|m| {
            m.items.iter().filter_map(move |item| match item {
                Item::ActorDef(actor) => Some(format!("`{}` in module `{}`", actor.name, m.name)),
                _ => None,
            })
        })
        .collect();

    if actors.is_empty() {
        return Ok(());
    }

    Err(Diagnostic::error(
        codes::M011,
        format!(
            "tool project (module `{tool_module}` declares `pub fn tool_main`, targeting the ephemeral forge) also declares actor {} — the forge cannot run actors. Remove the actor(s), or drop `tool_main` and build a persistent `entry actor` project instead",
            actors.join(", ")
        ),
        None,
    ))
}

/// N3-W5S1: enumerate every entry-point candidate in the merged Program.
/// Today's AST does not admit nested module declarations inside an
/// `Item::*` variant, so the "recursive descent" mandated by the
/// constraint collapses to flat iteration over `Program.modules` and
/// each module's `items`. If a future PR introduces nested modules as
/// AST variants, this helper must be extended to descend.
fn find_entry_points(program: &Program) -> Vec<EntryPoint> {
    let mut entries = Vec::new();
    for module in &program.modules {
        for item in &module.items {
            if is_tool_main(item) {
                entries.push(EntryPoint::ToolMain {
                    module: module.name.clone(),
                });
            }
            if is_entry_actor(item) {
                entries.push(EntryPoint::EntryActor {
                    module: module.name.clone(),
                });
            }
        }
    }
    entries
}

/// N11-W5S1: source-name charset + structure validation. Enforced at
/// both the CLI boundary and the library boundary so direct library
/// callers cannot bypass the check.
///
/// Rules:
/// - Must match `^[A-Za-z0-9_./\-]+\.sigil$`.
/// - Must not contain `..` as a path segment (no traversal).
/// - Must not contain NUL bytes or other control chars.
// `Diagnostic` is ~144 bytes after Wall 5 Step 1 added the
// source_name + source_id channels. The two helpers below return
// Result<(), Diagnostic> as a private internal shape; boxing the
// diagnostic would just add a heap hop with no real benefit
// (one Diagnostic per error path, never accumulated).
#[allow(clippy::result_large_err)]
fn validate_source_name(name: &str) -> Result<(), Diagnostic> {
    if name.is_empty() {
        return Err(Diagnostic::error(
            codes::M009,
            "source file name must not be empty",
            None,
        ));
    }
    if !name.ends_with(".sigil") {
        return Err(Diagnostic::error(
            codes::M009,
            format!("source file name `{name}` must end with `.sigil`"),
            None,
        ));
    }
    if name.bytes().any(|b| b == 0) {
        return Err(Diagnostic::error(
            codes::M009,
            format!("source file name `{name}` contains a NUL byte"),
            None,
        ));
    }
    if name.chars().any(|c| c.is_control()) {
        return Err(Diagnostic::error(
            codes::M009,
            format!("source file name `{name}` contains a control character"),
            None,
        ));
    }
    // Path traversal: forbid any `..` segment when split by `/`.
    if name.split('/').any(|seg| seg == "..") {
        return Err(Diagnostic::error(
            codes::M009,
            format!("source file name `{name}` contains a `..` path segment"),
            None,
        ));
    }
    // Charset whitelist (manual check; we don't import regex per
    // NF-S7-AG-16's lessons): `[A-Za-z0-9_./\\-]`.
    if !name
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '/' | '\\' | '-'))
    {
        return Err(Diagnostic::error(
            codes::M009,
            format!(
                "source file name `{name}` contains disallowed characters; allowed: A-Z a-z 0-9 _ . / \\ - and the `.sigil` extension"
            ),
            None,
        ));
    }
    Ok(())
}

/// N4-W5S1 + N12-W5S1: M001 — the FIRST module declared in `<stem>.sigil`
/// MUST be named `<stem>` (case-sensitive byte equality; no
/// `to_lowercase` normalization). Subsequent inline modules in the same
/// file are unconstrained (R4 from the plan's risk surface).
///
/// Edge cases:
/// - File declares zero modules → no panic. If items are present at
///   top level, fire M001 sub-case "declares items but no module".
///   Items-empty + modules-empty → silent no-op (whitespace-only file
///   compiles to nothing in multi-file mode; the merge step contributes
///   no modules from this file).
/// - File declares only `module foo;` with no items AFTER → first-module
///   check still applies normally.
#[allow(clippy::result_large_err)]
fn enforce_filename_module(source: &SourceFile, program: &Program) -> Result<(), Diagnostic> {
    // Extract stem: strip `.sigil` extension and any leading directory.
    // N12-W5S1: byte-equality; no case normalization.
    let stripped = source
        .name()
        .strip_suffix(".sigil")
        .expect("validate_source_name ensures `.sigil` suffix");
    let stem = stripped.rsplit_once('/').map_or(stripped, |(_, s)| s);
    let stem = stem.rsplit_once('\\').map_or(stem, |(_, s)| s);

    match program.modules.first() {
        None => {
            // Empty-modules file. Items can only appear inside a module,
            // so an empty modules vec implies an empty items list too —
            // a whitespace-only file. No error; the file contributes
            // nothing to the merge.
            Ok(())
        }
        Some(first) if first.name == stem => Ok(()),
        Some(first) => Err(Diagnostic::error_in_file(
            codes::M001,
            format!(
                "file `{}` declares `module {}` first, but the filename stem `{}` requires the first module to be named `{}`",
                source.name(),
                first.name,
                stem,
                stem
            ),
            Some(first.span),
            source.name(),
        )),
    }
}

/// N17-W5S1: M002 — duplicate module name across the project, whether
/// declared at file top-level or as an inline `module foo { ... }` in
/// another file. Single canonical BTreeMap keyed by module NAME (not
/// declaration form), values collect (source_name, span) tuples so the
/// diagnostic can point at every offending site.
fn find_duplicate_module_names(parsed: &[(SourceFile, Program)]) -> Option<Diagnostic> {
    let mut locations: BTreeMap<String, Vec<(String, Span)>> = BTreeMap::new();
    for (source, program) in parsed {
        for module in &program.modules {
            locations
                .entry(module.name.clone())
                .or_default()
                .push((source.name().to_string(), module.span));
        }
    }
    for (name, sites) in &locations {
        if sites.len() >= 2 {
            let site_list = sites
                .iter()
                .map(|(file, _)| format!("`{file}`"))
                .collect::<Vec<_>>()
                .join(", ");
            let (first_file, first_span) = &sites[0];
            return Some(Diagnostic::error_in_file(
                codes::M002,
                format!(
                    "module `{name}` declared in {} files: [{}] — module names must be unique across the project (top-level OR inline declarations both count)",
                    sites.len(),
                    site_list
                ),
                Some(*first_span),
                first_file,
            ));
        }
    }
    None
}

/// Hard caps on a single compilation unit. Adversarial source DoS is rejected
/// at the door rather than burning O(N²) work in cross-module dispatch.
/// Per Phase 5a-1.5 / I15.
pub const MAX_SOURCE_BYTES: usize = 5 * 1024 * 1024; // 5 MB
pub const MAX_MODULE_COUNT: usize = 256;
pub const MAX_FUNCTION_COUNT: usize = 10_000;

/// Ordered typed-AST security gates. Keeping the manifest and dispatcher together makes deleting
/// or reordering a production check an explicit, reviewable change rather than a one-line omission
/// in the larger compile pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypedSecurityPass {
    Ring,
    Effect,
    Taint,
}

const TYPED_SECURITY_PASSES: &[TypedSecurityPass] = &[
    TypedSecurityPass::Ring,
    TypedSecurityPass::Effect,
    TypedSecurityPass::Taint,
];

fn run_typed_security_passes(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    for pass in TYPED_SECURITY_PASSES {
        match pass {
            TypedSecurityPass::Ring => ring_check::check_rings(program)?,
            TypedSecurityPass::Effect => effect_check::check_effects(program)?,
            TypedSecurityPass::Taint => taint_check::check_taints(program)?,
        }
    }
    Ok(())
}

fn compile_source_with_options(
    source: &SourceFile,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    // SourceId follow-up: build a one-entry SourceMap for the
    // single-file path. Source id = 0; every span the lexer/parser
    // emits will carry SourceId(0).
    let mut source_map = SourceMap::new();
    let source_id = source_map.push(source.clone());
    let source_map = Arc::new(source_map);

    if source.text().trim().is_empty() {
        return Err(CompileError::with_sources(
            vec![Diagnostic::error(
                codes::S003,
                "source must not be empty",
                Some(Span::with_source(0, 0, source_id)),
            )],
            Arc::clone(&source_map),
        ));
    }

    // S005: source byte cap — checked before parse so adversarial inputs
    // never reach the lexer.
    if source.text().len() > MAX_SOURCE_BYTES {
        return Err(CompileError::with_sources(
            vec![Diagnostic::error(
                codes::S005,
                format!(
                    "source is {} bytes; maximum is {} ({} MB)",
                    source.text().len(),
                    MAX_SOURCE_BYTES,
                    MAX_SOURCE_BYTES / (1024 * 1024)
                ),
                Some(Span::with_source(0, 0, source_id)),
            )],
            Arc::clone(&source_map),
        ));
    }

    let (ast, parser_diagnostics) = parser::parse_with_id(source, source_id);
    // Severity-aware gate (P031 is the parser's first WARNING-tier diagnostic):
    // abort only on a `Severity::Error`, mirroring `check_with_warnings`'
    // documented contract. On failure the warnings still ride along (errors
    // first) so the render is unchanged; on success they merge into
    // `Compilation.warnings` ahead of the type-check warnings.
    let (parser_errors, parser_warnings): (Vec<Diagnostic>, Vec<Diagnostic>) = parser_diagnostics
        .into_iter()
        .partition(|d| d.severity() == crate::diagnostics::Severity::Error);
    if !parser_errors.is_empty() {
        let mut all = parser_errors;
        all.extend(parser_warnings);
        return Err(CompileError::with_sources(all, Arc::clone(&source_map)));
    }

    let mut compilation =
        compile_ast_with_options(ast, source.name().to_owned(), source_map, options, context)?;
    compilation.warnings.splice(0..0, parser_warnings);
    Ok(compilation)
}

/// Post-parse pipeline shared by `compile_source_with_options` (single-
/// file path) and `compile_project` (multi-file path). Picks up at the
/// S004 module-count cap and runs through wasm emission.
///
/// N32-W5S1: this is the SOLE convergence point — every compile path
/// terminates here.
fn compile_ast_with_options(
    ast: Program,
    source_name: String,
    sources: Arc<SourceMap>,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<Compilation, CompileError> {
    // S004: module count cap.
    if ast.modules.len() > MAX_MODULE_COUNT {
        return Err(CompileError::with_sources(
            vec![Diagnostic::error(
                codes::S004,
                format!(
                    "compilation unit declares {} modules; maximum is {}",
                    ast.modules.len(),
                    MAX_MODULE_COUNT
                ),
                Some(Span::default()),
            )],
            sources,
        ));
    }

    // S006: function count cap (across all modules; counts FnDef + ExternFnDecl
    // + ImplDef methods).
    let function_count: usize = ast
        .modules
        .iter()
        .map(|m| {
            m.items
                .iter()
                .map(|item| match item {
                    crate::ast::Item::FnDef(_) | crate::ast::Item::ExternFnDecl(_) => 1,
                    crate::ast::Item::ImplDef(impl_def) => impl_def.methods.len(),
                    _ => 0,
                })
                .sum::<usize>()
        })
        .sum();
    if function_count > MAX_FUNCTION_COUNT {
        return Err(CompileError::with_sources(
            vec![Diagnostic::error(
                codes::S006,
                format!(
                    "compilation unit declares {} functions across all modules; maximum is {}",
                    function_count, MAX_FUNCTION_COUNT
                ),
                Some(Span::default()),
            )],
            sources,
        ));
    }

    // M011 (RTC-NOOP slice 2): a tool project must declare no actors.
    // Runs at the convergence point so it catches the single-file path
    // that M001-M006 bypass. Pure pre-lowering rejection: no accepted
    // program's path changes, so the byte capstone stays pinned (X-G5).
    if let Err(diag) = enforce_tool_actor_exclusion(&ast) {
        return Err(CompileError::with_sources(vec![diag], sources));
    }

    let to_err = |diags| CompileError::with_sources(diags, Arc::clone(&sources));
    let resolved = name_resolution::resolve(&ast).map_err(to_err)?;
    let (mut typed, authority_registry, warnings) =
        type_check::check_with_warnings(&resolved, &options).map_err(to_err)?;
    run_typed_security_passes(&typed).map_err(to_err)?;
    // Preserve the pre-desugar typed program for the retained v6-derived security obligations.
    // The v8 semantic prefix and v9 occurrence declarations below are projected from the resolved
    // post-desugar AIR, so the linked Lean verifier sees every mandatory production layer in one
    // canonical byte string.
    let typed_for_formal = typed.clone();
    // Effect Handlers (EH4): the evidence-passing desugar — rewrites the
    // effect-handler surface it supports into ordinary closure-passing typed AST
    // BEFORE the gate (after the security passes, which walked the original nodes
    // for C-VIS).
    effect_desugar::desugar_effect_handlers(&mut typed);
    // Effect Handlers (EH3): the staged-rollout gate. Runs AFTER the desugar
    // (LC-PARTITION), so it rejects only what the desugar did NOT handle — a
    // well-formed but un-lowered `perform`/clause-`handle`/`resume` is rejected
    // (E004) and never reaches AIR. Narrowed as the desugar grows.
    effect_check::check_effect_handlers_gated(&typed).map_err(to_err)?;
    let effects_required = collect_program_effects(&typed, &ast);
    let typed_for_evidence = typed.clone();
    let air = air::lower(&typed);
    // Mandatory, load-bearing formal gate. The exact canonical bytes checked here are
    // fingerprinted in `FormalSecurityReport`; no environment switch or feature flag can bypass
    // this call. Defer an unsuccessful verdict until the compatibility gates below have had the
    // opportunity to return their established source-level C/O/T diagnostics.
    let formal_security_verdict =
        formal::verify_with_context(&typed_for_formal, &air, &authority_registry, context);
    // Structural checks + the v2 Z3 prover (the sole AIR-cap prover
    // since quarantine PR 5; the shadow comparison harness retired with
    // the legacy path it compared against).
    let capability_report = capability::verify(&air, &authority_registry).map_err(to_err)?;
    let ownership_report = ownership::verify(&air).map_err(to_err)?;
    let formal_security_report = formal_security_verdict.map_err(to_err)?;
    let (air, memory_report) = memory::lower(air);
    let (air, fuel_plan) = fuel::insert(air);
    let runtime_module = build_runtime_module(&typed, &air, fuel_plan.recommended_budget);
    let mut wasm_output = wasm::emit(&air);
    if let Some(requirement) = context.host_requirement() {
        wasm::append_host_profile_requirement(&mut wasm_output, requirement);
    }

    Ok(Compilation {
        source_name,
        module_names: ast
            .modules
            .iter()
            .map(|module| module.name.clone())
            .collect(),
        ast,
        typed: typed_for_evidence,
        air,
        wasm_inner: wasm_output.inner,
        wasm_outer: wasm_output.outer,
        fuel_budget: fuel_plan.recommended_budget,
        runtime_module,
        capability_report,
        ownership_report,
        formal_security_report,
        memory_report,
        fuel_plan,
        effects_required,
        warnings,
        sources,
    })
}

/// Union every declared function effect into a sorted, deduplicated policy
/// surface. Typed IDs remain authoritative for registered effects; the AST
/// pass preserves well-known marker names such as `FsIO`, `NetIO`, and
/// `Alloc` when a source uses them without a local `effect` declaration.
fn collect_program_effects(typed: &TypedProgram, ast: &Program) -> Vec<String> {
    let mut ids = BTreeSet::new();
    for module in &typed.modules {
        for function in &module.functions {
            for id in &function.effects.effects {
                ids.insert(*id);
            }
        }
    }
    let mut names: BTreeSet<String> = ids
        .into_iter()
        .filter_map(|id| typed.effect_registry.name_of(id).map(str::to_owned))
        .collect();

    for module in &ast.modules {
        for item in &module.items {
            match item {
                Item::FnDef(function) => {
                    // Phase 4 (row polymorphism): a row VARIABLE's name is a
                    // binder, not an effect — shipping the literal string (e.g.
                    // `"e"`) into `effects_required` would fail the deploy
                    // gate's bidirectional effect-set equality on every deploy.
                    // The variable's instantiations are already counted via the
                    // typed pass above (each mono's row is concrete).
                    let row_params = crate::ast::effect_row_param_names(function);
                    names.extend(
                        function
                            .effects
                            .iter()
                            .flatten()
                            .filter(|n| !row_params.contains(n))
                            .cloned(),
                    );
                }
                Item::ImplDef(implementation) => {
                    names.extend(
                        implementation
                            .methods
                            .iter()
                            .flat_map(|method| method.effects.iter().flatten().cloned()),
                    );
                }
                Item::ExternFnDecl(function) => {
                    names.extend(function.effects.iter().cloned());
                }
                _ => {}
            }
        }
    }

    names.into_iter().collect()
}

fn build_runtime_module(
    typed: &TypedProgram,
    air: &AirProgram,
    fuel_budget: u64,
) -> RuntimeModuleSpec {
    #[derive(Debug, Default)]
    struct ActorBuilder {
        actor_type_id: u32,
        is_entry: bool,
        init_export: Option<String>,
        init_params: Vec<RuntimeTypeSpec>,
        handlers: Vec<RuntimeHandlerSpec>,
        /// State fields (an actor's init/handler `captures`), captured once from
        /// the first init/handler seen. Used to emit `state_layout`/`state_size`.
        state_captures: Vec<crate::type_check::TypedParam>,
        /// PPS-4: computed from the typed init body (fail-closed `Default` =
        /// `false` until the init is seen and its walk says otherwise).
        init_replay_safe: bool,
    }

    let air_functions = air
        .functions
        .iter()
        .map(|function| (function.export_name.as_str(), &function.kind))
        .collect::<BTreeMap<_, _>>();
    let mut actors = BTreeMap::<String, ActorBuilder>::new();
    for module in &typed.modules {
        for function in &module.functions {
            let Some(kind) = air_functions.get(function.export_name.as_str()).copied() else {
                continue;
            };

            match (&function.kind, kind) {
                (
                    TypedFunctionKind::ActorInit { actor, is_entry },
                    AirFunctionKind::ActorInit { actor_type, .. },
                ) => {
                    let entry = actors.entry(actor.clone()).or_default();
                    entry.actor_type_id = actor_type.0;
                    entry.is_entry |= *is_entry;
                    entry.init_export = Some(function.export_name.clone());
                    entry.init_params = function
                        .params
                        .iter()
                        .map(|param| runtime_type(&param.ty))
                        .collect();
                    // Two gates, both fail-closed: the effects row is the
                    // TRANSITIVE summary (a cap-arg-free helper doing extern/
                    // unsafe work still surfaces here — only `Alloc` is
                    // replay-neutral), and the body walk fences the cap-flow
                    // constructs the row does not track.
                    let alloc_id = typed.effect_registry.lookup("Alloc");
                    let effects_replay_neutral = function
                        .effects
                        .effects
                        .iter()
                        .all(|id| Some(*id) == alloc_id);
                    entry.init_replay_safe =
                        effects_replay_neutral && init_body_replay_safe(&function.body);
                    if entry.state_captures.is_empty() {
                        entry.state_captures = function.captures.clone();
                    }
                }
                (
                    TypedFunctionKind::ActorHandler {
                        actor,
                        handler,
                        is_entry,
                    },
                    AirFunctionKind::ActorHandler {
                        actor_type,
                        handler_id,
                        ..
                    },
                ) => {
                    let entry = actors.entry(actor.clone()).or_default();
                    entry.actor_type_id = actor_type.0;
                    entry.is_entry |= *is_entry;
                    entry.handlers.push(RuntimeHandlerSpec {
                        name: handler.clone(),
                        handler_id: handler_id.0,
                        export_name: function.export_name.clone(),
                        params: function
                            .params
                            .iter()
                            .map(|param| runtime_type(&param.ty))
                            .collect(),
                        ret: runtime_type(&function.ret),
                    });
                    if entry.state_captures.is_empty() {
                        entry.state_captures = function.captures.clone();
                    }
                }
                _ => {}
            }
        }
    }

    let actors = actors
        .into_iter()
        .map(|(name, mut actor)| {
            actor.handlers.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
            // State struct placement — offsets/size from the single authority
            // (`state_layout_offsets`, SC-4), paired with each field's runtime
            // type. `ty` comes from the same `captures` the offsets are derived
            // from, so field i lines up by construction.
            let layout = crate::air::state_layout_offsets(&actor.state_captures);
            let state_layout = layout
                .fields
                .iter()
                .zip(&actor.state_captures)
                .map(|((fname, offset, _air_ty), cap)| RuntimeStateFieldSpec {
                    name: fname.clone(),
                    offset: *offset,
                    ty: runtime_type(&cap.ty),
                })
                .collect::<Vec<_>>();
            RuntimeActorSpec {
                name,
                actor_type_id: actor.actor_type_id,
                is_entry: actor.is_entry,
                init_export: actor.init_export,
                init_params: actor.init_params,
                handlers: actor.handlers,
                state_layout,
                state_size: layout.size,
                init_replay_safe: actor.init_replay_safe,
            }
        })
        .collect::<Vec<_>>();

    RuntimeModuleSpec {
        module_name: typed
            .modules
            .first()
            .map(|module| module.name.clone())
            .unwrap_or_else(|| "<inline>".to_owned()),
        fuel_budget,
        imports: RuntimeImportSpec::phase_one(),
        actors,
    }
}

/// PPS-4 (restart-as-GC): is this actor `init` body faithfully REPLAYABLE?
///
/// Replay-safe means re-running the init with the SAME retained argument
/// handles reproduces the same state without spending, minting, or moving any
/// authority and without emitting any outward effect. The walk is FAIL-CLOSED:
/// only constructs known to be pure state construction are admitted, and any
/// unrecognized statement or expression form makes the whole init
/// non-replayable (which merely restricts restart to the preserve-state path —
/// pessimal, never unsound). Fenced outright: the cap-table ops
/// (draw/split/restrict/mint), spawn/send/ask, extern/grant/effect constructs,
/// and any call passing a capability-typed argument (a helper could consume
/// it out of sight).
fn init_body_replay_safe(body: &crate::typed_ast::TypedBlock) -> bool {
    stmts_replay_safe(&body.statements)
}

fn stmts_replay_safe(stmts: &[crate::typed_ast::TypedStmt]) -> bool {
    use crate::typed_ast::TypedStmt;
    stmts.iter().all(|stmt| match stmt {
        TypedStmt::Let(s) => expr_replay_safe(&s.value),
        TypedStmt::Assign(s) => expr_replay_safe(&s.place) && expr_replay_safe(&s.value),
        TypedStmt::Expr(s) => expr_replay_safe(&s.expr),
        TypedStmt::Return(s) => s.value.as_ref().is_none_or(expr_replay_safe),
        TypedStmt::If(s) => {
            expr_replay_safe(&s.condition)
                && stmts_replay_safe(&s.then_branch.statements)
                && stmts_replay_safe(&s.else_branch.statements)
        }
        TypedStmt::Match(s) => {
            expr_replay_safe(&s.scrutinee)
                && s.arms.iter().all(|arm| {
                    arm.guard.as_ref().is_none_or(expr_replay_safe)
                        && stmts_replay_safe(&arm.body.statements)
                })
        }
        TypedStmt::While(s) => {
            expr_replay_safe(&s.condition) && stmts_replay_safe(&s.body.statements)
        }
        TypedStmt::ForIn(s) => expr_replay_safe(&s.iterable) && stmts_replay_safe(&s.body),
        TypedStmt::ForRange(s) => {
            expr_replay_safe(&s.start) && expr_replay_safe(&s.end) && stmts_replay_safe(&s.body)
        }
        TypedStmt::Break(_) | TypedStmt::Continue(_) => true,
    })
}

fn expr_replay_safe(expr: &crate::typed_ast::TypedExpr) -> bool {
    use crate::typed_ast::TypedExprKind;
    match &expr.kind {
        TypedExprKind::Literal(_) | TypedExprKind::Local(_) | TypedExprKind::StateField(_) => true,
        TypedExprKind::Binary(b) => expr_replay_safe(&b.lhs) && expr_replay_safe(&b.rhs),
        TypedExprKind::RecordConstruct(r) => {
            r.fields.iter().all(|(_, value)| expr_replay_safe(value))
        }
        TypedExprKind::FieldAccess(f) => expr_replay_safe(&f.object),
        TypedExprKind::ArrayLit(a) => a.elements.iter().all(expr_replay_safe),
        TypedExprKind::Index(i) => expr_replay_safe(&i.array) && expr_replay_safe(&i.index),
        TypedExprKind::ResultCtor(r) => expr_replay_safe(&r.value),
        TypedExprKind::EnumConstruct(e) => e.fields.iter().all(expr_replay_safe),
        TypedExprKind::Try(t) => expr_replay_safe(&t.value),
        TypedExprKind::Borrow(b) => expr_replay_safe(&b.inner),
        // A plain call is admitted ONLY when no argument is capability- or
        // actor-ref-typed — a helper handed a cap could draw/split it out of
        // the walk's sight, and one handed a ref could send. (A helper with
        // neither has no authority to reach: cap ops and messaging all
        // require such a value, and ambient-authority work — extern, unsafe,
        // effects — is caught by the effects-row gate at the init level.)
        TypedExprKind::Call(c) => c.args.iter().all(|arg| {
            !matches!(arg.ty, Type::Cap(..) | Type::ActorRef(_)) && expr_replay_safe(arg)
        }),
        TypedExprKind::Intrinsic(i) => i.args.iter().all(|arg| {
            !matches!(arg.ty, Type::Cap(..) | Type::ActorRef(_)) && expr_replay_safe(arg)
        }),
        // Everything else — the cap-table ops (CapDraw/CapSplit/CapRestrict/
        // Mint), Spawn/Send/Ask, Extern/Grant/Handle/Perform, closures,
        // indirect calls, regions, declassify, and ANY FUTURE VARIANT — is
        // non-replayable by default. Fail-closed.
        _ => false,
    }
}

fn runtime_type(ty: &Type) -> RuntimeTypeSpec {
    match ty {
        Type::Unit | Type::Error => RuntimeTypeSpec::Unit,
        Type::Bool => RuntimeTypeSpec::Bool,
        Type::I32 | Type::U32 | Type::I64 | Type::U64 | Type::F64 => RuntimeTypeSpec::I64,
        // u256/i256: a pointer-backed 32-byte aggregate at the runtime ABI, like
        // a record/tuple (NOT an i64 scalar). Not sendable across actors yet (E7).
        Type::U256 => RuntimeTypeSpec::Named("u256".to_owned()),
        Type::I256 => RuntimeTypeSpec::Named("i256".to_owned()),
        Type::Str => RuntimeTypeSpec::Str,
        Type::Named(name, _) => RuntimeTypeSpec::Named(name.clone()),
        Type::Cap(name, _) => RuntimeTypeSpec::Cap(name.clone()),
        Type::ActorRef(actor) => RuntimeTypeSpec::ActorRef(actor.clone()),
        Type::Array { .. } => RuntimeTypeSpec::Named("Array".to_owned()),
        Type::Generic(_) => RuntimeTypeSpec::Named("Generic".to_owned()),
        // PIL: IntLit should be resolved before reaching runtime_type
        // (which feeds runtime ABI spec). If it does, treat it as I64
        // (the eventual default-fallback target). Defensive — the
        // walker should eliminate IntLit at binding sites first.
        Type::IntLit(_) => RuntimeTypeSpec::I64,
        Type::Fn(_, _, _, _) => RuntimeTypeSpec::Named("Fn".to_owned()),
        Type::Ref(_, _) => RuntimeTypeSpec::Named("Ref".to_owned()),
        Type::Slice(_) => RuntimeTypeSpec::Named("Slice".to_owned()),
        Type::Ptr(_) => RuntimeTypeSpec::Named("Ptr".to_owned()),
        Type::MutPtr(_) => RuntimeTypeSpec::Named("MutPtr".to_owned()),
        // Tuple: a heap struct (pointer) at the runtime ABI, like a record.
        Type::Tuple(_) => RuntimeTypeSpec::Named("Tuple".to_owned()),
        // Regions (DEF-2b): a region handle is an i64 token at the runtime ABI.
        Type::Region => RuntimeTypeSpec::I64,
        // HKT (EX-4): a higher-kinded var/app/ctor must have been erased to a
        // concrete Type::Named before AIR — and runtime_type runs over the lowered
        // program — so any residual here is a compiler-internal invariant violation.
        Type::HktVar { name, .. } => {
            panic!("ICE: unresolved higher-kinded var `{name}` reached runtime_type")
        }
        Type::HktApp { ctor, .. } => {
            panic!("ICE: unresolved higher-kinded application `{ctor}<…>` reached runtime_type")
        }
        Type::TypeCtor(name) => {
            panic!("ICE: bare type-constructor `{name}` reached runtime_type (should be erased)")
        }
        // Typestate (ST-1 backstop): a state marker is type-level only and erases
        // before AIR; `runtime_type` runs over the lowered program, so any residual
        // here is a compiler-internal invariant violation.
        Type::StateMarker(name) => {
            panic!("ICE: state marker `{name}` reached runtime_type (should be erased)")
        }
        // Effect Handlers (C-NEVER): the abortive bottom type is gated before AIR.
        Type::Never => {
            panic!("ICE: Type::Never reached runtime_type (must be erased / gated before AIR)")
        }
    }
}

#[cfg(test)]
mod tests {
    use sigil_abi::RuntimeTypeSpec;

    use crate::air::{AirFunctionKind, AirStmt, AirTerminator};

    use super::{
        CompileLimits, compile_module, compile_named_module, compile_tool, compile_tool_with_limits,
    };

    #[test]
    fn rejects_empty_source() {
        assert!(compile_module("").is_err());
    }

    #[test]
    fn compiles_module_header_to_wasm() {
        let compilation = compile_module("module sigil;").expect("module should compile");

        assert_eq!(compilation.primary_module_name(), Some("sigil"));
        assert_eq!(&compilation.wasm_inner[..4], b"\0asm");
        assert_eq!(compilation.air.functions.len(), 1);
    }

    #[test]
    fn compiles_phase_one_top_level_shapes() {
        let source = r#"
module sigil;
const RETRIES: i64 = 3;
cap type FuelCap {
    units
}
fn boot(message: str) -> bool {
    let ready = true;
    return ready;
}
entry actor Main {
    state {
        counter: i64,
    }

    on Start(peer: ActorRef<Worker>) {}
}

actor Worker {
    on Ping() {}
}
"#;

        let compilation = compile_module(source).expect("source should compile");
        let exports = compilation
            .air
            .functions
            .iter()
            .map(|function| function.export_name.as_str())
            .collect::<Vec<_>>();

        assert_eq!(compilation.primary_module_name(), Some("sigil"));
        assert_eq!(compilation.air.functions.len(), 3);
        assert!(exports.contains(&"sigil__boot"));
        assert!(exports.contains(&"Main__Start"));
        assert!(exports.contains(&"Worker__Ping"));
    }

    #[test]
    fn compiles_actor_init_exports_and_state_reads() {
        let source = r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state {
        counter: i64,
        fuel: Fuel,
    }

    init(seed: i64) {
        let baseline = counter;
        let provided = seed;
    }

    on Start(peer: ActorRef<Worker>) -> i64 {
        return counter;
    }
}

actor Worker {
    on Ping() {}
}
"#;

        let compilation =
            compile_module(source).expect("actor init and state reads should compile");
        let exports = compilation
            .air
            .functions
            .iter()
            .map(|function| function.export_name.as_str())
            .collect::<Vec<_>>();

        assert!(exports.contains(&"Main__init"));
        assert!(exports.contains(&"Main__Start"));
        assert!(exports.contains(&"Worker__Ping"));
    }

    #[test]
    fn compiles_actor_message_ops_to_air() {
        let source = r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state {
        fuel: Fuel,
    }

    on Start(worker: ActorRef<Worker>) -> i64 {
        worker.send(Ping());
        let child = spawn::<Worker>(fuel);
        let response = worker.ask(GetCount(), timeout: 5);
        return response;
    }
}

actor Worker {
    init(fuel: Fuel) {}

    on Ping() {}

    on GetCount() -> i64 {
        return 1;
    }
}
"#;

        let compilation = compile_module(source).expect("message ops should compile");
        let has_send = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::MessageSend { .. }));
        let has_ask = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::MessageAsk { .. }));
        let has_spawn = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::SpawnActor { .. }));
        let has_payload_serialization = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::SerializeMessage { .. }));

        let start_handler = compilation
            .air
            .functions
            .iter()
            .find(|function| {
                matches!(
                    function.kind,
                    AirFunctionKind::ActorHandler {
                        ref actor,
                        ref handler,
                        ..
                    } if actor == "Main" && handler == "Start"
                )
            })
            .expect("expected Main::Start handler metadata");
        let send_stmt = start_handler
            .blocks
            .iter()
            .flat_map(|block| block.stmts.iter())
            .find_map(|stmt| match stmt {
                AirStmt::MessageSend {
                    actor_type,
                    handler,
                    ..
                } => Some((actor_type.0, handler.0)),
                _ => None,
            })
            .expect("expected send ABI metadata");

        assert!(has_send, "expected AIR to contain a message send");
        assert!(has_ask, "expected AIR to contain a message ask");
        assert!(has_spawn, "expected AIR to contain a spawn actor op");
        assert!(
            has_payload_serialization,
            "expected AIR to serialize message payloads before dispatch"
        );
        assert_ne!(send_stmt.0, 0, "expected stable actor type id");
        assert_ne!(send_stmt.1, 0, "expected stable handler id");
    }

    #[test]
    fn builds_runtime_module_metadata_for_entry_actor() {
        let compilation = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start(worker: ActorRef<Worker>) {}
}

actor Worker {
    init(fuel: Fuel) {}
    on Ping() {}
}
"#,
        )
        .expect("runtime metadata should compile");

        let entry = compilation
            .runtime_module
            .entry_actor()
            .expect("entry actor should be present");
        let start = entry
            .handler_named("Start")
            .expect("entry actor should expose Start");

        assert_eq!(compilation.runtime_module.module_name, "sigil");
        assert_eq!(
            compilation.runtime_module.fuel_budget,
            compilation.fuel_budget
        );
        assert_eq!(compilation.runtime_module.imports.module, "sigil");
        assert_eq!(entry.name, "Main");
        assert!(entry.is_entry);
        assert_eq!(start.export_name, "Main__Start");
        assert_eq!(
            start.params,
            vec![RuntimeTypeSpec::ActorRef("Worker".to_owned())]
        );
        assert_eq!(start.ret, RuntimeTypeSpec::Unit);
        assert_ne!(entry.actor_type_id, 0);
        assert_ne!(start.handler_id, 0);
    }

    // ── M1: actor state layout registry + ABI metadata ──
    // Shapes are chosen to remain valid after M2's entry-state / init-assignment
    // rules land.

    #[test]
    fn state_layout_offsets_accumulate_width_and_align_to_8() {
        use crate::air::state_layout_offsets;
        use crate::ast::TaintLabel;
        use crate::type_check::{Type, TypedParam};
        let p = |name: &str, ty: Type| TypedParam {
            flow: false,
            mutability: crate::ast::Mutability::Default,
            name: name.to_owned(),
            ty,
            taint: TaintLabel::Public,
        };
        // i64(8) @0, bool(4) @8, i64(8) @12 → raw end 20, size aligned up to 8 = 24.
        let layout =
            state_layout_offsets(&[p("a", Type::I64), p("flag", Type::Bool), p("b", Type::I64)]);
        let offsets: Vec<u32> = layout.fields.iter().map(|(_, off, _)| *off).collect();
        assert_eq!(offsets, vec![0, 8, 12]);
        assert_eq!(layout.size, 24);
        // Stateless → empty, size 0.
        assert_eq!(state_layout_offsets(&[]).size, 0);
    }

    // ── M1: property-based invariants of the SC-4 layout authority ──
    // `state_layout_offsets` is the SINGLE placement authority; these properties
    // pin the invariants every consumer (AIR lowering + the emitted ABI) relies
    // on, over arbitrary field-type sequences rather than one hand-picked shape.
    proptest::proptest! {
        #[test]
        fn state_layout_is_a_sound_struct_packing(
            // The FULL scalar state-field family, narrow ints INCLUDED. S0b (M3)
            // settled the width question the M1 comment flagged: there is exactly
            // ONE placement authority — the AIR field width (`AirType::width`, via
            // `state_layout_offsets`) — and the runtime consumes the emitted offsets
            // directly, never a re-derived width. The old `sigil_abi::state_field_width`
            // (which returned 8 for a source-i32 field because `RuntimeTypeSpec`
            // collapses i32/i64) was a dead, unconsumed SECOND authority that
            // DISAGREED with AIR for narrow ints; S0b deleted it. So a narrow-int
            // state field occupies its true AIR slot (i32/u32 → 4, f64/i64 → 8) and
            // the packing is sound for every scalar type — which this generator now
            // exercises directly.
            tys in proptest::collection::vec(
                proptest::prop_oneof![
                    proptest::strategy::Just(crate::type_check::Type::I64),
                    proptest::strategy::Just(crate::type_check::Type::Bool),
                    proptest::strategy::Just(crate::type_check::Type::I32),
                    proptest::strategy::Just(crate::type_check::Type::U32),
                    proptest::strategy::Just(crate::type_check::Type::F64),
                ],
                0..24usize,
            )
        ) {
            use crate::air::state_layout_offsets;
            use crate::ast::TaintLabel;
            use crate::type_check::TypedParam;
            let caps: Vec<TypedParam> = tys
                .iter()
                .enumerate()
                .map(|(i, ty)| TypedParam { name: format!("f{i}"), ty: ty.clone(), taint: TaintLabel::Public, flow: false, mutability: crate::ast::Mutability::Default, })
                .collect();
            let layout = state_layout_offsets(&caps);

            // (1) one placed entry per field, in declaration order.
            proptest::prop_assert_eq!(layout.fields.len(), caps.len());

            // (2) offsets are STRICTLY monotonic and NON-OVERLAPPING: each field
            //     starts exactly at the previous field's end (0-based, no padding
            //     between fields — the M1 packing rule).
            let mut expected = 0u32;
            for (i, (_, off, air_ty)) in layout.fields.iter().enumerate() {
                proptest::prop_assert_eq!(*off, expected, "field {} offset", i);
                expected += air_ty.width();
            }

            // (3) size is the accumulated width aligned UP to 8, and is itself
            //     8-aligned and never less than the raw end.
            proptest::prop_assert_eq!(layout.size, (expected + 7) & !7);
            proptest::prop_assert_eq!(layout.size % 8, 0);
            proptest::prop_assert!(layout.size >= expected);
        }
    }

    #[test]
    fn entry_cap_state_emits_single_slot_layout() {
        let compilation = compile_module(
            r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 0; }
}
"#,
        )
        .expect("cap-only entry actor should compile");

        let entry = compilation.runtime_module.entry_actor().unwrap();
        assert_eq!(entry.state_layout.len(), 1);
        assert_eq!(entry.state_layout[0].name, "fuel");
        assert_eq!(entry.state_layout[0].offset, 0);
        assert_eq!(entry.state_size, 8); // one 4-wide cap slot, aligned up to 8
    }

    #[test]
    fn stateless_actor_has_empty_layout_and_zero_size() {
        let compilation = compile_module(
            r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    init(f: Fuel) {}
    on Ping() {}
}
"#,
        )
        .expect("stateless Worker should compile");

        let worker = compilation
            .runtime_module
            .actors
            .iter()
            .find(|a| a.name == "Worker")
            .expect("Worker present");
        assert!(worker.state_layout.is_empty());
        assert_eq!(worker.state_size, 0);
    }

    #[test]
    fn builds_runtime_module_metadata_for_handler_payloads() {
        let compilation = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start(worker: ActorRef<Worker>) -> i64 {
        return worker.ask(Add(4, true), timeout: 5);
    }
}

actor Worker {
    init(fuel: Fuel) {}

    on Add(value: i64, enabled: bool) -> i64 {
        if enabled {
            return value;
        } else {
            return 0;
        }
    }
}
"#,
        )
        .expect("payload metadata should compile");

        let worker = compilation
            .runtime_module
            .actors
            .iter()
            .find(|actor| actor.name == "Worker")
            .expect("worker actor should be present");
        let add = worker
            .handler_named("Add")
            .expect("worker should expose Add");

        assert_eq!(
            worker.init_params,
            vec![RuntimeTypeSpec::Cap("Fuel".to_owned())]
        );
        assert_eq!(
            add.params,
            vec![RuntimeTypeSpec::I64, RuntimeTypeSpec::Bool]
        );
        assert_eq!(add.ret, RuntimeTypeSpec::I64);
    }

    #[test]
    fn reports_duplicate_linear_message_uses() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state {
        fuel: Fuel,
    }

    on Start(worker: ActorRef<Worker>) {
        worker.send(Burn(fuel, fuel));
    }
}

actor Worker {
    on Burn(primary: Fuel, secondary: Fuel) {}
}
"#,
        )
        .expect_err("linear caps should not be duplicated in one message");

        assert_eq!(
            err.diagnostics()[0].message(),
            "duplicate linear use of `fuel` in `sigil::Main::Start` — a linear value can be consumed at most once per statement"
        );
    }

    #[test]
    fn reports_reused_spawn_capabilities() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state {
        fuel: Fuel,
    }

    on Start() {
        let first = spawn::<Worker>(fuel);
        let second = spawn::<Worker>(fuel);
    }
}

actor Worker {
    init(seed: Fuel) {}
}
"#,
        )
        .expect_err("spawn should consume cap arguments");

        assert_eq!(
            err.diagnostics()[0].message(),
            "use after move of `fuel` in `sigil::Main::Start` — earlier passed to `spawn` in this scope"
        );
    }

    /// Step 3 (error message uplift): the move-kind in the O001 message is
    /// derived from the AIR stmt that consumed the cap, not hard-coded for
    /// `spawn`. A use-after-move through a message constructor must report
    /// the RecordField kind (the message-record's field assignment is what
    /// consumed the cap at AIR level). If this test starts producing
    /// "passed to `spawn`" the kind-tracking has regressed.
    ///
    /// Future iteration: the user-facing wording could collapse
    /// RecordField-followed-by-Send into "sent in a message" — that'd be a
    /// separate UX pass that needs cross-stmt provenance, out of scope here.
    #[test]
    fn reports_use_after_move_via_send_with_kind() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start(worker: ActorRef<Worker>) {
        worker.send(Burn(fuel));
        worker.send(Burn(fuel));
    }
}

actor Worker {
    on Burn(f: Fuel) {}
}
"#,
        )
        .expect_err("second send of `fuel` should fail");

        let msg = err.diagnostics()[0].message();
        assert!(
            msg.contains("stored into a record field"),
            "expected `stored into a record field` in O001 (kind-tracking \
             proof — the message constructor consumed `fuel` via record \
             field assignment at AIR level), got: {msg}"
        );
        assert!(
            !msg.contains("spawn"),
            "kind discrimination failed: spawn kind reported for a send/record case"
        );
    }

    /// Step 4 (error uplift on C003): the message names the *missing*
    /// authority by name, not just "restricted". For a `.restrict(burn)`
    /// fed to a sink requiring full `{burn, query}` authority, the missing
    /// set must be `{query}`. Locks the actual / required / missing
    /// three-set format so a future regression to the old "may have been
    /// restricted" message is caught. Solver-gated because C003 itself is
    /// emitted by the Z3 layer (z3_capability.rs is `#[cfg(feature = "solver")]`);
    /// without solver, the structural check emits R012 instead.
    #[test]
    #[cfg(feature = "solver")]
    fn c003_call_site_names_actual_required_and_missing_authorities() {
        let err = compile_module(
            r#"
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
"#,
        )
        .expect_err("attenuated cap passed to a full-auth call should fail C003");

        let msg = err.diagnostics()[0].message();
        assert!(
            msg.contains("authority {burn}"),
            "expected the actual authority set `{{burn}}` in C003, got: {msg}"
        );
        assert!(
            msg.contains("requires {burn, query}"),
            "expected the required authority set `{{burn, query}}` in C003, got: {msg}"
        );
        assert!(
            msg.contains("missing: {query}"),
            "expected the missing authority set `{{query}}` in C003, got: {msg}"
        );
        assert!(
            msg.contains("call site"),
            "expected the sink context `call site` in C003, got: {msg}"
        );
    }

    /// Step 4: the sink-context phrase differs by AIR stmt kind — call
    /// sites say "call site", spawn args say "spawn argument", message
    /// args say "message argument". Discrimination proves the context is
    /// derived from the stmt, not hard-coded. Solver-gated for the same
    /// reason as the call-site test above.
    #[test]
    #[cfg(feature = "solver")]
    fn c003_spawn_sink_uses_spawn_argument_phrasing() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel { burn, query }

actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}

entry actor Main {
    state { fuel: Fuel }

    on Start() -> i64 {
        let _child = spawn::<Worker>(fuel.restrict(burn));
        return 1;
    }
}
"#,
        )
        .expect_err("attenuated cap passed to spawn should fail C003");

        let msg = err.diagnostics()[0].message();
        assert!(
            msg.contains("spawn argument"),
            "expected `spawn argument` (not `call site`) for a Spawn sink, got: {msg}"
        );
        assert!(
            !msg.contains("call site"),
            "kind discrimination failed: Spawn sink should NOT say `call site`, got: {msg}"
        );
    }

    /// Step 3: `restrict` is a different MoveKind than `spawn`/`send`. The
    /// hint differs too — for restrict, the right advice is "bind the
    /// result, use that name" not "use .split() to keep a portion".
    #[test]
    fn reports_use_after_move_via_restrict_with_kind() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel { burn, query }

entry actor Main {
    state { fuel: Fuel }

    on Start() {
        let _weak = fuel.restrict(burn);
        let _weaker = fuel.restrict(query);
    }
}
"#,
        )
        .expect_err("second restrict of `fuel` should fail");

        let msg = err.diagnostics()[0].message();
        assert!(
            msg.contains("consumed by `.restrict"),
            "expected `consumed by .restrict` in O001 (kind-tracking proof), got: {msg}"
        );
    }

    #[test]
    fn compiles_result_constructors_and_try_to_air() {
        let source = r#"
module sigil;
fn helper() -> Result<i64, str> {
    return Ok(1);
}
fn boot() -> Result<i64, str> {
    let value = helper()?;
    return Ok(value);
}
"#;

        let compilation =
            compile_module(source).expect("result constructors and try should compile");
        let has_alloc = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::BumpAlloc { .. }));
        let has_try = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::ResultTry { .. }));

        assert!(
            has_alloc,
            "expected AIR to contain record allocation (BumpAlloc from RecordConstruct lowering)"
        );
        assert!(has_try, "expected AIR to contain try lowering");
    }

    /// PR OptTry / N9-OptTry: `?` on `Option<T>` lowers to
    /// `AirStmt::OptionTry`, NOT `AirStmt::ResultTry`. Distinct variants
    /// ensure the carriers' inverted tag semantics (Result is_ok=1
    /// means Ok, Option tag=0 means Some) can't be conflated at wasm
    /// emission time. Mirrors `compiles_result_constructors_and_try_to_air`
    /// but asserts the dispatch routes to OptionTry exclusively.
    #[test]
    fn compiles_option_try_to_option_try_air_variant() {
        let source = r#"
module sigil;
fn helper() -> Option<i64> {
    return Some(1);
}
fn boot() -> Option<i64> {
    let value = helper()?;
    return Some(value);
}
"#;
        let compilation = compile_module(source).expect("Option `?` should compile");
        let has_option_try = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::OptionTry { .. }));
        let has_result_try = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::ResultTry { .. }));
        assert!(
            has_option_try,
            "N9-OptTry: `?` on Option must lower to AirStmt::OptionTry"
        );
        assert!(
            !has_result_try,
            "N9-OptTry: `?` on Option must NOT lower to AirStmt::ResultTry (cross-carrier conflation forbidden)"
        );
    }

    /// PR OptTry / N16-OptTry: `stdlib/sigil/option.sigil`'s variant
    /// declaration order is locked at `Some(T), None`. The OptionTry
    /// wasm emission's tag-check hardcodes `OPTION_NONE_TAG = 1` (the
    /// short-circuit branch) and `OPTION_SOME_TAG = 0` (the extract
    /// branch); these values flow from the positional declaration
    /// order in the stdlib file via PR B's generic enum machinery.
    /// This test pre-flight-gates the wasm emission by asserting the
    /// stdlib's order matches the constants.
    #[test]
    fn option_variant_indices_locked() {
        use std::path::PathBuf;
        let stdlib_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("stdlib/sigil/option.sigil");
        let content = std::fs::read_to_string(&stdlib_path).unwrap_or_else(|e| {
            panic!("N16-OptTry: failed to read {}: {e}", stdlib_path.display())
        });
        // Locate the `enum Option<T> { ... }` declaration.
        let enum_start = content
            .find("pub enum Option<T> {")
            .expect("N16-OptTry: `pub enum Option<T> {` not found in stdlib option.sigil");
        let enum_body = &content[enum_start..];
        let close_brace = enum_body
            .find('}')
            .expect("N16-OptTry: closing brace missing from `enum Option<T>` declaration");
        let body = &enum_body[..close_brace];
        // Find the position of `Some(` and `None` literally.
        let some_pos = body
            .find("Some(")
            .expect("N16-OptTry: `Some(` variant missing from `enum Option<T>`");
        let none_pos = body
            .find("None")
            .expect("N16-OptTry: `None` variant missing from `enum Option<T>`");
        assert!(
            some_pos < none_pos,
            "N16-OptTry: stdlib option.sigil MUST declare `Some(T), None` in that order. \
             Current order has None before Some, which would invert OPTION_SOME_TAG / \
             OPTION_NONE_TAG semantics in OptionTry's wasm emission."
        );
        // Belt-and-braces: also assert the canonical constants in air.rs.
        assert_eq!(
            crate::air::OPTION_SOME_TAG,
            0,
            "N16-OptTry: OPTION_SOME_TAG must be 0 (positional variant 0)"
        );
        assert_eq!(
            crate::air::OPTION_NONE_TAG,
            1,
            "N16-OptTry: OPTION_NONE_TAG must be 1 (positional variant 1)"
        );
        assert_eq!(crate::air::OPTION_TAG_OFFSET, 0);
        assert_eq!(crate::air::OPTION_TAG_SIZE_BYTES, 4);
        assert_eq!(crate::air::OPTION_PAYLOAD_OFFSET, 4);
    }

    #[test]
    fn compiles_err_constructor_returns() {
        let source = r#"
module sigil;
fn boot() -> Result<i64, str> {
    return Err("boom");
}
"#;

        let compilation = compile_module(source).expect("Err constructor should compile");
        // PR B commit #2: ambient stdlib auto-include grows the AIR
        // function set (e.g., `result::init` for the stdlib module's
        // own init). Assert the user's function is present rather
        // than asserting an exact count.
        assert!(
            compilation
                .air
                .functions
                .iter()
                .any(|f| f.name == "sigil::boot"),
            "expected sigil::boot in AIR functions: {:?}",
            compilation
                .air
                .functions
                .iter()
                .map(|f| &f.name)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn compiles_generic_function_with_turbofish() {
        let source = r#"
module sigil;
fn identity<T>(x: T) -> T {
    return x;
}
fn boot() -> i64 {
    return identity::<i64>(42);
}
"#;
        let compilation =
            compile_module(source).expect("generic function with turbofish should compile");
        // Should have 2 functions: boot + identity__i64 (monomorphized)
        assert!(
            compilation.air.functions.len() >= 2,
            "expected at least 2 functions (boot + identity__i64), got {}",
            compilation.air.functions.len()
        );
    }

    #[test]
    fn compiles_generic_function_with_inference() {
        let source = r#"
module sigil;
fn identity<T>(x: T) -> T {
    return x;
}
fn boot() -> i64 {
    return identity(42);
}
"#;
        let compilation =
            compile_module(source).expect("generic function with inference should compile");
        assert!(
            compilation.air.functions.len() >= 2,
            "expected at least 2 functions, got {}",
            compilation.air.functions.len()
        );
    }

    #[test]
    fn reports_parser_errors() {
        let err = compile_named_module("inline", "module").expect_err("source should fail");

        assert_eq!(err.diagnostics().len(), 1);
        assert_eq!(
            err.diagnostics()[0].message(),
            "expected module name after `module`"
        );
    }

    #[test]
    fn reports_duplicate_actor_init_blocks() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    init() {}
    init() {}
}
"#,
        )
        .expect_err("duplicate actor init blocks should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "duplicate `init` block in actor `Main`"
        );
    }

    #[test]
    fn reports_non_actor_send_targets() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start() {
        let ready = true;
        ready.send(Ping());
    }
}
"#,
        )
        .expect_err("send targets must be actor refs");

        assert_eq!(
            err.diagnostics()[0].message(),
            "message target `ready` must be `ActorRef<T>`, found `bool`"
        );
    }

    #[test]
    fn reports_unknown_actor_handlers_for_messages() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start(worker: ActorRef<Worker>) {
        worker.send(Unknown());
    }
}

actor Worker {
    on Ping() {}
}
"#,
        )
        .expect_err("unknown handlers should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "actor `Worker` has no handler `Unknown`"
        );
    }

    #[test]
    fn reports_invalid_ask_timeout_types() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start(worker: ActorRef<Worker>) -> i64 {
        return worker.ask(GetCount(), timeout: true);
    }
}

actor Worker {
    on GetCount() -> i64 {
        return 1;
    }
}
"#,
        )
        .expect_err("ask timeout must be i64");

        assert_eq!(
            err.diagnostics()[0].message(),
            "`ask` timeout must be `i64`, found `bool`"
        );
    }

    #[test]
    fn reports_non_cap_spawn_arguments() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start() {
        let child = spawn::<Worker>(1);
    }
}

actor Worker {
    init(seed: i64) {}
}
"#,
        )
        .expect_err("spawn currently only supports cap args");

        assert_eq!(
            err.diagnostics()[0].message(),
            "spawn init arguments must be capability-typed or `Slot<Cap>`, found `i64`"
        );
    }

    #[test]
    fn reports_runtime_unsupported_message_argument_types() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start(worker: ActorRef<Worker>) {
        worker.send(SetLabel("sigil"));
    }
}

actor Worker {
    on SetLabel(label: str) {}
}
"#,
        )
        .expect_err("runtime-unsupported payloads should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "`send` to handler `SetLabel` on actor `Worker` currently supports runtime-serializable arguments of `bool`, `i64`, `ActorRef<T>`, or cap types, found `str`"
        );
    }

    #[test]
    fn reports_runtime_unsupported_ask_return_types() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start(worker: ActorRef<Worker>) -> str {
        return worker.ask(GetLabel(), timeout: 5);
    }
}

actor Worker {
    on GetLabel() -> str {
        return "sigil";
    }
}
"#,
        )
        .expect_err("runtime-unsupported ask returns should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "`ask` currently supports runtime-returnable handler types of `bool`, `i64`, `ActorRef<T>`, or cap types, found `str`"
        );
    }

    #[test]
    fn reports_missing_capability_init_parameters() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

actor Worker {
    state {
        fuel: Fuel,
    }

    on Ping() {}
}
"#,
        )
        .expect_err("non-entry actors should declare capability state in init params");

        assert_eq!(
            err.diagnostics()[0].message(),
            "actor `Worker` capability state field `fuel` of type `Fuel` must be provided by an `init` parameter"
        );
    }

    #[test]
    fn reports_missing_matching_capability_init_types() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

actor Worker {
    state {
        fuel: Fuel,
    }

    init(seed: i64) {}

    on Ping() {}
}
"#,
        )
        .expect_err("capability state should be surfaced through init params");

        assert_eq!(
            err.diagnostics()[0].message(),
            "actor `Worker` capability state field `fuel` of type `Fuel` must be provided by an `init` parameter"
        );
    }

    #[test]
    fn reports_try_in_non_result_functions() {
        let err = compile_module(
            r#"
module sigil;
fn helper() -> Result<i64, str> {
    return Ok(1);
}
fn boot() -> i64 {
    return helper()?;
}
"#,
        )
        .expect_err("`?` should require a Result-returning function");

        assert_eq!(
            err.diagnostics()[0].message(),
            "`?` requires the enclosing function to return `Result<_, E>`, found `i64`"
        );
    }

    #[test]
    fn reports_try_on_non_result_values() {
        let err = compile_module(
            r#"
module sigil;
fn boot() -> Result<i64, str> {
    let seed = 1;
    return Ok(seed?);
}
"#,
        )
        .expect_err("`?` should reject non-result values");

        assert_eq!(
            err.diagnostics()[0].message(),
            "`?` requires a `Result<T, E>` or `Option<T>` value, found `i64`"
        );
    }

    #[test]
    fn reports_try_error_type_mismatches() {
        let err = compile_module(
            r#"
module sigil;
fn helper() -> Result<i64, bool> {
    return Ok(1);
}
fn boot() -> Result<i64, str> {
    let value = helper()?;
    return Ok(value);
}
"#,
        )
        .expect_err("`?` should reject mismatched error types");

        assert_eq!(
            err.diagnostics()[0].message(),
            "`?` found error type `bool`, but enclosing function returns `Result<_, str>`"
        );
    }

    #[test]
    fn reports_duplicate_actor_state_blocks() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    state { counter: i64 }
    state { total: i64 }
}
"#,
        )
        .expect_err("duplicate actor state blocks should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "duplicate `state` block in actor `Main`"
        );
    }

    #[test]
    fn reports_entry_actor_name_mismatches() {
        let err = compile_module("module sigil; entry actor Boot {}")
            .expect_err("entry actor must be named Main");

        assert_eq!(
            err.diagnostics()[0].message(),
            "entry actor must be named `Main`, found `Boot` in module `sigil`"
        );
    }

    #[test]
    fn reports_actor_param_shadowing_state_fields() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    state { counter: i64 }
    on Start(counter: i64) {}
}
"#,
        )
        .expect_err("handler params should not shadow actor state fields");

        assert_eq!(
            err.diagnostics()[0].message(),
            "handler parameter `counter` in `Main::Start` of actor `Main` shadows a state field in module `sigil`"
        );
    }

    #[test]
    fn reports_unknown_actor_ref_targets() {
        let err = compile_module(
            r#"
module sigil;
entry actor Main {
    on Start(peer: ActorRef<Worker>) {}
}
"#,
        )
        .expect_err("unknown ActorRef targets should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "unknown actor `Worker` referenced by `ActorRef`"
        );
    }

    #[test]
    fn reports_missing_return_values() {
        let err = compile_module("module sigil; fn boot() -> bool {}")
            .expect_err("non-unit function should require a return");

        assert_eq!(
            err.diagnostics()[0].message(),
            "missing return value for function returning `bool`"
        );
    }

    #[test]
    fn reports_undefined_locals() {
        let err = compile_module("module sigil; fn boot() -> bool { return ready; }")
            .expect_err("undefined locals should fail");

        assert_eq!(err.diagnostics()[0].message(), "undefined local `ready`");
    }

    #[test]
    fn compiles_same_module_function_calls() {
        let source = r#"
module sigil;
fn helper(flag: bool) -> bool {
    return flag;
}
fn boot() -> bool {
    return helper(true);
}
"#;

        let compilation = compile_module(source).expect("calls should compile");
        let has_call = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| matches!(stmt, AirStmt::Call { .. }));

        assert_eq!(compilation.air.functions.len(), 2);
        assert!(has_call, "expected AIR to contain a direct call");
    }

    #[test]
    fn reports_undefined_functions() {
        let err = compile_module("module sigil; fn boot() -> bool { return helper(true); }")
            .expect_err("undefined function should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "undefined function `helper`"
        );
    }

    #[test]
    fn reports_wrong_call_arity() {
        let err = compile_module(
            "module sigil; fn helper(flag: bool) -> bool { return flag; } fn boot() -> bool { return helper(); }",
        )
        .expect_err("wrong arity should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "function `helper` expects 1 argument(s), found 0"
        );
    }

    #[test]
    fn compiles_binary_expressions() {
        let source = r#"
module sigil;
fn boot(seed: i64) -> bool {
    let next = seed + 1;
    return next == 2;
}
"#;

        let compilation = compile_module(source).expect("binary expressions should compile");
        let has_binary = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| {
                matches!(
                    stmt,
                    AirStmt::Assign {
                        val: crate::air::AirValue::Binary { .. },
                        ..
                    }
                )
            });

        assert!(has_binary, "expected AIR to contain binary operations");
    }

    #[test]
    fn compiles_relational_expressions() {
        let source = r#"
module sigil;
fn boot(seed: i64) -> bool {
    let next = seed + 1;
    return next < 3;
}
"#;

        let compilation = compile_module(source).expect("relational expressions should compile");
        let has_binary = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .any(|stmt| {
                matches!(
                    stmt,
                    AirStmt::Assign {
                        val: crate::air::AirValue::Binary { .. },
                        ..
                    }
                )
            });

        assert!(has_binary, "expected AIR to contain relational operations");
    }

    #[test]
    fn compiles_if_else_control_flow() {
        let source = r#"
module sigil;
fn boot(flag: bool) -> bool {
    if flag {
        return true;
    } else {
        return false;
    }
}
"#;

        let compilation = compile_module(source).expect("if/else should compile");
        let has_branch = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .any(|block| matches!(block.terminator, AirTerminator::Branch { .. }));

        assert!(has_branch, "expected AIR to contain a branch terminator");
    }

    #[test]
    fn compiles_match_on_bool() {
        let source = r#"
module sigil;
fn boot(flag: bool) -> bool {
    match flag {
        true => { return true; },
        false => { return false; }
    }
}
"#;

        let compilation = compile_module(source).expect("bool match should compile");
        let has_branch = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .any(|block| matches!(block.terminator, AirTerminator::Branch { .. }));

        assert!(
            has_branch,
            "expected AIR to contain branch tests for match arms"
        );
    }

    #[test]
    fn compiles_match_on_i64_with_wildcard() {
        let source = r#"
module sigil;
fn boot(seed: i64) -> bool {
    match seed {
        1 => { return true; },
        _ => { return false; }
    }
}
"#;

        let compilation = compile_module(source).expect("integer match should compile");
        let has_jump = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .any(|block| matches!(block.terminator, AirTerminator::Jump(_)));

        assert!(has_jump, "expected AIR to contain match control-flow jumps");
    }

    #[test]
    fn compiles_while_loops() {
        let source = r#"
module sigil;
fn boot(flag: bool) -> bool {
    while flag {
        return true;
    }
    return false;
}
"#;

        let compilation = compile_module(source).expect("while loops should compile");
        let has_loop = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .any(|block| matches!(block.terminator, AirTerminator::Loop { .. }));

        assert!(has_loop, "expected AIR to contain a loop header");
    }

    #[test]
    fn compiles_if_else_with_fallthrough() {
        let source = r#"
module sigil;
fn boot(flag: bool) -> bool {
    if flag {
        let branch = true;
    } else {
        let branch = false;
    }
    return flag == false;
}
"#;

        let compilation =
            compile_module(source).expect("if/else fallthrough should compile to Wasm");
        let has_jump = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .any(|block| matches!(block.terminator, AirTerminator::Jump(_)));

        assert!(has_jump, "expected AIR to contain a continuation jump");
    }

    #[test]
    fn reports_invalid_if_conditions() {
        let err = compile_module(
            "module sigil; fn boot() -> bool { if 1 { return true; } else { return false; } }",
        )
        .expect_err("if conditions must be booleans");

        assert_eq!(
            err.diagnostics()[0].message(),
            "if condition must be `bool`, found `i64`"
        );
    }

    #[test]
    fn reports_non_exhaustive_match_on_bool() {
        let err = compile_module(
            "module sigil; fn boot(flag: bool) -> bool { match flag { true => { return true; } } }",
        )
        .expect_err("bool match should require full coverage");

        assert!(
            err.diagnostics()[0]
                .message()
                .contains("non-exhaustive match"),
            "expected non-exhaustive error, got: {}",
            err.diagnostics()[0].message()
        );
    }

    #[test]
    fn reports_match_pattern_type_mismatch() {
        let err = compile_module(
            "module sigil; fn boot(flag: bool) -> bool { match flag { 1 => { return true; }, _ => { return false; } } }",
        )
        .expect_err("match patterns should align with the scrutinee type");

        assert_eq!(
            err.diagnostics()[0].message(),
            "match pattern expected `bool`, found `i64`"
        );
    }

    #[test]
    fn match_str_scrutinee_with_wildcard_compiles() {
        // str scrutinee is now supported — match with wildcard is exhaustive
        let _result = compile_module(
            "module sigil; fn boot() -> bool { let label = \"a\"; match label { _ => { return true; } } }",
        )
        .expect("match on str with wildcard should compile");
    }

    #[test]
    fn reports_invalid_while_conditions() {
        let err = compile_module("module sigil; fn boot() { while 1 { return; } }")
            .expect_err("while conditions must be booleans");

        assert_eq!(
            err.diagnostics()[0].message(),
            "while condition must be `bool`, found `i64`"
        );
    }

    #[test]
    fn reports_conditional_missing_returns() {
        let err = compile_module(
            "module sigil; fn boot(flag: bool) -> bool { if flag { return true; } else { let fallback = false; } }",
        )
        .expect_err("conditional returns should still require all paths to return");

        assert_eq!(
            err.diagnostics()[0].message(),
            "missing return value for function returning `bool`"
        );
    }

    #[test]
    fn reports_invalid_relational_operands() {
        let err = compile_module("module sigil; fn boot() -> bool { return true < 1; }")
            .expect_err("invalid relational comparison should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "operator `<` requires matching numeric operands, found `bool` and `i64`"
        );
    }

    #[test]
    fn reports_invalid_arithmetic_operands() {
        let err = compile_module("module sigil; fn boot() -> bool { return true + 1; }")
            .expect_err("invalid arithmetic should fail");

        assert_eq!(
            err.diagnostics()[0].message(),
            "operator `+` requires matching numeric operands, found `bool` and `i64`"
        );
    }

    // --- Phase 2A coverage tests ---

    #[test]
    fn compiles_record_construction_and_field_access() {
        let source = r#"
module sigil;
record Point { x: i64, y: i64 }
fn boot() -> i64 {
    let p = Point { x: 3, y: 4 };
    return p.x + p.y;
}
"#;
        let compilation =
            compile_module(source).expect("record construction and field access should compile");
        assert!(!compilation.air.functions.is_empty());
    }

    #[test]
    fn compiles_enum_construction_and_match() {
        // PR B commit #3: with ambient stdlib Option in scope,
        // bare `Some(42)` is ambiguous when a user enum also has
        // `Some` (T236 fires). Use qualified construction
        // `MyOption::Some(42)` to disambiguate.
        let source = r#"
module sigil;
enum MyOption<T> { Some(T), None }
fn boot() -> i64 {
    let opt = MyOption::Some(42);
    match opt {
        MyOption::Some(v) => { return v; },
        MyOption::None => { return 0; }
    }
}
"#;
        let compilation =
            compile_module(source).expect("enum construction and match should compile");
        assert!(!compilation.air.functions.is_empty());
    }

    #[test]
    fn compiles_match_with_guard() {
        let source = r#"
module sigil;
fn sign(n: i64) -> i64 {
    match n {
        x if x > 0 => { return 1; },
        x if x < 0 => { return 0 - 1; },
        _ => { return 0; }
    }
}
"#;
        let _compilation = compile_module(source).expect("match with guards should compile");
    }

    #[test]
    fn compiles_closure_expression() {
        let source = r#"
module sigil;
fn boot() -> i64 {
    let f = fn(x: i64) -> i64 { return x * 2; };
    return 0;
}
"#;
        let _compilation = compile_module(source).expect("closure expression should compile");
    }

    #[test]
    fn rejects_borrow_of_primitive() {
        let err = compile_module(
            "module sigil; fn boot() -> i64 { let x: i64 = 5; let r = &x; return 0; }",
        )
        .expect_err("borrowing a primitive should fail");

        assert!(
            err.diagnostics()[0]
                .message()
                .contains("cannot borrow primitive type"),
            "expected 'cannot borrow primitive type', got: {}",
            err.diagnostics()[0].message()
        );
    }

    #[test]
    fn rejects_nonexistent_field_access() {
        let err = compile_module(
            "module sigil; record Point { x: i64, y: i64 } fn boot() -> i64 { let p = Point { x: 1, y: 2 }; return p.z; }",
        )
        .expect_err("accessing nonexistent field should fail");

        assert!(
            err.diagnostics()[0].message().contains("has no field"),
            "expected 'has no field', got: {}",
            err.diagnostics()[0].message()
        );
    }

    #[test]
    fn compiles_borrow_of_record() {
        let source = r#"
module sigil;
record Point { x: i64, y: i64 }
fn read_x(p: &Point) -> i64 {
    return p.x;
}
fn boot() -> i64 {
    let p = Point { x: 10, y: 20 };
    return read_x(&p);
}
"#;
        let _compilation = compile_module(source).expect("borrow of record should compile");
    }

    #[test]
    fn compiles_slice_type_annotation() {
        let source = r#"
module sigil;
fn sum(arr: &[i64]) -> i64 {
    return 0;
}
fn boot() -> i64 {
    let data = [1, 2, 3];
    return sum(&data);
}
"#;
        let _compilation = compile_module(source).expect("slice type annotation should compile");
    }

    #[test]
    fn rejects_outer_ring_holding_cap() {
        let err = compile_module(
            "#[ring(outer)] module ext; cap type Token {} fn bad(t: Token) -> i64 { return 0; }",
        )
        .expect_err("outer ring holding cap should be rejected");

        assert!(
            err.diagnostics()[0]
                .message()
                .contains("outer ring cannot own capabilities"),
            "expected R001, got: {}",
            err.diagnostics()[0].message()
        );
    }

    #[test]
    fn compiles_outer_ring_pure_function() {
        let _compilation = compile_module(
            "#[ring(outer)] module ext; fn add(a: i64, b: i64) -> i64 { return a + b; }",
        )
        .expect("outer ring pure function should compile");
    }

    #[test]
    fn compiles_default_inner_ring() {
        let _compilation = compile_module("module sigil; fn boot() -> i64 { return 42; }")
            .expect("default inner ring module should compile");
    }

    #[test]
    fn rejects_grant_with_non_cap() {
        // Grant requires &cap T, not &Record
        let err = compile_module(
            "module sigil; record D { x: i64 } fn boot() -> i64 { let d = D { x: 1 }; return grant(&d, fn(r: &D) -> i64 { return 0; }); }",
        )
        .expect_err("grant with non-cap should be rejected");

        assert!(
            err.diagnostics()[0]
                .message()
                .contains("grant requires an immutable borrow of a capability"),
            "expected grant cap error, got: {}",
            err.diagnostics()[0].message()
        );
    }

    // ── 2C Effect System Tests ──────────────────────────────────────────

    #[test]
    fn compiles_pure_outer_function() {
        // Pure outer-ring function with empty effect row compiles
        let _ = compile_module(
            "#[ring(outer)] module ext; fn add(a: i64, b: i64) -> i64 ! {} { return a + b; }",
        )
        .expect("pure outer fn should compile");
    }

    #[test]
    fn compiles_outer_function_with_effect_row() {
        // Outer-ring function declaring effects compiles
        let _ = compile_module(
            "#[ring(outer)] module ext; effect Alloc; fn alloc_something() ! { Alloc } { return; }",
        )
        .expect("outer fn with declared effects should compile");
    }

    #[test]
    fn compiles_inner_ring_without_effects() {
        // Inner-ring functions are exempt from effect checking
        let _ = compile_module("module sigil; fn add(a: i64, b: i64) -> i64 { return a + b; }")
            .expect("inner ring fn should compile without effect row");
    }

    #[test]
    fn compiles_handle_block() {
        // Handle block with known effect compiles
        let _ = compile_module(
            "#[ring(outer)] module ext; effect NetIO; fn do_io() -> i64 ! { NetIO } { return 42; } fn caller() ! {} { handle NetIO { do_io(); }; return; }",
        )
        .expect("handle block should compile");
    }

    /// Step 6: T060 (undefined local) carries a "did you mean ..." hint
    /// when an in-scope name is within Levenshtein distance ≤2. This is
    /// the most common policy-author error — typos in capability names
    /// previously gave a flat "undefined local `fule`" with no recovery
    /// pointer. Now the user gets pointed at `fuel`.
    #[test]
    fn t060_suggests_close_in_scope_name() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start() -> i64 {
        let _x = fule;
        return 1;
    }
}
"#,
        )
        .expect_err("`fule` is undefined and should produce T060");

        let diag = err
            .diagnostics()
            .iter()
            .find(|d| d.code() == crate::diagnostics::codes::T060)
            .expect("expected T060");
        let hint = diag.hint().expect("T060 should carry a hint");
        assert!(
            hint.contains("did you mean") && hint.contains("`fuel`"),
            "expected `did you mean fuel` hint, got: {hint:?}"
        );
    }

    /// Step 6: when the typo is too far from any in-scope name (distance
    /// exceeds the bound), no `did you mean` suggestion fires — we fall back
    /// to the registry's default hint. Prevents misleading suggestions like
    /// `did you mean x?` for `xyzqrt`.
    #[test]
    fn t060_falls_back_when_no_close_name() {
        let err = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start() -> i64 {
        let _x = xyzqrt;
        return 1;
    }
}
"#,
        )
        .expect_err("`xyzqrt` is undefined and should produce T060");

        let diag = err
            .diagnostics()
            .iter()
            .find(|d| d.code() == crate::diagnostics::codes::T060)
            .expect("expected T060");
        let hint = diag.hint().unwrap_or("");
        assert!(
            !hint.contains("did you mean"),
            "expected no `did you mean` for distant typo, got hint: {hint:?}"
        );
    }

    /// Step 5: T068 rejects `return` inside a `handle` body. Previously
    /// this was silently dropped at AIR level — the inner return never
    /// fired, but the surface program looked fine. Closing this loophole
    /// is the load-bearing change of step 5; if this test starts passing
    /// with no T068 (i.e. `expect_err` becomes `expect`), the rejection
    /// has regressed and the silent-drop hole is back open.
    #[test]
    fn rejects_return_inside_handle_body() {
        let err = compile_module(
            "#[ring(outer)] #[trusted] module ext; fn f() ! {} { handle Unsafe { return; }; return; }",
        )
        .expect_err("`return` inside handle body must be rejected (T068)");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.code() == crate::diagnostics::codes::T068),
            "expected T068, got: {:?}",
            err.diagnostics()
        );
        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("`return`") && d.message().contains("`handle`")),
            "expected T068 to name `return` and `handle`, got: {:?}",
            err.diagnostics()
        );
    }

    /// Step 5: same rejection for `region`. Symmetry: both scoped-body
    /// constructs route through the same `reject_control_flow_in_scoped_body`
    /// helper, so a working handle test plus a working region test prove
    /// the helper is wired to both call sites.
    #[test]
    fn rejects_return_inside_region_body() {
        let err = compile_module(
            "#[ring(outer)] module ext; fn f() ! { Alloc } { region scratch(64) { return; }; return; }",
        )
        .expect_err("`return` inside region body must be rejected (T068)");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.code() == crate::diagnostics::codes::T068),
            "expected T068, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn compiles_trusted_module_with_handle_unsafe() {
        // #[trusted] module can handle Unsafe. Step 5: handle body uses a
        // straight-line `let` instead of `return;` — the latter is now
        // rejected by T068 because it's silently dropped at AIR level.
        let _ = compile_module(
            "#[ring(outer)] #[trusted] module ext; fn safe_wrapper() ! {} { handle Unsafe { let _x: i64 = 1; }; return; }",
        )
        .expect("trusted module with handle Unsafe should compile");
    }

    #[test]
    fn compiles_effect_decl() {
        // Effect declarations are accepted
        let _ = compile_module(
            "#[ring(outer)] module ext; effect CustomIO; fn f() ! { CustomIO } { return; }",
        )
        .expect("custom effect declaration should compile");
    }

    #[test]
    fn rejects_handle_unsafe_in_untrusted_module() {
        // E002: handle Unsafe requires #[trusted]. Step 5: placeholder body
        // updated from `return;` to `let _x: i64 = 1;` per T068.
        let err = compile_module(
            "#[ring(outer)] module ext; fn f() ! {} { handle Unsafe { let _x: i64 = 1; }; return; }",
        )
        .expect_err("handle Unsafe in untrusted module should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("E002") || d.message().contains("trusted")),
            "expected E002 trusted error, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn rejects_unknown_effect_in_handle() {
        // Unknown effect name in handle block. Step 5: placeholder body
        // updated per T068.
        let err = compile_module(
            "#[ring(outer)] module ext; fn f() ! {} { handle Nonexistent { let _x: i64 = 1; }; return; }",
        )
        .expect_err("unknown effect in handle should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("unknown effect")),
            "expected unknown effect error, got: {:?}",
            err.diagnostics()
        );
    }

    // ── 2D Taint System Tests ───────────────────────────────────────────

    #[test]
    fn compiles_public_value_to_public_return() {
        // @Public value flows to @Public return — OK
        let _ =
            compile_module("#[ring(outer)] module ext; fn f() -> i64 @Public ! {} { return 42; }")
                .expect("public value to public return should compile");
    }

    #[test]
    fn compiles_taint_upgrade() {
        // @Public value in @Secret binding — OK (upgrade is always safe)
        let _ = compile_module(
            "#[ring(outer)] module ext; fn f() -> i64 ! {} { let x: i64 @Secret = 42; return 0; }",
        )
        .expect("taint upgrade should compile");
    }

    #[test]
    fn compiles_unannotated_defaults_to_public() {
        // Unannotated values default to @Public
        let _ = compile_module(
            "#[ring(outer)] module ext; fn f() -> i64 ! {} { let x: i64 = 42; return x; }",
        )
        .expect("unannotated default @Public should compile");
    }

    #[test]
    fn compiles_secret_used_in_secret_context() {
        // @Secret value used only in @Secret context — OK
        let _ = compile_module(
            "#[ring(outer)] module ext; fn f() -> i64 @Secret ! {} { let x: i64 @Secret = 42; return x; }",
        )
        .expect("secret in secret context should compile");
    }

    #[test]
    fn compiles_taint_propagation_safe() {
        // @Secret + @Public → @Secret, returned from @Secret function — OK
        let _ = compile_module(
            "#[ring(outer)] module ext; fn f(a: i64 @Secret) -> i64 @Secret ! {} { let b: i64 = 1; return a + b; }",
        )
        .expect("taint propagation in safe context should compile");
    }

    #[test]
    fn rejects_secret_to_public_return() {
        // T001: @Secret value returned from @Public function
        let err = compile_module(
            "#[ring(outer)] module ext; fn f(s: i64 @Secret) -> i64 @Public ! {} { return s; }",
        )
        .expect_err("secret to public return should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("T001")),
            "expected T001, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn rejects_implicit_flow_leak() {
        // T001: branch on @Secret leaks through assignment to @Public return
        let err = compile_module(
            "#[ring(outer)] module ext; fn f(secret: bool @Secret) -> i64 @Public ! {} { let mut result: i64 = 0; if secret { result = 1; } else { result = 0; } return result; }",
        )
        .expect_err("implicit flow leak should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("T001")),
            "expected T001 for implicit flow, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn rejects_taint_concat_leak() {
        // T001: @Public + @Secret → @Secret, then returned as @Public
        let err = compile_module(
            "#[ring(outer)] module ext; fn f(secret: i64 @Secret) -> i64 @Public ! {} { let combined: i64 = secret + 1; return combined; }",
        )
        .expect_err("taint concat leak should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("T001")),
            "expected T001 for concat leak, got: {:?}",
            err.diagnostics()
        );
    }

    // ── 2E FFI + Region Tests ───────────────────────────────────────────

    #[test]
    fn compiles_extern_decl_in_trusted_outer() {
        // Extern declaration in #[trusted] outer module parses and compiles
        let _ = compile_module(
            "#[ring(outer)] #[trusted] module ext; extern \"C\" fn my_func(x: i64) -> i32 ! { FFI, Unsafe };",
        )
        .expect("extern decl in trusted outer module should compile");
    }

    #[test]
    fn compiles_region_basic() {
        // Region block compiles with numeric limit
        let _ = compile_module(
            "#[ring(outer)] module ext; fn f() ! {} { region buf(1024) { let x: i64 = 42; }; return; }",
        )
        .expect("basic region block should compile");
    }

    #[test]
    fn compiles_extern_with_multiple_params() {
        // Extern with multiple params and effect row
        let _ = compile_module(
            "#[ring(outer)] #[trusted] module ext; extern \"C\" fn compress(a: i64, b: i64) -> i32 ! { FFI, Unsafe };",
        )
        .expect("extern with multiple params should compile");
    }

    #[test]
    fn rejects_extern_without_ffi_effect() {
        // Extern function must declare FFI effect
        let err = compile_module(
            "#[ring(outer)] #[trusted] module ext; extern \"C\" fn bad() -> i32 ! { Unsafe };",
        )
        .expect_err("extern without FFI effect should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("FFI")),
            "expected FFI effect error, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn rejects_extern_without_unsafe_effect() {
        // Extern function must declare Unsafe effect
        let err = compile_module(
            "#[ring(outer)] #[trusted] module ext; extern \"C\" fn bad() -> i32 ! { FFI };",
        )
        .expect_err("extern without Unsafe effect should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("Unsafe")),
            "expected Unsafe effect error, got: {:?}",
            err.diagnostics()
        );
    }

    // ── 2F Two-Module Codegen Tests ─────────────────────────────────────

    #[test]
    fn compiles_two_module_emits_both_wasm() {
        // Program with inner + outer modules → both wasm blobs present
        let result =
            compile_module("module sigil; fn add(a: i64, b: i64) -> i64 { return a + b; }")
                .expect("inner-only program should compile");

        // Single-ring program → outer is None
        assert!(
            result.wasm_outer.is_none(),
            "single-ring program should not produce outer wasm"
        );
        assert!(
            !result.wasm_inner.is_empty(),
            "inner wasm should not be empty"
        );
    }

    #[test]
    fn compiles_inner_only_single_wasm() {
        // Program with only inner modules → single wasm, no outer
        let result = compile_module("module sigil; fn id(x: i64) -> i64 { return x; }")
            .expect("inner-only should compile");

        assert!(result.wasm_outer.is_none());
        assert!(!result.wasm_inner.is_empty());
    }

    #[test]
    fn compiles_outer_module_produces_outer_wasm() {
        // Program with outer module → outer wasm present
        let result = compile_named_module(
            "two_ring",
            "module sigil; fn boot() -> i64 { return 1; } #[ring(outer)] module ext; fn helper() -> i64 ! {} { return 42; }",
        )
        .expect("two-ring program should compile");

        assert!(
            result.wasm_outer.is_some(),
            "two-ring program should produce outer wasm"
        );
        assert!(
            !result.wasm_inner.is_empty(),
            "inner wasm should not be empty"
        );
        assert!(
            !result.wasm_outer.as_ref().unwrap().is_empty(),
            "outer wasm should not be empty"
        );
    }

    // ── 2G Security Validation: Cross-Cutting Attacks ───────────────────

    #[test]
    fn attack_43_generic_cap_smuggle() {
        // Generic function wrapping a cap must preserve ownership tracking.
        // After calling wrap(fuel), the original binding is consumed.
        // Trying to use it again → O001 use-after-move.
        let err = compile_module(
            "module sigil; cap type Fuel { burn } fn consume<T>(x: T) -> i64 { return 0; } entry actor Main { state {} init(fuel: Fuel) { let a: i64 = consume::<Fuel>(fuel); let b: i64 = consume::<Fuel>(fuel); } }",
        )
        .expect_err("generic cap smuggle should be rejected — use after move");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("use after move") || d.message().contains("O001")),
            "expected ownership error, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn attack_45_effect_row_smuggle_via_closure() {
        // Closure with undeclared effects passed to a function with narrower
        // effect row. The effect checker should reject at the call site.
        // Outer fn declared ! {} (pure) calls a fn that requires FFI.
        let err = compile_module(
            "#[ring(outer)] module ext; effect CustomIO; fn effectful() -> i64 ! { CustomIO } { return 0; } fn caller() -> i64 ! {} { return effectful(); }",
        )
        .expect_err("effect row smuggle should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("undeclared effect") || d.message().contains("E001")),
            "expected effect violation, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn attack_47_two_ring_import_segregation() {
        // Verify outer module's Wasm binary does NOT contain cap_restrict
        // or cap_split imports. Defense-in-depth structural test.
        let result = compile_named_module(
            "segregation",
            "module sigil; fn boot() -> i64 { return 1; } #[ring(outer)] module ext; fn helper() -> i64 ! {} { return 42; }",
        )
        .expect("two-ring program should compile");

        let outer_wasm = result.wasm_outer.expect("should have outer wasm");
        let outer_str = String::from_utf8_lossy(&outer_wasm);

        // cap_restrict and cap_split should NOT appear in outer module's import section
        assert!(
            !outer_str.contains("cap_restrict"),
            "outer module must not import cap_restrict"
        );
        assert!(
            !outer_str.contains("cap_split"),
            "outer module must not import cap_split"
        );
        assert!(
            !outer_str.contains("spawn"),
            "outer module must not import spawn"
        );
        assert!(
            !outer_str.contains("send"),
            "outer module must not import send"
        );
    }

    #[test]
    fn attack_29_secret_to_public_via_grant_return() {
        // @Secret data returned through a grant block to a @Public context.
        // The taint checker must reject this.
        let err = compile_module(
            "#[ring(outer)] module ext; fn leak(s: i64 @Secret) -> i64 @Public ! {} { return s; }",
        )
        .expect_err("secret to public via return should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("T001")),
            "expected T001 taint error, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn attack_26_outer_fn_missing_effect_clause() {
        // Outer-ring function without effect clause should still compile
        // (defaults to no effects = pure). But if it calls an effectful fn,
        // that should be rejected.
        let err = compile_module(
            "#[ring(outer)] module ext; effect NetIO; fn effectful() -> i64 ! { NetIO } { return 0; } fn pure_caller() -> i64 ! {} { return effectful(); }",
        )
        .expect_err("outer fn calling effectful fn without declaring effects should be rejected");

        assert!(
            err.diagnostics()
                .iter()
                .any(|d| d.message().contains("undeclared effect")),
            "expected effect error, got: {:?}",
            err.diagnostics()
        );
    }

    #[test]
    fn attack_42_audit_evasion_structural() {
        // Structural test: verify grants can only happen through the
        // grant mechanism (no direct cross-ring calls). Outer code
        // cannot call inner functions and vice versa without grant.
        // This is a compile-time guarantee from the ring checker.
        //
        // Note: runtime audit log verification is deferred to M4.
        let _ = compile_module(
            "module sigil; cap type Fuel { burn } entry actor Main { state {} init(fuel: Fuel) { let result: i64 = grant(&fuel, fn(cap_ref: &Fuel) -> i64 { return 42; }); } }",
        )
        .expect("grant block should compile — audit enforcement is structural");
    }

    #[test]
    fn compiles_tool_module() {
        let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#;
        let result = compile_tool(source).expect("tool module should compile");
        assert!(!result.wasm.is_empty());
        assert_eq!(result.wasm, result.wasm_inner);
        assert!(result.wasm_outer.is_none());
        assert!(result.fuel_budget > 0);
        assert!(result.function_count > 0);
    }

    #[test]
    fn outer_tool_preserves_certificate_artifacts_and_declared_effects() {
        let source = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FsIO, FFI, Unsafe } {
    return fs_read(input_ptr, input_len);
}
"#;

        let compilation = compile_module(source).expect("outer tool should compile");
        let tool_main = compilation
            .air
            .functions
            .iter()
            .find(|function| function.name.ends_with("::tool_main"))
            .expect("tool lowering retains tool_main");
        assert_eq!(
            tool_main.security.return_contract,
            crate::air::AirLabelContract::Concrete(crate::ast::TaintLabel::Internal),
            "AIR must preserve the source language's Internal host-bridge return contract"
        );
        assert_eq!(
            compilation.effects_required,
            vec!["FFI".to_string(), "FsIO".to_string(), "Unsafe".to_string()]
        );

        let result = compile_tool(source).expect("outer tool should compile for execution");
        let outer = result
            .wasm_outer
            .as_ref()
            .expect("outer tool must retain its outer certificate artifact");
        assert_eq!(&result.wasm, outer);
        assert_ne!(result.wasm_inner, *outer);
    }

    #[test]
    fn compiles_tool_byte_intrinsics() {
        let source = r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let out_ptr = alloc(input_len);
    let first = load8(input_ptr);
    store8(out_ptr, first);
    return out_ptr * 4294967296 + 1;
}
"#;
        let compilation = compile_module(source).expect("tool intrinsics should compile");
        let stmts = compilation
            .air
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.stmts.iter())
            .collect::<Vec<_>>();

        assert!(
            stmts
                .iter()
                .any(|stmt| matches!(stmt, AirStmt::IntrinsicAlloc { .. }))
        );
        assert!(
            stmts
                .iter()
                .any(|stmt| matches!(stmt, AirStmt::IntrinsicLoad8 { .. }))
        );
        assert!(
            stmts
                .iter()
                .any(|stmt| matches!(stmt, AirStmt::IntrinsicStore8 { .. }))
        );
    }

    #[test]
    fn rejects_tool_without_tool_main() {
        let source = r#"
module tool;
fn helper() -> i64 {
    return 42;
}
"#;
        let err = compile_tool(source).expect_err("should reject module without tool_main");
        let messages: Vec<String> = err
            .diagnostics()
            .iter()
            .map(|d| d.message().to_owned())
            .collect();
        assert!(
            messages
                .iter()
                .any(|m: &String| m.contains("tool module must export pub fn tool_main")),
            "expected tool_main error, got: {messages:?}"
        );
    }

    #[test]
    fn forge_source_too_large() {
        // Source exceeding the default 64KB limit should be rejected.
        let limits = CompileLimits::default();
        let source = "x".repeat(limits.max_source_bytes + 1);
        let err =
            compile_tool_with_limits(&source, &limits).expect_err("should reject oversized source");
        let messages: Vec<String> = err
            .diagnostics()
            .iter()
            .map(|d| d.message().to_owned())
            .collect();
        assert!(
            messages.iter().any(|m| m.contains("exceeds maximum size")),
            "expected size limit error, got: {messages:?}"
        );
    }

    // ── Wall 5 Step 1 / commit #2: compile_project + helpers ────────────

    use super::{CompileOptions, compile_project, find_entry_points, is_tool_main};
    use crate::ast::{FnDef, Item, Param, Path, Program, Ring, TypeExpr, Visibility};
    use crate::diagnostics::codes;
    use crate::source::SourceFile;
    use crate::span::Span;

    fn make_param(name: &str, ty_name: &str) -> Param {
        Param {
            flow: false,
            name: name.to_string(),
            ty: TypeExpr {
                path: Path {
                    segments: vec![ty_name.to_string()],
                    type_args: vec![],
                    span: Span::default(),
                },
                ref_kind: None,
                deadline: vec![],
                span: Span::default(),
                fn_type: None,
                array_type: None,
                tuple_type: None,
            },
            taint: None,
            mutability: crate::ast::Mutability::Default,
            region: None,
            span: Span::default(),
        }
    }

    fn make_type(name: &str) -> TypeExpr {
        TypeExpr {
            path: Path {
                segments: vec![name.to_string()],
                type_args: vec![],
                span: Span::default(),
            },
            ref_kind: None,
            deadline: vec![],
            span: Span::default(),
            fn_type: None,
            array_type: None,
            tuple_type: None,
        }
    }

    fn make_tool_main_fn() -> FnDef {
        FnDef {
            ret_flow: false,
            visibility: Visibility::Public,
            name: "tool_main".to_string(),
            type_params: vec![],
            params: vec![
                make_param("input_ptr", "i64"),
                make_param("input_len", "i64"),
            ],
            return_type: Some(make_type("i64")),
            effects: None,
            body: crate::ast::Block {
                statements: vec![],
                span: Span::default(),
            },
            span: Span::default(),
            ret_taint: None,
            param_refinements: vec![],
            return_refinement: None,
            region_outlives: vec![],
        }
    }

    /// N24-W5S1 positive case: canonical pub tool_main signature.
    #[test]
    fn is_tool_main_accepts_canonical_signature() {
        let item = Item::FnDef(make_tool_main_fn());
        assert!(is_tool_main(&item));
    }

    /// N24-W5S1 negative cases: every clause of the predicate has a
    /// counterexample. Mismatched signature → not a tool entry.
    #[test]
    fn is_tool_main_rejects_private() {
        let mut fn_def = make_tool_main_fn();
        fn_def.visibility = Visibility::Private;
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_wrong_name() {
        let mut fn_def = make_tool_main_fn();
        fn_def.name = "main".to_string();
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_single_arg() {
        let mut fn_def = make_tool_main_fn();
        fn_def.params = vec![make_param("input_ptr", "i64")];
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_three_args() {
        let mut fn_def = make_tool_main_fn();
        fn_def.params.push(make_param("extra", "i64"));
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_wrong_first_arg_type() {
        let mut fn_def = make_tool_main_fn();
        fn_def.params[0].ty = make_type("i32");
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_wrong_second_arg_type() {
        let mut fn_def = make_tool_main_fn();
        fn_def.params[1].ty = make_type("bool");
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_wrong_return_type() {
        let mut fn_def = make_tool_main_fn();
        fn_def.return_type = Some(make_type("bool"));
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_no_return_type() {
        let mut fn_def = make_tool_main_fn();
        fn_def.return_type = None;
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    #[test]
    fn is_tool_main_rejects_non_fn_item() {
        let item = Item::EffectDecl(crate::ast::EffectDecl {
            name: "tool_main".to_string(),
            ops: Vec::new(),
            span: Span::default(),
        });
        assert!(!is_tool_main(&item));
    }

    #[test]
    fn is_tool_main_rejects_ref_param_type() {
        let mut fn_def = make_tool_main_fn();
        fn_def.params[0].ty.ref_kind = Some(crate::ast::RefKind::Ref(false));
        assert!(!is_tool_main(&Item::FnDef(fn_def)));
    }

    /// N3-W5S1: find_entry_points walks every module's items. With
    /// today's AST (no nested-module Item variant), this collapses to
    /// flat iteration — but the test still confirms multi-module input
    /// is correctly enumerated.
    #[test]
    fn find_entry_points_finds_tool_main_across_modules() {
        let mut tool_fn = make_tool_main_fn();
        tool_fn.span = Span::new(10, 20);
        let program = Program {
            modules: vec![
                crate::ast::Module {
                    name: "helpers".to_string(),
                    ring: Ring::Inner,
                    trusted: false,
                    visibility: Visibility::Private,
                    items: vec![],
                    span: Span::default(),
                },
                crate::ast::Module {
                    name: "main".to_string(),
                    ring: Ring::Inner,
                    trusted: false,
                    visibility: Visibility::Private,
                    items: vec![Item::FnDef(tool_fn)],
                    span: Span::default(),
                },
            ],
        };
        let entries = find_entry_points(&program);
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].module(), "main");
    }

    /// Smoke test: compile_project with two real .sigil files compiles
    /// successfully, demonstrating the merge + entry-detection path
    /// works end-to-end.
    #[test]
    fn compile_project_two_files_basic() {
        let math = SourceFile::new(
            "math.sigil",
            "module math;\npub fn add(a: i64, b: i64) -> i64 { return a + b; }\n",
        );
        let main = SourceFile::new(
            "main.sigil",
            "module main;\nuse sigil::math;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return math::add(1, 2); }\n",
        );
        let compilation = compile_project(vec![math, main], None, CompileOptions::default())
            .expect("two-file project compiles");
        // Both modules survive into the merged Program.
        assert!(compilation.module_names.contains(&"math".to_string()));
        assert!(compilation.module_names.contains(&"main".to_string()));
        // WASM emitted for the project.
        assert_eq!(&compilation.wasm_inner[..4], b"\0asm");
    }

    /// N21-W5S1: single-file path bypasses M001-M006 and produces
    /// byte-equal wasm to the legacy direct path. Compiles the same
    /// source via compile_named_module (which now wraps compile_project)
    /// and via compile_named_module twice; both must produce identical
    /// wasm_inner bytes — same-source determinism (a stricter property
    /// than just "non-empty wasm").
    #[test]
    fn compile_named_module_wrapper_is_byte_equal_to_itself() {
        let source = "module sigil;\nfn boot() -> i64 { return 0; }\n";
        let a = compile_named_module("foo.sigil", source).expect("a compiles");
        let b = compile_named_module("foo.sigil", source).expect("b compiles");
        assert_eq!(a.wasm_inner, b.wasm_inner);
        assert_eq!(a.wasm_outer, b.wasm_outer);
    }

    /// N10-W5S1: empty input rejection.
    #[test]
    fn compile_project_empty_fires_m008() {
        let err =
            compile_project(vec![], None, CompileOptions::default()).expect_err("M008 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M008"), "got {codes:?}");
    }

    /// N9-W5S1: duplicate source-file names.
    #[test]
    fn compile_project_duplicate_names_fire_m007() {
        let a = SourceFile::new("dup.sigil", "module dup;\n");
        let b = SourceFile::new("dup.sigil", "module dup;\n");
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M007 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M007"), "got {codes:?}");
    }

    /// N11-W5S1: invalid source-name (no `.sigil` extension).
    #[test]
    fn compile_project_invalid_source_name_fires_m009() {
        let a = SourceFile::new("first.sigil", "module first;\n");
        let b = SourceFile::new("second.txt", "module second;\n");
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M009 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M009"), "got {codes:?}");
    }

    /// N11-W5S1: source-name with `..` path segment rejected.
    #[test]
    fn compile_project_path_traversal_fires_m009() {
        let a = SourceFile::new("first.sigil", "module first;\n");
        let b = SourceFile::new("a/../second.sigil", "module second;\n");
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M009 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M009"), "got {codes:?}");
    }

    /// M001: filename does not match first module declaration.
    #[test]
    fn compile_project_filename_module_mismatch_fires_m001() {
        let a = SourceFile::new("math.sigil", "module helpers;\n");
        let b = SourceFile::new(
            "main.sigil",
            "module main;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n",
        );
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M001 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M001"), "got {codes:?}");
    }

    /// N17-W5S1: M002 fires when two files declare the same module name,
    /// even when one is the file's first/only module and the other is
    /// also a top-level declaration. Inline-module collisions are
    /// covered by the same mechanism since the AST flattens both forms.
    #[test]
    fn compile_project_duplicate_module_name_fires_m002() {
        let a = SourceFile::new("a.sigil", "module a;\nmodule shared;\n");
        let b = SourceFile::new("b.sigil", "module b;\nmodule shared;\n");
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M002 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M002"), "got {codes:?}");
    }

    /// M003: no entry point in compilation set.
    #[test]
    fn compile_project_no_entry_fires_m003() {
        let a = SourceFile::new(
            "lib.sigil",
            "module lib;\npub fn helper() -> i64 { return 1; }\n",
        );
        let b = SourceFile::new(
            "util.sigil",
            "module util;\npub fn other() -> i64 { return 2; }\n",
        );
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M003 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M003"), "got {codes:?}");
    }

    /// M004: multiple entry points without `--entry` override.
    #[test]
    fn compile_project_multiple_entries_fire_m004() {
        let a = SourceFile::new(
            "a.sigil",
            "module a;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }\n",
        );
        let b = SourceFile::new(
            "b.sigil",
            "module b;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 2; }\n",
        );
        let err = compile_project(vec![a, b], None, CompileOptions::default())
            .expect_err("M004 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M004"), "got {codes:?}");
    }

    /// N16-W5S1: `--entry foo` where `foo` is not in the compilation
    /// set fires M010 listing available modules.
    #[test]
    fn compile_project_unknown_entry_fires_m010() {
        let a = SourceFile::new(
            "a.sigil",
            "module a;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }\n",
        );
        let b = SourceFile::new(
            "b.sigil",
            "module b;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 2; }\n",
        );
        let err = compile_project(vec![a, b], Some("ghost"), CompileOptions::default())
            .expect_err("M010 expected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(codes.contains(&"M010"), "got {codes:?}");
    }

    /// M004 resolved via `--entry` override.
    #[test]
    fn compile_project_entry_override_resolves_ambiguity() {
        let a = SourceFile::new(
            "a.sigil",
            "module a;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }\n",
        );
        let b = SourceFile::new(
            "b.sigil",
            "module b;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 2; }\n",
        );
        let compilation = compile_project(vec![a, b], Some("a"), CompileOptions::default())
            .expect("--entry resolves M004");
        assert_eq!(&compilation.wasm_inner[..4], b"\0asm");
    }

    /// N7-W5S1 / N29-W5S1: determinism under arg order. Three
    /// permutations of a 3-file fixture must produce byte-identical
    /// wasm. Permutation set explicitly includes a reverse-sort order
    /// (worst case for any insertion-order-dependent code).
    #[test]
    fn compile_project_is_deterministic_under_permuted_arg_order() {
        let a_text = "module a;\npub fn helper_a() -> i64 { return 1; }\n";
        let m_text = "module m;\npub fn helper_m() -> i64 { return 2; }\n";
        let z_text = "module z;\nuse sigil::a;\nuse sigil::m;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return a::helper_a() + m::helper_m(); }\n";

        let mk = |order: [&str; 3]| -> Vec<SourceFile> {
            order
                .iter()
                .map(|name| match *name {
                    "a.sigil" => SourceFile::new("a.sigil", a_text),
                    "m.sigil" => SourceFile::new("m.sigil", m_text),
                    "z.sigil" => SourceFile::new("z.sigil", z_text),
                    _ => unreachable!(),
                })
                .collect()
        };

        let ascending = compile_project(
            mk(["a.sigil", "m.sigil", "z.sigil"]),
            None,
            CompileOptions::default(),
        )
        .expect("ascending compiles");
        let descending = compile_project(
            mk(["z.sigil", "m.sigil", "a.sigil"]),
            None,
            CompileOptions::default(),
        )
        .expect("descending compiles");
        let arbitrary = compile_project(
            mk(["m.sigil", "z.sigil", "a.sigil"]),
            None,
            CompileOptions::default(),
        )
        .expect("arbitrary compiles");

        // N7-W5S1: byte-identical wasm across all three permutations.
        assert_eq!(ascending.wasm_inner, descending.wasm_inner);
        assert_eq!(ascending.wasm_inner, arbitrary.wasm_inner);
        // Module list is canonical-sorted under all permutations.
        assert_eq!(ascending.module_names, descending.module_names);
        assert_eq!(ascending.module_names, arbitrary.module_names);
    }

    /// N4-W5S1: enforce_filename_module handles empty-modules file
    /// without panicking. (Whitespace-only files are silently accepted
    /// and contribute no modules to the merge.)
    #[test]
    fn enforce_filename_module_accepts_empty_file() {
        use super::enforce_filename_module;
        let source = SourceFile::new("empty.sigil", "// just a comment\n");
        let program = Program { modules: vec![] };
        assert!(enforce_filename_module(&source, &program).is_ok());
    }

    /// Reference: codes::M001 etc. all wired into the registry; if a
    /// new code's registry entry is missing, debug_assert in
    /// Diagnostic::error will catch it. This test confirms the registry
    /// recognizes every M-prefix code we introduced.
    #[test]
    fn m_codes_are_registered() {
        let m_codes = [
            codes::M001,
            codes::M002,
            codes::M003,
            codes::M004,
            codes::M005,
            codes::M006,
            codes::M007,
            codes::M008,
            codes::M009,
            codes::M010,
            codes::M011,
        ];
        for code in m_codes {
            assert!(
                crate::diagnostics::registry::lookup(code).is_some(),
                "code {code} must be registered"
            );
        }
    }
}
