//! Crate root of `sigil-compiler`: the pass-module manifest and the
//! public facade (the `compile_*` entries, diagnostics, and the
//! `SOLVER_ENABLED` build witness). Owns the crate-wide
//! `forbid(unsafe_code)` and the `solver` feature seam: the `z3_*`
//! modules exist only on solver builds, so every other module must
//! compile without them (the gating no-default-features lane).
//! Declarations and re-exports only; no failure paths live here.

#![forbid(unsafe_code)]

pub mod air;
pub mod air_capability_v2;
pub mod ambient_stdlib;
pub mod ast;
pub mod capability;
pub mod compiler;
pub mod compiler_context;
pub mod diagnostics;
pub mod effect_check;
pub mod effect_desugar;
pub mod formal;
pub mod formal_v9;
pub mod fuel;
pub mod lexer;
pub mod memory;
pub mod name_resolution;
pub mod ownership;
#[cfg(feature = "json")]
pub mod package;
pub mod parser;
pub mod registries;
pub mod ring_check;
pub mod source;
pub mod span;
pub mod taint_check;
pub mod trace;
pub mod type_check;
pub mod type_check_v2;
pub mod typed_ast;
pub mod wasm;
#[cfg(feature = "solver")]
#[doc(hidden)]
pub mod z3_cache;
#[cfg(feature = "solver")]
pub mod z3_capability;
#[cfg(feature = "solver")]
#[doc(hidden)]
pub mod z3_fragment_guard;

/// Whether the Z3 prover is compiled into THIS build of the compiler.
///
/// Distribution witness, not an enforcement mechanism: the shipped `sigil`
/// binary pins `sigil-compiler` to `default-features = false` (see
/// `crates/sigil-cli/Cargo.toml`), so a released binary answers `false`
/// here and every certificate it emits carries `solver_verified: false`.
/// `sigil --version` reports this so a downloaded binary states its own
/// verification tier instead of leaving the user to infer it from a cert
/// field.
///
/// Deliberately NOT the `solver_verified` cert witness — that one is
/// assigned at exactly one site (`capability.rs`, pinned by
/// `tests/z3_guard_fences.rs`) and must stay the only thing a cert
/// consumer trusts.
pub const SOLVER_ENABLED: bool = cfg!(feature = "solver");

pub use compiler::{
    Compilation, CompileLimits, CompileOptions, CompileResult, compile_library_project,
    compile_library_project_with_context, compile_module, compile_module_with_context,
    compile_named_module, compile_named_module_with_context, compile_named_module_with_options,
    compile_project, compile_project_with_context, compile_tool, compile_tool_with_context,
    compile_tool_with_limits, compile_tool_with_limits_and_context,
};
pub use compiler_context::{CompilerContext, CompilerContextError};
pub use diagnostics::{CompileError, Diagnostic, DiagnosticCode, Severity, codes, registry};

#[cfg(feature = "json")]
pub use diagnostics::certificate;
#[cfg(feature = "json")]
pub use diagnostics::json;
pub use sigil_abi::{RuntimeActorSpec, RuntimeHandlerSpec, RuntimeImportSpec, RuntimeModuleSpec};
