//! Stable diagnostic codes for the Sigil compiler.
//!
//! Every diagnostic carries a `DiagnosticCode` — a stable, machine-readable
//! identifier that an LLM driver can act on. Codes are organized by single-letter
//! prefix matching the checker that fires the diagnostic:
//!
//! - `L` Lexer
//! - `P` Parser
//! - `N` Name resolution
//! - `T` Type checking (includes monomorphization)
//! - `O` Ownership / borrow
//! - `E` Effect / taint
//! - `R` Ring / structural capability
//! - `C` Z3 capability proofs
//! - `F` FFI / foreign types
//! - `S` Source-limit / forge gates
//! - `M` Module-set / multi-file project (Wall 5 Step 1 onwards)
//! - `Y` Codegen (reserved)
//! - `I` Internal compiler error
//!
//! Range policy:
//! - `001`–`799` compiler-emitted
//! - `800`–`899` reserved for runtime feedback re-emitted as compile diagnostics
//! - `900`–`999` unstable (may rename before 1.0)

/// A stable diagnostic identifier.
///
/// Newtype around `&'static str` so call sites can declare codes as
/// `pub const T001: DiagnosticCode = DiagnosticCode::new("T001")` adjacent to
/// the registry table — one source of truth, no 121-variant enum to maintain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagnosticCode(&'static str);

impl DiagnosticCode {
    pub const fn new(code: &'static str) -> Self {
        Self(code)
    }

    pub const fn as_str(&self) -> &'static str {
        self.0
    }
}

impl std::fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

pub use super::registry::generated_codes::*;
