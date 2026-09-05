//! Rust → SIGIL frontend — RS0 (the value-semantics core; the authority-free base
//! case of the capability synergy). See `docs/specs/rust-frontend-rs0.md`.
//!
//! Pipeline: [`lexer::lex`] → [`parser::parse`] → [`check::check`] → [`emit::emit`].
//! Every stage is fail-fast and total: on anything outside the RS0 subset it
//! returns a single [`FrontendDiag`] (an `FE6xx` reject) and emits NOTHING. The
//! translator is UNTRUSTED; the Rust `sigil-compiler` re-verifies the emitted
//! SIGIL.
//!
//! **S-AUTH (the guarantee) is STRUCTURAL.** The emitter's output alphabet is a
//! fixed set of arithmetic / comparison / control-flow / in-subset-call nodes over
//! `i64`/`bool` — it names no capability, intrinsic, `extern`, allocation, or host
//! operation, so the emitted program has no way to reach ambient `std`. This is
//! the frontend's to enforce, NOT the compiler's: an RS0 module is inner-ring,
//! which `effect_check` skips, so SIGIL type/structure-checks the output but does
//! not certify authority-freedom (the harden-spec UP-1 correction).
//!
//! RS0 skeleton scope (this increment): top-level `fn`/`pub fn`, `i64`/`bool`
//! params + return, and a body that is a single `return <expr>;` or tail `<expr>`
//! over `+ - *`, comparisons, `== !=`, unary `! -`, and calls to declared
//! in-subset functions. Locals (`let`) and control-flow (`if`/`while`) arrive in
//! the next increment.

pub mod check;
pub mod emit;
pub mod lexer;
pub mod parser;

use crate::{EmittedSigil, Frontend, FrontendDiag};

/// Rust subset → SIGIL — memory-safe (Rust) ∧ capability-safe (SIGIL).
pub struct RustFrontend;

impl Frontend for RustFrontend {
    fn name(&self) -> &'static str {
        "rust"
    }

    fn translate(&self, src: &str, source_name: &str) -> Result<EmittedSigil, Vec<FrontendDiag>> {
        let toks = lexer::lex(src).map_err(|d| vec![d])?;
        let program = parser::parse(toks, src.len()).map_err(|d| vec![d])?;
        // The sound checker (oracle agreement: every node gets the type the SIGIL
        // compiler would resolve) runs BEFORE emit, so a rejected program never
        // produces SIGIL text.
        check::check(&program).map_err(|d| vec![d])?;
        emit::emit(&program, source_name).map_err(|d| vec![d])
    }
}
