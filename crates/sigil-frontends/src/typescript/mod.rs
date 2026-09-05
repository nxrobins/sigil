//! The FE0 TypeScript → SIGIL capability-contract frontend.
//!
//! Pipeline: [`lexer::lex`] → [`parser::parse`] → [`emit::emit`]. Every stage is
//! fail-fast and total — on any out-of-subset or malformed input it returns a
//! single [`FrontendDiag`] and emits nothing (threat T12). See the
//! Constraints & Fallbacks matrix in `docs/specs/foreign-frontends.md`.

pub mod check;
pub mod desugar;
pub mod emit;
pub mod lexer;
pub mod parser;

use crate::{EmittedSigil, Frontend, FrontendDiag};

/// TypeScript policy subset → inner-ring SIGIL capability contracts.
pub struct TypeScriptFrontend;

impl Frontend for TypeScriptFrontend {
    fn name(&self) -> &'static str {
        "typescript"
    }

    fn translate(&self, src: &str, source_name: &str) -> Result<EmittedSigil, Vec<FrontendDiag>> {
        let toks = lexer::lex(src).map_err(|d| vec![d])?;
        let mut program = parser::parse(toks, src.len()).map_err(|d| vec![d])?;
        // Fixed pipeline order (M3): desugar &&/|| BEFORE check/emit, so both
        // run on the fully-lowered tree.
        desugar::desugar(&mut program).map_err(|d| vec![d])?;
        emit::emit(&program, source_name).map_err(|d| vec![d])
    }
}
