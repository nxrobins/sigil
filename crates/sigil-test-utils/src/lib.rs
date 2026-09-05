//! Shared testing infrastructure for the SIGIL workspace.
//!
//! This crate provides four shared testing pillars:
//!
//! 1. **Sub-Tree Parsing** ([`parse`]) — `parse_program!`,
//!    `parse_expr!`, `parse_type!` macros that wrap a SIGIL snippet in
//!    a minimal containing context, parse it via the real compiler
//!    front-end, and extract the requested AST node. Defeats AST
//!    setup hell in unit tests.
//!
//! 2. **Snapshot helpers** ([`snapshot`]) — wrappers around `insta`
//!    with canonical formatters that strip span/source-position noise
//!    so snapshots aren't sensitive to whitespace in the fixture
//!    source.
//!
//! 3. **Fixture loaders** ([`fixtures`]) — `load_cve_fixture(name)`,
//!    `each_fixture_in(dir)` iterators. Bridges the `tests/cve_corpus/`,
//!    `tests/attack/`, and `tests/z3_corpus/` directories to test code.
//!
//! 4. **Mock WASM FFI** ([`mock_wasm`]) — `MockWasmInstance` records
//!    every host-import call (`fuel_decrement`, `send`, `ask`,
//!    `spawn`, `cap_split`, `cap_restrict`) without compiling/running
//!    real WASM. Lets `proptest` action-stream fuzzers in
//!    `sigil-runtime` iterate at 1000+ cases/sec.
//!
//! ## Why a separate crate?
//!
//! `#[macro_export]` declarative macros need to live in a crate that
//! consumers can `use` directly; a `#[cfg(test)]` module inside
//! `sigil-compiler` would not be reachable from `sigil-runtime` tests.
//! A dedicated crate also keeps test-only dependencies (insta and
//! proptest) out of production builds.
//!
//! ## Consumer pattern
//!
//! ```toml
//! [dev-dependencies]
//! sigil-test-utils = { path = "../sigil-test-utils" }
//! ```
//!
//! ```rust,ignore
//! use sigil_test_utils::{parse_expr, parse_program};
//!
//! #[test]
//! fn narrowing_recognizes_eq() {
//!     let expr = parse_expr!("x == 7");
//!     // ... assertions on `expr` ...
//! }
//! ```

pub mod fixtures;
pub mod mock_wasm;
pub mod parse;
pub mod pipeline;
pub mod snap_fixtures;
pub mod snapshot;
