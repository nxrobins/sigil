//! Solidity → SIGIL frontend — SOL0 (minimal proof-of-synergy) + SOL1 (stateful
//! ledger plumbing).
//!
//! Pipeline: `lexer::lex` → `parser::parse` (multi-contract) → `flatten::flatten`
//! (C3 inheritance merge) → `check::validate_user_identifiers` → `recognize_cap_guards`
//! (cap-mode) → `desugar::desugar` (inline modifiers → lower `msg.sender` → ANF →
//! recognize transfers) → `check::check` → `lower_enum_members` → `lower_uintn_arith` →
//! `emit::emit`. Every stage is fail-fast and total: on anything outside the supported subset it
//! returns a single [`FrontendDiag`] (an `FE4xx` reject) and emits NOTHING. The
//! translator is UNTRUSTED; the Rust `sigil-compiler` re-verifies the emitted
//! SIGIL. The existential risk for a frontend is a translation that COMPILES but
//! MEANS something different from the source — so the discipline is "reject, never
//! best-effort." See `docs/specs/foreign-frontends.md` and the Solidity SCOPING /
//! hardening-triage sections of the epic plan.
//!
//! SOL0 scope: ONE contract → a SIGIL `record` (state) + `impl` (methods);
//! `uint256`/`uint` → `u256`, `bool` → `bool`; functions → `pub fn f(self: X @Mut,
//! …)`; checked `+ - * / %`; `require`/`assert`/`revert` → a runtime guard
//! (`trap_if`); `if`/`return`. Synergy: overflow-safety by construction (NOT
//! "proved invariants" — Solidity declares none; see SR-1 in the plan).
//!
//! SOL1a adds the stateful-ledger plumbing: the `address` type (a CLOSED distinct
//! type that lowers to `u256` but rejects arithmetic/ordering and never silently
//! mixes with `uint256`), single-level `mapping(K => V)` state (→ the bounded
//! `BoundedMap_u256_u256_64`), and `m[k]` index read/write (→ `get_or`/`insert`).
//! A `check.rs` `SolTy` inference pass is the SOLE gate for the address/uint256
//! distinction (the compiler sees only `u256`). A map insert is trap-capable, so the
//! CEI rule (NC-S1/NC-L2) forbids a second map write after a committed write —
//! the bounded-map two-write transfer is deferred to SOL1b.

pub mod check;
pub mod desugar;
pub mod emit;
pub mod flatten;
pub mod lexer;
pub mod parser;
pub mod project;

use crate::{EmittedSigil, Frontend, FrontendDiag};

/// Solidity contract subset → SIGIL record + impl, overflow-safe by construction.
pub struct SolidityFrontend;

impl Frontend for SolidityFrontend {
    fn name(&self) -> &'static str {
        "solidity"
    }

    fn translate(&self, src: &str, source_name: &str) -> Result<EmittedSigil, Vec<FrontendDiag>> {
        // SOL-CAP (opt-in): the `// sigil:cap-access-control` directive enables translating
        // the `onlyOwner` access-control pattern into an UNFORGEABLE `&Cap` gate (vs the
        // forgeable `__fe_sender == owner` trap). It is a comment (invisible to the lexer);
        // OFF by default → the whole cap path is inert and output is byte-identical SOL1c.
        let cap_mode = desugar::detect_cap_directive(src);
        let toks = lexer::lex(src).map_err(|d| vec![d])?;
        // SOL-INH: parse collects ALL top-level contracts; `flatten` C3-linearizes + merges the
        // inheritance hierarchy into the single `Program.contract` the rest of the pipeline
        // consumes unchanged. A lone single-concrete-no-bases contract takes the fast path and
        // passes through byte-identically; a hierarchy is merged (per-member derived-wins, with a
        // per-contract duplicate-modifier/function reject — SOL-HARDEN C1).
        let parsed = parser::parse(toks, src.len()).map_err(|d| vec![d])?;
        let program = flatten::flatten(parsed).map_err(|d| vec![d])?;
        run_pipeline(program, cap_mode, source_name)
    }
}

/// The post-flatten pipeline (validate → unwrap → normalize → cap scan → desugar → check →
/// lowerings → emit), shared VERBATIM by the single-file `translate` above and the
/// SOL-XFILE project path (`project.rs`) — extracting it is a pure refactor, so the
/// single-file behavior stays byte-identical (EX-6).
pub(super) fn run_pipeline(
    mut program: parser::Program,
    cap_mode: bool,
    source_name: &str,
) -> Result<EmittedSigil, Vec<FrontendDiag>> {
    {
        // Validate ALL user identifiers (contract/state/fn/param/local — INCL. locals inside
        // `unchecked` bodies, which `validate_local_idents` recurses into) BEFORE desugar injects
        // any synthesized `__fe_*` name — so no user identifier can collide with or alias a
        // synthesized one (the SOL1b adversarial-review bug class).
        check::validate_user_identifiers(&program).map_err(|d| vec![d])?;
        // SOL-ACCESS W3: enforce that EVERY `_msgSender` declaration is the pure `return
        // msg.sender;` shim — the precondition for treating a `_msgSender()` emit arg as a
        // droppable pure read. MUST run BEFORE `disambiguate_overloads` (which renames an
        // OVERLOADED `_msgSender` → `__fe_ov{arity}__msgSender`, hiding it from a literal-name
        // check → a CRITICAL authority bypass an adversarial review found: a guard-bearing
        // overloaded `_msgSender` called only in a discarded emit dropped its guard silently,
        // leaving the method ungated) and BEFORE `normalize_literals`/`desugar` touch the body.
        desugar::reject_impure_msgsender(&program.contract).map_err(|d| vec![d])?;
        // SOL-UNCHECKED: splice every `unchecked { … }` body into its enclosing block — AFTER
        // identifier validation (the alpha-rename of the block's top-level locals injects
        // `__fe_unchk` names, which validation must not see) but BEFORE the SOL-CAP scans below (a
        // wrapper reaching them would hide a `msg.sender`/owner use from FE454/FE455/E-2 — an
        // authority-widening bypass, adversarial-review F2/F3/F4). SIGIL u256 arithmetic is always
        // checked, so unwrapping means: where Solidity WRAPS on overflow, SIGIL TRAPS (fail-closed).
        desugar::unwrap_unchecked(&mut program.contract);
        // SOL-UPDATE: rewrite the EXACT `address(0)` cast → the numeric literal `0` over
        // functions + modifiers (NOT the constructor — AC-1 keeps the ctor path uniformly
        // fail-closed). A pure leaf rewrite (no statement erased, no identifier injected —
        // nothing the SOL-CAP scans below could miss); makes the OZ 5.x zero-address idioms
        // (leading guards, inline binds, `_update` dispatch conditions) typable via the
        // existing NC-L3c literal-vs-address rules. Every other `address(<e>)` cast stays
        // FE401 (fail-closed). SOL-XFILE PR5/L4: the same leaf-rewrite pass also folds the OZ
        // infinite-allowance literal `type(uint256).max` → the u256-max constant `2^256 − 1`
        // (only that exact shape; any other `type(...)` stays FE401).
        desugar::normalize_literals(&mut program.contract);
        // SOL-XFILE PR3/OVL: disambiguate same-name/different-arity OVERLOADS (e.g. OZ ERC20's
        // `_approve` 3-arg + 4-arg) — the flatten + validate gates kept them as a same-name set;
        // this renames each to `__fe_ov{arity}_{name}` + rewrites call sites by arg count. AFTER
        // `validate_user_identifiers` (the `__fe_` names must not be validated as user idents) and
        // BEFORE the cap scan + `inline_internal_calls`. Renaming a callee touches no argument, so
        // it hides no `msg.sender`/owner data-use from the SOL-CAP scans below (F2/F3/F4-safe).
        desugar::disambiguate_overloads(&mut program.contract).map_err(|d| vec![d])?;
        // SOL-ACCESS PR4: explode `mapping(K => Struct)` into per-field synthesized maps
        // (`__fe_sm_<var>_<field>`) — the declaration side of the parse-time access rewrite
        // (`M[k].f` → `__fe_sm_M_f[k]`). AFTER `validate_user_identifiers` (`__fe_` names
        // must not be validated as user idents) and BEFORE the SOL-CAP scans + desugar
        // (they then see only plain 1/2-key map shapes). A `__fe_sm_` reference with no
        // matching synthesis → a precise FE441 (fail-closed).
        desugar::explode_struct_maps(&mut program).map_err(|d| vec![d])?;
        // SOL-CAP recognizer + E-2 dataflow gate. Runs BEFORE desugar (it needs the
        // un-inlined modifiers + raw `msg.sender`). Returns `None` when cap-mode is off or
        // no strict `onlyOwner` pattern matches → the cap path stays inert (E-4). May reject
        // (FE454-457) when cap-mode IS on but the contract can't be faithfully cap-translated.
        let cap =
            desugar::recognize_cap_guards(&program.contract, cap_mode).map_err(|d| vec![d])?;
        // SOL1b: lower `msg.sender` → the `__fe_sender` param and ANF-desugar `&&`/`||`
        // (mirrors the TS pipeline order: lex → parse → desugar → check → emit) so the
        // checker and emitter only ever see the closed, short-circuit-free core. With a
        // cap result, desugar drops the recognized gate (the `&Cap` replaces the trap).
        desugar::desugar(&mut program, cap.as_ref()).map_err(|d| vec![d])?;
        // The sound checker (type allow-list + address distinctness, strict
        // checks-then-effects, zero-default, closed subset) runs BEFORE emit so a
        // rejected contract never produces SIGIL text.
        check::check(&program).map_err(|d| vec![d])?;
        // SOL-ENUM M2: lower `EnumName.Member` → its 0-based index literal (the enum decl is
        // erased; emit maps the surviving enum-typed field names to `u256`/`0`). Runs AFTER
        // check (so the Member nodes are type-validated) and BEFORE the uintN pass (which then
        // sees only `Num`s). FE466 if an enum-member access somehow slipped past check.
        check::lower_enum_members(&mut program).map_err(|d| vec![d])?;
        // SOL-ACCESS PR3: lower bool-valued maps to the canonical u256 0/1 — literal writes
        // `true`/`false` → `1`/`0`, reads wrapped `(… == 1)`. Runs AFTER check (write values
        // are validated literals, reads are type-validated Bool) and BEFORE the uintN pass;
        // emit then sees only plain u256 map ops + comparisons (it stays type-blind).
        check::lower_bool_maps(&mut program).map_err(|d| vec![d])?;
        // SOL-uintN M2: the width-trap lowering — rewrite same-width `uintN` `+`/`*` into the
        // checked `__fe_{add,mul}_checked(l, r, 2^N)` helpers (EX-1). Runs AFTER check (so the
        // program is well-typed) and BEFORE emit; returns which helpers to define inline.
        let uintn = check::lower_uintn_arith(&mut program);
        emit::emit(&program, source_name, cap.as_ref(), uintn).map_err(|d| vec![d])
    }
}
