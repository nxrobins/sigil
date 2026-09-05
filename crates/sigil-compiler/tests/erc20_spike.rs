//! SOL-ERC20 solver regression (EX-7): the emitted ERC20 shape — a `Token` holding a
//! single-level balances map + a two-key allowance map, whose `transferFrom` folds into
//! the atomic cross-map `transfer_from` — must compile under the SOLVER (Z3), not just
//! the structural rules. The `sigil-frontends` round-trip runs no-solver (the CLI is
//! `default-features = false`), so the solver proof lives here (cf. m2_cap_spike).
//!
//! `BoundedMap_u256_u256_64` / `BoundedMap2_u256_u256_u256_64` are AMBIENT-INJECTED by
//! their type-name triggers, so this also pins that the real shipped stdlib (the two-key
//! map + the cross-map `transfer_from`, with its two disjoint `@Mut` field borrows)
//! solves clean — including the M-spike's S1 shape it de-risked.
use sigil_compiler::compile_named_module;

#[test]
fn erc20_full_shape_compiles_under_solver() {
    // Mirrors the frontend's emitted ERC20 (the `erc20_full.sigil` golden): approve
    // (a two-key insert) + the atomic transferFrom (`allowance.transfer_from(balances,…)`,
    // two disjoint `@Mut` field borrows of `self`).
    let src = r#"module erc20_solver;
record Token { balances: BoundedMap_u256_u256_64, allowance: BoundedMap2_u256_u256_u256_64 }
impl Token {
    pub fn new() -> Token {
        return Token { balances: BoundedMap_u256_u256_64::new(), allowance: BoundedMap2_u256_u256_u256_64::new() };
    }
    pub fn approve(self: Token @Mut, __fe_sender: u256, spender: u256, amount: u256) {
        self.allowance.insert(__fe_sender, spender, amount);
    }
    pub fn transferFrom(self: Token @Mut, __fe_sender: u256, from: u256, to: u256, amount: u256) -> bool {
        trap_if(!((self.allowance.get_or(from, __fe_sender, 0) >= amount)));
        self.allowance.transfer_from(self.balances, from, __fe_sender, to, amount);
        return true;
    }
}
"#;
    if let Err(e) = compile_named_module("erc20_solver.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("ERC20 shape must compile under solver, got {codes:?}\n{msgs:#?}");
    }
}
