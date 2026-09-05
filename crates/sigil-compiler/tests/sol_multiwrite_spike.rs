//! SOL-MULTIWRITE M-spike: the emitted shape for a Solidity multi-write body (OZ `_burn`/`_mint`)
//! that the frontend's `total_cei` desugar pass produces must be valid SIGIL. The transform hoists
//! every trap-capable storage-write's arithmetic into a pre-write `__fe_wN` local and reorders the
//! single map write FIRST, so the emitted body is: [reads/guards/hoisted-lets] → [the one map
//! `insert`] → [trap-free scalar stores]. There is NO commit-then-trap: all trapping arithmetic is
//! evaluated before any storage write, and the only scalar stores after the map write read a
//! pre-computed local (trap-free). This regression pins that shape as accepted by the trusted
//! compiler (the frontend's FE412 gate — which the transform is engineered to pass — is verified
//! separately by the `erc20_burn`/`erc20_mint` compile goldens round-tripping). No caps/solver.
use sigil_compiler::compile_named_module;

#[test]
fn sol_multiwrite_hoisted_shape_compiles() {
    let src = r#"module sol_multiwrite_spike;

record Token { balances: BoundedMap_u256_u256_64, totalSupply: u256 }

impl Token {
    pub fn new() -> Token {
        return Token { balances: BoundedMap_u256_u256_64::new(), totalSupply: 0 };
    }

    // hoisted OZ `_burn`: `let fromBalance = balances[from]; require(fromBalance >= amount);
    // balances[from] = fromBalance - amount; totalSupply = totalSupply - amount;` — the
    // totalSupply arithmetic hoisted to `__fe_w0` before the map write; the map write first;
    // the scalar store trap-free.
    pub fn burn(self: Token @Mut, from: u256, amount: u256) {
        let mut fromBalance: u256 = self.balances.get_or(from, 0);
        trap_if(!((fromBalance >= amount)));
        let mut __fe_w0: u256 = (self.totalSupply - amount);
        self.balances.insert(from, (fromBalance - amount));
        self.totalSupply = __fe_w0;
    }

    // hoisted OZ `_mint` (compound form): `totalSupply += amount; balances[account] += amount;`
    // — the totalSupply arithmetic hoisted to `__fe_w0`; the compound map write kept whole and
    // reordered first; the scalar store trap-free.
    pub fn mint(self: Token @Mut, account: u256, amount: u256) {
        let mut __fe_w0: u256 = (self.totalSupply + amount);
        self.balances.insert(account, self.balances.get_or(account, 0) + (amount));
        self.totalSupply = __fe_w0;
    }
}
"#;
    if let Err(e) = compile_named_module("sol_multiwrite_spike.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("hoisted multi-write shape must compile, got {codes:?}\n{msgs:#?}");
    }
}
