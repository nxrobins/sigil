//! SOL-MULTIMAP M-A M-spike: the emitted shape for a ≥2-map body (writes to DISTINCT mappings) that the
//! frontend's `ReservedBatch` fold produces must be valid SIGIL. SIGIL has no rollback, so the CEI gate
//! rejects a 2nd map write after a commit — but writes to DIFFERENT maps are provably distinct storage,
//! so the batch is made atomic by RESERVE-ALL-THEN-WRITE: hoist every value, `reserve1` every deferred
//! map (read-only — commits nothing), run the ≤1 folded `.transfer()` (self-atomic), then the trap-free
//! `insert`s. This regression pins that shape as accepted by the trusted compiler. No caps/solver.
use sigil_compiler::compile_named_module;

#[test]
fn sol_multimap_reserved_batch_shape_compiles() {
    let src = r#"module sol_multimap_spike;

record Token {
    balances: BoundedMap_u256_u256_64,
    locked: BoundedMap_u256_u256_64,
    rewardDebt: BoundedMap_u256_u256_64,
}

impl Token {
    pub fn new() -> Token {
        return Token {
            balances: BoundedMap_u256_u256_64::new(),
            locked: BoundedMap_u256_u256_64::new(),
            rewardDebt: BoundedMap_u256_u256_64::new(),
        };
    }

    // lock: `balances[u] -= a; locked[u] += a;` — two plain writes to DISTINCT maps. Values hoisted
    // (read pre-write), both maps reserved (read-only), then both inserts trap-free.
    pub fn lock(self: Token @Mut, u: u256, a: u256) {
        let mut __fe_w0: u256 = (self.balances.get_or(u, 0) - a);
        let mut __fe_w1: u256 = (self.locked.get_or(u, 0) + a);
        self.balances.reserve1(u);
        self.locked.reserve1(u);
        self.balances.insert(u, __fe_w0);
        self.locked.insert(u, __fe_w1);
    }

    // transfer + reward: a folded balances `.transfer()` (self-atomic) + a deferred write to a DISTINCT
    // rewardDebt map. Reserve the deferred map first (read-only) → the atomic transfer → the trap-free
    // deferred insert. If the transfer traps (balance/capacity), rewardDebt was only reserved, not written.
    pub fn transferWithReward(self: Token @Mut, from: u256, to: u256, amt: u256, r: u256) {
        let mut __fe_w0: u256 = (self.rewardDebt.get_or(to, 0) + r);
        self.rewardDebt.reserve1(to);
        self.balances.transfer(from, to, amt);
        self.rewardDebt.insert(to, __fe_w0);
    }
}
"#;
    if let Err(e) = compile_named_module("sol_multimap_spike.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("reserved distinct-maps batch shape must compile, got {codes:?}\n{msgs:#?}");
    }
}
