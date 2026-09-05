//! Fuel insertion and the compiler's budget RECOMMENDATION.
//!
//! `recommended_budget` is `128 + 8 × WCC`, where WCC is the program's static
//! worst-case decrement total. For a program whose every decrement site sits
//! under statically-bounded loops only (for-range with literal bounds), whose
//! call graph is acyclic, and which contains no indirect calls or actor
//! sends, WCC is a PROVEN workload ceiling and `FuelPlan::is_workload_ceiling`
//! is true — running at the recommendation can never legitimately fuel-trap.
//!
//! Everything else falls back, per SITE, to the pre-WCC floor semantics (each
//! unbounded site contributes its amount once) and clears the flag: a while
//! loop's trip count is data-dependent, so no static formula can cover it —
//! a 5000-iteration while carries ONE back-edge site (weight 1, budgeted 8)
//! but burns 5001 fuel at run time. Callers that need a real ceiling for such
//! programs must choose one from policy — `sigil forge` defaults to 100_000
//! (`parse_forge_args`, `sigil-cli/src/args.rs`) and ignores this
//! recommendation.
//!
//! The WCC model (mirrored bit-exactly by the selfhost shadow, SH-FUEL F2):
//!   own(f)  = Σ over decrements of amount × block multiplicity
//!             (`AirFunction::block_static_multiplicity`, written by
//!             `air::lower`; None → ×1 + flag cleared)
//!   cost(f) = own(f) + Σ over call sites of multiplicity × cost(callee),
//!             resolved callee-first by a deterministic index-scan pass;
//!             functions on or behind a call-graph cycle keep cost = own and
//!             clear the flag
//!   WCC     = Σ over ALL functions of cost(f) — the program-TEXT model:
//!             shared callees are deliberately double-counted and dead code
//!             still budgets (over-recommendation is safe; the budget is a
//!             grant ceiling, and unspent fuel costs nothing)
//! All multiplication/addition saturates at `FUEL_MULT_CLAMP` (2^40) so the
//! shadow's i64 arithmetic can reproduce it exactly.

use crate::air::{AirProgram, AirStmt, AirTerminator, FUEL_MULT_CLAMP, fuel_mul_clamped};

const BASE_FUEL_BUDGET: u64 = 128;
const FUEL_COST_PER_SITE: u64 = 8;

/// `a + b` under the shared clamp (see `FUEL_MULT_CLAMP`).
fn fuel_add_clamped(a: u64, b: u64) -> u64 {
    a.saturating_add(b).min(FUEL_MULT_CLAMP)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuelPlan {
    pub inserted_sites: usize,
    pub recommended_budget: u64,
    /// True iff `recommended_budget` is a PROVEN workload ceiling: every fuel
    /// decrement site carries a static multiplicity (all enclosing loops are
    /// for-range with literal bounds), the call graph is acyclic, and no
    /// function contains an indirect call or actor send/ask/spawn (whose cost
    /// the static call graph cannot see). False = the budget is the old
    /// straight-line floor and a looping workload can legitimately exceed it.
    pub is_workload_ceiling: bool,
}

pub fn insert(program: AirProgram) -> (AirProgram, FuelPlan) {
    let mut inserted_sites = 0usize;
    let fn_count = program.functions.len();
    // Per function: own worst-case cost, call edges (callee index,
    // multiplicity), and whether any site was unbounded/unanalyzable.
    let mut own = vec![0u64; fn_count];
    let mut edges: Vec<Vec<(usize, u64)>> = vec![Vec::new(); fn_count];
    let mut poisoned = false;

    let functions: Vec<_> = program
        .functions
        .into_iter()
        .enumerate()
        .map(|(fn_idx, mut function)| {
            for block in &mut function.blocks {
                // Multiplicity of this block; out-of-bounds (hand-built AIR)
                // reads as None — fail-closed, never a ceiling.
                let mult = function
                    .block_static_multiplicity
                    .get(block.id.0 as usize)
                    .copied()
                    .flatten();
                let weighted = |amount: u64| match mult {
                    Some(m) => fuel_mul_clamped(amount.min(FUEL_MULT_CLAMP), m),
                    None => amount.min(FUEL_MULT_CLAMP),
                };
                // An unbounded block only poisons the ceiling claim if it
                // actually contributes cost or call edges — checked per-site.
                let mut lowered = Vec::with_capacity(block.stmts.len());
                for stmt in std::mem::take(&mut block.stmts) {
                    // Pre-existing decrements (memory::lower's alloc fuel,
                    // max(1, size/64)) were previously NOT counted at all —
                    // the recommendation under-funded every allocating
                    // program. They weight like any other site.
                    if let AirStmt::FuelDecrement { amount } = &stmt {
                        own[fn_idx] = fuel_add_clamped(own[fn_idx], weighted(u64::from(*amount)));
                        if mult.is_none() {
                            poisoned = true;
                        }
                    }
                    match &stmt {
                        AirStmt::Call { func, .. } => {
                            edges[fn_idx].push((func.0 as usize, mult.unwrap_or(1)));
                            if mult.is_none() {
                                poisoned = true;
                            }
                        }
                        // An indirect call's target — and therefore its cost —
                        // is invisible to the static call graph: a closure
                        // invoked inside a ×64 loop would otherwise let the
                        // flag report a ceiling UNSOUNDLY. Sends/asks/spawns
                        // bill real work to another actor's budget the same
                        // invisible way.
                        AirStmt::CallIndirect { .. }
                        | AirStmt::MessageSend { .. }
                        | AirStmt::MessageAsk { .. }
                        | AirStmt::SpawnActor { .. } => {
                            poisoned = true;
                        }
                        // AG-S1-M: `str ==` hides a byte-compare loop inside a
                        // single statement, and its trip count is a runtime
                        // string length — invisible to the static WCC formula,
                        // exactly like an indirect call's callee cost. The
                        // runtime charge lives in `wasm.rs` (1 per byte); here
                        // the statement contributes a floor and clears the
                        // ceiling. Deliberately NOT added to `requires_fuel`:
                        // that prepends ONE decrement before the statement, an
                        // O(1) charge for O(n) work, which would look like
                        // metering while providing none.
                        AirStmt::StrBytesEq { .. } => {
                            own[fn_idx] = fuel_add_clamped(own[fn_idx], weighted(1));
                            poisoned = true;
                        }
                        _ => {}
                    }
                    if requires_fuel(&stmt) {
                        lowered.push(AirStmt::FuelDecrement { amount: 1 });
                        inserted_sites += 1;
                        own[fn_idx] = fuel_add_clamped(own[fn_idx], weighted(1));
                        if mult.is_none() {
                            poisoned = true;
                        }
                    }
                    lowered.push(stmt);
                }
                // Back-edge fuel: burn fuel on every loop iteration (Spec §10).
                // The decrement lands in the cond block, which runs trip+1
                // times — its multiplicity already says E×(K+1).
                if matches!(block.terminator, AirTerminator::Loop { .. }) {
                    lowered.push(AirStmt::FuelDecrement { amount: 1 });
                    inserted_sites += 1;
                    own[fn_idx] = fuel_add_clamped(own[fn_idx], weighted(1));
                    if mult.is_none() {
                        poisoned = true;
                    }
                }
                block.stmts = lowered;
            }
            function
        })
        .collect();

    // Callee-first cost propagation: a deterministic index-scan pass (the
    // shadow mirrors this loop shape exactly — no queue, no hash order).
    // A function resolves once every callee has resolved; whatever is left
    // when a full scan makes no progress sits on or behind a cycle
    // (recursion) — it keeps cost = own and the ceiling claim dies.
    let mut cost = own.clone();
    let mut done = vec![false; fn_count];
    loop {
        let mut progressed = false;
        for i in 0..fn_count {
            if done[i] {
                continue;
            }
            let ready = edges[i]
                .iter()
                .all(|(callee, _)| *callee >= fn_count || done[*callee]);
            if ready {
                let mut c = own[i];
                for (callee, mult) in &edges[i] {
                    if *callee < fn_count {
                        c = fuel_add_clamped(c, fuel_mul_clamped(cost[*callee], *mult));
                    }
                }
                cost[i] = c;
                done[i] = true;
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }
    if done.iter().any(|d| !d) {
        poisoned = true;
    }

    let wcc = cost.iter().fold(0u64, |acc, c| fuel_add_clamped(acc, *c));

    (
        AirProgram { functions },
        FuelPlan {
            inserted_sites,
            recommended_budget: BASE_FUEL_BUDGET
                .saturating_add(wcc.saturating_mul(FUEL_COST_PER_SITE)),
            is_workload_ceiling: !poisoned,
        },
    )
}

fn requires_fuel(stmt: &AirStmt) -> bool {
    matches!(
        stmt,
        AirStmt::Call { .. }
            | AirStmt::MessageSend { .. }
            | AirStmt::MessageAsk { .. }
            | AirStmt::SpawnActor { .. }
    )
}
