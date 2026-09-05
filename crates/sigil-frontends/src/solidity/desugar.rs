//! Solidity pre-check lowering coordinator.
//!
//! Pass implementations live in focused submodules; the order here is part of the
//! frontend's soundness contract and is pinned by `pass_order_tests`.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use super::check::expr_has_checked_arith;
use super::parser::{
    AssignOp, BinOp, Constructor, Contract, Expr, Function, MAX_NEST_DEPTH, Modifier, Param,
    Program, StateMutability, StateVar, Stmt, TypeRef, Visibility, struct_map_synth_name,
};
use crate::FrontendDiag;
use crate::codes;
use crate::limits::SYNTH_PREFIX;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FunctionPass {
    Update,
    SpendTransfer,
    Transfer,
    TransferFrom,
    Split,
    Airdrop,
    TotalCei,
    ReserveMultiMap,
}

const FUNCTION_PASS_ORDER: [FunctionPass; 8] = [
    FunctionPass::Update,
    FunctionPass::SpendTransfer,
    FunctionPass::Transfer,
    FunctionPass::TransferFrom,
    FunctionPass::Split,
    FunctionPass::Airdrop,
    FunctionPass::TotalCei,
    FunctionPass::ReserveMultiMap,
];

impl FunctionPass {
    fn apply_recognizer(self, body: Vec<Stmt>) -> Result<Vec<Stmt>, FrontendDiag> {
        match self {
            Self::Update => Ok(recognize_update(body)),
            Self::SpendTransfer => Ok(recognize_spend_transfer(body)),
            Self::Transfer => Ok(recognize_transfers(body)),
            Self::TransferFrom => Ok(recognize_transfer_from(body)),
            Self::Split => Ok(recognize_split(body)),
            Self::Airdrop => recognize_airdrop(body),
            Self::TotalCei | Self::ReserveMultiMap => {
                unreachable!("storage passes use apply_storage")
            }
        }
    }

    fn apply_storage(
        self,
        body: Vec<Stmt>,
        state: &HashSet<String>,
        numeric: &HashSet<String>,
        types: &HashMap<String, TypeRef>,
        locals: &HashSet<String>,
        reserve_counter: &mut usize,
    ) -> Vec<Stmt> {
        match self {
            Self::TotalCei => total_cei(body, state, numeric, types, locals),
            Self::ReserveMultiMap => reserve_multi_map(body, state, types, locals, reserve_counter),
            _ => unreachable!("recognizer passes use apply_recognizer"),
        }
    }
}

#[cfg(test)]
mod pass_order_tests {
    use std::collections::HashSet;

    use super::{FUNCTION_PASS_ORDER, FunctionPass};

    #[test]
    fn function_pass_order_is_unique_and_respects_dependencies() {
        let unique: HashSet<_> = FUNCTION_PASS_ORDER.iter().copied().collect();
        assert_eq!(unique.len(), FUNCTION_PASS_ORDER.len());

        let dependencies = [
            (FunctionPass::Update, FunctionPass::SpendTransfer),
            (FunctionPass::SpendTransfer, FunctionPass::Transfer),
            (FunctionPass::Transfer, FunctionPass::TransferFrom),
            (FunctionPass::TransferFrom, FunctionPass::Split),
            (FunctionPass::Split, FunctionPass::Airdrop),
            (FunctionPass::Airdrop, FunctionPass::TotalCei),
            (FunctionPass::TotalCei, FunctionPass::ReserveMultiMap),
        ];
        for (before, after) in dependencies {
            let before_index = FUNCTION_PASS_ORDER.iter().position(|pass| *pass == before);
            let after_index = FUNCTION_PASS_ORDER.iter().position(|pass| *pass == after);
            assert!(
                before_index < after_index,
                "{before:?} must precede {after:?}"
            );
        }
    }
}

pub fn desugar(p: &mut Program, cap: Option<&CapGuardInfo>) -> Result<(), FrontendDiag> {
    // The emitted capability borrow replaces recognized gate modifiers.
    if let Some(info) = cap {
        for f in &mut p.contract.functions {
            if info.guarded_methods.contains(&f.name) {
                f.modifiers.clear();
            }
        }
    }
    // Inline modifiers before callees so every spliced body sees the same lowerings.
    inline_modifiers(&mut p.contract)?;
    inline_internal_calls(&mut p.contract, cap.is_some())?;
    prune_functions(&mut p.contract);

    // Snapshot storage metadata before mutably traversing function bodies.
    let mw_state: HashSet<String> = p.contract.state.iter().map(|sv| sv.name.clone()).collect();
    let mw_numeric: HashSet<String> = p
        .contract
        .state
        .iter()
        .filter(|sv| mw_is_numeric_ty(&sv.ty))
        .map(|sv| sv.name.clone())
        .collect();
    let mw_tys: HashMap<String, TypeRef> = p
        .contract
        .state
        .iter()
        .map(|sv| (sv.name.clone(), sv.ty.clone()))
        .collect();
    for f in &mut p.contract.functions {
        lower_sender(f);
        let mut d = D::default();
        let body = std::mem::take(&mut f.body);
        let mut body = d.block(body)?;
        for pass in FUNCTION_PASS_ORDER.iter().take(6).copied() {
            body = pass.apply_recognizer(body)?;
        }

        let mut mw_locals: HashSet<String> =
            f.params.iter().map(|param| param.name.clone()).collect();
        collect_local_names(&body, &mut mw_locals);
        let mut reserve_counter = 0;
        for pass in FUNCTION_PASS_ORDER.iter().skip(6).copied() {
            body = pass.apply_storage(
                body,
                &mw_state,
                &mw_numeric,
                &mw_tys,
                &mw_locals,
                &mut reserve_counter,
            );
        }
        f.body = body;
    }
    // Constructors have no `self`, so only sender and ANF lowering apply.
    if let Some(ctor) = &mut p.contract.constructor {
        lower_sender_ctor(ctor);
        let mut d = D::default();
        let body = std::mem::take(&mut ctor.body);
        ctor.body = d.block(body)?;
    }
    Ok(())
}

mod cap_guards;
mod inlining;
mod lowering;
mod preprocess;
mod storage;
mod transfers;

use cap_guards::*;
use inlining::*;
use lowering::*;
use preprocess::*;
use storage::*;
use transfers::*;

pub use cap_guards::{CapGuardInfo, detect_cap_directive, recognize_cap_guards};
pub(super) use lowering::{disambiguate_overloads, explode_struct_maps};
pub(super) use preprocess::{normalize_literals, reject_impure_msgsender, unwrap_unchecked};
