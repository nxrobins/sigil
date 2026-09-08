//! APC-1: independently check local AIR reads/writes and CFG transfers against emitted CSIR.
//!
//! The SSA plan is a witness, not an oracle: this module never uses its reaching-definition
//! solver. It reconstructs statement environments, checks actual instruction operands, and
//! enumerates every admitted predecessor transfer. Lean checks the resulting phi witnesses
//! against the final serialized program. Type-derived unreachable annotations and the AIR
//! security abstraction (including runtime scratch locals) remain explicit SR-017 premises.

use super::{Node, Op, SemanticSsaPlan, semantic_ref};
use crate::air::{AirFunction, AirStmt, AirTerminator, AirType, AirValue, BlockId, VarId};
use std::collections::{BTreeMap, BTreeSet};

pub(super) const MAX_TRANSFERS: usize = 1_000_000;
const MAX_WORK: usize = 16_000_000;

#[derive(Debug, Clone)]
pub(super) struct Transfer {
    function: u32,
    source: u32,
    target: u32,
    instruction: u32,
    operand: u32,
}

pub(super) fn encode(transfers: &[Transfer]) -> Result<Vec<u8>, String> {
    if transfers.len() > MAX_TRANSFERS {
        return Err("APC-1 transfer budget exceeded".into());
    }
    let mut bytes = Vec::with_capacity(8 + transfers.len() * 20);
    bytes.extend_from_slice(&1_u32.to_le_bytes());
    bytes.extend_from_slice(&(transfers.len() as u32).to_le_bytes());
    for transfer in transfers {
        for word in [
            transfer.function,
            transfer.source,
            transfer.target,
            transfer.instruction,
            transfer.operand,
        ] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
    }
    Ok(bytes)
}

#[derive(Default)]
pub(super) struct Budget(usize);

impl Budget {
    fn charge(&mut self, count: usize) -> Result<(), String> {
        self.0 = self
            .0
            .checked_add(count)
            .ok_or("APC-1 work budget overflow")?;
        if self.0 > MAX_WORK {
            return Err("APC-1 work budget exceeded".into());
        }
        Ok(())
    }
}

// Deliberately separate from air_stmt_destination and project_semantic_stmt. This exhaustive
// match classifies the security abstraction's reads/writes, not every Wasm scratch assignment.
fn statement_shape(statement: &AirStmt) -> (Option<VarId>, Vec<VarId>) {
    match statement {
        AirStmt::Assign { dst, val } => (
            Some(*dst),
            match val {
                AirValue::Var(src) => vec![*src],
                AirValue::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
                AirValue::RecordConstruct { fields } => {
                    fields.iter().map(|(_, value)| *value).collect()
                }
                AirValue::IntLit(_)
                | AirValue::FloatLit(_)
                | AirValue::BoolLit(_)
                | AirValue::StrLit(_)
                | AirValue::UnitLit => vec![],
            },
        ),
        AirStmt::StoreField { base_ptr, val, .. } => (None, vec![*base_ptr, *val]),
        AirStmt::LoadField { dst, base_ptr, .. } => (Some(*dst), vec![*base_ptr]),
        AirStmt::StateRead { dst, state_ptr, .. } => (Some(*dst), vec![*state_ptr]),
        AirStmt::StateWrite { state_ptr, val, .. } => (None, vec![*state_ptr, *val]),
        AirStmt::SecurityRelease { dst, src, cap, .. } => (Some(*dst), vec![*src, *cap]),
        AirStmt::Call { dst, args, .. } | AirStmt::ExternCall { dst, args, .. } => {
            (*dst, args.clone())
        }
        AirStmt::FuelDecrement { .. } | AirStmt::GrantEnd { .. } => (None, vec![]),
        AirStmt::MessageSend {
            target,
            msg,
            payload_buf,
            payload_len,
            ..
        } => (None, vec![*target, *msg, *payload_buf, *payload_len]),
        AirStmt::MessageAsk {
            dst,
            target,
            msg,
            payload_buf,
            payload_len,
            timeout,
            ..
        } => (
            Some(*dst),
            vec![*target, *msg, *payload_buf, *payload_len, *timeout],
        ),
        AirStmt::ResultTry { dst, src }
        | AirStmt::OptionTry { dst, src }
        | AirStmt::CapRestrict { dst, src, .. }
        | AirStmt::WrapI64 { dst, src }
        | AirStmt::ExtendU32 { dst, src }
        | AirStmt::SignExtendI32 { dst, src }
        | AirStmt::Borrow { dst, src, .. } => (Some(*dst), vec![*src]),
        AirStmt::ArrayOrSliceContains {
            dst,
            base_ptr,
            len,
            needle,
            idx,
            ..
        } => (Some(*dst), vec![*base_ptr, *len, *needle, *idx]),
        AirStmt::StrBytesEq {
            dst,
            lhs_data,
            lhs_len,
            rhs_data,
            rhs_len,
            idx,
        } => (
            Some(*dst),
            vec![*lhs_data, *lhs_len, *rhs_data, *rhs_len, *idx],
        ),
        AirStmt::SliceOptionElem {
            dst, data_ptr, len, ..
        } => (Some(*dst), vec![*data_ptr, *len]),
        AirStmt::SpawnActor {
            dst,
            caps,
            fuel_cap,
            ..
        } => (
            Some(*dst),
            std::iter::once(*fuel_cap)
                .chain(caps.iter().copied())
                .collect(),
        ),
        AirStmt::CapSplit { dst, src, amount } | AirStmt::CapDraw { dst, src, amount } => {
            (Some(*dst), vec![*src, *amount])
        }
        AirStmt::CapMint { dst, target, .. } => (Some(*dst), vec![*target]),
        AirStmt::SlotNew { dst, .. } | AirStmt::BumpAlloc { dst, .. } => (Some(*dst), vec![]),
        AirStmt::SlotPut { slot, cap } => (None, vec![*slot, *cap]),
        AirStmt::SlotTake { dst_cap, slot } => (Some(*dst_cap), vec![*slot]),
        AirStmt::SerializeMessage {
            msg,
            args,
            dst_buf,
            dst_len,
        } => (
            None,
            std::iter::once(*msg)
                .chain(args.iter().copied())
                .chain([*dst_buf, *dst_len])
                .collect(),
        ),
        AirStmt::DeserializeMessage {
            src_buf,
            src_len,
            dst,
        } => (Some(*dst), vec![*src_buf, *src_len]),
        AirStmt::PromoteBytes { dst, src, len } => (Some(*dst), vec![*src, *len]),
        AirStmt::IntrinsicAlloc { dst, size, .. } => (Some(*dst), vec![*size]),
        AirStmt::IntrinsicLoad8 { dst, ptr } => (Some(*dst), vec![*ptr]),
        AirStmt::IntrinsicStore8 { ptr, val } => (None, vec![*ptr, *val]),
        AirStmt::IntrinsicCtEq { dst, lhs, rhs } | AirStmt::IntrinsicCtLt { dst, lhs, rhs } => {
            (Some(*dst), vec![*lhs, *rhs])
        }
        AirStmt::IntrinsicCtSelect {
            dst,
            cond,
            then_val,
            else_val,
        } => (Some(*dst), vec![*cond, *then_val, *else_val]),
        AirStmt::LoadDynamic {
            dst,
            base_ptr,
            index,
            ..
        } => (Some(*dst), vec![*base_ptr, *index]),
        AirStmt::StoreDynamic {
            base_ptr,
            index,
            val,
            ..
        } => (None, vec![*base_ptr, *index, *val]),
        AirStmt::TrapIf { cond } => (None, vec![*cond]),
        AirStmt::CallIndirect {
            dst,
            table_index,
            args,
            ..
        } => (
            *dst,
            std::iter::once(*table_index)
                .chain(args.iter().copied())
                .collect(),
        ),
        AirStmt::GrantBegin { cap_var, .. } => (None, vec![*cap_var]),
        AirStmt::RegionBegin {
            limit_var,
            save_var,
            ..
        } => (Some(*save_var), vec![*limit_var]),
        AirStmt::RegionEnd {
            limit_var,
            save_var,
            ..
        } => (None, vec![*limit_var, *save_var]),
    }
}

fn successors(terminator: &AirTerminator) -> Vec<BlockId> {
    match terminator {
        AirTerminator::Return(_) | AirTerminator::Unreachable => vec![],
        AirTerminator::Jump(target) => vec![*target],
        AirTerminator::Loop {
            body_block,
            exit_block,
            ..
        } => vec![*body_block, *exit_block],
        AirTerminator::Branch {
            then_block,
            else_block,
            ..
        } => vec![*then_block, *else_block],
        AirTerminator::Dispatch { start, .. } => vec![*start],
    }
}

fn operands<'a>(nodes: &'a [Node], instruction: &Node) -> Result<&'a [Node], String> {
    let first = nodes
        .first()
        .ok_or("APC-1 missing function records")?
        .node_id;
    let start = instruction
        .node_id
        .checked_sub(first)
        .ok_or("APC-1 invalid instruction id")? as usize
        + 1;
    let end = start
        .checked_add(instruction.ceiling as usize)
        .ok_or("APC-1 operand span overflow")?;
    let values = nodes
        .get(start..end)
        .ok_or("APC-1 truncated operand span")?;
    for (position, operand) in values.iter().enumerate() {
        if !matches!(operand.op, Op::SemOperand)
            || operand.origin != instruction.node_id
            || operand.actual as usize != position
        {
            return Err("APC-1 noncanonical operand span".into());
        }
    }
    Ok(values)
}

fn check_reads(
    nodes: &[Node],
    instruction: &Node,
    reads: &[VarId],
    environment: &BTreeMap<VarId, VarId>,
    fixed: &BTreeMap<VarId, VarId>,
) -> Result<(), String> {
    let actual = operands(nodes, instruction)?
        .iter()
        .filter(|node| node.flags == 0)
        .map(|node| node.required)
        .collect::<Vec<_>>();
    let expected = reads
        .iter()
        .map(|base| {
            let version = environment
                .get(base)
                .or_else(|| fixed.get(base))
                .ok_or("APC-1 read of undeclared AIR value")?;
            semantic_ref(version.0, "APC-1 value")
        })
        .collect::<Result<Vec<_>, String>>()?;
    if actual != expected {
        return Err(format!(
            "APC-1 read mapping mismatch at instruction {}",
            instruction.node_id
        ));
    }
    Ok(())
}

pub(super) fn validate_function(
    function: &AirFunction,
    function_id: u32,
    bases: &[VarId],
    plan: &SemanticSsaPlan,
    nodes: &[Node],
    budget: &mut Budget,
    transfers: &mut Vec<Transfer>,
) -> Result<(), String> {
    budget.charge(nodes.len() + bases.len())?;
    let known = function
        .blocks
        .iter()
        .map(|block| block.id)
        .collect::<BTreeSet<_>>();
    if known.len() != function.blocks.len()
        || !known.contains(&function.entry_block)
        || plan.block_entries.keys().copied().collect::<BTreeSet<_>>() != known
        || !function
            .security
            .semantic_unreachable_blocks
            .is_subset(&known)
    {
        return Err("APC-1 invalid block inventory".into());
    }
    let initial = bases
        .iter()
        .enumerate()
        .map(|(index, base)| (*base, VarId(index as u32)))
        .collect::<BTreeMap<_, _>>();
    if plan.initial_versions != initial || initial.len() != bases.len() {
        return Err("APC-1 initial version mapping mismatch".into());
    }
    let mut declarations = initial
        .iter()
        .map(|(base, version)| (*version, *base))
        .collect::<BTreeMap<_, _>>();
    let mut definitions = BTreeMap::<VarId, Vec<VarId>>::new();
    let mut definition_count = 0;
    for block in &function.blocks {
        for (index, statement) in block.stmts.iter().enumerate() {
            let (destination, reads) = statement_shape(statement);
            budget.charge(1 + reads.len())?;
            if let Some(base) = destination {
                let version = *plan
                    .definition_versions
                    .get(&(block.id, index as u32))
                    .ok_or("APC-1 missing definition version")?;
                if !initial.contains_key(&base) || declarations.insert(version, base).is_some() {
                    return Err("APC-1 definition is undeclared or reuses a version".into());
                }
                definitions.entry(base).or_default().push(version);
                definition_count += 1;
            }
        }
    }
    if definition_count != plan.definition_versions.len() {
        return Err("APC-1 spurious definition version".into());
    }
    let parameters = function
        .params
        .iter()
        .map(|(base, _)| *base)
        .collect::<BTreeSet<_>>();
    let fixed = bases
        .iter()
        .filter_map(|base| {
            let defs = definitions.get(base).map(Vec::as_slice).unwrap_or(&[]);
            (defs.is_empty() || (defs.len() == 1 && !parameters.contains(base)))
                .then(|| (*base, defs.first().copied().unwrap_or(initial[base])))
        })
        .collect::<BTreeMap<_, _>>();
    if plan.fixed_versions != fixed {
        return Err("APC-1 fixed version classification mismatch".into());
    }
    let tracked = bases
        .iter()
        .filter(|base| !fixed.contains_key(base))
        .copied()
        .collect::<BTreeSet<_>>();
    let mut instructions = BTreeMap::<BlockId, Vec<&Node>>::new();
    for node in nodes {
        if matches!(node.op, Op::SemInstruction) {
            let block = node
                .actual
                .checked_sub(1)
                .map(BlockId)
                .ok_or("APC-1 zero block id")?;
            if node.origin != function_id || !known.contains(&block) {
                return Err("APC-1 instruction owner mismatch".into());
            }
            instructions.entry(block).or_default().push(node);
        }
    }
    let mut exits = BTreeMap::new();
    let mut phi_operands = BTreeMap::<(VarId, VarId), (u32, u32)>::new();
    for block in &function.blocks {
        budget.charge(tracked.len())?;
        let entries = &plan.block_entries[&block.id];
        if entries.keys().copied().collect::<BTreeSet<_>>() != tracked {
            return Err("APC-1 incomplete block entry mapping".into());
        }
        // Single-definition values share one immutable map. Copying all fixed locals into
        // every block would turn a small CFG certificate into quadratic retained memory.
        let mut environment = entries.clone();
        let emitted = instructions
            .get(&block.id)
            .ok_or("APC-1 block has no instructions")?;
        let phis = plan.phis.get(&block.id).map(Vec::as_slice).unwrap_or(&[]);
        if emitted.len() != phis.len() + block.stmts.len() + 1 {
            return Err("APC-1 instruction inventory mismatch".into());
        }
        let mut phi_bases = BTreeSet::new();
        for ((destination, base, sources), instruction) in phis.iter().zip(emitted) {
            if !tracked.contains(base)
                || !phi_bases.insert(*base)
                || entries.get(base) != Some(destination)
                || declarations.insert(*destination, *base).is_some()
                || instruction.aux != 2
                || instruction.required != semantic_ref(destination.0, "phi")?
            {
                return Err("APC-1 invalid phi definition".into());
            }
            let actual = operands(nodes, instruction)?;
            budget.charge(actual.len())?;
            if actual.len() != sources.len()
                || actual.iter().zip(sources).any(|(operand, source)| {
                    operand.flags != 0 || source.0.checked_add(1) != Some(operand.required)
                })
            {
                return Err("APC-1 emitted phi differs from witness".into());
            }
            for (operand, source) in actual.iter().zip(sources) {
                phi_operands.insert(
                    (*destination, *source),
                    (instruction.node_id, operand.node_id),
                );
            }
        }
        for (index, statement) in block.stmts.iter().enumerate() {
            let instruction = emitted[phis.len() + index];
            let (destination, reads) = statement_shape(statement);
            check_reads(nodes, instruction, &reads, &environment, &fixed)?;
            let expected = match destination {
                None => 0,
                Some(base) => {
                    let version = plan.definition_versions[&(block.id, index as u32)];
                    if tracked.contains(&base) {
                        environment.insert(base, version);
                    }
                    semantic_ref(version.0, "definition")?
                }
            };
            if instruction.required != expected {
                return Err("APC-1 emitted destination mismatch".into());
            }
        }
        let terminator = emitted.last().expect("inventory includes terminator");
        let impossible = function
            .security
            .semantic_unreachable_blocks
            .contains(&block.id)
            || (matches!(block.terminator, AirTerminator::Return(None))
                && function.ret != AirType::Unit);
        let (reads, targets) = if impossible {
            (vec![], vec![])
        } else {
            match &block.terminator {
                AirTerminator::Return(value) => (value.iter().copied().collect(), vec![]),
                AirTerminator::Unreachable => (vec![], vec![]),
                AirTerminator::Jump(target) => (vec![], vec![*target]),
                AirTerminator::Branch {
                    cond,
                    then_block,
                    else_block,
                    merge_block,
                } => (
                    vec![*cond],
                    [*then_block, *else_block]
                        .into_iter()
                        .chain(*merge_block)
                        .collect(),
                ),
                AirTerminator::Loop {
                    cond,
                    body_block,
                    exit_block,
                } => (vec![*cond], vec![*body_block, *exit_block]),
                AirTerminator::Dispatch { start, exit } => (vec![], vec![*start, *exit]),
            }
        };
        check_reads(nodes, terminator, &reads, &environment, &fixed)?;
        let actual_targets = operands(nodes, terminator)?
            .iter()
            .filter(|node| node.flags == 1)
            .map(|node| node.required)
            .collect::<Vec<_>>();
        let expected_targets = targets
            .iter()
            .map(|block| semantic_ref(block.0, "block"))
            .collect::<Result<Vec<_>, _>>()?;
        if actual_targets != expected_targets
            || terminator.required != 0
            || (impossible && terminator.aux != 29)
        {
            return Err("APC-1 control-flow mapping mismatch".into());
        }
        exits.insert(block.id, environment);
    }
    let declared = plan
        .declarations
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    if declarations != declared
        || declared.len() != plan.declarations.len()
        || plan.phis.keys().any(|block| !known.contains(block))
    {
        return Err("APC-1 version declaration inventory mismatch".into());
    }
    // Check entry/phi identities only after every declaration has been collected (loops may
    // refer forward). An entry cannot use another variable's version as an equality shortcut.
    for entries in plan.block_entries.values() {
        for (base, version) in entries {
            if declared.get(version) != Some(base) {
                return Err("APC-1 entry version belongs to a different AIR variable".into());
            }
        }
    }
    let mut require_transfer = |base: VarId, source: VarId, target: VarId| -> Result<(), String> {
        budget.charge(1)?;
        if declared.get(&source) != Some(&base) || declared.get(&target) != Some(&base) {
            return Err("APC-1 transfer changes AIR variable identity".into());
        }
        if source == target {
            return Ok(());
        }
        if transfers.len() >= MAX_TRANSFERS {
            return Err("APC-1 transfer budget exceeded".into());
        }
        let (instruction, operand) = phi_operands
            .get(&(target, source))
            .copied()
            .ok_or("APC-1 missing predecessor dependency in emitted phi")?;
        transfers.push(Transfer {
            function: function_id,
            source: semantic_ref(source.0, "source")?,
            target: semantic_ref(target.0, "target")?,
            instruction,
            operand,
        });
        Ok(())
    };
    for base in &tracked {
        require_transfer(
            *base,
            initial[base],
            plan.block_entries[&function.entry_block][base],
        )?;
    }
    for block in &function.blocks {
        // Unreachable annotations are checked for inventory and emitted trap correspondence,
        // but their semantic justification still belongs to the trusted type/lowering boundary.
        if function
            .security
            .semantic_unreachable_blocks
            .contains(&block.id)
        {
            continue;
        }
        for successor in successors(&block.terminator) {
            if !known.contains(&successor) {
                return Err("APC-1 missing CFG successor".into());
            }
            if function
                .security
                .semantic_unreachable_blocks
                .contains(&successor)
            {
                continue;
            }
            for base in &tracked {
                require_transfer(
                    *base,
                    exits[&block.id][base],
                    plan.block_entries[&successor][base],
                )?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formal::{Projector, build_semantic_ssa_plan, project_v9_from_projector};
    use crate::registries::AuthorityRegistry;

    const BRANCH: &str = r#"
module projection_probe;
fn probe(b: bool) -> i64 {
    let mut x = 0;
    if b { x = 1; } else { x = 2; }
    return x;
}
"#;
    const LOOP: &str = r#"
module projection_probe;
fn probe(n: i64) -> i64 {
    let mut x = 0;
    for i in 0..n { x = x + i; }
    return x;
}
"#;

    fn fixture(source: &str) -> (AirFunction, Vec<VarId>, SemanticSsaPlan, Projector, Vec<u8>) {
        let compilation = crate::compile_named_module("projection_probe.sigil", source)
            .expect("the unmodified source must compile through the production validator");
        assert_eq!(compilation.air.functions.len(), 1);
        let function = compilation.air.functions[0].clone();
        let bases = function
            .params
            .iter()
            .chain(&function.locals)
            .map(|(base, _)| *base)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let plan = build_semantic_ssa_plan(&function, &bases).expect("valid SSA fixture");
        let mut projector = Projector::default();
        projector
            .project_semantic_program(&compilation.air, &AuthorityRegistry::default())
            .expect("canonical semantic fixture projects");
        let bytes = project_v9_from_projector(
            &mut projector,
            &compilation.air,
            &crate::compiler_context::CompilerContext::default(),
        )
        .expect("canonical v9 fixture");
        (function, bases, plan, projector, bytes)
    }

    fn validate(
        function: &AirFunction,
        bases: &[VarId],
        plan: &SemanticSsaPlan,
        nodes: &[Node],
    ) -> Result<Vec<Transfer>, String> {
        let mut transfers = vec![];
        validate_function(
            function,
            1,
            bases,
            plan,
            nodes,
            &mut Budget::default(),
            &mut transfers,
        )?;
        Ok(transfers)
    }

    #[test]
    fn projection_accepts_source_branches_loops_and_reordered_blocks() {
        for source in [BRANCH, LOOP] {
            let (mut function, bases, plan, projector, bytes) = fixture(source);
            let transfers = validate(&function, &bases, &plan, &projector.nodes)
                .expect("independent validation must accept canonical transfers");
            assert!(
                !transfers.is_empty(),
                "the witness must exercise actual join transfers"
            );
            let obligations = encode(&transfers).expect("small transfer fixture");
            assert_eq!(
                sigil_formal_bridge::validate_projection(&bytes, &obligations),
                Ok(0)
            );
            function.blocks.reverse();
            validate(&function, &bases, &plan, &projector.nodes)
                .expect("AIR vector order must not change CFG meaning");
        }
    }

    #[test]
    fn projection_rejects_stale_reads_and_reused_definitions() {
        let (function, bases, mut plan, mut projector, _) = fixture(LOOP);
        let definitions = plan
            .definition_versions
            .values()
            .map(|value| value.0 + 1)
            .collect::<BTreeSet<_>>();
        let phi_ids = plan
            .phis
            .values()
            .flatten()
            .map(|(value, _, _)| value.0 + 1)
            .collect::<BTreeSet<_>>();
        let owner = projector
            .nodes
            .iter()
            .find(|instruction| {
                matches!(instruction.op, Op::SemInstruction)
                    && !phi_ids.contains(&instruction.required)
                    && operands(&projector.nodes, instruction)
                        .expect("canonical operands")
                        .iter()
                        .any(|operand| {
                            operand.flags == 0 && definitions.contains(&operand.required)
                        })
            })
            .expect("loop reads a produced value")
            .node_id;
        let operand = projector
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(node.op, Op::SemOperand)
                    && node.origin == owner
                    && node.flags == 0
                    && definitions.contains(&node.required)
            })
            .expect("selected value operand");
        operand.required = 1;
        assert!(validate(&function, &bases, &plan, &projector.nodes).is_err());
        let (_, _, _, clean, _) = fixture(LOOP);
        *plan
            .definition_versions
            .values_mut()
            .next()
            .expect("loop defines a value") = VarId(0);
        assert!(validate(&function, &bases, &plan, &clean.nodes).is_err());
    }

    #[test]
    fn projection_rejects_missing_branch_and_backedge_inputs_even_when_plan_agrees() {
        for source in [BRANCH, LOOP] {
            let (function, bases, mut plan, mut projector, _) = fixture(source);
            let (destination, _, sources) = plan
                .phis
                .values_mut()
                .flatten()
                .find(|(_, _, sources)| sources.len() >= 2)
                .expect("fixture has a real join");
            let removed = sources[0];
            let replacement = sources[1];
            assert_ne!(removed, replacement);
            sources[0] = replacement;
            let instruction = projector
                .nodes
                .iter()
                .find(|node| {
                    matches!(node.op, Op::SemInstruction) && node.required == destination.0 + 1
                })
                .expect("phi is emitted")
                .node_id;
            let operand = projector
                .nodes
                .iter_mut()
                .find(|node| {
                    matches!(node.op, Op::SemOperand)
                        && node.origin == instruction
                        && node.required == removed.0 + 1
                })
                .expect("phi source exists");
            operand.required = replacement.0 + 1;
            assert!(
                validate(&function, &bases, &plan, &projector.nodes).is_err(),
                "matching planner and emitter mutations must still lose to independent CFG checks"
            );
        }
    }

    #[test]
    fn projection_rejects_wrong_successors_and_unreachable_annotation_drift() {
        let (mut function, bases, plan, mut projector, _) = fixture(BRANCH);
        let branch = function
            .blocks
            .iter()
            .find(|block| matches!(block.terminator, AirTerminator::Branch { .. }))
            .expect("branch block")
            .id;
        let owner = projector
            .nodes
            .iter()
            .rev()
            .find(|node| matches!(node.op, Op::SemInstruction) && node.actual == branch.0 + 1)
            .expect("branch terminator")
            .node_id;
        projector
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(node.op, Op::SemOperand) && node.origin == owner && node.flags == 1
            })
            .expect("branch target")
            .required = branch.0 + 1;
        assert!(validate(&function, &bases, &plan, &projector.nodes).is_err());
        let (_, _, _, clean, _) = fixture(BRANCH);
        function.security.semantic_unreachable_blocks.insert(branch);
        assert!(
            validate(&function, &bases, &plan, &clean.nodes).is_err(),
            "new unreachable annotations must agree with an emitted trap"
        );
        // Semantic justification of an annotation and a matching trap remains an explicit
        // premise; APC-1 cannot establish source match exhaustiveness by checking these fields.
    }

    #[test]
    fn projection_native_checker_rejects_mutated_phi_records_and_witnesses() {
        let (function, bases, plan, projector, bytes) = fixture(LOOP);
        let transfers =
            validate(&function, &bases, &plan, &projector.nodes).expect("valid fixture");
        let obligations = encode(&transfers).expect("small fixture");
        assert_eq!(
            sigil_formal_bridge::validate_projection(&bytes, &obligations),
            Ok(0)
        );
        let transfer = &transfers[0];
        for (record, offset, replacement) in [
            (transfer.instruction, 20, 0),   // scalar cannot stand in for a phi
            (transfer.instruction, 4, 0),    // wrong function
            (transfer.instruction, 12, 0),   // no phi destination
            (transfer.operand, 12, 0),       // missing incoming version
            (transfer.operand, 4, 0),        // wrong instruction owner
            (transfer.operand, 8, u32::MAX), // operand outside its owner's span
        ] {
            let mut mutated = bytes.clone();
            let start = 12 + (record as usize - 1) * 32 + offset;
            mutated[start..start + 4].copy_from_slice(&replacement.to_le_bytes());
            assert_eq!(
                sigil_formal_bridge::validate_v9_declarations(&mutated),
                Ok(0),
                "the mutant remains a decodable declaration envelope"
            );
            assert_ne!(
                sigil_formal_bridge::validate_projection(&mutated, &obligations),
                Ok(0)
            );
        }
        for field in 0..5 {
            let mut mutated = obligations.clone();
            mutated[8 + field * 4..12 + field * 4].copy_from_slice(&u32::MAX.to_le_bytes());
            assert_ne!(
                sigil_formal_bridge::validate_projection(&bytes, &mutated),
                Ok(0)
            );
        }
    }

    #[test]
    fn projection_refuses_truncated_oversized_and_unknown_certificate_shapes() {
        let (_, _, _, projector, bytes) = fixture(BRANCH);
        let obligations = encode(&projector.projection_transfers).expect("small fixture");
        assert_eq!(
            sigil_formal_bridge::validate_projection(&bytes, &obligations),
            Ok(0)
        );
        for length in 0..obligations.len() {
            assert_ne!(
                sigil_formal_bridge::validate_projection(&bytes, &obligations[..length]),
                Ok(0)
            );
        }
        for (offset, value) in [(0, 2_u32), (4, MAX_TRANSFERS as u32 + 1)] {
            let mut mutant = obligations.clone();
            mutant[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
            assert_ne!(
                sigil_formal_bridge::validate_projection(&bytes, &mutant),
                Ok(0)
            );
        }
        let mut trailing = obligations;
        trailing.push(0);
        assert_ne!(
            sigil_formal_bridge::validate_projection(&bytes, &trailing),
            Ok(0)
        );
        let (function, bases, plan, projector, _) = fixture(BRANCH);
        assert!(
            validate_function(
                &function,
                1,
                &bases,
                &plan,
                &projector.nodes,
                &mut Budget(MAX_WORK),
                &mut vec![]
            )
            .is_err()
        );
    }
}
