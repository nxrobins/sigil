//! The memory-lowering pass: expands each AIR `RecordConstruct` into a
//! `BumpAlloc` plus `StoreField`s, pricing it (and every pre-existing
//! `BumpAlloc`) with a leading `FuelDecrement` of `max(1, size/64)`. The
//! offsets stored here must equal the sequential width sums that
//! `air::build_field_registry` bakes into `LoadField`; skew silently
//! corrupts field reads. Records in a state-backed `$state` mono instance
//! allocate on the persistent channel (PPS-0). Infallible, diagnostic-free;
//! mirrored operand-exactly by `selfhost/air.sigil` (`docs/specs/sh-air.md`)
//! and pinned by `sigil-runtime/tests/air_differential.rs`.

use crate::air::{AirFunction, AirProgram, AirStmt, AirType, AirValue, VarId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationStrategy {
    ArenaPerActor,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryLowering {
    pub allocation_strategy: AllocationStrategy,
    pub inserted_allocations: usize,
    pub total_bytes_allocated: u32,
}

pub fn lower(program: AirProgram) -> (AirProgram, MemoryLowering) {
    let mut inserted_allocations = 0usize;
    let mut total_bytes_allocated = 0u32;

    let functions = program
        .functions
        .into_iter()
        .map(|mut function| {
            let (allocs, bytes) = lower_function(&mut function);
            inserted_allocations += allocs;
            total_bytes_allocated += bytes;
            function
        })
        .collect();

    (
        AirProgram { functions },
        MemoryLowering {
            allocation_strategy: AllocationStrategy::ArenaPerActor,
            inserted_allocations,
            total_bytes_allocated,
        },
    )
}

fn lower_function(function: &mut AirFunction) -> (usize, u32) {
    let mut allocs = 0usize;
    let mut bytes = 0u32;
    // PPS-0: record constructs inside a state-backed mono instance allocate their headers on the
    // persistent channel (a rehashed `Map`'s replacement `Vec` headers must outlive the dispatch).
    // The instance's NAME is the signal — the same one `air::lower_function` uses to set
    // `state_backed_alloc` — so this pass needs no extra context threading.
    let persistent_module = function.name.ends_with(crate::air::STATE_VEC_MONO_SUFFIX);

    // Build a lookup of var types from immutable borrow first
    let var_type = |var: VarId| -> AirType { function.var_type(var) };

    // Pre-compute flattening data for all blocks while we can still borrow immutably
    let block_rewrites: Vec<Vec<AirStmt>> = function
        .blocks
        .iter()
        .map(|block| {
            let mut lowered = Vec::with_capacity(block.stmts.len());
            for stmt in &block.stmts {
                match stmt {
                    AirStmt::Assign {
                        dst,
                        val: AirValue::RecordConstruct { fields },
                    } => {
                        let field_data: Vec<(VarId, AirType)> =
                            fields.iter().map(|(_, v)| (*v, var_type(*v))).collect();
                        // PPS-0: a record construct inside a state-backed instance allocates its
                        // header persistently (a rehashed `Map`'s replacement `Vec` headers).
                        let (stmts, size) = flatten_record(*dst, &field_data, persistent_module);
                        let fuel_cost = std::cmp::max(1, size / 64);
                        lowered.push(AirStmt::FuelDecrement { amount: fuel_cost });
                        lowered.extend(stmts);
                        allocs += 1;
                        bytes += size;
                    }
                    AirStmt::BumpAlloc {
                        dst,
                        size_bytes,
                        align,
                        persistent,
                    } => {
                        let fuel_cost = std::cmp::max(1, *size_bytes / 64);
                        lowered.push(AirStmt::FuelDecrement { amount: fuel_cost });
                        lowered.push(AirStmt::BumpAlloc {
                            dst: *dst,
                            size_bytes: *size_bytes,
                            align: *align,
                            persistent: *persistent,
                        });
                        allocs += 1;
                        bytes += *size_bytes;
                    }
                    other => {
                        lowered.push(other.clone());
                    }
                }
            }
            lowered
        })
        .collect();

    // Apply the rewrites
    for (block, new_stmts) in function.blocks.iter_mut().zip(block_rewrites) {
        block.stmts = new_stmts;
    }

    (allocs, bytes)
}

fn flatten_record(
    dst: VarId,
    fields: &[(VarId, AirType)],
    persistent: bool,
) -> (Vec<AirStmt>, u32) {
    let mut stmts = Vec::new();
    let mut total_size = 0u32;

    // Calculate field offsets and total size
    let mut offsets = Vec::with_capacity(fields.len());
    for (_, ty) in fields {
        offsets.push(total_size);
        total_size += ty.width();
    }

    // Emit BumpAlloc for the entire record
    stmts.push(AirStmt::BumpAlloc {
        dst,
        size_bytes: total_size,
        align: 8,
        persistent,
    });

    // Emit StoreField for each field
    for (i, (var, ty)) in fields.iter().enumerate() {
        if *ty == AirType::Unit {
            continue; // Skip zero-width fields
        }
        stmts.push(AirStmt::StoreField {
            base_ptr: dst,
            offset: offsets[i],
            val: *var,
            ty: *ty,
        });
    }

    (stmts, total_size)
}
