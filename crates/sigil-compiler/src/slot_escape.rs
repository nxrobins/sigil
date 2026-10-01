//! The slot escape gate (C013): a Z3-free, always-on structural rule that
//! makes the per-function, variable-keyed `Slot<Cap>` authority meet sound
//! in the presence of slot ALIASING.
//!
//! ## The hole this closes
//!
//! `Slot<Cap>` is non-linear and freely aliasable: a callee's `Slot<Fuel>`
//! parameter, an actor-state slot read in another handler, and `let s2 = s`
//! all name the SAME runtime cell under DIFFERENT AIR variables. Both
//! authority checkers key slot contents on the AIR variable of the put:
//!
//! * the Z3 prover (`air_capability_v2`) constrains a `SlotTake`'s authority
//!   to the meet of the `SlotPut`s made through the take's OWN variable inside
//!   the SAME function (`slot_authority` is local to `verify_function`), or
//!   to `BV 0` when there are none;
//! * the linked Lean CSIR verifier binds a slot parameter or a state slot to a
//!   fresh occupied cell at the cap type's full ceiling and checks a take from
//!   it AT THAT CEILING (CLAIMS.md, `empty_slot_take_*` theorems).
//!
//! So a RESTRICTED capability put through an alias is invisible to both: the
//! caller (or the taking handler) takes through its own variable, the meet
//! sees only its own full-authority put, and a call sink that requires full
//! authority accepts the restricted capability. The runtime has no facet
//! semantics (restrict is an identity alias), so these static gates and the
//! certificate they mint are the ONLY enforcement of facet authority.
//!
//! ## The rule (the boring limit)
//!
//! Reject every `slot_put(slot, cap)` whose `cap` is POSSIBLY RESTRICTED
//! unless `slot` is CONFINED. Both predicates are syntactic, per function,
//! and conservative; each is spelled out on its own function below with the
//! direction it fails in.
//!
//! * `cap` is FULL only when every definition of it, followed through
//!   `Assign`/`draw`/`split` chains, bottoms out in a source the sink
//!   invariant already proves full: a parameter of a non-closure function
//!   (every call, spawn, message and return sink requires the full mask —
//!   SR-002 — so what arrives through a parameter is full), a `mint`, an
//!   actor-state read (a cap-typed state field only ever holds a full origin,
//!   which is the SECOND rule below, C014, not an assumption), or a DIRECT
//!   call result (the callee's `Return` is a full-mask sink; a `CallIndirect`
//!   closure result or an `ExternCall` FFI result is not). Everything else —
//!   `.restrict`, a `slot_take`, a field or buffer load, a closure parameter,
//!   an unknown definition — is POSSIBLY RESTRICTED. Failure direction: an
//!   unclassified source counts as restricted (fail closed: over-rejection,
//!   never acceptance).
//! * `slot` is CONFINED only when it is defined exactly once, by `slot_new`
//!   in this function, and every read of it is the `slot` operand of a
//!   `slot_put`/`slot_take` here. Any other read — an `Assign` copy, a call,
//!   spawn or message argument, a field or state store, a closure capture, a
//!   return, a borrow — is an ESCAPE; a parameter or a state-field read is
//!   never confined. Failure direction: an unclassified use counts as an
//!   escape (fail closed).
//!
//! ## Why this makes the variable-keyed meet sound
//!
//! Every put into a NON-confined slot is now a full-authority put, so the
//! runtime content of any slot reachable through an alias (a parameter, a
//! state field, a copy, a captured or stored slot) is always full, and both
//! "checked at the ceiling" (Lean) and "meet of my own puts, else 0" (Z3) are
//! sound for takes from it: the Z3 meet over the taker's own puts is either
//! the full mask or the fail-closed empty meet, never an over-approximation of
//! the true content. A CONFINED slot has exactly one variable, so the taker's
//! own puts ARE all the puts, and the existing meet is exact. Nothing crosses
//! functions, so the Z3 constraint shape and the Lean cell binding stay as
//! they are; this gate is what licenses keeping them variable-keyed
//! (docs/RESIDUAL_RISKS.md SR-020).
//!
//! ## Where it runs
//!
//! Called from `capability::verify`'s structural phase, before the Z3
//! prover and independent of the `solver` feature, so a solver-off build
//! (the shipped CLI) enforces it too. Any diagnostic fails the compile.
//! The counts in `CapabilityReport` are deliberately untouched — the
//! certificate compares `checked_sites` byte-for-byte across toolchains and
//! that number is the PROVER's site count — so this gate reports no count at
//! all: `check_function` returns `()`, and its only output is diagnostics.
//!
//! ## What it rejects, stated as the predicate and not as the motive
//!
//! The motivating hole is a `.restrict`ed cap relayed through an alias, but
//! the RULE is wider than that motive and rejects programs with no `.restrict`
//! anywhere: a `slot_take` result is `Taken` (only as wide as that slot's
//! puts, which this gate does not track across functions), and an origin this
//! gate cannot classify is `Unknown`. So take-and-put-back through an
//! aliasable slot — a `Slot<Cap>` parameter, an actor-state slot, a copy — is
//! C013 even when the cap put back is the very cap just taken out and no
//! authority is lost. That is the fail-closed direction, and it is stated as
//! such in docs/RESIDUAL_RISKS.md SR-020 and docs/SOUNDNESS_MATRIX.md
//! SND-CAP-001; `slot_alias_escape.rs` pins it end to end.
//!
//! ## The second rule: a cap-typed actor-state field holds only a full origin (C014)
//!
//! The `StateRead => Full` classification above (and the same classification
//! in the Z3 prover, which gives a state-read cap variable the full mask, and
//! in the Lean verifier) was a PREMISE nothing enforced: the type checker
//! makes a non-`mut` state field writable only in `init` (T123) and forbids a
//! `mut` cap field (C011), but nothing checked the AUTHORITY of the value
//! `init` stores. `init(f: Fuel) { fuel = f.restrict(burn); }` compiled, every
//! handler then read `fuel` as full, and `use_full(fuel.draw(10))` — or a
//! `slot_put(hold, fuel.draw(10))` this gate waved through as a full put —
//! handed a restricted capability to a full-authority sink.
//!
//! So this module also rejects every `StateWrite` whose value is a capability
//! (`AirValueKind::Cap`/`StateCap`, the same kind test the prover uses) that
//! is not in the SAME full-origin set the slot rule uses: a bare `init`
//! parameter, a `mint`, an actor-state read or a direct call result, directly
//! or through `let`/`draw`/`split`. It runs over every function kind, not only
//! `init`, so a handler write to a cap field (already T123/C011 upstream) is
//! rejected here too rather than relied on. Failure direction: a cap value
//! with an unclassified origin is rejected (over-rejection, never acceptance);
//! a value the lowering did not kind as a capability is not a capability to
//! the prover either, so the two share one premise rather than this gate
//! adding a second one. The sound spelling is to store the bare parameter and
//! `.restrict(...)` the value read from the field at the point of use.

use std::collections::{HashMap, HashSet};

use crate::{
    air::{AirFunction, AirFunctionKind, AirStmt, AirTerminator, AirValue, VarId},
    diagnostics::{Diagnostic, codes},
};

/// Where a capability variable's value comes from, as far as this gate is
/// willing to trust it. Collected per definition site; a variable with
/// several definitions is full only if every one of them is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CapOrigin {
    /// A source the sink invariant proves full (mint, state read, direct
    /// call result).
    Full,
    /// Same authority as another variable (`Assign`, `draw`, `split`).
    Inherit(VarId),
    /// `.restrict(...)`: narrowed by construction.
    Restricted,
    /// `slot_take`: only as wide as the meet of that slot's puts.
    Taken,
    /// Any other definition: a field/buffer load, a deserialized payload, an
    /// indirect or extern call result, a literal. Fail closed: treated as
    /// possibly restricted.
    Unknown,
}

/// The single destination a statement defines, if any, and the origin it
/// gives a capability-kinded destination. TOTAL over `AirStmt` — no `_` arm —
/// so a new statement kind cannot be silently classified (the walker-totality
/// fence: an unhandled arm is a compile error, not a fail-open default).
fn stmt_definition(stmt: &AirStmt) -> Option<(VarId, CapOrigin)> {
    match stmt {
        AirStmt::Assign { dst, val } => Some((
            *dst,
            match val {
                AirValue::Var(src) => CapOrigin::Inherit(*src),
                AirValue::IntLit(_)
                | AirValue::FloatLit(_)
                | AirValue::BoolLit(_)
                | AirValue::StrLit(_)
                | AirValue::UnitLit
                | AirValue::Binary { .. }
                | AirValue::RecordConstruct { .. } => CapOrigin::Unknown,
            },
        )),
        AirStmt::CapDraw { dst, src, .. } | AirStmt::CapSplit { dst, src, .. } => {
            Some((*dst, CapOrigin::Inherit(*src)))
        }
        AirStmt::CapRestrict { dst, .. } => Some((*dst, CapOrigin::Restricted)),
        AirStmt::SlotTake { dst_cap, .. } => Some((*dst_cap, CapOrigin::Taken)),
        AirStmt::CapMint { dst, .. } => Some((*dst, CapOrigin::Full)),
        // A handler's prologue loads each immutable state field once. That
        // cap is full because C014 (below, this module) rejects every
        // `StateWrite` of a cap without a full origin, C011 forbids a `mut`
        // cap field and C010 forbids consuming a state cap; without C014 this
        // arm would be an unenforced premise (`init` could store a
        // `.restrict` result).
        AirStmt::StateRead { dst, .. } => Some((*dst, CapOrigin::Full)),
        // The callee's `Return` terminator is a full-mask sink in both the Z3
        // prover and the Lean verifier, so a returned cap is full.
        AirStmt::Call { dst, .. } => dst.map(|dst| (dst, CapOrigin::Full)),
        AirStmt::LoadField { dst, .. }
        | AirStmt::SecurityRelease { dst, .. }
        | AirStmt::MessageAsk { dst, .. }
        | AirStmt::ResultTry { dst, .. }
        | AirStmt::OptionTry { dst, .. }
        | AirStmt::ArrayOrSliceContains { dst, .. }
        | AirStmt::StrBytesEq { dst, .. }
        | AirStmt::SliceOptionElem { dst, .. }
        | AirStmt::SpawnActor { dst, .. }
        | AirStmt::SlotNew { dst, .. }
        | AirStmt::DeserializeMessage { dst, .. }
        | AirStmt::PromoteBytes { dst, .. }
        | AirStmt::BumpAlloc { dst, .. }
        | AirStmt::IntrinsicAlloc { dst, .. }
        | AirStmt::IntrinsicLoad8 { dst, .. }
        | AirStmt::IntrinsicCtEq { dst, .. }
        | AirStmt::IntrinsicCtSelect { dst, .. }
        | AirStmt::IntrinsicCtLt { dst, .. }
        | AirStmt::LoadDynamic { dst, .. }
        | AirStmt::WrapI64 { dst, .. }
        | AirStmt::ExtendU32 { dst, .. }
        | AirStmt::SignExtendI32 { dst, .. }
        | AirStmt::Borrow { dst, .. } => Some((*dst, CapOrigin::Unknown)),
        // Closure results and FFI results are not full-mask sinks this gate
        // can lean on (`CallIndirect` arguments are not sink-checked), so
        // they stay possibly restricted.
        AirStmt::CallIndirect { dst, .. } | AirStmt::ExternCall { dst, .. } => {
            dst.map(|dst| (dst, CapOrigin::Unknown))
        }
        AirStmt::StoreField { .. }
        | AirStmt::StateWrite { .. }
        | AirStmt::FuelDecrement { .. }
        | AirStmt::MessageSend { .. }
        | AirStmt::SlotPut { .. }
        | AirStmt::SerializeMessage { .. }
        | AirStmt::IntrinsicStore8 { .. }
        | AirStmt::StoreDynamic { .. }
        | AirStmt::TrapIf { .. }
        | AirStmt::GrantBegin { .. }
        | AirStmt::GrantEnd { .. }
        | AirStmt::RegionBegin { .. }
        | AirStmt::RegionEnd { .. } => None,
    }
}

/// Every variable a statement READS, paired with whether the read is the
/// `slot` operand of a `slot_put`/`slot_take` (the only reads a confined slot
/// may have). TOTAL over `AirStmt` — no `_` arm — for the same reason as
/// `stmt_definition`: an unlisted read would be an invisible escape.
///
/// Totality here is per FIELD, not merely per variant: every `VarId`-typed
/// field of every arm is either listed as a read or defined by
/// `stmt_definition`. That includes fields today's lowering only ever fills
/// with a buffer, a scratch cap or a saved bump pointer — `SecurityRelease`'s
/// `cap_scratch`, `SerializeMessage`'s `dst_buf`/`dst_len`, and the region
/// statements' `save_var`. Failure direction: listing a non-slot field as a
/// read can only over-report an escape (over-rejection); omitting one would
/// make a future lowering that does put a slot there invisible here, which is
/// the fail-open direction this gate must not have. `air_stmt_var_fields_are_
/// all_classified` fences the omission case.
fn stmt_reads(stmt: &AirStmt) -> Vec<(VarId, bool)> {
    let plain = |vars: Vec<VarId>| vars.into_iter().map(|v| (v, false)).collect::<Vec<_>>();
    match stmt {
        AirStmt::Assign { val, .. } => plain(match val {
            AirValue::Var(v) => vec![*v],
            AirValue::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
            AirValue::RecordConstruct { fields } => fields.iter().map(|(_, v)| *v).collect(),
            AirValue::IntLit(_)
            | AirValue::FloatLit(_)
            | AirValue::BoolLit(_)
            | AirValue::StrLit(_)
            | AirValue::UnitLit => Vec::new(),
        }),
        AirStmt::StoreField { base_ptr, val, .. } => plain(vec![*base_ptr, *val]),
        AirStmt::LoadField { base_ptr, .. } => plain(vec![*base_ptr]),
        AirStmt::StateRead { state_ptr, .. } => plain(vec![*state_ptr]),
        AirStmt::StateWrite { state_ptr, val, .. } => plain(vec![*state_ptr, *val]),
        AirStmt::SecurityRelease {
            src,
            cap,
            cap_scratch,
            ..
        } => plain(vec![*src, *cap, *cap_scratch]),
        AirStmt::Call { args, .. } => plain(args.clone()),
        AirStmt::FuelDecrement { .. } => Vec::new(),
        AirStmt::MessageSend {
            target,
            msg,
            payload_buf,
            payload_len,
            ..
        } => plain(vec![*target, *msg, *payload_buf, *payload_len]),
        AirStmt::MessageAsk {
            target,
            msg,
            payload_buf,
            payload_len,
            timeout,
            ..
        } => plain(vec![*target, *msg, *payload_buf, *payload_len, *timeout]),
        AirStmt::ResultTry { src, .. } | AirStmt::OptionTry { src, .. } => plain(vec![*src]),
        AirStmt::ArrayOrSliceContains {
            base_ptr,
            len,
            needle,
            idx,
            ..
        } => plain(vec![*base_ptr, *len, *needle, *idx]),
        AirStmt::StrBytesEq {
            lhs_data,
            lhs_len,
            rhs_data,
            rhs_len,
            idx,
            ..
        } => plain(vec![*lhs_data, *lhs_len, *rhs_data, *rhs_len, *idx]),
        AirStmt::SliceOptionElem { data_ptr, len, .. } => plain(vec![*data_ptr, *len]),
        AirStmt::SpawnActor { caps, fuel_cap, .. } => {
            let mut vars = caps.clone();
            vars.push(*fuel_cap);
            plain(vars)
        }
        AirStmt::CapRestrict { src, .. } => plain(vec![*src]),
        AirStmt::CapSplit { src, amount, .. } | AirStmt::CapDraw { src, amount, .. } => {
            plain(vec![*src, *amount])
        }
        AirStmt::CapMint { target, .. } => plain(vec![*target]),
        AirStmt::SlotNew { .. } => Vec::new(),
        AirStmt::SlotPut { slot, cap } => vec![(*slot, true), (*cap, false)],
        AirStmt::SlotTake { slot, .. } => vec![(*slot, true)],
        AirStmt::SerializeMessage {
            msg,
            args,
            dst_buf,
            dst_len,
        } => {
            let mut vars = vec![*msg, *dst_buf, *dst_len];
            vars.extend_from_slice(args);
            plain(vars)
        }
        AirStmt::DeserializeMessage {
            src_buf, src_len, ..
        } => plain(vec![*src_buf, *src_len]),
        AirStmt::PromoteBytes { src, len, .. } => plain(vec![*src, *len]),
        AirStmt::BumpAlloc { .. } => Vec::new(),
        AirStmt::IntrinsicAlloc { size, .. } => plain(vec![*size]),
        AirStmt::IntrinsicLoad8 { ptr, .. } => plain(vec![*ptr]),
        AirStmt::IntrinsicStore8 { ptr, val } => plain(vec![*ptr, *val]),
        AirStmt::IntrinsicCtEq { lhs, rhs, .. } | AirStmt::IntrinsicCtLt { lhs, rhs, .. } => {
            plain(vec![*lhs, *rhs])
        }
        AirStmt::IntrinsicCtSelect {
            cond,
            then_val,
            else_val,
            ..
        } => plain(vec![*cond, *then_val, *else_val]),
        AirStmt::LoadDynamic {
            base_ptr, index, ..
        } => plain(vec![*base_ptr, *index]),
        AirStmt::StoreDynamic {
            base_ptr,
            index,
            val,
            ..
        } => plain(vec![*base_ptr, *index, *val]),
        AirStmt::TrapIf { cond } => plain(vec![*cond]),
        AirStmt::WrapI64 { src, .. }
        | AirStmt::ExtendU32 { src, .. }
        | AirStmt::SignExtendI32 { src, .. } => plain(vec![*src]),
        AirStmt::CallIndirect {
            table_index, args, ..
        } => {
            let mut vars = vec![*table_index];
            vars.extend_from_slice(args);
            plain(vars)
        }
        AirStmt::GrantBegin { cap_var, .. } => plain(vec![*cap_var]),
        AirStmt::GrantEnd { .. } => Vec::new(),
        AirStmt::Borrow { src, .. } => plain(vec![*src]),
        AirStmt::ExternCall { args, .. } => plain(args.clone()),
        AirStmt::RegionBegin {
            limit_var,
            save_var,
            ..
        }
        | AirStmt::RegionEnd {
            limit_var,
            save_var,
            ..
        } => plain(vec![*limit_var, *save_var]),
    }
}

/// Every variable a terminator reads. A returned slot is an escape.
fn terminator_reads(terminator: &AirTerminator) -> Vec<VarId> {
    match terminator {
        AirTerminator::Return(value) => value.iter().copied().collect(),
        AirTerminator::Loop { cond, .. } | AirTerminator::Branch { cond, .. } => vec![*cond],
        AirTerminator::Jump(_) | AirTerminator::Unreachable | AirTerminator::Dispatch { .. } => {
            Vec::new()
        }
    }
}

/// Why a slot is not confined, for the diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SlotEscape {
    Parameter,
    NotSlotNewLocal,
    Escapes,
}

/// The confinement verdict for every variable used as a slot in `function`.
/// See the module doc for the predicate; this is its only implementation.
fn slot_escapes(function: &AirFunction) -> HashMap<VarId, Option<SlotEscape>> {
    let params: HashSet<VarId> = function.params.iter().map(|(v, _)| *v).collect();
    let mut definition_count: HashMap<VarId, usize> = HashMap::new();
    let mut slot_new_defined: HashSet<VarId> = HashSet::new();
    let mut escaping_reads: HashSet<VarId> = HashSet::new();
    let mut slot_operands: HashSet<VarId> = HashSet::new();
    for block in &function.blocks {
        for stmt in &block.stmts {
            if let Some((dst, _)) = stmt_definition(stmt) {
                *definition_count.entry(dst).or_default() += 1;
            }
            if let AirStmt::SlotNew { dst, .. } = stmt {
                slot_new_defined.insert(*dst);
            }
            for (var, is_slot_operand) in stmt_reads(stmt) {
                if is_slot_operand {
                    slot_operands.insert(var);
                } else {
                    escaping_reads.insert(var);
                }
            }
        }
        escaping_reads.extend(terminator_reads(&block.terminator));
    }
    slot_operands
        .into_iter()
        .map(|slot| {
            let verdict = if params.contains(&slot) {
                Some(SlotEscape::Parameter)
            } else if !slot_new_defined.contains(&slot)
                || definition_count.get(&slot).copied().unwrap_or(0) != 1
            {
                Some(SlotEscape::NotSlotNewLocal)
            } else if escaping_reads.contains(&slot) {
                Some(SlotEscape::Escapes)
            } else {
                None
            };
            (slot, verdict)
        })
        .collect()
}

/// The set of variables this gate accepts as FULL authority (see the module
/// doc). A least fixed point over `Inherit` edges: a variable joins only when
/// every one of its definitions is `Full` or inherits from a member. The
/// iteration is monotone (members are never removed) and bounded by the
/// variable count, so it terminates; anything it never reaches is possibly
/// restricted (fail closed).
fn full_authority_vars(
    function: &AirFunction,
    definitions: &HashMap<VarId, Vec<CapOrigin>>,
) -> HashSet<VarId> {
    // A closure's parameters arrive through `CallIndirect`, which is not a
    // sink in either checker, so they are not trusted. Every other function
    // kind's parameters come through a full-mask sink (call, spawn, message).
    let params_are_full = !matches!(function.kind, AirFunctionKind::Closure);
    let mut full: HashSet<VarId> = HashSet::new();
    if params_are_full {
        full.extend(
            function
                .params
                .iter()
                .map(|(v, _)| *v)
                .filter(|v| !definitions.contains_key(v)),
        );
    }
    loop {
        let mut changed = false;
        for (var, origins) in definitions {
            if full.contains(var) {
                continue;
            }
            let every_origin_full = origins.iter().all(|origin| match origin {
                CapOrigin::Full => true,
                CapOrigin::Inherit(src) => full.contains(src),
                CapOrigin::Restricted | CapOrigin::Taken | CapOrigin::Unknown => false,
            });
            if every_origin_full {
                full.insert(*var);
                changed = true;
            }
        }
        if !changed {
            return full;
        }
    }
}

/// The first non-full reason on a capability's definition chain, for the
/// diagnostic. Follows `Inherit` edges depth-first with a visited set so a
/// (malformed) cyclic chain cannot loop.
fn describe_cap_origin(
    var: VarId,
    definitions: &HashMap<VarId, Vec<CapOrigin>>,
    function: &AirFunction,
) -> String {
    let mut visited: HashSet<VarId> = HashSet::new();
    let mut stack = vec![var];
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        let Some(origins) = definitions.get(&current) else {
            if matches!(function.kind, AirFunctionKind::Closure) {
                return "is a closure parameter (closure arguments are not authority sinks)"
                    .to_owned();
            }
            continue;
        };
        for origin in origins {
            match origin {
                CapOrigin::Restricted => {
                    return "may carry a `.restrict`ed authority set".to_owned();
                }
                // Stated as the predicate, not the motive: a `slot_take`
                // result counts as possibly restricted even when that slot
                // only ever held full authority, because this gate does not
                // track a slot's contents across functions (SR-020).
                CapOrigin::Taken => {
                    return "came out of a `slot_take`, and every `slot_take` result counts as possibly restricted — even a full capability, even one put straight back into the slot it came from — because this gate does not track a slot's contents across functions"
                        .to_owned();
                }
                CapOrigin::Unknown => {
                    return "has no full-authority origin this gate recognises".to_owned();
                }
                CapOrigin::Inherit(src) => stack.push(*src),
                CapOrigin::Full => {}
            }
        }
    }
    "has no full-authority origin this gate recognises".to_owned()
}

/// The rule itself, appended to every C013 message so the author reads the
/// predicate the gate enforces and not only the one reason it found: which
/// origins count as full, and which slots may take anything else.
const C013_RULE: &str = "only a capability whose origin is a non-closure parameter, `mint`, an actor-state read or a direct call result (directly or through `let`, `draw` or `split`) may be put into a slot that other code can reach; anything else — a `.restrict` result, a `slot_take` result, a closure parameter or closure-call result, an FFI result, a field load — may only go into a `slot_new` local of this same function that is used by nothing but `slot_put`/`slot_take`";

/// The rule appended to every C014 message: which origins a cap-typed
/// actor-state field may be assigned, and the sound spelling.
const C014_RULE: &str = "a cap-typed actor-state field may only be assigned a capability whose origin is a non-closure parameter, `mint`, an actor-state read or a direct call result (directly or through `let`, `draw` or `split`), because every read of that field — in this gate, in the Z3 prover and in the Lean verifier — counts as FULL authority; assign the bare `init` parameter and `.restrict(...)` the value read from the field at the point of use";

/// Run the gate over one function, appending a C013 for every offending
/// `slot_put`. Returns nothing: this gate's site count is deliberately NOT
/// part of any report (see the module doc's "Where it runs"), and a count no
/// caller reads is a claim no test enforces.
pub fn check_function(function: &AirFunction, diagnostics: &mut Vec<Diagnostic>) {
    let mut definitions: HashMap<VarId, Vec<CapOrigin>> = HashMap::new();
    for block in &function.blocks {
        for stmt in &block.stmts {
            if let Some((dst, origin)) = stmt_definition(stmt) {
                definitions.entry(dst).or_default().push(origin);
            }
        }
    }
    let full = full_authority_vars(function, &definitions);
    let escapes = slot_escapes(function);

    for block in &function.blocks {
        for stmt in &block.stmts {
            let AirStmt::SlotPut { slot, cap } = stmt else {
                continue;
            };
            if full.contains(cap) {
                continue;
            }
            // Every slot operand was registered by `slot_escapes`; a missing
            // entry is impossible for a put we just saw, but fail closed
            // (treat as escaping) rather than trust the map.
            let Some(escape) = escapes
                .get(slot)
                .copied()
                .unwrap_or(Some(SlotEscape::Escapes))
            else {
                continue;
            };
            let slot_label = function.var_label(*slot);
            let cap_label = function.var_label(*cap);
            let slot_reason = match escape {
                SlotEscape::Parameter => {
                    format!("`{slot_label}` is a parameter, so other functions hold the same slot")
                }
                SlotEscape::NotSlotNewLocal => format!(
                    "`{slot_label}` is not a `slot_new` local of this function (an actor-state field or a copy of another slot)"
                ),
                SlotEscape::Escapes => format!(
                    "`{slot_label}` escapes this function (copied, passed, stored, captured or returned)"
                ),
            };
            let cap_reason = describe_cap_origin(*cap, &definitions, function);
            diagnostics.push(Diagnostic::error(
                codes::C013,
                format!(
                    "`slot_put({slot_label}, {cap_label})` in `{}`: `{cap_label}` {cap_reason}, and {slot_reason}. The rule: {C013_RULE} (the take-side authority meet is keyed on the taking function's own variable and cannot see a put through another name)",
                    function.name
                ),
                function.var_span(*cap).or_else(|| function.var_span(*slot)),
            ));
        }
    }

    // C014: every capability stored into actor state must have a full origin,
    // in `init` and in any other function kind alike (a handler write is
    // already T123/C011 upstream; this gate does not rely on that ordering).
    // The kind test is the prover's own (`is_cap`: `Cap` or `StateCap`), so a
    // non-cap state write (a scalar, a record, a `Slot`) is not this rule's
    // business. Failure direction: a cap value with no recognised full origin
    // is rejected — over-rejection, never acceptance.
    for block in &function.blocks {
        for stmt in &block.stmts {
            let AirStmt::StateWrite { val, offset, .. } = stmt else {
                continue;
            };
            if !function.var_kind(*val).is_cap() || full.contains(val) {
                continue;
            }
            let cap_label = function.var_label(*val);
            let cap_reason = describe_cap_origin(*val, &definitions, function);
            diagnostics.push(Diagnostic::error(
                codes::C014,
                format!(
                    "assignment of `{cap_label}` to a cap-typed actor-state field (state offset {offset}) in `{}`: `{cap_label}` {cap_reason}, and every later read of that field counts as full authority. The rule: {C014_RULE}",
                    function.name
                ),
                // Anchor at the stored value's def site; a value with no
                // recorded span (hand-built AIR) falls back to the function.
                Some(function.var_span(*val).unwrap_or(function.def_span)),
            ));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::check_function;
    use crate::air::{
        ActorTypeId, AirBlock, AirFunction, AirFunctionKind, AirStmt, AirTerminator, AirType,
        AirValue, AirValueKind, BlockId, VarId,
    };
    use crate::ast::{Ring, TaintLabel};

    /// `fn fill(s: Slot<Fuel>, c: Fuel)` whose body is `stmts`; `c` is
    /// VarId(1), `s` VarId(0), locals VarId(2..).
    fn fill(
        kind: AirFunctionKind,
        stmts: Vec<AirStmt>,
        locals: &[(VarId, AirValueKind)],
    ) -> AirFunction {
        let mut value_kinds: BTreeMap<VarId, AirValueKind> = [
            (VarId(0), AirValueKind::Slot("Fuel".to_owned())),
            (VarId(1), AirValueKind::Cap("Fuel".to_owned())),
        ]
        .into_iter()
        .collect();
        let mut debug_names: BTreeMap<VarId, String> =
            [(VarId(0), "s".to_owned()), (VarId(1), "c".to_owned())]
                .into_iter()
                .collect();
        let mut local_types = Vec::new();
        for (var, k) in locals {
            value_kinds.insert(*var, k.clone());
            debug_names.insert(*var, format!("v{}", var.0));
            local_types.push((*var, AirType::Ptr));
        }
        AirFunction {
            name: "sigil::fill".to_owned(),
            export_name: "sigil__fill".to_owned(),
            ring: Ring::default(),
            kind,
            params: vec![(VarId(0), AirType::Ptr), (VarId(1), AirType::Ptr)],
            ret: AirType::Unit,
            locals: local_types,
            value_kinds,
            debug_names,
            blocks: vec![AirBlock {
                id: BlockId(0),
                stmts,
                terminator: AirTerminator::Return(None),
            }],
            entry_block: BlockId(0),
            def_span: Default::default(),
            debug_spans: Default::default(),
            block_static_multiplicity: Vec::new(),
            security: Default::default(),
        }
    }

    fn codes_of(function: &AirFunction) -> Vec<&'static str> {
        let mut diagnostics = Vec::new();
        check_function(function, &mut diagnostics);
        diagnostics.iter().map(|d| d.code().as_str()).collect()
    }

    /// SC-P4 anti-stub: the planted violation (a restricted cap put through
    /// a slot PARAMETER) is detected, exactly once, as C013.
    #[test]
    fn restricted_put_into_a_parameter_slot_is_c013() {
        let f = fill(
            AirFunctionKind::ModuleFunction,
            vec![
                AirStmt::CapRestrict {
                    dst: VarId(2),
                    src: VarId(1),
                    restriction_mask: 1,
                },
                AirStmt::SlotPut {
                    slot: VarId(0),
                    cap: VarId(2),
                },
            ],
            &[(VarId(2), AirValueKind::Cap("Fuel".to_owned()))],
        );
        assert_eq!(codes_of(&f), vec!["C013"]);
    }

    /// The clean negative: the same shape putting the FULL parameter cap is
    /// silent (the fixture-18 cross-handler pattern), so the detector is
    /// not simply firing on every put.
    #[test]
    fn full_put_into_a_parameter_slot_is_clean() {
        let f = fill(
            AirFunctionKind::ModuleFunction,
            vec![AirStmt::SlotPut {
                slot: VarId(0),
                cap: VarId(1),
            }],
            &[],
        );
        assert!(codes_of(&f).is_empty());
    }

    /// A confined local slot (`slot_new` here, used only by put/take) may
    /// hold a restricted cap: the Z3 meet over that one variable is exact.
    #[test]
    fn restricted_put_into_a_confined_local_slot_is_clean() {
        let f = fill(
            AirFunctionKind::ModuleFunction,
            vec![
                AirStmt::SlotNew {
                    dst: VarId(3),
                    cap_type: "Fuel".to_owned(),
                },
                AirStmt::CapRestrict {
                    dst: VarId(2),
                    src: VarId(1),
                    restriction_mask: 1,
                },
                AirStmt::SlotPut {
                    slot: VarId(3),
                    cap: VarId(2),
                },
                AirStmt::SlotTake {
                    dst_cap: VarId(4),
                    slot: VarId(3),
                },
            ],
            &[
                (VarId(2), AirValueKind::Cap("Fuel".to_owned())),
                (VarId(3), AirValueKind::Slot("Fuel".to_owned())),
                (VarId(4), AirValueKind::Cap("Fuel".to_owned())),
            ],
        );
        assert!(codes_of(&f).is_empty());
    }

    /// The same confined slot, copied once (`let s2 = s`), escapes: the
    /// restricted put through EITHER name is C013.
    #[test]
    fn a_copied_local_slot_escapes() {
        let f = fill(
            AirFunctionKind::ModuleFunction,
            vec![
                AirStmt::SlotNew {
                    dst: VarId(3),
                    cap_type: "Fuel".to_owned(),
                },
                AirStmt::Assign {
                    dst: VarId(5),
                    val: AirValue::Var(VarId(3)),
                },
                AirStmt::CapRestrict {
                    dst: VarId(2),
                    src: VarId(1),
                    restriction_mask: 1,
                },
                AirStmt::SlotPut {
                    slot: VarId(3),
                    cap: VarId(2),
                },
            ],
            &[
                (VarId(2), AirValueKind::Cap("Fuel".to_owned())),
                (VarId(3), AirValueKind::Slot("Fuel".to_owned())),
                (VarId(5), AirValueKind::Slot("Fuel".to_owned())),
            ],
        );
        assert_eq!(codes_of(&f), vec!["C013"]);
    }

    /// A cap TAKEN from a slot is possibly restricted, so relaying it into an
    /// escaping slot is C013 even with no `.restrict` in sight.
    #[test]
    fn a_taken_cap_relayed_into_a_parameter_slot_is_c013() {
        let f = fill(
            AirFunctionKind::ModuleFunction,
            vec![
                AirStmt::SlotNew {
                    dst: VarId(3),
                    cap_type: "Fuel".to_owned(),
                },
                AirStmt::SlotPut {
                    slot: VarId(3),
                    cap: VarId(1),
                },
                AirStmt::SlotTake {
                    dst_cap: VarId(4),
                    slot: VarId(3),
                },
                AirStmt::SlotPut {
                    slot: VarId(0),
                    cap: VarId(4),
                },
            ],
            &[
                (VarId(3), AirValueKind::Slot("Fuel".to_owned())),
                (VarId(4), AirValueKind::Cap("Fuel".to_owned())),
            ],
        );
        assert_eq!(codes_of(&f), vec!["C013"]);
    }

    /// The source census behind `stmt_reads`'s per-FIELD totality: for every
    /// `AirStmt` variant, every `VarId`-typed field must be NAMED in that
    /// variant's pattern in `stmt_reads` or in `stmt_definition`. A field left
    /// behind a `..` in both is a variable this gate never sees, which is the
    /// fail-open direction — a slot that reached such a field would look
    /// confined while escaping. Returns the offenders as `Variant.field`.
    ///
    /// `gate_src` is the text of the two walkers ONLY (`walker_src`): scanning
    /// the whole file would let the statements CONSTRUCTED by the tests below
    /// name the fields and make this census vacuous.
    fn unclassified_var_fields(air_src: &str, gate_src: &str) -> Vec<String> {
        let mut offenders = Vec::new();
        for (variant, fields) in air_stmt_var_fields(air_src) {
            let patterns = patterns_for(gate_src, &variant);
            for field in fields {
                let named = patterns.iter().any(|pattern| {
                    pattern
                        .split(|c: char| !c.is_alphanumeric() && c != '_')
                        .any(|token| token == field)
                });
                if !named {
                    offenders.push(format!("{variant}.{field}"));
                }
            }
        }
        offenders
    }

    /// `(variant, VarId-typed field names)` for every arm of `enum AirStmt`.
    fn air_stmt_var_fields(air_src: &str) -> Vec<(String, Vec<String>)> {
        let body = braced_body(
            air_src,
            air_src.find("pub enum AirStmt").expect("AirStmt exists"),
        );
        // Strip line comments BEFORE splitting: a comma inside a doc comment
        // would otherwise cut a variant in half and hide its fields.
        let body = body
            .lines()
            .map(|line| line.split("//").next().unwrap_or(""))
            .collect::<Vec<_>>()
            .join("\n");
        let mut variants = Vec::new();
        let mut depth = 0usize;
        let mut current = String::new();
        for ch in body.chars() {
            match ch {
                '{' => depth += 1,
                '}' => depth = depth.saturating_sub(1),
                _ => {}
            }
            if ch == ',' && depth == 0 {
                variants.push(std::mem::take(&mut current));
            } else {
                current.push(ch);
            }
        }
        variants.push(current);
        let mut out = Vec::new();
        for variant in variants {
            let Some((head, rest)) = variant.split_once('{') else {
                continue;
            };
            let name = head.trim().to_owned();
            if name.is_empty() {
                continue;
            }
            let fields = rest
                .split(',')
                .filter_map(|field| field.split_once(':'))
                .filter(|(_, ty)| ty.contains("VarId"))
                .map(|(field, _)| field.trim().to_owned())
                .collect();
            out.push((name, fields));
        }
        out
    }

    /// Every `AirStmt::<variant> { … }` pattern in `gate_src`, as text.
    fn patterns_for(gate_src: &str, variant: &str) -> Vec<String> {
        let needle = format!("AirStmt::{variant}");
        let mut patterns = Vec::new();
        let mut from = 0usize;
        while let Some(found) = gate_src[from..].find(&needle) {
            let at = from + found + needle.len();
            from = at;
            let rest = gate_src[at..].trim_start();
            // Reject a longer variant name that merely starts with this one.
            if rest.starts_with(|c: char| c.is_alphanumeric() || c == '_') {
                continue;
            }
            if rest.starts_with('{') {
                patterns.push(braced_body(gate_src, at).to_owned());
            }
        }
        patterns
    }

    /// The two walkers' bodies, concatenated — the only text the census reads.
    fn walker_src(src: &str) -> String {
        ["fn stmt_definition", "fn stmt_reads"]
            .into_iter()
            .map(|name| braced_body(src, src.find(name).expect("both walkers exist")))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// The text between the first `{` at or after `from` and its match.
    fn braced_body(src: &str, from: usize) -> &str {
        let open = from + src[from..].find('{').expect("a braced body follows");
        let mut depth = 0usize;
        for (offset, ch) in src[open..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return &src[open + 1..open + offset];
                    }
                }
                _ => {}
            }
        }
        panic!("unbalanced braces from {from}");
    }

    /// Per-field totality: no `VarId` field of any `AirStmt` variant is
    /// invisible to this gate's walkers.
    #[test]
    fn air_stmt_var_fields_are_all_classified() {
        let offenders = unclassified_var_fields(
            include_str!("air.rs"),
            &walker_src(include_str!("slot_escape.rs")),
        );
        assert_eq!(
            offenders,
            Vec::<String>::new(),
            "every VarId field must be named in stmt_reads or stmt_definition"
        );
    }

    /// SC-P4 anti-stub for the census above: hiding a field behind `..` in the
    /// gate source is detected, so the census is not vacuously green.
    #[test]
    fn anti_stub_a_field_hidden_behind_a_rest_pattern_is_reported() {
        let gate_src = walker_src(include_str!("slot_escape.rs"));
        let planted = gate_src.replace(
            "AirStmt::SlotPut { slot, cap } => vec![(*slot, true), (*cap, false)],",
            "AirStmt::SlotPut { slot, .. } => vec![(*slot, true)],",
        );
        assert_ne!(planted, gate_src, "the plant must change the gate source");
        assert_eq!(
            unclassified_var_fields(include_str!("air.rs"), &planted),
            vec!["SlotPut.cap".to_owned()],
            "the census must report the field the plant hid"
        );
    }

    /// A closure's parameters are NOT trusted as full (indirect calls are not
    /// sinks), so a closure putting its own parameter into a captured slot
    /// parameter is C013 where a module function's identical body is clean.
    #[test]
    fn closure_parameters_are_not_trusted_as_full() {
        let body = || {
            vec![AirStmt::SlotPut {
                slot: VarId(0),
                cap: VarId(1),
            }]
        };
        assert_eq!(
            codes_of(&fill(AirFunctionKind::Closure, body(), &[])),
            vec!["C013"]
        );
        assert!(codes_of(&fill(AirFunctionKind::ModuleFunction, body(), &[])).is_empty());
    }

    // ── C014: a cap-typed actor-state field holds only a full origin ─────────

    /// `init(s: Slot<Fuel>, c: Fuel)` of actor `Vault`; same VarId layout as
    /// `fill`, so `c` is VarId(1) and locals start at VarId(2).
    fn vault_init(stmts: Vec<AirStmt>, locals: &[(VarId, AirValueKind)]) -> AirFunction {
        fill(
            AirFunctionKind::ActorInit {
                actor: "Vault".to_owned(),
                actor_type: ActorTypeId(1),
                is_entry: false,
            },
            stmts,
            locals,
        )
    }

    /// `fuel = <val>` — the lowering of an actor-state assignment.
    fn state_write(val: VarId) -> AirStmt {
        AirStmt::StateWrite {
            state_ptr: VarId(0),
            offset: 0,
            val,
            ty: AirType::Ptr,
            label: TaintLabel::Public,
        }
    }

    /// SC-P4 anti-stub: the planted premise failure — `init` storing a
    /// `.restrict` result into a cap-typed state field — is detected, exactly
    /// once, as C014 (the b0a repro: `init(f: Fuel) { fuel = f.restrict(burn); }`).
    #[test]
    fn init_storing_a_restricted_cap_into_state_is_c014() {
        let f = vault_init(
            vec![
                AirStmt::CapRestrict {
                    dst: VarId(2),
                    src: VarId(1),
                    restriction_mask: 1,
                },
                state_write(VarId(2)),
            ],
            &[(VarId(2), AirValueKind::Cap("Fuel".to_owned()))],
        );
        assert_eq!(codes_of(&f), vec!["C014"]);
    }

    /// The clean negatives: storing the bare parameter, and storing a `draw`
    /// off it (an `Inherit` chain into a parameter), are the documented
    /// spellings and stay silent — so the detector is not firing on every
    /// state write of a capability.
    #[test]
    fn init_storing_its_bare_or_drawn_parameter_is_clean() {
        assert!(codes_of(&vault_init(vec![state_write(VarId(1))], &[])).is_empty());
        let drawn = vault_init(
            vec![
                AirStmt::CapDraw {
                    dst: VarId(2),
                    src: VarId(1),
                    amount: VarId(3),
                },
                state_write(VarId(2)),
            ],
            &[
                (VarId(2), AirValueKind::Cap("Fuel".to_owned())),
                (VarId(3), AirValueKind::Copy),
            ],
        );
        assert!(codes_of(&drawn).is_empty());
    }

    /// A `slot_take` result stored into state is C014: it is only as wide as
    /// that slot's puts, which nothing tracks across functions.
    #[test]
    fn init_storing_a_slot_take_result_into_state_is_c014() {
        let f = vault_init(
            vec![
                AirStmt::SlotTake {
                    dst_cap: VarId(2),
                    slot: VarId(0),
                },
                state_write(VarId(2)),
            ],
            &[(VarId(2), AirValueKind::Cap("Fuel".to_owned()))],
        );
        assert_eq!(codes_of(&f), vec!["C014"]);
    }

    /// The rule is not `init`-only: the same restricted store in a HANDLER
    /// body is C014 here as well (the type checker's T123/C011 reject it
    /// earlier in the real pipeline; this gate does not lean on that order).
    #[test]
    fn a_handler_storing_a_restricted_cap_into_state_is_c014_too() {
        let f = fill(
            AirFunctionKind::ActorHandler {
                actor: "Vault".to_owned(),
                actor_type: ActorTypeId(1),
                handler: "Narrow".to_owned(),
                handler_id: crate::air::HandlerId(7),
                is_entry: false,
            },
            vec![
                AirStmt::CapRestrict {
                    dst: VarId(2),
                    src: VarId(1),
                    restriction_mask: 1,
                },
                state_write(VarId(2)),
            ],
            &[(VarId(2), AirValueKind::Cap("Fuel".to_owned()))],
        );
        assert_eq!(codes_of(&f), vec!["C014"]);
    }

    /// A state write whose value is NOT a capability (a scalar counter, the
    /// `mut n: i64` idiom) is outside this rule even when its origin is
    /// unclassifiable — the kind test is what scopes C014 to cap fields.
    #[test]
    fn a_non_cap_state_write_is_not_c014() {
        let f = vault_init(
            vec![
                AirStmt::Assign {
                    dst: VarId(2),
                    val: AirValue::IntLit(0),
                },
                state_write(VarId(2)),
            ],
            &[(VarId(2), AirValueKind::Copy)],
        );
        assert!(codes_of(&f).is_empty());
    }
}
