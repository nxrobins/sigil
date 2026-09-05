//! The AIR ownership verifier: the linear move-checker run over each
//! function's CFG. Values whose `AirValueKind::is_linear()` holds (caps,
//! state caps, `Linear`-kinded values) are consumed at most once; the
//! eleven `MoveKind` sites let the O001 message name WHERE the earlier
//! move happened, with per-kind recovery hints.
//!
//! Invariants owned here:
//! * Move/borrow state propagates over control flow: a block's entry state
//!   is the may-move/may-borrow union of all reachable CFG predecessors,
//!   joins and loop back-edges included; returning paths do not flow into
//!   sibling continuations.
//! * `consumed_vars` mirrors `apply_moves`: O007 (move-while-borrowed)
//!   uses the same consuming-site census as O001, so a new move site
//!   cannot silently bypass the borrow check.
//! * M4 borrow-only state caps: a capability read from immutable actor
//!   state may be consumed ONLY during the construction phase (an actor's
//!   own `init`, or the entry actor's boot `Start` handler); every other
//!   consume -- an escaping `Return` included -- is C010.
//!
//! Failure discipline: typed diagnostics (O001, O007, C010), and any
//! diagnostic fails the compile. A malformed CFG (duplicate block ids,
//! missing entry block, dangling block references) rejects with I001
//! BEFORE dataflow rather than panicking. Proofs: docs/CLAIMS.md ledgers
//! the CFG-propagation and fail-closed-malformed-AIR claims against pins
//! in `crates/sigil-runtime/tests/own_check_differential.rs` (the
//! `own0_*` fns and `malformed_air_cfg_fails_closed_without_panicking`);
//! `docs/specs/typestate-in-sigil.md` leans on this pass for O001
//! use-after-transition and O007.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    air::{
        AirFunction, AirFunctionKind, AirProgram, AirStmt, AirTerminator, AirValue, AirValueKind,
        BlockId, VarId,
    },
    diagnostics::{Diagnostic, codes},
};

/// What kind of operation consumed a linear value. Used to produce O001
/// diagnostics that tell the policy author *where* the move happened, not
/// just that it did. Mapping is exhaustive over the move sites in
/// `apply_moves` — adding a new variant requires updating that match.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MoveKind {
    Spawn,
    Send,
    Ask,
    Call,
    CallIndirect,
    Restrict,
    Split,
    RecordField,
    ResultTry,
    OptionTry,
    Reassign,
}

impl MoveKind {
    /// Short phrase describing the move site, embedded in the O001 message.
    fn describe(self) -> &'static str {
        match self {
            MoveKind::Spawn => "passed to `spawn`",
            MoveKind::Send => "sent in a message",
            MoveKind::Ask => "sent in an `ask`",
            MoveKind::Call => "passed to a function call",
            MoveKind::CallIndirect => "passed to a closure call",
            MoveKind::Restrict => "consumed by `.restrict(...)`",
            MoveKind::Split => "consumed by `.split(...)`",
            MoveKind::RecordField => "stored into a record field",
            MoveKind::ResultTry => "unwrapped by `?`",
            MoveKind::OptionTry => "unwrapped by `?`",
            MoveKind::Reassign => "rebound to another name",
        }
    }

    /// Per-call-site hint tailored to the move kind. Empty string if the
    /// registry default is sufficient.
    fn recovery_hint(self) -> &'static str {
        match self {
            MoveKind::Spawn | MoveKind::Send | MoveKind::Ask => {
                "If you need to retain a portion, use `.split(N)` before this move \
                 — it returns a fresh sub-capability without consuming the original."
            }
            MoveKind::Call | MoveKind::CallIndirect => {
                "If the callee only needs partial authority, pass `.restrict(...)` \
                 instead of the bare capability; the original then remains usable."
            }
            MoveKind::Restrict | MoveKind::Split => {
                "`.restrict` and `.split` consume their receiver. Bind the result \
                 to a new name and use that name from here on."
            }
            MoveKind::RecordField
            | MoveKind::ResultTry
            | MoveKind::OptionTry
            | MoveKind::Reassign => "",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipReport {
    pub verified_functions: usize,
    pub move_sites: usize,
    pub linear_values_checked: usize,
}

pub fn verify(program: &AirProgram) -> Result<OwnershipReport, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let mut move_sites = 0usize;
    let mut linear_values_checked = 0usize;

    for function in &program.functions {
        let (function_move_sites, function_linear_checks) =
            verify_function(function, &mut diagnostics);
        move_sites += function_move_sites;
        linear_values_checked += function_linear_checks;
    }

    if diagnostics.is_empty() {
        Ok(OwnershipReport {
            verified_functions: program.functions.len(),
            move_sites,
            linear_values_checked,
        })
    } else {
        Err(diagnostics)
    }
}

/// M4 boot carve-out: consuming a capability read from immutable actor state is
/// permitted ONLY during the construction phase — an actor's own `init`, or the
/// entry actor's boot `Start` handler (the same triple the type-checker uses at
/// `type_check/mod.rs` and the runtime dispatches via `handler_named("Start")`).
/// In every other handler a state cap is borrow-only (C010).
fn is_construction_phase(kind: &AirFunctionKind) -> bool {
    match kind {
        AirFunctionKind::ActorInit { .. } => true,
        AirFunctionKind::ActorHandler {
            handler, is_entry, ..
        } => *is_entry && handler == "Start",
        _ => false,
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct OwnershipState {
    moved: HashMap<VarId, MoveKind>,
    active_borrows: HashMap<VarId, VarId>,
}

fn state_cap_aliases(function: &AirFunction) -> HashSet<VarId> {
    let mut state_cap: HashSet<VarId> = function
        .params
        .iter()
        .chain(function.locals.iter())
        .filter(|(var, _)| matches!(function.var_kind(*var), AirValueKind::StateCap(_)))
        .map(|(var, _)| *var)
        .collect();

    loop {
        let mut changed = false;
        for block in &function.blocks {
            for stmt in &block.stmts {
                if let AirStmt::Assign {
                    dst,
                    val: AirValue::Var(src),
                } = stmt
                    && state_cap.contains(src)
                {
                    changed |= state_cap.insert(*dst);
                }
            }
        }
        if !changed {
            return state_cap;
        }
    }
}

fn block_successors(terminator: &AirTerminator) -> Vec<BlockId> {
    match terminator {
        AirTerminator::Return(_) | AirTerminator::Unreachable => Vec::new(),
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

/// Every block reference encoded by a terminator, including structural metadata that is not a
/// direct dataflow edge for ownership propagation.
fn block_references(terminator: &AirTerminator) -> Vec<BlockId> {
    match terminator {
        AirTerminator::Return(_) | AirTerminator::Unreachable => Vec::new(),
        AirTerminator::Jump(target) => vec![*target],
        AirTerminator::Loop {
            body_block,
            exit_block,
            ..
        } => vec![*body_block, *exit_block],
        AirTerminator::Branch {
            then_block,
            else_block,
            merge_block,
            ..
        } => {
            let mut references = vec![*then_block, *else_block];
            references.extend(merge_block);
            references
        }
        AirTerminator::Dispatch { start, exit } => vec![*start, *exit],
    }
}

fn malformed_air(function: &AirFunction, detail: impl std::fmt::Display) -> Box<Diagnostic> {
    Box::new(Diagnostic::error(
        codes::I001,
        format!(
            "malformed AIR in ownership verifier for `{}`: {detail}",
            function.name
        ),
        Some(function.def_span),
    ))
}

fn merge_state(target: &mut OwnershipState, incoming: &OwnershipState) -> bool {
    let before_moved = target.moved.len();
    let before_borrows = target.active_borrows.len();
    for (var, kind) in &incoming.moved {
        target.moved.entry(*var).or_insert(*kind);
    }
    for (borrow, source) in &incoming.active_borrows {
        target.active_borrows.entry(*borrow).or_insert(*source);
    }
    target.moved.len() != before_moved || target.active_borrows.len() != before_borrows
}

fn transfer_state(
    function: &AirFunction,
    block_index: usize,
    mut state: OwnershipState,
    state_cap: &HashSet<VarId>,
    is_boot: bool,
) -> OwnershipState {
    let mut discarded_diagnostics = Vec::new();
    for stmt in &function.blocks[block_index].stmts {
        if let AirStmt::Borrow { dst, src, .. } = stmt {
            state.active_borrows.insert(*dst, *src);
        }
        apply_moves(
            function,
            stmt,
            &mut state.moved,
            state_cap,
            is_boot,
            &mut discarded_diagnostics,
        );
    }
    state
}

fn block_entry_states(
    function: &AirFunction,
    state_cap: &HashSet<VarId>,
    is_boot: bool,
) -> Result<Vec<Option<OwnershipState>>, Box<Diagnostic>> {
    let mut indices = HashMap::new();
    for (index, block) in function.blocks.iter().enumerate() {
        if indices.insert(block.id, index).is_some() {
            return Err(malformed_air(
                function,
                format_args!("duplicate block id {:?}", block.id),
            ));
        }
    }
    let Some(&entry) = indices.get(&function.entry_block) else {
        return Err(malformed_air(
            function,
            format_args!("missing entry block {:?}", function.entry_block),
        ));
    };

    // Validate every encoded reference, including unreachable blocks and structural branch/
    // dispatch targets that are not direct ownership-dataflow successors.
    for block in &function.blocks {
        for target in block_references(&block.terminator) {
            if !indices.contains_key(&target) {
                return Err(malformed_air(
                    function,
                    format_args!("block {:?} targets missing block {target:?}", block.id),
                ));
            }
        }
    }

    let mut states = vec![None; function.blocks.len()];
    states[entry] = Some(OwnershipState::default());
    let mut work = VecDeque::from([entry]);

    while let Some(index) = work.pop_front() {
        let Some(input) = states[index].clone() else {
            return Err(malformed_air(
                function,
                format_args!(
                    "queued block {:?} has no entry state",
                    function.blocks[index].id
                ),
            ));
        };
        let output = transfer_state(function, index, input, state_cap, is_boot);
        for successor in block_successors(&function.blocks[index].terminator) {
            let Some(&successor_index) = indices.get(&successor) else {
                return Err(malformed_air(
                    function,
                    format_args!(
                        "block {:?} targets missing block {successor:?}",
                        function.blocks[index].id
                    ),
                ));
            };
            let changed = match &mut states[successor_index] {
                Some(state) => merge_state(state, &output),
                slot @ None => {
                    *slot = Some(output.clone());
                    true
                }
            };
            if changed {
                work.push_back(successor_index);
            }
        }
    }

    Ok(states)
}

fn verify_function(function: &AirFunction, diagnostics: &mut Vec<Diagnostic>) -> (usize, usize) {
    let mut move_sites = 0usize;
    let mut linear_values_checked = 0usize;

    // M4: track which VarIds carry a capability read from immutable actor state.
    // Seeded from the `StateCap`-kinded loads (the handler state prologue / init
    // reads), then PROPAGATED across borrow-aliases (`let c = power`) as the walk
    // proceeds — the marker must survive to every consume-site for C010 to fire
    // (SC-1). Function-level (not per-block) so it flows across control flow.
    let is_boot = is_construction_phase(&function.kind);
    let state_cap = state_cap_aliases(function);
    let entry_states = match block_entry_states(function, &state_cap, is_boot) {
        Ok(states) => states,
        Err(diagnostic) => {
            diagnostics.push(*diagnostic);
            return (0, 0);
        }
    };

    for (block_index, block) in function.blocks.iter().enumerate() {
        // Unreachable blocks retain the historical local checking behavior, while reachable blocks
        // begin with the may-move/may-borrow union of all real CFG predecessors.
        let mut state = entry_states[block_index].clone().unwrap_or_default();

        for stmt in &block.stmts {
            // Track new borrows
            if let AirStmt::Borrow { dst, src, .. } = stmt {
                state.active_borrows.insert(*dst, *src);
            }

            // Check for move-while-borrowed (O007)
            check_move_while_borrowed(
                function,
                &consumed_vars(stmt),
                &state.active_borrows,
                diagnostics,
            );

            let uses = stmt_uses(stmt);
            linear_values_checked += check_uses(function, &uses, &state.moved, diagnostics);
            move_sites += apply_moves(
                function,
                stmt,
                &mut state.moved,
                &state_cap,
                is_boot,
                diagnostics,
            );
        }

        let terminator_uses = terminator_uses(&block.terminator);
        if let AirTerminator::Return(Some(var)) = &block.terminator {
            check_move_while_borrowed(function, &[*var], &state.active_borrows, diagnostics);
        }
        linear_values_checked += check_uses(function, &terminator_uses, &state.moved, diagnostics);

        // M4: RETURN is a consuming ESCAPE that `apply_moves` does not model
        // (it feeds `check_uses` only). Returning a state cap out of an ordinary
        // handler moves it past the actor boundary — reject (C010).
        if let AirTerminator::Return(Some(var)) = &block.terminator
            && state_cap.contains(var)
            && !is_boot
        {
            diagnostics.push(state_cap_consume_diagnostic(function, *var, "returned"));
        }
    }

    (move_sites, linear_values_checked)
}

/// Variables consumed by a statement. This mirrors `apply_moves`; keeping O007 on the same
/// exhaustive sink set prevents a new move site from silently bypassing the borrow check.
fn consumed_vars(stmt: &AirStmt) -> Vec<VarId> {
    match stmt {
        AirStmt::Assign {
            val: AirValue::Var(src),
            ..
        } => vec![*src],
        AirStmt::Assign {
            val: AirValue::RecordConstruct { fields },
            ..
        } => fields.iter().map(|(_, var)| *var).collect(),
        AirStmt::Call { args, .. } | AirStmt::CallIndirect { args, .. } => args.clone(),
        AirStmt::MessageSend { msg, .. } | AirStmt::MessageAsk { msg, .. } => vec![*msg],
        AirStmt::ResultTry { src, .. }
        | AirStmt::OptionTry { src, .. }
        | AirStmt::CapRestrict { src, .. }
        | AirStmt::CapSplit { src, .. } => vec![*src],
        AirStmt::SpawnActor { caps, fuel_cap, .. } => {
            let mut vars = caps.clone();
            vars.push(*fuel_cap);
            vars
        }
        AirStmt::SlotPut { cap, .. } => vec![*cap],
        _ => Vec::new(),
    }
}

fn check_move_while_borrowed(
    function: &AirFunction,
    moved_vars: &[VarId],
    active_borrows: &HashMap<VarId, VarId>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for moved_var in moved_vars {
        if !function.var_kind(*moved_var).is_linear() {
            continue;
        }
        for (borrow_var, source_var) in active_borrows {
            if source_var != moved_var {
                continue;
            }
            diagnostics.push(Diagnostic::error(
                codes::O007,
                format!(
                    "cannot move `{}` while it is borrowed by `{}` in `{}`",
                    function.var_label(*moved_var),
                    function.var_label(*borrow_var),
                    function.name
                ),
                function.var_span(*moved_var),
            ));
        }
    }
}

fn check_uses(
    function: &AirFunction,
    uses: &[VarId],
    moved: &HashMap<VarId, MoveKind>,
    diagnostics: &mut Vec<Diagnostic>,
) -> usize {
    let mut linear_checked = 0usize;
    let mut seen = HashSet::<VarId>::new();

    for var in uses {
        if !function.var_kind(*var).is_linear() {
            continue;
        }

        linear_checked += 1;
        if !seen.insert(*var) {
            diagnostics.push(Diagnostic::error(
                codes::O001,
                format!(
                    "duplicate linear use of `{}` in `{}` — a linear value can be \
                     consumed at most once per statement",
                    function.var_label(*var),
                    function.name
                ),
                None,
            ));
        }

        if let Some(kind) = moved.get(var) {
            let hint = kind.recovery_hint();
            let diag = Diagnostic::error(
                codes::O001,
                format!(
                    "use after move of `{}` in `{}` — earlier {} in this scope",
                    function.var_label(*var),
                    function.name,
                    kind.describe(),
                ),
                None,
            );
            diagnostics.push(if hint.is_empty() {
                diag
            } else {
                Diagnostic::error_with_hint(codes::O001, diag.message().to_string(), None, hint)
            });
        }
    }

    linear_checked
}

#[allow(clippy::too_many_arguments)]
fn apply_moves(
    function: &AirFunction,
    stmt: &AirStmt,
    moved: &mut HashMap<VarId, MoveKind>,
    state_cap: &HashSet<VarId>,
    is_boot: bool,
    diagnostics: &mut Vec<Diagnostic>,
) -> usize {
    let mut move_sites = 0usize;

    match stmt {
        AirStmt::Assign {
            dst,
            val: AirValue::Var(src),
        } => {
            // M4: `let c = power` where the source is a state cap is a BORROW-ALIAS
            // of immutable state — the state cap cannot be moved OUT of state, so we
            // propagate the marker to `dst` (making its later consumes C010-able)
            // rather than treating it as a linear move. A regular cap `let x = fuel`
            // is a normal move. This is the sole propagation channel — the only way
            // a StateCap-derived value reaches a fresh VarId without a consume.
            if state_cap.contains(src) {
                debug_assert!(
                    state_cap.contains(dst),
                    "state-cap alias closure must include dst"
                );
            } else {
                move_sites += mark_linear_move(function, *src, MoveKind::Reassign, moved);
            }
        }
        AirStmt::Assign {
            val: AirValue::RecordConstruct { fields },
            ..
        } => {
            for (_, var) in fields {
                move_sites += mark_consume(
                    function,
                    *var,
                    MoveKind::RecordField,
                    moved,
                    state_cap,
                    is_boot,
                    diagnostics,
                );
            }
        }
        AirStmt::Call { args, .. } => {
            for arg in args {
                move_sites += mark_consume(
                    function,
                    *arg,
                    MoveKind::Call,
                    moved,
                    state_cap,
                    is_boot,
                    diagnostics,
                );
            }
        }
        AirStmt::CallIndirect { args, .. } => {
            for arg in args {
                move_sites += mark_consume(
                    function,
                    *arg,
                    MoveKind::CallIndirect,
                    moved,
                    state_cap,
                    is_boot,
                    diagnostics,
                );
            }
        }
        AirStmt::MessageSend { msg, .. } => {
            move_sites += mark_consume(
                function,
                *msg,
                MoveKind::Send,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::MessageAsk { msg, .. } => {
            move_sites += mark_consume(
                function,
                *msg,
                MoveKind::Ask,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::ResultTry { src, .. } => {
            move_sites += mark_consume(
                function,
                *src,
                MoveKind::ResultTry,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::OptionTry { src, .. } => {
            // PR OptTry / N18-OptTry: `?` on `Option<Cap<C>>` performs
            // a structural move of the cap from the Option struct to
            // the unwrapped dst. Capability-checker treats the Option's
            // post-`?` state as "moved-from". Second use of the Option
            // would fire the existing linearity-violation diagnostic.
            move_sites += mark_consume(
                function,
                *src,
                MoveKind::OptionTry,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::SpawnActor { caps, fuel_cap, .. } => {
            for cap in caps {
                move_sites += mark_consume(
                    function,
                    *cap,
                    MoveKind::Spawn,
                    moved,
                    state_cap,
                    is_boot,
                    diagnostics,
                );
            }
            move_sites += mark_consume(
                function,
                *fuel_cap,
                MoveKind::Spawn,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::CapRestrict { src, .. } => {
            move_sites += mark_consume(
                function,
                *src,
                MoveKind::Restrict,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::CapSplit { src, .. } => {
            move_sites += mark_consume(
                function,
                *src,
                MoveKind::Split,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::SlotPut { cap, .. } => {
            // The cap is moved into the slot; second use after this is O001.
            // The slot itself is not linear (it's an i32 heap pointer).
            move_sites += mark_consume(
                function,
                *cap,
                MoveKind::Reassign,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        AirStmt::SecurityRelease { cap, .. } => {
            move_sites += mark_consume(
                function,
                *cap,
                MoveKind::Reassign,
                moved,
                state_cap,
                is_boot,
                diagnostics,
            );
        }
        // M4 (SC-1, closure-capture launder): storing a borrow-only state cap
        // into ANY heap cell — most importantly a closure env (captures lower to
        // raw `StoreField`s, `lower_closure_construct`) — MOVES it out of the
        // borrow-only regime. The adversarial hunt weaponised this: `let g =
        // field; grant(&x, fn(){ spawn(g) })` captures the state-cap ALIAS `g`
        // (in `state_cap` via the `Assign{Var}` propagation), and the marker was
        // lost across the capture boundary because `apply_moves` ignored the
        // capture `StoreField`. Reject it here (C010) in any ordinary handler.
        //
        // Deliberately NOT a general linear move: this GUARD fires ONLY for
        // `state_cap` operands, so init state-writes (`StoreField{base:STATE_PTR}`
        // in `init`, where `is_boot`) and every ordinary-cap store fall through to
        // `_ => {}` and keep their existing non-consuming ownership semantics.
        AirStmt::StoreField { val, .. } | AirStmt::StateWrite { val, .. }
            if state_cap.contains(val) && !is_boot =>
        {
            diagnostics.push(state_cap_consume_diagnostic(
                function,
                *val,
                "captured by a closure (or stored into a heap cell)",
            ));
        }
        _ => {}
    }

    move_sites
}

/// M4: a consuming move of a `state_cap` operand outside the construction phase
/// is borrow-only-violating (C010); otherwise it's an ordinary linear move.
fn mark_consume(
    function: &AirFunction,
    var: VarId,
    kind: MoveKind,
    moved: &mut HashMap<VarId, MoveKind>,
    state_cap: &HashSet<VarId>,
    is_boot: bool,
    diagnostics: &mut Vec<Diagnostic>,
) -> usize {
    if state_cap.contains(&var) && !is_boot {
        diagnostics.push(state_cap_consume_diagnostic(function, var, kind.describe()));
        return 0;
    }
    mark_linear_move(function, var, kind, moved)
}

/// M4 (C010): the borrow-only violation for a state cap consumed in a handler.
fn state_cap_consume_diagnostic(function: &AirFunction, var: VarId, action: &str) -> Diagnostic {
    let name = function
        .debug_names
        .get(&var)
        .cloned()
        .unwrap_or_else(|| function.var_label(var));
    Diagnostic::error(
        codes::C010,
        format!(
            "capability `{name}` read from immutable actor state is {action} in `{}` — a state \
             capability is borrow-only inside a handler. Use it non-consumingly (`grant(&{name}, …)` \
             or `{name}.draw(n)`), or delegate it at construction time (`init`, or the entry \
             actor's `Start`).",
            function.name,
        ),
        function.var_span(var),
    )
}

fn mark_linear_move(
    function: &AirFunction,
    var: VarId,
    kind: MoveKind,
    moved: &mut HashMap<VarId, MoveKind>,
) -> usize {
    if !function.var_kind(var).is_linear() {
        return 0;
    }
    // Only the FIRST move site is recorded — that's what the user needs to
    // see; subsequent uses produce the O001 diagnostic that names this kind.
    if moved.contains_key(&var) {
        return 0;
    }
    moved.insert(var, kind);
    1
}

fn stmt_uses(stmt: &AirStmt) -> Vec<VarId> {
    match stmt {
        AirStmt::Assign { val, .. } => value_uses(val),
        AirStmt::StoreField { base_ptr, val, .. } => vec![*base_ptr, *val],
        AirStmt::LoadField { base_ptr, .. } => vec![*base_ptr],
        AirStmt::StateWrite { state_ptr, val, .. } => vec![*state_ptr, *val],
        AirStmt::StateRead { state_ptr, .. } => vec![*state_ptr],
        AirStmt::SecurityRelease { src, cap, .. } => vec![*src, *cap],
        AirStmt::Call { args, .. } => args.clone(),
        AirStmt::MessageSend {
            target,
            msg,
            payload_buf,
            payload_len,
            ..
        } => vec![*target, *msg, *payload_buf, *payload_len],
        AirStmt::MessageAsk {
            target,
            msg,
            payload_buf,
            payload_len,
            timeout,
            ..
        } => vec![*target, *msg, *payload_buf, *payload_len, *timeout],
        AirStmt::ResultTry { src, .. } => vec![*src],
        AirStmt::OptionTry { src, .. } => vec![*src],
        // Phase-1 completion: a pure scan (reads the base ptr, length, needle;
        // `idx`/`dst` are internal scratch + the bool result). Treated like a
        // `LoadDynamic`-style read — no provenance change.
        AirStmt::ArrayOrSliceContains {
            base_ptr,
            len,
            needle,
            ..
        } => vec![*base_ptr, *len, *needle],
        // AG-S1-M: `str ==` by content. A pure read of both sides' data
        // pointers and lengths; the pointers themselves were produced by
        // ordinary `LoadField`s in the lowering arm.
        AirStmt::StrBytesEq {
            lhs_data,
            lhs_len,
            rhs_data,
            rhs_len,
            ..
        } => vec![*lhs_data, *lhs_len, *rhs_data, *rhs_len],
        // Phase-1 completion: fills the pre-allocated `dst` Option (read as the
        // store base) from the slice's `data_ptr`/`len`. A pure memory write.
        AirStmt::SliceOptionElem {
            dst, data_ptr, len, ..
        } => vec![*dst, *data_ptr, *len],
        AirStmt::SpawnActor { caps, fuel_cap, .. } => {
            let mut uses = caps.clone();
            uses.push(*fuel_cap);
            uses
        }
        AirStmt::CapRestrict { src, .. } => vec![*src],
        AirStmt::CapSplit { src, amount, .. } | AirStmt::CapDraw { src, amount, .. } => {
            vec![*src, *amount]
        }
        // Capabilities-as-values: `mint` reads the target (provenance) and
        // DEFINES `dst` — it is not a move site (see `apply_moves`, which has
        // no CapMint arm), so only the target is a use here.
        AirStmt::CapMint { target, .. } => vec![*target],
        AirStmt::SerializeMessage {
            msg,
            dst_buf,
            dst_len,
            ..
        } => vec![*msg, *dst_buf, *dst_len],
        AirStmt::DeserializeMessage {
            src_buf, src_len, ..
        } => vec![*src_buf, *src_len],
        AirStmt::BumpAlloc { .. } => Vec::new(),
        // PPS-2a: reads the source pointer and the length; the destination is a fresh
        // persistent buffer (a definition, not a use).
        AirStmt::PromoteBytes { src, len, .. } => vec![*src, *len],
        AirStmt::IntrinsicAlloc { size, .. } => vec![*size],
        AirStmt::IntrinsicLoad8 { ptr, .. } => vec![*ptr],
        AirStmt::IntrinsicStore8 { ptr, val } => vec![*ptr, *val],
        AirStmt::IntrinsicCtEq { lhs, rhs, .. } => vec![*lhs, *rhs],
        AirStmt::IntrinsicCtSelect {
            cond,
            then_val,
            else_val,
            ..
        } => vec![*cond, *then_val, *else_val],
        AirStmt::IntrinsicCtLt { lhs, rhs, .. } => vec![*lhs, *rhs],
        AirStmt::FuelDecrement { .. } => Vec::new(),
        AirStmt::LoadDynamic {
            base_ptr, index, ..
        } => vec![*base_ptr, *index],
        AirStmt::StoreDynamic {
            base_ptr,
            index,
            val,
            ..
        } => vec![*base_ptr, *index, *val],
        AirStmt::WrapI64 { src, .. } => vec![*src],
        AirStmt::ExtendU32 { src, .. } => vec![*src],
        AirStmt::SignExtendI32 { src, .. } => vec![*src],
        AirStmt::TrapIf { cond } => vec![*cond],
        AirStmt::CallIndirect {
            table_index, args, ..
        } => {
            let mut uses = vec![*table_index];
            uses.extend_from_slice(args);
            uses
        }
        AirStmt::Borrow { src, .. } => vec![*src],
        AirStmt::GrantBegin { cap_var, .. } => vec![*cap_var],
        AirStmt::GrantEnd { .. } => Vec::new(),
        AirStmt::ExternCall { args, .. } => args.clone(),
        AirStmt::RegionBegin { limit_var, .. } => vec![*limit_var],
        // DEF-2a PR-6: the limit local is read again at `RegionEnd` (the post-hoc
        // exit-check trap), so it stays live across the whole body — its slot must not
        // be reused by body allocations.
        AirStmt::RegionEnd { limit_var, .. } => vec![*limit_var],
        AirStmt::SlotNew { .. } => Vec::new(),
        AirStmt::SlotPut { slot, cap } => vec![*slot, *cap],
        AirStmt::SlotTake { slot, .. } => vec![*slot],
    }
}

fn value_uses(value: &AirValue) -> Vec<VarId> {
    match value {
        AirValue::Var(var) => vec![*var],
        AirValue::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
        AirValue::RecordConstruct { fields } => fields.iter().map(|(_, var)| *var).collect(),
        AirValue::IntLit(_)
        | AirValue::FloatLit(_)
        | AirValue::BoolLit(_)
        | AirValue::StrLit(_)
        | AirValue::UnitLit => Vec::new(),
    }
}

fn terminator_uses(terminator: &AirTerminator) -> Vec<VarId> {
    match terminator {
        AirTerminator::Return(value) => value.iter().copied().collect(),
        AirTerminator::Loop { cond, .. } | AirTerminator::Branch { cond, .. } => vec![*cond],
        // `Dispatch` is a pure control-flow wrapper (the scrutinee/test vars are
        // used by the chain's stmts/branches, not the terminator itself).
        AirTerminator::Jump(_) | AirTerminator::Unreachable | AirTerminator::Dispatch { .. } => {
            Vec::new()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::air::{
        AirBlock, AirFunction, AirFunctionKind, AirProgram, AirStmt, AirTerminator, AirType,
        AirValue, AirValueKind, BlockId, VarId,
    };
    use crate::ast::Ring;

    use super::verify;

    #[test]
    fn rejects_use_after_move_in_single_block() {
        let program = AirProgram {
            functions: vec![AirFunction {
                name: "sigil::linear".to_owned(),
                export_name: "sigil__linear".to_owned(),
                ring: Ring::default(),
                kind: AirFunctionKind::ModuleFunction,
                params: vec![(VarId(0), AirType::Ptr)],
                ret: AirType::Unit,
                locals: vec![(VarId(1), AirType::Ptr)],
                value_kinds: [
                    (VarId(0), AirValueKind::Cap("Fuel".to_owned())),
                    (VarId(1), AirValueKind::Copy),
                ]
                .into_iter()
                .collect(),
                debug_names: [(VarId(0), "fuel".to_owned()), (VarId(1), "msg".to_owned())]
                    .into_iter()
                    .collect(),
                def_span: Default::default(),
                debug_spans: Default::default(),
                block_static_multiplicity: Vec::new(),
                security: Default::default(),
                blocks: vec![AirBlock {
                    id: BlockId(0),
                    stmts: vec![
                        AirStmt::Assign {
                            dst: VarId(1),
                            val: AirValue::RecordConstruct {
                                fields: vec![("arg0".to_owned(), VarId(0))],
                            },
                        },
                        AirStmt::Assign {
                            dst: VarId(1),
                            val: AirValue::RecordConstruct {
                                fields: vec![("arg0".to_owned(), VarId(0))],
                            },
                        },
                    ],
                    terminator: AirTerminator::Return(None),
                }],
                entry_block: BlockId(0),
            }],
        };

        let err = verify(&program).expect_err("use-after-move should fail");
        assert_eq!(
            err[0].message(),
            "use after move of `fuel` in `sigil::linear` — earlier stored into a record field in this scope"
        );
    }
}
