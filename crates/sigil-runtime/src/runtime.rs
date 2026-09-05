//! The resident actor host: `RuntimeHost`, the wasmtime-backed runtime that
//! bootstraps a compiled module, spawns and supervises actors, delivers
//! mailbox messages, and links the actor-side host imports (fuel_decrement,
//! send/ask/spawn, alloc, alloc_persistent, cap restrict/split/mint).
//!
//! This file owns the per-actor resource discipline: a 64 KB arena at
//! `actor_id * ARENA_SIZE` with the actor's state struct at its front (M3);
//! a fuel refill (AL-1) and an arena rewind to the persistent floor
//! (AL-2 / AGG-1) before every TOP-LEVEL dispatch, and only there -- nested
//! send/ask share one grant (X-AL2) -- so init-built and persistent-promoted
//! objects survive while handler scratch is reclaimed; and REAL supervised
//! restarts (refill + reset + replay-safe reinit; PPS-4, restart-as-GC) whose
//! reinit trap propagates fail-loud (X-AL3c).
//!
//! Every fallible path returns the typed `RuntimeError`; host imports stash
//! theirs via `record_host_error` before trapping, so callers surface the
//! typed error, not just wasmtime's trap text. The mailbox fails closed with
//! `QueueFull` backpressure, the PPS-4 persistent-heap cap trips the distinct
//! `PersistentHeapExhausted`, and the per-dispatch wasmtime backstop
//! (`MAX_ACTOR_FUEL`) bounds handlers that never yield. No panic, assert, or
//! expect outside `#[cfg(test)]`.
//!
//! Specs: docs/specs/actor-live.md, actor-state-mutable.md,
//! persistent-aggregate-state.md, persistent-pointer-state.md. Pinned by the
//! tests below plus tests/actor_live_{fuel_refill,arena_reset,restart,serve}.rs,
//! tests/pps4_restart_as_gc.rs, tests/agg2b_alloc_persistent.rs, and the
//! host-import totality contract in tests/runtime_import_contract.rs.

use std::{
    cell::{Ref, RefCell},
    collections::{BTreeMap, HashMap},
    fmt,
    rc::Rc,
};

use sigil_abi::{RuntimeActorSpec, RuntimeHandlerSpec, RuntimeModuleSpec, RuntimeTypeSpec};
use wasmtime::{
    AsContext, AsContextMut, Caller, Config, Engine, Func, Linker, Memory, Module, Store, Val,
    ValType,
};

use crate::{
    actor::{ActorId, ActorInstance},
    audit::{AuditEventKind, AuditLog},
    capability::{Capability, CapabilityError, CapabilityId, CapabilityTable, FuelCapability},
    message::{Message, MessageQueue},
    supervisor::SupervisionStrategy,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeBootReport {
    pub module_name: String,
    pub entry_actor: Option<ActorId>,
    pub queued_messages: usize,
}

/// The wasm value kind of an exported function's parameter (see
/// [`RuntimeHost::export_param_kinds`]). `Other` covers V128/reference types the serve path never
/// accepts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmParamKind {
    I32,
    I64,
    F32,
    F64,
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    NotBootstrapped,
    UnknownActor(ActorId),
    UnknownActorType(u32),
    UnknownHandler {
        actor: String,
        handler_id: u32,
    },
    MissingExport(String),
    InvalidActorRef(i32),
    InvalidCapabilityRef(i32),
    NoActiveActor(&'static str),
    MissingMemoryExport,
    UnsupportedSpawnCaps {
        count: usize,
    },
    UnsupportedSignature {
        export: String,
        params: usize,
        results: usize,
    },
    Capability {
        message: String,
    },
    FuelExhausted {
        actor_id: ActorId,
    },
    Wasm {
        message: String,
    },
    /// The host message queue is at its capacity bound; the message was
    /// rejected via backpressure rather than growing memory without bound
    /// (availability finding P2).
    QueueFull {
        receiver: ActorId,
    },
    /// PPS-4: a persistent allocation would push the actor's persistent floor
    /// past the host-configured per-actor byte cap. The clean, DISTINCT
    /// exhaustion trap the restart-as-GC posture is built on: under
    /// `Restart(n)` supervision this trap triggers a restart that discards
    /// the heap (a replay-safe init) — the collector.
    PersistentHeapExhausted {
        actor_id: ActorId,
        requested: u32,
        would_be: u32,
        cap: u32,
    },
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotBootstrapped => write!(f, "runtime has not been bootstrapped"),
            Self::UnknownActor(actor_id) => write!(f, "unknown actor `{actor_id}`"),
            Self::UnknownActorType(actor_type_id) => {
                write!(f, "unknown actor type id `{actor_type_id}`")
            }
            Self::UnknownHandler { actor, handler_id } => {
                write!(f, "actor `{actor}` has no handler with id `{handler_id}`")
            }
            Self::MissingExport(export) => write!(f, "missing Wasm export `{export}`"),
            Self::InvalidActorRef(actor_ref) => write!(f, "invalid actor ref `{actor_ref}`"),
            Self::InvalidCapabilityRef(cap_ref) => {
                write!(f, "invalid capability ref `{cap_ref}`")
            }
            Self::NoActiveActor(operation) => {
                write!(f, "`{operation}` requires an active actor context")
            }
            Self::MissingMemoryExport => write!(f, "compiled module is missing exported memory"),
            Self::UnsupportedSpawnCaps { count } => write!(
                f,
                "spawn received {count} non-fuel capability argument(s), but runtime spawn only supports the dedicated fuel cap path today"
            ),
            Self::UnsupportedSignature {
                export,
                params,
                results,
            } => write!(
                f,
                "Wasm export `{export}` has unsupported signature ({params} param(s), {results} result(s))"
            ),
            Self::Capability { message } => write!(f, "{message}"),
            Self::FuelExhausted { actor_id } => {
                write!(f, "actor `{actor_id}` exhausted its fuel budget")
            }
            Self::Wasm { message } => write!(f, "{message}"),
            Self::QueueFull { receiver } => write!(
                f,
                "message queue full: cannot enqueue for actor `{receiver}` (host backpressure cap reached)"
            ),
            Self::PersistentHeapExhausted {
                actor_id,
                requested,
                would_be,
                cap,
            } => write!(
                f,
                "actor `{actor_id}` persistent heap exhausted: a {requested}-byte persistent allocation would raise the floor to {would_be} bytes, over the {cap}-byte cap"
            ),
        }
    }
}

impl std::error::Error for RuntimeError {}

impl From<CapabilityError> for RuntimeError {
    fn from(err: CapabilityError) -> Self {
        Self::Capability {
            message: format!("capability error: {err:?}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeState {
    actors: BTreeMap<ActorId, ActorInstance>,
    capability_table: CapabilityTable,
    message_queue: MessageQueue,
    audit_log: AuditLog,
    next_actor_id: u64,
}

impl RuntimeState {
    fn new() -> Self {
        Self {
            actors: BTreeMap::new(),
            capability_table: CapabilityTable::default(),
            message_queue: MessageQueue::default(),
            audit_log: AuditLog::default(),
            next_actor_id: 1,
        }
    }
}

struct RuntimeExecution {
    store: Store<StoreData>,
}

struct StoreData {
    state: Rc<RefCell<RuntimeState>>,
    module: RuntimeModuleSpec,
    exports: HashMap<String, Func>,
    active_actor: Option<ActorId>,
    last_error: Option<RuntimeError>,
    arena_cursors: HashMap<ActorId, u32>,
    /// AGG-1 (persistent aggregate state): the per-actor PERSISTENT FLOOR — the bump cursor
    /// captured immediately AFTER `init` runs, so every object `init` allocated (a record/array/
    /// tuple state field's heap payload, etc.) sits BELOW it. The AL-2 per-dispatch reset rewinds
    /// the cursor to THIS floor (not `arena_base + state_size`), so init's allocations persist
    /// across dispatches while a handler's scratch (allocated ABOVE the floor) is reclaimed. Absent
    /// (⇒ `arena_base + state_size`) for a stateless actor or one whose init allocates nothing, so
    /// scalar-state actors are unchanged. See docs/specs/persistent-aggregate-state.md.
    persistent_floors: HashMap<ActorId, u32>,
    /// Wasmtime fuel granted to each top-level actor dispatch, reset before
    /// every call in `call_export_from_store`. Defaults to `MAX_ACTOR_FUEL`;
    /// held here (rather than read from the const directly) so tests can inject
    /// a small cap to exercise the backstop without burning billions of ops.
    wasm_fuel_cap: u64,
    /// The instance's linear memory, cached at instantiation so both `Caller`
    /// and `Store` contexts can grow it to cover an actor's state region before
    /// the first state access (M3). `None` until `collect_runtime_exports` sets it.
    memory: Option<Memory>,
    /// PPS-4: the per-actor PERSISTENT-HEAP byte cap — the grant-shaped knob
    /// the restart-as-GC posture turns. A persistent allocation that would
    /// raise an actor's floor past `arena_base + persistent_cap` traps with
    /// the distinct `PersistentHeapExhausted` error instead of allocating.
    /// Defaults to `ARENA_SIZE` (the arena bound itself), which changes no
    /// behavior until a host lowers it.
    persistent_cap: u32,
}

const ARENA_SIZE: u32 = 65536; // 64KB per actor

/// The base address of an actor's arena — and, under the M3 actor-state ABI, the
/// STATE POINTER passed to that actor's init/handlers (its state struct lives at
/// the arena front). Computable from the actor id alone; `checked_mul` fails
/// closed on the >65535-actor overflow anti-goal (`arena_base` must fit u32).
fn arena_base_of(actor_id: ActorId) -> Result<u32, RuntimeError> {
    (actor_id.get() as u32)
        .checked_mul(ARENA_SIZE)
        .ok_or_else(|| RuntimeError::Wasm {
            message: format!("actor `{actor_id}` arena base overflows u32"),
        })
}

impl StoreData {
    fn new(state: Rc<RefCell<RuntimeState>>, module: RuntimeModuleSpec) -> Self {
        Self {
            state,
            module,
            exports: HashMap::new(),
            active_actor: None,
            last_error: None,
            arena_cursors: HashMap::new(),
            persistent_floors: HashMap::new(),
            wasm_fuel_cap: MAX_ACTOR_FUEL,
            memory: None,
            persistent_cap: ARENA_SIZE,
        }
    }

    /// AGG-1: capture the actor's PERSISTENT FLOOR — the bump cursor right after `init` ran, so
    /// init's allocations are below it and survive the AL-2 per-dispatch reset. Called after every
    /// init (spawn, entry bootstrap, replayable restart). No-op if the actor has no cursor (stateless).
    fn capture_persistent_floor(&mut self, actor: ActorId) {
        if let Some(cursor) = self.arena_cursors.get(&actor).copied() {
            self.persistent_floors.insert(actor, cursor);
        }
    }

    /// AGG-1: the AL-2 reset floor for this actor — the persistent floor if init established one,
    /// else `arena_base + state_size` (the pre-AGG-1 behavior for scalar/stateless actors).
    fn reset_floor(&self, actor: ActorId, state_size: u32) -> Result<u32, RuntimeError> {
        Ok(self
            .persistent_floors
            .get(&actor)
            .copied()
            .unwrap_or(arena_base_of(actor)? + state_size))
    }
}

pub struct RuntimeHost {
    default_fuel_budget: u64,
    state: Rc<RefCell<RuntimeState>>,
    execution: Option<RuntimeExecution>,
    /// PPS-4: the per-actor persistent-heap byte cap to stamp onto each
    /// bootstrap's `StoreData` (and the live one on `set_persistent_cap`).
    persistent_cap: u32,
}

impl RuntimeHost {
    pub fn new(fuel_budget: u64) -> Self {
        Self {
            default_fuel_budget: fuel_budget,
            state: Rc::new(RefCell::new(RuntimeState::new())),
            execution: None,
            persistent_cap: ARENA_SIZE,
        }
    }

    pub fn actors(&self) -> Ref<'_, BTreeMap<ActorId, ActorInstance>> {
        Ref::map(self.state.borrow(), |state| &state.actors)
    }

    pub fn capability_table(&self) -> Ref<'_, CapabilityTable> {
        Ref::map(self.state.borrow(), |state| &state.capability_table)
    }

    pub fn audit_log(&self) -> Ref<'_, AuditLog> {
        Ref::map(self.state.borrow(), |state| &state.audit_log)
    }

    pub fn pending_messages(&self) -> usize {
        self.state.borrow().message_queue.len()
    }

    /// PPS-4: set the per-actor PERSISTENT-HEAP byte cap (the grant-shaped
    /// restart-as-GC knob). Applies to the current execution if bootstrapped
    /// and to every later bootstrap. Values above `ARENA_SIZE` are clamped to
    /// it (the arena bound is the outer wall regardless).
    pub fn set_persistent_cap(&mut self, bytes: u32) {
        let bytes = bytes.min(ARENA_SIZE);
        self.persistent_cap = bytes;
        if let Some(execution) = self.execution.as_mut() {
            execution.store.data_mut().persistent_cap = bytes;
        }
    }

    /// PPS-4: the configured per-actor persistent-heap byte cap.
    pub fn persistent_cap(&self) -> u32 {
        self.persistent_cap
    }

    /// PPS-4 observability: the actor's CURRENT persistent bytes — its
    /// persistent floor minus its arena base (state slots + init allocations +
    /// every promoted/state-backed allocation, including the documented
    /// watermark residual). `None` when not bootstrapped, the actor is
    /// unknown, or no floor was ever captured.
    pub fn persistent_bytes(&self, actor: ActorId) -> Option<u32> {
        let execution = self.execution.as_ref()?;
        let floor = execution
            .store
            .data()
            .persistent_floors
            .get(&actor)
            .copied()?;
        Some(floor - arena_base_of(actor).ok()?)
    }

    /// The wasm value kinds of a bootstrapped export's params, or `None` if not bootstrapped / the
    /// export is absent. The serve loop (ACTOR-LIVE AL-4) uses this to fail fast at startup when a
    /// handler's LOWERED param width does not match the payload the driver encodes — the runtime
    /// `RuntimeTypeSpec` collapses `i32`/`u32`/`i64`/`u64`/`f64` all to `I64`, so the spec alone
    /// cannot tell an `i32` handler (wasm `i32` param) from an `i64` one; the emitted signature can.
    pub fn export_param_kinds(&self, export_name: &str) -> Option<Vec<WasmParamKind>> {
        let execution = self.execution.as_ref()?;
        let func = execution.store.data().exports.get(export_name)?;
        let kinds = func
            .ty(execution.store.as_context())
            .params()
            .map(|ty| match ty {
                ValType::I32 => WasmParamKind::I32,
                ValType::I64 => WasmParamKind::I64,
                ValType::F32 => WasmParamKind::F32,
                ValType::F64 => WasmParamKind::F64,
                _ => WasmParamKind::Other,
            })
            .collect();
        Some(kinds)
    }

    pub fn bootstrap(
        &mut self,
        module: &RuntimeModuleSpec,
        wasm: &[u8],
    ) -> Result<RuntimeBootReport, RuntimeError> {
        self.execution = None;
        *self.state.borrow_mut() = RuntimeState::new();

        self.state
            .borrow_mut()
            .audit_log
            .record(AuditEventKind::ModuleLoaded {
                module: module.module_name.clone(),
                wasm_bytes: wasm.len(),
                export_count: module.export_count(),
            });

        self.execution = Some(instantiate_runtime(
            Rc::clone(&self.state),
            module,
            wasm,
            self.persistent_cap,
        )?);

        let Some(entry_actor) = module.entry_actor().cloned() else {
            return Ok(RuntimeBootReport {
                module_name: module.module_name.clone(),
                entry_actor: None,
                queued_messages: 0,
            });
        };

        let entry_fuel_budget = if module.fuel_budget == 0 {
            self.default_fuel_budget
        } else {
            module.fuel_budget
        };
        let actor_id = {
            let mut state = self.state.borrow_mut();
            let actor_id = ActorId(state.next_actor_id);
            state.next_actor_id += 1;

            let mut actor = ActorInstance::new(
                entry_actor.name.clone(),
                entry_fuel_budget,
                SupervisionStrategy::Stop,
            );
            let fuel_cap = state
                .capability_table
                .insert(Capability::Fuel(FuelCapability::new(entry_fuel_budget)));
            actor.own_capability(fuel_cap);
            state.audit_log.record(AuditEventKind::ActorSpawned {
                actor_id,
                actor_type: entry_actor.name.clone(),
                parent: None,
            });
            state.actors.insert(actor_id, actor);
            drop(state);

            // M3: reserve the entry actor's state region at its arena front
            // (seed the bump cursor past `state_size`) before init/handlers run.
            if entry_actor.state_size > 0
                && let Some(execution) = self.execution.as_mut()
            {
                let reserved = arena_base_of(actor_id)? + entry_actor.state_size;
                execution
                    .store
                    .data_mut()
                    .arena_cursors
                    .insert(actor_id, reserved);
            }

            self.invoke_actor_init(&entry_actor, actor_id, fuel_cap)?;
            // AGG-1: capture the entry actor's persistent floor after its init allocations.
            if let Some(execution) = self.execution.as_mut() {
                execution
                    .store
                    .data_mut()
                    .capture_persistent_floor(actor_id);
            }
            actor_id
        };

        let mut queued_messages = 0usize;
        if let Some(handler) = entry_actor.handler_named("Start") {
            self.enqueue_message(Message::system(
                actor_id,
                handler.name.clone(),
                handler.handler_id,
            ))?;
            queued_messages = 1;
        }

        Ok(RuntimeBootReport {
            module_name: module.module_name.clone(),
            entry_actor: Some(actor_id),
            queued_messages,
        })
    }

    pub fn enqueue_message(&mut self, message: Message) -> Result<(), RuntimeError> {
        let mut state = self.state.borrow_mut();
        if !state.actors.contains_key(&message.receiver) {
            return Err(RuntimeError::UnknownActor(message.receiver));
        }

        let receiver = message.receiver;
        let event = AuditEventKind::MessageEnqueued {
            sender: message.sender,
            receiver: message.receiver,
            handler: message.handler.clone(),
        };
        // Enqueue first, apply backpressure at the cap, and only record the
        // audit event on success so the log never shows a phantom enqueue.
        state
            .message_queue
            .push(message)
            .map_err(|_| RuntimeError::QueueFull { receiver })?;
        state.audit_log.record(event);
        Ok(())
    }

    pub fn drain_messages(&mut self, limit: usize) -> Result<usize, RuntimeError> {
        if self.execution.is_none() {
            return Err(RuntimeError::NotBootstrapped);
        }

        let mut delivered = 0usize;
        for _ in 0..limit {
            let Some(message) = self.state.borrow_mut().message_queue.pop() else {
                break;
            };

            let _ = self.deliver_message(message)?;
            delivered += 1;
        }

        Ok(delivered)
    }

    fn invoke_actor_init(
        &mut self,
        actor_spec: &RuntimeActorSpec,
        actor_id: ActorId,
        fuel_cap: CapabilityId,
    ) -> Result<(), RuntimeError> {
        let Some(export_name) = actor_spec.init_export.as_deref() else {
            return Ok(());
        };

        let Some(execution) = self.execution.as_mut() else {
            return Err(RuntimeError::NotBootstrapped);
        };

        // M3 ABI: `init`'s leading parameter is the actor's state pointer; grow
        // memory to back the state region before init's first store.
        if let Some(memory) = execution.store.data().memory {
            ensure_state_region(
                memory,
                &mut execution.store,
                actor_id,
                actor_spec.state_size,
            )?;
        }
        let init_payload = build_init_args(actor_spec, &[], fuel_cap, export_name)?;
        let mut args = Vec::with_capacity(init_payload.len() + 1);
        args.push(Val::I32(arena_base_of(actor_id)? as i32));
        args.extend(init_payload);

        let _ = call_export_from_store(&mut execution.store, export_name, actor_id, &args)?;
        Ok(())
    }

    fn deliver_message(&mut self, message: Message) -> Result<i64, RuntimeError> {
        let Some(execution) = self.execution.as_mut() else {
            return Err(RuntimeError::NotBootstrapped);
        };

        let resolved = {
            let state = self.state.borrow();
            resolve_handler(
                &execution.store.data().module,
                &state,
                message.receiver,
                message.handler_id,
            )?
        };

        let payload =
            decode_payload_args(&message.payload, &resolved.params, &resolved.handler_name)?;
        // M3 ABI: the handler's leading parameter is the receiver's state pointer
        // (arena base); the decoded payload follows. Grow memory to back the
        // state region before the handler's first load.
        if let Some(memory) = execution.store.data().memory {
            ensure_state_region(
                memory,
                &mut execution.store,
                message.receiver,
                resolved.state_size,
            )?;
        }
        let mut args = Vec::with_capacity(payload.len() + 1);
        args.push(Val::I32(arena_base_of(message.receiver)? as i32));
        args.extend(payload);

        // ACTOR-LIVE AL-1: restore this actor's per-dispatch fuel grant BEFORE the handler runs.
        // Fuel is a per-dispatch budget, not a whole-life one — the `Store` is long-lived across
        // handler calls, so without this a resident actor exhausts its budget cumulatively and dies
        // forever. HOST action, no guest surface (X-AL1). TOP-LEVEL-ONLY: `deliver_message` drives
        // top-level dispatches; the re-entrant `call_export_from_caller` (send/ask within a
        // handler) does NOT refill, so a synchronous call-tree stays bounded by one grant (X-AL2) —
        // mirroring the wasmtime backstop reset in `call_export_from_store`. The borrow is dropped
        // before the call so the handler's own `fuel_decrement` can re-borrow the state.
        {
            let mut state = self.state.borrow_mut();
            if let Some(actor) = state.actors.get_mut(&message.receiver) {
                actor.refill_fuel();
            }
        }

        // ACTOR-LIVE AL-2, reconciled with the M3 state region (MS-S0b): reset this actor's
        // per-dispatch arena BEFORE the handler runs, but reset the cursor to
        // `arena_base + state_size` — NOT `arena_base` — so the reset reclaims the per-dispatch
        // SCRATCH TAIL while PRESERVING the durable STATE PREFIX reserved at the arena front (M3
        // places actor state there and seeds the cursor past it). Before M3, state was
        // closure-captures and nothing durable lived in the arena, so AL-2 removed the cursor
        // (X-AL3: "nothing durable lives in the arena"); with a real state region that invariant is
        // GENERALIZED — the state prefix persists across dispatches, only the scratch tail resets.
        // `state_size == 0` ⇒ `arena_base`, the original AL-2 behavior. TOP-LEVEL-ONLY, the AL-1
        // discipline (the re-entrant `call_export_from_caller` does NOT reset — X-AL2). Runtime-only.
        // AGG-1: the floor is the PERSISTENT FLOOR (post-init cursor) when init allocated durable
        // aggregate state, else `arena_base + state_size` — so init's aggregate payload survives
        // while the handler scratch above it is reclaimed.
        let receiver_floor = execution
            .store
            .data()
            .reset_floor(message.receiver, resolved.state_size)?;
        execution
            .store
            .data_mut()
            .arena_cursors
            .insert(message.receiver, receiver_floor);

        let call_result = call_export_from_store(
            &mut execution.store,
            &resolved.export_name,
            message.receiver,
            &args,
        );

        match call_result {
            Ok(result) => {
                let mut state = self.state.borrow_mut();
                state.audit_log.record(AuditEventKind::MessageDelivered {
                    sender: message.sender,
                    receiver: message.receiver,
                    handler: message.handler,
                });
                normalize_result(result)
            }
            Err(err) => {
                // Decide whether supervision restarts this actor (bound + strategy), in a state
                // borrow scoped so it is dropped before `restart_actor` re-borrows it (and before
                // the reinit runs guest code that re-borrows state via host imports).
                let should_restart = {
                    let state = self.state.borrow();
                    let actor = state
                        .actors
                        .get(&message.receiver)
                        .ok_or(RuntimeError::UnknownActor(message.receiver))?;
                    matches!(
                        actor.supervision(),
                        SupervisionStrategy::Restart { max_restarts }
                            if actor.restart_count() < max_restarts
                    )
                };
                if should_restart {
                    // ACTOR-LIVE AL-3: a REAL restart — refill fuel (AL-1) + reset arena (AL-2) +
                    // re-run init (when faithfully replayable) so the actor resumes from CLEAN
                    // state, not the corpse. Before AL-3 this only bumped the counter + swallowed
                    // the error, leaving whatever the trapped handler wrote to guest memory. X-AL3c:
                    // a reinit that itself traps propagates here (fail-loud), never a zombie `Ok`.
                    restart_actor(&mut execution.store, message.receiver)?;
                    Ok(0) // the actor was restarted; keep the host alive
                } else {
                    Err(err)
                }
            }
        }
    }
}

/// ACTOR-LIVE AL-3 (docs/specs/actor-live.md): perform a REAL restart of a supervised actor whose
/// handler trapped, instead of only bumping the restart counter and swallowing the error (which kept
/// the guest-state "corpse"). Refills the per-dispatch fuel grant (AL-1) + resets the arena (AL-2) +
/// RE-RUNS the actor's init export so its state returns to its initial value, then records the
/// restart in the audit log.
///
/// The reinit is applied when the init is faithfully replayable: either it takes no cap args
/// (`init_params` empty — the original argument vector is the empty vector), or — PPS-4,
/// restart-as-GC — the compiler marked it `init_replay_safe` (no cap-table op, no outward effect;
/// see `RuntimeActorSpec::init_replay_safe`) AND the spawn retained the ordered init-arg handles
/// to replay with. Replaying with the RETAINED handles moves no authority: the actor is handed the
/// same caps it already holds, so nothing is re-spent or re-minted — the fear AG-AL7 fenced. A
/// cap-init actor whose init is NOT replay-safe (it draws/splits/mints or reaches outward) keeps
/// the AG-AL7 preserve-state path: refill+reset to the persistent floor, no reinit — its
/// persistent heap is deliberately NOT reclaimed, the honest boundary of restart-as-GC.
///
/// X-AL3c fail-fast: if the reinit call itself traps, the error PROPAGATES (the restart failed) —
/// the audit is recorded only on success, so a half-reinitialized actor is never reported as a
/// successful restart. HOST-side, at top-level dispatch only (the AL-1/AL-2 discipline). Runtime-only.
fn restart_actor(store: &mut Store<StoreData>, receiver: ActorId) -> Result<(), RuntimeError> {
    let state_rc = Rc::clone(&store.data().state);

    // 1. Refill the per-dispatch fuel grant (AL-1) + read the actor's type and retained
    //    init-arg handles (PPS-4), in a borrow dropped before the reinit runs guest code.
    let (actor_type, retained_caps, retained_fuel_cap) = {
        let mut state = state_rc.borrow_mut();
        let actor = state
            .actors
            .get_mut(&receiver)
            .ok_or(RuntimeError::UnknownActor(receiver))?;
        actor.refill_fuel();
        (
            actor.actor_type().to_owned(),
            actor.init_caps().to_vec(),
            actor.init_fuel_cap(),
        )
    };

    // Look up the actor's spec ONCE for its state_size (M3) + the replayable init. An init
    // replays when its params are empty (nothing to retain) or when the compiler marked it
    // replay-safe AND this spawn retained the handles (PPS-4; a spec hand-built without a
    // recorded spawn falls back to preserve-state, fail-closed).
    let (state_size, reinit) = match actor_spec_by_name(&store.data().module, &actor_type) {
        Some(spec) => {
            let replayable = spec.init_params.is_empty()
                || (spec.init_replay_safe && retained_fuel_cap.is_some());
            (
                spec.state_size,
                match &spec.init_export {
                    Some(export) if replayable => Some((export.clone(), spec.clone())),
                    _ => None,
                },
            )
        }
        None => (0, None),
    };

    // 2. Reset the per-dispatch arena (AL-2, MS-S0b + AGG-1). For a REPLAYABLE actor (reinit below)
    //    reset to `arena_base + state_size` — the scratch AND the old persistent aggregate region
    //    are reclaimed, and the reinit rebuilds state to birth. For a CAP-INIT actor (AG-AL7:
    //    refill+reset only, NOT reinit'd) reset to the PERSISTENT FLOOR instead, so its durable
    //    aggregate state is PRESERVED (the next handler's scratch would otherwise clobber it).
    //    `state_size == 0` ⇒ arena_base.
    let floor = if reinit.is_some() {
        arena_base_of(receiver)? + state_size
    } else {
        store.data().reset_floor(receiver, state_size)?
    };
    store.data_mut().arena_cursors.insert(receiver, floor);

    // 3. Re-run init IF faithfully replayable (no cap args). Cap-init actors are fenced to
    //    refill+reset only (AG-AL7). M3 ABI: init's LEADING param is the state pointer (arena base),
    //    so the reinit is called with `[state_ptr]`, not `[]`; grow memory to back the region first.
    if let Some((export_name, spec)) = reinit {
        if let Some(memory) = store.data().memory {
            ensure_state_region(memory, &mut *store, receiver, state_size)?;
        }
        // PPS-4: rebuild the ORIGINAL argument vector from the retained handles via the same
        // `build_init_args` the spawn used — identical mapping, identical handles. Empty for a
        // no-arg init (the pre-PPS-4 path, unchanged).
        let init_payload = match retained_fuel_cap {
            Some(fuel_cap) if !spec.init_params.is_empty() => {
                build_init_args(&spec, &retained_caps, fuel_cap, &export_name)?
            }
            _ => Vec::new(),
        };
        let mut args = Vec::with_capacity(init_payload.len() + 1);
        args.push(Val::I32(arena_base_of(receiver)? as i32));
        args.extend(init_payload);
        // X-AL3c: a reinit trap propagates (fail-loud), never a swallowed half-restart.
        let _ = call_export_from_store(store, &export_name, receiver, &args)?;
        // AGG-1: re-establish the persistent floor — the reinit re-allocated the aggregate state
        // to birth, so the AL-2 reset must again rewind to just above it, not to `state_size`.
        store.data_mut().capture_persistent_floor(receiver);
    }

    // 4. Record the SUCCESSFUL restart (only reached if the reinit above did not trap).
    let mut state = state_rc.borrow_mut();
    let actor = state
        .actors
        .get_mut(&receiver)
        .ok_or(RuntimeError::UnknownActor(receiver))?;
    actor.increment_restart_count();
    let count = actor.restart_count();
    state.audit_log.record(AuditEventKind::ActorRestarted {
        actor_id: receiver,
        restart_count: count,
    });
    Ok(())
}

#[derive(Debug, Clone)]
struct ResolvedHandler {
    handler_name: String,
    export_name: String,
    params: Vec<RuntimeTypeSpec>,
    /// The receiving actor's state struct size (M3) — used to grow memory to
    /// cover its state region before the handler's first state load.
    state_size: u32,
}

fn instantiate_runtime(
    state: Rc<RefCell<RuntimeState>>,
    module_spec: &RuntimeModuleSpec,
    wasm: &[u8],
    persistent_cap: u32,
) -> Result<RuntimeExecution, RuntimeError> {
    crate::host_contract::reject_unbound_host_profile(wasm).map_err(|error| {
        RuntimeError::Wasm {
            message: error.to_string(),
        }
    })?;
    // Enable fuel so each actor dispatch can be bounded by a per-call wasmtime
    // fuel budget. Without it, an actor handler (or hand-written module passed
    // to `RuntimeHost::bootstrap`) could spin forever regardless of the
    // cooperative SIGIL fuel accounting (finding P1/P2).
    let mut config = Config::new();
    config.consume_fuel(true);
    let engine = Engine::new(&config).map_err(wasm_error)?;
    let module = Module::from_binary(&engine, wasm).map_err(wasm_error)?;
    let mut linker = Linker::new(&engine);

    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.fuel_decrement,
            |mut caller: Caller<'_, StoreData>, amount: i32| -> Result<(), wasmtime::Error> {
                fuel_decrement_import(&mut caller, amount)
                    .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.send,
            |mut caller: Caller<'_, StoreData>,
             target: i32,
             handler_id: i32,
             payload_buf: i32,
             payload_len: i32|
             -> Result<(), wasmtime::Error> {
                send_import(&mut caller, target, handler_id, payload_buf, payload_len)
                    .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.ask,
            |mut caller: Caller<'_, StoreData>,
             target: i32,
             handler_id: i32,
             payload_buf: i32,
             payload_len: i32,
             timeout: i64|
             -> Result<i64, wasmtime::Error> {
                let _ = timeout;
                ask_import(&mut caller, target, handler_id, payload_buf, payload_len)
                    .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.spawn,
            |mut caller: Caller<'_, StoreData>,
             actor_type_id: i32,
             caps_ptr: i32,
             caps_len: i32,
             fuel_cap: i32,
             supervision: i32|
             -> Result<i32, wasmtime::Error> {
                spawn_import(
                    &mut caller,
                    actor_type_id,
                    caps_ptr,
                    caps_len,
                    fuel_cap,
                    supervision,
                )
                .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.alloc,
            |mut caller: Caller<'_, StoreData>, size: i32| -> Result<i32, wasmtime::Error> {
                alloc_import(&mut caller, size).map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    // AGG-2b: the persistent-heap allocation channel. Defined unconditionally so a module that
    // imports it (AGG2b-2's state-backed collection instance) resolves; a state-free module simply
    // never imports it, so this definition is inert and moves no emitted bytes.
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.alloc_persistent,
            |mut caller: Caller<'_, StoreData>, size: i32| -> Result<i32, wasmtime::Error> {
                alloc_persistent_import(&mut caller, size)
                    .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.cap_restrict,
            |mut caller: Caller<'_, StoreData>,
             cap: i32,
             restriction: i32|
             -> Result<i32, wasmtime::Error> {
                cap_restrict_import(&mut caller, cap, restriction)
                    .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.cap_split,
            |mut caller: Caller<'_, StoreData>,
             cap: i32,
             amount: i64|
             -> Result<i32, wasmtime::Error> {
                cap_split_import(&mut caller, cap, amount)
                    .map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    linker
        .func_wrap(
            &module_spec.imports.module,
            &module_spec.imports.cap_mint,
            |mut caller: Caller<'_, StoreData>| -> Result<i32, wasmtime::Error> {
                cap_mint_import(&mut caller).map_err(|err| record_host_error(&mut caller, err))
            },
        )
        .map_err(wasm_error)?;
    let mut store = Store::new(&engine, StoreData::new(state, module_spec.clone()));
    // The engine runs with `consume_fuel(true)`, so a fresh store holds ZERO
    // fuel and anything charged before the first `set_fuel` traps. Instantiation
    // itself is charged (data-segment init and any start function), so the
    // backstop must be granted HERE, not only in `call_export_from_store` —
    // that runs after this point and would never be reached.
    //
    // This was latent until wasmtime 47: 43 charged nothing for instantiating
    // these modules, so instantiating on an empty store happened to work. The
    // ephemeral path always had the order right (`ephemeral.rs` sets fuel
    // before its `instantiate`), which is why only the actor host broke.
    store.set_fuel(MAX_ACTOR_FUEL).map_err(wasm_error)?;
    // PPS-4: stamp the host-configured per-actor persistent-heap cap.
    store.data_mut().persistent_cap = persistent_cap;
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(wasm_error)?;
    let exports = collect_runtime_exports(&instance, &mut store, module_spec)?;
    store.data_mut().exports = exports;
    // Cache the memory so the actor-state ABI can grow it to cover an actor's
    // state region before the first state load/store (M3).
    let memory = instance.get_memory(&mut store, "memory");
    store.data_mut().memory = memory;

    Ok(RuntimeExecution { store })
}

fn collect_runtime_exports(
    instance: &wasmtime::Instance,
    store: &mut Store<StoreData>,
    module_spec: &RuntimeModuleSpec,
) -> Result<HashMap<String, Func>, RuntimeError> {
    let mut exports = HashMap::new();

    for actor in &module_spec.actors {
        if let Some(init_export) = &actor.init_export {
            let func = instance
                .get_func(store.as_context_mut(), init_export)
                .ok_or_else(|| RuntimeError::MissingExport(init_export.clone()))?;
            exports.insert(init_export.clone(), func);
        }
        for handler in &actor.handlers {
            let func = instance
                .get_func(store.as_context_mut(), &handler.export_name)
                .ok_or_else(|| RuntimeError::MissingExport(handler.export_name.clone()))?;
            exports.insert(handler.export_name.clone(), func);
        }
    }

    Ok(exports)
}

fn fuel_decrement_import(
    caller: &mut Caller<'_, StoreData>,
    amount: i32,
) -> Result<(), RuntimeError> {
    let actor_id = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("fuel_decrement"))?;
    let amount = u64::try_from(amount).map_err(|_| RuntimeError::Wasm {
        message: format!("fuel decrement must be non-negative, found `{amount}`"),
    })?;

    let state_rc = Rc::clone(&caller.data().state);
    let mut state = state_rc.borrow_mut();
    let actor = state
        .actors
        .get_mut(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?;
    actor
        .consume_fuel(amount)
        .map_err(|_| RuntimeError::FuelExhausted { actor_id })?;
    Ok(())
}

fn send_import(
    caller: &mut Caller<'_, StoreData>,
    target: i32,
    handler_id: i32,
    payload_buf: i32,
    payload_len: i32,
) -> Result<(), RuntimeError> {
    let sender = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("send"))?;
    let receiver = actor_id_from_i32(target)?;
    let handler_id = handler_id_from_i32(handler_id)?;

    let state_rc = Rc::clone(&caller.data().state);
    let (handler_name, payload) = {
        let state = state_rc.borrow();
        let resolved = resolve_handler(&caller.data().module, &state, receiver, handler_id)?;
        let payload = read_memory_bytes(caller, payload_buf, payload_len)?;
        let _ = decode_payload_args(&payload, &resolved.params, &resolved.handler_name)?;
        (resolved.handler_name, payload)
    };

    let mut state = state_rc.borrow_mut();
    if !state.actors.contains_key(&receiver) {
        return Err(RuntimeError::UnknownActor(receiver));
    }
    let event = AuditEventKind::MessageEnqueued {
        sender: Some(sender),
        receiver,
        handler: handler_name.clone(),
    };
    state
        .message_queue
        .push(Message {
            sender: Some(sender),
            receiver,
            handler: handler_name,
            handler_id,
            payload,
        })
        .map_err(|_| RuntimeError::QueueFull { receiver })?;
    state.audit_log.record(event);

    Ok(())
}

fn ask_import(
    caller: &mut Caller<'_, StoreData>,
    target: i32,
    handler_id: i32,
    payload_buf: i32,
    payload_len: i32,
) -> Result<i64, RuntimeError> {
    let sender = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("ask"))?;
    let receiver = actor_id_from_i32(target)?;
    let handler_id = handler_id_from_i32(handler_id)?;
    let state_rc = Rc::clone(&caller.data().state);
    let resolved = {
        let state = state_rc.borrow();
        resolve_handler(&caller.data().module, &state, receiver, handler_id)?
    };
    let payload = read_memory_bytes(caller, payload_buf, payload_len)?;
    let decoded = decode_payload_args(&payload, &resolved.params, &resolved.handler_name)?;
    // M3 ABI: prepend the receiver's state pointer; grow memory to back its
    // state region before the handler's first load.
    if let Some(memory) = caller.data().memory {
        ensure_state_region(memory, &mut *caller, receiver, resolved.state_size)?;
    }
    let mut args = Vec::with_capacity(decoded.len() + 1);
    args.push(Val::I32(arena_base_of(receiver)? as i32));
    args.extend(decoded);

    {
        let mut state = state_rc.borrow_mut();
        state.audit_log.record(AuditEventKind::MessageEnqueued {
            sender: Some(sender),
            receiver,
            handler: resolved.handler_name.clone(),
        });
    }

    let call_result = call_export_from_caller(caller, &resolved.export_name, receiver, &args);
    match call_result {
        Ok(result) => {
            let mut state = state_rc.borrow_mut();
            state.audit_log.record(AuditEventKind::MessageDelivered {
                sender: Some(sender),
                receiver,
                handler: resolved.handler_name,
            });
            normalize_result(result)
        }
        Err(err) => Err(err),
    }
}

fn spawn_import(
    caller: &mut Caller<'_, StoreData>,
    actor_type_id: i32,
    caps_ptr: i32,
    caps_len: i32,
    fuel_cap: i32,
    supervision: i32,
) -> Result<i32, RuntimeError> {
    let parent = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("spawn"))?;
    let actor_type_id = actor_type_id as u32;
    let caps_len =
        usize::try_from(caps_len).map_err(|_| RuntimeError::UnsupportedSpawnCaps { count: 0 })?;
    let fuel_cap = capability_id_from_i32(fuel_cap)?;
    let actor_spec = actor_spec_by_type_id(&caller.data().module, actor_type_id)?.clone();
    // Threat model: `fuel_cap` below
    // is ownership-verified (release_capability) because it is the linear fuel budget the runtime
    // itself accounts. The rest of `caps` is passed to the child's init WITHOUT a runtime ownership
    // re-check — cap-ownership is trusted to the compiler's C-checks/Z3, which proved the parent
    // owns every spawned cap before this WASM was emitted. A hostile hand-WAT forging an unowned cap
    // id here is OUT of the actor threat model (an actor runs a compiler-verified project, unlike
    // the lone-untrusted-tool forge). Input SHAPE is still validated (read_capability_ids fails loud
    // on an overflowing count); only cap-ownership forgery is delegated to compile time.
    let caps = read_capability_ids(caller, caps_ptr, caps_len)?;
    let state_rc = Rc::clone(&caller.data().state);

    let child_id = {
        let mut state = state_rc.borrow_mut();
        let child_budget = state.capability_table.fuel_units(fuel_cap)?;
        {
            let parent_actor = state
                .actors
                .get_mut(&parent)
                .ok_or(RuntimeError::UnknownActor(parent))?;
            if !parent_actor.release_capability(fuel_cap) {
                return Err(RuntimeError::Capability {
                    message: format!(
                        "actor `{parent}` does not own fuel capability `{}`",
                        fuel_cap.0
                    ),
                });
            }
        }

        let child_id = ActorId(state.next_actor_id);
        state.next_actor_id += 1;

        let strategy = if supervision > 0 {
            SupervisionStrategy::Restart {
                max_restarts: supervision as u32,
            }
        } else {
            SupervisionStrategy::Stop
        };
        let mut child = ActorInstance::new(actor_spec.name.clone(), child_budget, strategy);
        child.own_capability(fuel_cap);
        // PPS-4: retain the ordered init-arg handles so a supervised restart
        // can replay a replay-safe init (restart-as-GC).
        child.record_init_caps(caps.clone(), fuel_cap);
        state.audit_log.record(AuditEventKind::ActorSpawned {
            actor_id: child_id,
            actor_type: actor_spec.name.clone(),
            parent: Some(parent),
        });
        state.actors.insert(child_id, child);
        child_id
    };

    // M3: reserve the state struct at the front of the child's arena — seed its
    // bump cursor past `state_size` so no allocation clobbers state.
    if actor_spec.state_size > 0 {
        let reserved = arena_base_of(child_id)? + actor_spec.state_size;
        caller.data_mut().arena_cursors.insert(child_id, reserved);
    }

    if actor_spec.init_export.is_some() {
        call_actor_init_from_caller(caller, &actor_spec, child_id, &caps, fuel_cap)?;
    }
    // AGG-1: capture the persistent floor now that init's aggregate allocations sit below the
    // cursor — the AL-2 per-dispatch reset will rewind to here, preserving them.
    caller.data_mut().capture_persistent_floor(child_id);

    Ok(child_id.get() as i32)
}

#[allow(clippy::cast_possible_truncation)]
fn alloc_import(caller: &mut Caller<'_, StoreData>, size: i32) -> Result<i32, RuntimeError> {
    bump_arena(caller, size, false)
}

/// AGG-2b: the persistent-heap allocation channel. A bump identical to `alloc_import`, but it ALSO
/// raises the active actor's persistent floor to the new cursor, so the just-allocated buffer sits
/// below the floor and survives the per-dispatch reset. A state-backed collection's grow allocation
/// routes here; every other allocation stays on the transient `alloc` channel.
fn alloc_persistent_import(
    caller: &mut Caller<'_, StoreData>,
    size: i32,
) -> Result<i32, RuntimeError> {
    bump_arena(caller, size, true)
}

/// The shared arena bump. Allocates `size` bytes from the active actor's arena, growing linear
/// memory as needed and trapping on arena exhaustion (the per-actor 64 KB ceiling). When
/// `persistent`, additionally raises the actor's persistent floor to the end of the allocation so
/// the AL-2 per-dispatch reset never reclaims it (B1).
fn bump_arena(
    caller: &mut Caller<'_, StoreData>,
    size: i32,
    persistent: bool,
) -> Result<i32, RuntimeError> {
    let actor_id = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("alloc"))?;
    // The guest-size contract, enforced by the SAME type the forge routes through
    // (alloc_size.rs) — a negative size is rejected here instead of casting to ~4 billion and
    // panicking the host on the align-up.
    let size = crate::alloc_size::AllocBytes::checked_from_guest(size)
        .map_err(|e| RuntimeError::Wasm {
            message: e.to_string(),
        })?
        .get();
    // A validated size is <= i32::MAX, so `+ 7` cannot overflow — but `checked_add` fails loud
    // if that invariant is ever bypassed, matching arena_base's discipline two lines down.
    let aligned_size = size
        .checked_add(7)
        .map(|v| v & !7)
        .ok_or_else(|| RuntimeError::Wasm {
            message: format!("actor `{actor_id}` alloc align-up overflows u32 (size {size})"),
        })?; // align_up(size, 8)
    let actor_index = actor_id.get() as u32;
    let arena_base = actor_index
        .checked_mul(ARENA_SIZE)
        .ok_or_else(|| RuntimeError::Wasm {
            message: format!(
                "actor `{actor_id}` arena base overflows u32 (actor index {actor_index})"
            ),
        })?;
    let cursor = caller
        .data()
        .arena_cursors
        .get(&actor_id)
        .copied()
        .unwrap_or(arena_base);
    let new_cursor = cursor + aligned_size;
    // PPS-4: a persistent allocation raises the floor to `new_cursor`, so the
    // actor's persistent bytes would become `new_cursor - arena_base` — trap
    // with the DISTINCT exhaustion error when that crosses the cap. Checked
    // before the arena bound so a lowered cap fires its own diagnostic (and
    // its restart-as-GC path) rather than the generic arena message.
    if persistent {
        let cap = caller.data().persistent_cap;
        let would_be = new_cursor - arena_base;
        if would_be > cap {
            return Err(RuntimeError::PersistentHeapExhausted {
                actor_id,
                requested: size,
                would_be,
                cap,
            });
        }
    }
    let arena_end = arena_base + ARENA_SIZE;
    if new_cursor > arena_end {
        return Err(RuntimeError::Wasm {
            message: format!(
                "actor `{actor_id}` arena exhausted: tried to allocate {size} bytes at offset {cursor}, arena ends at {arena_end}"
            ),
        });
    }

    // Ensure linear memory is large enough
    let needed_bytes = new_cursor as u64;
    let memory = caller
        .get_export("memory")
        .and_then(|e| e.into_memory())
        .ok_or(RuntimeError::MissingMemoryExport)?;
    let current_bytes = memory.data_size(&caller) as u64;
    if needed_bytes > current_bytes {
        #[allow(clippy::manual_div_ceil)]
        let needed_pages = (needed_bytes - current_bytes + 65535) / 65536;
        memory
            .grow(&mut *caller, needed_pages)
            .map_err(|_| RuntimeError::Wasm {
                message: format!("failed to grow memory by {needed_pages} page(s)"),
            })?;
    }

    caller.data_mut().arena_cursors.insert(actor_id, new_cursor);
    if persistent {
        // B1 floor-raise: the just-allocated buffer [cursor, new_cursor) now sits below the raised
        // floor, so the AL-2 per-dispatch reset (which rewinds the cursor to the floor) never
        // reclaims it. Reuses the AGG-1 persistent_floors machinery, fired at handler time.
        caller
            .data_mut()
            .persistent_floors
            .insert(actor_id, new_cursor);
    }
    Ok(cursor as i32)
}

fn cap_restrict_import(
    caller: &mut Caller<'_, StoreData>,
    cap: i32,
    _restriction: i32,
) -> Result<i32, RuntimeError> {
    // `_restriction` is the authority-set id the WASM ABI passes; the
    // compile-time Z3 layer already verified the restriction is sound,
    // so the runtime treats restrict as an alias-and-rebrand operation
    // that produces a fresh CapabilityId.
    let actor_id = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("cap_restrict"))?;
    let cap_id = capability_id_from_i32(cap)?;

    let state_rc = Rc::clone(&caller.data().state);
    let mut state = state_rc.borrow_mut();
    let actor = state
        .actors
        .get(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?;
    if !actor.owns_capability(cap_id) {
        return Err(RuntimeError::Capability {
            message: format!("actor `{actor_id}` does not own capability `{}`", cap_id.0),
        });
    }

    let new_cap_id = state.capability_table.restrict(cap_id)?;
    state
        .actors
        .get_mut(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?
        .own_capability(new_cap_id);

    Ok(new_cap_id.0 as i32)
}

/// Capabilities-as-values: `mint <Cap> for <target>`. Allocates a fresh
/// capability id and grants it to the active actor. Authority is proven at
/// compile time (the mint gate + Z3), so at runtime mint is a registration:
/// it CREATES a cap (unlike restrict/split, which derive from an owned src),
/// so there is no ownership precondition.
fn cap_mint_import(caller: &mut Caller<'_, StoreData>) -> Result<i32, RuntimeError> {
    let actor_id = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("cap_mint"))?;

    let state_rc = Rc::clone(&caller.data().state);
    let mut state = state_rc.borrow_mut();
    let new_cap_id = state.capability_table.mint();
    state
        .actors
        .get_mut(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?
        .own_capability(new_cap_id);

    Ok(new_cap_id.0 as i32)
}

fn cap_split_import(
    caller: &mut Caller<'_, StoreData>,
    cap: i32,
    amount: i64,
) -> Result<i32, RuntimeError> {
    let actor_id = caller
        .data()
        .active_actor
        .ok_or(RuntimeError::NoActiveActor("cap_split"))?;
    let cap_id = capability_id_from_i32(cap)?;
    // The guest emitter performs the same signed check before calling this
    // import.  Keep an independent host-side check because callers may supply
    // hand-written or tampered Wasm: casting a negative i64 directly to u64
    // would otherwise turn it into a very large, potentially satisfiable draw.
    if amount < 0 {
        return Err(RuntimeError::Capability {
            message: format!("cap_split amount must be non-negative, found {amount}"),
        });
    }
    let amount = amount as u64;

    let state_rc = Rc::clone(&caller.data().state);
    let mut state = state_rc.borrow_mut();
    let actor = state
        .actors
        .get(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?;
    if !actor.owns_capability(cap_id) {
        return Err(RuntimeError::Capability {
            message: format!("actor `{actor_id}` does not own capability `{}`", cap_id.0),
        });
    }

    let new_cap_id = state.capability_table.split(cap_id, amount)?;
    state
        .actors
        .get_mut(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?
        .own_capability(new_cap_id);

    Ok(new_cap_id.0 as i32)
}

fn call_actor_init_from_caller(
    caller: &mut Caller<'_, StoreData>,
    actor_spec: &RuntimeActorSpec,
    actor_id: ActorId,
    caps: &[CapabilityId],
    fuel_cap: CapabilityId,
) -> Result<(), RuntimeError> {
    let Some(export_name) = actor_spec.init_export.as_deref() else {
        return Ok(());
    };
    // M3 ABI: prepend the child actor's state pointer (its arena base); grow
    // memory to back its state region before init's first store.
    if let Some(memory) = caller.data().memory {
        ensure_state_region(memory, &mut *caller, actor_id, actor_spec.state_size)?;
    }
    let init_payload = build_init_args(actor_spec, caps, fuel_cap, export_name)?;
    let mut args = Vec::with_capacity(init_payload.len() + 1);
    args.push(Val::I32(arena_base_of(actor_id)? as i32));
    args.extend(init_payload);

    let _ = call_export_from_caller(caller, export_name, actor_id, &args)?;
    Ok(())
}

fn resolve_handler(
    module: &RuntimeModuleSpec,
    state: &RuntimeState,
    actor_id: ActorId,
    handler_id: u32,
) -> Result<ResolvedHandler, RuntimeError> {
    let actor = state
        .actors
        .get(&actor_id)
        .ok_or(RuntimeError::UnknownActor(actor_id))?;
    let actor_spec =
        actor_spec_by_name(module, actor.actor_type()).ok_or_else(|| RuntimeError::Capability {
            message: format!(
                "runtime actor `{actor_id}` has unknown type `{}`",
                actor.actor_type()
            ),
        })?;
    let handler =
        handler_by_id(actor_spec, handler_id).ok_or_else(|| RuntimeError::UnknownHandler {
            actor: actor.actor_type().to_owned(),
            handler_id,
        })?;

    Ok(ResolvedHandler {
        handler_name: handler.name.clone(),
        export_name: handler.export_name.clone(),
        params: handler.params.clone(),
        state_size: actor_spec.state_size,
    })
}

/// Grow linear memory so `[arena_base, arena_base + state_size)` is backed
/// before any state load/store for `actor_id` (M3). No-op for a stateless actor
/// (`state_size == 0`) or when memory already covers the region. Fails closed if
/// the grow is refused.
fn ensure_state_region(
    memory: Memory,
    mut ctx: impl AsContextMut,
    actor_id: ActorId,
    state_size: u32,
) -> Result<(), RuntimeError> {
    if state_size == 0 {
        return Ok(());
    }
    let needed = u64::from(arena_base_of(actor_id)?) + u64::from(state_size);
    let current = memory.data_size(&ctx) as u64;
    if needed > current {
        let pages = (needed - current).div_ceil(u64::from(ARENA_SIZE));
        memory
            .grow(&mut ctx, pages)
            .map_err(|_| RuntimeError::Wasm {
                message: format!("failed to grow memory to cover actor `{actor_id}` state region"),
            })?;
    }
    Ok(())
}

fn build_init_args(
    actor_spec: &RuntimeActorSpec,
    caps: &[CapabilityId],
    fuel_cap: CapabilityId,
    export_name: &str,
) -> Result<Vec<Val>, RuntimeError> {
    if actor_spec.init_params.is_empty() {
        return Ok(Vec::new());
    }

    if actor_spec.init_params.len() != caps.len() + 1 {
        return Err(RuntimeError::UnsupportedSignature {
            export: export_name.to_owned(),
            params: actor_spec.init_params.len(),
            results: 0,
        });
    }

    let mut args = Vec::with_capacity(actor_spec.init_params.len());
    for (index, ty) in actor_spec.init_params.iter().enumerate() {
        match ty {
            RuntimeTypeSpec::Cap(_) => {
                let cap = if index < caps.len() {
                    caps[index]
                } else {
                    fuel_cap
                };
                args.push(Val::I32(cap.0 as i32));
            }
            other => {
                return Err(RuntimeError::Wasm {
                    message: format!(
                        "actor init `{}` currently supports cap-typed runtime args only, found `{:?}`",
                        export_name, other
                    ),
                });
            }
        }
    }

    Ok(args)
}

fn read_memory_bytes(
    caller: &mut Caller<'_, StoreData>,
    payload_buf: i32,
    payload_len: i32,
) -> Result<Vec<u8>, RuntimeError> {
    if payload_len == 0 {
        return Ok(Vec::new());
    }

    let ptr = usize::try_from(payload_buf).map_err(|_| RuntimeError::Wasm {
        message: format!("payload pointer must be non-negative, found `{payload_buf}`"),
    })?;
    let len = usize::try_from(payload_len).map_err(|_| RuntimeError::Wasm {
        message: format!("payload length must be non-negative, found `{payload_len}`"),
    })?;
    let memory = caller
        .get_export("memory")
        .and_then(|export| export.into_memory())
        .ok_or(RuntimeError::MissingMemoryExport)?;
    let data = memory.data(caller.as_context());
    let end = ptr.checked_add(len).ok_or(RuntimeError::Wasm {
        message: "payload bounds overflowed memory address space".to_owned(),
    })?;
    let bytes = data.get(ptr..end).ok_or(RuntimeError::Wasm {
        message: format!("payload range `{ptr}..{end}` is out of bounds"),
    })?;
    Ok(bytes.to_vec())
}

fn read_capability_ids(
    caller: &mut Caller<'_, StoreData>,
    caps_ptr: i32,
    caps_len: usize,
) -> Result<Vec<CapabilityId>, RuntimeError> {
    if caps_len == 0 {
        return Ok(Vec::new());
    }

    // `caps_len * 4` is the byte length to read. The old `(caps_len * 4) as i32` was a lossy
    // usize->i32 cast: for caps_len >= 2^29 the product wraps and reads the WRONG number of bytes
    // silently (a hostile `spawn` with caps_len = 2^30 read 0 caps and proceeded — RTC-NOOP slice
    // 3). Fail loud instead: a caps count too large to address as an i32 byte length is rejected,
    // never silently truncated. (Input-shape validation is defense-in-depth; the trusted compiler
    // is the authority on a well-formed caps count — RTC-NOOP slice 3.)
    let byte_len = caps_len
        .checked_mul(4)
        .and_then(|n| i32::try_from(n).ok())
        .ok_or(RuntimeError::UnsupportedSpawnCaps { count: caps_len })?;
    let bytes = read_memory_bytes(caller, caps_ptr, byte_len)?;
    // `byte_len` is a checked multiple of 4, so the remainder half of
    // `as_chunks` is empty by construction.
    bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|chunk| Ok(CapabilityId(u32::from_le_bytes(*chunk))))
        .collect()
}

fn decode_payload_args(
    payload: &[u8],
    params: &[RuntimeTypeSpec],
    handler_name: &str,
) -> Result<Vec<Val>, RuntimeError> {
    let expected_len = params.iter().try_fold(0usize, |total, ty| {
        runtime_type_width(ty).map(|width| total + width)
    })?;
    if payload.len() != expected_len {
        return Err(RuntimeError::Wasm {
            message: format!(
                "handler `{handler_name}` expected {expected_len} payload byte(s), found {}",
                payload.len()
            ),
        });
    }

    let mut offset = 0usize;
    let mut values = Vec::with_capacity(params.len());
    for ty in params {
        let (value, consumed) = decode_payload_value(payload, offset, ty, handler_name)?;
        offset += consumed;
        values.push(value);
    }
    Ok(values)
}

fn decode_payload_value(
    payload: &[u8],
    offset: usize,
    ty: &RuntimeTypeSpec,
    handler_name: &str,
) -> Result<(Val, usize), RuntimeError> {
    match ty {
        RuntimeTypeSpec::Bool => {
            let bytes = read_exact::<4>(payload, offset, handler_name, ty)?;
            Ok((Val::I32(i32::from_le_bytes(bytes)), 4))
        }
        RuntimeTypeSpec::I64 => {
            let bytes = read_exact::<8>(payload, offset, handler_name, ty)?;
            Ok((Val::I64(i64::from_le_bytes(bytes)), 8))
        }
        RuntimeTypeSpec::ActorRef(_) | RuntimeTypeSpec::Cap(_) => {
            let bytes = read_exact::<4>(payload, offset, handler_name, ty)?;
            Ok((Val::I32(i32::from_le_bytes(bytes)), 4))
        }
        other => Err(RuntimeError::Wasm {
            message: format!(
                "handler `{handler_name}` currently cannot decode runtime payload type `{:?}`",
                other
            ),
        }),
    }
}

fn runtime_type_width(ty: &RuntimeTypeSpec) -> Result<usize, RuntimeError> {
    match ty {
        RuntimeTypeSpec::Bool | RuntimeTypeSpec::ActorRef(_) | RuntimeTypeSpec::Cap(_) => Ok(4),
        RuntimeTypeSpec::I64 => Ok(8),
        other => Err(RuntimeError::Wasm {
            message: format!(
                "runtime payload serialization currently supports `bool`, `i64`, `ActorRef<T>`, and cap types, found `{:?}`",
                other
            ),
        }),
    }
}

fn read_exact<const N: usize>(
    payload: &[u8],
    offset: usize,
    handler_name: &str,
    ty: &RuntimeTypeSpec,
) -> Result<[u8; N], RuntimeError> {
    let end = offset.checked_add(N).ok_or(RuntimeError::Wasm {
        message: format!("handler `{handler_name}` payload offset overflowed"),
    })?;
    let bytes = payload.get(offset..end).ok_or(RuntimeError::Wasm {
        message: format!(
            "handler `{handler_name}` payload for `{:?}` is truncated at byte {}",
            ty, offset
        ),
    })?;
    let mut out = [0u8; N];
    out.copy_from_slice(bytes);
    Ok(out)
}

fn actor_spec_by_name<'a>(
    module: &'a RuntimeModuleSpec,
    actor_name: &str,
) -> Option<&'a RuntimeActorSpec> {
    module.actors.iter().find(|actor| actor.name == actor_name)
}

fn actor_spec_by_type_id(
    module: &RuntimeModuleSpec,
    actor_type_id: u32,
) -> Result<&RuntimeActorSpec, RuntimeError> {
    module
        .actors
        .iter()
        .find(|actor| actor.actor_type_id == actor_type_id)
        .ok_or(RuntimeError::UnknownActorType(actor_type_id))
}

fn handler_by_id(actor: &RuntimeActorSpec, handler_id: u32) -> Option<&RuntimeHandlerSpec> {
    actor
        .handlers
        .iter()
        .find(|handler| handler.handler_id == handler_id)
}

/// Wasmtime fuel budget granted to a single top-level actor dispatch (init or
/// message handler). Reset before every dispatch in `call_export_from_store`,
/// so a long-lived host never accumulates toward exhaustion. Bounds a handler
/// (and its synchronous re-entrant calls) that never yields — separate from the
/// cooperative SIGIL fuel accounting. See the ephemeral `MAX_WASM_FUEL`.
const MAX_ACTOR_FUEL: u64 = 10_000_000_000;

fn call_export_from_store(
    store: &mut Store<StoreData>,
    export_name: &str,
    actor_id: ActorId,
    args: &[Val],
) -> Result<Option<Val>, RuntimeError> {
    let func = store
        .data()
        .exports
        .get(export_name)
        .cloned()
        .ok_or_else(|| RuntimeError::MissingExport(export_name.to_owned()))?;
    let ty = func.ty(store.as_context());
    let params = ty.params().collect::<Vec<_>>();
    let results = ty.results().collect::<Vec<_>>();
    if params.len() != args.len()
        || results.len() > 1
        || results
            .iter()
            .any(|result| !matches!(result, ValType::I32 | ValType::I64))
    {
        return Err(RuntimeError::UnsupportedSignature {
            export: export_name.to_owned(),
            params: params.len(),
            results: results.len(),
        });
    }

    let mut result_vals = results
        .iter()
        .map(default_value_for_type)
        .collect::<Result<Vec<_>, _>>()?;
    let previous_actor = store.data().active_actor;
    store.data_mut().last_error = None;
    store.data_mut().active_actor = Some(actor_id);
    // Reset the wasmtime fuel budget for THIS dispatch. The store is long-lived
    // across handler calls, so a budget set once at creation would be exhausted
    // cumulatively; each top-level actor call instead gets a fresh backstop.
    // Re-entrant calls (`call_export_from_caller`) intentionally share this
    // budget, bounding the whole synchronous call tree.
    let fuel_cap = store.data().wasm_fuel_cap;
    store.set_fuel(fuel_cap).map_err(wasm_error)?;
    let call_result = func.call(store.as_context_mut(), args, &mut result_vals);
    store.data_mut().active_actor = previous_actor;
    let host_error = store.data_mut().last_error.take();

    match call_result {
        Ok(()) => Ok(result_vals.into_iter().next()),
        Err(err) => Err(host_error.unwrap_or_else(|| wasm_error(err))),
    }
}

fn call_export_from_caller(
    caller: &mut Caller<'_, StoreData>,
    export_name: &str,
    actor_id: ActorId,
    args: &[Val],
) -> Result<Option<Val>, RuntimeError> {
    let func = caller
        .data()
        .exports
        .get(export_name)
        .cloned()
        .ok_or_else(|| RuntimeError::MissingExport(export_name.to_owned()))?;
    let ty = func.ty(caller.as_context());
    let params = ty.params().collect::<Vec<_>>();
    let results = ty.results().collect::<Vec<_>>();
    if params.len() != args.len()
        || results.len() > 1
        || results
            .iter()
            .any(|result| !matches!(result, ValType::I32 | ValType::I64))
    {
        return Err(RuntimeError::UnsupportedSignature {
            export: export_name.to_owned(),
            params: params.len(),
            results: results.len(),
        });
    }

    let mut result_vals = results
        .iter()
        .map(default_value_for_type)
        .collect::<Result<Vec<_>, _>>()?;
    let previous_actor = caller.data().active_actor;
    caller.data_mut().last_error = None;
    caller.data_mut().active_actor = Some(actor_id);
    let call_result = func.call(caller.as_context_mut(), args, &mut result_vals);
    caller.data_mut().active_actor = previous_actor;
    let host_error = caller.data_mut().last_error.take();

    match call_result {
        Ok(()) => Ok(result_vals.into_iter().next()),
        Err(err) => Err(host_error.unwrap_or_else(|| wasm_error(err))),
    }
}

fn default_value_for_type(ty: &ValType) -> Result<Val, RuntimeError> {
    match ty {
        ValType::I32 => Ok(Val::I32(0)),
        ValType::I64 => Ok(Val::I64(0)),
        _ => Err(RuntimeError::Wasm {
            message: format!("unsupported Wasm value type `{ty:?}`"),
        }),
    }
}

fn normalize_result(result: Option<Val>) -> Result<i64, RuntimeError> {
    match result {
        None => Ok(0),
        Some(Val::I32(value)) => Ok(i64::from(value)),
        Some(Val::I64(value)) => Ok(value),
        Some(other) => Err(RuntimeError::Wasm {
            message: format!("unsupported Wasm result `{other:?}`"),
        }),
    }
}

fn actor_id_from_i32(value: i32) -> Result<ActorId, RuntimeError> {
    u64::try_from(value)
        .map(ActorId)
        .map_err(|_| RuntimeError::InvalidActorRef(value))
}

fn capability_id_from_i32(value: i32) -> Result<CapabilityId, RuntimeError> {
    u32::try_from(value)
        .map(CapabilityId)
        .map_err(|_| RuntimeError::InvalidCapabilityRef(value))
}

fn handler_id_from_i32(value: i32) -> Result<u32, RuntimeError> {
    Ok(value as u32)
}

fn record_host_error(caller: &mut Caller<'_, StoreData>, err: RuntimeError) -> wasmtime::Error {
    caller.data_mut().last_error = Some(err.clone());
    wasmtime::Error::msg(err.to_string())
}

fn wasm_error(err: impl fmt::Display) -> RuntimeError {
    RuntimeError::Wasm {
        message: err.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use sigil_compiler::compile_module;

    use crate::{RuntimeHost, audit::AuditEventKind};

    fn compile_runtime_fixture(source: &str) -> sigil_compiler::Compilation {
        compile_module(source).expect("fixture should compile")
    }

    #[test]
    fn bootstraps_entry_actor_and_queues_start() {
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
entry actor Main {
    on Start() {}
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);

        let report = host
            .bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");

        assert_eq!(report.module_name, "sigil");
        assert_eq!(report.queued_messages, 1);
        assert_eq!(host.actors().len(), 1);
        assert_eq!(host.pending_messages(), 1);
        assert_eq!(host.capability_table().len(), 1);
    }

    #[test]
    fn drains_messages_and_records_delivery() {
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
entry actor Main {
    on Start() {}
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);

        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host
            .drain_messages(8)
            .expect("message drain should succeed");

        assert_eq!(delivered, 1);
        assert_eq!(host.pending_messages(), 0);
        assert!(
            host.audit_log()
                .events()
                .iter()
                .any(|event| matches!(event.kind, AuditEventKind::MessageDelivered { .. }))
        );
    }

    #[test]
    fn state_cap_persists_from_init_to_handler() {
        // M3 acceptance — breaks the cap-0 coincidence. The entry draws a DISTINCT
        // fuel cap (host id 1, not the entry's own id 0) and spawns Worker with it;
        // Worker's `init` stores it into `state { power }`; Worker's handler draws
        // from `power`. `draw` checks the actor OWNS the cap, so it succeeds ONLY
        // if `power` persisted the REAL drawn id — not the garbage/0 the old
        // (pre-state-pointer) codegen read. A runtime Capability error here would
        // mean state did not persist.
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let sub = fuel.draw(50);
        let w = spawn::<Worker>(sub);
        w.send(Tick());
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) { power = f; }
    on Tick() { let s = power.draw(10); }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host.drain_messages(8).expect(
            "Worker.Tick must draw from its persisted state cap — a Capability error \
             here means the state pointer did not carry the real cap id",
        );
        assert_eq!(delivered, 2, "both Start and Tick deliver");
        // fuel(0) + drawn sub(1) + Worker's power.draw(2) = 3 caps: the third only
        // exists if the handler's `power.draw` actually ran against a cap Worker owns.
        assert_eq!(
            host.capability_table().len(),
            3,
            "the handler's draw off persisted state must have minted a third cap"
        );
    }

    #[test]
    fn restart_of_stateful_cap_init_actor_does_not_respend_state_cap() {
        // State-cap restart soundness. `init` may receive a state cap, and restart may re-run
        // init. The question: can those two combine into a cross-restart double-spend of a
        // state cap?
        //
        // They cannot, and this pins why — the RATIONALE changed at PPS-4 while every assertion
        // held. Pre-PPS-4, AG-AL7 fenced ALL cap-init actors from replay, so init's `StoreField`
        // simply never re-ran. PPS-4 retains the spawn's init-arg handles and REPLAYS a
        // replay-safe init (this Worker's `power = f;` store-only body qualifies): the StoreField
        // now DOES re-run — with the IDENTICAL retained handle, writing the same i32 into the
        // same slot. Storing a handle mints nothing and spends nothing, so the table still must
        // not grow. (An init that DERIVES — `f.draw(n)` — is NOT replay-safe and keeps the
        // preserve-state path; `pps4_restart_as_gc.rs` pins that half.)
        // Worker stores its cap into state (exercising the M3 StoreField, unlike the empty-init
        // `cap_init_supervised_actor_survives_trap`), then its handler traps under Restart(1).
        // The host must SURVIVE (the trap is absorbed) and the capability table must NOT grow past
        // the two caps that legitimately exist (fuel(0) + the drawn sub(1)) — a third cap would be
        // exactly the double-spend this test exists to catch.
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let sub = fuel.draw(50);
        let w = spawn::<Worker>(sub, supervision: Restart(1));
        w.send(Boom());
        return 0;
    }
}
actor Worker {
    state { power: Fuel }
    init(f: Fuel) { power = f; }
    on Boom() -> i64 { trap(); }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        // Start + Boom deliver; Boom traps and is absorbed by Restart(1) — the drain SURVIVES.
        let delivered = host
            .drain_messages(8)
            .expect("the Boom trap must be absorbed by Restart supervision, not abort the drain");
        assert_eq!(
            delivered, 2,
            "both Start and Boom deliver (Boom's trap is caught)"
        );
        let restarts = host
            .audit_log()
            .events()
            .iter()
            .filter(|e| matches!(e.kind, AuditEventKind::ActorRestarted { .. }))
            .count();
        assert_eq!(
            restarts, 1,
            "the single Boom trap triggers exactly one restart"
        );
        // The replay did NOT respend `power`: the reinit re-stored the RETAINED handle (PPS-4),
        // which touches no table row. Only fuel(0) + the drawn sub(1) exist — a third cap would
        // be the cross-restart double-spend.
        assert_eq!(
            host.capability_table().len(),
            2,
            "replaying init's state-cap store must not mint — no third cap may exist"
        );
    }

    #[test]
    fn mut_state_field_read_after_write_is_not_stale() {
        // MUTABLE-STATE S2 / the read-model fix. A handler that WRITES a `mut` field
        // then READS it back must see the NEW value. Before the fresh-load fix a
        // handler read resolved to the load-once cached env local (the prologue value),
        // so `count = count + 1; let seen = count;` bound `seen` to the STALE 0 — a
        // silent wrong answer. Worker.Bump increments `count` (0 -> 1), reads it back,
        // and `trap()`s iff the read-back is not 1. The drain SURVIVES only when the
        // fresh-`LoadField` read model makes the read-after-write see the store.
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Worker>(fuel);
        w.send(Bump());
        return 0;
    }
}
actor Worker {
    state { mut count: i64 }
    init(f: Fuel) { count = 0; }
    on Bump() {
        count = count + 1;
        let seen = count;
        if seen != 1 { trap(); }
    }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host.drain_messages(8).expect(
            "Bump's read-after-write must see the new `count`; a stale (load-once) read \
             would make `seen` 0, trap, and fail the drain",
        );
        assert_eq!(
            delivered, 2,
            "both Start and Bump deliver (Bump does not trap)"
        );
    }

    #[test]
    fn nonmut_aggregate_state_field_persists_across_dispatches() {
        // AGG-1 (persistent-aggregate-state) — the crux test. A NON-`mut` record state field `d`
        // is set once in `init` to `Box { x: 42 }`; a handler ALLOCATES a scratch `Box` (which
        // would clobber `d`'s heap object if it lived in the transient region the AL-2 reset
        // rewinds), then a `Check` handler reads `d.x` back and `trap()`s iff it is not 42.
        //
        // Before AGG-1 this TRAPPED (the record's bytes were bump-allocated above `arena_base +
        // state_size` and reclaimed each dispatch). AGG-1 makes the AL-2 reset floor the POST-INIT
        // cursor, so init's allocation is below the floor and survives; the handler's scratch is
        // above it and is rewound. All three messages must deliver (Check must not trap).
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
record Box { x: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Probe>(fuel);
        w.send(Bump());
        w.send(Check(42));
        return 0;
    }
}
actor Probe {
    state { d: Box }
    init(f: Fuel) { d = Box { x: 42 }; }
    on Bump() { let scratch = Box { x: 999 }; }
    on Check(expected: i64) { let s2 = Box { x: 777 }; if d.x != expected { trap(); } }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host.drain_messages(16);
        assert_eq!(
            delivered,
            Ok(3),
            "a non-`mut` record state field must persist across dispatches: Start + Bump + \
             Check(42) must all deliver. If this traps, `d`'s heap object was clobbered — the \
             persistent floor did not protect init's allocation."
        );
    }

    #[test]
    fn nonmut_aggregate_persists_across_shapes() {
        // AGG-1 property: a NON-`mut` aggregate state field of ANY flat shape (record of k scalar
        // fields, fixed array, tuple) persists across dispatches — the persistent floor protects
        // init's allocation regardless of the field's size/shape. Each case sets the field in
        // init, a Bump handler allocates a scratch record (would clobber a transient field), and a
        // Check handler reads the field back and traps iff it is not 42. All 3 messages must
        // deliver for every shape. Sampled across representative shapes (property-flavored; a full
        // proptest would compile+run hundreds of guests — this covers the size/shape axis cheaply).
        let cases: &[(&str, &str, &str, &str, &str)] = &[
            // (label, extra_defs, state_decl, init_assign, check_expr)
            (
                "record-1",
                "record R1 { a: i64 }",
                "d: R1",
                "d = R1 { a: 42 };",
                "d.a",
            ),
            (
                "record-3",
                "record R3 { a: i64, b: i64, c: i64 }",
                "d: R3",
                "d = R3 { a: 1, b: 2, c: 42 };",
                "d.c",
            ),
            ("array-4", "", "a: [i64; 4]", "a = [1, 2, 3, 42];", "a[3]"),
            (
                "array-8",
                "",
                "a: [i64; 8]",
                "a = [0, 0, 0, 0, 0, 0, 0, 42];",
                "a[7]",
            ),
            // (tuple state fields hit a separate pre-existing `t.N` projection parser limit — not
            // an AGG-1 concern; records + arrays cover the size/shape axis.)
        ];
        for (label, extra_defs, state_decl, init_assign, check_expr) in cases {
            let src = format!(
                r#"
module sigil;
cap type Fuel {{}}
record Scratch {{ z: i64 }}
{extra_defs}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{
        let w = spawn::<Probe>(fuel);
        w.send(Bump());
        w.send(Check(42));
        return 0;
    }}
}}
actor Probe {{
    state {{ {state_decl} }}
    init(f: Fuel) {{ {init_assign} }}
    on Bump() {{ let scratch = Scratch {{ z: 999 }}; }}
    on Check(expected: i64) {{ let s2 = Scratch {{ z: 777 }}; if {check_expr} != expected {{ trap(); }} }}
}}
"#
            );
            let compilation = compile_runtime_fixture(&src);
            let mut host = RuntimeHost::new(compilation.fuel_budget);
            host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
                .unwrap_or_else(|e| panic!("[{label}] bootstrap should succeed: {e:?}"));
            let delivered = host.drain_messages(16);
            assert_eq!(
                delivered,
                Ok(3),
                "[{label}] a non-`mut` aggregate state field must persist across dispatches"
            );
        }
    }

    #[test]
    fn aggregate_state_capstone_ledger() {
        // AGG-3 capstone — "lasting software with aggregate memory". A `Ledger` actor holds a
        // NON-`mut` config record `cfg` (read across dispatches, AGG-1) AND a `mut` counter record
        // `c` (mutated IN PLACE across dispatches, AGG-2a) in the same actor. Each Add reads
        // `cfg.limit` and, if under the limit, accumulates `c.total` in place — after a scratch
        // allocation that would clobber a transient object. Both aggregate fields must persist:
        // Add(30)->30, Add(30)->60, Add(50)->110>100 so REJECTED (stays 60), Check(60). All 5
        // messages deliver iff both the non-mut config and the mut counter survived every reset.
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
record Config { limit: i64 }
record Counter { total: i64 }
record Scratch { z: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Ledger>(fuel);
        w.send(Add(30));
        w.send(Add(30));
        w.send(Add(50));
        w.send(Check(60));
        return 0;
    }
}
actor Ledger {
    state { cfg: Config, mut c: Counter }
    init(f: Fuel) { cfg = Config { limit: 100 }; c = Counter { total: 0 }; }
    on Add(n: i64) {
        let scratch = Scratch { z: 999 };
        let next: i64 = c.total + n;
        if next <= cfg.limit { c.total = next; }
    }
    on Check(expected: i64) { let s2 = Scratch { z: 777 }; if c.total != expected { trap(); } }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host.drain_messages(16);
        assert_eq!(
            delivered,
            Ok(5),
            "a non-`mut` config record AND a `mut` counter record must BOTH persist across \
             dispatches: the limit gate (60+50>100) holds and Check(60) does not trap"
        );
    }

    #[test]
    fn mut_flat_record_state_field_mutated_in_place_persists() {
        // AGG-2a: a `mut` FLAT-FIXED record state field, mutated IN PLACE across dispatches, must
        // persist. `c` is init-allocated below the persistent floor; each Add does `c.total =
        // c.total + n` (a StoreField into that persistent object — NO new allocation) after
        // allocating a scratch record that would clobber a transient object. Accumulate 0 -> 5 ->
        // 8; Check(8) traps iff wrong. All 4 messages must deliver.
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
record Counter { total: i64 }
record Scratch { z: i64 }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Acc>(fuel);
        w.send(Add(5));
        w.send(Add(3));
        w.send(Check(8));
        return 0;
    }
}
actor Acc {
    state { mut c: Counter }
    init(f: Fuel) { c = Counter { total: 0 }; }
    on Add(n: i64) { let scratch = Scratch { z: 999 }; c.total = c.total + n; }
    on Check(expected: i64) { let s2 = Scratch { z: 777 }; if c.total != expected { trap(); } }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host.drain_messages(16);
        assert_eq!(
            delivered,
            Ok(4),
            "a `mut` flat record field mutated in place must accumulate 0->5->8 across dispatches"
        );
    }

    #[test]
    fn mut_state_accumulates_across_dispatches_demonstrator() {
        // MUTABLE-STATE S3 — the "lasting software with memory" demonstrator. A `Counter`
        // accumulates a running total ACROSS many dispatches: `total` persists between
        // handler invocations (the whole point of mutable state). Start spawns Counter and
        // sends Add(5), Add(3), then Check(8) — which `trap()`s iff the accumulated total is
        // not 8. The drain surviving proves `total` went 0 -> 5 -> 8 across three separate
        // Counter dispatches (a per-dispatch reset would leave it at 3, trapping Check).
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Counter>(fuel);
        w.send(Add(5));
        w.send(Add(3));
        w.send(Check(8));
        return 0;
    }
}
actor Counter {
    state { mut total: i64 }
    init(f: Fuel) { total = 0; }
    on Add(n: i64) { total = total + n; }
    on Check(expected: i64) { if total != expected { trap(); } }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);
        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");
        let delivered = host.drain_messages(16).expect(
            "Counter must accumulate `total` across dispatches; a per-dispatch reset would \
             make Check(8) see 3 and trap",
        );
        assert_eq!(
            delivered, 4,
            "Start + Add(5) + Add(3) + Check(8) all deliver (Check does not trap)"
        );
    }

    #[test]
    fn mut_state_is_order_dependent_confluence_canary() {
        // MUTABLE-STATE S3 — the confluence canary. Immutable-state actors are
        // schedule-invariant (quiescent-confluence, the governor property); a `mut` actor
        // OPTS OUT of that — its outcome can depend on delivery order. This canary makes the
        // forfeit a TEST, not prose, and is RED-FIRST: it uses a NON-commutative op
        // (last-write-wins `Set`), so the two orders genuinely diverge — a commutative op
        // (like Add) would make it vacuously pass. `Check(2)` `trap()`s iff `val != 2`.
        //
        // Order A — Set(1); Set(2) → val = 2 → Check(2) SURVIVES.
        // Order B — Set(2); Set(1) → val = 1 → Check(2) TRAPS.
        // The two delivery orders of the SAME message multiset yield DIFFERENT outcomes ⇒
        // confluence is forfeited for the `mut` actor (the documented opt-in cost).
        fn run(order: &str) -> Result<usize, String> {
            let src = format!(
                r#"
module sigil;
cap type Fuel {{}}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{
        let w = spawn::<LastWrite>(fuel);
        {order}
        w.send(Check(2));
        return 0;
    }}
}}
actor LastWrite {{
    state {{ mut val: i64 }}
    init(f: Fuel) {{ val = 0; }}
    on Set(n: i64) {{ val = n; }}
    on Check(expected: i64) {{ if val != expected {{ trap(); }} }}
}}
"#
            );
            let compilation = compile_runtime_fixture(&src);
            let mut host = RuntimeHost::new(compilation.fuel_budget);
            host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
                .expect("bootstrap should succeed");
            host.drain_messages(16).map_err(|e| format!("{e:?}"))
        }
        let order_a = run("w.send(Set(1));\n        w.send(Set(2));");
        let order_b = run("w.send(Set(2));\n        w.send(Set(1));");
        assert_eq!(
            order_a,
            Ok(4),
            "order A (Set(1); Set(2)) leaves val=2, so Check(2) passes and all 4 deliver"
        );
        assert!(
            order_b.is_err(),
            "order B (Set(2); Set(1)) leaves val=1, so Check(2) TRAPS — the `mut` actor is \
             order-DEPENDENT (confluence forfeited); got {order_b:?}"
        );
    }

    // MUTABLE-STATE S3 — restart-to-birth semantics for a `mut` actor. A compiled fixture
    // CANNOT express it: a spawned actor requires a fuel-cap spawn argument (R011), so its
    // `init` takes a cap (cap-init), and AG-AL7 fences a cap-init actor from replay — restart
    // is refill+reset (state PRESERVED), not reinit. Reinit-to-birth is reachable only for a
    // REPLAYABLE (no-cap-arg) init, which today is exercised via hand-WAT in
    // `actor_live_restart.rs::restart_reinitializes_replayable_actor_state` (sentinel mem[0]
    // reset to 42) — the reinit mechanism (init re-run → `StoreField` resets the field) is
    // field-TYPE-agnostic, so it applies to a `mut` field verbatim. The complementary cap-init
    // `mut` case (restart PRESERVES state, no reinit / no cap double-spend) is
    // `restart_of_stateful_cap_init_actor_does_not_respend_state_cap` above.

    #[test]
    fn returns_no_entry_actor_when_metadata_has_none() {
        let compilation = compile_runtime_fixture("module sigil;");
        let mut host = RuntimeHost::new(compilation.fuel_budget);

        let report = host
            .bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("bootstrap should succeed");

        assert_eq!(report.entry_actor, None);
        assert_eq!(report.queued_messages, 0);
        assert_eq!(host.actors().len(), 0);
    }

    #[test]
    fn executes_zero_arg_spawn_send_and_ask_through_wasm() {
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start() -> i64 {
        let worker = spawn::<Worker>(fuel);
        worker.send(Ping());
        return worker.ask(GetCount(), timeout: 5);
    }
}

actor Worker {
    init(fuel: Fuel) {}

    on Ping() {}

    on GetCount() -> i64 {
        return 7;
    }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);

        let report = host
            .bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("runtime should bootstrap");
        let delivered = host
            .drain_messages(32)
            .expect("runtime should execute queued messages");

        assert_eq!(report.queued_messages, 1);
        assert_eq!(delivered, 2);
        assert_eq!(host.actors().len(), 2);
        assert_eq!(host.pending_messages(), 0);
        assert!(host.audit_log().events().iter().any(|event| matches!(
            event.kind,
            AuditEventKind::ActorSpawned {
                parent: Some(_),
                ..
            }
        )));
        assert!(
            host.audit_log()
                .events()
                .iter()
                .any(|event| matches!(&event.kind, AuditEventKind::MessageDelivered { handler, .. } if handler == "GetCount"))
        );
    }

    #[test]
    fn executes_parameterized_send_and_ask_through_wasm() {
        let compilation = compile_runtime_fixture(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start() -> i64 {
        let worker = spawn::<Worker>(fuel);
        worker.send(SetReady(true));
        return worker.ask(Add(4, 3), timeout: 5);
    }
}

actor Worker {
    init(fuel: Fuel) {}

    on SetReady(flag: bool) {
        if flag {
            return;
        } else {
            return;
        }
    }

    on Add(lhs: i64, rhs: i64) -> i64 {
        return lhs + rhs;
    }
}
"#,
        );
        let mut host = RuntimeHost::new(compilation.fuel_budget);

        host.bootstrap(&compilation.runtime_module, &compilation.wasm_inner)
            .expect("runtime should bootstrap");
        let delivered = host
            .drain_messages(32)
            .expect("runtime should execute parameterized messages");

        assert_eq!(delivered, 2);
        assert_eq!(host.pending_messages(), 0);
        assert!(
            host.audit_log()
                .events()
                .iter()
                .any(|event| matches!(&event.kind, AuditEventKind::MessageDelivered { handler, .. } if handler == "Add"))
        );
        assert!(
            host.audit_log()
                .events()
                .iter()
                .any(|event| matches!(&event.kind, AuditEventKind::MessageDelivered { handler, .. } if handler == "SetReady"))
        );
    }

    #[test]
    fn actor_handler_infinite_loop_is_bounded_by_fuel_backstop() {
        use sigil_abi::{
            RuntimeActorSpec, RuntimeHandlerSpec, RuntimeImportSpec, RuntimeModuleSpec,
            RuntimeTypeSpec,
        };

        // Hand-written actor wasm: a benign init plus a `Start` handler that
        // loops forever WITHOUT ever calling the cooperative `fuel_decrement`
        // import. A SIGIL-compiled loop would charge cooperative fuel, so the
        // module must be hand-written to exercise the per-dispatch wasmtime
        // fuel backstop in `call_export_from_store` specifically (finding
        // P1/P2). The test completing rather than hanging is the core
        // assertion — without the backstop this never returns.
        let wasm = wat::parse_str(
            r#"
            (module
              (memory (export "memory") 1)
              (func (export "actor_init") (param i32))
              (func (export "loop_handler") (param i32) (result i64)
                (loop $l (br $l))
                (i64.const 0)))
            "#,
        )
        .expect("hand-written actor wasm compiles");

        let spec = RuntimeModuleSpec {
            module_name: "loop_mod".to_string(),
            fuel_budget: 1_000,
            imports: RuntimeImportSpec::phase_one(),
            actors: vec![RuntimeActorSpec {
                name: "Main".to_string(),
                actor_type_id: 0,
                is_entry: true,
                init_export: Some("actor_init".to_string()),
                init_params: vec![],
                handlers: vec![RuntimeHandlerSpec {
                    name: "Start".to_string(),
                    handler_id: 0,
                    export_name: "loop_handler".to_string(),
                    params: vec![],
                    ret: RuntimeTypeSpec::I64,
                }],
                state_layout: vec![],
                state_size: 0,
                init_replay_safe: false,
            }],
        };

        let mut host = RuntimeHost::new(1_000);
        host.bootstrap(&spec, &wasm)
            .expect("bootstrap runs the benign init and queues Start");
        // Inject a small wasmtime fuel cap so the looping handler trips the
        // backstop in milliseconds instead of burning billions of ops.
        host.execution
            .as_mut()
            .unwrap()
            .store
            .data_mut()
            .wasm_fuel_cap = 200_000;

        let result = host.drain_messages(1);
        assert!(
            result.is_err(),
            "a non-cooperative actor handler loop must be bounded by the fuel backstop, got {result:?}"
        );
    }
}
