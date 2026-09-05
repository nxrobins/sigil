//! The compiler-to-runtime ABI contract: the `sigil` host-import name
//! constants plus the `RuntimeModuleSpec` metadata (actors, handlers, state
//! layout, fuel budget) that `sigil-compiler` emits and `sigil-runtime`
//! trusts at instantiation. Both sides link against this one crate, so an
//! edit here moves emitter and host together and no link error catches it;
//! the literal names and wasm-level signatures are pinned instead by
//! `crates/sigil-runtime/tests/runtime_import_contract.rs`. Layout flows one
//! way: state-field offsets are computed once compiler-side
//! (`state_layout_offsets` over AIR widths) and the runtime consumes them
//! verbatim, never recomputing a width. The legacy runtime spec is pure data;
//! field semantics (PPS-4 `init_replay_safe`, AGG-2b `alloc_persistent`)
//! carry their spec citations at the declaration site.
//!
//! [`host_contract`] defines the separately versioned, validated host-profile
//! vocabulary for occurrence-aware security. Constructing a profile is not
//! approval of a host implementation and does not enable private imports.

#![forbid(unsafe_code)]

pub mod host_contract;

pub const RUNTIME_IMPORT_MODULE: &str = "sigil";
pub const RUNTIME_IMPORT_FUEL_DECREMENT: &str = "fuel_decrement";
pub const RUNTIME_IMPORT_SEND: &str = "send";
pub const RUNTIME_IMPORT_ASK: &str = "ask";
pub const RUNTIME_IMPORT_SPAWN: &str = "spawn";
pub const RUNTIME_IMPORT_ALLOC: &str = "alloc";
pub const RUNTIME_IMPORT_CAP_RESTRICT: &str = "cap_restrict";
pub const RUNTIME_IMPORT_CAP_SPLIT: &str = "cap_split";
/// Capabilities-as-values: the `mint` host import — allocates a fresh
/// capability id for a `mint <Cap> for <target>` expression.
pub const RUNTIME_IMPORT_CAP_MINT: &str = "cap_mint";
/// AGG-2b (persistent collection heap): the persistent-heap allocation channel.
/// Identical to `alloc`, but the host ALSO raises the actor's persistent floor
/// so the allocated buffer survives the AL-2 per-dispatch reset (the B1
/// floor-raise). A state-backed collection's grow-alloc routes here; every other
/// allocation stays on the transient `alloc` channel. Emitted only when a module
/// contains a state-backed collection (the conditional-append import, AGG2b-2),
/// so it is ABSENT from state-free modules and the self-host byte capstone.
pub const RUNTIME_IMPORT_ALLOC_PERSISTENT: &str = "alloc_persistent";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeTypeSpec {
    Unit,
    Bool,
    I64,
    Str,
    Named(String),
    ActorRef(String),
    Cap(String),
    Option(Box<RuntimeTypeSpec>),
    Result {
        ok: Box<RuntimeTypeSpec>,
        err: Box<RuntimeTypeSpec>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeImportSpec {
    pub module: String,
    pub fuel_decrement: String,
    pub send: String,
    pub ask: String,
    pub spawn: String,
    pub alloc: String,
    pub cap_restrict: String,
    pub cap_split: String,
    pub cap_mint: String,
    /// AGG-2b: the persistent-heap allocation channel name (`alloc_persistent`).
    pub alloc_persistent: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeHandlerSpec {
    pub name: String,
    pub handler_id: u32,
    pub export_name: String,
    pub params: Vec<RuntimeTypeSpec>,
    pub ret: RuntimeTypeSpec,
}

/// One actor state field's placement in the per-actor state struct (the front
/// of the actor's arena). Emitted by the compiler so the runtime can populate
/// the entry actor's state at bootstrap and reserve the arena prefix.
///
/// `offset` is the byte offset within the state struct (0-based, no closure
/// table-index prefix), computed once on the compiler side from the SINGLE
/// placement authority — the AIR field width (`AirType::width`, via
/// `state_layout_offsets`) — and trusted here, never recomputed. The runtime
/// consumes these emitted offsets directly, so there is no independent
/// runtime-side width to reconcile: the offset IS the width contract.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeStateFieldSpec {
    pub name: String,
    pub offset: u32,
    pub ty: RuntimeTypeSpec,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeActorSpec {
    pub name: String,
    pub actor_type_id: u32,
    pub is_entry: bool,
    pub init_export: Option<String>,
    pub init_params: Vec<RuntimeTypeSpec>,
    pub handlers: Vec<RuntimeHandlerSpec>,
    /// Per-actor state struct layout (declaration order). Empty for a stateless
    /// actor. Lives at the front of the actor's arena; `state_size` bytes are
    /// reserved before the bump allocator's first allocation.
    pub state_layout: Vec<RuntimeStateFieldSpec>,
    /// Total state struct size in bytes, aligned up to 8. `0` when stateless.
    pub state_size: u32,
    /// PPS-4 (restart-as-GC): whether this actor's `init` body is faithfully
    /// REPLAYABLE — it performs no capability-table operation (draw/split/
    /// restrict/mint), no spawn/send/ask, no extern/grant/effect call, and
    /// passes no capability to a helper. A replay-safe init merely rebuilds
    /// state from its retained argument handles, so a supervised restart may
    /// discard the actor's persistent heap and re-run it. Computed by a
    /// fail-closed compile-time walk (an unrecognized construct ⇒ `false`);
    /// `false` restricts restart to the preserve-state path.
    pub init_replay_safe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeModuleSpec {
    pub module_name: String,
    pub fuel_budget: u64,
    pub imports: RuntimeImportSpec,
    pub actors: Vec<RuntimeActorSpec>,
}

impl RuntimeImportSpec {
    pub fn phase_one() -> Self {
        Self {
            module: RUNTIME_IMPORT_MODULE.to_owned(),
            fuel_decrement: RUNTIME_IMPORT_FUEL_DECREMENT.to_owned(),
            send: RUNTIME_IMPORT_SEND.to_owned(),
            ask: RUNTIME_IMPORT_ASK.to_owned(),
            spawn: RUNTIME_IMPORT_SPAWN.to_owned(),
            alloc: RUNTIME_IMPORT_ALLOC.to_owned(),
            cap_restrict: RUNTIME_IMPORT_CAP_RESTRICT.to_owned(),
            cap_split: RUNTIME_IMPORT_CAP_SPLIT.to_owned(),
            cap_mint: RUNTIME_IMPORT_CAP_MINT.to_owned(),
            alloc_persistent: RUNTIME_IMPORT_ALLOC_PERSISTENT.to_owned(),
        }
    }
}

impl RuntimeActorSpec {
    pub fn handler_named(&self, name: &str) -> Option<&RuntimeHandlerSpec> {
        self.handlers.iter().find(|handler| handler.name == name)
    }
}

impl RuntimeModuleSpec {
    pub fn entry_actor(&self) -> Option<&RuntimeActorSpec> {
        self.actors.iter().find(|actor| actor.is_entry)
    }

    pub fn entry_start_handler(&self) -> Option<&RuntimeHandlerSpec> {
        self.entry_actor()
            .and_then(|actor| actor.handler_named("Start"))
    }

    pub fn export_count(&self) -> usize {
        self.actors
            .iter()
            .map(|actor| actor.handlers.len() + usize::from(actor.init_export.is_some()))
            .sum()
    }
}
