//! `sigil-runtime` -- the wasmtime host for compiled SIGIL: resident actors,
//! fuel, capabilities, I/O grants, and ephemeral tool execution. Crate root:
//! module wiring and re-exports only; `#![forbid(unsafe_code)]` below is the
//! crate-wide guarantee, and the repo-wide census tests live in `tests/`.

#![forbid(unsafe_code)]

pub mod actor;
pub mod alloc_size;
pub mod audit;
pub mod capability;
pub mod ephemeral;
pub mod ephemeral_profile;
pub use ephemeral_profile::{ephemeral_host_profile, host_profile_by_name};
pub mod fuel;
pub mod grants;
pub mod host_contract;
pub mod message;
pub mod runtime;
pub mod serve;
pub mod supervisor;
pub mod trace;

pub use actor::{ActorId, ActorInstance};
pub use audit::{AuditEvent, AuditEventKind, AuditLog};
pub use capability::{Capability, CapabilityError, CapabilityId, CapabilityTable, FuelCapability};
pub use ephemeral::{
    ToolError, ToolResult, execute_ephemeral, execute_ephemeral_with_memory_budget,
};
pub use fuel::{FuelBudget, FuelExhausted};
pub use grants::{
    FsGrant, FsWriteGrant, GrantValidationError, HttpMethod, IoGrants, KvGrant, KvWriteGrant,
    MAX_GRANTS_PER_CATEGORY, NetGrant, RandomGrant, SecretGrant, TimeGrant, Z3Grant,
};
pub use message::{Message, MessageQueue};
pub use runtime::{RuntimeBootReport, RuntimeError, RuntimeHost, WasmParamKind};
pub use serve::{MAX_SERVE_LINE, ServeStats, serve_loop};
pub use sigil_abi::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeImportSpec, RuntimeModuleSpec, RuntimeTypeSpec,
};
pub use supervisor::SupervisionStrategy;
