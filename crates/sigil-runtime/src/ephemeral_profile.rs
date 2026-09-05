//! The ephemeral host's own declared host profile.
//!
//! `execute_ephemeral` links a fixed set of `ffi` operations. This module states that set as a
//! canonical [`HostContractProfile`] so a tool can be compiled against the host that will run it:
//! every operation is declared with the exact Wasm signature the linker defines, with Internal
//! occurrence (a call may happen under control that depends on Internal data, such as the error
//! code of the previous host call), Internal parameter labels, and Internal results. That is the
//! CSIR v9 declaration the legacy no-profile context cannot express, where every host operation
//! is Public-occurrence and a tool that checks one host result before making the next call is
//! refused.
//!
//! Load-bearing constraint: this table must equal the linker's `ffi` inventory name for name and
//! type for type, in both directions. `ephemeral_profile_declares_exactly_the_linked_ffi_imports`
//! in `ephemeral.rs` asserts that against the real linker, so an operation added to one side and
//! not the other fails there rather than at a user's first `--host-profile ephemeral` compile.
//! The runtime accepts a module that requires exactly this profile's fingerprint and still refuses
//! any other requirement (fail closed); a module with no requirement keeps its legacy semantics.
//!
//! A runtime built with the `solver` feature links one more operation, the Cap<Z3> shim
//! `z3_check`, so it is a different host: it declares itself under its own identity with that
//! operation in the table, and its fingerprint differs. A tool bound to one build is refused by
//! the other, which is the correct direction: its declarations were verified against an
//! operation set the other build does not link.

use std::sync::{Arc, OnceLock};

use sigil_abi::host_contract::{
    HostContractProfile, HostOperationContract, HostValueContract, HostValueType,
    OccurrenceVisibility, SecurityLabel,
};

/// Stable identity of the built-in ephemeral host in every profile fingerprint. A name denotes
/// exactly one operation set, so the solver build, which links `z3_check` too, has its own.
#[cfg(not(feature = "solver"))]
pub const EPHEMERAL_HOST_IDENTITY: &str = "sigil-ephemeral";
/// The solver build's identity; see [`SOLVER_OPERATIONS`].
#[cfg(feature = "solver")]
pub const EPHEMERAL_HOST_IDENTITY: &str = "sigil-ephemeral-solver";
/// Bump when an operation is added, removed, or retyped; the fingerprint changes with it and
/// every tool compiled against the old profile is refused by the new host.
pub const EPHEMERAL_HOST_REVISION: u64 = 1;

/// `(name, parameter count of i32, result type)` for every `ffi` import the ephemeral linker
/// defines. Every parameter of every operation is an `i32` pointer or length and every result
/// is a packed `i64`, which the table encodes as a count rather than a list so the type
/// discipline is visible at a glance.
const EPHEMERAL_OPERATIONS: &[(&str, usize)] = &[
    ("crypto_sha256", 2),
    ("crypto_sha512", 2),
    ("fs_list", 2),
    ("fs_read", 2),
    ("fs_write", 4),
    ("http_get", 2),
    ("http_post", 4),
    ("http_post_hdrs", 6),
    ("http_post_secret", 6),
    ("kv_delete", 4),
    ("kv_get", 4),
    ("kv_put", 6),
    ("random_bytes", 1),
    ("time_now", 0),
];

/// The operations the ephemeral linker defines only under the `solver` feature: the Cap<Z3>
/// shim (`docs/z3-runtime-capability.md`), which a default runtime neither links nor declares.
/// Both arms exist so the table is total in every build and the inventory test stays exact.
#[cfg(feature = "solver")]
const SOLVER_OPERATIONS: &[(&str, usize)] = &[("z3_check", 2)];
/// See the `solver` arm: a default build links no solver shim and declares none.
#[cfg(not(feature = "solver"))]
const SOLVER_OPERATIONS: &[(&str, usize)] = &[];

fn operation(name: &str, i32_params: usize) -> HostOperationContract {
    HostOperationContract {
        module: "ffi".to_owned(),
        name: name.to_owned(),
        occurrence: OccurrenceVisibility::Internal,
        params: vec![
            HostValueContract {
                ty: HostValueType::I32,
                label: SecurityLabel::Internal,
            };
            i32_params
        ],
        results: vec![HostValueContract {
            ty: HostValueType::I64,
            label: SecurityLabel::Internal,
        }],
        domains: Vec::new(),
    }
}

fn build() -> HostContractProfile {
    HostContractProfile::new(
        EPHEMERAL_HOST_IDENTITY.to_owned(),
        EPHEMERAL_HOST_REVISION,
        Vec::new(),
        EPHEMERAL_OPERATIONS
            .iter()
            .chain(SOLVER_OPERATIONS)
            .map(|(name, params)| operation(name, *params))
            .collect(),
    )
    .expect("the ephemeral host's declared operations form a valid profile (every name is a valid identifier, revision is nonzero, no duplicates, and Internal results carry every Internal influence)")
}

/// The ephemeral host's canonical profile, built once per process.
pub fn ephemeral_host_profile() -> Arc<HostContractProfile> {
    static PROFILE: OnceLock<Arc<HostContractProfile>> = OnceLock::new();
    PROFILE.get_or_init(|| Arc::new(build())).clone()
}

/// Resolve a host profile by the name a command line or service config uses.
/// Only the built-in ephemeral host is known; anything else is refused by name.
pub fn host_profile_by_name(name: &str) -> Option<Arc<HostContractProfile>> {
    match name {
        "ephemeral" => Some(ephemeral_host_profile()),
        _ => None,
    }
}
