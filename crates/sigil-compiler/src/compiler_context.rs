//! Explicit provider declarations for occurrence-aware compiler integration.
//!
//! The context preserves an immutable host profile and resolves source externs
//! against the exact import identity emitted by `wasm.rs`. Missing declarations
//! and mismatching identities/signatures fail closed; caller-computed labels
//! cannot substitute for a provider's operation contract. This configuration is
//! not host approval, a certificate, or evidence of callback conformance. The
//! runtime must independently match the requirement against its own bindings.
//!
//! Existing compile entry points use the empty legacy default. Context-aware
//! entry points pass declarations to the mandatory formal gate and bind every
//! emitted Wasm ring to the exact checked profile fingerprint. The requirement
//! is not runtime approval and does not classify an undeclared host as private.

use std::fmt;
use std::sync::Arc;

pub use sigil_abi::host_contract::HostContractProfile;
use sigil_abi::host_contract::{
    HostContractError, HostOperationContract, HostProfileRequirement, HostValueType,
    MAX_HOST_NAME_BYTES,
};

/// Source extern names are emitted unchanged in this Wasm namespace. Source
/// module names and the `extern` ABI string do not select a host import module.
pub const EXTERN_IMPORT_MODULE: &str = "ffi";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilerContextError {
    MissingHostProfile,
    UnsupportedExternName(String),
    HostContract(HostContractError),
}

impl fmt::Display for CompilerContextError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingHostProfile => write!(f, "compiler context has no host declarations"),
            Self::UnsupportedExternName(name) => {
                write!(f, "unsupported source extern identity `{name}`")
            }
            Self::HostContract(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for CompilerContextError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::HostContract(error) => Some(error),
            _ => None,
        }
    }
}

impl From<HostContractError> for CompilerContextError {
    fn from(error: HostContractError) -> Self {
        Self::HostContract(error)
    }
}

/// The embedding provider's declaration configuration, not an approval token.
///
/// Profiles may also be decoded from arbitrary bytes; constructing this value
/// does not authenticate their provenance. A trusted embedding chooses the
/// profile, and execution must still check the runtime's independent bindings.
/// Clones share the same immutable profile instead of copying its bounded wire
/// representation. No mutable profile access or per-call label override exists.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CompilerContext {
    host_profile: Option<Arc<HostContractProfile>>,
}

impl CompilerContext {
    pub fn with_host_profile(profile: impl Into<Arc<HostContractProfile>>) -> Self {
        Self {
            host_profile: Some(profile.into()),
        }
    }

    pub fn host_profile(&self) -> Option<&HostContractProfile> {
        self.host_profile.as_deref()
    }

    /// Canonical declarations to bind into the versioned compiler projection.
    /// Absence means legacy configuration, never an implicit private contract.
    pub fn canonical_host_profile_bytes(&self) -> Option<&[u8]> {
        self.host_profile()
            .map(HostContractProfile::canonical_bytes)
    }

    pub fn host_profile_fingerprint(&self) -> Option<[u8; 32]> {
        self.host_profile().map(HostContractProfile::fingerprint)
    }

    /// A requirement is a request for the exact profile, not permission to run.
    /// The ABI owns its canonical encoding and the runtime owns its validation.
    pub fn host_requirement(&self) -> Option<HostProfileRequirement> {
        self.host_profile_fingerprint()
            .map(|fingerprint| HostProfileRequirement { fingerprint })
    }

    /// Resolve an already lowered extern signature without guessing its labels.
    ///
    /// Use the actual ordered Wasm parameter/result types from AIR integration;
    /// pointer footprints remain part of the returned provider declaration, not
    /// something scalar type equality proves. Names are single source identifiers:
    /// qualified aliases, trimming, case folding, and host-module remaps fail closed.
    pub fn resolve_extern(
        &self,
        name: &str,
        params: &[HostValueType],
        results: &[HostValueType],
    ) -> Result<&HostOperationContract, CompilerContextError> {
        let profile = self
            .host_profile()
            .ok_or(CompilerContextError::MissingHostProfile)?;
        if !source_extern_name_supported(name) {
            return Err(CompilerContextError::UnsupportedExternName(name.to_owned()));
        }
        Ok(profile.resolve(EXTERN_IMPORT_MODULE, name, params, results)?)
    }
}

fn source_extern_name_supported(name: &str) -> bool {
    // The lexer admits ASCII identifiers. Keep identity exact and bounded by
    // the profile format; do not make a qualified source name match its suffix.
    let mut bytes = name.bytes();
    name.len() <= MAX_HOST_NAME_BYTES
        && bytes
            .next()
            .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}
