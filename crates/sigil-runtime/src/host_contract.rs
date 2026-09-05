//! Host-provider-owned function/contract binding.
//!
//! This is the binding foundation for the occurrence-aware compiler context,
//! not a new formal certificate or a sandbox entry point. Providers register
//! real typed functions with their declarations; finishing checks each actual
//! Wasm signature and freezes the linker and profile together. Instantiation
//! checks the module's required profile before its start function can execute.
//!
//! Host behavior (including complete state footprints and isolation) remains
//! trusted. This API does not claim to inspect callback bodies or establish
//! CSIR/Wasm correspondence. Callers own Store fuel, limits, capabilities, and
//! any other host state; existing actor/ephemeral execution keeps its own gates.

use std::fmt;

use sigil_abi::host_contract::{
    HOST_PROFILE_SECTION, HostContractError, HostContractProfile, HostDomain,
    HostOperationContract, HostProfileRequirement, HostValueType,
};
use wasmparser::{Parser, Payload};
use wasmtime::{Engine, Instance, IntoFunc, Linker, Module, Store, ValType};

#[derive(Debug)]
pub enum HostBindingError {
    Contract(HostContractError),
    InvalidModule(String),
    MissingProfile,
    DuplicateProfile,
    UnknownProfileSection,
    LegacyProfileUnsupported,
    EngineMismatch,
    Link(String),
}

impl fmt::Display for HostBindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Contract(error) => error.fmt(f),
            Self::InvalidModule(error) => write!(f, "invalid host-bound Wasm: {error}"),
            Self::MissingProfile => {
                write!(f, "host-bound module is missing its required host profile")
            }
            Self::DuplicateProfile => write!(f, "duplicate required host profile"),
            Self::UnknownProfileSection => write!(f, "unknown host-profile section"),
            Self::LegacyProfileUnsupported => write!(
                f,
                "host security profile requires contract-bound instantiation"
            ),
            Self::EngineMismatch => write!(f, "host bindings and store use different engines"),
            Self::Link(error) => write!(f, "host binding failed: {error}"),
        }
    }
}

impl std::error::Error for HostBindingError {}

impl From<HostContractError> for HostBindingError {
    fn from(error: HostContractError) -> Self {
        Self::Contract(error)
    }
}

/// The host provider supplies the callbacks, not just a claimed profile. The
/// linker is private and cannot be mutated after `finish` binds its profile.
pub struct HostBindingsBuilder<T: 'static> {
    linker: Linker<T>,
    identity: String,
    revision: u64,
    domains: Vec<HostDomain>,
    contracts: Vec<HostOperationContract>,
}

impl<T: 'static> HostBindingsBuilder<T> {
    pub fn new(engine: &Engine, identity: String, revision: u64, domains: Vec<HostDomain>) -> Self {
        Self {
            linker: Linker::new(engine),
            identity,
            revision,
            domains,
            contracts: vec![],
        }
    }

    /// Consuming registration keeps a failed/partial builder from being reused.
    /// Wasmtime derives the actual ABI from the typed callback independently of
    /// the provider's declared ABI; `finish` compares them before returning it.
    pub fn define<Params, Results>(
        mut self,
        contract: HostOperationContract,
        callback: impl IntoFunc<T, Params, Results>,
    ) -> Result<Self, HostBindingError> {
        self.linker
            .func_wrap(&contract.module, &contract.name, callback)
            .map_err(|error| HostBindingError::Link(error.to_string()))?;
        self.contracts.push(contract);
        Ok(self)
    }

    pub fn finish(
        self,
        store: &mut Store<T>,
    ) -> Result<InstalledHostBindings<T>, HostBindingError> {
        if !Engine::same(self.linker.engine(), store.engine()) {
            return Err(HostBindingError::EngineMismatch);
        }
        let profile =
            HostContractProfile::new(self.identity, self.revision, self.domains, self.contracts)?;
        for contract in profile.operations() {
            let function = self
                .linker
                .get(&mut *store, &contract.module, &contract.name)
                .map_err(|error| HostBindingError::Link(error.to_string()))?
                .into_func()
                .ok_or_else(|| {
                    HostBindingError::Link(format!(
                        "missing host function {}::{}",
                        contract.module, contract.name
                    ))
                })?;
            let ty = function.ty(&*store);
            let params = signature(ty.params())?;
            let results = signature(ty.results())?;
            profile.resolve(&contract.module, &contract.name, &params, &results)?;
        }
        Ok(InstalledHostBindings {
            linker: self.linker,
            profile,
        })
    }
}

pub struct InstalledHostBindings<T: 'static> {
    linker: Linker<T>,
    profile: HostContractProfile,
}

impl<T: 'static> InstalledHostBindings<T> {
    /// May be used to construct a compiler's explicit host context. The profile
    /// is immutable and was obtained from these installed callbacks.
    pub fn profile(&self) -> &HostContractProfile {
        &self.profile
    }

    pub fn instantiate(
        &self,
        store: &mut Store<T>,
        wasm: &[u8],
    ) -> Result<Instance, HostBindingError> {
        if !Engine::same(self.linker.engine(), store.engine()) {
            return Err(HostBindingError::EngineMismatch);
        }
        let required = required_host_profile(wasm)?.ok_or(HostBindingError::MissingProfile)?;
        self.profile
            .check_required_fingerprint(&required.fingerprint)?;
        let module = Module::from_binary(self.linker.engine(), wasm)
            .map_err(|error| HostBindingError::InvalidModule(error.to_string()))?;
        // Link validation runs before instantiation/start. The private linker
        // contains exactly the functions whose ABI was checked by finish.
        self.linker
            .instantiate(store, &module)
            .map_err(|error| HostBindingError::Link(error.to_string()))
    }
}

fn signature(types: impl Iterator<Item = ValType>) -> Result<Vec<HostValueType>, HostBindingError> {
    types
        .map(|ty| match ty {
            ValType::I32 => Ok(HostValueType::I32),
            ValType::I64 => Ok(HostValueType::I64),
            ValType::F32 => Ok(HostValueType::F32),
            ValType::F64 => Ok(HostValueType::F64),
            _ => Err(HostBindingError::Link(
                "unsupported host function ABI type".into(),
            )),
        })
        .collect()
}

fn required_host_profile(wasm: &[u8]) -> Result<Option<HostProfileRequirement>, HostBindingError> {
    let mut required = None;
    for payload in Parser::new(0).parse_all(wasm) {
        let payload =
            payload.map_err(|error| HostBindingError::InvalidModule(error.to_string()))?;
        if let Payload::CustomSection(section) = payload {
            if !section.name().starts_with(HOST_PROFILE_SECTION) {
                continue;
            }
            if section.name() != HOST_PROFILE_SECTION {
                return Err(HostBindingError::UnknownProfileSection);
            }
            if required.is_some() {
                return Err(HostBindingError::DuplicateProfile);
            }
            required = Some(HostProfileRequirement::decode(section.data())?);
        }
    }
    Ok(required)
}

/// Legacy entry points cannot ignore assumptions that they do not implement.
/// Modules without host requirements retain their existing import behavior.
pub(crate) fn reject_unbound_host_profile(wasm: &[u8]) -> Result<(), HostBindingError> {
    if required_host_profile(wasm)?.is_some() {
        Err(HostBindingError::LegacyProfileUnsupported)
    } else {
        Ok(())
    }
}

/// A module with no requirement keeps legacy semantics; a module that requires a profile runs
/// only under a host whose declared profile has exactly that fingerprint. Any other requirement
/// is refused (fail closed): the module's declarations were verified against a host this one
/// is not.
pub(crate) fn check_host_profile_requirement(
    wasm: &[u8],
    installed: &HostContractProfile,
) -> Result<(), HostBindingError> {
    match required_host_profile(wasm)? {
        None => Ok(()),
        Some(required) => Ok(installed.check_required_fingerprint(&required.fingerprint)?),
    }
}
