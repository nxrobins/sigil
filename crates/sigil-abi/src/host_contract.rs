//! Canonical declarations for an occurrence-aware host boundary.
//!
//! An operation's occurrence is independent of its payload/response labels.
//! All state, streams, queues, allocation identities, logs, and guest-memory
//! effects of an implementation must be covered by its declared domains. A
//! consumed input stream is a read AND a write: advancing its cursor can affect
//! a later Public operation even if the current response is discarded.
//!
//! This module validates and fingerprints declarations, NOT implementations.
//! A runtime must obtain declarations from its installed host bindings, never
//! approve a profile supplied by a guest, and check the required fingerprint
//! before instantiation (including any Wasm start function). Host conformance
//! remains a trusted assumption. No existing host is classified as private by
//! this module; retained CSIR v8 semantics and the schema-v9 certificate layout
//! are unchanged, while production CSIR v9 binds this profile explicitly.

use std::collections::BTreeMap;
use std::fmt;

use sha2::{Digest, Sha256};

/// This is the host-profile encoding version, NOT a CSIR or certificate version.
pub const HOST_PROFILE_VERSION: u32 = 1;
pub const MAX_HOST_PROFILE_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_HOST_PROFILE_ITEMS: usize = 1_000_000;
pub const MAX_HOST_NAME_BYTES: usize = 1024;

/// Reserved Wasm custom-section namespace. Legacy runtimes must reject it,
/// rather than execute a module while ignoring its host security assumptions.
pub const HOST_PROFILE_SECTION: &str = "sigil.host-profile";
pub const HOST_REQUIREMENT_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostProfileRequirement {
    pub fingerprint: [u8; 32],
}

impl HostProfileRequirement {
    pub fn encode(self) -> [u8; 36] {
        let mut bytes = [0; 36];
        bytes[..4].copy_from_slice(&HOST_REQUIREMENT_VERSION.to_le_bytes());
        bytes[4..].copy_from_slice(&self.fingerprint);
        bytes
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, HostContractError> {
        let bytes: &[u8; 36] = bytes
            .try_into()
            .map_err(|_| HostContractError::InvalidEncoding)?;
        let version = u32::from_le_bytes(
            bytes[..4]
                .try_into()
                .map_err(|_| HostContractError::InvalidEncoding)?,
        );
        if version != HOST_REQUIREMENT_VERSION {
            return Err(HostContractError::UnsupportedVersion(version));
        }
        Ok(Self {
            fingerprint: bytes[4..]
                .try_into()
                .map_err(|_| HostContractError::InvalidEncoding)?,
        })
    }
}

const PROFILE_MAGIC: &[u8] = b"SIGIL-HOST-PROFILE\0";

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum SecurityLabel {
    #[default]
    Public = 0,
    Internal = 1,
    Secret = 2,
    SecretCt = 3,
}

/// Host calls are variable-time boundaries. SecretCT cannot control their
/// occurrence; this deliberately has no SecretCT variant.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[repr(u8)]
pub enum OccurrenceVisibility {
    #[default]
    Public = 0,
    Internal = 1,
    Secret = 2,
}

impl OccurrenceVisibility {
    pub const fn label(self) -> SecurityLabel {
        match self {
            Self::Public => SecurityLabel::Public,
            Self::Internal => SecurityLabel::Internal,
            Self::Secret => SecurityLabel::Secret,
        }
    }
}

/// Exact scalar Wasm ABI. Memory reachable through pointer arguments must ALSO
/// appear in the domain footprint; a scalar signature is not a memory contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum HostValueType {
    I32 = 0,
    I64 = 1,
    F32 = 2,
    F64 = 3,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostValueContract {
    pub ty: HostValueType,
    pub label: SecurityLabel,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum HostDomainKind {
    State = 0,
    InputStream = 1,
    Output = 2,
    GuestMemory = 3,
}

/// A declared partition is an obligation on the installed implementation. In
/// particular, a shared PRNG is NOT a per-site stream just because a call site
/// or its result carries a private label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum HostDomainScope {
    Shared = 0,
    PerSite = 1,
    PerActor = 2,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostDomain {
    pub name: String,
    pub kind: HostDomainKind,
    pub scope: HostDomainScope,
    pub label: SecurityLabel,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum HostAccessMode {
    Read = 0,
    Write = 1,
    ReadWrite = 2,
}

impl HostAccessMode {
    const fn reads(self) -> bool {
        matches!(self, Self::Read | Self::ReadWrite)
    }

    const fn writes(self) -> bool {
        matches!(self, Self::Write | Self::ReadWrite)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostDomainAccess {
    pub domain: String,
    pub mode: HostAccessMode,
}

/// A declaration made by the host provider, not by the caller of an operation.
///
/// The initial profile language uses a conservative dependency contract: every
/// result and every written domain depends on occurrence, all parameters, and
/// all read domains. An operation that needs a finer dependency summary needs
/// a separately versioned extension; omitting a domain is never that extension.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostOperationContract {
    pub module: String,
    pub name: String,
    pub occurrence: OccurrenceVisibility,
    pub params: Vec<HostValueContract>,
    pub results: Vec<HostValueContract>,
    pub domains: Vec<HostDomainAccess>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostContractError {
    InvalidName,
    ZeroRevision,
    TooManyItems,
    TooManyBytes,
    InvalidEncoding,
    UnsupportedVersion(u32),
    NonCanonicalEncoding,
    DuplicateDomain(String),
    DuplicateOperation { module: String, name: String },
    DuplicateAccess(String),
    UnknownDomain(String),
    InvalidAccess(String),
    SecretCtInput,
    DomainFlow { domain: String },
    ResultFlow { result: usize },
    UnknownOperation { module: String, name: String },
    SignatureMismatch { module: String, name: String },
    ProfileMismatch,
}

impl fmt::Display for HostContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidName => {
                write!(f, "host contract name is empty, oversized, or noncanonical")
            }
            Self::ZeroRevision => write!(f, "host contract revision must be nonzero"),
            Self::TooManyItems => write!(f, "host contract exceeds the item ceiling"),
            Self::TooManyBytes => write!(f, "host contract exceeds the byte ceiling"),
            Self::InvalidEncoding => write!(f, "malformed or truncated host profile"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported host profile version {version}")
            }
            Self::NonCanonicalEncoding => write!(f, "host profile is not canonically ordered"),
            Self::DuplicateDomain(name) => write!(f, "duplicate host domain {name}"),
            Self::DuplicateOperation { module, name } => {
                write!(f, "duplicate host operation {module}::{name}")
            }
            Self::DuplicateAccess(name) => write!(f, "duplicate access to host domain {name}"),
            Self::UnknownDomain(name) => write!(f, "unknown host domain {name}"),
            Self::InvalidAccess(name) => write!(f, "invalid access mode for host domain {name}"),
            Self::SecretCtInput => write!(f, "SecretCT input to a variable-time host operation"),
            Self::DomainFlow { domain } => {
                write!(f, "host operation can influence lower domain {domain}")
            }
            Self::ResultFlow { result } => {
                write!(f, "host operation can influence lower result {result}")
            }
            Self::UnknownOperation { module, name } => {
                write!(f, "unknown host operation {module}::{name}")
            }
            Self::SignatureMismatch { module, name } => {
                write!(f, "host signature mismatch for {module}::{name}")
            }
            Self::ProfileMismatch => {
                write!(f, "required host profile differs from installed profile")
            }
        }
    }
}

impl std::error::Error for HostContractError {}

/// A structurally valid, immutable declaration set. This is not an approval
/// token or a formal-verification report. Only the actual host's binding layer
/// can establish which profile its implementation promises to satisfy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostContractProfile {
    identity: String,
    revision: u64,
    domains: Vec<HostDomain>,
    operations: Vec<HostOperationContract>,
    canonical_bytes: Vec<u8>,
    fingerprint: [u8; 32],
}

impl HostContractProfile {
    pub fn new(
        identity: String,
        revision: u64,
        mut domains: Vec<HostDomain>,
        mut operations: Vec<HostOperationContract>,
    ) -> Result<Self, HostContractError> {
        valid_name(&identity)?;
        if revision == 0 {
            return Err(HostContractError::ZeroRevision);
        }
        // Check sizes before sorting or allocating derived indexes/encoding.
        validate_budget(&identity, &domains, &operations)?;
        domains.sort_by(|left, right| left.name.cmp(&right.name));
        operations
            .sort_by(|left, right| (&left.module, &left.name).cmp(&(&right.module, &right.name)));
        let mut domain_index = BTreeMap::new();
        for domain in &domains {
            valid_name(&domain.name)?;
            if domain_index.insert(domain.name.as_str(), domain).is_some() {
                return Err(HostContractError::DuplicateDomain(domain.name.clone()));
            }
        }
        let mut previous = None;
        for operation in &mut operations {
            valid_name(&operation.module)?;
            valid_name(&operation.name)?;
            let key = (operation.module.as_str(), operation.name.as_str());
            if previous == Some(key) {
                // Wasm linkers bind a module/name pair to ONE function. Do not
                // treat a changed signature as a second overload of that name.
                return Err(HostContractError::DuplicateOperation {
                    module: operation.module.clone(),
                    name: operation.name.clone(),
                });
            }
            previous = Some(key);
            operation.domains.sort_by(|a, b| a.domain.cmp(&b.domain));
            validate_operation(operation, &domain_index)?;
        }
        let canonical_bytes = encode_profile(&identity, revision, &domains, &operations);
        debug_assert!(canonical_bytes.len() <= MAX_HOST_PROFILE_BYTES);
        let fingerprint = Sha256::digest(&canonical_bytes).into();
        Ok(Self {
            identity,
            revision,
            domains,
            operations,
            canonical_bytes,
            fingerprint,
        })
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    /// Decode declarations, not host approval. Bounds and discriminants are
    /// checked before allocation. Noncanonical order and trailing data fail
    /// closed instead of being normalized into the same certificate identity.
    pub fn decode(bytes: &[u8]) -> Result<Self, HostContractError> {
        if bytes.len() > MAX_HOST_PROFILE_BYTES {
            return Err(HostContractError::TooManyBytes);
        }
        let mut reader = ProfileReader {
            remaining: bytes,
            items: 0,
        };
        if reader.take(PROFILE_MAGIC.len())? != PROFILE_MAGIC {
            return Err(HostContractError::InvalidEncoding);
        }
        let version = reader.u32()?;
        if version != HOST_PROFILE_VERSION {
            return Err(HostContractError::UnsupportedVersion(version));
        }
        let identity = reader.name()?;
        let revision = reader.u64()?;
        let count = reader.count(8)?;
        let mut domains = Vec::with_capacity(count);
        for _ in 0..count {
            let name = reader.name()?;
            let kind = match reader.byte()? {
                0 => HostDomainKind::State,
                1 => HostDomainKind::InputStream,
                2 => HostDomainKind::Output,
                3 => HostDomainKind::GuestMemory,
                _ => return Err(HostContractError::InvalidEncoding),
            };
            let scope = match reader.byte()? {
                0 => HostDomainScope::Shared,
                1 => HostDomainScope::PerSite,
                2 => HostDomainScope::PerActor,
                _ => return Err(HostContractError::InvalidEncoding),
            };
            domains.push(HostDomain {
                name,
                kind,
                scope,
                label: reader.label()?,
            });
        }
        let count = reader.count(23)?;
        let mut operations = Vec::with_capacity(count);
        for _ in 0..count {
            let module = reader.name()?;
            let name = reader.name()?;
            let occurrence = match reader.byte()? {
                0 => OccurrenceVisibility::Public,
                1 => OccurrenceVisibility::Internal,
                2 => OccurrenceVisibility::Secret,
                _ => return Err(HostContractError::InvalidEncoding),
            };
            let params = reader.values()?;
            let results = reader.values()?;
            let count = reader.count(6)?;
            let mut accesses = Vec::with_capacity(count);
            for _ in 0..count {
                let domain = reader.name()?;
                let mode = match reader.byte()? {
                    0 => HostAccessMode::Read,
                    1 => HostAccessMode::Write,
                    2 => HostAccessMode::ReadWrite,
                    _ => return Err(HostContractError::InvalidEncoding),
                };
                accesses.push(HostDomainAccess { domain, mode });
            }
            operations.push(HostOperationContract {
                module,
                name,
                occurrence,
                params,
                results,
                domains: accesses,
            });
        }
        if !reader.remaining.is_empty() {
            return Err(HostContractError::InvalidEncoding);
        }
        let profile = Self::new(identity, revision, domains, operations)?;
        if profile.canonical_bytes != bytes {
            return Err(HostContractError::NonCanonicalEncoding);
        }
        Ok(profile)
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn domains(&self) -> &[HostDomain] {
        &self.domains
    }

    pub fn operations(&self) -> &[HostOperationContract] {
        &self.operations
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub fn fingerprint(&self) -> [u8; 32] {
        self.fingerprint
    }

    /// Call this on the profile obtained from installed host bindings, not on
    /// declarations decoded from a guest. Equality binds the whole profile,
    /// including state domains, rather than merely the currently used names.
    pub fn check_required_fingerprint(&self, required: &[u8; 32]) -> Result<(), HostContractError> {
        if &self.fingerprint == required {
            Ok(())
        } else {
            Err(HostContractError::ProfileMismatch)
        }
    }

    /// Resolve by the actual Wasm identity AND exact ordered signature. Caller
    /// labels cannot replace the provider's occurrence/payload declarations.
    pub fn resolve(
        &self,
        module: &str,
        name: &str,
        params: &[HostValueType],
        results: &[HostValueType],
    ) -> Result<&HostOperationContract, HostContractError> {
        let index = self.operations.binary_search_by(|operation| {
            (operation.module.as_str(), operation.name.as_str()).cmp(&(module, name))
        });
        let operation = index
            .ok()
            .map(|index| &self.operations[index])
            .ok_or_else(|| HostContractError::UnknownOperation {
                module: module.to_owned(),
                name: name.to_owned(),
            })?;
        if !operation
            .params
            .iter()
            .map(|value| value.ty)
            .eq(params.iter().copied())
            || !operation
                .results
                .iter()
                .map(|value| value.ty)
                .eq(results.iter().copied())
        {
            return Err(HostContractError::SignatureMismatch {
                module: module.to_owned(),
                name: name.to_owned(),
            });
        }
        Ok(operation)
    }
}

struct ProfileReader<'a> {
    remaining: &'a [u8],
    items: usize,
}

impl<'a> ProfileReader<'a> {
    fn take(&mut self, count: usize) -> Result<&'a [u8], HostContractError> {
        let (value, rest) = self
            .remaining
            .split_at_checked(count)
            .ok_or(HostContractError::InvalidEncoding)?;
        self.remaining = rest;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, HostContractError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, HostContractError> {
        Ok(u32::from_le_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| HostContractError::InvalidEncoding)?,
        ))
    }

    fn u64(&mut self) -> Result<u64, HostContractError> {
        Ok(u64::from_le_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| HostContractError::InvalidEncoding)?,
        ))
    }

    fn name(&mut self) -> Result<String, HostContractError> {
        let length = self.u32()? as usize;
        if length > MAX_HOST_NAME_BYTES {
            return Err(HostContractError::InvalidName);
        }
        let value =
            std::str::from_utf8(self.take(length)?).map_err(|_| HostContractError::InvalidName)?;
        valid_name(value)?;
        Ok(value.to_owned())
    }

    fn count(&mut self, minimum_bytes_per_item: usize) -> Result<usize, HostContractError> {
        let count = self.u32()? as usize;
        self.items = self
            .items
            .checked_add(count)
            .ok_or(HostContractError::TooManyItems)?;
        if self.items > MAX_HOST_PROFILE_ITEMS {
            return Err(HostContractError::TooManyItems);
        }
        if count > self.remaining.len() / minimum_bytes_per_item {
            return Err(HostContractError::InvalidEncoding);
        }
        Ok(count)
    }

    fn label(&mut self) -> Result<SecurityLabel, HostContractError> {
        match self.byte()? {
            0 => Ok(SecurityLabel::Public),
            1 => Ok(SecurityLabel::Internal),
            2 => Ok(SecurityLabel::Secret),
            3 => Ok(SecurityLabel::SecretCt),
            _ => Err(HostContractError::InvalidEncoding),
        }
    }

    fn values(&mut self) -> Result<Vec<HostValueContract>, HostContractError> {
        let count = self.count(2)?;
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            let ty = match self.byte()? {
                0 => HostValueType::I32,
                1 => HostValueType::I64,
                2 => HostValueType::F32,
                3 => HostValueType::F64,
                _ => return Err(HostContractError::InvalidEncoding),
            };
            values.push(HostValueContract {
                ty,
                label: self.label()?,
            });
        }
        Ok(values)
    }
}

fn valid_name(name: &str) -> Result<(), HostContractError> {
    // Restrict identifiers rather than Unicode-normalizing or trimming them:
    // both would allow distinct declared identities to alias at binding time.
    if name.is_empty()
        || name.len() > MAX_HOST_NAME_BYTES
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"_./:-".contains(&byte))
    {
        return Err(HostContractError::InvalidName);
    }
    Ok(())
}

fn validate_operation(
    operation: &HostOperationContract,
    domains: &BTreeMap<&str, &HostDomain>,
) -> Result<(), HostContractError> {
    let mut influence = operation.occurrence.label();
    for value in &operation.params {
        influence = influence.max(value.label);
    }
    let mut previous = None;
    for access in &operation.domains {
        valid_name(&access.domain)?;
        if previous == Some(access.domain.as_str()) {
            return Err(HostContractError::DuplicateAccess(access.domain.clone()));
        }
        previous = Some(access.domain.as_str());
        let domain = domains
            .get(access.domain.as_str())
            .ok_or_else(|| HostContractError::UnknownDomain(access.domain.clone()))?;
        match domain.kind {
            HostDomainKind::InputStream if access.mode != HostAccessMode::ReadWrite => {
                return Err(HostContractError::InvalidAccess(access.domain.clone()));
            }
            HostDomainKind::Output if access.mode != HostAccessMode::Write => {
                return Err(HostContractError::InvalidAccess(access.domain.clone()));
            }
            _ => {}
        }
        if access.mode.reads() {
            influence = influence.max(domain.label);
        }
    }
    if influence == SecurityLabel::SecretCt {
        return Err(HostContractError::SecretCtInput);
    }
    for access in &operation.domains {
        if access.mode.writes() && influence > domains[access.domain.as_str()].label {
            return Err(HostContractError::DomainFlow {
                domain: access.domain.clone(),
            });
        }
    }
    for (result, value) in operation.results.iter().enumerate() {
        if influence > value.label {
            return Err(HostContractError::ResultFlow { result });
        }
    }
    Ok(())
}

fn validate_budget(
    identity: &str,
    domains: &[HostDomain],
    operations: &[HostOperationContract],
) -> Result<(), HostContractError> {
    let mut items = domains
        .len()
        .checked_add(operations.len())
        .ok_or(HostContractError::TooManyItems)?;
    let mut bytes = PROFILE_MAGIC.len() + 4 + 4 + identity.len() + 8 + 4 + 4;
    for domain in domains {
        bytes = bytes
            .checked_add(4 + domain.name.len() + 3)
            .ok_or(HostContractError::TooManyBytes)?;
    }
    for operation in operations {
        for count in [
            operation.params.len(),
            operation.results.len(),
            operation.domains.len(),
        ] {
            items = items
                .checked_add(count)
                .ok_or(HostContractError::TooManyItems)?;
        }
        let signature_bytes = operation
            .params
            .len()
            .checked_add(operation.results.len())
            .and_then(|count| count.checked_mul(2))
            .ok_or(HostContractError::TooManyBytes)?;
        for count in [
            4,
            operation.module.len(),
            4,
            operation.name.len(),
            1,
            12,
            signature_bytes,
        ] {
            bytes = bytes
                .checked_add(count)
                .ok_or(HostContractError::TooManyBytes)?;
        }
        for access in &operation.domains {
            bytes = bytes
                .checked_add(4 + access.domain.len() + 1)
                .ok_or(HostContractError::TooManyBytes)?;
        }
    }
    if items > MAX_HOST_PROFILE_ITEMS {
        return Err(HostContractError::TooManyItems);
    }
    if bytes > MAX_HOST_PROFILE_BYTES {
        return Err(HostContractError::TooManyBytes);
    }
    Ok(())
}

fn encode_profile(
    identity: &str,
    revision: u64,
    domains: &[HostDomain],
    operations: &[HostOperationContract],
) -> Vec<u8> {
    // Sizes have been checked against ceilings below u32::MAX. All integers
    // have fixed widths; strings/lists have explicit lengths, no delimiters.
    fn count(bytes: &mut Vec<u8>, value: usize) {
        bytes.extend_from_slice(&(value as u32).to_le_bytes());
    }
    fn name(bytes: &mut Vec<u8>, value: &str) {
        count(bytes, value.len());
        bytes.extend_from_slice(value.as_bytes());
    }
    let mut bytes = PROFILE_MAGIC.to_vec();
    bytes.extend_from_slice(&HOST_PROFILE_VERSION.to_le_bytes());
    name(&mut bytes, identity);
    bytes.extend_from_slice(&revision.to_le_bytes());
    count(&mut bytes, domains.len());
    for domain in domains {
        name(&mut bytes, &domain.name);
        bytes.extend_from_slice(&[domain.kind as u8, domain.scope as u8, domain.label as u8]);
    }
    count(&mut bytes, operations.len());
    for operation in operations {
        name(&mut bytes, &operation.module);
        name(&mut bytes, &operation.name);
        bytes.push(operation.occurrence as u8);
        for values in [&operation.params, &operation.results] {
            count(&mut bytes, values.len());
            for value in values {
                bytes.extend_from_slice(&[value.ty as u8, value.label as u8]);
            }
        }
        count(&mut bytes, operation.domains.len());
        for access in &operation.domains {
            name(&mut bytes, &access.domain);
            bytes.push(access.mode as u8);
        }
    }
    bytes
}
