//! Canonical occurrence-declaration envelope consumed by the production CSIR v9 checker.
//!
//! This codec retains the exact v8 record prefix and appends declarations, not
//! computed taints or security verdicts. Decoding checks framing and complete
//! boundary bindings, NOT program safety, host conformance, or relational policy.
//! No method in this codec constructs a `Compilation` or `FormalSecurityReport`.
//! Authorization is performed separately by the linked v9 verifier, which also
//! re-runs the retained v8 gate over the exact embedded prefix.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use sigil_abi::host_contract::{HostContractProfile, HostValueType, SecurityLabel};

pub const MODEL_VERSION: u32 = 9;
pub const MAX_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_RECORDS: usize = 1_000_000;
const HEADER: usize = 12;
const RECORD: usize = 32;
const CHUNK: usize = 20;
const MANIFEST: u8 = 44;
const BYTES: u8 = 45;
const FFI: u8 = 46;
const ACTOR: u8 = 47;
const ROOT: u8 = 48;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationError {
    Bounds,
    Framing,
    NonCanonical,
    Profile,
    ForeignBinding,
    ActorBinding,
    RootContract,
}

impl fmt::Display for DeclarationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid occurrence declaration envelope: {self:?}")
    }
}

impl std::error::Error for DeclarationError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiBinding {
    pub owner: u32,
    /// One-based index in the complete canonical profile. Zero means legacy
    /// UNKNOWN, is legal only without a profile, and never means private.
    pub profile_operation: u32,
    pub first_argument: u32,
    pub parameter_count: u32,
    pub result_count: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForeignIdentity {
    pub name: String,
    pub params: Vec<HostValueType>,
    pub results: Vec<HostValueType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActorBinding {
    pub owner: u32,
    /// Send, ask, spawn, serialize, deserialize respectively. Local codecs are
    /// distinct from external crossings even when their operands have equal arity.
    pub subtype: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionRootContract {
    pub function_id: u32,
    /// Internal, module initializer/function, actor initializer/handler (0..4).
    pub role: u8,
    pub actor_type: u32,
    pub handler_id: u32,
    pub export_name: String,
    pub is_entry: bool,
    pub entry_occurrence: SecurityLabel,
    pub return_occurrence: SecurityLabel,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declarations {
    /// Explicitly retained version; this is not the version-erasing v8 Program.
    pub model_version: u32,
    pub legacy_v8: Vec<u8>,
    pub host_profile: Option<HostContractProfile>,
    pub ffi_bindings: Vec<FfiBinding>,
    /// Derived from the exact legacy operand slices, never supplied by a caller.
    pub foreign_identities: Vec<ForeignIdentity>,
    pub actor_bindings: Vec<ActorBinding>,
    pub roots: Vec<FunctionRootContract>,
    /// Stable root boundary sites, aligned with `roots` and taken from the
    /// canonical record IDs, not inferred from a returned payload's label.
    pub root_sites: Vec<u32>,
}

fn word(bytes: &[u8], start: usize) -> Result<u32, DeclarationError> {
    let value = bytes
        .get(start..start.checked_add(4).ok_or(DeclarationError::Bounds)?)
        .ok_or(DeclarationError::Framing)?;
    Ok(u32::from_le_bytes(
        value.try_into().map_err(|_| DeclarationError::Framing)?,
    ))
}

fn framed_records(bytes: &[u8], version: u32) -> Result<&[u8], DeclarationError> {
    if bytes.len() > MAX_BYTES || bytes.len() < HEADER {
        return Err(DeclarationError::Bounds);
    }
    let count = word(bytes, 8)? as usize;
    if bytes.get(..4) != Some(b"CSIR") || word(bytes, 4)? != version {
        return Err(DeclarationError::Framing);
    }
    if count > MAX_RECORDS || bytes.len() != HEADER + count * RECORD {
        return Err(DeclarationError::Bounds);
    }
    for (index, record) in bytes[HEADER..].as_chunks::<RECORD>().0.iter().enumerate() {
        if word(record, 24)? as usize != index + 1 || word(record, 28)? != 0 {
            return Err(DeclarationError::NonCanonical);
        }
    }
    Ok(&bytes[HEADER..])
}

fn legacy_records(bytes: &[u8]) -> Result<&[u8], DeclarationError> {
    let records = framed_records(bytes, 8)?;
    if records
        .as_chunks::<RECORD>()
        .0
        .iter()
        .any(|record| record[0] > 43 || record[1] > 3 || record[2] > 3)
    {
        return Err(DeclarationError::NonCanonical);
    }
    Ok(records)
}

fn label(value: u8) -> Result<SecurityLabel, DeclarationError> {
    match value {
        0 => Ok(SecurityLabel::Public),
        1 => Ok(SecurityLabel::Internal),
        2 => Ok(SecurityLabel::Secret),
        // Invocation and return are variable-time boundaries, never CT events.
        _ => Err(DeclarationError::RootContract),
    }
}

struct Reader<'a> {
    records: &'a [u8],
    position: usize,
}

impl<'a> Reader<'a> {
    fn record(&mut self, tag: u8, plain: bool) -> Result<&'a [u8], DeclarationError> {
        let start = self.position * RECORD;
        let record = self
            .records
            .get(start..start + RECORD)
            .ok_or(DeclarationError::Framing)?;
        if record[0] != tag || (plain && record[1..4] != [0, 0, 0]) {
            return Err(DeclarationError::NonCanonical);
        }
        self.position += 1;
        Ok(record)
    }

    fn bytes(&mut self, count: usize) -> Result<Vec<u8>, DeclarationError> {
        let chunks = count.div_ceil(CHUNK);
        if chunks > self.records.len() / RECORD - self.position {
            return Err(DeclarationError::Bounds);
        }
        let mut result = Vec::with_capacity(count);
        for index in 0..chunks {
            let record = self.record(BYTES, true)?;
            let size = (count - index * CHUNK).min(CHUNK);
            result.extend_from_slice(&record[4..4 + size]);
            if record[4 + size..24].iter().any(|byte| *byte != 0) {
                return Err(DeclarationError::NonCanonical);
            }
        }
        Ok(result)
    }
}

/// Decode bounded canonical declarations. A successful result says nothing
/// about the retained program's CFG, taint judgment, or executable authorization.
pub fn decode(bytes: &[u8]) -> Result<Declarations, DeclarationError> {
    let records = framed_records(bytes, MODEL_VERSION)?;
    let base_count = records
        .as_chunks::<RECORD>()
        .0
        .iter()
        .position(|record| record[0] > 43)
        .ok_or(DeclarationError::Framing)?;
    let mut reader = Reader {
        records,
        position: base_count,
    };
    let manifest = reader.record(MANIFEST, true)?;
    if word(manifest, 4)? as usize != base_count {
        return Err(DeclarationError::NonCanonical);
    }
    let counts = [
        word(manifest, 12)?,
        word(manifest, 16)?,
        word(manifest, 20)?,
    ];
    if counts.iter().any(|count| *count as usize > MAX_RECORDS)
        || counts.iter().map(|count| u64::from(*count)).sum::<u64>() > MAX_RECORDS as u64
    {
        return Err(DeclarationError::Bounds);
    }
    let profile_bytes = reader.bytes(word(manifest, 8)? as usize)?;
    let host_profile = if profile_bytes.is_empty() {
        None
    } else {
        Some(HostContractProfile::decode(&profile_bytes).map_err(|_| DeclarationError::Profile)?)
    };
    let mut ffi_bindings = Vec::new();
    for _ in 0..counts[0] {
        let record = reader.record(FFI, true)?;
        ffi_bindings.push(FfiBinding {
            owner: word(record, 4)?,
            profile_operation: word(record, 8)?,
            first_argument: word(record, 12)?,
            parameter_count: word(record, 16)?,
            result_count: word(record, 20)?,
        });
    }
    let mut actor_bindings = Vec::new();
    for _ in 0..counts[1] {
        let record = reader.record(ACTOR, true)?;
        if record[12..24].iter().any(|byte| *byte != 0) {
            return Err(DeclarationError::NonCanonical);
        }
        actor_bindings.push(ActorBinding {
            owner: word(record, 4)?,
            subtype: word(record, 8)?,
        });
    }
    let mut roots = Vec::new();
    let mut root_sites = Vec::new();
    for _ in 0..counts[2] {
        let record = reader.record(ROOT, false)?;
        root_sites.push(word(record, 24)?);
        if word(record, 20)? > 1 {
            return Err(DeclarationError::RootContract);
        }
        let export_name = String::from_utf8(reader.bytes(word(record, 16)? as usize)?)
            .map_err(|_| DeclarationError::RootContract)?;
        roots.push(FunctionRootContract {
            function_id: word(record, 4)?,
            role: record[3],
            actor_type: word(record, 8)?,
            handler_id: word(record, 12)?,
            export_name,
            is_entry: word(record, 20)? == 1,
            entry_occurrence: label(record[1])?,
            return_occurrence: label(record[2])?,
        });
    }
    if reader.position != records.len() / RECORD {
        return Err(DeclarationError::NonCanonical);
    }
    let mut legacy_v8 = Vec::with_capacity(HEADER + base_count * RECORD);
    legacy_v8.extend_from_slice(b"CSIR\x08\0\0\0");
    legacy_v8.extend_from_slice(&(base_count as u32).to_le_bytes());
    legacy_v8.extend_from_slice(&records[..base_count * RECORD]);
    legacy_records(&legacy_v8)?;
    let foreign_identities = validate_bindings(
        &legacy_v8,
        host_profile.as_ref(),
        &ffi_bindings,
        &actor_bindings,
        &roots,
    )?;
    Ok(Declarations {
        model_version: MODEL_VERSION,
        legacy_v8,
        host_profile,
        ffi_bindings,
        foreign_identities,
        actor_bindings,
        roots,
        root_sites,
    })
}

fn abi_type(code: u32) -> Result<HostValueType, DeclarationError> {
    match code {
        0..=3 | 7 => Ok(HostValueType::I32),
        4 | 5 => Ok(HostValueType::I64),
        6 => Ok(HostValueType::F64),
        _ => Err(DeclarationError::ForeignBinding),
    }
}

fn foreign_identity(
    records: &[u8],
    instruction: &[u8],
    binding: &FfiBinding,
    values: &BTreeMap<(u32, u32), HostValueType>,
) -> Result<ForeignIdentity, DeclarationError> {
    let owner = binding.owner;
    let function_id = word(instruction, 4)?;
    let count = word(instruction, 16)? as usize;
    let start = owner as usize * RECORD;
    let end = start
        .checked_add(count.checked_mul(RECORD).ok_or(DeclarationError::Bounds)?)
        .ok_or(DeclarationError::Bounds)?;
    let operands = records
        .get(start..end)
        .ok_or(DeclarationError::ForeignBinding)?;
    for (position, operand) in operands.as_chunks::<RECORD>().0.iter().enumerate() {
        if operand[0] != 38 || word(operand, 4)? != owner || word(operand, 8)? as usize != position
        {
            return Err(DeclarationError::ForeignBinding);
        }
    }
    let immediate = |position: usize| -> Result<u64, DeclarationError> {
        let operand = operands
            .get(position * RECORD..(position + 1) * RECORD)
            .ok_or(DeclarationError::ForeignBinding)?;
        if operand[3] != 3 {
            return Err(DeclarationError::ForeignBinding);
        }
        Ok(u64::from(word(operand, 12)?) | (u64::from(word(operand, 16)?) << 32))
    };
    if immediate(0)? != 3 {
        return Err(DeclarationError::ForeignBinding);
    }
    let name_len = usize::try_from(immediate(1)?).map_err(|_| DeclarationError::Bounds)?;
    if name_len == 0 || name_len > sigil_abi::host_contract::MAX_HOST_NAME_BYTES {
        return Err(DeclarationError::ForeignBinding);
    }
    let first_argument = 2 + name_len.div_ceil(8);
    if binding.first_argument as usize != first_argument
        || first_argument.checked_add(binding.parameter_count as usize) != Some(count)
    {
        return Err(DeclarationError::ForeignBinding);
    }
    let mut name_bytes = Vec::with_capacity(name_len);
    for index in 0..name_len.div_ceil(8) {
        let packed = immediate(index + 2)?.to_le_bytes();
        let size = (name_len - index * 8).min(8);
        name_bytes.extend_from_slice(&packed[..size]);
        if packed[size..].iter().any(|byte| *byte != 0) {
            return Err(DeclarationError::NonCanonical);
        }
    }
    if !(name_bytes[0].is_ascii_alphabetic() || name_bytes[0] == b'_')
        || name_bytes
            .iter()
            .any(|byte| !(byte.is_ascii_alphanumeric() || *byte == b'_'))
    {
        return Err(DeclarationError::ForeignBinding);
    }
    let name = String::from_utf8(name_bytes).map_err(|_| DeclarationError::ForeignBinding)?;
    let mut params = Vec::new();
    for operand in operands[first_argument * RECORD..].as_chunks::<RECORD>().0 {
        if operand[3] != 0 {
            return Err(DeclarationError::ForeignBinding);
        }
        params.push(
            *values
                .get(&(function_id, word(operand, 12)?))
                .ok_or(DeclarationError::ForeignBinding)?,
        );
    }
    let destination = word(instruction, 12)?;
    let results = if destination == 0 {
        vec![]
    } else {
        vec![
            *values
                .get(&(function_id, destination))
                .ok_or(DeclarationError::ForeignBinding)?,
        ]
    };
    if binding.result_count as usize != results.len() {
        return Err(DeclarationError::ForeignBinding);
    }
    Ok(ForeignIdentity {
        name,
        params,
        results,
    })
}

fn validate_bindings(
    base: &[u8],
    profile: Option<&HostContractProfile>,
    ffi: &[FfiBinding],
    actors: &[ActorBinding],
    roots: &[FunctionRootContract],
) -> Result<Vec<ForeignIdentity>, DeclarationError> {
    let records = legacy_records(base)?;
    let mut functions = BTreeMap::new();
    let mut values = BTreeMap::new();
    let mut foreign_owners = Vec::new();
    let mut actor_owners = Vec::new();
    for record in records.as_chunks::<RECORD>().0 {
        match record[0] {
            34 => {
                if word(record, 4)? as usize != functions.len() + 1
                    || record[3] > 4
                    || functions.insert(word(record, 4)?, record[3]).is_some()
                {
                    return Err(DeclarationError::RootContract);
                }
            }
            35 => {
                if word(record, 8)? == 0
                    || values
                        .insert(
                            (word(record, 4)?, word(record, 8)?),
                            abi_type(word(record, 12)?)?,
                        )
                        .is_some()
                {
                    return Err(DeclarationError::ForeignBinding);
                }
            }
            37 => match word(record, 20)? {
                15 => foreign_owners.push(word(record, 24)?),
                8 => actor_owners.push(word(record, 24)?),
                _ => {}
            },
            _ => {}
        }
    }
    if values
        .keys()
        .any(|(function_id, _)| !functions.contains_key(function_id))
    {
        return Err(DeclarationError::ForeignBinding);
    }
    for owner in foreign_owners.iter().chain(actor_owners.iter()) {
        let start = (*owner as usize - 1) * RECORD;
        if !functions.contains_key(&word(records, start + 4)?) {
            return Err(DeclarationError::NonCanonical);
        }
    }
    if ffi.iter().map(|binding| binding.owner).ne(foreign_owners)
        || actors.iter().map(|binding| binding.owner).ne(actor_owners)
        || roots
            .iter()
            .map(|root| root.function_id)
            .ne(functions.keys().copied())
    {
        return Err(DeclarationError::NonCanonical);
    }
    let mut identities = Vec::with_capacity(ffi.len());
    for binding in ffi {
        let start = (binding.owner as usize - 1) * RECORD;
        let identity =
            foreign_identity(records, &records[start..start + RECORD], binding, &values)?;
        match profile {
            None if binding.profile_operation == 0 => {}
            Some(profile) => {
                let operation = binding
                    .profile_operation
                    .checked_sub(1)
                    .and_then(|position| profile.operations().get(position as usize))
                    .ok_or(DeclarationError::ForeignBinding)?;
                if operation.module != "ffi" || operation.name != identity.name {
                    return Err(DeclarationError::ForeignBinding);
                }
                profile
                    .resolve("ffi", &identity.name, &identity.params, &identity.results)
                    .map_err(|_| DeclarationError::ForeignBinding)?;
            }
            None => return Err(DeclarationError::ForeignBinding),
        }
        identities.push(identity);
    }
    if actors
        .iter()
        .any(|binding| !(1..=5).contains(&binding.subtype))
    {
        return Err(DeclarationError::ActorBinding);
    }
    let mut export_names = BTreeSet::new();
    for root in roots {
        if root.export_name.is_empty()
            || root.role > 4
            || root.entry_occurrence == SecurityLabel::SecretCt
            || root.return_occurrence == SecurityLabel::SecretCt
        {
            return Err(DeclarationError::RootContract);
        }
        let kind = functions[&root.function_id];
        if root.role == 0 {
            if !(kind == 1 || kind == 4 || root.export_name.starts_with('$'))
                || root.actor_type != 0
                || root.handler_id != 0
                || root.is_entry
                || root.entry_occurrence != SecurityLabel::Public
                || root.return_occurrence != SecurityLabel::Public
            {
                return Err(DeclarationError::RootContract);
            }
        } else if kind > 3
            || root.role != kind + 1
            || root.export_name.starts_with('$')
            || !export_names.insert(&root.export_name)
        {
            return Err(DeclarationError::RootContract);
        }
        if (root.role == 1 || root.role == 2)
            && (root.actor_type != 0 || root.handler_id != 0 || root.is_entry)
            || root.role == 3 && root.handler_id != 0
        {
            return Err(DeclarationError::RootContract);
        }
    }
    Ok(identities)
}

struct Writer {
    records: Vec<u8>,
}

impl Writer {
    fn record(
        &mut self,
        tag: u8,
        labels: [u8; 3],
        payload: &[u8; CHUNK],
    ) -> Result<(), DeclarationError> {
        let id = self.records.len() / RECORD + 1;
        if id > MAX_RECORDS || HEADER + id * RECORD > MAX_BYTES {
            return Err(DeclarationError::Bounds);
        }
        self.records
            .extend_from_slice(&[tag, labels[0], labels[1], labels[2]]);
        self.records.extend_from_slice(payload);
        self.records.extend_from_slice(&(id as u32).to_le_bytes());
        self.records.extend_from_slice(&0_u32.to_le_bytes());
        Ok(())
    }

    fn fields(
        &mut self,
        tag: u8,
        labels: [u8; 3],
        fields: [u32; 5],
    ) -> Result<(), DeclarationError> {
        let mut payload = [0; CHUNK];
        for (slot, value) in payload.as_chunks_mut::<4>().0.iter_mut().zip(fields) {
            slot.copy_from_slice(&value.to_le_bytes());
        }
        self.record(tag, labels, &payload)
    }

    fn bytes(&mut self, bytes: &[u8]) -> Result<(), DeclarationError> {
        for chunk in bytes.chunks(CHUNK) {
            let mut payload = [0; CHUNK];
            payload[..chunk.len()].copy_from_slice(chunk);
            self.record(BYTES, [0; 3], &payload)?;
        }
        Ok(())
    }
}

/// Encode and independently validate declared bindings. Caller-supplied order
/// is checked, not sorted into a different certificate identity. There is no
/// default private contract and no acceptance/report path in this codec.
pub fn encode(
    legacy_v8: &[u8],
    host_profile: Option<&HostContractProfile>,
    ffi_bindings: &[FfiBinding],
    actor_bindings: &[ActorBinding],
    roots: &[FunctionRootContract],
) -> Result<Vec<u8>, DeclarationError> {
    let records = legacy_records(legacy_v8)?;
    validate_bindings(legacy_v8, host_profile, ffi_bindings, actor_bindings, roots)?;
    let profile = host_profile
        .map(HostContractProfile::canonical_bytes)
        .unwrap_or_default();
    let length = |n| u32::try_from(n).map_err(|_| DeclarationError::Bounds);
    let mut writer = Writer {
        records: records.to_vec(),
    };
    writer.fields(
        MANIFEST,
        [0; 3],
        [
            length(records.len() / RECORD)?,
            length(profile.len())?,
            length(ffi_bindings.len())?,
            length(actor_bindings.len())?,
            length(roots.len())?,
        ],
    )?;
    writer.bytes(profile)?;
    for binding in ffi_bindings {
        writer.fields(
            FFI,
            [0; 3],
            [
                binding.owner,
                binding.profile_operation,
                binding.first_argument,
                binding.parameter_count,
                binding.result_count,
            ],
        )?;
    }
    for binding in actor_bindings {
        writer.fields(ACTOR, [0; 3], [binding.owner, binding.subtype, 0, 0, 0])?;
    }
    for root in roots {
        writer.fields(
            ROOT,
            [
                root.entry_occurrence as u8,
                root.return_occurrence as u8,
                root.role,
            ],
            [
                root.function_id,
                root.actor_type,
                root.handler_id,
                length(root.export_name.len())?,
                u32::from(root.is_entry),
            ],
        )?;
        writer.bytes(root.export_name.as_bytes())?;
    }
    let mut bytes = Vec::with_capacity(HEADER + writer.records.len());
    bytes.extend_from_slice(b"CSIR");
    bytes.extend_from_slice(&MODEL_VERSION.to_le_bytes());
    bytes.extend_from_slice(&length(writer.records.len() / RECORD)?.to_le_bytes());
    bytes.extend_from_slice(&writer.records);
    Ok(bytes)
}
