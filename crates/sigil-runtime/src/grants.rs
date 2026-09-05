//! I/O grants for ephemeral tool execution.
//!
//! Grants are capability-based permissions that control what I/O operations
//! a tool may perform during ephemeral execution (network, filesystem,
//! wall clock, secure entropy).
//!
//! Per Phase 5a-1.5 / I26: each grant category is capped at
//! `MAX_GRANTS_PER_CATEGORY` entries to bound the cost of per-call grant
//! checks (linear scan today). Tools requiring more grants must be
//! decomposed.

use std::path::{Path, PathBuf};

/// Hard cap on entries per grant category. Per I26 / AP22 — adversarial
/// task specs that would degrade per-call FFI latency to O(N) on a giant
/// grant list are rejected.
pub const MAX_GRANTS_PER_CATEGORY: usize = 256;

/// HTTP methods that may be granted for network access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
}

/// A network grant allowing HTTP requests to hosts matching a pattern.
#[derive(Debug, Clone)]
pub struct NetGrant {
    /// Host pattern, e.g. `"*.example.com"` or `"api.example.com"`.
    pub host_pattern: String,
    /// Allowed HTTP methods.
    pub methods: Vec<HttpMethod>,
}

/// A filesystem grant allowing read access to paths under a directory.
/// Phase 5a-2: write access uses a separate grant type so granters can
/// scope read vs write independently. A tool with `FsGrant { ... }` for
/// `/data` can read but not write; an additional `FsWriteGrant { ... }`
/// for the same root is required to enable writes.
#[derive(Debug, Clone)]
pub struct FsGrant {
    /// The canonical root directory that read access is granted to.
    pub root: PathBuf,
}

/// A filesystem grant allowing write access to paths under a directory.
/// Separate from `FsGrant` (read) so granters can scope independently.
#[derive(Debug, Clone)]
pub struct FsWriteGrant {
    /// The canonical root directory that write access is granted to.
    pub root: PathBuf,
}

/// A key-value READ grant: authority to `kv_get` from `namespace`.
/// The namespace is an OPAQUE label matched by exact string compare —
/// it never touches the filesystem. `root` is the embedder-chosen
/// directory the host serves the namespace's bytes from; guest keys
/// are mapped to files by content hash, so key bytes never influence
/// path resolution either.
#[derive(Debug, Clone)]
pub struct KvGrant {
    /// Opaque namespace label the guest names in `kv_get` calls.
    pub namespace: String,
    /// Host directory backing this namespace (must exist).
    pub root: PathBuf,
}

/// A key-value WRITE grant: authority to `kv_put` / `kv_delete` in
/// `namespace`. Separate from `KvGrant` (read) so granters can scope
/// independently — mirrors the `FsGrant` / `FsWriteGrant` split.
#[derive(Debug, Clone)]
pub struct KvWriteGrant {
    /// Opaque namespace label the guest names in `kv_put`/`kv_delete`.
    pub namespace: String,
    /// Host directory backing this namespace (must exist).
    pub root: PathBuf,
}

/// Time grant — kinds of clock access a tool may perform.
///
/// Phase 5a-2 / I18: `Wall` is non-monotonic — wall-clock time can move
/// backwards under NTP correction or manual change. Stdlib must not
/// assume monotonicity. A separate `Monotonic` variant is reserved for
/// future expansion.
///
/// Slot-registry addendum (2026-05-19): `Frozen(ms)` returns the given
/// epoch-millisecond value verbatim from `time_now()`. Used by the slot
/// registry to make `Clock`-using slots deterministic across attest
/// runs. `Frozen` does NOT imply `Wall` access; the two variants are
/// independent grant axes. If both are present, `Frozen` wins (the shim
/// checks `frozen_time()` first).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeGrant {
    /// Read the wall clock (Unix epoch milliseconds).
    Wall,
    /// Return this exact ms value from `time_now()`. Deterministic.
    Frozen(i64),
}

/// Random grant — kinds of entropy a tool may consume.
///
/// `Secure` uses the host `getrandom` (cryptographic strength,
/// nondeterministic by design).
///
/// `Seeded(u64)` PINS the algorithm — Marsaglia xorshift64* with
/// multiplier `0x2545F4914F6CDD1D`. State lives on `EphemeralData`
/// (per-execution); initialized from the seed on every
/// `execute_ephemeral` entry. Once a sidecar attestation records a
/// `random_seed_u64`, this byte mapping MUST hold forever — changing
/// the algorithm or constants requires a NEW grant variant
/// (e.g. `Seeded2`), not a redefinition of `Seeded`.
///
/// Seed = 0 is REJECTED at `IoGrants::validate()` time because
/// xorshift on state 0 produces 0 forever.
///
/// Golden vector for seed = 1, first 16 output bytes (little-endian
/// per u64 produced):
///   `5d c4 01 4f 62 cf fa ba  5d 68 07 e5 91 68 da 02`
/// First u64 output = `0xBAFACF624F01C45D`
/// Second u64 output = `0x02DA6891E507685D`
/// Hardcoded as a golden vector in `tests/ffi_shims.rs`. Any change
/// requires a new `Seeded2` variant — `Seeded(u64)`'s byte mapping is
/// frozen.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RandomGrant {
    /// Cryptographically secure random bytes (`getrandom`).
    Secure,
    /// Deterministic xorshift64*-seeded entropy. State per-execution.
    Seeded(u64),
}

/// A secret grant: a named secret whose VALUE the host holds and the
/// guest never receives. Used by the `http_post_secret` shim, which
/// substitutes `{{secret:NAME}}` placeholders in an outbound header blob
/// host-side. The guest names the secret; only the host ever sees its
/// bytes — so a secret can't be laundered out of guest memory (there are
/// no secret bytes in guest memory to launder). Empty `secret` list =
/// fail-closed: every placeholder is denied.
#[derive(Clone)]
pub struct SecretGrant {
    /// Name the guest references as `{{secret:NAME}}`.
    pub name: String,
    /// The secret bytes. Host-held; never crosses into guest memory.
    pub value: Vec<u8>,
}

// Custom Debug: never print the secret value (it lands in logs/panics).
impl std::fmt::Debug for SecretGrant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SecretGrant")
            .field("name", &self.name)
            .field(
                "value",
                &format_args!("<{} redacted bytes>", self.value.len()),
            )
            .finish()
    }
}

/// Z3 solver grant — authority to invoke the SMT solver via the
/// `z3_check` host shim (the self-hosting `Cap<Z3>` boundary). A single
/// unit capability: holding any `Z3Grant::Solve` permits solver calls;
/// an empty `IoGrants.z3` fails closed — the shim returns the
/// grant-denied code WITHOUT constructing a solver or parsing the query.
///
/// Unlike `RandomGrant`/`TimeGrant`, the solver verdict (sat/unsat) is
/// deterministic under a pinned rlimit, so Z3-using tools may use
/// `expected_output_strategy: capture_from_reference`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Z3Grant {
    /// Permit SMT-LIB2 queries through `z3::check` / the `z3_check` shim.
    Solve,
}

/// The set of I/O grants for an ephemeral tool execution.
///
/// Phase 5a-2: gains `fs_write`, `time`, `random` categories. Time and
/// random are both grant-gated (vs ambient access in many languages) so
/// non-deterministic surface is auditable per task.
#[derive(Debug, Clone, Default)]
pub struct IoGrants {
    pub net: Vec<NetGrant>,
    pub fs: Vec<FsGrant>,
    pub fs_write: Vec<FsWriteGrant>,
    /// Key-value read grants. Empty = fail-closed: no `kv_get`.
    pub kv: Vec<KvGrant>,
    /// Key-value write grants. Empty = fail-closed: no `kv_put` /
    /// `kv_delete`.
    pub kv_write: Vec<KvWriteGrant>,
    pub time: Vec<TimeGrant>,
    pub random: Vec<RandomGrant>,
    /// Z3 solver capability. Empty (the `Default`) = fail-closed: no
    /// solver access. Any `Z3Grant::Solve` permits `z3_check` calls.
    pub z3: Vec<Z3Grant>,
    /// Named secrets the host holds. Gate `http_post_secret` placeholder
    /// substitution. Empty = fail-closed: every `{{secret:NAME}}` denied.
    pub secret: Vec<SecretGrant>,
}

/// Validation error from `IoGrants::validate()`. Carries the offending
/// category name and observed length so the MCP envelope can produce a
/// clean R808 diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrantValidationError {
    pub category: &'static str,
    pub len: usize,
    pub max: usize,
}

impl std::fmt::Display for GrantValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "grant category `{}` has {} entries; maximum is {}",
            self.category, self.len, self.max
        )
    }
}

impl std::error::Error for GrantValidationError {}

impl IoGrants {
    /// No grants — fully sandboxed.
    pub fn none() -> Self {
        Self::default()
    }

    /// Phase 5a-2 / I26: each grant category is capped. Reject grant
    /// sets that exceed the cap before any FFI shim runs (cap exists to
    /// bound per-call linear-scan cost; without it, an adversarial task
    /// spec could degrade FFI latency to O(N) on a giant grant list).
    ///
    /// Slot-registry addendum (2026-05-19): also rejects
    /// `RandomGrant::Seeded(0)` — xorshift on state 0 produces 0
    /// forever, so a zero seed is a quiet way to break determinism.
    pub fn validate(&self) -> Result<(), GrantValidationError> {
        for (category, len) in [
            ("net", self.net.len()),
            ("fs", self.fs.len()),
            ("fs_write", self.fs_write.len()),
            ("kv", self.kv.len()),
            ("kv_write", self.kv_write.len()),
            ("time", self.time.len()),
            ("random", self.random.len()),
            ("z3", self.z3.len()),
            ("secret", self.secret.len()),
        ] {
            if len > MAX_GRANTS_PER_CATEGORY {
                return Err(GrantValidationError {
                    category,
                    len,
                    max: MAX_GRANTS_PER_CATEGORY,
                });
            }
        }
        // Reject Seeded(0): xorshift weakness.
        if self
            .random
            .iter()
            .any(|g| matches!(g, RandomGrant::Seeded(0)))
        {
            return Err(GrantValidationError {
                category: "random_seeded_zero",
                len: 0,
                max: 0,
            });
        }
        Ok(())
    }

    /// Check whether reading the given canonical path is allowed by any `FsGrant`.
    pub fn fs_read_allowed(&self, path: &Path) -> bool {
        self.fs.iter().any(|grant| path.starts_with(&grant.root))
    }

    /// Check whether writing to the given canonical path is allowed by any
    /// `FsWriteGrant`. Phase 5a-2.
    pub fn fs_write_allowed(&self, path: &Path) -> bool {
        self.fs_write
            .iter()
            .any(|grant| path.starts_with(&grant.root))
    }

    /// Resolve the storage root for READING `namespace`, if granted.
    /// First matching grant wins; `None` = fail closed (the shim
    /// returns -403 without touching the filesystem).
    pub fn kv_read_root(&self, namespace: &str) -> Option<&Path> {
        self.kv
            .iter()
            .find(|g| g.namespace == namespace)
            .map(|g| g.root.as_path())
    }

    /// Resolve the storage root for WRITING `namespace`, if granted.
    /// Covers both `kv_put` and `kv_delete`.
    pub fn kv_write_root(&self, namespace: &str) -> Option<&Path> {
        self.kv_write
            .iter()
            .find(|g| g.namespace == namespace)
            .map(|g| g.root.as_path())
    }

    /// Check whether an HTTP request to the given host with the given method is
    /// allowed by any `NetGrant`.
    pub fn net_allowed(&self, host: &str, method: HttpMethod) -> bool {
        self.net.iter().any(|grant| {
            grant.methods.contains(&method) && pattern_matches(&grant.host_pattern, host)
        })
    }

    /// Phase 5a-2: check whether a `TimeGrant` of the requested kind is
    /// present. Today `Wall` and `Frozen(_)` exist; the kind argument is
    /// for forward compatibility with `Monotonic` etc.
    ///
    /// Note: equality on `TimeGrant::Frozen(_)` compares the inner ms
    /// value too. So `time_allowed(Frozen(1))` only returns true for an
    /// exact match. For "is *any* frozen grant present?" use
    /// `frozen_time().is_some()`.
    pub fn time_allowed(&self, kind: TimeGrant) -> bool {
        self.time.contains(&kind)
    }

    /// Phase 5a-2: check whether a `RandomGrant` of the requested kind is
    /// present.
    ///
    /// Note: same equality caveat as `time_allowed` — `Seeded(1)` and
    /// `Seeded(2)` are distinct. For "is any seeded grant present?" use
    /// `seeded_random().is_some()`.
    pub fn random_allowed(&self, kind: RandomGrant) -> bool {
        self.random.contains(&kind)
    }

    /// Slot-registry addendum: returns the frozen-clock value if any
    /// `TimeGrant::Frozen(_)` is present. Picks the first; multiple
    /// frozen grants are ill-defined and not expected.
    pub fn frozen_time(&self) -> Option<i64> {
        self.time.iter().find_map(|g| match g {
            TimeGrant::Frozen(ms) => Some(*ms),
            _ => None,
        })
    }

    /// Slot-registry addendum: returns the seed value if any
    /// `RandomGrant::Seeded(_)` is present.
    pub fn seeded_random(&self) -> Option<u64> {
        self.random.iter().find_map(|g| match g {
            RandomGrant::Seeded(s) => Some(*s),
            _ => None,
        })
    }

    /// Resolve a named secret's bytes, if granted. `None` = fail closed
    /// (the shim denies the placeholder without sending anything).
    pub fn secret_value(&self, name: &str) -> Option<&[u8]> {
        self.secret
            .iter()
            .find(|g| g.name == name)
            .map(|g| g.value.as_slice())
    }

    /// Whether any `Z3Grant` is present — i.e. authority to call the SMT
    /// solver. Empty `z3` ⇒ false ⇒ the `z3_check` shim fails closed
    /// (returns the grant-denied code before any solver work).
    pub fn z3_allowed(&self) -> bool {
        !self.z3.is_empty()
    }
}

/// Simple wildcard pattern matching for host grants.
///
/// Supports a leading `*` as a wildcard prefix (e.g. `"*.example.com"`
/// matches `"api.example.com"`). An exact string match is also accepted.
pub fn pattern_matches(pattern: &str, value: &str) -> bool {
    if let Some(suffix) = pattern.strip_prefix("*.") {
        // Wildcard: *.example.com matches sub.example.com and example.com
        value == suffix || value.ends_with(&format!(".{suffix}"))
    } else if pattern.starts_with('*') {
        // Bare wildcard "*" matches everything
        pattern == "*"
    } else {
        pattern == value
    }
}
