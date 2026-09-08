//! Deterministic, offline local-package compilation.
//!
//! This is deliberately a narrow `sigil-resolver-v1` seam. It consumes an
//! explicit package root, its checked-in lockfile, and only lockfile-named
//! workspace/vendored directories beneath that root. It performs no ambient
//! discovery, network access, download, or version substitution.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};

#[cfg(unix)]
use std::os::fd::OwnedFd;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::ast::{Item, Ring, TaintLabel, Visibility};
use crate::diagnostics::certificate::{COMPILER_VERSION, CertificateJson};
use crate::{
    Compilation, CompileError, CompileOptions, CompilerContext,
    compile_library_project_with_context, source::SourceFile,
};

pub const PACKAGE_PROTOCOL_VERSION: &str = "sigil-package-v1";
pub const RESOLVER_CONTRACT: &str = "sigil-resolver-v1";
pub const PACKAGE_CERTIFICATE_SCHEMA: &str = "2";
pub const PACKAGE_CERTIFICATE_EXTENSION: &str = "package-graph-v1";
pub const RUNTIME_VERSION: &str = "0.1.0";

const MANIFEST_FILE: &str = "sigil-package.json";
const LOCK_FILE: &str = "sigil-package.lock.json";
const MAX_JSON_BYTES: u64 = 1024 * 1024;
const MAX_SOURCE_BYTES: u64 = 1024 * 1024;
const MAX_PACKAGE_NODES: usize = 256;
const MAX_MANIFEST_DEPENDENCIES: usize = 256;
const MAX_GRAPH_EDGES: usize = 4096;
const MAX_PACKAGE_SOURCES: usize = 256;
const MAX_TOTAL_SOURCE_BYTES: usize = 16 * 1024 * 1024;
const MAX_DEPENDENCY_DEPTH: usize = 128;
const MAX_FEATURE_DEPTH: usize = 64;
const CONTENT_DOMAIN: &[u8] = b"SIGIL-PACKAGE-CONTENT\0V1\0";
const GRAPH_DOMAIN: &[u8] = b"SIGIL-PACKAGE-GRAPH\0V1\0";
const SOURCE_SET_DOMAIN: &[u8] = b"SIGIL-PACKAGE-SOURCES\0V1\0";
const PUBLIC_API_DOMAIN: &[u8] = b"SIGIL-PACKAGE-PUBLIC-API\0V1\0";
const ARTIFACT_ID_DOMAIN: &[u8] = b"SIGIL-PACKAGE-ARTIFACT\0V1\0";
const COMPILER_ID_DOMAIN: &[u8] = b"SIGIL-COMPILER-IDENTITY\0V1\0";

/// Stable package-layer failure. Compiler diagnostics remain `CompileError`
/// and are not remapped into package codes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackageErrorOrigin {
    Candidate,
    Infrastructure,
}

/// Stable package-layer failure. Compiler diagnostics remain `CompileError`
/// and are not remapped into package codes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageError {
    pub code: &'static str,
    pub message: String,
    pub origin: PackageErrorOrigin,
}

impl PackageError {
    fn new(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            origin: PackageErrorOrigin::Candidate,
        }
    }

    fn infrastructure(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            origin: PackageErrorOrigin::Infrastructure,
        }
    }
}

impl fmt::Display for PackageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.message)
    }
}

impl std::error::Error for PackageError {}

#[derive(Debug)]
pub enum PackageCompileError {
    Package(PackageError),
    Compiler(CompileError),
}

impl fmt::Display for PackageCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Package(error) => error.fmt(f),
            Self::Compiler(error) => write!(f, "{error:?}"),
        }
    }
}

impl std::error::Error for PackageCompileError {}

impl From<PackageError> for PackageCompileError {
    fn from(value: PackageError) -> Self {
        Self::Package(value)
    }
}

impl From<CompileError> for PackageCompileError {
    fn from(value: CompileError) -> Self {
        Self::Compiler(value)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PackageCertificateJson {
    pub schema_version: String,
    pub extension: String,
    pub package_protocol: String,
    pub resolver_contract: String,
    #[serde(deserialize_with = "deserialize_strict_base_certificate")]
    pub base_certificate: CertificateJson,
    pub root_package: String,
    pub root_version: String,
    pub root_manifest_hash: String,
    pub lockfile_hash: String,
    pub package_graph_hash: String,
    pub composed_source_framing_hash: String,
    pub compiler_version: String,
    pub compiler_identity_hash: String,
    pub runtime_version: String,
    pub stdlib_hash: String,
    pub modules: Vec<String>,
    pub ambient_stdlib: AmbientStdlibCertificateJson,
    pub packages: Vec<PackageNodeCertificateJson>,
    pub graph_resource_evidence_hash: String,
    pub public_api: Vec<serde_json::Value>,
    pub public_api_hash: String,
    pub artifact_identity_hash: String,
    pub proof_tier: String,
    pub solver_verified: bool,
    pub authentication: PackageAuthenticationJson,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct AmbientStdlibCertificateJson {
    pub modules: Vec<String>,
    pub derived: PackageDerivedFactsJson,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PackageNodeCertificateJson {
    pub package: String,
    pub version: String,
    pub source: LockSource,
    pub manifest_hash: String,
    pub content_hash: String,
    pub features: Vec<String>,
    pub modules: Vec<String>,
    pub dependencies: Vec<String>,
    pub derived: PackageDerivedFactsJson,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PackageDerivedFactsJson {
    pub rings: Vec<String>,
    pub effects: Vec<String>,
    pub host_imports: Vec<String>,
    pub grant_categories: Vec<String>,
    pub taint_contracts: Vec<String>,
    pub taint_contract_hash: String,
    pub trusted_surface: Vec<String>,
    pub package_imports: Vec<String>,
    pub ambient_imports: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PackageAuthenticationJson {
    pub status: String,
    pub subject: Option<String>,
    pub envelope_ref: Option<String>,
}

fn deserialize_strict_base_certificate<'de, D>(deserializer: D) -> Result<CertificateJson, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de::Error as _;

    fn exact_keys(value: &serde_json::Value, expected: &[&str], label: &str) -> Result<(), String> {
        let object = value
            .as_object()
            .ok_or_else(|| format!("{label} must be an object"))?;
        let actual: BTreeSet<&str> = object.keys().map(String::as_str).collect();
        let expected: BTreeSet<&str> = expected.iter().copied().collect();
        if actual != expected {
            return Err(format!(
                "{label} fields must match exactly: expected={expected:?}, actual={actual:?}"
            ));
        }
        Ok(())
    }

    let value = serde_json::Value::deserialize(deserializer)?;
    exact_keys(
        &value,
        &[
            "schema_version",
            "compiler_version",
            "source_name",
            "source_fingerprint",
            "wasm_inner_fingerprint",
            "wasm_outer_fingerprint",
            "primary_module",
            "module_names",
            "capability",
            "ownership",
            "formal",
            "effects_required",
        ],
        "package base_certificate",
    )
    .map_err(D::Error::custom)?;
    let object = value.as_object().expect("validated object");
    for field in ["source_fingerprint", "wasm_inner_fingerprint"] {
        exact_keys(&object[field], &["algorithm", "bytes", "hash"], field)
            .map_err(D::Error::custom)?;
    }
    if !object["wasm_outer_fingerprint"].is_null() {
        exact_keys(
            &object["wasm_outer_fingerprint"],
            &["algorithm", "bytes", "hash"],
            "wasm_outer_fingerprint",
        )
        .map_err(D::Error::custom)?;
    }
    exact_keys(
        &object["capability"],
        &[
            "verified_functions",
            "checked_blocks",
            "checked_sites",
            "z3_rlimit_consumed",
            "z3_cache_hits",
            "z3_cache_misses",
            "solver_verified",
        ],
        "capability",
    )
    .map_err(D::Error::custom)?;
    exact_keys(
        &object["ownership"],
        &["verified_functions", "move_sites", "linear_values_checked"],
        "ownership",
    )
    .map_err(D::Error::custom)?;
    if !object["formal"].is_null() {
        exact_keys(
            &object["formal"],
            &[
                "model_version",
                "lean_toolchain",
                "checker_source_fingerprint",
                "csir_fingerprint",
                "checked_functions",
                "checked_nodes",
                "checked_capabilities",
                "checked_flows",
                "checked_releases",
                "checked_ct_operations",
            ],
            "formal",
        )
        .map_err(D::Error::custom)?;
    }
    serde_json::from_value(value).map_err(D::Error::custom)
}

#[derive(Debug)]
pub struct PackageCompilation {
    pub compilation: Compilation,
    pub graph: ResolvedPackageGraph,
}

impl PackageCompilation {
    /// Write a create-new evidence directory. A failed write leaves an incomplete
    /// directory that is never overwritten on retry. The manifest is written last;
    /// consumers must verify its identities, not infer completeness from existence.
    pub fn write_evidence_directory(&self, output: &Path) -> Result<(), PackageError> {
        let files = self.evidence_files()?;
        let inventory: BTreeMap<_, _> = files
            .iter()
            .map(|(name, bytes)| {
                (
                    name.clone(),
                    serde_json::json!({"sha256": prefixed_sha256(bytes), "bytes": bytes.len()}),
                )
            })
            .collect();
        let manifest = serde_json::to_vec(&serde_json::json!({
            "schema_version": "sigil-package-evidence-v1", "files": inventory,
            "proof_tier": "solver_verified", "admission": "not_evaluated"
        }))
        .map_err(|e| PackageError::infrastructure("E_EVIDENCE", e.to_string()))?;
        #[cfg(unix)]
        {
            use rustix::fs::{Mode, mkdirat};
            let parent = output
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."));
            let leaf = output.file_name().ok_or_else(|| {
                PackageError::infrastructure("E_EVIDENCE", "output must name a new directory")
            })?;
            let parent = PackageDirectory::open_root(parent)?;
            mkdirat(
                &parent.fd,
                Path::new(leaf),
                Mode::RUSR | Mode::WUSR | Mode::XUSR,
            )
            .map_err(|e| PackageError::infrastructure("E_EVIDENCE", e.to_string()))?;
            let directory = parent.open_directory(Path::new(leaf), "E_EVIDENCE")?;
            for (name, bytes) in &files {
                directory.create_regular_file(name, bytes, "E_EVIDENCE")?;
            }
            directory.create_regular_file("evidence-manifest.json", &manifest, "E_EVIDENCE")?;
            fs::File::from(directory.fd)
                .sync_all()
                .map_err(|e| PackageError::infrastructure("E_EVIDENCE", e.to_string()))?;
            Ok(())
        }
        #[cfg(not(unix))]
        {
            let _ = (output, files, manifest);
            Err(PackageError::infrastructure(
                "E_UNSUPPORTED_PLATFORM",
                "secure evidence output is unavailable",
            ))
        }
    }

    /// Exact compiler-owned digest preimages and artifacts from one compilation.
    /// This method supplies evidence, never admission or publisher authentication.
    /// Structural builds cannot materialize an accepting-shaped evidence bundle.
    pub fn evidence_files(&self) -> Result<BTreeMap<String, Vec<u8>>, PackageError> {
        self.require_solver_verified()?;
        let certificate = self.certificate();
        let mut files = BTreeMap::from([
            (
                "sigil-package.lock.json".to_owned(),
                self.graph.lockfile_bytes.clone(),
            ),
            (
                "source-set.preimage".to_owned(),
                package_source_set_preimage(&self.graph.sources),
            ),
            (
                "package-graph.preimage".to_owned(),
                self.graph.graph_preimage.clone(),
            ),
            (
                "public-api.preimage".to_owned(),
                package_public_api_preimage(&certificate.public_api).map_err(|error| {
                    PackageError::infrastructure("E_EVIDENCE", error.to_string())
                })?,
            ),
            (
                "compiler-artifact.preimage".to_owned(),
                package_artifact_preimage(
                    &self.graph,
                    &self.compilation,
                    &certificate.compiler_identity_hash,
                    &certificate.public_api_hash,
                ),
            ),
            (
                "certificate.json".to_owned(),
                serde_json::to_vec(&certificate).map_err(|error| {
                    PackageError::infrastructure("E_EVIDENCE", error.to_string())
                })?,
            ),
            ("inner.wasm".to_owned(), self.compilation.wasm_inner.clone()),
        ]);
        if let Some(outer) = &self.compilation.wasm_outer {
            files.insert("outer.wasm".to_owned(), outer.clone());
        }
        // This comparison also detects accidental divergence if a derivation
        // changes without updating the corresponding evidence producer.
        for (path, expected) in [
            ("sigil-package.lock.json", &certificate.lockfile_hash),
            (
                "source-set.preimage",
                &certificate.composed_source_framing_hash,
            ),
            ("package-graph.preimage", &certificate.package_graph_hash),
            ("public-api.preimage", &certificate.public_api_hash),
            (
                "compiler-artifact.preimage",
                &certificate.artifact_identity_hash,
            ),
        ] {
            if prefixed_sha256(&files[path]) != *expected {
                return Err(PackageError::infrastructure(
                    "E_EVIDENCE",
                    format!("{path} differs from certified identity"),
                ));
            }
        }
        Ok(files)
    }

    /// Require the proof tier used by package acceptance and release gates.
    /// Structural package compilation remains useful for diagnostics, but it
    /// must never be confused with a solver-backed verification result.
    pub fn require_solver_verified(&self) -> Result<(), PackageError> {
        if self.compilation.capability_report.solver_verified {
            Ok(())
        } else {
            Err(PackageError::new(
                "E_SOLVER_UNVERIFIED",
                "package compilation is structural-only; a solver-verified witness is required",
            ))
        }
    }

    /// Produce the deterministic package-aware wrapper. The legacy/base
    /// certificate stays at schema v9 and keeps its single-file behavior; only
    /// this explicit package path emits the wrapper.
    pub fn certificate(&self) -> PackageCertificateJson {
        let compiler_identity_hash = compiler_identity_hash();
        let public_api = package_public_api(&self.graph, &self.compilation);
        let public_api_hash =
            package_public_api_hash(&public_api).expect("package public API is serializable");
        let proof_tier = if self.compilation.capability_report.solver_verified {
            "solver_verified"
        } else {
            "structural_only"
        }
        .to_owned();
        let artifact_identity_hash = package_artifact_identity_hash(
            &self.graph,
            &self.compilation,
            &compiler_identity_hash,
            &public_api_hash,
        );
        let sources: Vec<(String, String)> = self
            .graph
            .sources
            .iter()
            .map(|source| (source.logical_name.clone(), source.text.clone()))
            .collect();
        let mut base = CertificateJson::new_for_sources(
            format!("<package:{}>", self.graph.root_package),
            &sources,
            &self.compilation.wasm_inner,
            self.compilation.wasm_outer.as_deref(),
            None,
            self.compilation.module_names.clone(),
            &self.compilation.capability_report,
            &self.compilation.ownership_report,
            &self.compilation.formal_security_report,
            self.compilation.effects_required.clone(),
        );
        // These counters are operational telemetry, not deterministic proof
        // facts. Existing certificate comparison already excludes them. The
        // package wrapper canonicalizes them so the promised bytes are stable.
        base.capability.z3_rlimit_consumed = None;
        base.capability.z3_cache_hits = 0;
        base.capability.z3_cache_misses = 0;

        PackageCertificateJson {
            schema_version: PACKAGE_CERTIFICATE_SCHEMA.to_owned(),
            extension: PACKAGE_CERTIFICATE_EXTENSION.to_owned(),
            package_protocol: PACKAGE_PROTOCOL_VERSION.to_owned(),
            resolver_contract: RESOLVER_CONTRACT.to_owned(),
            base_certificate: base,
            root_package: self.graph.root_package.clone(),
            root_version: self.graph.root_version.clone(),
            root_manifest_hash: self.graph.root_manifest_hash.clone(),
            lockfile_hash: self.graph.lockfile_hash.clone(),
            package_graph_hash: self.graph.graph_hash.clone(),
            composed_source_framing_hash: self.graph.source_framing_hash.clone(),
            compiler_version: COMPILER_VERSION.to_owned(),
            compiler_identity_hash,
            runtime_version: RUNTIME_VERSION.to_owned(),
            stdlib_hash: compiler_stdlib_hash(),
            modules: self.compilation.module_names.clone(),
            ambient_stdlib: self.graph.ambient_stdlib.clone(),
            packages: self.graph.certificate_nodes.clone(),
            graph_resource_evidence_hash: graph_resource_evidence_hash(
                &self.graph,
                &self.compilation,
            ),
            public_api,
            public_api_hash,
            artifact_identity_hash,
            proof_tier,
            solver_verified: self.compilation.capability_report.solver_verified,
            authentication: PackageAuthenticationJson {
                status: "unsigned_local".to_owned(),
                subject: None,
                envelope_ref: None,
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedPackageGraph {
    pub root_package: String,
    pub root_version: String,
    pub root_manifest_hash: String,
    pub lockfile_hash: String,
    pub graph_hash: String,
    pub source_framing_hash: String,
    pub sources: Vec<PackageSource>,
    pub certificate_nodes: Vec<PackageNodeCertificateJson>,
    lockfile_bytes: Vec<u8>,
    graph_preimage: Vec<u8>,
    ambient_stdlib: AmbientStdlibCertificateJson,
    claims: BTreeMap<String, ManifestDeclared>,
}

#[derive(Debug, Clone)]
pub struct PackageSource {
    pub package: String,
    pub module: String,
    pub logical_name: String,
    pub text: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    format_version: String,
    name: String,
    namespace: String,
    version: String,
    maturity: String,
    description: String,
    license: String,
    #[serde(default)]
    maintainers: Vec<String>,
    #[serde(default)]
    source: Option<String>,
    compiler: CompilerRequirement,
    modules: Vec<String>,
    dependencies: Vec<ManifestDependency>,
    features: ManifestFeatures,
    declared: ManifestDeclared,
    evidence: ManifestEvidence,
    #[serde(default)]
    deprecation: Option<ManifestDeprecation>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestEvidence {
    charter_hash: String,
    api_contract_hash: String,
    api_card_hash: String,
    evidence_manifest_hash: String,
    #[serde(default)]
    certificate_refs: Vec<String>,
    #[serde(default)]
    corpus_lineage: Vec<String>,
}

/// A non-optional wrapper makes the `replacement` key required while still
/// accepting the schema's explicit JSON null value.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
enum NullableReplacement {
    Value(String),
    Null(()),
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestDeprecation {
    replacement: NullableReplacement,
    migration_ref: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompilerRequirement {
    requires: String,
    #[serde(default)]
    features: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestDependency {
    package: String,
    requirement: String,
    source: String,
    content_hash: String,
    #[serde(default)]
    optional: bool,
    #[serde(default = "default_true")]
    default_features: bool,
    #[serde(default)]
    features: Vec<String>,
}

fn default_true() -> bool {
    true
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestFeatures {
    default: Vec<String>,
    available: BTreeMap<String, FeatureDefinition>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct FeatureDefinition {
    description: String,
    enables: Vec<String>,
    optional_dependencies: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestDeclared {
    rings: Vec<String>,
    effects: Vec<String>,
    host_imports: Vec<String>,
    grant_categories: Vec<String>,
    taint_contracts: Vec<String>,
    determinism: String,
    resource_contract_ref: String,
    stable_errors: Vec<String>,
    trap_conditions: Vec<String>,
    trusted_surface: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Lockfile {
    format_version: String,
    root: String,
    root_manifest_hash: String,
    resolver: LockResolver,
    graph_hash: String,
    stdlib_hash: String,
    compiler_requires: String,
    nodes: Vec<LockNode>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LockResolver {
    contract: String,
    offline: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LockSource {
    pub kind: String,
    pub locator: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LockNode {
    package: String,
    version: String,
    source: LockSource,
    manifest_hash: String,
    content_hash: String,
    features: Vec<String>,
    modules: Vec<String>,
    dependencies: Vec<String>,
    yanked_observed: bool,
}

#[derive(Debug)]
struct LoadedPackage {
    manifest: Manifest,
    manifest_hash: String,
    content_hash: String,
    sources: Vec<PackageSource>,
}

/// An opened package directory. On Unix, every descendant is resolved from
/// this retained descriptor rather than by re-resolving an attacker-mutable
/// pathname. The path is diagnostic-only once the descriptor is acquired.
#[derive(Debug)]
struct PackageDirectory {
    path: PathBuf,
    #[cfg(unix)]
    fd: OwnedFd,
}

/// Resolve, validate, compile, and derive package claims through the compiler
/// of record, failing closed unless the fresh compilation is solver-verified.
/// The lockfile is mandatory and is never rewritten.
pub fn compile_local_package(
    root: &Path,
    options: CompileOptions,
) -> Result<PackageCompilation, PackageCompileError> {
    compile_local_package_with_context(root, options, &CompilerContext::default())
}

/// Accept a package only after compiling under the caller's explicit declaration
/// context and deriving a fresh solver witness. Context is not host approval.
pub fn compile_local_package_with_context(
    root: &Path,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<PackageCompilation, PackageCompileError> {
    let package = compile_local_package_structural_with_context(root, options, context)?;
    package.require_solver_verified()?;
    Ok(package)
}

/// Structural package compilation for solver-off diagnostics and regression
/// tests. This result is not acceptable release evidence and callers must not
/// emit or accept package artifacts from it.
#[doc(hidden)]
pub fn compile_local_package_structural(
    root: &Path,
    options: CompileOptions,
) -> Result<PackageCompilation, PackageCompileError> {
    compile_local_package_structural_with_context(root, options, &CompilerContext::default())
}

/// Structural-only package compilation with explicit declarations. This does
/// not waive the formal gate and is never solver-verified acceptance evidence.
#[doc(hidden)]
pub fn compile_local_package_structural_with_context(
    root: &Path,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<PackageCompilation, PackageCompileError> {
    let mut graph = load_locked_package(root)?;
    let source_files = graph
        .sources
        .iter()
        .map(|source| SourceFile::new(source.logical_name.clone(), source.text.clone()))
        .collect();
    let compilation = compile_library_project_with_context(source_files, options, context)?;
    bind_and_validate_claims(&compilation, &mut graph)?;
    Ok(PackageCompilation { compilation, graph })
}

/// Derive the canonical root-only offline lockfile bytes for a local package.
/// This helper is intentionally narrow: dependency resolution remains locked
/// by explicit checked-in lockfiles, while tests and successor proof tooling
/// can materialize the single-root candidate packages used by the fmt trial.
pub fn derive_local_package_lock(root: &Path) -> Result<Vec<u8>, PackageError> {
    let root = PackageDirectory::open_root(root)?;
    derive_open_package_lock(&root)
}

/// Create a root-only lock without overwriting any existing file or following a
/// leaf symlink. The retained directory descriptor owns both reads and the write.
pub fn create_local_package_lock(root: &Path) -> Result<Vec<u8>, PackageError> {
    let root = PackageDirectory::open_root(root)?;
    let bytes = derive_open_package_lock(&root)?;
    root.create_regular_file(LOCK_FILE, &bytes, "E_LOCK_CREATE")?;
    Ok(bytes)
}

fn derive_open_package_lock(root: &PackageDirectory) -> Result<Vec<u8>, PackageError> {
    let manifest_bytes =
        root.read_regular_file(Path::new(MANIFEST_FILE), MAX_JSON_BYTES, "E_MANIFEST")?;
    let manifest: Manifest = parse_json(&manifest_bytes, MANIFEST_FILE)?;
    validate_manifest_shape(&manifest)?;
    if !manifest.dependencies.is_empty() {
        return Err(PackageError::new(
            "E_MANIFEST",
            "derive_local_package_lock only supports root-only packages",
        ));
    }
    let identity = package_id(&manifest);
    let manifest_hash = canonical_manifest_hash(&manifest_bytes)?;
    let sources = load_module_sources(root, &identity, &manifest.modules)?;
    let content_hash =
        package_content_hash(&identity, &manifest.version, &manifest_bytes, &sources)?;
    let requested: BTreeSet<String> = manifest.features.default.iter().cloned().collect();
    let features: Vec<String> = feature_closure(&identity, &manifest, &requested)?
        .into_iter()
        .collect();
    let node = LockNode {
        package: identity.clone(),
        version: manifest.version.clone(),
        source: LockSource {
            kind: "workspace".to_owned(),
            locator: ".".to_owned(),
        },
        manifest_hash: manifest_hash.clone(),
        content_hash,
        features,
        modules: manifest.modules.clone(),
        dependencies: Vec::new(),
        yanked_observed: false,
    };
    let lock = Lockfile {
        format_version: "1".to_owned(),
        root: identity,
        root_manifest_hash: manifest_hash,
        resolver: LockResolver {
            contract: RESOLVER_CONTRACT.to_owned(),
            offline: true,
        },
        graph_hash: package_graph_hash(std::slice::from_ref(&node)),
        stdlib_hash: compiler_stdlib_hash(),
        compiler_requires: manifest.compiler.requires.clone(),
        nodes: vec![node],
    };
    serde_json::to_vec(&lock).map_err(|error| {
        PackageError::infrastructure(
            "E_LOCK_DERIVATION",
            format!("failed to serialize canonical lockfile: {error}"),
        )
    })
}

/// Recompile from the explicit root, compare every package-aware field, and
/// require a freshly derived solver witness before accepting the certificate.
/// Missing/malformed fields fail during strict deserialization; changed inputs
/// fail the exact comparison after fresh derivation.
pub fn verify_local_package_certificate(
    root: &Path,
    supplied: &PackageCertificateJson,
    options: CompileOptions,
) -> Result<PackageCompilation, PackageCompileError> {
    verify_local_package_certificate_with_context(
        root,
        supplied,
        options,
        &CompilerContext::default(),
    )
}

/// Re-derive using caller-selected declarations, never declarations inferred
/// from an unsigned certificate, and compare the complete existing certificate.
pub fn verify_local_package_certificate_with_context(
    root: &Path,
    supplied: &PackageCertificateJson,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<PackageCompilation, PackageCompileError> {
    let fresh = compile_local_package_with_context(root, options, context)?;
    compare_local_package_certificate(&fresh, supplied)?;
    Ok(fresh)
}

/// Exact structural re-derivation without accepting the result as
/// solver-verified. This exists for solver-off diagnostics and regression
/// tests; release and certificate-acceptance paths must call
/// [`verify_local_package_certificate`] instead.
#[doc(hidden)]
pub fn verify_local_package_certificate_structural(
    root: &Path,
    supplied: &PackageCertificateJson,
    options: CompileOptions,
) -> Result<PackageCompilation, PackageCompileError> {
    verify_local_package_certificate_structural_with_context(
        root,
        supplied,
        options,
        &CompilerContext::default(),
    )
}

/// Structural-only exact rederivation under the same caller context as compile.
/// Certificate acceptance must use the solver-requiring variant instead.
#[doc(hidden)]
pub fn verify_local_package_certificate_structural_with_context(
    root: &Path,
    supplied: &PackageCertificateJson,
    options: CompileOptions,
    context: &CompilerContext,
) -> Result<PackageCompilation, PackageCompileError> {
    let fresh = compile_local_package_structural_with_context(root, options, context)?;
    compare_local_package_certificate(&fresh, supplied)?;
    Ok(fresh)
}

fn compare_local_package_certificate(
    fresh: &PackageCompilation,
    supplied: &PackageCertificateJson,
) -> Result<(), PackageCompileError> {
    let expected = fresh.certificate();
    if supplied != &expected {
        return Err(PackageError::infrastructure(
            "E_CERTIFICATE",
            "package certificate does not match freshly resolved, compiled, and derived inputs",
        )
        .into());
    }
    Ok(())
}

fn load_locked_package(root: &Path) -> Result<ResolvedPackageGraph, PackageError> {
    let root = PackageDirectory::open_root(root)?;

    let lock_bytes = root.read_regular_file(Path::new(LOCK_FILE), MAX_JSON_BYTES, "E_MANIFEST")?;
    let lock: Lockfile = parse_json(&lock_bytes, LOCK_FILE)?;
    validate_lock_shape(&lock)?;

    let root_manifest_bytes =
        root.read_regular_file(Path::new(MANIFEST_FILE), MAX_JSON_BYTES, "E_MANIFEST")?;
    let root_manifest: Manifest = parse_json(&root_manifest_bytes, MANIFEST_FILE)?;
    validate_manifest_shape(&root_manifest)?;
    let root_id = package_id(&root_manifest);
    if lock.root != root_id {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            format!(
                "lock root `{}` differs from manifest `{root_id}`",
                lock.root
            ),
        ));
    }

    let mut nodes: BTreeMap<String, &LockNode> = BTreeMap::new();
    let mut validation_nodes: Vec<&LockNode> = lock.nodes.iter().collect();
    validation_nodes.sort_by(|left, right| {
        left.package
            .cmp(&right.package)
            .then(left.version.cmp(&right.version))
            .then(left.source.kind.cmp(&right.source.kind))
            .then(left.source.locator.cmp(&right.source.locator))
    });
    for node in validation_nodes {
        validate_lock_node(node)?;
        if let Some(previous) = nodes.insert(node.package.clone(), node) {
            let code = if previous.version != node.version
                || previous.source != node.source
                || previous.content_hash != node.content_hash
            {
                "E_SOURCE_CONFLICT"
            } else {
                "E_MANIFEST"
            };
            return Err(PackageError::new(
                code,
                format!("duplicate locked package `{}`", node.package),
            ));
        }
        if node.yanked_observed {
            return Err(PackageError::new(
                "E_YANKED",
                format!("locked package `{}` is marked yanked", node.package),
            ));
        }
    }
    if !nodes.contains_key(&lock.root) {
        return Err(PackageError::new(
            "E_OFFLINE_MISS",
            "lockfile does not contain its root package",
        ));
    }

    let edge_count: usize = nodes.values().map(|node| node.dependencies.len()).sum();
    let source_count: usize = nodes.values().map(|node| node.modules.len()).sum();
    if edge_count > MAX_GRAPH_EDGES || source_count > MAX_PACKAGE_SOURCES {
        return Err(PackageError::new(
            "E_RESOURCE_LIMIT",
            format!(
                "package graph exceeds limits: edges={edge_count}/{MAX_GRAPH_EDGES}, sources={source_count}/{MAX_PACKAGE_SOURCES}"
            ),
        ));
    }

    let mut loaded = BTreeMap::<String, LoadedPackage>::new();
    let mut total_source_bytes = 0usize;
    for (identity, node) in &nodes {
        let package_root = package_directory(&root, node, identity == &lock.root)?;
        let manifest_path = package_root.path.join(MANIFEST_FILE);
        let manifest_bytes = package_root.read_regular_file(
            Path::new(MANIFEST_FILE),
            MAX_JSON_BYTES,
            "E_OFFLINE_MISS",
        )?;
        let manifest: Manifest = parse_json(&manifest_bytes, &manifest_path.display().to_string())?;
        validate_manifest_shape(&manifest)?;
        let actual_id = package_id(&manifest);
        if actual_id != **identity || manifest.version != node.version {
            return Err(PackageError::new(
                "E_LOCK_DRIFT",
                format!(
                    "locked `{identity}@{}` resolves to manifest `{actual_id}@{}`",
                    node.version, manifest.version
                ),
            ));
        }
        let manifest_hash = canonical_manifest_hash(&manifest_bytes)?;
        let sources = load_module_sources(&package_root, identity, &manifest.modules)?;
        total_source_bytes = total_source_bytes.saturating_add(
            sources
                .iter()
                .map(|source| source.text.len())
                .sum::<usize>(),
        );
        if total_source_bytes > MAX_TOTAL_SOURCE_BYTES {
            return Err(PackageError::new(
                "E_RESOURCE_LIMIT",
                format!("normalized package source bytes exceed {MAX_TOTAL_SOURCE_BYTES}"),
            ));
        }
        let content_hash =
            package_content_hash(identity, &manifest.version, &manifest_bytes, &sources)?;
        loaded.insert(
            identity.clone(),
            LoadedPackage {
                manifest,
                manifest_hash,
                content_hash,
                sources,
            },
        );
    }

    // Structural graph failures are diagnosed from fully validated manifests
    // before cryptographic pins. In particular, a dependency cycle cannot have
    // a self-consistent family of manifests when each dependent pins the
    // other's content hash; detecting the structural cycle first keeps
    // E_DEP_CYCLE executable instead of making it unreachable behind hashes.
    preflight_manifest_graph(&lock, &nodes, &loaded)?;
    for (identity, package) in &loaded {
        let node = nodes[identity];
        if package.manifest.modules != node.modules {
            return Err(PackageError::new(
                "E_LOCK_DRIFT",
                format!("module list drift for `{identity}`"),
            ));
        }
        if package.manifest_hash != node.manifest_hash {
            return Err(PackageError::new(
                "E_HASH_MISMATCH",
                format!("manifest hash mismatch for `{identity}`"),
            ));
        }
        if package.content_hash != node.content_hash {
            return Err(PackageError::new(
                "E_HASH_MISMATCH",
                format!("content hash mismatch for `{identity}`"),
            ));
        }
    }

    let root_loaded = loaded.get(&lock.root).expect("root checked above");
    if lock.root_manifest_hash != root_loaded.manifest_hash {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            "root_manifest_hash differs from the root manifest",
        ));
    }
    if lock.compiler_requires != root_loaded.manifest.compiler.requires {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            "lock compiler requirement differs from the root manifest",
        ));
    }
    for (identity, package) in &loaded {
        if !compiler_requirement_matches(&package.manifest.compiler.requires, COMPILER_VERSION) {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!(
                    "package `{identity}` requires compiler `{}` but this compiler is `{COMPILER_VERSION}`",
                    package.manifest.compiler.requires
                ),
            ));
        }
    }

    validate_locked_resolution(&lock, &nodes, &loaded)?;
    let order = canonical_dependency_order(&lock.root, &nodes)?;
    let observed_order: Vec<&str> = lock
        .nodes
        .iter()
        .map(|node| node.package.as_str())
        .collect();
    let expected_order: Vec<&str> = order.iter().map(String::as_str).collect();
    if observed_order != expected_order {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            format!("lock node order is non-canonical; expected {expected_order:?}"),
        ));
    }

    let stdlib_hash = compiler_stdlib_hash();
    if lock.stdlib_hash != stdlib_hash {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            format!(
                "stdlib identity drift: lock={}, compiler={stdlib_hash}",
                lock.stdlib_hash
            ),
        ));
    }
    let graph_hash = package_graph_hash(&lock.nodes);
    if lock.graph_hash != graph_hash {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            format!(
                "graph hash mismatch: lock={}, derived={graph_hash}",
                lock.graph_hash
            ),
        ));
    }

    let stdlib_modules = crate::ambient_stdlib::all_module_names();
    let mut owners: BTreeMap<String, String> = stdlib_modules
        .into_iter()
        .map(|module| (module.to_owned(), "compiler stdlib".to_owned()))
        .collect();
    let mut sources = Vec::new();
    for identity in &order {
        let package = loaded
            .get(identity)
            .expect("canonical order uses loaded nodes");
        for source in &package.sources {
            if let Some(owner) = owners.insert(source.module.clone(), identity.clone()) {
                return Err(PackageError::new(
                    "E_MODULE_COLLISION",
                    format!(
                        "module `{}` from `{identity}` collides with `{owner}`",
                        source.module
                    ),
                ));
            }
            sources.push(source.clone());
        }
    }

    let source_framing_hash = package_source_set_hash(&sources);
    let lockfile_hash = prefixed_sha256(&lock_bytes);
    let claims = order
        .iter()
        .map(|identity| (identity.clone(), loaded[identity].manifest.declared.clone()))
        .collect();
    let certificate_nodes = order
        .iter()
        .map(|identity| {
            let node = nodes[identity];
            let package = &loaded[identity];
            PackageNodeCertificateJson {
                package: identity.clone(),
                version: node.version.clone(),
                source: node.source.clone(),
                manifest_hash: package.manifest_hash.clone(),
                content_hash: package.content_hash.clone(),
                features: node.features.clone(),
                modules: node.modules.clone(),
                dependencies: node.dependencies.clone(),
                derived: empty_derived_facts(),
            }
        })
        .collect();

    Ok(ResolvedPackageGraph {
        root_package: lock.root,
        root_version: root_loaded.manifest.version.clone(),
        root_manifest_hash: root_loaded.manifest_hash.clone(),
        lockfile_hash,
        graph_hash,
        source_framing_hash,
        sources,
        certificate_nodes,
        graph_preimage: package_graph_preimage(&lock.nodes),
        lockfile_bytes: lock_bytes,
        ambient_stdlib: AmbientStdlibCertificateJson {
            modules: Vec::new(),
            derived: empty_derived_facts(),
        },
        claims,
    })
}

fn preflight_manifest_graph(
    lock: &Lockfile,
    nodes: &BTreeMap<String, &LockNode>,
    loaded: &BTreeMap<String, LoadedPackage>,
) -> Result<(), PackageError> {
    let mut edges = BTreeMap::<String, Vec<String>>::new();
    for (identity, package) in loaded {
        let mut dependencies = Vec::new();
        for dependency in &package.manifest.dependencies {
            // Optional-only cycles are checked after feature expansion. Every
            // non-optional edge is unconditionally active and safe to preflight.
            if dependency.optional {
                continue;
            }
            let node = nodes.get(&dependency.package).ok_or_else(|| {
                PackageError::new(
                    "E_PACKAGE_MISSING",
                    format!(
                        "dependency `{}` of `{identity}` is absent",
                        dependency.package
                    ),
                )
            })?;
            if !version_matches(&node.version, &dependency.requirement) {
                return Err(PackageError::new(
                    "E_VERSION_CONFLICT",
                    format!(
                        "`{identity}` requires `{}` `{}` but lock selects `{}`",
                        dependency.package, dependency.requirement, node.version
                    ),
                ));
            }
            if node.source.kind != dependency.source {
                return Err(PackageError::new(
                    "E_SOURCE_CONFLICT",
                    format!("source kind conflict for `{}`", dependency.package),
                ));
            }
            dependencies.push(dependency.package.clone());
        }
        dependencies.sort();
        edges.insert(identity.clone(), dependencies);
    }

    fn visit(
        identity: &str,
        edges: &BTreeMap<String, Vec<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        depth: usize,
    ) -> Result<(), PackageError> {
        if depth > MAX_DEPENDENCY_DEPTH {
            return Err(PackageError::new(
                "E_RESOURCE_LIMIT",
                format!("dependency depth exceeds {MAX_DEPENDENCY_DEPTH}"),
            ));
        }
        if visited.contains(identity) {
            return Ok(());
        }
        if !visiting.insert(identity.to_owned()) {
            return Err(PackageError::new(
                "E_DEP_CYCLE",
                format!("dependency cycle includes `{identity}`"),
            ));
        }
        for dependency in edges.get(identity).into_iter().flatten() {
            visit(dependency, edges, visiting, visited, depth + 1)?;
        }
        visiting.remove(identity);
        visited.insert(identity.to_owned());
        Ok(())
    }
    visit(
        &lock.root,
        &edges,
        &mut BTreeSet::new(),
        &mut BTreeSet::new(),
        0,
    )?;

    let mut owners: BTreeMap<String, String> = crate::ambient_stdlib::all_module_names()
        .into_iter()
        .map(|module| (module.to_owned(), "compiler stdlib".to_owned()))
        .collect();
    for (identity, package) in loaded {
        for module in &package.manifest.modules {
            if let Some(owner) = owners.insert(module.clone(), identity.clone()) {
                return Err(PackageError::new(
                    "E_MODULE_COLLISION",
                    format!("module `{module}` from `{identity}` collides with `{owner}`"),
                ));
            }
        }
    }
    Ok(())
}

fn validate_locked_resolution(
    lock: &Lockfile,
    nodes: &BTreeMap<String, &LockNode>,
    loaded: &BTreeMap<String, LoadedPackage>,
) -> Result<(), PackageError> {
    // The root has no incoming manifest edge on which to carry an explicit
    // feature request. Resolver-v1 therefore uses the existing root lock-node
    // `features` field as that authoritative seed. Defaults and feature
    // closure are still derived from the freshly loaded manifest below, and
    // the ordinary equality check requires closure(seed U defaults) == seed.
    // Thus the same closed set remains graph/certificate-bound. This cannot
    // recover which members were in a hypothetical smaller original request.
    let root_requested = nodes[&lock.root].features.iter().cloned().collect();
    let mut requested: BTreeMap<String, BTreeSet<String>> =
        BTreeMap::from([(lock.root.clone(), root_requested)]);
    let mut defaults = BTreeSet::from([lock.root.clone()]);
    let mut reachable = BTreeSet::from([lock.root.clone()]);

    let mut converged = false;
    for _ in 0..(nodes.len().saturating_mul(8).max(8)) {
        let mut changed = false;
        for identity in reachable.clone() {
            let _node = nodes.get(&identity).ok_or_else(|| {
                PackageError::new(
                    "E_OFFLINE_MISS",
                    format!("locked dependency `{identity}` missing"),
                )
            })?;
            let package = &loaded[&identity];
            let mut wanted = requested.get(&identity).cloned().unwrap_or_default();
            if defaults.contains(&identity) {
                wanted.extend(package.manifest.features.default.iter().cloned());
            }
            let active_features = feature_closure(&identity, &package.manifest, &wanted)?;

            let optional_active: BTreeSet<String> = active_features
                .iter()
                .flat_map(|feature| {
                    package.manifest.features.available[feature]
                        .optional_dependencies
                        .iter()
                        .cloned()
                })
                .collect();
            let mut dependencies = package.manifest.dependencies.clone();
            dependencies.sort_by(|a, b| a.package.cmp(&b.package));
            for dependency in dependencies {
                if dependency.optional && !optional_active.contains(&dependency.package) {
                    continue;
                }
                let dependency_node = nodes.get(&dependency.package).ok_or_else(|| {
                    PackageError::new(
                        "E_OFFLINE_MISS",
                        format!(
                            "dependency `{}` of `{identity}` is absent",
                            dependency.package
                        ),
                    )
                })?;
                if !version_matches(&dependency_node.version, &dependency.requirement) {
                    return Err(PackageError::new(
                        "E_VERSION_CONFLICT",
                        format!(
                            "`{identity}` requires `{}` `{}` but lock selects `{}`",
                            dependency.package, dependency.requirement, dependency_node.version
                        ),
                    ));
                }
                if dependency_node.source.kind != dependency.source {
                    return Err(PackageError::new(
                        "E_SOURCE_CONFLICT",
                        format!("source kind conflict for `{}`", dependency.package),
                    ));
                }
                if dependency_node.content_hash != dependency.content_hash {
                    return Err(PackageError::new(
                        "E_HASH_MISMATCH",
                        format!(
                            "dependency content pin mismatch for `{}`",
                            dependency.package
                        ),
                    ));
                }
                if reachable.insert(dependency.package.clone()) {
                    changed = true;
                }
                let entry = requested.entry(dependency.package.clone()).or_default();
                let old_len = entry.len();
                entry.extend(dependency.features);
                changed |= old_len != entry.len();
                if dependency.default_features && defaults.insert(dependency.package) {
                    changed = true;
                }
            }
        }
        if !changed {
            converged = true;
            break;
        }
    }
    if !converged {
        return Err(PackageError::new(
            "E_MANIFEST",
            "feature/dependency expansion did not converge",
        ));
    }
    if reachable.len() != nodes.len() {
        let extras: Vec<&String> = nodes.keys().filter(|id| !reachable.contains(*id)).collect();
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            format!("lock contains unreachable packages: {extras:?}"),
        ));
    }

    // Compare against the lock only after the request/default-feature fixed
    // point. An earlier comparison rejects valid diamond graphs when a later
    // lexical node adds a feature request to a node already visited.
    for identity in &reachable {
        let node = nodes[identity];
        let package = &loaded[identity];
        let mut wanted = requested.get(identity).cloned().unwrap_or_default();
        if defaults.contains(identity) {
            wanted.extend(package.manifest.features.default.iter().cloned());
        }
        let active_features = feature_closure(identity, &package.manifest, &wanted)?;
        let locked_features: BTreeSet<String> = node.features.iter().cloned().collect();
        if active_features != locked_features {
            return Err(PackageError::new(
                "E_LOCK_DRIFT",
                format!(
                    "feature drift for `{identity}`: lock={locked_features:?}, derived={active_features:?}"
                ),
            ));
        }
        let optional_active: BTreeSet<String> = active_features
            .iter()
            .flat_map(|feature| {
                package.manifest.features.available[feature]
                    .optional_dependencies
                    .iter()
                    .cloned()
            })
            .collect();
        let active_dependencies: BTreeSet<String> = package
            .manifest
            .dependencies
            .iter()
            .filter(|dependency| {
                !dependency.optional || optional_active.contains(&dependency.package)
            })
            .map(|dependency| dependency.package.clone())
            .collect();
        let locked_dependencies: BTreeSet<String> = node.dependencies.iter().cloned().collect();
        if active_dependencies != locked_dependencies {
            return Err(PackageError::new(
                "E_LOCK_DRIFT",
                format!("active dependency drift for `{identity}`"),
            ));
        }
    }
    Ok(())
}

fn feature_closure(
    identity: &str,
    manifest: &Manifest,
    requested: &BTreeSet<String>,
) -> Result<BTreeSet<String>, PackageError> {
    fn visit(
        identity: &str,
        feature: &str,
        manifest: &Manifest,
        visiting: &mut BTreeSet<String>,
        active: &mut BTreeSet<String>,
        depth: usize,
    ) -> Result<(), PackageError> {
        if depth > MAX_FEATURE_DEPTH {
            return Err(PackageError::new(
                "E_RESOURCE_LIMIT",
                format!("feature depth in `{identity}` exceeds {MAX_FEATURE_DEPTH}"),
            ));
        }
        if active.contains(feature) {
            return Ok(());
        }
        if !visiting.insert(feature.to_owned()) {
            return Err(PackageError::new(
                "E_FEATURE_CYCLE",
                format!("feature cycle in `{identity}` at `{feature}`"),
            ));
        }
        let definition = manifest.features.available.get(feature).ok_or_else(|| {
            PackageError::new(
                "E_FEATURE_UNKNOWN",
                format!("unknown feature `{feature}` in `{identity}`"),
            )
        })?;
        let mut enabled = definition.enables.clone();
        enabled.sort();
        for child in enabled {
            visit(identity, &child, manifest, visiting, active, depth + 1)?;
        }
        visiting.remove(feature);
        active.insert(feature.to_owned());
        Ok(())
    }

    let mut active = BTreeSet::new();
    let mut visiting = BTreeSet::new();
    for feature in requested {
        visit(identity, feature, manifest, &mut visiting, &mut active, 0)?;
    }
    Ok(active)
}

fn canonical_dependency_order(
    root: &str,
    nodes: &BTreeMap<String, &LockNode>,
) -> Result<Vec<String>, PackageError> {
    fn visit(
        identity: &str,
        nodes: &BTreeMap<String, &LockNode>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        order: &mut Vec<String>,
        depth: usize,
    ) -> Result<(), PackageError> {
        if depth > MAX_DEPENDENCY_DEPTH {
            return Err(PackageError::new(
                "E_RESOURCE_LIMIT",
                format!("dependency depth exceeds {MAX_DEPENDENCY_DEPTH}"),
            ));
        }
        if visited.contains(identity) {
            return Ok(());
        }
        if !visiting.insert(identity.to_owned()) {
            return Err(PackageError::new(
                "E_DEP_CYCLE",
                format!("dependency cycle includes `{identity}`"),
            ));
        }
        let node = nodes.get(identity).ok_or_else(|| {
            PackageError::new(
                "E_OFFLINE_MISS",
                format!("missing locked node `{identity}`"),
            )
        })?;
        let mut dependencies = node.dependencies.clone();
        dependencies.sort();
        for dependency in dependencies {
            visit(&dependency, nodes, visiting, visited, order, depth + 1)?;
        }
        visiting.remove(identity);
        visited.insert(identity.to_owned());
        order.push(identity.to_owned());
        Ok(())
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut order = Vec::new();
    visit(root, nodes, &mut visiting, &mut visited, &mut order, 0)?;
    Ok(order)
}

impl PackageDirectory {
    fn create_regular_file(
        &self,
        leaf: &str,
        bytes: &[u8],
        code: &'static str,
    ) -> Result<(), PackageError> {
        #[cfg(unix)]
        {
            use rustix::fs::{Mode, OFlags, openat};
            use std::io::Write as _;
            // Internal fixed filenames only: this helper never traverses a path.
            if Path::new(leaf).components().count() != 1
                || !matches!(
                    Path::new(leaf).components().next(),
                    Some(Component::Normal(_))
                )
            {
                return Err(PackageError::infrastructure(
                    code,
                    "output must be a single regular filename",
                ));
            }
            let fd = openat(
                &self.fd,
                leaf,
                OFlags::WRONLY | OFlags::CREATE | OFlags::EXCL | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                Mode::RUSR | Mode::WUSR,
            )
            .map_err(|e| PackageError::infrastructure(code, e.to_string()))?;
            let mut file = fs::File::from(fd);
            file.write_all(bytes)
                .and_then(|()| file.sync_all())
                .map_err(|e| PackageError::infrastructure(code, e.to_string()))
        }
        #[cfg(not(unix))]
        {
            let _ = (leaf, bytes);
            Err(PackageError::infrastructure(
                code,
                "secure output is unavailable",
            ))
        }
    }

    fn open_root(path: &Path) -> Result<Self, PackageError> {
        #[cfg(unix)]
        {
            use rustix::fs::{Mode, OFlags, open};

            let flags = OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC;
            let fd = open(path, flags, Mode::empty()).map_err(|error| {
                PackageError::new(
                    "E_MANIFEST",
                    format!(
                        "package root `{}` is not a readable non-symlink directory: {error}",
                        path.display()
                    ),
                )
            })?;
            Ok(Self {
                path: path.to_owned(),
                fd,
            })
        }

        #[cfg(not(unix))]
        {
            Err(PackageError::new(
                "E_UNSUPPORTED_PLATFORM",
                format!(
                    "secure package traversal is unavailable on this platform for `{}`",
                    path.display()
                ),
            ))
        }
    }

    fn duplicate(&self) -> Result<Self, PackageError> {
        #[cfg(unix)]
        {
            let fd = rustix::io::fcntl_dupfd_cloexec(&self.fd, 0).map_err(|error| {
                PackageError::new(
                    "E_OFFLINE_MISS",
                    format!(
                        "failed to retain package directory `{}`: {error}",
                        self.path.display()
                    ),
                )
            })?;
            Ok(Self {
                path: self.path.clone(),
                fd,
            })
        }

        #[cfg(not(unix))]
        Ok(Self {
            path: self.path.clone(),
        })
    }

    fn open_directory(
        &self,
        relative: &Path,
        missing_code: &'static str,
    ) -> Result<Self, PackageError> {
        if relative.as_os_str().is_empty() {
            return self.duplicate();
        }

        #[cfg(unix)]
        {
            use rustix::fs::{Mode, OFlags, openat};

            let flags = OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC;
            let mut current = None;
            let mut display = self.path.clone();
            for component in relative.components() {
                let Component::Normal(name) = component else {
                    return Err(PackageError::new(
                        "E_MANIFEST",
                        format!(
                            "package directory path must be normalized and relative: `{}`",
                            relative.display()
                        ),
                    ));
                };
                display.push(name);
                let parent = current.as_ref().unwrap_or(&self.fd);
                let next = openat(parent, Path::new(name), flags, Mode::empty()).map_err(
                    |error| {
                        let code = if error == rustix::io::Errno::NOENT {
                            missing_code
                        } else {
                            "E_MANIFEST"
                        };
                        PackageError::new(
                            code,
                            format!(
                                "failed to open package directory `{}` without following symlinks: {error}",
                                display.display()
                            ),
                        )
                    },
                )?;
                current = Some(next);
            }
            Ok(Self {
                path: display,
                fd: current.expect("non-empty package directory path"),
            })
        }

        #[cfg(not(unix))]
        Err(PackageError::new(
            "E_UNSUPPORTED_PLATFORM",
            format!(
                "secure package traversal is unavailable on this platform for `{}`",
                self.path.join(relative).display()
            ),
        ))
    }

    fn read_regular_file(
        &self,
        relative: &Path,
        cap: u64,
        code: &'static str,
    ) -> Result<Vec<u8>, PackageError> {
        let path = self.path.join(relative);

        #[cfg(unix)]
        {
            use rustix::fs::{Mode, OFlags, openat};

            let leaf = relative.file_name().ok_or_else(|| {
                PackageError::new(
                    "E_MANIFEST",
                    format!(
                        "package file path must name a file: `{}`",
                        relative.display()
                    ),
                )
            })?;
            let parent = relative.parent().unwrap_or_else(|| Path::new(""));
            let opened_parent = if parent.as_os_str().is_empty() {
                None
            } else {
                Some(self.open_directory(parent, code)?)
            };
            let parent_fd = opened_parent
                .as_ref()
                .map(|directory| &directory.fd)
                .unwrap_or(&self.fd);
            let flags = OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC;
            let fd = openat(parent_fd, Path::new(leaf), flags, Mode::empty()).map_err(|error| {
                PackageError::new(
                    code,
                    format!(
                        "failed to open `{}` without following symlinks: {error}",
                        path.display()
                    ),
                )
            })?;
            let mut file = fs::File::from(fd);
            let metadata = file.metadata().map_err(|error| {
                PackageError::new(
                    code,
                    format!("failed to inspect `{}`: {error}", path.display()),
                )
            })?;
            if !metadata.is_file() {
                return Err(PackageError::new(
                    code,
                    format!("`{}` must be a regular non-symlink file", path.display()),
                ));
            }
            if metadata.len() > cap {
                return Err(PackageError::new(
                    code,
                    format!("`{}` exceeds the {cap}-byte limit", path.display()),
                ));
            }
            let mut bytes = Vec::new();
            file.by_ref()
                .take(cap + 1)
                .read_to_end(&mut bytes)
                .map_err(|error| {
                    PackageError::new(
                        code,
                        format!("failed to read `{}`: {error}", path.display()),
                    )
                })?;
            if bytes.len() as u64 > cap {
                return Err(PackageError::new(
                    code,
                    format!("`{}` exceeds the {cap}-byte limit", path.display()),
                ));
            }
            Ok(bytes)
        }

        #[cfg(not(unix))]
        Err(PackageError::new(
            "E_UNSUPPORTED_PLATFORM",
            format!(
                "secure package traversal is unavailable on this platform for `{}`",
                path.display()
            ),
        ))
    }
}

fn package_directory(
    root: &PackageDirectory,
    node: &LockNode,
    is_root: bool,
) -> Result<PackageDirectory, PackageError> {
    if is_root {
        if node.source.kind != "workspace" || node.source.locator != "." {
            return Err(PackageError::new(
                "E_LOCK_DRIFT",
                "the root lock node must use workspace locator `.`",
            ));
        }
        return root.duplicate();
    }
    let locator = normalized_relative_path(&node.source.locator, false)?;
    match node.source.kind.as_str() {
        "workspace" => root.open_directory(&locator, "E_OFFLINE_MISS"),
        "vendored" => root
            .open_directory(Path::new("vendor"), "E_OFFLINE_MISS")?
            .open_directory(&locator, "E_OFFLINE_MISS"),
        other => Err(PackageError::new(
            "E_MANIFEST",
            format!("unsupported source kind `{other}`"),
        )),
    }
}

fn load_module_sources(
    package_root: &PackageDirectory,
    identity: &str,
    modules: &[String],
) -> Result<Vec<PackageSource>, PackageError> {
    let mut sources = Vec::new();
    for module in modules {
        let relative = format!("src/{module}.sigil");
        let path = package_root.path.join(&relative);
        let bytes = package_root.read_regular_file(
            Path::new(&relative),
            MAX_SOURCE_BYTES,
            "E_OFFLINE_MISS",
        )?;
        let text = std::str::from_utf8(&bytes).map_err(|error| {
            PackageError::new(
                "E_MANIFEST",
                format!("source `{}` is not UTF-8: {error}", path.display()),
            )
        })?;
        let normalized = normalize_source(text);
        let parsed_source = SourceFile::new(path.display().to_string(), normalized.clone());
        let (program, diagnostics) = crate::parser::parse(&parsed_source);
        if diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity() == crate::diagnostics::Severity::Error)
        {
            let source_hash = prefixed_sha256(normalized.as_bytes());
            return Err(PackageError::new(
                "E_MANIFEST",
                format!(
                    "source `{}` with normalized hash {source_hash} cannot be parsed while validating its manifest module binding",
                    path.display()
                ),
            ));
        }
        if program.modules.len() != 1 || program.modules[0].name != *module {
            let declared: Vec<&str> = program
                .modules
                .iter()
                .map(|parsed| parsed.name.as_str())
                .collect();
            return Err(PackageError::new(
                "E_MANIFEST",
                format!(
                    "source `{}` must declare exactly manifest module `{module}`; parsed {declared:?}",
                    path.display()
                ),
            ));
        }
        for item in &program.modules[0].items {
            if let Some(kind) = unsupported_package_surface_kind(item) {
                return Err(PackageError::new(
                    "E_UNSUPPORTED_SURFACE",
                    format!(
                        "package `{identity}` module `{module}` uses unsupported v1 surface `{kind}`"
                    ),
                ));
            }
        }
        sources.push(PackageSource {
            package: identity.to_owned(),
            module: module.clone(),
            logical_name: format!("{identity}/{relative}"),
            text: normalized,
        });
    }
    sources.sort_by(|a, b| {
        a.module
            .cmp(&b.module)
            .then(a.logical_name.cmp(&b.logical_name))
    });
    Ok(sources)
}

fn unsupported_package_surface_kind(item: &Item) -> Option<&'static str> {
    match item {
        Item::ActorDef(_) => Some("actor"),
        Item::CapTypeDef(_) => Some("capability type"),
        Item::ImplDef(_) => Some("implementation"),
        Item::TraitDef(_) => Some("trait"),
        Item::StateDef(_) => Some("typestate"),
        _ => None,
    }
}

fn normalized_relative_path(value: &str, allow_dot: bool) -> Result<PathBuf, PackageError> {
    if value.is_empty() || value.contains('\\') || value.contains('\0') {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid package locator `{value}`"),
        ));
    }
    if allow_dot && value == "." {
        return Ok(PathBuf::from(value));
    }
    // `Path::components` normalizes repeated separators and `.` components.
    // Reject those aliases at the string boundary so one directory has one
    // graph identity and one certificate spelling on every platform.
    if value
        .split('/')
        .any(|component| component.is_empty() || component == "." || component == "..")
    {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("package locator must be normalized and relative: `{value}`"),
        ));
    }
    let path = Path::new(value);
    if path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("package locator must be normalized and relative: `{value}`"),
        ));
    }
    Ok(path.to_owned())
}

fn parse_json<T: for<'de> Deserialize<'de>>(bytes: &[u8], label: &str) -> Result<T, PackageError> {
    if bytes.starts_with(&[0xef, 0xbb, 0xbf]) {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("`{label}` must not contain a UTF-8 BOM"),
        ));
    }
    deserialize_json_without_duplicate_keys(bytes).map_err(|error| {
        PackageError::new("E_MANIFEST", format!("invalid `{label}` shape: {error}"))
    })
}

/// Deserialize JSON only after rejecting duplicate keys at every object
/// depth. `serde_json` otherwise accepts the last duplicate silently, which
/// makes the bytes-to-certificate/manifest interpretation ambiguous.
pub fn deserialize_json_without_duplicate_keys<T: serde::de::DeserializeOwned>(
    bytes: &[u8],
) -> Result<T, serde_json::Error> {
    let value: NoDuplicateJson = serde_json::from_slice(bytes)?;
    serde_json::from_value(value.0)
}

struct NoDuplicateJson(serde_json::Value);

impl<'de> Deserialize<'de> for NoDuplicateJson {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct JsonVisitor;

        impl<'de> serde::de::Visitor<'de> for JsonVisitor {
            type Value = NoDuplicateJson;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("JSON without duplicate object keys")
            }

            fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::Bool(value)))
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::Number(value.into())))
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::Number(value.into())))
            }

            fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                serde_json::Number::from_f64(value)
                    .map(|number| NoDuplicateJson(serde_json::Value::Number(number)))
                    .ok_or_else(|| E::custom("non-finite JSON number"))
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::String(value.to_owned())))
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::String(value)))
            }

            fn visit_none<E>(self) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::Null))
            }

            fn visit_unit<E>(self) -> Result<Self::Value, E> {
                Ok(NoDuplicateJson(serde_json::Value::Null))
            }

            fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut values = Vec::new();
                while let Some(value) = sequence.next_element::<NoDuplicateJson>()? {
                    values.push(value.0);
                }
                Ok(NoDuplicateJson(serde_json::Value::Array(values)))
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let mut values = serde_json::Map::new();
                while let Some(key) = map.next_key::<String>()? {
                    if values.contains_key(&key) {
                        return Err(serde::de::Error::custom(format!(
                            "duplicate JSON key `{key}`"
                        )));
                    }
                    values.insert(key, map.next_value::<NoDuplicateJson>()?.0);
                }
                Ok(NoDuplicateJson(serde_json::Value::Object(values)))
            }
        }

        deserializer.deserialize_any(JsonVisitor)
    }
}

fn validate_lock_shape(lock: &Lockfile) -> Result<(), PackageError> {
    if lock.format_version != "1"
        || lock.resolver.contract != RESOLVER_CONTRACT
        || !lock.resolver.offline
    {
        return Err(PackageError::new(
            "E_MANIFEST",
            "lockfile must use format 1, sigil-resolver-v1, and offline=true",
        ));
    }
    validate_package_id(&lock.root)?;
    validate_hash(&lock.root_manifest_hash)?;
    validate_hash(&lock.graph_hash)?;
    validate_hash(&lock.stdlib_hash)?;
    validate_bounded_string(&lock.compiler_requires, 1, 128, "lock compiler_requires")?;
    if lock.nodes.is_empty() {
        return Err(PackageError::new(
            "E_MANIFEST",
            "lockfile nodes must not be empty",
        ));
    }
    if lock.nodes.len() > MAX_PACKAGE_NODES {
        return Err(PackageError::new(
            "E_RESOURCE_LIMIT",
            format!(
                "lockfile contains {} nodes; maximum is {MAX_PACKAGE_NODES}",
                lock.nodes.len()
            ),
        ));
    }
    Ok(())
}

fn validate_lock_node(node: &LockNode) -> Result<(), PackageError> {
    validate_package_id(&node.package)?;
    parse_version(&node.version)?;
    validate_hash(&node.manifest_hash)?;
    validate_hash(&node.content_hash)?;
    match node.source.kind.as_str() {
        "workspace" | "vendored" => {}
        other => {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!("unsupported source kind `{other}`"),
            ));
        }
    }
    validate_bounded_string(&node.source.locator, 1, 1024, "lock source locator")?;
    normalized_relative_path(&node.source.locator, node.source.locator == ".")?;
    require_sorted_unique(&node.features, "locked features")?;
    require_sorted_unique(&node.modules, "locked modules")?;
    require_sorted_unique(&node.dependencies, "locked dependencies")?;
    if node.modules.is_empty() {
        return Err(PackageError::new(
            "E_MANIFEST",
            "locked modules must not be empty",
        ));
    }
    for feature in &node.features {
        validate_bounded_string(feature, 1, 128, "locked feature")?;
    }
    for module in &node.modules {
        validate_module_name(module)?;
    }
    for dependency in &node.dependencies {
        validate_package_id(dependency)?;
    }
    Ok(())
}

fn validate_manifest_shape(manifest: &Manifest) -> Result<(), PackageError> {
    if manifest.format_version != "1" {
        return Err(PackageError::new(
            "E_MANIFEST",
            "manifest format_version must be `1`",
        ));
    }
    validate_identity_component(&manifest.namespace)?;
    validate_identity_component(&manifest.name)?;
    parse_version(&manifest.version)?;
    if !matches!(
        manifest.maturity.as_str(),
        "contracted" | "incubating" | "candidate" | "stable" | "deprecated" | "retired"
    ) {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("unsupported package maturity `{}`", manifest.maturity),
        ));
    }
    validate_bounded_string(&manifest.description, 1, 1024, "description")?;
    validate_bounded_string(&manifest.license, 1, 128, "license")?;
    require_sorted_unique(&manifest.maintainers, "maintainers")?;
    for maintainer in &manifest.maintainers {
        validate_bounded_string(maintainer, 1, 256, "maintainer")?;
    }
    if let Some(source) = &manifest.source {
        validate_bounded_string(source, 0, 1024, "source")?;
    }
    validate_bounded_string(&manifest.compiler.requires, 1, 128, "compiler requires")?;
    if !compiler_requirement_matches(&manifest.compiler.requires, COMPILER_VERSION) {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!(
                "compiler requirement `{}` does not match compiler `{COMPILER_VERSION}`",
                manifest.compiler.requires
            ),
        ));
    }
    require_sorted_unique(&manifest.compiler.features, "compiler features")?;
    for feature in &manifest.compiler.features {
        validate_feature_name(feature)?;
        let available = match feature.as_str() {
            "json" => cfg!(feature = "json"),
            "solver" => crate::SOLVER_ENABLED,
            "trace" => cfg!(feature = "trace"),
            _ => {
                return Err(PackageError::new(
                    "E_MANIFEST",
                    format!("unsupported compiler feature `{feature}`"),
                ));
            }
        };
        if !available {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!("required compiler feature `{feature}` is not enabled"),
            ));
        }
    }
    if manifest.modules.is_empty() {
        return Err(PackageError::new(
            "E_MANIFEST",
            "manifest modules must not be empty",
        ));
    }
    require_sorted_unique(&manifest.modules, "manifest modules")?;
    for module in &manifest.modules {
        validate_module_name(module)?;
        if module != &manifest.name && !module.starts_with(&format!("{}_", manifest.name)) {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!(
                    "module `{module}` must equal package name `{}` or begin `{}_`",
                    manifest.name, manifest.name
                ),
            ));
        }
    }
    if manifest.dependencies.len() > MAX_MANIFEST_DEPENDENCIES {
        return Err(PackageError::new(
            "E_RESOURCE_LIMIT",
            format!(
                "manifest contains {} dependencies; maximum is {MAX_MANIFEST_DEPENDENCIES}",
                manifest.dependencies.len()
            ),
        ));
    }
    let mut dependency_optionality = BTreeMap::new();
    let dependency_order: Vec<String> = manifest
        .dependencies
        .iter()
        .map(|dependency| dependency.package.clone())
        .collect();
    require_sorted_unique(&dependency_order, "manifest dependencies")?;
    for dependency in &manifest.dependencies {
        validate_package_id(&dependency.package)?;
        validate_bounded_string(&dependency.requirement, 1, 128, "dependency requirement")?;
        parse_requirement(&dependency.requirement)?;
        validate_hash(&dependency.content_hash)?;
        if !matches!(dependency.source.as_str(), "workspace" | "vendored") {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!("unsupported dependency source `{}`", dependency.source),
            ));
        }
        require_sorted_unique(&dependency.features, "dependency features")?;
        for feature in &dependency.features {
            validate_feature_name(feature)?;
        }
        if dependency_optionality
            .insert(dependency.package.clone(), dependency.optional)
            .is_some()
        {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!("duplicate dependency `{}`", dependency.package),
            ));
        }
    }
    for feature in &manifest.features.default {
        validate_feature_name(feature)?;
    }
    require_sorted_unique(&manifest.features.default, "default features")?;
    for (name, definition) in &manifest.features.available {
        validate_feature_name(name)?;
        validate_bounded_string(&definition.description, 1, 512, "feature description")?;
        require_sorted_unique(&definition.enables, "enabled features")?;
        require_sorted_unique(
            &definition.optional_dependencies,
            "optional feature dependencies",
        )?;
        for enabled in &definition.enables {
            validate_feature_name(enabled)?;
            if !manifest.features.available.contains_key(enabled) {
                return Err(PackageError::new(
                    "E_MANIFEST",
                    format!("feature `{name}` enables undefined feature `{enabled}`"),
                ));
            }
        }
        for dependency in &definition.optional_dependencies {
            validate_bounded_string(dependency, 3, 129, "optional dependency")?;
            match dependency_optionality.get(dependency) {
                None => {
                    return Err(PackageError::new(
                        "E_MANIFEST",
                        format!("feature `{name}` activates undeclared dependency `{dependency}`"),
                    ));
                }
                Some(false) => {
                    return Err(PackageError::new(
                        "E_MANIFEST",
                        format!(
                            "feature `{name}` lists dependency `{dependency}` as optional, but its dependency declaration has optional=false"
                        ),
                    ));
                }
                Some(true) => {}
            }
        }
    }
    // Every declared feature is part of the manifest contract even when the
    // current root does not select it. Validate dormant branches now so a
    // later feature selection cannot awaken a previously certified cycle.
    let identity = package_id(manifest);
    for feature in manifest.features.available.keys() {
        feature_closure(&identity, manifest, &BTreeSet::from([feature.clone()]))?;
    }
    if manifest.declared.rings.is_empty() {
        return Err(PackageError::new(
            "E_MANIFEST",
            "declared rings must not be empty",
        ));
    }
    for ring in &manifest.declared.rings {
        if !matches!(ring.as_str(), "inner" | "outer" | "trusted_outer") {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!("unsupported declared ring `{ring}`"),
            ));
        }
    }
    for values in [
        &manifest.declared.effects,
        &manifest.declared.host_imports,
        &manifest.declared.grant_categories,
        &manifest.declared.taint_contracts,
        &manifest.declared.stable_errors,
        &manifest.declared.trap_conditions,
        &manifest.declared.trusted_surface,
    ] {
        require_sorted_unique(values, "manifest claim set")?;
        for value in values {
            validate_bounded_string(value, 1, 1024, "manifest claim")?;
        }
    }
    require_sorted_unique(&manifest.declared.rings, "manifest rings")?;
    if !matches!(
        manifest.declared.determinism.as_str(),
        "pure" | "state_relative" | "environment_relative" | "seeded" | "nondeterministic"
    ) {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!(
                "unsupported determinism claim `{}`",
                manifest.declared.determinism
            ),
        ));
    }
    validate_bounded_string(
        &manifest.declared.resource_contract_ref,
        1,
        1024,
        "resource_contract_ref",
    )?;
    for hash in [
        &manifest.evidence.charter_hash,
        &manifest.evidence.api_contract_hash,
        &manifest.evidence.api_card_hash,
        &manifest.evidence.evidence_manifest_hash,
    ] {
        validate_hash(hash)?;
    }
    for (values, label) in [
        (&manifest.evidence.certificate_refs, "certificate_refs"),
        (&manifest.evidence.corpus_lineage, "corpus_lineage"),
    ] {
        require_sorted_unique(values, label)?;
        for value in values {
            validate_bounded_string(value, 1, 1024, label)?;
        }
    }
    if let Some(deprecation) = &manifest.deprecation {
        if let NullableReplacement::Value(replacement) = &deprecation.replacement {
            validate_bounded_string(replacement, 0, 129, "deprecation replacement")?;
        }
        validate_bounded_string(
            &deprecation.migration_ref,
            1,
            1024,
            "deprecation migration_ref",
        )?;
    }
    Ok(())
}

fn validate_bounded_string(
    value: &str,
    min: usize,
    max: usize,
    label: &str,
) -> Result<(), PackageError> {
    let length = value.chars().count();
    if !(min..=max).contains(&length) {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("{label} length must be in {min}..={max} characters"),
        ));
    }
    Ok(())
}

fn validate_identity_component(value: &str) -> Result<(), PackageError> {
    let valid = (2..=64).contains(&value.len())
        && value.as_bytes()[0].is_ascii_lowercase()
        && value.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_' || byte == b'-'
        });
    if !valid {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid package identity component `{value}`"),
        ));
    }
    Ok(())
}

fn validate_package_id(value: &str) -> Result<(), PackageError> {
    let Some((namespace, name)) = value.split_once('/') else {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid package id `{value}`"),
        ));
    };
    if name.contains('/') {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid package id `{value}`"),
        ));
    }
    validate_identity_component(namespace)?;
    validate_identity_component(name)
}

fn validate_module_name(value: &str) -> Result<(), PackageError> {
    let mut bytes = value.bytes();
    let Some(first) = bytes.next() else {
        return Err(PackageError::new(
            "E_MANIFEST",
            "module name must not be empty",
        ));
    };
    if !(first.is_ascii_lowercase() || first == b'_')
        || !bytes.all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_')
    {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid module name `{value}`"),
        ));
    }
    Ok(())
}

fn validate_feature_name(value: &str) -> Result<(), PackageError> {
    if value.is_empty()
        || value.len() > 64
        || !value.as_bytes()[0].is_ascii_lowercase()
        || !value.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_' || byte == b'-'
        })
    {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid feature name `{value}`"),
        ));
    }
    Ok(())
}

fn validate_hash(value: &str) -> Result<(), PackageError> {
    let valid = value.len() == 71
        && value.starts_with("sha256:")
        && value[7..]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte));
    if !valid {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid SHA-256 value `{value}`"),
        ));
    }
    Ok(())
}

fn require_sorted_unique(values: &[String], label: &str) -> Result<(), PackageError> {
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("{label} must be lexically sorted and duplicate-free"),
        ));
    }
    Ok(())
}

fn package_id(manifest: &Manifest) -> String {
    format!("{}/{}", manifest.namespace, manifest.name)
}

type Version = semver::Version;

fn parse_version(value: &str) -> Result<Version, PackageError> {
    // V1 deliberately excludes build metadata even though SemVer itself
    // permits it; everything else uses the SemVer 2.0 parser and precedence.
    if value.contains('+') {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("invalid version `{value}`"),
        ));
    }
    semver::Version::parse(value)
        .map_err(|_| PackageError::new("E_MANIFEST", format!("invalid version `{value}`")))
}

fn parse_requirement(value: &str) -> Result<(char, Version), PackageError> {
    let mut chars = value.chars();
    let Some(operator @ ('=' | '^' | '~')) = chars.next() else {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!("unsupported package requirement `{value}`"),
        ));
    };
    Ok((operator, parse_version(chars.as_str())?))
}

fn version_matches(version: &str, requirement: &str) -> bool {
    let Ok(candidate) = parse_version(version) else {
        return false;
    };
    let Ok((operator, base)) = parse_requirement(requirement) else {
        return false;
    };
    if !candidate.pre.is_empty() || !base.pre.is_empty() {
        return operator == '=' && candidate == base;
    }
    let triplet = (candidate.major, candidate.minor, candidate.patch);
    let floor = (base.major, base.minor, base.patch);
    match operator {
        '=' => triplet == floor,
        '~' => triplet >= floor && triplet < (base.major, base.minor.saturating_add(1), 0),
        '^' if base.major > 0 => triplet >= floor && triplet < (base.major.saturating_add(1), 0, 0),
        '^' if base.minor > 0 => triplet >= floor && triplet < (0, base.minor.saturating_add(1), 0),
        '^' => triplet >= floor && triplet < (0, 0, base.patch.saturating_add(1)),
        _ => false,
    }
}

fn compiler_requirement_matches(requirement: &str, version: &str) -> bool {
    if let Some(base) = requirement.strip_prefix(">=") {
        return match (parse_version(version), parse_version(base)) {
            (Ok(candidate), Ok(floor)) => candidate >= floor,
            _ => false,
        };
    }
    version_matches(version, requirement)
}

fn normalize_source(source: &str) -> String {
    let lf = source.replace("\r\n", "\n").replace('\r', "\n");
    let mut normalized = lf
        .split('\n')
        .map(|line| line.trim_end_matches([' ', '\t']))
        .collect::<Vec<_>>()
        .join("\n");
    if !normalized.ends_with('\n') {
        normalized.push('\n');
    }
    normalized
}

fn canonical_manifest_hash(bytes: &[u8]) -> Result<String, PackageError> {
    let value: serde_json::Value = parse_json(bytes, MANIFEST_FILE)?;
    let canonical = serde_json::to_vec(&value).map_err(|error| {
        PackageError::new(
            "E_MANIFEST",
            format!("failed to canonicalize manifest: {error}"),
        )
    })?;
    Ok(prefixed_sha256(&canonical))
}

fn package_content_hash(
    identity: &str,
    version: &str,
    manifest_bytes: &[u8],
    sources: &[PackageSource],
) -> Result<String, PackageError> {
    let value: serde_json::Value = parse_json(manifest_bytes, MANIFEST_FILE)?;
    let canonical = serde_json::to_vec(&value).map_err(|error| {
        PackageError::new(
            "E_MANIFEST",
            format!("failed to canonicalize manifest: {error}"),
        )
    })?;
    let mut digest = Sha256::new();
    digest.update(CONTENT_DOMAIN);
    frame(&mut digest, identity.as_bytes());
    frame(&mut digest, version.as_bytes());
    frame(&mut digest, &canonical);
    for source in sources {
        let relative = format!("src/{}.sigil", source.module);
        frame(&mut digest, source.module.as_bytes());
        frame(&mut digest, relative.as_bytes());
        frame(&mut digest, source.text.as_bytes());
    }
    Ok(format!("sha256:{:x}", digest.finalize()))
}

fn package_graph_hash(nodes: &[LockNode]) -> String {
    prefixed_sha256(&package_graph_preimage(nodes))
}

fn package_graph_preimage(nodes: &[LockNode]) -> Vec<u8> {
    let mut digest = Preimage::default();
    digest.update(GRAPH_DOMAIN);
    for node in nodes {
        frame(&mut digest, node.package.as_bytes());
        frame(&mut digest, node.version.as_bytes());
        frame(&mut digest, node.source.kind.as_bytes());
        frame(&mut digest, node.source.locator.as_bytes());
        frame(&mut digest, node.manifest_hash.as_bytes());
        frame(&mut digest, node.content_hash.as_bytes());
        frame(
            &mut digest,
            canonical_string_array(&node.features).as_bytes(),
        );
        frame(
            &mut digest,
            canonical_string_array(&node.modules).as_bytes(),
        );
        frame(
            &mut digest,
            canonical_string_array(&node.dependencies).as_bytes(),
        );
    }
    digest.0
}

/// The compiled callable surface of package-owned modules, excluding ambient
/// library modules. Nominal types remain nominal: this is not a declaration
/// inventory for records, constants, or uninstantiated generics. Source/graph
/// and artifact identities bind the definitions behind those names separately.
fn package_public_api(
    graph: &ResolvedPackageGraph,
    compilation: &Compilation,
) -> Vec<serde_json::Value> {
    let modules: BTreeSet<&str> = graph.sources.iter().map(|s| s.module.as_str()).collect();
    let mut entries = Vec::new();
    let registry = &compilation.typed.effect_registry;
    for module in &compilation.typed.modules {
        if !modules.contains(module.name.as_str()) {
            continue;
        }
        for function in &module.functions {
            // Module initializers are compiler scaffolding, not declared API.
            // Their code/export still contributes to the exact Wasm identity.
            if !function.externally_callable
                || matches!(
                    function.kind,
                    crate::typed_ast::TypedFunctionKind::ModuleInit
                )
            {
                continue;
            }
            let name = function.name.rsplit("::").next().expect("function name");
            let params = function
                .params
                .iter()
                .map(|param| {
                    let label = if param.flow {
                        "Flow"
                    } else {
                        taint_name(param.taint)
                    };
                    format!(
                        "{}:{}@{label}",
                        param.name,
                        package_api_type(&param.ty, registry)
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let result = package_api_type(&function.ret, registry);
            let label = if function.ret_flow {
                "Flow"
            } else {
                taint_name(function.ret_taint)
            };
            // Typed effects describe the implementation, whereas a checked
            // declaration may intentionally expose a larger row (e.g. Alloc).
            // Join by declaration span, including generic specializations;
            // never derive a row from a package name or unchecked manifest.
            let mut effects: BTreeSet<String> = function
                .effects
                .effects
                .iter()
                .map(|id| registry.name_of(*id).expect("checked effect").to_owned())
                .collect();
            for source_module in &compilation.ast.modules {
                if source_module.name != module.name {
                    continue;
                }
                for item in &source_module.items {
                    let declarations: &[crate::ast::FnDef] = match item {
                        Item::FnDef(def) => std::slice::from_ref(def),
                        Item::ImplDef(def) => &def.methods,
                        _ => &[],
                    };
                    for def in declarations.iter().filter(|def| def.span == function.span) {
                        let variables = crate::ast::effect_row_param_names(def);
                        if let Some(row) = &def.effects {
                            effects.extend(
                                row.iter()
                                    .filter(|name| !variables.contains(*name))
                                    .cloned(),
                            );
                        }
                    }
                }
            }
            let effects = effects.into_iter().collect::<Vec<_>>().join(",");
            entries.push(serde_json::json!({
                "kind": "function",
                "module": module.name,
                "name": name,
                "signature": format!("fn {name}({params})->{result}@{label}!{{{effects}}}"),
                "wasm_export": function.export_name,
            }));
        }
    }
    entries.sort_by(|left, right| {
        let key = |value: &serde_json::Value| {
            (
                value["module"].as_str().unwrap_or_default().to_owned(),
                value["name"].as_str().unwrap_or_default().to_owned(),
            )
        };
        key(left).cmp(&key(right))
    });
    entries
}

fn package_api_effects(
    effects: &crate::registries::EffectSet,
    registry: &crate::registries::EffectRegistry,
) -> String {
    let names: BTreeSet<_> = effects
        .effects
        .iter()
        .map(|id| {
            registry
                .name_of(*id)
                .expect("checked effect has a registered identity")
        })
        .collect();
    names.into_iter().collect::<Vec<_>>().join(",")
}

/// Identity encoding, not the lossy diagnostic type renderer. In particular,
/// nested function types retain linearity and the names of their latent effects.
fn package_api_type(
    ty: &crate::type_check::Type,
    registry: &crate::registries::EffectRegistry,
) -> String {
    use crate::type_check::Type;
    let render = |ty: &Type| package_api_type(ty, registry);
    let render_many = |types: &[Type]| types.iter().map(&render).collect::<Vec<_>>().join(",");
    match ty {
        Type::Unit => "unit".into(),
        Type::Bool => "bool".into(),
        Type::I32 => "i32".into(),
        Type::U32 => "u32".into(),
        Type::I64 => "i64".into(),
        Type::U64 => "u64".into(),
        Type::F64 => "f64".into(),
        Type::U256 => "u256".into(),
        Type::I256 => "i256".into(),
        Type::Str => "str".into(),
        Type::Generic(name) => format!("generic<{name}>"),
        Type::Named(name, args) => format!("named<{name};{}>", render_many(args)),
        Type::Cap(name, args) => format!(
            "cap<{name};{}>",
            args.iter()
                .map(i64::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ),
        Type::ActorRef(name) => format!("actor<{name}>"),
        Type::Array { elem, size } => format!("[{};{size}]", render(elem)),
        Type::Fn(args, ret, linear, effects) => format!(
            "fn[linear={linear}]({})->{}!{{{}}}",
            render_many(args),
            render(ret),
            package_api_effects(effects, registry)
        ),
        Type::Ref(inner, mutable) => format!("ref[mutable={mutable}]<{}>", render(inner)),
        Type::Slice(inner) => format!("slice<{}>", render(inner)),
        Type::Ptr(inner) => format!("ptr<{}>", render(inner)),
        Type::MutPtr(inner) => format!("mutptr<{}>", render(inner)),
        Type::Region => "region".into(),
        Type::Tuple(elems) => format!("({})", render_many(elems)),
        Type::IntLit(value) => format!("intlit<{value}>"),
        Type::HktVar { name, arity } => format!("hktvar<{name};{arity}>"),
        Type::HktApp { ctor, args } => format!("hktapp<{ctor};{}>", render_many(args)),
        Type::TypeCtor(name) => format!("typector<{name}>"),
        Type::StateMarker(name) => format!("state<{name}>"),
        Type::Never => "never".into(),
        Type::Error => "error".into(),
    }
}

fn package_public_api_hash(entries: &[serde_json::Value]) -> Result<String, serde_json::Error> {
    Ok(prefixed_sha256(&package_public_api_preimage(entries)?))
}

fn package_public_api_preimage(
    entries: &[serde_json::Value],
) -> Result<Vec<u8>, serde_json::Error> {
    let json = serde_json::to_vec(entries)?;
    let mut digest = Preimage::default();
    digest.update(PUBLIC_API_DOMAIN);
    digest.update((json.len() as u64).to_be_bytes());
    digest.update(json);
    Ok(digest.0)
}

fn package_artifact_identity_hash(
    graph: &ResolvedPackageGraph,
    compilation: &Compilation,
    compiler_identity_hash: &str,
    public_api_hash: &str,
) -> String {
    prefixed_sha256(&package_artifact_preimage(
        graph,
        compilation,
        compiler_identity_hash,
        public_api_hash,
    ))
}

fn package_artifact_preimage(
    graph: &ResolvedPackageGraph,
    compilation: &Compilation,
    compiler_identity_hash: &str,
    public_api_hash: &str,
) -> Vec<u8> {
    let mut digest = Preimage::default();
    digest.update(ARTIFACT_ID_DOMAIN);
    frame(&mut digest, graph.graph_hash.as_bytes());
    frame(&mut digest, graph.source_framing_hash.as_bytes());
    frame(&mut digest, compiler_identity_hash.as_bytes());
    let proof_tier = if compilation.capability_report.solver_verified {
        "solver_verified"
    } else {
        "structural_only"
    };
    frame(&mut digest, proof_tier.as_bytes());
    frame(&mut digest, public_api_hash.as_bytes());
    frame(&mut digest, RUNTIME_VERSION.as_bytes());
    frame(&mut digest, &compilation.wasm_inner);
    if let Some(outer) = compilation.wasm_outer.as_deref() {
        frame(&mut digest, b"outer-present");
        frame(&mut digest, outer);
    } else {
        frame(&mut digest, b"outer-absent");
    }
    digest.0
}

fn package_source_set_hash(sources: &[PackageSource]) -> String {
    prefixed_sha256(&package_source_set_preimage(sources))
}

fn package_source_set_preimage(sources: &[PackageSource]) -> Vec<u8> {
    let mut digest = Preimage::default();
    digest.update(SOURCE_SET_DOMAIN);
    for source in sources {
        frame(&mut digest, source.package.as_bytes());
        frame(&mut digest, source.module.as_bytes());
        frame(&mut digest, source.logical_name.as_bytes());
        frame(&mut digest, source.text.as_bytes());
    }
    digest.0
}

fn canonical_string_array(values: &[String]) -> String {
    serde_json::to_string(values).expect("string array serialization is infallible")
}

trait FrameSink {
    fn append(&mut self, bytes: &[u8]);
}

impl FrameSink for Sha256 {
    fn append(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }
}

#[derive(Default)]
struct Preimage(Vec<u8>);

impl Preimage {
    fn update(&mut self, bytes: impl AsRef<[u8]>) {
        self.0.extend_from_slice(bytes.as_ref());
    }
}

impl FrameSink for Preimage {
    fn append(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }
}

fn frame(digest: &mut impl FrameSink, bytes: &[u8]) {
    digest.append(&(bytes.len() as u64).to_be_bytes());
    digest.append(bytes);
}

fn prefixed_sha256(bytes: &[u8]) -> String {
    format!(
        "sha256:{}",
        crate::diagnostics::certificate::sha256_hex(bytes)
    )
}

/// Identity of the compiler source set that implements parsing, security
/// analysis, package resolution, certificates, and Wasm emission. The list is
/// explicit so adding/removing a compiler input is a reviewable protocol edit.
const COMPILER_ID_INPUTS: &[(&str, &[u8])] = &[
    (
        "workspace/Cargo.toml",
        include_bytes!("../../../Cargo.toml"),
    ),
    (
        "workspace/Cargo.lock",
        include_bytes!("../../../Cargo.lock"),
    ),
    ("Cargo.toml", include_bytes!("../Cargo.toml")),
    ("build.rs", include_bytes!("../build.rs")),
    (
        "dependency/sigil-abi/Cargo.toml",
        include_bytes!("../../sigil-abi/Cargo.toml"),
    ),
    (
        "dependency/sigil-abi/src/lib.rs",
        include_bytes!("../../sigil-abi/src/lib.rs"),
    ),
    (
        "dependency/sigil-abi/src/host_contract.rs",
        include_bytes!("../../sigil-abi/src/host_contract.rs"),
    ),
    ("src/air.rs", include_bytes!("air.rs")),
    (
        "src/air_capability_v2/collector.rs",
        include_bytes!("air_capability_v2/collector.rs"),
    ),
    (
        "src/air_capability_v2/mod.rs",
        include_bytes!("air_capability_v2/mod.rs"),
    ),
    (
        "src/air_capability_v2/obligations.rs",
        include_bytes!("air_capability_v2/obligations.rs"),
    ),
    ("src/ambient_stdlib.rs", include_bytes!("ambient_stdlib.rs")),
    ("src/ast.rs", include_bytes!("ast.rs")),
    ("src/capability.rs", include_bytes!("capability.rs")),
    ("src/compiler.rs", include_bytes!("compiler.rs")),
    (
        "src/compiler_context.rs",
        include_bytes!("compiler_context.rs"),
    ),
    (
        "src/diagnostics/certificate.rs",
        include_bytes!("diagnostics/certificate.rs"),
    ),
    (
        "src/diagnostics/codes.rs",
        include_bytes!("diagnostics/codes.rs"),
    ),
    (
        "src/diagnostics/json.rs",
        include_bytes!("diagnostics/json.rs"),
    ),
    (
        "src/diagnostics/mod.rs",
        include_bytes!("diagnostics/mod.rs"),
    ),
    (
        "src/diagnostics/registry.rs",
        include_bytes!("diagnostics/registry.rs"),
    ),
    ("src/effect_check.rs", include_bytes!("effect_check.rs")),
    ("src/effect_desugar.rs", include_bytes!("effect_desugar.rs")),
    ("src/formal.rs", include_bytes!("formal.rs")),
    (
        "src/formal_projection.rs",
        include_bytes!("formal_projection.rs"),
    ),
    ("src/formal_v9.rs", include_bytes!("formal_v9.rs")),
    ("src/fuel.rs", include_bytes!("fuel.rs")),
    ("src/lexer.rs", include_bytes!("lexer.rs")),
    ("src/lib.rs", include_bytes!("lib.rs")),
    ("src/memory.rs", include_bytes!("memory.rs")),
    (
        "src/name_resolution.rs",
        include_bytes!("name_resolution.rs"),
    ),
    ("src/ownership.rs", include_bytes!("ownership.rs")),
    ("src/package.rs", include_bytes!("package.rs")),
    ("src/parser.rs", include_bytes!("parser.rs")),
    ("src/parser/limits.rs", include_bytes!("parser/limits.rs")),
    ("src/registries.rs", include_bytes!("registries.rs")),
    ("src/ring_check.rs", include_bytes!("ring_check.rs")),
    ("src/source.rs", include_bytes!("source.rs")),
    ("src/span.rs", include_bytes!("span.rs")),
    ("src/taint_check.rs", include_bytes!("taint_check.rs")),
    ("src/trace.rs", include_bytes!("trace.rs")),
    (
        "src/type_check/call_resolve.rs",
        include_bytes!("type_check/call_resolve.rs"),
    ),
    (
        "src/type_check/capability_tc.rs",
        include_bytes!("type_check/capability_tc.rs"),
    ),
    (
        "src/type_check/effect_infer.rs",
        include_bytes!("type_check/effect_infer.rs"),
    ),
    (
        "src/type_check/expressions.rs",
        include_bytes!("type_check/expressions.rs"),
    ),
    (
        "src/type_check/expressions/calls.rs",
        include_bytes!("type_check/expressions/calls.rs"),
    ),
    (
        "src/type_check/expressions/intrinsics.rs",
        include_bytes!("type_check/expressions/intrinsics.rs"),
    ),
    (
        "src/type_check/expressions/methods.rs",
        include_bytes!("type_check/expressions/methods.rs"),
    ),
    ("src/type_check/mod.rs", include_bytes!("type_check/mod.rs")),
    (
        "src/type_check/refinement.rs",
        include_bytes!("type_check/refinement.rs"),
    ),
    (
        "src/type_check/residual.rs",
        include_bytes!("type_check/residual.rs"),
    ),
    (
        "src/type_check/resolve.rs",
        include_bytes!("type_check/resolve.rs"),
    ),
    (
        "src/type_check/statements.rs",
        include_bytes!("type_check/statements.rs"),
    ),
    (
        "src/type_check/tests.rs",
        include_bytes!("type_check/tests.rs"),
    ),
    (
        "src/type_check/traits.rs",
        include_bytes!("type_check/traits.rs"),
    ),
    (
        "src/type_check/types.rs",
        include_bytes!("type_check/types.rs"),
    ),
    (
        "src/type_check/universe.rs",
        include_bytes!("type_check/universe.rs"),
    ),
    (
        "src/type_check/validators.rs",
        include_bytes!("type_check/validators.rs"),
    ),
    (
        "src/type_check_v2/mod.rs",
        include_bytes!("type_check_v2/mod.rs"),
    ),
    (
        "src/type_check_v2/obligations.rs",
        include_bytes!("type_check_v2/obligations.rs"),
    ),
    (
        "src/type_check_v2/refinement.rs",
        include_bytes!("type_check_v2/refinement.rs"),
    ),
    ("src/typed_ast.rs", include_bytes!("typed_ast.rs")),
    ("src/wasm.rs", include_bytes!("wasm.rs")),
    ("src/z3_cache.rs", include_bytes!("z3_cache.rs")),
    ("src/z3_capability.rs", include_bytes!("z3_capability.rs")),
    (
        "src/z3_fragment_guard.rs",
        include_bytes!("z3_fragment_guard.rs"),
    ),
];

pub fn compiler_identity_hash() -> String {
    compiler_identity_hash_with_features(env!("SIGIL_COMPILER_FEATURES"))
}

fn compiler_identity_hash_with_features(features: &str) -> String {
    let mut digest = Sha256::new();
    digest.update(COMPILER_ID_DOMAIN);
    for (path, bytes) in COMPILER_ID_INPUTS {
        frame(&mut digest, path.as_bytes());
        frame(&mut digest, bytes);
    }
    frame(&mut digest, b"build/rustc");
    frame(&mut digest, env!("SIGIL_RUSTC_IDENTITY").as_bytes());
    frame(&mut digest, b"build/target-profile");
    frame(&mut digest, env!("SIGIL_BUILD_IDENTITY").as_bytes());
    frame(&mut digest, b"build/features");
    frame(&mut digest, features.as_bytes());
    frame(&mut digest, b"build/native-z3");
    frame(&mut digest, env!("SIGIL_Z3_IDENTITY").as_bytes());
    frame(&mut digest, b"build/native-formal-checker");
    frame(
        &mut digest,
        crate::formal::checker_source_fingerprint().as_bytes(),
    );
    frame(&mut digest, b"build/lean-toolchain");
    frame(
        &mut digest,
        include_bytes!("../../../proofs/lean/lean-toolchain"),
    );
    format!("sha256:{:x}", digest.finalize())
}

#[cfg(test)]
mod compiler_identity_coverage_tests {
    use super::{COMPILER_ID_INPUTS, compiler_identity_hash_with_features};
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    fn rust_sources(root: &Path, current: &Path, paths: &mut BTreeSet<String>) {
        let mut entries: Vec<_> = std::fs::read_dir(current)
            .expect("compiler source directory is readable")
            .map(Result::unwrap)
            .collect();
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            if entry
                .file_type()
                .expect("dirent in the compiler's own source tree reports its type")
                .is_dir()
            {
                rust_sources(root, &path, paths);
            } else if path.extension().and_then(|value| value.to_str()) == Some("rs") {
                paths.insert(
                    path.strip_prefix(root)
                        .expect("walked path is under the root it was walked from")
                        .to_string_lossy()
                        .replace('\\', "/"),
                );
            }
        }
    }

    #[test]
    fn compiler_identity_covers_every_compiler_source_exactly_once() {
        let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mut observed = BTreeSet::from([
            "workspace/Cargo.toml".to_owned(),
            "workspace/Cargo.lock".to_owned(),
            "Cargo.toml".to_owned(),
            "build.rs".to_owned(),
            "dependency/sigil-abi/Cargo.toml".to_owned(),
            "dependency/sigil-abi/src/lib.rs".to_owned(),
            "dependency/sigil-abi/src/host_contract.rs".to_owned(),
        ]);
        rust_sources(&manifest, &manifest.join("src"), &mut observed);
        let declared: BTreeSet<String> = COMPILER_ID_INPUTS
            .iter()
            .map(|(path, _)| (*path).to_owned())
            .collect();
        assert_eq!(
            declared.len(),
            COMPILER_ID_INPUTS.len(),
            "duplicate identity input"
        );
        assert_eq!(
            declared, observed,
            "compiler identity source coverage drift"
        );
    }

    #[test]
    fn solver_feature_flip_changes_compiler_identity() {
        let current = env!("SIGIL_COMPILER_FEATURES");
        let flipped = if current.split(',').any(|feature| feature == "solver") {
            current
                .split(',')
                .filter(|feature| *feature != "solver")
                .collect::<Vec<_>>()
                .join(",")
        } else if current.is_empty() {
            "solver".to_owned()
        } else {
            format!("{current},solver")
        };
        assert_ne!(
            compiler_identity_hash_with_features(current),
            compiler_identity_hash_with_features(&flipped)
        );
    }
}

/// Exact identity of every compiler-coupled ambient stdlib source, independent
/// of host paths and filesystem state.
pub fn compiler_stdlib_hash() -> String {
    let mut digest = Sha256::new();
    digest.update(b"SIGIL-COMPILER-STDLIB\0V1\0");
    for (path, source) in crate::ambient_stdlib::all_module_sources() {
        frame(&mut digest, path.as_bytes());
        frame(&mut digest, normalize_source(source).as_bytes());
    }
    format!("sha256:{:x}", digest.finalize())
}

fn empty_derived_facts() -> PackageDerivedFactsJson {
    PackageDerivedFactsJson {
        rings: Vec::new(),
        effects: Vec::new(),
        host_imports: Vec::new(),
        grant_categories: Vec::new(),
        taint_contracts: Vec::new(),
        taint_contract_hash: prefixed_sha256(b"[]"),
        trusted_surface: Vec::new(),
        package_imports: Vec::new(),
        ambient_imports: Vec::new(),
    }
}

fn bind_and_validate_claims(
    compilation: &Compilation,
    graph: &mut ResolvedPackageGraph,
) -> Result<(), PackageError> {
    let mut module_to_package = BTreeMap::new();
    for node in &graph.certificate_nodes {
        for module in &node.modules {
            module_to_package.insert(module.clone(), node.package.clone());
        }
    }

    if !graph
        .sources
        .iter()
        .any(|source| source.package == graph.root_package)
    {
        return Err(PackageError::new(
            "E_MANIFEST",
            "root package has no source modules",
        ));
    }

    let mut facts: BTreeMap<String, PackageDerivedFactsJson> = graph
        .certificate_nodes
        .iter()
        .map(|node| (node.package.clone(), empty_derived_facts()))
        .collect();
    let direct_dependencies: BTreeMap<String, BTreeSet<String>> = graph
        .certificate_nodes
        .iter()
        .map(|node| {
            (
                node.package.clone(),
                node.dependencies.iter().cloned().collect(),
            )
        })
        .collect();
    let known_ambient: BTreeSet<String> = crate::ambient_stdlib::all_module_names()
        .into_iter()
        .map(str::to_owned)
        .collect();
    let mut ambient = empty_derived_facts();
    let mut selected_ambient = BTreeSet::new();

    for module in &compilation.ast.modules {
        let owner = module_to_package.get(&module.name).cloned();
        let is_ambient = owner.is_none() && known_ambient.contains(&module.name);
        if owner.is_none() && !is_ambient {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!("compiler emitted unowned package module `{}`", module.name),
            ));
        }
        if is_ambient {
            selected_ambient.insert(module.name.clone());
        }
        let derived = match &owner {
            Some(identity) => facts
                .get_mut(identity)
                .expect("module owner is a graph node"),
            None => &mut ambient,
        };
        let ring = match (module.ring, module.trusted) {
            (Ring::Inner, _) => "inner",
            (Ring::Outer, false) => "outer",
            (Ring::Outer, true) => "trusted_outer",
        };
        derived.rings.push(ring.to_owned());
        if module.ring == Ring::Outer || module.trusted {
            derived
                .trusted_surface
                .push(format!("module:{}", module.name));
        }
        for item in &module.items {
            match item {
                Item::UseDecl(import) => {
                    let target = import.path.segments.last().ok_or_else(|| {
                        PackageError::new("E_DEP_EDGE", "empty resolved import path")
                    })?;
                    if known_ambient.contains(target) {
                        derived.ambient_imports.push(target.clone());
                    } else if let Some(target_owner) = module_to_package.get(target) {
                        match &owner {
                            Some(source_owner) if source_owner == target_owner => {}
                            Some(source_owner)
                                if direct_dependencies[source_owner].contains(target_owner) =>
                            {
                                derived.package_imports.push(target_owner.clone());
                            }
                            Some(source_owner) => {
                                return Err(PackageError::new(
                                    "E_DEP_EDGE",
                                    format!(
                                        "module `{}` in `{source_owner}` imports `{target}` from `{target_owner}`, which is not a direct declared dependency",
                                        module.name
                                    ),
                                ));
                            }
                            None => {
                                return Err(PackageError::new(
                                    "E_DEP_EDGE",
                                    format!(
                                        "ambient stdlib module `{}` must not import package module `{target}`",
                                        module.name
                                    ),
                                ));
                            }
                        }
                    }
                }
                Item::FnDef(function) => {
                    if let Some(effects) = &function.effects {
                        let row_variables = crate::ast::effect_row_param_names(function);
                        derived.effects.extend(
                            effects
                                .iter()
                                .filter(|effect| !row_variables.contains(*effect))
                                .cloned(),
                        );
                    }
                    if function.visibility == Visibility::Public {
                        derived.taint_contracts.push(function_taint_contract(
                            &module.name,
                            &function.name,
                            &function.params,
                            function.ret_taint,
                            function.ret_flow,
                        ));
                    }
                }
                Item::ExternFnDecl(extern_fn) => {
                    derived.effects.extend(extern_fn.effects.iter().cloned());
                    derived
                        .host_imports
                        .push(format!("{}::{}", extern_fn.abi, extern_fn.name));
                    derived
                        .trusted_surface
                        .push(format!("extern:{}::{}", module.name, extern_fn.name));
                    derived.taint_contracts.push(function_taint_contract(
                        &module.name,
                        &extern_fn.name,
                        &extern_fn.params,
                        extern_fn.ret_taint,
                        false,
                    ));
                }
                Item::ImplDef(implementation) => {
                    for method in &implementation.methods {
                        if let Some(effects) = &method.effects {
                            derived.effects.extend(effects.iter().cloned());
                        }
                        if method.visibility == Visibility::Public {
                            derived.taint_contracts.push(function_taint_contract(
                                &module.name,
                                &method.name,
                                &method.params,
                                method.ret_taint,
                                method.ret_flow,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Typed functions are the authority for inferred closure effects,
    // monomorphized effect-row bindings, actor internals (if a future package
    // mode admits them), and every other effect the surface AST can omit.
    for module in &compilation.typed.modules {
        let owner = module_to_package.get(&module.name);
        let derived = match owner {
            Some(identity) => facts
                .get_mut(identity)
                .expect("typed module owner is a graph node"),
            None if known_ambient.contains(&module.name) => &mut ambient,
            None => {
                return Err(PackageError::new(
                    "E_MANIFEST",
                    format!("compiler typed unowned package module `{}`", module.name),
                ));
            }
        };
        for function in &module.functions {
            derived
                .effects
                .extend(function.effects.effects.iter().filter_map(|id| {
                    compilation
                        .typed
                        .effect_registry
                        .name_of(*id)
                        .map(str::to_owned)
                }));
        }
    }

    for derived in facts.values_mut().chain(std::iter::once(&mut ambient)) {
        sort_dedup(&mut derived.rings);
        sort_dedup(&mut derived.effects);
        sort_dedup(&mut derived.host_imports);
        sort_dedup(&mut derived.taint_contracts);
        sort_dedup(&mut derived.trusted_surface);
        sort_dedup(&mut derived.package_imports);
        sort_dedup(&mut derived.ambient_imports);
        derived.grant_categories = derive_grants(&derived.effects, &derived.host_imports);
        derived.taint_contract_hash =
            prefixed_sha256(canonical_string_array(&derived.taint_contracts).as_bytes());
    }

    let conserved_effects: BTreeSet<String> = facts
        .values()
        .chain(std::iter::once(&ambient))
        .flat_map(|derived| derived.effects.iter().cloned())
        .collect();
    let authoritative_effects: BTreeSet<String> =
        compilation.effects_required.iter().cloned().collect();
    if conserved_effects != authoritative_effects {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!(
                "compiler-derived effect partition is not conservative: partition={conserved_effects:?}, whole_program={authoritative_effects:?}"
            ),
        ));
    }

    // Reload manifests only through the source-bound data is intentionally not
    // possible here: `load_locked_package` already parsed them and bound their
    // exact hashes, but did not retain claims publicly. Re-read from graph is
    // avoided by storing the validated claims alongside the private resolver.
    // The claim comparison is performed in `validate_claims_from_sources`.
    validate_claims_from_sources(graph, &facts)?;
    for node in &mut graph.certificate_nodes {
        node.derived = facts.remove(&node.package).expect("one fact set per node");
    }
    graph.ambient_stdlib = AmbientStdlibCertificateJson {
        modules: selected_ambient.into_iter().collect(),
        derived: ambient,
    };
    Ok(())
}

fn graph_resource_evidence_hash(graph: &ResolvedPackageGraph, compilation: &Compilation) -> String {
    let resource = serde_json::json!({
        "package_graph_hash": graph.graph_hash,
        "composed_source_framing_hash": graph.source_framing_hash,
        "fuel_budget": compilation.fuel_budget,
        "wasm_inner_bytes": compilation.wasm_inner.len(),
        "wasm_outer_bytes": compilation.wasm_outer.as_ref().map(Vec::len),
    });
    prefixed_sha256(
        &serde_json::to_vec(&resource).expect("graph resource evidence JSON is serializable"),
    )
}

fn validate_claims_from_sources(
    graph: &ResolvedPackageGraph,
    facts: &BTreeMap<String, PackageDerivedFactsJson>,
) -> Result<(), PackageError> {
    for (identity, actual) in facts {
        let declared = &graph.claims[identity];
        compare_claim(identity, "rings", &declared.rings, &actual.rings)?;
        compare_claim(identity, "effects", &declared.effects, &actual.effects)?;
        compare_claim(
            identity,
            "host_imports",
            &declared.host_imports,
            &actual.host_imports,
        )?;
        compare_claim(
            identity,
            "grant_categories",
            &declared.grant_categories,
            &actual.grant_categories,
        )?;
        compare_claim(
            identity,
            "taint_contracts",
            &declared.taint_contracts,
            &actual.taint_contracts,
        )?;
        compare_claim(
            identity,
            "trusted_surface",
            &declared.trusted_surface,
            &actual.trusted_surface,
        )?;
        let provably_pure = actual.rings == ["inner"]
            && actual.effects.is_empty()
            && actual.host_imports.is_empty()
            && actual.grant_categories.is_empty()
            && actual.trusted_surface.is_empty();
        if declared.determinism == "pure" && !provably_pure {
            return Err(PackageError::new(
                "E_MANIFEST",
                format!(
                    "manifest for `{identity}` claims pure determinism but derived facts contradict it"
                ),
            ));
        }
    }
    Ok(())
}

fn compare_claim(
    identity: &str,
    field: &str,
    declared: &[String],
    actual: &[String],
) -> Result<(), PackageError> {
    if declared != actual {
        return Err(PackageError::new(
            "E_MANIFEST",
            format!(
                "manifest claim `{field}` for `{identity}` differs from compiler-derived facts: declared={declared:?}, derived={actual:?}"
            ),
        ));
    }
    Ok(())
}

fn function_taint_contract(
    module: &str,
    name: &str,
    params: &[crate::ast::Param],
    ret_taint: Option<TaintLabel>,
    ret_flow: bool,
) -> String {
    let params = params
        .iter()
        .map(|param| {
            let label = if param.flow {
                "Flow"
            } else {
                taint_name(param.taint.unwrap_or_default())
            };
            format!("{}:{label}", param.name)
        })
        .collect::<Vec<_>>()
        .join(",");
    let result = if ret_flow {
        "Flow"
    } else {
        taint_name(ret_taint.unwrap_or_default())
    };
    format!("{module}::{name}({params})->{result}")
}

fn taint_name(taint: TaintLabel) -> &'static str {
    match taint {
        TaintLabel::Public => "Public",
        TaintLabel::Internal => "Internal",
        TaintLabel::Secret => "Secret",
        TaintLabel::SecretCT => "SecretCT",
    }
}

fn derive_grants(effects: &[String], imports: &[String]) -> Vec<String> {
    let mut grants = BTreeSet::new();
    for effect in effects {
        match effect.as_str() {
            "FsIO" => {
                grants.insert("filesystem".to_owned());
            }
            "NetIO" => {
                grants.insert("network".to_owned());
            }
            "Time" => {
                grants.insert("time".to_owned());
            }
            "Random" => {
                grants.insert("random".to_owned());
            }
            "KvRead" | "KvWrite" => {
                grants.insert("key_value".to_owned());
            }
            "FFI" | "Unsafe" => {
                grants.insert("ffi".to_owned());
            }
            _ => {}
        }
    }
    if !imports.is_empty() {
        grants.insert("ffi".to_owned());
    }
    grants.into_iter().collect()
}

fn sort_dedup(values: &mut Vec<String>) {
    values.sort();
    values.dedup();
}

#[cfg(test)]
mod package_resource_limit_tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn retained_root_descriptor_resists_path_substitution() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("test tempdir");
        let root = temp.path().join("package");
        let outside = temp.path().join("outside");
        fs::create_dir(&root).expect("test dir setup");
        fs::create_dir(&outside).expect("test dir setup");
        fs::write(root.join("probe"), b"trusted").expect("test file setup");
        fs::write(outside.join("probe"), b"substituted").expect("test file setup");

        let opened =
            PackageDirectory::open_root(&root).expect("package root opens before the swap");
        fs::rename(&root, temp.path().join("original-package")).expect("test rename");
        symlink(&outside, &root).expect("test symlink");

        assert_eq!(
            opened
                .read_regular_file(Path::new("probe"), 64, "E_MANIFEST")
                .expect("probe reads through the held descriptor"),
            b"trusted"
        );
    }

    #[cfg(unix)]
    #[test]
    fn retained_vendor_descriptor_resists_path_substitution() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("test tempdir");
        let root = temp.path().join("package");
        let vendor = root.join("vendor");
        let outside = temp.path().join("outside-vendor");
        fs::create_dir_all(vendor.join("helper")).expect("test dir setup");
        fs::create_dir_all(outside.join("helper")).expect("test dir setup");
        fs::write(vendor.join("helper/probe"), b"trusted").expect("test file setup");
        fs::write(outside.join("helper/probe"), b"substituted").expect("test file setup");

        let opened_root =
            PackageDirectory::open_root(&root).expect("package root opens before the swap");
        let opened_vendor = opened_root
            .open_directory(Path::new("vendor"), "E_OFFLINE_MISS")
            .expect("vendor dir opens before the swap");
        fs::rename(&vendor, root.join("original-vendor")).expect("test rename");
        symlink(&outside, &vendor).expect("test symlink");

        let helper = opened_vendor
            .open_directory(Path::new("helper"), "E_OFFLINE_MISS")
            .expect("probe reads through the held descriptor");
        assert_eq!(
            helper
                .read_regular_file(Path::new("probe"), 64, "E_OFFLINE_MISS")
                .expect("probe reads through the held descriptor"),
            b"trusted"
        );
    }

    #[test]
    fn dependency_depth_limit_fails_without_stack_overflow() {
        let mut owned = Vec::new();
        for index in 0..=MAX_DEPENDENCY_DEPTH + 1 {
            let package = format!("aa/n{index:03}");
            let dependencies = if index <= MAX_DEPENDENCY_DEPTH {
                vec![format!("aa/n{:03}", index + 1)]
            } else {
                Vec::new()
            };
            owned.push(LockNode {
                package,
                version: "1.0.0".to_owned(),
                source: LockSource {
                    kind: "workspace".to_owned(),
                    locator: ".".to_owned(),
                },
                manifest_hash: format!("sha256:{}", "a".repeat(64)),
                content_hash: format!("sha256:{}", "b".repeat(64)),
                features: Vec::new(),
                modules: vec!["module".to_owned()],
                dependencies,
                yanked_observed: false,
            });
        }
        let nodes: BTreeMap<String, &LockNode> = owned
            .iter()
            .map(|node| (node.package.clone(), node))
            .collect();
        let error = canonical_dependency_order("aa/n000", &nodes).unwrap_err();
        assert_eq!(error.code, "E_RESOURCE_LIMIT");
        assert!(error.message.contains("dependency depth"));
    }
}
