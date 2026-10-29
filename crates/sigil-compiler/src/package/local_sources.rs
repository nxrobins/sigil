//! Explicit local source selection for feature-free package graphs. Source pins
//! remain authoritative; dependency materialization never overwrites files and
//! lock publication retains the parent's descriptor-anchored, create-new guard.
//! This developer workflow does not admit a package or authenticate a publisher.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use super::{
    COMPILER_VERSION, LOCK_FILE, LoadedPackage, LockNode, LockResolver, LockSource, Lockfile,
    MANIFEST_FILE, MAX_JSON_BYTES, MAX_PACKAGE_NODES, MAX_PACKAGE_SOURCES, MAX_TOTAL_SOURCE_BYTES,
    Manifest, PackageDirectory, PackageError, RESOLVER_CONTRACT, canonical_dependency_order,
    canonical_manifest_hash, compiler_requirement_matches, compiler_stdlib_hash,
    load_module_sources, package_content_hash, package_graph_hash, package_id, parse_json,
    preflight_manifest_graph, validate_lock_shape, validate_locked_resolution,
    validate_manifest_shape,
};

/// A caller-selected local dependency, not ambient package discovery. The
/// package id must match the selected manifest and every incoming content pin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalPackageDependency {
    pub package: String,
    pub path: PathBuf,
}

/// Materialize explicitly selected workspace dependencies and create a complete
/// offline lock. Initially supports non-optional, feature-free graphs only;
/// unsupported selection semantics fail closed rather than guessing features.
/// Existing locks and existing cache contents are never replaced. The root
/// manifest is not rewritten, so stale content pins remain observable failures.
pub fn create_local_package_lock_with_dependencies(
    root: &Path,
    dependencies: &[LocalPackageDependency],
) -> Result<Vec<u8>, PackageError> {
    let root = PackageDirectory::open_root(root)?;
    // UX preflight only. The final descriptor-relative O_EXCL create below is
    // the load-bearing protection against both leaf symlinks and races.
    if root.path.join(LOCK_FILE).symlink_metadata().is_ok() {
        return Err(PackageError::new(
            "E_LOCK_CREATE",
            "lockfile already exists",
        ));
    }
    if dependencies.len() >= MAX_PACKAGE_NODES {
        return Err(PackageError::new(
            "E_RESOURCE_LIMIT",
            "too many local sources",
        ));
    }
    let (_, root_package) = read_package(&root)?;
    let mut source_count = root_package.sources.len();
    let mut source_bytes: usize = root_package
        .sources
        .iter()
        .map(|source| source.text.len())
        .sum();
    let root_id = package_id(&root_package.manifest);
    let mut loaded = BTreeMap::from([(root_id.clone(), root_package)]);
    let mut snapshots = BTreeMap::new();
    for dependency in dependencies {
        if loaded.contains_key(&dependency.package) {
            return Err(PackageError::new(
                "E_SOURCE_CONFLICT",
                "duplicate local package id",
            ));
        }
        let directory = PackageDirectory::open_root(&dependency.path)?;
        let (manifest_bytes, package) = read_package(&directory)?;
        source_count += package.sources.len();
        source_bytes += package
            .sources
            .iter()
            .map(|source| source.text.len())
            .sum::<usize>();
        if source_count > MAX_PACKAGE_SOURCES || source_bytes > MAX_TOTAL_SOURCE_BYTES {
            return Err(PackageError::new(
                "E_RESOURCE_LIMIT",
                "local source graph exceeds package limits",
            ));
        }
        if package_id(&package.manifest) != dependency.package {
            return Err(PackageError::new(
                "E_SOURCE_CONFLICT",
                "selected package id differs from manifest",
            ));
        }
        snapshots.insert(dependency.package.clone(), manifest_bytes);
        loaded.insert(dependency.package.clone(), package);
    }
    if source_count > MAX_PACKAGE_SOURCES || source_bytes > MAX_TOTAL_SOURCE_BYTES {
        return Err(PackageError::new(
            "E_RESOURCE_LIMIT",
            "local source graph exceeds package limits",
        ));
    }
    let mut nodes = BTreeMap::new();
    for (identity, package) in &loaded {
        let manifest = &package.manifest;
        if !manifest.features.available.is_empty()
            || !manifest.features.default.is_empty()
            || manifest
                .dependencies
                .iter()
                .any(|dependency| dependency.optional || !dependency.features.is_empty())
        {
            return Err(PackageError::new(
                "E_MANIFEST",
                "local source selection requires non-optional, feature-free dependencies",
            ));
        }
        if !compiler_requirement_matches(&manifest.compiler.requires, COMPILER_VERSION) {
            return Err(PackageError::new(
                "E_MANIFEST",
                "selected package requires a different compiler",
            ));
        }
        let source = if identity == &root_id {
            LockSource {
                kind: "workspace".to_owned(),
                locator: ".".to_owned(),
            }
        } else {
            LockSource {
                kind: "workspace".to_owned(),
                locator: cache_locator(identity, &package.content_hash),
            }
        };
        let mut edges: Vec<String> = manifest
            .dependencies
            .iter()
            .map(|dependency| dependency.package.clone())
            .collect();
        edges.sort();
        nodes.insert(
            identity.clone(),
            LockNode {
                package: identity.clone(),
                version: manifest.version.clone(),
                source,
                manifest_hash: package.manifest_hash.clone(),
                content_hash: package.content_hash.clone(),
                features: Vec::new(),
                modules: manifest.modules.clone(),
                dependencies: edges,
                yanked_observed: false,
            },
        );
    }
    let references = nodes.iter().map(|(id, node)| (id.clone(), node)).collect();
    let order = canonical_dependency_order(&root_id, &references)?;
    if order.len() != nodes.len() {
        return Err(PackageError::new(
            "E_LOCK_DRIFT",
            "explicit sources include unreachable packages",
        ));
    }
    let ordered_nodes = order.iter().map(|id| nodes[id].clone()).collect::<Vec<_>>();
    let lock = Lockfile {
        format_version: "1".to_owned(),
        root: root_id.clone(),
        root_manifest_hash: loaded[&root_id].manifest_hash.clone(),
        resolver: LockResolver {
            contract: RESOLVER_CONTRACT.to_owned(),
            offline: true,
        },
        graph_hash: package_graph_hash(&ordered_nodes),
        stdlib_hash: compiler_stdlib_hash(),
        compiler_requires: loaded[&root_id].manifest.compiler.requires.clone(),
        nodes: ordered_nodes,
    };
    validate_lock_shape(&lock)?;
    preflight_manifest_graph(&lock, &references, &loaded)?;
    validate_locked_resolution(&lock, &references, &loaded)?;
    // Validate all source pins and graph semantics before publishing any cache
    // bytes. A dependency change is not silently repinned by a lock command.
    let bytes = serde_json::to_vec(&lock)
        .map_err(|error| PackageError::infrastructure("E_LOCK_DERIVATION", error.to_string()))?;
    if bytes.len() as u64 > MAX_JSON_BYTES {
        return Err(PackageError::new(
            "E_RESOURCE_LIMIT",
            "derived lock exceeds JSON limit",
        ));
    }
    for (identity, manifest_bytes) in snapshots {
        let package = &loaded[&identity];
        let directory = root.ensure_directory(Path::new(&nodes[&identity].source.locator))?;
        if directory
            .path
            .join(MANIFEST_FILE)
            .symlink_metadata()
            .is_ok()
        {
            let (_, cached) = read_package(&directory)?;
            if cached.manifest_hash != package.manifest_hash
                || cached.content_hash != package.content_hash
            {
                return Err(PackageError::new(
                    "E_HASH_MISMATCH",
                    "existing dependency cache differs from selected source",
                ));
            }
            continue;
        }
        let sources = directory.ensure_directory(Path::new("src"))?;
        for source in &package.sources {
            sources.create_regular_file(
                &format!("{}.sigil", source.module),
                source.text.as_bytes(),
                "E_LOCK_CREATE",
            )?;
        }
        directory.create_regular_file(MANIFEST_FILE, &manifest_bytes, "E_LOCK_CREATE")?;
    }
    root.create_regular_file(LOCK_FILE, &bytes, "E_LOCK_CREATE")?;
    Ok(bytes)
}

fn cache_locator(identity: &str, hash: &str) -> String {
    format!(
        ".sigil/deps/{identity}/{}",
        hash.strip_prefix("sha256:")
            .expect("package content hashes use the canonical prefix")
    )
}

fn read_package(directory: &PackageDirectory) -> Result<(Vec<u8>, LoadedPackage), PackageError> {
    let bytes =
        directory.read_regular_file(Path::new(MANIFEST_FILE), MAX_JSON_BYTES, "E_MANIFEST")?;
    let manifest: Manifest = parse_json(&bytes, MANIFEST_FILE)?;
    validate_manifest_shape(&manifest)?;
    let identity = package_id(&manifest);
    let sources = load_module_sources(directory, &identity, &manifest.modules)?;
    let manifest_hash = canonical_manifest_hash(&bytes)?;
    let content_hash = package_content_hash(&identity, &manifest.version, &bytes, &sources)?;
    Ok((
        bytes,
        LoadedPackage {
            manifest,
            manifest_hash,
            content_hash,
            sources,
        },
    ))
}

impl PackageDirectory {
    pub(super) fn ensure_directory(&self, relative: &Path) -> Result<Self, PackageError> {
        #[cfg(unix)]
        {
            use rustix::fs::{Mode, mkdirat};
            let relative = super::normalized_relative_path(&relative.to_string_lossy(), false)?;
            let mut directory = self.duplicate()?;
            for component in relative.components() {
                let std::path::Component::Normal(name) = component else {
                    return Err(PackageError::new(
                        "E_MANIFEST",
                        "cache path is not normalized",
                    ));
                };
                if let Err(error) =
                    mkdirat(&directory.fd, name, Mode::RUSR | Mode::WUSR | Mode::XUSR)
                    && error != rustix::io::Errno::EXIST
                {
                    return Err(PackageError::infrastructure(
                        "E_LOCK_CREATE",
                        error.to_string(),
                    ));
                }
                directory = directory.open_directory(Path::new(name), "E_LOCK_CREATE")?;
            }
            Ok(directory)
        }
        #[cfg(not(unix))]
        {
            let _ = relative;
            Err(PackageError::new(
                "E_UNSUPPORTED_PLATFORM",
                "secure dependency materialization is unavailable",
            ))
        }
    }
}
