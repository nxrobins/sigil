//! Explicit private-tool metadata refresh. Only root hashes change; locked
//! dependencies are revalidated, originals are preserved, and the lock is
//! published last. Interrupted multi-file publication fails closed, not atomic.

use std::path::{Path, PathBuf};

use super::PackageError;

/// A local refresh receipt, never compilation, admission or publisher approval.
#[derive(Debug)]
pub struct PackageRefresh {
    pub backup_directory: PathBuf,
    pub root_package: String,
    pub graph_hash: String,
}

/// Refresh only a starter-shaped, private bytes/fmt tool. This neither changes
/// dependency declarations nor repairs changed dependency caches. Existing state
/// is preserved under `.sigil/refresh`; failure during publication leaves the
/// guard and journal for inspection, never an automatically accepted new lock.
pub fn refresh_local_tool_package(root: &Path) -> Result<PackageRefresh, PackageError> {
    #[cfg(any(target_vendor = "apple", target_os = "linux", target_os = "android"))]
    {
        unix::refresh(root)
    }
    #[cfg(not(any(target_vendor = "apple", target_os = "linux", target_os = "android")))]
    {
        let _ = root;
        Err(PackageError::new(
            "E_UNSUPPORTED_PLATFORM",
            "secure package refresh is unavailable",
        ))
    }
}

#[cfg(any(target_vendor = "apple", target_os = "linux", target_os = "android"))]
mod unix {
    use std::collections::BTreeMap;
    use std::path::Path;
    use std::sync::atomic::{AtomicU64, Ordering};

    use rustix::fs::{AtFlags, Mode, RenameFlags, fsync, mkdirat, renameat_with, statat, unlinkat};
    use serde_json::{Value, json};

    use super::{PackageError, PackageRefresh};
    use crate::package::{
        LOCK_FILE, Lockfile, MANIFEST_FILE, MAX_JSON_BYTES, Manifest, PackageDirectory,
        canonical_manifest_hash, compiler_stdlib_hash, load_locked_snapshot, load_module_sources,
        package_content_hash, package_graph_hash, package_id, parse_json, prefixed_sha256,
        validate_lock_node, validate_lock_shape, validate_manifest_shape,
    };

    const INPUTS: [&str; 4] = ["API.md", "README.md", "api-card.json", "src/tool.sigil"];
    static SEQUENCE: AtomicU64 = AtomicU64::new(0);

    fn refuse(message: &str) -> PackageError {
        PackageError::new("E_LOCK_DRIFT", message)
    }

    fn io(error: impl std::fmt::Display) -> PackageError {
        PackageError::infrastructure("E_LOCK_CREATE", error.to_string())
    }

    fn encoded(value: &Value) -> Result<Vec<u8>, PackageError> {
        let mut bytes = serde_json::to_vec_pretty(value).map_err(io)?;
        bytes.push(b'\n');
        Ok(bytes)
    }

    fn read(directory: &PackageDirectory, name: &str) -> Result<Vec<u8>, PackageError> {
        directory.read_regular_file(Path::new(name), MAX_JSON_BYTES, "E_MANIFEST")
    }

    fn create_directory(
        parent: &PackageDirectory,
        name: &str,
    ) -> Result<PackageDirectory, PackageError> {
        mkdirat(&parent.fd, name, Mode::RWXU).map_err(io)?;
        fsync(&parent.fd).map_err(io)?;
        parent.open_directory(Path::new(name), "E_LOCK_CREATE")
    }

    fn move_new(
        from: &PackageDirectory,
        name: &str,
        to: &PackageDirectory,
    ) -> Result<(), PackageError> {
        // Descriptor-relative NOREPLACE preserves unexpected concurrent files;
        // there is no overwrite fallback on unsupported filesystems/platforms.
        renameat_with(&from.fd, name, &to.fd, name, RenameFlags::NOREPLACE).map_err(io)?;
        fsync(&from.fd).and_then(|()| fsync(&to.fd)).map_err(io)
    }

    struct Guard {
        directory: PackageDirectory,
        remove: bool,
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            if self.remove {
                // A failed removal leaves a conservative stale guard: subsequent
                // refresh refuses rather than guessing that a transaction ended.
                let _ = unlinkat(&self.directory.fd, "refresh.guard", AtFlags::empty());
            }
        }
    }

    fn derive(
        root: &PackageDirectory,
        old_bytes: &[u8],
        manifest_bytes: &[u8],
    ) -> Result<Vec<u8>, PackageError> {
        let mut lock: Lockfile = parse_json(old_bytes, LOCK_FILE)?;
        validate_lock_shape(&lock)?;
        for node in &lock.nodes {
            validate_lock_node(node)?;
        }
        if lock.graph_hash != package_graph_hash(&lock.nodes)
            || lock.stdlib_hash != compiler_stdlib_hash()
        {
            return Err(refuse("prior lock graph/stdlib identity is not intact"));
        }
        let manifest: Manifest = parse_json(manifest_bytes, MANIFEST_FILE)?;
        validate_manifest_shape(&manifest)?;
        if manifest.name != "tool"
            || manifest.modules != ["tool"]
            || manifest.maturity != "contracted"
            || !manifest.features.default.is_empty()
            || !manifest.features.available.is_empty()
            || !manifest.compiler.features.is_empty()
            || manifest.dependencies.len() != 2
            || lock.nodes.len() != 3
            || package_id(&manifest) != lock.root
            || manifest.compiler.requires != lock.compiler_requires
        {
            return Err(refuse(
                "refresh requires the existing private feature-free bytes/fmt tool profile",
            ));
        }
        let nodes: BTreeMap<_, _> = lock
            .nodes
            .iter()
            .map(|node| (node.package.as_str(), node))
            .collect();
        if nodes.len() != 3 {
            return Err(refuse("duplicate prior lock node"));
        }
        for package in ["sigil/bytes", "sigil/fmt"] {
            let node = nodes
                .get(package)
                .ok_or_else(|| refuse("missing prior bytes/fmt node"))?;
            let dependency = manifest
                .dependencies
                .iter()
                .find(|dep| dep.package == package)
                .ok_or_else(|| refuse("dependency selection changed"))?;
            let locator = format!(
                ".sigil/deps/{package}/{}",
                node.content_hash
                    .strip_prefix("sha256:")
                    .expect("validated hash")
            );
            if dependency.requirement != format!("={}", node.version)
                || dependency.content_hash != node.content_hash
                || dependency.source != "workspace"
                || dependency.optional
                || dependency.default_features
                || !dependency.features.is_empty()
                || node.source.kind != "workspace"
                || node.source.locator != locator
                || !node.dependencies.is_empty()
                || !node.features.is_empty()
                || node.yanked_observed
            {
                return Err(refuse(
                    "dependency declarations or locked selection changed; refresh never repins",
                ));
            }
        }
        let old_root = nodes
            .get(lock.root.as_str())
            .ok_or_else(|| refuse("missing prior root"))?;
        if old_root.version != manifest.version
            || old_root.modules != ["tool"]
            || old_root.source.kind != "workspace"
            || old_root.source.locator != "."
            || old_root.dependencies != ["sigil/bytes", "sigil/fmt"]
            || !old_root.features.is_empty()
            || old_root.yanked_observed
            || old_root.manifest_hash != lock.root_manifest_hash
        {
            return Err(refuse("root identity/version or dependency edges changed"));
        }
        let sources = load_module_sources(root, &lock.root, &manifest.modules)?;
        let hash = canonical_manifest_hash(manifest_bytes)?;
        let content =
            package_content_hash(&lock.root, &manifest.version, manifest_bytes, &sources)?;
        let identity = lock.root.clone();
        let node = lock
            .nodes
            .iter_mut()
            .find(|node| node.package == identity)
            .expect("root checked above");
        node.manifest_hash = hash.clone();
        node.content_hash = content;
        lock.root_manifest_hash = hash;
        lock.graph_hash = package_graph_hash(&lock.nodes);
        let bytes = serde_json::to_vec(&lock).map_err(io)?;
        // No drift switch enters the execution path. The proposed graph is
        // checked in full, including cached dependency bytes, before publication.
        load_locked_snapshot(root, &bytes, Some(manifest_bytes))?;
        Ok(bytes)
    }

    fn unchanged(
        root: &PackageDirectory,
        snapshot: &BTreeMap<String, Vec<u8>>,
    ) -> Result<(), PackageError> {
        for (name, bytes) in snapshot {
            if read(root, name)? != *bytes {
                return Err(refuse("project changed during refresh"));
            }
        }
        Ok(())
    }

    fn publish(
        root: &PackageDirectory,
        removed: &PackageDirectory,
        next: &PackageDirectory,
        managed: &[&str],
        snapshot: &BTreeMap<String, Vec<u8>>,
    ) -> Result<(), PackageError> {
        // Remove the lock first: partial publication is visibly non-runnable.
        // Every moved original survives, even if a non-cooperating writer raced.
        for name in
            std::iter::once(&LOCK_FILE).chain(managed.iter().filter(|name| **name != LOCK_FILE))
        {
            move_new(root, name, removed)?;
            if read(removed, name)? != snapshot[*name] {
                return Err(refuse(
                    "managed file changed during refresh; inspect preserved journal",
                ));
            }
        }
        for name in managed.iter().filter(|name| **name != LOCK_FILE) {
            move_new(next, name, root)?;
        }
        move_new(next, LOCK_FILE, root)
    }

    pub(super) fn refresh(path: &Path) -> Result<PackageRefresh, PackageError> {
        let root = PackageDirectory::open_root(path)?;
        let state = root.ensure_directory(Path::new(".sigil"))?;
        state.create_regular_file(
            "refresh.guard",
            b"Private root refresh in progress; inspect .sigil/refresh before recovery.\n",
            "E_LOCK_CREATE",
        )?;
        let mut guard = Guard {
            directory: state,
            remove: true,
        };
        let mut snapshot = BTreeMap::new();
        for name in INPUTS.into_iter().chain([MANIFEST_FILE, LOCK_FILE]) {
            snapshot.insert(name.to_owned(), read(&root, name)?);
        }
        let mut manifest: Value = parse_json(&snapshot[MANIFEST_FILE], MANIFEST_FILE)?;
        let typed_manifest: Manifest = parse_json(&snapshot[MANIFEST_FILE], MANIFEST_FILE)?;
        validate_manifest_shape(&typed_manifest)?;
        let inventory_name = match (
            statat(&root.fd, "starter-inputs.json", AtFlags::SYMLINK_NOFOLLOW),
            statat(&root.fd, "tool-inputs.json", AtFlags::SYMLINK_NOFOLLOW),
        ) {
            (Ok(_), Err(error)) if error == rustix::io::Errno::NOENT => "starter-inputs.json",
            (Err(error), Ok(_)) if error == rustix::io::Errno::NOENT => "tool-inputs.json",
            _ => {
                return Err(refuse(
                    "refresh requires exactly one starter-inputs.json or tool-inputs.json",
                ));
            }
        };
        let inventory_bytes = read(&root, inventory_name)?;
        if manifest["evidence"]["evidence_manifest_hash"] != prefixed_sha256(&inventory_bytes) {
            return Err(refuse(
                "inventory no longer matches the existing manifest reference",
            ));
        }
        let inventory: Value = parse_json(&inventory_bytes, inventory_name)?;
        let files = inventory["files"]
            .as_object()
            .ok_or_else(|| refuse("missing private input inventory"))?;
        if files.keys().map(String::as_str).collect::<Vec<_>>() != INPUTS
            || !inventory["scope"]
                .as_str()
                .is_some_and(|scope| scope.contains("not an admission evidence manifest"))
        {
            return Err(refuse(
                "unsupported inventory; refresh only manages the four private tool input files",
            ));
        }
        snapshot.insert(inventory_name.to_owned(), inventory_bytes);
        let files: BTreeMap<_, _> = INPUTS
            .iter()
            .map(|name| (*name, prefixed_sha256(&snapshot[*name])))
            .collect();
        let inventory = encoded(
            &json!({"scope": "private application inputs after explicit root refresh; not an admission evidence manifest", "files": files}),
        )?;
        for (key, name) in [
            ("charter_hash", "README.md"),
            ("api_contract_hash", "API.md"),
            ("api_card_hash", "api-card.json"),
        ] {
            manifest["evidence"][key] = json!(prefixed_sha256(&snapshot[name]));
        }
        manifest["evidence"]["evidence_manifest_hash"] = json!(prefixed_sha256(&inventory));
        let manifest = encoded(&manifest)?;
        let lock = derive(&root, &snapshot[LOCK_FILE], &manifest)?;
        if manifest == snapshot[MANIFEST_FILE]
            && inventory == snapshot[inventory_name]
            && lock == snapshot[LOCK_FILE]
        {
            return Err(refuse("nothing to refresh"));
        }
        let journals = guard.directory.ensure_directory(Path::new("refresh"))?;
        let journal = loop {
            let name = format!(
                "{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            );
            match mkdirat(&journals.fd, name.as_str(), Mode::RWXU) {
                Ok(()) => break journals.open_directory(Path::new(&name), "E_LOCK_CREATE")?,
                Err(error) if error == rustix::io::Errno::EXIST => continue,
                Err(error) => return Err(io(error)),
            }
        };
        // From here, any failure keeps the guard and all journal bytes. There
        // is no overwrite-based rollback or recursive cleanup that can eat edits.
        guard.remove = false;
        let backup_path = journal.path.clone();
        let result = (|| {
            let before = create_directory(&journal, "before")?;
            let source_dir = create_directory(&before, "src")?;
            for (name, bytes) in &snapshot {
                if name == "src/tool.sigil" {
                    source_dir.create_regular_file(
                        "tool.sigil.snapshot",
                        bytes,
                        "E_LOCK_CREATE",
                    )?;
                } else {
                    before.create_regular_file(
                        &format!("{name}.snapshot"),
                        bytes,
                        "E_LOCK_CREATE",
                    )?;
                }
            }
            let removed = create_directory(&journal, "removed")?;
            let next = create_directory(&journal, "next")?;
            let managed = [MANIFEST_FILE, inventory_name, LOCK_FILE];
            for (name, bytes) in [
                (MANIFEST_FILE, &manifest),
                (inventory_name, &inventory),
                (LOCK_FILE, &lock),
            ] {
                next.create_regular_file(name, bytes, "E_LOCK_CREATE")?;
            }
            for directory in [
                &source_dir,
                &before,
                &next,
                &removed,
                &journal,
                &journals,
                &guard.directory,
                &root,
            ] {
                fsync(&directory.fd).map_err(io)?;
            }
            unchanged(&root, &snapshot)?;
            if derive(&root, &snapshot[LOCK_FILE], &manifest)? != lock {
                return Err(refuse("inputs changed during derivation"));
            }
            journal.create_regular_file("receipt.json", &encoded(&json!({
            "scope": "before-refresh snapshot, including source already edited by caller; not admission or a pre-edit runnable version",
            "old_lock_hash": prefixed_sha256(&snapshot[LOCK_FILE]), "new_lock_hash": prefixed_sha256(&lock),
            "snapshot_files": snapshot.iter().map(|(name, bytes)| (name.clone(), json!({"path": format!("before/{name}.snapshot"), "hash": prefixed_sha256(bytes)}))).collect::<BTreeMap<_, _>>(),
            "managed_files": managed
        }))?, "E_LOCK_CREATE")?;
            fsync(&journal.fd).map_err(io)?;
            publish(&root, &removed, &next, &managed, &snapshot)?;
            // A racing editor can make the finished graph stale, never silently
            // accepted. Leave its journal/guard visible if the final strict load fails.
            for (name, bytes) in [
                (MANIFEST_FILE, &manifest),
                (inventory_name, &inventory),
                (LOCK_FILE, &lock),
            ] {
                if read(&root, name)? != *bytes {
                    return Err(refuse(
                        "published metadata changed; inspect refresh journal",
                    ));
                }
            }
            for name in INPUTS {
                if read(&root, name)? != snapshot[name] {
                    return Err(refuse("application inputs changed during publication"));
                }
            }
            let graph = load_locked_snapshot(&root, &lock, None)?;
            journal.create_regular_file(
                "complete",
                b"Metadata and root lock refreshed; no compilation or admission.\n",
                "E_LOCK_CREATE",
            )?;
            fsync(&journal.fd).map_err(io)?;
            Ok(PackageRefresh {
                backup_directory: journal.path,
                root_package: graph.root_package,
                graph_hash: graph.graph_hash,
            })
        })();
        match result {
            Ok(value) => {
                guard.remove = true;
                Ok(value)
            }
            Err(error) => Err(PackageError::infrastructure(
                "E_LOCK_CREATE",
                format!(
                    "refresh stopped; inspect preserved state in `{}` and .sigil/refresh.guard before recovery: {error}",
                    backup_path.display()
                ),
            )),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn fixture() -> (
            tempfile::TempDir,
            PackageDirectory,
            PackageDirectory,
            PackageDirectory,
            BTreeMap<String, Vec<u8>>,
        ) {
            let directory = tempfile::tempdir().expect("isolated refresh publication fixture");
            let root = PackageDirectory::open_root(directory.path()).expect("open root fixture");
            let removed =
                create_directory(&root, "removed").expect("create preserved-original directory");
            let next = create_directory(&root, "next").expect("create prepared metadata directory");
            let mut snapshot = BTreeMap::new();
            for name in [MANIFEST_FILE, "tool-inputs.json", LOCK_FILE] {
                root.create_regular_file(name, b"original", "E_LOCK_CREATE")
                    .expect("old managed file");
                next.create_regular_file(name, b"replacement", "E_LOCK_CREATE")
                    .expect("prepared replacement");
                snapshot.insert(name.to_owned(), b"original".to_vec());
            }
            (directory, root, removed, next, snapshot)
        }

        #[test]
        fn publication_never_overwrites_an_existing_preserved_file() {
            let (_directory, root, removed, next, snapshot) = fixture();
            removed
                .create_regular_file(LOCK_FILE, b"existing journal data", "E_LOCK_CREATE")
                .expect("collision witness");
            assert!(
                publish(
                    &root,
                    &removed,
                    &next,
                    &[MANIFEST_FILE, "tool-inputs.json", LOCK_FILE],
                    &snapshot
                )
                .is_err()
            );
            assert_eq!(
                read(&removed, LOCK_FILE).expect("preserved collision"),
                b"existing journal data"
            );
            for (name, bytes) in snapshot {
                assert_eq!(read(&root, &name).expect("root unchanged"), bytes);
            }
        }

        #[test]
        fn interrupted_publication_preserves_originals_without_a_new_lock() {
            let (_directory, root, removed, next, snapshot) = fixture();
            unlinkat(&next.fd, LOCK_FILE, AtFlags::empty())
                .expect("plant missing final staged lock");
            assert!(
                publish(
                    &root,
                    &removed,
                    &next,
                    &[MANIFEST_FILE, "tool-inputs.json", LOCK_FILE],
                    &snapshot
                )
                .is_err()
            );
            assert!(
                read(&root, LOCK_FILE).is_err(),
                "partial metadata must have no accepted lock"
            );
            for (name, bytes) in snapshot {
                assert_eq!(
                    read(&removed, &name).expect("moved original survives"),
                    bytes
                );
            }
            assert_eq!(
                read(&root, MANIFEST_FILE).expect("partial metadata is visible"),
                b"replacement"
            );
        }

        #[test]
        fn publication_keeps_hardlinked_originals_unchanged() {
            let (directory, root, removed, next, snapshot) = fixture();
            let alias = directory.path().join("user-owned-alias");
            std::fs::hard_link(directory.path().join(MANIFEST_FILE), &alias)
                .expect("old metadata alias");
            publish(
                &root,
                &removed,
                &next,
                &[MANIFEST_FILE, "tool-inputs.json", LOCK_FILE],
                &snapshot,
            )
            .expect("publish new leaf entries");
            assert_eq!(std::fs::read(alias).expect("alias preserved"), b"original");
            assert_eq!(
                read(&root, MANIFEST_FILE).expect("new file"),
                b"replacement"
            );
        }
    }
}
