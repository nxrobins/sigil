//! Explicit local package metadata, locking and create-new compiler evidence.
//! Refresh preserves old state; none of these commands judges or admits packages.

use crate::json_envelope::{self, Envelope, OutputFormat};
use serde_json::{Value, json};
use sigil_compiler::package::{
    LocalPackageDependency, compile_local_package_with_context, create_local_package_lock,
    create_local_package_lock_with_dependencies,
};
use sigil_compiler::{CompileOptions, CompilerContext};
use std::path::Path;

pub(super) fn emit(
    command: &'static str,
    fmt: OutputFormat,
    result: anyhow::Result<Value>,
) -> anyhow::Result<()> {
    match result {
        Ok(value) => {
            if fmt.is_json() {
                Envelope::ok(command, value).emit();
            } else {
                println!("{}", serde_json::to_string_pretty(&value)?);
            }
            Ok(())
        }
        Err(error) => {
            if fmt.is_json() {
                json_envelope::emit_generic_error(
                    command,
                    sigil_compiler::diagnostics::codes::R800,
                    error.to_string(),
                );
            }
            Err(error)
        }
    }
}

pub(crate) fn lock(
    root: &Path,
    dependencies: &[LocalPackageDependency],
    fmt: OutputFormat,
) -> anyhow::Result<()> {
    emit(
        "package-lock",
        fmt,
        (|| {
            let bytes = if dependencies.is_empty() {
                create_local_package_lock(root)?
            } else {
                create_local_package_lock_with_dependencies(root, dependencies)?
            };
            Ok(
                json!({"lockfile": root.join("sigil-package.lock.json"), "bytes": bytes.len(), "admission": "not_evaluated"}),
            )
        })(),
    )
}

pub(crate) fn refresh(root: &Path, fmt: OutputFormat) -> anyhow::Result<()> {
    emit(
        "package-refresh",
        fmt,
        (|| {
            let result = sigil_compiler::package::refresh_local_tool_package(root)?;
            Ok(
                json!({"root_package": result.root_package, "backup_directory": result.backup_directory,
            "package_graph_hash": result.graph_hash, "locked": true, "admission": "not_evaluated"}),
            )
        })(),
    )
}

pub(crate) fn evidence(
    root: &Path,
    output: &Path,
    fmt: OutputFormat,
    context: &CompilerContext,
) -> anyhow::Result<()> {
    emit(
        "package-evidence",
        fmt,
        (|| {
            // Output roots belong to the caller, never the package materialization.
            let source = root.canonicalize()?;
            let parent = output
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."))
                .canonicalize()?;
            let leaf = output
                .file_name()
                .ok_or_else(|| anyhow::anyhow!("output must name a new directory"))?;
            let target = parent.join(leaf);
            if target.starts_with(&source) || source.starts_with(&target) {
                anyhow::bail!("evidence output and package roots must be disjoint");
            }
            let package =
                compile_local_package_with_context(root, CompileOptions::default(), context)?;
            package.write_evidence_directory(&target)?;
            // The tier is the compilation's own witness, as in `sigil run`.
            Ok(
                json!({"output_dir": target, "proof_tier": package.proof_tier(), "admission": "not_evaluated"}),
            )
        })(),
    )
}
