//! Explicit Public-checkpoint import for a locked private storage consumer.
//! This host example never changes compiler labels or the normal package gate.

use anyhow::{Context, bail};
use serde_json::{Value, json};
use sigil_compiler::{
    CompileOptions, CompilerContext,
    ast::{Ring, TaintLabel},
    package::{PackageCompilation, compile_local_package_with_context},
    type_check::Type,
    typed_ast::TypedFunctionKind,
};
use sigil_runtime::{IoGrants, KvGrant, KvWriteGrant};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub const IMPORT_POLICY: &str = "operator-declared-public-checkpoints-v1";

fn options(arguments: &[String]) -> anyhow::Result<BTreeMap<String, String>> {
    let mut result = BTreeMap::new();
    let mut index = 0;
    while index < arguments.len() {
        let name = &arguments[index];
        if result.contains_key(name) {
            bail!("duplicate option: {name}");
        }
        let value = if name == "--allow-public-checkpoint-import" {
            String::new()
        } else if ["--package", "--input-hex", "--kv-read", "--kv-write"].contains(&name.as_str()) {
            index += 1;
            arguments
                .get(index)
                .context("missing option value")?
                .clone()
        } else {
            bail!("unknown option: {name}");
        };
        result.insert(name.clone(), value);
        index += 1;
    }
    // Fail before opening a package, store, or producing Internal output. The
    // decision belongs to the operator, never a field inside an untrusted blob.
    if !result.contains_key("--allow-public-checkpoint-import") {
        bail!("Public checkpoint import requires --allow-public-checkpoint-import");
    }
    Ok(result)
}

fn decode(input: &str) -> anyhow::Result<Vec<u8>> {
    if input.len() > 32792 || !input.len().is_multiple_of(2) {
        bail!("input must be bounded lowercase hexadecimal");
    }
    fn digit(byte: u8) -> anyhow::Result<u8> {
        match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => bail!("input must be bounded lowercase hexadecimal"),
        }
    }
    input
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok(16 * digit(pair[0])? + digit(pair[1])?))
        .collect()
}

pub fn require_storage_profile(package: &PackageCompilation) -> anyhow::Result<()> {
    // No legacy environment override: the current compilation is the witness.
    package.require_solver_verified()?;
    let compilation = &package.compilation;
    let root_tool =
        package.graph.root_package == "autoresearch-store/tool"
            && package.graph.sources.iter().any(|source| {
                source.package == package.graph.root_package && source.module == "tool"
            });
    let entry = compilation
        .typed
        .modules
        .iter()
        .find(|m| m.name == "tool")
        .and_then(|m| {
            m.functions
                .iter()
                .find(|f| f.export_name == "tool__tool_main")
        });
    let abi = entry.is_some_and(|entry| {
        entry.kind == TypedFunctionKind::ModuleFunction
            && entry.externally_callable
            && entry.captures.is_empty()
            && entry.ret == Type::I64
            && entry.ret_taint == TaintLabel::Internal
            && !entry.ret_flow
            && entry.params.len() == 2
            && entry
                .params
                .iter()
                .all(|p| p.ty == Type::I64 && p.taint == TaintLabel::Public && !p.flow)
    });
    let effects = compilation
        .effects_required
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if !root_tool
        || !abi
        || compilation.wasm_outer.is_none()
        || !compilation
            .typed
            .modules
            .iter()
            .all(|m| m.ring == Ring::Outer && m.trusted)
        || effects != BTreeSet::from(["Alloc", "FFI", "KvIO", "Unsafe"])
    {
        bail!("storage host requires the root-owned outer Internal-result storage profile");
    }
    Ok(())
}

pub fn run(arguments: &[String]) -> anyhow::Result<Value> {
    let options = options(arguments)?;
    let root = options.get("--package").context("--package is required")?;
    let input = decode(
        options
            .get("--input-hex")
            .context("--input-hex is required")?,
    )?;
    let context = CompilerContext::with_host_profile(sigil_runtime::ephemeral_host_profile());
    let package =
        compile_local_package_with_context(Path::new(root), CompileOptions::default(), &context)?;
    require_storage_profile(&package)?;
    let canonical = |name: &str| -> anyhow::Result<Option<PathBuf>> {
        options
            .get(name)
            .map(|path| {
                let path = Path::new(path)
                    .canonicalize()
                    .with_context(|| format!("grant root for {name}"))?;
                if !path.is_dir() {
                    bail!("grant root must be a directory");
                }
                Ok(path)
            })
            .transpose()
    };
    let read_root = canonical("--kv-read")?;
    let write_root = canonical("--kv-write")?;
    if let (Some(read), Some(write)) = (&read_root, &write_root)
        && read != write
    {
        bail!("read and write grants must name the same checkpoint store");
    }
    let grants = IoGrants {
        kv: read_root
            .into_iter()
            .map(|root| KvGrant {
                namespace: "autoresearch".to_owned(),
                root,
            })
            .collect(),
        kv_write: write_root
            .into_iter()
            .map(|root| KvWriteGrant {
                namespace: "autoresearch".to_owned(),
                root,
            })
            .collect(),
        ..IoGrants::none()
    };
    let output = sigil_runtime::execute_ephemeral_with_budgets(
        package
            .compilation
            .wasm_outer
            .as_deref()
            .context("profile requires outer artifact")?,
        &input,
        500_000,
        10_000_000,
        16 * 1024 * 1024,
        &grants,
    )?;
    if output.output.len() > 8192 {
        bail!("storage output exceeds the checkpoint bound");
    }
    Ok(json!({"status":"ok","data":{
        "output":output.output,"source_label":"Internal","result_label":"Public",
        "import_policy":IMPORT_POLICY,
        "storage_program":package.certificate().artifact_identity_hash,
    }}))
}

#[cfg(not(test))]
fn main() {
    match run(&std::env::args().skip(1).collect::<Vec<_>>()) {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("storage refused: {error}");
            std::process::exit(1);
        }
    }
}
