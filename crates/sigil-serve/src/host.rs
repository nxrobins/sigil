//! The tool host: compiles every configured tool once at boot, then
//! executes them on demand. Each execution is a fresh ephemeral run —
//! `execute_ephemeral` caches the compiled wasm module internally, so
//! per-invocation cost is instantiate + run, not recompile.

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::{Context, bail};
use sigil_compiler::{CompilerContext, compile_tool_with_context};
use sigil_runtime::{IoGrants, ToolError, execute_ephemeral};

use crate::config::Config;

/// Effects the serve cert gate cross-checks against grants. The CLI
/// gates FsIO/NetIO; serve also owns the kv surface, so KvIO joins.
const SERVE_GATED_EFFECTS: &[&str] = &["FsIO", "NetIO", "KvIO"];

/// Mirror of the CLI's certificate gate for served tools: schema,
/// fresh-solver-verification (the cert's own bit is forgeable — see
/// the CLI's gate for the full argument), source + wasm fingerprints,
/// and the effects ⇄ grants cross-check derived from the tool's
/// CONFIGURED grants. Every failure is a boot error.
fn gate_tool_certificate(
    name: &str,
    cert_path: &std::path::Path,
    source: &str,
    compiled: &sigil_compiler::CompileResult,
    grants: &IoGrants,
) -> anyhow::Result<()> {
    use sigil_compiler::certificate::{
        ArtifactFingerprint, CERTIFICATE_SCHEMA_VERSION, CertificateJson,
    };

    let text = std::fs::read_to_string(cert_path).with_context(|| {
        format!(
            "tool `{name}`: failed to read certificate `{}`",
            cert_path.display()
        )
    })?;
    let cert: CertificateJson = serde_json::from_str(&text).with_context(|| {
        format!(
            "tool `{name}`: certificate `{}` is not valid JSON",
            cert_path.display()
        )
    })?;

    if cert.schema_version != CERTIFICATE_SCHEMA_VERSION {
        bail!(
            "tool `{name}`: certificate schema v{} unsupported (expected v{})",
            cert.schema_version,
            CERTIFICATE_SCHEMA_VERSION
        );
    }

    if cert.formal.as_ref() != Some(&compiled.formal_security_report) {
        bail!("tool `{name}`: formal security report or CSIR fingerprint mismatch (R819)");
    }

    let allow_unverified = std::env::var("SIGIL_ALLOW_UNVERIFIED_CERT").as_deref() == Ok("1");
    if !allow_unverified && !compiled.solver_verified {
        bail!(
            "tool `{name}`: this toolchain did not solver-verify the tool (fail closed;              set SIGIL_ALLOW_UNVERIFIED_CERT=1 to serve without solver verification, or              build sigil-serve with the `solver` feature)"
        );
    }

    let canonical = cert.canonical_source_bytes(source.as_bytes());
    let fresh_source = ArtifactFingerprint::new(&canonical);
    if cert.source_fingerprint.hash != fresh_source.hash
        || cert.source_fingerprint.bytes != fresh_source.bytes
    {
        bail!(
            "tool `{name}`: source fingerprint mismatch — cert {} ({} bytes), fresh {} ({} bytes)",
            cert.source_fingerprint.hash,
            cert.source_fingerprint.bytes,
            fresh_source.hash,
            fresh_source.bytes
        );
    }

    let fresh_inner = ArtifactFingerprint::new(&compiled.wasm_inner);
    if cert.wasm_inner_fingerprint.hash != fresh_inner.hash
        || cert.wasm_inner_fingerprint.bytes != fresh_inner.bytes
    {
        bail!(
            "tool `{name}`: wasm fingerprint mismatch — cert {} ({} bytes), fresh {} ({} bytes)",
            cert.wasm_inner_fingerprint.hash,
            cert.wasm_inner_fingerprint.bytes,
            fresh_inner.hash,
            fresh_inner.bytes
        );
    }
    match (&cert.wasm_outer_fingerprint, compiled.wasm_outer.as_deref()) {
        (Some(claimed), Some(bytes)) => {
            let fresh = ArtifactFingerprint::new(bytes);
            if claimed.hash != fresh.hash || claimed.bytes != fresh.bytes {
                bail!("tool `{name}`: outer wasm fingerprint mismatch");
            }
        }
        (Some(_), None) => {
            bail!("tool `{name}`: cert claims an outer wasm but the tool compiled none")
        }
        (None, Some(_)) => {
            bail!("tool `{name}`: tool compiled an outer wasm but the cert claims none")
        }
        (None, None) => {}
    }

    let runtime: std::collections::BTreeSet<&str> = SERVE_GATED_EFFECTS
        .iter()
        .copied()
        .filter(|effect| match *effect {
            "FsIO" => !grants.fs.is_empty() || !grants.fs_write.is_empty(),
            "NetIO" => !grants.net.is_empty(),
            "KvIO" => !grants.kv.is_empty() || !grants.kv_write.is_empty(),
            _ => false,
        })
        .collect();
    let claimed: std::collections::BTreeSet<&str> = cert
        .effects_required
        .iter()
        .map(String::as_str)
        .filter(|effect| SERVE_GATED_EFFECTS.contains(effect))
        .collect();
    let missing: Vec<&&str> = claimed.difference(&runtime).collect();
    let extra: Vec<&&str> = runtime.difference(&claimed).collect();
    if !missing.is_empty() || !extra.is_empty() {
        bail!(
            "tool `{name}`: cert effects and configured grants disagree —              cert requires {missing:?} without grants; grants supply {extra:?} the cert never claims"
        );
    }
    Ok(())
}

pub struct CompiledTool {
    pub wasm: Vec<u8>,
    pub fuel: u64,
    pub grants: IoGrants,
}

/// One execution's outcome, decoded from the runtime's conventions.
#[derive(Debug)]
pub enum ToolOutcome {
    /// The tool returned a packed pointer; these are its output bytes.
    Success(Vec<u8>),
    /// The tool returned a negative code (the `tool returned error (K)`
    /// trap sentinel). Value is the tool's own negative code, e.g.
    /// -404.
    ToolError(i64),
    /// The run failed outside the tool's control (fuel exhausted,
    /// genuine trap, missing entry point).
    HostError(String),
}

pub struct ToolHost {
    tools: BTreeMap<String, CompiledTool>,
}

impl ToolHost {
    /// Compile every tool in the config. Tool source paths resolve
    /// relative to `base_dir` (the config file's directory).
    pub fn from_config(config: &Config, base_dir: &Path) -> anyhow::Result<Self> {
        let context = match config.host_profile.as_deref() {
            None => CompilerContext::default(),
            Some(name) => CompilerContext::with_host_profile(
                sigil_runtime::host_profile_by_name(name).ok_or_else(|| {
                    anyhow::anyhow!(
                        "config: unknown host_profile `{name}` (the built-in host is `ephemeral`)"
                    )
                })?,
            ),
        };
        Self::from_config_with_context(config, base_dir, &context)
    }

    /// Compile and rederive under caller-selected declarations. They do not
    /// approve runtime bindings; the execution path independently checks Wasm.
    pub fn from_config_with_context(
        config: &Config,
        base_dir: &Path,
        context: &CompilerContext,
    ) -> anyhow::Result<Self> {
        let mut tools = BTreeMap::new();
        for (name, tool_config) in &config.tools {
            let source_path = if tool_config.source.is_absolute() {
                tool_config.source.clone()
            } else {
                base_dir.join(&tool_config.source)
            };
            let source = std::fs::read_to_string(&source_path).with_context(|| {
                format!(
                    "tool `{name}`: failed to read source `{}`",
                    source_path.display()
                )
            })?;
            let compiled = match compile_tool_with_context(&source, context) {
                Ok(result) => result,
                Err(err) => {
                    let codes: Vec<&str> = err
                        .diagnostics()
                        .iter()
                        .map(|d| d.code().as_str())
                        .collect();
                    bail!(
                        "tool `{name}` (`{}`) failed to compile: {} diagnostic(s) {:?}",
                        source_path.display(),
                        err.diagnostics().len(),
                        codes
                    );
                }
            };
            if tool_config.fuel == 0 {
                bail!("tool `{name}`: fuel budget must be positive");
            }
            let grants = tool_config.grants.to_io_grants(name)?;
            if let Some(cert) = &tool_config.cert {
                let cert_path = if cert.is_absolute() {
                    cert.clone()
                } else {
                    base_dir.join(cert)
                };
                gate_tool_certificate(name, &cert_path, &source, &compiled, &grants)?;
            }
            tools.insert(
                name.clone(),
                CompiledTool {
                    wasm: compiled.wasm,
                    fuel: tool_config.fuel,
                    grants,
                },
            );
        }
        Ok(Self { tools })
    }

    pub fn tool_names(&self) -> impl Iterator<Item = &str> {
        self.tools.keys().map(String::as_str)
    }

    /// Run `name` once with `input`. Panics never; every failure mode
    /// is a `ToolOutcome` variant the caller can map to its protocol.
    pub fn execute(&self, name: &str, input: &[u8]) -> ToolOutcome {
        let Some(tool) = self.tools.get(name) else {
            return ToolOutcome::HostError(format!("unknown tool `{name}`"));
        };
        match execute_ephemeral(&tool.wasm, input, tool.fuel, &tool.grants) {
            Ok(result) => ToolOutcome::Success(result.output),
            Err(ToolError::Trapped { message }) => match decode_sentinel(&message) {
                Some(code) => ToolOutcome::ToolError(code),
                None => ToolOutcome::HostError(format!("tool `{name}` trapped: {message}")),
            },
            Err(ToolError::FuelExhausted { consumed }) => ToolOutcome::HostError(format!(
                "tool `{name}` exhausted its fuel budget after {consumed} units"
            )),
            Err(other) => ToolOutcome::HostError(format!("tool `{name}` failed: {other}")),
        }
    }
}

/// Extract K from `tool returned error (K)` and return it as the
/// tool's negative code.
fn decode_sentinel(message: &str) -> Option<i64> {
    let start = message.find("tool returned error (")? + "tool returned error (".len();
    let end = start + message[start..].find(')')?;
    let magnitude: i64 = message[start..end].parse().ok()?;
    Some(-magnitude)
}
