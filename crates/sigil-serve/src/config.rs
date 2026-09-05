//! Service configuration (JSON): tool definitions, HTTP routes,
//! schedule entries.
//!
//! Grant descriptors reuse the MCP envelope's conventions (`kv`:
//! `"NS=DIR"`, `time`: `"wall"`/`"frozen:<ms>"`, `random`:
//! `"secure"`/`"seeded:<u64>"`) with one deliberate difference: a
//! config file is operator intent, so malformed descriptors are BOOT
//! ERRORS here, not silently dropped grants.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use anyhow::{Context, bail};
use serde::Deserialize;
use sigil_runtime::{
    FsGrant, FsWriteGrant, HttpMethod, IoGrants, KvGrant, KvWriteGrant, NetGrant, RandomGrant,
    SecretGrant, TimeGrant,
};

/// Hard floor for schedule intervals — guards against a zero-interval
/// busy loop. Production configs should stay at or above 1000 ms; the
/// low floor exists so tests can run at realistic speed.
pub const MIN_INTERVAL_MS: u64 = 10;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    /// Tool definitions, keyed by the name routes/schedules refer to.
    pub tools: BTreeMap<String, ToolConfig>,
    #[serde(default)]
    pub http: Option<HttpConfig>,
    #[serde(default)]
    pub schedule: Vec<ScheduleEntry>,
    /// Directory for host-side state (scheduler last-run marks).
    /// Required when `schedule` is non-empty.
    #[serde(default)]
    pub state_dir: Option<PathBuf>,
    /// Name of the declared host profile every tool is compiled against (`"ephemeral"`,
    /// the built-in host this service runs tools under). Absent means the legacy
    /// no-profile context, where every host operation is Public-occurrence and a tool
    /// that checks one host result before the next host call is refused.
    #[serde(default)]
    pub host_profile: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolConfig {
    /// Path to the tool's `.sigil` source, relative to the config file.
    pub source: PathBuf,
    #[serde(default = "default_fuel")]
    pub fuel: u64,
    #[serde(default)]
    pub grants: GrantConfig,
    /// Optional verification-certificate path (relative to the config
    /// file). When present, boot verifies the certificate against the
    /// freshly compiled tool — source and wasm fingerprints, solver
    /// verification, and the gated-effect ⇄ grant cross-check — and
    /// refuses to start on any mismatch.
    #[serde(default)]
    pub cert: Option<PathBuf>,
}

fn default_fuel() -> u64 {
    1_000_000
}

#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GrantConfig {
    /// Filesystem read roots (directories).
    #[serde(default)]
    pub fs: Vec<String>,
    /// Filesystem write roots (directories).
    #[serde(default)]
    pub fs_write: Vec<String>,
    /// Outbound-HTTP host patterns (both GET and POST are granted).
    #[serde(default)]
    pub net: Vec<String>,
    /// KV read grants as `"NAMESPACE=DIR"`.
    #[serde(default)]
    pub kv: Vec<String>,
    /// KV write grants as `"NAMESPACE=DIR"`.
    #[serde(default)]
    pub kv_write: Vec<String>,
    /// `"wall"` or `"frozen:<ms>"`.
    #[serde(default)]
    pub time: Vec<String>,
    /// `"secure"` or `"seeded:<u64>"`.
    #[serde(default)]
    pub random: Vec<String>,
    /// Host-held secrets as `"NAME=VALUE"`, for `http::post_secret`. The
    /// guest writes `{{secret:NAME}}` in its header blob and the host
    /// substitutes the value on the way out, so the secret bytes never enter
    /// guest memory. An empty list is fail-closed: every placeholder is denied.
    ///
    /// The VALUE is a live credential. Prefer a config file the operator keeps
    /// out of version control — this field is never logged (`SecretGrant`'s
    /// `Debug` redacts it), but the file on disk holds it in the clear.
    #[serde(default)]
    pub secret: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HttpConfig {
    /// Bind address, e.g. `"127.0.0.1:8787"`. Use port 0 to let the OS
    /// pick (the chosen address is logged and exposed to tests).
    pub bind: String,
    pub routes: Vec<Route>,
    /// Maximum concurrently-handled connections; excess get 503.
    #[serde(default = "default_max_inflight")]
    pub max_inflight: usize,
}

fn default_max_inflight() -> usize {
    16
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Route {
    /// Exact request path (no wildcards in v1), must start with `/`.
    pub path: String,
    /// Tool name from `tools`.
    pub tool: String,
    #[serde(default = "default_content_type")]
    pub content_type: String,
    /// How the request becomes tool input. `raw` (default): the body
    /// bytes, or the query string for bodyless requests. `envelope`:
    /// an 8-digit ASCII length, the request-envelope JSON, then the
    /// raw body bytes — see `docs/serve-runtime.md`.
    #[serde(default)]
    pub input: InputMode,
    /// How tool output becomes the response. `raw` (default): output
    /// bytes are the 200 body. `envelope`: output is an 8-digit ASCII
    /// length, the response-envelope JSON ({"status", "headers"}),
    /// then the raw body bytes — see `docs/serve-runtime.md`.
    #[serde(default)]
    pub output: OutputMode,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum InputMode {
    #[default]
    Raw,
    Envelope,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OutputMode {
    #[default]
    Raw,
    Envelope,
}

fn default_content_type() -> String {
    "application/octet-stream".to_owned()
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScheduleEntry {
    /// Unique entry name — also the key for the durable last-run mark.
    pub name: String,
    /// Tool name from `tools`.
    pub tool: String,
    /// Fixed interval between runs. Exactly one of `every_ms` / `cron`.
    #[serde(default)]
    pub every_ms: Option<u64>,
    /// Five-field UTC cron expression (see `docs/serve-runtime.md`).
    /// Exactly one of `every_ms` / `cron`.
    #[serde(default)]
    pub cron: Option<String>,
    /// Input bytes passed to the tool on each scheduled run.
    #[serde(default)]
    pub input: String,
}

impl Config {
    /// Parse and validate a config file. `base_dir` for resolving tool
    /// source paths is the config file's parent directory.
    pub fn load(path: &Path) -> anyhow::Result<(Self, PathBuf)> {
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read config `{}`", path.display()))?;
        let config: Config = serde_json::from_str(&text)
            .with_context(|| format!("failed to parse config `{}`", path.display()))?;
        config.validate()?;
        let base_dir = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."))
            .to_path_buf();
        Ok((config, base_dir))
    }

    pub fn validate(&self) -> anyhow::Result<()> {
        if self.tools.is_empty() {
            bail!("config defines no tools");
        }
        if let Some(http) = &self.http {
            if http.routes.is_empty() {
                bail!("`http` is configured but has no routes");
            }
            if http.max_inflight == 0 {
                bail!("`http.max_inflight` must be at least 1");
            }
            let mut seen = BTreeSet::new();
            for route in &http.routes {
                let signature = validate_route_pattern(&route.path)?;
                if !seen.insert(signature.clone()) {
                    bail!(
                        "route `{}` collides with an earlier route (same shape `{}`)",
                        route.path,
                        signature
                    );
                }
                if !self.tools.contains_key(&route.tool) {
                    bail!("route `{}` names unknown tool `{}`", route.path, route.tool);
                }
            }
        }
        let mut names = BTreeSet::new();
        for entry in &self.schedule {
            if entry.name.is_empty() {
                bail!("schedule entries need a non-empty `name`");
            }
            if !names.insert(entry.name.as_str()) {
                bail!("duplicate schedule entry name `{}`", entry.name);
            }
            if !self.tools.contains_key(&entry.tool) {
                bail!(
                    "schedule entry `{}` names unknown tool `{}`",
                    entry.name,
                    entry.tool
                );
            }
            match (&entry.every_ms, &entry.cron) {
                (Some(every_ms), None) => {
                    if *every_ms < MIN_INTERVAL_MS {
                        bail!(
                            "schedule entry `{}`: every_ms {} is below the {} ms floor",
                            entry.name,
                            every_ms,
                            MIN_INTERVAL_MS
                        );
                    }
                }
                (None, Some(expr)) => {
                    crate::cron::parse(expr)
                        .with_context(|| format!("schedule entry `{}`", entry.name))?;
                }
                (Some(_), Some(_)) => {
                    bail!(
                        "schedule entry `{}`: give `every_ms` OR `cron`, not both",
                        entry.name
                    );
                }
                (None, None) => {
                    bail!(
                        "schedule entry `{}`: needs `every_ms` or `cron`",
                        entry.name
                    );
                }
            }
        }
        if !self.schedule.is_empty() && self.state_dir.is_none() {
            bail!("`schedule` entries require `state_dir` (durable last-run marks live there)");
        }
        if self.http.is_none() && self.schedule.is_empty() {
            bail!("config has neither `http` routes nor `schedule` entries — nothing to serve");
        }
        Ok(())
    }
}

impl GrantConfig {
    /// Convert to runtime grants. Every malformed descriptor is an
    /// error — a config typo must refuse to boot, not silently narrow
    /// (or widen) the sandbox.
    pub fn to_io_grants(&self, tool_name: &str) -> anyhow::Result<IoGrants> {
        let ctx = |what: &str, entry: &str| format!("tool `{tool_name}`: {what} grant `{entry}`");

        let mut grants = IoGrants::default();

        for entry in &self.fs {
            let root = canonical_dir(entry).with_context(|| ctx("fs", entry))?;
            grants.fs.push(FsGrant { root });
        }
        for entry in &self.fs_write {
            let root = canonical_dir(entry).with_context(|| ctx("fs_write", entry))?;
            grants.fs_write.push(FsWriteGrant { root });
        }
        for entry in &self.net {
            if entry.is_empty() {
                bail!("{}: empty host pattern", ctx("net", entry));
            }
            grants.net.push(NetGrant {
                host_pattern: entry.clone(),
                methods: vec![HttpMethod::Get, HttpMethod::Post],
            });
        }
        for entry in &self.kv {
            let (namespace, root) = parse_kv_descriptor(entry).with_context(|| ctx("kv", entry))?;
            grants.kv.push(KvGrant { namespace, root });
        }
        for entry in &self.kv_write {
            let (namespace, root) =
                parse_kv_descriptor(entry).with_context(|| ctx("kv_write", entry))?;
            grants.kv_write.push(KvWriteGrant { namespace, root });
        }
        for entry in &self.time {
            let grant = if entry == "wall" {
                TimeGrant::Wall
            } else if let Some(ms) = entry.strip_prefix("frozen:") {
                TimeGrant::Frozen(ms.parse().with_context(|| ctx("time", entry))?)
            } else {
                bail!("{}: expected `wall` or `frozen:<ms>`", ctx("time", entry));
            };
            grants.time.push(grant);
        }
        for entry in &self.random {
            let grant = if entry == "secure" {
                RandomGrant::Secure
            } else if let Some(seed) = entry.strip_prefix("seeded:") {
                RandomGrant::Seeded(seed.parse().with_context(|| ctx("random", entry))?)
            } else {
                bail!(
                    "{}: expected `secure` or `seeded:<u64>`",
                    ctx("random", entry)
                );
            };
            grants.random.push(grant);
        }
        for entry in &self.secret {
            // `NAME=VALUE`. A malformed entry is a hard error rather than a
            // skip: silently dropping it would boot a server whose every
            // `{{secret:NAME}}` placeholder is denied at request time, which
            // reads as an upstream auth failure rather than a config typo.
            // Never include the entry itself in an error — it carries the
            // secret.
            let Some((name, value)) = entry.split_once('=') else {
                bail!("tool `{tool_name}`: secret grant: expected `NAME=VALUE`");
            };
            if name.is_empty() {
                bail!("tool `{tool_name}`: secret grant: empty name in `NAME=VALUE`");
            }
            grants.secret.push(SecretGrant {
                name: name.to_owned(),
                value: value.as_bytes().to_vec(),
            });
        }

        grants
            .validate()
            .map_err(|e| anyhow::anyhow!("tool `{tool_name}`: {e}"))?;
        Ok(grants)
    }
}

/// Canonicalize a grant directory; it must already exist (creating
/// grant roots is the operator's job, matching the kv shim contract).
fn canonical_dir(entry: &str) -> anyhow::Result<PathBuf> {
    if entry.is_empty() {
        bail!("empty directory path");
    }
    let canonical = std::fs::canonicalize(entry)
        .with_context(|| format!("directory `{entry}` does not exist"))?;
    if !canonical.is_dir() {
        bail!("`{entry}` is not a directory");
    }
    Ok(canonical)
}

/// Validate a route pattern and return its SHAPE SIGNATURE — the
/// pattern with parameter names erased (`:x` → `:`, `*x` → `*`), so
/// `/t/:a` and `/t/:b` collide at boot instead of shadowing at
/// request time. Patterns are `/`-separated segments: literals,
/// `:name` parameters, and a `*rest` wildcard in FINAL position only.
pub fn validate_route_pattern(pattern: &str) -> anyhow::Result<String> {
    let Some(rest) = pattern.strip_prefix('/') else {
        bail!("route path `{pattern}` must start with `/`");
    };
    if pattern.contains('?') {
        bail!("route path `{pattern}` must not contain a query string");
    }
    let segments: Vec<&str> = rest.split('/').collect();
    let mut param_names = BTreeSet::new();
    let mut signature = String::new();
    for (index, segment) in segments.iter().enumerate() {
        signature.push('/');
        if let Some(name) = segment.strip_prefix(':') {
            if name.is_empty() {
                bail!("route `{pattern}`: `:` parameter needs a name");
            }
            if !param_names.insert(name.to_owned()) {
                bail!("route `{pattern}`: duplicate parameter name `{name}`");
            }
            signature.push(':');
        } else if let Some(name) = segment.strip_prefix('*') {
            if index != segments.len() - 1 {
                bail!("route `{pattern}`: `*` wildcard only allowed as the final segment");
            }
            if !name.is_empty() && !param_names.insert(name.to_owned()) {
                bail!("route `{pattern}`: duplicate parameter name `{name}`");
            }
            signature.push('*');
        } else {
            if segment.contains(':') || segment.contains('*') {
                bail!("route `{pattern}`: `:`/`*` must lead their segment (got `{segment}`)");
            }
            signature.push_str(segment);
        }
    }
    Ok(signature)
}

/// `"NAMESPACE=DIR"` — same shape the MCP envelope and `sigil forge
/// --kv` use.
fn parse_kv_descriptor(entry: &str) -> anyhow::Result<(String, PathBuf)> {
    let Some((ns, dir)) = entry.split_once('=') else {
        bail!("expected NAMESPACE=DIR");
    };
    if ns.is_empty() || dir.is_empty() {
        bail!("expected non-empty NAMESPACE and DIR");
    }
    Ok((ns.to_owned(), canonical_dir(dir)?))
}
