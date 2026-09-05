//! Argv parsing: the typed `Command` vocabulary and the hand-rolled
//! splitters `parse_args` fans out to. A parse failure
//! propagates as `Err` and `main` turns it into exit 2 (R800 under
//! `--json`) before any handler runs. Splitters read referenced source
//! files into the payload's `source_text`/`source_files` at parse time
//! (`parse_path_command` and `read_project_root` ingest whole project
//! roots); cert and wasm arguments stay `PathBuf`s for the handlers to
//! open. Payload shapes are pinned by the in-file
//! `typed_command_shape_tests` and `multi_file_cli_tests`.

use std::fs;
use std::path::PathBuf;

use anyhow::{Context, bail};

use crate::json_envelope::OutputFormat;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CommandKind {
    Check,
    Run,
    Forge,
    RegistryAdd,
    RegistrySearch,
    RegistryList,
    VerifyCert,
    Translate,
    Explain,
    Version,
    Help,
}

#[cfg(test)]
mod typed_command_shape_tests {
    use super::{Command, parse_args};
    use proptest::prelude::*;

    #[test]
    fn explain_parses_to_an_explain_payload() {
        let command = parse_args(&["explain".to_owned(), "T001".to_owned()]).unwrap();
        match command {
            Command::Explain(args) => assert_eq!(args.code, "T001"),
            other => panic!("expected explain command, got {other:?}"),
        }
    }

    #[test]
    fn inline_check_parses_to_a_compile_payload() {
        let command = parse_args(&["check-inline".to_owned(), "module demo;".to_owned()]).unwrap();
        match command {
            Command::Check(args) => assert_eq!(args.source_name, "<inline>"),
            other => panic!("expected check command, got {other:?}"),
        }
    }

    proptest! {
        #[test]
        fn explain_payload_round_trips(code in "[A-Z][0-9]{3}", json in any::<bool>()) {
            let mut raw = vec!["explain".to_owned(), code.clone()];
            if json {
                raw.push("--json".to_owned());
            }
            match parse_args(&raw).unwrap() {
                Command::Explain(args) => {
                    prop_assert_eq!(args.code, code);
                    prop_assert_eq!(args.json, json);
                }
                other => prop_assert!(false, "expected explain command, got {other:?}"),
            }
        }

        #[test]
        fn inline_payload_round_trips(
            run in any::<bool>(),
            source in "[A-Za-z0-9 ;{}]{0,80}",
        ) {
            let verb = if run { "run-inline" } else { "check-inline" };
            let raw = vec![verb.to_owned(), source.clone()];
            match parse_args(&raw).unwrap() {
                Command::Run(args) if run => prop_assert_eq!(args.source_text, source),
                Command::Check(args) if !run => prop_assert_eq!(args.source_text, source),
                other => prop_assert!(false, "unexpected command variant: {other:?}"),
            }
        }
    }
}

impl CommandKind {
    pub(crate) fn json_name(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Run => "run",
            Self::Forge => "forge",
            Self::RegistryAdd => "registry-add",
            Self::RegistrySearch => "registry-search",
            Self::RegistryList => "registry-list",
            Self::VerifyCert => "verify-cert",
            Self::Translate => "translate",
            Self::Explain => "explain",
            Self::Version => "version",
            Self::Help => "help",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CompileCommand {
    pub(crate) source_name: String,
    pub(crate) source_text: String,
    pub(crate) dump_wat: bool,
    pub(crate) json: bool,
    pub(crate) cert_path: Option<PathBuf>,
    pub(crate) wasm_out_path: Option<PathBuf>,
    pub(crate) build_deadline: Option<i64>,
    pub(crate) source_files: Vec<(String, String)>,
    pub(crate) entry_module: Option<String>,
    pub(crate) from: Option<String>,
    pub(crate) project_root: Option<String>,
    /// Explicit local package root. Never inferred from the current directory.
    pub(crate) package_root: Option<PathBuf>,
    /// ACTOR-LIVE AL-4: run as a resident service, feeding stdin lines to the entry actor.
    pub(crate) serve: bool,
    /// The entry-actor handler each stdin line routes to (`--on`); when `None`, the sole
    /// non-`Start` single-scalar-param handler is used.
    pub(crate) serve_handler: Option<String>,
    /// PPS-4: per-actor persistent-heap byte cap (`--persistent-cap`); `None`
    /// keeps the runtime default (the whole arena).
    pub(crate) persistent_cap: Option<u32>,
    /// `--host-profile <NAME>`: compile against a declared host profile (`ephemeral` is the
    /// built-in host); absent means the legacy no-profile context.
    pub(crate) host_profile: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ForgeCommand {
    pub(crate) source_name: String,
    pub(crate) source_text: String,
    pub(crate) fuel: u64,
    pub(crate) dump_wat: bool,
    pub(crate) json: bool,
    pub(crate) input: String,
    pub(crate) fs_roots: Vec<PathBuf>,
    pub(crate) net_hosts: Vec<String>,
    /// KV read grants (--kv NS=DIR flags), namespace → backing dir.
    pub(crate) kv_grants: Vec<(String, PathBuf)>,
    /// KV write grants (--kv-write NS=DIR flags).
    pub(crate) kv_write_grants: Vec<(String, PathBuf)>,
    pub(crate) template_id: Option<u64>,
    pub(crate) patches: Vec<(String, String)>,
    pub(crate) cert_path: Option<PathBuf>,
    pub(crate) frozen_time_ms: Option<i64>,
    pub(crate) host_profile: Option<String>,
    pub(crate) random_seed: Option<u64>,
    pub(crate) input_bytes_override: Option<Vec<u8>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegistryAddCommand {
    pub(crate) source_name: String,
    pub(crate) source_text: String,
    pub(crate) task_desc: String,
    pub(crate) tags: Vec<String>,
    pub(crate) json: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegistrySearchCommand {
    pub(crate) query: String,
    pub(crate) json: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VerifyCertCommand {
    pub(crate) source_name: String,
    pub(crate) source_text: String,
    pub(crate) cert_path: PathBuf,
    pub(crate) wasm_path: Option<PathBuf>,
    pub(crate) forbidden_effects: Vec<String>,
    pub(crate) allowed_effects: Vec<String>,
    pub(crate) package_root: Option<PathBuf>,
    pub(crate) json: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TranslateCommand {
    pub(crate) source_name: String,
    pub(crate) source_text: String,
    pub(crate) from: String,
    pub(crate) project_root: Option<String>,
    pub(crate) out_path: Option<PathBuf>,
    pub(crate) json: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExplainCommand {
    pub(crate) code: String,
    pub(crate) json: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Command {
    Check(CompileCommand),
    Run(CompileCommand),
    Forge(ForgeCommand),
    RegistryAdd(RegistryAddCommand),
    RegistrySearch(RegistrySearchCommand),
    RegistryList {
        json: bool,
    },
    VerifyCert(VerifyCertCommand),
    Translate(TranslateCommand),
    Explain(ExplainCommand),
    /// Version, host, and whether Z3 is linked into THIS binary.
    /// Payload-light like `RegistryList` — there is nothing to carry but
    /// the output format.
    Version {
        json: bool,
    },
    Help {
        json: bool,
    },
}

impl Command {
    /// The declared host profile named on the command line, if any.
    pub(crate) fn host_profile(&self) -> Option<&str> {
        match self {
            Command::Check(args) | Command::Run(args) => args.host_profile.as_deref(),
            Command::Forge(args) => args.host_profile.as_deref(),
            _ => None,
        }
    }

    pub(crate) fn kind(&self) -> CommandKind {
        match self {
            Self::Check(_) => CommandKind::Check,
            Self::Run(_) => CommandKind::Run,
            Self::Forge(_) => CommandKind::Forge,
            Self::RegistryAdd(_) => CommandKind::RegistryAdd,
            Self::RegistrySearch(_) => CommandKind::RegistrySearch,
            Self::RegistryList { .. } => CommandKind::RegistryList,
            Self::VerifyCert(_) => CommandKind::VerifyCert,
            Self::Translate(_) => CommandKind::Translate,
            Self::Explain(_) => CommandKind::Explain,
            Self::Version { .. } => CommandKind::Version,
            Self::Help { .. } => CommandKind::Help,
        }
    }

    pub(crate) fn output_format(&self) -> OutputFormat {
        let json = match self {
            Self::Check(args) | Self::Run(args) => args.json,
            Self::Forge(args) => args.json,
            Self::RegistryAdd(args) => args.json,
            Self::RegistrySearch(args) => args.json,
            Self::RegistryList { json } => *json,
            Self::VerifyCert(args) => args.json,
            Self::Translate(args) => args.json,
            Self::Explain(args) => args.json,
            Self::Version { json } | Self::Help { json } => *json,
        };
        if json {
            OutputFormat::Json
        } else {
            OutputFormat::Human
        }
    }
}

fn compile_command(kind: CommandKind, args: CompileCommand) -> Command {
    match kind {
        CommandKind::Check => Command::Check(args),
        CommandKind::Run => Command::Run(args),
        _ => unreachable!("only check and run share compile arguments"),
    }
}

/// SOL-XFILE: enumerate + read every `*.sol` under `root` into an in-memory map keyed by
/// `/`-separated ROOT-RELATIVE paths, and resolve `entry` to its key. The walk NEVER
/// follows symlinks (a symlinked file/dir is skipped — an out-of-root file can never
/// enter the map under an in-root key), and is bounded by dumb caps. This is the ONLY
/// filesystem I/O on the project path; the frontend resolves imports against the map.
pub(crate) fn read_project_root(
    root: &str,
    entry: &str,
) -> anyhow::Result<(std::collections::BTreeMap<String, String>, String)> {
    const MAX_WALK_FILES: usize = 2048;
    const MAX_WALK_BYTES: u64 = 32 * 1024 * 1024;
    let root_path = fs::canonicalize(root)
        .with_context(|| format!("--project-root `{root}` is not a readable directory"))?;
    let mut files = std::collections::BTreeMap::new();
    let mut stack = vec![root_path.clone()];
    let mut total: u64 = 0;
    while let Some(dir) = stack.pop() {
        let rd =
            fs::read_dir(&dir).with_context(|| format!("failed to list `{}`", dir.display()))?;
        for e in rd {
            let e = e?;
            let p = e.path();
            // symlink_metadata never follows the link — a symlink of EITHER kind is skipped.
            let meta = fs::symlink_metadata(&p)?;
            if meta.file_type().is_symlink() {
                continue;
            }
            if meta.is_dir() {
                stack.push(p);
            } else if p.extension().and_then(|x| x.to_str()) == Some("sol") {
                if files.len() >= MAX_WALK_FILES {
                    bail!("--project-root walk exceeds {MAX_WALK_FILES} .sol files");
                }
                total = total.saturating_add(meta.len());
                if total > MAX_WALK_BYTES {
                    bail!("--project-root walk exceeds {MAX_WALK_BYTES} bytes of .sol source");
                }
                let key = p
                    .strip_prefix(&root_path)
                    .expect("walked path is under root")
                    .to_string_lossy()
                    .replace('\\', "/");
                let text = fs::read_to_string(&p)
                    .with_context(|| format!("failed to read `{}`", p.display()))?;
                files.insert(key, text);
            }
        }
    }
    // The entry may be given as a filesystem path (canonicalize + strip the root) or as a
    // root-relative key (used as-is, `/`-normalized).
    let entry_key = match fs::canonicalize(entry) {
        Ok(abs) => abs
            .strip_prefix(&root_path)
            .map_err(|_| anyhow::anyhow!("entry `{entry}` is not under --project-root `{root}`"))?
            .to_string_lossy()
            .replace('\\', "/"),
        Err(_) => entry.replace('\\', "/"),
    };
    Ok((files, entry_key))
}

struct ArgCursor<'a> {
    args: &'a [String],
    index: usize,
}

impl<'a> ArgCursor<'a> {
    fn new(args: &'a [String], index: usize) -> Self {
        Self { args, index }
    }

    fn next(&mut self) -> Option<&'a str> {
        let value = self.args.get(self.index)?;
        self.index += 1;
        Some(value)
    }

    fn peek(&self) -> Option<&'a str> {
        self.args.get(self.index).map(String::as_str)
    }

    fn require(&mut self, message: &str) -> anyhow::Result<&'a str> {
        self.next()
            .ok_or_else(|| anyhow::anyhow!(message.to_owned()))
    }
}

pub(crate) fn parse_args(args: &[String]) -> anyhow::Result<Command> {
    match args.first().map(String::as_str) {
        None => Ok(Command::Check(CompileCommand {
            source_name: "<inline>".to_owned(),
            source_text: "module sigil;".to_owned(),
            ..CompileCommand::default()
        })),
        Some("check") => parse_path_command(args, "check", CommandKind::Check),
        Some("run") => parse_path_command(args, "run", CommandKind::Run),
        Some("check-inline") => parse_inline_command(args, "check-inline", CommandKind::Check),
        Some("run-inline") => parse_inline_command(args, "run-inline", CommandKind::Run),
        Some("forge") => parse_forge_args(args),
        Some("registry") => parse_registry_args(args),
        Some("verify-cert") => parse_verify_cert_args(args),
        Some("translate") => parse_translate_args(args),
        Some("explain") => parse_explain_args(args),
        // Distribution surface (Phase 0 of the prebuilt-binary channel): an
        // installer needs a stable way to ask an already-installed binary
        // what it is before deciding to replace it, and a downloaded binary
        // needs to answer `--help` rather than exit 2 on the first thing a
        // new user types. Accepted in both the GNU-flag and bare-subcommand
        // spellings because both are what people try.
        Some("--version" | "-V" | "version") => parse_info_command(args, CommandKind::Version),
        Some("--help" | "-h" | "help") => parse_info_command(args, CommandKind::Help),
        Some(other) => {
            bail!(
                "unknown command `{other}`. expected `check`, `run`, `check-inline`, `run-inline`, `forge`, `registry`, `verify-cert`, `translate`, or `explain`. run `sigil --help` for usage"
            );
        }
    }
}

/// Parse `--version` / `--help`, which take no arguments beyond an
/// optional `--json`.
fn parse_info_command(args: &[String], kind: CommandKind) -> anyhow::Result<Command> {
    let name = kind.json_name();
    let mut json = false;
    for arg in &args[1..] {
        match arg.as_str() {
            "--json" => json = true,
            other => bail!("{name}: unexpected argument `{other}` (expected none, or `--json`)"),
        }
    }
    Ok(match kind {
        CommandKind::Help => Command::Help { json },
        _ => Command::Version { json },
    })
}

fn parse_explain_args(args: &[String]) -> anyhow::Result<Command> {
    // explain <CODE> [--json]
    let mut code: Option<String> = None;
    let mut json = false;
    for arg in &args[1..] {
        match arg.as_str() {
            "--json" => json = true,
            other if other.starts_with('-') => bail!("explain: unknown flag `{other}`"),
            other => {
                if code.is_some() {
                    bail!(
                        "explain: unexpected extra argument `{other}` (expected exactly one code)"
                    );
                }
                code = Some(other.to_owned());
            }
        }
    }
    let code =
        code.context("explain: missing diagnostic code (usage: sigil explain <CODE> [--json])")?;
    Ok(Command::Explain(ExplainCommand { code, json }))
}

fn parse_forge_args(args: &[String]) -> anyhow::Result<Command> {
    // forge <path> [--fuel <n>] [--input <text>] [--fs <dir>] [--net <host>]
    //   [--kv <ns=dir>] [--kv-write <ns=dir>] [--json]
    //   OR
    // forge --template <id> [--patch "FIND=REPLACE"] [--fuel <n>] [...] [--json]

    let mut fuel: u64 = 100_000;
    let mut host_profile: Option<String> = None;
    let mut input = String::new();
    let mut dump_wat = false;
    let mut json = false;
    let mut fs_roots: Vec<PathBuf> = vec![];
    let mut net_hosts: Vec<String> = vec![];
    let mut kv_grants: Vec<(String, PathBuf)> = vec![];
    let mut kv_write_grants: Vec<(String, PathBuf)> = vec![];
    let mut template_id: Option<u64> = None;
    let mut patches: Vec<(String, String)> = vec![];
    let mut path: Option<String> = None;
    // Forge certificates also validate the requested filesystem and network grants.
    let mut cert_path: Option<PathBuf> = None;
    let mut frozen_time_ms: Option<i64> = None;
    let mut random_seed: Option<u64> = None;
    let mut input_bytes_override: Option<Vec<u8>> = None;

    let mut cursor = ArgCursor::new(args, 1);
    if cursor.peek().is_some_and(|arg| !arg.starts_with("--")) {
        path = cursor.next().map(str::to_owned);
    }

    while let Some(arg) = cursor.next() {
        match arg {
            "--host-profile" => {
                let name =
                    cursor.require("--host-profile requires a profile name (`ephemeral`)")?;
                if sigil_runtime::host_profile_by_name(name).is_none() {
                    bail!(
                        "--host-profile: unknown profile `{name}` (the built-in host is `ephemeral`)"
                    );
                }
                host_profile = Some(name.to_owned());
            }
            "--fuel" => {
                let value = cursor.require("--fuel requires a value")?;
                fuel = value
                    .parse()
                    .with_context(|| format!("invalid fuel value `{value}`"))?;
            }
            "--input" => {
                input = cursor.require("--input requires a value")?.to_owned();
            }
            "--wat" => {
                dump_wat = true;
            }
            "--json" => {
                json = true;
            }
            "--fs" => {
                fs_roots.push(PathBuf::from(
                    cursor.require("--fs requires a directory path")?,
                ));
            }
            "--net" => {
                net_hosts.push(cursor.require("--net requires a host pattern")?.to_owned());
            }
            "--kv" => {
                kv_grants.push(parse_kv_grant_flag(
                    cursor.require("--kv requires a value in NAMESPACE=DIR format")?,
                    "--kv",
                )?);
            }
            "--kv-write" => {
                kv_write_grants.push(parse_kv_grant_flag(
                    cursor.require("--kv-write requires a value in NAMESPACE=DIR format")?,
                    "--kv-write",
                )?);
            }
            "--template" => {
                let value = cursor.require("--template requires a template id")?;
                template_id = Some(
                    value
                        .parse()
                        .with_context(|| format!("invalid template id `{value}`"))?,
                );
            }
            "--patch" => {
                let patch_str =
                    cursor.require("--patch requires a value in FIND=REPLACE format")?;
                let eq_pos = patch_str
                    .find('=')
                    .with_context(|| format!("--patch value must contain `=`: `{patch_str}`"))?;
                let find = patch_str[..eq_pos].to_owned();
                let replace = patch_str[eq_pos + 1..].to_owned();
                patches.push((find, replace));
            }
            "--cert" => {
                cert_path = Some(PathBuf::from(
                    cursor.require("--cert requires a file path")?,
                ));
            }
            "--frozen-time" => {
                let value =
                    cursor.require("--frozen-time requires a value (ms since Unix epoch, i64)")?;
                frozen_time_ms = Some(value.parse::<i64>().with_context(|| {
                    format!("invalid --frozen-time value `{value}` (expect i64)")
                })?);
            }
            "--random-seed" => {
                let value = cursor.require("--random-seed requires a value (u64)")?;
                let seed: u64 = value.parse().with_context(|| {
                    format!("invalid --random-seed value `{value}` (expect u64)")
                })?;
                if seed == 0 {
                    bail!(
                        "--random-seed must be nonzero (xorshift weakness on 0; use any other u64)"
                    );
                }
                random_seed = Some(seed);
            }
            "--input-hex" => {
                let hex = cursor.require("--input-hex requires a hex string")?;
                // Canonical form: lowercase ASCII hex, even length, no
                // separators / 0x prefix / whitespace. Empty allowed
                // (treated as absent during cross-check).
                if !is_canonical_hex(hex) {
                    bail!(
                        "--input-hex value `{hex}` is not canonical hex: \
                         lowercase, even length, no whitespace / prefix / separators"
                    );
                }
                let bytes: Vec<u8> = (0..hex.len())
                    .step_by(2)
                    .map(|j| u8::from_str_radix(&hex[j..j + 2], 16).expect("regex pre-validated"))
                    .collect();
                input_bytes_override = Some(bytes);
            }
            other => {
                bail!("unknown forge option `{other}`");
            }
        }
    }

    // Empty text and byte inputs are equivalent to no input.
    let has_input_text = !input.is_empty();
    let has_input_hex = input_bytes_override
        .as_ref()
        .map(|b| !b.is_empty())
        .unwrap_or(false);
    if has_input_text && has_input_hex {
        bail!("--input and --input-hex are mutually exclusive (both non-empty)");
    }

    if template_id.is_some() {
        return Ok(Command::Forge(ForgeCommand {
            source_name: "<template>".to_owned(),
            source_text: String::new(), // filled later from registry
            fuel,
            dump_wat,
            json,
            input,
            fs_roots,
            net_hosts,
            kv_grants,
            kv_write_grants,
            template_id,
            patches,
            cert_path,
            frozen_time_ms,
            host_profile: host_profile.clone(),
            random_seed,
            input_bytes_override,
        }));
    }

    let path = path.ok_or_else(|| {
        anyhow::anyhow!(
            "`forge` requires a file path or --template <id>: forge <path> [options] OR forge --template <id> [options]"
        )
    })?;
    let source_text = fs::read_to_string(&path)
        .with_context(|| format!("failed to read source file `{path}`"))?;

    Ok(Command::Forge(ForgeCommand {
        host_profile: host_profile.clone(),
        source_name: path,
        source_text,
        fuel,
        dump_wat,
        json,
        input,
        fs_roots,
        net_hosts,
        kv_grants,
        kv_write_grants,
        template_id: None,
        patches: vec![],
        cert_path,
        frozen_time_ms,
        random_seed,
        input_bytes_override,
    }))
}

/// Parse a `NAMESPACE=DIR` kv-grant flag value. The namespace is an
/// opaque label (exact-match against `kv::` calls); DIR is the backing
/// directory the host serves the namespace from.
fn parse_kv_grant_flag(value: &str, flag: &str) -> anyhow::Result<(String, PathBuf)> {
    let (ns, dir) = value
        .split_once('=')
        .ok_or_else(|| anyhow::anyhow!("{flag} requires NAMESPACE=DIR, got `{value}`"))?;
    if ns.is_empty() || dir.is_empty() {
        bail!("{flag} requires a non-empty NAMESPACE and DIR, got `{value}`");
    }
    Ok((ns.to_owned(), PathBuf::from(dir)))
}

/// Canonical hex shape for `--input-hex`: lowercase ASCII hex digits
/// only, even length. Empty string allowed (treated as absent during
/// the mutual-exclusivity post-parse check).
///
/// Pinned identically to `header_parser._validate_hex` so the CLI and
/// the Python slot-registry's hex inputs round-trip without subtle
/// canonicalization gaps. Whitespace, `0x` prefix, separators (`-`, `:`,
/// etc.), and uppercase digits all rejected.
fn is_canonical_hex(s: &str) -> bool {
    if !s.len().is_multiple_of(2) {
        return false;
    }
    s.bytes()
        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn parse_registry_args(args: &[String]) -> anyhow::Result<Command> {
    if args.len() < 2 {
        bail!("`registry` requires a sub-command: add, search, or list");
    }
    match args[1].as_str() {
        "add" => {
            if args.len() < 3 {
                bail!("`registry add` requires a file path");
            }
            let path = args[2].clone();
            let source_text = fs::read_to_string(&path)
                .with_context(|| format!("failed to read source file `{path}`"))?;

            let mut task_desc = String::new();
            let mut tags = Vec::new();
            let mut json = false;

            let mut cursor = ArgCursor::new(args, 3);
            while let Some(arg) = cursor.next() {
                match arg {
                    "--task" => {
                        task_desc = cursor.require("--task requires a value")?.to_owned();
                    }
                    "--tags" => {
                        tags = cursor
                            .require("--tags requires a value")?
                            .split(',')
                            .map(|s| s.trim().to_owned())
                            .collect();
                    }
                    "--json" => json = true,
                    other => bail!("unknown registry add option `{other}`"),
                }
            }

            if task_desc.is_empty() {
                bail!("`registry add` requires --task \"description\"");
            }

            Ok(Command::RegistryAdd(RegistryAddCommand {
                source_name: path,
                source_text,
                task_desc,
                tags,
                json,
            }))
        }
        "search" => {
            if args.len() < 3 {
                bail!("`registry search` requires a query string");
            }
            let mut json = false;
            for arg in &args[3..] {
                if arg == "--json" {
                    json = true;
                } else {
                    bail!("unknown registry search option `{arg}`");
                }
            }
            Ok(Command::RegistrySearch(RegistrySearchCommand {
                query: args[2].clone(),
                json,
            }))
        }
        "list" => {
            let mut json = false;
            for arg in &args[2..] {
                if arg == "--json" {
                    json = true;
                } else {
                    bail!("unknown registry list option `{arg}`");
                }
            }
            Ok(Command::RegistryList { json })
        }
        other => bail!("unknown registry sub-command `{other}`. expected add, search, or list"),
    }
}

fn parse_path_command(
    args: &[String],
    command: &str,
    kind: CommandKind,
) -> anyhow::Result<Command> {
    let mut paths: Vec<String> = Vec::new();
    let mut host_profile: Option<String> = None;
    let mut dump_wat = false;
    let mut json = false;
    let mut wasm_out_path: Option<PathBuf> = None;
    let mut cert_path: Option<PathBuf> = None;
    let mut build_deadline: Option<i64> = None;
    let mut entry_module: Option<String> = None;
    let mut from: Option<String> = None;
    // The CLI reads Solidity project files; frontend import resolution stays in-memory.
    let mut project_root: Option<String> = None;
    let mut package_root: Option<PathBuf> = None;
    let mut serve = false;
    let mut serve_handler: Option<String> = None;
    let mut persistent_cap: Option<u32> = None;

    let mut cursor = ArgCursor::new(args, 1);
    while let Some(arg) = cursor.next() {
        match arg {
            "--host-profile" => {
                let name =
                    cursor.require("--host-profile requires a profile name (`ephemeral`)")?;
                if sigil_runtime::host_profile_by_name(name).is_none() {
                    bail!(
                        "--host-profile: unknown profile `{name}` (the built-in host is `ephemeral`)"
                    );
                }
                host_profile = Some(name.to_owned());
            }
            "--wat" => dump_wat = true,
            "--json" => json = true,
            "--serve" => serve = true,
            "--on" => {
                serve_handler = Some(cursor.require("--on requires a handler name")?.to_owned());
            }
            "--persistent-cap" => {
                let value = cursor.require("--persistent-cap requires a byte count")?;
                persistent_cap = Some(value.parse().with_context(|| {
                    format!("invalid --persistent-cap value `{value}` (bytes, u32)")
                })?);
            }
            "--from" => {
                from = Some(
                    cursor
                        .require("--from requires a language name (e.g. typescript)")?
                        .to_owned(),
                );
            }
            "--emit-wasm" => {
                wasm_out_path = Some(PathBuf::from(
                    cursor.require("--emit-wasm requires a file path")?,
                ));
            }
            "--cert" => {
                cert_path = Some(PathBuf::from(
                    cursor.require("--cert requires a file path")?,
                ));
            }
            "--build-deadline" => {
                let value = cursor.require("--build-deadline requires an i64 value")?;
                build_deadline = Some(value.parse::<i64>().with_context(|| {
                    format!("--build-deadline value `{value}` is not a valid i64")
                })?);
            }
            "--entry" => {
                entry_module = Some(cursor.require("--entry requires a module name")?.to_owned());
            }
            "--project-root" => {
                project_root = Some(
                    cursor
                        .require("--project-root requires a directory path")?
                        .to_owned(),
                );
            }
            "--package" => {
                let value = PathBuf::from(cursor.require("--package requires a directory path")?);
                if package_root.replace(value).is_some() {
                    bail!("--package may be supplied only once");
                }
            }
            other if other.starts_with("--") => bail!("unknown {command} option `{other}`"),
            other => {
                paths.push(other.to_owned());
            }
        }
    }

    if package_root.is_none() && paths.is_empty() {
        return Err(anyhow::anyhow!(
            "`{command}` requires at least one file path"
        ));
    }

    if let Some(package_root) = package_root {
        if kind != CommandKind::Check {
            bail!("--package is supported only with `check`");
        }
        if !paths.is_empty() {
            bail!("--package is mutually exclusive with source file paths");
        }
        if from.is_some()
            || project_root.is_some()
            || entry_module.is_some()
            || serve
            || serve_handler.is_some()
            || persistent_cap.is_some()
        {
            bail!(
                "--package cannot be combined with --from, --project-root, --entry, --serve, --on, or --persistent-cap"
            );
        }
        return Ok(Command::Check(CompileCommand {
            source_name: format!("<package:{}>", package_root.display()),
            package_root: Some(package_root),
            dump_wat,
            json,
            wasm_out_path,
            cert_path,
            build_deadline,
            host_profile: host_profile.clone(),
            ..CompileCommand::default()
        }));
    }

    // `--serve` (and its `--on`) only apply to `run` — `check` never starts the runtime.
    if serve && kind != CommandKind::Run {
        bail!("--serve is only supported with `run`, not `{command}`");
    }
    if serve_handler.is_some() && !serve {
        bail!("--on requires --serve");
    }

    if let Some(root) = project_root {
        let Some(lang) = from.as_deref() else {
            bail!("--project-root requires --from solidity");
        };
        if lang != "solidity" {
            bail!("--project-root is only supported with --from solidity");
        }
        if paths.len() != 1 {
            bail!("--project-root takes exactly one entry file");
        }
        let entry_raw = paths.pop().expect("len == 1");
        let (files, entry_key) = read_project_root(&root, &entry_raw)?;
        return match sigil_frontends::translate_solidity_project(&files, &entry_key) {
            Ok(emitted) => Ok(compile_command(
                kind,
                CompileCommand {
                    source_name: entry_key,
                    source_text: emitted.text,
                    dump_wat,
                    json,
                    wasm_out_path,
                    cert_path,
                    build_deadline,
                    entry_module,
                    from: None,
                    host_profile: host_profile.clone(),
                    ..CompileCommand::default()
                },
            )),
            Err(diags) => {
                for d in &diags {
                    eprintln!("{}: {}", d.code, d.message);
                }
                bail!("project translation failed for `{entry_raw}`");
            }
        };
    }

    if paths.len() == 1 {
        let path = paths.pop().expect("len == 1");
        let source_text = fs::read_to_string(&path)
            .with_context(|| format!("failed to read source file `{path}`"))?;
        return Ok(compile_command(
            kind,
            CompileCommand {
                source_name: path,
                source_text,
                dump_wat,
                json,
                wasm_out_path,
                cert_path,
                build_deadline,
                entry_module,
                from,
                serve,
                serve_handler,
                persistent_cap,
                host_profile: host_profile.clone(),
                ..CompileCommand::default()
            },
        ));
    }

    // `--from` translation is single-file only (the translator emits one
    // module from one DSL file).
    if from.is_some() {
        bail!("--from is only supported with a single input file");
    }

    let mut source_files: Vec<(String, String)> = Vec::with_capacity(paths.len());
    for path in &paths {
        let text = fs::read_to_string(path)
            .with_context(|| format!("failed to read source file `{path}`"))?;
        source_files.push((path.clone(), text));
    }

    Ok(compile_command(
        kind,
        CompileCommand {
            source_name: "<project>".to_string(),
            source_text: String::new(),
            dump_wat,
            json,
            wasm_out_path,
            cert_path,
            build_deadline,
            entry_module,
            source_files,
            serve,
            serve_handler,
            host_profile: host_profile.clone(),
            ..CompileCommand::default()
        },
    ))
}

fn parse_inline_command(
    args: &[String],
    command: &str,
    kind: CommandKind,
) -> anyhow::Result<Command> {
    let mut source_text: Option<String> = None;
    let mut host_profile: Option<String> = None;
    let mut dump_wat = false;
    let mut json = false;

    let mut rest = args[1..].iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--wat" => dump_wat = true,
            "--json" => json = true,
            "--host-profile" => {
                let name = rest
                    .next()
                    .context("--host-profile requires a profile name (`ephemeral`)")?;
                if sigil_runtime::host_profile_by_name(name).is_none() {
                    bail!(
                        "--host-profile: unknown profile `{name}` (the built-in host is `ephemeral`)"
                    );
                }
                host_profile = Some(name.to_owned());
            }
            other if other.starts_with("--") => bail!("unknown {command} option `{other}`"),
            other => {
                if source_text.is_some() {
                    bail!("`{command}` accepts exactly one source string");
                }
                source_text = Some(other.to_owned());
            }
        }
    }

    let source_text =
        source_text.ok_or_else(|| anyhow::anyhow!("`{command}` requires inline source text"))?;

    Ok(compile_command(
        kind,
        CompileCommand {
            source_name: "<inline>".to_owned(),
            source_text,
            dump_wat,
            json,
            host_profile: host_profile.clone(),
            ..CompileCommand::default()
        },
    ))
}

fn parse_translate_args(args: &[String]) -> anyhow::Result<Command> {
    let mut from: Option<String> = None;
    let mut path: Option<String> = None;
    let mut out: Option<PathBuf> = None;
    let mut json = false;
    let mut project_root: Option<String> = None;

    let mut cursor = ArgCursor::new(args, 1);
    while let Some(arg) = cursor.next() {
        match arg {
            "--from" => {
                from = Some(
                    cursor
                        .require("--from requires a language name (e.g. typescript)")?
                        .to_owned(),
                );
            }
            "--emit" => {
                out = Some(PathBuf::from(
                    cursor.require("--emit requires a file path")?,
                ));
            }
            "--json" => json = true,
            "--project-root" => {
                project_root = Some(
                    cursor
                        .require("--project-root requires a directory path")?
                        .to_owned(),
                );
            }
            other if other.starts_with("--") => bail!("unknown translate option `{other}`"),
            other => {
                if path.is_some() {
                    bail!("translate accepts exactly one input file");
                }
                path = Some(other.to_owned());
            }
        }
    }

    let from =
        from.ok_or_else(|| anyhow::anyhow!("translate requires --from <lang> (e.g. typescript)"))?;
    let path = path.ok_or_else(|| anyhow::anyhow!("translate requires an input file path"))?;
    // Project entries are root-relative keys resolved against the enumerated file set.
    if project_root.is_some() {
        if from != "solidity" {
            bail!("--project-root is only supported with --from solidity");
        }
        return Ok(Command::Translate(TranslateCommand {
            source_name: path,
            source_text: String::new(),
            json,
            from,
            project_root,
            out_path: out,
        }));
    }
    let source_text = fs::read_to_string(&path)
        .with_context(|| format!("failed to read source file `{path}`"))?;

    Ok(Command::Translate(TranslateCommand {
        source_name: path,
        source_text,
        json,
        from,
        project_root: None,
        out_path: out,
    }))
}

fn parse_verify_cert_args(args: &[String]) -> anyhow::Result<Command> {
    let mut cert_path: Option<PathBuf> = None;
    let mut source_path: Option<String> = None;
    let mut wasm_path: Option<PathBuf> = None;
    let mut forbidden_effects: Vec<String> = Vec::new();
    let mut allowed_effects: Vec<String> = Vec::new();
    let mut json = false;
    let mut package_root: Option<PathBuf> = None;

    let mut cursor = ArgCursor::new(args, 1);
    while let Some(arg) = cursor.next() {
        match arg {
            "--cert" => {
                cert_path = Some(PathBuf::from(
                    cursor.require("--cert requires a file path")?,
                ));
            }
            "--source" => {
                source_path = Some(cursor.require("--source requires a file path")?.to_owned());
            }
            "--wasm" => {
                wasm_path = Some(PathBuf::from(
                    cursor.require("--wasm requires a file path")?,
                ));
            }
            "--package" => {
                let value = PathBuf::from(cursor.require("--package requires a directory path")?);
                if package_root.replace(value).is_some() {
                    bail!("--package may be supplied only once");
                }
            }
            "--forbid-effect" => {
                forbidden_effects.push(
                    cursor
                        .require("--forbid-effect requires an effect name")?
                        .to_owned(),
                );
            }
            "--allow-effect" => {
                allowed_effects.push(
                    cursor
                        .require("--allow-effect requires an effect name")?
                        .to_owned(),
                );
            }
            "--json" => json = true,
            other => bail!("unknown verify-cert option `{other}`"),
        }
    }

    let cert_path =
        cert_path.ok_or_else(|| anyhow::anyhow!("`verify-cert` requires --cert <path>"))?;
    if package_root.is_some() && source_path.is_some() {
        bail!("verify-cert --package and --source are mutually exclusive");
    }
    if package_root.is_some()
        && (wasm_path.is_some() || !forbidden_effects.is_empty() || !allowed_effects.is_empty())
    {
        bail!(
            "verify-cert --package cannot be combined with --wasm, --forbid-effect, or --allow-effect"
        );
    }
    let (source_name, source_text) = if package_root.is_some() {
        (String::new(), String::new())
    } else {
        let source_path = source_path.ok_or_else(|| {
            anyhow::anyhow!("`verify-cert` requires --source <path> or --package <root>")
        })?;
        let source_text = fs::read_to_string(&source_path)
            .with_context(|| format!("failed to read source file `{source_path}`"))?;
        (source_path, source_text)
    };

    Ok(Command::VerifyCert(VerifyCertCommand {
        source_name,
        source_text,
        cert_path,
        wasm_path,
        forbidden_effects,
        allowed_effects,
        package_root,
        json,
    }))
}

#[cfg(test)]
mod multi_file_cli_tests {
    //! Wall 5 Step 1 / commit #3: parse_path_command admits N positional
    //! file paths and a `--entry <module>` flag. Tests exercise the
    //! arg-parsing surface directly; end-to-end multi-file compilation
    //! is covered by sigil-compiler's compile_project tests.

    use super::{Command, CommandKind, CompileCommand, parse_path_command};

    use std::fs;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    static TEST_DIR_COUNTER: AtomicU64 = AtomicU64::new(0);

    fn check_args(command: Command) -> CompileCommand {
        match command {
            Command::Check(args) => args,
            other => panic!("expected check command, got {other:?}"),
        }
    }

    /// Marker for a temp dir created for one test. Drop removes the
    /// directory tree. No external dep (avoids adding `tempfile` purely
    /// for tests).
    struct TempDir {
        path: PathBuf,
    }

    impl TempDir {
        fn new() -> Self {
            let id = TEST_DIR_COUNTER.fetch_add(1, Ordering::SeqCst);
            let path = std::env::temp_dir().join(format!(
                "sigil_wall5_test_{}_{}",
                std::process::id(),
                id
            ));
            fs::create_dir_all(&path).expect("create temp dir");
            Self { path }
        }

        fn path(&self) -> &std::path::Path {
            &self.path
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    /// Spin up a temp directory with the given (name, text) source
    /// files. Returned paths are absolute strings that
    /// `parse_path_command` can read.
    fn write_temp_sources(files: &[(&str, &str)]) -> (TempDir, Vec<String>) {
        let dir = TempDir::new();
        let mut paths = Vec::with_capacity(files.len());
        for (name, text) in files {
            let p = dir.path().join(name);
            fs::write(&p, text).expect("write temp source");
            paths.push(p.to_string_lossy().to_string());
        }
        (dir, paths)
    }

    /// Single-file invocation: source_files stays empty (legacy path).
    #[test]
    fn single_file_routes_legacy_path() {
        let (_dir, paths) = write_temp_sources(&[("one.sigil", "module one;\n")]);
        let mut args = vec!["check".to_string()];
        args.extend(paths);
        let cmd =
            parse_path_command(&args, "check", CommandKind::Check).expect("single file parses");
        let cmd = check_args(cmd);
        assert!(
            cmd.source_files.is_empty(),
            "single-file invocation must leave source_files empty for legacy dispatch"
        );
        assert!(!cmd.source_text.is_empty());
        assert!(cmd.entry_module.is_none());
    }

    /// Multi-file: source_files populated with all (path, text) pairs.
    #[test]
    fn multi_file_populates_source_files() {
        let (_dir, paths) = write_temp_sources(&[
            ("a.sigil", "module a;\n"),
            ("b.sigil", "module b;\n"),
            ("c.sigil", "module c;\n"),
        ]);
        let mut args = vec!["check".to_string()];
        args.extend(paths);
        let cmd =
            parse_path_command(&args, "check", CommandKind::Check).expect("multi-file parses");
        let cmd = check_args(cmd);
        assert_eq!(cmd.source_files.len(), 3);
        // source_text is the project sentinel for multi-file.
        assert_eq!(cmd.source_text, "");
        assert_eq!(cmd.source_name, "<project>");
    }

    /// `--entry <module>` is captured and surfaced on the Command.
    #[test]
    fn entry_flag_captured() {
        let (_dir, paths) =
            write_temp_sources(&[("a.sigil", "module a;\n"), ("b.sigil", "module b;\n")]);
        let mut args = vec!["check".to_string(), "--entry".to_string(), "a".to_string()];
        args.extend(paths);
        let cmd =
            parse_path_command(&args, "check", CommandKind::Check).expect("entry flag parses");
        let cmd = check_args(cmd);
        assert_eq!(cmd.entry_module.as_deref(), Some("a"));
    }

    /// `--entry` with no value bails.
    #[test]
    fn entry_flag_without_value_fails() {
        let args = vec!["check".to_string(), "--entry".to_string()];
        let err =
            parse_path_command(&args, "check", CommandKind::Check).expect_err("missing value");
        assert!(
            err.to_string().contains("--entry requires"),
            "expected --entry error: {err}"
        );
    }

    /// Zero paths → existing error path.
    #[test]
    fn zero_paths_fail() {
        let args = vec!["check".to_string()];
        let err = parse_path_command(&args, "check", CommandKind::Check)
            .expect_err("at least one path required");
        assert!(
            err.to_string().contains("requires at least one file path"),
            "expected required-path error: {err}"
        );
    }

    /// File-read failure surfaces a clear error referencing the missing path.
    #[test]
    fn nonexistent_file_fails() {
        let args = vec![
            "check".to_string(),
            "definitely_does_not_exist_xyz.sigil".to_string(),
        ];
        let err =
            parse_path_command(&args, "check", CommandKind::Check).expect_err("nonexistent file");
        assert!(
            err.to_string().contains("definitely_does_not_exist_xyz"),
            "expected path in error: {err}"
        );
    }

    /// Existing single-file flags (--wat, --json, --emit-wasm, --cert,
    /// --build-deadline) continue to work alongside multi-file paths.
    #[test]
    fn flags_compose_with_multi_file() {
        let (_dir, paths) =
            write_temp_sources(&[("a.sigil", "module a;\n"), ("b.sigil", "module b;\n")]);
        let mut args = vec![
            "check".to_string(),
            "--json".to_string(),
            "--build-deadline".to_string(),
            "1000".to_string(),
        ];
        args.extend(paths);
        let cmd = parse_path_command(&args, "check", CommandKind::Check)
            .expect("flag composition parses");
        let cmd = check_args(cmd);
        assert!(cmd.json);
        assert_eq!(cmd.build_deadline, Some(1000));
        assert_eq!(cmd.source_files.len(), 2);
    }

    /// Multi-file with --emit-wasm reaches the wasm-out path field.
    #[test]
    fn emit_wasm_with_multi_file() {
        let (_dir, paths) =
            write_temp_sources(&[("a.sigil", "module a;\n"), ("b.sigil", "module b;\n")]);
        let mut args = vec![
            "check".to_string(),
            "--emit-wasm".to_string(),
            "out.wasm".to_string(),
        ];
        args.extend(paths);
        let cmd = parse_path_command(&args, "check", CommandKind::Check)
            .expect("--emit-wasm + multi-file parses");
        let cmd = check_args(cmd);
        assert_eq!(cmd.wasm_out_path, Some(PathBuf::from("out.wasm")));
        assert_eq!(cmd.source_files.len(), 2);
    }
}
