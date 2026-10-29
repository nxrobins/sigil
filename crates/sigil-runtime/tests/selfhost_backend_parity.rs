//! SHP-0 — the never-diverge gate for the self-compiled compiler
//! (`docs/specs/self-host-backend-parity.md`, docs/CLAIMS.md claim 54).
//!
//! Every program the production compiler accepts in the gated corpora is compiled twice: by
//! production `compile_module`, and by the committed self-compiled compiler
//! (`seed/sigil-seed.wasm`, whose `tool_main` runs lex → parse → mn_expand → the seven gates →
//! emit). The self-hosted result must be byte-identical or a refusal. A DIFFERENT module is the
//! one forbidden outcome: it is a plausible artifact that is not the program production
//! certifies. Both compile one input: the seed is handed the program production compiled, its
//! source followed by every ambient stdlib module production injected, in production's order
//! (SHP-3), and production's stages (the chain the seed mirrors, plus the effect desugar) are
//! shown compiling that text to production's modules. Today's divergences are pinned as an exact
//! label set that may only shrink (`SHP_KNOWN_DIVERGENT`); every other verdict class is pinned or
//! floored below.
//!
//! The seed, not a test-time build of `selfhost/`, is the compiler under test: it is the committed
//! self-compiled compiler the lineage claims (38–40) rest on, and
//! `seed_is_the_oracle_emit_of_the_certified_source` already holds it byte-equal to the oracle's
//! build of the current certified source on every green commit.
//!
//! Load-bearing constraint: this runs in the default `test` lane, a required check, because the
//! whole sweep takes seconds (about half the programs stop at the seed's own gate chain). Do not
//! move it behind a feature: a gated proof needs a lane and a fence of its own to keep running
//! (see `interp_ddc_lane_is_wired_in_ci`), and this one needs neither.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use proc_macro2::{Delimiter, TokenStream, TokenTree};
use sha2::{Digest, Sha256};
use sigil_compiler::{Compilation, compile_module};
use sigil_runtime::execute_ephemeral_with_memory_budget;
use sigil_runtime::grants::IoGrants;

/// The self-compiled SIGIL compiler: the certified with-driver artifact (claims 36–38).
const SEED: &[u8] = include_bytes!("../../../seed/sigil-seed.wasm");
/// The F corpus roots are read from the parity manifest's own list, so the two cannot drift.
const PARITY_MANIFEST_RS: &str = include_str!("../../sigil-compiler/tests/parity_manifest.rs");
/// Production's intrinsic names are read from its own resolver, so the seed's list cannot drift.
const INTRINSICS_RS: &str =
    include_str!("../../sigil-compiler/src/type_check/expressions/intrinsics.rs");
/// The self-hosted compile budget: the SELF-4 ceilings the executed-artifact tests use.
const SEED_FUEL: u64 = 10_000_000_000;
const SEED_MEMORY: usize = 512 * 1024 * 1024;

// ── Pins (mirrored in docs/CLAIMS.md §A; prose cites the names, never the numbers) ───────────

/// Programs whose self-hosted module differs from production's on the same input. Shrink-only: a
/// fix removes its label in the same commit; a new label is a regression to fix or fence, never
/// to append.
const SHP_KNOWN_DIVERGENCES: usize = 0;
const SHP_KNOWN_DIVERGENT: &[&str] = &[];
/// A floor on the programs production expands with ambient stdlib modules (SHP-3), each handed to
/// the seed as the whole program production compiled: the expanded path is not vacuous.
const SHP_EXPANDED_FLOOR: usize = 173;
/// Programs on which the self-hosted compiler traps or exhausts its budget instead of answering.
const SHP_TRAPS: &[&str] = &[];
/// Programs on which production `compile_module` itself panics: an internal compiler error, out
/// of the gate's scope like a rejection, but a production bug, so pinned shrink-only rather than
/// ignored. A new label is a new production crash to fix, never to append.
const SHP_ORACLE_PANICS: &[&str] = &[];
/// Floors on byte-identical programs per corpus (rise freely; lowering one is a reviewed act).
const SHP_IDENTICAL_FLOOR_F: usize = 54;
const SHP_IDENTICAL_FLOOR_T: usize = 180;
const SHP_IDENTICAL_FLOOR_X: usize = 365;
/// Floors on production-accepted programs per corpus: the gate is not vacuous.
const SHP_CORPUS_FLOOR_F: usize = 218;
const SHP_CORPUS_FLOOR_T: usize = 183;
const SHP_CORPUS_FLOOR_X: usize = 647;
/// SHP-5b: the production AIR statement kinds at least one Identical program carries, a
/// grow-only set (its size is the §A mirror). A kind leaving it means the emitter stopped
/// reproducing a construct it reproduced, named by the kind; a kind with Identical programs the
/// set lacks is a pin to raise (`shp5b_identical_kinds_cover_the_pinned_set` prints it).
const SHP_IDENTICAL_KINDS_COUNT: usize = 28;
const SHP_IDENTICAL_KINDS: &[&str] = &[
    "Assign",
    "Borrow",
    "BumpAlloc",
    "Call",
    "CapDraw",
    "CapRestrict",
    "CapSplit",
    "ExtendU32",
    "ExternCall",
    "FuelDecrement",
    "IntrinsicAlloc",
    "IntrinsicCtEq",
    "IntrinsicCtLt",
    "IntrinsicCtSelect",
    "IntrinsicLoad8",
    "IntrinsicStore8",
    "LoadDynamic",
    "LoadField",
    "RegionBegin",
    "RegionEnd",
    "SecurityRelease",
    "SlotNew",
    "SlotPut",
    "SlotTake",
    "StoreDynamic",
    "StoreField",
    "TrapIf",
    "WrapI64",
];

// ── Verdicts ─────────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Verdict {
    /// The self-hosted module equals production's, byte for byte.
    Identical,
    /// The self-hosted emitter returned its `!!` poison marker: an explicit refusal.
    Poison,
    /// The self-hosted gate chain rejected the program (`REJECT:`): also a refusal.
    Refused,
    /// The self-hosted compiler trapped or ran out of budget instead of answering.
    Trap,
    /// The self-hosted compiler returned a module that is not production's. Forbidden.
    Diverge,
}

/// Classify one self-hosted answer against production's output. Pure, so the anti-stubs below
/// can feed it planted answers. Fails closed: anything that is not a well-formed refusal or an
/// exact match is a divergence, including malformed output, a single module where production
/// emits two, and two where it emits one. A two-ring answer takes the protocol's superset form
/// `OK:{inner}|{outer}` (SHP-2b), and both modules must match production's, in that order; a
/// single-ring answer is `OK:{hex}`, unchanged. The refusal forms are exact: `OK:!!` and nothing
/// after the marker, or `REJECT:` in the grammar `is_refusal` reads.
fn classify(inner: &[u8], outer: Option<&[u8]>, answer: &Result<String, String>) -> Verdict {
    let out = match answer {
        Ok(out) => out,
        Err(_) => return Verdict::Trap,
    };
    if let Some(rest) = out.strip_prefix("REJECT:") {
        return if is_refusal(rest) {
            Verdict::Refused
        } else {
            Verdict::Diverge
        };
    }
    let Some(body) = out.strip_prefix("OK:") else {
        return Verdict::Diverge;
    };
    if body == "!!" {
        return Verdict::Poison;
    }
    // One module, or exactly two around a single `|`; each half is a strict hex decode.
    let halves: Vec<&str> = body.split('|').collect();
    if halves.len() > 2 {
        return Verdict::Diverge;
    }
    let mut modules = Vec::new();
    for half in &halves {
        let Some(bytes) = decode_hex(half) else {
            return Verdict::Diverge;
        };
        modules.push(bytes);
    }
    let matches = match (outer, modules.as_slice()) {
        (None, [one]) => one.as_slice() == inner,
        (Some(o), [i, ou]) => i.as_slice() == inner && ou.as_slice() == o,
        _ => false,
    };
    if matches {
        Verdict::Identical
    } else {
        Verdict::Diverge
    }
}

/// The stages `sh_compile` (`selfhost/pipeline.sigil`) refuses at, one per gate.
const SH_REJECT_STAGES: &[&str] = &["nr", "tc", "ring", "effect", "taint", "cap", "own"];

/// The text after `REJECT:` as the pipeline writes it: a known stage, `:`, then one or more
/// `;`-terminated entries, each a code (letters, digits, `_`) optionally followed by
/// `,`-separated decimal fields (the tc stream's `code,start,end` spans). Anything else, a
/// newline or a lossily decoded byte included, is not a refusal the pipeline can produce.
fn is_refusal(rest: &str) -> bool {
    let Some((stage, entries)) = rest.split_once(':') else {
        return false;
    };
    let Some(body) = entries.strip_suffix(';') else {
        return false;
    };
    SH_REJECT_STAGES.contains(&stage)
        && body.split(';').all(|entry| {
            let mut fields = entry.split(',');
            let code_ok = fields.next().is_some_and(|code| {
                !code.is_empty() && code.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
            });
            code_ok && fields.all(|f| !f.is_empty() && f.bytes().all(|b| b.is_ascii_digit()))
        })
}

/// Strict lowercase-or-uppercase hex decode; `None` on odd length or any non-hex byte.
fn decode_hex(hex: &str) -> Option<Vec<u8>> {
    let b = hex.as_bytes();
    if !b.len().is_multiple_of(2) {
        return None;
    }
    b.chunks(2)
        .map(|p| {
            let hi = (p[0] as char).to_digit(16)?;
            let lo = (p[1] as char).to_digit(16)?;
            Some((hi * 16 + lo) as u8)
        })
        .collect()
}

/// Lowercase hex, the protocol's module transport.
fn to_hex(m: &[u8]) -> String {
    m.iter().map(|b| format!("{b:02x}")).collect()
}

// ── Corpora ──────────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Corpus {
    /// The parity-manifest roots plus the Z3 corpus.
    F,
    /// The agent tool programs in `tools/`.
    T,
    /// SIGIL programs extracted from string literals in `crates/*/tests`.
    X,
}

struct Program {
    corpus: Corpus,
    label: String,
    source: String,
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("sigil-runtime lives under crates/")
        .to_path_buf()
}

/// The `ROOTS` list of `parity_manifest.rs`, parsed from its source text.
fn parity_roots() -> Vec<String> {
    let start = PARITY_MANIFEST_RS
        .find("const ROOTS: &[&str] = &[")
        .expect("parity_manifest.rs still declares ROOTS");
    let body = &PARITY_MANIFEST_RS[start..];
    let end = body.find("];").expect("ROOTS list is closed");
    body[..end]
        .lines()
        .skip(1)
        .filter_map(|l| {
            let l = l.trim();
            l.strip_prefix('"')
                .and_then(|r| r.split_once('"'))
                .map(|(s, _)| s.to_string())
        })
        .collect()
}

/// Every file under `dir` with extension `ext`, in sorted order. Fails closed: a directory or
/// entry it cannot read panics, naming it, rather than shrinking a corpus without a word.
fn walk(dir: &Path, ext: &str, out: &mut Vec<PathBuf>) {
    let rd = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read corpus directory {}: {e}", dir.display()));
    let mut entries: Vec<PathBuf> = rd
        .map(|e| {
            e.unwrap_or_else(|e| panic!("cannot read an entry of {}: {e}", dir.display()))
                .path()
        })
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            walk(&p, ext, out);
        } else if p.extension().is_some_and(|x| x == ext) {
            out.push(p);
        }
    }
}

fn rel(root: &Path, p: &Path) -> String {
    p.strip_prefix(root)
        .expect("walked path is under the repository root")
        .to_string_lossy()
        .replace('\\', "/")
}

fn read_source(p: &Path) -> String {
    std::fs::read_to_string(p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

/// The `.sigil` programs under `dirs`. Fails closed: a root that does not exist panics (a renamed
/// corpus directory must be renamed here or in `parity_manifest.rs`'s `ROOTS`, never silently
/// dropped), and so does a file that cannot be read.
fn file_programs(root: &Path, dirs: &[String], corpus: Corpus) -> Vec<Program> {
    let mut paths = Vec::new();
    for d in dirs {
        let dir = root.join(d);
        assert!(
            dir.is_dir(),
            "{corpus:?} corpus root {d} does not exist: rename it here or in parity_manifest.rs \
             ROOTS, never drop it"
        );
        walk(&dir, "sigil", &mut paths);
    }
    paths.sort();
    paths.dedup();
    paths
        .into_iter()
        .map(|p| Program {
            corpus,
            label: rel(root, &p),
            source: read_source(&p),
        })
        .collect()
}

/// Test sources whose embedded programs are NOT evidence of general parity: the self-host
/// differential suites are curated to the self-hosted surface, so sampling them would inflate
/// the identical count. This file is excluded because its anti-stub programs are planted.
fn x_excluded(file_name: &str) -> bool {
    file_name.ends_with("_differential.rs")
        || file_name == "selfhost_self_census.rs"
        || file_name == "selfhost_backend_parity.rs"
}

/// Every label the pins name, across all three pinned sets.
fn pinned_labels() -> BTreeSet<&'static str> {
    SHP_KNOWN_DIVERGENT
        .iter()
        .chain(SHP_TRAPS)
        .chain(SHP_ORACLE_PANICS)
        .copied()
        .collect()
}

/// The X corpus: every program extracted from `crates/*/tests/**/*.rs`. Fails closed like
/// `walk`: an unreadable crate list or test file panics. A crate with no `tests/` directory
/// holds no test sources, so it contributes nothing.
fn x_programs(root: &Path) -> Vec<Program> {
    let crates_dir = root.join("crates");
    let mut crates: Vec<PathBuf> = std::fs::read_dir(&crates_dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", crates_dir.display()))
        .map(|e| {
            e.unwrap_or_else(|e| panic!("cannot read an entry of {}: {e}", crates_dir.display()))
                .path()
        })
        .collect();
    crates.sort();
    let mut files = Vec::new();
    for c in crates {
        let tests = c.join("tests");
        if tests.is_dir() {
            walk(&tests, "rs", &mut files);
        }
    }
    let sources: Vec<(String, String)> = files
        .iter()
        .filter(|f| {
            f.file_name()
                .is_some_and(|n| !x_excluded(&n.to_string_lossy()))
        })
        .map(|f| (rel(root, f), read_source(f)))
        .collect();
    label_x_programs(&sources, &pinned_labels())
}

/// Deduplicate the programs extracted from `files` (path, text; in walk order) and label each
/// `{file}#{first four bytes of its SHA-256}`. The file is the first, in walk order, that holds
/// the program, unless a pinned label names another file that also holds it: the pin then keeps
/// its label. Otherwise a new test file that sorts earlier and holds a verbatim copy of a pinned
/// program would relabel the pin, and the gate would report a new divergence when no compiler
/// changed. A pin whose file no longer holds its program does move, and the gate says so.
fn label_x_programs(files: &[(String, String)], pinned: &BTreeSet<&str>) -> Vec<Program> {
    let mut first_seen: Vec<String> = Vec::new();
    let mut holders: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for (file, text) in files {
        for program in extract_programs(file, text) {
            holders
                .entry(program)
                .or_insert_with_key(|p| {
                    first_seen.push(p.clone());
                    Vec::new()
                })
                .push(file);
        }
    }
    first_seen
        .into_iter()
        .map(|program| {
            let hash = program_hash(&program);
            let held_by = &holders[&program];
            let label = held_by
                .iter()
                .map(|f| format!("{f}#{hash}"))
                .find(|l| pinned.contains(l.as_str()))
                .unwrap_or_else(|| format!("{}#{hash}", held_by[0]));
            Program {
                corpus: Corpus::X,
                label,
                source: program,
            }
        })
        .collect()
}

/// The first four bytes of a program's SHA-256, in hex: the content half of an X label.
fn program_hash(program: &str) -> String {
    Sha256::digest(program.as_bytes())[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Does a string literal look like a whole SIGIL program: optional comment and attribute lines,
/// then a `module <name>;` header, and at least one function?
fn looks_like_program(lit: &str) -> bool {
    if !lit.contains("fn ") {
        return false;
    }
    let mut rest = lit.trim_start();
    loop {
        if let Some(r) = rest.strip_prefix("//") {
            rest = r.split_once('\n').map_or("", |(_, t)| t).trim_start();
        } else if rest.starts_with("#[") {
            rest = rest.split_once(']').map_or("", |(_, t)| t).trim_start();
        } else {
            break;
        }
    }
    let Some(r) = rest.strip_prefix("module") else {
        return false;
    };
    let r = r.trim_start();
    let name_len = r
        .bytes()
        .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
        .count();
    name_len > 0 && r[name_len..].trim_start().starts_with(';')
}

/// Every string literal in a Rust source that looks like a whole SIGIL program. Rust's own
/// tokenizer (`proc_macro2`) reads the file, so comments (nested ones included), char literals
/// and lifetimes never hide or fake a literal, and `syn` decodes each string literal's value:
/// escapes, line continuations, raw strings with any number of `#`. Byte and C strings are
/// skipped, and so are doc comments, which reach the tokens as `#[doc = "..."]` attributes.
/// `format!` templates have their doubled braces undone; any placeholder left behind makes the
/// program fail to compile, which takes it out of scope rather than into the gate. Fails
/// closed: a file the tokenizer cannot read panics, naming it, because skipping it would drop
/// every program it holds out of X without a word.
fn extract_programs(file: &str, text: &str) -> Vec<String> {
    let tokens = TokenStream::from_str(text)
        .unwrap_or_else(|e| panic!("{file} does not tokenize as Rust ({e:?}); X cannot read it"));
    let mut out = Vec::new();
    collect_programs(tokens, &mut out);
    out
}

fn collect_programs(tokens: TokenStream, out: &mut Vec<String>) {
    // True right after `#` or `#!`: the next bracket group is an attribute.
    let mut after_hash = false;
    for tt in tokens {
        let attribute = after_hash;
        after_hash = false;
        match tt {
            TokenTree::Punct(p) if p.as_char() == '#' => after_hash = true,
            TokenTree::Punct(p) if p.as_char() == '!' => after_hash = attribute,
            TokenTree::Group(g) => {
                let doc = attribute
                    && g.delimiter() == Delimiter::Bracket
                    && g.stream().into_iter().next().is_some_and(
                        |first| matches!(first, TokenTree::Ident(ref i) if i == "doc"),
                    );
                if !doc {
                    collect_programs(g.stream(), out);
                }
            }
            TokenTree::Literal(lit) => {
                if let syn::Lit::Str(s) = syn::Lit::new(lit) {
                    push_program(s.value(), out);
                }
            }
            _ => {}
        }
    }
}

fn push_program(lit: String, out: &mut Vec<String>) {
    let lit = if lit.contains("{{") {
        lit.replace("{{", "{").replace("}}", "}")
    } else {
        lit
    };
    if looks_like_program(&lit) {
        out.push(lit);
    }
}

// ── The sweep ────────────────────────────────────────────────────────────────────────────────

struct Row {
    corpus: Corpus,
    label: String,
    verdict: Verdict,
    /// Production compiled ambient stdlib modules besides the source (SHP-3).
    expanded: bool,
    /// The stage chain compiles the text the seed was handed to production's exact modules.
    /// Checked on every expanded program; true by construction for a source compiled alone.
    chain_agrees: bool,
    /// The production AIR statement kinds the program lowers to (SHP-5b's census).
    kinds: BTreeSet<String>,
    /// The seed's refusing stage (`REJECT:<stage>:`), `poison` for the emitter's marker, else empty.
    stage: String,
}

enum Outcome {
    /// Production rejected the program: out of the gate's scope.
    OracleReject,
    /// Production panicked: out of scope, but pinned exactly (`SHP_ORACLE_PANICS`).
    OraclePanic,
    Judged(Row),
}

fn run_seed(source: &str) -> Result<String, String> {
    match execute_ephemeral_with_memory_budget(
        SEED,
        source.as_bytes(),
        SEED_FUEL,
        SEED_MEMORY,
        &IoGrants::none(),
    ) {
        // Lossy, not strict: output that is not UTF-8 is a protocol violation, and decoding it
        // lossily hands `classify` text it cannot read as a refusal or a module — a divergence,
        // which fails closed. A strict decode would have filed it as a trap instead.
        Ok(r) => Ok(String::from_utf8_lossy(&r.output).into_owned()),
        Err(e) => Err(format!("{e}")),
    }
}

/// The program production compiled (SHP-3): every file of its source map, in the map's order,
/// joined by a newline. `compile_module` hands production one source, and its source map grows
/// past that one only when the ambient include adds stdlib files
/// (`apply_ambient_includes_with_count`); production then sorts the files by name, so the source
/// (`<inline>`) comes first and the stdlib files follow in path order. A source compiled alone
/// comes back unchanged.
fn production_input(compilation: &Compilation) -> String {
    let files: Vec<&str> = compilation
        .sources
        .files()
        .iter()
        .map(|f| f.text())
        .collect();
    files.join("\n")
}

/// The modules production's stages make of `text`, or the first stage's error: parse, resolve,
/// type check, the effect desugar, AIR, memory, fuel and emit. That is the chain the seed mirrors
/// (`oracle_compile` in `pipeline_differential.rs`, without its gates) plus the effect desugar,
/// the one pass outside it that changes the bytes `compile_module` emits (handlers are SHP-8).
/// With it the check measures the text the seed is handed, not the seed's coverage: a handler
/// program production expands compiles here as production compiles it.
fn stage_chain(text: &str) -> Result<(Vec<u8>, Option<Vec<u8>>), String> {
    stage_chain_with(text, true)
}

/// `stage_chain`, with the effect desugar run or skipped. Skipped, it is the chain the seed
/// mirrors, which the anti-stub of `shp3_production_stages_include_the_effect_desugar` runs to show
/// the desugar is needed.
fn stage_chain_with(text: &str, desugar: bool) -> Result<(Vec<u8>, Option<Vec<u8>>), String> {
    use sigil_compiler::{
        CompileOptions, air, effect_desugar, fuel, memory, name_resolution, parser,
        source::SourceFile, type_check, wasm,
    };
    let codes = |ds: &[sigil_compiler::Diagnostic]| -> Vec<String> {
        ds.iter().map(|d| d.code().to_string()).collect()
    };
    let (ast, parse_diags) = parser::parse(&SourceFile::new("<expanded>", text));
    if !parse_diags.is_empty() {
        return Err(format!("parse: {:?}", codes(&parse_diags)));
    }
    let resolved = name_resolution::resolve(&ast).map_err(|ds| format!("nr: {:?}", codes(&ds)))?;
    let (mut typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .map_err(|ds| format!("tc: {:?}", codes(&ds)))?;
    if desugar {
        effect_desugar::desugar_effect_handlers(&mut typed);
    }
    let (memory_lowered, _) = memory::lower(air::lower(&typed));
    let (fuelled, _) = fuel::insert(memory_lowered);
    let out = wasm::emit(&fuelled);
    Ok((out.inner, out.outer))
}

/// Whether production's stages compile `text` to exactly production's modules. A stage that
/// panics counts as a miss (fails closed), so the gate names the program instead of aborting the
/// sweep.
fn chain_matches(compilation: &Compilation, text: &str) -> bool {
    matches!(
        catch_unwind(AssertUnwindSafe(|| stage_chain(text))),
        Ok(Ok((inner, outer))) if inner == compilation.wasm_inner && outer == compilation.wasm_outer
    )
}

fn judge(p: &Program) -> Outcome {
    let production = catch_unwind(AssertUnwindSafe(|| compile_module(&p.source)));
    let compilation = match production {
        Err(_) => return Outcome::OraclePanic,
        Ok(Err(_)) => return Outcome::OracleReject,
        Ok(Ok(c)) => c,
    };
    // SHP-3: both compilers compile one input. A program production expanded is handed to the
    // seed whole, and production's stages must compile that text to production's modules, or a
    // divergence on it could be the expansion's rather than the seed's.
    let input = production_input(&compilation);
    let expanded = compilation.sources.len() > 1;
    let chain_agrees = !expanded || chain_matches(&compilation, &input);
    let kinds = air_statement_kinds(&compilation.air);
    let answer = run_seed(&input);
    let stage = match &answer {
        Ok(text) if text.starts_with("REJECT:") => text["REJECT:".len()..]
            .split(':')
            .next()
            .unwrap_or("")
            .to_string(),
        Ok(text) if text.contains("!!") => "poison".to_string(),
        _ => String::new(),
    };
    let verdict = classify(
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        &answer,
    );
    Outcome::Judged(Row {
        corpus: p.corpus,
        label: p.label.clone(),
        verdict,
        expanded,
        chain_agrees,
        kinds,
        stage,
    })
}

/// The AIR statement kinds a production compilation contains, one name per variant, read from
/// the `Debug` form's leading identifier so a new variant needs no arm here.
fn air_statement_kinds(air: &sigil_compiler::air::AirProgram) -> BTreeSet<String> {
    let mut kinds = BTreeSet::new();
    for function in &air.functions {
        for block in &function.blocks {
            for stmt in &block.stmts {
                let debug = format!("{stmt:?}");
                let name = debug
                    .split(|c: char| !c.is_ascii_alphanumeric())
                    .next()
                    .unwrap_or("");
                kinds.insert(name.to_string());
            }
        }
    }
    kinds
}

/// Every program the gate judges: the parity roots and the Z3 corpus as F, `tools/` as T, and
/// the programs embedded in test files as X.
fn gate_programs(root: &Path) -> Vec<Program> {
    let mut f_dirs = parity_roots();
    assert!(
        f_dirs.len() >= 9,
        "parsed only {} parity roots — the ROOTS parser broke",
        f_dirs.len()
    );
    f_dirs.push("crates/sigil-compiler/tests/z3_corpus".to_string());
    let mut programs = file_programs(root, &f_dirs, Corpus::F);
    programs.extend(file_programs(root, &["tools".to_string()], Corpus::T));
    programs.extend(x_programs(root));
    programs
}

/// SHP-5b: the production AIR statement kinds behind each verdict class, and the pin on the kinds
/// Identical programs carry. For every kind, how many programs containing it came out Identical,
/// Poison, Refused or Trap (the slice's instrument: a kind with Identical programs is one the
/// emitter reproduces somewhere, one with none a construct refused everywhere); every kind in
/// `SHP_IDENTICAL_KINDS` must still have an Identical program, and a kind with one the pin lacks
/// is printed for the next pin. For the kinds the slice targets, the label and stage behind every
/// non-Identical verdict follow. Anti-stub (SC-P4): the comparator is shown reporting a planted
/// kind no program carries, and a kind removed from the measured set, each by name.
#[test]
fn shp5b_identical_kinds_cover_the_pinned_set() {
    assert_eq!(
        SHP_IDENTICAL_KINDS.len(),
        SHP_IDENTICAL_KINDS_COUNT,
        "the pinned kind set and its count (the §A mirror) must agree"
    );
    let (rows, panics) = gate_sweep();
    assert!(panics.is_empty(), "the sweep panicked: {panics:?}");
    let kinds: BTreeSet<&str> = rows
        .iter()
        .flat_map(|r| r.kinds.iter().map(String::as_str))
        .collect();
    let n = |kind: &str, v: Verdict| {
        rows.iter()
            .filter(|r| r.verdict == v && r.kinds.contains(kind))
            .count()
    };
    println!("kind                      identical  poison  refused  trap");
    for kind in &kinds {
        println!(
            "{kind:<25} {:>9}  {:>6}  {:>7}  {:>4}",
            n(kind, Verdict::Identical),
            n(kind, Verdict::Poison),
            n(kind, Verdict::Refused),
            n(kind, Verdict::Trap)
        );
    }
    let identical: BTreeSet<String> = rows
        .iter()
        .filter(|r| r.verdict == Verdict::Identical)
        .flat_map(|r| r.kinds.iter().cloned())
        .collect();
    let missing = kinds_missing_from(SHP_IDENTICAL_KINDS, &identical);
    assert!(
        missing.is_empty(),
        "SHP-5b: pinned AIR statement kinds with no Identical program left: {missing:?}. The \
         emitter stopped reproducing a construct it reproduced: fix it, or lower the pin as a \
         reviewed act."
    );
    let unpinned: Vec<&str> = identical
        .iter()
        .map(String::as_str)
        .filter(|k| !SHP_IDENTICAL_KINDS.contains(k))
        .collect();
    if !unpinned.is_empty() {
        println!(
            "kinds with Identical programs the pin does not name yet (raise SHP_IDENTICAL_KINDS): {unpinned:?}"
        );
    }
    // Anti-stubs: a planted pin no program carries, and a kind taken out of the measured set.
    let planted_pin: Vec<&str> = SHP_IDENTICAL_KINDS
        .iter()
        .copied()
        .chain(["PlantedKind"])
        .collect();
    assert_eq!(
        kinds_missing_from(&planted_pin, &identical),
        vec!["PlantedKind"],
        "anti-stub: a pinned kind no Identical program carries is reported by name"
    );
    let mut without_release = identical.clone();
    without_release.remove("SecurityRelease");
    assert_eq!(
        kinds_missing_from(SHP_IDENTICAL_KINDS, &without_release),
        vec!["SecurityRelease"],
        "anti-stub: a kind removed from the measured set is reported by name"
    );
    for kind in [
        "Borrow",
        "SecurityRelease",
        "RegionBegin",
        "RegionEnd",
        "SlotNew",
        "SlotPut",
        "SlotTake",
        "CapRestrict",
        "CapSplit",
        "CapDraw",
        "CapMint",
        "GrantBegin",
        "GrantEnd",
    ] {
        for row in rows
            .iter()
            .filter(|r| r.kinds.contains(kind) && r.verdict != Verdict::Identical)
        {
            let others: Vec<&str> = row.kinds.iter().map(String::as_str).collect();
            println!(
                "TARGET {kind} {:?} {:?} stage={} {} kinds={}",
                row.corpus,
                row.verdict,
                row.stage,
                row.label,
                others.join(",")
            );
        }
    }
}

/// The pinned kinds `seen` lacks, in pin order.
fn kinds_missing_from<'a>(pinned: &[&'a str], seen: &BTreeSet<String>) -> Vec<&'a str> {
    pinned
        .iter()
        .copied()
        .filter(|k| !seen.contains(*k))
        .collect()
}

/// The sweep over every gated program, run once per test binary and shared by the tests that
/// read it (the divergence gate and the kind census), so the corpus is judged once.
fn gate_sweep() -> &'static (Vec<Row>, Vec<String>) {
    static SWEEP: OnceLock<(Vec<Row>, Vec<String>)> = OnceLock::new();
    SWEEP.get_or_init(|| {
        let root = repo_root();
        let programs = gate_programs(&root);
        sweep(&programs)
    })
}

fn sweep(programs: &[Program]) -> (Vec<Row>, Vec<String>) {
    let next = AtomicUsize::new(0);
    let rows = Mutex::new(Vec::new());
    let panics = Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism()
        .map_or(2, |n| n.get())
        .clamp(1, 8);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            std::thread::Builder::new()
                // Production's front end recurses on deep inputs; the default 2 MiB test-thread
                // stack is not a budget the compiler promises to fit in.
                .stack_size(256 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    loop {
                        let i = next.fetch_add(1, Ordering::SeqCst);
                        let Some(p) = programs.get(i) else {
                            break;
                        };
                        match judge(p) {
                            Outcome::OracleReject => {}
                            Outcome::OraclePanic => panics
                                .lock()
                                .expect("panic list lock")
                                .push(p.label.clone()),
                            Outcome::Judged(row) => rows.lock().expect("row lock").push(row),
                        }
                    }
                })
                .expect("spawn a gate worker");
        }
    });
    let mut rows = rows.into_inner().expect("row lock");
    rows.sort_by(|a, b| (a.corpus, &a.label).cmp(&(b.corpus, &b.label)));
    let mut panics = panics.into_inner().expect("panic list lock");
    panics.sort();
    (rows, panics)
}

fn count(rows: &[Row], corpus: Corpus, verdict: Option<Verdict>) -> usize {
    rows.iter()
        .filter(|r| r.corpus == corpus && verdict.is_none_or(|v| r.verdict == v))
        .count()
}

/// The pinned label that names the same X program (the same content hash) under another file.
fn pinned_twin(label: &str, pinned: &[&'static str]) -> Option<&'static str> {
    let (_, hash) = label.rsplit_once('#')?;
    pinned
        .iter()
        .copied()
        .find(|p| *p != label && p.rsplit_once('#').is_some_and(|(_, h)| h == hash))
}

/// The labels of every row with this verdict, in sweep order (corpus, then label).
fn labels(rows: &[Row], verdict: Verdict) -> Vec<&str> {
    rows.iter()
        .filter(|r| r.verdict == verdict)
        .map(|r| r.label.as_str())
        .collect()
}

/// THE GATE. The self-compiled compiler matches production or refuses on every accepted program
/// in F, T and X, given the program production compiled, except exactly the pinned divergences;
/// traps and production panics are exactly their pinned sets; every expanded program's text is
/// shown to be the program production compiled; the identical, corpus and expanded floors hold.
#[test]
fn shp_divergence_is_exactly_the_pinned_set() {
    let (rows, panics) = gate_sweep();

    println!("corpus  accepted  identical  poison  refused  trap  diverge  expanded");
    for corpus in [Corpus::F, Corpus::T, Corpus::X] {
        println!(
            "{corpus:?}       {:>8}  {:>9}  {:>6}  {:>7}  {:>4}  {:>7}  {:>8}",
            count(rows, corpus, None),
            count(rows, corpus, Some(Verdict::Identical)),
            count(rows, corpus, Some(Verdict::Poison)),
            count(rows, corpus, Some(Verdict::Refused)),
            count(rows, corpus, Some(Verdict::Trap)),
            count(rows, corpus, Some(Verdict::Diverge)),
            rows.iter()
                .filter(|r| r.corpus == corpus && r.expanded)
                .count(),
        );
    }
    let diverged = labels(rows, Verdict::Diverge);
    let trapped = labels(rows, Verdict::Trap);
    for (tag, set) in [("DIVERGE", &diverged), ("TRAP", &trapped)] {
        for label in set.iter() {
            println!("{tag} {label}");
        }
    }
    for label in panics {
        println!("ORACLE-PANIC {label}");
    }

    let unpinned: Vec<&str> = diverged
        .iter()
        .copied()
        .filter(|d| !SHP_KNOWN_DIVERGENT.contains(d))
        .collect();
    let moved: Vec<(&str, &str)> = unpinned
        .iter()
        .filter_map(|d| pinned_twin(d, SHP_KNOWN_DIVERGENT).map(|pin| (*d, pin)))
        .collect();
    assert!(
        moved.is_empty(),
        "MOVED PIN: the file a pinned divergence names no longer holds its program, which another \
         file does: {moved:?} (new label, pin). The program is unchanged and no compiler changed: \
         rename the pin to the new label in SHP_KNOWN_DIVERGENT."
    );
    let new: Vec<&str> = unpinned
        .into_iter()
        .filter(|d| pinned_twin(d, SHP_KNOWN_DIVERGENT).is_none())
        .collect();
    assert!(
        new.is_empty(),
        "NEW DIVERGENCE: the self-hosted compiler emitted a module production does not for \
         {new:?}. Mirror the production change in selfhost/ or make the self-host refuse the \
         construct, in this PR (the keep-up policy, docs/specs/self-host-backend-parity.md)."
    );
    assert_eq!(
        diverged, SHP_KNOWN_DIVERGENT,
        "the divergence set changed. A fixed divergence is a win: remove its label from \
         SHP_KNOWN_DIVERGENT and lower SHP_KNOWN_DIVERGENCES (and docs/CLAIMS.md §A) in the same \
         commit. Never append."
    );
    assert_eq!(
        diverged.len(),
        SHP_KNOWN_DIVERGENCES,
        "SHP_KNOWN_DIVERGENCES out of step"
    );
    let unfaithful: Vec<&str> = rows
        .iter()
        .filter(|r| !r.chain_agrees)
        .map(|r| r.label.as_str())
        .collect();
    assert!(
        unfaithful.is_empty(),
        "EXPANSION: the text handed to the seed is not the program production compiled for \
         {unfaithful:?}: production's stages do not compile it to production's modules. Either \
         production's ambient include or its multi-file path changed (make production_input \
         reproduce it), or production gained a pass that changes bytes and stage_chain lacks it \
         (add it there)."
    );
    let expanded = rows.iter().filter(|r| r.expanded).count();
    assert!(
        expanded >= SHP_EXPANDED_FLOOR,
        "only {expanded} programs production expands (floor {SHP_EXPANDED_FLOOR}); the ambient \
         include stopped firing or the expanded path broke"
    );
    assert_eq!(
        trapped, SHP_TRAPS,
        "the set of programs that trap the self-hosted compiler changed"
    );
    assert_eq!(
        panics, SHP_ORACLE_PANICS,
        "the set of programs on which production compile_module PANICS changed. A new label is a \
         production internal compiler error: fix it, never append it."
    );
    for (corpus, identical_floor, corpus_floor) in [
        (Corpus::F, SHP_IDENTICAL_FLOOR_F, SHP_CORPUS_FLOOR_F),
        (Corpus::T, SHP_IDENTICAL_FLOOR_T, SHP_CORPUS_FLOOR_T),
        (Corpus::X, SHP_IDENTICAL_FLOOR_X, SHP_CORPUS_FLOOR_X),
    ] {
        let accepted = count(rows, corpus, None);
        let identical = count(rows, corpus, Some(Verdict::Identical));
        assert!(
            accepted >= corpus_floor,
            "{corpus:?}: only {accepted} production-accepted programs (floor {corpus_floor}); the \
             corpus shrank or a walker broke"
        );
        assert!(
            identical >= identical_floor,
            "{corpus:?}: {identical} byte-identical programs, below the floor {identical_floor}. \
             Coverage regressed; restore it, or lower the floor with a stated reason."
        );
    }
}

// ── Anti-stubs (SC-P4): the detectors detect ─────────────────────────────────────────────────

/// The classifier must see a planted divergence, recognise both refusal forms exactly, refuse to
/// call a single module identical to a two-module production output, and treat malformed output
/// (an empty or invalid module included) and traps as what they are.
#[test]
fn shp_classifier_detects_planted_divergence() {
    // The empty module, and a different module that also validates (one empty type section).
    let module = vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
    let mut other = module.clone();
    other.extend([0x01, 0x01, 0x00]);
    // A flipped version byte: decodes as hex, fails validation.
    let mut flipped = module.clone();
    flipped[5] ^= 0x01;
    assert!(wasmparser::validate(&module).is_ok() && wasmparser::validate(&other).is_ok());
    assert!(wasmparser::validate(&flipped).is_err());
    let (hex, other_hex, flipped_hex) = (to_hex(&module), to_hex(&other), to_hex(&flipped));

    let ok = |h: &str| Ok::<String, String>(format!("OK:{h}"));
    let text = |t: &str| Ok::<String, String>(t.to_string());
    let c =
        |outer: Option<&[u8]>, answer: &Result<String, String>| classify(&module, outer, answer);
    assert_eq!(c(None, &ok(&hex)), Verdict::Identical);
    assert_eq!(c(None, &ok(&other_hex)), Verdict::Diverge);
    assert_eq!(
        c(Some(&module), &ok(&hex)),
        Verdict::Diverge,
        "one module can never stand in for production's two"
    );
    assert_eq!(c(None, &Err("fuel".to_string())), Verdict::Trap);
    // Refusals, exactly as the pipeline writes them.
    assert_eq!(c(None, &ok("!!")), Verdict::Poison);
    assert_eq!(c(None, &text("REJECT:nr:x;")), Verdict::Refused);
    assert_eq!(c(None, &text("REJECT:tc:x,10,20;y;")), Verdict::Refused);
    assert_eq!(
        c(None, &text("REJECT:taint:SH_TAINT_UNSUPPORTED;")),
        Verdict::Refused
    );
    // Malformed output is a divergence.
    for malformed in [
        ok(""),
        ok("00"),
        ok(&flipped_hex),
        ok("0g"),
        ok("abc"),
        ok(&format!("!!{hex}")),
        ok("!!garbage"),
        text("garbage"),
        text("REJECT:"),
        text("REJECT:nr:"),
        text("REJECT:nr:;"),
        text("REJECT:nr:x"),
        text("REJECT:nr:x;;"),
        text("REJECT:zz:x;"),
        text("REJECT:tc:x,1a;"),
        text("REJECT:tc:x,;"),
        text("REJECT:nr:\u{fffd};"),
        text(&format!("REJECT:nr:x;\nOK:{hex}")),
    ] {
        assert_eq!(
            c(None, &malformed),
            Verdict::Diverge,
            "{malformed:?} is not a refusal or a valid module"
        );
    }
}

/// A two-ring program whose outer ring holds two same-signature fns after an inner one, so a call
/// numbered by the wrong ring lands on a plausible neighbour. Global FuncIds: `first::dummy` 0
/// (inner), `two` 1, `three` 2, `tool_main` 3. The outer module imports fuel_decrement and alloc,
/// so `two` is its fn 2 and `three` its fn 3, and `tool_main` calls `two` as `call 2`.
const TWO_RING_NEIGHBOURS: &str = "module first;
fn dummy(a: i64) -> i64 {
    return a;
}
#[ring(outer)] module tool;
fn two(a: i64) -> i64 {
    return a + 2;
}
fn three(a: i64) -> i64 {
    return a + 3;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return two(input_len);
}
";

/// `module` with its one `call from` rewritten to `call to` (both one-byte LEB indices). Panics
/// unless exactly one call matched, so the plant is the one intended.
fn patch_call(module: &[u8], from: u32, to: u32) -> Vec<u8> {
    assert!(from < 128 && to < 128, "one-byte LEB indices only");
    let mut out = module.to_vec();
    let mut patched = 0;
    for payload in wasmparser::Parser::new(0).parse_all(module) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("a valid module") {
            let mut ops = body.get_operators_reader().expect("the body's operators");
            while !ops.eof() {
                let (op, offset) = ops.read_with_offset().expect("an operator");
                if let wasmparser::Operator::Call { function_index } = op
                    && function_index == from
                {
                    assert_eq!(out[offset], 0x10, "a call opcode at the operator's offset");
                    out[offset + 1] = u8::try_from(to).expect("checked above");
                    patched += 1;
                }
            }
        }
    }
    assert_eq!(patched, 1, "exactly one `call {from}` to plant");
    out
}

/// SHP-2b: the two-ring form, read exactly. Both halves must match production's two modules, in
/// order; one module for two, two for one, an empty or extra half and a malformed half are all
/// divergences. The slice's exit anti-stub:
/// an outer module that calls a fn by the wrong numbering — SR-018's bug, the global FuncId used
/// as the ring-local index, which turns `call 2` (`two`) into `call 3` (`three`, the
/// same-signature neighbour) — is a module that validates and runs a different fn, and the
/// classifier reports it.
#[test]
fn shp2_classifier_reads_the_two_ring_form() {
    let c = compile_module(TWO_RING_NEIGHBOURS).expect("production accepts the two-ring program");
    let inner = c.wasm_inner.clone();
    let outer = c
        .wasm_outer
        .clone()
        .expect("an outer-ring module makes production emit two modules");
    let (ih, oh) = (to_hex(&inner), to_hex(&outer));
    let ok = |text: String| Ok::<String, String>(text);
    let two_ring = |i: &str, o: &str| ok(format!("OK:{i}|{o}"));
    let c2 = |answer: &Result<String, String>| classify(&inner, Some(&outer), answer);
    assert_eq!(c2(&two_ring(&ih, &oh)), Verdict::Identical);
    assert_eq!(
        c2(&two_ring(&oh, &ih)),
        Verdict::Diverge,
        "the halves are ordered: inner, then outer"
    );
    for (answer, why) in [
        (
            ok(format!("OK:{ih}")),
            "one module cannot stand in for production's two",
        ),
        (ok(format!("OK:{oh}")), "nor can the outer one alone"),
        (ok(format!("OK:{ih}|")), "an empty outer half"),
        (ok(format!("OK:|{oh}")), "an empty inner half"),
        (ok(format!("OK:{ih}|{oh}|{oh}")), "a third module"),
        (ok(format!("OK:{ih}|{oh}0g")), "a half that is not hex"),
        (
            ok(format!("OK:!!|{oh}")),
            "the poison marker is the whole answer, or nothing",
        ),
    ] {
        assert_eq!(c2(&answer), Verdict::Diverge, "{why}");
    }
    assert_eq!(
        classify(&inner, None, &two_ring(&ih, &oh)),
        Verdict::Diverge,
        "two modules where production emits one"
    );
    let planted = patch_call(&outer, 2, 3);
    assert!(
        wasmparser::validate(&planted).is_ok(),
        "the plant is a plausible module, not garbage"
    );
    assert_eq!(
        c2(&two_ring(&ih, &to_hex(&planted))),
        Verdict::Diverge,
        "an outer call numbered by the global FuncId is a divergence"
    );
}

/// A program production expands: `Some` makes the ambient include add the stdlib `option` module
/// (and the `result` module it needs) besides the source.
const EXPANDED_PROGRAM: &str = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let o: Option<i64> = Some(input_len);
    match o {
        Some(v) => { return v; },
        None => { return 0; }
    }
}
";

/// SHP-3: the text the seed is handed is the program production compiled. For a program
/// production expands, it is the source and then each stdlib module production added, in
/// production's order, and the stage chain compiles it to production's exact modules; a source
/// compiled alone is handed over unchanged. The detector is shown failing a text that drops a
/// module production compiled, and one that holds production's modules in another order.
#[test]
fn shp3_the_seed_is_handed_the_program_production_compiled() {
    let alone = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n    return input_len;\n}\n";
    let c = compile_module(alone).expect("production accepts the plain program");
    assert_eq!(c.sources.len(), 1, "a plain program is compiled alone");
    assert_eq!(
        production_input(&c),
        alone,
        "a source compiled alone is handed over unchanged"
    );

    let c = compile_module(EXPANDED_PROGRAM).expect("production accepts the expanded program");
    let names: Vec<&str> = c.sources.files().iter().map(|f| f.name()).collect();
    assert!(
        names.len() >= 2 && names[1..].iter().all(|n| n.starts_with("stdlib/sigil/")),
        "production expands the program with stdlib modules after the source: {names:?}"
    );
    let input = production_input(&c);
    assert!(
        input.starts_with(EXPANDED_PROGRAM) && input.contains("module option;"),
        "the handed text is the source, then the stdlib modules"
    );
    assert!(
        chain_matches(&c, &input),
        "the stage chain compiles the handed text to production's modules"
    );

    let texts: Vec<&str> = c.sources.files().iter().map(|f| f.text()).collect();
    let dropped = texts[..texts.len() - 1].join("\n");
    assert!(
        !chain_matches(&c, &dropped),
        "anti-stub: a text without one of production's modules is not the program it compiled"
    );
    let mut reordered = texts.clone();
    reordered[1..].reverse();
    if texts.len() == 2 {
        reordered.swap(0, 1);
    }
    assert!(
        !chain_matches(&c, &reordered.join("\n")),
        "anti-stub: production's modules in another order are not the program it compiled"
    );
}

/// A handler program production expands: its `Option` makes the ambient include add the stdlib
/// `option` module, and its `handle`/`perform` reach the effect desugar.
const EXPANDED_HANDLER_PROGRAM: &str = "#[ring(outer)]
module a;
effect Reader { fn get() -> i64; }
fn f() -> i64 ! { Reader } { return perform Reader.get(); }
fn run() -> i64 { return handle f() { Reader.get() => resume 42 }; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let o: Option<i64> = Some(input_len);
    return run();
}
";

/// SHP-3: the expansion check runs production's stages, the effect desugar included, so a handler
/// program production expands is shown handed over faithfully rather than failing the gate for a
/// pass the check lacked. Anti-stub: the chain the seed mirrors, without the desugar, does not
/// compile the same text to production's modules.
#[test]
fn shp3_production_stages_include_the_effect_desugar() {
    let c =
        compile_module(EXPANDED_HANDLER_PROGRAM).expect("production accepts the handler program");
    assert!(
        c.sources.len() > 1,
        "the ambient include expands the handler program"
    );
    let input = production_input(&c);
    assert!(
        chain_matches(&c, &input),
        "production's stages compile the handed text to production's modules"
    );
    let undesugared = catch_unwind(AssertUnwindSafe(|| stage_chain_with(&input, false)));
    assert!(
        !matches!(undesugared, Ok(Ok((ref inner, ref outer))) if *inner == c.wasm_inner && *outer == c.wasm_outer),
        "anti-stub: without the effect desugar the chain must miss production's modules"
    );
}

/// The X extractor must find programs in every literal form the test sources use, and nothing
/// else; the walkers must find the corpora they claim to walk.
#[test]
fn shp_extractor_finds_planted_programs() {
    let synthetic = concat!(
        "// \"module c; fn in_comment() {}\"\n",
        "/// \"module d; fn in_doc() {}\"\n",
        "/* a /* nested */ \"module z; fn h() -> i64 { return 9; }\" */\n",
        "let a = \"module m;\\nfn f() -> i64 { return 1; }\\n\";\n",
        "let b = r#\"module r;\nfn g() -> i64 { return \"x\".len(); }\n\"#;\n",
        "let c = \"not a program\";\n",
        "let d = b\"module bytes; fn h() {}\";\n",
        "let e = format!(\"module t;\\nfn k() {{ {} }}\\n\", body);\n",
        "let q = '\"';\n",
        "m! { ['\\'', '\"'] }\n",
        "let f = \"#[ring(outer)] module o; fn z() {}\";\n",
        "let g = \"module w;\\n\\\n    fn y() {}\";\n",
    );
    let found = extract_programs("synthetic.rs", synthetic);
    assert_eq!(
        found,
        vec![
            "module m;\nfn f() -> i64 { return 1; }\n".to_string(),
            "module r;\nfn g() -> i64 { return \"x\".len(); }\n".to_string(),
            "module t;\nfn k() { {} }\n".to_string(),
            "#[ring(outer)] module o; fn z() {}".to_string(),
            "module w;\nfn y() {}".to_string(),
        ],
        "the extractor must find exactly the planted programs"
    );
    assert!(!looks_like_program("fn f() {}"), "no module header");
    assert!(!looks_like_program("module m;"), "no function");
    assert!(looks_like_program("// note\nmodule m;\nfn f() {}"));
    let unbalanced =
        catch_unwind(|| extract_programs("unbalanced.rs", "fn f() { \"module m; fn g() {}\""));
    assert!(
        unbalanced.is_err(),
        "a file that does not tokenize must stop the gate, not drop out of X"
    );

    let roots = parity_roots();
    assert!(
        roots.iter().any(|r| r == "tests/compile") && roots.iter().any(|r| r == "stdlib"),
        "the ROOTS parser must return the parity manifest's real roots, got {roots:?}"
    );
}

/// A verbatim copy of a pinned X program in a file that sorts earlier must not take the pin's
/// label; an unpinned program is labelled by the first file that holds it; a divergence whose
/// pinned file no longer holds it is reported as a moved pin, not a new divergence.
#[test]
fn shp_labels_stay_with_their_pins() {
    let program = "module m;\nfn f() -> i64 { return 1; }\n";
    let file = format!("let s = {program:?};\n");
    let files = vec![
        ("a.rs".to_string(), file.clone()),
        ("b.rs".to_string(), file),
    ];
    let hash = program_hash(program);
    let label_of = |pinned: &BTreeSet<&str>| -> Vec<String> {
        label_x_programs(&files, pinned)
            .into_iter()
            .map(|p| p.label)
            .collect()
    };
    assert_eq!(label_of(&BTreeSet::new()), vec![format!("a.rs#{hash}")]);
    let pin = format!("b.rs#{hash}");
    assert_eq!(label_of(&BTreeSet::from([pin.as_str()])), vec![pin.clone()]);

    let pinned: &[&'static str] = &["b.rs#0011aabb", "c.rs#22334455"];
    assert_eq!(pinned_twin("a.rs#0011aabb", pinned), Some("b.rs#0011aabb"));
    assert_eq!(pinned_twin("a.rs#99999999", pinned), None);
    assert_eq!(
        pinned_twin("b.rs#0011aabb", pinned),
        None,
        "a pin is not its own twin"
    );
}

// ── SHP-0b's named fences ────────────────────────────────────────────────────────────────────

/// What a named fence pins: the seed's module is production's, or the seed refuses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fence {
    Identical,
    Refused,
}

/// The fence a classified answer satisfies; `None` for a divergence, a trap, or malformed output.
fn fence_of(verdict: Verdict) -> Option<Fence> {
    match verdict {
        Verdict::Identical => Some(Fence::Identical),
        Verdict::Poison | Verdict::Refused => Some(Fence::Refused),
        Verdict::Trap | Verdict::Diverge => None,
    }
}

/// One program per construct SHP-0b fixed or fenced (docs/specs/self-host-backend-parity.md §1,
/// SR-029), with the verdict the committed seed must give it. The sweep above proves the
/// aggregate; this names each construct, so a regression fails by name and a fence quietly
/// turned into a divergence cannot hide in a count. Every row is a program production accepts
/// (asserted), or the row would measure nothing. The 4-byte signed index rows also pin the seed's
/// mirror of production's SR-030 fix, which no corpus program measures.
const SHP0B_FENCES: &[(&str, Fence, &str)] = &[
    // Fixed: the seed now emits exactly the oracle's bytes.
    (
        "signed_i32_lt",
        Fence::Identical,
        r#"module tool;
fn lt(a: i32, b: i32) -> bool { return a < b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: i32 = 0;
    let b: i32 = 1;
    let c: i32 = a - b;
    if lt(c, a) {
        return 1;
    } else {
    }
    return 0;
}
"#,
    ),
    (
        "signed_i32_gt",
        Fence::Identical,
        r#"module tool;
fn f(a: i32, b: i32) -> bool { return a > b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "signed_i32_ge",
        Fence::Identical,
        r#"module tool;
fn f(a: i32, b: i32) -> bool { return a >= b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "signed_i32_div",
        Fence::Identical,
        r#"module tool;
fn f(a: i32, b: i32) -> i32 { return a / b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "signed_i32_rem",
        Fence::Identical,
        r#"module tool;
fn f(a: i32, b: i32) -> i32 { return a % b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "byte_store_i32",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let p: i64 = alloc(8);
    let v: i32 = 65;
    store8(p, v);
    return 0;
}
"#,
    ),
    (
        "narrow_literal_arg",
        Fence::Identical,
        r#"module tool;
fn takes_u32(x: u32) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return takes_u32(42);
}
"#,
    ),
    (
        "return_i32_literal",
        Fence::Identical,
        r#"module tool;
fn f() -> i32 { return 5; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "record_i32_fields",
        Fence::Identical,
        r#"module tool;
record S { a: i32, b: i32 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { a: 3, b: 4 };
    if s.b == 4 {
        return 1;
    } else {
    }
    return 0;
}
"#,
    ),
    (
        "record_u32_bool_fields",
        Fence::Identical,
        r#"module tool;
record S { a: u32, b: bool, c: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { a: 7, b: true, c: 9 };
    return s.c;
}
"#,
    ),
    (
        "tuple_i32_literal",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let t: (i32, i64) = (1, 2);
    return 0;
}
"#,
    ),
    (
        "region_param",
        Fence::Identical,
        r#"module tool;
fn r(x: Region) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "unit_variant_last_arm",
        Fence::Identical,
        r#"module tool;
enum Color { Red, Green, Blue }
fn code(c: Color) -> i64 {
    match c {
        Color::Red => { return 1; },
        Color::Green => { return 2; },
        Color::Blue => { return 3; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return code(Color::Blue);
}
"#,
    ),
    (
        "match_assign_no_return",
        Fence::Identical,
        r#"module tool;
enum Color { Red, Green, Blue }
fn f(c: Color) -> i64 {
    let mut r: i64 = 0;
    match c {
        Color::Red => { r = 1; },
        Color::Green => { r = 2; },
        Color::Blue => { r = 3; },
    }
    return r;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return f(Color::Blue);
}
"#,
    ),
    (
        "match_unit_then_bound",
        Fence::Identical,
        r#"module tool;
enum Q { N, S(i64) }
fn f(q: Q) -> i64 {
    match q {
        Q::N => { return 0; },
        Q::S(x) => { return x; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return f(Q::S(4));
}
"#,
    ),
    (
        "match_bound_then_unit",
        Fence::Identical,
        r#"module tool;
enum Q { N, S(i64) }
fn f(q: Q) -> i64 {
    match q {
        Q::S(x) => { return x; },
        Q::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return f(Q::N);
}
"#,
    ),
    (
        "match_bare_last",
        Fence::Identical,
        r#"module tool;
enum Q { N, S(i64) }
fn f(q: Q) -> i64 {
    match q {
        S(x) => { return x; },
        N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return f(Q::N);
}
"#,
    ),
    // Fenced: the seed refuses.
    // An outer-ring module. SHP-0b refused it whole: production emits a second module, which the
    // single-ring protocol could not carry. SHP-2b emits both, in the `OK:{inner}|{outer}` form,
    // so it is exact.
    (
        "outer_ring_module",
        Fence::Identical,
        r#"#[ring(outer)]
module ext;
fn add(a: i64, b: i64) -> i64 {
    return a + b;
}
"#,
    ),
    (
        "alias_local",
        Fence::Refused,
        r#"module tool;
type Count = i64;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c: Count = 5;
    return c;
}
"#,
    ),
    // The parser skips a `where` refinement it cannot read; a skipped construct refuses the program.
    (
        "record_refinement_skipped",
        Fence::Refused,
        r#"module range;
record Range { lo: i64, hi: i64 } where lo <= hi
pub fn width(r: Range) -> i64 {
  return (r.hi - r.lo);
}
"#,
    ),
    (
        "u256_let",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: u256 = 5;
    return 0;
}
"#,
    ),
    (
        "record_u256_field",
        Fence::Refused,
        r#"module tool;
record S { v: u256, p: bool }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { v: 5, p: true };
    if s.p {
        return 1;
    } else {
    }
    return 0;
}
"#,
    ),
    // Exact since the review: an array literal takes the element type its slot declares.
    (
        "array_i32_literals",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: [i32; 2] = [1, 2];
    return 0;
}
"#,
    ),
    (
        "array_i32_arg",
        Fence::Identical,
        r#"module tool;
fn f(a: [i32; 2]) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return f([1, 2]);
}
"#,
    ),
    (
        "array_i32_repeat",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: [i32; 4] = [0; 4];
    return 0;
}
"#,
    ),
    (
        "const_i32",
        Fence::Refused,
        r#"module tool;
const C: i32 = 5;
fn f() -> i32 { return C; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "const_u64_div",
        Fence::Refused,
        r#"module tool;
const C: u64 = 9;
fn f(x: u64) -> u64 { return C / x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    // One name bound twice in a pattern.
    (
        "duplicate_binder",
        Fence::Refused,
        r#"module m;
enum P { V(i64, i64) }
fn boot() -> i64 {
  let p: P = P::V(1, 2);
  match p { P::V(x, x) => { return x; } }
}
"#,
    ),
    // A void method called in statement position on a generic instance.
    (
        "void_method_call",
        Fence::Refused,
        r#"module tool;
record Box<T> { v: T, hits: i64 }
impl Box<T> {
  pub fn make(seed: T) -> Box<T> { return Box { v: seed, hits: 0 }; }
  pub fn poke(self: Box<T> @Mut) { self.hits = self.hits + 10; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut bi: Box<i64> = Box::make(7);
    let mut bb: Box<bool> = Box::make(true);
    bi.poke();
    bb.poke();
    bb.poke();
    let total: i64 = bi.hits + bb.hits;
    return 0 - total;
}
"#,
    ),
    // `substr` bounds of type `i32`, which the oracle widens before its checks.
    (
        "substr_i32_bounds",
        Fence::Refused,
        r#"module tool;
fn sub_first(s: str, i: i32, j: i32) -> i64 {
    let v: str = s.substr(i, j);
    return v.byte_at(0);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let h: str = "hello";
    return 0 - sub_first(h, 1, 3);
}
"#,
    ),
    // Calling a higher-kinded generic: its instance used to trap the walk.
    (
        "hkt_generic_call",
        Fence::Refused,
        r#"module tool;
record Box<T> { val: T }
fn unwrap<F: * -> *, A>(xs: F<A>) -> i64 { return xs.val; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let b: Box<i64> = Box { val: 42 };
    return 0 - unwrap::<Box, i64>(b);
}

"#,
    ),
    // `<=` on `i32` is outside the opcode table: it refuses rather than guess.
    (
        "signed_i32_le",
        Fence::Refused,
        r#"module tool;
fn f(a: i32, b: i32) -> bool { return a <= b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    // From the review: every value is typed by the slot it is written to (a call or method
    // argument, a return, a record field, an array element, a field write), as the oracle types
    // it. Exact where this lowering can see the slot's type.
    (
        "u32_literal_arg_above_i32_max",
        Fence::Identical,
        r#"module tool;
fn takes_u32(x: u32) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return takes_u32(3000000000);
}
"#,
    ),
    (
        "u32_literal_field_above_i32_max",
        Fence::Identical,
        r#"module tool;
record S { a: u32, b: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { a: 0xFFFFFFFF, b: 40 };
    return 0 - s.b;
}
"#,
    ),
    (
        "u32_literal_compare_above_i32_max",
        Fence::Identical,
        r#"module tool;
fn f(x: u32) -> i64 {
    if x == 4000000000 {
        return 11;
    } else {
    }
    return 22;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "generic_record_i32_instance_literal",
        Fence::Identical,
        r#"module tool;
record Box<T> { v: T, w: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let b: Box<i32> = Box { v: 5, w: 7 };
    return 0 - b.w;
}
"#,
    ),
    (
        "generic_record_i32_instance_arg",
        Fence::Identical,
        r#"module tool;
record Box<T> { v: T, w: i64 }
fn take(b: Box<i32>) -> i64 { return b.w; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return take(Box { v: 5, w: 7 }); }
"#,
    ),
    (
        "method_arg_i32_literal",
        Fence::Identical,
        r#"module tool;
record P { v: i64 }
impl P {
    pub fn add(self: P, x: i32) -> i64 { return self.v; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let p: P = P { v: 3 };
    return p.add(5);
}
"#,
    ),
    (
        "method_arg_i32_array",
        Fence::Identical,
        r#"module tool;
record P { v: i64 }
impl P {
    pub fn take(self: P, a: [i32; 2]) -> i64 { return self.v; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let p: P = P { v: 3 };
    return p.take([1, 2]);
}
"#,
    ),
    (
        "i32_compare_literal_arithmetic",
        Fence::Identical,
        r#"module tool;
fn f(x: i32) -> i64 { if x < 1 + 2 { return 1; } return 2; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return f(0); }
"#,
    ),
    (
        "i32_literal_arithmetic_operand",
        Fence::Identical,
        r#"module tool;
fn f(x: i32) -> i32 { return (1 + 2) * x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: i32 = f(2); if r == 6 { return 1; } return 2; }
"#,
    ),
    (
        "byte_at_u32_index",
        Fence::Identical,
        r#"module tool;
fn f(s: str, i: u32) -> i64 { return s.byte_at(i); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return f("hello", 1); }
"#,
    ),
    // A 4-byte signed index at a bounds check. SHP-0b refused it in `byte_at`, where production
    // compared it signed; production now copies it into a U32 first (SR-030), at every bounds
    // check, and the seed makes the same copy, so these are exact.
    (
        "byte_at_i32_index",
        Fence::Identical,
        r#"module tool;
fn first(s: str, i: i32) -> i64 {
    return s.byte_at(i);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let h: str = "hello";
    return first(h, 1);
}
"#,
    ),
    (
        "array_read_i32_index",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: [i64; 3] = [7, 8, 9];
    let i: i32 = 2;
    let v: i64 = a[i];
    return v + a[i - 1] + input_len;
}
"#,
    ),
    (
        "array_write_i32_index",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut a: [i64; 3] = [7, 8, 9];
    let i: i32 = 1;
    a[i] = input_len;
    return a[1] + a[0];
}
"#,
    ),
    // Typed by the slot all the way down: an inner array's elements take the outer annotation's
    // element type, a field's array literal takes the field's, a nested generic construct takes
    // the instance its field type names, and a record construct payload types itself.
    (
        "i32_array_nested_literals",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: [[i32; 2]; 2] = [[1, 2], [3, 4]];
    return 0;
}
"#,
    ),
    (
        "i32_array_in_record_field",
        Fence::Identical,
        r#"module tool;
record S { arr: [i32; 2], w: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { arr: [1, 2], w: 5 };
    return s.w;
}
"#,
    ),
    (
        "generic_record_nested_construct",
        Fence::Identical,
        r#"module tool;
record Box<T> { v: T }
record Wrap<T> { inner: Box<T> }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let w: Wrap<i32> = Wrap { inner: Box { v: 41 } };
    let b: Box<i32> = w.inner;
    return input_len;
}
"#,
    ),
    (
        "record_enum_payload",
        Fence::Identical,
        r#"module tool;
record P { x: i32, y: i64 }
enum E { A, B(P) }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::B(P { x: 1, y: 40 });
    return input_len;
}
"#,
    ),
    // Refused where it cannot: literal arithmetic the oracle types by a narrower or unsigned
    // slot, an array literal under a slot whose element type is not visible here, a literal
    // wider than `i64`, and an `i32` string index (production's bounds check reads it signed).
    (
        "i32_field_literal_arithmetic",
        Fence::Refused,
        r#"module tool;
record S { a: i32, b: i32, c: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { a: 1 + 2, b: 4, c: 40 };
    return 0 - s.c;
}
"#,
    ),
    (
        "i32_return_literal_arithmetic",
        Fence::Refused,
        r#"module tool;
fn f() -> i32 { return 1 + 2; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "i32_arg_literal_arithmetic",
        Fence::Refused,
        r#"module tool;
fn takes_i32(x: i32) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return takes_i32(0 - 5);
}
"#,
    ),
    (
        "i32_payload_literal_arithmetic",
        Fence::Refused,
        r#"module tool;
enum E { V(i32, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b) => { return b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::V(1 + 2, 40);
    return 0 - get(e);
}
"#,
    ),
    (
        "i32_array_literal_arithmetic",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: [i32; 2] = [1 + 0, 2 + 0];
    let z: i32 = a[1];
    if z == 2 {
        return 0 - 11;
    } else {
    }
    return 0 - 22;
}
"#,
    ),
    (
        "i32_array_reassigned_literals",
        Fence::Refused,
        r#"module tool;
fn f(x: i32, y: i32) -> i64 {
    let mut a: [i32; 2] = [x, y];
    a = [1, 2];
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0;
}
"#,
    ),
    (
        "tuple_literal_untracked_payload",
        Fence::Refused,
        r#"module tool;
enum E { A, B((i32, i64)) }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::B((1, 2));
    return input_len;
}
"#,
    ),
    (
        "u64_arg_literal_division",
        Fence::Refused,
        r#"module tool;
fn f(x: u64) -> u64 { return x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: u64 = f(10 / 3); return 0; }
"#,
    ),
    (
        "i32_field_write_literal_arithmetic",
        Fence::Refused,
        r#"module tool;
record S { a: i32, b: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut s: S = S { a: 1, b: 4 }; s.a = 2 + 3; return s.b; }
"#,
    ),
    (
        "wide_decimal_literal",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let x = 99999999999999999999;
    return 0;
}
"#,
    ),
    (
        "wide_hex_literal",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let x = 0xFFFFFFFFFFFFFFFFFF;
    return 0;
}
"#,
    ),
    // SR-032: a construct's parts are typed by the slot they are written to, as production now
    // types them (docs/specs/sh-wasm.md, the construct-slot rule). SHP-0b refused the first three,
    // a literal payload narrower than `i64` and an array literal in a tuple, while production laid
    // them out at the `i64` default. Exact where this lowering can see the slot.
    (
        "enum_payload_i32",
        Fence::Identical,
        r#"module tool;
enum E { V(i32), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::V(3);
    return 0;
}
"#,
    ),
    (
        "payload_i32_then_i64",
        Fence::Identical,
        r#"module tool;
enum E { V(i32, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b) => { return b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::V(3, 40);
    return 0 - get(e);
}
"#,
    ),
    (
        "i32_array_in_tuple",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let t: ([i32; 2], i64) = ([1, 2], 3);
    return 0;
}
"#,
    ),
    (
        "tuple_i32_return",
        Fence::Identical,
        r#"module tool;
fn f() -> (i32, i64) { return (1, 2); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return input_len;
}
"#,
    ),
    (
        "tuple_i32_arg",
        Fence::Identical,
        r#"module tool;
fn f(t: (i32, i64)) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return f((1, 2));
}
"#,
    ),
    (
        "tuple_i32_array_element",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: [(i32, i64); 2] = [(7, 70), (8, 80)];
    return input_len;
}
"#,
    ),
    (
        "tuple_i32_record_field",
        Fence::Identical,
        r#"module tool;
record S { t: (i32, i64), w: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: S = S { t: (1, 2), w: 5 };
    return s.w;
}
"#,
    ),
    (
        "generic_payload_i32_annotation",
        Fence::Identical,
        r#"module tool;
enum G<T> { V(T, i64), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let g: G<i32> = G::V(3, 40);
    return input_len;
}
"#,
    ),
    // Refused where it cannot see the slot: an assignment's place, the generic instance a record
    // field names, and an array payload (the enum tables hold scalar payload types only).
    (
        "tuple_i32_reassigned_literals",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut t: (i32, i64) = (1, 2);
    t = (3, 4);
    return input_len;
}
"#,
    ),
    (
        "generic_payload_i32_reassigned",
        Fence::Refused,
        r#"module tool;
enum G<T> { V(T, i64), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut g: G<i32> = G::N;
    g = G::V(3, 40);
    return input_len;
}
"#,
    ),
    (
        "generic_payload_i32_record_field",
        Fence::Refused,
        r#"module tool;
enum G<T> { V(T, i64), N }
record H { g: G<i32>, w: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let h: H = H { g: G::V(3, 40), w: 5 };
    return h.w;
}
"#,
    ),
    (
        "i32_array_in_payload",
        Fence::Refused,
        r#"module tool;
enum E { V([i32; 2], i64), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::V([1, 2], 3);
    return input_len;
}
"#,
    ),
    // A compound literal passed to a generic function's instance: the instance's parameter is
    // fully substituted, while production pins the argument only once earlier arguments have
    // bound its type parameters, so the seed refuses a literal part there (cv_call_arg_tid).
    // These diverged before the fix (the array and the unit variant already on the old seed).
    (
        "generic_call_tuple_literal",
        Fence::Refused,
        r#"module tool;
fn g<T>(a: T, t: (i32, i64)) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, (1, 40)); }
"#,
    ),
    (
        "generic_call_tuple_bound_late",
        Fence::Refused,
        r#"module tool;
fn g<T>(t: (T, i32), a: T) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g((input_len, 4), input_len); }
"#,
    ),
    (
        "generic_call_enum_literal",
        Fence::Refused,
        r#"module tool;
enum G<T> { V(T, i64), N }
fn g<T>(a: T, e: G<i32>) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, G::V(3, 40)); }
"#,
    ),
    (
        "generic_call_unit_variant",
        Fence::Refused,
        r#"module tool;
enum G<T> { V(T, i64), N }
fn g<T>(a: T, e: G<T>) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, G::N); }
"#,
    ),
    (
        "generic_call_array_literal",
        Fence::Refused,
        r#"module tool;
fn g<T>(a: T, arr: [i32; 2]) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, [1, 2]); }
"#,
    ),
    (
        "generic_call_record_literal",
        Fence::Refused,
        r#"module tool;
record Bx<T> { v: T }
fn g<T>(b: Bx<T>, a: T) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let y: i64 = 2; return g(Bx { v: 5 }, y); }
"#,
    ),
    // Exact where nothing depends on the slot: a plain enum, a local tuple, a scalar literal.
    (
        "generic_call_plain_enum",
        Fence::Identical,
        r#"module tool;
enum E { V(i32, i64), N }
fn g<T>(a: T, e: E) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, E::V(3, 40)); }
"#,
    ),
    (
        "generic_call_local_tuple",
        Fence::Identical,
        r#"module tool;
fn g<T>(a: T, t: (i32, i64)) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let t: (i32, i64) = (1, 40); return g(input_len, t); }
"#,
    ),
    (
        "generic_call_scalar_literal",
        Fence::Identical,
        r#"module tool;
fn g<T>(a: T, n: i32) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, 7); }
"#,
    ),
    // A bare variant that several enums declare, with no slot in view: production picks the
    // slot's enum, while the emitter's ST-1 fallback took the first declaring enum, so it
    // refuses. The record field diverged on the seed before SR-032; the generic arguments
    // diverged once production pinned them.
    (
        "ambiguous_variant_generic_call",
        Fence::Refused,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
fn g<T>(a: T, e: E2) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return g(input_len, B(input_len)); }
"#,
    ),
    (
        "ambiguous_variant_generic_call_statement",
        Fence::Refused,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
fn g<T>(a: T, e: E2) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { g(input_len, B(input_len)); return 0; }
"#,
    ),
    (
        "ambiguous_variant_record_field",
        Fence::Refused,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
record S { e: E2 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: S = S { e: B(input_len) }; return 0; }
"#,
    ),
    (
        "ambiguous_unit_variant_record_field",
        Fence::Refused,
        r#"module tool;
enum E1 { P, Q }
enum E2 { Q, R }
record S { e: E2 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: S = S { e: Q }; return 0; }
"#,
    ),
    // Exact where the slot is in view.
    (
        "ambiguous_variant_let_annotation",
        Fence::Identical,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let e: E2 = B(input_len); return 0; }
"#,
    ),
    (
        "ambiguous_variant_argument",
        Fence::Identical,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
fn h(e: E2) -> i64 { return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return h(B(input_len)); }
"#,
    ),
    // A bare match pattern (`B(v) =>`) names the scrutinee's variant in production; the emitter's
    // pattern lookup took the first declaring enum and tested its tag. This diverged on the seed
    // before SR-032; it is now refused, and the qualified pattern stays exact.
    (
        "ambiguous_variant_match_pattern",
        Fence::Refused,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
fn h(e: E2) -> i64 { match e { B(v) => { return v; }, Y => { return 0; }, } return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return h(E2::B(input_len)); }
"#,
    ),
    (
        "ambiguous_variant_qualified_match_pattern",
        Fence::Identical,
        r#"module tool;
enum E1 { X, B(i64) }
enum E2 { B(i64), Y }
fn h(e: E2) -> i64 { match e { E2::B(v) => { return v; }, E2::Y => { return 0; }, } return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return h(E2::B(input_len)); }
"#,
    ),
];

// ── SHP-1's named fences ─────────────────────────────────────────────────────────────────────

/// One program per construct SHP-1 taught the self-hosted emitter or fenced (the SHP-1 rules in
/// docs/specs/sh-wasm.md), with the verdict the committed seed must give it, as `SHP0B_FENCES`
/// does for SHP-0b. The `byte_at` index rules are SHP-0b's, fenced in `SHP0B_FENCES`. The three
/// rows SHP-1 pinned Refused, a `ct_*` operand narrower than 8 bytes, left the list when
/// production began rejecting that operand at typecheck (T075): `fence_failures` requires
/// production to accept every row. They are pinned in `SHP1_PRODUCTION_REJECTS` instead.
///
/// `ct_lt` takes its order from its operands' signedness: signed for two `i64`, unsigned for two
/// `u64`. Production checks an integer literal beside a `u64` as a `u64`, a literal binding
/// included. The seed lowers a literal to an `i64` local and refuses the mixed pair rather than
/// pick an order, so the two literal rows are pinned Refused.
const SHP1_FENCES: &[(&str, Fence, &str)] = &[
    // Taught: the seed now emits exactly the oracle's bytes.
    (
        "load8_wide_pointer",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let mut sum: i64 = 0;
    let mut i: i64 = 0;
    while i < input_len {
        let b = load8(input_ptr + i);
        sum = sum + b;
        i = i + 1;
    }
    return sum;
}
"#,
    ),
    (
        "load8_narrow_pointer",
        Fence::Identical,
        r#"module tool;
fn first(p: i32) -> i64 {
    return load8(p);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let q: i32 = 1024;
    return first(q) + input_len;
}
"#,
    ),
    (
        "load8_literal_pointer",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let b: i64 = load8(1024);
    return b + input_len;
}
"#,
    ),
    (
        "load8_statement",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    load8(input_ptr);
    return input_len;
}
"#,
    ),
    (
        "load8_argument_and_condition",
        Fence::Identical,
        r#"module tool;
fn twice(x: i64) -> i64 {
    return x + x;
}
fn peek(p: i64) -> i64 {
    return load8(p);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a = twice(load8(input_ptr));
    if load8(input_ptr) > 64 {
        return a + peek(input_ptr + 1);
    }
    return a;
}
"#,
    ),
    (
        "ct_compare_and_select",
        Fence::Identical,
        r#"module tool;
fn ct_min(a: i64, b: i64) -> i64 {
    let lt: bool = ct_lt(a, b);
    return ct_select(lt, a, b);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let same: bool = ct_eq(input_ptr, input_len);
    let m = ct_min(input_ptr, input_len);
    return ct_select(same, 0, m);
}
"#,
    ),
    (
        "ct_unsigned_operands",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: u64 = 3;
    let b: u64 = 9;
    let lt: bool = ct_lt(a, b);
    return ct_select(lt, a, b);
}
"#,
    ),
    (
        "ct_lt_literal_beside_u64",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: u64 = 3;
    let lt: bool = ct_lt(a, 9);
    return ct_select(lt, 1, 0);
}
"#,
    ),
    (
        "ct_lt_literal_binding_beside_u64",
        Fence::Refused,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: u64 = 3;
    let n = 9;
    let lt: bool = ct_lt(n, a);
    return ct_select(lt, 1, 0);
}
"#,
    ),
];

/// The three narrow `ct_*` programs SHP-1 pinned Refused. Production rejects each at typecheck
/// now (T075), so they cannot be `SHP1_FENCES` rows and the gate never sees them. The seed's
/// typecheck leaves intrinsic parameters unchecked, so its emitter refusal of a 4-byte `ct_*`
/// operand is the only thing between the seed and an invalid module for the shape; this list
/// keeps that backstop pinned by name.
const SHP1_PRODUCTION_REJECTS: &[(&str, &str)] = &[
    (
        "ct_eq_narrow_operands",
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: i32 = 3;
    let b: i32 = 4;
    let same: bool = ct_eq(a, b);
    return ct_select(same, 1, 0);
}
"#,
    ),
    (
        "ct_lt_narrow_operand",
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: i32 = 3;
    let lt: bool = ct_lt(a, 4);
    return ct_select(lt, 1, 0);
}
"#,
    ),
    (
        "ct_select_narrow_operand",
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: i32 = 3;
    let c: bool = input_len > 2;
    return ct_select(c, a, 7);
}
"#,
    ),
];

/// A `ct_lt` pair of one `i64` and one `u64`, which has no single order. Production rejects it at
/// typecheck (T075), so it cannot be an `SHP1_FENCES` row; the seed's typecheck leaves intrinsic
/// parameters unchecked, so its emitter's mixed-pair refusal is the backstop this pins.
const SHP1_CT_LT_MIXED_SIGNEDNESS: &str = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let a: i64 = 3;
    let b: u64 = 9;
    let lt: bool = ct_lt(a, b);
    return ct_select(lt, 1, 0);
}
"#;

/// Is the seed's answer one of the two exact refusal forms `classify` accepts, the poison marker
/// or a well-formed `REJECT:`? Production's output plays no part, so it reads programs production
/// rejects.
fn is_seed_refusal(answer: &Result<String, String>) -> bool {
    match answer {
        Ok(out) => out == "OK:!!" || out.strip_prefix("REJECT:").is_some_and(is_refusal),
        Err(_) => false,
    }
}

/// The rows of `fences` whose program the committed seed does not answer with the pinned fence,
/// one `name: pinned X, the seed gives Y` line each. A row's program must be one production
/// accepts (asserted), or the row would measure nothing.
fn fence_failures(fences: &[(&str, Fence, &str)]) -> Vec<String> {
    let mut wrong = Vec::new();
    for (name, want, src) in fences {
        let compilation = compile_module(src).unwrap_or_else(|e| {
            panic!("fence {name}: production must accept the program, or the row measures nothing: {e:?}")
        });
        // The program production compiled, as the sweep hands it (SHP-3).
        let answer = run_seed(&production_input(&compilation));
        let got = fence_of(classify(
            &compilation.wasm_inner,
            compilation.wasm_outer.as_deref(),
            &answer,
        ));
        if got != Some(*want) {
            wrong.push(format!("{name}: pinned {want:?}, the seed gives {got:?}"));
        }
    }
    wrong
}

/// SHP-0b: every named fence holds on the committed seed. The fence map is not vacuous (it sends
/// a divergence and a trap to no fence at all), and the comparator is not
/// either: a planted row pinned to the verdict its program does not get is reported by name.
#[test]
fn shp0b_fences_hold_on_the_committed_seed() {
    assert_eq!(
        fence_of(Verdict::Diverge),
        None,
        "anti-stub: a divergence is no fence"
    );
    assert_eq!(
        fence_of(Verdict::Trap),
        None,
        "anti-stub: a trap is no fence"
    );
    let alias = SHP0B_FENCES
        .iter()
        .find(|(name, _, _)| *name == "alias_local")
        .expect("the type-alias fence is in the list");
    assert_eq!(
        alias.1,
        Fence::Refused,
        "the planted row borrows a refused program"
    );
    let planted = [("planted_wrong_pin", Fence::Identical, alias.2)];
    assert_eq!(
        fence_failures(&planted),
        vec!["planted_wrong_pin: pinned Identical, the seed gives Some(Refused)".to_string()],
        "anti-stub: the comparator must report a row pinned to a verdict its program does not get"
    );
    let wrong = fence_failures(SHP0B_FENCES);
    assert!(
        wrong.is_empty(),
        "SHP-0b named fences moved: {wrong:#?}. A construct pinned Identical that no longer is \
         has regressed; one pinned Refused that now diverges is a hole reopened."
    );
}

/// SHP-1: every named fence holds on the committed seed. The fence map's anti-stubs are in the
/// SHP-0b test above; both tests read the seed through `fence_failures`.
#[test]
fn shp1_fences_hold_on_the_committed_seed() {
    let wrong = fence_failures(SHP1_FENCES);
    assert!(
        wrong.is_empty(),
        "SHP-1 named fences moved: {wrong:#?}. A construct pinned Identical that no longer is \
         has regressed; one pinned Refused that now diverges is a hole reopened."
    );
}

/// SHP-1: each narrow `ct_*` program is exactly {T075} in production, and the committed seed
/// still refuses it. Anti-stub (SC-P4): the same refusal check reads the seed's module for the
/// 8-byte twin as no refusal, so it cannot pass every answer.
#[test]
fn shp1_narrow_ct_operands_are_rejected_by_production_and_refused_by_the_seed() {
    let twin = SHP1_FENCES
        .iter()
        .find(|(name, _, _)| *name == "ct_compare_and_select")
        .expect("the 8-byte ct twin is in SHP1_FENCES");
    assert!(
        !is_seed_refusal(&run_seed(twin.2)),
        "anti-stub: the refusal check must not read the seed's module for the 8-byte twin as a \
         refusal"
    );
    for (name, src) in SHP1_PRODUCTION_REJECTS {
        let Err(err) = compile_module(src) else {
            panic!("{name}: production must reject a 4-byte ct_* operand");
        };
        let codes: BTreeSet<String> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect();
        assert_eq!(
            codes,
            BTreeSet::from(["T075".to_string()]),
            "{name}: production must reject the 4-byte operand with the intrinsic argument code"
        );
        let answer = run_seed(src);
        assert!(
            is_seed_refusal(&answer),
            "{name}: the seed must refuse a 4-byte ct_* operand, as poison or a well-formed \
             reject, got {answer:?}"
        );
    }
}

/// SHP-2b: the two-ring constructs, each pinned by name to the verdict the committed seed must
/// give it (docs/specs/self-host-backend-parity.md, "SHP-2b as built"). Exact: an outer module's
/// reduced imports and its `ffi` imports, one per extern a call reaches, in the order the calls
/// first occur (functions, then blocks, then statements; never declaration order); the empty
/// inner module of an outer-only program; the per-ring indices and element runs of both module
/// orders; a ring's own string data; a call past a module with no fn of its own (the synthesized
/// init takes a FuncId); and a first module whose only fn is generic. Refused: the two extern
/// name collisions the seed does not mirror. The outer-ring actor this list also pinned Refused
/// left it when production began rejecting the declaration (`SHP2_OUTER_RING_ACTOR`).
const SHP2_FENCES: &[(&str, Fence, &str)] = &[
    (
        "outer_extern_tool",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {
    return fs_read(input_ptr, input_len);
}
"#,
    ),
    (
        "outer_extern_i64",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn fs_read(path: i64, path_len: i64) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {
    return fs_read(input_ptr, input_len);
}
"#,
    ),
    // Only a called extern is imported.
    (
        "outer_extern_uncalled_decls",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn http_get(url: i32, url_len: i32) -> i64 ! { FFI, Unsafe };
extern "C" fn http_post(url: i32, url_len: i32, body_ptr: i32, body_len: i32) -> i64 ! { FFI, Unsafe };
extern "C" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    return http_get(input_ptr, input_len);
}
"#,
    ),
    // The outer ring's alloc import is its fn 1.
    (
        "outer_helper_alloc",
        Fence::Identical,
        r#"#[ring(outer)] module tool;
fn bump(a: i64) -> i64 {
    return a + 1;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let buf: i64 = alloc(8);
    store8(buf, 65);
    let b: i64 = load8(buf);
    return bump(b);
}
"#,
    ),
    // Each ring lays its own string data out from 1024.
    (
        "outer_string",
        Fence::Identical,
        r#"#[ring(outer)] module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: str = "hello";
    return s.len();
}
"#,
    ),
    (
        "two_ring_inner_first",
        Fence::Identical,
        TWO_RING_NEIGHBOURS,
    ),
    (
        "two_ring_outer_first",
        Fence::Identical,
        r#"#[ring(outer)] module tool;
fn helper(a: i64) -> i64 {
    return a * 3;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return helper(input_len);
}
module second;
pub fn twice(a: i64) -> i64 {
    return a * 2;
}
"#,
    ),
    // A module with no fn of its own takes the synthesized init's FuncId, so the fns after it
    // shift by one.
    (
        "fnless_module_then_call",
        Fence::Identical,
        r#"module shapes;
record Point { x: i64, y: i64 }
module tool;
fn add_one(a: i64) -> i64 {
    return a + 1;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return add_one(input_len);
}
"#,
    ),
    // A generic fn is no fn of its own module, so `lib` takes a synthesized init, and the init
    // comes before the instances: production synthesizes it before the instances join the first
    // module.
    (
        "generic_only_first_module",
        Fence::Identical,
        r#"module lib;
fn id<T>(x: T) -> T {
    return x;
}
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return id(input_len);
}
"#,
    ),
    // Two externs: imported in the order their calls first occur, not declaration order.
    (
        "outer_externs_first_call_order",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn http_get(url: i64, url_len: i64) -> i64 ! { FFI, Unsafe };
extern "C" fn fs_read(path: i64, path_len: i64) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { FFI, Unsafe } {
    return fs_read(input_ptr, input_len) + http_get(input_ptr, input_len);
}
"#,
    ),
    // Function order decides it: `one` precedes `two`, whatever order `tool_main` calls them in.
    (
        "outer_externs_fn_order",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn a_ext(p: i64) -> i64 ! { FFI, Unsafe };
extern "C" fn b_ext(p: i64) -> i64 ! { FFI, Unsafe };
fn one(p: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return b_ext(p);
}
fn two(p: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return a_ext(p);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { FFI, Unsafe } {
    return two(input_len) + one(input_len);
}
"#,
    ),
    // Then block order, here a branch's block before the fall-through's.
    (
        "outer_externs_block_order",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn http_get(url: i64, url_len: i64) -> i64 ! { FFI, Unsafe };
extern "C" fn fs_read(path: i64, path_len: i64) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { FFI, Unsafe } {
    if input_len > 0 {
        return fs_read(input_ptr, input_len);
    }
    return http_get(input_ptr, input_len);
}
"#,
    ),
    // A key already imported adds nothing, and the key is the wasm types at the call: a literal
    // argument takes the declared `i64`, beside an extern of `i32` params.
    (
        "outer_extern_keys_by_call_types",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn narrow(p: i32, n: i32) -> i64 ! { FFI, Unsafe };
extern "C" fn wide(p: i64, n: i64) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FFI, Unsafe } {
    return wide(7, 9) + narrow(input_ptr, input_len) + wide(9, 7);
}
"#,
    ),
    // Two outer modules: one ring, one import list, in module order.
    (
        "outer_externs_two_modules",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module net;
extern "C" fn http_get(url: i64, url_len: i64) -> i64 ! { FFI, Unsafe };
pub fn get(p: i64, n: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return http_get(p, n);
}
#[ring(outer)] #[trusted] module disk;
extern "C" fn fs_read(path: i64, path_len: i64) -> i64 ! { FFI, Unsafe };
pub fn read(p: i64, n: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return fs_read(p, n);
}
"#,
    ),
    // Refused: an extern named like a fn. Production resolves `b`'s call to `b`'s own `get`, an
    // ordinary call, since a call is an FFI call only when it resolved to an extern. The seed's
    // signature table holds one entry per name, so it cannot tell that call from one to `a`'s
    // extern, and refuses the program.
    (
        "extern_named_like_a_fn",
        Fence::Refused,
        r#"#[ring(outer)] #[trusted] module a;
extern "C" fn get(p: i64) -> i64 ! { FFI, Unsafe };
pub fn x(p: i64) -> i64 {
    return p;
}
#[ring(outer)] module b;
fn get(p: i64) -> i64 {
    return p + 1;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return get(input_len);
}
"#,
    ),
    // Refused: one extern declared in two modules. The seed's signature table is keyed by bare
    // name across the program, so it cannot hold both declarations.
    (
        "extern_declared_twice",
        Fence::Refused,
        r#"#[ring(outer)] #[trusted] module net;
extern "C" fn fs_read(p: i64, n: i64) -> i64 ! { FFI, Unsafe };
pub fn get(p: i64, n: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return fs_read(p, n);
}
#[ring(outer)] #[trusted] module disk;
extern "C" fn fs_read(p: i32, n: i32) -> i64 ! { FFI, Unsafe };
pub fn read() -> i64 @Internal ! { FFI, Unsafe } {
    return fs_read(7, 9);
}
"#,
    ),
];

/// SHP-2b: every named two-ring fence holds on the committed seed. The fence map's anti-stubs are
/// in the SHP-0b test above; all three fence tests read the seed through `fence_failures`.
/// An actor in an outer-ring module, which SHP-2b pinned Refused in `SHP2_FENCES`. Production
/// rejects the declaration now (R014), so the program cannot be a fence row and the gate never
/// sees it. The seed refuses it as before: its taint shadow models no actor yet (SHP-9), and its
/// emitter's outer-ring-actor refusal stands behind that. This keeps the refusal pinned by name.
const SHP2_OUTER_RING_ACTOR: &str = r#"#[ring(outer)] module tool;
entry actor Main {
    on Start() -> i64 {
        return 0;
    }
}
"#;

#[test]
fn shp2_outer_ring_actor_is_rejected_by_production_and_refused_by_the_seed() {
    let identical = SHP2_FENCES
        .iter()
        .find(|(name, _, _)| *name == "outer_extern_tool")
        .expect("an Identical outer-ring row is in SHP2_FENCES");
    assert_eq!(
        identical.1,
        Fence::Identical,
        "the anti-stub must probe an Identical row"
    );
    assert!(
        !is_seed_refusal(&run_seed(identical.2)),
        "anti-stub: the refusal check must not read the seed's module for an Identical row as a \
         refusal"
    );
    let Err(err) = compile_module(SHP2_OUTER_RING_ACTOR) else {
        panic!("production must reject an actor declared in an outer-ring module");
    };
    let codes: BTreeSet<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    assert_eq!(
        codes,
        BTreeSet::from(["R014".to_string()]),
        "production must reject the outer-ring actor at its declaration"
    );
    let answer = run_seed(SHP2_OUTER_RING_ACTOR);
    assert!(
        is_seed_refusal(&answer),
        "the seed must refuse an outer-ring actor, as poison or a well-formed reject, got \
         {answer:?}"
    );
}

#[test]
fn shp2_fences_hold_on_the_committed_seed() {
    let wrong = fence_failures(SHP2_FENCES);
    assert!(
        wrong.is_empty(),
        "SHP-2 named fences moved: {wrong:#?}. A construct pinned Identical that no longer is \
         has regressed; one pinned Refused that now diverges is a hole reopened."
    );
}

/// SHP-2b: a call to an extern that another module declares. Production rejects it, because an
/// extern is private to its module. The seed's type check has no module context and would type
/// the call, so its emitter refuses the program instead (`ai_extern_refusal`): a module here would
/// compile a program production rejects. Production emits nothing to compare against, so the
/// seed's answer is read for a refusal alone (`is_seed_refusal`); the anti-stub shows a module
/// answer is not one.
#[test]
fn shp2_call_to_another_modules_extern_is_refused() {
    let src = r#"#[ring(outer)] #[trusted] module a;
extern "C" fn fs_read(path: i64, path_len: i64) -> i64 ! { FFI, Unsafe };
pub fn x(p: i64) -> i64 {
    return p;
}
#[ring(outer)] module b;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return fs_read(input_ptr, input_len);
}
"#;
    let codes: BTreeSet<&str> = match compile_module(src) {
        Ok(_) => panic!("production must reject a call to another module's extern"),
        Err(e) => e.diagnostics().iter().map(|d| d.code().as_str()).collect(),
    };
    assert_eq!(
        codes,
        BTreeSet::from(["T062"]),
        "production's exact rejection: the extern is undefined outside its module"
    );
    assert!(
        !is_seed_refusal(&Ok("OK:0061736d01000000".to_string())),
        "anti-stub: a module answer is no refusal"
    );
    let answer = run_seed(src);
    assert!(
        is_seed_refusal(&answer),
        "the seed must refuse a call to another module's extern, never emit it: {answer:?}"
    );
}

/// The names production resolves as intrinsics before any fn or extern: the first string of each
/// arm of `resolve_intrinsic_call`, as `("alloc", false) => Some(IntrinsicShape::Alloc),`.
fn production_intrinsic_names() -> Vec<String> {
    INTRINSICS_RS
        .lines()
        .filter(|line| line.contains("=> Some(IntrinsicShape::"))
        .filter_map(|line| {
            let rest = line.trim_start().strip_prefix("(\"")?;
            Some(rest.split_once('"')?.0.to_string())
        })
        .collect()
}

/// SHP-2b: an extern named like one of production's intrinsics. Production resolves an intrinsic's
/// name before any fn or extern, so it never calls such an extern. The seed's type check models
/// only some intrinsics, and for the rest it typed the call by the extern's declaration and
/// compiled an FFI call (for `slot_take` or `u256_from_i64`, in a program production rejects). Its
/// emitter now refuses any extern of such a name, called or not (`ai_extern_refusal`). The names
/// are read from production's resolver, so an intrinsic production adds is checked here with no
/// edit, and the reader is shown finding the first and last arms and one the seed does not model.
#[test]
fn shp2_extern_named_like_an_intrinsic_is_refused() {
    let names = production_intrinsic_names();
    for want in ["alloc", "slot_take", "trap"] {
        assert!(
            names.iter().any(|n| n == want),
            "anti-stub: the reader must find `{want}` in resolve_intrinsic_call: {names:?}"
        );
    }
    assert!(
        names.len() >= 17,
        "anti-stub: the reader must find every arm (17 when this test was written): {names:?}"
    );
    let not_refused: Vec<&String> = names
        .iter()
        .filter(|name| {
            let src = format!(
                "#[ring(outer)] #[trusted] module tool;\n\
                 extern \"C\" fn {name}(n: i64) -> i64 ! {{ FFI, Unsafe }};\n\
                 pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    \
                 return input_len;\n}}\n"
            );
            !is_seed_refusal(&run_seed(&src))
        })
        .collect();
    assert!(
        not_refused.is_empty(),
        "the seed must refuse an extern named like a production intrinsic: {not_refused:?}"
    );
}

/// SHP-1: a mixed-signedness `ct_lt` pair is exactly {T075} in production, and the committed seed
/// refuses it. Anti-stub (SC-P4): the same program with `b` declared `i64` compiles in production
/// and is no refusal in the seed, so neither half passes every program.
#[test]
fn shp1_mixed_signedness_ct_lt_is_rejected_by_production_and_refused_by_the_seed() {
    let same_signedness = SHP1_CT_LT_MIXED_SIGNEDNESS.replace("let b: u64 = 9;", "let b: i64 = 9;");
    assert_ne!(
        same_signedness, SHP1_CT_LT_MIXED_SIGNEDNESS,
        "the rewrite must hit the declaration"
    );
    compile_module(&same_signedness)
        .unwrap_or_else(|e| panic!("anti-stub: production must accept two i64: {e:?}"));
    assert!(
        !is_seed_refusal(&run_seed(&same_signedness)),
        "anti-stub: the refusal check must not read the seed's module for two i64 as a refusal"
    );
    let Err(err) = compile_module(SHP1_CT_LT_MIXED_SIGNEDNESS) else {
        panic!("production must reject a mixed-signedness ct_lt pair");
    };
    let codes: BTreeSet<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    assert_eq!(
        codes,
        BTreeSet::from(["T075".to_string()]),
        "production must reject the mixed pair with the intrinsic argument code"
    );
    let answer = run_seed(SHP1_CT_LT_MIXED_SIGNEDNESS);
    assert!(
        is_seed_refusal(&answer),
        "the seed must refuse a mixed-signedness ct_lt pair, as poison or a well-formed reject, \
         got {answer:?}"
    );
}

/// SHP-5a: non-public bindings under control flow, each pinned by name to the verdict the
/// committed seed must give it (docs/specs/self-host-backend-parity.md, "SHP-5a as built"). Before
/// SHP-5a the taint shadow refused every one of these at the taint stage (`SH_TAINT_UNSUPPORTED`);
/// now the shadow checks them as production does and the emitter, which already encoded the
/// constructs, answers production's bytes. Identical: a secret branch, an `@Internal` extern
/// result branched on (the shape 86 of the two-ring tools open with), a secret stored through a
/// pointer rebound to a fresh buffer every iteration (the M6 region model's no-false-positive
/// side), a match on a secret scrutinee, a range over a secret bound, and a secret-guarded
/// `break`. Two range-for rows pin the emitter side: an index the bound covers is Identical, one a
/// guard on the loop variable narrows is Refused (poisoned).
const SHP5_FENCES: &[(&str, Fence, &str)] = &[
    (
        "secret_branch",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: i64 @Secret = input_len;
    let mut x: i64 @Secret = 0;
    if s > 0 {
        x = 1;
    } else {
        x = 2;
    }
    return 0;
}
"#,
    ),
    (
        "internal_extern_result_branch",
        Fence::Identical,
        r#"#[ring(outer)] #[trusted] module tool;
extern "C" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {
    let raw: i64 @Internal = fs_read(input_ptr, input_len);
    if raw < 0 {
        return 0 - 1;
    }
    return raw;
}
"#,
    ),
    (
        "secret_store_through_fresh_buffer_each_iteration",
        Fence::Identical,
        r#"#[ring(outer)] module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let s: i64 @Secret = input_len;
    let out: i64 = alloc(8);
    let mut q: i64 = alloc(8);
    let mut i: i64 = 0;
    while i < 2 {
        store8(q, s);
        q = alloc(8);
        i = i + 1;
    }
    return out;
}
"#,
    ),
    (
        "match_on_secret_scrutinee",
        Fence::Identical,
        r#"module tool;
enum E { A(i64), B }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E @Secret = E::A(input_len);
    let mut r: i64 @Secret = 0;
    match e {
        E::A(v) => { r = v; },
        E::B => { r = 1; },
    }
    return 0;
}
"#,
    ),
    (
        "range_over_secret_bound",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: i64 @Secret = input_len;
    let mut acc: i64 @Secret = 0;
    for i in 0..s {
        acc = acc + i;
    }
    return 0;
}
"#,
    ),
    (
        "secret_guarded_break",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let s: i64 @Secret = input_len;
    let mut i: i64 @Secret = 0;
    while i < 10 {
        if s > i {
            break;
        }
        i = i + 1;
    }
    return 0;
}
"#,
    ),
    // Range-for bodies reach the emitter for the first time. An index the loop's bound covers
    // elides its check on both sides; one a guard on the loop variable narrows is RF-M3,
    // production's refinement channel, and the emitter poisons it rather than guess
    // (`rf_index_guarded`): the review's `if i < 5 { a[i] }` over `[i64; 5]` with `i` in `0..10`
    // diverged until it did.
    (
        "range_index_covered_by_the_bound",
        Fence::Identical,
        r#"module tool;
pub fn f(a: [i64; 5]) -> i64 {
    let mut acc: i64 = 0;
    for i in 0..5 {
        acc = acc + a[i];
    }
    return acc;
}
"#,
    ),
    (
        "range_index_narrowed_by_a_guard",
        Fence::Refused,
        r#"module tool;
pub fn f(a: [i64; 5]) -> i64 {
    let mut acc: i64 = 0;
    for i in 0..10 {
        if i < 5 {
            acc = acc + a[i];
        }
    }
    return acc;
}
"#,
    ),
];

#[test]
fn shp5_fences_hold_on_the_committed_seed() {
    let wrong = fence_failures(SHP5_FENCES);
    assert!(
        wrong.is_empty(),
        "SHP-5a named fences moved: {wrong:#?}. A construct pinned Identical that no longer is \
         has regressed: either the taint shadow refuses control flow over a secret again, or the \
         emitter stopped encoding it."
    );
}

/// SHP-5a: the fenced programs pass the seed's TAINT stage specifically (an Identical answer
/// proves every stage passed, but a future Refused answer could come from any stage, so the
/// stage is read by name). Anti-stub (SC-P4): a closure capturing a secret is still outside the
/// shadow's projection, and the seed refuses it at that stage with the unsupported marker, so
/// the stage read is shown telling a taint refusal from a pass.
#[test]
fn shp5_the_taint_stage_passes_control_flow_over_secrets() {
    for (name, _, src) in SHP5_FENCES {
        let compilation = compile_module(src)
            .unwrap_or_else(|e| panic!("fence {name}: production must accept the program: {e:?}"));
        let answer = run_seed(&production_input(&compilation));
        let out = answer
            .as_ref()
            .unwrap_or_else(|e| panic!("fence {name}: the seed must answer, got {e}"));
        assert!(
            !out.starts_with("REJECT:taint:"),
            "fence {name}: the seed's taint stage refused a shape SHP-5a models: {out}"
        );
    }
    // The closure value carries its capture's label, so the binding absorbs it at @Secret and
    // production accepts; the shadow refuses the closure form itself.
    let still_refused = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n    let s: i64 @Secret = input_len;\n    let g @Secret = fn() -> i64 {\n        let y: i64 @Secret = s;\n        return 0;\n    };\n    return 0;\n}\n";
    let compilation = compile_module(still_refused)
        .unwrap_or_else(|e| panic!("anti-stub: production must accept the closure program: {e:?}"));
    let answer = run_seed(&production_input(&compilation));
    let out = answer
        .as_ref()
        .unwrap_or_else(|e| panic!("anti-stub: the seed must answer, got {e}"));
    // The marker is asserted as an exact code token of the taint verdict, never as a substring
    // (CLAUDE.md: diagnostics are exact code sets).
    let codes: Vec<&str> = out
        .strip_prefix("REJECT:taint:")
        .map(|rest| rest.split(';').collect())
        .unwrap_or_default();
    assert!(
        codes.contains(&"SH_TAINT_UNSUPPORTED"),
        "anti-stub: a secret-capturing closure must still be refused at the taint stage with the \
         unsupported marker as an exact code, got {out}"
    );
}

/// SHP-5b: the security and capability constructs the emitter now reproduces, each pinned by name
/// to the verdict the committed seed must give it (docs/specs/self-host-backend-parity.md,
/// "SHP-5b as built"; docs/specs/sh-wasm.md, "Rules from SHP-5b"). Before the slice every row
/// poisoned: the emitter encoded none of `declassify`, `declassify_ct`, a cap borrow, `restrict`,
/// `restrict_deadline`, `split` or `draw`, and typed a capability annotation as its `<skip>`
/// sentinel. Identical: a declassify bound to a let, a constant-time declassify chained into a
/// declassify, a borrowed cap passed to a call, a restrict to the second declared authority (bit
/// 2, not 1), a restrict_deadline on a parametric cap with two authorities (the full mask, 3), a
/// split of a parameter amount, a draw of a literal passed to a call, a restrict chained
/// through an unannotated let (its receiver's type read through the let, MI-3), and, on a
/// 32-authority cap type, a restrict to its last authority and a restrict_deadline (masks with
/// bit 31 set, negative 4-byte constants). Refused: a borrow
/// of an array as a slice (production allocates a slice header the emitter does not mirror), a
/// borrow of a slice range (an operand that is not a local), and a restrict whose receiver name
/// two bindings give different cap types (the resolver cannot order a shadowing against the use,
/// so it refuses rather than pick one).
const SHP5B_FENCES: &[(&str, Fence, &str)] = &[
    (
        "declassify_into_a_let",
        Fence::Identical,
        r#"module tool;
cap type Declassify {}
pub fn f(s: i64 @Secret, c: Declassify) -> i64 {
    let x: i64 = declassify(s, c);
    return x;
}
"#,
    ),
    (
        "declassify_ct_then_declassify",
        Fence::Identical,
        r#"module tool;
cap type DeclassifyCT {}
cap type Declassify {}
pub fn f(s: i64 @SecretCT, c: DeclassifyCT, d: Declassify) -> i64 @Public {
    let mid: i64 @Secret = declassify_ct(s, c);
    return declassify(mid, d);
}
"#,
    ),
    (
        "borrowed_cap_passed_to_a_call",
        Fence::Identical,
        r#"module tool;
cap type Fuel { burn }
fn use_borrow(f: &Fuel) -> i64 {
    return 0;
}
pub fn boot(f: Fuel) -> i64 {
    return use_borrow(&f);
}
"#,
    ),
    (
        "restrict_to_the_second_authority",
        Fence::Identical,
        r#"module tool;
cap type Fuel { burn, query }
pub fn go(f: Fuel) -> i64 {
    let r: Fuel = f.restrict(query);
    return 0;
}
"#,
    ),
    (
        "restrict_deadline_takes_the_full_mask",
        Fence::Identical,
        r#"module tool;
cap type Approval(deadline_ms: i64) { burn, query }
pub fn narrow(c: Approval(2030)) -> i64 {
    let n = c.restrict_deadline(2025);
    return 1;
}
"#,
    ),
    (
        "split_of_a_parameter_amount",
        Fence::Identical,
        r#"module tool;
cap type Fuel {}
pub fn go(fuel: Fuel, amount: i64) -> i64 {
    let child: Fuel = fuel.split(amount);
    return 0;
}
"#,
    ),
    (
        "draw_of_a_literal_passed_to_a_call",
        Fence::Identical,
        r#"module tool;
cap type Fuel { burn, query }
fn need(f: Fuel) -> i64 {
    return 1;
}
pub fn go(f: Fuel) -> i64 {
    let d: Fuel = f.draw(10);
    return need(d);
}
"#,
    ),
    (
        "restrict_chained_through_an_unannotated_let",
        Fence::Identical,
        r#"module tool;
cap type Fuel { burn, query }
pub fn go(f: Fuel) -> i64 {
    let a = f.restrict(burn);
    let b: Fuel = a.restrict(burn);
    return 0;
}
"#,
    ),
    (
        "borrow_of_an_array_as_a_slice",
        Fence::Refused,
        r#"module tool;
pub fn f(a: [i64; 3]) -> i64 {
    let s: &[i64] = &a;
    return 0;
}
"#,
    ),
    (
        "borrow_of_a_slice_range",
        Fence::Refused,
        r#"module tool;
pub fn f(a: [i64; 3]) -> i64 {
    let t: &[i64] = &a[1..3];
    return 0;
}
"#,
    ),
    (
        "restrict_on_a_name_two_cap_types_share",
        Fence::Refused,
        r#"module tool;
cap type Fuel { burn }
cap type Tri { alpha }
fn use_fuel(f: Fuel) -> i64 {
    return 1;
}
pub fn go(f: Fuel, t: Tri) -> i64 {
    let c: Fuel = f;
    let x: i64 = use_fuel(c);
    let c: Tri = t;
    let r: Tri = c.restrict(alpha);
    return x;
}
"#,
    ),
    // The restriction mask is a 4-byte constant: a 32-authority cap type (the most production
    // allows) puts its last authority at bit 31, where production's `as i32` makes the constant
    // negative; so is its full mask.
    (
        "restrict_to_the_thirty_second_authority",
        Fence::Identical,
        r#"module tool;
cap type Wide { a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 }
pub fn go(w: Wide) -> i64 {
    let r: Wide = w.restrict(a31);
    return 0;
}
"#,
    ),
    (
        "restrict_deadline_full_mask_of_thirty_two",
        Fence::Identical,
        r#"module tool;
cap type Wide(deadline_ms: i64) { a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 }
pub fn narrow(w: Wide(2030)) -> i64 {
    let n = w.restrict_deadline(2025);
    return 1;
}
"#,
    ),
];

#[test]
fn shp5b_fences_hold_on_the_committed_seed() {
    let wrong = fence_failures(SHP5B_FENCES);
    assert!(
        wrong.is_empty(),
        "SHP-5b named fences moved: {wrong:#?}. A construct pinned Identical that no longer is \
         has regressed in the emitter's security-release, borrow or capability arms; one pinned \
         Refused that became Identical needs its rule stated in docs/specs/sh-wasm.md and the \
         pin raised."
    );
}

/// SHP-5c-3: the slot and region constructs the self-hosted compiler now carries end to end,
/// each pinned by name to the verdict the committed seed must give it
/// (docs/specs/self-host-backend-parity.md, "SHP-5c-3 as built"; docs/specs/sh-wasm.md, "Rules
/// from SHP-5c-3"). Before the slice every row refused at the type check (`slot_new::<C>()` is an
/// explicit instantiation it did not parse; `Slot<C>` and `Region` were types it did not name;
/// a `region` statement was a kind it did not type). Identical: a slot round trip, the taken cap
/// handed to a call, a put in both branches of an `if`, a rotation (take, put, take), a slot of a
/// parametric cap and of a two-parameter cap, a take without a put, a slot parameter beside an
/// annotated let, a slot copied through an unannotated let with a take fed into a put; a region
/// whose body binds scalars (in an outer-ring module and in a tool), the handle handed to a
/// `Region` parameter, the handle bound to a `Region` let. Refused, each accepted by production:
/// a region body binding a record, a str or a slot (the taint shadow's scalar-only rule stands
/// in for production's escape lattice), a `grant` of a closure (SHP-7), and an explicit
/// instantiation of a user generic (the type checker infers; `slot_new` is its one turbofish).
const SHP5C3_FENCES: &[(&str, Fence, &str)] = &[
    (
        "slot_round_trip",
        Fence::Identical,
        r#"module main;
cap type Fuel { burn }
fn boot(seed: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, seed);
    let extracted: Fuel = slot_take(s);
    let _consumed = extracted.draw(1);
    return 0;
}
"#,
    ),
    (
        "slot_take_into_a_call",
        Fence::Identical,
        r#"module main;
cap type Fuel { burn }
fn consume(f: Fuel) -> i64 { return 1; }
fn boot(seed: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, seed);
    return consume(slot_take(s));
}
"#,
    ),
    (
        "slot_put_in_both_branches",
        Fence::Identical,
        r#"module main;
cap type Fuel { burn }
fn boot(cond: i64, c1: Fuel, c2: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    if cond == 1 {
        slot_put(s, c1);
    } else {
        slot_put(s, c2);
    }
    let _taken: Fuel = slot_take(s);
    return 0;
}
"#,
    ),
    (
        "slot_rotation",
        Fence::Identical,
        r#"module main;
cap type Fuel { burn }
fn boot(c1: Fuel, c2: Fuel) -> i64 {
    let s = slot_new::<Fuel>();
    slot_put(s, c1);
    let _first: Fuel = slot_take(s);
    slot_put(s, c2);
    let _second: Fuel = slot_take(s);
    return 0;
}
"#,
    ),
    (
        "slot_of_a_parametric_cap",
        Fence::Identical,
        r#"module main;
cap type Approval(deadline_ms: i64) {}
fn boot(c: Approval(2030)) -> i64 {
    let s = slot_new::<Approval(2030)>();
    slot_put(s, c);
    return 0;
}
"#,
    ),
    (
        "slot_of_a_two_parameter_cap",
        Fence::Identical,
        r#"module main;
cap type Limited(deadline_ms: i64, max_uses: i64) {}
fn boot(c: Limited(2030, 5)) -> i64 {
    let s = slot_new::<Limited(2030, 5)>();
    slot_put(s, c);
    return 0;
}
"#,
    ),
    (
        "slot_take_without_a_put",
        Fence::Identical,
        r#"module tool;
cap type Foo { x }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let s = slot_new::<Foo>();
    let taken = slot_take(s);
    let _consumed = taken.draw(1);
    return 0;
}
"#,
    ),
    (
        "slot_param_and_annotated_let",
        Fence::Identical,
        r#"module m;
cap type Fuel { burn }
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 { slot_put(s, c); return 0; }
fn f(c: Fuel) -> i64 { let s: Slot<Fuel> = slot_new::<Fuel>(); return fill(s, c); }
"#,
    ),
    (
        "slot_copy_and_take_into_put",
        Fence::Identical,
        r#"module m;
cap type Fuel { burn }
fn f(c: Fuel) -> i64 { let s = slot_new::<Fuel>(); let s2 = s; let t = slot_new::<Fuel>(); slot_put(s2, c); slot_put(t, slot_take(s)); return 0; }
"#,
    ),
    (
        "region_scalar_body_in_an_outer_ring",
        Fence::Identical,
        r#"#[ring(outer)] module ext;
fn f(n: i64) -> i64 ! { Alloc } {
    region scratch(64) {
        let inner: i64 = n + 1;
        let used: i64 = inner * 2;
    };
    return n;
}
"#,
    ),
    (
        "region_scalar_body_in_a_tool",
        Fence::Identical,
        r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    region scratch(64) {
        let inner: i64 = input_len + 1;
    };
    return input_len;
}
"#,
    ),
    (
        "region_handle_to_a_region_param",
        Fence::Identical,
        r#"module m;
fn g(r: Region) -> i64 { return 0; }
fn f() -> i64 ! { Alloc } { region buf(64) { let x: i64 = g(buf); }; return 0; }
"#,
    ),
    (
        "region_handle_let",
        Fence::Identical,
        r#"module m;
fn f() -> i64 ! { Alloc } { region buf(64) { let h: Region = buf; }; return 0; }
"#,
    ),
    (
        "region_body_binding_a_record",
        Fence::Refused,
        r#"#[ring(outer)] module ext;
record P { x: i64 }
fn f(secret: i64 @Secret) -> i64 ! { Alloc } {
    region scratch(64) {
        let p: P = P { x: 1 };
    };
    return 0;
}
"#,
    ),
    (
        "region_body_binding_a_str",
        Fence::Refused,
        r#"#[ring(outer)] module ext;
fn f(secret: i64 @Secret) -> i64 ! { Alloc } {
    region scratch(64) {
        let t: str = "abc";
    };
    return 0;
}
"#,
    ),
    (
        "slot_inside_a_region",
        Fence::Refused,
        r#"#[ring(outer)] module ext;
cap type Fuel {}
fn f(secret: i64 @Secret) -> i64 ! { Alloc } {
    region scratch(64) {
        let s: Slot<Fuel> = slot_new::<Fuel>();
    };
    return 0;
}
"#,
    ),
    (
        "grant_of_a_closure",
        Fence::Refused,
        r#"module ext;
cap type C {}
fn f(c: C, g: Fn(&C) -> i64, s: i64) -> i64 {
    let mut a: [i64; 2] = [0, 0];
    let z: i64 = grant(&c, g);
    let y: i64 = a[0];
    return y;
}
"#,
    ),
    (
        "explicit_instantiation_of_a_user_generic",
        Fence::Refused,
        r#"module t;
fn id<T>(x: T) -> T {
    return x;
}
fn f() -> i64 {
    let a: i64 = id::<i64>(1);
    return a;
}
"#,
    ),
];

#[test]
fn shp5c3_fences_hold_on_the_committed_seed() {
    let wrong = fence_failures(SHP5C3_FENCES);
    assert!(
        wrong.is_empty(),
        "SHP-5c-3 named fences moved: {wrong:#?}. A construct pinned Identical that no longer is \
         has regressed in the slot intrinsics, the region typing or the emitter's slot and \
         region arms; one pinned Refused that became Identical needs its rule stated in \
         docs/specs/sh-wasm.md and the pin raised."
    );
}
