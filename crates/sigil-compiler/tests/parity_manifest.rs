//! Compiler-function parity manifest — reproducibility as a standing property.
//!
//! The compiler is a function: source in, `(class, wasm bytes, diagnostics,
//! fuel budget, module names, effect surface)` out. Certificates bind the
//! sha-256 of the emitted wasm, so BYTE stability of that function is a
//! product invariant, not refactor hygiene: any byte drift — a wasm-encoder
//! bump that pads differently, an incidental reordering — silently breaks
//! reproducibility for previously certified artifacts even when nothing
//! changed semantically. The existing pins cover the three self-host
//! artifacts; this manifest extends the same guarantee to the whole fixture
//! corpus, so extensional equality of the compiler function is checked on
//! every CI run rather than asserted in PR prose.
//!
//! ## The PR-class contract
//!
//! Every change is one of two classes, and this test enforces the declared
//! class mechanically:
//!
//! * **Parity-preserving** (refactors, dependency bumps, comment/doc work,
//!   style rewrites): `tests/parity/manifest.tsv` must be UNTOUCHED in the
//!   diff. This test green + manifest unchanged = extensional equality over
//!   the corpus, and the reviewer can verify the claim from those two facts.
//! * **Output-changing** (features, codegen changes, diagnostic wording):
//!   regenerate via the ritual below and commit the manifest diff. The diff
//!   is review content — every changed row names a fixture whose observable
//!   outputs changed, so a feature that unexpectedly churns an unrelated
//!   fixture is exactly what the reviewer sees.
//!
//! Regeneration ritual (deliberately env-armed, mirroring the seed
//! succession ritual in `pipeline_differential.rs` — `#[ignore]` alone is
//! not a guard because `--include-ignored` runs it):
//!
//! ```text
//! SIGIL_PARITY_REGENERATE=1 cargo test -p sigil-compiler --no-default-features \
//!     --test parity_manifest -- --ignored regenerate_parity_manifest --nocapture
//! ```
//!
//! `--no-default-features` is load-bearing: the crate's defaults include
//! `solver`, this file is compiled out under `solver`, and `cargo test`
//! exits 0 on zero tests — the un-flagged spelling is a silent no-op that
//! looks like success. `REGEN_CMD` is the single authoritative copy.
//!
//! ## What is pinned, per fixture
//!
//! * `class` — `ok`, `reject`, or `non-utf8` (a fail-closed placeholder for
//!   a fixture that is not valid UTF-8; accept/reject flips are the loudest
//!   drift).
//! * `source` — sha-256 of the fixture bytes as checked out. A fixture edit
//!   therefore changes its own row visibly; rows are keyed by path so the
//!   edit reads as a row change, not a silent regeneration.
//! * `inner` / `outer` — sha-256 of the emitted wasm byte vectors (`outer`
//!   is `-` when the compilation has no outer module).
//! * `diag` — sha-256 of a canonical rendering of every diagnostic in
//!   emission order: code, severity, message, effective hint, span, source
//!   attribution. On reject rows these are the errors; on ok rows these are
//!   the compilation's WARNINGS (the success path's user-visible channel),
//!   `-` when there are none. Message and hint text are user-visible
//!   behavior; rewording them is an output-changing PR by definition.
//! * `meta` — sha-256 over fuel budget, module names, and the required
//!   effect surface: the certificate-relevant outputs beyond the bytes.
//!
//! ## Corpus scope, and the exclusions with reasons
//!
//! Included roots are listed in `ROOTS`. Excluded deliberately:
//!
//! * `crates/sigil-compiler/tests/z3_corpus` — verdicts are feature-
//!   dependent by design (the solver lane proves what the default lane
//!   fails closed on), so those fixtures have no single-lane byte pin.
//!   This whole file is compiled out under the solver feature for the same
//!   reason: the manifest pins the DEFAULT (shipped-CLI) configuration.
//! * `selfhost/` — already byte-pinned to the ledger, and the composed
//!   artifact (not the per-file compile) is the meaningful unit there.
//! * `bench/fixtures/` — checked out `-text` as byte-exact forge inputs
//!   with their own verification lane.
//! * `seed/` — binary wasm, digest-pinned by the seed lane.
//!
//! Line endings: `.gitattributes` pins `*.sigil` and `*.tsv` to LF, so the
//! hashes agree on the Windows portability lane, which runs this test. The
//! parser below still strips a stray `\r` belt-and-braces.

#![cfg(not(feature = "solver"))]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};
use sigil_compiler::compile_module;
use sigil_compiler::diagnostics::Diagnostic;

const MANIFEST_REL: &str = "tests/parity/manifest.tsv";

/// The one authoritative regeneration invocation, referenced from the
/// manifest header and every failure message so the copies cannot drift.
/// See the module docs for why `--no-default-features` is load-bearing.
const REGEN_CMD: &str = "SIGIL_PARITY_REGENERATE=1 cargo test -p sigil-compiler \
     --no-default-features --test parity_manifest -- --ignored regenerate_parity_manifest --nocapture";

/// Corpus roots, relative to the workspace root, walked recursively for
/// `.sigil` files. Adding a root is an output-changing PR (new rows).
const ROOTS: &[&str] = &[
    "tests/compile",
    "tests/reject",
    "tests/attack",
    "tests/runtime",
    "tests/frontends",
    "crates/sigil-compiler/tests/fixtures",
    "crates/sigil-compiler/tests/precision_corpus",
    "crates/sigil-compiler/tests/cve_corpus",
    "stdlib",
];

/// Deletion ratchet: the regenerator refuses to write a manifest smaller
/// than this, and the checker asserts the committed manifest meets it, so
/// a broken walker or a mass fixture deletion cannot quietly shrink the
/// pinned surface. Measured at introduction (SC-P1: pin the measured value);
/// raise freely as the corpus grows, lower only with a stated reason.
const PARITY_FLOOR: usize = 243;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/sigil-compiler has a workspace root two levels up")
        .to_path_buf()
}

/// Every `.sigil` file under the corpus roots, as sorted workspace-relative
/// forward-slash paths (forward slashes so rows are identical on Windows).
fn walk_corpus() -> Vec<String> {
    let root = workspace_root();
    let mut found = Vec::new();
    for dir in ROOTS {
        let abs = root.join(dir);
        assert!(
            abs.is_dir(),
            "corpus root `{dir}` is missing — if it was renamed, update ROOTS \
             and regenerate; if it was deleted, that is an output-changing PR"
        );
        walk_into(&abs, &root, &mut found);
    }
    found.sort();
    found
}

fn walk_into(dir: &Path, root: &Path, out: &mut Vec<String>) {
    for entry in fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display())) {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            walk_into(&path, root, out);
        } else if path.extension().is_some_and(|x| x == "sigil") {
            let rel = path
                .strip_prefix(root)
                .expect("walked path is under the workspace root")
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
            out.push(rel);
        }
    }
}

fn sha_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    format!("{:x}", h.finalize())
}

/// One manifest row. Field order matches the serialized column order.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    class: String,
    source: String,
    inner: String,
    outer: String,
    diag: String,
    meta: String,
}

/// Canonical, accessor-based rendering of every diagnostic in emission
/// order. Built from the structured fields rather than the display
/// renderer so the pin is on WHAT is reported (code, severity, message,
/// effective hint, span, attribution), independent of presentation-layer
/// formatting. Fields are joined with an ASCII unit separator so no field
/// text can collide with the framing.
fn canonical_diagnostics(diags: &[Diagnostic]) -> String {
    let mut out = String::new();
    for d in diags {
        let span = match d.span() {
            Some(s) => format!("{}..{}@{:?}", s.start, s.end, s.source),
            None => "-".to_string(),
        };
        out.push_str(&format!(
            "{}\x1f{:?}\x1f{}\x1f{}\x1f{}\x1f{}\n",
            d.code(),
            d.severity(),
            d.message(),
            d.hint().unwrap_or("-"),
            span,
            d.source_name().unwrap_or("-"),
        ));
    }
    out
}

/// Compute the parity row for one fixture: run the compiler function and
/// hash each observable output channel.
fn compute_row(bytes: &[u8]) -> Row {
    let source_sha = sha_hex(bytes);
    let Ok(src) = std::str::from_utf8(bytes) else {
        // Fail-closed placeholder rather than a panic: a non-UTF-8 fixture
        // still gets a stable, visible row instead of taking down the run.
        return Row {
            class: "non-utf8".into(),
            source: source_sha,
            inner: "-".into(),
            outer: "-".into(),
            diag: "-".into(),
            meta: "-".into(),
        };
    };
    match compile_module(src) {
        Ok(c) => {
            let meta = format!(
                "fuel={}\x1fmodules={}\x1feffects={}",
                c.fuel_budget,
                c.module_names.join(","),
                c.effects_required.join(","),
            );
            Row {
                class: "ok".into(),
                source: source_sha,
                inner: sha_hex(&c.wasm_inner),
                outer: c.wasm_outer.as_deref().map_or("-".into(), sha_hex),
                // Warnings are the success path's user-visible diagnostic
                // channel (parser warnings, the read-only lint). Empty for
                // the whole corpus today, so this stays `-` until a fixture
                // exercises it — but the channel is pinned, not dropped.
                diag: if c.warnings.is_empty() {
                    "-".into()
                } else {
                    sha_hex(canonical_diagnostics(&c.warnings).as_bytes())
                },
                meta: sha_hex(meta.as_bytes()),
            }
        }
        Err(e) => Row {
            class: "reject".into(),
            source: source_sha,
            inner: "-".into(),
            outer: "-".into(),
            diag: sha_hex(canonical_diagnostics(e.diagnostics()).as_bytes()),
            meta: "-".into(),
        },
    }
}

fn compute_all() -> BTreeMap<String, Row> {
    let root = workspace_root();
    walk_corpus()
        .into_iter()
        .map(|rel| {
            let bytes = fs::read(root.join(&rel))
                .unwrap_or_else(|e| panic!("reading fixture `{rel}`: {e}"));
            // A compiler panic (neither Ok nor Err) must stay a loud
            // failure, but a bare unwind does not say WHICH fixture —
            // name it, then resume so the original message survives.
            let row = std::panic::catch_unwind(|| compute_row(&bytes)).unwrap_or_else(|cause| {
                eprintln!("compiler panicked while compiling fixture `{rel}`");
                std::panic::resume_unwind(cause)
            });
            (rel, row)
        })
        .collect()
}

fn serialize(rows: &BTreeMap<String, Row>) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "# Compiler-function parity manifest. One row per corpus fixture:\n\
         # path<TAB>class<TAB>sha256(source)<TAB>sha256(wasm_inner)<TAB>sha256(wasm_outer)<TAB>sha256(diagnostics)<TAB>sha256(meta)\n\
         # class is one of: ok, reject, non-utf8.\n\
         # Contract: parity-preserving PRs leave this file untouched; output-changing\n\
         # PRs regenerate it and the row diff is review content. Checked by\n\
         # crates/sigil-compiler/tests/parity_manifest.rs; regenerate with\n\
         # {}\n",
        REGEN_CMD.replace('\n', " ")
    ));
    for (path, r) in rows {
        out.push_str(&format!(
            "{path}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            r.class, r.source, r.inner, r.outer, r.diag, r.meta
        ));
    }
    out
}

fn parse(text: &str) -> BTreeMap<String, Row> {
    let mut rows = BTreeMap::new();
    for (i, raw) in text.lines().enumerate() {
        let line = raw.strip_suffix('\r').unwrap_or(raw);
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        assert!(
            f.len() == 7,
            "{MANIFEST_REL}:{}: expected 7 tab-separated columns, found {}",
            i + 1,
            f.len()
        );
        let prev = rows.insert(
            f[0].to_string(),
            Row {
                class: f[1].into(),
                source: f[2].into(),
                inner: f[3].into(),
                outer: f[4].into(),
                diag: f[5].into(),
                meta: f[6].into(),
            },
        );
        assert!(
            prev.is_none(),
            "{MANIFEST_REL}: duplicate row for `{}`",
            f[0]
        );
    }
    rows
}

/// The comparison itself, factored out so the anti-stub below can prove it
/// has teeth. Returns one human-readable finding per difference.
fn diff_rows(committed: &BTreeMap<String, Row>, computed: &BTreeMap<String, Row>) -> Vec<String> {
    let mut findings = Vec::new();
    for (path, want) in committed {
        match computed.get(path) {
            None => findings.push(format!(
                "`{path}`: row is committed but the fixture no longer exists (or left ROOTS)"
            )),
            Some(got) if got != want => {
                for (col, w, g) in [
                    ("class", &want.class, &got.class),
                    ("source", &want.source, &got.source),
                    ("inner", &want.inner, &got.inner),
                    ("outer", &want.outer, &got.outer),
                    ("diag", &want.diag, &got.diag),
                    ("meta", &want.meta, &got.meta),
                ] {
                    if w != g {
                        findings.push(format!(
                            "`{path}`: column `{col}` committed {w} != computed {g}"
                        ));
                    }
                }
            }
            Some(_) => {}
        }
    }
    for path in computed.keys() {
        if !committed.contains_key(path) {
            findings.push(format!("`{path}`: fixture exists but has no committed row"));
        }
    }
    findings
}

/// The checker: the committed manifest and the freshly computed corpus must
/// agree exactly — set-equal on paths, byte-equal per column.
#[test]
fn parity_manifest_matches_the_committed_rows() {
    let manifest_path = workspace_root().join(MANIFEST_REL);
    let text = fs::read_to_string(&manifest_path).unwrap_or_else(|e| {
        panic!(
            "cannot read {MANIFEST_REL}: {e}\nIf this is a fresh corpus, regenerate:\n  {REGEN_CMD}"
        )
    });
    let committed = parse(&text);
    assert!(
        committed.len() >= PARITY_FLOOR,
        "committed manifest has {} rows, below the deletion floor {PARITY_FLOOR}. \
         If the corpus genuinely shrank, lower the floor with a stated reason, then:\n  {REGEN_CMD}",
        committed.len()
    );

    let computed = compute_all();
    let findings = diff_rows(&committed, &computed);
    assert!(
        findings.is_empty(),
        "compiler-function parity drift: {} difference(s) against {MANIFEST_REL}.\n\
         \n{}\n\n\
         If this PR is parity-preserving, the change above is an accidental behavior \
         change — fix the code, not the manifest. If it is output-changing, regenerate:\n  \
         {REGEN_CMD}\n\
         and commit the manifest diff as review content.",
        findings.len(),
        findings.join("\n"),
    );
}

/// Anti-stub: prove the comparator reports every kind of drift it claims to
/// catch — EVERY column individually (the review pass showed a one-column
/// exercise would tolerate a comparator blind to the other five), plus a
/// missing fixture and an unpinned fixture.
#[test]
fn parity_comparator_detects_each_drift_kind() {
    let base = Row {
        class: "ok".into(),
        source: "s".into(),
        inner: "i".into(),
        outer: "o".into(),
        diag: "d".into(),
        meta: "m".into(),
    };

    for col in ["class", "source", "inner", "outer", "diag", "meta"] {
        let mut drifted = base.clone();
        match col {
            "class" => drifted.class = "DRIFT".into(),
            "source" => drifted.source = "DRIFT".into(),
            "inner" => drifted.inner = "DRIFT".into(),
            "outer" => drifted.outer = "DRIFT".into(),
            "diag" => drifted.diag = "DRIFT".into(),
            _ => drifted.meta = "DRIFT".into(),
        }
        let committed = BTreeMap::from([("a.sigil".to_string(), base.clone())]);
        let computed = BTreeMap::from([("a.sigil".to_string(), drifted)]);
        let findings = diff_rows(&committed, &computed);
        assert!(
            findings.iter().any(|f| f.contains(&format!("`{col}`"))),
            "a drift in column `{col}` went unreported: {findings:?}"
        );
    }

    let mut committed = BTreeMap::new();
    committed.insert("a.sigil".to_string(), base.clone());
    committed.insert("gone.sigil".to_string(), base.clone());
    let mut computed = BTreeMap::new();
    computed.insert("a.sigil".to_string(), base.clone());
    computed.insert("new.sigil".to_string(), base);
    let findings = diff_rows(&committed, &computed);
    assert_eq!(
        findings.len(),
        2,
        "expected exactly two findings: {findings:?}"
    );
    assert!(findings.iter().any(|f| f.contains("gone.sigil")));
    assert!(findings.iter().any(|f| f.contains("new.sigil")));

    let clean = diff_rows(&committed, &committed);
    assert!(clean.is_empty(), "identical maps must produce no findings");
}

/// Determinism spot-check: the row computation must be a pure function of
/// the fixture bytes. Double-computes one fixture of EACH class — ok and
/// reject hash different channels (wasm bytes + meta vs diagnostics), so
/// each must be checked; any wall-clock, map-ordering, or cache leakage
/// fails here before it fails confusingly in the full comparison.
#[test]
fn parity_row_computation_is_deterministic() {
    let root = workspace_root();
    let mut checked_ok = false;
    let mut checked_reject = false;
    for rel in walk_corpus() {
        let bytes = fs::read(root.join(&rel)).expect("fixture readable");
        let a = compute_row(&bytes);
        match a.class.as_str() {
            "ok" if !checked_ok => checked_ok = true,
            "reject" if !checked_reject => checked_reject = true,
            _ => continue,
        }
        let b = compute_row(&bytes);
        assert_eq!(
            a, b,
            "row for `{rel}` differs across two computations in-process"
        );
        if checked_ok && checked_reject {
            return;
        }
    }
    panic!("corpus must contain both classes (found ok={checked_ok}, reject={checked_reject})");
}

/// The regenerator must stay ignored and env-armed: an un-ignored
/// regenerator would rewrite the manifest on every plain test run,
/// converting the pin into an echo. The needles are assembled with
/// `concat!` so this test's own source cannot satisfy the scan (the
/// review pass mutation-proved the naive spelling was vacuous exactly
/// that way), and the marker count is pinned to one so a decoy
/// occurrence cannot redirect the search.
#[test]
fn parity_regenerator_stays_ignored_and_env_armed() {
    let src = include_str!("parity_manifest.rs");
    let marker = concat!("fn regenerate_", "parity_manifest");
    assert_eq!(
        src.matches(marker).count(),
        1,
        "expected exactly one regenerator definition; a decoy would redirect this scan"
    );
    let fn_pos = src.find(marker).expect("regenerator exists");
    let attr_needle = concat!("#[ig", "nore = \"rewrites tests/parity/manifest.tsv");
    let preceding = &src[..fn_pos];
    let attr_block = &preceding[preceding.len().saturating_sub(400)..];
    assert!(
        attr_block.contains(attr_needle),
        "the regenerator has lost its ignore attribute"
    );
    let arming_needle = concat!("std::env::var(\"SIGIL_PARITY_", "REGENERATE\")");
    let body = &src[fn_pos..];
    assert!(
        body.contains(arming_needle),
        "the regenerator has lost its env-var arming check"
    );
}

/// Regeneration ritual — see the module docs for when this is legitimate.
/// Refuses to shrink the corpus below the deletion floor.
#[test]
#[ignore = "rewrites tests/parity/manifest.tsv; set SIGIL_PARITY_REGENERATE=1 and run with --ignored"]
fn regenerate_parity_manifest() {
    let armed = std::env::var("SIGIL_PARITY_REGENERATE").is_ok_and(|v| v == "1");
    assert!(
        armed,
        "refusing to regenerate: set SIGIL_PARITY_REGENERATE=1 to arm \
         (--include-ignored alone must not rewrite the pin)"
    );
    let rows = compute_all();
    assert!(
        rows.len() >= PARITY_FLOOR,
        "regeneration would write {} rows, below the deletion floor {PARITY_FLOOR}; \
         if the corpus genuinely shrank, lower the floor with a stated reason first",
        rows.len()
    );
    let path = workspace_root().join(MANIFEST_REL);
    fs::create_dir_all(path.parent().expect("manifest has a parent dir")).expect("mkdir");
    fs::write(&path, serialize(&rows)).expect("write manifest");
    println!("wrote {} rows to {MANIFEST_REL}", rows.len());
}
