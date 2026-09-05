//! Ground truth for the independent interpreter's differential (`interp/`, Phase 2).
//!
//! WHY A COMMITTED GOLDEN. `interp/` is a second SIGIL implementation whose binary lineage does
//! not pass through the Rust oracle — that is the point (docs/CLAIMS.md, HB-3). It cannot run
//! WASM, and it is forbidden third-party packages, so it cannot compute the reference answers for
//! itself. This test computes them and commits them; the Python side only ever *reads* the file.
//!
//! WHY IT CANNOT GO STALE. A committed answer key is exactly the artifact that drifts, so the
//! generator is `#[ignore]`d and a normal test RECOMPUTES every entry and asserts the committed
//! file already matches. Changing the lexer without regenerating fails here rather than silently
//! grading the interpreter against a stale key.
//!
//! WHAT IS COMPARED. `encode(lex(src))` — the same `records|pool` encoding
//! `lexer_differential.rs` uses, produced by the SAME SIGIL source. Both sides execute
//! `selfhost/lexer.sigil`; only the machine underneath differs (wasmtime here, a tree-walking
//! evaluator there). A disagreement is therefore an interpreter-semantics bug, which is precisely
//! what this harness exists to surface.

use sigil_compiler::compile_tool;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const NAME_RESOLUTION: &str = include_str!("../../../selfhost/name_resolution.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const RING_CHECK: &str = include_str!("../../../selfhost/ring_check.sigil");
const EFFECT_CHECK: &str = include_str!("../../../selfhost/effect_check.sigil");
const TAINT_CHECK: &str = include_str!("../../../selfhost/taint_check.sigil");
const CAP_CHECK: &str = include_str!("../../../selfhost/cap_check.sigil");
const OWN_CHECK: &str = include_str!("../../../selfhost/own_check.sigil");
const AIR: &str = include_str!("../../../selfhost/air.sigil");
const MONOMORPH: &str = include_str!("../../../selfhost/monomorph.sigil");
const PIPELINE: &str = include_str!("../../../selfhost/pipeline.sigil");
const FUEL: u64 = 3_000_000_000;

/// Fixture programs, chosen to exercise the token classes the certified source actually uses:
/// keywords, identifiers, punctuation, integers (decimal and hex), strings with escapes,
/// comments, effect rows, generics, and the `>>` shift that must not be read as a generic close.
const CORPUS: &[(&str, &str)] = &[
    ("empty", ""),
    ("module_only", "module m;\n"),
    (
        "fn_scalar",
        "module m;\nfn f(a: i64) -> i64 { return a + 1; }\n",
    ),
    (
        "record_impl",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\n",
    ),
    (
        "string_escapes",
        "module m;\nfn g() -> str { return \"a\\nb\\\"c\\\\d\"; }\n",
    ),
    (
        "int_forms",
        "module m;\nfn h() -> i64 { let a: i64 = 0; let b: i64 = 1234567890; return a + b; }\n",
    ),
    (
        "comments",
        "module m;\n// line comment\nfn c() -> i64 { return 0; } // trailing\n",
    ),
    (
        "effect_row",
        "module m;\nfn e() -> i64 ! { Alloc } { return 0; }\n",
    ),
    (
        "generics",
        "module m;\nfn id(v: Vec<Vec<i64>>) -> i64 { return 0; }\n",
    ),
    (
        "shift",
        "module m;\nfn s(v: i64) -> i64 { return v >> 7; }\n",
    ),
    (
        "bools_and_cmp",
        "module m;\nfn b(x: i64) -> bool { return x <= 3; }\n",
    ),
    (
        "while_loop",
        "module m;\nfn w(n: i64) -> i64 { let mut i: i64 = 0; while i < n { i = i + 1; } return i; }\n",
    ),
    (
        "match_arms",
        "module m;\nfn m2(x: i64) -> i64 { match x { 1 => { return 1; }, _ => { return 0; } } }\n",
    ),
    (
        "unicode_string",
        "module m;\nfn u() -> str { return \"héllo\"; }\n",
    ),
    (
        "nested_calls",
        "module m;\nfn a1(x: i64) -> i64 { return x; }\nfn b1(x: i64) -> i64 { return a1(a1(x)); }\n",
    ),
];

fn lexer_tool(body: &str) -> String {
    let defs = LEXER.replace("\nmodule lexer;\n", "\n");
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn lexer_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
            \x20   let src: str = opt.unwrap_or(\"\");\n\
            \x20   let toks: Vec<Token> = lex(src);\n\
            \x20   let enc: str = encode(toks);\n\
            \x20   return enc.as_output();";
        compile_tool(&lexer_tool(body))
            .expect("the lexer tool compiles")
            .wasm
    })
}

fn encode_tokens(source: &str) -> String {
    let out = execute_ephemeral(lexer_wasm(), source.as_bytes(), FUEL, &IoGrants::none())
        .expect("the lexer tool executes")
        .output;
    String::from_utf8(out).expect("the encoding is UTF-8")
}

/// The PARSE side of the differential: `parser_encode(parser_parse(...))`, the same surface
/// `parser_differential.rs` compares. Adding it moves the interpreter's evidence from "reads
/// tokens correctly" to "builds the same tree", which is the layer the checkers all consume.
fn parser_tool(body: &str) -> String {
    let lexer = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser = PARSER.replace("\nmodule parser;\n", "\n");
    format!(
        "module tool;\n{lexer}\n{parser}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn parser_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
            \x20   let src: str = opt.unwrap_or(\"\");\n\
            \x20   let toks: Vec<Token> = lex(src);\n\
            \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
            \x20   let mut kids: Vec<i64> = Vec::new();\n\
            \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
            \x20   let enc: str = parser_encode(nodes, kids, root);\n\
            \x20   return enc.as_output();";
        compile_tool(&parser_tool(body))
            .expect("the parser tool compiles")
            .wasm
    })
}

fn encode_parse(source: &str) -> String {
    let out = execute_ephemeral(parser_wasm(), source.as_bytes(), FUEL, &IoGrants::none())
        .expect("the parser tool executes")
        .output;
    String::from_utf8(out).expect("the encoding is UTF-8")
}

/// The first CHECKER gate. Beyond the front end, this is the layer where the interpreter starts
/// reproducing verdicts rather than syntax — the shape the Phase-5 DDC comparison depends on.
fn nr_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let lexer = LEXER.replace("\nmodule lexer;\n", "\n");
        let parser = PARSER.replace("\nmodule parser;\n", "\n");
        let nr = NAME_RESOLUTION.replace("\nmodule name_resolution;\n", "\n");
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
            \x20   let src: str = opt.unwrap_or(\"\");\n\
            \x20   let toks: Vec<Token> = lex(src);\n\
            \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
            \x20   let mut kids: Vec<i64> = Vec::new();\n\
            \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
            \x20   let enc: str = nr_encode(nodes, kids, root);\n\
            \x20   return enc.as_output();";
        let source = format!(
            "module tool;\n{lexer}\n{parser}\n{nr}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
        );
        compile_tool(&source)
            .expect("the name-resolution tool compiles")
            .wasm
    })
}

/// THE WHOLE COMPILER: `sh_compile` — nr → tc → ring → effect → taint → cap → own → emit, the
/// frozen protocol (`OK:<hex>` or `REJECT:<stage>:<codes>`). This is the comparison Phase 5
/// depends on: if the interpreter reproduces this, it reproduces the compiler's OUTPUT BYTES, and
/// the DDC argument has something to stand on.
fn compiler_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let m = |src: &str, header: &str| src.replace(header, "\n");
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
            \x20   let src: str = opt.unwrap_or(\"\");\n\
            \x20   let toks: Vec<Token> = lex(src);\n\
            \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
            \x20   let mut kids: Vec<i64> = Vec::new();\n\
            \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
            \x20   let e: i64 = mn_expand(nodes, kids, root);\n\
            \x20   let enc: str = sh_compile(nodes, kids, root);\n\
            \x20   return enc.as_output();";
        let source = format!(
            "module tool;\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n",
            m(LEXER, "\nmodule lexer;\n"),
            m(PARSER, "\nmodule parser;\n"),
            m(NAME_RESOLUTION, "\nmodule name_resolution;\n"),
            m(TYPECHECK, "\nmodule typecheck;\n"),
            m(RING_CHECK, "\nmodule ring_check;\n"),
            m(EFFECT_CHECK, "\nmodule effect_check;\n"),
            m(TAINT_CHECK, "\nmodule taint_check;\n"),
            m(CAP_CHECK, "\nmodule cap_check;\n"),
            m(OWN_CHECK, "\nmodule own_check;\n"),
            m(AIR, "\nmodule air;\n"),
            m(MONOMORPH, "\nmodule monomorph;\n"),
            m(PIPELINE, "\nmodule pipeline;\n"),
        );
        compile_tool(&source)
            .expect("the composed compiler tool compiles")
            .wasm
    })
}

fn encode_compile(source: &str) -> String {
    let out = execute_ephemeral(compiler_wasm(), source.as_bytes(), FUEL, &IoGrants::none())
        .expect("the composed compiler tool executes")
        .output;
    String::from_utf8(out).expect("the encoding is UTF-8")
}

fn encode_nr(source: &str) -> String {
    let out = execute_ephemeral(nr_wasm(), source.as_bytes(), FUEL, &IoGrants::none())
        .expect("the name-resolution tool executes")
        .output;
    String::from_utf8(out).expect("the encoding is UTF-8")
}

/// Minimal JSON string escaping — enough for the fixtures above, and asserted below to round-trip.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn render_golden() -> String {
    let mut out = String::from("[\n");
    for (i, (name, src)) in CORPUS.iter().enumerate() {
        let enc = encode_tokens(src);
        out.push_str("  {\"name\": \"");
        out.push_str(&json_escape(name));
        out.push_str("\", \"source\": \"");
        out.push_str(&json_escape(src));
        out.push_str("\", \"encoded\": \"");
        out.push_str(&json_escape(&enc));
        out.push_str("\", \"parsed\": \"");
        out.push_str(&json_escape(&encode_parse(src)));
        out.push_str("\", \"resolved\": \"");
        out.push_str(&json_escape(&encode_nr(src)));
        out.push_str("\", \"compiled\": \"");
        out.push_str(&json_escape(&encode_compile(src)));
        out.push_str("\"}");
        if i + 1 < CORPUS.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push_str("]\n");
    out
}

fn golden_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("sigil-runtime lives under crates/")
        .join("interp")
        .join("corpus")
        .join("golden.json")
}

/// THE GENERATOR (run when the corpus or the lexer changes):
///
///   cargo test -p sigil-runtime --test interp_corpus regenerate -- --ignored --nocapture
#[test]
#[ignore = "regenerates interp/corpus/golden.json"]
fn regenerate_interp_golden() {
    let path = golden_path();
    std::fs::create_dir_all(path.parent().expect("corpus dir")).expect("create corpus dir");
    let rendered = render_golden();
    std::fs::write(&path, &rendered).expect("write golden");
    println!(
        "wrote {} ({} fixtures, {} bytes)",
        path.display(),
        CORPUS.len(),
        rendered.len()
    );
}

/// The committed answer key must equal what the lexer produces TODAY. This is what stops the
/// interpreter being graded against a stale reference.
#[test]
fn interp_golden_is_current() {
    let path = golden_path();
    let committed = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "interp/corpus/golden.json is committed ({}): {e}\nRegenerate with: cargo test \
             -p sigil-runtime --test interp_corpus regenerate -- --ignored --nocapture",
            path.display()
        )
    });
    let current = render_golden();
    assert_eq!(
        committed.replace("\r\n", "\n"),
        current,
        "the committed interpreter golden is STALE — the lexer or the corpus moved. Regenerate it \
         in the SAME change: cargo test -p sigil-runtime --test interp_corpus regenerate -- \
         --ignored --nocapture"
    );
}

/// Run a script under `interp/` and return its stdout, failing loudly on a non-zero exit.
///
/// Python is already a hard dependency of this repository (the hygiene lane lints `bench/` and
/// `interp/` with ruff), so a missing interpreter is a broken environment and must FAIL rather
/// than silently skip — a skipped proof is the failure mode the ledger exists to prevent.
fn run_interp_script(name: &str, context: &str) -> String {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("sigil-runtime lives under crates/");
    let script = repo.join("interp").join(name);

    let mut last_err = String::new();
    for exe in ["python3", "python"] {
        match std::process::Command::new(exe).arg(&script).output() {
            Ok(out) => {
                let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                let stderr = String::from_utf8_lossy(&out.stderr);
                assert!(
                    out.status.success(),
                    "{context}\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
                );
                return stdout;
            }
            Err(e) => last_err = format!("{exe}: {e}"),
        }
    }
    panic!(
        "no Python interpreter found ({last_err}). Python is required by this repository \
         (the hygiene lane lints bench/ and interp/); this proof cannot be skipped."
    );
}

/// docs/CLAIMS.md claim 41: the interpreter agrees with the oracle LAYER BY LAYER.
///
/// WHY THIS EXISTS. Claim 41 used to cite `interp_golden_is_current` and
/// `interp_golden_is_not_vacuous` — but neither invokes the interpreter. They assert the answer
/// key is current and non-trivial, which is Rust checking Rust. The comparison the claim actually
/// describes lives in `interp/test_differential.py`, and it ran only in the `hygiene` lane, which
/// is NOT a required check. So the claim's real evidence was neither named by a tag the ledger
/// could verify nor merge-gating. Deleting that CI step would have left claim 41 backed by
/// nothing, with every ledger check still green. Same reasoning as the DDC test below.
#[test]
fn interp_differential_agrees_layer_by_layer() {
    let stdout = run_interp_script(
        "test_differential.py",
        "the independent interpreter disagrees with the oracle on one or more layers",
    );
    assert!(
        stdout.contains("reproduce the oracle"),
        "the differential exited 0 without reporting a verdict — it may not have compared \
         anything:\n{stdout}"
    );
}

/// Does some workflow line actually RUN the gated DDC target?
///
/// Deliberately stricter than a substring scan over the whole file, which a COMMENTED-OUT line
/// satisfies and which would accept the two flags appearing on different invocations. The line
/// must be a `run:` step (after any `- ` list marker), not a comment, and must carry both the
/// target and its feature — cargo silently skips a target whose `required-features` are off.
fn ddc_lane_is_invoked(ci: &str) -> bool {
    ci.lines().map(str::trim).any(|line| {
        let line = line.strip_prefix("- ").unwrap_or(line);
        if line.starts_with('#') {
            return false;
        }
        let Some(cmd) = line.strip_prefix("run:") else {
            return false;
        };
        // The COMMAND must be cargo test — not an `echo` that merely mentions it, which a
        // `contains("cargo test")` scan happily accepts. `--no-run` compiles and stops; `--skip`
        // filters the only test out.
        let cmd = cmd.trim_start();
        cmd.starts_with("cargo test")
            && !cmd.contains("--no-run")
            && !cmd.contains("--skip")
            && cmd.contains("--test interp_ddc")
            && cmd.contains("--features ddc")
    })
}

/// Does the `interp-ddc` job carry a job-level `if:`?
///
/// This is the sharpest way to un-gate the proof without touching a single check: GitHub reports a
/// job skipped by a job-level `if:` as a SKIPPED check, and branch protection treats skipped as
/// satisfied. The job declaration would still exist for PIN-5, the `run:` line would still exist
/// for the matcher, and claim 40 would simply stop executing on pull requests. The idiom is
/// already used elsewhere in this workflow (`merge-audit`), so it is one copy-paste away.
fn ddc_job_has_conditional(ci: &str) -> bool {
    let Some(rest) = ci.split_once("\n  interp-ddc:") else {
        return false;
    };
    // Scan to the next top-level job (a line starting with exactly two spaces then a name).
    rest.1
        .lines()
        .take_while(|l| {
            !(l.starts_with("  ") && !l.starts_with("   ") && l.trim_end().ends_with(':'))
        })
        .any(|l| {
            let t = l.trim();
            !t.starts_with('#') && (t.starts_with("if:") || t.starts_with("continue-on-error:"))
        })
}

/// THE GATE'S OWN FENCE. `interp_ddc_reproduces_the_committed_seed` lives in a
/// `required-features = ["ddc"]` target so it can run in its own parallel CI lane instead of
/// serialising into `test`. That is a SECOND way to own a proof that never runs — the ledger's
/// name-based checks see a real, un-`#[ignore]`d `#[test]` and are satisfied, while
/// `cargo test --workspace` quietly skips it. Deleting the lane would leave claim 40 backed by
/// nothing, with every ledger check green.
///
/// So this test — which DOES run by default — reads the workflow and requires a job to invoke
/// that target. It is the same reasoning that put the DDC in the Rust suite in the first place:
/// a claim's proof has to be something a check can confirm actually executes.
#[test]
fn interp_ddc_lane_is_wired_in_ci() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("sigil-runtime lives under crates/");
    let ci = std::fs::read_to_string(repo.join(".github").join("workflows").join("ci.yml"))
        .expect(".github/workflows/ci.yml is committed");

    assert!(
        ddc_lane_is_invoked(&ci),
        "no CI job RUNS `--test interp_ddc` with `--features ddc` on a single `run:` line. The \
         DDC comparison is claim 40's proof and it is feature-gated, so without a lane invoking \
         it the claim is backed by nothing while every ledger check stays green. Restore the \
         lane, or un-gate the test and accept the cost."
    );

    // SC-P4 with SYNTHETIC input, both directions. The previous anti-stub asserted that a
    // made-up needle was absent from the real file — a property of `str::contains`, not evidence
    // the matcher can miss. These feed the matcher text and check it answers correctly.
    assert!(
        ddc_lane_is_invoked(
            "jobs:\n  x:\n    steps:\n      - run: cargo test --test interp_ddc --features ddc\n"
        ),
        "anti-stub: the matcher must ACCEPT a real invocation"
    );
    assert!(
        !ddc_lane_is_invoked("jobs:\n  x:\n    steps:\n      - run: cargo test --workspace\n"),
        "anti-stub: the matcher must REJECT a workflow that never names the target"
    );
    assert!(
        !ddc_lane_is_invoked("      # run: cargo test --test interp_ddc --features ddc\n"),
        "anti-stub: a COMMENTED-OUT invocation must not satisfy the fence"
    );
    assert!(
        !ddc_lane_is_invoked("      - run: cargo test --test interp_ddc\n"),
        "anti-stub: naming the target without `--features ddc` must not satisfy the fence — cargo \
         silently skips a target whose required feature is off"
    );
    assert!(
        !ddc_lane_is_invoked("      - run: cargo test --features ddc --test something_else\n"),
        "anti-stub: the two flags must be on the SAME invocation"
    );
    assert!(
        !ddc_lane_is_invoked(
            "      - run: echo 'locally: cargo test --test interp_ddc --features ddc'\n"
        ),
        "anti-stub: merely MENTIONING the command must not satisfy the fence"
    );
    assert!(
        !ddc_lane_is_invoked("      - run: cargo test --test interp_ddc --features ddc --no-run\n"),
        "anti-stub: `--no-run` compiles without running and must not satisfy the fence"
    );
    assert!(
        !ddc_lane_is_invoked(
            "      - run: cargo test --test interp_ddc --features ddc -- --skip interp_ddc\n"
        ),
        "anti-stub: filtering the only test out must not satisfy the fence"
    );

    // A job-level `if:` skips the job, and GitHub reports a skipped job as a SATISFIED check.
    assert!(
        !ddc_job_has_conditional(&ci),
        "the `interp-ddc` job carries a job-level `if:` or `continue-on-error:`. A skipped job \
         reports as a satisfied check, so claim 40's proof would stop running on pull requests \
         with every in-repo check still green."
    );
    assert!(
        ddc_job_has_conditional(
            "\n  interp-ddc:\n    runs-on: x\n    if: github.event_name == 'push'\n  other:\n"
        ),
        "anti-stub: the conditional detector must SEE a job-level if:"
    );
    assert!(
        !ddc_job_has_conditional("\n  interp-ddc:\n    runs-on: x\n    steps:\n      - run: y\n"),
        "anti-stub: the conditional detector must not invent one"
    );
    // …and the test it protects must exist, un-ignored, in that gated target.
    let gated = std::fs::read_to_string(
        repo.join("crates")
            .join("sigil-runtime")
            .join("tests")
            .join("interp_ddc.rs"),
    )
    .expect("the gated DDC test target is committed");
    assert!(
        gated.contains("fn interp_ddc_reproduces_the_committed_seed"),
        "the gated target no longer defines the DDC test"
    );
    // Match an ATTRIBUTE, not the text: this file's own doc comment discusses `#[ignore]`, and a
    // raw substring scan reads that as the attribute being present. Same trap the repo's
    // `#[test]`-name extractor was hardened against (a `fn` inside a string literal).
    //
    // `#[cfg…]` is checked for a reason the ledger's machinery structurally CANNOT see: a
    // `#[cfg(any())]` above the `#[test]` compiles the test OUT. The name still resolves for
    // `pin6_every_claim_names_a_real_test` (a source scan with no notion of cfg), the `#[ignore`
    // filter misses it, the lane runs `0 tests` and exits 0 — claim 40 backed by nothing, all
    // green. `#[cfg_attr(…, ignore)]` evades the ignore fence the same way.
    let disabling: Vec<&str> = gated
        .lines()
        .map(str::trim_start)
        .filter(|l| l.starts_with("#[ignore") || l.starts_with("#[cfg"))
        .collect();
    assert!(
        disabling.is_empty(),
        "the gated DDC test carries an attribute that can disable it: {disabling:?}. `#[ignore]` \
         skips it; `#[cfg(…)]` compiles it out and the lane then runs zero tests while every \
         name-based check stays green"
    );
}

/// LOW-3 from the sweep: `interp/certified.py` carries a hand-copied duplicate of the source
/// digest. Both sides are fail-closed if it drifts, but "the same pin the Rust side carries" was
/// an unverified human invariant. Now it is machine-checked.
#[test]
fn interp_certified_digest_matches_the_rust_pin() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("sigil-runtime lives under crates/");
    let py = std::fs::read_to_string(repo.join("interp").join("certified.py"))
        .expect("interp/certified.py is committed");
    let rs = include_str!("pipeline_differential.rs");

    let pin_from = |src: &str, needle: &str| -> String {
        let i = src
            .find(needle)
            .unwrap_or_else(|| panic!("{needle} not found"));
        let rest = &src[i + needle.len()..];
        let start = rest.find('"').expect("digest literal opens") + 1;
        let end = rest[start..].find('"').expect("digest literal closes") + start;
        rest[start..end].to_string()
    };
    let py_digest = pin_from(&py, "PIN_WITH_DRIVER_SRC_SHA256 = ");
    let rs_digest = pin_from(rs, "PIN_WITH_DRIVER_SRC_SHA256: &str =");
    assert_eq!(
        py_digest.len(),
        64,
        "anti-stub: the extracted Python digest is not a sha256: {py_digest:?}"
    );
    assert_eq!(
        py_digest, rs_digest,
        "interp/certified.py's pinned source digest disagrees with pipeline_differential.rs"
    );
}

/// SC-P4: the golden is only evidence if it carries real, distinguishing content. A key of empty
/// strings would satisfy the equality above while grading nothing.
#[test]
fn interp_golden_is_not_vacuous() {
    assert!(
        CORPUS.len() >= 15,
        "the interpreter corpus shrank below its floor ({} fixtures)",
        CORPUS.len()
    );
    let mut seen = std::collections::BTreeSet::new();
    for (name, src) in CORPUS {
        assert!(seen.insert(*name), "duplicate fixture name {name}");
        let enc = encode_tokens(src);
        assert!(
            enc.contains('|'),
            "fixture `{name}` produced no records|pool separator: {enc:?}"
        );
        if !src.is_empty() {
            assert!(
                enc.contains(','),
                "fixture `{name}` produced no token records: {enc:?}"
            );
            let parsed = encode_parse(src);
            assert!(
                !parsed.is_empty(),
                "fixture `{name}` produced an EMPTY parse encoding — the parse half would grade \
                 nothing"
            );
        }
    }
    // The escaper must survive the characters the fixtures actually contain.
    assert_eq!(json_escape("a\"b\\c\nd\te"), "a\\\"b\\\\c\\nd\\te");
}
