//! PIN-6 — the Claims Ledger is machine-checked.
//!
//! WHY THIS TEST EXISTS. `docs/CLAIMS.md` is the single authoritative statement of what SIGIL
//! proves. A prose ledger is exactly the artifact that drifts: Phase-0 of this epic measured the
//! documented capstone sizes as **9.6 KB stale**, and a prose table listed constructs as "fenced"
//! that measurement showed were byte-EQUAL. Writing a *better* prose ledger would repeat the
//! mistake. So the ledger carries machine-checkable tags and this test enforces them:
//!
//! * `@test:<fn>` — this claim is proven by that test. The test MUST exist in the repo.
//! * `@thm:<Name>` — this claim is proven by that Lean theorem. The name MUST be in the census.
//! * the unproven marker — this claim has NO executable proof. Allowed, but COUNTED and pinned,
//!   so adding one is a deliberate act rather than a quiet erosion.
//! * a fenced `pins` block of `NAME = VALUE` lines, each cross-checked against the Rust constant
//!   of the same name. A doc number that disagrees with code is a FAILURE, not a footnote.
//!
//! The extractors live in `support/ledger.rs` because the research overlay's ledger
//! (`proofs/lean-research/CLAIMS.md`, checked by `research_claims_ledger.rs`) is read by the same
//! code. SC-P4 (no assertion of absence without an anti-stub) applies to them: a regex that
//! silently matches nothing would make every assertion below vacuous, so they are proven
//! non-vacuous first, here.

use std::collections::HashSet;

#[path = "support/ledger.rs"]
mod ledger;
#[path = "support/repo_test_inventory.rs"]
mod repo_test_inventory;
#[path = "support/test_source.rs"]
mod test_source;
use ledger::{
    ledger_claim_numbers, ledger_pins, ledger_test_tags, ledger_thm_tags, rust_const_value,
};
use repo_test_inventory::{all_ignored_test_fn_names, all_test_fn_names};
use test_source::{ignored_test_fn_names_in, test_fn_names_in};

const LEDGER: &str = include_str!("../../../docs/CLAIMS.md");
/// The Lean theorem census. This is the gated authority on what is proved on the Lean side: the
/// axiom gate gives it an environment-derived census, and `soundness_contract.rs` requires it to
/// equal the complete source-derived theorem set. A claim citing a name absent from here is
/// citing a theorem that does not exist, was renamed, or was deleted.
const LEAN_MANIFEST: &str = include_str!("../../../proofs/lean/axiom-targets.txt");

/// SC-P4 anti-stub. Every assertion below is of the form "everything extracted is consistent" —
/// which passes trivially if the extractors extract NOTHING. Prove they distinguish present from
/// absent before trusting a single one of them.
#[test]
fn pin6_extractors_are_not_vacuous() {
    assert_eq!(
        ledger_test_tags("proven @test:foo_bar and @test:baz."),
        vec!["foo_bar", "baz"],
        "the @test: extractor must find tags and stop at punctuation"
    );
    assert!(
        ledger_test_tags("no tags here at all").is_empty(),
        "the @test: extractor must not invent tags"
    );

    assert_eq!(
        ledger_thm_tags("proved by @thm:Chk.sound and @thm:Chk.effect_safety_declared."),
        vec!["Chk.sound", "Chk.effect_safety_declared"],
        "the @thm: extractor must keep dotted names and drop a sentence-final full stop"
    );
    assert!(
        ledger_thm_tags("no theorem tags here").is_empty(),
        "the @thm: extractor must not invent tags"
    );
    assert!(
        ledger_thm_tags("@thm:").is_empty(),
        "an empty @thm: tag must not become a zero-length name that matches nothing"
    );

    let pins = ledger_pins("text\n```pins\nA_B = 1_234\nC = 7\n```\nmore");
    assert_eq!(
        pins.get("A_B"),
        Some(&1234),
        "pins block must parse underscores"
    );
    assert_eq!(pins.get("C"), Some(&7));
    assert!(
        ledger_pins("no fenced pins block").is_empty(),
        "the pins extractor must not invent pins"
    );

    assert_eq!(
        ledger_claim_numbers("## §B\n\n1. **One.**\n2. **Two.**\n\n---\n"),
        vec![1, 2]
    );
    assert!(ledger_claim_numbers("no claims section").is_empty());

    assert_eq!(
        rust_const_value("const FOO: usize = 483_753;", "FOO"),
        Some(483753),
        "the Rust-constant reader must parse an underscored literal"
    );
    assert_eq!(rust_const_value("const FOO: usize = 1;", "BAR"), None);

    // TASK #254 anti-stub: the test-name extractor must require `#[test]` and must NOT be fooled by
    // a `fn` inside a string literal (the raw-substring scan it replaced would have been).
    assert_eq!(
        test_fn_names_in("#[test]\nfn real_one() {}"),
        HashSet::from(["real_one".to_string()]),
        "a #[test] fn must be captured"
    );
    assert_eq!(
        test_fn_names_in("#[test]\n// a doc line\n#[ignore]\nfn tolerant() {}"),
        HashSet::from(["tolerant".to_string()]),
        "must tolerate comments/attributes between #[test] and fn"
    );
    assert!(
        test_fn_names_in("let s = \"module m;\\nfn f(a: i64, b: i64) -> i64\";").is_empty(),
        "a `fn` inside a string literal has no #[test] and must NOT be captured (the old bug)"
    );
    assert!(
        test_fn_names_in("fn helper() {}").is_empty(),
        "a non-#[test] fn must not be captured"
    );

    // The repo walker must find real tests — if it returned an empty set, every @test: tag would be
    // "missing" and the tag test would fail loudly rather than vacuously pass; but prove it works.
    let fns = all_test_fn_names();
    assert!(
        fns.contains("pin6_extractors_are_not_vacuous"),
        "the repo test walker must find this very test (found {} tests)",
        fns.len()
    );
}

#[test]
fn pin6_claim_numbers_are_unique_and_sequential() {
    let numbers = ledger_claim_numbers(LEDGER);
    let expected: Vec<usize> = (1..=numbers.len()).collect();

    assert_eq!(
        numbers, expected,
        "PIN-6: docs/CLAIMS.md claim numbers must be unique and sequential"
    );
}

/// PIN-6: every claim in the ledger that says it is proven MUST name a test that exists.
#[test]
fn pin6_every_claim_names_a_real_test() {
    let tags = ledger_test_tags(LEDGER);

    // Anti-vacuity floor: the ledger must actually carry proof tags. A ledger stripped of its
    // tags would otherwise pass this test while claiming everything and proving nothing.
    // RATCHET. Raised 46 → 61 on 2026-08-01: the floor had fallen 15 tags behind the ledger, so a
    // quarter of the proof tags could have been deleted with this test still green. Re-measure and
    // raise whenever claims are added; lowering it means a claim lost its proof and must move to §D.
    // Measure with THIS extractor, not a hand grep: a raw `@test:` count reads 62 because the
    // documentation table's `@test:<fn>` example has no identifier after the colon.
    const PIN6_TEST_TAG_FLOOR: usize = 67;
    assert!(
        tags.len() >= PIN6_TEST_TAG_FLOOR,
        "PIN-6: docs/CLAIMS.md carries only {} `@test:` tags (floor {PIN6_TEST_TAG_FLOOR}). \
         The ledger's whole purpose is that every claim names its proof — if tags were removed, \
         the ledger became prose again.",
        tags.len()
    );

    let fns = all_test_fn_names();
    let missing: Vec<&String> = tags.iter().filter(|t| !fns.contains(*t)).collect();
    assert!(
        missing.is_empty(),
        "PIN-6: docs/CLAIMS.md claims to be proven by tests that DO NOT EXIST: {missing:?}. \
         Either the test was renamed/deleted (the claim is now unproven — mark it @unproven and \
         bump the unproven pin) or the ledger has a typo. A claim pointing at a nonexistent test \
         is exactly the drift this ledger exists to prevent."
    );
}

/// PIN-6: every claim citing a Lean theorem MUST name one the axiom gate actually covers.
///
/// `@test:` couples a claim to a Rust test. Nothing coupled a claim to the *Lean* side, so the
/// formal-proof rows were ordinary prose and drifted like ordinary prose: claim 26 described the
/// manifest with an entry count that was long stale. A stale adjective is survivable; a claim
/// naming a theorem that no longer exists is not, because the reader cannot tell the difference
/// without reading Lean.
///
/// `axiom-targets.txt` is the right authority to check against rather than the Lean sources: the
/// gate derives a census from Lean's *elaborated environment* and requires it to equal this file,
/// and `soundness_contract.rs` independently requires this file to equal the complete
/// source-derived theorem set. So membership here means the named theorem exists, is public, is
/// inside the root import closure, and was audited against the three-axiom allowlist.
#[test]
fn pin6_every_lean_claim_names_a_censused_theorem() {
    let censused: HashSet<&str> = LEAN_MANIFEST.lines().map(str::trim).collect();
    // The manifest is the whole point of this check, so prove it was actually read rather than
    // arriving empty and turning every membership test below into a failure for the wrong reason.
    assert!(
        censused.len() > 1000,
        "PIN-6: the Lean manifest read as {} entries — it did not load",
        censused.len()
    );

    // Anti-vacuity floor: the ledger must actually cite Lean results by name.
    const PIN6_THM_TAG_FLOOR: usize = 5;
    let tags = ledger_thm_tags(LEDGER);
    assert!(
        tags.len() >= PIN6_THM_TAG_FLOOR,
        "PIN-6: docs/CLAIMS.md carries only {} `@thm:` tags (floor {PIN6_THM_TAG_FLOOR}). \
         Claims that name a Lean result must each name the theorem that proves them.",
        tags.len()
    );

    let missing: Vec<&String> = tags
        .iter()
        .filter(|t| !censused.contains(t.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "PIN-6: docs/CLAIMS.md cites Lean theorems that are NOT in the axiom-target census: \
         {missing:?}. Either the theorem was renamed or deleted (the claim is now unproven — \
         mark it @unproven), or the tag names a theorem that never existed. Names are \
         manifest-relative, so `Chk.sound`, never `LambdaSigil.Chk.sound`."
    );
}

/// PIN-6: a claim may not be "proven" by a test that never RUNS. `pin6_every_claim_names_a_real_test`
/// checks only that the name resolves, and the name extractor deliberately tolerates `#[ignore]`
/// (it must, or an attribute between `#[test]` and `fn` would hide a real test). That leaves one
/// quiet way to unprove a claim while every check stays green: add `#[ignore]` to the test it
/// names. `cargo test` then exits 0 without running it, the tag still resolves, and the ledger goes
/// on asserting a property nothing measures. This test closes that door by name.
#[test]
fn pin6_no_claim_is_proven_by_an_ignored_test() {
    let ignored = all_ignored_test_fn_names();

    // SC-P4 anti-stub: an empty `ignored` set would make the assertion below vacuous. The repo
    // deliberately contains at least one ignored test (the seed succession ritual), and the
    // extractor must distinguish ignored from running.
    assert_eq!(
        ignored_test_fn_names_in("#[test]\n#[ignore = \"why\"]\nfn skipped() {}"),
        HashSet::from(["skipped".to_string()]),
        "anti-stub: an #[ignore]d test must be recognized as ignored"
    );
    assert!(
        ignored_test_fn_names_in("#[test]\nfn runs() {}").is_empty(),
        "anti-stub: a running test must NOT be reported as ignored"
    );
    // …and this is exactly WHY the fence is needed: the existence extractor deliberately INCLUDES
    // ignored tests (`pin6_extractors_are_not_vacuous` pins that tolerance), so a name check alone
    // can never notice that a claim's proof stopped running.
    assert_eq!(
        test_fn_names_in("#[test]\n#[ignore]\nfn skipped() {}"),
        HashSet::from(["skipped".to_string()]),
        "the existence extractor must still find an ignored test by name"
    );
    assert!(
        !ignored.is_empty(),
        "anti-stub: the repo walker found NO ignored tests, so this fence would pass vacuously"
    );

    let proven_by_ignored: Vec<String> = ledger_test_tags(LEDGER)
        .into_iter()
        .filter(|t| ignored.contains(t))
        .collect();
    assert!(
        proven_by_ignored.is_empty(),
        "PIN-6: docs/CLAIMS.md claims to be proven by tests that are #[ignore]d and therefore \
         never run: {proven_by_ignored:?}. An ignored test proves nothing. Either un-ignore it, \
         or move the claim to §D and bump the unproven pin with a stated reason."
    );
}

/// The numbers §B prose is allowed to state without a pin, each with its reason. Kept tiny on
/// purpose: every entry is a number no assertion owns, which is the condition this ledger exists
/// to make rare and deliberate.
const PROSE_NUMBER_ALLOWLIST: &[(&str, &str)] = &[
    ("254", "a task id (`task #254`), not a measurement"),
    ("256", "part of `SHA-256`"),
    (
        "422",
        "the poison-census ratchet's starting point — §D declares this history unproven",
    ),
];

/// Strip the numbers that are STRUCTURE rather than measurement: ordered-list markers (`26. `)
/// and cross-references (`claim 34`, `claims 36–37`, `§B`). What remains is prose stating a
/// figure, which is what must be pinned.
///
/// KNOWN LIMITATION, stated rather than papered over: this sees ASCII DIGITS only, so a count
/// spelled as an English word ("Fifteen fixtures") evades it. Extending it to number-words was
/// considered and rejected — the ledger legitimately uses small spelled numbers structurally
/// ("seven gates", "three clauses", "two compatibility aliases"), so the check would be mostly
/// allowlist and its failures would stop being informative. The discipline that covers the gap is
/// editorial: a countable artifact's size belongs in the pins block whichever way it is spelled.
fn prose_measurement_numbers(section: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in section.lines() {
        // Drop the list marker: a line that begins a claim starts with `N. `.
        let body = match line.split_once(". ") {
            Some((n, rest)) if n.trim().chars().all(|c| c.is_ascii_digit()) && !n.is_empty() => {
                rest
            }
            _ => line,
        };
        let bytes: Vec<char> = body.chars().collect();
        let mut i = 0;
        while i < bytes.len() {
            if !bytes[i].is_ascii_digit() {
                i += 1;
                continue;
            }
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let num: String = bytes[start..i].iter().collect();
            if num.len() < 2 {
                continue;
            }
            // A cross-reference: the nearest preceding word is `claim`/`claims`, or the number is
            // part of a run like `36–37` / `36-37` whose head was already classified.
            let before: String = bytes[..start].iter().collect();
            // The preceding word, with leading brackets stripped — `(claim` must read as `claim`.
            let prev_word = before
                .trim_end()
                .rsplit(' ')
                .next()
                .unwrap_or("")
                .trim_start_matches(['(', '[', '*'])
                .to_ascii_lowercase();
            let prev_char = bytes[..start].last().copied().unwrap_or(' ');
            let is_ref = prev_word.starts_with("claim")
                || before.ends_with('–')
                || before.ends_with('-')
                || before.ends_with('§')
                // Inside an identifier: a diagnostic code (`T041`, `O001`, `SH_…`), never a figure.
                || prev_char.is_ascii_alphabetic()
                || prev_char == '_'
                // A PR or issue reference (`#682`).
                || prev_char == '#';
            // A year, or a date fragment like `2026-08-01`.
            let is_date = num.len() == 4 && num.starts_with("20");
            if !is_ref && !is_date {
                out.push(num);
            }
        }
    }
    out
}

/// PIN-6: a MEASUREMENT stated in §B prose must be a pinned number. This is the failure the whole
/// file was written to prevent, and it happened INSIDE the file: claim 26 said a manifest had 103
/// entries where the code asserted 160, and claim 29 said a 65-code backlog where the code
/// asserted 64. Neither number was in the `pins` block, so `pin6_ledger_numbers_match_the_code` —
/// which only checks doc→code for numbers already listed there — structurally could not see them.
/// Claims now cite pins by NAME; a bare figure must be pinned or explicitly allowlisted.
#[test]
fn pin6_section_b_prose_states_no_unpinned_measurement() {
    let start = LEDGER.find("## §B").expect("§B exists");
    let end = LEDGER.find("## §C").expect("§C exists");
    let section = &LEDGER[start..end];

    // SC-P4 anti-stub: the classifier must keep measurements and drop structure. Prove both.
    assert_eq!(
        prose_measurement_numbers(
            "26. **A committed 103-entry manifest** (claim 34, claims 36–37)"
        ),
        vec!["103"],
        "anti-stub: a bare measurement must survive while the list marker and cross-references drop"
    );
    assert!(
        prose_measurement_numbers("5. **See claims 36–37 and claim 12.**").is_empty(),
        "anti-stub: cross-references are not measurements"
    );
    assert!(
        prose_measurement_numbers("1. **Measured 2026-08-01.**").is_empty(),
        "anti-stub: dates are not measurements"
    );
    assert!(
        prose_measurement_numbers("9. **Codes T041, O001, N007 and PR #682.**").is_empty(),
        "anti-stub: diagnostic codes and PR references are not measurements"
    );

    let pinned: HashSet<u64> = ledger_pins(LEDGER).into_values().collect();
    let allowed: HashSet<&str> = PROSE_NUMBER_ALLOWLIST.iter().map(|(n, _)| *n).collect();
    let unpinned: Vec<String> = prose_measurement_numbers(section)
        .into_iter()
        .filter(|n| {
            !allowed.contains(n.as_str()) && !n.parse::<u64>().is_ok_and(|v| pinned.contains(&v))
        })
        .collect();
    assert!(
        unpinned.is_empty(),
        "PIN-6: §B prose states {unpinned:?} — figures no assertion owns. That is exactly how \
         claims 26 and 29 went stale. Put the measurement in the ```pins block with an owning \
         Rust constant and cite it by NAME, or add it to PROSE_NUMBER_ALLOWLIST with a reason."
    );
}

/// PIN-6: claims with no executable proof are ALLOWED but COUNTED. Growing the count is a
/// deliberate act with a reason, never an accident.
#[test]
fn pin6_unproven_claim_count_is_pinned() {
    // This is a floor from the current deduplicated audit. New findings should
    // raise it; closing a row with executable proof should lower it.
    const PIN6_UNPROVEN_CLAIMS: usize = 4;
    let n = LEDGER.matches("@unproven").count();
    assert_eq!(
        n, PIN6_UNPROVEN_CLAIMS,
        "PIN-6: the number of claims with NO executable proof moved ({n} vs pinned \
         {PIN6_UNPROVEN_CLAIMS}). Going UP means EITHER a new unbacked claim entered the ledger OR \
         a fresh audit found gaps the last one missed — the second is a win and should be said so \
         in the commit message. Going DOWN should mean a row was CLOSED by a test; going down \
         because a row was quietly deleted is exactly the failure this pin exists to catch."
    );
}

/// PIN-6: every number the ledger states MUST equal the constant the code asserts. This is the
/// direct fix for the drift that motivated the epic — documented sizes that no assertion contained.
#[test]
fn pin6_ledger_numbers_match_the_code() {
    let pins = ledger_pins(LEDGER);

    const PIN6_PIN_FLOOR: usize = 5;
    assert!(
        pins.len() >= PIN6_PIN_FLOOR,
        "PIN-6: the ledger's ```pins block carries only {} entries (floor {PIN6_PIN_FLOOR}) — \
         the numeric claims were removed or the block was renamed",
        pins.len()
    );

    // The sources that own these constants. `soundness_contract.rs` was ADDED after claims 26 and
    // 29 were found stale (a 103 against an asserted 160, a 65 against an asserted 64): their
    // numbers lived in a file this list did not read, so the ledger's own cross-check structurally
    // could not see them.
    let sources = [
        include_str!("pipeline_differential.rs"),
        include_str!("preserve_pins.rs"),
        include_str!("monomorph_differential.rs"),
        include_str!("soundness_contract.rs"),
    ];

    let mut unresolved = Vec::new();
    let mut mismatched = Vec::new();
    for (name, doc_value) in &pins {
        let found = sources.iter().find_map(|s| rust_const_value(s, name));
        match found {
            None => unresolved.push(name.clone()),
            Some(code_value) if code_value != *doc_value => {
                mismatched.push(format!(
                    "{name}: doc says {doc_value}, code says {code_value}"
                ));
            }
            Some(_) => {}
        }
    }

    assert!(
        unresolved.is_empty(),
        "PIN-6: the ledger pins constants that no longer exist in code: {unresolved:?}. \
         A number in the ledger with no owning assertion is undetectable drift — the exact \
         failure mode this epic was built to kill."
    );
    assert!(
        mismatched.is_empty(),
        "PIN-6: LEDGER/CODE DISAGREEMENT: {mismatched:?}. The code is the truth (SC-P1: pin the \
         MEASURED value, never the documented one). Update docs/CLAIMS.md to the measured value \
         and state in the commit message WHY the artifact changed (SC-P2)."
    );
}
