//! `sigil-corpus` — a compiler-validated training-corpus extractor for SIGIL.
//! See `docs/specs/training-corpus.md`. This crate library exposes the build
//! pipeline; `main.rs` is the thin CLI.
//!
//! The pipeline: each `Extractor` proposes `RawRecord`s; `certify` runs the §9
//! bounds + the validation gate, emitting a `Record` or charging a named drop
//! bucket; `build` reconciles `proposed == emitted + dropped` (ET-C6) and
//! asserts no validation-intent record slipped through unvalidated (ET-C1).

pub mod corpus_paths;
pub mod emit;
pub mod extract;
pub mod schema;
pub mod validate;

use std::collections::BTreeMap;

use extract::{ExtractCtx, Extractor, RawRecord, ValidationIntent};
use schema::{
    Kind, MAX_OUTPUT_BYTES, MAX_PROSE_BYTES, MAX_RECORDS, NegativeExample, Record, Validated,
    ValidationKind,
};

/// The committed Phase-1 extractor set. PR-2..4 append the others here.
pub fn extractors() -> Vec<Box<dyn Extractor>> {
    vec![
        Box::new(extract::error_corpus::ErrorCorpus),
        Box::new(extract::source_idiom::SourceIdiom),
        Box::new(extract::test_fixture::TestFixture),
        Box::new(extract::inline_program::InlineProgram),
        Box::new(extract::pr_history::PrHistory),
    ]
}

/// One dropped candidate, recorded for `rejects.log`.
pub struct Reject {
    pub id: String,
    pub extractor: String,
    pub reason: String,
}

/// Named drop buckets + the per-record reject log. The bucket name is the
/// reason's prefix before the first `:` (e.g. `OUTPUT_OVERSIZE`).
#[derive(Default)]
pub struct DropLedger {
    pub buckets: BTreeMap<String, usize>,
    pub rejects: Vec<Reject>,
}

impl DropLedger {
    fn bump(&mut self, extractor: &str, id: &str, reason: String) {
        let bucket = reason.split(':').next().unwrap_or("UNKNOWN").to_string();
        *self.buckets.entry(bucket).or_insert(0) += 1;
        self.rejects.push(Reject {
            id: id.to_string(),
            extractor: extractor.to_string(),
            reason,
        });
    }

    pub fn total(&self) -> usize {
        self.buckets.values().sum()
    }
}

/// The result of a build: emitted records (id-ordered) + the drop ledger + the
/// proposed count, with ET-C6/ET-C1 already asserted.
pub struct BuildResult {
    pub records: BTreeMap<String, Record>,
    pub ledger: DropLedger,
    pub proposed: usize,
}

/// Run every extractor through the gate and reconcile the ledger.
pub fn build(ctx: &ExtractCtx) -> anyhow::Result<BuildResult> {
    let mut records: BTreeMap<String, Record> = BTreeMap::new();
    let mut ledger = DropLedger::default();
    // Memoized compile verdict per validation unit (a stdlib file / the selfhost
    // trio), so each unit is compiled at most once across all its records.
    let mut unit_cache: BTreeMap<String, Result<(), String>> = BTreeMap::new();
    let mut proposed = 0usize;

    for ex in extractors() {
        for raw in ex.extract(ctx)? {
            proposed += 1;
            if let Some(rec) = certify(raw, &mut ledger, &mut unit_cache) {
                if records.len() >= MAX_RECORDS {
                    panic!("CORPUS_RECORD_CEILING: more than {MAX_RECORDS} records");
                }
                if let Some(prev) = records.insert(rec.id.clone(), rec) {
                    // Two records claiming one id is a pipeline bug — both
                    // cannot be emitted, and a silent overwrite would breach
                    // ET-C6's count identity.
                    panic!("CORPUS_DUPLICATE_ID: `{}`", prev.id);
                }
            }
        }
    }

    // ET-C6 — conservation identity.
    let emitted = records.len();
    let dropped = ledger.total();
    if proposed != emitted + dropped {
        panic!("CORPUS_SILENT_LOSS: proposed={proposed} emitted={emitted} dropped={dropped}");
    }
    // ET-C1 — no validation-intent record emitted unvalidated.
    let leaked = records
        .values()
        .filter(|r| {
            matches!(
                r.validated.how,
                ValidationKind::ParsedTypechecked | ValidationKind::ReproducedCode { .. }
            ) && !r.validated.ok
        })
        .count();
    if leaked != 0 {
        panic!("CORPUS_UNVALIDATED: {leaked} validated-intent records emitted with ok=false");
    }

    Ok(BuildResult {
        records,
        ledger,
        proposed,
    })
}

/// Apply the §9 field bounds + the validation gate to one candidate. Returns
/// `Some(record)` to emit, or `None` after charging a drop bucket. Bound
/// breaches that signal a pipeline bug (ungrounded prose, a secret) panic.
fn certify(
    raw: RawRecord,
    ledger: &mut DropLedger,
    unit_cache: &mut BTreeMap<String, Result<(), String>>,
) -> Option<Record> {
    let RawRecord {
        mut record,
        intent,
        name_for_compile,
        provenance,
    } = raw;

    // ET-C7 — per-record payload cap.
    if record.output.len() > MAX_OUTPUT_BYTES {
        ledger.bump(
            &record.extractor,
            &record.id,
            format!("OUTPUT_OVERSIZE:{}", record.output.len()),
        );
        return None;
    }

    // ET-C3 — prose bound + grounding (verbatim substring of provenance).
    let prose_fields: [(&str, Option<&String>); 2] = [
        ("intent", Some(&record.intent)),
        ("reasoning", record.reasoning.as_ref()),
    ];
    for (field, val) in prose_fields {
        let Some(text) = val.filter(|t| !t.is_empty()) else {
            continue;
        };
        if text.len() > MAX_PROSE_BYTES {
            ledger.bump(
                &record.extractor,
                &record.id,
                format!("PROSE_INVALID:{field}:oversize"),
            );
            return None;
        }
        if !provenance.contains(text.as_str()) {
            panic!("CORPUS_UNGROUNDED_FIELD: {}.{field}", record.id);
        }
    }

    // ET-C4 — secret / PII scan on every emitted string field.
    if let Some(pat) = scan_for_secret(&record) {
        panic!("CORPUS_SECRET_DETECTED: {} matched {pat}", record.id);
    }

    // The validation gate.
    let validated: Validated = match intent {
        ValidationIntent::Reference { reason } => Validated {
            ok: false,
            how: ValidationKind::Unvalidated { reason },
        },
        // Inline programs: the compiler verdict alone labels the record. Clean →
        // a validated positive; a reproduced registry code → a validated negative
        // carrying that code (ET-C2 — derived, never declared); anything else →
        // a counted drop. The extractor already proved it parses clean as SIGIL.
        ValidationIntent::Classify => {
            use validate::FixtureVerdict;
            match validate::classify_fixture(&name_for_compile, &record.output) {
                FixtureVerdict::Clean => Validated {
                    ok: true,
                    how: ValidationKind::ParsedTypechecked,
                },
                FixtureVerdict::Errored(codes) if !codes.is_empty() => {
                    let code = codes[0].clone();
                    record.kind = Kind::Rejection;
                    record.negative_examples = vec![NegativeExample {
                        code: code.clone(),
                        error: String::new(),
                        explanation: String::new(),
                    }];
                    Validated {
                        ok: true,
                        how: ValidationKind::ReproducedCode { code },
                    }
                }
                FixtureVerdict::Errored(_) => {
                    ledger.bump(
                        &record.extractor,
                        &record.id,
                        "NO_REGISTRY_CODE".to_string(),
                    );
                    return None;
                }
                FixtureVerdict::Timeout => {
                    ledger.bump(
                        &record.extractor,
                        &record.id,
                        "VALIDATE_TIMEOUT".to_string(),
                    );
                    return None;
                }
            }
        }
        ValidationIntent::Positive => {
            match validate::certify_positive(&name_for_compile, &record.output) {
                Ok(v) => v,
                Err(reason) => {
                    ledger.bump(&record.extractor, &record.id, reason);
                    return None;
                }
            }
        }
        ValidationIntent::Negative { code } => {
            match validate::certify_negative(&name_for_compile, &record.output, &code) {
                Ok(v) => v,
                Err(reason) => {
                    ledger.bump(&record.extractor, &record.id, reason);
                    return None;
                }
            }
        }
        ValidationIntent::PositiveUnit { unit_key, unit_src } => {
            let verdict = unit_cache
                .entry(unit_key.clone())
                .or_insert_with(|| validate::validate_unit(&unit_key, unit_src.as_str()))
                .clone();
            match verdict {
                Ok(()) => Validated {
                    ok: true,
                    how: ValidationKind::ParsedTypechecked,
                },
                Err(reason) => {
                    ledger.bump(&record.extractor, &record.id, reason);
                    return None;
                }
            }
        }
        ValidationIntent::Fixture { expect_error } => {
            use validate::FixtureVerdict;
            match (
                expect_error,
                validate::classify_fixture(&name_for_compile, &record.output),
            ) {
                // Expected-error fixture that reproduces a registry code → a
                // validated negative carrying the compiler's code (ET-C2).
                (true, FixtureVerdict::Errored(codes)) if !codes.is_empty() => {
                    let code = codes[0].clone();
                    record.kind = Kind::Rejection;
                    record.negative_examples = vec![NegativeExample {
                        code: code.clone(),
                        error: record.intent.clone(),
                        explanation: String::new(),
                    }];
                    Validated {
                        ok: true,
                        how: ValidationKind::ReproducedCode { code },
                    }
                }
                // Expected error but compiled clean (drift / solver-skipped), or
                // errored with no registry code → drop, never a guessed positive.
                (true, FixtureVerdict::Clean) => {
                    ledger.bump(
                        &record.extractor,
                        &record.id,
                        "EXPECTED_ERROR_BUT_CLEAN".to_string(),
                    );
                    return None;
                }
                (true, _) => {
                    ledger.bump(
                        &record.extractor,
                        &record.id,
                        "NO_REGISTRY_CODE".to_string(),
                    );
                    return None;
                }
                // Positive fixture: must compile clean.
                (false, FixtureVerdict::Clean) => Validated {
                    ok: true,
                    how: ValidationKind::ParsedTypechecked,
                },
                (false, FixtureVerdict::Errored(codes)) => {
                    ledger.bump(
                        &record.extractor,
                        &record.id,
                        format!("POSITIVE_DID_NOT_COMPILE:observed={}", codes.join("|")),
                    );
                    return None;
                }
                (false, FixtureVerdict::Timeout) => {
                    ledger.bump(
                        &record.extractor,
                        &record.id,
                        "VALIDATE_TIMEOUT".to_string(),
                    );
                    return None;
                }
            }
        }
    };
    record.validated = validated;
    Some(record)
}

/// Scan every user-facing string field of a record for a secret/PII pattern.
fn scan_for_secret(r: &Record) -> Option<&'static str> {
    let mut fields: Vec<&str> = vec![&r.intent, &r.output, &r.source_path];
    if let Some(reason) = &r.reasoning {
        fields.push(reason);
    }
    for t in &r.tags {
        fields.push(t);
    }
    for ne in &r.negative_examples {
        fields.push(&ne.error);
        fields.push(&ne.explanation);
    }
    for c in &r.context.constraints {
        fields.push(c);
    }
    fields.into_iter().find_map(validate::find_secret)
}
