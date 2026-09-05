//! Integration tests for the structured (JSON) diagnostic wire format.
//!
//! Covers:
//! - Roundtrip: compile a known-bad source, serialize the resulting
//!   `CompileError` to JSON, assert key fields are present and well-typed.
//! - Shape stability: a snapshot of the JSON envelope shape that fails
//!   loudly if any field renames or schema bumps happen accidentally.

#![cfg(feature = "json")]

use serde_json::Value;
use sigil_compiler::certificate::{CERTIFICATE_SCHEMA_VERSION, CertificateJson, sha256_hex};
use sigil_compiler::diagnostics::json::{SCHEMA_VERSION, diagnostics_to_json, to_json};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileError, compile_named_module};

fn compile_bad(name: &str, source: &str) -> (CompileError, SourceFile) {
    let file = SourceFile::new(name, source);
    let err = compile_named_module(name, source).expect_err("source should fail to compile");
    (err, file)
}

#[test]
fn roundtrip_undefined_local() {
    let (err, source) = compile_bad(
        "undef.sigil",
        "module sigil; fn boot() -> bool { return ready; }",
    );
    let diagnostics = diagnostics_to_json(err.diagnostics(), &source);
    assert!(!diagnostics.is_empty(), "expected at least one diagnostic");

    let first = &diagnostics[0];
    // After Step 1 backfill, undefined-local errors carry T060 with full
    // structured metadata: title from the registry, hint with a fix recipe.
    assert_eq!(first.code, "T060");
    assert!(first.message.contains("undefined local"));
    assert_eq!(first.doc_url, "sigil://errors/T060");
    assert!(first.title.is_some(), "T060 has a registry title");
    assert!(first.hint.is_some(), "T060 has a registry-default hint");
    let location = first.location.as_ref().expect("expected location");
    assert_eq!(location.file, "undef.sigil");
    assert!(location.line >= 1);
    assert!(location.column >= 1);
}

#[test]
fn roundtrip_use_after_move() {
    let source = r#"
module sigil;
cap type Fuel { burn }
entry actor Main {
    state {}
    init(fuel: Fuel) {
        let a = spawn::<Worker>(fuel);
        let b = spawn::<Worker>(fuel);
    }
}
actor Worker {
    init(seed: Fuel) {}
}
"#;
    let (err, file) = compile_bad("uam.sigil", source);
    let diagnostics = diagnostics_to_json(err.diagnostics(), &file);
    assert!(!diagnostics.is_empty());

    let first = &diagnostics[0];
    // Use-after-move now carries O001 with the move-kind context inline.
    // The harness fixtures (tests/reject/use_after_move.sigil and
    // tests/attack/attack_01_use_after_move.sigil) now match on the code
    // `O001`, not on a message substring — see step 3 of the supremum loop.
    assert_eq!(first.code, "O001");
    // The variable name MUST appear (policy author needs to find the move).
    assert!(
        first.message.contains("`fuel`"),
        "expected the moved variable name in the message, got: {}",
        first.message,
    );
    // The move kind MUST appear (policy author needs to find the move site).
    assert!(
        first.message.contains("spawn"),
        "expected the move kind (`spawn`) in the message, got: {}",
        first.message,
    );
    // A recovery hint MUST be present (otherwise the uplift is cosmetic).
    assert!(
        first.hint.is_some() && !first.hint.as_ref().unwrap().is_empty(),
        "expected a non-empty recovery hint, got: {:?}",
        first.hint,
    );
}

#[test]
fn json_severity_serializes_lowercase() {
    let (err, file) = compile_bad("s.sigil", "module sigil; fn f() -> bool { return ready; }");
    let diag = &err.diagnostics()[0];
    let json = to_json(diag, &file);
    let value: Value = serde_json::to_value(&json).unwrap();
    assert_eq!(value["severity"], Value::String("error".to_owned()));
}

#[test]
fn schema_version_is_two() {
    // v2 (a2): adds optional `suggested_edits`. Bumping further requires explicit
    // consensus and an additive-compatibility plan. The CLI envelope's
    // SCHEMA_VERSION is pinned equal by a compile-time assert in json_envelope.rs.
    assert_eq!(SCHEMA_VERSION, 2);
}

#[test]
fn suggested_edits_present_for_close_undefined_local() {
    // `fule` is a 1-edit typo of the in-scope `fuel`, so T060 carries a
    // structured, byte-applicable fix.
    let src = "module sigil; fn boot() -> i64 { let fuel = 7; return fule; }";
    let (err, file) = compile_bad("edit.sigil", src);
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T060")
        .expect("expected a T060 undefined-local");
    let json = to_json(diag, &file);
    let edits = json
        .suggested_edits
        .as_ref()
        .expect("suggested_edits present for a close name");
    assert_eq!(edits.len(), 1, "a2 caps at one edit");
    assert_eq!(edits[0].replacement, "fuel");
    // The spanned bytes are exactly the typo being replaced (drop-in).
    assert_eq!(&src[edits[0].start..edits[0].end], "fule");
    // And it serializes under the v2 wire field.
    let value: Value = serde_json::to_value(&json).unwrap();
    assert_eq!(value["suggested_edits"][0]["replacement"], "fuel");
}

#[test]
fn suggested_edits_absent_when_no_close_name() {
    // No in-scope name is within edit distance of `ready`, so no edit is offered
    // and the optional field is omitted entirely from the wire.
    let (err, file) = compile_bad(
        "noedit.sigil",
        "module sigil; fn f() -> bool { return ready; }",
    );
    let diag = err
        .diagnostics()
        .iter()
        .find(|d| d.code().as_str() == "T060")
        .expect("expected a T060 undefined-local");
    let json = to_json(diag, &file);
    assert!(json.suggested_edits.is_none(), "no close name -> no edit");
    let value: Value = serde_json::to_value(&json).unwrap();
    assert!(
        value.get("suggested_edits").is_none(),
        "absent field must be omitted from the wire, not null"
    );
}

#[test]
fn json_shape_stability_snapshot() {
    // If any field name in the wire format changes, this catches it and
    // forces a deliberate decision.
    let (err, file) = compile_bad(
        "snap.sigil",
        "module sigil; fn f() -> bool { return ready; }",
    );
    let diag = &err.diagnostics()[0];
    let json = to_json(diag, &file);
    let value: Value = serde_json::to_value(&json).unwrap();
    let obj = value
        .as_object()
        .expect("diagnostic must serialize as an object");

    // Required fields (must always be present).
    for key in ["severity", "code", "message", "doc_url", "location"] {
        assert!(
            obj.contains_key(key),
            "expected wire field `{key}` in serialized diagnostic"
        );
    }
    // Title is required for registered codes (everything after Step 1 backfill).
    assert!(
        obj.contains_key("title"),
        "title must be present for registered codes after Step 1 backfill"
    );
    // Hint is required when the registry default is set (every entry has one).
    assert!(
        obj.contains_key("hint"),
        "hint must be present for registered codes (registry default)"
    );

    let location = obj["location"]
        .as_object()
        .expect("location must be an object");
    for key in ["file", "span", "line", "column"] {
        assert!(
            location.contains_key(key),
            "expected location subfield `{key}`"
        );
    }
    let span = location["span"]
        .as_object()
        .expect("span must be an object");
    for key in ["start", "end"] {
        assert!(span.contains_key(key), "expected span subfield `{key}`");
    }
}

/// Step 11 (axis 5): the verification certificate emitted alongside
/// successful compilation gives external tools enough information to
/// trust a Sigil program WITHOUT re-running the compiler.
///
/// This test locks the contract: required top-level fields are present
/// and well-typed; the source fingerprint is deterministic (same source
/// → same hash); the compiler version is non-empty; the schema version
/// matches the constant (forward-compat contract — bumping requires
/// updating downstream consumers). This is the load-bearing test that
/// makes the certificate a real backend (per the axes-1/3/5 prompt's
/// rule 3) rather than decoration on the existing JSON envelope.
#[test]
fn verification_certificate_has_stable_shape() {
    let source = r#"
module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 1; }
}
"#;
    let compilation = compile_named_module("cert.sigil", source).expect("compiles cleanly");
    let cert = CertificateJson::new(
        compilation.source_name.clone(),
        source,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    );

    // Schema version matches the public constant.
    assert_eq!(cert.schema_version, CERTIFICATE_SCHEMA_VERSION);
    // Compiler version is non-empty (CARGO_PKG_VERSION must be set).
    assert!(
        !cert.compiler_version.is_empty(),
        "compiler_version must come from CARGO_PKG_VERSION"
    );
    // Source fingerprint algorithm stays SHA-256 (locked since v3 for
    // collision-resistance). Wall 5 Step 1 / v7 changes the INPUT to
    // SHA-256 from raw source bytes to the framed concatenation
    // `\x00 + name + \x00 + text`. The framing applies uniformly to
    // single-file (N=1) and multi-file inputs — single-file fingerprints
    // therefore differ between v6 and v7 even for byte-identical source.
    assert_eq!(cert.source_fingerprint.algorithm, "sha2-256");
    // The fingerprint records the framed buffer length, not the raw
    // source length. Framing adds 2 NUL bytes + name length per source.
    let framed_len = 2 + compilation.source_name.len() + source.len();
    assert_eq!(cert.source_fingerprint.bytes, framed_len as u64);
    // Hash equals SHA-256 of the framed buffer, not raw source.
    let mut framed = Vec::with_capacity(framed_len);
    framed.push(0u8);
    framed.extend_from_slice(compilation.source_name.as_bytes());
    framed.push(0u8);
    framed.extend_from_slice(source.as_bytes());
    assert_eq!(
        cert.source_fingerprint.hash,
        sha256_hex(&framed),
        "fingerprint hash must match the v7 framed-concat sha256"
    );
    // Schema v3: wasm_inner fingerprint binds the cert to the
    // emitted artifact, also via SHA-256.
    assert_eq!(cert.wasm_inner_fingerprint.algorithm, "sha2-256");
    assert_eq!(
        cert.wasm_inner_fingerprint.bytes,
        compilation.wasm_inner.len() as u64
    );
    assert_eq!(
        cert.wasm_inner_fingerprint.hash,
        sha256_hex(&compilation.wasm_inner),
        "wasm_inner fingerprint must be deterministic and match raw sha256_hex"
    );
    // Reports are populated.
    assert!(cert.capability.verified_functions > 0);
    assert!(cert.ownership.verified_functions > 0);

    // Round-trip through JSON is lossless for the fields we care about.
    let json = serde_json::to_value(&cert).expect("certificate serializes");
    assert_eq!(json["schema_version"], CERTIFICATE_SCHEMA_VERSION);
    assert_eq!(json["source_fingerprint"]["algorithm"], "sha2-256");
    assert!(json["capability"]["verified_functions"].is_u64());
    assert!(json["ownership"]["verified_functions"].is_u64());
}

/// Step 11: two compilations of the same source produce certificates
/// with the same fingerprint hash. Catches non-determinism (e.g. if
/// fingerprinting accidentally incorporates a timestamp or process-
/// random seed).
#[test]
fn verification_certificate_is_deterministic() {
    let source = "module sigil;\ncap type Fuel {}\nentry actor Main { state { fuel: Fuel } on Start() -> i64 { return 1; } }\n";
    let c1 = compile_named_module("det.sigil", source).expect("compiles");
    let c2 = compile_named_module("det.sigil", source).expect("compiles");
    let cert1 = CertificateJson::new(
        c1.source_name.clone(),
        source,
        &c1.wasm_inner,
        c1.wasm_outer.as_deref(),
        c1.primary_module_name().map(str::to_owned),
        c1.module_names.clone(),
        &c1.capability_report,
        &c1.ownership_report,
        &c1.formal_security_report,
        c1.effects_required.clone(),
    );
    let cert2 = CertificateJson::new(
        c2.source_name.clone(),
        source,
        &c2.wasm_inner,
        c2.wasm_outer.as_deref(),
        c2.primary_module_name().map(str::to_owned),
        c2.module_names.clone(),
        &c2.capability_report,
        &c2.ownership_report,
        &c2.formal_security_report,
        c2.effects_required.clone(),
    );
    assert_eq!(cert1.source_fingerprint.hash, cert2.source_fingerprint.hash);
    assert_eq!(
        cert1.source_fingerprint.bytes,
        cert2.source_fingerprint.bytes
    );
    // Step 13: deterministic effects_required is part of the certificate
    // determinism contract — same source compiles to same effect surface.
    assert_eq!(cert1.effects_required, cert2.effects_required);
    // Step 22 (schema v2): WASM-byte fingerprint determinism. Same
    // source must produce byte-identical WASM, so the wasm_inner
    // fingerprint must match across compilations.
    assert_eq!(
        cert1.wasm_inner_fingerprint.hash,
        cert2.wasm_inner_fingerprint.hash
    );
}

/// Step 13 (axis 5): the certificate exposes the union of effects
/// required across all functions, sorted and deduplicated. External
/// policy authorities consuming the certificate can decide whether
/// the program's effect surface is acceptable. This test compiles a
/// program declaring `effect NetIO` + a function requiring it, then
/// asserts the certificate names it.
#[test]
fn verification_certificate_lists_required_effects() {
    let source = r#"
#[ring(outer)]
module ext;

effect NetIO;

fn do_io() -> i64 ! { NetIO } { return 42; }
"#;
    let compilation = compile_named_module("eff.sigil", source).expect("compiles");
    let cert = CertificateJson::new(
        compilation.source_name.clone(),
        source,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    );
    assert!(
        cert.effects_required.iter().any(|e| e == "NetIO"),
        "expected `NetIO` in effects_required, got: {:?}",
        cert.effects_required
    );
    // Sorted: if multiple effects are present, the list is sorted.
    let mut sorted = cert.effects_required.clone();
    sorted.sort();
    assert_eq!(
        cert.effects_required, sorted,
        "effects_required must be sorted for deterministic output"
    );
}

/// Step 13: a program with no effect declarations / annotations
/// produces an empty effects_required list. Empty is a valid effect
/// surface and the certificate should serialize it as such.
#[test]
fn verification_certificate_empty_effects_is_empty_list() {
    let source = "module sigil;\ncap type Fuel {}\nentry actor Main { state { fuel: Fuel } on Start() -> i64 { return 1; } }\n";
    let compilation = compile_named_module("noeff.sigil", source).expect("compiles");
    let cert = CertificateJson::new(
        compilation.source_name.clone(),
        source,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    );
    assert!(
        cert.effects_required.is_empty(),
        "expected empty effects_required for a no-effect program, got: {:?}",
        cert.effects_required
    );
}

#[test]
fn ring_violation_has_full_structured_metadata() {
    // R001 (outer ring cannot own capabilities) — verifies the full
    // structured shape an LLM agent will consume in the AutoForge loop.
    let (err, source) = compile_bad(
        "ring.sigil",
        "#[ring(outer)] module ext; cap type Token {} fn bad(t: Token) -> i64 { return 0; }",
    );
    let diagnostics = diagnostics_to_json(err.diagnostics(), &source);
    assert!(!diagnostics.is_empty());

    let first = &diagnostics[0];
    assert_eq!(first.code, "R001");
    assert_eq!(first.title, Some("Outer-ring code cannot own capabilities"));
    assert_eq!(first.doc_url, "sigil://errors/R001");
    assert!(
        first.message.contains("outer ring cannot own capabilities"),
        "expected harness substring preserved"
    );
    assert!(
        first.hint.as_ref().is_some_and(|h| h.contains("grant")),
        "registry hint should suggest using grant"
    );
}

// =====================================================================
// Wall 4 Step 7 spec-compliance follow-up — cert v6 lock-in tests
// (NF-S7-AG-2 forward-AND-backward locked, NF-S7-12 byte-equality).
// =====================================================================

/// Lock `CERTIFICATE_SCHEMA_VERSION` at exact value 9. Schema v9 binds
/// the freshly re-derived `FormalSecurityReport` and canonical CSIR
/// fingerprint in addition to the v7 framed multi-source fingerprint.
/// Pre-v9 consumers fail-loud via `gate_cert`'s version check. Future bumps require
/// explicit test update (forward AND backward locked — both downgrade
/// and upgrade fail the assertion).
#[test]
fn certificate_schema_version_is_nine() {
    assert_eq!(CERTIFICATE_SCHEMA_VERSION, 9);
}

/// NF-S7-12 / Wall 5 Step 1: cert v7 JSON-shape lock-in test.
/// `CertificateJson` is a verification summary, not an AST dump.
/// Refinements are NOT serialized into the cert (corrected N28-S7).
/// Wall 5 Step 1's v6→v7 bump changes the `source_fingerprint`
/// computation (now framed-concat) but does NOT change the JSON
/// key set — the test still locks the same 11 documented keys.
///
/// If a future PR accidentally extends `CertificateJson` with
/// AST-level refinement data OR per-file fingerprint data (which
/// belongs to the 5.1b Merkle bump, not v7), this test fails with
/// the unexpected key, fail-loud per NF-S7-12.
#[test]
fn certificate_v7_carries_no_ast_refinement_data() {
    // Source exercises Wall 4 Step 1 refinement (record `where` clause)
    // — this is a known-good refined source from the z3_corpus. Step 7's
    // fn refinement isn't used here because the cert's JSON shape is
    // claimed to be source-shape-independent; any compiling source
    // produces the same set of cert JSON keys, so a Step 1 fixture is
    // sufficient to prove "no AST data in cert" (NF-S7-12).
    let source = r#"
module sigil;

record Index { value: i64 } where value > 0

entry actor Main {
    state { dummy: i64 }
    on Start() -> i64 {
        let idx: Index = Index { value: 5 };
        return 1;
    }
}
"#;
    let compilation = compile_named_module("cert_v6_shape.sigil", source)
        .expect("Step 1 refined source compiles cleanly");
    let cert = CertificateJson::new(
        compilation.source_name.clone(),
        source,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    );
    let json: Value = serde_json::to_value(&cert).expect("cert serializes");

    // The documented v6 cert JSON key-set. Verification summary only —
    // NO refinement-shaped keys (param_refinements, return_refinement,
    // refinement_clauses, etc.).
    let expected_keys = [
        "schema_version",
        "compiler_version",
        "source_name",
        "source_fingerprint",
        "wasm_inner_fingerprint",
        "wasm_outer_fingerprint",
        "primary_module",
        "module_names",
        "capability",
        "ownership",
        "formal",
        "effects_required",
    ];
    let json_obj = json.as_object().expect("cert JSON is an object");
    let actual_keys: std::collections::BTreeSet<&str> =
        json_obj.keys().map(|k| k.as_str()).collect();
    let expected_set: std::collections::BTreeSet<&str> = expected_keys.iter().copied().collect();

    // Catch new keys (cert leaked refinement data).
    let extra: Vec<&&str> = actual_keys.difference(&expected_set).collect();
    assert!(
        extra.is_empty(),
        "NF-S7-12: cert v6 carries unexpected key(s) {extra:?}; spec claims AST-data-free cert"
    );
    // Catch removed keys (the cert shape regressed).
    let missing: Vec<&&str> = expected_set.difference(&actual_keys).collect();
    assert!(
        missing.is_empty(),
        "NF-S7-12: cert v6 missing expected key(s) {missing:?}"
    );
    // Sanity check the schema version inside the JSON.
    assert_eq!(
        json["schema_version"], 9,
        "cert JSON's schema_version field must equal CERTIFICATE_SCHEMA_VERSION"
    );

    // v8: `solver_verified` lives in the nested `capability` object. v9 adds
    // the top-level combined formal report pinned in `expected_keys` above.
    // Pin the solver witness presence + that it reflects THIS build's feature
    // config — proving the witness rides in the cert. This test compiles
    // in BOTH CI lanes (the `rust` job, solver-off → false; the `solver`
    // job, solver-on → true), so each lane verifies its own truth
    // (a file-placement guarantee: see B1's note in z3_guard_fences).
    assert_eq!(
        json["capability"]["solver_verified"],
        serde_json::Value::Bool(cfg!(feature = "solver")),
        "cert's capability.solver_verified must equal this build's \
         `solver` feature flag — the v8 witness"
    );
}
