//! WHY THIS TEST EXISTS. The v9 declaration codec must retain the actual v8
//! projection and complete host identities; decoding is not a security verdict.
//! Positive source-built fixtures and single-field mutants exercise both sides
//! of that boundary. The explicitly armed generator owns committed shared bytes.

use sigil_abi::host_contract::{
    HostContractProfile, HostOperationContract, HostValueContract, HostValueType,
    OccurrenceVisibility, SecurityLabel,
};
use sigil_compiler::diagnostics::{Severity, codes};
use sigil_compiler::registries::AuthorityRegistry;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileOptions, CompilerContext, air, compile_named_module, effect_check, effect_desugar,
    formal, formal_v9, name_resolution, parser, ring_check, taint_check, type_check,
};

const SOURCE: &str = r#"
#[ring(outer)] #[trusted]
module occurrence_declarations;
extern "C" fn tick(value: i64) -> i64 ! { FFI, Unsafe };
fn run(value: i64) -> i64 @Internal ! { FFI, Unsafe } { return tick(value); }
"#;

const ACTORS: &str = r#"
module actor_declarations;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>) -> i64 {
        worker.send(Ping());
        let child = spawn::<Worker>(fuel);
        let response = worker.ask(GetCount(), timeout: 5);
        return response;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Ping() {}
    on GetCount() -> i64 { return 1; }
}
"#;

fn profile(revision: u64) -> HostContractProfile {
    HostContractProfile::new(
        "v9-codec-test".into(),
        revision,
        vec![],
        vec![HostOperationContract {
            module: "ffi".into(),
            name: "tick".into(),
            occurrence: OccurrenceVisibility::Public,
            params: vec![HostValueContract {
                ty: HostValueType::I64,
                label: SecurityLabel::Public,
            }],
            results: vec![HostValueContract {
                ty: HostValueType::I64,
                label: SecurityLabel::Internal,
            }],
            domains: vec![],
        }],
    )
    .expect("the test profile's declared flows are valid")
}

fn project(source: &str, context: &CompilerContext) -> Vec<u8> {
    // Declaration codec fixtures must not obtain their bytes from a successful
    // production compilation: v9 policy is deliberately allowed to reject a
    // structurally valid declaration fixture. Reproduce the source/type/AIR
    // projection prefix explicitly, stopping before every authorizing verifier.
    let source = SourceFile::new("declarations.sigil", source);
    let (ast, parser_diagnostics) = parser::parse(&source);
    assert!(
        parser_diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity() != Severity::Error),
        "declaration fixture must parse: {parser_diagnostics:?}"
    );
    let resolved = name_resolution::resolve(&ast).expect("declaration fixture must resolve");
    let (mut typed, authority_registry, _) =
        type_check::check_with_warnings(&resolved, &CompileOptions::default())
            .expect("declaration fixture must type-check");
    ring_check::check_rings(&typed).expect("declaration fixture must satisfy ring policy");
    effect_check::check_effects(&typed).expect("declaration fixture must satisfy effect policy");
    taint_check::check_taints(&typed)
        .expect("declaration fixture must satisfy legacy taint policy");
    effect_desugar::desugar_effect_handlers(&mut typed);
    effect_check::check_effect_handlers_gated(&typed)
        .expect("declaration fixture must lower supported effect handlers");
    let raw = air::lower(&typed);
    // Fixtures have no named authority bits; Fuel's full mask is empty.
    assert_eq!(
        authority_registry.full_mask("Fuel"),
        0,
        "fixtures must not introduce named authority bits"
    );
    formal::project_v9_declarations(&typed, &raw, &authority_registry, context)
        .expect("source/AIR declarations must project without authorizing v9 execution")
}

fn record(bytes: &[u8], tag: u8) -> usize {
    12 + bytes[12..]
        .as_chunks::<32>()
        .0
        .iter()
        .position(|record| record[0] == tag)
        .expect("fixture must contain the requested record")
        * 32
}

fn set_word(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn cases() -> Vec<(String, bool, Vec<u8>)> {
    let legacy = project(SOURCE, &CompilerContext::default());
    let declared = project(SOURCE, &CompilerContext::with_host_profile(profile(1)));
    let actors = project(ACTORS, &CompilerContext::default());
    let empty = formal_v9::encode(b"CSIR\x08\0\0\0\0\0\0\0", None, &[], &[], &[])
        .expect("an empty declaration envelope is not a verifier approval");
    let mut cases = vec![
        ("empty-framing".into(), true, empty),
        ("legacy-unknown-ffi".into(), true, legacy.clone()),
        ("declared-ffi".into(), true, declared.clone()),
        ("actor-identities".into(), true, actors.clone()),
        // Both are valid declarations. The separate occurrence policy must
        // distinguish the repeated Public send from the pure private guard;
        // an `accept-` filename here never claims security acceptance.
        (
            "loop-header-send".into(),
            true,
            project(
                include_str!("../../../proofs/lean/fixtures/occurrence-loop-header-send.sigil"),
                &CompilerContext::default(),
            ),
        ),
        (
            "loop-header-pure".into(),
            true,
            project(
                include_str!("../../../proofs/lean/fixtures/occurrence-loop-header-pure.sigil"),
                &CompilerContext::default(),
            ),
        ),
    ];
    let empty_profile = HostContractProfile::new("empty".into(), 1, vec![], vec![])
        .expect("empty declarations still have a canonical nonempty profile");
    cases.push((
        "empty-explicit-profile".into(),
        true,
        formal_v9::encode(
            b"CSIR\x08\0\0\0\0\0\0\0",
            Some(&empty_profile),
            &[],
            &[],
            &[],
        )
        .expect("profile absence is distinct from an empty profile"),
    ));
    let mut mutate = |name: &str, original: &[u8], change: &dyn Fn(&mut Vec<u8>)| {
        let mut bytes = original.to_vec();
        change(&mut bytes);
        cases.push((name.into(), false, bytes));
    };
    mutate("wrong-version", &declared, &|bytes| set_word(bytes, 4, 8));
    mutate("wrong-manifest-count", &declared, &|bytes| {
        let at = record(bytes, 44);
        set_word(bytes, at + 4, 0);
    });
    mutate("missing-ffi-count", &declared, &|bytes| {
        let at = record(bytes, 44);
        set_word(bytes, at + 12, 0);
    });
    mutate("missing-root-count", &declared, &|bytes| {
        let at = record(bytes, 44);
        set_word(bytes, at + 20, 0);
    });
    mutate("declared-profile-zero-binding", &declared, &|bytes| {
        let at = record(bytes, 46);
        set_word(bytes, at + 8, 0);
    });
    mutate("legacy-profile-nonzero-binding", &legacy, &|bytes| {
        let at = record(bytes, 46);
        set_word(bytes, at + 8, 1);
    });
    mutate("wrong-ffi-argument-start", &declared, &|bytes| {
        let at = record(bytes, 46);
        set_word(bytes, at + 12, 2);
    });
    mutate("wrong-ffi-result-count", &declared, &|bytes| {
        let at = record(bytes, 46);
        set_word(bytes, at + 20, 0);
    });
    mutate("wrong-ffi-owner", &declared, &|bytes| {
        let at = record(bytes, 46);
        set_word(bytes, at + 4, 0);
    });
    mutate("wrong-ffi-name", &declared, &|bytes| {
        let at = record(bytes, 46);
        let owner = u32::from_le_bytes(bytes[at + 4..at + 8].try_into().expect("fixed word"));
        let first_name = 12 + (owner as usize + 2) * 32 + 12;
        bytes[first_name] = b'T';
    });
    mutate("name-nonzero-padding", &declared, &|bytes| {
        let at = record(bytes, 46);
        let owner = u32::from_le_bytes(bytes[at + 4..at + 8].try_into().expect("fixed word"));
        bytes[12 + (owner as usize + 2) * 32 + 19] = 1;
    });
    mutate("wrong-ffi-abi", &declared, &|bytes| {
        let at = record(bytes, 35);
        set_word(bytes, at + 12, 6);
    });
    mutate("orphan-ffi-function", &declared, &|bytes| {
        let at = record(bytes, 46);
        let owner = u32::from_le_bytes(bytes[at + 4..at + 8].try_into().expect("fixed word"));
        set_word(bytes, 12 + (owner as usize - 1) * 32 + 4, 0);
    });
    mutate("orphan-actor-function", &actors, &|bytes| {
        let at = record(bytes, 47);
        let owner = u32::from_le_bytes(bytes[at + 4..at + 8].try_into().expect("fixed word"));
        set_word(bytes, 12 + (owner as usize - 1) * 32 + 4, 0);
    });
    mutate("noncanonical-function-id", &declared, &|bytes| {
        let at = record(bytes, 34);
        set_word(bytes, at + 4, 0);
    });
    mutate("zero-value-id", &declared, &|bytes| {
        let at = record(bytes, 35);
        set_word(bytes, at + 8, 0);
    });
    mutate("orphan-value-function", &declared, &|bytes| {
        let at = record(bytes, 35);
        set_word(bytes, at + 4, 0);
    });
    mutate("wrong-operand-owner", &declared, &|bytes| {
        let at = record(bytes, 46);
        let owner = u32::from_le_bytes(bytes[at + 4..at + 8].try_into().expect("fixed word"));
        set_word(bytes, 12 + owner as usize * 32 + 4, 0);
    });
    mutate("profile-nonzero-padding", &declared, &|bytes| {
        let at = record(bytes, 44);
        let len =
            u32::from_le_bytes(bytes[at + 8..at + 12].try_into().expect("fixed word")) as usize;
        assert_ne!(len % 20, 0, "fixture must have profile padding");
        bytes[at + len.div_ceil(20) * 32 + 23] = 1;
    });
    mutate("profile-invalid-magic", &declared, &|bytes| {
        let at = record(bytes, 45);
        bytes[at + 4] = b'X';
    });
    mutate("missing-actor-count", &actors, &|bytes| {
        let at = record(bytes, 44);
        set_word(bytes, at + 16, 0);
    });
    mutate("unknown-actor-subtype", &actors, &|bytes| {
        let at = record(bytes, 47);
        set_word(bytes, at + 8, 6);
    });
    mutate("actor-reserved-word", &actors, &|bytes| {
        let at = record(bytes, 47);
        set_word(bytes, at + 12, 1);
    });
    mutate("root-payload-cannot-be-occurrence", &declared, &|bytes| {
        let at = record(bytes, 48);
        bytes[at + 1] = 3;
    });
    mutate("false-internal-root", &actors, &|bytes| {
        // A zero-flag root claims to be internal. Only kind-1 and kind-4
        // functions (and `$`-named synthetics) may carry one; the first actor
        // root here belongs to the kind-3 `Main__Start` handler, so the claim
        // is false and the decoder must refuse it.
        let at = record(bytes, 48);
        bytes[at + 3] = 0;
    });
    mutate("root-is-entry-nonboolean", &declared, &|bytes| {
        let at = record(bytes, 48);
        set_word(bytes, at + 20, 2);
    });
    mutate("root-nonzero-padding", &declared, &|bytes| {
        // Last record is the final export-name chunk; generated names in this
        // fixture do not have a length divisible by twenty.
        let at = bytes.len() - 32;
        bytes[at + 23] = 1;
    });
    mutate("global-noncanonical-id", &declared, &|bytes| {
        let at = record(bytes, 44);
        set_word(bytes, at + 24, 0);
    });
    mutate("reserved-header-byte", &declared, &|bytes| {
        let at = record(bytes, 44);
        bytes[at + 3] = 1;
    });
    mutate("trailing-record", &declared, &|bytes| {
        bytes.extend_from_slice(&[0; 32])
    });
    cases
}

#[test]
fn source_built_declarations_and_single_field_mutants_have_exact_verdicts() {
    let cases = cases();
    assert_eq!(cases.len(), 37);
    for (name, accepted, bytes) in cases {
        assert_eq!(formal_v9::decode(&bytes).is_ok(), accepted, "{name}");
    }
}

#[test]
fn occurrence_loop_header_send_is_an_explicit_production_rejection() {
    let source = include_str!("../../../proofs/lean/fixtures/occurrence-loop-header-send.sigil");
    let error = compile_named_module("declarations.sigil", source)
        .expect_err("the production v9 occurrence policy must reject the repeated Public send");
    assert_eq!(
        error.diagnostics().len(),
        1,
        "the production rejection must remain one precise diagnostic"
    );
    let diagnostic = &error.diagnostics()[0];
    assert_eq!(diagnostic.code(), codes::I013);
    assert!(
        diagnostic.message().contains("detail=40"),
        "the v9 occurrence-policy refusal must remain distinguishable: {}",
        diagnostic.message()
    );
    let span = diagnostic
        .span()
        .expect("the production refusal must identify the repeated send site");
    let send_start = source
        .find("worker.send")
        .expect("fixture contains the send");
    let send_end = send_start
        + source[send_start..]
            .find(';')
            .expect("fixture send is terminated")
        + 1;
    assert!(
        send_start <= span.start && span.end <= send_end,
        "I013/detail=40 must point inside worker.send, got {span:?}"
    );
    assert_eq!(
        &source[span.start..span.end],
        "worker.send(Ping(7))",
        "the current projection reports the Public send occurrence itself; the payload \
         boundary before it converges under the postdominance-aware pc restore"
    );
}

#[test]
fn complete_profiles_and_boundary_identities_round_trip_without_security_evidence() {
    let bytes = project(SOURCE, &CompilerContext::with_host_profile(profile(1)));
    let decoded = formal_v9::decode(&bytes).expect("canonical declarations decode");
    assert_eq!(decoded.model_version, 9);
    assert_eq!(decoded.host_profile, Some(profile(1)));
    assert_eq!(decoded.ffi_bindings.len(), 1);
    assert_eq!(decoded.ffi_bindings[0].profile_operation, 1);
    assert_eq!(decoded.foreign_identities[0].name, "tick");
    assert_eq!(
        decoded.foreign_identities[0].params,
        vec![HostValueType::I64]
    );
    assert_eq!(
        decoded.foreign_identities[0].results,
        vec![HostValueType::I64]
    );
    assert_eq!(decoded.root_sites.len(), decoded.roots.len());
    assert!(decoded.root_sites.windows(2).all(|pair| pair[0] < pair[1]));
    assert_eq!(
        formal_v9::encode(
            &decoded.legacy_v8,
            decoded.host_profile.as_ref(),
            &decoded.ffi_bindings,
            &decoded.actor_bindings,
            &decoded.roots
        )
        .expect("decoded declarations re-encode"),
        bytes
    );
    // Old verifier must reject the whole v9 envelope, while the retained old
    // program really passes it. No header patch can substitute for a new verdict.
    assert_ne!(sigil_formal_bridge::verify(&bytes), Ok(0));
    assert_eq!(sigil_formal_bridge::verify(&decoded.legacy_v8), Ok(0));
    let changed = project(SOURCE, &CompilerContext::with_host_profile(profile(2)));
    assert_ne!(bytes, changed);
    let legacy = formal_v9::decode(&project(SOURCE, &CompilerContext::default()))
        .expect("legacy-unknown declarations are representable, not private");
    assert!(legacy.host_profile.is_none());
    assert_eq!(legacy.ffi_bindings[0].profile_operation, 0);
    assert_eq!(legacy.legacy_v8, decoded.legacy_v8);
}

#[test]
fn every_truncated_prefix_and_excessive_length_refuses_without_panicking() {
    let bytes = project(SOURCE, &CompilerContext::with_host_profile(profile(1)));
    for length in 0..bytes.len() {
        assert!(
            formal_v9::decode(&bytes[..length]).is_err(),
            "prefix {length}"
        );
    }
    let mut huge_count = bytes.clone();
    set_word(&mut huge_count, 8, u32::MAX);
    assert!(formal_v9::decode(&huge_count).is_err());
    let mut huge_name = bytes;
    let at = record(&huge_name, 48);
    set_word(&mut huge_name, at + 16, u32::MAX);
    assert!(formal_v9::decode(&huge_name).is_err());
}

#[test]
fn missing_actor_metadata_is_a_projection_error_not_an_inferred_contract() {
    let compiled = compile_named_module("actors.sigil", ACTORS).expect("actor fixture compiles");
    let mut raw = air::lower(&compiled.typed);
    let function = raw
        .functions
        .iter_mut()
        .find(|function| !function.security.actor_operations.is_empty())
        .expect("fixture has actor operations");
    function.security.actor_operations.pop_first();
    assert!(
        formal::project_v9_declarations(
            &compiled.typed,
            &raw,
            &AuthorityRegistry::default(),
            &CompilerContext::default()
        )
        .is_err()
    );
}

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    let mut text = String::with_capacity(bytes.len() * 2 + 1);
    for byte in bytes {
        write!(text, "{byte:02x}").expect("writing to String cannot fail");
    }
    text.push('\n');
    text
}

#[test]
fn committed_wire_fixtures_match_the_explicit_generator_and_inventory() {
    use std::collections::BTreeSet;
    let directory =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/lean/fixtures/csir-v9");
    let mut expected = BTreeSet::new();
    for (name, accepted, bytes) in cases() {
        let verdict = if accepted { "accept" } else { "reject" };
        let name = format!("{verdict}-{name}.hex");
        assert_eq!(
            std::fs::read_to_string(directory.join(&name))
                .expect("shared wire fixture is committed"),
            hex(&bytes),
            "regenerate only with SIGIL_V9_DECLARATIONS_REGENERATE=1 and the ignored generator"
        );
        expected.insert(name);
    }
    let actual: BTreeSet<_> = std::fs::read_dir(directory)
        .expect("shared fixture directory exists")
        .map(|entry| {
            entry
                .expect("fixture entry is readable")
                .file_name()
                .into_string()
                .expect("fixture filename is UTF-8")
        })
        .collect();
    assert!(!expected.is_empty());
    assert_eq!(
        expected, actual,
        "extra or missing fixture cannot disappear from parity"
    );
}

fn declaration_jobs_are_gated(workflow: &str) -> bool {
    ["checks", "portability"].into_iter().all(|job| {
        let marker = format!("\n  {job}:\n");
        let Some((_, body)) = workflow.split_once(&marker) else {
            return false;
        };
        let commands: Vec<_> = body
            .lines()
            .take_while(|line| {
                !line.starts_with("  ") || line.starts_with("   ") || line.trim().starts_with('#')
            })
            .map(str::trim)
            .filter(|line| line.starts_with("cargo test "))
            .collect();
        ["v9_declaration_parity", "formal_v9_declarations"]
            .into_iter()
            .all(|target| {
                let target = format!("--test {target}");
                commands.iter().any(|command| command.contains(&target))
            })
    })
}

#[test]
fn declaration_parity_cannot_disappear_from_required_or_portability_ci() {
    let workflow = include_str!("../../../.github/workflows/ci.yml");
    assert!(declaration_jobs_are_gated(workflow));
    assert!(!declaration_jobs_are_gated(""));
    for target in ["v9_declaration_parity", "formal_v9_declarations"] {
        let changed = workflow.replacen(&format!("--test {target}"), "--test planted_missing", 1);
        assert!(
            !declaration_jobs_are_gated(&changed),
            "removed required {target}"
        );
        let changed = workflow.replace(&format!("--test {target}"), "--test planted_missing");
        assert!(
            !declaration_jobs_are_gated(&changed),
            "comments cannot replace {target}"
        );
    }
}

#[test]
#[ignore = "explicitly armed shared-byte fixture generator"]
fn regenerate_occurrence_declaration_fixtures() {
    assert_eq!(
        std::env::var("SIGIL_V9_DECLARATIONS_REGENERATE").as_deref(),
        Ok("1")
    );
    let directory =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/lean/fixtures/csir-v9");
    std::fs::create_dir_all(&directory).expect("fixture directory is writable");
    for (name, accepted, bytes) in cases() {
        assert_eq!(formal_v9::decode(&bytes).is_ok(), accepted, "{name}");
        let verdict = if accepted { "accept" } else { "reject" };
        std::fs::write(directory.join(format!("{verdict}-{name}.hex")), hex(&bytes))
            .expect("explicit fixture regeneration writes canonical bytes");
    }
}
