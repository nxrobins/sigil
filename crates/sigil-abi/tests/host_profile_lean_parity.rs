//! WHY THIS TEST EXISTS. The Init-only Lean host-profile decoder and the Rust
//! provider ABI must consume the same canonical bytes and reject the same hostile
//! declarations. These fixtures are shared inputs, not an alternative Rust codec.
//!
//! WHY IT CANNOT GO STALE. Positive bytes come from the production constructor;
//! each negative changes a named field of those bytes. Committed hex and exact
//! Rust verdicts are checked independently, and the inventory/hex comparators
//! have planted anti-stubs. Lean supplies its own verdicts over these same files.
//! This corpus validates declarations, never the truth of host callback promises.

use std::collections::BTreeSet;
use std::fmt::Write;
use std::ops::Range;
use std::path::PathBuf;

use sigil_abi::host_contract::{
    HostAccessMode, HostContractError, HostContractProfile, HostDomain, HostDomainAccess,
    HostDomainKind, HostDomainScope, HostOperationContract, HostValueContract, HostValueType,
    MAX_HOST_NAME_BYTES, MAX_HOST_PROFILE_ITEMS, OccurrenceVisibility, SecurityLabel,
};

const REGENERATE: &str = "SIGIL_HOST_PROFILE_PARITY_REGENERATE=1 cargo test -p sigil-abi --test host_profile_lean_parity -- --ignored regenerate_host_profile_lean_fixtures --nocapture";
const FIXTURE_DIRECTORY: &str = "proofs/lean/fixtures/host-profiles";
const IDENTITY: &str = "shared-profile";

struct Fixture {
    name: &'static str,
    bytes: Vec<u8>,
    expected: Result<(), HostContractError>,
}

fn operation(name: &str) -> HostOperationContract {
    HostOperationContract {
        module: "ffi".into(),
        name: name.into(),
        occurrence: OccurrenceVisibility::Public,
        params: vec![],
        results: vec![],
        domains: vec![],
    }
}

fn value(ty: HostValueType, label: SecurityLabel) -> HostValueContract {
    HostValueContract { ty, label }
}

fn domain(
    name: &str,
    kind: HostDomainKind,
    scope: HostDomainScope,
    label: SecurityLabel,
) -> HostDomain {
    HostDomain {
        name: name.into(),
        kind,
        scope,
        label,
    }
}

fn access(name: &str, mode: HostAccessMode) -> HostDomainAccess {
    HostDomainAccess {
        domain: name.into(),
        mode,
    }
}

fn profile(
    domains: Vec<HostDomain>,
    operations: Vec<HostOperationContract>,
) -> HostContractProfile {
    HostContractProfile::new(IDENTITY.into(), 0x0102_0304_0506_0708, domains, operations)
        .expect("positive fixture declarations obey the production host contract")
}

fn positive_profiles() -> Vec<(&'static str, HostContractProfile)> {
    let mut response = operation("response");
    response.results = vec![value(HostValueType::I64, SecurityLabel::Secret)];

    let mut next = operation("next");
    next.occurrence = OccurrenceVisibility::Secret;
    next.results = vec![value(HostValueType::I64, SecurityLabel::Secret)];
    next.domains = vec![access("stream", HostAccessMode::ReadWrite)];

    let mut send = operation("send");
    send.params = vec![value(HostValueType::I64, SecurityLabel::Secret)];
    send.domains = vec![access("out", HostAccessMode::Write)];

    let mut variants = operation("variants");
    variants.occurrence = OccurrenceVisibility::Internal;
    variants.params = vec![
        value(HostValueType::I32, SecurityLabel::Public),
        value(HostValueType::I64, SecurityLabel::Internal),
        value(HostValueType::F32, SecurityLabel::Secret),
        value(HostValueType::F64, SecurityLabel::Public),
    ];
    variants.results = vec![
        value(HostValueType::I32, SecurityLabel::Secret),
        value(HostValueType::I64, SecurityLabel::Secret),
        value(HostValueType::F32, SecurityLabel::SecretCt),
        value(HostValueType::F64, SecurityLabel::Secret),
    ];
    variants.domains = vec![
        access("a-memory", HostAccessMode::Read),
        access("b-output", HostAccessMode::Write),
        access("c-state", HostAccessMode::ReadWrite),
        access("d-stream", HostAccessMode::ReadWrite),
        access("e-ct-output", HostAccessMode::Write),
    ];

    let ordered_domains = ["b", "a"]
        .into_iter()
        .map(|name| {
            domain(
                name,
                HostDomainKind::State,
                HostDomainScope::Shared,
                SecurityLabel::Public,
            )
        })
        .collect();
    let mut ordered_a = operation("z");
    ordered_a.module = "a".into();
    ordered_a.domains = vec![
        access("b", HostAccessMode::Write),
        access("a", HostAccessMode::Read),
    ];
    let mut ordered_b = operation("a");
    ordered_b.module = "b".into();

    vec![
        ("accept-empty", profile(vec![], vec![])),
        (
            "accept-public-secret-result",
            profile(vec![], vec![response]),
        ),
        (
            "accept-isolated-secret-stream",
            profile(
                vec![domain(
                    "stream",
                    HostDomainKind::InputStream,
                    HostDomainScope::PerSite,
                    SecurityLabel::Secret,
                )],
                vec![next],
            ),
        ),
        (
            "accept-public-secret-payload",
            profile(
                vec![domain(
                    "out",
                    HostDomainKind::Output,
                    HostDomainScope::PerActor,
                    SecurityLabel::Secret,
                )],
                vec![send],
            ),
        ),
        (
            "accept-all-variants",
            profile(
                vec![
                    domain(
                        "a-memory",
                        HostDomainKind::GuestMemory,
                        HostDomainScope::Shared,
                        SecurityLabel::Secret,
                    ),
                    domain(
                        "b-output",
                        HostDomainKind::Output,
                        HostDomainScope::PerSite,
                        SecurityLabel::Secret,
                    ),
                    domain(
                        "c-state",
                        HostDomainKind::State,
                        HostDomainScope::PerActor,
                        SecurityLabel::Secret,
                    ),
                    domain(
                        "d-stream",
                        HostDomainKind::InputStream,
                        HostDomainScope::Shared,
                        SecurityLabel::Secret,
                    ),
                    domain(
                        "e-ct-output",
                        HostDomainKind::Output,
                        HostDomainScope::PerActor,
                        SecurityLabel::SecretCt,
                    ),
                    domain(
                        "f-internal",
                        HostDomainKind::State,
                        HostDomainScope::Shared,
                        SecurityLabel::Internal,
                    ),
                ],
                vec![variants],
            ),
        ),
        (
            "accept-canonical-order",
            profile(ordered_domains, vec![ordered_b, ordered_a]),
        ),
        (
            "accept-name-alphabet-limit",
            HostContractProfile::new(
                "A0_./:-z".repeat(MAX_HOST_NAME_BYTES / 8),
                u64::MAX,
                vec![],
                vec![HostOperationContract {
                    module: "_./:-".into(),
                    name: "Z9_./:-".into(),
                    ..operation("unused")
                }],
            )
            .expect("all allowed name bytes and the exact name ceiling are legal"),
        ),
    ]
}

// Offsets locate mutation sites in bytes emitted by the production encoder;
// they never encode declarations or decide whether a profile should be legal.
struct NameOffsets {
    length: usize,
    bytes: Range<usize>,
}

struct DomainOffsets {
    record: Range<usize>,
    name: NameOffsets,
    tags: usize,
}

struct AccessOffsets {
    record: Range<usize>,
    name: NameOffsets,
    mode: usize,
}

struct OperationOffsets {
    record: Range<usize>,
    module: NameOffsets,
    name: NameOffsets,
    occurrence: usize,
    params_count: usize,
    params: Vec<usize>,
    results: Vec<usize>,
    accesses: Vec<AccessOffsets>,
}

struct Offsets {
    identity: NameOffsets,
    revision: usize,
    domains_count: usize,
    domains: Vec<DomainOffsets>,
    operations: Vec<OperationOffsets>,
}

fn name_offsets(cursor: &mut usize, name: &str) -> NameOffsets {
    let length = *cursor;
    *cursor += 4;
    let start = *cursor;
    *cursor += name.len();
    NameOffsets {
        length,
        bytes: start..*cursor,
    }
}

fn offsets(profile: &HostContractProfile) -> Offsets {
    let mut cursor = b"SIGIL-HOST-PROFILE\0".len() + 4;
    let identity = name_offsets(&mut cursor, profile.identity());
    let revision = cursor;
    cursor += 8;
    let domains_count = cursor;
    cursor += 4;
    let domains = profile
        .domains()
        .iter()
        .map(|domain| {
            let start = cursor;
            let name = name_offsets(&mut cursor, &domain.name);
            let tags = cursor;
            cursor += 3;
            DomainOffsets {
                record: start..cursor,
                name,
                tags,
            }
        })
        .collect();
    cursor += 4;
    let operations = profile
        .operations()
        .iter()
        .map(|operation| {
            let start = cursor;
            let module = name_offsets(&mut cursor, &operation.module);
            let name = name_offsets(&mut cursor, &operation.name);
            let occurrence = cursor;
            cursor += 1;
            let params_count = cursor;
            let mut signature = |values: &[HostValueContract]| {
                cursor += 4;
                values
                    .iter()
                    .map(|_| {
                        let position = cursor;
                        cursor += 2;
                        position
                    })
                    .collect::<Vec<_>>()
            };
            let params = signature(&operation.params);
            let results = signature(&operation.results);
            cursor += 4;
            let accesses = operation
                .domains
                .iter()
                .map(|access| {
                    let start = cursor;
                    let name = name_offsets(&mut cursor, &access.domain);
                    let mode = cursor;
                    cursor += 1;
                    AccessOffsets {
                        record: start..cursor,
                        name,
                        mode,
                    }
                })
                .collect();
            OperationOffsets {
                record: start..cursor,
                module,
                name,
                occurrence,
                params_count,
                params,
                results,
                accesses,
            }
        })
        .collect();
    assert_eq!(
        cursor,
        profile.canonical_bytes().len(),
        "mutation offsets must cover the canonical encoding exactly"
    );
    Offsets {
        identity,
        revision,
        domains_count,
        domains,
        operations,
    }
}

fn set_u32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn swap_adjacent(bytes: &mut Vec<u8>, first: Range<usize>, second: Range<usize>) {
    assert_eq!(
        first.end, second.start,
        "the selected records must be adjacent"
    );
    let swapped = [
        bytes[second.clone()].to_vec(),
        bytes[first.clone()].to_vec(),
    ]
    .concat();
    bytes.splice(first.start..second.end, swapped);
}

fn fixtures() -> Vec<Fixture> {
    let profiles = positive_profiles();
    let mut fixtures = profiles
        .iter()
        .map(|(name, profile)| Fixture {
            name,
            bytes: profile.canonical_bytes().to_vec(),
            expected: Ok(()),
        })
        .collect::<Vec<_>>();
    let mut reject = |name, source: usize, expected, mutate: &dyn Fn(&mut Vec<u8>, &Offsets)| {
        let profile = &profiles[source].1;
        let mut bytes = profile.canonical_bytes().to_vec();
        mutate(&mut bytes, &offsets(profile));
        assert_ne!(
            bytes,
            profile.canonical_bytes(),
            "every negative fixture must mutate its positive twin"
        );
        fixtures.push(Fixture {
            name,
            bytes,
            expected: Err(expected),
        });
    };

    reject(
        "reject-truncated",
        0,
        HostContractError::InvalidEncoding,
        &|bytes, _| {
            bytes.pop();
        },
    );
    reject(
        "reject-trailing",
        0,
        HostContractError::InvalidEncoding,
        &|bytes, _| bytes.push(0),
    );
    reject(
        "reject-magic",
        0,
        HostContractError::InvalidEncoding,
        &|bytes, _| bytes[0] = 0,
    );
    reject(
        "reject-version",
        0,
        HostContractError::UnsupportedVersion(2),
        &|bytes, _| set_u32(bytes, b"SIGIL-HOST-PROFILE\0".len(), 2),
    );
    reject(
        "reject-zero-revision",
        0,
        HostContractError::ZeroRevision,
        &|bytes, at| bytes[at.revision..at.revision + 8].fill(0),
    );
    reject(
        "reject-empty-name",
        0,
        HostContractError::InvalidName,
        &|bytes, at| set_u32(bytes, at.identity.length, 0),
    );
    reject(
        "reject-invalid-name",
        0,
        HostContractError::InvalidName,
        &|bytes, at| bytes[at.identity.bytes.start] = b' ',
    );
    reject(
        "reject-non-ascii-name",
        0,
        HostContractError::InvalidName,
        &|bytes, at| bytes[at.identity.bytes.start] = 0xff,
    );
    reject(
        "reject-name-limit",
        0,
        HostContractError::InvalidName,
        &|bytes, at| set_u32(bytes, at.identity.length, (MAX_HOST_NAME_BYTES + 1) as u32),
    );
    reject(
        "reject-domain-name",
        2,
        HostContractError::InvalidName,
        &|bytes, at| bytes[at.domains[0].name.bytes.start] = b'|',
    );
    reject(
        "reject-module-name",
        1,
        HostContractError::InvalidName,
        &|bytes, at| bytes[at.operations[0].module.bytes.start] = b'\0',
    );
    reject(
        "reject-operation-name",
        1,
        HostContractError::InvalidName,
        &|bytes, at| bytes[at.operations[0].name.bytes.start] = b'\n',
    );
    reject(
        "reject-domain-kind",
        2,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.domains[0].tags] = 4,
    );
    reject(
        "reject-domain-scope",
        2,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.domains[0].tags + 1] = 3,
    );
    reject(
        "reject-domain-label",
        2,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.domains[0].tags + 2] = 4,
    );
    reject(
        "reject-occurrence-tag",
        1,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.operations[0].occurrence] = 3,
    );
    reject(
        "reject-value-type",
        1,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.operations[0].results[0]] = 4,
    );
    reject(
        "reject-value-label",
        1,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.operations[0].results[0] + 1] = 4,
    );
    reject(
        "reject-access-tag",
        2,
        HostContractError::InvalidEncoding,
        &|bytes, at| bytes[at.operations[0].accesses[0].mode] = 3,
    );
    reject(
        "reject-item-count",
        0,
        HostContractError::TooManyItems,
        &|bytes, at| set_u32(bytes, at.domains_count, (MAX_HOST_PROFILE_ITEMS + 1) as u32),
    );
    reject(
        "reject-cumulative-item-count",
        2,
        HostContractError::TooManyItems,
        &|bytes, at| {
            set_u32(
                bytes,
                at.operations[0].params_count,
                (MAX_HOST_PROFILE_ITEMS - 1) as u32,
            )
        },
    );
    reject(
        "reject-short-item-count",
        0,
        HostContractError::InvalidEncoding,
        &|bytes, at| set_u32(bytes, at.domains_count, 1),
    );
    reject(
        "reject-domain-order",
        5,
        HostContractError::NonCanonicalEncoding,
        &|bytes, at| {
            swap_adjacent(
                bytes,
                at.domains[0].record.clone(),
                at.domains[1].record.clone(),
            )
        },
    );
    reject(
        "reject-operation-order",
        5,
        HostContractError::NonCanonicalEncoding,
        &|bytes, at| {
            swap_adjacent(
                bytes,
                at.operations[0].record.clone(),
                at.operations[1].record.clone(),
            )
        },
    );
    reject(
        "reject-access-order",
        5,
        HostContractError::NonCanonicalEncoding,
        &|bytes, at| {
            swap_adjacent(
                bytes,
                at.operations[0].accesses[0].record.clone(),
                at.operations[0].accesses[1].record.clone(),
            )
        },
    );
    reject(
        "reject-duplicate-domain",
        5,
        HostContractError::DuplicateDomain("a".into()),
        &|bytes, at| bytes[at.domains[1].name.bytes.start] = b'a',
    );
    reject(
        "reject-duplicate-operation",
        5,
        HostContractError::DuplicateOperation {
            module: "a".into(),
            name: "z".into(),
        },
        &|bytes, at| {
            bytes[at.operations[1].module.bytes.start] = b'a';
            bytes[at.operations[1].name.bytes.start] = b'z';
        },
    );
    reject(
        "reject-duplicate-access",
        5,
        HostContractError::DuplicateAccess("a".into()),
        &|bytes, at| bytes[at.operations[0].accesses[1].name.bytes.start] = b'a',
    );
    reject(
        "reject-missing-domain",
        2,
        HostContractError::UnknownDomain("xtream".into()),
        &|bytes, at| bytes[at.operations[0].accesses[0].name.bytes.start] = b'x',
    );
    reject(
        "reject-stream-readonly",
        2,
        HostContractError::InvalidAccess("stream".into()),
        &|bytes, at| bytes[at.operations[0].accesses[0].mode] = HostAccessMode::Read as u8,
    );
    reject(
        "reject-output-read",
        3,
        HostContractError::InvalidAccess("out".into()),
        &|bytes, at| bytes[at.operations[0].accesses[0].mode] = HostAccessMode::Read as u8,
    );
    reject(
        "reject-ct-parameter",
        3,
        HostContractError::SecretCtInput,
        &|bytes, at| bytes[at.operations[0].params[0] + 1] = SecurityLabel::SecretCt as u8,
    );
    reject(
        "reject-ct-read-domain",
        2,
        HostContractError::SecretCtInput,
        &|bytes, at| bytes[at.domains[0].tags + 2] = SecurityLabel::SecretCt as u8,
    );
    reject(
        "reject-downward-domain",
        3,
        HostContractError::DomainFlow {
            domain: "out".into(),
        },
        &|bytes, at| bytes[at.domains[0].tags + 2] = SecurityLabel::Public as u8,
    );
    reject(
        "reject-downward-result",
        2,
        HostContractError::ResultFlow { result: 0 },
        &|bytes, at| bytes[at.operations[0].results[0] + 1] = SecurityLabel::Public as u8,
    );
    reject(
        "reject-private-public-domain",
        5,
        HostContractError::DomainFlow { domain: "b".into() },
        &|bytes, at| bytes[at.operations[0].occurrence] = OccurrenceVisibility::Internal as u8,
    );
    reject(
        "reject-private-public-result",
        1,
        HostContractError::ResultFlow { result: 0 },
        &|bytes, at| {
            bytes[at.operations[0].occurrence] = OccurrenceVisibility::Internal as u8;
            bytes[at.operations[0].results[0] + 1] = SecurityLabel::Public as u8;
        },
    );
    reject(
        "reject-read-domain-public-result",
        2,
        HostContractError::ResultFlow { result: 0 },
        &|bytes, at| {
            bytes[at.operations[0].occurrence] = OccurrenceVisibility::Public as u8;
            bytes[at.operations[0].results[0] + 1] = SecurityLabel::Public as u8;
        },
    );
    fixtures
}

fn fixture_directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("sigil-abi is a child of crates")
        .parent()
        .expect("crates is a child of the workspace")
        .join(FIXTURE_DIRECTORY)
}

fn render_hex(bytes: &[u8]) -> String {
    let mut text = String::new();
    for chunk in bytes.chunks(32) {
        for byte in chunk {
            write!(&mut text, "{byte:02x}").expect("formatting into a String cannot fail");
        }
        text.push('\n');
    }
    text
}

fn parse_hex(text: &str) -> Result<Vec<u8>, &'static str> {
    let digits = text
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect::<Vec<_>>();
    if digits.len() % 2 != 0 {
        return Err("odd number of hex digits");
    }
    digits
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let high = char::from(pair[0])
                .to_digit(16)
                .ok_or("invalid hex digit")?;
            let low = char::from(pair[1])
                .to_digit(16)
                .ok_or("invalid hex digit")?;
            Ok((16 * high + low) as u8)
        })
        .collect()
}

fn compare_fixture(fixture: &Fixture, text: &str) -> Result<(), &'static str> {
    if parse_hex(text)? != fixture.bytes {
        return Err("fixture bytes differ from production construction");
    }
    if text != render_hex(&fixture.bytes) {
        return Err("fixture hex is not canonical lowercase LF text");
    }
    Ok(())
}

fn inventory_matches(actual: &[String], expected: &BTreeSet<String>) -> bool {
    actual.len() == expected.len() && actual.iter().cloned().collect::<BTreeSet<_>>() == *expected
}

#[test]
fn shared_host_profile_fixtures_match_production_bytes_and_exact_rust_verdicts() {
    let directory = fixture_directory();
    for fixture in fixtures() {
        let path = directory.join(format!("{}.hex", fixture.name));
        let text = std::fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "cannot read {}: {error}; regenerate using {REGENERATE}",
                path.display()
            )
        });
        assert_eq!(
            compare_fixture(&fixture, &text),
            Ok(()),
            "{}; regenerate using {REGENERATE} and apply the printed patch",
            path.display()
        );
        let bytes = parse_hex(&text).expect("comparison above established valid hex");
        assert_eq!(
            HostContractProfile::decode(&bytes).map(|_| ()),
            fixture.expected,
            "{} must have its independently declared verdict",
            fixture.name
        );
    }
}

#[test]
fn every_shared_positive_rejects_every_truncated_prefix() {
    for (name, profile) in positive_profiles() {
        let bytes = profile.canonical_bytes();
        assert_eq!(HostContractProfile::decode(bytes).as_ref(), Ok(&profile));
        for end in 0..bytes.len() {
            assert!(
                HostContractProfile::decode(&bytes[..end]).is_err(),
                "{name} must reject truncated prefix {end}"
            );
        }
    }
}

#[test]
fn fixture_comparators_detect_planted_drift_and_inventory_changes() {
    let fixture = Fixture {
        name: "anti-stub",
        bytes: vec![0, 255],
        expected: Ok(()),
    };
    assert_eq!(compare_fixture(&fixture, "00ff\n"), Ok(()));
    assert!(compare_fixture(&fixture, "00fe\n").is_err());
    assert!(compare_fixture(&fixture, "00FF\n").is_err());
    assert!(parse_hex("0").is_err());
    assert!(parse_hex("0g").is_err());
    let expected = BTreeSet::from(["a.hex".into(), "b.hex".into()]);
    assert!(inventory_matches(
        &["b.hex".into(), "a.hex".into()],
        &expected
    ));
    assert!(!inventory_matches(&["a.hex".into()], &expected));
    assert!(!inventory_matches(
        &["a.hex".into(), "b.hex".into(), "extra.hex".into()],
        &expected
    ));
    assert!(!inventory_matches(
        &["a.hex".into(), "a.hex".into()],
        &expected
    ));
    let actual = std::fs::read_dir(fixture_directory())
        .expect("shared fixture directory must exist")
        .map(|entry| {
            entry
                .expect("fixture directory entry must be readable")
                .file_name()
                .into_string()
                .expect("fixture filenames are ASCII")
        })
        .collect::<Vec<_>>();
    let expected = fixtures()
        .iter()
        .map(|fixture| format!("{}.hex", fixture.name))
        .collect();
    assert!(
        inventory_matches(&actual, &expected),
        "committed fixtures must exactly match the shared inventory"
    );
}

#[test]
fn accepted_profile_inventory_covers_every_wire_enum_variant() {
    let profiles = positive_profiles();
    let mut types = BTreeSet::new();
    let mut labels = BTreeSet::new();
    let mut kinds = BTreeSet::new();
    let mut scopes = BTreeSet::new();
    let mut accesses = BTreeSet::new();
    let mut occurrences = BTreeSet::new();
    for (_, profile) in &profiles {
        for domain in profile.domains() {
            kinds.insert(domain.kind as u8);
            scopes.insert(domain.scope as u8);
            labels.insert(domain.label as u8);
        }
        for operation in profile.operations() {
            occurrences.insert(operation.occurrence as u8);
            for value in operation.params.iter().chain(&operation.results) {
                types.insert(value.ty as u8);
                labels.insert(value.label as u8);
            }
            accesses.extend(operation.domains.iter().map(|access| access.mode as u8));
        }
    }
    assert_eq!(types, BTreeSet::from([0, 1, 2, 3]));
    assert_eq!(labels, BTreeSet::from([0, 1, 2, 3]));
    assert_eq!(kinds, BTreeSet::from([0, 1, 2, 3]));
    assert_eq!(scopes, BTreeSet::from([0, 1, 2]));
    assert_eq!(accesses, BTreeSet::from([0, 1, 2]));
    assert_eq!(occurrences, BTreeSet::from([0, 1, 2]));
}

#[test]
#[ignore = "prints a fixture patch only when explicitly armed"]
fn regenerate_host_profile_lean_fixtures() {
    assert_eq!(
        std::env::var("SIGIL_HOST_PROFILE_PARITY_REGENERATE").as_deref(),
        Ok("1"),
        "regenerate only via {REGENERATE}"
    );
    let fixtures = fixtures();
    for fixture in &fixtures {
        assert_eq!(
            HostContractProfile::decode(&fixture.bytes).map(|_| ()),
            fixture.expected,
            "{} must have the declared verdict before fixture generation",
            fixture.name
        );
    }
    println!("*** Begin Patch");
    for fixture in &fixtures {
        let path = fixture_directory().join(format!("{}.hex", fixture.name));
        match std::fs::read_to_string(&path) {
            Ok(previous) => {
                println!("*** Update File: {FIXTURE_DIRECTORY}/{}.hex", fixture.name);
                println!("@@");
                for line in previous.lines() {
                    println!("-{line}");
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                println!("*** Add File: {FIXTURE_DIRECTORY}/{}.hex", fixture.name);
            }
            Err(error) => panic!(
                "cannot inspect existing fixture {}: {error}",
                path.display()
            ),
        }
        for line in render_hex(&fixture.bytes).lines() {
            println!("+{line}");
        }
    }
    println!("*** End Patch");
    println!(
        "shared host-profile fixtures: {} accepted, {} rejected",
        fixtures
            .iter()
            .filter(|fixture| fixture.expected.is_ok())
            .count(),
        fixtures
            .iter()
            .filter(|fixture| fixture.expected.is_err())
            .count()
    );
}
