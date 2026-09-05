use sigil_abi::host_contract::{
    HOST_PROFILE_VERSION, HostAccessMode, HostContractError, HostContractProfile, HostDomain,
    HostDomainAccess, HostDomainKind, HostDomainScope, HostOperationContract, HostValueContract,
    HostValueType, MAX_HOST_NAME_BYTES, MAX_HOST_PROFILE_BYTES, MAX_HOST_PROFILE_ITEMS,
    OccurrenceVisibility, SecurityLabel,
};

fn value(label: SecurityLabel) -> HostValueContract {
    HostValueContract {
        ty: HostValueType::I64,
        label,
    }
}

fn domain(name: &str, kind: HostDomainKind, label: SecurityLabel) -> HostDomain {
    HostDomain {
        name: name.into(),
        kind,
        scope: HostDomainScope::Shared,
        label,
    }
}

fn access(name: &str, mode: HostAccessMode) -> HostDomainAccess {
    HostDomainAccess {
        domain: name.into(),
        mode,
    }
}

fn operation(name: &str) -> HostOperationContract {
    HostOperationContract {
        module: "host".into(),
        name: name.into(),
        occurrence: OccurrenceVisibility::default(),
        params: vec![],
        results: vec![],
        domains: vec![],
    }
}

fn profile(
    domains: Vec<HostDomain>,
    operations: Vec<HostOperationContract>,
) -> Result<HostContractProfile, HostContractError> {
    HostContractProfile::new("test-host".into(), 1, domains, operations)
}

#[test]
fn default_occurrence_is_public_even_for_secret_payloads() {
    let mut send = operation("send_secret");
    send.params = vec![value(SecurityLabel::Secret)];
    send.domains = vec![access("secret-mailbox", HostAccessMode::Write)];
    let profile = profile(
        vec![domain(
            "secret-mailbox",
            HostDomainKind::Output,
            SecurityLabel::Secret,
        )],
        vec![send],
    )
    .unwrap();
    let contract = profile
        .resolve("host", "send_secret", &[HostValueType::I64], &[])
        .unwrap();
    assert_eq!(contract.occurrence, OccurrenceVisibility::Public);
    assert_eq!(contract.params[0].label, SecurityLabel::Secret);
}

#[test]
fn zero_argument_private_operation_cannot_write_public_domain() {
    let mut tick = operation("tick");
    tick.occurrence = OccurrenceVisibility::Secret;
    tick.domains = vec![access("public-counter", HostAccessMode::Write)];
    assert_eq!(
        profile(
            vec![domain(
                "public-counter",
                HostDomainKind::State,
                SecurityLabel::Public
            )],
            vec![tick]
        ),
        Err(HostContractError::DomainFlow {
            domain: "public-counter".into()
        }),
    );
}

#[test]
fn private_stream_consumption_cannot_shift_public_stream() {
    for visibility in [OccurrenceVisibility::Internal, OccurrenceVisibility::Secret] {
        let mut random = operation("random");
        random.occurrence = visibility;
        random.results = vec![value(SecurityLabel::Secret)];
        random.domains = vec![access("shared-prng", HostAccessMode::ReadWrite)];
        assert_eq!(
            profile(
                vec![domain(
                    "shared-prng",
                    HostDomainKind::InputStream,
                    SecurityLabel::Public
                )],
                vec![random]
            ),
            Err(HostContractError::DomainFlow {
                domain: "shared-prng".into()
            }),
        );
    }
}

#[test]
fn input_stream_access_cannot_omit_cursor_advancement() {
    for mode in [HostAccessMode::Read, HostAccessMode::Write] {
        let mut random = operation("random");
        random.domains = vec![access("prng", mode)];
        assert_eq!(
            profile(
                vec![domain(
                    "prng",
                    HostDomainKind::InputStream,
                    SecurityLabel::Public
                )],
                vec![random]
            ),
            Err(HostContractError::InvalidAccess("prng".into())),
        );
    }
}

#[test]
fn private_state_cannot_be_laundered_through_another_public_operation() {
    let state = domain("counter", HostDomainKind::State, SecurityLabel::Secret);
    let mut private_tick = operation("tick");
    private_tick.occurrence = OccurrenceVisibility::Secret;
    private_tick.domains = vec![access("counter", HostAccessMode::ReadWrite)];
    let mut public_read = operation("read");
    public_read.domains = vec![access("counter", HostAccessMode::Read)];
    public_read.results = vec![value(SecurityLabel::Public)];
    assert_eq!(
        profile(vec![state], vec![private_tick, public_read]),
        Err(HostContractError::ResultFlow { result: 0 }),
    );
}

#[test]
fn isolated_private_stateful_and_public_operations_can_coexist() {
    let mut private_next = operation("private_next");
    private_next.occurrence = OccurrenceVisibility::Secret;
    private_next.results = vec![value(SecurityLabel::Secret)];
    private_next.domains = vec![access("private-stream", HostAccessMode::ReadWrite)];
    let mut public_next = operation("public_next");
    public_next.results = vec![value(SecurityLabel::Public)];
    public_next.domains = vec![access("public-stream", HostAccessMode::ReadWrite)];
    let mut private_stream = domain(
        "private-stream",
        HostDomainKind::InputStream,
        SecurityLabel::Secret,
    );
    private_stream.scope = HostDomainScope::PerSite;
    let profile = profile(
        vec![
            private_stream,
            domain(
                "public-stream",
                HostDomainKind::InputStream,
                SecurityLabel::Public,
            ),
        ],
        vec![private_next, public_next],
    )
    .unwrap();
    assert_eq!(profile.operations().len(), 2);
}

#[test]
fn all_results_and_written_domains_carry_input_influence() {
    let mut copy = operation("copy");
    copy.params = vec![value(SecurityLabel::Secret)];
    copy.results = vec![value(SecurityLabel::Secret), value(SecurityLabel::Public)];
    assert_eq!(
        profile(vec![], vec![copy.clone()]),
        Err(HostContractError::ResultFlow { result: 1 })
    );
    copy.results.clear();
    copy.domains = vec![access("public", HostAccessMode::Write)];
    assert_eq!(
        profile(
            vec![domain(
                "public",
                HostDomainKind::GuestMemory,
                SecurityLabel::Public
            )],
            vec![copy]
        ),
        Err(HostContractError::DomainFlow {
            domain: "public".into()
        }),
    );
}

#[test]
fn secretct_values_cannot_enter_variable_time_hosts() {
    let mut send = operation("send");
    send.params = vec![value(SecurityLabel::SecretCt)];
    assert_eq!(
        profile(vec![], vec![send]),
        Err(HostContractError::SecretCtInput)
    );
    let mut read = operation("read");
    read.domains = vec![access("ct-state", HostAccessMode::Read)];
    assert_eq!(
        profile(
            vec![domain(
                "ct-state",
                HostDomainKind::State,
                SecurityLabel::SecretCt
            )],
            vec![read]
        ),
        Err(HostContractError::SecretCtInput),
    );
}

#[test]
fn unknown_duplicate_and_conflicting_declarations_fail_closed() {
    let state = domain("state", HostDomainKind::State, SecurityLabel::Public);
    assert_eq!(
        profile(vec![state.clone(), state.clone()], vec![]),
        Err(HostContractError::DuplicateDomain("state".into()))
    );
    let mut read = operation("read");
    read.domains = vec![access("unknown", HostAccessMode::Read)];
    assert_eq!(
        profile(vec![], vec![read.clone()]),
        Err(HostContractError::UnknownDomain("unknown".into()))
    );
    read.domains = vec![
        access("state", HostAccessMode::Read),
        access("state", HostAccessMode::Write),
    ];
    assert_eq!(
        profile(vec![state], vec![read]),
        Err(HostContractError::DuplicateAccess("state".into()))
    );
    let mut overloaded = operation("same");
    overloaded.params = vec![value(SecurityLabel::Public)];
    assert_eq!(
        profile(vec![], vec![operation("same"), overloaded]),
        Err(HostContractError::DuplicateOperation {
            module: "host".into(),
            name: "same".into()
        }),
    );
}

#[test]
fn names_are_not_trimmed_normalized_or_delimiter_decoded() {
    for invalid in [
        "",
        " host",
        "host ",
        "host\0",
        "host\n",
        "höst",
        "host|name",
        "host=other",
    ] {
        assert_eq!(
            HostContractProfile::new(invalid.into(), 1, vec![], vec![]),
            Err(HostContractError::InvalidName)
        );
        let mut op = operation("op");
        op.module = invalid.into();
        assert_eq!(
            profile(vec![], vec![op]),
            Err(HostContractError::InvalidName)
        );
    }
    assert_eq!(
        HostContractProfile::new("host".into(), 0, vec![], vec![]),
        Err(HostContractError::ZeroRevision),
    );
}

#[test]
fn name_and_item_ceilings_are_checked() {
    assert!(HostContractProfile::new("x".repeat(MAX_HOST_NAME_BYTES), 1, vec![], vec![]).is_ok());
    assert_eq!(
        HostContractProfile::new("x".repeat(MAX_HOST_NAME_BYTES + 1), 1, vec![], vec![]),
        Err(HostContractError::InvalidName),
    );
    let mut large = operation("large");
    large.params = vec![value(SecurityLabel::Public); MAX_HOST_PROFILE_ITEMS];
    assert_eq!(
        profile(vec![], vec![large]),
        Err(HostContractError::TooManyItems)
    );
}

#[test]
fn exact_module_name_arity_types_results_and_order_are_required() {
    let mut op = operation("op");
    op.params = vec![
        value(SecurityLabel::Public),
        HostValueContract {
            ty: HostValueType::I32,
            label: SecurityLabel::Public,
        },
    ];
    op.results = vec![value(SecurityLabel::Public)];
    let profile = profile(vec![], vec![op]).unwrap();
    assert!(
        profile
            .resolve(
                "host",
                "op",
                &[HostValueType::I64, HostValueType::I32],
                &[HostValueType::I64]
            )
            .is_ok()
    );
    for (params, results) in [
        (
            vec![HostValueType::I32, HostValueType::I64],
            vec![HostValueType::I64],
        ),
        (vec![HostValueType::I64], vec![HostValueType::I64]),
        (vec![HostValueType::I64, HostValueType::I32], vec![]),
        (
            vec![HostValueType::I64, HostValueType::I32],
            vec![HostValueType::F64],
        ),
    ] {
        assert!(matches!(
            profile.resolve("host", "op", &params, &results),
            Err(HostContractError::SignatureMismatch { .. })
        ));
    }
    for (module, name) in [("other", "op"), ("host", "other"), ("host", "op ")] {
        assert!(matches!(
            profile.resolve(module, name, &[], &[]),
            Err(HostContractError::UnknownOperation { .. })
        ));
    }
}

#[test]
fn canonical_bytes_are_independent_of_declaration_and_access_order() {
    let a = domain("a", HostDomainKind::State, SecurityLabel::Public);
    let b = domain("b", HostDomainKind::State, SecurityLabel::Public);
    let mut op = operation("op");
    op.domains = vec![
        access("a", HostAccessMode::Read),
        access("b", HostAccessMode::Write),
    ];
    let first = profile(
        vec![a.clone(), b.clone()],
        vec![op.clone(), operation("unused")],
    )
    .unwrap();
    op.domains.reverse();
    let second = profile(vec![b, a], vec![operation("unused"), op]).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert!(
        second
            .check_required_fingerprint(&first.fingerprint())
            .is_ok()
    );
}

#[test]
fn every_security_contract_field_is_bound_into_the_fingerprint() {
    let base_domain = domain("state", HostDomainKind::State, SecurityLabel::Secret);
    let mut base_op = operation("op");
    base_op.params = vec![value(SecurityLabel::Public)];
    base_op.results = vec![value(SecurityLabel::Secret)];
    base_op.domains = vec![access("state", HostAccessMode::ReadWrite)];
    let base = profile(vec![base_domain.clone()], vec![base_op.clone()]).unwrap();
    let mut variants = vec![
        HostContractProfile::new(
            "another-host".into(),
            1,
            vec![base_domain.clone()],
            vec![base_op.clone()],
        )
        .unwrap(),
        HostContractProfile::new(
            "test-host".into(),
            2,
            vec![base_domain.clone()],
            vec![base_op.clone()],
        )
        .unwrap(),
    ];
    for mutate in [
        |op: &mut HostOperationContract| op.module = "other-module".into(),
        |op: &mut HostOperationContract| op.name = "other-operation".into(),
        |op: &mut HostOperationContract| op.occurrence = OccurrenceVisibility::Secret,
        |op: &mut HostOperationContract| op.params[0].ty = HostValueType::I32,
        |op: &mut HostOperationContract| op.params[0].label = SecurityLabel::Secret,
        |op: &mut HostOperationContract| op.results[0].ty = HostValueType::F64,
        |op: &mut HostOperationContract| op.results[0].label = SecurityLabel::SecretCt,
        |op: &mut HostOperationContract| op.domains[0].mode = HostAccessMode::Read,
    ] {
        let mut op = base_op.clone();
        mutate(&mut op);
        variants.push(profile(vec![base_domain.clone()], vec![op]).unwrap());
    }
    for mutate in [
        |d: &mut HostDomain| d.kind = HostDomainKind::InputStream,
        |d: &mut HostDomain| d.scope = HostDomainScope::PerSite,
        |d: &mut HostDomain| d.label = SecurityLabel::Internal,
    ] {
        let mut d = base_domain.clone();
        mutate(&mut d);
        variants.push(profile(vec![d], vec![base_op.clone()]).unwrap());
    }
    let mut renamed_domain = base_domain.clone();
    renamed_domain.name = "another-state".into();
    let mut renamed_op = base_op;
    renamed_op.domains[0].domain = renamed_domain.name.clone();
    variants.push(profile(vec![renamed_domain], vec![renamed_op]).unwrap());
    for changed in variants {
        assert_ne!(base.canonical_bytes(), changed.canonical_bytes());
        assert_ne!(base.fingerprint(), changed.fingerprint());
        assert_eq!(
            changed.check_required_fingerprint(&base.fingerprint()),
            Err(HostContractError::ProfileMismatch)
        );
    }
}

#[test]
fn encoding_pins_domain_separator_fixed_widths_and_little_endian_order() {
    let profile =
        HostContractProfile::new("test".into(), 0x0102_0304_0506_0708, vec![], vec![]).unwrap();
    assert_eq!(HOST_PROFILE_VERSION, 1);
    assert_eq!(profile.canonical_bytes(), b"SIGIL-HOST-PROFILE\0\x01\0\0\0\x04\0\0\0test\x08\x07\x06\x05\x04\x03\x02\x01\0\0\0\0\0\0\0\0");
    assert_eq!(profile.identity(), "test");
    assert_eq!(profile.revision(), 0x0102_0304_0506_0708);
    let digest = profile
        .fingerprint()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(
        digest,
        "7fe8e03c0832eba63e4782fa32f619872cecb4a253d5c4caabfe682ccc46a8f5"
    );
}

#[test]
fn decoder_enforces_byte_ceiling_before_parsing_or_allocating_records() {
    let bytes = vec![0; MAX_HOST_PROFILE_BYTES + 1];
    assert_eq!(
        HostContractProfile::decode(&bytes),
        Err(HostContractError::TooManyBytes)
    );
}

#[test]
fn every_occurrence_and_domain_label_pair_obeys_the_lattice() {
    for occurrence in [
        OccurrenceVisibility::Public,
        OccurrenceVisibility::Internal,
        OccurrenceVisibility::Secret,
    ] {
        for label in [
            SecurityLabel::Public,
            SecurityLabel::Internal,
            SecurityLabel::Secret,
            SecurityLabel::SecretCt,
        ] {
            let mut op = operation("write");
            op.occurrence = occurrence;
            op.domains = vec![access("output", HostAccessMode::Write)];
            let result = profile(
                vec![domain("output", HostDomainKind::Output, label)],
                vec![op],
            );
            assert_eq!(
                result.is_ok(),
                occurrence.label() <= label,
                "{occurrence:?} -> {label:?}"
            );
        }
    }
}

fn codec_fixture() -> HostContractProfile {
    let mut op = operation("op");
    op.params = vec![value(SecurityLabel::Public)];
    op.results = vec![value(SecurityLabel::Public)];
    op.domains = vec![access("state", HostAccessMode::ReadWrite)];
    profile(
        vec![domain(
            "state",
            HostDomainKind::State,
            SecurityLabel::Public,
        )],
        vec![op],
    )
    .unwrap()
}

#[test]
fn decoder_round_trips_and_rejects_every_truncated_prefix_and_trailing_byte() {
    let profile = codec_fixture();
    assert_eq!(
        HostContractProfile::decode(profile.canonical_bytes()),
        Ok(profile.clone())
    );
    for end in 0..profile.canonical_bytes().len() {
        assert!(
            HostContractProfile::decode(&profile.canonical_bytes()[..end]).is_err(),
            "accepted prefix of length {end}"
        );
    }
    let mut trailing = profile.canonical_bytes().to_vec();
    trailing.push(0);
    assert_eq!(
        HostContractProfile::decode(&trailing),
        Err(HostContractError::InvalidEncoding)
    );
}

#[test]
fn decoder_rejects_unknown_tags_and_versions_instead_of_defaulting_to_public() {
    let profile = codec_fixture();
    let prefix = b"SIGIL-HOST-PROFILE\0".len();
    let domain_start = prefix + 4 + 4 + "test-host".len() + 8 + 4;
    let domain_kind = domain_start + 4 + "state".len();
    let occurrence = domain_kind + 3 + 4 + 4 + "host".len() + 4 + "op".len();
    let param_type = occurrence + 1 + 4;
    let result_type = param_type + 2 + 4;
    let mode = result_type + 2 + 4 + 4 + "state".len();
    assert_eq!(mode + 1, profile.canonical_bytes().len());
    for position in [
        domain_kind,
        domain_kind + 1,
        domain_kind + 2,
        occurrence,
        param_type,
        param_type + 1,
        result_type,
        result_type + 1,
        mode,
    ] {
        let mut mutated = profile.canonical_bytes().to_vec();
        mutated[position] = 255;
        assert_eq!(
            HostContractProfile::decode(&mutated),
            Err(HostContractError::InvalidEncoding),
            "unknown discriminant at {position}"
        );
    }
    let mut version = profile.canonical_bytes().to_vec();
    version[prefix..prefix + 4].copy_from_slice(&2_u32.to_le_bytes());
    assert_eq!(
        HostContractProfile::decode(&version),
        Err(HostContractError::UnsupportedVersion(2))
    );
    version[0] ^= 1;
    assert_eq!(
        HostContractProfile::decode(&version),
        Err(HostContractError::InvalidEncoding)
    );
}

#[test]
fn decoder_revalidates_policy_not_just_encoding() {
    let profile = codec_fixture();
    let domain_kind =
        b"SIGIL-HOST-PROFILE\0".len() + 4 + 4 + "test-host".len() + 8 + 4 + 4 + "state".len();
    let occurrence = domain_kind + 3 + 4 + 4 + "host".len() + 4 + "op".len();
    let mut bytes = profile.canonical_bytes().to_vec();
    bytes[occurrence] = OccurrenceVisibility::Secret as u8;
    assert_eq!(
        HostContractProfile::decode(&bytes),
        Err(HostContractError::DomainFlow {
            domain: "state".into()
        })
    );
}

#[test]
fn decoder_checks_counts_before_allocating() {
    let profile = codec_fixture();
    let domain_count = b"SIGIL-HOST-PROFILE\0".len() + 4 + 4 + "test-host".len() + 8;
    let mut bytes = profile.canonical_bytes().to_vec();
    bytes[domain_count..domain_count + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert_eq!(
        HostContractProfile::decode(&bytes),
        Err(HostContractError::TooManyItems)
    );
    bytes[domain_count..domain_count + 4].copy_from_slice(&100_u32.to_le_bytes());
    assert_eq!(
        HostContractProfile::decode(&bytes),
        Err(HostContractError::InvalidEncoding)
    );
}

#[test]
fn decoder_rejects_unsorted_domains_operations_and_accesses() {
    let mut op = operation("aa");
    op.domains = vec![
        access("da", HostAccessMode::Read),
        access("db", HostAccessMode::Write),
    ];
    let profile = profile(
        vec![
            domain("da", HostDomainKind::State, SecurityLabel::Public),
            domain("db", HostDomainKind::State, SecurityLabel::Public),
        ],
        vec![op, operation("bb")],
    )
    .unwrap();
    let bytes = profile.canonical_bytes();
    // All names have equal widths, so exchanging their occurrences does not
    // disturb the wire shape. Renaming only the first/last occurrences tests
    // domain ordering and access ordering independently.
    let occurrences = |name: &[u8]| {
        bytes
            .windows(name.len())
            .enumerate()
            .filter_map(|(i, window)| (window == name).then_some(i))
            .collect::<Vec<_>>()
    };
    let da = occurrences(b"da");
    let db = occurrences(b"db");
    for (left, right) in [
        (da[0], db[0]),
        (da[1], db[1]),
        (occurrences(b"aa")[0], occurrences(b"bb")[0]),
    ] {
        let mut reordered = bytes.to_vec();
        for index in 0..2 {
            reordered.swap(left + index, right + index);
        }
        assert_eq!(
            HostContractProfile::decode(&reordered),
            Err(HostContractError::NonCanonicalEncoding)
        );
    }
}
