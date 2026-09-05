//! WHY THIS TEST EXISTS. The v8 semantic kernel seeds a `@Flow` contract at
//! `@Secret`, so a Public or Internal caller of a taint-polymorphic function
//! would be refused unless the projection says what the type checker verified:
//! one concrete instance per instantiation label a call site resolves to. This
//! pins the mechanism end to end — the recorded call-site labels, the projected
//! `$`-named internal instances, the untouched exported original, and the
//! absence of instances when no caller needs one — so a refactor cannot quietly
//! drop back to the all-Secret projection (which only shows up as a false
//! reject of every stdlib codec caller) or start inventing instances.

use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileOptions, CompilerContext, air, compile_named_module, effect_check, effect_desugar,
    formal, formal_v9, name_resolution, parser, ring_check, taint_check, type_check,
};

/// A polymorphic codec with one internal helper, called from Public and
/// Internal code, and once with a Secret argument that needs no instance.
const SOURCE: &str = r#"
#[ring(outer)] #[trusted]
module flow_instances;
fn helper(x: i64 @Flow) -> i64 @Flow { return x + 1; }
pub fn codec(value: i64 @Flow) -> i64 @Flow { return helper(value); }
pub fn public_caller(value: i64) -> i64 { return codec(value); }
pub fn internal_caller(value: i64 @Internal) -> i64 @Internal { return codec(value); }
fn secret_caller(value: i64 @Secret) -> i64 @Secret { return codec(value); }
"#;

/// The same codec used only at `@Secret`: the original's own seed already
/// covers it, so no instance may be projected.
const SECRET_ONLY: &str = r#"
#[ring(outer)] #[trusted]
module flow_secret_only;
pub fn codec(value: i64 @Flow) -> i64 @Flow { return value; }
fn secret_caller(value: i64 @Secret) -> i64 @Secret { return codec(value); }
"#;

fn declarations(source: &str) -> formal_v9::Declarations {
    let source = SourceFile::new("flow_instances.sigil", source);
    let (ast, parser_diagnostics) = parser::parse(&source);
    assert!(
        parser_diagnostics.is_empty(),
        "fixture must parse: {parser_diagnostics:?}"
    );
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (mut typed, authority_registry, _) =
        type_check::check_with_warnings(&resolved, &CompileOptions::default())
            .expect("fixture must type-check");
    ring_check::check_rings(&typed).expect("fixture must satisfy ring policy");
    effect_check::check_effects(&typed).expect("fixture must satisfy effect policy");
    taint_check::check_taints(&typed).expect("fixture must satisfy taint policy");
    effect_desugar::desugar_effect_handlers(&mut typed);
    effect_check::check_effect_handlers_gated(&typed).expect("fixture lowers effect handlers");
    let raw = air::lower(&typed);
    let bytes = formal::project_v9_declarations(
        &typed,
        &raw,
        &authority_registry,
        &CompilerContext::default(),
    )
    .expect("declarations project");
    formal_v9::decode(&bytes).expect("projected declarations decode")
}

fn root_names(declarations: &formal_v9::Declarations) -> Vec<(String, u8)> {
    declarations
        .roots
        .iter()
        .map(|root| (root.export_name.clone(), root.role))
        .collect()
}

#[test]
fn every_used_instantiation_label_gets_one_internal_instance() {
    let roots = root_names(&declarations(SOURCE));
    let names: Vec<&str> = roots.iter().map(|(name, _)| name.as_str()).collect();
    // The instances exist exactly for the labels call sites resolved to,
    // cascading into the helper the codec calls, and never for @Secret.
    for expected in [
        "$flow_instances__codec$flow$pub",
        "$flow_instances__codec$flow$internal",
        "$flow_instances__helper$flow$pub",
        "$flow_instances__helper$flow$internal",
    ] {
        assert!(
            names.contains(&expected),
            "missing instance {expected}: {names:?}"
        );
    }
    assert!(
        !names.iter().any(|name| name.ends_with("$flow$secret")),
        "a @Secret caller uses the seeded original, never an instance: {names:?}"
    );
    // Instances are internal roots; the exported original keeps its role.
    for (name, role) in &roots {
        if name.contains("$flow$") {
            assert_eq!(*role, 0, "instance {name} must be an internal root");
        }
    }
    let original = roots
        .iter()
        .find(|(name, _)| name == "flow_instances__codec")
        .expect("the exported original root survives");
    assert_ne!(
        original.1, 0,
        "the exported original stays an external root"
    );
}

#[test]
fn a_secret_only_caller_projects_no_instance() {
    let names = root_names(&declarations(SECRET_ONLY));
    assert!(
        names
            .iter()
            .any(|(name, _)| name == "flow_secret_only__codec"),
        "the original root is projected: {names:?}"
    );
    assert!(
        !names.iter().any(|(name, _)| name.contains("$flow$")),
        "no instance without a Public or Internal call site: {names:?}"
    );
}

#[test]
fn the_recorder_resolves_each_call_site_to_the_join_of_its_arguments() {
    let source = SourceFile::new("flow_instances.sigil", SOURCE);
    let (ast, _) = parser::parse(&source);
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (typed, _, _) = type_check::check_with_warnings(&resolved, &CompileOptions::default())
        .expect("fixture must type-check");
    let table = taint_check::flow_call_instantiations(&typed);
    let mut by_context = std::collections::BTreeMap::<String, Vec<String>>::new();
    for ((context, _), label) in &table.sites {
        let key = match context {
            Some((name, label)) => format!("{name}@{label:?}"),
            None => "ordinary".to_owned(),
        };
        by_context
            .entry(key)
            .or_default()
            .push(format!("{label:?}"));
    }
    for labels in by_context.values_mut() {
        labels.sort();
    }
    // Ordinary callers: Public, Internal and Secret calls of `codec`.
    assert_eq!(
        by_context.get("ordinary").map(Vec::as_slice),
        Some(
            [
                "Internal".to_owned(),
                "Public".to_owned(),
                "Secret".to_owned()
            ]
            .as_slice()
        ),
        "{by_context:?}"
    );
    // Inside `codec`, the call to `helper` resolves to the codec's own instantiation.
    for label in ["Public", "Internal", "Secret"] {
        assert_eq!(
            by_context
                .get(&format!("flow_instances::codec@{label}"))
                .map(Vec::as_slice),
            Some([label.to_owned()].as_slice()),
            "{by_context:?}"
        );
    }
}

#[test]
fn public_and_internal_callers_of_a_flow_codec_compile_through_the_gate() {
    compile_named_module("flow_instances.sigil", SOURCE)
        .expect("every instantiation passes the production verifier");
}
