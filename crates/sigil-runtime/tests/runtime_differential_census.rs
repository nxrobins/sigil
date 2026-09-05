//! RT-CENSUS — the runtime-differential census (docs/specs/runtime-differential-census.md).
//!
//! SIGIL ships two hosts: the ephemeral forge (`execute_ephemeral`, fresh Store per call) and
//! the actor runtime (`RuntimeHost`, resident Store + supervision). They share ONE compiler, so
//! every guest-side guarantee is shared by construction — but every guarantee a HOST enforces
//! can drift, and did: `sigil::fuel_decrement` was enforced in the actor runtime and merely
//! advisory in the forge one for the whole life of both, because NO FILE IN THE TREE DROVE BOTH
//! RUNTIMES. PR #582 closed that one cell. This census exists so the CLASS cannot recur.
//!
//! SCOPE — the unit is the HOST IMPORT:
//! (a) Guest-side guarantees (bounds/overflow/`trap()`) lower to `Instruction::Unreachable`
//!     (wasm.rs:681/896/951-962/1746/1778/1796/1933) — identical bytes under either host, so they
//!     CANNOT drift. Excluded on purpose, permanently (AG-RC1), not deferred.
//! (b) Witnesses are hand-written WAT, not SIGIL source. This is the forge's STATED threat model
//!     ("a hand-written or hostile module", ephemeral.rs:42-44) and it makes the census a claim
//!     about the HOSTS rather than about what the emitter happens to emit today — the exact
//!     property MI-FUEL lacked. It also dissolves the ABI problem: the actor runtime takes a
//!     hand-built `RuntimeModuleSpec` + raw bytes (runtime.rs:208), `init_export: None` is legal
//!     (runtime.rs:329-331), and a zero-param handler never reaches the payload width table
//!     (runtime.rs:1042-1049) — so M005/M006 and the actor payload restrictions are IRRELEVANT
//!     here; they constrain SIGIL source, and this file has none.
//! (c) `Completed` is compared at the CONSTRUCTOR level only: `drain_messages` discards each
//!     handler's i64 (runtime.rs:316), so return-value fidelity is out of scope — stated, not
//!     implied.
//! (d) `FuelExhausted` is normalized WITHOUT its payload: `ToolError::FuelExhausted { consumed:
//!     fuel_budget }` (ephemeral.rs:1015-1019) is a known fiction — the refused decrement was
//!     never applied, so the honest figure is `fuel_budget - fuel_remaining` — and the actor twin
//!     carries no consumption figure at all.
#![deny(clippy::wildcard_enum_match_arm)]

use sigil_abi::RuntimeTypeSpec;
use sigil_runtime::capability::CapabilityId;
use sigil_runtime::grants::IoGrants;
use sigil_runtime::{
    RuntimeActorSpec, RuntimeError, RuntimeHandlerSpec, RuntimeHost, RuntimeImportSpec,
    RuntimeModuleSpec, ToolError, ToolResult,
};

// ── the verdict lattice ──────────────────────────────────────────────────────────────────
// Deliberately coarse: it names WHAT the host decided, never how it phrased it. String-sniffing
// (`format!("{e}").contains("fuel")`, harness.rs:124-136) structurally cannot tell saturate from
// trap — which is precisely how the fuel divergence survived.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum VerdictClass {
    Completed,
    FuelExhausted,
    GuestTrap,
    HostRejected,
    NoEntry,
}

/// TOTAL over `ToolError`'s 3 variants (ephemeral.rs:68-72). A new variant fails to COMPILE here
/// until classified — the walker_fence precedent (PR #558).
fn classify_tool(r: Result<ToolResult, ToolError>) -> VerdictClass {
    match r {
        Ok(_) => VerdictClass::Completed,
        Err(ToolError::FuelExhausted { .. }) => VerdictClass::FuelExhausted,
        Err(ToolError::Trapped { .. }) => VerdictClass::GuestTrap,
        Err(ToolError::NoEntryPoint) => VerdictClass::NoEntry,
    }
}

/// TOTAL over `RuntimeError`'s 15 variants (runtime.rs:29-65). Same fence.
fn classify_actor_err(e: RuntimeError) -> VerdictClass {
    match e {
        RuntimeError::FuelExhausted { .. } => VerdictClass::FuelExhausted,
        // PPS-4: persistent-heap exhaustion is a RESOURCE trap like fuel — the
        // guest hit a host-enforced budget, not a host rejection of its shape.
        RuntimeError::PersistentHeapExhausted { .. } => VerdictClass::FuelExhausted,
        RuntimeError::Wasm { .. } => VerdictClass::GuestTrap,
        RuntimeError::MissingExport(_) => VerdictClass::NoEntry,
        RuntimeError::NotBootstrapped
        | RuntimeError::UnknownActor(_)
        | RuntimeError::UnknownActorType(_)
        | RuntimeError::UnknownHandler { .. }
        | RuntimeError::InvalidActorRef(_)
        | RuntimeError::InvalidCapabilityRef(_)
        | RuntimeError::NoActiveActor(_)
        | RuntimeError::MissingMemoryExport
        | RuntimeError::UnsupportedSpawnCaps { .. }
        | RuntimeError::UnsupportedSignature { .. }
        | RuntimeError::Capability { .. }
        | RuntimeError::QueueFull { .. } => VerdictClass::HostRejected,
    }
}

// ── the fail-closed fence on the actor `sigil` import set ────────────────────────────────
/// sigil-abi/src/lib.rs:31-41 is the single source of truth for the actor-side `sigil` imports,
/// and runtime.rs:424-532 names every import through it. This TOTAL DESTRUCTURE (no `..`) makes a
/// 9th field fail to COMPILE until it is classified here. Zero TCB change.
///
/// HONEST LIMIT: this fences the `sigil` namespace ONLY. The nine `ffi` imports
/// (ephemeral.rs:1205-1615) are forge-only and have no `RuntimeImportSpec` analogue, so their
/// fence would be a const list + count — weaker by construction (AG-RC4). Said, not pretended.
#[test]
fn rtc_import_set_is_fenced() {
    let RuntimeImportSpec {
        module,
        fuel_decrement,
        send,
        ask,
        spawn,
        alloc,
        cap_restrict,
        cap_split,
        cap_mint,
        alloc_persistent,
    } = RuntimeImportSpec::phase_one();

    assert_eq!(module, "sigil");
    // CENSUSED (slice 1): a row exists below.
    assert_eq!(fuel_decrement, "fuel_decrement");
    // CENSUSED (RTC-NOOP slice 1): the forge now TRAPS all six (ephemeral.rs; was: SILENT
    // no-ops returning 0). Enforced by `rtc_forge_traps_actor_and_cap_ops` below — a stub that
    // reverts to a silent no-op reds it. The full two-host differential (the actor host's
    // response to a hostile hand-WAT send/spawn/cap call) is the documented follow-on; the
    // M011 compile-time gate rejects actor machinery in a tool before either host runs.
    assert_eq!(send, "send");
    assert_eq!(ask, "ask");
    assert_eq!(spawn, "spawn");
    assert_eq!(cap_restrict, "cap_restrict");
    assert_eq!(cap_split, "cap_split");
    assert_eq!(cap_mint, "cap_mint");
    // CENSUSED (slice 2): the `alloc/negative` row below. Both hosts now route their guest
    // `i32` size through the AllocBytes sign check (alloc_size.rs), so a negative size is a
    // GuestTrap on both — where PRE-slice-2 the actor `alloc(-1)` panicked the host process on
    // `(size + 7)` overflow (runtime.rs) while the forge rejected cleanly.
    assert_eq!(alloc, "alloc");
    // CENSUSED (AGG2b-1): the persistent-heap allocation channel. ACTOR-ONLY — the forge/tool host
    // is single-shot and has no persistent floor, so there is no two-host convergent Probe row for
    // it (like the actor/cap ops the forge traps). Its floor-raise semantics are exercised by
    // `agg2b_alloc_persistent::alloc_persistent_survives_reset_vs_transient_clobber` (a hand-WAT
    // actor differential: a persistent buffer survives the AL-2 reset + a clobber; a transient one
    // does not).
    assert_eq!(alloc_persistent, "alloc_persistent");
}

// ── fixtures: hand-written WAT, identical guest logic, one per host ABI ───────────────────
/// The host import a row exercises. Each variant knows how to declare its import and build the
/// call sequence for BOTH host WATs, so one row table covers every import with the correct
/// signature. Adding an import = adding a variant (the census grows by declaration).
#[derive(Debug, Clone, Copy)]
enum Probe {
    /// `fuel_decrement(i32)` — returns nothing.
    FuelDecrement,
    /// `alloc(i32) -> i32` — returns a pointer, dropped.
    Alloc,
}

impl Probe {
    fn import_decl(self) -> &'static str {
        match self {
            Probe::FuelDecrement => r#"(import "sigil" "fuel_decrement" (func $f (param i32)))"#,
            Probe::Alloc => r#"(import "sigil" "alloc" (func $f (param i32) (result i32)))"#,
        }
    }

    fn call_seq(self, amount: i32) -> String {
        match self {
            Probe::FuelDecrement => format!("(i32.const {amount}) (call $f)"),
            Probe::Alloc => format!("(i32.const {amount}) (call $f) (drop)"),
        }
    }
}

fn forge_wat(probe: Probe, amount: i32) -> Vec<u8> {
    // `memory` + `BUMP_PTR` are required unconditionally even for empty input
    // (ephemeral.rs:206-223); `tool__tool_main` is the exact-match entry (ephemeral.rs:1812).
    let src = format!(
        r#"(module
  {import_decl}
  (memory (export "memory") 1)
  (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
  (func (export "tool__tool_main") (param i64 i64) (result i64)
    {call_seq}
    (i64.const 0)))"#,
        import_decl = probe.import_decl(),
        call_seq = probe.call_seq(amount),
    );
    wat::parse_str(&src).expect("forge WAT parses")
}

fn actor_wat(probe: Probe, amount: i32) -> Vec<u8> {
    let src = format!(
        r#"(module
  {import_decl}
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    {call_seq}
    (i64.const 0)))"#,
        import_decl = probe.import_decl(),
        call_seq = probe.call_seq(amount),
    );
    wat::parse_str(&src).expect("actor WAT parses")
}

/// BUDGET is identical on both hosts and ONE dispatch is driven, with a single overrunning
/// decrement — so there is no loop, and the fuel-LIFETIME confound (per-actor monotonic,
/// actor.rs:26/fuel.rs:20-27, vs per-call, ephemeral.rs:786-788) cannot arise. This is exactly
/// what the WAT lane buys that a SIGIL-source fixture could not.
const BUDGET: u64 = 128;

fn actor_spec() -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "census".to_owned(),
        fuel_budget: BUDGET,
        imports: RuntimeImportSpec::phase_one(),
        actors: vec![RuntimeActorSpec {
            name: "Main".to_owned(),
            actor_type_id: 0,
            is_entry: true,
            init_export: None, // legal: invoke_actor_init early-returns (runtime.rs:329-331)
            init_params: vec![],
            handlers: vec![RuntimeHandlerSpec {
                name: "Start".to_owned(),
                handler_id: 0,
                export_name: "Main__Start".to_owned(),
                params: vec![], // zero-param: never reaches the payload width table
                ret: RuntimeTypeSpec::I64,
            }],
            state_layout: vec![],
            state_size: 0,
            init_replay_safe: false,
        }],
    }
}

fn forge_verdict(probe: Probe, amount: i32) -> VerdictClass {
    classify_tool(sigil_runtime::execute_ephemeral(
        &forge_wat(probe, amount),
        b"",
        BUDGET,
        &IoGrants::none(),
    ))
}

fn actor_verdict(probe: Probe, amount: i32) -> VerdictClass {
    let spec = actor_spec();
    let mut host = RuntimeHost::new(spec.fuel_budget);
    let v = match host.bootstrap(&spec, &actor_wat(probe, amount)) {
        Err(e) => classify_actor_err(e),
        // bootstrap auto-enqueues Start (runtime.rs:267-274).
        Ok(_) => match host.drain_messages(1) {
            Ok(_) => VerdictClass::Completed,
            Err(e) => classify_actor_err(e),
        },
    };
    // The entry actor is pinned SupervisionStrategy::Stop (runtime.rs:248) — ASSERTED, not
    // assumed, so a restart can never swallow a verdict.
    assert!(
        host.audit_log().events().iter().all(|e| !matches!(
            e.kind,
            sigil_runtime::audit::AuditEventKind::ActorRestarted { .. }
        )),
        "a restart would swallow the verdict; the entry actor must be Stop-supervised"
    );
    v
}

// ── the census ───────────────────────────────────────────────────────────────────────────
struct Row {
    label: &'static str,
    /// The host import this row exercises.
    probe: Probe,
    /// The CONTROL argument: benign, must Complete on both. Doubles as the neutralized twin.
    control: i32,
    /// The WITNESS argument: the one under test.
    witness: i32,
    expect: VerdictClass,
}

const CENSUS: &[Row] = &[
    Row {
        label: "fuel_decrement/in_budget",
        probe: Probe::FuelDecrement,
        control: 1,
        witness: 1,
        expect: VerdictClass::Completed,
    },
    Row {
        label: "fuel_decrement/overrun",
        probe: Probe::FuelDecrement,
        control: 1,
        witness: 200,
        // The tree's ONLY cross-runtime parity claim (wasm.rs:75-78) was a COMMENT. This is it
        // as a test. Forge: ephemeral.rs:1104-1110 refuses + traps -> classified :1015-1019.
        // Actor: runtime.rs:586-588 consume_fuel err -> RuntimeError::FuelExhausted.
        expect: VerdictClass::FuelExhausted,
    },
    Row {
        label: "fuel_decrement/negative",
        probe: Probe::FuelDecrement,
        control: 1,
        witness: -8,
        expect: VerdictClass::GuestTrap,
    },
    Row {
        label: "alloc/negative",
        probe: Probe::Alloc,
        control: 16,
        witness: -1,
        // RTC slice 2: BEFORE this slice the actor `alloc(-1)` PANICKED the host
        // (runtime.rs `(size + 7)` overflow) while the forge rejected cleanly — a divergence
        // that could not even be a census row without crashing CI. The AllocBytes newtype
        // (alloc_size.rs) now routes BOTH hosts through one sign check, so both reject a
        // negative size as a GuestTrap. The row's red-first is the pre-fix probe (a panic),
        // recorded in the design doc rather than as a re-runnable mutant, because a missing
        // sign check crashes rather than dissents.
        expect: VerdictClass::GuestTrap,
    },
];

#[test]
fn rtc_runtime_differential_census() {
    let mut failures: Vec<String> = Vec::new();
    let mut cells_executed = 0usize;
    let mut forge_seen = std::collections::BTreeSet::new();
    let mut actor_seen = std::collections::BTreeSet::new();

    for row in CENSUS {
        let fw = forge_verdict(row.probe, row.witness);
        let aw = actor_verdict(row.probe, row.witness);
        cells_executed += 2;
        forge_seen.insert(fw);
        actor_seen.insert(aw);

        // ANTI-VACUITY 1 — the neutralized twin. A row whose witness cannot be distinguished
        // from its control proves NOTHING. This is the direct machine-check against
        // harness.rs:130-133's `Ok(_) => { // Fuel may not have been exhausted — acceptable }`,
        // which passes a fuel test that never exhausted. Rows whose witness IS the control are
        // pure controls and are exempt by construction.
        if row.control != row.witness {
            let fc = forge_verdict(row.probe, row.control);
            let ac = actor_verdict(row.probe, row.control);
            if fc != VerdictClass::Completed || ac != VerdictClass::Completed {
                failures.push(format!(
                    "{}: CONTROL must Complete on both (forge={fc:?} actor={ac:?}) — the row's \
                     witness is not isolated",
                    row.label
                ));
            }
            if fc == fw && ac == aw {
                failures.push(format!(
                    "{}: VACUOUS — witness verdicts equal the control's on BOTH hosts \
                     (forge={fw:?} actor={aw:?}); this row cannot fail and proves nothing",
                    row.label
                ));
            }
        }

        let expected = row.expect;
        if fw != expected || aw != expected {
            failures.push(format!(
                "{}: expected BOTH={expected:?}, got forge={fw:?} actor={aw:?} — the hosts \
                 DRIFTED on a guarantee that was convergent",
                row.label
            ));
        }
    }

    // The row-level report comes FIRST: it names the offending row, the guarantee, and both
    // verdicts. The guards below are backstops for what no row thought to check — if a guard
    // fired first it would mask the specific diagnosis with a generic one. (Verified against the
    // pre-#582 mutant: the row report says "the hosts DRIFTED on a guarantee that was
    // convergent"; the anti-stub only says "every row returned {Completed}".)
    assert!(
        failures.is_empty(),
        "runtime-differential census ({} row(s)):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );

    // ANTI-VACUITY 2 — a skipped cell is arithmetically visible.
    assert_eq!(
        cells_executed,
        2 * CENSUS.len(),
        "every row must execute on BOTH hosts"
    );

    // ANTI-VACUITY 3 — per-COLUMN anti-stub. Catches a column that returns ONE verdict for
    // everything: a stubbed driver (every row failing to instantiate) or a stubbed HOST. The
    // pre-#582 forge was exactly the latter — it could not fail, so it answered `Completed` to
    // every row. Per-column, not global.
    assert!(
        forge_seen.len() >= 2,
        "the forge column is a stub: every row returned {forge_seen:?} — this column cannot \
         distinguish a violation from a control, so no row through it proves anything"
    );
    assert!(
        actor_seen.len() >= 2,
        "the actor column is a stub: every row returned {actor_seen:?} — this column cannot \
         distinguish a violation from a control, so no row through it proves anything"
    );
}

// ── the no-silent-no-op invariant ────────────────────────────────────────────────────────
// The six actor/capability `sigil` imports (send/ask/spawn/cap_restrict/cap_split/cap_mint) used
// to be registered by the forge as SILENT no-ops returning 0 — the one outcome the security
// model cannot afford, because it is the only failure mode with NO signal on any channel. They
// now TRAP. This test encodes the invariant: a WAT tool that calls any of the six must trap
// (GuestTrap), never silently Complete. A future forge stub that goes back to a silent no-op —
// or a NEW `sigil` import that lands as one — reds here.
//
// Scope: this asserts the forge disposition. The actor host implements these operations; its
// hostile-input shape checks are covered separately below.
struct ForgeOp {
    name: &'static str,
    /// wasm param types of the import.
    params: &'static str,
    /// wasm result type, or "" for none.
    result: &'static str,
    /// the operand-push sequence that feeds a call to it.
    args: &'static str,
}

const FORGE_TRAP_OPS: &[ForgeOp] = &[
    ForgeOp {
        name: "send",
        params: "i32 i32 i32 i32",
        result: "",
        args: "(i32.const 0)(i32.const 0)(i32.const 0)(i32.const 0)",
    },
    ForgeOp {
        name: "ask",
        params: "i32 i32 i32 i32 i64",
        result: "i64",
        args: "(i32.const 0)(i32.const 0)(i32.const 0)(i32.const 0)(i64.const 0)",
    },
    ForgeOp {
        name: "spawn",
        params: "i32 i32 i32 i32 i32",
        result: "i32",
        args: "(i32.const 0)(i32.const 0)(i32.const 0)(i32.const 0)(i32.const 0)",
    },
    ForgeOp {
        name: "cap_restrict",
        params: "i32 i32",
        result: "i32",
        args: "(i32.const 0)(i32.const 0)",
    },
    ForgeOp {
        name: "cap_split",
        params: "i32 i64",
        result: "i32",
        args: "(i32.const 0)(i64.const 0)",
    },
    ForgeOp {
        name: "cap_mint",
        params: "",
        result: "i32",
        args: "",
    },
];

#[test]
fn rtc_forge_traps_actor_and_cap_ops() {
    let mut failures: Vec<String> = Vec::new();
    for op in FORGE_TRAP_OPS {
        let import_res = if op.result.is_empty() {
            String::new()
        } else {
            format!("(result {})", op.result)
        };
        // Drop the import's result (if any) so the tool body is well-typed and returns i64 0.
        let drop_res = if op.result.is_empty() { "" } else { "(drop)" };
        let src = format!(
            r#"(module
  (import "sigil" "{name}" (func $f (param {params}) {import_res}))
  (memory (export "memory") 1)
  (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
  (func (export "tool__tool_main") (param i64 i64) (result i64)
    {args} (call $f) {drop_res}
    (i64.const 0)))"#,
            name = op.name,
            params = op.params,
            args = op.args,
        );
        let wasm = wat::parse_str(&src).expect("forge WAT parses");
        let v = classify_tool(sigil_runtime::execute_ephemeral(
            &wasm,
            b"",
            128,
            &IoGrants::none(),
        ));
        if v != VerdictClass::GuestTrap {
            failures.push(format!(
                "`{}`: the forge must TRAP a tool that calls it, got {v:?} — a silent no-op is \
                 the one outcome with no signal on any channel",
                op.name
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "no-silent-no-op invariant ({} op(s)):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

// ── RTC-NOOP slice 3: the actor host rejects hostile args to the six ops cleanly ──────────────
// The twin of the FORGE side above. The six ops are Drift-by-construction between the hosts — the
// forge TRAPS all six, the actor IMPLEMENTS them — so this is NOT a convergence row. What it pins
// is the ACTOR side's input-shape ROBUSTNESS: a hostile hand-WAT calling an arg-taking op with
// adversarial args (a bad actor/cap ref, an out-of-bounds payload, or a caps_len that overflows an
// i32 byte length) gets a clean RuntimeError — NEVER a host-process panic (the alloc-panic class,
// RTC slice 2, which a panic here would reproduce by aborting the test) and NEVER a silent
// wrong-completion (the caps_len truncation this slice fixed).
//
// Threat model: this asserts only the defense-in-depth
// SHAPE validation the actor runtime performs. Cap-OWNERSHIP is trusted to the compiler's
// C-checks/Z3 — a hostile WAT forging an unowned cap into `spawn`'s caps array is out of the actor
// threat model (the actor runtime runs a compiler-verified project, unlike the lone-untrusted-tool
// forge). `cap_mint` takes no args — nothing to make hostile — and rides the forge trap test only.
struct HostileArgOp {
    label: &'static str,
    import_decl: &'static str,
    call_seq: &'static str,
}

const HOSTILE_ARG_OPS: &[HostileArgOp] = &[
    HostileArgOp {
        label: "send/bad_target",
        import_decl: r#"(import "sigil" "send" (func $f (param i32 i32 i32 i32)))"#,
        call_seq: "(i32.const -1) (i32.const 0) (i32.const 0) (i32.const 0) (call $f)",
    },
    HostileArgOp {
        label: "send/oob_payload",
        import_decl: r#"(import "sigil" "send" (func $f (param i32 i32 i32 i32)))"#,
        call_seq: "(i32.const 0) (i32.const 0) (i32.const 0) (i32.const 100000) (call $f)",
    },
    HostileArgOp {
        label: "ask/bad_target",
        import_decl: r#"(import "sigil" "ask" (func $f (param i32 i32 i32 i32 i64) (result i64)))"#,
        call_seq: "(i32.const 2147483647) (i32.const 0) (i32.const 0) (i32.const 0) (i64.const 5) (call $f) (drop)",
    },
    HostileArgOp {
        label: "spawn/unknown_type",
        import_decl: r#"(import "sigil" "spawn" (func $f (param i32 i32 i32 i32 i32) (result i32)))"#,
        call_seq: "(i32.const 999) (i32.const 0) (i32.const 0) (i32.const 0) (i32.const 0) (call $f) (drop)",
    },
    // The cast-fix pin (RED-FIRST): a caps_len of 2^30 makes `caps_len * 4` overflow an i32 byte
    // length. Before the fix this SILENTLY read 0 caps and the spawn Completed; now it fails loud.
    HostileArgOp {
        label: "spawn/wrapping_caps_len",
        import_decl: r#"(import "sigil" "spawn" (func $f (param i32 i32 i32 i32 i32) (result i32)))"#,
        call_seq: "(i32.const 0) (i32.const 0) (i32.const 1073741824) (i32.const 0) (i32.const 0) (call $f) (drop)",
    },
    HostileArgOp {
        label: "cap_restrict/unowned",
        import_decl: r#"(import "sigil" "cap_restrict" (func $f (param i32 i32) (result i32)))"#,
        call_seq: "(i32.const 12345) (i32.const 0) (call $f) (drop)",
    },
    HostileArgOp {
        label: "cap_split/unowned_neg_amount",
        import_decl: r#"(import "sigil" "cap_split" (func $f (param i32 i64) (result i32)))"#,
        call_seq: "(i32.const 12345) (i64.const -1) (call $f) (drop)",
    },
];

fn drive_actor_hostile(op: &HostileArgOp) -> Result<(), RuntimeError> {
    let src = format!(
        r#"(module
  {import_decl}
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    {call_seq}
    (i64.const 0)))"#,
        import_decl = op.import_decl,
        call_seq = op.call_seq,
    );
    let wasm = wat::parse_str(&src).expect("actor WAT parses");
    // A generous budget so an op's own validation error surfaces rather than FuelExhausted masking
    // it (the census's 128-fuel spec is tuned for the overrun rows, not these early-erroring ops).
    let mut spec = actor_spec();
    spec.fuel_budget = 4096;
    let mut host = RuntimeHost::new(spec.fuel_budget);
    host.bootstrap(&spec, &wasm)?;
    host.drain_messages(1).map(|_| ())
}

#[test]
fn rtc_actor_ops_reject_hostile_args() {
    let mut failures: Vec<String> = Vec::new();
    for op in HOSTILE_ARG_OPS {
        // Reaching the match at all proves the host did not panic (a panic aborts the process).
        match drive_actor_hostile(op) {
            Err(_) => {} // a clean rejection — the required outcome
            Ok(()) => failures.push(format!(
                "`{}`: hostile args must be rejected cleanly, got Ok — a silent wrong-completion",
                op.label
            )),
        }
    }
    assert!(
        failures.is_empty(),
        "actor hostile-arg robustness ({} op(s)):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

#[test]
fn cap_split_host_rejects_negative_before_conversion_without_mutation() {
    let source = r#"(module
  (import "sigil" "cap_split" (func $split (param i32 i64) (result i32)))
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64)
    (i32.const 0)
    (i64.const -1)
    (call $split)
    (drop)
    (i64.const 0)))"#;
    let wasm = wat::parse_str(source).expect("negative split probe parses");
    let mut spec = actor_spec();
    spec.fuel_budget = 4096;
    let mut host = RuntimeHost::new(spec.fuel_budget);
    host.bootstrap(&spec, &wasm).expect("probe bootstraps");

    let error = host
        .drain_messages(1)
        .expect_err("the host must independently reject a negative signed quantity");
    assert!(
        matches!(error, RuntimeError::Capability { ref message }
            if message.contains("non-negative") && message.contains("-1")),
        "unexpected rejection: {error:?}"
    );
    assert_eq!(
        host.capability_table().len(),
        1,
        "a rejected negative split must not allocate a wrapped child"
    );
    assert_eq!(
        host.capability_table().fuel_units(CapabilityId(0)),
        Ok(4096),
        "a rejected negative split must leave the parent balance unchanged"
    );
}
