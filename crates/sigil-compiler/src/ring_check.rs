//! Ring boundary checker.
//!
//! Enforces the two-ring trust model:
//! - R001: Outer ring cannot own capabilities (only borrow via grants)
//! - R002: Capability references cannot escape outer ring functions
//! - R003: Inner ring cannot call extern functions (forward-looking for 2E)
//! - R004: Cross-ring direct calls are forbidden (must use grants; emitted by
//!   `type_check::expressions::calls` at the SOURCE call site, not here)
//! - R007: a lowered call crosses the ring boundary although no source call did
//!   (`check_air_ring_placement`, below — an AIR-level gate, not a source one)

use crate::{
    air::{AirProgram, AirStmt},
    ast::Ring,
    diagnostics::{Diagnostic, codes},
    type_check::{Type, TypedModule, TypedProgram, TypedStmt},
    typed_ast::{TypedExpr, TypedExprKind},
};

pub fn check_rings(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();

    for module in &program.modules {
        check_module_ring_rules(module, program, &mut diagnostics);
    }

    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

/// AIR-level ring gate (P2B-TWORING round 2): every `AirStmt::Call` must name a callee in the
/// CALLER's ring.
///
/// R004 forbids cross-ring calls in SOURCE, but the AIR a two-ring program lowers to can still
/// contain one, because `type_check` files every monomorphized generic instance under
/// `modules[0]` (see the "Drain monomorphized outputs" comment in `type_check/mod.rs`: the
/// re-homing fix was deliberately narrowed to lambda-lifted closures, whose destination is not
/// pinned by the SH-MONO differential). An instance therefore inherits the FIRST module's ring
/// rather than its definer's, so a generic defined and called inside one ring of a two-ring
/// program lowers to a call from that ring into the other one — with no cross-ring call
/// anywhere in the source.
///
/// Wasm emission numbers each ring's functions by position in ITS slice, so it cannot encode
/// such a call at all: before this gate it panicked (an ICE on a program `main` compiles), and
/// before the per-ring index map it silently emitted a neighbour's index. FAIL DIRECTION: this
/// gate rejects at compile time (a real, source-anchored diagnostic) rather than emit an
/// artifact, so the residual is a REFUSED compile, never a misdirected call. It is a
/// conservative over-approximation only in the sense that a future fix routing instances to
/// their definer would make it unreachable; it never accepts a cross-ring call. Since the typed
/// checks govern an instance by the meet of its definer and resolving scopes (BUG-5b) rather
/// than by its filing module, this gate also refuses instances those checks ACCEPT whenever the
/// filing ring differs from a caller's — kept, by the author's decision of 2026-10-01, until
/// instances are emitted into their governing ring (issue #768).
///
/// SCOPE: direct calls. A funcref (a closure captured across the boundary) is already fail-closed
/// by emission — each module's `call_indirect` table spans the whole program's ids but leaves the
/// other ring's slots uninitialized, so an out-of-ring funcref TRAPS instead of landing on a
/// same-signature neighbour.
///
/// Single-ring programs cannot trip it (one ring, every callee in it), which covers the whole
/// self-hosted surface and every parity fixture except the two-ring ones; of those,
/// `tests/compile/ring_two_ring_inner_first.sigil` must pass it and
/// `tests/reject/ring_generic_instance_other_ring.sigil` must fail it with exactly this code.
///
/// WHY HERE, and not in the typed `check_rings` pass: the typed pass sees source modules, but
/// the defect is a property of where LOWERING put an instance. Predicting that from the typed
/// program would re-derive `type_check`'s filing rule in a second place (a copy that drifts the
/// day the rule changes, e.g. when instances are re-homed to their definer); checking the AIR
/// `emit` actually receives needs no prediction, so the emitter's ICE is unreachable from the
/// pipeline by construction rather than by agreement between two passes.
pub fn check_air_ring_placement(program: &AirProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    for caller in &program.functions {
        for block in &caller.blocks {
            for stmt in &block.stmts {
                let AirStmt::Call { func, .. } = stmt else {
                    continue;
                };
                // A `FuncId` out of range is an emitter ICE, not a ring verdict: leave it to
                // `wasm.rs`'s backstop rather than report a ring error we cannot substantiate.
                let Some(callee) = program.functions.get(func.0 as usize) else {
                    continue;
                };
                if callee.ring == caller.ring {
                    continue;
                }
                diagnostics.push(Diagnostic::error(
                    codes::R007,
                    format!(
                        // States only what the gate checked (the two rings). The CAUSE — a
                        // monomorphized generic instance filed under the first module — is
                        // the registry hint's job, because this walk observes rings, not
                        // provenance, and naming a cause it did not establish would be a
                        // guess dressed as a finding.
                        "`{}` ({}) calls `{}` ({}): the call crosses the ring boundary \
                         after lowering, so it has no emittable index",
                        caller.name,
                        ring_word(caller.ring),
                        callee.name,
                        ring_word(callee.ring),
                    ),
                    // The `Call` statement's own span moves with the memory/fuel rewrites that
                    // run before emission; the caller's declaration span is stable and always
                    // present for a lowered function (synthetic only for hand-built AIR).
                    Some(caller.def_span),
                ));
            }
        }
    }

    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

/// The word a ring is spelled with in a diagnostic (`#[ring(outer)]` / the default inner ring).
fn ring_word(ring: Ring) -> &'static str {
    match ring {
        Ring::Inner => "inner ring",
        Ring::Outer => "outer ring",
    }
}

fn check_module_ring_rules(
    filing: &TypedModule,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for function in &filing.functions {
        // BUG-5b: a monomorphized instance is FILED under `modules[0]`, so
        // keying its ring rules on the filing module let an outer-ring first
        // module carry an inner-ring generic's instance past R003. Round 3: the
        // re-checked body's names resolve in the caller's scope as well as the
        // definer's, so fails CLOSED: each ring's restrictions apply when ANY
        // governing module (definer or resolving scope) is in that ring — an
        // instance straddling both rings gets both sets. Non-instances resolve
        // to `filing` itself, exactly one ring.
        let governing = program.governing_context(filing, function);
        if governing.outer_rules {
            // R001: No cap ownership in outer ring
            for param in &function.params {
                if is_owned_cap(&param.ty) {
                    diagnostics.push(Diagnostic::error(
                        codes::R001,
                        format!(
                            "outer ring cannot own capabilities: parameter `{}` has type `{}`",
                            param.name,
                            render_type_brief(&param.ty)
                        ),
                        Some(function.span),
                    ));
                }
            }
            if is_owned_cap(&function.ret) {
                diagnostics.push(Diagnostic::error(
                    codes::R001,
                    format!(
                        "outer ring cannot own capabilities: function `{}` returns `{}`",
                        function.name,
                        render_type_brief(&function.ret)
                    ),
                    Some(function.span),
                ));
            }

            // R002: Cap references cannot be returned from outer functions
            if contains_cap_ref(&function.ret) {
                diagnostics.push(Diagnostic::error(
                    codes::R002,
                    format!(
                        "capability reference cannot be returned from outer ring function `{}`",
                        function.name
                    ),
                    Some(function.span),
                ));
            }

            // Walk body for cap ownership in let bindings
            check_outer_body(&function.body.statements, diagnostics);
        }
        if governing.inner_rules {
            // R003: Inner ring cannot call extern functions. FFI is the
            // privileged trust boundary — it can only be invoked from
            // outer-ring code (where R001/R002 quarantine cap state).
            // Inner-ring code is the safe-by-construction policy tier
            // and must reach FFI only through a `grant(&cap, fn(ref) -> ...)`
            // across the ring boundary, never via a direct extern call.
            //
            // Step 24 of the supremum loop (axis-6 second touch) made this
            // check real. Before, the ring_check pass was a no-op for
            // inner-ring modules ("forward-looking — no extern syntax
            // exists yet"), and an inner-ring module could declare AND
            // call `extern "C" fn foo() ! { FFI, Unsafe }` cleanly.
            check_inner_body_for_externs(&function.body.statements, diagnostics);
        }
    }
}

fn check_inner_body_for_externs(stmts: &[TypedStmt], diagnostics: &mut Vec<Diagnostic>) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Let(s) => check_expr_for_externs(&s.value, diagnostics),
            TypedStmt::Assign(s) => check_expr_for_externs(&s.value, diagnostics),
            TypedStmt::Expr(s) => check_expr_for_externs(&s.expr, diagnostics),
            TypedStmt::Return(s) => {
                if let Some(value) = &s.value {
                    check_expr_for_externs(value, diagnostics);
                }
            }
            // break/continue call no externs.
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
            TypedStmt::If(s) => {
                check_expr_for_externs(&s.condition, diagnostics);
                check_inner_body_for_externs(&s.then_branch.statements, diagnostics);
                check_inner_body_for_externs(&s.else_branch.statements, diagnostics);
            }
            TypedStmt::While(s) => {
                check_expr_for_externs(&s.condition, diagnostics);
                check_inner_body_for_externs(&s.body.statements, diagnostics);
            }
            TypedStmt::ForIn(s) => {
                check_expr_for_externs(&s.iterable, diagnostics);
                check_inner_body_for_externs(&s.body, diagnostics);
            }
            TypedStmt::ForRange(s) => {
                check_expr_for_externs(&s.start, diagnostics);
                check_expr_for_externs(&s.end, diagnostics);
                check_inner_body_for_externs(&s.body, diagnostics);
            }
            TypedStmt::Match(s) => {
                check_expr_for_externs(&s.scrutinee, diagnostics);
                for arm in &s.arms {
                    if let Some(guard) = &arm.guard {
                        check_expr_for_externs(guard, diagnostics);
                    }
                    check_inner_body_for_externs(&arm.body.statements, diagnostics);
                }
            }
        }
    }
}

fn check_expr_for_externs(expr: &TypedExpr, diagnostics: &mut Vec<Diagnostic>) {
    if let TypedExprKind::ExternCall(call) = &expr.kind {
        diagnostics.push(Diagnostic::error(
            codes::R003,
            format!(
                "inner-ring code cannot call extern function `{}` directly — FFI is reachable only from `#[ring(outer)] #[trusted]` modules, or via `grant(&cap, fn(ref) -> ...)` across the ring boundary",
                call.extern_name
            ),
            Some(expr.span),
        ));
    }

    // Recurse into sub-expressions. We only need to find ExternCall;
    // every other kind is traversed for completeness.
    match &expr.kind {
        TypedExprKind::Call(c) => {
            for arg in &c.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        // HOF / N9-HOF: explicit IndirectCall arm. Closure calls
        // don't cross ring boundaries (the callee is a local
        // variable bound at the construction site, which is in
        // the current ring by definition). We only recurse into
        // args to catch any extern calls nested in the args.
        TypedExprKind::IndirectCall(c) => {
            for arg in &c.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        TypedExprKind::ExternCall(c) => {
            for arg in &c.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        TypedExprKind::Intrinsic(i) => {
            for arg in &i.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        TypedExprKind::ResultCtor(r) => {
            check_expr_for_externs(&r.value, diagnostics);
        }
        TypedExprKind::EnumConstruct(e) => {
            for f in &e.fields {
                check_expr_for_externs(f, diagnostics);
            }
        }
        TypedExprKind::Try(t) => {
            check_expr_for_externs(&t.value, diagnostics);
        }
        TypedExprKind::Send(s) => {
            for arg in &s.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &a.args {
                check_expr_for_externs(arg, diagnostics);
            }
            check_expr_for_externs(&a.timeout, diagnostics);
        }
        TypedExprKind::Spawn(s) => {
            for arg in &s.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        TypedExprKind::Binary(b) => {
            check_expr_for_externs(&b.lhs, diagnostics);
            check_expr_for_externs(&b.rhs, diagnostics);
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, value) in &r.fields {
                check_expr_for_externs(value, diagnostics);
            }
        }
        TypedExprKind::FieldAccess(f) => {
            check_expr_for_externs(&f.object, diagnostics);
        }
        TypedExprKind::CapRestrict(_) => {
            // `cap.restrict(authority)` references a state field by name;
            // no sub-expressions to recurse into.
        }
        TypedExprKind::CapSplit(c) => {
            check_expr_for_externs(&c.amount, diagnostics);
        }
        TypedExprKind::CapDraw(c) => {
            check_expr_for_externs(&c.amount, diagnostics);
        }
        TypedExprKind::Mint(m) => {
            check_expr_for_externs(&m.target, diagnostics);
        }
        TypedExprKind::ArrayLit(a) => {
            for elem in &a.elements {
                check_expr_for_externs(elem, diagnostics);
            }
        }
        // PR-E3: recurse into f-string interpolation holes.
        TypedExprKind::FString(fs) => {
            for part in &fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = part {
                    check_expr_for_externs(h, diagnostics);
                }
            }
        }
        TypedExprKind::Index(i) => {
            check_expr_for_externs(&i.array, diagnostics);
            check_expr_for_externs(&i.index, diagnostics);
        }
        // PR AF / N20-AF: slice operator inherits receiver's ring;
        // recursively walk children for extern-call discovery.
        TypedExprKind::Slice(s) => {
            check_expr_for_externs(&s.array, diagnostics);
            if let Some(start) = &s.start {
                check_expr_for_externs(start, diagnostics);
            }
            if let Some(end) = &s.end {
                check_expr_for_externs(end, diagnostics);
            }
        }
        TypedExprKind::ClosureConstruct(_) => {
            // Closure bodies are typed independently; ring checks fire on
            // the closure's own function. No recursion needed here.
        }
        TypedExprKind::Borrow(b) => check_expr_for_externs(&b.inner, diagnostics),
        TypedExprKind::Grant(g) => {
            check_expr_for_externs(&g.cap, diagnostics);
            check_expr_for_externs(&g.body, diagnostics);
        }
        TypedExprKind::Handle(h) => {
            check_inner_body_for_externs(&h.body.statements, diagnostics);
        }
        // Effect Handlers (EH3, C-VIS): traverse the new nodes for completeness.
        TypedExprKind::Perform(p) => {
            for arg in &p.args {
                check_expr_for_externs(arg, diagnostics);
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            check_expr_for_externs(&c.scrutinee, diagnostics);
            for clause in &c.clauses {
                check_inner_body_for_externs(&clause.body.statements, diagnostics);
            }
        }
        TypedExprKind::Resume(r) => {
            check_expr_for_externs(&r.value, diagnostics);
        }
        TypedExprKind::Declassify(d) => {
            check_expr_for_externs(&d.value, diagnostics);
            check_expr_for_externs(&d.cap, diagnostics);
        }
        TypedExprKind::DeclassifyCt(d) => {
            check_expr_for_externs(&d.value, diagnostics);
            check_expr_for_externs(&d.cap, diagnostics);
        }
        TypedExprKind::Region(r) => {
            check_expr_for_externs(&r.limit, diagnostics);
            check_inner_body_for_externs(&r.body.statements, diagnostics);
        }
        TypedExprKind::Literal(_) | TypedExprKind::Local(_) | TypedExprKind::StateField(_) => {}
    }
}

fn check_outer_body(stmts: &[TypedStmt], diagnostics: &mut Vec<Diagnostic>) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Let(s) if is_owned_cap(&s.ty) => {
                diagnostics.push(Diagnostic::error(
                    codes::R001,
                    format!(
                        "outer ring cannot own capabilities: variable `{}` has type `{}`",
                        s.name,
                        render_type_brief(&s.ty)
                    ),
                    Some(s.span),
                ));
            }
            TypedStmt::If(s) => {
                check_outer_body(&s.then_branch.statements, diagnostics);
                check_outer_body(&s.else_branch.statements, diagnostics);
            }
            TypedStmt::While(s) => {
                check_outer_body(&s.body.statements, diagnostics);
            }
            TypedStmt::ForIn(s) => {
                check_outer_body(&s.body, diagnostics);
            }
            // FAIL-OPEN HAZARD (hand-audited): this walker ends in `_ => {}`, so
            // rustc will NOT flag a missing arm — an owned-cap `let` inside a
            // range-for body would silently evade R001 without this recursion.
            TypedStmt::ForRange(s) => {
                check_outer_body(&s.body, diagnostics);
            }
            TypedStmt::Match(s) => {
                for arm in &s.arms {
                    check_outer_body(&arm.body.statements, diagnostics);
                }
            }
            _ => {}
        }
    }
}

/// Check if a type is an owned capability (not a borrow).
///
/// The recursion MUST cover every OWNED-value position — a missing arm
/// lets a cap wrapped in an aggregate (tuple element, closure param/return)
/// evade R001. `Tuple` destructures to a fresh cap binding and `Fn`
/// passes/produces a cap across the indirect-call boundary, so both count
/// (mirrors `type_contains_cap` in type_check/resolve.rs — same walker-gap
/// bug class as the historical `type_contains_cap` Tuple/Fn miss).
#[deny(clippy::wildcard_enum_match_arm)]
fn is_owned_cap(ty: &Type) -> bool {
    match ty {
        Type::Cap(_, _) => true,
        Type::Named(_, args) => args.iter().any(is_owned_cap),
        Type::Array { elem, .. } => is_owned_cap(elem),
        Type::Tuple(elems) => elems.iter().any(is_owned_cap),
        Type::Fn(params, ret, _, _) => params.iter().any(is_owned_cap) || is_owned_cap(ret),
        // HKT application (erased before ring_check runs; classified rather
        // than wildcarded — the "walker forgot an arm" defense, F005): an
        // application owns a cap iff an argument does, mirroring
        // `type_contains_cap`'s INV-4 arm.
        Type::HktApp { args, .. } => args.iter().any(is_owned_cap),
        // Borrows/slices/raw pointers are not OWNED caps (`contains_cap_ref`
        // handles the borrow channel); the rest are leaves with no nested
        // type to carry a cap. Every arm is explicit (no `_`) so a future
        // `Type` variant fails to compile here until it is classified —
        // wildcarding this walker is exactly what the historical Tuple/Fn
        // miss (F005, PR #463) looked like.
        Type::Ref(_, _)
        | Type::Slice(_)
        | Type::Ptr(_)
        | Type::MutPtr(_)
        | Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::U256
        | Type::I256
        | Type::Str
        | Type::Generic(_)
        | Type::ActorRef(_)
        | Type::Region
        | Type::IntLit(_)
        | Type::HktVar { .. }
        | Type::TypeCtor(_)
        | Type::StateMarker(_)
        | Type::Never
        | Type::Error => false,
    }
}

/// Check if a type contains a capability reference (&cap T).
///
/// Like `is_owned_cap`, this must recurse through every position that can
/// carry a `&cap` outward — tuple elements, closure params/returns, and
/// array elements — or a cap reference wrapped in an aggregate evades R002.
#[deny(clippy::wildcard_enum_match_arm)]
fn contains_cap_ref(ty: &Type) -> bool {
    match ty {
        Type::Ref(inner, _) => is_owned_cap(inner) || contains_cap_ref(inner),
        Type::Slice(inner) => contains_cap_ref(inner),
        Type::Named(_, args) => args.iter().any(contains_cap_ref),
        Type::Tuple(elems) => elems.iter().any(contains_cap_ref),
        Type::Fn(params, ret, _, _) => params.iter().any(contains_cap_ref) || contains_cap_ref(ret),
        Type::Array { elem, .. } => contains_cap_ref(elem),
        // HKT application (erased before ring_check runs; classified rather
        // than wildcarded — the "walker forgot an arm" defense, F005).
        Type::HktApp { args, .. } => args.iter().any(contains_cap_ref),
        // An OWNED cap is not a cap-REF (that channel belongs to
        // `is_owned_cap`/R001); raw pointers are extern-context-gated; the
        // rest are leaves. Explicit arms, no `_` — a future `Type` variant
        // must be classified here before this compiles.
        Type::Cap(_, _)
        | Type::Ptr(_)
        | Type::MutPtr(_)
        | Type::Unit
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::U256
        | Type::I256
        | Type::Str
        | Type::Generic(_)
        | Type::ActorRef(_)
        | Type::Region
        | Type::IntLit(_)
        | Type::HktVar { .. }
        | Type::TypeCtor(_)
        | Type::StateMarker(_)
        | Type::Never
        | Type::Error => false,
    }
}

fn render_type_brief(ty: &Type) -> String {
    match ty {
        Type::Cap(name, params) if params.is_empty() => format!("cap {name}"),
        Type::Cap(name, params) => {
            let vals = params
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("cap {name}({vals})")
        }
        Type::Ref(inner, false) => format!("&{}", render_type_brief(inner)),
        Type::Ref(inner, true) => format!("&mut {}", render_type_brief(inner)),
        _ => format!("{ty:?}"),
    }
}

/// Walker-fence truth tables (F005): pin every structural channel's verdict
/// for the two ring-boundary cap walkers. The compile-time half of the fence
/// is the walkers' TOTAL matches; see `type_check/resolve.rs`'s
/// `walker_fence_tests` for the type-check-side twins.
#[cfg(test)]
mod walker_fence_tests {
    use super::*;
    use crate::registries::EffectSet;

    fn cap() -> Type {
        Type::Cap("Fuel".into(), Vec::new())
    }

    #[test]
    fn owned_cap_walker_finds_every_owned_channel() {
        assert!(is_owned_cap(&cap()));
        assert!(is_owned_cap(&Type::Named("Box".into(), vec![cap()])));
        assert!(is_owned_cap(&Type::Array {
            elem: Box::new(cap()),
            size: 1,
        }));
        assert!(is_owned_cap(&Type::Tuple(vec![Type::I64, cap()])));
        assert!(is_owned_cap(&Type::Fn(
            vec![cap()],
            Box::new(Type::I64),
            false,
            EffectSet::empty()
        )));
        assert!(is_owned_cap(&Type::Fn(
            vec![],
            Box::new(cap()),
            false,
            EffectSet::empty()
        )));
        assert!(is_owned_cap(&Type::HktApp {
            ctor: "F".into(),
            args: vec![cap()],
        }));
        // Borrows are NOT owned caps.
        assert!(!is_owned_cap(&Type::Ref(Box::new(cap()), false)));
        assert!(!is_owned_cap(&Type::Slice(Box::new(cap()))));
    }

    #[test]
    fn cap_ref_walker_finds_every_borrow_channel() {
        let ref_cap = Type::Ref(Box::new(cap()), false);
        assert!(contains_cap_ref(&ref_cap));
        assert!(contains_cap_ref(&Type::Slice(Box::new(ref_cap.clone()))));
        assert!(contains_cap_ref(&Type::Named(
            "Box".into(),
            vec![ref_cap.clone()]
        )));
        assert!(contains_cap_ref(&Type::Tuple(vec![
            Type::I64,
            ref_cap.clone()
        ])));
        assert!(contains_cap_ref(&Type::Fn(
            vec![ref_cap.clone()],
            Box::new(Type::I64),
            false,
            EffectSet::empty()
        )));
        assert!(contains_cap_ref(&Type::Fn(
            vec![],
            Box::new(ref_cap.clone()),
            false,
            EffectSet::empty()
        )));
        assert!(contains_cap_ref(&Type::Array {
            elem: Box::new(ref_cap.clone()),
            size: 1,
        }));
        assert!(contains_cap_ref(&Type::HktApp {
            ctor: "F".into(),
            args: vec![ref_cap],
        }));
        // A bare OWNED cap is not a cap-REF (that channel is R001's).
        assert!(!contains_cap_ref(&cap()));
    }
}
