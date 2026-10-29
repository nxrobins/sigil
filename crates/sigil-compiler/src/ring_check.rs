//! Ring boundary checker.
//!
//! Enforces the two-ring trust model:
//! - R001: Outer ring cannot own capabilities (a borrowed `&Cap` parameter is allowed)
//! - R002: Capability references cannot escape outer ring functions
//! - R003: Inner ring cannot call extern functions (forward-looking for 2E)
//! - R004: no call crosses the ring boundary, in either direction — one made inside a
//!   `grant` body included, because a `grant` closure runs in its caller's ring (emitted by
//!   `type_check::expressions::calls` at the SOURCE call site, not here)
//! - R007: a lowered call crosses the ring boundary although no source call did
//!   (`check_air_ring_placement`, below — an AIR-level gate, not a source one)
//! - R008: an outer-ring module that declares an `extern` must be `#[trusted]`, and an `extern`
//!   call in generic code needs every module governing the instance to be `#[trusted]`; binding a
//!   host function is the privilege the attribute grants (inner-ring `extern` calls are R003)
//! - R009: outer-ring code cannot message, spawn, or restrict, split, draw or mint a capability:
//!   the outer module has no host import for them (`check_air_outer_ring_imports`, below — an
//!   AIR-level gate, like R007)

use std::collections::BTreeSet;

use crate::{
    air::{AirProgram, AirStmt},
    ast::Ring,
    diagnostics::{Diagnostic, codes},
    type_check::{Type, TypedModule, TypedProgram, TypedStmt},
    typed_ast::{InstanceHome, TypedExpr, TypedExprKind},
    wasm,
};

pub fn check_rings(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();

    for module in &program.modules {
        check_extern_trust(module, &mut diagnostics);
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

/// R009: an outer-ring function cannot message, spawn, or restrict, split, draw or mint a
/// capability.
///
/// `wasm::emit` builds the outer module with a reduced host-import set that leaves out `send`,
/// `ask`, `spawn` and the capability imports. The reduced set is deliberate: the outer ring is FFI
/// surface, which cannot own capabilities (R001) or call inner-ring code (R004), and
/// `attack_47_two_ring_import_segregation` pins the outer module's imports. A statement that calls
/// one of the missing imports has nothing to call in the outer module. Before this gate, the
/// emitter panicked on such a statement (an ICE on a program every checker accepted). R001 refuses
/// an owned capability bound to a variable, but not a message or spawn, and not a capability
/// operation whose result is never bound (`fuel.split(50);`, `mint FileAccess for f;`).
///
/// FAIL DIRECTION: closed. The gate asks `wasm::outer_ring_missing_import`, which reads the
/// emitter's own import table, about every statement of every outer-ring function in the final
/// AIR `emit` receives (the same placement as R007). A statement the outer module cannot emit is
/// refused at compile time, and the emitter's `.expect` is its unreachable backstop. It reports
/// once per function and operation, at the function's declaration, because AIR statements carry
/// no span.
pub fn check_air_outer_ring_imports(program: &AirProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    for function in program.functions.iter().filter(|f| f.ring == Ring::Outer) {
        let mut reported = BTreeSet::new();
        for stmt in function.blocks.iter().flat_map(|block| &block.stmts) {
            let Some((operation, import)) = wasm::outer_ring_missing_import(stmt) else {
                continue;
            };
            if !reported.insert(operation) {
                continue;
            }
            diagnostics.push(Diagnostic::error(
                codes::R009,
                format!(
                    "`{}` (outer ring) uses `{operation}`, which calls the host import `{import}`; \
                     the outer-ring module has no host import for messaging, spawning or \
                     capability operations",
                    function.name,
                ),
                Some(function.def_span),
            ));
        }
    }

    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

/// R008: an outer-ring module may declare an `extern` only if it is `#[trusted]`.
///
/// A declaration binds a host function, so it is held to the trust of the module that WRITES
/// it, which is the module recorded here; no generic routing applies, because a declaration is
/// never monomorphized. The inner ring is out of scope on purpose: an inner-ring module cannot
/// be `#[trusted]` at all (R006), and any call it makes to an `extern` is already R003, so a
/// second code there would only double-report. FAIL DIRECTION: closed. The check runs on the
/// declaration, so an untrusted module cannot bind a host function even if nothing calls it.
/// Generic code is the one way to call an extern a module did not declare (its names resolve
/// in the instantiating module's scope); `check_module_ring_rules` holds those calls to the
/// governing meet.
fn check_extern_trust(module: &TypedModule, diagnostics: &mut Vec<Diagnostic>) {
    if module.ring != Ring::Outer || module.trusted {
        return;
    }
    for decl in &module.externs {
        diagnostics.push(Diagnostic::error(
            codes::R008,
            format!(
                "outer-ring module `{}` declares extern function `{}` but is not `#[trusted]`: \
                 binding a host function requires `#[ring(outer)] #[trusted]`",
                module.name, decl.name
            ),
            Some(decl.span),
        ));
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
            // and cannot reach FFI at all: not by a direct extern call
            // (this check), and not through an outer-ring wrapper, since
            // no call crosses the ring boundary (R004) — a call made
            // inside a `grant` body included, because the `grant`
            // closure runs in the inner ring like its caller.
            //
            // Step 24 of the supremum loop (axis-6 second touch) made this
            // check real. Before, the ring_check pass was a no-op for
            // inner-ring modules ("forward-looking — no extern syntax
            // exists yet"), and an inner-ring module could declare AND
            // call `extern "C" fn foo() ! { FFI, Unsafe }` cleanly.
            walk_extern_calls_stmts(&function.body.statements, &mut |expr, name| {
                diagnostics.push(Diagnostic::error(
                    codes::R003,
                    format!(
                        "inner-ring code cannot call extern function `{name}` — FFI is reachable only from `#[ring(outer)] #[trusted]` modules, and no call crosses the ring boundary, not even one made inside a `grant` body"
                    ),
                    Some(expr.span),
                ));
            });
        }
        // R008, call half. Generic code reaches an `extern` through the scope that resolved
        // its names (SR-019), so an extern call inside an instance, or inside a closure lifted
        // while one was re-checked, is held to the same meet as `handle Unsafe` (E002): it is
        // allowed only when EVERY governing module is trusted. Where inner-ring rules apply,
        // R003 above already rejects every extern call; a non-instance can call only its own
        // module's externs, which the declaration half (`check_extern_trust`) holds to that
        // module's trust. FAIL DIRECTION: closed. The message names the definer and every
        // untrusted governing module, since the module to fix is often not the one whose text
        // holds the call (a trusted generic instantiated by an untrusted caller).
        if let Some(home) = program.instance_homes.get(&function.name)
            && governing.outer_rules
            && !governing.inner_rules
            && !governing.trusted
        {
            let untrusted = untrusted_governing_subject(program, home);
            walk_extern_calls_stmts(&function.body.statements, &mut |expr, name| {
                diagnostics.push(Diagnostic::error(
                    codes::R008,
                    format!(
                        "generic code defined in module `{}` calls extern function `{name}`, but {untrusted} not `#[trusted]`: binding a host function requires every module governing this instance to be `#[ring(outer)] #[trusted]`",
                        home.definer
                    ),
                    Some(expr.span),
                ));
            });
        }
    }
}

/// The modules governing `home` that are not `#[trusted]`, as the subject of R008's call-half
/// message: "governing module `tool` is", or "governing modules `lib` and `tool` are". The
/// definer comes first, then the other scopes in name order, each once. The call half runs only
/// when `governing_context` found the meet over these same modules untrusted, so the list is never
/// empty, and every name resolves: that walk raised the ICE for a name that does not.
fn untrusted_governing_subject(program: &TypedProgram, home: &InstanceHome) -> String {
    let mut untrusted: Vec<String> = Vec::new();
    for name in std::iter::once(&home.definer).chain(&home.scopes) {
        let module = program
            .modules
            .iter()
            .find(|module| module.name == *name)
            .expect("`governing_context` resolved every module of this home before the call half");
        let quoted = format!("`{name}`");
        if !module.trusted && !untrusted.contains(&quoted) {
            untrusted.push(quoted);
        }
    }
    match untrusted.split_last() {
        Some((only, [])) => format!("governing module {only} is"),
        Some((last, rest)) => format!("governing modules {} and {last} are", rest.join(", ")),
        None => unreachable!(
            "R008's call half runs only on an untrusted meet, so a governing module is untrusted"
        ),
    }
}

/// Visit every `extern` call in `stmts`, in source order, with the call expression and the
/// extern's name. Shared by R003 and R008's call half; the match below is total (no `_` arm),
/// so a new statement or expression kind cannot be skipped silently.
fn walk_extern_calls_stmts(stmts: &[TypedStmt], visit: &mut dyn FnMut(&TypedExpr, &str)) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Let(s) => walk_extern_calls_expr(&s.value, visit),
            TypedStmt::Assign(s) => walk_extern_calls_expr(&s.value, visit),
            TypedStmt::Expr(s) => walk_extern_calls_expr(&s.expr, visit),
            TypedStmt::Return(s) => {
                if let Some(value) = &s.value {
                    walk_extern_calls_expr(value, visit);
                }
            }
            // break/continue call no externs.
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
            TypedStmt::If(s) => {
                walk_extern_calls_expr(&s.condition, visit);
                walk_extern_calls_stmts(&s.then_branch.statements, visit);
                walk_extern_calls_stmts(&s.else_branch.statements, visit);
            }
            TypedStmt::While(s) => {
                walk_extern_calls_expr(&s.condition, visit);
                walk_extern_calls_stmts(&s.body.statements, visit);
            }
            TypedStmt::ForIn(s) => {
                walk_extern_calls_expr(&s.iterable, visit);
                walk_extern_calls_stmts(&s.body, visit);
            }
            TypedStmt::ForRange(s) => {
                walk_extern_calls_expr(&s.start, visit);
                walk_extern_calls_expr(&s.end, visit);
                walk_extern_calls_stmts(&s.body, visit);
            }
            TypedStmt::Match(s) => {
                walk_extern_calls_expr(&s.scrutinee, visit);
                for arm in &s.arms {
                    if let Some(guard) = &arm.guard {
                        walk_extern_calls_expr(guard, visit);
                    }
                    walk_extern_calls_stmts(&arm.body.statements, visit);
                }
            }
        }
    }
}

fn walk_extern_calls_expr(expr: &TypedExpr, visit: &mut dyn FnMut(&TypedExpr, &str)) {
    if let TypedExprKind::ExternCall(call) = &expr.kind {
        visit(expr, &call.extern_name);
    }

    // Recurse into sub-expressions. We only need to find ExternCall;
    // every other kind is traversed for completeness.
    match &expr.kind {
        TypedExprKind::Call(c) => {
            for arg in &c.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        // HOF / N9-HOF: explicit IndirectCall arm. Closure calls
        // don't cross ring boundaries (the callee is a local
        // variable bound at the construction site, which is in
        // the current ring by definition). We only recurse into
        // args to catch any extern calls nested in the args.
        TypedExprKind::IndirectCall(c) => {
            for arg in &c.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        TypedExprKind::ExternCall(c) => {
            for arg in &c.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        TypedExprKind::Intrinsic(i) => {
            for arg in &i.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        TypedExprKind::ResultCtor(r) => {
            walk_extern_calls_expr(&r.value, visit);
        }
        TypedExprKind::EnumConstruct(e) => {
            for f in &e.fields {
                walk_extern_calls_expr(f, visit);
            }
        }
        TypedExprKind::Try(t) => {
            walk_extern_calls_expr(&t.value, visit);
        }
        TypedExprKind::Send(s) => {
            for arg in &s.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        TypedExprKind::Ask(a) => {
            for arg in &a.args {
                walk_extern_calls_expr(arg, visit);
            }
            walk_extern_calls_expr(&a.timeout, visit);
        }
        TypedExprKind::Spawn(s) => {
            for arg in &s.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        TypedExprKind::Binary(b) => {
            walk_extern_calls_expr(&b.lhs, visit);
            walk_extern_calls_expr(&b.rhs, visit);
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, value) in &r.fields {
                walk_extern_calls_expr(value, visit);
            }
        }
        TypedExprKind::FieldAccess(f) => {
            walk_extern_calls_expr(&f.object, visit);
        }
        TypedExprKind::CapRestrict(_) => {
            // `cap.restrict(authority)` references a state field by name;
            // no sub-expressions to recurse into.
        }
        TypedExprKind::CapSplit(c) => {
            walk_extern_calls_expr(&c.amount, visit);
        }
        TypedExprKind::CapDraw(c) => {
            walk_extern_calls_expr(&c.amount, visit);
        }
        TypedExprKind::Mint(m) => {
            walk_extern_calls_expr(&m.target, visit);
        }
        TypedExprKind::ArrayLit(a) => {
            for elem in &a.elements {
                walk_extern_calls_expr(elem, visit);
            }
        }
        // PR-E3: recurse into f-string interpolation holes.
        TypedExprKind::FString(fs) => {
            for part in &fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = part {
                    walk_extern_calls_expr(h, visit);
                }
            }
        }
        TypedExprKind::Index(i) => {
            walk_extern_calls_expr(&i.array, visit);
            walk_extern_calls_expr(&i.index, visit);
        }
        // PR AF / N20-AF: slice operator inherits receiver's ring;
        // recursively walk children for extern-call discovery.
        TypedExprKind::Slice(s) => {
            walk_extern_calls_expr(&s.array, visit);
            if let Some(start) = &s.start {
                walk_extern_calls_expr(start, visit);
            }
            if let Some(end) = &s.end {
                walk_extern_calls_expr(end, visit);
            }
        }
        TypedExprKind::ClosureConstruct(_) => {
            // Closure bodies are typed independently; ring checks fire on
            // the closure's own function. No recursion needed here.
        }
        TypedExprKind::Borrow(b) => walk_extern_calls_expr(&b.inner, visit),
        TypedExprKind::Grant(g) => {
            walk_extern_calls_expr(&g.cap, visit);
            walk_extern_calls_expr(&g.body, visit);
        }
        TypedExprKind::Handle(h) => {
            walk_extern_calls_stmts(&h.body.statements, visit);
        }
        // Effect Handlers (EH3, C-VIS): traverse the new nodes for completeness.
        TypedExprKind::Perform(p) => {
            for arg in &p.args {
                walk_extern_calls_expr(arg, visit);
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            walk_extern_calls_expr(&c.scrutinee, visit);
            for clause in &c.clauses {
                walk_extern_calls_stmts(&clause.body.statements, visit);
            }
        }
        TypedExprKind::Resume(r) => {
            walk_extern_calls_expr(&r.value, visit);
        }
        TypedExprKind::Declassify(d) => {
            walk_extern_calls_expr(&d.value, visit);
            walk_extern_calls_expr(&d.cap, visit);
        }
        TypedExprKind::DeclassifyCt(d) => {
            walk_extern_calls_expr(&d.value, visit);
            walk_extern_calls_expr(&d.cap, visit);
        }
        TypedExprKind::Region(r) => {
            walk_extern_calls_expr(&r.limit, visit);
            walk_extern_calls_stmts(&r.body.statements, visit);
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
