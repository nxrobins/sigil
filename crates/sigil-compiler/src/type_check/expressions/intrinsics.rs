//! Built-in intrinsic call recognition and type inference.

use std::collections::HashMap;

use super::super::resolve::{
    is_machine_integer_type, render_type, resolve_type_expr, try_cap_deadline_diagnostic,
    type_compatible,
};
use super::super::{Type, TypeUniverse};
use crate::ast::CallExpr;
use crate::diagnostics::{Diagnostic, codes};
use crate::typed_ast::{TypedExpr, TypedExprKind, TypedIntrinsicExpr, TypedIntrinsicKind};

/// Shape tag returned by `resolve_intrinsic_call` — identifies which
/// built-in intrinsic the call site is invoking without yet binding
/// the typed payload (e.g., `SlotNew` needs to resolve its type arg,
/// which requires the universe).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IntrinsicShape {
    Alloc,
    Load8,
    Store8,
    SlotNew,
    SlotPut,
    SlotTake,
    CtEq,
    CtSelect,
    CtLt,
    VecStore,
    VecLoad,
    StrFromRaw,
    U256FromI64,
    /// `u256_make(l0, l1, l2, l3)` — build a u256 from four u64 little-endian
    /// limbs. The stdlib u256 math's result constructor. Module-private to `u256`.
    U256Make,
    /// `u256_limb(v, i)` — read limb `i` (a constant 0-3) of a u256 as u64. The
    /// stdlib u256 math's operand reader. Module-private to `u256`.
    U256Limb,
    /// `trap_if(cond)` — runtime-trap (revert) when `cond` is true. Backs the
    /// checked-arithmetic overflow/underflow/÷0 reverts (E1). Module-private to `u256`.
    TrapIf,
    /// `trap()` — unconditional, explicit abort (wasm `unreachable`). The
    /// first-class replacement for the `arr[N]`-as-trap idiom. Globally callable.
    Trap,
}

pub(super) fn resolve_intrinsic_call(path: &crate::ast::Path) -> Option<IntrinsicShape> {
    if path.segments.len() != 1 {
        return None;
    }
    let has_type_args = !path.type_args.is_empty();
    match (path.segments[0].as_str(), has_type_args) {
        ("alloc", false) => Some(IntrinsicShape::Alloc),
        ("load8", false) => Some(IntrinsicShape::Load8),
        ("store8", false) => Some(IntrinsicShape::Store8),
        // slot_new is recognized regardless of type_args presence — the
        // missing-type-arg case emits T192 in infer_intrinsic_call_expr
        // rather than falling through to "unknown function".
        ("slot_new", _) => Some(IntrinsicShape::SlotNew),
        ("slot_put", false) => Some(IntrinsicShape::SlotPut),
        ("slot_take", false) => Some(IntrinsicShape::SlotTake),
        // Phase 2H §3.5: branch-free constant-time primitives.
        ("ct_eq", false) => Some(IntrinsicShape::CtEq),
        ("ct_select", false) => Some(IntrinsicShape::CtSelect),
        ("ct_lt", false) => Some(IntrinsicShape::CtLt),
        // Stdlib `Vec<T>` element access — stdlib-private (grep-enforced to
        // appear only in stdlib/sigil/vec.sigil via `tests/vec_quarantine.rs`).
        ("vec_store", false) => Some(IntrinsicShape::VecStore),
        ("vec_load", false) => Some(IntrinsicShape::VecLoad),
        // Owned-strings PR-1: the private str-header forge. Recognized for ALL
        // callers so the T257 module gate (in infer_intrinsic_call_expr) can
        // reject out-of-`string` callers with a real diagnostic rather than a
        // generic "unknown function" — and grep-quarantined to string.sigil.
        ("str_from_raw", false) => Some(IntrinsicShape::StrFromRaw),
        // u256 PR-U0: the minimal constructor — a non-negative i64 → u256.
        // Globally callable (unlike str_from_raw): it cannot forge an
        // out-of-bounds view — it always allocates a fresh, fully-initialized
        // 32-byte cell.
        ("u256_from_i64", false) => Some(IntrinsicShape::U256FromI64),
        // u256 PR-U1 stdlib-math building blocks. Recognized for ALL callers so
        // the module gate (in infer_intrinsic_call_expr) rejects out-of-`u256`
        // callers with a real diagnostic; grep-quarantined to u256.sigil.
        ("u256_make", false) => Some(IntrinsicShape::U256Make),
        ("u256_limb", false) => Some(IntrinsicShape::U256Limb),
        ("trap_if", false) => Some(IntrinsicShape::TrapIf),
        // Unconditional abort — globally callable (the explicit `trap()`
        // primitive that replaces the deliberate out-of-bounds-index trap).
        ("trap", false) => Some(IntrinsicShape::Trap),
        _ => None,
    }
}

pub(super) fn infer_intrinsic_call_expr(
    expr: &CallExpr,
    shape: IntrinsicShape,
    args: Vec<TypedExpr>,
    module_name: &str,
    universe: &TypeUniverse,
    diagnostics: &mut Vec<Diagnostic>,
) -> TypedExpr {
    let mut had_error = false;
    let name = match shape {
        IntrinsicShape::Alloc => "alloc",
        IntrinsicShape::Load8 => "load8",
        IntrinsicShape::Store8 => "store8",
        IntrinsicShape::SlotNew => "slot_new",
        IntrinsicShape::SlotPut => "slot_put",
        IntrinsicShape::SlotTake => "slot_take",
        IntrinsicShape::CtEq => "ct_eq",
        IntrinsicShape::CtSelect => "ct_select",
        IntrinsicShape::CtLt => "ct_lt",
        IntrinsicShape::VecStore => "vec_store",
        IntrinsicShape::VecLoad => "vec_load",
        IntrinsicShape::StrFromRaw => "str_from_raw",
        IntrinsicShape::U256FromI64 => "u256_from_i64",
        IntrinsicShape::U256Make => "u256_make",
        IntrinsicShape::U256Limb => "u256_limb",
        IntrinsicShape::TrapIf => "trap_if",
        IntrinsicShape::Trap => "trap",
    };
    let expected_arity = match shape {
        IntrinsicShape::Alloc | IntrinsicShape::Load8 | IntrinsicShape::SlotTake => 1,
        IntrinsicShape::Store8 | IntrinsicShape::SlotPut => 2,
        IntrinsicShape::SlotNew => 0,
        IntrinsicShape::CtEq | IntrinsicShape::CtLt => 2,
        IntrinsicShape::CtSelect => 3,
        IntrinsicShape::VecStore | IntrinsicShape::VecLoad => 4,
        IntrinsicShape::StrFromRaw => 2,
        IntrinsicShape::U256FromI64 => 1,
        IntrinsicShape::U256Make => 4,
        IntrinsicShape::U256Limb => 2,
        IntrinsicShape::TrapIf => 1,
        IntrinsicShape::Trap => 0,
    };

    if args.len() != expected_arity {
        diagnostics.push(Diagnostic::error(
            codes::T074,
            format!(
                "intrinsic `{name}` expects {expected_arity} argument(s), found {}",
                args.len()
            ),
            Some(expr.span),
        ));
        had_error = true;
    }

    // Per-shape arg validation. For Slot intrinsics, also extract the
    // cap-type from either the path's type_args (slot_new) or the
    // slot-typed arg's `Slot<T>` (slot_put / slot_take).
    let (kind, ty): (TypedIntrinsicKind, Type) = match shape {
        IntrinsicShape::Alloc => {
            if let Some(size) = args.first()
                && !is_machine_integer_type(&size.ty)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `alloc` expects an integer size, found `{}`",
                        render_type(&size.ty)
                    ),
                    Some(size.span),
                ));
                had_error = true;
            }
            (TypedIntrinsicKind::Alloc, Type::I64)
        }
        IntrinsicShape::Load8 => {
            if let Some(ptr) = args.first()
                && !is_machine_integer_type(&ptr.ty)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `load8` expects an integer pointer, found `{}`",
                        render_type(&ptr.ty)
                    ),
                    Some(ptr.span),
                ));
                had_error = true;
            }
            (TypedIntrinsicKind::Load8, Type::I64)
        }
        IntrinsicShape::Store8 => {
            if let Some(ptr) = args.first()
                && !is_machine_integer_type(&ptr.ty)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `store8` expects an integer pointer, found `{}`",
                        render_type(&ptr.ty)
                    ),
                    Some(ptr.span),
                ));
                had_error = true;
            }
            if let Some(value) = args.get(1)
                && !is_machine_integer_type(&value.ty)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `store8` expects an integer byte value, found `{}`",
                        render_type(&value.ty)
                    ),
                    Some(value.span),
                ));
                had_error = true;
            }
            (TypedIntrinsicKind::Store8, Type::Unit)
        }
        IntrinsicShape::SlotNew => {
            // slot_new::<T>() — T must be a cap type. Wall 3: inner
            // cap may have multi-position parameters. Preserve the
            // full Vec<i64> when constructing the Slot's inner type
            // so MI-1 (Slot subtyping respects all params) holds via
            // type_compatible's recursion.
            let (cap_type, cap_deadlines) = match expr.callee.type_args.first() {
                None => {
                    diagnostics.push(Diagnostic::error(
                        codes::T192,
                        "intrinsic `slot_new` requires a type argument: use `slot_new::<CapType>()`",
                        Some(expr.span),
                    ));
                    had_error = true;
                    ("<error>".to_owned(), Vec::new())
                }
                Some(ty_expr) => {
                    let resolved = resolve_type_expr(ty_expr, universe, &HashMap::new(), &[]);
                    match &resolved {
                        Type::Cap(name, deadlines) => (name.clone(), deadlines.clone()),
                        _ => {
                            diagnostics.push(Diagnostic::error(
                                codes::T191,
                                format!(
                                    "`Slot<T>` requires T to be a capability type, found `{}`",
                                    render_type(&resolved)
                                ),
                                Some(expr.span),
                            ));
                            had_error = true;
                            ("<error>".to_owned(), Vec::new())
                        }
                    }
                }
            };
            let slot_ty = if had_error {
                Type::Error
            } else {
                Type::Named(
                    "Slot".to_owned(),
                    vec![Type::Cap(cap_type.clone(), cap_deadlines)],
                )
            };
            (TypedIntrinsicKind::SlotNew { cap_type }, slot_ty)
        }
        IntrinsicShape::SlotPut => {
            // slot_put(slot, cap) — first arg must be Slot<T>, second must be T.
            let slot_cap_ty = args.first().and_then(|slot_arg| match &slot_arg.ty {
                Type::Named(name, type_args) if name == "Slot" && type_args.len() == 1 => {
                    Some(type_args[0].clone())
                }
                _ => None,
            });
            match (slot_cap_ty, args.get(1)) {
                (None, _) if !args.is_empty() => {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `slot_put` expects a `Slot<T>` as the first argument, found `{}`",
                            render_type(&args[0].ty)
                        ),
                        Some(args[0].span),
                    ));
                    had_error = true;
                }
                (Some(slot_cap), Some(cap_arg)) if !type_compatible(&slot_cap, &cap_arg.ty) => {
                    let arg_label = "slot_put cap argument".to_owned();
                    let site_ctx =
                        format!("`slot_put` site expecting `{}`", render_type(&slot_cap));
                    if let Some(t195) = try_cap_deadline_diagnostic(
                        &slot_cap,
                        &cap_arg.ty,
                        &arg_label,
                        &site_ctx,
                        cap_arg.span,
                    ) {
                        diagnostics.push(t195);
                    } else {
                        diagnostics.push(Diagnostic::error(
                            codes::T075,
                            format!(
                                "intrinsic `slot_put` expects a `{}` as the second argument, found `{}`",
                                render_type(&slot_cap),
                                render_type(&cap_arg.ty)
                            ),
                            Some(cap_arg.span),
                        ));
                    }
                    had_error = true;
                }
                _ => {}
            }
            (TypedIntrinsicKind::SlotPut, Type::Unit)
        }
        IntrinsicShape::SlotTake => {
            // slot_take(slot) — first arg must be Slot<T>; return type is T.
            let cap_ty = match args.first().map(|a| &a.ty) {
                Some(Type::Named(name, type_args)) if name == "Slot" && type_args.len() == 1 => {
                    type_args[0].clone()
                }
                Some(other) => {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `slot_take` expects a `Slot<T>` argument, found `{}`",
                            render_type(other)
                        ),
                        Some(args[0].span),
                    ));
                    had_error = true;
                    Type::Error
                }
                None => Type::Error,
            };
            (TypedIntrinsicKind::SlotTake, cap_ty)
        }
        IntrinsicShape::CtEq | IntrinsicShape::CtLt => {
            // ct_eq / ct_lt take two integer operands and return bool.
            for (idx, arg) in args.iter().enumerate().take(2) {
                if !is_machine_integer_type(&arg.ty) && !matches!(arg.ty, Type::Error) {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `{name}` expects integer arguments, arg #{} is `{}`",
                            idx + 1,
                            render_type(&arg.ty)
                        ),
                        Some(arg.span),
                    ));
                    had_error = true;
                }
            }
            let kind = match shape {
                IntrinsicShape::CtEq => TypedIntrinsicKind::CtEq,
                IntrinsicShape::CtLt => TypedIntrinsicKind::CtLt,
                _ => unreachable!(),
            };
            (kind, Type::Bool)
        }
        IntrinsicShape::CtSelect => {
            // ct_select(cond: bool, t: i64, f: i64) -> i64.
            if let Some(cond) = args.first()
                && !matches!(cond.ty, Type::Bool | Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `ct_select` expects a boolean condition, found `{}`",
                        render_type(&cond.ty)
                    ),
                    Some(cond.span),
                ));
                had_error = true;
            }
            for (idx, arg) in args.iter().enumerate().skip(1).take(2) {
                if !is_machine_integer_type(&arg.ty) && !matches!(arg.ty, Type::Error) {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `ct_select` expects integer branch values, arg #{} is `{}`",
                            idx + 1,
                            render_type(&arg.ty)
                        ),
                        Some(arg.span),
                    ));
                    had_error = true;
                }
            }
            (TypedIntrinsicKind::CtSelect, Type::I64)
        }
        IntrinsicShape::VecStore => {
            // vec_store(base, index, bound, val: T). base/index/bound are
            // integers; the element `AirType` is frozen from `val`'s
            // concrete type — never a turbofish, so monomorphization cannot
            // leak a generic param into a wrong store width.
            for (i, label) in [(0usize, "base"), (1, "index"), (2, "bound")] {
                if let Some(a) = args.get(i)
                    && !is_machine_integer_type(&a.ty)
                    && !matches!(a.ty, Type::Error)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `vec_store` {label} must be an integer, found `{}`",
                            render_type(&a.ty)
                        ),
                        Some(a.span),
                    ));
                    had_error = true;
                }
            }
            let elem = args
                .get(3)
                .map(|a| crate::air::lower_type(&a.ty))
                .unwrap_or(crate::air::AirType::I64);
            (TypedIntrinsicKind::VecStore { elem }, Type::Unit)
        }
        IntrinsicShape::VecLoad => {
            // vec_load(base, index, bound, witness: Vec<T>) -> T. The element
            // type is the `Vec<T>` witness's type-arg (mirrors slot_take's
            // return-from-arg).
            for (i, label) in [(0usize, "base"), (1, "index"), (2, "bound")] {
                if let Some(a) = args.get(i)
                    && !is_machine_integer_type(&a.ty)
                    && !matches!(a.ty, Type::Error)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `vec_load` {label} must be an integer, found `{}`",
                            render_type(&a.ty)
                        ),
                        Some(a.span),
                    ));
                    had_error = true;
                }
            }
            let elem_ty = match args.get(3).map(|a| &a.ty) {
                Some(Type::Named(name, type_args)) if name == "Vec" && type_args.len() == 1 => {
                    type_args[0].clone()
                }
                Some(other) => {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `vec_load` expects a `Vec<T>` witness as the 4th argument, found `{}`",
                            render_type(other)
                        ),
                        Some(args[3].span),
                    ));
                    had_error = true;
                    Type::Error
                }
                None => Type::Error,
            };
            let elem = crate::air::lower_type(&elem_ty);
            (TypedIntrinsicKind::VecLoad { elem }, elem_ty)
        }
        IntrinsicShape::StrFromRaw => {
            // ET-1 (owned-strings PR-1): the str-header forge is stdlib-private.
            // Reject any caller outside module `string` with T257 BEFORE producing
            // a `str` — a forged `(ptr, len)` would mint a fat-pointer that the
            // `byte_at`/`substr` bounds-checks then trust, reading out of bounds.
            // `string.sigil`'s `concat`/`join`/`itoa` builders are the only
            // sanctioned callers (they derive `len` from the buffer they alloc).
            if module_name != "string" {
                diagnostics.push(Diagnostic::error(
                    codes::T257,
                    format!(
                        "intrinsic `str_from_raw` is stdlib-private to module `string`; it forges a \
                         `str` from raw memory and may not be called from module `{module_name}`. \
                         Build owned strings via `concat`/`join`/`itoa` instead."
                    ),
                    Some(expr.span),
                ));
                had_error = true;
            }
            // Both args are machine integers: a raw data pointer and a byte length.
            if let Some(ptr) = args.first()
                && !is_machine_integer_type(&ptr.ty)
                && !matches!(ptr.ty, Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `str_from_raw` expects an integer data pointer, found `{}`",
                        render_type(&ptr.ty)
                    ),
                    Some(ptr.span),
                ));
                had_error = true;
            }
            if let Some(len) = args.get(1)
                && !is_machine_integer_type(&len.ty)
                && !matches!(len.ty, Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `str_from_raw` expects an integer length, found `{}`",
                        render_type(&len.ty)
                    ),
                    Some(len.span),
                ));
                had_error = true;
            }
            // Freeze the arg widths so AIR narrows each to U32 without a locals scan
            // (mirrors `StrSubstr`'s start/end stamps).
            let ptr = args
                .first()
                .map(|a| crate::air::lower_type(&a.ty))
                .unwrap_or(crate::air::AirType::I64);
            let len = args
                .get(1)
                .map(|a| crate::air::lower_type(&a.ty))
                .unwrap_or(crate::air::AirType::I64);
            (TypedIntrinsicKind::StrFromRaw { ptr, len }, Type::Str)
        }
        IntrinsicShape::U256FromI64 => {
            // u256 PR-U0: the operand is a machine integer; the result is a
            // freshly-allocated u256 (limb0 = arg, limbs 1-3 = 0).
            if let Some(arg) = args.first()
                && !is_machine_integer_type(&arg.ty)
                && !matches!(arg.ty, Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `u256_from_i64` expects an integer operand, found `{}`",
                        render_type(&arg.ty)
                    ),
                    Some(arg.span),
                ));
                had_error = true;
            }
            let arg = args
                .first()
                .map(|a| crate::air::lower_type(&a.ty))
                .unwrap_or(crate::air::AirType::I64);
            (TypedIntrinsicKind::U256FromI64 { arg }, Type::U256)
        }
        IntrinsicShape::U256Make => {
            // Build a u256 from four u64 little-endian limbs (the stdlib math's
            // result constructor). Each limb is a machine integer.
            for (i, a) in args.iter().enumerate() {
                if !is_machine_integer_type(&a.ty) && !matches!(a.ty, Type::Error) {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        format!(
                            "intrinsic `u256_make` limb {i} expects an integer, found `{}`",
                            render_type(&a.ty)
                        ),
                        Some(a.span),
                    ));
                    had_error = true;
                }
            }
            (TypedIntrinsicKind::U256Make, Type::U256)
        }
        IntrinsicShape::U256Limb => {
            // Read limb `i` (a compile-time-constant 0..=3) of a u256 as u64.
            if let Some(v) = args.first()
                && !matches!(v.ty, Type::U256 | Type::I256 | Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `u256_limb` expects a u256/i256 operand, found `{}`",
                        render_type(&v.ty)
                    ),
                    Some(v.span),
                ));
                had_error = true;
            }
            let index: u32 = match args.get(1).map(|a| &a.kind) {
                Some(TypedExprKind::Literal(crate::ast::Literal::Int(n))) if *n >= 0 && *n <= 3 => {
                    *n as u32
                }
                _ => {
                    diagnostics.push(Diagnostic::error(
                        codes::T075,
                        "intrinsic `u256_limb` index must be a constant integer 0..=3".to_string(),
                        Some(expr.span),
                    ));
                    had_error = true;
                    0
                }
            };
            (TypedIntrinsicKind::U256Limb { index }, Type::U64)
        }
        IntrinsicShape::TrapIf => {
            // Runtime-trap (revert) when the condition is true — the
            // checked-arithmetic overflow/underflow/÷0 mechanism (E1).
            if let Some(c) = args.first()
                && !matches!(c.ty, Type::Bool | Type::Error)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T075,
                    format!(
                        "intrinsic `trap_if` expects a bool condition, found `{}`",
                        render_type(&c.ty)
                    ),
                    Some(c.span),
                ));
                had_error = true;
            }
            (TypedIntrinsicKind::TrapIf, Type::Unit)
        }
        IntrinsicShape::Trap => {
            // `trap()` — an unconditional, explicit abort (wasm `unreachable`).
            // Zero args (arity checked above). Typed `Unit` (statement-position
            // abort): it really diverges at runtime, but the type system does
            // not yet track divergence — promoting it to `Type::Never` (value
            // position) is a clean future extension. First-class replacement for
            // the `arr[N]`-as-trap idiom. NOW typed the bottom type `Never`: it
            // ALWAYS aborts (the load-bearing invariant), so a statement of type
            // `Never` terminates a path (the return-checker divergence hook in
            // statements.rs). Value-position (`let x = trap()`, `return trap()`)
            // is Tier B — fail-closed for now (no `Never <: T` rule).
            (TypedIntrinsicKind::Trap, Type::Never)
        }
    };

    let final_ty = if had_error { Type::Error } else { ty };

    TypedExpr {
        ty: final_ty,
        kind: TypedExprKind::Intrinsic(TypedIntrinsicExpr { kind, args }),
        span: expr.span,

        refinement: None,
    }
}
