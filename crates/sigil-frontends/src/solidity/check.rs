//! SOL0/SOL1 sound checker — the fail-closed gate that makes the untrusted
//! translator safe. It enforces the hardening-triage negative constraints BEFORE
//! emit, so a contract outside the faithful subset is REJECTED (an `FE4xx`), never
//! mistranslated into verified-but-wrong SIGIL:
//! NC-S2/NC-S5: type allow-list `{uint256, uint, bool, address}` (reject every
//! other width, signed `int*`, `bytesN`, and `msg.*`/`block.*` members).
//! NC-S3: `pragma solidity` whole-range `>= 0.8.0`; no `unchecked` block.
//! NC-S6: closed lowering — reject member access, calls, and `&&`/`||`.
//! NC-S1: strict checks-then-effects — no storage write may be followed by a
//! trap-capable op (require/assert/revert OR checked `+ - * / %` OR a map insert),
//! because a SIGIL trap does not roll back prior writes (unlike Solidity's revert).
//! NC-S4: a state field's initializer must be a static literal (else zero).
//!
//! SOL1 adds a sound `SolTy` inference pass (NC-L3): `address` is a CLOSED distinct
//! type that lowers to `u256` but rejects arithmetic/ordering and never silently
//! mixes with `uint256`; `mapping(K => V)` is single-level only with `K`,`V` ∈
//! {address, uint256/uint}; an `m[k]` key's static type must EXACTLY match the
//! mapping's declared key type. The compiler only ever sees `u256`, so the frontend
//! is the SOLE gate for these distinctions.

use super::parser::{
    AssignOp, BinOp, Constructor, Enum, Expr, Function, Program, StateMutability, Stmt, Struct,
    TypeRef, UnOp,
};
use crate::{FrontendDiag, codes, is_legal_identifier, is_sigil_keyword, limits::SYNTH_PREFIX};
use std::collections::{HashMap, HashSet};
use std::ops::Range;

mod lower;
pub(crate) use lower::UintnHelpers;
pub(super) use lower::{lower_bool_maps, lower_enum_members, lower_uintn_arith};

/// The frontend's view of a value's type. `Num` is inference-only — an integer
/// literal, polymorphic over `U256`/`Address` until a use site pins it. Declared
/// types (`resolve_ty`) never produce `Num`. `Map` is the storage-mapping shape; it
/// is not a value type (a bare mapping must be indexed).
#[derive(Clone, PartialEq)]
enum SolTy {
    /// An integer literal — inference-only, polymorphic over `U256`/`Address`/`UintN`
    /// until a use site pins it. Carries the literal TEXT so its range can be checked
    /// against ANY width at the use site (`num_fits_width`): `address` = 160-bit, `uintN`
    /// = n-bit. Declared types (`resolve_ty`) never produce `Num`.
    Num {
        lit: String,
    },
    U256,
    /// A narrow `uintN` (N a multiple of 8, 8..=248). A CLOSED distinct type that lowers to
    /// the `u256` carrier (the `address` precedent); the frontend is the SOLE gate for its
    /// width — the literal range, widening/narrowing, AND the `2^N` arithmetic trap.
    /// `uint256`/`uint` stay `U256` (full-width, no trap).
    UintN(u16),
    Address,
    Bool,
    Map {
        key: Box<SolTy>,
        value: Box<SolTy>,
    },
    /// A SOL-STRUCT nominal struct type (by name). Identity is the name (EX-2). Lowers
    /// to a SIGIL `record` of the same name; a struct is a value-typed scalar-of-record
    /// (never a bounded-container payload — EX-3).
    Named(String),
    /// A SOL-ENUM nominal enum type (by name). Identity is the name (Color ≠ Direction).
    /// Lowers to a `u256` TAG carrier; `Name.Member` → the member's 0-based index. Admits
    /// all six comparisons among the SAME enum (Solidity enums are ordered); no arithmetic,
    /// no implicit enum↔uint (casts deferred). The frontend is the SOLE gate for enum-ness.
    Enum(String),
    /// SOL-AIRDROP (Rung C): a dynamic array `T[]` of a scalar u256-carrier element
    /// (`address[]`/`uint256[]`/`bytes32[]`) — the airdrop's `recipients`/`amounts` PARAM
    /// arrays, emitted as a bounded `BoundedVec_u256_64`. Only in PARAMETER position
    /// (`resolve_ty` → FE491 elsewhere); `.length` reads as `u256`; `arr[i]` outside a
    /// recognized airdrop loop stays FE442.
    Array(Box<SolTy>),
}

/// Where a declared type appears — restricts `mapping` to state fields.
#[derive(Clone, Copy, PartialEq)]
enum TyPos {
    StateField,
    Param,
    Return,
    Local,
}

/// Per-function context that does not vary along a control-flow path.
struct FnCtx<'a> {
    state: &'a HashSet<&'a str>,
    ret: Option<SolTy>,
    /// SOL-CTOR: true while checking a `constructor` body. The ctor builds a LOCAL `__fe_c`
    /// record returned only on success, so a trap unwinds `new()` and discards everything —
    /// CEI is MOOT (no write of any variant sets `committed_write`, EX-2), and the body may
    /// not `return` (EX-4 → FE464). Methods set this `false` and keep full CEI.
    in_constructor: bool,
}

pub fn check(p: &Program) -> Result<(), FrontendDiag> {
    // NB: identifiers were validated pre-desugar by `validate_user_identifiers`.
    check_pragma(p)?;
    let structs = &p.contract.structs;
    let enums = &p.contract.enums;
    // SOL-ENUM: validate every enum eagerly (empty / duplicate-member → FE467) + name
    // hygiene happened in validate_user_identifiers; struct defs likewise.
    validate_enum_defs(enums)?;
    // SOL-STRUCT: validate every struct definition eagerly (empty / duplicate-field /
    // mapping-or-unknown field type / self-referential cycle) BEFORE any use, so a bad
    // struct is rejected even if never referenced.
    validate_struct_defs(structs, enums)?;
    let state_names: HashSet<&str> = p.contract.state.iter().map(|s| s.name.as_str()).collect();
    // State-field types (incl. the mapping shapes) — the base type env every function
    // starts from.
    let mut state_tys: HashMap<String, SolTy> = HashMap::new();
    for sv in &p.contract.state {
        let sty = resolve_ty(&sv.ty, TyPos::StateField, structs, enums)?;
        if let Some(init) = &sv.init {
            // NC-S4: a state field initializer must be a static literal. A mapping
            // field has no literal form, so a `mapping(…) m = …` initializer lands
            // here as a non-literal and is rejected.
            if !matches!(init, Expr::Num(..) | Expr::Bool(..)) {
                return Err(FrontendDiag::new(
                    codes::FE413_INDETERMINATE_INIT,
                    "state-variable initializer must be a constant literal (SOL0 has no constructor)",
                    init.span(),
                ));
            }
            // NC-L3c + type-kind: the initializer must be ASSIGNABLE to the field type,
            // exactly as a body-position assignment is. Without this, an out-of-range
            // `address` field initializer would bypass the 160-bit range gate (FE430)
            // and a `bool`/numeric mismatch would emit ill-typed SIGIL — the frontend is
            // the SOLE gate for the address range, so it must check the init here too.
            let init_ty = infer(init, &state_tys, structs, enums)?;
            require_assignable(&init_ty, &sty, init.span())?;
        }
        state_tys.insert(sv.name.clone(), sty);
    }
    for f in &p.contract.functions {
        check_function(f, &state_names, &state_tys, structs, enums)?;
    }
    // SOL-CTOR: check the constructor body (deploy-time init logic) like a method body, but
    // CEI-moot (the record is local) and `return`-free (FE464).
    if let Some(ctor) = &p.contract.constructor {
        check_constructor(ctor, &state_names, &state_tys, structs, enums)?;
    }
    Ok(())
}

/// NC-S3: require a `pragma solidity` whose ENTIRE admitted range is `>= 0.8.0`.
/// A missing pragma, a pre-0.8 lower bound, or a range we cannot prove `>= 0.8.0`
/// all REJECT — pre-0.8 wraps arithmetic by default, which has no faithful target.
fn check_pragma(p: &Program) -> Result<(), FrontendDiag> {
    let Some((body, span)) = &p.pragma else {
        return Err(FrontendDiag::new(
            codes::FE411_UNCHECKED_OR_PRAGMA,
            "missing `pragma solidity >= 0.8.0;` (SOL0 requires checked-by-default arithmetic)",
            0..0,
        ));
    };
    // body is e.g. "solidity ^0.8.0" or "solidity >=0.8.2 <0.9.0". Strip "solidity".
    let ver = body
        .trim_start()
        .strip_prefix("solidity")
        .unwrap_or(body)
        .trim();
    if !pragma_is_0_8_plus(ver) {
        return Err(FrontendDiag::new(
            codes::FE411_UNCHECKED_OR_PRAGMA,
            format!(
                "pragma `{ver}` is not provably >= 0.8.0; SOL0 admits only `^0.8.x` / `>=0.8.y` (checked arithmetic)"
            ),
            span.clone(),
        ));
    }
    Ok(())
}

/// SOL-XFILE: the per-closure-file pragma gate (EX-4) — a raw `pragma` BODY (e.g.
/// "solidity ^0.8.20") is provably >= 0.8.0. Reuses the exact single-file rule so a
/// code-bearing imported file cannot smuggle pre-0.8 (wrapping) semantics past the gate.
pub(super) fn pragma_body_is_0_8(body: &str) -> bool {
    let ver = body
        .trim_start()
        .strip_prefix("solidity")
        .unwrap_or(body)
        .trim();
    pragma_is_0_8_plus(ver)
}

/// Conservative whole-range >= 0.8.0 check. Accepts a single `^0.8.x`,
/// `>=0.8.x` (optionally with a `<0.9.0`-style upper bound), or an exact `0.8.x`.
/// Anything else — `^0.7`, `>=0.7`, a bare `<0.8`, multiple `||` ranges, or an
/// unparseable form — is rejected (fail-closed).
fn pragma_is_0_8_plus(ver: &str) -> bool {
    if ver.contains("||") {
        return false; // disjunction: too permissive to prove
    }
    let toks: Vec<&str> = ver.split_whitespace().collect();
    let mut saw_lower_ok = false;
    let mut i = 0;
    while i < toks.len() {
        // Split an operator prefix off the token (longer ops first). `<=` before
        // `<`, `>=` before `>`.
        let (op, mut rest): (&str, &str) = if let Some(r) = toks[i].strip_prefix(">=") {
            (">=", r)
        } else if let Some(r) = toks[i].strip_prefix("<=") {
            ("<=", r)
        } else if let Some(r) = toks[i].strip_prefix('^') {
            ("^", r)
        } else if let Some(r) = toks[i].strip_prefix('>') {
            (">", r)
        } else if let Some(r) = toks[i].strip_prefix('<') {
            ("<", r)
        } else if let Some(r) = toks[i].strip_prefix('=') {
            ("=", r)
        } else {
            ("=", toks[i]) // a bare `0.8.0`
        };
        // A BARE operator (`>= 0.8.0` with a space) binds to the next token.
        if rest.is_empty() {
            i += 1;
            let Some(next) = toks.get(i) else {
                return false; // dangling operator with no version
            };
            rest = next;
        }
        let Some((maj, min)) = parse_major_minor(rest) else {
            return false;
        };
        match op {
            ">=" | "^" | "=" | ">" => {
                // The lower bound must be exactly the 0.8.x line: Solidity is `0.x`
                // only, so a fabricated major (`^2.0.0`, `1.0.0`) is rejected too.
                if !(maj == 0 && min >= 8) {
                    return false;
                }
                saw_lower_ok = true;
            }
            // Upper bounds are fine as long as a valid lower bound is also present.
            "<" | "<=" => {}
            _ => return false,
        }
        i += 1;
    }
    saw_lower_ok
}

/// Parse a `major.minor[.patch]` version like `0.8.0` / `0.8`. Returns `None` on
/// anything non-numeric OR with trailing junk (`0.8.x`, `0.8.0.1`), so a malformed
/// version fails closed rather than parsing the numeric prefix and ignoring the rest.
fn parse_major_minor(v: &str) -> Option<(u32, u32)> {
    let parts: Vec<&str> = v.split('.').collect();
    if parts.is_empty() || parts.len() > 3 {
        return None;
    }
    let maj: u32 = parts[0].parse().ok()?;
    let min: u32 = parts.get(1).copied().unwrap_or("0").parse().ok()?;
    if let Some(patch) = parts.get(2) {
        patch.parse::<u32>().ok()?; // a present patch must be numeric (no trailing junk)
    }
    Some((maj, min))
}

/// Parse a narrow `uintN` type name → its bit-width, for N a multiple of 8 in `8..=248`.
/// `uint256`/`uint` are NOT matched here (they resolve to `U256`); `uint264`, `uint7`,
/// `uint0`, and a bare `uint` return `None` (→ FE410). `pub(super)` so `emit::map_type`
/// can recognize the same set when lowering to the `u256` carrier.
pub(super) fn parse_uint_width(name: &str) -> Option<u16> {
    let rest = name.strip_prefix("uint")?;
    let n: u16 = rest.parse().ok()?;
    if (8..=248).contains(&n) && n.is_multiple_of(8) {
        Some(n)
    } else {
        None
    }
}

/// NC-S2/NC-S5 + NC-L3: resolve a declared type to its `SolTy`, enforcing the
/// allow-list. `address` is admitted (a distinct type). `mapping(K => V)` is admitted
/// ONLY in state-field position (single-level; `K`,`V` ∈ {address, uint256/uint}).
fn resolve_ty(
    t: &TypeRef,
    pos: TyPos,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<SolTy, FrontendDiag> {
    match t {
        TypeRef::Scalar { name, span } => match name.as_str() {
            "uint256" | "uint" => Ok(SolTy::U256),
            "address" => Ok(SolTy::Address),
            "bool" => Ok(SolTy::Bool),
            // SOL-ACCESS: `bytes32` is a full-width 256-bit opaque id (an AccessControl
            // role, a keccak hash) → the `u256` carrier — exactly the `address → u256`
            // precedent (256 bits, no truncation). ONLY the full width is unambiguous:
            // every `bytesN` (N<32) is LEFT-aligned in Solidity and stays FE410 (EX-3;
            // v1 has no left-alignment model and no bytes32 bitwise/arith).
            "bytes32" => Ok(SolTy::U256),
            // SOL-uintN: a narrow `uint8`..`uint248` (multiple of 8) → a width-carrying
            // distinct type lowering to the `u256` carrier. `uint256`/`uint` matched above.
            other if let Some(n) = parse_uint_width(other) => Ok(SolTy::UintN(n)),
            // SOL-ENUM: a name matching a declared `enum` → its nominal tag type (lowers to
            // u256). Enum and struct names are disjoint (validate_user_identifiers, EX-5).
            other if enums.iter().any(|e| e.name == *other) => Ok(SolTy::Enum(other.to_string())),
            // SOL-STRUCT: a name matching a declared `struct` → its nominal type. (Map
            // key/value positions use `resolve_map_*`, which never reach here, so a
            // struct-valued mapping stays FE441 — EX-3.)
            other if structs.iter().any(|s| s.name == *other) => {
                Ok(SolTy::Named(other.to_string()))
            }
            other => Err(FrontendDiag::new(
                codes::FE410_UNSUPPORTED_TYPE,
                format!(
                    "type `{other}` is outside the SOL allow-set {{uint8..uint256 (×8), bool, address, bytes32, struct, enum}} (no non-multiple-of-8 / >256 widths, signed ints, or bytesN for N<32)"
                ),
                span.clone(),
            )),
        },
        TypeRef::Mapping { key, value, span } => {
            if pos != TyPos::StateField {
                return Err(FrontendDiag::new(
                    codes::FE410_UNSUPPORTED_TYPE,
                    "a `mapping` type is only allowed for a state variable (mappings are storage-only)",
                    span.clone(),
                ));
            }
            let k = resolve_map_key(key)?;
            let v = resolve_map_value(value)?;
            Ok(SolTy::Map {
                key: Box::new(k),
                value: Box::new(v),
            })
        }
        // SOL-AIRDROP (Rung C): a dynamic array `T[]` — accepted ONLY as a function
        // PARAMETER (the airdrop recipients/amounts arrays), for a scalar u256-carrier
        // element. Any other position → FE491 (fail-closed).
        TypeRef::Array { elem, span } => {
            if pos != TyPos::Param {
                return Err(FrontendDiag::new(
                    codes::FE491_ARRAY_TYPE_SOL,
                    "a dynamic array type is only allowed as a function PARAMETER (the airdrop recipients/amounts arrays); array state variables, locals, and return types are unsupported",
                    span.clone(),
                ));
            }
            // Element allow-set = a map key's (address/uint256/bytes32); a bool/nested/
            // mapping element rejects (FE441/FE440) via `resolve_map_key`.
            let e = resolve_map_key(elem)?;
            Ok(SolTy::Array(Box::new(e)))
        }
    }
}

/// A mapping KEY: `address`, `uint256`/`uint`, or `bytes32` (all u256-carrier) only.
/// A `bool` KEY stays FE441 (a 2-slot "map" is not the bounded-ledger shape and no
/// real contract keys storage by bool); a mapping-typed key → FE440.
fn resolve_map_key(t: &TypeRef) -> Result<SolTy, FrontendDiag> {
    match t {
        TypeRef::Scalar { name, span } => match name.as_str() {
            "uint256" | "uint" => Ok(SolTy::U256),
            "address" => Ok(SolTy::Address),
            // SOL-ACCESS: a `bytes32` map key → the `u256` carrier, so a
            // `mapping(bytes32 => …)` (AccessControl roles as keys) resolves. bytesN
            // (N<32) is unsupported below (EX-3).
            "bytes32" => Ok(SolTy::U256),
            "bool" => Err(FrontendDiag::new(
                codes::FE441_BAD_MAP_KV_SOL,
                "a `bool`-KEYED mapping is unsupported (keys must be address/uint256/bytes32; a bool VALUE is supported)",
                span.clone(),
            )),
            // Also the VALUE-position fallthrough (`resolve_map_value_scalar` defers here),
            // so the message covers both.
            other => Err(FrontendDiag::new(
                codes::FE441_BAD_MAP_KV_SOL,
                format!(
                    "mapping key/value type `{other}` is unsupported (keys: address/uint256/bytes32; values also bool)"
                ),
                span.clone(),
            )),
        },
        TypeRef::Mapping { span, .. } => Err(FrontendDiag::new(
            codes::FE440_NESTED_MAPPING_SOL,
            "mapping nesting deeper than 2 levels (or a mapping-typed key) is unsupported (a faithful unbounded nested store has no bounded analog)",
            span.clone(),
        )),
        TypeRef::Array { span, .. } => Err(FrontendDiag::new(
            codes::FE441_BAD_MAP_KV_SOL,
            "an array type is not a valid mapping key or value (arrays appear only as airdrop parameters)",
            span.clone(),
        )),
    }
}

/// A mapping's SCALAR value: everything a key admits, PLUS `bool` (SOL-ACCESS EX-4:
/// stored as the u256 carrier with true=1/false=0 EXACTLY — `lower_bool_maps` rewrites
/// literal writes to `1`/`0` and wraps reads as `(… == 1)`, so no lax truthiness can
/// exist in storage, MC-6). The AccessControl `hasRole` field is `mapping(address =>
/// bool)`; a plain blocklist is the same shape one level up.
fn resolve_map_value_scalar(t: &TypeRef) -> Result<SolTy, FrontendDiag> {
    match t {
        TypeRef::Scalar { name, .. } if name == "bool" => Ok(SolTy::Bool),
        _ => resolve_map_key(t),
    }
}

/// A mapping VALUE: a scalar (single-level map), OR a single-level nested mapping
/// (the SOL-ERC20 two-key `allowance` shape). The inner mapping's key AND value must
/// both be scalars — so nesting is bounded at EXACTLY 2 levels (EX-5); a third level
/// makes the inner value a mapping → FE440 via `resolve_map_key`.
fn resolve_map_value(t: &TypeRef) -> Result<SolTy, FrontendDiag> {
    match t {
        TypeRef::Scalar { .. } => resolve_map_value_scalar(t),
        TypeRef::Mapping { key, value, .. } => {
            let ik = resolve_map_key(key)?;
            let iv = resolve_map_value_scalar(value)?;
            Ok(SolTy::Map {
                key: Box::new(ik),
                value: Box::new(iv),
            })
        }
        TypeRef::Array { span, .. } => Err(FrontendDiag::new(
            codes::FE441_BAD_MAP_KV_SOL,
            "an array type is not a valid mapping value (arrays appear only as airdrop parameters)",
            span.clone(),
        )),
    }
}

/// The `SolTy` of `field` in struct `sname`, or `None` if either is unknown. Field
/// types are guaranteed resolvable by `validate_struct_defs` (run eagerly in `check`).
fn struct_field_ty(structs: &[Struct], enums: &[Enum], sname: &str, field: &str) -> Option<SolTy> {
    let sdef = structs.iter().find(|s| s.name == sname)?;
    let f = sdef.fields.iter().find(|f| f.name == field)?;
    resolve_ty(&f.ty, TyPos::Local, structs, enums).ok()
}

/// SOL-STRUCT eager validation of every `struct` definition (run once in `check`,
/// before any use): non-empty (FE461), no duplicate field (FE460), every field type
/// resolves and is a scalar or another struct — a `mapping`/array/unknown field is
/// rejected (EX-3 → FE461/FE410) — and no self-reference cycle (EX-5 → FE461).
fn validate_struct_defs(structs: &[Struct], enums: &[Enum]) -> Result<(), FrontendDiag> {
    for s in structs {
        if s.fields.is_empty() {
            return Err(FrontendDiag::new(
                codes::FE461_BAD_STRUCT_SHAPE_SOL,
                format!(
                    "struct `{}` has no fields (an empty struct is unsupported)",
                    s.name
                ),
                s.span.clone(),
            ));
        }
        let mut seen: HashSet<&str> = HashSet::new();
        for f in &s.fields {
            if !seen.insert(f.name.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE460_STRUCT_FIELD_MISMATCH_SOL,
                    format!("struct `{}` has a duplicate field `{}`", s.name, f.name),
                    f.span.clone(),
                ));
            }
            match &f.ty {
                // A struct may hold only scalars or other structs — never a mapping
                // (a struct is a value-typed record, not a bounded-container holder).
                TypeRef::Mapping { span, .. } => {
                    return Err(FrontendDiag::new(
                        codes::FE461_BAD_STRUCT_SHAPE_SOL,
                        format!(
                            "struct `{}` field `{}` is a mapping; a struct may hold only scalars or other structs",
                            s.name, f.name
                        ),
                        span.clone(),
                    ));
                }
                // resolve_ty enforces the scalar allow-list OR a known struct name.
                TypeRef::Scalar { .. } => {
                    resolve_ty(&f.ty, TyPos::Local, structs, enums)?;
                }
                TypeRef::Array { span, .. } => {
                    return Err(FrontendDiag::new(
                        codes::FE461_BAD_STRUCT_SHAPE_SOL,
                        format!(
                            "struct `{}` field `{}` is an array; a struct may hold only scalars or other structs",
                            s.name, f.name
                        ),
                        span.clone(),
                    ));
                }
            }
        }
    }
    detect_struct_cycle(structs)?;
    Ok(())
}

/// SOL-ENUM eager validation (EX-4): a non-empty enum (≥1 member; an empty enum has no valid
/// zero-default) with no duplicate member name (a dup would silently alias two tags to the
/// same index via `position()`). Both → FE467, before the member-lowering pass runs.
fn validate_enum_defs(enums: &[Enum]) -> Result<(), FrontendDiag> {
    for e in enums {
        if e.members.is_empty() {
            return Err(FrontendDiag::new(
                codes::FE467_BAD_ENUM_SHAPE_SOL,
                format!(
                    "enum `{}` has no members (an empty enum is unsupported)",
                    e.name
                ),
                e.span.clone(),
            ));
        }
        let mut seen: HashSet<&str> = HashSet::new();
        for m in &e.members {
            if !seen.insert(m.as_str()) {
                return Err(FrontendDiag::new(
                    codes::FE467_BAD_ENUM_SHAPE_SOL,
                    format!("enum `{}` has a duplicate member `{}`", e.name, m),
                    e.span.clone(),
                ));
            }
        }
    }
    Ok(())
}

/// EX-5: reject a struct that contains itself by value (directly or transitively) — an
/// infinite-size record. A DFS over struct-typed fields; a back-edge to an on-stack
/// struct is a cycle → FE461. Bounded by the struct count (the on-stack set prevents
/// revisiting, so it always terminates).
fn detect_struct_cycle(structs: &[Struct]) -> Result<(), FrontendDiag> {
    fn visit(
        name: &str,
        structs: &[Struct],
        stack: &mut Vec<String>,
        done: &mut HashSet<String>,
    ) -> Result<(), FrontendDiag> {
        if done.contains(name) {
            return Ok(());
        }
        if stack.iter().any(|n| n == name) {
            let cyc = structs
                .iter()
                .find(|s| s.name == name)
                .expect("on-stack name exists");
            return Err(FrontendDiag::new(
                codes::FE461_BAD_STRUCT_SHAPE_SOL,
                format!(
                    "struct `{name}` is self-referential (a struct cannot contain itself by value)"
                ),
                cyc.span.clone(),
            ));
        }
        // Totality (adversarial-review finding): struct→struct-field references are a NEW
        // recursion axis the parser's per-body MAX_NEST_DEPTH never measured. Without a
        // cap, a deep linear chain (or a deep cycle, before its closing edge) overflows
        // the native stack HERE, and — via `zero_default`→`parse_self_check` — in the
        // trusted parser (~depth 18). `stack.len()` is the live depth; capping at
        // MAX_NEST_DEPTH (12, < 18) rejects deep chains as FE402 before any overflow, and
        // (since check runs before emit) bounds `zero_default` + the emitted nested literal.
        if stack.len() >= super::parser::MAX_NEST_DEPTH as usize {
            let cur = structs.iter().find(|s| s.name == name);
            return Err(FrontendDiag::new(
                codes::FE402_TOO_LARGE_SOL,
                format!(
                    "struct reference nesting exceeds the depth limit of {}",
                    super::parser::MAX_NEST_DEPTH
                ),
                cur.map(|s| s.span.clone()).unwrap_or(0..0),
            ));
        }
        stack.push(name.to_string());
        if let Some(s) = structs.iter().find(|s| s.name == name) {
            for f in &s.fields {
                if let TypeRef::Scalar { name: fname, .. } = &f.ty
                    && structs.iter().any(|s2| s2.name == *fname)
                {
                    visit(fname, structs, stack, done)?;
                }
            }
        }
        stack.pop();
        done.insert(name.to_string());
        Ok(())
    }
    let mut done: HashSet<String> = HashSet::new();
    for s in structs {
        let mut stack: Vec<String> = Vec::new();
        visit(&s.name, structs, &mut stack, &mut done)?;
    }
    Ok(())
}

fn check_identifier(name: &str, span: Range<usize>, what: &str) -> Result<(), FrontendDiag> {
    if !is_legal_identifier(name) {
        return Err(FrontendDiag::new(
            codes::FE420_BAD_IDENTIFIER_SOL,
            format!("{what} `{name}` is not a legal SIGIL identifier"),
            span,
        ));
    }
    if name.starts_with(SYNTH_PREFIX) || is_sigil_keyword(name) {
        return Err(FrontendDiag::new(
            codes::FE420_BAD_IDENTIFIER_SOL,
            format!(
                "{what} `{name}` collides with a SIGIL keyword or the reserved `{SYNTH_PREFIX}` prefix"
            ),
            span,
        ));
    }
    // The EVM globals are reserved: a user identifier shadowing `msg`/`tx`/`block`
    // would make the `msg.sender` → `__fe_sender` rewrite (desugar.rs) ambiguous.
    // SOL-ACCESS adds `keccak256`: the parser folds `keccak256("literal")` to a
    // precomputed constant, so a USER function of that name (solc historically only
    // WARNS on builtin shadowing) would have its literal calls silently folded
    // instead of dispatched — reject the declaration fail-closed instead.
    if matches!(name, "msg" | "tx" | "block" | "keccak256") {
        return Err(FrontendDiag::new(
            codes::FE420_BAD_IDENTIFIER_SOL,
            format!("{what} `{name}` collides with a reserved EVM global or builtin"),
            span,
        ));
    }
    // SOL-EVENTS: a Solidity elementary-type name (`address`/`payable`/`bool`/`uintN`/`bytesN`/…) is
    // a reserved keyword in solc, so no valid contract names a function/variable one. The frontend's
    // lexer admits them as plain idents, though — and `emit_arg_discard_safe` treats a `Call` to such
    // a name as a PURE cast, so a user `function payable(){ state mutation }` invoked inside a
    // discarded `emit` would be silently dropped. Reject the collision here (fail-closed; matches what
    // solc already rejects), closing that discard hole at the identifier gate.
    if super::parser::is_elementary_cast(name) {
        return Err(FrontendDiag::new(
            codes::FE420_BAD_IDENTIFIER_SOL,
            format!("{what} `{name}` collides with a Solidity elementary type name (reserved)"),
            span,
        ));
    }
    // `self` (the emitted method receiver, emit.rs) and `new` (the emitted
    // constructor, emit.rs) are emitter-OWNED names. Neither is a SIGIL keyword, so
    // the guard above misses them — but a user identifier colliding with either
    // produces a duplicate emitted binding (`fn f(self: C, self: u256)` → N005;
    // a second `new` in the impl → N002) that the FE500 parse self-check cannot see
    // (both are name-resolution errors). Reject up front so a collision is a clean
    // FE420, never a confusing downstream N-code on otherwise-legal input.
    if matches!(name, "self" | "new") {
        return Err(FrontendDiag::new(
            codes::FE420_BAD_IDENTIFIER_SOL,
            format!(
                "{what} `{name}` collides with a synthesized name (the emitted method receiver `self` / constructor `new`)"
            ),
            span,
        ));
    }
    Ok(())
}

/// Validate every USER-authored identifier — contract / state / function / parameter
/// / LOCAL — BEFORE the desugar pass injects any synthesized name. This is the SOLE
/// place the reserved `__fe_` prefix, SIGIL keywords, and EVM globals (`msg`/`tx`/
/// `block`) are rejected for user code (FE420). Because it runs pre-desugar, the
/// synthesized names — the `__fe_sender` caller param and the `__fe_N` `&&`/`||`
/// temps — are injected AFTER this gate and so can NEVER be confused with, or
/// collided by, a user identifier of the same name (the bug class the SOL1b
/// adversarial review found: a user `__fe_sender` param aliasing a transfer to a
/// net-zero no-op; a user `__fe_0` local clobbering a guard temp). `check`/`emit`
/// therefore do NOT re-validate identifiers.
pub fn validate_user_identifiers(p: &Program) -> Result<(), FrontendDiag> {
    check_identifier(&p.contract.name, p.contract.span.clone(), "contract name")?;
    // The frontend emits the stdlib map types (`BoundedMap_u256_u256_64`, and for a
    // nested mapping `BoundedMap2_u256_u256_u256_64`) for `mapping` fields; a contract
    // named the same SHADOWS the injected stdlib (the emitted `record BoundedMap…` flips
    // ambient-injection suppression), so a field initializer `…::new()` resolves to the
    // user record's `new` — and under cap-mode that `new` is arity-changed, ICE-ing the
    // trusted re-verifier (adversarial-review finding, for BOTH the single- and two-key
    // map). Reject ANY `BoundedMap*` contract name (a general fix; nobody names a contract
    // this), before the malformed emission can reach the trusted compiler.
    if p.contract.name.starts_with("BoundedMap") {
        return Err(FrontendDiag::new(
            codes::FE420_BAD_IDENTIFIER_SOL,
            format!(
                "contract name `{}` collides with a stdlib bounded-map type the frontend emits for `mapping` fields",
                p.contract.name
            ),
            p.contract.span.clone(),
        ));
    }
    let mut seen_state: HashSet<&str> = HashSet::new();
    for sv in &p.contract.state {
        check_identifier(&sv.name, sv.span.clone(), "state variable")?;
        // Two state variables sharing a name emit a malformed `record C { a: …, a: … }`. The
        // trusted compiler accepts a duplicate-field record (fail-open), so a later read silently
        // resolves to one field while the other is dead = silent mis-initialization. Real solc
        // rejects duplicate state vars, so only hand-crafted/invalid input reaches this, but the
        // untrusted translator must reject it fail-closed rather than emit malformed SIGIL.
        if !seen_state.insert(sv.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "duplicate state variable `{}` — two same-named state variables would emit a malformed record (duplicate field)",
                    sv.name
                ),
                sv.span.clone(),
            ));
        }
    }
    let mut seen_fns: HashSet<(&str, usize)> = HashSet::new();
    for f in &p.contract.functions {
        check_identifier(&f.name, f.span.clone(), "function name")?;
        // A user function named `new` collides with the synthesized `new()` constructor —
        // two impl-methods named `new` are an N002 duplicate at name-resolution (invisible
        // to the FE500 parse self-check). Reject it (found by the SOL-CAP review).
        if f.name == "new" {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                "function name `new` collides with the synthesized `new()` constructor",
                f.span.clone(),
            ));
        }
        // SOL-XFILE PR3/OVL: this gate runs BEFORE `desugar::disambiguate_overloads` mangles a
        // same-name/different-arity overload set to unique names, so it keys by (name, ARITY) —
        // a distinct-arity overload is tolerated here (mangled downstream); only a same-name
        // SAME-arity pair (which arg-count cannot disambiguate) is rejected fail-closed FE420.
        if !seen_fns.insert((f.name.as_str(), f.params.len())) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "duplicate function `{}` (same name AND arity) — Solidity same-arity overloading is unsupported (SIGIL impl methods must be uniquely named)",
                    f.name
                ),
                f.span.clone(),
            ));
        }
        for prm in &f.params {
            check_identifier(&prm.name, prm.span.clone(), "parameter")?;
        }
        validate_local_idents(&f.body)?;
    }
    // SOL1c: a modifier's name + its body locals are USER identifiers that get spliced
    // into functions by `inline_modifiers` (which runs AFTER this gate). Validate them
    // here, at the declaration, so an illegal/reserved modifier name or body local can
    // never reach inlining (FE420). Applied modifier NAMES in `Function.modifiers` are
    // resolved against these declarations, so checking the decls covers them.
    for m in &p.contract.modifiers {
        check_identifier(&m.name, m.span.clone(), "modifier name")?;
        validate_local_idents(&m.body)?;
    }
    // SOL-STRUCT (EX-6): struct names + field names are user identifiers emitted as
    // top-level `record`s. Reject illegal/reserved names, a `BoundedMap*` collision
    // (shadows the injected stdlib), a clash with the contract name (two records → N002),
    // and duplicate struct names.
    let mut seen_structs: HashSet<&str> = HashSet::new();
    for st in &p.contract.structs {
        check_identifier(&st.name, st.span.clone(), "struct name")?;
        if st.name.starts_with("BoundedMap") {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "struct name `{}` collides with a stdlib bounded-map type the frontend emits",
                    st.name
                ),
                st.span.clone(),
            ));
        }
        // A struct named after a SIGIL BUILTIN type (`u256`, `bool`, …) emits `record
        // <builtin>`, which collides with the primitive in the trust anchor (T071/T122,
        // not a clean diagnostic). These are NOT Solidity tokens (unlike `address`/`bool`/
        // `uint256`, which `resolve_ty` intercepts), so they slip past `check_identifier`
        // as plain idents — reject here, fail-closed (adversarial-review wart).
        const SIGIL_BUILTIN_TYPES: &[&str] = &[
            "unit", "bool", "str", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f64",
            "u256", "i256",
        ];
        if SIGIL_BUILTIN_TYPES.contains(&st.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "struct name `{}` collides with a SIGIL builtin type",
                    st.name
                ),
                st.span.clone(),
            ));
        }
        if st.name == p.contract.name {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!("struct name `{}` collides with the contract name", st.name),
                st.span.clone(),
            ));
        }
        if !seen_structs.insert(st.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!("duplicate struct name `{}`", st.name),
                st.span.clone(),
            ));
        }
        for f in &st.fields {
            check_identifier(&f.name, f.span.clone(), "struct field")?;
        }
    }
    // SOL-ENUM (EX-5): an enum name drives the type-name→`u256` lowering, so it runs the
    // SAME hygiene as a struct name (illegal/reserved, `BoundedMap*`, SIGIL builtin,
    // contract-name clash, duplicate) — PLUS enum-vs-struct disjointness (a name shared by
    // an enum and a struct would have two `resolve_ty` meanings). Member names are NOT
    // checked: they are erased to index literals (never emitted as identifiers).
    let mut seen_enums: HashSet<&str> = HashSet::new();
    for en in &p.contract.enums {
        check_identifier(&en.name, en.span.clone(), "enum name")?;
        if en.name.starts_with("BoundedMap") {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "enum name `{}` collides with a stdlib bounded-map type the frontend emits",
                    en.name
                ),
                en.span.clone(),
            ));
        }
        const SIGIL_BUILTIN_TYPES: &[&str] = &[
            "unit", "bool", "str", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f64",
            "u256", "i256",
        ];
        if SIGIL_BUILTIN_TYPES.contains(&en.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!("enum name `{}` collides with a SIGIL builtin type", en.name),
                en.span.clone(),
            ));
        }
        if en.name == p.contract.name {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!("enum name `{}` collides with the contract name", en.name),
                en.span.clone(),
            ));
        }
        if seen_structs.contains(en.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "enum name `{}` collides with a struct name (a name cannot be both an enum and a struct)",
                    en.name
                ),
                en.span.clone(),
            ));
        }
        if !seen_enums.insert(en.name.as_str()) {
            return Err(FrontendDiag::new(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!("duplicate enum name `{}`", en.name),
                en.span.clone(),
            ));
        }
    }
    // SOL-CTOR: the constructor's params + body locals are user identifiers spliced into the
    // synthesized `new()`. Validate them here (before desugar injects `__fe_sender`), so a
    // ctor param/local named `__fe_*`/`msg`/a keyword can't alias a synthesized name (EX-6,
    // the SOL1b synth-collision bug class).
    if let Some(ctor) = &p.contract.constructor {
        for prm in &ctor.params {
            check_identifier(&prm.name, prm.span.clone(), "constructor parameter")?;
        }
        validate_local_idents(&ctor.body)?;
    }
    Ok(())
}

/// Recursively validate every `LocalVar` binding name (the only name-binding
/// statement; `Assign`/`IndexAssign` targets are existing names). Runs on the
/// PARSED body, before desugar, so it sees only user locals.
fn validate_local_idents(stmts: &[Stmt]) -> Result<(), FrontendDiag> {
    for s in stmts {
        match s {
            Stmt::LocalVar { name, span, .. } => {
                check_identifier(name, span.clone(), "local variable")?
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                validate_local_idents(then_body)?;
                validate_local_idents(else_body)?;
            }
            // SOL-UNCHECKED: `unwrap_unchecked` runs AFTER this validation and alpha-renames the
            // block's top-level locals to `__fe_unchk*`; recurse so a user local declared inside an
            // `unchecked` block is still validated (incl. the reserved `__fe_` prefix reject) here,
            // BEFORE that rename injects a synthesized name.
            Stmt::Unchecked { body, .. } => validate_local_idents(body)?,
            _ => {}
        }
    }
    Ok(())
}

/// SOL-CTOR: check a `constructor` body. Mirrors `check_function` but with no return type,
/// `in_constructor = true` (CEI-moot — EX-2; an explicit `return` → FE464), and no view/pure
/// check (a constructor has no mutability). The env starts from the state fields + ctor
/// params, exactly like a method.
fn check_constructor(
    ctor: &Constructor,
    state: &HashSet<&str>,
    state_tys: &HashMap<String, SolTy>,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    let mut tys: HashMap<String, SolTy> = state_tys.clone();
    for p in &ctor.params {
        let pty = resolve_ty(&p.ty, TyPos::Param, structs, enums)?;
        tys.insert(p.name.clone(), pty);
    }
    let ctx = FnCtx {
        state,
        ret: None,
        in_constructor: true,
    };
    let mut committed_write = false;
    let mut locals: HashSet<String> = ctor.params.iter().map(|p| p.name.clone()).collect();
    check_stmts(
        &ctor.body,
        &ctx,
        &mut locals,
        &mut tys,
        &mut committed_write,
        structs,
        enums,
    )
}

fn check_function(
    f: &Function,
    state: &HashSet<&str>,
    state_tys: &HashMap<String, SolTy>,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    // Identifiers were validated pre-desugar by `validate_user_identifiers`; the
    // synthesized `__fe_sender` param injected by desugar is trusted (never re-checked).
    // The type env starts from the state fields, then gains params.
    let mut tys: HashMap<String, SolTy> = state_tys.clone();
    for p in &f.params {
        let pty = resolve_ty(&p.ty, TyPos::Param, structs, enums)?;
        tys.insert(p.name.clone(), pty);
    }
    let ret = match &f.ret {
        Some(rt) => Some(resolve_ty(rt, TyPos::Return, structs, enums)?),
        None => None,
    };
    let ctx = FnCtx {
        state,
        ret,
        in_constructor: false,
    };
    // `locals` (params, grown with each LocalVar) mirrors emit::resolve_name so a
    // name that SHADOWS a state field is NOT mis-counted as a storage write.
    let mut committed_write = false;
    let mut locals: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
    check_stmts(
        &f.body,
        &ctx,
        &mut locals,
        &mut tys,
        &mut committed_write,
        structs,
        enums,
    )?;
    // A `view`/`pure` function may not write state (Solidity's own rule). Reject early
    // with a precise FE-code rather than emitting a non-`@Mut` method that only the
    // trusted compiler's `@ReadOnly` check would catch (a confusing downstream error).
    if committed_write && matches!(f.mutability, StateMutability::View | StateMutability::Pure) {
        return Err(FrontendDiag::new(
            codes::FE446_VIEW_WRITE_SOL,
            format!(
                "`{}` is declared view/pure but writes contract state",
                f.name
            ),
            f.span.clone(),
        ));
    }
    Ok(())
}

/// Recursively check a statement list in execution order, threading `committed_write`
/// (whether a storage-field write has already committed on this path) and the type
/// env `tys`. The conservative CEI rule (NC-S1/NC-L2): once a storage write has
/// committed, NO later trap-capable op (require/assert/revert, an expression with
/// checked `+ - * / %`, OR a map insert) may run — SIGIL's trap would not roll the
/// write back.
fn check_stmts(
    stmts: &[Stmt],
    ctx: &FnCtx,
    locals: &mut HashSet<String>,
    tys: &mut HashMap<String, SolTy>,
    committed_write: &mut bool,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    for s in stmts {
        match s {
            // SOL-CALLS: desugar's inline pass must have spliced every internal call away; a residual
            // CallStmt here is a translator bug (FE500), never a user-facing reject.
            Stmt::CallStmt { span, .. } => {
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: an internal call statement survived desugar's inline pass",
                    span.clone(),
                ));
            }
            Stmt::Unchecked { span, .. } => {
                // Unreachable: `desugar::unwrap_unchecked` splices every `unchecked` body away
                // before check (SOL-UNCHECKED). A residual node is an internal pass bug — fail
                // loud (EX-4), never silently ignore.
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: an `unchecked` block survived `unwrap_unchecked`",
                    span.clone(),
                ));
            }
            // SOL-AIRDROP: `recognize_airdrop` folds every airdrop loop into a `BatchTransfer`
            // before check; a residual loop is a fold bug — fail loud (FE500), like the residual
            // CallStmt/Unchecked above.
            Stmt::AirdropLoop { span, .. } => {
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: an airdrop loop reached the checker (must be folded by recognize_airdrop)",
                    span.clone(),
                ));
            }
            Stmt::BatchTransfer {
                map,
                from,
                recipients,
                amounts,
                span,
            } => {
                // SOL-AIRDROP (Rung C): the recognized N-ary airdrop → the TRUSTED atomic
                // `map.batch_transfer(from, recipients, amounts)` (debit `from` by each amount,
                // credit each recipient; reserve-all-then-write, aliasing-correct over N, exec-proven).
                // ONE atomic storage op (the MapSplitTransfer precedent). Type-check: the map is a
                // uint256-valued mapping; `from` is the key type; `recipients`/`amounts` are ARRAY
                // params (recipients-of-key-type, amounts-of-u256).
                let mty = tys.get(map).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("airdrop on undeclared mapping `{map}`"),
                        span.clone(),
                    )
                })?;
                let (kt, vt) = match mty {
                    SolTy::Map { key, value } => (*key, *value),
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE442_BAD_INDEX_SOL,
                            format!("`{map}` is not a mapping"),
                            span.clone(),
                        ));
                    }
                };
                require_arith_target(&vt, span.clone())?;
                let ft = infer(from, tys, structs, enums)?;
                require_assignable(&ft, &kt, from.span())?;
                // `recipients`/`amounts` are the bare ARRAY-parameter names (the recognizer only
                // matches counter-indexed arrays; the parser produces an array type only in param
                // position). Verify each is an `Array` param with the right element type.
                match tys.get(recipients) {
                    Some(SolTy::Array(elem)) => {
                        require_assignable(elem.as_ref(), &kt, span.clone())?
                    }
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE492_AIRDROP_SHAPE_SOL,
                            format!("airdrop `{recipients}` must be a dynamic-array parameter"),
                            span.clone(),
                        ));
                    }
                }
                match tys.get(amounts) {
                    Some(SolTy::Array(elem)) => {
                        require_assignable(elem.as_ref(), &SolTy::U256, span.clone())?
                    }
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE492_AIRDROP_SHAPE_SOL,
                            format!("airdrop `{amounts}` must be a dynamic-array parameter"),
                            span.clone(),
                        ));
                    }
                }
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
                if !ctx.in_constructor {
                    *committed_write = true;
                }
            }
            Stmt::Require { cond, span } | Stmt::Assert { cond, span } => {
                infer(cond, tys, structs, enums)?;
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
            }
            Stmt::Revert { span } => {
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
            }
            Stmt::Return {
                value: Some(v),
                span,
            } => {
                if ctx.in_constructor {
                    return Err(ctor_return(span.clone()));
                }
                let vty = infer(v, tys, structs, enums)?;
                if let Some(rt) = &ctx.ret {
                    require_assignable(&vty, rt, v.span())?;
                }
                if *committed_write && expr_has_checked_arith(v) {
                    return Err(non_cei(span.clone()));
                }
            }
            Stmt::Return { value: None, span } => {
                // SOL-CTOR: even a bare `return;` is rejected in a ctor (it would short-circuit
                // the synthesized tail `return __fe_c`; early-exit is a documented anti-goal).
                if ctx.in_constructor {
                    return Err(ctor_return(span.clone()));
                }
            }
            Stmt::LocalVar {
                name,
                ty,
                value,
                span,
            } => {
                let dty = resolve_ty(ty, TyPos::Local, structs, enums)?;
                let vty = infer(value, tys, structs, enums)?;
                require_assignable(&vty, &dty, value.span())?;
                if *committed_write && expr_has_checked_arith(value) {
                    return Err(non_cei(span.clone()));
                }
                // A local declaration shadows any same-named state field from here on.
                locals.insert(name.clone());
                tys.insert(name.clone(), dty);
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => check_assign_stmt(
                target,
                op,
                value,
                span,
                ctx,
                locals,
                tys,
                committed_write,
                structs,
                enums,
            )?,
            Stmt::FieldAssign {
                obj,
                field,
                op,
                value,
                span,
            } => {
                // SOL-STRUCT: a struct field write `obj.field op= value`. `obj` must be a
                // struct-typed binding and `field` a declared field of that struct.
                let oty = tys.get(obj).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE401_UNSUPPORTED_SOL,
                        format!("field assignment to undeclared variable `{obj}`"),
                        span.clone(),
                    )
                })?;
                let SolTy::Named(sname) = oty else {
                    return Err(FrontendDiag::new(
                        codes::FE410_UNSUPPORTED_TYPE,
                        format!(
                            "`{obj}.{field} = ..` writes a field of `{obj}`, which is not a struct"
                        ),
                        span.clone(),
                    ));
                };
                let fty = struct_field_ty(structs, enums, &sname, field).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE460_STRUCT_FIELD_MISMATCH_SOL,
                        format!("struct `{sname}` has no field `{field}`"),
                        span.clone(),
                    )
                })?;
                let vty = infer(value, tys, structs, enums)?;
                if *op == AssignOp::Eq {
                    require_assignable(&vty, &fty, value.span())?;
                } else {
                    // Compound `op=` on a struct field — same-width arithmetic; a `uintN`
                    // field is accepted and the M2 width-trap pass adds the trap.
                    arith_result_ty(&fty, &vty, span.clone())?;
                }
                let this_traps = expr_has_checked_arith(value) || *op != AssignOp::Eq;
                if *committed_write && this_traps {
                    return Err(non_cei(span.clone()));
                }
                // EX-4: a write to a STATE-field struct (not shadowed) is a storage commit,
                // exactly like a scalar state-field write — except in a constructor, where it
                // writes the LOCAL `__fe_c` (EX-2, CEI-moot).
                if ctx.state.contains(obj.as_str())
                    && !locals.contains(obj.as_str())
                    && !ctx.in_constructor
                {
                    *committed_write = true;
                }
            }
            Stmt::IndexAssign {
                map,
                key,
                op,
                value,
                span,
            } => check_index_assign_stmt(
                map,
                key,
                op,
                value,
                span,
                ctx,
                tys,
                committed_write,
                structs,
                enums,
            )?,
            Stmt::IndexAssign2 {
                map,
                k1,
                k2,
                op,
                value,
                span,
            } => {
                let mty = tys.get(map).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("index assignment to undeclared variable `{map}`"),
                        span.clone(),
                    )
                })?;
                // EX-5: `m[k1][k2]` requires a TWO-key mapping (a mapping whose value is
                // itself a mapping). A single-level map indexed twice → FE442.
                let (k1t, k2t, vt) = match mty {
                    SolTy::Map { key, value } => match *value {
                        SolTy::Map { key: ik, value: iv } => (*key, *ik, *iv),
                        _ => {
                            return Err(FrontendDiag::new(
                                codes::FE442_BAD_INDEX_SOL,
                                format!(
                                    "`{map}[..][..]` indexes `{map}`, a single-level mapping (one key only)"
                                ),
                                span.clone(),
                            ));
                        }
                    },
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE442_BAD_INDEX_SOL,
                            format!("`{map}[..][..] = ..` indexes `{map}`, which is not a mapping"),
                            span.clone(),
                        ));
                    }
                };
                // EX-4: type-check BOTH key positions against BOTH declared key types.
                let k1ty = infer(k1, tys, structs, enums)?;
                require_assignable(&k1ty, &k1t, k1.span())?;
                let k2ty = infer(k2, tys, structs, enums)?;
                require_assignable(&k2ty, &k2t, k2.span())?;
                let vty = infer(value, tys, structs, enums)?;
                if *op == AssignOp::Eq {
                    require_assignable(&vty, &vt, value.span())?;
                    // SOL-ACCESS EX-4: same literal-only rule as the single-key arm —
                    // the two-key bool map IS the AccessControl `hasRole` storage shape.
                    if vt == SolTy::Bool && !matches!(value, Expr::Bool(..)) {
                        return Err(FrontendDiag::new(
                            codes::FE441_BAD_MAP_KV_SOL,
                            "a bool-valued mapping write must be a `true`/`false` literal (a computed bool value is unsupported)",
                            value.span(),
                        ));
                    }
                } else {
                    require_arith_target(&vt, span.clone())?;
                    require_assignable(&vty, &SolTy::U256, value.span())?;
                }
                // EX-1: a two-key map insert is a STORAGE WRITE, always trap-capable
                // (capacity-full + checked-u256 value overflow) — the same CEI rule as
                // the single-level write: no write may follow a committed write.
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
                // CEI-moot in a constructor (the map write is on the LOCAL `__fe_c`, EX-2).
                if !ctx.in_constructor {
                    *committed_write = true;
                }
            }
            Stmt::MapTransfer {
                map,
                from,
                to,
                amount,
                span,
            } => check_map_transfer_stmt(
                map,
                from,
                to,
                amount,
                span,
                ctx,
                tys,
                committed_write,
                structs,
                enums,
            )?,
            Stmt::MapSplitTransfer {
                map,
                from,
                amount,
                to,
                net,
                fee_to,
                fee,
                span,
            } => {
                // SOL-MULTIMAP M-B: the recognized fee-on-transfer split → the TRUSTED atomic
                // `map.transfer_split(from, amount, to, net, fee_to, fee)` (aliasing-correct, all checks
                // before any write). ONE atomic storage op. Type-check: the map is a uint256-valued
                // mapping; the three keys (from/to/fee_to) are the key type; the three amounts are u256.
                let mty = tys.get(map).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("split transfer on undeclared mapping `{map}`"),
                        span.clone(),
                    )
                })?;
                let (kt, vt) = match mty {
                    SolTy::Map { key, value } => (*key, *value),
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE442_BAD_INDEX_SOL,
                            format!("`{map}` is not a mapping"),
                            span.clone(),
                        ));
                    }
                };
                require_arith_target(&vt, span.clone())?;
                for key in [from, to, fee_to] {
                    let t = infer(key, tys, structs, enums)?;
                    require_assignable(&t, &kt, key.span())?;
                }
                for val in [amount, net, fee] {
                    let t = infer(val, tys, structs, enums)?;
                    require_assignable(&t, &SolTy::U256, val.span())?;
                }
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
                if !ctx.in_constructor {
                    *committed_write = true;
                }
            }
            Stmt::Erc20Update {
                map,
                ts_field,
                from,
                to,
                value,
                span,
            } => {
                // SOL-UPDATE: the recognized OZ 5.x `_update` → the TRUSTED atomic
                // `map.erc20_update(ts, from, to, value)` (dynamic zero-address mint/burn/
                // transfer dispatch, aliasing-correct, ALL checks before any write — the
                // `eu_*` exec-proof) plus a TRAP-FREE `ts_field = <returned new_ts>`
                // store-back emitted after it. ONE atomic storage op (the Erc20TransferFrom
                // precedent). Type-check: the map is a uint256-valued mapping; the
                // totalSupply target is a numeric scalar; from/to are the key type; value
                // is u256.
                let mty = tys.get(map).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("update on undeclared mapping `{map}`"),
                        span.clone(),
                    )
                })?;
                let (kt, vt) = match mty {
                    SolTy::Map { key, value } => (*key, *value),
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE442_BAD_INDEX_SOL,
                            format!("`{map}` is not a mapping"),
                            span.clone(),
                        ));
                    }
                };
                require_arith_target(&vt, span.clone())?;
                let tsty = tys.get(ts_field).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("update targets undeclared totalSupply `{ts_field}`"),
                        span.clone(),
                    )
                })?;
                require_arith_target(&tsty, span.clone())?;
                for key in [from, to] {
                    let t = infer(key, tys, structs, enums)?;
                    require_assignable(&t, &kt, key.span())?;
                }
                let vt2 = infer(value, tys, structs, enums)?;
                require_assignable(&vt2, &SolTy::U256, value.span())?;
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
                if !ctx.in_constructor {
                    *committed_write = true;
                }
            }
            Stmt::Erc20TransferFrom {
                bal_map,
                alw_map,
                from,
                spender,
                to,
                amount,
                oz5_infinite: _,
                span,
            } => {
                // The recognized atomic ERC20 `transferFrom` (desugar::recognize_transfer_from OR
                // ::recognize_spend_transfer) → the TRUSTED `alw.transfer_from(...)` / `erc20_transfer_from(...)`,
                // which runs ALL checks across BOTH maps before any write — ONE atomic,
                // internally-CEI-safe storage op (EX-1). The operand types + CEI are identical for
                // both shapes (only `emit` differs), so `oz5_infinite` is irrelevant here. Type-check
                // the operands and apply the single-trap-capable-op CEI rule (a transferFrom after a
                // committed write still destroys funds → FE412).
                let bty = tys.get(bal_map).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("transferFrom on undeclared balances mapping `{bal_map}`"),
                        span.clone(),
                    )
                })?;
                let (bk, bv) = match bty {
                    SolTy::Map { key, value } => (*key, *value),
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE442_BAD_INDEX_SOL,
                            format!("`{bal_map}` is not a mapping"),
                            span.clone(),
                        ));
                    }
                };
                // The balances must be a single-level uint256-valued map (value arithmetic).
                require_arith_target(&bv, span.clone())?;
                let aty = tys.get(alw_map).cloned().ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        format!("transferFrom on undeclared allowance mapping `{alw_map}`"),
                        span.clone(),
                    )
                })?;
                // The allowance must be a TWO-key map (a mapping whose value is a mapping).
                let (ak1, ak2, av) = match aty {
                    SolTy::Map { key, value } => match *value {
                        SolTy::Map { key: ik, value: iv } => (*key, *ik, *iv),
                        _ => {
                            return Err(FrontendDiag::new(
                                codes::FE442_BAD_INDEX_SOL,
                                format!("`{alw_map}` is not a two-key (allowance) mapping"),
                                span.clone(),
                            ));
                        }
                    },
                    _ => {
                        return Err(FrontendDiag::new(
                            codes::FE442_BAD_INDEX_SOL,
                            format!("`{alw_map}` is not a mapping"),
                            span.clone(),
                        ));
                    }
                };
                require_arith_target(&av, span.clone())?;
                // EX-4: `from` is BOTH a balances key and the allowance's FIRST key;
                // `spender` is the allowance's SECOND key; `to` is a balances key.
                let ft = infer(from, tys, structs, enums)?;
                require_assignable(&ft, &bk, from.span())?;
                require_assignable(&ft, &ak1, from.span())?;
                let st = infer(spender, tys, structs, enums)?;
                require_assignable(&st, &ak2, spender.span())?;
                let tt = infer(to, tys, structs, enums)?;
                require_assignable(&tt, &bk, to.span())?;
                let at = infer(amount, tys, structs, enums)?;
                require_assignable(&at, &SolTy::U256, amount.span())?;
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
                // CEI-moot in a constructor (the map write is on the LOCAL `__fe_c`, EX-2).
                if !ctx.in_constructor {
                    *committed_write = true;
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => check_if_stmt(
                cond,
                then_body,
                else_body,
                ctx,
                locals,
                tys,
                committed_write,
                structs,
                enums,
            )?,
            Stmt::Placeholder { span } => {
                // Unreachable: `inline_modifiers` (desugar) removed every placeholder
                // before check. A residual one is an internal inlining bug — fail loud (E1),
                // never silently ignore.
                return Err(FrontendDiag::new(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    "internal: a modifier `_` placeholder reached the checker",
                    span.clone(),
                ));
            }
            Stmt::ReservedBatch {
                transfer,
                writes,
                span,
            } => {
                // SOL-MULTIMAP (M-A): a recognized reserve-all-then-write batch of ≥2 DISTINCT-map
                // writes — ONE atomic storage op (the MapTransfer precedent), so FE412 only if a PRIOR
                // write already committed. The nested transfer + writes are type-checked EACH as-if-first
                // (a fresh commit flag), because their mutual CEI is discharged by the reservation (every
                // deferred map reserved read-only before any write), NOT by this gate.
                if *committed_write {
                    return Err(non_cei(span.clone()));
                }
                if let Some(t) = transfer {
                    let mut inner = false;
                    check_stmts(
                        std::slice::from_ref(t.as_ref()),
                        ctx,
                        locals,
                        tys,
                        &mut inner,
                        structs,
                        enums,
                    )?;
                }
                for w in writes {
                    let mut inner = false;
                    check_stmts(
                        std::slice::from_ref(w),
                        ctx,
                        locals,
                        tys,
                        &mut inner,
                        structs,
                        enums,
                    )?;
                }
                if !ctx.in_constructor {
                    *committed_write = true;
                }
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_assign_stmt(
    target: &str,
    op: &AssignOp,
    value: &Expr,
    span: &Range<usize>,
    ctx: &FnCtx,
    locals: &HashSet<String>,
    tys: &HashMap<String, SolTy>,
    committed_write: &mut bool,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    let value_ty = infer(value, tys, structs, enums)?;
    let target_ty = tys.get(target).cloned().ok_or_else(|| {
        FrontendDiag::new(
            codes::FE401_UNSUPPORTED_SOL,
            format!("assignment to undeclared variable `{target}`"),
            span.clone(),
        )
    })?;
    if *op == AssignOp::Eq {
        require_assignable(&value_ty, &target_ty, value.span())?;
    } else {
        arith_result_ty(&target_ty, &value_ty, span.clone())?;
    }
    if *committed_write && (expr_has_checked_arith(value) || *op != AssignOp::Eq) {
        return Err(non_cei(span.clone()));
    }
    if ctx.state.contains(target) && !locals.contains(target) && !ctx.in_constructor {
        *committed_write = true;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_index_assign_stmt(
    map: &str,
    key: &Expr,
    op: &AssignOp,
    value: &Expr,
    span: &Range<usize>,
    ctx: &FnCtx,
    tys: &HashMap<String, SolTy>,
    committed_write: &mut bool,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    let map_ty = tys.get(map).cloned().ok_or_else(|| {
        FrontendDiag::new(
            codes::FE442_BAD_INDEX_SOL,
            format!("index assignment to undeclared variable `{map}`"),
            span.clone(),
        )
    })?;
    let (key_ty, value_ty) = match map_ty {
        SolTy::Map { key, value } => (*key, *value),
        _ => {
            return Err(FrontendDiag::new(
                codes::FE442_BAD_INDEX_SOL,
                format!("`{map}[..] = ..` indexes `{map}`, which is not a mapping"),
                span.clone(),
            ));
        }
    };
    require_assignable(&infer(key, tys, structs, enums)?, &key_ty, key.span())?;
    let supplied_value_ty = infer(value, tys, structs, enums)?;
    if *op == AssignOp::Eq {
        require_assignable(&supplied_value_ty, &value_ty, value.span())?;
        if value_ty == SolTy::Bool && !matches!(value, Expr::Bool(..)) {
            return Err(FrontendDiag::new(
                codes::FE441_BAD_MAP_KV_SOL,
                "a bool-valued mapping write must be a `true`/`false` literal (a computed bool value is unsupported)",
                value.span(),
            ));
        }
    } else {
        require_arith_target(&value_ty, span.clone())?;
        require_assignable(&supplied_value_ty, &SolTy::U256, value.span())?;
    }
    if *committed_write {
        return Err(non_cei(span.clone()));
    }
    if !ctx.in_constructor {
        *committed_write = true;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_map_transfer_stmt(
    map: &str,
    from: &Expr,
    to: &Expr,
    amount: &Expr,
    span: &Range<usize>,
    ctx: &FnCtx,
    tys: &HashMap<String, SolTy>,
    committed_write: &mut bool,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    let map_ty = tys.get(map).cloned().ok_or_else(|| {
        FrontendDiag::new(
            codes::FE442_BAD_INDEX_SOL,
            format!("transfer on undeclared mapping `{map}`"),
            span.clone(),
        )
    })?;
    let (key_ty, value_ty) = match map_ty {
        SolTy::Map { key, value } => (*key, *value),
        _ => {
            return Err(FrontendDiag::new(
                codes::FE442_BAD_INDEX_SOL,
                format!("`{map}` is not a mapping"),
                span.clone(),
            ));
        }
    };
    require_arith_target(&value_ty, span.clone())?;
    require_assignable(&infer(from, tys, structs, enums)?, &key_ty, from.span())?;
    require_assignable(&infer(to, tys, structs, enums)?, &key_ty, to.span())?;
    require_assignable(
        &infer(amount, tys, structs, enums)?,
        &SolTy::U256,
        amount.span(),
    )?;
    if *committed_write {
        return Err(non_cei(span.clone()));
    }
    if !ctx.in_constructor {
        *committed_write = true;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_if_stmt(
    condition: &Expr,
    then_body: &[Stmt],
    else_body: &[Stmt],
    ctx: &FnCtx,
    locals: &HashSet<String>,
    tys: &HashMap<String, SolTy>,
    committed_write: &mut bool,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<(), FrontendDiag> {
    infer(condition, tys, structs, enums)?;
    if *committed_write && expr_has_checked_arith(condition) {
        return Err(non_cei(condition.span()));
    }

    let mut then_write = *committed_write;
    let mut then_locals = locals.clone();
    let mut then_types = tys.clone();
    check_stmts(
        then_body,
        ctx,
        &mut then_locals,
        &mut then_types,
        &mut then_write,
        structs,
        enums,
    )?;

    let mut else_write = *committed_write;
    let mut else_locals = locals.clone();
    let mut else_types = tys.clone();
    check_stmts(
        else_body,
        ctx,
        &mut else_locals,
        &mut else_types,
        &mut else_write,
        structs,
        enums,
    )?;
    *committed_write = then_write || else_write;
    Ok(())
}

fn non_cei(span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE412_NON_CEI,
        "non checks-then-effects: a trap-capable operation (require/revert/assert, checked +-*/%, \
         or a map insert) follows a storage write. SIGIL's trap does not roll back prior writes \
         like Solidity's atomic revert, so compute all values and run all guards BEFORE writing \
         any storage field.",
        span,
    )
}

/// FE464 — an explicit `return` in a constructor body (a Solidity ctor has no return value,
/// and our emit appends the sole `return __fe_c`; an interior return would short-circuit it).
fn ctor_return(span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE464_UNSUPPORTED_CTOR_SOL,
        "an explicit `return` is unsupported in a constructor (it has no return value)",
        span,
    )
}

/// Infer a value expression's `SolTy`, rejecting every form outside the closed
/// SOL1 lowering table (member access, calls, `&&`/`||`) AND every `address`
/// misuse (arithmetic, ordering, or a silent `address`↔`uint256` mix).
fn infer(
    e: &Expr,
    tys: &HashMap<String, SolTy>,
    structs: &[Struct],
    enums: &[Enum],
) -> Result<SolTy, FrontendDiag> {
    match e {
        Expr::Num(t, _) => Ok(SolTy::Num { lit: t.clone() }),
        Expr::Bool(..) => Ok(SolTy::Bool),
        Expr::Var(name, span) => tys.get(name).cloned().ok_or_else(|| {
            FrontendDiag::new(
                codes::FE401_UNSUPPORTED_SOL,
                format!("unresolved reference `{name}`"),
                span.clone(),
            )
        }),
        // SOL-STRUCT: field access `base.field` on a struct-typed value. (`msg.sender`
        // is rewritten away by desugar before check; any Member reaching here is a
        // struct field access or an error.)
        Expr::Member(base, member, span) => {
            // The EVM globals are not values: `msg.sender` was rewritten by desugar, so
            // any remaining `msg.*`/`tx.*`/`block.*` is an unsupported member (FE410) —
            // kept precise rather than the "unresolved `msg`" FE401 from inferring it.
            if let Expr::Var(g, _) = base.as_ref()
                && matches!(g.as_str(), "msg" | "tx" | "block")
            {
                return Err(FrontendDiag::new(
                    codes::FE410_UNSUPPORTED_TYPE,
                    format!(
                        "`{g}.{member}` is unsupported (no `msg.*`/`tx.*`/`block.*` beyond the rewritten `msg.sender`)"
                    ),
                    span.clone(),
                ));
            }
            // SOL-ENUM EX-8: `EnumName.Member` access. Fires ONLY when the base is a bare
            // `Var` naming a known enum that is NOT shadowed by an in-scope binding
            // (`name ∉ tys` — UP-2: a local/param/state field named like the enum wins and
            // falls through to value inference). The member must exist (EX-3 → FE466). The
            // result is the nominal enum type; `lower_enum_members` rewrites the node to the
            // member's index literal post-check.
            if let Expr::Var(name, _) = base.as_ref()
                && !tys.contains_key(name)
                && let Some(edef) = enums.iter().find(|e| e.name == *name)
            {
                return if edef.members.iter().any(|m| m == member) {
                    Ok(SolTy::Enum(name.clone()))
                } else {
                    Err(FrontendDiag::new(
                        codes::FE466_BAD_ENUM_MEMBER_SOL,
                        format!("`{name}.{member}` — `{member}` is not a member of enum `{name}`"),
                        span.clone(),
                    ))
                };
            }
            let bt = infer(base, tys, structs, enums)?;
            // SOL-AIRDROP (Rung C) UP-LENGTH: `<array>.length` types as `u256` (emitted
            // `.len()`), so a source `require(recipients.length == amounts.length)` before
            // an airdrop loop survives as a faithful runtime check. Any other member on an
            // array → FE410.
            if let SolTy::Array(_) = bt {
                if member == "length" {
                    return Ok(SolTy::U256);
                }
                return Err(FrontendDiag::new(
                    codes::FE410_UNSUPPORTED_TYPE,
                    format!("member access `.{member}` on an array (only `.length` is supported)"),
                    span.clone(),
                ));
            }
            let SolTy::Named(sname) = bt else {
                return Err(FrontendDiag::new(
                    codes::FE410_UNSUPPORTED_TYPE,
                    format!(
                        "member access `.{member}` on a non-struct value (no `msg.*`/`block.*`/`tx.*`)"
                    ),
                    span.clone(),
                ));
            };
            struct_field_ty(structs, enums, &sname, member).ok_or_else(|| {
                FrontendDiag::new(
                    codes::FE460_STRUCT_FIELD_MISMATCH_SOL,
                    format!("struct `{sname}` has no field `{member}`"),
                    span.clone(),
                )
            })
        }
        // SOL-STRUCT: a `Name(args)` call where `Name` is a struct → positional
        // construction (EX-1: supply every field, in order). Any other call is
        // unsupported (no internal/external calls).
        Expr::Call(callee, args, span) => {
            if let Expr::Var(name, _) = callee.as_ref()
                && let Some(sdef) = structs.iter().find(|s| s.name == *name)
            {
                if args.len() != sdef.fields.len() {
                    return Err(FrontendDiag::new(
                        codes::FE460_STRUCT_FIELD_MISMATCH_SOL,
                        format!(
                            "struct `{name}` construction supplies {} value(s) but `{name}` declares {} field(s) (positional construction must supply every field exactly once)",
                            args.len(),
                            sdef.fields.len()
                        ),
                        span.clone(),
                    ));
                }
                for (arg, fld) in args.iter().zip(sdef.fields.iter()) {
                    let aty = infer(arg, tys, structs, enums)?;
                    let fty = resolve_ty(&fld.ty, TyPos::Local, structs, enums)?;
                    require_assignable(&aty, &fty, arg.span())?;
                }
                return Ok(SolTy::Named(name.clone()));
            }
            Err(FrontendDiag::new(
                codes::FE401_UNSUPPORTED_SOL,
                "function calls are unsupported (no internal/external calls)",
                span.clone(),
            ))
        }
        Expr::Index(base, key, span) => {
            let bt = infer(base, tys, structs, enums)?;
            let (kt, vt) = match bt {
                SolTy::Map { key, value } => (*key, *value),
                _ => {
                    return Err(FrontendDiag::new(
                        codes::FE442_BAD_INDEX_SOL,
                        "index `[..]` applied to a value that is not a mapping",
                        span.clone(),
                    ));
                }
            };
            let kty = infer(key, tys, structs, enums)?;
            require_assignable(&kty, &kt, key.span())?;
            Ok(vt)
        }
        Expr::Unary(UnOp::Not, inner, _) => {
            // `!` yields bool; an operand-type mismatch (`!u256`) is caught by the
            // compiler's re-verification (not an existential mistranslation risk).
            infer(inner, tys, structs, enums)?;
            Ok(SolTy::Bool)
        }
        Expr::Unary(UnOp::Neg, _, span) => Err(FrontendDiag::new(
            codes::FE401_UNSUPPORTED_SOL,
            "unary minus is unsupported (u256 is unsigned)",
            span.clone(),
        )),
        Expr::Bin(op, l, r, span) => {
            let lt = infer(l, tys, structs, enums)?;
            let rt = infer(r, tys, structs, enums)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    // Returns the RESULT width (U256, or UintN(n) once M2 enables it) so the
                    // width-trap pass can read each node's `2^N` bound off its operands.
                    arith_result_ty(&lt, &rt, span.clone())
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    require_ordered_compatible(&lt, &rt, span.clone())?;
                    Ok(SolTy::Bool)
                }
                BinOp::Eq | BinOp::Ne => {
                    require_eq_compatible(&lt, &rt, span.clone())?;
                    Ok(SolTy::Bool)
                }
                BinOp::And | BinOp::Or => Err(FrontendDiag::new(
                    codes::FE401_UNSUPPORTED_SOL,
                    "compound boolean `&&`/`||` is unsupported in SOL1a (SIGIL has no short-circuit operators); use separate `require`s",
                    span.clone(),
                )),
            }
        }
    }
}

/// The RESULT type of an arithmetic op (`+ - * / %`) on `l`,`r`, enforcing same-width
/// (EX-2) and per-width literal range (EX-4). Returns `UintN(n)` for same-width narrow
/// arithmetic so the M2 width-trap pass can read each node's `2^n` bound (it wraps `+`/`*`
/// in the checked helper; `-`/`/`/`%` are width-safe). MIXED widths (`uintN op uintM` n≠m,
/// or `uintN op uint256`) → FE462; an out-of-range literal → FE430.
fn arith_result_ty(l: &SolTy, r: &SolTy, span: Range<usize>) -> Result<SolTy, FrontendDiag> {
    use SolTy::*;
    match (l, r) {
        (U256 | Num { .. }, U256 | Num { .. }) => Ok(U256),
        (UintN(n), UintN(m)) => {
            if n == m {
                Ok(UintN(*n))
            } else {
                Err(mixed_width(span))
            }
        }
        (UintN(n), Num { lit }) | (Num { lit }, UintN(n)) => {
            if num_fits_width(lit, *n) {
                Ok(UintN(*n))
            } else {
                Err(FrontendDiag::new(
                    codes::FE430_BAD_NUMBER_SOL,
                    format!("numeric literal exceeds the `uint{n}` range [0, 2^{n})"),
                    span,
                ))
            }
        }
        (UintN(_), U256) | (U256, UintN(_)) => Err(mixed_width(span)),
        (Address, _) | (_, Address) => Err(addr_mix(
            span,
            "arithmetic on an `address` is not allowed (address admits only `==`/`!=`)",
        )),
        (Bool, _) | (_, Bool) => Err(type_mismatch(
            span,
            "arithmetic operand must be numeric (got `bool`)",
        )),
        (Map { .. }, _) | (_, Map { .. }) => Err(map_as_value(span)),
        (Named(_), _) | (_, Named(_)) => Err(type_mismatch(
            span,
            "arithmetic operand must be numeric (got a struct)",
        )),
        // SOL-ENUM EX-2: an enum admits only the six comparisons, never arithmetic.
        (Enum(_), _) | (_, Enum(_)) => Err(type_mismatch(
            span,
            "arithmetic on an enum is not allowed (an enum admits only `== != < <= > >=`)",
        )),
        (Array(_), _) | (_, Array(_)) => Err(type_mismatch(
            span,
            "arithmetic operand must be numeric (got an array — arrays appear only as airdrop parameters)",
        )),
    }
}

/// FE462 — mixed-width arithmetic. Both operands must be the same width (`uintN op uintN`);
/// Solidity widens implicitly, but a single node needs one unambiguous `2^N` bound, so we
/// require an explicit widening (over-rejection, fail-closed — an EX-2 anti-goal).
fn mixed_width(span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE462_UINTN_WIDTH_SOL,
        "mixed-width arithmetic requires both operands the same width (`uintN op uintN`)",
        span,
    )
}

/// Relational `< <= > >=` compatibility. Pure-numeric operands compare freely (the `u256`
/// carrier compare is EXACT — matching Solidity's implicit widening), but a literal vs a
/// `uintN` must fit that width (EX-4). `address`/`bool` have no ordering; mapping/struct
/// are type errors.
fn require_ordered_compatible(
    l: &SolTy,
    r: &SolTy,
    span: Range<usize>,
) -> Result<(), FrontendDiag> {
    use SolTy::*;
    match (l, r) {
        (U256 | Num { .. } | UintN(_), U256 | Num { .. } | UintN(_)) => {
            lit_fits_operands(l, r, span)
        }
        (Address, _) | (_, Address) => Err(FrontendDiag::new(
            codes::FE443_ADDRESS_OP_SOL,
            "an `address` has no ordering (`< <= > >=` are not allowed; use `==`/`!=`)",
            span,
        )),
        (Bool, _) | (_, Bool) => Err(type_mismatch(
            span,
            "relational comparison operand must be numeric (got `bool`)",
        )),
        (Map { .. }, _) | (_, Map { .. }) => Err(map_as_value(span)),
        (Named(_), _) | (_, Named(_)) => Err(type_mismatch(
            span,
            "relational comparison operand must be numeric (got a struct)",
        )),
        // SOL-ENUM EX-2: Solidity enums are ORDERED — a SAME-enum pair compares with all six
        // operators (the ordinal). A cross-enum or enum-vs-other ordering → FE445.
        (Enum(a), Enum(b)) if a == b => Ok(()),
        (Enum(_), _) | (_, Enum(_)) => Err(type_mismatch(
            span,
            "relational comparison requires both operands the SAME enum",
        )),
        (Array(_), _) | (_, Array(_)) => Err(type_mismatch(
            span,
            "an array has no ordering (arrays appear only as airdrop parameters)",
        )),
    }
}

/// If exactly one operand is a `uintN` and the other a numeric literal, the literal MUST
/// fit that width (Solidity errors on an out-of-range literal comparison/op). Otherwise Ok
/// — numeric operands compare via the exact `u256` carrier.
fn lit_fits_operands(l: &SolTy, r: &SolTy, span: Range<usize>) -> Result<(), FrontendDiag> {
    use SolTy::*;
    let (n, lit) = match (l, r) {
        (UintN(n), Num { lit }) | (Num { lit }, UintN(n)) => (*n, lit),
        _ => return Ok(()),
    };
    if num_fits_width(lit, n) {
        Ok(())
    } else {
        Err(FrontendDiag::new(
            codes::FE430_BAD_NUMBER_SOL,
            format!("numeric literal exceeds the `uint{n}` range [0, 2^{n})"),
            span,
        ))
    }
}

/// `==`/`!=` operand compatibility (NC-L3b / LM4): `bool==bool`, `uint256`/numeric
/// among themselves, `address`/numeric among themselves — but NEVER `address` vs
/// `uint256` (a silent type confusion). A numeric literal compared to an `address`
/// must fit in 160 bits (NC-L3c / LM5).
fn require_eq_compatible(l: &SolTy, r: &SolTy, span: Range<usize>) -> Result<(), FrontendDiag> {
    use SolTy::*;
    match (l, r) {
        (Bool, Bool) => Ok(()),
        (U256, U256) | (U256, Num { .. }) | (Num { .. }, U256) | (Num { .. }, Num { .. }) => Ok(()),
        (Address, Address) => Ok(()),
        (Address, Num { lit }) | (Num { lit }, Address) => {
            if num_fits_width(lit, 160) {
                Ok(())
            } else {
                Err(FrontendDiag::new(
                    codes::FE430_BAD_NUMBER_SOL,
                    "numeric literal compared to an `address` exceeds the 160-bit address range",
                    span,
                ))
            }
        }
        // SOL-uintN: a `uintN` compares (`==`/`!=`) freely with any numeric (exact `u256`
        // carrier compare; Solidity implicitly widens); a literal must fit the width (EX-4).
        (UintN(_), UintN(_)) | (UintN(_), U256) | (U256, UintN(_)) => Ok(()),
        (UintN(n), Num { lit }) | (Num { lit }, UintN(n)) => {
            if num_fits_width(lit, *n) {
                Ok(())
            } else {
                Err(FrontendDiag::new(
                    codes::FE430_BAD_NUMBER_SOL,
                    format!("numeric literal compared to a `uint{n}` exceeds its [0, 2^{n}) range"),
                    span,
                ))
            }
        }
        (Address, UintN(_)) | (UintN(_), Address) => Err(addr_mix(
            span,
            "cannot compare an `address` with a `uintN` (distinct types; no implicit conversion)",
        )),
        (Address, U256) | (U256, Address) => Err(FrontendDiag::new(
            codes::FE443_ADDRESS_OP_SOL,
            "cannot compare an `address` with a `uint256` (distinct types; no implicit conversion)",
            span,
        )),
        (Map { .. }, _) | (_, Map { .. }) => Err(FrontendDiag::new(
            codes::FE442_BAD_INDEX_SOL,
            "a mapping must be indexed (`m[k]`) before use in an expression",
            span,
        )),
        // SOL-ENUM EX-2: a SAME-enum pair compares with `==`/`!=`; a cross-enum or
        // enum-vs-other pair falls to the `_` arm below → FE445 (no ordinal leak).
        (Enum(a), Enum(b)) if a == b => Ok(()),
        _ => Err(type_mismatch(
            span,
            "incompatible operand types for `==`/`!=`",
        )),
    }
}

/// A compound-assignment target on a MAPPING VALUE (`m[k] op= e`) must be `uint256` — the
/// bounded map is `u256`-valued. (Scalar `uintN` compound targets are validated by
/// `arith_result_ty` in the Assign/FieldAssign branches; a `uintN` map value is FE441 at
/// resolve, so the `UintN` arm here is defensive / unreachable for a valid program.)
fn require_arith_target(t: &SolTy, span: Range<usize>) -> Result<(), FrontendDiag> {
    match t {
        SolTy::U256 => Ok(()),
        SolTy::UintN(_) => Err(FrontendDiag::new(
            codes::FE462_UINTN_WIDTH_SOL,
            "arithmetic on a narrow `uintN` mapping value is unsupported (the bounded map is u256-valued)",
            span,
        )),
        SolTy::Address => Err(FrontendDiag::new(
            codes::FE443_ADDRESS_OP_SOL,
            "compound arithmetic assignment to an `address` is not allowed",
            span,
        )),
        _ => Err(type_mismatch(
            span,
            "compound arithmetic assignment requires a `uint256` target",
        )),
    }
}

/// Whether a value of type `from` may flow into a slot/position of type `to`
/// (let/assign/return/index-key/index-value). Enforces address distinctness
/// (NC-L3b) and the 160-bit address-literal range (NC-L3c).
fn require_assignable(from: &SolTy, to: &SolTy, span: Range<usize>) -> Result<(), FrontendDiag> {
    use SolTy::*;
    match to {
        U256 => match from {
            U256 | Num { .. } => Ok(()),
            // SOL-uintN: WIDENING a narrow `uintN` to `uint256` is safe and trap-free —
            // the `u256` carrier already holds the (in-range) value (EX-3 / R-W).
            UintN(_) => Ok(()),
            Address => Err(addr_mix(
                span,
                "an `address` cannot be used where `uint256` is expected",
            )),
            Bool => Err(type_mismatch(
                span,
                "a `bool` cannot be used where `uint256` is expected",
            )),
            Map { .. } => Err(map_as_value(span)),
            Named(_) => Err(type_mismatch(
                span,
                "a struct cannot be used where `uint256` is expected",
            )),
            Enum(_) => Err(type_mismatch(
                span,
                "an enum cannot be used where `uint256` is expected (no implicit enum↔uint conversion)",
            )),
            Array(_) => Err(type_mismatch(
                span,
                "an array cannot be used where `uint256` is expected",
            )),
        },
        Address => match from {
            Address => Ok(()),
            Num { lit } => {
                if num_fits_width(lit, 160) {
                    Ok(())
                } else {
                    Err(FrontendDiag::new(
                        codes::FE430_BAD_NUMBER_SOL,
                        "address literal exceeds the 160-bit address range [0, 2^160)",
                        span,
                    ))
                }
            }
            U256 => Err(addr_mix(
                span,
                "a `uint256` cannot be used where `address` is expected",
            )),
            UintN(_) => Err(addr_mix(
                span,
                "a `uintN` cannot be used where `address` is expected (distinct types)",
            )),
            Bool => Err(type_mismatch(
                span,
                "a `bool` cannot be used where `address` is expected",
            )),
            Map { .. } => Err(map_as_value(span)),
            Named(_) => Err(type_mismatch(
                span,
                "a struct cannot be used where `address` is expected",
            )),
            Enum(_) => Err(type_mismatch(
                span,
                "an enum cannot be used where `address` is expected",
            )),
            Array(_) => Err(type_mismatch(
                span,
                "an array cannot be used where `address` is expected",
            )),
        },
        Bool => match from {
            Bool => Ok(()),
            Map { .. } => Err(map_as_value(span)),
            _ => Err(type_mismatch(span, "expected a `bool` value")),
        },
        Map { .. } => Err(FrontendDiag::new(
            codes::FE442_BAD_INDEX_SOL,
            "cannot assign to a mapping as a whole (assign an element with `m[k] = v`)",
            span,
        )),
        // EX-2: structs are NOMINAL — only the SAME struct type is assignable; no
        // structural coercion, and no scalar↔struct mixing.
        Named(tn) => match from {
            Named(fnm) if fnm == tn => Ok(()),
            _ => Err(type_mismatch(
                span,
                "struct type mismatch (structs are nominal — only the same struct type is assignable)",
            )),
        },
        // SOL-uintN: WIDENING into `uintN` from a narrower `uintM` (m≤n) or a fitting
        // literal is safe + trap-free (the carrier already holds the in-range value).
        // NARROWING (from `uint256`, or a wider `uintM` with m>n) → FE462: Solidity
        // compile-errors implicit narrowing, and a silent truncation would corrupt data
        // (EX-3). The carrier is invisible to the trusted compiler, so this is the SOLE
        // narrowing gate (EX-5).
        UintN(n) => match from {
            UintN(m) if *m <= *n => Ok(()),
            UintN(_) => Err(FrontendDiag::new(
                codes::FE462_UINTN_WIDTH_SOL,
                format!(
                    "narrowing a wider `uintM` into `uint{n}` requires an explicit cast (implicit narrowing is rejected)"
                ),
                span,
            )),
            Num { lit } if num_fits_width(lit, *n) => Ok(()),
            Num { .. } => Err(FrontendDiag::new(
                codes::FE430_BAD_NUMBER_SOL,
                format!("numeric literal exceeds the `uint{n}` range [0, 2^{n})"),
                span,
            )),
            U256 => Err(FrontendDiag::new(
                codes::FE462_UINTN_WIDTH_SOL,
                format!(
                    "narrowing a `uint256` into `uint{n}` requires an explicit cast (implicit narrowing is rejected)"
                ),
                span,
            )),
            Address => Err(addr_mix(
                span,
                "an `address` cannot be used where a `uintN` is expected",
            )),
            Bool => Err(type_mismatch(
                span,
                "a `bool` cannot be used where a `uintN` is expected",
            )),
            Map { .. } => Err(map_as_value(span)),
            Named(_) => Err(type_mismatch(
                span,
                "a struct cannot be used where a `uintN` is expected",
            )),
            Enum(_) => Err(type_mismatch(
                span,
                "an enum cannot be used where a `uintN` is expected",
            )),
            Array(_) => Err(type_mismatch(
                span,
                "an array cannot be used where a `uintN` is expected",
            )),
        },
        // SOL-ENUM EX-2/EX-9: enums are NOMINAL — only the SAME enum type assigns; NEVER a
        // raw `uint`/`Num`/another enum (no implicit enum↔uint ordinal leak; casts deferred).
        Enum(tn) => match from {
            Enum(fnm) if fnm == tn => Ok(()),
            _ => Err(type_mismatch(
                span,
                "enum type mismatch (enums are nominal — only the same enum type is assignable; no implicit enum↔uint conversion)",
            )),
        },
        Array(_) => Err(type_mismatch(
            span,
            "cannot assign to an array (arrays appear only as read-only airdrop parameters)",
        )),
        Num { .. } => unreachable!("Num is never a declared/target type"),
    }
}

/// FE443 — a genuine `address`↔`uint256` misuse (an address used as/with a uint256).
fn addr_mix(span: Range<usize>, msg: &str) -> FrontendDiag {
    FrontendDiag::new(codes::FE443_ADDRESS_OP_SOL, msg.to_string(), span)
}

/// FE445 — a type-kind mismatch that does NOT involve an address↔uint256 confusion
/// (e.g. `bool` vs numeric). Kept separate so FE443 stays precise to address misuse.
fn type_mismatch(span: Range<usize>, msg: &str) -> FrontendDiag {
    FrontendDiag::new(codes::FE445_TYPE_MISMATCH_SOL, msg.to_string(), span)
}

fn map_as_value(span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(
        codes::FE442_BAD_INDEX_SOL,
        "a mapping must be indexed (`m[k]`) before use as a value",
        span,
    )
}

/// Whether a numeric literal (decimal or `0x`-hex) is `< 2^bits`. The lexer has already
/// bounded it to `< 2^256`. Used for the `address` 160-bit range AND every `uintN` width
/// — the frontend is the SOLE gate for both (the carrier is a bare `u256`).
fn num_fits_width(text: &str, bits: u16) -> bool {
    if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        // Each hex digit is 4 bits; a leading-zero-trimmed length of ≤ bits/4 fits.
        return hex.trim_start_matches('0').len() * 4 <= bits as usize;
    }
    // Decimal: fits iff value `< 2^bits`. Compare the trimmed literal to `2^bits` as a
    // string — equal-length numeric strings compare lexicographically; shorter is smaller.
    let pow = pow2_decimal(bits);
    let t = text.trim_start_matches('0');
    let t = if t.is_empty() { "0" } else { t };
    t.len() < pow.len() || (t.len() == pow.len() && t < pow.as_str())
}

/// `2^bits` as a decimal string (LSB-first repeated doubling). `bits` ≤ 256 ⇒ ≤ 78 digits.
fn pow2_decimal(bits: u16) -> String {
    let mut digits: Vec<u8> = vec![1];
    for _ in 0..bits {
        let mut carry = 0u8;
        for d in digits.iter_mut() {
            let v = *d * 2 + carry;
            *d = v % 10;
            carry = v / 10;
        }
        if carry > 0 {
            digits.push(carry);
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

/// Whether an expression contains a checked-u256 arithmetic op (`+ - * / %`),
/// which lowers to a trapping intrinsic. Comparisons/`!`/index reads do not trap
/// (the index `get_or` is total), but an index KEY may itself contain arithmetic.
/// (SOL-CALLS also reuses this as the "trap-capable value expr" test for FE489.)
pub(super) fn expr_has_checked_arith(e: &Expr) -> bool {
    match e {
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => false,
        // SOL-STRUCT: a `Call` is now a LEGAL surviving form — struct construction
        // `MyStruct(a, b)` — so its args may carry trap-capable arithmetic (e.g.
        // `Receipt(amt - fee, 0)`). The CEI gate MUST see it, or arithmetic hidden in a
        // construction after a storage write escapes FE412 (adversarial-review finding: a
        // trap-after-commit Solidity would revert but SIGIL would not → fund desync).
        // A `Member` base likewise (defensively) recursed; an arith base is rejected by
        // `infer` (non-`Named`) before this runs, so it only ever returns false.
        Expr::Member(base, _, _) => expr_has_checked_arith(base),
        Expr::Call(_, args, _) => args.iter().any(expr_has_checked_arith),
        Expr::Index(base, key, _) => expr_has_checked_arith(base) || expr_has_checked_arith(key),
        Expr::Unary(_, inner, _) => expr_has_checked_arith(inner),
        Expr::Bin(op, l, r, _) => {
            matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
            ) || expr_has_checked_arith(l)
                || expr_has_checked_arith(r)
        }
    }
}
