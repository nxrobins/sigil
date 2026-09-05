//! Recursive-descent parser for the SOL0 Solidity subset, with a depth counter
//! checked BEFORE each expression descent (threat: stack overflow on adversarial
//! nesting — the Rust parser has no such cap, so this frontend owns totality).
//! Fail-closed + total: any construct outside the grammar returns one
//! `FrontendDiag`. Type names are kept raw (`TypeRef`); the allow-list reject and
//! all semantic checks live in `check.rs`.

use super::lexer::{Tok, TokKind};
use crate::FrontendDiag;
use crate::codes;
use crate::limits::{MAX_FUNCTIONS, MAX_MODIFIERS_PER_FN};
use std::ops::Range;

/// Maximum AST nesting depth (statements + expressions, combined). Deliberately
/// LOW and Solidity-local (not the shared `limits::MAX_DEPTH`): the bound must be
/// safe not just for THIS parser but for every recursive consumer of the AST —
/// `check`, `emit`, the AST's own recursive `Drop`, AND the trusted SIGIL
/// compiler re-parsing the emitted text (in the FE500 self-check and in
/// `check --from`). The trusted parser recurses ~16× per nesting level and
/// overflows a 1 MiB main-thread stack around depth ~18 (measured, debug build —
/// the worst case; release / 8 MiB stacks are far higher). 12 stays well under
/// that on every platform while far exceeding any realistic SOL0 expression.
/// `pub(super)` so `desugar::inline_modifiers` can re-bound the MERGED body after
/// splicing (E3) against the same limit the parser enforced per-body.
pub(super) const MAX_NEST_DEPTH: u32 = 12;

// ── AST ──────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub struct Program {
    /// The `pragma … ;` body (raw) + its span, if present. Version-checked in check.rs.
    pub pragma: Option<(String, Range<usize>)>,
    pub contract: Contract,
}

/// SOL-INH: the raw result of parsing a file — the pragma + ALL top-level contract-like
/// declarations (concrete / abstract / interface / library), in source order. `flatten`
/// (M1) C3-linearizes + merges these into the single `Program.contract` the rest of the
/// pipeline consumes; until then a one-concrete-no-bases file reduces to `Program` directly
/// (the byte-identical existing path).
#[derive(Debug)]
pub struct ParsedFile {
    pub pragma: Option<(String, Range<usize>)>,
    pub contracts: Vec<Contract>,
    /// SOL-XFILE: the raw path text of every plain/named `import "p";` /
    /// `import {A, B} from "p";` line, in source order (+ its span). Captured for the
    /// PROJECT resolver (`project.rs`), which resolves each against the in-memory
    /// file-set ONLY (never the filesystem). The single-file path ignores them
    /// (self-contained files treat import lines as redundant, as before).
    pub imports: Vec<(String, Range<usize>)>,
}

/// SOL-INH: which top-level declaration kind a `Contract` came from. Only a `Concrete`
/// contract is a deployable "main" candidate (MI-2); `Interface`/`Abstract`/`Library` are
/// collected (they can be inheritance bases) but are never the translated sink.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractKind {
    Concrete,
    Abstract,
    Interface,
    Library,
}

/// SOL-INH: one entry in a `contract X is A, B(args)` inheritance list — a base name plus any
/// constructor args supplied on the `is` clause. `args` is empty for a plain base.
#[derive(Debug)]
pub struct BaseRef {
    pub name: String,
    pub args: Vec<Expr>,
    pub span: Range<usize>,
}

#[derive(Debug)]
pub struct Contract {
    pub name: String,
    /// SOL-INH: `Concrete` unless this was an `abstract`/`interface`/`library` declaration.
    pub kind: ContractKind,
    /// SOL-INH: the `is Base1, Base2(args)` inheritance list (empty for a flat contract). The
    /// `flatten` pass C3-linearizes + merges these; a single contract with no bases takes the
    /// byte-identical existing path (EX-9).
    pub bases: Vec<BaseRef>,
    /// SOL-STRUCT `struct` declarations → SIGIL `record`s (emitted before the contract
    /// record). Nominal/completeness/self-reference checks live in `check.rs`.
    pub structs: Vec<Struct>,
    pub state: Vec<StateVar>,
    pub functions: Vec<Function>,
    /// SOL1c `modifier` declarations. Consumed (inlined into the functions) by
    /// `desugar::inline_modifiers`; never reaches check/emit as a top-level item.
    pub modifiers: Vec<Modifier>,
    /// SOL-CTOR: the at-most-one `constructor(params){body}` with deploy-time init logic.
    /// Lowered to a `new(params) -> C` that builds the record, runs the body, and returns
    /// it (emit). `None` ⇒ the existing zero-init `new()` (byte-identical, EX-9).
    pub constructor: Option<Constructor>,
    /// SOL-ENUM `enum Name { A, B, C }` declarations. Lowered to a `u256` TAG carrier:
    /// `Name.Member` → the member's 0-based index literal, the decl ERASED (no SIGIL enum).
    /// Nominal/member-exists/shape checks live in `check.rs`.
    pub enums: Vec<Enum>,
    pub span: Range<usize>,
}

/// A SOL-ENUM `enum Name { A, B, C }`. Members are bare idents, source order = the 0-based
/// tag value. Lowers to a `u256` carrier; the frontend is the SOLE gate for enum-ness.
/// `Clone`: SOL-INH `flatten` copies inherited members from base contracts into the merge.
#[derive(Debug, Clone)]
pub struct Enum {
    pub name: String,
    pub members: Vec<String>,
    pub span: Range<usize>,
}

/// SOL-XFILE PR4/L3: a base-constructor invocation from a constructor's attribute window
/// (`constructor() ERC20("Name", "SYM") {}`). The ARGUMENTS are NOT retained — the metadata-ctor
/// reduction (`flatten::merge`) drops the whole call as a no-op — only whether every argument
/// TOKEN was a literal (string/number/bool) is recorded: an all-literal call to a base whose ctor
/// is itself metadata-only reduces to nothing; any non-literal argument → the call is non-droppable
/// → FE468.
#[derive(Debug, Clone)]
pub struct BaseCtorCall {
    pub name: String,
    pub all_literal: bool,
    pub span: Range<usize>,
}

/// A SOL-CTOR `constructor(params) <base-calls> { body }`. No name, no return type, no modifiers
/// (those are FE464). The body is checked/emitted like a method body, except it BUILDS the record
/// (`let mut __fe_c`), its scalar field writes are CEI-exempt locals (EX-2), and it returns
/// the record. `msg.sender` in the body → the `__fe_sender` deployer param (desugar).
#[derive(Debug, Clone)]
pub struct Constructor {
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
    /// SOL-XFILE PR4/L3: base-constructor invocations (`… ERC20("N","S")`). Validated + cleared by
    /// `flatten::merge`'s metadata-ctor reduction; a non-droppable call → FE468. Empty for a flat
    /// contract or a base-less constructor (the byte-identical existing path).
    pub base_calls: Vec<BaseCtorCall>,
    pub span: Range<usize>,
}

/// A SOL-STRUCT `struct Name { T field; … }` declaration → a SIGIL `record Name { … }`.
/// Fields are `T name;` lines (a trailing comma is tolerated). A struct-typed field
/// parses as `TypeRef::Scalar { name }`; the allow-list, nominal-identity,
/// construction-completeness, and self-reference checks all live in `check.rs`.
#[derive(Debug, Clone)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<StructField>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub ty: TypeRef,
    pub span: Range<usize>,
}

/// A `modifier name(params) { … _ … }` declaration. `params` is empty for the SOL1c
/// parameterless form and non-empty for a SOL-ACCESS parameterized modifier (the OZ
/// `onlyRole(bytes32 role)` shape); `body` contains EXACTLY ONE `Stmt::Placeholder`
/// (parse-enforced, FE447), counted across nested `if` branches. `inline_modifiers`
/// binds each param to its application argument via an eval-once `let` prelude.
#[derive(Debug, Clone)]
pub struct Modifier {
    pub name: String,
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
    pub span: Range<usize>,
}

/// A modifier APPLICATION on a function (`grantRole(…) onlyRole(getRoleAdmin(role))`):
/// the modifier name plus the argument expressions supplied at the call site. `args`
/// is empty for a bare/parameterless application; a non-empty `args` is bound
/// eval-once to the modifier's params during inlining. The arity (`args.len()` vs the
/// modifier's `params.len()`) is checked at inline time (FE448 on mismatch).
#[derive(Debug, Clone)]
pub struct ModifierApp {
    pub name: String,
    pub args: Vec<Expr>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub enum TypeRef {
    /// A scalar type name as written (`uint256`, `uint`, `bool`, `address`, `uint8`,
    /// …). The allow-list reject lives in `check.rs`.
    Scalar { name: String, span: Range<usize> },
    /// `mapping(K => V)` (SOL1). Single-level is the SUPPORTED shape; a nested
    /// `mapping(a => mapping(b => v))` parses (key/value are themselves `TypeRef`s)
    /// and is rejected in `check.rs` (FE440). The recursive descent is depth-guarded
    /// so an adversarially deep mapping type yields FE402, never a stack overflow.
    Mapping {
        key: Box<TypeRef>,
        value: Box<TypeRef>,
        span: Range<usize>,
    },
    /// SOL-AIRDROP (Rung C): a dynamic array `T[]` of a SCALAR element — the airdrop's
    /// `recipients`/`amounts` parallel arrays. Accepted ONLY in PARAMETER position (a
    /// state-var/local/return array, a sized `[N]`, or a 2-D `[][]` → FE491), emitted as
    /// a bounded `BoundedVec_u256_64`. `check.rs` types `.length` on it as `u256` (→
    /// `.len()`); `arr[i]` is consumed only inside a recognized airdrop loop (elsewhere
    /// FE442). A single trailing `[]` on a scalar element only.
    Array {
        elem: Box<TypeRef>,
        span: Range<usize>,
    },
}

impl TypeRef {
    pub fn span(&self) -> Range<usize> {
        match self {
            TypeRef::Scalar { span, .. }
            | TypeRef::Mapping { span, .. }
            | TypeRef::Array { span, .. } => span.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StateVar {
    pub name: String,
    pub ty: TypeRef,
    pub init: Option<Expr>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: TypeRef,
    pub span: Range<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Visibility {
    Public,
    Private,
    Internal,
    External,
    Default,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StateMutability {
    NonPayable,
    View,
    Pure,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<TypeRef>,
    pub visibility: Visibility,
    pub mutability: StateMutability,
    /// Applied modifiers, in source order (left = outermost) — each a name plus its
    /// application arguments (empty for a parameterless application). `desugar::
    /// inline_modifiers` inlines them and CLEARS this list; a non-empty list reaching
    /// emit is an internal bug (E1, FE500).
    pub modifiers: Vec<ModifierApp>,
    pub body: Vec<Stmt>,
    /// SOL-XFILE PR2/L2: a BODILESS declaration (`function f(…) … ;`, no `{ }`) — an abstract
    /// contract's `virtual` method signature. Distinct from an empty-BODIED `function f(){}`
    /// (`body == []` too). `flatten::merge` is derived-wins, so a bodied override drops the
    /// bodiless base; a bodiless that SURVIVES the merge (nothing implemented it) → FE475.
    /// Only a Concrete/Abstract contract's member parses; interfaces are body-skipped whole.
    pub bodiless: bool,
    pub span: Range<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AssignOp {
    Eq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    /// `require(cond)` / `require(cond, "reason")` — reason is dropped (NC AG-S4).
    Require { cond: Expr, span: Range<usize> },
    /// `assert(cond)` — same control-flow abort as require (NC AG-S4).
    Assert { cond: Expr, span: Range<usize> },
    /// `revert()` / `revert CustomError(...)` — an UNCONDITIONAL abort.
    Revert { span: Range<usize> },
    /// `name = e` / `name op= e` (target is a bare identifier: state field or local).
    Assign {
        target: String,
        op: AssignOp,
        value: Expr,
        span: Range<usize>,
    },
    /// `map[key] = e` / `map[key] op= e` (SOL1) — a single-level mapping index write.
    /// `map` is a bare identifier (a storage mapping field); the lvalue classifier
    /// admits `Var[key]` (here) and `Var[k1][k2]` (`IndexAssign2`); deeper → FE440.
    IndexAssign {
        map: String,
        key: Expr,
        op: AssignOp,
        value: Expr,
        span: Range<usize>,
    },
    /// `map[k1][k2] = e` / `map[k1][k2] op= e` (SOL-ERC20) — a TWO-key nested mapping
    /// index write (the ERC20 `allowance[owner][spender] = amt` target). `map` is a
    /// bare identifier; a three-level `m[a][b][c]` target is rejected (FE440).
    IndexAssign2 {
        map: String,
        k1: Expr,
        k2: Expr,
        op: AssignOp,
        value: Expr,
        span: Range<usize>,
    },
    /// A recognized atomic transfer (SOL1b): the canonical `map[from] -= amount;
    /// map[to] += amount;` debit/credit idiom, folded by the desugar pass into a single
    /// call to the TRUSTED `map.transfer(from, to, amount)` stdlib method (which does
    /// all balance/overflow/capacity checks before any write). NOT produced by the
    /// parser — only by `desugar::recognize_transfers`.
    MapTransfer {
        map: String,
        from: Expr,
        to: Expr,
        amount: Expr,
        span: Range<usize>,
    },
    /// A recognized atomic ERC20 `transferFrom`, in one of TWO source shapes (both fold to a
    /// trusted two-map primitive that runs all checks before any write — atomic, since SIGIL cannot
    /// roll back — and both are ONE `committed_write` to `check.rs`):
    ///   - `oz5_infinite == false` (SOL-ERC20, the OZ 4.x shape): the canonical
    ///     `allowance[from][spender] -= amount;` (a two-key debit) immediately followed by the
    ///     recognized balance `MapTransfer { from, to, amount }`, from `recognize_transfer_from` →
    ///     `alw.transfer_from(bal, from, spender, to, amount)`.
    ///   - `oz5_infinite == true` (SOL-XFILE PR6/AC-2, the OZ 5.x shape): the inlined
    ///     `_spendAllowance` (a `type(uint256).max` INFINITE-allowance dispatch guarding an
    ///     `_allowances[from][spender] = currentAllowance - value` decrement) + the `_transfer`
    ///     zero-guards + the folded balance `Erc20Update`, from `recognize_spend_transfer` →
    ///     `alw.erc20_transfer_from(bal, from, spender, to, amount)` (which ADDITIONALLY traps on a
    ///     zero from/to — never mint/burn — and skips the decrement for an infinite allowance). The
    ///     surviving from/to zero-guards stay as pure trap-checks before this single atomic op.
    ///
    /// NOT produced by the parser — only by the two recognizers. The operands + CEI treatment are
    /// identical; ONLY `emit` branches on `oz5_infinite` to pick the primitive.
    Erc20TransferFrom {
        bal_map: String,
        alw_map: String,
        from: Expr,
        spender: Expr,
        to: Expr,
        amount: Expr,
        oz5_infinite: bool,
        span: Range<usize>,
    },
    /// `obj.field = e` / `obj.field op= e` (SOL-STRUCT) — a struct field write. `obj` is
    /// a bare identifier (a struct-typed state field or local); the field is a SINGLE
    /// level (`a.b.c = e` → reject). A write to a state-field struct is a storage write
    /// (threads the CEI `committed_write` rule, like a scalar field write).
    FieldAssign {
        obj: String,
        field: String,
        op: AssignOp,
        value: Expr,
        span: Range<usize>,
    },
    /// `T name = e;` — a local variable declaration.
    LocalVar {
        name: String,
        ty: TypeRef,
        value: Expr,
        span: Range<usize>,
    },
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
        span: Range<usize>,
    },
    Return {
        value: Option<Expr>,
        span: Range<usize>,
    },
    /// An `unchecked { … }` block. The parser RETAINS its body; `desugar::unwrap_unchecked`
    /// (SOL-UNCHECKED) splices the body into the enclosing block and lowers it as CHECKED
    /// arithmetic (SIGIL u256 arith always traps on overflow — where Solidity wraps, SIGIL
    /// traps; a fail-closed over-approximation). A residual node reaching check → FE411.
    Unchecked { body: Vec<Stmt>, span: Range<usize> },
    /// The `_;` body-splice marker inside a `modifier` body (SOL1c). Produced ONLY when
    /// the parser's `in_modifier` flag is set; a `_;` in a function body falls through to
    /// a fail-closed FE401. Fully removed by `desugar::inline_modifiers` (replaced by the
    /// host function body); a residual Placeholder reaching check/emit is an internal
    /// inlining bug (FE500 — E1).
    Placeholder { span: Range<usize> },
    /// SOL-CALLS: a bare internal function-call STATEMENT (`_transfer(from, to, amt);`) — a
    /// `Var`-callee `Call` in statement position with no assignment. `desugar::inline_internal_calls`
    /// splices the callee's (alpha-renamed) body in place of this node; a residual `CallStmt` reaching
    /// check/emit is an internal inlining bug (FE500). `callee` is the bare name (a member call
    /// `a.b(…)` is an external call → FE401 at parse, never a `CallStmt`).
    CallStmt {
        callee: String,
        args: Vec<Expr>,
        span: Range<usize>,
    },
    /// SOL-MULTIMAP (M-A): a recognized RESERVED BATCH of ≥2 map writes to DISTINCT mappings, folded
    /// by `desugar::reserve_multi_map` into ONE atomic storage op (the `MapTransfer` precedent). Emit
    /// lowers it to reserve-all-then-write: `M.reserve1/2(k)` for every deferred plain write (read-only)
    /// → the ≤1 nested atomic `transfer`/`transfer_from` (self-atomic) → the trap-free `M.insert(k, v)`s.
    /// `check.rs` treats the whole batch as ONE `committed_write` (FE412 only if a PRIOR write committed),
    /// so the ≥2 distinct-map writes are atomic despite SIGIL's lack of rollback. NOT produced by the
    /// parser. `transfer` is the ≤1 folded `MapTransfer`/`Erc20TransferFrom`; `writes` are the deferred
    /// plain map writes, each an `IndexAssign`/`IndexAssign2` with `op: Eq` and a HOISTED `Var(__fe_wN)`
    /// value (the value arithmetic already lives in a preceding `LocalVar`, read pre-write).
    ReservedBatch {
        transfer: Option<Box<Stmt>>,
        writes: Vec<Stmt>,
        span: Range<usize>,
    },
    /// SOL-MULTIMAP (M-B): a recognized same-map fee-on-transfer SPLIT — the canonical `M[from] -= amount;
    /// M[to] += net; M[feeTo] += fee;` (a debit + TWO credits on ONE map, adjacent, pure operands), folded
    /// by `desugar::recognize_split` into ONE call to the TRUSTED `M.transfer_split(from, amount, to, net,
    /// feeTo, fee)` stdlib method. The primitive applies the three sequential deltas ALIASING-CORRECTLY
    /// across all 5 partitions of {from,to,feeTo} (the `a != b` the frontend cannot prove lives in verified
    /// stdlib, proven by the exec-proof), ALL checks before any write. `check.rs` treats it as ONE
    /// `committed_write` (the `MapTransfer` precedent). NOT produced by the parser. No conservation is
    /// assumed — `net`/`fee` are the source's deltas verbatim.
    MapSplitTransfer {
        map: String,
        from: Expr,
        amount: Expr,
        to: Expr,
        net: Expr,
        fee_to: Expr,
        fee: Expr,
        span: Range<usize>,
    },
    /// SOL-UPDATE: the recognized OZ 5.x unified `_update(from, to, value)` — the rigid 2-`if`
    /// zero-address-dispatch shape
    ///   `if (from == 0) { ts += value; } else { <debit M[from] by value> }`
    ///   `if (to   == 0) { ts -= value; } else { M[to] += value; }`
    /// (post-`normalize_literals`, so the conditions compare against the literal `0`), folded
    /// by `desugar::recognize_update` into ONE call to the TRUSTED `M.erc20_update(ts, from, to,
    /// value)` stdlib method. The primitive dispatches on the zero address DYNAMICALLY (mint /
    /// burn / transfer / self-transfer), aliasing-correct, ALL traps before any write, and NEVER
    /// writes `M[0]` (exec-proven, the `eu_*` oracle). `check.rs` treats it as ONE
    /// `committed_write` (the `Erc20TransferFrom` precedent); `emit` lowers it to the call plus a
    /// TRAP-FREE totalSupply store-back (`self.<ts_field> = <the returned new_ts>` — a bare-Var
    /// `=` store, CEI-safe after the committed map op). NOT produced by the parser.
    Erc20Update {
        map: String,
        ts_field: String,
        from: Expr,
        to: Expr,
        value: Expr,
        span: Range<usize>,
    },
    /// SOL-AIRDROP (Rung C): the rigid airdrop `for` loop — `for (uint <idx> = 0; <idx> <
    /// <len_array>.length; <inc>) { <body> }`, the PARSER'S ONLY loop output (produced by
    /// the `for`-header arm in `parse_stmt`; there is no general `Stmt::For`). It exists
    /// transiently from parse until `desugar::recognize_airdrop` folds it (body ==
    /// `[debit, credit]` with the counter-indexed recipient/amount + an invariant `from`)
    /// into a `BatchTransfer`, or REJECTS it (FE492). A residual `AirdropLoop` reaching
    /// `check` is an internal fold bug → FE500. The two SOL-CAP security walkers MUST
    /// recurse `body` (it exists at cap-scan time, before desugar — Correction B).
    AirdropLoop {
        idx: String,
        len_array: String,
        body: Vec<Stmt>,
        span: Range<usize>,
    },
    /// SOL-AIRDROP (Rung C): a recognized N-ary atomic airdrop, folded by
    /// `desugar::recognize_airdrop` from an `AirdropLoop` whose body is the canonical
    /// per-leg `M[from] -= amounts[i]; M[recipients[i]] += amounts[i];` debit/credit pair.
    /// `emit` lowers it to ONE call to the TRUSTED `self.<map>.batch_transfer(from,
    /// recipients, amounts)` stdlib method (debit `from` by each amount, credit each
    /// recipient; reserve-all-then-write via validate-on-a-clone-then-blit, aliasing-
    /// correct over N, exec-proven). `check.rs` treats it as ONE `committed_write` (the
    /// `MapSplitTransfer` precedent). `recipients`/`amounts` are the bare array PARAM
    /// names (emitted `BoundedVec_u256_64`); `from` is a pure loop-invariant operand. NOT
    /// produced by the parser.
    BatchTransfer {
        map: String,
        from: Expr,
        recipients: String,
        amounts: String,
        span: Range<usize>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Num(String, Range<usize>),
    Bool(bool, Range<usize>),
    Var(String, Range<usize>),
    /// Member access `base.member` (e.g. `msg.sender`) — parsed, then rejected by
    /// check.rs (SOL0 has no structs / globals).
    Member(Box<Expr>, String, Range<usize>),
    /// Call `callee(args)` — parsed, then rejected by check.rs (SOL0 has no
    /// internal/external calls).
    Call(Box<Expr>, Vec<Expr>, Range<usize>),
    /// Index `base[key]` (SOL1) — a mapping read. `check.rs` requires `base` to be a
    /// mapping-typed state field and `key` to match the mapping's declared key type.
    Index(Box<Expr>, Box<Expr>, Range<usize>),
    Unary(UnOp, Box<Expr>, Range<usize>),
    Bin(BinOp, Box<Expr>, Box<Expr>, Range<usize>),
}

impl Expr {
    pub fn span(&self) -> Range<usize> {
        match self {
            Expr::Num(_, s)
            | Expr::Bool(_, s)
            | Expr::Var(_, s)
            | Expr::Member(_, _, s)
            | Expr::Call(_, _, s)
            | Expr::Index(_, _, s)
            | Expr::Unary(_, _, s)
            | Expr::Bin(_, _, _, s) => s.clone(),
        }
    }
}

// ── parser ───────────────────────────────────────────────────────────────────

struct Parser {
    toks: Vec<Tok>,
    i: usize,
    depth: u32,
    /// True only while parsing a `modifier` body (SOL1c), so `parse_stmt` recognizes
    /// `_;` as `Stmt::Placeholder` anywhere in the modifier's statement tree (incl.
    /// nested `if` branches). Elsewhere `_;` falls through to a fail-closed FE401.
    in_modifier: bool,
    /// SOL-SAFEMATH: set once a `using SafeMath for uint256;` directive is seen (file- or
    /// contract-scope). While true, `parse_postfix` FOLDS a `recv.add/sub/mul/div/mod(operand)`
    /// SafeMath method call into the equivalent CHECKED `recv <binop> operand` (SIGIL arithmetic
    /// already traps on overflow/underflow/div-by-zero). File-level (once seen, active for the
    /// whole file — a `.add` without the directive is invalid Solidity anyway, and `check`
    /// re-validates operand types).
    safemath_active: bool,
}

/// `_src_len` is accepted for signature parity with the other frontends' parsers
/// (their span fallback uses it); SOL0 spans come from the tokens directly.
pub fn parse(toks: Vec<Tok>, _src_len: usize) -> Result<ParsedFile, FrontendDiag> {
    let mut p = Parser {
        toks,
        i: 0,
        depth: 0,
        in_modifier: false,
        safemath_active: false,
    };
    p.parse_program()
}

/// SOL-SAFEMATH: the OZ SafeMath method name → the CHECKED `BinOp` it lowers to. `None` for any
/// other method name (which then stays a `Call` → FE401 at check). Only the 5 UNSIGNED ops are
/// SafeMath here; `.tryAdd`/`.average`/`.ceilDiv`/SignedSafeMath (`int`) are out (they stay FE401).
fn safemath_binop(m: &str) -> Option<BinOp> {
    match m {
        "add" => Some(BinOp::Add),
        "sub" => Some(BinOp::Sub),
        "mul" => Some(BinOp::Mul),
        "div" => Some(BinOp::Div),
        "mod" => Some(BinOp::Mod),
        _ => None,
    }
}

/// SOL-ACCESS PR4: the synthesized per-field map name for a struct-map access `M[k].f`
/// / declaration explode — ONE encoding shared by the parse-time path rewrite and
/// `explode_struct_maps`' state-var synthesis (MC-4: the two sides can never disagree).
///
/// **INJECTIVE over `(var, field)`** — the length prefix is load-bearing, NOT cosmetic.
/// A naive `__fe_sm_{var}_{field}` is NON-injective because `_` is both the separator
/// AND a legal identifier char: var `a_b`/field `c` and var `a`/field `b_c` both collapse
/// to `__fe_sm_a_b_c`. An adversarial review CONFIRMED (3 lenses, HIGH) that this let a
/// NON-struct-map access `a_b[k].c` silently ALIAS struct-map `a`'s `b_c` slot — the
/// residual sweep checks name-set membership, and a colliding name passed it — defeating
/// the "never a silent shared slot / must reject loud" guarantee (a valid-Solidity trigger
/// exists: `a_b[k].balance` on an `address`-valued map). Emitting `__fe_sm_{len(var)}_{var}_{field}`
/// makes the split point unambiguous (read the length, take that many chars as the var,
/// the rest as the field), so DISTINCT pairs ⇒ DISTINCT names ⇒ set-membership IS
/// provenance. Under the reserved `__fe_` prefix (a user `__fe_` ident is FE420), so a
/// synthesized name can never alias a USER slot (MC-5). DO NOT drop the length prefix.
pub(super) fn struct_map_synth_name(var: &str, field: &str) -> String {
    format!("__fe_sm_{}_{var}_{field}", var.len())
}

/// SOL-ACCESS: is a string literal's RAW text safe to keccak-fold? The lexer stores the
/// raw bytes BETWEEN the quotes with escapes UNPROCESSED (and `from_utf8_lossy`), so a
/// `\` would make us hash the escape TEXT where solc hashes the escaped BYTE, and a
/// non-UTF-8 byte would hash a U+FFFD replacement — either is a constant of the WRONG
/// bytes that compiles (MC-3). Boring limit: printable ASCII (0x20..=0x7E) with no
/// backslash. This also matches solc's own grammar — a plain `""` literal is
/// printable-ASCII-only (non-ASCII needs the separate `unicode""` form) — and every
/// real role name (`MINTER_ROLE`) sits far inside. A refused literal is simply NOT
/// folded → the bare string fails expression parsing → FE401 (fail-closed).
fn keccak_foldable(raw: &str) -> bool {
    // Vacuously true for `""` — the canonical empty-string hash is a valid fold.
    raw.bytes()
        .all(|b| (0x20..=0x7e).contains(&b) && b != b'\\')
}

/// The Keccak-256 hash of the literal's exact ASCII bytes, as a SIGIL `0x…` u256 hex
/// literal (64 digits, leading zeros kept). `sha3::Keccak256` is the ETHEREUM Keccak
/// (the original pre-FIPS padding) — NOT `Sha3_256`, which produces a DIFFERENT digest
/// for every input. Vector integrity is pinned by named tests (`solidity_golden.rs`)
/// against independently published references (the on-chain `MINTER_ROLE` value; the
/// canonical empty-string hash) AND a second implementation (`tiny_keccak`) — EX-1.
fn keccak256_hex_literal(raw: &str) -> String {
    use sha3::{Digest, Keccak256};
    use std::fmt::Write as _;
    let digest = Keccak256::digest(raw.as_bytes());
    let mut s = String::with_capacity(66);
    s.push_str("0x");
    for b in digest {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// SOL-EVENTS: an `emit` argument is safe to DISCARD iff evaluating it has no observable effect — no
/// real function `Call` (a side effect / the internal-call anti-goal) and no trap-capable arithmetic
/// (`Bin` Add/Sub/Mul/Div/Mod, unary `Neg`). Mirrors `check::expr_has_checked_arith` but runs at
/// PARSE time (pre-types), so it is a purely syntactic walk. Trivial reads — `Var`/`Num`/`Bool`,
/// field/member reads, map `Index` reads, comparisons, `Unary(Not)` — are pure and trap-free.
///
/// A Solidity elementary-type CAST (`address(0)`, `uint8(x)`, `payable(a)`, …) lexes as a `Call`
/// whose callee names a type; it is a PURE truncating conversion that never reverts, so it is
/// discard-safe iff its arguments are (nested arithmetic inside the cast is still rejected). This is
/// load-bearing: `address(0)` dominates real event args (mint/burn from/to), so without it the
/// discard would over-reject ~12% of real contracts.
pub(super) fn emit_arg_discard_safe(e: &Expr) -> bool {
    match e {
        Expr::Num(..) | Expr::Bool(..) | Expr::Var(..) => true,
        Expr::Call(callee, args, _) => match &**callee {
            Expr::Var(name, _) if is_elementary_cast(name) => {
                args.iter().all(emit_arg_discard_safe)
            }
            // SOL-ACCESS: `_msgSender()` (zero-arg) is the OZ Context shim for `msg.sender`
            // — a PURE global read, so it is discard-safe (`emit RoleGranted(role, account,
            // _msgSender())`). SOUNDNESS depends on `_msgSender` actually being the pure
            // `return msg.sender;` shim; `desugar::reject_impure_msgsender` enforces exactly
            // that post-flatten (a `_msgSender` with any other body → FE481), so a
            // side-effecting fn of that name can never be silently dropped with the emit.
            Expr::Var(name, _) if name == "_msgSender" && args.is_empty() => true,
            _ => false, // a real function call — side effect / internal-call anti-goal
        },
        Expr::Member(base, _, _) => emit_arg_discard_safe(base),
        Expr::Index(base, key, _) => emit_arg_discard_safe(base) && emit_arg_discard_safe(key),
        Expr::Unary(op, inner, _) => *op != UnOp::Neg && emit_arg_discard_safe(inner),
        Expr::Bin(op, l, r, _) => {
            !matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
            ) && emit_arg_discard_safe(l)
                && emit_arg_discard_safe(r)
        }
    }
}

/// Is `name` a Solidity elementary type usable as a CAST callee (`address(x)`, `uint8(x)`, …)? Such
/// casts are pure, non-reverting truncations, so they are safe inside a discarded `emit`. A
/// conservative allow-list — any name not matched is treated as a real function call (rejected).
/// `pub(super)` so `check::check_identifier` can reject a user identifier colliding with one of these
/// (solc reserves them as keyword tokens, so no valid contract names a function/var an elementary
/// type — but rejecting it fail-closed prevents a user `function payable(){…}` from being silently
/// dropped as a "cast" inside a discarded emit).
pub(super) fn is_elementary_cast(name: &str) -> bool {
    match name {
        "address" | "payable" | "bool" | "string" | "bytes" | "uint" | "int" => true,
        _ => {
            if let Some(w) = name
                .strip_prefix("uint")
                .or_else(|| name.strip_prefix("int"))
            {
                // uintN / intN — N a multiple of 8 in [8, 256].
                matches!(w.parse::<u32>(), Ok(n) if (8..=256).contains(&n) && n % 8 == 0)
            } else if let Some(w) = name.strip_prefix("bytes") {
                // bytesN — N in [1, 32].
                matches!(w.parse::<u32>(), Ok(n) if (1..=32).contains(&n))
            } else {
                false
            }
        }
    }
}

/// A pure decimal-digit literal (no `0x`, no separators — the lexer already stripped `_`). Only
/// these are constant-folded for `**`; a hex literal takes the FE482 path (rare in real `**`).
fn is_decimal_digits(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

/// SOL-TOKEN: fold a decimal `base ** exp` to its decimal value, or `None` if it overflows the
/// u256 range (Solidity 0.8 reverts on `**` overflow → the caller maps `None` to FE430) or the
/// exponent is pathologically large. Both inputs are pure decimal digits (`is_decimal_digits`).
/// Worked entirely in decimal strings (no bignum dep) — `base`/`exp` fit `u64` (real `**` bases
/// and exponents are tiny; a base/exp that overflows `u64` yields `None`).
fn fold_pow_decimal(base: &str, exp: &str) -> Option<String> {
    let exp_v: u64 = exp.parse().ok()?;
    // Degenerate cases fold EXACTLY with no loop (faithful to Solidity, and a huge exponent on base
    // 0/1 still folds instead of mis-reporting "overflow"): `x ** 0 == 1` (incl. `0 ** 0 == 1`);
    // `x ** 1 == x` (base is an already-range-checked literal).
    if exp_v == 0 {
        return Some("1".to_string());
    }
    if exp_v == 1 {
        return Some(base.to_string());
    }
    let base_v: u64 = base.parse().ok()?;
    if base_v == 0 {
        return Some("0".to_string()); // 0 ** n == 0 for n ≥ 1
    }
    if base_v == 1 {
        return Some("1".to_string()); // 1 ** n == 1
    }
    // base ≥ 2: the result overflows 2^256 by exp ≈ 256, so any larger exponent is a guaranteed
    // overflow — bound the loop (it would FE430 anyway) so a pathological exponent can't spin.
    if exp_v > 4096 {
        return None;
    }
    let mut result = "1".to_string();
    for _ in 0..exp_v {
        result = mul_u64_decimal(&result, base_v);
        if !super::lexer::u256_decimal_in_range(&result) {
            return None;
        }
    }
    Some(result)
}

/// Multiply a decimal-digit string by a `u64` factor, returning the decimal product. Schoolbook
/// digit-by-digit with a `u128` carry (`9 * u64::MAX + carry < u128::MAX`, so no intermediate
/// overflow).
fn mul_u64_decimal(num: &str, factor: u64) -> String {
    let mut digits: Vec<u8> = Vec::with_capacity(num.len() + 20);
    let mut carry: u128 = 0;
    for ch in num.bytes().rev() {
        let prod = (ch - b'0') as u128 * factor as u128 + carry;
        digits.push((prod % 10) as u8);
        carry = prod / 10;
    }
    while carry > 0 {
        digits.push((carry % 10) as u8);
        carry /= 10;
    }
    if digits.is_empty() {
        return "0".to_string();
    }
    digits.iter().rev().map(|d| (d + b'0') as char).collect()
}

impl Parser {
    fn cur(&self) -> &TokKind {
        &self.toks[self.i].kind
    }
    fn span(&self) -> Range<usize> {
        self.toks[self.i].span.clone()
    }
    fn bump(&mut self) -> Range<usize> {
        let s = self.span();
        if self.i + 1 < self.toks.len() {
            self.i += 1;
        }
        s
    }
    fn at(&self, k: &TokKind) -> bool {
        self.cur() == k
    }

    fn err(&self, code: &'static str, msg: impl Into<String>) -> FrontendDiag {
        FrontendDiag::new(code, msg, self.span())
    }

    /// Recursion-depth guard threaded through EVERY recursive descent AND every
    /// flat operator/postfix chain (see the precedence loops, which `enter` once
    /// per accumulated node). Bounds total AST nesting at `MAX_NEST_DEPTH` so
    /// adversarial nesting — deep `if`, `else if` chains, `unchecked` nesting,
    /// `!`/`-` chains, parenthesised exprs, AND flat `a+b+c+…` / `a.b.c…` chains —
    /// yields an `FE402` reject BEFORE a deep AST is ever built. Crucial: a flat
    /// chain parses at constant recursion depth but yields an N-deep AST that would
    /// otherwise overflow the native stack in the downstream walkers / trusted
    /// re-parse / recursive `Drop`. This frontend OWNS totality (threat T12): the
    /// `Frontend` trait requires every input to terminate with `Ok`/`Err`, never a
    /// crash/hang. `leave` is skipped on the error path because the whole parse
    /// unwinds on the first error, so the stale counter is never observed.
    fn enter(&mut self) -> Result<(), FrontendDiag> {
        self.depth += 1;
        if self.depth > MAX_NEST_DEPTH {
            return Err(self.err(
                codes::FE402_TOO_LARGE_SOL,
                format!("nesting exceeds depth {MAX_NEST_DEPTH}"),
            ));
        }
        Ok(())
    }
    fn leave(&mut self) {
        self.depth -= 1;
    }

    fn expect(&mut self, k: TokKind, what: &str) -> Result<Range<usize>, FrontendDiag> {
        if self.cur() == &k {
            Ok(self.bump())
        } else {
            Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                format!("expected {what}, found {:?}", self.cur()),
            ))
        }
    }

    /// An identifier OR a type-name token (both lex as `Ident`). Returns (text, span).
    fn expect_ident(&mut self, what: &str) -> Result<(String, Range<usize>), FrontendDiag> {
        if let TokKind::Ident(name) = self.cur() {
            let name = name.clone();
            let s = self.bump();
            Ok((name, s))
        } else {
            Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                format!("expected {what}, found {:?}", self.cur()),
            ))
        }
    }

    /// SOL-INH: parse the whole file — pragmas, `import` lines, and all top-level
    /// `contract`/`abstract contract`/`interface`/`library` declarations (in source order) →
    /// a `ParsedFile`. `flatten` (M1) reduces the contract list to one; until then `mod.rs`
    /// bridges a single-concrete-no-bases file to the existing pipeline.
    fn parse_program(&mut self) -> Result<ParsedFile, FrontendDiag> {
        const MAX_CONTRACTS: usize = 64; // SOL-INH totality bound (EX-8)
        let mut pragma = None;
        let mut contracts = Vec::new();
        let mut imports = Vec::new();
        loop {
            match self.cur() {
                TokKind::Eof => break,
                // Pragmas may appear anywhere (`pragma abicoder v2;` etc.); keep the last
                // `solidity` one (word-boundary checked so `solidity8.0` is NOT adopted),
                // skip the rest. `check.rs` version-checks the body.
                TokKind::Pragma(body) => {
                    let body = body.clone();
                    let s = self.bump();
                    let trimmed = body.trim_start();
                    let is_solidity_pragma = trimmed == "solidity"
                        || trimmed
                            .strip_prefix("solidity")
                            .is_some_and(|r| r.starts_with(|c: char| c.is_whitespace()));
                    if is_solidity_pragma {
                        pragma = Some((body, s));
                    }
                }
                // SOL-INH: a top-level `import` — discard a plain/named one, reject aliased
                // (FE476). SOL-XFILE: the path text is CAPTURED for the project resolver.
                TokKind::Ident(n) if n == "import" => {
                    if let Some(imp) = self.parse_import()? {
                        imports.push(imp);
                    }
                }
                // SOL-SAFEMATH: `using SafeMath for uint256;` → set the flag + discard; every other
                // `using X for Y;` (free-function attachment) stays deferred (FE477).
                TokKind::Ident(n) if n == "using" => self.parse_using()?,
                // SOL-SYNTAX: a FILE-LEVEL custom `error Name(params);` declaration is DISCARDED
                // (same rationale as the contract-member arm — the lowering never consults an error
                // signature; `revert` is an unconditional `trap()`).
                TokKind::Ident(n) if n == "error" => self.parse_error_discard()?,
                _ => {
                    if contracts.len() >= MAX_CONTRACTS {
                        return Err(self.err(
                            codes::FE402_TOO_LARGE_SOL,
                            format!("too many top-level contracts (max {MAX_CONTRACTS})"),
                        ));
                    }
                    contracts.push(self.parse_contract()?);
                }
            }
        }
        Ok(ParsedFile {
            pragma,
            contracts,
            imports,
        })
    }

    /// SOL-INH: a top-level `import`. A plain/named import is DISCARDED (in a self-contained
    /// flattened file the imported symbols are inline, so the line is redundant); an aliased or
    /// namespaced import (`… as Name`, `import * …`) renames a symbol flatten can't silently
    /// drop → FE476. Consumes to the terminating `;`. (A string PATH is one `Str` token, so an
    /// "as" inside the path text is never mistaken for the alias keyword.)
    /// SOL-SAFEMATH: recognize a `using SafeMath for uint256;` (or the `uint` alias) directive → set
    /// the `safemath_active` flag and DISCARD it (a directive has no SIGIL target). EVERY other
    /// well-formed `using X for Y;` (a free-function / library attachment) is a fail-closed FE477 —
    /// never a silent accept. Called at both file scope and contract-member scope; consumes the `;`.
    fn parse_using(&mut self) -> Result<(), FrontendDiag> {
        self.bump(); // `using`
        let (lib, _) = self.expect_ident("a library name after `using`")?;
        if !matches!(self.cur(), TokKind::Ident(n) if n == "for") {
            return Err(self.err(
                codes::FE477_USING_FOR_SOL,
                "`using X for Y;` is unsupported",
            ));
        }
        self.bump(); // `for`
        let (ty, _) = self.expect_ident("a target type after `for`")?;
        self.expect(TokKind::Semi, "`;` to end the `using` directive")?;
        if lib == "SafeMath" && (ty == "uint256" || ty == "uint") {
            self.safemath_active = true;
            Ok(())
        } else {
            Err(self.err(
                codes::FE477_USING_FOR_SOL,
                "`using X for Y;` is unsupported (only `using SafeMath for uint256` is recognized)",
            ))
        }
    }

    /// SOL-XFILE: returns the import's PATH (the first — and, in every accepted form, only —
    /// string literal in the statement: `import "p";` and `import {A, B} from "p";` both carry
    /// exactly one) + its span, or `None` for a degenerate pathless `import;`. The named symbol
    /// list stays DISCARDED — project resolution is by globally-unique contract NAME, so the
    /// symbol list carries nothing the union's duplicate-name gate doesn't already enforce.
    fn parse_import(&mut self) -> Result<Option<(String, Range<usize>)>, FrontendDiag> {
        self.bump(); // `import`
        let mut path: Option<(String, Range<usize>)> = None;
        loop {
            match self.cur() {
                TokKind::Semi => {
                    self.bump();
                    return Ok(path);
                }
                TokKind::Eof => {
                    return Err(self.err(
                        codes::FE401_UNSUPPORTED_SOL,
                        "unterminated `import` (missing `;`)",
                    ));
                }
                TokKind::Star => {
                    return Err(self.err(
                        codes::FE476_IMPORT_OR_BASE_SOL,
                        "a namespaced import (`import * as M from …`) is unsupported (the namespace can't be flattened)",
                    ));
                }
                TokKind::Ident(n) if n == "as" => {
                    return Err(self.err(
                        codes::FE476_IMPORT_OR_BASE_SOL,
                        "an aliased import (`… as Name`) is unsupported (the alias renames a symbol flatten can't drop)",
                    ));
                }
                TokKind::Str(s) => {
                    if path.is_none() {
                        let text = s.clone();
                        let span = self.bump();
                        path = Some((text, span));
                    } else {
                        // A second string literal in one import is out of the accepted
                        // grammar (fail-closed — never silently pick one of two paths).
                        return Err(self.err(
                            codes::FE476_IMPORT_OR_BASE_SOL,
                            "an `import` with more than one string literal is unsupported",
                        ));
                    }
                }
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// SOL-INH: parse an optional `is Base1, Base2(args), …` after a contract name. PR1 parses
    /// the base NAMES (args are skipped here and parsed in M2's ctor-chaining); a single
    /// contract with no `is` clause keeps `bases` empty (the byte-identical path).
    fn parse_inheritance_list(&mut self) -> Result<Vec<BaseRef>, FrontendDiag> {
        const MAX_BASES: usize = 32; // SOL-INH totality bound (EX-8: linearized count)
        let mut bases = Vec::new();
        if !matches!(self.cur(), TokKind::Ident(n) if n == "is") {
            return Ok(bases);
        }
        self.bump(); // `is`
        loop {
            let (name, span) = self.expect_ident("base contract name")?;
            // Skip an optional `(args)` ctor-arg list (parsed in M2); args stay empty in M0.
            if self.at(&TokKind::LParen) {
                self.skip_token_group(TokKind::LParen, TokKind::RParen)?;
            }
            if bases.len() >= MAX_BASES {
                return Err(self.err(
                    codes::FE402_TOO_LARGE_SOL,
                    format!("inheritance list exceeds {MAX_BASES} bases"),
                ));
            }
            bases.push(BaseRef {
                name,
                args: Vec::new(),
                span,
            });
            if self.at(&TokKind::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        Ok(bases)
    }

    /// SOL-INH: skip a balanced `open`/`close` token group, the CURRENT token being `open`.
    /// Token-level (the lexer already balanced strings/comments into tokens, so a brace inside
    /// `"…"` is impossible here). Depth-bounded by the parser's overall token count; returns the
    /// `close` token's span.
    fn skip_token_group(
        &mut self,
        open: TokKind,
        close: TokKind,
    ) -> Result<Range<usize>, FrontendDiag> {
        let mut depth = 0u32;
        loop {
            if self.at(&TokKind::Eof) {
                return Err(self.err(codes::FE401_UNSUPPORTED_SOL, "unbalanced `(`/`{` group"));
            } else if self.at(&open) {
                depth += 1;
                self.bump();
            } else if self.at(&close) {
                depth -= 1;
                let s = self.bump();
                if depth == 0 {
                    return Ok(s);
                }
            } else {
                self.bump();
            }
        }
    }

    fn parse_contract(&mut self) -> Result<Contract, FrontendDiag> {
        // SOL-INH: the declaration kind — `abstract contract` / `contract` / `interface` /
        // `library`. `contract` is a keyword token; the others are bare idents.
        let (kind, start) = match self.cur() {
            TokKind::Contract => (ContractKind::Concrete, self.bump()),
            TokKind::Ident(n) if n == "abstract" => {
                let s = self.bump();
                self.expect(TokKind::Contract, "`contract` after `abstract`")?;
                (ContractKind::Abstract, s)
            }
            TokKind::Ident(n) if n == "interface" => (ContractKind::Interface, self.bump()),
            TokKind::Ident(n) if n == "library" => (ContractKind::Library, self.bump()),
            other => {
                return Err(self.err(
                    codes::FE401_UNSUPPORTED_SOL,
                    format!(
                        "expected a top-level `contract`/`interface`/`library`/`abstract`, found {other:?}"
                    ),
                ));
            }
        };
        let (name, _) = self.expect_ident("contract name")?;
        let bases = self.parse_inheritance_list()?;
        // SOL-XFILE PR2/L2: an INTERFACE or LIBRARY body is SKIPPED — an interface's members are
        // bodiless signatures that contribute nothing to a flattened concrete; a library is out
        // of the subset (FE476 if used as an inheritance base). But an ABSTRACT contract's body
        // IS parsed exactly like a concrete one: its members are the real implementation a
        // derived contract inherits (OZ's `abstract contract ERC20 { … }` is the canonical case).
        // An abstract contract is still never a deployable sink (`select_main`); a bodiless
        // `virtual` declaration or any out-of-subset member inside it is a fail-closed reject via
        // the normal member parsing.
        if matches!(kind, ContractKind::Interface | ContractKind::Library) {
            if !self.at(&TokKind::LBrace) {
                return Err(self.err(
                    codes::FE401_UNSUPPORTED_SOL,
                    "expected `{` after the contract head",
                ));
            }
            let end = self.skip_token_group(TokKind::LBrace, TokKind::RBrace)?;
            return Ok(Contract {
                name,
                kind,
                bases,
                structs: Vec::new(),
                state: Vec::new(),
                functions: Vec::new(),
                modifiers: Vec::new(),
                constructor: None,
                enums: Vec::new(),
                span: start.start..end.end,
            });
        }
        self.expect(TokKind::LBrace, "`{`")?;
        let mut state = Vec::new();
        let mut functions = Vec::new();
        let mut modifiers = Vec::new();
        let mut structs = Vec::new();
        let mut enums = Vec::new();
        let mut constructor: Option<Constructor> = None;
        while !self.at(&TokKind::RBrace) && !self.at(&TokKind::Eof) {
            if self.at(&TokKind::Function) {
                if functions.len() >= MAX_FUNCTIONS {
                    return Err(self.err(codes::FE402_TOO_LARGE_SOL, "too many functions"));
                }
                functions.push(self.parse_function()?);
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "modifier") {
                // SOL1c: a `modifier name() { … _ … }` declaration. `modifier` lexes as a
                // bare ident, but only ever leads a contract member here as a modifier decl
                // (a state var starts with a TYPE, a function with `function`). Bound the
                // count like functions (totality, FE402).
                if modifiers.len() >= MAX_FUNCTIONS {
                    return Err(self.err(codes::FE402_TOO_LARGE_SOL, "too many modifiers"));
                }
                modifiers.push(self.parse_modifier()?);
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "event") {
                // SOL-EVENTS: `event Name(...) [anonymous];` is DISCARDED — events carry no SIGIL
                // state/funds/control-flow effect, so the faithful lowering is nothing. Consume the
                // whole declaration (no `;` appears inside an event param list, so a skip to the
                // terminating `;` is safe + tolerates `indexed`/`anonymous`); produce no member.
                self.bump(); // `event`
                while !self.at(&TokKind::Semi) && !self.at(&TokKind::Eof) {
                    self.bump();
                }
                self.expect(TokKind::Semi, "`;` to end the `event` declaration")?;
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "error") {
                // SOL-SYNTAX: a custom `error Name(params);` declaration is DISCARDED (mirrors the
                // `event` arm). `revert CustomError(...)` already lowers to an unconditional `trap()`
                // dropping the name + args (SOL-DIVERGE), so the DECL carries no information the
                // translation uses. `error` leads a member only as a custom-error decl (a state var
                // leads with a TYPE, a function with `function`).
                self.parse_error_discard()?;
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "string")
                && !matches!(
                    self.toks.get(self.i + 1).map(|t| &t.kind),
                    Some(TokKind::LBracket)
                )
            {
                // SOL-TOKEN: a SCALAR `string` STATE VARIABLE (`string [public] name [= "lit"];`) is
                // DROPPED — a string is pure metadata (name/symbol) with no SIGIL state/funds/
                // control-flow effect, and SIGIL has no string type. Skip the whole declaration (a
                // `;` inside a `"…"` is part of the single `Str` token, so a skip to the terminating
                // `;` is safe). A READ of the dropped field elsewhere surfaces as an undefined
                // identifier (fail-closed); `string` in a param/return/local stays FE410
                // (resolve_ty's allow-list). The `!LBracket` guard keeps a `string[]` ARRAY on the
                // normal (unsupported-array) reject path — only scalar metadata is dropped. Only
                // fires at member scope, where `string` always leads a state var (return/param
                // strings live inside function signatures).
                self.bump(); // `string`
                while !self.at(&TokKind::Semi) && !self.at(&TokKind::Eof) {
                    self.bump();
                }
                self.expect(TokKind::Semi, "`;` to end the `string` state variable")?;
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "struct") {
                // SOL-STRUCT: a `struct Name { … }` declaration. `struct` lexes as a bare
                // ident but only ever leads a contract member here as a struct decl (a
                // state var starts with a TYPE, a function with `function`). Bound the
                // count like functions/modifiers (totality, FE402).
                if structs.len() >= MAX_FUNCTIONS {
                    return Err(self.err(codes::FE402_TOO_LARGE_SOL, "too many structs"));
                }
                structs.push(self.parse_struct()?);
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "enum") {
                // SOL-ENUM: an `enum Name { A, B, C }` declaration. `enum` lexes as a bare
                // ident but only ever leads a contract member here as an enum decl. Bound the
                // count like functions/structs (totality, FE402); `parse_enum` caps members.
                if enums.len() >= MAX_FUNCTIONS {
                    return Err(self.err(codes::FE402_TOO_LARGE_SOL, "too many enums"));
                }
                enums.push(self.parse_enum()?);
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "using") {
                // SOL-SAFEMATH: a contract-scope `using SafeMath for uint256;` (the common OZ
                // position) → set the flag + discard; other `using X for Y;` → FE477. Produces no
                // member.
                self.parse_using()?;
            } else if matches!(self.cur(), TokKind::Ident(n) if n == "constructor") {
                // SOL-CTOR: a `constructor(params) { body }`. `constructor` lexes as a bare
                // ident but is RESERVED in Solidity, so it never leads a state var — like the
                // sibling `modifier`/`struct` arms, dispatch on the bare ident. At most one
                // per contract (EX-3, FE463).
                if constructor.is_some() {
                    return Err(self.err(
                        codes::FE463_DUPLICATE_CONSTRUCTOR_SOL,
                        "a contract may declare at most one `constructor`",
                    ));
                }
                constructor = Some(self.parse_constructor()?);
            } else {
                // A state variable declaration: `T name [= init];`
                state.push(self.parse_state_var()?);
            }
        }
        let end = self.expect(TokKind::RBrace, "`}`")?;
        Ok(Contract {
            name,
            // SOL-XFILE PR2/L2: the body-parsing path serves BOTH `Concrete` and `Abstract`
            // (only Interface/Library skip the body above), so preserve the DETECTED kind —
            // hardcoding `Concrete` here would relabel an abstract as deployable (it would
            // become a spurious `select_main` sink).
            kind,
            bases,
            structs,
            state,
            functions,
            modifiers,
            constructor,
            enums,
            span: start.start..end.end,
        })
    }

    /// SOL-CTOR: parse `constructor(params) <attrs> { body }`. No name, no return type. The
    /// attribute window between `)` and `{` IGNORES deprecated `public`/`internal` and
    /// REJECTS everything else precisely (EX-4 → FE464): `payable`, a base-constructor call
    /// or a modifier (both bare idents), a `returns` clause, or any `view`/`pure`/`external`.
    fn parse_constructor(&mut self) -> Result<Constructor, FrontendDiag> {
        let start = self.bump(); // `constructor`
        let params = self.parse_param_list()?;
        let mut base_calls: Vec<BaseCtorCall> = Vec::new();
        loop {
            match self.cur().clone() {
                TokKind::Public | TokKind::Internal => {
                    self.bump(); // deprecated visibility no-ops — ignore
                }
                TokKind::LBrace => break,
                // SOL-XFILE PR4/L3: `Name(args)` in the attribute window is a base-constructor
                // invocation (`ERC20("N","S")`). RECORD the base name + whether every argument
                // token is a literal, and DROP the arguments (the reduction makes the call a
                // no-op). A bare `Name` with no `(` is a modifier on the constructor — still FE464.
                TokKind::Ident(a) => {
                    let name_span = self.bump(); // the base/modifier name
                    if !self.at(&TokKind::LParen) {
                        return Err(self.err(
                            codes::FE464_UNSUPPORTED_CTOR_SOL,
                            format!(
                                "unsupported constructor form `{a}` (a `payable` constructor or a modifier on the constructor is out of the closed-contract subset; a base-constructor call needs `(`)"
                            ),
                        ));
                    }
                    self.bump(); // `(`
                    // Token-level scan of the balanced argument list: `all_literal` iff every inner
                    // token is a string/number/bool literal or a comma. A nested `(`, an identifier,
                    // or any operator marks it non-literal (→ FE468 at flatten, never a dropped
                    // effect). We do NOT parse the arguments as `Expr` (a string literal is not an
                    // `Expr`); we only need the literal-ness verdict.
                    let mut depth = 1usize;
                    let mut all_literal = true;
                    let mut end = name_span.clone();
                    while depth > 0 {
                        match self.cur() {
                            TokKind::Eof => {
                                return Err(self.err(
                                    codes::FE464_UNSUPPORTED_CTOR_SOL,
                                    "unterminated base-constructor argument list",
                                ));
                            }
                            TokKind::LParen => {
                                depth += 1;
                                all_literal = false;
                                end = self.bump();
                            }
                            TokKind::RParen => {
                                depth -= 1;
                                end = self.bump();
                            }
                            TokKind::Str(_)
                            | TokKind::Num(_)
                            | TokKind::True
                            | TokKind::False
                            | TokKind::Comma => {
                                end = self.bump();
                            }
                            _ => {
                                all_literal = false;
                                end = self.bump();
                            }
                        }
                    }
                    base_calls.push(BaseCtorCall {
                        name: a,
                        all_literal,
                        span: name_span.start..end.end,
                    });
                }
                _ => {
                    return Err(self.err(
                        codes::FE464_UNSUPPORTED_CTOR_SOL,
                        "unsupported constructor attribute (no `returns`/`view`/`pure`/`external` on a constructor)",
                    ));
                }
            }
        }
        let (body, end) = self.parse_block()?;
        Ok(Constructor {
            params,
            body,
            base_calls,
            span: start.start..end.end,
        })
    }

    /// SOL-STRUCT: parse `struct Name { T field; … }`. Fields are `T name;` lines; a
    /// trailing comma after a field is tolerated. A struct-typed field parses as
    /// `TypeRef::Scalar { name }` (check.rs resolves it nominally). The field count is
    /// bounded for totality (FE402). An empty struct (`struct S { }`) parses to zero
    /// fields; check.rs rejects it (a zero-field record is degenerate).
    fn parse_struct(&mut self) -> Result<Struct, FrontendDiag> {
        let start = self.bump(); // `struct`
        let (name, _) = self.expect_ident("struct name")?;
        self.expect(TokKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while !self.at(&TokKind::RBrace) && !self.at(&TokKind::Eof) {
            if fields.len() >= MAX_FUNCTIONS {
                return Err(self.err(codes::FE402_TOO_LARGE_SOL, "too many struct fields"));
            }
            let ty = self.parse_type()?;
            let (fname, fspan) = self.expect_ident("struct field name")?;
            self.expect(TokKind::Semi, "`;` after struct field")?;
            // Tolerate a trailing comma between fields (some styles use it).
            if self.at(&TokKind::Comma) {
                self.bump();
            }
            fields.push(StructField {
                span: ty.span().start..fspan.end,
                name: fname,
                ty,
            });
        }
        let end = self.expect(TokKind::RBrace, "`}`")?;
        Ok(Struct {
            span: start.start..end.end,
            name,
            fields,
        })
    }

    /// SOL-ENUM: parse `enum Name { A, B, C }`. Members are comma-separated bare idents
    /// (source order = the 0-based tag). NO trailing comma (solc-faithful, mirrors
    /// `parse_param_list`). At most 256 members (the Solidity cap = our totality bound →
    /// FE402). An explicit discriminant (`A = 3`) → FE401 (solc has no such syntax). check.rs
    /// rejects an empty or duplicate-member enum (FE467).
    fn parse_enum(&mut self) -> Result<Enum, FrontendDiag> {
        let start = self.bump(); // `enum`
        let (name, _) = self.expect_ident("enum name")?;
        self.expect(TokKind::LBrace, "`{`")?;
        let mut members = Vec::new();
        while !self.at(&TokKind::RBrace) && !self.at(&TokKind::Eof) {
            if members.len() >= 256 {
                return Err(self.err(
                    codes::FE402_TOO_LARGE_SOL,
                    "an enum may have at most 256 members",
                ));
            }
            let (m, _) = self.expect_ident("enum member name")?;
            members.push(m);
            if self.at(&TokKind::Assign) {
                return Err(self.err(
                    codes::FE401_UNSUPPORTED_SOL,
                    "explicit enum member values (`A = N`) are unsupported",
                ));
            }
            if self.at(&TokKind::Comma) {
                self.bump();
                // A trailing comma (`,}`) is a solc parse error — require a member next.
                if self.at(&TokKind::RBrace) {
                    return Err(self.err(
                        codes::FE401_UNSUPPORTED_SOL,
                        "trailing comma in enum member list",
                    ));
                }
            } else {
                break;
            }
        }
        let end = self.expect(TokKind::RBrace, "`}` to close enum")?;
        Ok(Enum {
            span: start.start..end.end,
            name,
            members,
        })
    }

    /// SOL1c: parse `modifier name() { … _ … }`. Parameterless only — a non-empty
    /// parameter list is a parameterized modifier (FE448). The body is parsed with
    /// `in_modifier` set so `_;` becomes `Stmt::Placeholder`, and must contain EXACTLY
    /// ONE placeholder (FE447), counted across nested `if` branches.
    fn parse_modifier(&mut self) -> Result<Modifier, FrontendDiag> {
        let start = self.bump(); // `modifier`
        let (name, _) = self.expect_ident("modifier name")?;
        // SOL-ACCESS: an optional parameter list. Parameterless (`modifier m {…}` / `m() {…}`)
        // and parameterized (`modifier onlyRole(bytes32 role) {…}`) are both accepted;
        // `inline_modifiers` binds each param to its application arg eval-once.
        let params = if self.at(&TokKind::LParen) {
            self.parse_param_list()?
        } else {
            Vec::new()
        };
        // Parse the body in modifier mode so `_;` is a Placeholder. Restore the flag
        // before propagating any error (the whole parse unwinds on error anyway).
        self.in_modifier = true;
        let r = self.parse_block();
        self.in_modifier = false;
        let (body, end) = r?;
        let n = count_placeholders(&body);
        if n != 1 {
            return Err(FrontendDiag::new(
                codes::FE447_MODIFIER_PLACEHOLDER_SOL,
                format!("a modifier body must contain exactly one `_;` placeholder (found {n})"),
                start.start..end.end,
            ));
        }
        Ok(Modifier {
            span: start.start..end.end,
            name,
            params,
            body,
        })
    }

    fn parse_type(&mut self) -> Result<TypeRef, FrontendDiag> {
        // `mapping ( K => V )` — `mapping` lexes as a bare `Ident`. The recursive
        // descent (key/value are themselves types) is depth-guarded so a deeply
        // nested mapping type yields FE402, never a native stack overflow.
        if matches!(self.cur(), TokKind::Ident(name) if name == "mapping") {
            self.enter()?;
            let r = self.parse_mapping_type();
            self.leave();
            return r;
        }
        let (name, span) = self.expect_ident("a type name")?;
        let base = TypeRef::Scalar {
            name,
            span: span.clone(),
        };
        // SOL-AIRDROP (Rung C): a SINGLE trailing unsized `[]` on a scalar element → a
        // dynamic array type (the airdrop's `recipients`/`amounts` arrays). In a TYPE
        // position a `[` can only be an array marker; anything but an immediate `]` (a
        // sized `[N]`) is fail-closed FE491 (only unsized `T[]` is supported). A 2-D
        // `T[][]` leaves the second `[` for the caller's next `expect` (fail-closed FE401).
        // `check::resolve_ty` gates an array to PARAMETER position (FE491 elsewhere).
        if self.at(&TokKind::LBracket) {
            let lb = self.bump(); // `[`
            if self.at(&TokKind::RBracket) {
                let rb = self.bump(); // `]`
                return Ok(TypeRef::Array {
                    elem: Box::new(base),
                    span: span.start..rb.end,
                });
            }
            return Err(FrontendDiag::new(
                codes::FE491_ARRAY_TYPE_SOL,
                "only an unsized dynamic array `T[]` is supported (a fixed-size `T[N]` is not)",
                lb,
            ));
        }
        Ok(base)
    }

    fn parse_mapping_type(&mut self) -> Result<TypeRef, FrontendDiag> {
        let start = self.bump(); // `mapping`
        self.expect(TokKind::LParen, "`(` after `mapping`")?;
        let key = self.parse_type()?;
        // SOL-SYNTAX: Solidity ≥0.8.18 allows an OPTIONAL name after the key type
        // (`mapping(uint256 id => …)`) — pure documentation, zero semantic effect (no AST field).
        // Consume-and-discard it; the required `=>` below catches a wrong consume (fail-closed).
        if matches!(self.cur(), TokKind::Ident(_)) {
            self.bump();
        }
        self.expect(TokKind::FatArrow, "`=>` in mapping type")?;
        let value = self.parse_type()?;
        // SOL-SYNTAX: and an OPTIONAL name after the value type (`mapping(K => V bal)`) — same. The
        // required `)` below catches a wrong consume. Nested `mapping(K => mapping(...) name)` is
        // safe: the inner `)` was consumed by the recursive `parse_type`, so only the OUTER name is
        // seen here.
        if matches!(self.cur(), TokKind::Ident(_)) {
            self.bump();
        }
        let end = self.expect(TokKind::RParen, "`)` to close mapping type")?;
        Ok(TypeRef::Mapping {
            key: Box::new(key),
            value: Box::new(value),
            span: start.start..end.end,
        })
    }

    fn parse_state_var(&mut self) -> Result<StateVar, FrontendDiag> {
        let ty = self.parse_type()?;
        // Skip a visibility marker (public/private/internal) and the `constant`/
        // `immutable` mutability modifiers. Neither carries SIGIL storage semantics: a
        // `constant`/`immutable` with a compile-time-literal initializer is modeled as a
        // record field seeded with that literal (the initializer already flows to emit),
        // and a `public` auto-getter is dropped. `constant`/`immutable` are reserved
        // Solidity keywords, so they can never be the variable NAME — consuming them here
        // cannot swallow the identifier. (SOL-ACCESS wall 1.)
        while matches!(
            self.cur(),
            TokKind::Public | TokKind::Private | TokKind::Internal
        ) || matches!(self.cur(), TokKind::Ident(n) if n == "constant" || n == "immutable")
        {
            self.bump();
        }
        let (name, _) = self.expect_ident("state variable name")?;
        let init = if self.at(&TokKind::Assign) {
            self.bump();
            Some(self.parse_expr()?)
        } else {
            None
        };
        let end = self.expect(TokKind::Semi, "`;`")?;
        Ok(StateVar {
            span: ty.span().start..end.end,
            name,
            ty,
            init,
        })
    }

    /// Parse a `( T name, T name, … )` parameter list (each param: a type, an optional
    /// `memory`/`storage`/`calldata` data location, a name; trailing comma not allowed).
    /// Shared by `parse_function` and `parse_constructor` so the two cannot drift.
    fn parse_param_list(&mut self) -> Result<Vec<Param>, FrontendDiag> {
        self.expect(TokKind::LParen, "`(`")?;
        let mut params = Vec::new();
        while !self.at(&TokKind::RParen) {
            let ty = self.parse_type()?;
            // optional data location
            while matches!(
                self.cur(),
                TokKind::Memory | TokKind::Storage | TokKind::Calldata
            ) {
                self.bump();
            }
            let (pname, pspan) = self.expect_ident("parameter name")?;
            params.push(Param {
                span: ty.span().start..pspan.end,
                name: pname,
                ty,
            });
            if self.at(&TokKind::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(TokKind::RParen, "`)`")?;
        Ok(params)
    }

    fn parse_function(&mut self) -> Result<Function, FrontendDiag> {
        let start = self.expect(TokKind::Function, "`function`")?;
        let (name, _) = self.expect_ident("function name")?;
        let params = self.parse_param_list()?;

        // Visibility + mutability markers + modifier applications, in any order, until
        // `returns` or `{`. (Match an OWNED clone of the token so the modifier-name arm
        // can bind the ident and still call `self.bump()` — mirrors `parse_primary`.)
        let mut visibility = Visibility::Default;
        let mut mutability = StateMutability::NonPayable;
        let mut modifiers: Vec<ModifierApp> = Vec::new();
        loop {
            match self.cur().clone() {
                TokKind::Public => {
                    visibility = Visibility::Public;
                    self.bump();
                }
                TokKind::Private => {
                    visibility = Visibility::Private;
                    self.bump();
                }
                TokKind::Internal => {
                    visibility = Visibility::Internal;
                    self.bump();
                }
                TokKind::External => {
                    visibility = Visibility::External;
                    self.bump();
                }
                TokKind::View => {
                    mutability = StateMutability::View;
                    self.bump();
                }
                TokKind::Pure => {
                    mutability = StateMutability::Pure;
                    self.bump();
                }
                // A modifier application is a bare ident in this position.
                // `payable`/`virtual`/`override` also lex as idents. SOL-INH: `virtual`/`override`
                // are inheritance SPECIFIERS with no flatten semantics (the function NAME is the
                // override key), so ACCEPT and ignore them — `override(Base1, Base2)` carries an
                // optional base list, which we skip. `payable` is still unsupported → FE452.
                // SOL-ACCESS: a modifier ARGUMENT list (`onlyRole(getRoleAdmin(role))`) is CAPTURED
                // as arg expressions (bound eval-once at inline time); an empty `()` is a
                // parameterless application (`onlyOwner()`).
                TokKind::Ident(mname) => {
                    if mname == "payable" {
                        return Err(self.err(
                            codes::FE452_UNSUPPORTED_ATTRIBUTE_SOL,
                            "function attribute `payable` is unsupported",
                        ));
                    }
                    if mname == "virtual" || mname == "override" {
                        self.bump();
                        if mname == "override" && self.at(&TokKind::LParen) {
                            self.skip_token_group(TokKind::LParen, TokKind::RParen)?;
                        }
                        continue;
                    }
                    let mstart = self.bump();
                    let mut args = Vec::new();
                    let mut mend = mstart.end;
                    if self.at(&TokKind::LParen) {
                        self.bump(); // `(`
                        while !self.at(&TokKind::RParen) {
                            args.push(self.parse_expr()?);
                            if self.at(&TokKind::Comma) {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                        mend = self.expect(TokKind::RParen, "`)`")?.end;
                    }
                    if modifiers.len() >= MAX_MODIFIERS_PER_FN {
                        return Err(self.err(
                            codes::FE402_TOO_LARGE_SOL,
                            "too many modifiers on a function",
                        ));
                    }
                    modifiers.push(ModifierApp {
                        name: mname,
                        args,
                        span: mstart.start..mend,
                    });
                }
                _ => break,
            }
        }

        let ret = if self.at(&TokKind::Returns) {
            self.bump();
            self.expect(TokKind::LParen, "`(`")?;
            let t = self.parse_type()?;
            // optional data location on the return type
            while matches!(
                self.cur(),
                TokKind::Memory | TokKind::Storage | TokKind::Calldata
            ) {
                self.bump();
            }
            self.expect(TokKind::RParen, "`)`")?;
            Some(t)
        } else {
            None
        };

        // SOL-XFILE PR2/L2: a bodiless abstract declaration ends at `;` instead of a `{ … }`
        // block. Accept it (an abstract `virtual` signature) — `flatten::merge` drops it if a
        // derived contract implements it, or rejects FE475 if one survives the merge. A modifier
        // application on a bodiless decl is meaningless but harmless (nothing to guard).
        let (body, bodiless, end) = if self.at(&TokKind::Semi) {
            let semi = self.bump();
            (Vec::new(), true, semi)
        } else {
            let (b, e) = self.parse_block()?;
            (b, false, e)
        };
        Ok(Function {
            span: start.start..end.end,
            name,
            params,
            ret,
            visibility,
            mutability,
            modifiers,
            body,
            bodiless,
        })
    }

    /// Parse a `{ … }` block of statements. Returns (stmts, closing-brace span).
    /// Depth-guarded: nested blocks (and `unchecked { … }` nesting) descend here.
    fn parse_block(&mut self) -> Result<(Vec<Stmt>, Range<usize>), FrontendDiag> {
        self.enter()?;
        let r = self.parse_block_inner();
        self.leave();
        r
    }

    fn parse_block_inner(&mut self) -> Result<(Vec<Stmt>, Range<usize>), FrontendDiag> {
        self.expect(TokKind::LBrace, "`{`")?;
        let mut stmts = Vec::new();
        while !self.at(&TokKind::RBrace) && !self.at(&TokKind::Eof) {
            // SOL-EVENTS: an `emit Name(args);` is DISCARDED here — the SOLE statement-collection
            // loop, so it covers every body (function/constructor/modifier/if/else/nested) and
            // produces NO `Stmt` (no exhaustive-match walker tax). The lookahead (`emit` then an
            // Ident) keeps a user variable named `emit` on the assignment path. Discarding an emit
            // INTERLEAVED in a debit/credit pair makes the two writes adjacent — it only helps the
            // transfer recognizer. An effectful arg → FE481 (the dropped emit can't preserve it).
            if matches!(self.cur(), TokKind::Ident(n) if n == "emit")
                && matches!(
                    self.toks.get(self.i + 1).map(|t| &t.kind),
                    Some(TokKind::Ident(_))
                )
            {
                self.parse_emit_discard()?;
                continue;
            }
            stmts.push(self.parse_stmt()?);
        }
        let end = self.expect(TokKind::RBrace, "`}`")?;
        Ok((stmts, end))
    }

    /// SOL-EVENTS: consume + DISCARD an `emit Name(args);`. The args are parsed (depth-guarded via
    /// `parse_expr` → FE402; a malformed emit → FE401) and checked for discard-safety: a trap-capable
    /// or side-effecting arg → FE481 (a discarded emit can't preserve a revert/side-effect). Produces
    /// no `Stmt` — the event is gone by the time check/emit run.
    fn parse_emit_discard(&mut self) -> Result<(), FrontendDiag> {
        self.bump(); // `emit`
        self.expect_ident("event name")?;
        self.expect(TokKind::LParen, "`(`")?;
        let mut args = Vec::new();
        if !self.at(&TokKind::RParen) {
            loop {
                args.push(self.parse_expr()?);
                if self.at(&TokKind::Comma) {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        self.expect(TokKind::RParen, "`)`")?;
        self.expect(TokKind::Semi, "`;`")?;
        for a in &args {
            if !emit_arg_discard_safe(a) {
                return Err(FrontendDiag::new(
                    codes::FE481_EMIT_ARG_EFFECTFUL_SOL,
                    "an `emit` argument contains a call or trap-capable arithmetic; bind it to a local before the emit (the discarded event can't preserve its argument's revert/side-effect)",
                    a.span(),
                ));
            }
        }
        Ok(())
    }

    /// SOL-AIRDROP (Rung C): parse the ONE rigid airdrop `for` header + body →
    /// `Stmt::AirdropLoop`. The exact shape is
    ///   `for ( uint|uint256 <i> [= 0] ; <i> < <arr>.length ; <inc> ) { <body> }`
    /// with `<inc>` ∈ { `<i>++`, `++<i>`, `<i> += 1`, `<i> = <i> + 1` } (`++` lexes as two
    /// `+`). Every token is pinned; ANY deviation → FE401 (fail-closed — there is no general
    /// loop grammar). The body is parsed by `parse_block` (depth-guarded; `emit`s stripped).
    fn parse_airdrop_for(&mut self) -> Result<Stmt, FrontendDiag> {
        let start = self.bump(); // `for`
        self.expect(
            TokKind::LParen,
            "`(` after `for` (only the airdrop loop shape is supported)",
        )?;
        // init: `uint|uint256 <i> [= 0]`
        let (tyname, _) = self.expect_ident("`uint`/`uint256` loop-counter type")?;
        if tyname != "uint" && tyname != "uint256" {
            return Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                "the airdrop loop counter must be declared `uint`/`uint256`",
            ));
        }
        let (idx, _) = self.expect_ident("the loop-counter name")?;
        if self.at(&TokKind::Assign) {
            self.bump();
            self.expect_num_lit("0", "the loop must initialize the counter to 0")?;
        }
        self.expect(TokKind::Semi, "`;` after the loop init")?;
        // cond: `<i> < <arr>.length`
        let (ci, _) = self.expect_ident("the loop counter in the condition")?;
        if ci != idx {
            return Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                "the loop condition must test the loop counter",
            ));
        }
        self.expect(
            TokKind::Lt,
            "`<` in the loop condition (`<i> < <arr>.length`)",
        )?;
        let (len_array, _) = self.expect_ident("the array in `<arr>.length`")?;
        self.expect(TokKind::Dot, "`.` in `<arr>.length`")?;
        let (lenword, _) = self.expect_ident("`length`")?;
        if lenword != "length" {
            return Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                "the loop bound must be `<arr>.length`",
            ));
        }
        self.expect(TokKind::Semi, "`;` after the loop condition")?;
        // inc: `<i>++` | `++<i>` | `<i> += 1` | `<i> = <i> + 1`  (all ≡ idx + 1)
        self.parse_airdrop_inc(&idx)?;
        self.expect(TokKind::RParen, "`)` to close the `for` header")?;
        let (body, end) = self.parse_block()?;
        Ok(Stmt::AirdropLoop {
            idx,
            len_array,
            body,
            span: start.start..end.end,
        })
    }

    /// Expect a numeric literal equal to `want` (fail-closed FE401 otherwise). Consumes it.
    fn expect_num_lit(&mut self, want: &str, msg: &str) -> Result<(), FrontendDiag> {
        if matches!(self.cur(), TokKind::Num(n) if n == want) {
            self.bump();
            Ok(())
        } else {
            Err(self.err(codes::FE401_UNSUPPORTED_SOL, msg))
        }
    }

    /// Parse the airdrop loop increment, pinned to `+1` on `idx` (all four forms).
    fn parse_airdrop_inc(&mut self, idx: &str) -> Result<(), FrontendDiag> {
        if self.at(&TokKind::Plus) {
            // `++<i>` — two `+` then the counter.
            self.bump();
            self.expect(TokKind::Plus, "`++` (pre-increment)")?;
            let (v, _) = self.expect_ident("the loop counter after `++`")?;
            if v != idx {
                return Err(self.err(
                    codes::FE401_UNSUPPORTED_SOL,
                    "the loop increment must step the loop counter",
                ));
            }
            return Ok(());
        }
        let (v, _) = self.expect_ident("the loop counter in the increment")?;
        if v != idx {
            return Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                "the loop increment must step the loop counter",
            ));
        }
        if self.at(&TokKind::Plus) {
            // `<i>++`
            self.bump();
            self.expect(TokKind::Plus, "`++` (post-increment)")?;
            Ok(())
        } else if self.at(&TokKind::PlusEq) {
            // `<i> += 1`
            self.bump();
            self.expect_num_lit("1", "the airdrop loop must step by `+= 1`")
        } else if self.at(&TokKind::Assign) {
            // `<i> = <i> + 1`
            self.bump();
            let (v2, _) = self.expect_ident("`<i>` in `<i> = <i> + 1`")?;
            if v2 != idx {
                return Err(self.err(
                    codes::FE401_UNSUPPORTED_SOL,
                    "the loop increment must step the loop counter",
                ));
            }
            self.expect(TokKind::Plus, "`+` in `<i> = <i> + 1`")?;
            self.expect_num_lit("1", "the airdrop loop must step by `+ 1`")
        } else {
            Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                "unrecognized loop increment (use `i++` / `++i` / `i += 1` / `i = i + 1`)",
            ))
        }
    }

    fn parse_stmt(&mut self) -> Result<Stmt, FrontendDiag> {
        // SOL1c: inside a modifier body, `_;` is the body-splice placeholder. Recognize it
        // before the generic Ident path (where a bare `_` would otherwise FE401 as a
        // non-lvalue). Requires the EXACT two-token shape `_` `;`.
        if self.in_modifier
            && matches!(self.cur(), TokKind::Ident(n) if n == "_")
            && matches!(
                self.toks.get(self.i + 1).map(|t| &t.kind),
                Some(TokKind::Semi)
            )
        {
            let s = self.bump(); // `_`
            let semi = self.bump(); // `;`
            return Ok(Stmt::Placeholder {
                span: s.start..semi.end,
            });
        }
        // SOL-AIRDROP (Rung C): the rigid airdrop `for` header — the parser's ONLY loop
        // (`for` is a bare Ident, not a keyword). `for (uint <i> = 0; <i> < <arr>.length;
        // <inc>) { <body> }` → a transient `Stmt::AirdropLoop`; ANY deviation is fail-closed
        // FE401 (there is no general `for`/`while` grammar). `recognize_airdrop` then folds
        // it to a `BatchTransfer` or rejects it (FE492).
        if matches!(self.cur(), TokKind::Ident(n) if n == "for") {
            return self.parse_airdrop_for();
        }
        match self.cur() {
            TokKind::Require => self.parse_require(),
            TokKind::Assert => self.parse_assert(),
            TokKind::Revert => self.parse_revert(),
            TokKind::Return => self.parse_return(),
            TokKind::If => self.parse_if(),
            TokKind::Unchecked => {
                let s = self.bump();
                // RETAIN the body — `desugar::unwrap_unchecked` splices it into the parent and
                // lowers it as CHECKED arithmetic (SOL-UNCHECKED). `parse_block` is depth-guarded.
                let (body, end) = self.parse_block()?;
                Ok(Stmt::Unchecked {
                    body,
                    span: s.start..end.end,
                })
            }
            // SOL-LEX: inline `assembly { … }` (the lexer already skipped the whole balanced
            // YUL block into one `Assembly` marker) — a low-level sub-language we do not
            // translate; rejected precisely (FE478) rather than as a generic byte error.
            TokKind::Assembly => Err(self.err(
                codes::FE478_INLINE_ASSEMBLY_SOL,
                "inline `assembly` (YUL) is unsupported (a low-level sub-language that is not translated)",
            )),
            // SOL-EVENTS: `emit Name(...);` is intercepted + DISCARDED in `parse_block_inner` (the
            // sole caller of `parse_stmt`) before we get here, so no `emit` arm is needed.
            // `T name = e;` (local decl) when the current token is a type-name
            // identifier followed by another identifier; otherwise an assignment.
            TokKind::Ident(_) => self.parse_assign_or_local(),
            _ => Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                format!("unsupported statement starting with {:?}", self.cur()),
            )),
        }
    }

    fn parse_require(&mut self) -> Result<Stmt, FrontendDiag> {
        let start = self.bump(); // require
        self.expect(TokKind::LParen, "`(`")?;
        let cond = self.parse_expr()?;
        // optional `, "reason"` — SOL0 DROPS the reason (NC AG-S4): faithful because
        // SOL0 has no external calls / try-catch, so no translated code can observe
        // it. Only a string-literal reason is recognised; any other second-arg form
        // (an identifier, an expression) is a fail-closed reject.
        if self.at(&TokKind::Comma) {
            self.bump();
            if matches!(self.cur(), TokKind::Str(_)) {
                self.bump();
            } else {
                return Err(self.err(
                    codes::FE414_BAD_GUARD,
                    "require's reason argument must be a string literal (it is dropped)",
                ));
            }
        }
        self.expect(TokKind::RParen, "`)`")?;
        let end = self.expect(TokKind::Semi, "`;`")?;
        Ok(Stmt::Require {
            cond,
            span: start.start..end.end,
        })
    }

    fn parse_assert(&mut self) -> Result<Stmt, FrontendDiag> {
        let start = self.bump();
        self.expect(TokKind::LParen, "`(`")?;
        let cond = self.parse_expr()?;
        self.expect(TokKind::RParen, "`)`")?;
        let end = self.expect(TokKind::Semi, "`;`")?;
        Ok(Stmt::Assert {
            cond,
            span: start.start..end.end,
        })
    }

    fn parse_revert(&mut self) -> Result<Stmt, FrontendDiag> {
        let start = self.bump();
        // The three legal forms — `revert;`, `revert(...);`, `revert Custom(...);` —
        // all map to an unconditional abort. Recognise them EXPLICITLY and REQUIRE a
        // terminating `;`; a missing `;` is a fail-closed reject (FE401), never a
        // scan-to-next-`;` that silently swallows the following statement.
        if let TokKind::Ident(_) = self.cur() {
            self.bump(); // CustomError name
        }
        if self.at(&TokKind::LParen) {
            self.skip_balanced_parens()?;
        }
        let end = self.expect(TokKind::Semi, "`;`")?;
        Ok(Stmt::Revert {
            span: start.start..end.end,
        })
    }

    /// Consume a balanced `( … )` group (the current token must be `(`), discarding
    /// its contents. Total: unbalanced parens hit `Eof` → a fail-closed reject.
    fn skip_balanced_parens(&mut self) -> Result<(), FrontendDiag> {
        self.expect(TokKind::LParen, "`(`")?;
        let mut depth = 1i32;
        loop {
            match self.cur() {
                TokKind::LParen => {
                    depth += 1;
                    self.bump();
                }
                TokKind::RParen => {
                    depth -= 1;
                    self.bump();
                    if depth == 0 {
                        return Ok(());
                    }
                }
                TokKind::Eof => {
                    return Err(
                        self.err(codes::FE414_BAD_GUARD, "unterminated revert argument list")
                    );
                }
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// SOL-SYNTAX: consume and DISCARD a custom `error Name(params);` declaration (called from BOTH
    /// the contract-member loop and the file-level loop — one implementation, EX-4). Modern
    /// (Solidity ≥0.8.4) contracts declare custom errors instead of string reverts; the frontend
    /// lowers every `revert CustomError(...)` to an unconditional `trap()` (SOL-DIVERGE), dropping
    /// the name + args, so a custom-error DECLARATION carries NO information the translation uses.
    /// Consumes `error` + the name + the balanced `(params)` (types NOT parsed) + a REQUIRED `;` —
    /// bounded EXACTLY at the decl's own `;` via `skip_balanced_parens` + `expect(Semi)`, so it can
    /// never scan into the next member; a malformed decl is a fail-closed FE401, not a silent
    /// swallow. Every custom error has a `(…)` (possibly empty), so the parens are required.
    fn parse_error_discard(&mut self) -> Result<(), FrontendDiag> {
        self.bump(); // `error`
        self.expect_ident("error name")?;
        self.skip_balanced_parens()?;
        self.expect(TokKind::Semi, "`;` to end the `error` declaration")?;
        Ok(())
    }

    fn parse_return(&mut self) -> Result<Stmt, FrontendDiag> {
        let start = self.bump();
        let value = if self.at(&TokKind::Semi) {
            None
        } else {
            Some(self.parse_expr()?)
        };
        let end = self.expect(TokKind::Semi, "`;`")?;
        Ok(Stmt::Return {
            value,
            span: start.start..end.end,
        })
    }

    /// Depth-guarded: `else if` chains recurse directly through `parse_if`
    /// (bypassing `parse_block`), so the guard must live here too.
    fn parse_if(&mut self) -> Result<Stmt, FrontendDiag> {
        self.enter()?;
        let r = self.parse_if_inner();
        self.leave();
        r
    }

    fn parse_if_inner(&mut self) -> Result<Stmt, FrontendDiag> {
        let start = self.bump();
        self.expect(TokKind::LParen, "`(`")?;
        let cond = self.parse_expr()?;
        self.expect(TokKind::RParen, "`)`")?;
        let (then_body, mut end) = self.parse_block()?;
        let else_body = if self.at(&TokKind::Else) {
            self.bump();
            if self.at(&TokKind::If) {
                // `else if` chains into a nested If statement.
                let nested = self.parse_if()?;
                end = nested_span_end(&nested);
                vec![nested]
            } else {
                let (eb, e) = self.parse_block()?;
                end = e;
                eb
            }
        } else {
            Vec::new()
        };
        Ok(Stmt::If {
            cond,
            then_body,
            else_body,
            span: start.start..end.end,
        })
    }

    /// Disambiguate `T name = e;` (local decl: ident ident) from an assignment to an
    /// lvalue (`name op= e;` or `map[key] op= e;`). A `mapping(…)` local is impossible
    /// (mappings are storage-only), so the `ident ident` lookahead never mis-fires on
    /// one — `mapping` is followed by `(`, not an identifier.
    fn parse_assign_or_local(&mut self) -> Result<Stmt, FrontendDiag> {
        // Look ahead: ident followed by another ident => local decl.
        let next_is_ident = matches!(
            self.toks.get(self.i + 1).map(|t| &t.kind),
            Some(TokKind::Ident(_))
        );
        if next_is_ident {
            let ty = self.parse_type()?;
            let (name, _) = self.expect_ident("local variable name")?;
            self.expect(TokKind::Assign, "`=`")?;
            let value = self.parse_expr()?;
            let end = self.expect(TokKind::Semi, "`;`")?;
            return Ok(Stmt::LocalVar {
                span: ty.span().start..end.end,
                name,
                ty,
                value,
            });
        }
        // Assignment to an lvalue. Parse the lvalue as an expression (so `map[key]`
        // is handled by the postfix index rule, depth-guarded), then require an
        // assign-op and classify the lvalue. Only a bare `Var` or a single-level
        // `Var[key]` is assignable; anything else (member, call, nested index) is a
        // fail-closed reject.
        let lhs = self.parse_expr()?;
        // SOL-CALLS: a bare internal function-call STATEMENT — `name(args);` — a `Var`-callee `Call`
        // in statement position with no assignment. The parser is permissive (any such call becomes a
        // `CallStmt`); `desugar::inline_internal_calls` resolves the name against the flattened function
        // table and either inlines the body or fail-closes (an unknown name → FE401). A NON-`Var` callee
        // (`a.b(…)`) is an external/member call and falls through to the assign-op path below, where it
        // fail-closes (not an assignable lvalue → FE401).
        if matches!(self.cur(), TokKind::Semi)
            && matches!(&lhs, Expr::Call(c, _, _) if matches!(c.as_ref(), Expr::Var(_, _)))
        {
            let (callee_expr, args, cspan) = match lhs {
                Expr::Call(c, args, cspan) => (c, args, cspan),
                _ => unreachable!("guarded by the matches! above"),
            };
            let name = match *callee_expr {
                Expr::Var(n, _) => n,
                _ => unreachable!("guarded by the matches! above"),
            };
            let end = self.expect(TokKind::Semi, "`;`")?;
            return Ok(Stmt::CallStmt {
                callee: name,
                args,
                span: cspan.start..end.end,
            });
        }
        let op = match self.cur() {
            TokKind::Assign => AssignOp::Eq,
            TokKind::PlusEq => AssignOp::Plus,
            TokKind::MinusEq => AssignOp::Minus,
            TokKind::StarEq => AssignOp::Star,
            TokKind::SlashEq => AssignOp::Slash,
            TokKind::PercentEq => AssignOp::Percent,
            other => {
                return Err(self.err(
                    codes::FE401_UNSUPPORTED_SOL,
                    format!("expected an assignment operator, found {other:?}"),
                ));
            }
        };
        self.bump();
        let value = self.parse_expr()?;
        let end = self.expect(TokKind::Semi, "`;`")?;
        match lhs {
            Expr::Var(target, tspan) => Ok(Stmt::Assign {
                span: tspan.start..end.end,
                target,
                op,
                value,
            }),
            Expr::Index(base, key, ispan) => match *base {
                Expr::Var(map, _) => Ok(Stmt::IndexAssign {
                    span: ispan.start..end.end,
                    map,
                    key: *key,
                    op,
                    value,
                }),
                // SOL-ERC20: a two-key write `m[k1][k2] op= e` — the base is itself a
                // single-level `Var[k1]` index. The first index is `k1`, the outer is
                // `k2`. A third level (`m[a][b][c]`) has a non-Var inner base → FE440.
                Expr::Index(inner_base, mid_key, _) => match *inner_base {
                    Expr::Var(map, _) => Ok(Stmt::IndexAssign2 {
                        span: ispan.start..end.end,
                        map,
                        k1: *mid_key,
                        k2: *key,
                        op,
                        value,
                    }),
                    _ => Err(FrontendDiag::new(
                        codes::FE440_NESTED_MAPPING_SOL,
                        "mapping nesting deeper than 2 levels is unsupported (`m[a][b][c]`)",
                        ispan,
                    )),
                },
                _ => Err(FrontendDiag::new(
                    codes::FE401_UNSUPPORTED_SOL,
                    "invalid index-assignment target (only `m[k]` or `m[k1][k2]`)",
                    ispan,
                )),
            },
            // SOL-STRUCT: a struct field write `obj.field op= e`. `obj` must be a bare
            // identifier (a struct-typed state field or local); a deeper target
            // (`a.b.c = e`) has a non-Var base → rejected (one level only in v1).
            Expr::Member(base, field, mspan) => match *base {
                Expr::Var(obj, _) => Ok(Stmt::FieldAssign {
                    span: mspan.start..end.end,
                    obj,
                    field,
                    op,
                    value,
                }),
                _ => Err(FrontendDiag::new(
                    codes::FE401_UNSUPPORTED_SOL,
                    "invalid field-assignment target (only a single-level `obj.field` is assignable)",
                    mspan,
                )),
            },
            other => Err(FrontendDiag::new(
                codes::FE401_UNSUPPORTED_SOL,
                "invalid assignment target (only a variable, `map[key]`, or `obj.field`)",
                other.span(),
            )),
        }
    }

    // ── expressions (precedence climbing) ───────────────────────────────────

    fn parse_expr(&mut self) -> Result<Expr, FrontendDiag> {
        self.enter()?;
        let r = self.parse_or();
        self.leave();
        let e = r?;
        // SOL-LEX: a ternary `cond ? a : b` (lowest precedence, so it surfaces here). Lowering
        // to a guarded `if` is a focused follow-on (SIGIL has no if-expression); reject precisely
        // for now (FE480), not as a generic byte error.
        if self.at(&TokKind::Question) {
            return Err(self.err(
                codes::FE480_TERNARY_SOL,
                "the ternary operator `cond ? a : b` is unsupported (lowering deferred)",
            ));
        }
        Ok(e)
    }

    fn parse_or(&mut self) -> Result<Expr, FrontendDiag> {
        let mut lhs = self.parse_and()?;
        let mut chained = 0u32;
        while self.at(&TokKind::PipePipe) {
            let s = self.bump();
            self.enter()?; // bound the left-nested chain depth (built in this flat loop)
            chained += 1;
            let rhs = self.parse_and()?;
            let span = lhs.span().start..s.end.max(rhs.span().end);
            lhs = Expr::Bin(BinOp::Or, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<Expr, FrontendDiag> {
        let mut lhs = self.parse_bitwise()?;
        let mut chained = 0u32;
        while self.at(&TokKind::AmpAmp) {
            let s = self.bump();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_bitwise()?;
            let span = lhs.span().start..s.end.max(rhs.span().end);
            lhs = Expr::Bin(BinOp::And, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    /// SOL-LEX: bitwise/shift operators (`& | ^ << >>`) are unsupported. SIGIL native has no
    /// bitwise ops; these will be STDLIB-LOWERED later (`u256_and` already exists). Reject
    /// precisely (FE479) wherever one appears as a binary operator, at every expression
    /// position (this level sits in the main ladder, so a sub-expression `f(a & b)` is caught
    /// too). Precedence is irrelevant since we reject.
    fn parse_bitwise(&mut self) -> Result<Expr, FrontendDiag> {
        let lhs = self.parse_equality()?;
        if matches!(
            self.cur(),
            TokKind::Amp | TokKind::Pipe | TokKind::Caret | TokKind::Shl | TokKind::Shr
        ) {
            return Err(self.err(
                codes::FE479_BITWISE_OP_SOL,
                "bitwise/shift operators (`& | ^ ~ << >>`) are unsupported (stdlib-lowering deferred)",
            ));
        }
        Ok(lhs)
    }

    fn parse_equality(&mut self) -> Result<Expr, FrontendDiag> {
        let mut lhs = self.parse_relational()?;
        let mut chained = 0u32;
        loop {
            let op = match self.cur() {
                TokKind::EqEq => BinOp::Eq,
                TokKind::BangEq => BinOp::Ne,
                _ => break,
            };
            self.bump();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_relational()?;
            let span = lhs.span().start..rhs.span().end;
            lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_relational(&mut self) -> Result<Expr, FrontendDiag> {
        let mut lhs = self.parse_additive()?;
        let mut chained = 0u32;
        loop {
            let op = match self.cur() {
                TokKind::Lt => BinOp::Lt,
                TokKind::LtEq => BinOp::Le,
                TokKind::Gt => BinOp::Gt,
                TokKind::GtEq => BinOp::Ge,
                _ => break,
            };
            self.bump();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_additive()?;
            let span = lhs.span().start..rhs.span().end;
            lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_additive(&mut self) -> Result<Expr, FrontendDiag> {
        let mut lhs = self.parse_multiplicative()?;
        let mut chained = 0u32;
        loop {
            let op = match self.cur() {
                TokKind::Plus => BinOp::Add,
                TokKind::Minus => BinOp::Sub,
                _ => break,
            };
            self.bump();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_multiplicative()?;
            let span = lhs.span().start..rhs.span().end;
            lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, FrontendDiag> {
        let mut lhs = self.parse_power()?;
        let mut chained = 0u32;
        loop {
            let op = match self.cur() {
                TokKind::Star => BinOp::Mul,
                TokKind::Slash => BinOp::Div,
                TokKind::Percent => BinOp::Mod,
                _ => break,
            };
            self.bump();
            self.enter()?;
            chained += 1;
            let rhs = self.parse_power()?;
            let span = lhs.span().start..rhs.span().end;
            lhs = Expr::Bin(op, Box::new(lhs), Box::new(rhs), span);
        }
        self.depth -= chained;
        Ok(lhs)
    }

    /// SOL-TOKEN: `base ** exp` — Solidity exponentiation, binding TIGHTER than `* / %` and
    /// RIGHT-associative (`2 ** 3 ** 2` = `2 ** (3 ** 2)`). SIGIL has no `**` operator, so we
    /// CONSTANT-FOLD a literal `Num ** Num` to its range-checked decimal value (faithful to
    /// Solidity 0.8's checked `**`: an overflow past `2^256` → FE430, exactly as solc reverts).
    /// A non-constant operand (`x ** 2`, `10 ** decimals`) is rejected (FE482) — the dominant
    /// real use is the literal `10 ** 18` decimals idiom.
    fn parse_power(&mut self) -> Result<Expr, FrontendDiag> {
        let base = self.parse_unary()?;
        if !self.at(&TokKind::Pow) {
            return Ok(base);
        }
        let pow_span = self.bump(); // `**`
        self.enter()?;
        let exp = self.parse_power()?; // right-associative
        self.leave();
        let both_decimal = matches!((&base, &exp),
            (Expr::Num(b, _), Expr::Num(e, _)) if is_decimal_digits(b) && is_decimal_digits(e));
        match (&base, &exp) {
            (Expr::Num(b, _), Expr::Num(e, _)) if both_decimal => {
                let folded = fold_pow_decimal(b, e).ok_or_else(|| {
                    FrontendDiag::new(
                        codes::FE430_BAD_NUMBER_SOL,
                        "constant `**` result exceeds the u256 range [0, 2^256) (Solidity 0.8 reverts on this overflow)",
                        base.span().start..exp.span().end,
                    )
                })?;
                Ok(Expr::Num(folded, base.span().start..exp.span().end))
            }
            _ => Err(FrontendDiag::new(
                codes::FE482_NON_CONSTANT_POW_SOL,
                "only a CONSTANT decimal `**` (a literal base and exponent, e.g. `10 ** 18`) is supported; precompute a non-constant exponentiation into a literal",
                pow_span,
            )),
        }
    }

    /// Depth-guarded: a `!`/`-` chain self-recurses through `parse_unary` without
    /// re-entering `parse_expr`, so the guard must live here too.
    fn parse_unary(&mut self) -> Result<Expr, FrontendDiag> {
        self.enter()?;
        let r = self.parse_unary_inner();
        self.leave();
        r
    }

    fn parse_unary_inner(&mut self) -> Result<Expr, FrontendDiag> {
        match self.cur() {
            TokKind::Bang => {
                let s = self.bump();
                let e = self.parse_unary()?;
                let span = s.start..e.span().end;
                Ok(Expr::Unary(UnOp::Not, Box::new(e), span))
            }
            TokKind::Minus => {
                let s = self.bump();
                let e = self.parse_unary()?;
                let span = s.start..e.span().end;
                Ok(Expr::Unary(UnOp::Neg, Box::new(e), span))
            }
            // SOL-LEX: unary bitwise-not `~x` — unsupported (stdlib-lowering deferred), FE479.
            TokKind::Tilde => Err(self.err(
                codes::FE479_BITWISE_OP_SOL,
                "the bitwise-not operator `~` is unsupported (stdlib-lowering deferred)",
            )),
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, FrontendDiag> {
        let mut e = self.parse_primary()?;
        let mut chained = 0u32;
        loop {
            match self.cur() {
                TokKind::Dot => {
                    self.bump();
                    self.enter()?; // a `.a.b.c…` chain is left-nested Member nodes
                    chained += 1;
                    let (member, ms) = self.expect_ident("a member name")?;
                    let span = e.span().start..ms.end;
                    // SOL-ACCESS PR4: a struct-map FIELD PATH `M[k].f` rewrites AT PARSE to the
                    // synthesized per-field map read `__fe_sm_M_f[k]` — so `M[k].f[a]` chains
                    // into the EXISTING 2-key Index shape, and a WRITE `M[k].f[a] = v`
                    // classifies through the EXISTING IndexAssign2 arm (no new Stmt variant,
                    // no lvalue-classifier change, zero walker surface). `explode_struct_maps`
                    // (post-validate) synthesizes the matching state maps for genuine
                    // mapping-to-struct vars and PRECISELY rejects any `__fe_sm_` reference it
                    // did not synthesize — so a non-struct-map `x[k].f` is fail-closed, never
                    // silently accepted. Fires ONLY on a SINGLE-level `Var[key].member` base
                    // (`M[k1][k2].f` keeps its Member and rejects downstream) and ONLY when the
                    // member is NOT immediately CALLED — `bal[a].add(x)` is the SafeMath method
                    // idiom and must stay a `Member` for the fold above. Additive-accept: no
                    // currently-accepted program contains `Var[key].member` (a mapping-to-
                    // struct value was FE441 before this rung).
                    if !self.at(&TokKind::LParen)
                        && matches!(&e, Expr::Index(base, _, _) if matches!(base.as_ref(), Expr::Var(_, _)))
                    {
                        let Expr::Index(base, key, _) = e else {
                            unreachable!("guarded by the matches! above")
                        };
                        let Expr::Var(m, vspan) = *base else {
                            unreachable!("guarded by the matches! above")
                        };
                        let synth = struct_map_synth_name(&m, &member);
                        e = Expr::Index(Box::new(Expr::Var(synth, vspan)), key, span);
                        continue;
                    }
                    e = Expr::Member(Box::new(e), member, span);
                }
                TokKind::LParen => {
                    // SOL-SAFEMATH: fold a `recv.<op>(operand[, "msg"])` SafeMath method call into the
                    // checked `recv <binop> operand`. Recognized ONLY under an active `using SafeMath
                    // for uint256` and ONLY for the exact SafeMath ops. The receiver/operand TYPES are
                    // re-validated downstream by `check` (a non-uint256 receiver → FE443), so this
                    // parse-time syntactic fold is sound; running at PARSE (before flatten / cap /
                    // desugar / check) means a SafeMath-wrapped `msg.sender`/owner is never hidden from
                    // the SOL-CAP scans (the SOL-UNCHECKED F2/F3/F4 lesson). Chaining
                    // (`a.add(b).sub(c)`) folds naturally as the loop re-runs on the folded `Bin`.
                    let safemath_op = if self.safemath_active {
                        match &e {
                            Expr::Member(_, m, _) => safemath_binop(m),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    if let Some(op) = safemath_op {
                        self.bump(); // `(`
                        self.enter()?;
                        chained += 1;
                        let operand = self.parse_expr()?;
                        // `.sub`/`.div`/`.mod` take an OPTIONAL string revert-message 2nd arg — dropped,
                        // exactly like `require`'s reason (SIGIL's trap carries no message). `.add`/
                        // `.mul` take one operand only. Any other argument shape → FE490 (fail-closed).
                        if self.at(&TokKind::Comma) {
                            self.bump();
                            if matches!(self.cur(), TokKind::Str(_))
                                && matches!(op, BinOp::Sub | BinOp::Div | BinOp::Mod)
                            {
                                self.bump(); // drop the revert-message string literal
                            } else {
                                return Err(self.err(
                                    codes::FE490_SAFEMATH_SHAPE_SOL,
                                    "a SafeMath `.add`/`.sub`/`.mul`/`.div`/`.mod` call takes ONE operand \
                                     (plus an optional string revert-message for `.sub`/`.div`/`.mod`); \
                                     this argument shape is unsupported",
                                ));
                            }
                        }
                        let rp = self.expect(TokKind::RParen, "`)`")?;
                        // Recover the receiver from the `Member` callee; emit the checked binop.
                        let Expr::Member(recv, _, _) = e else {
                            unreachable!("safemath_op is Some only when `e` is a Member")
                        };
                        let span = recv.span().start..rp.end;
                        e = Expr::Bin(op, recv, Box::new(operand), span);
                        continue;
                    }
                    // SOL-ACCESS: fold `keccak256("<literal>")` — the AccessControl role-id
                    // idiom — into its PRECOMPUTED Keccak-256 hash as a `0x…` u256 literal.
                    // Parse-time (the `**`/SafeMath precedent), so no security scan ever sees
                    // an un-folded form. The lookahead is exactly `( Str )`: ANY other argument
                    // shape (a computed expression, `abi.encodePacked(...)`, two args) falls
                    // through to the generic call path, where a bare string fails expression
                    // parsing and a computed call fails at check — FE401, never a constant of
                    // the wrong bytes (MC-2). A literal the raw-text gate refuses (escape /
                    // non-printable-ASCII, `keccak_foldable`) likewise falls through — never
                    // hashed lossily (MC-3). A user fn NAMED `keccak256` cannot exist:
                    // `check_identifier` reserves the name (fail-closed, mirrors solc's
                    // builtin), so the fold can never shadow a real dispatch.
                    if matches!(&e, Expr::Var(n, _) if n == "keccak256")
                        && let Some(TokKind::Str(text)) = self.toks.get(self.i + 1).map(|t| &t.kind)
                        && matches!(
                            self.toks.get(self.i + 2).map(|t| &t.kind),
                            Some(TokKind::RParen)
                        )
                        && keccak_foldable(text)
                    {
                        let lit = keccak256_hex_literal(text);
                        self.bump(); // `(`
                        self.bump(); // the string literal
                        let rp = self.bump(); // `)`
                        let span = e.span().start..rp.end;
                        e = Expr::Num(lit, span);
                        continue;
                    }
                    let lp = self.bump();
                    self.enter()?; // a `f()()()…` chain is left-nested Call nodes
                    chained += 1;
                    let mut args = Vec::new();
                    while !self.at(&TokKind::RParen) {
                        args.push(self.parse_expr()?);
                        if self.at(&TokKind::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                    let rp = self.expect(TokKind::RParen, "`)`")?;
                    let span = e.span().start..rp.end;
                    let _ = lp;
                    e = Expr::Call(Box::new(e), args, span);
                }
                TokKind::LBracket => {
                    self.bump();
                    self.enter()?; // a `m[a][b]…` chain is left-nested Index nodes
                    chained += 1;
                    let key = self.parse_expr()?;
                    let rb = self.expect(TokKind::RBracket, "`]`")?;
                    let span = e.span().start..rb.end;
                    e = Expr::Index(Box::new(e), Box::new(key), span);
                }
                _ => break,
            }
        }
        self.depth -= chained;
        Ok(e)
    }

    fn parse_primary(&mut self) -> Result<Expr, FrontendDiag> {
        match self.cur().clone() {
            TokKind::Num(t) => {
                let s = self.bump();
                Ok(Expr::Num(t, s))
            }
            TokKind::True => Ok(Expr::Bool(true, self.bump())),
            TokKind::False => Ok(Expr::Bool(false, self.bump())),
            TokKind::Ident(name) => {
                let s = self.bump();
                Ok(Expr::Var(name, s))
            }
            TokKind::LParen => {
                self.bump();
                let e = self.parse_expr()?;
                self.expect(TokKind::RParen, "`)`")?;
                Ok(e)
            }
            other => Err(self.err(
                codes::FE401_UNSUPPORTED_SOL,
                format!("expected an expression, found {other:?}"),
            )),
        }
    }
}

fn nested_span_end(s: &Stmt) -> Range<usize> {
    match s {
        Stmt::If { span, .. } => span.clone(),
        _ => 0..0,
    }
}

/// Count `Stmt::Placeholder` nodes across a statement tree, descending into `if`
/// branches (a `_` nested in a modifier's `if` is legal Solidity). SOL1c requires
/// EXACTLY one per modifier (FE447): zero would drop the function body, two would
/// duplicate it.
fn count_placeholders(stmts: &[Stmt]) -> usize {
    let mut n = 0;
    for s in stmts {
        match s {
            Stmt::Placeholder { .. } => n += 1,
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                n += count_placeholders(then_body);
                n += count_placeholders(else_body);
            }
            _ => {}
        }
    }
    n
}
