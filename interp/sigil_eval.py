"""SIGIL evaluator — independent implementation, Phase 1 vertical slice.

See README.md for the independence rule. This walks the AST from `sigil_parse` directly; there is
no bytecode step and no code generation anywhere, because SIGIL's compiler returns its output as a
string rather than as machine code.

SEMANTIC DECISIONS, stated because they are where an independent implementation is most likely to
disagree — and disagreeing correctly is the point:

* `i64` is a wrapping 64-bit signed integer. Division and remainder truncate toward zero, which is
  what a WASM `i64.div_s` does and what Python's `//` does NOT.
* `str` is a BYTE string, modelled as Python `bytes`. `len`, `byte_at` and `substr` are all byte
  indexed; nothing here is codepoint aware. That matches how the certified source manipulates
  text (it scans bytes and compares them numerically).
* Records are REFERENCE semantic — `stdlib/sigil/arena.sigil` says so explicitly, and the parser's
  arena depends on it. A record value is a shared mutable object, never copied on assignment.
* `Vec` is SUBSTITUTED, not executed. It is the one stdlib type that bottoms out in raw linear
  memory, and the evidence that substituting it is sound is that the Rust oracle and the WASM
  selfhost already use completely different memory representations and emit identical bytes.
  Everything else runs as real SIGIL source.
"""

from __future__ import annotations

from sigil_parse import Node

MASK64 = (1 << 64) - 1
SIGN64 = 1 << 63

# Statement signals. Integers rather than exceptions: `return` out of a deep call chain is the
# hot path in a compiler, and Python exception unwinding is far more expensive than a tuple.
NORMAL, RETURN, BREAK, CONTINUE = 0, 1, 2, 3

# `str` methods that are NOT primitives: each desugars to an ordinary SIGIL function that lives in
# the certified source, so the interpreter must CALL it rather than substitute Python. Substituting
# these would skip real control flow at hundreds of call sites — including in the emitter — and
# make the DDC comparison blind to precisely the binary-vs-source divergence it exists to detect.
STR_METHOD_FNS = {
    "concat": "str_concat",
    "join": "str_join",
    "bytes_eq": "str_bytes_eq",
}


class SigilError(Exception):
    """A trap: the program did something the language forbids (bounds, divide by zero)."""


class _Missing:
    """Poison for a value that was never produced — an uninitialised `let`, or a bare `return`.

    Python `None` was used for both, and `None` is falsy and compares unequal to everything, so a
    missing value degraded into a silently wrong answer instead of an error. This raises the
    moment it is READ, which is where the fault actually is.
    """

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - diagnostics only
        return "<never assigned>"


MISSING = _Missing()


class Rec:
    """A record instance. Reference-semantic: assignment shares this object."""

    __slots__ = ("f", "ty")

    def __init__(self, ty: str, f: dict) -> None:
        self.ty = ty
        self.f = f

    def __repr__(self) -> str:
        return f"{self.ty}{self.f}"


class EnumVal:
    __slots__ = ("payload", "variant")

    def __init__(self, variant: str, payload: list) -> None:
        self.variant = variant
        self.payload = payload

    def __repr__(self) -> str:
        return f"{self.variant}({self.payload})" if self.payload else self.variant


def _char_boundary(b: bytes, i: int) -> bool:
    """Is byte offset `i` a UTF-8 character boundary? Continuation bytes are `10xxxxxx`."""
    return i in (0, len(b)) or (b[i] & 0xC0) != 0x80


def wrap64(v: int) -> int:
    v &= MASK64
    return v - (1 << 64) if v & SIGN64 else v


def div_trunc(a: int, b: int) -> int:
    if b == 0:
        raise SigilError("integer division by zero")
    # WASM's `i64.div_s` TRAPS on this overflow rather than wrapping — the quotient 2^63 has no
    # i64 representation. Wrapping it would be silently more permissive than the compiler.
    if a == SIGN64 * -1 and b == -1:
        raise SigilError("integer division overflow: i64::MIN / -1")
    q = abs(a) // abs(b)
    return wrap64(-q if (a < 0) != (b < 0) else q)


def rem_trunc(a: int, b: int) -> int:
    if b == 0:
        raise SigilError("integer remainder by zero")
    r = abs(a) % abs(b)
    return wrap64(-r if a < 0 else r)


class Interp:
    def __init__(self) -> None:
        self.fns: dict[str, Node] = {}
        self.records: dict[str, Node] = {}
        self.enums: dict[str, Node] = {}
        self.variant_owner: dict[str, str] = {}
        self.methods: dict[str, dict[str, Node]] = {}
        self.consts: dict[str, object] = {}
        self.const_nodes: dict[str, Node] = {}
        self.steps = 0
        # LINEAR MEMORY, so the stdlib's raw-memory layer can actually execute. `str_concat` and
        # friends allocate a buffer, fill it byte by byte with `store8`, and hand it back through
        # `str_from_raw`; without a memory model those functions are unrunnable and have to be
        # faked. Address 0 is never handed out so a null pointer stays distinguishable.
        self.mem = bytearray(1 << 16)
        self.bump = 8

    # ── loading ──────────────────────────────────────────────────────────────────────────────
    @staticmethod
    def _no_dup(table: dict, name: str, what: str) -> None:
        """`S` flattens 17 modules into ONE namespace, so a duplicate silently shadows — last
        write wins — and the interpreter runs a different declaration than the compiler resolves.
        Zero collisions today across all five kinds; that was an unchecked assumption."""
        if name in table:
            raise SigilError(f"duplicate {what} name across flattened modules: {name}")

    def load(self, program: Node) -> None:
        for item in program.items:
            k = item.kind
            if k == "fn":
                # `S` flattens 17 modules into one namespace, so a duplicate name would silently
                # shadow — last write wins — and the interpreter would run a different function
                # than the compiler resolves. There are zero collisions today; that is an
                # assumption this loop depended on and never checked.
                self._no_dup(self.fns, item.a, "function")
                self.fns[item.a] = item
            elif k == "record":
                self._no_dup(self.records, item.a, "record")
                self.records[item.a] = item
            elif k == "enum":
                self._no_dup(self.enums, item.a, "enum")
                self.enums[item.a] = item
                for v in item.b:
                    # A duplicate VARIANT name also mis-routes method dispatch, which looks the
                    # owning enum up by variant name.
                    self._no_dup(self.variant_owner, v.a, "enum variant")
                    self.variant_owner[v.a] = item.a
            elif k == "impl":
                # `setdefault` is required — `Vec`'s methods span several `impl` blocks — but the
                # per-method insert had no duplicate check.
                table = self.methods.setdefault(item.a, {})
                for m in item.b:
                    self._no_dup(table, m.a, f"method on {item.a}")
                    table[m.a] = m
            elif k == "const":
                self._no_dup(self.const_nodes, item.a, "constant")
                self.const_nodes[item.a] = item
            elif k not in ("module", "use"):
                # No silent `else`: an item kind the parser learns but the loader does not would
                # otherwise be dropped without a word — the repo's own "walker forgot an arm" class.
                raise SigilError(f"loader does not handle declaration kind {k!r}")

    def const(self, name: str):
        if name in self.consts:
            return self.consts[name]
        node = self.const_nodes[name]
        value = self.eval(node.c, {})
        self.consts[name] = value
        return value

    # ── calling ──────────────────────────────────────────────────────────────────────────────
    def call_fn(self, fn: Node, args: list):
        env: dict = {}
        params = fn.b
        if len(params) != len(args):
            raise SigilError(f"{fn.a}: expected {len(params)} args, got {len(args)}")
        for p, a in zip(params, args, strict=True):
            env[p.a] = a
        sig, val = self.exec_block(fn.d, env)
        if sig == RETURN and val is MISSING and fn.c is not None:
            raise SigilError(f"{fn.a}: bare `return` in a function declaring a return type")
        if sig != RETURN:
            # Falling off the end yielded Python `None`, which is falsy and compares unequal to
            # everything — so a missing return degraded into a silently wrong value rather than an
            # error. Functions returning unit legitimately fall off the end, so only a declared
            # return type makes this a fault.
            if fn.c is not None:
                raise SigilError(f"{fn.a}: control reached the end without returning a value")
            return None
        return val

    def call_named(self, name: str, args: list):
        fn = self.fns.get(name)
        if fn is None:
            raise SigilError(f"undefined function {name}")
        return self.call_fn(fn, args)

    # ── statements ───────────────────────────────────────────────────────────────────────────
    def exec_block(self, block: Node, env: dict) -> tuple[int, object]:
        """Run a block in its own SCOPE.

        The oracle is block-scoped — it clones the type environment for every `if` branch, match
        arm and loop body, and explicitly restores shadowed bindings on exit. A flat per-call
        environment silently disagrees: an inner `let y` would overwrite an outer `y` for the rest
        of the function, and a loop body's temporaries would outlive the loop. The certified source
        happens to contain two inner shadows whose outer binding is never read afterwards, so it
        agreed by luck; a third, or a reordering of those two, would have changed the emitted bytes
        with nothing to notice.

        Implementation note: the declared names are computed once per block and cached on the node,
        and blocks that declare nothing skip the bookkeeping entirely — this runs hundreds of
        millions of times.
        """
        names = block.a
        if names is None:
            names = []
            for st in block.items:
                if st.kind == "let":
                    names.append(st.a)
                elif st.kind == "let_tuple":
                    names.extend(st.a)
            block.a = names

        if not names:
            for st in block.items:
                sig, val = self.exec_stmt(st, env)
                if sig:
                    return sig, val
            return NORMAL, None

        shadowed = [(n, env[n]) for n in names if n in env]
        try:
            for st in block.items:
                sig, val = self.exec_stmt(st, env)
                if sig:
                    return sig, val
            return NORMAL, None
        finally:
            for n in names:
                env.pop(n, None)
            for n, v in shadowed:
                env[n] = v

    def exec_stmt(self, st: Node, env: dict) -> tuple[int, object]:
        self.steps += 1
        k = st.kind
        if k == "let":
            # An uninitialised `let` binds a POISON, not `None`. `None` is falsy and compares
            # unequal to everything, so reading it degraded into a silently wrong value — the
            # very failure the missing-return rule was added to remove.
            env[st.a] = self.eval(st.c, env) if st.c is not None else MISSING
            return NORMAL, None
        if k == "assign":
            self.assign(st.a, self.eval(st.b, env), env)
            return NORMAL, None
        if k == "expr_stmt":
            self.eval(st.a, env)
            return NORMAL, None
        if k == "return":
            return RETURN, (self.eval(st.a, env) if st.a is not None else MISSING)
        if k == "if":
            if self.eval(st.a, env):
                return self.exec_block(st.b, env)
            if st.c is not None:
                return self.exec_block(st.c, env) if st.c.kind == "block" else self.exec_stmt(st.c, env)
            return NORMAL, None
        if k == "while":
            cond = st.a
            body = st.b
            while self.eval(cond, env):
                sig, val = self.exec_block(body, env)
                if sig == RETURN:
                    return sig, val
                if sig == BREAK:
                    break
            return NORMAL, None
        if k == "break":
            return BREAK, None
        if k == "continue":
            return CONTINUE, None
        if k == "block":
            return self.exec_block(st, env)
        if k == "match":
            return self.exec_match(st, env)
        if k == "let_tuple":
            value = self.eval(st.c, env)
            for name, item in zip(st.a, value, strict=True):
                env[name] = item
            return NORMAL, None
        if k == "for_range":
            name, body = st.a, st.items[0]
            start = self.eval(st.b, env)
            end = self.eval(st.c, env)
            if st.d:
                end += 1
            # SCOPE the loop variable. Writing it into the enclosing environment clobbered an
            # outer binding of the same name and left the last value visible after the loop — and
            # an empty range never assigned at all, so the name kept a stale value.
            had = name in env
            prev = env.get(name)
            try:
                for i in range(start, end):
                    env[name] = i
                    sig, val = self.exec_block(body, env)
                    if sig == RETURN:
                        return sig, val
                    if sig == BREAK:
                        break
                return NORMAL, None
            finally:
                env.pop(name, None)
                if had:
                    env[name] = prev
        raise SigilError(f"unsupported statement {k}")

    def exec_match(self, st: Node, env: dict) -> tuple[int, object]:
        """Run a match, SCOPING each arm's pattern binders.

        `pattern_matches` writes binders straight into `env`, and nothing removed them — the same
        leak `exec_block` was fixed for, missed on the pattern path because `exec_block` only
        collects `let` names. Two consequences, both live: a binder clobbered an outer binding of
        the same name for the rest of the function, and a binder from an arm whose GUARD then
        failed survived into later arms and past the match entirely.
        """
        subject = self.eval(st.a, env)
        for arm in st.items:
            bound: dict = {}
            if not self.pattern_matches(arm.a, subject, env, bound):
                continue
            shadowed = [(n, env[n]) for n in bound if n in env]
            env.update(bound)
            try:
                if arm.b is not None and not self.eval(arm.b, env):
                    continue  # guard failed: `finally` unbinds before the next arm sees it
                body = arm.c
                if body.kind == "block":
                    return self.exec_block(body, env)
                self.eval(body, env)
                return NORMAL, None
            finally:
                for n in bound:
                    env.pop(n, None)
                for n, v in shadowed:
                    env[n] = v
        raise SigilError("no match arm applied")

    def pattern_matches(self, pat: Node, subject, env: dict, bound: dict) -> bool:
        """Match `pat`, collecting binders into `bound` rather than mutating `env` directly.

        The caller scopes them; writing into `env` here is what leaked binders past the match.
        """
        k = pat.kind
        if k == "pat_wild":
            return True
        if k == "pat_bool":
            return subject is pat.a
        if k == "pat_int":
            return subject == wrap64(int(pat.a, 0))  # `int(_, 0)` handles 0x / 0b / underscores
        if k == "pat_str":
            # Bytes equality — the compiler's own semantics since PR #699 (match arms funnel
            # into the same byte compare as `==`). Before that PR this line was a LATENT
            # divergence: the compiler compared data pointers here while this compared bytes,
            # unobservable in the DDC only because the certified source has no str-literal
            # match arms. The compiler moved to this semantics, not the other way around.
            return subject == pat.a.encode()
        if k == "pat_path":
            name = pat.a[-1]
            if isinstance(subject, EnumVal):
                if subject.variant != name:
                    return False
                if len(pat.b) != len(subject.payload):
                    raise SigilError(
                        f"pattern {name} binds {len(pat.b)} values but the variant carries "
                        f"{len(subject.payload)}"
                    )
                for binder, value in zip(pat.b, subject.payload, strict=True):
                    bound[binder] = value
                return True
            # A name that resolves to a CONSTANT is a value to compare against, not a binder.
            # Treating it as a binder made the first arm match unconditionally AND rebound the
            # constant to the subject for the rest of the frame.
            if name in self.const_nodes and name not in env:
                return subject == self.const(name)
            if name in self.variant_owner:
                return False  # a variant pattern against a non-enum subject cannot match
            bound[name] = subject
            return True
        raise SigilError(f"unsupported pattern {k}")

    def assign(self, target: Node, value, env: dict) -> None:
        k = target.kind
        if k == "name":
            name = target.a[0]
            # Assigning to an unbound name must be an ERROR, not a declaration. Creating it
            # silently would let a typo'd target look like a working assignment.
            if name not in env:
                raise SigilError(f"assignment to undeclared name {name}")
            env[name] = value
            return
        if k == "field":
            obj = self.eval(target.a, env)
            if not isinstance(obj, Rec):
                raise SigilError("field assignment on a non-record")
            obj.f[target.b] = value
            return
        if k == "index":
            seq = self.eval(target.a, env)
            index = self.eval(target.b, env)
            self._check_index(seq, index)
            seq[index] = value
            return
        raise SigilError(f"unsupported assignment target {k}")

    # ── expressions ──────────────────────────────────────────────────────────────────────────
    @staticmethod
    def _check_index(seq, index) -> None:
        """Bounds-check `seq[index]`.

        Raw Python indexing wrapped NEGATIVES to the end of the sequence — `v[-1]` read and wrote
        the last element where the oracle traps — and an out-of-range read escaped as a Python
        `IndexError`, which the DDC and differential harnesses do not catch, so it surfaced as a
        bare traceback instead of the intended diagnostic.
        """
        if not isinstance(index, int) or isinstance(index, bool):
            raise SigilError(f"index must be an integer, got {type(index).__name__}")
        if index < 0 or index >= len(seq):
            raise SigilError(f"index out of bounds: {index} of {len(seq)}")

    def _indexed(self, seq, index):
        self._check_index(seq, index)
        return seq[index]

    def eval(self, e: Node, env: dict):
        self.steps += 1
        k = e.kind
        if k == "name":
            name = e.a[0]
            if name in env:
                value = env[name]
                if value is MISSING:
                    raise SigilError(f"`{name}` is read before it is assigned")
                return value
            if name in self.const_nodes:
                return self.const(name)
            if name in self.variant_owner:
                return EnumVal(name, [])
            raise SigilError(f"undefined name {name}")
        if k == "int":
            return wrap64(int(e.a, 0))
        if k == "str":
            return e.a.encode()
        if k == "bool":
            return e.a
        if k == "binary":
            return self.binary(e, env)
        if k == "paren":
            return self.eval(e.a, env)
        if k == "call":
            return self.eval_call(e, env)
        if k == "method":
            return self.eval_method(e, env)
        if k == "field":
            obj = self.eval(e.a, env)
            if isinstance(obj, Rec):
                return obj.f[e.b]
            raise SigilError(f"field {e.b} on a non-record")
        if k == "index":
            return self._indexed(self.eval(e.a, env), self.eval(e.b, env))
        if k == "unary":
            v = self.eval(e.b, env)
            return (not v) if e.a == "!" else wrap64(-v)
        if k == "record_lit":
            return Rec(e.a[-1], {f.a: self.eval(f.b, env) for f in e.items})
        if k == "path":
            return self.eval_path(e, env)
        if k == "tuple":
            return tuple(self.eval(x, env) for x in e.items)
        raise SigilError(f"unsupported expression {k}")

    def binary(self, e: Node, env: dict):
        op = e.a
        # Short-circuit before evaluating the right side.
        if op == "&&":
            return bool(self.eval(e.b, env)) and bool(self.eval(e.c, env))
        if op == "||":
            return bool(self.eval(e.b, env)) or bool(self.eval(e.c, env))
        a = self.eval(e.b, env)
        b = self.eval(e.c, env)
        if op == "+":
            return wrap64(a + b)
        if op == "-":
            return wrap64(a - b)
        if op == "*":
            return wrap64(a * b)
        if op == "<":
            return a < b
        if op == ">":
            return a > b
        if op == "<=":
            return a <= b
        if op == ">=":
            return a >= b
        if op in ("==", "!="):
            # Python `==` on these is IDENTITY, so `Some(1) == Some(1)` is False and a record
            # compares unequal to a structurally identical one. Rather than guess which semantics
            # SIGIL intends and silently answer, refuse. Zero such comparisons in the certified
            # source (it uses `.bytes_eq()` throughout).
            if isinstance(a, (EnumVal, Rec)) or isinstance(b, (EnumVal, Rec)):
                raise SigilError(
                    f"`{op}` on a record or enum is unimplemented — Python identity would silently "
                    f"disagree with SIGIL's semantics"
                )
            # `str` values are Python `bytes` here, and the compiler's `str ==` compares BYTES
            # (air.rs `emit_str_bytes_eq`, PR #699: length first, then a byte scan), so Python's
            # content equality on `bytes` IS the compiler's semantics — fall through. Before that
            # PR the compiler compared data pointers and this arm refused rather than disagree in
            # both directions. The certified source still uses `.bytes_eq()` throughout (a shadow
            # fence pins it to zero `str ==`), so neither behavior is observable in the DDC.
            return a == b if op == "==" else a != b
        if op == "/":
            return div_trunc(a, b)
        if op == "%":
            return rem_trunc(a, b)
        if op == "&":
            return wrap64(a & b)
        if op == "|":
            return wrap64(a | b)
        if op == "^":
            return wrap64(a ^ b)
        if op == ">>":
            return wrap64(a >> (b & 63))
        if op == "<<":
            return wrap64(a << (b & 63))
        raise SigilError(f"unsupported operator {op}")

    def eval_path(self, e: Node, env: dict):
        path = e.a
        last = path[-1]
        if last in self.variant_owner:
            return EnumVal(last, [])
        raise SigilError(f"unsupported path {'::'.join(path)}")

    def eval_call(self, e: Node, env: dict):
        callee = e.a
        args = [self.eval(x, env) for x in e.items]
        if callee.kind == "name":
            name = callee.a[0]
            # A LOCAL of the same name was invisible here: the global was called and the binding
            # ignored. There are no first-class function values in the certified subset, so a
            # bound name in call position is a fault, not a dispatch decision.
            if name in env:
                raise SigilError(
                    f"`{name}` is a local binding, not a function — calling it would silently "
                    f"invoke the top-level `{name}` instead"
                )
            if name in self.fns:
                return self.call_fn(self.fns[name], args)
            if name in self.variant_owner:
                return EnumVal(name, args)
            return self.intrinsic(name, args)
        if callee.kind == "path":
            head, last = callee.a[0], callee.a[-1]
            # ONLY `Vec` is substituted — it is the single stdlib type that bottoms out in raw
            # linear memory. `Arena` is ordinary SIGIL (`record Arena<T> { store: Vec<T> }`) and
            # must run as such, or its `allocate`/`get` never execute and the parser's whole
            # node-storage layer goes untested.
            if head == "Vec":
                if last == "new":
                    return []
                # `Vec` has exactly ONE representation here: a Python list. Any other associated
                # function falls through to the real `vec.sigil` body, which returns a RECORD over
                # raw memory — so the program would then hold two incompatible Vec values and the
                # mismatch would surface far from its cause (or not at all). Zero call sites in
                # the certified source; refuse rather than build the incoherent state.
                raise SigilError(
                    f"Vec::{last} is not substituted, and letting it run would give Vec two "
                    f"incompatible representations (a Python list and a SIGIL record). Substitute "
                    f"it explicitly if the certified source starts using it."
                )
            if last in self.variant_owner:
                return EnumVal(last, args)
            table = self.methods.get(head)
            if table and last in table:
                return self.call_fn(table[last], args)
            raise SigilError(f"undefined path call {'::'.join(callee.a)}")
        raise SigilError(f"unsupported callee {callee.kind}")

    def eval_method(self, e: Node, env: dict):
        recv = self.eval(e.a, env)
        name = e.b
        args = [self.eval(x, env) for x in e.items]
        return self.method(recv, name, args)

    # ── substituted stdlib (see the module docstring) ────────────────────────────────────────
    def method(self, recv, name: str, args: list):
        if isinstance(recv, list):  # Vec
            if name == "push":
                recv.append(args[0])
                return len(recv)
            if name == "get":
                i = args[0]
                if i < 0 or i >= len(recv):
                    raise SigilError(f"Vec::get out of bounds: {i} of {len(recv)}")
                return recv[i]
            if name == "set":
                i = args[0]
                if i < 0 or i >= len(recv):
                    raise SigilError(f"Vec::set out of bounds: {i} of {len(recv)}")
                recv[i] = args[1]
                return i  # `vec.sigil` echoes the INDEX back, deliberately — not 0
            if name == "len":
                return len(recv)
        elif isinstance(recv, bytes):  # str
            # TRUE INTRINSICS. `len`/`byte_at`/`substr` are compiler primitives, not SIGIL: the
            # stdlib's own `str_concat` calls `a.len()` and `a.byte_at(i)`, so treating them as
            # library functions would be an infinite regress.
            if name == "len":
                return len(recv)
            if name == "byte_at":
                i = args[0]
                if i < 0 or i >= len(recv):
                    raise SigilError(f"str::byte_at out of bounds: {i} of {len(recv)}")
                return recv[i]
            if name == "substr":
                start, end = args[0], args[1]
                if start < 0 or end > len(recv) or start > end:
                    raise SigilError(f"str::substr out of range: {start}..{end} of {len(recv)}")
                # CODEPOINT-BOUNDARY TRAP. The oracle traps iff either index lands inside a
                # multi-byte character (`strings.sigil` states the contract; `air.rs` emits it).
                # Omitting it made this interpreter strictly MORE PERMISSIVE than the compiler at
                # 131 call sites — it could complete where the seed traps, which is the
                # "agrees for the wrong reason" shape a DDC comparison must not have.
                if not _char_boundary(recv, start) or not _char_boundary(recv, end):
                    raise SigilError(
                        f"str::substr not on a codepoint boundary: {start}..{end} of {len(recv)}"
                    )
                return recv[start:end]
            # NOT intrinsics — these desugar to ordinary SIGIL in the certified source
            # (`string::str_concat`, `string::str_join`, `strings::str_bytes_eq`). Substituting
            # them would silently skip ~120 lines of real control flow at hundreds of call sites,
            # including in the emitter, and would make the DDC comparison blind to exactly the
            # binary-vs-source divergence it exists to detect. Dispatch to the SIGIL bodies.
            if name in STR_METHOD_FNS:
                return self.call_named(STR_METHOD_FNS[name], [recv, *args])
        elif isinstance(recv, int) and not isinstance(recv, bool):
            # `.itoa()` desugars to `string::str_itoa` — again real SIGIL, notably running its
            # digit math in negative space so that i64::MIN survives.
            if name == "itoa":
                return self.call_named("str_itoa", [recv])
        elif isinstance(recv, Rec):
            table = self.methods.get(recv.ty)
            if table and name in table:
                return self.call_fn(table[name], [recv, *args])
        elif isinstance(recv, EnumVal):
            table = self.methods.get(self.variant_owner.get(recv.variant, ""))
            if table and name in table:
                return self.call_fn(table[name], [recv, *args])
        raise SigilError(f"unsupported method {type(recv).__name__}.{name}")

    def intrinsic(self, name: str, args: list):
        """The compiler-provided primitives the stdlib bottoms out in.

        These are genuine intrinsics — the compiler resolves them itself and there is no SIGIL
        body to execute, which is why implementing them here is not a substitution. `str_concat`
        calling `a.len()` and `a.byte_at(i)` is the proof: if those were library functions the
        definition would be circular.
        """
        if name == "alloc":
            n = args[0]
            if n < 0:
                raise SigilError(f"alloc of a negative size: {n}")
            addr = self.bump
            self.bump += n
            if self.bump > len(self.mem):
                grow = max(self.bump - len(self.mem), len(self.mem))
                self.mem.extend(bytes(grow))
            return addr
        # Bound against the ALLOCATED region (`self.bump`), not the arena's capacity. Checking
        # `len(self.mem)` let a stray write land in memory a later `alloc` will hand out — so
        # "freshly allocated memory is zero" was not actually guaranteed — and let reads of
        # never-allocated addresses return 0 instead of trapping. Address 0 stays unhanded-out and
        # is now genuinely unwritable, which the comment above already claimed.
        if name == "store8":
            addr = args[0]
            if addr < 8 or addr >= self.bump:
                raise SigilError(f"store8 outside the allocated region: {addr} (bump {self.bump})")
            self.mem[addr] = args[1] & 0xFF
            return None
        if name == "load8":
            addr = args[0]
            if addr < 8 or addr >= self.bump:
                raise SigilError(f"load8 outside the allocated region: {addr} (bump {self.bump})")
            return self.mem[addr]
        if name == "str_from_raw":
            ptr, n = args[0], args[1]
            if n < 0 or ptr < 8 or ptr + n > self.bump:
                raise SigilError(
                    f"str_from_raw outside the allocated region: {ptr}..{ptr + n} "
                    f"(bump {self.bump})"
                )
            return bytes(self.mem[ptr : ptr + n])
        raise SigilError(f"undefined function or intrinsic {name}")
