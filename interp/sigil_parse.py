"""SIGIL parser — independent implementation, PARSE-ONLY for now.

Written from the observable syntax of the certified sources (see sigil_lex.py's header for the
independence rule). It is deliberately LOUD: any construct it does not recognize raises
`ParseError` naming the file, line and token. That is the point — pointed at the certified source,
its failures ARE the subset inventory, and its silence is the proof the inventory is complete.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, ClassVar

from sigil_lex import Token, lex


class ParseError(Exception):
    def __init__(self, msg: str, tok: Token, path: str) -> None:
        super().__init__(f"{path}:{tok.line}:{tok.col}: {msg} (at {tok.kind} {tok.text!r})")
        self.tok = tok


# ── AST ───────────────────────────────────────────────────────────────────────────────────────
# Deliberately plain containers: this stage only needs shape, not semantics.


@dataclass(slots=True)
class Node:
    kind: str
    line: int = 0
    a: Any = None
    b: Any = None
    c: Any = None
    d: Any = None
    items: list = field(default_factory=list)


class Parser:
    def __init__(self, src: str, path: str = "<input>") -> None:
        self.path = path
        self.toks = lex(src, path)
        self.i = 0
        self.forms: set[str] = set()

    # ── token helpers ────────────────────────────────────────────────────────────────────────
    def peek(self, off: int = 0) -> Token:
        j = min(self.i + off, len(self.toks) - 1)
        return self.toks[j]

    def at(self, text: str, off: int = 0) -> bool:
        t = self.peek(off)
        return t.text == text and t.kind in ("op", "kw")

    def at_kind(self, kind: str, off: int = 0) -> bool:
        return self.peek(off).kind == kind

    def bump(self) -> Token:
        t = self.toks[self.i]
        if t.kind != "eof":
            self.i += 1
        return t

    def expect(self, text: str) -> Token:
        if not self.at(text):
            raise ParseError(f"expected {text!r}", self.peek(), self.path)
        return self.bump()

    def expect_ident(self) -> str:
        t = self.peek()
        # Contextual keywords appear as plain names in the certified sources (`state`, `entry`,
        # `type`, `on`, `handler`, …). Accept any keyword in a name position rather than build a
        # second keyword list that could drift from the lexer's.
        if t.kind not in ("ident", "kw"):
            raise ParseError("expected an identifier", t, self.path)
        return self.bump().text

    def note(self, form: str) -> None:
        self.forms.add(form)

    # ── entry ────────────────────────────────────────────────────────────────────────────────
    def parse_program(self) -> Node:
        items: list[Node] = []
        while not self.at_kind("eof"):
            items.append(self.parse_item())
        return Node("program", items=items)

    def parse_item(self) -> Node:
        while self.at("#"):  # attributes: #[ring(outer)], #[cfg(...)]
            self.note("attribute")
            self.bump()
            self.expect("[")
            depth = 1
            while depth:
                if self.at("["):
                    depth += 1
                elif self.at("]"):
                    depth -= 1
                elif self.at_kind("eof"):
                    raise ParseError("unterminated attribute", self.peek(), self.path)
                self.bump()

        if self.at("module"):
            self.note("module-decl")
            self.bump()
            name = self.expect_ident()
            self.expect(";")
            return Node("module", a=name)
        if self.at("use"):
            self.note("use-decl")
            self.bump()
            parts = [self.expect_ident()]
            while self.at("::"):
                self.bump()
                parts.append(self.expect_ident())
            self.expect(";")
            return Node("use", a=parts)

        is_pub = False
        if self.at("pub"):
            is_pub = True
            self.bump()

        if self.at("fn"):
            return self.parse_fn(is_pub)
        if self.at("const"):
            return self.parse_const()
        if self.at("record"):
            return self.parse_record()
        if self.at("enum"):
            return self.parse_enum()
        if self.at("impl"):
            return self.parse_impl()
        raise ParseError("unknown item", self.peek(), self.path)

    # ── declarations ─────────────────────────────────────────────────────────────────────────
    def parse_type_params(self) -> list[str]:
        if not self.at("<"):
            return []
        self.note("generic-params")
        self.bump()
        names = [self.expect_ident()]
        while self.at(","):
            self.bump()
            names.append(self.expect_ident())
        self.expect(">")
        return names

    def parse_type(self) -> Node:
        if self.at("&"):
            self.note("type-ref")
            self.bump()
        if self.peek().kind == "ident" and self.peek().text == "Fn" and self.at("(", 1):
            # `Fn(i64) -> i64` — a function TYPE in parameter position (the stdlib's iterator
            # adapters take one). Only the shape is needed here; the evaluator resolves callees.
            self.note("type-fn")
            self.bump()
            self.expect("(")
            args: list[Node] = []
            while not self.at(")"):
                args.append(self.parse_type())
                if self.at(","):
                    self.bump()
            self.expect(")")
            ret = None
            if self.at("->"):
                self.bump()
                ret = self.parse_type()
            self.parse_effect_row()
            return Node("ty_fn", a=args, b=ret)
        if self.at("["):
            self.bump()
            inner = self.parse_type()
            if self.at(";"):  # `[T; N]` — fixed-size array
                self.note("type-array")
                self.bump()
                size = self.bump().text
                self.expect("]")
                return Node("ty_array", a=inner, b=size)
            self.note("type-slice")  # `[T]` — slice
            self.expect("]")
            return Node("ty_slice", a=inner)
        if self.at("("):
            self.note("type-tuple")
            self.bump()
            elems = []
            while not self.at(")"):
                elems.append(self.parse_type())
                if self.at(","):
                    self.bump()
            self.expect(")")
            return Node("ty_tuple", items=elems)
        name = self.expect_ident()
        args: list[Node] = []
        if self.at("<"):
            self.note("generic-type-args")
            self.bump()
            args.append(self.parse_type())
            while self.at(","):
                self.bump()
                args.append(self.parse_type())
            self.expect(">")
        ty = Node("ty", a=name, items=args)
        while self.at("@"):  # taint / borrow annotations: @Mut, @ReadOnly, @Secret, @Public
            self.note("type-annotation")
            self.bump()
            self.expect_ident()
        return ty

    def parse_effect_row(self) -> list[str]:
        """`! { Alloc }` / `! {}` / `! { e }` — the effect row on a signature."""
        if not self.at("!"):
            return []
        self.note("effect-row")
        self.bump()
        self.expect("{")
        names: list[str] = []
        while not self.at("}"):
            names.append(self.expect_ident())
            if self.at(","):
                self.bump()
        self.expect("}")
        return names

    def parse_params(self) -> list[Node]:
        self.expect("(")
        params: list[Node] = []
        while not self.at(")"):
            if self.at("mut"):
                self.note("param-mut")
                self.bump()
            name = self.expect_ident()
            self.expect(":")
            ty = self.parse_type()
            params.append(Node("param", a=name, b=ty))
            if self.at(","):
                self.bump()
        self.expect(")")
        return params

    def parse_fn(self, is_pub: bool) -> Node:
        line = self.peek().line
        self.expect("fn")
        name = self.expect_ident()
        tparams = self.parse_type_params()
        params = self.parse_params()
        ret = None
        if self.at("->"):
            self.bump()
            ret = self.parse_type()
        effects = self.parse_effect_row()
        body = self.parse_block()
        self.note("fn-decl")
        return Node("fn", line=line, a=name, b=params, c=ret, d=body, items=[tparams, effects, is_pub])

    def parse_const(self) -> Node:
        line = self.peek().line
        self.expect("const")
        name = self.expect_ident()
        self.expect(":")
        ty = self.parse_type()
        self.expect("=")
        value = self.parse_expr()
        self.expect(";")
        self.note("const-decl")
        return Node("const", line=line, a=name, b=ty, c=value)

    def parse_record(self) -> Node:
        line = self.peek().line
        self.expect("record")
        name = self.expect_ident()
        tparams = self.parse_type_params()
        self.expect("{")
        fields: list[Node] = []
        while not self.at("}"):
            fname = self.expect_ident()
            self.expect(":")
            fty = self.parse_type()
            fields.append(Node("field", a=fname, b=fty))
            if self.at(","):
                self.bump()
        self.expect("}")
        self.note("record-decl")
        return Node("record", line=line, a=name, b=fields, items=[tparams])

    def parse_enum(self) -> Node:
        line = self.peek().line
        self.expect("enum")
        name = self.expect_ident()
        tparams = self.parse_type_params()
        self.expect("{")
        variants: list[Node] = []
        while not self.at("}"):
            vname = self.expect_ident()
            payload: list[Node] = []
            if self.at("("):
                self.note("enum-payload")
                self.bump()
                while not self.at(")"):
                    payload.append(self.parse_type())
                    if self.at(","):
                        self.bump()
                self.expect(")")
            variants.append(Node("variant", a=vname, b=payload))
            if self.at(","):
                self.bump()
        self.expect("}")
        self.note("enum-decl")
        return Node("enum", line=line, a=name, b=variants, items=[tparams])

    def parse_impl(self) -> Node:
        line = self.peek().line
        self.expect("impl")
        name = self.expect_ident()
        tparams = self.parse_type_params()
        self.expect("{")
        methods: list[Node] = []
        while not self.at("}"):
            is_pub = False
            if self.at("pub"):
                is_pub = True
                self.bump()
            methods.append(self.parse_fn(is_pub))
        self.expect("}")
        self.note("impl-decl")
        return Node("impl", line=line, a=name, b=methods, items=[tparams])

    # ── statements ───────────────────────────────────────────────────────────────────────────
    def parse_block(self) -> Node:
        self.expect("{")
        stmts: list[Node] = []
        while not self.at("}"):
            stmts.append(self.parse_stmt())
        self.expect("}")
        return Node("block", items=stmts)

    def parse_stmt(self) -> Node:
        line = self.peek().line
        if self.at("let"):
            self.bump()
            is_mut = False
            if self.at("mut"):
                is_mut = True
                self.bump()
            if self.at("("):
                self.note("let-tuple")
                self.bump()
                names = [self.expect_ident()]
                while self.at(","):
                    self.bump()
                    names.append(self.expect_ident())
                self.expect(")")
                ty = None
                if self.at(":"):
                    self.bump()
                    ty = self.parse_type()
                self.expect("=")
                init = self.parse_expr()
                self.expect(";")
                return Node("let_tuple", line=line, a=names, b=ty, c=init)
            name = self.expect_ident()
            ty = None
            if self.at(":"):
                self.bump()
                ty = self.parse_type()
            init = None
            if self.at("="):
                self.bump()
                init = self.parse_expr()
            self.expect(";")
            self.note("let-mut" if is_mut else "let")
            return Node("let", line=line, a=name, b=ty, c=init, d=is_mut)
        if self.at("return"):
            self.bump()
            value = None if self.at(";") else self.parse_expr()
            self.expect(";")
            self.note("return")
            return Node("return", line=line, a=value)
        if self.at("break"):
            self.bump()
            self.expect(";")
            self.note("break")
            return Node("break", line=line)
        if self.at("continue"):
            self.bump()
            self.expect(";")
            self.note("continue")
            return Node("continue", line=line)
        if self.at("if"):
            return self.parse_if()
        if self.at("while"):
            self.bump()
            if self.at("let"):
                self.note("while-let")
                self.bump()
                name = self.expect_ident()
                self.expect("=")
                subject = self.parse_expr()
                body = self.parse_block()
                return Node("while_let", line=line, a=name, b=subject, c=body)
            cond = self.parse_expr()
            body = self.parse_block()
            self.note("while")
            return Node("while", line=line, a=cond, b=body)
        if self.at("for"):
            self.bump()
            name = self.expect_ident()
            self.expect("in")
            start = self.parse_expr()
            end = None
            if self.at("..") or self.at("..="):
                self.note("for-range")
                inclusive = self.at("..=")
                self.bump()
                end = self.parse_expr()
                body = self.parse_block()
                return Node("for_range", line=line, a=name, b=start, c=end, d=inclusive, items=[body])
            body = self.parse_block()
            self.note("for-in")
            return Node("for_in", line=line, a=name, b=start, c=body)
        if self.at("match"):
            return self.parse_match()
        if self.at("{"):
            self.note("bare-block")
            return self.parse_block()

        # Expression statement or assignment.
        expr = self.parse_expr()
        if self.at("="):
            self.bump()
            value = self.parse_expr()
            self.expect(";")
            self.note("assign")
            return Node("assign", line=line, a=expr, b=value)
        self.expect(";")
        self.note("expr-stmt")
        return Node("expr_stmt", line=line, a=expr)

    def parse_if(self) -> Node:
        line = self.peek().line
        self.expect("if")
        if self.at("let"):
            self.note("if-let")
            self.bump()
            name = self.expect_ident()
            self.expect("=")
            subject = self.parse_expr()
            then = self.parse_block()
            els = None
            if self.at("else"):
                self.bump()
                els = self.parse_if() if self.at("if") else self.parse_block()
            return Node("if_let", line=line, a=name, b=subject, c=then, d=els)
        cond = self.parse_expr()
        then = self.parse_block()
        els = None
        if self.at("else"):
            self.bump()
            els = self.parse_if() if self.at("if") else self.parse_block()
        self.note("if")
        return Node("if", line=line, a=cond, b=then, c=els)

    def parse_match(self) -> Node:
        line = self.peek().line
        self.expect("match")
        subject = self.parse_expr()
        self.expect("{")
        arms: list[Node] = []
        while not self.at("}"):
            pat = self.parse_pattern()
            guard = None
            if self.at("if"):
                self.note("match-guard")
                self.bump()
                guard = self.parse_expr()
            self.expect("=>")
            body = self.parse_block() if self.at("{") else self.parse_expr()
            if self.at(","):
                self.bump()
            arms.append(Node("arm", a=pat, b=guard, c=body))
        self.expect("}")
        self.note("match")
        return Node("match", line=line, a=subject, items=arms)

    def parse_pattern(self) -> Node:
        # `_` lexes as an IDENT (the lexer treats it as a name start), so a kw/op test never
        # matches it and the wildcard would be silently mis-parsed as a one-element path.
        if self.peek().kind == "ident" and self.peek().text == "_":
            self.note("pattern-wildcard")
            self.bump()
            return Node("pat_wild")
        # TAGGED at parse time. Both kinds used to land in one untagged `pat_lit`, so the matcher
        # had to guess from the text — `str.isdigit()` — which read a digit-shaped STRING pattern
        # as an integer and a HEX integer (`0x10`) as bytes. The information is available here and
        # nowhere else; recovering it later is impossible.
        # `true`/`false` lex as KEYWORDS and `expect_ident` accepts keywords, so a bool pattern
        # fell through to the bare-binder branch: it matched unconditionally and bound a variable
        # literally named `true`. `match b { true => 1, false => 2 }` returned the first arm
        # whatever `b` was.
        if self.at("true") or self.at("false"):
            self.note("pattern-bool")
            return Node("pat_bool", a=self.bump().text == "true")
        if self.at_kind("str"):
            self.note("pattern-string")
            return Node("pat_str", a=self.bump().text)
        if self.at_kind("int") or self.at("-"):
            self.note("pattern-int")
            neg = self.at("-")
            if neg:
                self.bump()
            return Node("pat_int", a=("-" if neg else "") + self.bump().text)
        name = self.expect_ident()
        path = [name]
        while self.at("::"):
            self.bump()
            path.append(self.expect_ident())
        binders: list[str] = []
        if self.at("("):
            self.note("pattern-payload")
            self.bump()
            while not self.at(")"):
                binders.append(self.expect_ident())
                if self.at(","):
                    self.bump()
            self.expect(")")
        return Node("pat_path", a=path, b=binders)

    # ── expressions (precedence climbing) ────────────────────────────────────────────────────
    BINARY_LEVELS: ClassVar[list[list[str]]] = [
        ["||"],
        ["&&"],
        ["==", "!="],
        ["<", "<=", ">", ">="],
        ["|"],
        ["^"],
        ["&"],
        ["SHIFT"],  # `<<` / `>>`, recognized as two ADJACENT angle tokens (see parse_shift)
        ["+", "-"],
        ["*", "/", "%"],
    ]

    def parse_expr(self) -> Node:
        return self.parse_binary(0)

    def _adjacent_shift(self) -> str | None:
        """`>>` and `<<` are lexed as two single tokens so that `Vec<Vec<T>>` still closes.

        They are a shift only when the two angles are genuinely adjacent — same line, consecutive
        columns — which no nested generic close can be, since a type argument always separates
        them.
        """
        a, b = self.peek(), self.peek(1)
        if (
            a.kind == "op"
            and a.text in ("<", ">")
            and b.kind == "op"
            and b.text == a.text
            and a.line == b.line
            and b.col == a.col + 1
        ):
            return a.text * 2
        return None

    def parse_binary(self, level: int) -> Node:
        if level >= len(self.BINARY_LEVELS):
            return self.parse_unary()
        if self.BINARY_LEVELS[level] == ["SHIFT"]:
            node = self.parse_binary(level + 1)
            while (op := self._adjacent_shift()) is not None:
                self.bump()
                self.bump()
                rhs = self.parse_binary(level + 1)
                self.note(f"binop {op}")
                node = Node("binary", a=op, b=node, c=rhs)
            return node
        node = self.parse_binary(level + 1)
        while any(self.at(op) for op in self.BINARY_LEVELS[level]) and self._adjacent_shift() is None:
            op = self.bump().text
            rhs = self.parse_binary(level + 1)
            self.note(f"binop {op}")
            node = Node("binary", a=op, b=node, c=rhs)
        return node

    def parse_unary(self) -> Node:
        if self.at("!"):
            self.note("unary !")
            self.bump()
            return Node("unary", a="!", b=self.parse_unary())
        if self.at("-"):
            self.note("unary -")
            self.bump()
            return Node("unary", a="-", b=self.parse_unary())
        return self.parse_postfix()

    def parse_postfix(self) -> Node:
        node = self.parse_primary()
        while True:
            if self.at("."):
                self.bump()
                name = self.expect_ident()
                if self.at("("):
                    args = self.parse_args()
                    self.note("method-call")
                    node = Node("method", a=node, b=name, items=args)
                else:
                    self.note("field-access")
                    node = Node("field", a=node, b=name)
                continue
            if self.at("["):
                self.bump()
                index = self.parse_expr()
                self.expect("]")
                self.note("index")
                node = Node("index", a=node, b=index)
                continue
            if self.at("("):
                args = self.parse_args()
                self.note("call")
                node = Node("call", a=node, items=args)
                continue
            if self.at("as"):
                # Build a NODE rather than dropping the cast. Discarding it made `4294967296 as
                # i32` evaluate unchanged — the one construct this deliberately-loud parser
                # accepted and silently no-opped. The census still needs to SEE casts (that is how
                # it reports the form), so the loudness belongs in the evaluator, which refuses
                # `cast` outright. The certified source contains none.
                self.note("cast")
                self.bump()
                node = Node("cast", a=node, b=self.parse_type())
                continue
            break
        return node

    def parse_args(self) -> list[Node]:
        self.expect("(")
        args: list[Node] = []
        while not self.at(")"):
            args.append(self.parse_expr())
            if self.at(","):
                self.bump()
        self.expect(")")
        return args

    def _looks_like_record_literal(self) -> bool:
        """`Name {` is a record literal only where a block cannot begin.

        `if x { … }` and `Name { … }` are ambiguous by token alone. The certified sources only
        ever construct records with a `field:` first token inside the brace, so require that.
        """
        if not self.at("{"):
            return False
        return self.peek(1).kind in ("ident", "kw") and self.at(":", 2)

    def parse_primary(self) -> Node:
        t = self.peek()
        if t.kind == "int":
            self.bump()
            self.note("literal-int")
            return Node("int", a=t.text)
        if t.kind == "str":
            self.bump()
            self.note("literal-str")
            return Node("str", a=t.text)
        if self.at("true") or self.at("false"):
            self.bump()
            self.note("literal-bool")
            return Node("bool", a=t.text == "true")
        if self.at("("):
            self.bump()
            inner = self.parse_expr()
            if self.at(","):
                self.note("tuple-literal")
                elems = [inner]
                while self.at(","):
                    self.bump()
                    if self.at(")"):
                        break
                    elems.append(self.parse_expr())
                self.expect(")")
                return Node("tuple", items=elems)
            self.expect(")")
            return Node("paren", a=inner)
        if self.at("["):
            self.note("array-literal")
            self.bump()
            elems: list[Node] = []
            while not self.at("]"):
                elems.append(self.parse_expr())
                if self.at(";"):  # [value; count]
                    self.note("array-repeat")
                    self.bump()
                    count = self.parse_expr()
                    self.expect("]")
                    return Node("array_repeat", a=elems[0], b=count)
                if self.at(","):
                    self.bump()
            self.expect("]")
            return Node("array", items=elems)
        if t.kind in ("ident", "kw"):
            name = self.expect_ident()
            path = [name]
            while self.at("::"):
                self.bump()
                path.append(self.expect_ident())
                if self.at("<"):  # turbofish-style generic instantiation
                    self.note("path-generic-args")
                    self.bump()
                    self.parse_type()
                    while self.at(","):
                        self.bump()
                        self.parse_type()
                    self.expect(">")
            if len(path) > 1:
                self.note("path")
            if self._looks_like_record_literal():
                self.bump()
                fields: list[Node] = []
                while not self.at("}"):
                    fname = self.expect_ident()
                    self.expect(":")
                    fields.append(Node("initfield", a=fname, b=self.parse_expr()))
                    if self.at(","):
                        self.bump()
                self.expect("}")
                self.note("record-literal")
                return Node("record_lit", a=path, items=fields)
            return Node("path" if len(path) > 1 else "name", a=path)
        raise ParseError("unexpected token in expression", t, self.path)


def parse(src: str, path: str = "<input>") -> tuple[Node, set[str]]:
    p = Parser(src, path)
    program = p.parse_program()
    return program, p.forms
