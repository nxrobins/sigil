"""SIGIL lexer — independent implementation.

INDEPENDENCE DISCIPLINE (see README.md): this package is written from the OBSERVABLE SYNTAX of
`selfhost/*.sigil` and `stdlib/sigil/*.sigil`, never by porting `crates/sigil-compiler/src/`. It
must import nothing from the Rust tree. Its purpose is to be a second implementation whose binary
lineage does not pass through the Rust oracle, so that `interpret(S)` applied to `S` is genuine
evidence about the committed seed (docs/CLAIMS.md, HB-3).
"""

from __future__ import annotations

from dataclasses import dataclass

KEYWORDS = {
    "module", "use", "pub", "fn", "let", "mut", "if", "else", "while", "for", "in",
    "return", "break", "continue", "match", "record", "enum", "impl", "trait", "const",
    "true", "false", "cap", "type", "effect", "actor", "state", "handler", "spawn",
    "mint", "entry", "as", "self", "ring", "on", "resume", "with", "do", "handle",
}

# Multi-character operators, longest first so the scanner never splits one.
OPERATORS = [
    "..=", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "::", "..",
    "+", "-", "*", "/", "%", "<", ">", "=", "!", "&", "|", "^",
    "(", ")", "{", "}", "[", "]", ",", ";", ":", ".", "@", "?", "#",
]


class LexError(Exception):
    def __init__(self, msg: str, line: int, col: int, path: str = "<input>") -> None:
        super().__init__(f"{path}:{line}:{col}: {msg}")
        self.line = line
        self.col = col


@dataclass(slots=True)
class Token:
    kind: str  # ident | kw | int | str | op | eof
    text: str
    line: int
    col: int


def _string_literal(src: str, i: int, line: int, col: int, path: str) -> tuple[str, int, int]:
    """Scan a double-quoted literal starting at the opening quote. Returns (value, next_i, ncols).

    Escapes are decoded here so the parser never sees them: a literal's VALUE is what the
    interpreter compares and emits, and the certified sources embed `\\n`, `\\"` and `\\\\`.
    """
    out: list[str] = []
    i += 1
    cols = 1
    while True:
        if i >= len(src):
            raise LexError("unterminated string literal", line, col, path)
        c = src[i]
        if c == '"':
            return "".join(out), i + 1, cols + 1
        if c == "\n":
            raise LexError("newline inside string literal", line, col, path)
        if c == "\\":
            if i + 1 >= len(src):
                raise LexError("unterminated escape", line, col, path)
            nxt = src[i + 1]
            mapping = {"n": "\n", "t": "\t", "r": "\r", "0": "\0", '"': '"', "\\": "\\", "'": "'"}
            if nxt not in mapping:
                raise LexError(f"unknown escape \\{nxt}", line, col, path)
            out.append(mapping[nxt])
            i += 2
            cols += 2
            continue
        out.append(c)
        i += 1
        cols += 1


def lex(src: str, path: str = "<input>") -> list[Token]:
    toks: list[Token] = []
    i = 0
    line = 1
    col = 1
    n = len(src)
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            col = 1
            i += 1
            continue
        if c in " \t\r":
            i += 1
            col += 1
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":
            depth = 1
            i += 2
            col += 2
            while i < n and depth:
                if src.startswith("/*", i):
                    depth += 1
                    i += 2
                elif src.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    if src[i] == "\n":
                        line += 1
                        col = 0
                    i += 1
                    col += 1
            continue
        if c == '"':
            start_col = col
            value, i, cols = _string_literal(src, i, line, col, path)
            toks.append(Token("str", value, line, start_col))
            col += cols
            continue
        if c.isdigit():
            start = i
            start_col = col
            if c == "0" and i + 1 < n and src[i + 1] in "xX":
                i += 2
                while i < n and (src[i].isalnum() or src[i] == "_"):
                    i += 1
            else:
                while i < n and (src[i].isdigit() or src[i] == "_"):
                    i += 1
            text = src[start:i]
            col += i - start
            toks.append(Token("int", text, line, start_col))
            continue
        if c.isalpha() or c == "_":
            start = i
            start_col = col
            while i < n and (src[i].isalnum() or src[i] == "_"):
                i += 1
            text = src[start:i]
            col += i - start
            toks.append(Token("kw" if text in KEYWORDS else "ident", text, line, start_col))
            continue
        for op in OPERATORS:
            if src.startswith(op, i):
                toks.append(Token("op", op, line, col))
                i += len(op)
                col += len(op)
                break
        else:
            raise LexError(f"unexpected character {c!r}", line, col, path)
    toks.append(Token("eof", "", line, col))
    return toks
