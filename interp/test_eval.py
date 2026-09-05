"""Semantic pins for the evaluator.

These are the decisions where an independent implementation is most likely to differ from the
oracle — and where differing *correctly* is the whole point of the exercise. Each one is pinned so
a later change cannot quietly alter the language this interpreter implements:

* i64 wraps at the 64-bit boundary;
* `/` and `%` truncate toward zero (Python's `//` and `%` do NOT);
* records are reference-semantic;
* `str` is a byte string, so `len`/`byte_at`/`substr` are byte indexed, not codepoint indexed;
* `&&`/`||` short-circuit;
* out-of-bounds container access traps rather than returning a wrong value.

    python interp/test_eval.py
"""

from __future__ import annotations

from pathlib import Path

from sigil_eval import Interp, SigilError
from sigil_parse import parse

I64_MAX = (1 << 63) - 1
I64_MIN = -(1 << 63)

REPO = Path(__file__).resolve().parent.parent
STDLIB = (
    "stdlib/sigil/vec.sigil",
    "stdlib/sigil/string.sigil",
    "stdlib/sigil/strings.sigil",
)


def run(src: str, fn: str = "main", args: list | None = None, *, stdlib: bool = False):
    """Run a fixture. With `stdlib=True` the REAL `string.sigil` / `strings.sigil` bodies are
    loaded, so the string-method pins exercise SIGIL code rather than grading the interpreter's
    own conveniences against themselves — the methods below (`concat`, `join`, `bytes_eq`,
    `itoa`) are not primitives, they desugar to those functions.
    """
    interp = Interp()
    if stdlib:
        for rel in STDLIB:
            lib, _ = parse((REPO / rel).read_text(encoding="utf-8"), rel)
            interp.load(lib)
    program, _ = parse(src, f"<{fn}>")
    interp.load(program)
    return interp.call_named(fn, args or [])


def expect(label: str, got, want, failures: list) -> None:
    if got != want or type(got) is not type(want):
        failures.append(f"{label}: got {got!r} ({type(got).__name__}), want {want!r}")


def expect_trap(label: str, src: str, failures: list) -> None:
    try:
        run(src)
    except SigilError:
        return
    failures.append(f"{label}: expected a trap, but the program completed")


def main() -> int:
    f: list = []

    # ── i64 wrapping ─────────────────────────────────────────────────────────────────────────
    expect(
        "i64 wraps at MAX",
        run(f"module m;\nfn main() -> i64 {{ return {I64_MAX} + 1; }}"),
        I64_MIN,
        f,
    )
    expect(
        "i64 wraps at MIN",
        run(f"module m;\nfn main() -> i64 {{ return {I64_MIN} - 1; }}"),
        I64_MAX,
        f,
    )

    # ── division truncates toward zero, not toward negative infinity ─────────────────────────
    expect("-7 / 2 truncates toward zero", run("module m;\nfn main() -> i64 { return (0 - 7) / 2; }"), -3, f)
    expect("7 / -2 truncates toward zero", run("module m;\nfn main() -> i64 { return 7 / (0 - 2); }"), -3, f)
    expect("-7 % 2 takes the sign of the dividend", run("module m;\nfn main() -> i64 { return (0 - 7) % 2; }"), -1, f)
    expect_trap("divide by zero traps", "module m;\nfn main() -> i64 { return 1 / 0; }", f)

    # ── records are REFERENCE semantic ───────────────────────────────────────────────────────
    ref = """
module m;
record P { x: i64 }
fn bump(p: P) -> i64 { p.x = p.x + 1; return 0; }
fn main() -> i64 {
    let a: P = P { x: 1 };
    let b: P = a;
    let q: i64 = bump(a);
    return b.x;
}
"""
    expect("a record passed to a fn is shared, not copied", run(ref), 2, f)

    # ── str is a BYTE string ─────────────────────────────────────────────────────────────────
    # "é" is two bytes in UTF-8; a codepoint-indexed implementation would report 1.
    expect(
        "str::len counts BYTES",
        run('module m;\nfn main() -> i64 { let s: str = "é"; return s.len(); }'),
        2,
        f,
    )
    expect("str::byte_at returns a byte", run('module m;\nfn main() -> i64 { let s: str = "AB"; return s.byte_at(1); }'), 66, f)
    expect("str::substr is byte indexed", run('module m;\nfn main() -> str { let s: str = "hello"; return s.substr(1, 3); }'), b"el", f)
    # These four run the REAL SIGIL bodies (`string::str_concat`, `str_join`, `str_itoa`,
    # `strings::str_bytes_eq`) over the interpreter's linear memory — alloc / store8 /
    # str_from_raw — not a Python shortcut.
    expect(
        "str::concat runs str_concat",
        run('module m;\nfn main() -> str { let a: str = "ab"; return a.concat("cd"); }', stdlib=True),
        b"abcd",
        f,
    )
    expect(
        "str::bytes_eq runs str_bytes_eq",
        run('module m;\nfn main() -> bool { let a: str = "ab"; return a.bytes_eq("ab"); }', stdlib=True),
        True,
        f,
    )
    expect(
        "str::bytes_eq rejects a differing string",
        run('module m;\nfn main() -> bool { let a: str = "ab"; return a.bytes_eq("ac"); }', stdlib=True),
        False,
        f,
    )
    expect(
        "str::join runs str_join",
        run(
            'module m;\nfn main() -> str ! { Alloc } { let mut v: Vec<str> = Vec::new(); '
            'let q: i64 = v.push("a"); let r: i64 = v.push("b"); let s: str = "-"; '
            "return s.join(v); }",
            stdlib=True,
        ),
        b"a-b",
        f,
    )
    expect(
        "i64::itoa runs str_itoa",
        run("module m;\nfn main() -> str { let n: i64 = 0 - 42; return n.itoa(); }", stdlib=True),
        b"-42",
        f,
    )
    # str_itoa does its digit math in NEGATIVE space specifically so this case survives; negating
    # i64::MIN would overflow. A Python shortcut would pass this by accident, the SIGIL body only
    # by being correct.
    expect(
        "i64::itoa at i64::MIN",
        run(f"module m;\nfn main() -> str {{ let n: i64 = {I64_MIN}; return n.itoa(); }}", stdlib=True),
        str(I64_MIN).encode(),
        f,
    )
    expect_trap(
        "str::byte_at out of bounds traps",
        'module m;\nfn main() -> i64 { let s: str = "a"; return s.byte_at(5); }',
        f,
    )

    # ── short-circuit ────────────────────────────────────────────────────────────────────────
    # The right operand would divide by zero; short-circuiting means it is never evaluated.
    expect(
        "&& short-circuits",
        run("module m;\nfn main() -> bool { return false && (1 / 0) == 0; }"),
        False,
        f,
    )
    expect(
        "|| short-circuits",
        run("module m;\nfn main() -> bool { return true || (1 / 0) == 0; }"),
        True,
        f,
    )

    # ── control flow ─────────────────────────────────────────────────────────────────────────
    loop_src = """
module m;
fn main() -> i64 {
    let mut s: i64 = 0;
    let mut i: i64 = 0;
    while i < 10 {
        i = i + 1;
        if i == 3 { continue; }
        if i == 8 { break; }
        s = s + i;
    }
    return s;
}
"""
    # 1+2+4+5+6+7 = 25 (3 skipped by continue, loop stops at 8)
    expect("while / break / continue", run(loop_src), 25, f)

    # ── Vec ──────────────────────────────────────────────────────────────────────────────────
    vec_src = """
module m;
fn main() -> i64 {
    let mut v: Vec<i64> = Vec::new();
    let a: i64 = v.push(10);
    let b: i64 = v.push(20);
    let q: i64 = v.set(0, 5);
    return v.get(0) + v.get(1) + v.len();
}
"""
    expect("Vec push/get/set/len", run(vec_src), 27, f)
    expect_trap(
        "Vec::get out of bounds traps",
        "module m;\nfn main() -> i64 { let mut v: Vec<i64> = Vec::new(); return v.get(0); }",
        f,
    )

    # ── records + methods ────────────────────────────────────────────────────────────────────
    method_src = """
module m;
record Counter { n: i64 }
impl Counter {
    pub fn bump(self: Counter, by: i64) -> i64 { self.n = self.n + by; return self.n; }
}
fn main() -> i64 {
    let c: Counter = Counter { n: 1 };
    let x: i64 = c.bump(4);
    return c.n;
}
"""
    expect("impl method dispatch mutates through self", run(method_src), 5, f)

    # ── found by the 2026-08-02 sweep; each was a place the interpreter was silently MORE
    # ── PERMISSIVE than the compiler, which is how a differential agrees for the wrong reason.
    expect_trap(
        "substr must trap inside a multi-byte codepoint",
        'module m;\nfn main() -> str { let s: str = "é"; return s.substr(0, 1); }',
        f,
    )
    expect(
        "substr on a boundary still works",
        run('module m;\nfn main() -> str { let s: str = "é!"; return s.substr(2, 3); }'),
        b"!",
        f,
    )
    expect_trap(
        "i64::MIN / -1 traps rather than wrapping",
        f"module m;\nfn main() -> i64 {{ let a: i64 = {I64_MIN}; let b: i64 = 0 - 1; return a / b; }}",
        f,
    )
    expect_trap(
        "assignment to an undeclared name is an error",
        "module m;\nfn main() -> i64 { nope = 5; return nope; }",
        f,
    )
    expect(
        "Vec::set echoes the INDEX back",
        run(
            "module m;\nfn main() -> i64 ! { Alloc } { let mut v: Vec<i64> = Vec::new(); "
            "let a: i64 = v.push(7); let b: i64 = v.push(8); return v.set(1, 99); }"
        ),
        1,
        f,
    )
    # Block scoping: the oracle clones the environment per block, so neither of these leaks.
    expect(
        "an inner-block let does not overwrite the outer binding",
        run("module m;\nfn main() -> i64 { let y: i64 = 1; if 1 == 1 { let y: i64 = 2; } else { } return y; }"),
        1,
        f,
    )
    expect_trap(
        "a loop body's temporary does not outlive the loop",
        "module m;\nfn main() -> i64 { let mut i: i64 = 0; while i < 2 { let t: i64 = i; i = i + 1; } return t; }",
        f,
    )
    # A pattern naming a CONSTANT compares against it; it is not an unconditional binder.
    expect(
        "a const pattern matches by value, not by binding",
        run(
            "module m;\nconst TOK_A: i64 = 1;\nconst TOK_B: i64 = 2;\n"
            "fn main() -> i64 { let k: i64 = 2; match k { TOK_A => { return 100; } "
            "TOK_B => { return 200; } _ => { return 300; } } }"
        ),
        200,
        f,
    )

    # ── INTERP-AUDIT §D: latent classes. Each is unreachable from the certified source today and
    # ── each silently produced a WRONG value before. Where the right semantics are knowable the
    # ── behaviour is fixed; where they are not, the interpreter refuses rather than guesses.
    expect_trap(
        "Vec::with_capacity refuses (it would give Vec two representations)",
        "module m;\nfn main() -> i64 ! { Alloc } { let mut v: Vec<i64> = Vec::with_capacity(4); return 0; }",
        f,
    )
    expect_trap(
        "a local shadowing a fn name cannot be called",
        "module m;\nfn helper() -> i64 { return 1; }\n"
        "fn main() -> i64 { let helper: i64 = 99; return helper(); }",
        f,
    )
    expect_trap(
        "`==` on an enum refuses rather than using Python identity",
        "module m;\nenum Opt { Non, Som(i64) }\n"
        "fn main() -> bool { let a: Opt = Som(1); let b: Opt = Som(1); return a == b; }",
        f,
    )
    # Literal patterns are TAGGED at parse time; guessing from the text read hex as bytes and a
    # digit-shaped string as an integer.
    expect(
        "a hex integer pattern matches by value",
        run("module m;\nfn main() -> i64 { let b: i64 = 16; match b { 0x10 => { return 1; } _ => { return 0; } } }"),
        1,
        f,
    )
    expect(
        "a digit-shaped STRING pattern matches as a string",
        run('module m;\nfn main() -> i64 { let s: str = "1"; match s { "1" => { return 10; } _ => { return 20; } } }'),
        10,
        f,
    )

    # ── closing bug sweep. Each of these silently produced a WRONG VALUE before.
    expect(
        "a match binder does not leak past the match",
        run("module m;\nenum E { N, S(i64) }\n"
            "fn main() -> i64 { let v: i64 = 42; match S(9) { S(v) => { } N => { } } return v; }"),
        42,
        f,
    )
    expect(
        "a binder from an arm whose GUARD failed does not survive",
        run("module m;\nfn main() -> i64 { let x: i64 = 10; "
            "match 3 { x if x > 5 => { return 1; } _ => { } } return x; }"),
        10,
        f,
    )
    expect(
        "a for-loop variable does not clobber an outer binding",
        run("module m;\nfn main() -> i64 { let i: i64 = 7; for i in 0..3 { } return i; }"),
        7,
        f,
    )
    expect(
        "bool patterns match by value, not as binders",
        run("module m;\nfn main() -> i64 { let b: bool = false; "
            "match b { true => { return 1; } false => { return 2; } } }"),
        2,
        f,
    )
    # `==` on str byte-compares since the compiler does (PR #699) — this arm used to
    # expect_trap; Python `bytes` equality is now exactly the compiler's semantics.
    expect(
        "`==` on str compares bytes",
        run('module m;\nfn main() -> bool { let a: str = "ab"; return a == "ab"; }'),
        True,
        f,
    )
    expect(
        "a substr view is `==` a byte-equal literal (bytes, not addresses)",
        run('module m;\nfn main() -> bool { let s: str = "fnx"; '
            'let v: str = s.substr(0, 2); return v == "fn"; }'),
        True,
        f,
    )
    expect(
        "`!=` on str is the negation: a view differs from its longer parent",
        run('module m;\nfn main() -> bool { let s: str = "fnx"; '
            'let v: str = s.substr(0, 2); return v != s; }'),
        True,
        f,
    )
    expect_trap(
        "a negative index traps rather than wrapping to the end",
        "module m;\nfn main() -> i64 ! { Alloc } { let mut v: Vec<i64> = Vec::new(); "
        "let q: i64 = v.push(10); let r: i64 = v.push(20); let i: i64 = 0 - 1; return v[i]; }",
        f,
    )
    expect_trap(
        "reading an uninitialised let is an error, not a silent None",
        "module m;\nfn main() -> i64 { let x: i64; return x; }",
        f,
    )
    expect_trap(
        "a bare `return` in a function declaring a return type is an error",
        "module m;\nfn g() -> i64 { return; }\nfn main() -> i64 { return g(); }",
        f,
    )
    expect_trap(
        "a duplicate record name is refused",
        "module m;\nrecord P { x: i64 }\nrecord P { y: i64 }\nfn main() -> i64 { return 0; }",
        f,
    )
    expect_trap(
        "a duplicate enum VARIANT is refused (it mis-routes method dispatch)",
        "module m;\nenum A { X }\nenum B { X }\nfn main() -> i64 { return 0; }",
        f,
    )
    expect_trap(
        "store8 outside the allocated region traps",
        "module m;\nfn main() -> i64 ! { Alloc } { let p: i64 = alloc(2); "
        "store8(p + 1000, 65); return 0; }",
        f,
    )

    if f:
        print(f"FAILED ({len(f)}):")
        for msg in f:
            print(f"  {msg}")
        return 1
    print("ok: i64 wrapping, truncating division, reference records, byte strings, "
          "short-circuit, control flow, Vec, methods")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
