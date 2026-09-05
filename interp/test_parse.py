"""Anti-stub tests for the Phase-0 census.

SC-P4, applied to this package: the census reports which forms the certified source uses, and its
most interesting output is a set of ABSENCES — no `for` loop, no array indexing, no `continue`, no
`&&`/`||`. An absence is only evidence if the detector can see the thing when it IS there. A
parser that silently swallowed those constructs would produce exactly the same report.

So each absence claimed by the census is paired below with a snippet that MUST make the parser
report it, and the parser is separately proven loud on malformed input.

    python interp/test_parse.py
"""

from __future__ import annotations

import sys

from sigil_lex import LexError
from sigil_parse import ParseError, parse

sys.setrecursionlimit(20000)

FN = "module m;\nfn f() -> i64 {{\n{body}\n}}\n"

# (label, source, forms that MUST be reported)
POSITIVE = [
    ("for-range", FN.format(body="let mut s: i64 = 0;\nfor v in 0..10 { s = s + v; }\nreturn s;"),
     {"for-range"}),
    ("for-in", FN.format(body="let mut s: i64 = 0;\nfor v in xs { s = s + v; }\nreturn s;"),
     {"for-in"}),
    ("index", FN.format(body="return a[0];"), {"index"}),
    ("continue", FN.format(body="while true { continue; }\nreturn 0;"), {"continue"}),
    ("logical-and", FN.format(body="if a && b { return 1; }\nreturn 0;"), {"binop &&"}),
    ("logical-or", FN.format(body="if a || b { return 1; }\nreturn 0;"), {"binop ||"}),
    ("match-guard", FN.format(body="match x { 1 if y => { return 1; }, _ => { return 0; } }"),
     {"match", "match-guard", "pattern-wildcard", "pattern-int"}),
    ("if-let", FN.format(body="if let v = o { return v; }\nreturn 0;"), {"if-let"}),
    ("while-let", FN.format(body="while let v = o { return v; }\nreturn 0;"), {"while-let"}),
    ("array-literal", FN.format(body="let a: [i64; 2] = [1, 2];\nreturn 0;"),
     {"array-literal", "type-array"}),
    ("cast", FN.format(body="return x as i64;"), {"cast"}),
    ("attribute", "#[ring(outer)]\nmodule m;\n", {"attribute"}),
    ("use-decl", "module m;\nuse other;\n", {"use-decl"}),
    ("string-pattern", FN.format(body='match s { "a" => { return 1; }, _ => { return 0; } }'),
     {"pattern-string"}),
    ("shift", FN.format(body="return v >> 7;"), {"binop >>"}),
    ("slice-type", "module m;\nfn f(h: &[str]) -> bool { return true; }\n", {"type-slice"}),
    ("fn-type", "module m;\nfn f(g: Fn(i64) -> i64) -> i64 { return 0; }\n", {"type-fn"}),
]

# Nested generics must still close: `>>` is a shift only when the angles are ADJACENT.
NESTED_GENERIC = "module m;\nfn f(v: Vec<Vec<i64>>) -> i64 { return 0; }\n"

MALFORMED = [
    ("unclosed brace", "module m;\nfn f() -> i64 { return 0;\n"),
    ("bad item", "module m;\nwibble foo;\n"),
    ("unterminated string", 'module m;\nfn f() -> str { return "abc;\n}\n'),
    ("stray operator", "module m;\nfn f() -> i64 { return * 1; }\n"),
]


def main() -> int:
    failures: list[str] = []

    for label, src, expected in POSITIVE:
        try:
            _, forms = parse(src, f"<{label}>")
        except (ParseError, LexError) as e:
            failures.append(f"{label}: parser rejected its own positive fixture: {e}")
            continue
        missing = expected - forms
        if missing:
            failures.append(f"{label}: parsed but did NOT report {sorted(missing)}")

    try:
        _, forms = parse(NESTED_GENERIC, "<nested-generic>")
        if "binop >>" in forms:
            failures.append("nested generic Vec<Vec<i64>> was mis-read as a shift")
    except (ParseError, LexError) as e:
        failures.append(f"nested generic must parse: {e}")

    for label, src in MALFORMED:
        try:
            parse(src, f"<{label}>")
        except (ParseError, LexError):
            continue
        failures.append(f"{label}: parser ACCEPTED malformed input — it is not loud")

    if failures:
        print(f"FAILED ({len(failures)}):")
        for f in failures:
            print(f"  {f}")
        return 1
    print(f"ok: {len(POSITIVE)} form detectors, 1 nested-generic guard, {len(MALFORMED)} loudness checks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
