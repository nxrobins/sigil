"""Compose the CERTIFIED SOURCE — the exact 1.15 MB program the seed is compiled from.

This mirrors `cap0_input()` / `with_driver_input()` in
`crates/sigil-runtime/tests/pipeline_differential.rs`. Reimplementing a composition by hand is
exactly the kind of thing that is subtly wrong in a way no test notices, so this module does not
ask to be trusted: `verify()` hashes the result and compares it against the digest the Rust side
pins (and `seed/PROVENANCE.md` records). If the digest matches, the composition is provably the
same bytes; if it drifts, this fails loudly rather than quietly compiling a slightly different
program and reporting a mismatch as an interpreter bug.

    python interp/certified.py          # compose + verify the digest
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# PIN_WITH_DRIVER_SRC_SHA256, from pipeline_differential.rs and seed/PROVENANCE.md.
PIN_WITH_DRIVER_SRC_SHA256 = "fa69ab5fc7bbd58dba180432fc49d8cc7b7eff29cfdfa48b9ffe38c00d0cdc94"
PIN_WITH_DRIVER_SRC_CHARS = 1_151_054

# `boot_tool` composes these in this order, each with its `module X;` header stripped.
BOOT_MODULES = [
    ("selfhost/lexer.sigil", "lexer"),
    ("selfhost/parser.sigil", "parser"),
    ("selfhost/name_resolution.sigil", "name_resolution"),
    ("selfhost/typecheck.sigil", "typecheck"),
    ("selfhost/ring_check.sigil", "ring_check"),
    ("selfhost/effect_check.sigil", "effect_check"),
    ("selfhost/taint_check.sigil", "taint_check"),
    ("selfhost/cap_check.sigil", "cap_check"),
    ("selfhost/own_check.sigil", "own_check"),
    ("selfhost/air.sigil", "air"),
    ("selfhost/pipeline.sigil", "pipeline"),
]

STRIP = {
    "stdlib/sigil/string.sigil": ["str_utoa_u64"],
    "stdlib/sigil/strings.sigil": [
        "str_contains",
        "__sigil_slice_str_contains",
        "str_parse_u64",
        "str_parse_u32",
        "str_parse_i32",
    ],
}

SH_MONO_BODY = (
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n"
    "    let src: str = opt.unwrap_or(\"\");\n"
    "    let toks: Vec<Token> = lex(src);\n"
    "    let mut nodes: Arena<PNode> = Arena::new();\n"
    "    let mut kids: Vec<i64> = Vec::new();\n"
    "    let root: i64 = parser_parse(src, toks, nodes, kids);\n"
    "    let e: i64 = mn_expand(nodes, kids, root);\n"
    "    let enc: str = sh_compile(nodes, kids, root);\n"
    "    return enc.as_output();"
)

RUN_FROM_STR_ENTRY = (
    "pub fn run_from_str(src: str) -> i64 {\n"
    "    let toks: Vec<Token> = lex(src);\n"
    "    let mut nodes: Arena<PNode> = Arena::new();\n"
    "    let mut kids: Vec<i64> = Vec::new();\n"
    "    let root: i64 = parser_parse(src, toks, nodes, kids);\n"
    "    let e: i64 = mn_expand(nodes, kids, root);\n"
    "    let hex: str = ai_encode_wasm(nodes, kids, root);\n"
    "    return hex.as_output();\n"
    "}\n"
)

DRIVER = (
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n"
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n"
    "    let src: str = opt.unwrap_or(\"\");\n"
    "    let toks: Vec<Token> = lex(src);\n"
    "    let mut nodes: Arena<PNode> = Arena::new();\n"
    "    let mut kids: Vec<i64> = Vec::new();\n"
    "    let root: i64 = parser_parse(src, toks, nodes, kids);\n"
    "    let e: i64 = mn_expand(nodes, kids, root);\n"
    "    let out: str = sh_compile(nodes, kids, root);\n"
    "    return out.as_output();\n"
    "}\n"
)


def read(rel: str) -> str:
    return (REPO / rel).read_text(encoding="utf-8")


def strip_header(src: str, module: str) -> str:
    return src.replace(f"\nmodule {module};\n", "\n")


def strip_fn(src: str, name: str) -> str:
    marker = f"pub fn {name}("
    start = src.index(marker)
    line_start = src.rfind("\n", 0, start) + 1
    end_pat = "\n}\n"
    end = src.index(end_pat, start)
    return src[:line_start] + src[end + len(end_pat):]


def boot_mono_tool(body: str) -> str:
    parts = [strip_header(read(rel), mod) for rel, mod in BOOT_MODULES]
    base = (
        "module tool;\n"
        + "\n".join(parts)
        + "\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n"
        + body
        + "\n}\n"
    )
    mn = strip_header(read("selfhost/monomorph.sigil"), "monomorph")
    marker = "\npub fn tool_main("
    idx = base.index(marker)
    return f"{base[:idx]}\n{mn}\n{base[idx:]}"


def cap0_input() -> str:
    vecsrc = strip_header(read("stdlib/sigil/vec.sigil"), "vec")
    arenasrc = strip_header(read("stdlib/sigil/arena.sigil"), "arena")
    stringsrc = read("stdlib/sigil/string.sigil")
    for name in STRIP["stdlib/sigil/string.sigil"]:
        stringsrc = strip_fn(stringsrc, name)
    stringssrc = read("stdlib/sigil/strings.sigil")
    for name in STRIP["stdlib/sigil/strings.sigil"]:
        stringssrc = strip_fn(stringssrc, name)
    optionsrc = read("stdlib/sigil/option.sigil")

    base = boot_mono_tool(SH_MONO_BODY)
    cut = base.index("\npub fn tool_main(")
    header = "module tool;\n"
    hidx = base.index(header) + len(header)
    return (
        f"{base[:hidx]}{vecsrc}\n{arenasrc}\n{base[hidx:cut]}\n"
        f"{stringsrc}\n{stringssrc}\n{optionsrc}"
    )


def with_driver_input() -> str:
    cap = cap0_input()
    idx = cap.index("\nmodule string;")
    return f"{cap[:idx]}\n{RUN_FROM_STR_ENTRY}\n{DRIVER}{cap[idx:]}"


def verify(source: str | None = None) -> str:
    """Compose and prove the bytes are the certified ones. Raises with a diagnosis otherwise."""
    src = with_driver_input() if source is None else source
    raw = src.encode("utf-8")
    digest = hashlib.sha256(raw).hexdigest()
    if digest != PIN_WITH_DRIVER_SRC_SHA256:
        # BYTES, not codepoints. Rust's `.len()` on a `String` counts bytes, and the certified
        # source carries thousands of multi-byte characters (em-dashes in comments), so a
        # codepoint count reads ~5,000 short and looks like drift when nothing has moved.
        raise SystemExit(
            "certified source composition DRIFTED\n"
            f"  bytes  : {len(raw):,} (pinned {PIN_WITH_DRIVER_SRC_CHARS:,}, "
            f"delta {len(raw) - PIN_WITH_DRIVER_SRC_CHARS:+,})\n"
            f"  sha256 : {digest}\n"
            f"  pinned : {PIN_WITH_DRIVER_SRC_SHA256}\n"
            "This module mirrors cap0_input()/with_driver_input() in pipeline_differential.rs; "
            "one of them moved."
        )
    return src


def main() -> int:
    src = verify()
    raw = len(src.encode("utf-8"))
    print(f"certified source composed and VERIFIED: {raw:,} bytes ({len(src):,} codepoints)")
    print(f"  sha256 {PIN_WITH_DRIVER_SRC_SHA256}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
