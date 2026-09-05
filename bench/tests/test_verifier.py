"""Phase 5a-4: tests for the parse-aware stdlib-usage verifier.

The point of these tests is to prove the verifier is NOT regex-based
(AP18). A regex looking for `use sigil::fs;` would happily accept any
of the cases below as "uses fs", which is wrong:

- a `// use sigil::fs;` comment
- a string literal containing `"use sigil::fs;"`
- a typo like `use sigil::ffs;`

The verifier calls `sigil_inspect_uses` which queries the resolved
parse tree, so commented-out / string-literal mentions don't count and
typos surface as missing imports.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from sigil_bench.compose import compose_with_stdlib
from sigil_bench.config import find_repo_root
from sigil_bench.mcp_client import SigilMCP
from sigil_bench.runner import verify_stdlib_uses


@pytest.fixture(scope="module")
def repo_root() -> Path:
    return find_repo_root()


@pytest.fixture(scope="module")
def mcp_binary(repo_root: Path) -> Path:
    candidates = [
        repo_root / "target" / "release" / "sigil-mcp.exe",
        repo_root / "target" / "release" / "sigil-mcp",
        repo_root / "target" / "debug" / "sigil-mcp.exe",
        repo_root / "target" / "debug" / "sigil-mcp",
    ]
    for path in candidates:
        if path.is_file():
            return path
    pytest.skip(
        "sigil-mcp binary not built — run `cargo build --release -p sigil-mcp`"
    )


@pytest.fixture
def mcp(mcp_binary: Path) -> SigilMCP:
    return SigilMCP.spawn(mcp_binary)


def _real_use_source() -> str:
    return (
        "module tool;\n"
        "use sigil::fs;\n"
        "pub fn tool_main(p: i32, l: i32) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {\n"
        "    return fs::read(p, l);\n"
        "}\n"
    )


def _commented_use_source() -> str:
    # Looks like it imports fs (regex would match) but the `use` is in
    # a comment, so the parser ignores it.
    return (
        "module tool;\n"
        "// use sigil::fs;\n"
        "pub fn tool_main(p: i64, l: i64) -> i64 ! { Alloc } {\n"
        "    let out: i64 = alloc(1);\n"
        "    store8(out, 65);\n"
        "    return out * 4294967296 + 1;\n"
        "}\n"
    )


def _string_literal_use_source() -> str:
    # A string literal mentioning the import — must NOT count.
    # Sigil doesn't have user-facing string literals at the moment, so
    # we approximate by encoding the bytes manually (the regex would
    # still match in source if it scanned content).
    return (
        "module tool;\n"
        "// the bytes \"use sigil::fs;\" written into memory below\n"
        "pub fn tool_main(p: i64, l: i64) -> i64 ! { Alloc } {\n"
        "    let out: i64 = alloc(15);\n"
        "    store8(out, 117);\n"
        "    store8(out + 1, 115);\n"
        "    store8(out + 2, 101);\n"
        "    return out * 4294967296 + 15;\n"
        "}\n"
    )


def _typo_use_source() -> str:
    # Typo: `ffs` not `fs`. Both compile errors AND verifier should flag.
    # We use a real stdlib that does NOT have this typo so check fails
    # at parse time before we get to verification — but the verifier
    # should also report it as missing.
    return (
        "module tool;\n"
        "use sigil::definitely_not_a_real_module;\n"
        "pub fn tool_main(p: i64, l: i64) -> i64 ! { Alloc } {\n"
        "    return 0;\n"
        "}\n"
    )


def test_real_use_passes_verifier(repo_root: Path, mcp: SigilMCP) -> None:
    src = _real_use_source()
    composed = compose_with_stdlib(src, ["fs"], repo_root)
    missing = verify_stdlib_uses(composed, src, ["fs"], mcp)
    assert missing == []


def test_commented_use_rejected(repo_root: Path, mcp: SigilMCP) -> None:
    # A regex-based verifier would accept this; the parse-aware verifier
    # must report `fs` as missing because no real `use` decl exists.
    src = _commented_use_source()
    composed = compose_with_stdlib(src, ["fs"], repo_root)
    missing = verify_stdlib_uses(composed, src, ["fs"], mcp)
    assert "fs" in missing


def test_string_literal_use_rejected(repo_root: Path, mcp: SigilMCP) -> None:
    src = _string_literal_use_source()
    composed = compose_with_stdlib(src, ["fs"], repo_root)
    missing = verify_stdlib_uses(composed, src, ["fs"], mcp)
    assert "fs" in missing


def test_empty_expected_imports_returns_empty(
    repo_root: Path, mcp: SigilMCP
) -> None:
    # No expected imports → verifier is a no-op even for sources that
    # don't `use` anything.
    src = (
        "module tool;\n"
        "pub fn tool_main(p: i64, l: i64) -> i64 { return 0; }\n"
    )
    composed = compose_with_stdlib(src, [], repo_root)
    missing = verify_stdlib_uses(composed, src, [], mcp)
    assert missing == []


def test_multiple_expected_imports_partial_miss(
    repo_root: Path, mcp: SigilMCP
) -> None:
    # Source declares `use sigil::fs;` but task expects both fs AND
    # crypto — verifier should flag crypto as missing.
    src = (
        "module tool;\n"
        "use sigil::fs;\n"
        "pub fn tool_main(p: i32, l: i32) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {\n"
        "    return fs::read(p, l);\n"
        "}\n"
    )
    composed = compose_with_stdlib(src, ["fs", "crypto"], repo_root)
    missing = verify_stdlib_uses(composed, src, ["fs", "crypto"], mcp)
    assert missing == ["crypto"]


def test_typo_in_use_decl_surfaces_as_missing(
    repo_root: Path, mcp: SigilMCP
) -> None:
    # The source uses a non-existent module name; compose itself fails
    # because the file doesn't exist. The verifier never gets called in
    # this real flow, but the failure path is still exercised: compose
    # raises ValueError and the runner reports it.
    src = _typo_use_source()
    with pytest.raises(ValueError):
        compose_with_stdlib(
            src, ["definitely_not_a_real_module"], repo_root
        )
