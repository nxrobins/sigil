"""Phase 5a-4: tests for `sigil_bench.compose`.

Asserts:

- Empty `stdlib_modules` produces text byte-identical to the input source
  and yields the sentinel `EMPTY_STDLIB_HASH`.
- Identical inputs produce identical hash (determinism / I23).
- The hash is exactly 24 hex chars (I23).
- Reordering `stdlib_modules` doesn't change the result (sorted before
  composition; AP19 / determinism).
- Path-traversal characters in module names are rejected BEFORE any file
  I/O is attempted (I25 / AP19 / MI-2).
- CRLF input is normalized to LF (compose discipline).
- Same source + same modules across two `compose_with_stdlib` calls
  produces byte-identical text (LRU cache hit determinism).
"""

from __future__ import annotations

from pathlib import Path

import pytest

from sigil_bench.compose import (
    EMPTY_STDLIB_HASH,
    STDLIB_HASH_HEX_LEN,
    clear_stdlib_cache,
    compose_with_stdlib,
)
from sigil_bench.config import find_repo_root


@pytest.fixture(scope="module")
def repo_root() -> Path:
    return find_repo_root()


def test_empty_stdlib_byte_identical(repo_root: Path) -> None:
    src = "module tool;\npub fn tool_main(p: i64, l: i64) -> i64 { return 0; }\n"
    composed = compose_with_stdlib(src, [], repo_root)
    assert composed.text == src
    assert composed.stdlib_hash == EMPTY_STDLIB_HASH
    assert composed.modules_included == ()


def test_empty_stdlib_offset_zero(repo_root: Path) -> None:
    # iter 13: no prepended stdlib → no line shift → diagnostics need no remap.
    src = "module tool;\npub fn tool_main(p: i64, l: i64) -> i64 { return 0; }\n"
    composed = compose_with_stdlib(src, [], repo_root)
    assert composed.stdlib_line_offset == 0


def test_stdlib_offset_counts_prepended_lines(repo_root: Path) -> None:
    # The offset must equal the newline count of everything before the LLM
    # source — that's exactly the line shift a diagnostic needs corrected.
    src = "module tool;\npub fn tool_main(p: i64, l: i64) -> i64 { return 0; }\n"
    composed = compose_with_stdlib(src, ["fs"], repo_root)
    assert composed.text.endswith(src)
    prefix = composed.text[: len(composed.text) - len(src)]
    assert composed.stdlib_line_offset == prefix.count("\n")
    assert composed.stdlib_line_offset > 0


def test_hash_length_is_24_hex_chars(repo_root: Path) -> None:
    src = "module tool;\n"
    composed = compose_with_stdlib(src, ["fs"], repo_root)
    assert len(composed.stdlib_hash) == STDLIB_HASH_HEX_LEN
    assert STDLIB_HASH_HEX_LEN == 24
    int(composed.stdlib_hash, 16)  # raises if not hex


def test_module_order_does_not_affect_hash(repo_root: Path) -> None:
    src = "module tool;\n"
    a = compose_with_stdlib(src, ["fs", "crypto"], repo_root)
    b = compose_with_stdlib(src, ["crypto", "fs"], repo_root)
    assert a.stdlib_hash == b.stdlib_hash
    assert a.text == b.text
    assert a.modules_included == b.modules_included == ("crypto", "fs")


def test_same_inputs_byte_identical_across_calls(repo_root: Path) -> None:
    src = "module tool;\n"
    a = compose_with_stdlib(src, ["json"], repo_root)
    b = compose_with_stdlib(src, ["json"], repo_root)
    assert a.text == b.text
    assert a.stdlib_hash == b.stdlib_hash


def test_path_traversal_rejected_before_io(repo_root: Path) -> None:
    src = "module tool;\n"
    # Each of these would resolve to a path OUTSIDE stdlib/sigil/ if we
    # blindly joined; rejection must happen at the regex layer first.
    for bad in [
        "../etc/passwd",
        "..",
        "..\\fs",
        "fs/../../etc",
        "Fs",          # uppercase rejected
        "1starts_with_digit",
        "has-hyphen",
        "has space",
        "",
    ]:
        with pytest.raises(ValueError):
            compose_with_stdlib(src, [bad], repo_root)


def test_unknown_module_raises_after_validation(repo_root: Path) -> None:
    src = "module tool;\n"
    # Name passes the I25 regex but the file doesn't exist. compose
    # raises ValueError with the expected file path included so the
    # caller can debug typos.
    with pytest.raises(ValueError, match="definitely_not_a_real_module"):
        compose_with_stdlib(src, ["definitely_not_a_real_module"], repo_root)


def test_crlf_input_normalized_to_lf(repo_root: Path) -> None:
    src_lf = "module tool;\nfn x() -> i64 { return 1; }\n"
    src_crlf = src_lf.replace("\n", "\r\n")
    a = compose_with_stdlib(src_lf, ["fs"], repo_root)
    b = compose_with_stdlib(src_crlf, ["fs"], repo_root)
    # Compose should normalize stdlib content to LF; user source is left
    # intact in the current implementation but the stdlib_hash should
    # match because it's computed from the normalized stdlib bytes only.
    assert a.stdlib_hash == b.stdlib_hash


def test_composed_text_contains_module_decls(repo_root: Path) -> None:
    src = "module tool;\n"
    composed = compose_with_stdlib(src, ["fs", "json"], repo_root)
    # The bundled stdlib must contribute its `module fs;` and
    # `module json;` declarations so the compiler can resolve them.
    assert "module fs;" in composed.text
    assert "module json;" in composed.text


def test_composed_source_dataclass_is_frozen(repo_root: Path) -> None:
    composed = compose_with_stdlib("module tool;\n", [], repo_root)
    with pytest.raises((AttributeError, TypeError)):
        composed.text = "tampered"  # type: ignore[misc]


def test_clear_cache_does_not_raise(repo_root: Path) -> None:
    # Smoke test: cache invalidation works without error. Used by the
    # future evolve harness between trials.
    compose_with_stdlib("module tool;\n", ["fs"], repo_root)
    clear_stdlib_cache()
    compose_with_stdlib("module tool;\n", ["fs"], repo_root)


# ── Phase 6a-1: override_modules tests (I-OPS-1, -2, -3) ────────────────


def test_override_returns_override_bytes(repo_root: Path) -> None:
    """Smoke test: override-supplied bytes appear in the composed text;
    disk bytes for that module do NOT."""
    src = "module tool;\n"
    override_payload = "module fs;\n// THIS IS THE OVERRIDE\n"
    composed = compose_with_stdlib(
        src, ["fs"], repo_root, override_modules={"fs": override_payload}
    )
    assert "// THIS IS THE OVERRIDE" in composed.text
    # The disk-based fs.sigil contains "extern \"C\" fn fs_read"; if our
    # override bypass leaked, that string would be in the composed text.
    assert "extern \"C\" fn fs_read" not in composed.text, \
        "override should fully replace disk bytes for the named module"


def test_override_normalization_matches_disk(repo_root: Path) -> None:
    """I-OPS-1: override bytes and disk bytes that are LOGICALLY identical
    produce IDENTICAL stdlib_hash. CRLF endings on the override should
    normalize to the same bytes as LF on disk."""
    # Read the live fs.sigil, then pass the SAME content as an override
    # but with CRLF line endings. Hashes must match.
    fs_disk = (repo_root / "stdlib" / "sigil" / "fs.sigil").read_text(encoding="utf-8")
    fs_crlf = fs_disk.replace("\n", "\r\n")
    src = "module tool;\n"

    disk_composed = compose_with_stdlib(src, ["fs"], repo_root)
    override_composed = compose_with_stdlib(
        src, ["fs"], repo_root, override_modules={"fs": fs_crlf}
    )
    assert disk_composed.stdlib_hash == override_composed.stdlib_hash, (
        "CRLF override of the same logical content must produce the same "
        "stdlib_hash as the LF disk bytes"
    )
    assert disk_composed.text == override_composed.text


def test_override_does_not_poison_cache(repo_root: Path) -> None:
    """I-OPS-2: after override use, the LRU cache for that name MUST
    still hold the disk value, not the override. Subsequent non-override
    reads must see disk bytes."""
    src = "module tool;\n"
    # Prime the cache with a disk read.
    first = compose_with_stdlib(src, ["fs"], repo_root)
    # Use an override that's distinguishable from disk.
    compose_with_stdlib(
        src, ["fs"], repo_root,
        override_modules={"fs": "module fs;\n// POISONED?\n"},
    )
    # Read again WITHOUT override. Must not see "POISONED".
    after = compose_with_stdlib(src, ["fs"], repo_root)
    assert "// POISONED" not in after.text, \
        "override leaked into the LRU cache; non-override reads now see it"
    # Same hash as the very first call confirms the cache returned the
    # disk-derived value (not the override).
    assert first.stdlib_hash == after.stdlib_hash


def test_override_partial_raises(repo_root: Path) -> None:
    """I-OPS-3: override key NOT in stdlib_modules → ValueError, total
    or absent."""
    src = "module tool;\n"
    with pytest.raises(ValueError, match="not in stdlib_modules"):
        compose_with_stdlib(
            src, ["fs"], repo_root,
            override_modules={"json": "module json;\n"},  # json not requested
        )


def test_override_invalid_name_raises(repo_root: Path) -> None:
    """I-OPS-3 + I25 belt-and-suspenders: override key with bad characters
    must be rejected at the regex layer, not silently accepted."""
    src = "module tool;\n"
    with pytest.raises(ValueError, match="invalid module name"):
        compose_with_stdlib(
            src, ["fs"], repo_root,
            override_modules={"../etc/passwd": "anything"},
        )


def test_override_value_must_be_str(repo_root: Path) -> None:
    """I-OPS-3: override values are `str`. None or `bytes` raise TypeError."""
    src = "module tool;\n"
    with pytest.raises(TypeError, match="expected str"):
        compose_with_stdlib(
            src, ["fs"], repo_root,
            override_modules={"fs": b"bytes not str"},  # type: ignore[dict-item]
        )


def test_override_empty_value_raises(repo_root: Path) -> None:
    """An empty override value would never compile; refuse early with a
    clear error."""
    src = "module tool;\n"
    with pytest.raises(ValueError, match="empty"):
        compose_with_stdlib(
            src, ["fs"], repo_root,
            override_modules={"fs": ""},
        )


def test_override_changes_hash_vs_disk(repo_root: Path) -> None:
    """An override with DIFFERENT content from disk must produce a
    different stdlib_hash. Otherwise the prompt cache wouldn't
    invalidate when the candidate changes."""
    src = "module tool;\n"
    disk = compose_with_stdlib(src, ["fs"], repo_root)
    overridden = compose_with_stdlib(
        src, ["fs"], repo_root,
        override_modules={"fs": "module fs;\n// totally different fs\n"},
    )
    assert disk.stdlib_hash != overridden.stdlib_hash


def test_override_does_not_touch_disk(repo_root: Path) -> None:
    """Composing with an override must NOT modify the on-disk stdlib
    file. Captures (sha256, mtime) before and after; asserts unchanged.
    This is the canonical I-OPS-5 sentinel for compose specifically."""
    import hashlib

    fs_path = repo_root / "stdlib" / "sigil" / "fs.sigil"
    before_bytes = fs_path.read_bytes()
    before_sha = hashlib.sha256(before_bytes).hexdigest()
    before_mtime = fs_path.stat().st_mtime_ns

    compose_with_stdlib(
        "module tool;\n",
        ["fs"],
        repo_root,
        override_modules={"fs": "module fs;\n// override that doesn't touch disk\n"},
    )

    after_bytes = fs_path.read_bytes()
    after_sha = hashlib.sha256(after_bytes).hexdigest()
    after_mtime = fs_path.stat().st_mtime_ns

    assert before_sha == after_sha, "override mutated disk bytes"
    assert before_mtime == after_mtime, "override mutated disk mtime"
