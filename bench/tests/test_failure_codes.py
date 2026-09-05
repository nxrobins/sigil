"""Phase 6a-2 / I-OPS-17: structured failure_codes shape + migration.

The pre-6a-2 shape was `list[str]`; the new shape is
`list[{"code": str, "detail": str}]`. The migration auto-upgrades old
entries via a Pydantic field validator.

Tests pin:
- Bare strings auto-migrate (legacy data round-trips).
- Embedded `:` in `code` field is rejected (the parser hazard the
  spec called out in AP-OPS-14).
- `extract_codes` returns the structured shape with diagnostic
  message in `detail`.
- `STDLIB_MISSING` surfaces with comma-joined sorted module names
  in `detail`, never as `STDLIB_MISSING:fs,json` in the code field.
"""

from __future__ import annotations

import pytest

from sigil_bench.runner import (
    Attempt,
    TaskResult,
    _normalize_failure_code_entry,
    extract_codes,
)

# ── extract_codes ───────────────────────────────────────────────────────


def test_extract_codes_returns_structured_shape() -> None:
    envelope = {
        "status": "error",
        "diagnostics": [
            {"code": "T060", "message": "undefined local `x`"},
            {"code": "R001", "message": "missing #[trusted]"},
        ],
    }
    out = extract_codes(envelope)
    assert out == [
        {"code": "T060", "detail": "undefined local `x`"},
        {"code": "R001", "detail": "missing #[trusted]"},
    ]


def test_extract_codes_skips_diagnostics_without_code() -> None:
    envelope = {
        "status": "error",
        "diagnostics": [
            {"code": "T060", "message": "ok"},
            {"message": "no code field"},
            "not a dict",
        ],
    }
    out = extract_codes(envelope)
    assert len(out) == 1
    assert out[0]["code"] == "T060"


def test_extract_codes_empty_for_ok_envelope() -> None:
    assert extract_codes({"status": "ok"}) == []


# ── Migration via field_validator ───────────────────────────────────────


def test_legacy_string_failure_codes_migrate() -> None:
    """An old transcript with `failure_codes: ["T060", "T070"]` must
    load cleanly into the new schema."""
    a = Attempt(
        attempt_no=1,
        source="x",
        check_envelope={},
        failure_codes=["T060", "T070"],  # type: ignore[arg-type]
    )
    assert a.failure_codes == [
        {"code": "T060", "detail": ""},
        {"code": "T070", "detail": ""},
    ]


def test_mixed_dict_and_string_entries_migrate() -> None:
    """Forward-compatible: dicts pass through, strings auto-upgrade."""
    a = Attempt(
        attempt_no=1,
        source="x",
        check_envelope={},
        failure_codes=[
            "T060",
            {"code": "STDLIB_MISSING", "detail": "fs,json"},
            {"code": "R001"},  # detail defaults to ""
        ],  # type: ignore[arg-type]
    )
    codes = [e["code"] for e in a.failure_codes]
    assert codes == ["T060", "STDLIB_MISSING", "R001"]
    details = [e["detail"] for e in a.failure_codes]
    assert details == ["", "fs,json", ""]


def test_embedded_colon_in_code_rejected() -> None:
    """AP-OPS-14: `STDLIB_MISSING:fs,json` as a `code` field would
    reintroduce the embedded-delimiter parser hazard. Rejected at
    validation."""
    with pytest.raises((ValueError, Exception)):
        _normalize_failure_code_entry({"code": "STDLIB_MISSING:fs,json"})


def test_bad_entry_shape_raises() -> None:
    with pytest.raises(ValueError):
        _normalize_failure_code_entry(123)
    with pytest.raises(ValueError):
        _normalize_failure_code_entry({"detail": "no code field"})


# ── TaskResult round-trip ───────────────────────────────────────────────


def test_task_result_legacy_failure_codes_round_trip() -> None:
    """A TaskResult constructed with legacy `list[str]` must serialize
    out as the structured shape (post-migration)."""
    r = TaskResult(
        task_id="t1",
        passed=False,
        reason="exhausted_attempts",
        attempts_used=3,
        failure_codes=["T060", "R001"],  # type: ignore[arg-type]
    )
    dumped = r.model_dump()
    assert dumped["failure_codes"] == [
        {"code": "T060", "detail": ""},
        {"code": "R001", "detail": ""},
    ]
