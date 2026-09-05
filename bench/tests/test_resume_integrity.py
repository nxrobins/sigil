"""Phase 5a-4 / I24: tests for transcript-integrity validation.

`--resume` must reject:

1. transcripts written by a different `run_id` (cross-run reuse)
2. transcripts written under a different schema_version
3. transcripts whose body bytes differ from the recorded sha256
4. legacy transcripts (no header line at all)
5. truncated transcripts (no trailing newline)

A regex / `head -1` style verifier would miss most of these — the
sha256 over the body is the load-bearing check.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from sigil_bench.runner import Attempt, ForgeOutcome, TaskResult
from sigil_bench.scoring import (
    TRANSCRIPT_SCHEMA_VERSION,
    TranscriptIntegrityError,
    transcript_exists,
    validate_transcript_integrity,
    write_transcript,
)


def _make_result(task_id: str = "task001_echo") -> TaskResult:
    return TaskResult(
        task_id=task_id,
        passed=True,
        reason="passed",
        attempts_used=1,
        attempts=[
            Attempt(
                attempt_no=1,
                source="module tool;\npub fn tool_main() -> i64 { return 0; }\n",
                check_envelope={
                    "command": "check",
                    "status": "ok",
                    "schema_version": 2,
                    "data": {},
                },
            )
        ],
        forge_results=[
            ForgeOutcome(
                input_name="x",
                passed=True,
                output_text="x",
                expected_output="x",
                forge_envelope={
                    "command": "forge",
                    "status": "ok",
                    "schema_version": 2,
                    "data": {"output_text": "x"},
                },
            )
        ],
        total_fuel_consumed=10,
    )


def test_round_trip_validates(tmp_path: Path) -> None:
    result = _make_result()
    run_id = "abcd1234" * 4  # 32 hex chars
    write_transcript(result, tmp_path, run_id)
    # Should validate cleanly.
    validate_transcript_integrity(result.task_id, tmp_path, run_id)


def test_missing_file_raises(tmp_path: Path) -> None:
    with pytest.raises(TranscriptIntegrityError, match="missing"):
        validate_transcript_integrity("task001_echo", tmp_path, "anything")


def test_different_run_id_rejected(tmp_path: Path) -> None:
    result = _make_result()
    write_transcript(result, tmp_path, "original_run_id_aaa")
    with pytest.raises(TranscriptIntegrityError, match="written by run"):
        validate_transcript_integrity(
            result.task_id, tmp_path, "different_run_id_bbb"
        )


def test_mutated_body_rejected(tmp_path: Path) -> None:
    result = _make_result()
    run_id = "fedc0987" * 4
    path = write_transcript(result, tmp_path, run_id)
    # Flip a single byte in the BODY (not the header). We choose a byte
    # somewhere in the middle of the second line so we don't accidentally
    # break JSON parsing — we only need the body sha256 to mismatch.
    raw = path.read_text(encoding="utf-8")
    lines = raw.split("\n")
    assert len(lines) >= 3, "expect header + at least one body line + summary"
    # Mutate the very last character of the second line — the attempt
    # JSON closes with `}`. Replace with a different character.
    second = lines[1]
    if second.endswith("}"):
        lines[1] = second[:-1] + "X"
    else:
        # Failsafe: append a benign character.
        lines[1] = second + "X"
    path.write_text("\n".join(lines), encoding="utf-8")
    # Tampered file may not end with newline — re-add to keep the
    # truncation check from masking the sha256 mismatch.
    if not path.read_text(encoding="utf-8").endswith("\n"):
        with path.open("a", encoding="utf-8") as f:
            f.write("\n")
    with pytest.raises(TranscriptIntegrityError, match="integrity hash mismatch"):
        validate_transcript_integrity(result.task_id, tmp_path, run_id)


def test_header_field_tampered_rejected(tmp_path: Path) -> None:
    """Phase 6a-2 / I-OPS-16 / AP-OPS-13: tampering with the HEADER
    (not the body) must be rejected. Pre-fix the body-only sha256
    silently accepted run_id swaps. Zeroed-field protocol catches it.
    """
    result = _make_result()
    run_id_original = "AAAA" * 8
    path = write_transcript(result, tmp_path, run_id_original)

    # Read the file, swap the run_id field in the header (preserving
    # the original transcript_sha256), write back.
    raw = path.read_text(encoding="utf-8")
    lines = raw.splitlines()
    header = json.loads(lines[0])
    # Tamper: swap created_by_run_id without changing the hash field.
    header["created_by_run_id"] = "BBBB" * 8
    lines[0] = json.dumps(header, separators=(",", ":"), sort_keys=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    # The validator should reject because the recomputed hash (over the
    # tampered header) won't match the claimed hash. Note: validation
    # call uses the TAMPERED run_id so the run-id-mismatch check
    # would fire FIRST — we need to use the tampered id for the call.
    with pytest.raises(TranscriptIntegrityError, match="integrity hash mismatch"):
        validate_transcript_integrity("task001_echo", tmp_path, "BBBB" * 8)


def test_legacy_no_header_rejected(tmp_path: Path) -> None:
    # Simulate a transcript from a pre-5a-4 run: just the body lines,
    # no header. Resume must refuse rather than silently treat the first
    # body line as the header.
    path = tmp_path / "task001_echo.jsonl"
    path.write_text(
        json.dumps({"kind": "summary", "task_id": "task001_echo", "passed": True})
        + "\n",
        encoding="utf-8",
    )
    with pytest.raises(TranscriptIntegrityError, match="not a header"):
        validate_transcript_integrity("task001_echo", tmp_path, "anyrun")


def test_truncated_no_trailing_newline_rejected(tmp_path: Path) -> None:
    result = _make_result()
    run_id = "runrunrun" * 3 + "abc"
    path = write_transcript(result, tmp_path, run_id)
    # Strip the trailing newline. Without it we can't tell whether the
    # last line was fully written, so the integrity check must refuse.
    raw = path.read_text(encoding="utf-8")
    assert raw.endswith("\n")
    path.write_text(raw[:-1], encoding="utf-8")
    with pytest.raises(TranscriptIntegrityError, match="trailing newline"):
        validate_transcript_integrity(result.task_id, tmp_path, run_id)


def test_schema_version_mismatch_rejected(tmp_path: Path) -> None:
    # Hand-craft a transcript with the wrong schema_version. The
    # validator must refuse rather than process unknown-version data.
    body_lines = [
        json.dumps({"kind": "summary", "task_id": "x", "passed": True}),
    ]
    import hashlib

    body = "\n".join(body_lines) + "\n"
    sha = hashlib.sha256(body.encode("utf-8")).hexdigest()
    header = json.dumps(
        {
            "kind": "header",
            "schema_version": TRANSCRIPT_SCHEMA_VERSION + 99,
            "created_by_run_id": "rid",
            "transcript_sha256": sha,
        }
    )
    path = tmp_path / "x.jsonl"
    path.write_text(header + "\n" + body, encoding="utf-8")
    with pytest.raises(TranscriptIntegrityError, match="schema_version"):
        validate_transcript_integrity("x", tmp_path, "rid")


def test_transcript_exists_doesnt_validate(tmp_path: Path) -> None:
    # `transcript_exists` is just a file-presence check. Validation is
    # the caller's job — verify that the existence check doesn't raise
    # even on a tampered file.
    path = tmp_path / "task001_echo.jsonl"
    path.write_text("garbage but file exists\n", encoding="utf-8")
    assert transcript_exists("task001_echo", tmp_path) is True
    # And validation does raise on the same file.
    with pytest.raises(TranscriptIntegrityError):
        validate_transcript_integrity("task001_echo", tmp_path, "anyrun")
