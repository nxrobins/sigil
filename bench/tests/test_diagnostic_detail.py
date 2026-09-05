"""Unit tests for the A/B diagnostic rendering (diagnostics-axes a9 + the
suggested_edits/redundancy experiment).

Pure functions — no MCP binary — so these run in CI unconditionally. They pin
the ritual constraints on the rendering:
  E1  `bare` and `full` show the SAME diagnostic set; only verbosity differs.
  C3  suggested_edits render by edit TYPE + replacement text (insert vs use),
      NEVER by slicing the agent source or surfacing byte offsets (the offsets
      are composed-space on stdlib tasks, so a slice would garble the text).
  edits The suggested_edits fix line is its own A/B variable: `include_
      suggested_edits=False` suppresses it even in full mode.
"""

from __future__ import annotations

import re

from sigil_bench.generator import (
    _build_user_message,
    _format_diagnostic,
    _render_suggested_edits,
)
from sigil_bench.tasks import Difficulty, TaskInput, TaskSpec


def _diag(**kw):
    base = {
        "code": "T060",
        "title": "undefined local",
        "message": "cannot find value `fule` in this scope",
        "hint": "did you mean `fuel`?",
        "location": {"line": 1, "column": 12},
    }
    base.update(kw)
    return base


def _task() -> TaskSpec:
    return TaskSpec(
        id="t",
        source_path="unused.sigil",
        difficulty=Difficulty.TRIVIAL,
        description="d",
        signature="pub fn tool_main(input_ptr: i64, input_len: i64) -> i64",
        inputs=[TaskInput(name="x", value="")],
        expected_output_strategy="literal",
        expected_outputs={"x": ""},
        fuel_budget=100_000,
    )


# ── render forms (C3): by type + replacement, never sliced source ─────────


def test_render_replace_form():
    # A non-empty span is a replacement → "use `<new>`" (the corrected text).
    edit = {"start": 0, "end": 4, "replacement": "fuel"}
    assert _render_suggested_edits({"suggested_edits": [edit]}) == ["  fix: use `fuel`"]


def test_render_insert_form():
    # An empty span (start == end) is a pure insertion → "insert `<new>`".
    edit = {"start": 7, "end": 7, "replacement": ";"}
    assert _render_suggested_edits({"suggested_edits": [edit]}) == ["  fix: insert `;`"]


def test_render_never_slices_source():
    # Even a wildly out-of-range offset renders fine — we never index source.
    edit = {"start": 9999, "end": 9999, "replacement": "}"}
    assert _render_suggested_edits({"suggested_edits": [edit]}) == ["  fix: insert `}`"]


# ── detail variable (a9): bare vs full ────────────────────────────────────


def test_bare_is_code_and_message_only():
    d = _diag(suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}])
    out = _format_diagnostic(d, detail="bare")
    assert out == "[T060]: cannot find value `fule` in this scope"
    assert "undefined local" not in out  # no title
    assert "hint" not in out
    assert "fix" not in out
    assert "line 1" not in out  # no location


def test_full_carries_the_envelope():
    d = _diag(suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}])
    out = _format_diagnostic(d, detail="full")
    assert "undefined local" in out
    assert "@ line 1, col 12" in out
    assert "hint: did you mean `fuel`?" in out
    assert "fix: use `fuel`" in out


def test_e2_no_byte_offsets_leak():
    d = _diag(suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}])
    out = _format_diagnostic(d, detail="full")
    assert not re.search(r"\[\d+\s*,\s*\d+", out), out  # no `[s,e)` token
    assert not re.search(r"\b\d+\.\.\d+\b", out), out  # no `s..e` token
    assert not re.search(r"\bbytes?\b\s*\d", out), out  # no "byte N"


# ── edits variable (the redundancy experiment): off vs on ─────────────────


def test_full_edits_off_omits_fix_line():
    d = _diag(suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}])
    out = _format_diagnostic(d, detail="full", include_suggested_edits=False)
    # Everything else of the envelope survives — ONLY the fix line is gone.
    assert "undefined local" in out
    assert "hint:" in out
    assert "fix:" not in out


def test_full_edits_on_includes_fix_line():
    d = _diag(suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}])
    out = _format_diagnostic(d, detail="full", include_suggested_edits=True)
    assert "fix: use `fuel`" in out


def test_build_user_message_edits_toggle():
    diag = _diag(suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}])
    transcript = [
        {
            "attempt_no": 1,
            "source": "fule = 1;",
            "check_envelope": {"status": "error", "diagnostics": [diag]},
            "failure_codes": [{"code": "T060", "detail": ""}],
        }
    ]
    on = _build_user_message(_task(), transcript, detail="full", include_suggested_edits=True)
    off = _build_user_message(_task(), transcript, detail="full", include_suggested_edits=False)
    # The edits-off arm is identical EXCEPT the fix line — same diagnostic set,
    # same hint, same everything else (C2: a single variable).
    assert "fix:" in on
    assert "fix:" not in off
    assert "T060" in on and "T060" in off
    assert "hint:" in on and "hint:" in off


# ── line-offset remap (iter 13) ───────────────────────────────────────────


def test_line_offset_remaps_to_source_coordinates():
    # iter 13: composed line 850 with 840 prepended stdlib lines → the agent
    # sees its own line 10, never the composed-space 850.
    d = _diag(location={"line": 850, "column": 5}, suggested_edits=None)
    out = _format_diagnostic(d, detail="full", line_offset=840)
    assert "@ line 10, col 5" in out
    assert "850" not in out


def test_line_offset_zero_unchanged():
    d = _diag(location={"line": 12, "column": 3}, suggested_edits=None)
    out = _format_diagnostic(d, detail="full", line_offset=0)
    assert "@ line 12, col 3" in out


def test_error_in_stdlib_region_omits_location():
    # Composed line 5 but stdlib occupies 840 lines → the error is inside the
    # prepended stdlib, not the agent's code; show no (misleading) line number.
    d = _diag(location={"line": 5, "column": 1}, suggested_edits=None)
    out = _format_diagnostic(d, detail="full", line_offset=840)
    assert "@ line" not in out
    assert out.startswith("[T060]")  # still rendered, just without a location


# ── E1: same diagnostic set in both detail modes ──────────────────────────


def test_e1_same_diagnostic_set_both_modes():
    diags = [
        _diag(code="T060", suggested_edits=[{"start": 0, "end": 4, "replacement": "fuel"}]),
        _diag(code="T001", title="type mismatch", message="i64 vs str", hint=None,
              suggested_edits=None),
    ]
    transcript = [
        {
            "attempt_no": 1,
            "source": "fule = 1;",
            "check_envelope": {"status": "error", "diagnostics": diags},
            "failure_codes": [{"code": "T060", "detail": ""}],
        }
    ]
    bare = _build_user_message(_task(), transcript, detail="bare")
    full = _build_user_message(_task(), transcript, detail="full")
    # Same diagnostic SET, same ORDER, in both modes.
    for code in ("T060", "T001"):
        assert code in bare and code in full
    assert bare.index("T060") < bare.index("T001")
    assert full.index("T060") < full.index("T001")
    # Only verbosity differs: the envelope extras are full-only.
    assert "hint:" not in bare and "fix:" not in bare
    assert "hint:" in full and "fix:" in full
