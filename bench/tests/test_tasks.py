"""Verify the 5 task YAML specs parse, validate, and reference real source files."""

from __future__ import annotations

from pathlib import Path

import pytest

from sigil_bench.config import find_repo_root
from sigil_bench.tasks import Difficulty, TaskSpec, load_tasks


@pytest.fixture(scope="module")
def repo_root() -> Path:
    return find_repo_root()


@pytest.fixture(scope="module")
def tasks_dir(repo_root: Path) -> Path:
    return repo_root / "bench" / "tasks"


@pytest.fixture(scope="module")
def specs(tasks_dir: Path) -> list[TaskSpec]:
    return load_tasks(tasks_dir)


def test_loads_all_specs(specs):
    # The corpus was expanded to 24 tasks spanning compute / string / file-cap /
    # HTTP-effect / @Secret-taint for the agentic convergence experiment.
    # Update this list if you add another task.
    ids = sorted(s.id for s in specs)
    assert ids == [
        "task001_echo",
        "task002_reverse",
        "task004_uppercase",
        "task011_palindrome",
        "task015_ascii_sum",
        "task020_rot13",
        "task021_fibonacci",
        "task023_dec_to_hex",
        "task026_read_file",
        "task028_count_lines",
        "task029_count_lines_via_stdlib",
        "task032_sha256_hex",
        "task045_http_size_via_stdlib",
        "task061_json_field",
        "task085_eval_add_sub",
        "task101_secret_length",
        "task103_secret_mask",
        "task105_secret_xor_hex",
        "task121_secret_rot13",
        "task127_fs_sort_lines",
        "task129_fs_grep_error",
        "task151_http_size",
        "task152_http_lines",
        "task154_http_wc",
    ]


def test_source_paths_resolve(specs, repo_root):
    for spec in specs:
        path = spec.resolve_source(repo_root)
        assert path.is_file(), f"missing reference for {spec.id}: {path}"


def test_signatures_match_source_first_line(specs, repo_root):
    """Sanity: the spec's signature matches the actual source file's tool_main."""
    for spec in specs:
        src = spec.resolve_source(repo_root).read_text(encoding="utf-8")
        # The signature in the spec must appear verbatim in the source.
        assert spec.signature in src, (
            f"{spec.id}: signature mismatch.\n"
            f"  spec: {spec.signature}\n"
            f"  not found in {spec.source_path}"
        )


def test_difficulty_bands_cover_the_range(specs):
    bands = {s.difficulty for s in specs}
    assert Difficulty.TRIVIAL in bands
    assert Difficulty.BASIC in bands
    assert Difficulty.INTERMEDIATE in bands
    assert Difficulty.FFI_FS in bands
    assert Difficulty.FFI_NET in bands


def test_ffi_tasks_declare_attrs_and_effects(specs):
    """FFI tasks require ring+trusted attrs and FFI/Unsafe effects."""
    ffi_tasks = [s for s in specs if s.difficulty in (Difficulty.FFI_FS, Difficulty.FFI_NET)]
    assert ffi_tasks, "expected at least one FFI task"
    for spec in ffi_tasks:
        assert "#[ring(outer)]" in spec.required_attrs
        assert "#[trusted]" in spec.required_attrs
        assert "FFI" in spec.required_effects
        assert "Unsafe" in spec.required_effects


def test_each_task_has_at_least_one_input(specs):
    for spec in specs:
        assert spec.inputs, f"{spec.id} has no inputs"


def test_filter_by_id(tasks_dir):
    filtered = load_tasks(tasks_dir, only=["task001_echo"])
    assert len(filtered) == 1
    assert filtered[0].id == "task001_echo"


def test_filter_unknown_id_raises(tasks_dir):
    with pytest.raises(ValueError, match="not found"):
        load_tasks(tasks_dir, only=["task999_nope"])
