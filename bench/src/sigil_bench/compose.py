"""Phase 5a-4 + 6a-1: stdlib composition for the bench harness.

`compose_with_stdlib(source, stdlib_modules, repo_root, override_modules=None)`
reads the requested stdlib modules (or substitutes overrides for them),
normalizes their content, and concatenates with the LLM-generated source
into a single compilation unit suitable for `sigil_check` / `sigil_forge`.

Discipline (per spec invariants and anti-patterns):

- **I25 / AP19:** module names are validated against
  `^[a-z_][a-z0-9_]*$` BEFORE any file I/O. Path-traversal characters
  never reach `Path` operations. (Validation also happens in
  `tasks.py` at task-load time; this is the second-line defense.)
- **I23:** `stdlib_hash` is SHA-256 of the concatenated, normalized
  stdlib bytes, truncated to 24 hex chars (96 bits). Used as the
  prompt-cache key suffix in `AnthropicGenerator` so any stdlib edit
  invalidates the cache cleanly.
- **AP2:** the compose is deterministic: read each module once per
  process (cached by path), normalize line endings to LF, strip
  trailing whitespace per line, sort `stdlib_modules` to deduplicate
  and produce identical output regardless of the order in which the
  task spec listed them.
- **State perimeter (Op C "Footgun"):** the LRU file-read cache lives
  for the lifetime of the bench process. Caller is responsible for
  invalidating it (see `clear_stdlib_cache`) when stdlib content
  changes mid-run — relevant for the future evolve harness, not for
  one-shot bench runs.

## Phase 6a-1: per-trial isolation via `override_modules`

The evolve fitness path used to physically swap `stdlib/sigil/<module>.sigil`
on disk before each trial, then restore. That mechanism produced the
`.evolve_backup` orphan family (concurrent process races, mid-trial-kill
poisoning the live stdlib, gitignore hiding the corruption). PR 6a-1
replaces it with `override_modules`: an in-memory `dict[name -> source]`
that compose substitutes for the disk read.

Spec invariants honored here:

- **I-OPS-1**: override bytes and disk bytes that are logically identical
  produce IDENTICAL normalized output AND IDENTICAL `stdlib_hash`. Both
  paths flow through `_normalize_module_source` so CRLF vs LF, trailing
  whitespace, etc. are flattened uniformly.
- **I-OPS-2**: the LRU cache is BYPASSED on both lookup AND write for any
  name in `override_modules`. The cached value (if any) is untouched;
  subsequent non-override reads see the disk value, not the override.
- **I-OPS-3**: `override_modules` is total or absent — never partial. A
  key not in the requested `stdlib_modules` set raises `ValueError`.
  Each value MUST be a non-empty `str`; `None` or `bytes` raise `TypeError`.
- **I-OPS-4**: every `compose_with_stdlib` call site inside the bench
  package accepts and forwards `override_modules`. Enforced by
  `lint_compose_callers.py`, the compose-caller lint.
- **I-OPS-5**: this module never writes to `stdlib/sigil/*` — and never
  did, but documenting it here so future code knows the constraint.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

# Phase 5a-4 / I25: bare module name pattern. Defensive duplication of
# the same regex in tasks.py — both call sites guard the same invariant
# but at different layers (task-load vs compose).
_MODULE_NAME_RE = re.compile(r"^[a-z_][a-z0-9_]*$")

# Phase 5a-4 / I23: hash truncation length in hex chars. 24 hex = 96
# bits — collision-resistant for the projected scale (50 stdlib
# variations × 1000 task invocations). Constants are exposed so tests
# can assert the value without re-importing module internals.
STDLIB_HASH_HEX_LEN: int = 24

# Sentinel value for the empty-stdlib case — keeps prompt-cache keys
# distinct from "stdlib was requested with one module that happened to
# hash to zero bytes" (which can't actually happen but be precise).
EMPTY_STDLIB_HASH: str = "0" * STDLIB_HASH_HEX_LEN


@dataclass(frozen=True)
class ComposedSource:
    """Result of composing stdlib + LLM source. The `text` is what gets
    sent to `sigil_check`/`sigil_forge`; `stdlib_hash` is the cache-key
    suffix the generator uses. `modules_included` is the deduped sorted
    list — useful for diagnostics.

    `stdlib_line_offset` is how many lines the prepended stdlib blob adds
    ahead of the LLM source. `sigil_check` reports diagnostic line numbers
    in COMPOSED coordinates, but the agent only ever sees its own source —
    so a diagnostic's source-space line is `composed_line - stdlib_line_offset`.
    Without this remap a stdlib-task error reads as `@ line 847` for code the
    agent thinks starts at line 1 (diagnostics-axes a9 iter 13)."""

    text: str
    stdlib_hash: str
    modules_included: tuple[str, ...]
    stdlib_line_offset: int = 0


def _normalize_module_source(raw: str) -> str:
    """Apply the canonical normalization to a module's source bytes:
    LF line endings, per-line trailing-whitespace strip, ensure trailing
    newline. Pure function; deterministic. Used for BOTH disk reads and
    overrides so I-OPS-1 holds — same logical bytes produce same
    normalized output regardless of source."""
    lines = raw.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    normalized = "\n".join(line.rstrip() for line in lines)
    if not normalized.endswith("\n"):
        normalized = normalized + "\n"
    return normalized


@lru_cache(maxsize=64)
def _read_normalized_module(stdlib_dir_str: str, module_name: str) -> str:
    """Read `stdlib/sigil/<module>.sigil` and normalize. Cached per process
    by (stdlib_dir, module_name).

    Both arguments are strings (not `Path`) so `lru_cache` can hash them
    without surprises across platforms.

    I-OPS-2 / AP-OPS-3 note: callers using `override_modules` MUST NOT
    invoke this function for an overridden name. The cache must remain
    populated with disk-derived values only; otherwise an override could
    poison the cache for subsequent non-override reads. The bypass is
    enforced in `compose_with_stdlib`'s loop, not here.
    """
    stdlib_dir = Path(stdlib_dir_str)
    path = stdlib_dir / f"{module_name}.sigil"
    return _normalize_module_source(path.read_text(encoding="utf-8"))


def clear_stdlib_cache() -> None:
    """Drop the per-process stdlib read cache. The future evolve harness
    will call this between trials when the candidate stdlib changes
    on disk; one-shot bench runs don't need to call it."""
    _read_normalized_module.cache_clear()


def compose_with_stdlib(
    source: str,
    stdlib_modules: list[str],
    repo_root: Path,
    *,
    override_modules: dict[str, str] | None = None,
) -> ComposedSource:
    """Compose the LLM-generated `source` with the requested stdlib
    modules. Returns a `ComposedSource` carrying the final text plus a
    `stdlib_hash` suitable for prompt-cache invalidation.

    Args:
        source: LLM-generated `.sigil` source (or hand-written tool source).
        stdlib_modules: bare module names (e.g. `["fs", "json"]`).
            Empty list → no stdlib appended; `stdlib_hash` is the
            sentinel `EMPTY_STDLIB_HASH`.
        repo_root: workspace root containing `stdlib/sigil/`.
        override_modules: optional mapping `{name -> source}` substituted
            for the disk read. Used by the evolve fitness path to evaluate
            candidates without mutating the live stdlib. Per I-OPS-3:
            every key MUST be present in `stdlib_modules`; partial
            overrides raise `ValueError`. Per I-OPS-1: the override
            value flows through the same normalization as the disk path,
            so byte-identical inputs produce byte-identical hashes
            regardless of source.

    Raises:
        ValueError: invalid module name (I25 regex); module file not found
            on disk and not in overrides; `override_modules` contains a key
            outside `stdlib_modules` (I-OPS-3).
        TypeError: `override_modules` value is None or not a `str` (I-OPS-3).
    """
    # Defensive validation — task-load already checks, but compose is
    # also called by future code paths that may not go through TaskSpec.
    for entry in stdlib_modules:
        if not _MODULE_NAME_RE.fullmatch(entry):
            raise ValueError(
                f"compose_with_stdlib: invalid module name `{entry}` — "
                "must match ^[a-z_][a-z0-9_]*$ (path-traversal-safe)"
            )

    # I-OPS-3: total or absent, never partial.
    overrides: dict[str, str] = override_modules or {}
    requested_set = set(stdlib_modules)
    for name, value in overrides.items():
        if not _MODULE_NAME_RE.fullmatch(name):
            raise ValueError(
                f"compose_with_stdlib: override key `{name}` is an invalid "
                "module name (must match ^[a-z_][a-z0-9_]*$)"
            )
        if name not in requested_set:
            raise ValueError(
                f"compose_with_stdlib: override key `{name}` is not in "
                f"stdlib_modules ({sorted(requested_set)}); overrides must "
                "be total — every override key must correspond to a "
                "requested stdlib module."
            )
        if not isinstance(value, str):
            raise TypeError(
                f"compose_with_stdlib: override value for `{name}` is "
                f"{type(value).__name__}, expected str"
            )
        if not value:
            raise ValueError(
                f"compose_with_stdlib: override value for `{name}` is empty; "
                "an empty stdlib module would never compile, refusing to compose"
            )

    # Dedupe + sort so the composed bytes are deterministic regardless
    # of the order stdlib_modules came in.
    deduped: tuple[str, ...] = tuple(sorted(set(stdlib_modules)))

    if not deduped:
        return ComposedSource(
            text=source,
            stdlib_hash=EMPTY_STDLIB_HASH,
            modules_included=(),
        )

    stdlib_dir = repo_root / "stdlib" / "sigil"
    stdlib_dir_str = str(stdlib_dir)

    parts: list[str] = []
    for module_name in deduped:
        if module_name in overrides:
            # I-OPS-2: do NOT read or write the LRU cache for overridden
            # names. Run the override bytes through the same normalizer
            # the disk path uses so the resulting `stdlib_hash` matches
            # what the same logical bytes from disk would produce (I-OPS-1).
            parts.append(_normalize_module_source(overrides[module_name]))
            continue
        module_path = stdlib_dir / f"{module_name}.sigil"
        if not module_path.is_file():
            raise ValueError(
                f"compose_with_stdlib: stdlib module `{module_name}` not found at {module_path}"
            )
        parts.append(_read_normalized_module(stdlib_dir_str, module_name))

    stdlib_blob = "".join(parts)
    stdlib_hash = (
        hashlib.sha256(stdlib_blob.encode("utf-8")).hexdigest()[:STDLIB_HASH_HEX_LEN]
    )

    # LLM source goes LAST. We don't normalize the LLM source's line
    # endings — the LLM-author owns its format, and altering it would
    # invalidate any line-numbered diagnostic the agent later receives.
    composed_text = stdlib_blob + source

    return ComposedSource(
        text=composed_text,
        stdlib_hash=stdlib_hash,
        modules_included=deduped,
        # stdlib_blob ends with a newline, so the LLM source starts on the
        # line AFTER the blob: source line 1 == composed line offset+1.
        stdlib_line_offset=stdlib_blob.count("\n"),
    )
