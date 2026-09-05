#!/usr/bin/env python3
"""Refuse a tree that carries a private-development identifier, without naming the identifiers.

This tree was split out of a private monorepo whose research and training programs stayed
private and now pin this tree by commit. The split's exporter swept every shipped file for a
list of private identifiers; that list cannot ship, because listing the identifiers is itself
the disclosure. This sweep keeps the check alive in the public tree by matching HASHES: each
identifier's SHA-256 is in tools/forbidden-token-hashes.txt, this script hashes the tree's
own words and word-sequences, and a match is a refusal. A grep for an identifier finds
nothing; a commit that carries one still fails the hygiene lane.

Matching. A word is a maximal run of ASCII letters and digits. A candidate is one to five
consecutive words joined by the exact separator text between them, provided no separator
contains whitespace -- so `a/b`, `a-b-c`, `a_b`, and `a@b.c` are candidates exactly as
written, and an identifier with different punctuation is a different identifier. Matching
is case-sensitive. One rule lives in code rather than in the list because it is a pattern,
not a token: the word `A` `IN`, optionally followed by digits, the identifier prefix of a
private proof campaign (spelled apart here so this file does not match itself). Hits are
reported as `path:line` only, never as text, so a refusal in a public log discloses nothing.

Not a secrecy mechanism: the SHA-256 of a short guessable string is confirmable by
guessing. The list stops the identifiers from being READ; it does not stop a determined
reader from confirming a guess, and it does not need to.

In a checkout that carries export/keep-manifest.tsv (the private monorepo) only its KEEP
paths are swept, because the excluded paths are the private material itself. Anywhere else
every file is swept, and a sweep that sees fewer than MIN_FILES files refuses rather than
passing vacuously.

Usage:
    python tools/token_sweep.py                    sweep this tree; exit 1 on any hit
    python tools/token_sweep.py --self-test        prove the detector fires on planted probes
    python tools/token_sweep.py --regenerate FILE  (private) rebuild the hash list from a token file
    python tools/token_sweep.py --check-list FILE  (private) exit 1 unless the hash list matches FILE
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HASHES = ROOT / "tools" / "forbidden-token-hashes.txt"
PRIVATE_MANIFEST = ROOT / "export" / "keep-manifest.tsv"
WORD = re.compile(r"[A-Za-z0-9]+")
MAX_WORDS = 5
MIN_FILES = 50
SKIP_DIRS = {".git", "target", ".lake", "node_modules", "__pycache__", ".venv"}
# The campaign rule: the bare substring hits TAINT, MAIN, and DOMAIN, so it is a whole word.
CAMPAIGN = re.compile(r"(?<![A-Za-z0-9_])" + "A" "IN" + r"[0-9]*(?![A-Za-z0-9_])")


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def canonical(token: str) -> str:
    """An identifier as it appears between two words: leading and trailing punctuation dropped."""
    return re.sub(r"^[^A-Za-z0-9]+|[^A-Za-z0-9]+$", "", token)


def probes() -> list[str]:
    """Three planted identifiers whose hashes ship in the list so the self-test can prove the
    detector fires: one word, a hyphenated pair, and a punctuated triple. Assembled at run time
    so the literal never appears in this file, which is itself swept."""
    return ["".join(("sweep", "probe", "one")), "-".join(("sweep", "probe", "two")), "sweep" + "@" + "probe" + "." + "three"]


def load_hashes(path: Path = HASHES) -> tuple[set[str], set[str]]:
    """`(identifier digests, first-word digests)`; refuses a list too short to have loaded."""
    identifiers: set[str] = set()
    prefixes: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("prefix:"):
            prefixes.add(line[len("prefix:"):])
        else:
            identifiers.add(line)
    if len(identifiers) < 10:
        raise SystemExit(f"{path} parsed as {len(identifiers)} identifier digest(s) — it did not load")
    return identifiers, prefixes


def candidates(text: str, prefixes: set[str]):
    """`(offset, candidate)` for every word and every whitespace-free run of up to MAX_WORDS
    words; the longer runs are hashed only where a listed identifier's first word occurs."""
    words = list(WORD.finditer(text))
    for i, first in enumerate(words):
        start, end = first.start(), first.end()
        yield start, text[start:end]
        if digest(text[start:end]) not in prefixes:
            continue
        for j in range(i + 1, min(i + MAX_WORDS, len(words))):
            separator = text[end:words[j].start()]
            if any(c.isspace() for c in separator):
                break
            end = words[j].end()
            yield start, text[start:end]


def hits(text: str, identifiers: set[str], prefixes: set[str]) -> list[int]:
    """Offsets of every identifier occurrence and every campaign-rule match in `text`."""
    found = [offset for offset, candidate in candidates(text, prefixes) if digest(candidate) in identifiers]
    found.extend(m.start() for m in CAMPAIGN.finditer(text))
    return sorted(set(found))


def load_private_rules(path: Path) -> list[tuple[str, str]]:
    rules = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        disposition, prefix, _reason = line.split("\t", 2)
        if disposition not in ("KEEP", "EXCLUDE"):
            raise SystemExit(f"{path}: unknown disposition {disposition!r} for {prefix!r}")
        rules.append((prefix, disposition))
    rules.sort(key=lambda r: -len(r[0]))
    return rules


def files_to_sweep(root: Path) -> list[str]:
    """Tracked files when `root` is the top of a Git worktree, else every file under it."""
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=root, capture_output=True, text=True, check=False)
    if top.returncode == 0 and Path(top.stdout.strip()).resolve() == root.resolve():
        listed = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True)
        paths = [p for p in listed.stdout.decode("utf-8").split("\0") if p]
    else:
        paths = []
        for dirpath, dirs, names in os.walk(root):
            dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
            for name in names:
                paths.append((Path(dirpath) / name).relative_to(root).as_posix())
        paths.sort()
    manifest = root / "export" / "keep-manifest.tsv"
    if manifest.is_file():
        rules = load_private_rules(manifest)

        def disposition(path: str) -> str | None:
            return next((d for prefix, d in rules if path.startswith(prefix)), None)

        paths = [p for p in paths if disposition(p) == "KEEP"]
    return paths


def sweep(root: Path) -> int:
    identifiers, prefixes = load_hashes()
    paths = files_to_sweep(root)
    if len(paths) < MIN_FILES:
        print(f"REFUSED: only {len(paths)} file(s) to sweep under {root} — the tree looks wrong", file=sys.stderr)
        return 2
    findings = 0
    for rel in paths:
        if hits(rel, identifiers, prefixes):
            print(f"{rel}: the PATH carries an identifier", file=sys.stderr)
            findings += 1
        try:
            text = (root / rel).read_bytes().decode("utf-8")
        except (UnicodeDecodeError, OSError):
            continue  # binary or unreadable; the path check above still applied
        for offset in hits(text, identifiers, prefixes):
            print(f"{rel}:{text.count(chr(10), 0, offset) + 1}", file=sys.stderr)
            findings += 1
    if findings:
        print(f"REFUSED: {findings} identifier occurrence(s) in {len(paths)} swept file(s)", file=sys.stderr)
        return 1
    print(f"swept {len(paths)} files: no private-development identifier")
    return 0


def render_list(token_file: Path) -> str:
    tokens = [line.strip() for line in token_file.read_text(encoding="utf-8").splitlines() if line.strip() and not line.startswith("#")]
    identifiers = []
    for token in tokens + probes():
        form = canonical(token)
        words = WORD.findall(form)
        if not words or len(words) > MAX_WORDS or any(c.isspace() for c in form):
            raise SystemExit(f"cannot list {token!r}: identifiers are 1 to {MAX_WORDS} words with no whitespace")
        identifiers.append((form, words[0]))
    lines = [
        "# SHA-256 digests of the identifiers tools/token_sweep.py refuses. The identifiers",
        "# themselves are private; regenerate from their private list with",
        "#   python tools/token_sweep.py --regenerate <token file>",
        "# and prove the list with `--check-list <token file>`. A bare line is the digest of a",
        "# whole identifier as written; a `prefix:` line is the digest of an identifier's first",
        "# word, the pre-filter that decides where multi-word candidates are hashed. Three",
        "# entries are the self-test's planted probes.",
    ]
    lines += sorted({digest(form) for form, _first in identifiers})
    lines += sorted({f"prefix:{digest(first)}" for _form, first in identifiers})
    return "\n".join(lines) + "\n"


def self_test() -> int:
    identifiers, prefixes = load_hashes()
    one, two, three = probes()
    checks = [
        ("hash list loaded", len(identifiers) >= 10 and len(prefixes) >= 5),
        ("a one-word identifier fires", hits(f"see {one} here", identifiers, prefixes) == [4]),
        ("a hyphenated identifier fires", hits(f"path {two}/x", identifiers, prefixes) == [5]),
        ("a punctuated three-word identifier fires", hits(f"mail {three}", identifiers, prefixes) == [5]),
        ("the identifier inside a path fires", hits(f"docs/{one}/notes.md", identifiers, prefixes) != []),
        ("different punctuation is a different identifier", hits(two.replace("-", "_"), identifiers, prefixes) == []),
        ("whitespace ends a candidate", hits(two.replace("-", " "), identifiers, prefixes) == []),
        ("campaign rule fires on a tagged name", hits("A" "IN20.headline", identifiers, prefixes) == [0]),
        ("campaign rule fires bare", hits("campaign A" "IN closes", identifiers, prefixes) == [9]),
        ("campaign rule spares TAINT", hits("TaintSafety", identifiers, prefixes) == []),
        ("campaign rule spares MAIN", hits("fn main()", identifiers, prefixes) == []),
        ("campaign rule spares DOMAIN", hits("the DOMAIN of f", identifiers, prefixes) == []),
        ("ordinary text is clean", hits("a perfectly ordinary line of prose, with/some-punctuation", identifiers, prefixes) == []),
        ("the hash list does not match itself", hits(HASHES.read_text(encoding="utf-8"), identifiers, prefixes) == []),
        ("this file does not match itself", hits(Path(__file__).read_text(encoding="utf-8"), identifiers, prefixes) == []),
    ]
    import tempfile

    with tempfile.TemporaryDirectory() as scratch:
        (Path(scratch) / "one.txt").write_text("nothing\n", encoding="utf-8")
        checks.append(("a near-empty tree refuses instead of passing vacuously", sweep(Path(scratch)) == 2))
    failed = [name for name, ok in checks if not ok]
    for name, ok in checks:
        print(f"  {'ok  ' if ok else 'FAIL'} {name}")
    if failed:
        print(f"\nSELF-TEST FAILED: {len(failed)} check(s) do not hold", file=sys.stderr)
        return 1
    print(f"\nself-test ok: all {len(checks)} checks hold")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=ROOT, help="tree to sweep (default: this checkout)")
    ap.add_argument("--self-test", action="store_true", help="prove the detector fires, then exit")
    ap.add_argument("--regenerate", type=Path, metavar="FILE", help="rebuild the hash list from a plaintext token file")
    ap.add_argument("--check-list", type=Path, metavar="FILE", help="exit 1 unless the hash list matches FILE")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    if args.regenerate:
        HASHES.write_text(render_list(args.regenerate), encoding="utf-8")
        print(f"wrote {HASHES}")
        return 0
    if args.check_list:
        if HASHES.read_text(encoding="utf-8") != render_list(args.check_list):
            print(f"{HASHES} does not match {args.check_list}; run: python tools/token_sweep.py --regenerate {args.check_list}", file=sys.stderr)
            return 1
        print(f"{HASHES} matches {args.check_list}")
        return 0
    return sweep(args.root.resolve())


if __name__ == "__main__":
    sys.exit(main())
