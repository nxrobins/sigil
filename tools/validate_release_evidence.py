#!/usr/bin/env python3
"""Validate the CSIR v9 release-evidence structure without claiming a release.

WHY THIS EXISTS. The historical v8 TOML is a pending rollout record, not a
machine-checked tagged release. A green template check must never be mistaken
for completed platform, proof, or performance evidence. The two modes below
are deliberately disjoint and reject unknown fields and incomplete inventories.

    python tools/validate_release_evidence.py --self-test
    python tools/validate_release_evidence.py --template docs/release-evidence/csir-v9-dual-gate.toml
    python tools/validate_release_evidence.py --tagged /path/evidence.toml --artifacts /path/bundle

Tagged mode checks an EXISTING local tag, its subject's model/toolchain, complete
typed results, and the hashes of retained artifacts. It does not contact CI or
authenticate artifact provenance: independently verified CI attestations are a
separate release prerequisite. Exit zero means structurally consistent evidence,
never permission to tag, publish, retire a gate, or resolve a residual risk.

Python 3.11+ is required for the standard-library TOML parser. No files, refs,
or external state are changed except synthetic scratch artifacts in --self-test.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import math
import re
import subprocess
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path, PurePosixPath

import tomllib

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "docs/release-evidence/csir-v9-dual-gate.toml"
MAX_RECORD_BYTES = 1024 * 1024
MAX_COUNTER = (1 << 64) - 1
PENDING = "pending"

# Update protocol: widening or narrowing this inventory is a reviewed release
# contract change, never a way to turn an absent lane into a passing release.
# A platform record requires execution; an Intel cross-build alone cannot pass.
CHECKS = (
    "workspace_solver_off",
    "workspace_solver_on",
    "linux_runtime",
    "macos_arm64",
    "macos_x86_64",
    "windows_msvc",
    "cli",
    "mcp",
    "serve",
    "packages",
    "foreign_frontends",
    "corpus",
    "lean_proofs",
    "lean_dependency_audit",
    "native_decoder_diagnostics",
    "occurrence_mutants",
    "constructor_inventory",
    "claim_signatures",
    "public_independent_lengths",
    "secret_ct_preserved",
    "performance",
)
GATES = (
    "semantic_v9",
    "historical_v8",
    "obligations_v6",
    "rust_taint",
    "rust_ownership",
    "z3_air_capability",
)
RESULTS = (
    "corpus_total",
    "accepted_corpus_regressions",
    "unexplained_disagreements",
    "approved_policy_rejections",
    "median_verifier_ms",
    "p95_verifier_ms",
    "initialization_ms",
    "peak_memory_bytes",
    "million_record_count",
    "selfhost_trio_seconds",
)
TOP_LEVEL = {
    "evidence_version",
    "model_version",
    "certificate_schema",
    "phase",
    "state",
    "retirement_eligible",
    "unresolved_risks",
    "repository",
    "tag",
    "commit",
    "lean_toolchain",
    "rust_toolchain",
    "mandatory_gates",
    "limits",
    "results",
    "checks",
}
CHECK_FIELDS = {
    "status",
    "executed",
    "cases",
    "commit",
    "run_url",
    "artifact",
    "sha256",
}
HEX_COMMIT = re.compile(r"[0-9a-f]{40}(?:[0-9a-f]{24})?")
HEX_SHA256 = re.compile(r"[0-9a-f]{64}")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")


class EvidenceError(ValueError):
    """A fail-closed refusal with a stable reason used by the self-tests."""

    def __init__(self, code: str, detail: str):
        super().__init__(f"{code}: {detail}")
        self.code = code


def require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise EvidenceError(code, detail)


def exact_keys(value: object, expected: set[str], field: str) -> dict:
    require(type(value) is dict, "shape", f"{field} must be a table")
    require(
        set(value) == expected,
        "fields",
        f"{field} fields must be exactly {sorted(expected)}",
    )
    return value


def integer(value: object, field: str, minimum: int = 0) -> int:
    # bool is an int subclass in Python; accepting true as one checked case
    # would silently convert a claim into anti-vacuity evidence.
    require(
        type(value) is int and minimum <= value <= MAX_COUNTER,
        "integer",
        f"{field} must be an unsigned 64-bit integer >= {minimum}",
    )
    return value


def number(value: object, field: str) -> int | float:
    require(type(value) in (int, float), "number", f"{field} must be numeric")
    require(
        type(value) is not int or value <= MAX_COUNTER,
        "number",
        f"{field} integer measurement exceeds the counter bound",
    )
    require(
        math.isfinite(value) and value > 0,
        "number",
        f"{field} must be finite and positive",
    )
    return value


def nonpending(value: object, field: str) -> str:
    require(
        type(value) is str
        and bool(value.strip())
        and value == value.strip()
        and value.casefold() not in {PENDING, "unknown", "n/a", "none"},
        "pending",
        f"{field} needs concrete evidence",
    )
    return value


def artifact_path(value: object) -> PurePosixPath:
    require(
        type(value) is str, "artifact_path", "artifact must be a relative POSIX path"
    )
    path = PurePosixPath(value)
    require(
        bool(value)
        and value != PENDING
        and all(ord(character) >= 32 and ord(character) != 127 for character in value)
        and not path.is_absolute()
        and str(path) == value
        and ".." not in path.parts
        and "\\" not in value
        and ":" not in value,
        "artifact_path",
        "artifact must be canonical and remain inside the bundle",
    )
    return path


def validate_document(document: object, *, tagged: bool) -> dict:
    record = exact_keys(document, TOP_LEVEL, "evidence")
    for field, expected in (
        ("evidence_version", 1),
        ("model_version", 9),
        ("certificate_schema", 9),
        ("phase", "dual-gate-integration"),
        ("retirement_eligible", False),
    ):
        require(
            type(record[field]) is type(expected) and record[field] == expected,
            "policy",
            f"{field} must remain {expected!r}",
        )
    require(
        record["unresolved_risks"] == ["SR-013", "SR-017"],
        "risks",
        "SR-013 and SR-017 must remain explicitly unresolved",
    )
    require(
        record["state"] == ("complete" if tagged else PENDING),
        "state",
        "pending templates and completed tagged records use separate modes",
    )

    gates = exact_keys(record["mandatory_gates"], set(GATES), "mandatory_gates")
    for gate in GATES:
        require(
            gates[gate] is True, "gate", f"mandatory gate {gate} cannot be disabled"
        )
    limits = exact_keys(record["limits"], {"peak_memory_bytes"}, "limits")
    results = exact_keys(record["results"], set(RESULTS), "results")
    checks = exact_keys(record["checks"], set(CHECKS), "checks")
    for name in CHECKS:
        exact_keys(checks[name], CHECK_FIELDS, f"checks.{name}")

    if not tagged:
        for field in ("repository", "tag", "commit", "rust_toolchain"):
            require(
                record[field] == PENDING,
                "template_claim",
                f"template {field} must stay pending",
            )
        for field, value in results.items():
            require(
                value == PENDING,
                "template_claim",
                f"template results.{field} must stay pending",
            )
        require(
            limits["peak_memory_bytes"] == PENDING,
            "template_claim",
            "memory limit needs separate release review",
        )
        for name, check in checks.items():
            require(
                check["executed"] is False,
                "template_claim",
                f"template {name} cannot claim execution",
            )
            require(
                all(
                    value == PENDING
                    for field, value in check.items()
                    if field != "executed"
                ),
                "template_claim",
                f"template {name} must contain no completed evidence",
            )
        nonpending(record["lean_toolchain"], "lean_toolchain")
        return record

    repository = nonpending(record["repository"], "repository")
    require(
        REPOSITORY.fullmatch(repository) is not None,
        "repository",
        "repository must be owner/name",
    )
    commit = nonpending(record["commit"], "commit")
    require(
        HEX_COMMIT.fullmatch(commit) is not None,
        "commit",
        "commit must be a full lowercase Git object id",
    )
    tag = nonpending(record["tag"], "tag")
    require(
        re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._/-]{0,127}", tag) is not None,
        "tag",
        "tag must be a bounded explicit tag name",
    )
    for field in ("lean_toolchain", "rust_toolchain"):
        nonpending(record[field], field)
    run_url = re.compile(
        rf"https://github\.com/{re.escape(repository)}/actions/runs/[1-9][0-9]*/job/[1-9][0-9]*"
    )
    for name, check in checks.items():
        require(
            check["status"] == "passed" and check["executed"] is True,
            "check",
            f"{name} must have passed execution; skipped/build-only does not qualify",
        )
        integer(check["cases"], f"checks.{name}.cases", 1)
        require(
            check["commit"] == commit,
            "check_commit",
            f"{name} evidence is from a different commit",
        )
        require(
            type(check["run_url"]) is str
            and run_url.fullmatch(check["run_url"]) is not None,
            "run_url",
            f"{name} needs an exact CI job URL from {repository}",
        )
        artifact_path(check["artifact"])
        require(
            type(check["sha256"]) is str
            and HEX_SHA256.fullmatch(check["sha256"]) is not None,
            "digest",
            f"{name} needs a lowercase SHA-256 artifact digest",
        )

    total = integer(results["corpus_total"], "corpus_total", 1)
    for field in ("accepted_corpus_regressions", "unexplained_disagreements"):
        require(
            integer(results[field], field) == 0, "regression", f"{field} must be zero"
        )
    require(
        integer(results["approved_policy_rejections"], "approved_policy_rejections")
        <= total,
        "corpus",
        "approved rejections cannot exceed the measured corpus",
    )
    median = number(results["median_verifier_ms"], "median_verifier_ms")
    require(median < 1, "latency", "warm verifier median must be below one millisecond")
    require(
        number(results["p95_verifier_ms"], "p95_verifier_ms") >= median,
        "latency",
        "p95 must be at least the median",
    )
    number(results["initialization_ms"], "initialization_ms")
    peak = integer(results["peak_memory_bytes"], "peak_memory_bytes", 1)
    require(
        peak <= integer(limits["peak_memory_bytes"], "limits.peak_memory_bytes", 1),
        "memory",
        "measured peak exceeds the separately reviewed memory limit",
    )
    integer(results["million_record_count"], "million_record_count", 1_000_000)
    require(
        number(results["selfhost_trio_seconds"], "selfhost_trio_seconds") <= 5,
        "selfhost",
        "the existing five-second self-host canary must remain satisfied",
    )
    return record


def load_document(path: Path) -> dict:
    try:
        with path.open("rb") as stream:
            data = stream.read(MAX_RECORD_BYTES + 1)
        require(
            len(data) <= MAX_RECORD_BYTES,
            "size",
            "evidence record exceeds the byte ceiling",
        )
        return tomllib.loads(data.decode("utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise EvidenceError("read", f"cannot read {path}: {error}") from error


def git_read(repo: Path, *args: str) -> str:
    try:
        result = subprocess.run(
            ["git", "-C", str(repo), *args],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
        return result.stdout.strip()
    except (OSError, subprocess.SubprocessError) as error:
        raise EvidenceError(
            "git", "the existing tag or its subject could not be verified"
        ) from error


def validate_subject(record: dict, repo: Path, read_git: Callable = git_read) -> None:
    ref = f"refs/tags/{record['tag']}"
    read_git(repo, "check-ref-format", ref)
    commit = read_git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}")
    require(
        commit == record["commit"],
        "tag_commit",
        "tag and evidence name different commits",
    )
    for source, constant, expected in (
        ("crates/sigil-compiler/src/formal.rs", "CSIR_MODEL_VERSION", "9"),
        (
            "crates/sigil-compiler/src/diagnostics/certificate.rs",
            "CERTIFICATE_SCHEMA_VERSION",
            "9",
        ),
    ):
        text = read_git(repo, "show", f"{commit}:{source}")
        values = re.findall(
            rf"^pub const {constant}: u32 = ([0-9]+);$", text, re.MULTILINE
        )
        require(
            values == [expected],
            "subject_version",
            f"tagged subject must declare {constant} = {expected}",
        )
    toolchain = read_git(repo, "show", f"{commit}:proofs/lean/lean-toolchain")
    require(
        toolchain == record["lean_toolchain"],
        "toolchain",
        "tagged Lean toolchain differs from the evidence",
    )


def validate_artifacts(record: dict, bundle: Path) -> None:
    require(
        bundle.is_dir(), "artifact", "an existing artifact bundle directory is required"
    )
    root = bundle.resolve()
    for name, check in record["checks"].items():
        relative = artifact_path(check["artifact"])
        path = root.joinpath(*relative.parts)
        # Reject symlinks at EVERY path component: a digest must refer to the
        # retained bundle, not an ambient file outside it or a later retarget.
        current = root
        for part in relative.parts:
            current /= part
            require(
                not current.is_symlink(),
                "artifact",
                f"{name} artifact cannot traverse a symlink",
            )
        require(
            path.is_file(),
            "artifact",
            f"{name} artifact is missing or not a regular file",
        )
        digest = hashlib.sha256()
        size = 0
        try:
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
                    size += len(chunk)
        except OSError as error:
            raise EvidenceError(
                "artifact", f"cannot read artifact for {name}"
            ) from error
        require(size > 0, "artifact", f"{name} artifact cannot be empty")
        require(
            digest.hexdigest() == check["sha256"],
            "artifact_digest",
            f"{name} artifact digest differs",
        )


def self_test() -> int:
    """SC-P4: prove refusals on planted mutants, with an independent accept twin."""
    template = load_document(TEMPLATE)
    validate_document(template, tagged=False)
    count = 0

    def refuses(code: str, action: Callable) -> None:
        nonlocal count
        try:
            action()
        except EvidenceError as error:
            require(
                error.code == code, "self_test", f"expected {code}, got {error.code}"
            )
            count += 1
        else:
            raise EvidenceError("self_test", f"planted {code} mutation was accepted")

    complete = copy.deepcopy(template)
    complete.update(
        state="complete",
        repository="self-test/not-a-release",
        tag="self-test-only",
        commit="a" * 40,
        rust_toolchain="synthetic-self-test-only",
    )
    complete["limits"]["peak_memory_bytes"] = 1024
    complete["results"] = dict(
        zip(RESULTS, (2, 0, 0, 1, 0.5, 0.8, 1, 512, 1_000_000, 4), strict=True)
    )
    content = b"SYNTHETIC SELF-TEST FIXTURE; NOT RELEASE EVIDENCE\n"
    for check in complete["checks"].values():
        check.update(
            status="passed",
            executed=True,
            cases=1,
            commit="a" * 40,
            run_url="https://github.com/self-test/not-a-release/actions/runs/1/job/1",
            artifact="self-test.log",
            sha256=hashlib.sha256(content).hexdigest(),
        )
    validate_document(complete, tagged=True)

    def mutant(
        path: tuple[str, ...], value: object, code: str, *, pending: bool = False
    ) -> None:
        changed = copy.deepcopy(template if pending else complete)
        target = changed
        for field in path[:-1]:
            target = target[field]
        target[path[-1]] = value
        refuses(code, lambda: validate_document(changed, tagged=not pending))

    refuses("shape", lambda: validate_document([], tagged=True))
    for field in TOP_LEVEL:
        changed = copy.deepcopy(complete)
        del changed[field]
        refuses(
            "fields", lambda changed=changed: validate_document(changed, tagged=True)
        )
    mutant(("extra",), True, "fields")
    for field in ("mandatory_gates", "limits", "results", "checks"):
        mutant((field,), [], "shape")
        mutant((field, "extra"), True, "fields")
    for field in ("evidence_version", "model_version", "certificate_schema"):
        mutant((field,), True, "policy")
    mutant(("retirement_eligible",), True, "policy")
    mutant(("phase",), "retirement", "policy")
    mutant(("unresolved_risks",), [], "risks")
    mutant(("state",), PENDING, "state")
    refuses("state", lambda: validate_document(complete, tagged=False))
    for gate in GATES:
        mutant(("mandatory_gates", gate), False, "gate")
    mutant(("tag",), "v9-claimed", "template_claim", pending=True)
    mutant(("checks", "macos_x86_64", "executed"), True, "template_claim", pending=True)
    mutant(("results", "corpus_total"), 1, "template_claim", pending=True)
    mutant(("limits", "peak_memory_bytes"), 1024, "template_claim", pending=True)
    mutant(
        ("checks", "performance", "status"), "passed", "template_claim", pending=True
    )
    mutant(("repository",), "wrong", "repository")
    mutant(("commit",), "abc", "commit")
    mutant(("tag",), "-option", "tag")
    mutant(("rust_toolchain",), PENDING, "pending")
    for name in CHECKS:
        changed = copy.deepcopy(complete)
        del changed["checks"][name]
        refuses(
            "fields", lambda changed=changed: validate_document(changed, tagged=True)
        )
        mutant(("checks", name, "status"), "skipped", "check")
    for field, value, code in (
        ("executed", False, "check"),
        ("cases", 0, "integer"),
        ("cases", True, "integer"),
        ("cases", 1 << 64, "integer"),
        ("commit", "b" * 40, "check_commit"),
        ("run_url", "https://example.org", "run_url"),
        ("sha256", "not-a-digest", "digest"),
        ("artifact", "../escape", "artifact_path"),
        ("artifact", "/absolute", "artifact_path"),
        ("artifact", "a\\b", "artifact_path"),
        ("artifact", "a\x00b", "artifact_path"),
        ("artifact", "a//b", "artifact_path"),
        ("artifact", PENDING, "artifact_path"),
    ):
        mutant(("checks", "macos_x86_64", field), value, code)
    for field, value, code in (
        ("corpus_total", 0, "integer"),
        ("accepted_corpus_regressions", 1, "regression"),
        ("unexplained_disagreements", 1, "regression"),
        ("approved_policy_rejections", 3, "corpus"),
        ("median_verifier_ms", 1, "latency"),
        ("p95_verifier_ms", 0.1, "latency"),
        ("initialization_ms", float("nan"), "number"),
        ("initialization_ms", float("inf"), "number"),
        ("initialization_ms", True, "number"),
        ("initialization_ms", "1", "number"),
        ("initialization_ms", 1 << 1024, "number"),
        ("peak_memory_bytes", 2048, "memory"),
        ("million_record_count", 999_999, "integer"),
        ("selfhost_trio_seconds", 5.01, "selfhost"),
    ):
        mutant(("results", field), value, code)

    # The fake Git reader is confined to self-test. No tag is created, even in
    # scratch: the production path always reads the user's pre-existing ref.
    def subject(_repo: Path, *args: str) -> str:
        if args[0] == "check-ref-format":
            require(
                args == ("check-ref-format", "refs/tags/self-test-only"),
                "self_test",
                "must check the exact tag namespace",
            )
            return ""
        if args[0] == "rev-parse":
            require(
                args == ("rev-parse", "--verify", "refs/tags/self-test-only^{commit}"),
                "self_test",
                "must peel the exact tag",
            )
            return "a" * 40
        if args[-1].endswith("/formal.rs"):
            return "pub const CSIR_MODEL_VERSION: u32 = 9;"
        if args[-1].endswith("/certificate.rs"):
            return "pub const CERTIFICATE_SCHEMA_VERSION: u32 = 9;"
        return complete["lean_toolchain"]

    validate_subject(complete, ROOT, subject)
    refuses("tag_commit", lambda: validate_subject(complete, ROOT, lambda *_: "b" * 40))
    refuses(
        "subject_version",
        lambda: validate_subject(
            complete,
            ROOT,
            lambda repo, *args: subject(repo, *args).replace("= 9;", "= 8;"),
        ),
    )
    refuses(
        "subject_version",
        lambda: validate_subject(
            complete,
            ROOT,
            lambda repo, *args: (
                "pub const CERTIFICATE_SCHEMA_VERSION: u32 = 10;"
                if args[-1].endswith("/certificate.rs")
                else subject(repo, *args)
            ),
        ),
    )
    refuses(
        "toolchain",
        lambda: validate_subject(
            complete,
            ROOT,
            lambda repo, *args: (
                "wrong" if args[-1].endswith("lean-toolchain") else subject(repo, *args)
            ),
        ),
    )
    with tempfile.TemporaryDirectory(prefix="sigil-evidence-self-test-") as scratch:
        bundle = Path(scratch)
        path = bundle / "self-test.log"
        refuses("artifact", lambda: validate_artifacts(complete, bundle))
        path.write_bytes(content)
        validate_artifacts(complete, bundle)
        path.write_bytes(content + b"mutated")
        refuses("artifact_digest", lambda: validate_artifacts(complete, bundle))
        path.write_bytes(b"")
        refuses("artifact", lambda: validate_artifacts(complete, bundle))
        path.unlink()
        link_target = bundle / "link-target.log"
        link_target.write_bytes(content)
        path.symlink_to(link_target)
        refuses("artifact", lambda: validate_artifacts(complete, bundle))
        nested = copy.deepcopy(complete)
        nested["checks"]["performance"]["artifact"] = "linked/self-test.log"
        path.unlink()
        path.write_bytes(content)
        (bundle / "linked").symlink_to(bundle, target_is_directory=True)
        refuses("artifact", lambda: validate_artifacts(nested, bundle))
        invalid = bundle / "invalid.toml"
        refuses("read", lambda: load_document(invalid))
        invalid.write_text("state='pending'\nstate='complete'\n", encoding="utf-8")
        refuses("read", lambda: load_document(invalid))
        invalid.write_bytes(b"\xff")
        refuses("read", lambda: load_document(invalid))
        invalid.write_bytes(b"x" * (MAX_RECORD_BYTES + 1))
        refuses("size", lambda: load_document(invalid))
        refuses(
            "git",
            lambda: git_read(
                bundle, "rev-parse", "--verify", "refs/tags/absent^{commit}"
            ),
        )
    print(
        f"release-evidence self-test: {count} planted refusals detected; synthetic accept twins passed"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--template", type=Path)
    mode.add_argument("--tagged", type=Path)
    parser.add_argument("--artifacts", type=Path)
    parser.add_argument("--repo", type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        if args.self_test:
            return self_test()
        path = args.tagged or args.template
        record = validate_document(load_document(path), tagged=args.tagged is not None)
        if args.tagged is not None:
            require(
                args.artifacts is not None,
                "artifact",
                "tagged mode requires --artifacts",
            )
            validate_subject(record, args.repo)
            validate_artifacts(record, args.artifacts)
            print(
                "tagged evidence structure and artifact hashes valid; CI provenance is NOT authenticated; NOT release authorization"
            )
        else:
            toolchain = (
                (args.repo / "proofs/lean/lean-toolchain")
                .read_text(encoding="utf-8")
                .strip()
            )
            require(
                record["lean_toolchain"] == toolchain,
                "toolchain",
                "template Lean toolchain differs from the repository",
            )
            print("pending release-evidence template valid; release remains blocked")
        return 0
    except (EvidenceError, OSError) as error:
        print(f"release-evidence: refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
