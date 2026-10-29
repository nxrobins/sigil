"""Transport a bounded native search and preserve create-new checkpoint files.

No mutation, evaluation, fitting, ranking, checkpoint-schema construction or
compatibility decision runs in Python. SIGIL returns the state and envelopes.
The fixed dataset is checked against native bytes before any output is created.
This driver supports file checkpoints and CPU exchange, not KV or GPU execution.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import sys


def initial_request(seed, stream, generations, steps, hybrid, budget=None):
    for value, maximum in ((seed, 2**64 - 1), (stream, 2**63 - 1),
                           (generations, 40), (steps, 12)):
        if type(value) is not int or not 0 <= value <= maximum:
            raise ValueError("configuration is outside the declared search bounds")
    if generations == 0 or type(hybrid) is not bool:
        raise ValueError("generations must be positive and hybrid must be boolean")
    if budget is None:
        budget = (generations + 1) * 8
    if type(budget) is not int or not 0 <= budget <= (generations + 1) * 8:
        raise ValueError("candidate budget exceeds the configured search")
    return b"ASIN" + bytes((1, generations, steps, int(hybrid))) + struct.pack("<3Q", seed, stream, budget)


def command(name, payload):
    return name + bytes((1, 0, 0, 0)) + payload


def invoke(cli, package, request):
    result = subprocess.run([cli, "run", "--package", str(package), "--input", request.hex(),
                             "--fuel", "500000", "--json"], capture_output=True, timeout=60)
    envelope = json.loads(result.stdout)
    if result.returncode or type(envelope) is not dict or envelope.get("status") != "ok":
        raise ValueError("native search refused the request; previous checkpoints are unchanged")
    output = envelope["data"]["output"]
    if (type(output) is not list or len(output) > 8192
            or any(type(value) is not int or not 0 <= value <= 255 for value in output)):
        raise ValueError("invalid native response byte array")
    return bytes(output)


def evaluation_identity(cli, package, job_id):
    if type(job_id) is not str or re.fullmatch(r"[0-9a-f]{64}", job_id) is None:
        raise ValueError("exchange requires a 32-byte lowercase hexadecimal --job-id")
    checked = subprocess.run([cli, "check", "--package", str(package), "--json"],
                             capture_output=True, timeout=60)
    result = json.loads(checked.stdout)
    if checked.returncode or type(result) is not dict or result.get("status") != "ok":
        raise ValueError("cannot bind evaluation requests to a fresh package certificate")
    certificate = result["data"]["certificate"]
    identity = certificate["artifact_identity_hash"]
    if (certificate.get("solver_verified") is not True or type(identity) is not str
            or re.fullmatch(r"sha256:[0-9a-f]{64}", identity) is None):
        raise ValueError("expected a solver-verified package artifact identity")
    # This is an unsigned program identity, not a worker signature or score proof.
    return bytes.fromhex(job_id + identity[7:])


def write_new(path, content):
    with path.open("xb") as destination:
        destination.write(content)
        destination.flush()
        os.fsync(destination.fileno())


def exchange_step(cli, package, state, identity, directory):
    revision = header(state)[13]
    request = invoke(cli, package, command(b"ASEQ", identity + state))
    write_new(directory / f"evaluation-{revision:04d}-request.json", request)
    # Separate native calls keep the existing per-call fitting and wire budgets.
    # The decoder only returns an AFIT-v1 request; no host command is in the data.
    work = invoke(cli, package, command(b"ASED", request))
    report = invoke(cli, package, work)
    response = invoke(cli, package, command(b"ASER", struct.pack("<HB", len(request), 0)
                                           + request + report))
    write_new(directory / f"evaluation-{revision:04d}-response.json", response)
    return invoke(cli, package, command(b"ASEA", identity + state + response))


def read_checkpoint(path):
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        details = os.fstat(descriptor)
        if not stat.S_ISREG(details.st_mode) or details.st_size > 8192:
            raise ValueError("checkpoint must be a bounded regular file")
        source = os.fdopen(descriptor, "rb")
        descriptor = -1
        with source:
            raw = source.read(8193)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    if len(raw) > 8192:
        raise ValueError("checkpoint grew beyond the input bound")
    return raw


def header(state):
    if len(state) != 1736:
        raise ValueError("native response is not a search state")
    values = struct.unpack_from("<32Q", state)
    if values[:3] != (1397904193, 1, 2) or values[12] > 2 or values[13] > 368:
        raise ValueError("invalid native search state header")
    return values


def publish(directory, state, envelope):
    revision = header(state)[13]
    path = directory / f"checkpoint-{revision:04d}.json"
    # Create-new publication never replaces any earlier checkpoint or symlink.
    # An interrupted write may leave an incomplete new file; native restore
    # rejects it and all previously completed revisions remain available.
    write_new(path, envelope)
    return path


def dataset_bytes(package):
    """A fixed dataset contract; runtime numerical operations remain in SIGIL."""
    raw = read_checkpoint(package / "dataset.json")
    record = json.loads(raw)
    if (type(record) is not dict or set(record) != {"format", "model", "train", "validation", "identity_sha256"}
            or record["format"] != "sigil-regression-dataset-v1" or record["model"] != "slope*x+bias"
            or type(record["train"]) is not list or len(record["train"]) != 4
            or type(record["validation"]) is not list or len(record["validation"]) != 2):
        raise ValueError("incompatible fixed regression dataset")
    values = []
    for row in record["train"] + record["validation"]:
        if (type(row) is not list or len(row) != 2
                or any(type(v) not in (int, float) or not math.isfinite(v) for v in row)):
            raise ValueError("dataset requires six finite (x,y) pairs")
        values.extend(row)
    wire = b"RGRD" + bytes((1, 4, 2, 0)) + struct.pack("<12d", *values)
    identity = hashlib.sha256(wire).hexdigest()
    if record["identity_sha256"] != identity:
        raise ValueError("dataset identity does not match its rows")
    return wire, identity


def verify_dataset(cli, package, expected_identity=None):
    expected, identity = dataset_bytes(package)
    if expected_identity is not None and expected_identity != identity:
        raise ValueError("requested dataset differs from this fixed workload")
    if invoke(cli, package, command(b"RGDS", b"")) != expected:
        raise ValueError("dataset file differs from the compiled regression rows")
    return identity


def inspect_winner(cli, package, state):
    """Decode the native report; never reconstruct training or validation scores."""
    h = header(state)
    if h[12] != 2:
        return {}
    body = state[256:256 + 72 + state[262] * 4]
    request = b"AFIT" + bytes((1, 0, 0, 0)) + body
    result = invoke(cli, package, request)
    if len(result) != 840 + len(request) or result[840:] != request:
        raise ValueError("winner report does not match the requested candidate")
    values = struct.unpack_from("<14d", result, 152)
    if not all(math.isfinite(value) for value in values):
        raise ValueError("winner report contains nonfinite values")
    scores = invoke(cli, package, command(b"RGPR", struct.pack("<2d", *values[2:4])))
    if len(scores) != 16:
        raise ValueError("invalid native regression summary")
    training, validation = struct.unpack("<2d", scores)
    if not math.isclose(training, values[0], rel_tol=1e-12, abs_tol=1e-12) or not math.isfinite(validation):
        raise ValueError("native regression reports disagree")
    return {"training_loss": training, "validation_loss": validation,
            "slope": values[2], "bias": values[3], "candidate_gradients": list(values[6:])}


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--stream", type=int, default=54)
    parser.add_argument("--generations", type=int, default=2)
    parser.add_argument("--steps", type=int, default=12)
    parser.add_argument("--arm", choices=("discrete", "hybrid"), default="hybrid")
    parser.add_argument("--budget", type=int)
    parser.add_argument("--transitions", type=int, default=368)
    parser.add_argument("--evaluation", choices=("local", "exchange"), default="local")
    parser.add_argument("--job-id")
    parser.add_argument("--dataset-sha256", help="optional expected identity; never selects arbitrary data")
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        if not 0 <= args.transitions <= 368:
            raise ValueError("transition count must be in 0..368")
        initial = initial_request(args.seed, args.stream, args.generations, args.steps,
                                  args.arm == "hybrid", args.budget)
        if args.out_dir.exists() or args.out_dir.is_symlink():
            raise ValueError("output directory must be new")
        package = args.package.resolve()
        dataset = verify_dataset(args.sigil, package, args.dataset_sha256)
        if args.evaluation == "local" and args.job_id is not None:
            raise ValueError("--job-id requires --evaluation exchange")
        identity = evaluation_identity(args.sigil, package,
                                       args.job_id if args.evaluation == "exchange" else "00" * 32)
        marker = args.evaluation.encode("ascii") + b"\n" + identity.hex().encode("ascii") + b"\n"
        if args.resume:
            if read_checkpoint(args.resume.parent / "program-identity.hex") != marker:
                raise ValueError("resume requires the same mode, job and program identity")
            envelope = read_checkpoint(args.resume)
            state = invoke(args.sigil, package, command(b"ASOP", initial + envelope))
        else:
            state = invoke(args.sigil, package, initial)
            envelope = invoke(args.sigil, package, command(b"ASCK", state))
        if state[160:192].hex() != dataset:
            raise ValueError("native state belongs to another dataset")
        header(state)
        args.out_dir.mkdir()
        write_new(args.out_dir / "program-identity.hex", marker)
        path = publish(args.out_dir, state, envelope)
        for _ in range(args.transitions):
            if header(state)[12] == 2:
                break
            if args.evaluation == "exchange" and header(state)[12] == 0:
                next_state = exchange_step(args.sigil, package, state, identity, args.out_dir)
            else:
                next_state = invoke(args.sigil, package, command(b"ASST", state))
            next_envelope = invoke(args.sigil, package, command(b"ASAD", next_state + envelope))
            path = publish(args.out_dir, next_state, next_envelope)
            state, envelope = next_state, next_envelope
        h = header(state)
        print(json.dumps({"checkpoint": str(path.resolve()), "complete": h[12] == 2,
                          "task": "fixed-regression-v1", "dataset_sha256": dataset,
                          "generation": h[10], "candidate_cursor": h[11], "transitions": h[13],
                          "candidates_evaluated": h[14], "candidate_budget": h[15],
                          "graph_evaluations": h[16], "fitting_accepted": h[17],
                          "fitting_rejected": h[18], **inspect_winner(args.sigil, package, state)},
                         sort_keys=True, indent=2, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError, struct.error, RecursionError,
            subprocess.TimeoutExpired) as error:
        print(f"regression search refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
