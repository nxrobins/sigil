"""Transport a bounded native search and preserve create-new checkpoint files.

No mutation, evaluation, fitting, ranking, checkpoint-schema construction or
compatibility decision runs in Python. SIGIL returns the state and envelopes.
An optional explicit Public-checkpoint policy connects the grant-controlled KV
host. This driver has no network, GPU or subprocess selected by a candidate.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import sys


def initial_request(seed, stream, generations, steps, hybrid, budget=None):
    for value, maximum in ((seed, 2**64 - 1), (stream, 2**63 - 1),
                           (generations, 40), (steps, 20)):
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
    if values[:3] != (1397904193, 1, 1) or values[12] > 2 or values[13] > 368:
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


def storage_options(args):
    if args.kv_store is None:
        if args.resume_kv or args.allow_public_checkpoint_import or args.storage_host:
            raise ValueError("storage options require --kv-store")
    elif (not args.allow_public_checkpoint_import or not args.storage_host or args.resume):
        raise ValueError("KV requires an explicit Public-checkpoint opt-in and storage host; file resume is separate")


def open_store(directory, resume, identity):
    """Hold one advisory lease for the whole job; never unlink a live lock file."""
    import fcntl

    if not resume:
        directory.mkdir()
    if not stat.S_ISDIR(directory.lstat().st_mode):
        raise ValueError("store must be a real directory, not a symlink")
    flags = os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK
    if not resume:
        flags |= os.O_CREAT | os.O_EXCL
    descriptor = os.open(directory / "writer.lock", flags, 0o600)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValueError("writer lease must be a regular file")
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        marker = directory / "public-search-identity.bin"
        if resume:
            if read_checkpoint(marker) != identity:
                raise ValueError("stored checkpoint requires the same configuration, mode, job and program")
        else:
            write_new(marker, identity)
            (directory / "kv").mkdir()
        if not stat.S_ISDIR((directory / "kv").lstat().st_mode):
            raise ValueError("KV grant root must be a real directory")
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def stored_checkpoint(host, package, directory, previous=None, next_checkpoint=None):
    if previous is not None and (type(previous) is not bytes or len(previous) > 8192
                                or type(next_checkpoint) is not bytes or not 1 <= len(next_checkpoint) <= 8192):
        raise ValueError("storage publication requires bounded prior and next checkpoint bytes")
    request = command(b"AKVR", b"") if previous is None else command(
        b"AKVP", struct.pack("<I", len(previous)) + previous + next_checkpoint)
    arguments = [host, "--package", str(package), "--input-hex", request.hex(),
                 "--allow-public-checkpoint-import", "--kv-read", str(directory / "kv")]
    if previous is not None:
        arguments += ["--kv-write", str(directory / "kv")]
    result = subprocess.run(arguments, capture_output=True, timeout=60)
    if result.returncode:
        raise ValueError("storage refused or publication outcome is uncertain; resume by reading KV")
    envelope = json.loads(result.stdout)
    if type(envelope) is not dict or type(envelope.get("data")) is not dict:
        raise ValueError("invalid storage response envelope")
    data = envelope["data"]
    if (envelope.get("status") != "ok"
            or data.get("import_policy") != "operator-declared-public-checkpoints-v1"
            or data.get("source_label") != "Internal" or data.get("result_label") != "Public"):
        raise ValueError("storage host did not apply the explicit Public-checkpoint policy")
    output = data["output"]
    if (type(output) is not list or len(output) > 8192
            or any(type(value) is not int or not 0 <= value <= 255 for value in output)
            or (previous is not None and output)):
        raise ValueError("invalid storage response")
    return bytes(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--stream", type=int, default=54)
    parser.add_argument("--generations", type=int, default=12)
    parser.add_argument("--steps", type=int, default=20)
    parser.add_argument("--arm", choices=("discrete", "hybrid"), default="hybrid")
    parser.add_argument("--budget", type=int)
    parser.add_argument("--transitions", type=int, default=368)
    parser.add_argument("--evaluation", choices=("local", "exchange"), default="local")
    parser.add_argument("--job-id", help="32-byte lowercase hex job identity; required for exchange")
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--kv-store", type=Path, help="new job store, or existing store with --resume-kv")
    parser.add_argument("--resume-kv", action="store_true")
    parser.add_argument("--allow-public-checkpoint-import", action="store_true",
                        help="declare this job's stored checkpoints Public; does not publish them")
    parser.add_argument("--storage-host", help="explicit path to the autoresearch-storage host example")
    parser.add_argument("--storage-package", type=Path,
                        default=Path(__file__).resolve().parent.parent / "autoresearch-store")
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="new directory; resume also preserves its input in a new directory")
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    lease = None
    try:
        storage_options(args)
        if not 0 <= args.transitions <= 368:
            raise ValueError("transition count must be in 0..368")
        initial = initial_request(args.seed, args.stream, args.generations, args.steps,
                                  args.arm == "hybrid", args.budget)
        package = args.package.resolve()
        identity = None
        if args.evaluation == "exchange":
            identity = evaluation_identity(args.sigil, package, args.job_id)
        elif args.job_id is not None:
            raise ValueError("--job-id requires --evaluation exchange")
        if args.kv_store is not None:
            if args.out_dir.exists() or args.out_dir.is_symlink():
                raise ValueError("output directory must be new")
            program = identity if identity is not None else evaluation_identity(args.sigil, package, "00" * 32)
            binding = command(b"ASKV", bytes([int(identity is not None)]) + program + initial)
            lease = open_store(args.kv_store, args.resume_kv, binding)
        if args.resume_kv:
            envelope = stored_checkpoint(args.storage_host, args.storage_package, args.kv_store)
            state = invoke(args.sigil, package, command(b"ASOP", initial + envelope))
        elif args.resume:
            sidecar = args.resume.parent / "evaluation-identity.hex"
            if identity is not None:
                if read_checkpoint(sidecar) != identity.hex().encode("ascii") + b"\n":
                    raise ValueError("resume requires the same evaluation job and program identity")
            elif sidecar.exists() or sidecar.is_symlink():
                raise ValueError("an exchange checkpoint must resume in exchange mode")
            envelope = read_checkpoint(args.resume)
            state = invoke(args.sigil, package, command(b"ASOP", initial + envelope))
        else:
            state = invoke(args.sigil, package, initial)
            envelope = invoke(args.sigil, package, command(b"ASCK", state))
        header(state)
        args.out_dir.mkdir()
        if identity is not None:
            write_new(args.out_dir / "evaluation-identity.hex", identity.hex().encode("ascii") + b"\n")
        path = publish(args.out_dir, state, envelope)
        if args.kv_store is not None and not args.resume_kv:
            stored_checkpoint(args.storage_host, args.storage_package, args.kv_store, b"", envelope)
        for _ in range(args.transitions):
            if header(state)[12] == 2:
                break
            if identity is not None and header(state)[12] == 0:
                next_state = exchange_step(args.sigil, package, state, identity, args.out_dir)
            else:
                next_state = invoke(args.sigil, package, command(b"ASST", state))
            next_envelope = invoke(args.sigil, package, command(b"ASAD", next_state + envelope))
            path = publish(args.out_dir, next_state, next_envelope)
            if args.kv_store is not None:
                stored_checkpoint(args.storage_host, args.storage_package, args.kv_store, envelope, next_envelope)
            state, envelope = next_state, next_envelope
        h = header(state)
        print(json.dumps({"checkpoint": str(path.resolve()), "complete": h[12] == 2,
                          "generation": h[10], "candidate_cursor": h[11], "transitions": h[13],
                          "candidates_evaluated": h[14], "candidate_budget": h[15],
                          "graph_evaluations": h[16], "fitting_accepted": h[17],
                          "fitting_rejected": h[18]}, sort_keys=True, indent=2))
        return 0
    except (OSError, ValueError, TypeError, KeyError, struct.error, RecursionError,
            subprocess.TimeoutExpired) as error:
        print(f"search refused: {error}", file=sys.stderr)
        return 1
    finally:
        if lease is not None:
            os.close(lease)


if __name__ == "__main__":
    raise SystemExit(main())
