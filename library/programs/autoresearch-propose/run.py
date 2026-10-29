"""Transport native candidate proposals; no random or mutation logic runs here."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

SPEC = importlib.util.spec_from_file_location(
    "autoresearch_cpu_transport", Path(__file__).resolve().parent.parent / "autoresearch-cpu/run.py")
CPU = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CPU)
FORMAT = "sigil-autoresearch-proposal-v1"
ALGORITHM = "pcg-xsh-rr-64-32-v1"
KEYS = {"format", "algorithm", "candidate", "steps", "state", "increment",
        "mutation", "request_sha256"}


def word(value):
    if type(value) is not str or re.fullmatch("[0-9a-f]{16}", value) is None:
        raise ValueError("RNG words must be canonical 16-digit lowercase hex strings")
    return int(value, 16)


def validate_checkpoint(record):
    if type(record) is not dict or set(record) != KEYS:
        raise ValueError("proposal checkpoint has missing or unknown fields")
    if record["format"] != FORMAT or record["algorithm"] != ALGORITHM:
        raise ValueError("incompatible proposal or RNG algorithm")
    if (type(record["mutation"]) is not int or not 0 <= record["mutation"] <= 5
            or type(record["request_sha256"]) is not str
            or re.fullmatch("[0-9a-f]{64}", record["request_sha256"]) is None):
        raise ValueError("invalid mutation or request identity")
    word(record["state"])
    if word(record["increment"]) % 2 != 1:
        raise ValueError("RNG increment must be odd")
    candidate = CPU.validate(record["candidate"])
    if record["candidate"]["numeric"] != CPU.PROFILE:
        raise ValueError("checkpoint candidate must already use the canonical numerical profile")
    CPU.encode(candidate, record["steps"])
    return {**record, "candidate": candidate}


def read_checkpoint(path):
    with path.open("rb") as source:
        raw = source.read(16385)
    if len(raw) > 16384:
        raise ValueError("checkpoint exceeds 16384 bytes")
    return validate_checkpoint(json.loads(
        raw, object_pairs_hook=CPU.unique_object, parse_constant=CPU.reject_constant))


def encode(candidate=None, steps=20, seed=None, stream=None, resume=None):
    if resume is not None:
        if candidate is not None or seed is not None or stream is not None:
            raise ValueError("resume cannot be combined with a new candidate or seed")
        record = validate_checkpoint(resume)
        mode, first, second = 1, word(record["state"]), word(record["increment"])
        body = CPU.encode(record["candidate"], record["steps"])
    else:
        if (type(seed) is not int or not 0 <= seed < 2**64
                or type(stream) is not int or not 0 <= stream < 2**63):
            raise ValueError("seed must be u64 and stream must be in 0..2^63-1")
        mode, first, second = 0, seed, stream
        body = CPU.encode(candidate, steps)
    return b"APRP" + bytes([1, mode, 0, 0]) + struct.pack("<2Q", first, second) + body


def candidate_from_wire(wire):
    if not 76 <= len(wire) <= 120 or wire[:5] != b"ACPU\x01" or wire[7] != 1:
        raise ValueError("invalid candidate response framing")
    count = wire[6]
    if len(wire) != 72 + count * 4:
        raise ValueError("invalid response instruction count")
    rows = [wire[i:i + 4] for i in range(72, len(wire), 4)]
    candidate = {"format": CPU.FORMAT, "numeric": CPU.PROFILE,
                 "w": list(struct.unpack_from("<8d", wire, 8)),
                 **{key: [row[i] for row in rows]
                    for i, key in enumerate(("ops", "dst", "a", "b"))}}
    candidate = CPU.validate(candidate)
    if CPU.encode(candidate, wire[5]) != wire:
        raise ValueError("noncanonical native candidate")
    return candidate


def decode(output, request):
    if not 216 <= len(output) <= 304:
        raise ValueError("invalid native proposal length")
    version, state, increment, kind, length = struct.unpack_from("<5Q", output)
    if (version != 1 or increment % 2 != 1 or kind > 5 or not 76 <= length <= 120
            or len(output) != 40 + length + len(request)
            or output[40 + length:] != request):
        raise ValueError("invalid native header or request echo")
    original = struct.unpack_from("<Q", request, 16)[0]
    expected_increment = original if request[5] == 1 else 2 * original + 1
    if increment != expected_increment:
        raise ValueError("native proposal changed the RNG stream")
    wire = output[40:40 + length]
    if wire[5] != request[29]:
        raise ValueError("native proposal changed the task step count")
    record = {"format": FORMAT, "algorithm": ALGORITHM,
              "state": f"{state:016x}", "increment": f"{increment:016x}",
              "candidate": candidate_from_wire(wire), "steps": wire[5], "mutation": kind,
              "request_sha256": hashlib.sha256(request).hexdigest()}
    return validate_checkpoint(record)


def publish_candidate(path, candidate):
    # Exclusive creation refuses existing files and symlinks; no old state is overwritten.
    content = json.dumps(CPU.validate(candidate), sort_keys=True, indent=2, allow_nan=False) + "\n"
    with path.open("x", encoding="utf-8") as destination:
        destination.write(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--seed", type=int)
    parser.add_argument("--stream", type=int)
    parser.add_argument("--steps", type=int)
    parser.add_argument("--candidate-out", type=Path)
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        if args.resume:
            if any(value is not None for value in (args.candidate, args.seed, args.stream, args.steps)):
                raise ValueError("resume is exclusive of candidate, seed, stream and steps")
            request = encode(resume=read_checkpoint(args.resume))
        else:
            if args.candidate is None or args.seed is None:
                raise ValueError("a new proposal requires --candidate and --seed")
            request = encode(CPU.read_candidate(args.candidate),
                             20 if args.steps is None else args.steps, args.seed,
                             0 if args.stream is None else args.stream)
        completed = subprocess.run(
            [args.sigil, "run", "--package", str(args.package.resolve()), "--input",
             request.hex(), "--fuel", "500000", "--json"],
            capture_output=True, text=True, timeout=60, check=False)
        envelope = json.loads(completed.stdout)
        if (completed.returncode or type(envelope) is not dict
                or envelope.get("status") != "ok"):
            raise ValueError("native CLI refused candidate mutation")
        payload = envelope["data"]["output"]
        if (type(payload) is not list or not 216 <= len(payload) <= 304
                or any(type(value) is not int or not 0 <= value <= 255 for value in payload)):
            raise ValueError("native output is not a bounded byte array")
        record = decode(bytes(payload), request)
        if args.candidate_out:
            publish_candidate(args.candidate_out, record["candidate"])
        print(json.dumps(record, indent=2, sort_keys=True, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError,
            subprocess.TimeoutExpired) as error:
        print(f"candidate proposal refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
