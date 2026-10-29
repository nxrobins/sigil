"""Validate and transport candidate records; all loss and gradient work is native.

Unknown fields, duplicate keys, malformed native output and CLI failures refuse.
Request hashes identify bytes; they are not signatures or fitness attestations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import struct
import subprocess
import sys

FORMAT = "sigil-autoresearch-cpu-v1"
PROFILE = "saturating-f64-v1"
Q16_IMPORT = "q16-import-f64-v1"
KEYS = {"format", "numeric", "ops", "dst", "a", "b", "w"}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate candidate field: {key}")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f"nonfinite JSON token: {value}")


def validate(candidate: dict) -> dict:
    if type(candidate) is not dict or set(candidate) != KEYS:
        raise ValueError("candidate fields must be exactly format/numeric/ops/dst/a/b/w")
    if candidate["format"] != FORMAT or candidate["numeric"] not in (PROFILE, Q16_IMPORT):
        raise ValueError("unsupported candidate version or numerical profile")
    columns = [candidate[key] for key in ("ops", "dst", "a", "b")]
    if any(type(column) is not list for column in columns):
        raise ValueError("instruction columns must be arrays")
    count = len(columns[0])
    if not 1 <= count <= 12 or any(len(column) != count for column in columns):
        raise ValueError("candidate requires 1..12 equally sized instruction columns")
    for op, dst, a, b in zip(*columns, strict=True):
        if any(type(value) is not int for value in (op, dst, a, b)):
            raise ValueError("opcodes and operands must be integers, not booleans")
        if not (0 <= op <= 7 and 4 <= dst <= 15 and 0 <= a <= 15):
            raise ValueError("invalid opcode, writable destination or source register")
        ceiling = 7 if op in (4, 5, 6) else 15
        if not 0 <= b <= ceiling:
            raise ValueError("invalid second operand for the opcode")
    weights = candidate["w"]
    if type(weights) is not list or len(weights) != 8:
        raise ValueError("candidate requires exactly eight weights")
    if candidate["numeric"] == Q16_IMPORT:
        if any(type(w) is not int or not -268435456 <= w <= 268435456 for w in weights):
            raise ValueError("imported Q16 weights must be bounded signed integers")
        weights = [w / 65536 for w in weights]
    elif any(type(w) not in (int, float) or not -4096 <= w <= 4096 for w in weights):
        raise ValueError("weights must be finite numbers within [-4096,4096]")
    return {"format": FORMAT, "numeric": PROFILE,
            **{key: list(candidate[key]) for key in ("ops", "dst", "a", "b")},
            "w": [float(w) for w in weights]}


def read_candidate(path: Path) -> dict:
    with path.open("rb") as source:
        raw = source.read(16385)
    if len(raw) > 16384:
        raise ValueError("candidate JSON exceeds 16384 bytes")
    return validate(json.loads(raw, object_pairs_hook=unique_object, parse_constant=reject_constant))


def encode(candidate: dict, steps: int) -> bytes:
    candidate = validate(candidate)
    if type(steps) is not int or not 0 <= steps <= 20:
        raise ValueError("inner steps must be an integer in 0..20")
    instructions = bytes(value for row in zip(
        candidate["ops"], candidate["dst"], candidate["a"], candidate["b"], strict=True,
    ) for value in row)
    return (b"ACPU" + bytes([1, steps, len(candidate["ops"]), 1])
            + struct.pack("<8d", *candidate["w"]) + instructions)


def decode(output: bytes, request: bytes) -> dict:
    if len(output) != 144 + len(request) or output[144:] != request:
        raise ValueError("native report size or echoed request does not match")
    version, steps, count, nodes = struct.unpack_from("<4q", output)
    if (version, steps, count) != (1, request[5], request[6]) or not 24 <= nodes <= 768:
        raise ValueError("native report header is invalid")
    values = struct.unpack_from("<14d", output, 32)
    if not all(math.isfinite(value) for value in values):
        raise ValueError("native report contains nonfinite data")
    if values[0] < 0 or values[1] < values[0]:
        raise ValueError("native loss or complexity-penalized fitness is invalid")
    return {"format": "sigil-autoresearch-result-v1", "numeric": PROFILE,
            "request_sha256": hashlib.sha256(request).hexdigest(),
            "inner_steps": steps, "instruction_count": count, "tape_nodes": nodes,
            "loss": values[0], "fitness": values[1],
            "positions": list(values[2:4]), "momentum": list(values[4:6]),
            "gradient": list(values[6:14])}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--steps", type=int, choices=range(21), default=20)
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        candidate = read_candidate(args.candidate)
        request = encode(candidate, args.steps)
        completed = subprocess.run(
            [args.sigil, "run", "--package", str(args.package.resolve()), "--input",
             request.hex(), "--fuel", "500000", "--json"],
            capture_output=True, text=True, timeout=60, check=False,
        )
        envelope = json.loads(completed.stdout)
        if (completed.returncode or type(envelope) is not dict
                or envelope.get("status") != "ok"):
            raise ValueError("native CLI refused candidate evaluation")
        payload = envelope["data"]["output"]
        if (type(payload) is not list or len(payload) != 144 + len(request)
                or any(type(value) is not int or not 0 <= value <= 255 for value in payload)):
            raise ValueError("native output is not the bounded report byte array")
        result = decode(bytes(payload), request)
        result["candidate_sha256"] = hashlib.sha256(json.dumps(
            candidate, sort_keys=True, separators=(",", ":"), allow_nan=False,
        ).encode()).hexdigest()
        print(json.dumps(result, sort_keys=True, indent=2, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError,
            subprocess.TimeoutExpired) as error:
        print(f"candidate evaluation refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
