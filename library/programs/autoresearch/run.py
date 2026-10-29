"""Validate/display native fitting results; never fit or evaluate on the host."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import struct
import subprocess
import sys

SPEC = importlib.util.spec_from_file_location(
    "autoresearch_cpu_transport", Path(__file__).resolve().parent.parent / "autoresearch-cpu/run.py")
CPU = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CPU)
FORMAT = "sigil-autoresearch-fit-v1"
RECORD_FORMAT = "sigil-autoresearch-fit-record-v1"
RECORD_FIELDS = {"header_le": 64, "summary_f64le": 24, "weights_f64le": 64,
                 "accepted_f64le": 112, "decisions_le": 48, "trace_f64le": 528}


def encode(candidate, steps, rounds, *, record=False):
    if type(record) is not bool:
        raise ValueError("record selection must be a boolean")
    if type(rounds) is not int or not 0 <= rounds <= 6:
        raise ValueError("fitting rounds must be an integer in 0..6")
    wire = CPU.encode(candidate, steps)
    if (rounds + 1) * (24 + steps * (7 + 2 * wire[6])) > 2600:
        raise ValueError("fitting request exceeds the 2600-node total work bound; use fewer rounds")
    return b"AFIT" + bytes([2 if record else 1, rounds, 0, 0]) + wire


def unique_fields(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate fitting record field")
        result[key] = value
    return result


def decode_record(output, request):
    """Validate a native record; reconstruct bytes only, never recompute a score."""
    if len(output) > 4096 or request[:5] != b"AFIT\x02":
        raise ValueError("invalid fitting record size or request version")
    data = json.loads(output, object_pairs_hook=unique_fields)
    fields = {*RECORD_FIELDS, "request_hex", "format", "numeric"}
    if (type(data) is not dict or set(data) != fields
            or data["format"] != RECORD_FORMAT or data["numeric"] != "binary64le-hex-v1"):
        raise ValueError("incompatible fitting record schema")
    decoded = {}
    for key, size in {**RECORD_FIELDS, "request_hex": len(request)}.items():
        value = data[key]
        if (type(value) is not str or len(value) != size * 2
                or any(c not in "0123456789abcdef" for c in value)):
            raise ValueError("noncanonical fitting record bytes")
        decoded[key] = bytes.fromhex(value)
    if decoded["request_hex"] != request:
        raise ValueError("fitting record identifies another request")
    binary = b"".join(decoded[key] for key in RECORD_FIELDS) + request
    return decode(binary, request)


def decode(output, request):
    if len(output) != 840 + len(request) or output[840:] != request:
        raise ValueError("native fitting report length or request echo differs")
    version, steps, count, rounds, attempted, accepted, rejected, stopped = struct.unpack_from("<8q", output)
    if (version, steps, count, rounds) != (1, request[13], request[14], request[5]):
        raise ValueError("native fitting report identifies another request")
    if (not 0 <= accepted <= attempted <= rounds or not 0 <= rejected <= attempted
            or accepted + rejected != attempted or stopped not in (0, 1)
            or stopped != int(attempted < rounds)):
        raise ValueError("invalid native fitting counters")
    initial_loss, initial_fitness, next_step = struct.unpack_from("<3d", output, 64)
    weights = list(struct.unpack_from("<8d", output, 88))
    values = list(struct.unpack_from("<14d", output, 152))
    decisions = struct.unpack_from("<6q", output, 264)
    trace = struct.unpack_from("<66d", output, 312)
    if not all(math.isfinite(v) for v in (initial_loss, initial_fitness, next_step, *weights, *values, *trace)):
        raise ValueError("native fitting report contains nonfinite data")
    if (initial_loss < 0 or values[0] < 0 or any(not -4096 <= w <= 4096 for w in weights)
            or initial_fitness != initial_loss + count * (66 / 65536)
            or values[1] != values[0] + count * (66 / 65536)):
        raise ValueError("invalid native weights or loss/fitness relationship")
    current_fitness, rate = initial_fitness, 3277 / 65536
    history = []
    for index in range(6):
        row = trace[index * 11:(index + 1) * 11]
        decision = decisions[index]
        if index >= attempted:
            if decision != -1 or any(value != 0 for value in row):
                raise ValueError("unused fitting rows must be empty")
            continue
        step, base, proposal, *gradient = row
        if (step != rate or base != current_fitness or proposal < 0
                or decision not in (0, 1) or decision != int(proposal < base)
                or not any(g != 0 for g in gradient)):
            raise ValueError("invalid fitting decision or state transition")
        history.append({"step": step, "base_fitness": base, "proposal_fitness": proposal,
                        "gradient": gradient, "accepted": bool(decision)})
        if decision:
            current_fitness, rate = proposal, min(rate * 1.5, 13107 / 65536)
        else:
            rate /= 2
    if (sum(decisions[:attempted]) != accepted or values[1] != current_fitness
            or next_step != rate or (stopped and any(v != 0 for v in values[6:]))):
        raise ValueError("final fitting report does not match the accepted history")
    wire = request[8:]
    instructions = [wire[i:i + 4] for i in range(72, len(wire), 4)]
    candidate = CPU.validate({
        "format": CPU.FORMAT, "numeric": CPU.PROFILE, "w": weights,
        **{key: [row[i] for row in instructions] for i, key in enumerate(("ops", "dst", "a", "b"))},
    })
    if attempted == 0 and weights != list(struct.unpack_from("<8d", wire, 8)):
        raise ValueError("zero-attempt result changed the candidate")
    return {"format": FORMAT, "numeric": CPU.PROFILE, "candidate": candidate,
            "request_sha256": hashlib.sha256(request).hexdigest(), "inner_steps": steps,
            "rounds_requested": rounds, "attempted": attempted, "accepted": accepted,
            "rejected": rejected, "stopped_zero_gradient": bool(stopped),
            "initial_loss": initial_loss, "initial_fitness": initial_fitness,
            "next_step": next_step, "loss": values[0], "fitness": values[1],
            "positions": values[2:4], "momentum": values[4:6], "gradient": values[6:],
            "history": history}


def publish_candidate(path, candidate):
    content = json.dumps(CPU.validate(candidate), sort_keys=True, indent=2, allow_nan=False) + "\n"
    with path.open("x", encoding="utf-8") as destination:
        destination.write(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--rounds", type=int, choices=range(7), default=3)
    parser.add_argument("--steps", type=int, choices=range(21), default=20)
    parser.add_argument("--candidate-out", type=Path)
    parser.add_argument("--record", action="store_true",
                        help="emit the validated native exact-bit JSON record instead of the display summary")
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        request = encode(CPU.read_candidate(args.candidate), args.steps, args.rounds, record=args.record)
        completed = subprocess.run(
            [args.sigil, "run", "--package", str(args.package.resolve()), "--input",
             request.hex(), "--fuel", "500000", "--json"],
            capture_output=True, text=True, timeout=60, check=False)
        envelope = json.loads(completed.stdout)
        if completed.returncode or type(envelope) is not dict or envelope.get("status") != "ok":
            raise ValueError("native CLI refused candidate fitting")
        payload = envelope["data"]["output"]
        if (type(payload) is not list or len(payload) > 4096
                or any(type(v) is not int or not 0 <= v <= 255 for v in payload)):
            raise ValueError("native output is not the fitting report byte array")
        raw = bytes(payload)
        result = decode_record(raw, request) if args.record else decode(raw, request)
        if args.candidate_out:
            publish_candidate(args.candidate_out, result["candidate"])
        print(raw.decode("ascii") if args.record else json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError, RecursionError, subprocess.TimeoutExpired) as error:
        print(f"candidate fitting refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
