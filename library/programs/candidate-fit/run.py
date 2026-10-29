"""Display the native candidate-fitting ABI without computing gradients or updates."""

from __future__ import annotations

import argparse
import json
import math
import struct
import subprocess
import sys
from pathlib import Path


def decode(output: bytes, candidate: int, steps: int) -> dict:
    if len(output) != 304:
        raise ValueError("candidate fitting must return exactly 304 bytes")
    actual_candidate, actual_steps = struct.unpack_from("<2q", output)
    if (actual_candidate, actual_steps) != (candidate, steps):
        raise ValueError("native candidate/steps do not match the request")
    values = struct.unpack_from("<36d", output, 16)
    if not all(math.isfinite(value) for value in values):
        raise ValueError("native candidate fitting returned nonfinite data")
    return {"format": "candidate-fit-v2", "candidate": actual_candidate, "steps": actual_steps,
            "initial_loss": values[0], "final_loss": values[1],
            "initial_validation_loss": values[2], "validation_loss": values[3],
            "initial_constants": list(values[4:12]), "constants": list(values[12:20]),
            "initial_gradient": list(values[20:28]), "gradient": list(values[28:36])}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--candidate", type=int, choices=[0, 1], default=0)
    parser.add_argument("--steps", type=int, choices=range(17), default=16)
    args = parser.parse_args()
    try:
        completed = subprocess.run(
            [args.sigil, "run", "--package", str(args.package.resolve()), "--input",
             f"{args.candidate}:{args.steps}", "--fuel", "500000", "--json"],
            capture_output=True, text=True, timeout=60, check=False,
        )
        envelope = json.loads(completed.stdout)
        if completed.returncode or not isinstance(envelope, dict) or envelope.get("status") != "ok":
            print(json.dumps(envelope, indent=2), file=sys.stderr)
            return 1
        payload = envelope["data"]["output"]
        if (not isinstance(payload, list) or len(payload) != 304
                or any(type(value) is not int or not 0 <= value <= 255 for value in payload)):
            raise ValueError("native output must be a 304-byte array")
        print(json.dumps(decode(bytes(payload), args.candidate, args.steps),
                         indent=2, allow_nan=False))
        return 0
    except (OSError, subprocess.TimeoutExpired, ValueError, KeyError, TypeError) as error:
        # Invalid native output refuses; never substitute host-computed answers.
        print(f"native candidate fitting refused or output is invalid: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
