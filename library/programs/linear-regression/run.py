"""Display the native SIGIL training ABI; never compute or substitute model results."""

from __future__ import annotations

import argparse
import json
import math
import struct
import subprocess
import sys
from pathlib import Path

FIELDS = (
    "initial_loss", "final_loss", "bias", "slope", "initial_gradient_bias",
    "initial_gradient_slope", "final_gradient_bias", "final_gradient_slope", "validation_loss",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sigil", default="sigil")
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--steps", type=int, default=100, choices=range(201))
    args = parser.parse_args()
    root = args.package.resolve()
    try:
        completed = subprocess.run(
            [args.sigil, "run", "--package", str(root), "--input", str(args.steps),
             "--fuel", "250000", "--json"],
            capture_output=True, text=True, timeout=60, check=False,
        )
        envelope = json.loads(completed.stdout)
        if completed.returncode or envelope.get("status") != "ok":
            print(json.dumps(envelope, indent=2), file=sys.stderr)
            return 1
        raw = bytes(envelope["data"]["output"])
        if len(raw) != 72:
            raise ValueError("native training output must contain exactly nine f64 values")
        values = struct.unpack("<9d", raw)
        if not all(math.isfinite(value) for value in values):
            raise ValueError("native training output contains nonfinite data")
        print(json.dumps(dict(zip(FIELDS, values, strict=True)), indent=2))
        return 0
    except (OSError, subprocess.TimeoutExpired, ValueError, KeyError, TypeError) as error:
        print(f"native training refused or output is invalid: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
