"""Explicitly regenerate PCG answers by compiling the pinned upstream C code."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    if os.environ.get("SIGIL_REGENERATE_RNG") != "1":
        raise SystemExit("Set SIGIL_REGENERATE_RNG=1 to execute the C reference")
    root = Path(__file__).resolve().parent
    cases = []
    with tempfile.TemporaryDirectory(prefix="sigil-pcg-reference-") as directory:
        executable = Path(directory) / "reference"
        subprocess.run(["cc", "-std=c99", "-Wall", "-Wextra", "-Werror",
                        str(root / "reference.c"), str(root / "upstream/pcg_basic.c"),
                        "-o", str(executable)], check=True)
        for seed, stream in ((42, 54), (0, 0), (1, 1),
                             (2**64 - 1, 2**63 - 1), (2**63, 17)):
            for bound in (0, 1, 6, 2**31 + 1, 2**32 - 1, 2**32):
                result = subprocess.run([str(executable), str(seed), str(stream), str(bound)],
                                        check=True, capture_output=True, text=True)
                rows = [[int(word) for word in row.split()] for row in result.stdout.splitlines()]
                cases.append({"seed": seed, "stream": stream, "bound": bound,
                              "initial": rows[0], "draws": rows[1:]})
    sources = {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in sorted([root / "reference.c", *root.glob("upstream/*")])}
    print(json.dumps({"format": "sigil-pcg-reference-v1",
                      "upstream_revision": "bc39cd76ac3d541e618606bcc6e1e5ba5e5e6aa3",
                      "sources": sources, "cases": cases}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
