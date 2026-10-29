"""Emit independent CPU PyTorch answers, only with explicit generation opt-in.

This interpreter does not import the native wrapper or execute SIGIL. Its input
fixtures preserve the original Q16 seed weights, then use the documented f64
profile. torch.where deliberately makes clip derivatives zero at endpoints.
"""

from __future__ import annotations

import copy
import json
import math
import os
from pathlib import Path
import struct
import sys


def main() -> int:
    if os.environ.get("SIGIL_GENERATE_AUTORESEARCH_REFERENCE") != "1":
        print("set SIGIL_GENERATE_AUTORESEARCH_REFERENCE=1 to emit answers", file=sys.stderr)
        return 2
    import torch

    if torch.__version__.split("+", 1)[0] != "2.14.1":
        raise RuntimeError("reference generation requires PyTorch 2.14.1")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)

    def scalar(value):
        return torch.tensor(value, dtype=torch.float64)

    def clipped(value, low=-4096., high=4096.):
        return torch.where(value <= low, scalar(low),
                           torch.where(value >= high, scalar(high), value))

    def evaluate(candidate, weights, steps):
        positions, momentum = [scalar(-4.), scalar(3.)], [scalar(0.), scalar(0.)]
        for step in range(steps):
            for coordinate, (target, curvature) in enumerate([(3., 2.), (-2., 100.)]):
                registers = [scalar(0.) for _ in range(16)]
                registers[0] = clipped((positions[coordinate] - target) * curvature)
                registers[1] = registers[15] = momentum[coordinate]
                registers[2], registers[3] = scalar(step / 20.), scalar(1.)
                for op, dst, a, b in zip(candidate["ops"], candidate["dst"],
                                        candidate["a"], candidate["b"], strict=True):
                    left = registers[a]
                    right = weights[b] if op in (4, 5, 6) else registers[b]
                    if op in (0, 5):
                        value = left + right
                    elif op == 1:
                        value = left - right
                    elif op in (2, 4, 6):
                        value = left * right
                    elif op == 3:
                        value = torch.relu(left)
                    else:
                        assert op == 7
                        value = -left
                    registers[dst] = clipped(value, 0., 1.) if op == 6 else clipped(value)
                positions[coordinate] = clipped(positions[coordinate] + registers[14])
                momentum[coordinate] = registers[15]
        loss = (positions[0] - 3.) ** 2 + 50. * (positions[1] + 2.) ** 2
        # Preserve the eight-variable query even for disconnected/constant graphs.
        loss = loss + 0. * weights.sum()
        return loss, positions, momentum

    fixture_dir = Path(__file__).resolve().parents[3] / "examples/autoresearch-cpu/candidates"
    seeds = {name: json.loads((fixture_dir / f"{name}.json").read_text())
             for name in ("sgd", "momentum", "step-decay")}
    requests = [(f"{name}-{steps}", seed, steps, False)
                for name, seed in seeds.items() for steps in (0, 1, 2, 5, 10, 20)]

    def candidate(ops, dst, a, b, w):
        return {"format": "sigil-autoresearch-cpu-v1", "numeric": "saturating-f64-v1",
                "ops": ops, "dst": dst, "a": a, "b": b, "w": w}

    for name, weights in [("sgd", [-.01, 0., 0., 0., 0., 0., 0., 0.]),
                          ("momentum", [-.01, .8, 0., 0., 0., 0., 0., 0.])]:
        changed = copy.deepcopy(seeds[name])
        changed.update(numeric="saturating-f64-v1", w=weights)
        requests.append((f"stable-{name}-20", changed, 20, True))
    for op in range(8):
        item = candidate([op], [14], [3], [0 if op in (4, 5, 6) else 3], [.25] * 8)
        requests.append((f"opcode-{op}", item, 1, True))
    for value in (-1., 0., .25, 1., 2.):
        item = candidate([6], [14], [3], [0], [value] + [0.] * 7)
        requests.append((f"step-{value}", item, 1, value not in (0., 1.)))
    for sign in (-1., 1.):
        for magnitude in (4094., 4095., 4096.):
            item = candidate([7 if sign < 0 else 0, 5], [4, 14], [3, 4], [0, 0],
                             [sign * magnitude] + [0.] * 7)
            # ADD(1, r1=0) or NEG(1) prepares +/-1; endpoint = +/-4095 +/-1.
            item["b"][0] = 1
            requests.append((f"clip-{sign * magnitude}", item, 1, False))
    all_weights = candidate([5] * 8, [14] * 8, [3] + [14] * 7,
                            list(range(8)), [.01] * 8)
    requests.append(("all-eight-weights", all_weights, 2, True))
    maximum = candidate([0] * 11 + [4], [4] * 11 + [14], [3] * 11 + [0],
                        [1] * 11 + [0], [-.01] + [0.] * 7)
    requests.append(("maximum-12x20", maximum, 20, True))

    cases = []
    for name, record, steps, finite_differences in requests:
        weights = [float(w) / 65536 if record["numeric"] == "q16-import-f64-v1" else float(w)
                   for w in record["w"]]
        tensor = torch.tensor(weights, dtype=torch.float64, requires_grad=True)
        loss, positions, momentum = evaluate(record, tensor, steps)
        gradient, = torch.autograd.grad(loss, tensor)
        penalty = sum(66. / 65536 for _ in record["ops"])
        expected = [loss.item(), loss.item() + penalty,
                    *(p.item() for p in positions), *(m.item() for m in momentum),
                    *gradient.tolist()]
        assert len(expected) == 14 and all(math.isfinite(v) for v in expected)
        wire = (b"ACPU" + bytes([1, steps, len(record["ops"]), 1])
                + struct.pack("<8d", *weights)
                + bytes(v for row in zip(record["ops"], record["dst"], record["a"],
                                         record["b"], strict=True) for v in row))
        case = {"name": name, "candidate": record, "steps": steps,
                "request_hex": wire.hex(), "expected": expected}
        if finite_differences:
            differences = []
            for index in range(8):
                plus, minus = tensor.detach().clone(), tensor.detach().clone()
                plus[index] += 1e-7
                minus[index] -= 1e-7
                differences.append(((evaluate(record, plus, steps)[0]
                                     - evaluate(record, minus, steps)[0]) / 2e-7).item())
            case["finite_difference"] = differences
        cases.append(case)
    json.dump({"format": "sigil-autoresearch-cpu-torch-v1",
               "reference": {"torch": "2.14.1", "device": "cpu", "dtype": "float64",
                             "atol": 1e-10, "rtol": 1e-10,
                             "finite_difference_atol": 2e-4,
                             "finite_difference_rtol": 2e-6}, "cases": cases},
              sys.stdout, sort_keys=True, indent=2, allow_nan=False)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
