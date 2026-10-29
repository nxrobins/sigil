"""Generate fitting answers with fresh pinned CPU PyTorch, never with SIGIL."""
from __future__ import annotations

import copy
import json
import math
import os
from pathlib import Path
import struct


def main():
    if os.environ.get("SIGIL_GENERATE_AUTORESEARCH_FIT_REFERENCE") != "1":
        raise SystemExit("Set SIGIL_GENERATE_AUTORESEARCH_FIT_REFERENCE=1 to execute the reference")
    import torch
    if torch.__version__.split("+", 1)[0] != "2.14.1":
        raise RuntimeError("reference requires PyTorch 2.14.1")
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


    root = Path(__file__).resolve().parents[1]
    original = json.loads((root / "autoresearch-cpu/torch-v1.json").read_text())["cases"]
    by_name = {case["name"]: case for case in original}
    requests = [(case["name"] + "-fit-0", case["candidate"], case["steps"], 0) for case in original]
    for name in ("sgd-20", "momentum-20", "step-decay-20"):
        for rounds in (1, 3, 6):
            case = by_name[name]
            if name == "step-decay-20" and rounds == 6:
                rounds = 4
            requests.append((name + f"-fit-{rounds}", case["candidate"], case["steps"], rounds))
    for name in ("stable-sgd-20", "stable-momentum-20", "maximum-12x20",
                 "all-eight-weights", "step-0.25", "step-1.0", "sgd-0"):
        case = by_name[name]
        rounds = 3 if name == "maximum-12x20" else 6
        requests.append((name + f"-fit-{rounds}", case["candidate"], case["steps"], rounds))
    growing = {"format": "sigil-autoresearch-cpu-v1", "numeric": "saturating-f64-v1",
               "ops": [5], "dst": [14], "a": [1], "b": [0], "w": [0.] * 8}
    requests.append(("growing-rate-cap-fit-6", growing, 1, 6))
    cases = []
    for name, record, steps, rounds in requests:
        assert (rounds + 1) * (24 + steps * (7 + 2 * len(record["ops"]))) <= 2600
        initial_weights = [float(w) / 65536 if record["numeric"] == "q16-import-f64-v1" else float(w)
                           for w in record["w"]]
        weights = torch.tensor(initial_weights, dtype=torch.float64)
        penalty = sum(66. / 65536 for _ in record["ops"])

        def measured(values):
            values = values.detach().clone().requires_grad_(True)
            loss, positions, momentum = evaluate(record, values, steps)
            gradient, = torch.autograd.grad(loss, values)
            result = [loss.item(), loss.item() + penalty, *(p.item() for p in positions),
                      *(m.item() for m in momentum), *gradient.tolist()]
            assert all(math.isfinite(value) for value in result), name
            return result

        report = measured(weights)
        initial_loss, initial_fitness = report[:2]
        rate = 3277. / 65536
        history, decisions = [], []
        stopped = 0
        for _ in range(rounds):
            gradient = torch.tensor(report[6:], dtype=torch.float64)
            if not bool(torch.any(gradient != 0)):
                stopped = 1
                break
            proposed = torch.clamp(weights - rate * torch.sign(gradient), -4096., 4096.)
            trial = measured(proposed)
            history.append([rate, report[1], trial[1], *report[6:]])
            accepted = trial[1] < report[1]
            decisions.append(int(accepted))
            if accepted:
                weights, report = proposed, trial
                rate = min(rate * 1.5, 13107. / 65536)
            else:
                rate /= 2
        attempted, accepted = len(decisions), sum(decisions)
        wire = (b"AFIT" + bytes([1, rounds, 0, 0]) + b"ACPU"
                + bytes([1, steps, len(record["ops"]), 1])
                + struct.pack("<8d", *initial_weights)
                + bytes(v for row in zip(record["ops"], record["dst"], record["a"], record["b"], strict=True)
                        for v in row))
        numbers = [initial_loss, initial_fitness, rate, *weights.tolist(), *report]
        numbers.extend(value for row in history for value in row)
        numbers.extend([0.] * ((6 - attempted) * 11))
        assert len(numbers) == 91 and all(math.isfinite(v) for v in numbers)
        cases.append({"name": name, "candidate": copy.deepcopy(record), "steps": steps, "rounds": rounds,
                      "request_hex": wire.hex(), "expected_header":
                      [1, steps, len(record["ops"]), rounds, attempted, accepted, attempted - accepted, stopped],
                      "decisions": decisions + [-1] * (6 - attempted), "expected_numbers": numbers})
    assert len(cases) == 58
    print(json.dumps({"format": "sigil-autoresearch-fit-torch-v1",
                      "reference": {"torch": "2.14.1", "device": "cpu", "dtype": "float64",
                                    "atol": 1e-10, "rtol": 1e-10}, "cases": cases},
                     indent=2, sort_keys=True, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
