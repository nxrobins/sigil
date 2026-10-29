"""Independent CPU PyTorch regression oracle; never imports or executes SIGIL.

Inner gradients come from autograd on individual training observations, not the
native sufficient-statistic formula. Validation data is available only to report.
The explicit generator below is the only writer of the reference answer file.
"""
from __future__ import annotations

import copy
import json
import math
from pathlib import Path
import struct

ROOT = Path(__file__).resolve().parents[3]
DATASET = json.loads((ROOT / "programs/autoresearch-regression/dataset.json").read_text())


def measure(p, weights, steps, *, dataset=DATASET):
    import torch

    def scalar(value):
        return torch.tensor(value, dtype=torch.float64)

    def clip(value, low=-4096., high=4096.):
        return torch.where(value <= low, scalar(low), torch.where(value >= high, scalar(high), value))

    w = torch.tensor(weights, dtype=torch.float64, requires_grad=True)
    positions = torch.tensor([-1., .5], dtype=torch.float64, requires_grad=True)
    momentum = [scalar(0.), scalar(0.)]
    observations = torch.tensor(dataset["train"], dtype=torch.float64)
    x, y = observations[:, 0], observations[:, 1]
    for step in range(steps):
        predictions = positions[0] * x + positions[1]
        training = torch.mean((predictions - y) ** 2)
        inner_gradient, = torch.autograd.grad(training, positions, create_graph=True)
        following = []
        for k in range(2):
            registers = [scalar(0.) for _ in range(16)]
            registers[0] = clip(inner_gradient[k])
            registers[1] = registers[15] = momentum[k]
            registers[2], registers[3] = scalar(step / 12.), scalar(1.)
            for op, dst, a, b in zip(p["ops"], p["dst"], p["a"], p["b"], strict=True):
                left, right = registers[a], w[b] if op in (4, 5, 6) else registers[b]
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
                registers[dst] = clip(value, 0., 1.) if op == 6 else clip(value)
            following.append(clip(positions[k] + registers[14]))
            momentum[k] = registers[15]
        positions = torch.stack(following)
    loss = torch.mean((positions[0] * x + positions[1] - y) ** 2) + 0. * w.sum()
    gradient, = torch.autograd.grad(loss, w)
    values = [loss.item(), loss.item() + len(p["ops"]) * (66. / 65536.),
              *positions.detach().tolist(), *(m.item() for m in momentum), *gradient.tolist()]
    assert all(math.isfinite(v) for v in values)
    return values


def validation(parameters, *, dataset=DATASET):
    import torch

    rows = torch.tensor(dataset["validation"], dtype=torch.float64)
    return torch.mean((parameters[0] * rows[:, 0] + parameters[1] - rows[:, 1]) ** 2).item()


def fit(p, steps, rounds):
    import torch

    weights = torch.tensor(p["w"], dtype=torch.float64)
    initial = measure(p, weights.tolist(), steps)
    result, rate, history, decisions, stopped = initial, 3277. / 65536., [], [], 0
    for _ in range(rounds):
        gradient = torch.tensor(result[6:], dtype=torch.float64)
        if not bool(torch.any(gradient != 0)):
            stopped = 1
            break
        proposed = torch.clamp(weights - rate * torch.sign(gradient), -4096., 4096.)
        trial = measure(p, proposed.tolist(), steps)
        history.append([rate, result[1], trial[1], *result[6:]])
        accept = trial[1] < result[1]
        decisions.append(int(accept))
        if accept:
            weights, result = proposed, trial
            rate = min(rate * 1.5, 13107. / 65536.)
        else:
            rate /= 2
    p["w"], p["loss"], p["fitness"] = weights.tolist(), result[0], result[1]
    attempted, accepted = len(decisions), sum(decisions)
    numbers = [initial[0], initial[1], rate, *weights.tolist(), *result]
    numbers += [v for row in history for v in row] + [0.] * (66 - 11 * attempted)
    return {"header": [1, steps, len(p["ops"]), rounds, attempted, accepted, attempted - accepted, stopped],
            "numbers": numbers, "decisions": decisions + [-1] * (6 - attempted),
            "validation_loss": validation(result[2:4])}


def seeds():
    values = []
    for lineage, name in enumerate(("sgd", "momentum", "step-decay")):
        record = json.loads((ROOT / f"programs/autoresearch-cpu/candidates/{name}.json").read_text())
        record["w"] = [value / 65536. for value in record["w"]]
        record.update(lineage=lineage, loss=0., fitness=0.)
        values.append(record)
    return values


def request(candidate, steps, rounds):
    return (b"AFIT" + bytes((1, rounds, 0, 0)) + b"ACPU"
            + bytes((1, steps, len(candidate["ops"]), 2)) + struct.pack("<8d", *candidate["w"])
            + bytes(value for row in zip(candidate["ops"], candidate["dst"], candidate["a"], candidate["b"], strict=True)
                    for value in row))


def cases():
    requests = []
    for name, seed in zip(("sgd", "momentum", "step-decay"), seeds(), strict=True):
        for steps in (0, 1, 4, 12):
            requests.append((f"{name}-{steps}-fit-0", seed, steps, 0))
        for rounds in (1, 3):
            requests.append((f"{name}-12-fit-{rounds}", seed, 12, rounds))
    for op in range(8):
        p = {"ops": [op], "dst": [14], "a": [3], "b": [0 if op in (4,5,6) else 3], "w": [.25] * 8}
        requests.append((f"opcode-{op}", p, 1, 0))
    for value in (-1., 0., .25, 1., 2.):
        p = {"ops": [6], "dst": [14], "a": [3], "b": [0], "w": [value] + [0.] * 7}
        requests.append((f"step-{value}", p, 1, 0))
    p = {"ops": [0] * 11 + [4], "dst": [4] * 11 + [14], "a": [3] * 11 + [0],
         "b": [1] * 11 + [0], "w": [-.05] + [0.] * 7}
    requests.append(("maximum-12x12-fit-3", p, 12, 3))
    p = {"ops": [5] * 8, "dst": [14] * 8, "a": [3] + [14] * 7,
         "b": list(range(8)), "w": [.01] * 8}
    requests.append(("all-eight-weights", p, 2, 6))
    output = []
    for name, candidate, steps, rounds in requests:
        assert (rounds + 1) * (64 + steps * (14 + 2 * len(candidate["ops"]))) <= 2600
        before = copy.deepcopy(candidate)
        wire = request(before, steps, rounds)
        result = fit(copy.deepcopy(candidate), steps, rounds)
        case = {"name": name, "candidate": before, "steps": steps, "rounds": rounds,
                "request_hex": wire.hex(), **result}
        if name in ("sgd-4-fit-0", "momentum-4-fit-0", "all-eight-weights"):
            differences = []
            for index in range(8):
                plus, minus = before["w"].copy(), before["w"].copy()
                plus[index] += 1e-7
                minus[index] -= 1e-7
                differences.append((measure(before, plus, steps)[0] - measure(before, minus, steps)[0]) / 2e-7)
            case["initial_finite_differences"] = differences
        output.append(case)
    return output
