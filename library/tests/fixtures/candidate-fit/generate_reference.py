"""Emit fresh CPU float64 PyTorch answers for the fixed candidate-fitting ABI.

SIGIL_GENERATE_CANDIDATE_REFERENCE=1 arms generation. Only this independent
oracle emits expected answers; native tests never recompute them from SIGIL.
"""

from __future__ import annotations

import json
import os
import sys


def main() -> int:
    if os.environ.get("SIGIL_GENERATE_CANDIDATE_REFERENCE") != "1":
        print("set SIGIL_GENERATE_CANDIDATE_REFERENCE=1 to emit answers", file=sys.stderr)
        return 2
    import torch

    if torch.__version__.split("+", 1)[0] != "2.14.1":
        raise RuntimeError("reference generation requires PyTorch 2.14.1")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    train_x = torch.tensor([-1., -.75, -.5, -.25, .25, .5, .75, 1.], dtype=torch.float64)
    held_x = torch.tensor([-.875, -.375, .125, .625], dtype=torch.float64)

    def target(x):
        return .3 + .5 * x + .7 * torch.relu(1.1 * x + .2) - .4 * torch.relu(-.8 * x + .1)

    train_y, held_y = target(train_x), target(held_x)

    def predict(candidate, w, x):
        if candidate == 0:
            return (w[0] + w[1] * x + w[2] * torch.relu(w[3] * x + w[4])
                    + w[5] * torch.relu(w[6] * x + w[7]))
        return (w[0] + w[1] * x + w[2] * x * x + w[3] * x * x * x
                + w[4] * torch.relu(w[5] * x + w[6]) + w[7] * torch.relu(-x))

    def loss(candidate, w, x=train_x, y=train_y):
        return torch.mean((predict(candidate, w, x) - y) ** 2)

    def finite_difference(candidate, weights):
        differences = []
        for index in range(8):
            plus, minus = weights.detach().clone(), weights.detach().clone()
            plus[index] += 1e-6
            minus[index] -= 1e-6
            differences.append(((loss(candidate, plus) - loss(candidate, minus)) / 2e-6).item())
        return differences

    cases = []
    for candidate, initial in enumerate([
        [0., .1, .3, .8, -.1, -.2, -.7, .15],
        [0., .1, .05, 0., .3, .8, -.1, -.2],
    ]):
        weights = torch.tensor(initial, dtype=torch.float64, requires_grad=True)
        initial_loss = loss(candidate, weights).item()
        initial_held = loss(candidate, weights, held_x, held_y).item()
        first_gradient = torch.autograd.grad(loss(candidate, weights), weights)[0].tolist()
        for step in range(17):
            current_loss = loss(candidate, weights)
            gradient, = torch.autograd.grad(current_loss, weights)
            if step in [0, 1, 2, 4, 8, 12, 16]:
                expected = [initial_loss, current_loss.item(), initial_held,
                            loss(candidate, weights, held_x, held_y).item(),
                            *initial, *weights.detach().tolist(),
                            *first_gradient, *gradient.tolist()]
                assert len(expected) == 36 and all(torch.isfinite(torch.tensor(expected)))
                cases.append({"candidate": candidate, "steps": step, "expected": expected,
                              "finite_difference_final": finite_difference(candidate, weights)})
            if step < 16:
                weights = (weights - .1 * gradient).detach().requires_grad_(True)
    json.dump({"format": "sigil-candidate-fit-torch-v1",
               "reference": {"torch": "2.14.1", "device": "cpu", "dtype": "float64",
                             "atol": 1e-12, "rtol": 1e-11, "finite_difference_atol": 1e-8},
               "rate": .1, "train_x": train_x.tolist(), "train_y": train_y.tolist(),
               "held_x": held_x.tolist(), "held_y": held_y.tolist(), "cases": cases},
              sys.stdout, sort_keys=True, indent=2, allow_nan=False)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
