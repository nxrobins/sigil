"""Emit reviewable CPU float64 PyTorch answers; never overwrite a fixture.

Run with SIGIL_GENERATE_NUMERIC_REFERENCE=1 in the isolated pinned Torch
environment. The fixture is private test evidence, not training/admission data.
"""

from __future__ import annotations

import json
import os
import random
import sys


def main() -> int:
    if os.environ.get("SIGIL_GENERATE_NUMERIC_REFERENCE") != "1":
        print("reference generation requires SIGIL_GENERATE_NUMERIC_REFERENCE=1", file=sys.stderr)
        return 2
    import torch
    from torch.nn import functional

    if torch.__version__.split("+", 1)[0] != "2.14.1":
        raise RuntimeError("reference generation requires reviewed PyTorch 2.14.1")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    random_source = random.Random(1701)

    def tensor(rows, cols):
        values = [random_source.randint(-12, 12) / 4 for _ in range(rows * cols)]
        return torch.tensor(values, dtype=torch.float64, device="cpu").reshape(rows, cols)

    def view(value):
        return {"rows": value.shape[0], "cols": value.shape[1], "values": value.flatten().tolist()}

    operations = []
    for rows, cols in [(1, 1), (1, 3), (2, 2), (3, 2)]:
        a, b = tensor(rows, cols), tensor(rows, cols)
        differentiable = a.clone().requires_grad_()
        loss = functional.mse_loss(differentiable, b, reduction="mean")
        gradient = torch.autograd.grad(loss, differentiable)[0]
        results = {
            "add_into": a + b, "sub_into": a - b, "mul_into": a * b,
            "scale_into": a * -0.75, "relu_into": torch.relu(a),
            "sum_into": a.sum(), "mean_into": a.mean(),
            "dot_into": a.flatten().dot(b.flatten()),
            "mse_into": loss.detach(), "mse_grad_into": gradient,
            "transpose_into": a.transpose(0, 1),
        }
        for operation, result in results.items():
            scalar = result.ndim == 0
            operations.append({"operation": operation, "a": view(a), "b": view(b),
                               "out_rows": 1 if scalar else result.shape[0],
                               "out_cols": 1 if scalar else result.shape[1],
                               "scalar": scalar, "expected": result.flatten().tolist()})
    for rows, shared, cols in [(1, 1, 1), (2, 3, 2), (3, 1, 4), (2, 2, 3), (3, 3, 3)]:
        a, b = tensor(rows, shared), tensor(shared, cols)
        operations.append({"operation": "matmul_into", "a": view(a), "b": view(b),
                           "out_rows": rows, "out_cols": cols, "scalar": False,
                           "expected": (a @ b).flatten().tolist()})
    training = []
    x = torch.tensor([[1, 0], [1, 1], [1, 2], [1, 3]], dtype=torch.float64, device="cpu")
    target = torch.tensor([[1], [3], [5], [7]], dtype=torch.float64, device="cpu")
    validation_x = torch.tensor([[1, 4], [1, 5]], dtype=torch.float64, device="cpu")
    validation_target = torch.tensor([[9], [11]], dtype=torch.float64, device="cpu")
    for epochs in [0, 1, 2, 10, 100, 200]:
        weights = torch.zeros((2, 1), dtype=torch.float64, device="cpu", requires_grad=True)
        initial_loss = functional.mse_loss(x @ weights, target)
        initial_gradient = torch.autograd.grad(initial_loss, weights)[0]
        optimizer = torch.optim.SGD([weights], lr=0.05, momentum=0, foreach=False)
        for _ in range(epochs):
            optimizer.zero_grad()
            functional.mse_loss(x @ weights, target).backward()
            optimizer.step()
        loss = functional.mse_loss(x @ weights, target)
        gradient = torch.autograd.grad(loss, weights)[0]
        validation = functional.mse_loss(validation_x @ weights, validation_target)
        training.append({"epochs": epochs, "expected": [initial_loss.item(), loss.item(),
                         *weights.detach().flatten().tolist(), *initial_gradient.flatten().tolist(),
                         *gradient.flatten().tolist(), validation.item()]})
    json.dump({"format": "sigil-numeric-torch-reference-v1",
               "reference": {"torch": "2.14.1", "device": "cpu", "dtype": "float64",
                             "seed": 1701, "atol": 1e-12, "rtol": 1e-11},
               "operations": operations, "training": training}, sys.stdout, sort_keys=True, indent=2)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
