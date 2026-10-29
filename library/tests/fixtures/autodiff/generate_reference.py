"""Emit explicit PyTorch CPU float64 graph answers, never edit an answer file.

Run with SIGIL_GENERATE_AUTODIFF_REFERENCE=1 in the isolated Torch 2.14.1
environment. The graph format is a private test protocol, not an admitted IR.
"""

from __future__ import annotations

import json
import os
import random
import sys


def main() -> int:
    if os.environ.get("SIGIL_GENERATE_AUTODIFF_REFERENCE") != "1":
        print("reference generation requires SIGIL_GENERATE_AUTODIFF_REFERENCE=1", file=sys.stderr)
        return 2
    import torch

    if torch.__version__.split("+", 1)[0] != "2.14.1":
        raise RuntimeError("reference generation requires reviewed PyTorch 2.14.1")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    graphs = []

    def emit(name, nodes, output=None):
        values, variables = [], []
        for node in nodes:
            operation = node["op"]
            if operation in ("variable", "constant"):
                value = torch.tensor(node["value"], dtype=torch.float64, device="cpu",
                                     requires_grad=operation == "variable")
                if operation == "variable":
                    variables.append(value)
            elif operation == "add":
                value = values[node["a"]] + values[node["b"]]
            elif operation == "sub":
                value = values[node["a"]] - values[node["b"]]
            elif operation == "mul":
                value = values[node["a"]] * values[node["b"]]
            elif operation == "relu":
                value = torch.relu(values[node["a"]])
            elif operation == "select":
                value = torch.where(torch.tensor(node["condition"], device="cpu"),
                                    values[node["a"]], values[node["b"]])
            else:
                assert operation == "sum"
                value = (torch.stack([values[index] for index in node["terms"]]).sum()
                         if node["terms"] else torch.tensor(0.0, dtype=torch.float64, device="cpu"))
            values.append(value)
        root = len(nodes) - 1 if output is None else output
        result = values[root]
        # Zero-valued connections let actual autograd query disconnected variables
        # and constant roots without changing the function or its derivatives.
        anchored = result
        for variable in variables:
            anchored = anchored + variable * 0.0
        gradients = torch.autograd.grad(anchored, variables)
        expected = [result.item(), *(gradient.item() for gradient in gradients)]
        if not all(torch.isfinite(torch.tensor(value, dtype=torch.float64)) for value in expected):
            raise RuntimeError(f"nonfinite reference graph: {name}")
        graphs.append({"name": name, "nodes": nodes, "output": root, "expected": expected})

    for value in [-2.0, 0.0, 3.0]:
        emit(f"square-{value}", [{"op": "variable", "value": value},
                                 {"op": "mul", "a": 0, "b": 0}])
        emit(f"relu-{value}", [{"op": "variable", "value": value},
                               {"op": "relu", "a": 0}])
    for condition in [False, True]:
        emit(f"select-{condition}", [{"op": "variable", "value": 2.0},
                                    {"op": "variable", "value": -3.0},
                                    {"op": "mul", "a": 0, "b": 1},
                                    {"op": "select", "condition": condition, "a": 0, "b": 2}])
    emit("shared-polynomial", [{"op": "variable", "value": 0.75},
                               {"op": "variable", "value": -1.25},
                               {"op": "mul", "a": 0, "b": 1},
                               {"op": "add", "a": 2, "b": 0},
                               {"op": "sub", "a": 0, "b": 1},
                               {"op": "mul", "a": 3, "b": 4}])
    emit("sub-cancellation", [{"op": "variable", "value": 2.0},
                              {"op": "sub", "a": 0, "b": 0}])
    emit("sum-empty", [{"op": "variable", "value": 7.0}, {"op": "sum", "terms": []}])
    emit("sum-repeated", [{"op": "variable", "value": 2.0},
                          {"op": "variable", "value": -3.0},
                          {"op": "mul", "a": 0, "b": 1},
                          {"op": "sum", "terms": [2, 0, 2, 0]}])
    emit("disconnected", [{"op": "variable", "value": 3.0},
                          {"op": "variable", "value": 8.0},
                          {"op": "mul", "a": 0, "b": 0}])
    emit("constant-root", [{"op": "variable", "value": 3.0},
                           {"op": "constant", "value": 5.0}])
    for count in [1, 2, 8, 32, 128]:
        nodes = [{"op": "variable", "value": (index % 9 - 4) / 8} for index in range(count)]
        nodes.extend({"op": "mul", "a": index, "b": index} for index in range(count))
        nodes.append({"op": "sum", "terms": list(range(count, 2 * count))})
        emit(f"many-variables-{count}", nodes)
    rng = random.Random(3911)
    while len(graphs) < 64:
        nodes = [{"op": "variable", "value": rng.randint(-8, 8) / 8} for _ in range(3)]
        nodes.append({"op": "constant", "value": 0.5})
        for _ in range(18):
            operation = rng.choice(["add", "sub", "mul", "relu", "select", "sum"])
            a, b = rng.randrange(len(nodes)), rng.randrange(len(nodes))
            if operation == "sum":
                node = {"op": "sum", "terms": [a, b, a]}
            elif operation == "relu":
                node = {"op": "relu", "a": a}
            elif operation == "select":
                node = {"op": "select", "condition": bool(rng.randrange(2)), "a": a, "b": b}
            else:
                node = {"op": operation, "a": a, "b": b}
            nodes.append(node)
        emit(f"seeded-graph-{len(graphs)}", nodes)
    json.dump({"format": "sigil-autodiff-torch-reference-v1",
               "reference": {"torch": "2.14.1", "dtype": "float64", "device": "cpu",
                             "seed": 3911, "atol": 1e-12, "rtol": 1e-11},
               "graphs": graphs}, sys.stdout, sort_keys=True, indent=2)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
