"""Emit regression fitting/search answers using PyTorch and upstream C PCG only.

Generation is opt-in. The search-policy reference derives from the preserved
quadratic oracle; numerical evaluation uses autograd on raw regression rows.
"""
from __future__ import annotations

import copy
import ctypes
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile

import oracle

class Pcg(ctypes.Structure):
    _fields_ = [("state", ctypes.c_uint64), ("increment", ctypes.c_uint64)]

def main():
    if os.environ.get("SIGIL_GENERATE_REGRESSION_REFERENCE") != "1":
        raise SystemExit("Set SIGIL_GENERATE_REGRESSION_REFERENCE=1 to execute the reference")
    import torch
    if torch.__version__.split("+", 1)[0] != "2.14.1":
        raise RuntimeError("reference requires PyTorch 2.14.1")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    root = oracle.ROOT
    seeds = oracle.seeds()
    dataset_words = list(struct.unpack("<4Q", bytes.fromhex(oracle.DATASET["identity_sha256"])))
    fitting = oracle.cases()
    def fit(p, steps, rounds):
        result = oracle.fit(p, steps, rounds)
        return result["header"][5], result["header"][6]

    def wire(head, pop, history, steps):
        result = struct.pack("<32Q", *head)
        for p in pop:
            instructions = bytes(value for row in zip(p["ops"], p["dst"], p["a"], p["b"], strict=True) for value in row)
            result += b"ACPU" + bytes((1, steps, len(p["ops"]), 2)) + struct.pack("<8d", *p["w"])
            result += instructions.ljust(48, b"\x00") + struct.pack("<Q2d", p["lineage"], p["loss"], p["fitness"])
        return (result + struct.pack("<41d", *(history + [0.] * (41 - len(history))))).hex()

    with tempfile.TemporaryDirectory(prefix="sigil-search-reference-") as directory:
        source = root / "tests/fixtures/rng/upstream/pcg_basic.c"
        library = Path(directory) / "pcg.so"
        subprocess.run(["cc", "-shared", "-fPIC", "-O2", str(source), "-o", str(library)], check=True)
        pcg = ctypes.CDLL(str(library))
        pcg.pcg32_srandom_r.argtypes = [ctypes.POINTER(Pcg), ctypes.c_uint64, ctypes.c_uint64]
        pcg.pcg32_random_r.argtypes = [ctypes.POINTER(Pcg)]
        pcg.pcg32_random_r.restype = ctypes.c_uint32
        pcg.pcg32_boundedrand_r.argtypes = [ctypes.POINTER(Pcg), ctypes.c_uint32]
        pcg.pcg32_boundedrand_r.restype = ctypes.c_uint32
        cases = []
        for seed, steps, generations in ((42, 4, 1), (7, 12, 1)):
            for hybrid in (False, True):
                generator = Pcg()
                pcg.pcg32_srandom_r(ctypes.byref(generator), seed, 54)

                def below(n):
                    return pcg.pcg32_boundedrand_r(ctypes.byref(generator), n)

                def mutate(p):
                    p = copy.deepcopy(p)
                    kind, n = below(6), len(p["ops"])
                    if kind <= 2:
                        i = below(n)
                        if kind == 0:
                            op = below(8)
                            p["ops"][i], p["b"][i] = op, below(8 if op in (4, 5, 6) else 16)
                        elif kind == 1:
                            p["a"][i] = below(16)
                        else:
                            p["dst"][i] = 4 + below(12)
                    elif kind == 3 and n < 12:
                        op, dst, a = below(8), 4 + below(12), below(16)
                        b = below(8 if op in (4, 5, 6) else 16)
                        for key, value in zip(("ops", "dst", "a", "b"), (op, dst, a, b), strict=True):
                            p[key].append(value)
                    elif kind == 4 and n > 1:
                        i = below(n)
                        for key in ("ops", "dst", "a", "b"):
                            p[key].pop(i)
                    elif kind == 5:
                        i = below(8)
                        unit = pcg.pcg32_random_r(ctypes.byref(generator)) / 2**32
                        p["w"][i] = min(4096., max(-4096., p["w"][i] + unit * .5 - .25))
                    p.update(loss=0., fitness=0.)
                    return p

                def crossover(a, b):
                    cut_a, cut_b = 1 + below(len(a["ops"])), below(len(b["ops"]) + 1)
                    p = copy.deepcopy(a)
                    for key in ("ops", "dst", "a", "b"):
                        p[key] = (a[key][:cut_a] + b[key][cut_b:])[:12]
                    p["w"] = [a["w"][i] if i % 2 == 0 else b["w"][i] for i in range(8)]
                    return p

                pop, history = copy.deepcopy(seeds), []
                while len(pop) < 8:
                    pop.append(mutate(pop[below(3)]))
                head = [1397904193, 1, 2, seed, 54, generator.state, generator.increment,
                        generations, steps, int(hybrid), 0, 0, 0, 0, 0, (generations + 1) * 8,
                        0, 0, 0, 0] + dataset_words + [0] * 8
                # Every transition is emitted: the harness must compare search
                # decisions and population structure, not only the final winner.
                states = [wire(head, pop, history, steps)]
                for generation in range(generations + 1):
                    for index, p in enumerate(pop):
                        accepted, rejected = fit(p, steps, 3 if hybrid and generation < generations else 0)
                        head[11] = index + 1
                        head[13] += 1
                        head[14] += 1
                        head[16] += 1 + accepted + rejected
                        head[17] += accepted
                        head[18] += rejected
                        if index == 7:
                            pop = sorted(pop, key=lambda candidate: candidate["fitness"])
                            history.append(pop[0]["loss"])
                            head[12] = 2 if generation == generations else 1
                            head[19] = len(history)
                        states.append(wire(head, pop, history, steps))
                    if generation == generations:
                        break
                    following = copy.deepcopy(pop[:2])
                    while len(following) < 8:
                        parent = pop[below(4)]
                        if below(2) == 0:
                            parent = crossover(parent, pop[below(4)])
                        following.append(mutate(parent))
                    for p in following:
                        p.update(loss=0., fitness=0.)
                    pop = following
                    head[5:7] = generator.state, generator.increment
                    head[10:13] = generation + 1, 0, 0
                    head[13] += 1
                    states.append(wire(head, pop, history, steps))
                cases.append({"seed": str(seed), "steps": steps, "generations": generations,
                              "hybrid": hybrid, "states": states})
    changed = copy.deepcopy(oracle.DATASET)
    changed["validation"][0][1] += 1000.0
    seed = seeds[0]
    original_measurement = oracle.measure(seed, seed["w"], 4)
    assert oracle.measure(seed, seed["w"], 4, dataset=changed) == original_measurement
    assert oracle.validation(original_measurement[2:4], dataset=changed) != oracle.validation(original_measurement[2:4])
    print(json.dumps({"format": "sigil-regression-reference-v1", "torch": "2.14.1",
                      "device": "cpu", "dtype": "float64", "rng": "upstream-pcg-c",
                      "dataset_sha256": oracle.DATASET["identity_sha256"],
                      "atol": 1e-10, "rtol": 1e-10, "fits": fitting, "searches": cases},
                     sort_keys=True, indent=2, allow_nan=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
