"""Behavior tests for transport: never substitute a Python fitness evaluator."""

import contextlib
import copy
import importlib.util
import io
import json
import math
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "programs/autoresearch-cpu"
SPEC = importlib.util.spec_from_file_location("autoresearch_cpu_wrapper", EXAMPLE / "run.py")
WRAPPER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(WRAPPER)


class AutoresearchCpuTests(unittest.TestCase):
    def setUp(self):
        self.seed = json.loads((EXAMPLE / "candidates/momentum.json").read_text())
        self.reference = json.loads((ROOT / "tests/fixtures/autoresearch-cpu/torch-v1.json").read_text())
        self.case = next(c for c in self.reference["cases"] if c["name"] == "momentum-20")
        self.request = WRAPPER.encode(self.seed, 20)

    def report(self):
        return struct.pack("<4q14d", 1, 20, 3, 284, *self.case["expected"]) + self.request

    def test_q16_import_normalizes_exactly_and_every_reference_wire_matches(self):
        for case in self.reference["cases"]:
            with self.subTest(case=case["name"]):
                wire = WRAPPER.encode(case["candidate"], case["steps"])
                self.assertEqual(wire.hex(), case["request_hex"])
        normalized = WRAPPER.validate(self.seed)
        self.assertEqual(normalized["w"][:2], [-1966 / 65536, 58982 / 65536])
        self.assertEqual(WRAPPER.encode(normalized, 20), self.request)
        changed = copy.deepcopy(self.seed)
        changed["w"][0] += 1
        self.assertNotEqual(WRAPPER.encode(changed, 20), self.request)
        changed = copy.deepcopy(self.seed)
        changed["a"][0] = 3
        self.assertNotEqual(WRAPPER.encode(changed, 20), self.request)
        self.assertNotEqual(WRAPPER.encode(self.seed, 19), self.request)

    def test_seed_transcription_retains_original_instructions_and_raw_weights(self):
        seeds = {
            "sgd": ([4, 0], [14, 15], [0, 1], [0, 3], [-3277, 0, 0, 0, 0, 0, 0, 0]),
            "momentum": ([4, 0, 4], [4, 15, 14], [1, 4, 15], [1, 0, 0],
                         [-1966, 58982, 0, 0, 0, 0, 0, 0]),
            "step-decay": ([5, 6, 4, 5, 2, 4, 0], [4, 5, 6, 7, 8, 14, 15],
                           [2, 4, 5, 6, 0, 8, 1], [2, 3, 4, 5, 7, 0, 1],
                           [-3277, 0, -32768, 524288, -32768, 65536, 0, 0]),
        }
        for name, columns in seeds.items():
            record = json.loads((EXAMPLE / f"candidates/{name}.json").read_text())
            self.assertEqual(record["numeric"], WRAPPER.Q16_IMPORT)
            for key, expected in zip(("ops", "dst", "a", "b", "w"), columns, strict=True):
                self.assertEqual(record[key], expected, (name, key))

    def test_invalid_fields_types_bounds_and_nonfinite_values_refuse(self):
        self.assertEqual(len(WRAPPER.validate(self.seed)["w"]), 8)
        invalid = [None, [], {**self.seed, "fitness": 0}, {**self.seed, "lineage": 1},
                   {**self.seed, "numeric": "Q16"}, {**self.seed, "format": "v2"}]
        for field, values in {"ops": [[], [4] * 13, [True, 0, 4], [8, 0, 4]],
                              "dst": [[0, 15, 14], [16, 15, 14]],
                              "a": [[16, 4, 15], [0, -1, 15]],
                              "b": [[8, 0, 0], [1, 16, 0]],
                              "w": [[0] * 7, [True] * 8, [1.5] * 8,
                                    [268435457] * 8, [-268435457] * 8]}.items():
            invalid.extend({**self.seed, field: value} for value in values)
        for value in (math.nan, math.inf, -math.inf, 4096.00001, -4096.00001, True, "0"):
            invalid.append({**self.seed, "numeric": WRAPPER.PROFILE, "w": [value] * 8})
        for candidate in invalid:
            with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                WRAPPER.validate(candidate)
        for steps in (-1, 21, True, 2., "2"):
            with self.assertRaises(ValueError):
                WRAPPER.encode(self.seed, steps)
        # Both exact numerical endpoints and ignored unary b=15 remain legal.
        for value in (-4096., 4096.):
            WRAPPER.validate({**self.seed, "numeric": WRAPPER.PROFILE, "w": [value] * 8})
        WRAPPER.validate({**self.seed, "ops": [7], "dst": [14], "a": [3], "b": [15]})

    def test_bounded_json_refuses_duplicate_unknown_nonfinite_and_malformed_records(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "candidate.json"
            text = json.dumps(self.seed)
            path.write_text(text)
            self.assertEqual(WRAPPER.read_candidate(path), WRAPPER.validate(self.seed))
            for raw in [text[:-1] + ',"ops":[4,0,4]}', text[:-1] + ',"loss":0}',
                        text.replace('-1966', 'NaN'), text.replace('-1966', 'Infinity'),
                        text.replace('-1966', '1e999'), ' ' * 16385, '[', '\ud800',
                        '[' * 2000 + '0' + ']' * 2000]:
                path.write_bytes(raw.encode("utf-8", errors="surrogatepass"))
                with self.assertRaises((ValueError, RecursionError)):
                    WRAPPER.read_candidate(path)

    def test_decode_checks_shape_echo_header_and_finite_values(self):
        report = self.report()
        decoded = WRAPPER.decode(report, self.request)
        self.assertEqual(decoded["gradient"], self.case["expected"][6:])
        self.assertEqual(decoded["loss"], self.case["expected"][0])
        self.assertEqual(decoded["numeric"], WRAPPER.PROFILE)
        invalid = [report[:-1], report + b'\x00', report[:-1] + b'\xff']
        for offset, value in [(0, 2), (8, 19), (16, 4), (24, 23), (24, 769)]:
            changed = bytearray(report)
            struct.pack_into("<q", changed, offset, value)
            invalid.append(changed)
        for offset, value in [(32, -1.), (40, 0.), (80, math.inf), (32, math.nan)]:
            changed = bytearray(report)
            struct.pack_into("<d", changed, offset, value)
            invalid.append(changed)
        for output in invalid:
            with self.assertRaises(ValueError):
                WRAPPER.decode(output, self.request)

    def invoke(self, response=None, error=None, path=None):
        argv = ["run.py", "--candidate", str(path or EXAMPLE / "candidates/momentum.json"),
                "--sigil", "chosen-sigil"]
        out, err = io.StringIO(), io.StringIO()
        with patch.object(sys, "argv", argv), patch.object(WRAPPER.subprocess, "run",
                return_value=response, side_effect=error) as run, \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = WRAPPER.main()
        return status, out.getvalue(), err.getvalue(), run

    def test_wrapper_uses_native_result_and_never_falls_back_after_failures(self):
        payload = {"status": "ok", "data": {"output": list(self.report())}}
        good = subprocess.CompletedProcess([], 0, json.dumps(payload), "")
        status, text, error, run = self.invoke(good)
        self.assertEqual((status, error), (0, ""))
        self.assertEqual(json.loads(text)["gradient"], self.case["expected"][6:])
        command = run.call_args.args[0]
        self.assertEqual(command[:2], ["chosen-sigil", "run"])
        self.assertEqual(command[command.index("--input") + 1], self.request.hex())
        self.assertEqual(command[command.index("--fuel") + 1], "500000")
        self.assertEqual(run.call_args.kwargs["timeout"], 60)
        bad_payloads = ["not JSON", "null", "{}", json.dumps({**payload, "status": "error"})]
        for output in ([True] * len(self.report()), [256] * len(self.report()), [], "bytes"):
            bad_payloads.append(json.dumps({"status": "ok", "data": {"output": output}}))
        for result in [subprocess.CompletedProcess([], 1, good.stdout, "failure"),
                       *[subprocess.CompletedProcess([], 0, data, "") for data in bad_payloads]]:
            status, text, error, _ = self.invoke(result)
            self.assertEqual((status, text), (1, ""))
            self.assertIn("refused", error)
        for error in (FileNotFoundError("absent"), subprocess.TimeoutExpired("sigil", 60)):
            status, text, _, _ = self.invoke(error=error)
            self.assertEqual((status, text), (1, ""))
        with tempfile.TemporaryDirectory() as temporary:
            bad = Path(temporary) / "bad.json"
            bad.write_text('{}')
            status, _, _, run = self.invoke(good, path=bad)
            self.assertEqual(status, 1)
            run.assert_not_called()

    def test_oracle_generation_requires_explicit_opt_in_before_importing_torch(self):
        environment = dict(os.environ)
        environment.pop("SIGIL_GENERATE_AUTORESEARCH_REFERENCE", None)
        result = subprocess.run([sys.executable, str(ROOT / "tests/fixtures/autoresearch-cpu/generate_reference.py")],
                                env=environment, capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")
        self.assertIn("SIGIL_GENERATE_AUTORESEARCH_REFERENCE=1", result.stderr)


if __name__ == "__main__":
    unittest.main()
