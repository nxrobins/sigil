"""Exercise the candidate report viewer; malformed bytes must never become results.

The native fitting implementation is exercised by solver CLI tests. These tests
cover the serialized output boundary and viewer failures, not numerical training.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
VIEWER = ROOT / "library/programs/candidate-fit/run.py"
SPEC = importlib.util.spec_from_file_location("candidate_fit_viewer", VIEWER)
viewer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(viewer)


class CandidateFitViewerTests(unittest.TestCase):
    def payload(self):
        return struct.pack("<2q36d", 1, 16, *[float(i) for i in range(36)])

    def test_valid_native_report_decodes_and_bad_length_identity_or_finiteness_refuses(self):
        raw = self.payload()
        decoded = viewer.decode(raw, 1, 16)
        self.assertEqual(decoded["constants"], [float(i) for i in range(12, 20)])
        self.assertEqual(decoded["gradient"], [float(i) for i in range(28, 36)])
        self.assertEqual(decoded["initial_loss"], 0.0)
        self.assertEqual(decoded["format"], "candidate-fit-v2")
        self.assertEqual(decoded["initial_validation_loss"], 2.0)
        self.assertEqual(decoded["validation_loss"], 3.0)
        self.assertEqual(set(decoded), {
            "format", "candidate", "steps", "initial_loss", "final_loss",
            "initial_validation_loss", "validation_loss", "initial_constants",
            "constants", "initial_gradient", "gradient",
        })
        wrong_header = struct.pack("<2q", 0, 16) + raw[16:]
        nonfinite = raw[:16] + struct.pack("<d", float("nan")) + raw[24:]
        for bad in [raw[:-1], raw + b"x", b"", wrong_header, nonfinite]:
            with self.subTest(payload=bad[:24]), self.assertRaises(ValueError):
                viewer.decode(bad, 1, 16)
        with self.assertRaises(ValueError):
            viewer.decode(raw, 1, 15)

    def invoke(self, completed=None, error=None):
        stdout, stderr = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "argv", [str(VIEWER), "--sigil", "/test/native-sigil",
                                             "--candidate", "1", "--steps", "16"]), \
                mock.patch.object(viewer.subprocess, "run", return_value=completed,
                                  side_effect=error) as native, \
                contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            status = viewer.main()
        return status, stdout.getvalue(), stderr.getvalue(), native

    def test_viewer_calls_native_cli_and_only_displays_its_report(self):
        envelope = {"status": "ok", "data": {"output": list(self.payload())}}
        completed = subprocess.CompletedProcess([], 0, json.dumps(envelope), "")
        status, output, errors, native = self.invoke(completed)
        self.assertEqual(status, 0, errors)
        self.assertEqual(json.loads(output), viewer.decode(self.payload(), 1, 16))
        native.assert_called_once_with(
            ["/test/native-sigil", "run", "--package", str(VIEWER.parent.resolve()),
             "--input", "1:16", "--fuel", "500000", "--json"],
            capture_output=True, text=True, timeout=60, check=False,
        )

    def test_cli_refusal_timeout_and_malformed_output_never_fall_back_to_training(self):
        for completed in [
            subprocess.CompletedProcess([], 1, '{"status":"error","diagnostics":[]}', ""),
            subprocess.CompletedProcess([], 0, 'not json', ""),
            subprocess.CompletedProcess([], 0, '[]', ""),
            subprocess.CompletedProcess([], 0, 'null', ""),
            subprocess.CompletedProcess([], 0, '{"status":"ok","data":{"output":1000000000}}', ""),
            subprocess.CompletedProcess([], 0, json.dumps({"status": "ok", "data": {"output": [True] * 304}}), ""),
            subprocess.CompletedProcess([], 0, '{"status":"ok","data":{"output":[0]}}', ""),
            subprocess.CompletedProcess([], 0, '{"status":"ok","data":{"output":[256]}}', ""),
            subprocess.CompletedProcess([], 0, '{"status":"ok","data":{}}', ""),
        ]:
            status, output, errors, native = self.invoke(completed)
            self.assertEqual(status, 1)
            self.assertEqual(output, "")
            self.assertTrue(errors)
            native.assert_called_once()
        status, output, errors, native = self.invoke(error=subprocess.TimeoutExpired("sigil", 60))
        self.assertEqual(status, 1)
        self.assertEqual(output, "")
        self.assertTrue(errors)
        native.assert_called_once()

    def test_reference_generator_requires_explicit_opt_in(self):
        env = dict(os.environ)
        env.pop("SIGIL_GENERATE_CANDIDATE_REFERENCE", None)
        result = subprocess.run([sys.executable, str(ROOT / "library/tests/fixtures/candidate-fit/generate_reference.py")],
                                env=env, capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")
        self.assertEqual(result.stderr.strip(), "set SIGIL_GENERATE_CANDIDATE_REFERENCE=1 to emit answers")


if __name__ == "__main__":
    unittest.main()
