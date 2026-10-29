"""Fitting transport refuses corrupt reports; a fresh native export re-evaluates."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "programs/autoresearch"
SPEC = importlib.util.spec_from_file_location("autoresearch_fit_transport", EXAMPLE / "run.py")
WRAPPER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(WRAPPER)
ORACLE = json.loads((ROOT / "tests/fixtures/autoresearch-fit/torch-v1.json").read_text())


def report(case):
    numbers = case["expected_numbers"]
    return (struct.pack("<8q", *case["expected_header"]) + struct.pack("<25d", *numbers[:25])
            + struct.pack("<6q", *case["decisions"]) + struct.pack("<66d", *numbers[25:])
            + bytes.fromhex(case["request_hex"]))


def native_record(case):
    """Independent wire fixture, not an implementation-source snapshot."""
    binary = report(case)
    request = bytearray(bytes.fromhex(case["request_hex"]))
    request[4] = 2
    return {"format": "sigil-autoresearch-fit-record-v1", "numeric": "binary64le-hex-v1",
            "request_hex": request.hex(), "header_le": binary[:64].hex(),
            "summary_f64le": binary[64:88].hex(), "weights_f64le": binary[88:152].hex(),
            "accepted_f64le": binary[152:264].hex(), "decisions_le": binary[264:312].hex(),
            "trace_f64le": binary[312:840].hex()}


class FittingTransportTests(unittest.TestCase):
    def setUp(self):
        self.case = next(c for c in ORACLE["cases"] if c["name"] == "sgd-20-fit-3")
        self.request = bytes.fromhex(self.case["request_hex"])
        self.report = report(self.case)

    def test_all_generated_reports_round_trip_and_preserve_instruction_records(self):
        self.assertEqual(len(ORACLE["cases"]), 58)
        for case in ORACLE["cases"]:
            with self.subTest(case=case["name"]):
                request = WRAPPER.encode(case["candidate"], case["steps"], case["rounds"])
                self.assertEqual(request.hex(), case["request_hex"])
                result = WRAPPER.decode(report(case), request)
                self.assertEqual(result["attempted"], case["expected_header"][4])
                self.assertEqual(result["accepted"], case["expected_header"][5])
                self.assertEqual(result["candidate"]["w"], case["expected_numbers"][3:11])
                for key in ("ops", "dst", "a", "b"):
                    self.assertEqual(result["candidate"][key], case["candidate"][key])

    def test_encoder_refuses_invalid_rounds_steps_and_combined_work(self):
        for rounds in (-1, 7, True, 1.0, None):
            with self.assertRaises(ValueError):
                WRAPPER.encode(self.case["candidate"], 20, rounds)
        for steps in (-1, 21, True):
            with self.assertRaises(ValueError):
                WRAPPER.encode(self.case["candidate"], steps, 1)
        maximum = next(c for c in ORACLE["cases"] if c["name"] == "maximum-12x20-fit-3")
        self.assertEqual(WRAPPER.encode(maximum["candidate"], 20, 3).hex(), maximum["request_hex"])
        with self.assertRaises(ValueError):
            WRAPPER.encode(maximum["candidate"], 20, 4)

    def test_native_record_decoder_is_exact_and_refuses_corruption(self):
        for case in ORACLE["cases"]:
            request = WRAPPER.encode(case["candidate"], case["steps"], case["rounds"], record=True)
            data = native_record(case)
            self.assertEqual(data["request_hex"], request.hex())
            actual = WRAPPER.decode_record(json.dumps(data).encode(), request)
            binary = report(case)[:840] + request
            self.assertEqual(actual, WRAPPER.decode(binary, request))
        data = native_record(self.case)
        request = bytes.fromhex(data["request_hex"])
        for key, value in (("format", "unknown"), ("numeric", "decimal"),
                           ("request_hex", "00" * len(request)), ("header_le", "00" * 64),
                           ("summary_f64le", "f" * 48), ("weights_f64le", "A" + data["weights_f64le"][1:]),
                           ("trace_f64le", "00"), ("decisions_le", 0), ("unknown", "field")):
            mutated = dict(data, **{key: value})
            with self.subTest(key=key), self.assertRaises(ValueError):
                WRAPPER.decode_record(json.dumps(mutated).encode(), request)
        encoded = json.dumps(data).encode()
        for invalid in (b"[]", encoded[:-1], encoded + b"!", b" " * 4097,
                        encoded[:-1] + b',"format":"sigil-autoresearch-fit-record-v1"}',
                        json.dumps({k: v for k, v in data.items() if k != "weights_f64le"}).encode()):
            with self.assertRaises(ValueError):
                WRAPPER.decode_record(invalid, request)
        with self.assertRaises(ValueError):
            WRAPPER.decode_record(encoded, self.request)
        with self.assertRaises(ValueError):
            WRAPPER.encode(self.case["candidate"], 20, 3, record=1)

    def test_decoder_refuses_identity_counters_nonfinite_and_inconsistent_history(self):
        bad = [self.report[:-1], self.report + b"!", self.report[:-1] + b"!"]
        for offset, value in ((0, 2), (8, 19), (16, 3), (24, 4), (32, -1),
                              (32, 4), (40, 0), (48, 3), (56, 1), (264, 0), (272, 1), (288, 0)):
            data = bytearray(self.report)
            struct.pack_into("<q", data, offset, value)
            bad.append(data)
        for offset, value in ((64, -1), (72, 0), (80, 1), (88, 4097), (160, 0),
                              (312, 0), (320, 0), (328, -1), (344, float("nan")),
                              (352, float("inf")), (576, 1)):
            data = bytearray(self.report)
            struct.pack_into("<d", data, offset, value)
            bad.append(data)
        data = bytearray(self.report)
        struct.pack_into("<8d", data, 336, *([0.] * 8))
        bad.append(data)
        for data in bad:
            with self.subTest(data=data), self.assertRaises(ValueError):
                WRAPPER.decode(data, self.request)
        zero = next(c for c in ORACLE["cases"] if c["name"] == "sgd-0-fit-6")
        data = bytearray(report(zero))
        struct.pack_into("<d", data, 200, 1.)
        with self.assertRaises(ValueError):
            WRAPPER.decode(data, bytes.fromhex(zero["request_hex"]))
        data = bytearray(report(zero))
        struct.pack_into("<d", data, 88, 1.)
        with self.assertRaises(ValueError):
            WRAPPER.decode(data, bytes.fromhex(zero["request_hex"]))

    def test_publication_is_create_new_and_cli_errors_never_publish(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "candidate.json"
            argv = ["run.py", "--candidate", str(ROOT / "programs/autoresearch-cpu/candidates/sgd.json"),
                    "--rounds", "3", "--candidate-out", str(output)]
            payload = list(self.report)
            failures = [subprocess.CompletedProcess([], 1, '{"status":"error"}', ""),
                        subprocess.CompletedProcess([], 0, "not JSON", ""),
                        subprocess.CompletedProcess([], 0, '[]', ""),
                        subprocess.CompletedProcess([], 0, '{"status":"ok","data":{}}', "")]
            for bad in ([True] * len(payload), payload[:-1], [256] * len(payload)):
                failures.append(subprocess.CompletedProcess([], 0, json.dumps(
                    {"status": "ok", "data": {"output": bad}}), ""))
            for response in failures:
                out, err = io.StringIO(), io.StringIO()
                with patch.object(WRAPPER.sys, "argv", argv), \
                        patch.object(WRAPPER.subprocess, "run", return_value=response), \
                        contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    self.assertEqual(WRAPPER.main(), 1)
                self.assertEqual(out.getvalue(), "")
                self.assertFalse(output.exists())
            for failure in (OSError("unavailable"), subprocess.TimeoutExpired("sigil", 60)):
                with patch.object(WRAPPER.sys, "argv", argv), \
                        patch.object(WRAPPER.subprocess, "run", side_effect=failure), \
                        contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(WRAPPER.main(), 1)
                self.assertFalse(output.exists())
            healthy = subprocess.CompletedProcess([], 0, json.dumps(
                {"status": "ok", "data": {"output": payload}}), "")
            with patch.object(WRAPPER.sys, "argv", argv), \
                    patch.object(WRAPPER.subprocess, "run", return_value=healthy), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(WRAPPER.main(), 0)
            original = output.read_bytes()
            candidate = WRAPPER.CPU.read_candidate(output)
            with self.assertRaises(FileExistsError):
                WRAPPER.publish_candidate(output, candidate)
            link = Path(directory) / "link.json"
            link.symlink_to(output)
            with self.assertRaises(FileExistsError):
                WRAPPER.publish_candidate(link, candidate)
            self.assertEqual(output.read_bytes(), original)

    def test_reference_generation_requires_explicit_authorization(self):
        environment = dict(os.environ)
        environment.pop("SIGIL_GENERATE_AUTORESEARCH_FIT_REFERENCE", None)
        result = subprocess.run([WRAPPER.sys.executable,
                                 str(ROOT / "tests/fixtures/autoresearch-fit/generate_reference.py")],
                                env=environment, capture_output=True, text=True, timeout=60)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")


@unittest.skipUnless(os.environ.get("SIGIL_INTEGRATION_CLI"), "native solver CLI explicitly required")
class FittingNativeTests(unittest.TestCase):
    def test_fresh_checkout_fit_export_and_independent_cpu_evaluation(self):
        cli = os.environ["SIGIL_INTEGRATION_CLI"]
        with tempfile.TemporaryDirectory(prefix="sigil-fit-workflow-") as directory:
            root = Path(directory)
            ignore = shutil.ignore_patterns(".sigil", "__pycache__", "sigil-package.lock.json")
            for name in ("autoresearch", "autoresearch-cpu"):
                shutil.copytree(ROOT / "programs" / name, root / "programs" / name, ignore=ignore)
            for name in ("autodiff", "numeric", "optim", "records", "json", "rng", "checkpoint", "exchange"):
                shutil.copytree(ROOT / "packages" / name, root / name, ignore=ignore)
            fitting, cpu = root / "programs/autoresearch", root / "programs/autoresearch-cpu"
            shutil.copytree(ROOT / "packages/bytes/versions/0.1.0-public.5", root / "bytes", ignore=ignore)
            for target, deps in ((fitting, ("autodiff", "numeric", "optim", "records", "json", "rng", "bytes", "checkpoint", "exchange")), (cpu, ("autodiff",))):
                command = [cli, "package-lock", "--root", str(target), "--json"]
                for name in deps:
                    command.extend(["--dependency", f"sigil/{name}={root / name}"])
                result = subprocess.run(command, capture_output=True, timeout=60)
                self.assertEqual(result.returncode, 0, result)
            output = root / "fitted.json"
            command = [WRAPPER.sys.executable, str(fitting / "run.py"), "--sigil", cli,
                       "--candidate", str(cpu / "candidates/sgd.json"), "--rounds", "3",
                       "--candidate-out", str(output)]
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result)
            fitted = json.loads(result.stdout)
            self.assertEqual((fitted["attempted"], fitted["accepted"], fitted["rejected"]), (3, 1, 2))
            self.assertEqual(fitted["candidate"], WRAPPER.CPU.read_candidate(output))
            candidate_bytes = output.read_bytes()
            record_command = [WRAPPER.sys.executable, str(fitting / "run.py"), "--sigil", cli,
                              "--candidate", str(cpu / "candidates/sgd.json"), "--rounds", "3", "--record"]
            record_run = subprocess.run(record_command, capture_output=True, timeout=60)
            self.assertEqual(record_run.returncode, 0, record_run)
            request = WRAPPER.encode(WRAPPER.CPU.read_candidate(cpu / "candidates/sgd.json"), 20, 3, record=True)
            saved = WRAPPER.decode_record(record_run.stdout, request)
            self.assertEqual(saved["candidate"], fitted["candidate"])
            self.assertEqual(saved["history"], fitted["history"])
            repeated_record = subprocess.run(record_command, capture_output=True, timeout=60)
            self.assertEqual(repeated_record.returncode, 0, repeated_record)
            self.assertEqual(repeated_record.stdout, record_run.stdout)
            repeat = subprocess.run(command, capture_output=True, text=True, timeout=60)
            self.assertNotEqual(repeat.returncode, 0)
            self.assertEqual(output.read_bytes(), candidate_bytes)
            wire = WRAPPER.CPU.encode(fitted["candidate"], 20)
            result = subprocess.run([cli, "run", "--package", str(cpu), "--input", wire.hex(),
                                     "--fuel", "500000", "--json"], capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result)
            native = bytes(json.loads(result.stdout)["data"]["output"])
            values = struct.unpack_from("<14d", native, 32)
            self.assertEqual(list(values), [fitted["loss"], fitted["fitness"], *fitted["positions"],
                                           *fitted["momentum"], *fitted["gradient"]])
            # Fresh check binds the graph; cached provider drift must fail closed
            # without overwriting either the lock or previously exported result.
            locked = (fitting / "sigil-package.lock.json").read_bytes()
            graph = json.loads(locked)
            optim = next(n for n in graph["nodes"] if n["package"] == "sigil/optim")
            path = fitting / optim["source"]["locator"] / "src/optim.sigil"
            path.write_text("module optim;\n")
            failed = subprocess.run([cli, "check", "--package", str(fitting), "--json"],
                                    capture_output=True, text=True, timeout=60)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(json.loads(failed.stdout)["data"]["code"], "E_HASH_MISMATCH")
            self.assertEqual((fitting / "sigil-package.lock.json").read_bytes(), locked)
            self.assertEqual(output.read_bytes(), candidate_bytes)


if __name__ == "__main__":
    unittest.main()
