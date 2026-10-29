"""Strict local transport and a fresh interrupted native search workflow.

The Python driver never supplies a numerical or mutation backend. Native search
is compared independently against Torch/C in the CLI integration suite.
"""
import importlib.util
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
SPEC = importlib.util.spec_from_file_location("search_transport", ROOT / "programs/autoresearch/search.py")
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)


class SearchTransportTests(unittest.TestCase):
    def test_exchange_identity_requires_fresh_certificate_and_exact_job_id(self):
        identity = "a5" * 32
        result = {"status": "ok", "data": {"certificate": {
            "solver_verified": True, "artifact_identity_hash": "sha256:" + identity}}}
        completed = subprocess.CompletedProcess([], 0, json.dumps(result).encode(), b"")
        with patch.object(DRIVER.subprocess, "run", return_value=completed) as run:
            self.assertEqual(DRIVER.evaluation_identity("sigil", Path("consumer"), "17" * 32),
                             bytes.fromhex("17" * 32 + identity))
            self.assertEqual(run.call_args.args[0], ["sigil", "check", "--package", "consumer", "--json"])
            for bad in (None, "", "a" * 63, "A" * 64, "00 " * 32):
                with self.assertRaises(ValueError):
                    DRIVER.evaluation_identity("sigil", Path("consumer"), bad)
            result["data"]["certificate"]["solver_verified"] = False
            completed.stdout = json.dumps(result).encode()
            with self.assertRaises(ValueError):
                DRIVER.evaluation_identity("sigil", Path("consumer"), "17" * 32)

    def test_configuration_limits_and_exact_unsigned_identity(self):
        raw = DRIVER.initial_request(2**64 - 1, 2**63 - 1, 40, 20, True)
        self.assertEqual(len(raw), 32)
        self.assertEqual(struct.unpack_from("<3Q", raw, 8), (2**64 - 1, 2**63 - 1, 328))
        for args in ((-1, 54, 1, 20, True), (True, 54, 1, 20, True),
                     (42, 2**63, 1, 20, True), (42, 54, 0, 20, True),
                     (42, 54, 41, 20, True), (42, 54, 1, 21, True),
                     (42, 54, 1, 20, 1), (42, 54, 1, 20, True, 17)):
            with self.assertRaises(ValueError):
                DRIVER.initial_request(*args)

    def test_checkpoint_files_are_bounded_regular_and_never_overwritten(self):
        state = struct.pack("<32Q", 1397904193, 1, 1, *([0] * 29)) + bytes(1480)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = DRIVER.publish(root, state, b"opaque-native-checkpoint")
            self.assertEqual(DRIVER.read_checkpoint(path), b"opaque-native-checkpoint")
            with self.assertRaises(FileExistsError):
                DRIVER.publish(root, state, b"changed")
            link = root / "link"
            link.symlink_to(path)
            with self.assertRaises(OSError):
                DRIVER.read_checkpoint(link)
            fifo = root / "fifo"
            os.mkfifo(fifo)
            with self.assertRaises(ValueError):
                DRIVER.read_checkpoint(fifo)
            with self.assertRaises(ValueError):
                DRIVER.read_checkpoint(root)
            path.write_bytes(b"x" * 8193)
            with self.assertRaises(ValueError):
                DRIVER.read_checkpoint(path)

    def test_reference_generation_requires_explicit_opt_in(self):
        environment = dict(os.environ)
        environment.pop("SIGIL_GENERATE_AUTORESEARCH_SEARCH_REFERENCE", None)
        result = subprocess.run([DRIVER.sys.executable,
                                 str(ROOT / "tests/fixtures/autoresearch-search/generate_reference.py")],
                                env=environment, capture_output=True, timeout=60)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"SIGIL_GENERATE_AUTORESEARCH_SEARCH_REFERENCE=1", result.stderr)


@unittest.skipUnless(os.environ.get("SIGIL_INTEGRATION_CLI"), "native solver CLI explicitly required")
class SearchNativeTests(unittest.TestCase):
    def test_fresh_dependency_graph_interrupt_resume_and_wrong_job_refusal(self):
        cli = os.environ["SIGIL_INTEGRATION_CLI"]
        with tempfile.TemporaryDirectory(prefix="sigil-search-workflow-") as directory:
            root = Path(directory)
            ignore = shutil.ignore_patterns(".sigil", "__pycache__", "sigil-package.lock.json")
            consumer = root / "consumer"
            shutil.copytree(ROOT / "programs/autoresearch", consumer, ignore=ignore)
            dependencies = ("autodiff", "numeric", "optim", "records", "json", "rng", "checkpoint", "exchange", "bytes")
            command = [cli, "package-lock", "--root", str(consumer), "--json"]
            for name in dependencies:
                source = ROOT / "packages" / name
                if name == "bytes":
                    source = source / "versions/0.1.0-public.5"
                shutil.copytree(source, root / name, ignore=ignore)
                command += ["--dependency", f"sigil/{name}={root / name}"]
            result = subprocess.run(command, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result)
            base = [DRIVER.sys.executable, str(consumer / "search.py"), "--sigil", cli,
                    "--generations", "1", "--steps", "2"]

            def run(extra):
                return subprocess.run(base + extra, capture_output=True, text=True, timeout=180)

            uninterrupted = run(["--out-dir", str(root / "full")])
            self.assertEqual(uninterrupted.returncode, 0, uninterrupted)
            full = json.loads(uninterrupted.stdout)
            self.assertTrue(full["complete"])
            interrupted = run(["--out-dir", str(root / "part"), "--transitions", "5"])
            self.assertEqual(interrupted.returncode, 0, interrupted)
            part = json.loads(interrupted.stdout)
            self.assertFalse(part["complete"])
            preserved = Path(part["checkpoint"]).read_bytes()
            resumed = run(["--resume", part["checkpoint"], "--out-dir", str(root / "resumed")])
            self.assertEqual(resumed.returncode, 0, resumed)
            final = json.loads(resumed.stdout)
            self.assertTrue(final["complete"])
            self.assertEqual(Path(final["checkpoint"]).read_bytes(), Path(full["checkpoint"]).read_bytes())
            self.assertEqual(Path(part["checkpoint"]).read_bytes(), preserved)
            wrong = run(["--seed", "43", "--resume", part["checkpoint"], "--out-dir", str(root / "wrong")])
            self.assertNotEqual(wrong.returncode, 0)
            self.assertFalse((root / "wrong").exists())
            repeated = run(["--resume", part["checkpoint"], "--out-dir", str(root / "resumed")])
            self.assertNotEqual(repeated.returncode, 0)
            self.assertEqual(Path(final["checkpoint"]).read_bytes(), Path(full["checkpoint"]).read_bytes())
            exchange = ["--evaluation", "exchange", "--job-id", "17" * 32]
            interrupted = run(exchange + ["--out-dir", str(root / "exchange-part"), "--transitions", "5"])
            self.assertEqual(interrupted.returncode, 0, interrupted)
            part = json.loads(interrupted.stdout)
            checkpoint = Path(part["checkpoint"])
            preserved = checkpoint.read_bytes()
            response = checkpoint.parent / "evaluation-0000-response.json"
            response_before = response.read_bytes()
            self.assertEqual(len(list(checkpoint.parent.glob("evaluation-*-request.json"))), 5)
            resumed = run(exchange + ["--resume", str(checkpoint), "--out-dir", str(root / "exchange-resumed")])
            self.assertEqual(resumed.returncode, 0, resumed)
            finished = json.loads(resumed.stdout)
            self.assertTrue(finished["complete"])
            self.assertEqual(Path(finished["checkpoint"]).read_bytes(), Path(full["checkpoint"]).read_bytes())
            self.assertEqual(checkpoint.read_bytes(), preserved)
            self.assertEqual(response.read_bytes(), response_before)
            for extra in (["--evaluation", "exchange", "--job-id", "18" * 32], []):
                refused = run(extra + ["--resume", str(checkpoint), "--out-dir", str(root / "wrong-exchange")])
                self.assertNotEqual(refused.returncode, 0, refused)
                self.assertFalse((root / "wrong-exchange").exists())


if __name__ == "__main__":
    unittest.main()
