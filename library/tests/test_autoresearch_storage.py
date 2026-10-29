"""Explicit Public imports and serialized checkpoint transport, never a search backend.

The native workflow is opt-in and uses fresh locked packages and the real storage
host. Unit tests prove policy/identity/lease failures leave prior state intact.
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("stored_search", ROOT / "programs/autoresearch/search.py")
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)


class StorageTransportTests(unittest.TestCase):
    def test_public_import_is_opt_in_and_file_resume_is_separate(self):
        args = SimpleNamespace(kv_store=None, resume_kv=False, allow_public_checkpoint_import=False,
                               storage_host=None, resume=None)
        DRIVER.storage_options(args)
        for field, value in (("resume_kv", True), ("allow_public_checkpoint_import", True),
                             ("storage_host", "host")):
            changed = SimpleNamespace(**vars(args))
            setattr(changed, field, value)
            with self.assertRaises(ValueError):
                DRIVER.storage_options(changed)
        args.kv_store, args.storage_host = Path("store"), "host"
        with self.assertRaises(ValueError):
            DRIVER.storage_options(args)
        args.allow_public_checkpoint_import = True
        DRIVER.storage_options(args)
        args.resume = Path("checkpoint")
        with self.assertRaises(ValueError):
            DRIVER.storage_options(args)

    def test_writer_lease_identity_and_symlink_refusals_preserve_prior_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "store"
            lease = DRIVER.open_store(root, False, b"job-program-config")
            try:
                with self.assertRaises(OSError):
                    DRIVER.open_store(root, True, b"job-program-config")
                with self.assertRaises(FileExistsError):
                    DRIVER.open_store(root, False, b"different")
                self.assertEqual(DRIVER.read_checkpoint(root / "public-search-identity.bin"), b"job-program-config")
            finally:
                os.close(lease)
            with self.assertRaises(ValueError):
                DRIVER.open_store(root, True, b"different")
            lease = DRIVER.open_store(root, True, b"job-program-config")
            os.close(lease)
            alias = Path(directory) / "alias"
            alias.symlink_to(root, target_is_directory=True)
            with self.assertRaises(ValueError):
                DRIVER.open_store(alias, True, b"job-program-config")
            (root / "writer.lock").rename(root / "prior-lock")
            (root / "writer.lock").symlink_to(root / "prior-lock")
            with self.assertRaises(OSError):
                DRIVER.open_store(root, True, b"job-program-config")
            self.assertEqual(DRIVER.read_checkpoint(root / "public-search-identity.bin"), b"job-program-config")

    def test_storage_transport_checks_policy_bounds_and_separate_grants(self):
        envelope = {"status": "ok", "data": {"output": [0, 255], "source_label": "Internal",
                    "result_label": "Public", "import_policy": "operator-declared-public-checkpoints-v1"}}
        result = subprocess.CompletedProcess([], 0, json.dumps(envelope).encode(), b"")
        with patch.object(DRIVER.subprocess, "run", return_value=result) as run:
            self.assertEqual(DRIVER.stored_checkpoint("host", Path("package"), Path("store")), b"\x00\xff")
            command = run.call_args.args[0]
            self.assertIn("--allow-public-checkpoint-import", command)
            self.assertIn("--kv-read", command)
            self.assertNotIn("--kv-write", command)
            for field, bad in (("import_policy", "implicit"), ("source_label", "Secret"),
                               ("result_label", "Internal"), ("output", [True]), ("output", [0] * 8193)):
                changed = {**envelope, "data": {**envelope["data"], field: bad}}
                result.stdout = json.dumps(changed).encode()
                with self.assertRaises(ValueError):
                    DRIVER.stored_checkpoint("host", Path("package"), Path("store"))
            envelope["data"]["output"] = []
            result.stdout = json.dumps(envelope).encode()
            self.assertEqual(DRIVER.stored_checkpoint("host", Path("package"), Path("store"), b"old", b"new"), b"")
            command = run.call_args.args[0]
            self.assertIn("--kv-write", command)
            self.assertIn("--kv-read", command)
            self.assertEqual(bytes.fromhex(command[command.index("--input-hex") + 1]),
                             b"AKVP\x01\x00\x00\x00\x03\x00\x00\x00oldnew")
            for old, new in ((b"x" * 8193, b"new"), (b"old", b""), (b"old", b"x" * 8193)):
                with self.assertRaises(ValueError):
                    DRIVER.stored_checkpoint("host", Path("package"), Path("store"), old, new)

    def test_missing_opt_in_refuses_before_compilation_or_filesystem_changes(self):
        arguments = ["search.py", "--kv-store", "store", "--storage-host", "host", "--out-dir", "output"]
        with patch.object(DRIVER.sys, "argv", arguments), patch.object(DRIVER, "invoke") as invoke, \
                patch.object(DRIVER, "open_store") as opened, patch.object(DRIVER, "evaluation_identity") as identity, \
                patch.object(DRIVER.sys, "stderr"):
            self.assertEqual(DRIVER.main(), 1)
            invoke.assert_not_called()
            opened.assert_not_called()
            identity.assert_not_called()


@unittest.skipUnless(os.environ.get("SIGIL_INTEGRATION_CLI") and os.environ.get("SIGIL_STORAGE_HOST"),
                     "native solver CLI and explicit storage host required")
class StorageNativeTests(unittest.TestCase):
    def test_fresh_kv_search_resume_matches_files_and_corruption_does_not_advance(self):
        cli, host = os.environ["SIGIL_INTEGRATION_CLI"], os.environ["SIGIL_STORAGE_HOST"]
        with tempfile.TemporaryDirectory(prefix="sigil-kv-search-") as directory:
            root = Path(directory)
            ignore = shutil.ignore_patterns(".sigil", "__pycache__", "sigil-package.lock.json")
            for name in ("autoresearch", "autoresearch-store"):
                shutil.copytree(ROOT / "programs" / name, root / name, ignore=ignore)
            names = ("autodiff", "numeric", "optim", "records", "json", "rng", "checkpoint", "exchange", "bytes", "storage", "kv")
            for name in names:
                source = ROOT / "packages" / name
                if name == "bytes":
                    source /= "versions/0.1.0-public.5"
                shutil.copytree(source, root / name, ignore=ignore)
            for consumer, providers in (("autoresearch", names[:9]), ("autoresearch-store", names[9:])):
                command = [cli, "package-lock", "--root", str(root / consumer), "--json"]
                for name in providers:
                    command += ["--dependency", f"sigil/{name}={root / name}"]
                result = subprocess.run(command, capture_output=True, timeout=60)
                self.assertEqual(result.returncode, 0, result)
            base = [DRIVER.sys.executable, str(root / "autoresearch/search.py"), "--sigil", cli,
                    "--generations", "1", "--steps", "0", "--transitions", "1"]
            kv = ["--kv-store", str(root / "store"), "--storage-host", host,
                  "--storage-package", str(root / "autoresearch-store"), "--allow-public-checkpoint-import"]

            def run(extra):
                return subprocess.run(base + extra, capture_output=True, text=True, timeout=180)

            first = run(kv + ["--out-dir", str(root / "part")])
            self.assertEqual(first.returncode, 0, first)
            checkpoint = Path(json.loads(first.stdout)["checkpoint"])
            preserved = checkpoint.read_bytes()
            resumed = run(kv + ["--resume-kv", "--out-dir", str(root / "resumed")])
            self.assertEqual(resumed.returncode, 0, resumed)
            plain = run(["--transitions", "2", "--out-dir", str(root / "plain")])
            self.assertEqual(plain.returncode, 0, plain)
            resumed_path = Path(json.loads(resumed.stdout)["checkpoint"])
            self.assertEqual(resumed_path.read_bytes(), Path(json.loads(plain.stdout)["checkpoint"]).read_bytes())
            self.assertEqual(checkpoint.read_bytes(), preserved)
            prior = resumed_path.read_bytes()
            for extra in (["--seed", "43"], ["--evaluation", "exchange", "--job-id", "17" * 32]):
                refused = run(kv + ["--resume-kv", "--out-dir", str(root / "wrong")] + extra)
                self.assertNotEqual(refused.returncode, 0)
                self.assertFalse((root / "wrong").exists())
            next_run = run(["--transitions", "3", "--out-dir", str(root / "next")])
            self.assertEqual(next_run.returncode, 0, next_run)
            next_checkpoint = Path(json.loads(next_run.stdout)["checkpoint"]).read_bytes()
            real_run = subprocess.run

            def lose_reply(arguments, **kwargs):
                completed = real_run(arguments, **kwargs)
                self.assertEqual(completed.returncode, 0, completed)
                raise subprocess.TimeoutExpired(arguments, 60)

            with patch.object(DRIVER.subprocess, "run", side_effect=lose_reply):
                with self.assertRaises(subprocess.TimeoutExpired):
                    DRIVER.stored_checkpoint(host, root / "autoresearch-store", root / "store", prior, next_checkpoint)
            recovered = run(kv + ["--resume-kv", "--transitions", "0", "--out-dir", str(root / "recovered")])
            self.assertEqual(recovered.returncode, 0, recovered)
            self.assertEqual(Path(json.loads(recovered.stdout)["checkpoint"]).read_bytes(), next_checkpoint)
            self.assertEqual(resumed_path.read_bytes(), prior)
            # The same storage path also composes with the versioned CPU worker.
            exchange = kv.copy()
            exchange[1] = str(root / "exchange-store")
            exchange += ["--evaluation", "exchange", "--job-id", "17" * 32]
            first_exchange = run(exchange + ["--out-dir", str(root / "exchange-part")])
            self.assertEqual(first_exchange.returncode, 0, first_exchange)
            last_exchange = run(exchange + ["--resume-kv", "--out-dir", str(root / "exchange-resumed")])
            self.assertEqual(last_exchange.returncode, 0, last_exchange)
            self.assertEqual(Path(json.loads(last_exchange.stdout)["checkpoint"]).read_bytes(), prior)
            DRIVER.stored_checkpoint(host, root / "autoresearch-store", root / "store", next_checkpoint, b"malformed")
            refused = run(kv + ["--resume-kv", "--out-dir", str(root / "corrupt")])
            self.assertNotEqual(refused.returncode, 0)
            self.assertFalse((root / "corrupt").exists())
            self.assertEqual(DRIVER.stored_checkpoint(host, root / "autoresearch-store", root / "store"), b"malformed")
            self.assertEqual(resumed_path.read_bytes(), prior)


if __name__ == "__main__":
    unittest.main()
