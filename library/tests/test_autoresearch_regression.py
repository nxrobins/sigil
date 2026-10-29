"""Execute fixed-regression fitting, search and resume without weakening native gates.

Answers come from independently executed PyTorch/upstream C, not SIGIL. Live
numerical mutations prove the comparison detects wrong gradients and validation
leakage; identity refusals leave prior files intact. Native tests require an
explicit solver CLI and never replace an existing application's lock or cache.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "programs/autoresearch-regression"
FIXTURE = ROOT / "tests/fixtures/autoresearch-regression"
CLI = os.environ.get("SIGIL_INTEGRATION_CLI")
SPEC = importlib.util.spec_from_file_location("regression_transport", PACKAGE / "search.py")
DRIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DRIVER)
REFERENCE = json.loads((FIXTURE / "torch-pcg-v1.json").read_bytes())


def close_values(actual, expected, *, atol=1e-10, rtol=1e-10):
    return len(actual) == len(expected) and all(
        math.isfinite(a) and math.isfinite(e) and math.isclose(a, e, abs_tol=atol, rel_tol=rtol)
        for a, e in zip(actual, expected, strict=True))


def states_match(actual, expected):
    if len(actual) != 1736 or len(expected) != 1736 or actual[:256] != expected[:256]:
        return False
    for i in range(8):
        at = 256 + i * 144
        if actual[at:at+8] != expected[at:at+8] or actual[at+72:at+128] != expected[at+72:at+128]:
            return False
        a = struct.unpack_from("<8d", actual, at+8) + struct.unpack_from("<2d", actual, at+128)
        b = struct.unpack_from("<8d", expected, at+8) + struct.unpack_from("<2d", expected, at+128)
        if not close_values(a, b):
            return False
    return close_values(struct.unpack_from("<41d", actual, 1408), struct.unpack_from("<41d", expected, 1408))


def fingerprint(directory):
    return {p.relative_to(directory).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in directory.rglob("*") if p.is_file() and "__pycache__" not in p.parts}


def rebind(package):
    """Temporary live mutants receive real metadata and a new native graph."""
    def digest(name):
        return "sha256:" + hashlib.sha256((package / name).read_bytes()).hexdigest()
    inputs = json.loads((package / "tool-inputs.json").read_bytes())
    inputs["files"] = {name: digest(name) for name in inputs["files"]}
    (package / "tool-inputs.json").write_text(json.dumps(inputs, sort_keys=True, indent=2) + "\n")
    manifest = json.loads((package / "sigil-package.json").read_bytes())
    manifest["evidence"]["evidence_manifest_hash"] = digest("tool-inputs.json")
    (package / "sigil-package.json").write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")


class RegressionContractTests(unittest.TestCase):
    def test_comparators_reject_planted_numeric_structural_and_history_errors(self):
        self.assertTrue(close_values([1., -0.], [1., 0.]))
        for changed in ([2., 0.], [math.nan, 0.], [math.inf, 0.], [1.]):
            self.assertFalse(close_values(changed, [1., 0.]))
        state = bytes.fromhex(REFERENCE["searches"][0]["states"][-1])
        self.assertTrue(states_match(state, state))
        for offset in (40, 256+72, 160):
            changed = bytearray(state)
            changed[offset] ^= 1
            self.assertFalse(states_match(changed, state))
        for offset in (256+8, 256+128, 1408):
            changed = bytearray(state)
            struct.pack_into("<d", changed, offset, struct.unpack_from("<d", changed, offset)[0] + 1.)
            self.assertFalse(states_match(changed, state))

    def test_dataset_identity_configuration_and_reference_contracts(self):
        manifest = json.loads((PACKAGE / "sigil-package.json").read_bytes())
        previous = json.loads((ROOT / "programs/autoresearch/sigil-package.json").read_bytes())
        self.assertEqual(manifest["dependencies"], previous["dependencies"])
        self.assertEqual(manifest["declared"]["effects"], ["Alloc"])
        self.assertEqual(manifest["declared"]["host_imports"], [])
        wire, identity = DRIVER.dataset_bytes(PACKAGE)
        self.assertEqual(len(wire), 104)
        self.assertEqual(identity, REFERENCE["dataset_sha256"])
        self.assertEqual(REFERENCE["torch"], "2.14.1")
        self.assertEqual(REFERENCE["dtype"], "float64")
        self.assertGreaterEqual(len(REFERENCE["fits"]), 33)
        self.assertGreaterEqual(len(REFERENCE["searches"]), 4)
        self.assertEqual(len(DRIVER.initial_request(42, 54, 1, 12, True)), 32)
        with self.assertRaises(ValueError):
            DRIVER.initial_request(42, 54, 1, 13, True)
        with tempfile.TemporaryDirectory() as directory:
            package = Path(directory)
            changed = json.loads((PACKAGE / "dataset.json").read_bytes())
            changed["train"][0][1] += 1.
            (package / "dataset.json").write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                DRIVER.dataset_bytes(package)

    def test_reference_generation_requires_explicit_opt_in(self):
        environment = dict(os.environ)
        environment.pop("SIGIL_GENERATE_REGRESSION_REFERENCE", None)
        result = subprocess.run([sys.executable, str(FIXTURE / "generate_reference.py")],
                                env=environment, capture_output=True, timeout=30)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"SIGIL_GENERATE_REGRESSION_REFERENCE=1", result.stderr)


@unittest.skipUnless(CLI, "set SIGIL_INTEGRATION_CLI to execute the native solver suite")
class RegressionNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scratch = tempfile.TemporaryDirectory(prefix="sigil-regression-tests-")
        cls.addClassCleanup(cls.scratch.cleanup)
        cls.root = Path(cls.scratch.name)
        cls.package = cls.materialize(PACKAGE, cls.root / "consumer")

    @classmethod
    def materialize(cls, source, destination, mutation=None):
        shutil.copytree(source, destination, ignore=shutil.ignore_patterns(".sigil", "__pycache__", "sigil-package.lock.json"))
        if mutation:
            mutation(destination)
            rebind(destination)
        command = [CLI, "package-lock", "--root", str(destination), "--json"]
        for name in ("autodiff", "numeric", "optim", "records", "json", "rng", "bytes", "checkpoint", "exchange"):
            provider = ROOT / "packages" / name
            if name == "bytes":
                provider /= "versions/0.1.0-public.5"
            command += ["--dependency", f"sigil/{name}={provider}"]
        result = subprocess.run(command, capture_output=True, timeout=60)
        if result.returncode:
            raise AssertionError(result.stderr or result.stdout)
        result = subprocess.run([CLI, "check", "--package", str(destination), "--json"], capture_output=True, timeout=120)
        if result.returncode:
            raise AssertionError(result.stderr or result.stdout)
        if json.loads(result.stdout)["data"]["certificate"]["solver_verified"] is not True:
            raise AssertionError("a fresh solver witness is required")
        return destination

    def invoke(self, request, *, package=None, fuel=500000, success=True):
        result = subprocess.run([CLI, "run", "--package", str(package or self.package), "--input", request.hex(),
                                 "--fuel", str(fuel), "--json"], capture_output=True, timeout=90)
        if not success:
            self.assertNotEqual(result.returncode, 0, result.stdout)
            return result
        self.assertEqual(result.returncode, 0, result.stderr or result.stdout)
        envelope = json.loads(result.stdout)
        self.assertEqual(envelope["status"], "ok")
        self.assertEqual(envelope["data"]["proof_tier"], "solver_verified")
        self.assertEqual(envelope["data"]["admission"], "not_evaluated")
        return bytes(envelope["data"]["output"])

    def test_fitting_scores_gradients_acceptance_and_validation_match_pytorch(self):
        self.assertEqual(self.invoke(DRIVER.command(b"RGDS", b"")), DRIVER.dataset_bytes(self.package)[0])
        for case in REFERENCE["fits"]:
            with self.subTest(case=case["name"]):
                request = bytes.fromhex(case["request_hex"])
                result = self.invoke(request)
                self.assertEqual(result[840:], request)
                self.assertEqual(list(struct.unpack_from("<8q", result)), case["header"])
                self.assertEqual(list(struct.unpack_from("<6q", result, 264)), case["decisions"])
                numbers = list(struct.unpack_from("<25d", result, 64) + struct.unpack_from("<66d", result, 312))
                self.assertTrue(close_values(numbers, case["numbers"]), case["name"])
                scores = self.invoke(DRIVER.command(b"RGPR", result[168:184]))
                training, validation = struct.unpack("<2d", scores)
                self.assertTrue(close_values([training, validation], [numbers[11], case["validation_loss"]]))
                if "initial_finite_differences" in case:
                    initial_request = bytearray(request)
                    initial_request[5] = 0
                    initial = self.invoke(initial_request)
                    gradient = struct.unpack_from("<8d", initial, 200)
                    self.assertTrue(close_values(gradient, case["initial_finite_differences"], atol=2e-4, rtol=2e-6))

    def test_all_search_transitions_match_independent_torch_and_c_rng(self):
        for case in REFERENCE["searches"]:
            with self.subTest(seed=case["seed"], steps=case["steps"], hybrid=case["hybrid"]):
                request = DRIVER.initial_request(int(case["seed"]), 54, case["generations"], case["steps"], case["hybrid"])
                state = self.invoke(request)
                self.assertTrue(states_match(state, bytes.fromhex(case["states"][0])))
                for transition, expected in enumerate(case["states"][1:], 1):
                    state = self.invoke(DRIVER.command(b"ASST", state))
                    self.assertTrue(states_match(state, bytes.fromhex(expected)), (case, transition))
                self.assertEqual(DRIVER.header(state)[12], 2)
                self.invoke(DRIVER.command(b"ASST", state), success=False)

    def test_task_dataset_malformed_nonfinite_and_resource_refusals(self):
        old = self.materialize(ROOT / "programs/autoresearch", self.root / "quadratic")
        initial = DRIVER.initial_request(42, 54, 1, 2, True)
        state = self.invoke(initial)
        checkpoint = self.invoke(DRIVER.command(b"ASCK", state))
        restored = self.invoke(DRIVER.command(b"ASOP", initial + checkpoint))
        self.assertEqual(restored, state)
        quadratic = self.invoke(initial, package=old)
        old_checkpoint = self.invoke(DRIVER.command(b"ASCK", quadratic), package=old)
        self.invoke(DRIVER.command(b"ASOP", initial + old_checkpoint), success=False)
        self.invoke(DRIVER.command(b"ASOP", initial + checkpoint), package=old, success=False)
        for index in (16, 160):
            changed = bytearray(state)
            changed[index] ^= 1
            self.invoke(DRIVER.command(b"ASVA", changed), success=False)
        changed = json.loads(checkpoint)
        changed["compatibility"] = "0" * 64
        self.invoke(DRIVER.command(b"ASOP", initial + json.dumps(changed, separators=(",", ":")).encode()), success=False)
        request = bytearray(bytes.fromhex(REFERENCE["fits"][1]["request_hex"]))
        self.invoke(request)
        wrong_task = bytearray(request)
        wrong_task[15] = 1
        self.invoke(wrong_task, success=False)
        self.invoke(wrong_task, package=old)
        for offset, value in ((13, 13), (14, 13), (5, 7), (16, 0)):
            changed = bytearray(request)
            if offset == 16:
                struct.pack_into("<d", changed, 16, math.nan)
            else:
                changed[offset] = value
            self.invoke(changed, success=False)
        maximum = bytearray(bytes.fromhex(next(c for c in REFERENCE["fits"] if c["name"] == "maximum-12x12-fit-3")["request_hex"]))
        maximum[5] = 6
        self.invoke(maximum, success=False)
        self.invoke(request, fuel=1, success=False)
        self.invoke(DRIVER.command(b"RGPR", struct.pack("<2d", math.inf, 0.)), success=False)
        # Accept twins prove refusals have not disabled either working task.
        self.assertEqual(self.invoke(DRIVER.command(b"ASOP", initial + checkpoint)), state)
        self.assertEqual(self.invoke(DRIVER.command(b"ASOP", initial + old_checkpoint), package=old), quadratic)

    def test_live_gradient_fault_is_detected_and_validation_rows_do_not_train(self):
        case = next(c for c in REFERENCE["fits"] if c["name"] == "sgd-4-fit-0")
        request = bytes.fromhex(case["request_hex"])
        normal = self.invoke(request)
        def broken_gradient(package):
            source = package / "src/tool_fit.sigil"
            text = source.read_text()
            old = "result.data.set(6 + i, cell.value);"
            if text.count(old) != 1:
                raise AssertionError("live gradient mutation site must remain unique")
            source.write_text(text.replace(old, "result.data.set(6 + i, 0.0 - cell.value);"))
        mutant = self.materialize(PACKAGE, self.root / "wrong-gradient", broken_gradient)
        result = self.invoke(request, package=mutant)
        self.assertFalse(close_values(struct.unpack_from("<14d", result, 152), case["numbers"][11:25]))
        def changed_validation(package):
            source = package / "src/tool_dataset.sigil"
            text = source.read_text()
            old = "rows.push(1.5); rows.push(4.0);"
            if text.count(old) != 1:
                raise AssertionError("live validation mutation site must remain unique")
            source.write_text(text.replace(old, "rows.push(1.5); rows.push(400.0);"))
        alternate = self.materialize(PACKAGE, self.root / "changed-validation", changed_validation)
        self.assertEqual(self.invoke(request, package=alternate), normal)
        query = DRIVER.command(b"RGPR", normal[168:184])
        self.assertNotEqual(self.invoke(query, package=alternate), self.invoke(query))
        with self.assertRaises(ValueError):
            DRIVER.verify_dataset(CLI, alternate)

    def test_file_search_resume_matches_and_refusals_preserve_prior_outputs(self):
        for arm in ("discrete", "hybrid"):
            base = [sys.executable, str(self.package / "search.py"), "--sigil", CLI,
                    "--generations", "1", "--steps", "2", "--arm", arm]
            def run(extra, success=True):
                result = subprocess.run(base + extra, capture_output=True, text=True, timeout=300)
                if success:
                    self.assertEqual(result.returncode, 0, result.stderr)
                    return json.loads(result.stdout)
                self.assertNotEqual(result.returncode, 0, result)
            full = run(["--out-dir", str(self.root / f"{arm}-full")])
            part = run(["--transitions", "5", "--out-dir", str(self.root / f"{arm}-part")])
            prior = Path(part["checkpoint"])
            preserved = fingerprint(prior.parent)
            final = run(["--resume", str(prior), "--out-dir", str(self.root / f"{arm}-resumed")])
            self.assertTrue(final["complete"])
            self.assertEqual(final["transitions"], 17)
            self.assertEqual(Path(final["checkpoint"]).read_bytes(), Path(full["checkpoint"]).read_bytes())
            self.assertEqual(final["training_loss"], full["training_loss"])
            self.assertEqual(final["validation_loss"], full["validation_loss"])
            for extra in (["--seed", "43"], ["--dataset-sha256", "0"*64]):
                refused = self.root / f"{arm}-refused"
                run([*extra, "--resume", str(prior), "--out-dir", str(refused)], False)
                self.assertFalse(refused.exists())
            run(["--out-dir", str(prior.parent)], False)
            self.assertEqual(fingerprint(prior.parent), preserved)

    def test_cpu_exchange_matches_direct_step_and_refuses_other_dataset(self):
        state = self.invoke(DRIVER.initial_request(42, 54, 1, 2, True))
        identity = bytes.fromhex("17"*32 + "29"*32)
        request = self.invoke(DRIVER.command(b"ASEQ", identity + state))
        envelope = json.loads(request)
        context = bytes.fromhex(envelope["context_hex"])
        expected = struct.pack("<4Q", 42, 54, 1 | (2 << 8) | (1 << 16) | (16 << 24), 0)
        self.assertEqual(context, expected + identity + bytes.fromhex(REFERENCE["dataset_sha256"]))
        self.assertEqual(len(context), 128)
        changed_context = bytearray(context)
        changed_context[96] ^= 1
        envelope["context_hex"] = changed_context.hex()
        self.invoke(DRIVER.command(b"ASED", json.dumps(envelope, separators=(",", ":")).encode()), success=False)
        work = self.invoke(DRIVER.command(b"ASED", request))
        report = self.invoke(work)
        response = self.invoke(DRIVER.command(b"ASER", struct.pack("<HB", len(request), 0) + request + report))
        actual = self.invoke(DRIVER.command(b"ASEA", identity + state + response))
        self.assertEqual(actual, self.invoke(DRIVER.command(b"ASST", state)))
        changed = bytearray(state)
        changed[160] ^= 1
        self.invoke(DRIVER.command(b"ASEA", identity + changed + response), success=False)
        self.invoke(DRIVER.command(b"ASEA", identity + actual + response), success=False)
        wrong = bytes.fromhex("18"*32 + "29"*32)
        self.invoke(DRIVER.command(b"ASEA", wrong + state + response), success=False)

    def test_exchange_resume_preserves_identity_and_rejects_corrupt_checkpoints(self):
        base = [sys.executable, str(self.package / "search.py"), "--sigil", CLI,
                "--generations", "1", "--steps", "2", "--arm", "hybrid"]
        exchange = ["--evaluation", "exchange", "--job-id", "17"*32]

        def run(extra, success=True):
            result = subprocess.run(base + extra, capture_output=True, text=True, timeout=300)
            if success:
                self.assertEqual(result.returncode, 0, result.stderr)
                return json.loads(result.stdout)
            self.assertNotEqual(result.returncode, 0, result)

        full = run(["--transitions", "4", "--out-dir", str(self.root / "direct-four")])
        part = run([*exchange, "--transitions", "2", "--out-dir", str(self.root / "exchange-two")])
        prior = Path(part["checkpoint"])
        preserved = fingerprint(prior.parent)
        resumed = run([*exchange, "--transitions", "2", "--resume", str(prior),
                       "--out-dir", str(self.root / "exchange-four")])
        self.assertEqual(resumed["transitions"], 4)
        self.assertEqual(Path(full["checkpoint"]).read_bytes(), Path(resumed["checkpoint"]).read_bytes())
        for mode in ([], ["--evaluation", "exchange", "--job-id", "18"*32]):
            refused = self.root / "exchange-refused"
            run([*mode, "--transitions", "0", "--resume", str(prior), "--out-dir", str(refused)], False)
            self.assertFalse(refused.exists())
        # Preserve the actual earlier archive; corrupt only create-new copies.
        for problem in ("program", "checkpoint"):
            damaged = self.root / f"damaged-{problem}"
            damaged.mkdir()
            marker = (prior.parent / "program-identity.hex").read_bytes()
            if problem == "program":
                marker = marker[:74] + (b"0" if marker[74:75] != b"0" else b"1") + marker[75:]
            DRIVER.write_new(damaged / "program-identity.hex", marker)
            DRIVER.write_new(damaged / prior.name, prior.read_bytes()[:-1] if problem == "checkpoint" else prior.read_bytes())
            before = fingerprint(damaged)
            refused = self.root / f"damaged-{problem}-refused"
            run([*exchange, "--transitions", "0", "--resume", str(damaged / prior.name),
                 "--out-dir", str(refused)], False)
            self.assertFalse(refused.exists())
            self.assertEqual(fingerprint(damaged), before)
        self.assertEqual(fingerprint(prior.parent), preserved)


if __name__ == "__main__":
    unittest.main()
