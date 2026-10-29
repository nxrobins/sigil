"""Strict transport and a fresh native proposal -> CPU-evaluation workflow."""
import contextlib
import ctypes
import importlib.util
import json
import io
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "programs/autoresearch-propose"
SPEC = importlib.util.spec_from_file_location("autoresearch_propose_transport", EXAMPLE / "run.py")
WRAPPER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(WRAPPER)


def seed_candidate():
    return WRAPPER.CPU.read_candidate(ROOT / "programs/autoresearch-cpu/candidates/sgd.json")


class ProposalTransportTests(unittest.TestCase):
    def setUp(self):
        self.candidate = seed_candidate()
        self.request = WRAPPER.encode(self.candidate, 20, 42, 54)
        self.wire = WRAPPER.CPU.encode(self.candidate, 20)
        self.report = struct.pack("<5Q", 1, 2**64 - 1, 109, 0, len(self.wire)) + self.wire + self.request

    def test_exact_unsigned_words_and_resume_round_trip(self):
        record = WRAPPER.decode(self.report, self.request)
        self.assertEqual(record["state"], "ffffffffffffffff")
        restored = WRAPPER.encode(resume=record)
        self.assertEqual(struct.unpack_from("<2Q", restored, 8), (2**64 - 1, 109))
        self.assertEqual(restored[24:], self.wire)
        self.assertEqual(restored[5], 1)
        self.assertNotEqual(restored, self.request)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "checkpoint.json"
            path.write_text(json.dumps(record))
            self.assertEqual(WRAPPER.read_checkpoint(path), record)

    def test_invalid_checkpoint_fields_profiles_states_and_sizes_refuse(self):
        good = WRAPPER.decode(self.report, self.request)
        bad = [None, [], {**good, "extra": 0}, {**good, "format": "v2"},
               {**good, "algorithm": "old-lcg"}, {**good, "steps": True},
               {**good, "increment": "0000000000000002"}, {**good, "mutation": True},
               {**good, "mutation": 6}, {**good, "request_sha256": "00"},
               {**good, "candidate": {**self.candidate, "numeric": WRAPPER.CPU.Q16_IMPORT}}]
        for field in ("state", "increment"):
            bad.extend({**good, field: value} for value in
                       ("0", "FFFFFFFFFFFFFFFF", 2**64 - 1, "-000000000000001", "0" * 17))
        for record in bad:
            with self.subTest(record=record), self.assertRaises(ValueError):
                WRAPPER.validate_checkpoint(record)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "checkpoint.json"
            text = json.dumps(good)
            for raw in (text[:-1] + ',"state":"0000000000000000"}', " " * 16385, "[", '{"a":NaN}'):
                path.write_text(raw)
                with self.assertRaises(ValueError):
                    WRAPPER.read_checkpoint(path)

    def test_encoder_refuses_bad_seeds_and_mixed_resume(self):
        for seed, stream in ((-1, 0), (2**64, 0), (True, 0), (1, -1), (1, 2**63), (1, True)):
            with self.assertRaises(ValueError):
                WRAPPER.encode(self.candidate, 20, seed, stream)
        record = WRAPPER.decode(self.report, self.request)
        with self.assertRaises(ValueError):
            WRAPPER.encode(self.candidate, resume=record)
        with self.assertRaises(ValueError):
            WRAPPER.encode(resume=record, seed=42)
        self.assertEqual(len(WRAPPER.encode(self.candidate, 20, 2**64 - 1, 2**63 - 1)), 104)

    def test_decoder_rejects_bad_echo_framing_nonfinite_and_changed_steps(self):
        bad = [self.report[:-1], self.report + b"!", self.report[:-1] + b"!"]
        for offset, value in ((0, 2), (16, 2), (16, 111), (24, 6), (32, 75), (32, 121)):
            data = bytearray(self.report)
            struct.pack_into("<Q", data, offset, value)
            bad.append(data)
        for offset, value in ((40, 0), (44, 2), (45, 19), (46, 13), (47, 2), (112, 8), (113, 0)):
            data = bytearray(self.report)
            data[offset] = value
            bad.append(data)
        data = bytearray(self.report)
        struct.pack_into("<d", data, 48, float("nan"))
        bad.append(data)
        for report in bad:
            with self.subTest(report=report), self.assertRaises(ValueError):
                WRAPPER.decode(report, self.request)

    def test_candidate_publication_never_overwrites_files_or_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candidate.json"
            WRAPPER.publish_candidate(path, self.candidate)
            original = path.read_bytes()
            with self.assertRaises(FileExistsError):
                WRAPPER.publish_candidate(path, self.candidate)
            self.assertEqual(path.read_bytes(), original)
            link = Path(directory) / "link.json"
            link.symlink_to(path)
            with self.assertRaises(FileExistsError):
                WRAPPER.publish_candidate(link, self.candidate)
            self.assertEqual(path.read_bytes(), original)

    def test_cli_failures_never_publish_or_substitute_a_proposal(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "new-candidate.json"
            argv = ["run.py", "--candidate", str(ROOT / "programs/autoresearch-cpu/candidates/sgd.json"),
                    "--seed", "42", "--stream", "54", "--candidate-out", str(output)]
            payload = list(self.report)
            bad = [
                subprocess.CompletedProcess([], 1, '{"status":"error"}', ""),
                subprocess.CompletedProcess([], 0, "not JSON", ""),
                subprocess.CompletedProcess([], 0, '[]', ""),
                subprocess.CompletedProcess([], 0, '{"status":"ok","data":{}}', ""),
                subprocess.CompletedProcess([], 0, json.dumps(
                    {"status": "ok", "data": {"output": [True] * len(payload)}}), ""),
                subprocess.CompletedProcess([], 0, json.dumps(
                    {"status": "ok", "data": {"output": payload[:-1]}}), ""),
            ]
            for response in bad:
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
            self.assertEqual(WRAPPER.CPU.read_candidate(output), self.candidate)


class Pcg(ctypes.Structure):
    _fields_ = [("value", ctypes.c_uint64), ("increment", ctypes.c_uint64)]


@unittest.skipUnless(os.environ.get("SIGIL_INTEGRATION_CLI"), "native solver CLI explicitly required")
class ProposalNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="sigil-proposal-workflow-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.directory = Path(cls.temporary.name)
        cls.cli = os.environ["SIGIL_INTEGRATION_CLI"]
        cls.proposal = cls.directory / "proposal"
        cls.cpu = cls.directory / "cpu"
        cls.provider = cls.directory / "rng"
        ignore = shutil.ignore_patterns(".sigil", "__pycache__", "sigil-package.lock.json")
        for source, target in ((EXAMPLE, cls.proposal),
                               (ROOT / "programs/autoresearch-cpu", cls.cpu),
                               (ROOT / "packages/rng", cls.provider),
                               (ROOT / "packages/autodiff", cls.directory / "autodiff")):
            shutil.copytree(source, target, ignore=ignore)
        for target, package, provider in ((cls.proposal, "sigil/rng", cls.provider),
                                         (cls.cpu, "sigil/autodiff", cls.directory / "autodiff")):
            result = subprocess.run([cls.cli, "package-lock", "--root", str(target), "--dependency",
                                     f"{package}={provider}", "--json"], capture_output=True, timeout=60)
            if result.returncode:
                raise AssertionError(result)
        # Real pinned C, not a second handwritten generator.
        upstream = ROOT / "tests/fixtures/rng/upstream/pcg_basic.c"
        shared = cls.directory / "pcg.so"
        subprocess.run(["cc", "-shared", "-fPIC", str(upstream), "-o", str(shared)],
                       check=True, timeout=60, capture_output=True)
        cls.reference = ctypes.CDLL(str(shared))
        cls.reference.pcg32_srandom_r.argtypes = [ctypes.POINTER(Pcg), ctypes.c_uint64, ctypes.c_uint64]
        cls.reference.pcg32_random_r.argtypes = [ctypes.POINTER(Pcg)]
        cls.reference.pcg32_random_r.restype = ctypes.c_uint32
        cls.reference.pcg32_boundedrand_r.argtypes = [ctypes.POINTER(Pcg), ctypes.c_uint32]
        cls.reference.pcg32_boundedrand_r.restype = ctypes.c_uint32

    def native(self, request, package=None, fuel=500000, success=True):
        result = subprocess.run(
            [self.cli, "run", "--package", str(package or self.proposal), "--input",
             request.hex(), "--fuel", str(fuel), "--json"], capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode == 0, success, result)
        if success:
            return bytes(json.loads(result.stdout)["data"]["output"])
        return result

    def expected(self, request):
        first, second = struct.unpack_from("<2Q", request, 8)
        generator = Pcg()
        if request[5] == 0:
            self.reference.pcg32_srandom_r(ctypes.byref(generator), first, second)
        else:
            generator.value, generator.increment = first, second
        candidate = WRAPPER.candidate_from_wire(request[24:])
        def below(bound):
            return self.reference.pcg32_boundedrand_r(ctypes.byref(generator), bound)
        def operand(op):
            return below(8 if op in (4, 5, 6) else 16)
        kind = below(6)
        count = len(candidate["ops"])
        if kind <= 2:
            index = below(count)
            if kind == 0:
                candidate["ops"][index] = below(8)
                candidate["b"][index] = operand(candidate["ops"][index])
            elif kind == 1:
                candidate["a"][index] = below(16)
            else:
                candidate["dst"][index] = 4 + below(12)
        elif kind == 3 and count < 12:
            op, dst, a = below(8), 4 + below(12), below(16)
            for key, value in zip(("ops", "dst", "a", "b"), (op, dst, a, operand(op)), strict=True):
                candidate[key].append(value)
        elif kind == 4 and count > 1:
            index = below(count)
            for key in ("ops", "dst", "a", "b"):
                candidate[key].pop(index)
        elif kind == 5:
            index = below(8)
            unit = self.reference.pcg32_random_r(ctypes.byref(generator)) / 2**32
            candidate["w"][index] = min(4096., max(-4096., candidate["w"][index] + unit * 0.5 - 0.25))
        return candidate, generator.value, generator.increment, kind

    def assert_reference(self, request):
        candidate, value, increment, kind = self.expected(request)
        report = self.native(request)
        record = WRAPPER.decode(report, request)
        self.assertEqual(record["candidate"], candidate)
        self.assertEqual((WRAPPER.word(record["state"]), WRAPPER.word(record["increment"]),
                          record["mutation"]), (value, increment, kind))
        return record

    def test_all_mutations_bounds_replay_and_cpu_composition(self):
        representatives = {}
        for seed in range(512):
            kind = self.expected(WRAPPER.encode(seed_candidate(), 5, seed, 54))[3]
            representatives.setdefault(kind, seed)
        self.assertEqual(set(representatives), set(range(6)))
        seen = set()
        for seed in representatives.values():
            record = self.assert_reference(WRAPPER.encode(seed_candidate(), 5, seed, 54))
            seen.add(record["mutation"])
        self.assertEqual(seen, set(range(6)))
        for count in (1, 12):
            candidate = seed_candidate()
            for key in ("ops", "dst", "a", "b"):
                candidate[key] = (candidate[key] * 6)[:count]
            for seed in representatives.values():
                self.assert_reference(WRAPPER.encode(candidate, 5, seed, 54))
        candidate = seed_candidate()
        candidate["w"] = [-4096., 4096.] * 4
        for seed in (2**64 - 1, 2**63, 0, 1, 2):
            self.assert_reference(WRAPPER.encode(candidate, 5, seed, 2**63 - 1))
        # Find both clipping directions using the C reference, then require
        # native equality at the numerical bounds instead of hoping random
        # seeds happen to hit weight mutation.
        for endpoint in (-4096., 4096.):
            candidate["w"] = [endpoint] * 8
            found = False
            for seed in range(512):
                request = WRAPPER.encode(candidate, 5, seed, 54)
                changed, _, _, kind = self.expected(request)
                if kind == 5 and changed == candidate:
                    self.assert_reference(request)
                    found = True
                    break
            self.assertTrue(found, f"live clipping case for {endpoint}")
        request = WRAPPER.encode(seed_candidate(), 5, 42, 54)
        for _ in range(8):
            record = self.assert_reference(request)
            request = WRAPPER.encode(resume=record)
        checkpoint = self.directory / "checkpoint.json"
        checkpoint.write_text(json.dumps(record))
        resumed = WRAPPER.encode(resume=WRAPPER.read_checkpoint(checkpoint))
        self.assertEqual(resumed, request)
        self.assertEqual(self.native(resumed), self.native(request))
        for _ in range(8):
            record = self.assert_reference(request)
            request = WRAPPER.encode(resume=record)
        exported = self.directory / "proposed-candidate.json"
        WRAPPER.publish_candidate(exported, record["candidate"])
        cpu_request = WRAPPER.CPU.encode(WRAPPER.CPU.read_candidate(exported), 5)
        evaluated = WRAPPER.CPU.decode(self.native(cpu_request, self.cpu), cpu_request)
        self.assertEqual(len(evaluated["gradient"]), 8)
        self.assertGreaterEqual(evaluated["fitness"], evaluated["loss"])

    def test_native_refusals_wrapper_and_live_source_drift(self):
        request = WRAPPER.encode(seed_candidate(), 5, 42, 54)
        self.assert_reference(request)
        bad = [request[:-1], request + b"!", request[:99], request + b"!" * 50]
        for offset, value in ((0, 0), (4, 2), (5, 2), (6, 1), (7, 1),
                              (24, 0), (28, 2), (29, 21), (30, 13), (31, 2),
                              (96, 8), (97, 0), (98, 16), (99, 8)):
            data = bytearray(request)
            data[offset] = value
            bad.append(data)
        data = bytearray(request)
        struct.pack_into("<Q", data, 16, 2**63)
        bad.append(data)
        data = bytearray(request)
        data[5] = 1
        struct.pack_into("<Q", data, 16, 2)
        bad.append(data)
        data = bytearray(request)
        struct.pack_into("<d", data, 32, float("inf"))
        bad.append(data)
        for data in bad:
            self.native(data, success=False)
        self.native(request, fuel=1, success=False)
        output = self.directory / "wrapper-candidate.json"
        command = ["python3", str(EXAMPLE / "run.py"), "--sigil", self.cli,
                   "--package", str(self.proposal), "--candidate",
                   str(ROOT / "programs/autoresearch-cpu/candidates/sgd.json"),
                   "--seed", "42", "--stream", "54", "--steps", "5",
                   "--candidate-out", str(output)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result)
        record = WRAPPER.validate_checkpoint(json.loads(result.stdout))
        self.assertEqual(WRAPPER.CPU.read_candidate(output), record["candidate"])
        original = output.read_bytes()
        repeated = subprocess.run(command, capture_output=True, text=True, timeout=60)
        self.assertNotEqual(repeated.returncode, 0)
        self.assertEqual(output.read_bytes(), original)
        # A separate copied package proves cached drift is refused without harming siblings.
        other = self.directory / "drift-proposal"
        shutil.copytree(self.proposal, other)
        lock = json.loads((other / "sigil-package.lock.json").read_text())
        node = next(n for n in lock["nodes"] if n["package"] == "sigil/rng")
        source = other / node["source"]["locator"] / "src/rng.sigil"
        source.write_text("module rng;\n")
        self.native(request, package=other, success=False)
        self.assert_reference(request)


if __name__ == "__main__":
    unittest.main()
