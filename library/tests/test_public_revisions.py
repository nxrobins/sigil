"""Validate the published revision inventories, not claims about program behavior.

Module provenance is an intentional byte-preservation contract. Native CLI
suites separately execute the implementations and their refusal paths.
"""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return 'sha256:' + hashlib.sha256(data).hexdigest()


def mismatches(expected, actual):
    return sorted(name for name in expected.keys() | actual.keys()
                  if name not in actual or name not in expected
                  or expected[name] != digest(actual[name]))


class PublicRevisionTests(unittest.TestCase):
    def test_provider_modules_retain_their_declared_source_bytes(self):
        manifests = sorted((ROOT / 'packages').rglob('sigil-package.json'))
        self.assertEqual(len(manifests), 16)
        for manifest in manifests:
            with self.subTest(package=manifest.parent):
                value = json.loads(manifest.read_bytes())
                provenance = json.loads((manifest.parent / 'source-provenance.json').read_bytes())
                actual = {f'src/{name}.sigil': (manifest.parent / f'src/{name}.sigil').read_bytes()
                          for name in value['modules']}
                self.assertEqual(mismatches(provenance['module_sha256'], actual), [])
                self.assertNotEqual(value['version'], provenance['previous_version'])
                changed = dict(actual)
                name = next(iter(changed))
                changed[name] += b'\n'
                self.assertEqual(mismatches(provenance['module_sha256'], changed), [name])
                del changed[name]
                self.assertEqual(mismatches(provenance['module_sha256'], changed), [name])
                changed = {**actual, 'extra.sigil': b'extra'}
                self.assertEqual(mismatches(provenance['module_sha256'], changed), ['extra.sigil'])

    def test_manifest_and_inventory_bind_the_public_documents(self):
        manifests = sorted((ROOT / 'packages').rglob('sigil-package.json'))
        manifests += sorted((ROOT / 'programs').glob('*/sigil-package.json'))
        self.assertEqual(len(manifests), 27)
        for manifest in manifests:
            with self.subTest(package=manifest.parent):
                value = json.loads(manifest.read_bytes())
                root = manifest.parent
                inventory = 'inputs.json' if (root / 'inputs.json').is_file() else 'tool-inputs.json'
                for field, name in (('api_card_hash', 'api-card.json'), ('api_contract_hash', 'API.md'),
                                    ('charter_hash', 'README.md'), ('evidence_manifest_hash', inventory)):
                    self.assertEqual(value['evidence'][field], digest((root / name).read_bytes()))
                expected = json.loads((root / inventory).read_bytes())['files']
                actual = {name: (root / name).read_bytes() for name in expected}
                self.assertEqual(mismatches(expected, actual), [])
                self.assertEqual(json.loads((root / 'api-card.json').read_bytes())['contract_hash'],
                                 digest((root / 'API.md').read_bytes()))


if __name__ == '__main__':
    unittest.main()
