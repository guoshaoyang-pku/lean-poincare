"""Acceptance and fail-closed cases for the standalone P5 gate."""
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('release-hash-gate.py')
SPEC = importlib.util.spec_from_file_location('p5', SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class HashGateTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.base = Path(self.scratch.name)
        self.root = self.base / 'release'
        self.root.mkdir()
        self.source = self.root / 'source.txt'
        self.source.write_text('original bytes')
        self.manifest = self.base / 'baseline.sha256'
        digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        self.entry = digest + '  ./source.txt\n'
        self.manifest.write_text(self.entry)

    def check_gate(self, code, **kwargs):
        report, actual = GATE.check(self.manifest, self.root, **kwargs)
        self.assertEqual(actual, code, report)
        return report

    def test_unchanged_and_build_cache(self):
        (self.root / '.lake').mkdir()
        (self.root / '.lake' / 'build').write_text('not release source')
        report = self.check_gate(0)
        self.assertEqual(report['matched'], 1)
        self.assertEqual(report['added'], [])

    def test_changed_is_named(self):
        self.source.write_text('changed bytes')
        report = self.check_gate(1)
        self.assertEqual([x['path'] for x in report['changed']], ['source.txt'])

    def test_removed_is_named(self):
        self.source.rename(self.base / 'removed-source.txt')
        self.assertEqual(self.check_gate(1)['removed'], ['source.txt'])

    def test_added_is_reported_and_strict_mode_rejects(self):
        (self.root / 'addition.txt').write_text('new bytes')
        self.assertEqual(self.check_gate(0)['added'], ['addition.txt'])
        self.check_gate(1, fail_on_added=True)

    def test_malformed_empty_duplicate_and_unsafe_manifests(self):
        bad = ['', self.entry + 'malformed\n', self.entry * 2,
               self.entry.replace('./source.txt', '../source.txt'),
               self.entry.replace('./source.txt', '/source.txt'),
               self.entry.replace('./source.txt', '.lake/source.txt')]
        for text in bad:
            with self.subTest(text=text):
                self.manifest.write_text(text)
                self.assertTrue(self.check_gate(2)['errors'])

    def test_missing_manifest_or_root(self):
        self.manifest.rename(self.base / 'preserved.sha256')
        self.check_gate(2)
        self.manifest.write_text(self.entry)
        self.root = self.base / 'missing'
        self.check_gate(2)

    def test_symlink_is_not_silently_skipped(self):
        target = self.base / 'target'
        self.source.rename(target)
        self.source.symlink_to(target)
        self.check_gate(2)

    def test_authenticated_manifest(self):
        good = hashlib.sha256(self.manifest.read_bytes()).hexdigest()
        self.check_gate(0, expected_manifest_sha256=good)
        self.check_gate(2, expected_manifest_sha256='0' * 64)

    def test_cli_exit_matches_json_verdict(self):
        self.source.write_text('intentional CLI negative control')
        result = subprocess.run([sys.executable, str(SCRIPT), str(self.manifest),
                                 str(self.root)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn('"verdict": "FAIL"', result.stdout)


if __name__ == '__main__':
    unittest.main()
