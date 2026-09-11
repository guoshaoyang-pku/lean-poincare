#!/usr/bin/env python3
"""Compare a release to a previous sha256sum manifest (P5, read-only).

Exit 0: all original bytes match; 1: changed/removed/forbidden additions;
2: invalid input, unsupported filesystem entry, or IO failure.
Added files are reported, never accepted as proved or compiled.
The caller must authenticate the prior manifest and quiesce source writers.
Build caches (.lake) and Git metadata (.git) are outside this source gate.
Adapted from L1-lean-baseline/baseline/tools/p5_hash_gate.py's comparison policy;
this standalone entry point validates arbitrary supplied manifests strictly.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

EXCLUDED = {'.lake', '.git'}


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def read_manifest(path):
    raw = path.read_bytes()
    files = {}
    for number, line in enumerate(raw.decode('utf-8').splitlines(), 1):
        if not line.strip():
            continue
        match = re.fullmatch(r'([0-9a-fA-F]{64}) [ *](.+)', line)
        if not match:
            raise ValueError(f'malformed sha256sum record at line {number}')
        digest, name = match.groups()
        if name.startswith('./'):
            name = name[2:]
        parts = name.split('/')
        if (any(p in ('', '.', '..') or p in EXCLUDED for p in parts)
                or PurePosixPath(name).is_absolute() or '\\' in name
                or any(ord(c) < 32 for c in name)):
            raise ValueError(f'unsafe or excluded path at line {number}')
        if name in files:
            raise ValueError(f'duplicate path at line {number}: {name}')
        files[name] = digest.lower()
    if not files:
        raise ValueError('empty hash manifest')
    return files, hashlib.sha256(raw).hexdigest()


def tree_hashes(root):
    if not root.is_dir():
        raise ValueError('release root is not a directory')
    files = {}

    def fail(error):
        raise error

    for directory, dirs, names in os.walk(root, followlinks=False, onerror=fail):
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED)
        for name in dirs + names:
            path = Path(directory) / name
            mode = path.lstat().st_mode
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise ValueError('unsupported source entry: ' + path.relative_to(root).as_posix())
        for name in sorted(names):
            path = Path(directory) / name
            files[path.relative_to(root).as_posix()] = sha256(path)
    return files


def check(manifest, root, fail_on_added=False, expected_manifest_sha256=None):
    report = {'gate': 'P5-source-hash', 'schema': 1, 'verdict': 'ERROR',
              'manifest': str(manifest), 'release_root': str(root),
              'excluded_directories': sorted(EXCLUDED),
              'fail_on_added': fail_on_added, 'added': [], 'changed': [],
              'removed': [], 'errors': [], 'scope': 'source identity only; not compilation, axiom audit or semantic acceptance'}
    try:
        previous, manifest_hash = read_manifest(manifest)
        report['manifest_sha256'] = manifest_hash
        if expected_manifest_sha256 is not None:
            if not re.fullmatch(r'[0-9a-fA-F]{64}', expected_manifest_sha256):
                raise ValueError('expected manifest SHA256 must have 64 hex digits')
            if manifest_hash != expected_manifest_sha256.lower():
                raise ValueError('manifest SHA256 differs from authenticated reference')
        current = tree_hashes(root)
        report.update(recorded=len(previous), current_files=len(current),
                      matched=sum(current.get(p) == h for p, h in previous.items()),
                      added=sorted(current.keys() - previous.keys()),
                      removed=sorted(previous.keys() - current.keys()),
                      changed=[{'path': p, 'expected': previous[p], 'actual': current[p]}
                               for p in sorted(previous.keys() & current.keys())
                               if current[p] != previous[p]])
        if tree_hashes(root) != current or sha256(manifest) != manifest_hash:
            raise ValueError('source tree or manifest changed during the check')
        failed = bool(report['changed'] or report['removed'] or (fail_on_added and report['added']))
        report['verdict'] = 'FAIL' if failed else 'PASS'
        return report, int(failed)
    except (OSError, ValueError) as error:
        report['errors'].append(str(error))
        return report, 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('release_root', type=Path)
    parser.add_argument('--fail-on-added', action='store_true')
    parser.add_argument('--expected-manifest-sha256')
    args = parser.parse_args()
    report, code = check(args.manifest, args.release_root, args.fail_on_added, args.expected_manifest_sha256)
    print(json.dumps(report, indent=2, sort_keys=True))
    return code


if __name__ == '__main__':
    sys.exit(main())
