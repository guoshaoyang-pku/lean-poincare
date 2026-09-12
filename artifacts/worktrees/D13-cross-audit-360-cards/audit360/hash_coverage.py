#!/usr/bin/env python3
"""Provenance-coverage check: does each card's recorded `source_hashes` set cover every
D12-authored source file that is actually present in its release package?

The existing provenance check verifies that every *recorded* hash matches the bytes on
disk.  This is the converse question: are there bytes on disk that the card never
recorded?  A file under `release/Poincare/D12*` (or `release/Audit/D12*`) that appears in
no recorded key would mean the card's provenance claim is incomplete.

Writes `hash_coverage_round5.json` next to this script.
"""
import glob
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
TREES = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]


def recorded_keys(card):
    """Return (relpaths, basenames) of recorded hashes, normalised to release/-relative."""
    d = json.load(open(os.path.join(TREES, card, "longrun", "results", card + ".json")))
    sh = d.get("source_hashes", {})
    rel, names = set(), set()
    if card == "D12-volume-ibp":
        for k in sh:
            rel.add("Poincare/D12/VolumeIBP/" + k)
            rel.add(k)
            names.add(k)
    elif card == "D12-spectral-sobolev":
        for k in sh.get("sha256", {}):
            rel.add(k[len("release/"):] if k.startswith("release/") else k)
            names.add(os.path.basename(k))
    elif card == "D12-semantic-ledger":
        for group in ("package_lean_files", "d12_authored"):
            for k in sh.get(group, {}):
                rel.add(k)
                names.add(os.path.basename(k))
    else:
        for k in sh:
            if not isinstance(sh[k], str):
                continue
            rel.add(k[len("release/"):] if k.startswith("release/") else k)
            names.add(os.path.basename(k))
    return rel, names


def main():
    report = {"schema": "d13-hash-coverage-v1", "cards": {}}
    for card in CARDS:
        rel, names = recorded_keys(card)
        release = os.path.join(TREES, card, "release")
        uncovered, covered = [], 0
        for p in glob.glob(os.path.join(release, "**", "*.lean"), recursive=True):
            r = os.path.relpath(p, release)
            base = os.path.basename(p)
            # D12-authored files only: path mentions D12, or the file is a D12-named barrel
            if "D12" not in r:
                continue
            if r in rel or base in names:
                covered += 1
            else:
                uncovered.append(r)
        report["cards"][card] = {
            "d12_lean_files_on_disk": covered + len(uncovered),
            "covered": covered,
            "uncovered": sorted(uncovered),
        }
    with open(os.path.join(HERE, "hash_coverage_round5.json"), "w") as f:
        json.dump(report, f, indent=1)
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
