#!/usr/bin/env python3
"""Independent source-hash replay for one ophis-gpu D13 card.

Recomputes sha256 of every file under <task>/release (excluding .lake) and, when the
card ships a recorded hash manifest, compares recorded vs recomputed.  Writes
audit/evidence/<task>/release-hashes.txt and hash-replay.json.
"""
import hashlib
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent          # audit/
OPHIS = ROOT / "ophis"
EVID = ROOT / "evidence"


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def collect(release: Path):
    out = {}
    for p in sorted(release.rglob("*")):
        if p.is_file() and ".lake" not in p.parts:
            out[str(p.relative_to(release))] = sha256(p)
    return out


def parse_recorded(path: Path):
    """Parse `<sha256>  <path>` lines (path relative to release, ./ prefix ok)."""
    rec = {}
    for line in path.read_text().splitlines():
        m = re.match(r"^([0-9a-f]{64})[ \t]+(.+)$", line.strip())
        if not m:
            continue
        digest, name = m.group(1), m.group(2).strip()
        name = name[2:] if name.startswith("./") else name
        rec[name] = digest
    return rec


def main(task: str):
    rel = OPHIS / task / "release"
    if not rel.is_dir():
        print(f"NO_RELEASE {task}")
        return 2
    recomputed = collect(rel)
    rec_files = []
    for cand in ["audit-evidence/final-release-hashes.txt",
                 "audit-evidence/base-release-hashes-preintegration.txt",
                 "manifest/source-hashes.txt", "manifest/input-hashes.json",
                 "manifest/verification.json"]:
        p = OPHIS / task / cand
        if p.is_file():
            rec_files.append(str(p.relative_to(OPHIS / task)))
    recorded = {}
    recorded_src = None
    for cand in ["audit-evidence/final-release-hashes.txt",
                 "audit-evidence/base-release-hashes-preintegration.txt"]:
        p = OPHIS / task / cand
        if p.is_file():
            parsed = parse_recorded(p)
            if parsed:
                recorded = parsed
                recorded_src = cand
                break
    res = {
        "task": task,
        "recomputed_files": len(recomputed),
        "recomputed_total_sha256": hashlib.sha256(
            "".join(f"{k}:{v}\n" for k, v in sorted(recomputed.items())).encode()
        ).hexdigest(),
        "recorded_manifest": recorded_src,
        "recorded_files": len(recorded) if recorded else 0,
        "missing_in_recorded": [],
        "missing_in_recomputed": [],
        "mismatches": [],
        "hash_manifest_candidates": rec_files,
        "verdict": "NO_RECORDED_MANIFEST",
    }
    if recorded:
        for k, v in sorted(recomputed.items()):
            if k not in recorded:
                res["missing_in_recorded"].append(k)
            elif recorded[k] != v:
                res["mismatches"].append({"path": k, "recorded": recorded[k], "recomputed": v})
        for k in sorted(recorded):
            if k not in recomputed:
                res["missing_in_recomputed"].append(k)
                # hash-file paths sometimes have leading ./ or a release/ prefix
                alt = "release/" + k
                if alt in recomputed:
                    res["missing_in_recomputed"].pop()
                    if recorded[k] != recomputed[alt]:
                        res["mismatches"].append({"path": alt, "recorded": recorded[k],
                                                  "recomputed": recomputed[alt]})
        res["verdict"] = ("MATCH" if not res["mismatches"] and not res["missing_in_recomputed"]
                          else "MISMATCH")
    outdir = EVID / task
    outdir.mkdir(parents=True, exist_ok=True)
    with open(outdir / "release-hashes.txt", "w") as f:
        for k, v in sorted(recomputed.items()):
            f.write(f"{v}  ./{k}\n")
    (outdir / "hash-replay.json").write_text(json.dumps(res, indent=2) + "\n")
    print(f"{task}: files={len(recomputed)} recorded={res['recorded_files']} "
          f"verdict={res['verdict']} mismatches={len(res['mismatches'])} "
          f"missing={len(res['missing_in_recomputed'])} extra={len(res['missing_in_recorded'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
