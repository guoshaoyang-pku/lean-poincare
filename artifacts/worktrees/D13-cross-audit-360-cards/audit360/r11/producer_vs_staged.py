#!/usr/bin/env python3
"""Round-11 provenance check: is every audited source copy still byte-identical
to the *current* producer release tree?

The 360 dispatcher promoted seven D12 cards at 16:45-16:49 on 2026-09-11, after
the round-8 card freeze.  Cards were re-frozen in round 11 (unchanged), but a
card file is not a source tree: this script diffs every file of each producer
`release/` against the staged copy that rounds 1-11 actually built and probed.
Only audit-generated files (A3*.lean, A3Meta.json, A3Extra* dirs) may exist on
the staged side; any producer-side `Only in` or `Files ... differ` line fails.

Output: audit360/r11/producer_vs_staged_round11.json
"""
import datetime
import hashlib
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
PROD = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
STAGE = os.path.join(WT, "audit360", "pkgs")
OUT = os.path.join(HERE, "producer_vs_staged_round11.json")
CARDS = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]
EXCL = ["--exclude=.lake", "--exclude=.git", "--exclude=A3Extra", "--exclude=A3ExtraR3",
        "--exclude=A3ExtraR5", "--exclude=A3ExtraR6", "--exclude=A3ExtraR7",
        "--exclude=A3ExtraR8", "--exclude=A3ExtraR11", "--exclude=A3AllTypes.lean",
        "--exclude=A3FullAudit.lean", "--exclude=A3KindAudit.lean", "--exclude=A3Meta.json",
        "--exclude=A3Probe.lean", "--exclude=A3TautFull.lean", "--exclude=A3TautScreen.lean",
        "--exclude=A3UnusedHypFull.lean", "--exclude=A3UnusedHyp.lean"]


def main():
    out = {"schema": "a3-r11-producer-vs-staged-v1",
           "checked_at": datetime.datetime.now().isoformat(timespec="seconds"),
           "method": "diff -rq of producer release/ against the staged audit copy, "
                     "audit-generated files excluded from the staged side only",
           "cards": {}}
    bad = []
    for card in CARDS:
        prod = os.path.join(PROD, card, "release")
        stage = os.path.join(STAGE, card)
        p = subprocess.run(["diff", "-rq", *EXCL, prod, stage],
                           capture_output=True, text=True)
        lines = [l for l in p.stdout.splitlines() if l.strip()]
        producer_side = [l for l in lines
                         if l.startswith("Files ") or l.startswith(f"Only in {prod}")]
        # belt and braces: any line mentioning the producer path at all
        producer_side += [l for l in lines if l.startswith("Only in ") and prod in l
                          and l not in producer_side]
        # count producer source files and hash the sorted (path, sha256) list
        files = []
        for root, dirs, names in os.walk(prod):
            dirs[:] = [d for d in dirs if d not in (".lake", ".git", "A3Extra",
                                                    "A3ExtraR3", "A3ExtraR5",
                                                    "A3ExtraR6", "A3ExtraR7",
                                                    "A3ExtraR8", "A3ExtraR11")]
            for n in sorted(names):
                if n.startswith("A3") and (n.endswith(".lean") or n == "A3Meta.json"):
                    continue
                fp = os.path.join(root, n)
                rel = os.path.relpath(fp, prod)
                h = hashlib.sha256(open(fp, "rb").read()).hexdigest()
                files.append((rel, h))
        files.sort()
        digest = hashlib.sha256(
            "".join(f"{r}\0{h}\n" for r, h in files).encode()).hexdigest()
        out["cards"][card] = {
            "producer_files": len(files),
            "tree_sha256": digest,
            "producer_side_differences": producer_side,
            "staged_only_audit_files": len([l for l in lines
                                            if l.startswith(f"Only in {stage}")]),
            "identical": not producer_side,
        }
        if producer_side:
            bad.append(card)
    out["all_identical"] = not bad
    out["failed_cards"] = bad
    json.dump(out, open(OUT, "w", encoding="utf-8"), indent=1, sort_keys=True)
    print(json.dumps({c: {"identical": v["identical"], "files": v["producer_files"],
                          "tree_sha256": v["tree_sha256"][:16]}
                      for c, v in out["cards"].items()}, indent=1))
    print("ALL IDENTICAL:", out["all_identical"])
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
