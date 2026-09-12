#!/usr/bin/env python3
"""INDEPENDENT spot-check generator (verifier lane).

Samples every 40th data row of baseline/audit/declarations.tsv (deterministic),
determines which audit partition (G1 or G2, whose target-module sets are disjoint)
declares each sampled name from MY OWN audit logs, and writes two Lean drivers that
run `#print axioms <name>` inside the corresponding partition's import environment.
"""
import argparse
import json
import os
import re


def import_lines(driver):
    out = []
    for line in open(driver, encoding="utf-8"):
        if line.startswith("import "):
            out.append(line.rstrip("\n"))
        elif out:
            break
    return out


def raw_names(log):
    names = set()
    for line in open(log, encoding="utf-8", errors="replace"):
        if line.startswith("L1AXROW\t"):
            names.add(line.split("\t")[1])
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv", required=True)
    ap.add_argument("--mine-g1-log", required=True)
    ap.add_argument("--mine-g2-log", required=True)
    ap.add_argument("--frozen-g1-driver", required=True)
    ap.add_argument("--frozen-g2-driver", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--every", type=int, default=40)
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("--prefix", default="SpotCheck")
    a = ap.parse_args()

    rows = []
    with open(a.tsv, encoding="utf-8") as fh:
        hdr = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            f = line.rstrip("\n").split("\t")
            if len(f) == len(hdr):
                rows.append(dict(zip(hdr, f)))
    sample = [rows[i] for i in range(a.offset, len(rows), a.every)]
    g1_names = raw_names(a.mine_g1_log)
    g2_names = raw_names(a.mine_g2_log)

    g1_sample, g2_sample, unresolved = [], [], []
    for r in sample:
        n = r["name"]
        if n in g2_names:
            g2_sample.append(r)
        elif n in g1_names:
            g1_sample.append(r)
        else:
            unresolved.append(n)

    def write_driver(path, imports, sample_rows):
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("/- INDEPENDENT spot-check driver (verifier lane) -/\n")
            for imp in imports:
                fh.write(imp + "\n")
            fh.write("\n")
            for r in sample_rows:
                fh.write("#print axioms %s\n" % r["name"])

    write_driver(os.path.join(a.outdir, a.prefix + "_G1.lean"),
                 import_lines(a.frozen_g1_driver), g1_sample)
    write_driver(os.path.join(a.outdir, a.prefix + "_G2.lean"),
                 import_lines(a.frozen_g2_driver), g2_sample)

    meta = {
        "tsv_rows": len(rows),
        "every": a.every,
        "offset": a.offset,
        "sample_size": len(sample),
        "g1_sample": len(g1_sample),
        "g2_sample": len(g2_sample),
        "unresolved": unresolved,
        "sample": [
            {"name": r["name"], "kind": r["kind"], "module": r["module"],
             "cone_tsv": r["axioms"], "partition": ("G2" if r["name"] in g2_names else "G1")}
            for r in sample
        ],
    }
    with open(os.path.join(a.outdir, a.prefix.lower() + "-sample.json"), "w", encoding="utf-8") as fh:
        json.dump(meta, fh, indent=1)
    print(json.dumps({k: meta[k] for k in
                      ["tsv_rows", "every", "offset", "sample_size", "g1_sample", "g2_sample",
                       "unresolved"]}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
