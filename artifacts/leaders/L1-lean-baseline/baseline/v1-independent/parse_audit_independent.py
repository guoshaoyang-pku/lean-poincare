#!/usr/bin/env python3
"""INDEPENDENT parser for L1 axiom-audit logs (written from scratch for the verifier lane).

Parses `L1AXROW\t<name>\t<kind>\t<module>\t<axioms,comma-sep>\t<extra,comma-sep>\t<internal>`
lines emitted by the frozen drivers and compares against either
  (a) the frozen raw logs (per-partition, position-wise), and/or
  (b) baseline/audit/declarations.tsv (merged, row-by-row on name/kind/module/axioms).

No code is shared with baseline/tools/parse_axiom_audit.py.
"""
import argparse
import csv
import json
import sys


def parse_rows(path, partition):
    rows = []
    bad = []
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for lineno, line in enumerate(fh, 1):
            if not line.startswith("L1AXROW\t"):
                continue
            line = line.rstrip("\n").rstrip("\r")
            f = line.split("\t")
            if len(f) != 7:
                bad.append({"lineno": lineno, "nfields": len(f), "line": line[:200]})
                continue
            rows.append(
                {
                    "name": f[1],
                    "kind": f[2],
                    "module": f[3],
                    "cone": f[4],  # comma-separated axioms, as printed
                    "extra": f[5],
                    "internal": f[6],
                    "partition": partition,
                }
            )
    return rows, bad


def cone_tsv(cone_comma):
    """Frozen TSV stores the cone as ';'-separated."""
    if cone_comma == "":
        return ""
    return ";".join(cone_comma.split(","))


def key4(r):
    return (r["name"], r["kind"], r["module"], r["cone"])


def compare_lists(mine, frozen, label, limit=20):
    mism = []
    n = max(len(mine), len(frozen))
    for i in range(n):
        a = mine[i] if i < len(mine) else None
        b = frozen[i] if i < len(frozen) else None
        if a is None or b is None or key4(a) != key4(b):
            mism.append({"index": i, "mine": a, "frozen": b})
    return {
        "label": label,
        "mine_rows": len(mine),
        "frozen_rows": len(frozen),
        "compared": min(len(mine), len(frozen)),
        "mismatches": len(mism),
        "first_mismatches": mism[:limit],
    }


def merge_g2_precedence(rows_g1, rows_g2):
    """Union by name; G2 row wins on a name collision (rule empirically observed
    in the frozen pipeline; documented in the independent report)."""
    out = {}
    for r in rows_g1:
        out[r["name"]] = r
    for r in rows_g2:
        out[r["name"]] = r
    return [out[k] for k in sorted(out)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mine-g1", required=True)
    ap.add_argument("--mine-g2", required=True)
    ap.add_argument("--frozen-g1", default=None)
    ap.add_argument("--frozen-g2", default=None)
    ap.add_argument("--tsv", default=None)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()

    my_g1, bad1 = parse_rows(a.mine_g1, "G1")
    my_g2, bad2 = parse_rows(a.mine_g2, "G2")
    result = {
        "mine": {"G1_rows": len(my_g1), "G2_rows": len(my_g2),
                 "malformed": bad1 + bad2},
        "raw_partition_comparison": [],
        "tsv_comparison": None,
    }

    if a.frozen_g1 and a.frozen_g2:
        fr_g1, fbad1 = parse_rows(a.frozen_g1, "G1")
        fr_g2, fbad2 = parse_rows(a.frozen_g2, "G2")
        result["frozen"] = {"G1_rows": len(fr_g1), "G2_rows": len(fr_g2),
                            "malformed": fbad1 + fbad2}
        result["raw_partition_comparison"].append(
            compare_lists(my_g1, fr_g1, "G1: independent vs frozen raw log", 20))
        result["raw_partition_comparison"].append(
            compare_lists(my_g2, fr_g2, "G2: independent vs frozen raw log", 20))

    if a.tsv:
        merged = merge_g2_precedence(my_g1, my_g2)
        tsv = {}
        with open(a.tsv, "r", encoding="utf-8") as fh:
            rd = csv.reader(fh, delimiter="\t")
            hdr = next(rd)
            for row in rd:
                if len(row) != len(hdr):
                    continue
                tsv[row[0]] = dict(zip(hdr, row))
        # sanity: every raw name present in tsv
        raw_names = {r["name"] for r in my_g1} | {r["name"] for r in my_g2}
        missing = sorted(raw_names - set(tsv))
        extra_tsv = sorted(set(tsv) - raw_names)
        mism = []
        cmp_rows = []
        for r in merged:
            t = tsv.get(r["name"])
            if t is None:
                mism.append({"name": r["name"], "reason": "not in tsv", "mine": r})
                continue
            mine4 = (r["name"], r["kind"], r["module"], cone_tsv(r["cone"]))
            tsv4 = (t["name"], t["kind"], t["module"], t["axioms"])
            cmp_rows.append((mine4, tsv4))
            if mine4 != tsv4:
                mism.append({"reason": "field mismatch", "mine": r,
                             "frozen_tsv": {k: t[k] for k in hdr}})
        result["tsv_comparison"] = {
            "label": "merged (G2 precedence) vs baseline/audit/declarations.tsv",
            "mine_merged_rows": len(merged),
            "tsv_rows": len(tsv),
            "compared": len(cmp_rows),
            "mismatches": len(mism),
            "raw_names_missing_from_tsv": missing[:20],
            "tsv_names_not_in_raw": extra_tsv[:20],
            "first_mismatches": mism[:20],
        }
    with open(a.out, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({k: v for k, v in result.items()}, indent=1)[:4000])
    return 0


if __name__ == "__main__":
    sys.exit(main())
