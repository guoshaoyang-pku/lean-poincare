#!/usr/bin/env python3
"""Analyse the kernel declaration-kind audit (A3KindAudit.lean) and cross-reference
it with the card schemas.

Adversarial question answered here: of everything a card lists under
`proved_declarations` (or, for dict schemas, in *all* of its groups), how much is
actually a kernel proof of a proposition, and how much is a definition, a
structure, a type synonym or an explicitly statement-only Prop former?

Writes `kind_screen.json` next to this script and prints a summary.
"""
import glob
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))  # worktrees root (siblings of this task worktree)
CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]


def parse_kind_logs():
    per_card = {}
    for card in CARDS:
        path = os.path.join(HERE, "logs-kind", card + ".kind.log")
        rows = []
        summary = None
        for line in open(path):
            m = re.match(r"A3KIND\t([^\t]+)\t([^\t]+)\t(.+)$", line.strip())
            if m:
                rows.append({"name": m.group(1), "kind": m.group(2), "result": m.group(3)})
            m2 = re.match(r"A3KIND-SUMMARY\t(.+)$", line.strip())
            if m2:
                summary = m2.group(1)
        per_card[card] = {"rows": rows, "summary": summary}
    return per_card


def card_groups(card):
    """Return {group_name: [declared strings]} for the card JSON, or None."""
    p = os.path.join(WT, card, "longrun", "results", card + ".json")
    d = json.load(open(p))
    pd = d.get("proved_declarations")
    if isinstance(pd, dict):
        return {k: v for k, v in pd.items() if isinstance(v, list)}
    return None


def main():
    per_card = parse_kind_logs()
    out = {"schema": "d13-a3-kind-screen-v1", "method": "Lean.Meta ConstantInfo variant + result sort",
           "cards": {}, "totals": {}}
    tot = {}
    for card in CARDS:
        rows = per_card[card]["rows"]
        groups = card_groups(card)
        counts = {}
        for r in rows:
            key = r["kind"] + ":" + r["result"]
            counts[key] = counts.get(key, 0) + 1
            tot[key] = tot.get(key, 0) + 1
        distinct = len({r["name"] for r in rows})
        dups = len(rows) - distinct
        non_proof = [r for r in rows if not (r["kind"] == "theorem" or r["result"] == "PropResult")]
        out["cards"][card] = {
            "probe_rows": len(rows),
            "distinct_names": distinct,
            "duplicate_rows": dups,
            "kind_counts": counts,
            "non_proof_entries": non_proof,
            "card_schema": "dict:" + ",".join(groups.keys()) if groups else "flat list",
            "statement_only_groups": ([k for k in groups if "statement" in k] if groups else []),
        }
    out["totals"] = tot
    with open(os.path.join(HERE, "kind_screen.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(tot, indent=1))
    for card in CARDS:
        c = out["cards"][card]
        print(f"{card}: rows={c['probe_rows']} distinct={c['distinct_names']} dups={c['duplicate_rows']} "
              f"schema={c['card_schema']}")
    print("non-proof entries:")
    for card in CARDS:
        for r in out["cards"][card]["non_proof_entries"]:
            if r["result"] in ("PropFormer", "PropResult"):
                print("  ", card, r)


if __name__ == "__main__":
    main()
