#!/usr/bin/env python3
"""Round-7 surrogate/base audit for the two source-absent D12 cards.

`D12-tensor-maximum-bochner` (360-1) and `D12-triangulation-topology` (360-2)
have no artifacts anywhere on this host (re-verified in every round).  This
script does NOT audit them and cannot substitute for them.  What it does is:

  * record the D12-plan objective and canonical blocker ids for each missing card;
  * locate the local *precursor* cards/worktrees the D12 cards were meant to build
    on (D11/D10/D9/D8/D7 tasks);
  * independently recompute every source sha256 those precursor cards record, so
    the surrogate base is at least byte-verified rather than quoted;
  * extract each precursor's proved-vs-statement-only split.

Everything produced here is labelled `surrogate_for_missing_card` and must never
be counted as re-verification of a 360-produced card.  Output:
`audit360/proxy_base_round7.json`.
"""
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
PLAN = "/data3/guoshaoyang/workdir/lean_poincare/longrun/D12-plan.json"

MISSING = {
    "D12-tensor-maximum-bochner": [
        "D11-maximum-principle-tensor", "D11-bochner-manifold",
        "D10-maximum-principle-rn", "D10-bochner-euclidean",
        "D7-bochner-formula", "D7-tensor-laplacian", "D9-tensor-algebra-manifolds",
        "D7-riemann-curvature-tensor",
    ],
    "D12-triangulation-topology": [
        "D10-triangulation-low-dim", "D8-moise-statement-bridge",
        "D7-sphere-recognition", "D7-gh-compactness",
    ],
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def plan_entry(task_id):
    plan = json.load(open(PLAN))
    for t in plan["tasks"]:
        if t["id"] == task_id:
            return t
    return None


def collect_hash_entries(obj, acc):
    """Recursively collect every {path, sha256} pair from any card schema."""
    if isinstance(obj, dict):
        if isinstance(obj.get("path"), str) and isinstance(obj.get("sha256"), str):
            acc.append((obj["path"], obj["sha256"]))
        for v in obj.values():
            collect_hash_entries(v, acc)
    elif isinstance(obj, list):
        for v in obj:
            collect_hash_entries(v, acc)


def resolve(wt, p):
    cands = [os.path.join(wt, p)]
    if p.startswith("release/"):
        cands.append(os.path.join(wt, p[len("release/"):]))
    else:
        cands.append(os.path.join(wt, "release", p))
    for c in cands:
        if os.path.exists(c):
            return c
    return None


def verify_files(wt, entries):
    """entries: list of (path, sha256) from any card schema."""
    checked, mismatched, missing = 0, [], []
    for p, s in entries:
        full = resolve(wt, p)
        if full is None:
            missing.append(p)
            continue
        checked += 1
        if sha256(full) != s:
            mismatched.append(p)
    return {"checked": checked, "mismatched": mismatched, "missing": missing}


def summarize(task_id):
    wt = os.path.join(WT, task_id)
    rec = {"task_id": task_id, "worktree": wt, "worktree_exists": os.path.isdir(wt)}
    card_path = os.path.join(wt, "longrun", "results", task_id + ".json")
    rec["card"] = card_path
    rec["card_exists"] = os.path.exists(card_path)
    if not rec["card_exists"]:
        return rec
    d = json.load(open(card_path))
    rec["verdict"] = d.get("verdict") or d.get("status")
    rec["summary_head"] = (d.get("summary") or d.get("headline") or "")[:300]
    files = d.get("files") or d.get("deliverables") or []
    if isinstance(files, dict):
        files = []
    entries = []
    collect_hash_entries(d, entries)
    # de-duplicate, keeping first occurrence
    seen, uniq = set(), []
    for p, s in entries:
        if (p, s) not in seen:
            seen.add((p, s))
            uniq.append((p, s))
    rec["hashes_recorded"] = len(uniq)
    rec["hash_verification"] = verify_files(wt, uniq)
    rec["statement_only"] = [
        {"name": s.get("name"), "status": s.get("status")}
        for s in (d.get("statement_only_targets") or d.get("statement_only") or [])
        if isinstance(s, dict)
    ][:20]
    rec["axiom_audit_selfreport"] = (json.dumps(d.get("axiom_audit"))[:300]
                                     if d.get("axiom_audit") else None)
    # lean file inventory of the shipped module dir, if identifiable
    dirs = []
    for p, _s in uniq:
        if p.endswith(".lean"):
            dirs.append(os.path.dirname(p))
    for f in (files if isinstance(files, list) else []):
        p = f.get("path", "")
        if p.endswith(".lean"):
            dirs.append(os.path.dirname(p))
    dirs = sorted(set(dirs))
    rec["lean_dirs"] = dirs
    rec["lean_files_on_disk"] = sum(
        1 for dd in dirs for _ in
        (os.listdir(os.path.join(wt, dd)) if os.path.isdir(os.path.join(wt, dd)) else [])
        if _.endswith(".lean")) if dirs else 0
    return rec


def main():
    out = {
        "schema": "d13-proxy-base-v1",
        "NOT_A_SUBSTITUTE": (
            "Surrogate/base evidence only. These precursor cards are NOT the "
            "360-produced D12 cards, which remain source-absent and unaudited; "
            "no entry here may be counted toward the 9-card milestone."),
        "missing_cards": {},
    }
    for task_id, precursors in MISSING.items():
        out["missing_cards"][task_id] = {
            "plan": plan_entry(task_id),
            "precursors": [summarize(p) for p in precursors],
        }
    with open(os.path.join(HERE, "proxy_base_round7.json"), "w") as f:
        json.dump(out, f, indent=1)
    for task_id, e in out["missing_cards"].items():
        print("==", task_id, "| blockers", e["plan"].get("blockers"))
        for p in e["precursors"]:
            hv = p.get("hash_verification", {})
            print(f"   {p['task_id']:34s} card={p['card_exists']} "
                  f"hashes={hv.get('checked', 0)} mismatch={len(hv.get('mismatched', []))} "
                  f"missing={len(hv.get('missing', []))} stmt_only={len(p.get('statement_only', []))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
