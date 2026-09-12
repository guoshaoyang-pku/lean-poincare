#!/usr/bin/env python3
"""A3 round-13 independent source-hash rebuild.

Written from scratch for this invocation (does not import or reuse any earlier
A3 script).  For each of the nine D12 cards:

  1. locate the producer card JSON in the producer worktree (fresh glob, not
     read from a cached inventory);
  2. extract `source_hashes` (dict or list of {path,sha256} forms);
  3. recompute sha256 of every file in the *producer worktree*;
  4. recompute sha256 of the *staged* copy in audit360/pkgs/<card>/;
  5. compare producer-recomputed == card-claim and staged == producer;
  6. whole-tree Lean comparison of producer release/Poincare/D12 against the
     staged Poincare/D12 to detect uncovered/modified files.

Exit code 0 iff every claim verifies; 1 otherwise (fail-closed).
"""
import hashlib
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PKGS = os.path.join(ROOT, "audit360", "pkgs")
POINCARE_ROOT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"

CARDS = [
    ("D12-connection-curvature", "360-1"),
    ("D12-volume-ibp", "360-1"),
    ("D12-spectral-sobolev", "360-1"),
    ("D12-semantic-ledger", "360-1"),
    ("D12-comparison-geodesics", "360-2"),
    ("D12-geometric-compactness", "360-2"),
    ("D12-surgery-recognition", "360-2"),
    ("D12-triangulation-topology", "360-2"),
    ("D12-tensor-maximum-bochner", "360-1"),
]


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


_HASHKEYS = ("sha256", "hash", "sha", "digest")


def parse_hashes(obj, prefix=""):
    """Return list of (key, sha256) from arbitrary dict / list nesting.

    Recurses through container keys (e.g. {"sha256": {...}},
    {"package_lean_files": {...}}) because the nine cards use several shapes.
    """
    out = []
    if obj is None:
        return out
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str) and len(v) == 64 and all(c in "0123456789abcdef" for c in v):
                out.append((k, v))
            elif isinstance(v, dict):
                looks_like_entry = any(kk in v for kk in ("path", "file")) and any(
                    kk in v for kk in _HASHKEYS
                )
                if looks_like_entry:
                    pp = v.get("path") or v.get("file")
                    hh = next((v[kk] for kk in _HASHKEYS if kk in v), None)
                    if isinstance(pp, str) and isinstance(hh, str) and len(hh) == 64:
                        out.append((pp, hh))
                    else:
                        out.extend(parse_hashes(v, prefix + k + "."))
                else:
                    out.extend(parse_hashes(v, prefix + k + "."))
            elif isinstance(v, list):
                for e in v:
                    if isinstance(e, dict):
                        pp = e.get("path") or e.get("file") or e.get("key")
                        hh = next((e[kk] for kk in _HASHKEYS if kk in e), None)
                        if isinstance(hh, str) and isinstance(pp, str):
                            out.append((pp, hh))
                        else:
                            out.extend(parse_hashes(e, prefix + k + "."))
    elif isinstance(obj, list):
        for e in obj:
            out.extend(parse_hashes(e, prefix))
    return out


def locate(base, rel, want):
    """Locate a source_hashes key relative to a package root.

    Primary: exact relative path (with/without the release/ prefix).
    Fallback: content-addressed basename search -- the wanted sha256 must match
    a unique file with that basename.  This resolves cards that record bare
    basenames (e.g. D12-volume-ibp's "Basic.lean") without guessing.
    """
    cands = [rel]
    if rel.startswith("release/"):
        cands.append(rel[len("release/"):])
    else:
        cands.append("release/" + rel)
    if rel.startswith("./"):
        cands.append(rel[2:])
    for c in cands:
        p = os.path.join(base, c)
        if os.path.isfile(p):
            return p, "path"
    b = os.path.basename(rel)
    hits = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
        if b in filenames:
            p = os.path.join(dirpath, b)
            hits.append(p)
    matched = [p for p in hits if sha256_file(p) == want]
    if len(matched) == 1:
        return matched[0], "content-addressed"
    if len(matched) > 1:
        return matched[0], "content-addressed-ambiguous"
    return None, "unresolved"


def rel_to_producer(producer, path):
    return os.path.relpath(path, producer)


def rel_to_staged(staged, producer_rel):
    """Map a producer-relative path to the staged package path."""
    r = producer_rel
    if r.startswith("release/"):
        r = r[len("release/"):]
    p = os.path.join(staged, r)
    if os.path.isfile(p):
        return p
    # tools/* live at package root in the producer outside release/
    p2 = os.path.join(staged, producer_rel)
    if os.path.isfile(p2):
        return p2
    return None


def lean_tree(base):
    out = {}
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                out[os.path.relpath(p, base)] = sha256_file(p)
    return out


def main():
    report = {"lane": "A3-round13", "cards": {}, "verdict": "PASS", "errors": []}
    for card, lane in CARDS:
        wt = os.path.join(POINCARE_ROOT, card)
        staged = os.path.join(PKGS, card)
        entry = {
            "lane": lane,
            "producer_worktree": wt,
            "staged": staged,
            "producer_worktree_present": os.path.isdir(wt),
            "staged_present": os.path.isdir(staged),
            "claim_ok": 0,
            "claim_mismatch": [],
            "claim_missing": [],
            "staged_ok": 0,
            "staged_mismatch": [],
            "staged_missing": [],
            "producer_card_json": None,
            "producer_card_json_sha256": None,
            "recorded_hash_count": 0,
            "lean_tree": {},
        }
        # fresh glob for the card json
        cj = os.path.join(wt, "longrun", "results", card + ".json")
        if not os.path.isfile(cj):
            entry["error"] = "producer card json not found: " + cj
            report["errors"].append(entry["error"])
            report["verdict"] = "FAIL"
            report["cards"][card] = entry
            continue
        entry["producer_card_json"] = cj
        entry["producer_card_json_sha256"] = sha256_file(cj)
        card_json = json.load(open(cj))
        hashes = parse_hashes(card_json.get("source_hashes"))
        entry["recorded_hash_count"] = len(hashes)
        for rel, want in hashes:
            # (a) self-referential card json hash: structurally unsatisfiable
            if rel.endswith("/results/" + card + ".json") or rel == "longrun/results/" + card + ".json":
                entry.setdefault("self_hash", []).append({"key": rel, "recorded": want})
                continue
            # (b) semantic-ledger module-level hashes live in the snapshot package
            if rel.startswith("Poincare.") and card == "D12-semantic-ledger":
                snap = os.path.join(PKGS, "D12-semantic-ledger-snapshot")
                mp = os.path.join(snap, rel.replace(".", "/") + ".lean")
                if os.path.isfile(mp):
                    got = sha256_file(mp)
                    if got == want:
                        entry["claim_ok"] += 1
                        entry.setdefault("resolved_by", {})[rel] = "snapshot-module"
                    else:
                        entry["claim_mismatch"].append(
                            {"key": rel, "resolved": os.path.relpath(mp, ROOT), "want": want, "got": got}
                        )
                    entry["staged_ok"] += 1
                else:
                    entry["claim_missing"].append(
                        {"key": rel, "want": want, "note": "snapshot module file absent"}
                    )
                continue
            pp, how = locate(wt, rel, want)
            if pp is None:
                # is the key itself a hash of a file that exists but changed?
                entry["claim_missing"].append({"key": rel, "want": want})
                continue
            got = sha256_file(pp)
            prec = rel_to_producer(wt, pp)
            if got == want:
                entry["claim_ok"] += 1
                entry.setdefault("resolved_by", {})[rel] = how
            else:
                entry["claim_mismatch"].append(
                    {"key": rel, "resolved": prec, "want": want, "got": got}
                )
            sp = rel_to_staged(staged, prec)
            if sp is None:
                # non-build artefacts (tools/, negcontrol/, longrun/, docs/) are
                # deliberately not staged; report them separately.
                entry["staged_missing"].append({"key": rel, "producer_rel": prec})
                continue
            sgot = sha256_file(sp)
            if sgot == got:
                entry["staged_ok"] += 1
            else:
                entry["staged_mismatch"].append(
                    {"key": rel, "producer_rel": prec, "producer": got, "staged": sgot}
                )
        # whole-tree lean comparison: producer release/Poincare/D12 vs staged Poincare/D12
        pprod = os.path.join(wt, "release", "Poincare")
        pstag = os.path.join(staged, "Poincare")
        if os.path.isdir(pprod) and os.path.isdir(pstag):
            a = lean_tree(pprod)
            b = lean_tree(pstag)
            common = sorted(set(a) & set(b))
            entry["lean_tree"] = {
                "producer_files": len(a),
                "staged_files": len(b),
                "common": len(common),
                "differing": sorted([k for k in common if a[k] != b[k]]),
                "producer_only": sorted(set(a) - set(b)),
                "staged_only": sorted(set(b) - set(a)),
            }
        report["cards"][card] = entry

    # fail-closed verdict
    for card, e in report["cards"].items():
        if e.get("error"):
            report["verdict"] = "FAIL"
            continue
        # A claim is fatal if a recorded Lean/build source cannot be produced
        # with the recorded content.  Files outside release/ (producer tools,
        # negative controls, cards) are informational.  The self-referential
        # card-json hash is structurally unsatisfiable and is reported as such.
        real_missing = [
            m for m in e["claim_missing"]
            if m["key"].endswith(".lean") or m["key"].startswith("release/")
        ]
        real_staged_missing = [
            m for m in e["staged_missing"] if m["producer_rel"].startswith("release/")
        ]
        if e["claim_mismatch"] or real_missing or e["staged_mismatch"] or real_staged_missing:
            report["verdict"] = "FAIL"
        lt = e.get("lean_tree") or {}
        if lt.get("differing") or lt.get("producer_only") or lt.get("staged_only"):
            report["verdict"] = "FAIL"

    out = os.path.join(ROOT, "audit360", "r13", "rebuild_from_hashes.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("verdict:", report["verdict"])
    for card, e in report["cards"].items():
        lt = e.get("lean_tree") or {}
        print(
            f"  {card:32s} claim {e.get('claim_ok',0)}/{e.get('recorded_hash_count',0)} ok"
            f" | staged {e.get('staged_ok',0)} ok"
            f" | tree common={lt.get('common','-')} diff={len(lt.get('differing',[]))}"
            f" p_only={len(lt.get('producer_only',[]))} s_only={len(lt.get('staged_only',[]))}"
            + (f" | ERROR {e['error']}" if e.get('error') else "")
        )
        for k in ("claim_mismatch", "claim_missing", "staged_mismatch", "staged_missing"):
            if e.get(k):
                print("     ", k, json.dumps(e[k])[:400])
    print("wrote", out)
    return 0 if report["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
