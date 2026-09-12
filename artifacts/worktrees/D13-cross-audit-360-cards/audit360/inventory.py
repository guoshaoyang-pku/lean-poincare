#!/usr/bin/env python3
"""D13 cross-audit: locate the 360-produced D12 result cards and verify their
recorded source hashes against the actual sources in the producer worktrees.

Independent re-derivation: hashes are recomputed from bytes on disk; no producer
manifest is trusted. Output: audit360/inventory.json

The cards use three different source_hash schemas:
  flat   {relpath: sha256-hex}
  nested {"sha256": {relpath: hex}, "mathlib": {...}, "frenzymath": ...}
  named  {"package_lean_files": {relpath: hex}, ...}
All are normalised here; non-hex values are recorded as metadata, not hashes.
"""
import hashlib
import json
import os
import re
import sys

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
HERE = os.path.join(WT, "D13-cross-audit-360-cards")
OUT = os.path.join(HERE, "audit360", "inventory.json")

CARDS = [
    ("D12-connection-curvature", "360-1"),
    ("D12-volume-ibp", "360-1"),
    ("D12-tensor-maximum-bochner", "360-1"),
    ("D12-spectral-sobolev", "360-1"),
    ("D12-semantic-ledger", "360-1"),
    ("D12-comparison-geodesics", "360-2"),
    ("D12-geometric-compactness", "360-2"),
    ("D12-triangulation-topology", "360-2"),
    ("D12-surgery-recognition", "360-2"),
]

HEX = re.compile(r"^[0-9a-f]{64}$")
SKIP_DIRS = {".lake", "third_party", "input", "logs", "tmp", "scratch"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def collect_files(root):
    """(relpath, fullpath) for every file under root, excluding caches/imports."""
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            out.append((os.path.relpath(full, root), full))
    return out


def normalise(recorded):
    """Return (hash_map, metadata) from any of the card schemas."""
    if not isinstance(recorded, dict):
        return {}, {"source_hashes_raw_type": type(recorded).__name__}
    meta = {}
    # nested container keys
    for k in ("sha256", "package_lean_files", "files"):
        if isinstance(recorded.get(k), dict):
            inner = recorded[k]
            for kk, vv in recorded.items():
                if kk != k:
                    meta[kk] = vv
            return {a: b for a, b in inner.items() if isinstance(b, str)}, meta
    # flat
    return {a: b for a, b in recorded.items() if isinstance(b, str)}, meta


def main():
    inv = {"cards": [], "missing": []}
    for card, lane in CARDS:
        wt = os.path.join(WT, card)
        entry = {"card": card, "lane": lane, "worktree": wt}
        if not os.path.isdir(wt):
            entry["present"] = False
            inv["missing"].append(entry)
            inv["cards"].append(entry)
            continue
        entry["present"] = True
        card_md = os.path.join(wt, "longrun", "results", card + ".md")
        card_json = os.path.join(wt, "longrun", "results", card + ".json")
        entry["card_md"] = card_md if os.path.isfile(card_md) else None
        entry["card_json"] = card_json if os.path.isfile(card_json) else None
        if entry["card_md"]:
            entry["card_md_sha256"] = sha256(card_md)
            entry["card_md_mtime"] = os.path.getmtime(card_md)
        if entry["card_json"]:
            entry["card_json_sha256"] = sha256(card_json)
            entry["card_json_mtime"] = os.path.getmtime(card_json)
        ck = os.path.join(wt, "checkpoint.json")
        entry["checkpoint"] = ck if os.path.isfile(ck) else None
        if entry["checkpoint"]:
            entry["checkpoint_sha256"] = sha256(ck)
            with open(ck) as f:
                entry["checkpoint_status"] = json.load(f).get("status")
        rel = os.path.join(wt, "release")
        entry["release"] = rel if os.path.isdir(rel) else None
        # recorded source hashes
        recorded_raw = {}
        for src in (entry["card_json"], entry["checkpoint"]):
            if src and os.path.isfile(src):
                with open(src) as f:
                    try:
                        recorded_raw = json.load(f).get("source_hashes", {}) or {}
                    except Exception:
                        recorded_raw = {}
                if recorded_raw:
                    entry["hash_source"] = os.path.relpath(src, wt)
                    break
        recorded, meta = normalise(recorded_raw)
        entry["hash_metadata"] = meta
        entry["recorded_hash_count"] = len(recorded)
        all_files = collect_files(wt)
        by_suffix = {}
        for crel, cfull in all_files:
            by_suffix.setdefault(crel, cfull)
        checks = []
        n_ok = n_bad = n_amb = 0
        for key, want in sorted(recorded.items()):
            key_n = key.replace("release/", "", 1) if key.startswith("release/") else key
            cands = [(r, f) for (r, f) in all_files
                     if r == key or r == key_n or r.endswith("/" + key_n)]
            matches = []
            for crel, cfull in cands:
                got = sha256(cfull)
                matches.append({"rel": crel, "sha256": got, "match": got == want})
            ok = [m for m in matches if m["match"]]
            if ok:
                n_ok += 1
                if len(ok) > 1:
                    n_amb += 1
                # a matching file that also has a nonmatching twin is a warning
                if len(matches) > len(ok):
                    n_amb += 1
            else:
                n_bad += 1
            checks.append({"key": key, "want": want, "candidates": matches,
                           "verdict": "ok" if ok else ("mismatch" if matches else "missing")})
        entry["hash_checks"] = checks
        entry["hash_summary"] = {"ok": n_ok, "bad": n_bad, "ambiguous": n_amb,
                                 "total": len(checks)}
        inv["cards"].append(entry)
    with open(OUT, "w") as f:
        json.dump(inv, f, indent=1)
    for e in inv["cards"]:
        if not e.get("present"):
            print("MISSING", e["card"])
        else:
            print(e["card"], e.get("hash_summary"), "status=", e.get("checkpoint_status"),
                  "hashsrc=", e.get("hash_source"))


if __name__ == "__main__":
    main()
