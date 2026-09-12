#!/usr/bin/env python3
"""L1-lean-baseline P5 source-hash independent checker (verifier lane).

Implemented from the manifest formats only; the P5 gate tool
(baseline/tools/p5_hash_gate.py) was NOT read before this script was written
and run.  Hash every regular file under release/ excluding .lake/, compare
against four historical accepted manifests, recompute the three pin sha256
values, and cross-check two frozen in-tree hash records.
"""
import hashlib
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))          # .../L1-lean-baseline
LONGRUN = os.path.dirname(os.path.dirname(os.path.dirname(WT)))  # .../longrun
RELEASE = os.path.join(WT, "release")
OUT_JSON = os.path.join(HERE, "independent-hash-check.json")
OUT_LOG = os.path.join(HERE, "independent-hash-check.log")

# Historical accepted manifests (paths discovered on disk; logical names from
# baseline/reconcile/source-hash-drift.json and baseline/logs/pin-hashes.txt).
M_D13_FINAL = os.path.join(LONGRUN, "worktrees/D13-integrated-kernel-audit/audit-evidence/final-release-hashes.txt")
M_D13_BASE = os.path.join(LONGRUN, "worktrees/D13-integrated-kernel-audit/audit-evidence/base-release-hashes-preintegration.txt")
M_D6 = os.path.join(LONGRUN, "worktrees/D6_weekly_release/manifest/weekly-release-manifest.json")
M_D12 = os.path.join(LONGRUN, "results/D12-semantic-ledger.json")
M_D12_ALT = os.path.join(LONGRUN, "worktrees/D12-semantic-ledger/manifest/d12-semantic-ledger.json")

PRE_REBUILD = os.path.join(WT, "baseline/hashes/release-sources-pre-rebuild.json")
DRIFT = os.path.join(WT, "baseline/reconcile/source-hash-drift.json")
PINS = os.path.join(WT, "baseline/logs/pin-hashes.txt")

PINS_ORDER = ["lean-toolchain", "lake-manifest.json", "lakefile.toml"]


def norm(p):
    p = p.replace("\\", "/")
    while p.startswith("./"):
        p = p[2:]
    return p


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def hash_tree(root):
    """Return {relpath: sha256} for regular files, excluding .lake/ anywhere."""
    out = {}
    symlinks = []
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            if os.path.islink(full):
                symlinks.append(norm(os.path.relpath(full, root)))
                continue
            if not os.path.isfile(full):
                continue
            rel = norm(os.path.relpath(full, root))
            out[rel] = sha256_file(full)
    return out, symlinks


def parse_sha256sums(path):
    """`<sha256>  ./rel/path` lines (D13 format)."""
    rec = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip():
                continue
            parts = line.split(None, 1)
            if len(parts) != 2:
                raise ValueError("unparsable line in %s: %r" % (path, line))
            rec[norm(parts[1])] = parts[0].lower()
    return rec


def parse_d6(path):
    d = json.load(open(path, encoding="utf-8"))
    return {norm(e["path"]): e["sha256"].lower() for e in d["package"]["files"]}


def parse_d12(path):
    d = json.load(open(path, encoding="utf-8"))
    return {norm(k): v.lower() for k, v in d["source_hashes"]["package_lean_files"].items()}


def compare(recorded, current):
    matched, changed, absent = [], [], []
    for p, h in sorted(recorded.items()):
        if p not in current:
            absent.append({"path": p, "recorded": h})
        elif current[p] == h:
            matched.append(p)
        else:
            changed.append({"path": p, "recorded": h, "current": current[p]})
    added = sorted(set(current) - set(recorded))
    return {
        "recorded_count": len(recorded),
        "matched_count": len(matched),
        "changed_count": len(changed),
        "absent_count": len(absent),
        "added_count": len(added),
        "changed": changed,
        "absent": absent,
        "added": added,
    }


def main():
    t0 = time.time()
    log = []

    def emit(s=""):
        print(s)
        log.append(s)

    emit("== L1 independent hash check ==")
    emit("time=%s" % time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    emit("release=%s" % RELEASE)

    current, symlinks = hash_tree(RELEASE)
    n_lean = sum(1 for p in current if p.endswith(".lean"))
    emit("release regular files (excl .lake): %d; .lean: %d; symlinks skipped: %d"
         % (len(current), n_lean, len(symlinks)))
    n_lake_files = sum(len(fs) for _, _, fs in os.walk(os.path.join(RELEASE, ".lake"))) if os.path.isdir(os.path.join(RELEASE, ".lake")) else 0
    emit("release ALL files incl .lake (walk count): %d" % (len(current) + n_lake_files))

    report = {
        "schema": "l1-lean-baseline/v3-independent-hash-check-v1",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "release_root": RELEASE,
        "release_file_count_excl_lake": len(current),
        "release_lean_count": n_lean,
        "symlinks_skipped": symlinks,
        "manifests": {},
        "pins": [],
        "pre_rebuild": None,
        "drift_current_hashes": None,
        "wall_seconds": None,
    }

    manifest_specs = [
        ("D13-final-post-integration(462)", M_D13_FINAL, parse_sha256sums),
        ("D13-pre-integration-base(286)", M_D13_BASE, parse_sha256sums),
        ("D6-weekly-release-package.files(63)", M_D6, parse_d6),
        ("D12-semantic-ledger.package_lean_files(66)", M_D12, parse_d12),
    ]
    for label, path, parser in manifest_specs:
        exists = os.path.isfile(path)
        entry = {"manifest_label": label, "manifest_path": path, "manifest_exists": exists}
        if not exists:
            entry["error"] = "manifest file not found"
            emit("MANIFEST %-40s MISSING %s" % (label, path))
            report["manifests"][label] = entry
            continue
        recorded = parser(path)
        res = compare(recorded, current)
        entry.update(res)
        report["manifests"][label] = entry
        emit("MANIFEST %-40s recorded=%d matched=%d changed=%d absent=%d added=%d"
             % (label, res["recorded_count"], res["matched_count"], res["changed_count"],
                res["absent_count"], res["added_count"]))
        for c in res["changed"]:
            emit("   CHANGED %s recorded=%s current=%s" % (c["path"], c["recorded"], c["current"]))
        for a in res["absent"]:
            emit("   ABSENT  %s recorded=%s" % (a["path"], a["recorded"]))

    # D12 alternate copy sanity: same 66 entries?
    alt = {"path": M_D12_ALT, "exists": os.path.isfile(M_D12_ALT)}
    if alt["exists"]:
        r_alt = parse_d12(M_D12_ALT)
        r_main = parse_d12(M_D12)
        alt["entries"] = len(r_alt)
        alt["identical_to_primary"] = (r_alt == r_main)
        emit("D12 alternate ledger copy: entries=%d identical_to_primary=%s"
             % (alt["entries"], alt["identical_to_primary"]))
    report["d12_alternate"] = alt

    # Pins: expected from baseline/logs/pin-hashes.txt (sha256  name).
    expected_pins = parse_sha256sums(PINS)
    emit("pin-hashes.txt entries: %d" % len(expected_pins))
    pins_ok = True
    pin_names = sorted(expected_pins, key=lambda p: (PINS_ORDER.index(p) if p in PINS_ORDER else 99, p))
    for name in pin_names:
        exp = expected_pins[name]
        full = os.path.join(RELEASE, name)
        cur = sha256_file(full) if os.path.isfile(full) else None
        ok = cur == exp
        pins_ok = pins_ok and ok
        report["pins"].append({"path": name, "expected": exp, "current": cur, "ok": ok})
        emit("PIN %-20s expected=%s current=%s ok=%s" % (name, exp, cur, ok))

    # Frozen pre-rebuild record: 456 .lean files.
    pr = json.load(open(PRE_REBUILD, encoding="utf-8"))
    pr_rec = {norm(e["path"]): e["sha256"].lower() for e in pr["files"]}
    pr_res = compare(pr_rec, current)
    report["pre_rebuild"] = {
        "path": PRE_REBUILD,
        "recorded_count": pr_res["recorded_count"],
        "matched_count": pr_res["matched_count"],
        "changed_count": pr_res["changed_count"],
        "absent_count": pr_res["absent_count"],
        "added_count": pr_res["added_count"],
        "changed": pr_res["changed"],
        "absent": pr_res["absent"],
        "added_count_vs_lean_subset": sum(1 for p in pr_res["added"] if p.endswith(".lean")),
    }
    emit("PRE-REBUILD %s recorded=%d matched=%d changed=%d absent=%d added(vs all current)=%d"
         % (PRE_REBUILD, pr_res["recorded_count"], pr_res["matched_count"],
            pr_res["changed_count"], pr_res["absent_count"], pr_res["added_count"]))
    for c in pr_res["changed"]:
        emit("   CHANGED %s recorded=%s current=%s" % (c["path"], c["recorded"], c["current"]))
    for a in pr_res["absent"]:
        emit("   ABSENT  %s recorded=%s" % (a["path"], a["recorded"]))

    # Drift record current_hashes (462 entries).
    dr = json.load(open(DRIFT, encoding="utf-8"))
    dr_cur = {norm(k): v.lower() for k, v in dr["current_hashes"].items()}
    d_res = compare(dr_cur, current)
    report["drift_current_hashes"] = {
        "path": DRIFT,
        "recorded_count": d_res["recorded_count"],
        "matched_count": d_res["matched_count"],
        "changed_count": d_res["changed_count"],
        "absent_count": d_res["absent_count"],
        "added_count": d_res["added_count"],
        "changed": d_res["changed"],
        "absent": d_res["absent"],
        "added": d_res["added"],
    }
    emit("DRIFT current_hashes recorded=%d matched=%d changed=%d absent=%d added=%d"
         % (d_res["recorded_count"], d_res["matched_count"], d_res["changed_count"],
            d_res["absent_count"], d_res["added_count"]))
    for c in d_res["changed"]:
        emit("   CHANGED %s recorded=%s current=%s" % (c["path"], c["recorded"], c["current"]))
    for a in d_res["absent"]:
        emit("   ABSENT  %s recorded=%s" % (a["path"], a["recorded"]))

    overall = (
        all(v["changed_count"] == 0 and v["absent_count"] == 0 for k, v in report["manifests"].items() if v.get("manifest_exists"))
        and pins_ok
        and pr_res["changed_count"] == 0 and pr_res["absent_count"] == 0
        and d_res["changed_count"] == 0 and d_res["absent_count"] == 0 and d_res["added_count"] == 0
    )
    report["verdict"] = "INDEPENDENT-HASH-CHECK-PASS" if overall else "INDEPENDENT-HASH-CHECK-FAIL"
    report["wall_seconds"] = round(time.time() - t0, 3)
    emit("VERDICT %s (wall %.3fs)" % (report["verdict"], report["wall_seconds"]))

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=1, sort_keys=False)
        f.write("\n")
    with open(OUT_LOG, "w", encoding="utf-8") as f:
        f.write("\n".join(log) + "\n")
    return 0 if overall else 1


if __name__ == "__main__":
    sys.exit(main())
