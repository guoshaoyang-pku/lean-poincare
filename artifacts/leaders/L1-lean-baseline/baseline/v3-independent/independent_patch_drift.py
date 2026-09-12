#!/usr/bin/env python3
"""Independent A1 drift verification: replay baseline/a1/a1-restatement.patch on a
fresh byte-copy of release/ (excluding .lake) and compare the resulting drift
against baseline/a1/patched-drift.json and the recorded patched tree."""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
RELEASE = os.path.join(WT, "release")
PATCH = os.path.join(WT, "baseline/a1/a1-restatement.patch")
DRIFT = os.path.join(WT, "baseline/a1/patched-drift.json")
PATCHED_RELEASE = os.path.join(WT, "baseline/a1/patched-release")
DEST = os.path.join(HERE, "patch-check")
OUT_JSON = os.path.join(HERE, "independent-patch-drift.json")
OUT_LOG = os.path.join(HERE, "independent-patch-drift.log")


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
    out = {}
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            out[norm(os.path.relpath(full, root))] = sha256_file(full)
    return out


def copy_tree(src, dst):
    n = 0
    for dirpath, dirnames, filenames in os.walk(src, followlinks=False):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        rel = os.path.relpath(dirpath, src)
        target_dir = dst if rel == "." else os.path.join(dst, rel)
        os.makedirs(target_dir, exist_ok=True)
        for fn in filenames:
            s = os.path.join(dirpath, fn)
            if os.path.islink(s) or not os.path.isfile(s):
                continue
            shutil.copyfile(s, os.path.join(target_dir, fn))
            shutil.copystat(s, os.path.join(target_dir, fn))
            n += 1
    return n


def main():
    t0 = time.time()
    log = []

    def emit(s=""):
        print(s)
        log.append(s)

    emit("== independent A1 patch replay ==")
    if os.path.exists(DEST):
        shutil.rmtree(DEST)
    os.makedirs(DEST)
    copied = copy_tree(RELEASE, DEST)
    emit("copied %d files from release/ (excl .lake) to %s" % (copied, DEST))
    frozen = hash_tree(RELEASE)
    emit("frozen release hashes: %d" % len(frozen))

    with open(PATCH, "rb") as f:
        rc = subprocess.run(["patch", "-p1", "--no-backup-if-mismatch", "-i", PATCH],
                            cwd=DEST, capture_output=True, text=True)
    emit("$ patch -p1 --no-backup-if-mismatch -i %s   (cwd=%s)" % (PATCH, DEST))
    emit("exit=%d" % rc.returncode)
    for line in (rc.stdout or "").splitlines():
        emit("  stdout| " + line)
    for line in (rc.stderr or "").splitlines():
        emit("  stderr| " + line)

    patched = hash_tree(DEST)
    emit("patched tree hashes: %d" % len(patched))

    changed, added, removed = [], [], []
    for p, h in sorted(frozen.items()):
        if p not in patched:
            removed.append({"path": p, "frozen": h})
        elif patched[p] != h:
            changed.append({"path": p, "frozen": h, "patched": patched[p]})
    for p in sorted(set(patched) - set(frozen)):
        added.append({"path": p, "sha256": patched[p]})

    emit("MY REPLAY: changed=%d added=%d removed=%d" % (len(changed), len(added), len(removed)))
    for c in changed:
        emit("  CHANGED %s frozen=%s patched=%s" % (c["path"], c["frozen"], c["patched"]))
    for a in added:
        emit("  ADDED   %s sha256=%s" % (a["path"], a["sha256"]))
    for r in removed:
        emit("  REMOVED %s frozen=%s" % (r["path"], r["frozen"]))
    # stray patch artifacts (should be none)
    strays = [a["path"] for a in added if a["path"].endswith((".orig", ".rej"))]
    emit("stray .orig/.rej artifacts: %s" % (strays or "none"))

    claim = json.load(open(DRIFT, encoding="utf-8"))
    claim_changed = {c["path"]: (c["frozen"], c["patched"]) for c in claim["changed"]}
    claim_added = {a["path"]: a["sha256"] for a in claim["added"]}
    claim_removed = [r["path"] if isinstance(r, dict) else r for r in claim.get("removed", [])]
    my_changed = {c["path"]: (c["frozen"], c["patched"]) for c in changed}
    my_added = {a["path"]: a["sha256"] for a in added}

    cmp_claim = {
        "claimed_changed_count": len(claim_changed),
        "claimed_added_count": len(claim_added),
        "claimed_removed_count": len(claim_removed),
        "changed_set_equal": set(claim_changed) == set(my_changed),
        "added_set_equal": set(claim_added) == set(my_added),
        "changed_hashes_equal": claim_changed == my_changed,
        "added_hashes_equal": claim_added == my_added,
        "removed_set_equal": set(claim_removed) == {r["path"] for r in removed},
        "only_in_claim_changed": sorted(set(claim_changed) - set(my_changed)),
        "only_in_my_changed": sorted(set(my_changed) - set(claim_changed)),
        "only_in_claim_added": sorted(set(claim_added) - set(my_added)),
        "only_in_my_added": sorted(set(my_added) - set(claim_added)),
        "expected_changed_from_claim_matches": sorted(claim.get("expected_changed", [])) == sorted(my_changed),
        "expected_added_from_claim_matches": sorted(claim.get("expected_added", [])) == sorted(my_added),
    }
    emit("vs patched-drift.json: changed_set_equal=%s added_set_equal=%s changed_hashes_equal=%s added_hashes_equal=%s removed_set_equal=%s"
         % (cmp_claim["changed_set_equal"], cmp_claim["added_set_equal"], cmp_claim["changed_hashes_equal"],
            cmp_claim["added_hashes_equal"], cmp_claim["removed_set_equal"]))

    # Compare against recorded patched tree baseline/a1/patched-release.
    pr_tree = hash_tree(PATCHED_RELEASE) if os.path.isdir(PATCHED_RELEASE) else None
    cmp_tree = {"patched_release_exists": pr_tree is not None}
    if pr_tree is not None:
        pr_changed = {p: h for p, h in pr_tree.items() if frozen.get(p) != h}
        cmp_tree.update({
            "recorded_patched_file_count": len(pr_tree),
            "recorded_changed_count": len(pr_changed),
            "recorded_added": sorted(set(pr_tree) - set(frozen)),
            "recorded_removed": sorted(set(frozen) - set(pr_tree)),
            "my_tree_vs_recorded_tree_diff": sorted(
                p for p in set(pr_tree) | set(patched)
                if pr_tree.get(p) != patched.get(p)),
            "changed_files_same_hash": all(patched.get(p) == h for p, h in pr_changed.items()),
        })
        emit("vs baseline/a1/patched-release: files=%d changed=%d added=%s removed=%s tree_diff=%s changed_files_same_hash=%s"
             % (len(pr_tree), len(pr_changed), cmp_tree["recorded_added"], cmp_tree["recorded_removed"],
                cmp_tree["my_tree_vs_recorded_tree_diff"], cmp_tree["changed_files_same_hash"]))

    match = (
        rc.returncode == 0
        and not strays
        and len(changed) == 7 and len(added) == 1 and len(removed) == 0
        and cmp_claim["changed_hashes_equal"] and cmp_claim["added_hashes_equal"]
        and cmp_claim["expected_changed_from_claim_matches"] and cmp_claim["expected_added_from_claim_matches"]
        and cmp_tree.get("my_tree_vs_recorded_tree_diff") == []
        and cmp_tree.get("recorded_added") == sorted(my_added)
        and cmp_tree.get("recorded_removed") == []
    )
    verdict = "INDEPENDENT-PATCH-DRIFT-MATCH" if match else "INDEPENDENT-PATCH-DRIFT-MISMATCH"

    report = {
        "schema": "l1-lean-baseline/v3-independent-patch-drift-v1",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "frozen_tree": RELEASE,
        "frozen_files": len(frozen),
        "copy_dest": DEST,
        "copied_files": copied,
        "patch_command": "patch -p1 --no-backup-if-mismatch -i %s" % PATCH,
        "patch_exit": rc.returncode,
        "patch_stdout": rc.stdout,
        "patch_stderr": rc.stderr,
        "replay_changed_count": len(changed),
        "replay_added_count": len(added),
        "replay_removed_count": len(removed),
        "changed": changed,
        "added": added,
        "removed": removed,
        "stray_artifacts": strays,
        "vs_patched_drift_json": cmp_claim,
        "vs_patched_release_tree": cmp_tree,
        "verdict": verdict,
        "wall_seconds": round(time.time() - t0, 3),
    }
    emit("VERDICT %s (wall %.3fs)" % (verdict, report["wall_seconds"]))

    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=1)
        f.write("\n")
    with open(OUT_LOG, "w", encoding="utf-8") as f:
        f.write("\n".join(log) + "\n")
    return 0 if match else 1


if __name__ == "__main__":
    sys.exit(main())
