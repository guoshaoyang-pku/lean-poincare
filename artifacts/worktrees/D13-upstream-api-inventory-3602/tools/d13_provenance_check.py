#!/usr/bin/env python3
"""D13 provenance check for the preserved frenzymath snapshot.

Verifies that every file in the local snapshot matches the git blob hashes of
the upstream tree recorded in third_party/frenzymath/SOURCE.json, using the
GitHub trees API (no clone required).

Writes manifest/upstream-provenance.json.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SNAP = REPO / "third_party" / "frenzymath" / "Poincare-Conjecture"
SOURCE = REPO / "third_party" / "frenzymath" / "SOURCE.json"
OUT = REPO / "manifest" / "upstream-provenance.json"
PROXY = "socks5h://127.0.0.1:1080"


def git_blob_sha1(path: Path) -> str:
    data = path.read_bytes()
    h = hashlib.sha1()
    h.update(b"blob %d\0" % len(data))
    h.update(data)
    return h.hexdigest()


def fetch_tree(repo: str, tree: str, dest: Path) -> dict:
    url = f"https://api.github.com/repos/{repo}/git/trees/{tree}?recursive=1"
    env = dict(os.environ, ALL_PROXY=PROXY)
    r = subprocess.run(
        ["curl", "-sSL", "--retry", "2", "-o", str(dest), url],
        env=env,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        raise RuntimeError(f"curl failed: {r.stderr}")
    return json.loads(dest.read_text())


def main() -> int:
    src = json.loads(SOURCE.read_text())
    repo_url = src["repository"]
    slug = repo_url.rstrip("/").split("github.com/")[-1]
    tree = src["tree"]
    tmp = Path("/tmp/d13-upstream-tree.json")
    data = fetch_tree(slug, tree, tmp)

    remote = {}
    for ent in data.get("tree", []):
        if ent.get("type") == "blob":
            remote[ent["path"]] = ent["sha"]
    remote_dirs = sum(1 for e in data.get("tree", []) if e.get("type") == "tree")

    local = {}
    for dirpath, dirnames, filenames in os.walk(SNAP):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
        for fn in filenames:
            p = Path(dirpath) / fn
            local[str(p.relative_to(SNAP))] = git_blob_sha1(p)

    missing = sorted(set(remote) - set(local))
    extra = sorted(set(local) - set(remote))
    modified = sorted(p for p in set(remote) & set(local) if remote[p] != local[p])

    record = {
        "schema": "d13-upstream-provenance-v1",
        "generated_at": _dt.datetime.now().astimezone().isoformat(timespec="seconds"),
        "repository": repo_url,
        "commit": src["commit"],
        "tree": tree,
        "github_tree_truncated": data.get("truncated", False),
        "remote_blob_count": len(remote),
        "remote_subdir_count": remote_dirs,
        "local_file_count": len(local),
        "missing_files": missing[:50],
        "missing_count": len(missing),
        "extra_files": extra[:50],
        "extra_count": len(extra),
        "modified_files": modified[:50],
        "modified_count": len(modified),
        "verdict": (
            "exact_match"
            if not missing and not extra and not modified
            else "mismatch"
        ),
        "snapshot_digest_sha256": hashlib.sha256(
            "\n".join(f"{k} {v}" for k, v in sorted(local.items())).encode()
        ).hexdigest(),
    }
    OUT.write_text(json.dumps(record, indent=1) + "\n")
    print(json.dumps({k: record[k] for k in (
        "verdict", "remote_blob_count", "local_file_count",
        "missing_count", "extra_count", "modified_count",
        "snapshot_digest_sha256")}, indent=1))
    return 0 if record["verdict"] == "exact_match" else 1


if __name__ == "__main__":
    raise SystemExit(main())
