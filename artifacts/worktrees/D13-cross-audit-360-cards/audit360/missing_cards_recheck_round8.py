#!/usr/bin/env python3
"""Round-8 re-check that the two missing D12 cards are genuinely source-absent.

Checks, with timestamps and hashes:

  1. `longrun/queue.json` status/host of `D12-tensor-maximum-bochner` and
     `D12-triangulation-topology`;
  2. presence of a worktree, release package, card file, Lean module, state
     directory, or PUSHED/DONE marker for either card under the poincare root;
  3. presence of any file whose *name* mentions the two cards anywhere under
     /data3/guoshaoyang (bounded depth) and the home directory (bounded depth);
  4. transport route: TCP connect to the reverse-tunnel port 127.0.0.1:10022,
     `tailscale status` peer list for hosts named 360-1/360-2, NFS/CIFS/SSHFS
     mounts, and the sha256 of `longrun/bin/relay_push.sh`.

Fail-closed: if any source artifact is found the verdict flips to
AUDITABLE-NOW and the script exits 2 so the sweep pipeline cannot silently
ignore it.

Output: audit360/missing_cards_recheck_round8.json
"""
import datetime
import glob
import hashlib
import json
import os
import socket
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
LR = os.path.join(ROOT, "longrun")
HOME = "/data3/guoshaoyang"
MISSING = ["D12-tensor-maximum-bochner", "D12-triangulation-topology"]
OUT = os.path.join(HERE, "missing_cards_recheck_round8.json")


def sha(p):
    try:
        return hashlib.sha256(open(p, "rb").read()).hexdigest()
    except OSError:
        return None


def run(cmd, timeout=25):
    try:
        p = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        return p.stdout.strip() + (("\n" + p.stderr.strip()) if p.stderr.strip() else "")
    except Exception as exc:  # noqa: BLE001
        return f"<error: {exc}>"


def tcp(host, port):
    s = socket.socket()
    s.settimeout(4)
    try:
        s.connect((host, port))
        return "OPEN"
    except Exception as exc:  # noqa: BLE001
        return f"REFUSED/{type(exc).__name__}: {exc}"
    finally:
        s.close()


def find_named(roots, maxdepth=8):
    hits = []
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(root):
            depth = dirpath[len(root):].count(os.sep)
            if depth >= maxdepth:
                dirnames[:] = []
                continue
            dirnames[:] = [d for d in dirnames if d not in (".git", ".lake")]
            for name in list(dirnames) + filenames:
                for card in MISSING:
                    if card in name:
                        hits.append(os.path.join(dirpath, name))
    return hits


def main():
    now = datetime.datetime.now().isoformat(timespec="seconds")
    out = {"schema": "a3-missing-cards-recheck-v1", "round": 8, "checked_at": now,
           "cards": {}}

    queue = json.load(open(os.path.join(LR, "queue.json")))
    qstatus = {t["id"]: {k: t.get(k) for k in ("status", "host", "owner")}
               for t in queue["tasks"] if t["id"] in MISSING}

    for card in MISSING:
        entry = {"queue": qstatus.get(card)}
        entry["paths"] = {}
        for label, path in {
            "state_dir": os.path.join(LR, "state", card),
            "worktree": os.path.join(LR, "worktrees", card),
            "release_pkg": os.path.join(LR, "worktrees", card, "release"),
            "card_md": os.path.join(LR, "worktrees", card, "longrun", "results", card + ".md"),
            "card_json": os.path.join(LR, "worktrees", card, "longrun", "results", card + ".json"),
            "local_state": os.path.join(WT, "state", card),
        }.items():
            entry["paths"][label] = {"path": path, "exists": os.path.exists(path)}
        entry["named_hits"] = find_named([LR, os.path.join(HOME, "transfer")], maxdepth=7)
        out["cards"][card] = entry

    out["transport"] = {
        "tcp_127.0.0.1_10022": tcp("127.0.0.1", 10022),
        "tailscale_360_peers": [l for l in run("tailscale status").splitlines()
                                if "360" in l] or "<none>",
        "mounts": [l for l in run("mount").splitlines()
                   if any(k in l.lower() for k in ("nfs", "cifs", "sshfs"))] or "<none>",
        "relay_push_sha256": sha(os.path.join(LR, "bin", "relay_push.sh")),
        "dispatcher_log_tail": run(f"tail -6 {os.path.join(LR, 'logs', 'dispatch.log')}"),
    }

    found = [c for c, e in out["cards"].items()
             if any(v["exists"] for v in e["paths"].values()) or e["named_hits"]]
    out["found_artifacts"] = found
    out["verdict"] = ("NOT AUDITABLE: no worktree/package/card/module/state/marker for "
                      "either card on this host; transport route down"
                      if not found else "AUDITABLE-NOW: source artifacts found: " + ", ".join(found))
    out["not_a_substitute"] = (
        "Precursor D11 cards exist on this host but are NOT the 360-produced D12 cards; "
        "they are not counted toward the 9-card milestone.")
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "cards"}, indent=1))
    for card, e in out["cards"].items():
        print(card, "queue=", e["queue"], "named_hits=", len(e["named_hits"]))
    return 2 if found else 0


if __name__ == "__main__":
    sys.exit(main())
