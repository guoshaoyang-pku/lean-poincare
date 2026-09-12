#!/usr/bin/env python3
"""Seed a Lake package's .lake/packages from the local poincare-lab checkouts.

The upstream Frenzymath snapshot pins older mathlib dependency revisions than the
local release package, but the local poincare-lab clones carry full history, so
every pinned revision is already present locally.  Cloning with ``--shared``
(alternates) is instant and avoids a slow network clone; the ``origin`` remote is
restored to the canonical URL afterwards so Lake's dependency checks still see a
normal checkout.

Usage: seed-packages.py <package-dir> [<local-packages-dir>]
"""
import json
import os
import subprocess
import sys

DEFAULT_LOCAL = "/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages"


def sh(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def main():
    pkg = os.path.abspath(sys.argv[1])
    local = sys.argv[2] if len(sys.argv) > 2 else DEFAULT_LOCAL
    manifest = json.load(open(os.path.join(pkg, "lake-manifest.json")))
    dest_root = os.path.join(pkg, ".lake", "packages")
    os.makedirs(dest_root, exist_ok=True)
    report = []
    for dep in manifest["packages"]:
        name, rev, url = dep["name"], dep["rev"], dep["url"]
        dest = os.path.join(dest_root, name)
        src = os.path.join(local, name)
        if os.path.isdir(dest):
            have = sh(["git", "-C", dest, "rev-parse", "HEAD"]).stdout.strip()
            report.append({"name": name, "action": "present", "rev": have[:12]})
            continue
        if not os.path.isdir(os.path.join(src, ".git")):
            report.append({"name": name, "action": "missing-local-source"})
            continue
        r = sh(["git", "-C", src, "cat-file", "-t", rev])
        if r.stdout.strip() != "commit":
            report.append({"name": name, "action": "rev-not-local", "rev": rev[:12]})
            continue
        r = sh(["git", "clone", "--shared", "--no-checkout", src, dest])
        if r.returncode != 0:
            report.append({"name": name, "action": "clone-failed", "err": r.stderr.strip()[:200]})
            continue
        r = sh(["git", "-C", dest, "checkout", "--detach", rev])
        if r.returncode != 0:
            report.append({"name": name, "action": "checkout-failed", "err": r.stderr.strip()[:200]})
            continue
        sh(["git", "-C", dest, "remote", "set-url", "origin", url])
        report.append({"name": name, "action": "seeded", "rev": rev[:12]})
    print(json.dumps(report, indent=1))
    return 0 if all(r["action"] in ("present", "seeded") for r in report) else 1


if __name__ == "__main__":
    sys.exit(main())
