#!/usr/bin/env python3
"""D9: per-theorem import-cone analysis from TheoremConeAudit output.

Input : release/Audit/D9/logs/theorem_cones.raw  (D9THEOREM TSV lines)
Output: release/Audit/D9/logs/theorem_cones.json

For every theorem, the *direct* module set is the set of modules owning the constants
that occur in its type or proof term.  Its import cone is the union of the transitive
import closures of those modules (module import graph rebuilt from sources, exactly as
`import_cones.py` does).  This is a per-theorem import cone in the strict Lean sense:
every constant the proof can possibly unfold lives in a module reached this way.
"""
import json
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d9_scanner import code_mask  # noqa: E402

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
ELAN = "/data/home/guoshaoyang/workdir/lean_poincare/elan"
PKGS = os.path.join(RELEASE, ".lake", "packages")
RAW = os.path.join(HERE, "logs", "theorem_cones.raw")
OUT = os.path.join(HERE, "logs", "theorem_cones.json")

ROOTS = [
    os.path.join(ELAN, "toolchains", "leanprover--lean4---v4.34.0-rc2", "src", "lean"),
    os.path.join(ELAN, "toolchains", "leanprover--lean4---v4.34.0-rc2", "src", "lean", "lake"),
    os.path.join(PKGS, "mathlib"),
    os.path.join(PKGS, "batteries"),
    os.path.join(PKGS, "aesop"),
    os.path.join(PKGS, "Qq"),
    os.path.join(PKGS, "proofwidgets"),
    os.path.join(PKGS, "Cli"),
    os.path.join(PKGS, "importGraph"),
    os.path.join(PKGS, "LeanSearchClient"),
    os.path.join(PKGS, "plausible"),
    RELEASE,
]

IMPORT_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+|private[ \t]+|protected[ \t]+)?import[ \t]+"
    r"([A-Za-z0-9_.\u00ab\u00bb]+)[ \t]*$", re.M)

# compiler-generated / auxiliary theorem names, not human-authored claims
AUTO_SUFFIXES = (".mk", ".casesOn", ".rec", ".recOn", ".inj", ".injEq", ".noConfusion",
                 ".noConfusionType", ".below", ".brecOn", ".ibelow", ".sizeOf_spec",
                 ".toCtorIdx", ".ctorIdx", ".ind", ".rec_1", ".proof_1", ".proof_2",
                 ".proof_3", ".proof_4", ".proof_5", ".eq_1", ".eq_2", ".eq_def",
                 ".match_1", ".splitter", ".dcongr_rhs", ".dcongr_heq", ".ofNat",
                 ".unary", ".binary")


def is_auto(name):
    if "_proof_" in name or "._@." in name or "match_" in name.split(".")[-1]:
        return True
    return name.endswith(AUTO_SUFFIXES)


def build_graph():
    mods = {}
    for r in ROOTS:
        for dp, dn, fn in os.walk(r):
            dn[:] = [d for d in dn if d not in (".lake", ".git")]
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, r)[:-5].replace(os.sep, ".")
                mods.setdefault(mod, p)
    deps = {}
    missing = set()
    for mod, p in mods.items():
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            deps[mod] = set()
            continue
        d = set(IMPORT_RE.findall(code_mask(text)))
        for x in d:
            if x not in mods:
                missing.add(x)
        deps[mod] = {x for x in d if x in mods}
    # index modules
    idx = {m: i for i, m in enumerate(mods)}
    adj = [[] for _ in mods]
    for m, ds in deps.items():
        adj[idx[m]] = [idx[x] for x in ds]
    return mods, idx, adj, sorted(missing)


def parse_raw():
    theorems = []
    extra = {}
    meta = {"schemas": [], "counts": {}, "modules": []}
    for line in open(RAW, encoding="utf-8"):
        line = line.rstrip("\n")
        if line.startswith("D9THEOREM\t"):
            f = line.split("\t")
            if len(f) != 12:
                print("WARN short D9THEOREM line:", len(f), f[1] if len(f) > 1 else "?", file=sys.stderr)
                continue
            theorems.append({
                "name": f[1], "module": f[2], "direct_consts": int(f[3]),
                "direct_modules": int(f[4]), "explicit_binders": int(f[5]),
                "prop_binders": int(f[6]), "axiom_count": int(f[7]),
                "axiom_cone": f[8], "direct_module_list": f[9].split() if f[9] else [],
                "hypotheses": f[10].split(" ;; ") if f[10] else [],
                "type": f[11],
            })
        elif line.startswith("D9THMEX\t"):
            f = line.split("\t")
            if len(f) != 5:
                print("WARN short D9THMEX line:", len(f), file=sys.stderr)
                continue
            extra[f[1]] = {"true_conclusion": f[2] == "true",
                           "false_hypotheses": int(f[3]), "conclusion": f[4]}
        elif line.startswith("D9CONE\t"):
            f = line.split("\t")
            if len(f) >= 3 and f[1] == "module":
                meta["modules"].append(f[2])
            elif len(f) >= 3 and f[1] != "SHAPE":
                meta["counts"][f[1]] = f[2]
            else:
                meta["schemas"].append(f[1] if len(f) > 1 else "?")
    for t in theorems:
        t.update(extra.get(t["name"], {"true_conclusion": False, "false_hypotheses": 0,
                                       "conclusion": ""}))
    return theorems, meta


def main():
    mods, idx, adj, missing = build_graph()
    theorems, meta = parse_raw()
    print(f"modules={len(mods)} missing_imports={len(missing)} theorems={len(theorems)}")

    names = list(mods)
    # Release membership is taken from the census itself (filesystem-derived module list),
    # NOT from a name-prefix whitelist: the first census used a whitelist and silently
    # dropped module `ReleaseCheck`.
    release_modules = set(meta["modules"])
    project = [m in release_modules for m in names]
    unknown_release = sorted(release_modules - set(names))
    if unknown_release:
        print("release modules absent from import graph:", unknown_release[:10])
    mark = [0] * len(adj)
    stamp = 0

    def cone_size(direct):
        """multi-source DFS; returns (all-module count, project-module count) for the
        union of transitive import closures of `direct` (including `direct`)."""
        nonlocal stamp
        stamp += 1
        st = stamp
        stack = []
        n = 0
        np = 0
        for m in direct:
            i = idx.get(m)
            if i is None:
                continue
            if mark[i] != st:
                mark[i] = st
                n += 1
                np += project[i]
                stack.append(i)
        while stack:
            i = stack.pop()
            for j in adj[i]:
                if mark[j] != st:
                    mark[j] = st
                    n += 1
                    np += project[j]
                    stack.append(j)
        return n, np

    unknown = set()
    for t in theorems:
        t["cone_size"], t["release_cone"] = cone_size(t["direct_module_list"])
        t["cone_with_self"], t["release_cone_with_self"] = cone_size(
            t["direct_module_list"] + [t["module"]])
        if t["cone_size"] == 0:
            unknown.add(t["name"])
        t["auto_generated"] = is_auto(t["name"])
    print("theorems with zero resolved direct modules:", len(unknown))

    human = [t for t in theorems if not t["auto_generated"]]
    key = lambda t: (-t["release_cone"], -t["cone_size"], -t["direct_modules"],
                     -t["direct_consts"], t["name"])
    all_sorted = sorted(theorems, key=key)
    human_sorted = sorted(human, key=key)

    # saturation diagnostics
    from collections import Counter
    dist = Counter(t["cone_size"] for t in human)
    max_cone = max(dist) if dist else 0
    print(f"saturation: {dist[max_cone]}/{len(human)} human theorems at max cone {max_cone}")
    print(f"max release-cone: {max((t['release_cone'] for t in human), default=0)}")

    out = {
        "schema": "d9-adversarial-audit/theorem-cones-v1",
        "source": "release/Audit/D9/TheoremConeAudit.lean (Lean.collectAxioms + env enumeration)",
        "modules_total": len(mods),
        "release_modules": sorted(release_modules),
        "missing_imports": missing,
        "counts": meta["counts"],
        "theorems_total": len(theorems),
        "human_theorems_total": len(human),
        "auto_generated_total": len(theorems) - len(human),
        "top_human": human_sorted[:60],
        "top_all": all_sorted[:30],
        "vacuity_screen": [t for t in theorems
                           if t["true_conclusion"] or t["false_hypotheses"] > 0],
        "axiom_anomalies": [t for t in theorems
                            if t["axiom_cone"] not in ("", "propext;Classical.choice;Quot.sound",
                                                       "propext", "propext;Quot.sound")],
        "theorems": theorems,
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print("wrote", OUT)
    print("=== TOP 25 human-authored theorems by per-theorem import cone ===")
    for t in human_sorted[:25]:
        print(f'{t["release_cone"]:4d}rel/{t["cone_size"]:5d}  direct={t["direct_modules"]:3d}/{t["direct_consts"]:4d}  '
              f'h={t["explicit_binders"]}/{t["prop_binders"]}  {t["name"]}')
    print("=== TOP 10 all (incl. generated) ===")
    for t in all_sorted[:10]:
        print(f'{t["release_cone"]:4d}rel/{t["cone_size"]:5d}  direct={t["direct_modules"]:3d}  {t["name"]}')
    return 0


if __name__ == "__main__":
    sys.exit(main())
