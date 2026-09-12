#!/usr/bin/env python3
"""D9 independent gate 3: per-theorem import cones from the auditor's census.

Consumes `Audit/D9/logs/d9b/census.raw` (D9BTHM/D9BCONST lines from IndepCensus.lean)
and a freshly parsed module import graph (release + mathlib + toolchain + deps).

Import cone of a theorem = union of the transitive import closures of the modules that
own the constants used in its type and proof term (union over all directly used
constants).  Because Mathlib is one saturated pool, the raw measure has a large tie
group; we additionally record the *release cone* (number of release modules in the
union) and the direct module/const counts, and rank with a deterministic total order.

Outputs: release/Audit/D9/logs/d9b/indep_cones.json (+ stdout summary).
"""
import json
import os
import re
import sys
from collections import defaultdict

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
OUTDIR = os.path.join(RELEASE, "Audit", "D9", "logs", "d9b")
ELAN = "/data/home/guoshaoyang/workdir/lean_poincare/elan"
TOOLCHAIN = os.path.join(ELAN, "toolchains", "leanprover--lean4---v4.34.0-rc2", "src", "lean")
PKGS = os.path.join(RELEASE, ".lake", "packages")
ROOTS = [TOOLCHAIN, os.path.join(TOOLCHAIN, "lake")]
for p in sorted(os.listdir(PKGS)) if os.path.isdir(PKGS) else []:
    ROOTS.append(os.path.join(PKGS, p))
ROOTS.append(RELEASE)

IMPORT_RE = re.compile(r"^[ \t]*(?:public[ \t]+|private[ \t]+|protected[ \t]+)?import[ \t]+"
                       r"([A-Za-z0-9_.\u00ab\u00bb]+)[ \t]*$", re.M)


def mask_comments(text):
    out = []
    i, n = 0, len(text)
    in_block = 0
    in_str = False
    while i < n:
        c = text[i]
        if in_block:
            if text.startswith("-/", i):
                in_block -= 1
                i += 2
                continue
            if text.startswith("/-", i):
                in_block += 1
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
        elif in_str:
            if c == "\\":
                out.append("  ")
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " ")
            i += 1
        else:
            if text.startswith("/-", i):
                in_block = 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                j = n if j == -1 else j
                out.append(" " * (j - i))
                i = j
                continue
            if c == '"':
                in_str = True
                out.append(" ")
                i += 1
                continue
            out.append(c)
            i += 1
    return "".join(out)


def discover():
    mods = {}
    for r in ROOTS:
        if not os.path.isdir(r):
            continue
        for dp, dn, fn in os.walk(r):
            dn[:] = [d for d in dn if d not in (".lake", ".git")]
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, r)[:-5].replace(os.sep, ".")
                mods.setdefault(rel, p)
    # release sources take precedence
    release_mods = set()
    for dp, dn, fn in os.walk(RELEASE):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for f in fn:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, RELEASE)[:-5].replace(os.sep, ".")
                mods[rel] = p
                release_mods.add(rel)
    return mods, release_mods


def main():
    mods, release_mods = discover()
    deps = {}
    missing = set()
    for m, p in mods.items():
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            deps[m] = set()
            continue
        d = set(IMPORT_RE.findall(mask_comments(text)))
        missing |= {x for x in d if x not in mods}
        deps[m] = d
    # memoized transitive closure as int bitmask
    idx = {m: i for i, m in enumerate(sorted(mods))}
    memo = {}
    IN_PROGRESS = set()

    def closure(m):
        if m in memo:
            return memo[m]
        if m in IN_PROGRESS:  # import cycle: ignore back edge
            return 0
        IN_PROGRESS.add(m)
        b = 0
        for x in deps.get(m, ()):  # direct imports only; recursion adds their closure
            if x in mods:
                b |= closure(x) | (1 << idx[x])
        IN_PROGRESS.discard(m)
        memo[m] = b
        return b

    for m in mods:
        closure(m)
    release_ids = {idx[m] for m in release_mods if m in idx}
    release_mask = 0
    for i in release_ids:
        release_mask |= 1 << i

    # --- census (statement/proof) ---
    census_path = os.path.join(OUTDIR, "census.raw")
    modcensus_path = os.path.join(OUTDIR, "census_modules.raw")
    thms = []
    consts = []
    for line in open(census_path, encoding="utf-8", errors="replace"):
        if line.startswith("D9BTHM\t"):
            p = line.rstrip("\n").split("\t")
            if len(p) < 17:
                continue
            thms.append({
                "name": p[1], "module": p[2], "used": int(p[3]), "direct_mods": int(p[4]),
                "hyps": int(p[5]), "exp_hyps": int(p[6]), "prop_hyps": int(p[7]),
                "false_hyps": int(p[8]), "true_concl": p[9] == "true",
                "hyp_eq_concl": p[10] == "true", "proof_head": p[11], "proof_nodes": int(p[12]),
                "axioms": p[13].split(";") if p[13] else [], "d9": p[14] == "1",
                "hyp_types": p[15].split(" ;; ") if len(p) > 15 else [],
                "conclusion": p[16] if len(p) > 16 else "",
            })
        elif line.startswith("D9BCONST\t"):
            p = line.rstrip("\n").split("\t")
            consts.append({"name": p[1], "module": p[2], "kind": p[3], "safety": p[4],
                           "axioms": p[5].split(";") if p[5] else [], "d9": p[6] == "1"})
    # --- module census (direct module lists, authoritative for cones) ---
    mods_by_name = {}
    for line in open(modcensus_path, encoding="utf-8", errors="replace"):
        if line.startswith("D9BMOD\t"):
            p = line.rstrip("\n").split("\t")
            if len(p) < 6:
                continue
            mods_by_name[p[1]] = p[5].split()
    for t in thms:
        t["dom_list"] = mods_by_name.get(t["name"], [])
    for t in thms:
        b = 0
        for m in t["dom_list"]:
            if m in mods:
                b |= closure(m) | (1 << idx[m])
        t["cone"] = b.bit_count()
        t["release_cone"] = (b & release_mask).bit_count()
        t["owner_is_audit"] = t["module"].startswith("Audit.")
        t["owner_is_d9"] = t["module"].startswith("Audit.D9.")
        ph = t["proof_head"]
        nm = t["name"]
        t["auto_generated"] = (
            ph.endswith("proj")                       # structure field projection
            or ".match_" in nm or nm.startswith("_private.")
            or ".eq_" in nm or "sizeOf_spec" in nm or nm.endswith("_sizeOf")
            or "noConfusion" in nm or "below" in nm.split(".")[-1]
            or "brecOn" in nm or "recOn" in nm)
        t["authored"] = not t["auto_generated"]
        t["field_projection"] = ph.endswith("proj")

    def key_literal(t):
        return (-t["cone"], -t["direct_mods"], -t["used"], t["name"])
    def key_substantive(t):
        return (-t["release_cone"], -t["cone"], -t["used"], t["name"])
    def key_authored(t):
        return (-t["release_cone"], -t["cone"], -t["used"], t["name"])

    lit = sorted(thms, key=key_literal)
    sub = sorted([t for t in thms if not t["owner_is_audit"]], key=key_substantive)
    auth = sorted([t for t in thms if not t["owner_is_audit"] and t["authored"]],
                  key=key_authored)
    top_lit = lit[:10]
    top_sub = sub[:10]
    top_auth = auth[:10]
    max_cone = lit[0]["cone"] if lit else 0
    tie = [t for t in thms if t["cone"] == max_cone]

    out = {
        "schema": "d9-adversarial-audit/indep-cones-v1",
        "modules_total": len(mods),
        "release_modules": len(release_mods),
        "missing_imports": sorted(missing),
        "theorems": len(thms),
        "constants": len(consts),
        "max_cone": max_cone,
        "max_cone_tie_size": len(tie),
        "top10_literal": [{k: t[k] for k in
            ["name", "module", "cone", "release_cone", "direct_mods", "used", "hyps",
             "exp_hyps", "prop_hyps", "false_hyps", "true_concl", "hyp_eq_concl",
             "proof_head", "proof_nodes", "axioms", "d9"]} for t in top_lit],
        "top10_substantive": [{k: t[k] for k in
            ["name", "module", "cone", "release_cone", "direct_mods", "used", "hyps",
             "exp_hyps", "prop_hyps", "false_hyps", "true_concl", "hyp_eq_concl",
             "proof_head", "proof_nodes", "axioms", "d9", "auto_generated"]} for t in top_sub],
        "top10_authored_nonaudit": [{k: t[k] for k in
            ["name", "module", "cone", "release_cone", "direct_mods", "used", "hyps",
             "exp_hyps", "prop_hyps", "false_hyps", "true_concl", "hyp_eq_concl",
             "proof_head", "proof_nodes", "axioms", "d9", "auto_generated"]} for t in top_auth],
        "field_projection_theorems": [t["name"] for t in thms if t["field_projection"]],
        "auto_generated_theorems": [t["name"] for t in thms if t["auto_generated"]],
        "max_cone_tie_group": sorted([t["name"] for t in tie]),
        "release_wide_flags": {
            "true_conclusion": [t["name"] for t in thms if t["true_concl"]],
            "false_hypothesis": [t["name"] for t in thms if t["false_hyps"] > 0],
            "hyp_eq_conclusion": [t["name"] for t in thms if t["hyp_eq_concl"]],
            "proof_head_is_hypothesis": [t["name"] for t in thms
                                         if t["proof_head"].startswith("hyp:")],
            "proof_head_is_proj": [t["name"] for t in thms if t["proof_head"] == "proj"],
            "tiny_proof_le_5_nodes": [t["name"] for t in thms if t["proof_nodes"] <= 5],
        },
        "unapproved_axiom_theorems": [
            {"name": t["name"], "axioms": t["axioms"]} for t in thms
            if any(a not in ("propext", "Classical.choice", "Quot.sound") for a in t["axioms"])],
        "unapproved_axiom_constants": [
            {"name": c["name"], "kind": c["kind"], "axioms": c["axioms"]} for c in consts
            if any(a not in ("propext", "Classical.choice", "Quot.sound") for a in c["axioms"])],
        "kinds": {},
        "all_theorems": [{k: t[k] for k in
            ["name", "module", "cone", "release_cone", "direct_mods", "used", "hyps",
             "exp_hyps", "prop_hyps", "false_hyps", "true_concl", "hyp_eq_concl",
             "proof_head", "proof_nodes", "axioms", "d9"]} for t in lit],
    }
    for c in consts:
        k = c["kind"] + (":" + c["safety"] if c["kind"] == "def" else "")
        out["kinds"][k] = out["kinds"].get(k, 0) + 1
    with open(os.path.join(OUTDIR, "indep_cones.json"), "w") as fh:
        json.dump(out, fh, indent=1)

    print("modules:", len(mods), "release:", len(release_mods), "missing:", len(missing))
    print("theorems:", len(thms), "constants:", len(consts))
    print("max cone:", max_cone, "tie size:", len(tie))
    print("unapproved axiom theorems:", len(out["unapproved_axiom_theorems"]))
    print("unapproved axiom constants:", len(out["unapproved_axiom_constants"]))
    print("\n--- top10 literal ---")
    for t in top_lit:
        print(f"  {t['cone']:6d}/{t['release_cone']:3d} dmods={t['direct_mods']:3d} used={t['used']:4d} "
              f"hyps={t['hyps']}/{t['exp_hyps']} {t['name']}")
    print("\n--- top10 substantive (non-Audit owners) ---")
    for t in top_sub:
        print(f"  {t['cone']:6d}/{t['release_cone']:3d} dmods={t['direct_mods']:3d} used={t['used']:4d} "
              f"hyps={t['hyps']}/{t['exp_hyps']} gen={t['auto_generated']} {t['name']}")
    print("\n--- top10 authored non-Audit (auto-generated excluded) ---")
    for t in top_auth:
        print(f"  {t['cone']:6d}/{t['release_cone']:3d} dmods={t['direct_mods']:3d} used={t['used']:4d} "
              f"hyps={t['hyps']}/{t['exp_hyps']} {t['name']}")
    print("\nrelease-wide flags:")
    for k, v in out["release_wide_flags"].items():
        print(f"  {k}: {len(v)}")
        for n in v[:15]:
            print("     ", n)
    return 0


if __name__ == "__main__":
    sys.exit(main())
