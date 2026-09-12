#!/usr/bin/env python3
"""D9 post-hoc verification analysis (independent re-derivation).

Reads the *post-hoc verifier's* fresh logs from release/Audit/D9/logs/verify/raw/
(produced by D9Recompile.py, which re-ran `lake env lean` on every authored file,
including the auditor's own IndepCensus/IndepCensusModules/TheoremConeAudit drivers)
and independently:

  1. rebuilds the module import graph and recomputes per-theorem import cones;
  2. re-derives the literal / non-audit / authored top-10 cone rankings and
     compares them against the predecessor audit's indep_cones.json;
  3. screens the theorems for vacuity / definitional triviality, including a
     stricter "definitional alias" screen than the predecessor's;
  4. re-parses #print axioms and compares with the predecessor's map;
  5. cross-checks all 1619 declaration axiom cones against manifest/verified-declarations.json.

Output: release/Audit/D9/logs/verify/analysis.json (+ stdout summary).
"""
import json
import os
import re
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
RELEASE = os.path.join(ROOT, "release")
VR = os.path.join(RELEASE, "Audit", "D9", "logs", "verify")
RAW = os.path.join(VR, "raw")
PREV = os.path.join(RELEASE, "Audit", "D9", "logs", "d9b")
ELAN = os.environ.get("ELAN_HOME", "/data/home/guoshaoyang/workdir/lean_poincare/elan")
TOOLCHAIN = os.path.join(ELAN, "toolchains", "leanprover--lean4---v4.34.0-rc2", "src", "lean")
PKGS = os.path.join(RELEASE, ".lake", "packages")
APPROVED = {"propext", "Classical.choice", "Quot.sound"}

IMPORT_RE = re.compile(r"^[ \t]*(?:public[ \t]+|private[ \t]+|protected[ \t]+)?import[ \t]+"
                       r"([A-Za-z0-9_.\u00ab\u00bb]+)[ \t]*$", re.M)


def mask_comments(text):
    """Blank out Lean comments and string literals (own implementation)."""
    out = []
    i, n = 0, len(text)
    depth = 0
    in_str = False
    while i < n:
        c = text[i]
        if depth:
            if text.startswith("-/", i):
                depth -= 1; i += 2; continue
            if text.startswith("/-", i):
                depth += 1; i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1
        elif in_str:
            if c == "\\":
                out.append("  "); i += 2; continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " "); i += 1
        else:
            if text.startswith("/-", i):
                depth = 1; out.append("  "); i += 2; continue
            if text.startswith("--", i):
                j = text.find("\n", i); j = n if j == -1 else j
                out.append(" " * (j - i)); i = j; continue
            if c == '"':
                in_str = True; out.append(" "); i += 1; continue
            out.append(c); i += 1
    return "".join(out)


def discover_modules():
    mods = {}
    roots = [TOOLCHAIN, os.path.join(TOOLCHAIN, "lake")]
    if os.path.isdir(PKGS):
        roots += [os.path.join(PKGS, p) for p in sorted(os.listdir(PKGS))]
    roots.append(RELEASE)
    for r in roots:
        if not os.path.isdir(r):
            continue
        for dp, dn, fn in os.walk(r):
            dn[:] = [d for d in dn if d not in (".lake", ".git")]
            for f in fn:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    mods.setdefault(os.path.relpath(p, r)[:-5].replace(os.sep, "."), p)
    release_mods = set()
    for dp, dn, fn in os.walk(RELEASE):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for f in fn:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                m = os.path.relpath(p, RELEASE)[:-5].replace(os.sep, ".")
                mods[m] = p
                release_mods.add(m)
    return mods, release_mods


def parse_prefixed(path, prefix):
    for line in open(path, encoding="utf-8", errors="replace"):
        if line.startswith(prefix):
            yield line.rstrip("\n").split("\t")


def main():
    out = {"schema": "d9-adversarial-audit/verify-analysis-v1"}
    cen_log = os.path.join(RAW, "Audit__D9__IndepCensus.lean.log")
    mod_log = os.path.join(RAW, "Audit__D9__IndepCensusModules.lean.log")
    ax_log = os.path.join(RAW, "Audit__D9__IndepPrintAxioms.lean.log")

    thms, consts = {}, {}
    for p in parse_prefixed(cen_log, "D9BTHM\t"):
        if len(p) < 17:
            continue
        thms[p[1]] = {
            "name": p[1], "module": p[2], "used": int(p[3]), "direct_mods": int(p[4]),
            "hyps": int(p[5]), "exp_hyps": int(p[6]), "prop_hyps": int(p[7]),
            "false_hyps": int(p[8]), "true_concl": p[9] == "true",
            "hyp_eq_concl": p[10] == "true", "proof_head": p[11],
            "proof_nodes": int(p[12]), "axioms": [a for a in p[13].split(";") if a],
            "d9": p[14] == "1",
            "hyp_types": p[15].split(" ;; ") if p[15] else [],
            "conclusion": p[16],
        }
    for p in parse_prefixed(cen_log, "D9BCONST\t"):
        consts[p[1]] = {"name": p[1], "module": p[2], "kind": p[3], "safety": p[4],
                        "axioms": [a for a in p[5].split(";") if a], "d9": p[6] == "1"}
    modlist = {}
    for p in parse_prefixed(mod_log, "D9BMOD\t"):
        modlist[p[1]] = p[5].split()

    mods, release_mods = discover_modules()
    deps = {}
    missing = set()
    for m, p in mods.items():
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            deps[m] = set(); continue
        d = set(IMPORT_RE.findall(mask_comments(text)))
        missing |= {x for x in d if x not in mods}
        deps[m] = d
    idx = {m: i for i, m in enumerate(sorted(mods))}
    memo = {}
    stack = set()

    def closure(m):
        if m in memo:
            return memo[m]
        if m in stack:
            return 0
        stack.add(m)
        b = 0
        for x in deps.get(m, ()):
            if x in mods:
                b |= closure(x) | (1 << idx[x])
        stack.discard(m)
        memo[m] = b
        return b

    release_mask = 0
    for m in sorted(release_mods):
        release_mask |= 1 << idx[m]

    for t in thms.values():
        b = 0
        for m in modlist.get(t["name"], []):
            if m in mods:
                b |= closure(m) | (1 << idx[m])
        t["cone"] = b.bit_count()
        t["release_cone"] = (b & release_mask).bit_count()
        t["owner_is_audit"] = t["module"].startswith("Audit.")
        t["owner_is_d9"] = t["module"].startswith("Audit.D9.")
        nm, ph = t["name"], t["proof_head"]
        # predecessor classifier
        t["prev_auto"] = (ph.endswith("proj") or ".match_" in nm or nm.startswith("_private.")
                          or ".eq_" in nm or "sizeOf_spec" in nm or nm.endswith("_sizeOf")
                          or "noConfusion" in nm or "brecOn" in nm or "recOn" in nm)
        # stricter definitional-alias screen (auditor addition): proof term is
        # (lambdas ->) projection / rfl / an applied existing constant with tiny term
        core = ph.split("->")[-1]
        t["core_head"] = core
        t["def_alias"] = (core == "proj" or core in ("const:Eq.refl", "const:Iff.rfl", "const:rfl")
                          or (core.startswith("const:") and t["proof_nodes"] <= 12))
    ts = list(thms.values())
    max_cone = max(t["cone"] for t in ts)
    tie = [t for t in ts if t["cone"] == max_cone]

    key_lit = lambda t: (-t["cone"], -t["direct_mods"], -t["used"], t["name"])
    key_sub = lambda t: (-t["release_cone"], -t["cone"], -t["used"], t["name"])
    lit = sorted(ts, key=key_lit)
    sub = sorted([t for t in ts if not t["owner_is_audit"]], key=key_sub)
    auth = sorted([t for t in ts if not t["owner_is_audit"] and not t["prev_auto"]],
                  key=key_sub)
    out["counts"] = {"theorems": len(ts), "constants": len(consts),
                     "modules": len(mods), "release_modules": len(release_mods),
                     "missing_imports": sorted(missing)}
    out["max_cone"] = max_cone
    out["max_cone_tie_size"] = len(tie)
    out["max_cone_tie_group"] = sorted(t["name"] for t in tie)

    def row(t):
        return {k: t[k] for k in ("name", "module", "cone", "release_cone", "direct_mods",
                                  "used", "hyps", "exp_hyps", "prop_hyps", "false_hyps",
                                  "true_concl", "hyp_eq_concl", "proof_head", "proof_nodes",
                                  "axioms", "prev_auto", "def_alias", "hyp_types",
                                  "conclusion")}

    out["top10_literal"] = [row(t) for t in lit[:10]]
    out["top10_nonaudit"] = [row(t) for t in sub[:10]]
    out["top10_authored_nonaudit"] = [row(t) for t in auth[:10]]

    # ---- comparison with the predecessor audit ----
    prev = json.load(open(os.path.join(PREV, "indep_cones.json")))
    cmp = {}
    for tag, mine, hers in (("literal", out["top10_literal"], prev["top10_literal"]),
                            ("nonaudit", out["top10_nonaudit"], prev["top10_substantive"]),
                            ("authored", out["top10_authored_nonaudit"],
                             prev["top10_authored_nonaudit"])):
        mn = [t["name"] for t in mine]
        hn = [t["name"] for t in hers]
        cmp[tag] = {"same_order": mn == hn, "same_set": set(mn) == set(hn),
                    "mine": mn, "predecessor": hn,
                    "cone_mismatches": [{"name": a["name"], "mine": a["cone"],
                                         "predecessor": b["cone"]}
                                        for a, b in zip(mine, hers) if a["cone"] != b["cone"]]}
    cmp["max_cone"] = {"mine": max_cone, "predecessor": prev["max_cone"]}
    cmp["tie_size"] = {"mine": len(tie), "predecessor": prev["max_cone_tie_size"]}
    cmp["theorem_count"] = {"mine": len(ts), "predecessor": prev["theorems"]}
    cmp["modules"] = {"mine": len(mods), "predecessor": prev["modules_total"]}
    cmp["max_cone_tie_group_equal"] = (sorted(t["name"] for t in tie)
                                       == sorted(prev["max_cone_tie_group"]))
    out["predecessor_comparison"] = cmp

    # ---- vacuity / triviality screens ----
    flags = {
        "true_conclusion": [t["name"] for t in ts if t["true_concl"]],
        "false_hypothesis": [t["name"] for t in ts if t["false_hyps"] > 0],
        "hyp_eq_conclusion": [t["name"] for t in ts if t["hyp_eq_concl"]],
        "prev_auto_generated": [t["name"] for t in ts if t["prev_auto"]],
        "def_alias_strict": [t["name"] for t in ts if t["def_alias"]],
        "def_alias_strict_nonaudit": [t["name"] for t in ts
                                      if t["def_alias"] and not t["owner_is_audit"]],
        "nonempty_decidable_conclusion": [t["name"] for t in ts
                                          if "Nonempty (Decidable" in t["conclusion"]],
        "proof_nodes_le_5": [t["name"] for t in ts if t["proof_nodes"] <= 5],
        "unapproved_axiom_theorems": [t["name"] for t in ts
                                      if any(a not in APPROVED for a in t["axioms"])],
        "unapproved_axiom_constants": [c["name"] for c in consts.values()
                                       if any(a not in APPROVED for a in c["axioms"])],
    }
    flags["def_alias_not_prev"] = sorted(set(flags["def_alias_strict"])
                                         - set(flags["prev_auto_generated"]))
    out["screens"] = {k: {"count": len(v), "names": v if len(v) <= 60 else v[:60]}
                      for k, v in flags.items()}

    # ---- print axioms re-parse (output may be pretty-printer wrapped over lines) ----
    ax = {}
    ax_free = []
    buf = ""
    entries = []
    for raw in open(ax_log, encoding="utf-8", errors="replace"):
        line = raw.rstrip("\n")
        if line.startswith("'"):
            if buf:
                entries.append(buf)
            buf = line
        elif buf:
            buf += " " + line.strip()
    if buf:
        entries.append(buf)
    for entry in entries:
        m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", entry.strip())
        if m:
            ax[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
            continue
        m2 = re.match(r"^'([^']+)' does not depend on any axioms$", entry.strip())
        if m2:
            ax[m2.group(1)] = []
            ax_free.append(m2.group(1))
    prev_ax = json.load(open(os.path.join(PREV, "print_axioms_indep.json")))
    out["print_axioms"] = {
        "declarations": len(ax),
        "axiom_free": sorted(ax_free),
        "unapproved": {n: a for n, a in ax.items()
                       if any(x not in APPROVED for x in a)},
        "map_matches_predecessor": {n: ax[n] for n in sorted(set(ax) & set(prev_ax))
                                    if ax[n] != prev_ax[n]},
        "only_mine": sorted(set(ax) - set(prev_ax)),
        "only_predecessor": sorted(set(prev_ax) - set(ax)),
        "axioms": ax,
    }

    # ---- declaration-level axiom cone vs D6 manifest ----
    vd = json.load(open(os.path.join(ROOT, "manifest/verified-declarations.json")))
    man = {d["name"]: d for d in vd["declarations"]}
    mism = [{"name": n, "mine": consts[n]["axioms"],
             "manifest": [a for a in man[n]["axioms"] if a]}
            for n in sorted(set(man) & set(consts))
            if [a for a in man[n]["axioms"] if a] != consts[n]["axioms"]]
    # NOTE (post-hoc verification self-check, 2026-09-10): the first version of this
    # script compared Counter(labelled kind strings) against Counter(dict(vd["kinds"]))
    # (which counts the dict keys only) and therefore always reported kinds_match=False.
    # The corrected comparison below maps the raw kinds through the same labels as
    # manifest/verified-declarations.json and compares both dicts.
    raw_kinds = Counter(c["kind"] + (":" + c["safety"] if c["kind"] == "def" else "")
                        for c in consts.values())
    label = {"thm": "theorem", "def:safe": "def", "def:partial": "partial_def",
             "def:unsafe": "unsafe_def"}
    census_kinds = {label.get(k, k): v for k, v in raw_kinds.items()}
    out["manifest_conformance"] = {
        "manifest_count": vd["count"], "census_constants": len(consts),
        "missing_from_census": sorted(set(man) - set(consts)),
        "extra_in_census": sorted(set(consts) - set(man)),
        "axiom_cone_mismatches": mism,
        "census_kinds": census_kinds,
        "manifest_kinds": vd["kinds"],
        "kinds_match": census_kinds == vd["kinds"],
        "kinds_match_first_pass_bug": ("first pass compared a Counter of labelled kind "
                                       "strings against Counter(dict(vd['kinds'])) (keys "
                                       "only), so it could not match; fixed before the "
                                       "final analysis re-run"),
    }
    os.makedirs(VR, exist_ok=True)
    with open(os.path.join(VR, "analysis.json"), "w") as fh:
        json.dump(out, fh, indent=1)

    print("theorems", len(ts), "constants", len(consts), "modules", len(mods))
    print("max_cone", max_cone, "tie", len(tie))
    for tag in ("literal", "nonaudit", "authored"):
        c = cmp[tag]
        print(f"top10 {tag}: same_order={c['same_order']} same_set={c['same_set']} "
              f"cone_mismatches={len(c['cone_mismatches'])}")
    for k, v in out["screens"].items():
        print(f"  screen {k}: {v['count']}")
    print("print axioms:", len(ax), "free:", len(ax_free),
          "unapproved:", len(out["print_axioms"]["unapproved"]),
          "map diff:", len(out["print_axioms"]["map_matches_predecessor"]))
    print("manifest:", out["manifest_conformance"]["manifest_count"],
          "mismatches:", len(mism), "missing:", len(out["manifest_conformance"]["missing_from_census"]),
          "extra:", len(out["manifest_conformance"]["extra_in_census"]))
    print("wrote", os.path.join(VR, "analysis.json"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
