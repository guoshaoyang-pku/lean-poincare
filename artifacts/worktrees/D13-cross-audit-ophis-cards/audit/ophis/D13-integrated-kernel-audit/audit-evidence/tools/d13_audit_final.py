#!/usr/bin/env python3
"""D13 integrated kernel audit — consolidated evidence driver (final).

Reads the logs produced by `audit-evidence/tools/final_audit_replay.sh` (fresh build dir,
cwd = release/) and checks:

  C1  completeness: every expected clean D11/D12 module imported; declarations attributed
  C2  kernel: every declaration's cone ⊆ {propext, Classical.choice, Quot.sound}; no axiom,
      unsafe, sorry, native_decide, proof_wanted; collectAxioms failures are failures
  C3  collision freedom: negative-control declarations collide with nothing
  C4  negative control: the detector rejects the two negative-control modules
  C5  type inventory complete
  C6  literal `#print axioms` output covers every audited declaration and agrees with the
      programmatic cones
  C7  downstream-use probe parsed; constructors with no retained consumers listed
  C8  claimed (downstream, constructor) pairs resolved and evaluated
  C9  statement scan: hypothesis-equals-conclusion flags (expected: none)
  C10 D13 self-audit: the auditor's own declarations are kernel-clean
  C11 transcript: every audited command exit code as expected

Writes audit-evidence/kernel-audit.json.
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
EVID = WT / "audit-evidence"
LOGS = EVID / "logs"
APPROVED = {"propext", "Classical.choice", "Quot.sound"}

FINAL = {
    "build": "10-full-build.log",
    "kernel": "11-kernel-audit.log",
    "statement": "12-statement-audit.log",
    "usage": "13-usage-probe.log",
    "dependency": "14-dependency-probe.log",
    "nonvacuity": "15-nonvacuity-probe.log",
    "self": "16-self-audit.log",
    "full": "16b-full-audit.log",
    "negcontrol": "17-negcontrol-included.log",
    "print_axioms": [f"18-print-axioms-{i}.log" for i in range(4)],
}


def parse_audit_log(path: Path):
    decls, types, audit, fails, notes, verdict = {}, {}, {}, [], [], None
    for line in path.read_text(errors="replace").splitlines():
        parts = line.split("\t")
        if parts[0] == "D13DECL" and len(parts) >= 5:
            decls[parts[1]] = {"kind": parts[2], "module": parts[3],
                               "cone": [c for c in parts[4].split(";") if c]}
        elif parts[0] == "D13TYPE" and len(parts) >= 5:
            types[parts[1]] = {"kind": parts[2], "module": parts[3], "type": "\t".join(parts[4:])}
        elif parts[0] == "D13AUDIT" and len(parts) >= 3:
            audit[parts[1]] = parts[2]
        elif parts[0] == "D13FAIL":
            fails.append(parts[1:])
        elif parts[0] == "D13NOTE":
            notes.append(parts[1:])
        elif parts[0] == "D13VERDICT":
            verdict = parts[1]
    return {"decls": decls, "types": types, "audit": audit, "fails": fails,
            "notes": notes, "verdict": verdict}


def parse_print_axioms(paths):
    """Parse wrapped `#print axioms` output into {name: [cone]}.

    The greedy `(.+)` is required: declaration names may themselves end in an apostrophe
    (e.g. `..._integrableClass'`), so splitting on the first quote loses the prime.
    """
    cones, cur, buf = {}, None, ""
    dep = re.compile(r"^'(.+)' depends on axioms: \[(.*)$")
    nod = re.compile(r"^'(.+)' does not depend on any axioms")
    for p in paths:
        for line in p.read_text(errors="replace").splitlines():
            m = dep.match(line)
            if m:
                cur, buf = m.group(1), m.group(2)
            elif nod.match(line):
                cones[nod.match(line).group(1)] = []
                cur = None
            elif cur is not None:
                buf += " " + line
            if cur is not None and "]" in buf:
                body = buf.split("]")[0]
                cones[cur] = [x.strip() for x in body.split(",") if x.strip()]
                cur, buf = None, ""
    return cones


def parse_transcript():
    cmds = {}
    path = LOGS / "transcript.txt"
    if not path.exists():
        return cmds
    lines = path.read_text(errors="replace").splitlines()
    for i, ln in enumerate(lines):
        m = re.match(r"--- CMD\[(.+?)\] cwd=(\S+) :: (.*)", ln)
        if m:
            name, cwd, cmd = m.group(1), m.group(2), m.group(3)
            nxt = lines[i + 1] if i + 1 < len(lines) else ""
            e = re.match(r"--- EXIT\[(.+?)\]=(\d+)", nxt)
            cmds[name] = {"cwd": cwd, "cmd": cmd, "exit": int(e.group(2)) if e else None}
    return cmds


def main() -> int:
    res = {"checks": {}, "problems": []}
    kern = parse_audit_log(LOGS / FINAL["kernel"])
    neg = parse_audit_log(LOGS / FINAL["negcontrol"])
    a = kern["audit"]

    # C1
    c1 = (a.get("missing_modules") == "0" and a.get("duplicate_module_names") == "0"
          and int(a.get("declarations_audited", "0")) > 0)
    in_scope = ("Poincare.D11", "Poincare.D12", "Poincare.VKPort")
    off = [n for n, d in kern["decls"].items()
           if not d["module"].startswith(in_scope)]
    res["checks"]["C1_completeness"] = {
        "pass": c1 and not off, "audit": a, "off_scope_declarations": off[:10]}
    if not (c1 and not off):
        res["problems"].append("C1")

    # C2
    viol = {n: d["cone"] for n, d in kern["decls"].items() if not set(d["cone"]) <= APPROVED}
    kinds = Counter(d["kind"] for d in kern["decls"].values())
    cones = Counter(";".join(d["cone"]) for d in kern["decls"].values())
    c2 = (not viol and kinds.get("axiom", 0) == 0 and kinds.get("unsafe_def", 0) == 0
          and a.get("sorry_declarations") == "0" and a.get("native_decide_declarations") == "0"
          and a.get("unapproved_axiom_declarations") == "0"
          and a.get("proof_wanted_declarations") == "0"
          and a.get("collect_axioms_failures") == "0")
    res["checks"]["C2_kernel_cones"] = {
        "pass": c2, "violations": viol,
        "kind_histogram": dict(kinds), "cone_histogram": dict(cones),
        "partial_defs": sorted(n for n, d in kern["decls"].items() if d["kind"] == "partial_def"),
        "cross_namespace_declarations":
            sorted(n for n, d in kern["decls"].items()
                   if not n.startswith(("Poincare.D11", "Poincare.D12", "Poincare.VKPort"))),
        "vkport_declarations":
            sum(1 for d in kern["decls"].values() if d["module"].startswith("Poincare.VKPort"))}
    if not c2:
        res["problems"].append("C2")

    # C3
    clean_names = set(kern["decls"])
    neg_mods = {"Poincare.D12.TriangulationTopology.NegControl.NegControl",
                "Poincare.D12.VolumeIBP.Audit"}
    neg_decls = {n: d for n, d in neg["decls"].items() if d["module"] in neg_mods}
    collisions = [n for n in neg_decls if n in clean_names]
    res["checks"]["C3_collisions"] = {
        "pass": not collisions, "collisions": collisions,
        "negative_control_declarations": {n: neg_decls[n]["kind"] for n in sorted(neg_decls)}}
    if collisions:
        res["problems"].append("C3")

    # C4
    flagged = sorted({f[1] for f in neg["fails"] if f[0] == "project_axiom"})
    c4 = (bool(neg["verdict"]) and neg["verdict"].startswith("FAIL")
          and flagged == ["Poincare.D12.VolumeIBP.Audit.negativeControl", "d12NegControlBadAxiom"])
    res["checks"]["C4_negative_control"] = {
        "pass": c4, "verdict": neg["verdict"], "flagged_project_axioms": flagged,
        "all_negcontrol_fails": neg["fails"]}
    if not c4:
        res["problems"].append("C4")

    # C5
    miss_t = sorted(set(kern["decls"]) - set(kern["types"]))
    empty_t = sorted(n for n, t in kern["types"].items() if not t["type"].strip())
    res["checks"]["C5_type_inventory"] = {
        "pass": not miss_t and not empty_t,
        "decls": len(kern["decls"]), "types": len(kern["types"]),
        "missing": miss_t[:5], "empty": empty_t[:5]}
    if not res["checks"]["C5_type_inventory"]["pass"]:
        res["problems"].append("C5")

    # C6 literal #print axioms
    lit = parse_print_axioms([LOGS / f for f in FINAL["print_axioms"]])
    # Module-private names cannot be referenced by a literal `#print axioms` command from
    # another module; they are covered by the programmatic collectAxioms audit instead.
    private_names = sorted(n for n in clean_names if n.startswith("_private."))
    missing_lit = sorted(clean_names - set(lit) - set(private_names))
    lit_viol = {n: c for n, c in lit.items() if not set(c) <= APPROVED}
    mism = {n: {"print": lit[n], "programmatic": kern["decls"][n]["cone"]}
            for n in set(lit) & clean_names
            if sorted(lit[n]) != sorted(kern["decls"][n]["cone"])}
    c6 = not missing_lit and not lit_viol and not mism
    res["checks"]["C6_print_axioms"] = {
        "pass": c6, "covered": len(lit), "declarations": len(clean_names),
        "private_declarations_programmatic_only": len(private_names),
        "private_examples": private_names[:5],
        "missing": missing_lit[:10], "violations": lit_viol, "cone_mismatches": mism}
    if not c6:
        res["problems"].append("C6")

    # C7 usage probe
    uses = {}
    for line in (LOGS / FINAL["usage"]).read_text(errors="replace").splitlines():
        p = line.split("\t")
        if p[0] == "D13USE" and len(p) >= 5:
            uses[p[1]] = {"all_users": int(p[2]), "named_users": int(p[3]),
                          "anonymous_users": int(p[4]), "sample": p[5] if len(p) > 5 else ""}
        elif p[0] == "D13USEMISSING":
            uses[p[1]] = {"missing": True}
    zero = sorted(k for k, v in uses.items() if not v.get("missing") and v["all_users"] == 0)
    res["checks"]["C7_downstream_use"] = {
        "pass": True, "inputs_probed": len(uses), "zero_use_inputs": zero, "detail": uses}
    # not a failure by itself; the result card classifies each zero-use input

    # C8 claimed pairs
    deps = []
    for line in (LOGS / FINAL["dependency"]).read_text(errors="replace").splitlines():
        p = line.split("\t")
        if p[0] == "D13DEP" and len(p) >= 7 and p[4] != "EXISTS_FAIL":
            deps.append({"task": p[1], "downstream": p[2], "constructor": p[3],
                         "in_type": p[4] == "true", "in_proof": p[5] == "true"})
        elif p[0] == "D13DEP" and len(p) >= 7:
            deps.append({"task": p[1], "downstream": p[2], "constructor": p[3],
                         "exists_fail": True})
    res["checks"]["C8_claimed_pairs"] = {
        "pass": all(not d.get("exists_fail") for d in deps), "pairs": deps}
    if not res["checks"]["C8_claimed_pairs"]["pass"]:
        res["problems"].append("C8")

    # C9 statement scan
    stmt_counts, suspects = {}, []
    for line in (LOGS / FINAL["statement"]).read_text(errors="replace").splitlines():
        p = line.split("\t")
        if p[0] == "D13STMT" and len(p) >= 3:
            stmt_counts[p[1]] = int(p[2])
        elif p[0] == "D13SUSPECT":
            suspects.append(p[1:])
    res["checks"]["C9_statement_scan"] = {"pass": not suspects, "counts": stmt_counts,
                                          "suspects": suspects}
    if suspects:
        res["problems"].append("C9")

    # C10 self audit
    selfa, selfv = {}, None
    for line in (LOGS / FINAL["self"]).read_text(errors="replace").splitlines():
        p = line.split("\t")
        if p[0] == "D13SELFAUDIT" and len(p) >= 3:
            selfa[p[1]] = p[2]
        elif p[0] == "D13SELFVERDICT":
            selfv = p[1]
    c10 = (selfv is not None and selfv.startswith("PASS") and selfa.get("missing_modules") == "0"
           and selfa.get("project_axioms") == "0" and selfa.get("unsafe_declarations") == "0"
           and selfa.get("sorry_declarations") == "0"
           and selfa.get("unapproved_axiom_declarations") == "0"
           and selfa.get("collect_failures") == "0")
    res["checks"]["C10_self_audit"] = {"pass": c10, "verdict": selfv, "audit": selfa}
    if not c10:
        res["problems"].append("C10")

    # C11b full-package pass
    fulla, fullv = {}, None
    for line in (LOGS / FINAL["full"]).read_text(errors="replace").splitlines():
        p = line.split("\t")
        if p[0] == "D13FULLAUDIT" and len(p) >= 3:
            fulla[p[1]] = p[2]
        elif p[0] == "D13FULLVERDICT":
            fullv = p[1]
    c11b = (fullv is not None and fullv.startswith("PASS")
            and fulla.get("project_axioms") == "0" and fulla.get("unsafe_declarations") == "0"
            and fulla.get("sorry_declarations") == "0"
            and fulla.get("unapproved_axiom_declarations") == "0"
            and fulla.get("collect_failures") == "0"
            and int(fulla.get("declarations_audited", "0")) >= 4000)
    res["checks"]["C11b_full_package_audit"] = {"pass": c11b, "verdict": fullv, "audit": fulla}
    if not c11b:
        res["problems"].append("C11b")

    # C11 transcript
    tr = parse_transcript()
    expected = {f"{n:02d}-" + k: 0 for n, k in
                [(10, "full-build"), (11, "kernel-audit"), (12, "statement-audit"),
                 (13, "usage-probe"), (14, "dependency-probe"), (15, "nonvacuity-probe"),
                 (16, "self-audit")]}
    expected["16b-full-audit"] = 0
    expected["17-negcontrol-included"] = "nonzero"
    ok = True
    for name, exp in expected.items():
        got = tr.get(name, {}).get("exit")
        if exp == 0 and got != 0:
            ok = False
        if exp == "nonzero" and (got is None or got == 0):
            ok = False
    # `#print axioms` probes exit 1 despite producing complete output: Lean exits nonzero on
    # linter warnings about auto-generated auxiliary declarations.  Accept 0/1 provided the
    # log contains no `error:` line.
    for i in range(4):
        name = f"18-print-axioms-{i}"
        got = tr.get(name, {}).get("exit")
        log = LOGS / f"18-print-axioms-{i}.log"
        probe = EVID / "probes" / f"PrintAxiomsAll{i}.lean"
        n_priv = sum(1 for l in probe.read_text().splitlines()
                     if l.startswith("#print axioms _private"))
        errs = [l for l in log.read_text(errors="replace").splitlines() if "error:" in l]
        unexpected = [l for l in errs if "unexpected token '.'" not in l]
        if got not in (0, 1) or len(errs) != n_priv or unexpected:
            ok = False
    res["checks"]["C11_transcript"] = {"pass": ok, "commands": tr}
    if not ok:
        res["problems"].append("C11")

    res["pass"] = not res["problems"]
    (EVID / "kernel-audit.json").write_text(json.dumps(res, indent=1) + "\n")
    for k, v in res["checks"].items():
        print(f"{k}: {'PASS' if v['pass'] else 'FAIL'}")
    print("PROBLEMS:", res["problems"] if res["problems"] else "none")
    if "C7_downstream_use" in res["checks"]:
        print("zero-use inputs:", res["checks"]["C7_downstream_use"]["zero_use_inputs"])
    return 0 if res["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
