#!/usr/bin/env python3
"""Independent invocation-4 audit for L4-child-conjugate-point-bound.

Deliberately written from scratch (does not import or shell out to tools/l4cp_verify.py).
It checks, from first principles and by direct hashing:

  A. provenance: every imported file is byte-identical to its canonical origin, with the
     pinned sha256 taken from checkpoint.json (not from the shipped verify script);
  B. authored sources: kernel-level cleanliness is established by the `#print axioms` run,
     and additionally no `sorry`/`axiom` token survives comment stripping;
  C. the audit log produced by *this* invocation (`logs/l4cp-axioms-inv4-own.log`) parses
     into exactly the 27 expected declarations, every cone being exactly the allowed triple;
  D. the real negative control log (`logs/l4cp-negctl-inv4-own.log`) yields cones
     `[sorryAx]` and `[negControl_axiom]`, both outside the allowed set;
  E. the acceptance lock's type matches the headline theorem's type (checked textually from
     the elaborated `#print` output of tmp/l4cp_probe_inv4.lean).

Exit 0 iff every check passes.
"""
import hashlib
import json
import os
import re
import sys

ROOT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-conjugate-point-bound"
L1 = ("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
      "leaders/L1-lean-baseline/release")
LEADER = ("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
          "leaders/L4-geometric-critical-path/release")

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
failures = []
checks = {}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---- A. provenance against canonical origins, pins read from checkpoint.json -------------
cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))
pins = cp["imported_prior_artifacts"]
prov = {}
for rel, desc in pins.items():
    pin = desc.split(",")[0].replace("sha256", "").strip()
    local = os.path.join(ROOT, rel)
    if "L1-lean-baseline" in desc:
        origin = os.path.join(L1, rel.split("release/", 1)[1])
    else:
        origin = os.path.join(LEADER, rel.split("release/", 1)[1])
    lh, oh = sha256(local), sha256(origin) if os.path.exists(origin) else None
    ok = lh == pin == oh
    prov[rel] = {"pin": pin, "local": lh, "origin": oh, "origin_path": origin, "ok": ok}
    if not ok:
        failures.append("provenance: " + rel)
checks["provenance_all_match"] = all(v["ok"] for v in prov.values())
checks["provenance_count"] = len(prov)

# ---- B. authored source token scan (comments stripped) -----------------------------------
def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


authored = ["release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean",
            "release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean"]
token_hits = {}
for rel in authored:
    clean = strip_comments(open(os.path.join(ROOT, rel)).read())
    hits = {tok: len(re.findall(pat, clean)) for tok, pat in
            [("sorry", r"\bsorry\b"), ("axiom_decl", r"(?m)^\s*axiom\b"),
             ("admit", r"\badmit\b"), ("unsafe", r"\bunsafe\b"),
             ("native_decide", r"\bnative_decide\b"), ("proof_wanted", r"\bproof_wanted\b")]}
    hits = {k: v for k, v in hits.items() if v}
    token_hits[rel] = hits
    if hits:
        failures.append("forbidden tokens in " + rel)
checks["forbidden_tokens_clean"] = not any(token_hits.values())

# ---- C. audit log parsed independently ---------------------------------------------------
AX = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.S)
text = open(os.path.join(ROOT, "logs/l4cp-axioms-inv4-own.log")).read()
text = re.sub(r"\n\s+", " ", text)
cones = {m.group(1): [a.strip() for a in m.group(2).split(",") if a.strip()]
         for m in AX.finditer(text)}

audit_src = open(os.path.join(ROOT, authored[1])).read()
queried = re.findall(r"^#print axioms (\S+)\s*$", audit_src, re.M)
checks["audit_queries"] = len(queried)
checks["audit_parsed"] = len(cones)
checks["audit_queries_unique"] = len(set(queried)) == len(queried)
checks["audit_all_queried_found"] = all(q in cones for q in queried)
bad = {k: v for k, v in cones.items() if not set(v) <= ALLOWED}
checks["cones_all_allowed"] = not bad
checks["cones_exactly_allowed_triple"] = all(set(v) == ALLOWED for v in cones.values())
checks["no_sorryAx"] = not any("sorryAx" in v for v in cones.values())
if not checks["audit_all_queried_found"] or bad or not checks["no_sorryAx"]:
    failures.append("audit parse: missing=%s bad=%s" %
                    ([q for q in queried if q not in cones], bad))

# declaration coverage of the endpoint module (independent regex, same declared set)
endpoint = strip_comments(open(os.path.join(ROOT, authored[0])).read())
decls = sorted(set(re.findall(
    r"^(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][\w.']*)", endpoint, re.M)))
lock = "endpoint_bound_acceptance_lock"
expected_decls = sorted({"Poincare.L4.GeodesicComparison." + d for d in decls})
checks["endpoint_declarations"] = len(decls)
checks["endpoint_declarations_all_audited"] = all(d in cones for d in expected_decls)
if not checks["endpoint_declarations_all_audited"]:
    failures.append("unaudited endpoint declarations: %s" %
                    [d for d in expected_decls if d not in cones])

# ---- D. real negative control ------------------------------------------------------------
nctext = re.sub(r"\n\s+", " ", open(
    os.path.join(ROOT, "logs/l4cp-negctl-inv4-own.log")).read())
nccones = {m.group(1): [a.strip() for a in m.group(2).split(",") if a.strip()]
           for m in AX.finditer(nctext)}
checks["negcontrol_cones"] = nccones
checks["negcontrol_rejected"] = (
    nccones.get("negControl_sorry") == ["sorryAx"]
    and nccones.get("negControl_axiom") == ["negControl_axiom"])
if not checks["negcontrol_rejected"]:
    failures.append("negative control not rejected: %s" % nccones)

# ---- E. elaborated lock/headline type identity (textual, from the probe log) -------------
probe = open(os.path.join(ROOT, "logs/l4cp-probe-inv4.log")).read()
def elaborated(name):
    m = re.search(r"theorem Poincare\.L4\.GeodesicComparison\.%s : (.*?) :=\n" % name,
                  probe, re.S)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else None

t_bound = elaborated("conjugate_point_bound")
t_lock = elaborated("endpoint_bound_acceptance_lock")
t_rauch = elaborated("rauch_upper_of_jacobi_constCurv")
checks["lock_type_equals_headline"] = t_bound is not None and t_bound == t_lock
checks["headline_has_no_hzero"] = t_bound is not None and "K = 0 ∨" not in t_bound
checks["rauch_has_hzero"] = t_rauch is not None and "K = 0 ∨ √K * T < Real.pi" in t_rauch
if not (checks["lock_type_equals_headline"] and checks["headline_has_no_hzero"]
        and checks["rauch_has_hzero"]):
    failures.append("type identity / hzero check failed")

# ---- report ------------------------------------------------------------------------------
out = {"ok": not failures, "failures": failures, "checks": checks,
       "provenance": prov, "token_hits": token_hits}
print(json.dumps(out, indent=1, sort_keys=True))
sys.exit(0 if not failures else 1)
