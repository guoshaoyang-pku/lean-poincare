#!/usr/bin/env python3
"""Round-9 (same invocation) updater: kernel assumption-as-conclusion screens.

Adds the round-9 evidence to the result-card JSON and MD:
  * `taut_screen_round9.json`     — declared-set screen (raw criterion, shows the
    over-firing on data/type declarations),
  * `taut_screen_full_round9.json` — full-namespace Prop-gated screen over the
    1104 constants of the seven packages, with the positive control.
"""
import datetime
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES_JSON = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
RES_MD = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.md")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def h(name):
    return sha(os.path.join(HERE, name))


d = json.load(open(RES_JSON))
r9 = json.load(open(os.path.join(HERE, "taut_screen_round9.json")))
r9f = json.load(open(os.path.join(HERE, "taut_screen_full_round9.json")))
now = datetime.datetime.now().isoformat(timespec="seconds")

d["generated_at"] = now
d["elapsed_hours"] = 1.15
d["cumulative_task_hours"] = 4.1
d["round9_artifacts"] = {
    "gen_taut_screen.py": h("gen_taut_screen.py"),
    "run_taut_screen.sh": h("run_taut_screen.sh"),
    "taut_screen_summary.py": h("taut_screen_summary.py"),
    "taut_screen_round9.json": h("taut_screen_round9.json"),
    "gen_taut_full.py": h("gen_taut_full.py"),
    "run_taut_full.sh": h("run_taut_full.sh"),
    "taut_full_summary.py": h("taut_full_summary.py"),
    "taut_screen_full_round9.json": h("taut_screen_full_round9.json"),
}
for card in ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
             "D12-semantic-ledger", "D12-comparison-geodesics",
             "D12-geometric-compactness", "D12-surgery-recognition"]:
    d["round9_artifacts"]["pkgs/%s/A3TautScreen.lean" % card] = sha(
        os.path.join(HERE, "pkgs", card, "A3TautScreen.lean"))
    d["round9_artifacts"]["pkgs/%s/A3TautFull.lean" % card] = sha(
        os.path.join(HERE, "pkgs", card, "A3TautFull.lean"))

d["kernel_tautology_screen_round9"] = {
    "motivation": (
        "F18 showed the string-based vacuity screen was blind on signature-form "
        "binders.  This screen replaces string heuristics with a kernel check over "
        "compiled ConstantInfo: a declaration is flagged iff (a) a forall-binder's "
        "type is definitionally equal to the conclusion, (b) the conclusion is "
        "definitionally True, or (c) the proof body is an assumption-like term "
        "(bound variable, or bound variable applied only to bound variables) whose "
        "type is the flagged conclusion binder."),
    "declared_set": {
        "artifact": "audit360/taut_screen_round9.json",
        "sha256": h("taut_screen_round9.json"),
        "scope": "the card-declared audited names (332 declarations + positive control per package)",
        "total_checked_including_controls": r9["total_checked_including_controls"],
        "control_flagged_in_all_packages": r9["control_flagged_in_all_packages"],
        "non_control_flags": len(r9["non_control_flags"]),
        "flag_classification": [
            {"name": f["name"], "kind": f["kernel_kind"], "verdict": f["verdict"]}
            for f in r9["non_control_flags"]],
        "verdict": r9["verdict"],
    },
    "full_namespace_prop_gated": {
        "artifact": "audit360/taut_screen_full_round9.json",
        "sha256": h("taut_screen_full_round9.json"),
        "scope": ("every constant of each package's own `Poincare.D12` namespace — the same "
                  "enumeration as `A3FullAudit` (1103 declarations + the documented "
                  "volume-ibp negative control)"),
        "total_constants_checked": r9f["total_constants_checked"],
        "total_proof_valued": r9f["total_proof_valued"],
        "flags": len(r9f["flags"]),
        "control_flagged_in_all_packages": all(
            e["control_flagged"] for e in r9f["cards"].values()),
        "per_card": {c: {"checked": e["checked_constants"],
                         "proof_valued": e["proof_valued_constants"],
                         "flags": e["flags"], "rc": e["rc"]}
                     for c, e in r9f["cards"].items()},
        "verdict": r9f["verdict"],
    },
}

d["verdict"] = (
    d["verdict"].rstrip() + "  Round 9 (same invocation, new evidence): a kernel-level "
    "assumption-as-conclusion screen now complements the string-based vacuity screen.  On the "
    "332 card-declared names the raw criterion flags only the injected control and five "
    "data/type declarations (result type coinciding with a binder type — the same over-firing "
    "class already classified in round 8).  On the full 1104-constant namespace with the "
    "criterion restricted to Prop-valued conclusions, **zero** declarations are flagged and "
    "the injected control is flagged in all seven packages: no audited theorem assumes its "
    "own conclusion, concludes `True`, or proves its conclusion by an assumption.")

json.dump(d, open(RES_JSON, "w"), indent=1)
print("JSON updated; round9 artifacts:", len(d["round9_artifacts"]))

# ---------------- markdown --------------------------------------------------
text = open(RES_MD).read()
if "## 17. " in text:
    text = text[:text.find("\n## 17. ")]
section = f"""
## 17. Round-9 kernel assumption-as-conclusion screen (new evidence, invocation 7)

The round-7 finding F18 (a string screen blind on signature-form binders) is answered here
with a **kernel-level** replacement that never looks at pretty-printed text.  For every
declaration the screen decomposes the compiled `ConstantInfo` and flags it iff (a) a
forall-binder's type is **definitionally equal** to the final conclusion, (b) the conclusion
is definitionally `True`, or (c) the proof body is an assumption-like term (a bound
variable, or a bound variable applied only to bound variables) whose type is a flagged
conclusion binder.  A positive control `(P : Prop) (h : P) : P := h` is declared in every
screen file and must be flagged.

### 17.1 Declared-set screen (`taut_screen_round9.json`, sha256 `{sha(os.path.join(HERE, 'taut_screen_round9.json'))}`)

`gen_taut_screen.py` / `run_taut_screen.sh` generated and compiled `A3TautScreen.lean` in
all seven packages (rc 0; 339 declarations checked including controls).  The control is
flagged in **7/7** packages with both `hypothesis-eq-conclusion:h` and
`proof-is-hypothesis:h`.  The only non-control flags are five **data/type declarations**
(`ChartPoint`, `VectorField`, `ChartMetric.pullbackMetric`, `heatWeight`, `heatEvolve`),
each flagged because the declared result type is definitionally the same as one of its
argument types — exactly the over-firing class already classified in §16.3; the criteria
say nothing about data definitions.  **No theorem is flagged.**

### 17.2 Full-namespace Prop-gated screen (`taut_screen_full_round9.json`, sha256 `{sha(os.path.join(HERE, 'taut_screen_full_round9.json'))}`)

`gen_taut_full.py` / `run_taut_full.sh` generated and compiled `A3TautFull.lean`, which
enumerates **every constant of the package's own `Poincare.D12` namespace** — the same
environment as `A3FullAudit` — and restricts the criterion to Prop-valued conclusions, where
vacuity is meaningful.  Result across the seven packages: **1104 constants checked, 1061
proof-valued, 0 flags**, control flagged in 7/7, all runs rc 0.  Per package:

| card | constants checked | proof-valued | flags | rc |
|---|---|---|---|---|
""" + "\n".join(
    "| {} | {} | {} | {} | {} |".format(
        c, e["checked_constants"], e["proof_valued_constants"], e["flags"], e["rc"])
    for c, e in r9f["cards"].items()) + f"""

This is the strongest statement the audit can make about the conclusion-assumption failure
mode: **no declaration in the audited namespace has a hypothesis definitionally equal to its
conclusion, concludes `True`, or proves its conclusion by an assumption** — a kernel-checked
complement to the syntactic T1–T11 screen, with its own positive control.
"""
open(RES_MD, "w").write(text.rstrip("\n") + "\n" + section)
print("MD updated; sha256:", sha(RES_MD))
