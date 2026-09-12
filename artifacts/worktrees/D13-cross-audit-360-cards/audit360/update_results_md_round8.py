#!/usr/bin/env python3
"""Round-8 markdown updater: appends §15 (round 7) and §16 (round 8) to the D13
cross-audit result card and refreshes the header status/elapsed/A3 bullets.

Idempotent: everything from the `## 15.` marker onward is replaced.
"""
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES_MD = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.md")
RES_JSON = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def h(name):
    return sha(os.path.join(HERE, name))[:16]


d = json.load(open(RES_JSON))
r7 = json.load(open(os.path.join(HERE, "round7_summary.json")))
r8 = json.load(open(os.path.join(HERE, "round8_summary.json")))
f18 = json.load(open(os.path.join(HERE, "f18_flag_classification.json")))
cons = json.load(open(os.path.join(HERE, "closure_consumption_round8.json")))
miss = json.load(open(os.path.join(HERE, "missing_cards_recheck_round8.json")))
sc7 = json.load(open(os.path.join(HERE, "selfcontrol_round7.json")))
cc8 = json.load(open(os.path.join(HERE, "canonical_crosscheck_round8.json")))

text = open(RES_MD).read()

# ---- header refresh --------------------------------------------------------
old_status_tail = ("re-ran the sweep a fifth time (byte-identical again), **cold-rebuilt the five cards that\n"
                   "  had never been cold-rebuilt**, added a **sixth independent closure consumer at a concrete\n"
                   "  non-bi-invariant model**, ran a wider forbidden-token scan, and deep-reviewed\n"
                   "  `spectral-sobolev` and `connection-curvature` (§14).")
new_status_tail = old_status_tail + (
    "\n  **Round 7 (invocation 6)** re-ran the sweep a sixth time (byte-identical), added a\n"
    "  canonical blocker-register cross-check against the D12-semantic-ledger 31-entry register, a\n"
    "  type-identity probe for the connection-curvature closure, and an audit-of-the-auditor\n"
    "  self-control with injected axiom/sorry/tautology defects (§15). **Round 8 (invocation 7)**\n"
    "  re-ran everything a seventh time (byte-identical), classified the round-7 vacuity-screen\n"
    "  blind spot flag-by-flag, added a closure-consumption (wiring) screen and two new kernel\n"
    "  probes (pp-artifact evidence for `diam_rep_of_toGHSpace`, register-identity and\n"
    "  van-Kampen-independence evidence for the SR-5 closure), and re-checked the missing cards\n"
    "  (§16).  The status remains `TASK_BLOCKED` for exactly one reason: 2/9 cards are\n"
    "  source-absent with no transport route.")
if old_status_tail not in text:
    raise SystemExit("status tail anchor not found")
text = text.replace(old_status_tail, new_status_tail, 1)

old_elapsed = "- **Elapsed:** ≈0.3 h of this invocation (≈3.05 h cumulative for the task)."
new_elapsed = ("- **Elapsed:** ≈0.9 h of this invocation (≈3.85 h cumulative for the task); invocation 7,\n"
               "  2026-09-11.")
if old_elapsed in text:
    text = text.replace(old_elapsed, new_elapsed, 1)

# ---- body sections ---------------------------------------------------------
marker = "\n## 15. "
idx = text.find(marker)
if idx != -1:
    text = text[:idx]

cards7 = r7["cards"]
cards8 = r8["cards"]
per_card_lines = "\n".join(
    "| {} | {} | {} | {} | {} | {} |".format(
        c, cards8[c]["build_rc"], cards8[c]["probe_rc"], cards8[c]["fullaudit_rc"],
        cards8[c]["kind_rc"], "identical" if cards8[c]["build_identical_to_round7"] else "DRIFT")
    for c in cards8)

cons_lines = "\n".join(
    "| {} | `{}` | {} | {} | {} |".format(
        card, name, e["declarations"], e["producer_uses"], e["status"])
    for card, entry in cons["cards"].items()
    for ge in entry["groups"].values() for name, e in ge.items())

sections = f"""
## 15. Round-7 re-verification and new evidence (invocation 6)

### 15.1 Round-7 sweep — sixth consecutive byte-identical sweep

`audit360/run_round7.sh` → `audit360/logs-round7/`, summary
`audit360/round7_summary.json` (sha256 `{sha(os.path.join(HERE, 'round7_summary.json'))}`).
All **seven available cards**: `lake build` rc 0, `A3Probe` rc 0, `A3FullAudit` rc 0
(`A3FULL: PASS`), `A3KindAudit` rc 0; **342 per-declaration cones**, **1103
full-namespace declarations PASS**; build/probe/full-audit/kind outputs byte-identical to
round 6 (excluding `###` headers and lake `[k/N]` counters). The negative control flags
`sorryAx` and the private `native_decide` axiom; the semantic-ledger snapshot package
rebuilds rc 0 with its out-of-package probe rc 0; `a3d2d3` build/probe/round-3 screens all
rc 0. Every extra probe of the package (closure consumers, F1 validation, phantom-parameter
`rfl`s, sharp-restatement hypotheses removals) re-ran rc 0.

### 15.2 Canonical blocker-register cross-check (new)

`audit360/canonical_crosscheck_round7.py` → `canonical_crosscheck_round7.json` (sha256
`{sha(os.path.join(HERE, 'canonical_crosscheck_round7.json'))}`). The nine cards' closure and
remaining-blocker prose is matched against the **31-entry blocker register** published by the
`D12-semantic-ledger` card (`longrun/results/D12-semantic-ledger.json`, sha256
`c094b50defd6672674f6774d47d05a7e7d626cf4b72fd3c6d82b1990ba426c8c`). Verdicts:

| card | register id | verdict |
|---|---|---|
| connection-curvature | I1 | **CONFIRMED-PARTIAL** — `leviCivitaExists` proves the *identical* canonical D2 Prop `LeviCivitaExistenceStatement` (kernel type-ascription), but I1's second conjunct `CovariantDerivativeCurvatureStatement` has no theorem of that type, so the register item stays open |
| surgery-recognition | SR-5 | **CONFIRMED** — `ConnectedSumDecomposition.mkV2` constructs the register's own D7 field |
| surgery-recognition | I5 | **CONFIRMED-LOCAL** — covering-space recognition bridge constructed; canonical I5 open (space-form input remains a hypothesis) |
| surgery-recognition | I5, I6 | **CONFIRMED-LOCAL** — deck-triviality by monodromy; canonical entries open |

The `I1` second-conjunct scan found **zero theorems** with type
`CovariantDerivativeCurvatureStatement`; all occurrences are the definition itself, comments,
or hypothesis positions.

### 15.3 Canonical-closure type-identity probe (new kernel evidence)

`audit360/pkgs/D12-connection-curvature/A3ExtraR7/CanonicalClosure.lean` (sha256
`{sha(os.path.join(HERE, 'pkgs/D12-connection-curvature/A3ExtraR7/CanonicalClosure.lean'))}`),
rc 0, three declarations, all cones `{{propext, Classical.choice, Quot.sound}}`:
the closure is ascribed the canonical D2 type, routed through the D2 hypothesis-form
equivalence `leviCivitaExistence_iff_nonempty`, and consumed downstream to build the Stage-1
`CurvatureOperator`.

### 15.4 Audit-of-the-auditor self-control (new)

`audit360/selfcontrol_round7.py` → `selfcontrol_round7.json` (sha256
`{sha(os.path.join(HERE, 'selfcontrol_round7.json'))}`): a throwaway copy of the
`D12-semantic-ledger` package is built clean (C0) and with an injected module adding
`axiom a3CtlAxiom : False`, a theorem proved from it, a `sorry` theorem and a tautology
`(P : Prop) (h : P) : P` (C1C2C3). All ten checks pass: C0 builds/probes/full-audits clean
with no vacuity flag and no forbidden token; the injected copy is flagged by the cone
predicate (project axiom, `sorryAx`), by `A3FullAudit` (rc 1 with explicit `A3FULL-BAD`
lines) and by the forbidden-token scan.

### 15.5 Finding F18 — vacuity-screen blind spot (new)

The round-3 screen split only on top-level `→`/`,`; Lean prints `theorem (P) (h : P) : P` in
signature form, so `binders = []` and every binder-sensitive criterion was blind. The
injected tautology control was **not** flagged by the old screen (`old_screen_flags_on_control
= []`), which the fixed signature-aware splitter now flags with both
`T10-conclusion-is-hypothesis` and `T9-hypothesis-equals-conclusion`. The fixed screen
(`vacuity_screen7_fixed.json`, sha256
`{sha(os.path.join(HERE, 'vacuity_screen7_fixed.json'))}`) produced 5 new flags on real
cards, classified in round 8 (§16.3).

### 15.6 Producer-card freeze and forbidden-token scan (round 7)

`card_freeze_round7.json`: all **14/14** producer card files are byte-identical to the
round-4 freeze. `forbidden_scan_round7.json` (the same 12-token comment/string-aware scan as
round 6) is clean on all eight staged packages: the only producer hit is the documented
volume-ibp negative-control `axiom negativeControl : False`, which appears in no cone; the
`partial` hits are this audit's own proof-term metaprograms.

## 16. Round-8 re-verification and new evidence (invocation 7)

### 16.1 Round-8 sweep — seventh consecutive byte-identical sweep

`audit360/run_round8.sh` → `audit360/logs-round8/`, summary `audit360/round8_summary.json`
(sha256 `{sha(os.path.join(HERE, 'round8_summary.json'))}`). Per-card results:

| card | build rc | probe rc | full audit rc | kind rc | vs round 7 |
|---|---|---|---|---|---|
{per_card_lines}

Totals unchanged: **342 cones, 1103 declarations PASS**, `all_core_rc_zero` and
`all_core_identical_to_round7` both true. Negative control re-ran and flagged both escape
axioms; snapshot build/probe rc 0; `a3d2d3` build/probe/round-3 rc 0.

### 16.2 Canonical register cross-check reproduces; closure consumption

`canonical_crosscheck_round8.json` (sha256
`{sha(os.path.join(HERE, 'canonical_crosscheck_round8.json'))}`) is **JSON-identical** to the
round-7 cross-check: the register mapping and all four verdicts reproduce exactly.

New **closure-consumption (wiring) screen** `audit360/closure_consumption_round8.py` →
`closure_consumption_round8.json` (sha256
`{sha(os.path.join(HERE, 'closure_consumption_round8.json'))}`): every identifier that the
two claimed closures introduce or consume was searched, comment/string-aware, in the *staged
producer packages* (audit probes excluded), and each has producer-side uses — **0 orphans**:

| card | identifier | decl sites | producer uses | status |
|---|---|---|---|---|
{cons_lines}

The audit-side independent consumers exist for every closure identifier as well
(`A3ExtraR3`, `A3ExtraR5`, `A3ExtraR6`, `A3ExtraR7`, `A3ExtraR8`).

### 16.3 F18/F19 classification — no new vacuity defect

`audit360/f18_classify.py` → `f18_flag_classification.json` (sha256
`{sha(os.path.join(HERE, 'f18_flag_classification.json'))}`), fail-closed on any
theorem-level flag without a recorded verdict. Result: the injected control stays flagged
(T9+T10), and all **10 residual flags** on real cards are explained:

* **6 flags on `def:DataResult` declarations** (`ChartMetric.grad`, `ChartMetric.pullbackMetric`,
  `heatEvolve`, `heatWeight`, `quotientHomeoOfSubsingleton`, `sphericalPieceRecognition_of`):
  kernel `ConstantInfo` says these are data definitions, so hypothesis-equals-conclusion has
  no content — screen over-firing, not a defect;
* **2 structural `Subsingleton` flags** (`spaceForm_fiber_subsingleton`,
  `deckTrivial_of_simplyConnected_quotient`): the conclusion *is* the theorem's content
  (fibres are orbits; `deckTrivial` is defined as `Subsingleton Γ` with `Γ` an inhabited
  group), deep-reviewed in rounds 3/7;
* **1 numeric-shape flag** (`conformal_denom_pos`): the goal is the x-dependent
  `0 < 1 + x 0 ^ 2`, not a closed numeral;
* **1 pretty-printer flag** (`diam_rep_of_toGHSpace`, F19): see §16.4.

The fixed screen is also byte-identical between rounds 7 and 8 (`vacuity_screen8.json`,
`vacuity_screen8_fixed.json`).

### 16.4 New round-8 kernel probes

* `A3ExtraR8/PpArtifactCheck.lean` (geometric-compactness, sha256
  `{sha(os.path.join(HERE, 'pkgs/D12-geometric-compactness/A3ExtraR8/PpArtifactCheck.lean'))}`,
  rc 0) prints the kernel type of `diam_rep_of_toGHSpace` with `pp.all`, showing the two
  sides are `@Set.univ.{{0}} (GHSpace.Rep (toGHSpace X))` and `@Set.univ.{{u}} X`; the
  T4-trivial-equality flag is a pretty-printer artifact (the `rfl` attempt in
  `A3ExtraR3/TrivialCheck.lean` is rc 1 **by design**).
* `A3ExtraR8/RegisterIdentity.lean` (surgery-recognition, sha256
  `{sha(os.path.join(HERE, 'pkgs/D12-surgery-recognition/A3ExtraR8/RegisterIdentity.lean'))}`,
  rc 0, four declarations, all cones `{{propext, Classical.choice, Quot.sound}}`) proves the
  closure value has the **canonical D7 field type**, that the constructed
  `sphere_of_spheres` proof **factors definitionally** as
  `hX.trans hsum` through `iteratedSphereSum` (the conclusion is built, not assumed), and
  that the branch is **definitionally independent of the van Kampen hypothesis**.

### 16.5 Missing-card re-check (round 8) and A3 status

`audit360/missing_cards_recheck_round8.py` → `missing_cards_recheck_round8.json` (sha256
`{sha(os.path.join(HERE, 'missing_cards_recheck_round8.json'))}`), checked
{miss['checked_at']}: both cards remain `remote_owned` on 360-1/360-2; **no** worktree,
release package, card `.md`/`.json`, Lean module, state directory or marker anywhere under
the poincare root, 0 files named after either card under `/data3/guoshaoyang`; transport
`tcp 127.0.0.1:10022` → **refused**, no tailscale 360-1/360-2 peer, no NFS/CIFS/SSHFS mount.
Verdict: **source-absent on this host — not auditable here, not refuted**. This is a
transport blocker, not a mathematical one.

**A3 status after round 8:** unchanged in kind — *stale-as-stated / partially addressed*.
The seven available cards now have seven consecutive byte-identical sweeps, a hash-verified
frozen producer state, a canonical register mapping, wiring evidence for every claimed
closure, and a classified vacuity screen with a positive control; the D2/D3 defects
(§8, F10/F11) remain unrepaired on the producer side and 2/9 cards remain unaudited, so the
9-card milestone is still **blocked**.
"""

open(RES_MD, "w").write(text.rstrip("\n") + "\n" + sections)
print("MD updated; length", len(text) + len(sections))
print("md sha256:", sha(RES_MD))
