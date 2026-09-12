# Round-4 adversarial review — frozen artifact set and round-4 integrity

**Reviewer:** independent subagent `92419d8c-7698-443a-9a6b-82d43a858d11` (read-only; no
repository files touched).
**Scope:** the four frozen round-1/2/3 files, the round-4 additive module, the round-4 logs and
the acceptance claims (criteria (1)–(4)).
**Verdict:** **OVERALL PASS — no BLOCKER, no MAJOR.** Two MINOR and three INFO findings, all
documentation/consistency-level.

## Hashes (recomputed twice, including after concurrent activity) — all match

| file | sha256 |
| --- | --- |
| `RicciToDoubling.lean` | `9b17c673…a1d4` |
| `RicciToDoublingHyperbolic.lean` | `be50ae25…0841` |
| `RicciToDoublingAudit.lean` | `3e8510bc…1417` |
| `RicciToDoublingHyperbolicAudit.lean` | `dc9b2638…7ee3` |
| `RicciToDoublingHyperbolicClosedForm.lean` | `1064815e…2b28` |
| `RicciToDoublingHyperbolicClosedFormAudit.lean` | `cb1dba76…66ed` |

## Gates

1. **HASHES — PASS.**
2. **AXIOM CONES — PASS.** 49/49 cones exactly `{propext, Classical.choice, Quot.sound}`
   (34 frozen = 13 + 21; 15 new); zero unapproved. `round4-rebuild.log`:
   BUILD-EXIT=0 (l.18), `AXIOM-AUDIT PASS` ×2 (l.180, l.320), AUDIT1-EXIT=0 (l.181),
   AUDIT2-EXIT=0 (l.321), 0 `warning`, 0 `error`. `round4-closedform-build.log`:
   CF-BUILD-EXIT=0 (l.7). `round4-closedform-audit.log`: `AXIOM-AUDIT PASS` (l.94),
   AUDIT3-EXIT=0 (l.95). The reviewer **re-ran all three audits via `lake env lean --stdin`**
   (exit 0) and the outputs are **byte-identical** to the logged audit bodies, so the logs are
   not stale.
3. **CONCLUSION-EQUIVALENCE — PASS.** The reviewer independently parsed the compiled `#check`
   types, split at top-level arrows and peeled `∀`. For all 9 headline theorems the hypothesis
   list contains **zero** occurrences of the conclusion's head symbol
   (`radialVolume` / `coveringNumber` / `sinhPowIntegral`). Euclid/hyperbolic ratio and doubling
   have 18/20 scalar hypotheses; the two covering-interface lemmas have `(hμ, hpos)` and
   `(hμ, hdbl, hpos, hcomp)`; the composite has the 15 scalar hypotheses + `hμ` + `hr0` + `hrT`
   + `x`. Bishop–Gromov is only **applied** (`RicciToDoubling.lean:166`,
   `RicciToDoublingHyperbolic.lean:386`), never a hypothesis; `bishopGromov` occurs 0 times in
   the audit signature bodies.
4. **MANIFOLD OVERCLAIM — PASS.** Comment/string-stripped code of the 3 mathematical modules has
   **zero** occurrences of `Manifold` / `Riemannian` / `ChartedSpace` / `TangentBundle` /
   `IsManifold` / `VectorBundle` / `SmoothManifold` (all mentions are docstrings explicitly
   denying manifold claims). `IsRadialBallMeasure` is a real `def`
   (`RicciToDoubling.lean:344`; `#print` shows the body
   `fun μ A => ∀ x s, μ (closedBall x s) = ofReal (radialVolume A s)`), never an axiom, used only
   as a hypothesis/witness. No manifold measure is constructed or claimed.
5. **FROZEN INTEGRITY — PASS.** The new module imports only
   `Poincare.L4.Compactness.RicciToDoublingHyperbolic` + `Mathlib…IntegrationByParts`; no frozen
   file mentions `ClosedForm`; declaration-name intersection frozen(36) ∩ new(15) = ∅; no
   attribute/notation/instance/local shadowing; importing the new module and re-`#check`ing the
   frozen headlines reproduces their exact types.
6. **FORBIDDEN TOKENS — PASS.** 0 code matches for `sorry` / `sorryAx` / `axiom` / `unsafe` /
   `native_decide` / `proof_wanted` / `admit` in all 6 files. Informational only: the word
   "axiom" inside audit docstrings/error strings (4 lines).
7. **WITNESS / NON-VACUITY — PASS.** `euclidModel_hypotheses_witness`,
   `euclidModel_volume_doubling_closedForm`, `radialVolume_euclidModel_one_value_witness`
   (`= 2 ∧ = 1/2`), `hypModel_doubling_witness`, `hypModelA_one_one_volume`,
   `isRadialBallMeasure_real_witness` are all real compiled `#check`ed declarations, accepted by
   fresh Lean checks. Snowflake arithmetic independently recomputed (sympy):
   `μ(closedBall x s) = 2s²` for `s ≥ 0`, `0` for `s < 0`; `radialVolume (4|·|) s = 2s|s|`
   (`= −2s²` for `s < 0`, truncated to `0` by `ofReal`); hence
   `IsRadialBallMeasure volume_snowflake (4|·|)` holds for **all** real `s`. The joint
   realization with the scalar hypotheses (`d = 1`, `k = 0`, `C = 0`, `m = 1/t`, `dm = −1/t²`,
   `dA = 4`) checks out (`−1/t² + 1/t² + 0 = 0`).
8. **NEW-MODULE SPOT-CHECK — PASS.** `hypModelA_volume_closedForm` at `d = 1`, `κ = 1` gives
   `(1⁻¹)²·J₁(s) = cosh s − 1`, identical to the frozen `hypModelA_one_one_volume`;
   `hypModel_volumeRatio_closedForm` at `d = 1`, `κ = 1` gives `(cosh R − 1)/(cosh r − 1)`; the
   doubling constant `J₁(2s)/J₁(s) = 2(cosh s + 1)` for `s > 0`, matching the frozen
   `hypModelA_one_one_doubling` / `hyp_volume_doubling_d1_k1`. All verified by fresh Lean proofs
   (exit 0).

## Findings

**No BLOCKER. No MAJOR.**

* **MINOR-1.** `hypModelA_one_one_volume_closedForm` (`ClosedForm:270-273`) restates the frozen
  `hypModelA_one_one_volume` (`Hyperbolic:477-478`) with the identical type — a deliberate
  consistency corollary derived through the general closed form, not a duplication of
  `conjugate_point_bound`/Rauch, and it adds no hypothesis to any frozen declaration.
* **MINOR-2.** `hypModel_doubling_witness` (`Hyperbolic:443-464`) has a conclusion immediate from
  positivity of `radialVolume (hypModelA d κ) s`; its evidential value is the joint
  satisfiability of the hypothesis package (the proof supplies all model lemmas), while sharpness
  is separately witnessed by `euclidModel_volume_doubling_closedForm` and
  `radialVolume_euclidModel_one_doubling_witness`. Honest and adequate.
* **INFO-1.** The acceptance text's `hupper` does not exist in `MeasureGrowthCovers.lean` (only
  `hlower` l.93, `hcomp` l.274-275, `hdouble` l.311-314); the artifact documents this precisely
  (`RicciToDoubling.lean:55-58`). The composite derives the three dyadic doubling inequalities
  from the Riccati data (`RicciToDoubling.lean:498-511`); it does not assume them.
* **INFO-2.** The interface hypothesis `hμ : IsRadialBallMeasure μ A` unfolds definitionally to a
  statement mentioning `radialVolume` (the mandated interface); it is not conclusion-equivalent —
  no hypothesis of the interface lemmas mentions `coveringNumber`, and the composite's doubling
  inputs are proved, not assumed. The gap section (`RicciToDoubling.lean:544-591`) honestly
  states that a manifold proof would only establish a weaker two-sided comparability, and that
  the snowflake realization is informal.
* **INFO-3.** A bare ratio statement `J₁(2s)/J₁(s) = 2(cosh s + 1)` is false at `s = 0` under
  Lean's totalized division (`0/0 = 0 ≠ 4`); all artifact statements correctly require `0 < s`
  (e.g. `RicciToDoublingHyperbolicClosedForm.lean:354`).
* **INFO-4 (concurrent activity).** At 11:06 a forced rebuild of the closed-form module briefly
  removed its `.olean` (racing one spot check) and appended
  `logs/round4-closedform-build.log` + `AUDIT3-EXIT=0`. Re-verified afterwards: the audit body is
  still byte-identical to the reviewer's fresh rerun and all six artifact hashes are unchanged.

Also verified: every declaration in the three modules (36 frozen + 15 new) carries a
`**Class:**` line; the 13+21+15 audit lists cover every public declaration (the only omissions in
the frozen pair are the two `private` helpers, whose axioms necessarily propagate into the
audited public cones).

## Independent reproduction (stronger than reading the logs)

The reviewer re-elaborated all six files from source with `lake env lean --stdin` (read-only):
**exit 0 for all six, zero warnings/errors**. The three audit outputs are **byte-identical** to
the recorded standalone audit logs, and the audit sections inside `round4-rebuild.log` are
byte-identical to the fresh runs — the logs are not stale and the modules genuinely compile from
the frozen sources. Scratch work lived only under `/tmp/l4verify/`.

## Exact commands run (scratch files under `/tmp/l4verify/` only)

```bash
sha256sum release/.../{RicciToDoubling,RicciToDoublingHyperbolic,RicciToDoublingHyperbolicClosedForm}.lean \
          release/Audit/RicciToDoubling{,Hyperbolic,HyperbolicClosedForm}Audit.lean
grep -n "BUILD-EXIT\|AUDIT1-EXIT\|AUDIT2-EXIT\|AXIOM-AUDIT" logs/round4-rebuild.log logs/round4-closedform-audit.log
cd release && for f in <the six files>; do lake env lean --stdin < "$f" > "/tmp/l4verify/$(basename $f .lean).out"; done
diff <(sed -n '20,180p' logs/round4-rebuild.log)  /tmp/l4verify/RicciToDoublingAudit.out
diff <(sed -n '183,320p' logs/round4-rebuild.log) /tmp/l4verify/RicciToDoublingHyperbolicAudit.out
diff <(sed -n '2,94p' logs/round4-closedform-audit.log) /tmp/l4verify/RicciToDoublingHyperbolicClosedFormAudit.out
python3 /tmp/l4verify/parse_sigs.py ; python3 /tmp/l4verify/scan.py forbidden ; python3 /tmp/l4verify/decls.py
lake env lean --stdin < /tmp/l4verify/spot.lean    # d=1,k=1 consistency + witnesses; EXIT=0
lake env lean --stdin < /tmp/l4verify/print.lean   # #print IsRadialBallMeasure + #print axioms; EXIT=0
python3 -c "import sympy as sp; s,t=sp.symbols('s t',real=True); print(sp.integrate(4*sp.Abs(t),(t,0,s)))"
```

**Bottom line:** the frozen artifact set satisfies acceptance criteria (1)–(4), the round-4
additive module is a genuine strengthening (elementary closed form, 15/15 clean cones, no
frozen-symbol collisions, no hypothesis added to any frozen declaration), and nothing in it
invalidates the accepted claims. **PASS.**
