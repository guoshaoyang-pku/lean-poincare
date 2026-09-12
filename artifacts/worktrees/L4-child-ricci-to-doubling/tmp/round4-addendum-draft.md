## 10. Addendum — round-4 independent acceptance + elementary hyperbolic closed form

A fourth invocation performed an independent acceptance re-verification of the **frozen bytes**
(4/4 hashes unchanged: `9b17c673…`, `be50ae25…`, `3e8510bc…`, `dc9b2638…`) and, in addition,
closed the one residual strict-reading caveat of criterion (1) (round-3 finding **M3**: the
general-`d` hyperbolic constant was the explicit model *integral* ratio, evaluated elementarily
only at `d = 1`, `κ = 1`) by an **additive** module that leaves every frozen file untouched.

### 10.1 New artifact

| file | sha256 | decls | content |
| --- | --- | --- | --- |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean` | `1064815e…` | 15 | explicit elementary recursive antiderivative `sinhPowIntegral`, its derivative/integral theorems, `radialVolume (hypModelA d κ) s = (κ⁻¹)^(d+1)·J_d(κ s)`, elementary model ratio, closed-form Bishop–Gromov and doubling statements |
| `release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean` | `cb1dba76…` | — | `#check` signatures + fail-closed `collectAxioms` audit for the 15 new declarations |

Mathematical content: with `J_d(x) = ∫₀ˣ sinh(u)^d du` and the integration-by-parts recursion

    J_0(x) = x,    J_1(x) = cosh x − 1,
    J_{d+2}(x) = (sinh(x)^{d+1}·cosh x − (d+1)·J_d(x))/(d+2),

the module *proves* `J_d' = sinh^d` (`sinhPowIntegral_hasDerivAt`, strong induction; no
integral used in the induction) and the integral identity `∫₀ˢ sinh^d = J_d(s)`
(`sinhPowIntegral_integral`, FTC).  The substitution `u = κt` (change of variables
`intervalIntegral.integral_comp_mul_deriv`) then yields

    radialVolume (hypModelA d κ) s = (κ⁻¹)^(d+1) · J_d(κ·s)          (κ ≠ 0, all real s),

so `V̄ R/V̄ r = J_d(κR)/J_d(κr)` (`hypModel_volumeRatio_closedForm`) — an explicit elementary
expression for **every** `d`, with no integral left.  The closed-form composites

* `hyp_volume_ratio_le_of_ricci_ge_closedForm`:
  `radialVolume A R ≤ (J_d(κR)/J_d(κr))·radialVolume A r`, and
* `hyp_volume_doubling_closedForm`:
  `radialVolume A (2s) ≤ (J_d(2κs)/J_d(κs))·radialVolume A s`

carry **exactly** the same 27 top-level hypotheses as the frozen `hyp_volume_ratio_le_of_ricci_ge`
/ `hyp_volume_doubling_of_ricci_ge` (machine-compared, gate K below) and consume those frozen
theorems; Bishop–Gromov is still proved through D12, never assumed.  Low-dimension evaluations
are kernel-checked: `J_2 = (sinh·cosh − x)/2`, `J_3 = (sinh²·cosh − 2(cosh − 1))/3`,
`hypModelA_one_one_volume_closedForm` (`cosh s − 1`, agreeing with the frozen
`hypModelA_one_one_volume`), and the fully elementary `d = 2` ratio
`(sinh(κR)cosh(κR) − κR)/(sinh(κr)cosh(κr) − κr)` (`hypModel_volumeRatio_d2_closedForm`).

Every one of the 15 declarations is labelled `**Class:** model (scalar ODE)`; the module
contains no manifold, metric, measure or curvature-tensor content, and **no manifold measure is
constructed or claimed**.  The general-`d` constant is now an explicit finite elementary
expression (a recursion that unfolds to `sinh`/`cosh` monomials for each fixed `d`), not an
unevaluated integral.

### 10.2 Round-4 verification evidence (all gates PASS)

* **Forced recompilation of the frozen pair** (oleans deleted, `lake build` of the 7 targets):
  `✔ [3453/3454] (2.7s)`, `✔ [3454/3454]`, `Build completed successfully (3454 jobs)`,
  exit 0, **zero warnings** (`logs/round4-rebuild.log`, sha256 `905ae25b…`; copy with the full
  compiled `#check` signatures at `evidence/round4-audit-full.log`, sha256 `fccabd0e…`).
* **Forced recompilation of the new module** (olean/ilean/trace deleted, rebuilt from source):
  `Build completed successfully (3461 jobs)`, `CF-BUILD-EXIT=0`, zero warnings
  (`logs/round4-closedform-build.log`).
* **Fresh fail-closed axiom audits**: 34 (frozen) + 15 (new) = **49 cones, every one exactly
  `{propext, Classical.choice, Quot.sound}`**, 0 violations; `BUILD-EXIT=0`, `AUDIT1-EXIT=0`,
  `AUDIT2-EXIT=0`, `AUDIT3-EXIT=0`; no `warning` in either log.
* **Round-4 11-gate checker** (`tools/round4_acceptance_check.py`, sha256 `a8ab8aa8…`, a fresh
  implementation): hash freeze (frozen 4 + new 2), axiom cones, conclusion-equivalence
  (14 headline declarations, arrow-depth-aware), manifold-overclaim (0 tokens in 49 declaration
  types and in the stripped sources of the 3 modules), 51/51 classification labels, numeric
  evidence, no Rauch/conjugate duplication, canonical forbidden-token scan (0 hard matches),
  statement fidelity to the acceptance text, round-4 consumption of the frozen instantiation,
  and **closed-form hypotheses byte-identical to the frozen ones** — **11/11 PASS**
  (`evidence/round4-acceptance.json`, sha256 `b5b6f20f…`).
* **387/387 independent numeric checks** (`tools/round4_numeric_checks.py`, sha256 `2e7ecf30…`,
  `evidence/round4-numeric-checks.json`, sha256 `840cae39…`): Euclidean closed form / doubling /
  Riccati; hyperbolic Riccati / log-derivative / normalization and the `d = 1, κ = 1` values;
  the recursion `J_d` against quadrature of `sinh^d` for `d = 1..8` (max rel. err
  `1.65e-14`); the substitution identity for `κ ∈ {0.3, −0.8, 1, −2.5}` and signed radii
  `s ∈ {−1.5, −0.7, 0, 0.45, 1.6}` (max rel. err `2.25e-14`); the elementary `J_2`, `J_3` and
  `d = 2` ratio forms; snowflake joint-witness arithmetic.
* **Authoring driver re-run** on the frozen bytes after the round-4 work:
  `tools/ricci_to_doubling_verify.py` → `OVERALL: PASS` (6/6 gates).

### 10.3 Adversarial reviews (round 4)

* **Frozen-set re-verification review** (`evidence/round4-review-frozen.md`, independent
  subagent `92419d8c…`, read-only): **OVERALL PASS — no BLOCKER, no MAJOR**. The reviewer
  independently recomputed all six hashes (twice), reproduced all three axiom audits
  byte-identically via `lean --stdin`, re-parsed the compiled signatures to confirm zero
  conclusion symbols in every headline hypothesis list, confirmed frozen integrity (the new
  module neither edits nor shadows the frozen files; declaration-name intersection is empty),
  re-ran the forbidden-token scan (0 code matches), re-verified the non-vacuity witnesses and
  the snowflake arithmetic with sympy, and spot-checked the new module against the frozen
  `hypModelA_one_one_volume`. Two MINOR findings, both documentation-level and recorded:
  (i) `hypModelA_one_one_volume_closedForm` deliberately restates the frozen
  `hypModelA_one_one_volume` as a consistency corollary (not a Rauch/conjugate-point
  duplication); (ii) `hypModel_doubling_witness`'s conclusion is immediate from positivity —
  its evidential value is joint satisfiability of the hypothesis package (the Euclidean
  sharpness identity covers attainment). Both are transparently in-file.
* **Closed-form module review** (`evidence/round4-review-closedform.md`):
  **REVIEW_CLOSEDFORM_OUTCOME**

### 10.4 Honest scope (unchanged)

**U9's manifold half remains open and is not claimed.**  The round-4 addition is strictly inside
the scalar/model lane: it replaces an unevaluated model integral by an explicit elementary
expression.  No Riemannian manifold, Riemannian volume measure, geodesic sphere density, coarea
formula or curvature→Riccati derivation is formalized, and no manifold measure is constructed.
The `IsRadialBallMeasure` interface remains a documented conditional interface, and the
manifold realization is the named open input (a separate child task,
`L4-child-bishop-gromov-interface`, addresses the metric–measure packaging).

Verdict of the round-4 invocation: **TASK_DONE** at the scalar/model + documented conditional
metric–measure interface level, re-verified on unchanged frozen bytes and strengthened by an
additive elementary hyperbolic closed form; **U9's manifold half remains open**.
