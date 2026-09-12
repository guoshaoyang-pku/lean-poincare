# Adversarial semantic review #1 — `release/Poincare/L4/Compactness/RicciToDoubling.lean`

Reviewed revision: sha256 `905d920b1f771aebaf26547b57851f0256839baa596a31bffcac53be7c0891a2`
(the revision before the review-driven doc corrections; see
`longrun/results/L4-child-ricci-to-doubling.md` §4 for the dispositions and the final hash
`13d466b56109bf8e4364272ee96ff42bae71ce7d54bd3602c40f32ee3078f1d2`).
Reviewer: independent adversarial subagent (read-only; no build). Recorded here as evidence.

## A. Circularity / conclusion-equivalent hypotheses

* A1 [INFO] No hypothesis of `euclid_volume_ratio_le_of_ricci_nonneg` is the conclusion; the
  bound is derived by direct call to `bishopGromov_volume_le` + closed-form rewrite. The
  statement string never occurs as a hypothesis. Genuinely derived, not assumed.
* A2 [INFO] `hk`/`hineq`/`hnorm` do not secretly contain doubling. `hnorm` is the D12
  near-zero tangent normalization `|m t − d/t| ≤ C`; no volume statement in any hypothesis.
* A3 [MAJOR] The composite is not circular and **not vacuous** (a joint realization exists,
  see D6); but the file asserted the contrary in the gap section. Sound but its own status
  account was wrong.
* A4 [INFO] `IsRadialBallMeasure` is strictly stronger than the hypotheses it discharges
  (exact equality at every centre and every real radius vs a lower bound at radius r/2 for
  centres in the ball). The interface theorems are genuine implications.

## B. Manifold overclaim

* B1 [MINOR] "closes the measure-growth half of U9 at the scalar/model level" read as an
  overclaim; scope softened in the correction.
* B2 [INFO] No declaration claims a manifold measure, manifold doubling, or that U9 is
  closed.
* B3 [MINOR] Names `..._of_ricci_nonneg` refer to the scalar sign convention; documented.
* B4 [INFO] The `ω_{n−1}` discussion is conditional/motivational only.

## C. Label honesty

* C1 [INFO] All 13 declarations carried a `**Class:**` line at review time.
* C2 [MINOR] Header claimed exactly two label strings while the composite has a hybrid
  label; header corrected.
* C3 [INFO] No mislabelled declaration.

## D. Witness / non-vacuity accuracy

* D1 [INFO] `euclidModel_hypotheses_witness` matches its docstring.
* D2 [INFO] Closed-form doubling identity is the sharp form; accurate.
* D3 [MINOR] The `d = 1` witness docstring over-claimed general-`d` sharpness; corrected to
  cite `euclidModel_volume_doubling_closedForm`.
* D4 [INFO] `d = 1` arithmetic verified (`V 2 = 2`, `V 1 = 1/2`, `2 = 2²·(1/2)`).
* D5 [INFO] `isRadialBallMeasure_real_witness` verified for all real `s`, including `s < 0`.
* D6 [MAJOR] Gap-section errors: (a) the additivity argument for the usual metric on ℝ was
  not written as a derivation (corrected); (b) the claim that a joint realization requires
  the manifold construction is **false** — counterexample: `X = ℝ` with the snowflake metric
  `d(x,y) = √|x−y|`, `μ` = Lebesgue, `A(t) = 4|t|`; then `closedBall x s = [x−s², x+s²]`
  for `s ≥ 0` with measure `2s²`, empty for `s < 0`, and `radialVolume A s = 2s|s|`, so
  `IsRadialBallMeasure` holds; with `d = 1, k = 0, C = 0, m(t) = 1/t, dm(t) = −1/t², dA = 4`
  the scalar hypotheses hold (Riccati equality). Hence the composite's hypothesis set is
  jointly satisfiable. Corrected in the gap section.
* D7 [MINOR] `A ≡ 2` mislabelled "normalized" 1-dimensional profile; corrected to
  unnormalized (angular-constant-included).

## E. Statement strength

* E1, E2, E4 [INFO] Ratio bound, doubling and composite bound have the documented ranges,
  directions and constants; no weakening.
* E3 [MINOR] "all scales `s ≤ T/2`" was off by a factor 2 (the halving form holds for
  `s ≤ T`); corrected.
* E5 [INFO] The hyperbolic branch was not in the file under review; a companion file now
  supplies it.

## F. Interface precision

* F1, F2, F4 [INFO] Interface predicate precisely stated; the discharge mapping verified in
  Lean (`hlower`, the measure term, `hdouble` at the three dyadic scales, `hcomp` with
  `K = 1`).
* F3 [MINOR] Header's "hupper" mapping corrected (the token does not occur in the consumed
  files; `coveringNumber_le_measure_ratio` has no upper hypothesis).

## G. Residual risks

* G1 [MAJOR] Evidence was stale w.r.t. the reviewed bytes; all gates re-run on the final
  bytes (see `evidence/ricci-to-doubling-verify.json`, `OVERALL: PASS`).
* G2 [INFO] No forbidden tokens; all cones classical trio.
* G3 [MINOR] Dangling doc reference corrected.
* G4 [INFO] A few redundant hypotheses (harmless, no weakening).
* G5 [INFO] The predicate is stronger than needed; non-vacuity now documented (D6).
* G6 [INFO] `DoublingToCovers` imported as the required round-3 consumption; documented.
* G7 [MINOR] Two corollary docstrings deferred their hypothesis list; now explicit.

## Overall verdict (reviewer)

No BLOCKER-level defect: no `sorry`/`axiom`, no conclusion-equivalent hypothesis, no
manifold-measure or manifold-doubling overclaim, no statement weakened relative to its
docstring. Criteria (1) MET for Euclidean `k ≥ 0` (hyperbolic branch under the "if available"
clause, now supplied by the companion file); (2) MET with genuine scalar non-vacuity and
sharpness; (3) MET as a precise documented interface, with the composite in fact non-vacuous
(snowflake witness) — the file must not describe it as possibly vacuous; (4) MET in substance,
with minor taxonomy/doc exceptions. Reportable at the "scalar model + conditional
metric–measure interface (non-manifold)" level after the listed wording fixes and an
evidence re-run — all of which were applied.
