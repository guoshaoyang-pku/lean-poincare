# Adversarial semantic review #2 — `RicciToDoublingHyperbolic.lean` (+ `RicciToDoubling.lean` delta)

Reviewer: independent adversarial subagent (read-only; scratch `lake env lean` + `#print axioms`
only). Recorded here as evidence. Target revision:
`release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean`, sha256
`be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` (the reviewer first read
`4d1e07d2…`; the final revision differs by the review-driven doc fixes below);
secondary: `release/Poincare/L4/Compactness/RicciToDoubling.lean`, sha256
`9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4`.

## H1 — Mathematical correctness of the hyperbolic model — NO DEFECT (one INFO)

(a) Riccati equality correct: with `x = κt`, `mbar' + mbar²/d + kbar =
dκ²(cosh²x − sinh²x − 1)/sinh²x = 0`; `hypModelM_riccati` assumes exactly the three needed
nonzeroness conditions. (b) Normalization correct and sharp: both elementary bounds are true,
`coth_sub_inv_abs_le_one` gives `0 ≤ coth x − 1/x ≤ 1`, the supremum is exactly `dκ`, so
`d·κ ≤ C` is the weakest single-constant condition. (c) `hypModelA_logDeriv` genuinely needs
`0 < d`. (d) zero/positivity/continuity claims match their hypotheses.
**INFO:** at `κ = 0`, `hypModelA` is identically zero (not the flat limit `t^d`); dropping
`κ ≠ 0` from `hypModelA_zero` is sound but degenerate, and harmless because the instantiation
always pairs it with `hypModelA_pos hκ` (`κ > 0`).

## H2 — Instantiation fidelity — NO DEFECT (redundancy noted)

All 27 hypotheses of `bishopGromov_volume_le` checked positionally against the in-file model
lemmas; direction of the comparison is the correct Bishop–Gromov direction for `k ≥ −dκ²`.
`hdκC : d·κ ≤ C` is honest, necessary, sharp and documented in four places. Reviewer's
independent `#print axioms` on the current revision: all hyperbolic declarations (including
Section 7) depend on exactly `{propext, Classical.choice, Quot.sound}`; no `sorryAx`, no
assumed Bishop–Gromov. **INFO:** `hC`, `hT`, `hsT` are redundant given the other hypotheses
(harmless, mirrored from D12's signature).

## H3 — Conclusion-equivalence / vacuity — NO DEFECT (two MINOR)

No hypothesis mentions `radialVolume`, ball measures or covering numbers; the witness is a
genuine use of the theorem, certifying joint satisfiability; Section 7 strengthens it with an
evaluated `d = 1`, `κ = 1` equality.

* **MINOR (wording, fixed):** header called the negative-curvature range "complementary"; it
  actually contains the Euclidean range. Corrected.
* **MINOR (closed form):** for general `d` the constant is the explicit model ratio, honestly
  disclaimed; fully evaluated only for `d = 1`, `κ = 1` (`2(cosh s + 1)`).
* **INFO:** "the constant grows with `s`" is true but not proved in-file; informal remark.

## H4 — Statement strength / duplication — NO DEFECT (one INFO)

No overlap with `ConjugatePointBound.lean` / `ConstantCurvatureRauch*.lean` (those are
Jacobi/Rauch comparisons; none states a Riccati area model, Bishop–Gromov ratio or ball
measure). No weakening relative to docstrings. **INFO:** D10's `jacobiSolHyperbolic` with
`K = −κ²` equals `hypModelA 1 κ t`, but D10 is outside this worktree's import closure, so
"proved from scratch" is locally justified.

## H5 — Labels and hypothesis lists — NO DEFECT (one MINOR, fixed)

All 23 declarations (21 public + 2 private) carry accurate `**Class:**` labels; all statements
are `model (scalar ODE)`.

* **MINOR (fixed):** `hyp_volume_doubling_of_ricci_ge`'s docstring deferred its hypothesis
  list; now explicit.
* **INFO (fixed):** the module header's content list omitted `coth_sub_inv_abs_le_one` and the
  Section 7 declarations; now included.

## H6 — Secondary delta in `RicciToDoubling.lean` — NO DEFECT (one MINOR, fixed)

The snowflake-metric non-vacuity paragraph was re-verified independently and is correct:
`X = ℝ` with `d(x,y) = √|x−y|`, `μ` = Lebesgue, `A(t) = 4|t|` satisfies
`IsRadialBallMeasure` for every real `s`, and with `d = 1`, `k = 0`, `C = 0`, `m = 1/t`,
`dm = −1/t²`, `dA = 4` every scalar hypothesis of the composite holds; the text correctly
labels the witness informal and leaves the manifold realization open. The usual-metric
additivity no-go is correct.

* **MINOR (fixed):** `IsRadialBallMeasure`'s docstring said that at negative radii "both sides
  are `0`"; the right-hand side is `0` only when `∫₀ˢ A ≤ 0` (counterexample `A ≡ −1`,
  `s = −1`). The text now calls the negative-radius part a genuine constraint on `A` and notes
  that all uses are at positive radii. Nothing unsound resulted (all theorems use positive
  radii).

## Verdict (reviewer)

All six sections complete. **No BLOCKER, no MAJOR.** The hyperbolic file honestly meets
criterion (1)'s negative-curvature branch at the scalar/model level:
`hyp_volume_ratio_le_of_ricci_ge` is a genuine, axiom-clean instantiation of
`bishopGromov_volume_le` with the explicit model
`(Abar, mbar, kbar, dAbar) = (hypModelA, hypModelM, hypModelK, hypModelDA)`, with an honest,
sharp, documented `d·κ ≤ C`, no conclusion-equivalent hypothesis and no manifold overclaim.
Criteria (2)–(4) are met at the scalar/model + documented-interface level, subject to the two
MINOR wording fixes (both applied).
