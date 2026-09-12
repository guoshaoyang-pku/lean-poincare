# Independent acceptance review — `L4-child-ricci-to-doubling` (round-2 re-verification)

**Reviewer role:** independent acceptance invocation (not the authoring round). Read-only
w.r.t. the reviewed mathematical content; the only writes are evidence files, the checkpoint,
the result card, and the separate checker `tools/independent_acceptance_check.py`.
**Frozen revision reviewed (sha256):**

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/Compactness/RicciToDoubling.lean` | `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean` | `be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` |
| `release/Audit/RicciToDoublingAudit.lean` | `3e8510bc5ddf37d7d15e13841d20f30ee3f08ffe77ceca210871d515f72a1417` |
| `release/Audit/RicciToDoublingHyperbolicAudit.lean` | `dc9b26384f279add1108ac5b83b41df7dd960b89357329ce31ee7c03422c7ee3` |

All four hashes equal the `checkpoint.json` values; the 10 consumed sources are byte-identical
to their immediate origins (2 also to their ultimate D12 origin), re-verified in
`evidence/ricci-to-doubling-verify.json` and `evidence/independent-acceptance.json`.

## Method (independent of the authoring round)

1. **Forced recompilation.** Deleted the `.olean/.ilean/.trace/.hash` of both new modules and
   rebuilt with `lake build Poincare.L4.Compactness.RicciToDoubling
   Poincare.L4.Compactness.RicciToDoublingHyperbolic` from `release/`:
   `✔ [3453/3454] Built … (2.6s)`, `✔ [3454/3454] Built … (2.5s)`,
   `Build completed successfully (3454 jobs)`, exit 0, **zero warnings**
   (`logs/independent-acceptance-rebuild.log`, sha256 `a9a4049877c9ddcd…`).
2. **Fresh fail-closed axiom audit** of both drivers after that rebuild: 13 + 21 = 34
   declarations, every cone parsed independently and found to be *exactly*
   `{propext, Classical.choice, Quot.sound}`; both drivers exit 0. Because
   `Lean.collectAxioms` traverses the dependency cone, this also certifies that the consumed
   D12 theorems (in particular `bishopGromov_volume_le`) are free of `sorryAx` and of any
   unapproved axiom.
3. **Fresh signature capture** (`#check` of every declaration) used for the semantic scans.
4. **Separate adversarial checker** (`tools/independent_acceptance_check.py`, fresh
   implementation, not a wrapper of the authoring driver): 9 gates, all PASS —
   hash freeze, cone subsets, conclusion-equivalence, manifold-overclaim,
   36/36 classification labels, informal-witness arithmetic, no Rauch/conjugate-point
   duplication, canonical forbidden-token scan, statement fidelity to the acceptance text.
5. **Manual reading** of both mathematical modules, the D12 proof chain, and the two
   authoring-round reviews.

## Adversarial findings

### A. Conclusion-equivalent hypotheses — NONE

Mechanical scan of the full `#check` types (top-level hypothesis positions, arrow-depth
aware) for all 9 headline declarations:

* Model theorems (`euclid_volume_ratio_le_of_ricci_nonneg`,
  `euclid_volumeRatio_div_le_of_ricci_nonneg`, `euclid_volume_doubling_of_ricci_nonneg`,
  `hyp_volume_ratio_le_of_ricci_ge`, `hyp_volume_doubling_of_ricci_ge`,
  `hyp_volume_doubling_d1_k1`): **no hypothesis mentions `radialVolume` at all.** The
  hypotheses are local ODE data (`k` sign, Riccati inequality, differentiability/continuity,
  `EuclideanNormalizedOn`, positivity/vanishing of `A`, `m = dA/A`).
* Interface theorems (`coveringNumber_le_measure_ratio_of_radialBallMeasure`,
  `coveringNumber_le_of_radialBallMeasure_doubling`,
  `coveringNumber_le_of_ricci_nonneg_radialBallMeasure`): **no hypothesis mentions
  `coveringNumber`** (the conclusion head). `hpos : 0 < radialVolume A (r/2)` mentions the
  numerator symbol but is a non-collapsing positivity side condition, not the conclusion.
* `coveringNumber_le_of_radialBallMeasure_doubling` takes the halving-form doubling
  `hdbl : ∀ s, radialVolume A s ≤ C · radialVolume A (s/2)` as an explicit **interface
  input** (its docstring says so); its conclusion is the covering-number bound `≤ C³K`, a
  different statement. The composite theorem does **not** assume `hdbl`: it derives the three
  dyadic radial-volume inequalities `4r→2r→r→r/2` from the Riccati hypotheses via
  `euclid_volume_doubling_of_ricci_nonneg` and then calls
  `coveringNumber_le_of_dyadic_doubling`. Verified in the source and by the empty
  `hypotheses_mentioning_conclusion_head` list for the composite.
* Bishop–Gromov is **derived**, not assumed: `bishopGromov_volume_le` reduces to
  `bishopGromovVolumeRatio ← volumeRatio_antitone ← areaRatio_antitone_of_logDeriv_le ←
  riccati_le_of_singular_normalization`. The normalization hypothesis is only
  `|m t − d/t| ≤ C` near `0`.

### B. Non-vacuity / witnesses — GENUINE, with one documented informal step

* Requirement (2) witness is **kernel-checked**: `euclidModel_hypotheses_witness` instantiates
  every hypothesis of `euclid_volume_doubling_of_ricci_nonneg` with
  `(k, m, dm, A, dA, C, t₀) = (0, d/t, −d/t², t^d, d·t^{d−1}, 0, T)`, and
  `euclidModel_volume_doubling_closedForm` shows the constant `2^(d+1)` is *attained*.
  The `d = 1` numeric instance `2 = 2²·(1/2)` is kernel-checked.
* Hyperbolic witness kernel-checked: `hypModel_doubling_witness` meets all 27 hypotheses;
  the evaluated `d = 1`, `κ = 1` equality `V̄(2s) = 2(cosh s + 1)V̄(s)` is kernel-checked.
* Interface-alone witness kernel-checked: `isRadialBallMeasure_real_witness` proves
  `IsRadialBallMeasure volume (fun _ => 2)` on `ℝ`.
* **Joint** realisation of `IsRadialBallMeasure` and the scalar hypotheses is recorded as an
  explicit **informal** witness (snowflake metric on `ℝ`, `A(t) = 4|t|`, Lebesgue). I
  re-derived it by hand and re-checked it numerically (Simpson integration of `4|t|` against
  `2s|s|` at positive and negative radii; ball measure `2s²` vs `ofReal(2s|s|)`; Riccati
  equality `−1/t² + 1/t² = 0`; `m = dA/A`): all consistent. The source text labels this
  construction informal and non-kernel-checked. This is an honest limitation, not an
  overclaim; the acceptance requirement for a non-vacuous witness is met by the
  kernel-checked Euclidean/hyperbolic witnesses above.

### C. Manifold overclaim — NONE

* No declaration type in either new module mentions `Manifold`, `Riemannian`,
  `ChartedSpace`, `TangentBundle`, `IsManifold`, `VectorBundle`, or `SmoothManifold`
  (mechanical scan over all 34 fresh `#check` types and over the comment/string-stripped
  sources).
* The only measure-theoretic declarations are on an abstract
  `{X} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]` with an arbitrary
  `μ : Measure X`; `IsRadialBallMeasure` is a `def` (an interface predicate), and all
  theorems using it are conditional implications. The module header, the docstrings, the gap
  section, and the result card all state that no manifold, no Riemannian volume, no sphere
  density and no coarea formula is constructed, and that U9's manifold half remains open.
* The `ω_{n−1}` discussion is explicitly motivational/conditional and cancels in the ratios.

### D. Duplication / forbidden constructs — NONE

* No use of `conjugate_point_bound` or Rauch-type results in either new file (mechanical
  scan of stripped sources).
* Canonical comment/string-aware D5 scanner over the four new files: 0 hard matches
  (`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`).
* No `constant`, `opaque`, `@[implemented_by]`, `set_option`, `partial`, or `@[extern]`.
* Negative control in `negcontrol/NegativeControl.lean` still detects both `sorryAx` and the
  unapproved `native_decide` axiom.

### E. Labelling and hypothesis lists — MET

Every one of the 36 declarations (13 Euclidean/interface + 21 public hyperbolic + 2 private
hyperbolic helpers) is paired with a docstring containing exactly one `**Class:**` label from
the approved set; all analytic hypotheses are listed explicitly (definitions state
"Analytic hypotheses: none"). There is no manifold-labelled declaration because there is no
manifold-level statement.

### F. Statement fidelity to the acceptance text — MET

Canonicalised comparison of the compiled signatures against the required forms:

* `radialVolume A R ≤ (R / r) ^ (d + 1) * radialVolume A r` ✔
  (`euclid_volume_ratio_le_of_ricci_nonneg`, `d > 0`, `0 < r ≤ R ≤ T`);
* `radialVolume A (2 * s) ≤ 2 ^ (d + 1) * radialVolume A s` ✔
  (`euclid_volume_doubling_of_ricci_nonneg`);
* hyperbolic: `radialVolume A R ≤ (V̄ R / V̄ r) · radialVolume A r` with
  `V̄ = radialVolume (hypModelA d κ)` ✔, doubling with the explicit scale-dependent ratio ✔,
  and the evaluated `2(cosh s + 1)` form for `d = 1`, `κ = 1` ✔;
* `IsRadialBallMeasure μ A : ∀ x s, μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)`
  ✔, with discharge theorems mapping it onto `hlower`, the measure term of
  `coveringNumber_le_measure_ratio`, and `hdouble`/`hcomp` of
  `coveringNumber_le_of_measure_doubling`. The token `hupper` does not occur in the consumed
  round-3 files; the honest mapping (lower side vs upper/comparability side) is documented.

### G. Residual limitations (reported, not defects)

1. The hyperbolic closed form for general `d` is the explicit model ratio
   `V̄ R / V̄ r` (no elementary antiderivative of `sinh^d` is claimed); it is fully evaluated
   only for `d = 1`, `κ = 1`. This is the honest content of "hyperbolic closed form".
2. The joint interface+scalar witness is informal (item B).
3. `IsRadialBallMeasure` is strictly stronger than the comparability the covering-number
   theorems need (exact centre-independent profile vs two-sided comparability); this is
   documented in the gap section.
4. Redundant hypotheses (`hC` from `hdκC`; `hT` from `ht₀T`; `hsT` from `hs, h2s`) mirror the
   D12 signature; no weakening.
5. No derivation of the Riccati inequality from a Ricci-tensor bound; the manifold
   construction (sphere density, coarea, curvature→Riccati, centre comparability) is the open
   part of U9 and is not claimed.

## Verdict

**No BLOCKER and no MAJOR finding.** Acceptance criteria (1)–(4) are met at the
scalar/model + documented conditional metric–measure interface level, with kernel-checked
declarations, non-vacuous witnesses, a forced fresh compile (exit 0, zero warnings),
fail-closed axiom cones exactly `{propext, Classical.choice, Quot.sound}`, byte-identical
provenance, no conclusion-equivalent hypothesis, and no manifold overclaim. U9's manifold
half remains open and is not claimed.

`evidence/independent-acceptance.json` — 9/9 gates PASS
(`INDEPENDENT-ACCEPTANCE: PASS`).
