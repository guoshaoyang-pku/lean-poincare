# L4-geometric-critical-path — result card

- **Task id:** `L4-geometric-critical-path`
- **Worktree:** `longrun/worktrees/leaders/L4-geometric-critical-path`
- **Lane:** builder · **Invocation:** round 3 (rounds 1–2 artifacts preserved; nothing restarted)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`)
- **Generated:** 2026-09-12 (local) · **Verdict:** **TASK_DONE** (requests independent acceptance; **no named blocker is claimed closed**; this is not a claim that the Poincaré conjecture is proved)

## 0. Bottom line

Round 3 adds **31 kernel-checked declarations** in three files, each with a clear semantic class,
non-vacuous witnesses, a downstream consumer, and full verification evidence:

1. **U9 — metric doubling ⟹ uniform covering bounds** (`Poincare/L4/Compactness/DoublingToCovers.lean`):
   a finite cover-refinement induction turning "every ball of radius `2r` is covered by `n` points
   at radius `r`" into explicit bounds `coveringNumber (R/2^k) (closedBall x (2R)) ≤ n^(k+2)`, plus
   a downstream consumer chaining it with the round-2 GH-stability theorem.
2. **U9 — volume growth ⟹ packing/covering bounds** (`Poincare/L4/Compactness/MeasureGrowthCovers.lean`):
   the Bishop–Gromov-style disjoint-ball counting argument, the single-scale and all-scales
   doubling bounds with explicit constants, a bridge consuming mathlib's
   `IsUnifLocDoublingMeasure` at a single admissible scale, a natural-number (`ℕ∞`) form matching
   the interface of file 1, and a machine-checked Lebesgue-measure witness.
3. **U3 — Sturm zero counting** (`Poincare/L4/GeodesicComparison/SturmZeroCount.lean`):
   a constructed shifted constant-curvature model (Jacobi-solution structure, derivatives,
   positivity) consuming D12's abstract Sturm engine, with the strict-excess zero theorem, the
   anchored form at `0`, the dichotomy (no zero ⟹ `k = K`), an explicit zero witness, and a
   formalized necessity-of-strictness counterexample.

All 81 L4 declarations and the 8 D13 headline declarations pass the fail-closed axiom audit with
cones exactly `[propext, Classical.choice, Quot.sound]`; a planted `axiom`-based negative control
is detected; the forbidden-token scan is clean.  `lake build` exits 0 and every authored L4 file
compiles individually.

**The five named blockers in scope (U3, U7, U9, I4, I5) are all still open.**  Exact
blocker-closure list: **empty**.  Nothing here should be counted as a closure.

## 1. Named-blocker status (exact)

| blocker | round-3 advance | remaining (not closed) |
| --- | --- | --- |
| **U3** geodesics/exp map | constructed shifted-model Sturm zero counting with a real consumer of D12 `sturm_zero_comparison`: strict curvature excess forces a zero strictly before the model zero (`exists_jacobi_zero_of_curvature_gt`), the anchored form and dichotomy, witnesses including `sin(√2·π/√2) = 0`, and a formalized counterexample showing the strictness hypothesis is needed | geodesic spray `∇_{γ'}γ' = 0`, exp map, manifold Jacobi fields, shape-operator Riccati equation, Cauchy–Schwarz, identification of `u` with a geodesic-sphere density. Mathlib at the pin has no geodesic/exp/parallel-transport/curvature object. |
| **U7** volume form/IBP | unchanged this round (round 2: D13 headline re-audit, Dirichlet-energy sign, packaged self-adjointness) | mathlib-manifold → `SmoothOverlapAtlas` bridge, manifold smooth partition of unity, closed-manifold `v ≡ 1`, Stokes/boundary measure, oriented volume form. |
| **U9** compactness | **metric doubling ⟹ covering bounds** (`DoublingToCovers.lean`, 6 decls, incl. the GH transfer consumer) and **measure growth ⟹ packing/covering bounds** (`MeasureGrowthCovers.lean`, 14 decls: disjoint-ball counting, single-scale `C³·K`, dyadic and all-scales forms with explicit exponents, mathlib-class bridge, `ℕ∞` natural bound, Lebesgue witness) | curvature bound + κ-non-collapsing ⟹ the *uniform* doubling hypothesis (Bishop–Gromov realized as a ball measure); pointed GH convergence; harmonic coordinates/elliptic regularity; C^∞ limit upgrade. |
| **I4** entropy Props | unchanged | the five D3 `…Statement` Props; unrestricted forms are kernel-checked false. |
| **I5** κ/recognition | unchanged | κ-noncollapsing K1–K7 and recognition S1–S5 remain statement-only. |

## 2. What was constructed (31 declarations, all kernel-checked)

Semantic classes: **P** = proved (unconditional), **C** = conditional on explicit hypotheses,
**M** = model (concrete data, witnessed), **S** = statement-only (none new this round),
**U** = upstream source claim (none: all consumed D12 results are Lean theorems, not source claims).

### 2a. `Poincare/L4/Compactness/DoublingToCovers.lean` (6 decls)

| declaration | class | content |
| --- | --- | --- |
| `IsCover.finset_biUnion` | P | composition of a `δ`-cover with `ε`-covers of its `δ`-balls |
| `exists_finset_isCover_card_le` | P | from `coveringNumber ε A ≤ n` (n : ℕ) obtain a `Finset` cover with `card ≤ n` (mathlib `exists_set_encard_eq_coveringNumber`) |
| `exists_finset_cover_card_le_of_doubling` | C | doubling induction: a cover of `closedBall x (2R)` at radius `R/2^k` with `≤ n^(k+1)` centres |
| `coveringNumber_le_of_doubling` | C | `coveringNumber (R/2^k) (closedBall x (2R)) ≤ n^(k+2)`; the external→internal cover conversion costs one halving and one factor of `n` |
| `coveringNumber_le_of_doubling_of_le` | C | the same bound for every `ε ≥ R/2^k` |
| `coveringNumber_univ_le_of_ghDist_lt_of_doubling` | C | **downstream consumer**: `ghDist X Y < r`, `2r+δ<ε`, `R/2^k ≤ δ`, doubling on `Y` ⟹ `coveringNumber ε univ_X ≤ n^(k+2)` |

### 2b. `Poincare/L4/Compactness/MeasureGrowthCovers.lean` (14 decls)

| declaration | class | content |
| --- | --- | --- |
| `encard_le_of_forall_finset_card_le` | P | finite-subset cardinality bounds imply an `encard` bound (via `Set.Infinite.exists_subset_ncard_eq`) |
| `finset_card_mul_measure_le` | C | disjoint `(r/2)`-balls: `(s.card : ℝ≥0∞)·m ≤ μ(closedBall x (4r))` for finite `r`-separated `s ⊆ closedBall x (2r)` |
| `encard_mul_measure_le_of_isSeparated` | C | the same for arbitrary (possibly infinite) separated sets; infinity forces `μ = ⊤` |
| `packingNumber_le_measure_ratio` | C | `packingNumber r (closedBall x (2r)) ≤ μ(closedBall x (4r))/m` |
| `packingNumber_mul_measure_le` | C | unconditional multiplicative form `N_pack·m ≤ μ(closedBall x (4r))` |
| `coveringNumber_mul_measure_le` | C | same for `N_cover` (covering ≤ packing) |
| `coveringNumber_le_measure_ratio` | C | `coveringNumber r (closedBall x (2r)) ≤ μ(closedBall x (4r))/m` |
| `coveringNumber_le_of_dyadic_doubling` | C | the single-scale bound from the three dyadic inequalities only |
| `coveringNumber_le_of_measure_doubling` | C | halving-form doubling chain ⟹ `coveringNumber r (closedBall x (2r)) ≤ C³·K` |
| `coveringNumber_le_of_unifLocDoublingMeasure` | C | **consumes mathlib's `IsUnifLocDoublingMeasure`** at a single scale below `scalingScaleOf μ 4`, giving `≤ (scalingConstantOf μ 4)³·K` |
| `real_coveringNumber_doubling_witness` | M | machine-checked instance on `ℝ` with Lebesgue measure: `coveringNumber 1 (closedBall x 2) ≤ 8` (true value 2) |
| `measure_closedBall_le_pow_mul` | C | dyadic iteration `μ(closedBall y s) ≤ C^n·μ(closedBall y (s/2^n))` |
| `coveringNumber_le_of_measure_doubling_allScales` | C | explicit all-scales bound `coveringNumber s (closedBall x (2s)) ≤ C³·(K·C^n)` for `r/2^n ≤ s/2`, `s ≤ r` |
| `coveringNumber_le_floor_of_measure_doubling_allScales` | C | the natural-number (`ℕ∞`) form `≤ ⌊C³·(K·C^n)⌋ₑ`, the shape of file 1's uniform hypothesis |

### 2c. `Poincare/L4/GeodesicComparison/SturmZeroCount.lean` (11 decls + 3 defs)

| declaration | class | content |
| --- | --- | --- |
| `hasDerivAtR_sturmModel` | P | derivative of the shifted model `sin (√K(t-a))` |
| `hasDerivAtR_sturmModelDeriv` | P | second derivative (`√K·√K = K`, needs `K ≥ 0`) |
| `sturmModel_jacobiSolutionOn` | P | the shifted model is a `JacobiSolutionOn` for constant curvature `K ≥ 0` |
| `sturmModel_pos` | P | positivity before the first zero `a + π/√K` |
| `exists_jacobi_zero_of_curvature_gt` | C | `k ≥ K > 0` on `[a,b]`, `u a = 0`, `√K(b-a) = π`, strict excess `k > K` inside ⟹ `∃ c ∈ (a,b), u c = 0` (consumes D12 `sturm_zero_comparison`) |
| `exists_jacobi_zero_before_pi_sqrt` | C | anchored at `0`: strict excess in `(0, π/√K)` forces a zero there |
| `eq_curvature_of_no_jacobi_zero_before_pi_sqrt` | C | dichotomy: no zero in `(0, π/√K)` ⟹ `k = K` identically there |
| `sin_sqrt_two_explicit_zero` | M | `π/√2 ∈ (0,π)` and `sin(√2·π/√2) = 0` |
| `sturm_zero_curvature_witness` | M | the `k = 2`, `K = 1` instance satisfies every hypothesis and yields a zero in `(0,π)` |
| `sin_no_zero_in_Ioo_zero_pi` | P | `sin` has no zero in `(0,π)` |
| `sturm_zero_strictness_necessary` | M | formalized counterexample: `k ≡ 1`, `u = sin` on `(0,π)` satisfies every hypothesis *except* the strict excess, and the conclusion fails — the strictness hypothesis is not removable |

The three definitions (`sturmModel`, `sturmModelDeriv`, `sturmModelSecondDeriv`) are data, not
claims; every theorem about them is audited.

## 3. Downstream checked use (constructed input → consumer)

1. `exists_set_encard_eq_coveringNumber` → `exists_finset_isCover_card_le` →
   `exists_finset_cover_card_le_of_doubling` → `coveringNumber_le_of_doubling`.
2. `coveringNumber_le_of_doubling` + `coveringNumber_anti` + the set equality
   `closedBall y (2R) = univ` + `CoveringStability.coveringNumber_le_of_ghDist_lt`
   → `coveringNumber_univ_le_of_ghDist_lt_of_doubling`.
3. `measure_biUnion_finset` + strict `IsSeparated` disjointness → `finset_card_mul_measure_le`
   → `encard_le_of_forall_finset_card_le` → `encard_mul_measure_le_of_isSeparated`
   → `packingNumber_le_measure_ratio` → `coveringNumber_le_measure_ratio`.
4. Dyadic inequalities → `coveringNumber_le_of_dyadic_doubling` →
   `coveringNumber_le_of_measure_doubling`; mathlib
   `IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul` at the three scales →
   `coveringNumber_le_of_unifLocDoublingMeasure`.
5. `measure_closedBall_le_pow_mul` + `coveringNumber_le_of_measure_doubling` →
   `coveringNumber_le_of_measure_doubling_allScales` → (via `ENat.le_floor`)
   `coveringNumber_le_floor_of_measure_doubling_allScales` — the shape of
   `DoublingToCovers.hN`, with uniformity in the centre/scale explicitly left as the remaining
   geometric input.
6. D12 `sturm_zero_comparison` + the constructed `sturmModel_jacobiSolutionOn` /
   `sturmModel_pos` / endpoint derivative → `exists_jacobi_zero_of_curvature_gt` →
   `exists_jacobi_zero_before_pi_sqrt` → `eq_curvature_of_no_jacobi_zero_before_pi_sqrt`;
   `sin_no_zero_in_Ioo_zero_pi` + the model instance → `sturm_zero_strictness_necessary`.

## 4. Expanded hypotheses and semantic honesty

* Every conditional theorem lists its analytic hypotheses; no hypothesis is
  conclusion-equivalent or contradictory (adversarial reviews, §5).  The key non-vacuity checks:
  the doubling hypothesis of file 1 holds on `ℝ` with `n = 3`; the measure hypotheses of file 2
  hold on `ℝ` with Lebesgue measure (`C = 2, m = 1, K = 1`), machine-checked by
  `real_coveringNumber_doubling_witness`; the Sturm hypotheses hold for `k = 2`, `K = 1` on
  `(0,π)` with the explicit zero `π/√2`.
* **Model vs manifold is explicit.**  All three files are scalar/metric/measure-level.  No
  manifold measure, geodesic, exp map, Jacobi field or curvature tensor is constructed or
  claimed.  The U3 header states this; the U9 files state that the curvature →
  (uniform) doubling input is not claimed.
* **Review-driven corrections (round 3).**  The first adversarial review of
  `MeasureGrowthCovers.lean` found, with the mathematics sound, false *claims* in the header
  ("in the form consumed by `DoublingToCovers.lean`"; "the form in which mathlib's
  `IsUnifLocDoublingMeasure` produces doubling inequalities"), an unused import, and an
  over-strong reading of the `hcomp` hypothesis.  All were fixed: the header now states the
  remaining uniformity gap; the mathlib-class claim is backed by the new theorem
  `coveringNumber_le_of_unifLocDoublingMeasure` (single admissible scale); the unused import was
  removed and minimal mathlib imports added; `hcomp` is documented as a reverse-doubling
  comparability hypothesis.  The same review found the round-2-era helper
  `coveringNumber_univ_le_of_subset_univ` trivially true (`univ ⊆ A` forces `A = univ`); it was
  **deleted** and the GH consumer now uses the set equality directly.  The Sturm review found
  only docstring refinements, all applied, and the non-removability of the strictness hypothesis
  is now formalized (`sturm_zero_strictness_necessary`) rather than only argued.
* **Known non-defect gaps recorded:** (i) the literal corollary "`u 0 = 0`, `u' 0 = 1` ⟹ first
  zero `≤ π/√K`" is covered by round 2's `conjugate_point_bound` under stronger hypotheses, not
  restated here; (ii) the in-file Sturm non-vacuity witness uses constant `k = 2` (nonconstant-`k`
  instances were checked numerically by the reviewer only); (iii) `hab : a < b` in the main Sturm
  theorem is redundant given `K > 0` and `√K(b-a) = π`.

## 5. Independent adversarial reviews

Round 2 (all PASS unless noted): `RauchBridge` (witness-coverage gap closed);
`ConstantCurvatureRauch` + `WeightedSelfAdjointness` (novelty overclaim corrected);
`CoveringStability` + corrected `WeightedSelfAdjointness`; `ConstantCurvatureRauchLower` +
`ConjugatePointBound` + integrated theorems (14/14); D13 inventory and mathlib API scout.

Round 3 (independent subagent reviewers, read-only, scratch work outside the worktree):

| scope | outcome |
| --- | --- |
| `DoublingToCovers.lean` + first revision of `MeasureGrowthCovers.lean` | **DoublingToCovers PASS** (no direction/quantifier/scale/circularity defect; machine-checked `ℝ`, `n = 3` instance). **MeasureGrowthCovers PASS on mathematics, FAIL on claims fidelity**: all six then-present theorems true, proven, axiom-clean, hypotheses jointly satisfiable; two false header claims, an unused import and an over-strong `hcomp` reading found. All fixed (§4). |
| `SturmZeroCount.lean` (first revision) | **PASS**, no mathematical or formalization defect; direction/quantifier check faithful, no off-by-one, engine instantiation verified argument-by-argument; independent RK45 numerics (first zero `π/√2`, and tiny-excess cases); confirmed genuinely new relative to round-2 `conjugate_point_bound`.  Minor docstring/redundancy observations O1–O5 recorded and O1–O3 fixed. |
| Re-review of the revised files | **PASS / PASS.**  `DoublingToCovers.lean` PASS: the GH chain is correct after the trivial-lemma deletion and the docstrings match the proofs.  `MeasureGrowthCovers.lean` PASS: all earlier findings fixed and every new declaration verified, including machine-checked non-vacuity of the mathlib-class bridge on `ℝ`/Lebesgue and of the all-scales bound (`C = 2, r = 4, m = 8, K = 1, s = 1, n = 3 ⇒ 64`); the dyadic form, the dyadic iteration, the `C³·(K·Cⁿ)` accounting, the `ℕ∞`-floor form and the multiplicative corollaries were each checked.  Only documentation nits remained; they were applied afterwards (deleted-lemma bullet removed, two docstring rewordings), the proofs being untouched by comment-only edits, and the axiom audit was rerun on the final hashes. |

## 6. Compile evidence

* `cd release && lake build` (whole release) → exit 0, `Build completed successfully (9396 jobs)`
  (`evidence/l4-verify.log`).
* Per-file `lake env lean` sweep over all 13 `.lean` files under `Poincare/L4/` → 13/13 exit 0
  (`SWEEP_FILES=13 SWEEP_FAIL=0`, `evidence/l4-verify.log`).
* Release-wide authored-file sweep: all 513 `.lean` files under `release/` (excluding `.lake`)
  compiled individually with `lake env lean`, four at a time; final run with zero failures
  (`evidence/l4-release-sweep-round3.log`).  An earlier run had a single failure — the file
  being edited at that moment — which was re-run clean.
* Full build log: `evidence/l4-round3-build.log`.

## 7. Axiom evidence (fail-closed)

`python3 tools/l4_axiom_audit.py` → **PASS** (exit 0):
* **81/81 L4 declarations** reported; every cone is exactly
  `[propext, Classical.choice, Quot.sound]`.
* **8/8 D13 headline declarations** re-audited from outside the D13 tree; same cone.
* Planted negative control (`axiom l4NegControlAxiom : False`) **detected** through the same
  checker; the script fails closed if it is not.
* Forbidden-token scan (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`)
  over comment-stripped authored sources: **no hits**.
* Machine-readable report: `evidence/l4_axiom_audit.json`.

## 8. Source hashes (sha256, frozen at card time)

See `evidence/l4_source_hashes.txt`.  Round-3 headline files:

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/Compactness/DoublingToCovers.lean` | `9a8adc9ee12cdc20ac6923a7c6d4f1ee433433fbf310c4248ef7328a4fb53dc4` |
| `release/Poincare/L4/Compactness/MeasureGrowthCovers.lean` | `797afe6968f783163cd3d494b1f00bb15c1e00ca066ee0a556b6b833afcc356c` |
| `release/Poincare/L4/GeodesicComparison/SturmZeroCount.lean` | `5c1d421d3f7528f333c2afa8a2838ce64699ae860692f374081527addc238c4a` |
| `release/Poincare/L4/AxiomAudit.lean` | `3d07e31423843913d628528707ddeebc8c772e9308171848e4017309e6377c23` |
| `release/tools/l4_axiom_audit.py` | `69428f7e1a646ce131effced38fd1a09024a8e7ff10fa62caac901b65b66eee9` |

The two files whose hashes changed after the re-review (`9a8adc9e…`, `797afe69…`) differ from the
reviewed hashes only in the documentation-only edits the re-review requested; `SturmZeroCount.lean`
is byte-identical to its re-reviewed version.

## 9. Remaining blockers and next child tasks

Remaining blockers are listed per named blocker in §1; none is closed.  Child tasks written to
`comms/outbox/` (JSON with `id`, `group_id`, `parent_node`, `deps`, `lane`, `acceptance`,
`host_pool`, `requires_lean`, `max_hours`):

1. `L4-child-ricci-to-doubling` (U9) — instantiate D12's Bishop–Gromov chain with explicit
   constant-curvature models and derive the volume-ratio/doubling bounds; state precisely what
   would realize the radial volume as a ball measure.
2. `L4-child-gh-family-covers` (U9) — lift the pair-level GH transfer to a family in D12's
   `uniformCovers` language.
3. `L4-child-jacobi-zero-interlacing` (U3) — two-sided zero interlacing/spacing with the
   equality case, extending `SturmZeroCount.lean`.

Carried out this round (do not re-dispatch without checking this card):
`L4-C3-doubling-to-covers` (both halves delivered; curvature → doubling remains
`L4-child-ricci-to-doubling`) and `L4-child-sturm-zero-interlacing` (`SturmZeroCount.lean`).
Still open from earlier rounds: `L4-child-pointed-gh-transport` (U9),
`L4-child-d13-semantic-audit` (U7), `L4-C1-geodesic-spray-interface` (U3),
`L4-C2-manifold-atlas-bridge` (U7).  `L4-C4-constant-curvature-rauch` and
`L4-child-conjugate-point-bound` were carried out in round 2.

## 10. Statement of scope

This card requests independent acceptance of the *evidence and artifacts listed above*.  It does
**not** claim that any named blocker is closed, that the manifold-level Rauch theorem is proved,
that a manifold measure or Cheeger–Gromov compactness is available, or that the Poincaré
conjecture is proved in any form.

**TASK_DONE**
