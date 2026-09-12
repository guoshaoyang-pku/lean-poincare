/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — cross-check: the Sturm engine bound versus `conjugate_point_bound`

This round's `Poincare.L4.GeodesicComparison.conjugate_point_bound`
(`ConjugatePointBound.lean`) proves, under a quantitative Rauch-comparison normalization
(`|u''| ≤ B`, a threshold `t₀` with `B·t₀ ≤ 1/2` and
`(K·max (1/√K) T)·t₀ ≤ 1/2`, continuity of `ddu`, `u 0 = 0`, `u' 0 = 1`, and positivity of
`u` on `(0,T]`), that `T ≤ π/√K`.

The engine-derived `no_positive_solution_past_pi_sqrt` proves the same conclusion from
**strictly fewer hypotheses**: it only needs a `JacobiSolutionOn` on `(0,T)`, `u 0 = 0`,
positivity on `(0,T]`, `K > 0` and `k ≥ K` on `(0,T)`.  This file records the cross-check
in both directions:

* `conjugate_point_bound_via_engine` — the conclusion of `conjugate_point_bound` derived
  from the engine route, under the full hypothesis list of the leader theorem; this shows
  the two results are consistent and that the quantitative hypotheses are removable.
* `conjugate_point_bound_cross_check` — the leader theorem itself, invoked on the same data,
  confirming that both routes prove the identical proposition.
* `sharpened_witness`, `witness_agreement` — the explicit non-vacuous instance
  `k = 2`, `K = 1`, `T = 3/2` (the leader's own witness data): both routes give
  `3/2 ≤ π/√1`.

`conjugate_point_bound` is neither assumed as a hypothesis nor re-proved as the main
statement; it is used only here, as an independent check on the sharpened bound.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacing
import Poincare.L4.GeodesicComparison.ConjugatePointBound

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- **The leader's conclusion from the engine route.**  Every hypothesis of
`conjugate_point_bound` is accepted (including the quantitative normalization ones), and the
conclusion is derived from `no_positive_solution_past_pi_sqrt`, which does not use them.
Hence the quantitative Rauch hypotheses are not needed for the positivity bound. -/
theorem conjugate_point_bound_via_engine {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (_hBnn : 0 ≤ B) (_ht₀ : 0 < t₀) (_ht₀T : t₀ ≤ T) (_hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (_hdducont : ContinuousOn ddu (Icc 0 T))
    (_hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (_hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (_hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T ≤ Real.pi / Real.sqrt K :=
  no_positive_solution_past_pi_sqrt hT h hu0 hpos hK hk

/-- **Independent confirmation.**  The already-proved `conjugate_point_bound` invoked on the
same data: both routes establish the identical inequality. -/
theorem conjugate_point_bound_cross_check {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T ≤ Real.pi / Real.sqrt K :=
  conjugate_point_bound hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hpos hK hk hBmodel

/-- **Explicit non-vacuous witness for the engine route.**  On the leader's witness data
(`k = 2`, `K = 1`, `T = 3/2`, `u = jacobiSol 2`), the sharpened theorem gives
`3/2 ≤ π/√1`. -/
theorem sharpened_witness : (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 := by
  have hsqrt2_lt_two : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (3 / 2), 0 < jacobiSol 2 t := by
    intro t ht
    rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine jacobiSolSphere_pos (by norm_num : (0 : ℝ) < 2) ht.1 ?_
    have h1 : Real.sqrt 2 * t ≤ Real.sqrt 2 * (3 / 2) :=
      mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 2)
    nlinarith [Real.pi_gt_three]
  exact no_positive_solution_past_pi_sqrt (T := 3 / 2) (K := 1) (k := fun _ : ℝ => 2)
    (u := jacobiSol 2) (du := jacobiDeriv 2) (ddu := fun t => -(2 * jacobiSol 2 t))
    (by norm_num) (modelJacobiSolutionOn 2 (3 / 2)) (jacobiSol_zero 2) hpos (by norm_num)
    (fun t _ => by norm_num)

/-- **Witness agreement.**  Both routes give the same bound on the explicit instance. -/
theorem witness_agreement :
    (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 ∧ (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 :=
  ⟨conjugate_point_bound_witness, sharpened_witness⟩

end Poincare.L4.GeodesicComparison
