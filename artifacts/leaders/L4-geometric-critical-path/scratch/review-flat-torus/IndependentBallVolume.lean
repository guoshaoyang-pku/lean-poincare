/-
REVIEWER SCRATCH — adversarial independent re-derivation.  Not part of the release tree.

This file re-derives, from mathlib alone (it does NOT import
`Poincare.L4.Compactness.FlatTorusGrowth`), the exact closed-ball volume of the flat
2-torus `AddCircle 1 × AddCircle 1` in the max product metric.

Two independent derivations are given:

* `volume_closedBall_torus`  : via `Measure.volume_eq_prod` + `Measure.prod_prod` +
  mathlib's `AddCircle.volume_closedBall` (centre-independent);
* `volume_closedBall_torus_zero_center` : a *from-scratch* re-derivation for the centre
  `(0,0)` built on `volume_closedBall_circle_fundamental`, which computes the circle ball
  volume from the fundamental-domain theorem `AddCircle.add_projection_respects_measure`
  and `Real.volume_Icc`/`Real.volume_Ioc`, i.e. **without** using
  `AddCircle.volume_closedBall`.

All constants are checked numerically at `s = -1, 0, 1/4, 1/3, 1/2, 3/4`.
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

open scoped Topology ENNReal NNReal
open Set Metric MeasureTheory

noncomputable section

namespace ReviewFlatTorus

/-- The flat 2-torus as a type (definitionally identical to the one in M2). -/
abbrev T2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-! ## 1. The metric: closed balls are products of arcs -/

/-- In the max product metric the closed ball is the product of the two closed balls.
This is where the choice of metric enters: `x ∈ closedBall z s ↔ max (dist x.1 z.1)
(dist x.2 z.2) ≤ s`. -/
theorem closedBall_prod_max (x : T2) (s : ℝ) :
    closedBall x s = closedBall x.1 s ×ˢ closedBall x.2 s :=
  (closedBall_prod_same x.1 x.2 s).symm

/-! ## 2. First (mathlib-formula) derivation of the torus ball volume -/

/-- Exact closed-ball volume, first derivation. -/
theorem volume_closedBall_torus (x : T2) (s : ℝ) :
    volume (closedBall x s) = ENNReal.ofReal (min 1 (2 * s)) ^ 2 := by
  rw [closedBall_prod_max, Measure.volume_eq_prod, Measure.prod_prod,
    AddCircle.volume_closedBall, AddCircle.volume_closedBall, pow_two]

/-- Total mass of the torus is `1`. -/
theorem volume_univ_torus : volume (univ : Set T2) = 1 := by
  rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod,
    AddCircle.measure_univ]
  norm_num

/-! ## 3. Case checks requested by the review: `s < 0` and `s ≥ 1/2` -/

/-- Negative radii give measure zero on both sides. -/
theorem volume_closedBall_torus_neg (x : T2) {s : ℝ} (hs : s < 0) :
    volume (closedBall x s) = 0 := by
  rw [volume_closedBall_torus, min_eq_right (by linarith : 2 * s ≤ 1),
    ENNReal.ofReal_eq_zero.mpr (by linarith : (2 : ℝ) * s ≤ 0), zero_pow (by norm_num)]

/-- Radii at least the injectivity radius `1/2` give the total mass `1`. -/
theorem volume_closedBall_torus_big (x : T2) {s : ℝ} (hs : 1 / 2 ≤ s) :
    volume (closedBall x s) = 1 := by
  rw [volume_closedBall_torus, min_eq_left (by linarith : (1 : ℝ) ≤ 2 * s),
    ENNReal.ofReal_one, one_pow]

/-- At `s = 0` the ball is a point and has measure `0`, consistently with the formula. -/
theorem volume_closedBall_torus_zero (x : T2) : volume (closedBall x 0) = 0 := by
  rw [volume_closedBall_torus]
  norm_num

/-! ## 4. Numeric cross-checks (the constants that matter for the growth claim) -/

theorem volume_quarter (x : T2) :
    volume (closedBall x (1 / 4)) = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [volume_closedBall_torus, show min 1 (2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num,
    pow_two, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]

/-- The same value written as `1/4` in `ℝ≥0∞`. -/
theorem volume_quarter' (x : T2) : volume (closedBall x (1 / 4)) = (1 / 4 : ℝ≥0∞) := by
  rw [volume_quarter,
    show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num

theorem volume_half (x : T2) : volume (closedBall x (1 / 2)) = 1 :=
  volume_closedBall_torus_big x le_rfl

theorem volume_three_quarters (x : T2) : volume (closedBall x (3 / 4)) = 1 :=
  volume_closedBall_torus_big x (by norm_num)

theorem volume_third (x : T2) :
    volume (closedBall x (1 / 3)) = ENNReal.ofReal (4 / 9 : ℝ) := by
  rw [volume_closedBall_torus, show min 1 (2 * (1 / 3 : ℝ)) = 2 / 3 by norm_num,
    pow_two, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  rw [show (2 / 3 : ℝ) * (2 / 3) = 4 / 9 by norm_num]

theorem volume_neg_one (x : T2) : volume (closedBall x (-1)) = 0 :=
  volume_closedBall_torus_neg x (by norm_num)

/-! ## 5. Second, fully independent derivation of the circle ball volume

`AddCircle.add_projection_respects_measure` says that for the fundamental domain
`Ioc (-(1/2)) (1/2)` the measure of a measurable set downstairs equals the Lebesgue
measure of its preimage intersected with the fundamental domain.  We compute that
preimage explicitly. -/

/-- For a representative `y` in the fundamental domain `(-1/2, 1/2)`, the distance to `0`
in `AddCircle 1` is `|y|`. -/
theorem norm_coe_eq_abs_of_mem_Ioc {y : ℝ} (hy : y ∈ Ioc (-(1 / 2) : ℝ) (1 / 2)) :
    ‖(y : AddCircle (1 : ℝ))‖ = |y| := by
  rw [AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero, abs_one]
  rw [abs_le]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- Preimage of a small circle ball inside the fundamental domain. -/
theorem coe_preimage_inter_of_lt {r : ℝ} (hr : r < 1 / 2) :
    (↑) ⁻¹' closedBall (0 : AddCircle (1 : ℝ)) r ∩ Ioc (-(1 / 2) : ℝ) (1 / 2) =
      Icc (-r) r := by
  ext y
  constructor
  · rintro ⟨hy, hyI⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero] at hy
    rw [norm_coe_eq_abs_of_mem_Ioc hyI, abs_le] at hy
    exact ⟨hy.1, hy.2⟩
  · intro hy
    rw [mem_Icc] at hy
    have hyI : y ∈ Ioc (-(1 / 2) : ℝ) (1 / 2) :=
      ⟨by linarith [hy.1], by linarith [hy.2, hr]⟩
    refine ⟨?_, hyI⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero,
      norm_coe_eq_abs_of_mem_Ioc hyI, abs_le]
    exact ⟨hy.1, hy.2⟩

/-- Preimage of a large circle ball inside the fundamental domain: everything. -/
theorem coe_preimage_inter_of_ge {r : ℝ} (hr : 1 / 2 ≤ r) :
    (↑) ⁻¹' closedBall (0 : AddCircle (1 : ℝ)) r ∩ Ioc (-(1 / 2) : ℝ) (1 / 2) =
      Ioc (-(1 / 2) : ℝ) (1 / 2) := by
  ext y
  constructor
  · exact fun h => h.2
  · intro hy
    refine ⟨?_, hy⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero,
      norm_coe_eq_abs_of_mem_Ioc hy, abs_le]
    constructor <;> linarith [hy.1, hy.2, hr]

/-- **Circle ball volume from the fundamental domain**, for every real radius; this does
not use `AddCircle.volume_closedBall`. -/
theorem volume_closedBall_circle_fundamental (r : ℝ) :
    volume (closedBall (0 : AddCircle (1 : ℝ)) r) = ENNReal.ofReal (min 1 (2 * r)) := by
  have h := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) (-(1 / 2))
    (U := closedBall (0 : AddCircle (1 : ℝ)) r) measurableSet_closedBall
  rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num] at h
  rw [h]
  by_cases hr2 : r < 1 / 2
  · rw [coe_preimage_inter_of_lt hr2, Real.volume_Icc,
      min_eq_right (by linarith : 2 * r ≤ 1), show r - -r = 2 * r by ring]
  · rw [coe_preimage_inter_of_ge (not_lt.mp hr2), Real.volume_Ioc,
      min_eq_left (by linarith : (1 : ℝ) ≤ 2 * r),
      show (1 / 2 : ℝ) - -(1 / 2) = 1 by norm_num]

/-- **Second, independent derivation of the torus ball volume at the origin** (product
decomposition plus the fundamental-domain circle computation, no use of
`AddCircle.volume_closedBall`).  Centre-independence is covered by
`volume_closedBall_torus` above. -/
theorem volume_closedBall_torus_zero_center (s : ℝ) :
    volume (closedBall ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ))) s) =
      ENNReal.ofReal (min 1 (2 * s)) ^ 2 := by
  rw [closedBall_prod_max, Measure.volume_eq_prod, Measure.prod_prod, pow_two,
    volume_closedBall_circle_fundamental s]

end ReviewFlatTorus
