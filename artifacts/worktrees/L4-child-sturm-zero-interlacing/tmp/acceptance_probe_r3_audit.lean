/-
Independent acceptance probe, pass 3 (L4-child-sturm-zero-interlacing).

This probe is NOT part of the deliverable.  It exercises the delivered theorems on
constructed data that the deliverable never uses:

* hand-rolled Jacobi data `u(t) = sin(4t)/4`, `du = cos(4t)`, `ddu = -16u` (curvature 16),
  built from `Real.hasDerivAt_sin` / `Real.hasDerivAt_cos` rather than from the D10
  `jacobiSol` model;
* hand-rolled comparison data `u₂(t) = sin(2t)/2` (curvature 4) for the two-curvature
  interlacing and for the Wronskian monotonicity, with the explicit consequence
  `cos 4t ≤ cos²2t`;
* a two-sided first-zero bracket `π/5 ≤ firstPositiveZero u ≤ π/3` obtained from the
  deliverable's one-sided zero counting (upper bound, `K = 9`) together with the
  complementary leader theorem `no_first_zero_before_pi_sqrt_of_curvature_le`
  (lower bound, `K = 25`) from the read-only input
  `Poincare/L4/GeodesicComparison/TwoSidedSturm.lean`;
* an honest negative control: with `k = 0 < K = 1` and `u = t` the zero-counting
  conclusion fails, so the curvature hypothesis `k ≥ K` is load-bearing.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacing
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck
import Poincare.L4.GeodesicComparison.SturmUniqueness

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 0. Pinned derivative wrappers for `sin` and `cos`

`HasDerivAtR` pins the typeclass instances of `HasDerivAt` (see D12 `Definitions.lean`).
The two wrappers below pin the mathlib lemmas in the probe's import context so that they
compose with the pinned `HasDerivAtR` operations. -/

theorem p3_hasDerivAtR_sin (x : ℝ) : HasDerivAtR Real.sin (Real.cos x) x := by
  simpa using Real.hasDerivAt_sin x

theorem p3_hasDerivAtR_cos (x : ℝ) : HasDerivAtR Real.cos (-Real.sin x) x := by
  simpa using Real.hasDerivAt_cos x

/-! ## 1. Hand-rolled solution with curvature 16 -/

/-- `u(t) = sin(4t)/4`, normalized so that `u 0 = 0`, `u' 0 = 1`. -/
noncomputable def p3u (t : ℝ) : ℝ := Real.sin (4 * t) / 4

/-- First derivative data of `p3u`. -/
noncomputable def p3du (t : ℝ) : ℝ := Real.cos (4 * t)

/-- Second derivative data of `p3u`; equals `-16 * p3u t`. -/
noncomputable def p3ddu (t : ℝ) : ℝ := -(16 * p3u t)

theorem p3_hasDerivAt_u (t : ℝ) : HasDerivAtR p3u (p3du t) t := by
  have h1 : HasDerivAtR (fun s : ℝ => 4 * s) (4 * 1) t := (hasDerivAtR_id t).const_mul 4
  have h2 : HasDerivAtR (fun s : ℝ => Real.sin (4 * s)) (Real.cos (4 * t) * (4 * 1)) t :=
    (p3_hasDerivAtR_sin (4 * t)).comp t h1
  have h3 : HasDerivAtR (fun s : ℝ => Real.sin (4 * s) / 4)
      ((Real.cos (4 * t) * (4 * 1)) / 4) t := h2.div_const 4
  have h4 : (Real.cos (4 * t) * (4 * 1)) / 4 = p3du t := by
    simp [p3du]
  rwa [h4] at h3

theorem p3_hasDerivAt_du (t : ℝ) : HasDerivAtR p3du (p3ddu t) t := by
  have h1 : HasDerivAtR (fun s : ℝ => 4 * s) (4 * 1) t := (hasDerivAtR_id t).const_mul 4
  have h2 : HasDerivAtR (fun s : ℝ => Real.cos (4 * s)) (-Real.sin (4 * t) * (4 * 1)) t :=
    (p3_hasDerivAtR_cos (4 * t)).comp t h1
  have h3 : HasDerivAtR (fun s : ℝ => Real.cos (4 * s)) (-Real.sin (4 * t) * 4) t := by
    simpa using h2
  have h4 : (-Real.sin (4 * t) * 4 : ℝ) = p3ddu t := by
    simp only [p3ddu, p3u]
    ring
  rwa [h4] at h3

/-- The hand-rolled data solves the scalar Jacobi equation with constant curvature `16`
on every interval `(0,T)`. -/
theorem p3_jacobiSolutionOn (T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => (16 : ℝ)) p3u p3du p3ddu 0 T where
  hasDerivAt_u := by intro t _; exact p3_hasDerivAt_u t
  hasDerivAt_du := by intro t _; exact p3_hasDerivAt_du t
  eq_secondDeriv := by intro t _; simp [p3ddu]
  continuousOn_u := by
    show ContinuousOn (fun t : ℝ => Real.sin (4 * t) / 4) (Icc 0 T)
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const 4).continuousOn
  continuousOn_du := by
    show ContinuousOn (fun t : ℝ => Real.cos (4 * t)) (Icc 0 T)
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn

theorem p3u_zero : p3u 0 = 0 := by simp [p3u]

theorem p3du_zero : p3du 0 = 1 := by simp [p3du]

theorem p3u_pi_div_four : p3u (Real.pi / 4) = 0 := by
  simp only [p3u, show 4 * (Real.pi / 4) = Real.pi by ring, Real.sin_pi, zero_div]

/-- Positivity of the hand-rolled solution on its first period. -/
theorem p3u_pos_of_lt_pi_div_four {t : ℝ} (h0 : 0 < t) (h4 : t < Real.pi / 4) :
    0 < p3u t := by
  have h1 : 0 < 4 * t := by linarith
  have h2 : 4 * t < Real.pi := by linarith
  have h3 : 0 < Real.sin (4 * t) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  simp only [p3u]
  linarith

/-! ## 2. The deliverable's zero counting applied to the hand-rolled data -/

/-- Zero counting with `K = 9 ≤ 16 = k`: a zero in `(0, π/3]`. -/
theorem p3_zero_exists_K9 :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 9), p3u c = 0 :=
  exists_jacobi_zero_on_Ioc_pi_sqrt (K := 9) (k := fun _ : ℝ => 16) (by norm_num)
    (fun t _ => by norm_num) (p3_jacobiSolutionOn _) p3u_zero

/-- The normalized form records `u' 0 = 1`. -/
theorem p3_zero_exists_K9_normalized :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 9), p3u c = 0 :=
  exists_jacobi_zero_on_Ioc_pi_sqrt_normalized (K := 9) (k := fun _ : ℝ => 16) (by norm_num)
    (fun t _ => by norm_num) (p3_jacobiSolutionOn _) p3u_zero p3du_zero

/-- The first positive zero is at most `π/√9`. -/
theorem p3_firstZero_le_K9 : firstPositiveZero p3u ≤ Real.pi / Real.sqrt 9 :=
  firstPositiveZero_le_pi_sqrt (K := 9) (k := fun _ : ℝ => 16) (by norm_num)
    (fun t _ => by norm_num) (p3_jacobiSolutionOn _) p3u_zero

/-- The first positive zero is attained (normalization `u' 0 = 1`). -/
theorem p3_firstZero_mem :
    p3u (firstPositiveZero p3u) = 0 ∧ 0 < firstPositiveZero p3u ∧
      ∀ t ∈ Ioo (0 : ℝ) (firstPositiveZero p3u), p3u t ≠ 0 :=
  firstPositiveZero_mem_of_normalized (K := 9) (k := fun _ : ℝ => 16) (by norm_num)
    (fun t _ => by norm_num) (p3_jacobiSolutionOn _) p3u_zero p3du_zero

/-- The horizon form with `H = π/2 ≥ π/3 = π/√9`. -/
theorem p3_zero_exists_horizon_K9 :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 9), p3u c = 0 := by
  have hsqrt9 : Real.sqrt 9 = (3 : ℝ) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine exists_jacobi_zero_of_horizon (K := 9) (H := Real.pi / 2) (k := fun _ : ℝ => 16)
    (by norm_num) (fun t _ => by norm_num) (p3_jacobiSolutionOn _) p3u_zero p3du_zero ?_
  rw [hsqrt9]
  linarith [Real.pi_pos]

/-! ## 3. Exact first zero and the two-sided bracket -/

/-- `firstPositiveZero p3u = π/4` exactly: `sin(4t) > 0` on `(0, π/4)` and
`sin(4·(π/4)) = sin π = 0`.  This is an independent computation with hand-rolled data
(the deliverable computes closed forms only for `Real.sin` and the D10 model). -/
theorem p3_firstZero_eq_pi_div_four : firstPositiveZero p3u = Real.pi / 4 := by
  have hmem : Real.pi / 4 ∈ {t : ℝ | 0 < t ∧ p3u t = 0} :=
    ⟨by linarith [Real.pi_pos], p3u_pi_div_four⟩
  have hbdd : BddBelow {t : ℝ | 0 < t ∧ p3u t = 0} := ⟨0, fun y hy => hy.1.le⟩
  refine le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨_, hmem⟩ ?_)
  intro y hy
  by_contra hlt
  have hy4 : y < Real.pi / 4 := lt_of_not_ge hlt
  exact absurd hy.2 (ne_of_gt (p3u_pos_of_lt_pi_div_four hy.1 hy4))

/-- `π/3 < π/2` and the upper bound `firstPositiveZero p3u ≤ π/3`. -/
theorem p3_firstZero_le_pi_div_three : firstPositiveZero p3u ≤ Real.pi / 3 := by
  have hsqrt9 : Real.sqrt 9 = (3 : ℝ) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simpa [hsqrt9] using p3_firstZero_le_K9

/-- **Lower bound from the complementary leader engine.**  If the first positive zero were
below `π/5 = π/√25`, then it would be a first zero of the curvature-`16` solution strictly
before `π/√25`, contradicting the read-only leader theorem
`no_first_zero_before_pi_sqrt_of_curvature_le` (`TwoSidedSturm.lean`, `k ≤ K = 25`). -/
theorem p3_firstZero_ge_pi_div_five : Real.pi / 5 ≤ firstPositiveZero p3u := by
  by_contra hnot
  have hlt : firstPositiveZero p3u < Real.pi / 5 := lt_of_not_ge hnot
  have hsqrt25 : Real.sqrt 25 = (5 : ℝ) := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨hzero, hpos, hfirst⟩ := p3_firstZero_mem
  have hltHalf : firstPositiveZero p3u < Real.pi / 2 := by
    have h := p3_firstZero_le_pi_div_three
    linarith [Real.pi_pos]
  refine no_first_zero_before_pi_sqrt_of_curvature_le (K := 25) (k := fun _ : ℝ => 16)
    (b := Real.pi / 2) (c := firstPositiveZero p3u) (by norm_num) ?_
    (fun t _ => by norm_num) (p3_jacobiSolutionOn _) ⟨hpos, hltHalf⟩ p3u_zero hzero hfirst
  rw [hsqrt25]
  nlinarith [hlt]

/-- **Two-sided bracket from two independent engines**: the deliverable's one-sided zero
counting (`K = 9 ≤ k = 16`) and the leader's complementary no-first-zero theorem
(`k = 16 ≤ K = 25`) pin the first positive zero of the hand-rolled solution into
`[π/5, π/3]`, and the exact value `π/4` lies strictly inside. -/
theorem p3_two_sided_bracket :
    Real.pi / 5 ≤ firstPositiveZero p3u ∧ firstPositiveZero p3u ≤ Real.pi / 3 ∧
      Real.pi / 5 < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 3 :=
  ⟨p3_firstZero_ge_pi_div_five, p3_firstZero_le_pi_div_three,
    by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The bracket is realized exactly at `π/4`, so it is non-vacuous and the two-sided
statement is strictly stronger than either one-sided bound. -/
theorem p3_bracket_sharp :
    Real.pi / 5 ≤ firstPositiveZero p3u ∧ firstPositiveZero p3u = Real.pi / 4 ∧
      firstPositiveZero p3u ≤ Real.pi / 3 :=
  ⟨p3_firstZero_ge_pi_div_five, p3_firstZero_eq_pi_div_four, p3_firstZero_le_pi_div_three⟩

/-! ## 4. Hand-rolled comparison solution with curvature 4 and the engine's interlacing -/

/-- `u₂(t) = sin(2t)/2`: zeros at `0` and `π/2`, positive in between. -/
noncomputable def p3u2 (t : ℝ) : ℝ := Real.sin (2 * t) / 2

noncomputable def p3du2 (t : ℝ) : ℝ := Real.cos (2 * t)

noncomputable def p3ddu2 (t : ℝ) : ℝ := -(4 * p3u2 t)

theorem p3_hasDerivAt_u2 (t : ℝ) : HasDerivAtR p3u2 (p3du2 t) t := by
  have h1 : HasDerivAtR (fun s : ℝ => 2 * s) (2 * 1) t := (hasDerivAtR_id t).const_mul 2
  have h2 : HasDerivAtR (fun s : ℝ => Real.sin (2 * s)) (Real.cos (2 * t) * (2 * 1)) t :=
    (p3_hasDerivAtR_sin (2 * t)).comp t h1
  have h3 : HasDerivAtR (fun s : ℝ => Real.sin (2 * s) / 2)
      ((Real.cos (2 * t) * (2 * 1)) / 2) t := h2.div_const 2
  have h4 : (Real.cos (2 * t) * (2 * 1)) / 2 = p3du2 t := by simp [p3du2]
  rwa [h4] at h3

theorem p3_hasDerivAt_du2 (t : ℝ) : HasDerivAtR p3du2 (p3ddu2 t) t := by
  have h1 : HasDerivAtR (fun s : ℝ => 2 * s) (2 * 1) t := (hasDerivAtR_id t).const_mul 2
  have h2 : HasDerivAtR (fun s : ℝ => Real.cos (2 * s)) (-Real.sin (2 * t) * (2 * 1)) t :=
    (p3_hasDerivAtR_cos (2 * t)).comp t h1
  have h3 : HasDerivAtR (fun s : ℝ => Real.cos (2 * s)) (-Real.sin (2 * t) * 2) t := by
    simpa using h2
  have h4 : (-Real.sin (2 * t) * 2 : ℝ) = p3ddu2 t := by
    simp only [p3ddu2, p3u2]
    ring
  rwa [h4] at h3

theorem p3u2_jacobiSolutionOn (T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => (4 : ℝ)) p3u2 p3du2 p3ddu2 0 T where
  hasDerivAt_u := by intro t _; exact p3_hasDerivAt_u2 t
  hasDerivAt_du := by intro t _; exact p3_hasDerivAt_du2 t
  eq_secondDeriv := by intro t _; simp [p3ddu2]
  continuousOn_u := by
    show ContinuousOn (fun t : ℝ => Real.sin (2 * t) / 2) (Icc 0 T)
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const 2).continuousOn
  continuousOn_du := by
    show ContinuousOn (fun t : ℝ => Real.cos (2 * t)) (Icc 0 T)
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn

theorem p3u2_zero : p3u2 0 = 0 := by simp [p3u2]

theorem p3u2_zero_at_pi_div_two : p3u2 (Real.pi / 2) = 0 := by
  simp only [p3u2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_div]

theorem p3u2_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : 0 < p3u2 t := by
  have h1 : 0 < 2 * t := by linarith [ht.1]
  have h2 : 2 * t < Real.pi := by linarith [ht.2]
  have h3 : 0 < Real.sin (2 * t) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  simp only [p3u2]
  linarith

/-- **The engine's two-curvature interlacing with hand-rolled data**: `k₁ = 16 > 4 = k₂`
forces a zero of `p3u` strictly between the consecutive zeros `0`, `π/2` of `p3u2`. -/
theorem p3_interlacing_sin4_sin2 :
    ∃ c ∈ Ioo (0 : ℝ) (Real.pi / 2), p3u c = 0 := by
  refine exists_zero_of_curvature_lt (a := 0) (b := Real.pi / 2)
    (k₁ := fun _ : ℝ => 16) (k₂ := fun _ : ℝ => 4)
    (by linarith [Real.pi_pos]) (fun t _ => by norm_num)
    (p3_jacobiSolutionOn _) (p3u2_jacobiSolutionOn _)
    p3u_zero p3u2_zero p3u2_zero_at_pi_div_two (fun t ht => p3u2_pos ht)
    (p3_hasDerivAt_u2 (Real.pi / 2)) ?_
  exact ⟨Real.pi / 4, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, by norm_num⟩

/-- First-zero ordering form of the same instance: `firstPositiveZero p3u < π/2`. -/
theorem p3_firstZero_lt_half_pi : firstPositiveZero p3u < Real.pi / 2 :=
  firstPositiveZero_lt_of_curvature_lt (b := Real.pi / 2)
    (by linarith [Real.pi_pos]) (fun t _ => by norm_num)
    (p3_jacobiSolutionOn _) (p3u2_jacobiSolutionOn _)
    p3u_zero p3u2_zero p3u2_zero_at_pi_div_two (fun t ht => p3u2_pos ht)
    (p3_hasDerivAt_u2 (Real.pi / 2))
    ⟨Real.pi / 4, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, by norm_num⟩

/-! ## 5. Wronskian monotonicity with the hand-rolled pair -/

/-- `wronskian_antitoneOn_of_le` on the hand-rolled pair `(16, p3u)`, `(4, p3u2)` over
`[0, π/4]`: the sign hypothesis is `sin(4t)·sin(2t) ≥ 0`, i.e. `2 sin²(2t) cos(2t) ≥ 0`
(this forces the interval to stop at the first sign change of `sin 4t`). -/
theorem p3_wronskian_antitone :
    AntitoneOn (wronskian p3u p3du p3u2 p3du2) (Icc 0 (Real.pi / 4)) := by
  refine wronskian_antitoneOn_of_le (by linarith [Real.pi_pos]) (fun t _ => by norm_num) ?_
    (p3_jacobiSolutionOn _) (p3u2_jacobiSolutionOn _)
  intro t ht
  have hsin2 : 0 ≤ Real.sin (2 * t) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩
  have hcos2 : 0 ≤ Real.cos (2 * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
  have hsin4 : Real.sin (4 * t) = 2 * Real.sin (2 * t) * Real.cos (2 * t) := by
    rw [show 4 * t = 2 * (2 * t) by ring, Real.sin_two_mul]
  have hprod : p3u t * p3u2 t = (2 * Real.sin (2 * t) * Real.cos (2 * t)) *
      Real.sin (2 * t) / 8 := by
    simp only [p3u, p3u2, hsin4]
    ring
  rw [hprod]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsin2) hcos2) hsin2)
    (by norm_num)

/-- The explicit consequence: `cos 4t ≤ cos²2t` on `(0, π/4)`. -/
theorem p3_cos_four_le_cos_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 4)) :
    Real.cos (4 * t) ≤ (Real.cos (2 * t)) ^ 2 := by
  have htIcc : t ∈ Icc (0 : ℝ) (Real.pi / 4) := ⟨ht.1.le, ht.2.le⟩
  have hanti := p3_wronskian_antitone (left_mem_Icc.mpr (by linarith [Real.pi_pos]))
    htIcc ht.1.le
  have hW0 : wronskian p3u p3du p3u2 p3du2 0 = 0 := by
    simp [wronskian, p3u, p3u2]
  have hWt : wronskian p3u p3du p3u2 p3du2 t
      = (Real.sin (2 * t) / 2) * (Real.cos (4 * t) - (Real.cos (2 * t)) ^ 2) := by
    simp only [wronskian, p3u, p3du, p3u2, p3du2]
    have hsin4 : Real.sin (4 * t) = 2 * Real.sin (2 * t) * Real.cos (2 * t) := by
      rw [show 4 * t = 2 * (2 * t) by ring, Real.sin_two_mul]
    rw [hsin4]
    ring
  rw [hW0, hWt] at hanti
  have hsin2 : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hnonpos : Real.cos (4 * t) - (Real.cos (2 * t)) ^ 2 ≤ 0 := by
    by_contra hcon
    have hpos : 0 < Real.cos (4 * t) - (Real.cos (2 * t)) ^ 2 := lt_of_not_ge hcon
    have : 0 < (Real.sin (2 * t) / 2) * (Real.cos (4 * t) - (Real.cos (2 * t)) ^ 2) :=
      mul_pos (by linarith) hpos
    linarith
  linarith

/-- `wronskian_deriv` on the hand-rolled pair:
`W' = (4 − 16)·p3u·p3u2 = −(3/2)·sin(4t)·sin(2t)` on `(0, π/2)`. -/
theorem p3_wronskian_deriv {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (wronskian p3u p3du p3u2 p3du2) t
      = -(3 / 2) * Real.sin (4 * t) * Real.sin (2 * t) := by
  rw [wronskian_deriv (p3_jacobiSolutionOn _) (p3u2_jacobiSolutionOn _) ht]
  simp only [p3u, p3u2]
  ring

/-- Strict decay witness at `π/8`: `W' (π/8) = −3√2/4 < 0`. -/
theorem p3_wronskian_deriv_at_pi_div_eight :
    deriv (wronskian p3u p3du p3u2 p3du2) (Real.pi / 8)
      = -(3 * Real.sqrt 2) / 4 := by
  rw [p3_wronskian_deriv ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]
  have h1 : Real.sin (4 * (Real.pi / 8)) = 1 := by
    rw [show 4 * (Real.pi / 8) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have h2 : Real.sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
  rw [h1, h2]
  ring

/-! ## 6. Honest negative control: the curvature hypothesis is load-bearing -/

/-- With `k = 0 < K = 1` and `u(t) = t` (which satisfies `u 0 = 0`, `u' 0 = 1`), the
zero-counting conclusion is **false**: `t` has no zero in `(0, π]`.  So Theorem
`exists_jacobi_zero_on_Ioc_pi_sqrt` cannot drop the hypothesis `k ≥ K`. -/
theorem p3_zero_counting_needs_curvature :
    JacobiSolutionOn (fun _ : ℝ => 0) (fun t : ℝ => t) (fun _ => 1) (fun _ => 0) 0 Real.pi ∧
      (fun t : ℝ => t) 0 = 0 ∧
      ¬ ∃ c ∈ Ioc (0 : ℝ) Real.pi, (fun t : ℝ => t) c = 0 := by
  refine ⟨linearJacobiSolutionOn Real.pi, rfl, ?_⟩
  rintro ⟨c, hc, hcz⟩
  have hc0 : c = 0 := hcz
  linarith [hc.1]

/-- The deliverable's first-zero inequality, read without the existence theorem, is
trivially satisfied for the zero-free linear solution because `sInf ∅ = 0`; this records
that the substantive content of `firstPositiveZero_le_pi_sqrt` is the nonemptiness proved
by `exists_jacobi_zero_on_Ioc_pi_sqrt` (which the deliverable does prove), not the
inequality alone. -/
theorem p3_firstZero_linear_is_zero : firstPositiveZero (fun t : ℝ => t) = 0 := by
  have hset : {t : ℝ | 0 < t ∧ (fun t : ℝ => t) t = 0} = ∅ := by
    ext t
    constructor
    · rintro ⟨h1, h2⟩
      exact (ne_of_gt h1) h2
    · intro h
      exact absurd h (by simp)
  rw [firstPositiveZero, hset]
  exact Real.sInf_empty

end Poincare.L4.GeodesicComparison

/-! ## Pass-3 probe axiom audit (fail-closed) -/

#print axioms Poincare.L4.GeodesicComparison.p3_hasDerivAtR_sin
#print axioms Poincare.L4.GeodesicComparison.p3_hasDerivAtR_cos
#print axioms Poincare.L4.GeodesicComparison.p3u
#print axioms Poincare.L4.GeodesicComparison.p3du
#print axioms Poincare.L4.GeodesicComparison.p3ddu
#print axioms Poincare.L4.GeodesicComparison.p3_hasDerivAt_u
#print axioms Poincare.L4.GeodesicComparison.p3_hasDerivAt_du
#print axioms Poincare.L4.GeodesicComparison.p3_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.p3u_zero
#print axioms Poincare.L4.GeodesicComparison.p3du_zero
#print axioms Poincare.L4.GeodesicComparison.p3u_pi_div_four
#print axioms Poincare.L4.GeodesicComparison.p3u_pos_of_lt_pi_div_four
#print axioms Poincare.L4.GeodesicComparison.p3_zero_exists_K9
#print axioms Poincare.L4.GeodesicComparison.p3_zero_exists_K9_normalized
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_le_K9
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_mem
#print axioms Poincare.L4.GeodesicComparison.p3_zero_exists_horizon_K9
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_eq_pi_div_four
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_le_pi_div_three
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_ge_pi_div_five
#print axioms Poincare.L4.GeodesicComparison.p3_two_sided_bracket
#print axioms Poincare.L4.GeodesicComparison.p3_bracket_sharp
#print axioms Poincare.L4.GeodesicComparison.p3u2
#print axioms Poincare.L4.GeodesicComparison.p3du2
#print axioms Poincare.L4.GeodesicComparison.p3ddu2
#print axioms Poincare.L4.GeodesicComparison.p3_hasDerivAt_u2
#print axioms Poincare.L4.GeodesicComparison.p3_hasDerivAt_du2
#print axioms Poincare.L4.GeodesicComparison.p3u2_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.p3u2_zero
#print axioms Poincare.L4.GeodesicComparison.p3u2_zero_at_pi_div_two
#print axioms Poincare.L4.GeodesicComparison.p3u2_pos
#print axioms Poincare.L4.GeodesicComparison.p3_interlacing_sin4_sin2
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_lt_half_pi
#print axioms Poincare.L4.GeodesicComparison.p3_wronskian_antitone
#print axioms Poincare.L4.GeodesicComparison.p3_cos_four_le_cos_sq
#print axioms Poincare.L4.GeodesicComparison.p3_wronskian_deriv
#print axioms Poincare.L4.GeodesicComparison.p3_wronskian_deriv_at_pi_div_eight
#print axioms Poincare.L4.GeodesicComparison.p3_zero_counting_needs_curvature
#print axioms Poincare.L4.GeodesicComparison.p3_firstZero_linear_is_zero
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_before_pi_sqrt_of_curvature_le
#print axioms Poincare.L4.GeodesicComparison.eq_curvature_of_first_jacobi_zero_before_pi_sqrt
