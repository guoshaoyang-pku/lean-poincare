import Poincare.L4.GeodesicComparison.SturmInterlacing

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Sine solution on an arbitrary interval. -/
theorem sinJacobiSolutionOn' (a b : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => 1) Real.sin Real.cos (fun t => -Real.sin t) a b where
  hasDerivAt_u := by intro t _; simpa using Real.hasDerivAt_sin t
  hasDerivAt_du := by intro t _; simpa using Real.hasDerivAt_cos t
  eq_secondDeriv := by intro t _; simp
  continuousOn_u := Real.continuous_sin.continuousOn
  continuousOn_du := Real.continuous_cos.continuousOn

noncomputable def jacobiSolShift (K a : ℝ) : ℝ → ℝ := jacobiSol K ∘ fun t => t - a

noncomputable def jacobiDerivShift (K a : ℝ) : ℝ → ℝ := jacobiDeriv K ∘ fun t => t - a

theorem hasDerivAt_jacobiSolShift (K a t : ℝ) :
    HasDerivAtR (jacobiSolShift K a) (jacobiDerivShift K a t) t := by
  have h : HasDerivAtR (fun s : ℝ => s - a) 1 t := (hasDerivAtR_id t).sub_const a
  have h2 : HasDerivAtR (jacobiSol K ∘ fun s : ℝ => s - a) (jacobiDeriv K (t - a) * 1) t :=
    (hasDerivAt_jacobiSol K (t - a)).comp t h
  rw [mul_one] at h2
  simpa only [jacobiSolShift, jacobiDerivShift, Function.comp_apply] using h2

theorem hasDerivAt_jacobiDerivShift (K a t : ℝ) :
    HasDerivAtR (jacobiDerivShift K a) (-(K * jacobiSolShift K a t)) t := by
  have h : HasDerivAtR (fun s : ℝ => s - a) 1 t := (hasDerivAtR_id t).sub_const a
  have h2 : HasDerivAtR (jacobiDeriv K ∘ fun s : ℝ => s - a)
      (-(K * jacobiSol K (t - a)) * 1) t :=
    (hasDerivAt_jacobiDeriv K (t - a)).comp t h
  rw [mul_one] at h2
  simpa only [jacobiSolShift, jacobiDerivShift, Function.comp_apply] using h2

theorem jacobiSolShift_jacobiSolutionOn (K a b : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (jacobiSolShift K a) (jacobiDerivShift K a)
      (fun t => -(K * jacobiSolShift K a t)) a b where
  hasDerivAt_u := by intro t _; exact hasDerivAt_jacobiSolShift K a t
  hasDerivAt_du := by intro t _; exact hasDerivAt_jacobiDerivShift K a t
  eq_secondDeriv := by intro t _; ring
  continuousOn_u := by
    show ContinuousOn (jacobiSol K ∘ fun t : ℝ => t - a) (Icc a b)
    exact ((continuous_jacobiSol K).comp (continuous_id.sub continuous_const)).continuousOn
  continuousOn_du := by
    show ContinuousOn (jacobiDeriv K ∘ fun t : ℝ => t - a) (Icc a b)
    exact ((continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_jacobiDeriv K s).continuousAt).comp
        (continuous_id.sub continuous_const)).continuousOn

theorem jacobiSolShift_pos {K a : ℝ} (hK : 0 < K) :
    ∀ t ∈ Ioo a (a + Real.pi / Real.sqrt K), 0 < jacobiSolShift K a t := by
  intro t ht
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hx : 0 < t - a := by linarith [ht.1]
  have hxpi : Real.sqrt K * (t - a) < Real.pi := by
    have h1 : t - a < Real.pi / Real.sqrt K := by linarith [ht.2]
    have h2 := mul_lt_mul_of_pos_left h1 hsqrt
    rwa [mul_div_cancel₀ _ hsqrt.ne'] at h2
  have hmem : Real.sqrt K * (t - a) ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨mul_pos hsqrt hx, hxpi⟩
  have : 0 < jacobiSol K (t - a) := by
    rw [jacobiSol_of_pos hK]
    exact jacobiSolSphere_pos hK hx hxpi
  simpa only [jacobiSolShift, Function.comp_apply] using this

/-- Infinite interlacing: for every integer `n`, `sin` has a zero strictly between the
consecutive zeros `2nπ` and `2(n+1)π` of the model `2 sin(·/2)` (curvature `1/2`). -/
theorem sin_interlaces_half_model_all (n : ℤ) :
    ∃ c ∈ Ioo (2 * (n : ℝ) * Real.pi) (2 * ((n : ℝ) + 1) * Real.pi), Real.sin c = 0 := by
  have hK₂ : (0 : ℝ) < 1 / 4 := by norm_num
  set a : ℝ := 2 * (n : ℝ) * Real.pi with hadef
  have hspan : Real.pi / Real.sqrt (1 / 4) = 2 * Real.pi := by
    have : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]; ring
  have hb : a + Real.pi / Real.sqrt (1 / 4) = 2 * ((n : ℝ) + 1) * Real.pi := by
    rw [hspan, hadef]; ring
  have hstrict : ∃ t ∈ Ioo a (a + Real.pi / Real.sqrt (1 / 4)), (1 / 4 : ℝ) < 1 := by
    refine ⟨(a + (a + Real.pi / Real.sqrt (1 / 4))) / 2, ⟨?_, ?_⟩, by norm_num⟩
    · linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂]
    · linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂]
  have hsin_a : Real.sin a = 0 := by
    rw [hadef, Real.sin_eq_zero_iff]
    exact ⟨2 * n, by push_cast; ring⟩
  have hmain := exists_zero_of_curvature_lt (a := a) (b := a + Real.pi / Real.sqrt (1 / 4))
    (k₁ := fun _ : ℝ => 1) (k₂ := fun _ : ℝ => 1 / 4)
    (by linarith [Real.pi_pos, hspan])
    (fun t _ => by norm_num)
    (sinJacobiSolutionOn' a (a + Real.pi / Real.sqrt (1 / 4)))
    (jacobiSolShift_jacobiSolutionOn (1 / 4) a (a + Real.pi / Real.sqrt (1 / 4)))
    hsin_a (by simp [jacobiSolShift, jacobiSol_zero])
    (by
      have := modelJacobiSol_firstZero hK₂
      simpa only [jacobiSolShift, Function.comp_apply, add_sub_cancel_left] using this)
    (fun t ht => jacobiSolShift_pos hK₂ t ht)
    (hasDerivAt_jacobiSolShift (1 / 4) a (a + Real.pi / Real.sqrt (1 / 4)))
    hstrict
  rwa [hb] at hmain

/-- Explicit witness for the infinite interlacing. -/
theorem sin_zero_in_half_model_interval (n : ℤ) :
    (2 * (n : ℝ) + 1) * Real.pi ∈ Ioo (2 * (n : ℝ) * Real.pi) (2 * ((n : ℝ) + 1) * Real.pi) ∧
      Real.sin ((2 * (n : ℝ) + 1) * Real.pi) = 0 := by
  have hpi := Real.pi_pos
  constructor
  · constructor <;> nlinarith
  · rw [Real.sin_eq_zero_iff]
    exact ⟨2 * n + 1, by push_cast; ring⟩

end Poincare.L4.GeodesicComparison
