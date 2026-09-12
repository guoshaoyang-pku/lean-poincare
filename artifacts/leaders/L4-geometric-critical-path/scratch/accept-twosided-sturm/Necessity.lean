import Mathlib.Analysis.Real.Pi.Bounds
import Poincare.L4.GeodesicComparison.TwoSidedSturm

noncomputable section
open Set Filter
open scoped Topology
open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics

namespace AcceptScratch

/-- `jacobiSolutionOn_mono_Icc`'s hypothesis `a ≤ b'` is redundant: the same conclusion
follows without it (the proof term never uses it). -/
theorem jacobiSolutionOn_mono_Icc_no_left_le {k u du ddu : ℝ → ℝ} {a b b' : ℝ}
    (h : JacobiSolutionOn k u du ddu a b) (hb'b : b' ≤ b) :
    JacobiSolutionOn k u du ddu a b' where
  hasDerivAt_u := fun _ ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hb'b⟩
  hasDerivAt_du := fun _ ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hb'b⟩
  eq_secondDeriv := fun _ ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hb'b⟩
  continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hb'b)
  continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hb'b)

/-- `hfirst` is load-bearing.  With `u ≡ 0`, `k ≡ 2`, `K = 3`, `a = 0`, `c = π/2`, the main
theorem's conclusion is false. -/
theorem main_conclusion_false_without_hfirst :
    ¬ (∀ t ∈ Ioo (0:ℝ) (Real.pi/2), (fun _ : ℝ => (2:ℝ)) t = 3) := by
  intro h
  have ht : Real.pi/4 ∈ Ioo (0:ℝ) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have hc := h (Real.pi/4) ht
  norm_num at hc

/-- Every hypothesis of the main theorem except `hfirst` holds for that data. -/
theorem main_bundle_without_hfirst :
    (0:ℝ) < 3 ∧ Real.sqrt 3 * (Real.pi/2 - 0) ≤ Real.pi ∧
    (∀ t ∈ Icc (0:ℝ) (Real.pi/2), (fun _ : ℝ => (2:ℝ)) t ≤ 3) ∧
    JacobiSolutionOn (fun _ : ℝ => (2:ℝ)) (fun _ : ℝ => (0:ℝ)) (fun _ : ℝ => (0:ℝ))
      (fun _ : ℝ => (0:ℝ)) 0 2 ∧
    (Real.pi/2 : ℝ) ∈ Ioo (0:ℝ) 2 ∧ (fun _ : ℝ => (0:ℝ)) 0 = 0 ∧
    (fun _ : ℝ => (0:ℝ)) (Real.pi/2) = 0 := by
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hspan3 : Real.sqrt 3 * (Real.pi / 2 - 0) ≤ Real.pi := by
    have h := mul_le_mul_of_nonneg_right hsqrt3 (by positivity : (0:ℝ) ≤ Real.pi / 2)
    calc Real.sqrt 3 * (Real.pi / 2 - 0) = Real.sqrt 3 * (Real.pi / 2) := by ring
      _ ≤ 2 * (Real.pi / 2) := h
      _ = Real.pi := by ring
  refine ⟨by norm_num, hspan3, fun t ht => by norm_num, ?_, ?_, rfl, rfl⟩
  · refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, continuousOn_const, continuousOn_const⟩
    · exact hasDerivAtR_const 0 t
    · exact hasDerivAtR_const 0 t
    · ring
  · constructor <;> linarith [Real.pi_pos, Real.pi_lt_four]

/-- `hspan` is load-bearing: `k ≡ 1/4 ≤ K = 1` with `u = sin(t/2)` has first zero `c = 2π`,
where `√K (c - a) = 2π > π`, and the conclusion `k = K` on `(0, 2π)` is false. -/
theorem hspan_necessary :
    ∃ (k u du ddu : ℝ → ℝ) (K a b c : ℝ),
      0 < K ∧ ¬ (Real.sqrt K * (c - a) ≤ Real.pi) ∧
      (∀ t ∈ Icc a c, k t ≤ K) ∧ JacobiSolutionOn k u du ddu a b ∧
      c ∈ Ioo a b ∧ u a = 0 ∧ u c = 0 ∧ (∀ t ∈ Ioo a c, u t ≠ 0) ∧
      ¬ (∀ t ∈ Ioo a c, k t = K) := by
  have hs : Real.sqrt (1/4:ℝ) = 1/2 := by
    rw [show (1/4:ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun _ => (1:ℝ)/4, sturmModel (1/4) 0, sturmModelDeriv (1/4) 0,
    sturmModelSecondDeriv (1/4) 0, 1, 0, 8, 2*Real.pi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rw [Real.sqrt_one, one_mul, sub_zero]
    intro hle
    linarith [Real.pi_pos]
  · intro t ht; norm_num
  · exact sturmModel_jacobiSolutionOn (K := 1/4) (a := 0) (b := 8) (by norm_num)
  · constructor <;> linarith [Real.pi_pos, Real.pi_lt_four]
  · simp [sturmModel]
  · simp only [sturmModel, sub_zero]
    rw [hs]
    have : (1/2:ℝ) * (2*Real.pi) = Real.pi := by ring
    rw [this, Real.sin_pi]
  · intro t ht hz
    simp only [sturmModel, sub_zero] at hz
    rw [hs] at hz
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
    have ht' : (0:ℝ) < t := ht.1
    have ht'' : t < 2*Real.pi := ht.2
    have h2 : t = 2 * (n:ℝ) * Real.pi := by nlinarith [hn]
    have h1 : (0:ℝ) < (n:ℝ) := by nlinarith [Real.pi_pos, h2, ht']
    have h3 : (n:ℝ) < 1 := by nlinarith [Real.pi_pos, h2, ht'']
    have h1' : (0:ℤ) < n := by exact_mod_cast h1
    have h3' : n < (1:ℤ) := by exact_mod_cast h3
    omega
  · intro hconcl
    have ht : (1:ℝ) ∈ Ioo (0:ℝ) (2*Real.pi) := by
      constructor <;> linarith [Real.pi_pos, Real.pi_gt_three]
    have hc := hconcl 1 ht
    norm_num at hc

end AcceptScratch
