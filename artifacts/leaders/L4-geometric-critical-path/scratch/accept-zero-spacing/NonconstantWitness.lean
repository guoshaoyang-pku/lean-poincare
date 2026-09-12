import Poincare.L4.GeodesicComparison.ZeroSpacing

/-!
Scratch (reviewer-side, not part of the artifact): a fully explicit, *nonconstant*
curvature profile whose Jacobi solution has consecutive zeros closer than `π/√K`,
so that the hypotheses of `zero_spacing_lt_of_curvature_gt` are jointly satisfiable
with a nonconstant `k` (non-vacuity check).

Data: `K = 1`, `a = 0`, `c₂ = π/2`,
  u(t)  = sin(2t)·(1 + (1/10)cos(2t)),
  k(t)  = (4 + (8/5)cos(2t)) / (1 + (1/10)cos(2t)).
Then `k ≥ 1` on `[0,π]` with `k(π/4) = 4 > 1`, `u'' + k u = 0`, `u(0)=0`,
`u(π/2)=0` (first zero), so `π/2 < π/√1`.
-/

noncomputable section
open Set Filter
open scoped Topology
open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics

namespace ZeroSpacingScratch

noncomputable def kex (t : ℝ) : ℝ :=
  (4 + (8 : ℝ) / 5 * Real.cos (2 * t)) / (1 + (1 : ℝ) / 10 * Real.cos (2 * t))

noncomputable def uex (t : ℝ) : ℝ :=
  Real.sin (2 * t) * (1 + (1 : ℝ) / 10 * Real.cos (2 * t))

noncomputable def duex (t : ℝ) : ℝ :=
  2 * Real.cos (2 * t) + (1 : ℝ) / 5 * (Real.cos (2 * t)) ^ 2
    - (1 : ℝ) / 5 * (Real.sin (2 * t)) ^ 2

noncomputable def dduex (t : ℝ) : ℝ :=
  -4 * Real.sin (2 * t) - (8 : ℝ) / 5 * Real.sin (2 * t) * Real.cos (2 * t)

lemma hasDerivAt_sin_two (t : ℝ) :
    HasDerivAtR (fun s : ℝ => Real.sin (2 * s)) (2 * Real.cos (2 * t)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (2 : ℝ) * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_sin (2 * t)).comp t h2
  simpa [Function.comp_def, mul_comm] using h

lemma hasDerivAt_cos_two (t : ℝ) :
    HasDerivAtR (fun s : ℝ => Real.cos (2 * s)) (-2 * Real.sin (2 * t)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (2 : ℝ) * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_cos (2 * t)).comp t h2
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h

lemma hasDerivAt_uex (t : ℝ) : HasDerivAtR uex (duex t) t := by
  have hs := hasDerivAt_sin_two t
  have hc := hasDerivAt_cos_two t
  have hg : HasDerivAtR (fun s : ℝ => 1 + (1 : ℝ) / 10 * Real.cos (2 * s))
      (-(1 : ℝ) / 5 * Real.sin (2 * t)) t := by
    have h := hc.const_mul ((1 : ℝ) / 10)
    have h1 : HasDerivAtR (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have h2 := h1.add h
    have hder : (0 : ℝ) + (1 : ℝ) / 10 * (-2 * Real.sin (2 * t))
        = -(1 : ℝ) / 5 * Real.sin (2 * t) := by ring
    rw [hder] at h2
    convert h2 using 1
    ext s; simp
  have h := hs.mul hg
  convert h using 1
  · ext s; simp [uex]
  · simp [duex]; ring

lemma hasDerivAt_duex (t : ℝ) : HasDerivAtR duex (dduex t) t := by
  have hs := hasDerivAt_sin_two t
  have hc := hasDerivAt_cos_two t
  have h1 : HasDerivAtR (fun s : ℝ => 2 * Real.cos (2 * s)) (-4 * Real.sin (2 * t)) t := by
    have h := hc.const_mul (2 : ℝ)
    have hder : (2 : ℝ) * (-2 * Real.sin (2 * t)) = -4 * Real.sin (2 * t) := by ring
    rw [hder] at h
    simpa [mul_comm] using h
  have h2 : HasDerivAtR (fun s : ℝ => (1 : ℝ) / 5 * (Real.cos (2 * s)) ^ 2)
      ((1 : ℝ) / 5 * (2 * Real.cos (2 * t) * (-2 * Real.sin (2 * t)))) t := by
    have h := (hc.pow 2).const_mul ((1 : ℝ) / 5)
    convert h using 1
    · ext s; simp
    · simp only [Nat.cast_ofNat]; ring
  have h3 : HasDerivAtR (fun s : ℝ => -((1 : ℝ) / 5 * (Real.sin (2 * s)) ^ 2))
      (-((1 : ℝ) / 5 * (2 * Real.sin (2 * t) * (2 * Real.cos (2 * t))))) t := by
    have h := ((hs.pow 2).const_mul ((1 : ℝ) / 5)).neg
    convert h using 1
    · ext s; simp
    · simp only [Nat.cast_ofNat]; ring
  have h123 := (h1.add h2).add h3
  convert h123 using 1
  · ext s; simp [duex]; ring
  · simp [dduex]; ring

lemma kex_mul_uex (t : ℝ) : kex t * uex t = -dduex t := by
  have hc : -1 ≤ Real.cos (2 * t) := Real.neg_one_le_cos _
  have hden : 1 + (1 : ℝ) / 10 * Real.cos (2 * t) ≠ 0 := by linarith
  have hden' : (10 : ℝ) + Real.cos (2 * t) ≠ 0 := by linarith
  rw [kex, uex, dduex]
  field_simp [hden, hden']
  ring

lemma jacobi_ex : JacobiSolutionOn kex uex duex dduex 0 (Real.pi / 2) where
  hasDerivAt_u := fun t _ => hasDerivAt_uex t
  hasDerivAt_du := fun t _ => hasDerivAt_duex t
  eq_secondDeriv := by
    intro t _
    have h := kex_mul_uex t
    have h2 : -(kex t) * uex t = -(kex t * uex t) := by ring
    rw [h2, h, neg_neg]
  continuousOn_u := by unfold uex; fun_prop
  continuousOn_du := by unfold duex; fun_prop

lemma one_le_kex {t : ℝ} (_ : t ∈ Icc (0 : ℝ) Real.pi) : (1 : ℝ) ≤ kex t := by
  have hc : -1 ≤ Real.cos (2 * t) := Real.neg_one_le_cos _
  have hden : 0 < 1 + (1 : ℝ) / 10 * Real.cos (2 * t) := by linarith
  rw [kex, le_div_iff₀ hden]
  linarith

lemma kex_at_pi_div_four : kex (Real.pi / 4) = 4 := by
  have h : Real.cos (2 * (Real.pi / 4)) = 0 := by
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  rw [kex, h]
  norm_num

lemma kex_ne_const : ∃ s t : ℝ, kex s ≠ kex t := by
  refine ⟨0, Real.pi / 4, ?_⟩
  rw [kex_at_pi_div_four]
  norm_num [kex]

lemma uex_ne_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) : uex t ≠ 0 := by
  have h1 : 0 < Real.sin (2 * t) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [ht.1]
    · linarith [ht.2]
  have h2 : 0 < 1 + (1 : ℝ) / 10 * Real.cos (2 * t) := by
    have hc : -1 ≤ Real.cos (2 * t) := Real.neg_one_le_cos _
    linarith
  rw [uex]
  exact mul_ne_zero (ne_of_gt h1) (ne_of_gt h2)

lemma uex_at_pi_div_two : uex (Real.pi / 2) = 0 := by
  have h : 2 * (Real.pi / 2) = Real.pi := by ring
  simp [uex, h, Real.sin_pi]

/-- Joint satisfiability of every hypothesis of `zero_spacing_lt_of_curvature_gt`
with a **nonconstant** curvature profile (and the strict conclusion). -/
theorem nonconstant_profile_satisfies_hypotheses :
    (∀ t ∈ Icc (0 : ℝ) Real.pi, (1 : ℝ) ≤ kex t) ∧
      (∃ t ∈ Ioo (0 : ℝ) Real.pi, (1 : ℝ) < kex t) ∧
      JacobiSolutionOn kex uex duex dduex 0 (Real.pi / 2) ∧
      uex 0 = 0 ∧ uex (Real.pi / 2) = 0 ∧
      (∀ t ∈ Ioo (0 : ℝ) (Real.pi / 2), uex t ≠ 0) ∧
      (0 : ℝ) < Real.pi / 2 ∧ Real.pi / 2 < Real.pi ∧
      (∃ s t : ℝ, kex s ≠ kex t) :=
  ⟨fun t ht => one_le_kex ht,
   ⟨Real.pi / 4, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, by
      rw [kex_at_pi_div_four]; norm_num⟩,
   jacobi_ex, by simp [uex], uex_at_pi_div_two,
   fun t ht => uex_ne_zero ht,
   by linarith [Real.pi_pos], by linarith [Real.pi_pos], kex_ne_const⟩

/-- The strict conclusion of `zero_spacing_lt_of_curvature_gt` for this
nonconstant profile, obtained by applying the artifact theorem. -/
theorem nonconstant_profile_strict_conclusion : Real.pi / 2 < Real.pi := by
  have h := zero_spacing_lt_of_curvature_gt (K := 1) (c₁ := 0) (c₂ := Real.pi / 2)
    (k := kex) (u := uex) (du := duex) (ddu := dduex)
    (by norm_num) (by linarith [Real.pi_pos]) jacobi_ex (by simp [uex]) uex_at_pi_div_two
    (fun t ht => uex_ne_zero ht) (fun t ht => one_le_kex (by simpa [Real.sqrt_one] using ht))
    ⟨Real.pi / 4, ⟨by linarith [Real.pi_pos],
      by rw [Real.sqrt_one, div_one, zero_add]; linarith [Real.pi_pos]⟩, by
      rw [kex_at_pi_div_four]; norm_num⟩
  simpa [Real.sqrt_one] using h

#print axioms nonconstant_profile_satisfies_hypotheses
#print axioms nonconstant_profile_strict_conclusion

/-- The same nonconstant profile also satisfies the hypotheses of
`zero_spacing_ge_of_curvature_le` with the (larger) comparison curvature `K = 7`:
`kex ≤ 7` on `[0, π/2]`, and its first zero `π/2` is strictly beyond `π/√7`. -/
lemma jacobi_ex_pi : JacobiSolutionOn kex uex duex dduex 0 Real.pi where
  hasDerivAt_u := fun t _ => hasDerivAt_uex t
  hasDerivAt_du := fun t _ => hasDerivAt_duex t
  eq_secondDeriv := by
    intro t _
    have h := kex_mul_uex t
    have h2 : -(kex t) * uex t = -(kex t * uex t) := by ring
    rw [h2, h, neg_neg]
  continuousOn_u := by unfold uex; fun_prop
  continuousOn_du := by unfold duex; fun_prop

lemma kex_le_seven {t : ℝ} (_ : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : kex t ≤ 7 := by
  have hc : Real.cos (2 * t) ≤ 1 := Real.cos_le_one _
  have hden : 0 < 1 + (1 : ℝ) / 10 * Real.cos (2 * t) := by
    have h := Real.neg_one_le_cos (2 * t); linarith
  rw [kex, div_le_iff₀ hden]
  linarith

/-- The strict conclusion of `zero_spacing_ge_of_curvature_le` for this
nonconstant profile (`π/√7 < π/2`). -/
theorem nonconstant_profile_lower_bound : Real.pi / Real.sqrt 7 < Real.pi / 2 := by
  have hle : Real.pi / Real.sqrt 7 ≤ Real.pi / 2 := by
    have h := zero_spacing_ge_of_curvature_le (K := 7) (c₁ := 0) (c₂ := Real.pi / 2)
      (b := Real.pi) (k := kex) (u := uex) (du := duex) (ddu := dduex)
      (by norm_num) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      jacobi_ex_pi (by simp [uex]) uex_at_pi_div_two
      (fun t ht => uex_ne_zero ht) (fun t ht => kex_le_seven ht)
    simpa using h
  have hlt : Real.pi / Real.sqrt 7 ≠ Real.pi / 2 := by
    intro heq
    have h2 : Real.sqrt 7 = 2 := by
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      field_simp at heq
      linarith
    have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    rw [h2] at h7
    norm_num at h7
  exact lt_of_le_of_ne hle hlt

#print axioms nonconstant_profile_lower_bound

end ZeroSpacingScratch
