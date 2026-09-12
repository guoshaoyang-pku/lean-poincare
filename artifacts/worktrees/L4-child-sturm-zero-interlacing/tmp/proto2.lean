import Poincare.D12.ComparisonGeodesics.SturmComparison
import Poincare.D10.JacobiConstantCurvature.Comparison

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Prototype: D10 model is a D12 Jacobi solution. -/
theorem proto_jacobiSol_jacobiSolutionOn (K T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (jacobiSol K) (jacobiDeriv K)
      (fun t => -(K * jacobiSol K t)) 0 T where
  hasDerivAt_u := by intro t _; exact hasDerivAt_jacobiSol K t
  hasDerivAt_du := by intro t _; exact hasDerivAt_jacobiDeriv K t
  eq_secondDeriv := by intro t _; ring
  continuousOn_u := (continuous_jacobiSol K).continuousOn
  continuousOn_du :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn

/-- Prototype: shifted model. -/
noncomputable def protoJacobiSolShift (K a : ℝ) : ℝ → ℝ := fun t => jacobiSol K (t - a)

noncomputable def protoJacobiDerivShift (K a : ℝ) : ℝ → ℝ := fun t => jacobiDeriv K (t - a)

theorem proto_hasDerivAt_jacobiSolShift (K a t : ℝ) :
    HasDerivAtR (protoJacobiSolShift K a) (protoJacobiDerivShift K a t) t := by
  have h : HasDerivAtR (fun s : ℝ => s - a) 1 t := (hasDerivAtR_id t).sub_const a
  have h2 : HasDerivAtR (jacobiSol K ∘ fun s : ℝ => s - a) (jacobiDeriv K (t - a) * 1) t :=
    (hasDerivAt_jacobiSol K (t - a)).comp (g := fun s : ℝ => s - a) t h
  rw [mul_one] at h2
  simpa only [protoJacobiSolShift, protoJacobiDerivShift, Function.comp_apply] using h2

theorem proto_hasDerivAt_jacobiDerivShift (K a t : ℝ) :
    HasDerivAtR (protoJacobiDerivShift K a) (-(K * protoJacobiSolShift K a t)) t := by
  have h : HasDerivAtR (fun s : ℝ => s - a) 1 t := (hasDerivAtR_id t).sub_const a
  have h2 : HasDerivAtR (jacobiDeriv K ∘ fun s : ℝ => s - a)
      (-(K * jacobiSol K (t - a)) * 1) t :=
    (hasDerivAt_jacobiDeriv K (t - a)).comp (g := fun s : ℝ => s - a) t h
  rw [mul_one] at h2
  simpa only [protoJacobiSolShift, protoJacobiDerivShift, Function.comp_apply] using h2

theorem proto_jacobiSolShift_jacobiSolutionOn (K a b : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => K) (protoJacobiSolShift K a) (protoJacobiDerivShift K a)
      (fun t => -(K * protoJacobiSolShift K a t)) a b where
  hasDerivAt_u := by intro t _; exact proto_hasDerivAt_jacobiSolShift K a t
  hasDerivAt_du := by intro t _; exact proto_hasDerivAt_jacobiDerivShift K a t
  eq_secondDeriv := by intro t _; ring
  continuousOn_u := by
    have hc : Continuous (jacobiSol K ∘ fun t : ℝ => t - a) :=
      (continuous_jacobiSol K).comp (g := fun t : ℝ => t - a)
        (continuous_id.sub continuous_const)
    simpa only [protoJacobiSolShift, Function.comp_apply] using hc.continuousOn
  continuousOn_du := by
    have hc : Continuous (jacobiDeriv K ∘ fun t : ℝ => t - a) :=
      (continuous_iff_continuousAt.mpr fun s => (hasDerivAt_jacobiDeriv K s).continuousAt).comp
        (g := fun t : ℝ => t - a) (continuous_id.sub continuous_const)
    simpa only [protoJacobiDerivShift, Function.comp_apply] using hc.continuousOn

/-- Prototype: relaxed dichotomy wrapper around the engine's positive-case lemma. -/
theorem proto_dichotomy {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1a : u₁ a = 0) (hu2a : u₂ a = 0) (hu2b : u₂ b = 0)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u₂ t) (hdu2b : HasDerivAtR u₂ (du₂ b) b) :
    (∃ c ∈ Ioo a b, u₁ c = 0) ∨ (∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₁ t = k₂ t) := by
  by_cases hz : ∃ c ∈ Ioo a b, u₁ c = 0
  · exact Or.inl hz
  · right
    have hnozero : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → u₁ t ≠ 0 := by
      intro t ht he
      exact hz ⟨t, ht, he⟩
    have hsign := sign_constant_of_no_zero (h1.continuousOn_u.mono Ioo_subset_Icc_self) hnozero
    rcases hsign with hpos | hneg
    · exact sturm_zero_comparison_of_pos hab hk h1 h2 hu1a hu2a hu2b hpos hu2pos hdu2b
    · have hpos' : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < -u₁ t := by
        intro t ht
        exact neg_pos.mpr (hneg ht)
      have hneg1 : JacobiSolutionOn k₁ (-u₁) (-du₁) (-ddu₁) a b := h1.neg
      have hu1a' : (-u₁) a = 0 := by rw [Pi.neg_apply, hu1a, neg_zero]
      exact sturm_zero_comparison_of_pos hab hk hneg1 h2 hu1a' hu2a hu2b hpos' hu2pos hdu2b

/-- Prototype: Wronskian constancy and endpoint value in the equality case. -/
theorem proto_endpoint_zero {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K) → k t = K) :
    u (Real.pi / Real.sqrt K) = 0 := by
  set z : ℝ := Real.pi / Real.sqrt K with hzdef
  have hzpos : 0 < z := by
    rw [hzdef]; exact div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  have hmodel := proto_jacobiSol_jacobiSolutionOn K z
  set W : ℝ → ℝ := wronskian u du (jacobiSol K) (jacobiDeriv K) with hWdef
  -- derivative of W is zero on the interior
  have hWderiv : (Ioo (0 : ℝ) z).EqOn (deriv W) 0 := by
    intro t ht
    rw [hWdef, wronskian_deriv h hmodel ht, heq ht]
    simp
  have hWdiff : DifferentiableOn ℝ W (Ioo (0 : ℝ) z) := by
    rw [hWdef]; exact wronskian_differentiableOn h hmodel
  have hz2 : z / 2 ∈ Ioo (0 : ℝ) z := ⟨by linarith, by linarith⟩
  have hconst : ∀ x ∈ Ioo (0 : ℝ) z, ∀ y ∈ Ioo (0 : ℝ) z, W x = W y :=
    fun x hx y hy => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hWdiff hWderiv hx hy
  have hEqOn : EqOn W (fun _ => W (z / 2)) (Ioo (0 : ℝ) z) := by
    intro x hx
    exact hconst x hx (z / 2) hz2
  have hWcont : ContinuousOn W (Icc (0 : ℝ) z) := by
    rw [hWdef]
    exact wronskian_continuousOn h.continuousOn_u h.continuousOn_du
      (continuous_jacobiSol K).continuousOn
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn
  have hclosure : closure (Ioo (0 : ℝ) z) = Icc 0 z := closure_Ioo (ne_of_lt hzpos)
  have hEqOnIcc : EqOn W (fun _ => W (z / 2)) (Icc (0 : ℝ) z) :=
    hEqOn.of_subset_closure hWcont continuousOn_const Ioo_subset_Icc_self (by rw [hclosure])
  have hWz : W z = W 0 := by
    have h1 : W z = W (z / 2) := hEqOnIcc (right_mem_Icc.mpr hzpos.le)
    have h2 : W 0 = W (z / 2) := hEqOnIcc (left_mem_Icc.mpr hzpos.le)
    rw [h1, h2]
  -- explicit values
  have hmodelz : jacobiSol K z = 0 := by
    rw [hzdef, jacobiSol_of_pos hK]
    exact jacobiSolSphere_firstZero hK
  have hmodeld : jacobiDeriv K z = -1 := by
    rw [hzdef, jacobiDeriv_of_pos hK]
    have h : Real.sqrt K * (Real.pi / Real.sqrt K) = Real.pi :=
      mul_div_cancel₀ _ (Real.sqrt_pos_of_pos hK).ne'
    rw [h, Real.cos_pi]
  have hW0 : W 0 = 0 := by
    rw [hWdef, wronskian]
    simp [hu0]
  have hWzval : W z = u z := by
    rw [hWdef, wronskian, hmodelz, hmodeld]
    ring
  rw [hWzval, hW0] at hWz
  exact hWz

/-- Prototype: relaxed engine + endpoint zero gives the sharpened bound. -/
theorem proto_sharpened {k u du ddu : ℝ → ℝ} {T K : ℝ}
    (hT : 0 < T) (h : JacobiSolutionOn k u du ddu 0 T) (hu0 : u 0 = 0)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t) :
    T ≤ Real.pi / Real.sqrt K := by
  by_contra hcon
  have hzT : Real.pi / Real.sqrt K < T := not_le.mp hcon
  have hzpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  have hmono : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K) :=
    { hasDerivAt_u := fun t ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hzT.le⟩
      hasDerivAt_du := fun t ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hzT.le⟩
      eq_secondDeriv := fun t ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hzT.le⟩
      continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hzT.le)
      continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hzT.le) }
  have hmodel := proto_jacobiSol_jacobiSolutionOn K (Real.pi / Real.sqrt K)
  have hdich := proto_dichotomy hzpos (fun t ht => hk ⟨ht.1, lt_trans ht.2 hzT⟩) hmono hmodel
    hu0 (jacobiSol_zero K) (by rw [jacobiSol_of_pos hK]; exact jacobiSolSphere_firstZero hK)
    (fun t ht => by
      rw [jacobiSol_of_pos hK]
      refine jacobiSolSphere_pos hK ht.1 ?_
      have := mul_lt_mul_of_pos_left ht.2 (Real.sqrt_pos_of_pos hK)
      rwa [mul_div_cancel₀ _ (Real.sqrt_pos_of_pos hK).ne'] at this)
    (hasDerivAt_jacobiSol K _)
  rcases hdich with hzero | heq
  · obtain ⟨c, hc, hcz⟩ := hzero
    exact absurd hcz (ne_of_gt (hpos c ⟨hc.1, (lt_of_lt_of_le hc.2 hzT.le).le⟩))
  · have hend := proto_endpoint_zero hK hmono hu0 (fun t ht => (heq ht).symm)
    exact absurd hend (ne_of_gt (hpos _ ⟨hzpos, hzT.le⟩))

end Poincare.L4.GeodesicComparison
