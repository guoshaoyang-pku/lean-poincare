import Poincare.L4.GeodesicComparison.SturmInterlacing

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Positivity near `0` for normalized initial data. -/
theorem proto_pos_near_zero {k u du ddu : ℝ → ℝ} {z : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 z) (hu0 : u 0 = 0) (hdu0 : du 0 = 1) (hz : 0 < z) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → t ≤ z → 0 < u t := by
  have hcont_at : ContinuousWithinAt du (Icc (0 : ℝ) z) 0 :=
    h.continuousOn_du.continuousWithinAt (left_mem_Icc.mpr hz.le)
  have hev : ∀ᶠ s in 𝓝[Icc (0 : ℝ) z] 0, (1 / 2 : ℝ) < du s :=
    hcont_at (isOpen_Ioi.mem_nhds (by rw [hdu0]; norm_num))
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨s, hso, hs0, hsub⟩ := hev
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.isOpen_iff.mp hso 0 hs0
  have hdu_half : ∀ x ∈ Icc (0 : ℝ) z, x < δ₀ → (1 / 2 : ℝ) < du x := by
    intro x hx hxδ
    exact hsub ⟨hδ₀sub (Metric.mem_ball.mpr (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; exact hxδ)), hx⟩
  refine ⟨min δ₀ z, lt_min hδ₀pos hz, ?_⟩
  intro t ht htδ htz
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have hint : IntervalIntegrable du volume 0 t := by
    have hcont' : ContinuousOn du (uIcc (0 : ℝ) t) := by
      rw [uIcc_of_le ht.le]
      exact h.continuousOn_du.mono (Icc_subset_Icc_right htz)
    exact hcont'.intervalIntegrable
  have hftc : ∫ x in (0)..t, du x = u t - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le
      (h.continuousOn_u.mono (Icc_subset_Icc_right htz))
      (fun x hx => h.hasDerivAt_u ⟨hx.1, lt_of_lt_of_le hx.2 htz⟩) hint
  have hmono : ∫ x in (0)..t, (1 / 2 : ℝ) ≤ ∫ x in (0)..t, du x :=
    intervalIntegral.integral_mono_on ht.le intervalIntegrable_const hint (fun x hx =>
      le_of_lt (hdu_half x ⟨hx.1, le_trans hx.2 htz⟩ (lt_of_le_of_lt hx.2 htδ₀)))
  have hconst : ∫ x in (0)..t, (1 / 2 : ℝ) = t / 2 := by
    rw [intervalIntegral.integral_const]
    ring
  rw [hconst] at hmono
  have : u t = ∫ x in (0)..t, du x := by linarith [hftc, hu0]
  linarith [hmono, this, ht]

/-- `firstPositiveZero` is attained and is the least positive zero. -/
theorem proto_firstPositiveZero_mem {k u du ddu : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Icc (0 : ℝ) (Real.pi / Real.sqrt K), K ≤ k t)
    (h : JacobiSolutionOn k u du ddu 0 (Real.pi / Real.sqrt K))
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1) :
    u (firstPositiveZero u) = 0 ∧ 0 < firstPositiveZero u ∧
      ∀ t ∈ Ioo (0 : ℝ) (firstPositiveZero u), u t ≠ 0 := by
  set z : ℝ := Real.pi / Real.sqrt K with hzdef
  have hz : 0 < z := by
    rw [hzdef]
    exact div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)
  obtain ⟨δ, hδpos, hδ⟩ := proto_pos_near_zero h hu0 hdu0 hz
  obtain ⟨c, hc, hczero⟩ := exists_jacobi_zero_on_Ioc_pi_sqrt hK hk h hu0
  have hcδ : δ ≤ c := by
    by_contra hlt
    exact absurd hczero (ne_of_gt (hδ c hc.1 (lt_of_not_ge hlt) hc.2))
  set S : Set ℝ := {t : ℝ | 0 < t ∧ u t = 0} with hSdef
  set S' : Set ℝ := Icc δ z ∩ (Icc (0 : ℝ) z ∩ u ⁻¹' {0}) with hS'def
  have hS'closed : IsClosed S' := by
    rw [hS'def]
    exact isClosed_Icc.inter (h.continuousOn_u.preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton)
  have hS'ne : S'.Nonempty :=
    ⟨c, ⟨⟨hcδ, hc.2⟩, ⟨⟨hc.1.le, hc.2⟩, hczero⟩⟩⟩
  have hS'bdd : BddBelow S' := ⟨δ, fun y hy => hy.1.1⟩
  have hS_bdd : BddBelow S := ⟨0, fun y hy => hy.1.le⟩
  have hmem : sInf S' ∈ S' := hS'closed.csInf_mem hS'ne hS'bdd
  have hS'sub : S' ⊆ S := fun y hy => ⟨lt_of_lt_of_le hδpos hy.1.1, hy.2.2⟩
  have hle : sInf S ≤ sInf S' :=
    le_csInf hS'ne (fun y hy => csInf_le hS_bdd (hS'sub hy))
  have hge : sInf S' ≤ sInf S := by
    refine le_csInf ⟨c, ⟨hc.1, hczero⟩⟩ ?_
    intro y hy
    rcases le_or_gt y z with hyz | hzy
    · have hyδ : δ ≤ y := by
        by_contra hlt
        exact absurd hy.2 (ne_of_gt (hδ y hy.1 (lt_of_not_ge hlt) hyz))
      exact csInf_le hS'bdd ⟨⟨hyδ, hyz⟩, ⟨⟨hy.1.le, hyz⟩, hy.2⟩⟩
    · exact le_trans (csInf_le hS'bdd ⟨⟨hcδ, hc.2⟩,
        ⟨⟨hc.1.le, hc.2⟩, hczero⟩⟩) (le_trans hc.2 hzy.le)
  have hsInfEq : sInf S' = sInf S := le_antisymm hge hle
  have hsInfS : u (sInf S) = 0 := by
    rw [← hsInfEq]
    exact hmem.2.2
  have hposS : 0 < sInf S := by
    rw [← hsInfEq]
    exact lt_of_lt_of_le hδpos hmem.1.1
  refine ⟨by simpa [firstPositiveZero, hSdef] using hsInfS, ?_, ?_⟩
  · simpa [firstPositiveZero, hSdef] using hposS
  · intro t ht htzero
    have htS : t ∈ S := ⟨ht.1, htzero⟩
    have := csInf_le hS_bdd htS
    exact absurd this (not_le.mpr ht.2)

end Poincare.L4.GeodesicComparison
