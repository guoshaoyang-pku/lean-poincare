-- A3 round-3 kernel-checked evidence for the redundant-hypothesis defect in
-- D12-comparison-geodesics (finding F12b).
-- Written by D13-cross-audit-360-cards; not derived from the producer card.
--
-- The unused-binder screen found five explicit hypotheses that the compiled
-- proofs never touch (all underscore-named in the producer source).  Here each
-- is *removed* and the sharp restatement proved: for the `_hT` cases the
-- remaining binder already implies `0 < T`, or the conclusion is vacuous;
-- for `_hab` the conclusion is vacuous when `b < a`.
import Poincare.D12.ComparisonGeodesics.VolumeRatio
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.D12.ComparisonGeodesics.SturmComparison

namespace A3R3

open Set
open Poincare.D12.ComparisonGeodesics

/-- `_hT` removed: `ht : t ∈ Ioo 0 T` already gives `0 < T`. -/
theorem a3_radialVolume_hasDerivAt_sharp {A : ℝ → ℝ} {T : ℝ}
    (hcont : ContinuousOn A (Icc 0 T)) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAtR (radialVolume A) (A t) t :=
  radialVolume_hasDerivAt (T := T) (lt_trans ht.1 ht.2) hcont ht

/-- `_hT` removed: `hx : x ∈ Ioc 0 T` already gives `0 < T`. -/
theorem a3_radialVolume_numerator_le_zero_sharp {T x : ℝ} {A Abar : ℝ → ℝ}
    (hx : x ∈ Ioc 0 T)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hA0 : A 0 = 0) (hAbar0 : Abar 0 = 0)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hratio : ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t → A t / Abar t ≤ A s / Abar s) :
    A x * radialVolume Abar x - radialVolume A x * Abar x ≤ 0 :=
  radialVolume_numerator_le_zero (T := T) (lt_of_lt_of_le hx.1 hx.2) hx hAcont hAbarcont
    hA0 hAbar0 hAbarpos hratio

/-- `_hT` removed: the conclusion is vacuous for `T ≤ 0`. -/
theorem a3_areaRatio_antitone_of_logDeriv_le_sharp {T : ℝ}
    {A dA Abar dAbar m mbar : ℝ → ℝ}
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR Abar (dAbar t) t)
    (hAcont : ContinuousOn A (Icc 0 T)) (hAbarcont : ContinuousOn Abar (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hAbarpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < Abar t)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    (hmAbar : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → mbar t = dAbar t / Abar t)
    (hmle : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t ≤ mbar t) :
    ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → s ≤ t →
      A t / Abar t ≤ A s / Abar s := by
  by_cases hT : 0 < T
  · exact areaRatio_antitone_of_logDeriv_le hT hA hAbar hAcont hAbarcont hApos
      hAbarpos hmA hmAbar hmle
  · intro s hs
    exact absurd (lt_of_lt_of_le hs.1 hs.2) hT

/-- `_hT` removed: the conclusion is vacuous for `T ≤ 0`. -/
theorem a3_radialVolume_pos_of_pos_sharp {A : ℝ → ℝ} {T : ℝ}
    (hcont : ContinuousOn A (Icc 0 T)) (hpos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < radialVolume A t := by
  by_cases hT : 0 < T
  · exact radialVolume_pos_of_pos hT hcont hpos
  · intro t ht
    exact absurd (lt_of_lt_of_le ht.1 ht.2) hT

/-- `_hab` removed: the conclusion is vacuous for `b < a`. -/
theorem a3_wronskian_antitoneOn_of_le_sharp
    {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₂ t ≤ k₁ t)
    (hsign : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 ≤ u₁ t * u₂ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b) :
    AntitoneOn (wronskian u₁ du₁ u₂ du₂) (Icc a b) := by
  by_cases hab : a ≤ b
  · exact wronskian_antitoneOn_of_le hab hk hsign h1 h2
  · intro x hx
    exact absurd (le_trans hx.1 hx.2) hab

/-- `_hdne` removed: the Riccati identity also holds for `d = 0` because `0/0 = 0` in `ℝ`. -/
theorem a3_euclidModelM_riccati_sharp {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    euclidModelDm d t + euclidModelM d t ^ 2 / (d : ℝ) + 0 = 0 := by
  unfold euclidModelM euclidModelDm
  field_simp [ht]
  ring

end A3R3

#print axioms A3R3.a3_euclidModelM_riccati_sharp
#print axioms A3R3.a3_radialVolume_hasDerivAt_sharp
#print axioms A3R3.a3_radialVolume_numerator_le_zero_sharp
#print axioms A3R3.a3_areaRatio_antitone_of_logDeriv_le_sharp
#print axioms A3R3.a3_radialVolume_pos_of_pos_sharp
#print axioms A3R3.a3_wronskian_antitoneOn_of_le_sharp
