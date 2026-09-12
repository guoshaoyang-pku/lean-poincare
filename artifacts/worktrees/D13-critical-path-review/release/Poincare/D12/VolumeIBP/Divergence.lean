/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Regularity

/-!
# The chart divergence theorem with compact support

On the chart `Vec d = ℝᵈ` we prove the **weighted divergence theorem**: for a `C¹` weight `ω`
and a `C¹` vector field `X` with compact support,

`∫ x, ∑ i, ∂ᵢ(ω · Xᵢ)(x) dx = 0`,

from mathlib's Euclidean box divergence theorem
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` (no divergence theorem is
assumed: the box theorem is a mathlib theorem). The compact support is used twice: to find a box
containing it (extreme value theorem on each coordinate), and to kill the boundary face terms.

Specializing the weight to the Riemannian density `ω = ρ = √(det g)` gives the **chart divergence
theorem for the Riemannian measure**: for `div_g X = ρ⁻¹ · ∑ᵢ ∂ᵢ(ρ Xᵢ)`,

`∫ div_g X dvol = 0`,

the identity the entropy chain consumes (`∫ Δ_g f dvol = 0`, see `IBP.lean`).

The dimension is written `d = n + 1` because the pinned mathlib box theorem is stated on
`Fin (n+1) → ℝ`; the `n = 0` case is dimension 1.
-/

open scoped BigOperators ENNReal NNReal Topology

noncomputable section

open MeasureTheory Set Function

namespace Poincare.D12.VolumeIBP

/-- Every compact subset of `Vec d` lies in some open box (a product of open intervals), together
with the coordinatewise ordering of the box corners. -/
lemma exists_pi_Ioo_supset_compact {d : ℕ} (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ a b : Vec d, (∀ i : Fin d, a i ≤ b i) ∧ K ⊆ Set.pi Set.univ fun i => Ioo (a i) (b i) := by
  classical
  by_cases hne : K.Nonempty
  · have hmin_fun : ∀ i : Fin d, ∃ mᵢ ∈ K, IsMinOn (fun x : Vec d => x i) K mᵢ := by
      intro i
      exact hK.exists_isMinOn hne (continuous_apply i).continuousOn
    have hmax_fun : ∀ i : Fin d, ∃ Mᵢ ∈ K, IsMaxOn (fun x : Vec d => x i) K Mᵢ := by
      intro i
      exact hK.exists_isMaxOn hne (continuous_apply i).continuousOn
    choose m hmK hmin using hmin_fun
    choose M hMK hmax using hmax_fun
    refine ⟨fun i => m i i - 1, fun i => M i i + 1, ?_, ?_⟩
    · intro i
      have hmm : m i i ≤ M i i := Filter.eventually_principal.1 (hmax i) (m i) (hmK i)
      linarith
    · intro x hx
      rw [Set.mem_univ_pi]
      intro i
      have hminx : m i i ≤ x i := Filter.eventually_principal.1 (hmin i) x hx
      have hmaxx : x i ≤ M i i := Filter.eventually_principal.1 (hmax i) x hx
      exact ⟨by linarith, by linarith⟩
  · refine ⟨0, 1, ?_, ?_⟩
    · intro i
      norm_num
    · intro x hx
      exact (hne ⟨x, hx⟩).elim

namespace ChartMetric

variable {n : ℕ}

/-- The `i`-th coordinate partial derivative of a scalar function on the chart
(Euclidean chart gradient component): `∂ᵢ f x = fderiv f x eᵢ`. -/
def partialDeriv (i : Fin (n + 1)) (f : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The weighted divergence `∑ᵢ ∂ᵢ(ω · Xᵢ)` of a vector field `X` with weight `ω`. -/
def weightedDivergence (ω : Vec (n + 1) → ℝ) (X : Vec (n + 1) → Vec (n + 1))
    (x : Vec (n + 1)) : ℝ :=
  ∑ i, fderiv ℝ (fun y => ω y * X y i) x (Pi.single i 1)

variable (G : ChartMetric (n + 1))

/-- The metric divergence `ρ⁻¹ · ∑ᵢ ∂ᵢ(ρ · Xᵢ)`, the divergence with respect to the Riemannian
measure of the metric. -/
def divergence (X : Vec (n + 1) → Vec (n + 1)) (x : Vec (n + 1)) : ℝ :=
  weightedDivergence G.density X x / G.density x

/-- **Weighted chart divergence theorem**: for a `C¹` weight `ω` and a `C¹` compactly supported
vector field `X`, the integral of the weighted divergence vanishes. Proved from mathlib's box
divergence theorem; no divergence theorem is assumed. -/
theorem weighted_divergence_integral_eq_zero (ω : Vec (n + 1) → ℝ) (hω : ContDiff ℝ 1 ω)
    (X : Vec (n + 1) → Vec (n + 1)) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ x, weightedDivergence ω X x = 0 := by
  classical
  -- a box containing the topological support
  have hK : IsCompact (tsupport X) := hXc.isCompact
  rcases exists_pi_Ioo_supset_compact (tsupport X) hK with ⟨a, b, hle, hbox⟩
  have hsuppIoo : support X ⊆ Set.pi Set.univ (fun i => Ioo (a i) (b i)) :=
    (subset_tsupport X).trans hbox
  have hXzero : ∀ x, x ∉ Set.pi Set.univ (fun i => Ioo (a i) (b i)) → X x = 0 := by
    intro x hx
    by_contra hnx
    exact hx (hsuppIoo (mem_support.mpr hnx))
  let F : Fin (n + 1) → Vec (n + 1) → ℝ := fun i x => ω x * X x i
  let F' : Fin (n + 1) → Vec (n + 1) → Vec (n + 1) →L[ℝ] ℝ :=
    fun i x => fderiv ℝ (fun y => ω y * X y i) x
  have hXcoord : ∀ i, ContDiff ℝ 1 (fun x : Vec (n + 1) => X x i) := fun i => by
    have hproj : ContDiff ℝ ⊤ (fun y : Vec (n + 1) => y i) :=
      (ContinuousLinearMap.proj i : Vec (n + 1) →L[ℝ] ℝ).contDiff
    change ContDiff ℝ 1 ((fun y : Vec (n + 1) => y i) ∘ X)
    exact ContDiff.comp (hproj.of_le le_top) hX
  have hFc : ∀ i, ContDiff ℝ 1 (F i) := fun i => hω.mul (hXcoord i)
  have hFcont : ∀ i, ContinuousOn (F i) (Icc a b) := fun i => (hFc i).continuous.continuousOn
  have hdF : ∀ x ∈ (Set.pi Set.univ fun i => Ioo (a i) (b i)) \ (∅ : Set (Vec (n + 1))), ∀ i,
      HasFDerivAt (F i) (F' i x) x := by
    intro x _ i
    exact ((hFc i).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hDcont : Continuous (fun x : Vec (n + 1) => ∑ i, F' i x (Pi.single i 1)) := by
    refine continuous_finsetSum (Finset.univ : Finset (Fin (n + 1))) fun i _ => ?_
    exact ((ContinuousLinearMap.apply ℝ (Fₗ := ℝ) (Pi.single i 1)).continuous.comp
      ((hFc i).continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)))
  have hiBox : IntegrableOn (fun x => ∑ i, F' i x (Pi.single i 1)) (Icc a b) :=
    hDcont.continuousOn.integrableOn_compact isCompact_Icc
  -- the divergence vanishes outside the closed box
  have hDzero : ∀ x ∈ (Icc a b)ᶜ, (∑ i, F' i x (Pi.single i 1)) = 0 := by
    intro x hx
    have hxoo : x ∉ Set.pi Set.univ (fun i => Ioo (a i) (b i)) := by
      intro hx'
      apply hx
      rw [← pi_univ_Icc]
      exact Set.mem_univ_pi.2 fun i =>
        ⟨(Set.mem_univ_pi.1 hx' i).1.le, (Set.mem_univ_pi.1 hx' i).2.le⟩
    have hxT : x ∈ (tsupport X)ᶜ := by
      intro hxT'
      exact hxoo (hbox hxT')
    have hXeq0 : X x = 0 := by
      by_contra hnx
      exact hxT (subset_tsupport X (mem_support.mpr hnx))
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz : (fun y => ω y * X y i) =ᶠ[𝓝 x] fun _ : Vec (n + 1) => (0 : ℝ) := by
      filter_upwards [IsOpen.mem_nhds (isClosed_tsupport X).isOpen_compl hxT] with y hy
      have hyX : X y = 0 := by
        by_contra hny
        exact hy (subset_tsupport X (mem_support.mpr hny))
      simp [hyX]
    have hfd : fderiv ℝ (fun y => ω y * X y i) x =
        fderiv ℝ (fun _ : Vec (n + 1) => (0 : ℝ)) x := hz.fderiv_eq
    unfold F'
    have hfd' : (fderiv ℝ (fun y => ω y * X y i) x) (Pi.single i 1) = 0 := by
      rw [hfd]
      simpa using congrArg (fun L => L (Pi.single i 1))
        (fderiv_const (𝕜 := ℝ) (E := Vec (n + 1)) (x := x) (c := (0 : ℝ)))
    rw [hfd']
  -- compact support of the divergence
  have hDc : HasCompactSupport (fun x => ∑ i, F' i x (Pi.single i 1)) := by
    have hsuppD : support (fun x => ∑ i, F' i x (Pi.single i 1)) ⊆ Icc a b := by
      intro x hx
      by_contra hx'
      exact (mem_support.mp hx) (hDzero x hx')
    have htsuppD : tsupport (fun x => ∑ i, F' i x (Pi.single i 1)) ⊆ Icc a b := by
      rw [← isClosed_Icc.closure_eq]
      exact closure_mono hsuppD
    simpa [HasCompactSupport] using
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) htsuppD
  have hDi : Integrable (fun x => ∑ i, F' i x (Pi.single i 1)) :=
    hDcont.integrable_of_hasCompactSupport hDc
  -- the face terms vanish
  have hfaces : ∀ i, (∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (Fin.insertNth i (b i) x)) -
        ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (Fin.insertNth i (a i) x) = 0 := by
    intro i
    have hFfront : ∀ y : Vec n, F i (Fin.insertNth i (b i) y) = 0 := by
      intro y
      unfold F
      have hyoo : Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) y ∉
          Set.pi Set.univ (fun j => Ioo (a j) (b j)) := by
        intro h
        have hmem : (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) y) i ∈
            Ioo (a i) (b i) := Set.mem_univ_pi.1 h i
        rw [Fin.insertNth_apply_same] at hmem
        exact (lt_irrefl (b i)) (mem_Ioo.mp hmem).2
      rw [hXzero (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (b i) y) hyoo]
      simp
    have hFback : ∀ y : Vec n, F i (Fin.insertNth i (a i) y) = 0 := by
      intro y
      unfold F
      have hyoo : Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) y ∉
          Set.pi Set.univ (fun j => Ioo (a j) (b j)) := by
        intro h
        have hmem : (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) y) i ∈
            Ioo (a i) (b i) := Set.mem_univ_pi.1 h i
        rw [Fin.insertNth_apply_same] at hmem
        exact (lt_irrefl (a i)) (mem_Ioo.mp hmem).1
      rw [hXzero (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i (a i) y) hyoo]
      simp
    have hI1 : ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        F i (Fin.insertNth i (b i) x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero
        (t := Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove))
        (f := fun x : Vec n => F i (Fin.insertNth i (b i) x)) (by intro x _; exact hFfront x)
    have hI2 : ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        F i (Fin.insertNth i (a i) x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero
        (t := Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove))
        (f := fun x : Vec n => F i (Fin.insertNth i (a i) x)) (by intro x _; exact hFback x)
    rw [hI1, hI2, sub_self]
  -- apply mathlib's box divergence theorem
  have hboxThm := integral_divergence_of_hasFDerivAt_off_countable' a b
    (by intro i; exact hle i) F F' (∅ : Set (Vec (n + 1))) countable_empty hFcont hdF hiBox
  have hboxIntegral : ∫ x in Icc a b, (∑ i, F' i x (Pi.single i 1)) = 0 := by
    rw [hboxThm]
    refine Finset.sum_eq_zero fun i _ => hfaces i
  -- lift from the box to the whole space
  have hfull : ∫ x, (∑ i, F' i x (Pi.single i 1)) =
      ∫ x in Icc a b, (∑ i, F' i x (Pi.single i 1)) := by
    rw [← integral_add_compl (s := Icc a b) isClosed_Icc.measurableSet hDi]
    have hc : ∫ x in (Icc a b)ᶜ, (∑ i, F' i x (Pi.single i 1)) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (t := (Icc a b)ᶜ) hDzero
    rw [hc]
    simp
  simpa [weightedDivergence, F, F'] using (show
    ∫ x : Vec (n + 1), (∑ i, F' i x (Pi.single i 1)) = 0 by exact hfull.trans hboxIntegral)

/-- **Chart divergence theorem for the Riemannian measure**: a compactly supported `C¹` vector
field has vanishing metric-divergence integral: `∫ div_g X dvol = 0`. -/
theorem divergence_integral_eq_zero (X : Vec (n + 1) → Vec (n + 1)) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ x, G.divergence X x ∂G.riemannianMeasure = 0 := by
  rw [G.integral_riemannianMeasure_eq]
  have hfun : (fun x : Vec (n + 1) => G.divergence X x * G.density x) =
      weightedDivergence G.density X := by
    funext x
    rw [divergence, div_mul_cancel₀ (weightedDivergence G.density X x) (G.density_ne_zero x)]
  rw [hfun]
  exact weighted_divergence_integral_eq_zero G.density G.density_contDiff_one X hX hXc

/-- `∫ div_g X dvol = 0` in the density-weighted form. -/
lemma divergence_integral_eq_zero_density (X : Vec (n + 1) → Vec (n + 1))
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ x, G.divergence X x * G.density x = 0 := by
  have hfun : (fun x : Vec (n + 1) => G.divergence X x * G.density x) =
      weightedDivergence G.density X := by
    funext x
    rw [divergence, div_mul_cancel₀ (weightedDivergence G.density X x) (G.density_ne_zero x)]
  rw [hfun]
  exact weighted_divergence_integral_eq_zero G.density G.density_contDiff_one X hX hXc

end ChartMetric

end Poincare.D12.VolumeIBP
