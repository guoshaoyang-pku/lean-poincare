/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10 builder

# D10 — The semidiscrete (finite-dimensional ODE) comparison lemma

Kernel-checked fallback theorem for the parabolic maximum principle: the comparison principle
for the semidiscrete heat equation, i.e. for the cooperative ODE system obtained by
discretising the Laplacian in space (the *method of lines*).

If `w : ℝ → Fin n → ℝ` is differentiable on `[0,T]`, satisfies `w ≤ 0` at time `0`, and
obeys the cooperative differential inequality

`wᵢ' ≤ ∑_{j ≠ i} a_{ij} (w_j - w_i)`,  `a_{ij} ≥ 0`,

then `w ≤ 0` on `[0,T]` (`semidiscrete_comparison_principle`).  The case `a_{ij} = 1` is the
discrete Laplacian / discrete maximum principle (`semidiscrete_heat_comparison`), and the
equivalent matrix form with a cooperative matrix whose row sums are `≤ 0` is
`semidiscrete_comparison_matrix`.  The scalar case `φ' ≤ 0`, `φ 0 ≤ 0 ⟹ φ ≤ 0` is
`scalar_ode_comparison`.

The proof is the ODE analogue of the `u - εt` trick: subtracting `εt` from every component
makes the inequality strict at the point where the perturbation attains its maximum, and the
maximal component of a cooperative system cannot cross `0` upwards.
-/

import Poincare.D10.MaximumPrincipleRN.SecondDerivativeTest

namespace Poincare.D10.MaximumPrincipleRN

open Set Filter
open scoped Topology

/-- **Scalar ODE comparison principle.**  If `φ' ≤ 0` on `[0,T]` and `φ 0 ≤ 0`, then
`φ ≤ 0` on `[0,T]`. -/
theorem scalar_ode_comparison {φ φ' : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hφ : ∀ t ∈ Icc 0 T, HasDerivAt φ (φ' t) t)
    (hφ0 : φ 0 ≤ 0) (hsub : ∀ t ∈ Icc 0 T, φ' t ≤ 0) :
    ∀ t ∈ Icc 0 T, φ t ≤ 0 := by
  have hcont : ContinuousOn φ (Icc 0 T) := fun t ht =>
    (hφ t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Icc 0 T)) := fun t ht =>
    (hφ t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn φ (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont hdiff fun t ht => by
      rw [interior_Icc] at ht
      rw [(hφ t ⟨ht.1.le, ht.2.le⟩).deriv]
      exact hsub t ⟨ht.1.le, ht.2.le⟩
  intro t ht
  exact le_trans (hanti ⟨le_rfl, hT⟩ ht ht.1) hφ0

/-- The `εt` perturbation step, isolated for reuse by the cooperative and the matrix form of
the semidiscrete comparison principle.

If a component of `w` is positive somewhere on `[0,T]`, then for a suitable `ε > 0` the
perturbed field `W = w - εt` attains a positive maximum at a point `t₀ ∈ (0,T]`, `i₀`, where
the time derivative of `w` is at least `ε` and `i₀` is a maximal component. -/
private theorem exists_critical_point {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    {w w' : ℝ → Fin n → ℝ}
    (hw_diff : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s : ℝ => w s i) (w' t i) t)
    (hw0 : ∀ i, w 0 i ≤ 0)
    (t₁ : ℝ) (ht₁ : t₁ ∈ Icc 0 T) (i₁ : Fin n) (hi₁ : 0 < w t₁ i₁) :
    ∃ (ε t₀ : ℝ) (i₀ : Fin n), 0 < ε ∧ t₀ ∈ Ioc 0 T ∧ 0 ≤ w' t₀ i₀ - ε ∧
      0 < w t₀ i₀ ∧ ∀ j, w t₀ j ≤ w t₀ i₀ := by
  -- choose `ε > 0` small enough that the perturbed maximum is still positive
  obtain ⟨ε, hεpos, hεT⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * T < w t₁ i₁ :=
    ⟨w t₁ i₁ / (2 * T), by positivity, by
      have h2 : w t₁ i₁ / (2 * T) * T = w t₁ i₁ / 2 := by field_simp
      rw [h2]
      linarith⟩
  set W : ℝ → Fin n → ℝ := fun t i => w t i - ε * t with hW
  have hW_apply : ∀ t i, W t i = w t i - ε * t := fun _ _ => rfl
  -- maxima of the components of `W` over `[0,T]`
  have hcont_fun (i : Fin n) : ContinuousOn (fun t : ℝ => W t i) (Icc 0 T) := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => w s i) (w' t i) t := hw_diff t ht i
    have h2 : HasDerivAt (fun s : ℝ => ε * s) ε t := by
      simpa using (hasDerivAt_id t).const_mul ε
    exact (h1.sub h2).continuousAt.continuousWithinAt
  have hmax_i : ∀ i : Fin n, ∃ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, W s i ≤ W t i := by
    intro i
    obtain ⟨t, ht, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT.le⟩ (hcont_fun i)
    exact ⟨t, ht, fun s hs => hmax hs⟩
  choose τ hτmem hτmax using hmax_i
  obtain ⟨i₀, -, hi₀max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun i => W (τ i) i)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hWmax : ∀ t ∈ Icc 0 T, ∀ i, W t i ≤ W (τ i₀) i₀ := fun t ht i =>
    le_trans (hτmax i t ht) (hi₀max i (Finset.mem_univ i))
  -- the maximum is positive and attained at a positive time
  have hWpos : 0 < W (τ i₀) i₀ := by
    have h1 : 0 < W t₁ i₁ := by
      rw [hW_apply]
      have : ε * t₁ ≤ ε * T := mul_le_mul_of_nonneg_left ht₁.2 hεpos.le
      linarith
    exact lt_of_lt_of_le h1 (hWmax t₁ ht₁ i₁)
  have ht₀_ne : τ i₀ ≠ 0 := by
    intro h
    have : W (τ i₀) i₀ ≤ 0 := by
      rw [hW_apply, h, mul_zero, sub_zero]
      exact hw0 i₀
    linarith
  have ht₀ : τ i₀ ∈ Ioc 0 T :=
    ⟨lt_of_le_of_ne (hτmem i₀).1 (Ne.symm ht₀_ne), (hτmem i₀).2⟩
  -- the time derivative of the maximal component at the maximum is `≥ 0`
  have htime_le : ∀ s ∈ Icc 0 (τ i₀), W s i₀ ≤ W (τ i₀) i₀ := fun s hs =>
    hWmax s ⟨hs.1, le_trans hs.2 (hτmem i₀).2⟩ i₀
  have hderiv : HasDerivAt (fun s : ℝ => W s i₀) (w' (τ i₀) i₀ - ε) (τ i₀) := by
    have h1 : HasDerivAt (fun s : ℝ => w s i₀) (w' (τ i₀) i₀) (τ i₀) :=
      hw_diff (τ i₀) (hτmem i₀) i₀
    have h2 : HasDerivAt (fun s : ℝ => ε * s) ε (τ i₀) := by
      simpa using (hasDerivAt_id (τ i₀)).const_mul ε
    exact h1.sub h2
  have hnonneg : 0 ≤ w' (τ i₀) i₀ - ε :=
    hasDerivWithinAt_nonneg_of_isMaxOn_Icc ht₀.1 htime_le hderiv.hasDerivWithinAt
  have hw_le : ∀ j, w (τ i₀) j ≤ w (τ i₀) i₀ := by
    intro j
    have h := hWmax (τ i₀) (hτmem i₀) j
    rw [hW_apply, hW_apply] at h
    linarith
  have hwpos : 0 < w (τ i₀) i₀ := by
    have := hWpos
    rw [hW_apply] at this
    have : 0 < ε * (τ i₀) := mul_pos hεpos ht₀.1
    linarith
  exact ⟨ε, τ i₀, i₀, hεpos, ht₀, hnonneg, hwpos, hw_le⟩

/-- **Semidiscrete comparison lemma (finite-dimensional / method of lines).**

Let `w : ℝ → Fin n → ℝ` (`n ≥ 1`) be differentiable on `[0,T]` with `T > 0`, with
`w 0 ≤ 0` componentwise and satisfying the *cooperative* differential inequality
`wᵢ' ≤ ∑_{j ≠ i} a_{ij} (w_j - w_i)` on `[0,T]`, where the off-diagonal coefficients
`a_{ij}` (`i ≠ j`) are nonnegative.  Then `w ≤ 0` on `[0,T]` componentwise. -/
theorem semidiscrete_comparison_principle {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    {a : Fin n → Fin n → ℝ} (ha : ∀ i j, i ≠ j → 0 ≤ a i j)
    {w w' : ℝ → Fin n → ℝ}
    (hw_diff : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s : ℝ => w s i) (w' t i) t)
    (hw0 : ∀ i, w 0 i ≤ 0)
    (hw_sub : ∀ t ∈ Icc 0 T, ∀ i,
      w' t i ≤ ∑ j ∈ Finset.univ.erase i, a i j * (w t j - w t i)) :
    ∀ t ∈ Icc 0 T, ∀ i, w t i ≤ 0 := by
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨t₁, ht₁, i₁, hi₁⟩ := hcon
  obtain ⟨ε, t₀, i₀, hεpos, ht₀, hnonneg, -, hw_le⟩ :=
    exists_critical_point hn hT hw_diff hw0 t₁ ht₁ i₁ hi₁
  have hsum : ∑ j ∈ Finset.univ.erase i₀, a i₀ j * (w t₀ j - w t₀ i₀) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    exact mul_nonpos_of_nonneg_of_nonpos (ha i₀ j (Ne.symm hji)) (sub_nonpos.mpr (hw_le j))
  have hsub := hw_sub t₀ ⟨ht₀.1.le, ht₀.2⟩ i₀
  linarith

/-- **Discrete maximum principle for the discrete Laplacian.**  The semidiscrete heat equation
`wᵢ' ≤ ∑_{j ≠ i} (w_j - w_i)` (unit coupling between all distinct components) preserves
nonpositivity. -/
theorem semidiscrete_heat_comparison {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    {w w' : ℝ → Fin n → ℝ}
    (hw_diff : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s : ℝ => w s i) (w' t i) t)
    (hw0 : ∀ i, w 0 i ≤ 0)
    (hw_sub : ∀ t ∈ Icc 0 T, ∀ i,
      w' t i ≤ ∑ j ∈ Finset.univ.erase i, (w t j - w t i)) :
    ∀ t ∈ Icc 0 T, ∀ i, w t i ≤ 0 :=
  semidiscrete_comparison_principle hn hT (fun _ _ _ => zero_le_one) hw_diff hw0
    (fun t ht i => by simpa using hw_sub t ht i)

/-- **Matrix form of the semidiscrete comparison lemma.**  Let `A` be a cooperative matrix
(`A i j ≥ 0` for `i ≠ j`) with nonpositive row sums, and suppose
`wᵢ' ≤ ∑_j A_{ij} w_j` on `[0,T]` with `w 0 ≤ 0`.  Then `w ≤ 0` on `[0,T]`.

For the cooperative form `A_{ij} = a_{ij}` (`i ≠ j`), `A_{ii} = -∑_{j≠i} a_{ij}` the hypothesis
`wᵢ' ≤ ∑_{j≠i} a_{ij}(w_j - w_i)` is *equivalent* to `wᵢ' ≤ ∑_j A_{ij} w_j`. -/
theorem semidiscrete_comparison_matrix {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    {A : Fin n → Fin n → ℝ} (hA : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ≤ 0)
    {w w' : ℝ → Fin n → ℝ}
    (hw_diff : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s : ℝ => w s i) (w' t i) t)
    (hw0 : ∀ i, w 0 i ≤ 0)
    (hw_sub : ∀ t ∈ Icc 0 T, ∀ i, w' t i ≤ ∑ j, A i j * w t j) :
    ∀ t ∈ Icc 0 T, ∀ i, w t i ≤ 0 := by
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨t₁, ht₁, i₁, hi₁⟩ := hcon
  obtain ⟨ε, t₀, i₀, hε, ht₀, hnonneg, hwpos, hw_le⟩ :=
    exists_critical_point hn hT hw_diff hw0 t₁ ht₁ i₁ hi₁
  have hrow_i : A i₀ i₀ + ∑ j ∈ Finset.univ.erase i₀, A i₀ j ≤ 0 := by
    have h := hrow i₀
    rwa [← Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun j => A i₀ j)
      (Finset.mem_univ i₀)] at h
  have hsum_le : ∑ j, A i₀ j * w t₀ j ≤ 0 := by
    have hsplit : ∑ j, A i₀ j * w t₀ j
        = A i₀ i₀ * w t₀ i₀ + ∑ j ∈ Finset.univ.erase i₀, A i₀ j * w t₀ j := by
      rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun j => A i₀ j * w t₀ j) (Finset.mem_univ i₀), add_comm]
    rw [hsplit]
    have h1 : ∑ j ∈ Finset.univ.erase i₀, A i₀ j * w t₀ j
        ≤ ∑ j ∈ Finset.univ.erase i₀, A i₀ j * w t₀ i₀ :=
      Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hw_le j) (hA i₀ j (Ne.symm (Finset.mem_erase.mp hj).1))
    have h2 : ∑ j ∈ Finset.univ.erase i₀, A i₀ j * w t₀ i₀
        = (∑ j ∈ Finset.univ.erase i₀, A i₀ j) * w t₀ i₀ :=
      (Finset.sum_mul (Finset.univ.erase i₀) (fun j => A i₀ j) (w t₀ i₀)).symm
    have h3 : (A i₀ i₀ + ∑ j ∈ Finset.univ.erase i₀, A i₀ j) * w t₀ i₀ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrow_i hwpos.le
    nlinarith [h1, h3]
  have hsub := hw_sub t₀ ⟨ht₀.1.le, ht₀.2⟩ i₀
  linarith

end Poincare.D10.MaximumPrincipleRN
