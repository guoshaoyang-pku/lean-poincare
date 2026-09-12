/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)
-/

import Mathlib
import Poincare.Longrun.Geometry.MetricData
import Poincare.D9.DeTurck.SymbolModel

/-!
# Poincare.D13.ToppingAdapter.Scalar

**Upstream provenance.** The first part of this module transcribes, verbatim, the scalar
parabolic-symbol layer of the pinned Frenzymath snapshot,

  `formalized-sources/Topping/Topping/ParabolicPDE/Scalar.lean`

(commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`), upstream namespace
`Topping.ParabolicPDE`, re-namespaced here to `Poincare.D13.ToppingAdapter.Scalar`.  The
transcribed declarations (all with their upstream proof bodies, re-verified by the local
kernel) are:

* `ScalarSecondOrderCoefficients`, `ScalarSecondOrderJet` (structures);
* `euclideanNormSq`, `symbol`, `ScalarSecondOrderCoefficients.principalSymbol`,
  `IsPositiveDefinite`, `PointwiseParabolic`, `UniformlyParabolic` (definitions);
* `pointwiseParabolic_iff_symbol_positive`, `symbol_zero`, `symbol_add`, `symbol_smul`,
  `symbol_one`, `euclideanNormSq_nonneg`, `euclideanNormSq_pos`,
  `uniformlyParabolic_pointwiseParabolic` (Scalar.lean:101/107/111/123/168/173/177/188);
* `heatCoefficients` (Scalar.lean:198) and `heatCoefficients_principalSymbol`,
  `heatCoefficients_uniformlyParabolic`, `heatCoefficients_pointwiseParabolic`
  (Scalar.lean:204/210/217) — the Euclidean heat operator `∂ₜ - Δ` has principal symbol
  `|ξ|²`, uniformly parabolic with constant `1`;
* `symbol_congruence`, `IsPositiveDefinite.congruence` (Scalar.lean:231/252) — symbol
  covariance under linear changes of cotangent coordinates (the chart-transition law the
  local D12 parabolic layer uses to pass from the coordinate symbol to the intrinsic
  operator).

This is the upstream **parabolic-PDE layer** the local blocker **U6** records as missing: the
coordinate-level uniform-parabolicity certificate and its covariance.  The remaining upstream
Scalar.lean content (the exponential-conjugation jet block
`conjugatedScalarOperator_eq_quadratic_plus_lower`, Scalar.lean:265ff) is recorded as an
upstream source claim in the D13 result card, not transcribed here.

**Adapter part.** The second part of the module connects this transcribed layer to the local
D9 symbol model `Poincare.D9.DeTurck.SymbolModel` (`Poincare.Longrun.DeTurck`):

* `euclideanMetricData n` — the standard Euclidean `MetricData (Fin n → ℝ) (Fin n)` (dot
  product, standard basis): the flat-model instance of the D9 interface;
* `covectorOf` — the coordinate covector `ξ : Fin n → ℝ` as a linear functional;
* `covectorNormSq_euclidean_eq_euclideanNormSq` — the local `|ξ|²_g` equals the transcribed
  upstream `euclideanNormSq ξ` on the flat model;
* `heatPrincipalSymbol_eq_localLaplacianCoeff` — the transcribed upstream heat principal
  symbol equals the local D9 Laplacian coefficient `covectorNormSq g ξ` (the coefficient of
  `laplacianSymbol g ξ h = |ξ|² · h`): the local D9 layer and the upstream Topping scalar
  layer are the *same* symbol object on the flat model;
* `flowSymbol_eq_neg_heatPrincipalSymbol` — via the local D9 theorem `flowSymbol`, the
  symbol of the Ricci-DeTurck linearization `-2 Ric + L_W g` equals
  `-(heatCoefficients.principalSymbol x ξ) · h`: the strict-parabolicity certificate of the
  upstream MorganTian `canonicalRicciDeTurckStrictParabolic`
  (`formalized-sources/MorganTian/MorganTianLib/Ch03/RicciFlow/PDE/LocalExistence.lean:50`)
  in the local language, with the sign conventions matched (upstream parabolic symbol
  `+|ξ|²`, local DeTurck symbol `-|ξ|² · Id`).
-/

open scoped BigOperators

namespace Poincare.D13.ToppingAdapter.Scalar

/-! ## Verbatim transcription of `Topping/Topping/ParabolicPDE/Scalar.lean` -/

/-- Upstream Scalar.lean:13-17. -/
structure ScalarSecondOrderCoefficients (Ω : Type*) (n : ℕ) where
  a : Ω → Matrix (Fin n) (Fin n) ℝ
  b : Ω → Fin n → ℝ
  c : Ω → ℝ

/-- Upstream Scalar.lean:19-23. -/
structure ScalarSecondOrderJet (n : ℕ) where
  value : ℝ
  first : Fin n → ℝ
  second : Fin n → Fin n → ℝ

/-- Upstream Scalar.lean:72-74. -/
def euclideanNormSq {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  ∑ i, ξ i ^ 2

/-- Upstream Scalar.lean:76-78. -/
def symbol {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : ℝ :=
  dotProduct ξ (a.mulVec ξ)

/-- Upstream Scalar.lean:80-84. -/
def ScalarSecondOrderCoefficients.principalSymbol
    {Ω : Type*} {n : ℕ} (A : ScalarSecondOrderCoefficients Ω n)
    (x : Ω) (ξ : Fin n → ℝ) : ℝ :=
  symbol (A.a x) ξ

/-- Upstream Scalar.lean:86-89. -/
def IsPositiveDefinite {n : ℕ}
    (a : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ ξ, ξ ≠ 0 → 0 < symbol a ξ

/-- Upstream Scalar.lean:91-94. -/
def PointwiseParabolic {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n) : Prop :=
  ∀ x, IsPositiveDefinite (A.a x)

/-- Upstream Scalar.lean:96-100. -/
def UniformlyParabolic {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n) : Prop :=
  ∃ ell : ℝ, 0 < ell ∧
    ∀ x ξ, ell * euclideanNormSq ξ ≤ A.principalSymbol x ξ

/-- Upstream Scalar.lean:101-105. -/
theorem pointwiseParabolic_iff_symbol_positive
    {Ω : Type*} {n : ℕ} {A : ScalarSecondOrderCoefficients Ω n} :
    PointwiseParabolic A ↔
      ∀ x ξ, ξ ≠ 0 → 0 < A.principalSymbol x ξ := by
  rfl

/-- Upstream Scalar.lean:107-110. -/
theorem symbol_zero {n : ℕ} (ξ : Fin n → ℝ) :
    symbol (0 : Matrix (Fin n) (Fin n) ℝ) ξ = 0 := by
  simp [symbol]

/-- Upstream Scalar.lean:111-121. -/
theorem symbol_add {n : ℕ}
    (a₁ a₂ : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    symbol (a₁ + a₂) ξ =
      symbol a₁ ξ + symbol a₂ ξ := by
  unfold symbol
  rw [Matrix.add_mulVec]
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply, mul_add]

/-- Upstream Scalar.lean:123-136. -/
theorem symbol_smul {n : ℕ} (r : ℝ)
    (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    symbol (r • a) ξ = r * symbol a ξ := by
  unfold symbol
  rw [Matrix.smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, ξ i * (r * a.mulVec ξ i)) =
        ∑ i, r * (ξ i * a.mulVec ξ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = r * ∑ i, ξ i * a.mulVec ξ i := by
      rw [Finset.mul_sum]

/-- Upstream Scalar.lean:168-172. -/
theorem symbol_one {n : ℕ} (ξ : Fin n → ℝ) :
    symbol (1 : Matrix (Fin n) (Fin n) ℝ) ξ =
      euclideanNormSq ξ := by
  simp [symbol, euclideanNormSq, dotProduct, pow_two]

/-- Upstream Scalar.lean:173-176. -/
theorem euclideanNormSq_nonneg {n : ℕ} (ξ : Fin n → ℝ) :
    0 ≤ euclideanNormSq ξ := by
  exact Finset.sum_nonneg' (fun i => sq_nonneg (ξ i))

/-- Upstream Scalar.lean:177-186. -/
theorem euclideanNormSq_pos {n : ℕ} {ξ : Fin n → ℝ} (hξ : ξ ≠ 0) :
    0 < euclideanNormSq ξ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
  have hi' : ξ i ≠ 0 := by simpa using hi
  have hiff :
      0 < ∑ j : Fin n, ξ j ^ 2 ↔
        ∃ j ∈ (Finset.univ : Finset (Fin n)), 0 < ξ j ^ 2 :=
    Finset.sum_pos_iff_of_nonneg (fun j hj => sq_nonneg (ξ j))
  rw [euclideanNormSq, hiff]
  exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi'⟩

/-- Upstream Scalar.lean:188-197. -/
theorem uniformlyParabolic_pointwiseParabolic
    {Ω : Type*} {n : ℕ} {A : ScalarSecondOrderCoefficients Ω n}
    (hA : UniformlyParabolic A) : PointwiseParabolic A := by
  obtain ⟨ell, hell, hbound⟩ := hA
  intro x ξ hξ
  have hnorm : 0 < euclideanNormSq ξ := euclideanNormSq_pos hξ
  have hscaled : 0 < ell * euclideanNormSq ξ := mul_pos hell hnorm
  exact lt_of_lt_of_le hscaled (hbound x ξ)

/-- Upstream Scalar.lean:198-203 (`heatCoefficients`). -/
def heatCoefficients (Ω : Type*) (n : ℕ) :
    ScalarSecondOrderCoefficients Ω n where
  a := fun _ => 1
  b := fun _ _ => 0
  c := fun _ => 0

/-- Upstream Scalar.lean:204-208. -/
theorem heatCoefficients_principalSymbol {Ω : Type*} {n : ℕ}
    (x : Ω) (ξ : Fin n → ℝ) :
    (heatCoefficients Ω n).principalSymbol x ξ = euclideanNormSq ξ := by
  change symbol (1 : Matrix (Fin n) (Fin n) ℝ) ξ = _
  exact symbol_one ξ

/-- Upstream Scalar.lean:210-216. -/
theorem heatCoefficients_uniformlyParabolic (Ω : Type*) (n : ℕ) :
    UniformlyParabolic (heatCoefficients Ω n) := by
  refine ⟨1, by norm_num, ?_⟩
  intro x ξ
  rw [heatCoefficients_principalSymbol]
  simp

/-- Upstream Scalar.lean:217-219. -/
theorem heatCoefficients_pointwiseParabolic (Ω : Type*) (n : ℕ) :
    PointwiseParabolic (heatCoefficients Ω n) :=
  uniformlyParabolic_pointwiseParabolic (heatCoefficients_uniformlyParabolic Ω n)

/-- Upstream Scalar.lean:231-250. -/
theorem symbol_congruence {m n : ℕ}
    (J : Matrix (Fin m) (Fin n) ℝ)
    (a : Matrix (Fin m) (Fin m) ℝ) (ξ : Fin n → ℝ) :
    symbol (J.transpose * a * J) ξ = symbol a (J.mulVec ξ) := by
  unfold symbol
  calc
    ξ ⬝ᵥ (J.transpose * a * J).mulVec ξ =
        ξ ⬝ᵥ (J.transpose * a).mulVec (J.mulVec ξ) :=
      congrArg (fun z => ξ ⬝ᵥ z)
        (Matrix.mulVec_mulVec ξ (J.transpose * a) J).symm
    _ = ξ ⬝ᵥ J.transpose.mulVec (a.mulVec (J.mulVec ξ)) :=
      congrArg (fun z => ξ ⬝ᵥ z)
        (Matrix.mulVec_mulVec (J.mulVec ξ) J.transpose a).symm
    _ = a.mulVec (J.mulVec ξ) ⬝ᵥ J.mulVec ξ :=
      Matrix.dotProduct_transpose_mulVec J ξ (a.mulVec (J.mulVec ξ))
    _ = J.mulVec ξ ⬝ᵥ a.mulVec (J.mulVec ξ) :=
      dotProduct_comm _ _

/-- Upstream Scalar.lean:252-266. -/
theorem IsPositiveDefinite.congruence {m n : ℕ}
    (J : Matrix (Fin m) (Fin n) ℝ)
    (a : Matrix (Fin m) (Fin m) ℝ)
    (ha : IsPositiveDefinite a)
    (hJ : Function.Injective J.mulVec) :
    IsPositiveDefinite (J.transpose * a * J) := by
  intro ξ hξ
  rw [symbol_congruence]
  apply ha
  intro hzero
  apply hξ
  apply hJ
  simpa using hzero

/-! ## Adapter part: the transcribed Topping layer on the local D9 flat model -/

open Poincare.Longrun.Geometry
open Poincare.Longrun.DeTurck

/-- **The standard Euclidean metric datum on `Fin n → ℝ`**: dot product, standard basis.
This is the flat-model instance of the D9 `MetricData` interface; its `covectorNormSq`
is `∑ i, ξ i²`, the transcribed upstream `euclideanNormSq`. -/
noncomputable def euclideanMetricData (n : ℕ) : MetricData (Fin n → ℝ) (Fin n) where
  form := LinearMap.mk₂ ℝ (fun X Y => dotProduct X Y)
    (by intro X₁ X₂ Y; simp only [add_dotProduct])
    (by intro a X Y; simp only [smul_dotProduct, smul_eq_mul])
    (by intro X Y₁ Y₂; simp only [dotProduct_add])
    (by intro a X Y; simp only [dotProduct_smul, smul_eq_mul])
  symm := by
    intro X Y
    exact dotProduct_comm X Y
  pos_def := by
    intro X hX
    rcases Function.ne_iff.mp hX with ⟨i, hi⟩
    have hi' : X i ≠ 0 := by simpa using hi
    simp only [dotProduct]
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ X j * X j := by
      intro j _
      exact mul_self_nonneg (X j)
    have hwit : ∃ j ∈ (Finset.univ : Finset (Fin n)), 0 < X j * X j :=
      ⟨i, Finset.mem_univ i, by simpa [sq] using (sq_pos_of_ne_zero hi')⟩
    exact Finset.sum_pos' hnonneg hwit
  basis := Module.Basis.ofEquivFun (LinearEquiv.refl ℝ (Fin n → ℝ))
  orthonormal := by
    intro i j
    have hb (k : Fin n) : (Module.Basis.ofEquivFun (LinearEquiv.refl ℝ (Fin n → ℝ))) k =
        Finsupp.single k 1 := by
      ext l
      simp [Module.Basis.coe_ofRepr]
      by_cases hkl : k = l
      · subst l
        simp
      · have hlk : ¬ l = k := fun h => hkl h.symm
        simp [hlk, hkl]
    change dotProduct ((Module.Basis.ofEquivFun (LinearEquiv.refl ℝ (Fin n → ℝ))) i)
      ((Module.Basis.ofEquivFun (LinearEquiv.refl ℝ (Fin n → ℝ))) j) = if i = j then 1 else 0
    rw [hb i, hb j]
    by_cases hij : i = j
    · subst j
      simp [dotProduct, Finsupp.single_apply]
    · simp only [dotProduct, Finsupp.single_apply]
      have hzero : (∑ x, (if i = x then 1 else 0) * (if j = x then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hik : i = k
        · subst k
          have hji : ¬ j = i := fun h => hij h.symm
          simp [hji]
        · simp [hik]
      simpa [hij] using hzero

/-- The coordinate covector `ξ : Fin n → ℝ` as a linear functional `X ↦ ξ · X`. -/
noncomputable def covectorOf {n : ℕ} (ξ : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun X => dotProduct ξ X
  map_add' := by
    intro X Y
    simp only [dotProduct_add]
  map_smul' := by
    intro a X
    change dotProduct ξ (a • X) = a * dotProduct ξ X
    rw [dotProduct_smul]
    rfl

/-- On the flat model, the local D9 covector norm `|ξ|²_g` equals the transcribed upstream
`euclideanNormSq ξ`. -/
theorem covectorNormSq_euclidean_eq_euclideanNormSq {n : ℕ} (ξ : Fin n → ℝ) :
    covectorNormSq (euclideanMetricData n) (covectorOf ξ) = euclideanNormSq ξ := by
  rw [covectorNormSq_eq_sum_sq, euclideanNormSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : (euclideanMetricData n).basis i = Finsupp.single i 1 := by
    ext l
    simp [euclideanMetricData, Module.Basis.coe_ofRepr]
    by_cases hil : i = l
    · subst l
      simp
    · have hli : ¬ l = i := fun h => hil h.symm
      simp [hli, hil]
  change (dotProduct ξ ((euclideanMetricData n).basis i)) ^ 2 = ξ i ^ 2
  rw [hb]
  simp [dotProduct, Finsupp.single_apply]

/-- **Adapter theorem (U6).** The transcribed upstream heat principal symbol equals the
local D9 Laplacian coefficient: `heatCoefficients.principalSymbol x ξ = |ξ|²_g` of the
D9 `MetricData` layer.  The local `laplacianSymbol g ξ h = covectorNormSq g ξ • h`
(D9 `SymbolModel`) and the upstream `heatCoefficients` therefore describe the *same*
principal symbol on the flat model. -/
theorem heatPrincipalSymbol_eq_localLaplacianCoeff {n : ℕ}
    (x : Fin n → ℝ) (ξ : Fin n → ℝ) :
    (heatCoefficients (Fin n → ℝ) n).principalSymbol x ξ =
      covectorNormSq (euclideanMetricData n) (covectorOf ξ) := by
  rw [heatCoefficients_principalSymbol]
  exact (covectorNormSq_euclidean_eq_euclideanNormSq ξ).symm

/-- **Adapter theorem (U8, symbol level).** Via the local D9 theorem `flowSymbol`
(`σ(-2 Ric + L_W g) = -laplacianSymbol`), the symbol of the Ricci-DeTurck linearization
equals `-heatCoefficients.principalSymbol x ξ · h`: the negative of the transcribed upstream
heat principal symbol times the identity.  This is the local form of the strict-parabolicity
certificate `canonicalRicciDeTurckStrictParabolic`
(`MorganTianLib/Ch03/RicciFlow/PDE/LocalExistence.lean:50`) with the sign conventions
matched (upstream parabolic symbol `+|ξ|²` of `∂ₜ - Δ`; local flow symbol `-|ξ|² · Id` of
`∂ₜg = -2Ric + L_W g`). -/
theorem flowSymbol_eq_neg_heatPrincipalSymbol {n : ℕ}
    (ξ : Fin n → ℝ) (h : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (X Y : Fin n → ℝ) :
    ((-2 : ℝ) • ricciSymbol (euclideanMetricData n) (covectorOf ξ) h +
        lieSymbol (euclideanMetricData n) (covectorOf ξ) h) X Y =
      - (heatCoefficients (Fin n → ℝ) n).principalSymbol (0 : Fin n → ℝ) ξ * h X Y := by
  calc
    ((-2 : ℝ) • ricciSymbol (euclideanMetricData n) (covectorOf ξ) h +
        lieSymbol (euclideanMetricData n) (covectorOf ξ) h) X Y =
        - (covectorNormSq (euclideanMetricData n) (covectorOf ξ) * h X Y) := by
      rw [flowSymbol, laplacianSymbol]
      simp only [LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
    _ = - (heatCoefficients (Fin n → ℝ) n).principalSymbol (0 : Fin n → ℝ) ξ * h X Y := by
      rw [heatCoefficients_principalSymbol, covectorNormSq_euclidean_eq_euclideanNormSq]
      ring

end Poincare.D13.ToppingAdapter.Scalar
