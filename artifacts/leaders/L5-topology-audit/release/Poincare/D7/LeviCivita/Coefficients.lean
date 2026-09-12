import Poincare.D7.LeviCivita.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Poincare.D7.LeviCivita.Coefficients

**D7 Levi-Civita smoothness/functoriality layer, part 2: connection coefficients and their
smoothness interface.**

This module provides the connection-coefficient interface that the smoothness layer is phrased in.

## Part 1: basis coefficients of an abstract connection

For an abstract connection `∇` and a metric datum with orthonormal basis `eᵢ`, the connection
coefficients are `Γ^k_{ij} = (∇_{eᵢ} eⱼ)^k`, the `k`-th coordinate of `∇_{eᵢ} eⱼ`. The file proves:

* `sum_connectionCoefficient_smul` — the reconstruction formula
  `∇_{eᵢ} eⱼ = ∑ k, Γ^k_{ij} eₖ`;
* `isMetricCompatible_coefficient_relation` — metric compatibility in coefficients:
  `Γ^k_{ij} + Γ^j_{ik} = 0`;
* `isTorsionFree_coefficient_relation` — torsion-freeness in coefficients:
  `Γ^k_{ij} - Γ^k_{ji} = C^k_{ij}` where `C` is the bracket coefficient;
* `connectionCoefficient_affine` and the affine closure of both relations, i.e. the
  coefficient-level form of the mean-connection functoriality of task item 2a.

## Part 2: the smooth coefficient interface

A point-dependent connection field `∇ : P → V →L[ℝ] V →L[ℝ] V` (the local expression of a
connection in a chart with model space `P`) has coefficient functions
`x ↦ ℓ (∇ x eᵢ eⱼ)` for a continuous linear coefficient functional `ℓ`. The main results are:

* `contMDiff_coefficientField` — if the connection field is `C^n`, then so are all its
  coefficients. The proof uses `ContMDiff.clm_apply` and `ContinuousLinearMap.contMDiff`; it does
  **not** need a finite-dimensionality argument, because the coefficient functional is continuous
  by hypothesis (in a chart, coordinate functionals are continuous linear functionals).
* `contMDiff_coefficientField_comp_chart` — **the chart-smoothness hypothesis**: if `φ : P' → P`
  is a `C^n` chart and the connection field is `C^n`, then the pulled-back coefficients
  `p ↦ coefficientField (φ p)` are `C^n`. This is the precise sense in which the coefficient
  interface is smooth under a stated chart-smoothness hypothesis.
* `SmoothCoefficientSystem` — the bundled interface (coefficient functions + `C^n` smoothness +
  the torsion and metric relations against a bracket-coefficient field). It is closed under
  affine combinations (`SmoothCoefficientSystem.affineCombination`) and under pullback along a
  `C^n` chart (`SmoothCoefficientSystem.pullback`), and it is inhabited by the constant
  coefficients of any abstract connection (`SmoothCoefficientSystem.const`).

## Honest boundary

Part 2 takes the smoothness of the connection field (or of the coefficient functions) as an
explicit hypothesis. Deriving it from the smoothness of the metric is exactly the missing
mathlib theorem recorded as `Poincare.D7.LeviCivita.LeviCivitaSmoothnessStatement` in
`Poincare.D7.LeviCivita.Blocked`; the chart-level Koszul-formula version is proved in
`Poincare.D7.LeviCivita.Koszul`. All proofs are complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

open Bundle
open scoped BigOperators Manifold ContDiff

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace LeviCivita

open Poincare.Longrun.Geometry

universe v w u

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Part 1: basis coefficients of an abstract connection -/

/-- **Connection coefficients** of an abstract connection in the orthonormal basis of a metric
datum: `Γ^k_{ij}` is the `k`-th coordinate of `∇_{eᵢ} eⱼ`, i.e.
`∇_{eᵢ} eⱼ = ∑ k, Γ^k_{ij} eₖ`. -/
noncomputable def connectionCoefficient (m : MetricData V ι)
    (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) (i j k : ι) : ℝ :=
  m.basis.repr (nabla (m.basis i) (m.basis j)) k

/-- **Bracket coefficients** in the orthonormal basis: `[eᵢ, eⱼ] = ∑ k, C^k_{ij} eₖ`. -/
noncomputable def bracketCoefficient (m : MetricData V ι) (b : LieBracketData ℝ V)
    (i j k : ι) : ℝ :=
  m.basis.repr (b.bracket (m.basis i) (m.basis j)) k

/-- **Reconstruction formula**: the connection coefficients reconstruct the connection on the
basis, `∇_{eᵢ} eⱼ = ∑ k, Γ^k_{ij} eₖ`. -/
theorem sum_connectionCoefficient_smul (m : MetricData V ι)
    (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) (i j : ι) :
    ∑ k : ι, connectionCoefficient m nabla i j k • m.basis k =
      nabla (m.basis i) (m.basis j) := by
  rw [← m.basis.sum_repr (nabla (m.basis i) (m.basis j))]
  exact Finset.sum_congr rfl fun k _ => by rw [connectionCoefficient]

/-- The metric pairing with a basis vector extracts the corresponding coefficient:
`⟨∇_{eᵢ} eⱼ, eₖ⟩ = Γ^k_{ij}`. -/
theorem form_nabla_basis (m : MetricData V ι) (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) (i j k : ι) :
    m.form (nabla (m.basis i) (m.basis j)) (m.basis k) =
      connectionCoefficient m nabla i j k := by
  rw [m.form_symm]
  exact MetricData.form_basis_apply m k _

/-- **Metric compatibility in coefficients**: `Γ^k_{ij} + Γ^j_{ik} = 0`. -/
theorem isMetricCompatible_coefficient_relation (m : MetricData V ι)
    {nabla : V →ₗ[ℝ] V →ₗ[ℝ] V} (h : IsMetricCompatible m nabla) (i j k : ι) :
    connectionCoefficient m nabla i j k + connectionCoefficient m nabla i k j = 0 := by
  have h1 : m.form (nabla (m.basis i) (m.basis j)) (m.basis k) =
      connectionCoefficient m nabla i j k := form_nabla_basis m nabla i j k
  have h2 : m.form (m.basis j) (nabla (m.basis i) (m.basis k)) =
      connectionCoefficient m nabla i k j := by
    rw [m.form_symm, form_nabla_basis]
  linarith [h (m.basis i) (m.basis j) (m.basis k)]

/-- **Torsion-freeness in coefficients**: `Γ^k_{ij} - Γ^k_{ji} = C^k_{ij}`. -/
theorem isTorsionFree_coefficient_relation (m : MetricData V ι) (b : LieBracketData ℝ V)
    {nabla : V →ₗ[ℝ] V →ₗ[ℝ] V} (h : IsTorsionFree b nabla) (i j k : ι) :
    connectionCoefficient m nabla i j k - connectionCoefficient m nabla j i k =
      bracketCoefficient m b i j k := by
  have h' := congrArg (fun v : V => m.basis.repr v k) (h (m.basis i) (m.basis j))
  simpa [connectionCoefficient, bracketCoefficient, map_sub] using h'

/-- **Coefficient functoriality under affine combinations.** -/
theorem connectionCoefficient_affine (m : MetricData V ι) (a : ℝ)
    (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) (i j k : ι) :
    connectionCoefficient m (affineConnection a nabla₁ nabla₂) i j k =
      a * connectionCoefficient m nabla₁ i j k +
        (1 - a) * connectionCoefficient m nabla₂ i j k := by
  simp only [connectionCoefficient, affineConnection_apply, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]

/-- **Coefficient functoriality under the mean connection.** -/
theorem connectionCoefficient_mean (m : MetricData V ι)
    (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) (i j k : ι) :
    connectionCoefficient m (meanConnection nabla₁ nabla₂) i j k =
      (1 / 2 : ℝ) *
        (connectionCoefficient m nabla₁ i j k + connectionCoefficient m nabla₂ i j k) := by
  rw [meanConnection_eq_affine, connectionCoefficient_affine]
  ring

/-- **Coefficient functoriality under the difference tensor.** -/
theorem connectionCoefficient_difference (m : MetricData V ι)
    (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) (i j k : ι) :
    connectionCoefficient m (differenceTensor nabla₁ nabla₂) i j k =
      connectionCoefficient m nabla₁ i j k - connectionCoefficient m nabla₂ i j k := by
  simp only [connectionCoefficient, differenceTensor_apply, map_sub, Finsupp.sub_apply]

/-- The metric-compatibility coefficient relation is preserved by affine combinations. -/
theorem isMetricCompatible_coefficient_relation_affine (m : MetricData V ι) (a : ℝ)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : ∀ i j k : ι,
      connectionCoefficient m nabla₁ i j k + connectionCoefficient m nabla₁ i k j = 0)
    (h₂ : ∀ i j k : ι,
      connectionCoefficient m nabla₂ i j k + connectionCoefficient m nabla₂ i k j = 0)
    (i j k : ι) :
    connectionCoefficient m (affineConnection a nabla₁ nabla₂) i j k +
      connectionCoefficient m (affineConnection a nabla₁ nabla₂) i k j = 0 := by
  rw [connectionCoefficient_affine, connectionCoefficient_affine]
  linear_combination a * h₁ i j k + (1 - a) * h₂ i j k

/-- The torsion-freeness coefficient relation is preserved by affine combinations. -/
theorem isTorsionFree_coefficient_relation_affine (m : MetricData V ι) (b : LieBracketData ℝ V)
    (a : ℝ) {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : ∀ i j k : ι,
      connectionCoefficient m nabla₁ i j k - connectionCoefficient m nabla₁ j i k =
        bracketCoefficient m b i j k)
    (h₂ : ∀ i j k : ι,
      connectionCoefficient m nabla₂ i j k - connectionCoefficient m nabla₂ j i k =
        bracketCoefficient m b i j k)
    (i j k : ι) :
    connectionCoefficient m (affineConnection a nabla₁ nabla₂) i j k -
      connectionCoefficient m (affineConnection a nabla₁ nabla₂) j i k =
        bracketCoefficient m b i j k := by
  rw [connectionCoefficient_affine, connectionCoefficient_affine]
  linear_combination a * h₁ i j k + (1 - a) * h₂ i j k

/-! ## Part 2: smooth coefficient fields

`P` is the model space of a chart; `nabla : P → V →L[ℝ] V →L[ℝ] V` is the local expression of a
point-dependent connection. `ℓ` is a continuous linear coefficient functional (in a chart, the
coordinate functionals are continuous linear functionals). -/

section Smoothness

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Coefficient field** of a point-dependent connection: the coefficient of `∇ x (e i) (e j)`
extracted by the continuous linear functional `ℓ`. -/
noncomputable def coefficientField (e : ι → V) (ℓ : V →L[ℝ] ℝ)
    (nabla : P → V →L[ℝ] V →L[ℝ] V) (i j : ι) (x : P) : ℝ :=
  ℓ (nabla x (e i) (e j))

/-- Constant scalar multiplication preserves `C^n` smoothness (realised as composition with the
continuous linear map `c • id`). -/
theorem contMDiff_const_smul_field {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {n : ℕ∞ω} {f : P → M} (hf : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, M) n f) (c : ℝ) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, M) n (fun x => c • f x) :=
  ((c • ContinuousLinearMap.id ℝ M).contMDiff).comp hf

/-- **Smoothness transfer.** If the connection field is `C^n`, then all its coefficients are
`C^n`. No chart hypothesis is needed for this direction: the coefficient functional is continuous
by construction. -/
theorem contMDiff_coefficientField {n : ℕ∞ω} {e : ι → V} {ℓ : V →L[ℝ] ℝ}
    {nabla : P → V →L[ℝ] V →L[ℝ] V}
    (h : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] V) n nabla) (i j : ι) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) n (coefficientField e ℓ nabla i j) := by
  have h1 : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V) n (fun x => nabla x (e i)) :=
    h.clm_apply contMDiff_const
  have h2 : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V) n (fun x => nabla x (e i) (e j)) :=
    h1.clm_apply contMDiff_const
  exact ℓ.contMDiff.comp h2

/-- **Chart-smoothness hypothesis.** If `φ : P' → P` is a `C^n` chart and the connection field is
`C^n`, then the coefficients pulled back along the chart are `C^n`. -/
theorem contMDiff_coefficientField_comp_chart {P' : Type*} [NormedAddCommGroup P']
    [NormedSpace ℝ P'] {n : ℕ∞ω} {e : ι → V} {ℓ : V →L[ℝ] ℝ}
    {nabla : P → V →L[ℝ] V →L[ℝ] V} {φ : P' → P}
    (hφ : ContMDiff 𝓘(ℝ, P') 𝓘(ℝ, P) n φ)
    (h : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] V) n nabla) (i j : ι) :
    ContMDiff 𝓘(ℝ, P') 𝓘(ℝ, ℝ) n (fun p => coefficientField e ℓ nabla i j (φ p)) :=
  (contMDiff_coefficientField (e := e) (ℓ := ℓ) h i j).comp hφ

/-- Pointwise affine combination of two connection fields. -/
noncomputable def affineField (a : ℝ) (nabla₁ nabla₂ : P → V →L[ℝ] V →L[ℝ] V) :
    P → V →L[ℝ] V →L[ℝ] V :=
  fun x => a • nabla₁ x + (1 - a) • nabla₂ x

/-- Defining equation of the pointwise affine combination. -/
theorem affineField_apply (a : ℝ) (nabla₁ nabla₂ : P → V →L[ℝ] V →L[ℝ] V) (x : P) :
    affineField a nabla₁ nabla₂ x = a • nabla₁ x + (1 - a) • nabla₂ x := rfl

/-- **Smoothness is closed under pointwise affine combinations.** -/
theorem contMDiff_affineField {n : ℕ∞ω} {nabla₁ nabla₂ : P → V →L[ℝ] V →L[ℝ] V}
    (h₁ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] V) n nabla₁)
    (h₂ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] V) n nabla₂) (a : ℝ) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] V) n (affineField a nabla₁ nabla₂) := by
  change ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] V) n
    (fun x => a • nabla₁ x + (1 - a) • nabla₂ x)
  exact (contMDiff_const_smul_field h₁ a).add (contMDiff_const_smul_field h₂ (1 - a))

/-- Coefficients of a pointwise affine combination are the affine combinations of the
coefficients. -/
theorem coefficientField_affineField {e : ι → V} {ℓ : V →L[ℝ] ℝ} (a : ℝ)
    (nabla₁ nabla₂ : P → V →L[ℝ] V →L[ℝ] V) (i j : ι) (x : P) :
    coefficientField e ℓ (affineField a nabla₁ nabla₂) i j x =
      a * coefficientField e ℓ nabla₁ i j x +
        (1 - a) * coefficientField e ℓ nabla₂ i j x := by
  simp only [coefficientField, affineField, add_apply, smul_apply, map_add, map_smul,
    smul_eq_mul]

end Smoothness

/-! ## The bundled smooth coefficient interface -/

/-- **Smooth connection-coefficient system.** The coefficient functions `Γ^k_{ij}` of a connection
on a chart with model space `P`, together with:

* `smooth`: the stated `C^n` chart-smoothness of every coefficient;
* `torsion_relation`: torsion-freeness against the bracket-coefficient field `β`;
* `metric_relation`: metric compatibility.

The bracket coefficient field `β` is part of the data: for an abstract (constant) bracket it is
`bracketCoefficient m b`, while on a manifold it is the bracket of the coordinate frame. -/
structure SmoothCoefficientSystem (P : Type u) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (m : MetricData V ι) (β : ι → ι → ι → P → ℝ) (n : ℕ∞ω) where
  /-- The coefficient functions `Γ^k_{ij}`. -/
  coeff : ι → ι → ι → P → ℝ
  /-- The stated chart-smoothness hypothesis: every coefficient is `C^n`. -/
  smooth : ∀ i j k : ι, ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) n (coeff i j k)
  /-- Torsion-freeness in coefficients: `Γ^k_{ij} - Γ^k_{ji} = β^k_{ij}`. -/
  torsion_relation : ∀ (i j k : ι) (x : P), coeff i j k x - coeff j i k x = β i j k x
  /-- Metric compatibility in coefficients: `Γ^k_{ij} + Γ^j_{ik} = 0`. -/
  metric_relation : ∀ (i j k : ι) (x : P), coeff i j k x + coeff i k j x = 0

namespace SmoothCoefficientSystem

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {m : MetricData V ι} {β : ι → ι → ι → P → ℝ} {n : ℕ∞ω}

/-- **Affine combination of smooth coefficient systems.** The coefficient functions are combined
pointwise, `a Γ₁ + (1 - a) Γ₂`; smoothness and both relations are preserved. This is the
coefficient-level form of task item 2a. -/
noncomputable def affineCombination (S₁ S₂ : SmoothCoefficientSystem P m β n) (a : ℝ) :
    SmoothCoefficientSystem P m β n where
  coeff i j k x := a * S₁.coeff i j k x + (1 - a) * S₂.coeff i j k x
  smooth i j k :=
    (contMDiff_const_smul_field (S₁.smooth i j k) a).add
      (contMDiff_const_smul_field (S₂.smooth i j k) (1 - a))
  torsion_relation i j k x := by
    have h₁ := S₁.torsion_relation i j k x
    have h₂ := S₂.torsion_relation i j k x
    linear_combination a * h₁ + (1 - a) * h₂
  metric_relation i j k x := by
    have h₁ := S₁.metric_relation i j k x
    have h₂ := S₂.metric_relation i j k x
    linear_combination a * h₁ + (1 - a) * h₂

/-- The **mean** of two smooth coefficient systems, the affine combination at `a = 1/2`. -/
noncomputable def mean (S₁ S₂ : SmoothCoefficientSystem P m β n) :
    SmoothCoefficientSystem P m β n :=
  affineCombination S₁ S₂ (1 / 2)

/-- **Pullback of a smooth coefficient system along a chart.** If `φ : P' → P` is `C^n`, the
pulled-back coefficients `p ↦ Γ^k_{ij} (φ p)` are again a smooth coefficient system. This is the
precise content of "the coefficient interface is smooth under a stated chart-smoothness
hypothesis". -/
def pullback {P' : Type*} [NormedAddCommGroup P'] [NormedSpace ℝ P'] (φ : P' → P)
    (hφ : ContMDiff 𝓘(ℝ, P') 𝓘(ℝ, P) n φ)
    (S : SmoothCoefficientSystem P m β n) :
    SmoothCoefficientSystem P' m (fun i j k p => β i j k (φ p)) n where
  coeff i j k p := S.coeff i j k (φ p)
  smooth i j k := (S.smooth i j k).comp hφ
  torsion_relation i j k p := S.torsion_relation i j k (φ p)
  metric_relation i j k p := S.metric_relation i j k (φ p)

/-- **Constant coefficient systems.** Every abstract connection `∇` with an abstract bracket `b`
gives a smooth coefficient system whose coefficients are the constant basis coefficients. The
`C^n` smoothness is `contMDiff_const` (constants are smooth for every `n`); the relations are
`isTorsionFree_coefficient_relation` and `isMetricCompatible_coefficient_relation`. This is the
non-vacuity witness for the interface. -/
noncomputable def const (m : MetricData V ι) (b : LieBracketData ℝ V)
    {nabla : V →ₗ[ℝ] V →ₗ[ℝ] V} (ht : IsTorsionFree b nabla)
    (hm : IsMetricCompatible m nabla) (n : ℕ∞ω) :
    SmoothCoefficientSystem P m (fun i j k _ => bracketCoefficient m b i j k) n where
  coeff i j k _ := connectionCoefficient m nabla i j k
  smooth i j k := contMDiff_const
  torsion_relation i j k x := isTorsionFree_coefficient_relation m b ht i j k
  metric_relation i j k x := isMetricCompatible_coefficient_relation m hm i j k

@[simp]
theorem const_coeff (m : MetricData V ι) (b : LieBracketData ℝ V)
    {nabla : V →ₗ[ℝ] V →ₗ[ℝ] V} (ht : IsTorsionFree b nabla)
    (hm : IsMetricCompatible m nabla) (n : ℕ∞ω) (i j k : ι) (x : P) :
    (const m b ht hm n).coeff i j k x = connectionCoefficient m nabla i j k := rfl

/-- The affine combination of coefficient systems evaluates pointwise to the affine combination
of the coefficient functions. -/
@[simp]
theorem affineCombination_coeff (S₁ S₂ : SmoothCoefficientSystem P m β n) (a : ℝ)
    (i j k : ι) (x : P) :
    (affineCombination S₁ S₂ a).coeff i j k x =
      a * S₁.coeff i j k x + (1 - a) * S₂.coeff i j k x := rfl

/-- The mean coefficient system evaluates pointwise to the mean of the coefficient functions. -/
theorem mean_coeff (S₁ S₂ : SmoothCoefficientSystem P m β n) (i j k : ι) (x : P) :
    (mean S₁ S₂).coeff i j k x =
      (1 / 2 : ℝ) * (S₁.coeff i j k x + S₂.coeff i j k x) := by
  rw [mean, affineCombination_coeff]
  ring

end SmoothCoefficientSystem

end LeviCivita
end D7
end Poincare
