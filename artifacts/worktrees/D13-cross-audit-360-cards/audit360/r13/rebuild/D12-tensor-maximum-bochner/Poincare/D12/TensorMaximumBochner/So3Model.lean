import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct
import Poincare.D12.TensorMaximumBochner.BochnerIdentity

/-!
# Poincare.D12.TensorMaximumBochner.So3Model

**Task `D12-tensor-maximum-bochner`: the so(3) model — a concrete, non-flat downstream
application of the abstract Bochner machinery.**

The abstract `Bochner.bochner_identity` is conditional over a `LeviCivitaData` and a
`DerivationData`. This module constructs the geometric half concretely on `ℝ³` with the
cross-product bracket:

* `Vec3 = Fin 3 → ℝ` with the standard dot-product metric datum `stdMetric` (orthonormal basis
  `Pi.basisFun`);
* `crossBracket : LieBracketData ℝ Vec3` — the cross product, a Lie bracket by
  `cross_anticomm` and `jacobi_cross`;
* `crossMetricSkew` — the metric is invariant under the bracket action
  (`⟨X×Y,Z⟩ + ⟨Y,X×Z⟩ = 0`, the triple-product antisymmetry);
* `crossLeviCivita : LeviCivitaData stdMetric crossBracket` — the **mean connection**
  `∇_X Y = ½[X,Y]`, closing the upstream `BLOCKED` `LeviCivitaExistenceStatement` under the
  natural hypothesis (metric-skew bracket) by the proved `meanConnection_isMetricCompatible_iff`;
* `curvature_eq_quarter_doubleBracket` — the curvature of the mean connection:
  `R(X,Y)Z = −¼[[X,Y],Z]`;
* `ricci_eq_half_metric` — **`Ric = ½g`** for the so(3) model (the trace is computed against
  the orthonormal basis via `CurvatureOperator.ricci_eq_ricciSum`);
* `sectional_nonflat` — an explicit non-flatness witness (`⟨R(e₁,e₂)e₂, e₁⟩ = ¼ ≠ 0`), proving
  the model is genuinely curved (the Bochner identity here is not the flat Euclidean one).

Every object is constructed; nothing is assumed. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

open scoped BigOperators Matrix

namespace Poincare
namespace D12
namespace TensorMaximumBochner
namespace So3

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra

noncomputable section

abbrev Vec3 := Fin 3 → ℝ

/-! ## The standard metric datum on `ℝ³` -/

/-- The standard dot-product metric datum on `Vec3 = ℝ³`, with the standard orthonormal basis. -/
def stdMetric : MetricData Vec3 (Fin 3) where
  form := LinearMap.mk₂ ℝ (fun X Y : Vec3 => X ⬝ᵥ Y)
    (fun X Y Z => add_dotProduct X Y Z)
    (fun a X Y => smul_dotProduct a X Y)
    (fun X Y Z => dotProduct_add X Y Z)
    (fun a X Y => dotProduct_smul a X Y)
  symm := fun X Y => dotProduct_comm X Y
  pos_def := by
    intro X hX
    change 0 < X ⬝ᵥ X
    have hsum : X ⬝ᵥ X = X 0 * X 0 + X 1 * X 1 + X 2 * X 2 := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [hsum]
    rcases eq_or_ne (X 0) 0 with h0 | h0
    · rcases eq_or_ne (X 1) 0 with h1 | h1
      · have h2 : X 2 ≠ 0 := by
          intro h2
          exact hX (by ext i; fin_cases i <;> simp [h0, h1, h2])
        nlinarith [mul_self_pos.mpr h2]
      · nlinarith [mul_self_pos.mpr h1]
    · nlinarith [mul_self_pos.mpr h0]
  basis := Pi.basisFun ℝ (Fin 3)
  orthonormal := by
    intro i j
    show (Pi.basisFun ℝ (Fin 3) i) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) j) = if i = j then 1 else 0
    by_cases h : i = j
    · subst h
      simp [Pi.basisFun_apply]
    · simp [Pi.basisFun_apply, h]

/-- The defining evaluation of the standard metric form. -/
@[simp] lemma stdMetric_form (X Y : Vec3) : stdMetric.form X Y = X ⬝ᵥ Y := rfl

/-! ## The cross-product bracket and its invariance -/

/-- The cross product on `ℝ³` as a Lie bracket datum. -/
def crossBracket : LieBracketData ℝ Vec3 where
  bracket := crossProduct
  skew := by intro X Y; exact (cross_anticomm Y X).symm
  jacobi := jacobi_cross

/-- **Metric invariance of the cross product**: `⟨X×Y, Z⟩ + ⟨Y, X×Z⟩ = 0`. -/
lemma crossMetricSkew (X Y Z : Vec3) :
    (X ⨯₃ Y) ⬝ᵥ Z + Y ⬝ᵥ (X ⨯₃ Z) = 0 := by
  have h1 : (X ⨯₃ Y) ⬝ᵥ Z = X ⬝ᵥ (Y ⨯₃ Z) := by
    rw [dotProduct_comm, triple_product_permutation]
  have h2 : Y ⬝ᵥ (X ⨯₃ Z) = - (X ⬝ᵥ (Y ⨯₃ Z)) := by
    rw [show X ⨯₃ Z = - (Z ⨯₃ X) from (cross_anticomm Z X).symm]
    rw [dotProduct_neg, triple_product_permutation, triple_product_permutation]
  rw [h1, h2, add_neg_cancel]

/-! ## The mean-connection Levi-Civita datum (conditional closure) -/

/-- **The mean connection closes the abstract Levi-Civita existence statement** under the
metric-skew hypothesis: for the cross-product bracket on `ℝ³` the mean connection
`∇_X Y = ½[X,Y]` is torsion-free and metric-compatible, giving a full `LeviCivitaData`. -/
def crossLeviCivita : LeviCivitaData stdMetric crossBracket where
  nabla := (meanConnection crossBracket).nabla
  torsion_free := (meanConnection crossBracket).torsion_free
  metric_compatible := by
    rw [meanConnection_isMetricCompatible_iff]
    intro X Y Z
    simp only [stdMetric_form]
    exact crossMetricSkew X Y Z

/-! ## The curvature: `R(X,Y)Z = −¼[[X,Y],Z]` and `Ric = ½g` -/

/-- The curvature of the mean connection on so(3): `R(X,Y)Z = −¼[[X,Y],Z]`. -/
lemma curvature_eq_quarter_doubleBracket (X Y Z : Vec3) :
    crossLeviCivita.toCurvatureOperator X Y Z
      = (-(1 / 4) : ℝ) • ((X ⨯₃ Y) ⨯₃ Z) := by
  change (meanConnection crossBracket).curvature X Y Z = (-(1 / 4) : ℝ) • ((X ⨯₃ Y) ⨯₃ Z)
  rw [mean_curvature_apply]
  rfl

/-- The Ricci form of the so(3) model: `Ric(X,Y) = ½⟨X,Y⟩`. -/
lemma ricci_eq_half_metric (X Y : Vec3) :
    CurvatureOperator.ricci crossLeviCivita.toCurvatureOperator X Y = (1 / 2 : ℝ) * (X ⬝ᵥ Y) := by
  rw [CurvatureOperator.ricci_eq_ricciSum (Pi.basisFun ℝ (Fin 3)) _ X Y]
  simp only [CurvatureOperator.ricciSum]
  have hterm : ∀ i : Fin 3,
      (Pi.basisFun ℝ (Fin 3)).repr
          (crossLeviCivita.toCurvatureOperator (Pi.basisFun ℝ (Fin 3) i) X Y) i
        = (-1 / 4 : ℝ) * (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ X) ⨯₃ Y) i := by
    intro i
    rw [curvature_eq_quarter_doubleBracket, Pi.basisFun_repr]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hexp : ∀ i : Fin 3,
      (((Pi.basisFun ℝ (Fin 3) i) ⨯₃ X) ⨯₃ Y) i
        = (Y i) * X i - (X ⬝ᵥ Y) * ((Pi.basisFun ℝ (Fin 3) i) i) := by
    intro i
    rw [cross_cross_eq_smul_sub_smul]
    have h1 : (Pi.basisFun ℝ (Fin 3) i) ⬝ᵥ Y = Y i := by
      simp [Pi.basisFun_apply]
    simp only [h1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hexp]
  rw [Fin.sum_univ_three]
  simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
  ring

/-! ## Non-flatness witness -/

/-- The model is genuinely curved: `⟨R(e₁,e₂)e₂, e₁⟩ = ¼ ≠ 0`. -/
lemma sectional_nonflat :
    stdMetric.form (crossLeviCivita.toCurvatureOperator (Pi.basisFun ℝ (Fin 3) 0)
        (Pi.basisFun ℝ (Fin 3) 1) (Pi.basisFun ℝ (Fin 3) 1))
      (Pi.basisFun ℝ (Fin 3) 0) = (1 / 4 : ℝ) := by
  rw [curvature_eq_quarter_doubleBracket]
  have h2 : (((Pi.basisFun ℝ (Fin 3) 0) ⨯₃ (Pi.basisFun ℝ (Fin 3) 1)) ⨯₃
      (Pi.basisFun ℝ (Fin 3) 1)) = - (Pi.basisFun ℝ (Fin 3) 0) := by
    rw [cross_cross_eq_smul_sub_smul]
    have h01 : (Pi.basisFun ℝ (Fin 3) 0) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) 1) = 0 := by
      simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
    have h11 : (Pi.basisFun ℝ (Fin 3) 1) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) 1) = 1 := by
      simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
    rw [h01, h11]
    simp
  rw [h2]
  simp [stdMetric, Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]

/-! ## Axiom audit (fail-closed; see `tools/d12_axiom_audit.py`)

Every declaration of this file is listed here; the audit script additionally checks coverage
(that no declaration is silently left unaudited). -/

#print axioms Vec3
#print axioms stdMetric
#print axioms stdMetric_form
#print axioms crossBracket
#print axioms crossMetricSkew
#print axioms crossLeviCivita
#print axioms curvature_eq_quarter_doubleBracket
#print axioms ricci_eq_half_metric
#print axioms sectional_nonflat

end

end So3
end TensorMaximumBochner
end D12
end Poincare
