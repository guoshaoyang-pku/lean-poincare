import Poincare.D12.ConnectionCurvature.ChartLeviCivita
import Poincare.D12.ConnectionCurvature.RicciSymmetry

/-!
# Poincare.D12.ConnectionCurvature.ChartLeviCivitaForm

**D12-connection-curvature: the chart connection on vector coefficients and its
metric compatibility, bridged to the D7/Stage1 tensor interface.**

From the chart coefficient datum (`ChartMetricCoefficients`) this module builds, at the
chart point, the actual bilinear operators on `V = ι → ℝ` (vector coefficients in the
coordinate frame):

* `formOf c` — the metric pairing `g(X,Y) = Σᵢⱼ G_{ij} XⁱYʲ`;
* `nablaOf c` — the Christoffel connection on constant-coefficient vectors
  `(∇_X Y)ᵏ = Σᵢⱼ Γᵏᵢⱼ XⁱYʲ`;
* `dFormOf c` — the metric-derivative trilinear datum `d(X,Y,Z) = Σᵢⱼₖ d_{i j k} XⁱYʲZᵏ`.

The main theorem `chartMetricCompatible_form` proves, for **all** coefficient vectors
`X Y Z` (not just the frame):

`formOf c (nablaOf c X Y) Z + formOf c Y (nablaOf c X Z) = dFormOf c X Y Z`,

i.e. `∂ₓg(Y,Z) = g(∇ₓY,Z) + g(Y,∇ₓZ)` — metric compatibility of the Christoffel
connection against the metric-derivative datum. The proof reduces to the coefficient
identity `metricDerivative_christoffel'` by expansion of the three double sums (the
algebraic content is exactly `A_{jkl} + A_{lkj} = d_{klj}`).

`chartTorsionFree_form` proves the coordinate-frame torsion-freeness
`nablaOf c X Y − nablaOf c Y X = 0` (the coordinate Lie bracket of constant-coefficient
fields vanishes), reducing to `christoffel_symm`.

Finally `chartAbstractConnection` packages the connection with the **zero** coordinate
bracket into the existing `AbstractConnection` structure, whose adapter
`toCurvatureOperator` produces the D7/Stage1 `CurvatureOperator` with the *checked*
identities (first-pair skew-symmetry, first Bianchi) — this is the bridge from the
nonconstant chart metric to the D7 tensor data, with theorem provenance.

## Honest boundary

`nablaOf` acts on *constant-coefficient* vector fields (the Christoffel part); the full
smooth field-level connection `(∇ₓY)(x) = dY(x)X(x) + Γ(x)(X(x),Y(x))` and the
x-dependent smoothness statements are in `ChartLeviCivitaSmooth`. The compatibility
theorem here is the algebraic core those proofs reduce to. No `sorry`, `axiom`,
`unsafe`, `native_decide` or `proof_wanted` appears in this file.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace ConnectionCurvature

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra

universe w

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Sum-reordering helpers -/

/-- Reorder a three-fold sum `ΣₐΣ_bΣ_c` into `Σ_cΣ_aΣ_b`. -/
lemma sum_three_reorder {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) = ∑ c : γ, ∑ a : α, ∑ b : β, f a b c := by
  classical
  calc
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) = ∑ a : α, ∑ c : γ, ∑ b : β, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ b : β, f a b c := by
      exact Finset.sum_comm

/-- Reorder a four-fold sum `ΣₐΣ_bΣ_cΣ_d` into `Σ_cΣ_dΣ_bΣ_a`. -/
lemma sum_four_reorder {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d) =
      ∑ c : γ, ∑ d : δ, ∑ b : β, ∑ a : α, f a b c d := by
  classical
  calc
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d)
        = ∑ a : α, ∑ c : γ, ∑ b : β, ∑ d : δ, f a b c d := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ b : β, ∑ d : δ, f a b c d := by
          exact Finset.sum_comm
    _ = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d := by
          apply Finset.sum_congr rfl
          intro c hc
          exact sum_three_reorder (fun a b d => f a b c d)
    _ = ∑ c : γ, ∑ d : δ, ∑ b : β, ∑ a : α, f a b c d := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_comm

/-! ## The operators on vector coefficients -/

variable (c : ChartMetricCoefficients ι)

/-- The metric pairing on vector coefficients: `g(X,Y) = Σᵢⱼ G_{ij} XⁱYʲ`. -/
noncomputable def formOf : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun X := {
    toFun Y := ∑ i : ι, ∑ j : ι, c.g i j * X i * Y j
    map_add' Y₁ Y₂ := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' a Y := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change c.g i j * X i * (a * Y j) = a * (c.g i j * X i * Y j)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    change (∑ i : ι, ∑ j : ι, c.g i j * (X₁ i + X₂ i) * Y j) =
      (∑ i : ι, ∑ j : ι, c.g i j * X₁ i * Y j) + (∑ i : ι, ∑ j : ι, c.g i j * X₂ i * Y j)
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ i : ι, ∑ j : ι, c.g i j * (a * X i) * Y j) =
      a * (∑ i : ι, ∑ j : ι, c.g i j * X i * Y j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change c.g i j * (a * X i) * Y j = a * (c.g i j * X i * Y j)
    ring

@[simp]
theorem formOf_apply (X Y : ι → ℝ) :
    formOf c X Y = ∑ i : ι, ∑ j : ι, c.g i j * X i * Y j := rfl

/-- The Christoffel connection on constant-coefficient vectors:
`(∇_X Y)ᵏ = Σᵢⱼ Γᵏᵢⱼ XⁱYʲ`. -/
noncomputable def nablaOf : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun X := {
    toFun Y := fun k : ι => ∑ i : ι, ∑ j : ι, c.christoffel k i j * X i * Y j
    map_add' Y₁ Y₂ := by
      ext k
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' a Y := by
      ext k
      change (∑ i : ι, ∑ j : ι, c.christoffel k i j * X i * (a * Y j)) =
        a * (∑ i : ι, ∑ j : ι, c.christoffel k i j * X i * Y j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change c.christoffel k i j * X i * (a * Y j) = a * (c.christoffel k i j * X i * Y j)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    ext k
    change (∑ i : ι, ∑ j : ι, c.christoffel k i j * (X₁ i + X₂ i) * Y j) =
      (∑ i : ι, ∑ j : ι, c.christoffel k i j * X₁ i * Y j) +
        (∑ i : ι, ∑ j : ι, c.christoffel k i j * X₂ i * Y j)
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    ext k
    change (∑ i : ι, ∑ j : ι, c.christoffel k i j * (a * X i) * Y j) =
      a * (∑ i : ι, ∑ j : ι, c.christoffel k i j * X i * Y j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change c.christoffel k i j * (a * X i) * Y j = a * (c.christoffel k i j * X i * Y j)
    ring

@[simp]
theorem nablaOf_apply (X Y : ι → ℝ) (k : ι) :
    nablaOf c X Y k = ∑ i : ι, ∑ j : ι, c.christoffel k i j * X i * Y j := rfl

/-- The metric-derivative trilinear datum on vector coefficients:
`d(X,Y,Z) = Σᵢⱼₖ d_{i j k} XⁱYʲZᵏ`. -/
noncomputable def dFormOf (X Y Z : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, ∑ k : ι, c.d i j k * X i * Y j * Z k

/-! ## Metric compatibility and torsion-freeness at the form level -/

/-- The metric pairing of the connection action on the first slot:
`g(∇_X Y, Z) = Σₖₗⱼ A_{jkl} XᵏYˡZʲ`. -/
theorem form_nabla_eq_sum (X Y Z : ι → ℝ) :
    formOf c (nablaOf c X Y) Z =
      ∑ k : ι, ∑ l : ι, ∑ j : ι, c.christoffelLower j k l * (X k * Y l * Z j) := by
  classical
  calc
    formOf c (nablaOf c X Y) Z
        = ∑ i : ι, ∑ j : ι, c.g i j * (∑ k : ι, ∑ l : ι,
            c.christoffel i k l * X k * Y l) * Z j := by
          simp [formOf_apply, nablaOf_apply]
    _ = ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
            (c.g i j * (c.christoffel i k l * X k * Y l)) * Z j := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ k : ι, ∑ l : ι, ∑ j : ι, ∑ i : ι,
            (c.g i j * (c.christoffel i k l * X k * Y l)) * Z j := by
          exact sum_four_reorder (fun i j k l =>
            (c.g i j * (c.christoffel i k l * X k * Y l)) * Z j)
    _ = ∑ k : ι, ∑ l : ι, ∑ j : ι,
            (∑ i : ι, c.g i j * c.christoffel i k l) * (X k * Y l * Z j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ k : ι, ∑ l : ι, ∑ j : ι, c.christoffelLower j k l * (X k * Y l * Z j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro j hj
          rw [c.christoffel_raised_contraction j k l]

/-- The metric pairing of the connection action on the second slot:
`g(Y, ∇_X Z) = Σₖₗᵢ A_{ikl} YⁱXᵏZˡ`. -/
theorem form_nabla_second_eq_sum (X Y Z : ι → ℝ) :
    formOf c Y (nablaOf c X Z) =
      ∑ k : ι, ∑ l : ι, ∑ i : ι, c.christoffelLower i k l * (Y i * (X k * Z l)) := by
  classical
  calc
    formOf c Y (nablaOf c X Z)
        = ∑ i : ι, ∑ j : ι, c.g i j * Y i * (∑ k : ι, ∑ l : ι,
            c.christoffel j k l * X k * Z l) := by
          simp [formOf_apply, nablaOf_apply]
    _ = ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
            (c.g i j * Y i) * (c.christoffel j k l * X k * Z l) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ k : ι, ∑ l : ι, ∑ j : ι, ∑ i : ι,
            (c.g i j * Y i) * (c.christoffel j k l * X k * Z l) := by
          exact sum_four_reorder (fun i j k l =>
            (c.g i j * Y i) * (c.christoffel j k l * X k * Z l))
    _ = ∑ k : ι, ∑ l : ι, ∑ i : ι, ∑ j : ι,
            (c.g i j * Y i) * (c.christoffel j k l * X k * Z l) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          exact Finset.sum_comm
    _ = ∑ k : ι, ∑ l : ι, ∑ i : ι,
            (∑ j : ι, c.g i j * c.christoffel j k l) * (Y i * (X k * Z l)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ k : ι, ∑ l : ι, ∑ i : ι, c.christoffelLower i k l * (Y i * (X k * Z l)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro i hi
          rw [show (∑ j : ι, c.g i j * c.christoffel j k l) =
              ∑ j : ι, c.g j i * c.christoffel j k l from
            Finset.sum_congr rfl (by intro j hj; rw [c.g_symm i j])]
          rw [c.christoffel_raised_contraction i k l]

/-- **Metric compatibility at the form level (all coefficient vectors).**
`∂ₓg(Y,Z) = g(∇ₓY,Z) + g(Y,∇ₓZ)` — the classical Koszul compatibility of the
Christoffel connection, proved from the coefficient identity
`A_{jkl} + A_{lkj} = d_{klj}`. -/
theorem chartMetricCompatible_form (X Y Z : ι → ℝ) :
    formOf c (nablaOf c X Y) Z + formOf c Y (nablaOf c X Z) = dFormOf c X Y Z := by
  classical
  rw [form_nabla_eq_sum c X Y Z, form_nabla_second_eq_sum c X Y Z]
  have hT1re : (∑ k : ι, ∑ l : ι, ∑ j : ι, c.christoffelLower j k l * (X k * Y l * Z j))
      = ∑ k : ι, ∑ i : ι, ∑ l : ι, c.christoffelLower l k i * (X k * Y i * Z l) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
  rw [hT1re]
  rw [show (∑ k : ι, ∑ l : ι, ∑ i : ι, c.christoffelLower i k l * (Y i * (X k * Z l)))
      = ∑ k : ι, ∑ i : ι, ∑ l : ι, c.christoffelLower i k l * (Y i * (X k * Z l)) from by
    apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  rw [dFormOf]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← c.christoffel_raised_contraction l k i, ← c.christoffel_raised_contraction_first i k l,
    c.metricDerivative_christoffel' k i l]
  ring

/-- **Coordinate-frame torsion-freeness.** `∇_X Y − ∇_Y X = 0` for constant-coefficient
vectors (the coordinate Lie bracket vanishes), from `christoffel_symm`. -/
theorem chartTorsionFree_form (X Y : ι → ℝ) :
    nablaOf c X Y - nablaOf c Y X = 0 := by
  classical
  ext k
  simp only [Pi.sub_apply, nablaOf_apply]
  have hswap : (∑ i : ι, ∑ j : ι, c.christoffel k i j * Y i * X j) =
      ∑ i : ι, ∑ j : ι, c.christoffel k i j * X i * Y j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [c.christoffel_symm k j i]
    ring
  rw [hswap, sub_self]
  rfl

/-! ## Bridge to the D7/Stage1 tensor interface -/

/-- The chart Christoffel connection packaged as an `AbstractConnection` with the
**zero** coordinate bracket (constant-coefficient vector fields commute). Its adapter
`toCurvatureOperator` produces the D7/Stage1 `CurvatureOperator` with the *checked*
identities: first-pair skew-symmetry and first Bianchi (proved for any abstract
connection in `Poincare.Longrun.Geometry.ConnectionAdapter`, not assumed here). -/
noncomputable def chartAbstractConnection : AbstractConnection ℝ (ι → ℝ) where
  nabla := nablaOf c
  lie := LieBracketData.zero
  torsion_free := by
    intro X Y
    simpa [LieBracketData.zero] using chartTorsionFree_form c X Y

/-- **The D7/Stage1 curvature operator of the chart Christoffel connection.** This is
the bridge from the nonconstant chart metric coefficients to the D7 tensor data: the
curvature `R(X,Y)Z` of the connection constructed from `(g, g⁻¹, d)`, packaged as a
`CurvatureOperator` (with its two interface identities checked by construction). -/
noncomputable def chartCurvatureOperator : CurvatureOperator ℝ (ι → ℝ) :=
  (chartAbstractConnection c).toCurvatureOperator

/-- The chart curvature evaluates as `R(X,Y)Z = ∇ₓ∇ᵧZ − ∇ᵧ∇ₓZ` (the coordinate bracket
term vanishes). -/
theorem chartCurvatureOperator_apply (X Y Z : ι → ℝ) :
    chartCurvatureOperator c X Y Z =
      nablaOf c X (nablaOf c Y Z) - nablaOf c Y (nablaOf c X Z) := by
  rw [chartCurvatureOperator, AbstractConnection.toCurvatureOperator_apply,
    AbstractConnection.curvature_apply]
  simp [chartAbstractConnection, LieBracketData.zero]

end ConnectionCurvature
end D12
end Poincare
