import Poincare.D7.RicciScalar.Scalar
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Poincare.D7.RicciScalar.Product

**D7 Ricci/scalar layer, part 3: the Riemannian product structure and scalar additivity.**

For two metric-compatible torsion-free connection data `D₁` on `V₁` and `D₂` on `V₂`, this file
constructs the **product datum** `prodData D₁ D₂` on `V₁ × V₂`:

* the product bracket `[(X₁,X₂),(Y₁,Y₂)] = ([X₁,Y₁],[X₂,Y₂])` (`prodBracket`);
* the product connection `∇_{(X₁,X₂)}(Y₁,Y₂) = (∇¹_{X₁}Y₁, ∇²_{X₂}Y₂)` (`prodConn`), which is
  torsion-free because both factors are, and metric-compatible for the product metric because
  both factors are;
* the product metric `g₁ ⊕ g₂`, whose orthonormal basis is the direct-sum basis
  `Basis.prod` indexed by `ι₁ ⊕ ι₂` (`prodMetric`).

The main theorem is the classical product formula

`prodData_scalarCurvature : scal (D₁ × D₂) = scal D₁ + scal D₂`,

proved by splitting the curvature, the Ricci contraction and finally the orthonormal-basis
trace over the direct-sum index. The Ricci splitting `prodData_ricciForm` uses the mathlib trace
formula `LinearMap.trace_prodMap'` for `prodMap` endomorphisms.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Poincare
namespace D7
namespace RicciScalar

universe v₁ v₂ w₁ w₂

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V₁ : Type v₁} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
variable {V₂ : Type v₂} [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
variable {ι₁ : Type w₁} [Fintype ι₁] [DecidableEq ι₁]
variable {ι₂ : Type w₂} [Fintype ι₂] [DecidableEq ι₂]

/-! ## The product bracket and connection -/

/-- **The product bracket** `[(X₁,X₂),(Y₁,Y₂)] = ([X₁,Y₁],[X₂,Y₂])`. The Lie-algebra axioms
hold componentwise. -/
noncomputable def prodBracket (b₁ : LieBracketData ℝ V₁) (b₂ : LieBracketData ℝ V₂) :
    LieBracketData ℝ (V₁ × V₂) where
  bracket :=
    { toFun := fun X =>
        { toFun := fun Y => (b₁.bracket X.1 Y.1, b₂.bracket X.2 Y.2)
          map_add' := fun Y Z => by
            apply Prod.ext <;> simp
          map_smul' := fun a Y => by
            apply Prod.ext <;> simp }
      map_add' := fun X Z => by
        apply LinearMap.ext; intro Y
        apply Prod.ext <;> simp
      map_smul' := fun a X => by
        apply LinearMap.ext; intro Y
        apply Prod.ext <;> simp }
  skew := fun X Y => by
    apply Prod.ext
    · exact b₁.skew X.1 Y.1
    · exact b₂.skew X.2 Y.2
  jacobi := fun X Y Z => by
    apply Prod.ext
    · exact b₁.jacobi X.1 Y.1 Z.1
    · exact b₂.jacobi X.2 Y.2 Z.2

/-- Defining equation of the product bracket. -/
@[simp] theorem prodBracket_bracket (b₁ : LieBracketData ℝ V₁) (b₂ : LieBracketData ℝ V₂)
    (X Y : V₁ × V₂) :
    (prodBracket b₁ b₂).bracket X Y = (b₁.bracket X.1 Y.1, b₂.bracket X.2 Y.2) :=
  rfl

/-- **The product connection** `∇_{(X₁,X₂)}(Y₁,Y₂) = (∇¹_{X₁}Y₁, ∇²_{X₂}Y₂)`. -/
noncomputable def prodConn (c₁ : AbstractConnection ℝ V₁) (c₂ : AbstractConnection ℝ V₂) :
    AbstractConnection ℝ (V₁ × V₂) where
  nabla :=
    { toFun := fun X =>
        { toFun := fun Y => (c₁.nabla X.1 Y.1, c₂.nabla X.2 Y.2)
          map_add' := fun Y Z => by
            apply Prod.ext <;> simp
          map_smul' := fun a Y => by
            apply Prod.ext <;> simp }
      map_add' := fun X Z => by
        apply LinearMap.ext; intro Y
        apply Prod.ext <;> simp
      map_smul' := fun a X => by
        apply LinearMap.ext; intro Y
        apply Prod.ext <;> simp }
  lie := prodBracket c₁.lie c₂.lie
  torsion_free := fun X Y => by
    apply Prod.ext <;> simp [c₁.torsion_free, c₂.torsion_free]

/-- Defining equation of the product connection. -/
@[simp] theorem prodConn_nabla (c₁ : AbstractConnection ℝ V₁) (c₂ : AbstractConnection ℝ V₂)
    (X Y : V₁ × V₂) :
    (prodConn c₁ c₂).nabla X Y = (c₁.nabla X.1 Y.1, c₂.nabla X.2 Y.2) :=
  rfl

/-- The bracket of the product connection is the product bracket. -/
@[simp] theorem prodConn_lie (c₁ : AbstractConnection ℝ V₁) (c₂ : AbstractConnection ℝ V₂) :
    (prodConn c₁ c₂).lie = prodBracket c₁.lie c₂.lie :=
  rfl

/-! ## The product metric -/

/-- **The product bilinear form** `(g₁ ⊕ g₂)((X₁,X₂),(Y₁,Y₂)) = g₁(X₁,Y₁) + g₂(X₂,Y₂)`. -/
noncomputable def prodForm (m₁ : MetricData V₁ ι₁) (m₂ : MetricData V₂ ι₂) :
    (V₁ × V₂) →ₗ[ℝ] (V₁ × V₂) →ₗ[ℝ] ℝ :=
  m₁.form.compl₁₂ (LinearMap.fst ℝ V₁ V₂) (LinearMap.fst ℝ V₁ V₂) +
  m₂.form.compl₁₂ (LinearMap.snd ℝ V₁ V₂) (LinearMap.snd ℝ V₁ V₂)

/-- Defining equation of the product bilinear form. -/
@[simp] theorem prodForm_apply (m₁ : MetricData V₁ ι₁) (m₂ : MetricData V₂ ι₂)
    (X Y : V₁ × V₂) :
    prodForm m₁ m₂ X Y = m₁.form X.1 Y.1 + m₂.form X.2 Y.2 := by
  simp [prodForm, LinearMap.compl₁₂_apply]

/-- **The product metric datum** `g₁ ⊕ g₂` with the direct-sum orthonormal basis
`Basis.prod` indexed by `ι₁ ⊕ ι₂`. -/
noncomputable def prodMetric (m₁ : MetricData V₁ ι₁) (m₂ : MetricData V₂ ι₂) :
    MetricData (V₁ × V₂) (ι₁ ⊕ ι₂) where
  form := prodForm m₁ m₂
  symm := fun X Y => by
    rw [prodForm_apply, prodForm_apply, m₁.symm, m₂.symm]
  pos_def := by
    intro X hX
    rw [prodForm_apply]
    rcases X with ⟨x₁, x₂⟩
    by_cases h₁ : x₁ = 0
    · have h₂ : x₂ ≠ 0 := by
        intro h; exact hX (by simp [h₁, h])
      have hpos : 0 < m₂.form x₂ x₂ := m₂.pos_def x₂ h₂
      have hnonneg : 0 ≤ m₁.form x₁ x₁ := m₁.form_self_nonneg x₁
      rw [h₁] at hnonneg ⊢
      simpa using add_pos_of_nonneg_of_pos hnonneg hpos
    · have hpos : 0 < m₁.form x₁ x₁ := m₁.pos_def x₁ h₁
      have hnonneg : 0 ≤ m₂.form x₂ x₂ := m₂.form_self_nonneg x₂
      exact add_pos_of_pos_of_nonneg hpos hnonneg
  basis := m₁.basis.prod m₂.basis
  orthonormal := by
    intro p q
    rcases p with i | i <;> rcases q with j | j <;>
      simp [Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
        Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
        m₁.orthonormal, m₂.orthonormal]

/-! ## The product curvature data -/

/-- **The product metric-compatible torsion-free connection datum.** -/
noncomputable def prodData (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) :
    RiemannCurvatureData (V₁ × V₂) (ι₁ ⊕ ι₂) where
  conn := prodConn D₁.conn D₂.conn
  metric := prodMetric D₁.metric D₂.metric
  compatible := by
    intro X Y Z
    change prodForm D₁.metric D₂.metric
        (D₁.conn.nabla X.1 Y.1, D₂.conn.nabla X.2 Y.2) Z +
      prodForm D₁.metric D₂.metric Y
        (D₁.conn.nabla X.1 Z.1, D₂.conn.nabla X.2 Z.2) = 0
    rw [prodForm_apply, prodForm_apply]
    have h1 := D₁.compatible X.1 Y.1 Z.1
    have h2 := D₂.compatible X.2 Y.2 Z.2
    linarith

/-- The product datum's metric form is the sum of the factor forms. -/
@[simp] theorem prodData_form_apply (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (X Y : V₁ × V₂) :
    (prodData D₁ D₂).metric.form X Y = D₁.metric.form X.1 Y.1 + D₂.metric.form X.2 Y.2 :=
  prodForm_apply D₁.metric D₂.metric X Y

/-- The product datum's connection is the product connection. -/
@[simp] theorem prodData_nabla (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (X Y : V₁ × V₂) :
    (prodData D₁ D₂).conn.nabla X Y = (D₁.conn.nabla X.1 Y.1, D₂.conn.nabla X.2 Y.2) :=
  rfl

/-- **The curvature of the product connection splits componentwise**:
`R((X₁,X₂),(Y₁,Y₂))(Z₁,Z₂) = (R₁(X₁,Y₁)Z₁, R₂(X₂,Y₂)Z₂)`. -/
theorem prodConn_curvature_apply (c₁ : AbstractConnection ℝ V₁) (c₂ : AbstractConnection ℝ V₂)
    (X Y Z : V₁ × V₂) :
    (prodConn c₁ c₂).curvature X Y Z =
      (c₁.curvature X.1 Y.1 Z.1, c₂.curvature X.2 Y.2 Z.2) := by
  apply Prod.ext <;>
    simp [AbstractConnection.curvature_apply, prodConn_nabla, prodBracket_bracket]

/-- The curvature of the product datum splits componentwise. -/
theorem prodData_curvature_apply (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (X Y Z : V₁ × V₂) :
    (prodData D₁ D₂).curvature X Y Z =
      (D₁.curvature X.1 Y.1 Z.1, D₂.curvature X.2 Y.2 Z.2) :=
  prodConn_curvature_apply D₁.conn D₂.conn X Y Z

/-- **The metric-lowered curvature of the product splits as a sum**:
`⟨R((X₁,X₂),(Y₁,Y₂))(Z₁,Z₂),(W₁,W₂)⟩ = R₁(X₁,Y₁,Z₁,W₁) + R₂(X₂,Y₂,Z₂,W₂)`. -/
theorem prodData_curvatureForm_apply (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (X Y Z W : V₁ × V₂) :
    (prodData D₁ D₂).curvatureForm X Y Z W =
      D₁.curvatureForm X.1 Y.1 Z.1 W.1 + D₂.curvatureForm X.2 Y.2 Z.2 W.2 := by
  rw [RiemannCurvatureData.curvatureForm_apply, prodData_curvature_apply, prodData_form_apply]
  rfl

/-! ## Ricci and scalar curvature of the product -/

/-- The product datum's basis at a direct-sum index `inl i` is `(bᵢ, 0)`. -/
@[simp] theorem prodData_basis_inl (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (i : ι₁) :
    (prodData D₁ D₂).metric.basis (Sum.inl i) = (D₁.metric.basis i, 0) := by
  apply Prod.ext
  · exact Module.Basis.prod_apply_inl_fst _ _ i
  · exact Module.Basis.prod_apply_inl_snd _ _ i

/-- The product datum's basis at a direct-sum index `inr i` is `(0, bᵢ)`. -/
@[simp] theorem prodData_basis_inr (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (i : ι₂) :
    (prodData D₁ D₂).metric.basis (Sum.inr i) = (0, D₂.metric.basis i) := by
  apply Prod.ext
  · exact Module.Basis.prod_apply_inr_fst _ _ i
  · exact Module.Basis.prod_apply_inr_snd _ _ i

/-- **The Ricci endomorphism of the product is the product of the factor endomorphisms.** -/
theorem prodData_endoRicci (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (X Y : V₁ × V₂) :
    CurvatureOperator.endoRicci (prodData D₁ D₂).toCurvatureOperator X Y =
      LinearMap.prodMap (CurvatureOperator.endoRicci D₁.toCurvatureOperator X.1 Y.1)
        (CurvatureOperator.endoRicci D₂.toCurvatureOperator X.2 Y.2) := by
  apply LinearMap.ext
  intro Z
  apply Prod.ext <;> rfl

/-- **The Ricci contraction of the product is the sum of the factor contractions**:
`Ric((X₁,X₂),(Y₁,Y₂)) = Ric₁(X₁,Y₁) + Ric₂(X₂,Y₂)`. -/
theorem prodData_ricciForm (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) (X Y : V₁ × V₂) :
    (prodData D₁ D₂).ricciForm X Y =
      D₁.ricciForm X.1 Y.1 + D₂.ricciForm X.2 Y.2 := by
  rw [RiemannCurvatureData.ricciForm_apply, prodData_endoRicci,
    LinearMap.trace_prodMap']
  rfl

/-- The scalar curvature of the product datum is the sum of the factor scalar curvatures:
`scal(D₁ × D₂) = scal(D₁) + scal(D₂)`. This is the stated product formula; it is proved by
splitting the orthonormal-basis trace over the direct-sum index `ι₁ ⊕ ι₂` and using the Ricci
splitting. -/
theorem prodData_scalarCurvature (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) :
    (prodData D₁ D₂).scalarCurvature = D₁.scalarCurvature + D₂.scalarCurvature := by
  have h1 : (∑ i : ι₁,
        (prodData D₁ D₂).ricciForm ((prodData D₁ D₂).metric.basis (Sum.inl i))
          ((prodData D₁ D₂).metric.basis (Sum.inl i))) = D₁.scalarCurvature := by
    rw [RiemannCurvatureData.scalarCurvature_eq_sum_basis D₁]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prodData_ricciForm]
    simp [prodData_basis_inl]
  have h2 : (∑ i : ι₂,
        (prodData D₁ D₂).ricciForm ((prodData D₁ D₂).metric.basis (Sum.inr i))
          ((prodData D₁ D₂).metric.basis (Sum.inr i))) = D₂.scalarCurvature := by
    rw [RiemannCurvatureData.scalarCurvature_eq_sum_basis D₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prodData_ricciForm]
    simp [prodData_basis_inr]
  rw [RiemannCurvatureData.scalarCurvature_eq_sum_basis (prodData D₁ D₂),
    Fintype.sum_sum_type, h1, h2]

/-- The metric trace of the product is the sum of the factor metric traces. -/
theorem prodData_scalarMetricTrace (D₁ : RiemannCurvatureData V₁ ι₁)
    (D₂ : RiemannCurvatureData V₂ ι₂) :
    scalarMetricTrace (prodData D₁ D₂) = D₁.scalarCurvature + D₂.scalarCurvature := by
  rw [scalarMetricTrace_eq_scalarCurvature, prodData_scalarCurvature]

end RicciScalar
end D7
end Poincare
