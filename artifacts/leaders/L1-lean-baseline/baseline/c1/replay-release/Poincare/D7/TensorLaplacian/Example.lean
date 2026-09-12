import Poincare.D7.TensorLaplacian.Commutation
import Poincare.D7.TensorLaplacian.Evolution
import Poincare.D7.Curvature.Example
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Poincare.D7.TensorLaplacian.Example

**D7 tensor Laplacian layer, part 4: concrete inhabitants, the nonzero-curvature model, and the
negative control for the evolution identity.**

This module exhibits instances so that the interface of `Poincare.D7.TensorLaplacian` is
demonstrably non-vacuous:

* `scalarTensorData` — the trivial tensor representation `T = ℝ` (zero connection and curvature);
* `vectorTensorData` — the vector-field representation `T = V`, whose curvature certificate is
  the **definition** of the D7 curvature (`∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]}Z = R(X,Y)Z`);
* `prodTensorData` — the componentwise product of two tensor representations;
* `so3_ricciNormSq_pos` — in the concrete `so(3)` model of `Poincare.D7.Curvature.Example` the
  Frobenius norm squared `|Ric|²` is **strictly positive** (`|Ric|² ≥ (1/2)²`), so the evolution
  identity is not the trivial `0 = 0` there;
* `so3EvolutionCertificate` — a `ScalarEvolutionCertificate` over the nonzero-curvature `so3`
  datum, with `lapScal = 0` and `scalDeriv = 2 |Ric|²`; the identity holds and its right-hand
  side is strictly positive;
* `so3_vector_curvature_witness` — the vector-field representation of the `so(3)` datum has the
  nonzero curvature `R(e₀,e₁)e₁ = ¼ e₀`;
* `wrongBianchiExample` and `wrongBianchi_identity_fails` — a **negative control** showing that
  the contracted Bianchi certificate is essential: with the opposite sign the identity fails.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Poincare
namespace D7
namespace TensorLaplacian

universe v w t t₁ t₂

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Inhabitants of the tensor-data interface -/

/-- **The scalar representation**: `T = ℝ` with the zero covariant derivative and the zero
curvature action. -/
noncomputable def scalarTensorData (D : RiemannCurvatureData V ι) : TensorConnectionData D ℝ where
  nabla := 0
  curvature := 0
  curvature_certificate := by
    intro X Y s
    simp

/-- **The vector-field representation**: `T = V` with the D7 covariant derivative
`∇_X Y` and the D7 curvature `R(X,Y)Z`. The curvature certificate is the definition of the D7
curvature. -/
noncomputable def vectorTensorData (D : RiemannCurvatureData V ι) :
    TensorConnectionData D V where
  nabla := D.conn.nabla
  curvature := D.curvature
  curvature_certificate := fun _ _ _ => rfl

/-- **The product representation**: componentwise covariant derivative and curvature. -/
noncomputable def prodTensorData (D : RiemannCurvatureData V ι)
    {T₁ : Type t₁} {T₂ : Type t₂} [AddCommGroup T₁] [Module ℝ T₁]
    [AddCommGroup T₂] [Module ℝ T₂] (TD₁ : TensorConnectionData D T₁)
    (TD₂ : TensorConnectionData D T₂) : TensorConnectionData D (T₁ × T₂) where
  nabla :=
    { toFun := fun X =>
        { toFun := fun s => (TD₁.nabla X s.1, TD₂.nabla X s.2)
          map_add' := by
            intro s u
            ext <;> simp
          map_smul' := by
            intro a s
            ext <;> simp }
      map_add' := by
        intro X Y
        ext s <;> simp
      map_smul' := by
        intro a X
        ext s <;> simp }
  curvature :=
    { toFun := fun X =>
        { toFun := fun Y =>
            { toFun := fun s => (TD₁.curvature X Y s.1, TD₂.curvature X Y s.2)
              map_add' := by
                intro s u
                ext <;> simp
              map_smul' := by
                intro a s
                ext <;> simp }
          map_add' := by
            intro Y₁ Y₂
            ext s <;> simp
          map_smul' := by
            intro a Y
            ext s <;> simp }
      map_add' := by
        intro X₁ X₂
        ext Y s <;> simp
      map_smul' := by
        intro a X
        ext Y s <;> simp }
  curvature_certificate := by
    intro X Y s
    apply Prod.ext <;>
      simp [TD₁.curvature_certificate, TD₂.curvature_certificate]

/-! ## The nonzero-curvature `so(3)` model -/

namespace So3Example

open Poincare.D7.Curvature

/-- The Ricci form of the `so(3)` model at the first frame vector is `1/2` (reused from
`Poincare.D7.Curvature.Example`). -/
theorem so3_ricciForm_basis_zero :
    So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis 0) = (1 / 2 : ℝ) := by
  have hb : So3.so3.metric.basis 0 = So3.e 0 := So3.stdBasis_eq_e 0
  rw [hb]
  exact So3.so3_ricciForm_e0_e0

/-- **`|Ric|² > 0` for the `so(3)` model**: the Frobenius norm squared dominates the single
diagonal term `(1/2)²`. -/
theorem so3_ricciNormSq_pos : 0 < ricciNormSq So3.so3 := by
  have hsingle : So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis 0)
        * So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis 0)
      ≤ ∑ j : Fin 3, So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j)
          * So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j) :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 3 => So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j)
        * So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j))
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ (0 : Fin 3))
  have hinner : ∀ i : Fin 3,
      (0 : ℝ) ≤ ∑ j : Fin 3, So3.so3.ricciForm (So3.so3.metric.basis i) (So3.so3.metric.basis j)
        * So3.so3.ricciForm (So3.so3.metric.basis i) (So3.so3.metric.basis j) :=
    fun i => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have houter :
      (∑ j : Fin 3, So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j)
          * So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j))
      ≤ ricciNormSq So3.so3 := by
    simp only [ricciNormSq]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 3 => ∑ j : Fin 3, So3.so3.ricciForm (So3.so3.metric.basis i)
        (So3.so3.metric.basis j) * So3.so3.ricciForm (So3.so3.metric.basis i)
        (So3.so3.metric.basis j))
      (fun i _ => hinner i) (Finset.mem_univ (0 : Fin 3))
  calc (0 : ℝ) < (1 / 2) * (1 / 2) := by norm_num
    _ = So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis 0)
        * So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis 0) := by
        rw [so3_ricciForm_basis_zero]
    _ ≤ ∑ j : Fin 3, So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j)
        * So3.so3.ricciForm (So3.so3.metric.basis 0) (So3.so3.metric.basis j) := hsingle
    _ ≤ ricciNormSq So3.so3 := houter

/-- The derivative of the linear scalar path `scal₀ + t * c` is `c`. -/
private theorem hasDerivAt_scalPath (c : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => So3.so3.scalarCurvature + s * c) c t := by
  have h1 : HasDerivAt (fun s : ℝ => s * c) c t := by
    simpa using (hasDerivAt_id t).mul_const c
  have h0 : HasDerivAt (fun _ : ℝ => So3.so3.scalarCurvature) (0 : ℝ) t :=
    hasDerivAt_const t _
  have h2 := h0.add h1
  have hfun : ((fun _ : ℝ => So3.so3.scalarCurvature) + fun s : ℝ => s * c)
      = fun s : ℝ => So3.so3.scalarCurvature + s * c := by
    funext s
    rfl
  rw [hfun] at h2
  simpa using h2

/-- **A non-vacuous evolution certificate over the nonzero-curvature `so(3)` datum.** The scalar
path is `scal(t) = scal₀ + 2 |Ric|² t` with `Δ scal = 0`, so the identity
`∂ₜ scal = Δ scal + 2 |Ric|²` holds with a strictly positive right-hand side. -/
noncomputable def so3EvolutionCertificate :
    ScalarEvolutionCertificate So3.so3 (ricciFlowVelocity So3.so3) where
  scalPath := fun t => So3.so3.scalarCurvature + t * (2 * ricciNormSq So3.so3)
  scalDeriv := fun _ => 2 * ricciNormSq So3.so3
  lapScal := fun _ => 0
  divdivH := fun _ => 0
  velocity := fun _ _ => rfl
  flow := fun t => hasDerivAt_scalPath (2 * ricciNormSq So3.so3) t
  variation := by
    intro t
    have hp : pairingH So3.so3 (ricciFlowVelocity So3.so3) = -2 * ricciNormSq So3.so3 :=
      pairingH_ricciFlowVelocity So3.so3
    rw [hp]
    have hval : -(-2 * (0 : ℝ)) + 0 - (-2 * ricciNormSq So3.so3)
        = 2 * ricciNormSq So3.so3 := by ring
    rw [hval]
    exact hasDerivAt_scalPath (2 * ricciNormSq So3.so3) t
  bianchi := fun _ => by simp
  anchor := by simp

/-- **The identity holds on the `so(3)` model**: `∂ₜ scal = Δ scal + 2 |Ric|²`. -/
theorem so3_evolution_identity :
    so3EvolutionCertificate.scalDeriv 0
      = so3EvolutionCertificate.lapScal 0 + 2 * ricciNormSq So3.so3 :=
  so3EvolutionCertificate.scalarDeriv_eq 0

/-- **The right-hand side of the `so(3)` identity is strictly positive**, so the identity is not
the trivial `0 = 0`. -/
theorem so3_evolution_rhs_pos :
    0 < so3EvolutionCertificate.lapScal 0 + 2 * ricciNormSq So3.so3 := by
  have h := so3_ricciNormSq_pos
  simp only [so3EvolutionCertificate]
  linarith

/-- **The vector-field representation of the `so(3)` model is a tensor connection**, and its
curvature action is the nonzero D7 curvature. -/
theorem so3_vector_curvature_witness :
    (vectorTensorData So3.so3).curvature (So3.e 0) (So3.e 1) (So3.e 1)
      = (1 / 4 : ℝ) • So3.e 0 :=
  So3.so3_curvature_e0_e1_e1

end So3Example

/-! ## Negative control: the Bianchi certificate is essential -/

/-- **A raw scalar-evolution model with the opposite Bianchi sign.** It keeps the variation
formula and the flow equation but replaces the contracted Bianchi identity
`divdivH = -Δ scal` by `divdivH = Δ scal`. -/
structure WrongBianchiData where
  /-- The scalar curvature path. -/
  scal : ℝ → ℝ
  /-- Its derivative. -/
  scalDeriv : ℝ → ℝ
  /-- The Laplacian `Δ scal`. -/
  lapScal : ℝ → ℝ
  /-- The double divergence. -/
  divdivH : ℝ → ℝ
  /-- The Frobenius norm squared. -/
  ricNormSq : ℝ
  /-- The pairing `⟨h, Ric⟩`. -/
  pairingH : ℝ
  /-- The flow equation. -/
  flow : ∀ t : ℝ, HasDerivAt scal (scalDeriv t) t
  /-- The Lichnerowicz trace variation. -/
  variation : ∀ t : ℝ, HasDerivAt scal (-(-2 * lapScal t) + divdivH t - pairingH) t
  /-- **The wrong-sign Bianchi relation** `divdivH = Δ scal`. -/
  bianchi_wrong : ∀ t : ℝ, divdivH t = lapScal t
  /-- The pairing is `-2 |Ric|²`. -/
  pairing_eq : pairingH = -2 * ricNormSq

/-- A concrete model satisfying every relation of `WrongBianchiData` with nonzero Laplacian:
`Δ scal = 1`, `|Ric|² = 1`, `∂ₜ scal = 5`. -/
noncomputable def wrongBianchiExample : WrongBianchiData where
  scal := fun t => 5 * t
  scalDeriv := fun _ => 5
  lapScal := fun _ => 1
  divdivH := fun _ => 1
  ricNormSq := 1
  pairingH := -2
  flow := by
    intro t
    have h : HasDerivAt (fun s : ℝ => 5 * s) 5 t := by
      simpa using (hasDerivAt_id t).const_mul 5
    exact h
  variation := by
    intro t
    have hval : -(-2 * (1 : ℝ)) + 1 - (-2) = 5 := by norm_num
    rw [hval]
    have h : HasDerivAt (fun s : ℝ => 5 * s) 5 t := by
      simpa using (hasDerivAt_id t).const_mul 5
    exact h
  bianchi_wrong := fun _ => rfl
  pairing_eq := by norm_num

/-- **The negative control**: in `wrongBianchiExample` the scalar-evolution identity
`∂ₜ scal = Δ scal + 2 |Ric|²` is **false** (`5 ≠ 1 + 2`). Hence the contracted Bianchi
certificate in `ScalarEvolutionCertificate` is essential, not decorative. -/
theorem wrongBianchi_identity_fails :
    wrongBianchiExample.scalDeriv 0
      ≠ wrongBianchiExample.lapScal 0 + 2 * wrongBianchiExample.ricNormSq := by
  simp only [wrongBianchiExample]
  norm_num

end TensorLaplacian
end D7
end Poincare
