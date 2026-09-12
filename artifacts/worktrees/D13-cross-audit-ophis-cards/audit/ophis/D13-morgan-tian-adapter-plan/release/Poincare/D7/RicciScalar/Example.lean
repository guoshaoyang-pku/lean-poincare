import Poincare.D7.RicciScalar.Variation
import Poincare.D7.Curvature.Example
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Poincare.D7.RicciScalar.Example

**D7 Ricci/scalar layer, part 5: concrete non-vacuity witnesses.**

The theorems of this layer are stated for an arbitrary metric-compatible torsion-free connection
datum. This module evaluates them on the concrete non-flat `so(3)` model of
`Poincare.D7.Curvature.So3`:

* `so3_ricciForm_apply` — the Ricci contraction of the `so(3)` mean connection is
  `Ric(X,Y) = ½ ⟨X,Y⟩`; the proof uses the scalar triple product identity
  `Y × (X × Z) = (Y·Z) X - (X·Y) Z` and the trace formula `tr(f.smulRight x) = f x`;
* `so3_scalarCurvature` — `scal = 3/2`, so the scalar curvature is nonzero;
* `so3_ricciTrace_basis_independent_witness` — the basis-trace formula gives the same value
  `1/2` in the standard basis and in a permuted basis, instantiating basis-independence on a
  non-flat model;
* `prodData_so3_scalarCurvature` — the product formula on `so(3) × so(3)` gives `3 = 3/2 + 3/2`,
  so `prodData_scalarCurvature` is non-vacuous.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators Matrix

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace RicciScalar

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature
open Poincare.D7.Curvature.So3

/-- **Trace of the composed cross-product endomorphism.**
`tr(Z ↦ Y × (X × Z)) = -2 ⟨X,Y⟩`, from the scalar triple product identity and
`tr(f.smulRight x) = f x`. -/
theorem so3_trace_comp (X Y : V) :
    LinearMap.trace ℝ V ((crossProduct Y).comp (crossProduct X)) = -(2 : ℝ) * (X ⬝ᵥ Y) := by
  have h : ∀ Z : V, (crossProduct Y).comp (crossProduct X) Z =
      ((dotProductBilin ℝ ℝ Y).smulRight X -
        (X ⬝ᵥ Y) • (LinearMap.id : V →ₗ[ℝ] V)) Z := by
    intro Z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.id_apply, dotProductBilin_apply_apply]
    exact cross_cross_eq_smul_sub_smul' Y X Z
  have hfun : (crossProduct Y).comp (crossProduct X) =
      (dotProductBilin ℝ ℝ Y).smulRight X -
        (X ⬝ᵥ Y) • (LinearMap.id : V →ₗ[ℝ] V) := by
    apply LinearMap.ext
    intro Z
    exact h Z
  rw [hfun, map_sub, map_smul, LinearMap.trace_smulRight, LinearMap.trace_id]
  simp [dotProduct_comm Y X, smul_eq_mul]
  ring

/-- **Ricci contraction of the `so(3)` model**: `Ric(X,Y) = ½ ⟨X,Y⟩`. -/
theorem so3_ricciForm_apply (X Y : V) : so3.ricciForm X Y = (1 / 2 : ℝ) * (X ⬝ᵥ Y) := by
  have hEndo : CurvatureOperator.endoRicci so3.toCurvatureOperator X Y =
      (-(1 / 4) : ℝ) • (crossBracket.bracket Y).comp (crossBracket.bracket X) :=
    mean_endoRicci crossBracket X Y
  rw [RiemannCurvatureData.ricciForm_apply, hEndo, map_smul]
  change -(1 / 4) • LinearMap.trace ℝ V ((crossProduct Y).comp (crossProduct X)) =
    1 / 2 * (X ⬝ᵥ Y)
  rw [so3_trace_comp]
  ring

/-- Each diagonal Ricci component of the model is `1/2`. -/
theorem so3_ricciForm_e_self (i : Fin 3) : so3.ricciForm (e i) (e i) = (1 / 2 : ℝ) := by
  rw [so3_ricciForm_apply]
  simp [e, dotProduct, Pi.single_apply]

/-- **Scalar curvature of the `so(3)` model**: `scal = 3/2`. -/
theorem so3_scalarCurvature : so3.scalarCurvature = (3 / 2 : ℝ) := by
  rw [RiemannCurvatureData.scalarCurvature_eq_sum_basis, Fin.sum_univ_three]
  have hb : ∀ i : Fin 3, so3.metric.basis i = e i := fun i => stdBasis_eq_e i
  simp only [hb, so3_ricciForm_e_self]
  norm_num

/-- **Basis-independence witness.** The standard basis and the basis obtained by swapping the
first two standard basis vectors give the same Ricci trace `Ric(e₀,e₀) = 1/2`. -/
noncomputable def permBasis : Module.Basis (Fin 3) ℝ V :=
  stdBasis.reindex (Equiv.swap (0 : Fin 3) 1)

theorem so3_ricciTrace_e0_e0 : ricciTrace so3 stdBasis (e 0) (e 0) = (1 / 2 : ℝ) := by
  rw [ricciTrace_eq_ricciForm, so3_ricciForm_e_self 0]

theorem so3_ricciTrace_basis_independent_witness :
    ricciTrace so3 stdBasis (e 0) (e 0) = ricciTrace so3 permBasis (e 0) (e 0) :=
  ricciTrace_basis_independent so3 stdBasis permBasis (e 0) (e 0)

/-- The permuted-basis Ricci trace also evaluates to `1/2` (through basis-independence). -/
theorem so3_ricciTrace_permBasis_e0_e0 :
    ricciTrace so3 permBasis (e 0) (e 0) = (1 / 2 : ℝ) := by
  rw [← so3_ricciTrace_basis_independent_witness, so3_ricciTrace_e0_e0]

/-- **The product formula on `so(3) × so(3)`**: `scal = 3/2 + 3/2 = 3`. -/
theorem prodData_so3_scalarCurvature :
    (prodData so3 so3).scalarCurvature = (3 : ℝ) := by
  rw [prodData_scalarCurvature, so3_scalarCurvature]
  norm_num

/-- The product Ricci contraction is the sum of the factor contractions on the model. -/
theorem prodData_so3_ricciForm (X Y : V × V) :
    (prodData so3 so3).ricciForm X Y =
      (1 / 2 : ℝ) * (X.1 ⬝ᵥ Y.1) + (1 / 2 : ℝ) * (X.2 ⬝ᵥ Y.2) := by
  rw [prodData_ricciForm, so3_ricciForm_apply, so3_ricciForm_apply]

end RicciScalar
end D7
end Poincare
