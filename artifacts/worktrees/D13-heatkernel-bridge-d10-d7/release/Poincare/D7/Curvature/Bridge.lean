import Poincare.D7.Curvature.Blocked
import Probe.GeometryApi

/-!
# Poincare.D7.Curvature.Bridge

**D7 Riemann curvature tensor layer, part 5: bridges to the D2 release and to `Probe`.**

This file connects the D7 layer to the two pre-existing interfaces:

1. `Poincare.Longrun.Geometry.RiemannCurvatureTensor` — the acceptance-named bundled `(1,3)`
   Riemann curvature tensor of a `RiemannCurvatureData`, together with the kernel-checked
   first-pair skew-symmetry (`RiemannCurvatureTensor_first_pair_skew`), first Bianchi identity
   (`RiemannCurvatureTensor_bianchi`) and pair interchange
   (`RiemannCurvatureTensor_interchange`) for the metric-lowered `(0,4)` tensor.
2. `Probe.CurvatureTensor` — the D1 probe's manifold-level curvature interface.
   `Probe.CurvatureTensor.toCurvatureOperator` turns it pointwise into a D2 Stage1
   `CurvatureOperator`, and `ricci_eq_probe_ricci` proves that the D2
   `CurvatureOperator.ricci` of that operator is exactly the probe's
   `Probe.CurvatureTensor.ricci` (both are `tr(X ↦ R(X,Y)Z)`).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare.Longrun.Geometry

open Poincare.D7.Curvature

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The bundled `(1,3)` Riemann curvature tensor** of a metric-compatible torsion-free
connection datum. It is the D2 `AbstractConnection.curvature` bundled with the D7 metric
datum; the name `Poincare.Longrun.Geometry.RiemannCurvatureTensor` is the one fixed by the
`D7-riemann-curvature-tensor` acceptance criteria. -/
noncomputable def RiemannCurvatureTensor (D : RiemannCurvatureData V ι) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V :=
  D.curvature

/-- Defining equation of the bundled tensor. -/
@[simp] theorem RiemannCurvatureTensor_apply (D : RiemannCurvatureData V ι) (X Y Z : V) :
    RiemannCurvatureTensor D X Y Z = D.curvature X Y Z := rfl

/-- **Kernel-checked first-pair skew-symmetry** of the bundled Riemann curvature tensor:
`R(X,Y)Z = -R(Y,X)Z`. -/
theorem RiemannCurvatureTensor_first_pair_skew (D : RiemannCurvatureData V ι) (X Y Z : V) :
    RiemannCurvatureTensor D X Y Z = - RiemannCurvatureTensor D Y X Z :=
  D.curvature_skew₁₂ X Y Z

/-- **Kernel-checked first Bianchi identity** of the bundled Riemann curvature tensor:
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`. -/
theorem RiemannCurvatureTensor_bianchi (D : RiemannCurvatureData V ι) (X Y Z : V) :
    RiemannCurvatureTensor D X Y Z + RiemannCurvatureTensor D Y Z X +
      RiemannCurvatureTensor D Z X Y = 0 :=
  D.curvature_bianchi X Y Z

/-- **Kernel-checked pair interchange symmetry** of the metric-lowered `(0,4)` tensor:
`R(X,Y,Z,W) = R(Z,W,X,Y)`. -/
theorem RiemannCurvatureTensor_interchange (D : RiemannCurvatureData V ι) (X Y Z W : V) :
    D.curvatureForm X Y Z W = D.curvatureForm Z W X Y :=
  D.curvatureForm_interchange X Y Z W

/-- **Kernel-checked second-pair skew-symmetry** of the metric-lowered `(0,4)` tensor:
`R(X,Y,Z,W) = -R(X,Y,W,Z)`. -/
theorem RiemannCurvatureTensor_second_pair_skew (D : RiemannCurvatureData V ι)
    (X Y Z W : V) :
    D.curvatureForm X Y Z W = - D.curvatureForm X Y W Z :=
  D.curvatureForm_skew₃₄ X Y Z W

/-- The metric-lowered `(0,4)` Riemann tensor of the bundled curvature tensor. -/
noncomputable def RiemannCurvatureForm (D : RiemannCurvatureData V ι) (X Y Z W : V) : ℝ :=
  D.curvatureForm X Y Z W

end Poincare.Longrun.Geometry

namespace Probe
namespace CurvatureTensor

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Pointwise Stage1 curvature operator of a `Probe.CurvatureTensor`.** The probe interface
carries the first-pair antisymmetry and the first Bianchi identity as fields, exactly the two
obligations of the D2 Stage1 `CurvatureOperator`. -/
noncomputable def toCurvatureOperator (R : Probe.CurvatureTensor I M) (x : M) :
    CurvatureOperator ℝ (TangentSpace I x) where
  toTrilinear :=
    { toFun := fun X =>
        { toFun := fun Y =>
            { toFun := fun Z => R.toFun x X Y Z
              map_add' := fun Z₁ Z₂ => map_add (R.toFun x X Y) Z₁ Z₂
              map_smul' := fun c Z => map_smul (R.toFun x X Y) c Z }
          map_add' := fun Y₁ Y₂ => by ext Z; simp
          map_smul' := fun c Y => by ext Z; simp }
      map_add' := fun X₁ X₂ => by ext Y Z; simp
      map_smul' := fun c X => by ext Y Z; simp }
  first_pair_skew := fun X Y Z => R.antisymm x X Y Z
  first_bianchi := fun X Y Z => R.bianchi x X Y Z

/-- The bridge operator evaluates to the probe's curvature tensor. -/
@[simp] theorem toCurvatureOperator_apply
    (R : Probe.CurvatureTensor I M) (x : M) (X Y Z : TangentSpace I x) :
    R.toCurvatureOperator x X Y Z = R.toFun x X Y Z := rfl

end CurvatureTensor
end Probe

namespace Poincare
namespace D7
namespace Curvature

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

/-- **Bridge theorem `ricci_eq_probe_ricci`.** The D2 Stage1
`Poincare.CurvatureAlgebra.CurvatureOperator.ricci` of the bridged probe curvature tensor is
exactly the probe's own `Probe.CurvatureTensor.ricci`; both are the trace
`tr(X ↦ R(X,Y)Z)`. -/
theorem ricci_eq_probe_ricci {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (R : Probe.CurvatureTensor I M) (x : M) (Y Z : TangentSpace I x) :
    CurvatureOperator.ricci (R.toCurvatureOperator x) Y Z =
      Probe.CurvatureTensor.ricci R x Y Z := by
  simp only [CurvatureOperator.ricci, CurvatureOperator.ricciHom,
    CurvatureOperator.endoRicci, Probe.CurvatureTensor.ricci, Probe.CurvatureTensor.endo,
    Probe.CurvatureTensor.toCurvatureOperator]
  rfl

end Curvature
end D7
end Poincare
