import Poincare.D7.Curvature.Basic
import Poincare.D7.Curvature.Symmetries
import Poincare.D7.Curvature.Sectional
import Poincare.D7.Curvature.Blocked
import Poincare.D7.Curvature.Bridge
import Poincare.D7.Curvature.Probe
import Poincare.D7.Curvature.Example

/-!
# Poincare.D7.Curvature

Umbrella module for the `D7-riemann-curvature-tensor` layer:

* `Poincare.D7.Curvature.Basic` — the metric-compatible torsion-free connection datum
  `RiemannCurvatureData`, the `(1,3)` tensor `curvature` (the D2 `AbstractConnection.curvature`),
  the metric-lowered `(0,4)` tensor `curvatureForm`, four-slot linearity, the bridge into the
  D2 Stage1 `CurvatureOperator`, and the non-vacuity constructors `zero` / `mean`;
* `Poincare.D7.Curvature.Symmetries` — first-pair skew-symmetry, first Bianchi identity,
  second-pair skew-symmetry (metric compatibility), pair interchange symmetry, the Ricci
  contraction `ricciForm` (the D2 `CurvatureOperator.ricci`) with its orthonormal-basis formula
  and symmetry, explicit index raising `ricciEndo`, and scalar curvature;
* `Poincare.D7.Curvature.Sectional` — the Gram determinant, nondegenerate 2-planes, sectional
  curvature, scaling/shear/GL(2) invariance, and the bundled `TwoPlane`;
* `Poincare.D7.Curvature.Blocked` — the explicit unproved `Prop`s with named blockers
  (`ManifoldCurvatureStatement`, `SecondBianchiStatement`);
* `Poincare.D7.Curvature.Bridge` — the acceptance-named
  `Poincare.Longrun.Geometry.RiemannCurvatureTensor` and the `Probe.CurvatureTensor` bridge
  with `ricci_eq_probe_ricci`;
* `Poincare.D7.Curvature.Probe` — the compilable mathlib/D7 API probe;
* `Poincare.D7.Curvature.Example` — the concrete non-flat `so(3)` model (`so3`) witnessing
  that the symmetry and sectional-curvature theorems are non-vacuous.
-/

