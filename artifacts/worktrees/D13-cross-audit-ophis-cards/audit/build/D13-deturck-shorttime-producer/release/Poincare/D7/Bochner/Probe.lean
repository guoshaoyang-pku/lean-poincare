/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Poincare.D7.Bochner.Blocked
import Poincare.D7.Bochner.Example

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.Probe

**D7 Bochner / Weitzenböck layer, part 6: the mathlib API probe and the D7 API index.**

This module is a compilable probe. Every `#check` below must succeed against the pinned
toolchain, and every `#check_failure` must fail (recording a genuinely absent declaration). The
output of this file is the machine-checked record of the probe required by the task.

## Probe result (pinned mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`)

* **Present and reused**: `CovariantDerivative`, `CovariantDerivative.leviCivitaConnection`,
  `CovariantDerivative.IsLeviCivitaConnection`,
  `CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`,
  `CovariantDerivative.IsLeviCivitaConnection.apply_eq` (the Koszul formula), `mfderiv`,
  `ContMDiff`, `TangentSpace`, `RiemannianBundle`, `IsRiemannianManifold`, `ModelWithCorners`,
  `IsManifold`, `iteratedFDeriv`, `fderiv`, and the discrete/linear-algebra API used by the model
  (`Finset.sum_sub_distrib`, `Fin.sum_univ_two`, `Pi.single`, `Matrix`).
* **Absent**: `Hessian`, `LaplaceBeltrami`, `Riemann`, `Ricci`, `Bochner`, `Weitzenbock`,
  `CovariantDerivative.secondCovariantDerivative`, `CovariantDerivative.curvature`,
  `Manifold.curvature`, `Laplacian`, `roughLaplacian`, `RiemannianVolumeMeasure`. The smooth
  Bochner formula is therefore the blocked `Prop` of `Poincare.D7.Bochner.Blocked`, with the exact
  missing dependencies listed there.

All proofs are complete; the `#print axioms` audit reports only the standard Lean dependencies.
-/

open Bundle Manifold

open scoped Bundle Manifold

namespace Poincare.D7.Bochner

/-! ## 1. Present mathlib API: the covariant derivative and the Levi-Civita connection -/

#check CovariantDerivative
#check CovariantDerivative.leviCivitaConnection
#check CovariantDerivative.IsLeviCivitaConnection
#check CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
#check CovariantDerivative.IsLeviCivitaConnection.apply_eq
#check CovariantDerivative.IsLeviCivitaConnection.uniqueness
#check CovariantDerivative.torsion
#check CovariantDerivative.IsMetricCompatible

/-! ## 2. Present mathlib API: smooth manifolds and Euclidean calculus -/

#check mfderiv
#check ContMDiff
#check TangentSpace
#check RiemannianBundle
#check IsRiemannianManifold
#check ModelWithCorners
#check IsManifold
#check iteratedFDeriv
#check fderiv

/-! ## 3. Present mathlib API: the discrete/linear-algebra model -/

#check Finset.sum_sub_distrib
#check Finset.sum_congr
#check Fin.sum_univ_two
#check Pi.single
#check Matrix

/-! ## 4. Absent at the pinned revision (recorded by `#check_failure`) -/

#check_failure Hessian
#check_failure LaplaceBeltrami
#check_failure Riemann
#check_failure Ricci
#check_failure Bochner
#check_failure Weitzenbock
#check_failure CovariantDerivative.secondCovariantDerivative
#check_failure CovariantDerivative.curvature
#check_failure Manifold.curvature
#check_failure Laplacian
#check_failure roughLaplacian
#check_failure RiemannianVolumeMeasure

/-! ## 5. The D7 Bochner API index -/

#check BochnerCertificate
#check BochnerCertificate.bochner
#check BochnerCertificate.oneFormLaplacian_eq_roughLaplacian_of_ricci_zero
#check GradientCertificate
#check GradientCertificate.gradient_estimate
#check GradientCertificate.bochner_inequality
#check GradientCertificate.gradient_estimate_eq_iff_ricci_zero
#check gradientCertificateOfData
#check Euclidean.euclideanBochnerCertificate
#check diff_laplacian_comm
#check Euclidean.oneFormLaplacian_eq_roughLaplacian
#check SmoothBochnerDatum
#check IsSmoothBochnerDatum
#check SmoothBochnerFormulaStatement
#check SmoothBochnerWeitzenbockStatement
#check SmoothBochnerGradientEstimateStatement
#check MissingMathlibDependencies
#check PresentMathlibDependencies
#check BlockerHessian
#check BlockerLaplaceBeltrami
#check BlockerRoughLaplacian
#check BlockerManifoldCurvature
#check BlockerBochnerWeitzenbock
#check flatExampleCertificate
#check curvedExampleCertificate
#check curvedExampleGradient
#check negativeControl

end Poincare.D7.Bochner
