/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D9-ancient-kappa-solutions builder
-/
module

public import Poincare.D9.AncientKappa.Basic
public import Poincare.D9.AncientKappa.GaussianSoliton
public import Poincare.D9.AncientKappa.Classification

/-!
# Poincare.D9.AncientKappa.PrintAxioms

Per-declaration logical-dependency report for the D9 ancient-solution / κ-solution / soliton
interfaces.

Each `#print axioms` line below is a kernel command: it lists the logical postulates on which
the declaration depends.  Every declaration in this development is expected to depend only on
`propext`, `Classical.choice` and `Quot.sound` (or on nothing), and never on an unproved hole or
a project-specific postulate.
-/

@[expose] public section

/-! ## Ancient solutions -/

#print axioms Poincare.Longrun.AncientKappa.AncientSolution.mem_timeDomain_iff
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.time_le_zero
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.ricciFlow_equation
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.exists_curvature_bound
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.ricci_symm

/-! ## κ-non-collapsing at all scales -/

#print axioms Poincare.Longrun.AncientKappa.KappaNoncollapsingAllScales.toKappaNoncollapsing
#print axioms Poincare.Longrun.AncientKappa.KappaNoncollapsingAllScales.volume_ball_pos
#print axioms Poincare.Longrun.AncientKappa.KappaNoncollapsingAllScales.mono
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.toKappaNoncollapsing

/-! ## Gradient shrinking solitons -/

#print axioms Poincare.Longrun.AncientKappa.GradientShrinkingSoliton.soliton_equation_one
#print axioms Poincare.Longrun.AncientKappa.ManifoldGradientShrinkingSoliton.soliton_equation_one

/-! ## Gaussian shrinking soliton on `ℝⁿ` -/

#print axioms Poincare.Longrun.AncientKappa.euclidean_ricci_zero
#print axioms Poincare.Longrun.AncientKappa.fderiv_gaussianPotential
#print axioms Poincare.Longrun.AncientKappa.fderiv_fderiv_gaussianPotential
#print axioms Poincare.Longrun.AncientKappa.hessian_gaussianPotential
#print axioms Poincare.Longrun.AncientKappa.inner_gradient_gaussianPotential
#print axioms Poincare.Longrun.AncientKappa.gradient_gaussianPotential
#print axioms Poincare.Longrun.AncientKappa.gaussian_soliton_equation
#print axioms Poincare.Longrun.AncientKappa.gaussianMetric_inner
#print axioms Poincare.Longrun.AncientKappa.gaussianGradientShrinkingSoliton
#print axioms Poincare.Longrun.AncientKappa.gaussianGradientShrinkingSoliton_potential
#print axioms Poincare.Longrun.AncientKappa.gaussianGradientShrinkingSoliton_tau
#print axioms Poincare.Longrun.AncientKappa.gaussianGradientShrinkingSoliton_equation

/-! ## State-only statements -/

#print axioms Poincare.Longrun.AncientKappa.ThreeDimKappaSolution.timeDomain_eq
#print axioms Poincare.Longrun.AncientKappa.ThreeDimKappaSolution.kappa_pos
#print axioms Poincare.Longrun.AncientKappa.ThreeDimKappaSolution.exists_curvature_bound
#print axioms Poincare.Longrun.AncientKappa.threeDimensionalKappaSolutionClassification_iff
#print axioms Poincare.Longrun.AncientKappa.asymptoticSolitonStatement_iff
#print axioms Poincare.Longrun.AncientKappa.perelmanCompactnessTheorem_iff
#print axioms Poincare.Longrun.AncientKappa.canonicalNeighborhoodLinkage_iff
