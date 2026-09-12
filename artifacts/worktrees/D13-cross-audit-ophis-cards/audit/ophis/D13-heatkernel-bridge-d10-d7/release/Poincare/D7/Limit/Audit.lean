/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.All

/-!
# Poincare.D7.Limit.Audit

Per-declaration `#print axioms` report for the D7 discrete-to-continuous limit
layer.  The expected axiom cones are `{}`, `{propext}` and
`{propext, Classical.choice, Quot.sound}`; any `sorryAx`, `native_decide` or
project axiom would show up here.

This file contains no mathematical content.
-/

namespace Poincare.D7.Limit

/-! ## Basic: meshes, time meshes, slabs -/

#print axioms abs_three_le
#print axioms GridMesh
#print axioms GridMesh.a_lt_b
#print axioms GridMesh.a_le_x
#print axioms GridMesh.x_le_b
#print axioms GridMesh.mem_Icc
#print axioms GridMesh.Refines
#print axioms GridMesh.Refines.refl
#print axioms GridMesh.Refines.trans
#print axioms GridMesh.uniform
#print axioms GridMesh.uniform_x
#print axioms TimeMesh
#print axioms TimeMesh.time_eq
#print axioms TimeMesh.monotone
#print axioms TimeMesh.strictMono
#print axioms SlabGrid
#print axioms SlabGrid.step_heatStep
#print axioms SlabGrid.ofHeatGridEvolution
#print axioms SlabGrid.ofHeatGridEvolution_v
#print axioms SlabGrid.toHeatGridEvolution
#print axioms SlabGrid.toHeatGridEvolution_u

/-! ## ErrorRecursion: the consistency certificate -/

#print axioms ConsistencyCertificate
#print axioms ConsistencyCertificate.alpha_mul_h_sq
#print axioms ConsistencyCertificate.error
#print axioms ConsistencyCertificate.error_left
#print axioms ConsistencyCertificate.error_right
#print axioms error_recursion_of_truncation
#print axioms ConsistencyCertificate.error_step
#print axioms ConsistencyCertificate.toHeatGridEvolution
#print axioms ConsistencyCertificate.toHeatGridEvolution_u
#print axioms truncationConstant
#print axioms truncationConstant_nonneg
#print axioms truncationConstant_eq

/-! ## Stability: the explicit error bound -/

#print axioms perturbed_recursion_stable
#print axioms ConsistencyCertificate.error_le_of_certificate
#print axioms ConsistencyCertificate.error_le_uniform
#print axioms ConsistencyCertificate.error_le_order
#print axioms ConsistencyCertificate.error_le_order_rate
#print axioms ConsistencyCertificate.error_eq_zero_of_exact

/-! ## Refinement: the mesh-independent maximum principle -/

#print axioms negEvolution
#print axioms negEvolution_u
#print axioms abs_le_of_initial_abs_le
#print axioms le_zero_of_initial_nonpos
#print axioms RefinesEvolution
#print axioms RefinesEvolution.toRefines
#print axioms RefinesEvolution.sup_initial_le
#print axioms maxPrinciple_uniform_in_mesh
#print axioms maxPrinciple_preserved_under_refinement

/-! ## Convergence: mesh convergence and the continuous interface -/

#print axioms tendsto_zero_of_abs_le
#print axioms HeatMeshSequence
#print axioms HeatMeshSequence.certificate
#print axioms HeatMeshSequence.error_le
#print axioms HeatMeshSequence.tendsto_u
#print axioms HeatMeshSequence.tendsto_value
#print axioms IsRefiningMesh
#print axioms HasVanishingError
#print axioms HeatMeshConvergence
#print axioms heatMeshConvergence_of_stability
#print axioms finiteMeshConvergence_of_stability
#print axioms continuousHeatMaxPrinciple_of_meshConvergence
#print axioms continuousHeatMaximumPrincipleInterface_of_meshConvergence
#print axioms HeatMeshConvergenceTheorem
#print axioms heatMeshConvergenceTheorem_isProp
#print axioms heatMeshConvergenceTheorem_of_vanishingError

/-! ## Blocked: state-only statements, blockers and missing dependencies -/

#print axioms ContinuousHeatMaximumPrincipleConjecture
#print axioms continuousHeatMaximumPrincipleConjecture_isProp
#print axioms continuousHeatMaximumPrincipleConjecture_of_meshConvergence
#print axioms Blocker
#print axioms blockers
#print axioms blockers_length
#print axioms blockers_ne_nil
#print axioms MissingMathlibDependencies
#print axioms MissingMathlibDependencies_length
#print axioms PresentMathlibDependencies
#print axioms PresentMathlibDependencies_length

/-! ## Example: the quadratic certificate and negative controls -/

#print axioms quadSolution
#print axioms quadSolution_continuousHeatHypotheses
#print axioms quadMesh
#print axioms quadMesh_x
#print axioms quadTime
#print axioms quadTime_time
#print axioms quad_step
#print axioms quadSlab
#print axioms quadSlab_v
#print axioms quadCertificate
#print axioms quad_error_zero
#print axioms quad_truncation_eq_of_alpha_zero
#print axioms quad_truncation_abs_pos
#print axioms cfl_essential

end Poincare.D7.Limit
