/-
D11 adversarial audit — independent full-environment axiom sweep of every D10 module.

This driver is written by the D11 auditor, NOT by the D10 authors.  It imports all six
D10 modules (through their own audit drivers, whose `run_cmd` checks also execute) and
then, independently of the D10 authors' curated declaration lists, enumerates **every**
constant of the environment whose name lies in a D10 namespace (including private,
name-mangled constants) and re-runs `Lean.collectAxioms` (the same machinery as
`#print axioms`) on each of them.  A declaration fails if its axiom cone is not a subset
of `{propext, Classical.choice, Quot.sound}`, if it contains `sorryAx`, or if it is a
non-theorem constant without a stored value (covers `axiom`, `opaque`, `proof_wanted`).

Explicit `#print axioms` lines for the headline theorems follow the sweep.
-/
import Poincare.D10.HeatKernelEuclidean.AxiomAudit
import Poincare.D10.GaussianToolbox.PrintAxioms
import Poincare.D10.MaximumPrincipleRN.AxiomAudit
import Poincare.D10.BochnerEuclidean.Axioms
import Poincare.D10.JacobiConstantCurvature.AxiomAudit
import Poincare.D10.TriangulationLowDim.Audit

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let approved : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let inScope := env.constants.fold (fun acc n ci =>
    let s := n.toString
    if s.startsWith "Poincare.D10" || s.startsWith "Poincare.GaussianToolbox" ||
        s.startsWith "_private.Poincare.D10" || s.startsWith "_private.Poincare.GaussianToolbox" then
      (n, ci) :: acc
    else acc) []
  let mut total := 0
  let mut thms := 0
  let mut defs := 0
  let mut badCone : Array (Name × Array Name) := #[]
  let mut badValue : Array Name := #[]
  let mut theoremNames : Array Name := #[]
  for (n, ci) in inScope do
    total := total + 1
    if ci.isTheorem then
      thms := thms + 1
      theoremNames := theoremNames.push n
    else
      defs := defs + 1
    let axs ← Lean.collectAxioms n
    let bad := axs.filter fun a => !approved.contains a
    if !bad.isEmpty then
      badCone := badCone.push (n, bad)
    match ci with
    | .axiomInfo _ => badValue := badValue.push n
    | .opaqueInfo _ => badValue := badValue.push n
    | _ => pure ()
  logInfo ("D11AxiomSweep: scanned " ++ toString total ++ " constants (" ++ toString thms
    ++ " theorems, " ++ toString defs ++ " defs) in D10 namespaces")
  logInfo ("D11AxiomSweep: theorem names: "
    ++ String.intercalate ", " (theoremNames.toList.map Name.toString))
  if badCone.isEmpty && badValue.isEmpty then
    logInfo "D11AxiomSweep: PASS — every D10-namespace constant depends only on [propext, Classical.choice, Quot.sound]"
  else
    for (n, bad) in badCone do
      logError ("D11AxiomSweep: " ++ toString n ++ " has unapproved axioms "
        ++ String.intercalate ", " (bad.toList.map Name.toString))
    for n in badValue do
      logError ("D11AxiomSweep: " ++ toString n
        ++ " is a non-theorem without a stored value (axiom/opaque)")
    throwError "D11AxiomSweep: FAIL"

/-! ## Headline theorems, explicit `#print axioms` (D11 independent re-run) -/

#print axioms Poincare.D10.HeatKernelEuclidean.heat_equation
#print axioms Poincare.D10.HeatKernelEuclidean.heat_equation_fun
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral
#print axioms Poincare.D10.HeatKernelEuclidean.semigroupConvolutionIdentity
#print axioms Poincare.D10.HeatKernelEuclidean.laplacian_exp_norm_sq
#print axioms Poincare.D10.HeatKernelEuclidean.integral_exp_neg_mul_norm_sq

#print axioms Poincare.GaussianToolbox.integral_gaussianKernel
#print axioms Poincare.GaussianToolbox.integral_moment_zero
#print axioms Poincare.GaussianToolbox.integral_moment_two
#print axioms Poincare.GaussianToolbox.integral_moment_four
#print axioms Poincare.GaussianToolbox.integral_moment_six
#print axioms Poincare.GaussianToolbox.integral_gaussianDensity
#print axioms Poincare.GaussianToolbox.gaussianKernel_convolution
#print axioms Poincare.GaussianToolbox.gaussianDensity_convolution
#print axioms Poincare.GaussianToolbox.integral_gaussianVec
#print axioms Poincare.GaussianToolbox.integral_gaussianVecNormalized
#print axioms Poincare.GaussianToolbox.integral_standardGaussianDensity

#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle
#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle_strict
#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle_sSup
#print axioms Poincare.D10.MaximumPrincipleRN.exists_max_on_parabolicBoundary
#print axioms Poincare.D10.MaximumPrincipleRN.semidiscrete_comparison_principle
#print axioms Poincare.D10.MaximumPrincipleRN.semidiscrete_comparison_matrix

#print axioms Poincare.D10.BochnerEuclidean.bochner_identity
#print axioms Poincare.D10.BochnerEuclidean.bochner_identity_components
#print axioms Poincare.D10.BochnerEuclidean.harmonic_lap_gradNormSq
#print axioms Poincare.D10.BochnerEuclidean.harmonic_energy_density_subharmonic
#print axioms Poincare.D10.BochnerEuclidean.grad_eq_gradient
#print axioms Poincare.D10.BochnerEuclidean.lap_eq_laplacian

#print axioms Poincare.D10.jacobiSol_ode
#print axioms Poincare.D10.jacobiSol_solves_ivp
#print axioms Poincare.D10.jacobiSol_solvesJacobiODE
#print axioms Poincare.D10.jacobiSol_initial
#print axioms Poincare.D10.rauch_comparison
#print axioms Poincare.D10.rauch_comparison_sphere
#print axioms Poincare.D10.rauch_comparison_of_nonpos
#print axioms Poincare.D10.jacobiSol_nonneg
#print axioms Poincare.D10.jacobiSol_firstZero

#print axioms Poincare.D10.TriangulationLowDim.d10_eulerChar_values
#print axioms Poincare.D10.TriangulationLowDim.torus7_isClosedSurface
#print axioms Poincare.D10.TriangulationLowDim.torus7_eulerChar
#print axioms Poincare.D10.TriangulationLowDim.circleS1_eulerChar
#print axioms Poincare.D10.TriangulationLowDim.circleS1_isClosedCurve
#print axioms Poincare.D10.TriangulationLowDim.tetrahedronBoundary_eulerChar
#print axioms Poincare.D10.TriangulationLowDim.octahedronBoundary_isClosedSurface
#print axioms Poincare.D10.TriangulationLowDim.triangulates_self
#print axioms Poincare.D10.TriangulationLowDim.admitsFiniteTriangulation_realization
#print axioms Poincare.D10.TriangulationLowDim.moiseTriangulationTheorem_compactThreeManifold
