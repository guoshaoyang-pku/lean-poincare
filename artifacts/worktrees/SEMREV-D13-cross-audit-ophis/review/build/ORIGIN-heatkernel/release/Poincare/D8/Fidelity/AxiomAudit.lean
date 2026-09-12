/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D8-moise-statement-bridge)
-/
import Poincare.D8.Fidelity.FidelityCard

/-!
# Poincare.D8.Fidelity.AxiomAudit

`#print axioms` audit for every declaration authored by task `D8-moise-statement-bridge`.

Expected output for every entry: dependence on at most the three Lean kernel axioms
`propext`, `Classical.choice`, `Quot.sound` — and in particular **no** `sorryAx`, no
project-specific postulate, no `unsafe`, no `native_decide`.

This file contains no definitions and no proofs; it exists so that the foundational
dependency report is part of the checked build.
-/

open scoped Manifold ContDiff Topology

/-! ## Smooth structures and the equivalence relation (`SmoothStructure.lean`) -/

#print axioms Poincare.D8.Fidelity.SmoothStructure
#print axioms Poincare.D8.Fidelity.SmoothStructure.Diffeomorph
#print axioms Poincare.D8.Fidelity.SmoothStructure.Diffeomorph.toHomeomorph
#print axioms Poincare.D8.Fidelity.SmoothStructure.diffeomorph_refl
#print axioms Poincare.D8.Fidelity.SmoothStructure.diffeomorph_symm
#print axioms Poincare.D8.Fidelity.SmoothStructure.diffeomorph_trans
#print axioms Poincare.D8.Fidelity.SmoothStructure.diffeomorph_equivalence

/-! ## Moise certificate (`MoiseData.lean`) -/

#print axioms Poincare.D8.Fidelity.MoiseData
#print axioms Poincare.D8.Fidelity.MoiseData.toSmoothStructure
#print axioms Poincare.D8.Fidelity.MoiseData.diffeomorph_self
#print axioms Poincare.D8.Fidelity.MoiseData.diffeomorph_any
#print axioms Poincare.D8.Fidelity.MoiseData.uniqueness_relation
#print axioms Poincare.D8.Fidelity.MoiseData.diffeomorph_iff_eq
#print axioms Poincare.D8.Fidelity.MoiseData.diffeomorph_of_moiseData
#print axioms Poincare.D8.Fidelity.MoiseData.nonempty_chartedSpace
#print axioms Poincare.D8.Fidelity.MoiseData.isManifold

/-! ## Statement-fidelity bridge (`Bridge.lean`) -/

#print axioms Poincare.D8.Fidelity.SmoothStructure.DiffeomorphSphere
#print axioms Poincare.D8.Fidelity.SmoothStructure.DiffeomorphSphere.toHomeomorph
#print axioms Poincare.D8.Fidelity.SmoothStructure.SmoothPoincareConclusion
#print axioms Poincare.D8.Fidelity.SmoothStructure.smoothPoincareConclusion_iff_stage6
#print axioms Poincare.D8.Fidelity.SmoothStructure.diffeomorphSphere_shape
#print axioms Poincare.D8.Fidelity.SmoothStructure.SmoothPoincareConclusion.of_diffeomorph
#print axioms Poincare.D8.Fidelity.topological_of_smoothConclusion
#print axioms Poincare.D8.Fidelity.stage6Target_of_smoothConclusion_and_moiseData
#print axioms Poincare.D8.Fidelity.stage6Target_of_smoothConclusion_and_compactThreeManifold
#print axioms Poincare.D8.Fidelity.smoothPoincareConclusion_of_missingSmoothPoincare
#print axioms Poincare.D8.Fidelity.stage6Target_of_missingSmoothPoincare_and_moiseData
#print axioms Poincare.D8.Fidelity.sphereRecognition_of_smoothConclusion_and_moiseData

/-! ## Statement-only Moise ledger (`MoiseStatement.lean`) -/

#print axioms Poincare.D8.Fidelity.moiseExistence
#print axioms Poincare.D8.Fidelity.moiseUniqueness
#print axioms Poincare.D8.Fidelity.moiseTheorem
#print axioms Poincare.D8.Fidelity.moiseTheorem_iff
#print axioms Poincare.D8.Fidelity.moiseExistence_of_moiseTheorem
#print axioms Poincare.D8.Fidelity.moiseUniqueness_of_moiseTheorem
#print axioms Poincare.D8.Fidelity.moiseTheorem_of_existence_uniqueness
#print axioms Poincare.D8.Fidelity.moiseData_of_existence_uniqueness
#print axioms Poincare.D8.Fidelity.PLStructure
#print axioms Poincare.D8.Fidelity.missingTriangulability
#print axioms Poincare.D8.Fidelity.missingSmoothStructureOfPLStructure
#print axioms Poincare.D8.Fidelity.missingSmoothStructureUniquenessOnPL
#print axioms Poincare.D8.Fidelity.missingHomeomorphismIsotopicToDiffeomorphism
#print axioms Poincare.D8.Fidelity.missingHirschObstructionVanishing
#print axioms Poincare.D8.Fidelity.missingKirbySiebenmannObstruction
#print axioms Poincare.D8.Fidelity.missingFourDimensionalSmoothingFailure
#print axioms Poincare.D8.Fidelity.moiseTheorem_of_triangulability_smoothing
#print axioms Poincare.D8.Fidelity.moiseData_of_triangulability_smoothing
#print axioms Poincare.D8.Fidelity.stage6Target_of_moiseTheorem_and_uniformSmooth
#print axioms Poincare.D8.Fidelity.sphereRecognition_of_moiseTheorem_and_uniformSmooth

/-! ## Fidelity card (`FidelityCard.lean`) -/

#print axioms Poincare.D8.Fidelity.FidelityEntry
#print axioms Poincare.D8.Fidelity.fidelityCard

/-! ## Re-exported shared targets consumed by the bridge -/

#print axioms Poincare.Stage6.poincareConjectureTopologicalThree
#print axioms Poincare.Stage6.poincareConjectureSmoothThree
#print axioms Poincare.Longrun.Topology.stage6Target
#print axioms Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree
