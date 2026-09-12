/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D11-triangulation-3d)
-/
import Poincare.D11.Triangulation3D.Models
import Poincare.D11.Triangulation3D.Bridge
import Poincare.D11.Triangulation3D.LensFamily

/-!
# Axiom audit of the D11 triangulation files

Every theorem of `Poincare.D11.Triangulation3D` must have an axiom cone contained in
`{propext, Classical.choice, Quot.sound}`.  This file carries out the audit in two ways.

1. It re-prints the axiom sets of the headline theorems with `#print axioms` (below).
2. It runs a **fail-closed programmatic scan**: a `run_cmd` walks *every* constant of the
   namespace `Poincare.D11.Triangulation3D` in the compiled environment, computes its axiom
   cone with `Lean.collectAxioms`, and reports an error for any declaration whose cone leaves
   the allowed set, for any declaration that is an actual `axiom`, and for any `unsafe`
   definition.  Because the harness compile gate runs `lake env lean` on this file with exit
   code as the pass/fail signal, a single violation makes the audit *fail the build* rather
   than merely print a warning.

In particular no `sorryAx`, no project `axiom`, no `unsafe`, no `native_decide`
(`Lean.ofReduceBool`) and no `proof_wanted` can occur in the cone of an audited declaration
without failing this file.
-/

open Poincare.D11.Triangulation3D

/-! ## The headline theorems -/

#check ball3_manifold
#check s3Double_manifold
#check s3Simplex_manifold
#check solidTorus3_manifold
#check lens31_manifold
#check lens21_manifold

#print axioms ball3_manifold
#print axioms s3Double_manifold
#print axioms s3Simplex_manifold
#print axioms solidTorus3_manifold
#print axioms lens31_manifold
#print axioms lens21_manifold

/-! ## The computed numerical invariants -/

#print axioms ball3_fvector
#print axioms s3Double_fvector
#print axioms s3Simplex_fvector
#print axioms solidTorus3_fvector
#print axioms lens31_fvector
#print axioms lens21_fvector

#print axioms ball3_euler
#print axioms s3Double_euler
#print axioms s3Simplex_euler
#print axioms solidTorus3_euler
#print axioms lens31_euler
#print axioms lens21_euler

#print axioms ball3_boundaryChi
#print axioms solidTorus3_boundaryChi

/-! ## Consistency / orientation / closedness of every example -/

#print axioms ball3_consistent
#print axioms ball3_orientationReversing
#print axioms ball3_orientable
#print axioms ball3_connected
#print axioms ball3_notClosed
#print axioms ball3_boundary

#print axioms s3Double_consistent
#print axioms s3Double_orientable
#print axioms s3Double_connected
#print axioms s3Double_closed

#print axioms s3Simplex_partner
#print axioms s3Simplex_consistent
#print axioms s3Simplex_orientable
#print axioms s3Simplex_connected
#print axioms s3Simplex_closed

#print axioms solidTorus3_consistent
#print axioms solidTorus3_orientationReversing
#print axioms solidTorus3_orientable
#print axioms solidTorus3_connected
#print axioms solidTorus3_notClosed
#print axioms solidTorus3_boundary

#print axioms lens31_consistent
#print axioms lens31_orientationReversing
#print axioms lens31_orientable
#print axioms lens31_connected
#print axioms lens31_closed

#print axioms lens21_consistent
#print axioms lens21_orientable
#print axioms lens21_connected
#print axioms lens21_closed

/-! ## The union-find quotient lemmas of the checker -/

#print axioms fastForallMem_iff
#print axioms FacePairing3.PairConnected_mono
#print axioms FacePairing3.mergePair_grow
#print axioms FacePairing3.grow_foldl
#print axioms FacePairing3.mergePair_connected
#print axioms FacePairing3.mergePair_connected_full
#print axioms FacePairing3.foldl_connected
#print axioms FacePairing3.componentsOf_blocks_connected
#print axioms FacePairing3.blocks_disjoint
#print axioms FacePairing3.blocks_disjoint_foldl
#print axioms FacePairing3.same_block_preserved
#print axioms FacePairing3.same_block_of_pair_foldl
#print axioms FacePairing3.same_block_of_pair

/-! ## The bridge to the D10 low-dimensional simplicial-complex layer -/

#print axioms ball3Label_isSimplicial
#print axioms s3SimplexLabel_isSimplicial
#print axioms inducedFaces_downward_closed
#print axioms ball3_induced_faces
#print axioms ball3_fvector_agreement
#print axioms ball3_induced_euler
#print axioms s3Simplex_induced_faces
#print axioms s3Simplex_fvector_agreement
#print axioms s3Simplex_induced_euler

/-! ## The bipyramid lens-space family `lensPQ` -/

#print axioms lensPQ_three_one_glue
#print axioms lensPQ_21_manifold
#print axioms lensPQ_31_manifold
#print axioms lensPQ_41_manifold
#print axioms lensPQ_51_manifold
#print axioms lensPQ_52_manifold
#print axioms lensPQ_21_fvector
#print axioms lensPQ_31_fvector
#print axioms lensPQ_41_fvector
#print axioms lensPQ_51_fvector
#print axioms lensPQ_52_fvector
#print axioms lensPQ_21_euler
#print axioms lensPQ_31_euler
#print axioms lensPQ_41_euler
#print axioms lensPQ_51_euler
#print axioms lensPQ_52_euler

/-! ## Fail-closed programmatic audit over every declaration of the namespace -/

open Lean Elab Command in
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Array Name) := #[]
  let mut declaredAxioms : Array Name := #[]
  let mut unsafeDefs : Array Name := #[]
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if (`Poincare.D11.Triangulation3D).isPrefixOf n then
      count := count + 1
      match ci with
      | .axiomInfo _ => declaredAxioms := declaredAxioms.push n
      | .defnInfo d => if d.safety == .unsafe then unsafeDefs := unsafeDefs.push n
      | _ => pure ()
      let axs ← collectAxioms n
      let extra := axs.filter (fun a => !allowed.contains a)
      if extra.size > 0 then bad := bad.push (n, extra)
  logInfo m!"D11 axiom audit: audited {count} declarations in Poincare.D11.Triangulation3D; \
    axiom-cone violations: {bad.size}; declared axioms: {declaredAxioms.size}; \
    unsafe definitions: {unsafeDefs.size}; allowed cones: propext, Classical.choice, Quot.sound"
  for (n, e) in bad do
    logError m!"AXIOM CONE VIOLATION: {n} uses {e}"
  for n in declaredAxioms do
    logError m!"DECLARED AXIOM IN NAMESPACE: {n}"
  for n in unsafeDefs do
    logError m!"UNSAFE DEFINITION IN NAMESPACE: {n}"
  if bad.size == 0 && declaredAxioms.size == 0 && unsafeDefs.size == 0 then
    logInfo m!"D11 axiom audit PASSED"
