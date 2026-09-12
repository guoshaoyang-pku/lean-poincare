/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Poincare.D12.TriangulationTopology.SphereGluing
import Poincare.Longrun.Topology.Basic

/-!
# Poincare.D12.TriangulationTopology.Downstream

Downstream use of the gluing theorems for **sphere recognition**: the concrete
homeomorphism realizing `𝕊³` (the model space `Poincare.Longrun.Topology.SphereThree`
targeted by `Poincare.Stage6.poincareConjectureTopologicalThree`) as two `3`-disks
glued along their common boundary `2`-sphere, together with dimension, compactness and
nonemptiness audits of every space involved.

This is the "gluing lemma needed by sphere recognition": each spherical piece `S³/Γᵢ`
of the finite-extinction decomposition is a quotient of the space constructed here.
-/

noncomputable section

open scoped Topology

namespace Poincare.D12.TriangulationTopology

/-! ## Dimension audit of the model spaces -/

/-- `Sphere 3 = 𝕊³ ⊂ ℝ⁴` is definitionally the sphere-recognition model space
`Poincare.Longrun.Topology.SphereThree`. -/
theorem sphereThree_eq_sphere3 :
    Poincare.Longrun.Topology.SphereThree = Sphere 3 :=
  rfl

/-- `∂(Disk 3) = Sphere 2 = S² ⊂ ℝ³`: the boundary of the `3`-disk is the `2`-sphere
in `ℝ³`. -/
theorem disk3_boundary_eq_sphere2 :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 = Sphere 2 :=
  rfl

/-- `Disk 3 = D³ ⊂ ℝ³`, `Disk 4 = D⁴ ⊂ ℝ⁴`.  Shapes only. -/
example : Disk 3 = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := rfl
example : Disk 4 = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 := rfl

/-! ## Compactness / nonemptiness audit of the quotients -/

/-- The cone quotient is compact (quotient of a compact cylinder). -/
example (n : ℕ) : CompactSpace (ConeQuot n) := inferInstance

/-- The suspension quotient is compact. -/
example (n : ℕ) : CompactSpace (SuspQuot n) := inferInstance

/-- The double-disk quotient is compact. -/
example (n : ℕ) : CompactSpace (DoubleDiskQuot n) := inferInstance

/-- **Nonemptiness (explicit witness).** The cone quotient contains the vertex class. -/
instance coneQuotNonempty (n : ℕ) : Nonempty (ConeQuot n) := by
  refine ⟨Quot.mk _ (Classical.choice (sphereNonempty n), ⟨0, by norm_num⟩)⟩

/-- **Nonemptiness (explicit witness).** The suspension quotient contains the class of
any point of the cylinder. -/
instance suspQuotNonempty (n : ℕ) : Nonempty (SuspQuot n) := by
  refine ⟨Quot.mk _ (Classical.choice (sphereNonempty n), ⟨0, by norm_num⟩)⟩

/-- **Nonemptiness (explicit witness).** The double-disk quotient contains the class of
`inl 0`. -/
instance doubleDiskQuotNonempty (n : ℕ) : Nonempty (DoubleDiskQuot n) := by
  refine ⟨Quot.mk _ (Sum.inl (0 : Disk (n + 1)))⟩

/-! ## The sphere-recognition gluing homeomorphism -/

/-- **Downstream use of Theorem 3.** The sphere-recognition target `𝕊³`
(`Poincare.Longrun.Topology.SphereThree`) is homeomorphic to two `3`-disks
(`Disk 3 ⊂ ℝ³`) glued along their common boundary `2`-sphere (`Sphere 2 ⊂ ℝ³`):
`𝕊³ = D³ ∪_{S²} D³`. -/
def sphereThreeGluedDisks : DoubleDiskQuot 2 ≃ₜ Poincare.Longrun.Topology.SphereThree :=
  (doubleDiskQuotHomeoSphere 2 : DoubleDiskQuot 2 ≃ₜ Sphere 3)

/-- **Downstream use of Theorem 2.** `𝕊³` is the suspension of `S²` (double cone on
`S²`). -/
def sphereThreeSuspension : SuspQuot 2 ≃ₜ Poincare.Longrun.Topology.SphereThree :=
  (suspQuotHomeoSphere 2 : SuspQuot 2 ≃ₜ Sphere 3)

/-- **Downstream use of Theorem 1.** The cone over `S²` is the `3`-disk `D³ ⊂ ℝ³`. -/
def coneOverSphere2HomeoDisk3 : ConeQuot 2 ≃ₜ Disk 3 :=
  coneQuotHomeoDisk 2

/-- The target `𝕊³` is nonempty (from the nonempty gluing quotient). -/
example : Nonempty Poincare.Longrun.Topology.SphereThree :=
  Nonempty.map sphereThreeGluedDisks (doubleDiskQuotNonempty 2)

/-- The target `𝕊³` is compact (from the compact gluing quotient, a quotient of a
compact space). -/
example : CompactSpace Poincare.Longrun.Topology.SphereThree :=
  Homeomorph.compactSpace sphereThreeGluedDisks

/-- The target `𝕊³` is T2 (subtype of `ℝ⁴`). -/
example : T2Space Poincare.Longrun.Topology.SphereThree := inferInstance

end Poincare.D12.TriangulationTopology
