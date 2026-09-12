/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D11-triangulation-3d)
-/
import Poincare.D11.Triangulation3D.Models
import Poincare.D10.TriangulationLowDim.Complex

/-!
# Bridge: from a labelled face pairing to a D10 finite abstract simplicial complex

This file **reuses the D10 low-dimensional triangulation infrastructure**
(`Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex`, its `fVector` and its
`eulerChar`) and shows how a Δ-complex/face-pairing presentation of the D11 layer induces
such a complex:

* `IsSimplicialLabeling T lab` says that the corners of the tetrahedra carry vertex labels
  which are constant on the corner identifications of the pairing and injective on every
  tetrahedron;
* `inducedComplex lab` is the finite abstract simplicial complex whose faces are the
  downward closures of the labelled tetrahedra (`inducedFaces_downward_closed` discharges
  the closure axiom of the D10 structure);
* for the two **genuinely simplicial** examples (`ball3`, `s3Simplex`) the `f`-vector of the
  induced complex is proved (by computation) to agree with the vertex/edge/face class counts
  of the face pairing, and its D10 Euler characteristic to agree with `eulerChar3`.

The two remaining closed examples (`s3Double`, `lens31`, `lens21`) are *generalized*
triangulations: several tetrahedra share the same vertex set, so they are honestly
Δ-complexes and not simplicial complexes.  For those only the face-pairing layer applies.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096

open Finset

namespace Poincare

namespace D11

namespace Triangulation3D

open FacePairing3
open Poincare.D10.TriangulationLowDim (FiniteAbstractSimplicialComplex)

variable {N : ℕ} {α : Type}

/-- A **simplicial labelling** of a face pairing: a vertex label for every corner which is
constant on the corner identifications and injective on every tetrahedron.  (Marked
`@[reducible]` so that the `Decidable` instance for the conjunction is synthesised and the
concrete labellings below are checked by `decide`.) -/
@[reducible] def IsSimplicialLabeling [DecidableEq α] (T : FacePairing3 N) (lab : Corner N → α) : Prop :=
  (∀ p ∈ T.cornerPairs, lab p.1 = lab p.2) ∧
    (∀ t : Fin N, Function.Injective fun j : Fin 4 => lab ⟨t, j⟩)

/-- The vertex set of a labelled tetrahedron. -/
def facetSet [DecidableEq α] (lab : Corner N → α) (t : Fin N) : Finset α :=
  (Finset.univ : Finset (Fin 4)).image fun j => lab ⟨t, j⟩

/-- The faces of the complex induced by a labelling: the downward closure of the labelled
tetrahedra. -/
def inducedFaces [DecidableEq α] (lab : Corner N → α) : Finset (Finset α) :=
  (Finset.univ : Finset (Fin N)).biUnion fun t => (facetSet lab t).powerset

/-- The induced face family is downward closed (the D10 closure axiom). -/
theorem inducedFaces_downward_closed [DecidableEq α] (lab : Corner N → α) :
    ∀ s ∈ inducedFaces lab, s.powerset ⊆ inducedFaces lab := by
  intro s hs
  rw [inducedFaces, mem_biUnion] at hs
  rcases hs with ⟨t, -, hst⟩
  rw [mem_powerset] at hst
  intro u hu
  rw [inducedFaces, mem_biUnion]
  exact ⟨t, mem_univ _, by
    rw [mem_powerset]
    exact Subset.trans (mem_powerset.mp hu) hst⟩

/-- The **finite abstract simplicial complex induced by a labelled face pairing**. -/
def inducedComplex [DecidableEq α] (lab : Corner N → α) : FiniteAbstractSimplicialComplex α where
  faces := inducedFaces lab
  downward_closed := inducedFaces_downward_closed lab

/-! ## The 3-ball as a labelled tetrahedron -/

/-- The single tetrahedron labelled by its corner index. -/
def ball3Label : Corner 1 → Fin 4 := fun c => c.j

theorem ball3Label_isSimplicial : IsSimplicialLabeling ball3 ball3Label := by decide

/-- The induced complex of a single labelled tetrahedron is the full 3-simplex. -/
theorem ball3_induced_faces :
    (inducedComplex ball3Label).faces = (Finset.univ : Finset (Fin 4)).powerset := by
  decide

/-- The `f`-vector of the induced complex agrees with the class counts of the pairing. -/
theorem ball3_fvector_agreement :
    (inducedComplex ball3Label).fVector 0 = ball3.vertexClasses.card ∧
      (inducedComplex ball3Label).fVector 1 = ball3.edgeClasses.card ∧
      (inducedComplex ball3Label).fVector 2 = ball3.faceClasses.card := by
  decide

/-- The D10 Euler characteristic of the induced complex is the D11 Euler characteristic of
the face pairing. -/
theorem ball3_induced_euler :
    (inducedComplex ball3Label).eulerChar = ball3.eulerChar3 := by decide

/-! ## The boundary of the 4-simplex as a labelled triangulation -/

/-- The vertex label of the corner `(t,j)` of the boundary-of-`Δ⁴` triangulation. -/
def s3SimplexLabel : Corner 5 → Fin 5 := fun c => facetVertex c.t c.j

theorem s3SimplexLabel_isSimplicial : IsSimplicialLabeling s3Simplex s3SimplexLabel := by decide

/-- The induced complex of the boundary-of-`Δ⁴` triangulation is the boundary of the
4-simplex: its facets are exactly the complements of the five vertices. -/
theorem s3Simplex_induced_faces :
    (inducedComplex s3SimplexLabel).faces =
      ((Finset.univ : Finset (Fin 5)).powerset).filter (fun s => s ≠ Finset.univ) := by
  decide

/-- The `f`-vector `(5,10,10,5)` of the induced complex agrees with the class counts of the
face pairing: the triangulation is simplicial. -/
theorem s3Simplex_fvector_agreement :
    (inducedComplex s3SimplexLabel).fVector 0 = s3Simplex.vertexClasses.card ∧
      (inducedComplex s3SimplexLabel).fVector 1 = s3Simplex.edgeClasses.card ∧
      (inducedComplex s3SimplexLabel).fVector 2 = s3Simplex.faceClasses.card ∧
      (inducedComplex s3SimplexLabel).fVector 3 = 5 := by
  decide

/-- The D10 Euler characteristic of the induced complex is the D11 Euler characteristic of
the face pairing (both vanish, as for every closed 3-manifold). -/
theorem s3Simplex_induced_euler :
    (inducedComplex s3SimplexLabel).eulerChar = s3Simplex.eulerChar3 := by decide

end Triangulation3D

end D11

end Poincare
