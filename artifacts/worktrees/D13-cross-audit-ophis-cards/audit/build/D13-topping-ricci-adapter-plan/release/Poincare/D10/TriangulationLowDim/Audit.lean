/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D10-triangulation-low-dim)
-/
import Poincare.D10.TriangulationLowDim.Moise

/-!
# Axiom audit for `Poincare.D10.TriangulationLowDim`

This file is the machine-checkable audit trail for the D10 low-dimensional triangulation
island.  Running

```
lake env lean Poincare/D10/TriangulationLowDim/Audit.lean
```

prints the axiom cone of every declaration of the development.  The expected output is
recorded in `longrun/results/D10-triangulation-low-dim.md`; the external checker
`longrun`-side re-parses it and asserts that every cone is contained in

`{propext, Classical.choice, Quot.sound}`,

the three axioms of the ambient mathlib library.  In particular there must be no
`sorryAx`, no project `axiom`, no `unsafe`, no `native_decide` and no `proof_wanted`
anywhere in the cone of an audited declaration.

The two statement-only targets (`MoiseTriangulationTheorem`, `HeawoodTorusVertexBound`)
are `def`s of type `Prop`; printing their types and their axiom cones shows that they are
definitions, not postulates, so the gap they record is not smuggled into the trusted base.
-/

open Poincare.D10.TriangulationLowDim

/-! ## Core complex API -/

#print axioms FiniteAbstractSimplicialComplex.mem_of_subset
#print axioms FiniteAbstractSimplicialComplex.empty_mem_of_nonempty
#print axioms FiniteAbstractSimplicialComplex.mem_vertices
#print axioms FiniteAbstractSimplicialComplex.face_subset_vertices
#print axioms FiniteAbstractSimplicialComplex.eulerChar
#print axioms FiniteAbstractSimplicialComplex.eulerChar_eq_sum
#print axioms FiniteAbstractSimplicialComplex.ofFacets
#print axioms FiniteAbstractSimplicialComplex.mem_ofFacets
#print axioms FiniteAbstractSimplicialComplex.subset_of_mem_ofFacets
#print axioms FiniteAbstractSimplicialComplex.ofFacets_mono
#print axioms FiniteAbstractSimplicialComplex.vertices_ofFacets
#print axioms FiniteAbstractSimplicialComplex.toPreAbstractSimplicialComplex
#print axioms FiniteAbstractSimplicialComplex.toMathlibAbstractSimplicialComplex

/-! ## The face-family (downward-closure) axioms, restated per construction -/

#print axioms triangleDisk_downward_closed
#print axioms circleS1_downward_closed
#print axioms tetrahedronBoundary_downward_closed
#print axioms octahedronBoundary_downward_closed
#print axioms torus7_downward_closed

/-! ## The closed triangle `Δ²` (a disk) -/

#print axioms triangleDisk_faces_card
#print axioms triangleDisk_vertices_card
#print axioms triangleDisk_fVector_zero
#print axioms triangleDisk_fVector_one
#print axioms triangleDisk_fVector_two
#print axioms triangleDisk_eulerChar
#print axioms triangleDisk_eulerChar_eq_fVector

/-! ## The circle `S¹` as the boundary of a triangle -/

#print axioms circleS1_faces_card
#print axioms circleS1_vertices_card
#print axioms circleS1_fVector_zero
#print axioms circleS1_fVector_one
#print axioms circleS1_fVector_two
#print axioms circleS1_eulerChar
#print axioms circleS1_eulerChar_eq_fVector
#print axioms circleS1_isClosedCurve
#print axioms circleS1_singleton_mem

/-! ## The `2`-sphere as the boundary of a tetrahedron -/

#print axioms tetrahedronBoundary_faces_card
#print axioms tetrahedronBoundary_vertices_card
#print axioms tetrahedronBoundary_fVector_zero
#print axioms tetrahedronBoundary_fVector_one
#print axioms tetrahedronBoundary_fVector_two
#print axioms tetrahedronBoundary_eulerChar
#print axioms tetrahedronBoundary_eulerChar_eq_fVector
#print axioms tetrahedronBoundary_isClosedSurface

/-! ## The `2`-sphere as an octahedron -/

#print axioms octahedronBoundary_faces_card
#print axioms octahedronBoundary_vertices_card
#print axioms octahedronBoundary_fVector_zero
#print axioms octahedronBoundary_fVector_one
#print axioms octahedronBoundary_fVector_two
#print axioms octahedronBoundary_eulerChar
#print axioms octahedronBoundary_eulerChar_eq_fVector
#print axioms octahedronBoundary_isClosedSurface

/-! ## The `7`-vertex torus `T²` -/

#print axioms torus7Facets_card
#print axioms torus7_faces_card
#print axioms torus7_vertices_card
#print axioms torus7_vertices_eq_univ
#print axioms torus7_fVector_zero
#print axioms torus7_fVector_one
#print axioms torus7_fVector_two
#print axioms torus7_eulerChar
#print axioms torus7_eulerChar_eq_fVector
#print axioms torus7_isClosedSurface
#print axioms torus7_linkNeighbors_card
#print axioms torus7_link_isCycle
#print axioms torus7_singleton_mem
#print axioms torus7Mathlib
#print axioms torus7_mem_torus7Mathlib
#print axioms d10_eulerChar_values

/-! ## The Moise target and the positive sanity checks -/

#print axioms triangulates_self
#print axioms admitsFiniteTriangulation_realization
#print axioms moiseTriangulationTheorem_compactThreeManifold
#print axioms MoiseTriangulationTheorem
#print axioms HeawoodTorusVertexBound

/-! ## Shape checks: the statement-only targets are `Prop`-valued definitions -/

#check @MoiseTriangulationTheorem
#check @HeawoodTorusVertexBound
#check @AdmitsFiniteTriangulation
#check @Triangulates
#check @GeometricRealization
#check @realizationSet
#print MoiseTriangulationTheorem
#print HeawoodTorusVertexBound
