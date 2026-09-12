/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D10-triangulation-low-dim)
-/
import Poincare.D10.TriangulationLowDim.Complex

/-!
# Explicit triangulations of low-dimensional manifolds

This file builds four explicit finite abstract simplicial complexes and verifies, **by
computation alone** (`decide`), that

* the downward-closure axiom holds for each of them (it is checked when the structure is
  elaborated, since the closure field is a bounded/decidable proposition);
* their face counts, `f`-vectors and Euler characteristics are the expected ones;
* the surface/curve conditions hold (each edge in exactly two triangles, vertex links
  `2`-regular; each vertex of the circle in exactly two edges).

| complex | carrier | `f`-vector | `χ` |
| --- | --- | --- | --- |
| `triangleDisk` | closed triangle `Δ²` (a disk) | `(3, 3, 1)` | `1` |
| `circleS1` | boundary of a triangle, `S¹` | `(3, 3)` | `0` |
| `tetrahedronBoundary` | boundary of a tetrahedron, `S²` | `(4, 6, 4)` | `2` |
| `octahedronBoundary` | boundary of an octahedron, `S²` | `(6, 12, 8)` | `2` |
| `torus7` | `7`-vertex torus triangulation, `T²` | `(7, 21, 14)` | `0` |

## A note on the value of `χ` for `S¹`

The Euler characteristic of the circle is `0` (`χ = V - E = 3 - 3`), and `circleS1_eulerChar`
below proves exactly that.  The value `1` that one might associate with "the triangle" is
the Euler characteristic of the **filled** triangle `Δ²`, which is a disk and not a circle;
it is realised here as `triangleDisk_eulerChar`.  Both computations are unconditional.

## The `7`-vertex torus

`torus7` is the Möbius–Császár style minimal triangulation of the torus: with vertices
`ℤ/7`, the `14` facets are the two cyclic families

* `{i, i+1, i+3}` and
* `{i, i+2, i+3}`,

each family being a `(7,3,1)` difference family; together they use each of the `21` pairs
exactly twice, so `7 - 21 + 14 = 0`.  `torus7_isClosedSurface` verifies the surface
conditions and `torus7_linkNeighbors_card` shows every vertex link is `2`-regular on `6`
vertices.  The number `7` is the minimal possible number of vertices of a torus
triangulation (Heawood bound); that optimality statement is recorded, unproved, as
`HeawoodTorusVertexBound` in `Poincare.D10.TriangulationLowDim.Moise`.
-/

-- The largest computations below (the `7`-vertex torus, whose `14` facets generate a
-- `43`-face complex) need more than the default recursion depth budget of the elaborator.
set_option maxRecDepth 8000

open Finset

namespace Poincare

namespace D10

namespace TriangulationLowDim

open FiniteAbstractSimplicialComplex

/-! ## The closed triangle `Δ²` (a disk) -/

/-- The **closed triangle** `Δ²`, i.e. the full `2`-simplex on `{0, 1, 2}`: the complex of
*all* subsets of `{0, 1, 2}`.  This is a triangulated disk, and its Euler characteristic
is `1`. -/
def triangleDisk : FiniteAbstractSimplicialComplex (Fin 3) where
  faces := (Finset.univ : Finset (Fin 3)).powerset
  downward_closed := by decide

/-- **The face-family (downward-closure) axiom for `Δ²`**, restated as a named theorem.
The proof is the structure field, which was discharged by computation. -/
theorem triangleDisk_downward_closed :
    ∀ s ∈ triangleDisk.faces, s.powerset ⊆ triangleDisk.faces :=
  triangleDisk.downward_closed

/-- `Δ²` has `8` faces (`1 + 3 + 3 + 1`). -/
theorem triangleDisk_faces_card : triangleDisk.faces.card = 8 := by decide

/-- `Δ²` has `3` vertices. -/
theorem triangleDisk_vertices_card : triangleDisk.vertices.card = 3 := by decide

theorem triangleDisk_fVector_zero : triangleDisk.fVector 0 = 3 := by decide
theorem triangleDisk_fVector_one : triangleDisk.fVector 1 = 3 := by decide
theorem triangleDisk_fVector_two : triangleDisk.fVector 2 = 1 := by decide

/-- **`χ(Δ²) = 3 - 3 + 1 = 1`.** -/
theorem triangleDisk_eulerChar : triangleDisk.eulerChar = 1 := by decide

/-- The `f`-vector form of `triangleDisk_eulerChar`: `χ = f₀ - f₁ + f₂`. -/
theorem triangleDisk_eulerChar_eq_fVector :
    triangleDisk.eulerChar
      = (triangleDisk.fVector 0 : ℤ) - (triangleDisk.fVector 1 : ℤ)
        + (triangleDisk.fVector 2 : ℤ) := by decide

/-! ## The circle `S¹` as the boundary of a triangle -/

/-- The **boundary of a triangle**: the `1`-dimensional cycle on `{0, 1, 2}` with the
three edges `{0,1}`, `{1,2}`, `{0,2}`.  Its geometric realisation is the circle `S¹`. -/
def circleS1 : FiniteAbstractSimplicialComplex (Fin 3) where
  faces := ({∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3)))
  downward_closed := by decide

/-- **The face-family (downward-closure) axiom for `S¹`**, restated as a named theorem. -/
theorem circleS1_downward_closed :
    ∀ s ∈ circleS1.faces, s.powerset ⊆ circleS1.faces :=
  circleS1.downward_closed

/-- `S¹` has `7` faces (`∅`, `3` vertices, `3` edges). -/
theorem circleS1_faces_card : circleS1.faces.card = 7 := by decide

/-- `S¹` has `3` vertices. -/
theorem circleS1_vertices_card : circleS1.vertices.card = 3 := by decide

theorem circleS1_fVector_zero : circleS1.fVector 0 = 3 := by decide
theorem circleS1_fVector_one : circleS1.fVector 1 = 3 := by decide
theorem circleS1_fVector_two : circleS1.fVector 2 = 0 := by decide

/-- **`χ(S¹) = 3 - 3 = 0`**, the Euler characteristic of the circle. -/
theorem circleS1_eulerChar : circleS1.eulerChar = 0 := by decide

/-- The `f`-vector form of `circleS1_eulerChar`. -/
theorem circleS1_eulerChar_eq_fVector :
    circleS1.eulerChar
      = (circleS1.fVector 0 : ℤ) - (circleS1.fVector 1 : ℤ) := by decide

/-- The boundary of a triangle is a closed curve. -/
theorem circleS1_isClosedCurve : circleS1.IsClosedCurve := by decide

/-- Every vertex of `circleS1` spans a face, so `circleS1` restricts to a mathlib
`AbstractSimplicialComplex`. -/
theorem circleS1_singleton_mem :
    ∀ v : Fin 3, ({v} : Finset (Fin 3)) ∈ circleS1.faces := by decide

/-! ## The `2`-sphere as the boundary of a tetrahedron -/

/-- The **boundary of a tetrahedron**: all proper subsets of `{0,1,2,3}` of size at most
`3`.  This is a triangulation of `S²` with `4` vertices, `6` edges and `4` triangles. -/
def tetrahedronBoundary : FiniteAbstractSimplicialComplex (Fin 4) where
  faces := ((Finset.univ : Finset (Fin 4)).powerset).filter (fun s => s.card ≤ 3)
  downward_closed := by decide

/-- **The face-family (downward-closure) axiom for the tetrahedron boundary.** -/
theorem tetrahedronBoundary_downward_closed :
    ∀ s ∈ tetrahedronBoundary.faces, s.powerset ⊆ tetrahedronBoundary.faces :=
  tetrahedronBoundary.downward_closed

/-- The tetrahedron boundary has `15` faces (`1 + 4 + 6 + 4`). -/
theorem tetrahedronBoundary_faces_card : tetrahedronBoundary.faces.card = 15 := by decide

/-- The tetrahedron boundary has `4` vertices. -/
theorem tetrahedronBoundary_vertices_card : tetrahedronBoundary.vertices.card = 4 := by decide

theorem tetrahedronBoundary_fVector_zero : tetrahedronBoundary.fVector 0 = 4 := by decide
theorem tetrahedronBoundary_fVector_one : tetrahedronBoundary.fVector 1 = 6 := by decide
theorem tetrahedronBoundary_fVector_two : tetrahedronBoundary.fVector 2 = 4 := by decide

/-- **`χ(S²) = 4 - 6 + 4 = 2`** for the tetrahedron boundary. -/
theorem tetrahedronBoundary_eulerChar : tetrahedronBoundary.eulerChar = 2 := by decide

/-- The `f`-vector form of `tetrahedronBoundary_eulerChar`. -/
theorem tetrahedronBoundary_eulerChar_eq_fVector :
    tetrahedronBoundary.eulerChar
      = (tetrahedronBoundary.fVector 0 : ℤ) - (tetrahedronBoundary.fVector 1 : ℤ)
        + (tetrahedronBoundary.fVector 2 : ℤ) := by decide

/-- The tetrahedron boundary is a closed surface. -/
theorem tetrahedronBoundary_isClosedSurface :
    tetrahedronBoundary.IsClosedSurface := by decide

/-! ## The `2`-sphere as an octahedron -/

/-- The `8` facets of the octahedron: for each choice of one vertex from each of the three
antipodal pairs `{0,1}`, `{2,3}`, `{4,5}`. -/
def octahedronFacets : Finset (Finset (Fin 6)) :=
  ({ {0, 2, 4}, {1, 2, 4}, {0, 3, 4}, {1, 3, 4},
     {0, 2, 5}, {1, 2, 5}, {0, 3, 5}, {1, 3, 5} } : Finset (Finset (Fin 6)))

/-- The **boundary of an octahedron**: the complex generated by the `8` triangular facets
`octahedronFacets`.  This is a triangulation of `S²` with `6` vertices, `12` edges and
`8` triangles. -/
def octahedronBoundary : FiniteAbstractSimplicialComplex (Fin 6) :=
  ofFacets octahedronFacets

/-- **The face-family (downward-closure) axiom for the octahedron boundary.** -/
theorem octahedronBoundary_downward_closed :
    ∀ s ∈ octahedronBoundary.faces, s.powerset ⊆ octahedronBoundary.faces :=
  octahedronBoundary.downward_closed

/-- The octahedron complex has `27` faces (`1 + 6 + 12 + 8`). -/
theorem octahedronBoundary_faces_card : octahedronBoundary.faces.card = 27 := by decide

/-- The octahedron complex has `6` vertices. -/
theorem octahedronBoundary_vertices_card : octahedronBoundary.vertices.card = 6 := by decide

theorem octahedronBoundary_fVector_zero : octahedronBoundary.fVector 0 = 6 := by decide
theorem octahedronBoundary_fVector_one : octahedronBoundary.fVector 1 = 12 := by decide
theorem octahedronBoundary_fVector_two : octahedronBoundary.fVector 2 = 8 := by decide

/-- **`χ(S²) = 6 - 12 + 8 = 2`** for the octahedron. -/
theorem octahedronBoundary_eulerChar : octahedronBoundary.eulerChar = 2 := by decide

/-- The `f`-vector form of `octahedronBoundary_eulerChar`. -/
theorem octahedronBoundary_eulerChar_eq_fVector :
    octahedronBoundary.eulerChar
      = (octahedronBoundary.fVector 0 : ℤ) - (octahedronBoundary.fVector 1 : ℤ)
        + (octahedronBoundary.fVector 2 : ℤ) := by decide

/-- The octahedron boundary is a closed surface. -/
theorem octahedronBoundary_isClosedSurface :
    octahedronBoundary.IsClosedSurface := by decide

/-! ## The torus `T²` with a minimal `7`-vertex triangulation -/

/-- The cyclic family of triples `{i, i+a, i+b}` in `ℤ/7`. -/
def cyclicTriples (a b : Fin 7) : Finset (Finset (Fin 7)) :=
  (Finset.univ : Finset (Fin 7)).image fun i => ({i, i + a, i + b} : Finset (Fin 7))

/-- The `14` facets of the minimal `7`-vertex torus triangulation: the two cyclic families
`{i, i+1, i+3}` and `{i, i+2, i+3}`. -/
def torus7Facets : Finset (Finset (Fin 7)) :=
  cyclicTriples 1 3 ∪ cyclicTriples 2 3

/-- The **minimal `7`-vertex triangulation of the torus**: generated by the `14` facets
`torus7Facets`. -/
def torus7 : FiniteAbstractSimplicialComplex (Fin 7) :=
  ofFacets torus7Facets

/-- **The face-family (downward-closure) axiom for the `7`-vertex torus.** -/
theorem torus7_downward_closed :
    ∀ s ∈ torus7.faces, s.powerset ⊆ torus7.faces :=
  torus7.downward_closed

/-- The `14` facets are pairwise distinct. -/
theorem torus7Facets_card : torus7Facets.card = 14 := by decide

/-- The torus complex has `43` faces (`1 + 7 + 21 + 14`). -/
theorem torus7_faces_card : torus7.faces.card = 43 := by decide

/-- The torus complex has `7` vertices. -/
theorem torus7_vertices_card : torus7.vertices.card = 7 := by decide

/-- The vertex set of `torus7` is all of `Fin 7`. -/
theorem torus7_vertices_eq_univ : torus7.vertices = Finset.univ := by decide

theorem torus7_fVector_zero : torus7.fVector 0 = 7 := by decide
theorem torus7_fVector_one : torus7.fVector 1 = 21 := by decide
theorem torus7_fVector_two : torus7.fVector 2 = 14 := by decide

/-- **`χ(T²) = 7 - 21 + 14 = 0`** for the `7`-vertex torus triangulation. -/
theorem torus7_eulerChar : torus7.eulerChar = 0 := by decide

/-- The `f`-vector form of `torus7_eulerChar`. -/
theorem torus7_eulerChar_eq_fVector :
    torus7.eulerChar
      = (torus7.fVector 0 : ℤ) - (torus7.fVector 1 : ℤ) + (torus7.fVector 2 : ℤ) := by
  decide

/-- Every edge of `torus7` lies in exactly two triangles, making it a closed surface. -/
theorem torus7_isClosedSurface : torus7.IsClosedSurface := by decide

/-- Every vertex of the `7`-vertex torus triangulation has a `6`-element link. -/
theorem torus7_linkNeighbors_card (v : Fin 7) :
    (torus7.linkNeighbors v).card = 6 := by
  fin_cases v <;> decide

/-- Every vertex link of `torus7` is a cycle: it has `6` vertices, each of degree `2`,
where `w` and `u` are joined in the link of `v` exactly when `{v, w, u}` is a triangle. -/
theorem torus7_link_isCycle (v : Fin 7) (w : Fin 7) (hw : w ∈ torus7.linkNeighbors v) :
    ((torus7.linkNeighbors v).filter fun u => u ≠ w ∧ {v, w, u} ∈ torus7.faces).card = 2 :=
  torus7_isClosedSurface.2.2 v (by
    rw [torus7_vertices_eq_univ]
    exact Finset.mem_univ v) w hw

/-- Every vertex of `torus7` spans a face, so `torus7` restricts to a mathlib
`AbstractSimplicialComplex`. -/
theorem torus7_singleton_mem :
    ∀ v : Fin 7, ({v} : Finset (Fin 7)) ∈ torus7.faces := by decide

/-- The `7`-vertex torus triangulation, viewed as a mathlib `AbstractSimplicialComplex`
(via the bridge `FiniteAbstractSimplicialComplex.toMathlibAbstractSimplicialComplex`). -/
def torus7Mathlib : AbstractSimplicialComplex (Fin 7) :=
  torus7.toMathlibAbstractSimplicialComplex torus7_singleton_mem

/-- The bridge preserves faces: a nonempty face of `torus7` is a face of the mathlib
complex `torus7Mathlib`. -/
theorem torus7_mem_torus7Mathlib {s : Finset (Fin 7)} (hs : s ∈ torus7.faces)
    (hne : s.Nonempty) : s ∈ torus7Mathlib :=
  ⟨hs, hne⟩

/-! ## Summary of the computed Euler characteristics -/

/-- **All five computed Euler characteristics in one kernel-checked conjunction.**

The D10 task asks for the values `1, 2, 2, 0`.  Four of them are realised here as

* `1` — the **filled** triangle `Δ²` (a triangulated disk);
* `2` — the tetrahedron boundary `S²`;
* `2` — the octahedron boundary `S²`;
* `0` — the `7`-vertex torus `T²`.

The circle `S¹` (the *boundary* of a triangle) has `χ = 3 - 3 = 0`, not `1`: for a
`1`-dimensional complex `χ = f₀ - f₁`, and the boundary of a triangle has three vertices and
three edges.  The value `1` belongs to the filled triangle, whose face family is a different
complex on the same three vertices.  Both are computed here, so the discrepancy is
explicit and kernel-checked rather than silently absorbed. -/
theorem d10_eulerChar_values :
    triangleDisk.eulerChar = 1 ∧ circleS1.eulerChar = 0 ∧
      tetrahedronBoundary.eulerChar = 2 ∧ octahedronBoundary.eulerChar = 2 ∧
      torus7.eulerChar = 0 :=
  ⟨triangleDisk_eulerChar, circleS1_eulerChar, tetrahedronBoundary_eulerChar,
    octahedronBoundary_eulerChar, torus7_eulerChar⟩

end TriangulationLowDim

end D10

end Poincare
