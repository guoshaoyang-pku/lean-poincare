/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D10-triangulation-low-dim)
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Tactic

/-!
# Finite abstract simplicial complexes

This file fixes the combinatorial notion of a **finite abstract simplicial complex** that
the rest of `Poincare.D10.TriangulationLowDim` is built on, together with its Euler
characteristic.  Everything here is *unconditional*: there are no postulates, no holes and
no kernel bypasses.

## Design notes

A complex on a vertex type `V` is a finite family `faces : Finset (Finset V)` of *finite
vertex sets* which is closed downwards under taking subsets.  The closure axiom is stored
in the form

`∀ s ∈ faces, s.powerset ⊆ faces`

rather than the more usual `∀ s t, s ∈ faces → t ⊆ s → t ∈ faces`.  The two are equivalent
(`mem_of_subset` below recovers the usual form), but the `powerset` form is a *bounded*
quantifier, hence decidable for a concrete `faces`: it is exactly what lets each of the
explicit triangulations in `Poincare.D10.TriangulationLowDim.Models` discharge the axiom by
computation (`decide`), with no appeal to any classical choice principle inside the proof
term.

## Euler characteristic

`eulerChar K = ∑ s ∈ K.faces, (-1) ^ (dim s)` where the sum runs over the **nonempty**
faces and `dim s = s.card - 1`.  Equivalently `χ = ∑_{i ≥ 0} (-1)^i f_i` with `f_i` the
number of `i`-dimensional faces, which is the topological Euler characteristic of the
geometric realisation.  The empty face is excluded because it would contribute the `i = -1`
term of the *reduced* Euler characteristic; `eulerChar_eq_sum` shows that the empty face
contributes `0` to the plain sum.
-/

open Finset

universe u

namespace Poincare

namespace D10

namespace TriangulationLowDim

variable {V : Type u}

/-- A **finite abstract simplicial complex** on a vertex type `V`: a finite family of
finite vertex sets, closed downwards under taking subsets.

The vertex set is not part of the structure; it is recovered as `vertices` (the union of
all faces), and every face is a subset of it (`face_subset_vertices`). -/
structure FiniteAbstractSimplicialComplex (V : Type u) [DecidableEq V] where
  /-- The faces of the complex, as a finset of finite vertex sets. -/
  faces : Finset (Finset V)
  /-- **Downward closure**, in the finitely checkable `powerset` form: every subset of a
  face is again a face.  See `mem_of_subset` for the usual formulation. -/
  downward_closed : ∀ s ∈ faces, s.powerset ⊆ faces

namespace FiniteAbstractSimplicialComplex

variable [DecidableEq V]

/-- The usual formulation of the closure axiom: a subset of a face is a face. -/
theorem mem_of_subset (K : FiniteAbstractSimplicialComplex V) {s t : Finset V}
    (hs : s ∈ K.faces) (ht : t ⊆ s) : t ∈ K.faces :=
  K.downward_closed s hs (mem_powerset.mpr ht)

/-- A nonempty complex contains the empty face (it is a subset of any face). -/
theorem empty_mem_of_nonempty (K : FiniteAbstractSimplicialComplex V) (h : K.faces.Nonempty) :
    ∅ ∈ K.faces := by
  obtain ⟨s, hs⟩ := h
  exact K.mem_of_subset hs (empty_subset s)

/-- The **vertex set** of a complex: the union of all of its faces. -/
def vertices (K : FiniteAbstractSimplicialComplex V) : Finset V :=
  K.faces.biUnion id

@[simp]
theorem mem_vertices (K : FiniteAbstractSimplicialComplex V) {v : V} :
    v ∈ K.vertices ↔ ∃ s ∈ K.faces, v ∈ s := by
  simp [vertices]

/-- Every face is a subset of the vertex set. -/
theorem face_subset_vertices (K : FiniteAbstractSimplicialComplex V) {s : Finset V}
    (hs : s ∈ K.faces) : s ⊆ K.vertices := by
  intro v hv
  rw [mem_vertices]
  exact ⟨s, hs, hv⟩

/-- The number of `i`-dimensional faces, i.e. the `i`-th entry of the `f`-vector.
(`fVector K 0` is the number of vertices, `fVector K 1` the number of edges, …) -/
def fVector (K : FiniteAbstractSimplicialComplex V) (i : ℕ) : ℕ :=
  (K.faces.filter fun s => s.card = i + 1).card

/-- The **Euler characteristic** of a finite abstract simplicial complex:
`χ = ∑_{i ≥ 0} (-1)^i f_i`, the alternating sum of the numbers of nonempty faces by
dimension.  Written as a sum over the faces themselves, with `dim s = s.card - 1`. -/
def eulerChar (K : FiniteAbstractSimplicialComplex V) : ℤ :=
  ∑ s ∈ K.faces.filter (fun s => s.Nonempty), (-1 : ℤ) ^ (s.card - 1)

/-- Unfolding lemma for `eulerChar`. -/
theorem eulerChar_def (K : FiniteAbstractSimplicialComplex V) :
    K.eulerChar
      = ∑ s ∈ K.faces.filter (fun s => s.Nonempty), (-1 : ℤ) ^ (s.card - 1) :=
  rfl

/-- The empty face contributes `0` to the alternating sum, so `eulerChar` can be written
as a sum over *all* faces.  This makes the exclusion of `∅` in the definition explicit. -/
theorem eulerChar_eq_sum (K : FiniteAbstractSimplicialComplex V) :
    K.eulerChar
      = ∑ s ∈ K.faces, (if s = ∅ then 0 else (-1 : ℤ) ^ (s.card - 1)) := by
  rw [eulerChar]
  conv_lhs => rw [sum_filter]
  refine sum_congr rfl fun s _ => ?_
  by_cases h : s.Nonempty
  · simp [h, h.ne_empty]
  · have h' : s = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [h']

/-- A complex is **two-dimensional** if all of its faces have at most three vertices. -/
def IsTwoDimensional (K : FiniteAbstractSimplicialComplex V) : Prop :=
  ∀ s ∈ K.faces, s.card ≤ 3

/-- The **link neighbours** of a vertex `v`: the vertices joined to `v` by an edge. -/
def linkNeighbors (K : FiniteAbstractSimplicialComplex V) (v : V) : Finset V :=
  (K.faces.filter fun t => t.card = 2 ∧ v ∈ t).biUnion fun t => t.erase v

/-- A complex is a **closed surface complex** if it is two-dimensional, every edge is
contained in exactly two triangles, and the link of every vertex is 2-regular (hence a
disjoint union of cycles).  Here `w` and `u` are joined in the link of `v` exactly when
`{v, w, u}` is a triangle of the complex. -/
def IsClosedSurface (K : FiniteAbstractSimplicialComplex V) : Prop :=
  K.IsTwoDimensional ∧
    (∀ s ∈ K.faces, s.card = 2 →
      (K.faces.filter fun t => s ⊆ t ∧ t.card = 3).card = 2) ∧
    (∀ v ∈ K.vertices, ∀ w ∈ K.linkNeighbors v,
      ((K.linkNeighbors v).filter fun u => u ≠ w ∧ {v, w, u} ∈ K.faces).card = 2)

/-- A complex is a **closed curve complex** if all faces have at most two vertices and
every vertex lies in exactly two edges. -/
def IsClosedCurve (K : FiniteAbstractSimplicialComplex V) : Prop :=
  (∀ s ∈ K.faces, s.card ≤ 2) ∧
    (∀ s ∈ K.faces, s.card = 1 →
      (K.faces.filter fun t => s ⊆ t ∧ t.card = 2).card = 2)

/-- `IsTwoDimensional` is a decidable predicate, so concrete complexes can be checked by
computation. -/
instance decidableIsTwoDimensional (K : FiniteAbstractSimplicialComplex V) :
    Decidable K.IsTwoDimensional :=
  inferInstanceAs (Decidable (∀ s ∈ K.faces, s.card ≤ 3))

/-- `IsClosedSurface` is a decidable predicate. -/
instance decidableIsClosedSurface (K : FiniteAbstractSimplicialComplex V) :
    Decidable K.IsClosedSurface :=
  inferInstanceAs (Decidable (K.IsTwoDimensional ∧
    (∀ s ∈ K.faces, s.card = 2 →
      (K.faces.filter fun t => s ⊆ t ∧ t.card = 3).card = 2) ∧
    (∀ v ∈ K.vertices, ∀ w ∈ K.linkNeighbors v,
      ((K.linkNeighbors v).filter fun u => u ≠ w ∧ {v, w, u} ∈ K.faces).card = 2)))

/-- `IsClosedCurve` is a decidable predicate. -/
instance decidableIsClosedCurve (K : FiniteAbstractSimplicialComplex V) :
    Decidable K.IsClosedCurve :=
  inferInstanceAs (Decidable ((∀ s ∈ K.faces, s.card ≤ 2) ∧
    (∀ s ∈ K.faces, s.card = 1 →
      (K.faces.filter fun t => s ⊆ t ∧ t.card = 2).card = 2)))

/-- The **facets** of a complex are its maximal faces, i.e. the faces not strictly
contained in another face. -/
def facets (K : FiniteAbstractSimplicialComplex V) : Finset (Finset V) :=
  K.faces.filter fun s => ∀ t ∈ K.faces, s ⊆ t → t ⊆ s

end FiniteAbstractSimplicialComplex

namespace FiniteAbstractSimplicialComplex

variable [DecidableEq V]

/-- **The complex generated by a family of facets**: the union of the power sets of the
given vertex sets.  Downward closure is automatic, so this is the preferred way to build
concrete complexes from a list of maximal simplices. -/
def ofFacets (facets : Finset (Finset V)) : FiniteAbstractSimplicialComplex V where
  faces := facets.biUnion Finset.powerset
  downward_closed := by
    intro s hs t ht
    rw [mem_biUnion] at hs ⊢
    obtain ⟨f, hf, hsf⟩ := hs
    exact ⟨f, hf,
      mem_powerset.mpr (Subset.trans (mem_powerset.mp ht) (mem_powerset.mp hsf))⟩

@[simp]
theorem mem_ofFacets {facets : Finset (Finset V)} {s : Finset V} :
    s ∈ (ofFacets facets).faces ↔ ∃ f ∈ facets, s ⊆ f := by
  simp [ofFacets]

/-- A face of `ofFacets facets` is a subset of some facet. -/
theorem subset_of_mem_ofFacets {facets : Finset (Finset V)} {s : Finset V}
    (hs : s ∈ (ofFacets facets).faces) : ∃ f ∈ facets, s ⊆ f :=
  mem_ofFacets.mp hs

/-- Generating complexes is monotone in the facet family. -/
theorem ofFacets_mono {facets facets' : Finset (Finset V)} (h : facets ⊆ facets') :
    (ofFacets facets).faces ⊆ (ofFacets facets').faces := by
  intro s hs
  rw [mem_ofFacets] at hs ⊢
  obtain ⟨f, hf, hsf⟩ := hs
  exact ⟨f, h hf, hsf⟩

/-- The vertices of a generated complex are exactly the vertices occurring in its
facets. -/
theorem vertices_ofFacets (facets : Finset (Finset V)) :
    (ofFacets facets).vertices = facets.biUnion id := by
  ext v
  simp only [mem_vertices, mem_ofFacets, mem_biUnion, id_eq]
  constructor
  · rintro ⟨s, ⟨f, hf, hsf⟩, hvs⟩
    exact ⟨f, hf, hsf hvs⟩
  · rintro ⟨f, hf, hvf⟩
    exact ⟨f, ⟨f, hf, subset_rfl⟩, hvf⟩

end FiniteAbstractSimplicialComplex

/-! ## Bridge to mathlib's `PreAbstractSimplicialComplex`

Mathlib's `PreAbstractSimplicialComplex ι` stores its faces as a `Set (Finset ι)` of
*nonempty* finsets, closed downwards for nonempty subsets; `AbstractSimplicialComplex ι`
additionally contains every singleton.  A finite complex in the sense of this file is
*finite* (its faces are a `Finset`), which is what makes the computations below possible,
and it may or may not contain the empty face.  Forgetting the empty face therefore gives a
mathlib `PreAbstractSimplicialComplex`, and if in addition all singletons are faces one
gets a mathlib `AbstractSimplicialComplex`. -/

variable [DecidableEq V]

/-- Forget the empty face of a finite complex: its nonempty faces form a mathlib
`PreAbstractSimplicialComplex`. -/
def FiniteAbstractSimplicialComplex.toPreAbstractSimplicialComplex
    (K : FiniteAbstractSimplicialComplex V) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K.faces ∧ s.Nonempty}
  isRelLowerSet_faces := fun _ ha =>
    ⟨ha.2, fun _ hba hb => ⟨K.mem_of_subset ha.1 hba, hb⟩⟩

/-- A finite complex all of whose singletons are faces yields a mathlib
`AbstractSimplicialComplex`. -/
def FiniteAbstractSimplicialComplex.toMathlibAbstractSimplicialComplex
    (K : FiniteAbstractSimplicialComplex V)
    (h : ∀ v : V, ({v} : Finset V) ∈ K.faces) : AbstractSimplicialComplex V where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex
  singleton_mem v := ⟨h v, Finset.singleton_nonempty v⟩

@[simp]
theorem FiniteAbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex
    (K : FiniteAbstractSimplicialComplex V) {s : Finset V} :
    s ∈ K.toPreAbstractSimplicialComplex ↔ s ∈ K.faces ∧ s.Nonempty :=
  Iff.rfl

end TriangulationLowDim

end D10

end Poincare
