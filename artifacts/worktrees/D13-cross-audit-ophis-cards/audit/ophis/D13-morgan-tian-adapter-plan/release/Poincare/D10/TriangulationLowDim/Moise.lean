/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D10-triangulation-low-dim)
-/
import Poincare.D10.TriangulationLowDim.Models
import Poincare.Longrun.Topology.CompactThreeManifold

/-!
# Triangulability of compact manifolds: the Moise target

This file contains the **statement-only** targets that the explicit low-dimensional
triangulations of `Poincare.D10.TriangulationLowDim.Models` do *not* reach:

* `MoiseTriangulationTheorem` — every compact smooth `3`-manifold admits a finite
  triangulation (Moise, 1952);
* `HeawoodTorusVertexBound` — a closed surface triangulation with `χ = 0` has at least
  `7` vertices, so the `7`-vertex torus triangulation is minimal.

Both are `def`s of type `Prop`.  They are **not proved here and not postulated**: there is
no `axiom`, no `theorem` asserting them, and therefore no extra logical strength is added
to the development.  They are recorded as the precise remaining gap.  In particular

* `AdmitsFiniteTriangulation` is a genuine mathematical predicate, defined by asking for a
  homeomorphism from the geometric realisation of an explicit finite complex;
* `admitsFiniteTriangulation_realization` proves the *positive* direction that the
  realisation of every finite complex admits such a triangulation (by the identity
  homeomorphism), so the predicate is not vacuous;
* `moiseTriangulationTheorem_compactThreeManifold` is a **checked** reduction: the raw
  statement implies the version phrased with the project's bundled interface
  `Poincare.Longrun.Topology.CompactThreeManifold`.

## The geometric realisation

For a finite vertex type `Fin n`, the realisation of `K` is the subspace of the standard
simplex of `Fin n → ℝ` consisting of the nonnegative points of sum `1` whose support is
contained in a face.  Because the face family is closed downwards, this is the usual
"union of the closed simplices on the faces".

Restricting the vertex type to `Fin n` loses no generality: any finite abstract
simplicial complex can be relabelled along a bijection of its vertex set with `Fin n`.
-/

open scoped Manifold ContDiff Topology ENNReal

open Poincare.Longrun.Topology

namespace Poincare

namespace D10

namespace TriangulationLowDim

open FiniteAbstractSimplicialComplex

variable {n : ℕ}

/-- The **geometric realisation** of a finite abstract simplicial complex `K` on `Fin n`,
as a subset of the standard simplex of `Fin n → ℝ`: nonnegative points of total mass `1`
whose support is contained in a face of `K`.

(The support is described by the condition `x v ≠ 0 → v ∈ s` rather than as a `Finset`
so that no decidability of equality on `ℝ` is required.) -/
def realizationSet (K : FiniteAbstractSimplicialComplex (Fin n)) : Set (Fin n → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v = 1) ∧ ∃ s ∈ K.faces, ∀ v, x v ≠ 0 → v ∈ s}

/-- The **geometric realisation** of `K`, as a topological space: the subtype of the
standard simplex carried by `realizationSet`, with the subspace topology. -/
abbrev GeometricRealization (K : FiniteAbstractSimplicialComplex (Fin n)) : Type :=
  {x : Fin n → ℝ // x ∈ realizationSet K}

/-- `K` **triangulates** a topological space `X` if the geometric realisation of `K` is
homeomorphic to `X`. -/
def Triangulates (K : FiniteAbstractSimplicialComplex (Fin n)) (X : Type*) [TopologicalSpace X] :
    Prop :=
  Nonempty (GeometricRealization K ≃ₜ X)

/-- A topological space **admits a finite triangulation** if it is homeomorphic to the
geometric realisation of some finite abstract simplicial complex.  The vertex set may be
taken to be `Fin n` without loss of generality. -/
def AdmitsFiniteTriangulation (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, ∃ K : FiniteAbstractSimplicialComplex (Fin n), Triangulates K X

/-- **Positive sanity check.**  Every geometric realisation of a finite complex is
triangulated by that complex, via the identity homeomorphism.  This shows that
`AdmitsFiniteTriangulation` is not vacuous. -/
theorem triangulates_self (K : FiniteAbstractSimplicialComplex (Fin n)) :
    Triangulates K (GeometricRealization K) :=
  ⟨Homeomorph.refl _⟩

/-- **Positive sanity check.**  The geometric realisation of any finite abstract
simplicial complex admits a finite triangulation. -/
theorem admitsFiniteTriangulation_realization (K : FiniteAbstractSimplicialComplex (Fin n)) :
    AdmitsFiniteTriangulation (GeometricRealization K) :=
  ⟨n, K, triangulates_self K⟩

/-- **Moise's triangulation theorem, statement only.**

Every compact smooth `3`-manifold (Hausdorff, without boundary, modelled on `ℝ³`) admits a
finite triangulation.

This is the target that the current community gap blocks: it is stated here so that the
explicit low-dimensional complexes can be compared against it, but it is deliberately
**not** postulated and **not** proved.  It is a `def` of type `Prop`, so `#print axioms`
stays clean and nothing is added to the trusted base. -/
def MoiseTriangulationTheorem : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace EuclideanThree M] [IsManifold ThreeManifoldModel ∞ M],
    AdmitsFiniteTriangulation M

/-- **Checked reduction.**  `MoiseTriangulationTheorem` implies its version phrased with
the project's bundled interface `Poincare.Longrun.Topology.CompactThreeManifold`.

This is a real (if easy) theorem: the bundled class provides every hypothesis of the raw
statement.  It does not prove the triangulation theorem itself. -/
theorem moiseTriangulationTheorem_compactThreeManifold
    (h : MoiseTriangulationTheorem) (M : Type) [TopologicalSpace M]
    [CompactThreeManifold M] : AdmitsFiniteTriangulation M :=
  h M

/-- **Heawood's vertex bound for `χ = 0`, statement only.**

Any closed surface triangulation (every edge in exactly two triangles, vertex links
`2`-regular) with Euler characteristic `0` has at least `7` vertices.  Applied to `torus7`,
for which `torus7_vertices_card` and `torus7_isClosedSurface` are checked, this is the
statement that the `7`-vertex torus triangulation is *minimal*.

Recorded for the same reason as `MoiseTriangulationTheorem`: it is a `def` of type `Prop`,
not a postulate, and it is not proved in this task. -/
def HeawoodTorusVertexBound : Prop :=
  ∀ (n : ℕ) (K : FiniteAbstractSimplicialComplex (Fin n)),
    K.IsClosedSurface → K.eulerChar = 0 → 7 ≤ K.vertices.card

end TriangulationLowDim

end D10

end Poincare
