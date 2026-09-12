/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Poincare.D12.TriangulationTopology.Downstream
import Poincare.D12.TriangulationTopology.CoveringLemma
import Poincare.D12.TriangulationTopology.SimplexBoundary
import Poincare.D12.TriangulationTopology.HemisphereDisk
import Poincare.D12.TriangulationTopology.SimplexCone

/-!
# Poincare.D12.TriangulationTopology.MoiseBranch

**Statement-only** ledger of the remaining nodes of the Moise/smoothing dependency DAG
(see `MOISE_DAG.md` in this directory).  Every `def ... : Prop` below fixes the exact
statement of a named next lemma or named blocker; none of them is a theorem, a postulate,
or a statement stub, and none is used as a hypothesis of any proved theorem.  The three
gluing/realization theorems of `SphereGluing.lean` (which ARE proved) are recorded here
as the discharged DAG nodes (7), (8), (11).

Moise's theorem for arbitrary topological 3-manifolds is a separate task: a triangulated
input or a definition called `Triangulable` is not its proof.  The Moise statement below
is the *weakened* consequence expressible with mathlib objects (existence of a CW
complex structure with `Set.univ` as the total space); full triangulability with unique
PL structure is strictly stronger and is recorded in `MOISE_DAG.md` only.
-/

noncomputable section

open scoped Topology

namespace Poincare.D12.TriangulationTopology

/-- A predicate expressing that a topological space is locally modelled on `ℝⁿ`
(locally homeomorphic to open balls of `EuclideanSpace ℝ (Fin n)`).  A definition of a
predicate, not an assumption of any theorem. -/
def LocallyEuclideanOfDimension (M : Type) [TopologicalSpace M] (n : ℕ) : Prop :=
  ∀ x : M, ∃ U : Set M, x ∈ U ∧ IsOpen U ∧
    Nonempty (↥U ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-! ## Named next lemmas (statements, to be proved in later invocations) -/

/-- **DAG node 5, PROVED** in `CoveringLemma.lean` (was a named next lemma; discharged
2026-09-11).

A covering map from a compact path-connected space onto a simply connected space is a
homeomorphism.  The proved theorem
`coveringOfSimplyConnectedIsHomeo [CompactSpace E] [T2Space X] [PathConnectedSpace E]
[SimplyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p) (hsurj : Surjective p) :
Nonempty (E ≃ₜ X)` is *stronger* than the originally recorded `Bijective` form (which
follows, see the example below).  The proof uses mathlib's path lifting
(`IsCoveringMap.exists_path_lifts`) and `liftPath_apply_one_eq_of_homotopicRel`: a path
joining two points of a fiber projects to a loop that is null-homotopic rel endpoints by
simply-connectedness, so its lift ends where it started; injectivity follows, and
compactness + T₂ give the homeomorphism.  The downstream use for spherical space forms is
`sphericalSpaceFormRecognition` in `AntipodalQuotient.lean`. -/
example {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [CompactSpace E]
    [PathConnectedSpace E] [SimplyConnectedSpace X] [T2Space X]
    (p : E → X) (hp : IsCoveringMap p) (hbij : Function.Bijective p) : Nonempty (E ≃ₜ X) :=
  coveringOfSimplyConnectedIsHomeo p hp hbij.2

/-- **MISSING THEOREM (van Kampen cover criterion, DAG node 6).**

A space covered by two open path-connected simply connected subspaces with path-connected
intersection is simply connected.  This is the van Kampen corollary used both for
`π₁(𝕊ⁿ) = 0` (`n ≥ 2`, via the two stereographic hemispheres) and for the connected-sum
decomposition of sphere recognition.  mathlib pinned rev has no Van Kampen; frenzymath
HatcherLib Ch1 proves a sorry-free version (`simplyConnectedSpace_of_pathConnectedOpenCover`)
at toolchain v4.32.1/mathlib 520045a (recorded port source, Apache-2.0). -/
def vanKampenSimplyConnectedCover : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (A B : Set X),
    IsOpen A → IsOpen B → A ∪ B = Set.univ →
      (PathConnectedSpace ↥A) → (PathConnectedSpace ↥B) → (PathConnectedSpace ↥(A ∩ B)) →
      (SimplyConnectedSpace ↥A) → (SimplyConnectedSpace ↥B) → SimplyConnectedSpace X

/-- **DAG node 9, PROVED** in `SimplexBoundary.lean` (discharged 2026-09-11, this invocation).

The boundary of the standard `(n+1)`-simplex (points with some vertex coordinate equal to
`0`) is homeomorphic to the `n`-sphere.  The proved theorem `simplexBoundaryHomeoSphere n`
carries exactly the statement recorded below (checked by the example); `SimplexBoundary 3 ≃ₜ
𝕊³` is the standard triangulation of the 3-sphere as `|∂Δ⁴|`, and the compactness / T2 /
nonemptiness audits of `∂Δⁿ⁺¹` are proved instances in `SimplexBoundary.lean`.
Together with the proved `doubleDiskQuotHomeoSphere` this closes the triangulation form of
the sphere-recognition gluing input. -/
example (n : ℕ) :
    Nonempty ({x : Convexity.StdSimplex ℝ (Fin (n + 2)) //
      0 ∈ Set.range fun i : Fin (n + 2) => x.weights i} ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨simplexBoundaryHomeoSphere n⟩

/-- **Downstream use.** The boundary of the 4-simplex realizes the sphere-recognition
model space `𝕊³ = Poincare.Longrun.Topology.SphereThree` (definitional via
`sphereThree_eq_sphere3`): the standard triangulation of the 3-sphere as `|∂Δ⁴|`. -/
example : SimplexBoundary 3 ≃ₜ Poincare.Longrun.Topology.SphereThree :=
  (simplexBoundaryHomeoSphere 3 : SimplexBoundary 3 ≃ₜ Sphere 3)

/-- **DAG node 9, second half PROVED** in `SimplexCone.lean` (discharged 2026-09-11).

The standard `(n+1)`-simplex is homeomorphic to the closed `(n+1)`-disk: `Δⁿ⁺¹ ≅ Dⁿ⁺¹`.
The proved theorem `simplexHomeoDisk n` carries exactly the statement recorded below
(checked by the example), by the radial cone-over-boundary form
`Δⁿ⁺¹ ≅ Cone(𝕊ⁿ) ≅ Dⁿ⁺¹`; the literal radial form `Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹)` is
`simplexHomeoBoundaryConeStd`.  Together with `simplexBoundaryHomeoSphere` (first half)
and `coneQuotHomeoDisk` (node 8) this closes DAG node 9 completely. -/
example (n : ℕ) :
    Nonempty (Convexity.StdSimplex ℝ (Fin (n + 2)) ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨simplexHomeoDisk n⟩

/-- **Downstream use.** The tetrahedron `Δ³` realizes the closed 3-ball `D³`: the ball
piece of the sphere-recognition gluing `S³ = D³ ∪_{S²} D³` is a simplex. -/
example : Convexity.StdSimplex ℝ (Fin 4) ≃ₜ Disk 3 :=
  simplexHomeoDisk 2

/-- **Downstream use.** The tetrahedron is the cone over its own boundary:
`Δ³ ≅ Cone(∂Δ³)`, the literal radial form (cone over the triangle boundary). -/
example : Convexity.StdSimplex ℝ (Fin 4) ≃ₜ SimplexBoundaryCone 2 :=
  simplexHomeoBoundaryConeStd 2

/-- **DAG node 10, PROVED** in `HemisphereDisk.lean` (discharged 2026-09-11, this invocation).

`𝕊ⁿ` minus the open upper hemisphere is the closed lower hemisphere, homeomorphic to the
closed `n`-disk.  The proved theorem `lowerHemisphereHomeoDisk n` carries exactly the
statement recorded below (checked by the example): `{x ∈ 𝕊ⁿ | x_last ≤ 0} ≃ₜ 𝔻ⁿ`.
With `doubleDiskQuotHomeoSphere` (node 7) this closes the induction `S³ # S³ ≅ S³` over
the finite extinction decomposition.  Compactness / T2 / nonemptiness audits of the
hemisphere are proved instances in `HemisphereDisk.lean`. -/
example (n : ℕ) :
    Nonempty ({x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 //
      (x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) ≤ 0} ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ⟨lowerHemisphereHomeoDisk n⟩

/-! ## Named blockers (statements only; explicitly NOT claimed) -/

/-- **MISSING THEOREM (Moise 1952, DAG node 1, weakened consequence).**

Every connected second-countable locally-ℝ³ space admits a CW complex structure whose
total set is the whole space.  This is strictly weaker than Moise's triangulability with
unique PL structure (recorded in `MOISE_DAG.md`); it is stated here only because
mathlib's `CWComplex` provides the conclusion object.  A named blocker — not a theorem,
not an assumption, and NOT implied by any definition called `Triangulable`. -/
def moiseWeakenedCW : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M],
    LocallyEuclideanOfDimension M 3 → Nonempty (Topology.CWComplex (X := M) Set.univ)

/-! ## Discharged DAG nodes (proved in this worktree) -/

/-- **DAG node (7), proved.** `Sⁿ⁺¹ = Dⁿ⁺¹ ∪_{Sⁿ} Dⁿ⁺¹`; in particular
`𝕊³ = D³ ∪_{S²} D³` via `sphereThreeGluedDisks`. -/
example (n : ℕ) : DoubleDiskQuot n ≃ₜ Sphere (n + 1) :=
  doubleDiskQuotHomeoSphere n

/-- **DAG node (8), proved.** Suspension and cone realizations. -/
example (n : ℕ) : SuspQuot n ≃ₜ Sphere (n + 1) :=
  suspQuotHomeoSphere n

example (n : ℕ) : ConeQuot n ≃ₜ Disk (n + 1) :=
  coneQuotHomeoDisk n

/-- **DAG node (11), proved.** The sphere-recognition target `𝕊³` is realized by the
gluing construction, with dimension/compactness/nonemptiness audits (Downstream.lean). -/
example : DoubleDiskQuot 2 ≃ₜ Poincare.Longrun.Topology.SphereThree :=
  sphereThreeGluedDisks

end Poincare.D12.TriangulationTopology
