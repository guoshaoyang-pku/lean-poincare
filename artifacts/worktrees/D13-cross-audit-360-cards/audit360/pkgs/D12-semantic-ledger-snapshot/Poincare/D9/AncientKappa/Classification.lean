/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D9-ancient-kappa-solutions builder
-/
module

public import Poincare.D9.AncientKappa.Basic

/-!
# Poincare.D9.AncientKappa.Classification

**State-only statements for 3-dimensional κ-solutions.**

This file fixes the *statements* of the three classical results of the singularity-analysis
layer, without claiming their proofs:

* `threeDimensionalKappaSolutionClassification` — the classification of 3-dimensional
  κ-solutions: up to parabolic scaling and passage to a quotient, a κ-solution is a round
  cylinder `S² × ℝ` (or a quotient), the Bryant steady soliton, or asymptotically solitonic;
* `asymptoticSolitonStatement` — the asymptotic-soliton alternative: a κ-solution that is not
  asymptotically cylindrical is asymptotic to a soliton at infinity;
* `perelmanCompactnessTheorem` — Perelman's compactness theorem for the space of κ-solutions:
  a sequence of pointed κ-solutions with a uniform non-collapsing constant and a uniform
  curvature bound at the basepoints has a subsequence converging, in the pointed sense, to a
  κ-solution;
* `canonicalNeighborhoodLinkage` — the canonical-neighbourhood linkage: on a 3-dimensional
  κ-solution, every point of sufficiently high curvature admits a canonical neighbourhood of
  neck, cap or compact-positively-curved type.

The geometric recognition and convergence notions (`Recognizes`, `ConvergesTo`,
`HighCurvature`, `HasCanonicalNeighborhood`) are *explicit parameters* of the statements: mathlib
has no isometry classification of Riemannian manifolds, no pointed Cheeger–Gromov convergence and
no canonical-neighbourhood theory, so these notions are supplied by a future development.  Each
statement is a `Prop`-valued definition, never a proof obligation discharged here; the
`_iff` lemmas below are kernel-checked shape lemmas recording that the definitions are exactly
the displayed formulas.

## Sources

* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109, §§1, 11;
* G. Perelman, *The entropy formula for the Ricci flow and its geometric applications*,
  arXiv:math/0211159, §4;
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, AMS (2007), Chapters 9, 11;
* S. Brendle, *Rotational symmetry of self-similar solutions to the Ricci flow*, Invent. Math.
  (2013) (the Bryant-soliton and asymptotic-soliton alternatives).

No declaration in this file is an unproved hole or an extra logical postulate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Manifold Topology ENNReal

namespace Poincare
namespace Longrun
namespace AncientKappa

/-! ## 1. Three-dimensional κ-solutions -/

/-- The Euclidean model space `ℝ³`. -/
abbrev Euclid3 := EuclideanSpace ℝ (Fin 3)

/-- **Three-dimensional κ-solution.**  An ancient solution on a 3-manifold, together with a
volume family and a non-collapsing constant `κ` such that the solution is κ-non-collapsed at all
scales, plus a scalar-curvature function with a nonnegativity hypothesis.

The field `compact_up_to_scaling` is an explicit placeholder for the remaining condition in the
standard definition ("each blow-down limit is compact"): mathlib has no compactness theory of
Riemannian manifolds, so the condition cannot be expressed and is carried as a `Prop` field with
this docstring.  The bounded-curvature hypothesis is part of `AncientSolution`. -/
structure ThreeDimKappaSolution (M : Type*) [PseudoEMetricSpace M] [ChartedSpace Euclid3 M]
    [MeasurableSpace M] where
  /-- The underlying ancient solution. -/
  ancient : AncientSolution (𝓘(ℝ, Euclid3)) M
  /-- The volume family of the flow. -/
  volume : ℝ → Measure M
  /-- The non-collapsing constant. -/
  κ : ℝ
  /-- κ-non-collapsing at all scales. -/
  noncollapsing : AncientSolution.KappaNoncollapsingAtAllScales 3 ancient volume κ
  /-- A scalar-curvature function. -/
  scalarCurvature : ℝ → M → ℝ
  /-- The scalar curvature is nonnegative (the scalar shadow of nonnegative curvature operator). -/
  scalar_nonneg : ∀ (t : ℝ) (x : M), 0 ≤ scalarCurvature t x
  /-- Explicit placeholder for "compact up to scaling" (each blow-down limit is compact). -/
  compact_up_to_scaling : Prop

namespace ThreeDimKappaSolution

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace Euclid3 M] [MeasurableSpace M]
  (S : ThreeDimKappaSolution M)

/-- **Checked consequence.**  A 3-dimensional κ-solution is an ancient solution on `(-∞, 0]`. -/
theorem timeDomain_eq : S.ancient.flow.timeDomain = Set.Iic 0 :=
  S.ancient.timeDomain_eq

/-- **Checked consequence.**  The non-collapsing constant is positive. -/
theorem kappa_pos : 0 < S.κ :=
  S.noncollapsing.kappa_pos

/-- **Checked consequence.**  The curvature is bounded on every compact time subinterval and every
compact spatial set. -/
theorem exists_curvature_bound {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) {K : Set M}
    (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x ∈ K, |S.ancient.curvature t x| ≤ C :=
  S.ancient.exists_curvature_bound hab hb hK

end ThreeDimKappaSolution

/-- **State-only statement: classification of 3-dimensional κ-solutions.**  Given the
model-recognition predicates `IsRoundCylinderOrQuotient` (the solution is, up to parabolic
scaling, a quotient of the round cylinder `S² × ℝ`), `IsBryantSteadySoliton` (the solution is the
Bryant steady soliton) and `IsAsymptoticSoliton` (the solution is asymptotic to a soliton at
infinity), every 3-dimensional κ-solution is recognised by one of the three.

The recognition predicates are explicit parameters: the pinned mathlib has no isometry
classification of Riemannian manifolds, so the geometric content of each alternative must be
supplied by a future development. -/
def threeDimensionalKappaSolutionClassification {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace Euclid3 M] [MeasurableSpace M]
    (IsRoundCylinderOrQuotient IsBryantSteadySoliton IsAsymptoticSoliton :
      ThreeDimKappaSolution M → Prop) : Prop :=
  ∀ S : ThreeDimKappaSolution M,
    IsRoundCylinderOrQuotient S ∨ IsBryantSteadySoliton S ∨ IsAsymptoticSoliton S

/-- **Checked shape lemma.**  `threeDimensionalKappaSolutionClassification` is exactly the
displayed formula, i.e. it is a definition and not an additional postulate. -/
theorem threeDimensionalKappaSolutionClassification_iff {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace Euclid3 M] [MeasurableSpace M]
    (IsRoundCylinderOrQuotient IsBryantSteadySoliton IsAsymptoticSoliton :
      ThreeDimKappaSolution M → Prop) :
    threeDimensionalKappaSolutionClassification IsRoundCylinderOrQuotient
        IsBryantSteadySoliton IsAsymptoticSoliton ↔
      ∀ S : ThreeDimKappaSolution M,
        IsRoundCylinderOrQuotient S ∨ IsBryantSteadySoliton S ∨ IsAsymptoticSoliton S :=
  Iff.rfl

/-- **State-only statement: asymptotic soliton behaviour.**  Every 3-dimensional κ-solution that
is not asymptotically cylindrical is asymptotic to a soliton at infinity (in the positively
curved case, the Bryant soliton; the cylindrical case is the neck alternative).  The two
recognition predicates are explicit parameters, since mathlib has no asymptotic-geometry theory
for Riemannian manifolds. -/
def asymptoticSolitonStatement {M : Type*} [PseudoEMetricSpace M] [ChartedSpace Euclid3 M]
    [MeasurableSpace M] (IsAsymptoticallyCylindrical IsAsymptoticToSoliton :
      ThreeDimKappaSolution M → Prop) : Prop :=
  ∀ S : ThreeDimKappaSolution M,
    ¬ IsAsymptoticallyCylindrical S → IsAsymptoticToSoliton S

/-- **Checked shape lemma.**  `asymptoticSolitonStatement` is exactly the displayed formula. -/
theorem asymptoticSolitonStatement_iff {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace Euclid3 M] [MeasurableSpace M]
    (IsAsymptoticallyCylindrical IsAsymptoticToSoliton : ThreeDimKappaSolution M → Prop) :
    asymptoticSolitonStatement IsAsymptoticallyCylindrical IsAsymptoticToSoliton ↔
      ∀ S : ThreeDimKappaSolution M,
        ¬ IsAsymptoticallyCylindrical S → IsAsymptoticToSoliton S :=
  Iff.rfl

/-! ## 2. Perelman's compactness theorem -/

/-- A **pointed** 3-dimensional κ-solution: a κ-solution together with a basepoint. -/
structure PointedKappaSolution3D (M : Type*) [PseudoEMetricSpace M] [ChartedSpace Euclid3 M]
    [MeasurableSpace M] where
  /-- The underlying κ-solution. -/
  solution : ThreeDimKappaSolution M
  /-- The basepoint. -/
  basepoint : M

/-- **State-only statement: Perelman's compactness theorem for κ-solutions.**  Let `seq` be a
sequence of pointed 3-dimensional κ-solutions.  If the non-collapsing constants are uniformly
bounded below (equivalently, all equal to a fixed positive `κ`) and the scalar curvature at the
basepoints is uniformly bounded, then there is a strictly increasing reindexing `φ` and a pointed
κ-solution `limit` such that `seq (φ k)` converges to `limit` in the pointed sense supplied by the
relation `ConvergesTo`.

The convergence relation is an explicit parameter: mathlib has no pointed Cheeger–Gromov
convergence of Riemannian manifolds. -/
def perelmanCompactnessTheorem {M : Type*} [PseudoEMetricSpace M] [ChartedSpace Euclid3 M]
    [MeasurableSpace M] (ConvergesTo : PointedKappaSolution3D M → PointedKappaSolution3D M → Prop) :
    Prop :=
  ∀ seq : ℕ → PointedKappaSolution3D M,
    (∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, (seq k).solution.κ = κ) →
    (∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      |(seq k).solution.scalarCurvature 0 (seq k).basepoint| ≤ C) →
    ∃ (limit : PointedKappaSolution3D M) (φ : ℕ → ℕ) (K : ℕ),
      StrictMono φ ∧ ∀ k : ℕ, K ≤ k → ConvergesTo (seq (φ k)) limit

/-- **Checked shape lemma.**  `perelmanCompactnessTheorem` is exactly the displayed formula. -/
theorem perelmanCompactnessTheorem_iff {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace Euclid3 M] [MeasurableSpace M]
    (ConvergesTo : PointedKappaSolution3D M → PointedKappaSolution3D M → Prop) :
    perelmanCompactnessTheorem ConvergesTo ↔
      ∀ seq : ℕ → PointedKappaSolution3D M,
        (∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, (seq k).solution.κ = κ) →
        (∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
          |(seq k).solution.scalarCurvature 0 (seq k).basepoint| ≤ C) →
        ∃ (limit : PointedKappaSolution3D M) (φ : ℕ → ℕ) (K : ℕ),
          StrictMono φ ∧ ∀ k : ℕ, K ≤ k → ConvergesTo (seq (φ k)) limit :=
  Iff.rfl

/-! ## 3. Canonical-neighbourhood linkage -/

/-- The three types of canonical neighbourhood in Perelman's neck analysis. -/
inductive CanonicalNeighborhoodType where
  /-- A δ-neck `S² × (-δ⁻¹, δ⁻¹)`. -/
  | neck
  /-- A δ-cap (a positively curved cap glued to a neck). -/
  | cap
  /-- A compact positively curved manifold (the whole solution is compact and positively curved). -/
  | compactPositive
  deriving DecidableEq

/-- **State-only statement: canonical-neighbourhood linkage.**  For every 3-dimensional
κ-solution `S` and every `ε > 0` there is `δ > 0` such that every point `x` of high curvature
(curvature scale above `ε⁻²`, supplied by the predicate `HighCurvature`) admits a canonical
neighbourhood of radius `δ`: a δ-neck, a δ-cap, or a compact positively curved manifold
(supplied by the predicate `HasCanonicalNeighborhood`).

Both geometric predicates are explicit parameters, because mathlib has no neck analysis.  The
statement records the exact logical linkage `κ-solution + high curvature ⟹ canonical
neighbourhood` used in the surgery construction. -/
def canonicalNeighborhoodLinkage {M : Type*} [PseudoEMetricSpace M] [ChartedSpace Euclid3 M]
    [MeasurableSpace M] (HighCurvature : ThreeDimKappaSolution M → ℝ → M → Prop)
    (HasCanonicalNeighborhood : ThreeDimKappaSolution M → M → ℝ →
      CanonicalNeighborhoodType → Prop) : Prop :=
  ∀ (S : ThreeDimKappaSolution M) (ε : ℝ), 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : M, HighCurvature S ε x →
      HasCanonicalNeighborhood S x δ CanonicalNeighborhoodType.neck ∨
      HasCanonicalNeighborhood S x δ CanonicalNeighborhoodType.cap ∨
      HasCanonicalNeighborhood S x δ CanonicalNeighborhoodType.compactPositive

/-- **Checked shape lemma.**  `canonicalNeighborhoodLinkage` is exactly the displayed formula. -/
theorem canonicalNeighborhoodLinkage_iff {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace Euclid3 M] [MeasurableSpace M]
    (HighCurvature : ThreeDimKappaSolution M → ℝ → M → Prop)
    (HasCanonicalNeighborhood : ThreeDimKappaSolution M → M → ℝ →
      CanonicalNeighborhoodType → Prop) :
    canonicalNeighborhoodLinkage HighCurvature HasCanonicalNeighborhood ↔
      ∀ (S : ThreeDimKappaSolution M) (ε : ℝ), 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ x : M, HighCurvature S ε x →
          HasCanonicalNeighborhood S x δ CanonicalNeighborhoodType.neck ∨
          HasCanonicalNeighborhood S x δ CanonicalNeighborhoodType.cap ∨
          HasCanonicalNeighborhood S x δ CanonicalNeighborhoodType.compactPositive :=
  Iff.rfl

end AncientKappa
end Longrun
end Poincare
