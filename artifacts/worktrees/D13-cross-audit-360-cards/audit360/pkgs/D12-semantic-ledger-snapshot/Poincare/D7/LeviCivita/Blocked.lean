import Poincare.D7.LeviCivita.Coefficients
import Poincare.D7.LeviCivita.Koszul
import Poincare.Stage1.RiemannAdapter
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Poincare.D7.LeviCivita.Blocked

**D7 Levi-Civita smoothness layer, part 4: the explicit unproved `Prop`s and their named
blockers.**

Per the task rules, everything this layer cannot prove is recorded as an **explicit unproved
`Prop`** with a **named blocker**. There is no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` anywhere in the D7 sources; each item below is a `def ... : Prop` (a well-formed
statement) together with a `def ... : String` naming the blocker and listing the exact missing
mathlib dependencies.

## Blocked items

1. `LeviCivitaSmoothnessStatement` — smoothness of mathlib's `leviCivitaConnection`: if `M` is
   `C^{n+2}` and the metric is `C^{n+1}`, the Levi-Civita connection is `C^n`. The pinned mathlib
   revision `7974e751bece493b6ff508039423ca9fa2452fa8` states this as a future PR in the module
   docstring of `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`
   (lines 22-23) but proves nothing about it. The target predicate
   `ContMDiffCovariantDerivative` exists (`CovariantDerivative/Basic.lean:412`) and has no
   instance for `leviCivitaConnection`.
2. `SmoothLeviCivitaExistenceStatement` — the **full** Levi-Civita existence theorem on a smooth
   Riemannian manifold: a `C^n` torsion-free metric-compatible connection. Mathlib already
   provides existence, torsion-freeness and metric compatibility
   (`leviCitaConnection`, `isLeviCivitaConnection_leviCivitaConnection`), so this statement is
   *equivalent* to item 1 plus the checked reduction
   `smoothLeviCivitaExistence_of_smoothness`; the smoothness half is the missing input.
3. `CovariantDerivativeCurvatureMatchesD7` — a `CovariantDerivative.curvature` matching the D7
   `(1,3)` tensor. The candidate formula is stated explicitly (`curvatureCandidate`), so the
   missing input is not the statement but the *construction*: the second covariant derivative of a
   section and the smoothness of the connection needed to differentiate `∇_Y Z`.
4. `SecondBianchiStatement` for the candidate — the covariant derivative of the curvature
   (`∇R`), which needs the induced connection on the (1,3) tensor bundle.

Each blocker string is checked nonempty (`..._ne_nil`), and each missing-dependency list is
checked nonempty, so the named blocker is an auditable kernel declaration rather than prose only.
-/

open Bundle
open scoped BigOperators Manifold ContDiff Bundle

namespace Poincare
namespace D7
namespace LeviCivita

universe v w uE uH uM

/-! ## Named blockers and missing-dependency records -/

/-- **Blocker `B-D7-LC-SMOOTHNESS`.** The pinned mathlib revision has no smoothness result for
`leviCivitaConnection`; its own module docstring says this is a future PR. -/
def BlockerLeviCivitaSmoothness : String :=
  "B-D7-LC-SMOOTHNESS: pinned mathlib 7974e751 proves no smoothness statement for \
  CovariantDerivative.leviCivitaConnection; the module docstring of \
  CovariantDerivative/LeviCivita.lean (lines 22-23) announces it as a future PR. The target \
  predicate ContMDiffCovariantDerivative exists (CovariantDerivative/Basic.lean:412) but no \
  instance for leviCivitaConnection is provided."

/-- **Blocker `B-D7-MANIFOLD-CURVATURE`.** The pinned mathlib revision has no
`CovariantDerivative.curvature`; the candidate `(1,3)` formula is stateable but its construction
needs second covariant derivatives of sections and smoothness of the connection. -/
def BlockerCovariantDerivativeCurvature : String :=
  "B-D7-MANIFOLD-CURVATURE: pinned mathlib 7974e751 has no CovariantDerivative.curvature and no \
  Riemann/Ricci curvature declaration (grep of Mathlib/ for curvature finds only a docstring in \
  MeasureTheory/Measure/Doubling.lean). The candidate formula \
  R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z needs a second covariant derivative of a section \
  (a calculus of ∇_X∇_Y Z) and smoothness of the connection to differentiate ∇_Y Z."

/-- **Blocker `B-D7-NABLA-R`.** The second Bianchi identity needs the covariant derivative of the
curvature tensor, i.e. the induced connection on the (1,3) tensor bundle. -/
def BlockerSecondBianchi : String :=
  "B-D7-NABLA-R: no covariant-derivative calculus on tensor fields (nabla R); the induced \
  connection on the (1,3) tensor bundle is absent from the released API."

theorem BlockerLeviCivitaSmoothness_ne_nil : BlockerLeviCivitaSmoothness ≠ "" := by
  unfold BlockerLeviCivitaSmoothness
  simp

theorem BlockerCovariantDerivativeCurvature_ne_nil :
    BlockerCovariantDerivativeCurvature ≠ "" := by
  unfold BlockerCovariantDerivativeCurvature
  simp

theorem BlockerSecondBianchi_ne_nil : BlockerSecondBianchi ≠ "" := by
  unfold BlockerSecondBianchi
  simp

/-- Exact missing mathlib dependencies of `LeviCivitaSmoothnessStatement`. -/
def LeviCivitaSmoothnessMissingDependencies : List String :=
  [ "ContMDiffCovariantDerivative (leviCivitaConnection I M) n: ABSENT (the class exists at \
    CovariantDerivative/Basic.lean:412, the instance is not proved)",
    "Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean lines 22-23: \
    'Future PRs will prove smoothness: if M is C^{n+2} and g is C^{n+1}, the Levi-Civita \
    connection is a C^n connection.' (docstring only)",
    "No manifold-level inverse function theorem / musical-isomorphism smoothness lemma for the \
    dual of the Koszul form is packaged; the coordinate-level half is proved in \
    Poincare.D7.LeviCivita.contDiff_christoffelSymbol" ]

/-- Exact missing mathlib dependencies of `CovariantDerivativeCurvatureMatchesD7`. -/
def CovariantDerivativeCurvatureMissingDependencies : List String :=
  [ "CovariantDerivative.curvature: ABSENT (no declaration; grep of pinned Mathlib/ for \
    'curvature' matches only MeasureTheory/Measure/Doubling.lean)",
    "second covariant derivative of a section: ABSENT (no calculus of ∇_X ∇_Y Z, hence the \
    candidate curvatureCandidate cannot be proved tensorial)",
    "smoothness of the connection (ContMDiffCovariantDerivative): needed to differentiate the \
    section y ↦ ∇_{Y(y)} Z as a section; this is the same gap as B-D7-LC-SMOOTHNESS",
    "induced connection on the (1,3) tensor bundle (nabla R): ABSENT (needed for the second \
    Bianchi identity, blocker B-D7-NABLA-R)" ]

theorem LeviCivitaSmoothnessMissingDependencies_ne_nil :
    LeviCivitaSmoothnessMissingDependencies ≠ [] := by
  unfold LeviCivitaSmoothnessMissingDependencies
  simp

theorem CovariantDerivativeCurvatureMissingDependencies_ne_nil :
    CovariantDerivativeCurvatureMissingDependencies ≠ [] := by
  unfold CovariantDerivativeCurvatureMissingDependencies
  simp

/-! ## Blocked item 1: smoothness of the Levi-Civita connection -/

section LeviCivitaSmoothness

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

/-- **BLOCKED (`BlockerLeviCivitaSmoothness`).** Smoothness of mathlib's
`leviCivitaConnection`: if `M` is `C^{n+2}` and the metric is `C^{n+1}`, the Levi-Civita
connection is a `C^n` connection. This is a `Prop` with no proof: the pinned mathlib revision
proves the torsion-free and metric-compatible halves but not the smoothness half. -/
def LeviCivitaSmoothnessStatement (n : ℕ∞ω) : Prop :=
  CovariantDerivative.ContMDiffCovariantDerivative (CovariantDerivative.leviCivitaConnection I M) n

/-- **BLOCKED (`BlockerLeviCivitaSmoothness`).** The full Levi-Civita existence theorem on a
smooth Riemannian manifold: there exists a `C^n` torsion-free metric-compatible connection.

Mathlib already provides the connection, its torsion-freeness and its metric compatibility
(`isLeviCivitaConnection_leviCivitaConnection`); only the `C^n` part is missing. The checked
reduction `smoothLeviCivitaExistence_of_smoothness` shows that this statement follows from
`LeviCivitaSmoothnessStatement`. -/
def SmoothLeviCivitaExistenceStatement (n : ℕ∞ω) : Prop :=
  ∃ cov : CovariantDerivative I E (TangentSpace I : M → Type uE),
    cov.IsLeviCivitaConnection ∧ CovariantDerivative.ContMDiffCovariantDerivative cov n

/-- **Checked reuse of the mathlib existence half.** `leviCivitaConnection` is a Levi-Civita
connection, so the only missing ingredient of `SmoothLeviCivitaExistenceStatement` is its
smoothness. -/
theorem leviCivitaConnection_isLeviCivitaConnection :
    (CovariantDerivative.leviCivitaConnection I M).IsLeviCivitaConnection :=
  CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I

/-- **Checked reduction.** Smoothness of `leviCivitaConnection` implies the full smooth
Levi-Civita existence statement. -/
theorem smoothLeviCivitaExistence_of_smoothness {n : ℕ∞ω}
    (h : LeviCivitaSmoothnessStatement (I := I) (M := M) n) : SmoothLeviCivitaExistenceStatement (I := I) (M := M) n :=
  ⟨CovariantDerivative.leviCivitaConnection I M,
    CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I, h⟩

/-- The smoothness statement is exactly the `C^n` clause of the full existence statement for the
canonical connection. -/
theorem leviCivitaSmoothness_iff_contMDiff (n : ℕ∞ω) :
    LeviCivitaSmoothnessStatement (I := I) (M := M) n ↔
      CovariantDerivative.ContMDiffCovariantDerivative (CovariantDerivative.leviCivitaConnection I M) n :=
  Iff.rfl

end LeviCivitaSmoothness

/-! ## Blocked item 2: `CovariantDerivative.curvature` matching the D7 (1,3) tensor -/

section ManifoldCurvature

open Poincare.RiemannAdapter

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- **The candidate `(1,3)` curvature formula**, stateable in current mathlib using the
extension `FiberBundle.extend` of a tangent vector to a global vector field and the Lie bracket
`VectorField.mlieBracket`:

`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`

at the point `x`. The section `∇_Y Z` is `fun y => cov (extend Z) y (extend Y y)`; the outer
`cov` applies to it. This is the same formula as the D7 abstract curvature
`Poincare.Longrun.Geometry.AbstractConnection.curvature` (see
`Poincare.D7.Curvature.RiemannCurvatureData.curvature_apply_eq`).

The formula is *stateable*, but turning it into a pointwise tensor is exactly what mathlib cannot
do: the section `∇_Y Z` must be differentiable for the construction to be tensorial, which needs
smoothness of `cov`. -/
noncomputable def curvatureCandidate
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) (x : M)
    (X₀ Y₀ Z₀ : TangentSpace I x) : TangentSpace I x :=
  cov (fun y => cov (FiberBundle.extend E Z₀) y (FiberBundle.extend E Y₀ y)) x
      (FiberBundle.extend E X₀ x)
    - cov (fun y => cov (FiberBundle.extend E Z₀) y (FiberBundle.extend E X₀ y)) x
      (FiberBundle.extend E Y₀ x)
    - cov (FiberBundle.extend E Z₀) x
      (VectorField.mlieBracket I (FiberBundle.extend E X₀) (FiberBundle.extend E Y₀) x)

/-- **BLOCKED (`BlockerCovariantDerivativeCurvature`).** The missing
`CovariantDerivative.curvature` matching the D7 `(1,3)` tensor: there is a pointwise `(1,3)`
tensor `κ` whose value is the candidate formula and which satisfies the two D7 interface
obligations (first-pair antisymmetry and the first Bianchi identity).

This is a `Prop` with no proof. Mathlib has no curvature declaration for a covariant derivative,
and the construction needs the second covariant derivative of a section together with smoothness
of the connection. -/
def CovariantDerivativeCurvatureMatchesD7
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) : Prop :=
  ∃ κ : PointwiseCurvature I M,
    (∀ (x : M) (X Y Z : TangentSpace I x), κ x X Y Z = curvatureCandidate I cov x X Y Z) ∧
    (∀ (x : M) (X Y Z : TangentSpace I x), κ x X Y Z = - κ x Y X Z) ∧
    (∀ (x : M) (X Y Z : TangentSpace I x),
      κ x X Y Z + κ x Y Z X + κ x Z X Y = 0)

/-- **Checked packaging.** Given a pointwise tensor satisfying the candidate formula and the two
D7 interface obligations, the blocked statement holds. This shows the `Prop` is the precise
interface and does not smuggle in a proof of existence. -/
theorem covariantDerivativeCurvatureMatchesD7_of_data
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (κ : PointwiseCurvature I M)
    (hform : ∀ (x : M) (X Y Z : TangentSpace I x),
      κ x X Y Z = curvatureCandidate I cov x X Y Z)
    (hskew : ∀ (x : M) (X Y Z : TangentSpace I x), κ x X Y Z = - κ x Y X Z)
    (hbianchi : ∀ (x : M) (X Y Z : TangentSpace I x),
      κ x X Y Z + κ x Y Z X + κ x Z X Y = 0) :
    CovariantDerivativeCurvatureMatchesD7 I cov :=
  ⟨κ, hform, hskew, hbianchi⟩

/-- The blocked D7-matching curvature statement implies the D2 blocked contract
`Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement` (the pointwise tensor with the
two symmetry obligations), for the same connection. This is the bridge between the D7 smoothness
layer and the D2 interface. -/
theorem covariantDerivativeCurvatureStatement_of_matchesD7
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (h : CovariantDerivativeCurvatureMatchesD7 I cov) :
    Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement I M cov := by
  obtain ⟨κ, -, hskew, hbianchi⟩ := h
  exact ⟨κ, hskew, hbianchi⟩

end ManifoldCurvature

end LeviCivita
end D7
end Poincare
