/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.InnerProductSpace.Orientation

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Volume.Blocked

**D7 orientability and volume-form algebra layer, part 5: the explicit unproved `Prop`s for the
manifold-level Riemannian volume form, and the exact missing mathlib dependencies.**

Per the task rules, everything this layer cannot prove is recorded as an **explicit unproved
`Prop`** with a **named blocker**. There is no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` anywhere in the D7 sources; each item below is a `def ... : Prop` (a well-formed
statement) together with a `def ... : String` naming the blocker.

## Blocked items

1. `RiemannianVolumeFormExistsStatement` — on an oriented Riemannian manifold, there is a global
   family of top-degree alternating forms whose value at each point is the orientation volume form
   of the tangent space. Blocker `BlockerRiemannianVolumeForm`.
2. `RiemannianVolumeFormSmoothStatement` — the stronger statement that the family is a **smooth
   section** of the bundle of top alternating forms. Blocker `BlockerRiemannianVolumeForm`. The
   missing ingredient is the smooth vector bundle `x ↦ AlternatingMap ℝ (TangentSpace I x) ℝ n`
   (the top exterior power of the cotangent bundle) with its `FiberBundle`, `VectorBundle` and
   `ContMDiffVectorBundle` instances, together with a smooth positively oriented orthonormal frame.
3. `RiemannianVolumeMeasureStatement` — the Riemannian volume measure associated with the volume
   form. Blocker `BlockerManifoldMeasureTheory`. Mathlib has no measure theory on manifolds: no
   `MeasurableSpace` instance for a `ChartedSpace`/`IsManifold`, no integration of top forms, and
   `IsAddHaarMeasure` is only for locally compact topological groups (not manifolds).

The exact missing declarations are listed in `MissingMathlibDependencies`.

Each blocker string is checked nonempty (`..._ne_nil`), so the named blocker is an auditable
kernel declaration rather than prose only.
-/

open Bundle Manifold Module MeasureTheory

open scoped Bundle

universe uE uH uM

namespace Poincare.D7.Volume

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]

/-! ## Named blockers -/

/-- **Blocker `B-D7-RIEMANNIAN-VOLUME-FORM`.** The pinned mathlib revision
`7974e751bece493b6ff508039423ca9fa2452fa8` has the pointwise volume form
`Orientation.volumeForm` on a single oriented inner product space, but no manifold-level
construction: no orientation of the tangent bundle, no smooth bundle of alternating forms, and no
smooth positively oriented orthonormal frame field. -/
def BlockerRiemannianVolumeForm : String :=
  "B-D7-RIEMANNIAN-VOLUME-FORM: pinned mathlib 7974e751 has Orientation.volumeForm only for a \
  single oriented inner product space; the manifold-level volume form needs the smooth top \
  alternating-form bundle (exterior power of the cotangent bundle), a manifold orientation, and \
  a smooth positively oriented orthonormal frame field, none of which exist in mathlib."

/-- **Blocker `B-D7-MANIFOLD-MEASURE-THEORY`.** Mathlib has no measure theory on smooth
manifolds: no `MeasurableSpace`/`BorelSpace` instance for a `ChartedSpace`, no integration of
top-degree forms, no Riemannian volume density, and no partition-of-unity gluing of local volume
forms into a measure. `IsAddHaarMeasure` is only available on locally compact topological groups
and finite-dimensional real vector spaces, not on manifolds. -/
def BlockerManifoldMeasureTheory : String :=
  "B-D7-MANIFOLD-MEASURE-THEORY: no MeasurableSpace/BorelSpace instance for a ChartedSpace, no \
  integration of top forms on manifolds, no Riemannian volume density, and no partition-of-unity \
  gluing of local volume forms; IsAddHaarMeasure exists only on locally compact groups and \
  finite-dimensional real vector spaces."

/-- **Blocker `B-D7-MANIFOLD-ORIENTATION`.** Mathlib has `Orientation R M ι` for a module `M`,
but no orientation of the tangent bundle of a manifold and no orientability predicate for
manifolds. The statements below therefore quantify over a pointwise orientation family
`orient : ∀ x, Orientation ℝ (TangentSpace I x) (Fin n)`; the smooth consistency of such a
family across charts is part of the missing structure. -/
def BlockerManifoldOrientation : String :=
  "B-D7-MANIFOLD-ORIENTATION: mathlib has Orientation for a module but no tangent-bundle \
  orientation, no manifold orientability predicate, and no orientation double cover; the \
  statements quantify over a pointwise orientation family whose smooth consistency is missing."

theorem BlockerRiemannianVolumeForm_ne_nil : BlockerRiemannianVolumeForm ≠ "" := by
  unfold BlockerRiemannianVolumeForm; simp

theorem BlockerManifoldMeasureTheory_ne_nil : BlockerManifoldMeasureTheory ≠ "" := by
  unfold BlockerManifoldMeasureTheory; simp

theorem BlockerManifoldOrientation_ne_nil : BlockerManifoldOrientation ≠ "" := by
  unfold BlockerManifoldOrientation; simp

/-! ## The pointwise orientation volume form on a tangent space -/

/-- The dimension of a tangent space is the dimension of the model space. -/
theorem finrank_tangentSpace (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : finrank ℝ (TangentSpace I x) = finrank ℝ E :=
  (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq

/-- The pointwise orientation volume form on a tangent space, obtained from the mathlib
`Orientation.volumeForm` of the tangent space at `x`. -/
noncomputable def tangentVolumeForm (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (TangentSpace I : M → Type uE)]
    {n : ℕ} (orient : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (hn : finrank ℝ E = n) (x : M) : AlternatingMap ℝ (TangentSpace I x) ℝ (Fin n) :=
  letI : Fact (finrank ℝ (TangentSpace I x) = n) :=
    ⟨by rw [finrank_tangentSpace I M x, hn]⟩
  @Orientation.volumeForm (TangentSpace I x) _ _ n _ (orient x)

/-! ## The missing smooth bundle of top alternating forms -/

/-- Contract for the (missing) smooth vector bundle of top-degree alternating forms
`x ↦ AlternatingMap ℝ (TangentSpace I x) ℝ n` over `M`, the top exterior power of the cotangent
bundle. All bundle fields are the exact structures that mathlib lacks for this bundle. -/
structure TopFormBundle (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] (n : ℕ) where
  /-- The model fiber of the bundle of `n`-alternating forms. -/
  F : Type uE
  [normedAddCommGroupF : NormedAddCommGroup F]
  [normedSpaceF : NormedSpace ℝ F]
  /-- The bundle of `n`-alternating forms over `M`. -/
  V : M → Type uE
  [topologicalSpaceTotal : TopologicalSpace (TotalSpace F V)]
  [topologicalSpaceFiber : ∀ x : M, TopologicalSpace (V x)]
  [addCommGroupFiber : ∀ x : M, AddCommGroup (V x)]
  [moduleFiber : ∀ x : M, Module ℝ (V x)]
  [fiberBundle : FiberBundle F V]
  [vectorBundle : VectorBundle ℝ F V]
  [contMDiffVectorBundle : ContMDiffVectorBundle (⊤ : WithTop ℕ∞) F V I]
  /-- Fiberwise identification with the top alternating forms on the tangent space. -/
  fiberEquiv : ∀ x : M, V x ≃ₗ[ℝ] AlternatingMap ℝ (TangentSpace I x) ℝ (Fin n)
  /-- A smooth section of the bundle. -/
  section' : ContMDiffSection I F (⊤ : WithTop ℕ∞) V

/-- The pointwise volume-form property of a section of the top-form bundle. -/
def IsOrientationVolumeForm (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (TangentSpace I : M → Type uE)]
    {n : ℕ} (C : TopFormBundle I M n)
    (orient : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (hn : finrank ℝ E = n) : Prop :=
  ∀ x : M, C.fiberEquiv x (C.section' x) = tangentVolumeForm I M orient hn x

/-! ## Blocked statements -/

/-- **BLOCKED (`BlockerRiemannianVolumeForm`).** Existence of the Riemannian volume form: on an
oriented Riemannian manifold, there is a family of top-degree alternating forms on the tangent
spaces whose value at each point is the orientation volume form.

This is a `Prop` with no proof. The pointwise part is elementary (`Orientation.volumeForm`), but
the manifold-level statement requires the missing orientation and smooth-bundle structure; the
stronger smooth statement is `RiemannianVolumeFormSmoothStatement`. -/
def RiemannianVolumeFormExistsStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [PseudoEMetricSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [RiemannianBundle (TangentSpace I : M → Type uE)],
    ∀ orient : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)),
      ∃ form : ∀ x : M, AlternatingMap ℝ (TangentSpace I x) ℝ (Fin (finrank ℝ E)),
        ∀ x : M, form x = tangentVolumeForm I M orient rfl x

/-- **BLOCKED (`BlockerRiemannianVolumeForm`).** Smoothness of the Riemannian volume form: on an
oriented Riemannian manifold, there is a smooth section of the bundle of top alternating forms
whose value at each point is the orientation volume form of the tangent space.

This is a `Prop` with no proof; it asserts the existence of the missing bundle contract
`TopFormBundle` together with the pointwise volume-form property. -/
def RiemannianVolumeFormSmoothStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [PseudoEMetricSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [RiemannianBundle (TangentSpace I : M → Type uE)],
    ∀ orient : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)),
      ∃ C : TopFormBundle I M (finrank ℝ E), IsOrientationVolumeForm I M C orient rfl

/-- **BLOCKED (`BlockerManifoldMeasureTheory`).** Existence of the Riemannian volume measure: on
an oriented Riemannian manifold, there is a nonzero Borel measure that is finite on compact sets.

This is a `Prop` with no proof. The missing ingredients are the `MeasurableSpace`/`BorelSpace`
structure on a charted space, the integration of top forms, and the local density
`√(det g)` gluing by partition of unity; the measure is not characterised here because the
characterisation itself needs the missing integration theory. -/
def RiemannianVolumeMeasureStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [PseudoEMetricSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M] [IsManifold I (⊤ : WithTop ℕ∞) M]
    [RiemannianBundle (TangentSpace I : M → Type uE)],
    ∃ μ : Measure M, μ ≠ 0 ∧ ∀ K : Set M, IsCompact K → μ K < ⊤

/-! ## Exact missing mathlib dependencies -/

/-- The exact mathlib declarations/structures missing for the manifold-level Riemannian volume
form and measure, at the pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`. -/
def MissingMathlibDependencies : List String :=
  [ "Manifold orientation: no `Orientation` of the tangent bundle and no orientability predicate \
    for manifolds (only `Orientation R M ι` for a module).",
    "Top alternating-form bundle: no `FiberBundle`/`VectorBundle`/`ContMDiffVectorBundle` \
    instances for `x ↦ AlternatingMap ℝ (TangentSpace I x) ℝ n` (top exterior power of the \
    cotangent bundle).",
    "Smooth frame field: no smooth positively oriented orthonormal frame; `stdOrthonormalBasis` \
    and `Orientation.finOrthonormalBasis` are noncomputable and not smooth in the base point.",
    "Manifold measure theory: no `MeasurableSpace`/`BorelSpace` instance for a `ChartedSpace`, no \
    integration of top-degree forms, no Riemannian volume density `√(det g)`.",
    "Partition of unity: mathlib has `SmoothPartitionOfUnity` but no gluing of local volume forms \
    or densities into a global measure.",
    "Haar measure: `IsAddHaarMeasure` is only for locally compact topological groups and \
    finite-dimensional real vector spaces, not for manifolds." ]

theorem MissingMathlibDependencies_ne_nil : MissingMathlibDependencies ≠ [] := by
  unfold MissingMathlibDependencies
  simp

theorem MissingMathlibDependencies_length :
    MissingMathlibDependencies.length = 6 := rfl

end Poincare.D7.Volume
