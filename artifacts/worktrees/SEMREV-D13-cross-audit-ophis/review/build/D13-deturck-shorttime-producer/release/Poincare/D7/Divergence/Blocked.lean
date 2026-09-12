/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Divergence.Blocked

**D7 divergence / integration-by-parts layer, part 5: the smooth-manifold divergence theorem as an
explicit unproved `Prop`, with the exact missing mathlib dependencies.**

Per the task rules, everything this layer cannot prove is recorded as an **explicit unproved
`Prop`** with a **named blocker**. There is no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` anywhere in the D7 sources; the item below is a `def ... : Prop` (a well-formed
statement) together with `def ... : String` blockers and a list of exact missing declarations.

## What mathlib (pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`) does provide

* `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` — the **Euclidean box divergence
  theorem**: for `f : ℝⁿ⁺¹ → E` differentiable off a countable set on the box `[a, b]`,
  `∫_[a,b] ∑ i, f' x eᵢ i = ∑ i, (∫_{front face i} f - ∫_{back face i} f)`;
* `ModelWithCorners.boundary I M : Set M` with the interior/boundary point API
  (`Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary`);
* `mfderiv`, `ContMDiff`, `TangentSpace`, `RiemannianBundle`, `IsRiemannianManifold`;
* `Measure.addHaar`, `Measure.IsAddHaarMeasure` on finite-dimensional real vector spaces and
  locally compact groups.

## What is missing (the blockers)

1. **`BlockerStokes`** — Stokes' theorem for differential forms on manifolds,
   `∫_M dω = ∫_{∂M} ω`; in particular the divergence theorem `∫_M div X vol = ∫_{∂M} ⟨X, n⟩ σ`.
   Mathlib has no integration of top-degree forms on manifolds and no Stokes theorem (the string
   `stokes` occurs only in the documentation of the Euclidean box theorem).
2. **`BlockerRiemannianVolumeMeasure`** — the Riemannian volume measure: no global volume form on
   the tangent bundle, no density `√(det g)`, no partition-of-unity gluing. This is the same
   blocker recorded by the D7 orientability/volume-form layer.
3. **`BlockerManifoldBoundary`** — the boundary as a smooth manifold with an induced orientation
   and an induced boundary measure, and the outward unit normal field. Mathlib has only the
   **set** `ModelWithCorners.boundary I M`; there is no `Boundary` manifold, no collar
   neighbourhood, no boundary measure, and no outward normal.
4. **`BlockerManifoldDivergence`** — the metric divergence of a vector field
   (`div X = tr ∇X`), the metric normal pairing `⟨X, n⟩`, and the chart/partition-of-unity
   transfer of the Euclidean box theorem to manifolds.

The exact missing declarations are listed in `MissingMathlibDependencies`; the pieces that are
available and reused are listed in `PresentMathlibDependencies`. Each blocker string is checked
nonempty (`..._ne_nil`), so the named blocker is an auditable kernel declaration rather than prose
only.
-/

open Bundle Manifold MeasureTheory

open scoped Bundle

universe uE uH uM

namespace Poincare.D7.Divergence

/-! ## Named blockers -/

/-- **Blocker `B-D7-STOKES`.** The pinned mathlib revision has the Euclidean box divergence theorem
but no Stokes theorem for differential forms on a manifold and no integration of top-degree forms. -/
def BlockerStokes : String :=
  "B-D7-STOKES: mathlib has MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable for a \
  box in R^n, but no Stokes theorem for differential forms on a manifold, no integration of \
  top-degree forms on manifolds, and no chart/partition-of-unity transfer of the Euclidean box \
  theorem to a manifold."

/-- **Blocker `B-D7-RIEMANNIAN-VOLUME-MEASURE`.** There is no Riemannian volume measure on a
manifold: no global volume form, no density `√(det g)`, no gluing by partition of unity. -/
def BlockerRiemannianVolumeMeasure : String :=
  "B-D7-RIEMANNIAN-VOLUME-MEASURE: no global Riemannian volume form on the tangent bundle, no \
  density sqrt(det g), and no partition-of-unity gluing of local densities into a measure; \
  Measure.IsAddHaarMeasure is only available on locally compact groups and finite-dimensional real \
  vector spaces."

/-- **Blocker `B-D7-MANIFOLD-BOUNDARY`.** The boundary is available only as a set
(`ModelWithCorners.boundary`): there is no boundary manifold, no induced orientation, no induced
boundary measure, and no outward unit normal field. -/
def BlockerManifoldBoundary : String :=
  "B-D7-MANIFOLD-BOUNDARY: ModelWithCorners.boundary I M is only a Set M; there is no Boundary \
  manifold, no induced orientation of the boundary, no induced boundary measure, no collar \
  neighbourhood, and no outward unit normal field."

/-- **Blocker `B-D7-MANIFOLD-DIVERGENCE`.** There is no metric divergence of a vector field on a
Riemannian manifold (`div X = tr ∇X`) and no metric normal pairing `⟨X, n⟩`. -/
def BlockerManifoldDivergence : String :=
  "B-D7-MANIFOLD-DIVERGENCE: no metric divergence of a vector field on a Riemannian manifold \
  (div X = tr nabla X) and no metric pairing of a vector field with an outward unit normal; \
  mathlib has mfderiv but not the covariant derivative or its trace."

theorem BlockerStokes_ne_nil : BlockerStokes ≠ "" := by
  unfold BlockerStokes; simp

theorem BlockerRiemannianVolumeMeasure_ne_nil : BlockerRiemannianVolumeMeasure ≠ "" := by
  unfold BlockerRiemannianVolumeMeasure; simp

theorem BlockerManifoldBoundary_ne_nil : BlockerManifoldBoundary ≠ "" := by
  unfold BlockerManifoldBoundary; simp

theorem BlockerManifoldDivergence_ne_nil : BlockerManifoldDivergence ≠ "" := by
  unfold BlockerManifoldDivergence; simp

/-! ## The schematic Riemannian divergence datum -/

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]

/-- **A schematic divergence datum on a smooth manifold.** It collects the four objects whose
construction is blocked: the volume measure, the boundary measure, the divergence operator on
vector fields, and the metric pairing with the outward unit normal.

The fields are plain data; the geometric properties that make the datum *Riemannian* are recorded
separately in `IsRiemannianDivergenceDatum`, so that the blocked statement
`SmoothManifoldDivergenceTheoremStatement` is a statement **about** a Riemannian divergence datum
rather than an assertion that one exists. -/
structure ManifoldDivergenceDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] where
  /-- The Riemannian volume measure (missing: `BlockerRiemannianVolumeMeasure`). -/
  volume : Measure M
  /-- The measure induced on the boundary (missing: `BlockerManifoldBoundary`). -/
  boundaryMeasure : Measure M
  /-- The divergence of a vector field (missing: `BlockerManifoldDivergence`). -/
  divergence : (∀ x : M, TangentSpace I x) → M → ℝ
  /-- The metric pairing of a vector field with the outward unit normal
  (missing: `BlockerManifoldDivergence`). -/
  normalPairing : (∀ x : M, TangentSpace I x) → M → ℝ

/-- **The defining properties of a Riemannian divergence datum.** These are the properties that
the missing constructions (volume measure, boundary measure, divergence, normal pairing) would
have to satisfy; the divergence theorem is then the statement that the integral identity holds for
every such datum. Each conjunct is a genuine geometric requirement:

* the volume measure is positive on nonempty open sets and finite on compact sets;
* the boundary measure is supported on `ModelWithCorners.boundary I M`;
* the normal pairing is supported on the boundary;
* the divergence is `ℝ`-linear and satisfies the Leibniz rule
  `div (f • X) = f * div X + df (X)` for smooth `f`;
* the normal pairing is `ℝ`-linear. -/
def IsRiemannianDivergenceDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (D : ManifoldDivergenceDatum I M) : Prop :=
  (∀ s : Set M, IsOpen s → s.Nonempty → 0 < D.volume s) ∧
  (∀ K : Set M, IsCompact K → D.volume K < ⊤) ∧
  (∀ s : Set M, Disjoint s (ModelWithCorners.boundary (I := I) M) → D.boundaryMeasure s = 0) ∧
  (∀ (X : ∀ x : M, TangentSpace I x) (x : M),
    x ∉ ModelWithCorners.boundary (I := I) M → D.normalPairing X x = 0) ∧
  (∀ (X Y : ∀ x : M, TangentSpace I x) (a b : ℝ) (x : M),
    D.divergence (fun y => a • X y + b • Y y) x = a * D.divergence X x + b * D.divergence Y x) ∧
  (∀ (f : M → ℝ) (X : ∀ x : M, TangentSpace I x) (x : M),
    ContMDiff I 𝓘(ℝ) (1 : WithTop ℕ∞) f →
      D.divergence (fun y => f y • X y) x
        = f x * D.divergence X x + (show ℝ from mfderiv I 𝓘(ℝ) f x (X x))) ∧
  (∀ (X Y : ∀ x : M, TangentSpace I x) (a b : ℝ) (x : M),
    D.normalPairing (fun y => a • X y + b • Y y) x = a * D.normalPairing X x + b * D.normalPairing Y x)

/-! ## The blocked statement -/

/-- **BLOCKED (`BlockerStokes`, `BlockerRiemannianVolumeMeasure`, `BlockerManifoldBoundary`,
`BlockerManifoldDivergence`).** The **smooth-manifold divergence theorem**: for a Riemannian
divergence datum on an `n`-dimensional smooth Riemannian manifold with boundary, and for every
integrable vector field `X`,

`∫_M div X dvol = ∫_{∂M} ⟨X, n⟩ dσ`,

i.e. the integral of the divergence of `X` against the Riemannian volume measure equals the flux
of `X` through the boundary against the induced boundary measure.

This is a `Prop` with no proof. The Euclidean box case is available in mathlib
(`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`); what is missing is the Stokes
theorem / chart-and-partition-of-unity transfer together with the construction of the volume
measure, the boundary measure, the divergence, and the normal pairing (see the named blockers and
`MissingMathlibDependencies`). -/
def SmoothManifoldDivergenceTheoremStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [PseudoEMetricSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (TangentSpace I : M → Type uE)],
    ∀ D : ManifoldDivergenceDatum I M, IsRiemannianDivergenceDatum I M D →
      ∀ X : ∀ x : M, TangentSpace I x,
        Integrable (fun x => D.divergence X x) D.volume →
        Integrable (fun x => D.normalPairing X x) D.boundaryMeasure →
        ∫ x, D.divergence X x ∂D.volume = ∫ x, D.normalPairing X x ∂D.boundaryMeasure

/-- The Riemannian divergence datum is inhabited by the zero datum, so the structures above are
not vacuous. The *geometric* content is the predicate `IsRiemannianDivergenceDatum`, which the
zero datum does not satisfy (its volume measure is not positive on open sets). -/
noncomputable def ManifoldDivergenceDatum.zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] : ManifoldDivergenceDatum I M where
  volume := 0
  boundaryMeasure := 0
  divergence := fun _ _ => 0
  normalPairing := fun _ _ => 0

/-- The zero datum is not Riemannian, because its volume measure is not positive on nonempty open
sets. This separates the data contract from the geometric predicate. -/
theorem ManifoldDivergenceDatum.not_isRiemannian_zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (h : ∃ s : Set M, IsOpen s ∧ s.Nonempty) :
    ¬IsRiemannianDivergenceDatum I M (ManifoldDivergenceDatum.zero I M) := by
  rintro ⟨hpos, _⟩
  obtain ⟨s, hs, hne⟩ := h
  have := hpos s hs hne
  simp [ManifoldDivergenceDatum.zero] at this

/-- **The geometric predicate is consistent.** On an empty manifold the zero datum satisfies
`IsRiemannianDivergenceDatum`, since all of its conditions quantify over points or nonempty open
sets of an empty type. The construction of a datum satisfying the predicate on a *nonempty*
Riemannian manifold is precisely the blocked content (`BlockerRiemannianVolumeMeasure`,
`BlockerManifoldBoundary`, `BlockerManifoldDivergence`). -/
theorem ManifoldDivergenceDatum.isRiemannian_zero_of_isEmpty (I : ModelWithCorners ℝ E H)
    (M : Type uM) [IsEmpty M] [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] :
    IsRiemannianDivergenceDatum I M (ManifoldDivergenceDatum.zero I M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ hne
    obtain ⟨x, _⟩ := hne
    exact isEmptyElim x
  · intro K _
    simp [ManifoldDivergenceDatum.zero]
  · intro s _
    simp [ManifoldDivergenceDatum.zero]
  · intro X x
    exact isEmptyElim x
  · intro X Y a b x
    exact isEmptyElim x
  · intro f X x
    exact isEmptyElim x
  · intro X Y a b x
    exact isEmptyElim x

/-! ## Exact missing mathlib dependencies -/

/-- The exact mathlib declarations/structures missing for the smooth-manifold divergence theorem, at
the pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`. -/
def MissingMathlibDependencies : List String :=
  [ "Stokes' theorem for differential forms on manifolds: `∫_M dω = ∫_{∂M} ω`; mathlib has no \
    integration of top-degree forms on manifolds and no Stokes theorem.",
    "Riemannian volume measure: no global Riemannian volume form on the tangent bundle, no density \
    `sqrt(det g)`, and no partition-of-unity gluing of local densities into a measure.",
    "Boundary manifold: `ModelWithCorners.boundary I M` is only a set; there is no boundary \
    manifold, no induced orientation, no induced boundary measure, no collar neighbourhood, and no \
    outward unit normal field.",
    "Metric divergence: no covariant derivative `nabla X` and no trace `div X = tr (nabla X)` for a \
    vector field on a Riemannian manifold.",
    "Metric normal pairing `⟨X, n⟩`: no outward unit normal field and no Riemannian pairing of a \
    vector field with it along the boundary.",
    "Chart/partition-of-unity transfer: mathlib has the Euclidean box divergence theorem \
    `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`, but no transfer of it to a \
    manifold by charts, local trivializations, and a smooth partition of unity.",
    "Integration on manifolds: no Bochner integral of densities with respect to a Riemannian volume \
    measure and no change-of-variables formula for manifold charts beyond the linear \
    finite-dimensional one." ]

/-- The mathlib declarations that are present and reused by the blocked statement. -/
def PresentMathlibDependencies : List String :=
  [ "MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable: the Euclidean box divergence \
    theorem on `[a, b] ⊆ ℝⁿ⁺¹`.",
    "ModelWithCorners.boundary and the interior/boundary point API \
    (Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary).",
    "mfderiv, ContMDiff, TangentSpace, RiemannianBundle, IsRiemannianManifold.",
    "Measure.addHaar and Measure.IsAddHaarMeasure on finite-dimensional real vector spaces and \
    locally compact groups.",
    "MeasureTheory.Measure and the Bochner integral on an arbitrary measurable space." ]

theorem MissingMathlibDependencies_ne_nil : MissingMathlibDependencies ≠ [] := by
  unfold MissingMathlibDependencies
  simp

theorem MissingMathlibDependencies_length : MissingMathlibDependencies.length = 7 := rfl

theorem PresentMathlibDependencies_ne_nil : PresentMathlibDependencies ≠ [] := by
  unfold PresentMathlibDependencies
  simp

theorem PresentMathlibDependencies_length : PresentMathlibDependencies.length = 5 := rfl

end Poincare.D7.Divergence
