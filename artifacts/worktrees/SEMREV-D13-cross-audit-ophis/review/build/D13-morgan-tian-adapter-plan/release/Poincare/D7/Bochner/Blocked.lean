/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.Blocked

**D7 Bochner / Weitzenböck layer, part 5: the smooth Bochner formula as an explicit unproved
`Prop`, with the exact missing mathlib dependencies.**

Per the task rules, everything this layer cannot prove is recorded as an **explicit unproved
`Prop`** with a **named blocker**. There is no incomplete proof anywhere in the D7 sources; the
items below are `def ... : Prop` (well-formed statements) together with `def ... : String` blockers
and lists of the exact missing declarations.

## What mathlib (pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`) does provide

* `CovariantDerivative I E (TangentSpace I)` — a covariant derivative on the tangent bundle of a
  smooth manifold;
* `CovariantDerivative.leviCivitaConnection` — a choice of Levi-Civita connection on the tangent
  bundle of a Riemannian manifold, with
  `CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection` proving that it is metric
  compatible and torsion free;
* `mfderiv`, `ContMDiff`, `TangentSpace`, `RiemannianBundle`, `IsRiemannianManifold`,
  `ModelWithCorners`, `IsManifold`.

## What is missing (the blockers)

1. **`BlockerHessian`** — the second covariant derivative (Hessian) of a function,
   `∇ df = ∇²f`, as a section of `T*M ⊗ T*M`, and its squared norm `|∇²f|²`.
2. **`BlockerLaplaceBeltrami`** — the Laplace–Beltrami operator `Δf = tr_g ∇²f` on functions.
3. **`BlockerRoughLaplacian`** — the rough (connection) Laplacian `∇*∇` on 1-forms, together with
   its pairing against `df`.
4. **`BlockerManifoldCurvature`** — the Riemann curvature endomorphism and its Ricci contraction
   on a smooth manifold. Mathlib has no curvature of a manifold connection at this revision; the
   D7 curvature layer (`Poincare.D7.Curvature`, `Poincare.D7.RicciScalar`) is a purely algebraic
   finite-dimensional model, not a manifold-level construction.
5. **`BlockerBochnerWeitzenbock`** — the Bochner–Weitzenböck identity itself, i.e. the pointwise
   decomposition `Δ₁ = ∇*∇ + Ric` and the scalar formula
   `Δ(|∇f|²) = 2 |∇²f|² + 2 ⟨∇f, ∇Δf⟩ + 2 Ric(∇f, ∇f)`.

The exact missing declarations are listed in `MissingMathlibDependencies`; the pieces that are
available and reused are listed in `PresentMathlibDependencies`. Each blocker string is checked
nonempty (`..._ne_nil`), so the named blocker is an auditable kernel declaration rather than prose
only.

All other proofs in this layer are complete; the `#print axioms` audit reports only the standard
Lean dependencies.
-/

open Bundle Manifold

open scoped Bundle Manifold

universe uE uH uM

namespace Poincare.D7.Bochner

/-! ## Named blockers -/

/-- **Blocker `B-D7-BOCHNER-HESSIAN`.** The second covariant derivative (Hessian) of a function is
missing: there is no `∇²f` as a section of `T*M ⊗ T*M` and no squared norm `|∇²f|²`. -/
def BlockerHessian : String :=
  "B-D7-BOCHNER-HESSIAN: mathlib has CovariantDerivative but no second covariant derivative \
  (Hessian) of a function, no section of the tensor bundle T*M ⊗ T*M, and no squared norm \
  |nabla^2 f|^2 of the Hessian."

/-- **Blocker `B-D7-BOCHNER-LAPLACE-BELTRAMI`.** The Laplace–Beltrami operator on functions is
missing: there is no `Δf = tr_g ∇²f`. -/
def BlockerLaplaceBeltrami : String :=
  "B-D7-BOCHNER-LAPLACE-BELTRAMI: no Laplace-Beltrami operator on functions, no trace of the \
  Hessian against the metric, and no relation Delta f = tr_g (nabla^2 f)."

/-- **Blocker `B-D7-BOCHNER-ROUGH-LAPLACIAN`.** The rough (connection) Laplacian `∇*∇` on 1-forms
is missing, together with its pairing against the exact form `df`. -/
def BlockerRoughLaplacian : String :=
  "B-D7-BOCHNER-ROUGH-LAPLACIAN: no rough (connection) Laplacian nabla^* nabla on 1-forms, no \
  formal adjoint of the covariant derivative on forms, and no pairing of the rough Laplacian \
  against the exact form df."

/-- **Blocker `B-D7-BOCHNER-MANIFOLD-CURVATURE`.** The Riemann curvature endomorphism and its
Ricci contraction on a smooth manifold are missing. The D7 curvature layer is a finite-dimensional
algebraic model, not a manifold-level construction. -/
def BlockerManifoldCurvature : String :=
  "B-D7-BOCHNER-MANIFOLD-CURVATURE: no Riemann curvature endomorphism of a manifold connection, \
  no Ricci contraction of it, and no identification with the curvature of the Levi-Civita \
  connection; the D7 curvature and Ricci layers are algebraic finite-dimensional models."

/-- **Blocker `B-D7-BOCHNER-WEITZENBOCK`.** The Bochner–Weitzenböck identity itself is missing:
the pointwise decomposition `Δ₁ = ∇*∇ + Ric` and the scalar formula for `Δ(|∇f|²)`. -/
def BlockerBochnerWeitzenbock : String :=
  "B-D7-BOCHNER-WEITZENBOCK: no Bochner-Weitzenbock identity Delta_1 = nabla^* nabla + Ric on \
  1-forms, no scalar Bochner formula Delta(|nabla f|^2) = 2 |nabla^2 f|^2 + 2 <nabla f, nabla \
  Delta f> + 2 Ric(nabla f, nabla f), and no gradient estimate derived from it."

theorem BlockerHessian_ne_nil : BlockerHessian ≠ "" := by
  unfold BlockerHessian; simp

theorem BlockerLaplaceBeltrami_ne_nil : BlockerLaplaceBeltrami ≠ "" := by
  unfold BlockerLaplaceBeltrami; simp

theorem BlockerRoughLaplacian_ne_nil : BlockerRoughLaplacian ≠ "" := by
  unfold BlockerRoughLaplacian; simp

theorem BlockerManifoldCurvature_ne_nil : BlockerManifoldCurvature ≠ "" := by
  unfold BlockerManifoldCurvature; simp

theorem BlockerBochnerWeitzenbock_ne_nil : BlockerBochnerWeitzenbock ≠ "" := by
  unfold BlockerBochnerWeitzenbock; simp

/-! ## The schematic smooth Bochner datum -/

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]

/-- **A schematic smooth Bochner datum.** It collects the scalar quantities of the pointwise
Bochner formula on a smooth manifold together with the metric pairing and the gradient. The
geometric objects whose construction is blocked are the Laplace–Beltrami operator, the Hessian
norm, the gradient-of-Laplacian pairing, the Ricci pairing, the 1-form and rough Laplacian pairings,
and the scalar Laplacian of `|∇f|²`.

The fields are plain data; the geometric properties that make the datum *Bochner* are recorded
separately in `IsSmoothBochnerDatum`, so that the blocked statements below are statements **about**
a smooth Bochner datum rather than assertions that one exists. -/
structure SmoothBochnerDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The Riemannian metric pairing at each point. -/
  metricInner : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- The gradient of a function, the metric dual of `mfderiv`. -/
  gradient : (M → ℝ) → (x : M) → TangentSpace I x
  /-- The Laplace–Beltrami operator `Δf` on functions (missing:
  `BlockerLaplaceBeltrami`). -/
  laplaceBeltrami : (M → ℝ) → M → ℝ
  /-- The squared Hessian norm `|∇²f|²` (missing: `BlockerHessian`). -/
  hessNormSq : (M → ℝ) → M → ℝ
  /-- The pairing `⟨∇f, ∇Δf⟩` (missing: `BlockerLaplaceBeltrami`, `BlockerHessian`). -/
  gradLapPairing : (M → ℝ) → M → ℝ
  /-- The Ricci pairing `Ric(∇f, ∇f)` (missing: `BlockerManifoldCurvature`). -/
  ricciPairing : (M → ℝ) → M → ℝ
  /-- The 1-form Laplacian pairing `⟨Δ₁ df, df⟩` (missing: `BlockerBochnerWeitzenbock`). -/
  oneFormLaplacian : (M → ℝ) → M → ℝ
  /-- The rough Laplacian pairing `⟨∇*∇ df, df⟩` (missing: `BlockerRoughLaplacian`). -/
  roughLaplacian : (M → ℝ) → M → ℝ
  /-- The scalar Laplacian `Δ(|∇f|²)` (missing: `BlockerLaplaceBeltrami`). -/
  laplacianGradNormSq : (M → ℝ) → M → ℝ

/-- **The defining properties of a smooth Bochner datum.** These are the properties that the
missing constructions would have to satisfy:

* the gradient is the metric dual of `mfderiv` of a smooth function;
* the scalar Laplacian of `|∇f|²` is twice the 1-form Laplacian pairing;
* the 1-form Laplacian pairing decomposes as the rough Laplacian plus the Ricci pairing
  (Weitzenböck);
* the rough Laplacian pairing expands as `|∇²f|² + ⟨∇f, ∇Δf⟩`;
* the Ricci pairing is nonnegative (`Ric ≥ 0`);
* harmonicity `Δf = 0` forces `⟨∇f, ∇Δf⟩ = 0`. -/
def IsSmoothBochnerDatum (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] (D : SmoothBochnerDatum I M) : Prop :=
  (∀ (f : M → ℝ) (x : M), ContMDiff I 𝓘(ℝ) (1 : WithTop ℕ∞) f →
    ∀ v : TangentSpace I x,
      D.metricInner x (D.gradient f x) v = (show ℝ from mfderiv I 𝓘(ℝ) f x v)) ∧
  (∀ (f : M → ℝ) (x : M),
    D.laplacianGradNormSq f x = 2 * D.oneFormLaplacian f x) ∧
  (∀ (f : M → ℝ) (x : M),
    D.oneFormLaplacian f x = D.roughLaplacian f x + D.ricciPairing f x) ∧
  (∀ (f : M → ℝ) (x : M),
    D.roughLaplacian f x = D.hessNormSq f x + D.gradLapPairing f x) ∧
  (∀ (f : M → ℝ) (x : M), 0 ≤ D.ricciPairing f x) ∧
  (∀ (f : M → ℝ) (x : M), D.laplaceBeltrami f x = 0 → D.gradLapPairing f x = 0)

/-! ## The blocked statements -/

/-- **BLOCKED (`BlockerHessian`, `BlockerLaplaceBeltrami`, `BlockerRoughLaplacian`,
`BlockerManifoldCurvature`, `BlockerBochnerWeitzenbock`).** The **smooth scalar Bochner formula**:
for every smooth function `f` on a Riemannian manifold and every point `x`,

`Δ(|∇f|²) = 2 |∇²f|² + 2 ⟨∇f, ∇Δf⟩ + 2 Ric(∇f, ∇f)`.

This is a `Prop` with no proof. The finite-dimensional algebraic model is proved in
`Poincare.D7.Bochner.Basic` and `Poincare.D7.Bochner.GradientEstimate`; what is missing is the
construction of the geometric quantities (Hessian, Laplace–Beltrami, rough Laplacian, manifold
curvature) and the identity itself (see the named blockers and `MissingMathlibDependencies`). -/
def SmoothBochnerFormulaStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (D : SmoothBochnerDatum I M), IsSmoothBochnerDatum I M D →
      ∀ (f : M → ℝ) (x : M),
        D.laplacianGradNormSq f x
          = 2 * D.hessNormSq f x + 2 * D.gradLapPairing f x + 2 * D.ricciPairing f x

/-- **BLOCKED (`BlockerRoughLaplacian`, `BlockerManifoldCurvature`, `BlockerBochnerWeitzenbock`).**
The **smooth Weitzenböck identity** on the exact 1-form `df`: for every smooth function `f` and
every point `x`,

`⟨Δ₁ df, df⟩ = ⟨∇*∇ df, df⟩ + Ric(∇f, ∇f)`.

This is a `Prop` with no proof; the finite-dimensional identity is the `BochnerCertificate` of
`Poincare.D7.Bochner.Basic`. -/
def SmoothBochnerWeitzenbockStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (D : SmoothBochnerDatum I M), IsSmoothBochnerDatum I M D →
      ∀ (f : M → ℝ) (x : M),
        D.oneFormLaplacian f x = D.roughLaplacian f x + D.ricciPairing f x

/-- **BLOCKED (`BlockerHessian`, `BlockerLaplaceBeltrami`, `BlockerManifoldCurvature`,
`BlockerBochnerWeitzenbock`).** The **smooth gradient estimate**: under `Ric ≥ 0` and
harmonicity `Δf = 0`,

`Δ(|∇f|²) ≥ 2 |∇²f|²`.

This is a `Prop` with no proof; the finite-dimensional estimate is
`Poincare.D7.Bochner.GradientCertificate.gradient_estimate`. -/
def SmoothBochnerGradientEstimateStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (D : SmoothBochnerDatum I M), IsSmoothBochnerDatum I M D →
      ∀ (f : M → ℝ) (x : M), D.laplaceBeltrami f x = 0 →
        2 * D.hessNormSq f x ≤ D.laplacianGradNormSq f x

/-- The zero datum: all operators are zero. It shows that the datum structure is inhabited; the
geometric content is the predicate `IsSmoothBochnerDatum`. -/
noncomputable def SmoothBochnerDatum.zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : SmoothBochnerDatum I M where
  metricInner := fun _ => 0
  gradient := fun _ _ => 0
  laplaceBeltrami := fun _ _ => 0
  hessNormSq := fun _ _ => 0
  gradLapPairing := fun _ _ => 0
  ricciPairing := fun _ _ => 0
  oneFormLaplacian := fun _ _ => 0
  roughLaplacian := fun _ _ => 0
  laplacianGradNormSq := fun _ _ => 0

/-- The zero datum is not Bochner on a nonempty manifold, because the metric pairing of the zero
gradient is zero while `mfderiv` of a nonconstant function need not vanish. The construction of a
datum satisfying the predicate on a nonempty Riemannian manifold is precisely the blocked content
(`BlockerHessian`, `BlockerLaplaceBeltrami`, `BlockerRoughLaplacian`,
`BlockerManifoldCurvature`, `BlockerBochnerWeitzenbock`). -/
theorem SmoothBochnerDatum.zero_not_isSmooth_of_nontrivial (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    (h : ∃ (f : M → ℝ) (x : M) (v : TangentSpace I x),
      ContMDiff I 𝓘(ℝ) (1 : WithTop ℕ∞) f ∧ (show ℝ from mfderiv I 𝓘(ℝ) f x v) ≠ 0) :
    ¬IsSmoothBochnerDatum I M (SmoothBochnerDatum.zero I M) := by
  rintro ⟨hgrad, -⟩
  obtain ⟨f, x, v, hf, hv⟩ := h
  have hzero := hgrad f x hf v
  simp [SmoothBochnerDatum.zero] at hzero
  exact hv hzero.symm

/-- **The predicate is consistent.** On an empty manifold the zero datum satisfies
`IsSmoothBochnerDatum`, since all of its conditions quantify over points of an empty type. -/
theorem SmoothBochnerDatum.isSmooth_zero_of_isEmpty (I : ModelWithCorners ℝ E H) (M : Type uM)
    [IsEmpty M] [TopologicalSpace M] [ChartedSpace H M] :
    IsSmoothBochnerDatum I M (SmoothBochnerDatum.zero I M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f x _ v
    exact isEmptyElim x
  · intro f x
    exact isEmptyElim x
  · intro f x
    exact isEmptyElim x
  · intro f x
    exact isEmptyElim x
  · intro f x
    exact isEmptyElim x
  · intro f x _
    exact isEmptyElim x

/-! ## Exact missing mathlib dependencies -/

/-- The exact mathlib declarations/structures missing for the smooth Bochner formula, at the pinned
revision `7974e751bece493b6ff508039423ca9fa2452fa8`. -/
def MissingMathlibDependencies : List String :=
  [ "Hessian (second covariant derivative): no `nabla (nabla f)` as a section of the tensor \
    bundle `T*M ⊗ T*M`, and no squared norm `|nabla^2 f|^2`.",
    "Laplace-Beltrami operator: no `Delta f = tr_g (nabla^2 f)` on functions, and no trace of a \
    tensor field against the metric.",
    "Rough Laplacian on 1-forms: no formal adjoint `nabla^*` of the covariant derivative on forms \
    and no pairing `<nabla^* nabla df, df>`.",
    "Manifold curvature: no Riemann curvature endomorphism of a connection on a smooth manifold \
    and no Ricci contraction of it; the D7 `Poincare.D7.Curvature` and \
    `Poincare.D7.RicciScalar` layers are finite-dimensional algebraic models.",
    "Bochner-Weitzenbock identity: no pointwise decomposition `Delta_1 = nabla^* nabla + Ric` for \
    the Hodge-de Rham Laplacian on 1-forms.",
    "Scalar Bochner formula: no identity \
    `Delta(|nabla f|^2) = 2 |nabla^2 f|^2 + 2 <nabla f, nabla Delta f> + 2 Ric(nabla f, nabla f)`.",
    "Gradient estimate: no Bochner gradient estimate `Delta(|nabla f|^2) >= 2 |nabla^2 f|^2` under \
    `Ric >= 0` and `Delta f = 0`." ]

/-- The mathlib declarations that are present and reused by the blocked statements. -/
def PresentMathlibDependencies : List String :=
  [ "CovariantDerivative I E (TangentSpace I): a covariant derivative on the tangent bundle of a \
    smooth manifold.",
    "CovariantDerivative.leviCivitaConnection: a choice of Levi-Civita connection on a Riemannian \
    manifold, with IsLeviCivitaConnection and its metric-compatibility and torsion-free proofs.",
    "mfderiv, ContMDiff, TangentSpace, RiemannianBundle, IsRiemannianManifold.",
    "ModelWithCorners, IsManifold, ChartedSpace and the smooth-manifold structure.",
    "The D7 finite-dimensional Bochner certificates: BochnerCertificate and GradientCertificate in \
    `Poincare.D7.Bochner.Basic` and `Poincare.D7.Bochner.GradientEstimate`." ]

theorem MissingMathlibDependencies_ne_nil : MissingMathlibDependencies ≠ [] := by
  unfold MissingMathlibDependencies
  simp

theorem MissingMathlibDependencies_length : MissingMathlibDependencies.length = 7 := rfl

theorem PresentMathlibDependencies_ne_nil : PresentMathlibDependencies ≠ [] := by
  unfold PresentMathlibDependencies
  simp

theorem PresentMathlibDependencies_length : PresentMathlibDependencies.length = 5 := rfl

end Poincare.D7.Bochner
