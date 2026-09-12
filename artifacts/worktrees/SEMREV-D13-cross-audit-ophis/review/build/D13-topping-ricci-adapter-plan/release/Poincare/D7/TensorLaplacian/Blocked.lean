import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.TensorLaplacian.Blocked

**D7 tensor Laplacian layer, part 5: the smooth commutation formulas and the smooth
scalar-curvature evolution identity as explicit unproved `Prop`s, with the exact missing mathlib
dependencies.**

Per the task rules, everything this layer cannot prove is recorded as an **explicit unproved
`Prop`** with a **named blocker**. There is no incomplete proof anywhere in the D7 sources; the
items below are `def ... : Prop` (well-formed statements) together with `def ... : String`
blockers and lists of the exact missing declarations.

## What mathlib (pinned revision `7974e751bece493b6ff508039423ca9fa2452fa8`) does provide

* `CovariantDerivative I E (TangentSpace I)` — a covariant derivative on the tangent bundle of a
  smooth manifold;
* `CovariantDerivative.leviCivitaConnection` — a choice of Levi-Civita connection on the tangent
  bundle of a Riemannian manifold, with metric compatibility and torsion-freeness;
* `mfderiv`, `ContMDiff`, `TangentSpace`, `RiemannianBundle`, `IsRiemannianManifold`,
  `ModelWithCorners`, `IsManifold`.

## What is missing (the blockers)

1. **`BlockerSmoothTensorBundle`** — the smooth tensor bundle `T^{r,s}M` and its smooth sections;
   mathlib has `TangentSpace` and vector bundles, but no tensor bundle of mixed type.
2. **`BlockerSmoothTensorConnection`** — the covariant derivative on a tensor bundle induced by
   the Levi-Civita connection (the Leibniz rule on each tensor slot).
3. **`BlockerSmoothRoughLaplacian`** — the rough (connection) Laplacian `∇*∇` on smooth tensor
   fields, i.e. the metric trace of the second covariant derivative.
4. **`BlockerManifoldCurvature`** — the Riemann curvature endomorphism of a manifold connection
   and its action on tensor fields, together with the Ricci endomorphism. Mathlib has no
   curvature of a manifold connection at this revision; the D7 curvature layer is a
   finite-dimensional algebraic model.
5. **`BlockerSmoothCommutation`** — the smooth commutation formula for the rough Laplacian.
6. **`BlockerSmoothScalarEvolution`** — the smooth scalar-curvature evolution identity
   `∂ₜ R = Δ R + 2 |Ric|²` under the Ricci-flow equation `∂ₜ g = -2 Ric`, together with the
   Lichnerowicz trace variation and the contracted Bianchi identity it uses.

The exact missing declarations are listed in `MissingMathlibDependencies`; the pieces that are
available and reused are listed in `PresentMathlibDependencies`. Each blocker string is checked
nonempty (`..._ne_nil`), so the named blocker is an auditable kernel declaration rather than prose
only.

All other proofs in this layer are complete; the `#print axioms` audit reports only the standard
Lean dependencies.
-/

open Bundle Manifold

open scoped Bundle Manifold

universe uE uH uM uT

namespace Poincare
namespace D7
namespace TensorLaplacian

/-! ## Named blockers -/

/-- **Blocker `B-D7-TL-SMOOTH-TENSOR-BUNDLE`.** The smooth tensor bundle of mixed type and its
smooth sections are missing. -/
def BlockerSmoothTensorBundle : String :=
  "B-D7-TL-SMOOTH-TENSOR-BUNDLE: no smooth tensor bundle T^{r,s}M of mixed type and no type of \
  smooth sections of it; mathlib has TangentSpace and vector bundles but no tensor bundle."

/-- **Blocker `B-D7-TL-SMOOTH-TENSOR-CONNECTION`.** The covariant derivative on a tensor bundle
induced by the Levi-Civita connection is missing. -/
def BlockerSmoothTensorConnection : String :=
  "B-D7-TL-SMOOTH-TENSOR-CONNECTION: no covariant derivative on a tensor bundle induced by the \
  Levi-Civita connection; the Leibniz rule on each tensor slot is not formalized."

/-- **Blocker `B-D7-TL-SMOOTH-ROUGH-LAPLACIAN`.** The rough (connection) Laplacian on smooth
tensor fields is missing. -/
def BlockerSmoothRoughLaplacian : String :=
  "B-D7-TL-SMOOTH-ROUGH-LAPLACIAN: no rough (connection) Laplacian nabla^* nabla on smooth tensor \
  fields and no metric trace of the second covariant derivative."

/-- **Blocker `B-D7-TL-MANIFOLD-CURVATURE`.** The manifold Riemann curvature endomorphism acting
on tensor fields and its Ricci contraction are missing; the D7 curvature layer is a
finite-dimensional algebraic model. -/
def BlockerManifoldCurvature : String :=
  "B-D7-TL-MANIFOLD-CURVATURE: no Riemann curvature endomorphism of a manifold connection, no \
  action of it on tensor fields, and no Ricci endomorphism; the D7 curvature and Ricci layers are \
  algebraic finite-dimensional models."

/-- **Blocker `B-D7-TL-SMOOTH-COMMUTATION`.** The smooth commutation formula for the rough
Laplacian is missing. -/
def BlockerSmoothCommutation : String :=
  "B-D7-TL-SMOOTH-COMMUTATION: no smooth commutation formula \
  Delta(nabla_X T) - nabla_X(Delta T) = 2 Ric(X) T for the rough Laplacian on tensor fields."

/-- **Blocker `B-D7-TL-SMOOTH-SCALAR-EVOLUTION`.** The smooth scalar-curvature evolution
identity and its inputs (Lichnerowicz trace variation, contracted Bianchi identity) are missing. -/
def BlockerSmoothScalarEvolution : String :=
  "B-D7-TL-SMOOTH-SCALAR-EVOLUTION: no smooth scalar-curvature evolution \
  d/dt R = Delta R + 2 |Ric|^2 under d/dt g = -2 Ric, and no Lichnerowicz trace variation or \
  contracted Bianchi identity on a smooth manifold."

theorem BlockerSmoothTensorBundle_ne_nil : BlockerSmoothTensorBundle ≠ "" := by
  unfold BlockerSmoothTensorBundle; simp

theorem BlockerSmoothTensorConnection_ne_nil : BlockerSmoothTensorConnection ≠ "" := by
  unfold BlockerSmoothTensorConnection; simp

theorem BlockerSmoothRoughLaplacian_ne_nil : BlockerSmoothRoughLaplacian ≠ "" := by
  unfold BlockerSmoothRoughLaplacian; simp

theorem BlockerManifoldCurvature_ne_nil : BlockerManifoldCurvature ≠ "" := by
  unfold BlockerManifoldCurvature; simp

theorem BlockerSmoothCommutation_ne_nil : BlockerSmoothCommutation ≠ "" := by
  unfold BlockerSmoothCommutation; simp

theorem BlockerSmoothScalarEvolution_ne_nil : BlockerSmoothScalarEvolution ≠ "" := by
  unfold BlockerSmoothScalarEvolution; simp

/-! ## The schematic smooth tensor-Laplacian datum -/

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]

/-- **A schematic smooth tensor-Laplacian datum.** It collects the operators whose smooth
constructions are blocked: the covariant derivative on tensor fields, the rough Laplacian, the
curvature action on tensor fields, the Ricci action, and the abstract Lie bracket used in the
curvature certificate. The tensor-field type `Tf` and its smoothness predicate are part of the
datum; the geometric properties are recorded separately in `IsSmoothTensorLaplacianDatum`. -/
structure SmoothTensorLaplacianDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf] where
  /-- The metric pairing at each point. -/
  metricInner : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- The covariant derivative of a tensor field in a direction (missing:
  `BlockerSmoothTensorConnection`). -/
  tensorNabla : Tf → (x : M) → TangentSpace I x → Tf
  /-- The rough Laplacian on tensor fields (missing: `BlockerSmoothRoughLaplacian`). -/
  roughLaplacian : Tf → Tf
  /-- The curvature action `R(X,Y)s` on tensor fields (missing: `BlockerManifoldCurvature`). -/
  curvatureAction : (x : M) → TangentSpace I x → TangentSpace I x → Tf → Tf
  /-- The Ricci action on tensor fields (missing: `BlockerManifoldCurvature`). -/
  ricciAction : (x : M) → TangentSpace I x → Tf → Tf
  /-- The abstract Lie bracket of vector fields (missing smooth Lie-bracket formalization). -/
  lieBracket : (x : M) → TangentSpace I x → TangentSpace I x → TangentSpace I x
  /-- The number of frame directions (missing: `BlockerSmoothTensorBundle`). -/
  dim : ℕ
  /-- A frame field used for the frame-trace form of the commutation formula. -/
  frame : (x : M) → Fin dim → TangentSpace I x
  /-- The smoothness predicate on tensor fields (missing: `BlockerSmoothTensorBundle`). -/
  isSmoothTensorField : Tf → Prop

/-- **The defining properties of a smooth tensor-Laplacian datum.** These are the properties that
the missing constructions would have to satisfy: the curvature certificate, the smooth
commutation formula, and preservation of smooth tensor fields by the covariant derivative. -/
def IsSmoothTensorLaplacianDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf]
    (D : SmoothTensorLaplacianDatum I M Tf) : Prop :=
  (∀ (s : Tf) (x : M) (X Y : TangentSpace I x),
    D.tensorNabla (D.tensorNabla s x Y) x X - D.tensorNabla (D.tensorNabla s x X) x Y
        - D.tensorNabla s x (D.lieBracket x X Y)
      = D.curvatureAction x X Y s) ∧
  (∀ (s : Tf) (x : M) (X : TangentSpace I x),
    D.roughLaplacian (D.tensorNabla s x X) - D.tensorNabla (D.roughLaplacian s) x X
      = (2 : ℝ) • D.ricciAction x X s) ∧
  (∀ (s : Tf) (x : M) (X : TangentSpace I x), D.isSmoothTensorField s →
    D.isSmoothTensorField (D.tensorNabla s x X)) ∧
  (∀ s : Tf, D.isSmoothTensorField s → D.isSmoothTensorField (D.roughLaplacian s))

/-! ## The blocked smooth commutation statements -/

/-- **BLOCKED (`BlockerSmoothTensorBundle`, `BlockerSmoothTensorConnection`,
`BlockerSmoothRoughLaplacian`, `BlockerManifoldCurvature`, `BlockerSmoothCommutation`).** The
**smooth curvature certificate**: for every smooth tensor field `s`,
`∇_X∇_Y s - ∇_Y∇_X s - ∇_{[X,Y]} s = R(X,Y)s`.

This is a `Prop` with no proof; the finite-dimensional certificate is the `TensorConnectionData`
field of `Poincare.D7.TensorLaplacian.Basic`. -/
def SmoothCurvatureCertificateStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf]
    (D : SmoothTensorLaplacianDatum I M Tf), IsSmoothTensorLaplacianDatum I M Tf D →
      ∀ (s : Tf) (x : M) (X Y : TangentSpace I x),
        D.tensorNabla (D.tensorNabla s x Y) x X - D.tensorNabla (D.tensorNabla s x X) x Y
            - D.tensorNabla s x (D.lieBracket x X Y)
          = D.curvatureAction x X Y s

/-- **BLOCKED (`BlockerSmoothTensorBundle`, `BlockerSmoothTensorConnection`,
`BlockerSmoothRoughLaplacian`, `BlockerManifoldCurvature`, `BlockerSmoothCommutation`).** The
**smooth commutation formula for the rough Laplacian**:
`Δ(∇_X s) - ∇_X(Δ s) = 2 Ric(X)s`.

This is a `Prop` with no proof; the finite-dimensional formula is
`Poincare.D7.TensorLaplacian.TensorConnectionData.roughLaplacian_commutator_of_parallel` (with the
stated parallel-curvature certificate) and its Ricci form
`...roughLaplacian_commutator_ricci`. -/
def SmoothCommutationStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf]
    (D : SmoothTensorLaplacianDatum I M Tf), IsSmoothTensorLaplacianDatum I M Tf D →
      ∀ (s : Tf) (x : M) (X : TangentSpace I x),
        D.roughLaplacian (D.tensorNabla s x X) - D.tensorNabla (D.roughLaplacian s) x X
          = (2 : ℝ) • D.ricciAction x X s

/-- **BLOCKED (`BlockerSmoothTensorBundle`, `BlockerSmoothTensorConnection`,
`BlockerSmoothRoughLaplacian`, `BlockerManifoldCurvature`, `BlockerSmoothCommutation`).** The
**smooth Ricci form of the commutation formula**: the frame trace of the commutators is
`2 scal • s`; this is the smooth counterpart of
`Poincare.D7.TensorLaplacian.TensorConnectionData.roughLaplacian_commutator_frame_trace`. -/
def SmoothFrameTraceCommutationStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf]
    (scal : M → ℝ) (D : SmoothTensorLaplacianDatum I M Tf), IsSmoothTensorLaplacianDatum I M Tf D →
      ∀ (s : Tf) (x : M),
        (∑ i : Fin D.dim,
            (D.roughLaplacian (D.tensorNabla s x (D.frame x i))
              - D.tensorNabla (D.roughLaplacian s) x (D.frame x i)))
          = (2 * scal x) • s

/-! ## The blocked smooth scalar-curvature evolution statement -/

/-- **A schematic smooth scalar-curvature evolution datum.** It collects the scalar fields of the
identity `∂ₜ R = ΔR + 2 |Ric|²` together with the metric velocity and the Ricci form. The
geometric properties are recorded in `IsSmoothScalarEvolutionDatum`. -/
structure SmoothScalarEvolutionDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The scalar curvature path. -/
  scal : ℝ → M → ℝ
  /-- Its time derivative `∂ₜ R`. -/
  scalarDeriv : ℝ → M → ℝ
  /-- The Laplacian `ΔR`. -/
  laplaceScal : ℝ → M → ℝ
  /-- The Laplacian of the velocity trace `Δ(tr h)`. -/
  lapTrace : ℝ → M → ℝ
  /-- The double divergence `∇ⁱ∇ʲhᵢⱼ`. -/
  divdivH : ℝ → M → ℝ
  /-- The pairing `⟨h, Ric⟩`. -/
  pairingH : ℝ → M → ℝ
  /-- The Frobenius norm squared `|Ric|²`. -/
  ricciNormSq : ℝ → M → ℝ
  /-- The metric velocity `h = ∂ₜ g`. -/
  metricVelocity : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- The Ricci form. -/
  ricciForm : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

/-- **The defining properties of a smooth scalar-evolution datum**: the stated Ricci-flow
equation `∂ₜ g = -2 Ric`, the flow equation `∂ₜ R = scalarDeriv`, the Lichnerowicz trace
variation, the linearity `Δ(tr h) = -2 ΔR`, the contracted Bianchi identity
`∇ⁱ∇ʲhᵢⱼ = -ΔR`, and the pairing `⟨h, Ric⟩ = -2 |Ric|²`. -/
def IsSmoothScalarEvolutionDatum (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] (D : SmoothScalarEvolutionDatum I M) : Prop :=
  (∀ (t : ℝ) (x : M) (X Y : TangentSpace I x),
    D.metricVelocity t x X Y = -2 * D.ricciForm t x X Y) ∧
  (∀ (t : ℝ) (x : M), HasDerivAt (fun s : ℝ => D.scal s x) (D.scalarDeriv t x) t) ∧
  (∀ (t : ℝ) (x : M),
    D.scalarDeriv t x = -D.lapTrace t x + D.divdivH t x - D.pairingH t x) ∧
  (∀ (t : ℝ) (x : M), D.lapTrace t x = -2 * D.laplaceScal t x) ∧
  (∀ (t : ℝ) (x : M), D.divdivH t x = -D.laplaceScal t x) ∧
  (∀ (t : ℝ) (x : M), D.pairingH t x = -2 * D.ricciNormSq t x)

/-- **BLOCKED (`BlockerSmoothTensorBundle`, `BlockerSmoothTensorConnection`,
`BlockerSmoothRoughLaplacian`, `BlockerManifoldCurvature`, `BlockerSmoothScalarEvolution`).** The
**smooth scalar-curvature evolution identity** under the Ricci-flow equation `∂ₜ g = -2 Ric`:

`∂ₜ R = ΔR + 2 |Ric|²`.

This is a `Prop` with no proof; the finite-dimensional identity between interface fields is
`Poincare.D7.TensorLaplacian.ScalarEvolutionCertificate.scalarDeriv_eq`. -/
def SmoothScalarEvolutionStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (D : SmoothScalarEvolutionDatum I M), IsSmoothScalarEvolutionDatum I M D →
      ∀ (t : ℝ) (x : M),
        D.scalarDeriv t x = D.laplaceScal t x + 2 * D.ricciNormSq t x

/-! ## Consistency: the zero data satisfy the predicates -/

/-- The zero smooth tensor-Laplacian datum: all operators are zero and every tensor field is
declared smooth. It shows that the datum structure is inhabited and that the predicates are
satisfiable. -/
noncomputable def SmoothTensorLaplacianDatum.zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf] :
    SmoothTensorLaplacianDatum I M Tf where
  metricInner := fun _ => 0
  tensorNabla := fun _ _ _ => 0
  roughLaplacian := fun _ => 0
  curvatureAction := fun _ _ _ _ => 0
  ricciAction := fun _ _ _ => 0
  lieBracket := fun _ _ _ => 0
  dim := 0
  frame := fun _ i => i.elim0
  isSmoothTensorField := fun _ => True

/-- **The predicate is consistent**: the zero datum satisfies
`IsSmoothTensorLaplacianDatum` (the covariant derivative and rough Laplacian are the identity
there, so all equations reduce to `s - s = 0`). -/
theorem SmoothTensorLaplacianDatum.isSmooth_zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] (Tf : Type uT) [AddCommGroup Tf] [Module ℝ Tf] :
    IsSmoothTensorLaplacianDatum I M Tf (SmoothTensorLaplacianDatum.zero I M Tf) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x X Y
    simp [SmoothTensorLaplacianDatum.zero]
  · intro s x X
    simp [SmoothTensorLaplacianDatum.zero]
  · intro s x X _
    trivial
  · intro s _
    trivial

/-- The zero smooth scalar-evolution datum. -/
noncomputable def SmoothScalarEvolutionDatum.zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : SmoothScalarEvolutionDatum I M where
  scal := fun _ _ => 0
  scalarDeriv := fun _ _ => 0
  laplaceScal := fun _ _ => 0
  lapTrace := fun _ _ => 0
  divdivH := fun _ _ => 0
  pairingH := fun _ _ => 0
  ricciNormSq := fun _ _ => 0
  metricVelocity := fun _ _ => 0
  ricciForm := fun _ _ => 0

/-- **The scalar predicate is consistent**: the zero datum satisfies
`IsSmoothScalarEvolutionDatum`. -/
theorem SmoothScalarEvolutionDatum.isSmooth_zero (I : ModelWithCorners ℝ E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] :
    IsSmoothScalarEvolutionDatum I M (SmoothScalarEvolutionDatum.zero I M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x X Y; simp [SmoothScalarEvolutionDatum.zero]
  · intro t x; simpa [SmoothScalarEvolutionDatum.zero] using hasDerivAt_const (x := t) (c := 0)
  · intro t x; simp [SmoothScalarEvolutionDatum.zero]
  · intro t x; simp [SmoothScalarEvolutionDatum.zero]
  · intro t x; simp [SmoothScalarEvolutionDatum.zero]
  · intro t x; simp [SmoothScalarEvolutionDatum.zero]

/-! ## Exact missing mathlib dependencies -/

/-- The exact mathlib declarations/structures missing for the smooth commutation formula and the
smooth scalar-curvature evolution identity, at the pinned revision
`7974e751bece493b6ff508039423ca9fa2452fa8`. -/
def MissingMathlibDependencies : List String :=
  [ "Smooth tensor bundle of mixed type `T^{r,s}M` and its smooth sections (mathlib has \
    `TangentSpace` and vector bundles but no mixed tensor bundle).",
    "Covariant derivative on a tensor bundle induced by the Levi-Civita connection (the Leibniz \
    rule on each tensor slot).",
    "Rough (connection) Laplacian `nabla^* nabla` on smooth tensor fields, as the metric trace of \
    the second covariant derivative.",
    "Riemann curvature endomorphism of a manifold connection acting on tensor fields, and its \
    Ricci endomorphism; the D7 `Poincare.D7.Curvature` and `Poincare.D7.RicciScalar` layers are \
    finite-dimensional algebraic models.",
    "Smooth Lie bracket of vector fields as a global tensor operation with the Leibniz rule \
    against the covariant derivative.",
    "Smooth commutation formula \
    `Delta(nabla_X T) - nabla_X(Delta T) = 2 Ric(X) T` for the rough Laplacian on tensor fields.",
    "Lichnerowicz variation of the Ricci/scalar curvature under `d/dt g = h`, and the contracted \
    Bianchi identity `nabla^i nabla^j h_ij = -Delta R` for `h = -2 Ric`.",
    "Smooth scalar-curvature evolution identity `d/dt R = Delta R + 2 |Ric|^2` under the \
    Ricci-flow equation `d/dt g = -2 Ric`." ]

/-- The mathlib declarations that are present and reused by the blocked statements. -/
def PresentMathlibDependencies : List String :=
  [ "CovariantDerivative I E (TangentSpace I): a covariant derivative on the tangent bundle of a \
    smooth manifold.",
    "CovariantDerivative.leviCivitaConnection: a choice of Levi-Civita connection on a Riemannian \
    manifold, with IsLeviCivitaConnection and its metric-compatibility and torsion-free proofs.",
    "mfderiv, ContMDiff, TangentSpace, RiemannianBundle, IsRiemannianManifold.",
    "ModelWithCorners, IsManifold, ChartedSpace and the smooth-manifold structure.",
    "The D7 finite-dimensional tensor Laplacian layer: TensorConnectionData, the rough Laplacian \
    and the commutation formulas in `Poincare.D7.TensorLaplacian`." ]

theorem MissingMathlibDependencies_ne_nil : MissingMathlibDependencies ≠ [] := by
  unfold MissingMathlibDependencies
  simp

theorem MissingMathlibDependencies_length : MissingMathlibDependencies.length = 8 := rfl

theorem PresentMathlibDependencies_ne_nil : PresentMathlibDependencies ≠ [] := by
  unfold PresentMathlibDependencies
  simp

theorem PresentMathlibDependencies_length : PresentMathlibDependencies.length = 5 := rfl

end TensorLaplacian
end D7
end Poincare
