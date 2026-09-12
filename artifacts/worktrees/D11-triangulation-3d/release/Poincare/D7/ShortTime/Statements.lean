import Poincare.D7.ShortTime.Equivalence

/-!
# Poincare.D7.ShortTime.Statements

**D7 Hamilton 1982 short-time existence layer, part 6: the state-only analytic statements and
the missing-dependency ledger.**

The finite-dimensional matrix model of `Poincare.D7.ShortTime.Equivalence` proves the *algebraic*
DeTurck equivalence. The analytic content of Hamilton's 1982 theorem is **not** formalized: the
pinned mathlib has no quasilinear parabolic PDE theory and no manifold Ricci flow. This file
records that content as two explicit, unproved propositions over an abstract continuum interface,
together with a kernel-checked ledger of the missing dependencies.

* `DeTurckParabolicProblem` — abstract data of the continuum problem: a normed state space of
  metrics, the Ricci and DeTurck right-hand sides, the gauge transform (pullback along the
  DeTurck diffeomorphism flow), and the solution predicates, which are *defined* to be the
  corresponding `HasDerivAt` equations. The intended instantiation is the space of smooth
  Riemannian metrics on a closed manifold, with `deTurckOp` the quasilinear operator
  `-2 Ric(g) - Bᵀ g - g B`; that instantiation is not constructed.
* `DeTurckShortTimeExistence P` — **state-only `Prop`**: there is `T > 0` and a solution of the
  modified flow on `(0,T)` with the prescribed initial metric. This is Hamilton's parabolic
  short-time existence statement. It is *not* proved; `quasilinearParabolicDependencies` lists
  the missing analytic inputs.
* `DeTurckToRicciConversion P` — **state-only `Prop`**: every solution of the modified flow on
  `(0,T)` pulls back along the gauge flow to a solution of the Ricci flow on `(0,T)`.
* `matrixProblem D C` — the finite-dimensional matrix model as an instance of the abstract
  interface; `matrixProblem_deTurckToRicciConversion` **proves** the conversion `Prop` for this
  instance (it is the algebraic equivalence of `Equivalence.lean`), which shows the statement is
  consistent and not vacuous. The general continuum conversion statement remains state-only.
* `MissingDependency`, `quasilinearParabolicDependencies`, and the `Blocker...` strings — the
  named ledger of what is missing.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file: the
state-only content is a `def ... : Prop` (a well-formed statement), never an axiom.
-/

open scoped Matrix

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace ShortTime

noncomputable section

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

/-! ## The abstract continuum interface -/

/-- **Abstract continuum data of the Ricci--DeTurck flow problem.**

The intended instantiation is: `MetricState` = smooth Riemannian metrics on a closed manifold
`M`, `ricciOp g = -2 Ric(g)`, `deTurckOp t g = -2 Ric(g) - Bᵀ g - g B` with `B` the velocity
gradient of the DeTurck vector field, `gaugeTransform u t = φ_t^* (u t)` for the flow `φ_t` of
the DeTurck field, and the solution predicates the corresponding evolution equations. The
manifold structure is deliberately abstracted away: it is exactly the part that is missing from
the pinned mathlib. -/
structure DeTurckParabolicProblem where
  /-- The state space of metrics. -/
  MetricState : Type
  /-- Metric states form a normed additive group (in the finite-dimensional model, matrices). -/
  [normedAddCommGroup : NormedAddCommGroup MetricState]
  /-- Metric states form a real normed space. -/
  [normedSpace : NormedSpace ℝ MetricState]
  /-- The Ricci flow right-hand side `-2 Ric`. -/
  ricciOp : MetricState → MetricState
  /-- The DeTurck-modified right-hand side at time `t`, including the gauge correction. -/
  deTurckOp : ℝ → MetricState → MetricState
  /-- The prescribed initial metric. -/
  initial : MetricState
  /-- Pullback along the gauge diffeomorphism flow: `(u, t) ↦ φ_t^* (u t)`. -/
  gaugeTransform : (ℝ → MetricState) → ℝ → MetricState
  /-- The gauge transform is the identity at time zero (`φ_0 = id`). -/
  gaugeTransform_zero : ∀ u : ℝ → MetricState, gaugeTransform u 0 = u 0
  /-- `IsDeTurckSolutionOn T u` means `u` solves the modified flow on `(0,T)`. -/
  IsDeTurckSolutionOn : ℝ → (ℝ → MetricState) → Prop
  /-- `IsRicciFlowOn T u` means `u` solves the Ricci flow on `(0,T)`. -/
  IsRicciFlowOn : ℝ → (ℝ → MetricState) → Prop
  /-- The DeTurck solution predicate is the modified evolution equation. -/
  isDeTurckSolutionOn_iff : ∀ (T : ℝ) (u : ℝ → MetricState),
    IsDeTurckSolutionOn T u ↔
      ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt u (deTurckOp t (u t)) t
  /-- The Ricci flow solution predicate is the Ricci evolution equation. -/
  isRicciFlowOn_iff : ∀ (T : ℝ) (u : ℝ → MetricState),
    IsRicciFlowOn T u ↔
      ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt u (ricciOp (u t)) t

/-- **State-only `Prop`: parabolic short-time existence for the Ricci--DeTurck flow.** There is
a time `T > 0` and a solution `u` of the modified flow on `(0,T)` with `u 0 = initial`.

This is the analytic heart of Hamilton 1982 and is **not** proved here. In the finite-dimensional
matrix model the analogous statement is a Picard--Lindelöf existence theorem under a Lipschitz
hypothesis, but the continuum operator is quasilinear and unbounded, so the PDE statement needs
the inputs listed in `quasilinearParabolicDependencies`. -/
def DeTurckShortTimeExistence (P : DeTurckParabolicProblem) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → P.MetricState,
    u 0 = P.initial ∧ P.IsDeTurckSolutionOn T u

/-- **State-only `Prop`: conversion of a Ricci--DeTurck solution back to a Ricci flow.** Every
solution of the modified flow on `(0,T)` pulls back along the gauge flow to a solution of the
Ricci flow on `(0,T)`.

For the finite-dimensional matrix model this is the algebraic DeTurck equivalence and is proved
below (`matrixProblem_deTurckToRicciConversion`). For the continuum problem it is the geometric
DeTurck trick and remains state-only here, because it needs the manifold-level diffeomorphism
flow and the manifold-level gauge covariance of the Ricci tensor. -/
def DeTurckToRicciConversion (P : DeTurckParabolicProblem) : Prop :=
  ∀ (T : ℝ) (u : ℝ → P.MetricState), P.IsDeTurckSolutionOn T u →
    P.IsRicciFlowOn T (fun t => P.gaugeTransform u t)

/-! ## The finite-dimensional matrix model as an instance -/

variable {n : ℕ}

/-- **The finite-dimensional matrix model as an instance of the abstract interface.** This is a
consistency and non-vacuity check: the abstract data are inhabited by the matrix model, and the
conversion `Prop` for this instance is proved by the algebraic equivalence theorem. -/
def matrixProblem (D : RicciFlowData n) (C : DeTurckCertificate D) :
    DeTurckParabolicProblem where
  MetricState := Matrix (Fin n) (Fin n) ℝ
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  ricciOp := fun G => (-2 : ℝ) • D.ricci G
  deTurckOp := fun t G => deTurckRHS D (C.gaugeField t) G
  initial := D.metric 0
  gaugeTransform := fun u t => (C.gauge t)ᵀ * u t * C.gauge t
  gaugeTransform_zero := by
    intro u
    simp [C.gauge_zero]
  IsDeTurckSolutionOn := fun T u =>
    ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt u (deTurckRHS D (C.gaugeField t) (u t)) t
  IsRicciFlowOn := fun T u =>
    ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt u ((-2 : ℝ) • D.ricci (u t)) t
  isDeTurckSolutionOn_iff := fun T u => Iff.rfl
  isRicciFlowOn_iff := fun T u => Iff.rfl

/-- **The conversion `Prop` holds for the matrix instance**, by the algebraic DeTurck
equivalence. This shows the state-only conversion statement is consistent with the proved
algebraic layer. -/
theorem matrixProblem_deTurckToRicciConversion (D : RicciFlowData n)
    (C : DeTurckCertificate D) :
    DeTurckToRicciConversion (matrixProblem D C) := by
  intro T u hu t ht
  exact C.pullback_hasDerivAt_of_Ioo u T hu ht

/-! ## The missing-dependency ledger -/

/-- A named missing analytic input for the parabolic short-time existence theorem. -/
structure MissingDependency where
  /-- Short name of the missing input. -/
  name : String
  /-- Why it is missing / what exactly is needed. -/
  reason : String
  deriving Repr, Inhabited

/-- **Blocker `B-D7-HST-PARABOLIC-EXISTENCE`.** The continuum short-time existence theorem for
the quasilinear DeTurck flow is not available: the pinned mathlib has no quasilinear parabolic
PDE theory. -/
def BlockerDeTurckShortTime : String :=
  "B-D7-HST-PARABOLIC-EXISTENCE: no quasilinear parabolic short-time existence theorem in the \
  pinned mathlib; the DeTurck operator is an unbounded quasilinear second-order operator and \
  needs linearization, strict parabolicity, a priori estimates and a Nash-Moser / inverse \
  function theorem on tame Frechet spaces."

/-- **Blocker `B-D7-HST-CONVERSION`.** The continuum conversion of a DeTurck solution back to a
Ricci flow is not available: it needs the manifold-level diffeomorphism flow of the DeTurck
vector field and the manifold-level gauge covariance of the Ricci tensor. -/
def BlockerDeTurckConversion : String :=
  "B-D7-HST-CONVERSION: no manifold-level diffeomorphism flow of a time-dependent vector field \
  with smooth dependence on the initial condition, and no manifold-level Ricci tensor; the \
  pointwise gauge covariance is only available as an abstract field in the matrix model."

theorem BlockerDeTurckShortTime_ne_nil : BlockerDeTurckShortTime ≠ "" := by
  simp [BlockerDeTurckShortTime]

theorem BlockerDeTurckConversion_ne_nil : BlockerDeTurckConversion ≠ "" := by
  simp [BlockerDeTurckConversion]

/-- **The quasilinear parabolic dependencies.** Each entry names a standard ingredient of the
short-time existence proof for a quasilinear parabolic equation and records why it is absent. -/
def quasilinearParabolicDependencies : List MissingDependency := [
  ⟨"QP-1 linearization",
   "The derivative of the Ricci tensor in the direction of a metric variation is a second-order \
    linear operator; the linearization (and its principal symbol) is not constructed. Needed to \
    read off parabolicity."⟩,
  ⟨"QP-2 strict parabolicity",
   "The DeTurck gauge removes the diffeomorphism-invariance degeneracy so that the principal \
    symbol becomes the Laplacian and the operator is strictly parabolic. Strict parabolicity of \
    the linearized operator is not formalized."⟩,
  ⟨"QP-3 a priori estimates",
   "Schauder / Sobolev (energy) estimates for the linear parabolic operator on the relevant \
    function spaces, with constants uniform on a short time interval. No PDE estimate library."⟩,
  ⟨"QP-4 quasilinear short-time existence",
   "A short-time existence theorem for quasilinear parabolic systems (Nash-Moser / inverse \
    function theorem on tame Frechet spaces, or a fixed-point argument on a scale of Banach \
    spaces). This is the exact content of Hamilton 1982, Section 3."⟩,
  ⟨"QP-5 regularity and continuation",
   "Higher regularity (parabolic smoothing) of the solution and the continuation criterion for \
    the maximal existence time; needed to produce a smooth solution on an open time interval."⟩,
  ⟨"QP-6 diffeomorphism flow",
   "The flow of the time-dependent DeTurck vector field on a closed manifold, its smooth \
    dependence on the initial condition, and the pullback action on metrics. The matrix model \
    replaces this by a family of matrices with an explicit ODE."⟩,
  ⟨"QP-7 manifold gauge covariance",
   "Diffeomorphism invariance of the Ricci tensor: pullback of the Ricci tensor along a \
    diffeomorphism equals the Ricci tensor of the pulled-back metric. The matrix model assumes \
    the pointwise algebraic shadow as the field `ricci_congruence` of `RicciFlowData`."⟩,
  ⟨"QP-8 manifold Ricci flow theory",
   "Smooth Riemannian metrics on a manifold, the manifold Ricci tensor, and the covariant \
    derivative calculus. Inherited from the blocked `Poincare.D7.Curvature` layer; the pinned \
    mathlib has no `CovariantDerivative.curvature`."⟩
]

theorem quasilinearParabolicDependencies_length :
    quasilinearParabolicDependencies.length = 8 := rfl

theorem quasilinearParabolicDependencies_ne_nil :
    quasilinearParabolicDependencies ≠ [] := by
  simp [quasilinearParabolicDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem quasilinearParabolicDependencies_all_named :
    ∀ d ∈ quasilinearParabolicDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [quasilinearParabolicDependencies]

end

end ShortTime
end D7
end Poincare
