import Poincare.D7.Reduced.Basic
import Poincare.D7.Reduced.Certificate
import Poincare.D7.ShortTime.Statements

/-!
# Poincare.D7.Reduced.Statements

**D7 reduced length / reduced volume layer, part 3: state-only propositions and the
missing-dependency ledger.**

The finite-dimensional `L`-length layer of `Poincare.D7.Reduced.Basic` and the reduced-volume
certificates of `Poincare.D7.Reduced.Certificate` are complete.  The analytic content of
Perelman's reduced length / reduced volume step (P-REDUCED-VOL in the program ledger) is **not**
formalized: the pinned mathlib has no path space with a compactness or lower-semicontinuity
argument, no first/second variation calculus for the `L`-length, no `L`-exponential map, and no
manifold Ricci-flow PDE.  This file records that content as explicit, unproved propositions over
the stated interface, together with a kernel-checked ledger of the missing dependencies.

* `LMinimizerExistence F p` — **state-only `Prop`**: for every `q` and every `τ > 0` there is an
  admissible path from `p` to `q` over `[0, τ]` whose `L`-length is minimal.
* `JacobianComparisonInterface E`, `JacobianComparison J` — **state-only `Prop`**: the Jacobian of
  the `L`-exponential map is bounded above by the comparison (Gaussian) Jacobian.
* `ReducedVolumeMonotonicity Ṽ` — **state-only `Prop`**: the reduced volume is nonincreasing in
  backward time.  This is the declaration `missingReducedVolumeMonotonicity` of the program
  ledger; the certificate layer proves the order-algebraic consequences of the explicit analytic
  fields, but the fields themselves are not discharged.
* `reducedVolumeDependencies` — the named ledger of missing analytic inputs, reusing the
  `MissingDependency` record of the accepted `D7-hamilton-short-time` layer.
* `BlockerLMinimizerExistence`, `BlockerJacobianComparison`, `BlockerReducedVolumeMonotonicity` —
  the named blockers.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file: the
state-only content is a `def ... : Prop` (a well-formed statement), never an axiom.
-/

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Poincare
namespace D7
namespace Reduced

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. State-only proposition: existence of `L`-length minimisers -/

/-- **State-only `Prop`: existence of `L`-length minimisers.**  For every endpoint `q` and every
positive backward time `τ` there is an admissible path from `p` to `q` over `[0, τ]` whose
`L`-length is at most that of every other admissible path.

This is not proved for the general interface.  The finite-dimensional Gaussian model proves it
(`Poincare.D7.Reduced.Gaussian.gaussianLMinimizerExistence`), which shows the statement is
consistent and not vacuous; the general case needs the path-space compactness and
lower-semicontinuity inputs listed in `reducedVolumeDependencies`. -/
def LMinimizerExistence (F : MetricFlowInterface E) (p : E) : Prop :=
  ∀ (q : E) (τ : ℝ), 0 < τ → ∃ P : LPath F p q τ, IsLMinimizer P

/-- **State-only `Prop`: monotonicity of the reduced volume.**  The reduced volume functional
`V` is nonincreasing on positive backward times.  This is the program-ledger declaration
`missingReducedVolumeMonotonicity`. -/
def ReducedVolumeMonotonicity (V : ℝ → ℝ) : Prop :=
  AntitoneOn V (Set.Ioi 0)

/-- The certificate fields of `ReducedVolumeCertificate` prove the state-only monotonicity
statement for the certified volume functional.  The general statement remains unproved because the
fields are not discharged. -/
theorem reducedVolumeMonotonicity_of_certificate (C : ReducedVolumeCertificate E) :
    ReducedVolumeMonotonicity C.volume :=
  C.antitoneOn

/-! ## 2. State-only proposition: Jacobian comparison -/

/-- **Interface for the Jacobian comparison.**  The intended instantiation is: `jacobian τ x` is
the Jacobian of the `L`-exponential map from the base point at backward time `τ` evaluated at `x`,
and `comparison τ x` is the corresponding Euclidean/Gaussian comparison Jacobian
`(4πτ)^{-n/2} e^{-|x|²/(4τ)}` (up to a normalising factor).  The intended instantiation is not
constructed: the pinned mathlib has no `L`-exponential map and no Jacobian of a map between
manifolds. -/
structure JacobianComparisonInterface (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  /-- The underlying metric-flow interface. -/
  flow : MetricFlowInterface E
  /-- The Jacobian of the `L`-exponential map at backward time `τ`. -/
  jacobian : ℝ → E → ℝ
  /-- The comparison Jacobian at backward time `τ`. -/
  comparison : ℝ → E → ℝ
  /-- The Jacobian is nonnegative at positive backward times. -/
  jacobian_nonneg : ∀ (τ : ℝ) (x : E), 0 < τ → 0 ≤ jacobian τ x
  /-- The comparison Jacobian is positive at positive backward times. -/
  comparison_pos : ∀ (τ : ℝ) (x : E), 0 < τ → 0 < comparison τ x

/-- **State-only `Prop`: Jacobian comparison.**  The Jacobian of the `L`-exponential map is at most
the comparison Jacobian at every positive backward time.  This is Perelman's Jacobian comparison
input to the reduced-volume monotonicity proof; it is not proved here. -/
def JacobianComparison (J : JacobianComparisonInterface E) : Prop :=
  ∀ (τ : ℝ) (x : E), 0 < τ → J.jacobian τ x ≤ J.comparison τ x

/-! ## 3. The missing-dependency ledger -/

/-- **Blocker `B-D7-RLV-MINIMIZER`.**  Existence of `L`-length minimisers for the general
interface is not available. -/
def BlockerLMinimizerExistence : String :=
  "B-D7-RLV-MINIMIZER: no path space with a compactness or lower-semicontinuity theorem for the \
  L-length functional in the pinned mathlib; minimiser existence is a state-only proposition, \
  proved only for the finite-dimensional Gaussian model."

/-- **Blocker `B-D7-RLV-JACOBIAN`.**  The Jacobian comparison for the `L`-exponential map is not
available. -/
def BlockerJacobianComparison : String :=
  "B-D7-RLV-JACOBIAN: no L-exponential map, no Jacobian of a map between manifolds, and no second \
  variation / index-form calculus for the L-length in the pinned mathlib; the comparison is a \
  state-only proposition."

/-- **Blocker `B-D7-RLV-MONOTONICITY`.**  Reduced-volume monotonicity is not available. -/
def BlockerReducedVolumeMonotonicity : String :=
  "B-D7-RLV-MONOTONICITY: reduced-volume monotonicity is represented by explicit certificate \
  fields (derivative sign, nonnegativity) whose analytic discharge needs the L-geodesic \
  differential inequality, differentiation under the integral, and a Jacobian comparison."

theorem BlockerLMinimizerExistence_ne_nil : BlockerLMinimizerExistence ≠ "" := by
  simp [BlockerLMinimizerExistence]

theorem BlockerJacobianComparison_ne_nil : BlockerJacobianComparison ≠ "" := by
  simp [BlockerJacobianComparison]

theorem BlockerReducedVolumeMonotonicity_ne_nil :
    BlockerReducedVolumeMonotonicity ≠ "" := by
  simp [BlockerReducedVolumeMonotonicity]

/-- **The reduced length / reduced volume dependencies.**  Each entry names a standard ingredient
of Perelman's construction and records why it is absent. -/
def reducedVolumeDependencies : List ShortTime.MissingDependency := [
  ⟨"RLV-1 path space",
   "A path space for curves in a manifold, with the compactness (Arzela-Ascoli) or convexity \
    argument that produces a minimiser of the L-length. The layer works with an explicit \
    admissible-path structure instead; existence for the general interface is state-only."⟩,
  ⟨"RLV-2 L-geodesic equation",
   "The first variation of the L-length, the resulting L-geodesic ODE, and its solvability. Only \
    the finite-dimensional Gaussian model has an explicit geodesic here."⟩,
  ⟨"RLV-3 minimiser regularity",
   "Regularity of a minimiser (smooth on (0, tau], continuous at the base time) and the endpoint \
    value l(0, tau) = 0. No variational regularity theory is available."⟩,
  ⟨"RLV-4 L-exponential map",
   "The L-exponential map based at (p, 0), its differentiability and the Jacobian used in the \
    Jacobian comparison. The map is not constructed."⟩,
  ⟨"RLV-5 second variation and index form",
   "The second variation of the L-length, the L-index form and its nonnegativity along a \
    minimiser. This is the input to both Jacobian comparison and the differential inequality \
    for l."⟩,
  ⟨"RLV-6 Jacobian comparison",
   "Perelman's Jacobian comparison: the Jacobian of the L-exponential map is bounded above by the \
    Gaussian comparison Jacobian under a Ricci curvature lower bound. Stated here as a Prop."⟩,
  ⟨"RLV-7 reduced-length differential inequality",
   "The inequality l_tau - Delta l + |grad l|^2 - R + n/(2 tau) >= 0 satisfied by the reduced \
    length, with its Laplacian, gradient and scalar curvature terms. The layer keeps the \
    surviving consequence l' >= -n/(2 tau) as the field `derivative_lower` of the Gaussian \
    density certificate."⟩,
  ⟨"RLV-8 differentiation under the integral",
   "Dominated convergence / differentiation under the integral sign for the reduced volume \
    integral, producing the derivative sign from the pointwise inequality. The certificate takes \
    the derivative as data."⟩,
  ⟨"RLV-9 manifold metric flow",
   "Smooth Riemannian metrics on a closed manifold, the manifold Ricci tensor, the covariant \
    derivative calculus and bounded curvature. Inherited from the blocked Poincare.D7.Curvature \
    layer; the pinned mathlib has no manifold Ricci flow."⟩,
  ⟨"RLV-10 Gaussian normalisation",
   "The normalisation integral of the Gaussian weight, (4 pi tau)^{-n/2} times the integral of \
    exp(-|x|^2/(4 tau)), equal to one. Not needed for the finite-dimensional computation of the \
    reduced length in the Gaussian model, but needed for the reduced volume normalisation."⟩
]

theorem reducedVolumeDependencies_length : reducedVolumeDependencies.length = 10 := rfl

theorem reducedVolumeDependencies_ne_nil : reducedVolumeDependencies ≠ [] := by
  simp [reducedVolumeDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem reducedVolumeDependencies_all_named :
    ∀ d ∈ reducedVolumeDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [reducedVolumeDependencies]

end

end Reduced
end D7
end Poincare
