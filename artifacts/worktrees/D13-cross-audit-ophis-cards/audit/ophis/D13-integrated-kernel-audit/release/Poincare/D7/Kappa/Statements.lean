/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing, part 3: state-only statements and the named missing-input
ledger.**

The conditional assembly of `Poincare.D7.Kappa.Basic` and `Poincare.D7.Kappa.EntropyBridge`
proves the order-algebraic/comparison skeleton.  The **full Perelman no-local-collapsing
argument** is not formalized: it needs the Ricci-flow PDE, the conjugate heat kernel, the
reduced-length/L-exponential calculus, Perelman's Jacobian comparison, the blow-up/compactness
argument and the rigidity of ancient solutions.  This file fixes the full statement as an
explicit, state-only `Prop` and names every missing analytic input.

* `PerelmanNoncollapsingConclusion M μ K` — the conclusion `∃ κ r₀, KappaNoncollapsingCertificate`.
* `fullPerelmanNoncollapsing M μ K FlowHypotheses` — the state-only `Prop`
  `FlowHypotheses → PerelmanNoncollapsingConclusion`; it is definitionally the D3
  `missingKappaNoncollapsing` statement, which is checked below.
* `fullPerelmanNoncollapsing_of_comparisonData` / `…_of_entropy_and_comparison` — the
  kernel-checked **reduction** of the state-only statement to the assembled comparison data
  (and to the D7 entropy interface plus the comparison hypothesis).  These theorems show
  exactly what is missing: the comparison data, not the logical structure.
* `perelmanNoncollapsingDependencies` — the named ledger of twelve missing analytic inputs,
  reusing the `MissingDependency` record of the accepted `D7-hamilton-short-time` layer.
* `BlockerBallVolumeComparison`, `BlockerAncientSolutionRigidity`,
  `BlockerEntropyNormalisation`, `BlockerUniformKappa` — named blockers.

Every unproved input is a `Prop`/structure field or a `String` ledger entry; there is no
axiom, no `sorry`, no `unsafe`, no `native_decide` and no `proof_wanted` in this file.
-/

import Poincare.D7.Kappa.EntropyBridge
import Poincare.Longrun.Topology.MissingTheorems
import Poincare.D7.ShortTime.Statements

open MeasureTheory Set
open scoped ENNReal

namespace Poincare
namespace D7
namespace Kappa

open Poincare.Longrun.Topology
open Poincare.Longrun.Entropy
open Poincare.D7.ShortTime

noncomputable section

universe u

/-! ## 1. The state-only conclusion -/

/-- **The full Perelman noncollapsing conclusion.**  There exist a positive constant `κ` and a
positive scale `r₀` such that every curvature-bounded ball of radius `r ≤ r₀` has volume at
least `κ r³` (the D3 `KappaNoncollapsingCertificate`). -/
def PerelmanNoncollapsingConclusion (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) : Prop :=
  ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀

/-- **Checked shape lemma.**  The conclusion unfolds to its certificate form. -/
theorem perelmanNoncollapsingConclusion_iff {M : Type*} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) (K : CurvatureBoundedOn M) :
    PerelmanNoncollapsingConclusion M μ K ↔
      ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀ :=
  Iff.rfl

/-- **State-only `Prop`: the full Perelman no-local-collapsing theorem.**  Under the
normalized Ricci-flow hypotheses `FlowHypotheses` (a `Prop` parameter, because the flow is not
formalized), a κ-noncollapsing certificate exists.  The named missing analytic inputs are
listed in `perelmanNoncollapsingDependencies`. -/
def fullPerelmanNoncollapsing (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) : Prop :=
  FlowHypotheses → PerelmanNoncollapsingConclusion M μ K

/-- **Checked shape lemma.**  The state-only statement unfolds to its implication form. -/
theorem fullPerelmanNoncollapsing_iff {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) :
    fullPerelmanNoncollapsing M μ K FlowHypotheses ↔
      (FlowHypotheses → PerelmanNoncollapsingConclusion M μ K) :=
  Iff.rfl

/-- **Checked identification with the D3 statement-only target.**  The full Perelman
statement is exactly the D3 `missingKappaNoncollapsing` statement of
`Poincare.Longrun.Topology.MissingTheorems`, i.e. the D3 ledger entry `K1`. -/
theorem fullPerelmanNoncollapsing_iff_missingKappaNoncollapsing
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (FlowHypotheses : Prop) :
    fullPerelmanNoncollapsing M μ K FlowHypotheses ↔
      missingKappaNoncollapsing μ K FlowHypotheses :=
  Iff.rfl

/-! ## 2. Checked reductions of the state-only statement -/

/-- **Checked reduction (comparison data).**  Once the assembled comparison data are
supplied, the state-only statement holds.  This isolates the missing content of the full
argument in `KappaComparisonData`: the reduced-volume certificate, the uniform lower bound,
the comparison function and the ball-volume comparison hypothesis. -/
theorem fullPerelmanNoncollapsing_of_comparisonData
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {κ r₀ : ℝ}
    (D : KappaComparisonData M μ K E κ r₀) (FlowHypotheses : Prop) :
    fullPerelmanNoncollapsing M μ K FlowHypotheses :=
  fun _ => ⟨κ, r₀, D.toKappaCertificate.toD3⟩

/-- **Checked reduction (D7 entropy interface plus comparison).**  The D7
`PerelmanWMuKernelHypotheses` (conjugate-heat certificate, first variation, regularity,
reduced-volume envelope) together with the explicit comparison data imply the full
noncollapsing conclusion, hence the state-only statement.  Every hypothesis appears
explicitly in the signature. -/
theorem fullPerelmanNoncollapsing_of_entropy_and_comparison
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {X : Type u} [MeasurableSpace X] {μX : Measure X}
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] {fam : ι → ℝ → EntropyData X μX}
    (H : Poincare.D7.Monotonicity.PerelmanWMuKernelHypotheses F fam) (φ : ℝ → ℝ)
    {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ H.reducedVolume.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K H.reducedVolume φ r₀)
    (FlowHypotheses : Prop) :
    fullPerelmanNoncollapsing M μ K FlowHypotheses :=
  fun _ => ⟨κ, r₀,
    Poincare.D7.Kappa.kappaNoncollapsing_of_perelmanWMu H φ hκ hr₀ hτ₀ hscale hv₀ hv
      hφmono hφ comparison⟩

/-- **Checked reduction of the D3 entropy-route missing theorem.**  The D3 statement
`missingKappaNoncollapsingOfMuMonotonicity` (entropy monotonicity plus flow hypotheses imply
`K1`) holds as soon as the comparison data are supplied; the entropy-monotonicity and flow
hypotheses are the two `Prop` parameters of that statement. -/
theorem missingKappaNoncollapsingOfMuMonotonicity_of_comparisonData
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {κ r₀ : ℝ}
    (D : KappaComparisonData M μ K E κ r₀) (MuMonotone FlowHypotheses : Prop) :
    missingKappaNoncollapsingOfMuMonotonicity μ K MuMonotone FlowHypotheses :=
  fun _ _ => ⟨κ, r₀, D.toKappaCertificate.toD3⟩

/-! ## 3. The named missing-input ledger -/

/-- **Blocker `B-D7-KNC-COMPARISON`.**  The ball-volume comparison is an explicit hypothesis
of the assembly; its analytic proof is missing. -/
def BlockerBallVolumeComparison : String :=
  "B-D7-KNC-COMPARISON: the comparison 'a collapsed ball at scale r forces a small reduced \
  volume at backward time r^2' is an explicit field of BallVolumeComparison; the analytic \
  proof needs the conjugate heat kernel, the reduced-length estimates and the blow-up \
  (compactness) argument, none of which is in the pinned mathlib."

/-- **Blocker `B-D7-KNC-RIGIDITY`.**  The rigidity/equality case of the reduced volume is
missing. -/
def BlockerAncientSolutionRigidity : String :=
  "B-D7-KNC-RIGIDITY: the equality/rigidity case (a complete ancient solution with bounded \
  curvature and constant reduced volume is the Gaussian shrinking soliton, up to Euclidean \
  space) is needed to make the limiting argument quantitative; it is not formalized."

/-- **Blocker `B-D7-KNC-NORMALISATION`.**  The reduced-volume normalisation and the
identification of the limiting reduced volume with the asymptotic volume ratio are missing. -/
def BlockerEntropyNormalisation : String :=
  "B-D7-KNC-NORMALISATION: the normalisation of the reduced volume (the (4 pi tau)^{-n/2} \
  Gaussian factor and the base-time value) and the identification of its large-time limit \
  with the asymptotic volume ratio of the initial metric are not formalized; they are what \
  makes kappa depend only on g(0) and T."

/-- **Blocker `B-D7-KNC-UNIFORM-KAPPA`.**  The extraction of a single uniform `κ` from the
monotonicity and the comparison is missing at the level of the genuine flow. -/
def BlockerUniformKappa : String :=
  "B-D7-KNC-UNIFORM-KAPPA: the reduction of the two alternatives of Perelman's argument \
  (either the curvature bound fails, or the ball is non-collapsed) to a single constant \
  kappa depending only on g(0) and T requires the full contradiction/compactness argument; \
  the assembly here takes the uniform lower bound v0 <= Vtilde(tau0) as an explicit field."

theorem BlockerBallVolumeComparison_ne_nil : BlockerBallVolumeComparison ≠ "" := by
  simp [BlockerBallVolumeComparison]

theorem BlockerAncientSolutionRigidity_ne_nil : BlockerAncientSolutionRigidity ≠ "" := by
  simp [BlockerAncientSolutionRigidity]

theorem BlockerEntropyNormalisation_ne_nil : BlockerEntropyNormalisation ≠ "" := by
  simp [BlockerEntropyNormalisation]

theorem BlockerUniformKappa_ne_nil : BlockerUniformKappa ≠ "" := by
  simp [BlockerUniformKappa]

/-- **The named missing inputs of the full Perelman noncollapsing argument.**  Each entry
names a standard ingredient of the proof and records why it is absent from the pinned mathlib
and from this development. -/
def perelmanNoncollapsingDependencies : List MissingDependency := [
  ⟨"NCF-1 normalized Ricci flow",
   "A smooth solution of the normalized Ricci flow on a closed 3-manifold over a time \
    interval [0, T]. The pinned mathlib has no Ricci-flow PDE, no quasilinear parabolic \
    existence theorem and no manifold Ricci tensor."⟩,
  ⟨"NCF-2 curvature bound",
   "The hypothesis |Rm| <= r^{-2} on the ball B(x,r). The pinned mathlib has no Riemann \
    curvature tensor, so the predicate K is opaque and the bound is carried as a hypothesis \
    K x r."⟩,
  ⟨"NCF-3 conjugate heat kernel",
   "Existence, positivity, unit total mass and parabolic regularity of the conjugate heat \
    kernel (the fundamental solution of the backward heat equation) that defines W, the \
    reduced length and the reduced volume."⟩,
  ⟨"NCF-4 reduced length and L-exponential map",
   "Existence and regularity of L-length minimisers, the L-geodesic equation, and the \
    L-exponential map with its Jacobian. Only the finite-dimensional Gaussian model has an \
    explicit minimiser in this development (D7-reduced-length-volume)."⟩,
  ⟨"NCF-5 Jacobian comparison",
   "Perelman's Jacobian comparison: the Jacobian of the L-exponential map is bounded above by \
    the Gaussian comparison Jacobian under a Ricci curvature lower bound. It is a state-only \
    Prop in D7-reduced-length-volume."⟩,
  ⟨"NCF-6 reduced-length differential inequality",
   "The inequality l_tau - Delta l + |grad l|^2 - R + n/(2 tau) >= 0 for the reduced length, \
    with its Laplacian, gradient and scalar-curvature terms. The layer keeps only the \
    surviving consequence l' >= -n/(2 tau) as the Gaussian-density certificate field."⟩,
  ⟨"NCF-7 differentiation under the integral",
   "Dominated convergence / differentiation under the integral sign for the reduced-volume \
    integral, producing the derivative sign from the pointwise differential inequality."⟩,
  ⟨"NCF-8 reduced-volume monotonicity",
   "The reduced volume Vtilde is nonincreasing in backward time. It is represented here by \
    the explicit certificate fields of ReducedVolumeCertificate (derivative sign and \
    nonnegativity), whose discharge needs NCF-4 to NCF-7."⟩,
  ⟨"NCF-9 ball-volume comparison",
   "The comparison used by Perelman's argument: a collapsed ball at scale r forces the \
    reduced volume at backward time r^2 to be small. Supplied as the explicit structure \
    BallVolumeComparison; its analytic proof is missing."⟩,
  ⟨"NCF-10 ancient solution rigidity",
   "Rigidity of the equality case: a complete ancient solution with bounded curvature and \
    constant reduced volume is the Gaussian shrinking soliton (up to Euclidean space). \
    Needed to extract a uniform constant from the limiting argument."⟩,
  ⟨"NCF-11 no-local-collapsing compactness",
   "The pointed compactness/blow-up argument that extracts a complete ancient limit solution \
    from a sequence of collapsing balls with bounded curvature, including the smoothing and \
    convergence estimates."⟩,
  ⟨"NCF-12 normalisation and uniform kappa",
   "The normalisation of the reduced volume and the identification of its large-time limit \
    with the asymptotic volume ratio of the initial metric, yielding a kappa > 0 that depends \
    only on g(0) and T. The assembly takes the uniform lower bound v0 <= Vtilde(tau0) as an \
    explicit field instead."⟩
]

theorem perelmanNoncollapsingDependencies_length :
    perelmanNoncollapsingDependencies.length = 12 := rfl

theorem perelmanNoncollapsingDependencies_ne_nil :
    perelmanNoncollapsingDependencies ≠ [] := by
  simp [perelmanNoncollapsingDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem perelmanNoncollapsingDependencies_all_named :
    ∀ d ∈ perelmanNoncollapsingDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [perelmanNoncollapsingDependencies]

/-- The four named blockers of the conditional κ-noncollapsing assembly. -/
def perelmanNoncollapsingBlockers : List String := [
  BlockerBallVolumeComparison,
  BlockerAncientSolutionRigidity,
  BlockerEntropyNormalisation,
  BlockerUniformKappa
]

theorem perelmanNoncollapsingBlockers_length : perelmanNoncollapsingBlockers.length = 4 := rfl

theorem perelmanNoncollapsingBlockers_ne_nil : perelmanNoncollapsingBlockers ≠ [] := by
  simp [perelmanNoncollapsingBlockers]

/-- Every named blocker is a nonempty string. -/
theorem perelmanNoncollapsingBlockers_all_named :
    ∀ b ∈ perelmanNoncollapsingBlockers, b ≠ "" := by
  simp [perelmanNoncollapsingBlockers, BlockerBallVolumeComparison,
    BlockerAncientSolutionRigidity, BlockerEntropyNormalisation, BlockerUniformKappa]

end

end Kappa
end D7
end Poincare
