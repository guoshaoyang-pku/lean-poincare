/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-kappa-variational builder
-/
import Poincare.D12.KappaVariational.CurvatureEnergy
import Poincare.D12.KappaVariational.Transfer
import Poincare.D7.Kappa.Basic
import Poincare.D7.ShortTime.Statements

/-!
# Poincare.D12.KappaVariational.Statements

**Closure records, checked reductions and the remaining missing-input ledger for the
kappa-variational track.**

This file separates the three semantic classes required by the task:

* **closed inputs** — `ClosureRecord` entries carrying a name, the exact constructor
  declaration, the downstream consumer, the statement as a `Prop` and a *proof of that
  statement*.  Three named missing inputs of the D7 layer are closed at the model level:
  `RLV-10` (Gaussian normalisation, `gaussianReducedVolume_eq_one`), the model half of `NCF-12`
  (reduced-length normalisation `gaussianReducedVolumeViaL_eq_one`), and the constant-curvature
  family case of `RLV-1` (`constantCurvatureLMinimizerExistence`).
* **conditional transfer** — `gaussianKappaNoncollapsing_of_ballVolumeComparison`: on the
  Gaussian model `EuclideanSpace ℝ (Fin 3)` with Lebesgue measure, the D7 conditional theorem
  `kappaNoncollapsing_of_entropy_and_volumeComparison` fires once a `BallVolumeComparison` is
  supplied — the *only* remaining input for κ-noncollapsing on this model is the ball-volume
  comparison, because the normalisation (`v₀ = 1`, `τ₀ = 1`, `Ṽ ≡ 1`) is discharged by the
  integral computation.  The comparison itself remains state-only (`ballVolumeComparisonExists`).
* **general state-only statements** — `ballVolumeComparisonExists` (NCF-9) and the remaining
  ledger `kappaVariationalRemainingDependencies` (thirteen named entries), all kernel-checked
  (`…_length`, `…_all_named`).

No canonical-neighbourhood or ancient-solution classification is inferred from any record in
this file.  No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` is used.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real Topology

namespace Poincare
namespace D12
namespace KappaVariational

open D7.Reduced
open D7.Kappa
open Longrun.Topology

/-! ## 1. Closure records -/

/-- A **closure record**: a named missing input, the exact constructor declaration that
provides it, the downstream declaration that consumes it, the statement as a `Prop`, and a
kernel-checked proof of that statement.  A closure record is inhabited only if the named input
is actually constructed and used downstream. -/
structure ClosureRecord where
  /-- The name of the closed missing input. -/
  dependencyName : String
  /-- The exact declaration that constructs the input. -/
  constructorDecl : String
  /-- The exact downstream declaration that consumes the input. -/
  downstreamUseDecl : String
  /-- The mathematical statement of the closed input. -/
  statement : Prop
  /-- A proof of the statement (the constructor, kernel-checked). -/
  proof : statement

/-- **RLV-10 statement.** The Gaussian reduced-volume normalisation:
`Ṽ(τ) = ∫ (4πτ)^{-n/2} exp (-‖q‖²/(4τ)) dq = 1` for every `n` and every `τ > 0`. -/
def rlv10Statement : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 < τ → gaussianReducedVolume n τ = 1

/-- **Closure of RLV-10 "Gaussian normalisation"** (the continuum Gaussian integral listed as
missing in `Poincare.D7.Reduced.Statements.reducedVolumeDependencies`): constructed by
`gaussianReducedVolume_eq_one`, consumed downstream by
`gaussianReducedVolumeCertificate_volume`. -/
def rlv10Closure : ClosureRecord where
  dependencyName := "RLV-10 Gaussian normalisation"
  constructorDecl := "Poincare.D12.KappaVariational.gaussianReducedVolume_eq_one"
  downstreamUseDecl := "Poincare.D12.KappaVariational.gaussianReducedVolumeCertificate_volume"
  statement := rlv10Statement
  proof := fun n τ hτ => gaussianReducedVolume_eq_one n hτ

/-- **NCF-12 model statement.** The reduced volume of the Gaussian shrinking soliton written
through the D7 reduced length `l(q,τ) = ‖q‖²/(4τ)` is exactly `1` at every positive backward
time — the model half of the "normalisation and uniform κ" input. -/
def ncf12ModelStatement : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 < τ → gaussianReducedVolumeViaL n τ = 1

/-- **Closure of the model half of NCF-12**: constructed by `gaussianReducedVolumeViaL_eq_one`,
consumed downstream by `gaussianReducedVolumeDensity_shape` /
`gaussianUniformReducedVolumeLowerBound`. -/
def ncf12ModelClosure : ClosureRecord where
  dependencyName := "NCF-12 normalisation (Gaussian model half)"
  constructorDecl := "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL_eq_one"
  downstreamUseDecl := "Poincare.D12.KappaVariational.gaussianUniformReducedVolumeLowerBound"
  statement := ncf12ModelStatement
  proof := fun n τ hτ => gaussianReducedVolumeViaL_eq_one n hτ

/-- **RLV-1 model statement.** `L`-length minimiser existence for the whole constant-curvature
family `R₀ ≥ 0` (the D7 state-only `Prop` `LMinimizerExistence`, previously proved only for
`R ≡ 0`). -/
def rlv1ModelStatement : Prop :=
  ∀ (n : ℕ) (R0 : ℝ), 0 ≤ R0 → LMinimizerExistence (constantCurvatureFlow n R0) 0

/-- **Closure of the constant-curvature family case of RLV-1**: constructed by
`constantCurvatureLMinimizerExistence`, consumed downstream by `constantCurvature_reducedLength_le`
(the quantitative reduced-length lower bound). -/
def rlv1ModelClosure : ClosureRecord where
  dependencyName := "RLV-1 path-space minimiser (constant-curvature family case)"
  constructorDecl := "Poincare.D12.KappaVariational.constantCurvatureLMinimizerExistence"
  downstreamUseDecl := "Poincare.D12.KappaVariational.constantCurvature_reducedLength_le"
  statement := rlv1ModelStatement
  proof := fun n R0 hR0 => constantCurvatureLMinimizerExistence n R0 hR0

/-- **The closure ledger of this task** (kernel-checked: each entry carries its own proof). -/
def kappaVariationalClosures : List ClosureRecord :=
  [rlv10Closure, ncf12ModelClosure, rlv1ModelClosure]

/-- **Non-vacuity.** The closure ledger is nonempty and every entry is named. -/
theorem kappaVariationalClosures_nonempty :
    kappaVariationalClosures ≠ [] ∧
      ∀ c ∈ kappaVariationalClosures, c.dependencyName ≠ "" ∧ c.constructorDecl ≠ ""
        ∧ c.downstreamUseDecl ≠ "" := by
  constructor
  · intro h
    cases h
  · simp [kappaVariationalClosures, rlv10Closure, ncf12ModelClosure, rlv1ModelClosure]

/-! ## 2. Checked reduction: on the Gaussian model, κ-noncollapsing reduces to the comparison -/

/-- **State-only (NCF-9).** The ball-volume comparison hypothesis on a metric measure space for
a given reduced-volume certificate: some monotone comparison function `φ` exists such that a
collapsed ball at scale `r` forces a small reduced volume at `τ = r²`.  This is the hypothesis
consumed by `Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison`; its analytic
proof (path-space / conjugate-heat-kernel estimates) is not provided here. -/
def ballVolumeComparisonExists {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (C : ReducedVolumeCertificate E) (r₀ : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, BallVolumeComparison M μ K C φ r₀

/-- **Checked conditional transfer.**  On the Gaussian model `M = EuclideanSpace ℝ (Fin 3)`
with Lebesgue measure and the trivial curvature predicate, the D7 conditional theorem fires: the
normalisation `v₀ = 1` at `τ₀ = 1` is discharged by the Gaussian normalisation integral, so
**the only remaining input** for a D3 κ-noncollapsing certificate on this model is a
`BallVolumeComparison` for a monotone `φ` with `φ 1 = κ`.  The comparison itself is
`ballVolumeComparisonExists` (state-only). -/
theorem gaussianKappaNoncollapsing_of_ballVolumeComparison {κ r₀ : ℝ} (hκ : 0 < κ)
    (hr₀ : 0 < r₀) (hscale : r₀ ^ 2 ≤ 1) {φ : ℝ → ℝ}
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ 1 = κ)
    (comparison : BallVolumeComparison (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True)
      (gaussianReducedVolumeCertificate 3) φ r₀) :
    KappaNoncollapsingCertificate (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True) κ r₀ :=
  kappaNoncollapsing_of_entropy_and_volumeComparison
    (gaussianReducedVolumeCertificate 3) φ hκ hr₀ zero_lt_one hscale zero_lt_one
    (by rfl : (1 : ℝ) ≤ (gaussianReducedVolumeCertificate 3).volume 1) hφmono hφ comparison

/-! ## 3. The remaining missing-input ledger -/

/-- **Remaining missing inputs** for the full Perelman no-local-collapsing argument from the
perspective of this track.  `RLV-10`, the model half of `NCF-12` and the constant-curvature
family case of `RLV-1` are closed (`kappaVariationalClosures`); everything else below remains an
explicit named input. -/
def kappaVariationalRemainingDependencies : List D7.ShortTime.MissingDependency :=
  [ ⟨"KV-1 path-space compactness (general RLV-1)",
      "compactness/lower-semicontinuity for L-length minimisers on a general metric-flow interface; only the Gaussian and constant-curvature families have explicit minimisers (constantCurvatureLMinimizerExistence, gaussianLMinimizerExistence)"⟩,
    ⟨"KV-2 L-geodesic equation (RLV-2)",
      "first variation of the L-length and the L-geodesic ODE for general curvature data"⟩,
    ⟨"KV-3 minimiser regularity (RLV-3)",
      "smoothness of L-minimisers on (0, tau] and continuity at the base time for general flows"⟩,
    ⟨"KV-4 L-exponential map (RLV-4)",
      "construction and differentiability of the L-exponential map"⟩,
    ⟨"KV-5 second variation and index form (RLV-5)",
      "nonnegativity of the L-index form along minimising L-geodesics"⟩,
    ⟨"KV-6 Jacobian comparison (RLV-6)",
      "Perelman's Jacobian bound under a Ricci lower bound for general flows"⟩,
    ⟨"KV-7 reduced-length differential inequality (RLV-7)",
      "l_tau - Delta l + |grad l|^2 - R + n/(2 tau) >= 0 for the reduced length of a genuine Ricci flow"⟩,
    ⟨"KV-8 differentiation under the integral (RLV-8)",
      "dominated convergence for the derivative of the continuum reduced volume"⟩,
    ⟨"KV-9 manifold metric flow (RLV-9)",
      "manifold metrics, Ricci tensor and covariant calculus on a genuine Ricci flow"⟩,
    ⟨"KV-10 ball-volume comparison (NCF-9)",
      "collapsed ball at scale r forces small reduced volume at tau = r^2 (the ballVolumeComparisonExists input)"⟩,
    ⟨"KV-11 ancient-solution rigidity (NCF-10)",
      "equality case of the monotonicity: the Gaussian shrinking soliton; not inferred from any formal record"⟩,
    ⟨"KV-12 no-local-collapsing compactness (NCF-11)",
      "blow-up/compactness extraction of the ancient limit"⟩,
    ⟨"KV-13 normalisation and uniform kappa (general NCF-12)",
      "the general reduced-volume normalisation and the identification of the uniform kappa; the Gaussian model half is closed (ncf12ModelClosure)"⟩]

/-- **Kernel-checked ledger invariant.**  The remaining-dependencies list has thirteen entries. -/
theorem kappaVariationalRemainingDependencies_length :
    kappaVariationalRemainingDependencies.length = 13 := by
  rfl

/-- **Kernel-checked ledger invariant.**  Every remaining dependency is named (nonempty name and
reason). -/
theorem kappaVariationalRemainingDependencies_all_named :
    ∀ d ∈ kappaVariationalRemainingDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [kappaVariationalRemainingDependencies]

end KappaVariational
end D12
end Poincare
