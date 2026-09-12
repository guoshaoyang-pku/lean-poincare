import Mathlib
import Poincare.Stage1.RiemannAdapter
import Poincare.D9.CheegerGromov.PointedConvergence
import Poincare.D9.CheegerGromov.DiscreteModel

/-!
# Poincare.D9.CheegerGromov.CheegerGromov

**D9 / Cheeger–Gromov compactness: the state-only statements.**

This module is part of the `D9-cheeger-gromov-compactness` task.  It states — and does **not** prove —
the Cheeger–Gromov compactness theorem in three forms, over the release's manifold layer
(`Poincare.Stage1.RiemannAdapter`, the `PointwiseCurvature` interface) and the pointed `C^k`
convergence interface of `Poincare.D9.CheegerGromov.PointedConvergence`:

* `CurvatureNormBound X Λ` — the hypothesis `|Rm| ≤ Λ`, as an explicit interface predicate: there
  is a pointwise `(1,3)` curvature tensor satisfying the release's `PointwiseCurvature` interface
  obligations (first-pair antisymmetry and the first Bianchi identity) with the multilinear norm
  bound `‖R(u,v)w‖ ≤ Λ ‖u‖ ‖v‖ ‖w‖`.
* `PointedManifoldWithRadius` / `InjectivityRadiusAtLeast X i₀` — the hypothesis `inj ≥ i₀`.  The
  injectivity radius is an explicit interface field of the pointed manifold layer: the pinned
  mathlib revision (`7974e751bece493b6ff508039423ca9fa2452fa8`) constructs neither the exponential
  map nor the injectivity radius, so it is carried as data, exactly as the release carries its
  blocked curvature/Levi-Civita interfaces in `Poincare.Longrun.Geometry.LeviCivitaBlocked`.
* `UniformCurvatureBounds X Λ` — the smooth hypothesis: uniform bounds `Λ k` on the curvature and
  **all** its covariant derivatives (`‖∇^k Rm‖ ≤ Λ (k+1)`), as an explicit interface family.
* `CheegerGromovCompactness Λ i₀` (**state only**) — completeness, compact balls, `|Rm| ≤ Λ` and
  `inj ≥ i₀` on a sequence of pointed manifolds over a fixed model space (fixed dimension) imply a
  pointed `C^1`-convergent subsequence whose limit is complete, has compact metric balls and again
  satisfies `inj ≥ i₀`.
* `CheegerGromovCompactnessSmooth Λ i₀` (**state only**) — the smooth version: uniform bounds on all
  curvature derivatives give pointed `C^k` convergence for every `k`, with the same conclusions on
  the limit.
* `InjectivityRadiusLowerBoundPassesToLimit i₀` (**state only**) — the injectivity-radius lower bound
  passes to the limit: if `X n → Y` in the pointed `C^1` sense and `inj (X n) ≥ i₀` for all `n`, then
  `inj Y ≥ i₀`.

## Checked content

The hard analytic statements are *state-only* `def`s of type `Prop` (referred to by the task as
"state-only Props"); no proof of them is asserted anywhere.  The file does contain fully checked
lemmas anchoring the interfaces:

* `curvatureNormBound_zero`, `uniformCurvatureBounds_zero` — the interfaces are inhabited
  (consistency witnesses): the zero tensor satisfies the `PointwiseCurvature` obligations and the
  norm bounds whenever the bounds are nonnegative.
* `uniformCurvatureBounds_implies_curvatureNormBound` — the smooth hierarchy restricts to the
  `|Rm| ≤ Λ` predicate at order `0`.
* `ckConvergesTo_mono_order` — pointed `C^k` convergence is monotone in the order `k`.
* `ckConvergesTo_all_implies_one` — the all-orders conclusion of the smooth statement restricts
  to the `C^1` conclusion of the `|Rm| ≤ Λ` statement (the smooth hypotheses are stronger, so the
  implication is between the conclusions, not between the state-only Props).
* `discrete_analogue_is_proved` — the *finite* analogue of the compactness statement is a theorem,
  kernel-checked in the computable setting of `Poincare.D9.CheegerGromov.DiscreteModel` (pigeonhole
  / finite `ε`-net argument).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Bundle Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

namespace Poincare
namespace D9
namespace CheegerGromov

universe uE uH uM

noncomputable section

set_option synthInstance.maxHeartbeats 400000

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ## The curvature bound `|Rm| ≤ Λ` -/

/-- **The curvature-norm bound `|Rm| ≤ Λ`** (state-only interface predicate).  There is a pointwise
`(1,3)` curvature tensor over the release's `PointwiseCurvature` type satisfying the two
`RiemannianCurvatureData` interface obligations (first-pair antisymmetry and the first Bianchi
identity) and the multilinear norm bound `‖R(u,v)w‖ ≤ Λ ‖u‖ ‖v‖ ‖w‖`. -/
def CurvatureNormBound (X : PointedManifold E H I) (Λ : ℝ) : Prop :=
  letI : RiemannianBundle (TangentSpace I : X.M → Type uE) :=
    ⟨X.metric.toRiemannianMetric⟩
  ∃ κ : Poincare.RiemannAdapter.PointwiseCurvature I X.M,
    (∀ (x : X.M) (u v w : TangentSpace I x), κ x u v w = -κ x v u w) ∧
      (∀ (x : X.M) (u v w : TangentSpace I x),
        κ x u v w + κ x v w u + κ x w u v = 0) ∧
      (∀ (x : X.M) (u v w : TangentSpace I x), ‖κ x u v w‖ ≤ Λ * ‖u‖ * ‖v‖ * ‖w‖)

set_option linter.style.haveILetI false in
/-- **Consistency witness.**  The `|Rm| ≤ Λ` interface is inhabited: the zero curvature tensor
satisfies the `PointwiseCurvature` obligations and the norm bound for every `Λ ≥ 0`. -/
theorem curvatureNormBound_zero (X : PointedManifold E H I) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    CurvatureNormBound X Λ := by
  letI : RiemannianBundle (TangentSpace I : X.M → Type uE) := ⟨X.metric.toRiemannianMetric⟩
  refine ⟨0, ?_, ?_, ?_⟩
  · intro x u v w; simp
  · intro x u v w; simp
  · intro x u v w
    have h0 : ‖(0 : TangentSpace I x)‖ = 0 := norm_zero
    simp only [Pi.zero_apply, LinearMap.zero_apply, h0]
    exact mul_nonneg (mul_nonneg (mul_nonneg hΛ (norm_nonneg u)) (norm_nonneg v)) (norm_nonneg w)

/-! ## The injectivity-radius interface and the bound `inj ≥ i₀` -/

/-- **Pointed manifold with an injectivity-radius interface field.**  The Riemannian injectivity
radius is carried as explicit data (an interface field), since the pinned mathlib revision
constructs neither the exponential map nor the injectivity radius; the only constraint recorded is
positivity.  The intended evaluation of `injRadius` is the Riemannian injectivity radius. -/
structure PointedManifoldWithRadius (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    extends PointedManifold E H I where
  /-- The injectivity-radius interface field. -/
  injRadius : M → ℝ
  /-- The injectivity radius is positive. -/
  injRadius_pos : ∀ x : M, 0 < injRadius x

/-- **The injectivity-radius lower bound `inj ≥ i₀`** (state-only interface predicate): the
injectivity-radius field is at least `i₀` at every point. -/
def InjectivityRadiusAtLeast (X : PointedManifoldWithRadius E H I) (i₀ : ℝ) : Prop :=
  ∀ x : X.M, i₀ ≤ X.injRadius x

/-! ## Uniform bounds on all curvature derivatives (smooth version) -/

/-- **Uniform bounds on the curvature and all its covariant derivatives** (state-only interface
predicate): there are

* a pointwise `(1,3)` curvature tensor `κ` satisfying the `PointwiseCurvature` obligations with
  `‖κ x u v w‖ ≤ Λ 0 ‖u‖ ‖v‖ ‖w‖`, and
* for every `k ≥ 1` a `k`-th covariant-derivative tensor `D k x` (a tangent-vector-valued function
  of `k + 3` tangent vectors at `x`), with `‖D k x v‖ ≤ Λ (k+1) ∏ i ‖v i‖`, and coherent at `k = 0`
  with `κ`.

The tensors `D k` are interface data: the pinned mathlib revision has no curvature tensor and no
covariant derivatives of tensors. -/
def UniformCurvatureBounds (X : PointedManifold E H I) (Λ : ℕ → ℝ) : Prop :=
  letI : RiemannianBundle (TangentSpace I : X.M → Type uE) :=
    ⟨X.metric.toRiemannianMetric⟩
  ∃ (κ : Poincare.RiemannAdapter.PointwiseCurvature I X.M)
    (D : (k : ℕ) → (x : X.M) → (Fin (k + 3) → TangentSpace I x) → TangentSpace I x),
    (∀ (x : X.M) (u v w : TangentSpace I x), κ x u v w = -κ x v u w) ∧
      (∀ (x : X.M) (u v w : TangentSpace I x),
        κ x u v w + κ x v w u + κ x w u v = 0) ∧
      (∀ (x : X.M) (u v w : TangentSpace I x), ‖κ x u v w‖ ≤ Λ 0 * ‖u‖ * ‖v‖ * ‖w‖) ∧
      (∀ (x : X.M) (u v w : TangentSpace I x), D 0 x ![u, v, w] = κ x u v w) ∧
      (∀ (k : ℕ) (x : X.M) (v : Fin (k + 3) → TangentSpace I x),
        ‖D k x v‖ ≤ Λ (k + 1) * ∏ i, ‖v i‖)

set_option linter.style.haveILetI false in
/-- **Consistency witness.**  The uniform-curvature-bounds interface is inhabited: the zero
hierarchy satisfies the obligations whenever all bounds are nonnegative. -/
theorem uniformCurvatureBounds_zero (X : PointedManifold E H I) {Λ : ℕ → ℝ}
    (hΛ : ∀ k, 0 ≤ Λ k) : UniformCurvatureBounds X Λ := by
  letI : RiemannianBundle (TangentSpace I : X.M → Type uE) := ⟨X.metric.toRiemannianMetric⟩
  refine ⟨0, fun _ _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro x u v w; simp
  · intro x u v w; simp
  · intro x u v w
    have h0 : ‖(0 : TangentSpace I x)‖ = 0 := norm_zero
    simp only [Pi.zero_apply, LinearMap.zero_apply, h0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hΛ 0) (norm_nonneg u)) (norm_nonneg v))
      (norm_nonneg w)
  · intro x u v w; simp
  · intro k x v
    have h0 : ‖(0 : TangentSpace I x)‖ = 0 := norm_zero
    simp only [h0]
    exact mul_nonneg (hΛ (k + 1)) (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-- The smooth hierarchy restricts to the `|Rm| ≤ Λ` predicate at order `0`. -/
theorem uniformCurvatureBounds_implies_curvatureNormBound {X : PointedManifold E H I}
    {Λ : ℕ → ℝ} (h : UniformCurvatureBounds X Λ) : CurvatureNormBound X (Λ 0) := by
  obtain ⟨κ, D, hskew, hbianchi, hbound, -, -⟩ := h
  exact ⟨κ, hskew, hbianchi, hbound⟩

/-! ## Pointed `C^k` convergence is monotone in the order -/

/-- Pointed `C^k` convergence is monotone in the order: convergence through order `k` implies
convergence through every smaller order. -/
theorem ckConvergesTo_mono_order {k k' : ℕ} (hk : k' ≤ k) {X : ℕ → PointedManifold E H I}
    {Y : PointedManifold E H I} (h : CkConvergesTo k X Y) : CkConvergesTo k' X Y := by
  intro R hR ε hε
  obtain ⟨N, hN⟩ := h R hR ε hε
  exact ⟨N, fun n hn => (hN n hn).elim fun c => ⟨c.mono_order hk⟩⟩

/-! ## The state-only compactness statements -/

/-- **Cheeger–Gromov compactness (state only).**

Let `Λ ≥ 0` and `i₀ > 0`.  Every sequence of complete pointed Riemannian manifolds over the fixed
model space `(E, H, I)` (fixed dimension), with compact pointed balls, `|Rm| ≤ Λ` and
`inj ≥ i₀` uniformly, has a subsequence converging in the pointed `C^1` sense to a complete pointed
limit with compact metric balls which again satisfies `inj ≥ i₀`.

This is **not proved here**: the analytic content (Cheeger–Gromov compactness / Gromov's convergence
theorem) is exactly the statement, and the pinned mathlib revision has no curvature tensor, no
injectivity radius and no Riemannian distance.  The finite analogue of the statement is
kernel-checked in `Poincare.D9.CheegerGromov.DiscreteModel` (see `discrete_analogue_is_proved`).

The conclusion is stated for `CkConvergesTo 1`, whose `C^{1+1}` metric comparison through order two
is the standard amount of control needed to pass `|Rm| ≤ Λ` to the limit. -/
def CheegerGromovCompactness (Λ i₀ : ℝ) : Prop :=
  0 ≤ Λ → 0 < i₀ →
    ∀ X : ℕ → PointedManifoldWithRadius.{uE, uH, uM} E H I,
      (∀ n, CurvatureNormBound (X n).toPointedManifold Λ) →
        (∀ n, InjectivityRadiusAtLeast (X n) i₀) →
          (∀ n, (X n).toPointedManifold.IsCompleteMetric) →
            (∀ n, (X n).toPointedManifold.HasCompactMetricBalls) →
              ∃ (Y : PointedManifoldWithRadius.{uE, uH, uM} E H I) (φ : ℕ → ℕ),
                StrictMono φ ∧
                  CkConvergesTo 1 (fun n => (X (φ n)).toPointedManifold) Y.toPointedManifold ∧
                  Y.toPointedManifold.IsCompleteMetric ∧
                  Y.toPointedManifold.HasCompactMetricBalls ∧
                  InjectivityRadiusAtLeast Y i₀

/-- **Smooth Cheeger–Gromov compactness (state only).**

Let `i₀ > 0` and let `Λ : ℕ → ℝ` be nonnegative.  Every sequence of complete pointed Riemannian
manifolds over the fixed model space `(E, H, I)`, with compact pointed balls, uniform bounds on the
curvature and on **all** its covariant derivatives (`‖∇^k Rm‖ ≤ Λ (k+1)`) and `inj ≥ i₀` uniformly,
has a subsequence converging in the pointed `C^k` sense for **every** `k` to a complete limit with
compact metric balls which again satisfies `inj ≥ i₀`.

This is **not proved here**; it is the smooth (all-derivatives) version of the compactness theorem.
-/
def CheegerGromovCompactnessSmooth (Λ : ℕ → ℝ) (i₀ : ℝ) : Prop :=
  (∀ k, 0 ≤ Λ k) → 0 < i₀ →
    ∀ X : ℕ → PointedManifoldWithRadius.{uE, uH, uM} E H I,
      (∀ n, UniformCurvatureBounds (X n).toPointedManifold Λ) →
        (∀ n, InjectivityRadiusAtLeast (X n) i₀) →
          (∀ n, (X n).toPointedManifold.IsCompleteMetric) →
            (∀ n, (X n).toPointedManifold.HasCompactMetricBalls) →
              ∃ (Y : PointedManifoldWithRadius.{uE, uH, uM} E H I) (φ : ℕ → ℕ),
                StrictMono φ ∧
                  (∀ k, CkConvergesTo k (fun n => (X (φ n)).toPointedManifold)
                    Y.toPointedManifold) ∧
                  Y.toPointedManifold.IsCompleteMetric ∧
                  Y.toPointedManifold.HasCompactMetricBalls ∧
                  InjectivityRadiusAtLeast Y i₀

/-- **Convergence of the injectivity-radius bound under the limit (state only).**

If a sequence of pointed manifolds converges in the pointed `C^1` sense to a limit `Y` and each
approximant satisfies `inj ≥ i₀`, then the limit satisfies `inj ≥ i₀`: a geodesic loop shorter than
`2 i₀` would persist under `C^1` perturbation of the metric, contradicting `inj ≥ i₀` on the
approximants.  This is **not proved here**; it is a state-only statement, and it is also part of the
conclusions of the two compactness Props above. -/
def InjectivityRadiusLowerBoundPassesToLimit (i₀ : ℝ) : Prop :=
  ∀ (X : ℕ → PointedManifoldWithRadius.{uE, uH, uM} E H I)
    (Y : PointedManifoldWithRadius.{uE, uH, uM} E H I),
    (∀ n, InjectivityRadiusAtLeast (X n) i₀) →
      CkConvergesTo 1 (fun n => (X n).toPointedManifold) Y.toPointedManifold →
        InjectivityRadiusAtLeast Y i₀

/-! ## Checked relations between the state-only statements -/

/-- **All-orders convergence implies `C^1` convergence** for a fixed sequence and limit: the `k = 1`
instance of the conclusion of the smooth statement.  (Note that the smooth statement has *stronger
hypotheses* — bounds on all curvature derivatives — so it does not imply the `|Rm| ≤ Λ` statement
itself; only its conclusion, under those stronger hypotheses, restricts to the `C^1` conclusion of
the `|Rm| ≤ Λ` statement, which is what this lemma records.) -/
theorem ckConvergesTo_all_implies_one {X : ℕ → PointedManifold E H I}
    {Y : PointedManifold E H I} (h : ∀ k, CkConvergesTo k X Y) : CkConvergesTo 1 X Y :=
  ckConvergesTo_mono_order (le_refl 1) (h 1)

/-- **The finite analogue of the compactness statement is kernel-checked.**  The discrete
(pigeonhole / finite `ε`-net) model of `Poincare.D9.CheegerGromov.DiscreteModel` satisfies its own
sequential compactness statement; the manifold statements above are the state-only counterparts. -/
theorem discrete_analogue_is_proved (N : ℕ) (S : Finset ℝ) (D δ : ℝ) :
    DiscreteCheegerGromovCompactness N S D δ :=
  discreteCheegerGromovCompactness_holds N S D δ

end

end CheegerGromov
end D9
end Poincare
