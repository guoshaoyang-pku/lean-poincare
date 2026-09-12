/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — comparison geometry: shared analytic definitions

This file defines the predicate-level scaffolding for the nonconstant-curvature scalar
Jacobi / Riccati comparison theorems.  Everything here is a definition: no theorem is
assumed, and no division by zero is ever performed — all divisibility obligations are
carried in the hypotheses (positivity of solutions on closed intervals, or the interval
`Ioo a b` being genuinely open).

The central objects:

* `JacobiSolutionOn k u du ddu a b` — `u'' + k·u = 0` on `Ioo a b`, with explicit
  derivative data `du`, `ddu` (`HasDerivAt` at every interior point) and continuity of
  `u`, `du` on the closed interval `Icc a b`.  This is the *solution* predicate for the
  nonconstant scalar Jacobi equation.
* `RiccatiLeOn d k m dm a b` — the Riccati inequality `m' + m²/d + k ≤ 0` on `Ioo a b`.
* `RiccatiEqOn d k m dm a b` — the Riccati equality `m' + m²/d + k = 0` on `Ioo a b`.
* `EuclideanNormalizedOn m d C t₀` — the quantitative Euclidean-tangent normalization
  `|m t − d/t| ≤ C` on `(0,t₀]`.  For `d = 1` and `m = u'/u` this is the exact quantified
  form of the initial conditions `u 0 = 0`, `u' 0 = 1` for a `C²` Jacobi field (proved in
  `SingularRiccati.lean`); for general `d = n−1` and `m = A'/A` it is the quantitative
  form of the Euclidean-tangent expansion `A t = t^d·(1 + O(t))` of an `(n−1)`-area
  function along a unit-speed radial geodesic.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.D12.ComparisonGeodesics

/-! ## Instance-pinned derivative predicate

`HasDerivAt` carries `AddCommGroup ℝ`, `Module ℝ ℝ`, `TopologicalSpace ℝ` and
`ContinuousSMul ℝ ℝ` instance arguments, and the instance synthesis for these is
sensitive to the import context (e.g. `Semiring.toModule` versus
`RCLike.toInnerProductSpaceReal.toModule` are not definitionally equal).  To keep the
statement of every structure field and theorem in this directory independent of the
consumer's import context, all derivative data is stated with the following explicitly
pinned instances (the ones produced by mathlib's own `HasDerivAt` lemmas such as
`HasDerivAt.mul`, so they compose with the standard library). -/
abbrev HasDerivAtR (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ
    Real.normedAddCommGroup.toAddCommGroup RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace (PolynormableSpace.continuousSMul ℝ ℝ)
    f f' x

/-! ## Pinned elementary derivatives

The following wrappers pin the instance arguments of the elementary derivative lemmas
`id`, `const`, `inv`, `pow` to exactly the instances used by `HasDerivAtR`.  They are
proved in *this* file's import context (the context in which the pinning was calibrated),
so downstream files can compose pinned derivatives without re-triggering instance
synthesis, which is import-context dependent (see the header note on `HasDerivAtR`). -/

theorem hasDerivAtR_id (t : ℝ) : HasDerivAtR (fun x : ℝ => x) 1 t := hasDerivAt_id t

theorem hasDerivAtR_const (c t : ℝ) : HasDerivAtR (fun _ : ℝ => c) 0 t := hasDerivAt_const t c

theorem hasDerivAtR_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAtR (fun x : ℝ => x⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht

theorem hasDerivAtR_pow (n : ℕ) (t : ℝ) :
    HasDerivAtR (fun x : ℝ => x ^ n) ((n : ℝ) * t ^ (n - 1)) t := hasDerivAt_pow n t

/-! ## The scalar Jacobi equation with nonconstant curvature -/

/-- A function `u` together with explicit first and second derivatives `du`, `ddu` solves
the scalar Jacobi equation `u'' + k·u = 0` on the open interval `Ioo a b`, and is `C¹`
up to the boundary.  The derivative data is carried by pointwise `HasDerivAt` facts, so
every later computation is checked by the kernel. -/
structure JacobiSolutionOn (k u du ddu : ℝ → ℝ) (a b : ℝ) : Prop where
  hasDerivAt_u : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR u (du t) t
  hasDerivAt_du : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR du (ddu t) t
  eq_secondDeriv : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → ddu t = -(k t) * u t
  continuousOn_u : ContinuousOn u (Icc a b)
  continuousOn_du : ContinuousOn du (Icc a b)

/-- Negating a solution negates the derivative data and preserves the equation. -/
lemma JacobiSolutionOn.neg {k u du ddu : ℝ → ℝ} {a b : ℝ}
    (h : JacobiSolutionOn k u du ddu a b) :
    JacobiSolutionOn k (-u) (-du) (-ddu) a b where
  hasDerivAt_u := by
    intro t ht
    exact (h.hasDerivAt_u ht).neg
  hasDerivAt_du := by
    intro t ht
    exact (h.hasDerivAt_du ht).neg
  eq_secondDeriv := by
    intro t ht
    rw [Pi.neg_apply, Pi.neg_apply]
    rw [h.eq_secondDeriv ht]
    ring
  continuousOn_u := h.continuousOn_u.neg
  continuousOn_du := h.continuousOn_du.neg

/-- The Wronskian `u₂·du₁ − u₁·du₂` of two Jacobi data. -/
def wronskian (u₁ du₁ u₂ du₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => u₂ t * du₁ t - u₁ t * du₂ t

/-! ## Riccati inequalities and equalities -/

/-- The Riccati *inequality* `m' + m²/d + k ≤ 0` on `Ioo a b` (with derivative data
`dm`).  For `d = n−1` and `m = A'/A` this is the analytic form of
`Ric ≥ (n−1)K`-type curvature bounds on the radial curvature `k` (after the
Cauchy–Schwarz step `tr S² ≥ m²/d`, which is the geometric input recorded separately,
not assumed here). -/
structure RiccatiLeOn (d k m dm : ℝ → ℝ) (a b : ℝ) : Prop where
  hasDerivAt_m : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR m (dm t) t
  ineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dm t + m t ^ 2 / d t + k t ≤ 0
  continuousOn_m : ContinuousOn m (Icc a b)

/-- The Riccati *equality* `m' + m²/d + k = 0` on `Ioo a b`. -/
structure RiccatiEqOn (d k m dm : ℝ → ℝ) (a b : ℝ) : Prop where
  hasDerivAt_m : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → HasDerivAtR m (dm t) t
  eq : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → dm t + m t ^ 2 / d t + k t = 0
  continuousOn_m : ContinuousOn m (Icc a b)

/-- An equality solution is in particular an inequality solution. -/
lemma RiccatiEqOn.toLe {d k m dm : ℝ → ℝ} {a b : ℝ} (h : RiccatiEqOn d k m dm a b) :
    RiccatiLeOn d k m dm a b where
  hasDerivAt_m := h.hasDerivAt_m
  ineq := by
    intro t ht
    exact (h.eq ht).le
  continuousOn_m := h.continuousOn_m

/-! ## Quantitative Euclidean normalization -/

/-- The quantitative Euclidean-tangent normalization: `|m t − d/t| ≤ C` on `(0, t₀]`.
For a Jacobi field `u` with `u 0 = 0`, `u' 0 = 1` and bounded `u''` this holds with
`d = 1` for `m = u'/u` (see `riccati_normalization_of_smooth_initial`); for an
`(n−1)`-area function `A` this is the quantitative statement that `A t / t^d` is bounded
and bounded away from `0` near `0`. -/
def EuclideanNormalizedOn (m : ℝ → ℝ) (d C t₀ : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 t₀ → |m t - d / t| ≤ C

/-! ## Cumulative volume along a radial geodesic -/

/-- The cumulative `(n−1)`-area / radial volume function `V t = ∫₀ᵗ A s ds`.  If `A` is
the `(n−1)`-area of the geodesic spheres of radius `s` around a fixed point, `V` is the
volume of the corresponding metric balls (up to the identification of the ball with
`[0,t] ×` the tangent sphere, which is the geometric ingredient recorded separately). -/
def radialVolume (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, A s

end Poincare.D12.ComparisonGeodesics
