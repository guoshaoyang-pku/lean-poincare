/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D9-ancient-kappa-solutions builder
-/
module

public import Ledger.PerelmanDefinitions

/-!
# Poincare.D9.AncientKappa.Basic

Interfaces for the singularity-analysis layer of the Ricci-flow program: ancient solutions,
κ-non-collapsing at all scales, and gradient shrinking solitons.

The pinned mathlib has no Ricci flow, no Ricci tensor of a smooth metric, no Riemannian volume
form and no Hessian of a function on a manifold, so the analytic objects are introduced as data
together with **explicit hypotheses**, in the style of `Ledger.PerelmanDefinitions`.  Every
structure below is conditional: it asserts no existence of solutions, no curvature bounds and no
non-collapsing theorem.  A consumer must supply the fields before a statement applies.

## Main interfaces

* `CurvatureBoundedOnCompactIntervals curvature` — the bounded-curvature hypothesis of an ancient
  solution: on every compact time subinterval of `(-∞, 0]` and every compact spatial set, the
  curvature is bounded by a constant;
* `AncientSolution I M` — a Ricci-flow candidate whose time domain is exactly `(-∞, 0]`, together
  with the bounded-curvature hypothesis.  It contains a `Perelman.MetricFlowData`, so the
  Ricci-flow equation `∂ₜ g = -2 Ric` is a field;
* `KappaNoncollapsingAllScales n flow Rm volume κ` — Perelman's κ-non-collapsing inequality
  *without* the small-scale restriction `r ≤ r₀`: whenever the curvature is bounded by `r⁻²` on
  the ball of radius `r`, that ball has volume at least `κ rⁿ`;
* `GradientShrinkingSoliton E` — the model-space soliton equation
  `Ric + Hess f = (1 / (2τ)) g` for a positive scale parameter `τ`, with the metric, the Ricci
  tensor, the Hessian of the potential and the potential itself as fields; the manifold-level
  variant `ManifoldGradientShrinkingSoliton I M` carries the same equation on tangent spaces.

## Checked consequences

* `AncientSolution.ricciFlow_equation` — the flow equation at every `t ≤ 0`;
* `AncientSolution.exists_curvature_bound` — the curvature bound extracted from the interface;
* `KappaNoncollapsingAllScales.toKappaNoncollapsing` — all-scales non-collapsing implies the
  ledger's fixed-scale `Perelman.KappaNoncollapsing`;
* `KappaNoncollapsingAllScales.volume_ball_pos` and `.mono` — positivity and monotonicity in the
  non-collapsing constant;
* `GradientShrinkingSoliton.soliton_equation_one` and
  `ManifoldGradientShrinkingSoliton.soliton_equation_one` — the `τ = 1` specialization
  `Ric + Hess f = (1/2) g`, the form verified concretely for the Gaussian soliton in
  `Poincare.D9.AncientKappa.GaussianSoliton`.

## Sources

* G. Perelman, *The entropy formula for the Ricci flow and its geometric applications*,
  arXiv:math/0211159;
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109;
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, AMS (2007).

No declaration in this file is an unproved hole or an extra logical postulate.
-/

@[expose] public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal

namespace Poincare
namespace Longrun
namespace AncientKappa

/-! ## 1. Ancient solutions -/

section Ancient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Bounded curvature on compact subintervals.**  On every compact time subinterval
`[a, b]` of `(-∞, 0]` and every compact spatial set `K`, the curvature function `curvature` is
bounded by a nonnegative constant.  This is the standing bounded-curvature hypothesis of an
ancient solution; the curvature itself is data, because mathlib has no Riemann tensor. -/
def CurvatureBoundedOnCompactIntervals (curvature : ℝ → M → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set M, IsCompact K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x ∈ K, |curvature t x| ≤ C

/-- **Ancient solution.**  A Ricci-flow candidate on the time interval `(-∞, 0]` together with
the bounded-curvature hypothesis on compact subintervals.

The field `flow` carries the metric family, the abstract Ricci tensor, the symmetry of the Ricci
tensor and the Ricci-flow equation `∂ₜ g = -2 Ric`.  The field `timeDomain_eq` pins the time
domain to `(-∞, 0]`.  The curvature function is data, and `bounded_curvature` is the explicit
hypothesis.  The structure is not inhabited by fiat: providing a term requires the flow
equation and the curvature bounds. -/
structure AncientSolution (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  /-- The underlying Ricci-flow candidate. -/
  flow : Perelman.MetricFlowData I M
  /-- The time domain is exactly `(-∞, 0]`. -/
  timeDomain_eq : flow.timeDomain = Set.Iic 0
  /-- A scalar curvature-type function, standing for the norm of the Riemann tensor. -/
  curvature : ℝ → M → ℝ
  /-- Bounded curvature on compact time subintervals and compact spatial sets. -/
  bounded_curvature : CurvatureBoundedOnCompactIntervals curvature

namespace AncientSolution

variable (S : AncientSolution I M)

/-- The time domain of an ancient solution is `(-∞, 0]`. -/
theorem mem_timeDomain_iff {t : ℝ} : t ∈ S.flow.timeDomain ↔ t ≤ 0 := by
  rw [S.timeDomain_eq]
  exact Iff.rfl

/-- Every time in the domain of an ancient solution is nonpositive. -/
theorem time_le_zero {t : ℝ} (ht : t ∈ S.flow.timeDomain) : t ≤ 0 :=
  S.mem_timeDomain_iff.mp ht

/-- The time domain contains every nonpositive time. -/
theorem mem_timeDomain_of_le_zero {t : ℝ} (ht : t ≤ 0) : t ∈ S.flow.timeDomain :=
  S.mem_timeDomain_iff.mpr ht

/-- **Checked consequence.**  The Ricci-flow equation holds at every time `t ≤ 0`. -/
theorem ricciFlow_equation {t : ℝ} (ht : t ≤ 0) :
    Perelman.HasMetricTimeDerivative S.flow.metric (Perelman.negTwoRicci (S.flow.ricci t)) t :=
  S.flow.ricciFlow_equation t (S.mem_timeDomain_of_le_zero ht)

/-- **Checked consequence.**  The curvature bound extracted from the interface: for every
compact time subinterval `[a, b] ⊆ (-∞, 0]` and every compact `K`, there is a nonnegative
constant `C` with `|curvature t x| ≤ C` for all `t ∈ [a, b]` and `x ∈ K`. -/
theorem exists_curvature_bound {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) {K : Set M}
    (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x ∈ K, |S.curvature t x| ≤ C :=
  S.bounded_curvature a b hab hb K hK

/-- The Ricci tensor of an ancient solution is symmetric at every time and point. -/
theorem ricci_symm (t : ℝ) (x : M) (v w : TangentSpace I x) :
    S.flow.ricci t x v w = S.flow.ricci t x w v :=
  S.flow.ricci_symm t x v w

end AncientSolution

end Ancient

/-! ## 2. κ-non-collapsing at all scales -/

section Noncollapsing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [MeasurableSpace M]

/-- **κ-non-collapsing at all scales.**  Perelman's non-collapsing inequality with the small-scale
restriction removed: for every time in the flow domain, every centre `x` and every radius `r > 0`,
if the curvature is bounded by `r⁻²` on the ball `B(x, r)`, then `vol B(x, r) ≥ κ rⁿ`.

Positivity of `κ` is a field, so the statement can never be satisfied by the vacuous constant
`κ = 0`.  The curvature-bound predicate is `Perelman.CurvatureBoundedOn` from the ledger. -/
structure KappaNoncollapsingAllScales {n : ℕ} (flow : Perelman.MetricFlowData I M)
    (Rm : ℝ → M → ℝ) (volume : ℝ → Measure M) (κ : ℝ) : Prop where
  /-- The non-collapsing constant is positive. -/
  kappa_pos : 0 < κ
  /-- The non-collapsing volume lower bound at every scale. -/
  volume_ball_lower : ∀ t ∈ flow.timeDomain, ∀ x : M, ∀ r : ℝ, 0 < r →
    Perelman.CurvatureBoundedOn Rm t (r⁻¹ ^ 2) (Metric.eball x (ENNReal.ofReal r)) →
    ENNReal.ofReal (κ * r ^ n) ≤ volume t (Metric.eball x (ENNReal.ofReal r))

namespace KappaNoncollapsingAllScales

variable {n : ℕ} {flow : Perelman.MetricFlowData I M} {Rm : ℝ → M → ℝ}
  {volume : ℝ → Measure M} {κ : ℝ}

/-- **Checked consequence.**  Non-collapsing at all scales implies the ledger's fixed-scale
`Perelman.KappaNoncollapsing` for every positive scale `r₀`. -/
theorem toKappaNoncollapsing (h : KappaNoncollapsingAllScales (n := n) flow Rm volume κ)
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    Perelman.KappaNoncollapsing (n := n) flow Rm volume κ r₀ where
  kappa_pos := h.kappa_pos
  r0_pos := hr₀
  volume_ball_lower := fun t ht x r hr _ hK => h.volume_ball_lower t ht x r hr hK

/-- **Checked consequence.**  Every ball in the curvature-bounded range has positive measure. -/
theorem volume_ball_pos (h : KappaNoncollapsingAllScales (n := n) flow Rm volume κ)
    {t : ℝ} (ht : t ∈ flow.timeDomain) {x : M} {r : ℝ} (hr : 0 < r)
    (hK : Perelman.CurvatureBoundedOn Rm t (r⁻¹ ^ 2) (Metric.eball x (ENNReal.ofReal r))) :
    0 < volume t (Metric.eball x (ENNReal.ofReal r)) := by
  have hκr : 0 < κ * r ^ n := mul_pos h.kappa_pos (pow_pos hr n)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hκr) (h.volume_ball_lower t ht x r hr hK)

/-- **Checked consequence.**  Non-collapsing is monotone in the constant: a certificate with
constant `κ` is a certificate with any smaller positive constant `κ' ≤ κ`. -/
theorem mono (h : KappaNoncollapsingAllScales (n := n) flow Rm volume κ) {κ' : ℝ}
    (hκ' : 0 < κ') (hle : κ' ≤ κ) :
    KappaNoncollapsingAllScales (n := n) flow Rm volume κ' where
  kappa_pos := hκ'
  volume_ball_lower := by
    intro t ht x r hr hK
    have hr' : 0 ≤ r ^ n := pow_nonneg hr.le n
    exact le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle hr'))
      (h.volume_ball_lower t ht x r hr hK)

end KappaNoncollapsingAllScales

/-- **κ-non-collapsing at all scales for an ancient solution.**  The non-collapsing interface
applied to the flow and curvature of an ancient solution, in dimension `n`. -/
abbrev AncientSolution.KappaNoncollapsingAtAllScales (n : ℕ) (S : AncientSolution I M)
    (volume : ℝ → Measure M) (κ : ℝ) : Prop :=
  KappaNoncollapsingAllScales (n := n) S.flow S.curvature volume κ

/-- **Checked consequence.**  An ancient solution that is non-collapsing at all scales satisfies
the ledger's fixed-scale non-collapsing hypothesis at every positive scale. -/
theorem AncientSolution.toKappaNoncollapsing {n : ℕ} (S : AncientSolution I M)
    {volume : ℝ → Measure M} {κ : ℝ}
    (h : S.KappaNoncollapsingAtAllScales n volume κ) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    Perelman.KappaNoncollapsing (n := n) S.flow S.curvature volume κ r₀ :=
  h.toKappaNoncollapsing r₀ hr₀

end Noncollapsing

/-! ## 3. Gradient shrinking solitons -/

section Soliton

/-- **Gradient shrinking soliton (model-space form).**  A metric `g`, a Ricci tensor `Ric`, the
Hessian of a potential, the potential `f` and a positive scale `τ`, satisfying the soliton
equation `Ric + Hess f = (1/(2τ)) g` for every point and every pair of model-space vectors.

All geometric objects are interface fields: mathlib has no Ricci tensor of a smooth metric and no
Hessian on a manifold.  The two symmetry fields record that `Ric` and `Hess f` are symmetric
bilinear forms.  The equation is a field, so a term of this structure can only be produced by
proving it.  This is the form used for the explicit Euclidean computation in
`Poincare.D9.AncientKappa.GaussianSoliton`; the manifold-level variant is
`ManifoldGradientShrinkingSoliton` below. -/
structure GradientShrinkingSoliton (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The metric, as a family of bilinear forms. -/
  metric : E → E → E → ℝ
  /-- The Ricci tensor, as a family of bilinear forms. -/
  ricci : E → E → E → ℝ
  /-- The Hessian of the potential, as a family of bilinear forms. -/
  hessian : E → E → E → ℝ
  /-- The soliton potential `f`. -/
  potential : E → ℝ
  /-- The scale parameter `τ`; positivity makes the soliton shrinking. -/
  τ : ℝ
  /-- The scale parameter is positive. -/
  τ_pos : 0 < τ
  /-- The Ricci tensor is symmetric. -/
  ricci_symm : ∀ (x v w : E), ricci x v w = ricci x w v
  /-- The Hessian is symmetric. -/
  hessian_symm : ∀ (x v w : E), hessian x v w = hessian x w v
  /-- The soliton equation `Ric + Hess f = (1/(2τ)) g`. -/
  soliton_equation : ∀ (x v w : E), ricci x v w + hessian x v w = (1 / (2 * τ)) * metric x v w

namespace GradientShrinkingSoliton

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : GradientShrinkingSoliton E)

/-- **Checked consequence.**  At `τ = 1` the soliton equation specializes to
`Ric + Hess f = (1/2) g`, the normalization used for the Gaussian soliton. -/
theorem soliton_equation_one (hτ : S.τ = 1) (x v w : E) :
    S.ricci x v w + S.hessian x v w = (1 / 2 : ℝ) * S.metric x v w := by
  have h := S.soliton_equation x v w
  rw [hτ] at h
  norm_num at h
  exact h

end GradientShrinkingSoliton

section ManifoldSoliton

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Gradient shrinking soliton (manifold form).**  The same soliton equation as
`GradientShrinkingSoliton`, but with all bilinear forms defined on the tangent spaces of a smooth
manifold `M`, and the metric bundled as a `Bundle.RiemannianMetric`.  This is the geometric
interface; the model-space form is the one instantiated by the explicit Euclidean computation. -/
structure ManifoldGradientShrinkingSoliton (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The Riemannian metric. -/
  metric : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)
  /-- The Ricci tensor. -/
  ricci : Perelman.RicciTensor I M
  /-- The Hessian of the potential, as a family of bilinear forms. -/
  hessian : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- The soliton potential `f`. -/
  potential : M → ℝ
  /-- The scale parameter `τ`; positivity makes the soliton shrinking. -/
  τ : ℝ
  /-- The scale parameter is positive. -/
  τ_pos : 0 < τ
  /-- The Ricci tensor is symmetric. -/
  ricci_symm : ∀ (x : M) (v w : TangentSpace I x), ricci x v w = ricci x w v
  /-- The Hessian is symmetric. -/
  hessian_symm : ∀ (x : M) (v w : TangentSpace I x), hessian x v w = hessian x w v
  /-- The soliton equation `Ric + Hess f = (1/(2τ)) g`. -/
  soliton_equation : ∀ (x : M) (v w : TangentSpace I x),
    ricci x v w + hessian x v w = (1 / (2 * τ)) * metric.inner x v w

namespace ManifoldGradientShrinkingSoliton

variable (S : ManifoldGradientShrinkingSoliton I M)

/-- **Checked consequence.**  At `τ = 1` the manifold-form soliton equation specializes to
`Ric + Hess f = (1/2) g`. -/
theorem soliton_equation_one (hτ : S.τ = 1) (x : M) (v w : TangentSpace I x) :
    S.ricci x v w + S.hessian x v w = (1 / 2 : ℝ) * S.metric.inner x v w := by
  have h := S.soliton_equation x v w
  rw [hτ] at h
  norm_num at h
  exact h

end ManifoldGradientShrinkingSoliton

end ManifoldSoliton

end Soliton

end AncientKappa
end Longrun
end Poincare
