/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D1-perelman-ledger builder
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit interfaces for Perelman's monotonicity arguments

This file fixes the *language* in which the Ricci-flow / Perelman ledger is stated.  Mathlib
(v4.34.0-rc2) has a Riemannian metric on a manifold but no Ricci tensor, no scalar curvature, no
Riemannian volume form and no smooth manifold of metrics, so the missing analytic objects are
introduced as data together with **explicit hypotheses**.  Every structure below is conditional:
it asserts no existence of solutions, no curvature bounds and no monotonicity.  Those statements
appear only as `Prop`-valued fields or as named hypothesis structures, so a consumer must supply a
proof before a theorem applies.

The main interfaces are:

* `MetricFlowData` : a time-dependent metric family with an abstract Ricci tensor and the explicit
  Ricci-flow equation `∂ₜ g = -2 Ric` (a pointwise derivative identity, not a theorem);
* `VolumeFormData` : a time-dependent measure together with an explicit predicate saying that it is
  the Riemannian volume form of the metric family (`√det g` is provided concretely);
* `ScalarCurvatureData` : a scalar curvature function together with the explicit trace formula
  `R = ∑ g^{ij} Ric_{ij}` in every basis;
* `perelmanF`, `perelmanW`, `perelmanMu` : the F/W functionals as Bochner integrals (definitions,
  not identities), and `FProfile`/`WProfile` for their time profiles;
* `FMonotonicity`, `WMontonicity`, `MuMonotonicity` : Perelman's monotonicity statements as
  hypothesis structures, never as theorems;
* `ScalarCurvatureLowerBound`, `RicciLowerBound`, `CurvatureBoundedOn`, `KappaNoncollapsing` :
  the standing curvature/non-collapsing hypotheses of Steps I--III.

## Sources

* G. Perelman, *The entropy formula for the Ricci flow and its geometric applications*,
  arXiv:math/0211159 (the F and W functionals, their monotonicity, and κ-noncollapsing);
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109 (long-time
  behaviour and canonical neighbourhoods);
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, AMS (2007) (the
  exposition used to name the steps).

## Warnings

Nothing here is a proof of the Poincaré conjecture.  The file is a *statement layer*: all
mathematical content beyond the definitions is a hypothesis, and the accompanying ledger records
which hypotheses remain to be discharged.
-/

@[expose] public section

noncomputable section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff Topology ENNReal

namespace Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ## 1. Metric flow data -/

/-- A one-parameter family of Riemannian metrics on `M`.  No regularity in time or space is
assumed by the abbreviation itself; regularity hypotheses are added by the structures below. -/
abbrev MetricFamily (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := ℝ → Bundle.RiemannianMetric (fun x : M => TangentSpace I x)

/-- The Ricci tensor at a single point: a family of bilinear forms on the tangent space.  In a
full development this is the trace of the Riemann curvature tensor; here it is data. -/
abbrev RicciTensor (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

/-- A time-dependent Ricci tensor. -/
abbrev RicciFamily (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := ℝ → RicciTensor I M

/-- `HasMetricTimeDerivative g dg t` means that at time `t` the scalar function
`s ↦ g s (v, w)` has derivative `dg x v w`, for every `x` and every pair of tangent vectors.
This is the coordinate-free form of `∂ₜ g = dg`; no smoothness of `g` is built in. -/
def HasMetricTimeDerivative (g : MetricFamily I M)
    (dg : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (t : ℝ) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x),
    HasDerivAt (fun s : ℝ => (g s).inner x v w) (dg x v w) t

/-- The bilinear form `-2 Ric`, as it appears on the right-hand side of the Ricci-flow equation. -/
def negTwoRicci (Ric : RicciTensor I M) :
    (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  fun x => (-2 : ℝ) • Ric x

/-- A candidate Ricci flow on a fixed smooth manifold.

The fields `timeDomain`, `metric` and `ricci` are data.  The remaining fields are the explicit
hypotheses: `0` lies in the time domain, the time domain is an interval, the metric coefficients
are smooth in time, the Ricci tensor is symmetric, and the Ricci-flow equation `∂ₜ g = -2 Ric`
holds at every time in the domain.  The structure is not inhabited by fiat: providing a term
requires proving the equation. -/
structure MetricFlowData (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] where
  /-- The time interval on which the flow is considered. -/
  timeDomain : Set ℝ
  /-- The initial time `0` belongs to the time domain. -/
  zero_mem : 0 ∈ timeDomain
  /-- The time domain is an interval (`OrdConnected`). -/
  timeDomain_ordConnected : OrdConnected timeDomain
  /-- The one-parameter family of Riemannian metrics. -/
  metric : MetricFamily I M
  /-- The metric coefficients are smooth in time. -/
  metric_time_smooth : ∀ (x : M) (v w : TangentSpace I x),
    ContDiff ℝ ⊤ (fun s : ℝ => (metric s).inner x v w)
  /-- The abstract Ricci tensor of the flow. -/
  ricci : RicciFamily I M
  /-- The Ricci tensor is symmetric. -/
  ricci_symm : ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
    ricci t x v w = ricci t x w v
  /-- The Ricci-flow equation `∂ₜ g = -2 Ric`, as a pointwise derivative identity. -/
  ricciFlow_equation : ∀ t ∈ timeDomain,
    HasMetricTimeDerivative metric (negTwoRicci (ricci t)) t

namespace MetricFlowData

variable (flow : MetricFlowData I M)

/-- The time domain of a Ricci-flow candidate is an interval containing `0`. -/
theorem Icc_subset {s t : ℝ} (hs : s ∈ flow.timeDomain) (ht : t ∈ flow.timeDomain) :
    Icc s t ⊆ flow.timeDomain :=
  flow.timeDomain_ordConnected.out hs ht

end MetricFlowData

/-! ## 2. Volume forms -/

/-- The Gram matrix of a Riemannian metric `g` in a basis `b` of the tangent space at `x`. -/
def gramMatrix {n : ℕ} (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x))
    (x : M) (b : Basis (Fin n) ℝ (TangentSpace I x)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => g.inner x (b i) (b j)

/-- The classical Riemannian volume density `√det g` at `x`, expressed in a basis `b` of the
tangent space.  This is the local coordinate formula; its positivity is proved under an explicit
positive-definiteness hypothesis in `Ledger.DefinitionSmoke`. -/
def riemannianVolumeDensity {n : ℕ}
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) : ℝ :=
  Real.sqrt (Matrix.det (gramMatrix g x b))

section

variable [MeasurableSpace M]

/-- A predicate expressing that a measure is the Riemannian volume form of a metric family.
Mathlib does not define the Riemannian volume form, so this is an explicit parameter of the
interface: a consumer instantiates it with the intended notion (for example
`HasFrameVolumeDensity` below). -/
abbrev RiemannianVolumePredicate (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [MeasurableSpace M] := ℝ → MetricFamily I M → Measure M → Prop

/-- The concrete frame-based Riemannian volume predicate: `μ` has density `√det g` with respect
to the reference measure `μ₀` in the global frame `frame`.  A global Riemannian volume form
without a global frame requires a partition of unity; that refinement is a ledger blocker. -/
def HasFrameVolumeDensity {n : ℕ} (μ₀ : Measure M)
    (frame : (x : M) → Basis (Fin n) ℝ (TangentSpace I x))
    (t : ℝ) (g : MetricFamily I M) (μ : Measure M) : Prop :=
  μ = μ₀.withDensity (fun x => ENNReal.ofReal (riemannianVolumeDensity (g t) x (frame x)))

/-- Time-dependent volume form data for a metric flow, together with the explicit hypotheses that
it is the Riemannian volume form of the flow and that it is a locally finite, non-zero measure.
The predicate `IsRiemannianVolumeOf` is a parameter, so no property of the volume form is asserted
by the structure itself. -/
structure VolumeFormData (flow : MetricFlowData I M)
    (IsRiemannianVolumeOf : RiemannianVolumePredicate I M) where
  /-- The volume measure at each time. -/
  volume : ℝ → Measure M
  /-- Explicit hypothesis: the measure is the Riemannian volume form of the metric family. -/
  is_riemannian_volume : ∀ t ∈ flow.timeDomain,
    IsRiemannianVolumeOf t flow.metric (volume t)
  /-- Explicit hypothesis: the volume is locally finite. -/
  locally_finite : ∀ t ∈ flow.timeDomain, IsLocallyFiniteMeasure (volume t)
  /-- Explicit hypothesis: the volume form is non-zero. -/
  volume_ne_zero : ∀ t ∈ flow.timeDomain, volume t ≠ 0

end

/-! ## 3. Scalar curvature -/

/-- The scalar curvature of a Ricci tensor `Ric` with respect to the metric `g` at `x`, computed
in the basis `b` by the trace formula `R = ∑ᵢⱼ g^{ij} Ric_{ij}`. -/
def scalarCurvatureInBasis {n : ℕ}
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x))
    (Ric : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) (b : Basis (Fin n) ℝ (TangentSpace I x)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (gramMatrix g x b)⁻¹ i j * Ric x (b i) (b j)

/-- `IsScalarCurvature g Ric R` says that `R` is the scalar curvature of `Ric` for the metric
family `g`: at every time, point and basis of the tangent space, `R` is given by the trace formula.
Basis-independence is therefore part of the statement, as it must be for an intrinsic scalar
curvature. -/
def IsScalarCurvature {n : ℕ} (g : MetricFamily I M) (Ric : RicciFamily I M)
    (R : ℝ → M → ℝ) : Prop :=
  ∀ (t : ℝ) (x : M) (b : Basis (Fin n) ℝ (TangentSpace I x)),
    R t x = scalarCurvatureInBasis (g t) (Ric t) x b

/-- Scalar curvature data for a metric flow: the function `R` together with the explicit trace
hypothesis and a continuity hypothesis. -/
structure ScalarCurvatureData {n : ℕ} (flow : MetricFlowData I M) where
  /-- The scalar curvature function `R(t, x)`. -/
  scalar : ℝ → M → ℝ
  /-- Explicit hypothesis: `scalar` is the trace of the Ricci tensor in every basis. -/
  is_scalar : IsScalarCurvature (n := n) flow.metric flow.ricci scalar
  /-- Explicit hypothesis: the scalar curvature is continuous in space at each time. -/
  scalar_continuous : ∀ t ∈ flow.timeDomain, Continuous (scalar t)

section

variable [MeasurableSpace M]

/-! ## 4. The F and W functionals -/

/-- Perelman's F-functional `F(g, f) = ∫ (R + |∇f|²) e^{-f} dV`, as a Bochner integral against
the volume measure `μ`.  This is a definition only; its finiteness and monotonicity are not
asserted. -/
def perelmanF (μ : Measure M) (R gradSq f : M → ℝ) : ℝ :=
  ∫ x, (R x + gradSq x) * Real.exp (-(f x)) ∂μ

/-- Perelman's W-functional
`W(g, f, τ) = ∫ [τ (|∇f|² + R) + f - n] (4πτ)^{-n/2} e^{-f} dV`,
as a Bochner integral against the volume measure `μ`. -/
def perelmanW (μ : Measure M) (n : ℕ) (τ : ℝ) (R gradSq f : M → ℝ) : ℝ :=
  ∫ x, (τ * (gradSq x + R x) + f x - (n : ℝ)) *
      (Real.rpow (4 * Real.pi * τ) (-(n : ℝ) / 2) * Real.exp (-(f x))) ∂μ

/-- The constraint that the Gaussian-weighted density has total mass one, i.e. that `f` is
admissible for Perelman's μ-invariant. -/
def HasUnitMass (μ : Measure M) (n : ℕ) (τ : ℝ) (f : M → ℝ) : Prop :=
  ∫ x, Real.rpow (4 * Real.pi * τ) (-(n : ℝ) / 2) * Real.exp (-(f x)) ∂μ = 1

/-- Perelman's μ-invariant, defined as the infimum of a W-profile over its range.  The admissible
functions (unit mass) are encoded by the profile itself; no existence of a minimiser is asserted. -/
def perelmanMu (W : ℝ → ℝ) : ℝ :=
  sInf (Set.range W)

/-- The F-profile of a metric flow: `t ↦ F(g(t), f(t))`. -/
def FProfile (μ : ℝ → Measure M) (R gradSq : ℝ → M → ℝ) (f : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  perelmanF (μ t) (R t) (gradSq t) (f t)

/-- The W-profile of a metric flow: `t ↦ W(g(t), f(t), τ(t))`. -/
def WProfile (μ : ℝ → Measure M) (n : ℕ) (τ : ℝ → ℝ) (R gradSq : ℝ → M → ℝ)
    (f : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  perelmanW (μ t) n (τ t) (R t) (gradSq t) (f t)

/-- The coordinate derivative `∂ᵢ f` in the basis direction `b i`, as a real number. -/
def directionalDerivative {n : ℕ} (f : M → ℝ) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) (i : Fin n) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f x (b i)

/-- The squared Riemannian norm of the gradient of `f` at `x`, computed in the basis `b` by the
formula `|∇f|² = ∑ᵢⱼ g^{ij} ∂ᵢf ∂ⱼf`. -/
def gradientNormSqInBasis {n : ℕ}
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (f : M → ℝ) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (gramMatrix g x b)⁻¹ i j * directionalDerivative f x b i * directionalDerivative f x b j

end

/-! ## 5. Monotonicity and curvature hypotheses -/

/-- Perelman's F-monotonicity, as an explicit hypothesis on a time profile `F`: the profile is
non-increasing on the time domain of the flow. -/
structure FMonotonicity (flow : MetricFlowData I M) (F : ℝ → ℝ) : Prop where
  /-- The F-profile is non-increasing. -/
  antitone : AntitoneOn F flow.timeDomain

/-- Perelman's W-monotonicity, as an explicit hypothesis on a time profile `W`. -/
structure WMonotonicity (flow : MetricFlowData I M) (W : ℝ → ℝ) : Prop where
  /-- The W-profile is non-increasing. -/
  antitone : AntitoneOn W flow.timeDomain

/-- Monotonicity of Perelman's μ-invariant in the scale parameter `τ`, as an explicit hypothesis. -/
structure MuMonotonicity (J : Set ℝ) (mu : ℝ → ℝ) : Prop where
  /-- μ is non-decreasing in `τ`. -/
  monotone : MonotoneOn mu J

/-- An explicit lower bound on scalar curvature along the flow. -/
structure ScalarCurvatureLowerBound {n : ℕ} (flow : MetricFlowData I M)
    (S : ScalarCurvatureData (n := n) flow) (c : ℝ) : Prop where
  /-- `R ≥ c` at every time and point. -/
  lower_bound : ∀ t ∈ flow.timeDomain, ∀ x : M, c ≤ S.scalar t x

/-- An explicit lower bound `Ric ≥ κ g` along the flow. -/
structure RicciLowerBound (flow : MetricFlowData I M) (κ : ℝ) : Prop where
  /-- `Ric(v, v) ≥ κ g(v, v)` at every time, point and tangent vector. -/
  lower_bound : ∀ t ∈ flow.timeDomain, ∀ (x : M) (v : TangentSpace I x),
    κ * (flow.metric t).inner x v v ≤ flow.ricci t x v v

/-- The curvature bound `|Rm| ≤ K` on a set, stated for a scalar curvature-type function. -/
def CurvatureBoundedOn (Rm : ℝ → M → ℝ) (t K : ℝ) (s : Set M) : Prop :=
  ∀ y ∈ s, |Rm t y| ≤ K

section

variable [MeasurableSpace M]

/-- Perelman's κ-non-collapsing hypothesis at scale `r₀`, with all metric and measure data
explicit: if the curvature is bounded by `r⁻²` on a ball of radius `r ≤ r₀`, then the volume of
that ball is at least `κ rⁿ`.  The hypotheses `0 < κ`, `0 < r₀` are fields, not conventions. -/
structure KappaNoncollapsing {n : ℕ} [PseudoEMetricSpace M]
    (flow : MetricFlowData I M) (Rm : ℝ → M → ℝ) (volume : ℝ → Measure M) (κ r₀ : ℝ) : Prop where
  /-- The non-collapsing constant is positive. -/
  kappa_pos : 0 < κ
  /-- The scale is positive. -/
  r0_pos : 0 < r₀
  /-- The ball-volume lower bound, under the explicit curvature bound. -/
  volume_ball_lower : ∀ t ∈ flow.timeDomain, ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ →
    CurvatureBoundedOn Rm t (r⁻¹ ^ 2) (Metric.eball x (ENNReal.ofReal r)) →
    ENNReal.ofReal (κ * r ^ n) ≤ volume t (Metric.eball x (ENNReal.ofReal r))

end

end Perelman
