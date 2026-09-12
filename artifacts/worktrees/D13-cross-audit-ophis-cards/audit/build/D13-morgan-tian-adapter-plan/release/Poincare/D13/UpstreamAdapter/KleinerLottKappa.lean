/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-upstream-adapter-audit)

# Upstream adapter: KleinerLott κ-noncollapsing predicates ↔ local D7 κ-certificate

This file is part of the D13 upstream-adapter audit.  It transcribes the κ-noncollapsing
predicates of the pinned Frenzymath snapshot (package `KleinerLott`, files
`formalized-sources/KleinerLott/KleinerLott/RicciFlow/{FlowData,Noncollapsing}.lean`, commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0) verbatim, and proves the conditional
adapter from the upstream predicate to the local D3/D7 κ-certificate
`Poincare.Longrun.Topology.KappaNoncollapsingCertificate` (the certificate consumed by
`Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison`).

Upstream declarations (quoted from the snapshot):
* `KleinerLott.RicciFlowData` (FlowData.lean:16): data fields `dist : ℝ → M → M → ℝ`,
  `curvatureNorm : M → ℝ → ℝ`, `volume : ℝ → Set M → ℝ`;
* `KleinerLott.RicciFlowData.ball` (Noncollapsing.lean:15): `{x | flow.dist t x₀ x < r}`;
* `KleinerLott.RicciFlowData.HasCurvatureBoundOnParabolicBall` (Noncollapsing.lean:21):
  curvature ≤ bound on the terminal ball throughout `[t₀ - r², t₀]`;
* `KleinerLott.IsKappaNoncollapsedOnScale` (Noncollapsing.lean:30): the κ-noncollapsing
  predicate (a definition — the upstream snapshot states the predicate but proves no
  κ-noncollapsing theorem);
* `KleinerLott.IsKappaCollapsedAt` (Noncollapsing.lean:39): the collapsed-ball predicate.

The adapter theorem `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` is a
**conditional adapter** with three expanded translation hypotheses, one per kind of data:
`hcurv` (the local curvature predicate implies the upstream parabolic-curvature bound),
`hvol` (the upstream volume function's value on its own ball is at most the measure of the
containing local closed ball), and the domain/scale hypotheses `t₀ < T`, `r₀ < ρ`,
`ρ² ≤ t₀`.  These are exactly the translations between the two formalizations of the same
geometry (upstream: data functions `dist`/`volume`; local: `PseudoEMetricSpace` structure +
`Measure`), and are the natural compatibility conditions — `hvol` is an *upper* comparison
of two volume functionals, not the κ-lower-bound conclusion.  In the upstream source the
correspondence between the two sides is the `induced_distance` field of
`SmoothCompleteRicciFlowOn` (SmoothRicciFlow.lean:236): the induced Riemannian distance
equals the data distance, which is exactly the condition that makes `hvol` provable for the
Riemannian volume; that construction is upstream, not repeated here.
-/

import Poincare.D7.Kappa.Basic

open MeasureTheory Set
open scoped Topology ENNReal

namespace Poincare.D13.UpstreamAdapter.KleinerLott

/-! ## 1. Transcribed upstream definitions -/

/-- Upstream `KleinerLott.RicciFlowData` (FlowData.lean:16), transcribed verbatim: the
distance, curvature-norm, and volume data used by scalar statements about a Ricci flow. -/
structure RicciFlowData (M : Type*) where
  dist : ℝ → M → M → ℝ
  curvatureNorm : M → ℝ → ℝ
  volume : ℝ → Set M → ℝ

namespace RicciFlowData

/-- Upstream `KleinerLott.RicciFlowData.ball` (Noncollapsing.lean:15): the open ball for the
metric at a specified time.  Transcribed verbatim. -/
def ball {M : Type*} (flow : RicciFlowData M) (t : ℝ) (x₀ : M) (r : ℝ) :
    Set M :=
  {x | flow.dist t x₀ x < r}

/-- Upstream `KleinerLott.RicciFlowData.HasCurvatureBoundOnParabolicBall`
(Noncollapsing.lean:21): a curvature bound on a terminal-time ball throughout a backward
time interval whose length is the square of the radius.  Transcribed verbatim. -/
def HasCurvatureBoundOnParabolicBall {M : Type*} (flow : RicciFlowData M)
    (x₀ : M) (t₀ r bound : ℝ) : Prop :=
  ∀ x ∈ flow.ball t₀ x₀ r, ∀ t ∈ Set.Icc (t₀ - r ^ (2 : ℕ)) t₀,
    flow.curvatureNorm x t ≤ bound

end RicciFlowData

/-- Upstream `KleinerLott.IsKappaNoncollapsedOnScale` (Noncollapsing.lean:30), transcribed
verbatim: a flow on `[0, T)` is κ-noncollapsed on scale `ρ` when every admissible parabolic
ball has the prescribed volume lower bound. -/
def IsKappaNoncollapsedOnScale {M : Type*} (flow : RicciFlowData M) (n : ℕ)
    (T kappa rho : ℝ) : Prop :=
  ∀ x₀ t₀ r, 0 < r → r < rho → r ^ (2 : ℕ) ≤ t₀ → t₀ < T →
    flow.HasCurvatureBoundOnParabolicBall x₀ t₀ r ((r⁻¹) ^ 2) →
      kappa * r ^ n ≤ flow.volume t₀ (flow.ball t₀ x₀ r)

/-- Upstream `KleinerLott.IsKappaCollapsedAt` (Noncollapsing.lean:39), transcribed
verbatim: a flow is κ-collapsed at a spacetime point on scale `r` when curvature is
controlled on the associated parabolic ball but its terminal volume is at most `κ rⁿ`. -/
def IsKappaCollapsedAt {M : Type*} (flow : RicciFlowData M) (n : ℕ)
    (kappa r t₀ : ℝ) (x₀ : M) : Prop :=
  0 < r ∧
    flow.HasCurvatureBoundOnParabolicBall x₀ t₀ r ((r⁻¹) ^ 2) ∧
      flow.volume t₀ (flow.ball t₀ x₀ r) ≤ kappa * r ^ n

/-! ## 2. Conditional adapter: upstream predicate ⇒ local D3/D7 κ-certificate -/

/-- **Conditional adapter (KleinerLott → local D7).**  If the upstream
κ-noncollapsing predicate holds for the flow data at the terminal time `t₀` (with
`t₀ < T`), and the flow data translate into the local metric-measure data on the scale
`r₀ < ρ` with `ρ² ≤ t₀` (expanded translation hypotheses `hcurv` and `hvol` below), then
the local 3-dimensional κ-certificate `KappaNoncollapsingCertificate M μ K κ r₀` holds.
The local certificate is the input consumed by
`Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison`, so this adapter
connects the upstream predicate to the local D7 κ-assembly.

Hypotheses (all expanded, none equivalent to the conclusion):
* `hcurv` — the local curvature predicate `K x r` implies the upstream
  parabolic-curvature bound `(r⁻¹)²` on the flow ball at `t₀` (translation of the
  curvature data);
* `hvol` — the upstream volume function's value on its own ball is at most the measure of
  the local closed ball containing it (translation of the volume data; an *upper*
  comparison, while the conclusion is the κ-*lower* bound);
* `ht₀T`, `hr₀ρ`, `hscale` — the domain/scale alignment (`r₀ < ρ`, `ρ² ≤ t₀`, `t₀ < T`).

Class: conditional adapter (typed implication, locally proved). -/
theorem isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (flow : RicciFlowData M) (μ : Measure M)
    (K : Poincare.Longrun.Topology.CurvatureBoundedOn M)
    {T t₀ κ ρ r₀ : ℝ} (ht₀T : t₀ < T) (hr₀ : 0 < r₀) (hr₀ρ : r₀ < ρ)
    (hscale : ρ ^ (2 : ℕ) ≤ t₀) (hκ : 0 < κ)
    (hvol : ∀ x r, 0 < r → ENNReal.ofReal (flow.volume t₀ (flow.ball t₀ x r)) ≤
      μ (Metric.eball x (ENNReal.ofReal r)))
    (hcurv : ∀ x r, 0 < r → K x r →
      flow.HasCurvatureBoundOnParabolicBall x t₀ r ((r⁻¹) ^ 2))
    (hkl : IsKappaNoncollapsedOnScale flow 3 T κ ρ) :
    Poincare.Longrun.Topology.KappaNoncollapsingCertificate M μ K κ r₀ where
  kappa_pos := hκ
  r0_pos := hr₀
  volume_ball_lower := fun x r hr hr₀le hK => by
    have hrρ : r < ρ := lt_of_le_of_lt hr₀le hr₀ρ
    have hrsq : r ^ (2 : ℕ) ≤ t₀ := by
      have hsq : r ^ (2 : ℕ) ≤ ρ ^ (2 : ℕ) := pow_le_pow_left₀ hr.le (le_of_lt hrρ) 2
      exact le_trans hsq hscale
    have hbound : flow.HasCurvatureBoundOnParabolicBall x t₀ r ((r⁻¹) ^ 2) :=
      hcurv x r hr hK
    have hlower : κ * r ^ (3 : ℕ) ≤ flow.volume t₀ (flow.ball t₀ x r) :=
      hkl x t₀ r hr hrρ hrsq ht₀T hbound
    exact le_trans (ENNReal.ofReal_le_ofReal hlower) (hvol x r hr)

end Poincare.D13.UpstreamAdapter.KleinerLott
