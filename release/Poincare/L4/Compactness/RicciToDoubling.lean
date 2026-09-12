/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — from the scalar Riccati comparison to explicit volume doubling

This file closes the **measure-growth half of U9 at the scalar/model level, conditional on an
explicit ball-measure realization interface**.  It is *not* a manifold theorem: the
manifold construction (geodesic sphere densities, coarea, curvature → Riccati, and the
two-sided centrewise comparability of a Riemannian ball measure) is stated as an open gap at
the end of the file and is not claimed.  The file consumes

* D12's `Poincare/D12/ComparisonGeodesics/VolumeRatio.lean`
  (`bishopGromov_volume_le`, `bishopGromovVolumeRatio`, `radialVolume_pos_of_pos`),
* D12's `Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean`
  (`euclidModelA`, `euclidModelM`, `euclidModel_volume`, `euclidModelM_riccati`, …),
* the round-3 metric file `Poincare/L4/Compactness/DoublingToCovers.lean` (imported as part
  of the round-3 U9 pair; its declarations are the consumer-side metric-doubling forms — the
  composite bound below is derived through the measure-doubling route of
  `MeasureGrowthCovers.lean`, so no `DoublingToCovers` declaration is invoked directly), and
* the round-3 measure file `Poincare/L4/Compactness/MeasureGrowthCovers.lean`
  (`coveringNumber_le_measure_ratio`, `coveringNumber_le_of_measure_doubling`,
  `coveringNumber_le_of_dyadic_doubling`).

The negative-curvature companion is `Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean`
(the constant-curvature hyperbolic model for `k ≥ −d·κ²`).

The file produces three things:

1. **`euclid_volume_ratio_le_of_ricci_nonneg`** — an *instantiation* of
   `bishopGromov_volume_le` with the explicit Euclidean comparison model
   (`Abar = euclidModelA d = t^d`, `mbar = euclidModelM d = d/t`, `kbar = 0`) for a
   nonnegative scalar curvature function `k ≥ 0` (the name refers to this *scalar* sign
   convention, not to a manifold Ricci tensor).  The model volume ratio is evaluated in
   closed form (`euclidModel_volumeRatio_closedForm`, `euclidModel_volume`):
   `V R / V̄ R ≤ V r / V̄ r` becomes the closed-form bound
   `radialVolume A R ≤ (R / r) ^ (d + 1) * radialVolume A r`
   (`euclid_volumeRatio_div_le_of_ricci_nonneg` is the same statement in ratio form).
2. **`euclid_volume_doubling_of_ricci_nonneg`** — the single-scale doubling consequence
   `radialVolume A (2 r) ≤ 2 ^ (d + 1) * radialVolume A r`, with the model witness
   `euclidModel_hypotheses_witness` (all hypotheses jointly satisfiable) and the sharpness
   identity `euclidModel_volume_doubling_closedForm` (the constant `2 ^ (d + 1)` is
   *attained* on the model, so the bound is sharp, not vacuous).
3. **The ball-measure realization interface** `IsRadialBallMeasure μ A`, a *definition*
   (not an assumed theorem): the additional hypothesis that a measure `μ` on a
   pseudo-metric space has centre-independent closed balls whose measure is the radial
   volume profile, `μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)`.  The theorems
   `coveringNumber_le_measure_ratio_of_radialBallMeasure`,
   `coveringNumber_le_of_radialBallMeasure_doubling` and
   `coveringNumber_le_of_ricci_nonneg_radialBallMeasure` show that this hypothesis
   discharges, for `coveringNumber_le_measure_ratio`, the lower-bound hypothesis `hlower`
   and the measure term `μ (closedBall x (4 r))` on the right of its conclusion, and, for
   `coveringNumber_le_of_measure_doubling` / `coveringNumber_le_of_dyadic_doubling`, the
   lower bound `hlower`, the halving-form doubling hypothesis `hdouble` (derived at the
   three dyadic scales) and the reference-ball comparability `hcomp`.  (`hlower` and `hcomp`
   are the "lower" and "upper" comparison sides; the token `hupper` does not occur in the
   consumed files — in `coveringNumber_le_measure_ratio` there is no upper hypothesis, only
   the upper measure term on the right.)
   **No manifold measure is constructed or claimed**: see the section
   "The manifold gap, stated precisely" at the end of the file.

## Classification of every declaration

Every declaration in this file carries a `**Class:**` line in its docstring:

* `**Class:** model (scalar ODE)` — a statement about real functions on an interval
  (radial area `A`, logarithmic derivative `m`, curvature function `k`) and their
  integrals; no manifold, no metric space, no measure.
* `**Class:** metric–measure interface (non-manifold)` — a statement about an abstract
  pseudo-metric space and an abstract measure, conditional on the interface predicate.
  The composite `coveringNumber_le_of_ricci_nonneg_radialBallMeasure` carries the extended
  label `metric–measure interface (non-manifold), conditional on the scalar model
  hypotheses` because it also takes the scalar hypotheses of Section 2 as arguments.

There is **no manifold-level declaration** in this file.  In particular nothing here
constructs a Riemannian metric, a Riemannian volume measure, a geodesic sphere density, or
a ball-volume identification; those remain the open part of U9.  Nothing here assumes the
Bishop–Gromov conclusion: the closed-form bounds are *derived* from the Riccati
inequality, the model equality and the Euclidean normalization through D12's
`bishopGromov_volume_le`.
-/
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.D12.ComparisonGeodesics.VolumeRatio
import Poincare.L4.Compactness.DoublingToCovers
import Poincare.L4.Compactness.MeasureGrowthCovers

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Poincare.L4.Compactness

open Poincare.D12.ComparisonGeodesics

/-! ## 1. The Euclidean model volume ratio in closed form

The Euclidean comparison model of D12 is `euclidModelA d t = t ^ d` with cumulative volume
`euclidModel_volume : radialVolume (euclidModelA d) t = t ^ (d + 1) / (d + 1)`.  Its volume
ratio is therefore the exact power `(R / r) ^ (d + 1)`; this is the constant that the
Bishop–Gromov comparison transfers to an arbitrary radial area function `A` with `k ≥ 0`. -/

/-- **Class:** model (scalar ODE).

Closed form of the Euclidean model volume ratio:
`V̄ R / V̄ r = (R / r) ^ (d + 1)` for the model `V̄ t = ∫₀ᵗ s ^ d ds`.  Analytic hypotheses:
`0 < d` (dimension parameter `d = n − 1`) and `r ≠ 0`.  No curvature, no manifold. -/
theorem euclidModel_volumeRatio_closedForm {d : ℕ} (hdpos : 0 < d) {r R : ℝ} (hr : r ≠ 0) :
    radialVolume (euclidModelA d) R / radialVolume (euclidModelA d) r = (R / r) ^ (d + 1) := by
  have hd1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hrpow : r ^ (d + 1) ≠ 0 := pow_ne_zero _ hr
  rw [euclidModel_volume, euclidModel_volume, div_pow]
  field_simp

/-- **Class:** model (scalar ODE).

The Euclidean model doubling identity: `V̄ (2 r) = 2 ^ (d + 1) · V̄ r`.  Analytic
hypotheses: `0 < d` and `0 < r`.  This is the sharp form of the doubling consequence; the
inequality `≤` of `euclid_volume_doubling_of_ricci_nonneg` is an equality on the model. -/
theorem euclidModel_volume_doubling_closedForm {d : ℕ} (hdpos : 0 < d) {r : ℝ} (hr : 0 < r) :
    radialVolume (euclidModelA d) (2 * r) = 2 ^ (d + 1) * radialVolume (euclidModelA d) r := by
  have hd1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [euclidModel_volume, euclidModel_volume, mul_pow]
  field_simp

/-! ## 2. Instantiating `bishopGromov_volume_le` with the Euclidean model -/

/-- **Class:** model (scalar ODE).

**Euclidean closed-form Bishop–Gromov volume bound.**  Let `d > 0`, `T > 0`, `C ≥ 0`,
`0 < t₀ ≤ T`.  Suppose:

* (`hk`) the radial curvature function is nonnegative, `0 ≤ k t` on `(0,T)`;
* (`hineq`) the radial area function `A` has logarithmic derivative `m = A'/A` satisfying
  the Riccati inequality `m' + m²/d + k ≤ 0` on `(0,T)`;
* (`hm`, `hmcont`, `hnorm`) `m` has derivative `dm`, is continuous on `(0,T]`, and is
  Euclidean-normalized: `|m t − d/t| ≤ C` on `(0,t₀)`;
* (`hA`, `hAcont`, `hApos`, `hA0`, `hmA`) `A` has derivative `dA` on `(0,T)`, is continuous
  on `[0,T]`, positive on `(0,T]`, vanishes at `0`, and `m = dA/A` there.

Then for `0 < r ≤ R ≤ T`:

    radialVolume A R ≤ (R / r) ^ (d + 1) * radialVolume A r.

This is `bishopGromov_volume_le` instantiated with the explicit Euclidean comparison model
`Abar = euclidModelA d`, `mbar = euclidModelM d`, `kbar = 0` (so `hkk` is `hk`), followed
by the closed-form evaluation `euclidModel_volumeRatio_closedForm`.  Bishop–Gromov is
*proved* here from the Riccati data, not assumed.  The geometric passage from
`Ric ≥ (n−1)K` to `hineq` is not part of this statement. -/
theorem euclid_volume_ratio_le_of_ricci_nonneg {d : ℕ} (hdpos : 0 < d) {T C t₀ : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → 0 ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {r R : ℝ} (hr : r ∈ Ioc 0 T) (hR : R ∈ Ioc 0 T) (hrR : r ≤ R) :
    radialVolume A R ≤ (R / r) ^ (d + 1) * radialVolume A r := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hle := bishopGromov_volume_le (d := (d : ℝ)) hd hT hC ht₀ ht₀T
    (k := k) (kbar := fun _ => 0) (m := m) (dm := dm)
    (mbar := euclidModelM d) (dmbar := euclidModelDm d)
    (A := A) (dA := dA) (Abar := euclidModelA d)
    (dAbar := fun t => (d : ℝ) * t ^ (d - 1))
    hineq
    (fun t ht => euclidModelM_riccati (ne_of_gt ht.1) (ne_of_gt hd))
    (fun _t ht => hk ht)
    hm
    (fun t ht => euclidModelM_hasDerivAt (ne_of_gt ht.1))
    hmcont euclidModelM_contOn hnorm (euclidModelM_normalized hC)
    hA (fun t _ht => euclidModelA_hasDerivAt t) hAcont euclidModelA_contOn hApos
    euclidModelA_pos hA0 (euclidModelA_zero hdpos) hmA
    (fun t ht => (euclidModelA_logDeriv (ne_of_gt ht.1) hdpos).symm)
    hr hR hrR
  calc radialVolume A R
      ≤ (radialVolume (euclidModelA d) R / radialVolume (euclidModelA d) r) *
          radialVolume A r := hle
    _ = (R / r) ^ (d + 1) * radialVolume A r := by
        rw [euclidModel_volumeRatio_closedForm hdpos (ne_of_gt hr.1)]

/-- **Class:** model (scalar ODE).

Ratio form of `euclid_volume_ratio_le_of_ricci_nonneg`.  Analytic hypotheses (listed
explicitly): `0 < d`, `0 < T`, `0 ≤ C`, `0 < t₀ ≤ T`; the scalar curvature function
satisfies `0 ≤ k t` on `(0,T)`; `dm t + m t²/d + k t ≤ 0` on `(0,T)`; `m` has derivative
`dm` on `(0,T)`, is continuous on `(0,T]`, and `|m t − d/t| ≤ C` on `(0,t₀)`; `A` has
derivative `dA` on `(0,T)`, is continuous on `[0,T]`, positive on `(0,T]`, `A 0 = 0`, and
`m = dA/A` on `(0,T)`; `r, R ∈ (0,T]` with `r ≤ R`.  Conclusion:
`radialVolume A R / radialVolume A r ≤ (R / r) ^ (d + 1)`.  Since `A > 0` on `(0,T]` and
`A` is continuous on `[0,T]`, the denominator is positive
(`radialVolume_pos_of_pos`), so the division is legitimate. -/
theorem euclid_volumeRatio_div_le_of_ricci_nonneg {d : ℕ} (hdpos : 0 < d) {T C t₀ : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → 0 ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {r R : ℝ} (hr : r ∈ Ioc 0 T) (hR : R ∈ Ioc 0 T) (hrR : r ≤ R) :
    radialVolume A R / radialVolume A r ≤ (R / r) ^ (d + 1) := by
  have hVpos : 0 < radialVolume A r := radialVolume_pos_of_pos hT hAcont hApos hr
  rw [div_le_iff₀ hVpos]
  exact euclid_volume_ratio_le_of_ricci_nonneg hdpos hT hC ht₀ ht₀T hk hineq hm hmcont hnorm
    hA hAcont hApos hA0 hmA hr hR hrR

/-- **Class:** model (scalar ODE).

**Single-scale volume doubling from a nonnegative radial curvature bound.**  Analytic
hypotheses (listed explicitly, identical to `euclid_volume_ratio_le_of_ricci_nonneg`):
`0 < d`, `0 < T`, `0 ≤ C`, `0 < t₀ ≤ T`; `0 ≤ k t` on `(0,T)`;
`dm t + m t²/d + k t ≤ 0` on `(0,T)`; `m` has derivative `dm` on `(0,T)`, is continuous on
`(0,T]`, and `|m t − d/t| ≤ C` on `(0,t₀)`; `A` has derivative `dA` on `(0,T)`, is
continuous on `[0,T]`, positive on `(0,T]`, `A 0 = 0`, and `m = dA/A` on `(0,T)`; and
`0 < s` with `s ≤ T` and `2 s ≤ T`.  Conclusion:

    radialVolume A (2 * s) ≤ 2 ^ (d + 1) * radialVolume A s.

This is `euclid_volume_ratio_le_of_ricci_nonneg` at `R = 2 s`, where the model ratio
evaluates to `((2 s) / s) ^ (d + 1) = 2 ^ (d + 1)`. -/
theorem euclid_volume_doubling_of_ricci_nonneg {d : ℕ} (hdpos : 0 < d) {T C t₀ : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → 0 ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume A (2 * s) ≤ 2 ^ (d + 1) * radialVolume A s := by
  have hr : s ∈ Ioc 0 T := ⟨hs, hsT⟩
  have hR : 2 * s ∈ Ioc 0 T := ⟨by linarith, h2s⟩
  have hle := euclid_volume_ratio_le_of_ricci_nonneg hdpos hT hC ht₀ ht₀T hk hineq hm hmcont
    hnorm hA hAcont hApos hA0 hmA hr hR (by linarith)
  have hratio : (2 * s / s) ^ (d + 1) = 2 ^ (d + 1) := by
    rw [show 2 * s / s = 2 by field_simp]
  simpa [hratio] using hle

/-! ## 3. Non-vacuity witnesses for the model statements

The witnesses below instantiate the full hypothesis list of
`euclid_volume_doubling_of_ricci_nonneg` with the Euclidean model itself
(`A = euclidModelA d`, `m = euclidModelM d`, `k = 0`) and verify the conclusion with
concrete numbers.  Since the model attains equality (`euclidModel_volume_doubling_closedForm`)
the bound is sharp, not merely satisfiable. -/

/-- **Class:** model (scalar ODE).

The Euclidean model satisfies *every* analytic hypothesis of
`euclid_volume_doubling_of_ricci_nonneg` (`k = 0 ≥ 0`, `m = mbar = d/t`, `A = t^d`,
`C = 0`, `t₀ = T`), so the hypothesis set is jointly satisfiable.  This is a *use* of the
instantiated theorem, not a new assumption. -/
theorem euclidModel_hypotheses_witness {d : ℕ} (hdpos : 0 < d) {T : ℝ} (hT : 0 < T)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume (euclidModelA d) (2 * s) ≤ 2 ^ (d + 1) * radialVolume (euclidModelA d) s :=
  euclid_volume_doubling_of_ricci_nonneg (d := d) hdpos hT (le_refl (0 : ℝ)) hT le_rfl
    (k := fun _ => 0) (m := euclidModelM d) (dm := euclidModelDm d)
    (A := euclidModelA d) (dA := fun t => (d : ℝ) * t ^ (d - 1))
    (fun _t _ht => le_rfl)
    (fun t ht => (euclidModelM_riccati (ne_of_gt ht.1) (by exact_mod_cast hdpos.ne')).le)
    (fun t ht => euclidModelM_hasDerivAt (ne_of_gt ht.1))
    euclidModelM_contOn (euclidModelM_normalized (C := (0 : ℝ)) (t₀ := T) le_rfl)
    (fun _t _ht => euclidModelA_hasDerivAt _) euclidModelA_contOn euclidModelA_pos
    (euclidModelA_zero hdpos)
    (fun t ht => (euclidModelA_logDeriv (ne_of_gt ht.1) hdpos).symm)
    hs hsT h2s

/-- **Class:** model (scalar ODE).

Numeric sharpness witness in dimension parameter `d = 1`: the Euclidean model satisfies
`V (2 · 1) = 2 ^ (1 + 1) · V 1` exactly, i.e. `2 = 4 · (1/2)`.  The general-`d` sharpness
identity is `euclidModel_volume_doubling_closedForm` (equality `V (2r) = 2^(d+1) · V r` for
every `d ≥ 1` and `r > 0`); this `d = 1` instance is its concrete numeric form. -/
theorem radialVolume_euclidModel_one_doubling_witness :
    radialVolume (euclidModelA 1) (2 * 1) = 2 ^ (1 + 1) * radialVolume (euclidModelA 1) 1 := by
  have h := euclidModel_volume_doubling_closedForm (d := 1) (by norm_num) (r := (1 : ℝ))
    (by norm_num)
  simpa using h

/-- **Class:** model (scalar ODE).

Numeric witness for the bound of `euclid_volume_doubling_of_ricci_nonneg` in dimension
parameter `d = 1` at scale `s = 1`: the values are `V 2 = 2` and `V 1 = 1/2`, so the
doubling bound `V 2 ≤ 2 ^ (1+1) · V 1` reads `2 ≤ 2`, i.e. it is attained. -/
theorem radialVolume_euclidModel_one_value_witness :
    radialVolume (euclidModelA 1) 2 = 2 ∧ radialVolume (euclidModelA 1) 1 = 1 / 2 := by
  constructor <;> rw [euclidModel_volume] <;> norm_num

/-! ## 4. The ball-measure realization interface

The round-3 measure file `MeasureGrowthCovers.lean` proves the counting estimates

* `coveringNumber_le_measure_ratio` — hypotheses `hm : 0 < m` and
  `hlower : ∀ y ∈ closedBall x (2 r), m ≤ μ (closedBall y (r / 2))`, conclusion
  `coveringNumber r (closedBall x (2 r)) ≤ μ (closedBall x (4 r)) / m`;
* `coveringNumber_le_of_measure_doubling` — additionally the halving-form doubling
  hypothesis `hdouble : ∀ y s, μ (closedBall y s) ≤ C · μ (closedBall y (s / 2))` and the
  reference-ball upper comparability `hcomp : μ (closedBall x (r / 2)) ≤ K · m`.

The definition `IsRadialBallMeasure` below is the **precise additional hypothesis** that
realizes the radial volume profile `radialVolume A` as a genuine ball measure and thereby
discharges the lower bound (`hlower`) and the upper side (the measure term on the right of
`coveringNumber_le_measure_ratio`, and the comparability hypothesis `hcomp` of
`coveringNumber_le_of_measure_doubling`).  It is a *definition*, never assumed as a theorem:
the lemmas in this section are conditional implications, and no measure on any manifold is
constructed. -/

/-- **Class:** metric–measure interface (non-manifold).

**Interface predicate (definition, not an assumed theorem).**  A measure `μ` on a
pseudo-metric space `X` *realizes the radial volume profile* `A : ℝ → ℝ` if every closed
ball, at every centre and every real radius, has `μ`-measure equal to the radial volume:
`μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)`.

This is exactly the additional hypothesis that makes `radialVolume A` a genuine ball
measure with a *centre-independent* profile.  It is deliberately not claimed for any
manifold, Riemannian metric or curvature bound.  The `ENNReal.ofReal` coercion is the
canonical map `ℝ → ℝ≥0∞` (negatives truncate to `0`), so the identity is required for all
real radii, negative ones included; for `s < 0` the closed ball is empty (left-hand side
`0`) while the right-hand side is `0` exactly when `∫₀ˢ A ≤ 0`, so the negative-radius part
is a genuine constraint on `A` (all uses below are at positive radii).

The angular constant `ω_{n−1}` of the unit sphere is *absent* here: a genuine Riemannian
ball measure would satisfy the identity with `radialVolume A` replaced by
`ω_{n−1} · radialVolume A`; the constant cancels in every ratio used below, which is why
the normalized profile is the right interface for covering-number bounds.  The
non-normalized version is recorded in the gap section at the end of the file. -/
def IsRadialBallMeasure {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (A : ℝ → ℝ) : Prop :=
  ∀ (x : X) (s : ℝ), μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)

/-- **Class:** metric–measure interface (non-manifold).

Non-vacuity of the interface predicate on the real line: Lebesgue measure and the constant
profile `A ≡ 2` satisfy `IsRadialBallMeasure volume (fun _ => 2)`, because
`volume (closedBall x s) = ofReal (2 s) = ofReal (∫₀ˢ 2)`.  This is the *unnormalized*
(angular-constant-included) 1-dimensional Euclidean ball profile: the normalized profile of
the file's convention is `euclidModelA 0 ≡ 1`, and `ω₀ · euclidModelA 0 = 2 · 1 = 2`.
It witnesses that the interface predicate is not an empty hypothesis; it is **not** a
manifold statement.  The profile `A ≡ 2` does not satisfy the model hypotheses
(`A 0 = 0` fails), so a *joint* realization of the interface and the scalar hypotheses
requires a different construction; the gap section records a concrete informal one
(the snowflake metric), which shows the composite theorem below is not vacuous. -/
theorem isRadialBallMeasure_real_witness :
    IsRadialBallMeasure (volume : Measure ℝ) (fun _ : ℝ => (2 : ℝ)) := by
  intro x s
  rw [Real.volume_closedBall]
  congr 1
  unfold radialVolume
  rw [intervalIntegral.integral_const]
  ring

/-- **Class:** metric–measure interface (non-manifold).

**Discharging the hypotheses of `coveringNumber_le_measure_ratio`.**  If `μ` realizes the
profile `radialVolume A` at every centre and `radialVolume A (r / 2) > 0`, then the lower
bound `hlower` holds with `m = radialVolume A (r / 2)` at *every* centre of
`closedBall x (2 r)` (this is where centre-independence is used), and the upper measure term
`μ (closedBall x (4 r))` evaluates to `ofReal (radialVolume A (4 r))`.  Conclusion:

    coveringNumber r (closedBall x (2 r)) ≤ radialVolume A (4 r) / radialVolume A (r / 2).

The `ENNReal.ofReal`-divisions are the canonical `ℝ≥0∞` divisions. -/
theorem coveringNumber_le_measure_ratio_of_radialBallMeasure
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {A : ℝ → ℝ} {r : ℝ≥0} {x : X}
    (hμ : IsRadialBallMeasure μ A) (hpos : 0 < radialVolume A ((r : ℝ) / 2)) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      ENNReal.ofReal (radialVolume A (4 * (r : ℝ))) /
        ENNReal.ofReal (radialVolume A ((r : ℝ) / 2)) := by
  set m : ℝ≥0 := ⟨radialVolume A ((r : ℝ) / 2), hpos.le⟩ with hmdef
  have hmR : (0 : ℝ) < (m : ℝ) := by rw [hmdef]; exact hpos
  have hm : 0 < m := by exact_mod_cast hmR
  have hcoe : (m : ℝ≥0∞) = ENNReal.ofReal (radialVolume A ((r : ℝ) / 2)) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  have hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)) := by
    intro y _
    rw [hμ y, hcoe]
  have h := coveringNumber_le_measure_ratio (μ := μ) (r := r) (m := m) hm hlower
  rwa [hμ x, hcoe] at h

/-- **Class:** metric–measure interface (non-manifold).

**Discharging the hypotheses of `coveringNumber_le_of_measure_doubling`.**  Assume:

* (`hμ`) `μ` realizes the profile `radialVolume A` (centre-independent balls);
* (`hdbl`) the halving-form volume doubling `radialVolume A s ≤ C · radialVolume A (s / 2)`
  for every real `s` — this is the *interface* form of the doubling inequality; the
  scalar half of it (in the equivalent form `radialVolume A (2 t) ≤ C · radialVolume A t`)
  is proved for `A` from the Riccati hypotheses in Section 2 at all scales `t` with
  `2 t ≤ T`, i.e. the halving form at all scales `s ≤ T`, while the all-scales statement
  beyond `T` is not derived here;
* (`hpos`) the reference half-ball has positive profile, `radialVolume A (r / 2) > 0`
  (the non-collapsing input);
* (`hcomp`) the reverse comparability `radialVolume A (r / 2) ≤ K · radialVolume A (r / 2)`
  for the reference half-ball (an upper bound on the reference ball; with the exact profile
  it holds for `K = 1`).

Then `coveringNumber r (closedBall x (2 r)) ≤ C ^ 3 · K`. -/
theorem coveringNumber_le_of_radialBallMeasure_doubling
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {A : ℝ → ℝ} {C K : ℝ≥0} {r : ℝ≥0} {x : X}
    (hμ : IsRadialBallMeasure μ A)
    (hdbl : ∀ s : ℝ, radialVolume A s ≤ (C : ℝ) * radialVolume A (s / 2))
    (hpos : 0 < radialVolume A ((r : ℝ) / 2))
    (hcomp : radialVolume A ((r : ℝ) / 2) ≤ (K : ℝ) * radialVolume A ((r : ℝ) / 2)) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤ (C : ℝ≥0∞) ^ 3 * (K : ℝ≥0∞) := by
  set m : ℝ≥0 := ⟨radialVolume A ((r : ℝ) / 2), hpos.le⟩ with hmdef
  have hmR : (0 : ℝ) < (m : ℝ) := by rw [hmdef]; exact hpos
  have hm : 0 < m := by exact_mod_cast hmR
  have hcoe : (m : ℝ≥0∞) = ENNReal.ofReal (radialVolume A ((r : ℝ) / 2)) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  have hCcoe : (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) := ENNReal.coe_nnreal_eq C
  have hKcoe : (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) := ENNReal.coe_nnreal_eq K
  have hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)) := by
    intro y _
    rw [hμ y, hcoe]
  have hdouble : ∀ (y : X) (s : ℝ),
      μ (closedBall y s) ≤ (C : ℝ≥0∞) * μ (closedBall y (s / 2)) := by
    intro y s
    rw [hμ y, hμ y, hCcoe]
    calc ENNReal.ofReal (radialVolume A s)
        ≤ ENNReal.ofReal ((C : ℝ) * radialVolume A (s / 2)) :=
          ENNReal.ofReal_le_ofReal (hdbl s)
      _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (radialVolume A (s / 2)) :=
          ENNReal.ofReal_mul C.2
  have hcompp : μ (closedBall x ((r : ℝ) / 2)) ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞) := by
    rw [hμ x, hcoe, hKcoe]
    calc ENNReal.ofReal (radialVolume A ((r : ℝ) / 2))
        ≤ ENNReal.ofReal ((K : ℝ) * radialVolume A ((r : ℝ) / 2)) :=
          ENNReal.ofReal_le_ofReal hcomp
      _ = ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (radialVolume A ((r : ℝ) / 2)) :=
          ENNReal.ofReal_mul K.2
  exact coveringNumber_le_of_measure_doubling (μ := μ) (C := C) (K := K) (r := r) (m := m)
    hdouble hm hlower hcompp

/-! ## 5. The composite bound: nonnegative curvature + ball realization ⟹ covering numbers

The next theorem combines the scalar half (Section 2) with the interface (Section 4): the
three dyadic radial-volume inequalities needed by `coveringNumber_le_of_dyadic_doubling` are
*derived* from the Riccati data through `euclid_volume_doubling_of_ricci_nonneg`, the lower
bound and the reference comparability are discharged by `IsRadialBallMeasure`, and the
resulting bound is `coveringNumber r (closedBall x (2 r)) ≤ (2 ^ (d + 1)) ^ 3`. -/

/-- **Class:** metric–measure interface (non-manifold), conditional on the scalar model
hypotheses.

**Composite covering bound.**  Let `d > 0`, `T > 0`, `C ≥ 0`, `0 < t₀ ≤ T`.  Suppose the
radial area function `A` satisfies the scalar hypotheses of Section 2 (nonnegative radial
curvature `k ≥ 0`; Riccati inequality `m' + m²/d + k ≤ 0`; continuity and Euclidean
normalization of `m`; `A` differentiable on `(0,T)`, continuous on `[0,T]`, positive on
`(0,T]`, `A 0 = 0`, `m = A'/A`), and suppose `μ` realizes the profile `radialVolume A`
(`IsRadialBallMeasure μ A`).  Then for every `r > 0` with `4 r ≤ T` and every `x`,

    coveringNumber r (closedBall x (2 r)) ≤ (2 ^ (d + 1)) ^ 3.

The bound is the cube of the doubling constant: three halvings (`4r → 2r → r → r/2`) each
cost `2 ^ (d + 1)`.  The measure `μ` is an interface input, not constructed here. -/
theorem coveringNumber_le_of_ricci_nonneg_radialBallMeasure
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℕ} (hdpos : 0 < d) {T C t₀ : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → 0 ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {μ : Measure X} (hμ : IsRadialBallMeasure μ A)
    {r : ℝ≥0} (hr0 : 0 < r) (hrT : 4 * (r : ℝ) ≤ T) (x : X) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      (((2 : ℝ≥0) ^ (d + 1)) ^ 3 : ℝ≥0) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  -- the three dyadic radial-volume inequalities, derived from the Riccati data
  have hV4 : radialVolume A (4 * (r : ℝ)) ≤ (2 : ℝ) ^ (d + 1) * radialVolume A (2 * (r : ℝ)) := by
    have h := euclid_volume_doubling_of_ricci_nonneg (d := d) hdpos hT hC ht₀ ht₀T hk hineq
      hm hmcont hnorm hA hAcont hApos hA0 hmA (s := 2 * (r : ℝ))
      (by linarith) (by linarith) (by linarith)
    simpa [show 2 * (2 * (r : ℝ)) = 4 * (r : ℝ) by ring] using h
  have hV2 : radialVolume A (2 * (r : ℝ)) ≤ (2 : ℝ) ^ (d + 1) * radialVolume A (r : ℝ) :=
    euclid_volume_doubling_of_ricci_nonneg (d := d) hdpos hT hC ht₀ ht₀T hk hineq
      hm hmcont hnorm hA hAcont hApos hA0 hmA (s := (r : ℝ))
      hrR (by linarith) (by linarith)
  have hV1 : radialVolume A (r : ℝ) ≤ (2 : ℝ) ^ (d + 1) * radialVolume A ((r : ℝ) / 2) := by
    have h := euclid_volume_doubling_of_ricci_nonneg (d := d) hdpos hT hC ht₀ ht₀T hk hineq
      hm hmcont hnorm hA hAcont hApos hA0 hmA (s := (r : ℝ) / 2)
      (by linarith) (by linarith) (by linarith)
    simpa [show 2 * ((r : ℝ) / 2) = (r : ℝ) by ring] using h
  -- positivity of the reference half-ball profile (non-collapsing input)
  have hpos : 0 < radialVolume A ((r : ℝ) / 2) :=
    radialVolume_pos_of_pos hT hAcont hApos ⟨by linarith, by linarith⟩
  set mm : ℝ≥0 := ⟨radialVolume A ((r : ℝ) / 2), hpos.le⟩ with hmdef
  have hmmR : (0 : ℝ) < (mm : ℝ) := by rw [hmdef]; exact hpos
  have hmm : 0 < mm := by exact_mod_cast hmmR
  have hcoe : (mm : ℝ≥0∞) = ENNReal.ofReal (radialVolume A ((r : ℝ) / 2)) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  have hCcoe : (((2 : ℝ≥0) ^ (d + 1) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ (d + 1)) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  have hconv : ∀ {s t : ℝ}, radialVolume A s ≤ (2 : ℝ) ^ (d + 1) * radialVolume A t →
      μ (closedBall x s) ≤ (((2 : ℝ≥0) ^ (d + 1) : ℝ≥0) : ℝ≥0∞) * μ (closedBall x t) := by
    intro s t hst
    rw [hμ x, hμ x, hCcoe]
    calc ENNReal.ofReal (radialVolume A s)
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (d + 1) * radialVolume A t) :=
          ENNReal.ofReal_le_ofReal hst
      _ = ENNReal.ofReal ((2 : ℝ) ^ (d + 1)) * ENNReal.ofReal (radialVolume A t) :=
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (d + 1))
  have hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (mm : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)) := by
    intro y _
    rw [hμ y, hcoe]
  have hcomp : μ (closedBall x ((r : ℝ) / 2)) ≤ (1 : ℝ≥0∞) * (mm : ℝ≥0∞) := by
    rw [hμ x, hcoe]
    simp
  have h := coveringNumber_le_of_dyadic_doubling (μ := μ) (x := x) (m := mm)
    (C := (2 : ℝ≥0) ^ (d + 1)) (K := 1) (r := r) (hconv hV4) (hconv hV2) (hconv hV1)
    hmm hlower hcomp
  simpa using h

/-! ## 6. The manifold gap, stated precisely

Nothing above is a manifold statement.  The following inputs are **not** formalized here and
are exactly what remains of U9 (measure-growth half):

1. **Sphere density.**  A Riemannian manifold `(M, g)`, a point `x`, and a radial area
   function `A` identified with the `(n−1)`-dimensional area of the geodesic spheres
   `∂B(x, s)` (via the geodesic exponential map and the shape-operator/Riccati equation
   `S' + S² + R_γ = 0`).
2. **Coarea/ball decomposition.**  The identity `vol (closedBall x s) = ω_{n−1} ∫₀ˢ A`,
   i.e. the metric ball is measurably isomorphic to `[0, s] × S^{n−1}` with the induced
   density.  This is the *angular constant* `ω_{n−1}` mentioned above; it cancels in the
   ratios used by the covering-number theorems but is part of the honest ball formula.
3. **Curvature → Riccati.**  The passage from a Ricci/radial curvature bound to the scalar
   Riccati inequality `m' + m²/d + k ≤ 0` (the Cauchy–Schwarz step `tr S² ≥ (tr S)²/d`).
4. **Centre-independence / two-sided comparability.**  The hypotheses of
   `coveringNumber_le_measure_ratio` require the lower bound `m` at *every* centre
   `y ∈ closedBall x (2 r)`.  In a general manifold the ball volume depends on the centre;
   what is needed is a two-sided comparability `m ≤ vol (closedBall y (r/2))` for all such
   `y`, which in the Cheeger–Gromov route comes from Bishop–Gromov (upper) together with
   κ-non-collapsing (lower), *not* from an exact centre-independent profile.  The predicate
   `IsRadialBallMeasure` is the strongest (exact, centre-independent) form of this input;
   the weaker comparability form is what a manifold proof would actually establish.

**The composite is not vacuous (informal witness).**  `isRadialBallMeasure_real_witness`
realizes the interface predicate alone (on `ℝ` with the usual metric, with the constant
profile `A ≡ 2`), and `euclidModel_hypotheses_witness` realizes the scalar hypotheses alone.
A *joint* realization also exists, but not on the usual metric of `ℝ`: with the usual metric,
centre-independence of a measure forces the profile `V(s) = μ(closedBall x s)` to be additive
on positive increments (`μ([x, x+ℓ])` is independent of `x`, so `V(x+y) = V(x) + V(y)` for
`x,y ≥ 0`), hence `V(s) = λs` and `A ≡ λ`, contradicting `A > 0` on `(0,T]` together with
`A 0 = 0`.  The following non-manifold metric–measure space does realize the conjunction
(this construction was supplied by an independent adversarial review; it is recorded here
**informally**, it is not a kernel-checked declaration):

* `X = ℝ` with the snowflake metric `d(x,y) = √|x − y|` (a genuine metric inducing the usual
  topology, hence the usual Borel structure);
* `μ =` Lebesgue measure, `A(t) = 4|t|`.

Then for `s ≥ 0`, `closedBall x s = [x − s², x + s²]`, so `μ = ofReal (2 s²)`, and for
`s < 0` the ball is empty and both sides are `0`; while `radialVolume A s = 2 s |s|`.  Hence
`IsRadialBallMeasure μ A` holds for every real `s`.  With `d = 1`, `k = 0`, `C = 0`,
`m(t) = 1/t`, `dm(t) = −1/t²`, `dA = 4`, the scalar hypotheses of Section 2 hold on `(0,T)`
(the Riccati relation is the equality `−1/t² + (1/t)² + 0 = 0`), so the hypothesis set of
`coveringNumber_le_of_ricci_nonneg_radialBallMeasure` is jointly satisfiable.  What remains
open — and is *not* claimed — is the **manifold** realization of items 1–4; the composite
result is a non-vacuous conditional metric–measure interface, not a manifold theorem.
This paragraph is informal (none of it is kernel-checked).
-/

end Poincare.L4.Compactness
