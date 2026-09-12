/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing, part 4: kernel-checked non-vacuity witnesses.**

Every structure and every transfer theorem of the conditional κ-noncollapsing assembly is
instantiated here on an explicit model:

* `M = Unit` with the counting measure `μ = Measure.count` (every ball has measure `1`),
  the curvature predicate `K x r = True`, the constant reduced-volume certificate
  `Ṽ ≡ 1` of the accepted `D7-perelman-conditional-monotonicity` layer, the comparison
  function `φ ≡ 1` and the constants `κ = v₀ = r₀ = τ₀ = 1`.

On this model

* the comparison hypothesis `BallVolumeComparison` holds (`ballVolumeComparison_unit`);
* the main conditional theorem fires (`kappaNoncollapsing_of_entropy_and_volumeComparison_unit`);
* the D7 entropy bridge fires (`kappaNoncollapsing_of_perelmanWMu_unit`) on the zero
  `PerelmanWMuKernelHypotheses` instance;
* the extended `KappaCertificate` is constructed (`unitKappaCertificate`) and the D3 κ-algebra
  consequences fire (`unitKappaCertificate_volume_ball_pos`);
* the state-only `Prop` is inhabited (`perelmanNoncollapsingConclusion_unit`,
  `fullPerelmanNoncollapsing_unit`), so the full statement is consistent and the conditional
  reduction is not vacuous;
* the named-input ledger is nonempty (`perelmanNoncollapsingDependencies_length`).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Kappa.Statements
import Poincare.D7.Monotonicity.Nonvacuity

open MeasureTheory Set
open scoped ENNReal

namespace Poincare
namespace D7
namespace Kappa

open Poincare.Longrun.Topology
open Poincare.D7.Reduced
open Poincare.D7.Monotonicity

noncomputable section

/-! ## 1. The comparison hypothesis on the one-point counting model -/

/-- **The comparison hypothesis holds on `Unit` with the counting measure.**  Every ball is
the whole space, so `μ (B(x,r)) = 1`; for `0 < r ≤ 1` we have `r³ ≤ 1`, hence
`1 ≤ 1 / r³ = normalizedBallVolume μ x r`, and `φ ≡ 1` makes the left-hand side `1`. -/
theorem ballVolumeComparison_unit :
    BallVolumeComparison Unit (Measure.count : Measure Unit) (fun _ _ => True)
      constantReducedVolumeCertificate (fun _ => 1) 1 where
  comparison := by
    intro x r hr _hrle _
    have hball : Metric.eball x (ENNReal.ofReal r) = Set.univ := by
      ext y
      simp [hr]
    have hcount : (Measure.count : Measure Unit) (Metric.eball x (ENNReal.ofReal r)) = 1 := by
      rw [hball]
      simp
    rw [normalizedBallVolume, hcount]
    simp only [ENNReal.ofReal_one]
    have hr3le : ENNReal.ofReal (r ^ 3) ≤ (1 : ℝ≥0∞) := by
      have h3 : r ^ 3 ≤ (1 : ℝ) := by
        simpa using pow_le_pow_left₀ hr.le _hrle 3
      simpa using ENNReal.ofReal_le_ofReal h3
    calc (1 : ℝ≥0∞) = 1 / 1 := by simp
      _ ≤ 1 / ENNReal.ofReal (r ^ 3) := ENNReal.div_le_div_left hr3le 1

/-- The comparison hypothesis is monotone in the comparison function: `φ ≡ 1` dominates
`ψ ≡ 1/2`, so the weaker comparison hypothesis also holds. -/
theorem ballVolumeComparison_unit_half :
    BallVolumeComparison Unit (Measure.count : Measure Unit) (fun _ _ => True)
      constantReducedVolumeCertificate (fun _ => 1 / 2) 1 :=
  BallVolumeComparison.mono ballVolumeComparison_unit (fun _v => by norm_num)

/-! ## 2. Non-vacuity of the main conditional theorem -/

/-- **The main conditional theorem fires on the one-point model.** -/
theorem kappaNoncollapsing_of_entropy_and_volumeComparison_unit :
    KappaNoncollapsingCertificate Unit (Measure.count : Measure Unit) (fun _ _ => True) 1 1 :=
  kappaNoncollapsing_of_entropy_and_volumeComparison constantReducedVolumeCertificate
    (fun _ => 1) one_pos one_pos one_pos (by norm_num) one_pos
    (by simp [constantReducedVolumeCertificate])
    (by intro x _hx y _hy _hxy; exact le_rfl) rfl ballVolumeComparison_unit

/-- **The D7 entropy bridge fires on the zero instance.**  The `W`/`μ` kernel hypotheses of
the accepted monotonicity layer carry the constant reduced-volume certificate, so the
bridge `kappaNoncollapsing_of_perelmanWMu` applies. -/
theorem kappaNoncollapsing_of_perelmanWMu_unit :
    KappaNoncollapsingCertificate Unit (Measure.count : Measure Unit) (fun _ _ => True) 1 1 :=
  kappaNoncollapsing_of_perelmanWMu perelmanWMuKernelHypotheses_zero (fun _ => 1)
    one_pos one_pos one_pos (by norm_num) one_pos
    (by simp [perelmanWMuKernelHypotheses_zero, constantReducedVolumeCertificate])
    (by intro x _hx y _hy _hxy; exact le_rfl) rfl ballVolumeComparison_unit

/-- **The uniform reduced-volume constant on the model.**  `Ṽ ≡ 1 ≥ 1 = v₀` at every
`0 < τ ≤ 1`, by reduced-volume monotonicity. -/
theorem uniformReducedVolumeLowerBound_unit :
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → (1 : ℝ) ≤ constantReducedVolumeCertificate.volume τ :=
  uniformReducedVolumeLowerBound constantReducedVolumeCertificate one_pos
    (by simp [constantReducedVolumeCertificate])

/-- **Entropy monotonicity and the uniform constant on the zero instance.** -/
theorem perelmanWMu_monotone_and_uniformReducedVolume_zero :
    MonotoneOn (fun t : ℝ => (constantFamily () t).W) (Set.Ici 0) ∧
      MonotoneOn (muOfFamily constantFamily) (Set.Ici 0) ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → (1 : ℝ) ≤ constantReducedVolumeCertificate.volume τ :=
  perelmanWMu_monotone_and_uniformReducedVolume perelmanWMuKernelHypotheses_zero ()
    one_pos
    (by simp [perelmanWMuKernelHypotheses_zero, constantReducedVolumeCertificate])

/-! ## 3. Non-vacuity of the extended certificate -/

/-- **The comparison data are inhabited on the one-point model.** -/
def unitKappaComparisonData :
    KappaComparisonData Unit (Measure.count : Measure Unit) (fun _ _ => True) ℝ 1 1 where
  reducedVolume := constantReducedVolumeCertificate
  tau0 := 1
  tau0_pos := one_pos
  scale := by norm_num
  v0 := 1
  v0_pos := one_pos
  v0_le_volume := by simp [constantReducedVolumeCertificate]
  phi := fun _ => 1
  phi_mono := by intro x _hx y _hy _hxy; exact le_rfl
  phi_v0 := rfl
  kappa_pos := one_pos
  r0_pos := one_pos
  comparison := ballVolumeComparison_unit

/-- **The extended κ-certificate is inhabited.** -/
def unitKappaCertificate :
    KappaCertificate Unit (Measure.count : Measure Unit) (fun _ _ => True) ℝ 1 1 :=
  unitKappaComparisonData.toKappaCertificate

/-- **The D3 certificate extracted from the extended certificate.** -/
theorem kappaNoncollapsing_unit :
    KappaNoncollapsingCertificate Unit (Measure.count : Measure Unit) (fun _ _ => True) 1 1 :=
  unitKappaCertificate.toD3

/-- **The D3 κ-algebra consequence fires on the extended certificate.** -/
theorem unitKappaCertificate_volume_ball_pos (x : Unit) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    0 < (Measure.count : Measure Unit) (Metric.eball x (ENNReal.ofReal r)) :=
  unitKappaCertificate.volume_ball_pos hr hr1 trivial

/-- **The D3 κ-algebra monotonicity fires on the extended certificate.**  A certificate with
constant `1` is a certificate with constant `1/2`, and its comparison function is capped at
`1/2`. -/
def unitKappaCertificate_half :
    KappaCertificate Unit (Measure.count : Measure Unit) (fun _ _ => True) ℝ (1 / 2) 1 :=
  unitKappaCertificate.mono (by norm_num) (by norm_num)

/-- **The uniform constant survives on the half-constant certificate.** -/
theorem unitKappaCertificate_half_uniform_volume_lower {τ : ℝ} (hτ : 0 < τ) (hττ : τ ≤ 1) :
    (1 : ℝ) ≤ unitKappaCertificate_half.reducedVolume.volume τ :=
  unitKappaCertificate_half.uniform_volume_lower hτ hττ

/-- **The extended certificate's normalized form fires (K1 → K2).** -/
theorem unitKappaCertificate_normalized :
    NormalizedBallVolumeLowerBound Unit (Measure.count : Measure Unit) (fun _ _ => True) 1 1 :=
  unitKappaCertificate.toNormalizedBallVolumeLowerBound

/-! ## 4. Non-vacuity of the state-only statement and its reductions -/

/-- **The full conclusion is inhabited on the one-point model.** -/
theorem perelmanNoncollapsingConclusion_unit :
    PerelmanNoncollapsingConclusion Unit (Measure.count : Measure Unit) (fun _ _ => True) :=
  ⟨1, 1, kappaNoncollapsing_unit⟩

/-- **The state-only `Prop` is inhabited on the one-point model.** -/
theorem fullPerelmanNoncollapsing_unit :
    fullPerelmanNoncollapsing Unit (Measure.count : Measure Unit) (fun _ _ => True) True :=
  fun _ => perelmanNoncollapsingConclusion_unit

/-- **The reduction from the comparison data fires.** -/
theorem fullPerelmanNoncollapsing_of_comparisonData_unit :
    fullPerelmanNoncollapsing Unit (Measure.count : Measure Unit) (fun _ _ => True) True :=
  fullPerelmanNoncollapsing_of_comparisonData unitKappaComparisonData True

/-- **The reduction from the D7 entropy interface plus comparison fires.** -/
theorem fullPerelmanNoncollapsing_of_entropy_and_comparison_unit :
    fullPerelmanNoncollapsing Unit (Measure.count : Measure Unit) (fun _ _ => True) True :=
  fullPerelmanNoncollapsing_of_entropy_and_comparison perelmanWMuKernelHypotheses_zero
    (fun _ => 1) one_pos one_pos one_pos (by norm_num) one_pos
    (by simp [perelmanWMuKernelHypotheses_zero, constantReducedVolumeCertificate])
    (by intro x _hx y _hy _hxy; exact le_rfl) rfl ballVolumeComparison_unit True

/-- **The D3 entropy-route missing statement is reduced to the comparison data.** -/
theorem missingKappaNoncollapsingOfMuMonotonicity_unit :
    missingKappaNoncollapsingOfMuMonotonicity (Measure.count : Measure Unit)
      (fun _ _ => True) True True :=
  missingKappaNoncollapsingOfMuMonotonicity_of_comparisonData unitKappaComparisonData True True

/-- **The named missing-input ledger is nonempty and has twelve entries.** -/
theorem perelmanNoncollapsingDependencies_nonvacuous :
    perelmanNoncollapsingDependencies.length = 12 ∧ perelmanNoncollapsingDependencies ≠ [] :=
  ⟨perelmanNoncollapsingDependencies_length, perelmanNoncollapsingDependencies_ne_nil⟩

end

end Kappa
end D7
end Poincare
