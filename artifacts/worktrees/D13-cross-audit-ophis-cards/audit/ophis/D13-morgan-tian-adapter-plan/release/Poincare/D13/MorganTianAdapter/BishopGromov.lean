/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# MorganTian adapter: Bishop-Gromov comparison and the flat-model κ-noncollapsing (blocker U9)

Objective blocker **U9** records that the local program has no reduced length/volume, no
pointed Gromov-Hausdorff compactness, no canonical-neighborhood theorem and no surgery
machinery.  The pinned Frenzymath snapshot provides a large part of the *geometric* half of
this in MorganTian:

* Bishop-Gromov: `MorganTianLib.bishop_gromov_ball` (Ch01/BishopGromovBall.lean:226),
  `bishop_gromov_ball_ratio` (:466), `bishop_gromov_manifold_ratio`
  (Ch01/BishopGromovManifold.lean:302), `BishopGromovManifoldProducers` (:456),
  `bishop_gromov_manifold_with_producers` (:519, theorem), the model densities
  `snK`/`csK`/`ctK` (Ch01/ComparisonFunctions.lean:56/65/73), the Jacobi comparisons
  `ricci_curvature_comparison_of_not_conjugate` (Ch01/ComparisonGeometric.lean:134) and
  `ricci_curvature_comparison_radial_of_minimizing` (Ch01/ComparisonMinimizing.lean:254);
* pointed Gromov-Hausdorff: the full Ch05 layer (`PointedGH.lean`,
  `PointedGHNetCharacterization.lean`, `MarkedGHExtraction.lean`, `Precompactness.lean`,
  `PointedGHConverges` Ch05/PointedGH.lean:845);
* ε-necks (the canonical-neighbourhood building block): `EpsilonNeckStructure`
  (Ch02/EpsilonNeck.lean:195), `roundSphereMetric` (:136), `IsRoundCylinderMetric` (:158),
  `canonicalScalarCurvature` (:179).

**Decisive negatives (verified against the pinned snapshot):** there is **no** Lean
declaration for Perelman reduced volume / reduced length / reduced distance / L-minimizers
anywhere in the snapshot (0 grep hits in every package, including MorganTian); surgery and
canonical-neighbourhood occur only in docstrings.  The snapshot has the geometric
ingredients (comparison geometry, GH theory, ε-necks) but **not** the Perelman layer that
the local KV-ledger (`Poincare.D12.KappaVariational.kappaVariationalRemainingDependencies`)
still lists as missing.

**What this file proves (model theorems + one general analysis lemma):**

* `antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one` — the general analysis content of the
  upstream normalization conclusion of `bishop_gromov_manifold_with_producers`: an antitone
  ball-volume/model-volume ratio on `(0,R)` that tends to `1` at `0⁺` is `≤ 1` everywhere.
  This is the *upper* comparison direction of Bishop-Gromov (the ratio decreases away from
  the normalization `1`).
* `flatModel_normalizedBallVolume_eq` — on flat `ℝ³` the local normalized ball volume
  `μ(B(x,r))/r³` equals the model constant `ω₃ = 4π/3` (mathlib
  `EuclideanSpace.volume_ball_fin_three`) — the **equality case** of the Bishop-Gromov
  comparison in constant curvature `0`.
* `flatModel_ballVolumeComparison` — the **model case of KV-10 / NCF-9**: the D7
  `BallVolumeComparison` hypothesis on flat `ℝ³` with the constant comparison function
  `φ ≡ ω₃` is *proved* (it is an equality).
* `flatModel_kappaNoncollapsingCertificate` — downstream use of the D12 conditional
  transfer: with the comparison discharged, the D12 theorem
  `gaussianKappaNoncollapsing_of_ballVolumeComparison` produces a D3
  `KappaNoncollapsingCertificate` on flat `ℝ³` with `κ = 4π/3`, `r₀ = 1`.  The certificate
  is then consumed (`flatModel_volume_ball_pos`).

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted` occurs in this file.
-/

import Poincare.D12.KappaVariational.Statements
import Poincare.D13.MorganTianAdapter.Curvature
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open scoped BigOperators Topology ENNReal

noncomputable section

namespace Poincare.D13.MorganTianAdapter.BishopGromov

open MeasureTheory Filter
open Poincare.Longrun.Topology
open Poincare.D7.Kappa
open Poincare.D12.KappaVariational

/-! ## 1. The analysis core of the Bishop-Gromov normalization conclusion -/

/-- **Upper comparison core (U9).**  If a ratio `f` of ball volume over model-ball volume is
antitone on `(0,R)` and tends to `1` as the radius tends to `0` from the right, then
`f r ≤ 1` for every `r ∈ (0,R)`.  This is exactly the normalization half of the upstream
`bishop_gromov_manifold_with_producers` conclusion
(Ch01/BishopGromovManifold.lean:519, whose antitone ratio and `𝓝[>] 0`-normalization limit
`1` are the two hypotheses here).  Proved by the standard contradiction: `1 < f r` forces
`1 < f s` for all `s ∈ (0,r)` by antitonicity, contradicting convergence to `1`.
Class: local proved theorem (general analysis lemma; no geometric data). -/
theorem antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one {R : ℝ} (_hR : 0 < R) {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Set.Ioo 0 R)) (hlim : Tendsto f (𝓝[>] 0) (𝓝 1)) {r : ℝ}
    (hr : r ∈ Set.Ioo 0 R) : f r ≤ 1 := by
  by_contra hnot
  have hgt : 1 < f r := lt_of_not_ge hnot
  have hpos : 0 < (f r - 1) / 2 := half_pos (sub_pos.mpr hgt)
  obtain ⟨δ, hδ, hclose⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlim) ((f r - 1) / 2) hpos
  let s : ℝ := (min δ r) / 2
  have hs0 : 0 < s := half_pos (lt_min hδ hr.1)
  have hsr : s < r := by
    exact lt_of_lt_of_le (half_lt_self (lt_min hδ hr.1)) (min_le_right _ _)
  have hsδ : s < δ := by
    exact lt_of_lt_of_le (half_lt_self (lt_min hδ hr.1)) (min_le_left _ _)
  have hclose_s := hclose (by simpa using hs0) (by
    rw [Real.dist_eq]
    simpa [sub_zero, abs_of_pos hs0] using hsδ)
  have hfs : f s < f r := by
    have hd : |f s - 1| < (f r - 1) / 2 := by simpa [Real.dist_eq] using hclose_s
    have hle1 : f s - 1 ≤ |f s - 1| := le_abs_self _
    linarith
  have hant := hanti (show s ∈ Set.Ioo 0 R from ⟨hs0, lt_trans hsr hr.2⟩)
    (show r ∈ Set.Ioo 0 R from hr) (le_of_lt hsr)
  exact (not_lt_of_ge hant) hfs

/-! ## 2. The flat-model comparison (the equality case of Bishop-Gromov) -/

/-- The emetric ball of an `ENNReal` radius `ofReal r` with `r > 0` is the ordinary metric
ball.  Class: local proved theorem. -/
theorem eball_ofReal_eq_ball {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) {r : ℝ}
    (hr : 0 < r) :
    Metric.eball x (ENNReal.ofReal r) = Metric.ball x r := by
  ext y
  rw [Metric.mem_eball, Metric.mem_ball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hr]

/-- **Flat-model Bishop-Gromov equality.**  On flat `ℝ³` the local normalized ball volume
`μ(B(x,r))/r³` equals the model constant `ω₃ = π·4/3` (mathlib
`EuclideanSpace.volume_ball_fin_three`).  This is the equality case of the upstream
Bishop-Gromov comparison in constant curvature `0`, and the model discharge of the
`flat_model_power_identification` producer of `BishopGromovManifoldProducers`
(Ch01/BishopGromovManifold.lean:456) with `C = ω₃`.  Class: local proved theorem
(model computation; consumes mathlib ball volume). -/
theorem flatModel_normalizedBallVolume_eq {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin 3)) :
    normalizedBallVolume (volume : Measure (EuclideanSpace ℝ (Fin 3))) x r
      = ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [normalizedBallVolume]
  rw [eball_ofReal_eq_ball x hr]
  rw [EuclideanSpace.volume_ball_fin_three x r]
  have hpow : (ENNReal.ofReal r) ^ (3 : ℕ) = ENNReal.ofReal (r ^ (3 : ℕ)) := by
    calc
      (ENNReal.ofReal r) ^ (3 : ℕ) = ENNReal.ofReal r ^ (2 : ℕ) * ENNReal.ofReal r := by
        norm_num [pow_succ]
      _ = (ENNReal.ofReal r * ENNReal.ofReal r) * ENNReal.ofReal r := by
        norm_num [pow_succ]
      _ = ENNReal.ofReal (r * r) * ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul hr.le]
      _ = ENNReal.ofReal ((r * r) * r) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hr.le hr.le)]
      _ = ENNReal.ofReal (r ^ (3 : ℕ)) := by
        ring_nf
  rw [hpow]
  rw [mul_comm (ENNReal.ofReal (r ^ (3 : ℕ))) (ENNReal.ofReal (Real.pi * 4 / 3))]
  rw [ENNReal.mul_div_cancel_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr 3))) ENNReal.ofReal_ne_top]

/-- **Model case of KV-10 / NCF-9 (the D7 ball-volume comparison).**  On flat `ℝ³` with the
trivial curvature predicate and the Gaussian reduced-volume certificate (volume `≡ 1`), the
`BallVolumeComparison` hypothesis holds for the constant comparison function
`φ ≡ ω₃ = 4π/3`: `ENNReal.ofReal (φ (Ṽ(r²))) = ω₃ ≤ μ(B(x,r))/r³`, with **equality** by
`flatModel_normalizedBallVolume_eq`.  Class: local proved theorem (model theorem; the only
missing D7 input on this model — `ballVolumeComparisonExists` — is now proved for the
flat constant-curvature family). -/
theorem flatModel_ballVolumeComparison (r₀ : ℝ) :
    BallVolumeComparison (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True)
      (gaussianReducedVolumeCertificate 3) (fun _ => 4 * Real.pi / 3) r₀ := by
  refine ⟨fun x r hr hr₀ hK => ?_⟩
  rw [flatModel_normalizedBallVolume_eq hr x]
  rw [show (4 * Real.pi / 3 : ℝ) = Real.pi * 4 / 3 by ring]

/-- **Downstream use of the D12 conditional transfer on the flat model.**  With the
ball-volume comparison discharged (`flatModel_ballVolumeComparison`), the D12 theorem
`gaussianKappaNoncollapsing_of_ballVolumeComparison` produces a D3
`KappaNoncollapsingCertificate` on flat `ℝ³` with `κ = 4π/3` at scale `r₀ = 1`: under the
trivial curvature predicate every ball `B(x,r)` with `0 < r ≤ 1` has volume
`(4π/3)·r³`.  Class: local proved theorem (model theorem; consumes the D12 deliverable). -/
theorem flatModel_kappaNoncollapsingCertificate :
    KappaNoncollapsingCertificate (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True)
      (4 * Real.pi / 3) 1 := by
  exact gaussianKappaNoncollapsing_of_ballVolumeComparison (κ := 4 * Real.pi / 3) (r₀ := 1)
    (by positivity : 0 < 4 * Real.pi / 3) zero_lt_one (by norm_num)
    (by intro x _ y _ _; rfl) (by rfl) (flatModel_ballVolumeComparison 1)

/-- **Checked consequence.**  On the flat model every curvature-bounded ball of radius
`0 < r ≤ 1` has positive volume — the D3 non-collapsing algebra
(`KappaNoncollapsingCertificate.volume_ball_pos`) applied to the flat-model certificate.
Class: local proved theorem (downstream use). -/
theorem flatModel_volume_ball_pos {x : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) :
    0 < volume (Metric.eball x (ENNReal.ofReal r)) :=
  flatModel_kappaNoncollapsingCertificate.volume_ball_pos hr hr1 trivial

end Poincare.D13.MorganTianAdapter.BishopGromov
