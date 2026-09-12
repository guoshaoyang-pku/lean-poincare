/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — the Euclidean model: non-vacuity witness for the singular Riccati comparison

This file proves that the hypothesis set of the (v2, corrected-domain) singular Riccati
comparison and of the full Bishop–Gromov chain is **jointly satisfiable**, by exhibiting
the Euclidean model:

* `euclidModelM d t = d / t` — the logarithmic derivative of the `d`-dimensional radial
  area `t ↦ t^d`; it satisfies the Riccati *equality* `m' + m²/d + 0 = 0` on `(0,T)`,
  is continuous on `(0,T]`, and satisfies the Euclidean normalization
  `|m t − d/t| = 0 ≤ C` (so `C = 0` works);
* `euclidModelA d t = t ^ d` (`d : ℕ`, `d ≥ 1`) — the Euclidean radial area, with
  `A'/A = d/t = m`, `A > 0` on `(0,T]`, `A 0 = 0`, continuous on `[0,T]`.

The two witness theorems

* `euclidModel_singular_comparison` — instantiates `riccati_le_of_singular_normalization`
  with `m = m̄ = d/t`, `k = k̄ = 0`, `C = 0`, proving the hypotheses are consistent
  (hence the comparison theorem is **non-vacuous**), and
* `euclidModel_bishopGromov` — instantiates `bishopGromovVolumeRatio` with
  `A = Ā = t^d`,

together with the explicit computation `euclidModel_volume : V t = t^(d+1)/(d+1)` of the
cumulative volume — the honest Euclidean ball-volume density (up to the `ω_{d}`-type
angular constant, which is recorded as a missing geometric constant and cancels in all
ratios).
-/
import Poincare.D12.ComparisonGeodesics.Definitions
import Poincare.D12.ComparisonGeodesics.SingularRiccati
import Poincare.D12.ComparisonGeodesics.VolumeRatio
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.D12.ComparisonGeodesics

/-! ## The Euclidean model -/

/-- The Euclidean model logarithmic derivative `t ↦ d/t` (the logarithmic derivative of
`t ↦ t^d`). -/
def euclidModelM (d : ℕ) (t : ℝ) : ℝ := (d : ℝ) / t

/-- The explicit derivative of `euclidModelM d`: `t ↦ −d/t²`. -/
def euclidModelDm (d : ℕ) (t : ℝ) : ℝ := -(d : ℝ) / t ^ 2

/-- The Euclidean radial area model `t ↦ t^d`. -/
def euclidModelA (d : ℕ) (t : ℝ) : ℝ := t ^ d

/-- `euclidModelM d` is differentiable away from `0`, with derivative `−d/t²`. -/
theorem euclidModelM_hasDerivAt {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    HasDerivAtR (euclidModelM d) (euclidModelDm d t) t := by
  have hdiv : HasDerivAtR (fun s : ℝ => (d : ℝ) / s) ((0 * t - (d : ℝ) * 1) / t ^ 2) t :=
    (hasDerivAtR_const (d : ℝ) t).div (hasDerivAtR_id t) ht
  convert hdiv using 1
  · ext s
    rfl
  · unfold euclidModelDm
    field_simp [ht]
    ring

/-- The Euclidean model satisfies the Riccati equality `m' + m²/d + 0 = 0` (for `d ≠ 0`),
away from `0`. -/
theorem euclidModelM_riccati {d : ℕ} {t : ℝ} (ht : t ≠ 0) (_hdne : (d : ℝ) ≠ 0) :
    euclidModelDm d t + euclidModelM d t ^ 2 / (d : ℝ) + 0 = 0 := by
  unfold euclidModelM euclidModelDm
  field_simp [ht]
  ring

/-- `euclidModelM d` is continuous on `(0,T]`. -/
theorem euclidModelM_contOn {d : ℕ} {T : ℝ} :
    ContinuousOn (euclidModelM d) (Ioc 0 T) := by
  unfold euclidModelM
  exact continuousOn_const.div continuousOn_id (by intro x hx; exact ne_of_gt hx.1)

/-- The Euclidean normalization holds with `C = 0` (exact equality `m t = d/t`). -/
theorem euclidModelM_normalized {d : ℕ} {C t₀ : ℝ} (hC : 0 ≤ C) :
    EuclideanNormalizedOn (euclidModelM d) (d : ℝ) C t₀ := by
  intro t _ht
  unfold euclidModelM
  simp
  exact hC

/-- `euclidModelA d` is differentiable with derivative `d · t^(d−1)`. -/
theorem euclidModelA_hasDerivAt {d : ℕ} (t : ℝ) :
    HasDerivAtR (euclidModelA d) ((d : ℝ) * t ^ (d - 1)) t := by
  unfold euclidModelA
  exact hasDerivAtR_pow d t

/-- `euclidModelA d` is positive on `(0,T]` (for any `d`; note `t > 0`). -/
theorem euclidModelA_pos {d : ℕ} {T : ℝ} : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < euclidModelA d t := by
  intro t ht
  unfold euclidModelA
  exact pow_pos ht.1 d

/-- `euclidModelA d 0 = 0` for `d ≥ 1`. -/
theorem euclidModelA_zero {d : ℕ} (hdpos : 0 < d) : euclidModelA d 0 = 0 := by
  unfold euclidModelA
  exact zero_pow (Nat.ne_of_gt hdpos)

/-- `euclidModelA d` is continuous on `[0,T]`. -/
theorem euclidModelA_contOn {d : ℕ} {T : ℝ} : ContinuousOn (euclidModelA d) (Icc 0 T) := by
  unfold euclidModelA
  exact (continuous_id.pow d).continuousOn

/-- The logarithmic derivative of `euclidModelA d` is `euclidModelM d`: for `t ≠ 0`,
`d·t^(d−1) / t^d = d/t`. -/
theorem euclidModelA_logDeriv {d : ℕ} {t : ℝ} (ht : t ≠ 0) (hdpos : 0 < d) :
    (d : ℝ) * t ^ (d - 1) / euclidModelA d t = euclidModelM d t := by
  unfold euclidModelA euclidModelM
  field_simp [ht]
  rw [← pow_succ (a := t) (n := d - 1)]
  rw [show (d - 1) + 1 = d by omega]

/-- **The Euclidean volume formula.**  `V t = ∫₀ᵗ s^d = t^(d+1)/(d+1)` — the cumulative
volume of the Euclidean model (the honest radial ball-volume density). -/
theorem euclidModel_volume {d : ℕ} (t : ℝ) :
    radialVolume (euclidModelA d) t = t ^ (d + 1) / (d + 1 : ℝ) := by
  unfold radialVolume euclidModelA
  have hderiv : ∀ x ∈ uIcc 0 t, HasDerivAt (fun s : ℝ => s ^ (d + 1) / ((d + 1 : ℕ) : ℝ)) (x ^ d) x := by
    intro x _hx
    have hpow : HasDerivAt (fun s : ℝ => s ^ (d + 1)) (((d + 1 : ℕ) : ℝ) * x ^ ((d + 1) - 1)) x :=
      hasDerivAt_pow (d + 1) x
    have hpow' : HasDerivAt (fun s : ℝ => s ^ (d + 1)) (((d + 1 : ℕ) : ℝ) * x ^ d) x := by
      convert hpow using 1
      rw [Nat.add_sub_cancel]
    have hdiv : HasDerivAt (fun s : ℝ => s ^ (d + 1) / ((d + 1 : ℕ) : ℝ))
        ((((d + 1 : ℕ) : ℝ) * x ^ d) / ((d + 1 : ℕ) : ℝ)) x :=
      hpow'.div_const (((d + 1 : ℕ) : ℝ))
    convert hdiv using 1
    · field_simp
  have hint : IntervalIntegrable (fun x : ℝ => x ^ d) volume 0 t := by
    exact ((continuous_id.pow d).continuousOn).intervalIntegrable
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hmain]
  simp [zero_pow (Nat.succ_ne_zero d), Nat.cast_add, Nat.cast_one]

/-! ## Non-vacuity witnesses -/

/-- **The singular Riccati comparison is non-vacuous (witness, upper direction).**  The
Euclidean model `m = m̄ = d/t`, `k = k̄ = 0`, `C = 0` satisfies *all* hypotheses of the
(v2) `riccati_le_of_singular_normalization`, and the conclusion `m ≤ m̄` holds (as
equality).  This proves the hypothesis set of the corrected theorem is consistent. -/
theorem euclidModel_singular_comparison {d : ℕ} {T t₀ : ℝ} (hdpos : 0 < d) (hT : 0 < T)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → euclidModelM d t ≤ euclidModelM d t := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd
  refine riccati_le_of_singular_normalization hd hT (show 0 ≤ (0 : ℝ) from le_rfl) ht₀ ht₀T
    (k := fun _ => 0) (kbar := fun _ => 0)
    (m := euclidModelM d) (dm := euclidModelDm d)
    (mbar := euclidModelM d) (dmbar := euclidModelDm d) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (euclidModelM_riccati (ne_of_gt ht.1) hdne).le
  · intro t ht
    exact euclidModelM_riccati (ne_of_gt ht.1) hdne
  · intro t _ht
    exact le_rfl
  · intro t ht
    exact euclidModelM_hasDerivAt (ne_of_gt ht.1)
  · intro t ht
    exact euclidModelM_hasDerivAt (ne_of_gt ht.1)
  · exact euclidModelM_contOn
  · exact euclidModelM_contOn
  · exact euclidModelM_normalized (show 0 ≤ (0 : ℝ) from le_rfl)
  · exact euclidModelM_normalized (show 0 ≤ (0 : ℝ) from le_rfl)

/-- **The singular Riccati comparison is non-vacuous (witness, lower direction).**  The
same Euclidean model satisfies all hypotheses of `riccati_ge_of_singular_normalization`
(with `k = k̄ = 0`, `C = 0`), and the conclusion `m̄ ≤ m` holds. -/
theorem euclidModel_singular_comparison_ge {d : ℕ} {T t₀ : ℝ} (hdpos : 0 < d) (hT : 0 < T)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → euclidModelM d t ≤ euclidModelM d t := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd
  refine riccati_ge_of_singular_normalization hd hT (show 0 ≤ (0 : ℝ) from le_rfl) ht₀ ht₀T
    (k := fun _ => 0) (kbar := fun _ => 0)
    (m := euclidModelM d) (dm := euclidModelDm d)
    (mbar := euclidModelM d) (dmbar := euclidModelDm d) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (euclidModelM_riccati (ne_of_gt ht.1) hdne).symm.le
  · intro t ht
    exact euclidModelM_riccati (ne_of_gt ht.1) hdne
  · intro t _ht
    exact le_rfl
  · intro t ht
    exact euclidModelM_hasDerivAt (ne_of_gt ht.1)
  · intro t ht
    exact euclidModelM_hasDerivAt (ne_of_gt ht.1)
  · exact euclidModelM_contOn
  · exact euclidModelM_contOn
  · exact euclidModelM_normalized (show 0 ≤ (0 : ℝ) from le_rfl)
  · exact euclidModelM_normalized (show 0 ≤ (0 : ℝ) from le_rfl)

/-- **The Bishop–Gromov chain is non-vacuous (witness).**  The Euclidean model
`A = Ā = t^d` (`d = n−1 ≥ 1`), with `m = m̄ = d/t`, `k = k̄ = 0`, `C = 0`, satisfies every
hypothesis of `bishopGromovVolumeRatio`; the conclusion is the (trivial) comparison of
the Euclidean volume with itself, and combined with `euclidModel_volume` it reads
`V R/V r = (R/r)^(d+1)`. -/
theorem euclidModel_bishopGromov {d : ℕ} {T t₀ : ℝ} (hdpos : 0 < d) (hT : 0 < T)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    ∀ ⦃r : ℝ⦄, r ∈ Ioc 0 T → ∀ ⦃R : ℝ⦄, R ∈ Ioc 0 T → r ≤ R →
      radialVolume (euclidModelA d) R / radialVolume (euclidModelA d) R
        ≤ radialVolume (euclidModelA d) r / radialVolume (euclidModelA d) r := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd
  refine bishopGromovVolumeRatio hd hT (show 0 ≤ (0 : ℝ) from le_rfl) ht₀ ht₀T
    (k := fun _ => 0) (kbar := fun _ => 0)
    (m := euclidModelM d) (dm := euclidModelDm d)
    (mbar := euclidModelM d) (dmbar := euclidModelDm d)
    (A := euclidModelA d) (dA := fun t => (d : ℝ) * t ^ (d - 1))
    (Abar := euclidModelA d) (dAbar := fun t => (d : ℝ) * t ^ (d - 1))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (euclidModelM_riccati (ne_of_gt ht.1) hdne).le
  · intro t ht
    exact euclidModelM_riccati (ne_of_gt ht.1) hdne
  · intro t _ht
    exact le_rfl
  · intro t ht
    exact euclidModelM_hasDerivAt (ne_of_gt ht.1)
  · intro t ht
    exact euclidModelM_hasDerivAt (ne_of_gt ht.1)
  · exact euclidModelM_contOn
  · exact euclidModelM_contOn
  · exact euclidModelM_normalized (show 0 ≤ (0 : ℝ) from le_rfl)
  · exact euclidModelM_normalized (show 0 ≤ (0 : ℝ) from le_rfl)
  · intro t ht
    exact euclidModelA_hasDerivAt t
  · intro t ht
    exact euclidModelA_hasDerivAt t
  · exact euclidModelA_contOn
  · exact euclidModelA_contOn
  · exact euclidModelA_pos
  · exact euclidModelA_pos
  · exact euclidModelA_zero hdpos
  · exact euclidModelA_zero hdpos
  · intro t ht
    exact (euclidModelA_logDeriv (ne_of_gt ht.1) hdpos).symm
  · intro t ht
    exact (euclidModelA_logDeriv (ne_of_gt ht.1) hdpos).symm

end Poincare.D12.ComparisonGeodesics
