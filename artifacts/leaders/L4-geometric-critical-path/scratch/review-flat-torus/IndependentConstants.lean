/-
REVIEWER SCRATCH — adversarial independent verification of the *constants* of M2.
Not part of the release tree.  Does NOT import `Poincare.L4.Compactness.FlatTorusGrowth`
or `RicciGrowthChain`: it only uses the upstream D12 definitions (`radialVolume`,
`EuclideanNormalizedOn`) plus mathlib.

Checked here:
* the profile `pA t = 8t` on `(0,1/2]`, `0` elsewhere, and its cumulative volume;
* the exact halving inequality `V s ≤ 4 * V (s/2)`, its equality set `s ≤ 1/2`, and the
  *optimality* of the constant `4` (no `c < 4` works);
* the `UniformMeasureGrowth` constants `C = 4`, `K = 1` with `m s = (V s).toNNReal`;
* the Riccati data at sample points, including exact equality in `dm + m²/d + k ≤ 0`;
* that the saturation field *must* use the strict inequality `T < s` (a non-strict
  variant is inconsistent with `A > 0` on `(0,T]`);
* the diameter `1/2` of the max-product torus, attained, and `2R = 1/2` for `R = 1/4`.
-/
import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

open scoped Topology ENNReal NNReal
open Set Metric MeasureTheory
open Poincare.D12.ComparisonGeodesics

noncomputable section

namespace ReviewFlatTorus

abbrev T2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-! ## 1. The profile and its cumulative volume -/

/-- The radial profile `A t = 8 t` on `(0, 1/2]`, `0` elsewhere. -/
def pA (t : ℝ) : ℝ := (Ioc 0 (1 / 2)).indicator (fun t => 8 * t) t

theorem pA_of_mem {t : ℝ} (ht : t ∈ Ioc 0 (1 / 2)) : pA t = 8 * t :=
  Set.indicator_of_mem ht _

theorem pA_of_notMem {t : ℝ} (ht : t ∉ Ioc 0 (1 / 2)) : pA t = 0 :=
  Set.indicator_of_notMem ht _

theorem pA_of_nonpos {t : ℝ} (ht : t ≤ 0) : pA t = 0 :=
  pA_of_notMem fun h => absurd h.1 (not_lt.mpr ht)

theorem pA_of_gt_half {t : ℝ} (ht : 1 / 2 < t) : pA t = 0 :=
  pA_of_notMem fun h => absurd h.2 (not_le.mpr ht)

theorem pA_eq_of_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 (1 / 2)) : pA t = 8 * t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    rw [pA_of_nonpos le_rfl]
    norm_num
  · exact pA_of_mem ⟨h, ht.2⟩

theorem pA_nonneg (t : ℝ) : 0 ≤ pA t := by
  rcases le_or_gt t 0 with h | h
  · rw [pA_of_nonpos h]
  · rcases le_or_gt t (1 / 2) with h2 | h2
    · rw [pA_of_mem ⟨h, h2⟩]; linarith
    · rw [pA_of_gt_half h2]

theorem pA_abs_le_four (t : ℝ) : |pA t| ≤ 4 := by
  rw [abs_of_nonneg (pA_nonneg t)]
  rcases le_or_gt t 0 with h | h
  · rw [pA_of_nonpos h]; norm_num
  · rcases le_or_gt t (1 / 2) with h2 | h2
    · rw [pA_of_mem ⟨h, h2⟩]; linarith
    · rw [pA_of_gt_half h2]; norm_num

theorem pA_measurable : Measurable pA :=
  ((continuous_const.mul continuous_id).measurable).indicator measurableSet_Ioc

theorem pA_intervalIntegrable (a b : ℝ) : IntervalIntegrable pA volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (s := uIoc a b) (μ := volume) (f := pA) (E := ℝ)
    (lt_of_le_of_lt (measure_mono uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top)
    pA_measurable.aestronglyMeasurable 4 ?_
  rw [ae_restrict_iff' measurableSet_uIoc]
  exact Filter.Eventually.of_forall fun x _ => by
    simpa [Real.norm_eq_abs] using pA_abs_le_four x

/-- Cumulative volume below the injectivity radius. -/
theorem radialVolume_pA_of_le_half {s : ℝ} (h0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    radialVolume pA s = 4 * s ^ 2 := by
  rw [radialVolume]
  trans ∫ x in (0)..s, 8 * x
  · exact intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le h0] at hx
      exact pA_eq_of_mem_Icc ⟨hx.1, le_trans hx.2 hs⟩
  · rw [intervalIntegral.integral_const_mul, integral_id]
    ring

/-- Cumulative volume above the injectivity radius: saturation at total mass `1`. -/
theorem radialVolume_pA_of_ge_half {s : ℝ} (hs : 1 / 2 ≤ s) : radialVolume pA s = 1 := by
  rw [radialVolume,
    ← intervalIntegral.integral_add_adjacent_intervals (pA_intervalIntegrable 0 (1 / 2))
      (pA_intervalIntegrable (1 / 2) s)]
  have h1 : (∫ x in (0)..(1 / 2), pA x) = 1 := by
    trans ∫ x in (0)..(1 / 2), 8 * x
    · exact intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
        exact pA_eq_of_mem_Icc hx
    · rw [intervalIntegral.integral_const_mul, integral_id]
      norm_num
  have h2 : (∫ x in (1 / 2)..s, pA x) = 0 := by
    rw [intervalIntegral.integral_of_le hs, setIntegral_eq_zero_of_forall_eq_zero]
    intro x hx
    exact pA_of_notMem fun h => absurd h.2 (not_le.mpr hx.1)
  rw [h1, h2, add_zero]

theorem radialVolume_pA_of_nonpos {s : ℝ} (hs : s ≤ 0) : radialVolume pA s = 0 := by
  rw [radialVolume, intervalIntegral.integral_of_ge hs,
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => pA_of_nonpos hx.2), neg_zero]

/-- **Exact cumulative volume**: `V s = (min 1 (2s))²` for `s ≥ 0`. -/
theorem radialVolume_pA_eq {s : ℝ} (hs : 0 ≤ s) :
    radialVolume pA s = (min 1 (2 * s)) ^ 2 := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [radialVolume_pA_of_le_half hs h, min_eq_right (by linarith)]; ring
  · rw [radialVolume_pA_of_ge_half h.le, min_eq_left (by linarith)]; norm_num

theorem radialVolume_pA_nonneg (s : ℝ) : 0 ≤ radialVolume pA s := by
  rcases le_or_gt s 0 with h | h
  · rw [radialVolume_pA_of_nonpos h]
  · rw [radialVolume_pA_eq h.le]; positivity

/-! ## 2. The halving ratio, its equality set and the optimality of `C = 4` -/

/-- `min 1 (2s) ≤ 2 * min 1 s`; the key elementary inequality (true for every real `s`). -/
theorem min_one_two_mul_le (s : ℝ) : min 1 (2 * s) ≤ 2 * min 1 s := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_right (by linarith : 2 * s ≤ 1), min_eq_right (by linarith : s ≤ 1)]
  · rw [min_eq_left (by linarith : (1 : ℝ) ≤ 2 * s)]
    rcases le_or_gt s 1 with h1 | h1
    · rw [min_eq_right h1]; linarith
    · rw [min_eq_left h1.le]; norm_num

/-- **The halving inequality with `C = 4`**, for every real scale. -/
theorem pA_halving_ratio_le (s : ℝ) :
    radialVolume pA s ≤ 4 * radialVolume pA (s / 2) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [radialVolume_pA_of_nonpos hs, radialVolume_pA_of_nonpos (by linarith : s / 2 ≤ 0)]
    positivity
  · rw [radialVolume_pA_eq hs.le, radialVolume_pA_eq (by linarith : (0 : ℝ) ≤ s / 2),
      show 2 * (s / 2) = s by ring]
    have hle := min_one_two_mul_le s
    have hnn : 0 ≤ min 1 (2 * s) := le_min zero_le_one (by linarith)
    calc min 1 (2 * s) ^ 2 = min 1 (2 * s) * min 1 (2 * s) := by ring
      _ ≤ (2 * min 1 s) * (2 * min 1 s) := mul_self_le_mul_self hnn hle
      _ = 4 * min 1 s ^ 2 := by ring

/-- **Equality holds exactly for `s ≤ 1/2`** (for `s ≤ 0` both sides vanish, so the
inequality is also an equality there). -/
theorem pA_halving_ratio_eq_iff (s : ℝ) :
    radialVolume pA s = 4 * radialVolume pA (s / 2) ↔ s ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra hs
    rw [not_le] at hs
    have hlt : radialVolume pA s < 4 * radialVolume pA (s / 2) := by
      rcases le_or_gt s 1 with h1 | h1
      · rw [radialVolume_pA_of_ge_half hs.le,
          radialVolume_pA_of_le_half (by linarith) (by linarith)]
        nlinarith
      · rw [radialVolume_pA_of_ge_half hs.le,
          radialVolume_pA_of_ge_half (by linarith : (1 : ℝ) / 2 ≤ s / 2)]
        norm_num
    linarith
  · intro hs
    rcases le_or_gt s 0 with h0 | h0
    · rw [radialVolume_pA_of_nonpos h0, radialVolume_pA_of_nonpos (by linarith)]
      ring
    · rw [radialVolume_pA_of_le_half h0.le hs,
        radialVolume_pA_of_le_half (by linarith) (by linarith)]
      ring

/-- Strict form: beyond the horizon the halving inequality is strict. -/
theorem pA_halving_ratio_lt_iff (s : ℝ) :
    radialVolume pA s < 4 * radialVolume pA (s / 2) ↔ 1 / 2 < s := by
  constructor
  · intro h
    by_contra hs
    rw [not_lt] at hs
    exact absurd (pA_halving_ratio_eq_iff s |>.mpr hs) (ne_of_lt h)
  · intro hs
    have h := (pA_halving_ratio_eq_iff s).not.mpr (not_le.mpr hs)
    exact lt_of_le_of_ne (pA_halving_ratio_le s) h

/-- **`C = 4` is optimal**: no smaller halving constant works for this profile. -/
theorem four_is_least_halving_constant (c : ℝ) (hc : c < 4) :
    ∃ s : ℝ, c * radialVolume pA (s / 2) < radialVolume pA s := by
  refine ⟨1 / 2, ?_⟩
  rw [radialVolume_pA_of_ge_half le_rfl,
    radialVolume_pA_of_le_half (by norm_num) (by norm_num)]
  linarith

/-! ## 3. Riccati data at sample points -/

theorem sample_A_quarter : pA (1 / 4) = 2 := by
  rw [pA_of_mem (by norm_num)]; norm_num

theorem sample_A_half : pA (1 / 2) = 4 := by
  rw [pA_of_mem (by norm_num)]; norm_num

theorem sample_A_zero : pA 0 = 0 := pA_of_nonpos le_rfl

theorem sample_A_beyond : pA (3 / 5) = 0 := pA_of_gt_half (by norm_num)

/-- `m = A'/A` at `s = 1/4`, with `m s = s⁻¹` and `A' = 8`. -/
theorem sample_logDeriv : (1 / 4 : ℝ)⁻¹ = 8 / pA (1 / 4) := by
  rw [sample_A_quarter]; norm_num

/-- **The Riccati inequality is an equality at `s = 1/4`.** -/
theorem sample_riccati_equality :
    -(↑(1 / 4 : ℝ) ^ 2)⁻¹ + ((1 / 4 : ℝ)⁻¹) ^ 2 / (1 : ℝ) + 0 = 0 := by
  norm_num

/-- The same identity with the M2 naming: `dm s + m s ^ 2 / d + k s` at `s = 1/4`. -/
theorem sample_riccati_equality' :
    (fun s : ℝ => -(s ^ 2)⁻¹) (1 / 4) +
        (fun s : ℝ => s⁻¹) (1 / 4) ^ 2 / ((1 : ℕ) : ℝ) +
        (fun _ : ℝ => (0 : ℝ)) (1 / 4) = 0 := by
  norm_num

/-- `m` is Euclidean-normalized with the *exact* constants `d = 1`, `C = 0`, `t₀ = 1/2`. -/
theorem euclid_normalized_inv : EuclideanNormalizedOn (fun t : ℝ => t⁻¹) 1 0 (1 / 2) := by
  intro t _ht
  rw [one_div, sub_self, abs_zero]


/-! ## 3b. The same Riccati/log-derivative/continuity fields for *every* scale -/

/-- The Riccati inequality is an **equality for every nonzero scale** (not only at samples). -/
theorem riccati_equality_all (s : ℝ) (hs : s ≠ 0) :
    -(s ^ 2)⁻¹ + (s⁻¹) ^ 2 / (1 : ℝ) + 0 = 0 := by
  field_simp
  ring

/-- `m = A'/A` for the concrete data at every scale of the horizon. -/
theorem logDeriv_all {s : ℝ} (hs : s ∈ Ioo 0 (1 / 2)) : s⁻¹ = 8 / pA s := by
  rw [pA_of_mem ⟨hs.1, hs.2.le⟩]
  field_simp

theorem pA_pos {t : ℝ} (ht : t ∈ Ioc 0 (1 / 2)) : 0 < pA t := by
  rw [pA_of_mem ht]; linarith [ht.1]

theorem pA_cont : ContinuousOn pA (Icc 0 (1 / 2)) :=
  (continuous_const.mul continuous_id).continuousOn.congr
    (fun _x hx => pA_eq_of_mem_Icc hx)

theorem pA_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 (1 / 2)) : HasDerivAtR pA 8 t := by
  have hev : pA =ᶠ[𝓝 t] fun x : ℝ => 8 * x := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact pA_of_mem ⟨hx.1, hx.2.le⟩
  simpa using (hasDerivAtR_id t).const_mul 8 |>.congr_of_eventuallyEq hev

theorem m_cont : ContinuousOn (fun t : ℝ => t⁻¹) (Ioc 0 (1 / 2)) :=
  continuousOn_id.inv₀ (fun _ hx => ne_of_gt hx.1)

/-! ## 4. The saturation field *must* be strict -/

/-- A structure whose saturation field were `T ≤ s → A s = 0` would be inconsistent with
`hApos : 0 < A s` on `(0,T]`.  Hence the strict inequality `T < s` in M2's `A_saturate`
(and in `UniformRicciBallGrowth`) is necessary, and `A T = 4 ≠ 0` is the correct value. -/
theorem nonstrict_saturation_inconsistent {A : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ s : ℝ, s ∈ Ioc 0 T → 0 < A s) (hsat : ∀ s : ℝ, T ≤ s → A s = 0) : False := by
  have h := hpos T ⟨hT, le_rfl⟩
  rw [hsat T le_rfl] at h
  exact lt_irrefl 0 h

/-- The concrete profile indeed fails the non-strict saturation statement. -/
theorem pA_not_saturate_nonstrict : ¬ (∀ s : ℝ, 1 / 2 ≤ s → pA s = 0) := by
  intro h
  have h1 := h (1 / 2) le_rfl
  rw [sample_A_half] at h1
  norm_num at h1

/-! ## 5. Diameter and exhaustion radius -/

theorem circle_dist_le_half (x y : AddCircle (1 : ℝ)) : dist x y ≤ 1 / 2 := by
  rw [dist_eq_norm]
  simpa using (AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x - y) one_ne_zero)

theorem circle_dist_half_eq :
    dist (0 : AddCircle (1 : ℝ)) (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) = 1 / 2 := by
  rw [dist_eq_norm, zero_sub]
  simpa using (AddCircle.norm_half_period_eq (p := (1 : ℝ)))

theorem torus_dist_le_half (x y : T2) : dist x y ≤ 1 / 2 := by
  rw [Prod.dist_eq]
  exact max_le (circle_dist_le_half _ _) (circle_dist_le_half _ _)

/-- The bound `1/2` is attained (non-degeneracy of the metric). -/
theorem torus_dist_half_attained :
    dist ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ((((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)), 0) = 1 / 2 := by
  rw [Prod.dist_eq, circle_dist_half_eq, dist_self]
  norm_num

/-- `R = 1/4` gives `2R = 1/2`, exactly the diameter: the exhaustion radius is sharp. -/
theorem two_R_eq_diameter : 2 * (1 / 4 : ℝ≥0) = 1 / 2 := by norm_num

/-! ## 6. The measure side: `realize` and the `UniformMeasureGrowth` constants -/

theorem ball_formula (x : T2) (s : ℝ) :
    volume (closedBall x s) = ENNReal.ofReal (min 1 (2 * s)) ^ 2 := by
  rw [show closedBall x s = closedBall x.1 s ×ˢ closedBall x.2 s from
      (closedBall_prod_same x.1 x.2 s).symm,
    Measure.volume_eq_prod, Measure.prod_prod, AddCircle.volume_closedBall,
    AddCircle.volume_closedBall, pow_two]

/-- **`realize`, independently**: the concrete measure of every closed ball is the
`ofReal` of the cumulative profile, for `s ≥ 0`. -/
theorem realize_link (x : T2) {s : ℝ} (hs : 0 ≤ s) :
    volume (closedBall x s) = ENNReal.ofReal (radialVolume pA s) := by
  rw [ball_formula, radialVolume_pA_eq hs, pow_two, pow_two,
    ENNReal.ofReal_mul (le_min zero_le_one (by linarith : (0 : ℝ) ≤ 2 * s))]

theorem ofReal_four : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : (0 : ℝ) ≤ 4)]
  rfl

/-- **The halving/doubling inequality at the measure level with the explicit constant 4.** -/
theorem doubling_ennreal (x : T2) (s : ℝ) :
    volume (closedBall x s) ≤ 4 * volume (closedBall x (s / 2)) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [ball_formula, ball_formula, show 2 * (s / 2) = s by ring,
      min_eq_right (by linarith : 2 * s ≤ 1), min_eq_right (by linarith : s ≤ 1),
      ENNReal.ofReal_eq_zero.mpr (by linarith : 2 * s ≤ 0), zero_pow (by norm_num)]
    positivity
  · rw [realize_link x hs.le, realize_link x (by linarith : (0 : ℝ) ≤ s / 2),
      ← ofReal_four, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (pA_halving_ratio_le s)

/-- **`K = 1` with `m s = (V s).toNNReal`**: the comparability field is an exact identity. -/
theorem compare_exact (x : T2) {s : ℝ} (hs : 0 < s) :
    volume (closedBall x s) = (1 : ℝ≥0∞) * ((radialVolume pA s).toNNReal : ℝ≥0∞) := by
  rw [realize_link x hs.le, one_mul, ENNReal.coe_nnreal_eq,
    Real.coe_toNNReal _ (radialVolume_pA_nonneg s)]

/-- **Non-collapsing**: the lower bound `m s` is met with equality. -/
theorem noncollapse_exact (x : T2) {s : ℝ} (hs : 0 < s) :
    ((radialVolume pA s).toNNReal : ℝ≥0∞) ≤ volume (closedBall x s) := by
  rw [compare_exact x hs, one_mul]

theorem m_pos {s : ℝ} (hs : 0 < s) : 0 < (radialVolume pA s).toNNReal := by
  rw [Real.toNNReal_pos]
  rcases le_or_gt s (1 / 2) with h | h
  · rw [radialVolume_pA_of_le_half hs.le h]; positivity
  · rw [radialVolume_pA_of_ge_half h.le]; norm_num

end ReviewFlatTorus
