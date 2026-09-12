/-
  scratch/review_circle_family_checks.lean  —  adversarial / independent checks of
  release/Poincare/L4/Compactness/MeasureGrowthChainCircleFamily.lean
  (the T ∈ [1,2] family module; NOT part of release/)

  Sections:
    FA. exact ball-volume formula for general circumference T
    FB. T-uniform constants: independence, validity across the range, tightness,
        and the genuine thresholds for the individual inequalities
    FC. non-vacuity / non-degeneracy for every T > 0
    FD. end-to-end definitional consumption
-/
import Poincare.L4.Compactness.MeasureGrowthChainCircleFamily

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff QuotientAddGroup
open Poincare.L4.Compactness

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ReviewCircleFamilyChecks

-- concrete Fact instances for the numeric T values used below
instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
instance : Fact (0 < ((3 : ℝ) / 2)) := ⟨by norm_num⟩
instance : Fact (0 < ((1 : ℝ) / 2)) := ⟨by norm_num⟩
instance : Fact (0 < ((3 : ℝ) / 4)) := ⟨by norm_num⟩
instance : Fact (0 < ((1 : ℝ) / 4)) := ⟨by norm_num⟩

/-- `ofReal (1/2) = 1/2` in `ℝ≥0∞`. -/
theorem fam_ofReal_half : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
  rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-! ## FA. The exact ball formula for general circumference -/

/-- **FA0.** The measure really is the transported Haar measure, for every T. -/
example (T : ℝ) [Fact (0 < T)] :
    circleMeasureT T = Measure.map (circleEquivT T).symm volume := rfl

/-- **FA1.** Concrete evaluations of the exact formula `ofReal (min T (2 s))`. -/
example : circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) ((1 : ℝ) / 2)) =
    ENNReal.ofReal 1 := by
  rw [circleMeasureT_closedBall]; norm_num

example : circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) 1) =
    ENNReal.ofReal 2 := by
  rw [circleMeasureT_closedBall]; norm_num

example : circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) ((3 : ℝ) / 2)) =
    ENNReal.ofReal 2 := by
  rw [circleMeasureT_closedBall]; norm_num

example : circleMeasureT ((3 : ℝ) / 2) (closedBall ((circleEquivT ((3 : ℝ) / 2)).symm 0)
    ((3 : ℝ) / 4)) = ENNReal.ofReal ((3 : ℝ) / 2) := by
  rw [circleMeasureT_closedBall]; norm_num

/-- Negative radius truncates to zero for every circumference. -/
example : circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) (-(1 : ℝ))) = 0 := by
  rw [circleMeasureT_closedBall,
    show min 2 (2 * (-(1 : ℝ))) = -(2 : ℝ) by norm_num]
  exact ENNReal.ofReal_of_nonpos (by norm_num)

/-- **FA2.** Total mass is exactly the circumference `T` (the transported Haar measure is
normalised to mass `T`, so `AddCircle T` really is the circumference-`T` circle). -/
example : circleMeasureT 2 (univ : Set (toGHSpace (AddCircle (2 : ℝ))).Rep) =
    ENNReal.ofReal 2 :=
  circleMeasureT_univ 2

/-- **FA3.** The member measure of the `T`-family equals the transported measure. -/
example (T : ℝ) [Fact (0 < T)] :
    circleMeasureTOf T (toGHSpace (AddCircle T)) = circleMeasureT T :=
  circleMeasureTOf_apply_member T

/-! ## FB. The constants: independence, validity, tightness -/

/-- **FB1.** The stored constants are literally the same numerals/functions for every T. -/
example : (circleGrowthT 1 (by norm_num) (by norm_num)).C = 2 := rfl
example : (circleGrowthT 2 (by norm_num) (by norm_num)).C = 2 := rfl
example : (circleGrowthT 2 (by norm_num) (by norm_num)).K = 4 := rfl
example : (circleGrowthT ((3 : ℝ) / 2) (by norm_num) (by norm_num)).K = 4 := rfl
example : (circleGrowthT 2 (by norm_num) (by norm_num)).R = 1 := rfl
example : (circleGrowthT 2 (by norm_num) (by norm_num)).m =
    fun s : ℝ => (min s (1 / 2)).toNNReal := rfl

/-- The two instances of `circleGrowthT` at different circumferences have identical constants. -/
example : (circleGrowthT 1 (by norm_num) (by norm_num)).C =
    (circleGrowthT 2 (by norm_num) (by norm_num)).C := rfl
example : (circleGrowthT 1 (by norm_num) (by norm_num)).K =
    (circleGrowthT 2 (by norm_num) (by norm_num)).K := rfl
example : (circleGrowthT 1 (by norm_num) (by norm_num)).R =
    (circleGrowthT 2 (by norm_num) (by norm_num)).R := rfl

/-- **FB2.** Doubling with `C = 2` is exactly tight for every T (at `s = T/2`); `C = 3/2`
already fails at `T = 2`, `s = 1`. -/
theorem fb2_C_two_not_improvable :
    ¬ (∀ s : ℝ, circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) s) ≤
        (3 / 2 : ℝ≥0∞) * circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) (s / 2))) := by
  intro h
  have h1 := h 1
  rw [circleMeasureT_closedBall, circleMeasureT_closedBall] at h1
  norm_num at h1
  have hfin : (3 / 2 : ℝ≥0∞) ≠ ∞ := by finiteness
  have h2 := ENNReal.toReal_mono hfin h1
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  norm_num at h2

/-- **FB3.** Comparability with `K = 4` is exactly tight at `T = 2`: `K = 3` already fails at
`s = 1`.  (Hence no smaller uniform `K` works on the whole range `[1,2]`.) -/
theorem fb3_K_four_not_improvable :
    ¬ (∀ s : ℝ, 0 < s →
        circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) s) ≤
          (3 : ℝ≥0∞) * ENNReal.ofReal (min s (1 / 2))) := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [circleMeasureT_closedBall] at h1
  norm_num at h1
  rw [fam_ofReal_half] at h1
  have hfin : ((3 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2 := ENNReal.toReal_mono hfin h1
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at h2
  norm_num at h2

/-- **FB4.** The lower bound `T ≥ 1` used by the module is *sufficient*; the true threshold for
the stated non-collapsing bound `m s = min s (1/2)` is exactly `T ≥ 1/2`, so the module's range is
valid but conservative on the lower end (this is an observation, not an error). -/
theorem fb4_noncollapse_true_threshold (T s : ℝ) (hT : 1 / 2 ≤ T) (hs : 0 < s) :
    min s (1 / 2) ≤ min T (2 * s) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_left h]
    exact le_min (by linarith) (by linarith)
  · rw [min_eq_right (le_of_lt h)]
    exact le_min hT (by linarith)

/-- The module's threshold `1 ≤ T` is not an artefact: `T = 1/4` genuinely violates the claimed
non-collapsing inequality with `m s = min s (1/2)`. -/
theorem fb4_lower_bound_needed :
    ¬ (∀ s : ℝ, 0 < s →
        ENNReal.ofReal (min s (1 / 2)) ≤
          ENNReal.ofReal (min ((1 : ℝ) / 4) (2 * s))) := by
  intro h
  have h1 := h (1 / 2) (by norm_num)
  rw [show min ((1 : ℝ) / 2) (1 / 2) = 1 / 2 by norm_num,
    show min ((1 : ℝ) / 4) (2 * ((1 : ℝ) / 2)) = 1 / 4 by norm_num] at h1
  rw [show ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) by
        rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num,
      show ENNReal.ofReal ((1 : ℝ) / 4) = (1 / 4 : ℝ≥0∞) by
        rw [show (1 : ℝ) / 4 = 4⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
        norm_num] at h1
  have h2 := ENNReal.toReal_mono (by finiteness) h1
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  norm_num at h2

/-- **FB5.** Comparability with `K = 4` actually holds for every `T ≤ 2` (no lower bound on `T`
is needed for *this* inequality); so the module's `1 ≤ T` is used in its proof but is not needed
for the truth of the compare field.  Again an observation, not an error. -/
theorem fb5_compare_true_threshold (T s : ℝ) (_hT : 0 < T) (hT2 : T ≤ 2) (hs : 0 < s) :
    min T (2 * s) ≤ 4 * min s (1 / 2) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_left h]
    have : min T (2 * s) ≤ 2 * s := min_le_right _ _
    linarith
  · rw [min_eq_right (le_of_lt h)]
    have : min T (2 * s) ≤ T := min_le_left _ _
    linarith

/-- **FB6.** Exhaustion `R = 1` needs exactly `T ≤ 2` (the coarse diameter bound is `T`, and
`2 R = 2`).  Check the boundary case `T = 2` explicitly. -/
example (x y : (toGHSpace (AddCircle (2 : ℝ))).Rep) : dist x y ≤ 2 * ((1 : ℝ≥0) : ℝ) := by
  have h := circleT_dist_le 2 x y
  norm_num at h ⊢
  exact h

/-- **FB7.** Grid check of the three uniform inequalities across the whole range `[1,2]`. -/
example : min (2 : ℝ) (2 * (1 / 4 : ℝ)) ≤ 2 * min 2 (1 / 4 : ℝ) := by norm_num
example : min ((3 : ℝ) / 2) (2 * (1 / 2 : ℝ)) ≤ 2 * min ((3 : ℝ) / 2) (1 / 2 : ℝ) := by norm_num
example : min (1 : ℝ) (2 * (1 / 2 : ℝ)) ≤ 2 * min 1 (1 / 2 : ℝ) := by norm_num
example : min (2 : ℝ) (2 * (3 : ℝ)) ≤ 2 * min 2 (3 : ℝ) := by norm_num
example : min (1 : ℝ) (2 * (-(1 : ℝ))) ≤ 2 * min 1 (-(1 : ℝ)) := by norm_num

example : min ((1 : ℝ) / 4) (1 / 2) ≤ min 2 (2 * ((1 : ℝ) / 4)) := by norm_num
example : min ((1 : ℝ) / 2) (1 / 2) ≤ min 1 (2 * ((1 : ℝ) / 2)) := by norm_num
example : min (1 : ℝ) (1 / 2) ≤ min ((3 : ℝ) / 2) (2 * 1) := by norm_num

example : min ((3 : ℝ) / 2) (2 * (1 : ℝ)) ≤ 4 * min 1 (1 / 2 : ℝ) := by norm_num
example : min (2 : ℝ) (2 * 1) ≤ 4 * min 1 (1 / 2 : ℝ) := by norm_num
example : min (2 : ℝ) (2 * (1 / 4 : ℝ)) ≤ 4 * min (1 / 4 : ℝ) (1 / 2) := by norm_num


/-- **FB8 (independent re-proof).** `min T (2 s) ≤ 2 * min T s` for every `T ≥ 0` (the doubling
field's real content), by splitting at `s = T`. -/
theorem fb8_doubling_general (T s : ℝ) (hT : 0 ≤ T) : min T (2 * s) ≤ 2 * min T s := by
  rcases le_total s T with h | h
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left h]
    calc min T (2 * s) ≤ T := min_le_left _ _
      _ ≤ 2 * T := by linarith

/-- **FB9 (inter-module consistency).** At `T = 1` the family module *is* the unit-circle module:
the chosen isometry and the transported measure are definitionally identical. -/
example : circleEquivT 1 = circleEquiv := rfl
example : circleMeasureT 1 = circleMeasure := rfl
example : (circleGrowthT 1 (by norm_num) (by norm_num)).C = circleGrowth.C := rfl
-- NB: the family module deliberately uses the looser uniform exhaustion radius R = 1
-- (the unit-circle module uses R = 1/2); both are valid for their respective claims.
example : (circleGrowthT 1 (by norm_num) (by norm_num)).R = 1 := rfl


/-- **FB2' (general tightness in `C`).** Every `C < 2` fails at `T = 2`, `s = 1`. -/
theorem fb2b_C_optimal (C : ℝ≥0) (hC : C < 2) :
    ¬ (∀ s : ℝ, circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) s) ≤
        (C : ℝ≥0∞) * circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) (s / 2))) := by
  intro h
  have h1 := h 1
  rw [circleMeasureT_closedBall, circleMeasureT_closedBall] at h1
  norm_num at h1
  have hfin : (C : ℝ≥0∞) ≠ ∞ := by finiteness
  have h2 : (2 : ℝ) ≤ (C : ℝ) := by
    have := ENNReal.toReal_mono hfin h1
    simpa [ENNReal.toReal_ofNat] using this
  exact (not_le.mpr hC) h2

/-- **FB3' (general tightness in `K`).** Every `K < 4` fails at `T = 2`, `s = 1`; hence `K = 4` is
the exact uniform comparability constant on the whole range. -/
theorem fb3b_K_optimal (K : ℝ≥0) (hK : K < 4) :
    ¬ (∀ s : ℝ, 0 < s →
        circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) s) ≤
          (K : ℝ≥0∞) * ENNReal.ofReal (min s (1 / 2))) := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [circleMeasureT_closedBall] at h1
  norm_num at h1
  rw [fam_ofReal_half] at h1
  have hfin : ((K : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2 : (2 : ℝ) ≤ (K : ℝ) * (1 / 2) := by
    have := ENNReal.toReal_mono hfin h1
    simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using this
  have : (4 : ℝ) ≤ K := by linarith
  exact (not_le.mpr hK) this

/-- **FB10.** The family's derived metric doubling constant is `32`, independent of `T`. -/
example : (circleGrowthT 2 (by norm_num) (by norm_num)).doublingConstant = 32 := by
  rw [UniformMeasureGrowth.doublingConstant]
  norm_num [circleGrowthT]

/-- **FB11.** The doubling ratio at `s = T/2` is exactly `2` for every circumference, so `C = 2`
cannot be improved for any `T` (not just `T = 2`). -/
theorem fb11_doubling_ratio_two (T : ℝ) (hT : 0 < T) :
    min T (2 * (T / 2)) = 2 * min T (T / 2) := by
  rw [show 2 * (T / 2) = T by ring, min_self, min_eq_right (by linarith)]
  ring

/-! ## FC. Non-vacuity / non-degeneracy for every circumference -/

/-- **FC1.** `AddCircle T` is infinite for every `T > 0`. -/
theorem fc1_infinite_circleT (T : ℝ) (hT : 0 < T) : Infinite (AddCircle T) := by
  haveI : Fact (0 < T) := ⟨hT⟩
  haveI : Infinite (Ico (0 : ℝ) (0 + T)) := Set.Ico.infinite (by linarith)
  refine Infinite.of_injective (fun x : Ico (0 : ℝ) (0 + T) => (x : AddCircle T)) ?_
  intro x y hxy
  exact Subtype.ext (AddCircle.coe_eq_coe_iff_of_mem_Ico x.2 y.2 |>.mp hxy)

/-- **FC2.** Hence the representative carrying `circleMeasureT T` is infinite. -/
theorem fc2_infinite_repT (T : ℝ) [Fact (0 < T)] :
    Infinite (toGHSpace (AddCircle T)).Rep := by
  haveI := fc1_infinite_circleT T Fact.out
  exact Infinite.of_injective (circleEquivT T).symm (circleEquivT T).symm.injective

/-- **FC3.** The transported measure is non-zero for every `T > 0` (mass `T`). -/
example : circleMeasureT 2 ≠ 0 := by
  intro h
  have h1 := circleMeasureT_univ 2
  rw [h] at h1
  simp at h1

/-- **FC4.** Radius dependence holds across the range: `μ (B 0 (T/4)) = T/2` and
`μ (B 0 (3T/4)) = T` for `T = 2`. -/
example : circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) ((2 : ℝ) / 4)) =
    ENNReal.ofReal ((2 : ℝ) / 2) :=
  (circleGrowthT_measure_varies (T := 2) (hT1 := by norm_num)).1

example : circleMeasureT 2 (closedBall ((circleEquivT 2).symm 0) (3 * (2 : ℝ) / 4)) =
    ENNReal.ofReal 2 :=
  (circleGrowthT_measure_varies (T := 2) (hT1 := by norm_num)).2

/-! ## FD. End-to-end definitional consumption -/

example (T : ℝ) [Fact (0 < T)] (h1 : 1 ≤ T) (h2 : T ≤ 2) :
    totallyBounded_circleT T h1 h2 =
      totallyBounded_of_uniformMeasureGrowth (circleGrowthT T h1 h2) := rfl

example (T : ℝ) [Fact (0 < T)] (h1 : 1 ≤ T) (h2 : T ≤ 2) :
    isCompact_circleT T h1 h2 =
      isCompact_of_uniformMeasureGrowth (circleGrowthT T h1 h2) isClosed_singleton := rfl

end ReviewCircleFamilyChecks
