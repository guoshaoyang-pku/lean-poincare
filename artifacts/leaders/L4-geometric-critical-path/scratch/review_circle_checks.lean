/-
  scratch/review_circle_checks.lean  —  adversarial / independent checks of
  release/Poincare/L4/Compactness/MeasureGrowthChainCircle.lean
  (NOT part of release/; compiled with an absolute path from the release dir)

  Sections:
    A. exact ball-volume formula: independent derivation route + concrete values
    B. constants C = 2, K = 2, m = min s (1/2), R = 1/2: validity and tightness
    C. non-vacuity / non-degeneracy: infiniteness, atomlessness, non-zero measure
    D. non-restatement / definitional shape of the construction
-/
import Poincare.L4.Compactness.MeasureGrowthChainCircle
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff QuotientAddGroup
open Poincare.L4.Compactness

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ReviewCircleChecks

/-! ## A. The exact ball-volume formula -/

/-- **A0 (definitional shape).** The transported measure really is
`Measure.map circleEquiv.symm volume` — i.e. the Haar measure of `AddCircle 1` pushed forward
along the canonical isometry, and nothing else. -/
example : circleMeasure = Measure.map circleEquiv.symm volume := rfl

/-- Helper: `ofReal (2 x) = 2 * ofReal x` (mathlib `ENNReal.ofReal_mul` with the nonnegative
factor `2`).  Used to turn `ENNReal`-valued grid checks into real inequalities. -/
theorem ofReal_two_mul (x : ℝ) : ENNReal.ofReal (2 * x) = 2 * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem ofReal_half : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
  rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem ofReal_quarter : ENNReal.ofReal ((1 : ℝ) / 4) = (1 / 4 : ℝ≥0∞) := by
  rw [show (1 : ℝ) / 4 = 4⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- **A1 (independent route, small scales).** For the centre `circleZero` and radius `1/4`, the
value `1/2` is re-derived *without* `AddCircle.volume_closedBall`, using instead the
fundamental-domain formula `AddCircle.add_projection_respects_measure` and
`Real.volume_Icc`. -/
theorem a1_quarter_ball_via_fundamentalDomain :
    circleMeasure (closedBall circleZero (1 / 4)) = ENNReal.ofReal (1 / 2) := by
  have hmap : circleMeasure (closedBall circleZero (1 / 4)) =
      (volume : Measure (AddCircle (1 : ℝ))) (closedBall (0 : AddCircle (1 : ℝ)) (1 / 4)) := by
    rw [circleMeasure,
      Measure.map_apply circleEquiv.symm.continuous.measurable measurableSet_closedBall,
      IsometryEquiv.preimage_closedBall]
    simp [circleZero]
  rw [hmap]
  have h := AddCircle.add_projection_respects_measure (T := 1) (-(1 / 2))
    (U := closedBall (0 : AddCircle (1 : ℝ)) (1 / 4)) measurableSet_closedBall
  rw [show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num] at h
  rw [h]
  have hsub : Ioc (-(1 / 2)) (1 / 2) ⊆ closedBall (0 : ℝ) (|(1 : ℝ)| / 2) := by
    intro y hy
    rw [Real.closedBall_eq_Icc]
    constructor <;> linarith [hy.1, hy.2]
  have hpre := AddCircle.coe_real_preimage_closedBall_inter_eq (p := 1) (x := 0) (ε := 1 / 4)
    (s := Ioc (-(1 / 2)) (1 / 2)) hsub
  change volume (QuotientAddGroup.mk ⁻¹' closedBall ((0 : ℝ) : AddCircle (1 : ℝ)) (1 / 4)
    ∩ Ioc (-(1 / 2)) (1 / 2)) = ENNReal.ofReal (1 / 2)
  rw [hpre]
  rw [ite_eq_left (by norm_num : (1 / 4 : ℝ) < |(1 : ℝ)| / 2)]
  have hset : closedBall (0 : ℝ) (1 / 4) ∩ Ioc (-(1 / 2)) (1 / 2) = Icc (-(1 / 4)) (1 / 4) := by
    ext y
    rw [mem_inter_iff, Real.closedBall_eq_Icc, zero_sub, zero_add]
    constructor
    · rintro ⟨⟨hy1, hy2⟩, _⟩
      exact ⟨hy1, hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨⟨hy1, hy2⟩, ⟨by linarith, by linarith⟩⟩
  rw [hset, Real.volume_Icc]
  norm_num

/-- **A2 (independent route, large scales).** For every centre, the ball of radius `1/2` is all of
`AddCircle 1` by the half-period lemma `AddCircle.closedBall_eq_univ_of_half_period_le` (again
without `AddCircle.volume_closedBall`), so its transported measure is `1`. -/
theorem a2_half_ball_via_univ (c : (toGHSpace (AddCircle (1 : ℝ))).Rep) :
    circleMeasure (closedBall c (1 / 2)) = 1 := by
  have hmap : circleMeasure (closedBall c (1 / 2)) =
      (volume : Measure (AddCircle (1 : ℝ))) (closedBall (circleEquiv c) (1 / 2)) := by
    rw [circleMeasure,
      Measure.map_apply circleEquiv.symm.continuous.measurable measurableSet_closedBall,
      IsometryEquiv.preimage_closedBall]
    rfl
  rw [hmap,
    AddCircle.closedBall_eq_univ_of_half_period_le (p := 1) (by norm_num) (circleEquiv c)
      (ε := 1 / 2) (by norm_num),
    AddCircle.measure_univ]
  norm_num

/-- **A3.** The module's exact formula evaluated at the requested scales. -/
example : circleMeasure (closedBall circleZero ((1 : ℝ) / 10)) = ENNReal.ofReal (1 / 5) := by
  rw [circleMeasure_closedBall]; norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 4)) = ENNReal.ofReal (1 / 2) := by
  rw [circleMeasure_closedBall]; norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 2)) = ENNReal.ofReal 1 := by
  rw [circleMeasure_closedBall]; norm_num

example : circleMeasure (closedBall circleZero ((3 : ℝ) / 4)) = ENNReal.ofReal 1 := by
  rw [circleMeasure_closedBall]; norm_num

example : circleMeasure (closedBall circleZero ((3 : ℝ) / 2)) = ENNReal.ofReal 1 := by
  rw [circleMeasure_closedBall]; norm_num

/-- Negative radius: `ENNReal.ofReal` truncates the negative value `2 s` to `0`. -/
example : circleMeasure (closedBall circleZero (-(1 : ℝ) / 3)) = 0 := by
  rw [circleMeasure_closedBall,
    show min 1 (2 * (-(1 : ℝ) / 3)) = -(2 / 3) by norm_num]
  exact ENNReal.ofReal_of_nonpos (by norm_num)

/-- The A1 independent route agrees with the module's formula. -/
example :
    circleMeasure (closedBall circleZero (1 / 4)) =
      ENNReal.ofReal (min 1 (2 * (1 / 4 : ℝ))) :=
  circleMeasure_closedBall circleZero (1 / 4)

/-! ## B. Validity and tightness of the claimed constants -/

/-- **B1.** The doubling inequality is exactly tight at `s = 1/2`: `C = 3/2` already fails, so
`C = 2` cannot be lowered. -/
theorem b1_C_two_not_improvable :
    ¬ (∀ c : (toGHSpace (AddCircle (1 : ℝ))).Rep, ∀ s : ℝ,
        circleMeasure (closedBall c s) ≤ (3 / 2 : ℝ≥0∞) *
          circleMeasure (closedBall c (s / 2))) := by
  intro h
  have h1 := h circleZero (1 / 2)
  rw [circleMeasure_closedBall, circleMeasure_closedBall] at h1
  norm_num at h1
  rw [ofReal_half] at h1
  have hfin : (3 / 2 * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2 := ENNReal.toReal_mono hfin h1
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  norm_num at h2

/-- **B2.** The reference-comparability inequality is exactly tight at `s = 1/4`: `K = 3/2`
already fails, so `K = 2` cannot be lowered. -/
theorem b2_K_two_not_improvable :
    ¬ (∀ c : (toGHSpace (AddCircle (1 : ℝ))).Rep, ∀ s : ℝ, 0 < s →
        circleMeasure (closedBall c s) ≤ (3 / 2 : ℝ≥0∞) * ENNReal.ofReal (min s (1 / 2))) := by
  intro h
  have h1 := h circleZero (1 / 4) (by norm_num)
  rw [circleMeasure_closedBall] at h1
  norm_num at h1
  rw [ofReal_half, ofReal_quarter] at h1
  have hfin : (3 / 2 * (1 / 4 : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2 := ENNReal.toReal_mono hfin h1
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  norm_num at h2

/-- **B3.** The non-collapsing bound `m s = min s (1/2)` is *not* over-claimed: replacing it by the
true ball measure `min 1 (2 s)` would already fail at `s = 1/4` (`1/2 ≤ 1/4` is false).  So `m` is
a genuine (and deliberately conservative) lower bound. -/
theorem b3_m_not_overclaimed :
    ¬ (∀ s : ℝ, 0 < s →
        ENNReal.ofReal (min 1 (2 * s)) ≤ ENNReal.ofReal (min s (1 / 2))) := by
  intro h
  have h1 := h (1 / 4) (by norm_num)
  norm_num at h1

/-- **B4.** Grid check of the doubling inequality at both signs and around the transition
scale `1/2`, directly on the transported measure at `circleZero`. -/
example : circleMeasure (closedBall circleZero (-3)) ≤
    2 * circleMeasure (closedBall circleZero ((-3) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 1000)) ≤
    2 * circleMeasure (closedBall circleZero (((1 : ℝ) / 1000) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 10)) ≤
    2 * circleMeasure (closedBall circleZero (((1 : ℝ) / 10) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 4)) ≤
    2 * circleMeasure (closedBall circleZero (((1 : ℝ) / 4) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((499 : ℝ) / 1000)) ≤
    2 * circleMeasure (closedBall circleZero (((499 : ℝ) / 1000) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 2)) ≤
    2 * circleMeasure (closedBall circleZero (((1 : ℝ) / 2) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((501 : ℝ) / 1000)) ≤
    2 * circleMeasure (closedBall circleZero (((501 : ℝ) / 1000) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((3 : ℝ) / 4)) ≤
    2 * circleMeasure (closedBall circleZero (((3 : ℝ) / 4) / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero (2)) ≤
    2 * circleMeasure (closedBall circleZero (2 / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero (100)) ≤
    2 * circleMeasure (closedBall circleZero (100 / 2)) := by
  rw [circleMeasure_closedBall, circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

/-- **B5.** Grid check of the non-collapsing and comparability inequalities at the same scales. -/
example : ENNReal.ofReal (min ((1 : ℝ) / 1000) (1 / 2)) ≤
    circleMeasure (closedBall circleZero ((1 : ℝ) / 1000)) := by
  rw [circleMeasure_closedBall]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : ENNReal.ofReal (min ((1 : ℝ) / 4) (1 / 2)) ≤
    circleMeasure (closedBall circleZero ((1 : ℝ) / 4)) := by
  rw [circleMeasure_closedBall]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : ENNReal.ofReal (min ((1 : ℝ) / 2) (1 / 2)) ≤
    circleMeasure (closedBall circleZero ((1 : ℝ) / 2)) := by
  rw [circleMeasure_closedBall]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : ENNReal.ofReal (min ((3 : ℝ) / 4) (1 / 2)) ≤
    circleMeasure (closedBall circleZero ((3 : ℝ) / 4)) := by
  rw [circleMeasure_closedBall]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : ENNReal.ofReal (min (100 : ℝ) (1 / 2)) ≤
    circleMeasure (closedBall circleZero 100) := by
  rw [circleMeasure_closedBall]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 4)) ≤
    2 * ENNReal.ofReal (min ((1 : ℝ) / 4) (1 / 2)) := by
  rw [circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((1 : ℝ) / 2)) ≤
    2 * ENNReal.ofReal (min ((1 : ℝ) / 2) (1 / 2)) := by
  rw [circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero ((3 : ℝ) / 4)) ≤
    2 * ENNReal.ofReal (min ((3 : ℝ) / 4) (1 / 2)) := by
  rw [circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

example : circleMeasure (closedBall circleZero 100) ≤
    2 * ENNReal.ofReal (min (100 : ℝ) (1 / 2)) := by
  rw [circleMeasure_closedBall, ← ofReal_two_mul]
  apply ENNReal.ofReal_le_ofReal
  norm_num

/-- **B6.** The claimed constants are the ones actually stored in the structure. -/
example : circleGrowth.C = 2 := rfl
example : circleGrowth.K = 2 := rfl
example : circleGrowth.R = 1 / 2 := rfl
example : circleGrowth.m = fun s : ℝ => (min s (1 / 2)).toNNReal := rfl
example : circleGrowth.μ (toGHSpace (AddCircle (1 : ℝ))) = circleMeasure :=
  circleMeasureOf_apply_member

/-- **B7.** The circle has diameter at most `1/2`, so the exhaustion radius `2 R = 1` used by the
module is valid but a factor `2` larger than needed (`R = 1/4` would already exhaust the family;
this is *not* an error, only non-tightness). -/
theorem b7_circle_dist_le_half (x y : (toGHSpace (AddCircle (1 : ℝ))).Rep) :
    dist x y ≤ 1 / 2 := by
  rw [← circleEquiv.dist_eq x y, dist_eq_norm]
  have h := AddCircle.norm_le_half_period (p := (1 : ℝ)) (by norm_num)
    (x := circleEquiv x - circleEquiv y)
  rwa [abs_one] at h

/-- The smaller radius `2 * (1/4) = 1/2` already exhausts the canonical representative. -/
theorem b7_exhaust_with_quarter_radius (p : GHSpace)
    (hp : p = toGHSpace (AddCircle (1 : ℝ))) :
    ∃ y : GHSpace.Rep p, (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * ((1 / 4 : ℝ≥0) : ℝ)) := by
  subst hp
  refine ⟨circleZero, fun x _ => ?_⟩
  rw [mem_closedBall]
  have h : (2 : ℝ) * ((1 / 4 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [h]
  exact b7_circle_dist_le_half x circleZero


/-- **B8 (independent re-proof, different case split).** The three real inequalities underlying the
structure fields, proved here by splitting at `s = 1` instead of `s = 1/2` and reducing to
`min_le_left` / `min_le_right`; this confirms the module's case analysis is exhaustive and correct
without reusing its proof scripts. -/
theorem b8_doubling_general (s : ℝ) : min 1 (2 * s) ≤ 2 * min 1 s := by
  rcases le_total s 1 with h | h
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left h]
    calc min 1 (2 * s) ≤ 1 := min_le_left _ _
      _ ≤ 2 * 1 := by norm_num

theorem b9_noncollapse_general (s : ℝ) (hs : 0 < s) : min s (1 / 2) ≤ min 1 (2 * s) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_left h]
    exact le_min (by linarith) (by linarith)
  · rw [min_eq_right (le_of_lt h)]
    exact le_min (by norm_num) (by linarith)

theorem b10_compare_general (s : ℝ) : min 1 (2 * s) ≤ 2 * min s (1 / 2) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_left h]
    exact le_trans (min_le_right _ _) (le_refl _)
  · rw [min_eq_right (le_of_lt h)]
    calc min 1 (2 * s) ≤ 1 := min_le_left _ _
      _ = 2 * (1 / 2) := by norm_num


/-- **B1' (general tightness).** Not merely `3/2`: *every* `C < 2` fails the doubling inequality,
at `s = 1/2` where the ratio is exactly `2`. -/
theorem b1b_C_optimal (C : ℝ≥0) (hC : C < 2) :
    ¬ (∀ c : (toGHSpace (AddCircle (1 : ℝ))).Rep, ∀ s : ℝ,
        circleMeasure (closedBall c s) ≤ (C : ℝ≥0∞) *
          circleMeasure (closedBall c (s / 2))) := by
  intro h
  have h1 := h circleZero (1 / 2)
  rw [circleMeasure_closedBall, circleMeasure_closedBall] at h1
  norm_num at h1
  rw [ofReal_half] at h1
  have hfin : ((C : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2 : (1 : ℝ) ≤ (C : ℝ) * (1 / 2) := by
    have := ENNReal.toReal_mono hfin h1
    simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using this
  have : (2 : ℝ) ≤ C := by linarith
  exact (not_le.mpr hC) this

/-- **B2' (general tightness).** *Every* `K < 2` fails the comparability inequality, at `s = 1/4`. -/
theorem b2b_K_optimal (K : ℝ≥0) (hK : K < 2) :
    ¬ (∀ c : (toGHSpace (AddCircle (1 : ℝ))).Rep, ∀ s : ℝ, 0 < s →
        circleMeasure (closedBall c s) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (min s (1 / 2))) := by
  intro h
  have h1 := h circleZero (1 / 4) (by norm_num)
  rw [circleMeasure_closedBall] at h1
  norm_num at h1
  rw [ofReal_half, ofReal_quarter] at h1
  have hfin : ((K : ℝ≥0∞) * (1 / 4 : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2 : (1 / 2 : ℝ) ≤ (K : ℝ) * (1 / 4) := by
    have := ENNReal.toReal_mono hfin h1
    simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using this
  have : (2 : ℝ) ≤ K := by linarith
  exact (not_le.mpr hK) this

/-- **B11.** The metric doubling constant derived by the leader chain for the unit-circle witness. -/
example : circleGrowth.doublingConstant = 16 := by
  rw [UniformMeasureGrowth.doublingConstant]
  norm_num [circleGrowth]

/-! ## C. Non-vacuity / non-degeneracy -/

/-- **C1.** The circle is infinite (via the half-open interval `[0,1)` and injectivity of the
projection on it). -/
theorem c1_infinite_circle : Infinite (AddCircle (1 : ℝ)) := by
  haveI : Infinite (Ico (0 : ℝ) (0 + 1)) := Set.Ico.infinite (by norm_num)
  refine Infinite.of_injective (fun x : Ico (0 : ℝ) (0 + 1) => (x : AddCircle (1 : ℝ))) ?_
  intro x y hxy
  exact Subtype.ext (AddCircle.coe_eq_coe_iff_of_mem_Ico x.2 y.2 |>.mp hxy)

/-- **C2.** Hence the canonical representative `(toGHSpace (AddCircle 1)).Rep` on which the measure
lives is infinite too: `circleGrowth` is a genuine continuum, not a finite/discrete collapse. -/
theorem c2_infinite_rep : Infinite (toGHSpace (AddCircle (1 : ℝ))).Rep := by
  haveI := c1_infinite_circle
  exact Infinite.of_injective circleEquiv.symm circleEquiv.symm.injective

/-- The representative is not a subsingleton (explicit two-point witness). -/
example : ¬ Subsingleton (toGHSpace (AddCircle (1 : ℝ))).Rep := by
  intro h
  have h01 : circleEquiv.symm (0 : AddCircle (1 : ℝ)) =
      circleEquiv.symm ((((1 : ℝ) / 2 : ℝ)) : AddCircle (1 : ℝ)) := Subsingleton.elim _ _
  have h0 : (0 : AddCircle (1 : ℝ)) = ((((1 : ℝ) / 2 : ℝ)) : AddCircle (1 : ℝ)) :=
    circleEquiv.symm.injective h01
  have hdist : dist (0 : AddCircle (1 : ℝ)) ((((1 : ℝ) / 2 : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
    rw [h0, dist_self]
  rw [dist_eq_norm] at hdist
  have hnorm : ‖(0 : AddCircle (1 : ℝ)) - ((((1 : ℝ) / 2 : ℝ)) : AddCircle (1 : ℝ))‖ = 1 / 2 := by
    rw [zero_sub, norm_neg]
    simpa using AddCircle.norm_half_period_eq (p := (1 : ℝ))
  rw [hnorm] at hdist
  norm_num at hdist

/-- **C3.** The transported measure is not the zero measure (`univ` has mass `1`). -/
example : circleMeasure ≠ 0 := by
  intro h
  have h1 := circleMeasure_univ
  rw [h] at h1
  simp at h1

/-- **C4.** The transported measure is not a Dirac mass either: the ball of radius `1/4` around
`circleZero` has measure `1/2`, while a Dirac at `circleZero` gives it mass `1`. -/
example : circleMeasure ≠ Measure.dirac circleZero := by
  intro h
  have h1 : circleMeasure (closedBall circleZero (1 / 4)) = ENNReal.ofReal (1 / 2) := by
    rw [circleMeasure_closedBall]; norm_num
  rw [h] at h1
  have hmem : circleZero ∈ closedBall circleZero (1 / 4) := by
    rw [mem_closedBall]; norm_num
  rw [Measure.dirac_apply_of_mem hmem] at h1
  have hne : ENNReal.ofReal ((1 : ℝ) / 2) ≠ 1 := by
    intro hh
    have h2 := congrArg ENNReal.toReal hh
    simp [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h2
  exact hne h1.symm

/-- **C5.** Every singleton is null for `volume` on `AddCircle 1` (the Haar measure has no atoms),
via mathlib's `AddCircle.closedBall_ae_eq_ball`; hence `circleMeasure` is atomless too.  Together
with C2 and C3 this rules out any finite/discrete collapse of the witness. -/
theorem c5_volume_singleton (x : AddCircle (1 : ℝ)) : volume ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
  have h := AddCircle.closedBall_ae_eq_ball (T := 1) (x := x) (ε := 0)
  rw [closedBall_zero', ball_zero, closure_singleton] at h
  have h2 : volume ({x} : Set (AddCircle (1 : ℝ))) = volume (∅ : Set (AddCircle (1 : ℝ))) :=
    measure_congr h
  simpa using h2

theorem c5_circleMeasure_singleton (x : (toGHSpace (AddCircle (1 : ℝ))).Rep) :
    circleMeasure ({x} : Set (toGHSpace (AddCircle (1 : ℝ))).Rep) = 0 := by
  rw [circleMeasure,
    Measure.map_apply circleEquiv.symm.continuous.measurable (measurableSet_singleton x)]
  have hset : circleEquiv.symm ⁻¹' ({x} : Set (toGHSpace (AddCircle (1 : ℝ))).Rep) =
      {circleEquiv x} := by
    ext a
    exact Equiv.symm_apply_eq circleEquiv.toEquiv
  rw [hset]
  exact c5_volume_singleton (circleEquiv x)

/-- **C6.** The measure is non-trivial at positive scales *and* vanishes at negative scales, and the
ball measure is genuinely radius-dependent (independently of the module's packaged theorem). -/
example : circleMeasure (closedBall circleZero (1 / 4)) ≠
    circleMeasure (closedBall circleZero (-(1 : ℝ))) := by
  have hneg : circleMeasure (closedBall circleZero (-(1 : ℝ))) = 0 := by
    rw [circleMeasure_closedBall,
      show min 1 (2 * (-(1 : ℝ))) = -2 by norm_num]
    exact ENNReal.ofReal_of_nonpos (by norm_num)
  rw [hneg]
  intro h
  have h1 : circleMeasure (closedBall circleZero (1 / 4)) = ENNReal.ofReal (1 / 2) := by
    rw [circleMeasure_closedBall]; norm_num
  rw [h1] at h
  exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne' h

/-! ## D. Non-restatement / end-to-end consumption -/

/-- **D1.** `totallyBounded_circle` is *definitionally* the leader-chain theorem applied to
`circleGrowth` (no extra hypothesis, no restatement). -/
example : totallyBounded_circle = totallyBounded_of_uniformMeasureGrowth circleGrowth := rfl

/-- **D2.** Same for compactness. -/
example : isCompact_circle = isCompact_of_uniformMeasureGrowth circleGrowth isClosed_singleton :=
  rfl

/-- **D3.** Same for the pointed-subsequence theorem. -/
example : exists_pointed_subseq_circle =
    exists_pointed_subseq_of_uniformMeasureGrowth circleGrowth isClosed_singleton
      (fun _ => toGHSpace (AddCircle (1 : ℝ))) (fun _ => rfl) (fun _ => circleZero) := rfl

end ReviewCircleChecks
