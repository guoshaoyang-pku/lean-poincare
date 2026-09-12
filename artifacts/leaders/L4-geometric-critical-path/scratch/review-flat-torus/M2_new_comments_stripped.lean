
import Poincare.L4.Compactness.RicciGrowthChain



import Poincare.L4.Compactness.MeasureGrowthChainCircle
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Analysis.Normed.Group.Quotient

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff QuotientAddGroup

noncomputable section

namespace Poincare.L4.Compactness

open Poincare.D12.ComparisonGeodesics




abbrev FlatTorus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)


def torusEquiv : (toGHSpace FlatTorus).Rep ≃ᵢ FlatTorus :=
  Classical.choice (Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv FlatTorus)


def torusZero : (toGHSpace FlatTorus).Rep := torusEquiv.symm (0, 0)


def torusMeasure : Measure (toGHSpace FlatTorus).Rep :=
  Measure.map torusEquiv.symm volume


def torusMeasureOf (p : GHSpace) : Measure (GHSpace.Rep p) := by
  classical
  exact if h : p = toGHSpace FlatTorus then h ▸ torusMeasure else 0

theorem torusMeasureOf_apply_member :
    torusMeasureOf (toGHSpace FlatTorus) = torusMeasure := by
  rw [torusMeasureOf, dite_eq_left rfl]


theorem torusMeasure_closedBall (c : (toGHSpace FlatTorus).Rep) (s : ℝ) :
    torusMeasure (closedBall c s) = ENNReal.ofReal (min 1 (2 * s)) ^ 2 := by
  rw [torusMeasure, Measure.map_apply torusEquiv.symm.continuous.measurable measurableSet_closedBall,
    IsometryEquiv.preimage_closedBall, IsometryEquiv.symm_symm]
  obtain ⟨a, b⟩ := torusEquiv c
  rw [← closedBall_prod_same a b s, Measure.volume_eq_prod, Measure.prod_prod,
    AddCircle.volume_closedBall, AddCircle.volume_closedBall, pow_two]


theorem torusMeasure_univ : torusMeasure (univ : Set (toGHSpace FlatTorus).Rep) = 1 := by
  rw [torusMeasure, Measure.map_apply torusEquiv.symm.continuous.measurable MeasurableSet.univ,
    preimage_univ, ← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod,
    AddCircle.measure_univ]
  norm_num




def torusA (t : ℝ) : ℝ := (Ioc 0 (1 / 2)).indicator (fun t => 8 * t) t

theorem torusA_of_mem {t : ℝ} (ht : t ∈ Ioc 0 (1 / 2)) : torusA t = 8 * t :=
  Set.indicator_of_mem ht _

theorem torusA_of_notMem {t : ℝ} (ht : t ∉ Ioc 0 (1 / 2)) : torusA t = 0 :=
  Set.indicator_of_notMem ht _

theorem torusA_of_nonpos {t : ℝ} (ht : t ≤ 0) : torusA t = 0 :=
  torusA_of_notMem fun h => absurd h.1 (not_lt.mpr ht)

theorem torusA_of_gt {t : ℝ} (ht : 1 / 2 < t) : torusA t = 0 :=
  torusA_of_notMem fun h => absurd h.2 (not_le.mpr ht)


theorem torusA_half : torusA (1 / 2) = 4 := by
  rw [torusA_of_mem (right_mem_Ioc.mpr (by norm_num : (0 : ℝ) < 1 / 2))]
  norm_num


theorem torusA_eq_of_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 (1 / 2)) : torusA t = 8 * t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    rw [torusA_of_nonpos le_rfl]
    norm_num
  · exact torusA_of_mem ⟨h, ht.2⟩

theorem torusA_pos {t : ℝ} (ht : t ∈ Ioc 0 (1 / 2)) : 0 < torusA t := by
  rw [torusA_of_mem ht]
  linarith [ht.1]

theorem torusA_nonneg (t : ℝ) : 0 ≤ torusA t := by
  rcases le_or_gt t 0 with h | h
  · rw [torusA_of_nonpos h]
  · rcases le_or_gt t (1 / 2) with h2 | h2
    · exact (torusA_pos ⟨h, h2⟩).le
    · rw [torusA_of_gt h2]

theorem torusA_abs_le_four (t : ℝ) : |torusA t| ≤ 4 := by
  rw [abs_of_nonneg (torusA_nonneg t)]
  rcases le_or_gt t 0 with h | h
  · rw [torusA_of_nonpos h]
    norm_num
  · rcases le_or_gt t (1 / 2) with h2 | h2
    · rw [torusA_of_mem ⟨h, h2⟩]
      linarith
    · rw [torusA_of_gt h2]
      norm_num

theorem torusA_cont : ContinuousOn torusA (Icc 0 (1 / 2)) :=
  (continuous_const.mul continuous_id).continuousOn.congr
    (fun _x hx => torusA_eq_of_mem_Icc hx)


theorem torusA_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 (1 / 2)) : HasDerivAtR torusA 8 t := by
  have hev : torusA =ᶠ[𝓝 t] fun x : ℝ => 8 * x := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact torusA_of_mem ⟨hx.1, hx.2.le⟩
  have h8 : HasDerivAtR (fun x : ℝ => 8 * x) 8 t := by
    simpa using (hasDerivAtR_id t).const_mul 8
  exact h8.congr_of_eventuallyEq hev

theorem torusA_zero : torusA 0 = 0 := torusA_of_nonpos le_rfl


theorem torusA_measurable : Measurable torusA :=
  ((continuous_const.mul continuous_id).measurable).indicator measurableSet_Ioc


theorem torusA_intervalIntegrable (a b : ℝ) : IntervalIntegrable torusA volume a b := by
  rw [intervalIntegrable_iff]
  have hfin : volume (uIoc a b) < ∞ :=
    lt_of_le_of_lt (measure_mono uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top
  refine IntegrableOn.of_bound (s := uIoc a b) (μ := volume) (f := torusA) (E := ℝ)
    hfin ?_ 4 ?_
  · exact torusA_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun _x _ => by
      simpa [Real.norm_eq_abs] using torusA_abs_le_four _x


theorem torusRadialVolume_of_le_half {s : ℝ} (h0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    radialVolume torusA s = 4 * s ^ 2 := by
  rw [radialVolume]
  trans ∫ x in (0)..s, 8 * x
  · exact intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le h0] at hx
      exact torusA_eq_of_mem_Icc ⟨hx.1, le_trans hx.2 hs⟩
  · rw [intervalIntegral.integral_const_mul, integral_id]
    ring


theorem torusRadialVolume_of_ge_half {s : ℝ} (hs : 1 / 2 ≤ s) : radialVolume torusA s = 1 := by
  rw [radialVolume]
  rw [← intervalIntegral.integral_add_adjacent_intervals (torusA_intervalIntegrable 0 (1 / 2))
    (torusA_intervalIntegrable (1 / 2) s)]
  have h1 : (∫ x in (0)..(1 / 2), torusA x) = 1 := by
    trans ∫ x in (0)..(1 / 2), 8 * x
    · exact intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
        exact torusA_eq_of_mem_Icc hx
    · rw [intervalIntegral.integral_const_mul, integral_id]
      norm_num
  have h2 : (∫ x in (1 / 2)..s, torusA x) = 0 := by
    rw [intervalIntegral.integral_of_le hs, setIntegral_eq_zero_of_forall_eq_zero]
    intro x hx
    exact torusA_of_gt hx.1
  rw [h1, h2, add_zero]

theorem torusRadialVolume_of_nonpos {s : ℝ} (hs : s ≤ 0) : radialVolume torusA s = 0 := by
  rw [radialVolume, intervalIntegral.integral_of_ge hs,
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => torusA_of_nonpos hx.2), neg_zero]


theorem torusRadialVolume_eq {s : ℝ} (hs : 0 ≤ s) :
    radialVolume torusA s = (min 1 (2 * s)) ^ 2 := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [torusRadialVolume_of_le_half hs h, min_eq_right (by linarith)]
    ring
  · rw [torusRadialVolume_of_ge_half h.le, min_eq_left (by linarith)]
    norm_num


theorem torusMeasure_closedBall_eq_ofReal (c : (toGHSpace FlatTorus).Rep) (s : ℝ) :
    torusMeasure (closedBall c s) = ENNReal.ofReal (radialVolume torusA s) := by
  rw [torusMeasure_closedBall]
  rcases le_or_gt 0 s with hs | hs
  · rw [torusRadialVolume_eq hs, pow_two, pow_two,
      ENNReal.ofReal_mul (le_min zero_le_one (by linarith))]
  · rw [torusRadialVolume_of_nonpos hs.le]
    have hmin : min 1 (2 * s) = 2 * s := min_eq_right (by linarith)
    rw [hmin, ENNReal.ofReal_eq_zero.mpr (by linarith : 2 * s ≤ 0),
      zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero]




theorem circle_norm_le_half (z : AddCircle (1 : ℝ)) : ‖z‖ ≤ 1 / 2 := by
  set r : ℝ := ((AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z :
    Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1 : ℝ)) : ℝ) with hrdef
  have hr : r ∈ Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1 : ℝ) :=
    (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).2
  have hz : (r : AddCircle (1 : ℝ)) = z := by
    rw [← AddCircle.coe_equivIco (p := (1 : ℝ)) (a := -(1 / 2)) (y := z)]
  calc ‖z‖ = ‖(r : AddCircle (1 : ℝ))‖ := by rw [hz]
    _ ≤ ‖r‖ := norm_mk_le_norm
    _ = |r| := Real.norm_eq_abs r
    _ ≤ 1 / 2 := by
        rw [abs_le]
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩


theorem circle_dist_le_half (x y : AddCircle (1 : ℝ)) : dist x y ≤ 1 / 2 := by
  rw [dist_eq_norm]
  exact circle_norm_le_half _


theorem torus_dist_le_half (x y : FlatTorus) : dist x y ≤ 1 / 2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  rw [Prod.dist_eq]
  exact max_le (circle_dist_le_half a a') (circle_dist_le_half b b')




def torusRicciBallGrowth :
    UniformRicciBallGrowth ({toGHSpace FlatTorus} : Set GHSpace) where
  μ := torusMeasureOf
  d := 1
  hd := by norm_num
  T := 1 / 2
  hT := by norm_num
  Cn := 0
  hCn := le_rfl
  t₀ := 1 / 2
  ht₀ := by norm_num
  ht₀T := le_rfl
  k := fun _ => 0
  m := fun t => t⁻¹
  dm := fun t => -(t ^ 2)⁻¹
  A := torusA
  dA := fun _ => 8
  hk := by intro s _; norm_num
  hineq := by
    intro s hs
    have h : (s⁻¹) ^ 2 = (s ^ 2)⁻¹ := inv_pow s 2
    rw [h]
    norm_num
  hm := by
    intro s hs
    exact hasDerivAtR_inv (ne_of_gt hs.1)
  hmcont := continuousOn_id.inv₀ (fun x hx => ne_of_gt hx.1)
  hnorm := by
    intro s hs
    have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1, one_div, sub_self, abs_zero]
  hA := by
    intro s hs
    exact torusA_hasDerivAt hs
  hAcont := torusA_cont
  hApos := by
    intro s hs
    exact torusA_pos hs
  hA0 := torusA_zero
  hmA := by
    intro s hs
    rw [torusA_of_mem ⟨hs.1, hs.2.le⟩]
    field_simp
  hAint := torusA_intervalIntegrable
  realize := by
    intro p hp c s
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rw [torusMeasureOf_apply_member]
    exact torusMeasure_closedBall_eq_ofReal c s
  A_nonpos := fun s hs => torusA_of_nonpos hs
  A_saturate := fun s hs => torusA_of_gt hs
  R := 1 / 4
  hRT := by norm_num
  exhaust := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨torusZero, fun x _ => ?_⟩
    rw [mem_closedBall]
    have h : (2 : ℝ) * ((1 / 4 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [h, ← torusEquiv.dist_eq]
    have hz : torusEquiv torusZero = (0, 0) := by
      simp [torusZero]
    rw [hz]
    exact torus_dist_le_half _ _




theorem torusGrowth_measure_varies :
    torusMeasure (closedBall torusZero (1 / 4)) = 1 / 4 ∧
      torusMeasure (closedBall torusZero (3 / 4)) = 1 := by
  constructor
  · rw [torusMeasure_closedBall, show min 1 (2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num, pow_two]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (1 / 2 : ℝ) * (1 / 2) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  · rw [torusMeasure_closedBall, show min 1 (2 * (3 / 4 : ℝ)) = 1 by norm_num]
    norm_num


theorem torus_nondegenerate :
    dist (torusEquiv.symm ((0 : AddCircle (1 : ℝ)), 0))
      (torusEquiv.symm ((((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)), 0)) = 1 / 2 := by
  rw [← torusEquiv.dist_eq, Prod.dist_eq]
  simp only [IsometryEquiv.apply_symm_apply]
  have h1 : dist (0 : AddCircle (1 : ℝ)) ((((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ))) = 1 / 2 := by
    rw [dist_eq_norm, norm_sub_rev, sub_zero]
    show ‖(((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ))‖ = 1 / 2
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).mpr
      (by norm_num : |(1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2)]
    norm_num
  rw [h1, dist_self, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]




theorem totallyBounded_torus : TotallyBounded ({toGHSpace FlatTorus} : Set GHSpace) :=
  totallyBounded_of_uniformRicciBallGrowth torusRicciBallGrowth


theorem isCompact_torus : IsCompact ({toGHSpace FlatTorus} : Set GHSpace) :=
  isCompact_of_uniformRicciBallGrowth torusRicciBallGrowth isClosed_singleton


theorem exists_pointed_subseq_torus :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ ({toGHSpace FlatTorus} : Set GHSpace) ∧ StrictMono φ ∧
        Nonempty (Poincare.L4.PointedGH.PointedGHCoupling
          (fun _ => (toGHSpace FlatTorus).Rep) (fun _ => torusZero) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformRicciBallGrowth torusRicciBallGrowth isClosed_singleton
    (fun _ => toGHSpace FlatTorus) (fun _ => rfl) (fun _ => torusZero)

end Poincare.L4.Compactness
