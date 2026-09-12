/-
Reviewer scratch — independent reproduction for the adversarial review of
`Poincare/L4/Compactness/RicciGrowthChain.lean` (M1).  NOT part of the release tree.

Contents
  A. reviewer-authored re-proofs of the derived lemmas of `UniformRicciBallGrowth`
     (nothing from `UniformRicciBallGrowth.*` is used except the structure fields and
     D12's `radialVolume_pos_of_pos`; the child theorem
     `euclid_volume_doubling_of_ricci_nonneg` is consumed as intended);
  B. a proof that a one-point family CANNOT carry `UniformRicciBallGrowth`;
  C. a reviewer-authored inhabitant of `UniformRicciBallGrowth` on the empty family;
  D. a check that the companion module's claimed geometric witness really inhabits
     the structure.
-/
import Poincare.L4.Compactness.FlatTorusGrowth

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff

noncomputable section

namespace ReviewRicciGrowth

open Poincare.L4.Compactness
open Poincare.D12.ComparisonGeodesics

/-! ## A. Independent re-derivation of the structure's lemmas -/

/-- Reviewer re-proof: the profile is nonnegative everywhere (the two saturation fields). -/
theorem rev_A_nonneg {t : Set GHSpace} (G : UniformRicciBallGrowth t) (s : ℝ) : 0 ≤ G.A s := by
  by_cases h : s ≤ 0
  · rw [G.A_nonpos s h]
  · rw [not_le] at h
    by_cases h2 : s ≤ G.T
    · exact le_of_lt (G.hApos ⟨h, h2⟩)
    · rw [not_le] at h2
      rw [G.A_saturate s h2]

/-- Reviewer re-proof: the cumulative volume vanishes on nonpositive radii. -/
theorem rev_radialVolume_eq_zero_of_nonpos {t : Set GHSpace} (G : UniformRicciBallGrowth t)
    {s : ℝ} (hs : s ≤ 0) : radialVolume G.A s = 0 := by
  rw [radialVolume, intervalIntegral.integral_of_ge hs]
  have hzero : (∫ x in Ioc s 0, G.A x) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => G.A_nonpos x hx.2)
  rw [hzero, neg_zero]

/-- Reviewer re-proof: the cumulative volume is nonnegative everywhere. -/
theorem rev_radialVolume_nonneg {t : Set GHSpace} (G : UniformRicciBallGrowth t) (s : ℝ) :
    0 ≤ radialVolume G.A s := by
  rcases le_or_gt 0 s with h | h
  · exact intervalIntegral.integral_nonneg h (fun u _ => rev_A_nonneg G u)
  · rw [rev_radialVolume_eq_zero_of_nonpos G h.le]

/-- Reviewer re-proof: the cumulative volume is monotone. -/
theorem rev_radialVolume_mono {t : Set GHSpace} (G : UniformRicciBallGrowth t) :
    Monotone (radialVolume G.A) := by
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · rw [rev_radialVolume_eq_zero_of_nonpos G (le_trans hab hb),
      rev_radialVolume_eq_zero_of_nonpos G hb]
  rcases le_or_gt 0 a with ha | ha
  · have hsplit : (∫ x in (0)..a, G.A x) + (∫ x in a..b, G.A x) = ∫ x in (0)..b, G.A x :=
      intervalIntegral.integral_add_adjacent_intervals (G.hAint 0 a) (G.hAint a b)
    have hnonneg : 0 ≤ ∫ x in a..b, G.A x :=
      intervalIntegral.integral_nonneg hab (fun u _ => rev_A_nonneg G u)
    simp only [radialVolume]
    linarith
  · rw [rev_radialVolume_eq_zero_of_nonpos G ha.le]
    exact rev_radialVolume_nonneg G b

/-- Reviewer re-proof: saturation of the cumulative volume beyond the horizon. -/
theorem rev_radialVolume_eq_of_ge {t : Set GHSpace} (G : UniformRicciBallGrowth t) {s : ℝ}
    (hs : G.T ≤ s) : radialVolume G.A s = radialVolume G.A G.T := by
  have hsplit : (∫ x in (0)..G.T, G.A x) + (∫ x in G.T..s, G.A x) = ∫ x in (0)..s, G.A x :=
    intervalIntegral.integral_add_adjacent_intervals (G.hAint 0 G.T) (G.hAint G.T s)
  have hzero : (∫ x in G.T..s, G.A x) = 0 := by
    rw [intervalIntegral.integral_of_le hs]
    exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => G.A_saturate x hx.1)
  simp only [radialVolume]
  rw [← hsplit, hzero, add_zero]

/-- Reviewer re-proof: strict positivity of the cumulative volume at positive scales. -/
theorem rev_radialVolume_pos {t : Set GHSpace} (G : UniformRicciBallGrowth t) {s : ℝ}
    (hs : 0 < s) : 0 < radialVolume G.A s := by
  rcases le_or_gt s G.T with h | h
  · exact radialVolume_pos_of_pos G.hT G.hAcont G.hApos ⟨hs, h⟩
  · rw [rev_radialVolume_eq_of_ge G h.le]
    exact radialVolume_pos_of_pos G.hT G.hAcont G.hApos ⟨G.hT, le_rfl⟩

/-- Reviewer re-proof: the all-scales halving inequality, consuming the child theorem
`euclid_volume_doubling_of_ricci_nonneg` and nothing else. -/
theorem rev_radialVolume_halving {t : Set GHSpace} (G : UniformRicciBallGrowth t) (s : ℝ) :
    radialVolume G.A s ≤ (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (s / 2) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [rev_radialVolume_eq_zero_of_nonpos G hs,
      rev_radialVolume_eq_zero_of_nonpos G (by linarith : s / 2 ≤ 0), mul_zero]
  rcases le_or_gt s G.T with hsT | hsT
  · have h := euclid_volume_doubling_of_ricci_nonneg (d := G.d) G.hd G.hT G.hCn G.ht₀ G.ht₀T
      G.hk G.hineq G.hm G.hmcont G.hnorm G.hA G.hAcont G.hApos G.hA0 G.hmA
      (s := s / 2) (by linarith) (by linarith) (by linarith)
    rwa [show 2 * (s / 2) = s by ring] at h
  · have hTpos : 0 < G.T := G.hT
    have hT2 : 0 < G.T / 2 := by linarith
    have hT2T : 2 * (G.T / 2) ≤ G.T := by linarith
    have hbase : radialVolume G.A G.T ≤
        (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (G.T / 2) := by
      have h := euclid_volume_doubling_of_ricci_nonneg (d := G.d) G.hd G.hT G.hCn G.ht₀ G.ht₀T
        G.hk G.hineq G.hm G.hmcont G.hnorm G.hA G.hAcont G.hApos G.hA0 G.hmA
        (s := G.T / 2) hT2 (by linarith) hT2T
      rwa [show 2 * (G.T / 2) = G.T by ring] at h
    rcases le_or_gt G.T (s / 2) with hhalf | hhalf
    · rw [rev_radialVolume_eq_of_ge G hsT.le, rev_radialVolume_eq_of_ge G hhalf]
      exact le_mul_of_one_le_left (rev_radialVolume_nonneg G G.T)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    · calc radialVolume G.A s = radialVolume G.A G.T := rev_radialVolume_eq_of_ge G hsT.le
        _ ≤ (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (G.T / 2) := hbase
        _ ≤ (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (s / 2) :=
            mul_le_mul_of_nonneg_left (rev_radialVolume_mono G (by linarith : G.T / 2 ≤ s / 2))
              (by positivity)

/-- Reviewer-authored version of `toUniformMeasureGrowth`. -/
def rev_toUniformMeasureGrowth {t : Set GHSpace} (G : UniformRicciBallGrowth t) :
    UniformMeasureGrowth t where
  μ := G.μ
  C := (2 : ℝ≥0) ^ (G.d + 1)
  K := 1
  m s := (radialVolume G.A s).toNNReal
  m_pos s hs := by
    rw [Real.toNNReal_pos]
    exact rev_radialVolume_pos G hs
  doubling := by
    intro p hp c s
    have hcoe : (((2 : ℝ≥0) ^ (G.d + 1) : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((2 : ℝ) ^ (G.d + 1)) := by
      rw [ENNReal.coe_nnreal_eq, NNReal.coe_pow]
      norm_num
    rw [G.realize p hp c s, G.realize p hp c (s / 2), hcoe,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (G.d + 1))]
    exact ENNReal.ofReal_le_ofReal (rev_radialVolume_halving G s)
  noncollapse := by
    intro p hp c s hs
    have hcoe : (((radialVolume G.A s).toNNReal : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (radialVolume G.A s) := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (rev_radialVolume_nonneg G s)]
    rw [G.realize p hp c s, hcoe]
  compare := by
    intro p hp c s hs
    have hcoe : (((radialVolume G.A s).toNNReal : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (radialVolume G.A s) := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (rev_radialVolume_nonneg G s)]
    rw [G.realize p hp c s, hcoe, ENNReal.coe_one, one_mul]
  R := G.R
  exhaust := G.exhaust

/-- Reviewer-authored downstream consumption of the round-5 chain. -/
theorem rev_totallyBounded {t : Set GHSpace} (G : UniformRicciBallGrowth t) : TotallyBounded t :=
  totallyBounded_of_uniformMeasureGrowth (rev_toUniformMeasureGrowth G)

/-! ## B. A one-point family cannot carry the structure

The `realize` field forces the measure of `univ = closedBall c 0 = closedBall c T`
to be simultaneously `ofReal (V 0) = 0` and `ofReal (V T) > 0`. -/

theorem no_uniformRicciBallGrowth_punit :
    ¬ Nonempty (UniformRicciBallGrowth ({toGHSpace PUnit.{1}} : Set GHSpace)) := by
  rintro ⟨G⟩
  let c : (toGHSpace PUnit.{1}).Rep :=
    Classical.choice (inferInstance : Nonempty (toGHSpace PUnit.{1}).Rep)
  have hball0 : closedBall c (0 : ℝ) = (univ : Set (toGHSpace PUnit).Rep) := by
    apply eq_univ_of_forall
    intro y
    rw [mem_closedBall]
    have hy : y = c := Subsingleton.elim y c
    rw [hy, dist_self]
  have hballT : closedBall c G.T = (univ : Set (toGHSpace PUnit).Rep) := by
    apply eq_univ_of_forall
    intro y
    rw [mem_closedBall]
    have hy : y = c := Subsingleton.elim y c
    rw [hy, dist_self]
    exact G.hT.le
  have h0 := G.realize (toGHSpace PUnit.{1}) (by simp) c 0
  have hT := G.realize (toGHSpace PUnit.{1}) (by simp) c G.T
  rw [hball0] at h0
  rw [hballT] at hT
  rw [rev_radialVolume_eq_zero_of_nonpos G le_rfl, ENNReal.ofReal_zero] at h0
  rw [h0] at hT
  have hz : radialVolume G.A G.T ≤ 0 := ENNReal.ofReal_eq_zero.mp hT.symm
  exact (not_lt_of_ge hz) (rev_radialVolume_pos G G.hT)

/-! ## C. A reviewer-authored inhabitant on the empty family -/

/-- Reviewer's own profile: `t` on `(0,1]` and `0` elsewhere. -/
def profA (t : ℝ) : ℝ := (Ioc 0 1).indicator (fun t => t) t

theorem profA_of_mem {t : ℝ} (ht : t ∈ Ioc 0 1) : profA t = t :=
  Set.indicator_of_mem ht _

theorem profA_of_notMem {t : ℝ} (ht : t ∉ Ioc 0 1) : profA t = 0 :=
  Set.indicator_of_notMem ht _

theorem profA_of_nonpos {t : ℝ} (ht : t ≤ 0) : profA t = 0 :=
  profA_of_notMem fun h => absurd h.1 (not_lt.mpr ht)

theorem profA_of_gt_one {t : ℝ} (ht : 1 < t) : profA t = 0 :=
  profA_of_notMem fun h => absurd h.2 (not_le.mpr ht)

theorem profA_eq_of_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 1) : profA t = t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, profA_of_nonpos le_rfl]
  · exact profA_of_mem ⟨h, ht.2⟩

theorem profA_pos {t : ℝ} (ht : t ∈ Ioc 0 1) : 0 < profA t := by
  rw [profA_of_mem ht]
  exact ht.1

theorem profA_zero : profA 0 = 0 := profA_of_nonpos le_rfl

theorem profA_cont : ContinuousOn profA (Icc 0 1) :=
  continuous_id.continuousOn.congr (fun _x hx => profA_eq_of_mem_Icc hx)

theorem profA_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 1) : HasDerivAtR profA 1 t := by
  have hev : profA =ᶠ[𝓝 t] fun x : ℝ => x := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact profA_eq_of_mem_Icc ⟨hx.1.le, hx.2.le⟩
  exact (hasDerivAtR_id t).congr_of_eventuallyEq hev

theorem profA_abs_le_one (t : ℝ) : |profA t| ≤ 1 := by
  rcases le_or_gt t 0 with h | h
  · rw [profA_of_nonpos h, abs_zero]
    norm_num
  · rcases le_or_gt t 1 with h2 | h2
    · rw [profA_eq_of_mem_Icc ⟨h.le, h2⟩, abs_of_pos h]
      exact h2
    · rw [profA_of_gt_one h2, abs_zero]
      norm_num

theorem profA_intervalIntegrable (a b : ℝ) : IntervalIntegrable profA volume a b := by
  rw [intervalIntegrable_iff]
  have hfin : volume (uIoc a b) < ∞ :=
    lt_of_le_of_lt (measure_mono uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top
  refine IntegrableOn.of_bound (s := uIoc a b) (μ := volume) (f := profA) (E := ℝ)
    hfin ?_ 1 ?_
  · exact (measurable_id.indicator measurableSet_Ioc).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun _x _ => by
      simpa [Real.norm_eq_abs] using profA_abs_le_one _x

/-- **Reviewer-authored inhabitant of `UniformRicciBallGrowth`** on the empty family.
The scalar Riccati data is the normalized profile `A t = t` on `(0,1]` with `m = 1/t`,
`d = 1`, `k = 0`; `realize` and `exhaust` are vacuous.  This certifies joint consistency
of every field except the non-vacuous content of `realize`/`exhaust`, which is tested
separately by the one-point impossibility theorem and by the companion torus witness. -/
def reviewEmptyWitness : UniformRicciBallGrowth (∅ : Set GHSpace) where
  μ := fun _ => 0
  d := 1
  hd := by norm_num
  T := 1
  hT := by norm_num
  Cn := 0
  hCn := le_rfl
  t₀ := 1
  ht₀ := by norm_num
  ht₀T := le_rfl
  k := fun _ => 0
  m := fun t => t⁻¹
  dm := fun t => -(t ^ 2)⁻¹
  A := profA
  dA := fun _ => 1
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
    exact profA_hasDerivAt hs
  hAcont := profA_cont
  hApos := by
    intro s hs
    exact profA_pos hs
  hA0 := profA_zero
  hmA := by
    intro s hs
    rw [profA_of_mem ⟨hs.1, hs.2.le⟩, one_div]
  hAint := profA_intervalIntegrable
  realize := by
    intro p hp
    exact absurd hp (Set.notMem_empty p)
  A_nonpos := fun s hs => profA_of_nonpos hs
  A_saturate := fun s hs => profA_of_gt_one hs
  R := 0
  hRT := by norm_num
  exhaust := by
    intro p hp
    exact absurd hp (Set.notMem_empty p)

theorem reviewEmptyWitness_inhabited :
    Nonempty (UniformRicciBallGrowth (∅ : Set GHSpace)) :=
  ⟨reviewEmptyWitness⟩

/-! ## D. The companion module's geometric witness really inhabits the structure -/

example : UniformRicciBallGrowth ({toGHSpace FlatTorus} : Set GHSpace) := torusRicciBallGrowth

#print axioms torusRicciBallGrowth

-- Axiom cones of the reviewer-authored declarations.
#print axioms rev_A_nonneg
#print axioms rev_radialVolume_nonneg
#print axioms rev_radialVolume_mono
#print axioms rev_radialVolume_halving
#print axioms rev_toUniformMeasureGrowth
#print axioms rev_totallyBounded
#print axioms no_uniformRicciBallGrowth_punit
#print axioms profA_intervalIntegrable
#print axioms reviewEmptyWitness
#print axioms reviewEmptyWitness_inhabited

end ReviewRicciGrowth
