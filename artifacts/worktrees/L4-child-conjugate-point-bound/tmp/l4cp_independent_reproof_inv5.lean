/-
Invocation-5 **independent re-proof** of the endpoint conjugate-point bound.

This file imports only `ConstantCurvatureRauch.lean` (NOT `ConjugatePointEndpoint.lean`), and
re-derives `T ≤ π/√K` from `jacobi_le_constCurvModel` with an independently written proof:

* the restriction of a Jacobi solution is proved locally (`inv5_mono`) rather than using the
  artifact's `JacobiSolutionOn.mono`;
* the comparison interval is chosen as `T'' = (max t t₀ + x)/2` directly from `x = π/√K`
  (the artifact uses `min T (π/√K)`);
* the endpoint limit is formalized with a **sequence** `x − 2/(n+1) → x` and
  `le_of_tendsto_of_tendsto'` along `atTop`, rather than with the one-sided filter
  `𝓝[<] x`.

If this compiles, the endpoint passage is confirmed by a second, independent proof term.
-/
import Poincare.L4.GeodesicComparison.ConstantCurvatureRauch

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Local restriction lemma (independent of the artifact's version). -/
theorem inv5_mono {k u du ddu : ℝ → ℝ} {T T' : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hT' : T' ≤ T) :
    JacobiSolutionOn k u du ddu 0 T' where
  hasDerivAt_u := fun _ ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  hasDerivAt_du := fun _ ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  eq_secondDeriv := fun _ ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hT')
  continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hT')

/-- Local normalisation base-point bound (independent of the artifact's version): the model
threshold `(K·max (1/√K) T)·t₀ ≤ 1/2` forces `t₀ < π/√K`, because
`K·max (1/√K) T ≥ √K`. -/
theorem inv5_basePoint_lt_firstZero {T t₀ K : ℝ} (hK : 0 < K) (ht₀ : 0 < t₀)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    t₀ < Real.pi / Real.sqrt K := by
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hKnn : 0 ≤ K := le_of_lt hK
  have hsq : Real.sqrt K * Real.sqrt K = K := by
    simpa [sq] using Real.sq_sqrt hKnn
  have hle : Real.sqrt K ≤ K * max (1 / Real.sqrt K) T := by
    have h1 : Real.sqrt K = K * (1 / Real.sqrt K) := by
      rw [mul_one_div, eq_div_iff hsqrtK.ne']
      exact hsq
    calc Real.sqrt K = K * (1 / Real.sqrt K) := h1
      _ ≤ K * max (1 / Real.sqrt K) T :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hKnn
  have h2 : Real.sqrt K * t₀ ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hle ht₀.le) hBmodel
  have h3 : Real.sqrt K * t₀ < Real.pi := by nlinarith [h2, Real.pi_gt_three]
  rw [lt_div_iff₀ hsqrtK]
  linarith [h3]

/-- **Independent endpoint bound.**  Same statement as the acceptance theorem, proved from
`jacobi_le_constCurvModel` by the sequence-based limiting argument. -/
theorem inv5_independent_endpoint_bound {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T ≤ Real.pi / Real.sqrt K := by
  by_contra hcon
  rw [not_le] at hcon
  set x : ℝ := Real.pi / Real.sqrt K with hxdef
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hxpos : 0 < x := by rw [hxdef]; exact div_pos Real.pi_pos hsqrtK
  have hxT : x < T := hcon
  have ht₀x : t₀ < x := by
    rw [hxdef]; exact inv5_basePoint_lt_firstZero hK ht₀ hBmodel
  -- Pointwise comparison on `(0,x)`, with the interval `T'' = (max t t₀ + x)/2`.
  have hcompare : ∀ t ∈ Ioo 0 x, u t ≤ jacobiSol K t := by
    intro t ht
    have htT : t < T := lt_trans ht.2 hxT
    have hMx : max t t₀ < x := max_lt ht.2 ht₀x
    set T'' : ℝ := (max t t₀ + x) / 2 with hT''def
    have htT'' : t < T'' := by rw [hT''def]; linarith [le_max_left t t₀]
    have ht₀T'' : t₀ ≤ T'' := by rw [hT''def]; linarith [le_max_right t t₀]
    have hT''x : T'' < x := by rw [hT''def]; linarith
    have hT''T : T'' ≤ T := le_of_lt (lt_trans hT''x hxT)
    have hT''pos : 0 < T'' := lt_trans ht.1 htT''
    have hT''pi : Real.sqrt K * T'' < Real.pi := by
      have h1 := mul_lt_mul_of_pos_left hT''x hsqrtK
      rw [hxdef, mul_div_cancel₀ Real.pi hsqrtK.ne'] at h1
      exact h1
    have hBmodel'' : (K * max (1 / Real.sqrt K) T'') * t₀ ≤ 1 / 2 := by
      have hmax : max (1 / Real.sqrt K) T'' ≤ max (1 / Real.sqrt K) T :=
        max_le_max le_rfl hT''T
      have hKnn : 0 ≤ K := le_of_lt hK
      exact le_trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hKnn) ht₀.le) hBmodel
    exact (jacobi_le_constCurvModel (T := T'') (B := B) (t₀ := t₀) (K := K)
      hT''pos hBnn ht₀ ht₀T'' hBt₀ (inv5_mono h hT''T)
      (hdducont.mono (Icc_subset_Icc_right hT''T))
      (fun s hs => hB s ⟨hs.1, lt_of_lt_of_le hs.2 hT''T⟩) hu0 hdu0
      (fun s hs => hpos s ⟨hs.1, le_trans hs.2 hT''T⟩) hK.le
      (fun s hs => hk s ⟨hs.1, lt_of_lt_of_le hs.2 hT''T⟩) hBmodel''
      (Or.inr hT''pi)) t ⟨ht.1, htT''⟩
  -- The sequence `x - 2/(n+1)` tends to `x` from below.
  have hlim_sub : Tendsto (fun n : ℕ => x - 2 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop
          (𝓝 ((2 : ℝ) * 0)) := tendsto_const_nhds.mul h1
      simpa [div_eq_mul_inv] using h2
    simpa using tendsto_const_nhds.sub h3
  have hev_lt : ∀ᶠ n : ℕ in atTop, x - 2 / ((n : ℝ) + 1) < x :=
    Eventually.of_forall fun n => by
      have hpos : 0 < 2 / ((n : ℝ) + 1) := by positivity
      linarith
  have hev_pos : ∀ᶠ n : ℕ in atTop, 0 < x - 2 / ((n : ℝ) + 1) :=
    hlim_sub.eventually (Ioi_mem_nhds hxpos)
  have hev : ∀ᶠ n : ℕ in atTop, x - 2 / ((n : ℝ) + 1) ∈ Ioo 0 x :=
    hev_pos.and hev_lt
  have hev_le : ∀ᶠ n : ℕ in atTop,
      u (x - 2 / ((n : ℝ) + 1)) ≤ jacobiSol K (x - 2 / ((n : ℝ) + 1)) :=
    hev.mono fun n hn => hcompare _ hn
  have hxmem : x ∈ Icc (0 : ℝ) T := ⟨hxpos.le, hxT.le⟩
  have hmem_ev : ∀ᶠ n : ℕ in atTop, x - 2 / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) T :=
    hev.mono fun n hn => ⟨hn.1.le, le_of_lt (lt_trans hn.2 hxT)⟩
  have hf : Tendsto (fun n : ℕ => u (x - 2 / ((n : ℝ) + 1))) atTop (𝓝 (u x)) :=
    ((h.continuousOn_u x hxmem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim_sub, hmem_ev⟩))
  have hg : Tendsto (fun n : ℕ => jacobiSol K (x - 2 / ((n : ℝ) + 1))) atTop
      (𝓝 (jacobiSol K x)) :=
    ((continuous_jacobiSol K).tendsto x).comp hlim_sub
  have hfin : u x ≤ jacobiSol K x := le_of_tendsto_of_tendsto hf hg hev_le
  have hxzero : jacobiSol K x = 0 := by
    rw [hxdef, jacobiSol_of_pos hK, jacobiSolSphere_firstZero hK]
  rw [hxzero] at hfin
  exact absurd hfin (not_le.mpr (hpos x ⟨hxpos, hxT.le⟩))

/-- The acceptance sentence, restated inside this file. -/
def inv5_HeadlineType' : Prop :=
  ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
    0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
    JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
    (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
    (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2 → T ≤ Real.pi / Real.sqrt K

/-- The independently proved theorem has the acceptance type (defeq check). -/
example : inv5_HeadlineType' := inv5_independent_endpoint_bound

end Poincare.L4.GeodesicComparison

#print axioms Poincare.L4.GeodesicComparison.inv5_mono
#print axioms Poincare.L4.GeodesicComparison.inv5_basePoint_lt_firstZero
#print axioms Poincare.L4.GeodesicComparison.inv5_independent_endpoint_bound
