/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.

# L4 — the sharp Sturm first-zero bound: equality of curvatures forces proportionality

`Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` proves that, if `k ≤ K` and `u` has a
*first* zero `c` at or before the model's first zero, then `k = K` on `(a,c)`.  The remaining
gap in the two-sided count is the equality case: when `k = K` on `(a,c)`, can a nonzero
solution still vanish at `c` before `π/√K`?  This file closes that gap with the Wronskian, and
removes the "first zero" hypothesis from the sharp statement.

* `wronskian_sturmModel_eq_zero_of_pos` — if `k = K` on `(a,c)`, `u > 0` on `(a,c)` with
  `u a = u c = 0`, then the Wronskian `W = u·m' − m·u'` (with `m = sturmModel K a`) vanishes
  on all of `[a,c]`.  Both endpoints give `W = 0` (at `c` via the endpoint derivative sign
  lemma), and the Wronskian is antitone because the two curvatures agree.
* `eq_zero_of_wronskian_sturmModel_eq_zero` — if `W ≡ 0` on `[a,c]` and `√K (c-a) < π`, then
  `u ≡ 0` on `(a,c)`: `W = 0` makes `(u/m)' = 0`, so `u = λ·m` on `(a,c)`; continuity extends
  the identity to `c`, and `m c > 0` forces `λ = 0`.
* `no_first_zero_of_curvature_le_of_lt_pi` — **the sharp theorem:** if `k ≤ K` on `[a,c]`,
  `u` is a Jacobi solution with `u a = u c = 0`, and `√K (c-a) < π`, then `c` cannot be the
  first zero of `u` after `a`.  In particular a *nonzero* solution has no zero strictly before
  `a + π/√K`.  The strict inequality is necessary: `strict_span_necessary` exhibits the model
  itself, whose first zero sits exactly at `π/√K`.
* `no_first_zero_before_pi_sqrt_of_curvature_le` — anchored form at `0`.

Everything is scalar ODE data.  No manifold, geodesic, exponential map or curvature-tensor
statement is constructed or claimed; the existence of a first zero (equivalently `u' a ≠ 0`)
is a hypothesis, not a conclusion.
-/
import Poincare.L4.GeodesicComparison.TwoSidedSturm

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics

/-! ## 1. Positivity of the model at the right endpoint -/

/-- The shifted model is strictly positive at `c` when `0 < √K (c - a) < π` (the pointwise
form used to evaluate the ratio `u / m` at the right endpoint). -/
theorem sturmModel_pos_at_right {K a c : ℝ} (hK : 0 < K) (hac : a < c)
    (hspan : Real.sqrt K * (c - a) < Real.pi) : 0 < sturmModel K a c := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have h1 : 0 < Real.sqrt K * (c - a) := mul_pos hsqrt (by linarith)
  simpa [sturmModel] using Real.sin_pos_of_pos_of_lt_pi h1 hspan

/-- The model vanishes at `a + π/√K`: the equality case of the sharp first-zero bound. -/
theorem sturmModel_eq_zero_at_pi_sqrt {K a : ℝ} (hK : 0 < K) :
    sturmModel K a (a + Real.pi / Real.sqrt K) = 0 := by
  have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos_of_pos hK).ne'
  simp only [sturmModel]
  have harg : Real.sqrt K * (a + Real.pi / Real.sqrt K - a) = Real.pi := by
    rw [add_sub_cancel_left, mul_div_cancel₀ Real.pi hsqrt]
  rw [harg, Real.sin_pi]

/-! ## 2. The Wronskian vanishes in the equality case -/

/-- **The Wronskian vanishes identically when the curvatures agree.**  Let `k = K` on `(a,c)`,
let `u > 0` on `(a,c)` be a Jacobi solution on `[a,b]` with `a < c < b` and `u a = u c = 0`.
Then `W = u·m' − m·u'` (with `m = sturmModel K a`) vanishes on `[a,c]`.

At `a` and `c` both `W`-values are `0`: at `a` because `u a = m a = 0`, at `c` because
`u c = 0` and the endpoint derivative `u' c` is `≤ 0` while `m c > 0`.  Since `k = K`, the
Wronskian is antitone on `[a,c]`, so it is squeezed between its two endpoint values. -/
theorem wronskian_sturmModel_eq_zero_of_pos {k : ℝ → ℝ} {K a b c : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) < Real.pi)
    (hk : ∀ t ∈ Ioo a c, k t = K)
    (h : JacobiSolutionOn k u du ddu a b) (hca : c ∈ Ioo a b)
    (hua : u a = 0) (huc : u c = 0)
    (hupos : ∀ t ∈ Ioo a c, 0 < u t) (hduc : HasDerivAtR u (du c) c) :
    ∀ t ∈ Icc a c,
      wronskian (sturmModel K a) (sturmModelDeriv K a) u du t = 0 := by
  have hac : a < c := hca.1
  have hmono : JacobiSolutionOn k u du ddu a c :=
    jacobiSolutionOn_mono_Icc h hac.le hca.2.le
  have hmodel : JacobiSolutionOn (fun _ : ℝ => K) (sturmModel K a) (sturmModelDeriv K a)
      (sturmModelSecondDeriv K a) a c :=
    sturmModel_jacobiSolutionOn (K := K) (a := a) (b := c) hK.le
  have hspanle : Real.sqrt K * (c - a) ≤ Real.pi := le_of_lt hspan
  have hmpos : ∀ t ∈ Ioo a c, 0 < sturmModel K a t :=
    fun _ ht => sturmModel_pos_of_le hK hspanle ht
  have hAnti : AntitoneOn
      (wronskian (sturmModel K a) (sturmModelDeriv K a) u du) (Icc a c) := by
    refine wronskian_antitoneOn_of_le hac.le ?_ ?_ hmodel hmono
    · intro t ht
      rw [hk t ht]
    · intro t ht
      exact le_of_lt (mul_pos (hmpos t ht) (hupos t ht))
  have hWa : wronskian (sturmModel K a) (sturmModelDeriv K a) u du a = 0 := by
    simp [wronskian, hua, sturmModel]
  have hmc_pos : 0 < sturmModel K a c := sturmModel_pos_at_right hK hac hspan
  have hdu_le : du c ≤ 0 :=
    deriv_nonpos_of_posOn_Ioo_of_eq_at_right hac hupos huc hduc
  have hWc_eq : wronskian (sturmModel K a) (sturmModelDeriv K a) u du c
      = -(sturmModel K a c * du c) := by
    simp only [wronskian, huc, zero_mul, zero_sub]
  have hWc_nonneg : 0 ≤ wronskian (sturmModel K a) (sturmModelDeriv K a) u du c := by
    rw [hWc_eq]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hmc_pos.le hdu_le)
  have hWc_le : wronskian (sturmModel K a) (sturmModelDeriv K a) u du c
      ≤ wronskian (sturmModel K a) (sturmModelDeriv K a) u du a :=
    hAnti (left_mem_Icc.mpr hac.le) (right_mem_Icc.mpr hac.le) hac.le
  rw [hWa] at hWc_le
  have hWc : wronskian (sturmModel K a) (sturmModelDeriv K a) u du c = 0 :=
    le_antisymm hWc_le hWc_nonneg
  intro t ht
  have h1 : wronskian (sturmModel K a) (sturmModelDeriv K a) u du t
      ≤ wronskian (sturmModel K a) (sturmModelDeriv K a) u du a :=
    hAnti (left_mem_Icc.mpr hac.le) ht ht.1
  have h2 : wronskian (sturmModel K a) (sturmModelDeriv K a) u du c
      ≤ wronskian (sturmModel K a) (sturmModelDeriv K a) u du t :=
    hAnti ht (right_mem_Icc.mpr hac.le) ht.2
  rw [hWa] at h1
  rw [hWc] at h2
  linarith

/-! ## 3. Proportionality in the equality case -/

/-- **A vanishing Wronskian makes `u` proportional to the model.**  If
`W = u·m' − m·u' ≡ 0` on `[a,c]` with `√K (c-a) ≤ π`, then `u = λ·m` on `(a,c)` for some
`λ : ℝ`: the ratio `u/m` has zero derivative there and `m > 0`. -/
theorem exists_smul_sturmModel_of_wronskian_eq_zero {K a c : ℝ} {u du : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) ≤ Real.pi)
    (hu_deriv : ∀ t ∈ Ioo a c, HasDerivAtR u (du t) t)
    (hW : ∀ t ∈ Icc a c, wronskian (sturmModel K a) (sturmModelDeriv K a) u du t = 0) :
    ∃ lam, ∀ t ∈ Ioo a c, u t = lam * sturmModel K a t := by
  have hmpos : ∀ t ∈ Ioo a c, 0 < sturmModel K a t :=
    fun _ ht => sturmModel_pos_of_le hK hspan ht
  have hratio_deriv : ∀ t ∈ Ioo a c,
      HasDerivAt (fun s : ℝ => u s / sturmModel K a s) 0 t := by
    intro t ht
    have hdiv := (hu_deriv t ht).div (hasDerivAtR_sturmModel K a t) (ne_of_gt (hmpos t ht))
    have hWt : u t * sturmModelDeriv K a t - sturmModel K a t * du t = 0 := by
      have := hW t (Ioo_subset_Icc_self ht)
      simpa [wronskian] using this
    have hnum : du t * sturmModel K a t - u t * sturmModelDeriv K a t = 0 := by linarith
    have hval : (du t * sturmModel K a t - u t * sturmModelDeriv K a t)
        / (sturmModel K a t) ^ 2 = 0 := by
      rw [hnum]
      simp
    rwa [hval] at hdiv
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => u s / sturmModel K a s) (Ioo a c) :=
    fun t ht => (hratio_deriv t ht).differentiableAt.differentiableWithinAt
  have hderiv0 : (Ioo a c).EqOn (deriv fun s : ℝ => u s / sturmModel K a s) 0 :=
    fun t ht => (hratio_deriv t ht).deriv
  obtain ⟨lam, hlam⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (Convex.isPreconnected (convex_Ioo a c)) hdiff hderiv0
  refine ⟨lam, fun t ht => ?_⟩
  have hmne : sturmModel K a t ≠ 0 := ne_of_gt (hmpos t ht)
  have hval := hlam t ht
  rwa [div_eq_iff hmne] at hval

/-- **The Wronskian vanishes identically when the curvatures agree.**  If `k = K` on `(a,c)`
and `u` is a Jacobi solution on `[a,b]` with `a < c < b` and `u a = 0`, then
`W = u·m' − m·u' ≡ 0` on `[a,c]`, with *no* sign or first-zero hypothesis: `W` has zero
derivative on `(a,c)`, hence is constant there, and continuity at `a` evaluates the constant
to `W a = 0`. -/
theorem wronskian_sturmModel_eq_zero_of_curvature_eq {k : ℝ → ℝ} {K a b c : ℝ}
    {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hk : ∀ t ∈ Ioo a c, k t = K)
    (h : JacobiSolutionOn k u du ddu a b) (hca : c ∈ Ioo a b) (hua : u a = 0) :
    ∀ t ∈ Icc a c, wronskian (sturmModel K a) (sturmModelDeriv K a) u du t = 0 := by
  have hac : a < c := hca.1
  have hmono : JacobiSolutionOn k u du ddu a c := jacobiSolutionOn_mono_Icc h hac.le hca.2.le
  have hmodel : JacobiSolutionOn (fun _ : ℝ => K) (sturmModel K a) (sturmModelDeriv K a)
      (sturmModelSecondDeriv K a) a c := sturmModel_jacobiSolutionOn hK.le
  have hWcont : ContinuousOn (wronskian (sturmModel K a) (sturmModelDeriv K a) u du)
      (Icc a c) :=
    wronskian_continuousOn hmodel.continuousOn_u hmodel.continuousOn_du
      hmono.continuousOn_u hmono.continuousOn_du
  have hWdiff : DifferentiableOn ℝ
      (wronskian (sturmModel K a) (sturmModelDeriv K a) u du) (Ioo a c) :=
    wronskian_differentiableOn hmodel hmono
  have hWderiv : (Ioo a c).EqOn
      (deriv (wronskian (sturmModel K a) (sturmModelDeriv K a) u du)) 0 := by
    intro t ht
    rw [wronskian_deriv hmodel hmono ht]
    have hzero : (k t - K) * sturmModel K a t * u t = 0 := by
      rw [hk t ht]
      ring
    simpa using hzero
  obtain ⟨w, hw⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (Convex.isPreconnected (convex_Ioo a c)) hWdiff hWderiv
  have hconst : Set.EqOn (wronskian (sturmModel K a) (sturmModelDeriv K a) u du)
      (fun _ : ℝ => w) (Icc a c) :=
    Set.EqOn.of_subset_closure hw hWcont continuous_const.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt hac)])
  have hwa : wronskian (sturmModel K a) (sturmModelDeriv K a) u du a = 0 := by
    simp [wronskian, hua, sturmModel]
  have hw0 : w = 0 := by
    have hval := hconst (left_mem_Icc.mpr hac.le)
    rw [hwa] at hval
    exact hval.symm
  intro t ht
  rw [hconst ht, hw0]

/-- **Proportionality in the equality case of the Sturm comparison.**  If `k = K` on `(a,c)`,
`u` is a Jacobi solution on `[a,b]` with `a < c < b`, `u a = 0` and `√K (c-a) ≤ π`, then `u`
is proportional to the shifted model on `(a,c)`: `u = λ · sin(√K (· - a))`.  This is the
sharp form of the scalar equality case, with neither a sign nor a first-zero hypothesis. -/
theorem exists_smul_sturmModel_of_curvature_eq {k : ℝ → ℝ} {K a b c : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) ≤ Real.pi)
    (hk : ∀ t ∈ Ioo a c, k t = K)
    (h : JacobiSolutionOn k u du ddu a b) (hca : c ∈ Ioo a b) (hua : u a = 0) :
    ∃ lam, ∀ t ∈ Ioo a c, u t = lam * sturmModel K a t :=
  exists_smul_sturmModel_of_wronskian_eq_zero hK hspan
    (fun _ ht => (jacobiSolutionOn_mono_Icc h hca.1.le hca.2.le).hasDerivAt_u ht)
    (wronskian_sturmModel_eq_zero_of_curvature_eq hK hk h hca hua)

/-! ## 4. A vanishing Wronskian forces `u` to vanish -/

/-- **A vanishing Wronskian with `√K(c-a) < π` forces `u ≡ 0`.**  If `W = u·m' − m·u' ≡ 0`
on `[a,c]`, then the ratio `u/m` has zero derivative on `(a,c)`, hence is constant there;
continuity extends the identity `u = λ·m` to `c`, and `m c > 0` forces `λ = 0`. -/
theorem eq_zero_of_wronskian_sturmModel_eq_zero {K a c : ℝ} {u du : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) < Real.pi) (hac : a < c)
    (hu_cont : ContinuousOn u (Icc a c))
    (hu_deriv : ∀ t ∈ Ioo a c, HasDerivAtR u (du t) t)
    (huc : u c = 0)
    (hW : ∀ t ∈ Icc a c, wronskian (sturmModel K a) (sturmModelDeriv K a) u du t = 0) :
    ∀ t ∈ Ioo a c, u t = 0 := by
  have hspanle : Real.sqrt K * (c - a) ≤ Real.pi := le_of_lt hspan
  have hmpos : ∀ t ∈ Ioo a c, 0 < sturmModel K a t :=
    fun _ ht => sturmModel_pos_of_le hK hspanle ht
  have hmcont : ContinuousOn (sturmModel K a) (Icc a c) :=
    (sturmModel_jacobiSolutionOn (K := K) (a := a) (b := c) hK.le).continuousOn_u
  -- derivative of the ratio `u / m` is zero
  have hratio_deriv : ∀ t ∈ Ioo a c,
      HasDerivAt (fun s : ℝ => u s / sturmModel K a s) 0 t := by
    intro t ht
    have hdiv := (hu_deriv t ht).div (hasDerivAtR_sturmModel K a t) (ne_of_gt (hmpos t ht))
    have hWt : u t * sturmModelDeriv K a t - sturmModel K a t * du t = 0 := by
      have := hW t (Ioo_subset_Icc_self ht)
      simpa [wronskian] using this
    have hnum : du t * sturmModel K a t - u t * sturmModelDeriv K a t = 0 := by
      linarith
    have hval : (du t * sturmModel K a t - u t * sturmModelDeriv K a t)
        / (sturmModel K a t) ^ 2 = 0 := by
      rw [hnum]
      simp
    rwa [hval] at hdiv
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => u s / sturmModel K a s) (Ioo a c) :=
    fun t ht => (hratio_deriv t ht).differentiableAt.differentiableWithinAt
  have hderiv0 : (Ioo a c).EqOn (deriv fun s : ℝ => u s / sturmModel K a s) 0 :=
    fun t ht => (hratio_deriv t ht).deriv
  obtain ⟨lam, hlam⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (Convex.isPreconnected (convex_Ioo a c)) hdiff hderiv0
  -- extend `u = lam * m` from `(a,c)` to `c` by continuity
  have hEqOn : Set.EqOn u (fun t : ℝ => lam * sturmModel K a t) (Ioo a c) := by
    intro t ht
    have hmne : sturmModel K a t ≠ 0 := ne_of_gt (hmpos t ht)
    have := hlam t ht
    rw [div_eq_iff hmne] at this
    exact this
  have hcont_lam : ContinuousOn (fun t : ℝ => lam * sturmModel K a t) (Icc a c) :=
    hmcont.const_mul lam
  have hclosure : Set.EqOn u (fun t : ℝ => lam * sturmModel K a t) (Icc a c) :=
    Set.EqOn.of_subset_closure hEqOn hu_cont hcont_lam Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt hac)])
  have hc_mem : c ∈ Icc a c := right_mem_Icc.mpr hac.le
  have hmc_ne : sturmModel K a c ≠ 0 := ne_of_gt (sturmModel_pos_at_right hK hac hspan)
  have hlam_eq : lam = 0 := by
    have hval : u c = lam * sturmModel K a c := hclosure hc_mem
    rw [huc] at hval
    exact (mul_eq_zero.mp hval.symm).resolve_right hmc_ne
  intro t ht
  simp [hEqOn ht, hlam_eq]

/-! ## 5. The sharp first-zero bound -/

/-- **No first zero strictly before the model's first zero when `k ≤ K`.**  If `k ≤ K` on
`[a,c]`, `u` is a Jacobi solution on `[a,b]` with `a < c < b` and `u a = u c = 0`, and
`√K (c-a) < π`, then `c` cannot be the *first* zero of `u` after `a`.

Proof: `TwoSidedSturm.eq_curvature_of_first_jacobi_zero_of_curvature_le` forces `k = K` on
`(a,c)`; the sign-constant solution then has a vanishing Wronskian against the model
(`wronskian_sturmModel_eq_zero_of_pos`), so `eq_zero_of_wronskian_sturmModel_eq_zero` makes `u`
vanish on all of `(a,c)`, contradicting the first-zero hypothesis.  In particular a nonzero
Jacobi solution with `u a = 0` has no zero strictly before `a + π/√K`. -/
theorem no_first_zero_of_curvature_le_of_lt_pi {k : ℝ → ℝ} {K a b c : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) < Real.pi)
    (hk : ∀ t ∈ Icc a c, k t ≤ K)
    (h : JacobiSolutionOn k u du ddu a b) (hca : c ∈ Ioo a b)
    (hua : u a = 0) (huc : u c = 0) (hfirst : ∀ t ∈ Ioo a c, u t ≠ 0) : False := by
  have hac : a < c := hca.1
  have hspanle : Real.sqrt K * (c - a) ≤ Real.pi := le_of_lt hspan
  have heq : ∀ t ∈ Ioo a c, k t = K :=
    eq_curvature_of_first_jacobi_zero_of_curvature_le hK hspanle hk h hca hua huc hfirst
  have hmono : JacobiSolutionOn k u du ddu a c := jacobiSolutionOn_mono_Icc h hac.le hca.2.le
  have hcont : ContinuousOn u (Ioo a c) :=
    h.continuousOn_u.mono fun t ht => ⟨ht.1.le, (ht.2.trans hca.2).le⟩
  have hduc : HasDerivAtR u (du c) c := h.hasDerivAt_u hca
  obtain ⟨t, ht⟩ := exists_between hac
  rcases sign_constant_of_no_zero hcont hfirst with hpos | hneg
  · have hW := wronskian_sturmModel_eq_zero_of_pos hK hspan heq h hca hua huc hpos hduc
    have hzero := eq_zero_of_wronskian_sturmModel_eq_zero hK hspan hac hmono.continuousOn_u
      (fun _ ht => hmono.hasDerivAt_u ht) huc hW
    exact hfirst t ht (hzero t ht)
  · have hW := wronskian_sturmModel_eq_zero_of_pos (u := -u) (du := -du) (ddu := -ddu)
      hK hspan heq h.neg hca (by simp [hua]) (by simp [huc])
      (fun _ ht => neg_pos.mpr (hneg ht)) hduc.neg
    have hzero := eq_zero_of_wronskian_sturmModel_eq_zero (u := -u) (du := -du) hK hspan hac
      hmono.neg.continuousOn_u (fun _ ht => hmono.neg.hasDerivAt_u ht) (by simp [huc]) hW
    exact (ne_of_lt (hneg ht)) (by simpa using hzero t ht)

/-- **Anchored form at `0`.**  For `k ≤ K` on `[0,c]`, a Jacobi solution with `u 0 = u c = 0`
and `√K · c < π` cannot have `c` as its first zero after `0`. -/
theorem no_first_zero_before_pi_sqrt_of_curvature_le {k : ℝ → ℝ} {K b c : ℝ}
    {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * c < Real.pi)
    (hk : ∀ t ∈ Icc 0 c, k t ≤ K)
    (h : JacobiSolutionOn k u du ddu 0 b) (hc : c ∈ Ioo 0 b)
    (hu0 : u 0 = 0) (huc : u c = 0) (hfirst : ∀ t ∈ Ioo 0 c, u t ≠ 0) : False :=
  no_first_zero_of_curvature_le_of_lt_pi (a := 0) hK (by simpa using hspan) hk h hc hu0 huc hfirst

/-- **Local nonvanishing at a simple zero.**  If `u` is differentiable at `a` with nonzero
derivative and `u a = 0`, then `u` does not vanish on a right-neighbourhood `(a, a+ε)`. -/
theorem nonvanishing_near_left_of_deriv_ne {u : ℝ → ℝ} {a m : ℝ}
    (ha : HasDerivAtR u m a) (hm : m ≠ 0) :
    ∃ ε > 0, ∀ t, a < t → t < a + ε → u t ≠ u a := by
  have hsub : Ioi a ⊆ ({a}ᶜ : Set ℝ) := fun _ hx => ne_of_gt hx
  have hev : ∀ᶠ t in 𝓝[>] a, u t ≠ u a :=
    (nhdsWithin_mono a hsub) (ha.eventually_ne hm)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hεpos, fun t hat hlt => hε (y := t) ?_ hat⟩
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hat)]
  linarith

/-- **The global sharp first-zero bound.**  If `k ≤ K` on `[a,b]`, `u` is a Jacobi solution on
`[a,b]` with `u a = 0` and `u' a ≠ 0` (the endpoint derivative is a hypothesis, as in the
initial data of a Jacobi field), and `√K (b-a) < π`, then `u` has **no** zero in `(a,b)`:
a nonzero solution vanishing at `a` cannot return to zero before `a + π/√K`.

Proof: `u` is nonzero on a right-neighbourhood of `a`; if `u c = 0` with `c ∈ (a,b)`, the
zero set in `[a+ε/2, c]` is compact and nonempty, so it has a least element `c₁`, which is a
genuine *first* zero; `no_first_zero_of_curvature_le_of_lt_pi` then gives a contradiction. -/
theorem no_zero_of_curvature_le_of_deriv_ne {k : ℝ → ℝ} {K a b : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (b - a) < Real.pi)
    (hk : ∀ t ∈ Icc a b, k t ≤ K)
    (h : JacobiSolutionOn k u du ddu a b)
    (ha : HasDerivAtR u (du a) a) (hua : u a = 0) (hdua : du a ≠ 0) :
    ∀ c ∈ Ioo a b, u c ≠ 0 := by
  intro c hc huc
  obtain ⟨ε, hεpos, hε⟩ := nonvanishing_near_left_of_deriv_ne ha hdua
  by_cases hsmall : c < a + ε
  · exact hε c hc.1 hsmall (by rw [huc, hua])
  · have hδc : a + ε / 2 ≤ c := by linarith
    have haδ : a < a + ε / 2 := by linarith
    have hsub : Icc (a + ε / 2) c ⊆ Icc a b :=
      fun t ht => ⟨by linarith [ht.1], ht.2.trans hc.2.le⟩
    have hZclosed : IsClosed (Icc (a + ε / 2) c ∩ u ⁻¹' {0}) :=
      (h.continuousOn_u.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton
    have hZcompact : IsCompact (Icc (a + ε / 2) c ∩ u ⁻¹' {0}) :=
      (isCompact_Icc (a := a + ε / 2) (b := c)).of_isClosed_subset hZclosed inter_subset_left
    have hZne : (Icc (a + ε / 2) c ∩ u ⁻¹' {0}).Nonempty :=
      ⟨c, right_mem_Icc.mpr hδc, huc⟩
    obtain ⟨c₁, hc₁Z, hc₁min⟩ := hZcompact.exists_isMinOn hZne continuous_id.continuousOn
    have hc₁_mem : c₁ ∈ Icc (a + ε / 2) c := hc₁Z.1
    have hc₁zero : u c₁ = 0 := hc₁Z.2
    have hac₁ : a < c₁ := lt_of_lt_of_le haδ hc₁_mem.1
    have hc₁b : c₁ < b := lt_of_le_of_lt hc₁_mem.2 hc.2
    have hfirst : ∀ t ∈ Ioo a c₁, u t ≠ 0 := by
      intro t ht htzero
      by_cases htδ : t < a + ε / 2
      · exact hε t ht.1 (by linarith) (by rw [htzero, hua])
      · have htZ : t ∈ Icc (a + ε / 2) c ∩ u ⁻¹' {0} :=
          ⟨⟨le_of_not_gt htδ, ht.2.le.trans hc₁_mem.2⟩, htzero⟩
        have hle : c₁ ≤ t := hc₁min htZ
        linarith [ht.2]
    have hspan₁ : Real.sqrt K * (c₁ - a) < Real.pi := by
      have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
      have hle : c₁ - a ≤ b - a := by linarith [hc₁b]
      calc Real.sqrt K * (c₁ - a) ≤ Real.sqrt K * (b - a) :=
            mul_le_mul_of_nonneg_left hle hsqrt.le
        _ < Real.pi := hspan
    exact no_first_zero_of_curvature_le_of_lt_pi hK hspan₁
      (fun t ht => hk t ⟨ht.1, ht.2.trans hc₁b.le⟩) h ⟨hac₁, hc₁b⟩ hua hc₁zero hfirst

/-! ## 6. The strict inequality is necessary -/

/-- **Sharpness: the strict inequality `√K (c-a) < π` cannot be relaxed to `≤`.**  For
`K = 1`, `k ≡ K`, `u = sin` on `(0, 2π)` and `c = π`, every hypothesis of
`no_first_zero_before_pi_sqrt_of_curvature_le` holds *except* the strict inequality (there
`√K · c = π`), and the conclusion fails: `sin` has its first zero exactly at `π`.  Hence the
equality case genuinely admits a first zero at the model's first zero. -/
theorem strict_span_necessary :
    ∃ (k : ℝ → ℝ) (u du ddu : ℝ → ℝ),
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, k t = 1) ∧
        JacobiSolutionOn k u du ddu 0 (2 * Real.pi) ∧ u 0 = 0 ∧ u Real.pi = 0 ∧
        (∀ t ∈ Ioo (0 : ℝ) Real.pi, u t ≠ 0) ∧ Real.sqrt 1 * Real.pi = Real.pi := by
  refine ⟨fun _ : ℝ => 1, sturmModel 1 0, sturmModelDeriv 1 0, sturmModelSecondDeriv 1 0,
    fun _ _ => rfl,
    sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := 2 * Real.pi) (by norm_num),
    by simp [sturmModel], ?_, ?_, by rw [Real.sqrt_one, one_mul]⟩
  · simp only [sturmModel, Real.sqrt_one, one_mul, sub_zero]
    exact Real.sin_pi
  · intro t ht h
    exact sin_no_zero_in_Ioo_zero_pi ⟨t, ht, by simpa [sturmModel] using h⟩

end Poincare.L4.GeodesicComparison
