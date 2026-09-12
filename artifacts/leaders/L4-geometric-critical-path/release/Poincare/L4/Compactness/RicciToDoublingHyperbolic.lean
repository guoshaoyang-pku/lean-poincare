/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — the constant-curvature hyperbolic comparison model (K ≤ 0, k ≥ d·K)

The companion file `RicciToDoubling.lean` instantiates D12's `bishopGromov_volume_le` with
the **Euclidean** comparison model, valid for a nonnegative radial curvature function
(`k ≥ 0`).  This file supplies the **hyperbolic** comparison model for the range
`K = -κ² ≤ 0` (equivalently `k ≥ d·K = -d·κ²`), which contains the Euclidean range
`k ≥ 0` as the limiting case `κ → 0`; the two files are complementary in the sense that the
Euclidean model is the flat comparison and the hyperbolic model the negative-curvature one.

Conventions (matching D12's `RiccatiLeOn` docstring): the scalar Riccati unknown is
`m = A'/A`, `d = n − 1` is the dimension parameter, and the "curvature function" `k` is the
radial curvature (the `(n−1)`-fold normalized Ricci term), so that the constant-curvature
model of sectional curvature `K = -κ² ≤ 0` has

    kbar = d·K = -d·κ²,      mbar t = d·κ·coth(κ t),      Abar t = (sinh(κ t)/κ)^d,

and `mbar' + mbar²/d + kbar = 0` holds exactly.  The file proves, from scratch (no
`Real.coth` exists in the pinned mathlib, so `coth` is written as `cosh/sinh`):

* `hypModelM_hasDerivAt`, `hypModelM_contOn`, `hypModelM_riccati` — the model Riccati
  equality and regularity;
* `hypModelM_normalized` — the Euclidean normalization `|mbar t − d/t| ≤ d·κ` on `(0,t₀)`,
  proved from the elementary bound `0 ≤ x·cosh x − sinh x ≤ x·sinh x` (`x ≥ 0`);
* `hypModelA_hasDerivAt`, `hypModelA_contOn`, `hypModelA_pos`, `hypModelA_zero`,
  `hypModelA_logDeriv` — the model radial area and its logarithmic derivative;
* `hyp_volume_ratio_le_of_ricci_ge` — the instantiation of `bishopGromov_volume_le` with the
  explicit hyperbolic model for `k ≥ -d·κ²` (sectional curvature `≥ -κ²`), together with the
  model-normalization constant hypothesis `d·κ ≤ C`:
  `radialVolume A R ≤ (V̄ R / V̄ r) · radialVolume A r` with
  `V̄ t = radialVolume (hypModelA d κ) t` (the hyperbolic closed form; no elementary
  antiderivative of `sinh^d` is claimed for general `d`);
* `hyp_volume_doubling_of_ricci_ge` — the single-scale doubling consequence at `R = 2 s`,
  with the explicit scale-dependent model constant `V̄ (2s)/V̄ s`;
* `hypModel_doubling_witness` — non-vacuity: the model satisfies every hypothesis;
* `coth_sub_inv_abs_le_one` — the elementary `coth` bound behind the normalization
  (public, used by `hypModelM_normalized`);
* Section 7 (`hypModelA_one_one_volume`, `hypModelA_one_one_doubling`,
  `hyp_volume_doubling_d1_k1`) — the evaluated `d = 1`, `κ = 1` closed forms
  (`V̄ s = cosh s − 1`, ratio `2(cosh s + 1)`).

Every declaration carries a `**Class:**` line; all declarations in this file are
`model (scalar ODE)` — no manifold, metric or measure structure occurs.  Nothing here
constructs a Riemannian manifold or a manifold measure.
-/
import Poincare.L4.Compactness.RicciToDoubling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Poincare.L4.Compactness

open Poincare.D12.ComparisonGeodesics

/-! ## 1. The model data -/

/-- **Class:** model (scalar ODE).

The model curvature function `kbar = -d·κ²`, i.e. `d` times the sectional curvature
`K = -κ²`.  It is the constant right-hand side for which `hypModelM` satisfies the Riccati
equality.  Analytic hypotheses: none (a definition); `κ` is the curvature magnitude and
`d` the dimension parameter `n − 1`. -/
noncomputable def hypModelK (d : ℕ) (κ : ℝ) : ℝ := -((d : ℝ) * κ ^ 2)

/-- **Class:** model (scalar ODE).

The hyperbolic model radial area `Abar t = (sinh(κ t)/κ)^d`.  Analytic hypotheses: none
(a definition); positivity on `(0,T]` and `Abar 0 = 0` are proved below for `κ > 0`,
`d ≥ 1`. -/
noncomputable def hypModelA (d : ℕ) (κ t : ℝ) : ℝ := (Real.sinh (κ * t) / κ) ^ d

/-- **Class:** model (scalar ODE).

The hyperbolic model logarithmic derivative `mbar t = d·κ·cosh(κ t)/sinh(κ t)`
(`= d·κ·coth(κ t)`).  Analytic hypotheses: none (a definition). -/
noncomputable def hypModelM (d : ℕ) (κ t : ℝ) : ℝ :=
  (d : ℝ) * κ * (Real.cosh (κ * t) / Real.sinh (κ * t))

/-- **Class:** model (scalar ODE).

The explicit derivative of `hypModelM`: `t ↦ −d·κ²/sinh(κ t)²`.  Analytic hypotheses: none
(a definition). -/
noncomputable def hypModelDm (d : ℕ) (κ t : ℝ) : ℝ :=
  -((d : ℝ) * κ ^ 2 / (Real.sinh (κ * t)) ^ 2)

/-- **Class:** model (scalar ODE).

The explicit derivative of `hypModelA`: `t ↦ d·(sinh(κ t)/κ)^(d−1)·cosh(κ t)`.  Analytic
hypotheses: none (a definition). -/
noncomputable def hypModelDA (d : ℕ) (κ t : ℝ) : ℝ :=
  (d : ℝ) * (Real.sinh (κ * t) / κ) ^ (d - 1) * Real.cosh (κ * t)

/-! ## 2. Elementary hyperbolic inequalities used for the normalization

The normalization bound for `mbar` reduces to
`0 ≤ x·cosh x − sinh x ≤ x·sinh x` for `x ≥ 0`, which is proved here from
`cosh² − sinh² = 1`, `sinh x ≥ x` and `exp(−x) ≤ 1`.  These are scalar real inequalities;
they are stated as private lemmas (not part of the public interface). -/

/-- **Class:** model (scalar ODE), private helper.

`0 ≤ x·cosh x − sinh x` for `x ≥ 0` (equivalently `sinh x ≤ x·cosh x`), proved by
monotonicity of `y ↦ y·cosh y − sinh y`, whose derivative is `y·sinh y ≥ 0`.  Analytic
hypotheses: `0 ≤ x`. -/
private theorem sinh_mul_cosh_sub_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.cosh x - Real.sinh x := by
  have hcont : ContinuousOn (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Ici 0) := by fun_prop
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => y * Real.cosh y - Real.sinh y) (interior (Ici 0)) := by
    rw [interior_Ici]
    intro y _
    exact ((differentiableAt_id.mul Real.differentiableAt_cosh).sub
      Real.differentiableAt_sinh).differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Ici 0),
      0 ≤ deriv (fun y : ℝ => y * Real.cosh y - Real.sinh y) y := by
    rw [interior_Ici]
    intro y hy
    have hd : HasDerivAtR (fun y : ℝ => y * Real.cosh y - Real.sinh y) (y * Real.sinh y) y := by
      have h := ((hasDerivAtR_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
      have hderiv_eq : 1 * Real.cosh y + y * Real.sinh y - Real.cosh y = y * Real.sinh y := by ring
      convert h using 1
      · ext x
        simp
      · rw [hderiv_eq]
    rw [hd.deriv]
    exact mul_nonneg hy.le (Real.sinh_pos_iff.mpr hy).le
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hderiv
  have h0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simpa using h0

/-- **Class:** model (scalar ODE), private helper.

`x·cosh x − sinh x ≤ x·sinh x` for `x ≥ 0` (equivalently `x·exp(−x) ≤ sinh x`), proved
from `cosh − sinh = exp(−x)`, `exp(−x) ≤ 1` and `x ≤ sinh x`.  Analytic hypotheses:
`0 ≤ x`. -/
private theorem sinh_mul_cosh_sub_sinh_le {x : ℝ} (hx : 0 ≤ x) :
    x * Real.cosh x - Real.sinh x ≤ x * Real.sinh x := by
  have hexp : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hxe : x * Real.exp (-x) ≤ x * 1 := mul_le_mul_of_nonneg_left hexp hx
  have hxsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx
  have hmain : x * Real.exp (-x) ≤ Real.sinh x := by linarith
  have hcs : Real.cosh x - Real.sinh x = Real.exp (-x) := Real.cosh_sub_sinh x
  nlinarith [hmain, hcs]

/-- **Class:** model (scalar ODE).

The `coth` bound behind the Euclidean normalization of the hyperbolic model: for `x > 0`,
`|cosh x / sinh x − 1/x| ≤ 1`.  Equivalently `0 ≤ coth x − 1/x ≤ 1`.  Analytic
hypotheses: `0 < x` only. -/
theorem coth_sub_inv_abs_le_one {x : ℝ} (hx : 0 < x) :
    |Real.cosh x / Real.sinh x - 1 / x| ≤ 1 := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hxsinh : 0 < Real.sinh x * x := mul_pos hs hx
  have hlower : 0 ≤ Real.cosh x / Real.sinh x - 1 / x := by
    rw [div_sub_div _ _ (ne_of_gt hs) (ne_of_gt hx)]
    exact div_nonneg (by linarith [sinh_mul_cosh_sub_sinh_nonneg hx.le]) hxsinh.le
  have hupper : Real.cosh x / Real.sinh x - 1 / x ≤ 1 := by
    rw [div_sub_div _ _ (ne_of_gt hs) (ne_of_gt hx)]
    exact (div_le_one hxsinh).mpr (by linarith [sinh_mul_cosh_sub_sinh_le hx.le])
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-! ## 3. The model Riccati equality and regularity -/

/-- **Class:** model (scalar ODE).

Derivative of the hyperbolic model logarithmic derivative:
`mbar' = −d·κ²/sinh(κ t)²` for `κ ≠ 0` and `t ≠ 0` (where `sinh(κ t) ≠ 0`).  Analytic
hypotheses: `κ ≠ 0`, `t ≠ 0`; no positivity of `t` is needed. -/
theorem hypModelM_hasDerivAt {d : ℕ} {κ t : ℝ} (hκ : κ ≠ 0) (ht : t ≠ 0) :
    HasDerivAtR (hypModelM d κ) (hypModelDm d κ t) t := by
  have hlin : HasDerivAtR (fun s : ℝ => κ * s) κ t := by
    simpa using (hasDerivAtR_id t).const_mul κ
  have hcosh : HasDerivAtR (fun s : ℝ => Real.cosh (κ * s)) (Real.sinh (κ * t) * κ) t :=
    (Real.hasDerivAt_cosh (κ * t)).comp t hlin
  have hsinh : HasDerivAtR (fun s : ℝ => Real.sinh (κ * s)) (Real.cosh (κ * t) * κ) t :=
    (Real.hasDerivAt_sinh (κ * t)).comp t hlin
  have hsinhne : Real.sinh (κ * t) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero hκ ht)
  have hdiv : HasDerivAtR (fun s : ℝ => Real.cosh (κ * s) / Real.sinh (κ * s))
      ((Real.sinh (κ * t) * κ * Real.sinh (κ * t)
          - Real.cosh (κ * t) * (Real.cosh (κ * t) * κ)) / Real.sinh (κ * t) ^ 2) t :=
    hcosh.div hsinh hsinhne
  have hmain : HasDerivAtR (fun s : ℝ => (d : ℝ) * κ * (Real.cosh (κ * s) / Real.sinh (κ * s)))
      ((d : ℝ) * κ * ((Real.sinh (κ * t) * κ * Real.sinh (κ * t)
          - Real.cosh (κ * t) * (Real.cosh (κ * t) * κ)) / Real.sinh (κ * t) ^ 2)) t :=
    hdiv.const_mul ((d : ℝ) * κ)
  convert hmain using 1
  · ext s
    rfl
  · unfold hypModelDm
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (κ * t)]

/-- **Class:** model (scalar ODE).

The hyperbolic model satisfies the model Riccati equality
`mbar' + mbar²/d + kbar = 0` with `kbar = −d·κ²`, for `κ ≠ 0`, `t ≠ 0` and `d ≠ 0`.
Analytic hypotheses: `(d : ℝ) ≠ 0`, `κ ≠ 0`, `t ≠ 0`. -/
theorem hypModelM_riccati {d : ℕ} {κ t : ℝ} (hd : (d : ℝ) ≠ 0) (hκ : κ ≠ 0) (ht : t ≠ 0) :
    hypModelDm d κ t + hypModelM d κ t ^ 2 / (d : ℝ) + hypModelK d κ = 0 := by
  have hsinhne : Real.sinh (κ * t) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero hκ ht)
  have hs2 : (Real.sinh (κ * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hsinhne
  have hcs := Real.cosh_sq_sub_sinh_sq (κ * t)
  have hsq : ((d : ℝ) * κ * (Real.cosh (κ * t) / Real.sinh (κ * t))) ^ 2 / (d : ℝ)
      = (d : ℝ) * κ ^ 2 * (Real.cosh (κ * t)) ^ 2 / (Real.sinh (κ * t)) ^ 2 := by
    field_simp
  have key : (d : ℝ) * κ ^ 2 * (Real.cosh (κ * t)) ^ 2 / (Real.sinh (κ * t)) ^ 2
      - (d : ℝ) * κ ^ 2 / (Real.sinh (κ * t)) ^ 2 = (d : ℝ) * κ ^ 2 := by
    rw [← sub_div, div_eq_iff hs2]
    have h : (d : ℝ) * κ ^ 2 * (Real.cosh (κ * t)) ^ 2
        - (d : ℝ) * κ ^ 2 * (Real.sinh (κ * t)) ^ 2 = (d : ℝ) * κ ^ 2 := by
      rw [← mul_sub, hcs, mul_one]
    linarith [h]
  unfold hypModelDm hypModelM hypModelK
  rw [hsq]
  linarith [key]

/-- **Class:** model (scalar ODE).

Continuity of the hyperbolic model logarithmic derivative on `(0,T]` for `κ > 0` (so that
`sinh(κ t) ≠ 0` there).  Analytic hypotheses: `κ > 0`. -/
theorem hypModelM_contOn {d : ℕ} {κ T : ℝ} (hκ : 0 < κ) :
    ContinuousOn (hypModelM d κ) (Ioc 0 T) := by
  have hne : ∀ x ∈ Ioc (0 : ℝ) T, Real.sinh (κ * x) ≠ 0 := fun x hx =>
    Real.sinh_ne_zero.mpr (mul_ne_zero (ne_of_gt hκ) (ne_of_gt hx.1))
  unfold hypModelM
  exact ContinuousOn.mul continuousOn_const
    (ContinuousOn.div (Real.continuous_cosh.comp_continuousOn (continuousOn_id.const_mul κ))
      (Real.continuous_sinh.comp_continuousOn (continuousOn_id.const_mul κ)) hne)

/-- **Class:** model (scalar ODE).

Euclidean normalization of the hyperbolic model: for `κ > 0`, `d ≥ 0` and `C ≥ d·κ`,
`|mbar t − d/t| ≤ C` on `(0,t₀)`.  Analytic hypotheses: `κ > 0` and `(d : ℝ)·κ ≤ C`; the
bound is proved from `coth_sub_inv_abs_le_one`. -/
theorem hypModelM_normalized {d : ℕ} {κ C t₀ : ℝ} (hκ : 0 < κ) (hC : (d : ℝ) * κ ≤ C) :
    EuclideanNormalizedOn (hypModelM d κ) (d : ℝ) C t₀ := by
  intro t ht
  have htpos : 0 < t := ht.1
  have hx : 0 < κ * t := mul_pos hκ htpos
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hκnn : (0 : ℝ) ≤ κ := hκ.le
  have hkey : hypModelM d κ t - (d : ℝ) / t
      = (d : ℝ) * κ * (Real.cosh (κ * t) / Real.sinh (κ * t) - 1 / (κ * t)) := by
    unfold hypModelM
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg (mul_nonneg hdnn hκnn)]
  calc (d : ℝ) * κ * |Real.cosh (κ * t) / Real.sinh (κ * t) - 1 / (κ * t)|
      ≤ (d : ℝ) * κ * 1 := mul_le_mul_of_nonneg_left (coth_sub_inv_abs_le_one hx)
          (mul_nonneg hdnn hκnn)
    _ = (d : ℝ) * κ := mul_one _
    _ ≤ C := hC

/-! ## 4. The model radial area -/

/-- **Class:** model (scalar ODE).

Derivative of the hyperbolic model radial area: `Abar' = d·(sinh(κ t)/κ)^(d−1)·cosh(κ t)`
for `κ ≠ 0`.  Analytic hypotheses: `κ ≠ 0`. -/
theorem hypModelA_hasDerivAt {d : ℕ} {κ t : ℝ} (hκ : κ ≠ 0) :
    HasDerivAtR (hypModelA d κ) (hypModelDA d κ t) t := by
  have hlin : HasDerivAtR (fun s : ℝ => κ * s) κ t := by
    simpa using (hasDerivAtR_id t).const_mul κ
  have hsinh : HasDerivAtR (fun s : ℝ => Real.sinh (κ * s)) (Real.cosh (κ * t) * κ) t :=
    (Real.hasDerivAt_sinh (κ * t)).comp t hlin
  have hsinh_div : HasDerivAtR (fun s : ℝ => Real.sinh (κ * s) / κ) (Real.cosh (κ * t)) t := by
    have h := hsinh.div_const κ
    have hval : (Real.cosh (κ * t) * κ) / κ = Real.cosh (κ * t) := by field_simp
    simpa only [hval] using h
  have hpow : HasDerivAtR ((fun s : ℝ => Real.sinh (κ * s) / κ) ^ d)
      ((d : ℝ) * (Real.sinh (κ * t) / κ) ^ (d - 1) * Real.cosh (κ * t)) t :=
    hsinh_div.pow d
  change HasDerivAtR (fun s : ℝ => (Real.sinh (κ * s) / κ) ^ d)
    ((d : ℝ) * (Real.sinh (κ * t) / κ) ^ (d - 1) * Real.cosh (κ * t)) t at hpow
  change HasDerivAtR (fun s : ℝ => (Real.sinh (κ * s) / κ) ^ d)
    ((d : ℝ) * (Real.sinh (κ * t) / κ) ^ (d - 1) * Real.cosh (κ * t)) t
  exact hpow

/-- **Class:** model (scalar ODE).

Continuity of the hyperbolic model radial area on `[0,T]` (for every `κ`; the definition
uses totalized division, and `hypModelA` is a power of a continuous function).  Analytic
hypotheses: none. -/
theorem hypModelA_contOn {d : ℕ} {κ T : ℝ} :
    ContinuousOn (hypModelA d κ) (Icc 0 T) := by
  unfold hypModelA
  exact ((Real.continuous_sinh.comp_continuousOn (continuousOn_id.const_mul κ)).div_const κ).pow d

/-- **Class:** model (scalar ODE).

Positivity of the hyperbolic model radial area on `(0,T]` for `κ > 0`.  Analytic
hypotheses: `κ > 0` (no condition on `d`: `(positive)^0 = 1 > 0`). -/
theorem hypModelA_pos {d : ℕ} {κ T : ℝ} (hκ : 0 < κ) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < hypModelA d κ t := by
  intro t ht
  have hs : 0 < Real.sinh (κ * t) := Real.sinh_pos_iff.mpr (mul_pos hκ ht.1)
  unfold hypModelA
  exact pow_pos (div_pos hs hκ) d

/-- **Class:** model (scalar ODE).

`Abar 0 = 0` for `d ≥ 1`.  Analytic hypotheses: `0 < d` (no condition on `κ`: the
statement is true for every `κ`, including `κ = 0`, by totalized division). -/
theorem hypModelA_zero {d : ℕ} (hdpos : 0 < d) {κ : ℝ} :
    hypModelA d κ 0 = 0 := by
  unfold hypModelA
  rw [mul_zero, Real.sinh_zero, zero_div]
  exact zero_pow (Nat.ne_of_gt hdpos)

/-- **Class:** model (scalar ODE).

Logarithmic derivative of the hyperbolic model radial area: `Abar'/Abar = mbar`, i.e.
`d·(sinh(κ t)/κ)^(d−1)·cosh(κ t) / (sinh(κ t)/κ)^d = d·κ·cosh(κ t)/sinh(κ t)`, for `d ≥ 1`,
`κ ≠ 0`, `t ≠ 0`.  Analytic hypotheses: `0 < d`, `κ ≠ 0`, `t ≠ 0`. -/
theorem hypModelA_logDeriv {d : ℕ} (hdpos : 0 < d) {κ t : ℝ} (hκ : κ ≠ 0) (ht : t ≠ 0) :
    hypModelDA d κ t / hypModelA d κ t = hypModelM d κ t := by
  have hsinhne : Real.sinh (κ * t) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero hκ ht)
  have hu_ne : Real.sinh (κ * t) / κ ≠ 0 := div_ne_zero hsinhne hκ
  have hpow_ne : (Real.sinh (κ * t) / κ) ^ (d - 1) ≠ 0 := pow_ne_zero _ hu_ne
  have hpow_succ : (Real.sinh (κ * t) / κ) ^ d
      = (Real.sinh (κ * t) / κ) ^ (d - 1) * (Real.sinh (κ * t) / κ) := by
    rw [← pow_succ]
    congr 1
    omega
  unfold hypModelDA hypModelA hypModelM
  rw [hpow_succ]
  field_simp

/-! ## 5. Instantiating `bishopGromov_volume_le` with the hyperbolic model -/

/-- **Class:** model (scalar ODE).

**Hyperbolic closed-form Bishop–Gromov volume bound (k ≥ −d·κ²).**  Let `d > 0`, `T > 0`,
`C ≥ 0`, `0 < t₀ ≤ T`, `κ > 0`.  Suppose:

* (`hk`) the radial curvature function is bounded below by the model curvature,
  `−d·κ² ≤ k t` on `(0,T)` (i.e. sectional curvature `≥ −κ²`);
* (`hineq`) the radial area function `A` has logarithmic derivative `m = A'/A` satisfying
  the Riccati inequality `m' + m²/d + k ≤ 0` on `(0,T)`;
* (`hm`, `hmcont`, `hnorm`) `m` has derivative `dm`, is continuous on `(0,T]`, and is
  Euclidean-normalized: `|m t − d/t| ≤ C` on `(0,t₀)`; the *same* constant `C` must also
  bound the model normalization, which is the explicit hypothesis
  `hdκC : d·κ ≤ C`;
* (`hA`, `hAcont`, `hApos`, `hA0`, `hmA`) `A` has derivative `dA` on `(0,T)`, is continuous
  on `[0,T]`, positive on `(0,T]`, vanishes at `0`, and `m = dA/A` there.

Then for `0 < r ≤ R ≤ T`:

    radialVolume A R ≤ (V̄ R / V̄ r) · radialVolume A r,
    V̄ t = radialVolume (hypModelA d κ) t.

This is `bishopGromov_volume_le` instantiated with `Abar = hypModelA d κ`,
`mbar = hypModelM d κ`, `kbar = hypModelK d κ = −d·κ²` (so `hkk` is `hk`) and the model
normalization constant `d·κ ≤ C` (so `hnormbar` is `hypModelM_normalized`).  The ratio
`V̄ R/V̄ r` is the explicit hyperbolic model ratio; no elementary closed form for
`∫₀ᵗ (sinh(κ s)/κ)^d ds` is claimed.  Bishop–Gromov is proved here from the Riccati data,
not assumed. -/
theorem hyp_volume_ratio_le_of_ricci_ge {d : ℕ} (hdpos : 0 < d) {κ T C t₀ : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hdκC : (d : ℝ) * κ ≤ C)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → hypModelK d κ ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {r R : ℝ} (hr : r ∈ Ioc 0 T) (hR : R ∈ Ioc 0 T) (hrR : r ≤ R) :
    radialVolume A R ≤
      (radialVolume (hypModelA d κ) R / radialVolume (hypModelA d κ) r) * radialVolume A r := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd
  have hmodel_eq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T →
      hypModelDm d κ t + hypModelM d κ t ^ 2 / (d : ℝ) + hypModelK d κ = 0 :=
    fun t ht => hypModelM_riccati hdne hκne (ne_of_gt ht.1)
  refine bishopGromov_volume_le (d := (d : ℝ)) hd hT hC ht₀ ht₀T
    (k := k) (kbar := fun _ => hypModelK d κ) (m := m) (dm := dm)
    (mbar := hypModelM d κ) (dmbar := hypModelDm d κ)
    (A := A) (dA := dA) (Abar := hypModelA d κ) (dAbar := hypModelDA d κ)
    hineq hmodel_eq hk hm
    (fun t ht => hypModelM_hasDerivAt hκne (ne_of_gt ht.1))
    hmcont (hypModelM_contOn hκ) hnorm (hypModelM_normalized hκ hdκC)
    hA (fun _t _ht => hypModelA_hasDerivAt hκne) hAcont hypModelA_contOn
    hApos (hypModelA_pos hκ) hA0 (hypModelA_zero hdpos) hmA
    (fun t ht => (hypModelA_logDeriv hdpos hκne (ne_of_gt ht.1)).symm)
    hr hR hrR

/-- **Class:** model (scalar ODE).

**Hyperbolic single-scale doubling.**  Analytic hypotheses (listed explicitly, identical to
`hyp_volume_ratio_le_of_ricci_ge`): `0 < d`, `0 < κ`, `0 < T`, `0 ≤ C`, `0 < t₀ ≤ T`, and
the model-normalization constant bound `d·κ ≤ C`; the scalar curvature function satisfies
`hypModelK d κ = −d·κ² ≤ k t` on `(0,T)`; `dm t + m t²/d + k t ≤ 0` on `(0,T)`; `m` has
derivative `dm` on `(0,T)`, is continuous on `(0,T]`, and `|m t − d/t| ≤ C` on `(0,t₀)`;
`A` has derivative `dA` on `(0,T)`, is continuous on `[0,T]`, positive on `(0,T]`,
`A 0 = 0`, and `m = dA/A` on `(0,T)`; and `0 < s`, `s ≤ T`, `2 s ≤ T`.  Conclusion:

    radialVolume A (2 s) ≤ (V̄ (2 s) / V̄ s) · radialVolume A s,
    V̄ t = radialVolume (hypModelA d κ) t.

The constant is scale-dependent (it grows with `s`), which is the honest hyperbolic
statement: negative curvature does not give a scale-uniform doubling constant, only the
explicit model ratio. -/
theorem hyp_volume_doubling_of_ricci_ge {d : ℕ} (hdpos : 0 < d) {κ T C t₀ : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (hdκC : (d : ℝ) * κ ≤ C)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → hypModelK d κ ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (d : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (d : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume A (2 * s) ≤
      (radialVolume (hypModelA d κ) (2 * s) / radialVolume (hypModelA d κ) s) *
        radialVolume A s :=
  hyp_volume_ratio_le_of_ricci_ge hdpos hκ hT hC ht₀ ht₀T hdκC hk hineq hm hmcont hnorm
    hA hAcont hApos hA0 hmA ⟨hs, hsT⟩ ⟨by linarith, h2s⟩ (by linarith)

/-! ## 6. Non-vacuity of the hyperbolic model -/

/-- **Class:** model (scalar ODE).

The hyperbolic model satisfies every hypothesis of `hyp_volume_doubling_of_ricci_ge` with
`k = kbar = −d·κ²`, `m = mbar`, `A = Abar`, `C = d·κ`, `t₀ = T` (all hypotheses, including
the model-normalization constant `d·κ ≤ C`, are met, so the hypothesis set is jointly
satisfiable), and the conclusion holds for it. -/
theorem hypModel_doubling_witness {d : ℕ} (hdpos : 0 < d) {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume (hypModelA d κ) (2 * s) ≤
      (radialVolume (hypModelA d κ) (2 * s) / radialVolume (hypModelA d κ) s) *
        radialVolume (hypModelA d κ) s := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd
  have hmodel_eq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T →
      hypModelDm d κ t + hypModelM d κ t ^ 2 / (d : ℝ) + hypModelK d κ ≤ 0 :=
    fun t ht => (hypModelM_riccati hdne hκne (ne_of_gt ht.1)).le
  refine hyp_volume_doubling_of_ricci_ge (d := d) (C := (d : ℝ) * κ) hdpos hκ hT
    (by positivity) hT le_rfl le_rfl
    (k := fun _ => hypModelK d κ) (m := hypModelM d κ) (dm := hypModelDm d κ)
    (A := hypModelA d κ) (dA := hypModelDA d κ)
    (fun _t _ht => le_rfl) hmodel_eq
    (fun t ht => hypModelM_hasDerivAt hκne (ne_of_gt ht.1))
    (hypModelM_contOn hκ) (hypModelM_normalized (d := d) (C := (d : ℝ) * κ) hκ le_rfl)
    (fun _t _ht => hypModelA_hasDerivAt hκne) hypModelA_contOn
    (hypModelA_pos hκ) (hypModelA_zero hdpos)
    (fun t ht => (hypModelA_logDeriv hdpos hκne (ne_of_gt ht.1)).symm)
    hs hsT h2s

/-! ## 7. The evaluated `d = 1`, `κ = 1` closed forms

For the lowest dimension parameter the hyperbolic model volume has an elementary
antiderivative (`∫₀ˢ sinh = cosh s − 1`), so the model ratio becomes the fully evaluated
closed form `V̄ (2s)/V̄ s = 2·(cosh s + 1)`.  These declarations make the "hyperbolic closed
form" of criterion (1) fully explicit in that case.  All are `model (scalar ODE)`. -/

/-- **Class:** model (scalar ODE).

The `d = 1`, `κ = 1` model volume: `V̄ s = ∫₀ˢ sinh τ dτ = cosh s − 1`.  Analytic
hypotheses: none. -/
theorem hypModelA_one_one_volume (s : ℝ) :
    radialVolume (hypModelA 1 1) s = Real.cosh s - 1 := by
  unfold radialVolume hypModelA
  simp only [one_mul, div_one, pow_one]
  have hderiv : ∀ x ∈ uIcc 0 s, HasDerivAt (fun y : ℝ => Real.cosh y - 1) (Real.sinh x) x := by
    intro x _
    simpa using (Real.hasDerivAt_cosh x).sub_const 1
  have hint : IntervalIntegrable (fun x : ℝ => Real.sinh x) volume 0 s :=
    Real.continuous_sinh.intervalIntegrable 0 s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- **Class:** model (scalar ODE).

Evaluated `d = 1`, `κ = 1` doubling identity:
`V̄ (2s) = 2·(cosh s + 1)·V̄ s` for the model volume `V̄ s = cosh s − 1` (from
`cosh (2s) = 2 cosh s² − 1`).  Analytic hypotheses: none. -/
theorem hypModelA_one_one_doubling (s : ℝ) :
    radialVolume (hypModelA 1 1) (2 * s)
      = 2 * (Real.cosh s + 1) * radialVolume (hypModelA 1 1) s := by
  rw [hypModelA_one_one_volume, hypModelA_one_one_volume, Real.cosh_two_mul, Real.sinh_sq]
  ring

/-- **Class:** model (scalar ODE).

**Evaluated hyperbolic doubling in the `d = 1`, `κ = 1` case.**  Analytic hypotheses:
`0 < T`, `0 ≤ C`, `0 < t₀ ≤ T`, `1 ≤ C`; `−1 ≤ k t` on `(0,T)`;
`dm t + m t² + k t ≤ 0` on `(0,T)`; `m` has derivative `dm` on `(0,T)`, is continuous on
`(0,T]`, and `|m t − 1/t| ≤ C` on `(0,t₀)`; `A` has derivative `dA` on `(0,T)`, is continuous
on `[0,T]`, positive on `(0,T]`, `A 0 = 0`, and `m = dA/A` on `(0,T)`; `0 < s`, `s ≤ T`,
`2 s ≤ T`.  Conclusion:

    radialVolume A (2 s) ≤ 2 * (Real.cosh s + 1) * radialVolume A s.

This is `hyp_volume_doubling_of_ricci_ge` specialised to `d = 1`, `κ = 1` with the model
ratio evaluated by `hypModelA_one_one_doubling`; the constant `2(cosh s + 1)` is explicit and
grows with `s` (no scale-uniform negative-curvature doubling is claimed). -/
theorem hyp_volume_doubling_d1_k1 {T C t₀ : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hC1 : 1 ≤ C)
    {k m dm A dA : ℝ → ℝ}
    (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → -(1 : ℝ) ≤ k t)
    (hineq : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → dm t + m t ^ 2 / (1 : ℝ) + k t ≤ 0)
    (hm : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR m (dm t) t)
    (hmcont : ContinuousOn m (Ioc 0 T))
    (hnorm : EuclideanNormalizedOn m (1 : ℝ) C t₀)
    (hA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → HasDerivAtR A (dA t) t)
    (hAcont : ContinuousOn A (Icc 0 T))
    (hApos : ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 T → 0 < A t)
    (hA0 : A 0 = 0)
    (hmA : ∀ ⦃t : ℝ⦄, t ∈ Ioo 0 T → m t = dA t / A t)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume A (2 * s) ≤ 2 * (Real.cosh s + 1) * radialVolume A s := by
  have h := hyp_volume_doubling_of_ricci_ge (d := 1) (κ := 1) (C := C) (t₀ := t₀)
    (by norm_num) one_pos hT hC ht₀ ht₀T (by simpa using hC1)
    (k := k) (m := m) (dm := dm) (A := A) (dA := dA)
    (fun t ht => by simpa [hypModelK] using hk ht)
    (fun t ht => by simpa using hineq ht)
    hm hmcont (by simpa using hnorm) hA hAcont hApos hA0 hmA hs hsT h2s
  have hVpos : 0 < radialVolume (hypModelA 1 1) s := by
    rw [hypModelA_one_one_volume]
    exact sub_pos.mpr ((Real.one_lt_cosh).mpr (ne_of_gt hs))
  have hratio : radialVolume (hypModelA 1 1) (2 * s) / radialVolume (hypModelA 1 1) s
      = 2 * (Real.cosh s + 1) := by
    rw [hypModelA_one_one_doubling]
    field_simp [ne_of_gt hVpos]
  calc radialVolume A (2 * s)
      ≤ (radialVolume (hypModelA 1 1) (2 * s) / radialVolume (hypModelA 1 1) s) *
          radialVolume A s := h
    _ = 2 * (Real.cosh s + 1) * radialVolume A s := by rw [hratio]

end Poincare.L4.Compactness
