/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — downstream consumption of the Jacobi/Rauch bridge

This file continues `Poincare.L4.GeodesicComparison.RauchBridge` and makes the
"constructed input ⟶ downstream checked use" chain explicit:

* `logDeriv_continuousOn` — general (proved): the logarithmic derivative `u'/u` of a
  positive Jacobi solution is continuous on `(0,T]`.  (Factored out of the two Rauch
  theorems so that both directions share the same constructed input.)
* `rauch_lower_of_jacobi` — **conditional** (proved): **Rauch II lower comparison** for a
  genuine scalar Jacobi solution with `k ≤ 0`: `1/t ≤ u' t/u t` on `(0,T)`.  This is the
  mirrored direction of `rauch_upper_of_jacobi` and consumes the *same* constructed
  Euclidean normalization `euclideanNormalizedOn_of_jacobi` through the D12 mirrored
  singular engine `riccati_ge_of_singular_normalization`.
* `jacobi_bishopGromovVolumeRatio` — **conditional** (proved): the Bishop–Gromov volume
  ratio conclusion for the cumulative radial volumes,
  `V R / V̄ R ≤ V r / V̄ r`, obtained by consuming `jacobi_areaRatio_antitone` (this
  invocation) through the D12 theorem `volumeRatio_antitone`.  `V = ∫₀ᵗ u` is the
  cumulative density of the Jacobi solution and `V̄ = ∫₀ᵗ t` the Euclidean model.
* `sinh_half_le_one` — general (proved): the explicit numerical bound used for the
  hyperbolic witness.
* `sinh_jacobiSolution`, `sinh_rauch_lower_witness` — **model** (proved): the explicit
  hyperbolic witness `u = sinh`, `k = -1` on `(0,1/4)` satisfies every hypothesis and
  yields the genuinely nontrivial inequality `1/t ≤ cosh t/sinh t`.
* `sin_volumeRatio_witness` — **model** (proved): the sine model satisfies the
  Bishop–Gromov volume-ratio conclusion.

The geometric identification of `u` with the area density of geodesic spheres is **not**
claimed; all statements here are analytic comparison statements about a scalar Jacobi
solution.  See the L4 result card for the semantic classification.
-/
import Poincare.L4.GeodesicComparison.RauchBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics

/-! ## 1. Continuity of the logarithmic derivative (shared constructed input) -/

/-- **Continuity of `u'/u` on `(0,T]`.**  If `u` is continuous on `[0,T]`, `u'` is
continuous on `[0,T]` and `u > 0` on `(0,T]`, then `t ↦ u' t/u t` is continuous on
`(0,T]`.  This is the continuity hypothesis consumed by the singular Riccati engine. -/
theorem logDeriv_continuousOn {k u du ddu : ℝ → ℝ} {T : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) :
    ContinuousOn (fun t => du t / u t) (Ioc 0 T) := by
  have hdu' : ContinuousOn du (Ioc 0 T) :=
    h.continuousOn_du.mono (fun x hx => ⟨hx.1.le, hx.2⟩)
  have hu' : ContinuousOn u (Ioc 0 T) :=
    h.continuousOn_u.mono (fun x hx => ⟨hx.1.le, hx.2⟩)
  exact hdu'.div hu' (fun x hx => ne_of_gt (hpos x hx))

/-! ## 2. Rauch II: the lower comparison from the mirrored singular engine -/

/-- **Rauch II (lower) comparison for a scalar Jacobi solution.**  If `k ≤ 0` on `(0,T)`,
`u'' + k u = 0`, `u > 0` on `(0,T]`, `u 0 = 0`, `u' 0 = 1`, `|u''| ≤ B` on `(0,T)` with
`B ≥ 0`, and `0 < t₀ ≤ T` with `B t₀ ≤ 1/2`, then `1/t ≤ u' t/u t` for every
`t ∈ (0,T)`.  The proof consumes the constructed normalization
`euclideanNormalizedOn_of_jacobi` and the constructed Riccati equality
`riccati_identity_of_jacobi` through the *mirrored* D12 singular engine
`riccati_ge_of_singular_normalization`; the Euclidean model `m̄ = 1/t` is again the
comparison solution. -/
theorem rauch_lower_of_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hk : ∀ t ∈ Ioo 0 T, k t ≤ 0) :
    ∀ t ∈ Ioo 0 T, 1 / t ≤ du t / u t := by
  have hid := riccati_identity_of_jacobi h hpos
  have hnorm := euclideanNormalizedOn_of_jacobi h hdducont hBnn hB hu0 hdu0 ht₀ ht₀T hBt₀
  have hmain := riccati_ge_of_singular_normalization (d := 1) (T := T) (C := 4 * B)
    (t₀ := t₀) (k := k) (kbar := fun _ => 0) (m := fun t => du t / u t)
    (dm := fun t => (ddu t * u t - du t ^ 2) / u t ^ 2)
    (mbar := euclidModelM 1) (dmbar := euclidModelDm 1)
    (by norm_num) hT (by positivity) ht₀ ht₀T
    (fun t ht => le_of_eq (hid.2 t ht).symm)
    (fun t ht => by
      simpa using euclidModelM_riccati (d := 1) (ne_of_gt ht.1)
        (by norm_num : ((1 : ℕ) : ℝ) ≠ 0))
    (fun t ht => hk t ht)
    (fun t ht => hid.1 t ht)
    (fun t ht => euclidModelM_hasDerivAt (d := 1) (ne_of_gt ht.1))
    (logDeriv_continuousOn h hpos) euclidModelM_contOn hnorm
    (by simpa using euclidModelM_normalized (d := 1) (C := 4 * B) (t₀ := t₀) (by positivity))
  intro t ht
  have := hmain ht
  simpa [euclidModelM] using this

/-! ## 3. Bishop–Gromov volume ratio for the Jacobi density -/

/-- **Bishop–Gromov volume ratio from Jacobi data.**  Under the hypotheses of
`jacobi_areaRatio_antitone`, the cumulative radial volumes satisfy
`V R / V̄ R ≤ V r / V̄ r` for `0 < r ≤ R ≤ T`, where `V = ∫₀ᵗ u` is the cumulative density
of the Jacobi solution and `V̄ = ∫₀ᵗ t^1` is the Euclidean model.  This consumes the
area-ratio theorem of this invocation through the D12 theorem `volumeRatio_antitone`; the
geometric identification of `V` with a geodesic-ball volume is not claimed. -/
theorem jacobi_bishopGromovVolumeRatio {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hk : ∀ t ∈ Ioo 0 T, 0 ≤ k t) :
    ∀ ⦃r : ℝ⦄, r ∈ Ioc 0 T → ∀ ⦃R : ℝ⦄, R ∈ Ioc 0 T → r ≤ R →
      radialVolume u R / radialVolume (euclidModelA 1) R
        ≤ radialVolume u r / radialVolume (euclidModelA 1) r := by
  exact volumeRatio_antitone hT h.continuousOn_u euclidModelA_contOn hu0
    (euclidModelA_zero (d := 1) (by norm_num))
    (fun t ht => euclidModelA_pos ht)
    (by simpa [euclidModelA] using
      jacobi_areaRatio_antitone hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hpos hk)

/-! ## 4. Non-vacuity: the hyperbolic witness for Rauch II -/

/-- Explicit numerical bound used by the hyperbolic witness: `sinh (1/2) ≤ 1`. -/
theorem sinh_half_le_one : Real.sinh (1 / 2) ≤ 1 := by
  rw [Real.sinh_eq]
  have hexp2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hexp2lt : Real.exp (1 / 2) < 2 := by
    nlinarith [Real.exp_pos (1 / 2), Real.exp_one_lt_three, hexp2,
      sq_nonneg (Real.exp (1 / 2) - 2)]
  have hnum : Real.exp (1 / 2) - Real.exp (-(1 / 2)) ≤ Real.exp (1 / 2) := by
    linarith [Real.exp_pos (-(1 / 2))]
  linarith

/-- The hyperbolic model `u = sinh`, `k = -1` is a Jacobi solution on `(0,1/4)` with
`u 0 = 0`, `u' 0 = 1`. -/
theorem sinh_jacobiSolution : JacobiSolutionOn (fun _ : ℝ => -1) Real.sinh Real.cosh
    (fun t => Real.sinh t) 0 (1 / 4) where
  hasDerivAt_u := by
    intro t ht
    simpa using Real.hasDerivAt_sinh t
  hasDerivAt_du := by
    intro t ht
    simpa using Real.hasDerivAt_cosh t
  eq_secondDeriv := by
    intro t ht
    ring
  continuousOn_u := Real.continuous_sinh.continuousOn
  continuousOn_du := Real.continuous_cosh.continuousOn

/-- **Rauch II witness.**  The hyperbolic model satisfies every hypothesis of
`rauch_lower_of_jacobi` with `B = 2`, `t₀ = 1/4`, and the conclusion is the genuinely
nontrivial inequality `1/t ≤ cosh t/sinh t` on `(0,1/4)`, equivalently `tanh t ≤ t`. -/
theorem sinh_rauch_lower_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 4), 1 / t ≤ Real.cosh t / Real.sinh t := by
  have hmain := rauch_lower_of_jacobi (T := 1 / 4) (B := 2) (t₀ := 1 / 4)
    (k := fun _ : ℝ => -1) (u := Real.sinh) (du := Real.cosh) (ddu := fun t => Real.sinh t)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    sinh_jacobiSolution
    (by fun_prop)
    (fun t ht => by
      have hmono : Real.sinh t ≤ Real.sinh (1 / 2) :=
        Real.sinh_le_sinh.mpr (by linarith [ht.2])
      have hnonneg : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht.1.le
      rw [abs_of_nonneg hnonneg]
      linarith [sinh_half_le_one])
    (by simp) (by simp)
    (fun t ht => Real.sinh_pos_iff.mpr ht.1)
    (fun t ht => by norm_num)
  intro t ht
  exact hmain t ht

/-! ## 5. Non-vacuity: the sine model for the volume ratio -/

/-- **Volume-ratio witness.**  The sine model satisfies every hypothesis of
`jacobi_bishopGromovVolumeRatio`, giving the Bishop–Gromov ratio inequality for the
cumulative volume of `sin` against the Euclidean model `t ↦ t` on `(0,1/2]`. -/
theorem sin_volumeRatio_witness :
    ∀ ⦃r : ℝ⦄, r ∈ Ioc 0 (1 / 2) → ∀ ⦃R : ℝ⦄, R ∈ Ioc 0 (1 / 2) → r ≤ R →
      radialVolume Real.sin R / radialVolume (euclidModelA 1) R
        ≤ radialVolume Real.sin r / radialVolume (euclidModelA 1) r := by
  have hmain := jacobi_bishopGromovVolumeRatio (T := 1 / 2) (B := 1) (t₀ := 1 / 2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    sin_jacobiSolution
    (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro r hr R hR hrR
  exact hmain hr hR hrR

end Poincare.L4.GeodesicComparison

#print axioms Poincare.L4.GeodesicComparison.logDeriv_continuousOn
#print axioms Poincare.L4.GeodesicComparison.rauch_lower_of_jacobi
#print axioms Poincare.L4.GeodesicComparison.jacobi_bishopGromovVolumeRatio
#print axioms Poincare.L4.GeodesicComparison.sinh_rauch_lower_witness
#print axioms Poincare.L4.GeodesicComparison.sin_volumeRatio_witness
