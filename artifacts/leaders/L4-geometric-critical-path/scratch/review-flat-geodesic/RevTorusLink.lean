/-
Adversarial-review scratch file #2 (reviewer-owned, NOT part of the release tree).

Independent check of the **cross-module claims** of M3
(`Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean`):

  * the flat-torus link `torusA t = 8 * J t` (with a *locally defined* radial model,
    so this file does NOT import M3);
  * the exact domain of validity of that identity, including the failure for `t > 1/2`
    (outside the injectivity radius the profile saturates to `0`) and the value at the
    endpoint `t = 1/2`;
  * the D12 scalar statement `JacobiSolutionOn 0 (t ↦ t) 1 0 0 T`, re-derived here;
  * `euclidModelA 1 = id`;
  * the substantive reading of M3's docstring claim that the scalar profile `t ↦ t` is
    "consumed by `euclid_volume_doubling_of_ricci_nonneg`": we instantiate that theorem
    with `d = 1`, `A = fun t => t`, `m = fun t => t⁻¹`, `k = 0` and prove every hypothesis.

Imports: FlatTorusGrowth + D12 ModelEuclidean/RicciToDoubling.  **No import of M3.**
-/
import Poincare.L4.Compactness.FlatTorusGrowth
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.L4.Compactness.RicciToDoubling

open Set Metric
open MeasureTheory
open scoped Topology

noncomputable section

namespace RevTorusLink

open Poincare.D12.ComparisonGeodesics

/-- Reviewer's own local copy of the radial model `J v t = t * v` (M3 is not imported). -/
def revRadialJacobi (v : ℝ) (t : ℝ) : ℝ := t * v

/-- **(i) The torus link on the closed interval `[0, 1/2]`** — strictly stronger domain than
M3's `Ioc 0 (1/2)`; note it already follows from FlatTorusGrowth's own
`torusA_eq_of_mem_Icc`, with no new input. -/
theorem rev_torusA_eq_eight_mul (t : ℝ) (ht : t ∈ Icc 0 (1 / 2)) :
    Poincare.L4.Compactness.torusA t = 8 * revRadialJacobi 1 t := by
  rw [Poincare.L4.Compactness.torusA_eq_of_mem_Icc ht]
  simp [revRadialJacobi]

/-- **(ii) Endpoint check**: `torusA (1/2) = 4 = 8 * (1/2)`. -/
theorem rev_torusA_half :
    Poincare.L4.Compactness.torusA (1 / 2) = 4 ∧
      8 * revRadialJacobi 1 (1 / 2) = 4 := by
  constructor
  · rw [Poincare.L4.Compactness.torusA_half]
  · norm_num [revRadialJacobi]

/-- **(iii) The identity also holds at `t = 0`**, so M3's `Ioc 0 (1/2)` is *sufficient*
but not the exact domain of validity. -/
theorem rev_torusA_zero :
    Poincare.L4.Compactness.torusA 0 = 8 * revRadialJacobi 1 0 := by
  rw [Poincare.L4.Compactness.torusA_zero]
  simp [revRadialJacobi]

/-- **(iv) The identity FAILS for every `t > 1/2`**: the profile saturates to `0` while
`8 * J t = 8 t > 0`.  This is exactly why M3 must restrict the domain. -/
theorem rev_torusA_ne_eight_of_gt {t : ℝ} (ht : 1 / 2 < t) :
    Poincare.L4.Compactness.torusA t ≠ 8 * revRadialJacobi 1 t := by
  rw [Poincare.L4.Compactness.torusA_of_gt ht, revRadialJacobi]
  have hpos : 0 < 8 * (t * 1) := by linarith
  exact ne_of_lt hpos

/-- **(v) Concrete failure witness at `t = 3/4`**: `0 ≠ 6`. -/
theorem rev_torusA_fails_at_three_quarters :
    Poincare.L4.Compactness.torusA (3 / 4) = 0 ∧ 8 * revRadialJacobi 1 (3 / 4) = 6 := by
  constructor
  · rw [Poincare.L4.Compactness.torusA_of_gt (by norm_num : (1 / 2 : ℝ) < 3 / 4)]
  · norm_num [revRadialJacobi]

/-- **(vi) The D12 scalar claim, re-derived independently** (same statement as M3's
`scalarRadialJacobiSolutionOn`, built from the D12 definition directly). -/
theorem rev_scalarRadialJacobiSolutionOn (T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => 0) (fun t : ℝ => t) (fun _ : ℝ => 1)
      (fun _ : ℝ => 0) 0 T where
  hasDerivAt_u := by
    intro t _
    simpa using hasDerivAtR_id t
  hasDerivAt_du := by
    intro t _
    exact hasDerivAtR_const 1 t
  eq_secondDeriv := by
    intro t _
    ring
  continuousOn_u := continuous_id.continuousOn
  continuousOn_du := continuous_const.continuousOn

/-- **(vii) `euclidModelA 1` is the identity function** (M3's `euclidModelA_one_eq`). -/
theorem rev_euclidModelA_one : euclidModelA 1 = fun t : ℝ => t := by
  funext t
  simp [euclidModelA]

/-- **(viii) The substantive content of M3's "profile consumed by the doubling chain"
claim**: the scalar radial Jacobi field `t ↦ t` really is an admissible `A` in
`euclid_volume_doubling_of_ricci_nonneg` with `d = 1`, `m t = t⁻¹`, `k ≡ 0`, `C = 0`. -/
theorem rev_id_is_doubling_profile {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) (h2s : 2 * s ≤ T) :
    radialVolume (fun t : ℝ => t) (2 * s) ≤ 2 ^ (1 + 1) * radialVolume (fun t : ℝ => t) s :=
  Poincare.L4.Compactness.euclid_volume_doubling_of_ricci_nonneg (d := 1) (T := T) (C := 0) (t₀ := T)
    (by norm_num) hT le_rfl hT le_rfl
    (k := fun _ => 0) (m := fun t : ℝ => t⁻¹) (dm := fun t : ℝ => -(t ^ 2)⁻¹)
    (A := fun t : ℝ => t) (dA := fun _ => 1)
    (fun _ _ => le_rfl)
    (fun t ht => by
      have h : (t⁻¹) ^ 2 = (t ^ 2)⁻¹ := inv_pow t 2
      rw [h]
      norm_num)
    (fun t ht => hasDerivAtR_inv (ne_of_gt ht.1))
    (continuousOn_id.inv₀ (fun x hx => ne_of_gt hx.1))
    (fun t ht => by
      simp [one_div])
    (fun t _ => hasDerivAtR_id t)
    continuous_id.continuousOn
    (fun t ht => ht.1)
    rfl
    (fun t ht => by rw [one_div])
    hs hsT h2s

/-- **(ix) The doubling inequality is an equality on this profile** (`V (2s) = 2s²`,
`2^(1+1) * V s = 2s²`), which confirms the profile is the sharp Euclidean `d = 1` one. -/
theorem rev_id_doubling_values (s : ℝ) :
    radialVolume (fun t : ℝ => t) (2 * s) = 2 * s ^ 2 ∧
      2 ^ (1 + 1) * radialVolume (fun t : ℝ => t) s = 2 * s ^ 2 := by
  constructor
  · rw [radialVolume, integral_id]
    ring
  · rw [radialVolume, integral_id]
    ring

end RevTorusLink
