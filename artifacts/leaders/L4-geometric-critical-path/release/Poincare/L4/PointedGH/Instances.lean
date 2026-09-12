/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task L4-child-pointed-gh-transport)
-/
import Poincare.L4.PointedGH.Family
import Poincare.D12.GeometricCompactness.GridFamily

/-!
# Poincare.L4.PointedGH.Instances

**Non-vacuous Euclidean and grid instantiations of the pointed GH coupling interface.**

The point of this file is to exhibit inhabitants of `PointedGHCoupling` on genuine metric
spaces, so that the interface of `Poincare.L4.PointedGH.Family` is not vacuous, and to run the
D12-consuming assembly on the grid family.

## Instantiation E — shrinking closed balls in the Euclidean plane

`euclidX n` is the closed ball of radius `1 + 1/(n+1)` around the origin of
`EuclideanSpace ℝ (Fin 2)`, with basepoint `0`; the limit is the unit closed ball, basepoint `0`.
The coupling space is the plane itself and both embeddings are the subtype inclusions.  The
Hausdorff bound `hausdorffDist (closedBall 0 r) (closedBall 0 1) ≤ r - 1` (for `r ≥ 1`) is proved
by the radial contraction `x ↦ r⁻¹ • x`.  The spaces genuinely vary (radii `1 + 1/(n+1) → 1`);
both basepoints are exactly `0`.

## Instantiation G — the D12 unit-square grids

`gridX n` is D12's mesh-`1/(n+1)` grid `gridSpace (n+1)` with basepoint `(0,0)`, and the limit is
D12's Euclidean unit square `squareSpace` with basepoint `(0,0)`; the coupling space is the plane
and the embeddings are the subtype inclusions.  The Hausdorff bound is D12's
`hausdorffDist_grid_square_le`.  This family has **unbounded cardinality** `(n+2)²` (D12's
`gridSpace_card`), so the instance is nondegenerate in the sense that no finite-points bound is
available.  `grid_pointed_subseq` then applies the D12-consuming assembly
`pointed_subseq_of_familyBounds` to this family end to end.

Both instantiations exhibit the full explicit data: coupling spaces, isometric embeddings,
positive rates tending to zero, Hausdorff compatibility and basepoint compatibility.

## Main declarations

* `hausdorffDist_closedBall_le`
* `euclideanPointedCoupling`, `euclideanPointedCoupling_nonempty`
* `euclidean_ghDist_tendsto`, `euclidean_basepoint_tendsto`
* `gridPointedCoupling`, `gridPointedCoupling_nonempty`
* `grid_ghDist_tendsto`, `grid_basepoint_tendsto`
* `grid_pointed_subseq`
* `euclidX_basepoint_radius`, `gridX_card` (non-degeneracy witnesses)
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

noncomputable section

namespace Poincare.L4.PointedGH

open Poincare.D12.GeometricCompactness

/-! ## Metric lemma: Hausdorff distance of concentric closed balls -/

/-- **Concentric closed balls are Hausdorff-close.**  For `1 ≤ r` in the Euclidean plane,
`hausdorffDist (closedBall 0 r) (closedBall 0 1) ≤ r - 1`: the radial contraction
`x ↦ r⁻¹ • x` maps the radius-`r` ball into the unit ball and moves each point by at most
`r - 1`. -/
theorem hausdorffDist_closedBall_le (r : ℝ) (hr : 1 ≤ r) :
    hausdorffDist (Metric.closedBall (0 : E2) r) (Metric.closedBall (0 : E2) 1) ≤ r - 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hrinv_nonneg : 0 ≤ r⁻¹ := inv_nonneg.2 (le_of_lt hr0)
  have hrinv_le : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  refine hausdorffDist_le_of_mem_dist (sub_nonneg.2 hr) ?_ ?_
  · intro x hx
    have hxnorm : ‖x‖ ≤ r := by simpa [dist_eq_norm] using hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hrinv_nonneg]
      calc r⁻¹ * ‖x‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hxnorm hrinv_nonneg
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hr0)
    · rw [dist_eq_norm]
      have hsub : x - r⁻¹ • x = (1 - r⁻¹) • x := by rw [sub_smul, one_smul]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hrinv_le)]
      calc (1 - r⁻¹) * ‖x‖ ≤ (1 - r⁻¹) * r :=
            mul_le_mul_of_nonneg_left hxnorm (sub_nonneg.2 hrinv_le)
        _ = r - 1 := by
            rw [sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hr0)]
  · intro y hy
    have hynorm : ‖y‖ ≤ 1 := by simpa [dist_eq_norm] using hy
    refine ⟨y, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    · rw [dist_self]
      exact sub_nonneg.2 hr

/-! ## Instantiation E: shrinking closed balls in the Euclidean plane -/

/-- The closed ball of radius `r` around the origin of the Euclidean plane, as a metric space. -/
abbrev euclidBall (r : ℝ) : Type := {x : E2 // x ∈ Metric.closedBall (0 : E2) r}

instance instEuclidBallMetricSpace (r : ℝ) : MetricSpace (euclidBall r) := Subtype.metricSpace

instance instEuclidBallCompactSpace (r : ℝ) : CompactSpace (euclidBall r) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : E2) r)

/-- The origin as a point of the closed ball of radius `r` (for `0 ≤ r`). -/
def euclidBallOrigin (r : ℝ) (hr : 0 ≤ r) : euclidBall r :=
  ⟨0, by simpa [Metric.mem_closedBall] using hr⟩

/-- The approximating Euclidean ball of radius `1 + 1/(n+1)`. -/
abbrev euclidX (n : ℕ) : Type := euclidBall (1 + 1 / ((n : ℝ) + 1))

/-- The basepoint of the approximating Euclidean ball. -/
def euclidx (n : ℕ) : euclidX n :=
  euclidBallOrigin _ (by positivity)

/-- The Euclidean limit: the unit closed ball. -/
abbrev euclidLim : Type := euclidBall 1

/-- The basepoint of the Euclidean limit. -/
def euclidxLim : euclidLim := euclidBallOrigin _ (by norm_num)

instance instEuclidXNonempty (n : ℕ) : Nonempty (euclidX n) := ⟨euclidx n⟩

instance instEuclidLimNonempty : Nonempty euclidLim := ⟨euclidxLim⟩

/-- **Instantiation E.**  Explicit compatible-coupling data for the shrinking Euclidean balls:
coupling space the plane, subtype inclusions, rate `2/(n+1)`, Hausdorff compatibility from
`hausdorffDist_closedBall_le`, basepoint compatibility since both basepoints are the origin. -/
def euclideanPointedCoupling :
    PointedGHCoupling euclidX euclidx euclidLim euclidxLim where
  Z := fun _ => E2
  instZ := fun _ => inferInstance
  Φ := fun _ => Subtype.val
  Ψ := fun _ => Subtype.val
  isometry_Φ := fun _ => isometry_subtype_coe
  isometry_Ψ := fun _ => isometry_subtype_coe
  ε := fun n => 2 / ((n : ℝ) + 1)
  ε_pos := fun n => by positivity
  ε_tendsto := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  hausdorff_lt := fun n => by
    have hr : (1 : ℝ) ≤ 1 + 1 / ((n : ℝ) + 1) :=
      le_add_of_nonneg_right (by positivity)
    have h := hausdorffDist_closedBall_le (1 + 1 / ((n : ℝ) + 1)) hr
    have hsub : hausdorffDist (range (Subtype.val : euclidX n → E2))
        (range (Subtype.val : euclidLim → E2)) =
        hausdorffDist (Metric.closedBall (0 : E2) (1 + 1 / ((n : ℝ) + 1)))
          (Metric.closedBall (0 : E2) 1) := by
      rw [Subtype.range_coe, Subtype.range_coe]
    rw [hsub]
    calc hausdorffDist (Metric.closedBall (0 : E2) (1 + 1 / ((n : ℝ) + 1)))
          (Metric.closedBall (0 : E2) 1) ≤ (1 + 1 / ((n : ℝ) + 1)) - 1 := h
      _ = 1 / ((n : ℝ) + 1) := by ring
      _ < 2 / ((n : ℝ) + 1) :=
          div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) (by positivity)
  basepoint_lt := fun n => by
    have h : (0 : ℝ) < 2 / ((n : ℝ) + 1) := by positivity
    simpa [euclidx, euclidxLim, euclidBallOrigin] using h

/-- The Euclidean shrinking-ball family inhabits the explicit pointed-coupling interface. -/
theorem euclideanPointedCoupling_nonempty :
    Nonempty (PointedGHCoupling euclidX euclidx euclidLim euclidxLim) :=
  ⟨euclideanPointedCoupling⟩

/-- Unpointed convergence of the Euclidean shrinking balls, from the explicit pointed data. -/
theorem euclidean_ghDist_tendsto :
    Tendsto (fun n => ghDist (euclidX n) euclidLim) atTop (𝓝 0) :=
  euclideanPointedCoupling.ghDist_tendsto

/-- Basepoint convergence of the Euclidean shrinking balls, from the explicit pointed data. -/
theorem euclidean_basepoint_tendsto :
    Tendsto (fun n => dist ((euclidx n : E2)) (euclidxLim : E2)) atTop (𝓝 0) :=
  euclideanPointedCoupling.basepoint_tendsto

/-! ## Instantiation G: the D12 unit-square grids -/

/-- The mesh-`1/(n+1)` D12 grid as the approximating space. -/
abbrev gridX (n : ℕ) : Type := gridSpace (n + 1)

/-- The `(0,0)` basepoint of the approximating grid. -/
def gridx (n : ℕ) : gridX n := ⟨0, zero_mem_gridSet (n + 1)⟩

/-- The D12 Euclidean unit square as the limit space. -/
abbrev gridLim : Type := squareSpace

/-- The `(0,0)` basepoint of the limit square. -/
def gridxLim : gridLim := ⟨0, zero_mem_unitSquare⟩

instance instGridXNonempty (n : ℕ) : Nonempty (gridX n) := ⟨gridx n⟩

instance instGridLimNonempty : Nonempty gridLim := ⟨gridxLim⟩

/-- **Instantiation G.**  Explicit compatible-coupling data for the D12 unit-square grids:
coupling space the plane, subtype inclusions, rate `√2/(n+1) + 1/(n+1)`, Hausdorff compatibility
from D12's `hausdorffDist_grid_square_le`, basepoint compatibility since both basepoints are the
origin.  The members have unbounded cardinality `(n+2)²` (D12's `gridSpace_card`). -/
def gridPointedCoupling : PointedGHCoupling gridX gridx gridLim gridxLim where
  Z := fun _ => E2
  instZ := fun _ => inferInstance
  Φ := fun _ => Subtype.val
  Ψ := fun _ => Subtype.val
  isometry_Φ := fun _ => isometry_subtype_coe
  isometry_Ψ := fun _ => isometry_subtype_coe
  ε := fun n => Real.sqrt 2 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)
  ε_pos := fun n => by positivity
  ε_tendsto := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.sqrt 2)
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h1.add h2
  hausdorff_lt := fun n => by
    have h := hausdorffDist_grid_square_le (n + 1) (by positivity)
    have hsub : hausdorffDist (range (Subtype.val : gridX n → E2))
        (range (Subtype.val : gridLim → E2)) =
        hausdorffDist (gridSet (n + 1)) unitSquare := by
      rw [Subtype.range_coe, Subtype.range_coe]
    rw [hsub]
    calc hausdorffDist (gridSet (n + 1)) unitSquare ≤ Real.sqrt 2 / ((n : ℝ) + 1) := by
          simpa [Nat.cast_add, Nat.cast_one] using h
      _ < Real.sqrt 2 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) :=
          lt_add_of_pos_right _ (by positivity)
  basepoint_lt := fun n => by
    have h : (0 : ℝ) < Real.sqrt 2 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by positivity
    simpa [gridx, gridxLim] using h

/-- The grid family inhabits the explicit pointed-coupling interface. -/
theorem gridPointedCoupling_nonempty :
    Nonempty (PointedGHCoupling gridX gridx gridLim gridxLim) :=
  ⟨gridPointedCoupling⟩

/-- Unpointed convergence of the grids to the unit square, from the explicit pointed data
(compare D12's `grid_gh_tendsto_square`, which proves the same convergence directly). -/
theorem grid_ghDist_tendsto :
    Tendsto (fun n => ghDist (gridX n) gridLim) atTop (𝓝 0) :=
  gridPointedCoupling.ghDist_tendsto

/-- Basepoint convergence of the grids to the unit square, from the explicit pointed data. -/
theorem grid_basepoint_tendsto :
    Tendsto (fun n => dist ((gridx n : E2)) (gridxLim : E2)) atTop (𝓝 0) :=
  gridPointedCoupling.basepoint_tendsto

/-- **End-to-end application of the D12-consuming assembly to the grid family.**  The unpointed
grid family is totally bounded in `GHSpace` (D12's `gridFamily_totallyBounded`), so the pointed
assembly produces a subsequence, a limit in the closure, a limit basepoint, and the explicit
compatible-coupling data — with no pointed convergence hypothesis assumed. -/
theorem grid_pointed_subseq :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ closure {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)} ∧ StrictMono φ ∧
        Nonempty (PointedGHCoupling (fun k => gridX (φ k)) (fun k => gridx (φ k)) a.Rep xinf) :=
  pointed_subseq_of_familyBounds gridFamily_totallyBounded gridx
    (fun n => subset_closure ⟨n, rfl⟩)

/-! ## Non-degeneracy witnesses for the two instantiations -/

/-- **Non-degeneracy of the Euclidean instantiation.**  For every `n` the approximating ball
contains a point at distance exactly `1 + 1/(n+1) > 1` from the basepoint, while every point of
the limit ball is at distance at most `1` from its basepoint.  So the pointed spaces genuinely
vary: the maximal distance from the basepoint strictly decreases to `1`.  The explicit witness is
the radial point `(1 + 1/(n+1)) • e₀` along the first standard basis vector `e₀`. -/
theorem euclidX_basepoint_radius (n : ℕ) :
    (∃ x : euclidX n, dist (x : E2) (euclidx n : E2) = 1 + 1 / ((n : ℝ) + 1)) ∧
      (∀ y : euclidLim, dist (y : E2) (euclidxLim : E2) ≤ 1) ∧
      1 < 1 + 1 / ((n : ℝ) + 1) := by
  have hr : 0 ≤ 1 + 1 / ((n : ℝ) + 1) := by positivity
  have hnorm : ‖(PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E2)‖ = 1 := by simp
  have hsmul : ‖(1 + 1 / ((n : ℝ) + 1)) • (PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E2)‖ =
      1 + 1 / ((n : ℝ) + 1) := by
    rw [norm_smul, hnorm, mul_one, Real.norm_of_nonneg hr]
  have hmem : (1 + 1 / ((n : ℝ) + 1)) • (PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E2) ∈
      Metric.closedBall (0 : E2) (1 + 1 / ((n : ℝ) + 1)) := by
    rw [Metric.mem_closedBall, dist_zero_right, hsmul]
  refine ⟨⟨⟨_, hmem⟩, ?_⟩, ?_, ?_⟩
  · have h1 : ((⟨_, hmem⟩ : euclidX n) : E2) =
        (1 + 1 / ((n : ℝ) + 1)) • (PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E2) := rfl
    have h2 : ((euclidx n : euclidX n) : E2) = 0 := rfl
    rw [dist_eq_norm, h1, h2, sub_zero]
    exact hsmul
  · intro y
    have h2 : ((euclidxLim : euclidLim) : E2) = 0 := rfl
    have hy : ‖(y : E2)‖ ≤ 1 := by
      have h := y.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact h
    rw [dist_eq_norm, h2, sub_zero]
    exact hy
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **Non-degeneracy of the grid instantiation.**  The `n`-th grid has `(n+2)²` points (D12's
`gridSpace_card`), so the cardinalities are unbounded and the instance is not a finite-points
degeneracy. -/
theorem gridX_card (n : ℕ) : Fintype.card (gridX n) = (n + 2) * (n + 2) := by
  simpa [gridX, Nat.add_assoc] using gridSpace_card (n + 1)

end Poincare.L4.PointedGH

end
