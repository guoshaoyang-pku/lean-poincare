/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-geometric-compactness)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Poincare.D12.GeometricCompactness.Criterion

/-!
# Poincare.D12.GeometricCompactness.GridFamily

A nondegenerate model family for Gromov's compactness criterion: the finite
Euclidean grids `{i/m, j/m : 0 ≤ i, j ≤ m} ⊆ [0,1]²` with the induced
Euclidean metric, viewed in mathlib's Gromov–Hausdorff space `GHSpace`.

The family is genuinely nontrivial for the criterion: its members have
**unbounded cardinality** `(m+1)²`, so no "at most N points" bound is
available; compactness/precompactness must come from the covering-number
mechanism.  We prove:

* `square_grid_dense`: for `0 < m`, every point of the closed unit square of
  `EuclideanSpace ℝ (Fin 2)` is within `√2/m` of a mesh-`1/m` grid vertex;
* `gridUniformCover`: for every `ε > 0` there is `K = (⌈4/ε⌉₊ + 1)²` such
  that **every** grid space (all meshes at once) is covered by `≤ K`
  `ε`-balls — the covering numbers are uniform while the cardinalities are
  unbounded;
* `gridSpace_diam_le`: all grid spaces have diameter `≤ √2`;
* `grid_gh_tendsto_square`: the sequence of grids `gridGH (n+1)` converges
  in `ghDist` to the Euclidean unit square — an explicit
  convergence/subsequence witness with a named limit;
* `gridFamily_infinite`: the family is infinite (cardinality `(m+1)²`,
  isometry classes of different cardinalities are distinct);
* `gridFamily_totallyBounded` / `gridFamily_closure_isCompact` /
  `gridFamily_subseq`: the family is totally bounded in `GHSpace`, its
  closure is compact, and every sequence of members has a strictly monotone
  reindexing converging in `ghDist`.

This is the *model* level: the spaces are genuine Euclidean metric spaces
(no fake metrics), but the family is Euclidean/flat — curvature bounds play
no role here, which is exactly the gap that the Cheeger–Gromov frontier
(`Poincare.D12.GeometricCompactness.Frontier`) records.
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

set_option maxHeartbeats 800000

noncomputable section

namespace Poincare.D12.GeometricCompactness

/-- The Euclidean plane with the standard L² metric. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The point `(a, b)` of the Euclidean plane. -/
def mk2 (a b : ℝ) : E2 :=
  WithLp.toLp 2 fun k : Fin 2 => if k = 0 then a else b

@[simp] theorem mk2_ofLp_zero (a b : ℝ) : (mk2 a b).ofLp 0 = a := by
  simp [mk2]

@[simp] theorem mk2_ofLp_one (a b : ℝ) : (mk2 a b).ofLp 1 = b := by
  simp [mk2, show (1 : Fin 2) ≠ 0 by norm_num]

/-- The closed unit square `[0,1]²` in the Euclidean plane. -/
def unitSquare : Set E2 := {x | ∀ k : Fin 2, 0 ≤ x.ofLp k ∧ x.ofLp k ≤ 1}

/-- The mesh-`1/m` grid vertices `{(i/m, j/m) | 0 ≤ i, j ≤ m}`. -/
def gridVertices (m : ℕ) : Finset E2 :=
  (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).image fun p =>
    mk2 ((p.1 : ℝ) / m) ((p.2 : ℝ) / m)

/-- The grid as a set of points. -/
abbrev gridSet (m : ℕ) : Set E2 := (gridVertices m : Set E2)

/-- The grid as a metric space (induced Euclidean metric). -/
abbrev gridSpace (m : ℕ) : Type := {x // x ∈ gridSet m}

/-- The unit square as a metric space (induced Euclidean metric). -/
abbrev squareSpace : Type := {x // x ∈ unitSquare}

/-- The `(0, 0)` grid point. -/
theorem zero_mem_gridSet (m : ℕ) : (0 : E2) ∈ gridSet m := by
  rw [gridSet]
  refine Finset.mem_image.2 ⟨(0 : Fin (m + 1) × Fin (m + 1)), by simp, ?_⟩
  apply PiLp.ext
  intro k
  simp [mk2]

/-- The `(0, 0)` point lies in the unit square. -/
theorem zero_mem_unitSquare : (0 : E2) ∈ unitSquare := by
  intro k
  constructor <;> norm_num

instance instGridSpaceMetricSpace (m : ℕ) : MetricSpace (gridSpace m) :=
  Subtype.metricSpace

instance instSquareSpaceMetricSpace : MetricSpace squareSpace :=
  Subtype.metricSpace

instance instGridSpaceFintype (m : ℕ) : Fintype (gridSpace m) :=
  Finset.Subtype.fintype (gridVertices m)

instance instGridSpaceNonempty (m : ℕ) : Nonempty (gridSpace m) :=
  ⟨⟨0, zero_mem_gridSet m⟩⟩

instance instGridSpaceCompactSpace (m : ℕ) : CompactSpace (gridSpace m) :=
  ⟨Set.finite_univ.isCompact⟩

/-- The unit square is compact (closed and bounded in the proper space `E2`). -/
theorem isCompact_unitSquare : IsCompact (unitSquare : Set E2) := by
  let coordClosed (k : Fin 2) : IsClosed {x : E2 | 0 ≤ x.ofLp k ∧ x.ofLp k ≤ 1} :=
    (isClosed_le (show Continuous fun _ : E2 => (0 : ℝ) from continuous_const)
        (PiLp.continuous_apply (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 2 => ℝ) k)).inter
      (isClosed_le (PiLp.continuous_apply (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 2 => ℝ) k)
        (show Continuous fun _ : E2 => (1 : ℝ) from continuous_const))
  have hclosed : IsClosed unitSquare := by
    rw [show unitSquare = {x : E2 | 0 ≤ x.ofLp 0 ∧ x.ofLp 0 ≤ 1} ∩
        {x : E2 | 0 ≤ x.ofLp 1 ∧ x.ofLp 1 ≤ 1} by
      ext x
      constructor
      · intro hx
        exact ⟨hx 0, hx 1⟩
      · rintro ⟨h0, h1⟩ k
        fin_cases k <;> assumption]
    exact (coordClosed 0).inter (coordClosed 1)
  refine (isCompact_closedBall (0 : E2) 2).of_isClosed_subset hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hnorm : ‖x‖ ≤ Real.sqrt 2 := by
    calc
      ‖x‖ = √(∑ k : Fin 2, ‖x.ofLp k‖ ^ 2) := EuclideanSpace.norm_eq x
      _ = √(‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2) := by rw [Fin.sum_univ_two]
      _ ≤ √(1 ^ 2 + 1 ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply add_le_add
        · rw [Real.norm_eq_abs]
          have h0 : |x.ofLp 0| ≤ 1 := by
            rw [abs_of_nonneg (hx 0).1]
            exact (hx 0).2
          exact sq_le_sq.2 (by simpa using h0)
        · rw [Real.norm_eq_abs]
          have h1 : |x.ofLp 1| ≤ 1 := by
            rw [abs_of_nonneg (hx 1).1]
            exact (hx 1).2
          exact sq_le_sq.2 (by simpa using h1)
      _ = Real.sqrt 2 := by
        rw [show (1 ^ 2 + 1 ^ 2 : ℝ) = 2 by norm_num]
  exact hnorm.trans (by
    rw [Real.sqrt_le_left (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num)

instance instSquareSpaceCompactSpace : CompactSpace squareSpace :=
  isCompact_iff_compactSpace.1 isCompact_unitSquare

instance instSquareSpaceNonempty : Nonempty squareSpace :=
  ⟨⟨0, zero_mem_unitSquare⟩⟩

/-- The mesh-`1/m` grid as a point of `GHSpace`. -/
abbrev gridGH (m : ℕ) : GHSpace := toGHSpace (gridSpace m)

/-- The Euclidean unit square as a point of `GHSpace`. -/
abbrev squareGH : GHSpace := toGHSpace squareSpace

/-- If `0 ≤ i ≤ m`, then `0 ≤ i/m ≤ 1`. -/
lemma coordBounds {i m : ℕ} (hi : i ≤ m) : 0 ≤ (i : ℝ) / m ∧ (i : ℝ) / m ≤ 1 := by
  by_cases hm : m = 0
  · subst hm
    constructor <;> norm_num
  · have hm' : 0 < (m : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hm')
    · rw [div_le_iff₀ hm']
      simpa using (Nat.cast_le.mpr hi : (i : ℝ) ≤ (m : ℝ))

/-- Every grid point has coordinates in `[0,1]`, i.e. lies in the unit square. -/
theorem gridPoint_coord (m : ℕ) {x : E2} (hx : x ∈ gridSet m) :
    x ∈ unitSquare := by
  intro k
  rcases Finset.mem_image.1 hx with ⟨p, hp, rfl⟩
  have h1 := coordBounds (m := m) (i := p.1) p.1.is_le
  have h2 := coordBounds (m := m) (i := p.2) p.2.is_le
  by_cases hk : k = 0
  · subst hk
    simpa [mk2] using h1
  · have hk' : k = 1 := by
      fin_cases k <;> simp at hk ⊢
    subst hk'
    simpa [mk2] using h2

/-- For `0 < m`, every point of the unit square is within `√2/m` of a mesh-`1/m` grid vertex. -/
theorem square_grid_dense {m : ℕ} (hm : 0 < m) {x : E2} (hx : x ∈ unitSquare) :
    ∃ v ∈ gridSet m, dist x v ≤ Real.sqrt 2 / m := by
  classical
  let i := ⌊x.ofLp 0 * m⌋₊
  let j := ⌊x.ofLp 1 * m⌋₊
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.2 hm
  have hi_le : i ≤ m := by
    have hle : x.ofLp 0 * (m : ℝ) ≤ (m : ℝ) := by
      have hx0 : x.ofLp 0 ≤ 1 := (hx 0).2
      have hmnn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      calc
        x.ofLp 0 * (m : ℝ) ≤ 1 * (m : ℝ) := mul_le_mul_of_nonneg_right hx0 hmnn
        _ = m := by norm_num
    have hfloor : Nat.floor (x.ofLp 0 * (m : ℝ)) ≤ Nat.floor ((m : ℝ)) := Nat.floor_mono hle
    simpa [i, Nat.floor_natCast] using hfloor
  have hj_le : j ≤ m := by
    have hle : x.ofLp 1 * (m : ℝ) ≤ (m : ℝ) := by
      have hx1 : x.ofLp 1 ≤ 1 := (hx 1).2
      have hmnn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      calc
        x.ofLp 1 * (m : ℝ) ≤ 1 * (m : ℝ) := mul_le_mul_of_nonneg_right hx1 hmnn
        _ = m := by norm_num
    have hfloor : Nat.floor (x.ofLp 1 * (m : ℝ)) ≤ Nat.floor ((m : ℝ)) := Nat.floor_mono hle
    simpa [j, Nat.floor_natCast] using hfloor
  have hcoord0 : |x.ofLp 0 - (i : ℝ) / m| ≤ 1 / m := by
    have h0 : 0 ≤ x.ofLp 0 * (m : ℝ) := mul_nonneg (hx 0).1 (Nat.cast_nonneg m)
    have hlow : 0 ≤ x.ofLp 0 - (i : ℝ) / m := by
      have hi_le' : (i : ℝ) ≤ x.ofLp 0 * (m : ℝ) := Nat.floor_le h0
      have hdiv : (i : ℝ) / m ≤ (x.ofLp 0 * (m : ℝ)) / m :=
        div_le_div_of_nonneg_right hi_le' (le_of_lt hm')
      have hrewrite : (x.ofLp 0 * (m : ℝ)) / m = x.ofLp 0 := by
        field_simp [hm'.ne']
      linarith
    have hhigh : x.ofLp 0 - (i : ℝ) / m ≤ 1 / m := by
      have hlt : x.ofLp 0 * (m : ℝ) < (i : ℝ) + 1 := Nat.lt_floor_add_one (x.ofLp 0 * (m : ℝ))
      have hsub : x.ofLp 0 * (m : ℝ) - (i : ℝ) ≤ 1 := by linarith
      have hdiv : (x.ofLp 0 * (m : ℝ) - (i : ℝ)) / m ≤ 1 / m :=
        div_le_div_of_nonneg_right hsub (le_of_lt hm')
      have hrewrite : (x.ofLp 0 * (m : ℝ) - (i : ℝ)) / m = x.ofLp 0 - (i : ℝ) / m := by
        field_simp [hm'.ne']
      rwa [← hrewrite]
    exact abs_le.2 ⟨by linarith, hhigh⟩
  have hcoord1 : |x.ofLp 1 - (j : ℝ) / m| ≤ 1 / m := by
    have h0 : 0 ≤ x.ofLp 1 * (m : ℝ) := mul_nonneg (hx 1).1 (Nat.cast_nonneg m)
    have hlow : 0 ≤ x.ofLp 1 - (j : ℝ) / m := by
      have hj_le' : (j : ℝ) ≤ x.ofLp 1 * (m : ℝ) := Nat.floor_le h0
      have hdiv : (j : ℝ) / m ≤ (x.ofLp 1 * (m : ℝ)) / m :=
        div_le_div_of_nonneg_right hj_le' (le_of_lt hm')
      have hrewrite : (x.ofLp 1 * (m : ℝ)) / m = x.ofLp 1 := by
        field_simp [hm'.ne']
      linarith
    have hhigh : x.ofLp 1 - (j : ℝ) / m ≤ 1 / m := by
      have hlt : x.ofLp 1 * (m : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one (x.ofLp 1 * (m : ℝ))
      have hsub : x.ofLp 1 * (m : ℝ) - (j : ℝ) ≤ 1 := by linarith
      have hdiv : (x.ofLp 1 * (m : ℝ) - (j : ℝ)) / m ≤ 1 / m :=
        div_le_div_of_nonneg_right hsub (le_of_lt hm')
      have hrewrite : (x.ofLp 1 * (m : ℝ) - (j : ℝ)) / m = x.ofLp 1 - (j : ℝ) / m := by
        field_simp [hm'.ne']
      rwa [← hrewrite]
    exact abs_le.2 ⟨by linarith, hhigh⟩
  let v : E2 := mk2 ((i : ℝ) / m) ((j : ℝ) / m)
  have hv_mem : v ∈ gridSet m := by
    rw [gridSet]
    refine Finset.mem_image.2 ⟨⟨⟨i, Nat.lt_succ_of_le hi_le⟩, ⟨j, Nat.lt_succ_of_le hj_le⟩⟩, by simp, ?_⟩
    rfl
  refine ⟨v, hv_mem, ?_⟩
  calc
    dist x v = √(∑ k : Fin 2, dist (x.ofLp k) (v.ofLp k) ^ 2) := EuclideanSpace.dist_eq x v
    _ = √(dist (x.ofLp 0) (v.ofLp 0) ^ 2 + dist (x.ofLp 1) (v.ofLp 1) ^ 2) := by
      rw [Fin.sum_univ_two]
    _ ≤ √((1 / m) ^ 2 + (1 / m) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply add_le_add
      · have h01 : |dist (x.ofLp 0) (v.ofLp 0)| ≤ (1 : ℝ) / m := by
          rw [Real.dist_eq]
          rw [show v.ofLp 0 = (i : ℝ) / m by simp [v, mk2]]
          simpa using hcoord0
        have h01' : |dist (x.ofLp 0) (v.ofLp 0)| ≤ |(1 : ℝ) / m| := by
          rw [abs_of_nonneg (show 0 ≤ (1 : ℝ) / m from one_div_nonneg.mpr (Nat.cast_nonneg m))]
          exact h01
        exact sq_le_sq.2 h01'
      · have h11 : |dist (x.ofLp 1) (v.ofLp 1)| ≤ (1 : ℝ) / m := by
          rw [Real.dist_eq]
          rw [show v.ofLp 1 = (j : ℝ) / m by simp [v, mk2]]
          simpa using hcoord1
        have h11' : |dist (x.ofLp 1) (v.ofLp 1)| ≤ |(1 : ℝ) / m| := by
          rw [abs_of_nonneg (show 0 ≤ (1 : ℝ) / m from one_div_nonneg.mpr (Nat.cast_nonneg m))]
          exact h11
        exact sq_le_sq.2 h11'
    _ ≤ Real.sqrt 2 / m := by
      calc
        √((1 / m) ^ 2 + (1 / m) ^ 2) ≤ √(2 * (1 / m) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg ((1 : ℝ) / m)]
        _ = √2 * |(1 : ℝ) / m| := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) (((1 : ℝ) / m) ^ 2), Real.sqrt_sq_eq_abs]
        _ = √2 * ((1 : ℝ) / m) := by
          rw [abs_of_nonneg (show 0 ≤ (1 : ℝ) / m from one_div_nonneg.mpr (Nat.cast_nonneg m))]
        _ = Real.sqrt 2 / m := by ring

/-- **Uniform covering numbers for the whole grid family.**  For every `ε > 0` there is
`K = (⌈4/ε⌉₊ + 1)²` such that every grid space (of every mesh) is covered by `≤ K` `ε`-balls.
The cardinalities `(m+1)²` of the members are unbounded, so this bound comes from genuine
geometry (denseness of the square grid), not from a finite-points argument. -/
theorem gridUniformCover (ε : ℝ) (εpos : 0 < ε) :
    ∃ K : ℕ, ∀ m : ℕ, ∃ s : Set (gridSpace m), #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  let m₀ := ⌈4 / ε⌉₊
  have hm₀pos : 0 < m₀ := Nat.ceil_pos.2 (by positivity : 0 < 4 / ε)
  have hm₀' : 0 < (m₀ : ℝ) := Nat.cast_pos.2 hm₀pos
  have hm₀_le : 4 / ε ≤ (m₀ : ℝ) := by
    simpa [m₀] using (Nat.le_ceil (4 / ε) : (4 / ε : ℝ) ≤ (⌈4 / ε⌉₊ : ℝ))
  -- for each square-grid vertex p (indexed by the pair type directly) of mesh 1/m₀, choose a
  -- point c m p of the target grid near that vertex (if one exists), else the default point 0.
  let gridPt (p : Fin (m₀ + 1) × Fin (m₀ + 1)) : E2 := mk2 ((p.1 : ℝ) / m₀) ((p.2 : ℝ) / m₀)
  let defaultPoint (m : ℕ) : gridSpace m := ⟨0, zero_mem_gridSet m⟩
  -- `c m p` is a point of the target grid which is within √2/m₀ of `gridPt p` whenever such a
  -- point exists (and an arbitrary grid point otherwise); the existence statement is made total
  -- by a conditional so that no `if`-elimination is needed later.
  let c (m : ℕ) (p : Fin (m₀ + 1) × Fin (m₀ + 1)) : gridSpace m :=
    Classical.choose (show ∃ z : gridSpace m,
      (∃ w : gridSpace m, dist (w : E2) (gridPt p) ≤ Real.sqrt 2 / m₀) →
        dist (z : E2) (gridPt p) ≤ Real.sqrt 2 / m₀ from by
      by_cases h : ∃ w : gridSpace m, dist (w : E2) (gridPt p) ≤ Real.sqrt 2 / m₀
      · rcases h with ⟨w, hw⟩
        exact ⟨w, fun _ => hw⟩
      · refine ⟨defaultPoint m, fun hw => False.elim ?_⟩
        exact h hw)
  refine ⟨(m₀ + 1) * (m₀ + 1), ?_⟩
  intro m
  refine ⟨range fun p : Fin (m₀ + 1) × Fin (m₀ + 1) => c m p, ?_, ?_⟩
  · -- cardinality bound: the centers are indexed by the (m₀+1)² pairs
    calc
      #(range fun p : Fin (m₀ + 1) × Fin (m₀ + 1) => c m p) ≤ #(Fin (m₀ + 1) × Fin (m₀ + 1)) :=
        Cardinal.mk_range_le (f := fun p : Fin (m₀ + 1) × Fin (m₀ + 1) => c m p)
      _ = (((m₀ + 1) * (m₀ + 1) : ℕ) : Cardinal) := by
        rw [Cardinal.mk_fintype]
        simp [Fintype.card_prod]
  · -- covering property
    intro y hy
    have hy_sq : (y : E2) ∈ unitSquare := gridPoint_coord m y.2
    rcases square_grid_dense hm₀pos hy_sq with ⟨v, hv, hdist⟩
    -- v is a grid vertex, so v = gridPt p for some pair p
    rcases (Finset.mem_image.1 (show v ∈ (Finset.univ : Finset (Fin (m₀ + 1) × Fin (m₀ + 1))).image
        (fun p : Fin (m₀ + 1) × Fin (m₀ + 1) => mk2 ((p.1 : ℝ) / m₀) ((p.2 : ℝ) / m₀)) from by
      simpa [gridSet, gridVertices] using hv)) with ⟨p, hp, hv_eq⟩
    have hv_eq' : gridPt p = v := by
      simpa [gridPt] using hv_eq
    have hdist' : dist (y : E2) (gridPt p) ≤ Real.sqrt 2 / m₀ := by
      simpa [hv_eq'] using hdist
    -- the chosen center c m p is within √2/m₀ of gridPt p (by the `if` condition, since y witnesses it)
    have hnear : dist ((c m p : gridSpace m) : E2) (gridPt p) ≤ Real.sqrt 2 / m₀ := by
      dsimp [c]
      exact (Classical.choose_spec (show ∃ z : gridSpace m,
        (∃ w : gridSpace m, dist (w : E2) (gridPt p) ≤ Real.sqrt 2 / m₀) →
          dist (z : E2) (gridPt p) ≤ Real.sqrt 2 / m₀ from by
        by_cases h : ∃ w : gridSpace m, dist (w : E2) (gridPt p) ≤ Real.sqrt 2 / m₀
        · rcases h with ⟨w, hw⟩
          exact ⟨w, fun _ => hw⟩
        · refine ⟨defaultPoint m, fun hw => False.elim ?_⟩
          exact h hw))
        ⟨y, hdist'⟩
    have hclose : dist y (c m p) < ε := by
      calc
        dist y (c m p) = dist (y : E2) ((c m p : gridSpace m) : E2) :=
          (Subtype.dist_eq y (c m p)).symm
        _ ≤ dist (y : E2) (gridPt p) + dist (gridPt p) ((c m p : gridSpace m) : E2) := dist_triangle _ _ _
        _ ≤ Real.sqrt 2 / m₀ + Real.sqrt 2 / m₀ := by
          have hnear' : dist (gridPt p) ((c m p : gridSpace m) : E2) ≤ Real.sqrt 2 / m₀ := by
            rw [dist_comm]
            exact hnear
          exact add_le_add hdist' hnear'
        _ = 2 * (Real.sqrt 2 / m₀) := by nlinarith
        _ < ε := by
          have hsqrt : Real.sqrt 2 < 2 := by
            rw [Real.sqrt_lt' (by norm_num : 0 < (2 : ℝ))]
            norm_num
          have hm₀inv : (m₀ : ℝ)⁻¹ ≤ ε / 4 := by
            have hle : (m₀ : ℝ)⁻¹ ≤ (4 / ε)⁻¹ := by
              rw [inv_le_inv₀ hm₀' (by positivity : 0 < (4 / ε : ℝ))]
              exact hm₀_le
            rw [inv_div] at hle
            exact hle
          have h1 : Real.sqrt 2 / m₀ ≤ Real.sqrt 2 * (ε / 4) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left hm₀inv (Real.sqrt_nonneg 2)
          have h2 : 2 * (Real.sqrt 2 / m₀) ≤ 2 * (Real.sqrt 2 * (ε / 4)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
          have h3 : 2 * (Real.sqrt 2 * (ε / 4)) < ε := by
            have hleft : 2 * (Real.sqrt 2 * (ε / 4)) = (Real.sqrt 2 / 2) * ε := by
              ring_nf
            have hhalf : Real.sqrt 2 / 2 < 1 := by nlinarith [hsqrt]
            rw [hleft]
            exact (mul_lt_mul_of_pos_right hhalf εpos).trans_eq (one_mul ε)
          exact lt_of_le_of_lt h2 h3
    refine mem_iUnion₂.2 ⟨c m p, mem_range_self _, mem_ball.2 hclose⟩

/-- All grid spaces have diameter `≤ √2`. -/
theorem gridSpace_diam_le (m : ℕ) : diam (univ : Set (gridSpace m)) ≤ Real.sqrt 2 := by
  refine diam_le_of_forall_dist_le (C := Real.sqrt 2) (by positivity : 0 ≤ Real.sqrt 2) ?_
  intro x hx y hy
  have hxsq : (x : E2) ∈ unitSquare := gridPoint_coord m x.2
  have hysq : (y : E2) ∈ unitSquare := gridPoint_coord m y.2
  calc
    dist x y = dist (x : E2) (y : E2) := (Subtype.dist_eq x y).symm
    _ = √(∑ k : Fin 2, dist ((x : E2).ofLp k) ((y : E2).ofLp k) ^ 2) := by
      rw [EuclideanSpace.dist_eq]
    _ = √(dist ((x : E2).ofLp 0) ((y : E2).ofLp 0) ^ 2 + dist ((x : E2).ofLp 1) ((y : E2).ofLp 1) ^ 2) := by
      rw [Fin.sum_univ_two]
    _ ≤ √(1 ^ 2 + 1 ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply add_le_add
      · rw [Real.dist_eq]
        have h0 : |(x : E2).ofLp 0 - (y : E2).ofLp 0| ≤ 1 := by
          have hx0 := (hxsq 0)
          have hy0 := (hysq 0)
          rw [abs_le]
          constructor <;> linarith
        exact sq_le_sq.2 (by simpa using h0)
      · rw [Real.dist_eq]
        have h1 : |(x : E2).ofLp 1 - (y : E2).ofLp 1| ≤ 1 := by
          have hx1 := (hxsq 1)
          have hy1 := (hysq 1)
          rw [abs_le]
          constructor <;> linarith
        exact sq_le_sq.2 (by simpa using h1)
    _ = Real.sqrt 2 := by
      rw [show (1 ^ 2 + 1 ^ 2 : ℝ) = 2 by norm_num]

/-- The Hausdorff distance between the mesh-`1/m` grid and the unit square in the plane is at
most `√2/m` (for `0 < m`). -/
theorem hausdorffDist_grid_square_le (m : ℕ) (hm : 0 < m) :
    hausdorffDist (gridSet m) unitSquare ≤ Real.sqrt 2 / m := by
  refine hausdorffDist_le_of_mem_dist (div_nonneg (Real.sqrt_nonneg 2) (Nat.cast_nonneg m) :
    0 ≤ Real.sqrt 2 / m) ?_ ?_
  · intro x hx
    exact ⟨x, gridPoint_coord m hx, by
      simpa [dist_self] using (div_nonneg (Real.sqrt_nonneg 2) (Nat.cast_nonneg m) :
        0 ≤ Real.sqrt 2 / m)⟩
  · intro x hx
    rcases square_grid_dense hm hx with ⟨v, hv, hdist⟩
    exact ⟨v, hv, hdist⟩

/-- **Convergence witness: the finite grids converge to the Euclidean square.** -/
theorem grid_gh_tendsto_square :
    Tendsto (fun n : ℕ => gridGH (n + 1)) atTop (𝓝 squareGH) := by
  classical
  have hdist_le : ∀ n : ℕ, dist (gridGH (n + 1)) squareGH ≤ Real.sqrt 2 / ((n : ℝ) + 1) := by
    intro n
    rw [dist_ghDist]
    have hcongr : ghDist (GHSpace.Rep (gridGH (n + 1))) (GHSpace.Rep squareGH) =
        ghDist (gridSpace (n + 1)) squareSpace := by
      rcases toGHSpace_rep_isometryEquiv (gridSpace (n + 1)) with ⟨e⟩
      rcases toGHSpace_rep_isometryEquiv squareSpace with ⟨e'⟩
      rw [ghDist_congr_left e, ghDist_congr_right e']
    rw [hcongr]
    have hH : hausdorffDist (gridSet (n + 1)) unitSquare ≤ Real.sqrt 2 / ((n : ℝ) + 1) := by
      simpa [Nat.cast_add] using hausdorffDist_grid_square_le (n + 1) (by positivity)
    calc
      ghDist (gridSpace (n + 1)) squareSpace ≤
          hausdorffDist (range (Subtype.val : gridSpace (n + 1) → E2))
            (range (Subtype.val : squareSpace → E2)) :=
        ghDist_le_hausdorffDist isometry_subtype_coe isometry_subtype_coe
      _ = hausdorffDist (gridSet (n + 1)) unitSquare := by
        rw [Subtype.range_coe, Subtype.range_coe]
      _ ≤ Real.sqrt 2 / ((n : ℝ) + 1) := hH
  refine Metric.tendsto_atTop.2 fun ε εpos => ?_
  have htend : Tendsto (fun n : ℕ => Real.sqrt 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.sqrt 2)
  rcases Metric.tendsto_atTop.1 htend ε εpos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hle := hdist_le n
  have habs : |dist (gridGH (n + 1)) squareGH| < ε := by
    have hd := hN n hn
    have hnonneg : 0 ≤ dist (gridGH (n + 1)) squareGH := dist_nonneg
    calc
      |dist (gridGH (n + 1)) squareGH| = dist (gridGH (n + 1)) squareGH := abs_of_nonneg hnonneg
      _ ≤ Real.sqrt 2 / ((n : ℝ) + 1) := hle
      _ = |Real.sqrt 2 / ((n : ℝ) + 1)| := by
        rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg 2) (by positivity : 0 ≤ (n : ℝ) + 1))]
      _ < ε := by
        rw [Real.dist_eq, sub_zero] at hd
        exact hd
  simpa [Real.dist_eq] using habs

/-- The grid space of mesh `1/m` has `(m+1)²` points. -/
theorem gridSpace_card (m : ℕ) : Fintype.card (gridSpace m) = (m + 1) * (m + 1) := by
  have hbase : (gridVertices m).card = (m + 1) * (m + 1) := by
    calc
      (gridVertices m).card = (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).card := by
        apply Finset.card_image_of_injective
        intro p q hpq
        by_cases hm : m = 0
        · subst hm
          apply Prod.ext
          · simpa using (Fin.subsingleton_one.elim p.1 q.1 : p.1 = q.1)
          · simpa using (Fin.subsingleton_one.elim p.2 q.2 : p.2 = q.2)
        · have hm' : 0 < (m : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
          have hp0 : (mk2 ((p.1 : ℝ) / m) ((p.2 : ℝ) / m)).ofLp 0 =
              (mk2 ((q.1 : ℝ) / m) ((q.2 : ℝ) / m)).ofLp 0 := congrArg (·.ofLp 0) hpq
          have hp1 : (mk2 ((p.1 : ℝ) / m) ((p.2 : ℝ) / m)).ofLp 1 =
              (mk2 ((q.1 : ℝ) / m) ((q.2 : ℝ) / m)).ofLp 1 := congrArg (·.ofLp 1) hpq
          simp at hp0 hp1
          have hq1 : (p.1 : ℝ) = (q.1 : ℝ) := by
            have hmul : (p.1 : ℝ) * m = (q.1 : ℝ) * m := (div_eq_div_iff hm'.ne' hm'.ne').1 hp0
            exact mul_right_cancel₀ hm'.ne' hmul
          have hq2 : (p.2 : ℝ) = (q.2 : ℝ) := by
            have hmul : (p.2 : ℝ) * m = (q.2 : ℝ) * m := (div_eq_div_iff hm'.ne' hm'.ne').1 hp1
            exact mul_right_cancel₀ hm'.ne' hmul
          ext
          · exact_mod_cast hq1
          · exact_mod_cast hq2
      _ = (m + 1) * (m + 1) := by
        simp [Fintype.card_prod]
  rw [show Fintype.card (gridSpace m) = (gridVertices m).card by
    rw [show Fintype.card (gridSpace m) = (Finset.univ : Finset (gridSpace m)).card from rfl,
      Finset.univ_eq_attach, Finset.card_attach], hbase]

/-- Two grid spaces with different mesh sizes are non-isometric (their cardinalities differ),
so they give distinct points of `GHSpace`. -/
theorem gridGH_injective : Function.Injective fun n : ℕ => gridGH (n + 1) := by
  intro n n' h
  have hisom : Nonempty (gridSpace (n + 1) ≃ᵢ gridSpace (n' + 1)) := by
    simpa [gridGH] using (toGHSpace_eq_toGHSpace_iff_isometryEquiv (X := gridSpace (n + 1))
      (Y := gridSpace (n' + 1))).1 h
  rcases hisom with ⟨e⟩
  have hcard : Fintype.card (gridSpace (n + 1)) = Fintype.card (gridSpace (n' + 1)) := by
    have hmk : #(gridSpace (n + 1)) = #(gridSpace (n' + 1)) := Equiv.cardinal_eq e.toEquiv
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype] at hmk
    exact Nat.cast_injective hmk
  rw [gridSpace_card, gridSpace_card] at hcard
  nlinarith

/-- The grid family is infinite: unbounded cardinality, so precompactness cannot come from
a uniform finite-points bound. -/
theorem gridFamily_infinite : Set.Infinite {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)} := by
  rw [show {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)} = range fun n : ℕ => gridGH (n + 1) by
    ext p
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩]
  exact Set.infinite_range_of_injective gridGH_injective

/-- The grid family satisfies the uniform diameter and covering-number hypotheses of Gromov's
criterion (with `u n = 1/(n+1)`), hence is totally bounded in `GHSpace`. -/
theorem gridFamily_totallyBounded :
    TotallyBounded {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)} := by
  classical
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have ulim : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let t : Set GHSpace := {p | ∃ n : ℕ, p = gridGH (n + 1)}
  have hdiam : ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ Real.sqrt 2 := by
    intro p hp
    rcases hp with ⟨n, rfl⟩
    rw [diam_rep_of_toGHSpace (gridSpace (n + 1))]
    exact gridSpace_diam_le (n + 1)
  choose K hKcov using fun n : ℕ =>
    gridUniformCover (1 / ((n : ℝ) + 1)) (one_div_pos.mpr (by positivity : 0 < (n : ℝ) + 1))
  have hcov : ∀ p ∈ t, ∀ n : ℕ, ∃ s : Set (GHSpace.Rep p),
      #s ≤ K n ∧ univ ⊆ ⋃ x ∈ s, ball x (u n) := by
    intro p hp n
    rcases hp with ⟨m, rfl⟩
    rcases hKcov n (m + 1) with ⟨s₀, hs₀card, hs₀cov⟩
    rcases toGHSpace_rep_isometryEquiv (gridSpace (m + 1)) with ⟨e⟩
    -- transfer the cover of gridSpace (m+1) to p.Rep along the isometry e : p.Rep ≃ᵢ gridSpace (m+1)
    have hcov₀ : ∀ y : gridSpace (m + 1), ∃ i : s₀, dist y (i : gridSpace (m + 1)) < 1 / ((n : ℝ) + 1) := by
      intro y
      have hy : y ∈ ⋃ x ∈ s₀, ball x (1 / ((n : ℝ) + 1)) := hs₀cov (mem_univ y)
      rcases mem_iUnion₂.1 hy with ⟨x, hx, hxb⟩
      exact ⟨⟨x, hx⟩, by simpa [dist_comm] using mem_ball'.1 hxb⟩
    rcases cover_transfer_of_isometry e hcov₀ with ⟨s, hscard, hscov⟩
    exact ⟨s, hscard.trans hs₀card, hscov⟩
  exact GromovHausdorff.totallyBounded ulim hdiam hcov

/-- The closure of the grid family is compact in `GHSpace`. -/
theorem gridFamily_closure_isCompact :
    IsCompact (closure {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)}) := by
  exact gridFamily_totallyBounded.closure.isCompact_of_isClosed isClosed_closure

/-- **Subsequence witness for the grid family.**  Every sequence of grid spaces has a strictly
monotone reindexing converging in `ghDist` to a limit in the closure of the family. -/
theorem gridFamily_subseq {u : ℕ → GHSpace} (hu : ∀ n, u n ∈ closure {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)}) :
    ∃ (a : GHSpace) (φ : ℕ → ℕ), a ∈ closure {p : GHSpace | ∃ n : ℕ, p = gridGH (n + 1)} ∧
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) ∧
      Tendsto (fun n => ghDist (GHSpace.Rep (u (φ n))) (GHSpace.Rep a)) atTop (𝓝 0) := by
  exact gh_subseq_of_compact gridFamily_closure_isCompact hu

end Poincare.D12.GeometricCompactness
