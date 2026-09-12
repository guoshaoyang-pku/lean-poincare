/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib
import Poincare.D12.TriangulationTopology.SphereGluing

/-!
# Poincare.D12.TriangulationTopology.SimplexBoundary

**DAG node 9, proved.** The boundary of the standard `(n+1)`-simplex is homeomorphic to
the `n`-sphere: `∂Δⁿ⁺¹ ≃ₜ 𝕊ⁿ`, with the exact statement recorded in
`MoiseBranch.simplexBoundaryHomeoSphere` (in terms of `Convexity.StdSimplex ℝ (Fin (n+2))`).
For `n = 3` this is the standard triangulation of the 3-sphere as `|∂Δ⁴|` (five tetrahedra),
the triangulation input of the sphere-recognition branch.

## Construction

Both maps are explicit radial formulas from the barycenter `c = 1/(n+2)` of `Δⁿ⁺¹`:

* Forward `∂Δⁿ⁺¹ → 𝕊ⁿ`: take the first `n+1` barycentric coordinates minus `c`, normalize.
* Backward `𝕊ⁿ → ∂Δⁿ⁺¹`: the ray from `c` through `(y, -∑y)` leaves the simplex when the
  minimal coordinate hits `0`, at time `λ(y) = -c / ⨅ᵢ d(y)ᵢ` where `d(y) = (y, -∑y)`.

All algebra is checked on `Fin (n+2)` coordinates (`Fin.sum_univ_castSucc` splits the
last coordinate), continuity of the minimum comes from `IsCompact.continuous_sInf` over
the finite index set, and the two maps are shown mutually inverse by norm algebra of the
same shape as `SphereGluing.lean`.  The transfer from the function-space model to
`Convexity.StdSimplex` uses mathlib's `Convexity.StdSimplex.isEmbedding_toFun_comp_weights`
and `Topology.IsEmbedding.homeomorphImage`.

## Provenance of external mathematics

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by lake-manifest.json),
  Apache-2.0: all imported lemmas.  The radial-projection homeomorphism between the simplex
  boundary and the sphere is classical; all proofs here are original to this worktree.
-/

noncomputable section

open scoped Topology
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## The function-space model of the simplex boundary -/

/-- The barycenter of the standard `(n+1)`-simplex in `ℝⁿ⁺²` coordinates:
all weights equal to `(n+2)⁻¹`. -/
def simplexCenter (n : ℕ) : ℝ := ((n + 2 : ℕ) : ℝ)⁻¹

/-- **Nonemptiness/nondegeneracy audit.** The barycenter weight is positive. -/
theorem simplexCenter_pos (n : ℕ) : 0 < simplexCenter n := by
  rw [simplexCenter, inv_pos, Nat.cast_pos]
  norm_num

/-- **Dimension audit.** The barycenter has `n+2` coordinates summing to 1:
`(n+2) • c = 1`. -/
theorem simplexCenter_total (n : ℕ) : ((n + 2 : ℕ) : ℝ) * simplexCenter n = 1 := by
  rw [simplexCenter, mul_inv_cancel₀]
  exact Nat.cast_ne_zero.mpr (by norm_num : n + 2 ≠ 0)

/-- The boundary of the standard `(n+1)`-simplex as a subset of `ℝⁿ⁺²`:
nonnegative weights, total weight 1, and some vertex coordinate is `0`. -/
def simplexBoundarySet (n : ℕ) : Set (Fin (n + 2) → ℝ) :=
  {s | 0 ≤ s ∧ (∑ i, s i) = 1 ∧ 0 ∈ Set.range s}

/-- Function-space model of `∂Δⁿ⁺¹` (subtype topology of `ℝⁿ⁺²`). -/
abbrev SimplexBoundaryFn (n : ℕ) := simplexBoundarySet n

/-- The direction function: `d(y) = (y, -∑y) ∈ ℝⁿ⁺²`, a vector orthogonal to the all-ones
vector (its coordinate sum is `0`). -/
def simplexDir (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) : Fin (n + 2) → ℝ :=
  Fin.lastCases (n := n + 1) (-∑ j : Fin (n + 1), y j) (fun j => y j)

@[simp] theorem simplexDir_last (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    simplexDir n y (Fin.last (n + 1)) = -∑ j : Fin (n + 1), y j := by
  simp [simplexDir]

@[simp] theorem simplexDir_castSucc (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) : simplexDir n y j.castSucc = y j := by
  simp [simplexDir]

/-- The direction vector has coordinate sum zero. -/
theorem simplexDir_sum (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    (∑ i : Fin (n + 2), simplexDir n y i) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [add_neg_cancel]

/-- The minimal coordinate `⨅ i, d(y) i` of the direction vector. -/
def simplexMin (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  ⨅ i : Fin (n + 2), simplexDir n y i

theorem simplexMin_le (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 2)) :
    simplexMin n y ≤ simplexDir n y i := by
  exact ciInf_le (f := simplexDir n y) (Set.finite_range (simplexDir n y) |>.bddBelow) i

theorem le_simplexMin (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) {a : ℝ}
    (h : ∀ i : Fin (n + 2), a ≤ simplexDir n y i) : a ≤ simplexMin n y := by
  exact le_ciInf (f := simplexDir n y) h

theorem simplexMin_attains (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ i : Fin (n + 2), simplexDir n y i = simplexMin n y := by
  exact exists_eq_ciInf_of_finite (f := simplexDir n y)

/-- On the unit sphere, the minimal direction coordinate is strictly negative
(otherwise all coordinates would be `≥ 0`, forcing `y = 0` by `∑ d = 0`). -/
theorem simplexMin_neg_of_unit (n : ℕ) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : ‖y‖ = 1) :
    simplexMin n y < 0 := by
  by_contra h
  have hm_nonneg : 0 ≤ simplexMin n y := le_of_not_gt h
  have hle : ∀ i : Fin (n + 2), 0 ≤ simplexDir n y i := fun i =>
    hm_nonneg.trans (simplexMin_le n y i)
  have hzero : ∀ i : Fin (n + 2), simplexDir n y i = 0 := by
    have hsum := simplexDir_sum n y
    have h' := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (f := fun i : Fin (n + 2) => simplexDir n y i)
      (fun i hi => hle i)).1 hsum
    intro i
    exact h' i (Finset.mem_univ i)
  have hyz : y = 0 := by
    apply PiLp.ext
    intro j
    simpa using hzero j.castSucc
  rw [hyz, norm_zero] at hy
  norm_num at hy

/-- Continuity of `d(y) i` in `y` for each fixed vertex `i`. -/
theorem continuous_simplexDir_apply (n : ℕ) (i : Fin (n + 2)) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => simplexDir n y i) := by
  refine Fin.lastCases (n := n + 1)
    (motive := fun i => Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => simplexDir n y i))
    ?_ ?_ i
  · -- i = last: -∑ y
    have hsum : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        (∑ j : Fin (n + 1), y j)) :=
      continuous_finsetSum Finset.univ (fun j _ =>
        PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) j)
    simp only [simplexDir, Fin.lastCases_last]
    exact continuous_neg.comp hsum
  · intro j
    have hj : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y j) :=
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) j
    simp only [simplexDir, Fin.lastCases_castSucc]
    exact hj

/-- Continuity of the direction function `y ↦ d(y)`. -/
theorem continuous_simplexDir (n : ℕ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => simplexDir n y) := by
  apply continuous_pi
  intro i
  exact continuous_simplexDir_apply n i

/-- Continuity of the minimal coordinate `y ↦ ⨅ i, d(y) i`, via
`IsCompact.continuous_sInf` over the finite vertex set. -/
theorem continuous_simplexMin (n : ℕ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => simplexMin n y) := by
  change Continuous fun y : EuclideanSpace ℝ (Fin (n + 1)) => sInf (Set.range (simplexDir n y))
  have hf : Continuous
      (fun p : EuclideanSpace ℝ (Fin (n + 1)) × Fin (n + 2) => simplexDir n p.1 p.2) := by
    have hg : Continuous (fun q : Fin (n + 2) × EuclideanSpace ℝ (Fin (n + 1)) =>
        simplexDir n q.2 q.1) := by
      rw [continuous_prod_of_discrete_left]
      intro i
      exact continuous_simplexDir_apply n i
    change Continuous ((fun q : Fin (n + 2) × EuclideanSpace ℝ (Fin (n + 1)) =>
      simplexDir n q.2 q.1) ∘ Prod.swap)
    exact hg.comp continuous_swap
  have h := IsCompact.continuous_sInf (α := ℝ) (β := Fin (n + 2))
    (γ := EuclideanSpace ℝ (Fin (n + 1)))
    (f := fun y : EuclideanSpace ℝ (Fin (n + 1)) => simplexDir n y) (K := Set.univ)
    isCompact_univ hf
  simpa [Set.image_univ] using h

/-- The radial exit time: `λ(y) = -c / ⨅ᵢ d(y)ᵢ`, positive on the unit sphere. -/
def simplexLambda (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  -simplexCenter n * (simplexMin n y)⁻¹

theorem simplexLambda_pos_of_unit (n : ℕ) {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : ‖y‖ = 1) :
    0 < simplexLambda n y := by
  unfold simplexLambda
  exact mul_pos_of_neg_of_neg
    (neg_neg_of_pos (simplexCenter_pos n))
    ((inv_lt_zero).2 (simplexMin_neg_of_unit n hy))

/-- Continuity of `λ` on the sphere. -/
theorem continuous_sphere_simplexLambda (n : ℕ) :
    Continuous (fun y : Sphere n => simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hm : Continuous (fun y : Sphere n => simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1)))) :=
    (continuous_simplexMin n).comp continuous_subtype_val
  have hne : ∀ y : Sphere n, simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 :=
    fun y => ne_of_lt (simplexMin_neg_of_unit n (mem_sphere_zero_iff_norm.mp y.2))
  exact Continuous.mul continuous_const (Continuous.inv₀ hm hne)

/-! ## The two radial maps -/

/-- Truncated difference from the barycenter: first `n+1` coordinates of `s - c`. -/
def truncToCenter (n : ℕ) (s : Fin (n + 2) → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) => s j.castSucc - simplexCenter n)

/-- The truncated difference is nonzero on the boundary (it vanishes only at the
barycenter, which is interior). -/
theorem truncToCenter_ne_zero (n : ℕ) {s : Fin (n + 2) → ℝ} (hs : s ∈ simplexBoundarySet n) :
    truncToCenter n s ≠ 0 := by
  intro h
  have hf : (fun j : Fin (n + 1) => s j.castSucc - simplexCenter n) = 0 := by
    dsimp [truncToCenter] at h
    exact congrArg (WithLp.equiv 2 (Fin (n + 1) → ℝ)) h
  have hcast : ∀ j : Fin (n + 1), s j.castSucc = simplexCenter n := by
    intro j
    have hj : s j.castSucc - simplexCenter n = 0 := congr_fun hf j
    simpa [sub_eq_zero] using hj
  have hlast : s (Fin.last (n + 1)) = simplexCenter n := by
    have hsum : (∑ i : Fin (n + 2), s i) = 1 := hs.2.1
    rw [Fin.sum_univ_castSucc] at hsum
    have hsum' : (∑ j : Fin (n + 1), s j.castSucc) = ((n + 1 : ℕ) : ℝ) * simplexCenter n := by
      calc
        (∑ j : Fin (n + 1), s j.castSucc) = ∑ j : Fin (n + 1), simplexCenter n := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcast j
        _ = (Finset.univ : Finset (Fin (n + 1))).card • simplexCenter n :=
          (Finset.sum_const (s := (Finset.univ : Finset (Fin (n + 1)))) (simplexCenter n))
        _ = ((n + 1 : ℕ) : ℝ) * simplexCenter n := by simp [nsmul_eq_mul]
    rw [hsum'] at hsum
    have hc : ((n + 2 : ℕ) : ℝ) * simplexCenter n = 1 := simplexCenter_total n
    have hsub : ((n + 2 : ℕ) : ℝ) * simplexCenter n - ((n + 1 : ℕ) : ℝ) * simplexCenter n
        = simplexCenter n := by
      have hnat : ((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = 1 := by
        norm_num [Nat.cast_add]
      nlinarith [hnat]
    calc
      s (Fin.last (n + 1)) = 1 - ((n + 1 : ℕ) : ℝ) * simplexCenter n := by
        linarith [hsum]
      _ = ((n + 2 : ℕ) : ℝ) * simplexCenter n - ((n + 1 : ℕ) : ℝ) * simplexCenter n := by
        rw [hc]
      _ = simplexCenter n := hsub
  rcases hs.2.2 with ⟨i₀, hi₀⟩
  have hzero : (0 : ℝ) = simplexCenter n := by
    refine Fin.lastCases (n := n + 1) (motive := fun i => s i = 0 → (0 : ℝ) = simplexCenter n) ?_ ?_ i₀ hi₀
    · intro hzero_last
      rw [hlast] at hzero_last
      exact hzero_last.symm
    · intro j hzero_j
      rw [hcast j] at hzero_j
      exact hzero_j.symm
  have hpos : 0 < simplexCenter n := simplexCenter_pos n
  linarith

/-- Forward map `∂Δⁿ⁺¹ → 𝕊ⁿ`: normalize the truncated barycenter difference. -/
def simplexBoundaryToSphere (n : ℕ) (s : SimplexBoundaryFn n) : Sphere n :=
  ⟨(‖truncToCenter n (s : Fin (n + 2) → ℝ)‖)⁻¹ • truncToCenter n (s : Fin (n + 2) → ℝ), by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    have ht : 0 < ‖truncToCenter n (s : Fin (n + 2) → ℝ)‖ :=
      norm_pos_iff.mpr (truncToCenter_ne_zero n s.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt ht))]
    exact inv_mul_cancel₀ (ne_of_gt ht)⟩

/-- Continuity of the truncated difference in the ambient function space. -/
theorem continuous_truncToCenter (n : ℕ) :
    Continuous (fun s : Fin (n + 2) → ℝ => truncToCenter n s) := by
  unfold truncToCenter
  refine PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ) |>.comp ?_
  apply continuous_pi
  intro j
  exact (continuous_apply j.castSucc).sub continuous_const

/-- Continuity of the forward map `∂Δⁿ⁺¹ → 𝕊ⁿ`. -/
theorem continuous_simplexBoundaryToSphere (n : ℕ) :
    Continuous (simplexBoundaryToSphere n) := by
  rw [continuous_induced_rng]
  change Continuous (fun s : SimplexBoundaryFn n =>
    (‖truncToCenter n (s : Fin (n + 2) → ℝ)‖)⁻¹ • truncToCenter n (s : Fin (n + 2) → ℝ))
  refine Continuous.smul (f := fun s : SimplexBoundaryFn n =>
    (‖truncToCenter n (s : Fin (n + 2) → ℝ)‖)⁻¹)
    (g := fun s : SimplexBoundaryFn n => truncToCenter n (s : Fin (n + 2) → ℝ)) ?_ ?_
  · refine Continuous.inv₀ (Continuous.norm ((continuous_truncToCenter n).comp continuous_subtype_val)) ?_
    intro s
    exact norm_ne_zero_iff.mpr (truncToCenter_ne_zero n s.2)
  · exact (continuous_truncToCenter n).comp continuous_subtype_val

/-- Backward map `𝕊ⁿ → ∂Δⁿ⁺¹`: the ray from the barycenter in direction `d(y)`, stopped
when the minimal coordinate reaches `0`. -/
def sphereToSimplexBoundary (n : ℕ) (y : Sphere n) : Fin (n + 2) → ℝ :=
  fun i => simplexCenter n +
    simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i

/-- The backward map lands in the boundary set: coordinates nonnegative (the minimal one
is `0`), total weight 1, and a vertex coordinate equal to `0`. -/
theorem sphereToSimplexBoundary_mem (n : ℕ) (y : Sphere n) :
    sphereToSimplexBoundary n y ∈ simplexBoundarySet n := by
  change 0 ≤ sphereToSimplexBoundary n y ∧
    (∑ i, sphereToSimplexBoundary n y i) = 1 ∧ 0 ∈ Set.range (sphereToSimplexBoundary n y)
  have hy : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  have hlambda_nonneg : 0 ≤ simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) :=
    le_of_lt (simplexLambda_pos_of_unit n hy)
  constructor
  · rw [Pi.le_def]
    intro i
    dsimp [sphereToSimplexBoundary]
    have hdir : simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) ≤
        simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i :=
      simplexMin_le n (y : EuclideanSpace ℝ (Fin (n + 1))) i
    calc
      simplexCenter n + simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) *
          simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i
          ≥ simplexCenter n + simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) *
              simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hdir hlambda_nonneg)
      _ = 0 := by
        have hm : simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 :=
          ne_of_lt (simplexMin_neg_of_unit n hy)
        dsimp [simplexLambda]
        field_simp [hm]
        ring
  · constructor
    · dsimp [sphereToSimplexBoundary]
      rw [Fin.sum_univ_castSucc]
      simp only [simplexDir_castSucc, simplexDir_last, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_neg]
      rw [Finset.mul_sum]
      ring_nf
      have hcast : ((1 + n : ℕ) : ℝ) * simplexCenter n + simplexCenter n =
          ((n + 2 : ℕ) : ℝ) * simplexCenter n := by
        calc
          ((1 + n : ℕ) : ℝ) * simplexCenter n + simplexCenter n
              = (((1 + n : ℕ) : ℝ) + 1) * simplexCenter n := by ring
          _ = ((n + 2 : ℕ) : ℝ) * simplexCenter n := by
            congr 1
            norm_num [Nat.cast_add]
            ring
      rw [hcast, simplexCenter_total n]
    · rcases simplexMin_attains n (y : EuclideanSpace ℝ (Fin (n + 1))) with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      dsimp [sphereToSimplexBoundary, simplexLambda]
      rw [hi]
      have hm : simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 :=
        ne_of_lt (simplexMin_neg_of_unit n hy)
      field_simp [hm]
      ring

/-- The backward map as a map into the boundary subtype. -/
def sphereToSimplexBoundaryFn (n : ℕ) (y : Sphere n) : SimplexBoundaryFn n :=
  ⟨sphereToSimplexBoundary n y, sphereToSimplexBoundary_mem n y⟩

/-- Continuity of the backward map `𝕊ⁿ → ∂Δⁿ⁺¹`. -/
theorem continuous_sphereToSimplexBoundaryFn (n : ℕ) :
    Continuous (sphereToSimplexBoundaryFn n) := by
  rw [continuous_induced_rng]
  change Continuous (fun y : Sphere n => sphereToSimplexBoundary n y)
  apply continuous_pi
  intro i
  refine Continuous.add continuous_const ?_
  refine Continuous.mul (continuous_sphere_simplexLambda n) ?_
  exact (continuous_simplexDir_apply n i).comp continuous_subtype_val

/-! ## Mutually inverse -/

/-- The truncation of the backward image is `λ(y) • y`. -/
theorem truncToCenter_sphereToSimplexBoundary (n : ℕ) (y : Sphere n) :
    truncToCenter n (sphereToSimplexBoundary n y) =
      simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) • (y : EuclideanSpace ℝ (Fin (n + 1))) := by
  apply PiLp.ext
  intro j
  dsimp [truncToCenter, sphereToSimplexBoundary]
  rw [simplexDir_castSucc]
  ring

/-- `F(G(y)) = y`. -/
theorem simplexBoundaryToSphere_sphereToSimplexBoundary (n : ℕ) (y : Sphere n) :
    simplexBoundaryToSphere n (⟨sphereToSimplexBoundary n y, sphereToSimplexBoundary_mem n y⟩ :
      SimplexBoundaryFn n) = y := by
  apply Subtype.ext
  dsimp [simplexBoundaryToSphere]
  rw [truncToCenter_sphereToSimplexBoundary n y]
  have hlambda_pos : 0 < simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) :=
    simplexLambda_pos_of_unit n (mem_sphere_zero_iff_norm.mp y.2)
  have hnorm : ‖simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) •
      (y : EuclideanSpace ℝ (Fin (n + 1)))‖ = simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hlambda_pos),
      mem_sphere_zero_iff_norm.mp y.2, mul_one]
  rw [hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hlambda_pos), one_smul]

/-- On the boundary, the minimal weight coordinate is exactly `0`. -/
theorem simplexMin_eq_zero_of_mem_boundary (n : ℕ) {s : Fin (n + 2) → ℝ}
    (hs : s ∈ simplexBoundarySet n) : (⨅ i : Fin (n + 2), s i) = 0 := by
  apply le_antisymm
  · rcases hs.2.2 with ⟨i₀, hi₀⟩
    calc
      (⨅ i : Fin (n + 2), s i) ≤ s i₀ :=
        ciInf_le (f := s) (Set.finite_range s |>.bddBelow) i₀
      _ = 0 := hi₀
  · exact le_ciInf (f := s) (fun i => hs.1 i)

/-- The direction vector of `F(s)` equals `(s - c)/‖u‖` pointwise, where `u` is the
truncated barycenter difference of `s`. -/
theorem simplexDir_of_simplexBoundaryToSphere (n : ℕ) (s : SimplexBoundaryFn n) :
    (∀ i : Fin (n + 2),
      simplexDir n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) i =
        ((s : Fin (n + 2) → ℝ) i - simplexCenter n) / ‖truncToCenter n (s : Fin (n + 2) → ℝ)‖) := by
  let u := truncToCenter n (s : Fin (n + 2) → ℝ)
  let t := ‖u‖
  have htpos : 0 < t := by
    dsimp [t, u]
    exact norm_pos_iff.mpr (truncToCenter_ne_zero n s.2)
  intro i
  refine Fin.lastCases (n := n + 1)
    (motive := fun i => simplexDir n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) i =
      ((s : Fin (n + 2) → ℝ) i - simplexCenter n) / t) ?_ ?_ i
  · -- last coordinate: -∑ y = -(∑u)/t; use the weight-1 total to identify it with (s last - c)/t
    have hsumu : (∑ j : Fin (n + 1), (t⁻¹ • u) j) = (∑ j : Fin (n + 1), u j) / t := by
      calc
        (∑ j : Fin (n + 1), (t⁻¹ • u) j) = ∑ j : Fin (n + 1), (t⁻¹ * u j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rfl
        _ = t⁻¹ * (∑ j : Fin (n + 1), u j) := by
          rw [Finset.mul_sum]
        _ = (∑ j : Fin (n + 1), u j) / t := by
          exact (div_eq_inv_mul (∑ j : Fin (n + 1), u j) t).symm
    have hsumdiff : (∑ j : Fin (n + 1), u j) = simplexCenter n - (s : Fin (n + 2) → ℝ) (Fin.last (n + 1)) := by
      have hsums : (∑ i : Fin (n + 2), (s : Fin (n + 2) → ℝ) i) = 1 := s.2.2.1
      rw [Fin.sum_univ_castSucc] at hsums
      have hsums' : (∑ j : Fin (n + 1), (s : Fin (n + 2) → ℝ) j.castSucc) =
          1 - (s : Fin (n + 2) → ℝ) (Fin.last (n + 1)) := by
        linarith [hsums]
      dsimp [u, truncToCenter]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, hsums']
      have hc' : ((n + 1 : ℕ) : ℝ) * simplexCenter n + simplexCenter n = 1 := by
        calc
          ((n + 1 : ℕ) : ℝ) * simplexCenter n + simplexCenter n
              = (((n + 1 : ℕ) : ℝ) + 1) * simplexCenter n := by ring
          _ = ((n + 2 : ℕ) : ℝ) * simplexCenter n := by
            congr 1
            norm_num [Nat.cast_add]
            ring
          _ = 1 := simplexCenter_total n
      linarith
    simp only [simplexDir_last]
    have hcoe : ((simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) = t⁻¹ • u) := rfl
    rw [hcoe, hsumu, hsumdiff]
    field_simp [ne_of_gt htpos]
    ring
  · intro j
    simp only [simplexDir_castSucc]
    dsimp [simplexBoundaryToSphere, truncToCenter, u, t]
    exact (div_eq_inv_mul ((s : Fin (n + 2) → ℝ) j.castSucc - simplexCenter n)
      ‖truncToCenter n (s : Fin (n + 2) → ℝ)‖).symm

/-- The minimal direction coordinate of `F(s)` is `-c/‖u‖`. -/
theorem simplexMin_of_simplexBoundaryToSphere (n : ℕ) (s : SimplexBoundaryFn n) :
    simplexMin n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) =
      -simplexCenter n / ‖truncToCenter n (s : Fin (n + 2) → ℝ)‖ := by
  let u := truncToCenter n (s : Fin (n + 2) → ℝ)
  let t := ‖u‖
  have htpos : 0 < t := by
    dsimp [t, u]
    exact norm_pos_iff.mpr (truncToCenter_ne_zero n s.2)
  have hdir := simplexDir_of_simplexBoundaryToSphere n s
  calc
    simplexMin n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1)))
        = ⨅ i : Fin (n + 2), ((s : Fin (n + 2) → ℝ) i - simplexCenter n) / t := by
          apply congrArg (fun f : Fin (n + 2) → ℝ => ⨅ i, f i)
          funext i
          exact hdir i
    _ = (⨅ i : Fin (n + 2), ((s : Fin (n + 2) → ℝ) i - simplexCenter n)) / t := by
      apply le_antisymm
      · rcases exists_eq_ciInf_of_finite
          (f := fun i : Fin (n + 2) => (s : Fin (n + 2) → ℝ) i - simplexCenter n) with ⟨i₀, hi₀⟩
        calc
          (⨅ i : Fin (n + 2), ((s : Fin (n + 2) → ℝ) i - simplexCenter n) / t)
              ≤ ((s : Fin (n + 2) → ℝ) i₀ - simplexCenter n) / t :=
            ciInf_le (f := fun i : Fin (n + 2) => ((s : Fin (n + 2) → ℝ) i - simplexCenter n) / t)
              (Set.finite_range _ |>.bddBelow) i₀
          _ = (⨅ i : Fin (n + 2), ((s : Fin (n + 2) → ℝ) i - simplexCenter n)) / t := by
            rw [hi₀]
      · exact le_ciInf (fun i =>
          div_le_div_of_nonneg_right
            (ciInf_le (f := fun i : Fin (n + 2) => (s : Fin (n + 2) → ℝ) i - simplexCenter n)
              (Set.finite_range _ |>.bddBelow) i) (le_of_lt htpos))
    _ = ((⨅ i : Fin (n + 2), (s : Fin (n + 2) → ℝ) i) - simplexCenter n) / t := by
      congr 1
      apply le_antisymm
      · rcases exists_eq_ciInf_of_finite (f := fun i : Fin (n + 2) => (s : Fin (n + 2) → ℝ) i)
          with ⟨i₀, hi₀⟩
        calc
          (⨅ i : Fin (n + 2), ((s : Fin (n + 2) → ℝ) i - simplexCenter n))
              ≤ ((s : Fin (n + 2) → ℝ) i₀ - simplexCenter n) :=
            ciInf_le (f := fun i : Fin (n + 2) => ((s : Fin (n + 2) → ℝ) i - simplexCenter n))
              (Set.finite_range _ |>.bddBelow) i₀
          _ = (⨅ i : Fin (n + 2), (s : Fin (n + 2) → ℝ) i) - simplexCenter n := by
            rw [hi₀]
      · exact le_ciInf (fun i => sub_le_sub_right
          (ciInf_le (f := fun i : Fin (n + 2) => (s : Fin (n + 2) → ℝ) i)
            (Set.finite_range _ |>.bddBelow) i) (simplexCenter n))
    _ = -simplexCenter n / t := by
      rw [simplexMin_eq_zero_of_mem_boundary n s.2]
      ring

/-- `G(F(s)) = s`. -/
theorem sphereToSimplexBoundary_simplexBoundaryToSphere (n : ℕ) (s : SimplexBoundaryFn n) :
    sphereToSimplexBoundaryFn n (simplexBoundaryToSphere n s) = s := by
  apply Subtype.ext
  dsimp [sphereToSimplexBoundaryFn]
  let u := truncToCenter n (s : Fin (n + 2) → ℝ)
  let t := ‖u‖
  have htpos : 0 < t := by
    dsimp [t, u]
    exact norm_pos_iff.mpr (truncToCenter_ne_zero n s.2)
  have hlambda : simplexLambda n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) = t := by
    dsimp [simplexLambda, t]
    rw [simplexMin_of_simplexBoundaryToSphere n s]
    have hc : simplexCenter n ≠ 0 := ne_of_gt (simplexCenter_pos n)
    field_simp [hc, ne_of_gt htpos]
    ring
  apply funext
  intro i
  have hdir := simplexDir_of_simplexBoundaryToSphere n s
  dsimp [sphereToSimplexBoundary]
  calc
    simplexCenter n + simplexLambda n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) *
        simplexDir n (simplexBoundaryToSphere n s : EuclideanSpace ℝ (Fin (n + 1))) i
        = simplexCenter n + t * (((s : Fin (n + 2) → ℝ) i - simplexCenter n) / t) := by
          rw [hlambda, hdir i]
    _ = (s : Fin (n + 2) → ℝ) i := by
      field_simp [ne_of_gt htpos]
      ring

/-! ## The homeomorphism (function-space model) -/

/-- **DAG node 9.** The boundary of the standard `(n+1)`-simplex (function-space model)
is homeomorphic to the `n`-sphere. -/
def simplexBoundaryFnHomeoSphere (n : ℕ) : SimplexBoundaryFn n ≃ₜ Sphere n where
  toEquiv :=
    { toFun := simplexBoundaryToSphere n
      invFun := sphereToSimplexBoundaryFn n
      left_inv := fun s => sphereToSimplexBoundary_simplexBoundaryToSphere n s
      right_inv := fun y => simplexBoundaryToSphere_sphereToSimplexBoundary n y }
  continuous_toFun := continuous_simplexBoundaryToSphere n
  continuous_invFun := continuous_sphereToSimplexBoundaryFn n

/-! ## Transfer to `Convexity.StdSimplex` -/

/-- The boundary of the standard simplex in the `Convexity.StdSimplex ℝ (Fin (n+2))`
model: exactly the statement recorded in `MoiseBranch.simplexBoundaryHomeoSphere`. -/
abbrev SimplexBoundary (n : ℕ) :=
  {x : Convexity.StdSimplex ℝ (Fin (n + 2)) //
    0 ∈ Set.range fun i : Fin (n + 2) => x.weights i}

/-- The range of the weights embedding is the closed simplex
`{s | 0 ≤ s ∧ ∑ s = 1}` (function-space form). -/
theorem range_weights_eq_simplex (n : ℕ) :
    Set.range (fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) =>
      (t.weights : Fin (n + 2) → ℝ)) = {s : Fin (n + 2) → ℝ | 0 ≤ s ∧ (∑ i, s i) = 1} := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext s
  constructor
  · intro h
    rw [Set.mem_inter_iff, Set.mem_iInter] at h
    rcases h with ⟨hle, hsum⟩
    constructor
    · rw [Pi.le_def]
      intro i
      exact hle i
    · exact hsum
  · intro h
    rw [Set.mem_inter_iff, Set.mem_iInter]
    rcases h with ⟨hle, hsum⟩
    rw [Pi.le_def] at hle
    exact ⟨hle, hsum⟩

/-- Under the weights embedding, the boundary of the simplex (some coordinate `0`)
corresponds to the function-space boundary set. -/
theorem image_weights_boundary_eq (n : ℕ) :
    (fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => (t.weights : Fin (n + 2) → ℝ)) ''
      {x : Convexity.StdSimplex ℝ (Fin (n + 2)) |
        0 ∈ Set.range fun i : Fin (n + 2) => x.weights i} = simplexBoundarySet n := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 ≤ (x.weights : Fin (n + 2) → ℝ) ∧
      (∑ i : Fin (n + 2), x.weights i) = 1 ∧ 0 ∈ Set.range (fun i : Fin (n + 2) => x.weights i)
    constructor
    · rw [Pi.le_def]
      intro i
      exact x.weights_nonneg i
    · constructor
      · exact (Convexity.StdSimplex.total_of_fintype x)
      · exact hx
  · intro hs
    change 0 ≤ s ∧ (∑ i, s i) = 1 ∧ 0 ∈ Set.range s at hs
    rcases hs with ⟨hnonneg, hsum, hzero⟩
    refine ⟨⟨Finsupp.equivFunOnFinite.symm s, ?_, ?_⟩, ?_, ?_⟩
    · intro i
      rw [Finsupp.coe_equivFunOnFinite_symm]
      rw [Pi.le_def] at hnonneg
      exact hnonneg i
    · rw [Finsupp.sum_fintype]
      · simpa [Finsupp.coe_equivFunOnFinite_symm] using hsum
      · intro i
        simp
    · simpa [Finsupp.coe_equivFunOnFinite_symm] using hzero
    · change (Finsupp.equivFunOnFinite.symm s : Fin (n + 2) → ℝ) = s
      exact Finsupp.coe_equivFunOnFinite_symm s

/-- The `Convexity.StdSimplex`-model boundary is homeomorphic to the function-space model,
via the weights embedding. -/
def simplexBoundaryHomeoBoundaryFn (n : ℕ) : SimplexBoundary n ≃ₜ SimplexBoundaryFn n := by
  let e := Convexity.StdSimplex.isEmbedding_toFun_comp_weights (R := ℝ) (M := Fin (n + 2))
  exact (e.homeomorphImage
    {x : Convexity.StdSimplex ℝ (Fin (n + 2)) |
      0 ∈ Set.range fun i : Fin (n + 2) => x.weights i}).trans
    (Homeomorph.setCongr (image_weights_boundary_eq n))

/-- **DAG node 9, exact ledger statement.** The boundary of the standard `(n+1)`-simplex
is homeomorphic to the `n`-sphere: `∂Δⁿ⁺¹ ≃ₜ 𝕊ⁿ`. -/
def simplexBoundaryHomeoSphere (n : ℕ) :
    {x : Convexity.StdSimplex ℝ (Fin (n + 2)) //
      0 ∈ Set.range fun i : Fin (n + 2) => x.weights i} ≃ₜ Sphere n :=
  (simplexBoundaryHomeoBoundaryFn n).trans (simplexBoundaryFnHomeoSphere n)

/-! ## Audits: compactness, T2, nonemptiness, shape examples -/

/-- **Compactness audit.** `∂Δⁿ⁺¹` is compact (transferred from the compact sphere). -/
instance simplexBoundaryCompactSpace (n : ℕ) : CompactSpace (SimplexBoundary n) :=
  Homeomorph.compactSpace (simplexBoundaryHomeoSphere n).symm

/-- **T2 audit.** `∂Δⁿ⁺¹` is Hausdorff (transferred from the sphere). -/
instance simplexBoundaryT2Space (n : ℕ) : T2Space (SimplexBoundary n) :=
  Homeomorph.t2Space (simplexBoundaryHomeoSphere n).symm

/-- **Nonemptiness audit.** `∂Δⁿ⁺¹` is nonempty: the vertex `e₀` of the simplex
(weight 1 at vertex `0`) has vertex `1` with weight `0`, so it lies on the boundary. -/
instance simplexBoundaryNonempty (n : ℕ) : Nonempty (SimplexBoundary n) :=
  Nonempty.map (simplexBoundaryHomeoSphere n).symm (sphereNonempty n)

/-- **Shape example.** `∂Δ⁴` is the standard triangulation of the 3-sphere: the boundary
of the 4-simplex realizes `𝕊³ ⊂ ℝ⁴`. -/
example : SimplexBoundary 3 ≃ₜ Sphere 3 :=
  simplexBoundaryHomeoSphere 3

/-- **Shape example.** `∂Δ²` (the triangle boundary) is the circle `𝕊¹`. -/
example : SimplexBoundary 1 ≃ₜ Sphere 1 :=
  simplexBoundaryHomeoSphere 1

/-- **Shape example.** `∂Δ¹` is two points, i.e. the 0-sphere `𝕊⁰`. -/
example : SimplexBoundary 0 ≃ₜ Sphere 0 :=
  simplexBoundaryHomeoSphere 0

end Poincare.D12.TriangulationTopology
