/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib
import Poincare.D12.TriangulationTopology.SimplexBoundary

/-!
# Poincare.D12.TriangulationTopology.SimplexCone

**DAG node 9, second half.** The standard `(n+1)`-simplex `Δⁿ⁺¹` is homeomorphic to the
closed `(n+1)`-disk `Dⁿ⁺¹`, by the radial cone-over-boundary form of the barycenter map,
composed with the already proved cone homeomorphism `coneQuotHomeoDisk`.  Three exact
statements with actual topological spaces:

1. `sphereConeHomeoSimplex n : ConeQuot n ≃ₜ SimplexFn n` — the cone over the `n`-sphere
   realizes the standard `(n+1)`-simplex: `(y, t) ↦ (1-t)·c + t·b(y)` where `c` is the
   barycenter and `b(y) ∈ ∂Δⁿ⁺¹` the boundary exit point of the ray from `c` in direction
   `(y, -∑y)`.  This is the sphere-cone route.
2. `simplexHomeoBoundaryCone n : SimplexFn n ≃ₜ SimplexBoundaryCone n` — the literal
   radial form: `Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹)`, the cone over the boundary of the simplex, by
   `(b, t) ↦ (1-t)·c + t·b` with inverse `x ↦ (c + (x-c)/t(x), t(x))`,
   `t(x) = (c - ⨅ᵢ xᵢ)/c` the radial exit time (the minimum coordinate stops the ray).
3. `simplexHomeoDisk n : Convexity.StdSimplex ℝ (Fin (n+2)) ≃ₜ Disk (n+1)` — the exact
   ledger statement `Δⁿ⁺¹ ≅ Dⁿ⁺¹`, obtained by transferring model (1) to
   `Convexity.StdSimplex` via the weights embedding and composing with `coneQuotHomeoDisk`.
   For `n = 2`: the tetrahedron is homeomorphic to the closed 3-ball.

Continuity goes through the quotient (`continuous_quot_lift`); bijectivity is checked by
coordinate algebra on `Fin (n+2)` (the truncation identities
`truncToCenter n (c + tλ(y)d(y)) = tλ(y) • y` and the exit-time bound `‖u‖ ≤ λ(y)` from
the minimal coordinate), and compactness of the cone quotient plus T2 of the simplex
subtype finish the homeomorphism (`Continuous.homeoOfEquivCompactToT2`).

## Provenance of external mathematics

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by lake-manifest.json),
  Apache-2.0: all imported lemmas.  The radial cone homeomorphism between a simplex and a
  cone over its boundary is classical; all proofs here are original to this worktree.
-/

noncomputable section

open scoped Topology
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## The full standard simplex (function-space model) -/

/-- The closed standard `(n+1)`-simplex as a subset of `ℝⁿ⁺²`: nonnegative weights with
total weight 1. -/
def simplexSet (n : ℕ) : Set (Fin (n + 2) → ℝ) :=
  {s | 0 ≤ s ∧ (∑ i, s i) = 1}

/-- Function-space model of `Δⁿ⁺¹` (subtype topology of `ℝⁿ⁺²`). -/
abbrev SimplexFn (n : ℕ) := simplexSet n

/-- **Nonemptiness audit.** `Δⁿ⁺¹` is nonempty (it contains the barycenter). -/
instance simplexFnNonempty (n : ℕ) : Nonempty (SimplexFn n) :=
  ⟨fun _ => simplexCenter n, by
    change 0 ≤ (fun _ : Fin (n + 2) => simplexCenter n) ∧
      (∑ i : Fin (n + 2), simplexCenter n) = 1
    constructor
    · rw [Pi.le_def]
      intro i
      exact le_of_lt (simplexCenter_pos n)
    · rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, simplexCenter_total n]⟩

/-- **T2 audit.** `Δⁿ⁺¹` is Hausdorff (subtype of `ℝⁿ⁺²`). -/
instance simplexFnT2Space (n : ℕ) : T2Space (SimplexFn n) :=
  inferInstance

/-! ## Route 1: the cone over the sphere realizes the simplex -/

/-- The cone map `(y, t) ↦ (1-t)·c + t·b(y)` where `b(y) = sphereToSimplexBoundary n y`
is the boundary exit point of the ray from the barycenter in direction `(y, -∑y)`. -/
def simplexConeMap (n : ℕ) (p : Sphere n × Set.Icc (0 : ℝ) 1) : Fin (n + 2) → ℝ :=
  fun i => (1 - (p.2 : ℝ)) * simplexCenter n + (p.2 : ℝ) * sphereToSimplexBoundary n p.1 i

/-- The cone map lands in the simplex: convex combination of the barycenter and the
boundary point `b(y)`. -/
theorem simplexConeMap_mem (n : ℕ) (p : Sphere n × Set.Icc (0 : ℝ) 1) :
    simplexConeMap n p ∈ simplexSet n := by
  change 0 ≤ simplexConeMap n p ∧ (∑ i, simplexConeMap n p i) = 1
  have hb := sphereToSimplexBoundary_mem n p.1
  rcases hb with ⟨hb_nonneg, hb_sum, _⟩
  constructor
  · rw [Pi.le_def]
    intro i
    dsimp [simplexConeMap]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2.2) (le_of_lt (simplexCenter_pos n)))
      (mul_nonneg p.2.2.1 (hb_nonneg i))
  · dsimp [simplexConeMap]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hc : (∑ i : Fin (n + 2), simplexCenter n) = 1 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, simplexCenter_total n]
    rw [hc, hb_sum]
    ring

/-- Continuity of the coordinate `y ↦ b(y) i` of the boundary exit point. -/
theorem continuous_sphereToSimplexBoundary_apply (n : ℕ) (i : Fin (n + 2)) :
    Continuous (fun y : Sphere n => sphereToSimplexBoundary n y i) := by
  dsimp [sphereToSimplexBoundary]
  exact Continuous.add continuous_const
    (Continuous.mul (continuous_sphere_simplexLambda n)
      ((continuous_simplexDir_apply n i).comp continuous_subtype_val))

/-- Continuity of the boundary exit map `y ↦ b(y)`. -/
theorem continuous_sphereToSimplexBoundary (n : ℕ) :
    Continuous (fun y : Sphere n => sphereToSimplexBoundary n y) := by
  apply continuous_pi
  intro i
  exact continuous_sphereToSimplexBoundary_apply n i

/-- The cone map is continuous. -/
theorem continuous_simplexConeMap (n : ℕ) :
    Continuous (fun p : Sphere n × Set.Icc (0 : ℝ) 1 => simplexConeMap n p) := by
  apply continuous_pi
  intro i
  dsimp [simplexConeMap]
  refine Continuous.add ?_ ?_
  · exact Continuous.mul (Continuous.sub continuous_const
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  · exact Continuous.mul (continuous_subtype_val.comp continuous_snd)
      ((continuous_sphereToSimplexBoundary_apply n i).comp continuous_fst)

/-- The cone map respects the cone relation (the base `t = 0` collapses to the
barycenter). -/
theorem simplexConeMap_respects (n : ℕ) (p q : Sphere n × Set.Icc (0 : ℝ) 1) :
    coneRel n p q → simplexConeMap n p = simplexConeMap n q := by
  intro h
  rcases h with h | ⟨hp, hq⟩
  · subst h
    rfl
  · funext i
    dsimp [simplexConeMap]
    rw [hp, hq]
    ring

/-- The descended cone map `ConeQuot n → Δⁿ⁺¹`. -/
noncomputable def simplexConeMapQuot (n : ℕ) : ConeQuot n → SimplexFn n :=
  Quot.lift (fun p : Sphere n × Set.Icc (0 : ℝ) 1 =>
      ⟨simplexConeMap n p, simplexConeMap_mem n p⟩)
    (fun p q h => Subtype.ext (simplexConeMap_respects n p q h))

/-- Continuity of the descended cone map. -/
theorem continuous_simplexConeMapQuot (n : ℕ) : Continuous (simplexConeMapQuot n) := by
  refine continuous_quot_lift
    (fun p q h => Subtype.ext (simplexConeMap_respects n p q h)) ?_
  refine Continuous.subtype_mk ?_ (fun p => simplexConeMap_mem n p)
  exact continuous_simplexConeMap n

/-- The truncated barycenter difference of the cone image is `tλ(y) • y`: for each
`j < n+1`, `(1-t)c + t(c + λd) - c` has `j`-coordinate `tλ(y)·yⱼ`. -/
theorem truncToCenter_simplexConeMap (n : ℕ) (p : Sphere n × Set.Icc (0 : ℝ) 1) :
    truncToCenter n (simplexConeMap n p) =
      ((p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
        (p.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
  apply PiLp.ext
  intro j
  dsimp [truncToCenter, simplexConeMap, sphereToSimplexBoundary]
  rw [simplexDir_castSucc]
  ring

/-- A point of the simplex with truncated difference `u = ‖u‖ • y` is
`c + ‖u‖ · d(y)` pointwise (`d(y) = (y, -∑y)`), using the weight-1 total to identify the
last coordinate. -/
theorem simplex_point_eq_center_add_norm_mul_dir (n : ℕ) {x : SimplexFn n} {y : Sphere n}
    (hy : truncToCenter n (x : Fin (n + 2) → ℝ) = ‖truncToCenter n (x : Fin (n + 2) → ℝ)‖ •
      (y : EuclideanSpace ℝ (Fin (n + 1)))) :
    (x : Fin (n + 2) → ℝ) = fun i => simplexCenter n +
      ‖truncToCenter n (x : Fin (n + 2) → ℝ)‖ * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i := by
  funext i
  let u := truncToCenter n (x : Fin (n + 2) → ℝ)
  refine Fin.lastCases (n := n + 1)
    (motive := fun i => (x : Fin (n + 2) → ℝ) i = simplexCenter n + ‖u‖ * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i)
    ?_ ?_ i
  · -- last coordinate: weight-1 total identifies it with `c - ‖u‖·∑y`
    have huj : ∀ j : Fin (n + 1), u j = ‖u‖ * (y : EuclideanSpace ℝ (Fin (n + 1))) j := by
      intro j
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v j) hy
      simpa [Pi.smul_apply] using h
    have hsum : (∑ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) = 1 := x.2.2
    rw [Fin.sum_univ_castSucc] at hsum
    have hfirst : (∑ j : Fin (n + 1), (x : Fin (n + 2) → ℝ) j.castSucc) =
        ((n + 1 : ℕ) : ℝ) * simplexCenter n +
          ‖u‖ * (∑ j : Fin (n + 1), (y : EuclideanSpace ℝ (Fin (n + 1))) j) := by
      calc
        (∑ j : Fin (n + 1), (x : Fin (n + 2) → ℝ) j.castSucc)
            = ∑ j : Fin (n + 1), (simplexCenter n + u j) := by
              apply Finset.sum_congr rfl
              intro j hj
              dsimp [u, truncToCenter]
              ring
        _ = (∑ j : Fin (n + 1), simplexCenter n) + ∑ j : Fin (n + 1), u j := by
              rw [Finset.sum_add_distrib]
        _ = ((n + 1 : ℕ) : ℝ) * simplexCenter n + ∑ j : Fin (n + 1), u j := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        _ = ((n + 1 : ℕ) : ℝ) * simplexCenter n +
              ‖u‖ * (∑ j : Fin (n + 1), (y : EuclideanSpace ℝ (Fin (n + 1))) j) := by
              rw [Finset.mul_sum]
              exact congrArg (((n + 1 : ℕ) : ℝ) * simplexCenter n + ·)
                (Finset.sum_congr rfl (fun j _ => huj j))
    calc
      (x : Fin (n + 2) → ℝ) (Fin.last (n + 1))
          = 1 - ((n + 1 : ℕ) : ℝ) * simplexCenter n -
              ‖u‖ * (∑ j : Fin (n + 1), (y : EuclideanSpace ℝ (Fin (n + 1))) j) := by
            linarith [hsum, hfirst]
      _ = simplexCenter n + ‖u‖ * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last (n + 1)) := by
        rw [simplexDir_last]
        have hc : ((n + 2 : ℕ) : ℝ) * simplexCenter n = 1 := simplexCenter_total n
        have hnat : ((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.cast_add]
        nlinarith
  · intro j
    have huj : u j = ‖u‖ * (y : EuclideanSpace ℝ (Fin (n + 1))) j := by
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v j) hy
      simpa [Pi.smul_apply] using h
    have hxj : (x : Fin (n + 2) → ℝ) j.castSucc = simplexCenter n + u j := by
      dsimp [u, truncToCenter]
      ring
    rw [hxj, huj, simplexDir_castSucc]

/-- **Injectivity.** `(1-t)c + t·b(y) = (1-t')c + t'·b(y')` forces `coneRel (y,t) (y',t')`:
the truncation is `tλ(y)•y`, so equal values have equal `tλ` and then equal `y` and `t`
(unless `t = t' = 0`, the collapsed base). -/
theorem simplexConeMapQuot_injective (n : ℕ) : Function.Injective (simplexConeMapQuot n) := by
  intro a b h
  revert h b
  refine Quot.inductionOn a ?_
  intro p b h
  revert h
  refine Quot.inductionOn b ?_
  intro q hpq
  apply Quot.sound
  have hval' : simplexConeMapQuot n (Quot.mk (coneRel n) p) =
      simplexConeMapQuot n (Quot.mk (coneRel n) q) := hpq
  have hval : simplexConeMap n p = simplexConeMap n q := by
    have hh : (⟨simplexConeMap n p, simplexConeMap_mem n p⟩ : SimplexFn n) =
        ⟨simplexConeMap n q, simplexConeMap_mem n q⟩ := by
      simpa [simplexConeMapQuot] using hval'
    exact congrArg Subtype.val hh
  have htrunc : truncToCenter n (simplexConeMap n p) = truncToCenter n (simplexConeMap n q) := by
    rw [hval]
  rw [truncToCenter_simplexConeMap n p, truncToCenter_simplexConeMap n q] at htrunc
  have hlam_pos_p : 0 < simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) :=
    simplexLambda_pos_of_unit n (mem_sphere_zero_iff_norm.mp p.1.2)
  have hlam_pos_q : 0 < simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) :=
    simplexLambda_pos_of_unit n (mem_sphere_zero_iff_norm.mp q.1.2)
  have hnorm : (p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) =
      (q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
    have hp : ‖((p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
        (p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = (p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg p.2.2.1 (le_of_lt hlam_pos_p)),
        mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
    have hq : ‖((q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
        (q.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = (q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg q.2.2.1 (le_of_lt hlam_pos_q)),
        mem_sphere_zero_iff_norm.mp q.1.2, mul_one]
    calc
      (p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1)))
          = ‖((p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
              (p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := hp.symm
      _ = ‖((q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
              (q.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := by rw [htrunc]
      _ = (q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := hq
  by_cases h0 : (p.2 : ℝ) = 0
  · right
    have hq0 : (q.2 : ℝ) = 0 := by
      have hq' : (q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
        rw [← hnorm, h0, zero_mul]
      exact (mul_eq_zero.mp hq').resolve_right (ne_of_gt hlam_pos_q)
    exact ⟨h0, hq0⟩
  · left
    have ht_pos : 0 < (p.2 : ℝ) := lt_of_le_of_ne p.2.2.1 (Ne.symm h0)
    have hlam_ne : simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 :=
      ne_of_gt hlam_pos_p
    have hscal_ne : (p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 :=
      mul_ne_zero (ne_of_gt ht_pos) hlam_ne
    have hy : (p.1 : EuclideanSpace ℝ (Fin (n + 1))) =
        (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
      calc
        (p.1 : EuclideanSpace ℝ (Fin (n + 1)))
            = ((p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))))⁻¹ •
                (((p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
                  (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) := by
              rw [smul_smul, inv_mul_cancel₀ hscal_ne, one_smul]
        _ = ((p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))))⁻¹ •
                (((q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) •
                  (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) := by rw [htrunc]
        _ = (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
          rw [← hnorm, smul_smul, inv_mul_cancel₀ hscal_ne, one_smul]
    have ht : (p.2 : ℝ) = (q.2 : ℝ) := by
      have hlam : simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) =
          simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by rw [hy]
      calc
        (p.2 : ℝ) = (p.2 : ℝ) * simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))) *
            (simplexLambda n (p.1 : EuclideanSpace ℝ (Fin (n + 1))))⁻¹ := by
              field_simp [hlam_ne]
        _ = (q.2 : ℝ) * simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))) *
            (simplexLambda n (q.1 : EuclideanSpace ℝ (Fin (n + 1))))⁻¹ := by rw [hnorm, hlam]
        _ = (q.2 : ℝ) := by
          field_simp [ne_of_gt hlam_pos_q]
    apply Prod.ext
    · apply Subtype.ext
      exact hy
    · apply Subtype.ext
      exact ht

/-- **Surjectivity.** Every simplex point is `c + tλ(y)·d(y)` for the normalized
truncation `y` of its barycenter difference and `t = ‖u‖/λ(y) ∈ [0,1]`; the bound
`‖u‖ ≤ λ(y)` comes from the minimal coordinate `c + ‖u‖·⨅d ≥ 0` and `⨅d = -c/λ(y) < 0`.
The barycenter itself is the collapsed base `t = 0`. -/
theorem simplexConeMapQuot_surjective (n : ℕ) : Function.Surjective (simplexConeMapQuot n) := by
  intro x
  let u := truncToCenter n (x : Fin (n + 2) → ℝ)
  by_cases h0 : u = 0
  · -- the barycenter: any sphere point with `t = 0` maps to it
    let y0 : Sphere n := Classical.choice (sphereNonempty n)
    refine ⟨Quot.mk (coneRel n) (y0, ⟨0, by norm_num⟩), ?_⟩
    apply Subtype.ext
    funext i
    have hx : (x : Fin (n + 2) → ℝ) = fun _ => simplexCenter n := by
      have hf : (fun j : Fin (n + 1) => (x : Fin (n + 2) → ℝ) j.castSucc - simplexCenter n) = 0 := by
        dsimp [truncToCenter, u] at h0
        exact congrArg (WithLp.equiv 2 (Fin (n + 1) → ℝ)) h0
      funext j
      refine Fin.lastCases (n := n + 1)
        (motive := fun j => (x : Fin (n + 2) → ℝ) j = simplexCenter n) ?_ ?_ j
      · have hsum : (∑ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) = 1 := x.2.2
        rw [Fin.sum_univ_castSucc] at hsum
        have hfirst : (∑ j : Fin (n + 1), (x : Fin (n + 2) → ℝ) j.castSucc) =
            ((n + 1 : ℕ) : ℝ) * simplexCenter n := by
          calc
            (∑ j : Fin (n + 1), (x : Fin (n + 2) → ℝ) j.castSucc)
                = ∑ j : Fin (n + 1), simplexCenter n := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hj' : (x : Fin (n + 2) → ℝ) j.castSucc - simplexCenter n = 0 :=
                    congr_fun hf j
                  exact sub_eq_zero.mp hj'
            _ = ((n + 1 : ℕ) : ℝ) * simplexCenter n := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hc : ((n + 2 : ℕ) : ℝ) * simplexCenter n = 1 := simplexCenter_total n
        calc
          (x : Fin (n + 2) → ℝ) (Fin.last (n + 1)) = 1 - ((n + 1 : ℕ) : ℝ) * simplexCenter n := by
            linarith [hsum, hfirst]
          _ = simplexCenter n := by
            have hnat : ((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.cast_add]
            nlinarith [hc, hnat]
      · intro j
        have hj' : (x : Fin (n + 2) → ℝ) j.castSucc - simplexCenter n = 0 := congr_fun hf j
        exact sub_eq_zero.mp hj'
    rw [hx]
    simp [simplexConeMapQuot, simplexConeMap, sphereToSimplexBoundary]
  · -- non-barycenter: radial decomposition
    have hnorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hunit : (‖u‖)⁻¹ • u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
      exact inv_mul_cancel₀ hnorm_ne
    let y : Sphere n := ⟨(‖u‖)⁻¹ • u, hunit⟩
    have hyu : u = ‖u‖ • (y : EuclideanSpace ℝ (Fin (n + 1))) := by
      dsimp [y]
      rw [smul_smul, mul_inv_cancel₀ hnorm_ne, one_smul]
    have hlam_pos : 0 < simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) :=
      simplexLambda_pos_of_unit n (mem_sphere_zero_iff_norm.mp y.2)
    have hxdir : (x : Fin (n + 2) → ℝ) = fun i => simplexCenter n +
        ‖u‖ * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i :=
      simplex_point_eq_center_add_norm_mul_dir n (by
        simpa [u] using hyu)
    have hu_le_lam : ‖u‖ ≤ simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
      have hm_neg : simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) < 0 :=
        simplexMin_neg_of_unit n (mem_sphere_zero_iff_norm.mp y.2)
      rcases simplexMin_attains n (y : EuclideanSpace ℝ (Fin (n + 1))) with ⟨i₀, hi₀⟩
      have hx_nonneg : 0 ≤ (x : Fin (n + 2) → ℝ) i₀ := x.2.1 i₀
      have hcoord : (x : Fin (n + 2) → ℝ) i₀ = simplexCenter n +
          ‖u‖ * simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
        calc
          (x : Fin (n + 2) → ℝ) i₀ = simplexCenter n +
              ‖u‖ * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i₀ := congr_fun hxdir i₀
          _ = simplexCenter n + ‖u‖ * simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
            rw [hi₀]
      have hineq : ‖u‖ * (-simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1)))) ≤ simplexCenter n := by
        have hle : 0 ≤ simplexCenter n + ‖u‖ * simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
          rwa [← hcoord]
        linarith [hle]
      have hm_ne : simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := ne_of_lt hm_neg
      calc
        ‖u‖ = ‖u‖ * (-simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1)))) *
            (-simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))))⁻¹ := by
              field_simp [neg_ne_zero.mpr hm_ne]
        _ ≤ simplexCenter n * (-simplexMin n (y : EuclideanSpace ℝ (Fin (n + 1))))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hineq
            (inv_nonneg.mpr (le_of_lt (neg_pos.mpr hm_neg)))
        _ = simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) := by
          dsimp [simplexLambda]
          ring
    have htmem : ‖u‖ / simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor
      · exact div_nonneg (norm_nonneg u) (le_of_lt hlam_pos)
      · rw [div_le_iff₀ hlam_pos]
        simpa using hu_le_lam
    let t : Set.Icc (0 : ℝ) 1 := ⟨‖u‖ / simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))), htmem⟩
    refine ⟨Quot.mk (coneRel n) (y, t), ?_⟩
    apply Subtype.ext
    funext i
    calc
      simplexConeMap n (y, t) i = simplexCenter n +
          ((t : ℝ) * simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1)))) *
            simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i := by
        dsimp [simplexConeMap, sphereToSimplexBoundary]
        ring
      _ = simplexCenter n + ‖u‖ * simplexDir n (y : EuclideanSpace ℝ (Fin (n + 1))) i := by
        have htlam : (t : ℝ) * simplexLambda n (y : EuclideanSpace ℝ (Fin (n + 1))) = ‖u‖ := by
          dsimp [t]
          exact div_mul_cancel₀ (‖u‖) (ne_of_gt hlam_pos)
        rw [htlam]
      _ = (x : Fin (n + 2) → ℝ) i := by
        exact (congr_fun hxdir i).symm

/-- **Route 1 theorem.** The cone over the `n`-sphere realizes the standard `(n+1)`-simplex
(the radial cone-over-boundary form through `∂Δⁿ⁺¹ ≅ 𝕊ⁿ`). -/
noncomputable def sphereConeHomeoSimplex (n : ℕ) : ConeQuot n ≃ₜ SimplexFn n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (simplexConeMapQuot n)
      ⟨simplexConeMapQuot_injective n, simplexConeMapQuot_surjective n⟩)
    (continuous_simplexConeMapQuot n)

/-- The simplex is homeomorphic to the cone over the sphere (inverse direction). -/
noncomputable def simplexHomeoConeQuot (n : ℕ) : SimplexFn n ≃ₜ ConeQuot n :=
  (sphereConeHomeoSimplex n).symm

/-! ## Route 2: the simplex is the cone over its own boundary (literal radial form) -/

/-- The cone relation on the boundary `∂Δⁿ⁺¹`: the base `t = 0` is collapsed. -/
def simplexBoundaryConeRel (n : ℕ) :
    SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1 → SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1 → Prop :=
  fun p q => p = q ∨ ((p.2 : ℝ) = 0 ∧ (q.2 : ℝ) = 0)

/-- The cone over the boundary of the standard `(n+1)`-simplex. -/
abbrev SimplexBoundaryCone (n : ℕ) : Type := Quot (simplexBoundaryConeRel n)

/-- The cone map `(b, t) ↦ (1-t)·c + t·b`: the barycenter joined to the boundary point
`b` along the radial segment. -/
def simplexBoundaryConeMap (n : ℕ) (p : SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1) :
    Fin (n + 2) → ℝ :=
  fun i => (1 - (p.2 : ℝ)) * simplexCenter n + (p.2 : ℝ) * (p.1 : Fin (n + 2) → ℝ) i

/-- The cone map lands in the simplex: convex combination of the barycenter and a
boundary point. -/
theorem simplexBoundaryConeMap_mem (n : ℕ) (p : SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1) :
    simplexBoundaryConeMap n p ∈ simplexSet n := by
  change 0 ≤ simplexBoundaryConeMap n p ∧ (∑ i, simplexBoundaryConeMap n p i) = 1
  have hb : 0 ≤ (p.1 : Fin (n + 2) → ℝ) := p.1.2.1
  constructor
  · rw [Pi.le_def]
    intro i
    dsimp [simplexBoundaryConeMap]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2.2) (le_of_lt (simplexCenter_pos n)))
      (mul_nonneg p.2.2.1 (hb i))
  · dsimp [simplexBoundaryConeMap]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsumc : (∑ i : Fin (n + 2), simplexCenter n) = 1 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, simplexCenter_total n]
    rw [hsumc, p.1.2.2.1]
    ring

/-- The cone map is continuous. -/
theorem continuous_simplexBoundaryConeMap (n : ℕ) :
    Continuous (fun p : SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1 => simplexBoundaryConeMap n p) := by
  apply continuous_pi
  intro i
  dsimp [simplexBoundaryConeMap]
  refine Continuous.add ?_ ?_
  · exact Continuous.mul (Continuous.sub continuous_const
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  · exact Continuous.mul (continuous_subtype_val.comp continuous_snd)
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))

/-- The cone map respects the cone relation (the base collapses to the barycenter). -/
theorem simplexBoundaryConeMap_respects (n : ℕ) (p q : SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1) :
    simplexBoundaryConeRel n p q → simplexBoundaryConeMap n p = simplexBoundaryConeMap n q := by
  intro h
  rcases h with h | ⟨hp, hq⟩
  · subst h
    rfl
  · funext i
    dsimp [simplexBoundaryConeMap]
    rw [hp, hq]
    ring

/-- The descended cone map `Cone(∂Δⁿ⁺¹) → Δⁿ⁺¹`. -/
noncomputable def simplexBoundaryConeMapQuot (n : ℕ) : SimplexBoundaryCone n → SimplexFn n :=
  Quot.lift (fun p : SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1 =>
      ⟨simplexBoundaryConeMap n p, simplexBoundaryConeMap_mem n p⟩)
    (fun p q h => Subtype.ext (simplexBoundaryConeMap_respects n p q h))

/-- Continuity of the descended cone map. -/
theorem continuous_simplexBoundaryConeMapQuot (n : ℕ) :
    Continuous (simplexBoundaryConeMapQuot n) := by
  refine continuous_quot_lift
    (fun p q h => Subtype.ext (simplexBoundaryConeMap_respects n p q h)) ?_
  refine Continuous.subtype_mk ?_ (fun p => simplexBoundaryConeMap_mem n p)
  exact continuous_simplexBoundaryConeMap n

/-- The minimum weight is at most the barycenter weight (average argument). -/
theorem simplexMin_le_center (n : ℕ) (x : SimplexFn n) :
    (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) ≤ simplexCenter n := by
  have hsum : (∑ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) = 1 := x.2.2
  have hmul : ((n + 2 : ℕ) : ℝ) * (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) ≤ 1 := by
    calc
      ((n + 2 : ℕ) : ℝ) * (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i)
          = ∑ i : Fin (n + 2), (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i := by
        exact Finset.sum_le_sum (fun i _ =>
          ciInf_le (f := (x : Fin (n + 2) → ℝ)) (Set.finite_range _ |>.bddBelow) i)
      _ = 1 := hsum
  have hnz : ((n + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num : n + 2 ≠ 0)
  have hle : ((n + 2 : ℕ) : ℝ)⁻¹ * (((n + 2 : ℕ) : ℝ) *
      (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i)) ≤ ((n + 2 : ℕ) : ℝ)⁻¹ * 1 :=
    mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr (Nat.cast_nonneg _))
  rwa [← mul_assoc, inv_mul_cancel₀ hnz, one_mul, mul_one] at hle

/-- The minimum weight is strictly below the barycenter weight unless all weights equal
the barycenter weight. -/
theorem simplexMin_lt_center_of_ne_center (n : ℕ) {x : SimplexFn n}
    (hx : (x : Fin (n + 2) → ℝ) ≠ fun _ => simplexCenter n) :
    (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) < simplexCenter n := by
  have hm_le : (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) ≤ simplexCenter n :=
    simplexMin_le_center n x
  have hm_ne : (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) ≠ simplexCenter n := by
    intro h
    have hx' : (x : Fin (n + 2) → ℝ) = fun _ => simplexCenter n := by
      funext i
      have hsum : (∑ i : Fin (n + 2), ((x : Fin (n + 2) → ℝ) i - simplexCenter n)) = 0 := by
        rw [Finset.sum_sub_distrib, x.2.2]
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, simplexCenter_total n]
        ring
      have hnn : ∀ i : Fin (n + 2), i ∈ Finset.univ → 0 ≤ (x : Fin (n + 2) → ℝ) i - simplexCenter n :=
        fun i _ => sub_nonneg.mpr (h.symm.le.trans
          (ciInf_le (f := (x : Fin (n + 2) → ℝ)) (Set.finite_range _ |>.bddBelow) i))
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : Fin (n + 2) => (x : Fin (n + 2) → ℝ) i - simplexCenter n) hnn).1 hsum
      have hi : (x : Fin (n + 2) → ℝ) i - simplexCenter n = 0 := hzero i (Finset.mem_univ i)
      exact sub_eq_zero.mp hi
    exact hx hx'
  exact lt_of_le_of_ne hm_le hm_ne

/-- The radial exit time `t(x) = (c - ⨅ᵢxᵢ)/c`: the parameter where the ray from the
barycenter through `x` leaves the simplex (the minimal coordinate reaches `0`). -/
def simplexRadialTime (n : ℕ) (x : SimplexFn n) : ℝ :=
  (simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) / simplexCenter n

/-- The boundary exit point `b(x) = c + (x - c)/t(x)` of the ray from the barycenter
through `x`. -/
def simplexBoundaryPoint (n : ℕ) (x : SimplexFn n) : Fin (n + 2) → ℝ :=
  fun i => simplexCenter n + ((x : Fin (n + 2) → ℝ) i - simplexCenter n) / simplexRadialTime n x

/-- **Audit.** `t(x) ≥ 0`. -/
theorem simplexRadialTime_nonneg (n : ℕ) (x : SimplexFn n) : 0 ≤ simplexRadialTime n x := by
  dsimp [simplexRadialTime]
  exact div_nonneg (sub_nonneg.mpr (simplexMin_le_center n x)) (le_of_lt (simplexCenter_pos n))

/-- **Audit.** `t(x) ≤ 1` (the minimum weight is nonnegative). -/
theorem simplexRadialTime_le_one (n : ℕ) (x : SimplexFn n) : simplexRadialTime n x ≤ 1 := by
  have hm_nonneg : 0 ≤ ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i :=
    le_ciInf (f := (x : Fin (n + 2) → ℝ)) (fun i => x.2.1 i)
  dsimp [simplexRadialTime]
  rw [div_le_iff₀ (simplexCenter_pos n)]
  simpa using sub_le_self (simplexCenter n) hm_nonneg

/-- **Audit.** `t(x) > 0` away from the barycenter. -/
theorem simplexRadialTime_pos_of_ne_center (n : ℕ) {x : SimplexFn n}
    (hx : (x : Fin (n + 2) → ℝ) ≠ fun _ => simplexCenter n) : 0 < simplexRadialTime n x := by
  dsimp [simplexRadialTime]
  exact div_pos (sub_pos.mpr (simplexMin_lt_center_of_ne_center n hx)) (simplexCenter_pos n)

/-- The boundary exit point lies on `∂Δⁿ⁺¹`: coordinates nonnegative (with the minimum
coordinate exactly `0`), total weight 1. -/
theorem simplexBoundaryPoint_mem_of_ne_center (n : ℕ) {x : SimplexFn n}
    (hx : (x : Fin (n + 2) → ℝ) ≠ fun _ => simplexCenter n) :
    simplexBoundaryPoint n x ∈ simplexBoundarySet n := by
  change 0 ≤ simplexBoundaryPoint n x ∧ (∑ i, simplexBoundaryPoint n x i) = 1 ∧
    0 ∈ Set.range (simplexBoundaryPoint n x)
  have hc : 0 < simplexCenter n := simplexCenter_pos n
  have ht_pos : 0 < simplexRadialTime n x := simplexRadialTime_pos_of_ne_center n hx
  constructor
  · rw [Pi.le_def]
    intro i
    have hct : simplexCenter n * simplexRadialTime n x =
        simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i := by
      dsimp [simplexRadialTime]
      exact mul_div_cancel₀ (simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i)
        (ne_of_gt hc)
    have hx_le : (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) ≤ (x : Fin (n + 2) → ℝ) i :=
      ciInf_le (f := (x : Fin (n + 2) → ℝ)) (Set.finite_range _ |>.bddBelow) i
    have hclear : 0 ≤ simplexCenter n * simplexRadialTime n x +
        ((x : Fin (n + 2) → ℝ) i - simplexCenter n) := by
      rw [hct]
      nlinarith [hx_le]
    have hsumdiv : simplexCenter n + ((x : Fin (n + 2) → ℝ) i - simplexCenter n) / simplexRadialTime n x =
        (simplexCenter n * simplexRadialTime n x + ((x : Fin (n + 2) → ℝ) i - simplexCenter n)) /
          simplexRadialTime n x := by
      field_simp [ne_of_gt ht_pos]
    dsimp [simplexBoundaryPoint]
    rw [hsumdiv]
    simpa using (div_nonneg hclear (le_of_lt ht_pos))
  · constructor
    · dsimp [simplexBoundaryPoint]
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      have hsumc : (∑ i : Fin (n + 2), simplexCenter n) = ((n + 2 : ℕ) : ℝ) * simplexCenter n := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hsumd : (∑ i : Fin (n + 2), ((x : Fin (n + 2) → ℝ) i - simplexCenter n)) =
          1 - ((n + 2 : ℕ) : ℝ) * simplexCenter n := by
        rw [Finset.sum_sub_distrib, x.2.2]
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      rw [hsumc, hsumd, simplexCenter_total n]
      ring
    · rcases exists_eq_ciInf_of_finite (f := (x : Fin (n + 2) → ℝ)) with ⟨i₀, hi₀⟩
      refine ⟨i₀, ?_⟩
      have htm : simplexRadialTime n x = (simplexCenter n - (x : Fin (n + 2) → ℝ) i₀) / simplexCenter n := by
        dsimp [simplexRadialTime]
        rw [hi₀]
      have hct : simplexCenter n * simplexRadialTime n x = simplexCenter n - (x : Fin (n + 2) → ℝ) i₀ := by
        rw [htm]
        exact mul_div_cancel₀ (simplexCenter n - (x : Fin (n + 2) → ℝ) i₀) (ne_of_gt hc)
      have hmul : simplexCenter n * simplexRadialTime n x + ((x : Fin (n + 2) → ℝ) i₀ - simplexCenter n) = 0 := by
        rw [hct]
        ring
      calc
        simplexBoundaryPoint n x i₀ = (simplexCenter n * simplexRadialTime n x +
            ((x : Fin (n + 2) → ℝ) i₀ - simplexCenter n)) / simplexRadialTime n x := by
          dsimp [simplexBoundaryPoint]
          field_simp [ne_of_gt ht_pos]
        _ = 0 := by rw [hmul, zero_div]

/-- **Uniqueness of the radial time.** If `x = (1-t)c + t·b` with `b ∈ ∂Δⁿ⁺¹` and
`t > 0`, then `t = t(x) = (c - ⨅ᵢxᵢ)/c`. -/
theorem simplexRadialTime_eq_of_radial_repr (n : ℕ) {x : SimplexFn n} {b : SimplexBoundaryFn n}
    {t : Set.Icc (0 : ℝ) 1} (ht : 0 < (t : ℝ))
    (hx : (x : Fin (n + 2) → ℝ) = simplexBoundaryConeMap n (b, t)) :
    (t : ℝ) = simplexRadialTime n x := by
  have hb_ge : ∀ i : Fin (n + 2), 0 ≤ (b : Fin (n + 2) → ℝ) i := b.2.1
  rcases b.2.2.2 with ⟨i₀, hi₀⟩
  have hi₀' : (b : Fin (n + 2) → ℝ) i₀ = 0 := hi₀
  have hxi : ∀ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i =
      (1 - (t : ℝ)) * simplexCenter n + (t : ℝ) * (b : Fin (n + 2) → ℝ) i :=
    fun i => congr_fun hx i
  have hge : ∀ i : Fin (n + 2), simplexCenter n * (t : ℝ) ≥ simplexCenter n - (x : Fin (n + 2) → ℝ) i := by
    intro i
    have hb_i : 0 ≤ (t : ℝ) * (b : Fin (n + 2) → ℝ) i := mul_nonneg (le_of_lt ht) (hb_ge i)
    nlinarith [hxi i, hb_i]
  have hge_m : simplexCenter n * (t : ℝ) ≥ simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i := by
    rcases exists_eq_ciInf_of_finite (f := (x : Fin (n + 2) → ℝ)) with ⟨j, hj⟩
    have hge_j := hge j
    rw [hj] at hge_j
    exact hge_j
  have hle_m : simplexCenter n * (t : ℝ) ≤ simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i := by
    have hx₀ : (x : Fin (n + 2) → ℝ) i₀ = simplexCenter n - simplexCenter n * (t : ℝ) := by
      rw [hxi i₀, hi₀']
      ring
    have hm_le₀ : (⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i) ≤ (x : Fin (n + 2) → ℝ) i₀ :=
      ciInf_le (f := (x : Fin (n + 2) → ℝ)) (Set.finite_range _ |>.bddBelow) i₀
    nlinarith [hx₀, hm_le₀]
  have hct : simplexCenter n * (t : ℝ) = simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i :=
    le_antisymm hle_m hge_m
  calc
    (t : ℝ) = (simplexCenter n * (t : ℝ)) / simplexCenter n := by
      field_simp [ne_of_gt (simplexCenter_pos n)]
    _ = simplexRadialTime n x := by
      dsimp [simplexRadialTime]
      rw [hct]

/-- **Uniqueness of the boundary point.** If `x = (1-t)c + t·b` with `b ∈ ∂Δⁿ⁺¹` and
`t > 0`, then `b = b(x) = c + (x - c)/t(x)`. -/
theorem simplexBoundaryPoint_eq_of_radial_repr (n : ℕ) {x : SimplexFn n} {b : SimplexBoundaryFn n}
    {t : Set.Icc (0 : ℝ) 1} (ht : 0 < (t : ℝ))
    (hx : (x : Fin (n + 2) → ℝ) = simplexBoundaryConeMap n (b, t)) :
    (b : Fin (n + 2) → ℝ) = simplexBoundaryPoint n x := by
  have ht_eq : (t : ℝ) = simplexRadialTime n x := simplexRadialTime_eq_of_radial_repr n ht hx
  funext i
  have hxi : (x : Fin (n + 2) → ℝ) i =
      (1 - (t : ℝ)) * simplexCenter n + (t : ℝ) * (b : Fin (n + 2) → ℝ) i := congr_fun hx i
  have hmul : (t : ℝ) * (b : Fin (n + 2) → ℝ) i =
      simplexCenter n * (t : ℝ) + (x : Fin (n + 2) → ℝ) i - simplexCenter n := by
    nlinarith [hxi]
  calc
    (b : Fin (n + 2) → ℝ) i = ((t : ℝ) * (b : Fin (n + 2) → ℝ) i) / (t : ℝ) := by
      field_simp [ne_of_gt ht]
    _ = (simplexCenter n * (t : ℝ) + (x : Fin (n + 2) → ℝ) i - simplexCenter n) / (t : ℝ) := by
      rw [hmul]
    _ = simplexCenter n + ((x : Fin (n + 2) → ℝ) i - simplexCenter n) / (t : ℝ) := by
      field_simp [ne_of_gt ht]
      ring
    _ = simplexBoundaryPoint n x i := by
      dsimp [simplexBoundaryPoint]
      rw [ht_eq]

/-- **Injectivity.** The radial representation `x = (1-t)c + t·b` is unique: the base
(`t = 0`) collapses to the barycenter, and for `t > 0` the representation is recovered by
the exit time `t(x)` and exit point `b(x)`. -/
theorem simplexBoundaryConeMapQuot_injective (n : ℕ) :
    Function.Injective (simplexBoundaryConeMapQuot n) := by
  intro a b h
  revert h b
  refine Quot.inductionOn a ?_
  intro p b h
  revert h
  refine Quot.inductionOn b ?_
  intro q hpq
  apply Quot.sound
  have hval' : simplexBoundaryConeMapQuot n (Quot.mk (simplexBoundaryConeRel n) p) =
      simplexBoundaryConeMapQuot n (Quot.mk (simplexBoundaryConeRel n) q) := hpq
  have hval : simplexBoundaryConeMap n p = simplexBoundaryConeMap n q := by
    have hh : (⟨simplexBoundaryConeMap n p, simplexBoundaryConeMap_mem n p⟩ : SimplexFn n) =
        ⟨simplexBoundaryConeMap n q, simplexBoundaryConeMap_mem n q⟩ := by
      simpa [simplexBoundaryConeMapQuot] using hval'
    exact congrArg Subtype.val hh
  by_cases h0 : (p.2 : ℝ) = 0
  · right
    have hq0 : (q.2 : ℝ) = 0 := by
      by_contra hq
      have htq_pos : 0 < (q.2 : ℝ) := lt_of_le_of_ne q.2.2.1 (Ne.symm hq)
      have hp0 : simplexBoundaryConeMap n p = fun _ => simplexCenter n := by
        funext i
        dsimp [simplexBoundaryConeMap]
        rw [h0]
        ring
      have hb : (q.1 : Fin (n + 2) → ℝ) = fun _ => simplexCenter n := by
        funext i
        have hi : simplexBoundaryConeMap n q i = simplexCenter n := by
          have h := congr_fun (hp0.symm.trans hval) i
          exact h.symm
        dsimp [simplexBoundaryConeMap] at hi
        have hmul : (q.2 : ℝ) * ((q.1 : Fin (n + 2) → ℝ) i - simplexCenter n) = 0 := by
          nlinarith [hi]
        exact sub_eq_zero.mp (mul_eq_zero.mp hmul |>.resolve_left (ne_of_gt htq_pos))
      rcases q.1.2.2.2 with ⟨i₀, hi₀⟩
      have hzero : (q.1 : Fin (n + 2) → ℝ) i₀ = 0 := hi₀
      have hpos : (q.1 : Fin (n + 2) → ℝ) i₀ = simplexCenter n := congr_fun hb i₀
      have : (0 : ℝ) = simplexCenter n := hzero.symm.trans hpos
      have hc := simplexCenter_pos n
      rw [← this] at hc
      exact lt_irrefl (0 : ℝ) hc
    exact ⟨h0, hq0⟩
  · left
    have ht_pos : 0 < (p.2 : ℝ) := lt_of_le_of_ne p.2.2.1 (Ne.symm h0)
    let x : SimplexFn n := ⟨simplexBoundaryConeMap n p, simplexBoundaryConeMap_mem n p⟩
    have hx_ne : (x : Fin (n + 2) → ℝ) ≠ fun _ => simplexCenter n := by
      intro hxeq
      have hb : (p.1 : Fin (n + 2) → ℝ) = fun _ => simplexCenter n := by
        funext i
        have hi : simplexBoundaryConeMap n p i = simplexCenter n := by
          simpa using (congr_fun hxeq i)
        dsimp [simplexBoundaryConeMap] at hi
        have hmul : (p.2 : ℝ) * ((p.1 : Fin (n + 2) → ℝ) i - simplexCenter n) = 0 := by
          nlinarith [hi]
        exact sub_eq_zero.mp (mul_eq_zero.mp hmul |>.resolve_left (ne_of_gt ht_pos))
      rcases p.1.2.2.2 with ⟨i₀, hi₀⟩
      have hzero : (p.1 : Fin (n + 2) → ℝ) i₀ = 0 := hi₀
      have hpos : (p.1 : Fin (n + 2) → ℝ) i₀ = simplexCenter n := congr_fun hb i₀
      have : (0 : ℝ) = simplexCenter n := hzero.symm.trans hpos
      have hc := simplexCenter_pos n
      rw [← this] at hc
      exact lt_irrefl (0 : ℝ) hc
    have hq_pos : 0 < (q.2 : ℝ) := by
      by_contra hq
      have hq0 : (q.2 : ℝ) = 0 := le_antisymm (le_of_not_gt hq) q.2.2.1
      have hqc : simplexBoundaryConeMap n q = fun _ => simplexCenter n := by
        funext i
        dsimp [simplexBoundaryConeMap]
        rw [hq0]
        ring
      have : (x : Fin (n + 2) → ℝ) = fun _ => simplexCenter n := by
        funext i
        have h := congr_fun hval i
        rw [hqc] at h
        simpa using h
      exact hx_ne this
    have hp1 : (p.1 : Fin (n + 2) → ℝ) = simplexBoundaryPoint n x := by
      exact simplexBoundaryPoint_eq_of_radial_repr n ht_pos rfl
    have hq1 : (q.1 : Fin (n + 2) → ℝ) = simplexBoundaryPoint n x := by
      have hxq : (x : Fin (n + 2) → ℝ) = simplexBoundaryConeMap n q := by
        funext i
        have h := congr_fun hval i
        simpa using h
      exact simplexBoundaryPoint_eq_of_radial_repr n hq_pos hxq
    have hpt : (p.2 : ℝ) = simplexRadialTime n x :=
      simplexRadialTime_eq_of_radial_repr n ht_pos rfl
    have hqt : (q.2 : ℝ) = simplexRadialTime n x := by
      have hxq : (x : Fin (n + 2) → ℝ) = simplexBoundaryConeMap n q := by
        funext i
        have h := congr_fun hval i
        simpa using h
      exact simplexRadialTime_eq_of_radial_repr n hq_pos hxq
    apply Prod.ext
    · apply Subtype.ext
      exact hp1.trans hq1.symm
    · apply Subtype.ext
      exact hpt.trans hqt.symm

/-- The vertex `e₀` of `Δⁿ⁺¹` (weight 1 at vertex 0) lies on the boundary. -/
def simplexVertexZero (n : ℕ) : Fin (n + 2) → ℝ := fun i => if i = 0 then 1 else 0

/-- Membership of the vertex `e₀` in `∂Δⁿ⁺¹`. -/
theorem simplexVertexZero_mem_boundary (n : ℕ) : simplexVertexZero n ∈ simplexBoundarySet n := by
  constructor
  · rw [Pi.le_def]
    intro i
    dsimp [simplexVertexZero]
    split <;> norm_num
  · constructor
    · rw [Finset.sum_eq_single (0 : Fin (n + 2))]
      · simp [simplexVertexZero]
      · intro b _ hb
        simp [simplexVertexZero, hb]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin (n + 2))) h
    · refine ⟨1, ?_⟩
      have hne : (1 : Fin (n + 2)) ≠ 0 := by
        intro h
        have h' := congrArg (fun i : Fin (n + 2) => (i : ℕ)) h
        norm_num at h'
      simp [simplexVertexZero, hne]

/-- **Surjectivity.** Every simplex point is `(1-t(x))c + t(x)·b(x)`; the barycenter is
the collapsed base `t = 0`. -/
theorem simplexBoundaryConeMapQuot_surjective (n : ℕ) :
    Function.Surjective (simplexBoundaryConeMapQuot n) := by
  intro x
  by_cases hx : (x : Fin (n + 2) → ℝ) = fun _ => simplexCenter n
  · let b₀ : SimplexBoundaryFn n := ⟨simplexVertexZero n, simplexVertexZero_mem_boundary n⟩
    refine ⟨Quot.mk (simplexBoundaryConeRel n) (b₀, ⟨0, by norm_num⟩), ?_⟩
    apply Subtype.ext
    funext i
    rw [hx]
    simp [simplexBoundaryConeMapQuot, simplexBoundaryConeMap]
  · let t : Set.Icc (0 : ℝ) 1 := ⟨simplexRadialTime n x,
      ⟨simplexRadialTime_nonneg n x, simplexRadialTime_le_one n x⟩⟩
    let b : SimplexBoundaryFn n := ⟨simplexBoundaryPoint n x,
      simplexBoundaryPoint_mem_of_ne_center n hx⟩
    refine ⟨Quot.mk (simplexBoundaryConeRel n) (b, t), ?_⟩
    apply Subtype.ext
    funext i
    simp only [simplexBoundaryConeMapQuot, simplexBoundaryConeMap]
    dsimp [b, t, simplexBoundaryPoint, simplexRadialTime]
    have hc : 0 < simplexCenter n := simplexCenter_pos n
    have hsub : simplexCenter n - ⨅ i : Fin (n + 2), (x : Fin (n + 2) → ℝ) i ≠ 0 :=
      ne_of_gt (sub_pos.mpr (simplexMin_lt_center_of_ne_center n hx))
    field_simp [ne_of_gt hc, hsub]
    ring

/-- **Compactness audit.** `∂Δⁿ⁺¹` (function-space model) is compact (transferred from the
compact sphere). -/
instance simplexBoundaryFnCompactSpace (n : ℕ) : CompactSpace (SimplexBoundaryFn n) :=
  Homeomorph.compactSpace (simplexBoundaryFnHomeoSphere n).symm

/-- **Route 2 theorem.** The standard `(n+1)`-simplex is homeomorphic to the cone over
its own boundary: `Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹)`, the literal radial form. -/
noncomputable def simplexBoundaryConeHomeoSimplex (n : ℕ) : SimplexBoundaryCone n ≃ₜ SimplexFn n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (simplexBoundaryConeMapQuot n)
      ⟨simplexBoundaryConeMapQuot_injective n, simplexBoundaryConeMapQuot_surjective n⟩)
    (continuous_simplexBoundaryConeMapQuot n)

/-- `Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹)` (inverse direction). -/
noncomputable def simplexHomeoBoundaryCone (n : ℕ) : SimplexFn n ≃ₜ SimplexBoundaryCone n :=
  (simplexBoundaryConeHomeoSimplex n).symm

/-! ## Transfer to `Convexity.StdSimplex` and the disk -/

/-- The `Convexity.StdSimplex` model is homeomorphic to the function-space model via the
weights embedding (range equality `range_weights_eq_simplex`). -/
noncomputable def simplexHomeoStdSimplexFn (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) ≃ₜ SimplexFn n := by
  let e := Convexity.StdSimplex.isEmbedding_toFun_comp_weights (R := ℝ) (M := Fin (n + 2))
  exact ((Homeomorph.Set.univ (Convexity.StdSimplex ℝ (Fin (n + 2)))).symm.trans
    ((e.homeomorphImage (Set.univ : Set (Convexity.StdSimplex ℝ (Fin (n + 2))))).trans
      (Homeomorph.setCongr (show
          (fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => (t.weights : Fin (n + 2) → ℝ)) '' Set.univ =
            simplexSet n by
        rw [Set.image_univ]
        exact range_weights_eq_simplex n))))

/-- **DAG node 9, exact ledger statement (second half).** The standard `(n+1)`-simplex is
homeomorphic to the closed `(n+1)`-disk: `Δⁿ⁺¹ ≅ Dⁿ⁺¹`, by
`Δⁿ⁺¹ ≅ Cone(𝕊ⁿ) ≅ Dⁿ⁺¹` (route 1) composed with the proved cone homeomorphism
`coneQuotHomeoDisk`. -/
noncomputable def simplexHomeoDisk (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n + 2)) ≃ₜ Disk (n + 1) :=
  (simplexHomeoStdSimplexFn n).trans ((simplexHomeoConeQuot n).trans (coneQuotHomeoDisk n))

/-- The `Convexity.StdSimplex` model of `Δⁿ⁺¹` is homeomorphic to the cone over
`∂Δⁿ⁺¹` (route 2, StdSimplex model). -/
noncomputable def simplexHomeoBoundaryConeStd (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) ≃ₜ SimplexBoundaryCone n :=
  (simplexHomeoStdSimplexFn n).trans (simplexHomeoBoundaryCone n)

/-! ## Audits: compactness, nonemptiness, shape examples -/

/-- **Compactness audit.** `Δⁿ⁺¹` (function-space model) is compact (transferred from the
compact cone quotient). -/
instance simplexFnCompactSpace (n : ℕ) : CompactSpace (SimplexFn n) :=
  Homeomorph.compactSpace (sphereConeHomeoSimplex n)

/-- **Compactness audit.** `Cone(∂Δⁿ⁺¹)` is compact (quotient of the compact product). -/
instance simplexBoundaryConeCompactSpace (n : ℕ) : CompactSpace (SimplexBoundaryCone n) :=
  inferInstance

/-- **T2 audit.** `Cone(∂Δⁿ⁺¹)` is Hausdorff (transferred from the simplex). -/
instance simplexBoundaryConeT2Space (n : ℕ) : T2Space (SimplexBoundaryCone n) :=
  Homeomorph.t2Space (simplexBoundaryConeHomeoSimplex n).symm

/-- **Nonemptiness audit.** `Cone(∂Δⁿ⁺¹)` is nonempty. -/
instance simplexBoundaryConeNonempty (n : ℕ) : Nonempty (SimplexBoundaryCone n) :=
  Nonempty.map (simplexHomeoBoundaryCone n) (simplexFnNonempty n)

/-- **Shape example.** The tetrahedron `Δ³` is homeomorphic to the closed 3-ball `D³`. -/
example : Convexity.StdSimplex ℝ (Fin 4) ≃ₜ Disk 3 :=
  simplexHomeoDisk 2

/-- **Shape example.** The triangle `Δ²` is homeomorphic to the closed 2-disk `D²`. -/
example : Convexity.StdSimplex ℝ (Fin 3) ≃ₜ Disk 2 :=
  simplexHomeoDisk 1

/-- **Shape example.** The interval `Δ¹` is homeomorphic to the closed 1-disk `D¹`. -/
example : Convexity.StdSimplex ℝ (Fin 2) ≃ₜ Disk 1 :=
  simplexHomeoDisk 0

/-- **Shape example.** The tetrahedron is the cone over its boundary (the triangle
boundary): `Δ³ ≅ Cone(∂Δ³)`. -/
example : Convexity.StdSimplex ℝ (Fin 4) ≃ₜ SimplexBoundaryCone 2 :=
  simplexHomeoBoundaryConeStd 2

/-- **Consistency check.** The simplex ≅ disk statement factors through the cone
definitionally. -/
example (n : ℕ) :
    simplexHomeoDisk n =
      (simplexHomeoStdSimplexFn n).trans ((simplexHomeoConeQuot n).trans (coneQuotHomeoDisk n)) :=
  rfl


/-! ## Cone functoriality: `Cone(∂Δⁿ⁺¹) ≅ Cone(𝕊ⁿ)` -/

/-- **General lemma.** A homeomorphism `e : X ≃ₜ Y` transporting a relation `r` to a
relation `s` (in both directions) induces a homeomorphism of the quotient spaces
`Quot r ≃ₜ Quot s`.  This is the functoriality of quotient spaces under homeomorphisms;
continuity of both directions comes from `continuous_quot_lift`, so no compactness is
needed. -/
noncomputable def quotMapHomeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {r : X → X → Prop} {s : Y → Y → Prop}
    (h : ∀ a b : X, r a b ↔ s (e a) (e b)) : Quot r ≃ₜ Quot s := by
  let f : Quot r → Quot s := Quot.lift (fun a => Quot.mk s (e a))
    (fun a b hab => Quot.sound (h a b |>.1 hab))
  let g : Quot s → Quot r := Quot.lift (fun a => Quot.mk r (e.symm a))
    (fun a b hab => Quot.sound (h (e.symm a) (e.symm b) |>.2 (by
      simpa [Homeomorph.apply_symm_apply] using hab)))
  have hfg : ∀ x : Quot r, g (f x) = x := by
    intro x
    refine Quot.inductionOn x ?_
    intro a
    dsimp [f, g]
    rw [Homeomorph.symm_apply_apply]
  have hgf : ∀ x : Quot s, f (g x) = x := by
    intro x
    refine Quot.inductionOn x ?_
    intro a
    dsimp [f, g]
    rw [Homeomorph.apply_symm_apply]
  have hf : Continuous f := by
    dsimp [f]
    refine continuous_quot_lift
      (fun a b hab => Quot.sound (h a b |>.1 hab)) ?_
    exact continuous_quot_mk.comp e.continuous
  have hg : Continuous g := by
    dsimp [g]
    refine continuous_quot_lift
      (fun a b hab => Quot.sound (h (e.symm a) (e.symm b) |>.2 (by
        simpa [Homeomorph.apply_symm_apply] using hab))) ?_
    exact continuous_quot_mk.comp e.continuous_symm
  exact
    { toEquiv := { toFun := f, invFun := g, left_inv := hfg, right_inv := hgf }
      continuous_toFun := hf
      continuous_invFun := hg }

/-- The cone relation on `∂Δⁿ⁺¹` transported by `simplexBoundaryToSphere` is the cone
relation on `𝕊ⁿ` (both collapse the base `t = 0`; the boundary homeomorphism is
injective). -/
theorem simplexBoundaryConeRel_iff_coneRel (n : ℕ)
    (p q : SimplexBoundaryFn n × Set.Icc (0 : ℝ) 1) :
    simplexBoundaryConeRel n p q ↔
      coneRel n (simplexBoundaryToSphere n p.1, p.2) (simplexBoundaryToSphere n q.1, q.2) := by
  constructor
  · intro h
    rcases h with h | ⟨hp, hq⟩
    · left
      subst h
      rfl
    · right
      exact ⟨hp, hq⟩
  · intro h
    rcases h with h | ⟨hp, hq⟩
    · left
      have hfst : simplexBoundaryToSphere n p.1 = simplexBoundaryToSphere n q.1 :=
        congrArg Prod.fst h
      have hsnd : p.2 = q.2 :=
        congrArg (fun z : Sphere n × Set.Icc (0 : ℝ) 1 => z.2) h
      have hp1 : p.1 = q.1 := (simplexBoundaryFnHomeoSphere n).injective hfst
      exact Prod.ext hp1 hsnd
    · right
      exact ⟨hp, hq⟩

/-- **Cone functoriality.** The cone over the boundary of the standard `(n+1)`-simplex is
homeomorphic to the cone over the `n`-sphere, induced by `∂Δⁿ⁺¹ ≅ 𝕊ⁿ`
(`simplexBoundaryHomeoSphere` / `simplexBoundaryFnHomeoSphere`).  This is the middle
isomorphism of the node-9 diagram `Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹) ≅ Cone(𝕊ⁿ) ≅ Dⁿ⁺¹`: the two routes
to `simplexHomeoDisk` are the same geometric map transported across it. -/
noncomputable def simplexBoundaryConeHomeoSphereCone (n : ℕ) :
    SimplexBoundaryCone n ≃ₜ ConeQuot n :=
  quotMapHomeo ((simplexBoundaryFnHomeoSphere n).prodCongr (Homeomorph.refl (Set.Icc (0 : ℝ) 1)))
    (simplexBoundaryConeRel_iff_coneRel n)

/-- **Coherence check.** The middle node of the diagram composes with the literal radial
form to give the sphere-cone homeomorphism up to the functoriality isomorphism. -/
example (n : ℕ) : SimplexBoundaryCone n ≃ₜ ConeQuot n :=
  simplexBoundaryConeHomeoSphereCone n

end Poincare.D12.TriangulationTopology