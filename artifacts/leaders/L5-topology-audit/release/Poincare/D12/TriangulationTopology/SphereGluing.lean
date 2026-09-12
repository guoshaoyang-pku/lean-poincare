/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib

/-!
# Poincare.D12.TriangulationTopology.SphereGluing

Concrete homeomorphism theorems with actual topological spaces: the gluing/realization
lemmas behind sphere recognition (S³ = D³ ∪_{S²} D³, each extinction piece S³/Γᵢ is built
from balls glued along a triangulated sphere).

All spaces are plain metric subspaces of Euclidean space (matching the model spaces of
`Poincare.Longrun.Topology.Basic`, where `SphereThree` is the unit sphere in ℝ⁴):

* `Sphere n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` — the unit `n`-sphere
  in `ℝⁿ⁺¹` (dimension convention: `𝕊 n ⊂ ℝⁿ⁺¹`, as in `TopCat.sphere n`);
* `Disk n = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1` — the unit `n`-disk
  in `ℝⁿ` (dimension convention: `𝔻 n ⊂ ℝⁿ`, as in `TopCat.disk n`);
  in particular `∂(Disk (n+1)) = Sphere n`.

## Theorems (all proved here, no `sorry`, no axioms)

1. `coneQuotHomeoDisk n : Quot (coneRel n) ≃ₜ Disk (n + 1)` — the cone over the
   `n`-sphere (cylinder `Sphere n × [0,1]` with the base collapsed to the vertex) is
   homeomorphic to the closed `(n+1)`-disk.  Geometric realization of the cone of a
   finite complex.
2. `suspQuotHomeoSphere n : Quot (suspRel n) ≃ₜ Sphere (n + 1)` — the suspension of the
   `n`-sphere (cylinder `Sphere n × [-1,1]` with both ends collapsed) is homeomorphic to
   the `(n+1)`-sphere.
3. `doubleDiskQuotHomeoSphere n : Quot (doubleDiskRel n) ≃ₜ Sphere (n + 1)` — two
   `(n+1)`-disks glued along their common boundary `Sphere n` yield the `(n+1)`-sphere.
4. TopCat corollaries (`𝔻`, `𝕊`, `∂𝔻` notation): `ULift (ConeQuot n) ≃ₜ 𝔻 (n+1)`,
   `ULift (SuspQuot n) ≃ₜ 𝕊 (n+1)`, `ULift (DoubleDiskQuot n) ≃ₜ 𝕊 (n+1)`.

## Method

Each gluing map is an explicit continuous formula with a checked norm identity
(`norm_sq_esnoc` decomposes `‖esnoc w s‖² = ‖w‖² + s²`, where `esnoc w s` is the point of
`ℝⁿ⁺²` with coordinates `w` followed by last coordinate `s`).  It respects the gluing
relation, descends to a continuous bijection on `Quot` (surjectivity and injectivity by
norm algebra over the `esnoc` coordinates), and compactness of the source quotient
(`Quot.compactSpace` from compact sphere/interval/disk factors) plus T2 of the target
turn it into a homeomorphism (`Continuous.homeoOfEquivCompactToT2`).

## Provenance of external mathematics

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by lake-manifest.json),
  Apache-2.0: all imported lemmas.  This file adds original gluing constructions; the
  constructions are classical (cone/suspension/hemisphere gluing), with no copied proofs.
-/

noncomputable section

open scoped Topology
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## Model spaces and dimension conventions -/

/-- The unit `n`-sphere in `ℝⁿ⁺¹`: `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (n+1))`.
Matches the convention `𝕊 n ⊂ ℝⁿ⁺¹` of `TopCat.sphere n = TopCat.diskBoundary (n+1)`. -/
abbrev Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The unit `n`-disk in `ℝⁿ`: `Metric.closedBall 0 1` in `EuclideanSpace ℝ (Fin n)`.
Matches the convention `𝔻 n ⊂ ℝⁿ` of `TopCat.disk n`. -/
abbrev Disk (n : ℕ) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- **Dimension audit.** The boundary of the `(n+1)`-disk is the `n`-sphere: both are
definitionally the unit sphere in `ℝⁿ⁺¹`.  (This is exactly the convention used by
`TopCat.diskBoundary (n+1) = TopCat.sphere n`.) -/
theorem disk_boundary_eq_sphere (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 = Sphere n :=
  rfl

/-- **Dimension audit.** `𝕊 3` is the sphere in `ℝ⁴`; `∂𝔻 4 = 𝕊 3`.  Shapes only
(definitional), matching `TopCat` conventions. -/
example : TopCat.sphere 3 = TopCat.diskBoundary 4 := rfl

/-- **Compactness audit.** Every sphere is compact (proper-space argument). -/
instance sphereCompactSpace (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- **Compactness audit.** Every disk is compact. -/
instance diskCompactSpace (n : ℕ) : CompactSpace (Disk n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- **Compactness audit.** Compact intervals. -/
instance iccCompactSpace (a b : ℝ) : CompactSpace (Set.Icc a b) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc a b))

instance diskNonempty (n : ℕ) : Nonempty (Disk n) :=
  ⟨0, mem_closedBall_iff_norm.2 (by simp)⟩

/-! ## Norm algebra over `esnoc` coordinates -/

/-- Append a last coordinate to a point of `ℝⁿ⁺¹` to get a point of `ℝⁿ⁺²`
(the `PiLp 2` version of `Fin.snoc`). -/
def esnoc {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 (@Fin.snoc (n + 1) (fun _ : Fin (n + 2) => ℝ) (fun i : Fin (n + 1) => w i) s)

@[simp] theorem esnoc_last {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    esnoc w s (Fin.last (n + 1)) = s := by
  simp [esnoc, Fin.snoc_last]

@[simp] theorem esnoc_castSucc {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ)
    (j : Fin (n + 1)) : esnoc w s j.castSucc = w j := by
  simp [esnoc, Fin.snoc_castSucc]

/-- `esnoc` is injective in both components (via `Fin.snoc_injective2`). -/
theorem esnoc_injective2 {n : ℕ} {w w' : EuclideanSpace ℝ (Fin (n + 1))} {s s' : ℝ}
    (h : esnoc w s = esnoc w' s') : w = w' ∧ s = s' := by
  have h' : @Fin.snoc (n + 1) (fun _ : Fin (n + 2) => ℝ) (fun i : Fin (n + 1) => w i) s =
      @Fin.snoc (n + 1) (fun _ : Fin (n + 2) => ℝ) (fun i : Fin (n + 1) => w' i) s' := by
    dsimp [esnoc] at h
    exact congrArg (WithLp.equiv 2 (Fin (n + 2) → ℝ)) h
  rcases Fin.snoc_injective2 h' with ⟨hw, hs⟩
  constructor
  · apply PiLp.ext
    intro i
    exact congr_fun hw i
  · exact hs

/-- Squared-norm decomposition for `esnoc`: `‖esnoc w s‖² = ‖w‖² + s²`.  The key
algebra behind all membership checks of the hemisphere/cone formulas. -/
theorem norm_sq_esnoc {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) :
    ‖esnoc w s‖ ^ 2 = ‖w‖ ^ 2 + s ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_castSucc]
  simp only [esnoc_castSucc, esnoc_last, Real.norm_eq_abs, sq_abs]

/-- A vector has norm 1 iff its squared norm is 1 (norm is nonnegative). -/
theorem norm_eq_one_iff_norm_sq_eq_one {E : Type*} [SeminormedAddGroup E] (x : E) :
    ‖x‖ = 1 ↔ ‖x‖ ^ 2 = 1 := by
  constructor
  · intro h
    rw [h, one_pow]
  · intro h
    calc
      ‖x‖ = |‖x‖| := (abs_of_nonneg (norm_nonneg x)).symm
      _ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq_eq_abs ‖x‖).symm
      _ = Real.sqrt 1 := by rw [h]
      _ = 1 := Real.sqrt_one

/-- **Nonemptiness audit.** `Sphere n` is nonempty for every `n`: the first basis vector
`e₀` of `ℝⁿ⁺¹` has norm 1. -/
instance sphereNonempty (n : ℕ) : Nonempty (Sphere n) := by
  let e₀ : Fin (n + 1) → ℝ := fun i => if i = 0 then (1 : ℝ) else 0
  refine ⟨⟨WithLp.toLp 2 e₀, ?_⟩⟩
  rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [e₀]
  · intro b _ hb
    simp [e₀, hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h

/-- For a unit vector `x` and `|s| ≤ 1`, the hemisphere point
`(√(1-s²) • x, s)` has norm 1. -/
theorem norm_esnoc_smul_sqrt_sub_sq_eq_one {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (hx : ‖x‖ = 1) {s : ℝ} (hs : |s| ≤ 1) :
    ‖esnoc (Real.sqrt (1 - s ^ 2) • x) s‖ = 1 := by
  rw [norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc]
  have hsle : s ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one s).2 hs
  have hpos : 0 ≤ 1 - s ^ 2 := sub_nonneg.mpr hsle
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  calc
    ‖Real.sqrt (1 - s ^ 2) • x‖ ^ 2 + s ^ 2
        = (‖Real.sqrt (1 - s ^ 2)‖ * ‖x‖) ^ 2 + s ^ 2 := by
          rw [norm_smul]
    _ = (Real.sqrt (1 - s ^ 2) * 1) ^ 2 + s ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg, hx]
    _ = (Real.sqrt (1 - s ^ 2)) ^ 2 + s ^ 2 := by ring
    _ = (1 - s ^ 2) + s ^ 2 := by rw [Real.sq_sqrt hpos]
    _ = 1 := by ring

/-! ## Theorem 1: the cone over `Sⁿ` is the `(n+1)`-disk -/

/-- The cone over `Sphere n`: the cylinder `Sphere n × [0,1]`, quotient by the relation
that collapses the base `Sphere n × {0}` to the cone vertex. -/
def coneRel (n : ℕ) : Sphere n × Set.Icc (0 : ℝ) 1 → Sphere n × Set.Icc (0 : ℝ) 1 → Prop :=
  fun p q => p = q ∨ ((p.2 : ℝ) = 0 ∧ (q.2 : ℝ) = 0)

/-- The quotient space of the cone relation (the geometric cone). -/
abbrev ConeQuot (n : ℕ) : Type := Quot (coneRel n)

/-- Membership: `t • x` has norm `t` for `t ≥ 0` and unit `x`, hence lies in the disk. -/
theorem coneMap_mem (n : ℕ) (p : Sphere n × Set.Icc (0 : ℝ) 1) :
    (p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin (n + 1))) ∈ Disk (n + 1) := by
  rw [mem_closedBall_iff_norm, sub_zero]
  calc
    ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖
        = ‖(p.2 : ℝ)‖ * ‖(p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := by rw [norm_smul]
    _ = (p.2 : ℝ) * ‖(p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg p.2.2.1]
    _ = (p.2 : ℝ) := by
          rw [mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
    _ ≤ 1 := p.2.2.2

/-- The cone map `(x, t) ↦ t • x ∈ 𝔻ⁿ⁺¹`, the geometric realization of the cone. -/
def coneMap (n : ℕ) : Sphere n × Set.Icc (0 : ℝ) 1 → Disk (n + 1) := fun p =>
  ⟨(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin (n + 1))), coneMap_mem n p⟩

/-- The cone map is continuous. -/
theorem continuous_coneMap (n : ℕ) : Continuous (coneMap n) := by
  refine Continuous.subtype_mk ?_ (fun p => coneMap_mem n p)
  fun_prop

/-- The cone map respects the cone relation (the base collapses to the vertex `0`). -/
theorem coneMap_respects (n : ℕ) (p q : Sphere n × Set.Icc (0 : ℝ) 1) :
    coneRel n p q → coneMap n p = coneMap n q := by
  intro h
  rcases h with h | ⟨hp, hq⟩
  · subst h
    rfl
  · apply Subtype.ext
    dsimp [coneMap]
    rw [hp, hq, zero_smul, zero_smul]

/-- The descended cone map `ConeQuot n → Disk (n+1)` is continuous. -/
noncomputable def coneMapQuot (n : ℕ) : ConeQuot n → Disk (n + 1) :=
  Quot.lift (coneMap n) (coneMap_respects n)

/-- Continuity of the descended cone map. -/
theorem continuous_coneMapQuot (n : ℕ) : Continuous (coneMapQuot n) :=
  continuous_quot_lift (coneMap_respects n) (continuous_coneMap n)

/-- Surjectivity: every disk point is `t • x` for some unit `x` and `t ∈ [0,1]`
(the radial decomposition). -/
theorem coneMapQuot_surjective (n : ℕ) : Function.Surjective (coneMapQuot n) := by
  intro d
  by_cases h : (d : EuclideanSpace ℝ (Fin (n + 1))) = 0
  · -- the vertex: any base point `(x, 0)` maps to `0`
    let x : Sphere n := Classical.choice (sphereNonempty n)
    refine ⟨Quot.mk _ (x, ⟨0, by norm_num⟩), ?_⟩
    apply Subtype.ext
    simp [coneMapQuot, coneMap, h]
  · -- radial decomposition: `d = ‖d‖ • ((‖d‖)⁻¹ • d)`
    have hnorm_ne : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr h
    have hnorm_mem : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor
      · exact norm_nonneg _
      · simpa using (mem_closedBall_iff_norm.mp d.2)
    have hdunit : (‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ •
        (d : EuclideanSpace ℝ (Fin (n + 1))) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ hnorm_ne
    refine ⟨Quot.mk _ (⟨_, hdunit⟩, ⟨_, hnorm_mem⟩), ?_⟩
    apply Subtype.ext
    simp [coneMapQuot, coneMap, smul_smul, mul_inv_cancel₀ hnorm_ne]

/-- Injectivity on fibers: `t₁ • x₁ = t₂ • x₂` with unit `xᵢ` forces `t₁ = t₂`, and
`x₁ = x₂` unless `t = 0` (where the cone relation collapses all of the base). -/
theorem coneMapQuot_injective (n : ℕ) : Function.Injective (coneMapQuot n) := by
  intro a b h
  revert h b
  refine Quot.inductionOn a ?_
  intro p b h
  revert h
  refine Quot.inductionOn b ?_
  intro q hpq
  apply Quot.sound
  have hval' : coneMapQuot n (Quot.mk (coneRel n) p) = coneMapQuot n (Quot.mk (coneRel n) q) := hpq
  have hval : (coneMap n p : EuclideanSpace ℝ (Fin (n + 1))) =
      (coneMap n q : EuclideanSpace ℝ (Fin (n + 1))) := by
    have : coneMap n p = coneMap n q := by
      simpa [coneMapQuot] using hval'
    exact congrArg Subtype.val this
  dsimp [coneMap] at hval
  have ht : (p.2 : ℝ) = (q.2 : ℝ) := by
    have hp : ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = (p.2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.2.2.1, mem_sphere_zero_iff_norm.mp p.1.2,
        mul_one]
    have hq : ‖(q.2 : ℝ) • (q.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = (q.2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.2.2.1, mem_sphere_zero_iff_norm.mp q.1.2,
        mul_one]
    calc
      (p.2 : ℝ) = ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := hp.symm
      _ = ‖(q.2 : ℝ) • (q.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ := by rw [hval]
      _ = (q.2 : ℝ) := hq
  by_cases h0 : (p.2 : ℝ) = 0
  · right
    exact ⟨h0, ht.symm.trans h0⟩
  · left
    have hpos : 0 < (p.2 : ℝ) := lt_of_le_of_ne p.2.2.1 (Ne.symm h0)
    have hx : (p.1 : EuclideanSpace ℝ (Fin (n + 1))) =
        (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
      calc
        (p.1 : EuclideanSpace ℝ (Fin (n + 1)))
            = (p.2 : ℝ)⁻¹ • ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) :=
              (inv_smul_smul₀ (ne_of_gt hpos) _).symm
        _ = (p.2 : ℝ)⁻¹ • ((q.2 : ℝ) • (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) := by rw [hval]
        _ = (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
              rw [← ht]
              exact inv_smul_smul₀ (ne_of_gt hpos) _
    apply Prod.ext
    · apply Subtype.ext
      exact hx
    · apply Subtype.ext
      exact ht

/-- **Theorem 1.** The cone over the `n`-sphere is homeomorphic to the closed
`(n+1)`-disk. -/
noncomputable def coneQuotHomeoDisk (n : ℕ) : ConeQuot n ≃ₜ Disk (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (coneMapQuot n)
      ⟨coneMapQuot_injective n, coneMapQuot_surjective n⟩)
    (continuous_coneMapQuot n)

/-! ## Theorem 2: the suspension of `Sⁿ` is `Sⁿ⁺¹` -/

/-- The suspension cylinder: `Sphere n × [-1,1]`. -/
abbrev SuspCyl (n : ℕ) : Type := Sphere n × Set.Icc (-1 : ℝ) 1

/-- The suspension relation: both ends `s = ±1` of the cylinder are collapsed. -/
def suspRel (n : ℕ) : SuspCyl n → SuspCyl n → Prop := fun p q =>
  p = q ∨ ((p.2 : ℝ) = 1 ∧ (q.2 : ℝ) = 1) ∨ ((p.2 : ℝ) = -1 ∧ (q.2 : ℝ) = -1)

/-- The quotient space of the suspension relation. -/
abbrev SuspQuot (n : ℕ) : Type := Quot (suspRel n)

/-- Membership: `(√(1-s²) • x, s)` has norm 1 for unit `x` and `|s| ≤ 1`. -/
theorem suspMap_mem (n : ℕ) (p : SuspCyl n) :
    esnoc (Real.sqrt (1 - (p.2 : ℝ) ^ 2) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (p.2 : ℝ) ∈
      Sphere (n + 1) := by
  rw [mem_sphere_zero_iff_norm]
  apply norm_esnoc_smul_sqrt_sub_sq_eq_one
  · exact mem_sphere_zero_iff_norm.mp p.1.2
  · exact abs_le.mpr p.2.2

/-- The suspension map `(x, s) ↦ (√(1-s²) • x, s) ∈ Sⁿ⁺¹ ⊂ ℝⁿ⁺²`: the point with
latitude `s` and longitude `x`. -/
def suspMap (n : ℕ) : SuspCyl n → Sphere (n + 1) := fun p =>
  ⟨esnoc (Real.sqrt (1 - (p.2 : ℝ) ^ 2) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (p.2 : ℝ),
    suspMap_mem n p⟩

/-- The suspension map is continuous. -/
theorem continuous_suspMap (n : ℕ) : Continuous (suspMap n) := by
  refine Continuous.subtype_mk ?_ (fun p => suspMap_mem n p)
  have hcont_pi : Continuous fun p : SuspCyl n =>
      @Fin.snoc (n + 1) (fun _ : Fin (n + 2) => ℝ)
        (fun i : Fin (n + 1) =>
          Real.sqrt (1 - (p.2 : ℝ) ^ 2) • ((p.1 : EuclideanSpace ℝ (Fin (n + 1))) i))
        (p.2 : ℝ) := by
    fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 2) => ℝ)).comp hcont_pi

/-- The suspension map respects the suspension relation. -/
theorem suspMap_respects (n : ℕ) (p q : SuspCyl n) :
    suspRel n p q → suspMap n p = suspMap n q := by
  intro h
  rcases h with h | h | h
  · subst h
    rfl
  · rcases h with ⟨hp, hq⟩
    apply Subtype.ext
    simp [suspMap, hp, hq, one_pow, sub_self, zero_smul]
  · rcases h with ⟨hp, hq⟩
    apply Subtype.ext
    simp [suspMap, hp, hq, sub_self, zero_smul]

/-- The descended suspension map `SuspQuot n → Sphere (n+1)` is continuous. -/
noncomputable def suspMapQuot (n : ℕ) : SuspQuot n → Sphere (n + 1) :=
  Quot.lift (suspMap n) (suspMap_respects n)

/-- Continuity of the descended suspension map. -/
theorem continuous_suspMapQuot (n : ℕ) : Continuous (suspMapQuot n) :=
  continuous_quot_lift (suspMap_respects n) (continuous_suspMap n)

/-- If `‖y‖² + z² = 1` and `y ≠ 0`, then `√(1 - z²) = ‖y‖`. -/
theorem sqrt_one_sub_sq_eq_norm_of_norm_sq_add_sq_eq_one {n : ℕ}
    (y : EuclideanSpace ℝ (Fin (n + 1))) (z : ℝ)
    (h : ‖y‖ ^ 2 + z ^ 2 = 1) :
    Real.sqrt (1 - z ^ 2) = ‖y‖ := by
  have hnorm2 : ‖y‖ ^ 2 = 1 - z ^ 2 := by
    linarith
  calc
    Real.sqrt (1 - z ^ 2) = Real.sqrt (‖y‖ ^ 2) := by rw [hnorm2]
    _ = |‖y‖| := Real.sqrt_sq_eq_abs _
    _ = ‖y‖ := abs_of_nonneg (norm_nonneg _)

/-- Surjectivity of the suspension map: every point of `Sⁿ⁺¹ = {(y,z) : ‖y‖² + z² = 1}`
is `(√(1-z²) • x, z)` for a unit `x` (longitude), unless `y = 0` where `z = ±1` is one of
the two collapsed poles. -/
theorem suspMapQuot_surjective (n : ℕ) : Function.Surjective (suspMapQuot n) := by
  intro v
  let y : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (fun j : Fin (n + 1) => (v : EuclideanSpace ℝ (Fin (n + 2))) j.castSucc)
  let z : ℝ := (v : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))
  have hv : (v : EuclideanSpace ℝ (Fin (n + 2))) = esnoc y z := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases (n := n + 1) ?_ ?_ i
    · simp [z, esnoc_last]
    · intro j
      simp [y, esnoc_castSucc]
  have hnorm : ‖y‖ ^ 2 + z ^ 2 = 1 := by
    have := mem_sphere_zero_iff_norm.mp v.2
    rw [hv] at this
    have hsq := congrArg (fun t : ℝ => t ^ 2) this
    simpa [norm_sq_esnoc] using hsq
  have hzmem : z ∈ Set.Icc (-1 : ℝ) 1 := by
    have hz2 : z ^ 2 ≤ 1 := by
      have : z ^ 2 ≤ ‖y‖ ^ 2 + z ^ 2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      simpa [hnorm] using this
    rw [Set.mem_Icc]
    constructor
    · exact (abs_le.mp ((sq_le_one_iff_abs_le_one z).1 hz2)).1
    · exact (abs_le.mp ((sq_le_one_iff_abs_le_one z).1 hz2)).2
  by_cases h : y = 0
  · -- the poles: `z = ±1`; any longitude `x₀` works
    have hz_sq : z ^ 2 = 1 := by
      simpa [h, zero_smul] using hnorm
    let x₀ : Sphere n := Classical.choice (sphereNonempty n)
    refine ⟨Quot.mk _ (x₀, ⟨z, hzmem⟩), ?_⟩
    apply Subtype.ext
    rw [hv]
    have hsqrt : Real.sqrt (1 - z ^ 2) = 0 := by
      rw [hz_sq, sub_self, Real.sqrt_zero]
    simp [suspMapQuot, suspMap, hsqrt, h, zero_smul]
  · -- the longitudes: `x = (‖y‖)⁻¹ • y`
    have hnorm_ne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hy_unit : (‖y‖)⁻¹ • y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ hnorm_ne
    refine ⟨Quot.mk _ (⟨(‖y‖)⁻¹ • y, hy_unit⟩, ⟨z, hzmem⟩), ?_⟩
    apply Subtype.ext
    rw [hv]
    have hsqrt : Real.sqrt (1 - z ^ 2) = ‖y‖ :=
      sqrt_one_sub_sq_eq_norm_of_norm_sq_add_sq_eq_one y z hnorm
    have hydiv : ‖y‖ • ((‖y‖)⁻¹ • y) = y := by
      rw [smul_smul, mul_inv_cancel₀ hnorm_ne, one_smul]
    simp [suspMapQuot, suspMap, hsqrt, hydiv]

/-- Injectivity of the suspension map: `(√(1-s²)x, s) = (√(1-t²)x', t)` forces `s = t`,
and `x = x'` unless `s = ±1` (where the suspension relation collapses the end). -/
theorem suspMapQuot_injective (n : ℕ) : Function.Injective (suspMapQuot n) := by
  intro a b h
  revert h b
  refine Quot.inductionOn a ?_
  intro p b h
  revert h
  refine Quot.inductionOn b ?_
  intro q hpq
  apply Quot.sound
  have hval' : suspMapQuot n (Quot.mk (suspRel n) p) = suspMapQuot n (Quot.mk (suspRel n) q) := hpq
  have hval : (suspMap n p : EuclideanSpace ℝ (Fin (n + 2))) =
      (suspMap n q : EuclideanSpace ℝ (Fin (n + 2))) := by
    have : suspMap n p = suspMap n q := by
      simpa [suspMapQuot] using hval'
    exact congrArg Subtype.val this
  simp only [suspMap] at hval
  rcases esnoc_injective2 hval with ⟨hw, ht⟩
  by_cases hpole : (p.2 : ℝ) = 1 ∨ (p.2 : ℝ) = -1
  · rcases hpole with hp | hp
    · right
      left
      exact ⟨hp, ht.symm.trans hp⟩
    · right
      right
      exact ⟨hp, ht.symm.trans hp⟩
  · left
    have hsq_ne : (p.2 : ℝ) ^ 2 ≠ 1 := by
      intro hsq
      have : (p.2 : ℝ) = 1 ∨ (p.2 : ℝ) = -1 := sq_eq_one_iff.mp hsq
      exact hpole this
    have hpos : 0 < 1 - (p.2 : ℝ) ^ 2 := by
      have hle : (p.2 : ℝ) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).2 (abs_le.mpr p.2.2)
      exact sub_pos.mpr (lt_of_le_of_ne hle hsq_ne)
    have hsqrt_ne : Real.sqrt (1 - (p.2 : ℝ) ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hpos)
    have hx : (p.1 : EuclideanSpace ℝ (Fin (n + 1))) =
        (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
      calc
        (p.1 : EuclideanSpace ℝ (Fin (n + 1)))
            = (Real.sqrt (1 - (p.2 : ℝ) ^ 2))⁻¹ •
              (Real.sqrt (1 - (p.2 : ℝ) ^ 2) • (p.1 : EuclideanSpace ℝ (Fin (n + 1)))) :=
              (inv_smul_smul₀ hsqrt_ne _).symm
        _ = (Real.sqrt (1 - (p.2 : ℝ) ^ 2))⁻¹ •
              (Real.sqrt (1 - (q.2 : ℝ) ^ 2) • (q.1 : EuclideanSpace ℝ (Fin (n + 1)))) := by
              rw [hw]
        _ = (q.1 : EuclideanSpace ℝ (Fin (n + 1))) := by
              rw [← ht]
              exact inv_smul_smul₀ hsqrt_ne _
    apply Prod.ext
    · apply Subtype.ext
      exact hx
    · apply Subtype.ext
      exact ht

/-- **Theorem 2.** The suspension of the `n`-sphere is homeomorphic to the
`(n+1)`-sphere. -/
noncomputable def suspQuotHomeoSphere (n : ℕ) : SuspQuot n ≃ₜ Sphere (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (suspMapQuot n)
      ⟨suspMapQuot_injective n, suspMapQuot_surjective n⟩)
    (continuous_suspMapQuot n)

/-! ## Theorem 3: gluing two `(n+1)`-disks along their boundary gives `Sⁿ⁺¹` -/

/-- Disjoint union of two copies of `Disk (n+1)` (the two hemispheres). -/
abbrev DoubleDisk (n : ℕ) : Type := Disk (n + 1) ⊕ Disk (n + 1)

/-- The gluing relation: the two copies of the boundary sphere `Sphere n` are identified
pointwise (`inl d ~ inr d` for `d` on the boundary), symmetric and reflexive closure. -/
def doubleDiskRel (n : ℕ) : DoubleDisk n → DoubleDisk n → Prop := fun p q =>
  p = q ∨
    (∃ d e : Disk (n + 1), p = Sum.inl d ∧ q = Sum.inr e ∧ d = e ∧
      (d : EuclideanSpace ℝ (Fin (n + 1))) ∈ Sphere n) ∨
    (∃ d e : Disk (n + 1), p = Sum.inr d ∧ q = Sum.inl e ∧ d = e ∧
      (d : EuclideanSpace ℝ (Fin (n + 1))) ∈ Sphere n)

/-- The quotient space: two `(n+1)`-disks glued along their common boundary. -/
abbrev DoubleDiskQuot (n : ℕ) : Type := Quot (doubleDiskRel n)

/-- Membership for the upper hemisphere: `(d, √(1-‖d‖²))` has norm 1. -/
theorem doubleDiskMap_mem_pos (n : ℕ) (d : Disk (n + 1)) :
    esnoc (d : EuclideanSpace ℝ (Fin (n + 1)))
      (Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) ∈ Sphere (n + 1) := by
  rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc]
  have hd' : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    simpa using (mem_closedBall_iff_norm.mp d.2)
  have hle : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    simpa [abs_of_nonneg (norm_nonneg _)] using hd'
  have hpos : 0 ≤ 1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := sub_nonneg.mpr hle
  calc
    ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 +
        Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) ^ 2
        = ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 +
          (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) := by
          rw [Real.sq_sqrt hpos]
    _ = 1 := by ring

/-- Membership for the lower hemisphere: `(d, -√(1-‖d‖²))` has norm 1. -/
theorem doubleDiskMap_mem_neg (n : ℕ) (d : Disk (n + 1)) :
    esnoc (d : EuclideanSpace ℝ (Fin (n + 1)))
      (-Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) ∈ Sphere (n + 1) := by
  rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc]
  have hd' : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    simpa using (mem_closedBall_iff_norm.mp d.2)
  have hle : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    simpa [abs_of_nonneg (norm_nonneg _)] using hd'
  have hpos : 0 ≤ 1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := sub_nonneg.mpr hle
  calc
    ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 +
        (-Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) ^ 2
        = ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 +
          (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) := by
          rw [neg_sq, Real.sq_sqrt hpos]
    _ = 1 := by ring

/-- The gluing map: upper hemisphere `inl d ↦ (d, √(1-‖d‖²))`, lower hemisphere
`inr d ↦ (d, -√(1-‖d‖²))`.  On the boundary `‖d‖ = 1` both formulas give `(d, 0)`. -/
def doubleDiskMap (n : ℕ) : DoubleDisk n → Sphere (n + 1) :=
  Sum.elim
    (fun d => ⟨esnoc (d : EuclideanSpace ℝ (Fin (n + 1)))
      (Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)), doubleDiskMap_mem_pos n d⟩)
    (fun d => ⟨esnoc (d : EuclideanSpace ℝ (Fin (n + 1)))
      (-Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)), doubleDiskMap_mem_neg n d⟩)

/-- The gluing map is continuous. -/
theorem continuous_doubleDiskMap (n : ℕ) : Continuous (doubleDiskMap n) := by
  rw [doubleDiskMap]
  refine (continuous_sumElim).2 ?_
  constructor
  · -- upper hemisphere
    have hd : Continuous fun d : Disk (n + 1) => (d : EuclideanSpace ℝ (Fin (n + 1))) :=
      continuous_subtype_val
    have hnorm : Continuous fun d : Disk (n + 1) => ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
      continuous_norm.comp hd
    have hsq : Continuous fun d : Disk (n + 1) =>
        1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 :=
      Continuous.sub continuous_const (hnorm.pow 2)
    have hsqrt : Continuous fun d : Disk (n + 1) =>
        Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) :=
      Continuous.sqrt hsq
    refine Continuous.subtype_mk ?_ (fun d => doubleDiskMap_mem_pos n d)
    have hcont_pi : Continuous fun d : Disk (n + 1) =>
        @Fin.snoc (n + 1) (fun _ : Fin (n + 2) => ℝ)
          (fun i : Fin (n + 1) => (d : EuclideanSpace ℝ (Fin (n + 1))) i)
          (Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) := by
      fun_prop
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 2) => ℝ)).comp hcont_pi
  · -- lower hemisphere
    have hd : Continuous fun d : Disk (n + 1) => (d : EuclideanSpace ℝ (Fin (n + 1))) :=
      continuous_subtype_val
    have hnorm : Continuous fun d : Disk (n + 1) => ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
      continuous_norm.comp hd
    have hsq : Continuous fun d : Disk (n + 1) =>
        1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 :=
      Continuous.sub continuous_const (hnorm.pow 2)
    have hsqrt : Continuous fun d : Disk (n + 1) =>
        Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) :=
      Continuous.sqrt hsq
    refine Continuous.subtype_mk ?_ (fun d => doubleDiskMap_mem_neg n d)
    have hcont_pi : Continuous fun d : Disk (n + 1) =>
        @Fin.snoc (n + 1) (fun _ : Fin (n + 2) => ℝ)
          (fun i : Fin (n + 1) => (d : EuclideanSpace ℝ (Fin (n + 1))) i)
          (-Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) := by
      fun_prop
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 2) => ℝ)).comp hcont_pi

/-- The gluing map respects the gluing relation. -/
theorem doubleDiskMap_respects (n : ℕ) (p q : DoubleDisk n) :
    doubleDiskRel n p q → doubleDiskMap n p = doubleDiskMap n q := by
  intro h
  rcases h with h | h | h
  · subst h
    rfl
  · rcases h with ⟨d, e, rfl, rfl, hde, hd⟩
    apply Subtype.ext
    have hnorm : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp hd
    have hsqrt : Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) = 0 := by
      rw [hnorm, one_pow, sub_self, Real.sqrt_zero]
    subst hde
    simp [doubleDiskMap, hsqrt]
  · rcases h with ⟨d, e, rfl, rfl, hde, hd⟩
    apply Subtype.ext
    have hnorm : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp hd
    have hsqrt : Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) = 0 := by
      rw [hnorm, one_pow, sub_self, Real.sqrt_zero]
    subst hde
    simp [doubleDiskMap, hsqrt]

/-- The descended gluing map `DoubleDiskQuot n → Sphere (n+1)` is continuous. -/
noncomputable def doubleDiskMapQuot (n : ℕ) : DoubleDiskQuot n → Sphere (n + 1) :=
  Quot.lift (doubleDiskMap n) (doubleDiskMap_respects n)

/-- Continuity of the descended gluing map. -/
theorem continuous_doubleDiskMapQuot (n : ℕ) : Continuous (doubleDiskMapQuot n) :=
  continuous_quot_lift (doubleDiskMap_respects n) (continuous_doubleDiskMap n)

/-- Surjectivity: every `(y, z) ∈ Sⁿ⁺¹` lies on the upper (`z ≥ 0`) or lower (`z < 0`)
hemisphere, i.e. is the image of `y` in the corresponding disk copy. -/
theorem doubleDiskMapQuot_surjective (n : ℕ) : Function.Surjective (doubleDiskMapQuot n) := by
  intro v
  let y : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (fun j : Fin (n + 1) => (v : EuclideanSpace ℝ (Fin (n + 2))) j.castSucc)
  let z : ℝ := (v : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))
  have hv : (v : EuclideanSpace ℝ (Fin (n + 2))) = esnoc y z := by
    apply PiLp.ext
    intro i
    refine Fin.lastCases (n := n + 1) ?_ ?_ i
    · simp [z, esnoc_last]
    · intro j
      simp [y, esnoc_castSucc]
  have hnorm : ‖y‖ ^ 2 + z ^ 2 = 1 := by
    have := mem_sphere_zero_iff_norm.mp v.2
    rw [hv] at this
    have hsq := congrArg (fun t : ℝ => t ^ 2) this
    simpa [norm_sq_esnoc] using hsq
  have hy_mem : y ∈ Disk (n + 1) := by
    rw [mem_closedBall_iff_norm]
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by
      have : ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + z ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      simpa [hnorm] using this
    have hyl : ‖y‖ ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one] at hy2
      simpa [abs_of_nonneg (norm_nonneg _)] using (abs_le.mp hy2).2
    simpa using hyl
  by_cases hz : 0 ≤ z
  · refine ⟨Quot.mk _ (Sum.inl ⟨y, hy_mem⟩), ?_⟩
    apply Subtype.ext
    rw [hv]
    have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = z := by
      have hz2 : z ^ 2 = 1 - ‖y‖ ^ 2 := by
        linarith
      calc
        Real.sqrt (1 - ‖y‖ ^ 2) = Real.sqrt (z ^ 2) := by rw [hz2]
        _ = |z| := Real.sqrt_sq_eq_abs _
        _ = z := abs_of_nonneg hz
    simp [doubleDiskMapQuot, doubleDiskMap, hsqrt]
  · refine ⟨Quot.mk _ (Sum.inr ⟨y, hy_mem⟩), ?_⟩
    apply Subtype.ext
    rw [hv]
    have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = -z := by
      have hz2 : z ^ 2 = 1 - ‖y‖ ^ 2 := by
        linarith
      calc
        Real.sqrt (1 - ‖y‖ ^ 2) = Real.sqrt (z ^ 2) := by rw [hz2]
        _ = |z| := Real.sqrt_sq_eq_abs _
        _ = -z := abs_of_neg (lt_of_not_ge hz)
    simp [doubleDiskMapQuot, doubleDiskMap, hsqrt]

/-- `√a = -√a` forces `a = 0` (for `a ≥ 0`): the two hemisphere formulas can agree only
on the equator. -/
theorem eq_neg_self_of_sqrt_eq_neg_sqrt {a : ℝ} (ha : 0 ≤ a)
    (h : Real.sqrt a = -Real.sqrt a) : a = 0 := by
  have hsq : Real.sqrt a = 0 := by
    nlinarith
  calc
    a = (Real.sqrt a) ^ 2 := (Real.sq_sqrt ha).symm
    _ = 0 := by rw [hsq, zero_pow two_ne_zero]

/-- Injectivity: two hemisphere points agree only within the same hemisphere, or on the
equator `‖d‖ = 1` where the gluing relation identifies the two copies. -/
theorem doubleDiskMapQuot_injective (n : ℕ) : Function.Injective (doubleDiskMapQuot n) := by
  intro a b h
  revert h b
  refine Quot.inductionOn a ?_
  intro p b h
  revert h
  refine Quot.inductionOn b ?_
  intro q hpq
  apply Quot.sound
  have hval' : doubleDiskMapQuot n (Quot.mk (doubleDiskRel n) p) =
      doubleDiskMapQuot n (Quot.mk (doubleDiskRel n) q) := hpq
  have hval : (doubleDiskMap n p : EuclideanSpace ℝ (Fin (n + 2))) =
      (doubleDiskMap n q : EuclideanSpace ℝ (Fin (n + 2))) := by
    have : doubleDiskMap n p = doubleDiskMap n q := by
      simpa [doubleDiskMapQuot] using hval'
    exact congrArg Subtype.val this
  rcases p with d | d <;> rcases q with e | e
  · -- inl d, inl e: same hemisphere
    left
    apply congrArg Sum.inl
    apply Subtype.ext
    simp only [doubleDiskMap] at hval
    exact (esnoc_injective2 hval).1
  · -- inl d, inr e: must glue on the equator
    right
    left
    simp only [doubleDiskMap] at hval
    have hsnoc := esnoc_injective2 hval
    have hde : (d : EuclideanSpace ℝ (Fin (n + 1))) =
        (e : EuclideanSpace ℝ (Fin (n + 1))) := hsnoc.1
    have hd_bound : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 ≤ 1 := by
      have hd' : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
        simpa using (mem_closedBall_iff_norm.mp d.2)
      rw [sq_le_one_iff_abs_le_one]
      simpa [abs_of_nonneg (norm_nonneg _)] using hd'
    have hzero : 1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 0 := by
      apply eq_neg_self_of_sqrt_eq_neg_sqrt (sub_nonneg.mpr hd_bound)
      simpa [hde] using hsnoc.2
    have hnorm : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      have hsq : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 1 := by
        linarith
      have : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 ∨
          ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = -1 := sq_eq_one_iff.mp hsq
      rcases this with h1 | h2
      · exact h1
      · have : 0 ≤ ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ := norm_nonneg _
        linarith
    refine ⟨d, e, rfl, rfl, ?_, ?_⟩
    · apply Subtype.ext
      exact hde
    · rwa [mem_sphere_zero_iff_norm]
  · -- inr d, inl e: symmetric
    right
    right
    simp only [doubleDiskMap] at hval
    have hsnoc := esnoc_injective2 hval
    have hde : (d : EuclideanSpace ℝ (Fin (n + 1))) =
        (e : EuclideanSpace ℝ (Fin (n + 1))) := hsnoc.1
    have hd_bound : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 ≤ 1 := by
      have hd' : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
        simpa using (mem_closedBall_iff_norm.mp d.2)
      rw [sq_le_one_iff_abs_le_one]
      simpa [abs_of_nonneg (norm_nonneg _)] using hd'
    have hzero : 1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 0 := by
      apply eq_neg_self_of_sqrt_eq_neg_sqrt (sub_nonneg.mpr hd_bound)
      have h' : Real.sqrt (1 - ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) =
          -Real.sqrt (1 - ‖(e : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) := by
        exact neg_eq_iff_eq_neg.mp hsnoc.2
      simpa [hde] using h'
    have hnorm : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      have hsq : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 1 := by
        linarith
      have : ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 ∨
          ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ = -1 := sq_eq_one_iff.mp hsq
      rcases this with h1 | h2
      · exact h1
      · have : 0 ≤ ‖(d : EuclideanSpace ℝ (Fin (n + 1)))‖ := norm_nonneg _
        linarith
    refine ⟨d, e, rfl, rfl, ?_, ?_⟩
    · apply Subtype.ext
      exact hde
    · rwa [mem_sphere_zero_iff_norm]
  · -- inr d, inr e: same hemisphere
    left
    apply congrArg Sum.inr
    apply Subtype.ext
    simp only [doubleDiskMap] at hval
    exact (esnoc_injective2 hval).1

/-- **Theorem 3.** Gluing two `(n+1)`-disks along their common boundary `n`-sphere
yields the `(n+1)`-sphere: `Sⁿ⁺¹ = Dⁿ⁺¹ ∪_{Sⁿ} Dⁿ⁺¹`. -/
noncomputable def doubleDiskQuotHomeoSphere (n : ℕ) : DoubleDiskQuot n ≃ₜ Sphere (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (doubleDiskMapQuot n)
      ⟨doubleDiskMapQuot_injective n, doubleDiskMapQuot_surjective n⟩)
    (continuous_doubleDiskMapQuot n)

/-! ## TopCat corollaries -/

open scoped TopCat

/-- **TopCat corollary of Theorem 1.** The cone over `𝕊 n` is homeomorphic to the
closed `(n+1)`-disk `𝔻 (n+1)` (through the `ULift` wrapper of `TopCat.disk`). -/
noncomputable def coneQuotHomeoTopCatDisk (n : ℕ) : ULift (ConeQuot n) ≃ₜ TopCat.disk (n + 1) := by
  change ULift (ConeQuot n) ≃ₜ ULift (Disk (n + 1))
  exact (Homeomorph.ulift : ULift (ConeQuot n) ≃ₜ ConeQuot n).trans
    ((coneQuotHomeoDisk n).trans
      (Homeomorph.ulift : ULift (Disk (n + 1)) ≃ₜ Disk (n + 1)).symm)

/-- **TopCat corollary of Theorem 2.** The suspension of `𝕊 n` is homeomorphic to the
`(n+1)`-sphere `𝕊 (n+1)`. -/
noncomputable def suspQuotHomeoTopCatSphere (n : ℕ) : ULift (SuspQuot n) ≃ₜ TopCat.sphere (n + 1) := by
  change ULift (SuspQuot n) ≃ₜ ULift (Sphere (n + 1))
  exact (Homeomorph.ulift : ULift (SuspQuot n) ≃ₜ SuspQuot n).trans
    ((suspQuotHomeoSphere n).trans
      (Homeomorph.ulift : ULift (Sphere (n + 1)) ≃ₜ Sphere (n + 1)).symm)

/-- **TopCat corollary of Theorem 3.** Gluing two `(n+1)`-disks along `∂𝔻 (n+1)` yields
the `(n+1)`-sphere `𝕊 (n+1)`. -/
noncomputable def doubleDiskQuotHomeoTopCatSphere (n : ℕ) :
    ULift (DoubleDiskQuot n) ≃ₜ TopCat.sphere (n + 1) := by
  change ULift (DoubleDiskQuot n) ≃ₜ ULift (Sphere (n + 1))
  exact (Homeomorph.ulift : ULift (DoubleDiskQuot n) ≃ₜ DoubleDiskQuot n).trans
    ((doubleDiskQuotHomeoSphere n).trans
      (Homeomorph.ulift : ULift (Sphere (n + 1)) ≃ₜ Sphere (n + 1)).symm)

end Poincare.D12.TriangulationTopology
