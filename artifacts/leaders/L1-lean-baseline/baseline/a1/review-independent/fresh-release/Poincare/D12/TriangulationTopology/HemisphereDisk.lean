/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib
import Poincare.D12.TriangulationTopology.SphereGluing

/-!
# Poincare.D12.TriangulationTopology.HemisphereDisk

**DAG node 10, proved.** The closed lower hemisphere of the `n`-sphere (last coordinate
`≤ 0`) is homeomorphic to the closed `n`-disk: `{x ∈ 𝕊ⁿ | x_last ≤ 0} ≃ₜ 𝔻ⁿ`.
Together with the proved gluing `doubleDiskQuotHomeoSphere` (node 7) this closes the
induction `S³ # S³ ≅ S³` over the finite extinction decomposition of sphere recognition.

## Construction

Explicit graph-of-a-function formulas (the same `esnoc`/`norm_sq_esnoc` algebra as
`SphereGluing.lean`):

* Forward: `x ↦ x` restricted to the first `n` coordinates (the vertical projection of the
  hemisphere onto the equatorial disk);
* Backward: `y ↦ (y, -√(1 - ‖y‖²))` (the graph of the southern hemisphere).

The norm identity `‖esnoc w s‖² = ‖w‖² + s²` plus `‖x‖ = 1`, `x_last ≤ 0` checks
membership, injectivity (`√(1-‖w‖²) = -s` when `‖w‖² + s² = 1` and `s ≤ 0`), and the two
maps are mutually inverse by `esnoc_castSucc`/`esnoc_last`.

## Provenance of external mathematics

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by lake-manifest.json),
  Apache-2.0: all imported lemmas.  The hemisphere/disk radial formulas are classical;
  all proofs here are original to this worktree.
-/

noncomputable section

open scoped Topology
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## The closed lower hemisphere -/

/-- The closed lower hemisphere of `𝕊ⁿ`: points of the unit `n`-sphere in `ℝⁿ⁺¹` with
last coordinate `≤ 0`. -/
abbrev LowerHemisphere (n : ℕ) :=
  {x : Sphere n // (x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) ≤ 0}

-- The `esnoc` helper of `SphereGluing.lean` appends to `Fin (n+1)`; here we need the
-- version appending to `Fin n` (target `ℝⁿ⁺¹`), including `n = 0`.
/-- Append a last coordinate to a point of `ℝⁿ` to get a point of `ℝⁿ⁺¹`. -/
def esnoc' (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (@Fin.snoc n (fun _ : Fin (n + 1) => ℝ) (fun i : Fin n => w i) s)

@[simp] theorem esnoc'_last {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    esnoc' n w s (Fin.last n) = s := by
  simp [esnoc', Fin.snoc_last]

@[simp] theorem esnoc'_castSucc {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (s : ℝ)
    (j : Fin n) : esnoc' n w s j.castSucc = w j := by
  simp [esnoc', Fin.snoc_castSucc]

/-- Squared-norm decomposition for `esnoc'`: `‖esnoc' w s‖² = ‖w‖² + s²`. -/
theorem norm_sq_esnoc' {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    ‖esnoc' n w s‖ ^ 2 = ‖w‖ ^ 2 + s ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_castSucc]
  simp only [esnoc'_castSucc, esnoc'_last, Real.norm_eq_abs, sq_abs]

/-- Drop the last coordinate: the vertical projection of `ℝⁿ⁺¹` onto `ℝⁿ`. -/
def lowerTrunc (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n => x j.castSucc)

/-- Reattaching the last coordinate reconstructs the point (`esnoc'`/`Fin.snoc` identity). -/
theorem esnoc'_lowerTrunc_eq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    esnoc' n (lowerTrunc n x) (x (Fin.last n)) = x := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases (n := n)
    (motive := fun i => esnoc' n (lowerTrunc n x) (x (Fin.last n)) i = x i) ?_ ?_ i
  · simp
  · intro j
    simp [lowerTrunc]

/-- On the unit sphere, `‖trunc x‖² + x_last² = 1`. -/
theorem trunc_norm_sq_add_last_sq_eq_one (n : ℕ) (x : LowerHemisphere n) :
    ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2
      + ((x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) ^ 2 = 1 := by
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp x.1.2
  rw [← norm_sq_esnoc', esnoc'_lowerTrunc_eq, hxnorm, one_pow]

/-- For a unit vector with nonpositive last coordinate,
`√(1 - ‖trunc x‖²) = -x_last`. -/
theorem sqrt_one_sub_trunc_norm_sq_eq_neg_last (n : ℕ) (x : LowerHemisphere n) :
    Real.sqrt (1 - ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)
      = -((x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) := by
  have hsq := trunc_norm_sq_add_last_sq_eq_one n x
  have hsub : 1 - ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2
      = ((x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) ^ 2 := by
    linarith
  rw [hsub, Real.sqrt_sq_eq_abs, abs_of_nonpos x.2]

/-! ## The two maps -/

/-- Forward map: restrict a hemisphere point to its first `n` coordinates (the disk
membership follows from `‖trunc x‖² ≤ 1`). -/
def lowerHemisphereToDisk (n : ℕ) (x : LowerHemisphere n) : Disk n :=
  ⟨lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1))), by
    rw [mem_closedBall_iff_norm, sub_zero]
    have hsq := trunc_norm_sq_add_last_sq_eq_one n x
    have hsqle : ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 ≤ 1 := by
      nlinarith
    simpa [abs_of_nonneg (norm_nonneg _)] using
      (sq_le_one_iff_abs_le_one ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖).mp hsqle⟩

/-- Backward map: the graph of the southern hemisphere `y ↦ (y, -√(1-‖y‖²))`. -/
def diskToLowerHemisphere (n : ℕ) (y : Disk n) : LowerHemisphere n :=
  ⟨⟨esnoc' n (y : EuclideanSpace ℝ (Fin n)) (-Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)),
      by
        rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc']
        have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
          simpa [sub_zero] using (mem_closedBall_iff_norm.mp y.2)
        have hsq : ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 1 := by
          nlinarith [hy, norm_nonneg (y : EuclideanSpace ℝ (Fin n))]
        rw [neg_sq, Real.sq_sqrt (sub_nonneg.mpr hsq)]
        ring⟩,
    by
      change esnoc' n (y : EuclideanSpace ℝ (Fin n))
          (-Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)) (Fin.last n) ≤ 0
      simp only [esnoc'_last]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)⟩

/-- Continuity of `esnoc'` in both arguments. -/
theorem continuous_esnoc' (n : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => esnoc' n p.1 p.2) := by
  unfold esnoc'
  refine PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ) |>.comp ?_
  apply continuous_pi
  intro i
  refine Fin.lastCases (n := n)
    (motive := fun i => Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      @Fin.snoc n (fun _ : Fin (n + 1) => ℝ) (fun j : Fin n => p.1 j) p.2 i)) ?_ ?_ i
  · simpa using continuous_snd
  · intro j
    simp only [Fin.snoc_castSucc]
    change Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1.ofLp j)
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) j).comp continuous_fst

/-- Continuity of the forward map. -/
theorem continuous_lowerHemisphereToDisk (n : ℕ) : Continuous (lowerHemisphereToDisk n) := by
  exact Continuous.subtype_mk
    (f := fun x : LowerHemisphere n => lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1))))
    (h := PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ) |>.comp (by
      apply continuous_pi
      intro j
      exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) j.castSucc).comp
        continuous_subtype_val).comp continuous_subtype_val))
    (hp := fun x => (lowerHemisphereToDisk n x).2)

/-- Continuity of the backward map. -/
theorem continuous_diskToLowerHemisphere (n : ℕ) : Continuous (diskToLowerHemisphere n) := by
  exact Continuous.subtype_mk
    (f := fun y : Disk n => (⟨esnoc' n (y : EuclideanSpace ℝ (Fin n))
      (-Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)), by
        rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc']
        have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
          simpa [sub_zero] using (mem_closedBall_iff_norm.mp y.2)
        have hsq : ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 1 := by
          nlinarith [hy, norm_nonneg (y : EuclideanSpace ℝ (Fin n))]
        rw [neg_sq, Real.sq_sqrt (sub_nonneg.mpr hsq)]
        ring⟩ : Sphere n))
    (h := by
      exact Continuous.subtype_mk
        (f := fun y : Disk n => esnoc' n (y : EuclideanSpace ℝ (Fin n))
          (-Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)))
        (h := continuous_esnoc' n |>.comp (by
          refine Continuous.prodMk
            (g := fun y : Disk n => -Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2))
            continuous_subtype_val ?_
          exact continuous_neg.comp
            ((continuous_const.sub ((Continuous.norm continuous_subtype_val).pow 2)).sqrt)))
        (hp := fun y => (diskToLowerHemisphere n y).1.2))
    (hp := fun y => (diskToLowerHemisphere n y).2)

/-! ## Mutually inverse -/

/-- `toFun (invFun y) = y`. -/
theorem lowerHemisphereToDisk_diskToLowerHemisphere (n : ℕ) (y : Disk n) :
    lowerHemisphereToDisk n (diskToLowerHemisphere n y) = y := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  simp [lowerHemisphereToDisk, diskToLowerHemisphere, lowerTrunc]

/-- `invFun (toFun x) = x`. -/
theorem diskToLowerHemisphere_lowerHemisphereToDisk (n : ℕ) (x : LowerHemisphere n) :
    diskToLowerHemisphere n (lowerHemisphereToDisk n x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.lastCases (n := n)
    (motive := fun i => (diskToLowerHemisphere n (lowerHemisphereToDisk n x) :
      EuclideanSpace ℝ (Fin (n + 1))) i = (x : EuclideanSpace ℝ (Fin (n + 1))) i) ?_ ?_ i
  · have hsqrt := sqrt_one_sub_trunc_norm_sq_eq_neg_last n x
    dsimp [diskToLowerHemisphere, lowerHemisphereToDisk]
    rw [esnoc'_last]
    linarith
  · intro j
    dsimp [diskToLowerHemisphere, lowerHemisphereToDisk]
    rw [esnoc'_castSucc]
    rfl

/-! ## The homeomorphism -/

/-- **DAG node 10, exact ledger statement.** The closed lower hemisphere of `𝕊ⁿ` is
homeomorphic to the closed `n`-disk. -/
def lowerHemisphereHomeoDisk (n : ℕ) : LowerHemisphere n ≃ₜ Disk n where
  toEquiv :=
    { toFun := lowerHemisphereToDisk n
      invFun := diskToLowerHemisphere n
      left_inv := diskToLowerHemisphere_lowerHemisphereToDisk n
      right_inv := lowerHemisphereToDisk_diskToLowerHemisphere n }
  continuous_toFun := continuous_lowerHemisphereToDisk n
  continuous_invFun := continuous_diskToLowerHemisphere n

/-! ## Audits: compactness, T2, nonemptiness, shape examples -/

/-- **Compactness audit.** The closed lower hemisphere is compact. -/
instance lowerHemisphereCompactSpace (n : ℕ) : CompactSpace (LowerHemisphere n) :=
  Homeomorph.compactSpace (lowerHemisphereHomeoDisk n).symm

/-- **T2 audit.** The closed lower hemisphere is Hausdorff. -/
instance lowerHemisphereT2Space (n : ℕ) : T2Space (LowerHemisphere n) :=
  Homeomorph.t2Space (lowerHemisphereHomeoDisk n).symm

/-- **Nonemptiness audit.** The closed lower hemisphere is nonempty (e.g. the south pole). -/
instance lowerHemisphereNonempty (n : ℕ) : Nonempty (LowerHemisphere n) :=
  Nonempty.map (lowerHemisphereHomeoDisk n).symm (diskNonempty n)

/-- **Shape example.** The closed lower hemisphere of `𝕊³` is the closed `3`-disk
`D³ ⊂ ℝ³`: the complement-of-a-hemisphere lemma behind `S³ # S³ ≅ S³`. -/
example : LowerHemisphere 3 ≃ₜ Disk 3 :=
  lowerHemisphereHomeoDisk 3

/-- **Shape example.** The closed lower semicircle is the unit interval-disk `D¹`. -/
example : LowerHemisphere 1 ≃ₜ Disk 1 :=
  lowerHemisphereHomeoDisk 1

/-- **Shape example.** The lower hemisphere of `𝕊⁰` is a point, homeomorphic to `D⁰`. -/
example : LowerHemisphere 0 ≃ₜ Disk 0 :=
  lowerHemisphereHomeoDisk 0

end Poincare.D12.TriangulationTopology
