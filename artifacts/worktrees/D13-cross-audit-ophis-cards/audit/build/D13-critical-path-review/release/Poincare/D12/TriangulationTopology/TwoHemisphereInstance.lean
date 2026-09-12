/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Non-vacuity instance for closed-cover sphere recognition

`sphereOfTwoDisks` (in `SphereOfTwoDisks.lean`) recognises `𝕊ⁿ⁺¹` from a compact Hausdorff
space covered by two closed `(n+1)`-balls whose intersection is the boundary sphere of the
first chart.  This file proves that its hypotheses are **satisfiable**, by exhibiting them
for the standard two-hemisphere decomposition of `𝕊ⁿ⁺¹`:

* `UpperHemisphere n ≃ₜ Disk n` (the mirrored chart `y ↦ (y, +√(1-‖y‖²))`, complementing
  `lowerHemisphereHomeoDisk` of `HemisphereDisk.lean`);
* the two closed hemispheres cover `𝕊ⁿ⁺¹` and meet exactly in the equator;
* the first chart maps the equator onto the boundary sphere, and the two charts agree on
  the equator with `h = id`;
* hence `sphereOfTwoDisks` applies and yields `𝕊ⁿ⁺¹ ≃ₜ 𝕊ⁿ⁺¹` for the concrete hypotheses.

## Provenance

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned), Apache-2.0: imported
  lemmas only.  Proofs original for this worktree (the upper-hemisphere chart mirrors the
  lower-hemisphere construction of `HemisphereDisk.lean` from this worktree).
-/

import Poincare.D12.TriangulationTopology.SphereOfTwoDisks
import Poincare.D12.TriangulationTopology.HemisphereDisk

noncomputable section

open scoped Topology
open Set Function Filter

namespace Poincare.D12.TriangulationTopology

/-! ## The mirrored (upper) hemisphere chart -/

/-- The closed **upper** hemisphere of `𝕊ⁿ`. -/
abbrev UpperHemisphere (n : ℕ) : Type :=
  {x : Sphere n // 0 ≤ (x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)}

/-- Squared-norm decomposition for a sphere point: `‖trunc x‖² + x_last² = 1`. -/
theorem sphere_trunc_norm_sq_add_last_sq_eq_one (n : ℕ) (x : Sphere n) :
    ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2
      + ((x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) ^ 2 = 1 := by
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.2
  rw [← norm_sq_esnoc', esnoc'_lowerTrunc_eq, hxnorm, one_pow]

/-- On the upper hemisphere, `√(1-‖trunc x‖²) = x_last`. -/
theorem sqrt_one_sub_trunc_norm_sq_eq_last (n : ℕ) (x : UpperHemisphere n) :
    Real.sqrt (1 - ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)
      = (x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n) := by
  have hsq := sphere_trunc_norm_sq_add_last_sq_eq_one n x.1
  have hsub : 1 - ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2
      = ((x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)) ^ 2 := by
    linarith
  rw [hsub, Real.sqrt_sq_eq_abs, abs_of_nonneg x.2]

/-- Forward map of the upper chart: restrict to the first `n` coordinates. -/
def upperHemisphereToDisk (n : ℕ) (x : UpperHemisphere n) : Disk n :=
  ⟨lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1))), by
    rw [mem_closedBall_iff_norm, sub_zero]
    have hsq := sphere_trunc_norm_sq_add_last_sq_eq_one n x.1
    have hsqle : ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((x : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n))]
    simpa [abs_of_nonneg (norm_nonneg _)] using
      (sq_le_one_iff_abs_le_one ‖lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1)))‖).mp hsqle⟩

/-- Backward map of the upper chart: the graph `y ↦ (y, +√(1-‖y‖²))`. -/
def diskToUpperHemisphere (n : ℕ) (y : Disk n) : UpperHemisphere n :=
  ⟨⟨esnoc' n (y : EuclideanSpace ℝ (Fin n))
      (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)), by
        rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc']
        have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
          simpa [sub_zero] using (mem_closedBall_iff_norm.mp y.2)
        have hsq : ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 1 := by
          nlinarith [hy, norm_nonneg (y : EuclideanSpace ℝ (Fin n))]
        rw [Real.sq_sqrt (sub_nonneg.mpr hsq)]
        ring⟩,
    by
      change 0 ≤ esnoc' n (y : EuclideanSpace ℝ (Fin n))
          (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)) (Fin.last n)
      simp only [esnoc'_last]
      exact Real.sqrt_nonneg _⟩

/-- Continuity of the upper forward map. -/
theorem continuous_upperHemisphereToDisk (n : ℕ) : Continuous (upperHemisphereToDisk n) := by
  exact Continuous.subtype_mk
    (f := fun x : UpperHemisphere n => lowerTrunc n (x : EuclideanSpace ℝ (Fin (n + 1))))
    (h := PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ) |>.comp (by
      apply continuous_pi
      intro j
      exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ) j.castSucc).comp
        continuous_subtype_val).comp continuous_subtype_val))
    (hp := fun x => (upperHemisphereToDisk n x).2)

/-- Continuity of the upper backward map. -/
theorem continuous_diskToUpperHemisphere (n : ℕ) : Continuous (diskToUpperHemisphere n) := by
  exact Continuous.subtype_mk
    (f := fun y : Disk n => (⟨esnoc' n (y : EuclideanSpace ℝ (Fin n))
      (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)), by
        rw [mem_sphere_zero_iff_norm, norm_eq_one_iff_norm_sq_eq_one, norm_sq_esnoc']
        have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
          simpa [sub_zero] using (mem_closedBall_iff_norm.mp y.2)
        have hsq : ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 1 := by
          nlinarith [hy, norm_nonneg (y : EuclideanSpace ℝ (Fin n))]
        rw [Real.sq_sqrt (sub_nonneg.mpr hsq)]
        ring⟩ : Sphere n))
    (h := by
      exact Continuous.subtype_mk
        (f := fun y : Disk n => esnoc' n (y : EuclideanSpace ℝ (Fin n))
          (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)))
        (h := continuous_esnoc' n |>.comp (by
          refine Continuous.prodMk
            (g := fun y : Disk n => Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2))
            continuous_subtype_val ?_
          exact (continuous_const.sub ((Continuous.norm continuous_subtype_val).pow 2)).sqrt))
        (hp := fun y => (diskToUpperHemisphere n y).1.2))
    (hp := fun y => (diskToUpperHemisphere n y).2)

/-- `toFun (invFun y) = y` for the upper chart. -/
theorem upperHemisphereToDisk_diskToUpperHemisphere (n : ℕ) (y : Disk n) :
    upperHemisphereToDisk n (diskToUpperHemisphere n y) = y := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  simp [upperHemisphereToDisk, diskToUpperHemisphere, lowerTrunc]

/-- `invFun (toFun x) = x` for the upper chart. -/
theorem diskToUpperHemisphere_upperHemisphereToDisk (n : ℕ) (x : UpperHemisphere n) :
    diskToUpperHemisphere n (upperHemisphereToDisk n x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.lastCases (n := n)
    (motive := fun i => (diskToUpperHemisphere n (upperHemisphereToDisk n x) :
      EuclideanSpace ℝ (Fin (n + 1))) i = (x : EuclideanSpace ℝ (Fin (n + 1))) i) ?_ ?_ i
  · have hsqrt := sqrt_one_sub_trunc_norm_sq_eq_last n x
    dsimp [diskToUpperHemisphere, upperHemisphereToDisk]
    rw [esnoc'_last]
    linarith
  · intro j
    dsimp [diskToUpperHemisphere, upperHemisphereToDisk]
    rw [esnoc'_castSucc]
    rfl

/-- **Audit companion of DAG node 10.** The closed upper hemisphere of `𝕊ⁿ` is homeomorphic
to the closed `n`-disk (mirror image of `lowerHemisphereHomeoDisk`). -/
def upperHemisphereHomeoDisk (n : ℕ) : UpperHemisphere n ≃ₜ Disk n where
  toEquiv :=
    { toFun := upperHemisphereToDisk n
      invFun := diskToUpperHemisphere n
      left_inv := diskToUpperHemisphere_upperHemisphereToDisk n
      right_inv := upperHemisphereToDisk_diskToUpperHemisphere n }
  continuous_toFun := continuous_upperHemisphereToDisk n
  continuous_invFun := continuous_diskToUpperHemisphere n

/-- **Compactness audit.** The closed upper hemisphere is compact. -/
instance upperHemisphereCompactSpace (n : ℕ) : CompactSpace (UpperHemisphere n) :=
  Homeomorph.compactSpace (upperHemisphereHomeoDisk n).symm

/-- **T2 audit.** The closed upper hemisphere is Hausdorff. -/
instance upperHemisphereT2Space (n : ℕ) : T2Space (UpperHemisphere n) :=
  Homeomorph.t2Space (upperHemisphereHomeoDisk n).symm

/-- **Nonemptiness audit.** The closed upper hemisphere is nonempty (the north pole). -/
instance upperHemisphereNonempty (n : ℕ) : Nonempty (UpperHemisphere n) :=
  Nonempty.map (upperHemisphereHomeoDisk n).symm (diskNonempty n)

/-! ## The two-hemisphere instance of closed-cover recognition -/

/-- **Non-vacuity input (boundary).**  For the closed lower hemisphere of `𝕊ⁿ⁺¹`, the lower
chart carries a point to the boundary sphere of `𝔻ⁿ⁺¹` exactly when the point also lies in
the upper hemisphere, i.e. on the equator. -/
theorem lowerHemisphere_boundary_eq_inter (n : ℕ) (x : Sphere (n + 1))
    (hx : (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0) :
    (((lowerHemisphereHomeoDisk (n + 1) ⟨x, hx⟩ : Disk (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 1))) ∈ Sphere n) ↔
      0 ≤ (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) := by
  have hval : ((lowerHemisphereHomeoDisk (n + 1) ⟨x, hx⟩ : Disk (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1))) = lowerTrunc (n + 1)
        (x : EuclideanSpace ℝ (Fin (n + 2))) := rfl
  rw [hval, mem_sphere_zero_iff_norm]
  constructor
  · intro hnorm
    have hsq := sphere_trunc_norm_sq_add_last_sq_eq_one (n + 1) x
    have hsq' : (1 : ℝ) +
        ((x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) ^ 2 = 1 := by
      have h := hsq
      rw [hnorm] at h
      simpa using h
    have hzero : ((x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) = 0 := by
      have : ((x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) ^ 2 = 0 := by
        linarith
      exact sq_eq_zero_iff.mp this
    show 0 ≤ ((x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)))
    rw [hzero]
  · intro hxnonneg
    have hzero : ((x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) = 0 :=
      le_antisymm hx hxnonneg
    have hsq := sphere_trunc_norm_sq_add_last_sq_eq_one (n + 1) x
    rw [hzero, zero_pow (by norm_num)] at hsq
    rw [norm_eq_one_iff_norm_sq_eq_one]
    linarith

/-- **Non-vacuity input (closedness).**  The closed lower hemisphere is closed in `𝕊ⁿ⁺¹`. -/
theorem lowerHemisphere_isClosed (n : ℕ) :
    IsClosed {x : Sphere (n + 1) |
      (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0} :=
  isClosed_Iic.preimage
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 2) => ℝ)
      (Fin.last (n + 1))).comp continuous_subtype_val)

/-- **Non-vacuity input (closedness).**  The closed upper hemisphere is closed in `𝕊ⁿ⁺¹`. -/
theorem upperHemisphere_isClosed (n : ℕ) :
    IsClosed {x : Sphere (n + 1) |
      0 ≤ (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))} :=
  isClosed_Ici.preimage
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 2) => ℝ)
      (Fin.last (n + 1))).comp continuous_subtype_val)

/-- **Non-vacuity input (cover).**  The two closed hemispheres cover `𝕊ⁿ⁺¹`. -/
theorem hemisphere_cover (n : ℕ) :
    {x : Sphere (n + 1) | (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0} ∪
      {x : Sphere (n + 1) | 0 ≤ (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))}
      = univ := by
  ext x
  simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
  exact le_total ((x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) 0

/-- **Non-vacuity input (chart compatibility).**  On the equator the two hemisphere charts
agree with the identity gluing. -/
theorem hemisphere_charts_agree (n : ℕ) (x : Sphere (n + 1))
    (hxA : (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0)
    (hxB : 0 ≤ (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) :
    ((upperHemisphereHomeoDisk (n + 1) ⟨x, hxB⟩ : Disk (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 1))) =
      ((sphereToDisk n ⟨lowerHemisphereHomeoDisk (n + 1) ⟨x, hxA⟩,
        (lowerHemisphere_boundary_eq_inter n x hxA).mpr hxB⟩ : Disk (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-- **Non-vacuity instance (node 13a).**  The hypotheses of `sphereOfTwoDisks` are satisfied
by the standard two-hemisphere decomposition of `𝕊ⁿ⁺¹`: the closed lower and upper
hemispheres are closed, cover the sphere, the lower chart carries their intersection (the
equator) exactly onto the boundary sphere, and the two charts agree there with the identity
gluing homeomorphism.  The conclusion is the (trivially true but hypothesis-checking)
homeomorphism `𝕊ⁿ⁺¹ ≃ₜ 𝕊ⁿ⁺¹`, produced by applying `sphereOfTwoDisks` to the concrete
data. -/
noncomputable def sphereOfTwoDisks_hemisphere_instance (n : ℕ) :
    Sphere (n + 1) ≃ₜ Sphere (n + 1) := by
  refine sphereOfTwoDisks n
    {x : Sphere (n + 1) | (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0}
    {x : Sphere (n + 1) | 0 ≤ (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))}
    ?_ ?_ ?_ (lowerHemisphereHomeoDisk (n + 1)) (upperHemisphereHomeoDisk (n + 1))
    (Homeomorph.refl (Sphere n)) ?_ ?_
  · exact lowerHemisphere_isClosed n
  · exact upperHemisphere_isClosed n
  · exact hemisphere_cover n
  · -- the lower chart carries the intersection onto the boundary sphere
    exact lowerHemisphere_boundary_eq_inter n
  · -- the charts agree on the equator with the identity gluing
    intro x hxA hxB
    apply Subtype.ext
    rfl

end Poincare.D12.TriangulationTopology
