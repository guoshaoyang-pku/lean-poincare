/-
Task `D1-pde-api-map`: probe the exact pinned-mathlib API surface needed for a
heat-equation / parabolic maximum-principle development, and check a small set of
toy lemmas.  Every declaration below is fully checked; the file contains no
placeholder proofs and introduces no extra logical assumptions.
-/
import Mathlib

/-!
# `Probe.PdeApi`: PDE API map

Pinned toolchain: `leanprover/lean4:v4.34.0-rc2`; `mathlib` at the revision recorded in
`lake-manifest.json`.  This file is a *probe*: it `#check`s the declarations the
Ricci-flow PDE layer will need and proves a handful of checked toy lemmas, including a
strict finite-grid maximum principle.

## Findings

* **Continuous / differentiable functions.** `Continuous`, `ContinuousOn`, `ContDiff`,
  `ContDiffAt`, `DifferentiableAt`, `DifferentiableOn`, `DifferentiableWithinAt` all exist,
  together with the standard transfer lemmas (`Continuous.continuousOn`,
  `ContDiff.continuous`, `ContDiffAt.differentiableAt`).
* **First derivative.** `HasDerivAt`, `deriv`, `HasDerivAt.deriv`, `hasDerivAt_pow`,
  `deriv_pow`, `deriv_const_mul`, `HasDerivAt.const_mul`.
* **Second derivative.** `iteratedDeriv`, `iteratedDeriv_succ`, `iteratedDeriv_succ'`,
  `iteratedDeriv_zero`; on `ℝ` the Laplacian is the second derivative:
  `InnerProductSpace.laplacian_eq_iteratedDeriv_real`.
* **Interval compactness / extrema.** `isCompact_Icc`, `IsCompact.exists_isMaxOn`,
  `IsCompact.exists_isMinOn`, `isMaxOn_iff`, `isMinOn_iff`,
  `ContinuousOn.exists_isMaxOn'`.
* **Finite grids, recurrences, order.** `Fin n` carries a `LinearOrder`
  (`Fin.instLinearOrder`), `Fin.last`, `Fin.castSucc`, `Fin.succ`; finite extrema via
  `Finset.exists_max_image`, `Finset.max'`, `Finset.max'_mem`, `Finset.le_max'`;
  `Finset.range`, `Finset.mem_range` for grids indexed by `ℕ`.
* **Maximum principle / heat equation.** The pinned mathlib contains **no heat-equation
  theory and no parabolic maximum principle**.  The nearest declarations are the complex
  maximum modulus principle (`Complex.exists_mem_frontier_isMaxOn_norm`), harmonic
  functions (`InnerProductSpace.HarmonicAt`, `InnerProductSpace.HarmonicOnNhd`) and the
  finite maximum principle for convex functions (`ConvexOn.le_max_of_mem_Icc`,
  `ConcaveOn.min_le_of_mem_Icc`).  The continuous heat-equation statement is therefore
  recorded below as an explicit hypothesis-carrying `Prop`-valued structure
  (`HeatSlabMaximumPrincipleInterface`) instead of a theorem; the fully checked
  finite-grid strict maximum principle `strict_finite_grid_max_principle` is separate.
-/

open Set

namespace Probe.PdeApi

/-! ## 1. Continuous and differentiable functions -/

#check @Continuous
#check @ContinuousOn
#check @ContDiff
#check @ContDiffAt
#check @DifferentiableAt
#check @DifferentiableOn
#check @DifferentiableWithinAt
#check @Continuous.continuousOn
#check @ContDiff.continuous
#check @ContDiffAt.differentiableAt

/-! ## 2. First and second derivatives -/

#check @HasDerivAt
#check @deriv
#check @HasDerivAt.deriv
#check @hasDerivAt_pow
#check @deriv_pow
#check @HasDerivAt.const_mul
#check @iteratedDeriv
#check @iteratedDeriv_succ
#check @iteratedDeriv_succ'
#check @iteratedDeriv_zero
#check @Laplacian.laplacian
#check @InnerProductSpace.laplacian_eq_iteratedDeriv_real

/-! ## 3. Interval compactness and extrema -/

#check @isCompact_Icc
#check @IsCompact.exists_isMaxOn
#check @IsCompact.exists_isMinOn
#check @isMaxOn_iff
#check @isMinOn_iff
#check @ContinuousOn.exists_isMaxOn'
#check @IsCompact.exists_isMaxOn_mem_subset

/-! ## 4. Finite grids, recurrences and order structures -/

#check @Fin.instLinearOrder
#check @Fin.last
#check @Fin.castSucc
#check @Fin.succ
#check @Fin.induction
#check @Finset.range
#check @Finset.mem_range
#check @Finset.exists_max_image
#check @Finset.max'
#check @Finset.max'_mem
#check @Finset.le_max'

/-! ## 5. Existing maximum-principle / heat-equation declarations

The search recorded in the result card shows that `Mathlib/Analysis/PDE` does not exist and
that no `HeatEquation` / parabolic maximum principle is present.  The closest existing
declarations are checked here. -/

#check @InnerProductSpace.HarmonicAt
#check @InnerProductSpace.HarmonicOnNhd
#check @Complex.exists_mem_frontier_isMaxOn_norm
#check @ConvexOn.le_max_of_mem_Icc
#check @ConcaveOn.min_le_of_mem_Icc

/-! ## 6. Checked toy lemmas -/

/-- Extreme value theorem on a compact interval, in explicit `∀ y ∈ Icc a b` form. -/
theorem continuousOn_Icc_exists_max {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf
  exact ⟨x, hx, isMaxOn_iff.mp hxmax⟩

/-- First derivative of `x ↦ x ^ 2`. -/
theorem deriv_sq (x : ℝ) : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  rw [(hasDerivAt_pow (𝕜 := ℝ) 2 x).deriv]
  norm_num

/-- Second derivative of `x ↦ x ^ 3`, expressed with `iteratedDeriv 2`. -/
theorem iteratedDeriv_two_cube (x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => y ^ 3) x = 6 * x := by
  have h2 : iteratedDeriv 2 (fun y : ℝ => y ^ 3) = deriv (deriv (fun y : ℝ => y ^ 3)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_zero]
  rw [h2]
  have hf : deriv (fun y : ℝ => y ^ 3) = fun y => 3 * y ^ 2 := by
    funext y
    rw [(hasDerivAt_pow (𝕜 := ℝ) 3 y).deriv]
    norm_num
  rw [hf]
  have hg : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (3 * (2 * x)) x := by
    simpa using (hasDerivAt_pow (𝕜 := ℝ) 2 x).const_mul (3 : ℝ)
  rw [hg.deriv]
  ring

/-- Second difference (discrete Laplacian) on the integer grid. -/
def discreteLaplacian (u : ℤ → ℝ) (i : ℤ) : ℝ :=
  u (i - 1) + u (i + 1) - 2 * u i

/-- Affine sequences are discrete harmonic: their second difference vanishes. -/
theorem discreteLaplacian_affine (a b : ℝ) (i : ℤ) :
    discreteLaplacian (fun j : ℤ => a * (j : ℝ) + b) i = 0 := by
  simp only [discreteLaplacian]
  push_cast
  ring

/-- **Strict finite-grid maximum principle (`max`-of-neighbours form).**

If `u` is strictly discrete subharmonic in the weak sense that its value at every
interior grid point is strictly below the larger of its two neighbours, then every
interior value is strictly below the larger of the two endpoint values.  The grid is
`0, 1, …, N`, so `N` is the last index and `N ≥ 2` is implicit in the existence of
interior points. -/
theorem strict_finite_grid_max_principle_max {N : ℕ} (u : ℕ → ℝ)
    (hsub : ∀ i, 0 < i → i < N → u i < max (u (i - 1)) (u (i + 1))) :
    ∀ i, 0 < i → i < N → u i < max (u 0) (u N) := by
  classical
  intro i hi0 hiN
  by_contra hnot
  simp only [not_lt] at hnot
  -- an index where the maximum of `u` on the grid is attained
  obtain ⟨k, hk_mem, hkmax⟩ :=
    Finset.exists_max_image (Finset.range (N + 1)) u
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
  have hi_mem : i ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_lt hiN))
  -- the interior value at `i` is strictly below the grid maximum
  have hneigh : u i < u k := by
    have h3 := hsub i hi0 hiN
    have h4 : u (i - 1) ≤ u k :=
      hkmax (i - 1) (Finset.mem_range.mpr (by omega))
    have h5 : u (i + 1) ≤ u k :=
      hkmax (i + 1) (Finset.mem_range.mpr (by omega))
    linarith [max_le h4 h5]
  have hui : u i ≤ u k := hkmax i hi_mem
  -- hence the maximizing index cannot be an endpoint
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk] at hneigh
    linarith [le_max_left (u 0) (u N), hnot]
  have hkN : k ≠ N := by
    intro hk
    rw [hk] at hneigh
    linarith [le_max_right (u 0) (u N), hnot]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hklt : k < N := lt_of_le_of_ne hk_le hkN
  -- but at an interior maximizer the strict inequality is impossible
  have h1 : u (k - 1) ≤ u k :=
    hkmax (k - 1) (Finset.mem_range.mpr (by omega))
  have h2 : u (k + 1) ≤ u k :=
    hkmax (k + 1) (Finset.mem_range.mpr (by omega))
  have h3 := hsub k hkpos hklt
  linarith [max_le h1 h2]

/-- **Strict finite-grid maximum principle.**

If `u` is strictly discrete subharmonic (its value at every interior grid point is
strictly below the average of its two neighbours), then every interior value is strictly
below the larger of the two endpoint values.  This is the standard strict discrete
maximum principle; it follows from the `max`-of-neighbours form above because an average
is at most the larger of the two summands. -/
theorem strict_finite_grid_max_principle {N : ℕ} (u : ℕ → ℝ)
    (hsub : ∀ i, 0 < i → i < N → u i < (u (i - 1) + u (i + 1)) / 2) :
    ∀ i, 0 < i → i < N → u i < max (u 0) (u N) := by
  refine strict_finite_grid_max_principle_max u (fun i hi0 hiN => ?_)
  have h := hsub i hi0 hiN
  have havg : (u (i - 1) + u (i + 1)) / 2 ≤ max (u (i - 1)) (u (i + 1)) := by
    linarith [le_max_left (u (i - 1)) (u (i + 1)), le_max_right (u (i - 1)) (u (i + 1))]
  linarith

/-! ## 7. Continuous heat-equation interface (mathlib has no heat-equation theory)

The structure below records the classical maximum principle for the heat equation on the
space-time slab `Icc a b × Icc 0 T` with every hypothesis explicit.  It is a definition of
the *statement*, not an extra assumption: to obtain `bound_nonpos` for a concrete `u` one
must construct the structure, i.e. prove the heat equation, continuity and the boundary
bounds.
The zero solution below shows the interface is inhabited. -/

/-- Interface for the parabolic maximum principle on a slab `[a,b] × [0,T]` for the heat
equation `∂ₜ u = ∂ₓ² u`, with nonpositive initial and lateral data. -/
structure HeatSlabMaximumPrincipleInterface (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop where
  /-- `u` satisfies the heat equation in the interior of the slab. -/
  heat_equation : ∀ x t, x ∈ Icc a b → t ∈ Ioo 0 T →
    deriv (fun s => u x s) t = iteratedDeriv 2 (fun y => u y t) x
  /-- `u` is continuous on the closed slab. -/
  continuousOn_slab : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc a b ×ˢ Icc 0 T)
  /-- The initial datum is nonpositive on `[a,b]`. -/
  initial_nonpos : ∀ x ∈ Icc a b, u x 0 ≤ 0
  /-- The lateral boundary data are nonpositive. -/
  lateral_nonpos : ∀ t ∈ Icc 0 T, u a t ≤ 0 ∧ u b t ≤ 0
  /-- Conclusion of the parabolic maximum principle: `u ≤ 0` on the slab. -/
  bound_nonpos : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0

/-- Eliminating the interface: any function carrying the heat-slab maximum-principle
interface is nonpositive on the slab. -/
theorem heat_slab_nonpos_of_interface {u : ℝ → ℝ → ℝ} {a b T : ℝ}
    (h : HeatSlabMaximumPrincipleInterface u a b T) :
    ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0 :=
  h.bound_nonpos

/-- The zero solution inhabits the heat-equation interface, so the interface is not
vacuous. -/
theorem heat_slab_zero_interface (a b T : ℝ) :
    HeatSlabMaximumPrincipleInterface (fun _ _ => (0 : ℝ)) a b T where
  heat_equation := by
    intro x t _ _
    simp
  continuousOn_slab := continuous_const.continuousOn
  initial_nonpos := by
    intro x _
    norm_num
  lateral_nonpos := by
    intro t _
    exact ⟨le_rfl, le_rfl⟩
  bound_nonpos := by
    intro x _ t _
    norm_num

/-- A nontrivial inhabited instance: an affine steady state `u x t = c * x + d` satisfies
the heat equation, and if its initial and lateral data are nonpositive then it is
nonpositive on the whole slab.  This is a checked (finite-dimensional) instance of the
interface, not an appeal to it. -/
theorem heat_slab_affine_interface {c d a b T : ℝ}
    (hinit : ∀ x ∈ Icc a b, c * x + d ≤ 0)
    (hleft : c * a + d ≤ 0) (hright : c * b + d ≤ 0) :
    HeatSlabMaximumPrincipleInterface (fun x _ => c * x + d) a b T where
  heat_equation := by
    intro x t _ _
    have h0 : deriv (fun s : ℝ => c * x + d) t = 0 :=
      deriv_const t (c * x + d)
    have h2 : iteratedDeriv 2 (fun y : ℝ => c * y + d) x = 0 := by
      have hlin : ∀ y : ℝ, HasDerivAt (fun z : ℝ => c * z + d) c y := by
        intro y
        simpa using (hasDerivAt_id y).const_mul c |>.add_const d
      have hderiv : deriv (fun y : ℝ => c * y + d) = fun _ => c := by
        funext y
        exact (hlin y).deriv
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_zero, hderiv]
      simp
    rw [h0, h2]
  continuousOn_slab := by
    have hcont : Continuous (fun p : ℝ × ℝ => c * p.1 + d) :=
      (continuous_const.mul continuous_fst).add continuous_const
    simpa using hcont.continuousOn
  initial_nonpos := hinit
  lateral_nonpos := by
    intro t _
    exact ⟨hleft, hright⟩
  bound_nonpos := by
    intro x hx t _
    have hx' : a ≤ x ∧ x ≤ b := mem_Icc.mp hx
    have hle : c * x + d ≤ max (c * a + d) (c * b + d) := by
      have hmono : c * x + d ≤ max (c * a + d) (c * b + d) := by
        rcases le_total c 0 with hc | hc
        · have h1 : c * x ≤ c * a := mul_le_mul_of_nonpos_left hx'.1 hc
          have h2 : c * x + d ≤ c * a + d := by linarith
          exact h2.trans (le_max_left _ _)
        · have h1 : c * x ≤ c * b := mul_le_mul_of_nonneg_left hx'.2 hc
          have h2 : c * x + d ≤ c * b + d := by linarith
          exact h2.trans (le_max_right _ _)
      exact hmono
    exact hle.trans (max_le hleft hright)

end Probe.PdeApi

/-! ## 8. Axiom audit

The toy lemmas depend only on the standard Lean/mathlib axioms (or none). -/

#print axioms Probe.PdeApi.continuousOn_Icc_exists_max
#print axioms Probe.PdeApi.deriv_sq
#print axioms Probe.PdeApi.iteratedDeriv_two_cube
#print axioms Probe.PdeApi.discreteLaplacian_affine
#print axioms Probe.PdeApi.strict_finite_grid_max_principle
#print axioms Probe.PdeApi.strict_finite_grid_max_principle_max
#print axioms Probe.PdeApi.heat_slab_nonpos_of_interface
#print axioms Probe.PdeApi.heat_slab_zero_interface
#print axioms Probe.PdeApi.heat_slab_affine_interface
