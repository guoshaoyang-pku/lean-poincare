/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

# Scalar forward invariance with the *correct* kernel condition

The D12-tensor-maximum-bochner result card records its mathematical blocker `B1` as the
invariance of the PSD cone under Hamilton's **kernel** tangent condition

    vᵀA v = 0  ⟹  vᵀ P(A) v ≥ 0        (A positive semidefinite)

for `P` locally Lipschitz, together with the first-exit argument.  The D12 module
`Poincare.D12.TensorMaximumBochner.PositivityPreservation` proves the matrix theorem under
the strictly *stronger* condition `vᵀA v ≤ 0 ⟹ vᵀP(A)v ≥ 0`, and
`Poincare.D12.TensorMaximumBochner.TangentCone` proves that for `n = 1` the kernel
condition is exactly `P 0 ≥ 0` and that mere continuity is insufficient
(`x' = -√|x|` leaves `[0,∞)`).

This file closes the **scalar (`n = 1`) case of B1 with the correct kernel condition**:
for `f : ℝ → ℝ` locally Lipschitz near the range of the solution and `f 0 ≥ 0`, every
solution of `x' = f (x)` with `x 0 ≥ 0` stays nonnegative on its interval of existence.

The proof is the classical first/last-exit argument: if `x` becomes negative, take the
**last** zero `s` of `x` before the crossing; on `(s, t₁]` the solution is strictly negative,
so `f (x u) ≥ f 0 - L |x u| = f 0 + L x u ≥ L x u`; hence `u ↦ x u · exp(-L u)` has
nonnegative derivative and is monotone, giving `x t₁ ≥ 0`, a contradiction.

## Classification

`scalar_forward_invariance` is **general**: it is an unconditional theorem about an
arbitrary locally Lipschitz scalar field and an arbitrary `C¹` solution, with every
hypothesis expanded (the Lipschitz constant is an explicit hypothesis; boundedness of the
trajectory is an explicit hypothesis).  It is not a manifold statement and it does not
close `B1` for `n ≥ 2`.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

set_option linter.unusedVariables false

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.D13.CriticalPathReview

/-! ## The last-zero lemma -/

/-- **Last-zero lemma.**  If `g` is continuous on `[0,t₀]`, `g 0 ≥ 0` and `g t₀ < 0`, then
there is a last zero `s` of `g` in `[0,t₀]`: `g s = 0` and `g < 0` on `(s,t₀]`.

This is the order-topology step of the exit argument (dual to
`Poincare.D12.TensorMaximumBochner.exists_first_zero`, which the D12 module uses for the
strengthened condition). -/
lemma exists_last_zero {g : ℝ → ℝ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hg : ContinuousOn g (Icc 0 t₀)) (h0 : 0 ≤ g 0) (ht : g t₀ < 0) :
    ∃ s ∈ Icc 0 t₀, g s = 0 ∧ ∀ u ∈ Ioc s t₀, g u < 0 := by
  classical
  let Z : Set ℝ := {t | t ∈ Icc 0 t₀ ∧ g t = 0}
  have hZne : Z.Nonempty := by
    have hmem : (0 : ℝ) ∈ Icc (g t₀) (g 0) := ⟨le_of_lt ht, h0⟩
    rcases intermediate_value_Icc' ht₀ hg hmem with ⟨u, hu, hgu⟩
    exact ⟨u, hu, hgu⟩
  have hZbd : BddAbove Z := ⟨t₀, fun t ht => ht.1.2⟩
  let s : ℝ := sSup Z
  have hsle : s ≤ t₀ := csSup_le hZne fun t ht => ht.1.2
  have hsge : 0 ≤ s := by
    rcases hZne with ⟨z, hz⟩
    exact le_trans hz.1.1 (le_csSup hZbd hz)
  -- the supremum of the zero set is itself a zero
  have hs0 : g s = 0 := by
    rcases lt_trichotomy (g s) 0 with hlt | heq | hgt
    · -- `g s < 0` is impossible: `g < 0` near `s` kills the zeros accumulating at `s`
      have hcont_s : ContinuousWithinAt g (Icc 0 t₀) s := hg s ⟨hsge, hsle⟩
      have hev : ∀ᶠ u in 𝓝[Icc 0 t₀] s, g u < 0 := hcont_s.eventually (Iio_mem_nhds hlt)
      rcases (Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)) with
        ⟨ε, hε, hεball⟩
      have hε' : 0 < ε / 2 := half_pos hε
      have ha : s - ε / 2 < s := sub_lt_self _ hε'
      rcases exists_lt_of_lt_csSup hZne ha with ⟨z, hzZ, hsz⟩
      have hz_le_s : z ≤ s := le_csSup hZbd hzZ
      have hzIcc : z ∈ Icc 0 t₀ := hzZ.1
      have hzε : |z - s| < ε := by
        rw [abs_of_nonpos (sub_nonpos.mpr hz_le_s)]
        linarith [hsz, hε]
      have hgz : g z < 0 := hεball (by simpa [Real.dist_eq] using hzε) hzIcc
      exact absurd hzZ.2 (ne_of_lt hgz)
    · exact heq
    · -- `g s > 0` is impossible: `g > 0` near `s`, but zeros accumulate at `s` from below
      have hcont_s : ContinuousWithinAt g (Icc 0 t₀) s := hg s ⟨hsge, hsle⟩
      have hev : ∀ᶠ u in 𝓝[Icc 0 t₀] s, 0 < g u := hcont_s.eventually (Ioi_mem_nhds hgt)
      rcases (Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)) with
        ⟨ε, hε, hεball⟩
      have hε' : 0 < ε / 2 := half_pos hε
      have ha : s - ε / 2 < s := sub_lt_self _ hε'
      rcases exists_lt_of_lt_csSup hZne ha with ⟨z, hzZ, hsz⟩
      have hz_le_s : z ≤ s := le_csSup hZbd hzZ
      have hzIcc : z ∈ Icc 0 t₀ := hzZ.1
      have hzε : |z - s| < ε := by
        rw [abs_of_nonpos (sub_nonpos.mpr hz_le_s)]
        linarith [hsz, hε]
      have hgz : 0 < g z := hεball (by simpa [Real.dist_eq] using hzε) hzIcc
      exact absurd hzZ.2 (ne_of_gt hgz)
  refine ⟨s, ⟨hsge, hsle⟩, hs0, ?_⟩
  intro u hu
  rcases lt_trichotomy (g u) 0 with hlt | heq | hgt
  · exact hlt
  · -- `g u = 0` with `u > s` contradicts maximality of `s`
    exact absurd (le_csSup hZbd ⟨⟨le_trans hsge hu.1.le, hu.2⟩, heq⟩) (not_le.mpr hu.1)
  · -- `g u > 0`: IVT on `[u,t₀]` (using `g t₀ < 0`) produces a zero strictly above `s`
    have hmem : (0 : ℝ) ∈ Ioo (g t₀) (g u) := ⟨ht, hgt⟩
    rcases intermediate_value_Ioo' hu.2
      (hg.mono (Icc_subset_Icc (le_trans hsge hu.1.le) le_rfl)) hmem with
      ⟨v, hv, hgv⟩
    exact absurd (le_csSup hZbd ⟨⟨le_trans hsge (le_trans hu.1.le hv.1.le),
      le_trans hv.2.le le_rfl⟩, hgv⟩) (not_le.mpr (lt_trans hu.1 hv.1))

/-! ## Scalar forward invariance -/

/-- **Scalar forward invariance under the kernel condition.**  Let `f : ℝ → ℝ` be Lipschitz
with constant `L ≥ 0` on `[-M,M]`, with `f 0 ≥ 0` (the exact scalar kernel condition), and
let `x` be a solution of `x' = f (x)` on `(0,T)` that is continuous on `[0,T]`, starts at
`x 0 ≥ 0` and stays in `[-M,M]`.  Then `x ≥ 0` on `[0,T]`.

All hypotheses are expanded: `L`, `M` are explicit; no differentiability or growth
condition is hidden; `T ≥ 0`, `M ≥ 0`, `L ≥ 0` are explicit. -/
theorem scalar_forward_invariance {f x : ℝ → ℝ} {T M L : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hlip : ∀ a ∈ Icc (-M) M, ∀ b ∈ Icc (-M) M, |f a - f b| ≤ L * |a - b|)
    (hker : 0 ≤ f 0)
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hcont : ContinuousOn x (Icc 0 T))
    (hx0 : 0 ≤ x 0)
    (hxM : ∀ t ∈ Icc 0 T, |x t| ≤ M) :
    ∀ t ∈ Icc 0 T, 0 ≤ x t := by
  intro t₁ ht₁
  by_contra hneg
  simp only [not_le] at hneg
  -- the crossing point is strictly positive
  have ht₁pos : 0 < t₁ := by
    rcases lt_or_eq_of_le ht₁.1 with h | h
    · exact h
    · exact absurd (h ▸ hx0) (not_le.mpr hneg)
  have ht₁T : t₁ ≤ T := ht₁.2
  -- continuity of `x` on `[0,t₁]`
  have hcont₁ : ContinuousOn x (Icc 0 t₁) :=
    hcont.mono (Icc_subset_Icc le_rfl ht₁T)
  -- last zero `s` of `x` before the crossing
  rcases exists_last_zero ht₁pos.le hcont₁ hx0 hneg with ⟨s, hsIcc, hs0, hsneg⟩
  have hsge : 0 ≤ s := hsIcc.1
  have hsle : s ≤ t₁ := hsIcc.2
  have hslt : s < t₁ := by
    rcases lt_or_eq_of_le hsle with h | h
    · exact h
    · exact absurd (h ▸ hs0) (ne_of_lt hneg)
  -- the exponential weight
  let g : ℝ → ℝ := fun u => x u * Real.exp (-L * u)
  have hgs : g s = 0 := by simp [g, hs0]
  -- Lipschitz bound on the trajectory: `L * x u ≤ f (x u)` for `u ∈ (s,t₁)`
  have hbound : ∀ u ∈ Ioo s t₁, L * x u ≤ f (x u) := by
    intro u hu
    have huIccT : u ∈ Icc 0 T :=
      ⟨le_trans hsge hu.1.le, le_trans hu.2.le ht₁T⟩
    have huxM : |x u| ≤ M := hxM u huIccT
    have hxu_mem : x u ∈ Icc (-M) M := abs_le.mp huxM
    have h0_mem : (0 : ℝ) ∈ Icc (-M) M := ⟨by linarith, hM⟩
    have hlip_u := hlip (x u) hxu_mem 0 h0_mem
    have hxu_neg : x u < 0 := hsneg u ⟨hu.1, hu.2.le⟩
    have habs : |x u - 0| = -x u := by
      rw [sub_zero, abs_of_neg hxu_neg]
    rw [habs] at hlip_u
    have h1 : f 0 - L * (-x u) ≤ f (x u) := by
      have := (abs_le.mp hlip_u).1
      linarith
    nlinarith [hker, h1, hxu_neg]
  -- derivative of the weighted trajectory is nonnegative
  have hderiv_nonneg : ∀ u ∈ Ioo s t₁, 0 ≤ deriv g u := by
    intro u hu
    have huT : u ∈ Ioo 0 T :=
      ⟨lt_of_le_of_lt hsge hu.1, lt_of_lt_of_le hu.2 ht₁T⟩
    have hxder : HasDerivAt x (f (x u)) u := hx u huT
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-L * v))
        (Real.exp (-L * u) * (-L)) u := by
      have h1 : HasDerivAt (fun v : ℝ => -L * v) (-L) u := by
        simpa using (hasDerivAt_const_mul (x := u) (-L))
      simpa using h1.exp
    have hgder : HasDerivAt g
        (f (x u) * Real.exp (-L * u) + x u * (Real.exp (-L * u) * (-L))) u :=
      hxder.mul hexp
    rw [hgder.deriv]
    have hb := hbound u hu
    have hexp_pos : 0 < Real.exp (-L * u) := Real.exp_pos _
    nlinarith [hb, hexp_pos]
  -- continuity and differentiability of `g` on `[s,t₁]`
  have hgcont : ContinuousOn g (Icc s t₁) := by
    have hxcont : ContinuousOn x (Icc s t₁) :=
      hcont.mono (Icc_subset_Icc hsge ht₁T)
    exact hxcont.mul (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul continuousOn_id))
  have hgdiff : DifferentiableOn ℝ g (interior (Icc s t₁)) := by
    rw [interior_Icc]
    intro u hu
    have huT : u ∈ Ioo 0 T :=
      ⟨lt_of_le_of_lt hsge hu.1, lt_of_lt_of_le hu.2 ht₁T⟩
    have hxder : HasDerivAt x (f (x u)) u := hx u huT
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-L * v))
        (Real.exp (-L * u) * (-L)) u := by
      have h1 : HasDerivAt (fun v : ℝ => -L * v) (-L) u := by
        simpa using (hasDerivAt_const_mul (x := u) (-L))
      simpa using h1.exp
    exact (hxder.mul hexp).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn g (Icc s t₁) :=
    monotoneOn_of_deriv_nonneg (convex_Icc s t₁) hgcont hgdiff
      (fun u hu => hderiv_nonneg u (by rwa [interior_Icc] at hu))
  -- monotonicity gives `x t₁ ≥ 0`, contradiction
  have hle := hmono (left_mem_Icc.mpr hslt.le) (right_mem_Icc.mpr hslt.le) hslt.le
  rw [hgs] at hle
  have hexp_pos : 0 < Real.exp (-L * t₁) := Real.exp_pos _
  have : 0 ≤ x t₁ := by
    by_contra hxneg
    simp only [not_le] at hxneg
    nlinarith [hle, hexp_pos, hxneg]
  exact absurd this (not_le.mpr hneg)

/-! ## From mathlib's local Lipschitz notion to the expanded hypothesis -/

/-- **Derived form from `LocallyLipschitzOn`.**  A function locally Lipschitz on the compact
interval `[-M,M]` is Lipschitz there with some constant, so the expanded-hypothesis theorem
applies.  This is the standard regularity hypothesis (no expansion of `LocallyLipschitzOn`
is hidden: it is mathlib's definition, and compactness supplies the constant). -/
theorem scalar_forward_invariance_of_locallyLipschitz {f x : ℝ → ℝ} {T M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hlip : LocallyLipschitzOn (Icc (-M) M) f)
    (hker : 0 ≤ f 0)
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hcont : ContinuousOn x (Icc 0 T))
    (hx0 : 0 ≤ x 0)
    (hxM : ∀ t ∈ Icc 0 T, |x t| ≤ M) :
    ∀ t ∈ Icc 0 T, 0 ≤ x t := by
  rcases hlip.exists_lipschitzOnWith_of_compact isCompact_Icc with ⟨K, hK⟩
  exact scalar_forward_invariance hT hM K.coe_nonneg
    (fun a ha b hb => by
      have h := hK.dist_le_mul a ha b hb
      simpa [Real.dist_eq] using h)
    hker hx hcont hx0 hxM

/-! ## Non-vacuity: a checked nondegenerate instance

The hypotheses of `scalar_forward_invariance` are simultaneously inhabited by a genuinely
non-constant solution: `f x = x` (Lipschitz with constant `1`, `f 0 = 0 ≥ 0`) and
`x t = c · exp t` with `c ≥ 0`, which grows without being constant, stays nonnegative and
is bounded on `[0,T]`. -/

/-- The exponential solution of `x' = x` is a nondegenerate witness for the hypotheses and
the conclusion of `scalar_forward_invariance`. -/
theorem scalar_forward_invariance_witness (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, 0 ≤ c * Real.exp t := by
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun u : ℝ => c * Real.exp u)
        ((fun y : ℝ => y) ((fun u : ℝ => c * Real.exp u) t)) t := by
    intro t _
    simpa using (Real.hasDerivAt_exp t).const_mul c
  have hcont : ContinuousOn (fun u : ℝ => c * Real.exp u) (Icc 0 T) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  have hM : ∀ t ∈ Icc 0 T, |c * Real.exp t| ≤ c * Real.exp T := by
    intro t ht
    rw [abs_of_nonneg (mul_nonneg hc (Real.exp_pos t).le)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht.2) hc
  have hmain := scalar_forward_invariance (f := fun y : ℝ => y)
      (x := fun u : ℝ => c * Real.exp u) (T := T) (M := c * Real.exp T) (L := 1)
      hT (mul_nonneg hc (Real.exp_pos T).le) (by norm_num)
      (fun a _ b _ => by simp) (by norm_num) hderiv hcont (by simpa using hc) hM
  intro t ht
  exact hmain t ht

end Poincare.D13.CriticalPathReview

end
