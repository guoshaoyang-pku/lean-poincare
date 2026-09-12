/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (manifold IBP layer)

# Smooth bump functions and smooth partitions of unity on `Vec d`

This file provides, for the Euclidean model space `Vec d = Fin d → ℝ`:

* `exists_contDiff_bump`: a smooth bump function which equals `1` on a compact set `K`
  and whose topological support is contained in any prescribed open neighbourhood of `K`;
* `exists_smooth_partitionOfUnity_subordinate`: a smooth partition of unity subordinate
  to a finite open cover of a compact set.

Both statements are proved from the `C^∞` bump functions of an inner product space
(`ContDiffBump`).  They are the elementary Euclidean inputs for gluing local (chart) data
in the manifold IBP layer; note that the blocker `B-D13-SMOOTH-POU` concerns the genuinely
manifold-level statement, whereas the Euclidean statements below are unconditional.

## Note on the differentiability parameter

In the pinned mathlib, the order parameter of `ContDiff` lives in `ℕ∞ω = WithTop ℕ∞`:
`∞` (i.e. `(⊤ : ℕ∞)` coerced) means *smooth* (`C^∞`) while `⊤` (i.e. `ω`) means
*analytic*.  The two are genuinely different: `ContDiff ℝ ω f ↔ AnalyticOnNhd ℝ f univ`
(`contDiff_omega_iff_analyticOnNhd`), and by the identity principle an analytic function
which equals `1` on a nonempty open set equals `1` on the whole connected space `Vec d`,
so no analytic bump function supported in a proper open set can exist.  Accordingly the
classical "smooth bump function" statements below are stated with `∞`.
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Poincare.D12.VolumeIBP.Basic

noncomputable section

open scoped BigOperators Topology ContDiff
open Set Metric Function
open Poincare.D12.VolumeIBP

namespace Poincare.D13.ManifoldIBP

/-- **Smooth bump function on `Vec d`.**  For a compact set `K` contained in an open set
`U` there is a smooth function `χ : Vec d → ℝ` with values in `[0,1]`, equal to `1` on
`K` and with `tsupport χ ⊆ U`. -/
theorem exists_contDiff_bump {d : ℕ} {K U : Set (Vec d)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : Vec d → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ K, χ x = 1) ∧ tsupport χ ⊆ U := by
  classical
  -- Every point of `K` has a closed ball around it contained in `U`.
  have hball : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall (x : Vec d) r ⊆ U := by
    intro x
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU x.2))
    exact ⟨ε / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose r hrpos hrclosed using hball
  -- A finite subcover of `K` by the half-balls.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Vec d) (r x / 2))
    (fun _ => isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (by linarith [hrpos ⟨y, hy⟩])⟩)
  -- The bump functions attached to the centres.
  let φ : (x : K) → ContDiffBump (x : Vec d) :=
    fun x => ⟨r x / 2, r x, by linarith [hrpos x], by linarith [hrpos x]⟩
  refine ⟨fun y => 1 - ∏ x ∈ t, (1 - φ x y), ?_, ?_, ?_, ?_⟩
  · -- smoothness
    exact contDiff_const.sub (contDiff_prod fun x _ => contDiff_const.sub (φ x).contDiff)
  · -- bounds `0 ≤ χ ≤ 1`
    intro y
    have hprod : ∏ x ∈ t, (1 - φ x y) ∈ Set.Icc (0 : ℝ) 1 :=
      Finset.prod_induction (s := t) (f := fun x => 1 - φ x y)
        (p := fun z => z ∈ Set.Icc (0 : ℝ) 1)
        (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1,
          (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by rw [one_mul]; exact hb.2)⟩)
        (by norm_num)
        (fun x _ => ⟨by linarith [(φ x).le_one (x := y)], by linarith [(φ x).nonneg (x := y)]⟩)
    exact ⟨by linarith [hprod.2], by linarith [hprod.1]⟩
  · -- `χ = 1` on `K`
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
    have h1 : φ x y = 1 := (φ x).one_of_mem_closedBall (by
      rw [mem_closedBall]
      exact le_of_lt hyx)
    have h0 : (1 : ℝ) - φ x y = 0 := by rw [h1]; ring
    show 1 - ∏ x ∈ t, (1 - φ x y) = 1
    rw [Finset.prod_eq_zero hxt h0]
    ring
  · -- the topological support is contained in `U`
    have hclosed : IsClosed (⋃ x ∈ t, tsupport (φ x : Vec d → ℝ)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    have hsupp : support (fun y => 1 - ∏ x ∈ t, (1 - φ x y)) ⊆
        ⋃ x ∈ t, tsupport (φ x : Vec d → ℝ) := by
      intro y hy
      by_contra hcon
      rw [mem_iUnion₂] at hcon
      simp only [not_exists] at hcon
      have hzero : ∀ x ∈ t, φ x y = 0 := by
        intro x hx
        by_contra hne
        exact hcon x hx (subset_tsupport (φ x) (Function.mem_support.mpr hne))
      apply hy
      show 1 - ∏ x ∈ t, (1 - φ x y) = 0
      rw [Finset.prod_eq_one fun x hx => by rw [hzero x hx]; ring]
      ring
    have hSU : (⋃ x ∈ t, tsupport (φ x : Vec d → ℝ)) ⊆ U := by
      intro y hy
      obtain ⟨x, _, hyx⟩ := mem_iUnion₂.mp hy
      exact hrclosed x (by rwa [ContDiffBump.tsupport_eq] at hyx)
    exact (closure_mono hsupp).trans ((le_of_eq hclosed.closure_eq).trans hSU)

/-- **Smooth partition of unity subordinate to a finite open cover of a compact set.**
For a finite open cover `U` of a compact set `K` in `Vec d` there is a family of smooth
nonnegative functions `ψ i`, with `tsupport (ψ i) ⊆ U i`, whose sum equals `1` on `K`. -/
theorem exists_smooth_partitionOfUnity_subordinate {d : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → Set (Vec d)) (hUo : ∀ i, IsOpen (U i))
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ ⋃ i, U i) :
    ∃ ψ : ι → Vec d → ℝ,
      (∀ i, ContDiff ℝ ∞ (ψ i)) ∧ (∀ i x, 0 ≤ ψ i x) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ (∀ x ∈ K, ∑ i, ψ i x = 1) := by
  classical
  -- For every point of `K`, a bump function whose topological support lies in one `U i`.
  have hdata : ∀ x : K, ∃ (i : ι) (r : ℝ), 0 < r ∧ closedBall (x : Vec d) r ⊆ U i := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, (x : Vec d) ∈ U i := by simpa using hKU x.2
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp ((hUo i).mem_nhds hi)
    exact ⟨i, ε / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose ix r hrpos hrclosed using hdata
  -- A finite subcover of `K` by the half-balls.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Vec d) (r x / 2))
    (fun _ => isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (by linarith [hrpos ⟨y, hy⟩])⟩)
  let φ : (x : K) → ContDiffBump (x : Vec d) :=
    fun x => ⟨r x / 2, r x, by linarith [hrpos x], by linarith [hrpos x]⟩
  -- The `i`-th preliminary sum and the total sum.
  let Φ : ι → Vec d → ℝ := fun i y => ∑ x ∈ t.filter (fun x => ix x = i), φ x y
  let ρ : Vec d → ℝ := fun y => ∑ i, Φ i y
  have hΦ_smooth : ∀ i, ContDiff ℝ ∞ (Φ i) :=
    fun i => ContDiff.sum fun x _ => (φ x).contDiff
  have hΦ_nonneg : ∀ i y, 0 ≤ Φ i y :=
    fun i y => Finset.sum_nonneg fun x _ => (φ x).nonneg
  have hΦ_tsupp : ∀ i, tsupport (Φ i) ⊆ U i := by
    intro i
    have hclosed : IsClosed (⋃ x ∈ t.filter (fun x => ix x = i), tsupport (φ x : Vec d → ℝ)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    have hsupp : support (Φ i) ⊆
        ⋃ x ∈ t.filter (fun x => ix x = i), tsupport (φ x : Vec d → ℝ) := by
      intro y hy
      by_contra hcon
      rw [mem_iUnion₂] at hcon
      simp only [not_exists] at hcon
      have hzero : ∀ x ∈ t.filter (fun x => ix x = i), φ x y = 0 := by
        intro x hx
        by_contra hne
        exact hcon x hx (subset_tsupport (φ x) (Function.mem_support.mpr hne))
      exact hy (Finset.sum_eq_zero hzero)
    calc tsupport (Φ i) = closure (support (Φ i)) := rfl
      _ ⊆ closure (⋃ x ∈ t.filter (fun x => ix x = i), tsupport (φ x : Vec d → ℝ)) :=
          closure_mono hsupp
      _ = ⋃ x ∈ t.filter (fun x => ix x = i), tsupport (φ x : Vec d → ℝ) := hclosed.closure_eq
      _ ⊆ U i := by
          intro y hy
          obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
          have hix : ix x = i := (Finset.mem_filter.mp hx).2
          have hmem : y ∈ closedBall (x : Vec d) (r x) := by
            rwa [ContDiffBump.tsupport_eq] at hyx
          simpa [hix] using hrclosed x hmem
  have hρ_smooth : ContDiff ℝ ∞ ρ := ContDiff.sum fun i _ => hΦ_smooth i
  have hρ_nonneg : ∀ y, 0 ≤ ρ y := fun y => Finset.sum_nonneg fun i _ => hΦ_nonneg i y
  have hρ_ge_one : ∀ y ∈ K, 1 ≤ ρ y := by
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
    have hφ1 : φ x y = 1 := (φ x).one_of_mem_closedBall (by
      rw [mem_closedBall]
      exact le_of_lt hyx)
    have hmem : x ∈ t.filter (fun z => ix z = ix x) := by
      rw [Finset.mem_filter]
      exact ⟨hxt, rfl⟩
    have h1 : φ x y ≤ Φ (ix x) y := by
      have hle := Finset.single_le_sum (s := t.filter (fun z => ix z = ix x))
        (f := fun z => φ z y) (fun z _ => (φ z).nonneg) hmem
      rw [hφ1] at hle ⊢
      simpa only [Φ] using hle
    have h2 : Φ (ix x) y ≤ ρ y :=
      Finset.single_le_sum (s := Finset.univ) (f := fun i => Φ i y)
        (fun i _ => hΦ_nonneg i y) (Finset.mem_univ _)
    linarith
  -- A bump function which is `1` on `K` and supported where `ρ` is positive.
  have hopen : IsOpen {y : Vec d | 0 < ρ y} := isOpen_lt continuous_const hρ_smooth.continuous
  have hKsub : K ⊆ {y : Vec d | 0 < ρ y} :=
    fun y hy => lt_of_lt_of_le zero_lt_one (hρ_ge_one y hy)
  obtain ⟨χ, hχ_smooth, hχ_range, hχ_one, hχ_tsupp⟩ := exists_contDiff_bump hK hopen hKsub
  let ψ : ι → Vec d → ℝ := fun i y => χ y * Φ i y / ρ y
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · -- smoothness of the renormalised pieces
    intro i
    have hA : IsOpen {y : Vec d | ρ y ≠ 0} := isOpen_ne_fun hρ_smooth.continuous continuous_const
    have hB : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    have hAB : {y : Vec d | ρ y ≠ 0} ∪ (tsupport χ)ᶜ = univ := by
      rw [eq_univ_iff_forall]
      intro y
      by_cases h : ρ y = 0
      · exact Or.inr fun hy => absurd h (ne_of_gt (hχ_tsupp hy))
      · exact Or.inl h
    refine contDiff_of_contDiffOn_union_of_isOpen ?_ ?_ hAB hA hB
    · -- on `{y | ρ y ≠ 0}` it is the quotient of smooth functions
      exact (hχ_smooth.contDiffOn.mul (hΦ_smooth i).contDiffOn).div hρ_smooth.contDiffOn
        (fun y hy => hy)
    · -- on the complement of `tsupport χ` it vanishes
      refine ContDiffOn.congr (f := fun _ : Vec d => (0 : ℝ)) contDiffOn_const fun y hy => ?_
      have hχ0 : χ y = 0 := by
        by_contra hne
        exact hy (subset_tsupport χ (Function.mem_support.mpr hne))
      simp only [ψ, hχ0, zero_mul, zero_div]
  · -- nonnegativity
    intro i y
    exact div_nonneg (mul_nonneg (hχ_range y).1 (hΦ_nonneg i y)) (hρ_nonneg y)
  · -- supports are subordinate to the cover
    intro i
    have hsupp : support (ψ i) ⊆ tsupport (Φ i) := by
      intro y hy
      have hψ : ψ i y ≠ 0 := hy
      have hnum : χ y * Φ i y ≠ 0 := by
        intro h
        exact hψ (by simp only [ψ, h, zero_div])
      exact subset_tsupport (Φ i) (Function.mem_support.mpr (mul_ne_zero_iff.mp hnum).2)
    calc tsupport (ψ i) = closure (support (ψ i)) := rfl
      _ ⊆ closure (tsupport (Φ i)) := closure_mono hsupp
      _ = tsupport (Φ i) := (isClosed_tsupport (Φ i)).closure_eq
      _ ⊆ U i := hΦ_tsupp i
  · -- the sum equals one on `K`
    intro y hy
    have hρ1 : 1 ≤ ρ y := hρ_ge_one y hy
    have hρ0 : ρ y ≠ 0 := by linarith
    have hχ1 : χ y = 1 := hχ_one y hy
    have hsum : ∑ i, ψ i y = (χ y * ρ y) / ρ y := by
      calc ∑ i, ψ i y = ∑ i, χ y * Φ i y / ρ y := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [ψ]
        _ = (∑ i, χ y * Φ i y) / ρ y := by rw [Finset.sum_div]
        _ = (χ y * ρ y) / ρ y := by
            show (∑ i, χ y * Φ i y) / (∑ i, Φ i y) =
              (χ y * (∑ i, Φ i y)) / (∑ i, Φ i y)
            rw [Finset.mul_sum]
    rw [hsum, hχ1, one_mul]
    exact div_self hρ0

#print axioms exists_contDiff_bump
#print axioms exists_smooth_partitionOfUnity_subordinate

end Poincare.D13.ManifoldIBP
