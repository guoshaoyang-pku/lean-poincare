/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — the two-sided Sturm count: equality is forced by an early zero

`Poincare.L4.GeodesicComparison.SturmZeroCount` proves the *existence* half of the scalar
Sturm comparison for Jacobi equations: if `k ≥ K` on `[a,b]`, `u` solves `u'' + k u = 0` with
`u a = 0`, `k > K` somewhere in `(a,b)` and `b = a + π/√K` is the model's first zero, then `u`
vanishes somewhere in `(a,b)`.  In the complementary regime `k ≤ K` the *equality* case of the
Sturm alternative is the only possibility, and it becomes a genuine theorem once a zero is
assumed to exist:

* `eq_curvature_of_first_jacobi_zero_of_curvature_le` — **the main theorem.**  If `k ≤ K` on
  `[a,c]`, `u` is a Jacobi solution on `[a,b]` with `a < c < b`, `u a = u c = 0`, `c` is the
  *first* zero of `u` after `a` (`u` has no zero in `(a,c)`), and `√K (c - a) ≤ π`, then
  `k = K` identically on `(a,c)`: a zero at or before the model's first zero can only happen in
  the equality case.  This is the exact complement of round 3's
  `eq_curvature_of_no_jacobi_zero_before_pi_sqrt` (no zero ⟹ equality on the whole span), and it
  completes the two-sided picture: in either case the curvature is pinned to `K` up to the
  first zero.
* `first_jacobi_zero_le_of_curvature_deficit` — a strict deficit `k t₀ < K` inside `(a,c)` is
  *incompatible* with `c` being the first zero: the formal conclusion `c ≤ t₀` contradicts the
  hypothesis `t₀ ∈ (a,c)`.  Equivalently: the first zero cannot lie after the deficit point, so
  under a deficit the equality conclusion of the main theorem is forced up to `t₀`.  This is the
  two-sided companion of the strict-excess theorem of round 3 (there, `k > K` somewhere inside
  `(a,b)` *forces* a zero strictly before the model zero).
* `const_curvature_deficit_no_first_zero` — for constant curvature `k ≡ cst < K`, no Jacobi
  solution with `u a = 0` has a first zero `c` with `√K (c - a) ≤ π`.  This is the scalar-model
  case of an *upper* curvature bound `k ≤ K`: the first conjugate point is pushed strictly beyond
  `π/√K` (the classical comparison with the model of curvature `K` from above).
* Witnesses: `sturmModel_first_zero_witness` exhibits the equality case (`k ≡ K = 1`, `u = sin`,
  first zero at `π`); `sin_no_first_zero_before_pi_div_sqrt_two` exhibits the exclusion
  (`k ≡ 1 < K = 2`, the first zero of `sin` is not before `π/√2`), so the hypothesis set is
  jointly satisfiable and the conclusion is not vacuous.

Everything is scalar ODE data on a real interval.  No manifold, geodesic, exponential map or
curvature-tensor statement is constructed or claimed; in particular the *existence* of a first
zero is a hypothesis, not a conclusion (it needs `u' a ≠ 0` and an ODE-uniqueness argument that
is not formalized here).
-/
import Poincare.L4.GeodesicComparison.SturmZeroCount

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics

/-! ## 1. Two elementary interval lemmas -/

/-- **Monotonicity of `JacobiSolutionOn` in the right endpoint, for an arbitrary left
endpoint.**  (The round-2 lemma `JacobiSolutionOn.mono` is stated only for `a = 0`; the
complementary Sturm count below needs the general form.) -/
theorem jacobiSolutionOn_mono_Icc {k u du ddu : ℝ → ℝ} {a b b' : ℝ}
    (h : JacobiSolutionOn k u du ddu a b) (_hab' : a ≤ b') (hb'b : b' ≤ b) :
    JacobiSolutionOn k u du ddu a b' where
  hasDerivAt_u := fun _ ht => h.hasDerivAt_u ⟨ht.1, lt_of_lt_of_le ht.2 hb'b⟩
  hasDerivAt_du := fun _ ht => h.hasDerivAt_du ⟨ht.1, lt_of_lt_of_le ht.2 hb'b⟩
  eq_secondDeriv := fun _ ht => h.eq_secondDeriv ⟨ht.1, lt_of_lt_of_le ht.2 hb'b⟩
  continuousOn_u := h.continuousOn_u.mono (Icc_subset_Icc_right hb'b)
  continuousOn_du := h.continuousOn_du.mono (Icc_subset_Icc_right hb'b)

/-- **Positivity of the shifted model up to the model's first zero.**  If `√K (c - a) ≤ π`
then `sin (√K (t - a)) > 0` for every `t ∈ (a, c)`.  This is the form needed when the right
endpoint `c` is *below* the model's first zero `a + π/√K`; round 3's `sturmModel_pos` assumes
the equality `√K (b - a) = π`. -/
theorem sturmModel_pos_of_le {K a c t : ℝ} (hK : 0 < K)
    (hspan : Real.sqrt K * (c - a) ≤ Real.pi) (ht : t ∈ Ioo a c) :
    0 < sturmModel K a t := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have h1 : 0 < Real.sqrt K * (t - a) := mul_pos hsqrt (by linarith [ht.1])
  have h2 : Real.sqrt K * (t - a) < Real.pi :=
    calc Real.sqrt K * (t - a) < Real.sqrt K * (c - a) :=
          mul_lt_mul_of_pos_left (by linarith [ht.2]) hsqrt
      _ ≤ Real.pi := hspan
  simpa [sturmModel] using Real.sin_pos_of_pos_of_lt_pi h1 h2

/-! ## 2. The equality-forcing theorem -/

/-- **An early first zero forces equality of the curvatures.**  Let `K > 0`, let `u` solve
`u'' + k u = 0` on `(a,b)`, suppose `u a = 0` and that `c ∈ (a,b)` is the *first* zero of `u`
after `a` (`u` has no zero in `(a,c)`).  If `k ≤ K` on `[a,c]` and `√K (c - a) ≤ π` (so `c` is
at or before the model's first zero), then `k = K` identically on `(a,c)`.

Proof: apply the D12 Sturm engine on `[a,c]` with the constructed shifted model
`sturmModel K a` as `u₁` and the sign-normalised `u` as `u₂` (the sign is constant on `(a,c)`
because `u` has no zero there).  The engine's first alternative — the model has a zero in
`(a,c)` — is refuted by `sturmModel_pos_of_le`, leaving the equality alternative.

This is the exact complement of `eq_curvature_of_no_jacobi_zero_before_pi_sqrt`: with a zero
present, equality holds up to that zero; with no zero present, equality holds on the whole
span. -/
theorem eq_curvature_of_first_jacobi_zero_of_curvature_le
    {k : ℝ → ℝ} {K a b c : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) ≤ Real.pi)
    (hk : ∀ t ∈ Icc a c, k t ≤ K)
    (h : JacobiSolutionOn k u du ddu a b) (hca : c ∈ Ioo a b)
    (hua : u a = 0) (huc : u c = 0)
    (hfirst : ∀ t ∈ Ioo a c, u t ≠ 0) :
    ∀ t ∈ Ioo a c, k t = K := by
  have hac : a < c := hca.1
  have hcont : ContinuousOn u (Ioo a c) :=
    h.continuousOn_u.mono fun t ht => ⟨ht.1.le, (ht.2.trans hca.2).le⟩
  have hsign := sign_constant_of_no_zero hcont hfirst
  have hderivc : HasDerivAtR u (du c) c := h.hasDerivAt_u hca
  have hmodel : JacobiSolutionOn (fun _ : ℝ => K) (sturmModel K a) (sturmModelDeriv K a)
      (sturmModelSecondDeriv K a) a c :=
    sturmModel_jacobiSolutionOn (K := K) (a := a) (b := c) hK.le
  have hmodelpos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a c → 0 < sturmModel K a t :=
    fun _ ht => sturmModel_pos_of_le hK hspan ht
  have hmodela : sturmModel K a a = 0 := by simp [sturmModel]
  have hmono : JacobiSolutionOn k u du ddu a c := jacobiSolutionOn_mono_Icc h hac.le hca.2.le
  rcases hsign with hpos | hneg
  · have hcmp := sturm_zero_comparison (k₁ := fun _ : ℝ => K) (k₂ := k)
      (u₁ := sturmModel K a) (du₁ := sturmModelDeriv K a)
      (ddu₁ := sturmModelSecondDeriv K a) (u₂ := u) (du₂ := du) (ddu₂ := ddu)
      hac (fun t ht => hk t ht) hmodel hmono
      hmodela hua huc (fun _ ht => hpos ht) hderivc
    rcases hcmp with ⟨z, hz, hzm⟩ | heq
    · exact absurd hzm (ne_of_gt (hmodelpos hz))
    · intro t ht
      exact (heq ht).symm
  · have hnegpos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a c → 0 < -u t := fun _ ht => neg_pos.mpr (hneg ht)
    have hcmp := sturm_zero_comparison (k₁ := fun _ : ℝ => K) (k₂ := k)
      (u₁ := sturmModel K a) (du₁ := sturmModelDeriv K a)
      (ddu₁ := sturmModelSecondDeriv K a) (u₂ := -u) (du₂ := -du) (ddu₂ := -ddu)
      hac (fun t ht => hk t ht) hmodel (hmono.neg)
      hmodela (by simp [hua]) (by simp [huc]) (fun _ ht => hnegpos ht) hderivc.neg
    rcases hcmp with ⟨z, hz, hzm⟩ | heq
    · exact absurd hzm (ne_of_gt (hmodelpos hz))
    · intro t ht
      exact (heq ht).symm

/-- **Anchored form at `0`.**  Companion of `eq_curvature_of_first_jacobi_zero_of_curvature_le`
for the geometric anchoring `a = 0`, in the same shape as round 3's
`eq_curvature_of_no_jacobi_zero_before_pi_sqrt`. -/
theorem eq_curvature_of_first_jacobi_zero_before_pi_sqrt
    {k : ℝ → ℝ} {K b c : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * c ≤ Real.pi)
    (hk : ∀ t ∈ Icc 0 c, k t ≤ K)
    (h : JacobiSolutionOn k u du ddu 0 b) (hc : c ∈ Ioo 0 b)
    (hu0 : u 0 = 0) (huc : u c = 0)
    (hfirst : ∀ t ∈ Ioo 0 c, u t ≠ 0) :
    ∀ t ∈ Ioo 0 c, k t = K := by
  have hmain := eq_curvature_of_first_jacobi_zero_of_curvature_le (K := K) (a := 0)
    (b := b) (c := c) hK (by simpa using hspan) hk h hc hu0 huc hfirst
  simpa using hmain

/-! ## 3. Corollaries: the two-sided first-zero location -/

/-- **A strict curvature deficit rules out a first zero after the deficit point.**  Under the
hypotheses of the equality-forcing theorem, if `k t₀ < K` at some `t₀ ∈ (a,c)`, then necessarily
`c ≤ t₀` — which contradicts `t₀ ∈ (a,c)`.  So no configuration with a deficit strictly inside
`(a,c)` and a first zero at `c` exists; equivalently, the first zero cannot occur after `t₀`.
This is the two-sided companion of round 3's strict-excess theorem (`k > K` somewhere inside
`(a,b)` *forces* a zero strictly before the model zero). -/
theorem first_jacobi_zero_le_of_curvature_deficit
    {k : ℝ → ℝ} {K a b c t₀ : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hspan : Real.sqrt K * (c - a) ≤ Real.pi)
    (hk : ∀ t ∈ Icc a c, k t ≤ K)
    (h : JacobiSolutionOn k u du ddu a b) (hca : c ∈ Ioo a b)
    (hua : u a = 0) (huc : u c = 0)
    (hfirst : ∀ t ∈ Ioo a c, u t ≠ 0)
    (ht₀ : t₀ ∈ Ioo a c) (hdef : k t₀ < K) :
    c ≤ t₀ := by
  by_contra hnot
  have ht₀c : t₀ < c := lt_of_not_ge hnot
  have heq := eq_curvature_of_first_jacobi_zero_of_curvature_le hK hspan hk h hca hua huc hfirst
  exact absurd (heq t₀ ⟨ht₀.1, ht₀c⟩) (ne_of_lt hdef)

/-- **A strict constant deficit prevents a first zero before `π/√K`.**  If `k ≡ cst < K` on
`[a,b]`, `u` is a Jacobi solution on `[a,b]` with `u a = 0`, then there is no `c ∈ (a,b)` with
`√K (c - a) ≤ π` at which `u` has its first zero after `a`.  In the scalar model this is the
classical statement that a curvature strictly below `K` pushes the first conjugate point
strictly beyond `π/√K`. -/
theorem const_curvature_deficit_no_first_zero
    {k : ℝ → ℝ} {K cst a b : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hkconst : ∀ t ∈ Icc a b, k t = cst) (hcst : cst < K)
    (h : JacobiSolutionOn k u du ddu a b) (hua : u a = 0) :
    ¬ ∃ c ∈ Ioo a b, Real.sqrt K * (c - a) ≤ Real.pi ∧ u c = 0 ∧
        ∀ t ∈ Ioo a c, u t ≠ 0 := by
  rintro ⟨c, hc, hspan, huc, hfirst⟩
  have hk : ∀ t ∈ Icc a c, k t ≤ K := by
    intro t ht
    rw [hkconst t ⟨ht.1, ht.2.trans hc.2.le⟩]
    exact hcst.le
  have heq := eq_curvature_of_first_jacobi_zero_of_curvature_le hK hspan hk h hc hua huc hfirst
  obtain ⟨t, ht⟩ := exists_between hc.1
  have hkt : k t = K := heq t ht
  rw [hkconst t ⟨ht.1.le, ht.2.le.trans hc.2.le⟩] at hkt
  exact absurd hkt (ne_of_lt hcst)

/-! ## 4. Non-vacuity witnesses -/

/-- **The equality case is realized.**  Explicit data satisfying every hypothesis of
`eq_curvature_of_first_jacobi_zero_before_pi_sqrt`: `K = 1`, `k ≡ K`, `u = sin` on `(0, 2π)`,
`c = π` (the first zero of `u` after `0`, with `√K · π ≤ π`).  The final conjunct of the
statement — `k = K` on `(0,π)` — is *derived* by applying the equality-forcing theorem to this
data, so the witness is not a restatement of its own hypothesis. -/
theorem sturmModel_first_zero_witness :
    ∃ (k : ℝ → ℝ) (u du ddu : ℝ → ℝ) (K : ℝ),
      0 < K ∧ (∀ t ∈ Icc (0 : ℝ) Real.pi, k t ≤ K) ∧
        JacobiSolutionOn k u du ddu 0 (2 * Real.pi) ∧ u 0 = 0 ∧ u Real.pi = 0 ∧
        Real.sqrt K * (Real.pi - 0) ≤ Real.pi ∧
        (∀ t ∈ Ioo (0 : ℝ) Real.pi, u t ≠ 0) ∧
        ∀ t ∈ Ioo (0 : ℝ) Real.pi, k t = K := by
  have hK : (0 : ℝ) < 1 := by norm_num
  have hmodel : JacobiSolutionOn (fun _ : ℝ => (1 : ℝ)) (sturmModel 1 0)
      (sturmModelDeriv 1 0) (sturmModelSecondDeriv 1 0) 0 (2 * Real.pi) :=
    sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := 2 * Real.pi) (by norm_num)
  have hc : Real.pi ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
  have huc : sturmModel 1 0 Real.pi = 0 := by
    simp only [sturmModel, Real.sqrt_one, one_mul, sub_zero]
    exact Real.sin_pi
  have hfirst : ∀ t ∈ Ioo (0 : ℝ) Real.pi, sturmModel 1 0 t ≠ 0 := by
    intro t ht h
    have hsin : Real.sin t = 0 := by simpa [sturmModel] using h
    exact sin_no_zero_in_Ioo_zero_pi ⟨t, ht, hsin⟩
  refine ⟨fun _ : ℝ => 1, sturmModel 1 0, sturmModelDeriv 1 0, sturmModelSecondDeriv 1 0, 1,
    hK, fun _ _ => le_rfl, hmodel, by simp [sturmModel], huc, ?_, hfirst,
    eq_curvature_of_first_jacobi_zero_before_pi_sqrt (K := 1) (b := 2 * Real.pi)
      hK (by rw [Real.sqrt_one, one_mul]) (fun _ _ => le_rfl) hmodel hc
      (by simp [sturmModel]) huc hfirst⟩
  rw [Real.sqrt_one, sub_zero, one_mul]

/-- **The exclusion is non-vacuous.**  For `k ≡ 1 < K = 2`, no Jacobi solution with `u 0 = 0`
has its first zero at or before `π/√2`: the first zero of `sin` is at `π > π/√2`.  This is the
scalar-model instance of "no conjugate point before `π/√K` under the *upper* curvature bound
`k ≤ K`"; it is deduced from `const_curvature_deficit_no_first_zero`, so it fails if that
theorem is false. -/
theorem sin_no_first_zero_before_pi_div_sqrt_two :
    ¬ ∃ c ∈ Ioo (0 : ℝ) 3, Real.sqrt 2 * c ≤ Real.pi ∧ Real.sin c = 0 ∧
        ∀ t ∈ Ioo (0 : ℝ) c, Real.sin t ≠ 0 := by
  have hK : (0 : ℝ) < 2 := by norm_num
  have hmodel : JacobiSolutionOn (fun _ : ℝ => (1 : ℝ)) (sturmModel 1 0)
      (sturmModelDeriv 1 0) (sturmModelSecondDeriv 1 0) 0 3 :=
    sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := 3) (by norm_num)
  have hno := const_curvature_deficit_no_first_zero (K := 2) (cst := 1) (a := 0) (b := 3)
    (k := fun _ : ℝ => 1) (u := sturmModel 1 0) (du := sturmModelDeriv 1 0)
    (ddu := sturmModelSecondDeriv 1 0) hK (fun _ _ => rfl) (by norm_num) hmodel
    (by simp [sturmModel])
  rintro ⟨c, hc, hspan, hsin, hfirst⟩
  exact hno ⟨c, hc, by simpa using hspan, by simpa [sturmModel] using hsin,
    fun t ht => by simpa [sturmModel] using hfirst t ht⟩

end Poincare.L4.GeodesicComparison
