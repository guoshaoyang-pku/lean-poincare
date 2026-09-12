import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Poincare.D12.TensorMaximumBochner.PositivityPreservation

**Task `D12-tensor-maximum-bochner`, track B (positivity preservation): a matrix ODE
maximum principle with the correct tangent-cone condition and time regularity.**

This module deliberately distinguishes three things that the D11 (D2/D3-era) outputs do not:

1. The D11 `Poincare.Longrun.PDE.DiscreteMaximumPrinciple` is a **scalar, semidiscrete**
   estimate on a finite grid (explicit heat scheme, `0 ≤ α ≤ 1/2`). It is *not* Hamilton's
   tensor maximum principle.
2. The D11 `Entropy.BochnerStatement` is a **statement-only Prop** over abstract operators
   (`WeightedCalculus` has arbitrary `grad`/`laplacian`/`hessSq`/`metric`/`ricci` fields;
   blockers I4/U7). It is *not* a proved Bochner identity.
3. This module proves an elementary but genuine **matrix positivity preservation theorem**
   for a time-dependent symmetric matrix path: if the path is differentiable in time,
   Hermitian-valued, positive semidefinite at time `0`, and satisfies the quadratic-form
   tangent condition (at every time, on every ray where the quadratic form is nonpositive,
   the derivative form is nonnegative), then it stays positive semidefinite for all `t ≥ 0`.

## Honest boundary and the "correct" tangent condition

The classical Hamilton tangent-cone condition for the PSD cone is the **kernel condition**:
`vᵀA v = 0 ⟹ vᵀP(A)v ≥ 0` for `A ≥ 0`; with locally Lipschitz `P` (Nagumo's theorem) it does
imply invariance, but the Nagumo theorem is not in the pinned mathlib and is not smuggled in
here. The condition used below is the elementary **strengthened** version
`vᵀA v ≤ 0 ⟹ vᵀP(A)v ≥ 0` (for all `A`), which is:

* **sufficient** — proved below by reduction to a scalar mean-value lemma, with time
  regularity exactly `DifferentiableAt` in `t`;
* **stronger than the kernel condition** — the kernel condition is the special case
  `vᵀAv = 0`; the file documents and *checks in Lean* the classical counterexample showing
  that the kernel condition alone (with mere continuity) is genuinely insufficient:
  `x(t) = -t²/4` solves `x' = -√|x|` for `t ≥ 0`, starts at `0`, and leaves the cone
  `[0,∞)` — the field `P(y) = -√|y|` is continuous, satisfies the kernel condition at the
  only boundary point, but is not locally Lipschitz there, and violates the strengthened
  condition at `y = -1`.

The matrix theorem is therefore stated and proved with **fully expanded hypotheses**; no
conclusion is assumed. Its hypotheses are inhabited by the explicitly checked nondegenerate
field `P(A) = A² - A` (`M' = M² - M`), for which the strengthened condition is proved from
`|Av|² ≥ 0`, and an explicit solution `M(t) = diag(1/(1+eᵗ), 1/(1+2eᵗ))` starting at
`diag(1/2, 1/3) ≥ 0` is verified to satisfy the ODE and to stay positive semidefinite. This
is a **model** application (matrix ODE), not a claim about Ricci flow on manifolds.

No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators
open Filter
open Set
open scoped Topology
open scoped Matrix

namespace Poincare
namespace D12
namespace TensorMaximumBochner

/-! ## The scalar sign-preservation lemma (mean-value based) -/

/-- **First-crossing lemma.** If `f` is continuous on `[0,t₀]` with `f 0 ≥ 0` and `f t₀ < 0`,
then there is a "first" point `s ∈ [0,t₀]` with `f s = 0` such that `f ≤ 0` on `(s, t₀]`.
This is the elementary order-topology step underlying the scalar maximum principle. -/
lemma exists_first_zero {f : ℝ → ℝ} {t₀ : ℝ} (hf : ContinuousOn f (Icc 0 t₀)) (ht₀ : 0 ≤ t₀)
    (hf₀ : 0 ≤ f 0) (hneg : f t₀ < 0) :
    ∃ s ∈ Icc 0 t₀, f s = 0 ∧ ∀ u ∈ Ioc s t₀, f u ≤ 0 := by
  classical
  let S : Set ℝ := {t | t ∈ Icc 0 t₀ ∧ 0 ≤ f t}
  have hSne : S.Nonempty := by
    refine ⟨(0 : ℝ), ?_⟩
    change (0 : ℝ) ∈ Icc 0 t₀ ∧ 0 ≤ f 0
    exact ⟨mem_Icc.mpr ⟨le_rfl, ht₀⟩, hf₀⟩
  have hSbd : BddAbove S := ⟨t₀, fun x hx => hx.1.2⟩
  let s : ℝ := sSup S
  have hsle : s ≤ t₀ := csSup_le hSne fun x hx => hx.1.2
  have hsnonneg : 0 ≤ s := le_csSup hSbd (by
    change (0 : ℝ) ∈ Icc 0 t₀ ∧ 0 ≤ f 0
    exact ⟨mem_Icc.mpr ⟨le_rfl, ht₀⟩, hf₀⟩)
  -- `f s ≥ 0`: if `f s < 0` then continuity pushes `f < 0` in a neighbourhood of `s`,
  -- leaving no points of `S` near `s`, contradicting `s = sSup S`.
  have hfs₀ : 0 ≤ f s := by
    by_contra hsneg
    have hfslt : f s < 0 := lt_of_not_ge hsneg
    have hcont_s : ContinuousWithinAt f (Icc 0 t₀) s := hf s ⟨hsnonneg, hsle⟩
    have hev : ∀ᶠ x in 𝓝[Icc 0 t₀] s, f x < 0 := hcont_s.eventually (Iio_mem_nhds hfslt)
    rcases (Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)) with
      ⟨ε, hε, hεball⟩
    have hε' : 0 < ε / 2 := half_pos hε
    have ha : s - ε / 2 < s := sub_lt_self _ hε'
    rcases exists_lt_of_lt_csSup hSne ha with ⟨x, hxS, hsx⟩
    have hx_le_s : x ≤ s := le_csSup hSbd hxS
    have hxIcc : x ∈ Icc 0 t₀ := hxS.1
    have hxε : |x - s| < ε := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx_le_s)]
      linarith [hsx, hε]
    have hfx : f x < 0 := hεball (by simpa [Real.dist_eq] using hxε) hxIcc
    exact (not_lt_of_ge hxS.2) hfx
  -- `s < t₀`: `f t₀ < 0` near `t₀` pushes `S` away from `t₀`.
  have hslt : s < t₀ := by
    by_contra hnot
    have hst : t₀ ≤ s := le_of_not_gt hnot
    have hs₀' : s = t₀ := le_antisymm hsle hst
    rw [hs₀'] at hfs₀
    exact not_lt_of_ge hfs₀ hneg
  -- `f s ≤ 0`: if `f s > 0` then `f > 0` near `s` inside `[0,t₀]`, giving points of `S`
  -- strictly above `s`.
  have hfs1 : f s ≤ 0 := by
    by_contra hsneg
    have hsgt : 0 < f s := lt_of_not_ge hsneg
    have hcont_s : ContinuousWithinAt f (Icc 0 t₀) s := hf s ⟨hsnonneg, hsle⟩
    have hev : ∀ᶠ x in 𝓝[Icc 0 t₀] s, 0 < f x := hcont_s.eventually (Ioi_mem_nhds hsgt)
    rcases (Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)) with
      ⟨ε, hε, hεball⟩
    have hεt : 0 < min (t₀ - s) ε := lt_min (sub_pos.mpr hslt) hε
    let u : ℝ := s + min (t₀ - s) ε / 2
    have hsu : s < u := lt_add_of_pos_right _ (half_pos hεt)
    have hut₀ : u < t₀ := by
      have hmin : min (t₀ - s) ε / 2 < t₀ - s :=
        lt_of_lt_of_le (half_lt_self hεt) (min_le_left _ _)
      have : s + min (t₀ - s) ε / 2 < t₀ := by linarith
      simpa [u] using this
    have huIcc : u ∈ Icc 0 t₀ := ⟨le_trans hsnonneg (le_of_lt hsu), le_of_lt hut₀⟩
    have huε : |u - s| < ε := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hsu))]
      have hmin : min (t₀ - s) ε ≤ ε := min_le_right _ _
      have hhalf : min (t₀ - s) ε / 2 < ε := lt_of_lt_of_le (half_lt_self hεt) hmin
      simpa [u] using hhalf
    have hfu : 0 < f u := hεball (by simpa [Real.dist_eq] using huε) huIcc
    have huS : u ∈ S := ⟨huIcc, le_of_lt hfu⟩
    have hu_le_s : u ≤ s := le_csSup hSbd huS
    exact not_lt_of_ge hu_le_s hsu
  -- `f ≤ 0` on `(s, t₀]`: any strictly positive value above `s` gives points of `S` above `s`.
  have hnonpos : ∀ u ∈ Ioc s t₀, f u ≤ 0 := by
    intro u hu
    by_contra hneg
    have hfu : 0 < f u := lt_of_not_ge hneg
    have huIcc : u ∈ Icc 0 t₀ := ⟨le_trans hsnonneg (le_of_lt hu.1), hu.2⟩
    have hcont_u : ContinuousWithinAt f (Icc 0 t₀) u := hf u huIcc
    have hev : ∀ᶠ x in 𝓝[Icc 0 t₀] u, 0 < f x := hcont_u.eventually (Ioi_mem_nhds hfu)
    rcases (Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)) with
      ⟨ε, hε, hεball⟩
    have hε' : 0 < min (u - s) ε := lt_min (sub_pos.mpr hu.1) hε
    let v : ℝ := u - min (u - s) ε / 2
    have hsv : s < v := by
      have hmin : min (u - s) ε / 2 < u - s :=
        lt_of_lt_of_le (half_lt_self hε') (min_le_left _ _)
      dsimp [v]
      linarith
    have hvu : v < u := sub_lt_self _ (half_pos hε')
    have hv0 : 0 ≤ v := le_trans hsnonneg (le_of_lt hsv)
    have hvIcc : v ∈ Icc 0 t₀ := ⟨hv0, le_trans (le_of_lt hvu) hu.2⟩
    have hvε : |v - u| < ε := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hvu))]
      have hmin : min (u - s) ε ≤ ε := min_le_right _ _
      have hhalf : min (u - s) ε / 2 < ε := lt_of_lt_of_le (half_lt_self hε') hmin
      simpa [v] using hhalf
    have hfv : 0 < f v := hεball (by simpa [Real.dist_eq] using hvε) hvIcc
    have hvS : v ∈ S := ⟨hvIcc, le_of_lt hfv⟩
    have hv_le_s : v ≤ s := le_csSup hSbd hvS
    exact not_lt_of_ge hv_le_s hsv
  exact ⟨s, ⟨hsnonneg, hsle⟩, le_antisymm hfs1 hfs₀, hnonpos⟩

/-- **Scalar sign-preservation (semidiscrete scalar maximum principle).** If `f` is
differentiable on `[0, ∞)`, `f 0 ≥ 0`, and `deriv f t ≥ 0` whenever `t ≥ 0` and `f t ≤ 0`,
then `f t ≥ 0` for all `t ≥ 0`. The proof combines the first-crossing lemma with Lagrange's
mean value theorem. -/
theorem nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos {f : ℝ → ℝ}
    (hf₀ : 0 ≤ f 0)
    (hdiff : ∀ t, 0 ≤ t → DifferentiableAt ℝ f t)
    (hderiv : ∀ t, 0 ≤ t → f t ≤ 0 → 0 ≤ deriv f t) :
    ∀ t, 0 ≤ t → 0 ≤ f t := by
  intro t₀ ht₀
  by_contra hneg
  have hfneg : f t₀ < 0 := lt_of_not_ge hneg
  have hcontOn : ContinuousOn f (Icc 0 t₀) := by
    intro x hx
    exact (hdiff x hx.1).continuousAt.continuousWithinAt
  rcases exists_first_zero hcontOn ht₀ hf₀ hfneg with ⟨s, hsIcc, hfs, hnonpos⟩
  have hs₀ : 0 ≤ s := hsIcc.1
  have hst : s < t₀ := by
    by_contra h
    have hle : t₀ ≤ s := le_of_not_gt h
    have hs₀' : s = t₀ := le_antisymm hsIcc.2 hle
    rw [hs₀'] at hfs
    linarith
  have hcontOnst : ContinuousOn f (Icc s t₀) := by
    exact hcontOn.mono (by intro x hx; exact ⟨le_trans hs₀ hx.1, hx.2⟩)
  have hdiffOn : DifferentiableOn ℝ f (Ioo s t₀) := by
    intro x hx
    exact (hdiff x (le_trans hs₀ (le_of_lt hx.1))).differentiableWithinAt
  rcases exists_deriv_eq_slope f hst hcontOnst hdiffOn with ⟨c, hcIoo, hc⟩
  have hc₀ : 0 ≤ c := le_trans hs₀ (le_of_lt hcIoo.1)
  have hcnonpos : f c ≤ 0 := hnonpos c ⟨hcIoo.1, le_of_lt hcIoo.2⟩
  have hderivc : 0 ≤ deriv f c := hderiv c hc₀ hcnonpos
  have hslope : deriv f c = (f t₀ - f s) / (t₀ - s) := hc
  have hdenom : 0 < t₀ - s := sub_pos.mpr hst
  have hnum : 0 ≤ f t₀ - f s := by
    have hdiv : 0 ≤ (f t₀ - f s) / (t₀ - s) := by simpa [hslope] using hderivc
    rcases div_nonneg_iff.mp hdiv with h | h
    · exact h.1
    · have hden : 0 ≤ t₀ - s := le_of_lt hdenom
      linarith
  have : 0 ≤ f t₀ := by
    rw [hfs] at hnum
    simpa using hnum
  exact not_lt_of_ge this hfneg

/-! ## The matrix ODE maximum principle -/

/-- **Scalar sign-preservation on a finite horizon.**  Same first-crossing/mean-value argument
as `nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos`, with the differentiability hypothesis
restricted to the closed interval `[0,T]` and the derivative sign condition required only on
the *open* interval `(0,T)`.  The latter is exactly the part of the interval used by the
argument, so the theorem applies to paths whose tangent condition degenerates at the terminal
time — e.g. a metric reaching the extinction time of a Ricci flow. -/
theorem nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos_Icc {f : ℝ → ℝ} {T : ℝ}
    (hf₀ : 0 ≤ f 0)
    (hdiff : ∀ t, t ∈ Icc 0 T → DifferentiableAt ℝ f t)
    (hderiv : ∀ t, t ∈ Ioo 0 T → f t ≤ 0 → 0 ≤ deriv f t) :
    ∀ t, t ∈ Icc 0 T → 0 ≤ f t := by
  intro t₀ ht₀
  by_contra hneg
  have hfneg : f t₀ < 0 := lt_of_not_ge hneg
  have hcontOn : ContinuousOn f (Icc 0 t₀) := by
    intro x hx
    exact (hdiff x ⟨hx.1, le_trans hx.2 ht₀.2⟩).continuousAt.continuousWithinAt
  rcases exists_first_zero hcontOn ht₀.1 hf₀ hfneg with ⟨s, hsIcc, hfs, hnonpos⟩
  have hs₀ : 0 ≤ s := hsIcc.1
  have hst : s < t₀ := by
    by_contra h
    have hle : t₀ ≤ s := le_of_not_gt h
    have hs₀' : s = t₀ := le_antisymm hsIcc.2 hle
    rw [hs₀'] at hfs
    linarith
  have hcontOnst : ContinuousOn f (Icc s t₀) :=
    hcontOn.mono (by intro x hx; exact ⟨le_trans hs₀ hx.1, hx.2⟩)
  have hdiffOn : DifferentiableOn ℝ f (Ioo s t₀) := by
    intro x hx
    exact (hdiff x ⟨le_trans hs₀ (le_of_lt hx.1),
      le_trans (le_of_lt hx.2) ht₀.2⟩).differentiableWithinAt
  rcases exists_deriv_eq_slope f hst hcontOnst hdiffOn with ⟨c, hcIoo, hc⟩
  have hc₀ : 0 ≤ c := le_trans hs₀ (le_of_lt hcIoo.1)
  have hcnonpos : f c ≤ 0 := hnonpos c ⟨hcIoo.1, le_of_lt hcIoo.2⟩
  have hderivc : 0 ≤ deriv f c :=
    hderiv c ⟨lt_of_le_of_lt hs₀ hcIoo.1, lt_of_lt_of_le hcIoo.2 ht₀.2⟩ hcnonpos
  have hslope : deriv f c = (f t₀ - f s) / (t₀ - s) := hc
  have hdenom : 0 < t₀ - s := sub_pos.mpr hst
  have hnum : 0 ≤ f t₀ - f s := by
    have hdiv : 0 ≤ (f t₀ - f s) / (t₀ - s) := by simpa [hslope] using hderivc
    rcases div_nonneg_iff.mp hdiv with h | h
    · exact h.1
    · have hden : 0 ≤ t₀ - s := le_of_lt hdenom
      linarith
  have : 0 ≤ f t₀ := by
    rw [hfs] at hnum
    simpa using hnum
  exact not_lt_of_ge this hfneg

/-- **Matrix ODE maximum principle (elementary sufficient form).**

A path `M : ℝ → n → n → ℝ` (read as a time-dependent `n × n` real matrix) that is
differentiable at every `t ≥ 0`, Hermitian-valued at every time, positive semidefinite at
time `0`, and satisfies the **quadratic-form tangent condition** — for every `t ≥ 0` and
every vector `v`, if `vᵀ M(t) v ≤ 0` then `0 ≤ vᵀ M'(t) v` — stays positive semidefinite for
all `t ≥ 0`. This is the honest matrix analogue of the scalar lemma above, obtained by
applying it to the scalar path `t ↦ vᵀ M(t) v` for every `v`. -/
theorem staysPosSemidef_of_tangent {n : Type u} [Fintype n]
    {M : ℝ → n → n → ℝ}
    (hdiff : ∀ t, 0 ≤ t → DifferentiableAt ℝ M t)
    (hHerm : ∀ t, Matrix.IsHermitian (M t))
    (hinit : Matrix.PosSemidef (M 0))
    (htan : ∀ t, 0 ≤ t → ∀ v : n → ℝ,
      star v ⬝ᵥ (Matrix.mulVec (M t) v) ≤ 0 →
        0 ≤ star v ⬝ᵥ (Matrix.mulVec (show n → n → ℝ from deriv M t) v)) :
    ∀ t, 0 ≤ t → Matrix.PosSemidef (M t) := by
  intro t ht
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm t, ?_⟩
  intro v
  let φ : ℝ → ℝ := fun s => star v ⬝ᵥ (Matrix.mulVec (M s) v)
  have hφdiff : ∀ s, 0 ≤ s → DifferentiableAt ℝ φ s := by
    intro s hs
    let L : (n → n → ℝ) →L[ℝ] ℝ := {
        toFun := fun A => star v ⬝ᵥ (Matrix.mulVec A v)
        map_add' := by
          intro A B
          simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
            Finset.mul_sum]
        map_smul' := by
          intro a A
          simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum]
        cont := by
          -- a linear map on the finite-dimensional space `n → n → ℝ` is continuous
          let Llin : (n → n → ℝ) →ₗ[ℝ] ℝ := {
            toFun := fun A => star v ⬝ᵥ (Matrix.mulVec A v)
            map_add' := by
              intro A B
              simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
                Finset.mul_sum]
            map_smul' := by
              intro a A
              simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
          simpa [Llin] using Llin.continuous_of_finiteDimensional }
    change DifferentiableAt ℝ (fun s => L (M s)) s
    exact (L.hasFDerivAt.comp_hasDerivAt s (hdiff s hs).hasDerivAt).differentiableAt
  have hφinit : 0 ≤ φ 0 := Matrix.PosSemidef.dotProduct_mulVec_nonneg hinit v
  have hφderiv : ∀ s, 0 ≤ s → φ s ≤ 0 → 0 ≤ deriv φ s := by
    intro s hs hle
    let L : (n → n → ℝ) →L[ℝ] ℝ := {
        toFun := fun A => star v ⬝ᵥ (Matrix.mulVec A v)
        map_add' := by
          intro A B
          simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
            Finset.mul_sum]
        map_smul' := by
          intro a A
          simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum]
        cont := by
          let Llin : (n → n → ℝ) →ₗ[ℝ] ℝ := {
            toFun := fun A => star v ⬝ᵥ (Matrix.mulVec A v)
            map_add' := by
              intro A B
              simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
                Finset.mul_sum]
            map_smul' := by
              intro a A
              simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
          simpa [Llin] using Llin.continuous_of_finiteDimensional }
    have hd : HasDerivAt (fun s => L (M s)) (L (deriv M s)) s :=
      L.hasFDerivAt.comp_hasDerivAt s (hdiff s hs).hasDerivAt
    have hder : deriv (fun s => L (M s)) s =
        star v ⬝ᵥ (Matrix.mulVec (show n → n → ℝ from deriv M s) v) := by
      rw [hd.deriv]
      rfl
    change 0 ≤ deriv (fun s => L (M s)) s
    rw [hder]
    have hle' : star v ⬝ᵥ (Matrix.mulVec (M s) v) ≤ 0 := by
      simpa [φ] using hle
    exact htan s hs v hle'
  have hmain := nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos
    (f := φ) hφinit hφdiff hφderiv
  simpa [φ] using hmain t ht

/-- **Matrix ODE maximum principle on a finite horizon.**  The path is required to be
differentiable on `[0,T]`, Hermitian-valued on `[0,T]`, positive semidefinite at time `0`, and
to satisfy the quadratic-form tangent condition on the *open* interval `(0,T)`; the conclusion
is positive semidefiniteness on all of `[0,T]`.  Compared with `staysPosSemidef_of_tangent`
this is what makes the theorem applicable to a path whose tangent condition degenerates at the
terminal time (for instance a metric reaching the extinction time of a Ricci flow): at the
terminal time only Hermitian-valuedness is needed, not the tangent condition. -/
theorem staysPosSemidef_of_tangent_Icc {n : Type u} [Fintype n]
    {M : ℝ → n → n → ℝ} {T : ℝ}
    (hdiff : ∀ t, t ∈ Icc 0 T → DifferentiableAt ℝ M t)
    (hHerm : ∀ t, t ∈ Icc 0 T → Matrix.IsHermitian (M t))
    (hinit : Matrix.PosSemidef (M 0))
    (htan : ∀ t, t ∈ Ioo 0 T → ∀ v : n → ℝ,
      star v ⬝ᵥ (Matrix.mulVec (M t) v) ≤ 0 →
        0 ≤ star v ⬝ᵥ (Matrix.mulVec (show n → n → ℝ from deriv M t) v)) :
    ∀ t, t ∈ Icc 0 T → Matrix.PosSemidef (M t) := by
  intro t ht
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm t ht, ?_⟩
  intro v
  let L : (n → n → ℝ) →L[ℝ] ℝ := {
      toFun := fun A => star v ⬝ᵥ (Matrix.mulVec A v)
      map_add' := by
        intro A B
        simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
          Finset.mul_sum]
      map_smul' := by
        intro a A
        simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum]
      cont := by
        let Llin : (n → n → ℝ) →ₗ[ℝ] ℝ := {
          toFun := fun A => star v ⬝ᵥ (Matrix.mulVec A v)
          map_add' := by
            intro A B
            simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
              Finset.mul_sum]
          map_smul' := by
            intro a A
            simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
        simpa [Llin] using Llin.continuous_of_finiteDimensional }
  let φ : ℝ → ℝ := fun s => star v ⬝ᵥ (Matrix.mulVec (M s) v)
  have hφdiff : ∀ s, s ∈ Icc 0 T → DifferentiableAt ℝ φ s := by
    intro s hs
    change DifferentiableAt ℝ (fun s => L (M s)) s
    exact (L.hasFDerivAt.comp_hasDerivAt s (hdiff s hs).hasDerivAt).differentiableAt
  have hφinit : 0 ≤ φ 0 := Matrix.PosSemidef.dotProduct_mulVec_nonneg hinit v
  have hφderiv : ∀ s, s ∈ Ioo 0 T → φ s ≤ 0 → 0 ≤ deriv φ s := by
    intro s hs hle
    have hd : HasDerivAt (fun s => L (M s)) (L (deriv M s)) s :=
      L.hasFDerivAt.comp_hasDerivAt s (hdiff s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).hasDerivAt
    have hder : deriv (fun s => L (M s)) s =
        star v ⬝ᵥ (Matrix.mulVec (show n → n → ℝ from deriv M s) v) := by
      rw [hd.deriv]
      rfl
    change 0 ≤ deriv (fun s => L (M s)) s
    rw [hder]
    have hle' : star v ⬝ᵥ (Matrix.mulVec (M s) v) ≤ 0 := by simpa [φ] using hle
    exact htan s hs v hle'
  have hmain := nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos_Icc
    (f := φ) hφinit hφdiff hφderiv
  simpa [φ] using hmain t ht

/-- **Field form.** If `M` is a differentiable path solving `deriv M t = P (M t)` where `P`
satisfies the strengthened tangent condition on all Hermitian matrices, `M` is
Hermitian-valued, and `M 0` is PSD, then `M t` is PSD for all `t ≥ 0`. -/
theorem staysPosSemidef_of_field {n : Type u} [Fintype n]
    {M : ℝ → n → n → ℝ} (P : Matrix n n ℝ → Matrix n n ℝ)
    (hdiff : ∀ t, 0 ≤ t → DifferentiableAt ℝ M t)
    (hHerm : ∀ t, Matrix.IsHermitian (M t))
    (hinit : Matrix.PosSemidef (M 0))
    (hode : ∀ t, 0 ≤ t → deriv M t = P (M t))
    (hC : ∀ A : Matrix n n ℝ, Matrix.IsHermitian A → ∀ v : n → ℝ,
      star v ⬝ᵥ (Matrix.mulVec A v) ≤ 0 → 0 ≤ star v ⬝ᵥ (Matrix.mulVec (P A) v)) :
    ∀ t, 0 ≤ t → Matrix.PosSemidef (M t) := by
  refine staysPosSemidef_of_tangent (M := M) hdiff hHerm hinit ?_
  intro t ht v hv
  rw [hode t ht]
  exact hC (M t) (hHerm t) v hv

/-! ## The concrete nondegenerate field `P(A) = A² - A` -/

/-- **The field `P(A) = A² - A` satisfies the strengthened tangent condition on Hermitian
matrices.** For Hermitian `A` and a vector `v` with `vᵀAv ≤ 0`:
`vᵀ(A² - A)v = (Av)ᵀ(Av) - vᵀAv ≥ 0`. This is the honest check that makes the theorem above
applicable to the genuinely nonlinear ODE `M' = M² - M`. -/
theorem tangentCondition_selfSq_sub_self {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : Matrix.IsHermitian A) (v : n → ℝ)
    (hv : star v ⬝ᵥ (Matrix.mulVec A v) ≤ 0) :
    0 ≤ star v ⬝ᵥ (Matrix.mulVec (A ^ 2 - A) v) := by
  have h1 : star v ⬝ᵥ (Matrix.mulVec (A ^ 2) v) = star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v) := by
    rw [pow_two]
    rw [← Matrix.mulVec_mulVec]
    change star v ⬝ᵥ (fun i => (A i) ⬝ᵥ (Matrix.mulVec A v)) =
      star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)
    rw [← dotProduct_assoc]
    have h2 : star (Matrix.mulVec A v) = Matrix.vecMul (star v) A := by
      rw [Matrix.star_mulVec, hA]
    change Matrix.vecMul (star v) A ⬝ᵥ (Matrix.mulVec A v) =
      star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)
    rw [← h2]
  rw [Matrix.sub_mulVec]
  rw [show star v ⬝ᵥ (Matrix.mulVec (A ^ 2) v - Matrix.mulVec A v)
      = star v ⬝ᵥ (Matrix.mulVec (A ^ 2) v) - star v ⬝ᵥ (Matrix.mulVec A v) by
    simp [dotProduct, mul_sub]]
  rw [h1]
  have hnonneg : 0 ≤ star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v) :=
    dotProduct_self_star_nonneg (Matrix.mulVec A v)
  nlinarith

/-! ## The explicit model solution `M(t) = diag(1/(1+eᵗ), 1/(1+2eᵗ))` -/

/-- The scalar entry `λ_c(t) = (1 + c eᵗ)⁻¹`. -/
noncomputable def lambdaInv (c t : ℝ) : ℝ := (1 + c * Real.exp t)⁻¹

/-- The derivative of `λ_c`: `λ_c' = -c eᵗ / (1 + c eᵗ)²`. -/
theorem hasDerivAt_lambdaInv (c t : ℝ) (hne : 1 + c * Real.exp t ≠ 0) :
    HasDerivAt (fun t : ℝ => lambdaInv c t)
      (-(c * Real.exp t) / (1 + c * Real.exp t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + c * Real.exp t) (c * Real.exp t) t :=
    ((Real.hasDerivAt_exp t).const_mul c).const_add 1
  have hinv : HasDerivAt (fun t : ℝ => (1 + c * Real.exp t)⁻¹)
      ((-((1 + c * Real.exp t) ^ 2)⁻¹) * (c * Real.exp t)) t :=
    (hasDerivAt_inv hne).comp t h1
  have hgoal : HasDerivAt (fun t : ℝ => (1 + c * Real.exp t)⁻¹)
      (-(c * Real.exp t) / (1 + c * Real.exp t) ^ 2) t := by
    have hder : (-((1 + c * Real.exp t) ^ 2)⁻¹) * (c * Real.exp t) =
        -(c * Real.exp t) / (1 + c * Real.exp t) ^ 2 := by
      field_simp [hne]
    rw [← hder]
    exact hinv
  simpa [lambdaInv] using hgoal

/-- The ODE relation of the entries: `λ² - λ = -c eᵗ/(1 + c eᵗ)²`. -/
theorem lambdaInv_sq_sub (c t : ℝ) (hne : 1 + c * Real.exp t ≠ 0) :
    lambdaInv c t ^ 2 - lambdaInv c t = -((c * Real.exp t) / (1 + c * Real.exp t) ^ 2) := by
  rw [lambdaInv]
  field_simp [hne]
  ring

/-- **Derivative of a diagonal path.** The diagonal matrix path built from entrywise
differentiable entries is differentiable, with derivative the diagonal of the entrywise
derivatives. (mathlib's matrix normed structures are non-instances, so the statement is
formulated with the path valued in the Pi type `n → n → ℝ`.) -/
theorem diagonal_hasDerivAt {n : Type u} [Fintype n] [DecidableEq n]
    {f : ℝ → n → ℝ} {f' : n → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => f s i) (f' i) t) :
    HasDerivAt (fun s : ℝ => show n → n → ℝ from Matrix.diagonal (f s))
      (show n → n → ℝ from Matrix.diagonal f') t := by
  let LdiagLin : (n → ℝ) →ₗ[ℝ] n → n → ℝ := {
    toFun := fun x i j => if i = j then x i else 0
    map_add' := by
      intro x y
      ext i j
      by_cases hij : i = j <;> simp [hij]
    map_smul' := by
      intro a x
      ext i j
      by_cases hij : i = j <;> simp [hij, smul_eq_mul] }
  let Ldiag : (n → ℝ) →L[ℝ] n → n → ℝ := {
    toLinearMap := LdiagLin
    cont := by
      exact LdiagLin.continuous_of_finiteDimensional }
  let Φ' : ℝ →L[ℝ] n → ℝ :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.toSpanSingleton ℝ (f' i))
  have hF : HasFDerivAt f Φ' t := by
    refine hasFDerivAt_pi'' ?_
    intro i
    have hid : HasFDerivAt (fun x => f x i) (ContinuousLinearMap.toSpanSingleton ℝ (f' i)) t :=
      (h i).hasFDerivAt
    have hderiv : (ContinuousLinearMap.proj i).comp Φ' =
        ContinuousLinearMap.toSpanSingleton ℝ (f' i) := by
      apply ContinuousLinearMap.ext
      intro x
      simp [Φ']
    rwa [hderiv]
  have hder : Ldiag.comp Φ' =
      (ContinuousLinearMap.toSpanSingleton ℝ (fun i j => if i = j then f' i else 0) :
        ℝ →L[ℝ] n → n → ℝ) := by
    apply ContinuousLinearMap.ext
    intro s
    ext i j
    by_cases hij : i = j <;> simp [Ldiag, LdiagLin, Φ', hij,
      ContinuousLinearMap.toSpanSingleton_apply]
  have hcomp : HasFDerivAt (fun s : ℝ => Ldiag (f s)) (Ldiag.comp Φ') t :=
    Ldiag.hasFDerivAt.comp t hF
  have hfderiv : HasFDerivAt (fun s : ℝ => Ldiag (f s))
      (ContinuousLinearMap.toSpanSingleton ℝ (fun i j => if i = j then f' i else 0)) t := by
    rw [← hder]
    exact hcomp
  exact hasDerivAt_iff_hasFDerivAt.mpr hfderiv

/-- The explicit model path `M(t) = diag(λ₁(t), λ₂(t))` with `λᵢ(t) = (1 + (i+1) eᵗ)⁻¹`,
i.e. `diag(1/(1+eᵗ), 1/(1+2eᵗ))`, formulated with the Pi-typed codomain so that
differentiability is available (mathlib's matrix normed structures are non-instances). -/
noncomputable def quadSelfPath (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t)

/-- The explicit path is positive semidefinite at every time (checked directly). -/
theorem quadSelfPath_posSemidef (t : ℝ) : Matrix.PosSemidef (quadSelfPath t) := by
  rw [quadSelfPath]
  refine Matrix.PosSemidef.diagonal ?_
  intro i
  change 0 ≤ (1 + (((i : ℕ) + 1 : ℝ) * Real.exp t))⁻¹
  exact inv_nonneg.mpr (le_of_lt (by positivity))

/-- The explicit path is Hermitian (symmetric) at every time. -/
theorem quadSelfPath_hermitian (t : ℝ) : Matrix.IsHermitian (quadSelfPath t) := by
  rw [quadSelfPath]
  exact Matrix.isHermitian_diagonal_iff.mpr (fun i => by
    change star (lambdaInv (((i : ℕ) + 1 : ℝ)) t) = lambdaInv (((i : ℕ) + 1 : ℝ)) t
    rfl)

/-- `M(t)² - M(t)` for the model path, stated with the Pi-typed codomain (the matrix
squaring is performed on the `Matrix`-typed diagonal, not as pointwise squaring). -/
noncomputable def quadSelfSquareSub (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t) ^ 2
    - Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t)

/-- **The explicit path solves `M' = M² - M`.** -/
theorem quadSelfPath_solves (t : ℝ) :
    HasDerivAt quadSelfPath (quadSelfSquareSub t) t := by
  have hd := diagonal_hasDerivAt (n := Fin 2)
    (f := fun s i => lambdaInv (((i : ℕ) + 1 : ℝ)) s)
    (f' := fun i : Fin 2 => (-((((i : ℕ) + 1 : ℝ) * Real.exp t))) /
      (1 + ((i : ℕ) + 1 : ℝ) * Real.exp t) ^ 2)
    (t := t) (fun i => hasDerivAt_lambdaInv (((i : ℕ) + 1 : ℝ)) t (by positivity))
  have hP : (Matrix.diagonal (fun i : Fin 2 => (-((((i : ℕ) + 1 : ℝ) * Real.exp t))) /
      (1 + ((i : ℕ) + 1 : ℝ) * Real.exp t) ^ 2)) =
      Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t) ^ 2
        - Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) t) := by
    rw [Matrix.diagonal_pow, Matrix.diagonal_sub]
    congr 1
    funext i
    rw [Pi.pow_apply]
    rw [lambdaInv_sq_sub (((i : ℕ) + 1 : ℝ)) t (by positivity), neg_div]
  rw [show quadSelfPath = (fun s : ℝ => show Fin 2 → Fin 2 → ℝ from
    Matrix.diagonal (fun i : Fin 2 => lambdaInv (((i : ℕ) + 1 : ℝ)) s)) from by
    funext s i j
    rfl]
  rw [show quadSelfSquareSub t = (show Fin 2 → Fin 2 → ℝ from
    Matrix.diagonal (fun i : Fin 2 => (-((((i : ℕ) + 1 : ℝ) * Real.exp t))) /
      (1 + ((i : ℕ) + 1 : ℝ) * Real.exp t) ^ 2)) from by
    rw [quadSelfSquareSub]
    exact hP.symm]
  exact hd

/-- **Downstream application.** The explicit path `M(t) = diag(1/(1+eᵗ), 1/(1+2eᵗ))` solves
`M' = M² - M`, starts positive semidefinite, and therefore — by the matrix maximum principle
`staysPosSemidef_of_field` instantiated with the verified tangent condition
`tangentCondition_selfSq_sub_self` — stays positive semidefinite for all `t ≥ 0`. The PSD
conclusion is also verified directly in `quadSelfPath_posSemidef`, so this is a genuine
consumption of the theorem, not a projection from an assumed conclusion. -/
theorem quadSelfPath_stays_posSemidef :
    ∀ t, 0 ≤ t → Matrix.PosSemidef (quadSelfPath t) := by
  have hmain := staysPosSemidef_of_field (n := Fin 2) (M := quadSelfPath)
    (P := fun A : Matrix (Fin 2) (Fin 2) ℝ => A ^ 2 - A)
    (hdiff := by
      intro s _
      exact (quadSelfPath_solves s).differentiableAt)
    (hHerm := quadSelfPath_hermitian)
    (hinit := quadSelfPath_posSemidef 0)
    (hode := by
      intro s _
      convert (quadSelfPath_solves s).deriv using 1
      unfold quadSelfPath quadSelfSquareSub
      rfl)
    (hC := tangentCondition_selfSq_sub_self)
  simpa using hmain

/-! ## The checked counterexample for the kernel-only condition -/

/-- **Checked counterexample: the kernel-only tangent condition plus mere continuity does not
preserve the cone.** The function `x(t) = -t²/4` satisfies `x(0) = 0` and, for every `t ≥ 0`,
`HasDerivAt x (-√|x(t)|) t` (i.e. it solves `x' = -√|x|` on `[0,∞)`), yet `x(t) < 0` for
every `t > 0`: the solution leaves the cone `[0,∞)` although the field `P(y) = -√|y|` is
continuous and satisfies the kernel condition at the only boundary point (`P(0) = 0 ≥ 0`).
The strengthened condition used in this module is exactly what rules this example out:
at `y = -1 < 0` one has `P(-1) = -1 < 0`. -/
theorem negSqrtCounterexample :
    (∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s : ℝ => -(s ^ 2) / 4)
      (-(Real.sqrt |-(t ^ 2) / 4|)) t) ∧
    (fun s : ℝ => -(s ^ 2) / 4) 0 = 0 ∧
    (∀ t : ℝ, 0 < t → (fun s : ℝ => -(s ^ 2) / 4) t < 0) ∧
    ContinuousAt (fun y : ℝ => -Real.sqrt |y|) 0 ∧
    (fun y : ℝ => -Real.sqrt |y|) 0 = 0 ∧
    (fun y : ℝ => -Real.sqrt |y|) (-1) < 0 := by
  refine ⟨?_, by norm_num, ?_, ?_, ?_, by norm_num⟩
  · intro t ht
    have hs : Real.sqrt |-(t ^ 2) / 4| = t / 2 := by
      have h1 : |-(t ^ 2 : ℝ) / 4| = t ^ 2 / 4 := by
        rw [abs_div, abs_neg, abs_pow, abs_of_nonneg ht]
        norm_num
      rw [h1, Real.sqrt_div (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_nonneg ht]
      norm_num
    have hd : HasDerivAt (fun s : ℝ => -(s ^ 2) / 4) (-(t / 2)) t := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        have h : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t :=
          (hasDerivAt_id t).mul (hasDerivAt_id t)
        have hfun : (fun s : ℝ => s * s) = fun s : ℝ => s ^ 2 := by
          funext s
          exact (pow_two s).symm
        rw [hfun] at h
        convert h using 1
        ring
      have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2)) (-(2 * t)) t := hsq.neg
      have h2 : HasDerivAt (fun s : ℝ => -(s ^ 2) / 4) (-(2 * t) / 4) t := h1.div_const 4
      convert h2 using 1
      ring
    have hx : -(Real.sqrt |-(t ^ 2) / 4|) = -(t / 2) := by rw [hs]
    simpa [hx] using hd
  · intro t ht
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    nlinarith
  · exact (Real.continuous_sqrt.continuousAt.comp continuous_abs.continuousAt).neg
  · simp

/-! ## Axiom audit (fail-closed; see the per-file audit script)

Every declaration of this file is listed here; `tools/d12_axiom_audit.py` additionally
checks coverage (that no declaration is silently left unaudited). -/

#print axioms lambdaInv
#print axioms quadSelfPath
#print axioms quadSelfSquareSub
#print axioms exists_first_zero
#print axioms nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos
#print axioms nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos_Icc
#print axioms staysPosSemidef_of_tangent
#print axioms staysPosSemidef_of_tangent_Icc
#print axioms staysPosSemidef_of_field
#print axioms tangentCondition_selfSq_sub_self
#print axioms hasDerivAt_lambdaInv
#print axioms lambdaInv_sq_sub
#print axioms diagonal_hasDerivAt
#print axioms quadSelfPath_posSemidef
#print axioms quadSelfPath_hermitian
#print axioms quadSelfPath_solves
#print axioms quadSelfPath_stays_posSemidef
#print axioms negSqrtCounterexample

end TensorMaximumBochner
end D12
end Poincare
