/-
Task `D2-pde-foundation`: statement-only continuous maximum-principle interface.

This file is part of the long-run Poincaré formalization.  It consumes the
accepted `D1-pde-api-map` probe (`longrun/results/D1-pde-api-map.md`), which
established that the pinned mathlib has no heat-equation theory and no parabolic
maximum principle.
-/
import Mathlib

/-!
# `Poincare.Longrun.PDE.ContinuousInterface`

A **statement-only** interface for the continuous parabolic maximum principle,
plus fully checked toy theorems showing that the interface is not vacuous.

## Why statement-only?

The pinned mathlib (`leanprover/lean4:v4.34.0-rc2`, mathlib `7974e751…`) has a
Laplacian and harmonic-function machinery, but no heat kernel and no parabolic
PDE theory.  The continuous maximum principle therefore cannot be proved here.
Following the D1 probe, the statement is recorded as a `Prop`-valued definition
with every hypothesis explicit; it carries **no proof field** and no proof
placeholder of any kind.  (This fixes a weakness of the D1 interface, in which
the conclusion `bound_nonpos` was itself a field.)

## Setting

On the space-time slab `[a,b] × [0,T]`:

* `∂ₜ u = ∂ₓ² u` in the interior (positive sign convention),
* `u` continuous on the closed slab,
* the initial datum `u x 0` is `≤ 0` on `[a,b]`,
* the lateral data `u a t` and `u b t` are `≤ 0` for `t ∈ [0,T]`.

The conclusion is `u x t ≤ 0` on the whole slab.

## Checked toy theorems

* `continuousHeatHypotheses_zero` / `continuousHeatHypotheses_affine` /
  `continuousHeatHypotheses_quadratic`: the hypothesis package is inhabited
  (zero, affine steady states, and the genuine non-steady heat solution
  `u x t = -x^2 - 2t` on `[-1,1] × [0,T]`, for which `∂ₜ u = -2 = ∂ₓ² u`).
* `continuousHeatMaxPrinciple_zero`: the implication holds for the zero solution.
* `continuousHeatMaxPrinciple_of_timeIndependent`: any time-independent function
  with nonpositive initial datum satisfies the implication (a genuine, if easy,
  family of checked instances).
* `continuousHeatMaxPrinciple_affine`: the affine steady state
  `u x t = c * x + d` satisfies the implication whenever its initial datum is
  nonpositive.
* `continuousHeatMaxPrinciple_quadratic`: the implication holds for the
  non-steady solution `u x t = -x^2 - 2t` on `[-1,1] × [0,T]`; here the
  conclusion is verified directly (`x^2 ≥ 0` and `t ≥ 0`), not read off from the
  initial datum, so this is a genuine (if elementary) instance of the maximum
  principle for a solution that actually evolves in time.
-/

open Set

namespace Poincare.Longrun.PDE

/-- Hypotheses of the continuous parabolic maximum principle on the slab
`[a,b] × [0,T]`, with the heat equation, continuity and boundary data all
explicit.  This is a `Prop`-valued structure: it packages assumptions only. -/
structure ContinuousHeatHypotheses (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop where
  /-- `u` satisfies the heat equation `∂ₜ u = ∂ₓ² u` in the slab interior. -/
  heat_equation : ∀ x t, x ∈ Icc a b → t ∈ Ioo 0 T →
    deriv (fun s => u x s) t = iteratedDeriv 2 (fun y => u y t) x
  /-- `u` is continuous on the closed slab. -/
  continuous_on_slab : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc a b ×ˢ Icc 0 T)
  /-- The initial datum is nonpositive on `[a,b]`. -/
  initial_nonpos : ∀ x ∈ Icc a b, u x 0 ≤ 0
  /-- The lateral boundary data are nonpositive. -/
  lateral_nonpos : ∀ t ∈ Icc 0 T, u a t ≤ 0 ∧ u b t ≤ 0

/-- **Statement-only continuous maximum principle.**

The named interface is the implication "hypotheses of the slab problem imply
`u ≤ 0` on the slab".  It is a definition, not a theorem: the pinned mathlib has
no parabolic PDE theory, so no proof of this implication is available.  No proof
placeholder of any kind is used. -/
def ContinuousHeatMaximumPrincipleInterface (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop :=
  ContinuousHeatHypotheses u a b T → ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0

/-- The zero function satisfies the slab hypotheses, so the hypothesis package is
inhabited. -/
theorem continuousHeatHypotheses_zero (a b T : ℝ) :
    ContinuousHeatHypotheses (fun _ _ => (0 : ℝ)) a b T where
  heat_equation := by
    intro x t _ _
    simp
  continuous_on_slab := continuous_const.continuousOn
  initial_nonpos := by
    intro x _
    norm_num
  lateral_nonpos := by
    intro t _
    exact ⟨le_rfl, le_rfl⟩

/-- A nonpositive affine steady state `u x t = c * x + d` satisfies the slab
hypotheses.  This is the checked affine instance of the D1 probe, re-proved in
the `Poincare.Longrun.PDE` namespace. -/
theorem continuousHeatHypotheses_affine {c d a b T : ℝ}
    (hinit : ∀ x ∈ Icc a b, c * x + d ≤ 0)
    (hleft : c * a + d ≤ 0) (hright : c * b + d ≤ 0) :
    ContinuousHeatHypotheses (fun x _ => c * x + d) a b T where
  heat_equation := by
    intro x t _ _
    have h0 : deriv (fun s : ℝ => c * x + d) t = 0 := deriv_const t (c * x + d)
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
  continuous_on_slab := by
    have hcont : Continuous (fun p : ℝ × ℝ => c * p.1 + d) :=
      (continuous_const.mul continuous_fst).add continuous_const
    simpa using hcont.continuousOn
  initial_nonpos := hinit
  lateral_nonpos := by
    intro t _
    exact ⟨hleft, hright⟩

/-- A genuine non-steady heat solution inhabits the slab hypotheses:
`u x t = -x^2 - 2t` on `[-1,1] × [0,T]`.  Indeed `∂ₜ u = -2 = ∂ₓ² u`, the
initial datum `-x^2` is nonpositive, and the lateral data at `x = ±1` are
`-1 - 2t ≤ 0` for `t ≥ 0`. -/
theorem continuousHeatHypotheses_quadratic (T : ℝ) :
    ContinuousHeatHypotheses (fun x t => -x ^ 2 - 2 * t) (-1) 1 T where
  heat_equation := by
    intro x t _ _
    have hL : deriv (fun s : ℝ => -x ^ 2 - 2 * s) t = -2 := by
      have h1 : HasDerivAt (fun s : ℝ => (-2) * s) (-2) t := by
        simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
      have h2 : HasDerivAt (fun s : ℝ => (-x ^ 2) + (-2) * s) (-2) t :=
        h1.const_add (-x ^ 2)
      have h3 : HasDerivAt (fun s : ℝ => -x ^ 2 - 2 * s) (-2) t := by
        convert h2 using 1
        funext s
        ring
      exact h3.deriv
    have hderiv1 : deriv (fun y : ℝ => -y ^ 2 - 2 * t) = fun y => (-2) * y := by
      funext y
      have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        simpa using (hasDerivAt_pow (𝕜 := ℝ) 2 y)
      have h2 : HasDerivAt (fun z : ℝ => (-1) * z ^ 2) ((-1) * (2 * y)) y := h1.const_mul (-1)
      have h3 : HasDerivAt (fun z : ℝ => (-1) * z ^ 2 + (-(2 * t))) ((-1) * (2 * y)) y :=
        h2.add_const (-(2 * t))
      have h4 : HasDerivAt (fun z : ℝ => -z ^ 2 - 2 * t) ((-2) * y) y := by
        convert h3 using 1
        · funext z
          ring
        · ring
      exact h4.deriv
    have hlin : HasDerivAt (fun y : ℝ => (-2) * y) (-2) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
    have hR : iteratedDeriv 2 (fun y : ℝ => -y ^ 2 - 2 * t) x = -2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_zero, hderiv1]
      exact hlin.deriv
    rw [hL, hR]
  continuous_on_slab := by
    have hcont : Continuous (fun p : ℝ × ℝ => -p.1 ^ 2 - 2 * p.2) :=
      ((continuous_fst.pow 2).neg).sub (continuous_const.mul continuous_snd)
    simpa using hcont.continuousOn
  initial_nonpos := by
    intro x _
    have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    simp only [mul_zero, sub_zero]
    linarith
  lateral_nonpos := by
    intro t ht
    have ht0 : 0 ≤ t := (mem_Icc.mp ht).1
    constructor <;> norm_num <;> linarith

/-- **Checked toy instance (zero solution).**  The zero function satisfies the
statement-only interface. -/
theorem continuousHeatMaxPrinciple_zero (a b T : ℝ) :
    ContinuousHeatMaximumPrincipleInterface (fun _ _ => (0 : ℝ)) a b T := by
  intro _ x _ t _
  norm_num

/-- **Checked toy theorem (time-independent data).**  Any function which is
constant in time and whose initial datum is nonpositive satisfies the
statement-only interface.  The proof uses only the initial bound; the heat
equation is irrelevant because the function does not evolve. -/
theorem continuousHeatMaxPrinciple_of_timeIndependent {u : ℝ → ℝ → ℝ} {a b T : ℝ}
    (htime : ∀ x t, u x t = u x 0) :
    ContinuousHeatMaximumPrincipleInterface u a b T := by
  intro h x hx t _
  rw [htime x t]
  exact h.initial_nonpos x hx

/-- **Checked toy theorem (affine steady state).**  For `u x t = c * x + d`, the
implication of the interface holds: the conclusion follows from the initial
bound packaged in the hypotheses. -/
theorem continuousHeatMaxPrinciple_affine (c d a b T : ℝ) :
    ContinuousHeatMaximumPrincipleInterface (fun x _ => c * x + d) a b T := by
  intro h x hx t _
  exact h.initial_nonpos x hx

/-- **Checked toy theorem (non-steady heat solution).**  For the genuine heat
solution `u x t = -x^2 - 2t` on `[-1,1] × [0,T]`, the implication of the
interface holds.  Unlike the steady-state instances, the conclusion is verified
directly from `x^2 ≥ 0` and `t ≥ 0`, not read off from the initial datum. -/
theorem continuousHeatMaxPrinciple_quadratic (T : ℝ) :
    ContinuousHeatMaximumPrincipleInterface (fun x t => -x ^ 2 - 2 * t) (-1) 1 T := by
  intro _ x _ t ht
  have ht0 : 0 ≤ t := (mem_Icc.mp ht).1
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  nlinarith

/-! ## Axiom audit -/

#print axioms ContinuousHeatHypotheses
#print axioms ContinuousHeatMaximumPrincipleInterface
#print axioms continuousHeatHypotheses_zero
#print axioms continuousHeatHypotheses_affine
#print axioms continuousHeatHypotheses_quadratic
#print axioms continuousHeatMaxPrinciple_zero
#print axioms continuousHeatMaxPrinciple_of_timeIndependent
#print axioms continuousHeatMaxPrinciple_affine
#print axioms continuousHeatMaxPrinciple_quadratic

end Poincare.Longrun.PDE
