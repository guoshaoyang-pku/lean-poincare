/-
# Poincare.D7.EvolutionSharp.GibbsSharp

**D7 evolution sharp restatement: the one-variable Gibbs term at the sharp threshold.**

This module consumes the D4 adversarial audit (`D4-counterexample-audit`, finding #5-#7)
and restates the strict one-variable theorems of the promoted D4 cluster
(`Poincare.Longrun.Evolution.Gibbs`) under the **weakest hypothesis the audit proved
sufficient**:

* the promoted `gibbsTerm_strictAnti` assumes `1 < c`;
* the sharpened `gibbsTerm_strictAnti_of_one_le` assumes only `1 ≤ c`;
* the promoted `gibbsTerm_step_lt` assumes `1 < c`;
* the sharpened `gibbsTerm_step_lt_of_one_le` assumes only `1 ≤ c`.

The discarded hypothesis is exactly the strictness `1 < c`; the audit's counterexample
analysis shows that `1 ≤ c` cannot be weakened further (already `c = 1/2 ≥ 0` fails, see
`D4Audit.counterexample_discrete_c_half` and `D4Audit.counterexample_continuous_c_half`).

## Why `1 ≤ c` suffices at the flat spot

For `c = 1` the derivative is

`deriv (gibbsTerm 1) x = -((x - 1)²) * exp (-x)`,

which vanishes only at the isolated point `x = 1`. The function is therefore strictly
antitone on each side of `1`, and the two strict inequalities glue across the flat spot
because `gibbsTerm 1 1 < gibbsTerm 1 x` for `x < 1` and `gibbsTerm 1 y < gibbsTerm 1 1`
for `1 < y`. This is the only place where the proof of the promoted `1 < c` theorem does
not apply; for `1 < c` the promoted proof is reused verbatim.

## Analytic boundary (explicit)

`gibbsTerm` is the one-variable finite model term `(c + x²) e^{-x}`, not Perelman's
`(R + |∇f|²) e^{-f}`. The hypothesis `1 ≤ c` is the finite analogue of a scalar-curvature
lower bound and remains an explicit hypothesis; the flat spot at `(c, x) = (1, 1)` is real
and is exactly why the strict theorem needs the isolated-zero argument rather than a global
strict derivative sign. This file is proof-complete: it uses no `sorry`, no `axiom`, no
`unsafe`, no `native_decide`, and no `proof_wanted`.
-/

import Poincare.Longrun.Evolution

open Set

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.Evolution

/-! ## Strict antitonicity at the threshold `c = 1` -/

/-- **Strict antitonicity of the Gibbs term at the sharp threshold `c = 1`.** The derivative
`-((x - 1)²) e^{-x}` is strictly negative off the isolated flat spot `x = 1`; the two
one-sided strict antitonicity statements glue at the flat spot. -/
theorem gibbsTerm_strictAnti_one : StrictAnti (gibbsTerm 1) := by
  have hcont : Continuous (gibbsTerm 1) := by
    unfold gibbsTerm
    fun_prop
  have hderiv : ∀ x : ℝ, deriv (gibbsTerm 1) x = -((x - 1) ^ 2) * Real.exp (-x) := by
    intro x
    rw [(gibbsTerm_hasDerivAt 1 x).deriv]
    ring
  have hneg : ∀ x : ℝ, x ≠ 1 → deriv (gibbsTerm 1) x < 0 := by
    intro x hx
    rw [hderiv x]
    have hsq : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    have hexp : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith
  have hleft : StrictAntiOn (gibbsTerm 1) (Iic 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic (1 : ℝ)) hcont.continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    exact hneg x (ne_of_lt hx)
  have hright : StrictAntiOn (gibbsTerm 1) (Ici 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici (1 : ℝ)) hcont.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    exact hneg x (ne_of_gt hx)
  intro x y hxy
  rcases le_or_gt y 1 with hy | hy
  · exact hleft (a := x) (mem_Iic.mpr (le_of_lt (lt_of_lt_of_le hxy hy))) (b := y)
      (mem_Iic.mpr hy) hxy
  · by_cases hx1 : 1 ≤ x
    · exact hright (a := x) (mem_Ici.mpr hx1) (b := y) (mem_Ici.mpr (le_of_lt hy)) hxy
    · simp only [not_le] at hx1
      have h1 : gibbsTerm 1 1 < gibbsTerm 1 x :=
        hleft (a := x) (mem_Iic.mpr (le_of_lt hx1)) (b := 1) (mem_Iic.mpr (le_refl 1)) hx1
      have h2 : gibbsTerm 1 y < gibbsTerm 1 1 :=
        hright (a := 1) (mem_Ici.mpr (le_refl 1)) (b := y) (mem_Ici.mpr (le_of_lt hy)) hy
      exact h2.trans h1

/-! ## The sharpened one-variable theorems -/

/-- **Sharpened strict antitonicity.** The hypothesis `1 < c` of the promoted
`gibbsTerm_strictAnti` is overstrong: `1 ≤ c` suffices. For `1 < c` this is the promoted
theorem; for `c = 1` it is `gibbsTerm_strictAnti_one`. -/
theorem gibbsTerm_strictAnti_of_one_le (c : ℝ) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c) := by
  rcases lt_or_eq_of_le hc with hlt | rfl
  · exact Poincare.Longrun.Evolution.gibbsTerm_strictAnti c (le_of_lt hlt)
  · exact gibbsTerm_strictAnti_one

/-- **Sharpened strict one-step inequality.** The hypothesis `1 < c` of the promoted
`gibbsTerm_step_lt` is overstrong: `1 ≤ c` and `0 < u` suffice. -/
theorem gibbsTerm_step_lt_of_one_le {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  gibbsTerm_strictAnti_of_one_le c hc (lt_add_of_pos_right x hu)

/-! ## Axiom audit -/

#print axioms gibbsTerm_strictAnti_one
#print axioms gibbsTerm_strictAnti_of_one_le
#print axioms gibbsTerm_step_lt_of_one_le

end EvolutionSharp
end D7
end Poincare
