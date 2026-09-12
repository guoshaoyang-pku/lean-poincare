#!/usr/bin/env python3
"""Apply the A1 upstream restatement to a *copy* of the release sources.

A1 (D12 ledger): the three promoted D4 theorems
  * Poincare.Longrun.Evolution.gibbsTerm_strictAnti
  * Poincare.Longrun.Evolution.gibbsTerm_step_lt
  * Poincare.Longrun.Evolution.perelmanF_step_lt
carry the overstrong hypothesis `1 < c` where `1 ≤ c` suffices.  The D12 validation rule is
"the blocker stays open until upstream restatement".  This script performs that restatement
on a byte-copy of `release/` (never on the frozen tree itself), using exact-string
replacements that are each asserted to apply exactly once.

ASCII only.  Run from the worktree root:
    python3 baseline/a1/make_patch.py
"""
import hashlib
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PATCHED = os.path.join(ROOT, "baseline", "a1", "patched-release")

# ---------------------------------------------------------------- replacements

GIBBS_OLD = '''/-- Strict antitonicity for `1 < c`: then the derivative is strictly negative everywhere. -/
theorem gibbsTerm_strictAnti (c : ℝ) (hc : 1 < c) : StrictAnti (gibbsTerm c) := by
  apply strictAnti_of_deriv_neg
  intro x
  have hd : deriv (gibbsTerm c) x =
      -((x - 1) ^ 2 + (c - 1)) * Real.exp (-x) := (gibbsTerm_hasDerivAt c x).deriv
  have hsq : 0 < (x - 1) ^ 2 + (c - 1) := by
    have hc1 : 0 < c - 1 := by linarith
    have := sq_nonneg (x - 1)
    linarith
  have hexp : 0 < Real.exp (-x) := Real.exp_pos _
  rw [hd]
  nlinarith
'''

GIBBS_NEW = '''/-- **Strict antitonicity at the sharp threshold `1 ≤ c`.** The originally promoted
hypothesis `1 < c` was overstrong (D12 blocker A1). For `1 < c` the derivative is strictly
negative everywhere. For `c = 1` the derivative `-((x - 1)²) e^{-x}` vanishes only at the
isolated flat spot `x = 1`, so the two one-sided strict antitonicity statements glue across
it. -/
theorem gibbsTerm_strictAnti (c : ℝ) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c) := by
  rcases lt_or_eq_of_le hc with hlt | rfl
  · apply strictAnti_of_deriv_neg
    intro x
    have hd : deriv (gibbsTerm c) x =
        -((x - 1) ^ 2 + (c - 1)) * Real.exp (-x) := (gibbsTerm_hasDerivAt c x).deriv
    have hsq : 0 < (x - 1) ^ 2 + (c - 1) := by
      have hc1 : 0 < c - 1 := by linarith
      have := sq_nonneg (x - 1)
      linarith
    have hexp : 0 < Real.exp (-x) := Real.exp_pos _
    rw [hd]
    nlinarith
  · -- flat-spot case `c = 1`: glue the two one-sided strict antitonicity statements
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
    · exact hleft (mem_Iic.mpr (le_of_lt (lt_of_lt_of_le hxy hy))) (mem_Iic.mpr hy) hxy
    · by_cases hx1 : 1 ≤ x
      · exact hright (mem_Ici.mpr hx1) (mem_Ici.mpr (le_of_lt hy)) hxy
      · simp only [not_le] at hx1
        have h1 : gibbsTerm 1 1 < gibbsTerm 1 x :=
          hleft (a := x) (mem_Iic.mpr (le_of_lt hx1)) (b := 1) (mem_Iic.mpr (le_refl 1)) hx1
        have h2 : gibbsTerm 1 y < gibbsTerm 1 1 :=
          hright (a := 1) (mem_Ici.mpr (le_refl 1)) (b := y) (mem_Ici.mpr (le_of_lt hy)) hy
        exact h2.trans h1
'''

GIBBS_STEP_OLD = '''/-- **Strict discrete one-step inequality.** For `1 < c` and a strictly positive increment
`u > 0`, the Gibbs term strictly decreases. -/
theorem gibbsTerm_step_lt {c x u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  gibbsTerm_strictAnti c hc (lt_add_of_pos_right x hu)
'''

GIBBS_STEP_NEW = '''/-- **Strict discrete one-step inequality at the sharp threshold.** For `1 ≤ c` and a
strictly positive increment `u > 0`, the Gibbs term strictly decreases; the flat spot
`(c, x) = (1, 1)` does not obstruct strictness because the increment is positive. -/
theorem gibbsTerm_step_lt {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  gibbsTerm_strictAnti c hc (lt_add_of_pos_right x hu)
'''

GIBBS_IMPORT_OLD = '''import Poincare.Longrun.CurvatureODE
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
'''

GIBBS_IMPORT_NEW = '''import Poincare.Longrun.CurvatureODE
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.DenselyOrdered
'''

DISCRETE_OLD = '''/-- **Strict decrease (discrete time).** If `1 < c i`, the step size is positive and the D2
reaction at component `i` is strictly positive, then the functional strictly decreases in
one step. -/
theorem perelmanF_step_lt (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 < c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) := by
  unfold perelmanF
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [ev.step n j]
    exact gibbsTerm_step_le (le_of_lt (hc j)) (mul_nonneg (le_of_lt hh) (F.eval_nonneg (traj n) j))
  · rw [ev.step n i]
    exact gibbsTerm_step_lt (hc i) (mul_pos hh hi)
'''

DISCRETE_NEW = '''/-- **Strict decrease (discrete time) at the sharp threshold.** If `1 ≤ c i` (rather than
the originally promoted `1 < c i`), the step size is positive and the D2 reaction at
component `i` is strictly positive, then the functional strictly decreases in one step.
This is the upstream restatement of the A1 finding: the one-variable strict step
`gibbsTerm_step_lt` is already sharp, so the promoted `∀ i, 1 < c i` was overstrong. -/
theorem perelmanF_step_lt (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) := by
  unfold perelmanF
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [ev.step n j]
    exact gibbsTerm_step_le (hc j) (mul_nonneg (le_of_lt hh) (F.eval_nonneg (traj n) j))
  · rw [ev.step n i]
    exact gibbsTerm_step_lt (hc i) (mul_pos hh hi)
'''

DISCRETE_DOC_OLD = '''The strict version `perelmanF_step_lt` shows that when `1 < c i` and the reaction is
strictly positive at a component, the functional strictly decreases.
'''

DISCRETE_DOC_NEW = '''The strict version `perelmanF_step_lt` shows that when `1 ≤ c i` and the reaction is
strictly positive at a component, the functional strictly decreases (the sharp threshold
`1 ≤ c` is the A1 upstream restatement; for `c = 1` the flat spot is bypassed because the
step increment at a component with positive reaction is strictly positive).
'''

EVOLUTION_DOC_OLD = '''* `Poincare.Longrun.Evolution.Gibbs` — the one-variable Gibbs term `(c + x²) e^{-x}`, its
  exact derivative `-((x-1)² + (c-1)) e^{-x}`, antitonicity for `1 ≤ c`, strict antitonicity
  for `1 < c`, and the within/global chain rules;
'''

EVOLUTION_DOC_NEW = '''* `Poincare.Longrun.Evolution.Gibbs` — the one-variable Gibbs term `(c + x²) e^{-x}`, its
  exact derivative `-((x-1)² + (c-1)) e^{-x}`, antitonicity and strict antitonicity both at
  the sharp threshold `1 ≤ c`, and the within/global chain rules;
'''

AUDIT_OLD = '''  · exact gibbsTerm_strictAnti c hlt
'''

AUDIT_NEW = '''  · exact gibbsTerm_strictAnti c (le_of_lt hlt)
'''

SHARP_OLD = '''  · exact Poincare.Longrun.Evolution.gibbsTerm_strictAnti c hlt
'''

SHARP_NEW = '''  · exact Poincare.Longrun.Evolution.gibbsTerm_strictAnti c (le_of_lt hlt)
'''

IMPL_STRICT_OLD = '''theorem gibbsTerm_strictAnti_promoted (c : ℝ) (hc : 1 < c) : StrictAnti (gibbsTerm c) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti c hc
'''

IMPL_STRICT_NEW = '''theorem gibbsTerm_strictAnti_promoted (c : ℝ) (hc : 1 < c) : StrictAnti (gibbsTerm c) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti c (le_of_lt hc)
'''

IMPL_STEP_OLD = '''theorem gibbsTerm_step_lt_promoted {c x u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  Poincare.Longrun.Evolution.gibbsTerm_step_lt hc hu
'''

IMPL_STEP_NEW = '''theorem gibbsTerm_step_lt_promoted {c x u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  Poincare.Longrun.Evolution.gibbsTerm_step_lt (le_of_lt hc) hu
'''

IMPL_FUNC_OLD = '''    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F hc hh ev hi
'''

IMPL_FUNC_NEW = '''    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F (fun i => le_of_lt (hc i)) hh ev hi
'''

AXIOMAUDIT_OLD = "import Poincare.D7.EvolutionSharp.Certificates\n"

AXIOMAUDIT_NEW = ("import Poincare.D7.EvolutionSharp.Certificates\n"
                  "import Poincare.D7.EvolutionSharp.SharpOnlyConsumers\n")

REPLACEMENTS = [
    ("Poincare/Longrun/Evolution/Gibbs.lean", GIBBS_IMPORT_OLD, GIBBS_IMPORT_NEW),
    ("Poincare/Longrun/Evolution/Gibbs.lean", GIBBS_OLD, GIBBS_NEW),
    ("Poincare/Longrun/Evolution/Gibbs.lean", GIBBS_STEP_OLD, GIBBS_STEP_NEW),
    ("Poincare/Longrun/Evolution/Discrete.lean", DISCRETE_DOC_OLD, DISCRETE_DOC_NEW),
    ("Poincare/Longrun/Evolution/Discrete.lean", DISCRETE_OLD, DISCRETE_NEW),
    ("Poincare/Longrun/Evolution.lean", EVOLUTION_DOC_OLD, EVOLUTION_DOC_NEW),
    ("Audit/CounterexampleAudit.lean", AUDIT_OLD, AUDIT_NEW),
    ("Poincare/D7/EvolutionSharp/GibbsSharp.lean", SHARP_OLD, SHARP_NEW),
    ("Poincare/D7/EvolutionSharp/Implications.lean", IMPL_STRICT_OLD, IMPL_STRICT_NEW),
    ("Poincare/D7/EvolutionSharp/Implications.lean", IMPL_STEP_OLD, IMPL_STEP_NEW),
    ("Poincare/D7/EvolutionSharp/Implications.lean", IMPL_FUNC_OLD, IMPL_FUNC_NEW),
    ("Poincare/D7/EvolutionSharp/AxiomAudit.lean", AXIOMAUDIT_OLD, AXIOMAUDIT_NEW),
]

NEW_FILE = "Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean"
NEW_FILE_CONTENT = '''/-
# Poincare.D7.EvolutionSharp.SharpOnlyConsumers

**D7 evolution sharp restatement: consumers that require the sharp hypothesis.**

The A1 upstream restatement (`Poincare.Longrun.Evolution.gibbsTerm_strictAnti`,
`gibbsTerm_step_lt`, `perelmanF_step_lt` now assume `1 ≤ c`) gives the promoted theorems a
kernel-checked downstream consumer that the *old* `1 < c` statements could not serve: the
threshold configuration `c ≡ 1`. For `c = 1` the derivative of the Gibbs term vanishes at
the isolated flat spot `x = 1`, so the strict statements are not instances of the old
`1 < c` theorems; they are genuine consequences of the sharpened hypothesis.

This module records:

* `gibbsTerm_strictAnti_at_threshold_one` — the promoted restated theorem applied at
  `c = 1` (an application that does not typecheck against the old statement);
* `perelmanF_step_lt_at_threshold_one` — the finite Perelman functional strictly decreases
  along a non-static explicit-Euler step when every `c i = 1`; a `1 < c i` hypothesis is
  unavailable at this configuration;
* `perelmanF_step_lt_sharp_of_lt` — backward compatibility: every old-format application is
  recovered from the restated theorem.

## Analytic boundary (explicit)

These are statements about the finite D4 model, not about Perelman's functional along a
Ricci flow. The driver is deliberately small: it is a consumer of the restated promoted
theorems, not a new mathematical development. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.Implications

open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Evolution

universe w

variable {ι : Type w} [Fintype ι]

/-! ## The flat-spot consumer -/

/-- **The restated promoted theorem at the flat spot `c = 1`.** The old promoted statement
required `1 < c` and therefore did not apply here; the sharpened hypothesis `1 ≤ c` does. -/
theorem gibbsTerm_strictAnti_at_threshold_one : StrictAnti (gibbsTerm 1) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti 1 le_rfl

/-- **Sharp-only downstream consumer.** If every component of the curvature data equals `1`
(the threshold excluded by the old statements), the step size is positive and some reaction
component is strictly positive, then the finite Perelman functional strictly decreases in
one explicit-Euler step. This application is impossible against the old `∀ i, 1 < c i`
statement. -/
theorem perelmanF_step_lt_at_threshold_one (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, c i = 1) {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {n : ℕ} {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F (fun i => le_of_eq (hc i).symm) hh ev hi

/-- **Backward compatibility of the restatement.** Every application in the old
`∀ i, 1 < c i` format is recovered from the restated promoted theorem. -/
theorem perelmanF_step_lt_sharp_of_lt (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 < c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F (fun i => le_of_lt (hc i)) hh ev hi

/-! ## Axiom audit -/

#print axioms gibbsTerm_strictAnti_at_threshold_one
#print axioms perelmanF_step_lt_at_threshold_one
#print axioms perelmanF_step_lt_sharp_of_lt

end EvolutionSharp
end D7
end Poincare
'''


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    changed = []
    for rel, old, new in REPLACEMENTS:
        path = os.path.join(PATCHED, rel)
        with open(path, encoding="utf-8") as f:
            text = f.read()
        n = text.count(old)
        if n != 1:
            print("FAIL %s: anchor count %d (expected 1)" % (rel, n))
            return 1
        with open(path, "w", encoding="utf-8") as f:
            f.write(text.replace(old, new))
        changed.append(rel)
        print("patched %s" % rel)

    new_path = os.path.join(PATCHED, NEW_FILE)
    if os.path.exists(new_path):
        print("FAIL new file already exists: %s" % NEW_FILE)
        return 1
    with open(new_path, "w", encoding="utf-8") as f:
        f.write(NEW_FILE_CONTENT)
    print("added   %s" % NEW_FILE)

    print("\nchanged files (sha256 after patch):")
    for rel in sorted(set(changed) | {NEW_FILE}):
        print("  %s  %s" % (sha256(os.path.join(PATCHED, rel)), rel))
    return 0


if __name__ == "__main__":
    sys.exit(main())
