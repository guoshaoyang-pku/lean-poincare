import Poincare.Longrun.CurvatureODE.Evolution
import Poincare.Longrun.CurvatureODE.ScalarODE

/-!
# Poincare.Longrun.CurvatureODE.Invariant

**Stage 2 / curvature-ODE cluster: invariant region and sign preservation.**

This module proves the first main theorem of the cluster: for the reaction field of
`Poincare.Longrun.CurvatureODE.Evolution` (whose reaction is nonnegative in **every** state),
every component of a continuous trajectory is nondecreasing, hence

* `component_monotone`: `traj 0 i ≤ traj t i` on `[0,T]`;
* `nonneg_orthant_invariant`: the nonnegative orthant `{lam | ∀ i, 0 ≤ lam i}` is
  forward-invariant;
* the discrete (explicit Euler) analogues `component_monotone_discrete` and
  `nonneg_orthant_invariant_discrete`.

The engine is the scalar sign-preservation lemma
`Poincare.Longrun.CurvatureODE.le_left_of_hasDerivWithinAt_nonpos` applied to `-trajᵢ`.
The mathematical content is the sign convention: the reaction is `≥ 0` in every state, so
no a priori region restriction is needed. The geometric reading — nonnegative diagonal
curvature data is preserved by the reaction ODE — is conditional on the explicit bridge of
`Poincare.Longrun.CurvatureODE.Bridge`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

open Set

namespace Poincare
namespace Longrun
namespace CurvatureODE

universe w

variable {ι : Type w} [Fintype ι]

/-! ## Continuous-time invariant region -/

/-- **Componentwise monotonicity.** Every component of any solution of the reaction ODE is
nondecreasing, because the reaction `Fᵢ` is nonnegative in every state. -/
theorem component_monotone (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) (i : ι) :
    ∀ t ∈ Icc 0 T, traj 0 i ≤ traj t i := by
  have hcont : ContinuousOn (fun s => -(traj s i)) (Icc 0 T) := (ev.continuous i).neg
  have hderiv : ∀ x ∈ Ico 0 T,
      HasDerivWithinAt (fun s => -(traj s i)) (-(F.eval (traj x) i)) (Ici x) x :=
    fun x hx => (ev.hasDeriv i x hx).neg
  have hmono : ∀ x ∈ Ico 0 T, -(F.eval (traj x) i) ≤ 0 :=
    fun x _ => neg_nonpos.mpr (F.eval_nonneg (traj x) i)
  intro t ht
  have hle := le_left_of_hasDerivWithinAt_nonpos hcont hderiv hmono t ht
  linarith

/-- **Sign preservation.** A nonnegative component stays nonnegative. -/
theorem nonneg_component (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) {i : ι} (h0 : 0 ≤ traj 0 i) :
    ∀ t ∈ Icc 0 T, 0 ≤ traj t i :=
  fun t ht => h0.trans (component_monotone F ev i t ht)

/-- **Invariant-region theorem.** The nonnegative orthant is forward-invariant under the
reaction ODE: if every component of the initial state is nonnegative, then so is every
component at every later time in `[0,T]`. -/
theorem nonneg_orthant_invariant (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) (h0 : ∀ i, 0 ≤ traj 0 i) :
    ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ traj t i :=
  fun t ht i => nonneg_component F ev (h0 i) t ht

/-! ## Discrete (explicit Euler) invariant region -/

/-- **Discrete componentwise monotonicity** for the explicit-Euler recurrence with step
size `h ≥ 0`. -/
theorem component_monotone_discrete (F : ReactionField ι) {h : ℝ} (hh : 0 ≤ h)
    {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) (i : ι) :
    ∀ n, traj 0 i ≤ traj n i := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have hstep : traj n i ≤ traj (n + 1) i := by
      rw [ev.step n i]
      exact le_add_of_nonneg_right (mul_nonneg hh (F.eval_nonneg (traj n) i))
    exact ih.trans hstep

/-- **Discrete invariant-region theorem.** The nonnegative orthant is forward-invariant
under the explicit-Euler recurrence with `h ≥ 0`. -/
theorem nonneg_orthant_invariant_discrete (F : ReactionField ι) {h : ℝ} (hh : 0 ≤ h)
    {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) (h0 : ∀ i, 0 ≤ traj 0 i) :
    ∀ n i, 0 ≤ traj n i :=
  fun n i => (h0 i).trans (component_monotone_discrete F hh ev i n)

/-- **Consistency witness.** The invariant-region theorem applies to the zero trajectory of
the canonical field, so the theorem is not vacuous. -/
theorem zero_orthant_invariant (T : ℝ) :
    ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ (fun _ (_ : ι) => (0 : ℝ)) t i :=
  nonneg_orthant_invariant (ReactionField.hamilton : ReactionField ι)
    (zero_evolutionRelation T) (fun _ => le_refl 0)

end CurvatureODE
end Longrun
end Poincare
