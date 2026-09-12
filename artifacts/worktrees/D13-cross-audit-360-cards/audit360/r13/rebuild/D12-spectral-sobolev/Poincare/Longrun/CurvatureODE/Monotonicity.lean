import Poincare.Longrun.CurvatureODE.Invariant

/-!
# Poincare.Longrun.CurvatureODE.Monotonicity

**Stage 2 / curvature-ODE cluster: scalar monotonicity.**

This module proves the second main theorem of the cluster: the weighted scalar functional

`S_w(lam) = ∑ i, w i * lam i`,  with `w i ≥ 0`,

is nondecreasing along any solution of the reaction ODE of
`Poincare.Longrun.CurvatureODE.Evolution`. The scalar curvature of the diagonal model is
the unweighted case `scalarOfState lam = ∑ i, lam i` (the trace of the diagonal
endomorphism, which the geometry cluster identifies with `scalarCurvature`).

* `hasDerivWithinAt_scalarFunctional` — the derivative of `S_w` along the flow is the
  weighted sum of the reaction terms.
* `scalarFunctional_monotone` — continuous-time monotonicity.
* `scalarOfState_monotone` — the unweighted scalar functional is nondecreasing.
* `scalarFunctional_monotone_discrete` / `scalarOfState_monotone_discrete` — explicit-Euler
  analogues.
* `ReactionField.hamilton_eval_pos` — sign-convention audit: the canonical reaction is
  strictly positive at every nonzero component.

The sign convention matches the reaction part of `∂ₜ R = ΔR + 2|Ric|²`: the reaction term is
nonnegative, so the scalar functional is nondecreasing. The spatial Laplacian is **not**
modeled here; the exact approximation boundary is the explicit interface of
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

/-! ## Continuous-time scalar monotonicity -/

/-- **Derivative of the weighted scalar functional** along the reaction ODE: it is the
weighted sum of the reaction terms. -/
theorem hasDerivWithinAt_scalarFunctional (F : ReactionField ι) (w : ι → ℝ)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => scalarFunctional w (traj s))
      (∑ i : ι, w i * F.eval (traj t) i) (Ici t) t := by
  have hsum : HasDerivWithinAt (fun s => ∑ i : ι, w i * traj s i)
      (∑ i : ι, w i * F.eval (traj t) i) (Ici t) t := by
    have h := HasDerivWithinAt.fun_sum (u := Finset.univ)
      (fun i _ => (ev.hasDeriv i t ht).const_mul (w i))
    simpa using h
  simpa [scalarFunctional] using hsum

/-- **Scalar monotonicity (continuous time).** Along any solution of the reaction ODE, the
weighted scalar functional with nonnegative weights is nondecreasing on `[0,T]`. -/
theorem scalarFunctional_monotone (F : ReactionField ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    ∀ t ∈ Icc 0 T, scalarFunctional w (traj 0) ≤ scalarFunctional w (traj t) := by
  have hcont : ContinuousOn (fun s => -scalarFunctional w (traj s)) (Icc 0 T) := by
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.mul (ev.continuous i)
  have hderiv : ∀ x ∈ Ico 0 T,
      HasDerivWithinAt (fun s => -scalarFunctional w (traj s))
        (-(∑ i : ι, w i * F.eval (traj x) i)) (Ici x) x :=
    fun x hx => (hasDerivWithinAt_scalarFunctional F w ev hx).neg
  have hmono : ∀ x ∈ Ico 0 T, -(∑ i : ι, w i * F.eval (traj x) i) ≤ 0 :=
    fun x _ => neg_nonpos.mpr <|
      Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (F.eval_nonneg (traj x) i)
  intro t ht
  have hle := le_left_of_hasDerivWithinAt_nonpos hcont hderiv hmono t ht
  linarith

/-- **Scalar monotonicity, unweighted form.** The scalar functional `∑ i, lam i` (the trace
of the diagonal endomorphism, i.e. the scalar-curvature contraction of the diagonal model)
is nondecreasing. -/
theorem scalarOfState_monotone (F : ReactionField ι) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) :
    ∀ t ∈ Icc 0 T, scalarOfState (traj 0) ≤ scalarOfState (traj t) := by
  have h := scalarFunctional_monotone F (w := fun _ => 1) (fun _ => zero_le_one) ev
  simpa [scalarFunctional, scalarOfState] using h

/-! ## Discrete (explicit Euler) scalar monotonicity -/

/-- **Scalar monotonicity (explicit Euler).** With step size `h ≥ 0` and nonnegative weights,
the weighted scalar functional is nondecreasing along the discrete recurrence. -/
theorem scalarFunctional_monotone_discrete (F : ReactionField ι) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) :
    ∀ n, scalarFunctional w (traj 0) ≤ scalarFunctional w (traj n) := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have hsplit : scalarFunctional w (traj (n + 1)) =
        scalarFunctional w (traj n) + ∑ i : ι, w i * (h * F.eval (traj n) i) := by
      simp only [scalarFunctional, ev.step, mul_add, Finset.sum_add_distrib]
    have hnonneg : 0 ≤ ∑ i : ι, w i * (h * F.eval (traj n) i) :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw i) (mul_nonneg hh (F.eval_nonneg (traj n) i))
    linarith

/-- **Discrete scalar monotonicity, unweighted form.** -/
theorem scalarOfState_monotone_discrete (F : ReactionField ι) {h : ℝ} (hh : 0 ≤ h)
    {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) :
    ∀ n, scalarOfState (traj 0) ≤ scalarOfState (traj n) := by
  have h := scalarFunctional_monotone_discrete F (w := fun _ => 1) (fun _ => zero_le_one) hh ev
  simpa [scalarFunctional, scalarOfState] using h

/-- **Consistency witness.** The scalar monotonicity theorem applies to the zero trajectory
of the canonical field, so the theorem is not vacuous. -/
theorem zero_scalar_monotone (T : ℝ) :
    ∀ t ∈ Icc 0 T,
      scalarOfState ((fun _ (_ : ι) => (0 : ℝ)) 0) ≤
        scalarOfState ((fun _ (_ : ι) => (0 : ℝ)) t) :=
  scalarOfState_monotone (ReactionField.hamilton : ReactionField ι) (zero_evolutionRelation T)

/-! ## Sign-convention audit -/

/-- **Strict positivity of the canonical reaction.** If a component of the state is nonzero,
the canonical reaction at that component is strictly positive; this fixes the sign
convention (reaction increases the scalar functional, it never decreases it). -/
theorem ReactionField.hamilton_eval_pos (lam : ι → ℝ) (i : ι) (h : lam i ≠ 0) :
    0 < (ReactionField.hamilton : ReactionField ι).eval lam i := by
  rw [ReactionField.hamilton_eval]
  have h1 : 0 < (lam i) ^ 2 := sq_pos_of_ne_zero h
  have h2 : 0 ≤ ∑ j : ι, (lam j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- Sanity computation for the sign convention: at the state `lam = 1` of `Fin 1`, the
canonical reaction is `2 > 0`. -/
example : (ReactionField.hamilton : ReactionField (Fin 1)).eval (fun _ => 1) 0 = 2 := by
  norm_num [ReactionField.hamilton_eval]

/-- Sign-convention audit: the reaction at a negative state is positive, so the nonpositive
orthant is **not** invariant (negative components are pushed up). -/
example : 0 < (ReactionField.hamilton : ReactionField (Fin 1)).eval (fun _ => -1) 0 := by
  norm_num [ReactionField.hamilton_eval]

end CurvatureODE
end Longrun
end Poincare
