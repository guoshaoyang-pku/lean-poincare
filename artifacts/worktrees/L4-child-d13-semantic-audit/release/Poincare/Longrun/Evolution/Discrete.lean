import Poincare.Longrun.Evolution.Continuous

/-!
# Poincare.Longrun.Evolution.Discrete

**D4 evolution cluster: discrete-time monotonicity of the finite Perelman functional.**

This module is part of the `D4-evolution-theorem` task. It proves the explicit-Euler
(discrete-time) analogue of `Poincare.Longrun.Evolution.Continuous`: along any D2
`DiscreteEvolution F h traj` with step size `h ≥ 0` and curvature data `1 ≤ c i`, the
finite Perelman functional is nonincreasing,

`perelmanF c (traj (n+1)) ≤ perelmanF c (traj n)`.

The discrete proof needs **no** CFL-type step-size restriction: the one-step inequality is
the monotonicity `gibbsTerm_step_le` of the one-variable Gibbs term, which holds for every
nonnegative increment. This is a genuine strengthening of the explicit-Euler scheme's
stability story for this functional, and it is packaged as a D3
`AntitoneCertificate ℕ`.

The strict version `perelmanF_step_lt` shows that when `1 < c i` and the reaction is
strictly positive at a component, the functional strictly decreases.

## Approximation boundary (explicit)

The discrete theorem is a statement about the D2 explicit-Euler recurrence, not about a
continuous flow. The passage to the continuous-time theorem is `Continuous.lean`; the
passage to a continuous Perelman functional remains the unproved hypothesis interface of
`Poincare.Longrun.Evolution.Bridge`. No `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` occurs in this file.
-/

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Evolution

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy

universe w

variable {ι : Type w} [Fintype ι]

/-- **One-step discrete monotonicity.** For `0 ≤ h` and `1 ≤ c i`, the explicit-Euler step
of the D2 reaction field does not increase the finite Perelman functional. -/
theorem perelmanF_step_le (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) (n : ℕ) :
    perelmanF c (traj (n + 1)) ≤ perelmanF c (traj n) := by
  unfold perelmanF
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ev.step n i]
  exact gibbsTerm_step_le (hc i) (mul_nonneg hh (F.eval_nonneg (traj n) i))

/-- **Main theorem (discrete time).** Along the D2 explicit-Euler recurrence with `h ≥ 0`
and `1 ≤ c i`, the finite Perelman functional is nonincreasing in the time index. -/
theorem perelmanF_antitone_discrete (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) :
    ∀ ⦃m n : ℕ⦄, m ≤ n → perelmanF c (traj n) ≤ perelmanF c (traj m) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (perelmanF_step_le F hc hh ev n).trans ih

/-- **Comparison with the initial state (discrete time).** -/
theorem perelmanF_le_initial_discrete (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) (n : ℕ) :
    perelmanF c (traj n) ≤ perelmanF c (traj 0) :=
  perelmanF_antitone_discrete F hc hh ev (Nat.zero_le n)

/-- **Strict decrease (discrete time).** If `1 < c i`, the step size is positive and the D2
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

/-- **The D3 entropy-interface form (discrete time).** The `EntropyData.F` functional of the
finite counting-measure datum is nonincreasing along the explicit-Euler recurrence. -/
theorem finiteReactionEntropyData_F_antitone_discrete [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) :
    ∀ ⦃m n : ℕ⦄, m ≤ n →
      EntropyData.F (finiteReactionEntropyData c (traj n))
        ≤ EntropyData.F (finiteReactionEntropyData c (traj m)) := by
  intro m n hmn
  rw [finiteReactionEntropyData_F, finiteReactionEntropyData_F]
  exact perelmanF_antitone_discrete F hc hh ev hmn

/-- **Packaging as a D3 `AntitoneCertificate` over `ℕ`.** -/
noncomputable def perelmanAntitoneCertificate_discrete (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) :
    AntitoneCertificate ℕ (fun n => perelmanF c (traj n)) where
  mono := fun _ _ hab => perelmanF_antitone_discrete F hc hh ev hab
  lowerBound := 0
  lower_le := fun _ => perelmanF_nonneg fun i => le_trans zero_le_one (hc i)

/-- **D3 certificate consequence (discrete comparison).** -/
theorem perelmanF_certificate_compare_discrete (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {m n : ℕ} (hmn : m ≤ n) :
    perelmanF c (traj n) ≤ perelmanF c (traj m) :=
  (perelmanAntitoneCertificate_discrete F hc hh ev).F_le_of_le hmn

/-! ## Non-vacuity witness -/

/-- **A nontrivial discrete flow.** The trajectory `traj n i = n` solves the explicit-Euler
recurrence for the constant reaction field `unitReactionField` with step size `1`. -/
theorem unitDiscreteEvolution :
    DiscreteEvolution (unitReactionField : ReactionField ι) 1 (fun n (_ : ι) => (n : ℝ)) where
  step := by
    intro n i
    rw [unitReactionField_eval]
    push_cast
    ring

/-- **Non-vacuity of the discrete certificate.** The nontrivial discrete flow above
inhabits the D3 antitone certificate. -/
theorem perelmanAntitoneCertificate_discrete_nonvacuous (c : ι → ℝ) (hc : ∀ i, 1 ≤ c i) :
    (perelmanAntitoneCertificate_discrete (unitReactionField : ReactionField ι) hc
      (h := 1) (by norm_num) (unitDiscreteEvolution (ι := ι))).lowerBound ≤
      perelmanF c (fun _ : ι => (0 : ℝ)) := by
  simpa using (perelmanAntitoneCertificate_discrete (unitReactionField : ReactionField ι) hc
    (h := 1) (by norm_num) (unitDiscreteEvolution (ι := ι))).lower_le_value 0

end Evolution
end Longrun
end Poincare
