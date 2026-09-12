import Poincare.Longrun.Evolution.Functional
import Poincare.Longrun.CurvatureODE.Monotonicity
import Poincare.Longrun.Entropy.Certificate

/-!
# Poincare.Longrun.Evolution.Continuous

**D4 evolution cluster: continuous-time monotonicity of the finite Perelman functional.**

This module is part of the `D4-evolution-theorem` task. It proves the main continuous-time
monotonicity theorem of the cluster: along any solution of the accepted D2 reaction ODE
`Poincare.Longrun.CurvatureODE.EvolutionRelation`, the finite Perelman-type functional

`perelmanF c lam = ∑ i, (c i + (lam i)²) e^{-lam i}`

is **nonincreasing**, with the exact dissipation identity

`d/dt perelmanF c (traj t) =
  -∑ i, F.eval (traj t) i * ((traj t i - 1)² + (c i - 1)) * e^{-traj t i}`.

Since `F.eval (traj t) i ≥ 0` (D2 `ReactionField.eval_nonneg`) and the curvature condition
`1 ≤ c i` makes the second factor nonnegative, the derivative is `≤ 0`. This is a finite
analogue of the Perelman `F`-functional computation: the dissipation density is exactly the
Gibbs-weighted curvature term `R + |∇f|²` of the finite model.

The theorem is stated both for the D2 interval relation `EvolutionRelation F T traj` and,
via the global relation `GlobalReactionFlow`, for the D3 continuous certificate
`ContinuousAntitoneCertificate`; the latter is an honest inhabitant of the accepted D3
structure, and its checked consequences (`antitoneOn`, `F_le_initial`, flat-spot rigidity)
therefore apply to `perelmanF`.

## Approximation boundary (explicit)

The finite state, the finite sum and the abstract curvature data `c` are **not** a
continuous Ricci flow and **not** Perelman's `F`-functional. The theorem is a statement
about a finite-dimensional reaction ODE; the passage to the continuous functional is the
explicit unproved hypothesis interface of `Poincare.Longrun.Evolution.Bridge`. No `sorry`,
`axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Evolution

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy

universe w

variable {ι : Type w} [Fintype ι]

/-! ## The derivative identity along the D2 reaction ODE -/

/-- **Exact dissipation identity (continuous time).** Along any solution of the D2 reaction
ODE, the right derivative of the finite Perelman functional is the negative Gibbs-weighted
sum of the reaction terms. -/
theorem hasDerivWithinAt_perelmanF (F : ReactionField ι) (c : ι → ℝ) {T : ℝ}
    {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => perelmanF c (traj s))
      (-∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i))) (Ici t) t := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      HasDerivWithinAt (fun s => gibbsTerm (c i) (traj s i))
        (-((traj t i - 1) ^ 2 + (c i - 1)) * Real.exp (-(traj t i)) * F.eval (traj t) i)
        (Ici t) t :=
    fun i _ => gibbsTerm_comp (c i) (ev.hasDeriv i t ht)
  have h := HasDerivWithinAt.fun_sum hterm
  have hderiv : (∑ i : ι, -((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i)) * F.eval (traj t) i)
      = -∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hderiv] at h
  unfold perelmanF
  exact h

/-- **Continuity of the finite Perelman functional along the D2 flow.** -/
theorem continuousOn_perelmanF (F : ReactionField ι) (c : ι → ℝ) {T : ℝ}
    {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    ContinuousOn (fun s => perelmanF c (traj s)) (Icc 0 T) := by
  unfold perelmanF
  apply continuousOn_finsetSum
  intro i _
  unfold gibbsTerm
  exact ((continuousOn_const.add ((ev.continuous i).pow 2)).mul
    (Real.continuous_exp.comp_continuousOn (ev.continuous i).neg))

/-- **Nonpositivity of the dissipation.** For `1 ≤ c i` and a nonnegative reaction
(D2 `ReactionField.eval_nonneg`), every summand of the dissipation is nonnegative, so the
right derivative is `≤ 0`. -/
theorem perelmanF_dissipation_nonpos (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    (lam : ι → ℝ) :
    -∑ i : ι, F.eval lam i * ((lam i - 1) ^ 2 + (c i - 1)) * Real.exp (-(lam i)) ≤ 0 := by
  have hsum : 0 ≤ ∑ i : ι, F.eval lam i * ((lam i - 1) ^ 2 + (c i - 1)) *
      Real.exp (-(lam i)) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : 0 ≤ F.eval lam i := F.eval_nonneg lam i
    have h2 : 0 ≤ (lam i - 1) ^ 2 + (c i - 1) := by
      have hsq : 0 ≤ (lam i - 1) ^ 2 := sq_nonneg _
      have hc1 : 0 ≤ c i - 1 := by linarith [hc i]
      linarith
    have h3 : 0 < Real.exp (-(lam i)) := Real.exp_pos _
    exact mul_nonneg (mul_nonneg h1 h2) (le_of_lt h3)
  linarith

/-! ## The main continuous-time monotonicity theorem -/

/-- **Main theorem (continuous time, interval form).** For any D2 reaction field with
`1 ≤ c i` and any solution of the reaction ODE on `[0,T]`, the finite Perelman functional
is nonincreasing: for `s ≤ t` in `[0,T]`,
`perelmanF c (traj t) ≤ perelmanF c (traj s)`.

The proof is the D2 sign-preservation engine
`Poincare.Longrun.CurvatureODE.le_left_of_hasDerivWithinAt_nonpos` applied to
`t ↦ perelmanF c (traj t)` on `[s,t]`. -/
theorem perelmanF_antitone (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    ∀ ⦃s t : ℝ⦄, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
      perelmanF c (traj t) ≤ perelmanF c (traj s) := by
  intro s t hs ht hst
  have hcont : ContinuousOn (fun x => perelmanF c (traj x)) (Icc s t) :=
    (continuousOn_perelmanF F c ev).mono (fun x hx =>
      ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩)
  have hderiv : ∀ x ∈ Ico s t,
      HasDerivWithinAt (fun y => perelmanF c (traj y))
        (-∑ i : ι, F.eval (traj x) i * ((traj x i - 1) ^ 2 + (c i - 1)) *
          Real.exp (-(traj x i))) (Ici x) x :=
    fun x hx => hasDerivWithinAt_perelmanF F c ev ⟨hs.1.trans hx.1, lt_of_lt_of_le hx.2 ht.2⟩
  have hmono : ∀ x ∈ Ico s t,
      (-∑ i : ι, F.eval (traj x) i * ((traj x i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj x i))) ≤ 0 :=
    fun x _ => perelmanF_dissipation_nonpos F hc (traj x)
  have hle := le_left_of_hasDerivWithinAt_nonpos hcont hderiv hmono t ⟨hst, le_rfl⟩
  exact hle

/-- **Comparison with the initial state.** -/
theorem perelmanF_le_initial (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    perelmanF c (traj t) ≤ perelmanF c (traj 0) :=
  perelmanF_antitone F hc ev ⟨le_refl 0, ht.1.trans ht.2⟩ ht ht.1

/-- **Flat-spot rigidity.** If the functional at time `t ∈ [0,T]` equals its initial value,
then it is constant on the whole interval `[0,t]`. -/
theorem perelmanF_eq_on_Icc_of_eq_at (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj)
    {t : ℝ} (ht : t ∈ Icc 0 T) (heq : perelmanF c (traj t) = perelmanF c (traj 0))
    {s : ℝ} (hs : s ∈ Icc 0 t) :
    perelmanF c (traj s) = perelmanF c (traj 0) := by
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  have h1 : perelmanF c (traj s) ≤ perelmanF c (traj 0) :=
    perelmanF_antitone (s := 0) (t := s) F hc ev ⟨le_refl 0, hsT.1.trans hsT.2⟩ hsT hs.1
  have h2 : perelmanF c (traj t) ≤ perelmanF c (traj s) :=
    perelmanF_antitone (s := s) (t := t) F hc ev hsT ht hs.2
  rw [heq] at h2
  exact le_antisymm h1 h2

/-- **The D3 entropy-interface form of the theorem.** The `EntropyData.F` functional of the
finite counting-measure datum of `Poincare.Longrun.Evolution.Functional` is nonincreasing
along the D2 reaction ODE. This restates `perelmanF_antitone` at the level of the accepted
D3 interface. -/
theorem finiteReactionEntropyData_F_antitone [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) :
    ∀ ⦃s t : ℝ⦄, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
      EntropyData.F (finiteReactionEntropyData c (traj t))
        ≤ EntropyData.F (finiteReactionEntropyData c (traj s)) := by
  intro s t hs ht hst
  rw [finiteReactionEntropyData_F, finiteReactionEntropyData_F]
  exact perelmanF_antitone F hc ev hs ht hst

/-! ## Packaging as a D3 `AntitoneCertificate` -/

/-- **The D4 monotonicity theorem as a D3 antitone certificate.** This is a genuine
inhabitant of the accepted `D3-entropy-interface` structure
`Poincare.Longrun.Entropy.AntitoneCertificate`, with lower bound `0` (nonnegativity of the
finite functional). All of the D3 certificate consequences — comparison
(`F_le_of_le`), the lower bound (`lower_le_value`) and flat-spot rigidity
(`eq_of_le_of_eq`) — therefore apply to the finite Perelman functional. -/
noncomputable def perelmanAntitoneCertificate (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    AntitoneCertificate {t : ℝ // t ∈ Icc 0 T} (fun t => perelmanF c (traj t.1)) where
  mono := fun a b hab => perelmanF_antitone F hc ev a.2 b.2 (show a.1 ≤ b.1 from hab)
  lowerBound := 0
  lower_le := fun _ => perelmanF_nonneg fun i => le_trans zero_le_one (hc i)

/-- **D3 certificate consequence (comparison).** -/
theorem perelmanF_certificate_compare (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj)
    {a b : {t : ℝ // t ∈ Icc 0 T}} (hab : a ≤ b) :
    perelmanF c (traj b.1) ≤ perelmanF c (traj a.1) :=
  (perelmanAntitoneCertificate F hc ev).F_le_of_le hab

/-- **D3 certificate consequence (lower bound).** -/
theorem perelmanF_certificate_lower (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj)
    (t : {t : ℝ // t ∈ Icc 0 T}) :
    0 ≤ perelmanF c (traj t.1) :=
  (perelmanAntitoneCertificate F hc ev).lower_le_value t

/-! ## Global flows and the D3 continuous certificate -/

/-- **A global reaction flow.** The D2 `EvolutionRelation` is an interval relation; for the
D3 `ContinuousAntitoneCertificate` we need a flow defined for all real times. This structure
records global continuity and a global derivative `trajᵢ' = Fᵢ(traj)`; it restricts to
`EvolutionRelation F T traj` on every `[0,T]`. -/
structure GlobalReactionFlow (F : ReactionField ι) (traj : ℝ → ι → ℝ) : Prop where
  /-- Componentwise global continuity. -/
  continuous : ∀ i, Continuous (fun t => traj t i)
  /-- Componentwise global derivative. -/
  hasDeriv : ∀ i (t : ℝ), HasDerivAt (fun s => traj s i) (F.eval (traj t) i) t

/-- A global flow restricts to the D2 interval evolution relation on every `[0,T]`. -/
theorem GlobalReactionFlow.evolutionRelation {F : ReactionField ι} {traj : ℝ → ι → ℝ}
    (G : GlobalReactionFlow F traj) (T : ℝ) : EvolutionRelation F T traj where
  continuous := fun i => (G.continuous i).continuousOn
  hasDeriv := fun i t _ => (G.hasDeriv i t).hasDerivWithinAt

/-- **Global dissipation identity.** The `HasDerivAt` version of
`hasDerivWithinAt_perelmanF` for a global reaction flow. -/
theorem hasDerivAt_perelmanF {F : ReactionField ι} {traj : ℝ → ι → ℝ}
    (G : GlobalReactionFlow F traj) (c : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => perelmanF c (traj s))
      (-∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i))) t := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun s => gibbsTerm (c i) (traj s i))
        (-((traj t i - 1) ^ 2 + (c i - 1)) * Real.exp (-(traj t i)) * F.eval (traj t) i) t :=
    fun i _ => gibbsTerm_comp_hasDerivAt (c i) (G.hasDeriv i t)
  have h := HasDerivAt.fun_sum hterm
  have hderiv : (∑ i : ι, -((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i)) * F.eval (traj t) i)
      = -∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hderiv] at h
  unfold perelmanF
  exact h

/-- Global continuity of the finite Perelman functional along a global flow. -/
theorem continuous_perelmanF_comp {F : ReactionField ι} {traj : ℝ → ι → ℝ}
    (G : GlobalReactionFlow F traj) (c : ι → ℝ) :
    Continuous (fun s => perelmanF c (traj s)) := by
  unfold perelmanF
  apply continuous_finsetSum
  intro i _
  unfold gibbsTerm
  exact ((continuous_const.add ((G.continuous i).pow 2)).mul
    (Real.continuous_exp.comp (G.continuous i).neg))

/-- **The continuous D3 certificate.** A global reaction flow with `1 ≤ c i` yields a
genuine inhabitant of the accepted D3 `ContinuousAntitoneCertificate` for the family
`t ↦ finiteReactionEntropyData c (traj t)`. Its `dissipation` field is the exact negative
Gibbs-weighted reaction sum; the analytic hypotheses of the D3 certificate (derivative,
continuity, sign, lower bound) are all discharged here from the D2 ODE data. -/
noncomputable def continuousPerelmanCertificate [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {F : ReactionField ι} {traj : ℝ → ι → ℝ} (G : GlobalReactionFlow F traj)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) :
    ContinuousAntitoneCertificate (fun t : ℝ => finiteReactionEntropyData c (traj t)) where
  dissipation := fun t => -∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
    Real.exp (-(traj t i))
  hasDerivAt_F := by
    intro t _
    have h := hasDerivAt_perelmanF G c t
    have hfun : (fun s : ℝ => (finiteReactionEntropyData c (traj s)).F) =
        fun s : ℝ => perelmanF c (traj s) := by
      funext s
      exact finiteReactionEntropyData_F c (traj s)
    rw [hfun]
    exact h
  continuousOn_F := by
    apply ContinuousOn.congr (continuous_perelmanF_comp G c).continuousOn
    intro s _
    exact finiteReactionEntropyData_F c (traj s)
  dissipation_nonpos := fun t _ => perelmanF_dissipation_nonpos F hc (traj t)
  lowerBound := 0
  lower_le := fun t _ => by
    rw [finiteReactionEntropyData_F]
    exact perelmanF_nonneg fun i => le_trans zero_le_one (hc i)

/-- **D3 continuous certificate consequence.** The finite `EntropyData.F` is antitone on
`[0,∞)` along any global reaction flow with `1 ≤ c i`. -/
theorem continuousPerelmanCertificate_antitoneOn [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {F : ReactionField ι} {traj : ℝ → ι → ℝ} (G : GlobalReactionFlow F traj)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) :
    AntitoneOn (fun s : ℝ => (finiteReactionEntropyData c (traj s)).F) (Ici 0) :=
  (continuousPerelmanCertificate G hc).antitoneOn

/-- **D3 continuous certificate consequence (initial comparison).** -/
theorem continuousPerelmanCertificate_le_initial
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {F : ReactionField ι} {traj : ℝ → ι → ℝ} (G : GlobalReactionFlow F traj)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    (finiteReactionEntropyData c (traj t)).F ≤ (finiteReactionEntropyData c (traj 0)).F :=
  (continuousPerelmanCertificate G hc).F_le_initial ht

/-! ## Non-vacuity witnesses -/

/-- The constant reaction field `Fᵢ(lam) = 1`, a D2 `ReactionField` (with `a = 0`,
`g = 1`). It has a nontrivial global flow `t ↦ t`, used below to witness that the
continuous D3 certificate is inhabited. -/
def unitReactionField : ReactionField ι where
  a := fun _ => 0
  g := fun _ _ => 1
  a_nonneg := fun _ => le_refl 0
  g_nonneg := fun _ _ => zero_le_one

/-- Evaluation of the constant reaction field. -/
@[simp]
theorem unitReactionField_eval (lam : ι → ℝ) (i : ι) :
    (unitReactionField : ReactionField ι).eval lam i = 1 := by
  simp [ReactionField.eval, unitReactionField]

/-- **A nontrivial global reaction flow.** The state `traj t i = t` solves the constant
reaction ODE `traj' = 1` for all real times. -/
theorem unitGlobalFlow :
    GlobalReactionFlow (unitReactionField : ReactionField ι) (fun t (_ : ι) => t) where
  continuous := fun _ => continuous_id
  hasDeriv := fun i t => by
    rw [unitReactionField_eval]
    exact hasDerivAt_id t

/-- The zero trajectory solves the D2 canonical Hamiltonian reaction field globally. -/
theorem zeroGlobalFlow :
    GlobalReactionFlow (ReactionField.hamilton : ReactionField ι) (fun _ _ => 0) where
  continuous := fun _ => continuous_const
  hasDeriv := fun i t => by
    rw [ReactionField.hamilton_eval_zero]
    simpa using hasDerivAt_const t (0 : ℝ)

/-- **Non-vacuity of the continuous D3 certificate.** The constant reaction field with the
nontrivial global flow `t ↦ t` inhabits `ContinuousAntitoneCertificate`, so the certificate
is not vacuous. -/
theorem continuousPerelmanCertificate_nonvacuous [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (c : ι → ℝ) (hc : ∀ i, 1 ≤ c i) :
    (continuousPerelmanCertificate (unitGlobalFlow (ι := ι)) hc).lowerBound ≤
      (finiteReactionEntropyData c (fun _ : ι => (0 : ℝ))).F :=
  (continuousPerelmanCertificate (unitGlobalFlow (ι := ι)) hc).lower_le_initial

/-! ## Two-sided monotonicity with the D2 scalar functional -/

/-- **Two-sided monotonicity.** Along the same D2 reaction ODE, the D2 scalar functional
`scalarOfState` is nondecreasing (`Poincare.Longrun.CurvatureODE.scalarOfState_monotone`)
while the finite Perelman functional is nonincreasing. -/
theorem two_sided_monotonicity (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    perelmanF c (traj t) ≤ perelmanF c (traj 0) ∧
      scalarOfState (traj 0) ≤ scalarOfState (traj t) :=
  ⟨perelmanF_le_initial F hc ev ht, scalarOfState_monotone F ev t ht⟩

end Evolution
end Longrun
end Poincare
