/-
# D4-counterexample-audit — adversarial verification of the D4 evolution cluster

This driver imports **only** the promoted umbrella interface
`Poincare.Longrun.Evolution` and re-examines it from the fresh namespace `D4Audit`.
It contains, in order:

1. fresh-namespace re-checks of the promoted monotonicity theorem and its consequences;
2. independent counterexamples to weakened hypotheses:
   * `0 ≤ c` instead of `1 ≤ c` fails already at `c = 1/2`, in discrete and continuous time;
   * `h < 0` instead of `0 ≤ h` fails;
   * a negative reaction (i.e. dropping the D2 `ReactionField.eval_nonneg` content) fails;
   * `0 < h` and `0 < F.eval` are needed for the strict-decrease statement;
   * `0 ≤ c` is needed for `perelmanF_nonneg`;
3. a corrected (sharpened) strict-decrease theorem: the hypothesis `1 < c i` of
   `perelmanF_step_lt` is overstrong and can be weakened to `1 ≤ c i`, because the flat spot
   of `(1 + x²) e^{-x}` at `x = 1` is isolated; the corrected statement is proved here;
4. non-vacuity witnesses for the statement-only approximation boundary;
5. `#print axioms` for every declaration of this file and for the promoted main declarations.

No forbidden proof escape occurs in this file.
-/
import Poincare.Longrun.Evolution

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D4Audit

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy
open Poincare.Longrun.Evolution

universe w

variable {ι : Type w} [Fintype ι]

/-! ## 1. Fresh-namespace re-check of the promoted theorem -/

/-- The promoted continuous-time monotonicity theorem, restated and re-checked in the
fresh namespace `D4Audit`. -/
theorem audit_perelmanF_antitone (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    ∀ ⦃s t : ℝ⦄, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
      perelmanF c (traj t) ≤ perelmanF c (traj s) :=
  perelmanF_antitone F hc ev

/-- The promoted discrete-time monotonicity theorem, re-checked in `D4Audit`. -/
theorem audit_perelmanF_antitone_discrete (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) :
    ∀ ⦃m n : ℕ⦄, m ≤ n → perelmanF c (traj n) ≤ perelmanF c (traj m) :=
  perelmanF_antitone_discrete F hc hh ev

/-- The promoted exact dissipation identity, re-checked in `D4Audit`. -/
theorem audit_hasDerivWithinAt_perelmanF (F : ReactionField ι) (c : ι → ℝ) {T : ℝ}
    {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => perelmanF c (traj s))
      (-∑ i : ι, F.eval (traj t) i * ((traj t i - 1) ^ 2 + (c i - 1)) *
        Real.exp (-(traj t i))) (Ici t) t :=
  hasDerivWithinAt_perelmanF F c ev ht

/-- The promoted two-sided statement, re-checked in `D4Audit`. -/
theorem audit_two_sided_monotonicity (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    perelmanF c (traj t) ≤ perelmanF c (traj 0) ∧
      scalarOfState (traj 0) ≤ scalarOfState (traj t) :=
  two_sided_monotonicity F hc ev ht

/-- The promoted theorem is non-vacuous: the constant reaction field with the nontrivial
global flow `t ↦ t` satisfies all its hypotheses at `c = 1`. -/
theorem nonvacuity_main_theorem :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) ((fun t (_ : Fin 1) => t) 1) ≤
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) ((fun t (_ : Fin 1) => t) 0) :=
  audit_perelmanF_antitone (unitReactionField : ReactionField (Fin 1))
    (fun _ => le_refl 1)
    (GlobalReactionFlow.evolutionRelation (unitGlobalFlow (ι := Fin 1)) 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Elementary sharp bound used repeatedly below: `2 e^{-1} < 1`, i.e. `e > 2`. -/
theorem two_exp_neg_one_lt_one : 2 * Real.exp (-1) < 1 := by
  rw [Real.exp_neg, inv_eq_one_div, mul_one_div, div_lt_one (Real.exp_pos 1)]
  linarith [Real.exp_one_gt_two]

/-- Values of the Gibbs term at the two states used by the counterexamples. -/
theorem gibbsTerm_one_values :
    gibbsTerm 1 1 = 2 * Real.exp (-1) ∧ gibbsTerm 1 0 = 1 := by
  constructor <;> norm_num [gibbsTerm]

/-- The conclusion of the promoted theorem is not constantly an equality: along the same
nontrivial flow it is strict. -/
theorem nonvacuity_main_theorem_strict :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) ((fun t (_ : Fin 1) => t) 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) ((fun t (_ : Fin 1) => t) 0) := by
  simp only [perelmanF, Fin.sum_univ_one]
  rw [gibbsTerm_one_values.1, gibbsTerm_one_values.2]
  exact two_exp_neg_one_lt_one

/-- Sanity value of the exact dissipation identity: along `t ↦ t` with `c = 1`, the
promoted identity gives derivative `-1` at `t = 0`. -/
theorem dissipation_sanity :
    HasDerivAt (fun s : ℝ => perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => s)) (-1) 0 := by
  have h := hasDerivAt_perelmanF (unitGlobalFlow (ι := Fin 1))
    (fun _ : Fin 1 => (1 : ℝ)) 0
  simpa using h

/-! ## 2. Counterexample: `0 ≤ c` cannot replace `1 ≤ c` (threshold `c = 1` is sharp) -/

/-- The arithmetic inequality behind the `c = 1/2` counterexample: `3 e^{-1} < 9 e^{-2}`,
i.e. `e < 3`. -/
theorem three_exp_neg_one_lt_nine_exp_neg_two :
    3 * Real.exp (-1) < 9 * Real.exp (-2) := by
  have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp2 : Real.exp (-2) = ((Real.exp 1) * (Real.exp 1))⁻¹ := by
    rw [show (-2 : ℝ) = -(1 + 1) by norm_num, Real.exp_neg, Real.exp_add]
  rw [Real.exp_neg, hexp2, inv_eq_one_div, inv_eq_one_div]
  field_simp
  linarith

/-- At `c = 1/2` (which satisfies the weakened hypothesis `0 ≤ c`) the one-variable Gibbs
term increases from `x = 1` to `x = 2`. -/
theorem gibbsTerm_half_one_lt_two : gibbsTerm (1 / 2) 1 < gibbsTerm (1 / 2) 2 := by
  have h := three_exp_neg_one_lt_nine_exp_neg_two
  norm_num [gibbsTerm] at h ⊢
  linarith

/-- **Counterexample (discrete).** With `c = 1/2 ≥ 0` and the square reaction, one
explicit-Euler step with `h = 1` from `lam = 1` to `lam = 2` strictly increases the finite
Perelman functional. So the hypothesis `1 ≤ c i` of `perelmanF_step_le` /
`perelmanF_antitone_discrete` cannot be weakened to `0 ≤ c i`. -/
theorem counterexample_discrete_c_half :
    perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) <
      perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ))
        (eulerStep (squareField : ReactionField (Fin 1)) 1 (fun _ => (1 : ℝ))) := by
  rw [eulerStep_squareField_one]
  simpa [perelmanF, Fin.sum_univ_one] using gibbsTerm_half_one_lt_two

/-- The weakened discrete monotonicity statement (with `0 ≤ c` in place of `1 ≤ c`) is
false. -/
theorem antitone_discrete_fails_at_c_half :
    ¬ (perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ))
        (eulerStep (squareField : ReactionField (Fin 1)) 1 (fun _ => (1 : ℝ))) ≤
      perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => (1 : ℝ))) :=
  not_le.mpr counterexample_discrete_c_half

/-- **Counterexample (continuous).** The explicit blow-up trajectory
`lam(t) = 1/(1 - t)` is a genuine `EvolutionRelation` for the square reaction field on
`[0, 1/2]`; along it the functional with `c = 1/2 ≥ 0` strictly increases from `t = 0` to
`t = 1/2`. So `1 ≤ c` cannot be weakened to `0 ≤ c` in `perelmanF_antitone` either. -/
theorem counterexample_continuous_c_half :
    perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ)) (squareTraj 0) <
      perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ)) (squareTraj (1 / 2)) := by
  have h := gibbsTerm_half_one_lt_two
  norm_num [perelmanF, gibbsTerm, squareTraj, Fin.sum_univ_one] at h ⊢
  exact h

/-- The trajectory used by the continuous counterexample really solves the D2 reaction ODE,
so the counterexample is not an artefact of a fictitious trajectory. -/
theorem counterexample_continuous_c_half_is_evolution :
    EvolutionRelation (squareField : ReactionField (Fin 1)) (1 / 2) squareTraj :=
  squareTraj_evolution

/-- The weakened continuous monotonicity statement (with `0 ≤ c` in place of `1 ≤ c`) is
false. -/
theorem antitone_fails_at_c_half :
    ¬ (perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ)) (squareTraj (1 / 2)) ≤
      perelmanF (fun _ : Fin 1 => (1 / 2 : ℝ)) (squareTraj 0)) :=
  not_le.mpr counterexample_continuous_c_half

/-! ## 3. Counterexample: `h < 0` cannot replace `0 ≤ h` -/

/-- **Counterexample.** With `c = 1`, `lam = 2` and a negative step `h = -1` (the square
reaction sends the state to `-2`), the functional strictly increases. So the hypothesis
`0 ≤ h` of the discrete theorem is necessary. -/
theorem counterexample_negative_step :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (2 : ℝ)) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ))
        (eulerStep (squareField : ReactionField (Fin 1)) (-1) (fun _ => (2 : ℝ))) := by
  have hstep : eulerStep (squareField : ReactionField (Fin 1)) (-1) (fun _ => (2 : ℝ)) =
      (fun _ => (-2 : ℝ)) := by
    funext i
    fin_cases i
    norm_num [eulerStep, squareField_eval]
  rw [hstep]
  have h2 : gibbsTerm 1 2 = 5 * Real.exp (-2) := by norm_num [gibbsTerm]
  have hm2 : gibbsTerm 1 (-2) = 5 * Real.exp 2 := by norm_num [gibbsTerm]
  simp only [perelmanF, Fin.sum_univ_one]
  rw [h2, hm2]
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by norm_num)) (by norm_num)

/-- The weakened discrete statement (with an arbitrary real step `h`, no sign condition) is
false. -/
theorem antitone_discrete_fails_at_negative_step :
    ¬ (perelmanF (fun _ : Fin 1 => (1 : ℝ))
        (eulerStep (squareField : ReactionField (Fin 1)) (-1) (fun _ => (2 : ℝ))) ≤
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (2 : ℝ))) :=
  not_le.mpr counterexample_negative_step

/-! ## 4. Counterexample: a negative reaction cannot be admitted

The D2 `ReactionField` structure enforces `F.eval lam i ≥ 0` (`ReactionField.eval_nonneg`).
The next two statements show that this sign condition is essential: if arbitrary reaction
functions are allowed, both the discrete and the continuous monotonicity conclusions fail. -/

/-- The constant negative reaction `G ≡ -1` on a one-point state. -/
def negReaction : (Fin 1 → ℝ) → Fin 1 → ℝ := fun _ _ => -1

/-- The discrete trajectory `lam(n) = 1 - n`, which follows `G ≡ -1` with step `h = 1`. -/
def negTrajDisc : ℕ → Fin 1 → ℝ := fun n _ => (1 : ℝ) - n

/-- `negTrajDisc` satisfies the recurrence with `h = 1` and the negative reaction. -/
theorem negTrajDisc_step (n : ℕ) (i : Fin 1) :
    negTrajDisc (n + 1) i = negTrajDisc n i + (1 : ℝ) * negReaction (negTrajDisc n) i := by
  simp only [negTrajDisc, negReaction]
  push_cast
  ring

/-- **Counterexample.** The discrete monotonicity statement without the D2 sign condition on
the reaction is false: with `G ≡ -1`, `h = 1`, `c = 1`, the functional increases from
`2 e^{-1}` at `n = 0` to `1` at `n = 1`. -/
theorem weak_discrete_monotonicity_false :
    ¬ (∀ (G : (Fin 1 → ℝ) → Fin 1 → ℝ) (traj : ℕ → Fin 1 → ℝ) (h : ℝ),
        0 ≤ h → (∀ n i, traj (n + 1) i = traj n i + h * G (traj n) i) →
        ∀ n, perelmanF (fun _ : Fin 1 => (1 : ℝ)) (traj n) ≤
          perelmanF (fun _ : Fin 1 => (1 : ℝ)) (traj 0)) := by
  intro H
  have hstep : perelmanF (fun _ : Fin 1 => (1 : ℝ)) (negTrajDisc 1) ≤
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (negTrajDisc 0) :=
    H negReaction negTrajDisc 1 (by norm_num) (fun n i => negTrajDisc_step n i) 1
  have h1 : perelmanF (fun _ : Fin 1 => (1 : ℝ)) (negTrajDisc 1) = 1 := by
    norm_num [perelmanF, gibbsTerm, negTrajDisc, Fin.sum_univ_one]
  have h0 : perelmanF (fun _ : Fin 1 => (1 : ℝ)) (negTrajDisc 0) = 2 * Real.exp (-1) := by
    norm_num [perelmanF, gibbsTerm, negTrajDisc, Fin.sum_univ_one]
  rw [h1, h0] at hstep
  have hlt : 2 * Real.exp (-1) < 1 := two_exp_neg_one_lt_one
  linarith

/-- The continuous analogue of the D2 evolution relation with an arbitrary (possibly
negative) reaction, used only to state the counterexample below. -/
structure NoSignEvolution (G : (Fin 1 → ℝ) → Fin 1 → ℝ) (T : ℝ) (traj : ℝ → Fin 1 → ℝ) :
    Prop where
  /-- Componentwise continuity. -/
  continuous : ∀ i, ContinuousOn (fun t => traj t i) (Icc 0 T)
  /-- Componentwise right derivative given by the arbitrary reaction `G`. -/
  hasDeriv : ∀ i, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => traj s i) (G (traj t) i) (Ici t) t

/-- The continuous trajectory `lam(t) = 1 - t`, which follows `G ≡ -1` on `[0,1]`. -/
def negTrajCont : ℝ → Fin 1 → ℝ := fun t _ => (1 : ℝ) - t

/-- Derivative of `negTrajCont` (any component). -/
theorem negTrajCont_hasDeriv (t : ℝ) :
    HasDerivWithinAt (fun s : ℝ => negTrajCont s 0) (-1) (Ici t) t := by
  have h : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  exact h.hasDerivWithinAt

/-- `negTrajCont` is an evolution relation with the negative reaction `G ≡ -1`. -/
theorem noSignEvolution_neg : NoSignEvolution negReaction 1 negTrajCont where
  continuous := fun _ => by
    show ContinuousOn (fun t : ℝ => (1 : ℝ) - t) (Icc 0 1)
    fun_prop
  hasDeriv := fun i t _ => by
    simpa [negReaction, negTrajCont] using negTrajCont_hasDeriv t

/-- **Counterexample.** Without the sign condition on the reaction, the continuous
monotonicity conclusion fails: along `lam(t) = 1 - t` with reaction `-1` and `c = 1`, the
functional increases from `2 e^{-1}` at `t = 0` to `1` at `t = 1`. -/
theorem negative_reaction_continuous_counterexample :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (negTrajCont 0) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (negTrajCont 1) := by
  have h0 : negTrajCont 0 = (fun _ : Fin 1 => (1 : ℝ)) := by
    funext i
    norm_num [negTrajCont]
  have h1 : negTrajCont 1 = (fun _ : Fin 1 => (0 : ℝ)) := by
    funext i
    norm_num [negTrajCont]
  rw [h0, h1]
  simp only [perelmanF, Fin.sum_univ_one]
  rw [gibbsTerm_one_values.1, gibbsTerm_one_values.2]
  exact two_exp_neg_one_lt_one

/-- The weakened continuous statement without the D2 sign condition on the reaction is
false. -/
theorem no_sign_continuous_monotonicity_false :
    ¬ (∀ (G : (Fin 1 → ℝ) → Fin 1 → ℝ) (traj : ℝ → Fin 1 → ℝ),
        NoSignEvolution G 1 traj →
        perelmanF (fun _ : Fin 1 => (1 : ℝ)) (traj 1) ≤
          perelmanF (fun _ : Fin 1 => (1 : ℝ)) (traj 0)) := by
  intro H
  have h := H negReaction negTrajCont noSignEvolution_neg
  exact absurd h (not_le.mpr negative_reaction_continuous_counterexample)

/-! ## 5. Necessity of the strict-decrease side conditions -/

/-- With step `h = 0` the Euler step is the identity, so strict decrease is impossible. -/
theorem zero_step_constant (F : ReactionField ι) (c : ι → ℝ) (lam : ι → ℝ) :
    perelmanF c (eulerStep F 0 lam) = perelmanF c lam := by
  simp [perelmanF, eulerStep]

/-- Consequently `0 < h` cannot be dropped from `perelmanF_step_lt`. -/
theorem strict_step_needs_pos_step (F : ReactionField ι) (c : ι → ℝ) (lam : ι → ℝ) :
    ¬ perelmanF c (eulerStep F 0 lam) < perelmanF c lam := by
  rw [zero_step_constant]
  exact lt_irrefl _

/-- The zero state is a fixed point of the canonical reaction field, so with
`F.eval (traj n) i = 0` the strict decrease fails even for `1 < c` and `0 < h`. -/
theorem strict_step_needs_pos_reaction :
    ¬ perelmanF (fun _ : Fin 1 => (2 : ℝ))
        (eulerStep (ReactionField.hamilton : ReactionField (Fin 1)) 1 (fun _ => (0 : ℝ))) <
      perelmanF (fun _ : Fin 1 => (2 : ℝ)) (fun _ => (0 : ℝ)) := by
  have h : eulerStep (ReactionField.hamilton : ReactionField (Fin 1)) 1
      (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
    funext i
    simp [eulerStep]
  rw [h]
  exact lt_irrefl _

/-! ## 6. Corrected theorem: `1 < c` is overstrong; `1 ≤ c` suffices

The derivative of `gibbsTerm 1` is `-((x - 1)²) e^{-x}`, which vanishes only at the isolated
point `x = 1`. Hence `gibbsTerm 1` is *strictly* antitone, and the hypothesis `1 < c` of
`gibbsTerm_strictAnti`, `gibbsTerm_step_lt` and `perelmanF_step_lt` can be weakened to
`1 ≤ c`. The corrected statements are proved below. -/

/-- The one-variable Gibbs term is strictly antitone already for `1 ≤ c`. -/
theorem gibbsTerm_strictAnti_of_one_le (c : ℝ) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c) := by
  rcases lt_or_eq_of_le hc with hlt | rfl
  · exact gibbsTerm_strictAnti c (le_of_lt hlt)
  · have hcont : Continuous (gibbsTerm 1) := by
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
      refine strictAntiOn_of_deriv_neg (convex_Iic (1 : ℝ)) hcont.continuousOn
        (fun x hx => ?_)
      rw [interior_Iic] at hx
      exact hneg x (ne_of_lt hx)
    have hright : StrictAntiOn (gibbsTerm 1) (Ici 1) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici (1 : ℝ)) hcont.continuousOn
        (fun x hx => ?_)
      rw [interior_Ici] at hx
      exact hneg x (ne_of_gt hx)
    intro x y hxy
    rcases le_or_gt y 1 with hy | hy
    · exact hleft (Set.mem_Iic.mpr (by linarith)) (Set.mem_Iic.mpr hy) hxy
    · by_cases hx1 : 1 ≤ x
      · exact hright (Set.mem_Ici.mpr hx1) (Set.mem_Ici.mpr (le_of_lt hy)) hxy
      · simp only [not_le] at hx1
        have h1 : gibbsTerm 1 1 < gibbsTerm 1 x :=
          hleft (a := x) (Set.mem_Iic.mpr (le_of_lt hx1)) (b := 1)
            (Set.mem_Iic.mpr (le_refl 1)) hx1
        have h2 : gibbsTerm 1 y < gibbsTerm 1 1 :=
          hright (a := 1) (Set.mem_Ici.mpr (le_refl 1)) (b := y)
            (Set.mem_Ici.mpr (le_of_lt hy)) hy
        exact h2.trans h1

/-- Corrected one-step strict inequality: `1 ≤ c` and `0 < u` suffice. -/
theorem gibbsTerm_step_lt_of_one_le {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  gibbsTerm_strictAnti_of_one_le c hc (lt_add_of_pos_right x hu)

/-- **Corrected theorem.** The strict-decrease theorem `perelmanF_step_lt` holds with the
weaker hypothesis `∀ i, 1 ≤ c i` in place of `∀ i, 1 < c i`. -/
theorem perelmanF_step_lt_of_one_le (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) := by
  unfold perelmanF
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [ev.step n j]
    exact gibbsTerm_step_le (hc j) (mul_nonneg (le_of_lt hh) (F.eval_nonneg (traj n) j))
  · rw [ev.step n i]
    exact gibbsTerm_step_lt_of_one_le (hc i) (mul_pos hh hi)

/-! ## 7. Sharpness of `perelmanF_nonneg` and a strict-decrease positive control -/

/-- The hypothesis `0 ≤ c i` of `perelmanF_nonneg` is necessary: at `c = -1` and `lam = 0`
the functional is `-1 < 0`. -/
theorem perelmanF_nonneg_sharp :
    perelmanF (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => (0 : ℝ)) < 0 := by
  norm_num [perelmanF, gibbsTerm, Fin.sum_univ_one]

/-- Concrete trajectory for the square reaction field: `lam(0) = 1` and explicit Euler steps
with `h = 1`. -/
def sqTraj : ℕ → Fin 1 → ℝ
  | 0 => fun _ => (1 : ℝ)
  | n + 1 => eulerStep (squareField : ReactionField (Fin 1)) 1 (sqTraj n)

/-- `sqTraj` solves the explicit-Euler recurrence for the square reaction field. -/
theorem sqTraj_evolution :
    DiscreteEvolution (squareField : ReactionField (Fin 1)) 1 sqTraj where
  step := fun _ _ => rfl

/-- **Positive control for the corrected theorem.** At `c = 1` (where the original
`perelmanF_step_lt` is inapplicable, since it needs `1 < c`) the corrected statement still
gives strict decrease. -/
theorem strict_step_positive_control :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sqTraj 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sqTraj 0) :=
  perelmanF_step_lt_of_one_le (squareField : ReactionField (Fin 1))
    (c := fun _ : Fin 1 => (1 : ℝ)) (fun _ => le_refl 1) (h := 1) (by norm_num)
    (traj := sqTraj) sqTraj_evolution (n := 0) (i := 0) (by simp [sqTraj, squareField_eval])

/-! ## 8. Non-vacuity of the statement-only approximation boundary -/

/-- The `PerelmanApproximation` structure of the promoted bridge is inhabited: take the
continuous family to be the finite counting-measure datum itself. This shows the conditional
transfer theorem `continuousPerelmanFMonotone_of_approximation` is not vacuous, while also
showing that this particular inhabitant carries no continuous content. -/
theorem perelmanApproximation_nonvacuous [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {T : ℝ} {traj : ℝ → ι → ℝ}
    (ev : EvolutionRelation F T traj) :
    Nonempty (PerelmanApproximation (X := ι) (μ := (Measure.count : Measure ι))
      (fun t => finiteReactionEntropyData c (traj t)) F T traj c) :=
  ⟨{ hc := hc
     evolves := ev
     identification := fun t _ => finiteReactionEntropyData_F c (traj t) }⟩

/-- Applying the promoted conditional transfer to the inhabitant above, with the constant
reaction field and the nontrivial flow `t ↦ t`, produces a genuine conclusion. -/
theorem transfer_nonvacuous [MeasurableSpace (Fin 1)] [MeasurableSingletonClass (Fin 1)] :
    ContinuousPerelmanFMonotonicity
      (fun t => finiteReactionEntropyData (fun _ : Fin 1 => (1 : ℝ))
        ((fun s (_ : Fin 1) => s) t)) 1 :=
  continuousPerelmanFMonotone_of_approximation
    { hc := fun _ => le_refl 1
      evolves := GlobalReactionFlow.evolutionRelation (unitGlobalFlow (ι := Fin 1)) 1
      identification := fun t _ =>
        finiteReactionEntropyData_F (fun _ : Fin 1 => (1 : ℝ)) ((fun s (_ : Fin 1) => s) t) }

/-- The statement-only `FiniteMeshConvergence` predicate is inhabited: the mesh `1/(n+1)`
tends to `0` and the constant finite state converges to its limit. -/
theorem finiteMeshConvergence_nonvacuous :
    FiniteMeshConvergence (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (fun _ (_ : Fin 1) => (0 : ℝ)) (fun _ => (0 : ℝ)) :=
  ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    fun _ => tendsto_const_nhds⟩

/-- A nontrivial check of the promoted limit-passage theorem: the sequence
`state n = 1 - 1/(n+1)` increases to `1`, the finite comparison holds at every `n`, and the
conclusion passes to the limit. -/
theorem limit_passage_sanity :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) ≤
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1 - 1 / (((0 : ℕ) : ℝ) + 1)) := by
  apply perelmanF_limit_le_of_discrete (ι := Fin 1) (c := fun _ : Fin 1 => (1 : ℝ))
    (state := fun n (_ : Fin 1) => 1 - 1 / ((n : ℝ) + 1))
    (limit := fun _ : Fin 1 => (1 : ℝ))
  · intro n
    have hle : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h := gibbsTerm_antitone 1 le_rfl hle
    simpa [perelmanF, Fin.sum_univ_one] using h
  · exact tendsto_pi_nhds.mpr (fun _ => by
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h1.sub h2)

/-! ## 9. Certificate and entropy-interface re-checks -/

/-- The D3 `AntitoneCertificate` packaged by the cluster has the advertised lower bound `0`. -/
theorem certificate_lower_bound_zero (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    (perelmanAntitoneCertificate F hc ev).lowerBound = 0 := rfl

/-- The D3 certificate consequence (comparison) re-checked in `D4Audit`. -/
theorem audit_certificate_compare (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj)
    {a b : {t : ℝ // t ∈ Icc 0 T}} (hab : a ≤ b) :
    perelmanF c (traj b.1) ≤ perelmanF c (traj a.1) :=
  perelmanF_certificate_compare F hc ev hab

/-- The D3 `ContinuousAntitoneCertificate` consequence re-checked in `D4Audit`. -/
theorem audit_continuous_certificate [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {F : ReactionField ι} {traj : ℝ → ι → ℝ} (G : GlobalReactionFlow F traj)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    (finiteReactionEntropyData c (traj t)).F ≤ (finiteReactionEntropyData c (traj 0)).F :=
  continuousPerelmanCertificate_le_initial G hc ht

/-- The finite entropy datum's `F` really is the finite Perelman sum, re-checked. -/
theorem audit_finiteReactionEntropyData_F [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (c lam : ι → ℝ) :
    EntropyData.F (finiteReactionEntropyData c lam) = perelmanF c lam :=
  finiteReactionEntropyData_F c lam

/-! ## 10. Axiom audit -/

#print axioms audit_perelmanF_antitone
#print axioms audit_perelmanF_antitone_discrete
#print axioms audit_hasDerivWithinAt_perelmanF
#print axioms audit_two_sided_monotonicity
#print axioms nonvacuity_main_theorem
#print axioms nonvacuity_main_theorem_strict
#print axioms two_exp_neg_one_lt_one
#print axioms gibbsTerm_one_values
#print axioms dissipation_sanity
#print axioms three_exp_neg_one_lt_nine_exp_neg_two
#print axioms gibbsTerm_half_one_lt_two
#print axioms counterexample_discrete_c_half
#print axioms antitone_discrete_fails_at_c_half
#print axioms counterexample_continuous_c_half
#print axioms counterexample_continuous_c_half_is_evolution
#print axioms antitone_fails_at_c_half
#print axioms counterexample_negative_step
#print axioms antitone_discrete_fails_at_negative_step
#print axioms negReaction
#print axioms negTrajDisc
#print axioms negTrajDisc_step
#print axioms weak_discrete_monotonicity_false
#print axioms NoSignEvolution
#print axioms negTrajCont
#print axioms negTrajCont_hasDeriv
#print axioms noSignEvolution_neg
#print axioms negative_reaction_continuous_counterexample
#print axioms no_sign_continuous_monotonicity_false
#print axioms zero_step_constant
#print axioms strict_step_needs_pos_step
#print axioms strict_step_needs_pos_reaction
#print axioms gibbsTerm_strictAnti_of_one_le
#print axioms gibbsTerm_step_lt_of_one_le
#print axioms perelmanF_step_lt_of_one_le
#print axioms perelmanF_nonneg_sharp
#print axioms sqTraj
#print axioms sqTraj_evolution
#print axioms strict_step_positive_control
#print axioms perelmanApproximation_nonvacuous
#print axioms transfer_nonvacuous
#print axioms finiteMeshConvergence_nonvacuous
#print axioms limit_passage_sanity
#print axioms certificate_lower_bound_zero
#print axioms audit_certificate_compare
#print axioms audit_continuous_certificate
#print axioms audit_finiteReactionEntropyData_F

/-! ### Promoted declarations, independently re-printed -/

#print axioms Poincare.Longrun.Evolution.perelmanF_antitone
#print axioms Poincare.Longrun.Evolution.perelmanF_antitone_discrete
#print axioms Poincare.Longrun.Evolution.perelmanF_step_lt
#print axioms Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#print axioms Poincare.Longrun.Evolution.gibbsTerm_step_lt
#print axioms Poincare.Longrun.Evolution.perelmanF_nonneg
#print axioms Poincare.Longrun.Evolution.squareTraj_counterexample
#print axioms Poincare.Longrun.Evolution.continuousPerelmanCertificate
#print axioms Poincare.Longrun.Evolution.perelmanF_limit_le_of_discrete
#print axioms Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation
#print axioms Poincare.Longrun.Evolution.perelmanF_monotone_of_tensorBridge
#print axioms Poincare.Longrun.Evolution.PerelmanEvolutionBoundary

end D4Audit
