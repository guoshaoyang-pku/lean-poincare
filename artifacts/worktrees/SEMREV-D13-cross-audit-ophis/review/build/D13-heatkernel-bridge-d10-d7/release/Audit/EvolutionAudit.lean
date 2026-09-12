import Poincare.Longrun.Evolution

/-!
# D4-evolution-theorem — independent `#print axioms` probe

This driver is intentionally **outside** the `Poincare/` library tree. It imports the
umbrella module `Poincare.Longrun.Evolution` and prints the axiom dependencies of every
principal declaration of the D4 cluster. Run:

```text
lake env lean Audit/EvolutionAudit.lean
```

Expected: every line is `depends on axioms: [propext, Classical.choice, Quot.sound]`; no
`sorryAx`, no project axiom.
-/

/-! ## Main theorem and its exact dissipation identity -/

#print axioms Poincare.Longrun.Evolution.perelmanF_antitone
#print axioms Poincare.Longrun.Evolution.perelmanF_antitone_discrete
#print axioms Poincare.Longrun.Evolution.hasDerivWithinAt_perelmanF
#print axioms Poincare.Longrun.Evolution.hasDerivAt_perelmanF
#print axioms Poincare.Longrun.Evolution.perelmanF_le_initial
#print axioms Poincare.Longrun.Evolution.perelmanF_eq_on_Icc_of_eq_at
#print axioms Poincare.Longrun.Evolution.perelmanF_step_lt
#print axioms Poincare.Longrun.Evolution.two_sided_monotonicity

/-! ## The finite functional and its D3 `EntropyData` instance -/

#print axioms Poincare.Longrun.Evolution.perelmanF
#print axioms Poincare.Longrun.Evolution.perelmanF_nonneg
#print axioms Poincare.Longrun.Evolution.perelmanF_zero
#print axioms Poincare.Longrun.Evolution.continuous_perelmanF
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_F
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_conj
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_FDissipation
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_W
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_F_antitone
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_F_antitone_discrete

/-! ## The one-variable Gibbs engine -/

#print axioms Poincare.Longrun.Evolution.gibbsTerm
#print axioms Poincare.Longrun.Evolution.gibbsTerm_hasDerivAt
#print axioms Poincare.Longrun.Evolution.gibbsTerm_antitone
#print axioms Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#print axioms Poincare.Longrun.Evolution.gibbsTerm_comp
#print axioms Poincare.Longrun.Evolution.gibbsTerm_comp_hasDerivAt
#print axioms Poincare.Longrun.Evolution.gibbsTerm_nonneg
#print axioms Poincare.Longrun.Evolution.gibbsTerm_step_le
#print axioms Poincare.Longrun.Evolution.gibbsTerm_step_lt
#print axioms Poincare.Longrun.Evolution.gibbsTerm_deriv_at_one

/-! ## D3 certificate consumption -/

#print axioms Poincare.Longrun.Evolution.perelmanAntitoneCertificate
#print axioms Poincare.Longrun.Evolution.perelmanF_certificate_compare
#print axioms Poincare.Longrun.Evolution.perelmanF_certificate_lower
#print axioms Poincare.Longrun.Evolution.perelmanAntitoneCertificate_discrete
#print axioms Poincare.Longrun.Evolution.perelmanF_certificate_compare_discrete
#print axioms Poincare.Longrun.Evolution.continuousPerelmanCertificate
#print axioms Poincare.Longrun.Evolution.continuousPerelmanCertificate_antitoneOn
#print axioms Poincare.Longrun.Evolution.continuousPerelmanCertificate_le_initial

/-! ## Global flows and non-vacuity -/

#print axioms Poincare.Longrun.Evolution.GlobalReactionFlow
#print axioms Poincare.Longrun.Evolution.GlobalReactionFlow.evolutionRelation
#print axioms Poincare.Longrun.Evolution.unitReactionField
#print axioms Poincare.Longrun.Evolution.unitReactionField_eval
#print axioms Poincare.Longrun.Evolution.unitGlobalFlow
#print axioms Poincare.Longrun.Evolution.zeroGlobalFlow
#print axioms Poincare.Longrun.Evolution.continuousPerelmanCertificate_nonvacuous
#print axioms Poincare.Longrun.Evolution.unitDiscreteEvolution
#print axioms Poincare.Longrun.Evolution.perelmanAntitoneCertificate_discrete_nonvacuous

/-! ## Counterexample / sign-convention audit -/

#print axioms Poincare.Longrun.Evolution.squareField
#print axioms Poincare.Longrun.Evolution.squareField_eval
#print axioms Poincare.Longrun.Evolution.eulerStep_squareField_one
#print axioms Poincare.Longrun.Evolution.exp_neg_one_lt_four_exp_neg_two
#print axioms Poincare.Longrun.Evolution.perelmanF_step_increases_of_c_zero
#print axioms Poincare.Longrun.Evolution.perelmanF_step_increases_of_negative_step
#print axioms Poincare.Longrun.Evolution.perelmanF_dissipation_pos_at_c_zero
#print axioms Poincare.Longrun.Evolution.squareTraj
#print axioms Poincare.Longrun.Evolution.squareTraj_evolution
#print axioms Poincare.Longrun.Evolution.squareTraj_counterexample
#print axioms Poincare.Longrun.Evolution.gibbsTerm_deriv_at_one_zero
#print axioms Poincare.Longrun.Evolution.gibbsTerm_one_two_lt
#print axioms Poincare.Longrun.Evolution.perelmanF_one_two_le

/-! ## Approximation boundary and conditional transfer -/

#print axioms Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity
#print axioms Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman
#print axioms Poincare.Longrun.Evolution.FiniteMeshConvergence
#print axioms Poincare.Longrun.Evolution.PerelmanApproximation
#print axioms Poincare.Longrun.Evolution.tendsto_perelmanF
#print axioms Poincare.Longrun.Evolution.perelmanF_limit_le_of_discrete
#print axioms Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation
#print axioms Poincare.Longrun.Evolution.perelmanF_monotone_of_tensorBridge
#print axioms Poincare.Longrun.Evolution.PerelmanEvolutionBoundary
