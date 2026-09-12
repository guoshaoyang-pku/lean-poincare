/-
D9-adversarial-audit-release — kernel axiom cones of every flagged declaration.

`#print axioms` is the kernel's own report of the axioms a declaration depends on.  This
file prints it for

* the ten largest-import-cone theorems selected by the audit (see `analyze_cones.py`);
* every declaration flagged by the assumption-inflation hunt, including the definitionally
  trivial interface projections and the "MISSING THEOREM" placeholders;
* the audit's own restatements in `Audit.D9.AssumptionAudit`.

Expected output: only `propext`, `Classical.choice`, `Quot.sound`, or nothing.  Any
occurrence of `sorryAx` or of an unapproved axiom is a FAIL of this audit.
-/
import ReleaseCheck

/-! ## §1. The ten largest-import-cone theorems -/

#print axioms D4Audit.gibbsTerm_strictAnti_of_one_le
#print axioms D4Audit.weak_discrete_monotonicity_false
#print axioms D4Audit.counterexample_continuous_c_half
#print axioms D4Audit.gibbsTerm_half_one_lt_two
#print axioms D4Audit.negTrajCont_hasDeriv
#print axioms D4Audit.counterexample_discrete_c_half
#print axioms D4Audit.negative_reaction_continuous_counterexample
#print axioms D4Audit.noSignEvolution_neg
#print axioms D4Audit.strict_step_positive_control
#print axioms D4Audit.negTrajDisc_step

/-! ## §1b. Max-cone tie group (22 human theorems tie at cone 10450): the hypothesis-carrying
members, i.e. the declarations for which hypothesis inflation is even possible.
Listed here so the axiom report covers the whole class, not just the tie-break top ten. -/

#print axioms D4Audit.perelmanF_step_lt_of_one_le
#print axioms D4Audit.NoSignEvolution.hasDeriv
#print axioms D4Audit.NoSignEvolution.continuous
#print axioms D4Audit.gibbsTerm_step_lt_of_one_le
#print axioms D4Audit.strict_step_needs_pos_step
#print axioms D4Audit.sqTraj_evolution

/-! ## §2. Promoted theorems with overstrong hypotheses -/

#print axioms Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#print axioms Poincare.Longrun.Evolution.gibbsTerm_step_lt
#print axioms Poincare.Longrun.Evolution.perelmanF_step_lt

/-! ## §3. Conditional transfers and certificate projections -/

#print axioms Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation
#print axioms Poincare.Longrun.Evolution.perelmanF_monotone_of_tensorBridge
#print axioms Poincare.Longrun.Entropy.continuousMonotoneCertificateOfBridge
#print axioms Poincare.Longrun.Entropy.AntitoneCertificate.F_le_of_le
#print axioms Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.antitoneOn
#print axioms Poincare.Longrun.Entropy.heatEnergy_le_initial
#print axioms Perelman.FMonotonicity.apply
#print axioms Perelman.WMonotonicity.apply
#print axioms Perelman.MuMonotonicity.apply
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.apply
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_pos
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.apply
#print axioms Poincare.Longrun.Surgery.SurgeryCertificate.simplyConnected
#print axioms Poincare.Longrun.Surgery.SurgeryCertificate.compact
#print axioms Poincare.Longrun.Surgery.SurgeryCertificate.orientable
#print axioms Poincare.Longrun.Surgery.NeckAnalysis.target_preserved_of_highCurvature
#print axioms Poincare.Longrun.Surgery.extincts_and_target

/-! ## §3b. The release-check marker (vacuously `True`) -/

#print axioms D5ReleaseCheck.release_check_compiles

/-! ## §4. "Missing theorem" and "BLOCKED" placeholders -/

#print axioms Poincare.Longrun.Topology.missingSphereRecognitionAlgorithm
#print axioms Poincare.Longrun.Topology.missingKappaPersistenceUnderSurgery
#print axioms Poincare.Longrun.Topology.missingCanonicalNeighborhoodTheorem
#print axioms Poincare.Longrun.Topology.missingKappaNoncollapsing
#print axioms Poincare.Longrun.Topology.stage6Target_of_sphereRecognition
#print axioms Poincare.Stage6.poincareConjectureTopologicalThree
#print axioms Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement
#print axioms Poincare.Longrun.Geometry.LeviCivitaData.isLeviCivita
#print axioms Poincare.RiemannAdapter.RiemannianCurvatureData.toCurvatureOperator

/-! ## §5. The audit's own restatements and triviality certificates

The `D9Audit.*` declarations live in `Audit.D9.AssumptionAudit`, whose own footer runs
`#print axioms` over every one of them.  That file is checked separately (its per-file log
is `release/Audit/D9/logs/assumption_audit.log`); importing it here would require a shared
`.olean` build that this audit deliberately does not add to the release's `.lake`. -/
