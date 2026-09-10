# Theorem / dependency ledger — `week-1-2026-09-09`

Generated `2026-09-09T04:14:39.611927+00:00` from accepted D5 inputs plus the D6 kernel audit.

## Summary

| metric | value |
|---|---|
| program_steps | 11 |
| program_steps_blocked | 4 |
| program_steps_planned | 7 |
| program_steps_proved | 0 |
| interface_nodes | 43 |
| interface_nodes_checked | 34 |
| interface_nodes_open | 9 |
| headline_checked_results | 18 |
| headline_partial_results | 0 |
| blocked_layer_entries | 46 |
| edges | 119 |
| kernel_declarations_audited | 1619 |
| kernel_theorems | 887 |
| card_claims_named | 193 |
| card_claims_resolved | 193 |
| ledger_declarations_referenced | 191 |
| ledger_declarations_unresolved | 0 |

## Perelman program steps (none proved)

| step | status | proved | dependencies | principal blockers |
|---|---|---|---|---|
| `P-F-MONO` | blocked | False | `iface.metric_flow_data`, `iface.scalar_curvature_data`, `iface.gradient_norm_sq`, `iface.perelman_F`, `iface.F_profile` | no formal backward heat equation or conjugate heat kernel in mathlib; integration by parts on a Riemannian manifold is not available; integrability and finiteness of perelmanF are not established; the scalar curvature is |
| `P-W-MONO` | blocked | False | `P-F-MONO`, `iface.perelman_W`, `iface.has_unit_mass`, `iface.W_profile` | all blockers of P-F-MONO; tau-differentiation and the Gaussian normalization (4 pi tau)^{-n/2} require a measure-theoretic change-of-variables argument |
| `P-MU-MONO` | blocked | False | `P-W-MONO`, `iface.perelman_mu`, `iface.has_unit_mass` | attainment of the infimum defining mu is not proved; the admissible class (unit mass) is a predicate without a constructed minimizer |
| `P-NLC` | blocked | False | `P-W-MONO`, `P-MU-MONO`, `iface.kappa_noncollapsing`, `iface.curvature_bounded_on`, `iface.volume_form_data` | reduced length and reduced volume are not formalized; the full Riemann curvature tensor norm is not available; only a scalar stand-in is used; comparison-geometry volume estimates for balls are not in mathlib |
| `P-REDUCED-VOL` | planned | False | `P-F-MONO`, `iface.metric_flow_data` | needs path spaces, minimizers of the reduced length functional, and a Jacobian comparison theory |
| `P-HARNACK` | planned | False | `P-W-MONO`, `P-REDUCED-VOL` | requires the conjugate heat kernel and a Li-Yau-type differential Harnack argument |
| `P-KAPPA-SOL` | planned | False | `P-NLC` | needs the full curvature operator, non-collapsing, and the classification of 3D ancient solutions; mathlib has no Riemann curvature tensor or Ricci flow ancient-solution theory |
| `P-CANON` | planned | False | `P-KAPPA-SOL`, `P-NLC` | pointed Gromov-Hausdorff convergence and compactness are not in mathlib; epsilon-close model geometries (round sphere, round cylinder) are not formalized |
| `P-LONG` | planned | False | `P-CANON`, `P-NLC` | needs collapsing theory, hyperbolic 3-manifold geometry and a compactness argument |
| `P-SURG` | planned | False | `P-CANON`, `P-LONG` | requires the surgery algorithm, canonical neighborhood input, a priori curvature estimates, and a discrete flow construction |
| `P-EXT` | planned | False | `P-SURG` | needs the topological classification of 3-manifolds produced by the surgery decomposition; the topological conclusion is out of scope for the D1 interface layer |

## Checked results (kernel-checked, with file + axiom cone)

### L-D1-CURVATURE-ALGEBRA — D1-mathlib-geometry-map

**Claim.** Finite-dimensional curvature-tensor algebra probe: skew-symmetry, Bianchi, Ricci trace and additivity are kernel-checked.

- status: **checked** (proved: True)
- declarations: `Probe.CurvatureTensor.antisymm`, `Probe.CurvatureTensor.bianchi`, `Probe.CurvatureTensor.endo`, `Probe.CurvatureTensor.ricci`, `Probe.CurvatureTensor.ricci_add_toy`, `Probe.CurvatureTensor.ricci_zero_toy`
- files: Probe/GeometryApi.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Probe only: mathlib has no Riemann curvature tensor (blocker U1).

### L-D1-LEVI-CIVITA-PROBE — D1-mathlib-geometry-map

**Claim.** Levi-Civita uniqueness and torsion antisymmetry toy probes are kernel-checked.

- status: **checked** (proved: True)
- declarations: `Probe.leviCivita_uniqueness_toy`, `Probe.leviCivita_isLeviCivita_toy`, `Probe.torsion_antisymm_toy`, `Probe.inner_self_nonneg_toy`
- files: Probe/GeometryApi.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: —

### L-D1-PDE-PROBE — D1-pde-api-map

**Claim.** Discrete heat-slab maximum-principle probe and affine heat-slab interface are kernel-checked; the continuous interface is statement-only.

- status: **checked** (proved: True)
- declarations: `Probe.PdeApi.strict_finite_grid_max_principle`, `Probe.PdeApi.strict_finite_grid_max_principle_max`, `Probe.PdeApi.heat_slab_nonpos_of_interface`, `Probe.PdeApi.heat_slab_zero_interface`, `Probe.PdeApi.heat_slab_affine_interface`, `Probe.PdeApi.HeatSlabMaximumPrincipleInterface`
- files: Probe/PdeApi.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: HeatSlabMaximumPrincipleInterface is an unproved Prop (blocker U6/I2).

### L-D1-PERELMAN-TOY — D1-perelman-ledger

**Claim.** Perelman F/W/mu interfaces are defined and the toy monotonicity lemmas are kernel-checked.

- status: **checked** (proved: True)
- declarations: `Perelman.toyF_mono`, `Perelman.toyW_nonneg`, `Perelman.perelmanMu_le`, `Perelman.hasMetricTimeDerivative_const`, `Perelman.satisfies_ricciFlow_const_zero`, `Perelman.riemannianVolumeDensity_nonneg`, `Perelman.FMonotonicity_iff_antitoneOn`, `Perelman.WMonotonicity_iff_antitoneOn`, `Perelman.CurvatureBoundedOn.mono`
- files: Ledger/DefinitionSmoke.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: The F/W/mu monotonicity structures are hypotheses, not proved theorems (blockers U12).

### L-D2-CURVATURE-IDENTITIES — D2-geometry-foundation

**Claim.** Abstract connection curvature identities: skew, Bianchi, cyclic decomposition, Ricci additivity, scalar additivity/scaling and the basis trace formula.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Geometry.AbstractConnection.curvature_skew`, `Poincare.Longrun.Geometry.AbstractConnection.curvature_bianchi`, `Poincare.Longrun.Geometry.AbstractConnection.curvature_cyclic_decomp`, `Poincare.CurvatureAlgebra.CurvatureOperator.ricci_add`, `Poincare.CurvatureAlgebra.CurvatureOperator.ricci_smul`, `Poincare.CurvatureAlgebra.CurvatureOperator.scalarCurvature_add`, `Poincare.CurvatureAlgebra.CurvatureOperator.scalarCurvature_smul`, `Poincare.Longrun.Geometry.MetricData.scalarCurvature_eq_sum_basis`, `Poincare.Longrun.Geometry.MetricData.form_raiseIndex`, `Poincare.Longrun.Geometry.curvatureForm_first_pair_skew`, `Poincare.Longrun.Geometry.curvatureForm_first_bianchi`
- files: Poincare/Longrun/Geometry/ConnectionAdapter.lean, Poincare/Longrun/Geometry/Contraction.lean, Poincare/Longrun/Geometry/MetricData.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound'), ('propext', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Algebraic identities over abstract data; not differential-geometric curvature of a manifold.

### L-D2-LEVI-CIVITA — D2-geometry-foundation

**Claim.** Levi-Civita uniqueness and metric-compatibility equivalence are kernel-checked; existence and covariant-derivative curvature are explicit unproved Props.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Geometry.leviCivita_nabla_unique`, `Poincare.Longrun.Geometry.meanConnection_isMetricCompatible_iff`, `Poincare.Longrun.Geometry.leviCivitaExistence_iff_nonempty`, `Poincare.Longrun.Geometry.mean_curvature_apply`, `Poincare.Longrun.Geometry.mean_endoRicci`, `Poincare.Longrun.Geometry.mean_ricci_comm`
- files: Poincare/Longrun/Geometry/ConnectionAdapter.lean, Poincare/Longrun/Geometry/LeviCivitaBlocked.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: LeviCivitaExistenceStatement and CovariantDerivativeCurvatureStatement are BLOCKED Props (blocker I1).

### L-D2-DISCRETE-MAX-PRINCIPLE — D2-pde-foundation

**Claim.** Discrete maximum principle on a finite heat grid: the evolution never exceeds the initial supremum and the discrete energy is non-increasing.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le`, `Poincare.Longrun.PDE.HeatGridEvolution.le_sup'_initial`, `Poincare.Longrun.PDE.HeatGridEvolution.succ_le`, `Poincare.Longrun.PDE.HeatGridEvolution.energy_nonincreasing`, `Poincare.Longrun.PDE.continuousHeatHypotheses_affine`
- files: Poincare/Longrun/PDE/ContinuousInterface.lean, Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean, Poincare/Longrun/PDE/Energy.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Finite-grid content only; ContinuousHeatMaximumPrincipleInterface is statement-only (blocker I2).

### L-D2-ODE-INVARIANT — D2-ricci-ode-cluster

**Claim.** The non-negative orthant is invariant under the finite-dimensional Hamilton reaction ODE (continuous and explicit-Euler discrete).

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.CurvatureODE.component_monotone`, `Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant`, `Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant_discrete`, `Poincare.Longrun.CurvatureODE.zero_orthant_invariant`
- files: Poincare/Longrun/CurvatureODE/Invariant.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: —

### L-D2-ODE-SCALAR-MONO — D2-ricci-ode-cluster

**Claim.** The scalar curvature functional of the finite-dimensional reaction ODE is monotone (continuous and discrete).

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.CurvatureODE.scalarFunctional_monotone`, `Poincare.Longrun.CurvatureODE.scalarOfState_monotone`, `Poincare.Longrun.CurvatureODE.scalarFunctional_monotone_discrete`, `Poincare.Longrun.CurvatureODE.scalarOfState_monotone_discrete`, `Poincare.Longrun.CurvatureODE.zero_scalar_monotone`, `Poincare.Longrun.CurvatureODE.scalarCurvature_monotone_of_bridge`
- files: Poincare/Longrun/CurvatureODE/Bridge.lean, Poincare/Longrun/CurvatureODE/Monotonicity.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: scalarCurvature_monotone_of_bridge is conditional on the uninhabited TensorRicciFlowODEBridge (blocker I3).

### L-D3-ENTROPY-CERTIFICATES — D3-entropy-interface

**Claim.** Entropy interface: F/W data, monotonicity and decay certificates, their composition and the discrete heat-energy certificate are kernel-checked; all analytic inputs are explicit hypotheses.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Entropy.EntropyData.F`, `Poincare.Longrun.Entropy.EntropyData.W`, `Poincare.Longrun.Entropy.EntropyData.FDissipation_nonneg`, `Poincare.Longrun.Entropy.EntropyData.F_mono_integrand`, `Poincare.Longrun.Entropy.EntropyData.conjugateWeight_pos`, `Poincare.Longrun.Entropy.EntropyData.τ_pos`, `Poincare.Longrun.Entropy.EntropyData.ρ_nonneg`, `Poincare.Longrun.Entropy.EntropyData.integrable_F`, `Poincare.Longrun.Entropy.EntropyData.integrable_W`, `Poincare.Longrun.Entropy.AntitoneCertificate.mono`, `Poincare.Longrun.Entropy.AntitoneCertificate.F_le_of_le`, `Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.antitoneOn`, `Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.dissipation_nonpos`, `Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.hasDerivAt_F`, `Poincare.Longrun.Entropy.MonotoneCertificate.mono`, `Poincare.Longrun.Entropy.LinearDecayCertificate.decay`, `Poincare.Longrun.Entropy.LinearDecayCertificate.rate_pos`, `Poincare.Longrun.Entropy.heatEnergy_le_initial`, `Poincare.Longrun.Entropy.heatEnergy_nonneg`, `Poincare.Longrun.Entropy.heatEnergyCertificate_zero`, `Poincare.Longrun.Entropy.finiteCurvatureDatum_F`, `Poincare.Longrun.Entropy.finiteCurvatureDatum_W`, `Poincare.Longrun.Entropy.continuousMonotoneCertificateOfBridge`, `Poincare.Longrun.Entropy.entropyRegularityBridge_zero`
- files: Poincare/Longrun/Entropy/Bridge.lean, Poincare/Longrun/Entropy/Certificate.lean, Poincare/Longrun/Entropy/DiscreteHeat.lean, Poincare/Longrun/Entropy/FiniteGeometry.lean, Poincare/Longrun/Entropy/Functional.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: No Perelman entropy monotonicity: FDerivativeStatement, WeightedIBPStatement, BochnerStatement, ConjugateMeasureEvolutionStatement and EntropyFunctionalRegularityStatement are unproved Props (blocker I4).

### L-D3-KAPPA-MANIFOLD — D3-kappa-ledger

**Claim.** Compact 3-manifold class yields the expected topological consequences (sigma-compact, paracompact, locally compact, second countable, finite chart cover).

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Topology.CompactThreeManifold.toSigmaCompactSpace`, `Poincare.Longrun.Topology.CompactThreeManifold.toParacompactSpace`, `Poincare.Longrun.Topology.CompactThreeManifold.toLocallyCompactSpace`, `Poincare.Longrun.Topology.CompactThreeManifold.toSecondCountableTopology`, `Poincare.Longrun.Topology.CompactThreeManifold.toTopologicalManifold`, `Poincare.Longrun.Topology.CompactThreeManifold.exists_finite_chart_cover`, `Poincare.Longrun.Topology.CompactThreeManifold.exists_mem_chart_source`
- files: Poincare/Longrun/Topology/CompactThreeManifold.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: —

### L-D3-KAPPA-ALGEBRA — D3-kappa-ledger

**Claim.** kappa-noncollapsing certificate algebra and its equivalence with the normalized-ball-volume lower bound are kernel-checked.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_pos`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_ne_zero`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.mono`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_unit_ball_lower`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.exists_uniform_unit_ball_lower_bound`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.apply`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.apply`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.nonneg`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.pos`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.mono`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.bddBelow_range`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.exists_lower_bound`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.add`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.smul`, `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.const_iff`, `Poincare.Longrun.Topology.normalizedBallVolume_nonneg`, `Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.unit_ball_lower`, `Poincare.Longrun.Topology.kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound`, `Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.toKappaNoncollapsingCertificate`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.toNormalizedBallVolumeLowerBound`, `Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.volume_ball_pos`, `Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.mono`
- files: Poincare/Longrun/Topology/Noncollapsing.lean, Poincare/Longrun/Topology/NormalizedVolume.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: The non-collapsing theorem itself (K1-K7) is statement-only (blocker I5).

### L-D3-SURGERY-INTERFACE — D3-surgery-ledger

**Claim.** Surgery ledger interface: datum/predicates/certificate constructors and chain composition preserve the ledger invariants.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Surgery.SurgeryCertificate.trivial`, `Poincare.Longrun.Surgery.SurgeryCertificate.ofHomeomorph`, `Poincare.Longrun.Surgery.SurgeryCertificate.ofHomotopyEquiv`, `Poincare.Longrun.Surgery.ChainCertificate.append`, `Poincare.Longrun.Surgery.ChainCertificate.preservation`, `Poincare.Longrun.Surgery.ChainCertificate.compact_preserved`, `Poincare.Longrun.Surgery.ChainCertificate.orientable_preserved`, `Poincare.Longrun.Surgery.ChainCertificate.simplyConnected_preserved`
- files: Poincare/Longrun/Surgery/Basic.lean, Poincare/Longrun/Surgery/Chain.lean
- axiom cones: [(), ('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: NeckAnalysis, ExtinctionTheorem and MissingInputs are statement-only (blocker I6); orientability is a parameter (U11).

### L-D3-SURGERY-TOY — D3-surgery-ledger

**Claim.** Toy extinction skeleton: the toy complexity relation strictly decreases and admits no infinite chain.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Surgery.toyRel_functional`, `Poincare.Longrun.Surgery.toyRel_lt`, `Poincare.Longrun.Surgery.toyRel_succ`, `Poincare.Longrun.Surgery.toyRel_not_refl`, `Poincare.Longrun.Surgery.toyRel_nonempty`, `Poincare.Longrun.Surgery.toyRel_odd_iff`, `Poincare.Longrun.Surgery.ToyChain.value`, `Poincare.Longrun.Surgery.ToyChain.le`, `Poincare.Longrun.Surgery.ToyChain.no_infinite`, `Poincare.Longrun.Surgery.ToyChain.reflTransGen`, `Poincare.Longrun.Surgery.toyCertificate`, `Poincare.Longrun.Surgery.toyChain321_preserves`, `Poincare.Longrun.Surgery.toyChain321_compact`, `Poincare.Longrun.Surgery.toy_extinction_skeleton`
- files: Poincare/Longrun/Surgery/Missing.lean, Poincare/Longrun/Surgery/Toy.lean
- axiom cones: [(), ('propext', 'Classical.choice', 'Quot.sound'), ('propext', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Toy relation only; it models the decreasing part of extinction, not a geometric neck surgery.

### L-D4-PERELMAN-F-ANTITONE — D4-evolution-theorem

**Claim.** Finite Gibbs-weighted functional perelmanF is antitone along the D2 evolution relation (continuous and discrete), with an explicit dissipation identity.

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Evolution.perelmanF_antitone`, `Poincare.Longrun.Evolution.perelmanF_antitone_discrete`, `Poincare.Longrun.Evolution.hasDerivWithinAt_perelmanF`
- files: Poincare/Longrun/Evolution/Continuous.lean, Poincare/Longrun/Evolution/Discrete.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: NOT Perelman F-monotonicity: finite sum, c is abstract data, FDissipation = 0, sign convention opposite to Perelman's F (blockers A2/I7).

### L-D4-EVOLUTION-CERTIFICATES — D4-evolution-theorem

**Claim.** D3 antitone certificates are instantiated for the evolution cluster (continuous and discrete).

- status: **checked** (proved: True)
- declarations: `Poincare.Longrun.Evolution.perelmanAntitoneCertificate`, `Poincare.Longrun.Evolution.perelmanAntitoneCertificate_discrete`, `Poincare.Longrun.Evolution.continuousPerelmanCertificate`, `Poincare.Longrun.Evolution.finiteReactionEntropyData_F`, `Poincare.Longrun.Evolution.perelmanF_monotone_of_tensorBridge`, `Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation`
- files: Poincare/Longrun/Evolution/Bridge.lean, Poincare/Longrun/Evolution/Continuous.lean, Poincare/Longrun/Evolution/Discrete.lean, Poincare/Longrun/Evolution/Functional.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Transfer theorems are conditional on uninhabited interfaces (blocker I8).

### L-D4-SHARP-CORRECTIONS — D4-counterexample-audit

**Claim.** Adversarial audit found no false statement; three promoted theorems have overstrong hypotheses and sharp-hypothesis replacements are kernel-checked.

- status: **checked** (proved: True)
- declarations: `D4Audit.gibbsTerm_strictAnti_of_one_le`, `D4Audit.gibbsTerm_step_lt_of_one_le`, `D4Audit.perelmanF_step_lt_of_one_le`
- files: Audit/CounterexampleAudit.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Blocker A1: upstream restatement recommended; corrected declarations live in D4Audit.

### L-D4-COUNTEREXAMPLES — D4-counterexample-audit

**Claim.** Counterexamples delimit the hypotheses of the D4 cluster and non-vacuity checks confirm the main theorem is not vacuous.

- status: **checked** (proved: True)
- declarations: `D4Audit.counterexample_continuous_c_half`, `D4Audit.counterexample_discrete_c_half`, `D4Audit.counterexample_negative_step`, `D4Audit.perelmanF_nonneg_sharp`, `D4Audit.nonvacuity_main_theorem`, `D4Audit.nonvacuity_main_theorem_strict`, `D4Audit.perelmanApproximation_nonvacuous`, `D4Audit.transfer_nonvacuous`, `D4Audit.finiteMeshConvergence_nonvacuous`, `D4Audit.dissipation_sanity`
- files: Audit/CounterexampleAudit.lean
- axiom cones: [('propext', 'Classical.choice', 'Quot.sound')]
- evidence: `logs/13_d6_decl_report.log`
- note: Audit scope covers the D4 evolution cluster only (blocker A3).

## Interface nodes

| node | type | status | declarations |
|---|---|---|---|
| `bg.smooth_manifold` | context | checked |  |
| `iface.metric_family` | definition | checked | `Perelman.MetricFamily` |
| `iface.ricci_tensor` | definition | checked | `Perelman.RicciTensor`, `Perelman.RicciFamily` |
| `iface.has_metric_time_derivative` | definition | checked | `Perelman.HasMetricTimeDerivative` |
| `iface.neg_two_ricci` | definition | checked | `Perelman.negTwoRicci` |
| `iface.metric_flow_data` | structure | interface | `Perelman.MetricFlowData` |
| `lemma.metric_flow_data_Icc_subset` | lemma | checked | `Perelman.MetricFlowData.Icc_subset` |
| `iface.gram_matrix` | definition | checked | `Perelman.gramMatrix` |
| `iface.riemannian_volume_density` | definition | checked | `Perelman.riemannianVolumeDensity` |
| `iface.riemannian_volume_predicate` | definition | checked | `Perelman.RiemannianVolumePredicate` |
| `iface.has_frame_volume_density` | definition | checked | `Perelman.HasFrameVolumeDensity` |
| `iface.volume_form_data` | structure | interface | `Perelman.VolumeFormData` |
| `iface.scalar_curvature_in_basis` | definition | checked | `Perelman.scalarCurvatureInBasis` |
| `iface.is_scalar_curvature` | definition | checked | `Perelman.IsScalarCurvature` |
| `iface.scalar_curvature_data` | structure | interface | `Perelman.ScalarCurvatureData` |
| `iface.perelman_F` | definition | checked | `Perelman.perelmanF` |
| `iface.perelman_W` | definition | checked | `Perelman.perelmanW` |
| `iface.has_unit_mass` | definition | checked | `Perelman.HasUnitMass` |
| `iface.perelman_mu` | definition | checked | `Perelman.perelmanMu` |
| `iface.F_profile` | definition | checked | `Perelman.FProfile` |
| `iface.W_profile` | definition | checked | `Perelman.WProfile` |
| `iface.directional_derivative` | definition | checked | `Perelman.directionalDerivative` |
| `iface.gradient_norm_sq` | definition | checked | `Perelman.gradientNormSqInBasis` |
| `iface.F_monotonicity` | structure | interface | `Perelman.FMonotonicity` |
| `iface.W_monotonicity` | structure | interface | `Perelman.WMonotonicity` |
| `iface.mu_monotonicity` | structure | interface | `Perelman.MuMonotonicity` |
| `iface.scalar_curvature_lower_bound` | structure | interface | `Perelman.ScalarCurvatureLowerBound` |
| `iface.ricci_lower_bound` | structure | interface | `Perelman.RicciLowerBound` |
| `iface.curvature_bounded_on` | definition | checked | `Perelman.CurvatureBoundedOn` |
| `iface.kappa_noncollapsing` | structure | interface | `Perelman.KappaNoncollapsing` |
| `toy.toy_F` | definition | checked | `Perelman.toyF` |
| `toy.toy_F_mono` | lemma | checked | `Perelman.toyF_mono` |
| `toy.toy_W` | definition | checked | `Perelman.toyW` |
| `toy.toy_W_nonneg` | lemma | checked | `Perelman.toyW_nonneg` |
| `toy.perelman_mu_le` | lemma | checked | `Perelman.perelmanMu_le` |
| `toy.has_metric_time_derivative_const` | lemma | checked | `Perelman.hasMetricTimeDerivative_const` |
| `toy.satisfies_ricci_flow_const_zero` | lemma | checked | `Perelman.satisfies_ricciFlow_const_zero` |
| `toy.constant_flow` | definition | checked | `Perelman.constantFlow` |
| `toy.volume_density_nonneg` | lemma | checked | `Perelman.riemannianVolumeDensity_nonneg` |
| `toy.volume_density_pos_of_posDef` | lemma | checked | `Perelman.riemannianVolumeDensity_pos_of_posDef` |
| `toy.monotonicity_apply` | lemma | checked | `Perelman.FMonotonicity.apply`, `Perelman.WMonotonicity.apply`, `Perelman.MuMonotonicity.apply` |
| `toy.monotonicity_iff` | lemma | checked | `Perelman.FMonotonicity_iff_antitoneOn`, `Perelman.WMonotonicity_iff_antitoneOn` |
| `toy.curvature_bounded_on_mono` | lemma | checked | `Perelman.CurvatureBoundedOn.mono` |

## Blocked / missing layer

| id | cluster | kind | statement | blockers |
|---|---|---|---|---|
| `BLK-LeviCivitaExistenceStatement` | D2-geometry-foundation | unproved-prop | abstract Levi-Civita existence is false without an invariant-metric hypothesis; smooth-manifold existence in mathlib is for CovariantDerivative, not this algebraic setting | I1 |
| `BLK-CovariantDerivativeCurvatureStatement` | D2-geometry-foundation | unproved-prop | mathlib has no CovariantDerivative.curvature (D1 card: #check_failure RiemannCurvatureTensor) | I1 |
| `BLK-CONTINUOUS-MAX-PRINCIPLE` | D2-pde-foundation | unproved-prop | pinned mathlib has no heat-equation theory, heat kernel, or parabolic PDE layer; the continuous implication cannot be proved here | I2, U6 |
| `BLK-ODE-1` | D2-ricci-ode-cluster | unproved-interface | Spatial Laplacian of the curvature evolution is not modeled (mathlib has no tensor Laplacian); exposed as the explicit DiffusionVanishes hypothesis of TensorRicciFlowODEBridge. | I3, U10 |
| `BLK-ODE-2` | D2-ricci-ode-cluster | unproved-interface | Manifold curvature API missing (CovariantDerivativeCurvatureStatement, geometry cluster); exposed as the explicit ManifoldCurvatureRealization conjunct of TensorRicciFlowODERealization. | I3, U10 |
| `BLK-ODE-3` | D2-ricci-ode-cluster | unproved-interface | No inhabitant of TensorRicciFlowODEBridge is constructed; the bridge is an explicit interface, never an axiom. | I3, U10 |
| `BLK-ENTROPY-1` | D3-entropy-interface | unproved-prop | FDerivativeStatement (differentiation under the integral sign / first variation of F) is an unproved Prop. | I4, U7 |
| `BLK-ENTROPY-2` | D3-entropy-interface | unproved-prop | WeightedIBPStatement and BochnerStatement are unproved Props; the pinned mathlib has no Riemannian geometry API (D1 card). | I4, U7 |
| `BLK-ENTROPY-3` | D3-entropy-interface | unproved-prop | ConjugateMeasureEvolutionStatement is an unproved Prop; the pinned mathlib has no heat-equation theory (D2 card). | I4, U7 |
| `BLK-ENTROPY-4` | D3-entropy-interface | unproved-prop | EntropyFunctionalRegularityStatement (C^1 regularity of the functional) is an unproved Prop. | I4, U7 |
| `BLK-ENTROPY-5` | D3-entropy-interface | unproved-prop | The one-sided bound fields (upper_le / lower_le) are explicit hypotheses, not derived. | I4, U7 |
| `BLK-ENTROPY-6` | D3-entropy-interface | unproved-prop | WeightedCalculus is abstract data; no smooth manifold or metric is constructed. | I4, U7 |
| `K1` | D3-kappa-ledger | missing-theorem | Perelman 2002 §4 Thm 4.1: normalized Ricci flow with |Rm| ≤ r^-2 on B(x,r) satisfies vol B(x,r) ≥ κ r^3 with κ = κ(g(0),T) > 0 | I5, U9 |
| `K2` | D3-kappa-ledger | missing-theorem | Normalized-volume form μ(B(x,r))/r^3 ≥ κ; equivalent to K1 by the checked interface equivalence | I5, U9 |
| `K3` | D3-kappa-ledger | missing-theorem | Entropy monotonicity (μ or W) plus normalization implies K1 | I5, U9 |
| `K4` | D3-kappa-ledger | missing-theorem | Reduced volume V~(τ) is non-increasing along the flow | I5, U9 |
| `K5` | D3-kappa-ledger | missing-theorem | Existence of the conjugate heat kernel (unit-mass measurable family) | I5, U9 |
| `K6` | D3-kappa-ledger | missing-theorem | κ-non-collapsing persists under surgery (possibly smaller κ) | I5, U9 |
| `K7` | D3-kappa-ledger | missing-theorem | High-curvature points of a 3D κ-solution are ε-close to model geometries | I5, U9 |
| `S1` | D3-kappa-ledger | missing-theorem | SimplyConnectedSpace 𝕊³ | I5, U9 |
| `S2` | D3-kappa-ledger | missing-theorem | ∀ x, Subsingleton (π₁ 𝕊³ x) | I5, U9 |
| `S3` | D3-kappa-ledger | missing-theorem | compact T2 ℝ³-charted simply connected M satisfies Nonempty (M ≃ₜ 𝕊³) | I5, U9 |
| `S4` | D3-kappa-ledger | missing-theorem | same with a diffeomorphism M ≃ₘ⟮𝓡3,𝓡3⟯ 𝕊³ | I5, U9 |
| `S5` | D3-kappa-ledger | missing-theorem | decidable recognition of M ≃ₜ 𝕊³ for compact 3-manifolds | I5, U9 |
| `GAP-RIEMANN-CURVATURE-TENSOR-FROM-A-CONNECTI` | D3-kappa-ledger | foundational-gap | Riemann curvature tensor from a connection | U1, U2, U7, U8, U9 |
| `GAP-RICCI-AND-SCALAR-CURVATURE` | D3-kappa-ledger | foundational-gap | Ricci and scalar curvature | U1, U2, U7, U8, U9 |
| `GAP-RIEMANNIAN-VOLUME-FORM-AND-MEASURE` | D3-kappa-ledger | foundational-gap | Riemannian volume form and measure | U1, U2, U7, U8, U9 |
| `GAP-DIVERGENCE-THEOREM-AND-INTEGRATION-BY-PA` | D3-kappa-ledger | foundational-gap | Divergence theorem and integration by parts on manifolds | U1, U2, U7, U8, U9 |
| `GAP-HAMILTON-SHORT-TIME-EXISTENCE-FOR-RICCI-` | D3-kappa-ledger | foundational-gap | Hamilton short-time existence for Ricci flow (DeTurck/Uhlenbeck) | U1, U2, U7, U8, U9 |
| `GAP-HEAT-EQUATION-CONJUGATE-HEAT-KERNEL-FUND` | D3-kappa-ledger | foundational-gap | Heat equation / conjugate heat kernel fundamental solution | U1, U2, U7, U8, U9 |
| `GAP-REDUCED-LENGTH-L-AND-ITS-MINIMIZERS-JACO` | D3-kappa-ledger | foundational-gap | Reduced length L and its minimizers; Jacobian comparison | U1, U2, U7, U8, U9 |
| `GAP-CHEEGER-GROMOV-POINTED-COMPACTNESS-GROMO` | D3-kappa-ledger | foundational-gap | Cheeger-Gromov pointed compactness; Gromov-Hausdorff convergence | U1, U2, U7, U8, U9 |
| `GAP-BRENDLE-SCHOEN-CLASSIFICATION-OF-3D-SOLU` | D3-kappa-ledger | foundational-gap | Brendle-Schoen classification of 3D κ-solutions | U1, U2, U7, U8, U9 |
| `BLK-NECK_ANALYSIS` | D3-surgery-ledger | missing-theorem | high-curvature region exists; canonical neighbourhood theorem yields a delta-neck; the neck is separating in the simply connected case; cut-and-cap surgery is admissible and realizes the datum | I6, U9 |
| `BLK-EXTINCTION_THEOREM` | D3-surgery-ledger | missing-theorem | strictly decreasing surgery complexity; finitely many surgeries; finite-time extinction; terminal manifold is the 3-sphere | I6, U9 |
| `BLK-D4-BOUNDARY-1` | D4-evolution-theorem | explicit-boundary | finite sum, not an integral over a manifold | I7, I8, A2 |
| `BLK-D4-BOUNDARY-2` | D4-evolution-theorem | explicit-boundary | c is abstract curvature-like data, not scalar curvature of a metric | I7, I8, A2 |
| `BLK-D4-BOUNDARY-3` | D4-evolution-theorem | explicit-boundary | no spatial Laplacian / Bochner dissipation (FDissipation = 0) | I7, I8, A2 |
| `BLK-D4-BOUNDARY-4` | D4-evolution-theorem | explicit-boundary | functional direction opposite to Perelman F | I7, I8, A2 |
| `BLK-D4-BOUNDARY-5` | D4-evolution-theorem | explicit-boundary | identification and mesh convergence are statement-only, no inhabitant | I7, I8, A2 |
| `BLK-D4-BOUNDARY-6` | D4-evolution-theorem | explicit-boundary | tensor bridge has no inhabitant (D2 card boundary) | I7, I8, A2 |
| `BLK-D4A-BOUNDARY-1` | D4-counterexample-audit | explicit-boundary | PerelmanApproximation is inhabited only by the trivial finite identification; no continuous content. | A2, A3 |
| `BLK-D4A-BOUNDARY-2` | D4-counterexample-audit | explicit-boundary | TensorRicciFlowODEBridge / PerelmanEvolutionBoundary have no inhabitant; transfer theorems are conditional. | A2, A3 |
| `BLK-D4A-BOUNDARY-3` | D4-counterexample-audit | explicit-boundary | FiniteRepresentsContinuousPerelman and FiniteMeshConvergence remain statement-only. | A2, A3 |
| `BLK-D4A-BOUNDARY-4` | D4-counterexample-audit | explicit-boundary | FDissipation = 0 for the finite datum; no spatial Laplacian/Bochner content. | A2, A3 |
| `BLK-D4A-BOUNDARY-5` | D4-counterexample-audit | explicit-boundary | The functional is nonincreasing, opposite to Perelman's F; the cluster explicitly disclaims Perelman's monotonicity theorem. | A2, A3 |

## Claim resolution

- card claims: 193 named, 193 resolved
- unresolved: none
- ledger declarations unresolved: none
