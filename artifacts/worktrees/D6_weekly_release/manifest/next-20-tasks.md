# Next 20 queued builder tasks

Every task is a builder task with compile-first acceptance. Tasks are ordered by dependency depth, not priority; the integrator may run independent tasks in parallel. A task that cannot prove its objective must deliver an explicit-hypothesis interface plus a checked toy theorem and a BLOCKED result card.

Count: **20** builder tasks + 1 verifier task.

## 1. `D7-riemann-curvature-tensor` — Local Riemann curvature tensor from an abstract connection

**Objective.** Define a bundled Riemann curvature tensor for the D2 AbstractConnection/CovariantDerivative layer, prove the algebraic symmetries (skew in the first pair, Bianchi), and connect it to Probe.CurvatureTensor and Poincare.CurvatureAlgebra.CurvatureOperator. Do not claim a manifold-level tensor until U4/U5 are discharged.

- stage/lane: `D7` / `builder`
- motivation blockers: `U1`
- deliverables: `Poincare/Longrun/Geometry/CurvatureTensor.lean`, `bridge theorems to Probe.CurvatureTensor and Poincare.CurvatureAlgebra`
- depends on: `D6-weekly-release`
- risk: Mathlib has no manifold Riemann tensor; keep the construction algebraic with explicit connection hypotheses.
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `Poincare.Longrun.Geometry.RiemannCurvatureTensor` is a def with kernel-checked skew/Bianchi
  - bridge theorem `ricci_eq_probe_ricci` checked on the abstract model

## 2. `D7-ricci-scalar-curvature` — Ricci and scalar curvature from the local curvature tensor

**Objective.** Derive Ricci and scalar curvature as traces of the D7 Riemann tensor and prove consistency with Poincare.CurvatureAlgebra (ricci_add/smul, scalarCurvature_add/smul, basis trace) and with Perelman.IsScalarCurvature / ScalarCurvatureData.

- stage/lane: `D7` / `builder`
- motivation blockers: `U2`
- deliverables: `Poincare/Longrun/Geometry/RicciScalar.lean`, `consistency theorems with Poincare.CurvatureAlgebra and Perelman.ScalarCurvatureData`
- depends on: `D7-riemann-curvature-tensor`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `ricciTensor`, `scalarCurvature` defined and the basis-trace formula proved

## 3. `D7-geodesic-exponential` — Geodesic flow and exponential map interface

**Objective.** Define geodesics as autoparallel curves for the D7 connection, define the exponential map on a star-shaped domain with explicit ODE-solution hypotheses, and prove the toy linear-connection case. State parallel transport as an explicit Prop with a checked toy instance.

- stage/lane: `D7` / `builder`
- motivation blockers: `U3`
- deliverables: `Poincare/Longrun/Geometry/Geodesic.lean`
- depends on: `D6-weekly-release`
- risk: Mathlib lacks geodesic flow; existence of geodesics must remain an explicit hypothesis.
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - toy flat-connection geodesic/exponential lemmas checked

## 4. `D7-levi-civita-smoothness` — Levi-Civita existence and C^k smoothness interface

**Objective.** Discharge the D2 blocked Prop LeviCivitaExistenceStatement under explicit invariant-metric and smoothness hypotheses, prove the germ-vs-1-jet lemma (U5) that the covariant derivative only depends on the germ, and connect to mathlib's CovariantDerivative API.

- stage/lane: `D7` / `builder`
- motivation blockers: `U4`, `U5`, `I1`
- deliverables: `Poincare/Longrun/Geometry/LeviCivitaExistence.lean`
- depends on: `D7-riemann-curvature-tensor`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `leviCivitaExistence_of_invariantMetric` checked under explicit hypotheses
  - germ-dependence lemma checked

## 5. `D7-orientability-volume-form` — Manifold orientability and Riemannian volume form

**Objective.** Define orientability for the D3 CompactThreeManifold interface, construct a local Riemannian volume density/measure from a metric in a chart, prove Perelman.RiemannianVolumePredicate for the construction, and instantiate the surgery LedgerPredicates `Orientable` parameter.

- stage/lane: `D7` / `builder`
- motivation blockers: `U7`, `U11`
- deliverables: `Poincare/Longrun/Geometry/VolumeForm.lean`, `Poincare/Longrun/Topology/Orientability.lean`
- depends on: `D7-ricci-scalar-curvature`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `Orientable` is a definition, not a parameter, with a checked equivalence to the D3 parameter
  - `riemannianVolumeDensity` construction satisfies Perelman.RiemannianVolumePredicate

## 6. `D7-divergence-ibp` — Divergence theorem and weighted integration by parts on a chart domain

**Objective.** Prove a chart-domain divergence theorem with explicit boundary regularity hypotheses and use it to discharge D3's WeightedIBPStatement for compactly supported weights. Every analytic input (smoothness, integrability, boundary) must be an explicit hypothesis.

- stage/lane: `D7` / `builder`
- motivation blockers: `U7`, `I4`
- deliverables: `Poincare/Longrun/Geometry/DivergenceTheorem.lean`, `Poincare/Longrun/Entropy/WeightedIBP.lean`
- depends on: `D7-orientability-volume-form`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `weightedIBP_of_boundaryHypotheses` checked, with the D3 statement as corollary

## 7. `D7-bochner-formula` — Bochner formula for the weighted Laplacian

**Objective.** Formalize the Bochner identity for the D7 connection/curvature/volume package and discharge D3's BochnerStatement under explicit smoothness and completeness hypotheses; add a non-vacuity check on the flat torus/round-sphere toy models if available in the local algebra.

- stage/lane: `D7` / `builder`
- motivation blockers: `U7`, `I4`
- deliverables: `Poincare/Longrun/Geometry/Bochner.lean`, `Poincare/Longrun/Entropy/BochnerBridge.lean`
- depends on: `D7-divergence-ibp`, `D7-ricci-scalar-curvature`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `bochner_identity` checked under explicit hypotheses
  - non-vacuity toy instance checked

## 8. `D7-conjugate-heat-interface` — Conjugate heat equation operator and F-derivative identity

**Objective.** Define the conjugate heat operator for the D3 entropy data, prove the formal adjoint identity and the FDerivativeStatement under explicit differentiability/integrability hypotheses, and provide a discrete analogue on the D2 heat grid.

- stage/lane: `D7` / `builder`
- motivation blockers: `U6`, `I4`
- deliverables: `Poincare/Longrun/Entropy/ConjugateHeat.lean`
- depends on: `D7-divergence-ibp`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `FDerivativeStatement` proved under named hypotheses
  - discrete conjugate-heat analogue checked

## 9. `D7-heat-kernel-existence` — Heat kernel / conjugate heat kernel existence interface

**Objective.** State the conjugate heat kernel existence and unit-mass property as an explicit structure with all analytic hypotheses, prove its algebraic consequences (mass evolution, symmetry), and instantiate it on the finite heat grid.

- stage/lane: `D7` / `builder`
- motivation blockers: `U6`, `I5`
- deliverables: `Poincare/Longrun/Entropy/HeatKernel.lean`
- depends on: `D7-conjugate-heat-interface`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `ConjugateHeatKernel` structure with non-vacuous finite-grid instance
  - mass-conservation and symmetry lemmas checked

## 10. `D7-discrete-continuous-limit` — Discrete-to-continuous limit for the heat maximum principle

**Objective.** Strengthen the D2 PDE cluster: define the mesh refinement relation, prove the discrete maximum principle is preserved under refinement, and state/prove FiniteMeshConvergence under explicit stability and consistency hypotheses; connect to ContinuousHeatMaximumPrincipleInterface.

- stage/lane: `D7` / `builder`
- motivation blockers: `I2`, `I7`
- deliverables: `Poincare/Longrun/PDE/MeshConvergence.lean`
- depends on: `D7-heat-kernel-existence`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `finiteMeshConvergence_of_stability` checked under explicit hypotheses
  - continuous interface recovered as a corollary

## 11. `D7-hamilton-short-time` — Hamilton short-time existence interface

**Objective.** Model the space of Riemannian metrics on a compact 3-manifold (or a faithful finite-dimensional slice) and state Hamilton/DeTurck short-time existence with explicit parabolicity hypotheses; prove the linearized toy equation and non-vacuity checks.

- stage/lane: `D7` / `builder`
- motivation blockers: `U8`
- deliverables: `Poincare/Longrun/RicciFlow/ShortTime.lean`
- depends on: `D7-ricci-scalar-curvature`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `hamiltonShortTimeExistence` structure with all hypotheses explicit
  - linearized toy existence theorem checked

## 12. `D7-tensor-laplacian` — Tensor Laplacian and curvature evolution

**Objective.** Define the tensor Laplacian for the D7 tensor package and formalize the reaction-diffusion curvature evolution equation, discharging the D2 TensorRicciFlowODEBridge DiffusionVanishes hypothesis in the presence of an explicit spatial Laplacian; keep the bridge inhabitant explicit.

- stage/lane: `D7` / `builder`
- motivation blockers: `U10`, `I3`, `I7`
- deliverables: `Poincare/Longrun/RicciFlow/TensorLaplacian.lean`, `Poincare/Longrun/CurvatureODE/TensorBridge.lean`
- depends on: `D7-hamilton-short-time`, `D7-bochner-formula`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `tensorLaplacian` defined; `tensorRicciFlowODEBridge_of_laplacian` checked
  - no axiom introduced for the bridge

## 13. `D7-reduced-length-volume` — Reduced length, reduced volume and their monotonicity interface

**Objective.** Define the reduced length functional on a path-space model and reduced volume, prove toy monotonicity and a non-vacuity instance, and state minimizer existence/Jacobian comparison as explicit structures (Perelman step P-REDUCED-VOL).

- stage/lane: `D7` / `builder`
- motivation blockers: `U9`, `I5`
- deliverables: `Poincare/Longrun/RicciFlow/ReducedLength.lean`
- depends on: `D7-hamilton-short-time`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `reducedLength`/`reducedVolume` defined; toy monotonicity checked
  - minimizer existence is an explicit structure, not an axiom

## 14. `D7-kappa-noncollapsing-conditional` — Conditional kappa-noncollapsing from entropy monotonicity

**Objective.** Prove K1/K3 as conditional theorems: entropy monotonicity (D7 interfaces) plus a ball-volume comparison hypothesis imply the D3 KappaNoncollapsingCertificate; prove the K1<->K2 equivalence is reused, and add non-vacuity checks.

- stage/lane: `D7` / `builder`
- motivation blockers: `I5`
- deliverables: `Poincare/Longrun/Topology/NoncollapsingConditional.lean`
- depends on: `D7-reduced-length-volume`, `D7-perelman-conditional-monotonicity`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `kappaNoncollapsing_of_entropy_and_volumeComparison` checked
  - hypotheses appear explicitly in the theorem signature

## 15. `D7-gh-compactness` — Pointed Gromov-Hausdorff compactness interface

**Objective.** Define pointed Gromov-Hausdorff convergence for the D3 CompactThreeManifold setting, prove metric-space toy compactness lemmas, and state Cheeger-Gromov compactness as an explicit structure with all hypotheses.

- stage/lane: `D7` / `builder`
- motivation blockers: `U9`, `I5`
- deliverables: `Poincare/Longrun/Topology/GromovHausdorff.lean`
- depends on: `D7-kappa-noncollapsing-conditional`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - toy GH-convergence lemmas checked
  - Cheeger-Gromov stated as an explicit structure

## 16. `D7-canonical-neighborhood` — Canonical neighborhood theorem interface

**Objective.** Formalize the model geometries (round sphere, round cylinder) as explicit structures and state the canonical neighborhood theorem as an explicit structure over the D7 GH/curvature interfaces; prove its conditional consequences and non-vacuity on the round sphere model.

- stage/lane: `D7` / `builder`
- motivation blockers: `I5`
- deliverables: `Poincare/Longrun/Topology/CanonicalNeighborhood.lean`
- depends on: `D7-gh-compactness`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - model-geometry structures non-vacuous
  - conditional consequences checked

## 17. `D7-surgery-neck-extinction` — Conditional neck analysis and finite extinction

**Objective.** Discharge the conditional consequences of D3 NeckAnalysis and ExtinctionTheorem: from explicit high-curvature/neck and complexity-decrease hypotheses, prove admissible surgery, preservation of the target, finite extinction and terminal sphere; connect to extincts_and_target.

- stage/lane: `D7` / `builder`
- motivation blockers: `I6`, `U9`
- deliverables: `Poincare/Longrun/Surgery/NeckConditional.lean`, `Poincare/Longrun/Surgery/ExtinctionConditional.lean`
- depends on: `D7-canonical-neighborhood`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `neckAnalysis_of_highCurvature` and `extincts_and_target_of_complexity` checked
  - no geometric input asserted as an axiom

## 18. `D7-sphere-recognition` — Sphere recognition: S^3 simple connectivity and pi_1 triviality

**Objective.** Formalize the S1-S5 sphere-recognition statements locally: prove SimplyConnectedSpace S^3 (or the pi_1-trivial equivalent) using the available mathlib topology/homotopy API if possible, otherwise reduce to named explicit hypotheses and prove the equivalences between S1-S5.

- stage/lane: `D7` / `builder`
- motivation blockers: `I5`
- deliverables: `Poincare/Longrun/Topology/SphereRecognition.lean`
- depends on: `D7-canonical-neighborhood`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - S1-S5 equivalence chain checked
  - any unconditional result clearly separated from hypotheses

## 19. `D7-evolution-sharp-restatement` — Promote the D4 sharp-hypothesis corrections upstream

**Objective.** Restate perelmanF_step_lt, gibbsTerm_strictAnti and gibbsTerm_step_lt with the sharp hypothesis 1 <= c in Poincare.Longrun.Evolution, keep deprecated aliases for the old names, and re-run the D4 counterexample audit against the restated cluster.

- stage/lane: `D7` / `builder`
- motivation blockers: `A1`
- deliverables: `Poincare/Longrun/Evolution/Gibbs.lean (restated)`, `Audit/PromotedEvolutionAudit.lean (re-run)`
- depends on: `D6-weekly-release`
- risk: Changing promoted theorem statements must keep the release build green and re-run the adversarial audit.
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - old names still resolve as deprecated aliases
  - D4Audit positive control still passes

## 20. `D7-perelman-conditional-monotonicity` — Conditional F/W/mu monotonicity assembly

**Objective.** Assemble the conditional Perelman monotonicity chain: from FDerivativeStatement + WeightedIBPStatement + BochnerStatement + integrability and heat-kernel hypotheses, prove Perelman.FMonotonicity; then W- and mu-monotonicity from the conjugate heat kernel and reduced volume interfaces. Every hypothesis explicit; non-vacuity checks mandatory.

- stage/lane: `D7` / `builder`
- motivation blockers: `U12`, `I8`
- deliverables: `Poincare/Longrun/Entropy/FMonotonicityConditional.lean`, `Poincare/Longrun/Entropy/WMuMonotonicityConditional.lean`
- depends on: `D7-bochner-formula`, `D7-heat-kernel-existence`, `D7-reduced-length-volume`
- risk: —
- acceptance:
  - at least one new `.lean` file compiles: `lake env lean <file>` exit 0
  - `#print axioms <main declaration>` ⊆ {propext, Classical.choice, Quot.sound}
  - no sorry/axiom/unsafe/native_decide/proof_wanted in new sources
  - result card with exact commands, exit codes and axiom output
  - unproved inputs stated as explicit hypotheses/Props, never as axioms
  - `perelmanFMonotone_of_analyticHypotheses` checked
  - `perelmanWMuMonotone_of_kernelHypotheses` checked
  - non-vacuity instances checked for each transfer theorem

## Verifier task `VERIFIER-D7-adversarial-audit-d2d3` — Adversarial counterexample audit of the D2 geometry and D3 entropy/kappa clusters

**Objective.** Extend the D4 audit method (A3) to D2/D3: search for false, vacuous or overstrong statements in the geometry, PDE, entropy, kappa and surgery clusters; prove sharp-hypothesis corrections.
