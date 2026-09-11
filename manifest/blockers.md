# Explicit blockers for the full Perelman proof

22 of the 29 D5 blockers remain open; P1 (stale queue) is corrected in manifest/queue.updated.json but promotion to the shared longrun/queue.json is pending a wider sandbox. D6 adds P4 (prompt/runtime worktree-name mismatch) and P5 (release-source delta). No blocker is a release-hygiene failure: every one is an upstream mathlib gap, an explicit unproved interface, or a documented boundary.

## Counts

- total: **32**
- open: **24**
- documented: **1**
- resolved_by_d6: **0**
- resolved_in_worktree: **1**
- known_environment_limit: **3**
- informational: **3**

## Blockers

| id | class | status | blocker | unblocked by |
|---|---|---|---|---|
| `U1` | upstream-mathlib-gap | open | Pinned mathlib has no Riemann curvature tensor; curvature-based evolution equations cannot use a mathlib object. | `D7-riemann-curvature-tensor` |
| `U2` | upstream-mathlib-gap | open | Pinned mathlib has no Ricci tensor or scalar curvature. | `D7-ricci-scalar-curvature` |
| `U3` | upstream-mathlib-gap | open | No geodesics, exponential map, or parallel transport in pinned mathlib. | `D7-geodesic-exponential` |
| `U4` | upstream-mathlib-gap | open | Levi-Civita connection smoothness (C^k) is not proved upstream; it must be a hypothesis. | `D7-levi-civita-smoothness` |
| `U5` | upstream-mathlib-gap | open | Covariant derivative is known to depend only on the germ, not the 1-jet, of a section; tensorial identities may need germ-level arguments. | `D7-levi-civita-smoothness` |
| `U6` | upstream-mathlib-gap | open | No heat-equation theory, heat kernel, or parabolic PDE layer; the continuous parabolic maximum principle cannot be proved and is a statement-only interface. | `D7-conjugate-heat-interface`, `D7-heat-kernel-existence` |
| `U7` | upstream-mathlib-gap | open | No Riemannian volume form, divergence theorem, integration by parts, or Bochner formula in the pinned mathlib. | `D7-divergence-ibp`, `D7-bochner-formula` |
| `U8` | upstream-mathlib-gap | open | No smooth manifold of Riemannian metrics and no Hamilton short-time existence theorem for Ricci flow. | `D7-hamilton-short-time` |
| `U9` | upstream-mathlib-gap | open | No reduced length/reduced volume, no pointed Gromov-Hausdorff compactness, no canonical-neighborhood theorem, no surgery machinery; Perelman steps P-REDUCED-VOL, P-HARNACK, P-KAPPA-SOL, P-CANON, P-LONG, P-SURG, P-EXT remain planned/blocked. | `D7-reduced-length-volume`, `D7-gh-compactness`, `D7-canonical-neighborhood`, `D7-surgery-neck-extinction` |
| `U10` | upstream-mathlib-gap | open | No tensor Laplacian: the spatial Laplacian of the curvature evolution is not modeled; exposed as the explicit DiffusionVanishes hypothesis. | `D7-tensor-laplacian` |
| `U11` | upstream-mathlib-gap | open | Pinned mathlib has no manifold orientability: `Orientable` is a parameter of the surgery LedgerPredicates, not a definition; a future contribution should define it and instantiate canonicalLedger. | `D7-orientability-volume-form` |
| `U12` | upstream-mathlib-gap | open | The four blocked Perelman steps P-F-MONO, P-W-MONO, P-MU-MONO and P-NLC are recorded as hypothesis structures only: no backward/conjugate heat equation, no integration by parts, no integrability/finiteness of the F/W integrals, no attainment of the infimum def | `D7-perelman-conditional-monotonicity` |
| `I1` | explicit-unproved-interface | open | LeviCivitaExistenceStatement and CovariantDerivativeCurvatureStatement are explicit BLOCKED Props with no proof. | `D7-levi-civita-smoothness` |
| `I2` | explicit-unproved-interface | open | ContinuousHeatMaximumPrincipleInterface is statement-only; no discrete-to-continuous limit is proved. | `D7-discrete-continuous-limit` |
| `I3` | explicit-unproved-interface | open | TensorRicciFlowODEBridge / ManifoldCurvatureRealization have no inhabitant; the ODE-to-tensor-Ricci-flow bridge is an explicit interface, never an axiom. | `D7-tensor-laplacian` |
| `I4` | explicit-unproved-interface | open | FDerivativeStatement, WeightedIBPStatement, BochnerStatement, ConjugateMeasureEvolutionStatement, EntropyFunctionalRegularityStatement are unproved Props; one-sided bounds are hypotheses; WeightedCalculus is abstract data. | `D7-conjugate-heat-interface`, `D7-bochner-formula` |
| `I5` | explicit-unproved-interface | open | kappa-noncollapsing K1-K7 and sphere-recognition S1-S5 are statement-only; nine foundational gaps listed (curvature, volume form, IBP, short-time existence, heat kernel, reduced length, Cheeger-Gromov, Brendle-Schoen). | `D7-kappa-noncollapsing-conditional`, `D7-sphere-recognition` |
| `I6` | explicit-unproved-interface | open | NeckAnalysis, ExtinctionTheorem and MissingInputs are statement-only; no geometric neck analysis or extinction theorem is proved. | `D7-surgery-neck-extinction` |
| `I7` | explicit-unproved-interface | open | FiniteMeshConvergence, PerelmanEvolutionBoundary and FiniteRepresentsContinuousPerelman are statement-only; FDissipation = 0 (no spatial Laplacian/Bochner content). | `D7-tensor-laplacian`, `D7-discrete-continuous-limit` |
| `I8` | explicit-unproved-interface | open | The transfer theorems perelmanF_monotone_of_tensorBridge / continuousPerelmanFMonotone_of_approximation are conditional on interfaces with no inhabitant; only a trivial finite identification inhabits PerelmanApproximation. | `D7-perelman-conditional-monotonicity` |
| `A1` | audit-residual-finding | open | Overstrong hypotheses (not falsity) in three promoted theorems: perelmanF_step_lt and gibbsTerm_strictAnti/gibbsTerm_step_lt assume 1 < c where 1 ≤ c suffices. Corrected theorems are proved in D4Audit; upstream restatement recommended. | `D7-evolution-sharp-restatement` |
| `A2` | audit-residual-finding | documented | Sign convention: the released functional is nonincreasing, opposite to Perelman's F-monotonicity; the cluster explicitly disclaims Perelman's theorem. | — |
| `A3` | audit-residual-finding | open | No false statement was found, but the adversarial audit only covers the D4 evolution cluster; earlier clusters (D2/D3) have axiom audits but no counterexample search. | `VERIFIER-D7-adversarial-audit-d2d3` |
| `P1` | process-delivery | resolved-in-worktree | queue.json is stale (last update 2026-09-08T23:55, before 5 later tasks finished): D2-geometry-foundation is recorded as running; D2-ricci-ode-cluster, D3-entropy-interface, D4-evolution-theorem and D4-counterexample-audit are recorded as queued. D5 clean-room | — |
| `P2` | process-delivery | known-environment-limit | Shared longrun/results/ path is outside the worker workspace-write sandbox; every card was mirrored inside its worktree and promoted later. D5 uses the same delivery pattern. D6 promotion of longrun/queue.json and longrun/results/D6-weekly-release.{md,json} to | — |
| `P3` | process-delivery | known-environment-limit | Prompt worktree names do not match the runtime worktree names (D5_rebuild vs D5_clean_rebuild; D2_geometry vs D2_geometry_foundation; D2_ode vs D2_ricci_ode_cluster; D3_topology vs D3_kappa_ledger; D4_audit vs D4_counterexample_audit). | — |
| `H1` | hygiene-note | informational | Two compiler-generated partial-safety helpers exist for safe structural recursions: D4Audit.sqTraj._unsafe_rec and Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec. They are DefinitionSafety.partial, not unsafe declarations, introduce no axioms, and ar | — |
| `H2` | hygiene-note | informational | Batteries.Util.ProofWanted is imported transitively (it defines the proof_wanted command); no project source uses proof_wanted (comment-aware scan clean) and no proof_wanted-derived project declaration exists. | — |
| `H3` | hygiene-note | informational | In Lean 4.34.0-rc2 native_decide no longer routes through ofReduceBool; it emits a private axiom <decl>._native.native_decide.ax_*. The audit catches it through the unapproved-axiom rule; the negative control confirms detection. | — |
| `P4` | process-delivery | known-environment-limit | Prompt worktree name D6_release does not match the runtime workspace D6_weekly_release; all D6 work is in D6_weekly_release. | — |
| `P5` | process-delivery | open | The D6 release package adds one new driver (D6AuditReport.lean) and a generated D6LedgerProbe.lean to the accepted D5 source set; promoted D1-D4 sources remain byte-identical (hash-verified). Any future release must re-run the hash check. | — |

| `M8` | explicit-unproved-interface | open | The canonical M8 topological-recognition/Poincare-conclusion node has no unconditional formal proof; existing cards are partial, conditional, model, statement-only, or audit artifacts. | `L5-child-recognition-spaceform`, `L5-child-surgery-nontrivial-datum`, `L5-child-moise-geometric-realization` |

## Program-step view

| step | status | blockers |
|---|---|---|
| `P-F-MONO` | blocked | no formal backward heat equation or conjugate heat kernel in mathlib; integration by parts on a Riemannian manifold is not available; integrability and finiteness of perelmanF are not established; the scalar curvature is data satisfying a trace formula rather than the trace of a constructed Ricci te |
| `P-W-MONO` | blocked | all blockers of P-F-MONO; tau-differentiation and the Gaussian normalization (4 pi tau)^{-n/2} require a measure-theoretic change-of-variables argument |
| `P-MU-MONO` | blocked | attainment of the infimum defining mu is not proved; the admissible class (unit mass) is a predicate without a constructed minimizer |
| `P-NLC` | blocked | reduced length and reduced volume are not formalized; the full Riemann curvature tensor norm is not available; only a scalar stand-in is used; comparison-geometry volume estimates for balls are not in mathlib |
| `P-REDUCED-VOL` | planned | needs path spaces, minimizers of the reduced length functional, and a Jacobian comparison theory |
| `P-HARNACK` | planned | requires the conjugate heat kernel and a Li-Yau-type differential Harnack argument |
| `P-KAPPA-SOL` | planned | needs the full curvature operator, non-collapsing, and the classification of 3D ancient solutions; mathlib has no Riemann curvature tensor or Ricci flow ancient-solution theory |
| `P-CANON` | planned | pointed Gromov-Hausdorff convergence and compactness are not in mathlib; epsilon-close model geometries (round sphere, round cylinder) are not formalized |
| `P-LONG` | planned | needs collapsing theory, hyperbolic 3-manifold geometry and a compactness argument |
| `P-SURG` | planned | requires the surgery algorithm, canonical neighborhood input, a priori curvature estimates, and a discrete flow construction |
| `P-EXT` | planned | needs the topological classification of 3-manifolds produced by the surgery decomposition; the topological conclusion is out of scope for the D1 interface layer |

Release-hygiene failures: **none**
