# D6-weekly-release — result card

- **Task id:** `D6-weekly-release`
- **Release id:** `week-1-2026-09-09`
- **Stage / lane:** D6 / integrator
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release` (prompt said `D6_release`; runtime is `D6_weekly_release`)
- **Generated:** `2026-09-09T04:14:39.611927+00:00`
- **Verdict:** **WEEKLY RELEASE CUT — STAGES 1-4 INFRASTRUCTURE VERIFIED; PERELMAN PROGRAM NOT PROVED**

> This release does **not** claim the Poincare conjecture, Ricci-flow existence, Perelman
> monotonicity, kappa-noncollapsing, canonical neighbourhoods, surgery, extinction or sphere
> recognition. Those remain blocked/planned (see §6). The verified content is finite-dimensional,
> algebraic and discrete infrastructure plus an adversarial audit of the D4 evolution cluster.

## 1. Consumed input (accepted D5 only)

- `D5-clean-rebuild` verdict: **RELEASE GATE PASS**
- card sha256: `e029e7cf04995b8b10029da911456af8ae98022531ae5b6a11f5f95f2f870185`
- clusters accepted: 11, promoted files: 53
- D5 manifests hashed: 7 files
- promoted-source hash check: **53 checked, 0 changed, 0 missing**

## 2. Independent D6 clean-room verification

The D6 integrator rebuilt the accepted sources from a fresh `.lake/build` in the D6 worktree
and re-ran every gate. Full logs and exit codes: `manifest/verification.json`.

| gate step | command | exit | seconds |
|---|---|---|---|
| `source_hash_verification` | `python3 tools/d6_verify.py (in-process source_hash_verification)` | 0 | 0.0 |
| `lake_build` | `lake build` | 0 | 3.6 |
| `release_check` | `lake env lean ReleaseCheck.lean` | 0 | 3.9 |
| `release_audit` | `lake env lean ReleaseAudit.lean` | 0 | 5.8 |
| `d6_decl_report` | `lake env lean D6AuditReport.lean` | 0 | 6.0 |
| `release_claims` | `lake env lean ReleaseClaims.lean` | 0 | 4.6 |
| `per_file_checks` | `lake env lean <each promoted file>` | 0 | 191.2 |
| `forbidden_token_scan` | `python3 input/d5-tools/scan_forbidden.py release` | 0 | 0.0 |
| `negative_control` | `lake env lean ../negcontrol/NegativeControl.lean` | 0 | 0.9 |
| `mathlib_head` | `git rev-parse HEAD` | 0 | 0.0 |
| `mathlib_status` | `git status --porcelain` | 0 | 0.0 |
| `ledger_probe` | `lake env lean D6LedgerProbe.lean` | 0 | 4.8 |

Gate failures: **none**

- declarations audited by `D6AuditReport.lean`: **1619** (theorems: 887)
- ledger/claim probe (`D6LedgerProbe.lean`): **262 declarations, exit 0** (`logs/18_d6_ledger_probe.log`)
- forbidden dependency counts (project axiom / unsafe / sorryAx / native_decide / unapproved / proof_wanted): **0 / 0 / 0 / 0 / 0 / 0**
- card-claimed declarations resolved: **193/193**
- ledger declarations unresolved: **0**

## 3. Weekly release manifest (summary)

- package: `release/` — 63 Lean files (58 promoted + drivers)
- manifest: `manifest/weekly-release-manifest.json` / `.md`
- verified declarations: `manifest/verified-declarations.json` (1619 declarations, per-declaration axiom cone)
- axiom report: `manifest/axiom-report.json`, log `logs/13_d6_decl_report.log`

## 4. Theorem / dependency ledger (summary)

- program_steps: **11**
- program_steps_blocked: **4**
- program_steps_planned: **7**
- program_steps_proved: **0**
- interface_nodes: **43**
- interface_nodes_checked: **34**
- interface_nodes_open: **9**
- headline_checked_results: **18**
- headline_partial_results: **0**
- blocked_layer_entries: **46**
- edges: **119**
- kernel_declarations_audited: **1619**
- kernel_theorems: **887**
- card_claims_named: **193**
- card_claims_resolved: **193**
- ledger_declarations_referenced: **191**
- ledger_declarations_unresolved: **0**

Full ledger: `manifest/theorem-dependency-ledger.json` / `.md`.

## 5. Verified Lean declarations (headline results)

Every entry below resolves to a kernel-audited declaration with a compiling file and an
axiom cone contained in `{propext, Classical.choice, Quot.sound}`. The complete
per-declaration inventory is `manifest/verified-declarations.json`.

- **L-D1-CURVATURE-ALGEBRA** [checked]: Finite-dimensional curvature-tensor algebra probe: skew-symmetry, Bianchi, Ricci trace and additivity are kernel-checked. — `Probe.CurvatureTensor.antisymm`, `Probe.CurvatureTensor.bianchi`, `Probe.CurvatureTensor.endo`, `Probe.CurvatureTensor.ricci` (+2 more)
- **L-D1-LEVI-CIVITA-PROBE** [checked]: Levi-Civita uniqueness and torsion antisymmetry toy probes are kernel-checked. — `Probe.leviCivita_uniqueness_toy`, `Probe.leviCivita_isLeviCivita_toy`, `Probe.torsion_antisymm_toy`, `Probe.inner_self_nonneg_toy`
- **L-D1-PDE-PROBE** [checked]: Discrete heat-slab maximum-principle probe and affine heat-slab interface are kernel-checked; the continuous interface is statement-only. — `Probe.PdeApi.strict_finite_grid_max_principle`, `Probe.PdeApi.strict_finite_grid_max_principle_max`, `Probe.PdeApi.heat_slab_nonpos_of_interface`, `Probe.PdeApi.heat_slab_zero_interface` (+2 more)
- **L-D1-PERELMAN-TOY** [checked]: Perelman F/W/mu interfaces are defined and the toy monotonicity lemmas are kernel-checked. — `Perelman.toyF_mono`, `Perelman.toyW_nonneg`, `Perelman.perelmanMu_le`, `Perelman.hasMetricTimeDerivative_const` (+5 more)
- **L-D2-CURVATURE-IDENTITIES** [checked]: Abstract connection curvature identities: skew, Bianchi, cyclic decomposition, Ricci additivity, scalar additivity/scaling and the basis trace formula. — `Poincare.Longrun.Geometry.AbstractConnection.curvature_skew`, `Poincare.Longrun.Geometry.AbstractConnection.curvature_bianchi`, `Poincare.Longrun.Geometry.AbstractConnection.curvature_cyclic_decomp`, `Poincare.CurvatureAlgebra.CurvatureOperator.ricci_add` (+7 more)
- **L-D2-LEVI-CIVITA** [checked]: Levi-Civita uniqueness and metric-compatibility equivalence are kernel-checked; existence and covariant-derivative curvature are explicit unproved Props. — `Poincare.Longrun.Geometry.leviCivita_nabla_unique`, `Poincare.Longrun.Geometry.meanConnection_isMetricCompatible_iff`, `Poincare.Longrun.Geometry.leviCivitaExistence_iff_nonempty`, `Poincare.Longrun.Geometry.mean_curvature_apply` (+2 more)
- **L-D2-DISCRETE-MAX-PRINCIPLE** [checked]: Discrete maximum principle on a finite heat grid: the evolution never exceeds the initial supremum and the discrete energy is non-increasing. — `Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le`, `Poincare.Longrun.PDE.HeatGridEvolution.le_sup'_initial`, `Poincare.Longrun.PDE.HeatGridEvolution.succ_le`, `Poincare.Longrun.PDE.HeatGridEvolution.energy_nonincreasing` (+1 more)
- **L-D2-ODE-INVARIANT** [checked]: The non-negative orthant is invariant under the finite-dimensional Hamilton reaction ODE (continuous and explicit-Euler discrete). — `Poincare.Longrun.CurvatureODE.component_monotone`, `Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant`, `Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant_discrete`, `Poincare.Longrun.CurvatureODE.zero_orthant_invariant`
- **L-D2-ODE-SCALAR-MONO** [checked]: The scalar curvature functional of the finite-dimensional reaction ODE is monotone (continuous and discrete). — `Poincare.Longrun.CurvatureODE.scalarFunctional_monotone`, `Poincare.Longrun.CurvatureODE.scalarOfState_monotone`, `Poincare.Longrun.CurvatureODE.scalarFunctional_monotone_discrete`, `Poincare.Longrun.CurvatureODE.scalarOfState_monotone_discrete` (+2 more)
- **L-D3-ENTROPY-CERTIFICATES** [checked]: Entropy interface: F/W data, monotonicity and decay certificates, their composition and the discrete heat-energy certificate are kernel-checked; all analytic inputs are explicit hypotheses. — `Poincare.Longrun.Entropy.EntropyData.F`, `Poincare.Longrun.Entropy.EntropyData.W`, `Poincare.Longrun.Entropy.EntropyData.FDissipation_nonneg`, `Poincare.Longrun.Entropy.EntropyData.F_mono_integrand` (+20 more)
- **L-D3-KAPPA-MANIFOLD** [checked]: Compact 3-manifold class yields the expected topological consequences (sigma-compact, paracompact, locally compact, second countable, finite chart cover). — `Poincare.Longrun.Topology.CompactThreeManifold.toSigmaCompactSpace`, `Poincare.Longrun.Topology.CompactThreeManifold.toParacompactSpace`, `Poincare.Longrun.Topology.CompactThreeManifold.toLocallyCompactSpace`, `Poincare.Longrun.Topology.CompactThreeManifold.toSecondCountableTopology` (+3 more)
- **L-D3-KAPPA-ALGEBRA** [checked]: kappa-noncollapsing certificate algebra and its equivalence with the normalized-ball-volume lower bound are kernel-checked. — `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_pos`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_ne_zero`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.mono`, `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_unit_ball_lower` (+18 more)
- **L-D3-SURGERY-INTERFACE** [checked]: Surgery ledger interface: datum/predicates/certificate constructors and chain composition preserve the ledger invariants. — `Poincare.Longrun.Surgery.SurgeryCertificate.trivial`, `Poincare.Longrun.Surgery.SurgeryCertificate.ofHomeomorph`, `Poincare.Longrun.Surgery.SurgeryCertificate.ofHomotopyEquiv`, `Poincare.Longrun.Surgery.ChainCertificate.append` (+4 more)
- **L-D3-SURGERY-TOY** [checked]: Toy extinction skeleton: the toy complexity relation strictly decreases and admits no infinite chain. — `Poincare.Longrun.Surgery.toyRel_functional`, `Poincare.Longrun.Surgery.toyRel_lt`, `Poincare.Longrun.Surgery.toyRel_succ`, `Poincare.Longrun.Surgery.toyRel_not_refl` (+10 more)
- **L-D4-PERELMAN-F-ANTITONE** [checked]: Finite Gibbs-weighted functional perelmanF is antitone along the D2 evolution relation (continuous and discrete), with an explicit dissipation identity. — `Poincare.Longrun.Evolution.perelmanF_antitone`, `Poincare.Longrun.Evolution.perelmanF_antitone_discrete`, `Poincare.Longrun.Evolution.hasDerivWithinAt_perelmanF`
- **L-D4-EVOLUTION-CERTIFICATES** [checked]: D3 antitone certificates are instantiated for the evolution cluster (continuous and discrete). — `Poincare.Longrun.Evolution.perelmanAntitoneCertificate`, `Poincare.Longrun.Evolution.perelmanAntitoneCertificate_discrete`, `Poincare.Longrun.Evolution.continuousPerelmanCertificate`, `Poincare.Longrun.Evolution.finiteReactionEntropyData_F` (+2 more)
- **L-D4-SHARP-CORRECTIONS** [checked]: Adversarial audit found no false statement; three promoted theorems have overstrong hypotheses and sharp-hypothesis replacements are kernel-checked. — `D4Audit.gibbsTerm_strictAnti_of_one_le`, `D4Audit.gibbsTerm_step_lt_of_one_le`, `D4Audit.perelmanF_step_lt_of_one_le`
- **L-D4-COUNTEREXAMPLES** [checked]: Counterexamples delimit the hypotheses of the D4 cluster and non-vacuity checks confirm the main theorem is not vacuous. — `D4Audit.counterexample_continuous_c_half`, `D4Audit.counterexample_discrete_c_half`, `D4Audit.counterexample_negative_step`, `D4Audit.perelmanF_nonneg_sharp` (+6 more)

## 6. Explicit blockers for the full Perelman proof

22 of the 29 D5 blockers remain open; P1 (stale queue) is corrected in manifest/queue.updated.json but promotion to the shared longrun/queue.json is pending a wider sandbox. D6 adds P4 (prompt/runtime worktree-name mismatch) and P5 (release-source delta). No blocker is a release-hygiene failure: every one is an upstream mathlib gap, an explicit unproved interface, or a documented boundary.

- `P-F-MONO` (blocked): no formal backward heat equation or conjugate heat kernel in mathlib; integration by parts on a Riemannian manifold is not available; integrability and finiteness of perelmanF are not established; the scalar curvature is data satisfying a t
- `P-W-MONO` (blocked): all blockers of P-F-MONO; tau-differentiation and the Gaussian normalization (4 pi tau)^{-n/2} require a measure-theoretic change-of-variables argument
- `P-MU-MONO` (blocked): attainment of the infimum defining mu is not proved; the admissible class (unit mass) is a predicate without a constructed minimizer
- `P-NLC` (blocked): reduced length and reduced volume are not formalized; the full Riemann curvature tensor norm is not available; only a scalar stand-in is used; comparison-geometry volume estimates for balls are not in mathlib
- `P-REDUCED-VOL` (planned): needs path spaces, minimizers of the reduced length functional, and a Jacobian comparison theory
- `P-HARNACK` (planned): requires the conjugate heat kernel and a Li-Yau-type differential Harnack argument
- `P-KAPPA-SOL` (planned): needs the full curvature operator, non-collapsing, and the classification of 3D ancient solutions; mathlib has no Riemann curvature tensor or Ricci flow ancient-solution theory
- `P-CANON` (planned): pointed Gromov-Hausdorff convergence and compactness are not in mathlib; epsilon-close model geometries (round sphere, round cylinder) are not formalized
- `P-LONG` (planned): needs collapsing theory, hyperbolic 3-manifold geometry and a compactness argument
- `P-SURG` (planned): requires the surgery algorithm, canonical neighborhood input, a priori curvature estimates, and a discrete flow construction
- `P-EXT` (planned): needs the topological classification of 3-manifolds produced by the surgery decomposition; the topological conclusion is out of scope for the D1 interface layer

Full list: `manifest/blockers.json` / `.md` (23 open, 1 documented, 0 resolved by D6, 1 resolved in worktree pending promotion, 3 environment limits, 3 informational).

## 7. Next 20 queued builder tasks

| # | task | objective | blockers |
|---|---|---|---|
| 1 | `D7-riemann-curvature-tensor` | Local Riemann curvature tensor from an abstract connection | U1 |
| 2 | `D7-ricci-scalar-curvature` | Ricci and scalar curvature from the local curvature tensor | U2 |
| 3 | `D7-geodesic-exponential` | Geodesic flow and exponential map interface | U3 |
| 4 | `D7-levi-civita-smoothness` | Levi-Civita existence and C^k smoothness interface | U4, U5, I1 |
| 5 | `D7-orientability-volume-form` | Manifold orientability and Riemannian volume form | U7, U11 |
| 6 | `D7-divergence-ibp` | Divergence theorem and weighted integration by parts on a chart domain | U7, I4 |
| 7 | `D7-bochner-formula` | Bochner formula for the weighted Laplacian | U7, I4 |
| 8 | `D7-conjugate-heat-interface` | Conjugate heat equation operator and F-derivative identity | U6, I4 |
| 9 | `D7-heat-kernel-existence` | Heat kernel / conjugate heat kernel existence interface | U6, I5 |
| 10 | `D7-discrete-continuous-limit` | Discrete-to-continuous limit for the heat maximum principle | I2, I7 |
| 11 | `D7-hamilton-short-time` | Hamilton short-time existence interface | U8 |
| 12 | `D7-tensor-laplacian` | Tensor Laplacian and curvature evolution | U10, I3, I7 |
| 13 | `D7-reduced-length-volume` | Reduced length, reduced volume and their monotonicity interface | U9, I5 |
| 14 | `D7-kappa-noncollapsing-conditional` | Conditional kappa-noncollapsing from entropy monotonicity | I5 |
| 15 | `D7-gh-compactness` | Pointed Gromov-Hausdorff compactness interface | U9, I5 |
| 16 | `D7-canonical-neighborhood` | Canonical neighborhood theorem interface | I5 |
| 17 | `D7-surgery-neck-extinction` | Conditional neck analysis and finite extinction | I6, U9 |
| 18 | `D7-sphere-recognition` | Sphere recognition: S^3 simple connectivity and pi_1 triviality | I5 |
| 19 | `D7-evolution-sharp-restatement` | Promote the D4 sharp-hypothesis corrections upstream | A1 |
| 20 | `D7-perelman-conditional-monotonicity` | Conditional F/W/mu monotonicity assembly | U12, I8 |

Full acceptance criteria: `manifest/next-20-tasks.json` / `.md`. One verifier task follows: `VERIFIER-D7-adversarial-audit-d2d3`.

## 8. What is explicitly NOT claimed

- the Poincare conjecture
- existence or uniqueness of Ricci flow
- Perelman F/W/mu monotonicity
- kappa-noncollapsing
- canonical neighbourhoods
- Ricci flow with surgery
- finite extinction or sphere recognition

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release
python3 tools/d6_verify.py            # gates + per-declaration axiom report
python3 tools/d6_build_release.py     # ledger + probe + manifest + blockers + tasks + card
```

## 10. Files produced

- `manifest/weekly-release-manifest.json`
- `manifest/theorem-dependency-ledger.json`
- `manifest/verified-declarations.json`
- `manifest/verified-theorems.json`
- `manifest/axiom-report.json`
- `manifest/blockers.json`
- `manifest/next-20-tasks.json`
- `manifest/verification.json`
- `manifest/input-hashes.json`
- `manifest/queue.updated.json`
- `longrun/results/D6-weekly-release.md`
- `longrun/results/D6-weekly-release.json`
- `release/D6AuditReport.lean` — per-declaration kernel axiom report
- `release/D6LedgerProbe.lean` — generated `#check` probe for every ledger declaration
- `logs/` — every command's full log
