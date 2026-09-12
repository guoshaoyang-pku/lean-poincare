# L5-topology-audit — research brief (2026-09-11, invocation 1)

**Lane:** auditor (M4 topology and adversarial audit). **Question:** is the recognition /
triangulation / surgery evidence in the union release what the result cards say it is, and what
exactly remains open?

## Bottom line

The topology lane's *proved* layer is real, small, and reproducible: the ball-gluing /
Alexander-trick / two-disks triangulation lemmas and the covering-space + monodromy deck-triviality
theorems are unconditional, axiom-clean, and genuinely consumed downstream. Everything that would
connect them to the Poincaré conjecture is either an explicit conditional interface or an
uninhabited statement, and the end-game assembly (`stage6Target_of_v3hypotheses`) is a
**conditional implication**, not a theorem about manifolds. The named blockers in scope
(`M8`, `A3`, `I6`, `I7`) are all still open; `M8` is not even bound to a definition in the
control plane. Two new adversarial findings matter more than the positive recheck:
**conclusion-equivalent hypotheses** in the two `stage6Target_of_*` wrapper theorems and a
**union release that cannot be imported as a whole** (58 duplicated declaration names).

## What was rechecked, and how

- `lake build` (pinned `v4.34.0-rc2`, mathlib `7974e751`) — exit 0, 9347 jobs; plus per-file
  elaboration of all 464 authored `.lean` files (0 failures). `ReleaseClaims.lean` and
  `D6LedgerProbe.lean` are **not** built by `lake build` at all; they do elaborate.
- Independent fail-closed kernel audit, two collision-free passes covering all 462 buildable
  modules: 0 unexpected project axioms, 0 `sorryAx`, 0 `native_decide`, 0 `unsafe`, 0 unapproved
  cones. Negative controls fire in both directions (fresh axiom; the release's own axiom).
- Statement-shape scan (syntactic + definitional conclusion-equivalence), statement-only `Prop`
  inventory, retained-consumer recomputation, textual forbidden-token scan, source-hash diff
  against the pre-audit baseline (0 differences: the audit changed nothing in `release/`).

## Evidence classification (topology lane, 3220 declarations)

| class | examples | note |
|---|---|---|
| proved, unconditional | `doubleBallHomeoSphere`, `sphereConnectSum_homeo_sphere`, `diskGlueQuotHomeoSphere`, `alexanderHomeo`, `sphereOfTwoDisks`, `finiteFreeOrbit_isQuotientCoveringMap`, `deckTrivial_of_simplyConnected_quotient` | clean cones; real consumers (6–12 for triangulation glue, 2 for deck triviality) |
| proved but unconsumed | `iteratedSphereSum_homeo_sphere` (0) | the SR-5 closure lemma is bypassed by `mkV2` |
| constructed bridge | `ConnectedSumDecomposition.mkV2` | consumed by `stage6Target_of_v2decomposition` |
| conditional implication | `stage6Target_of_v2/v3hypotheses`, `sphericalPieceRecognition_of_spaceForm`, D7 `stage6Target_of_certificates` | hypotheses explicit; terminal assembly has 0 consumers |
| model | `Poincare.D7.Limit.HeatMeshConvergence` (1-D heat mesh) | conditional on a stability input |
| statement-only | `MoiseTriangulationTheorem`, `NeckAnalysisHypotheses`, `missingFullNeckAnalysis`, `missingExtinctionTheorem`, `FiniteMeshConvergence`, `FiniteRepresentsContinuousPerelman`, `PerelmanEvolutionBoundary` | no inhabitant anywhere in the tree |
| upstream source claim | ported `HatcherLib` van Kampen cluster (682 decls, axiom-clean) | imported only by D13 audit modules; SR-4 unwired |
| circular / vacuous | `stage6Target_of_sphereRecognition`, `stage6Target_of_compactThreeManifold`; `realLineProcedureChain_simplyConnected` | flagged; 0 consumers |

## New findings worth acting on

1. **Colliding declarations (integration defect).** `D7.Bochner.Basic` vs
   `D7.Monotonicity.BochnerCertificate`, `D7.Bochner.GradientEstimate` vs
   `D7.Monotonicity.BochnerGradientEstimate`, `D7.ConjugateHeat.Basic` vs
   `D7.Monotonicity.ConjugateHeatCertificate` declare 58 identical names. 25 modules depend on the
   original side, 14 on the copy; a whole-release import is impossible. This will bite any future
   task that tries to import both lanes together (e.g. a global kernel-trust statement).
2. **Conclusion-equivalent wrappers.** The `stage6Target_of_sphereRecognition` /
   `..._of_compactThreeManifold` theorems are `P → P` after unfolding the target alias. They are
   honestly docstringed, but a downstream reader could mistake them for progress.
3. **Audit-list drift.** The D12 recognition audit list covers 171 of 172 module constants
   (`AntipodalGroup` missing); the D10 list covers 71 of 96. The L5 environment audit closes the
   gap, but the cards' coverage numbers should be regenerated from the environment.
4. **A3 has a clean mechanical screen, not a closure.** 596 D2/D3 declarations show no
   vacuous/circular/tautological/unused-hypothesis defect; counterexample searches remain absent.

## Exact residual mathematics (what a builder must supply)

- **SR-4 (van Kampen for connected sums).** Machinerary is ported and compiles; the missing work
  is the open cover of the iterated connected sum + factorizations-connected + the free-product
  triviality lemma, then wiring `RemainingRecognitionHypothesesV3.vanKampen`.
- **I6.** Geometric neck analysis (canonical-neighbourhood data → separating/cut-and-cap neck) and
  finite-time extinction from strictly decreasing complexity; both currently `Prop`-valued
  interfaces with no inhabitant.
- **I7.** A constructed stability/vanishing-error input for the mesh limit, and an inhabitant (or
  a genuine discharge) of `FiniteRepresentsContinuousPerelman` / `PerelmanEvolutionBoundary`; the
  accepted `FDissipationCorrected` correction supersedes the `FDissipation = 0` wording.
- **A3.** Counterexample searches over D2 (`CurvatureODE`) and D3 (`Entropy`, `PDE`).
- **Moise.** Untouched and unclaimed; `MoiseTriangulationTheorem` is a statement-only `Prop`.

## Hand-off

Nine child tasks in `comms/outbox/` (two for A3, two for I6, two for I7, one for M8 binding, one
for the collision reconciliation, one for SR-4). No blocker was closed in this audit; nothing was
promoted; the Poincaré conjecture is not claimed.
