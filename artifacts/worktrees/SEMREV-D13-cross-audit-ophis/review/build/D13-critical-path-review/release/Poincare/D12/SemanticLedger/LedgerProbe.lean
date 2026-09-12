/-
Copyright (c) 2026 Poincare Longrun D12 semantic-ledger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-semantic-ledger)
-/

import Poincare.Stage6.TopologyBridge
import Poincare.Stage6.SphereSimplyConnected
import Poincare.Longrun.Surgery
import Poincare.Longrun.Evolution
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.PDE.ContinuousInterface
import Poincare.Longrun.Topology.MissingTheorems
import Poincare.Longrun.Topology.CompactThreeManifold
import Poincare.Longrun.Entropy
import Probe.PdeApi

/-!
# Poincare.D12.SemanticLedger.LedgerProbe

**In-package declaration probe for the machine-readable semantic ledger.**

Each `#check` below re-verifies, in the D12 worktree's own fresh build, the
declaration that the ledger records for a claimed main-chain theorem or a
certificate/record field of the D1-D6 promoted content.  A `#check` failure
would make this module (and hence `lake build` of the `Poincare` library)
fail, so the probe is fail-closed.  D7-D10-D11 declarations are probed
separately against the independently recompiled snapshot oleans
(`audit_probes/D12RealModuleProbe.lean`); the classification of each item
(model / conditional / statement-only / genuine-general) is recorded in
`manifest/d12-semantic-ledger.json`, not in Lean.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file.
-/

/-! ## Stage 6 statement-only targets (D1/D6) -/

#check Poincare.Stage6.poincareConjectureTopologicalThree
#check Poincare.Stage6.sphereThreeSimplyConnected
#check Poincare.Stage6.sphereThreePiOneTrivial
#check Poincare.Stage6.pathConnectedSpace_sphereThree
#check Poincare.Stage6.sphereThreeSimplyConnected_iff_simplyConnectedSpace

/-! ## Surgery / extinction interface (D3/D6) -/

#check Poincare.Longrun.Surgery.ExtinctionTheorem
#check Poincare.Longrun.Surgery.NeckAnalysis
#check Poincare.Longrun.Surgery.ChainCertificate
#check Poincare.Longrun.Surgery.ExtinctionTheorem.finitelyMany_of_complexity
#check Poincare.Longrun.Surgery.ExtinctionTheorem.extincts_of_complexity

/-! ## Evolution cluster (D4): promoted theorems and the A1 overstrength sites -/

#check Poincare.Longrun.Evolution.perelmanF_step_lt
#check Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#check Poincare.Longrun.Evolution.gibbsTerm_step_lt
#check Poincare.Longrun.Evolution.perelmanF

/-! ## Discrete heat grid (D2/D3): finite-model theorems -/

#check Poincare.Longrun.PDE.HeatGridEvolution.le_sup'_initial
#check Poincare.Longrun.PDE.HeatGridEvolution.energy_nonincreasing
#check Poincare.Longrun.PDE.ContinuousHeatMaximumPrincipleInterface
#check Probe.PdeApi.HeatSlabMaximumPrincipleInterface
#check Probe.PdeApi.strict_finite_grid_max_principle

/-! ## Statement-only missing inputs (D2 topology cluster) -/

#check Poincare.Longrun.Topology.missingKappaNoncollapsing
#check Poincare.Longrun.Topology.missingNormalizedNoLocalCollapsing
#check Poincare.Longrun.Topology.missingConjugateHeatKernel
#check Poincare.Longrun.Topology.missingReducedVolumeMonotonicity

/-! ## Re-verification of the axiom cones of the ledger-cited in-package theorems -/

#print axioms Poincare.Longrun.Evolution.perelmanF_step_lt
#print axioms Poincare.Longrun.PDE.HeatGridEvolution.le_sup'_initial
#print axioms Poincare.Longrun.Surgery.ExtinctionTheorem.finitelyMany_of_complexity
#print axioms Poincare.Stage6.pathConnectedSpace_sphereThree
