/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — independent kernel-axiom audit of the D13 manifold-IBP headline theorems

The D13 `ManifoldIBP`/entropy layer is the U7/I4-relevant body of work inherited by this
worktree.  An inventory taken during this invocation found that the layer is *terminal*: its
headline theorems are consumed only inside the D13 tree.  As part of the L4 verification
duty, this file re-derives the kernel axiom cones of the headline declarations from the
outside (separate module, same pinned toolchain, no D13 audit file involved) so that the
`[propext, Classical.choice, Quot.sound]` claim in the D13 card is independently reproduced.

This file contains no mathematics.  The machine-checked fail-closed gate over its output is
`tools/l4_axiom_audit.py` (list `D13_HEADLINES`).
-/
import Poincare.D13.ManifoldIBP.POUConstruction
import Poincare.D13.ManifoldIBP.PartialChartModelPOU
import Poincare.D13.ManifoldIBP.SmoothAtlasModel
import Poincare.D13.ManifoldIBP.Transfer
import Poincare.D13.HeatKernelBridge

/-! ## General manifold-IBP engine and its unconditional model instantiation -/

#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou
#print axioms Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData

/-! ## Gaussian entropy bridge (I4 model consumption) -/

#print axioms Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian
#print axioms Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian
