/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.Basic
import Poincare.D13.HeatKernelBridge.EuclideanTransport
import Poincare.D13.HeatKernelBridge.CompactUpgrade

/-!
# Poincare.D13.HeatKernelBridge.All

Umbrella module for the D13 heat-kernel bridge: the D7 `HeatKernelData` interface on the corrected
admissible-test-function domain (`Basic`), the D10 Euclidean heat kernel transported to it in every
dimension (`EuclideanTransport`), and the upgrade to the legacy D7 interface in the compact
finite-measure scope (`CompactUpgrade`).

The seven companion notes `PredicateSemantics` (what the legacy D7 heat-equation field actually
says), `PDERepair` (a versioned repair of that field, inhabited by the D10 kernel in every
dimension), `StatementRefutation` (the D7 existence statement is refutable as formalized, since
the schematic `HeatSpacetime` does not constrain the analytic operators), `GeometricRepair` (the
statement-level repair: geometric necessary conditions on the Laplacian excluding the counterexample,
the refutation of the Laplacian-only repair through the free forward time derivative, the
incomparability of the snapshot and PDE predicates, and the data-level repaired statement),
`LaplacianSymmetryRefutation` (the classical integration-by-parts/self-adjointness axiom is false
for the honest flat packaged Laplacian), `DataRefutation` (the two statement-level repairs are
themselves false as written: the two-point closed Riemannian spacetime with `Δ = 0` satisfies the
whole repaired hypothesis class and admits no strictly positive datum, while the bare interface is
inhabited with `C_lo = 0`; the corrected-domain flat statement is proved) and `ConjugateHeatBridge`
(the conjugate-heat half of the D7 interface: the schematic `ConjugateHeatKernelExistenceStatement`
is refuted by the two-point datum with the identity Laplacian, the versioned predicate
`IsConjugateHeatKernelPDE` carries the genuine conjugate heat equation, any corrected-domain datum
is transported to it by time reversal, and the time-reversed D10 kernel inhabits it in every
dimension while refuting the legacy snapshot predicate) import this umbrella rather than being
re-exported by it, so they are audited separately in `AxiomAudit.lean`. The D7-namespaced consumers
`Poincare.D7.HeatKernel.StatementStatus`, `Poincare.D7.HeatKernel.RepairStatus`,
`Poincare.D7.HeatKernel.DataStatus` and `Poincare.D7.ConjugateHeat.Status` record the refutations
at the D7 level. The eighth companion note `FiniteSpaceHeat` supplies the missing hypothesis-class
repair in the finite-dimensional setting: a pinned finite Laplace operator (symmetric,
constant-annihilating, strictly positive off-diagonal), the explicit matrix-exponential heat kernel
with its checked laws (strict positivity, symmetry, unit mass, Chapman-Kolmogorov, the genuine
`HasDerivAt` PDE, the Gaussian upper bound, the Dirac initial condition against *all* functions,
and non-degeneracy against the identity kernel), the legacy and corrected-domain D7 datums, the
certified closed-Riemannian schematic spacetime, the inhabitation of the repaired predicate
`IsHeatKernelPDE`, and the *proved* pinned-operator existence statement
`FinitePinnedHeatExistenceStatement`; the D7 consumer `Poincare.D7.HeatKernel.FiniteStatus` records
it at the D7 level. The ninth companion note `FiniteUniqueness` supplies the *uniqueness* half of
the same pinned problem by the classical energy method: the `ℓ²` energy `∑ x, (u x)^2` of a
solution of `∂_t u = Δ u` has derivative `2 * ∑ x, u x * Δ u x ≤ 0`, so it is antitone in time and
a solution with zero initial limit vanishes identically; consequently any kernel with the pinned
Laplacian, the genuine PDE and the pointwise Dirac initial data is the matrix-exponential kernel for
every positive time, and among causal kernels the pinned problem has exactly one solution
(`exists_unique_finiteHeatKernel`). The D7 consumer `Poincare.D7.HeatKernel.UniquenessStatus`
records the existence-and-uniqueness summary at the D7 level. The tenth companion note
`FiniteConjugateUniqueness` supplies the *well-posedness of the conjugate half*: for the backward
equation `∂_t u = -A u` with a quadratic form bounded below, the Grönwall-weighted energy
`s ↦ exp (-(2C) s) * ∑ x, u (t₀ - s) x ^ 2` is antitone, so a solution with zero terminal limit
vanishes and the conjugate predicate has at most one solution below `t₀`; the canonical
time-reversed kernel `finiteConjugateKernel G t₀ x y t = K_G x y (t₀ - t)` inhabits the repaired
conjugate predicate on the finite pinned model, and among anticausal kernels it is the unique
solution (`exists_unique_finiteConjugateKernel`). The D7 consumer
`Poincare.D7.ConjugateHeat.UniquenessStatus` records the conjugate summary at the D7 level. This is
the finite-dimensional model of the remaining manifold content, not a proof of
`D7-HEAT-KERNEL-EXISTENCE` or of its conjugate sibling.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
