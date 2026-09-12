import Poincare.Longrun.Evolution.Gibbs
import Poincare.Longrun.Evolution.Functional
import Poincare.Longrun.Evolution.Continuous
import Poincare.Longrun.Evolution.Discrete
import Poincare.Longrun.Evolution.Counterexample
import Poincare.Longrun.Evolution.Bridge

/-!
# Poincare.Longrun.Evolution

**D4 evolution cluster: a checked finite-dimensional Perelman-type monotonicity theorem.**

This cluster is the `D4-evolution-theorem` deliverable. It consumes the two accepted
predecessor cards

* `D2-ricci-ode-cluster` — the finite reaction ODE `Poincare.Longrun.CurvatureODE`;
* `D3-entropy-interface` — the measure-theoretic `EntropyData` / certificate interface
  `Poincare.Longrun.Entropy`,

and builds one genuinely nontrivial checked evolution/monotonicity theorem:

> Along any solution of the D2 reaction ODE `d lamᵢ/dt = Fᵢ(lam)` with `Fᵢ ≥ 0`, the finite
> Perelman-type functional `perelmanF c lam = ∑ i, (c i + (lam i)²) e^{-lam i}` is
> **nonincreasing** whenever the curvature-like data satisfies `1 ≤ c i`, with the exact
> dissipation identity
> `d/dt perelmanF = -∑ i, Fᵢ(lam) * ((lamᵢ - 1)² + (cᵢ - 1)) * e^{-lamᵢ} ≤ 0`.

The theorem holds in continuous time (`perelmanF_antitone`), for the explicit-Euler
recurrence (`perelmanF_antitone_discrete`, with no CFL restriction beyond `h ≥ 0`), and is
packaged as genuine inhabitants of the accepted D3 `AntitoneCertificate` and
`ContinuousAntitoneCertificate` structures. The finite functional is exactly the D3
`EntropyData.F` of a finite counting-measure datum, so the theorem is a statement about the
accepted entropy interface (`finiteReactionEntropyData_F`).

## Approximation boundary (explicit, read this before citing anything)

This is a **finite-dimensional model**, not Perelman's monotonicity theorem. In particular:

* `c` is an abstract curvature-like data vector, not the scalar curvature of a metric;
* the integral `∫ (R + |∇f|²) e^{-f} dV` is replaced by the finite sum `perelmanF`;
* the spatial Laplacian / Bochner / integration-by-parts content is **not** modeled;
* the functional is nonincreasing, the opposite direction to Perelman's `F`-monotonicity,
  because the finite model couples the Gibbs weight `e^{-lam}` to the curvature state itself.

The explicit identification hypothesis from the finite sum to a continuous functional, the
statement-only mesh convergence, and the conditional transfer theorems are in
`Poincare.Longrun.Evolution.Bridge`; the D2 tensor bridge and the D3 Bochner/IBP bridge are
re-exported there as unproved hypothesis fields. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` occurs anywhere in the cluster.

Modules:

* `Poincare.Longrun.Evolution.Gibbs` — the one-variable Gibbs term `(c + x²) e^{-x}`, its
  exact derivative `-((x-1)² + (c-1)) e^{-x}`, antitonicity for `1 ≤ c`, strict antitonicity
  for `1 < c`, and the within/global chain rules;
* `Poincare.Longrun.Evolution.Functional` — the finite Perelman functional `perelmanF`, the
  finite counting-measure `EntropyData` instance, and the checked identity
  `EntropyData.F = perelmanF`;
* `Poincare.Longrun.Evolution.Continuous` — the continuous-time dissipation identity and
  monotonicity theorem, flat-spot rigidity, the D3 `AntitoneCertificate`, the global-flow
  D3 `ContinuousAntitoneCertificate`, and non-vacuity witnesses;
* `Poincare.Longrun.Evolution.Discrete` — the explicit-Euler one-step inequality, the
  discrete monotonicity theorem, strict decrease, and the D3 `AntitoneCertificate ℕ`;
* `Poincare.Longrun.Evolution.Counterexample` — the sign-convention audit: `1 ≤ c` is
  necessary (one-step and full continuous-trajectory counterexamples), `h ≥ 0` and
  nonnegative reactions are necessary, and the threshold `c = 1` is sharp;
* `Poincare.Longrun.Evolution.Bridge` — the explicit approximation-boundary interface
  (`FiniteRepresentsContinuousPerelman`, `FiniteMeshConvergence`), the checked limit passage,
  and the conditional transfer theorems.
-/
