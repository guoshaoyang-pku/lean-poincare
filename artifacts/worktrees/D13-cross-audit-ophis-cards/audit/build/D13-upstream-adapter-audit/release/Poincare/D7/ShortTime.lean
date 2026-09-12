import Poincare.D7.ShortTime.Basic
import Poincare.D7.ShortTime.ODE
import Poincare.D7.ShortTime.MatrixDeriv
import Poincare.D7.ShortTime.Gauge
import Poincare.D7.ShortTime.Equivalence
import Poincare.D7.ShortTime.Statements
import Poincare.D7.ShortTime.Example

/-!
# Poincare.D7.ShortTime

Umbrella module for the `D7-hamilton-short-time` layer:

* `Poincare.D7.ShortTime.Basic` — the finite-dimensional matrix model:
  `RicciFlowData` (Ricci operator with gauge covariance, metric path, Ricci flow equation),
  `deTurckRHS` (the modified Ricci--DeTurck right-hand side), and `DeTurckCertificate`
  (gauge family, inverse gauge family, gauge field, modified flow equation, initial conditions),
  with every field explicit;
* `Poincare.D7.ShortTime.ODE` — the Lipschitz interface `LipschitzVectorField` and the
  uniqueness theorem `LipschitzVectorField.solution_unique` for the ODE `y' = v(t, y)`, plus the
  specialization `RicciLipschitzInterface` to the Ricci flow vector field;
* `Poincare.D7.ShortTime.MatrixDeriv` — the entrywise calculus rules on matrices
  (`hasDerivAt_transpose`, `hasDerivAt_mul`, and arithmetic wrappers);
* `Poincare.D7.ShortTime.Gauge` — the gauge algebra: the pullback identity, the gauge correction
  completing the modified right-hand side to the Ricci flow right-hand side, and the algebraic
  core `gauge_pullback_deTurckRHS` of the DeTurck equivalence;
* `Poincare.D7.ShortTime.Equivalence` — the kernel-checked algebraic equivalence: the inverse
  gauge ODE is derived, the pullback of a DeTurck solution solves the Ricci flow, the pullback is
  identified with the Ricci flow datum under the Lipschitz interface, and the reverse direction
  recovers a DeTurck solution from a Ricci flow;
* `Poincare.D7.ShortTime.Statements` — the state-only `Prop`s
  `DeTurckShortTimeExistence` and `DeTurckToRicciConversion` over the abstract continuum
  interface `DeTurckParabolicProblem`, the finite-dimensional consistency witness, and the
  named missing-dependency ledger `quasilinearParabolicDependencies`;
* `Poincare.D7.ShortTime.Example` — non-vacuity witnesses: the Einstein model with the explicit
  solution `exp(-2ct) • G₀`, the trivial gauge certificate, and a nonzero-gauge nilpotent
  certificate with explicit `3 × 3` matrices.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in this layer. The
analytic content of Hamilton's 1982 theorem is stated but not proved; see
`Poincare.D7.ShortTime.Statements`.
-/
