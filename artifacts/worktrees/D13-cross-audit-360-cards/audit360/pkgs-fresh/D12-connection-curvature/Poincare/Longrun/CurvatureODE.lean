import Poincare.Longrun.CurvatureODE.State
import Poincare.Longrun.CurvatureODE.Evolution
import Poincare.Longrun.CurvatureODE.ScalarODE
import Poincare.Longrun.CurvatureODE.Invariant
import Poincare.Longrun.CurvatureODE.Monotonicity
import Poincare.Longrun.CurvatureODE.Bridge

/-!
# Poincare.Longrun.CurvatureODE

Umbrella module for the `D2-ricci-ode-cluster` finite-dimensional Ricci-flow-inspired ODE
cluster. It consumes the accepted `D2-geometry-foundation` result
(`Poincare.Longrun.Geometry`) and contains:

* `Poincare.Longrun.CurvatureODE.State` — the finite state `ι → ℝ`, its diagonal
  endomorphism on a `MetricData`, the scalar functional, and the checked identity
  `scalarOfState (stateOfCurvature m K) = scalarCurvature K m.toScalarContractionData`;
* `Poincare.Longrun.CurvatureODE.Evolution` — the finite reaction field
  `Fᵢ(lam) = aᵢ lamᵢ² + gᵢ(lam)` with nonnegative reaction, the continuous-time evolution
  relation, and its explicit-Euler discrete analogue;
* `Poincare.Longrun.CurvatureODE.ScalarODE` — the scalar mean-value/Grönwall
  sign-preservation lemmas that power the invariant and monotone theorems;
* `Poincare.Longrun.CurvatureODE.Invariant` — the checked invariant-region theorem: the
  nonnegative orthant is forward-invariant (and every component is nondecreasing);
* `Poincare.Longrun.CurvatureODE.Monotonicity` — the checked scalar monotonicity theorem:
  the weighted scalar functional `∑ i, wᵢ lamᵢ` is nondecreasing for `wᵢ ≥ 0`;
* `Poincare.Longrun.CurvatureODE.Bridge` — the **exact missing bridge** from the finite ODE
  to tensor Ricci flow, exposed as an explicit `Prop`-valued interface
  (`TensorRicciFlowODERealization` / `TensorRicciFlowODEBridge`) with no proof and no axiom,
  together with the conditional transfer theorems to the tensor-level diagonal Ricci
  contraction and scalar curvature.

Honest boundary: this is a finite-dimensional model, not Hamilton's theorem. The Laplacian
term and the exact `Rm#` coefficients are not modeled; the missing tensor-level statements
are explicit hypotheses in `Poincare.Longrun.CurvatureODE.Bridge`. No `sorry`, `axiom`,
`unsafe`, `native_decide`, or `proof_wanted` occurs anywhere in the cluster.
-/
