import Poincare.D7.RicciScalar.Basic
import Poincare.D7.RicciScalar.Scalar
import Poincare.D7.RicciScalar.Product
import Poincare.D7.RicciScalar.Variation
import Poincare.D7.RicciScalar.Example
import Poincare.D7.RicciScalar.Bridge

/-!
# Poincare.D7.RicciScalar

Umbrella module for the `D7-ricci-scalar-curvature` layer:

* `Poincare.D7.RicciScalar.Basic` — Ricci curvature as the trace of the `(1,3)` curvature over a
  finite-dimensional basis (`ricciTrace`), basis-independence, the `ricciTensor` alias,
  compatibility with the D2 `CurvatureOperator.ricci`, and symmetry for metric-compatible
  torsion-free data;
* `Poincare.D7.RicciScalar.Scalar` — scalar curvature as the metric trace of the raised Ricci
  endomorphism (`scalarMetricTrace`), the orthonormal-basis sum (`scalarBasisSum`),
  basis-independence of both traces, and compatibility with the D2
  `CurvatureOperator.scalarCurvature`;
* `Poincare.D7.RicciScalar.Product` — the product metric-compatible torsion-free datum
  (`prodData`) and the product formula `scal(D₁ × D₂) = scal(D₁) + scal(D₂)`;
* `Poincare.D7.RicciScalar.Variation` — the stated flow equation, the two exact missing
  dependencies (Levi-Civita evolution, commutation of `d/dt` with the trace), the scalar
  variation statement, and the kernel-checked reduction of the scalar variation to the
  trace-commutation dependency;
* `Poincare.D7.RicciScalar.Example` — concrete non-vacuity witnesses on the `so(3)` model
  (`scal = 3/2`, basis-independence witness, product formula `3 = 3/2 + 3/2`);
* `Poincare.D7.RicciScalar.Bridge` — D2 linearity/consistency restatements and the blocked
  Perelman-ledger manifold realization.
-/
