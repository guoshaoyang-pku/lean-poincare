import Poincare.D12.ConnectionCurvature.MilnorLeviCivita
import Poincare.D12.ConnectionCurvature.RicciSymmetry
import Poincare.D12.ConnectionCurvature.ChartLeviCivita
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaForm
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth
import Poincare.D12.ConnectionCurvature.ConformalChartModel
import Poincare.D12.ConnectionCurvature.SoThreeModel
import Poincare.D12.ConnectionCurvature.ChartModel1D

/-! # Poincare.D12.ConnectionCurvature

D12-connection-curvature: metric/connection geometry connected to D7 tensor data.

* `MilnorLeviCivita`: unconditional abstract Levi-Civita existence (Milnor's formula),
  closing the named blocker `LeviCivitaExistenceStatement`.
* `RicciSymmetry`: Ricci symmetry for any abstract Levi-Civita connection; Ricci/scalar
  contraction formulas in any orthonormal frame (D7/Stage1 `CurvatureOperator`).
* `ChartLeviCivita`: Christoffel symbols from chart metric coefficients `(g, g⁻¹, d)`
  with the torsion and `∇g = 0` coefficient identities.
* `ChartLeviCivitaForm`: the chart connection on vector coefficients, metric
  compatibility for all coefficient vectors, and the bridge to the D7/Stage1
  `CurvatureOperator`.
* `ChartLeviCivitaSmooth`: the smooth (x-dependent) chart construction — smooth
  Christoffel family, the field-level connection with smoothness, Leibniz rule,
  torsion-freeness and metric compatibility against the actual Frechet derivative of
  the field pairing.
* `ConformalChartModel`: the 2-dimensional conformal chart model `g = (1+x₀²)·δ` with
  **nonzero curvature** (`R¹₂₁₂(0) = -1 ≠ 0`, Gauss curvature `K(0) = -1`) — the
  chart-model companion of the flat 1D model, computed from the metric coefficients
  through the proved Christoffel formulas.
* `SoThreeModel`: the so(3) model with nonzero curvature and nonzero Ricci — concrete
  non-vacuity of the Milnor machinery.
* `ChartModel1D`: the nonconstant 1D chart model (nonzero Christoffel connection,
  honest curvature vanishing in dimension 1).
-/
