import Poincare.D7.TensorLaplacian.Basic
import Poincare.D7.TensorLaplacian.Commutation
import Poincare.D7.TensorLaplacian.Evolution
import Poincare.D7.TensorLaplacian.Example
import Poincare.D7.TensorLaplacian.Blocked
import Poincare.D7.TensorLaplacian.Probe

/-!
# Poincare.D7.TensorLaplacian

Umbrella module for the `D7-tensor-laplacian` layer:

* `Poincare.D7.TensorLaplacian.Basic` — `TensorConnectionData`, tensor data with a covariant
  derivative and curvature action over the D7 connection layer, the stated curvature certificate,
  the derived first-pair antisymmetry `curvature_skew`, and the **rough Laplacian**
  `Δ = ∑ᵢ ∇_{eᵢ}∇_{eᵢ}` with its linearity lemmas;
* `Poincare.D7.TensorLaplacian.Commutation` — the per-direction commutator identity, the general
  commutation formula `Δ(∇_X s) - ∇_X(Δ s) = ∑ᵢ (...)` under the curvature certificate, the
  commuting-frame and parallel-curvature specializations
  `Δ(∇_X s) - ∇_X(Δ s) = 2 • ∑ᵢ R(eᵢ,X)(∇ᵢ s)`, the stated `RicciCommutationCertificate` and
  `ScalarCurvatureCommutationCertificate` giving the Ricci form and the frame trace
  `(2 * scal) • s`, and the flat sanity check;
* `Poincare.D7.TensorLaplacian.Evolution` — the D7 quantities `ricciNormSq`, `traceH`,
  `pairingH`, `ricciFlowVelocity`, the `ScalarEvolutionCertificate` with the stated flow equation
  `∂ₜ g = -2 Ric`, the Lichnerowicz trace variation and the contracted Bianchi identity, and the
  **exact identity** `∂ₜ scal = Δ scal + 2 |Ric|²` (`scalarDeriv_eq`, `scalar_evolution`,
  `scalar_evolution_iff`);
* `Poincare.D7.TensorLaplacian.Example` — concrete inhabitants (`scalarTensorData`,
  `vectorTensorData`, `prodTensorData`), the nonzero-curvature `so(3)` witnesses
  (`so3_ricciNormSq_pos`, `so3EvolutionCertificate`, `so3_evolution_rhs_pos`,
  `so3_vector_curvature_witness`), and the negative control
  `wrongBianchi_identity_fails` showing the Bianchi certificate is essential;
* `Poincare.D7.TensorLaplacian.Blocked` — the state-only smooth `Prop`s
  (`SmoothCurvatureCertificateStatement`, `SmoothCommutationStatement`,
  `SmoothFrameTraceCommutationStatement`, `SmoothScalarEvolutionStatement`) with six named
  blockers and the exact missing mathlib dependencies;
* `Poincare.D7.TensorLaplacian.Probe` — the compilable mathlib/D7 API probe.
-/
