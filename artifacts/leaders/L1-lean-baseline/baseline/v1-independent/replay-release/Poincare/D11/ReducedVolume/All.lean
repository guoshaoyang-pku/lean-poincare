import Poincare.D11.ReducedVolume.Basic
import Poincare.D11.ReducedVolume.StraightRays
import Poincare.D11.ReducedVolume.Volume
import Poincare.D11.ReducedVolume.Statements

/-!
# Poincare.D11.ReducedVolume.All

Umbrella module for the `D11-reduced-volume-euclidean` layer.  It imports the four content
modules:

* `Poincare.D11.ReducedVolume.Basic` — the flat metric-flow interface, the flat `L`-length
  `∫ √τ (|γ'|² + R) dτ` with `R = 0`, and the reduced distance from the heat-kernel
  asymptotics (`ℓ = |x|²/(4τ)`);
* `Poincare.D11.ReducedVolume.StraightRays` — the `L`-geodesics from the origin are exactly
  the straight rays (minimality and uniqueness, unconditional);
* `Poincare.D11.ReducedVolume.Volume` — the reduced-volume integrand coincides with the
  Gaussian; the reduced volume is constant `1`;
* `Poincare.D11.ReducedVolume.Statements` — the named monotonicity-theorem `Prop`, the
  manifold reduced-volume interface consumed by `D7-reduced-length-volume`, and the
  field-by-field Euclidean instantiation.
-/
