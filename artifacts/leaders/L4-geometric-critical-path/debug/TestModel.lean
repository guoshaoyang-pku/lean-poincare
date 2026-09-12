import Poincare.D12.ComparisonGeodesics.Definitions
import Poincare.D10.JacobiConstantCurvature.ODE
import Poincare.D10.JacobiConstantCurvature.Comparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

example (K t : ℝ) : HasDerivAtR (jacobiSol K) (jacobiDeriv K t) t := by
  exact hasDerivAt_jacobiSol K t

example (K t : ℝ) : HasDerivAtR (jacobiDeriv K) (-(K * jacobiSol K t)) t := by
  exact hasDerivAt_jacobiDeriv K t

example (K : ℝ) : ContinuousOn (jacobiDeriv K) (Set.Icc 0 1) := by
  exact (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn
