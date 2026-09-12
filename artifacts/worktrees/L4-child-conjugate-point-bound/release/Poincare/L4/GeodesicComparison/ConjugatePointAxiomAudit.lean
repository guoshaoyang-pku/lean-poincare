/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — fail-closed kernel axiom audit for the conjugate-point endpoint bound

This file contains two things:

1. `endpoint_bound_acceptance_lock` — the acceptance sentence, re-stated *independently* of
   the implementation file.  It compiles only if `conjugate_point_bound` has exactly the
   claimed type (same hypotheses, conclusion `T ≤ π/√K`), so it locks the statement against
   silent weakening.
2. `#print axioms` queries for every declaration authored in `ConjugatePointEndpoint.lean`
   together with the comparison, engine and model lemmas it consumes.

The verification script `tools/l4cp_verify.py` parses the query output fail-closed:

* every declaration in the expected list must be present in the output;
* the queried list in this file must be *exactly* the expected fully-qualified set;
* every axiom cone must be a subset of `{propext, Classical.choice, Quot.sound}`;
* a real negative control (`negcontrol/EndpointNegativeControl.lean`, containing `sorry`
  and a declared `axiom`) must be rejected by the same acceptance predicate.

The file contains no `sorry`, no `axiom` declaration and no mathematical content beyond the
statement lock; it only queries the kernel.
-/
import Poincare.L4.GeodesicComparison.ConjugatePointEndpoint

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- **Acceptance statement lock.**  The acceptance sentence for
`L4-child-conjugate-point-bound`, written out independently: if `k ≥ K > 0` on `(0,T)`,
`u 0 = 0`, `u' 0 = 1`, `u > 0` on `(0,T]`, and the analytic normalization hypotheses of
`rauch_upper_of_jacobi_constCurv` hold, then `T ≤ π/√K`. -/
theorem endpoint_bound_acceptance_lock {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 < K) (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hBmodel : (K * max (1 / Real.sqrt K) T) * t₀ ≤ 1 / 2) :
    T ≤ Real.pi / Real.sqrt K :=
  conjugate_point_bound hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hpos hK hk hBmodel

end Poincare.L4.GeodesicComparison

/-! ## Authored declarations (`ConjugatePointEndpoint.lean` + statement lock) -/

#print axioms Poincare.L4.GeodesicComparison.JacobiSolutionOn.mono
#print axioms Poincare.L4.GeodesicComparison.basePoint_lt_firstZero
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_strict
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound
#print axioms Poincare.L4.GeodesicComparison.endpoint_bound_acceptance_lock
#print axioms Poincare.L4.GeodesicComparison.jacobiSolTwo_second_deriv_bound_four
#print axioms Poincare.L4.GeodesicComparison.jacobiSolTwo_pos_Ioc_two
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K1
#print axioms Poincare.L4.GeodesicComparison.conjugate_point_bound_witness_k2_K2
#print axioms Poincare.L4.GeodesicComparison.pi_div_sqrt_two_lt_pi
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_iff
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_two_pos_iff
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_two_firstZero
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_two_not_pos_at_firstZero

/-! ## Consumed comparison lemmas (`ConstantCurvatureRauch.lean`, `RauchBridge.lean`) -/

#print axioms Poincare.L4.GeodesicComparison.jacobi_le_constCurvModel
#print axioms Poincare.L4.GeodesicComparison.rauch_upper_of_jacobi_constCurv
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_jacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_pos_of_nonneg
#print axioms Poincare.L4.GeodesicComparison.jacobiSol_second_deriv_bound
#print axioms Poincare.L4.GeodesicComparison.euclideanNormalizedOn_of_jacobi

/-! ## Consumed singular Riccati engine (D12) -/

#print axioms Poincare.D12.ComparisonGeodesics.riccati_le_of_singular_normalization

/-! ## Consumed constant-curvature model (D10) -/

#print axioms Poincare.D10.jacobiSolSphere_firstZero
#print axioms Poincare.D10.jacobiSol_of_pos
#print axioms Poincare.D10.jacobiSol_zero
#print axioms Poincare.D10.jacobiDeriv_zero
#print axioms Poincare.D10.jacobiSolSphere_pos
#print axioms Poincare.D10.continuous_jacobiSol
