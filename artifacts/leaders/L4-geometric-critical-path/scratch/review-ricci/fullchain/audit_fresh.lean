/-
Independent adversarial-review axiom audit for the three L4-child-ricci-to-doubling modules
staged in the leader release tree.  Read-only scratch file: imports the three modules and
prints the kernel axiom cone of every top-level declaration.
-/
import Poincare.L4.Compactness.RicciToDoubling
import Poincare.L4.Compactness.RicciToDoublingHyperbolic
import Poincare.L4.Compactness.RicciToDoublingHyperbolicClosedForm

-- ===== RicciToDoubling.lean (13 public declarations) =====
#print axioms Poincare.L4.Compactness.euclidModel_volumeRatio_closedForm
#print axioms Poincare.L4.Compactness.euclidModel_volume_doubling_closedForm
#print axioms Poincare.L4.Compactness.euclid_volume_ratio_le_of_ricci_nonneg
#print axioms Poincare.L4.Compactness.euclid_volumeRatio_div_le_of_ricci_nonneg
#print axioms Poincare.L4.Compactness.euclid_volume_doubling_of_ricci_nonneg
#print axioms Poincare.L4.Compactness.euclidModel_hypotheses_witness
#print axioms Poincare.L4.Compactness.radialVolume_euclidModel_one_doubling_witness
#print axioms Poincare.L4.Compactness.radialVolume_euclidModel_one_value_witness
#print axioms Poincare.L4.Compactness.IsRadialBallMeasure
#print axioms Poincare.L4.Compactness.isRadialBallMeasure_real_witness
#print axioms Poincare.L4.Compactness.coveringNumber_le_measure_ratio_of_radialBallMeasure
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_radialBallMeasure_doubling
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_ricci_nonneg_radialBallMeasure

-- ===== RicciToDoublingHyperbolic.lean (21 public + 2 private) =====
#print axioms Poincare.L4.Compactness.hypModelK
#print axioms Poincare.L4.Compactness.hypModelA
#print axioms Poincare.L4.Compactness.hypModelM
#print axioms Poincare.L4.Compactness.hypModelDm
#print axioms Poincare.L4.Compactness.hypModelDA
-- the two `private` helpers are not nameable from an importing module, so their cones are
-- collected directly from the environment by the meta command below
open Lean Elab Command in
run_cmd do
  let base := Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "Poincare") "L4") "Compactness") "RicciToDoublingHyperbolic") "0") "Poincare") "L4") "Compactness"
  for s in ["sinh_mul_cosh_sub_sinh_nonneg", "sinh_mul_cosh_sub_sinh_le"] do
    let n := base.str s
    let axs ← collectAxioms n
    logInfo m!"PRIVATE {n} depends on axioms: {axs.toList}"
#print axioms Poincare.L4.Compactness.coth_sub_inv_abs_le_one
#print axioms Poincare.L4.Compactness.hypModelM_hasDerivAt
#print axioms Poincare.L4.Compactness.hypModelM_riccati
#print axioms Poincare.L4.Compactness.hypModelM_contOn
#print axioms Poincare.L4.Compactness.hypModelM_normalized
#print axioms Poincare.L4.Compactness.hypModelA_hasDerivAt
#print axioms Poincare.L4.Compactness.hypModelA_contOn
#print axioms Poincare.L4.Compactness.hypModelA_pos
#print axioms Poincare.L4.Compactness.hypModelA_zero
#print axioms Poincare.L4.Compactness.hypModelA_logDeriv
#print axioms Poincare.L4.Compactness.hyp_volume_ratio_le_of_ricci_ge
#print axioms Poincare.L4.Compactness.hyp_volume_doubling_of_ricci_ge
#print axioms Poincare.L4.Compactness.hypModel_doubling_witness
#print axioms Poincare.L4.Compactness.hypModelA_one_one_volume
#print axioms Poincare.L4.Compactness.hypModelA_one_one_doubling
#print axioms Poincare.L4.Compactness.hyp_volume_doubling_d1_k1

-- ===== RicciToDoublingHyperbolicClosedForm.lean (15 public) =====
#print axioms Poincare.L4.Compactness.sinhPowIntegral
#print axioms Poincare.L4.Compactness.sinhPowIntegral_zero
#print axioms Poincare.L4.Compactness.sinhPowIntegral_one
#print axioms Poincare.L4.Compactness.sinhPowIntegral_add_two
#print axioms Poincare.L4.Compactness.sinhPowIntegral_apply_zero
#print axioms Poincare.L4.Compactness.sinhPowIntegral_hasDerivAt
#print axioms Poincare.L4.Compactness.sinhPowIntegral_integral
#print axioms Poincare.L4.Compactness.sinhPowIntegral_two
#print axioms Poincare.L4.Compactness.sinhPowIntegral_three
#print axioms Poincare.L4.Compactness.hypModelA_volume_closedForm
#print axioms Poincare.L4.Compactness.hypModel_volumeRatio_closedForm
#print axioms Poincare.L4.Compactness.hypModelA_one_one_volume_closedForm
#print axioms Poincare.L4.Compactness.hypModel_volumeRatio_d2_closedForm
#print axioms Poincare.L4.Compactness.hyp_volume_ratio_le_of_ricci_ge_closedForm
#print axioms Poincare.L4.Compactness.hyp_volume_doubling_closedForm
