import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.MeasureTheory.Integral.IntegrableOn
noncomputable section
open Set Filter
open scoped Topology
namespace Poincare.D12.ComparisonGeodesics

set_option pp.all true in
#check fun {u du ddu : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAtR u (du t) t) (hdu : HasDerivAtR du (ddu t) t) (hu0 : u t ≠ 0) =>
  hdu.div hu hu0

set_option pp.all true in
#check fun {u₁ du₁ u₂ du₂ : ℝ → ℝ} {t : ℝ}
    (h₁ : HasDerivAtR u₁ (du₁ t) t) (h₂ : HasDerivAtR u₂ (du₂ t) t) =>
  h₁.sub h₂

end Poincare.D12.ComparisonGeodesics
