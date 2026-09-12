import Poincare.D12.ComparisonGeodesics.Definitions
noncomputable section
open Set Filter
open scoped Topology
namespace Poincare.D12.ComparisonGeodesics

example {δ p M : ℝ → ℝ} {δ' : ℝ} {t : ℝ}
    (hδd : HasDerivAtR δ δ' t) (hM : HasDerivAtR M (p t * M t) t) :
    HasDerivAtR (fun s => δ s * M s) ((δ' + p t * δ t) * M t) t := by
  convert hδd.mul hM using 1
  · ext s
    rfl
  · ring

end Poincare.D12.ComparisonGeodesics
