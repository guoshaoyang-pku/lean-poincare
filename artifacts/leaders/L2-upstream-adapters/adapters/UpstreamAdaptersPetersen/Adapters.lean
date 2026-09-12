import PetersenLib

/-!
# Adapter aliases for PetersenLib

`alias` copies the upstream type and proof term, so these names cannot weaken or
strengthen the upstream statements.  Kept in the `UpstreamAdaptersPetersen`
library because PetersenLib cannot share a Lean environment with `Shared`
(duplicate `metric_simp` attribute registration).
-/

namespace UpstreamAdaptersPetersen.Adapters

alias curvatureTensor_indexLowering := PetersenLib.curvatureTensor_indexLowering
alias curvatureTensor_coordinates := PetersenLib.curvatureTensor_coordinates
alias contMDiff_curvatureTensorFour := PetersenLib.contMDiff_curvatureTensorFour
alias curvatureTensor_derivation := PetersenLib.curvatureTensor_derivation
alias expMap_localDiffeomorphism := PetersenLib.expMap_localDiffeomorphism
alias expMap_smul := PetersenLib.expMap_smul
alias expMap_zero := PetersenLib.expMap_zero
alias isGeodesicOn_of_isChartGeodesicOn := PetersenLib.isGeodesicOn_of_isChartGeodesicOn
alias segment_isGeodesic := PetersenLib.segment_isGeodesic
alias energyLocalMinimum_isGeodesic := PetersenLib.energyLocalMinimum_isGeodesic

-- Round 5: the remaining inventoried U1/U2/U3/U4 entry points.
alias curvatureTensorTypes := PetersenLib.curvatureTensorTypes
alias curvatureTensor_zero_first := PetersenLib.curvatureTensor_zero_first
alias curvatureTensor_eq_ricci_identity := PetersenLib.curvatureTensor_eq_ricci_identity
alias expMap := PetersenLib.expMap
alias RicciCurvature := PetersenLib.RicciCurvature
alias IsJacobiField := PetersenLib.IsJacobiField
alias ConjugatePoint := PetersenLib.ConjugatePoint
alias myersRicciDiameterBound_of_ricciLowerBound :=
  PetersenLib.myersRicciDiameterBound_of_ricciLowerBound
alias leviCivita := PetersenLib.RiemannianMetric.leviCivita
alias koszul := PetersenLib.RiemannianConnection.koszul

end UpstreamAdaptersPetersen.Adapters
