import PetersenLib

/-!
# Compile-time API probes: PetersenLib (U1, U3)

Petersen's *Riemannian Geometry* development.  It is deliberately kept in a
**separate Lean library** from `UpstreamAdapters`: both `PetersenLib` and
`Shared` call `register_simp_attr metric_simp`, so a single module importing
both fails with

```
import PetersenLib.Foundations.Attributes failed,
environment already contains 'Parser.Attr.metric_simp' from Shared.Util.Attributes
```

which is recorded as an M2 compatibility finding.  A consumer must pick one
family per module until upstream renames or removes the duplicate attribute.
-/

namespace UpstreamAdaptersPetersen.Probes

-- U1: curvature tensor, coordinates, index lowering, smoothness
#check @PetersenLib.curvatureTensorTypes
#check @PetersenLib.curvatureTensor_coordinates
#check @PetersenLib.curvatureTensor_indexLowering
#check @PetersenLib.contMDiff_curvatureTensorFour
#check @PetersenLib.curvatureTensor_zero_first
#check @PetersenLib.curvatureTensor_derivation

-- U3: exponential map, geodesics, segment minimizers
#check @PetersenLib.expMap
#check @PetersenLib.expMap_zero
#check @PetersenLib.expMap_smul
#check @PetersenLib.expMap_localDiffeomorphism
#check @PetersenLib.isGeodesicOn_of_isChartGeodesicOn
#check @PetersenLib.segment_isGeodesic
#check @PetersenLib.energyLocalMinimum_isGeodesic

end UpstreamAdaptersPetersen.Probes
