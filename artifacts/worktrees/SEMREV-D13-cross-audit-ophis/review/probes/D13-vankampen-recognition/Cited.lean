/- SEMREV cited-declaration compile check: every cited name must #check. -/
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.SurgeryRecognition.Audit
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces
import Poincare.D12.SurgeryRecognition.SphereOfSpheres
import Poincare.D13.VanKampenRecognition.All
import Poincare.D13.VanKampenRecognition.Audit
import Poincare.D13.VanKampenRecognition.FreeProduct
import Poincare.D13.VanKampenRecognition.SR4Closure
import Poincare.D13.VanKampenRecognition.SphereVanKampen
import Poincare.D13.VanKampenRecognition.Stereographic
import Poincare.D7.Canonical.Basic
import Poincare.D7.Canonical.Classification
import Poincare.D7.Canonical.Curvature
import Poincare.D7.Canonical.Models
import Poincare.D7.Canonical.Statements
import Poincare.D7.Compactness.Basic
import Poincare.D7.Curvature.Basic
import Poincare.D7.Curvature.Example
import Poincare.D7.Curvature.Sectional
import Poincare.D7.Curvature.Symmetries
import Poincare.D7.Recognition.All
import Poincare.D7.Recognition.Assembly
import Poincare.D7.Recognition.Audit
import Poincare.D7.Recognition.Basic
import Poincare.D7.Recognition.Homeomorphism
import Poincare.D7.Recognition.Probe
import Poincare.D7.RicciScalar
import Poincare.D7.RicciScalar.Basic
import Poincare.D7.RicciScalar.Bridge
import Poincare.D7.RicciScalar.Example
import Poincare.D7.RicciScalar.Product
import Poincare.D7.RicciScalar.Scalar
import Poincare.D7.RicciScalar.Variation
import Poincare.D7.ShortTime.Basic
import Poincare.D7.ShortTime.Equivalence
import Poincare.D7.ShortTime.Gauge
import Poincare.D7.ShortTime.MatrixDeriv
import Poincare.D7.ShortTime.ODE
import Poincare.D7.ShortTime.Statements
import Poincare.VKPort.HatcherLib.Ch1.AlgebraicConstructions
import Poincare.VKPort.HatcherLib.Ch1.BasicConstructions
import Poincare.VKPort.HatcherLib.Ch1.VanKampen
import Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSubdivision
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenWordCalculus
import Poincare.VKPort.HatcherLib.VKProbe

set_option autoImplicit false

#check @Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2
#print axioms Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2
#check @Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete
#print axioms Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete
#check @Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3
#print axioms Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3
#check @Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2
#print axioms Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2
#check @Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates
#print axioms Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates
#check @Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses
#print axioms Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses
