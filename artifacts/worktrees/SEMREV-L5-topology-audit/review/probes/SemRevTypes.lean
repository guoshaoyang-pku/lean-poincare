/- SEMREV-L5 independent replay: exact types of the declarations cited by the L5 card. -/
import Poincare.D10.TriangulationLowDim.Complex
import Poincare.D10.TriangulationLowDim.Moise
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.TriangulationTopology.DiskGluing
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D12.TriangulationTopology.TwoHemisphereInstance
import Poincare.D12.VolumeIBP.Audit
import Poincare.D13.CriticalPathReview.NegControl
import Poincare.D7.Limit.Blocked
import Poincare.D7.Limit.Convergence
import Poincare.D7.Recognition.All
import Poincare.D7.SurgeryFlow.Basic
import Poincare.D7.SurgeryFlow.Statements
import Poincare.Longrun.Evolution.Bridge
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.Topology.Stage6Bridge
import Poincare.VKPort.HatcherLib.Ch1.VanKampen

set_option autoImplicit false
set_option pp.universes true
set_option maxHeartbeats 0
-- card-class: proved_unconditional (card section 5)
#check @Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere
-- card-class: proved_unconditional (card section 5)
#check @Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere
-- card-class: proved_unconditional (card section 5)
#check @Poincare.D12.SurgeryRecognition.sphereConnectSum_transported
-- card-class: proved_but_unconsumed (card section 5)
#check @Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere
-- card-class: constructed_bridge (card section 5)
#check @Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2
-- card-class: proved_unconditional (card section 5)
#check @Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap
-- card-class: proved_unconditional (card section 5)
#check @Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient
-- card-class: conditional_implication (card section 5)
#check @Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition
-- card-class: conditional_implication (card section 5)
#check @Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses
-- card-class: conditional_implication_terminal (card section 5)
#check @Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses
-- card-class: abbrev_empty_cone (card section 5)
#check @Poincare.D12.SurgeryRecognition.AntipodalGroup
-- card-class: conditional_implication (card section 5)
#check @Poincare.D7.Recognition.stage6Target_of_certificates
-- card-class: upstream_proved (card section 5)
#check @HatcherLib.vanKampenMap
-- card-class: upstream_proved (card section 5)
#check @HatcherLib.vanKampenMap_surjective
-- card-class: upstream_proved (card section 5)
#check @HatcherLib.vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected
-- card-class: proved_unconditional (card section 6)
#check @Poincare.D12.TriangulationTopology.alexanderHomeo
-- card-class: proved_unconditional (card section 6)
#check @Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff
-- card-class: proved_unconditional (card section 6)
#check @Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere
-- card-class: proved_unconditional (card section 6)
#check @Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply
-- card-class: proved_unconditional (card section 6)
#check @Poincare.D12.TriangulationTopology.sphereOfTwoDisks
-- card-class: proved_unconditional (card section 6)
#check @Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance
-- card-class: statement_only_prop (card section 6)
#check @Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem
-- card-class: structure (card section 6)
#check @Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex
-- card-class: statement_only_structure (card section 7)
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses
-- card-class: statement_only_prop (card section 7)
#check @Poincare.D7.SurgeryFlow.missingFullNeckAnalysis
-- card-class: statement_only_prop (card section 7)
#check @Poincare.D7.SurgeryFlow.missingExtinctionTheorem
-- card-class: statement_only_prop (card section 7)
#check @Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem
-- card-class: structure (card section 7)
#check @Poincare.D7.SurgeryFlow.ExtinctionData
-- card-class: statement_only_structure (card section 7)
#check @Poincare.Longrun.Surgery.ExtinctionTheorem
-- card-class: statement_only_structure (card section 7)
#check @Poincare.Longrun.Surgery.MissingInputs
-- card-class: vacuous_P_implies_P (card section 7)
#check @Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected
-- card-class: statement_only_prop (card section 8)
#check @Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman
-- card-class: statement_only_prop (card section 8)
#check @Poincare.Longrun.Evolution.FiniteMeshConvergence
-- card-class: statement_only_structure (card section 8)
#check @Poincare.Longrun.Evolution.PerelmanEvolutionBoundary
-- card-class: structure (card section 8)
#check @Poincare.Longrun.Evolution.PerelmanApproximation
-- card-class: statement_only_prop (card section 8)
#check @Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity
-- card-class: model_prop (card section 8)
#check @Poincare.D7.Limit.HeatMeshConvergence
-- card-class: model_conditional_theorem (card section 8)
#check @Poincare.D7.Limit.heatMeshConvergence_of_stability
-- card-class: model_conditional_theorem (card section 8)
#check @Poincare.D7.Limit.finiteMeshConvergence_of_stability
-- card-class: statement_only_prop (card section 8)
#check @Poincare.D7.Limit.HeatMeshConvergenceTheorem
-- card-class: hypothesis_predicate (card section 8)
#check @Poincare.D7.Limit.IsRefiningMesh
-- card-class: hypothesis_predicate (card section 8)
#check @Poincare.D7.Limit.HasVanishingError
-- card-class: circular_conclusion_equivalent (card section 9a)
#check @Poincare.Longrun.Topology.stage6Target_of_sphereRecognition
-- card-class: circular_conclusion_equivalent (card section 9a)
#check @Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold
-- card-class: proved_bridge_defeq (card section 9a)
#check @Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition
-- card-class: statement_only_alias (card section 9a)
#check @Poincare.Stage6.poincareConjectureTopologicalThree
-- card-class: registered_negative_control (card section 2)
#check @d12NegControlBadAxiom
-- card-class: registered_negative_control (card section 2)
#check @d12NegControlBadTheorem
-- card-class: registered_negative_control (card section 2)
#check @Poincare.D12.VolumeIBP.Audit.negativeControl
-- card-class: registered_negative_control (card section 2)
#check @Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom
-- card-class: registered_negative_control (card section 2)
#check @Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem
