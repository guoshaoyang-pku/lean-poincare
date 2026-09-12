import HatcherLib
import KleinerLott

/-!
# Compile-time API probes: algebraic topology (M4 topology lane)

`HatcherLib` (Hatcher, *Algebraic Topology*) supplies fundamental groups,
covering-space theory, homotopy equivalences and CW/attaching-space material
that the local topology lane (L5) needs for the recognition step.  The probes
record the names that exist; no claim about the Poincaré conjecture itself is
made or implied.
-/

namespace UpstreamAdapters.Probes.Topology

-- Fundamental group and simple connectivity
#check @HatcherLib.fundamentalGroup_mapOfEq_rfl
#check @HatcherLib.fundamentalGroup_basepointTransport_comp_map
#check @HatcherLib.fundamentalGroupProdMulEquiv
#check @HatcherLib.fundamentalGroupPiMulEquiv
#check @HatcherLib.simplyConnected_iff_unique_path_class
#check @HatcherLib.simplyConnected_paths_homotopic
#check @HatcherLib.simplyConnectedSpace_of_pathConnectedOpenCover

-- Covering spaces
#check @HatcherLib.IsUniversalCoveringMap.simplyConnectedSpace
#check @HatcherLib.coveringPiOneImageSubgroup_eq_bot_of_simplyConnected
#check @HatcherLib.UniversalCoverConstruction.universalCover_simplyConnectedSpace

-- Homotopy equivalences, mapping cylinders, attaching spaces
#check @HatcherLib.attachingSpace_homotopyEquiv
#check @HatcherLib.attachingSpace_homotopyEquiv_rel
#check @HatcherLib.collapseMk_homotopyEquiv
#check @HatcherLib.collapseMk_homotopyEquiv_of_cwPair
#check @HatcherLib.homotopy_equiv_iff_mcylDeformationRetract
#check @HatcherLib.homotopyEquiv_iff_common_deformationRetract
#check @HatcherLib.DeformationRetract.homotopyEquiv
#check @HatcherLib.homotopyEquivPiOneMulEquiv
#check @HatcherLib.homotopyEquivPiOneMulEquiv_apply

-- Kleiner-Lott smooth Ricci-flow interface used by the point-selection argument
#check @KleinerLott.LeviCivitaConnectionData
#check @KleinerLott.RiemannCurvatureTensorAt
#check @KleinerLott.inducedRiemannianEDist

end UpstreamAdapters.Probes.Topology
