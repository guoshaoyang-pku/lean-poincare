/-
D13 adapter probe: Hatcher, *Algebraic Topology* — CW complexes, covering
spaces, spheres and simple connectivity.  Upstream: frenzymath/Poincare-Conjecture
@ bb91a091f0b968f8bbe8d861e025a88d82b161be, package `formalized-sources/Hatcher`
(HatcherLib), pinned to Lean v4.32.1 + mathlib 520045ab.  Read-only consumer.
-/
import HatcherLib.Ch0.CellComplexes
import HatcherLib.Ch1.CoveringSpaces
import HatcherLib.Ch1.Sphere

open HatcherLib

/-! ## CW complexes -/

#check @IsCWComplex
#check @CharacteristicMap
#check @IsFiniteDimensionalCW
#check @IsCWSubcomplex
#check @IsCWPair
#check @IsCWSubcomplex.isClosed
#check @IsCWPair.isClosed
#check @Skeleton
#check @CWDimension
#check @cwDimension_le_of_skeleton_eq

/-! ## Covering spaces -/

#check @CoveringMap
#check @EvenlyCovered
#check @CoveringMap.surjective_of_pathConnectedSpace
#check @CoveringMap.locPathConnectedSpace
#check @IsLift
#check @liftHomotopy
#check @existsUnique_liftHomotopy
#check @exists_path_lift
#check @coveringPiOneMap_injective
#check @exists_lift_iff_piOne_range_le
#check @SemilocallySimplyConnected

/-! ## Spheres and simple connectivity -/

#check @standardSphereSimplyConnected
#check @sphereSimplyConnected_of_two_le
#check @sphere_piOne_subsingleton_of_two_le
#check @sphereComplementHomeomorphEuclidean
#check @standardSpherePathConnectedOpenCover

-- The adapter terms below are deliberately `def`s: they are terms built from
-- upstream declarations, not new mathematical claims.  The style linter that
-- asks for `theorem` on proposition-valued definitions is disabled for them.
set_option linter.defProp false

/-! ## Adapter terms -/

noncomputable def d13_coveringLiftHomotopy := @liftHomotopy
@[reducible] noncomputable def d13_sphereSimplyConnected := @sphereSimplyConnected_of_two_le
noncomputable def d13_coveringPiOne_injective := @coveringPiOneMap_injective
noncomputable def d13_cwDimension := @CWDimension

/-! ## Axiom footprint -/

#print axioms sphereSimplyConnected_of_two_le
#print axioms CoveringMap.surjective_of_pathConnectedSpace
#print axioms existsUnique_liftHomotopy
#print axioms coveringPiOneMap_injective
#print axioms IsCWSubcomplex.isClosed
