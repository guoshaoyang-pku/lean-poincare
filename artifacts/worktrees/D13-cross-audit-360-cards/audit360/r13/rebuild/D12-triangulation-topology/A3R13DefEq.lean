-- A3 round-13 definitional hyp-equals-conclusion screen (generated)
import Poincare.D12.TriangulationTopology.AntipodalQuotient
import Poincare.D12.TriangulationTopology.AxiomAudit
import Poincare.D12.TriangulationTopology.CoveringLemma
import Poincare.D12.TriangulationTopology.DiskGluing
import Poincare.D12.TriangulationTopology.Downstream
import Poincare.D12.TriangulationTopology.HemisphereDisk
import Poincare.D12.TriangulationTopology.MoiseBranch
import Poincare.D12.TriangulationTopology.NegControl.NegControl
import Poincare.D12.TriangulationTopology.SimplexBoundary
import Poincare.D12.TriangulationTopology.SimplexCone
import Poincare.D12.TriangulationTopology.SphereGluing
import Poincare.D12.TriangulationTopology.SphereMissedPoint
import Poincare.D12.TriangulationTopology.SphereOfTwoDisks
import Poincare.D12.TriangulationTopology.SpherePolygonal
import Poincare.D12.TriangulationTopology.SphereRecognition
import Poincare.D12.TriangulationTopology.SphereSimplyConnected
import Poincare.D12.TriangulationTopology.SphereSimplyConnectedMain
import Poincare.D12.TriangulationTopology.TwoHemisphereInstance

open Lean Elab Command
open Lean Meta
namespace A3R13D

def claimed : List Name := [``Poincare.D12.TriangulationTopology.DiskGlueQuot,
  ``Poincare.D12.TriangulationTopology.PuncturedDisk,
  ``Poincare.D12.TriangulationTopology.RealProjective,
  ``Poincare.D12.TriangulationTopology.UpperHemisphere,
  ``Poincare.D12.TriangulationTopology.alexanderHomeo,
  ``Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff,
  ``Poincare.D12.TriangulationTopology.alexanderHomeo_refl,
  ``Poincare.D12.TriangulationTopology.alexanderHomeo_sphereToDisk,
  ``Poincare.D12.TriangulationTopology.alexanderHomeo_symm_sphereToDisk,
  ``Poincare.D12.TriangulationTopology.alexanderHomeo_zero,
  ``Poincare.D12.TriangulationTopology.antipodalContinuousConstSMul,
  ``Poincare.D12.TriangulationTopology.antipodalIsCancelSMul,
  ``Poincare.D12.TriangulationTopology.antipodalMulAction,
  ``Poincare.D12.TriangulationTopology.antipodalQuotientCovering,
  ``Poincare.D12.TriangulationTopology.antipodalSmul,
  ``Poincare.D12.TriangulationTopology.antipodalSmul_ofAdd_one,
  ``Poincare.D12.TriangulationTopology.antipodalSmul_one,
  ``Poincare.D12.TriangulationTopology.antipodal_mul_self,
  ``Poincare.D12.TriangulationTopology.antipodal_smul_ofAdd_one_eq,
  ``Poincare.D12.TriangulationTopology.antipodal_smul_one_eq,
  ``Poincare.D12.TriangulationTopology.coneMapQuot_injective,
  ``Poincare.D12.TriangulationTopology.coneMapQuot_surjective,
  ``Poincare.D12.TriangulationTopology.coneOverSphere2HomeoDisk3,
  ``Poincare.D12.TriangulationTopology.coneQuotHomeoDisk,
  ``Poincare.D12.TriangulationTopology.coneQuotHomeoTopCatDisk,
  ``Poincare.D12.TriangulationTopology.coneQuotNonempty,
  ``Poincare.D12.TriangulationTopology.continuousOn_diskDirection,
  ``Poincare.D12.TriangulationTopology.continuous_antipodal_ofAdd_one,
  ``Poincare.D12.TriangulationTopology.continuous_diskDirection_punctured,
  ``Poincare.D12.TriangulationTopology.continuous_diskToUpperHemisphere,
  ``Poincare.D12.TriangulationTopology.continuous_radialExtend,
  ``Poincare.D12.TriangulationTopology.continuous_simplexBoundaryConeMap,
  ``Poincare.D12.TriangulationTopology.continuous_simplexBoundaryConeMapQuot,
  ``Poincare.D12.TriangulationTopology.continuous_simplexConeMap,
  ``Poincare.D12.TriangulationTopology.continuous_simplexConeMapQuot,
  ``Poincare.D12.TriangulationTopology.continuous_simplexMin,
  ``Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundary,
  ``Poincare.D12.TriangulationTopology.continuous_sphereToSimplexBoundary_apply,
  ``Poincare.D12.TriangulationTopology.continuous_upperHemisphereToDisk,
  ``Poincare.D12.TriangulationTopology.coveringMap_injective_of_simplyConnected,
  ``Poincare.D12.TriangulationTopology.coveringMap_surjective_of_pathConnected,
  ``Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo,
  ``Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo_bijective,
  ``Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo_of_nonempty,
  ``Poincare.D12.TriangulationTopology.disk3_boundary_eq_sphere2,
  ``Poincare.D12.TriangulationTopology.diskCompactSpace,
  ``Poincare.D12.TriangulationTopology.diskContractible,
  ``Poincare.D12.TriangulationTopology.diskCoverPipeline,
  ``Poincare.D12.TriangulationTopology.diskDirection,
  ``Poincare.D12.TriangulationTopology.diskDirection_of_ne,
  ``Poincare.D12.TriangulationTopology.diskDirection_radialExtend,
  ``Poincare.D12.TriangulationTopology.diskDirection_sphereToDisk,
  ``Poincare.D12.TriangulationTopology.diskGlueQuotCompactSpace,
  ``Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere,
  ``Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere_refl_apply,
  ``Poincare.D12.TriangulationTopology.diskGlueQuotNonempty,
  ``Poincare.D12.TriangulationTopology.diskGlueQuotT2Space,
  ``Poincare.D12.TriangulationTopology.diskGlueRel,
  ``Poincare.D12.TriangulationTopology.diskGlueRel_id_iff_doubleDiskRel,
  ``Poincare.D12.TriangulationTopology.diskGlueRel_transport,
  ``Poincare.D12.TriangulationTopology.diskGlueSumHomeo,
  ``Poincare.D12.TriangulationTopology.diskGlueSumHomeo_inl,
  ``Poincare.D12.TriangulationTopology.diskGlueSumHomeo_inr,
  ``Poincare.D12.TriangulationTopology.diskNonempty,
  ``Poincare.D12.TriangulationTopology.diskSimplyConnected,
  ``Poincare.D12.TriangulationTopology.diskToLowerHemisphere,
  ``Poincare.D12.TriangulationTopology.diskToUpperHemisphere,
  ``Poincare.D12.TriangulationTopology.diskToUpperHemisphere_upperHemisphereToDisk,
  ``Poincare.D12.TriangulationTopology.disk_boundary_eq_sphere,
  ``Poincare.D12.TriangulationTopology.doubleDiskMapQuot_injective,
  ``Poincare.D12.TriangulationTopology.doubleDiskMapQuot_surjective,
  ``Poincare.D12.TriangulationTopology.doubleDiskQuotHomeoSphere,
  ``Poincare.D12.TriangulationTopology.doubleDiskQuotHomeoTopCatSphere,
  ``Poincare.D12.TriangulationTopology.doubleDiskQuotNonempty,
  ``Poincare.D12.TriangulationTopology.eq_neg_self_of_sqrt_eq_neg_sqrt,
  ``Poincare.D12.TriangulationTopology.esnoc'_lowerTrunc_eq,
  ``Poincare.D12.TriangulationTopology.esnoc_injective2,
  ``Poincare.D12.TriangulationTopology.hemisphere_charts_agree,
  ``Poincare.D12.TriangulationTopology.hemisphere_cover,
  ``Poincare.D12.TriangulationTopology.iccCompactSpace,
  ``Poincare.D12.TriangulationTopology.isCoveringMap_id,
  ``Poincare.D12.TriangulationTopology.locallyCompactSpace_of_compact_t2,
  ``Poincare.D12.TriangulationTopology.lowerHemisphereCompactSpace,
  ``Poincare.D12.TriangulationTopology.lowerHemisphereHomeoDisk,
  ``Poincare.D12.TriangulationTopology.lowerHemisphereNonempty,
  ``Poincare.D12.TriangulationTopology.lowerHemisphereT2Space,
  ``Poincare.D12.TriangulationTopology.lowerHemisphereToDisk,
  ``Poincare.D12.TriangulationTopology.lowerHemisphere_boundary_eq_inter,
  ``Poincare.D12.TriangulationTopology.lowerHemisphere_isClosed,
  ``Poincare.D12.TriangulationTopology.norm_eq_one_iff_norm_sq_eq_one,
  ``Poincare.D12.TriangulationTopology.norm_esnoc_smul_sqrt_sub_sq_eq_one,
  ``Poincare.D12.TriangulationTopology.norm_radialExtend,
  ``Poincare.D12.TriangulationTopology.norm_sq_esnoc,
  ``Poincare.D12.TriangulationTopology.norm_sq_esnoc',
  ``Poincare.D12.TriangulationTopology.one_ne_ofAdd_one,
  ``Poincare.D12.TriangulationTopology.quotMapHomeo,
  ``Poincare.D12.TriangulationTopology.quotMapHomeo_mk,
  ``Poincare.D12.TriangulationTopology.radialExtend,
  ``Poincare.D12.TriangulationTopology.radialExtend_apply,
  ``Poincare.D12.TriangulationTopology.radialExtend_comp,
  ``Poincare.D12.TriangulationTopology.radialExtend_id,
  ``Poincare.D12.TriangulationTopology.radialExtend_sphereToDisk,
  ``Poincare.D12.TriangulationTopology.radialExtend_zero,
  ``Poincare.D12.TriangulationTopology.rpCompactSpace,
  ``Poincare.D12.TriangulationTopology.rpNonempty,
  ``Poincare.D12.TriangulationTopology.rpPathConnectedSpace_of_pos,
  ``Poincare.D12.TriangulationTopology.rpT2Space,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryCompactSpace,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeCompactSpace,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSimplex,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSphereCone,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeMap,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot_injective,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeMapQuot_surjective,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeMap_mem,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeMap_respects,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeNonempty,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeRel,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeRel_iff_coneRel,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryConeT2Space,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryFnCompactSpace,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryFnHomeoSphere,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryHomeoBoundaryFn,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryHomeoSphere,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryNonempty,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryPoint,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryPoint_eq_of_radial_repr,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryPoint_mem_of_ne_center,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryT2Space,
  ``Poincare.D12.TriangulationTopology.simplexBoundaryToSphere,
  ``Poincare.D12.TriangulationTopology.simplexConeMap,
  ``Poincare.D12.TriangulationTopology.simplexConeMapQuot,
  ``Poincare.D12.TriangulationTopology.simplexConeMapQuot_injective,
  ``Poincare.D12.TriangulationTopology.simplexConeMapQuot_surjective,
  ``Poincare.D12.TriangulationTopology.simplexConeMap_mem,
  ``Poincare.D12.TriangulationTopology.simplexConeMap_respects,
  ``Poincare.D12.TriangulationTopology.simplexFnCompactSpace,
  ``Poincare.D12.TriangulationTopology.simplexFnNonempty,
  ``Poincare.D12.TriangulationTopology.simplexFnT2Space,
  ``Poincare.D12.TriangulationTopology.simplexHomeoBoundaryCone,
  ``Poincare.D12.TriangulationTopology.simplexHomeoBoundaryConeStd,
  ``Poincare.D12.TriangulationTopology.simplexHomeoConeQuot,
  ``Poincare.D12.TriangulationTopology.simplexHomeoDisk,
  ``Poincare.D12.TriangulationTopology.simplexHomeoStdSimplexFn,
  ``Poincare.D12.TriangulationTopology.simplexMin_attains,
  ``Poincare.D12.TriangulationTopology.simplexMin_eq_zero_of_mem_boundary,
  ``Poincare.D12.TriangulationTopology.simplexMin_le_center,
  ``Poincare.D12.TriangulationTopology.simplexMin_lt_center_of_ne_center,
  ``Poincare.D12.TriangulationTopology.simplexMin_neg_of_unit,
  ``Poincare.D12.TriangulationTopology.simplexRadialTime,
  ``Poincare.D12.TriangulationTopology.simplexRadialTime_eq_of_radial_repr,
  ``Poincare.D12.TriangulationTopology.simplexRadialTime_le_one,
  ``Poincare.D12.TriangulationTopology.simplexRadialTime_nonneg,
  ``Poincare.D12.TriangulationTopology.simplexRadialTime_pos_of_ne_center,
  ``Poincare.D12.TriangulationTopology.simplexSet,
  ``Poincare.D12.TriangulationTopology.simplexVertexZero,
  ``Poincare.D12.TriangulationTopology.simplexVertexZero_mem_boundary,
  ``Poincare.D12.TriangulationTopology.simplex_point_eq_center_add_norm_mul_dir,
  ``Poincare.D12.TriangulationTopology.sphereBase,
  ``Poincare.D12.TriangulationTopology.sphereCompactSpace,
  ``Poincare.D12.TriangulationTopology.sphereConeHomeoSimplex,
  ``Poincare.D12.TriangulationTopology.sphereNonempty,
  ``Poincare.D12.TriangulationTopology.sphereOfTwoDisks,
  ``Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance,
  ``Poincare.D12.TriangulationTopology.spherePathConnectedSpace_of_pos,
  ``Poincare.D12.TriangulationTopology.sphereThreeGluedDisks,
  ``Poincare.D12.TriangulationTopology.sphereThreeSuspension,
  ``Poincare.D12.TriangulationTopology.sphereThree_eq_sphere3,
  ``Poincare.D12.TriangulationTopology.sphereToDisk,
  ``Poincare.D12.TriangulationTopology.sphereToDisk_coe,
  ``Poincare.D12.TriangulationTopology.sphereToSimplexBoundaryFn,
  ``Poincare.D12.TriangulationTopology.sphere_eq_neg_self_impossible,
  ``Poincare.D12.TriangulationTopology.sphere_trunc_norm_sq_add_last_sq_eq_one,
  ``Poincare.D12.TriangulationTopology.sphericalSpaceFormRecognition,
  ``Poincare.D12.TriangulationTopology.sqrt_one_sub_sq_eq_norm_of_norm_sq_add_sq_eq_one,
  ``Poincare.D12.TriangulationTopology.sqrt_one_sub_trunc_norm_sq_eq_last,
  ``Poincare.D12.TriangulationTopology.sqrt_one_sub_trunc_norm_sq_eq_neg_last,
  ``Poincare.D12.TriangulationTopology.suspMapQuot_injective,
  ``Poincare.D12.TriangulationTopology.suspMapQuot_surjective,
  ``Poincare.D12.TriangulationTopology.suspQuotHomeoSphere,
  ``Poincare.D12.TriangulationTopology.suspQuotHomeoTopCatSphere,
  ``Poincare.D12.TriangulationTopology.suspQuotNonempty,
  ``Poincare.D12.TriangulationTopology.trivialization_id,
  ``Poincare.D12.TriangulationTopology.truncToCenter_simplexConeMap,
  ``Poincare.D12.TriangulationTopology.upperHemisphereCompactSpace,
  ``Poincare.D12.TriangulationTopology.upperHemisphereHomeoDisk,
  ``Poincare.D12.TriangulationTopology.upperHemisphereNonempty,
  ``Poincare.D12.TriangulationTopology.upperHemisphereT2Space,
  ``Poincare.D12.TriangulationTopology.upperHemisphereToDisk,
  ``Poincare.D12.TriangulationTopology.upperHemisphereToDisk_diskToUpperHemisphere,
  ``Poincare.D12.TriangulationTopology.upperHemisphere_isClosed,
  ``Poincare.D12.TriangulationTopology.zmod2Mul_eq_ofAdd_one_or_one,
  ``Poincare.D12.TriangulationTopology.zmod2_eq_zero_or_one]

/-- Only theorems with a Prop-valued hypothesis can commit the
assumption-as-conclusion defect; a plain function whose argument type equals
its result type (e.g. `def f (x : R) : R`) is benign. -/
def run : CommandElabM Unit := do
  liftTermElabM do
    let mut checked := 0
    for n in claimed do
      let ci ← getConstInfo n
      unless ci matches .thmInfo _ do continue
      checked := checked + 1
      Lean.Meta.forallTelescope ci.type (fun args body => do
        if ← isDefEq body (.const ``True []) then
          logInfo m!"A3R13D|TRIVIAL_TRUE|{n}"
        for a in args do
          let ty ← inferType a
          if ← isProp ty then
            if ← isDefEq ty body then
              let u := a.fvarId!.name
              logInfo m!"A3R13D|HYP_DEFEQ|{n}|{u}"
        )
    logInfo m!"A3R13D|CHECKED|{checked}"
  logInfo m!"A3R13D|DONE"

end A3R13D
run_cmd A3R13D.run
