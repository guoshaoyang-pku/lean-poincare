#!/usr/bin/env python3
"""Generate independent use/citation probes for the SEMREV review.

Two files per card:
  UseProbe.lean  - existence + type/value occurrence for the closure pairs, plus a reverse
                   direct-use census for named constructors, computed in the rebuilt
                   environment (ConstantInfo.value? true, Expr.getUsedConstants).
  Cited.lean     - `#check @name` and `#print axioms name` for every cited declaration, so a
                   failed citation is a hard compile error and the types are printed for
                   semantic reading.
"""
import json
import os

REV = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis"
PROBES = f"{REV}/review/probes"

# closure triples claimed by the parent card (constructor -> downstream checked use)
SPECS = {
    "D13-vankampen-recognition": {
        "exists": [
            "Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2",
            "Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete",
            "Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3",
            "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
            "Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates",
        ],
        "pairs": [
            ["Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2",
             "Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete"],
            ["Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2",
             "Poincare.D13.VanKampenRecognition.RemainingRecognitionHypothesesV4.toRemainingV3"],
            ["Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
             "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses"],
            ["Poincare.D13.VanKampenRecognition.ConnectedSumDecomposition.mkV2Complete",
             "Poincare.D13.VanKampenRecognition.stage6Target_of_v4hypotheses_from_certificates"],
        ],
        "reverse": [
            "Poincare.D13.VanKampenRecognition.simplyConnectedPieces_of_v2",
            "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
        ],
    },
    "D13-critical-path-review": {
        "exists": [
            "Poincare.D13.CriticalPathReview.b1_dimension_one",
            "Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff",
            "Poincare.D13.CriticalPathReview.scalar_forward_invariance",
            "Poincare.D13.CriticalPathReview.NegControl",
        ],
        "pairs": [
            ["Poincare.D13.CriticalPathReview.b1_dimension_one",
             "Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff"],
            ["Poincare.D13.CriticalPathReview.b1_dimension_one",
             "Poincare.D13.CriticalPathReview.scalar_forward_invariance"],
        ],
        "reverse": [
            "Poincare.D13.CriticalPathReview.b1_dimension_one",
            "Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere",
        ],
    },
    "D13-morgan-tian-adapter-plan": {
        "exists": [
            "Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_ballVolumeComparison",
            "Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_kappaNoncollapsingCertificate",
        ],
        "pairs": [
            ["Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_ballVolumeComparison",
             "Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_kappaNoncollapsingCertificate"],
        ],
        "reverse": [
            "Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_ballVolumeComparison",
        ],
    },
    "D13-manifold-ibp-volume-form": {
        "exists": [
            "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
            "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero",
            "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet",
            "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy",
            "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity",
        ],
        "pairs": [
            ["Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
             "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero"],
            ["Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
             "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet"],
            ["Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
             "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy"],
            ["Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
             "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity"],
        ],
        "reverse": [
            "Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional",
        ],
    },
    "D13-deturck-shorttime-producer": {
        "exists": [
            "Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.of_metric",
            "Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.existsUnique_mildSolution_of_model",
            "Poincare.D13.DeturckProducer.PicardModel.MildClassicalOutput",
            "Poincare.D13.DeturckProducer.PicardModel.deTurckShortTimeExistence_of_classicalOutput",
            "Poincare.D13.DeturckProducer.PicardModel.ricciFlow_of_model",
            "Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel",
            "Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.strictParabolic",
        ],
        "pairs": [
            ["Poincare.D13.DeturckProducer.PicardModel.MildClassicalOutput",
             "Poincare.D13.DeturckProducer.PicardModel.deTurckShortTimeExistence_of_classicalOutput"],
            ["Poincare.D13.DeturckProducer.PicardModel.deTurckShortTimeExistence_of_classicalOutput",
             "Poincare.D13.DeturckProducer.PicardModel.ricciFlow_of_model"],
        ],
        "reverse": [
            "Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.strictParabolic",
            "Poincare.D13.DeturckProducer.PicardModel.MildClassicalOutput",
        ],
    },
    "D13-heatkernel-bridge-d10-d7": {
        "exists": [
            "Poincare.D7.HeatKernel.HeatKernelData",
            "Poincare.D13.HeatKernelBridge.HeatKernelDataV1",
            "Poincare.D13.HeatKernelBridge.exists_v1_iff_exists_legacy",
            "Poincare.D7.HeatKernel.heatKernelExistenceStatement_iff_v1",
            "Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1_of_legacy_refutation",
        ],
        "pairs": [
            ["Poincare.D13.HeatKernelBridge.HeatKernelDataV1",
             "Poincare.D7.HeatKernel.heatKernelExistenceStatement_iff_v1"],
        ],
        "reverse": [
            "Poincare.D13.HeatKernelBridge.exists_v1_iff_exists_legacy",
            "Poincare.D13.HeatKernelBridge.HeatKernelDataV1",
        ],
    },
    "D13-integrated-kernel-audit": {
        "exists": [
            "Poincare.D7.ConjugateHeat.ConjugateHeatData",
            "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp",
            "Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq",
            "Poincare.D12.ConnectionCurvature.leviCivitaExists",
            "Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent",
            "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
            "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
        ],
        "pairs": [
            ["Poincare.D12.HeatSemigroup.heatOperatorBCF_comp",
             "Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq"],
            ["Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
             "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses"],
        ],
        "reverse": [
            "Poincare.D12.ConnectionCurvature.leviCivitaExists",
            "Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent",
            "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
            "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses",
        ],
    },
}

TEMPLATE = r'''/-
SEMREV independent use probe for @TASK@ (written for the SEMREV review).
Checks existence, type-level and value-level occurrence of closure pairs, and reverse direct use.
-/
@IMPORTS@
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace @NS@

def existsNames : List Name := [
  @EXISTS@]

def pairs : List (Name × Name) := [
  @PAIRS@]

def reverseNames : List Name := [
  @REVERSE@]

def scanPrefixes : List Name := [
  "Poincare".toName]

end @NS@

open @NS@ in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  for n in existsNames do
    match env.find? n with
    | none => IO.println s!"USE_EXISTS\t{n}\tMISSING"
    | some ci =>
        let axs ← try Lean.collectAxioms n catch _ => pure #[]
        IO.println s!"USE_EXISTS\t{n}\tOK\t{";".intercalate (axs.toList.map Name.toString)}"
  for (ctor, down) in pairs do
    let ci? := env.find? down
    let inType := match ci? with
      | some ci => ci.type.getUsedConstants.contains ctor
      | none => false
    let inValue := match ci? with
      | some ci => (match ci.value? true with
          | some v => v.getUsedConstants.contains ctor
          | none => false)
      | none => false
    IO.println s!"USE_PAIR\t{ctor}\t{down}\texists={(env.find? down).isSome}\ttype={inType}\tvalue={inValue}"
  for ctor in reverseNames do
    let mut direct : Array Name := #[]
    for (d, _) in env.constants.toList do
      if d == ctor then continue
      let inScan : Bool :=
        match env.getModuleIdxFor? d with
        | some i => scanPrefixes.any (fun r => r.isPrefixOf (mods.getD i .anonymous))
        | none => false
      if !inScan then continue
      match env.find? d with
      | some ci =>
          let inT := ci.type.getUsedConstants.contains ctor
          let inV := match ci.value? true with
            | some v => v.getUsedConstants.contains ctor
            | none => false
          if inT || inV then direct := direct.push d
      | none => pure ()
    IO.println s!"USE_REVERSE\t{ctor}\t{direct.size}"
    for d in direct.qsort (fun a b => a.toString < b.toString) do
      IO.println s!"USE_USER\t{ctor}\t{d}"
  IO.println s!"USE_DONE\t@TASK@"
'''


def main():
    for task, spec in SPECS.items():
        d = f"{PROBES}/{task}"
        if not os.path.isdir(d):
            print("skip", task)
            continue
        cfg = json.load(open(f"{d}/spec.json"))
        imports_s = "\n".join("import " + m for m in cfg["imports"])
        ex = ",\n  ".join('"' + n + '".toName' for n in spec["exists"])
        pr = ",\n  ".join('("' + a + '".toName, "' + b + '".toName)' for a, b in spec["pairs"])
        rv = ",\n  ".join('"' + n + '".toName' for n in spec["reverse"])
        ns = "SEMREVUse_" + task.replace("-", "_")
        src = (TEMPLATE.replace("@TASK@", task).replace("@NS@", ns)
               .replace("@IMPORTS@", imports_s).replace("@EXISTS@", ex)
               .replace("@PAIRS@", pr).replace("@REVERSE@", rv))
        open(f"{d}/UseProbe.lean", "w").write(src)
        # Cited.lean: every named declaration gets a #check and an axiom print
        allnames = []
        for n in spec["exists"] + spec["reverse"]:
            if n not in allnames:
                allnames.append(n)
        for a, b in spec["pairs"]:
            for n in (a, b):
                if n not in allnames:
                    allnames.append(n)
        lines = ["/- SEMREV cited-declaration compile check: every cited name must #check. -/",
                 imports_s, "", "set_option autoImplicit false", ""]
        for n in allnames:
            lines.append(f"#check @{n}")
            lines.append(f"#print axioms {n}")
        open(f"{d}/Cited.lean", "w").write("\n".join(lines) + "\n")
        print("wrote", task, len(allnames), "cited names")


if __name__ == "__main__":
    main()
