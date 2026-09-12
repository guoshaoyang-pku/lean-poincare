/-
Independent transitive downstream-use probe for D13-integrated-kernel-audit.
For every claimed (constructor, downstream) pair, walks the transitive proof-term closure of the
downstream declaration (type + value, theorems unsealed) restricted to project modules and reports
whether the constructor occurs anywhere in that closure.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import ReleaseCheck
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace D13XTrans

end D13XTrans

open D13XTrans in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let packageRoots : List Name := ["Poincare".toName, "Probe".toName, "Ledger".toName,
    "Audit".toName, "ReleaseCheck".toName, "ReleaseAudit".toName, "D6AuditReport".toName]
  let inPkg (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some midx => packageRoots.any (fun r => r.isPrefixOf (mods.getD midx .anonymous))
    | none => false
  let spec : List (String × String) := [
    ("Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator", "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp"),
    ("Poincare.D12.ParabolicLocal.gaussianS_add", "Poincare.D12.ParabolicLocal.linearCandidate_isFixedPt"),
    ("Poincare.D12.ParabolicLocal.heatConv_semigroup", "Poincare.D12.ParabolicLocal.linearCandidate_isFixedPt"),
    ("Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC", "Poincare.D12.ParabolicLocal.gaussianSmap_continuous"),
    ("Poincare.D12.TriangulationTopology.alexanderHomeo", "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere"),
    ("Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded", "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp"),
    ("Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2", "Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition"),
    ("Poincare.D12.ConnectionCurvature.milnorConnection", "Poincare.D12.ConnectionCurvature.leviCivitaExists"),
    ("Poincare.D12.ParabolicLocal.derivativeLossBarrier_holds", "Poincare.D12.ParabolicLocal.derivativeLossBarrier_discharged")
  ]
  for (ctorS, downS) in spec do
    let ctor := ctorS.toName
    let down := downS.toName
    match env.find? down with
    | none => IO.println s!"D13XTRANS\t{ctorS}\t{downS}\tDOWNSTREAM_MISSING"
    | some ci =>
      let init : Array Name :=
        ci.type.getUsedConstants ++ ((ci.value? true).map (fun v => v.getUsedConstants)).getD #[]
      let mut work := init
      let mut seen : Array Name := #[]
      let mut i : Nat := 0
      let mut found := false
      while i < work.size ∧ i < 200000 do
        let x := work[i]!
        i := i + 1
        if x == ctor then
          found := true
          i := work.size
        else if seen.contains x then
          pure ()
        else
          seen := seen.push x
          if inPkg x then
            match env.find? x with
            | some c2 =>
              let more := c2.type.getUsedConstants ++
                ((c2.value? true).map (fun v => v.getUsedConstants)).getD #[]
              work := work ++ more
            | none => pure ()
      IO.println s!"D13XTRANS\t{ctorS}\t{downS}\t{found}"
  IO.println "D13XTRANS_DONE"
