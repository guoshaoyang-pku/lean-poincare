#!/usr/bin/env python3
"""SEMREV-L5: generate the two collision-free whole-release audit passes.

Each pass imports every module assigned to it and then runs the reviewer's own
fail-closed package audit (axioms / sorryAx / native_decide / unsafe / partial),
environment-level consumer counts for the cited declarations, and an inhabitant
scan for the statement-only interfaces.
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EV = os.path.join(ROOT, "evidence")

ALLOWED = ["propext", "Classical.choice", "Quot.sound"]
NEG_CONTROL = [
    "d12NegControlBadAxiom",
    "d12NegControlBadTheorem",
    "Poincare.D12.VolumeIBP.Audit.negativeControl",
    "Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom",
    "Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem",
]

USE_TARGETS = [
    "Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere",
    "Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere",
    "Poincare.D12.SurgeryRecognition.sphereConnectSum_transported",
    "Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere",
    "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2",
    "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap",
    "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient",
    "Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition",
    "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses",
    "Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses",
    "Poincare.D12.SurgeryRecognition.AntipodalGroup",
    "Poincare.D7.Recognition.stage6Target_of_certificates",
    "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere",
    "Poincare.D12.TriangulationTopology.alexanderHomeo",
    "Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff",
    "Poincare.D12.TriangulationTopology.sphereOfTwoDisks",
    "Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance",
    "Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected",
    "Poincare.Longrun.Topology.stage6Target_of_sphereRecognition",
    "Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold",
    "Poincare.D7.Limit.HeatMeshConvergence",
    "Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition",
    # I6/I7 interface consumer counts cited in the L5 card sections 7-8
    "Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses",
    "Poincare.D7.SurgeryFlow.missingFullNeckAnalysis",
    "Poincare.D7.SurgeryFlow.missingExtinctionTheorem",
    "Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem",
    "Poincare.Longrun.Surgery.ExtinctionTheorem",
    "Poincare.Longrun.Surgery.MissingInputs",
    "Poincare.Longrun.Evolution.FiniteMeshConvergence",
    "Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman",
    "Poincare.Longrun.Evolution.PerelmanEvolutionBoundary",
    "Poincare.Longrun.Evolution.PerelmanApproximation",
    "Poincare.D7.Limit.HeatMeshConvergenceTheorem",
]

# statement-only interfaces: no declaration may prove them
INHABIT_TARGETS = [
    "Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem",
    "Poincare.D7.Limit.HeatMeshConvergenceTheorem",
    "Poincare.D7.Limit.ContinuousHeatMaximumPrincipleConjecture",
    "Poincare.D7.SurgeryFlow.missingFullNeckAnalysis",
    "Poincare.D7.SurgeryFlow.missingExtinctionTheorem",
    "Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem",
    "Poincare.D7.SurgeryFlow.missingAPrioriCurvatureEstimates",
    "Poincare.Longrun.Evolution.FiniteMeshConvergence",
    "Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman",
    "Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity",
    "Poincare.Longrun.Evolution.PerelmanApproximation",
    "Poincare.Longrun.Evolution.PerelmanEvolutionBoundary",
    "Poincare.D7.Recognition.ExtinctionCertificate",
    "Poincare.D7.Recognition.SphericalPieceRecognition",
    "Poincare.D7.Recognition.CanonicalNeighborhoodInput",
    "Poincare.D7.Recognition.RecognitionHypotheses",
    "Poincare.D12.SurgeryRecognition.ConnectedSumDecompositionV2",
    "Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2",
    "Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3",
    "Poincare.Longrun.Surgery.NeckAnalysis",
    "Poincare.Longrun.Surgery.MissingInputs",
    "Poincare.Longrun.Surgery.ExtinctionTheorem",
    "Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses",
    "Poincare.D7.SurgeryFlow.ExtinctionData",
]


def lean_list(names):
    return ",\n  ".join(f"`{n}" for n in names)


def emit_pass(name, modules):
    lines = [f"/- SEMREV-L5 independent whole-release audit pass {name}: {len(modules)} modules. -/"]
    for m in modules:
        lines.append(f"import {m}")
    lines.append("import Lean.Util.CollectAxioms")
    lines.append("import Lean.Elab.Command")
    lines.append("")
    lines.append("set_option autoImplicit false")
    lines.append("set_option maxHeartbeats 0")
    lines.append("set_option maxRecDepth 100000")
    lines.append("")
    lines.append("open Lean Elab Command")
    lines.append("")
    lines.append(f"namespace SemRevPass{name}")
    lines.append("")
    lines.append("def approvedAxioms : List Name := [" + lean_list(ALLOWED) + "]")
    lines.append("")
    lines.append("def negControls : List Name := [" + lean_list(NEG_CONTROL) + "]")
    lines.append("")
    lines.append("def useTargets : List Name := [" + lean_list(USE_TARGETS) + "]")
    lines.append("")
    lines.append("def inhabitTargets : List Name := [" + lean_list(INHABIT_TARGETS) + "]")
    lines.append("")
    lines.append("def packageRoots : List Name := [")
    lines.append("  `Poincare, `Probe, `Ledger, `Audit, `ReleaseCheck, `ReleaseAudit, `D6AuditReport,")
    lines.append("  `ReleaseClaims, `D6LedgerProbe]")
    lines.append("")
    lines.append("def isUnder (roots : List Name) (m : Name) : Bool :=")
    lines.append("  roots.any (fun r => r.isPrefixOf m)")
    lines.append("")
    lines.append(r'''
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => mods.getD i .anonymous
    | none => .anonymous
  let inPkg (n : Name) : Bool := isUnder packageRoots (moduleOf n)
  let mut decls := 0
  let mut theorems := 0
  let mut axiomsUnexpected : Array Name := #[]
  let mut unsafeD : Array Name := #[]
  let mut partialD : Array Name := #[]
  let mut sorryUnexpected : Array Name := #[]
  let mut nativeUnexpected : Array Name := #[]
  let mut unapproved : Array (Name × Name) := #[]
  let mut proofWanted : Array Name := #[]
  let mut collectFail : Array (Name × String) := #[]
  let mut rows : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    if inPkg n then
      rows := rows.push (n, ci)
      decls := decls + 1
      if n.toString.contains "proof_wanted" then proofWanted := proofWanted.push n
      match ci with
      | .thmInfo _ => theorems := theorems + 1
      | .defnInfo v =>
          match v.safety with
          | .«unsafe» => unsafeD := unsafeD.push n
          | .«partial» => partialD := partialD.push n
          | .safe => pure ()
      | .axiomInfo _ => axiomsUnexpected := axiomsUnexpected.push n
      | _ => pure ()
      let axs ←
        try Lean.collectAxioms n
        catch _ => do
          collectFail := collectFail.push (n, "collectAxioms raised")
          pure #[]
      for a in axs do
        if a == `sorryAx then sorryUnexpected := sorryUnexpected.push n
        else if a == `Lean.ofReduceBool || a == `ofReduceBool then nativeUnexpected := nativeUnexpected.push n
        else if !approvedAxioms.contains a then
          unapproved := unapproved.push (n, a)
  -- registered negative controls are excused from the unapproved count but reported by name
  let unapprovedUnexpected := unapproved.filter (fun (n, _) => !negControls.contains n)
  IO.println s!"SEMREVPKG	decls	{decls}"
  IO.println s!"SEMREVPKG	theorems	{theorems}"
  IO.println s!"SEMREVPKG	axioms_unexpected	{axiomsUnexpected.size}"
  IO.println s!"SEMREVPKG	unsafe	{unsafeD.size}"
  IO.println s!"SEMREVPKG	partial	{partialD.size}"
  IO.println s!"SEMREVPKG	sorryAx_unexpected	{sorryUnexpected.size}"
  IO.println s!"SEMREVPKG	native_decide_unexpected	{nativeUnexpected.size}"
  IO.println s!"SEMREVPKG	unapproved_axiom_all	{unapproved.size}"
  IO.println s!"SEMREVPKG	unapproved_axiom_unexpected	{unapprovedUnexpected.size}"
  IO.println s!"SEMREVPKG	proof_wanted	{proofWanted.size}"
  IO.println s!"SEMREVPKG	collect_failures	{collectFail.size}"
  for n in axiomsUnexpected do IO.println s!"SEMREVFAIL	project_axiom	{n}"
  for n in unsafeD do IO.println s!"SEMREVFAIL	unsafe	{n}"
  for n in sorryUnexpected do IO.println s!"SEMREVFAIL	sorryAx	{n}"
  for n in nativeUnexpected do IO.println s!"SEMREVFAIL	native_decide	{n}"
  for n in proofWanted do IO.println s!"SEMREVFAIL	proof_wanted	{n}"
  for (n, a) in unapprovedUnexpected do IO.println s!"SEMREVFAIL	unapproved_axiom	{n}	{a}"
  for (n, e) in collectFail do IO.println s!"SEMREVFAIL	collect_exception	{n}	{e}"
  -- environment-level consumer counts for the cited declarations (own implementation)
  let useSet : NameSet := useTargets.foldl (fun acc t => acc.insert t) ({} : NameSet)
  let mut consumers : NameMap (Array Name) := {}
  for (n, ci) in rows do
    let used := ci.type.getUsedConstants.toList.eraseDups.toArray
    let used := match ci.value? true with
      | some v => used ++ v.getUsedConstants.toList.eraseDups.toArray
      | none => used
    for u in used do
      if useSet.contains u then
        consumers := consumers.insert u (((consumers.find? u).getD #[]).push n)
  for t in useTargets do
    let cs := (consumers.find? t).getD #[]
    IO.println s!"SEMREVUSE	{t}	{cs.size}	{";".intercalate (cs.toList.eraseDups.take 12 |>.map Name.toString)}"
  -- inhabitant scan: any package declaration whose type concludes in a statement-only target
  let inhSet : NameSet := inhabitTargets.foldl (fun acc t => acc.insert t) ({} : NameSet)
  let inhabitants ← liftTermElabM do
    let mut inhabitants : Array (Name × Name × String) := #[]
    let rec peelForalls (e : Expr) : Expr :=
      match e with
      | .forallE _ _ b _ => peelForalls b
      | e => e
    for (n, ci) in rows do
      if n == `sorryAx then continue
      match ci with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
          let hitTarget (e : Expr) : Option Name :=
            let head := e.getAppFn
            match head with
            | .const h _ =>
                if inhSet.contains h && h != n then some h
                else if h == ``Nonempty then
                  match e.getAppArgs[0]? with
                  | some a =>
                      match a.getAppFn with
                      | .const h2 _ => if inhSet.contains h2 && h2 != n then some h2 else none
                      | _ => none
                  | none => none
                else none
            | _ => none
          match hitTarget (peelForalls ci.type) with
          | some h => inhabitants := inhabitants.push (n, h, "syntactic")
          | none =>
              let hit ← try
                  Meta.forallTelescopeReducing ci.type fun _ body => do
                    return hitTarget body
                catch _ => pure none
              if let some h := hit then
                inhabitants := inhabitants.push (n, h, "reduced")
      | _ => pure ()
    return inhabitants
  IO.println s!"SEMREVINH	count	{inhabitants.size}"
  for (n, t, how) in inhabitants do IO.println s!"SEMREVINH	{n}	{t}	{how}"
  -- conclusion-equivalence scan (reviewer's own implementation):
  -- a theorem whose hypothesis type is definitionally equal to its conclusion
  let equiv ← liftTermElabM do
    let mut hits : Array (Name × Nat) := #[]
    for (n, ci) in rows do
      match ci with
      | .thmInfo _ =>
          let hit ← try
              Meta.forallTelescopeReducing ci.type fun _ body => do
                let lctx ← getLCtx
                let mut found : Option Nat := none
                let mut idx := 0
                for x in lctx do
                  if !x.isLet && !x.isImplementationDetail then
                    let same := Expr.equal x.type body
                    let deq ← try Meta.isDefEq x.type body catch _ => pure false
                    if (same || deq) && found.isNone then found := some idx
                    idx := idx + 1
                return found
            catch _ => pure none
          if let some i := hit then hits := hits.push (n, i)
      | _ => pure ()
    return hits
  IO.println s!"SEMREVEQUIV	count	{equiv.size}"
  for (n, i) in equiv do IO.println s!"SEMREVEQUIV	{n}	hyp#{i}"
  IO.println "SEMREVPASS DONE"
''')
    lines.append("")
    lines.append(f"end SemRevPass{name}")
    lines.append("")
    return "\n".join(lines)


def main():
    with open(os.path.join(EV, "passes.json")) as f:
        passes = json.load(f)
    probes = os.path.join(ROOT, "probes")
    with open(os.path.join(probes, "PassA.lean"), "w") as f:
        f.write(emit_pass("A", passes["passA"]))
    with open(os.path.join(probes, "PassB.lean"), "w") as f:
        f.write(emit_pass("B", passes["passB"]))
    print(f"wrote PassA.lean ({len(passes['passA'])} imports), PassB.lean ({len(passes['passB'])} imports)")


if __name__ == "__main__":
    main()
