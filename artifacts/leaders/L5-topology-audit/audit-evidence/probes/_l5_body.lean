import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean Elab Command Meta

namespace L5Audit

/-- The only axioms accepted in a released dependency cone. -/
def approvedAxioms : List Name :=
  ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

def sorryAxiom : Name := "sorryAx".toName
def nativeAxioms : List Name := ["ofReduceBool".toName, "Lean.ofReduceBool".toName]

/-- Negative controls intentionally present in the release tree: the three forbidden axiom
declarations and the two theorems that consume them.  They are *excused* only when the
caller passes them as `excluded` (the positive run does); they are always reported by name
with their axiom cones, and a run with `excluded := []` must fail on them. -/
def knownNegControls : List Name :=
  ["d12NegControlBadAxiom".toName,
   "d12NegControlBadTheorem".toName,
   "Poincare.D12.VolumeIBP.Audit.negativeControl".toName,
   "Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom".toName,
   "Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem".toName]

/-- Package top-level namespaces (audit scope). -/
def packageRoots : List Name :=
  ["Poincare".toName, "Probe".toName, "Ledger".toName, "Audit".toName,
   "ReleaseCheck".toName, "ReleaseAudit".toName, "D6AuditReport".toName,
   "ReleaseClaims".toName, "D6LedgerProbe".toName, "L5NegControlFresh".toName]

/-- Topology lane: recognition, triangulation, surgery, end game and the audited interface
layers that feed them. -/
def laneRoots : List Name :=
  ["Poincare.D7.Recognition".toName,
   "Poincare.D7.SurgeryFlow".toName,
   "Poincare.D7.Limit".toName,
   "Poincare.D10.TriangulationLowDim".toName,
   "Poincare.D12.SurgeryRecognition".toName,
   "Poincare.D12.TriangulationTopology".toName,
   "Poincare.D12.SemanticLedger".toName,
   "Poincare.D13.CriticalPathReview".toName,
   "Poincare.Longrun.Surgery".toName,
   "Poincare.Longrun.Topology".toName,
   "Poincare.Stage6".toName,
   "Poincare.D8.Fidelity".toName,
   "Poincare.VKPort".toName]

def isUnder (roots : List Name) (m : Name) : Bool :=
  roots.any (fun r => r.isPrefixOf m)

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v =>
      match v.safety with
      | .«unsafe» => "unsafe_def"
      | .«partial» => "partial_def"
      | .safe => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Fail-closed package audit.  `excluded` lists the *declarations* excused from the
unexpected-kernel-dependency verdict (never axiom *names*); every cone is still computed and
reported, so excusing is visible in the log. -/
def runAudit (roots : List Name) (excluded : List Name) (annotate : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let imported := env.header.moduleNames
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => imported.getD i .anonymous
    | none => .anonymous
  -- fail-closed module inventory: every imported package module is named in the log
  let pkgMods := imported.filter (fun m => isUnder roots m)
  IO.println s!"L5MOD\timported_total\t{imported.size}"
  IO.println s!"L5MOD\timported_package\t{pkgMods.size}"
  for m in pkgMods do IO.println s!"L5MOD\t{m}"
  let rows : Array (Name × ConstantInfo × Name) :=
    env.constants.fold (fun acc n ci =>
      let m := moduleOf n
      if isUnder roots m then acc.push (n, ci, m) else acc) #[]
  let mut decls := 0
  let mut theorems := 0
  let mut axiomsUnexpected : Array Name := #[]
  let mut unsafeD : Array Name := #[]
  let mut partialD : Array Name := #[]
  let mut sorryUnexpected : Array Name := #[]
  let mut nativeUnexpected : Array Name := #[]
  let mut unapprovedUnexpected : Array (Name × Name) := #[]
  let mut unapprovedAll : Array (Name × Name) := #[]
  let mut proofWanted : Array Name := #[]
  let mut collectFail : Array (Name × String) := #[]
  for (n, ci, m) in rows do
    decls := decls + 1
    if n.toString.contains "proof_wanted" then proofWanted := proofWanted.push n
    match ci with
    | .axiomInfo _ => if !excluded.contains n then axiomsUnexpected := axiomsUnexpected.push n
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => unsafeD := unsafeD.push n
        | .«partial» => partialD := partialD.push n
        | .safe => pure ()
    | .thmInfo _ => theorems := theorems + 1
    | _ => pure ()
    let axs ←
      try Lean.collectAxioms n
      catch _ =>
        collectFail := collectFail.push (n, "collectAxioms raised an exception")
        pure #[]
    for a in axs do
      if a == sorryAxiom then
        if !excluded.contains n then sorryUnexpected := sorryUnexpected.push n
      else if nativeAxioms.contains a then
        if !excluded.contains n then nativeUnexpected := nativeUnexpected.push n
      else if !approvedAxioms.contains a then
        unapprovedAll := unapprovedAll.push (n, a)
        if !excluded.contains n then unapprovedUnexpected := unapprovedUnexpected.push (n, a)
  let modsWithDecls := rows.foldl (fun acc (_, _, m) => if acc.contains m then acc else acc.push m) #[]
  IO.println s!"L5PKG\tdeclarations\t{decls}"
  IO.println s!"L5PKG\ttheorems\t{theorems}"
  IO.println s!"L5PKG\tmodules_with_declarations\t{modsWithDecls.size}"
  IO.println s!"L5PKG\tproject_axiom_declarations_unexpected\t{axiomsUnexpected.size}"
  IO.println s!"L5PKG\tunsafe_declarations\t{unsafeD.size}"
  IO.println s!"L5PKG\tpartial_declarations\t{partialD.size}"
  IO.println s!"L5PKG\tsorryAx_declarations_unexpected\t{sorryUnexpected.size}"
  IO.println s!"L5PKG\tnative_decide_declarations_unexpected\t{nativeUnexpected.size}"
  IO.println s!"L5PKG\tunapproved_axiom_declarations_all\t{unapprovedAll.size}"
  IO.println s!"L5PKG\tunapproved_axiom_declarations_unexpected\t{unapprovedUnexpected.size}"
  IO.println s!"L5PKG\tproof_wanted_declarations\t{proofWanted.size}"
  IO.println s!"L5PKG\tcollect_failures\t{collectFail.size}"
  for n in axiomsUnexpected do IO.println s!"L5PKGFAIL\tproject_axiom\t{n}"
  for n in unsafeD do IO.println s!"L5PKGFAIL\tunsafe\t{n}"
  for n in sorryUnexpected do IO.println s!"L5PKGFAIL\tsorryAx\t{n}"
  for n in nativeUnexpected do IO.println s!"L5PKGFAIL\tnative_decide\t{n}"
  for (n, a) in unapprovedUnexpected do IO.println s!"L5PKGFAIL\tunapproved_axiom\t{n}\t{a}"
  for n in proofWanted do IO.println s!"L5PKGFAIL\tproof_wanted\t{n}"
  for (n, e) in collectFail do IO.println s!"L5PKGFAIL\tcollect_exception\t{n}\t{e}"
  -- negative-control registry: always reported, with exact cones
  IO.println s!"L5NEGCLUSTER\tregistered\t{knownNegControls.length}"
  for n in knownNegControls do
    let present := env.constants.contains n
    let kind := match env.find? n with
      | some ci => kindOf ci
      | none => "ABSENT"
    let axs ←
      try Lean.collectAxioms n
      catch _ => pure #[]
    IO.println s!"L5NEGCLUSTER\t{n}\tpresent={present}\tkind={kind}\tcone={";".intercalate (axs.toList.map Name.toString)}"
  if annotate then
    let laneRows := rows.filter (fun (_, _, m) => isUnder laneRoots m)
    for (n, ci, _) in laneRows do
      let axs ←
        try Lean.collectAxioms n
        catch _ => pure #[]
      IO.println s!"L5DECL\t{n}\t{kindOf ci}\t{";".intercalate (axs.toList.map Name.toString)}"
    for (n, ci, _) in laneRows do
      let ty ← liftTermElabM (Meta.ppExpr ci.type)
      IO.println s!"L5TYPE\t{n}\t{kindOf ci}\t{(" ".intercalate (ty.pretty.splitOn "\n"))}"
    for (n, ci, _) in laneRows do
      match ci with
      | .defnInfo _ | .opaqueInfo _ =>
          let isP ← liftTermElabM (Meta.isProp ci.type)
          if isP then IO.println s!"L5PROP\t{n}\t{kindOf ci}"
      | _ => pure ()
    IO.println "L5EQUIV\tbegin"
    for (n, ci, _) in laneRows do
      if let .thmInfo _ := ci then
        try
          liftTermElabM do
            forallTelescopeReducing ci.type fun _ body => do
              for x in ← getLCtx do
                if !x.isLet && !x.isImplementationDetail then
                  let same := Expr.equal x.type body
                  let deq ← try Meta.isDefEq x.type body catch _ => pure false
                  if same || deq then
                    let ty ← Meta.ppExpr ci.type
                    IO.println s!"L5EQUIV\tHIT\t{n}\tsyntactic={same}\tdefeq={deq}\t{(" ".intercalate (ty.pretty.splitOn "\n"))}"
        catch _ => pure ()
    IO.println "L5EQUIV\tend"
    let laneSet : NameMap Unit := laneRows.foldl (fun acc (n, _, _) => acc.insert n ()) {}
    let mut consumers : NameMap (Array Name) := {}
    for (n, ci, _) in rows do
      let used := ci.type.getUsedConstants.toList.eraseDups.toArray
      let used := match ci.value? true with
        | some v => used ++ v.getUsedConstants.toList.eraseDups.toArray
        | none => used
      for u in used do
        if laneSet.contains u then
          consumers := consumers.insert u (((consumers.find? u).getD #[]).push n)
    let mut zeroUse := 0
    for (n, ci, _) in laneRows do
      let cs := (consumers.find? n).getD #[]
      if cs.isEmpty then zeroUse := zeroUse + 1
      IO.println s!"L5USE\t{n}\t{kindOf ci}\t{cs.size}\t{";".intercalate (cs.toList.eraseDups.take 8 |>.map Name.toString)}"
    IO.println s!"L5USE\tlane_declarations\t{laneRows.size}"
    IO.println s!"L5USE\tlane_declarations_with_zero_package_consumers\t{zeroUse}"
  let failed := !axiomsUnexpected.isEmpty || !unsafeD.isEmpty || !sorryUnexpected.isEmpty ||
      !nativeUnexpected.isEmpty || !unapprovedUnexpected.isEmpty || !proofWanted.isEmpty ||
      !collectFail.isEmpty
  if failed then
    IO.println "L5VERDICT\tFAIL"
    throwError "L5Audit: unexpected forbidden kernel dependency detected (see L5PKGFAIL lines)"
  else
    IO.println "L5VERDICT\tPASS — every audited declaration except the registered negative-control cluster depends only on {propext, Classical.choice, Quot.sound}"

end L5Audit
