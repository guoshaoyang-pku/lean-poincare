/-
Independent reviewer check: transitive *constant-dependency* closure of each
headline theorem, computed from the kernel environment (mirroring
`Lean.Util.CollectAxioms`), used to test
  (e) `gromovCriterion` is not used anywhere in the proof of the direction checks;
  (d) the main uniform-cover theorem does not depend on the D12 criterion that it
      is supposed to feed (no smuggling of the conclusion into its own proof).
-/
import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.Compactness.FamilyCoversWitness
import Lean.Elab.Command

open Lean Elab Command

namespace ReviewerClosure

partial def visitAll (env : Environment) (work : List Name) (seen : NameSet) : NameSet :=
  match work with
  | [] => seen
  | c :: rest =>
    if seen.contains c then visitAll env rest seen
    else
      let seen := seen.insert c
      let cs := match env.checked.get.find? c with
        | some ci =>
          let ty := ci.toConstantVal.type.getUsedConstants.toList
          let v := match ci with
            | .defnInfo v => v.value.getUsedConstants.toList
            | .thmInfo v => v.value.getUsedConstants.toList
            | .opaqueInfo v => v.value.getUsedConstants.toList
            | _ => []
          ty ++ v
        | none => []
      visitAll env (cs ++ rest) seen

def closureOf (env : Environment) (n : Name) : NameSet := visitAll env [n] {}

def gc : Name := ``Poincare.D12.GeometricCompactness.gromovCriterion
def tbu : Name := ``Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers
def icu : Name := ``Poincare.D12.GeometricCompactness.isCompact_of_uniformCovers
def ucu : Name := ``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling
def cnt : Name := ``Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling

def targets : List (Name × List (Name × Bool)) :=
  [ (``Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling,
      [(gc, false), (ucu, false), (tbu, false), (icu, false)])
  , (``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling,
      [(gc, false), (ucu, true), (tbu, false), (icu, false), (cnt, true)])
  , (``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale,
      [(gc, false), (ucu, true)])
  , (``Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling,
      [(gc, false), (ucu, false)])
  , (``Poincare.L4.Compactness.totallyBounded_of_uniformDoubling,
      [(gc, false), (tbu, true), (ucu, true)])
  , (``Poincare.L4.Compactness.isCompact_of_uniformDoubling,
      [(gc, false), (icu, true), (ucu, true)])
  , (``Poincare.L4.Compactness.finiteDiscFamily_hypotheses,
      [(gc, false)])
  , (``Poincare.L4.Compactness.not_uniformCovers_allDiscFamily,
      [(gc, false)])
  , (``Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily,
      [(gc, false)])
  ]

run_cmd do
  let env ← getEnv
  let mut fails : Array String := #[]
  for (t, exps) in targets do
    let cl := closureOf env t
    logInfo (toString t ++ ": closure size " ++ toString cl.size)
    for (n, want) in exps do
      let got := cl.contains n
      logInfo ("   " ++ toString n ++ " present=" ++ toString got ++ " expected=" ++ toString want)
      if got != want then
        fails := fails.push (toString t ++ ": " ++ toString n ++ " present=" ++ toString got
          ++ " but expected " ++ toString want)
  if fails.isEmpty then logInfo "REVIEWER-CLOSURE: PASS"
  else
    for f in fails do logError f
    throwError "REVIEWER-CLOSURE: FAIL"

end ReviewerClosure
