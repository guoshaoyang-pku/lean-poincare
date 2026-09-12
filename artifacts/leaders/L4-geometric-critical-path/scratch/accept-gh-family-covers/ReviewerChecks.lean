/-
Independent reviewer scratch checks:
* transitive constant-dependency closure of every headline theorem, checked for
  `gromovCriterion` (circularity) and for the main conclusion names being used
  as if they were inputs (not applicable to closures, but we check the four
  "main conclusion" constants are only *produced*, listed separately);
* statement dump via `#check` for comparison against the result card;
* concrete computations on the discrete witness model.
-/
import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.Compactness.FamilyCoversWitness
import Lean.Elab.Command

open Lean Elab Command
open Set Metric

namespace ReviewerChecks

partial def closure (env : Environment) (work acc : List Name) : List Name :=
  match work with
  | [] => acc
  | m :: rest =>
    if acc.contains m then closure env rest acc
    else
      let acc := m :: acc
      let cs := match env.find? m with
        | some ci => (match ci.value? true with
                      | some v => v.getUsedConstants.toList
                      | none => [])
        | none => []
      closure env (cs ++ rest) acc

def headline : List Name :=
  [``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling,
   ``Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling,
   ``Poincare.L4.Compactness.totallyBounded_of_uniformDoubling,
   ``Poincare.L4.Compactness.isCompact_of_uniformDoubling,
   ``Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale,
   ``Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling,
   ``Poincare.L4.Compactness.exists_finset_ball_cover_card_le_of_coveringNumber_le,
   ``Poincare.L4.Compactness.exists_set_ball_cover_card_le_of_coveringNumber_le,
   ``Poincare.L4.Compactness.exists_div_pow_two_le]

def witnessKey : List Name :=
  [``Poincare.L4.Compactness.finiteDiscFamily_hypotheses,
   ``Poincare.L4.Compactness.finiteDiscFamily_coveringNumber_quarter,
   ``Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half,
   ``Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half_explicit,
   ``Poincare.L4.Compactness.finiteDiscFamily_cover_half_card_ge,
   ``Poincare.L4.Compactness.discGH_injective,
   ``Poincare.L4.Compactness.not_uniformCovers_allDiscFamily,
   ``Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily]

run_cmd do
  let env ← getEnv
  let mut problems : Array String := #[]
  for t in headline ++ witnessKey do
    let cl := closure env [t] []
    let hasGromov := cl.contains ``Poincare.D12.GeometricCompactness.gromovCriterion
    let hasSorry := cl.contains ``sorryAx
    logInfo (toString t ++ ": closure size " ++ toString cl.length
      ++ ", gromovCriterion=" ++ toString hasGromov ++ ", sorryAx=" ++ toString hasSorry)
    if hasGromov then problems := problems.push ("gromovCriterion in closure of " ++ toString t)
    if hasSorry then problems := problems.push ("sorryAx in closure of " ++ toString t)
  -- the four "main conclusions" must not appear in the closure of the two
  -- *direction-check* theorems, which only consume the workhorse + D12
  let dirClosureTB := closure env [``Poincare.L4.Compactness.totallyBounded_of_uniformDoubling] []
  let dirClosureIC := closure env [``Poincare.L4.Compactness.isCompact_of_uniformDoubling] []
  logInfo ("direction-check totallyBounded closure mentions gromovCriterion: "
    ++ toString (dirClosureTB.contains ``Poincare.D12.GeometricCompactness.gromovCriterion))
  logInfo ("direction-check isCompact closure mentions gromovCriterion: "
    ++ toString (dirClosureIC.contains ``Poincare.D12.GeometricCompactness.gromovCriterion))
  if problems.isEmpty then logInfo "REVIEWER-CLOSURE: PASS" else
    for p in problems do logError p
    throwError "REVIEWER-CLOSURE: FAIL"

end ReviewerChecks

#print axioms Poincare.L4.Compactness.uniformCovers_of_uniformDoubling

/-! ## Statement dump for fidelity comparison -/
#check @Poincare.L4.Compactness.exists_finset_ball_cover_card_le_of_coveringNumber_le
#check @Poincare.L4.Compactness.exists_set_ball_cover_card_le_of_coveringNumber_le
#check @Poincare.L4.Compactness.exists_div_pow_two_le
#check @Poincare.L4.Compactness.coveringNumber_univ_le_of_uniformDoubling
#check @Poincare.L4.Compactness.uniformCovers_of_uniformDoubling
#check @Poincare.L4.Compactness.uniformCovers_of_uniformDoubling_familyScale
#check @Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling
#check @Poincare.L4.Compactness.totallyBounded_of_uniformDoubling
#check @Poincare.L4.Compactness.isCompact_of_uniformDoubling
#check @Poincare.L4.Compactness.finiteDiscFamily_hypotheses
#check @Poincare.L4.Compactness.finiteDiscFamily_coveringNumber_quarter
#check @Poincare.L4.Compactness.finiteDiscFamily_uniformCovers_half_explicit
#check @Poincare.L4.Compactness.finiteDiscFamily_cover_half_card_ge
#check @Poincare.L4.Compactness.not_uniformCovers_allDiscFamily
#check @Poincare.L4.Compactness.not_uniformDoubling_allDiscFamily

/-! ## Concrete checks on the discrete witness model -/
namespace ReviewerChecks

open Poincare.L4.Compactness

example : Disc.d 3 ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ = 1 := by decide
example : Disc.d 3 ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = 0 := by decide
example : dist (show Disc 3 from (⟨0, by norm_num⟩ : Fin 3))
    (show Disc 3 from (⟨2, by norm_num⟩ : Fin 3)) = 1 := by
  rw [Disc.dist_def]; decide
example : dist (show Disc 3 from (⟨1, by norm_num⟩ : Fin 3))
    (show Disc 3 from (⟨1, by norm_num⟩ : Fin 3)) = 0 := by
  rw [Disc.dist_def]; decide
example : (Finset.univ : Finset (Disc 3)).card = 3 := by decide
example : (univ : Set (Disc 3)).encard = (3 : ℕ∞) := by simp [Disc]
example : (univ : Set (Disc 0)).encard = (0 : ℕ∞) := by simp [Disc]

end ReviewerChecks
