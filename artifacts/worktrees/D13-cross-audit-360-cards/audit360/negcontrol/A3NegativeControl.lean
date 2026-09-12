-- A3 audit negative control: declarations that MUST be flagged by the fail-closed
-- axiom-cone predicate.  Never imported by any audited card.
import Mathlib

theorem a3_neg_sorry : (1 : ℕ) = 1 := by sorry

theorem a3_neg_native : (List.range 3).length = 3 := by native_decide

#print axioms a3_neg_sorry
#print axioms a3_neg_native
