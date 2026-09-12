import Mathlib.Tactic

section
universe uA
variable {A : Type uA} [CommRing A] [Algebra ℝ A]
abbrev gA (r : ℝ) : A := algebraMap ℝ A r

def ga (i : ℕ) : A := gA (i : ℝ)

lemma t1 : ga 0 = ga 0 := by rfl

lemma t2 (h : ga 0 = ga 1) : ga 1 = ga 0 := h.symm

end
