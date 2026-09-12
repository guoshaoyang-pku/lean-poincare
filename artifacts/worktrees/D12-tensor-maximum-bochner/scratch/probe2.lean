import Mathlib.Tactic

namespace Probe
universe v w uA
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {A : Type uA} [CommRing A] [Algebra ℝ A]
variable {D : V →ₗ[ℝ] A →ₗ[ℝ] A}

abbrev gA (r : ℝ) : A := algebraMap ℝ A r

variable (hleib : ∀ (X : V) (f g : A), D X (f * g) = D X f * g + f * D X g)

lemma test_one (X : V) : D X (1 : A) = 0 := by
  have h := hleib X (1 : A) (1 : A)
  simpa using (add_right_eq_self.mp h.symm)

end Probe
