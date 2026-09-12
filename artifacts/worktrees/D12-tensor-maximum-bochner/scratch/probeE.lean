import Mathlib.Tactic

section
universe w uA
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {A : Type uA} [AddCommGroup A]

abbrev VF (A : Type uA) (ι : Type w) : Type (max uA w) := ι → A

variable (f : ι → ι → A) (g : ι → ι → A) (u : A)

def fieldLaplacianProbe : VF A ι :=
  fun j => ∑ i : ι,
    f i j
      - g i j

end
