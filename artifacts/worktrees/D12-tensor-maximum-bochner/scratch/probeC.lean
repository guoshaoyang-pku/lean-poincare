import Mathlib.Tactic

section
universe w uA
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {A : Type uA} [AddCommGroup A]

abbrev VF (A : Type uA) (ι : Type w) : Type (max uA w) := ι → A

def foo (u : A) : VF A ι :=
  fun j => ∑ i : ι,
    u
      - u

def bar (u : A) : VF A ι :=
  fun j => ∑ i : ι, u - u

end
