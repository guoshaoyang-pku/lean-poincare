import Mathlib

example {A : Type*} [AddCommGroup A] (S F U1 U2 : A) :
    S + F - U1 + U2 = S + F - (U1 - U2) := by
  abel

example {A : Type*} [AddCommGroup A] (S F U1 U2 : A) :
    S + F - U1 + U2 = S + F - (U1 - U2) := by
  abel_nf
