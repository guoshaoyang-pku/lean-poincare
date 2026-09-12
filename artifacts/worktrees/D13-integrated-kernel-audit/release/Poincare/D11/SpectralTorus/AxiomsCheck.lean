import Poincare.D11.SpectralTorus.Laplacian
import Poincare.D11.SpectralTorus.Parseval
import Poincare.D11.SpectralTorus.Sobolev
import Poincare.D11.SpectralTorus.Poincare

/-! # Axiom audit for the D11 spectral-torus island

Every theorem below must print only `[propext, Classical.choice, Quot.sound]`.
-/

open Poincare.D11.SpectralTorus

#print axioms torusFourier_abs_eq_one
#print axioms fourierMode_periodic
#print axioms torusEquivUnitAddTorus
#print axioms differentiableAt_fourierMode
#print axioms laplacian_fourierMode
#print axioms torusLaplacian_mFourier
#print axioms mFourier_isEigenfunction
#print axioms trigPoly_parseval
#print axioms trigPoly_integral
#print axioms trigPoly_mean_zero_iff
#print axioms summable_sobolevWeight_inv
#print axioms sobolev_embedding_trigPoly
#print axioms one_le_normSq_of_ne_zero
#print axioms poincare_trigPoly
#print axioms torusDeriv_mFourier
