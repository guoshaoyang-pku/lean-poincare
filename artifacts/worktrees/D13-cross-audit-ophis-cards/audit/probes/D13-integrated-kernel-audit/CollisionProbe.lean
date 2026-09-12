/-
Independent cross-audit collision probe: importing the two modules that (independently) declare
`Poincare.D7.ConjugateHeat.ConjugateHeatData` in the same environment must be rejected by Lean.
This file is expected to FAIL to elaborate; the exact error is the collision evidence.
-/
import Poincare.D7.ConjugateHeat.Basic
import Poincare.D7.Monotonicity.ConjugateHeatCertificate
