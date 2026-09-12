-- A3 round-3 kernel-checked evidence for the phantom-parameter defect in the
-- D12-geometric-compactness statement-only frontier (finding F12a).
-- Written by D13-cross-audit-360-cards; not derived from the producer card.
--
-- The unused-binder screen shows that `harmonicCoordinatesExistence`,
-- `cheegerGromovCompactness` and `bishopGromovVolumeComparison` do not use their
-- dimension / Holder-exponent parameters.  Here we prove, by `rfl`, that the
-- resulting `Prop` is literally independent of those parameters: any two
-- choices give the same statement.  Consequently proving one instance proves
-- all of them, and the interface cannot carry the dimension/exponent
-- dependence its docstrings describe.
import Poincare.D12.GeometricCompactness.Frontier

namespace A3R3

open Poincare.D12.GeometricCompactness

/-- The harmonic-coordinates frontier is independent of `n` and `α`. -/
theorem a3_harmonicCoordinates_phantom (n n' : ℕ) (α α' : ℝ) (R : Type*)
    (C : R → Prop) (K I : R → ℝ → Prop) :
    harmonicCoordinatesExistence n α R C K I =
      harmonicCoordinatesExistence n' α' R C K I := rfl

/-- The Cheeger-Gromov compactness frontier is independent of `n` and `α`. -/
theorem a3_cheegerGromov_phantom (n n' : ℕ) (α α' : ℝ) (P : Type*)
    (Conv : P → P → Prop) (K I D : P → ℝ → Prop) :
    cheegerGromovCompactness n α P Conv K I D =
      cheegerGromovCompactness n' α' P Conv K I D := rfl

/-- The Bishop-Gromov volume-comparison frontier is independent of `n`. -/
theorem a3_bishopGromov_phantom (n n' : ℕ) (R : Type*)
    (V : R → ℝ → ℝ) (Ric : R → ℝ → Prop) (VolModel : ℝ → ℝ) :
    bishopGromovVolumeComparison n R V Ric VolModel =
      bishopGromovVolumeComparison n' R V Ric VolModel := rfl

end A3R3

#print axioms A3R3.a3_harmonicCoordinates_phantom
#print axioms A3R3.a3_cheegerGromov_phantom
#print axioms A3R3.a3_bishopGromov_phantom
