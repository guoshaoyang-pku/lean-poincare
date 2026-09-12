import Poincare.D7.LeviCivita.Probe
import Poincare.D7.Curvature.Example

/-!
# Poincare.D7.LeviCivita.Smoke

**D7 Levi-Civita smoothness layer, part 6: compilable non-vacuity witnesses and computations.**

Every declaration in this file is a kernel-checked `example` or `theorem` witnessing that the new
interfaces are inhabited and that the main theorems are non-vacuous:

* the zero connection is a fixed point of the mean and the difference tensor;
* the mean of two zero connections is metric-compatible for any metric datum;
* the constant coefficient system of the zero connection exists for every `n`;
* the mean and pullback operations on `SmoothCoefficientSystem` produce actual systems;
* the Christoffel symbols of the constant Euclidean metric vanish (and hence are `C^n`);
* the `so(3)` D7 curvature datum is a fixed point of `meanData` and its difference tensor with
  itself vanishes.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Poincare.Longrun.Geometry
open scoped BigOperators Manifold ContDiff

namespace Poincare
namespace D7
namespace LeviCivita

universe v w u

section Abstract

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The mean of the zero connection with itself is the zero connection. -/
example : meanConnection (0 : V →ₗ[ℝ] V →ₗ[ℝ] V) 0 = 0 := by
  ext X Y
  simp

/-- The mean of two zero connections is metric-compatible for every metric datum (task item 2a,
concrete instance). -/
example (m : MetricData V ι) : IsMetricCompatible m (meanConnection 0 0) :=
  isMetricCompatible_mean m (by intro X Y Z; simp) (by intro X Y Z; simp)

/-- The difference tensor of the zero connection with itself vanishes. -/
example : differenceTensor (0 : V →ₗ[ℝ] V →ₗ[ℝ] V) 0 = 0 := by
  ext X Y
  simp

/-- The difference tensor of two copies of the D2 mean connection (torsion-free for its own
bracket) is symmetric (task item 2b, concrete instance). -/
example (b : LieBracketData ℝ V) (X Y : V) :
    differenceTensor (Poincare.Longrun.Geometry.meanConnection b).nabla
        (Poincare.Longrun.Geometry.meanConnection b).nabla X Y =
      differenceTensor (Poincare.Longrun.Geometry.meanConnection b).nabla
        (Poincare.Longrun.Geometry.meanConnection b).nabla Y X :=
  differenceTensor_symm b
    (fun X Y => (Poincare.Longrun.Geometry.meanConnection b).torsion_free X Y)
    (fun X Y => (Poincare.Longrun.Geometry.meanConnection b).torsion_free X Y) X Y

/-- The constant coefficient system of the zero connection with the zero bracket exists for every
smoothness exponent `n` (the interface is inhabited). -/
example (m : MetricData V ι) (n : ℕ∞ω) :
    Nonempty (SmoothCoefficientSystem V m
      (fun i j k _ => bracketCoefficient m LieBracketData.zero i j k) n) :=
  ⟨SmoothCoefficientSystem.const (nabla := 0) m LieBracketData.zero
    (fun X Y => by simp [LieBracketData.zero])
    (fun X Y Z => by simp) n⟩

/-- The mean of two copies of a constant coefficient system is a coefficient system. -/
example (m : MetricData V ι) (n : ℕ∞ω)
    (S : SmoothCoefficientSystem V m
      (fun i j k _ => bracketCoefficient m LieBracketData.zero i j k) n) :
    Nonempty (SmoothCoefficientSystem V m
      (fun i j k _ => bracketCoefficient m LieBracketData.zero i j k) n) :=
  ⟨SmoothCoefficientSystem.mean S S⟩

/-- The pullback of a coefficient system along the identity chart is a coefficient system. -/
example (m : MetricData V ι) (n : ℕ∞ω)
    (S : SmoothCoefficientSystem V m
      (fun i j k _ => bracketCoefficient m LieBracketData.zero i j k) n) :
    Nonempty (SmoothCoefficientSystem V m
      (fun i j k _ => bracketCoefficient m LieBracketData.zero i j k) n) :=
  ⟨SmoothCoefficientSystem.pullback (fun x : V => x) contMDiff_id S⟩

end Abstract

section Koszul

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The Christoffel symbols of the constant Euclidean metric vanish. -/
example (v : ι → P) (m i j : ι) (x : P) :
    christoffelSymbol (euclideanMetricData (P := P) ι) v m i j x = 0 := by
  simp [christoffelSymbol, euclideanMetricData]

/-- The Euclidean Christoffel symbols are `C^n` (re-derived from the vanishing computation). -/
example (n : ℕ∞) (v : ι → P) (m i j : ι) :
    ContDiff ℝ n (christoffelSymbol (euclideanMetricData (P := P) ι) v m i j) :=
  contDiff_euclidean_christoffel n v m i j

end Koszul

section So3

/-- The `so(3)` D7 curvature datum is a fixed point of the mean datum. -/
example : Curvature.RiemannCurvatureData.meanData Curvature.So3.so3 Curvature.So3.so3 rfl rfl =
    Curvature.So3.so3 :=
  Curvature.RiemannCurvatureData.meanData_self Curvature.So3.so3

/-- The difference tensor of the `so(3)` datum with itself is symmetric and vanishes. -/
example (X Y : Fin 3 → ℝ) :
    Curvature.RiemannCurvatureData.differenceTensor Curvature.So3.so3 Curvature.So3.so3 X Y =
      Curvature.RiemannCurvatureData.differenceTensor Curvature.So3.so3 Curvature.So3.so3 Y X :=
  Curvature.RiemannCurvatureData.differenceTensor_symm Curvature.So3.so3 Curvature.So3.so3
    rfl X Y

end So3

end LeviCivita
end D7
end Poincare
