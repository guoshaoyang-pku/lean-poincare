/-
SEMREV-L3 independent review — Stage C2: constructed inputs and downstream consumers.

Unlike the parent card's `#check` probes (which only ascribe types to *hypothetical* data), this
file constructs a concrete `BUC` datum, instantiates the discharged obligation, the packaged
solution, the uniform statement and the `BCFn` derivative at it, and consumes their fields.
-/

import Poincare.L3.HeatTimeDeriv.All

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace SemrevL3

open Poincare.D10.HeatKernelEuclidean
open Poincare.D12.ParabolicLocal
open Poincare.L3.HeatTimeDeriv

/-! ## 1. A concrete input: the constant-one BUC datum on ℝ³ (and ℝ⁰, ℝ¹) -/

def f3 : BUCn 3 :=
  ⟨BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin 3)) (1 : ℝ),
    uniformContinuous_const⟩

def f0 : BUCn 0 :=
  ⟨BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin 0)) (0 : ℝ),
    uniformContinuous_const⟩

example : (f3 : EuclideanSpace ℝ (Fin 3) → ℝ) 0 = 1 := rfl
example : (f0 : EuclideanSpace ℝ (Fin 0) → ℝ) 0 = 0 := rfl

/-! ## 2. The discharged D12 obligation, instantiated at the concrete datum -/

example (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => fun x : EuclideanSpace ℝ (Fin 3) => (heatConv 3 s f3.val) x)
      (fun x : EuclideanSpace ℝ (Fin 3) => timeDerivIntegral 3 t f3.val x) t :=
  mildToClassicalBridge_pointwise 3 ht f3

example : mildToClassicalBridge 0 := mildToClassicalBridge_holds 0

/-! ## 3. The packaged solution, with its fields consumed at the concrete datum -/

example : (heatConv_classicalHeatSolution 3 f3).T = 1 := rfl

example (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (heatConv_classicalHeatSolution 3 f3).T)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s : ℝ => (heatConv_classicalHeatSolution 3 f3).u s x)
      (∫ y : EuclideanSpace ℝ (Fin 3),
        (Δ (gaussianKernel 3 t) (x - y)) * (heatConv_classicalHeatSolution 3 f3).u₀ y) t :=
  (heatConv_classicalHeatSolution 3 f3).isSolution t ht x

example : Tendsto (heatConv_classicalHeatSolution 3 f3).u (𝓝[>] (0 : ℝ))
    (𝓝 (heatConv_classicalHeatSolution 3 f3).u₀) :=
  (heatConv_classicalHeatSolution 3 f3).initial

/-! ## 4. The uniform statement instantiated; δ extracted and used at a concrete x -/

example (t : ℝ) (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
      ∀ x : EuclideanSpace ℝ (Fin 3),
        |(heatConv 3 (t + h) f3.val x - heatConv 3 t f3.val x) / h
          - timeDerivIntegral 3 t f3.val x| < 1 :=
  uniformMildToClassicalBridge_holds 3 ht f3 1 (by norm_num)

/-! ## 5. A genuine consumer of the Banach-space derivative: continuity of the orbit -/

example (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => heatConv 3 s f3.val) t :=
  (hasDerivAt_heatConv_BCF 3 ht f3).continuousAt

example (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatConv 3 s f3.val) (timeDerivBCF 3 ht f3) t :=
  hasDerivAt_heatConv_BCF 3 ht f3

/-! ## 6. Consistency / non-vacuity of the derivative formula at the concrete datum -/

example (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin 0)) :
    (∫ y : EuclideanSpace ℝ (Fin 0),
      gaussianKernel 0 t (x - y) * timeCoeff 0 t (x - y) * (1 : ℝ)) = 0 :=
  integral_timeDerivKernel_mul_const 0 ht x

example (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin 3)) :
    Poincare.D12.HeatSemigroup.heatOperator 3 t (fun _ => (5 : ℝ)) x = 5 :=
  heatOperator_const 3 ht 5 x

/-! ## 7. The residual `SpatialLaplacianBridge` is a `def : Prop` (statement-only) -/

#check @SpatialLaplacianBridge
#check @UniformMildToClassicalBridge

end SemrevL3
