/-
SEMREV-L3 independent review — Stage A2: how does the D12 obligation's `HasDerivAt` on the raw
function space `EuclideanSpace ℝ (Fin n) → ℝ` obtain its normed-space structure?

`#synth NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) → ℝ)` fails with only
`import Poincare.L3.HeatTimeDeriv.All` in scope. This file inspects the exact instance
arguments stored in the D12 declaration and tries to reconstruct the goal from scratch.
-/

import Poincare.L3.HeatTimeDeriv.All

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace SemrevL3

-- Exact stored statement, all implicit arguments shown.
set_option pp.all true in
#print Poincare.D12.ParabolicLocal.mildToClassicalBridge

-- The signature of the Pi-derivative lemma, all arguments shown.
set_option pp.all true in
#check @hasDerivAt_pi

-- Can the exact goal of the D12 obligation be restated from scratch?
example {n : ℕ} {t : ℝ} (ht : 0 < t) (f : Poincare.D12.ParabolicLocal.BUCn n) :
    HasDerivAt
      (fun s : ℝ => fun x : EuclideanSpace ℝ (Fin n) =>
        (Poincare.D12.ParabolicLocal.heatConv n s f.val) x)
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y : EuclideanSpace ℝ (Fin n),
          Poincare.D10.HeatKernelEuclidean.gaussianKernel n t (x - y) *
            (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * f.val y) t :=
  (Poincare.D12.ParabolicLocal.mildToClassicalBridge n) ht f

-- Which instance does Lean use in a *freshly elaborated* `HasDerivAt` over this function space?
set_option pp.all true in
#check (fun (g : ℝ → EuclideanSpace ℝ (Fin 4) → ℝ) (g' : EuclideanSpace ℝ (Fin 4) → ℝ) =>
  (HasDerivAt g g' 0 : Prop))

end SemrevL3
