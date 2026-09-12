/-
SEMREV-L3 independent review — round 2, Stage A3: corrected restatement + ambient structure.

The round-1 `StageA2.lean` probe attempted to restate the D12 statement from scratch and apply
`mildToClassicalBridge n` directly; that attempt errors with "Function expected ... but this term
has type Prop" — a *probe artifact*: `mildToClassicalBridge` is a `def : Prop`, and the
elaborator does not unfold semireducible definitions merely to apply a term. This file performs
the restatement correctly (unfold the def in the hypothesis, then apply), and re-confirms the
ambient structure:

  * an independently written copy of the obligation's statement is inhabited by the L3 theorem,
    so the from-scratch restatement and the D12 body are definitionally equal;
  * `#synth TopologicalSpace/AddCommGroup/Module` on `EuclideanSpace ℝ (Fin 3) → ℝ` succeed via
    the Pi instances (product topology + pointwise module), while `SemrevSynthFail.lean` shows
    `NormedAddCommGroup` on the same type does *not* synthesize — the instance-level proof that
    the obligation's `HasDerivAt` is the topological-vector-space one, i.e. pointwise in `x`.
-/

import Poincare.L3.HeatTimeDeriv.All

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace SemrevL3

/-- The D12 obligation's goal, written out from scratch and inhabited by the L3 theorem. -/
example {n : ℕ} {t : ℝ} (ht : 0 < t) (f : Poincare.D12.ParabolicLocal.BUCn n) :
    HasDerivAt
      (fun s : ℝ => fun x : EuclideanSpace ℝ (Fin n) =>
        (Poincare.D12.ParabolicLocal.heatConv n s f.val) x)
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y : EuclideanSpace ℝ (Fin n),
          Poincare.D10.HeatKernelEuclidean.gaussianKernel n t (x - y) *
            (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * f.val y) t := by
  have h : Poincare.D12.ParabolicLocal.mildToClassicalBridge n :=
    Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds n
  unfold Poincare.D12.ParabolicLocal.mildToClassicalBridge at h
  exact h ht f

-- The L3 theorem inhabits the D12 name, by type ascription (kernel-checked).
example (n : ℕ) : Poincare.D12.ParabolicLocal.mildToClassicalBridge n :=
  Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds n

-- Ambient structure: product topology + pointwise module (TVS `HasDerivAt`), not a Banach space.
#synth TopologicalSpace (EuclideanSpace ℝ (Fin 3) → ℝ)
#synth AddCommGroup (EuclideanSpace ℝ (Fin 3) → ℝ)
#synth Module ℝ (EuclideanSpace ℝ (Fin 3) → ℝ)

end SemrevL3
