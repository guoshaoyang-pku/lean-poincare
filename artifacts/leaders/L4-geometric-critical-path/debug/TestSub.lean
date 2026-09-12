import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Set Filter
open scoped Topology
open Poincare.D12.ComparisonGeodesics

example {du ddu : ℝ → ℝ} {x : ℝ} (h : HasDerivAtR du (ddu x) x) :
    HasDerivAtR (fun s => du s - 1) (ddu x - 0) x := by
  convert h.sub (hasDerivAtR_const (1 : ℝ) x) using 1
  ext s
  simp only [Pi.sub_apply]
  ring

example {u du : ℝ → ℝ} {x : ℝ} (h : HasDerivAtR u (du x) x) :
    HasDerivAtR (fun s => u s - s) (du x - 1) x := by
  convert h.sub (hasDerivAtR_id x) using 1
  ext s
  simp only [Pi.sub_apply]
  ring
