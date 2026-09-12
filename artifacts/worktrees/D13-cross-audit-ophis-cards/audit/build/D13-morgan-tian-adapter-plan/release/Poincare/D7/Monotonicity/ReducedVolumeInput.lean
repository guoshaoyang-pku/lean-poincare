/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-perelman-conditional-monotonicity)

**D7 conditional monotonicity assembly, part 1: consumption of the D7 reduced-length /
reduced-volume certificate and its dictionary into the D3 `EntropyData` interface.**

The D7 reduced-volume certificate of `Poincare.D7.Reduced.Certificate` is part of this
worktree's scaffold and is imported directly (no vendoring).  This file

* re-exports the certificate's checked monotonicity consequences in the backward-time form
  used by the entropy assembly (`ReducedVolumeCertificate.antitoneOn`, `volume_le_of_le`,
  `neg_log_monotoneOn`, and the nonincreasing `log` form);
* proves the **dictionary lemma** `hasConjugateWeight_of_reducedLengthDensity`: the Gaussian
  reduced-volume weight `ρ(τ,i) = exp(-(n/2) log (4πτ) - l(τ,i))` of a
  `ReducedLengthDensityCertificate` is exactly the D3 conjugate weight `e^{-f}` for the
  potential `f(τ,i) = (n/2) log (4πτ) + l(τ,i)`.  This is how the reduced-volume certificate
  feeds the D3 `EntropyData` composition lemmas;
* records the **open input `B-D7-W-REDUCED-DUALITY`** as the structure
  `ReducedVolumeWDuality`: `W = log Ṽ + correction` with an antitone correction, which is the
  monotonicity-relevant consequence of Perelman's variational identification of the `W`
  minimiser with the reduced length.  The structure is a hypothesis bundle, never an axiom,
  and `antitoneOn_of_reducedVolumeWDuality` derives backward-time antitonicity of `W` from the
  certificate's antitonicity of `Ṽ`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Reduced.Certificate
import Poincare.Longrun.Entropy.Functional

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Poincare
namespace D7
namespace Monotonicity

universe u

noncomputable section

open Poincare.D7.Reduced
open Poincare.Longrun.Entropy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. Backward-time consequences of the D7 reduced-volume certificate -/

/-- **Consumption of `ReducedVolumeCertificate.antitoneOn`.**  The certified reduced volume is
nonincreasing on positive backward times. -/
theorem reducedVolume_antitone_of_certificate (C : ReducedVolumeCertificate E) :
    AntitoneOn C.volume (Set.Ioi 0) :=
  C.antitoneOn

/-- **Consumption of `ReducedVolumeCertificate.volume_le_of_le`.**  The reduced volume at a
later positive backward time is at most its value at an earlier one. -/
theorem reducedVolume_le_of_le (C : ReducedVolumeCertificate E) {τ₁ τ₂ : ℝ}
    (h₁ : 0 < τ₁) (h : τ₁ ≤ τ₂) : C.volume τ₂ ≤ C.volume τ₁ :=
  C.volume_le_of_le h₁ h

/-- **Consumption of `ReducedVolumeCertificate.neg_log_monotoneOn`.**  If the reduced volume is
positive, then `τ ↦ -log Ṽ(τ)` is nondecreasing on positive backward times. -/
theorem neg_log_reducedVolume_monotoneOn (C : ReducedVolumeCertificate E)
    (hpos : ∀ τ : ℝ, 0 < τ → 0 < C.volume τ) :
    MonotoneOn (fun τ : ℝ => -Real.log (C.volume τ)) (Set.Ioi 0) :=
  C.neg_log_monotoneOn hpos

/-- **Nonincreasing `log` form.**  If the reduced volume is positive, then `τ ↦ log Ṽ(τ)` is
nonincreasing on positive backward times.  This is the form consumed by the `W`-duality
transfer below. -/
theorem log_reducedVolume_antitoneOn (C : ReducedVolumeCertificate E)
    (hpos : ∀ τ : ℝ, 0 < τ → 0 < C.volume τ) :
    AntitoneOn (fun τ : ℝ => Real.log (C.volume τ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact Real.log_le_log (hpos y hy) (C.antitoneOn hx hy hxy)

/-! ## 2. The Gaussian reduced-volume density is a D3 conjugate weight -/

/-- **Dictionary: reduced-length density is a conjugate weight.**  Let `C` be a D7
`ReducedLengthDensityCertificate` with Gaussian weight `ρ(τ,i) = exp(-(n/2) log (4πτ) - l(τ,i))`
and let `D` be a D3 `EntropyData` whose density and potential agree with that certificate at
`(τ,i)`:
`D.ρ x = C.density τ i` and `D.f x = (n/2) log (4πτ) + l(τ,i)`.  Then `D` has the D3
conjugate weight `HasConjugateWeight`.  This is the checked bridge from the reduced-volume
layer into the D3 `EntropyData` composition lemmas. -/
theorem hasConjugateWeight_of_reducedLengthDensity {X : Type u} [MeasurableSpace X]
    {μ : Measure X} {ι : Type*} [Fintype ι]
    (C : ReducedLengthDensityCertificate ι) (D : EntropyData X μ) (τ : ℝ) (i : ι)
    (hρ : ∀ x : X, D.ρ x = C.density τ i)
    (hf : ∀ x : X, D.f x = (C.dimension / 2) * Real.log (4 * Real.pi * τ)
      + C.reducedLength τ i) :
    D.HasConjugateWeight := by
  intro x
  rw [hρ, hf, ReducedLengthDensityCertificate.density]
  congr 1
  ring

/-! ## 3. The open `W`-reduced-volume duality input -/

/-- **Open input `B-D7-W-REDUCED-DUALITY` (statement-only hypothesis bundle).**

Perelman's variational identification of the `W`-entropy minimiser with the reduced length
implies that, along the flow, `W` is the logarithm of the reduced volume plus a correction
that is antitone in backward time.  The exact normalisation constant and the minimiser
identification `f = l + n/2` are **not** formalised in this program; this structure records
the monotonicity-relevant consequence as explicit hypotheses:

* `duality : W τ = log (C.volume τ) + correction τ` at every positive backward time;
* `correction_antitone : AntitoneOn correction (Ioi 0)`;
* `volume_pos : Ṽ > 0` on positive backward times, which is what makes `log Ṽ` antitone when
  `Ṽ` is antitone.

The structure is a hypothesis bundle, not an axiom: `antitoneOn_of_reducedVolumeWDuality`
derives antitonicity of `W` from the certificate `C.antitoneOn` and these fields. -/
structure ReducedVolumeWDuality (W : ℝ → ℝ) (C : ReducedVolumeCertificate E) where
  /-- The correction term in `W = log Ṽ + correction`. -/
  correction : ℝ → ℝ
  /-- The correction is antitone in backward time. -/
  correction_antitone : AntitoneOn correction (Set.Ioi 0)
  /-- The duality identity at every positive backward time. -/
  duality : ∀ τ : ℝ, 0 < τ → W τ = Real.log (C.volume τ) + correction τ
  /-- Positivity of the reduced volume on positive backward times. -/
  volume_pos : ∀ τ : ℝ, 0 < τ → 0 < C.volume τ

/-- **Checked transfer `B-D7-W-REDUCED-DUALITY`.**  If the `W`-functional satisfies the
reduced-volume duality of `ReducedVolumeWDuality`, then `W` is nonincreasing in backward time.
The proof consumes the certificate's antitonicity (`ReducedVolumeCertificate.antitoneOn`) and
the monotonicity of `Real.log` on positive reals. -/
theorem antitoneOn_of_reducedVolumeWDuality {W : ℝ → ℝ} {C : ReducedVolumeCertificate E}
    (D : ReducedVolumeWDuality W C) : AntitoneOn W (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [D.duality x hx, D.duality y hy]
  have hlog : Real.log (C.volume y) ≤ Real.log (C.volume x) :=
    Real.log_le_log (D.volume_pos y hy) (C.antitoneOn hx hy hxy)
  have hcorr : D.correction y ≤ D.correction x := D.correction_antitone hx hy hxy
  linarith

/-- **Comparison form of the duality transfer.**  Under the duality, the `W`-value at a later
positive backward time is at most its value at an earlier one. -/
theorem W_le_of_le_of_reducedVolumeWDuality {W : ℝ → ℝ} {C : ReducedVolumeCertificate E}
    (D : ReducedVolumeWDuality W C) {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h : τ₁ ≤ τ₂) :
    W τ₂ ≤ W τ₁ :=
  antitoneOn_of_reducedVolumeWDuality D h₁ (h₁.trans_le h) h

end

end Monotonicity
end D7
end Poincare
