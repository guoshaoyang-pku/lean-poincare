import Poincare.D7.Reduced.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Poincare.D7.Reduced.Certificate

**D7 reduced length / reduced volume layer, part 2: reduced-volume certificates and their
algebraic monotonicity consequences.**

Perelman's reduced volume `Ṽ(τ) = ∫ (4πτ)^{-n/2} e^{-l(q,τ)} dV(q)` is nonincreasing in backward
time `τ` along a Ricci flow.  The analytic content of the proof is a differential inequality for
the reduced length `l` together with a differentiation-under-the-integral argument.  The pinned
mathlib has neither the path-space theory nor the Ricci-flow PDE, so this module isolates the
**order-algebraic skeleton**:

* `ReducedVolumeCertificate` — the continuum certificate: a volume functional `Ṽ` with an explicit
  backward-time derivative, a nonpositive derivative field and a nonnegativity field.  The
  derivative sign is the analytic input; the passage to monotonicity is the checked consequence
  `antitoneOn`, and `volume_le_of_le`, `volume_le_at`, `neg_log_monotoneOn` are its algebraic
  consequences.
* `FiniteReducedVolumeCertificate` — the finite-density certificate: a family of densities
  `ρᵢ : ℝ → ℝ`, each with an explicit derivative, a nonpositive derivative field, and the total
  volume `∑ᵢ ρᵢ`.  The total volume is proved nonincreasing.
* `ReducedLengthDensityCertificate` — the **Gaussian weight certificate** with the actual
  reduced-volume shape `ρᵢ(τ) = exp(-(n/2) log(4πτ) - lᵢ(τ))`.  Its field is the Perelman-type
  lower bound `lᵢ'(τ) ≥ -n/(2τ)`; the checked consequence is that each Gaussian weight has
  nonpositive derivative, hence the finite reduced volume `∑ᵢ ρᵢ(τ)` is nonincreasing.  This is
  the exact algebraic mechanism by which the reduced-length differential inequality implies
  reduced-volume monotonicity, with the Laplacian, gradient and scalar-curvature terms of the
  continuum inequality left in the explicit certificate field.
* `zeroReducedLengthDensityCertificate` and `criticalReducedLengthDensityCertificate` — explicit
  non-vacuity instances (the second has constant density `1`).

Every proof is complete; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` in this file.  The unproved continuum monotonicity theorem is not asserted: it is
represented by the explicit fields of `ReducedVolumeCertificate`.
-/

open MeasureTheory intervalIntegral Set
open scoped RealInnerProductSpace

namespace Poincare
namespace D7
namespace Reduced

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. The continuum reduced-volume certificate -/

/-- **Reduced-volume certificate.**  The volume functional `Ṽ : ℝ → ℝ`, its backward-time
derivative `derivative`, and the analytic hypotheses:

* `hasDerivAt_volume` — differentiability at every positive backward time with the stated
  derivative (the differentiation-under-the-integral step);
* `derivative_nonpos` — the derivative is nonpositive (the reduced-length differential
  inequality plus nonnegativity of the Gaussian weight);
* `volume_nonneg` — the reduced volume is nonnegative.

The monotonicity consequence is `ReducedVolumeCertificate.antitoneOn`, proved from these fields by
the mean-value theorem. -/
structure ReducedVolumeCertificate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    where
  /-- The underlying metric-flow interface. -/
  flow : MetricFlowInterface E
  /-- The reduced volume functional `Ṽ(τ)`. -/
  volume : ℝ → ℝ
  /-- The backward-time derivative of `Ṽ`. -/
  derivative : ℝ → ℝ
  /-- Differentiability with the stated derivative at every positive backward time. -/
  hasDerivAt_volume : ∀ τ : ℝ, 0 < τ → HasDerivAt volume (derivative τ) τ
  /-- The derivative is nonpositive. -/
  derivative_nonpos : ∀ τ : ℝ, 0 < τ → derivative τ ≤ 0
  /-- The reduced volume is nonnegative. -/
  volume_nonneg : ∀ τ : ℝ, 0 < τ → 0 ≤ volume τ

namespace ReducedVolumeCertificate

variable (C : ReducedVolumeCertificate E)

/-- **Checked consequence (mean-value theorem).**  The nonpositive derivative field gives
monotonicity of the reduced volume on positive backward times. -/
theorem antitoneOn : AntitoneOn C.volume (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (C.hasDerivAt_volume x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx
    exact (C.hasDerivAt_volume x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    rw [(C.hasDerivAt_volume x hx).deriv]
    exact C.derivative_nonpos x hx

/-- **The reduced volume functional** of the certificate. -/
def reducedVolume (τ : ℝ) : ℝ := C.volume τ

/-- **Algebraic monotonicity consequence for the reduced volume functional.** -/
theorem reducedVolume_antitone : AntitoneOn C.reducedVolume (Set.Ioi 0) :=
  C.antitoneOn

/-- **Algebraic consequence (comparison).**  The reduced volume at a later backward time is at
most its value at an earlier positive backward time. -/
theorem volume_le_of_le {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h : τ₁ ≤ τ₂) :
    C.volume τ₂ ≤ C.volume τ₁ :=
  C.antitoneOn h₁ (h₁.trans_le h) h

/-- **Algebraic consequence (reference time).**  For `τ ≥ τ₀ > 0` the reduced volume at `τ` is at
most its value at `τ₀`. -/
theorem volume_le_at {τ₀ τ : ℝ} (h₀ : 0 < τ₀) (h : τ₀ ≤ τ) :
    C.volume τ ≤ C.volume τ₀ :=
  C.volume_le_of_le h₀ h

/-- **Algebraic consequence (initial-time bound).**  For `1 ≤ τ` the reduced volume at `τ` is at
most its value at `1`. -/
theorem volume_le_one {τ : ℝ} (h : 1 ≤ τ) : C.volume τ ≤ C.volume 1 :=
  C.volume_le_of_le zero_lt_one h

/-- **Algebraic consequence (entropy monotonicity).**  If the reduced volume is positive, then
`τ ↦ -log Ṽ(τ)` is nondecreasing on positive backward times. -/
theorem neg_log_monotoneOn (hpos : ∀ τ : ℝ, 0 < τ → 0 < C.volume τ) :
    MonotoneOn (fun τ => -Real.log (C.volume τ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hle : C.volume y ≤ C.volume x := C.antitoneOn hx hy hxy
  have hx' : 0 < C.volume x := hpos x hx
  have hy' : 0 < C.volume y := hpos y hy
  have hlog : Real.log (C.volume y) ≤ Real.log (C.volume x) := Real.log_le_log hy' hle
  linarith

end ReducedVolumeCertificate

/-! ## 2. Finite-density certificates -/

/-- **Finite reduced-volume certificate.**  A finite family of densities `ρᵢ : ℝ → ℝ`, each with
an explicit backward-time derivative, a nonpositive derivative field, and the total volume
`∑ᵢ ρᵢ`.  The intended reading is a finite model of the reduced volume integral. -/
structure FiniteReducedVolumeCertificate (ι : Type*) [Fintype ι] where
  /-- The density of the `i`-th site. -/
  density : ℝ → ι → ℝ
  /-- The backward-time derivative of the density. -/
  derivative : ℝ → ι → ℝ
  /-- Differentiability of each density with the stated derivative at positive times. -/
  hasDerivAt_density : ∀ (i : ι) (τ : ℝ), 0 < τ →
    HasDerivAt (fun s => density s i) (derivative τ i) τ
  /-- The density derivative is nonpositive at positive times. -/
  derivative_nonpos : ∀ (i : ι) (τ : ℝ), 0 < τ → derivative τ i ≤ 0

namespace FiniteReducedVolumeCertificate

variable {ι : Type*} [Fintype ι] (C : FiniteReducedVolumeCertificate ι)

/-- The **total reduced volume** `∑ᵢ ρᵢ(τ)`. -/
def volume (τ : ℝ) : ℝ := ∑ i, C.density τ i

/-- The **finite reduced volume** functional. -/
def reducedVolume (τ : ℝ) : ℝ := C.volume τ

/-- **Algebraic monotonicity consequence.**  If every density has nonpositive derivative, the
total finite reduced volume is nonincreasing on positive backward times.  The passage from the
per-site derivative fields to the sum uses `Finset.sum_le_sum` after applying the mean-value
theorem to each density. -/
theorem volume_antitone : AntitoneOn (fun τ => C.volume τ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hanti : ∀ i : ι, C.density y i ≤ C.density x i := by
    intro i
    have hmono : AntitoneOn (fun s => C.density s i) (Set.Ioi 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      · intro z hz
        exact (C.hasDerivAt_density i z hz).continuousAt.continuousWithinAt
      · rw [interior_Ioi]
        intro z hz
        exact (C.hasDerivAt_density i z hz).differentiableAt.differentiableWithinAt
      · rw [interior_Ioi]
        intro z hz
        rw [(C.hasDerivAt_density i z hz).deriv]
        exact C.derivative_nonpos i z hz
    exact hmono hx hy hxy
  unfold volume
  exact Finset.sum_le_sum fun i _ => hanti i

/-- **Algebraic monotonicity consequence (finite reduced volume).** -/
theorem reducedVolume_antitone : AntitoneOn (fun τ => C.reducedVolume τ) (Set.Ioi 0) :=
  C.volume_antitone

/-- **Algebraic consequence (comparison).**  The total finite reduced volume at a later positive
backward time is at most its value at an earlier positive backward time. -/
theorem volume_le_of_le {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h : τ₁ ≤ τ₂) :
    C.volume τ₂ ≤ C.volume τ₁ :=
  C.volume_antitone h₁ (h₁.trans_le h) h

end FiniteReducedVolumeCertificate

/-! ## 3. The Gaussian weight certificate -/

/-- **Reduced-length density certificate.**  The reduced-length data `lᵢ : ℝ → ι → ℝ`, an explicit
derivative field, and the Perelman-type lower bound `lᵢ'(τ) ≥ -n/(2τ)` at positive backward times.
The associated Gaussian weight is
`ρᵢ(τ) = exp(-(n/2) log(4πτ) - lᵢ(τ))`, the reduced-volume density with the `(4πτ)^{-n/2}`
normalisation written in exponential form. -/
structure ReducedLengthDensityCertificate (ι : Type*) [Fintype ι] where
  /-- The dimension parameter `n` of the reduced-volume normalisation. -/
  dimension : ℝ
  /-- The reduced length `lᵢ(τ)` at site `i`. -/
  reducedLength : ℝ → ι → ℝ
  /-- The backward-time derivative of the reduced length. -/
  derivative : ℝ → ι → ℝ
  /-- Differentiability of the reduced length with the stated derivative at positive times. -/
  hasDerivAt_reducedLength : ∀ (i : ι) (τ : ℝ), 0 < τ →
    HasDerivAt (fun s => reducedLength s i) (derivative τ i) τ
  /-- The Perelman-type lower bound `lᵢ'(τ) ≥ -n/(2τ)`. -/
  derivative_lower : ∀ (i : ι) (τ : ℝ), 0 < τ → -(dimension / (2 * τ)) ≤ derivative τ i

namespace ReducedLengthDensityCertificate

variable {ι : Type*} [Fintype ι] (C : ReducedLengthDensityCertificate ι)

/-- The **Gaussian weight** `ρᵢ(τ) = exp(-(n/2) log(4πτ) - lᵢ(τ))`. -/
def density (τ : ℝ) (i : ι) : ℝ :=
  Real.exp (-(C.dimension / 2) * Real.log (4 * Real.pi * τ) - C.reducedLength τ i)

/-- The total finite reduced volume `∑ᵢ ρᵢ(τ)`. -/
def volume (τ : ℝ) : ℝ := ∑ i, C.density τ i

/-- The **finite reduced volume** of the Gaussian weight certificate. -/
def reducedVolume (τ : ℝ) : ℝ := C.volume τ

/-- The derivative of the normalisation factor `-(n/2) log(4πτ)` is `-(n/2)/τ` at positive
backward times. -/
theorem hasDerivAt_normalisation {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun s : ℝ => -(C.dimension / 2) * Real.log (4 * Real.pi * s))
      (-(C.dimension / 2) / τ) τ := by
  have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) τ := by
    simpa using (hasDerivAt_id τ).const_mul (4 * Real.pi)
  have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s))
      ((4 * Real.pi) / (4 * Real.pi * τ)) τ :=
    hlin.log (by positivity)
  have hmul := hlog.const_mul (-(C.dimension / 2))
  have hcoef : -(C.dimension / 2) * ((4 * Real.pi) / (4 * Real.pi * τ)) = -(C.dimension / 2) / τ := by
    field_simp
  simpa [hcoef] using hmul

/-- **Checked derivative of the Gaussian weight.**  The density `ρᵢ` has derivative
`ρᵢ(τ) (-(n/2)/τ - lᵢ'(τ))` at positive backward times. -/
theorem density_hasDerivAt (i : ι) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun s => C.density s i)
      (C.density τ i * (-(C.dimension / 2) / τ - C.derivative τ i)) τ := by
  have harg : HasDerivAt
      (fun s : ℝ => -(C.dimension / 2) * Real.log (4 * Real.pi * s) - C.reducedLength s i)
      (-(C.dimension / 2) / τ - C.derivative τ i) τ :=
    (C.hasDerivAt_normalisation hτ).sub (C.hasDerivAt_reducedLength i τ hτ)
  simpa [density] using harg.exp

/-- **Checked sign of the Gaussian weight derivative.**  The Perelman-type lower bound
`lᵢ'(τ) ≥ -n/(2τ)` makes the derivative of the Gaussian weight nonpositive. -/
theorem density_derivative_nonpos (i : ι) {τ : ℝ} (hτ : 0 < τ) :
    C.density τ i * (-(C.dimension / 2) / τ - C.derivative τ i) ≤ 0 := by
  have hpos : 0 < C.density τ i := Real.exp_pos _
  have hle : -(C.dimension / 2) / τ ≤ C.derivative τ i := by
    have h := C.derivative_lower i τ hτ
    have hcoef : -(C.dimension / 2) / τ = -(C.dimension / (2 * τ)) := by ring
    rw [hcoef]
    exact h
  exact mul_nonpos_of_nonneg_of_nonpos hpos.le (sub_nonpos.mpr hle)

/-- The Gaussian weight certificate packaged as a finite reduced-volume certificate. -/
def toFiniteCertificate : FiniteReducedVolumeCertificate ι where
  density := C.density
  derivative := fun τ i => C.density τ i * (-(C.dimension / 2) / τ - C.derivative τ i)
  hasDerivAt_density := fun i _τ hτ => C.density_hasDerivAt i hτ
  derivative_nonpos := fun i _τ hτ => C.density_derivative_nonpos i hτ

/-- **Algebraic monotonicity consequence (Gaussian weights).**  The reduced-length differential
inequality `lᵢ' ≥ -n/(2τ)` implies that the finite reduced volume `∑ᵢ ρᵢ(τ)` is nonincreasing on
positive backward times. -/
theorem volume_antitone : AntitoneOn (fun τ => C.volume τ) (Set.Ioi 0) := by
  have h := C.toFiniteCertificate.volume_antitone
  simpa [volume, FiniteReducedVolumeCertificate.volume, toFiniteCertificate] using h

/-- **Algebraic monotonicity consequence for the finite reduced volume.** -/
theorem reducedVolume_antitone : AntitoneOn (fun τ => C.reducedVolume τ) (Set.Ioi 0) :=
  C.volume_antitone

/-- **Algebraic consequence (comparison).**  The finite reduced volume at a later positive
backward time is at most its value at an earlier positive backward time. -/
theorem volume_le_of_le {τ₁ τ₂ : ℝ} (h₁ : 0 < τ₁) (h : τ₁ ≤ τ₂) :
    C.volume τ₂ ≤ C.volume τ₁ :=
  C.volume_antitone h₁ (h₁.trans_le h) h

end ReducedLengthDensityCertificate

/-! ## 4. Non-vacuity instances -/

/-- **Constant-zero reduced-length certificate.**  With `lᵢ ≡ 0` the derivative field is `0`, and
the lower bound `0 ≥ -n/(2τ)` holds for nonnegative dimension `n` at every positive time. -/
def zeroReducedLengthDensityCertificate (ι : Type*) [Fintype ι] (n : ℝ) (hn : 0 ≤ n) :
    ReducedLengthDensityCertificate ι where
  dimension := n
  reducedLength := fun _ _ => 0
  derivative := fun _ _ => 0
  hasDerivAt_reducedLength := fun _ τ _ => hasDerivAt_const τ 0
  derivative_lower := fun _ τ hτ => by
    have hτ2 : 0 < 2 * τ := by linarith
    have hdiv : 0 ≤ n / (2 * τ) := div_nonneg hn hτ2.le
    simpa using neg_nonpos.mpr hdiv

/-- **Critical Gaussian certificate.**  With `lᵢ(τ) = -(n/2) log(4πτ)` the derivative field is
exactly `-(n/2)/τ`, so the lower bound holds with equality and the Gaussian weight is the constant
`1`. -/
def criticalReducedLengthDensityCertificate (ι : Type*) [Fintype ι] (n : ℝ) :
    ReducedLengthDensityCertificate ι where
  dimension := n
  reducedLength := fun τ _ => -(n / 2) * Real.log (4 * Real.pi * τ)
  derivative := fun τ _ => -(n / 2) / τ
  hasDerivAt_reducedLength := fun _ τ hτ => by
    have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) τ := by
      simpa using (hasDerivAt_id τ).const_mul (4 * Real.pi)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s))
        ((4 * Real.pi) / (4 * Real.pi * τ)) τ :=
      hlin.log (by positivity)
    have hmul := hlog.const_mul (-(n / 2))
    have hcoef : -(n / 2) * ((4 * Real.pi) / (4 * Real.pi * τ)) = -(n / 2) / τ := by
      field_simp
    simpa [hcoef] using hmul
  derivative_lower := fun _ τ _ => by
    have hcoef : -(n / (2 * τ)) = -(n / 2) / τ := by ring
    exact le_of_eq hcoef

/-- **Non-vacuity check.**  The critical certificate has constant Gaussian weight `1`. -/
theorem criticalReducedLengthDensityCertificate_density (ι : Type*) [Fintype ι] (n : ℝ)
    (i : ι) (τ : ℝ) :
    (criticalReducedLengthDensityCertificate ι n).density τ i = 1 := by
  simp [ReducedLengthDensityCertificate.density, criticalReducedLengthDensityCertificate]

/-- **Non-vacuity check.**  The critical certificate has constant finite reduced volume. -/
theorem criticalReducedLengthDensityCertificate_volume (ι : Type*) [Fintype ι] (n : ℝ) (τ : ℝ) :
    (criticalReducedLengthDensityCertificate ι n).volume τ = Fintype.card ι := by
  simp [ReducedLengthDensityCertificate.volume,
    criticalReducedLengthDensityCertificate_density]

/-- **Non-vacuity check.**  The zero certificate has nonincreasing finite reduced volume. -/
theorem zeroReducedLengthDensityCertificate_volume_antitone (ι : Type*) [Fintype ι]
    (n : ℝ) (hn : 0 ≤ n) :
    AntitoneOn (fun τ => (zeroReducedLengthDensityCertificate ι n hn).volume τ) (Set.Ioi 0) :=
  (zeroReducedLengthDensityCertificate ι n hn).volume_antitone

end

end Reduced
end D7
end Poincare
