/-
Task `D3-entropy-interface`: monotonicity certificates for F/W-style functionals.

**Scope and honesty boundary.** Nothing here is a proof of Perelman's entropy
monotonicity or of the Poincaré conjecture.  This file defines:

* `MonotoneCertificate` / `AntitoneCertificate`: purely order-algebraic
  certificates (a monotonicity field plus a one-sided bound), with checked
  algebraic consequences (comparison, flat-spot rigidity);
* `ContinuousMonotoneCertificate` / `ContinuousAntitoneCertificate`: the same
  certificates with **all analytic assumptions explicit** — a time derivative
  with a sign, continuity of the functional, and the one-sided bound.  The
  passage from the derivative sign to monotonicity is the mean-value theorem and
  is proved here;
* `LinearDecayCertificate`: a certificate with an explicit linear decay rate,
  whose checked consequence is a finite lifetime bound.

The analytic assumptions are the fields of the structures, so a consumer must
display them at every use site.  The missing manifold-level theorems that would
produce the derivative field from a genuine Ricci flow are statement-only in
`Poincare.Longrun.Entropy.Bridge`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/
import Poincare.Longrun.Entropy.Functional

open MeasureTheory Set

namespace Poincare.Longrun.Entropy

universe u

/-! ## Order-algebraic certificates -/

/-- **Nondecreasing certificate.**  `F` is nondecreasing along the order `T` and
bounded above by `upperBound`.  Both fields are assumptions; the consequences
below are algebraic. -/
structure MonotoneCertificate (T : Type*) [Preorder T] (F : T → ℝ) : Type where
  /-- Monotonicity assumption. -/
  mono : Monotone F
  /-- The upper bound. -/
  upperBound : ℝ
  /-- The bound is valid at every time. -/
  upper_le : ∀ t : T, F t ≤ upperBound

namespace MonotoneCertificate

variable {T : Type*} [Preorder T] {F : T → ℝ}

/-- **Algebraic consequence 1 (comparison).**  At later times the functional is
larger. -/
theorem F_le_of_le (c : MonotoneCertificate T F) {s t : T} (h : s ≤ t) : F s ≤ F t :=
  c.mono h

/-- Comparison with a fixed reference time. -/
theorem F_ge_at (c : MonotoneCertificate T F) {t₀ t : T} (h : t₀ ≤ t) : F t₀ ≤ F t :=
  c.mono h

/-- The bound holds at every time. -/
theorem le_upper (c : MonotoneCertificate T F) (t : T) : F t ≤ c.upperBound :=
  c.upper_le t

/-- **Algebraic consequence 2 (flat-spot rigidity).**  If `F s = F t` for
`s ≤ t`, then `F` is constant on the whole interval `[s, t]`. -/
theorem eq_of_le_of_eq (c : MonotoneCertificate T F) {s t : T}
    (heq : F s = F t) : ∀ u : T, s ≤ u → u ≤ t → F u = F s := by
  intro u hsu hut
  have h1 : F s ≤ F u := c.mono hsu
  have h2 : F u ≤ F s := by
    have := c.mono hut
    linarith
  exact le_antisymm h2 h1

end MonotoneCertificate

/-- **Nonincreasing certificate.**  `F` is nonincreasing along the order `T` and
bounded below by `lowerBound`. -/
structure AntitoneCertificate (T : Type*) [Preorder T] (F : T → ℝ) : Type where
  /-- Monotonicity assumption. -/
  mono : Antitone F
  /-- The lower bound. -/
  lowerBound : ℝ
  /-- The bound is valid at every time. -/
  lower_le : ∀ t : T, lowerBound ≤ F t

namespace AntitoneCertificate

variable {T : Type*} [Preorder T] {F : T → ℝ}

/-- **Algebraic consequence 1 (comparison).**  At later times the functional is
smaller. -/
theorem F_le_of_le (c : AntitoneCertificate T F) {s t : T} (h : s ≤ t) : F t ≤ F s :=
  c.mono h

/-- Comparison with a fixed reference time. -/
theorem F_le_at (c : AntitoneCertificate T F) {t₀ t : T} (h : t₀ ≤ t) : F t ≤ F t₀ :=
  c.mono h

/-- The bound holds at every time. -/
theorem lower_le_value (c : AntitoneCertificate T F) (t : T) : c.lowerBound ≤ F t :=
  c.lower_le t

/-- **Algebraic consequence 2 (flat-spot rigidity).**  If `F s = F t` for
`s ≤ t`, then `F` is constant on the whole interval `[s, t]`. -/
theorem eq_of_le_of_eq (c : AntitoneCertificate T F) {s t : T}
    (heq : F s = F t) : ∀ u : T, s ≤ u → u ≤ t → F u = F s := by
  intro u hsu hut
  have h1 : F u ≤ F s := c.mono hsu
  have h2 : F s ≤ F u := by
    have := c.mono hut
    linarith
  exact le_antisymm h1 h2

end AntitoneCertificate

/-! ## Continuous certificates over `ℝ` with explicit analytic assumptions -/

/-- **Continuous nondecreasing certificate.**

The analytic assumptions are fields: `dissipation` is the time derivative of the
functional along the flow; `hasDerivAt_F` asserts the derivative exists at every
positive time with that value; `continuousOn_F` is continuity on `[0, ∞)`;
`dissipation_nonneg` is the sign of the derivative; `upper_le` is the one-sided
bound.  The passage to monotonicity is the checked consequence `monotoneOn`. -/
structure ContinuousMonotoneCertificate {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) : Type where
  /-- The time derivative of `t ↦ F (E t)`. -/
  dissipation : ℝ → ℝ
  /-- Differentiability along the flow with the stated derivative. -/
  hasDerivAt_F : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => (E s).F) (dissipation t) t
  /-- Continuity on `[0, ∞)`, including the endpoint `0`. -/
  continuousOn_F : ContinuousOn (fun s : ℝ => (E s).F) (Ici 0)
  /-- The derivative is nonnegative: the monotonicity assumption. -/
  dissipation_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ dissipation t
  /-- The upper bound. -/
  upperBound : ℝ
  /-- The bound is valid for all nonnegative times. -/
  upper_le : ∀ t : ℝ, 0 ≤ t → (E t).F ≤ upperBound

namespace ContinuousMonotoneCertificate

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : ℝ → EntropyData X μ}

/-- **Checked consequence (mean-value theorem).**  The derivative sign and
continuity give monotonicity on `[0, ∞)`. -/
theorem monotoneOn (c : ContinuousMonotoneCertificate E) :
    MonotoneOn (fun s : ℝ => (E s).F) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) c.continuousOn_F
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    exact (c.hasDerivAt_F x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    rw [(c.hasDerivAt_F x hx').deriv]
    exact c.dissipation_nonneg x hx'

/-- **Algebraic consequence.**  The functional at time `0` is a lower bound for
all later times. -/
theorem F_ge_initial (c : ContinuousMonotoneCertificate E) {t : ℝ} (ht : 0 ≤ t) :
    (E 0).F ≤ (E t).F :=
  c.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- **Algebraic consequence (flat-spot rigidity).**  If the functional returns to
its initial value at time `t ≥ 0`, it is constant on `[0, t]`. -/
theorem eq_on_Icc_of_eq_at (c : ContinuousMonotoneCertificate E) {t : ℝ} (ht : 0 ≤ t)
    (heq : (E t).F = (E 0).F) {s : ℝ} (hs : s ∈ Icc 0 t) : (E s).F = (E 0).F := by
  obtain ⟨hs0, hst⟩ := mem_Icc.mp hs
  have h1 : (E 0).F ≤ (E s).F :=
    c.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs0) hs0
  have h2 : (E s).F ≤ (E t).F :=
    c.monotoneOn (mem_Ici.mpr hs0) (mem_Ici.mpr ht) hst
  rw [heq] at h2
  exact le_antisymm h2 h1

/-- The continuous certificate restricts to the order-algebraic certificate on
the subtype `{t // 0 ≤ t}`. -/
noncomputable def toMonotoneCertificateOnIci (c : ContinuousMonotoneCertificate E) :
    MonotoneCertificate {t : ℝ // 0 ≤ t} (fun t => (E t.1).F) where
  mono := fun _a _b hab => c.monotoneOn _a.2 _b.2 hab
  upperBound := c.upperBound
  upper_le := fun t => c.upper_le t.1 t.2

end ContinuousMonotoneCertificate

/-- **Continuous nonincreasing certificate.**  The sign of the derivative is
nonpositive and the one-sided bound is a lower bound. -/
structure ContinuousAntitoneCertificate {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) : Type where
  /-- The time derivative of `t ↦ F (E t)`. -/
  dissipation : ℝ → ℝ
  /-- Differentiability along the flow with the stated derivative. -/
  hasDerivAt_F : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => (E s).F) (dissipation t) t
  /-- Continuity on `[0, ∞)`. -/
  continuousOn_F : ContinuousOn (fun s : ℝ => (E s).F) (Ici 0)
  /-- The derivative is nonpositive. -/
  dissipation_nonpos : ∀ t : ℝ, 0 < t → dissipation t ≤ 0
  /-- The lower bound. -/
  lowerBound : ℝ
  /-- The bound is valid for all nonnegative times. -/
  lower_le : ∀ t : ℝ, 0 ≤ t → lowerBound ≤ (E t).F

namespace ContinuousAntitoneCertificate

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : ℝ → EntropyData X μ}

/-- **Checked consequence (mean-value theorem).**  The nonpositive derivative and
continuity give antitonicity on `[0, ∞)`. -/
theorem antitoneOn (c : ContinuousAntitoneCertificate E) :
    AntitoneOn (fun s : ℝ => (E s).F) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) c.continuousOn_F
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    exact (c.hasDerivAt_F x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    rw [(c.hasDerivAt_F x hx').deriv]
    exact c.dissipation_nonpos x hx'

/-- **Algebraic consequence.**  The initial value is an upper bound for all later
times. -/
theorem F_le_initial (c : ContinuousAntitoneCertificate E) {t : ℝ} (ht : 0 ≤ t) :
    (E t).F ≤ (E 0).F :=
  c.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- **Algebraic consequence.**  The lower bound is valid at time `0`. -/
theorem lower_le_initial (c : ContinuousAntitoneCertificate E) : c.lowerBound ≤ (E 0).F :=
  c.lower_le 0 le_rfl

/-- **Algebraic consequence (flat-spot rigidity).**  If the functional returns to
its initial value at time `t ≥ 0`, it is constant on `[0, t]`. -/
theorem eq_on_Icc_of_eq_at (c : ContinuousAntitoneCertificate E) {t : ℝ} (ht : 0 ≤ t)
    (heq : (E t).F = (E 0).F) {s : ℝ} (hs : s ∈ Icc 0 t) : (E s).F = (E 0).F := by
  obtain ⟨hs0, hst⟩ := mem_Icc.mp hs
  have h1 : (E s).F ≤ (E 0).F :=
    c.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs0) hs0
  have h2 : (E 0).F ≤ (E s).F := by
    have h3 : (E t).F ≤ (E s).F :=
      c.antitoneOn (mem_Ici.mpr hs0) (mem_Ici.mpr ht) hst
    rw [heq] at h3
    exact h3
  exact le_antisymm h1 h2

/-- The continuous certificate restricts to the order-algebraic certificate on
the subtype `{t // 0 ≤ t}`. -/
noncomputable def toAntitoneCertificateOnIci (c : ContinuousAntitoneCertificate E) :
    AntitoneCertificate {t : ℝ // 0 ≤ t} (fun t => (E t.1).F) where
  mono := fun _a _b hab => c.antitoneOn _a.2 _b.2 hab
  lowerBound := c.lowerBound
  lower_le := fun t => c.lower_le t.1 t.2

end ContinuousAntitoneCertificate

/-! ## Linear decay certificate -/

/-- **Linear decay certificate.**  A nonincreasing certificate together with an
explicit positive rate and the decay inequality
`F (E t) ≤ F (E 0) - rate * t` for `t ≥ 0`.  The checked consequence
`time_le` is a finite-lifetime bound: the functional cannot stay above
`lowerBound` beyond `(F (E 0) - lowerBound) / rate`. -/
structure LinearDecayCertificate {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) : Type where
  /-- The underlying nonincreasing certificate. -/
  cert : ContinuousAntitoneCertificate E
  /-- The linear decay rate. -/
  rate : ℝ
  /-- The rate is positive. -/
  rate_pos : 0 < rate
  /-- The linear decay inequality. -/
  decay : ∀ t : ℝ, 0 ≤ t → (E t).F ≤ (E 0).F - rate * t

namespace LinearDecayCertificate

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : ℝ → EntropyData X μ}

/-- **Algebraic consequence.**  The initial value is an upper bound. -/
theorem F_le_initial (c : LinearDecayCertificate E) {t : ℝ} (ht : 0 ≤ t) :
    (E t).F ≤ (E 0).F :=
  c.cert.F_le_initial ht

/-- **Algebraic consequence (finite lifetime bound).**  From
`lowerBound ≤ F (E t)` and `F (E t) ≤ F (E 0) - rate * t` with `rate > 0`, every
nonnegative time satisfies `t ≤ (F (E 0) - lowerBound) / rate`. -/
theorem time_le (c : LinearDecayCertificate E) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ ((E 0).F - c.cert.lowerBound) / c.rate := by
  have h1 : c.cert.lowerBound ≤ (E t).F := c.cert.lower_le t ht
  have h2 : (E t).F ≤ (E 0).F - c.rate * t := c.decay t ht
  have h3 : t * c.rate ≤ (E 0).F - c.cert.lowerBound := by linarith
  rw [le_div_iff₀ c.rate_pos]
  linarith

/-- **Algebraic consequence.**  The lower bound holds at every nonnegative
time. -/
theorem lower_le_value (c : LinearDecayCertificate E) {t : ℝ} (ht : 0 ≤ t) :
    c.cert.lowerBound ≤ (E t).F :=
  c.cert.lower_le t ht

end LinearDecayCertificate

/-! ## Non-vacuity: the zero datum -/

/-- The zero entropy datum on the one-point space with counting measure: all
curvature, potential and weight densities vanish.  This shows the interface is
inhabited. -/
noncomputable def zeroEntropyData : EntropyData Unit (Measure.count : Measure Unit) where
  R := 0
  gradSq := 0
  f := 0
  ρ := 0
  τ := 1
  τ_pos := one_pos
  n := 0
  riccHess := 0
  ρ_nonneg := fun _ => le_rfl
  integrable_F := Integrable.of_finite
  integrable_W := Integrable.of_finite

/-- The zero datum has zero `F`. -/
theorem zeroEntropyData_F : EntropyData.F zeroEntropyData = 0 := by
  simp [EntropyData.F, zeroEntropyData]

/-- The zero family satisfies the continuous nondecreasing certificate: a checked
witness that the certificate is not vacuous. -/
noncomputable def continuousMonotoneCertificate_zero :
    ContinuousMonotoneCertificate (fun _ : ℝ => zeroEntropyData) where
  dissipation := fun _ => 0
  hasDerivAt_F := by
    intro t _ht
    have h : (fun _ : ℝ => EntropyData.F zeroEntropyData) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact zeroEntropyData_F
    rw [h]
    exact hasDerivAt_const t 0
  continuousOn_F := by
    have h : (fun _ : ℝ => EntropyData.F zeroEntropyData) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact zeroEntropyData_F
    rw [h]
    exact continuousOn_const
  dissipation_nonneg := fun _ _ => le_rfl
  upperBound := 0
  upper_le := by
    intro _t _ht
    exact le_of_eq zeroEntropyData_F

/-- The zero family is also a nonincreasing certificate. -/
noncomputable def continuousAntitoneCertificate_zero :
    ContinuousAntitoneCertificate (fun _ : ℝ => zeroEntropyData) where
  dissipation := fun _ => 0
  hasDerivAt_F := by
    intro t _ht
    have h : (fun _ : ℝ => EntropyData.F zeroEntropyData) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact zeroEntropyData_F
    rw [h]
    exact hasDerivAt_const t 0
  continuousOn_F := by
    have h : (fun _ : ℝ => EntropyData.F zeroEntropyData) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact zeroEntropyData_F
    rw [h]
    exact continuousOn_const
  dissipation_nonpos := fun _ _ => le_rfl
  lowerBound := 0
  lower_le := by
    intro _t _ht
    exact le_of_eq zeroEntropyData_F.symm

/-! ## Axiom audit -/

#print axioms MonotoneCertificate
#print axioms MonotoneCertificate.F_le_of_le
#print axioms MonotoneCertificate.eq_of_le_of_eq
#print axioms AntitoneCertificate
#print axioms AntitoneCertificate.F_le_of_le
#print axioms AntitoneCertificate.eq_of_le_of_eq
#print axioms ContinuousMonotoneCertificate
#print axioms ContinuousMonotoneCertificate.monotoneOn
#print axioms ContinuousMonotoneCertificate.F_ge_initial
#print axioms ContinuousMonotoneCertificate.eq_on_Icc_of_eq_at
#print axioms ContinuousMonotoneCertificate.toMonotoneCertificateOnIci
#print axioms ContinuousAntitoneCertificate
#print axioms ContinuousAntitoneCertificate.antitoneOn
#print axioms ContinuousAntitoneCertificate.F_le_initial
#print axioms ContinuousAntitoneCertificate.lower_le_initial
#print axioms ContinuousAntitoneCertificate.eq_on_Icc_of_eq_at
#print axioms ContinuousAntitoneCertificate.toAntitoneCertificateOnIci
#print axioms LinearDecayCertificate
#print axioms LinearDecayCertificate.time_le
#print axioms LinearDecayCertificate.lower_le_value
#print axioms zeroEntropyData
#print axioms zeroEntropyData_F
#print axioms continuousMonotoneCertificate_zero
#print axioms continuousAntitoneCertificate_zero

end Poincare.Longrun.Entropy
