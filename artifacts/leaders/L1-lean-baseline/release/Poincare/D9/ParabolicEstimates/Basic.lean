/-
Task `D9-sobolev-parabolic-estimates`: the abstract energy-functional interface and
the weak-solution data for the linear parabolic equation `∂ₜu = Δu + f`.

This file is part of the long-run Poincaré formalization.  It consumes the
release's manifold-with-measure layer in the same style as
`Poincare.Longrun.Entropy.Functional` and `Poincare.Longrun.Topology.Noncollapsing`:
the measure `μ` is abstract data (mathlib has no Riemannian volume form), and the
Laplacian enters only through a *Dirichlet form* `(u, v) ↦ ∫ ⟨∇u, ∇v⟩ dμ`, again
abstract data.  The concrete, kernel-checked finite-dimensional model is in
`Poincare.D9.ParabolicEstimates.MatrixModel`; the state-only closed-manifold
statements are in `Poincare.D9.ParabolicEstimates.Statements`.

## What is defined here

* `energyDensity μ u = ∫ |u|² dμ`, the `L²` energy density of a field;
* `EnergyFunctional X μ`: a time-dependent field `u`, a forcing `f` and an energy
  function `E` with `E t = ∫ |u t|² dμ`;
* `DirichletForm X`: the abstract Dirichlet form, symmetric and nonnegative on the
  diagonal;
* `WeakSolution X μ`: weak-solution data for `∂ₜu = Δu + f`, with the test-function
  class explicit;
* `EnergyIdentityStatement`: the energy identity
  `(d/dt) E = -2 |∇u|² + 2 ⟨u, f⟩` as a `Prop` (proved in the finite-dimensional
  model, recorded here as part of the classical-solution data);
* `ClassicalSolution`: a weak solution together with the energy identity;
* `ParabolicL2Bound`: the Grönwall bound
  `E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ ∫ |f|² dμ)` as a `Prop`, together with the checked
  reduction `parabolicL2Bound_of_energyIdentity` from the identity and the Young
  inequality.

Every proof in this file is complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/
import Poincare.D9.ParabolicEstimates.Gronwall

open MeasureTheory intervalIntegral

namespace Poincare.D9.ParabolicEstimates

universe u

/-- The `L²` energy density `∫ |u|² dμ` of a real-valued field. -/
noncomputable def energyDensity (X : Type u) [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) : ℝ :=
  ∫ x, (u x) ^ 2 ∂μ

/-- The forcing energy `∫ |f|² dμ`. -/
noncomputable def forcingEnergy (X : Type u) [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂μ

/-- **Energy-functional interface.**

A time-dependent field `u : ℝ → X → ℝ`, a forcing `f : ℝ → X → ℝ`, an energy
function `E : ℝ → ℝ`, and the defining identity `E t = ∫ |u t|² dμ`.  The measure
`μ` is the manifold-with-measure datum of the release layer. -/
structure EnergyFunctional (X : Type u) [MeasurableSpace X] (μ : Measure X) where
  /-- The time-dependent field. -/
  u : ℝ → X → ℝ
  /-- The forcing term. -/
  f : ℝ → X → ℝ
  /-- The energy functional `E(t) = ∫ |u(t)|² dμ`. -/
  E : ℝ → ℝ
  /-- The defining identity of the energy functional. -/
  energy_eq : ∀ t : ℝ, E t = energyDensity X μ (u t)
  /-- Each slice is square-integrable. -/
  integrable_energy : ∀ t : ℝ, Integrable (fun x => (u t x) ^ 2) μ

namespace EnergyFunctional

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- The energy is nonnegative. -/
theorem energy_nonneg (D : EnergyFunctional X μ) (t : ℝ) : 0 ≤ D.E t := by
  rw [D.energy_eq t, energyDensity]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- Unfolding lemma: the energy is the integral of the squared field. -/
theorem energy_eq_integral (D : EnergyFunctional X μ) (t : ℝ) :
    D.E t = ∫ x, (D.u t x) ^ 2 ∂μ := by
  rw [D.energy_eq t, energyDensity]

end EnergyFunctional

/-- **Abstract Dirichlet form.**  `form u v` is the stand-in for the Dirichlet
pairing `∫ ⟨∇u, ∇v⟩ dμ`.  It is symmetric and nonnegative on the diagonal.  No
manifold structure is assumed; the closed-manifold instantiation is recorded in
`Poincare.D9.ParabolicEstimates.Statements`. -/
structure DirichletForm (X : Type u) where
  /-- The Dirichlet pairing. -/
  form : (X → ℝ) → (X → ℝ) → ℝ
  /-- Symmetry of the pairing. -/
  symm : ∀ u v : X → ℝ, form u v = form v u
  /-- Nonnegativity of the diagonal (the gradient energy is `|∇u|² ≥ 0`). -/
  nonneg : ∀ u : X → ℝ, 0 ≤ form u u

/-- **Weak-solution data for `∂ₜu = Δu + f`.**

The weak equation is stated against an explicit test-function class `testClass`:
for every `t` and every test function `φ`,

`(d/ds) ∫ u(s) φ dμ = -form (u t) φ + ∫ f(t) φ dμ`.

The Dirichlet form encodes the integration-by-parts pairing `∫ ⟨∇u, ∇φ⟩ dμ`. -/
structure WeakSolution (X : Type u) [MeasurableSpace X] (μ : Measure X)
    extends EnergyFunctional X μ where
  /-- The Dirichlet form realizing the weak Laplacian. -/
  D : DirichletForm X
  /-- The class of admissible test functions. -/
  testClass : Set (X → ℝ)
  /-- Every time slice is an admissible test function. -/
  u_mem_testClass : ∀ t : ℝ, u t ∈ testClass
  /-- The weak parabolic equation against every test function. -/
  weak_equation : ∀ (t : ℝ) (φ : X → ℝ), φ ∈ testClass →
    HasDerivAt (fun s : ℝ => ∫ x, u s x * φ x ∂μ)
      (-(D.form (u t) φ) + ∫ x, f t x * φ x ∂μ) t

/-- **The energy identity** `(d/dt) E(t) = -2 |∇u|² + 2 ⟨u, f⟩` for a weak
solution, written as a `Prop`.  It is the analytic content proved in the
finite-dimensional matrix model and recorded here as a statement. -/
def EnergyIdentityStatement {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (S : WeakSolution X μ) : Prop :=
  ∀ t : ℝ, HasDerivAt S.E
    (-2 * S.D.form (S.u t) (S.u t) + 2 * ∫ x, S.u t x * S.f t x ∂μ) t

/-- A weak solution satisfying the energy identity: the `ClassicalSolution` data
used by the `L²` a-priori estimate. -/
structure ClassicalSolution (X : Type u) [MeasurableSpace X] (μ : Measure X)
    extends WeakSolution X μ where
  /-- The energy identity for the solution. -/
  energy_identity : EnergyIdentityStatement toWeakSolution

/-- **The parabolic `L²` Grönwall bound** `E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ ∫ |f|² dμ)`
for `C ≥ 0` and `t ≥ 0`, as a `Prop`. -/
def ParabolicL2Bound {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (S : WeakSolution X μ) (C : ℝ) : Prop :=
  0 ≤ C → ∀ t : ℝ, 0 ≤ t →
    S.E t ≤ Real.exp (C * t) * (S.E 0 + ∫ s in 0..t, forcingEnergy X μ (S.f s))

/-- **Checked reduction of the `L²` a-priori estimate to the energy identity.**

If a classical solution satisfies the pointwise Young bound
`2 ∫ u f dμ ≤ E + ∫ |f|² dμ` and the two integrability hypotheses needed by the
fundamental theorem of calculus, then the Grönwall bound
`ParabolicL2Bound S C` holds.  The proof is the checked real-analysis Grönwall
lemma `gronwall_energy_bound`; the Dirichlet form only enters through its
nonnegativity, which is what makes the gradient term dissipative. -/
theorem parabolicL2Bound_of_energyIdentity {X : Type u} [MeasurableSpace X]
    {μ : Measure X} (S : ClassicalSolution X μ) {C : ℝ} (hC : 1 ≤ C)
    (hYoung : ∀ s : ℝ, 2 * (∫ x, S.u s x * S.f s x ∂μ)
      ≤ S.E s + forcingEnergy X μ (S.f s))
    (hintY : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s =>
      Real.exp (-C * s) * ((-2 * S.D.form (S.u s) (S.u s)
        + 2 * ∫ x, S.u s x * S.f s x ∂μ) - C * S.E s)) volume 0 t)
    (hintg : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable
      (fun s => forcingEnergy X μ (S.f s)) volume 0 t) :
    ParabolicL2Bound S.toWeakSolution C := by
  intro _ t ht
  refine gronwall_energy_bound (le_trans zero_le_one hC) ht (fun s => S.energy_identity s) ?_ ?_
    (hintY t ht) (hintg t ht)
  · intro s
    have hQ : 0 ≤ S.D.form (S.u s) (S.u s) := S.D.nonneg _
    have hy := hYoung s
    have hE : 0 ≤ S.E s := S.energy_nonneg s
    nlinarith
  · intro s
    rw [forcingEnergy]
    exact integral_nonneg (fun x => sq_nonneg _)

/-- **Young's inequality under the integral sign.**  For square-integrable `u, f`
with integrable product, `2 ∫ u f dμ ≤ ∫ u² dμ + ∫ f² dμ`.  This is the pointwise
inequality `2 a b ≤ a² + b²` integrated. -/
theorem young_integral {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {u f : X → ℝ} (huf : Integrable (fun x => u x * f x) μ)
    (hu : Integrable (fun x => (u x) ^ 2) μ)
    (hf : Integrable (fun x => (f x) ^ 2) μ) :
    2 * (∫ x, u x * f x ∂μ) ≤ (∫ x, (u x) ^ 2 ∂μ) + ∫ x, (f x) ^ 2 ∂μ := by
  have hpoint : ∀ x, 2 * (u x * f x) ≤ (u x) ^ 2 + (f x) ^ 2 := fun x => by
    nlinarith [sq_nonneg (u x - f x)]
  have hmono : (∫ x, 2 * (u x * f x) ∂μ) ≤ ∫ x, ((u x) ^ 2 + (f x) ^ 2) ∂μ :=
    integral_mono (huf.const_mul 2) (hu.add hf) hpoint
  rw [MeasureTheory.integral_const_mul, integral_add hu hf] at hmono
  linarith

/-! ## Non-vacuity: the zero datum -/

/-- The zero energy functional on any measure space. -/
noncomputable def zeroEnergyFunctional (X : Type u) [MeasurableSpace X] (μ : Measure X) :
    EnergyFunctional X μ where
  u := fun _ _ => 0
  f := fun _ _ => 0
  E := fun _ => 0
  energy_eq := by
    intro t
    simp [energyDensity]
  integrable_energy := by
    intro t
    simp

/-- The zero Dirichlet form. -/
def zeroDirichletForm (X : Type u) : DirichletForm X where
  form := fun _ _ => 0
  symm := by
    intro u v
    rfl
  nonneg := by
    intro u
    rfl

/-- The zero weak solution on any measure space. -/
noncomputable def zeroWeakSolution (X : Type u) [MeasurableSpace X] (μ : Measure X) :
    WeakSolution X μ where
  toEnergyFunctional := zeroEnergyFunctional X μ
  D := zeroDirichletForm X
  testClass := Set.univ
  u_mem_testClass := fun _ => Set.mem_univ _
  weak_equation := by
    intro t φ _
    have hconst : (fun s : ℝ => ∫ x, (zeroEnergyFunctional X μ).u s x * φ x ∂μ) = fun _ => (0 : ℝ) := by
      funext s
      simp [zeroEnergyFunctional]
    rw [hconst]
    have hzero : (-(zeroDirichletForm X).form ((zeroEnergyFunctional X μ).u t) φ
        + ∫ x, (zeroEnergyFunctional X μ).f t x * φ x ∂μ) = 0 := by
      simp [zeroEnergyFunctional, zeroDirichletForm]
    rw [hzero]
    exact hasDerivAt_const t 0

/-- **Checked non-vacuity.**  The zero datum satisfies the energy identity, so the
`ClassicalSolution` interface is inhabited on every measure space. -/
noncomputable def zeroClassicalSolution (X : Type u) [MeasurableSpace X] (μ : Measure X) :
    ClassicalSolution X μ where
  toWeakSolution := zeroWeakSolution X μ
  energy_identity := by
    intro t
    have hval : (-2 * (zeroWeakSolution X μ).D.form ((zeroWeakSolution X μ).u t) ((zeroWeakSolution X μ).u t)
        + 2 * ∫ x, (zeroWeakSolution X μ).u t x * (zeroWeakSolution X μ).f t x ∂μ) = 0 := by
      simp [zeroWeakSolution, zeroEnergyFunctional, zeroDirichletForm]
    rw [hval]
    exact hasDerivAt_const t 0

/-- **Checked corollary.**  The zero datum satisfies the parabolic `L²` bound for
every `C ≥ 0`, showing the bound is not vacuous. -/
theorem zero_parabolicL2Bound (X : Type u) [MeasurableSpace X] (μ : Measure X) (C : ℝ) :
    ParabolicL2Bound (zeroClassicalSolution X μ).toWeakSolution C := by
  intro hC t ht
  simp [zeroClassicalSolution, zeroWeakSolution, zeroEnergyFunctional, forcingEnergy]

/-! ## Axiom audit -/

#print axioms energyDensity
#print axioms forcingEnergy
#print axioms EnergyFunctional
#print axioms EnergyFunctional.energy_nonneg
#print axioms EnergyFunctional.energy_eq_integral
#print axioms DirichletForm
#print axioms WeakSolution
#print axioms EnergyIdentityStatement
#print axioms ClassicalSolution
#print axioms ParabolicL2Bound
#print axioms parabolicL2Bound_of_energyIdentity
#print axioms young_integral
#print axioms zeroEnergyFunctional
#print axioms zeroDirichletForm
#print axioms zeroWeakSolution
#print axioms zeroClassicalSolution
#print axioms zero_parabolicL2Bound

end Poincare.D9.ParabolicEstimates
