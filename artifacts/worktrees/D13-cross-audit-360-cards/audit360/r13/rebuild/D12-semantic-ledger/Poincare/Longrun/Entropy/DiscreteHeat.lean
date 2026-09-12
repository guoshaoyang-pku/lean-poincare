/-
Task `D3-entropy-interface`: consume the accepted `D2-pde-foundation` result card.

**Scope and honesty boundary.** Nothing here is a proof of Perelman's entropy
monotonicity or of the Poincaré conjecture.  The D2 finite-grid ℓ² energy is used
only as a *non-vacuous discrete instance* of the order-algebraic monotonicity
certificate of `Poincare.Longrun.Entropy.Certificate`.  The continuous
Ricci-flow certificate remains conditional on the statement-only bridge in
`Poincare.Longrun.Entropy.Bridge`.

Consumed card: `longrun/results/D2-pde-foundation.md` and its worktree sources
`Poincare/Longrun/PDE/{HeatGrid,DiscreteMaximumPrinciple,Energy,ContinuousInterface}.lean`
(copied byte-identically; sha256 recorded in the result card).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/
import Poincare.Longrun.PDE.Energy
import Poincare.Longrun.Entropy.Certificate

open scoped BigOperators

namespace Poincare.Longrun.PDE

/-- **Discrete-time antitonicity of the D2 ℓ² energy.**  This strengthens the D2
statement `energy_nonincreasing` (which compares every time to time `0`) to full
antitonicity: for `s ≤ t`, `energy (u t) ≤ energy (u s)`.  It is proved from the
D2 one-step estimate `energy_succ_le` by induction. -/
theorem HeatGridEvolution.energy_antitone {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    Antitone fun t : ℕ => energy (ev.u t) N := by
  intro s t hst
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ n _hmn ih => exact (ev.energy_succ_le hα0 hα1 n).trans ih

/-- The zero evolution on the finite grid: a concrete inhabitant of the D2
structure, used to witness that the certificate instance below is non-vacuous. -/
def zeroHeatGridEvolution (N : ℕ) (α : ℝ) : HeatGridEvolution N α where
  u := fun _ _ => 0
  boundary_left := fun _ => rfl
  boundary_right := fun _ => rfl
  step := fun _ _ _ _ => by simp

end Poincare.Longrun.PDE

namespace Poincare.Longrun.Entropy

open Poincare.Longrun.PDE

/-- **The D2 ℓ² energy as an antitone certificate over discrete time.**
Assumptions: the CFL/convexity condition `0 ≤ α ≤ 1/2` (explicit), zero Dirichlet
boundary (fields of `HeatGridEvolution`), and the ℓ² energy `Σ (u i)^2`.  The
lower bound `0` is the D2 theorem `energy_nonneg`. -/
noncomputable def heatEnergyCertificate {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    AntitoneCertificate ℕ (fun t : ℕ => energy (ev.u t) N) where
  mono := ev.energy_antitone hα0 hα1
  lowerBound := 0
  lower_le := fun t => energy_nonneg (ev.u t) N

/-- **Certificate consequence (comparison).**  The certificate's comparison
consequence recovers the D2 global energy monotonicity statement. -/
theorem heatEnergy_le_initial {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (t : ℕ) :
    energy (ev.u t) N ≤ energy (ev.u 0) N :=
  (heatEnergyCertificate ev hα0 hα1).F_le_at (Nat.zero_le t)

/-- **Certificate consequence (lower bound).**  The energy is nonnegative at all
times, read off from the certificate. -/
theorem heatEnergy_nonneg {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (t : ℕ) :
    0 ≤ energy (ev.u t) N :=
  (heatEnergyCertificate ev hα0 hα1).lower_le_value t

/-- **Certificate consequence (flat-spot rigidity).**  If the energy at time `t`
equals the initial energy, the energy is constant on `[0, t]`. -/
theorem heatEnergy_eq_of_eq_initial {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) {t : ℕ}
    (heq : energy (ev.u t) N = energy (ev.u 0) N) :
    ∀ s : ℕ, s ≤ t → energy (ev.u s) N = energy (ev.u 0) N := by
  intro s hs
  exact (heatEnergyCertificate ev hα0 hα1).eq_of_le_of_eq heq.symm s (Nat.zero_le s) hs

/-- The certificate is inhabited by the zero evolution on every grid: the
discrete interface is not vacuous. -/
theorem heatEnergyCertificate_zero (N : ℕ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    (heatEnergyCertificate (zeroHeatGridEvolution N α) hα0 hα1).lowerBound ≤
      energy ((zeroHeatGridEvolution N α).u 0) N :=
  (heatEnergyCertificate (zeroHeatGridEvolution N α) hα0 hα1).lower_le_value 0

/-! ## Axiom audit -/

#print axioms Poincare.Longrun.PDE.HeatGridEvolution.energy_antitone
#print axioms Poincare.Longrun.PDE.zeroHeatGridEvolution
#print axioms heatEnergyCertificate
#print axioms heatEnergy_le_initial
#print axioms heatEnergy_nonneg
#print axioms heatEnergy_eq_of_eq_initial
#print axioms heatEnergyCertificate_zero

end Poincare.Longrun.Entropy
