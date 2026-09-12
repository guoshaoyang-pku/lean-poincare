/-
# Poincare.D7.EvolutionSharp.Certificates

**D7 evolution sharp restatement: D3 entropy certificates at the sharpened hypothesis.**

The D4 cluster instantiates the accepted D3 entropy certificates
(`Poincare.Longrun.Entropy.AntitoneCertificate` and
`Poincare.Longrun.Entropy.ContinuousAntitoneCertificate`) for the finite Perelman
functional at the curvature hypothesis `1 ≤ c i`. The sharpened strict theorem
`Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le` also assumes only `1 ≤ c i`, so
the certificate layer and the strict-decrease layer now share **one** hypothesis instead of
the old split (`1 ≤ c i` for certificates, `1 < c i` for strict decrease). This module

* re-instantiates the three D3 certificates in the D7 namespace at the sharpened
  hypothesis (`perelmanAntitoneCertificate_discrete_sharp`,
  `perelmanAntitoneCertificate_sharp`, `continuousPerelmanCertificate_sharp`);
* proves that the sharpened strict step **composes** with the D3 certificate's own
  consequences: comparison (`F_le_of_le`), the lower bound (`lower_le_value`), and
  flat-spot rigidity (`eq_of_le_of_eq`), the last in the form
  `perelmanAntitoneCertificate_discrete_sharp_no_strict_step_of_eq`: if the functional is
  constant between `m` and `n`, no intermediate step can have a strictly positive reaction;
* shows backward compatibility: the promoted hypothesis `1 < c i` still yields the same D3
  certificate, because it is a special case of `1 ≤ c i`;
* exhibits the sharpened certificate at the threshold `c ≡ 1`, the case the promoted strict
  theorem excluded.

## Analytic boundary (explicit)

The certificates are honest inhabitants of the D3 structures: the `mono` field is the
promoted (non-strict) monotonicity theorem, and the `lower_le` field is nonnegativity of the
finite functional under `0 ≤ c i`, which follows from `1 ≤ c i`. The strict addendum is a
separate theorem, not a certificate field, because strictness holds only at steps with
strictly positive reaction and positive step size. All hypotheses are displayed. No
continuous or manifold-level statement is asserted. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.Witnesses
import Poincare.Longrun.Entropy.Certificate

open Set
open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy
open Poincare.Longrun.Evolution

universe w

variable {ι : Type w} [Fintype ι]

/-! ## The discrete D3 certificate at the sharpened hypothesis -/

/-- **Sharpened discrete D3 certificate.** The D3 `AntitoneCertificate` over `ℕ` for the
finite Perelman functional along the explicit-Euler recurrence, at the weakest curvature
hypothesis `1 ≤ c i` and `0 ≤ h`. Its `mono` field is the promoted non-strict monotonicity
theorem; its lower bound is `0`. -/
noncomputable def perelmanAntitoneCertificate_discrete_sharp (F : ReactionField ι)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) :
    AntitoneCertificate ℕ (fun n => perelmanF c (traj n)) where
  mono := fun _ _ hab =>
    Poincare.Longrun.Evolution.perelmanF_antitone_discrete F hc hh ev hab
  lowerBound := 0
  lower_le := fun _ => perelmanF_nonneg fun i => le_trans zero_le_one (hc i)

/-- **Composition with the sharpened strict step.** At any step with `0 < h` and a strictly
positive reaction at some component, the D3 certificate's monotonicity is strict. -/
theorem perelmanAntitoneCertificate_discrete_sharp_strict_step (F : ReactionField ι)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {n : ℕ} {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  perelmanF_step_lt_of_one_le F hc hh ev hi

/-- **D3 certificate consequence (comparison)** at the sharpened hypothesis, via the D3
structure's own `F_le_of_le`. -/
theorem perelmanAntitoneCertificate_discrete_sharp_compare (F : ReactionField ι)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {m n : ℕ} (hmn : m ≤ n) :
    perelmanF c (traj n) ≤ perelmanF c (traj m) :=
  (perelmanAntitoneCertificate_discrete_sharp F hc hh ev).F_le_of_le hmn

/-- **D3 certificate consequence (lower bound)** at the sharpened hypothesis, via the D3
structure's own `lower_le_value`. -/
theorem perelmanAntitoneCertificate_discrete_sharp_lower (F : ReactionField ι)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) (n : ℕ) :
    0 ≤ perelmanF c (traj n) :=
  (perelmanAntitoneCertificate_discrete_sharp F hc hh ev).lower_le_value n

/-- **Flat-spot rigidity composed with the sharpened strict step.** If the functional is
constant between `m` and `n` (`m ≤ n`), the D3 certificate forces it constant in between;
then no intermediate step can have a strictly positive reaction, because the sharpened
strict theorem would contradict constancy. -/
theorem perelmanAntitoneCertificate_discrete_sharp_no_strict_step_of_eq (F : ReactionField ι)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {m n : ℕ} (_hmn : m ≤ n)
    (heq : perelmanF c (traj m) = perelmanF c (traj n)) :
    ∀ k : ℕ, m ≤ k → k < n → ∀ i : ι, ¬ (0 < F.eval (traj k) i) := by
  intro k hmk hkn i hi
  have hcert := perelmanAntitoneCertificate_discrete_sharp F hc (le_of_lt hh) ev
  have hk : perelmanF c (traj k) = perelmanF c (traj m) :=
    hcert.eq_of_le_of_eq heq k hmk (le_of_lt hkn)
  have hk1 : perelmanF c (traj (k + 1)) = perelmanF c (traj m) :=
    hcert.eq_of_le_of_eq heq (k + 1) (Nat.le_succ_of_le hmk) (Nat.succ_le_of_lt hkn)
  have hstrict : perelmanF c (traj (k + 1)) < perelmanF c (traj k) :=
    perelmanF_step_lt_of_one_le F hc hh ev hi
  rw [hk, hk1] at hstrict
  exact lt_irrefl _ hstrict

/-- **Backward compatibility.** The promoted hypothesis `∀ i, 1 < c i` still produces the
same D3 certificate, because it implies the sharpened hypothesis `∀ i, 1 ≤ c i`. -/
noncomputable def perelmanAntitoneCertificate_discrete_of_old (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 < c i) {h : ℝ} (hh : 0 ≤ h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) :
    AntitoneCertificate ℕ (fun n => perelmanF c (traj n)) :=
  perelmanAntitoneCertificate_discrete_sharp F (fun i => le_of_lt (hc i)) hh ev

/-- **Non-vacuity at the sharpened hypothesis.** The promoted constant reaction field with
the nontrivial discrete flow `n ↦ n` inhabits the sharpened discrete certificate. -/
theorem perelmanAntitoneCertificate_discrete_sharp_nonvacuous (c : ι → ℝ) (hc : ∀ i, 1 ≤ c i) :
    (perelmanAntitoneCertificate_discrete_sharp (unitReactionField : ReactionField ι) hc
      (h := 1) (by norm_num) (unitDiscreteEvolution (ι := ι))).lowerBound ≤
      perelmanF c (fun _ : ι => (0 : ℝ)) := by
  simpa using
    (perelmanAntitoneCertificate_discrete_sharp (unitReactionField : ReactionField ι) hc
      (h := 1) (by norm_num) (unitDiscreteEvolution (ι := ι))).lower_le_value 0

/-! ## The continuous D3 certificates at the sharpened hypothesis -/

/-- **Sharpened continuous interval D3 certificate.** The D3 `AntitoneCertificate` on the
time subtype `{t // t ∈ Icc 0 T}` for the finite Perelman functional along the D2 reaction
ODE, at the sharpened hypothesis `1 ≤ c i`. -/
noncomputable def perelmanAntitoneCertificate_sharp (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {T : ℝ} {traj : ℝ → ι → ℝ} (ev : EvolutionRelation F T traj) :
    AntitoneCertificate {t : ℝ // t ∈ Icc 0 T} (fun t => perelmanF c (traj t.1)) where
  mono := fun a b hab =>
    Poincare.Longrun.Evolution.perelmanF_antitone F hc ev a.2 b.2 (show a.1 ≤ b.1 from hab)
  lowerBound := 0
  lower_le := fun _ => perelmanF_nonneg fun i => le_trans zero_le_one (hc i)

/-- **Sharpened continuous D3 certificate.** The accepted D3 `ContinuousAntitoneCertificate`
for the finite counting-measure `EntropyData` family along a global D2 reaction flow, at the
sharpened hypothesis `1 ≤ c i`. All analytic fields (derivative, continuity, derivative
sign, lower bound) are the promoted checked inhabitants. -/
noncomputable def continuousPerelmanCertificate_sharp [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {F : ReactionField ι} {traj : ℝ → ι → ℝ}
    (G : GlobalReactionFlow F traj) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) :
    ContinuousAntitoneCertificate (fun t : ℝ => finiteReactionEntropyData c (traj t)) :=
  Poincare.Longrun.Evolution.continuousPerelmanCertificate G hc

/-- **D3 continuous certificate consequence (initial comparison)** at the sharpened
hypothesis, via the D3 structure's own `F_le_initial`. -/
theorem continuousPerelmanCertificate_sharp_le_initial [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {F : ReactionField ι} {traj : ℝ → ι → ℝ}
    (G : GlobalReactionFlow F traj) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    (finiteReactionEntropyData c (traj t)).F ≤ (finiteReactionEntropyData c (traj 0)).F :=
  (continuousPerelmanCertificate_sharp G hc).F_le_initial ht

/-- **Non-vacuity at the sharpened hypothesis.** The promoted constant reaction field with
the nontrivial global flow `t ↦ t` inhabits the sharpened continuous D3 certificate. -/
theorem continuousPerelmanCertificate_sharp_nonvacuous [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (c : ι → ℝ) (hc : ∀ i, 1 ≤ c i) :
    (continuousPerelmanCertificate_sharp (unitGlobalFlow (ι := ι)) hc).lowerBound ≤
      (finiteReactionEntropyData c (fun _ : ι => (0 : ℝ))).F :=
  (continuousPerelmanCertificate_sharp (unitGlobalFlow (ι := ι)) hc).lower_le_initial

/-! ## Composition at the newly admitted threshold `c ≡ 1` -/

/-- **The sharpened discrete certificate covers the threshold `c ≡ 1`**, the case excluded
by the promoted strict theorem's hypothesis `1 < c i`. The certificate's comparison
consequence is applied to the explicit square-field witness. -/
theorem perelmanAntitoneCertificate_discrete_sharp_at_one :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) ≤
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0) :=
  perelmanAntitoneCertificate_discrete_sharp_compare (squareField : ReactionField (Fin 1))
    (c := fun _ : Fin 1 => (1 : ℝ)) (fun _ => le_rfl) (h := 1) (by norm_num)
    (traj := sharpWitnessTraj) sharpWitnessTraj_evolution (m := 0) (n := 1) (by norm_num)

/-- **The sharpened certificate's strict addendum at the threshold `c ≡ 1`.** The same
witness step is strictly decreasing via the sharpened strict theorem, so the certificate's
comparison is strict at the newly admitted boundary. -/
theorem perelmanAntitoneCertificate_discrete_sharp_strict_at_one :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0) :=
  perelmanAntitoneCertificate_discrete_sharp_strict_step (squareField : ReactionField (Fin 1))
    (c := fun _ : Fin 1 => (1 : ℝ)) (fun _ => le_rfl) (h := 1) (by norm_num)
    (traj := sharpWitnessTraj) sharpWitnessTraj_evolution (n := 0) (i := 0)
    sharpWitness_reaction_pos

/-! ## Axiom audit -/

#print axioms perelmanAntitoneCertificate_discrete_sharp
#print axioms perelmanAntitoneCertificate_discrete_sharp_strict_step
#print axioms perelmanAntitoneCertificate_discrete_sharp_compare
#print axioms perelmanAntitoneCertificate_discrete_sharp_lower
#print axioms perelmanAntitoneCertificate_discrete_sharp_no_strict_step_of_eq
#print axioms perelmanAntitoneCertificate_discrete_of_old
#print axioms perelmanAntitoneCertificate_discrete_sharp_nonvacuous
#print axioms perelmanAntitoneCertificate_sharp
#print axioms continuousPerelmanCertificate_sharp
#print axioms continuousPerelmanCertificate_sharp_le_initial
#print axioms continuousPerelmanCertificate_sharp_nonvacuous
#print axioms perelmanAntitoneCertificate_discrete_sharp_at_one
#print axioms perelmanAntitoneCertificate_discrete_sharp_strict_at_one

end EvolutionSharp
end D7
end Poincare
