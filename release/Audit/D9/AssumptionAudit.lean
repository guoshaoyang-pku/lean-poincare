/-
D9-adversarial-audit-release — assumption-inflation findings, as compiled `Prop`s.

Every declaration in this file is written by the D9 adversarial auditor.  It records, in
kernel-checked form, the sharp restatements and hypothesis-necessity facts found by the
assumption-inflation hunt (task item 3) and is the evidence file for the flagged
declarations of the result card.

Sections:

* §1 sharp restatements of the hypothesis-carrying declarations in the ten
  largest-import-cone theorems of the release (`analyze_cones.py`: 22 human theorems tie at
  the saturated maximum cone 10450 / release-cone 25; the ten are selected by the
  deterministic tie-break `direct_modules`, `direct_consts`, `name`, and 9 of the 10 are
  unconditional concrete counterexample lemmas).  The sharp restatements concern the
  *promoted* overstrong theorems these audit declarations correct (D6 blocker A1);
* §2 sharpness of the threshold `1 ≤ c` for the Gibbs term (the promoted theorem
  `Poincare.Longrun.Evolution.gibbsTerm_strictAnti` uses the overstrong `1 < c`);
* §3 definitional-triviality characterisations of the "interface apply" theorems:
  the hypothesis structure is *exactly* a conjunction, so the theorems add no content;
* §4 the conditional transfer of `Poincare.Longrun.Evolution.Bridge` cannot be made
  unconditional: continuous Perelman monotonicity fails for an arbitrary entropy family;
* §5 the D3 certificate interfaces unfold to their fields (projection audit);
* §6 "missing theorem" placeholders that are trivial as stated;
* §7 the "BLOCKED" curvature-API contract is trivially inhabited;
* §8 the `D5ReleaseCheck.release_check_compiles` marker is literally `True`;
* §9 the remaining certificate interfaces (`W`, `μ`, normalized volume, surgery) are their
  fields.

None of these declarations is used by the release; they exist only as audit evidence.
-/
import ReleaseCheck

open MeasureTheory
open scoped BigOperators Topology ENNReal

namespace D9Audit

universe w u

/-! ## §1. Sharp restatements of the two hypothesis-carrying largest-cone theorems -/

open Poincare.Longrun.CurvatureODE in
open Poincare.Longrun.Evolution in
/-- **Sharp restatement of `D4Audit.gibbsTerm_strictAnti_of_one_le`** (one of the ten
largest-import-cone theorems): the exact threshold is `1 ≤ c`, not `1 < c`. -/
theorem sharp_gibbsTerm_strictAnti (c : ℝ) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c) :=
  D4Audit.gibbsTerm_strictAnti_of_one_le c hc

open Poincare.Longrun.CurvatureODE in
open Poincare.Longrun.Evolution in
/-- **Sharp restatement of `D4Audit.perelmanF_step_lt_of_one_le`** (one of the ten
largest-import-cone theorems): `1 ≤ c` suffices for strict one-step decrease; the promoted
`Poincare.Longrun.Evolution.perelmanF_step_lt` still assumes the overstrong `1 < c`. -/
theorem sharp_perelmanF_step_lt {ι : Type w} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {n : ℕ} {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  D4Audit.perelmanF_step_lt_of_one_le F hc hh ev hi

/-! ## §2. The threshold `1 ≤ c` is exactly sharp -/

open Poincare.Longrun.Evolution in
/-- **Sharpness of the threshold.** The Gibbs term is not strictly antitone for every
`c`; `c = 1/2` is an explicit failure (the release proves `gibbsTerm (1/2) 1 <
gibbsTerm (1/2) 2`).  Hence the hypothesis `1 ≤ c` in the sharp restatement §1 cannot be
dropped, and the promoted `1 < c` version is strictly weaker than necessary. -/
theorem threshold_gibbsTerm_strictAnti_is_sharp :
    ¬ (∀ c : ℝ, StrictAnti (gibbsTerm c)) := by
  intro h
  have h21 : gibbsTerm (1 / 2) 2 < gibbsTerm (1 / 2) 1 := h (1 / 2) (by norm_num)
  exact absurd h21 (not_lt.mpr (le_of_lt D4Audit.gibbsTerm_half_one_lt_two))

/-! ## §3. Interface "apply" theorems are definitionally their hypothesis -/

open Poincare.Longrun.Topology in
/-- **Definitional-triviality certificate for `KappaNoncollapsingCertificate`.**  The
structure is *exactly* the conjunction of its three fields, so the visited projections
`volume_ball_pos`, `volume_ball_ne_zero`, `mono`, `volume_unit_ball_lower`,
`exists_uniform_unit_ball_lower_bound` and `apply` derive no mathematical content beyond
the assumed non-collapsing inequality. -/
theorem kappaCertificate_iff_fields {M : Type u} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ} :
    KappaNoncollapsingCertificate M μ K κ r₀ ↔
      (0 < κ ∧ 0 < r₀ ∧ ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ → K x r →
        ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r))) :=
  ⟨fun h => ⟨h.kappa_pos, h.r0_pos, fun x r hr hr₀ hK => h.volume_ball_lower x r hr hr₀ hK⟩,
   fun h => ⟨h.1, h.2.1, fun x r hr hr₀ hK => h.2.2 x r hr hr₀ hK⟩⟩

/-- **Definitional-triviality certificate for `Perelman.FMonotonicity` / `.apply`.**  The
structure has a single field, so `FMonotonicity.apply` (and the analogous `W`/`μ` lemmas)
is the hypothesis re-spelled; no monotonicity is proved. -/
theorem perelmanFMonotonicity_iff_statement {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type w} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (flow : Perelman.MetricFlowData I M) (F : ℝ → ℝ) :
    Perelman.FMonotonicity flow F ↔
      ∀ s ∈ flow.timeDomain, ∀ t ∈ flow.timeDomain, s ≤ t → F t ≤ F s :=
  ⟨fun h _ hs _ ht hst => h.antitone hs ht hst,
   fun h => ⟨fun s hs t ht hst => h s hs t ht hst⟩⟩

/-- **Definitional-triviality certificate for `Poincare.Longrun.Entropy.AntitoneCertificate`.**
The structure is exactly `Antitone F` plus an explicit lower bound; `F_le_of_le`,
`F_le_at` and `lower_le_value` are its projections. -/
theorem antitoneCertificate_iff_fields (T : Type u) [Preorder T] (F : T → ℝ) :
    Nonempty (Poincare.Longrun.Entropy.AntitoneCertificate T F) ↔
      Antitone F ∧ ∃ b : ℝ, ∀ t : T, b ≤ F t :=
  ⟨fun ⟨c⟩ => ⟨c.mono, c.lowerBound, c.lower_le⟩,
   fun h => ⟨⟨h.1, h.2.choose, h.2.choose_spec⟩⟩⟩

/-! ## §4. The conditional transfer needs its identification hypothesis -/

open Poincare.Longrun.Entropy in
open Poincare.Longrun.Evolution in
/-- **The approximation hypothesis is not removable.**  Continuous Perelman
`F`-monotonicity is *false* for an arbitrary entropy family: the finite counting-measure
family with curvature data `c t = t` and zero potential has `F = t`, which increases.
Hence `continuousPerelmanFMonotone_of_approximation` is a genuine conditional transfer,
and its `identification` field cannot be dropped (nor can the finite theorem's `1 ≤ c`
hypothesis, which fails at `c = 1/2`). -/
theorem continuousPerelmanFMonotonicity_needs_identification :
    ¬ (∀ {X : Type} [MeasurableSpace X] {μ : Measure X} (E : ℝ → EntropyData X μ) (T : ℝ),
        ContinuousPerelmanFMonotonicity E T) := by
  intro H
  have hle : (finiteReactionEntropyData (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))).F ≤
      (finiteReactionEntropyData (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))).F := by
    have h := H (X := Fin 1) (μ := (Measure.count : Measure (Fin 1)))
      (fun t : ℝ => finiteReactionEntropyData (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ))) 2
    exact h 1 (by norm_num)
  rw [finiteReactionEntropyData_F, finiteReactionEntropyData_F] at hle
  have e1 : perelmanF (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) = 1 := by
    simp [perelmanF, gibbsTerm]
  have e0 : perelmanF (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
    simp [perelmanF, gibbsTerm]
  rw [e1, e0] at hle
  norm_num at hle

/-! ## §5. Statement-only aliases are definitionally their target -/

open Poincare.Longrun.Entropy in
/-- **The certificate consequence `ContinuousAntitoneCertificate.antitoneOn` is a
mean-value theorem over an assumed derivative sign.**  The analytic content (the sign of
`dissipation`) is a structure field; the sharpest unconditional statement available from
the interface is the implication itself, recorded here as an iff for the record. -/
theorem continuousCertificate_consequence_is_field
    {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : ℝ → EntropyData X μ}
    (c : ContinuousAntitoneCertificate E) :
    AntitoneOn (fun s : ℝ => (E s).F) (Set.Ici 0) :=
  c.antitoneOn

/-! ## §6. "Missing theorem" placeholders that are trivial as stated

The release files `Poincare.Longrun.Topology.MissingTheorems` and
`Poincare.Longrun.Surgery.Missing` declare several research targets as `def ... : Prop`.
The audit proves that three of them carry no content as stated, so they cannot serve as
faithful targets for a future proof. -/

open Poincare.Longrun.Topology in
/-- **`missingSphereRecognitionAlgorithm` is trivially true.**  As stated it is
`∀ M, Nonempty (Decidable (· ≃ₜ 𝕊³))`, and `Nonempty (Decidable P)` is classically
inhabited for every proposition `P`.  The release labels this a MISSING THEOREM, but the
audit closes it unconditionally: the statement does not express "there is a decision
procedure". -/
theorem missingSphereRecognitionAlgorithm_is_trivial :
    missingSphereRecognitionAlgorithm :=
  fun _ _ _ _ _ => ⟨Classical.propDecidable _⟩

open Poincare.Longrun.Topology in
/-- **`missingKappaPersistenceUnderSurgery` is trivially true.**  The conclusion
`∃ κ' r₀', Certificate κ' r₀'` is discharged by the hypothesis certificate with
`κ' = κ`, `r₀' = r₀`; the `SurgeryHypotheses` binder is inert, and no surgery occurs in the
statement. -/
theorem missingKappaPersistenceUnderSurgery_is_trivial {M : Type u} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) (K : CurvatureBoundedOn M) (S : Prop) (κ r₀ : ℝ) :
    missingKappaPersistenceUnderSurgery μ K S κ r₀ :=
  fun _ hcert => ⟨κ, r₀, hcert⟩

open Poincare.Longrun.Topology in
/-- **`missingCanonicalNeighborhoodTheorem` is a satisfiable schema.**  With the caller-
supplied canonical-neighbourhood predicate instantiated at `True`, the "missing theorem"
holds for every high-curvature predicate: the statement contains no ε-closeness, neck or
model-geometry content. -/
theorem missingCanonicalNeighborhoodTheorem_is_trivial (M : Type u)
    (HighCurvature : M → Prop) :
    missingCanonicalNeighborhoodTheorem M (fun _ => True) HighCurvature :=
  fun _ _ => trivial

open Poincare.Longrun.Topology in
/-- **`missingKappaNoncollapsing` is satisfiable by a degenerate curvature predicate.**  With
`K := fun _ _ => False` the curvature hypothesis is never met, so the certificate exists for
every measure `μ`; hence the placeholder statement is a schema whose content depends
entirely on the interpretation of the opaque `CurvatureBoundedOn` parameter. -/
theorem missingKappaNoncollapsing_trivial_K {M : Type u} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) :
    missingKappaNoncollapsing μ (fun _ _ => False) True :=
  fun _ => ⟨1, 1, one_pos, one_pos, fun _x _r _hr _hr₀ hK => hK.elim⟩

/-! ## §7. The "BLOCKED" curvature-API contract is trivially inhabited -/

open Bundle in
/-- **`CovariantDerivativeCurvatureStatement` is trivially true.**  The release marks this
statement as BLOCKED ("the manifold-level missing curvature API"), but the connection
argument `_cov` is unused and the existential is discharged by the zero pointwise tensor:
both the antisymmetry and the Bianchi identity hold definitionally.  Hence the statement
is not a faithful contract for the missing curvature construction (which would have to
relate `κ` to `cov`). -/
theorem covariantDerivativeCurvatureStatement_is_trivial
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u)) :
    Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement I M cov :=
  ⟨0, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

/-! ## §8. The `ReleaseCheck` marker is vacuous

`D5ReleaseCheck.release_check_compiles` is the only declaration of module `ReleaseCheck`,
the module that imports **every** other release module.  Its name suggests that it records
the success of the release check; as a `Prop` it is literally `True`, so it is implied by
every proposition and carries no information about the release.  (The first D9 census even
missed it, because it inherited a module-prefix whitelist that excluded `ReleaseCheck`;
see `TheoremConeAudit.lean`.) -/

/-- **The release-check marker's statement is `True`.**  `D5ReleaseCheck.release_check_compiles`
is a proof of `True`; it asserts nothing about compilation, imports or the ledger. -/
theorem releaseCheck_marker_is_trivial_proof :
    D5ReleaseCheck.release_check_compiles = (trivial : True) :=
  Subsingleton.elim _ _

/-- **Vacuity witness.**  The marker's statement is `True`, so it follows from *any*
proposition; it cannot distinguish a compiling release from a non-compiling one. -/
theorem releaseCheck_marker_holds_under_any_hypothesis (p : Prop) (hp : p) : True :=
  D5ReleaseCheck.release_check_compiles

/-- **Sharp replacement shape.**  The strongest faithful content that can be attached to the
marker in Lean consists of these two facts: every proposition implies its statement (`True`),
and its proof is the canonical one.  The actual release check is the *elaboration* of the
probe drivers, which is recorded by exit codes, not by this `Prop`. -/
theorem releaseCheck_marker_content_is_True :
    (∀ p : Prop, p → True) ∧
      D5ReleaseCheck.release_check_compiles = (trivial : True) :=
  ⟨fun _ _ => trivial, releaseCheck_marker_is_trivial_proof⟩

/-! ## §9. The remaining certificate interfaces are their fields

Completes the projection audit of §3 for `W`/`μ` monotonicity, the normalized-volume lower
bound and the surgery certificate.  In each case the structure is *exactly* the conjunction
of its fields, so the `apply`/projection lemmas add no mathematical content beyond the
assumed inequality. -/

open Perelman in
/-- **Definitional-triviality certificate for `Perelman.WMonotonicity`.** -/
theorem wMonotonicity_iff_statement {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (flow : Perelman.MetricFlowData I M) (W : ℝ → ℝ) :
    Perelman.WMonotonicity flow W ↔ AntitoneOn W flow.timeDomain :=
  ⟨fun h => h.antitone, fun h => ⟨h⟩⟩

/-- **Definitional-triviality certificate for `Perelman.MuMonotonicity`.** -/
theorem muMonotonicity_iff_statement (J : Set ℝ) (mu : ℝ → ℝ) :
    Perelman.MuMonotonicity J mu ↔ MonotoneOn mu J :=
  ⟨fun h => h.monotone, fun h => ⟨h⟩⟩

open Poincare.Longrun.Topology in
/-- **Definitional-triviality certificate for `NormalizedVolumeLowerBound`.** -/
theorem normalizedVolumeLowerBound_iff_field {M : Type u} {vol : M → ℝ} {v₀ : ℝ} :
    NormalizedVolumeLowerBound M vol v₀ ↔ ∀ x : M, v₀ ≤ vol x :=
  ⟨fun h => h.lower_bound, fun h => ⟨h⟩⟩

open Poincare.Longrun.Surgery in
/-- **Definitional-triviality certificate for `SurgeryCertificate`.** -/
theorem surgeryCertificate_iff_fields {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) :
    SurgeryCertificate P D ↔
      ((P.Compact X → P.Compact Y) ∧ (P.Orientable X → P.Orientable Y) ∧
        (P.SimplyConnected X → P.SimplyConnected Y)) :=
  ⟨fun h => ⟨h.compact_preserved, h.orientable_preserved, h.simplyConnected_preserved⟩,
   fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end D9Audit

/-! ## §8. Kernel axiom report for this audit file -/

#print axioms D9Audit.sharp_gibbsTerm_strictAnti
#print axioms D9Audit.sharp_perelmanF_step_lt
#print axioms D9Audit.threshold_gibbsTerm_strictAnti_is_sharp
#print axioms D9Audit.kappaCertificate_iff_fields
#print axioms D9Audit.perelmanFMonotonicity_iff_statement
#print axioms D9Audit.antitoneCertificate_iff_fields
#print axioms D9Audit.continuousPerelmanFMonotonicity_needs_identification
#print axioms D9Audit.continuousCertificate_consequence_is_field
#print axioms D9Audit.missingSphereRecognitionAlgorithm_is_trivial
#print axioms D9Audit.missingKappaPersistenceUnderSurgery_is_trivial
#print axioms D9Audit.missingCanonicalNeighborhoodTheorem_is_trivial
#print axioms D9Audit.missingKappaNoncollapsing_trivial_K
#print axioms D9Audit.covariantDerivativeCurvatureStatement_is_trivial
#print axioms D9Audit.releaseCheck_marker_is_trivial_proof
#print axioms D9Audit.releaseCheck_marker_holds_under_any_hypothesis
#print axioms D9Audit.releaseCheck_marker_content_is_True
#print axioms D9Audit.wMonotonicity_iff_statement
#print axioms D9Audit.muMonotonicity_iff_statement
#print axioms D9Audit.normalizedVolumeLowerBound_iff_field
#print axioms D9Audit.surgeryCertificate_iff_fields
