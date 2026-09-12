/-
D9-adversarial-audit-release — independent adversarial findings (auditor-written).

This file is *not* part of the D6 release.  It records, as compiled `Prop`s, the
assumption-inflation / vacuity / definitional-triviality findings of the independent D9
audit of the D6 weekly release, plus sharp-hypothesis restatements and hypothesis-necessity
counterexamples.  Every declaration here is proved from the release interfaces and
mathlib alone; no `sorry`, `axiom`, `unsafe`, `native_decide` or `admit` is used.

Sections:

* §1  Release-wide vacuity: the `ReleaseCheck` marker is literally `True`, the
      `missing...` placeholders in `Topology.MissingTheorems` are provable as stated,
      and the `BLOCKED` manifold-curvature contract is trivially inhabited.
* §2  Definitional triviality of interface projections: the non-audit theorems at the
      top of the import-cone ranking are auto-generated structure-field projections;
      `PerelmanApproximation`, `PerelmanEvolutionBoundary`, `ExtinctionTheorem` and
      `NeckAnalysis` are exactly their field conjunctions.
* §3  Hypothesis sharpness: the Gibbs threshold `1 ≤ c` is exactly sharp; the
      `identification` hypothesis of the continuous transfer cannot be dropped; the
      monotonicity hypothesis of the finite-to-limit passage cannot be dropped.
-/
import ReleaseCheck

open MeasureTheory Set
open scoped BigOperators Topology ENNReal Manifold ContDiff Bundle

namespace D9Indep

universe u v w uE uH uM

/-! ## §1. Release-wide vacuity and triviality certificates -/

open Poincare.Longrun.Topology in
/-- **The `ReleaseCheck` marker is `True`.**  The only declaration of the module that
imports every other release module asserts nothing: it is a proof of `True`, so it is
implied by every proposition and cannot distinguish a compiling release from a
non-compiling one.  The actual release check is the elaboration recorded by exit codes. -/
theorem releaseCheck_marker_is_True :
    D5ReleaseCheck.release_check_compiles = (trivial : True) :=
  Subsingleton.elim _ _

open Poincare.Longrun.Topology in
/-- **`missingSphereRecognitionAlgorithm` holds as stated.**  It is
`∀ M, Nonempty (Decidable (Nonempty (M ≃ₜ 𝕊³)))`, and classical decidability inhabits every
`Decidable` proposition, so the statement is not a decision procedure. -/
theorem missingSphereRecognitionAlgorithm_trivial :
    missingSphereRecognitionAlgorithm :=
  fun _ _ _ _ _ => ⟨Classical.propDecidable _⟩

open Poincare.Longrun.Topology in
/-- **`missingKappaPersistenceUnderSurgery` holds as stated.**  The existential is
discharged by the hypothesis certificate itself (`κ' = κ`, `r₀' = r₀`); no surgery occurs
in the statement and the `SurgeryHypotheses` binder is inert here. -/
theorem missingKappaPersistenceUnderSurgery_trivial {M : Type u} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) (K : CurvatureBoundedOn M) (S : Prop) (κ r₀ : ℝ) :
    missingKappaPersistenceUnderSurgery μ K S κ r₀ :=
  fun _ hcert => ⟨κ, r₀, hcert⟩

open Poincare.Longrun.Topology in
/-- **`missingCanonicalNeighborhoodTheorem` is a satisfiable schema.**  Instantiating the
caller-supplied canonical-neighbourhood predicate at `True` makes the statement hold for
every high-curvature predicate: no ε-closeness, neck or model-geometry content remains. -/
theorem missingCanonicalNeighborhoodTheorem_trivial (M : Type u) (H : M → Prop) :
    missingCanonicalNeighborhoodTheorem M (fun _ => True) H :=
  fun _ _ => trivial

open Poincare.Longrun.Topology in
/-- **`missingKappaNoncollapsing` is vacuous for a degenerate curvature predicate.**  With
`K := fun _ _ => False` the curvature hypothesis is never met, so a certificate exists for
every measure and the statement is `True`-valued. -/
theorem missingKappaNoncollapsing_vacuous {M : Type u} [PseudoEMetricSpace M]
    [MeasurableSpace M] (μ : Measure M) :
    missingKappaNoncollapsing μ (fun _ _ => False) True :=
  fun _ => ⟨1, 1, one_pos, one_pos, fun _x _r _hr _hr₀ hK => hK.elim⟩

open Bundle in
/-- **The `BLOCKED` manifold-curvature contract is trivially inhabited.**  The connection
argument is unused and the existential is discharged by the zero pointwise tensor; both
antisymmetry and Bianchi hold definitionally.  The statement therefore does not relate the
curvature tensor to `cov` and is not a faithful contract for the missing API. -/
theorem covariantDerivativeCurvatureStatement_trivial
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u)) :
    Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement I M cov :=
  ⟨0, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

/-! ## §2. Interface projections are exactly their field conjunctions -/

open Filter Poincare.Longrun.Evolution Poincare.Longrun.Entropy Poincare.Longrun.CurvatureODE in
/-- **Definitional-triviality certificate for `PerelmanApproximation`.**  The structure is
exactly the conjunction of its three fields; the theorems `PerelmanApproximation.hc`,
`.evolves`, `.identification` are Lean-generated field projections, so they add no
mathematical content beyond the hypotheses. -/
theorem perelmanApproximation_iff_fields {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {ι : Type w} [Fintype ι] (E : ℝ → EntropyData X μ) (F : ReactionField ι)
    (T : ℝ) (traj : ℝ → ι → ℝ) (c : ι → ℝ) :
    Nonempty (PerelmanApproximation E F T traj c) ↔
      (∀ i, 1 ≤ c i) ∧ EvolutionRelation F T traj ∧
        FiniteRepresentsContinuousPerelman E c traj T := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.hc, h.evolves, h.identification⟩
  · rintro ⟨hc, hev, hid⟩
    exact ⟨{ hc := hc, evolves := hev, identification := hid }⟩

open Filter Poincare.Longrun.Evolution Poincare.Longrun.Entropy Poincare.Longrun.CurvatureODE
  Poincare.Longrun.Geometry Poincare.CurvatureAlgebra in
/-- **Definitional-triviality certificate for `PerelmanEvolutionBoundary`.**  The
`statement-only` boundary bundle is exactly the conjunction of its five fields; in
particular the non-audit theorems `PerelmanEvolutionBoundary.hc`, `.evolves`,
`.identification`, `.tensor_realization`, `.entropy_bridge` at the top of the import-cone
ranking are generated field projections, not proved mathematics. -/
theorem perelmanEvolutionBoundary_iff_fields
    {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {E' : Type uE} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E' (TangentSpace I : M → Type uE))
    (C : WeightedCalculus X) (E : ℝ → EntropyData X μ) (F : ReactionField ι)
    (T : ℝ) (traj : ℝ → ι → ℝ) (c : ι → ℝ)
    (metric : ℝ → MetricData V ι) (curvature : ℝ → CurvatureOperator ℝ V)
    (DiffusionVanishes : Prop) :
    Nonempty (PerelmanEvolutionBoundary I M cov C E F T traj c metric curvature
        DiffusionVanishes) ↔
      FiniteRepresentsContinuousPerelman E c traj T ∧ EvolutionRelation F T traj ∧
        (∀ i, 1 ≤ c i) ∧
        Poincare.Longrun.CurvatureODE.TensorRicciFlowODERealization I M cov metric
          curvature T DiffusionVanishes ∧
        EntropyRegularityBridge C E := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.identification, h.evolves, h.hc, h.tensor_realization, h.entropy_bridge⟩
  · rintro ⟨hid, hev, hc, htr, hbr⟩
    exact ⟨{ identification := hid, evolves := hev, hc := hc,
             tensor_realization := htr, entropy_bridge := hbr }⟩

open Poincare.Longrun.Surgery in
/-- **Definitional-triviality certificate for `ExtinctionTheorem`.**  The structure that
carries the name "extinction theorem" is exactly a chain of three implications between
*freely chosen* `Prop`s; it is inhabited for every such chain, so it carries no geometric
content.  The projections `extincts_of_finite`, `terminalSphere_of_extincts`, etc. are field
extractions. -/
theorem extinctionTheorem_iff_prop_chain (P : LedgerPredicates.{u}) :
    Nonempty (ExtinctionTheorem P) ↔
      ∃ a b c d : Prop, (a → b) ∧ (b → c) ∧ (c → d) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.complexityDecreases, E.finitelyManySurgeries, E.extincts, E.terminalSphere,
      E.finitelyMany_of_decrease, E.extincts_of_finite, E.terminalSphere_of_extincts⟩
  · rintro ⟨a, b, c, d, hab, hbc, hcd⟩
    exact ⟨{ complexityDecreases := a, finitelyManySurgeries := b, extincts := c,
             terminalSphere := d, finitelyMany_of_decrease := hab,
             extincts_of_finite := hbc, terminalSphere_of_extincts := hcd }⟩

open Poincare.Longrun.Surgery in
/-- **Definitional-triviality certificate for `NeckAnalysis`.**  The "geometric neck
analysis" input is a chain of four implications plus the target-invariant obligation, over
freely chosen `Prop`s; it is inhabited for every choice, so it is a bookkeeping device and
not a geometric hypothesis with content. -/
theorem neckAnalysis_iff_prop_chain (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) :
    Nonempty (NeckAnalysis P D) ↔
      ∃ a b c d e : Prop, (a → b) ∧ (b → c) ∧ (c → d) ∧ (d → e) ∧
        (e → (P.SimplyConnected X → P.SimplyConnected Y)) := by
  constructor
  · rintro ⟨N⟩
    exact ⟨N.highCurvatureRegion, N.deltaNeckExists, N.neckSeparating, N.surgeryAdmissible,
      N.realizesDatum, N.neck_of_highCurvature, N.separating_of_neck,
      N.admissible_of_separating, N.realizes_of_admissible, N.target_preserved⟩
  · rintro ⟨a, b, c, d, e, hab, hbc, hcd, hde, hep⟩
    exact ⟨{ highCurvatureRegion := a, deltaNeckExists := b, neckSeparating := c,
             surgeryAdmissible := d, realizesDatum := e, neck_of_highCurvature := hab,
             separating_of_neck := hbc, admissible_of_separating := hcd,
             realizes_of_admissible := hde, target_preserved := hep }⟩

/-! ## §3. Sharp restatements and hypothesis necessity -/

open Poincare.Longrun.Evolution in
/-- **The Gibbs threshold `1 ≤ c` is exactly sharp.**  The promoted theorems
`gibbsTerm_strictAnti`, `gibbsTerm_step_lt` and `perelmanF_step_lt` assume the overstrong
`1 < c`; `1 ≤ c` suffices (`D4Audit.gibbsTerm_strictAnti_of_one_le`) and cannot be lowered,
because `gibbsTerm (1/2)` strictly increases between `1` and `2`. -/
theorem gibbs_threshold_exactly_one :
    (∀ c : ℝ, 1 ≤ c → StrictAnti (gibbsTerm c)) ∧
      ¬ (∀ c : ℝ, StrictAnti (gibbsTerm c)) := by
  constructor
  · intro c hc
    exact D4Audit.gibbsTerm_strictAnti_of_one_le c hc
  · intro H
    have hlt : gibbsTerm (1 / 2) 1 < gibbsTerm (1 / 2) 2 :=
      D4Audit.gibbsTerm_half_one_lt_two
    have hgt : gibbsTerm (1 / 2) 2 < gibbsTerm (1 / 2) 1 :=
      H (1 / 2) (by norm_num : (1 : ℝ) < 2)
    exact absurd hgt (not_lt.mpr (le_of_lt hlt))

open Filter Poincare.Longrun.Entropy Poincare.Longrun.Evolution in
/-- **The `identification` hypothesis of the continuous transfer cannot be dropped.**
Continuous Perelman `F`-monotonicity is *false* for an arbitrary entropy family: the finite
counting-measure family with curvature data `c t = t` and zero potential has `F = t`.  Hence
`continuousPerelmanFMonotone_of_approximation` is a genuine conditional transfer. -/
theorem continuous_monotonicity_needs_identification :
    ¬ (∀ (E : ℝ → EntropyData (Fin 1) (Measure.count : Measure (Fin 1))) (T : ℝ),
        ContinuousPerelmanFMonotonicity E T) := by
  intro H
  have h := H (fun t : ℝ =>
    finiteReactionEntropyData (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ))) 1
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hle := h 1 h1
  have e1 : (finiteReactionEntropyData (fun _ : Fin 1 => (1 : ℝ))
      (fun _ : Fin 1 => (0 : ℝ))).F = 1 := by
    rw [finiteReactionEntropyData_F]
    simp [perelmanF, gibbsTerm]
  have e0 : (finiteReactionEntropyData (fun _ : Fin 1 => (0 : ℝ))
      (fun _ : Fin 1 => (0 : ℝ))).F = 0 := by
    rw [finiteReactionEntropyData_F]
    simp [perelmanF, gibbsTerm]
  rw [e1, e0] at hle
  norm_num at hle

open Filter Poincare.Longrun.Evolution in
/-- **The monotonicity hypothesis of the finite-to-limit passage cannot be dropped.**
If only `Tendsto state atTop (𝓝 limit)` is assumed, the conclusion of
`perelmanF_limit_le_of_discrete` fails: the eventually-constant sequence `1, 2, 2, …` for
`c = 0` converges to `2`, and `perelmanF 0 (· ↦ 2) = 4e^{-2} > e^{-1} =
perelmanF 0 (· ↦ 1)`. -/
theorem limit_passage_needs_monotonicity :
    ¬ (∀ (state : ℕ → Fin 1 → ℝ) (limit : Fin 1 → ℝ),
        Tendsto state atTop (𝓝 limit) →
          perelmanF (fun _ : Fin 1 => (0 : ℝ)) limit ≤
            perelmanF (fun _ : Fin 1 => (0 : ℝ)) (state 0)) := by
  intro H
  let state : ℕ → Fin 1 → ℝ := fun n _ => if n = 0 then 1 else 2
  let limit : Fin 1 → ℝ := fun _ => 2
  have hlim : Tendsto state atTop (𝓝 limit) := by
    apply tendsto_pi_nhds.mpr
    intro i
    rw [show (fun n : ℕ => state n i) = fun n : ℕ => if n = 0 then (1 : ℝ) else 2 from rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [limit, show n ≠ 0 from by omega]
  have hbad := H state limit hlim
  have h2 : perelmanF (fun _ : Fin 1 => (0 : ℝ)) limit = 4 * Real.exp (-2) := by
    simp only [limit, perelmanF, gibbsTerm, Fin.sum_univ_one]
    norm_num
  have h1 : perelmanF (fun _ : Fin 1 => (0 : ℝ)) (state 0) = Real.exp (-1) := by
    simp only [state, perelmanF, gibbsTerm, Fin.sum_univ_one]
    norm_num
  rw [h2, h1] at hbad
  have hcontr : Real.exp (-1) < 4 * Real.exp (-2) :=
    Poincare.Longrun.Evolution.exp_neg_one_lt_four_exp_neg_two
  linarith

end D9Indep

/-! ## Kernel axiom report for the audit certificates (gate 4/5 evidence) -/

#print axioms D9Indep.releaseCheck_marker_is_True
#print axioms D9Indep.missingSphereRecognitionAlgorithm_trivial
#print axioms D9Indep.missingKappaPersistenceUnderSurgery_trivial
#print axioms D9Indep.missingCanonicalNeighborhoodTheorem_trivial
#print axioms D9Indep.missingKappaNoncollapsing_vacuous
#print axioms D9Indep.covariantDerivativeCurvatureStatement_trivial
#print axioms D9Indep.perelmanApproximation_iff_fields
#print axioms D9Indep.perelmanEvolutionBoundary_iff_fields
#print axioms D9Indep.extinctionTheorem_iff_prop_chain
#print axioms D9Indep.neckAnalysis_iff_prop_chain
#print axioms D9Indep.gibbs_threshold_exactly_one
#print axioms D9Indep.continuous_monotonicity_needs_identification
#print axioms D9Indep.limit_passage_needs_monotonicity
