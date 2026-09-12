/-
# A3 lane — independent adversarial probe over the accepted D6 release sources

This file is written by the D13 cross-audit (lane A3) against a *fresh copy* of the
accepted `D6_weekly_release` sources (`a3d2d3/`, byte-copied from this worktree's
`release/`, rebuilt here with `lake build`, exit 0).  It does **not** import or
reuse any file of `VERIFIER-D7-adversarial-audit-d2d3`; every statement below is
re-derived from the accepted release definitions.

Purpose: the named blocker `A3` records that *"the adversarial audit only covers
the D4 evolution cluster; earlier clusters (D2/D3) have axiom audits but no
counterexample search."*  This probe performs the missing D2/D3 counterexample
search on the headline items and separates:

* defects that reproduce as **kernel-checked refutations/vacuity results**;
* claims of the earlier D2/D3 audit that are themselves **refuted** here.

All declarations are `#print axioms`-audited at the bottom; the expected cone is
`{propext, Classical.choice, Quot.sound}` only.
-/
import Poincare.Longrun.Entropy.Certificate
import Poincare.Longrun.Entropy.Bridge
import Poincare.Longrun.CurvatureODE.Bridge
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.ConnectionAdapter
import Poincare.Longrun.Surgery.Basic
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.Topology.MissingTheorems
import Poincare.Longrun.Topology.NormalizedVolume

open MeasureTheory Set
open scoped BigOperators

namespace A3D2D3

open Poincare.Longrun.Entropy
open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Geometry
open Poincare.Longrun.Surgery
open Poincare.Longrun.PDE
open Poincare.Longrun.Topology
open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.RiemannAdapter

universe u v w uE uH uM

/-! ## Finding A3-D2D3-1: `LinearDecayCertificate` is provably empty

The structure (`Poincare/Longrun/Entropy/Certificate.lean`, lines 261–270) carries
both a global lower bound `lowerBound ≤ F (E t)` for all `t ≥ 0` **and** a global
linear decay `F (E t) ≤ F (E 0) - rate * t` with `rate > 0`.  At large `t` the two
are incompatible in `ℝ`, so there is no certificate at all: the "finite lifetime"
consequence `time_le` is a theorem about an empty type. -/

theorem linearDecay_uninhabited {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) (c : LinearDecayCertificate E) : False := by
  set t : ℝ := max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hle : t ≤ ((E 0).F - c.cert.lowerBound) / c.rate := c.time_le ht0
  have hlt : ((E 0).F - c.cert.lowerBound) / c.rate < t := by
    rw [ht]
    exact lt_add_of_le_of_pos (le_max_left _ _) one_pos
  linarith

/-- No entropy datum admits a linear decay certificate. -/
theorem linearDecay_isEmpty {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) : IsEmpty (LinearDecayCertificate E) :=
  ⟨fun c => linearDecay_uninhabited E c⟩

/-- The two incompatible fields, exhibited without going through `time_le`:
`lower_le` and `decay` already contradict each other at `t = C + 1`. -/
theorem linearDecay_fields_contradict {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) (c : LinearDecayCertificate E) :
    ¬ (c.cert.lowerBound ≤ (E (max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1)).F ∧
       (E (max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1)).F ≤
         (E 0).F - c.rate * (max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1)) := by
  rintro ⟨h1, h2⟩
  have h3 : c.rate * (max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1) ≤
      (E 0).F - c.cert.lowerBound := by linarith
  have h4 : ((E 0).F - c.cert.lowerBound) / c.rate <
      max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1 :=
    lt_add_of_le_of_pos (le_max_left _ _) one_pos
  have h5 : (E 0).F - c.cert.lowerBound <
      c.rate * (max (((E 0).F - c.cert.lowerBound) / c.rate) 0 + 1) := by
    have := (div_lt_iff₀ c.rate_pos).mp h4
    linarith
  linarith

/-! ## Finding A3-D2D3-2: the "BLOCKED" curvature statement is a triviality

`CovariantDerivativeCurvatureStatement` (Geometry/LeviCivitaBlocked.lean, lines
230–238) existentially quantifies a pointwise `(1,3)` curvature tensor satisfying
first-pair antisymmetry and first Bianchi, and **ignores `cov` entirely** (the
parameter is literally `_cov`).  The zero tensor inhabits it unconditionally, so
the `BLOCKED` label in the module and in the D12 semantic ledger is wrong: the
statement captures none of the missing curvature API. -/

theorem covariantCurvatureStatement_trivial
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) :
    CovariantDerivativeCurvatureStatement I M cov := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro x X Y Z; simp
  · intro x X Y Z; simp

/-! ## Finding A3-D2D3-3: the tensor-Ricci-flow bridge is inhabited and degenerate

The D12 semantic ledger notes for `L-D2-ODE-SCALAR-MONO` state that
`scalarCurvature_monotone_of_bridge` is *"conditional on the uninhabited
TensorRicciFlowODEBridge"*.  Both halves are wrong:

* the bridge **is inhabited** (zero reaction field, constant metric, zero
  trajectory, zero curvature; witness `bridgeWitness` below), and
* **every** inhabitant has `traj ≡ 0` on `[0,T]` for `T > 0`, because
  `basis_fixed` + the orthonormality field pin the metric form and hence force
  the Ricci contraction to vanish.

So the transfer theorems are not "vacuous for lack of inhabitants"; they are
statements about a degenerate inhabited interface. -/

section Bridge

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The metric form is determined by the chosen basis: two metric data with the
same orthonormal basis have the same form.  (Both are expanded in the basis via
`MetricData.bilin_apply_eq_sum` and evaluated with `orthonormal`.) -/
theorem form_eq_of_basis_eq (m₁ m₂ : MetricData V ι) (h : m₁.basis = m₂.basis) :
    ∀ X Y : V, m₁.form X Y = m₂.form X Y := by
  have hrepr : m₁.basis.repr = m₂.basis.repr := congrArg Module.Basis.repr h
  intro X Y
  rw [MetricData.bilin_apply_eq_sum m₁ m₁.form X Y,
    MetricData.bilin_apply_eq_sum m₂ m₂.form X Y]
  simp only [MetricData.form_basis_apply]
  rw [hrepr]

/-- The zero curvature operator, reused from `CurvatureAlgebra` (this also documents
that the release already provides the trivial inhabitant of the operator interface). -/
abbrev zeroCurvature : CurvatureOperator ℝ V := CurvatureOperator.zero

@[simp] theorem zeroCurvature_apply (X Y Z : V) : zeroCurvature X Y Z = 0 := rfl

/-- The zero reaction field (both nonnegativity fields hold trivially). -/
def zeroReaction : ReactionField ι where
  a := 0
  g := fun _ _ => 0
  a_nonneg := by intro i; norm_num
  g_nonneg := by intro lam i; norm_num

@[simp] theorem zeroReaction_eval (lam : ι → ℝ) (i : ι) : zeroReaction.eval lam i = 0 := by
  simp [ReactionField.eval, zeroReaction]

/-- **The bridge is inhabited.**  For any manifold/covariant-derivative data, any
metric datum `m₀`, and `T`, the zero reaction field with constant metric, zero
curvature and zero trajectory inhabits the bridge. -/
noncomputable def bridgeWitness {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    (m₀ : MetricData V ι) (T : ℝ) :
    TensorRicciFlowODEBridge (V := V) I M cov (zeroReaction (ι := ι)) T
      (fun _ _ => 0) True where
  metric := fun _ => m₀
  curvature := fun _ => zeroCurvature
  basis_fixed := by intro t ht; rfl
  state_eq := by intro t ht i; simp [ricci_zero]
  realization := by
    refine ⟨covariantCurvatureStatement_trivial I M cov, ?_, ?_, trivial⟩
    · intro t ht X
      simpa [ricci_zero] using
        (hasDerivWithinAt_const (x := t) (c := m₀.form X X) (s := Icc 0 T))
    · refine ⟨?_, ?_⟩ <;> intro t ht X Y Z W <;> simp [curvatureForm]
  evolves := by
    intro i t ht
    simpa [zeroReaction_eval] using
      (hasDerivWithinAt_const (x := t) (c := (0 : ℝ)) (s := Ici t))
  continuous := by intro i; exact continuousOn_const

/-- **Every inhabitant of the bridge has zero diagonal Ricci curvature on `[0,T]`.**
`basis_fixed` makes the metric form constant on `[0,T]` (via
`form_eq_of_basis_eq` and the orthonormality field), so the diagonal metric
derivative vanishes; `MetricFamilySolvesRicciFlow` then forces
`ricci (curvature t) X X = 0` by uniqueness of the derivative within `Icc 0 T`. -/
theorem bridge_forces_zero_ricci {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) (X : V) :
    ricci (B.curvature t) X X = 0 := by
  have hconst : ∀ s ∈ Icc 0 T, (B.metric s).form X X = (B.metric 0).form X X :=
    fun s hs => form_eq_of_basis_eq _ _ (B.basis_fixed s hs) X X
  have hderiv : HasDerivWithinAt (fun s : ℝ => (B.metric s).form X X) 0 (Icc 0 T) t :=
    (hasDerivWithinAt_const (x := t) (c := (B.metric 0).form X X) (s := Icc 0 T)).congr
      (fun s hs => hconst s hs) (hconst t ht)
  have h2 := B.realization.2.1 t ht X
  have hU : UniqueDiffWithinAt ℝ (Icc 0 T) t := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have huniq : -2 * ricci (B.curvature t) X X = 0 :=
    UniqueDiffWithinAt.eq_deriv (Icc 0 T) hU h2 hderiv
  linarith

/-- **Every inhabitant of the bridge has zero trajectory on `[0,T]`.**  This makes
the transfer theorems `ricciDiagonal_nonneg_of_bridge` and
`scalarCurvature_monotone_of_bridge` degenerate: their conclusions hold only in
the zero configuration. -/
theorem bridge_forces_zero_traj {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) (i : ι) :
    traj t i = 0 := by
  rw [B.state_eq t ht i]
  exact bridge_forces_zero_ricci B hT ht ((B.metric t).basis i)

end Bridge

/-! ## Finding A3-D2D3-4: refutation of the earlier audit's entropy sign finding

`VERIFIER-D7-adversarial-audit-d2d3`, finding F2, asserts that
`FDerivativeStatement` has the *wrong sign* because "Perelman's F satisfies
`dF/dt = -2 ∫ |Ric + Hess f|² e^{-f} ≤ 0`".  That is not the standard
convention.  Perelman's original paper, §1.2 equation (1.4), states

  `F_t = 2 ∫ |R_ij + ∇_i∇_j f|² e^{-f} dV`

for the coupled system `(g_ij)_t = -2 R_ij`, `f_t = -Δf + |∇f|² - R`; F is
nondecreasing (Perelman, *The entropy formula for the Ricci flow and its
geometric applications*, arXiv:math/0211159, §1.2; see also λ(g) nondecreasing
in §2.2).  The release's `FDerivativeStatement` is exactly this identity, so F2
is a **false positive** of the earlier audit and the bridge's reduction to
`ContinuousMonotoneCertificate` is convention-correct.  The opposite sign does
occur in the D4 *finite model* (`Poincare.Longrun.Evolution.perelmanF_antitone`),
whose own ledger note already flags it as "sign convention opposite to
Perelman's F" — the earlier audit conflated the two clusters.

Similarly, `ConjugateMeasureEvolutionStatement` (Entropy/Bridge.lean, lines
86–91) is labelled "the conjugate heat equation" but states `∂_t ρ = -Δρ`, the
plain heat equation, with no scalar-curvature term.  The conjugate heat equation
for `ρ = (4πτ)^{-n/2} e^{-f}` is `∂_t ρ = -Δρ + R ρ`
(equivalently `(-∂_t - Δ + R) ρ = 0`), so as named this interface is insensitive
to `R`: a convention/labelling defect (not a false theorem, since the statement
is an explicit hypothesis field). -/

/-! ## Finding A3-D2D3-5: "MISSING THEOREM" statements that are trivial or false

Three statement-only items of `Poincare.Longrun.Topology.MissingTheorems` and the
surgery interface are defective as *statements* (independent of any proof
obligation):

* `missingSphereRecognitionAlgorithm` is documented as the missing
  Rubinstein–Thompson decision procedure, but as formalized it is
  `∀ M, Nonempty (Decidable (M ≃ₜ 𝕊³))`, which is immediate from classical
  decidability of every proposition.  It therefore asserts nothing about an
  algorithm and is not a "missing theorem".
* `SurgeryCertificate P D` has three fields that only relate the ledger
  predicates across `X` and `Y`; neither the relation `D.rel` nor the neck/cap
  predicates occur.  Hence a certificate exists for a datum whose relation is
  identically `False` (no surgery at all) as soon as `X = Y`.
* `missingConjugateHeatKernel` and `missingKappaNoncollapsing` are stated for an
  arbitrary measure with no positivity/nondegeneracy hypothesis; they are
  **false for the zero measure** (the unit-mass condition `∫ u = 1` and the
  positive lower bound `κ r³ ≤ μ(B)` cannot both hold).  These are refutable
  interface statements, not merely unproved ones. -/

theorem missingSphereRecognitionAlgorithm_trivial : missingSphereRecognitionAlgorithm :=
  fun _M _ _ _ _ => ⟨Classical.propDecidable _⟩

/-- A surgery datum from `X` to `X` with empty relation, empty neck and empty cap
predicates: no cut and no gluing is described. -/
def emptyRelationDatum (X : TopSpace.{u}) : SurgeryDatum X X where
  neck := X
  rel := fun _ _ => False
  liesOnNeck := fun _ => False
  liesOnCap := fun _ => False

/-- **A certificate exists for the empty-relation datum.**  The certificate fields
do not mention the datum, so "surgery" certificates are blind to whether any
surgery is described. -/
theorem surgeryCertificate_emptyRelation (P : LedgerPredicates.{u}) (X : TopSpace.{u}) :
    SurgeryCertificate P (emptyRelationDatum X) where
  compact_preserved := id
  orientable_preserved := id
  simplyConnected_preserved := id

/-- The conjugate-heat-kernel "missing theorem" is false for the zero measure. -/
theorem not_missingConjugateHeatKernel_zero :
    ¬ missingConjugateHeatKernel (M := ℝ) (0 : Measure ℝ) True := by
  intro h
  obtain ⟨u, _meas, hint⟩ := h trivial
  have h1 := hint 1 one_pos
  simp at h1

/-- The κ-non-collapsing "missing theorem" is false for the zero measure on `ℝ`. -/
theorem not_missingKappaNoncollapsing_zero :
    ¬ missingKappaNoncollapsing (M := ℝ) (0 : Measure ℝ) (fun _ _ => True) True := by
  intro h
  obtain ⟨κ, r₀, hcert⟩ := h trivial
  have hr : 0 < min r₀ 1 := lt_min hcert.r0_pos one_pos
  have hr₀ : min r₀ 1 ≤ r₀ := min_le_left _ _
  have hle := hcert.volume_ball_lower 0 (min r₀ 1) hr hr₀ trivial
  have hpos : 0 < ENNReal.ofReal (κ * (min r₀ 1) ^ (3 : ℕ)) := by
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos hcert.kappa_pos (pow_pos hr 3)
  have hzero : (0 : Measure ℝ) (Metric.eball 0 (ENNReal.ofReal (min r₀ 1))) = 0 := by simp
  rw [hzero] at hle
  exact (not_le_of_gt hpos) hle

/-- **`NeckAnalysis` is trivially inhabited.**  Its five `Prop` fields can all be
`False`, which makes every implication field vacuous; the "missing input" of the
surgery cluster therefore imposes no obligation as a structure.  (The D12 ledger
note `L-D3-SURGERY-INTERFACE` calls it "statement-only"; the sharper statement is
that it is inhabited with empty content.) -/
theorem neckAnalysis_inhabited (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) : Nonempty (NeckAnalysis P D) :=
  ⟨{ highCurvatureRegion := False
     deltaNeckExists := False
     neckSeparating := False
     surgeryAdmissible := False
     realizesDatum := False
     neck_of_highCurvature := fun h => h
     separating_of_neck := fun h => h
     admissible_of_separating := fun h => h
     realizes_of_admissible := fun h => h
     target_preserved := fun h => h.elim }⟩

/-! ## Finding A3-D2D3-6: extinction conclusions are free fields; `hM` is redundant

* `ExtinctionTheorem` is a structure of four `Prop` fields related only to each
  other.  Setting all four to `True` with trivial implications inhabits it, so
  "finite-time extinction" and "the terminal manifold is `𝕊³`" are *free fields*,
  not obligations.  Consequently `MissingInputs` can carry a trivial neck analysis
  together with a trivial extinction theorem whose conclusions are `True` by
  definition.
* In the discrete maximum principle `HeatGridEvolution.le_of_initial_le`, the
  hypothesis `hM : 0 ≤ M` is **redundant**: the left Dirichlet boundary
  `u 0 0 = 0` together with the initial bound `hinit` already gives `0 ≤ M`.  The
  sharp restatement below removes it.  (The `hM` of `zeroExtend_le` and
  `succ_le` is *not* redundant: those statements have no initial-boundary data.) -/

/-- `ExtinctionTheorem` with all four conclusions set to `True`. -/
def extinctionTheorem_true (P : LedgerPredicates.{u}) : ExtinctionTheorem P where
  complexityDecreases := True
  finitelyManySurgeries := True
  extincts := True
  terminalSphere := True
  finitelyMany_of_decrease := fun _ => trivial
  extincts_of_finite := fun _ => trivial
  terminalSphere_of_extincts := fun _ => trivial

/-- `MissingInputs` whose extinction half has all conclusions true by definition
(pairing the all-`False` neck analysis with `extinctionTheorem_true`). -/
theorem missingInputs_with_true_extinction (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) :
    ∃ M : MissingInputs P D, M.extinction.extincts ∧ M.extinction.terminalSphere :=
  ⟨{ neck := (neckAnalysis_inhabited P D).some
     extinction := extinctionTheorem_true P }, trivial, trivial⟩

/-- **Sharp discrete maximum principle without the redundant `0 ≤ M`.** -/
theorem heatGrid_le_of_initial_le_no_hM {N : ℕ} {α M : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hinit : ∀ i ≤ N + 1, ev.u 0 i ≤ M) :
    ∀ t i, i ≤ N + 1 → ev.u t i ≤ M := by
  have hM : 0 ≤ M := by
    have h := hinit 0 (Nat.zero_le _)
    rwa [ev.boundary_left 0] at h
  exact ev.le_of_initial_le hα0 hα1 hM hinit


/-! ## Finding A3-D2D3-7: redundant positivity hypotheses in the κ equivalence

`kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` takes
`hκ : 0 < κ` and `hr₀ : 0 < r₀` as hypotheses, but **both are fields of either
side** of the equivalence, so they are redundant.  The sharp restatement below
removes them and derives the positivity from whichever side is assumed. -/

theorem kappa_iff_normalized_no_hyp
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ} :
    KappaNoncollapsingCertificate M μ K κ r₀ ↔
      NormalizedBallVolumeLowerBound M μ K κ r₀ := by
  constructor
  · intro h
    refine ⟨h.kappa_pos, h.r0_pos, fun x r hr hr₀ hK => ?_⟩
    exact ((kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound
      h.kappa_pos h.r0_pos).mp h).normalized_lower x r hr hr₀ hK
  · intro h
    exact (kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound
      h.kappa_pos h.r0_pos).mpr h

/-! ## Axiom audit -/

#print axioms linearDecay_uninhabited
#print axioms linearDecay_isEmpty
#print axioms linearDecay_fields_contradict
#print axioms covariantCurvatureStatement_trivial
#print axioms form_eq_of_basis_eq
#print axioms bridgeWitness
#print axioms bridge_forces_zero_ricci
#print axioms bridge_forces_zero_traj
#print axioms missingSphereRecognitionAlgorithm_trivial
#print axioms surgeryCertificate_emptyRelation
#print axioms not_missingConjugateHeatKernel_zero
#print axioms not_missingKappaNoncollapsing_zero
#print axioms extinctionTheorem_true
#print axioms neckAnalysis_inhabited
#print axioms missingInputs_with_true_extinction
#print axioms heatGrid_le_of_initial_le_no_hM
#print axioms kappa_iff_normalized_no_hyp

end A3D2D3
