/-
Task `D9-sobolev-parabolic-estimates`: **statement-only** Props for the analytic
inputs that close the Ricci-flow PDE argument.

This file is part of the long-run Poincaré formalization.  It follows the honesty
boundary of `Poincare.Longrun.PDE.ContinuousInterface` and
`Poincare.Longrun.Entropy.Bridge`: the pinned mathlib has no Riemannian volume
form, no Laplacian on manifolds, no Sobolev spaces and no parabolic regularity
theory, so the corresponding theorems cannot be proved here.  They are recorded as
`def ... : Prop` with every hypothesis explicit.  No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` is used.

## Contents

1. `ParabolicData M` — the closed-manifold parabolic datum: a measure `μ` (the
   Riemannian volume), a field `u`, a forcing `f`, an energy `E(t) = ∫ |u(t)|² dμ`,
   a Dirichlet form `(u, v) ↦ ∫ ⟨∇u, ∇v⟩ dμ`, the weak equation `∂ₜu = Δu + f`
   and the energy identity.  The construction of this datum from a Riemannian
   manifold is exactly what mathlib is missing.
2. `ParabolicL2AprioriEstimate` — the closed-manifold `L²` a-priori estimate
   `E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ ∫ |f|² dμ)` for `C ≥ 1`.
3. `ParabolicEnergyDissipationEstimate` — the integrated energy identity
   `E(T) + 2 ∫₀ᵀ |∇u|² ≤ E(0) + ∫₀ᵀ ∫ |f|² dμ`.
4. `ParabolicSmoothingEstimate` / `ParabolicL2ToHkSmoothing` — higher-regularity
   smoothing estimates with the sharp `t^{-k/2}` rate.
5. `SobolevScale M` and the Sobolev embedding statements needed for Ricci flow:
   `H¹ ↪ L⁶`, `H² ↪ C⁰`, the higher-order `H^k ↪ C⁰`, Rellich–Kondrachov
   compactness, the Gagliardo–Nirenberg interpolation inequality and the Poincaré
   inequality.
6. `ClosedManifold...` wrappers carrying the closed-manifold typeclass context
   (`CompactSpace`, `T2Space`, `I.Boundaryless`), plus checked shape lemmas.
7. Checked non-vacuity witnesses: the zero scale, the one-point scale, and a
   genuine instance of the `L²` a-priori estimate in the finite-dimensional matrix
   model of `Poincare.D9.ParabolicEstimates.MatrixModel`.
-/
import Poincare.D9.ParabolicEstimates.MatrixModel

open MeasureTheory Set intervalIntegral
open scoped Manifold ContDiff Topology ENNReal

namespace Poincare.D9.ParabolicEstimates

universe u

/-! ## 1. Closed-manifold parabolic datum -/

/-- **Parabolic datum on a manifold with measure.**

The measure `μ` is the Riemannian volume of the release's manifold-with-measure
layer; the Dirichlet form `dirichlet u v` is the abstract stand-in for
`∫ ⟨∇u, ∇v⟩ dμ` (mathlib has no gradient on manifolds).  The fields `weak_equation`
and `energy_identity` are the PDE content: the weak formulation of
`∂ₜu = Δu + f` against the test class `testClass`, and the energy identity
`(d/dt) E = -2 |∇u|² + 2 ⟨u, f⟩`.

This is a data structure, not a proof: constructing it from an actual Riemannian
manifold is precisely the missing analytic content. -/
structure ParabolicData (M : Type u) [MeasurableSpace M] where
  /-- The volume measure. -/
  μ : Measure M
  /-- The field. -/
  u : ℝ → M → ℝ
  /-- The forcing term. -/
  f : ℝ → M → ℝ
  /-- The energy `E(t) = ∫ |u(t)|² dμ`. -/
  E : ℝ → ℝ
  /-- The Dirichlet form `∫ ⟨∇u, ∇v⟩ dμ`. -/
  dirichlet : (M → ℝ) → (M → ℝ) → ℝ
  /-- The defining identity of the energy. -/
  energy_eq : ∀ t : ℝ, E t = ∫ x, (u t x) ^ 2 ∂μ
  /-- Symmetry of the Dirichlet form. -/
  dirichlet_symm : ∀ w v : M → ℝ, dirichlet w v = dirichlet v w
  /-- Nonnegativity of the Dirichlet form on the diagonal. -/
  dirichlet_nonneg : ∀ w : M → ℝ, 0 ≤ dirichlet w w
  /-- The admissible test functions. -/
  testClass : Set (M → ℝ)
  /-- Every time slice is admissible. -/
  u_mem_testClass : ∀ t : ℝ, u t ∈ testClass
  /-- The weak formulation of `∂ₜu = Δu + f`. -/
  weak_equation : ∀ (t : ℝ) (φ : M → ℝ), φ ∈ testClass →
    HasDerivAt (fun s : ℝ => ∫ x, u s x * φ x ∂μ)
      (-(dirichlet (u t) φ) + ∫ x, f t x * φ x ∂μ) t
  /-- The energy identity `(d/dt) E = -2 |∇u|² + 2 ⟨u, f⟩`. -/
  energy_identity : ∀ t : ℝ, HasDerivAt E
    (-2 * dirichlet (u t) (u t) + 2 * ∫ x, u t x * f t x ∂μ) t

/-- **The energy identity as a named `Prop`.** -/
def ManifoldEnergyIdentity {M : Type u} [MeasurableSpace M] (D : ParabolicData M) : Prop :=
  ∀ t : ℝ, HasDerivAt D.E
    (-2 * D.dirichlet (D.u t) (D.u t) + 2 * ∫ x, D.u t x * D.f t x ∂D.μ) t

/-- The energy identity is part of the parabolic datum. -/
theorem manifoldEnergyIdentity_of_data {M : Type u} [MeasurableSpace M]
    (D : ParabolicData M) : ManifoldEnergyIdentity D :=
  D.energy_identity

/-! ## 2. The parabolic `L²` a-priori estimate -/

/-- **Statement only.**  The parabolic `L²` a-priori estimate on a manifold with
measure: for a classical solution of `∂ₜu = Δu + f` with energy `E` and Dirichlet
form `|∇u|²`,

`E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ ∫ |f(s)|² dμ ds)` for every `t ∈ [0, T]`,

whenever `C ≥ 1` and `T ≥ 0`.  This is the Grönwall form of the estimate; the
finite-dimensional instance is proved in
`parabolicL2AprioriEstimate_matrix`. -/
def ParabolicL2AprioriEstimate {M : Type u} [MeasurableSpace M] (D : ParabolicData M)
    (T C : ℝ) : Prop :=
  1 ≤ C → 0 ≤ T → ∀ t ∈ Icc 0 T,
    D.E t ≤ Real.exp (C * t) * (D.E 0 + ∫ s in 0..t, ∫ x, (D.f s x) ^ 2 ∂D.μ)

/-- **Statement only.**  The integrated form of the energy identity: for a
solution of `∂ₜu = Δu + f` on `[0, T]`,

`E(T) + 2 ∫₀ᵀ |∇u|² ≤ E(0) + ∫₀ᵀ ∫ |f|² dμ`.

This is the estimate obtained by integrating `E' = -2|∇u|² + 2⟨u,f⟩` and using
Young's inequality; it is the form used to control the Dirichlet energy. -/
def ParabolicEnergyDissipationEstimate {M : Type u} [MeasurableSpace M]
    (D : ParabolicData M) (T : ℝ) : Prop :=
  0 ≤ T →
    D.E T + 2 * ∫ s in 0..T, D.dirichlet (D.u s) (D.u s)
      ≤ D.E 0 + ∫ s in 0..T, ∫ x, (D.f s x) ^ 2 ∂D.μ

/-- **Checked shape lemma.**  The `L²` a-priori estimate unfolds to its integral
form. -/
theorem parabolicL2AprioriEstimate_iff {M : Type u} [MeasurableSpace M]
    (D : ParabolicData M) (T C : ℝ) :
    ParabolicL2AprioriEstimate D T C ↔
      (1 ≤ C → 0 ≤ T → ∀ t ∈ Icc 0 T,
        D.E t ≤ Real.exp (C * t) * (D.E 0 + ∫ s in 0..t, ∫ x, (D.f s x) ^ 2 ∂D.μ)) :=
  Iff.rfl

/-! ## 3. Higher-regularity smoothing estimates -/

/-- **Sobolev scale data on a manifold.**  `sobolevNorm s p u` is the `H^{s,p}`
norm, `supNorm` the sup norm and `mean` the average.  The scale is data: mathlib
has no Sobolev spaces on manifolds. -/
structure SobolevScale (M : Type u) where
  /-- The `H^{s,p}` norm. -/
  sobolevNorm : ℝ → ℝ → (M → ℝ) → ℝ
  /-- The sup norm. -/
  supNorm : (M → ℝ) → ℝ
  /-- The mean value. -/
  mean : (M → ℝ) → ℝ

/-- **Statement only.**  The parabolic smoothing estimate for
`∂ₜu = Δu + f` on a manifold with measure: for `t > 0` and `k ≥ 0`,

`‖u(t)‖_{H^k} ≤ C t^{-k/2} ‖u(0)‖_{L²}
  + C ∫₀ᵗ (t-s)^{-k/2} ‖f(s)‖_{L²} ds`.

The `t^{-k/2}` rate is the sharp smoothing rate of the heat semigroup; the
Duhamel integral is the contribution of the forcing.  This is the higher-regularity
estimate needed to bootstrap `L²` energy bounds to pointwise curvature bounds. -/
noncomputable def ParabolicSmoothingEstimate {M : Type u}
    (S : SobolevScale M) (u f : ℝ → M → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  0 < C → ∀ t : ℝ, 0 < t →
    S.sobolevNorm (k : ℝ) 2 (u t) ≤
      C * t ^ (-(k : ℝ) / 2) * S.sobolevNorm 0 2 (u 0)
        + C * ∫ s in 0..t, (t - s) ^ (-(k : ℝ) / 2) * S.sobolevNorm 0 2 (f s)

/-- **Statement only.**  The homogeneous `L² → H^k` smoothing estimate: the
forcing-free special case of `ParabolicSmoothingEstimate`, stated separately
because it is the exact analytic input for instantaneous smoothing of the initial
datum. -/
noncomputable def ParabolicL2ToHkSmoothing {M : Type u}
    (S : SobolevScale M) (u : ℝ → M → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  0 < C → ∀ t : ℝ, 0 < t →
    S.sobolevNorm (k : ℝ) 2 (u t) ≤ C * t ^ (-(k : ℝ) / 2) * S.sobolevNorm 0 2 (u 0)

/-! ## 4. Sobolev embeddings for the Ricci-flow PDE argument -/

/-- **Statement only.**  A general Sobolev embedding `H^{s,p} ↪ H^{t,q}`: there
is `C > 0` with `‖u‖_{H^{t,q}} ≤ C ‖u‖_{H^{s,p}}` for all `u`. -/
def SobolevEmbeddingStatement {M : Type u} (S : SobolevScale M) (s p t q : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : M → ℝ, S.sobolevNorm t q u ≤ C * S.sobolevNorm s p u

/-- **Statement only (Ricci flow input).**  The Sobolev embedding
`H¹(M) ↪ L⁶(M)` on a three-manifold (`1/6 = 1/2 - 1/3`).  This is the embedding
that turns the `L²` energy estimate for `∇Rm` into the `L⁶` control used in the
curvature estimates along Ricci flow. -/
def SobolevEmbeddingH1ToL6 {M : Type u} (S : SobolevScale M) : Prop :=
  SobolevEmbeddingStatement S 1 2 0 6

/-- **Statement only (Ricci flow input).**  The Sobolev embedding
`H²(M) ↪ C⁰(M)` on a three-manifold (`2 > 3/2`).  This is the embedding that
converts an `H²` energy bound on the curvature into a pointwise bound. -/
def SobolevEmbeddingH2ToContinuous {M : Type u} (S : SobolevScale M) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : M → ℝ, S.supNorm u ≤ C * S.sobolevNorm 2 2 u

/-- **Statement only (Ricci flow input).**  The higher-order embedding
`H^k(M) ↪ C⁰(M)` for `k ≥ 2`.  This is the bootstrap step: once the smoothing
estimate produces `H^k` bounds, the curvature is controlled pointwise. -/
def SobolevEmbeddingHkToContinuous {M : Type u} (S : SobolevScale M) (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : M → ℝ, S.supNorm u ≤ C * S.sobolevNorm (k : ℝ) 2 u

/-- **Statement only (Ricci flow input).**  The Rellich–Kondrachov compact
embedding `H¹(M) ↪↪ L²(M)`: every sequence bounded in `H¹` has an `L²`-convergent
subsequence.  This is the compactness input for the limiting arguments in the
existence and convergence theory. -/
def RellichKondrachovStatement {M : Type u} (S : SobolevScale M) : Prop :=
  ∀ u : ℕ → M → ℝ, (∃ B : ℝ, ∀ n, S.sobolevNorm 1 2 (u n) ≤ B) →
    ∃ (φ : ℕ → ℕ) (w : M → ℝ), StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        S.sobolevNorm 0 2 (fun x => u (φ n) x - w x) < ε

/-- **Statement only (Ricci flow input).**  The Gagliardo–Nirenberg
interpolation inequality `‖u‖_{H¹} ≤ C ‖u‖_{L²}^{1/2} ‖u‖_{H²}^{1/2}`.  This is
used to interpolate between the `L²` energy bound and the `H²` smoothing bound. -/
noncomputable def GagliardoNirenbergInterpolationStatement {M : Type u}
    (S : SobolevScale M) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : M → ℝ,
    S.sobolevNorm 1 2 u ≤
      C * S.sobolevNorm 0 2 u ^ (1 / 2 : ℝ) * S.sobolevNorm 2 2 u ^ (1 / 2 : ℝ)

/-- **Statement only (Ricci flow input).**  The Poincaré inequality for
zero-mean functions: `‖u‖_{L²} ≤ C ‖u‖_{H¹}` when `⨍ u = 0`.  This identifies the
`H¹` norm with the Dirichlet form and supplies the constant in the Grönwall
estimate. -/
def PoincareInequalityStatement {M : Type u} (S : SobolevScale M) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : M → ℝ, S.mean u = 0 → S.sobolevNorm 0 2 u ≤ C * S.sobolevNorm 1 2 u

/-! ## 5. Closed-manifold wrappers

The statements above are over an abstract type `M` carrying a measure, so that the
finite-dimensional model can instantiate them.  The wrappers below add the exact
closed-manifold typeclass context: `M` is a compact Hausdorff `C^∞` manifold
modelled on `(E, I)` without boundary.  They are definitionally the same Props.
-/

section ClosedManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [I.Boundaryless] [MeasurableSpace M]

/-- **Statement only (closed-manifold form).**  The parabolic `L²` a-priori
estimate on a closed Riemannian manifold. -/
def ClosedManifoldParabolicL2AprioriEstimate (D : ParabolicData M) (T C : ℝ) : Prop :=
  ParabolicL2AprioriEstimate D T C

/-- **Statement only (closed-manifold form).**  The integrated energy-dissipation
estimate on a closed Riemannian manifold. -/
def ClosedManifoldParabolicEnergyDissipationEstimate (D : ParabolicData M) (T : ℝ) : Prop :=
  ParabolicEnergyDissipationEstimate D T

/-- **Statement only (closed-manifold form).**  The parabolic smoothing estimate
on a closed Riemannian manifold. -/
noncomputable def ClosedManifoldParabolicSmoothingEstimate (S : SobolevScale M)
    (u f : ℝ → M → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  ParabolicSmoothingEstimate S u f k C

/-- **Statement only (closed-manifold form).**  The Sobolev embedding
`H¹ ↪ L⁶` on a closed Riemannian three-manifold. -/
def ClosedManifoldSobolevEmbeddingH1ToL6 (S : SobolevScale M) : Prop :=
  SobolevEmbeddingH1ToL6 S

/-- **Statement only (closed-manifold form).**  The Sobolev embedding
`H² ↪ C⁰` on a closed Riemannian three-manifold. -/
def ClosedManifoldSobolevEmbeddingH2ToContinuous (S : SobolevScale M) : Prop :=
  SobolevEmbeddingH2ToContinuous S

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] in
/-- **Checked shape lemma.**  The closed-manifold a-priori estimate is
definitionally the core statement. -/
theorem closedManifoldParabolicL2AprioriEstimate_iff (D : ParabolicData M) (T C : ℝ) :
    ClosedManifoldParabolicL2AprioriEstimate D T C ↔ ParabolicL2AprioriEstimate D T C :=
  Iff.rfl

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] [MeasurableSpace M] in
/-- **Checked shape lemma.**  The closed-manifold smoothing estimate is
definitionally the core statement. -/
theorem closedManifoldParabolicSmoothingEstimate_iff (S : SobolevScale M)
    (u f : ℝ → M → ℝ) (k : ℕ) (C : ℝ) :
    ClosedManifoldParabolicSmoothingEstimate S u f k C ↔
      ParabolicSmoothingEstimate S u f k C :=
  Iff.rfl

end ClosedManifold

/-! ## 6. Checked non-vacuity witnesses -/

/-- The zero Sobolev scale. -/
def zeroSobolevScale (M : Type u) : SobolevScale M where
  sobolevNorm := fun _ _ _ => 0
  supNorm := fun _ => 0
  mean := fun _ => 0

/-- **Checked non-vacuity.**  The zero scale satisfies every embedding statement
(with constant `1`), so the statement family is consistent. -/
theorem sobolevEmbedding_zero (M : Type u) (s p t q : ℝ) :
    SobolevEmbeddingStatement (zeroSobolevScale M) s p t q :=
  ⟨1, one_pos, fun u => by simp [zeroSobolevScale]⟩

/-- **Checked non-vacuity.**  The zero scale satisfies `H¹ ↪ L⁶`. -/
theorem sobolevEmbeddingH1ToL6_zero (M : Type u) :
    SobolevEmbeddingH1ToL6 (zeroSobolevScale M) :=
  sobolevEmbedding_zero M 1 2 0 6

/-- **Checked non-vacuity.**  The zero scale satisfies `H² ↪ C⁰`. -/
theorem sobolevEmbeddingH2ToContinuous_zero (M : Type u) :
    SobolevEmbeddingH2ToContinuous (zeroSobolevScale M) :=
  ⟨1, one_pos, fun u => by simp [zeroSobolevScale]⟩

/-- **Checked non-vacuity.**  The zero scale satisfies the Rellich–Kondrachov
compactness statement. -/
theorem rellichKondrachov_zero (M : Type u) :
    RellichKondrachovStatement (zeroSobolevScale M) := by
  intro u _
  refine ⟨id, fun _ => 0, fun a b h => h, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  simp [zeroSobolevScale, hε]

/-- **Checked non-vacuity.**  The zero scale satisfies the Poincaré inequality. -/
theorem poincare_zero (M : Type u) : PoincareInequalityStatement (zeroSobolevScale M) :=
  ⟨1, one_pos, fun u _ => by simp [zeroSobolevScale]⟩

/-- **Checked non-vacuity.**  The zero scale satisfies the smoothing estimate
(with constant `1`), for every field and every order. -/
theorem parabolicSmoothingEstimate_zero (M : Type u) (u f : ℝ → M → ℝ) (k : ℕ) :
    ParabolicSmoothingEstimate (zeroSobolevScale M) u f k 1 := by
  intro _ t _
  simp [zeroSobolevScale]

/-- **A genuine non-vacuity witness.**  On the one-point space, take all norms to
be the absolute value.  Then `H¹ ↪ L⁶` holds with constant `1`. -/
def unitSobolevScale : SobolevScale Unit where
  sobolevNorm := fun _ _ u => |u ()|
  supNorm := fun u => |u ()|
  mean := fun u => u ()

/-- **Checked non-vacuity.**  `H¹ ↪ L⁶` holds for the one-point scale. -/
theorem sobolevEmbeddingH1ToL6_unit : SobolevEmbeddingH1ToL6 unitSobolevScale :=
  ⟨1, one_pos, fun u => by simp [unitSobolevScale]⟩

/-- **Checked non-vacuity.**  `H² ↪ C⁰` holds for the one-point scale. -/
theorem sobolevEmbeddingH2ToContinuous_unit :
    SobolevEmbeddingH2ToContinuous unitSobolevScale :=
  ⟨1, one_pos, fun u => by simp [unitSobolevScale]⟩

/-- **Checked non-vacuity.**  The Poincaré inequality holds for the one-point
scale (zero-mean functions vanish). -/
theorem poincare_unit : PoincareInequalityStatement unitSobolevScale :=
  ⟨1, one_pos, fun u _hu => by simp [unitSobolevScale]⟩

/-! ## 7. A genuine instance of the `L²` a-priori estimate -/

/-- The parabolic datum of the finite-dimensional matrix model. -/
noncomputable def matrixParabolicData {n : ℕ} (F : SemiDiscreteHeatFlow n) :
    ParabolicData (Fin n) where
  μ := Measure.count
  u := F.u
  f := F.f
  E := fun t => matrixEnergy (F.u t)
  dirichlet := dirichletForm F.L
  energy_eq := by
    intro t
    rw [matrixEnergy, integral_count]
    simp [dotProduct, sq]
  dirichlet_symm := fun w v => dirichletForm_symm F.isLaplacian w v
  dirichlet_nonneg := fun w => dirichletForm_nonneg F.isLaplacian w
  testClass := Set.univ
  u_mem_testClass := fun _ => Set.mem_univ _
  weak_equation := fun t φ _ => F.weak_equation t φ
  energy_identity := by
    intro t
    have hint : (∫ x, F.u t x * F.f t x ∂(Measure.count : Measure (Fin n))) = F.u t ⬝ᵥ F.f t := by
      rw [integral_count]
      simp [dotProduct]
    simpa [hint] using F.energy_identity t

/-- **Checked instance of the state-only a-priori estimate.**  In the
finite-dimensional matrix model the parabolic `L²` a-priori estimate is a theorem,
by `SemiDiscreteHeatFlow.energy_gronwall`.  This shows that the statement is not
vacuous and isolates the missing analytic content (constructing `ParabolicData`
from a genuine Riemannian manifold). -/
theorem parabolicL2AprioriEstimate_matrix {n : ℕ} (F : SemiDiscreteHeatFlow n)
    {T C : ℝ} (hC : 1 ≤ C) : ParabolicL2AprioriEstimate (matrixParabolicData F) T C := by
  intro _ _ t ht
  have ht0 : 0 ≤ t := ht.1
  have h := F.energy_gronwall hC ht0
  have hint : (∫ s in 0..t, ∫ x, (F.f s x) ^ 2 ∂(Measure.count : Measure (Fin n)))
      = ∫ s in 0..t, matrixEnergy (F.f s) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp [matrixEnergy, dotProduct, sq, integral_count]
  show matrixEnergy (F.u t) ≤ Real.exp (C * t) *
    (matrixEnergy (F.u 0) + ∫ s in 0..t, ∫ x, (F.f s x) ^ 2 ∂(Measure.count : Measure (Fin n)))
  rw [hint]
  exact h

/-! ## Axiom audit -/

#print axioms ParabolicData
#print axioms ManifoldEnergyIdentity
#print axioms manifoldEnergyIdentity_of_data
#print axioms ParabolicL2AprioriEstimate
#print axioms ParabolicEnergyDissipationEstimate
#print axioms parabolicL2AprioriEstimate_iff
#print axioms SobolevScale
#print axioms ParabolicSmoothingEstimate
#print axioms ParabolicL2ToHkSmoothing
#print axioms SobolevEmbeddingStatement
#print axioms SobolevEmbeddingH1ToL6
#print axioms SobolevEmbeddingH2ToContinuous
#print axioms SobolevEmbeddingHkToContinuous
#print axioms RellichKondrachovStatement
#print axioms GagliardoNirenbergInterpolationStatement
#print axioms PoincareInequalityStatement
#print axioms ClosedManifoldParabolicL2AprioriEstimate
#print axioms ClosedManifoldParabolicEnergyDissipationEstimate
#print axioms ClosedManifoldParabolicSmoothingEstimate
#print axioms ClosedManifoldSobolevEmbeddingH1ToL6
#print axioms ClosedManifoldSobolevEmbeddingH2ToContinuous
#print axioms closedManifoldParabolicL2AprioriEstimate_iff
#print axioms closedManifoldParabolicSmoothingEstimate_iff
#print axioms zeroSobolevScale
#print axioms sobolevEmbedding_zero
#print axioms sobolevEmbeddingH1ToL6_zero
#print axioms sobolevEmbeddingH2ToContinuous_zero
#print axioms rellichKondrachov_zero
#print axioms poincare_zero
#print axioms parabolicSmoothingEstimate_zero
#print axioms unitSobolevScale
#print axioms sobolevEmbeddingH1ToL6_unit
#print axioms sobolevEmbeddingH2ToContinuous_unit
#print axioms poincare_unit
#print axioms matrixParabolicData
#print axioms parabolicL2AprioriEstimate_matrix

end Poincare.D9.ParabolicEstimates
