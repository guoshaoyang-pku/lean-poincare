/-
Task `D9-sobolev-parabolic-estimates`: the kernel-checked semi-discrete heat-equation
model.

This file is part of the long-run Poincaré formalization.  It provides the fully
checked finite-dimensional (matrix) Laplacian model of the linear parabolic
equation `∂ₜu = -L u + f` and proves, at the level of linear algebra and calculus:

* the exact energy identity `(d/dt) E(t) = -2 |∇u|² + 2 ⟨u, f⟩`, where
  `E(t) = u(t) ⬝ᵥ u(t)` and `|∇u|² = u ⬝ᵥ (L *ᵥ u)` is the Dirichlet form;
* the differential inequality `E' ≤ E + ‖f‖²` obtained from the nonnegativity of
  the Dirichlet form and Young's inequality;
* the Grönwall bound `E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ ‖f(s)‖² ds)` for `C ≥ 1`;
* the bridge to the abstract interface of `Poincare.D9.ParabolicEstimates.Basic`:
  the matrix model is an instance of `WeakSolution` and of `ClassicalSolution` with
  the counting measure, and it satisfies the abstract `ParabolicL2Bound`.

The matrix `L` is a *matrix Laplacian*: symmetric and positive semidefinite.  The
canonical example is the graph Laplacian `Bᵀ * B` of a finite-dimensional gradient
(incidence) operator `B`, for which `|∇u|² = u ⬝ᵥ ((Bᵀ * B) *ᵥ u) = ‖B *ᵥ u‖²`;
this is proved in `dirichletForm_transpose_mul_self`.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/
import Poincare.D9.ParabolicEstimates.Basic

open MeasureTheory intervalIntegral
open scoped Matrix

namespace Poincare.D9.ParabolicEstimates

/-! ## 1. The matrix energy and the Dirichlet form -/

/-- The `ℓ²` energy `E(u) = u ⬝ᵥ u = Σ i, (u i)²` of a finite-dimensional field. -/
def matrixEnergy {n : ℕ} (u : Fin n → ℝ) : ℝ := u ⬝ᵥ u

/-- The Dirichlet form `|∇u|² = u ⬝ᵥ (L *ᵥ u)` associated with a matrix `L`. -/
def dirichletForm {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) : ℝ :=
  u ⬝ᵥ (L.mulVec v)

/-- A **matrix Laplacian**: a symmetric positive-semidefinite matrix.  The
Dirichlet form it induces is the finite-dimensional stand-in for `∫ |∇u|² dμ`. -/
structure IsMatrixLaplacian {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- Symmetry of the matrix. -/
  symm : L.IsSymm
  /-- Positive semidefiniteness, in the form `0 ≤ u ⬝ᵥ (L *ᵥ u)`. -/
  nonneg : ∀ x : Fin n → ℝ, 0 ≤ dirichletForm L x x

/-- The energy is nonnegative. -/
theorem matrixEnergy_nonneg {n : ℕ} (u : Fin n → ℝ) : 0 ≤ matrixEnergy u := by
  simp only [matrixEnergy, dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

/-- The matrix energy is the squared `ℓ²` (`L²`) norm: `E(u) = Σ i, (u i)²`. -/
theorem matrixEnergy_eq_sum_sq {n : ℕ} (u : Fin n → ℝ) :
    matrixEnergy u = ∑ i, (u i) ^ 2 := by
  simp [matrixEnergy, dotProduct, sq]

/-- The Dirichlet form of a matrix Laplacian is nonnegative on the diagonal. -/
theorem dirichletForm_nonneg {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : IsMatrixLaplacian L) (x : Fin n → ℝ) : 0 ≤ dirichletForm L x x :=
  hL.nonneg x

/-- The Dirichlet form of a matrix Laplacian is symmetric. -/
theorem dirichletForm_symm {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ} (hL : IsMatrixLaplacian L)
    (u v : Fin n → ℝ) : dirichletForm L u v = dirichletForm L v u := by
  unfold dirichletForm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hL.symm.eq]
  exact dotProduct_comm _ _

/-- **Young's inequality for the `ℓ²` pairing.**  `2 u ⬝ᵥ f ≤ E(u) + E(f)`.
This is the Cauchy–Schwarz inequality for finite sums followed by `2ab ≤ a² + b²`;
it needs no inner-product-space structure, only the dot product. -/
theorem matrixEnergy_young {n : ℕ} (u f : Fin n → ℝ) :
    2 * (u ⬝ᵥ f) ≤ matrixEnergy u + matrixEnergy f := by
  have hcs : (u ⬝ᵥ f) ^ 2 ≤ matrixEnergy u * matrixEnergy f := by
    simpa [dotProduct, matrixEnergy, sq] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) u f)
  have hu : 0 ≤ matrixEnergy u := matrixEnergy_nonneg u
  have hf : 0 ≤ matrixEnergy f := matrixEnergy_nonneg f
  by_cases hx : u ⬝ᵥ f ≤ 0
  · nlinarith
  · simp only [not_le] at hx
    have h2 : (2 * (u ⬝ᵥ f)) ^ 2 ≤ (matrixEnergy u + matrixEnergy f) ^ 2 := by
      nlinarith [sq_nonneg (matrixEnergy u - matrixEnergy f)]
    nlinarith

/-! ## 2. The semi-discrete heat flow -/

/-- **Semi-discrete heat flow.**  A classical solution of `∂ₜu = -L u + f` on the
finite-dimensional space `Fin n → ℝ`, where `L` is a matrix Laplacian.  Time is
continuous (`u : ℝ → Fin n → ℝ`); space is finite-dimensional, whence the name
"semi-discrete".  The continuity fields are used to obtain interval integrability
for the Grönwall lemma. -/
structure SemiDiscreteHeatFlow (n : ℕ) where
  /-- The matrix Laplacian. -/
  L : Matrix (Fin n) (Fin n) ℝ
  /-- The Laplacian axioms. -/
  isLaplacian : IsMatrixLaplacian L
  /-- The field. -/
  u : ℝ → Fin n → ℝ
  /-- The forcing term. -/
  f : ℝ → Fin n → ℝ
  /-- The semi-discrete heat equation `∂ₜu = -L u + f`. -/
  hasDeriv : ∀ t i, HasDerivAt (fun s => u s i) ((-(L.mulVec (u t)) + f t) i) t
  /-- Componentwise continuity of the field. -/
  cont_u : ∀ i, Continuous (fun s => u s i)
  /-- Componentwise continuity of the forcing. -/
  cont_f : ∀ i, Continuous (fun s => f s i)

/-- The derivative of the energy of a field with componentwise derivative `rhs`:
`(d/dt) (u ⬝ᵥ u) = 2 u ⬝ᵥ rhs`.  This is the linear-algebra part of the energy
identity, before the equation `rhs = -L u + f` is inserted. -/
theorem hasDerivAt_matrixEnergy {n : ℕ} (u : ℝ → Fin n → ℝ) (rhs : Fin n → ℝ) (t : ℝ)
    (h : ∀ i, HasDerivAt (fun s => u s i) (rhs i) t) :
    HasDerivAt (fun s => matrixEnergy (u s)) (2 * (u t ⬝ᵥ rhs)) t := by
  have hsum : HasDerivAt (fun s => ∑ i, u s i * u s i)
      (∑ i, (rhs i * u t i + u t i * rhs i)) t := by
    have h' := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun i s => u s i * u s i) (A' := fun i => rhs i * u t i + u t i * rhs i)
      (fun i _ => (h i).mul (h i))
    rw [show (∑ i, fun s => u s i * u s i) = (fun s => ∑ i, u s i * u s i) from by
      funext s; simp [Finset.sum_apply]] at h'
    exact h'
  have hval : (∑ i, (rhs i * u t i + u t i * rhs i)) = 2 * (u t ⬝ᵥ rhs) := by
    simp only [dotProduct]
    rw [show (∑ i, (rhs i * u t i + u t i * rhs i)) = ∑ i, 2 * (u t i * rhs i) from
      Finset.sum_congr rfl (fun i _ => by ring)]
    rw [Finset.mul_sum]
  rw [hval] at hsum
  simpa [matrixEnergy, dotProduct, sq] using hsum

/-- Continuity of the energy along a componentwise continuous field. -/
theorem continuous_matrixEnergy {n : ℕ} (u : ℝ → Fin n → ℝ)
    (h : ∀ i, Continuous (fun s => u s i)) : Continuous (fun s => matrixEnergy (u s)) := by
  simp only [matrixEnergy, dotProduct]
  exact continuous_finsetSum _ (fun i _ => (h i).mul (h i))

/-- Continuity of the Dirichlet form along a componentwise continuous field. -/
theorem continuous_dirichletForm {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (u : ℝ → Fin n → ℝ)
    (h : ∀ i, Continuous (fun s => u s i)) :
    Continuous (fun s => dirichletForm L (u s) (u s)) := by
  simp only [dirichletForm, dotProduct, Matrix.mulVec]
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul (h i)
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (h j)

/-- Continuity of the pairing of two componentwise continuous fields. -/
theorem continuous_dotProduct {n : ℕ} (u f : ℝ → Fin n → ℝ)
    (hu : ∀ i, Continuous (fun s => u s i)) (hf : ∀ i, Continuous (fun s => f s i)) :
    Continuous (fun s => u s ⬝ᵥ f s) := by
  simp only [dotProduct]
  exact continuous_finsetSum _ (fun i _ => (hu i).mul (hf i))

namespace SemiDiscreteHeatFlow

variable {n : ℕ} (F : SemiDiscreteHeatFlow n)

/-- **The exact semi-discrete energy identity**

`(d/dt) E(t) = -2 |∇u|² + 2 ⟨u, f⟩`,

where `E(t) = u(t) ⬝ᵥ u(t)` and `|∇u|² = dirichletForm L (u t) (u t)`. -/
theorem energy_identity (t : ℝ) :
    HasDerivAt (fun s => matrixEnergy (F.u s))
      (-2 * dirichletForm F.L (F.u t) (F.u t) + 2 * (F.u t ⬝ᵥ F.f t)) t := by
  have h := hasDerivAt_matrixEnergy F.u (-(F.L.mulVec (F.u t)) + F.f t) t
    (fun i => F.hasDeriv t i)
  have hval : 2 * (F.u t ⬝ᵥ (-(F.L.mulVec (F.u t)) + F.f t))
      = -2 * dirichletForm F.L (F.u t) (F.u t) + 2 * (F.u t ⬝ᵥ F.f t) := by
    unfold dirichletForm
    rw [dotProduct_add, dotProduct_neg]
    ring
  rwa [hval] at h

/-- **The energy differential inequality** `E' ≤ E + ‖f‖²`.  The dissipative term
`-2 |∇u|²` is dropped using the nonnegativity of the Dirichlet form, and the
forcing term is estimated by Young's inequality. -/
theorem energy_deriv_le (t : ℝ) :
    deriv (fun s => matrixEnergy (F.u s)) t ≤ matrixEnergy (F.u t) + matrixEnergy (F.f t) := by
  have h := (F.energy_identity t).deriv
  have hQ : 0 ≤ dirichletForm F.L (F.u t) (F.u t) := dirichletForm_nonneg F.isLaplacian _
  have hy := matrixEnergy_young (F.u t) (F.f t)
  rw [h]
  linarith

/-- **The Grönwall bound**

`E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ ‖f(s)‖² ds)` for every `C ≥ 1` and `t ≥ 0`.

The proof combines the energy identity with the real-analysis Grönwall lemma
`gronwall_energy_bound`; the integrability hypotheses of that lemma are discharged
from the componentwise continuity of `u` and `f`. -/
theorem energy_gronwall {C t : ℝ} (hC : 1 ≤ C) (ht : 0 ≤ t) :
    matrixEnergy (F.u t) ≤ Real.exp (C * t) *
      (matrixEnergy (F.u 0) + ∫ s in 0..t, matrixEnergy (F.f s)) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hE : ∀ s, HasDerivAt (fun s => matrixEnergy (F.u s))
      (-2 * dirichletForm F.L (F.u s) (F.u s) + 2 * (F.u s ⬝ᵥ F.f s)) s :=
    fun s => F.energy_identity s
  have hineq : ∀ s, (-2 * dirichletForm F.L (F.u s) (F.u s) + 2 * (F.u s ⬝ᵥ F.f s))
      ≤ C * matrixEnergy (F.u s) + matrixEnergy (F.f s) := by
    intro s
    have hQ : 0 ≤ dirichletForm F.L (F.u s) (F.u s) := dirichletForm_nonneg F.isLaplacian _
    have hy := matrixEnergy_young (F.u s) (F.f s)
    have hE0 : 0 ≤ matrixEnergy (F.u s) := matrixEnergy_nonneg _
    nlinarith
  have hg : ∀ s, 0 ≤ matrixEnergy (F.f s) := fun s => matrixEnergy_nonneg _
  have hcontE : Continuous (fun s => matrixEnergy (F.u s)) := continuous_matrixEnergy F.u F.cont_u
  have hcontQ : Continuous (fun s => dirichletForm F.L (F.u s) (F.u s)) :=
    continuous_dirichletForm F.L F.u F.cont_u
  have hcontuf : Continuous (fun s => F.u s ⬝ᵥ F.f s) :=
    continuous_dotProduct F.u F.f F.cont_u F.cont_f
  have hcontY : Continuous (fun s => Real.exp (-C * s) *
      ((-2 * dirichletForm F.L (F.u s) (F.u s) + 2 * (F.u s ⬝ᵥ F.f s))
        - C * matrixEnergy (F.u s))) := by
    apply Continuous.mul
    · exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
    · exact ((hcontQ.const_mul (-2)).add (hcontuf.const_mul 2)).sub (hcontE.const_mul C)
  have hintY : IntervalIntegrable (fun s => Real.exp (-C * s) *
      ((-2 * dirichletForm F.L (F.u s) (F.u s) + 2 * (F.u s ⬝ᵥ F.f s))
        - C * matrixEnergy (F.u s))) volume 0 t := hcontY.intervalIntegrable 0 t
  have hintg : IntervalIntegrable (fun s => matrixEnergy (F.f s)) volume 0 t :=
    (continuous_matrixEnergy F.f F.cont_f).intervalIntegrable 0 t
  exact gronwall_energy_bound hC0 ht hE hineq hg hintY hintg

/-! ## 3. The weak formulation and the abstract interface -/

/-- **The matrix model satisfies the weak parabolic equation.**  For every test
function `φ`, `(d/ds) Σ x, u(s) x * φ x = -u(t) ⬝ᵥ (L *ᵥ φ) + Σ x, f(t) x * φ x`;
the symmetry of `L` is exactly what moves `L` from the solution to the test
function (discrete integration by parts). -/
theorem weak_equation (t : ℝ) (φ : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, F.u s x * φ x ∂(Measure.count : Measure (Fin n)))
      (-(dirichletForm F.L (F.u t) φ)
        + ∫ x, F.f t x * φ x ∂(Measure.count : Measure (Fin n))) t := by
  have hsum : ∀ s : ℝ, (∫ x, F.u s x * φ x ∂(Measure.count : Measure (Fin n)))
      = ∑ x, F.u s x * φ x := fun s => integral_count _
  simp only [hsum]
  have hderiv : HasDerivAt (fun s => ∑ x, F.u s x * φ x)
      (∑ x, ((-(F.L.mulVec (F.u t)) + F.f t) x) * φ x) t := by
    have h' := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun i s => F.u s i * φ i)
      (A' := fun i => ((-(F.L.mulVec (F.u t)) + F.f t) i) * φ i)
      (fun i _ => (F.hasDeriv t i).mul_const (φ i))
    rw [show (∑ i, fun s => F.u s i * φ i) = (fun s => ∑ i, F.u s i * φ i) from by
      funext s; simp [Finset.sum_apply]] at h'
    exact h'
  have hs : (∑ x, (F.L.mulVec (F.u t)) x * φ x) = dirichletForm F.L (F.u t) φ := by
    rw [show (∑ x, (F.L.mulVec (F.u t)) x * φ x) = (F.L.mulVec (F.u t)) ⬝ᵥ φ by
      simp [dotProduct]]
    rw [dotProduct_comm, dirichletForm_symm F.isLaplacian (F.u t) φ]
    rfl
  have hval : (∑ x, ((-(F.L.mulVec (F.u t)) + F.f t) x) * φ x)
      = -(dirichletForm F.L (F.u t) φ) + ∑ x, F.f t x * φ x := by
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [show (∑ x, (-(F.L.mulVec (F.u t)) x + F.f t x) * φ x)
        = ∑ x, (-((F.L.mulVec (F.u t)) x * φ x) + F.f t x * φ x) from
      Finset.sum_congr rfl (fun x _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hs]
  rw [hval] at hderiv
  rw [show (∫ x, F.f t x * φ x ∂(Measure.count : Measure (Fin n))) = ∑ x, F.f t x * φ x
    from integral_count _]
  exact hderiv

/-- The energy functional of the matrix model over the counting measure. -/
noncomputable def matrixEnergyFunctional : EnergyFunctional (Fin n) (Measure.count) where
  u := F.u
  f := F.f
  E := fun t => matrixEnergy (F.u t)
  energy_eq := by
    intro t
    rw [energyDensity, integral_count]
    simp [matrixEnergy, dotProduct, sq]
  integrable_energy := by
    intro t
    exact Integrable.of_finite

/-- The Dirichlet form of the matrix model as an abstract `DirichletForm`. -/
def matrixDirichletForm : DirichletForm (Fin n) where
  form := dirichletForm F.L
  symm := fun u v => dirichletForm_symm F.isLaplacian u v
  nonneg := fun u => dirichletForm_nonneg F.isLaplacian u

/-- The matrix model as an abstract weak solution over the counting measure. -/
noncomputable def matrixWeakSolution : WeakSolution (Fin n) (Measure.count) where
  toEnergyFunctional := matrixEnergyFunctional F
  D := matrixDirichletForm F
  testClass := Set.univ
  u_mem_testClass := fun _ => Set.mem_univ _
  weak_equation := fun t φ _ => F.weak_equation t φ

/-- **Checked instance of the abstract energy identity.**  The matrix model
satisfies `EnergyIdentityStatement` for the abstract weak-solution interface; this
is the exact `(d/dt) E = -2 |∇u|² + 2 ⟨u, f⟩` transported through
`∫ = Σ` (the counting-measure identity). -/
theorem matrixEnergyIdentity : EnergyIdentityStatement (matrixWeakSolution F) := by
  intro t
  have hint : (∫ x, F.u t x * F.f t x ∂(Measure.count : Measure (Fin n))) = F.u t ⬝ᵥ F.f t := by
    rw [integral_count]
    simp [dotProduct]
  simpa [EnergyIdentityStatement, matrixWeakSolution, matrixEnergyFunctional,
    matrixDirichletForm, hint] using F.energy_identity t

/-- The matrix model as an abstract classical solution. -/
noncomputable def matrixClassicalSolution : ClassicalSolution (Fin n) (Measure.count) where
  toWeakSolution := matrixWeakSolution F
  energy_identity := matrixEnergyIdentity F

end SemiDiscreteHeatFlow

/-- The forcing energy over the counting measure is the `ℓ²` energy of the
forcing: `∫ |f|² d# = f ⬝ᵥ f`. -/
theorem forcingEnergy_count {n : ℕ} (f : Fin n → ℝ) :
    forcingEnergy (Fin n) (Measure.count) f = matrixEnergy f := by
  rw [forcingEnergy, matrixEnergy, integral_count]
  simp [dotProduct, sq]

/-- **The abstract parabolic `L²` bound holds for the matrix model.**  This
instantiates `ParabolicL2Bound` from the abstract interface with the concrete
Grönwall estimate `SemiDiscreteHeatFlow.energy_gronwall`. -/
theorem matrix_parabolicL2Bound {n : ℕ} (F : SemiDiscreteHeatFlow n) {C : ℝ}
    (hC : 1 ≤ C) : ParabolicL2Bound (F.matrixClassicalSolution).toWeakSolution C := by
  intro _ t ht
  have h := F.energy_gronwall hC ht
  simpa [ParabolicL2Bound, SemiDiscreteHeatFlow.matrixClassicalSolution,
    SemiDiscreteHeatFlow.matrixWeakSolution, SemiDiscreteHeatFlow.matrixEnergyFunctional,
    forcingEnergy_count] using h

/-! ## 4. Non-vacuity: the graph Laplacian `Bᵀ * B` and the zero flow -/

/-- **The graph Laplacian is a matrix Laplacian.**  For any finite-dimensional
gradient (incidence) operator `B`, the Dirichlet form of `Bᵀ * B` is
`u ↦ (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = ‖B *ᵥ u‖²`, the squared length of the discrete
gradient. -/
theorem dirichletForm_transpose_mul_self {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin n → ℝ) :
    dirichletForm (Bᵀ * B) u u = matrixEnergy (B.mulVec u) := by
  unfold dirichletForm matrixEnergy
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose]

/-- **Checked non-vacuity.**  Every graph Laplacian `Bᵀ * B` is a matrix
Laplacian, so the model is not vacuous and covers the standard finite-difference
and graph discretizations. -/
theorem isMatrixLaplacian_transpose_mul_self {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    IsMatrixLaplacian (Bᵀ * B) where
  symm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  nonneg := by
    intro x
    rw [dirichletForm_transpose_mul_self B x]
    exact matrixEnergy_nonneg _

/-- The zero matrix is a matrix Laplacian. -/
theorem isMatrixLaplacian_zero (n : ℕ) :
    IsMatrixLaplacian (0 : Matrix (Fin n) (Fin n) ℝ) where
  symm := by
    unfold Matrix.IsSymm
    simp
  nonneg := by
    intro x
    simp [dirichletForm]

/-- **Checked non-vacuity.**  The zero flow (zero field, zero forcing, zero
Laplacian) is a semi-discrete heat flow, so the structure is inhabited for every
dimension. -/
noncomputable def zeroHeatFlow (n : ℕ) : SemiDiscreteHeatFlow n where
  L := 0
  isLaplacian := isMatrixLaplacian_zero n
  u := fun _ _ => 0
  f := fun _ _ => 0
  hasDeriv := by
    intro t i
    simpa using hasDerivAt_const t (0 : ℝ)
  cont_u := fun _ => continuous_const
  cont_f := fun _ => continuous_const

/-! ## Axiom audit -/

#print axioms matrixEnergy
#print axioms dirichletForm
#print axioms IsMatrixLaplacian
#print axioms matrixEnergy_nonneg
#print axioms matrixEnergy_eq_sum_sq
#print axioms dirichletForm_nonneg
#print axioms dirichletForm_symm
#print axioms matrixEnergy_young
#print axioms hasDerivAt_matrixEnergy
#print axioms continuous_matrixEnergy
#print axioms continuous_dirichletForm
#print axioms continuous_dotProduct
#print axioms SemiDiscreteHeatFlow
#print axioms SemiDiscreteHeatFlow.energy_identity
#print axioms SemiDiscreteHeatFlow.energy_deriv_le
#print axioms SemiDiscreteHeatFlow.energy_gronwall
#print axioms SemiDiscreteHeatFlow.weak_equation
#print axioms SemiDiscreteHeatFlow.matrixEnergyFunctional
#print axioms SemiDiscreteHeatFlow.matrixDirichletForm
#print axioms SemiDiscreteHeatFlow.matrixWeakSolution
#print axioms SemiDiscreteHeatFlow.matrixEnergyIdentity
#print axioms SemiDiscreteHeatFlow.matrixClassicalSolution
#print axioms forcingEnergy_count
#print axioms matrix_parabolicL2Bound
#print axioms dirichletForm_transpose_mul_self
#print axioms isMatrixLaplacian_transpose_mul_self
#print axioms isMatrixLaplacian_zero
#print axioms zeroHeatFlow

end Poincare.D9.ParabolicEstimates
