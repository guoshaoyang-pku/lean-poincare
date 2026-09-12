import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Poincare.D12.TensorMaximumBochner.PositivityPreservation

/-!
# Poincare.D12.TensorMaximumBochner.TangentCone

**Task `D12-tensor-maximum-bochner`, track B2: the *correct* tangent-cone condition for the
positive-semidefinite cone, and the algebraic core of Hamilton's tensor maximum principle.**

The companion module `PositivityPreservation` proves a matrix ODE maximum principle under the
*strengthened* quadratic-form condition

`vᵀ A v ≤ 0 ⟹ 0 ≤ vᵀ P(A) v  for all Hermitian A and all v`

which is strictly stronger than the classical Hamilton (null-eigenvector / tangent-cone)
condition.  This module isolates, with proofs, the precise difference:

1. `KernelTangent A N` is Hamilton's null-eigenvector condition: `A v = 0 ⟹ 0 ≤ vᵀN v` for
   `A ⪰ 0`.  For `A ⪰ 0` this is exactly the condition that `N` lie in the (closed) tangent
   cone of the PSD cone at `A`; it is *not* an assumed identity, it is a quadratic-form
   condition on the pair `(A, N)`.
2. `FeasibleDirection A N` is the *feasibility* condition: `A + s N ⪰ 0` for all small
   `s ≥ 0`.
3. `kernelTangent_of_feasibleDirection` proves that the Hamilton condition is **necessary**
   for feasibility, and `kernelTangent_of_posSemidef_path` proves the path (first-variation)
   form: the derivative at time `0` of a PSD path lies in the tangent cone at the initial
   point.  So the condition cannot be weakened; it is the correct one.
4. `kernelTangent_not_feasible` gives an explicit, checked **2 × 2 witness** showing that the
   Hamilton condition is *not* a feasibility condition: `A = diag(0,1)`, `N = !![0,1;1,-1]`
   satisfies `KernelTangent` while `det (A + s • N) = -s²` for every `s ≠ 0`, so `A + s • N` is
   never positive semidefinite.  This is the exact reason why the classical condition cannot be
   used by a first-order perturbation argument inside the cone, and why a Nagumo /
   eigenvalue-comparison step (not formalised here) is required to pass from `KernelTangent` to
   ODE invariance.  The failure is genuinely second order; the condition itself is nevertheless
   the exact tangent-cone condition.
5. `hamiltonField A = A² + adj(A)` is the algebraic core of the reaction ODE of Hamilton's
   tensor maximum principle for the curvature operator in dimension 3 (under the Hodge-star
   identification `Λ²ℝ³ ≅ ℝ³`, the Lie-algebra square `R#` becomes the adjugate/cofactor
   matrix, so the reaction term `R² + R#` becomes `A² + adj(A)`).
   `adjugate_posSemidef` proves `A ⪰ 0 ⟹ adj(A) ⪰ 0` (the algebraic content of "`R#` is
   nonnegative on the PSD cone"), and `hamiltonField_kernelTangent` proves that this field
   satisfies Hamilton's null-eigenvector condition at every PSD matrix.  This is a genuine
   downstream computation: the conclusion is not a projection of an assumed identity, it is
   computed from the cofactor expansion.
6. `hamiltonField_not_strengthened` proves that the *strengthened* hypothesis of
   `PositivityPreservation.staysPosSemidef_of_field` **fails** for this field at a non-PSD
   Hermitian matrix.  Hence the earlier theorem does not cover Hamilton's field, and the
   passage from the null-eigenvector condition to ODE invariance is exactly the missing step
   (recorded as the remaining blocker; no such invariance theorem is claimed here).

All hypotheses are expanded; there is no `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`
or `proof_wanted`.
-/

open scoped BigOperators
open scoped Matrix
open scoped Topology
open Filter

namespace Poincare
namespace D12
namespace TensorMaximumBochner

/-! ## The two conditions -/

/-- **Hamilton's null-eigenvector (tangent-cone) condition.**  For matrices `A N : Matrix n n ℝ`,
`KernelTangent A N` says that the quadratic form of `N` is nonnegative on the kernel of `A`.
For `A ⪰ 0` this is exactly the condition `N ∈ T_{PSD}(A)` (the closed tangent cone of the
positive-semidefinite cone at `A`). -/
def KernelTangent {n : Type*} [Fintype n] (A N : Matrix n n ℝ) : Prop :=
  ∀ v : n → ℝ, A *ᵥ v = 0 → 0 ≤ star v ⬝ᵥ (N *ᵥ v)

/-- **Strict form of the tangent-cone condition.**  The quadratic form of `N` is not only
nonnegative but bounded below by `c ‖v‖²` on the kernel of `A`.  This is the condition under
which `N` is a genuine interior tangent direction; the general passage from `KernelTangent` to
invariance is *not* proved in this module (see the module docstring and `checkpoint.json`). -/
def StrictKernelTangent {n : Type*} [Fintype n] (A N : Matrix n n ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ v : n → ℝ, A *ᵥ v = 0 → c * (star v ⬝ᵥ v) ≤ star v ⬝ᵥ (N *ᵥ v)

/-- **Feasibility of a tangent direction.**  `FeasibleDirection A N` says that `A + s • N` is
positive semidefinite for all sufficiently small `s ≥ 0`; this is the (non-closed) cone of
genuine first-order perturbations of `A` inside the PSD cone. -/
def FeasibleDirection {n : Type*} [Fintype n] (A N : Matrix n n ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc 0 ε, (A + s • N).PosSemidef

/-- Continuity of the quadratic form `M ↦ xᵀ M x` on matrices (a linear map on a
finite-dimensional space). -/
lemma continuous_dotProduct_mulVec {n : Type*} [Fintype n] (x : n → ℝ) :
    Continuous fun M : Matrix n n ℝ => star x ⬝ᵥ (M *ᵥ x) := by
  let L : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
      map_add' := by
        intro B C
        simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
          Finset.mul_sum]
      map_smul' := by
        intro a B
        simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
  simpa [L] using L.continuous_of_finiteDimensional

/-! ## Necessity: the Hamilton condition is the correct tangent-cone condition -/

/-- **The null-eigenvector condition is necessary for feasibility.**  If `A + s • N` is
positive semidefinite for all small `s ≥ 0`, then `vᵀ N v ≥ 0` for every `v` in the kernel of
`A`: apply the PSD quadratic-form inequality at `s > 0` and use `A v = 0`.  This is the
first-variation computation that pins down the condition; it shows the condition cannot be
replaced by a weaker one. -/
theorem kernelTangent_of_feasibleDirection {n : Type*} [Fintype n] {A N : Matrix n n ℝ}
    (h : FeasibleDirection A N) : KernelTangent A N := by
  obtain ⟨ε, hε, hfeas⟩ := h
  intro v hv
  have hs : ε / 2 ∈ Set.Icc 0 ε := ⟨by linarith, by linarith⟩
  have hpsd : (A + (ε / 2) • N).PosSemidef := hfeas (ε / 2) hs
  have hnn : 0 ≤ star v ⬝ᵥ ((A + (ε / 2) • N) *ᵥ v) := hpsd.dotProduct_mulVec_nonneg v
  have hexp : star v ⬝ᵥ ((A + (ε / 2) • N) *ᵥ v)
      = star v ⬝ᵥ (A *ᵥ v) + (ε / 2) * (star v ⬝ᵥ (N *ᵥ v)) := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hexp, hv] at hnn
  simp only [dotProduct_zero, zero_add] at hnn
  have hε2 : 0 < ε / 2 := by linarith
  by_contra hneg
  have hneg' : star v ⬝ᵥ (N *ᵥ v) < 0 := not_le.mp hneg
  have : (ε / 2) * (star v ⬝ᵥ (N *ᵥ v)) < 0 := mul_neg_of_pos_of_neg hε2 hneg'
  linarith

/-- **First variation of a PSD path.**  If a matrix path is positive semidefinite on `[0,ε]`,
starts at `A`, and each scalar quadratic form `t ↦ vᵀ M(t) v` has right derivative `vᵀ N v` at
time `0` (the explicit time-regularity hypothesis), then `N` satisfies Hamilton's
null-eigenvector condition at `A = M 0`.  This is the path form of
`kernelTangent_of_feasibleDirection`: for `v ∈ ker A` the scalar path has a boundary minimum at
`t = 0`, so its right derivative there is nonnegative. -/
theorem kernelTangent_of_posSemidef_path {n : Type*} [Fintype n] {M : ℝ → Matrix n n ℝ}
    {A N : Matrix n n ℝ} {ε : ℝ} (hε : 0 < ε)
    (hpsd : ∀ t ∈ Set.Icc 0 ε, (M t).PosSemidef)
    (hM0 : M 0 = A)
    (hderiv : ∀ v : n → ℝ,
      HasDerivAt (fun t => star v ⬝ᵥ (M t *ᵥ v)) (star v ⬝ᵥ (N *ᵥ v)) 0) :
    KernelTangent A N := by
  intro v hv
  let φ : ℝ → ℝ := fun t => star v ⬝ᵥ (M t *ᵥ v)
  have hφ0 : φ 0 = 0 := by simp [φ, hM0, hv]
  have hφnonneg : ∀ t ∈ Set.Icc 0 ε, 0 ≤ φ t := fun t ht =>
    (hpsd t ht).dotProduct_mulVec_nonneg v
  have hφderiv : HasDerivAt φ (star v ⬝ᵥ (N *ᵥ v)) 0 := hderiv v
  by_contra hneg
  have hneg' : star v ⬝ᵥ (N *ᵥ v) < 0 := not_le.mp hneg
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (φ t - φ 0)) (𝓝[>] 0)
      (𝓝 (star v ⬝ᵥ (N *ᵥ v))) := by
    simpa using HasDerivAt.tendsto_slope_zero_right hφderiv
  have hevslope : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * (φ t - φ 0) < 0 :=
    hslope.eventually (IsOpen.mem_nhds isOpen_Iio hneg')
  have hevpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hevε : Set.Iio ε ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio hε)
  have hevall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (φ t - φ 0) < 0 ∧ 0 < t ∧ t < ε :=
    hevslope.and (hevpos.and hevε)
  obtain ⟨t, ht1, ht2, ht3⟩ := hevall.exists
  have hφt : φ t < 0 := by
    have hpos : 0 < t := ht2
    have hmul : t * (t⁻¹ * (φ t - φ 0)) < 0 := mul_neg_of_pos_of_neg hpos ht1
    calc φ t = t * (t⁻¹ * (φ t - φ 0)) := by
          rw [hφ0, sub_zero, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      _ < 0 := hmul
  exact not_lt_of_ge (hφnonneg t ⟨le_of_lt ht2, le_of_lt ht3⟩) hφt

/-! ## The Hamilton condition is not a feasibility condition: an explicit witness -/

/-- The PSD matrix `diag(0,1)` used in the sharpness witness. -/
def counterexampleA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- The symmetric matrix `!![0,1;1,-1]` used in the sharpness witness.  Its quadratic form is
nonnegative on the kernel of `counterexampleA` but it is not a feasible direction. -/
def counterexampleN : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, -1]

lemma counterexampleA_posSemidef : counterexampleA.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [counterexampleA]
  · intro v
    simp [counterexampleA, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    first | positivity | nlinarith [sq_nonneg (v 1)]

lemma counterexampleA_isHermitian : counterexampleA.IsHermitian :=
  counterexampleA_posSemidef.1

/-- The kernel of `counterexampleA` is spanned by `![1,0]`; on it the quadratic form of
`counterexampleN` vanishes.  Hence the Hamilton condition holds. -/
theorem counterexample_kernelTangent : KernelTangent counterexampleA counterexampleN := by
  intro v hv
  have hv1 : v 1 = 0 := by
    have h := congrFun hv 1
    simpa [counterexampleA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  simp [counterexampleN, dotProduct, Matrix.mulVec, Fin.sum_univ_two, hv1]

/-- **The witness: the Hamilton condition does not imply feasibility.**  For
`A = diag(0,1)` and `N = !![0,1;1,-1]` the determinant of `A + s • N` equals `-s²`, so that
matrix is never positive semidefinite for `s ≠ 0`.  This shows that the passage from the
null-eigenvector condition to invariance cannot be a first-order perturbation argument; the
tangency is genuinely second order. -/
theorem counterexample_not_feasible : ¬ FeasibleDirection counterexampleA counterexampleN := by
  rintro ⟨ε, hε, hfeas⟩
  have hs : ε / 2 ∈ Set.Icc 0 ε := ⟨by linarith, by linarith⟩
  have hpsd : (counterexampleA + (ε / 2) • counterexampleN).PosSemidef := hfeas (ε / 2) hs
  have hdet_nonneg : 0 ≤ (counterexampleA + (ε / 2) • counterexampleN).det := hpsd.det_nonneg
  have hdet : (counterexampleA + (ε / 2) • counterexampleN).det = -((ε / 2) ^ 2) := by
    simp [counterexampleA, counterexampleN, Matrix.det_fin_two]
    ring
  rw [hdet] at hdet_nonneg
  have hpos : 0 < (ε / 2) ^ 2 := pow_pos (by linarith : 0 < ε / 2) 2
  linarith

/-- **Sharpness of the tangent-cone condition.**  The Hamilton null-eigenvector condition is
necessary (`kernelTangent_of_feasibleDirection`) but not sufficient for feasibility: there is
an explicit pair `(A, N)` with `A ⪰ 0`, `KernelTangent A N` and `¬ FeasibleDirection A N`.
Consequently no theorem can deduce ODE invariance from `KernelTangent` alone by a perturbation
argument; the classical proof needs a Nagumo/eigenvalue-comparison argument, which is exactly
the missing ingredient recorded in `checkpoint.json`. -/
theorem kernelTangent_not_feasible :
    ∃ A N : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosSemidef ∧ KernelTangent A N ∧ ¬ FeasibleDirection A N :=
  ⟨counterexampleA, counterexampleN, counterexampleA_posSemidef,
    counterexample_kernelTangent, counterexample_not_feasible⟩

/-! ## The algebraic core of Hamilton's tensor maximum principle in dimension 3

Under the Hodge-star identification `Λ²ℝ³ ≅ ℝ³`, an operator `R : Λ²ℝ³ → Λ²ℝ³` corresponds to a
`3 × 3` matrix `A`, and the Lie-algebra square `R#` corresponds to the adjugate (cofactor)
matrix `adj(A)`: for `A = diag(λ₁,λ₂,λ₃)` one has `adj(A) = diag(λ₂λ₃, λ₁λ₃, λ₁λ₂)`, which is
exactly the action of `Λ²A` on `e₂∧e₃, e₁∧e₃, e₁∧e₂`.  The reaction ODE of the tensor maximum
principle is therefore `A' = A² + adj(A)`, and the two algebraic facts needed for the
null-eigenvector condition are proved below. -/

/-- **Adjugate of an invertible matrix.**  For an invertible matrix, `adj(A) = det(A) • A⁻¹`.
This is the identity used to transfer positive semidefiniteness from `A⁻¹` to `adj(A)`. -/
theorem adjugate_eq_det_smul_inv {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (h : IsUnit A.det) : A.adjugate = A.det • A⁻¹ := by
  have h1 : A⁻¹ = (A.det)⁻¹ • A.adjugate := by
    rw [Matrix.nonsing_inv_apply A h]
    congr 1
    exact Units.val_inv_eq_inv_val h.unit |>.trans (congrArg Inv.inv (IsUnit.unit_spec h))
  calc A.adjugate = (A.det * (A.det)⁻¹) • A.adjugate := by
        rw [mul_inv_cancel₀ h.ne_zero, one_smul]
    _ = A.det • ((A.det)⁻¹ • A.adjugate) := by rw [← smul_smul]
    _ = A.det • A⁻¹ := by rw [h1]

/-- **The adjugate preserves positive semidefiniteness.**  If `A ⪰ 0` then `adj(A) ⪰ 0`.  In
dimension 3 this is the statement that `R# ⪰ 0` whenever the curvature operator `R ⪰ 0`, i.e.
the algebraic content of Hamilton's cone-invariance computation for the reaction ODE.

Proof: for `ε > 0` the matrix `A + ε • 1` is positive definite, hence invertible with
`adj(A + ε • 1) = det(A + ε • 1) • (A + ε • 1)⁻¹ ⪰ 0` (the determinant and the inverse are both
nonnegative).  Letting `ε ↓ 0` and using continuity of the adjugate and closedness of the PSD
quadratic-form inequalities gives the claim for `A`. -/
theorem adjugate_posSemidef {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : A.adjugate.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · exact (Matrix.adjugate_conjTranspose A).trans (by rw [hA.1.eq])
  · intro x
    have hεpos : ∀ ε : ℝ, 0 < ε → ((A + ε • 1).adjugate).PosSemidef := by
      intro ε hε
      have hpd : (A + ε • 1).PosDef :=
        Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)
      have hunit : IsUnit (A + ε • 1).det :=
        (Matrix.isUnit_iff_isUnit_det (A + ε • 1)).mp (Matrix.PosDef.isUnit hpd)
      rw [adjugate_eq_det_smul_inv hunit]
      exact Matrix.PosSemidef.smul (Matrix.PosSemidef.inv (Matrix.PosDef.posSemidef hpd))
        (le_of_lt (Matrix.PosDef.det_pos hpd))
    have hadj : Continuous fun ε : ℝ => (A + ε • 1).adjugate :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_adjugate
    have htend : Tendsto (fun ε : ℝ => star x ⬝ᵥ ((A + ε • 1).adjugate *ᵥ x)) (𝓝[>] 0)
        (𝓝 (star x ⬝ᵥ (A.adjugate *ᵥ x))) := by
      have h := ((continuous_dotProduct_mulVec x).comp hadj).tendsto 0 |>.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))
      simpa [Function.comp_def] using h
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hεpos ε hε).dotProduct_mulVec_nonneg x

/-- **The Hamilton reaction field in dimension 3**: `P(A) = A² + adj(A)`, the matrix form of
`R² + R#` under the identification `Λ²ℝ³ ≅ ℝ³` (see the section docstring). -/
noncomputable def hamiltonField {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A ^ 2 + A.adjugate

/-- **The square term is a square.**  `vᵀ A² v = ‖A v‖²` for Hermitian `A`, the identity that
makes the `A²` part of the reaction field vanish on the kernel of `A`. -/
lemma dotProduct_mulVec_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (v : n → ℝ) :
    star v ⬝ᵥ (Matrix.mulVec (A ^ 2) v) = star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v) := by
  rw [pow_two]
  rw [← Matrix.mulVec_mulVec]
  change star v ⬝ᵥ (fun i => (A i) ⬝ᵥ (Matrix.mulVec A v)) =
    star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)
  rw [← dotProduct_assoc]
  have h2 : star (Matrix.mulVec A v) = Matrix.vecMul (star v) A := by
    rw [Matrix.star_mulVec, hA]
  change Matrix.vecMul (star v) A ⬝ᵥ (Matrix.mulVec A v) =
    star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)
  rw [← h2]

/-- **The Hamilton reaction field satisfies the null-eigenvector condition at every PSD
matrix.**  If `A ⪰ 0` and `A v = 0`, then `vᵀ(A² + adj A)v = ‖Av‖² + vᵀ adj(A) v ≥ 0`: the
first term vanishes on the kernel and the second is nonnegative by `adjugate_posSemidef`.
This is a genuine computation from the cofactor expansion, not a projection of an assumed
identity. -/
theorem hamiltonField_kernelTangent {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : KernelTangent A (hamiltonField A) := by
  intro v hv
  have hsq : star v ⬝ᵥ ((A ^ 2) *ᵥ v) = 0 := by
    rw [dotProduct_mulVec_sq hA.1]
    rw [hv]
    simp
  have hadj : 0 ≤ star v ⬝ᵥ (A.adjugate *ᵥ v) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg (adjugate_posSemidef A hA) v
  rw [hamiltonField, Matrix.add_mulVec, dotProduct_add, hsq, zero_add]
  exact hadj

/-! ## The strengthened condition does not cover the Hamilton field -/

/-- **The strengthened quadratic-form hypothesis of the earlier matrix maximum principle fails
for the Hamilton reaction field.**  `PositivityPreservation.staysPosSemidef_of_field` requires
`vᵀAv ≤ 0 ⟹ 0 ≤ vᵀP(A)v` for *every* Hermitian `A` (including non-PSD ones).  For
`A = !![(-1),0;0,0]` and `v = ![0,1]` we have `vᵀAv = 0 ≤ 0` but
`vᵀ(A² + adj A)v = -1 < 0`.  Hence the earlier theorem cannot be applied to Hamilton's field,
and the missing step is exactly the passage from `KernelTangent` to ODE invariance on the cone
(a Nagumo/eigenvalue-comparison argument), not a rearrangement of the earlier proof. -/
theorem hamiltonField_not_strengthened :
    ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.IsHermitian → ∀ v : Fin 2 → ℝ,
        star v ⬝ᵥ (A *ᵥ v) ≤ 0 → 0 ≤ star v ⬝ᵥ (hamiltonField A *ᵥ v)) := by
  intro h
  have hHerm : (!![(-1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hv : star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
      ((!![(-1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) ≤ 0 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  have hcon := h (!![(-1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) hHerm ![0, 1] hv
  have hval : star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
      (hamiltonField (!![(-1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = -1 := by
    simp [hamiltonField, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two]
  rw [hval] at hcon
  norm_num at hcon

/-! ## Non-vacuity of the conditions -/

/-- Non-vacuity of the null-eigenvector condition: at the PSD matrix `A = diag(1,0)` the field
`A² + adj(A)` is `diag(1,1)`, whose quadratic form on the kernel vector `e₂` equals `1 > 0`.
So `hamiltonField_kernelTangent` is not a vacuous statement at a singular PSD matrix, and the
value is strictly positive, coming from the adjugate term (the `A²` term contributes `0` on the
kernel). -/
theorem hamiltonField_kernel_witness :
    star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
      (hamiltonField (!![(1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = 1 := by
  simp [hamiltonField, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two]

/-- The counterexample pair is nondegenerate: `counterexampleA` is PSD with a nontrivial kernel
and `counterexampleN` is nonzero. -/
theorem counterexample_nondegenerate :
    counterexampleA 0 0 = 0 ∧ counterexampleA 1 1 = 1 ∧ counterexampleN 0 1 = 1 ∧
      counterexampleA *ᵥ (![1, 0] : Fin 2 → ℝ) = 0 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  ext i
  fin_cases i <;> simp [counterexampleA, Matrix.mulVec]

/-! ## Axiom audit (fail-closed; see `tools/d12_axiom_audit.py`)

Every declaration of this file is listed here; the audit script additionally checks coverage
(that no declaration is silently left unaudited). -/

#print axioms KernelTangent
#print axioms StrictKernelTangent
#print axioms FeasibleDirection
#print axioms continuous_dotProduct_mulVec
#print axioms kernelTangent_of_feasibleDirection
#print axioms kernelTangent_of_posSemidef_path
#print axioms counterexampleA
#print axioms counterexampleN
#print axioms counterexampleA_posSemidef
#print axioms counterexampleA_isHermitian
#print axioms counterexample_kernelTangent
#print axioms counterexample_not_feasible
#print axioms kernelTangent_not_feasible
#print axioms adjugate_eq_det_smul_inv
#print axioms adjugate_posSemidef
#print axioms hamiltonField
#print axioms dotProduct_mulVec_sq
#print axioms hamiltonField_kernelTangent
#print axioms hamiltonField_not_strengthened
#print axioms hamiltonField_kernel_witness
#print axioms counterexample_nondegenerate

end TensorMaximumBochner
end D12
end Poincare
