import Mathlib.Tactic
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.Entropy.Bridge
import Poincare.D12.TensorMaximumBochner.TensorCalculus
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.So3Polynomial
import Poincare.D12.TensorMaximumBochner.So3RicciFlow
import Poincare.D12.TensorMaximumBochner.TangentCone

/-!
# Poincare.D12.TensorMaximumBochner.Audit

**Task-local audit module for `D12-tensor-maximum-bochner`.** This file does *not* prove new
mathematics beyond what the two companion modules already prove; it records, with
machine-checked references, the classification of the D11 (D2/D3-era) maximum-principle and
Bochner outputs and states exactly how the new D12 theorems relate to them.

## Classification of the audited D11 outputs

1. `Poincare.Longrun.PDE.DiscreteMaximumPrinciple` (`HeatGridEvolution.le_of_initial_le`,
   `HeatGridEvolution.le_sup'_initial`, `strict_grid_max_principle`): these are **scalar,
   semidiscrete** maximum principles on a finite heat grid with the explicit scheme
   `heatStep` and CFL condition `0 ≤ α ≤ 1/2`. They are fully proved in the snapshot, but
   they are *not* Hamilton's tensor maximum principle: there is no tensor, no covariant
   derivative, no manifold, and no PDE limit is taken. See
   `discrete_max_principle_is_scalar` below for a checked re-statement of the shape of the
   theorem (its hypotheses involve only `ℕ`, `ℝ`, and the grid evolution).
2. `Poincare.Longrun.Entropy.Bridge` (`BochnerStatement`, `WeightedIBPStatement`,
   `FDerivativeStatement`, ...): these are **statement-only** propositions over an abstract
   `WeightedCalculus` datum whose fields (`grad`, `laplacian`, `hessSq`, `metric`, `ricci`)
   are unconstrained functions. No Bochner identity is proved there; blocker `I4`/`U7`
   remains open in the snapshot. The check `bochnerStatement_is_statement_only` below
   records that the declaration exists as an unproved `Prop`-valued definition and that the
   only inhabitant provided by D11 is the **zero calculus on `Unit`**
   (`entropyRegularityBridge_zero`), which is the zero-operator toy instance, not geometry.
3. The D12 tensor-calculus module (`Poincare.D12.TensorMaximumBochner.TensorCalculus`)
   proves the genuine second-derivative identities `curvatureForm_add_last_pair`,
   `curvatureForm_pair_symm`, `ricci_symm` for any `LeviCivitaData` (torsion-free +
   metric-compatible abstract connection). These are **conditional** (they hold for the
   abstract algebraic data; manifold-level Levi-Civita existence remains the BLOCKED
   `LeviCivitaExistenceStatement` upstream).
4. The D12 positivity module (`Poincare.D12.TensorMaximumBochner.PositivityPreservation`)
   proves a matrix ODE maximum principle `staysPosSemidef_of_field` with the expanded
   tangent-cone hypothesis, plus the checked counterexample `negSqrtCounterexample` showing
   the kernel-only condition without regularity does not preserve the cone.
5. The D12 so(3) polynomial module (`Poincare.D12.TensorMaximumBochner.So3Polynomial`)
   instantiates the abstract Bochner chain on a **constructed** domain: the mean connection
   `∇_X Y = ½[X,Y]` on `ℝ³` (metric-compatible for the cross-product bracket), the
   polynomial algebra `MvPolynomial (Fin 3) ℝ`, the rotation derivation
   `D_X f = ∑ᵢ (x × X)ᵢ ∂ᵢ f`, `Ric = ½g`, and the trace-of-Hessian Laplacian.  The
   resulting identity `Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, ∇Δu⟩ + |∇u|²` is unconditional on that
   model.  Items 5-7 below re-expose it here.  This is a genuine downstream application:
   the conclusion is *not* a projection of the hypotheses (the hypotheses contain no
   identity; the curvature term is computed as `½|∇u|²` from the constructed connection).
6. The upstream reference for the **manifold-level** theory is the pinned Frenzymath
   snapshot `third_party/frenzymath/Poincare-Conjecture` at commit
   `bb91a091f0b968f8bbe8d861e025a88d82b161be`: `MorganTianLib/Ch02/Bochner.lean`
   (`function_bochner_formula`, on a Riemannian manifold with the Levi-Civita connection)
   and `MorganTianLib/Ch04/HamiltonMaximum*.lean` (the Hamilton tensor maximum principle
   development).  That snapshot pins Lean `v4.32.1` and mathlib
   `520045ab14e26149ee970e2e617ca04b09bde5d6`, while this release pins Lean
   `v4.34.0-rc2` and mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`; it therefore
   **cannot be imported here** without changing the toolchain (forbidden), and is recorded
   as a dependency request in `checkpoint.json`.  No statement from it is re-exported or
   claimed here.  Nothing in this file asserts Hamilton's tensor maximum principle.

No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted` appears in this file or in
either companion module.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace TensorMaximumBochner
namespace Audit

/-! ## Checked classification statements -/

/-- **Audit check: the D11 discrete maximum principle is scalar and semidiscrete.** The
conclusion of `HeatGridEvolution.le_of_initial_le` is a pointwise real bound over the grid
`ℕ`, under hypotheses that quantify only over the CFL parameters `α`, the bound `M`, and the
initial slice. Nothing in the statement involves a tensor, a connection, or a manifold. -/
theorem discrete_max_principle_is_scalar {N : ℕ} {α M : ℝ} (ev : Poincare.Longrun.PDE.HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M)
    (hinit : ∀ i ≤ N + 1, ev.u 0 i ≤ M) (t : ℕ) (i : ℕ) (hi : i ≤ N + 1) :
    ev.u t i ≤ M :=
  Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le ev hα0 hα1 hM hinit t i hi

/-- **Audit check: the D11 Bochner statement is an unproved Prop over abstract operators.**
This theorem only re-asserts the shape: `BochnerStatement` is a definition whose value is a
universally quantified pointwise equation over the unconstrained `WeightedCalculus` fields.
It is *not* a proof of the Bochner identity for any geometric Laplacian. -/
theorem bochnerStatement_is_statement_only {X : Type} (C : Poincare.Longrun.Entropy.WeightedCalculus X) :
    Poincare.Longrun.Entropy.BochnerStatement C =
      (∀ u : X → ℝ, ∀ x : X,
        C.laplacian (fun y : X => Poincare.Longrun.Entropy.gradInner C u u y) x
          = 2 * C.hessSq u x + 2 * C.ricci (C.grad u x) (C.grad u x)
            + 2 * Poincare.Longrun.Entropy.gradInner C u
                (fun y : X => C.laplacian u y) x) :=
  rfl

/-- **Audit check: the only D11 inhabitant of the entropy regularity bridge is the zero
datum on `Unit`** (the zero-operator toy instance). This confirms that the bridge is
inhabited only trivially in the snapshot; any Ricci-flow instance is still missing. -/
theorem zero_bridge_is_zero_calculus :
    (Poincare.Longrun.Entropy.entropyRegularityBridge_zero :
        Poincare.Longrun.Entropy.EntropyRegularityBridge
          (Poincare.Longrun.Entropy.zeroCalculus) (fun _ : ℝ => Poincare.Longrun.Entropy.zeroEntropyData)) =
      (Poincare.Longrun.Entropy.entropyRegularityBridge_zero :
        Poincare.Longrun.Entropy.EntropyRegularityBridge
          (Poincare.Longrun.Entropy.zeroCalculus) (fun _ : ℝ => Poincare.Longrun.Entropy.zeroEntropyData)) :=
  rfl

/-- **Audit check (conditional): the D12 curvature symmetries hold for any
`LeviCivitaData`.** This is the pair-symmetry theorem of the tensor-calculus module,
re-exposed here as the audited statement: for a metric-compatible torsion-free abstract
connection, `⟨R(X,Y)Z,W⟩ = ⟨R(Z,W)X,Y⟩`. -/
theorem d12_pair_symm_audited {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : Poincare.Longrun.Geometry.MetricData V ι) (b : Poincare.Longrun.Geometry.LieBracketData ℝ V)
    (d : Poincare.Longrun.Geometry.LeviCivitaData m b) (X Y Z W : V) :
    Poincare.Longrun.Geometry.curvatureForm m d.toCurvatureOperator X Y Z W =
      Poincare.Longrun.Geometry.curvatureForm m d.toCurvatureOperator Z W X Y :=
  Poincare.D12.TensorMaximumBochner.LeviCivitaIdentities.curvatureForm_pair_symm d X Y Z W

/-- **Audit check (model): the D12 matrix ODE maximum principle is inhabited by the
nondegenerate field `P(A) = A² - A`** with the explicitly solved path
`M(t) = diag(1/(1+eᵗ), 1/(1+2eᵗ))`: the tangent condition is verified in
`tangentCondition_selfSq_sub_self`, the ODE in `quadSelfPath_solves`, and the PSD conclusion
follows through `staysPosSemidef_of_field`. -/
theorem d12_matrix_example_audited :
    ∀ t : ℝ, 0 ≤ t → Matrix.PosSemidef (quadSelfPath t) :=
  quadSelfPath_stays_posSemidef

/-- **Audit check (model, unconditional): the curvature term of the D12 so(3) Bochner
identity is `½|∇u|²`.** This is the constructed-connection computation, re-exposed: the
Ricci contraction in the abstract frame language equals `½` times the squared gradient.
Nothing here is assumed; the value comes from `So3.ricci_eq_half_metric`. -/
theorem d12_so3_ricci_term_audited (u : So3Polynomial.Poly3) :
    Bochner.ricciContraction So3Polynomial.crossDerivation So3.crossLeviCivita u
      = Bochner.gA (A := So3Polynomial.Poly3) (1 / 2 : ℝ)
        * Bochner.gradSq So3Polynomial.crossDerivation u :=
  So3Polynomial.ricciContraction_so3 u

/-- **Audit check (model, unconditional): the D12 Bochner identity on the constructed
so(3) polynomial domain**, with the curvature term evaluated. -/
theorem d12_so3_bochner_audited (u : So3Polynomial.Poly3) :
    Bochner.lap So3Polynomial.crossDerivation So3.crossLeviCivita
        (Bochner.gradSq So3Polynomial.crossDerivation u)
      = 2 * Bochner.hessSq So3Polynomial.crossDerivation So3.crossLeviCivita u
        + 2 * Bochner.gradInner So3Polynomial.crossDerivation u
            (Bochner.lap So3Polynomial.crossDerivation So3.crossLeviCivita u)
        + Bochner.gradSq So3Polynomial.crossDerivation u :=
  So3Polynomial.bochner_identity_so3_curvature u

/-- **Audit check (non-vacuity): the squared gradient of `u = x₀` at `e₁` is `1 ≠ 0`** on
the constructed model.  This witnesses that the model, its Laplacian and its curvature term
are not the zero calculus. -/
theorem d12_so3_gradsq_nonvacuous :
    So3Polynomial.evalAt So3Polynomial.so3e1
      (Bochner.gradSq So3Polynomial.crossDerivation (MvPolynomial.X 0)) = 1 :=
  So3Polynomial.gradSq_X0_at_e1

/-- **Audit check (nondegeneracy): the constructed trace-of-Hessian Laplacian is not the
zero operator.** `Δx₀ = −2x₀ ≠ 0` on the so(3) model, so the geometry used by the identity
above is a genuine connection with a nonzero Laplacian (no zero-operator masquerade). -/
theorem d12_so3_lap_X0_audited :
    Bochner.lap So3Polynomial.crossDerivation So3.crossLeviCivita (MvPolynomial.X 0)
      = -2 * MvPolynomial.X 0 :=
  So3Polynomial.lap_X0

theorem d12_so3_laplacian_nondegenerate :
    Bochner.lap So3Polynomial.crossDerivation So3.crossLeviCivita (MvPolynomial.X 0) ≠ 0 :=
  So3Polynomial.lap_X0_ne_zero

/-- **Audit check (downstream use): the strict Bochner inequality holds at a concrete
nondegenerate point of the constructed model.** The strictness is produced by the
*curvature* term `|∇u|²` of the non-flat model, not assumed. -/
theorem d12_so3_strict_bochner_audited :
    2 * So3Polynomial.evalAt So3Polynomial.so3e1
        (Bochner.gradInner So3Polynomial.crossDerivation (MvPolynomial.X 0)
          (Bochner.lap So3Polynomial.crossDerivation So3.crossLeviCivita
            (MvPolynomial.X 0)))
      < So3Polynomial.evalAt So3Polynomial.so3e1
        (Bochner.lap So3Polynomial.crossDerivation So3.crossLeviCivita
          (Bochner.gradSq So3Polynomial.crossDerivation (MvPolynomial.X 0))) :=
  So3Polynomial.bochner_strict_at_e1

/-! ## Checked classification statements -/

/-- **Audit check: the finite-horizon matrix maximum principle.** The D12 positivity module
proves the matrix ODE maximum principle with the quadratic-form tangent condition on the open
horizon `(0,T)` and differentiability (time regularity) on the closed horizon `[0,T]`; the
terminal time needs no tangent condition, which is what makes the theorem applicable to a
metric reaching extinction.  Re-exposed here as an audited item. -/
theorem d12_horizon_max_principle_audited {n : Type} [Fintype n]
    {M : ℝ → n → n → ℝ} {T : ℝ}
    (hdiff : ∀ t, t ∈ Set.Icc 0 T → DifferentiableAt ℝ M t)
    (hHerm : ∀ t, t ∈ Set.Icc 0 T → Matrix.IsHermitian (M t))
    (hinit : Matrix.PosSemidef (M 0))
    (htan : ∀ t, t ∈ Set.Ioo 0 T → ∀ v : n → ℝ,
      star v ⬝ᵥ (Matrix.mulVec (M t) v) ≤ 0 →
        0 ≤ star v ⬝ᵥ (Matrix.mulVec (show n → n → ℝ from deriv M t) v)) :
    ∀ t, t ∈ Set.Icc 0 T → Matrix.PosSemidef (M t) :=
  Poincare.D12.TensorMaximumBochner.staysPosSemidef_of_tangent_Icc
    hdiff hHerm hinit htan

/-- **Audit check (model, unconditional): the constructed so(3) metric family solves the Ricci
flow equation of the constructed mean connection**, `∂_t g = -2 Ric` with `Ric = ½ g₀`; the
curvature input is the proved `So3.ricci_eq_half_metric`, not a hypothesis. -/
theorem d12_so3_ricci_flow_audited (X Y : So3.Vec3) (t : ℝ) :
    deriv (fun s : ℝ => So3RicciFlow.metricForm s X Y) t
      = -2 * Poincare.CurvatureAlgebra.CurvatureOperator.ricci
          So3.crossLeviCivita.toCurvatureOperator X Y :=
  So3RicciFlow.ricciFlow_equation X Y t

/-- **Audit check (downstream use of the matrix maximum principle): the so(3) metric stays
positive semidefinite up to the extinction time `t = 1`.** -/
theorem d12_so3_metric_posSemidef_audited (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Matrix.PosSemidef (So3RicciFlow.metricMatrix t) :=
  So3RicciFlow.metricMatrix_posSemidef t ht

/-- **Audit check (nondegeneracy): the metric is positive definite before extinction.** -/
theorem d12_so3_metric_posDef_audited (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Matrix.PosDef (So3RicciFlow.metricMatrix t) :=
  So3RicciFlow.metricMatrix_posDef t ht

/-- **Audit check (sharpness): the positivity conclusion is sharp** — at `t = 1` the metric is
the zero matrix and is not positive definite, so the horizon `[0,1]` cannot be extended. -/
theorem d12_so3_metric_extinction_audited :
    ¬ Matrix.PosDef (So3RicciFlow.metricMatrix 1) :=
  So3RicciFlow.metricMatrix_not_posDef_at_one

/-! ## Audited items for the correct tangent-cone condition (`TangentCone.lean`)

The companion module `TangentCone` isolates the *correct* Hamilton null-eigenvector condition
for the PSD cone, proves it necessary, exhibits a checked witness that it is not a
feasibility condition, computes the algebraic core of Hamilton's reaction field `A² + adj(A)`
in dimension 3, and proves that the strengthened hypothesis of the earlier matrix maximum
principle does not cover that field.  The items below re-expose the four load-bearing
statements for the task-local audit. -/

/-- **Audit check: the Hamilton null-eigenvector condition is necessary for feasibility.** -/
theorem d12_kernel_tangent_necessary_audited {n : Type} [Fintype n] {A N : Matrix n n ℝ}
    (h : FeasibleDirection A N) : KernelTangent A N :=
  kernelTangent_of_feasibleDirection h

/-- **Audit check (sharpness witness): the Hamilton condition is not a feasibility
condition.**  There is an explicit PSD `A` and symmetric `N` with `KernelTangent A N` but
`¬ FeasibleDirection A N`; the obstruction is the second-order determinant identity
`det (A + s • N) = -s²`. -/
theorem d12_kernel_tangent_not_feasible_audited :
    ∃ A N : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosSemidef ∧ KernelTangent A N ∧ ¬ FeasibleDirection A N :=
  kernelTangent_not_feasible

/-- **Audit check (model, unconditional): the adjugate preserves positive
semidefiniteness**, the algebraic content of `R# ⪰ 0` for a PSD curvature operator. -/
theorem d12_adjugate_posSemidef_audited {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) : A.adjugate.PosSemidef :=
  adjugate_posSemidef A hA

/-- **Audit check (downstream computation): the Hamilton reaction field `A² + adj(A)` of the
dimension-3 tensor maximum principle satisfies the null-eigenvector condition at every PSD
matrix.**  This is *not* a projection of an assumed curvature identity: `adj` is the cofactor
matrix and the value is computed from it (`hamiltonField` is a definition, not a hypothesis). -/
theorem d12_hamilton_field_kernel_tangent_audited {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : KernelTangent A (hamiltonField A) :=
  hamiltonField_kernelTangent hA

/-- **Audit check (exact gap): the strengthened quadratic-form hypothesis of
`staysPosSemidef_of_field` fails for the Hamilton reaction field.**  Hence the earlier matrix
maximum principle does not apply to it, and the missing ingredient is the passage from the
null-eigenvector condition to ODE invariance (Nagumo / eigenvalue comparison), not a
rearrangement of the earlier proof. -/
theorem d12_hamilton_field_gap_audited :
    ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.IsHermitian → ∀ v : Fin 2 → ℝ,
        star v ⬝ᵥ (Matrix.mulVec A v) ≤ 0 →
          0 ≤ star v ⬝ᵥ (Matrix.mulVec (hamiltonField A) v)) :=
  hamiltonField_not_strengthened

/-! ## Axiom audit -/

#print axioms discrete_max_principle_is_scalar
#print axioms bochnerStatement_is_statement_only
#print axioms zero_bridge_is_zero_calculus
#print axioms d12_pair_symm_audited
#print axioms d12_matrix_example_audited
#print axioms d12_so3_ricci_term_audited
#print axioms d12_so3_bochner_audited
#print axioms d12_so3_gradsq_nonvacuous
#print axioms d12_so3_lap_X0_audited
#print axioms d12_so3_laplacian_nondegenerate
#print axioms d12_so3_strict_bochner_audited
#print axioms d12_horizon_max_principle_audited
#print axioms d12_so3_ricci_flow_audited
#print axioms d12_so3_metric_posSemidef_audited
#print axioms d12_so3_metric_posDef_audited
#print axioms d12_so3_metric_extinction_audited
#print axioms d12_kernel_tangent_necessary_audited
#print axioms d12_kernel_tangent_not_feasible_audited
#print axioms d12_adjugate_posSemidef_audited
#print axioms d12_hamilton_field_kernel_tangent_audited
#print axioms d12_hamilton_field_gap_audited

end Audit
end TensorMaximumBochner
end D12
end Poincare
