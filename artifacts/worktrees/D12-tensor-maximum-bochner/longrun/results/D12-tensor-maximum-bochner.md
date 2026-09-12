# D12-tensor-maximum-bochner — result card (invocation 7)

**Status: in progress (checkpoint, invocation 7 of ≤24; elapsed ≈ 10.4 h of the 72 h cap).**
Terminal marker at the bottom: `TASK_BLOCKED` — the intended *full* objective (the correct
tangent-cone condition carried all the way to ODE invariance, and Hamilton's tensor maximum
principle on manifolds) is **not** proved; the card reports the exact missing statement, the
proved partial lemmas, and fresh audited evidence. No claim here says Perelman is proved.

## 1. What is new in this invocation: the *correct* tangent-cone condition

New module `release/Poincare/D12/TensorMaximumBochner/TangentCone.lean` (21 declarations,
`lake env lean` exit 0, no errors, no warnings, no `sorry`). It separates three notions:

| name | statement | status |
|---|---|---|
| `KernelTangent A N` | `∀ v, A *ᵥ v = 0 → 0 ≤ star v ⬝ᵥ (N *ᵥ v)` — Hamilton's null-eigenvector condition, i.e. `N` lies in the (closed) tangent cone of the PSD cone at `A` | definition |
| `FeasibleDirection A N` | `∃ ε > 0, ∀ s ∈ Icc 0 ε, (A + s • N).PosSemidef` — the genuine first-order perturbation cone | definition |
| `StrictKernelTangent A N` | `∃ c > 0, ∀ v, A *ᵥ v = 0 → c * (star v ⬝ᵥ v) ≤ star v ⬝ᵥ (N *ᵥ v)` | definition |

### Full statements of the load-bearing new results (all proved, axiom-clean)

```lean
theorem kernelTangent_of_feasibleDirection {n : Type*} [Fintype n] {A N : Matrix n n ℝ}
    (h : FeasibleDirection A N) : KernelTangent A N

theorem kernelTangent_of_posSemidef_path {n : Type*} [Fintype n] {M : ℝ → Matrix n n ℝ}
    {A N : Matrix n n ℝ} {ε : ℝ} (hε : 0 < ε)
    (hpsd : ∀ t ∈ Set.Icc 0 ε, (M t).PosSemidef)
    (hM0 : M 0 = A)
    (hderiv : ∀ v : n → ℝ,
      HasDerivAt (fun t => star v ⬝ᵥ (M t *ᵥ v)) (star v ⬝ᵥ (N *ᵥ v)) 0) :
    KernelTangent A N

theorem counterexample_kernelTangent : KernelTangent counterexampleA counterexampleN
theorem counterexample_not_feasible : ¬ FeasibleDirection counterexampleA counterexampleN

theorem kernelTangent_not_feasible :
    ∃ A N : Matrix (Fin 2) (Fin 2) ℝ,
      A.PosSemidef ∧ KernelTangent A N ∧ ¬ FeasibleDirection A N

theorem adjugate_eq_det_smul_inv {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (h : IsUnit A.det) : A.adjugate = A.det • A⁻¹

theorem adjugate_posSemidef {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : A.adjugate.PosSemidef

noncomputable def hamiltonField {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ := A ^ 2 + A.adjugate

lemma dotProduct_mulVec_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (v : n → ℝ) :
    star v ⬝ᵥ (Matrix.mulVec (A ^ 2) v) = star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)

theorem hamiltonField_kernelTangent {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : KernelTangent A (hamiltonField A)

theorem hamiltonField_not_strengthened :
    ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.IsHermitian → ∀ v : Fin 2 → ℝ,
        star v ⬝ᵥ (Matrix.mulVec A v) ≤ 0 →
          0 ≤ star v ⬝ᵥ (Matrix.mulVec (hamiltonField A) v))

theorem hamiltonField_kernel_witness :
    star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
      (hamiltonField (!![(1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = 1

theorem counterexample_nondegenerate :
    counterexampleA 0 0 = 0 ∧ counterexampleA 1 1 = 1 ∧ counterexampleN 0 1 = 1 ∧
      counterexampleA *ᵥ (![1, 0] : Fin 2 → ℝ) = 0
```

### Expanded hypotheses and why each is needed

* `kernelTangent_of_feasibleDirection`: the hypothesis is exactly feasibility
  `∃ ε > 0, ∀ s ∈ [0,ε], (A + s • N).PosSemidef`; the proof evaluates at `s = ε/2 > 0` and uses
  `Matrix.PosSemidef.dotProduct_mulVec_nonneg` plus `Av = 0`. No regularity, no symmetry, no
  boundedness is assumed — the conclusion is the first-variation inequality. **This proves the
  Hamilton condition is necessary, so it cannot be weakened.**
* `kernelTangent_of_posSemidef_path`: the time regularity is stated *explicitly and per
  vector*: for every `v`, the scalar path `t ↦ vᵀ M(t) v` has right derivative `vᵀ N v` at `0`
  (`HasDerivAt`). The PSD hypothesis is imposed on the closed interval `[0,ε]`; the boundary
  minimum argument (`HasDerivAt.tendsto_slope_zero_right`) is what needs the regularity. No
  differentiability of the whole matrix path is assumed. (Deriving the per-vector hypothesis
  from `HasDerivAt M N 0` is a routine chain rule; it is *not* used, so nothing circular is
  smuggled in.)
* `counterexample_*`: `A = !![0,0;0,1]` (PSD, kernel spanned by `e₁`), `N = !![0,1;1,-1]`
  (nonzero symmetric). `KernelTangent` holds since `v₁ = 0` forces `vᵀNv = 0`; and
  `det (A + s•N) = -s²` for every `s`, so `A + s•N` is never PSD for `s ≠ 0`
  (`Matrix.PosSemidef.det_nonneg`). The obstruction is exactly second order.
* `adjugate_posSemidef`: for `ε > 0`, `A + ε•1` is `PosDef`, `adj = det • (·)⁻¹` with both
  factors nonnegative, and `ε ↓ 0` is taken with `Continuous.matrix_adjugate` and
  `ge_of_tendsto` along `𝓝[>] 0`. No eigenvalue theory is used.
* `hamiltonField_not_strengthened`: the *strengthened* hypothesis of
  `PositivityPreservation.staysPosSemidef_of_field` (an all-Hermitian-matrix hypothesis) fails
  for `A = !![(-1),0;0,0]`, `v = ![0,1]`: `vᵀAv = 0 ≤ 0` but `vᵀ(A²+adj A)v = -1 < 0`.

## 2. Meaning: the correct tangent-cone condition, and the exact gap

* The Hamilton null-eigenvector condition is **necessary** (proved) and it is in fact the
  exact condition for membership in the *closed* tangent cone `T_{PSD}(A)`.
* It is **not** a first-order feasibility condition: the checked witness shows that
  `KernelTangent A N` does not imply `A + s•N ⪰ 0` for any `s > 0`. Therefore the classical
  passage from the null-eigenvector condition to invariance is genuinely a Nagumo /
  min-eigenvalue-comparison argument, **not** a rearrangement of the strengthened-condition
  proof of invocations 1–6, and **not** something obtainable by perturbation inside the cone.
  `hamiltonField_not_strengthened` shows the earlier theorem does not apply to Hamilton's field
  at all.
* The *missing statement* (recorded as blocker `B1` below) is the invariance theorem: for a
  locally Lipschitz (or continuous) field `P` with `A ⪰ 0 → KernelTangent A (P A)`, every
  solution of `M' = P(M)` with `M(0) ⪰ 0` stays PSD. The natural formalisation route (known to
  be available in the pinned mathlib) is the min-eigenvalue/Danskin comparison lemma
  `D⁺λ_min(M(t)) ≥ min {vᵀP(M(t))v : ‖v‖ = 1, M(t)v = λ_min(M(t)) v}` together with a
  first-exit argument. **This is not assumed anywhere.**

## 3. Hamilton's reaction field in dimension 3 (downstream, not a projection)

`hamiltonField A = A² + adj(A)` is the matrix form of `R² + R#` under the Hodge-star
identification `Λ²ℝ³ ≅ ℝ³` (for `A = diag(λ₁,λ₂,λ₃)`, `adj(A) = diag(λ₂λ₃, λ₁λ₃, λ₁λ₂)`, which
is exactly the action of `Λ²A` on `e₂∧e₃, e₁∧e₃, e₁∧e₂`). Two facts are proved:

* `adjugate_posSemidef` — the algebraic content of “`R#` is nonnegative on the PSD cone”;
* `hamiltonField_kernelTangent` — `A ⪰ 0 ⟹ KernelTangent A (A² + adj A)`, i.e. the
  null-eigenvector condition holds for the genuine reaction field, with the value on the kernel
  coming from the cofactor expansion (witness: at `A = diag(1,0)`, `v = e₂`, the form equals
  `1 > 0`; the `A²` part contributes `0`).

The conclusion is computed from a definition (`hamiltonField`), not projected from a hypothesis
about curvature. What is **not** claimed: invariance of the PSD cone under this field
(`A(t) ⪰ 0` for all `t`), Hamilton's tensor maximum principle on a manifold, or the curvature
evolution equation `∂_t R = ΔR + R² + R#`.

## 4. Audit of the D11 maximum-principle / Bochner outputs (classification)

Audited in `Audit.lean` (all re-exposed with `#print axioms`):

* `Poincare.Longrun.PDE.DiscreteMaximumPrinciple` — the D11 maximum principle is **scalar and
  semidiscrete** (finite heat grid, explicit scheme, CFL `0 ≤ α ≤ 1/2`); it is *not* Hamilton's
  tensor maximum principle (no tensor, no connection, no manifold, no PDE limit).
* `Poincare.Longrun.Entropy.Bridge` — `BochnerStatement` is a **statement-only Prop over
  unconstrained abstract operators**; the only D11 inhabitant of the bridge is the zero
  calculus on `Unit` (zero-operator toy instance). Blockers I4/U7 remain open upstream.
* The D12 abstract tensor calculus (`TensorCalculus`, `BochnerIdentity`) is **conditional** on
  `LeviCivitaData` (torsion-free + metric-compatible abstract connection) and `DerivationData`
  (Leibniz + bracket compatibility): Hessian symmetry, the first/second-derivative commutators,
  `∇`-metric compatibility for fields, and the assembled Bochner identity
  `Δ|∇u|² = 2|∇∇u|² + 2⟨∇u,∇Δu⟩ + Ric(∇u,∇u)`.
* The constructed `so(3)` model (mean connection `∇_X Y = ½[X,Y]`, cross-product bracket,
  polynomial algebra, trace-of-Hessian Laplacian, proved `Ric = ½g`) makes the Bochner identity
  **unconditional on that model** with curvature term `½|∇u|²`, and the metric path
  `g(t) = (1-t)g₀` solves `∂_t g = -2 Ric` with PSD Gram matrix up to extinction at `t = 1`.
* Manifold-level **Hamilton tensor maximum principle is still out of scope**; no such statement
  is asserted.

## 5. Fresh verification evidence

All commands run with `cwd = release/` (Lean `v4.34.0-rc2`, mathlib rev
`7974e751bece493b6ff508039423ca9fa2452fa8`, pinned by `release/lake-manifest.json`).

| command | exit | evidence |
|---|---|---|
| `lake env lean Poincare/D12/TensorMaximumBochner/TangentCone.lean` | 0 | `scratch/tc_final.log` (0 errors, 0 warnings) |
| `lake env lean Poincare/D12/TensorMaximumBochner/Audit.lean` | 0 | `scratch/audit_lean_final.log` (0 errors, 0 warnings) |
| `lake build Poincare.D12.TensorMaximumBochner.Audit` | 0 | `scratch/build_tc2.log` — `Build completed successfully (8897 jobs).` |
| `python3 tools/d12_axiom_audit.py` | 0 | `scratch/audit_inv7b.log` — `AXIOM AUDIT PASS`; coverage 222/222 declarations over 8 files; forbidden-token scan clean; negative control flags a fake axiom |

Axiom evidence: every declaration of the eight task files is covered by a `#print axioms` line
(fail-closed coverage check) and every line reports only
`{propext, Classical.choice, Quot.sound}`. Coverage for `TangentCone.lean` is 21/21.
No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, or `proof_wanted` occurs in any
authored file.

Fresh source hashes (sha256):

| file | sha256 |
|---|---|
| `release/Poincare/D12/TensorMaximumBochner/TangentCone.lean` | `f2f51efa216b9c7ac7fdc35627f7689e66a3a1faf71cd79b9b212e61682ea0ea` |
| `release/Poincare/D12/TensorMaximumBochner/Audit.lean` | `2f88170f696cb0b183f34df0ac9300d088b04ca96dd61c52be49b873244db9e3` |
| `release/Poincare/D12/TensorMaximumBochner/PositivityPreservation.lean` | `9dfeb301fab4606ef158ae67643458d1df2ac2e0579c6b0f53c39c5ad338da2f` |
| `release/Poincare/D12/TensorMaximumBochner/BochnerIdentity.lean` | `20be805c924d6f43685b68ad8a3e7ee29c2a8fb3f049dd3e3e6db6a9d09624e9` |
| `release/Poincare/D12/TensorMaximumBochner/TensorCalculus.lean` | `cd135ae56b41a5afc1d60d27557dff763144563a4fa5d749465ddef685e755de` |
| `release/Poincare/D12/TensorMaximumBochner/So3Model.lean` | `b45ac089a9a20ea9b25387b361a6036631a2517c92e4b3c004834fd140009cb2` |
| `release/Poincare/D12/TensorMaximumBochner/So3Polynomial.lean` | `8db737efc39ec979f73df024f1a0b90d45b7ac68740b955853a9db8472836848` |
| `release/Poincare/D12/TensorMaximumBochner/So3RicciFlow.lean` | `075fc20f8c2b96076369921535d8baedb87fc24752eac8b8f2ba7925d6f5b908` |
| `tools/d12_axiom_audit.py` | `85784e63d48a42744180db40d824e35841e2dc1528d80dff044b3692f577c522` |

Coverage gap fixed in this invocation: 9 declarations of `So3Model.lean` / `So3Polynomial.lean`
that the invocation-6 fail-closed coverage check flagged now have `#print axioms` lines, and
`TangentCone.lean` was registered in `tools/d12_axiom_audit.py` (both FILES and the
expected-declaration table).

## 6. Blockers

**Closed (this invocation).**

* `C1` — *Is the strengthened quadratic-form hypothesis the correct tangent-cone condition?*
  Answered: it is **strictly stronger** than Hamilton's condition, and it fails for the genuine
  Hamilton reaction field (`hamiltonField_not_strengthened`). The correct condition is
  `KernelTangent`, which is **necessary** (`kernelTangent_of_feasibleDirection`, path form
  `kernelTangent_of_posSemidef_path`). This is a genuine mathematical sharpening with an
  explicit checked witness (`kernelTangent_not_feasible`).
* `C2` — *Is the Hamilton reaction field's algebraic core available?* Yes:
  `adjugate_posSemidef` + `hamiltonField_kernelTangent` (dimension-3 `R# ↔ adj` identification
  documented; no eigenvalue theory needed).
* `C3` — *Fail-closed axiom-audit coverage gap from invocation 6.* Closed; audit now passes
  222/222 with no exemption list.

**Remaining (exact statements; not assumed anywhere).**

* `B1` (**the** mathematical blocker) — invariance of the PSD cone under the *correct*
  condition. Exact missing statement: for `n` finite, `P : Matrix n n ℝ → Matrix n n ℝ`
  continuous (or locally Lipschitz) with `∀ A, A.PosSemidef → KernelTangent A (P A)`, every
  differentiable `M : ℝ → Matrix n n ℝ` with `∀ t ≥ 0, deriv M t = P (M t)` and `M 0 ⪰ 0`
  satisfies `∀ t ≥ 0, (M t).PosSemidef`. The proof needs the min-eigenvalue comparison
  (Danskin) lemma plus a first-exit argument; mathlib has `Matrix.IsHermitian.eigenvalues` /
  `eigenvectorBasis` / the spectral theorem in the pinned revision, so this is a formalisation
  task, not a missing-mathematics task.
* `B2` — manifold-level Levi-Civita existence (upstream `LeviCivitaExistenceStatement`): still
  BLOCKED in general; closed here only for the metric-skew mean connection on the `so(3)`
  model. Hamilton's tensor maximum principle on manifolds (curvature-operator bundle,
  Uhlenbeck trick, `∂_t R = ΔR + R² + R#`) is not formalised.

## 7. Dependency requests

* No new imports are required for the proved material.
* For `B1`: reuse the pinned mathlib spectral machinery
  (`Mathlib/Analysis/Matrix/Spectrum.lean`, `Mathlib/Analysis/Matrix/PosDef.lean`) — no external
  package needed.
* Port of `MorganTianLib.Ch02.Bochner` / `Ch04.HamiltonMaximumCore` (frenzymath snapshot
  `bb91a091f0b968f8bbe8d861e025a88d82b161be`) remains toolchain-blocked: that snapshot pins
  Lean `v4.32.1` / mathlib `520045ab…`, while this release is pinned at Lean `v4.34.0-rc2` /
  mathlib `7974e751…`; changing the toolchain is forbidden by the task rules.

## 8. Honest terminal assessment

The invocation-level milestones (exact target, dependency search, compiling lemmas, a useful
nontrivial lemma with full type, a downstream application not obtained by projection, fresh
fail-closed audit) hold and are reproducible from the hashes above. The **full** task objective
— the correct tangent-cone condition carried to ODE invariance, and Hamilton's tensor maximum
principle on manifolds — is **not** achieved. Hence this card is a partial-results/blocked
report with the exact missing statement `B1`, its mathematical content identified (Nagumo /
min-eigenvalue comparison), and the concrete formalisation route recorded.

TASK_BLOCKED
