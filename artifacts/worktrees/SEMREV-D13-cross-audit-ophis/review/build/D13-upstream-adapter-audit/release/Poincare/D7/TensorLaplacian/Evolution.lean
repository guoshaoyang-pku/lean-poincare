import Poincare.D7.TensorLaplacian.Basic
import Poincare.D7.RicciScalar.Variation

/-!
# Poincare.D7.TensorLaplacian.Evolution

**D7 tensor Laplacian layer, part 3: the scalar-curvature evolution identity
`∂ₜ scal = Δ scal + 2 |Ric|²` as an exact identity between interface fields, under the stated
Ricci-flow equation `∂ₜ g = -2 Ric`.**

This module builds on the D7 `RiemannCurvatureData` (the connection layer) and the scalar
variation interface of `Poincare.D7.RicciScalar.Variation`.

## Interface fields

For a connection datum `D : RiemannCurvatureData V ι` with orthonormal frame `eᵢ` and a stated
metric velocity `h : V → V → ℝ`:

* `ricciNormSq D = ∑ᵢ ∑ⱼ Ric(eᵢ,eⱼ)²` — the **Frobenius norm squared `|Ric|²`** in the
  orthonormal frame (concrete, defined over the D7 layer);
* `traceH D h = ∑ᵢ h(eᵢ,eᵢ)` — the trace of the velocity;
* `pairingH D h = ∑ᵢ ∑ⱼ h(eᵢ,eⱼ) Ric(eᵢ,eⱼ)` — the pairing `⟨h, Ric⟩`;
* `ricciFlowVelocity D = -2 Ric` — the Ricci-flow velocity.

## The identity

`ScalarEvolutionCertificate D h` carries the interface fields `scalPath`, `scalDeriv`
(`∂ₜ scal`), `lapScal` (`Δ scal`) and `divdivH` (`∇ⁱ∇ʲhᵢⱼ`), together with

* `velocity` — **the stated flow equation** `h = -2 Ric`;
* `flow` — `scalDeriv` is the time derivative of `scalPath`;
* `variation` — the Lichnerowicz trace variation
  `∂ₜ scal = -Δ(tr h) + ∇ⁱ∇ʲhᵢⱼ - ⟨h, Ric⟩` (the analytic input; its construction is blocked at
  the manifold level, see `Poincare.D7.TensorLaplacian.Blocked`);
* `bianchi` — the contracted Bianchi identity `∇ⁱ∇ʲhᵢⱼ = -Δ scal` for `h = -2 Ric`;
* `anchor` — `scalPath 0 = D.scalarCurvature`.

From these, and only from these, the module proves

* `traceH_eq : traceH D h = -2 * scal` (from `h = -2 Ric` and the D7 basis trace);
* `pairingH_eq : pairingH D h = -2 * ricciNormSq D` (from `h = -2 Ric`);
* `scalarDeriv_eq : ∂ₜ scal = Δ scal + 2 |Ric|²` — **the identity between the interface
  fields**;
* `scalar_evolution : HasDerivAt scalPath (lapScal t + 2 * ricciNormSq D) t` — the same identity
  as a derivative statement.

The algebraic chain is the classical one:
`2ΔR - ΔR + 2|Ric|² = ΔR + 2|Ric|²`.

## Honest boundary

The variation formula and the contracted Bianchi identity are **stated certificates**, not
theorems of this layer: they are exactly the manifold-level inputs that the D7 algebraic model
does not provide. The conclusion is therefore an identity between the interface fields *under*
those certificates. The state-only smooth statement is
`Poincare.D7.TensorLaplacian.Blocked.SmoothScalarEvolutionStatement`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Poincare
namespace D7
namespace TensorLaplacian

universe v w

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## The D7 quantities of the evolution identity -/

/-- **The Frobenius norm squared `|Ric|²` of the Ricci form** in the orthonormal frame:
`∑ᵢ ∑ⱼ Ric(eᵢ,eⱼ)²`. -/
noncomputable def ricciNormSq (D : RiemannCurvatureData V ι) : ℝ :=
  ∑ i : ι, ∑ j : ι, D.ricciForm (D.metric.basis i) (D.metric.basis j)
    * D.ricciForm (D.metric.basis i) (D.metric.basis j)

/-- `|Ric|² ≥ 0`: it is a sum of squares. -/
theorem ricciNormSq_nonneg (D : RiemannCurvatureData V ι) : 0 ≤ ricciNormSq D := by
  unfold ricciNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- **The trace of a metric velocity** `h` in the orthonormal frame: `∑ᵢ h(eᵢ,eᵢ)`. -/
noncomputable def traceH (D : RiemannCurvatureData V ι) (h : V → V → ℝ) : ℝ :=
  ∑ i : ι, h (D.metric.basis i) (D.metric.basis i)

/-- **The pairing `⟨h, Ric⟩`** of a metric velocity with the Ricci form in the orthonormal frame:
`∑ᵢ ∑ⱼ h(eᵢ,eⱼ) Ric(eᵢ,eⱼ)`. -/
noncomputable def pairingH (D : RiemannCurvatureData V ι) (h : V → V → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, h (D.metric.basis i) (D.metric.basis j)
    * D.ricciForm (D.metric.basis i) (D.metric.basis j)

/-- **The Ricci-flow velocity** `∂ₜ g = -2 Ric` at the reference time. -/
noncomputable def ricciFlowVelocity (D : RiemannCurvatureData V ι) : V → V → ℝ :=
  fun X Y => -2 * D.ricciForm X Y

/-- **The stated Ricci-flow equation**: a velocity `h` with `h = -2 Ric`. -/
def IsRicciFlowVelocity (D : RiemannCurvatureData V ι) (h : V → V → ℝ) : Prop :=
  ∀ X Y : V, h X Y = -2 * D.ricciForm X Y

/-- The Ricci-flow velocity satisfies the stated flow equation. -/
theorem isRicciFlowVelocity_ricciFlowVelocity (D : RiemannCurvatureData V ι) :
    IsRicciFlowVelocity D (ricciFlowVelocity D) :=
  fun _ _ => rfl

/-- **The trace of the Ricci-flow velocity is `-2 scal`**: `∑ᵢ (-2 Ric(eᵢ,eᵢ)) = -2 scal`. -/
theorem traceH_ricciFlowVelocity (D : RiemannCurvatureData V ι) :
    traceH D (ricciFlowVelocity D) = -2 * D.scalarCurvature := by
  have hscal : D.scalarCurvature =
      ∑ i : ι, D.ricciForm (D.metric.basis i) (D.metric.basis i) :=
    RiemannCurvatureData.scalarCurvature_eq_sum_basis D
  calc traceH D (ricciFlowVelocity D)
      = ∑ i : ι, -2 * D.ricciForm (D.metric.basis i) (D.metric.basis i) := rfl
    _ = -2 * ∑ i : ι, D.ricciForm (D.metric.basis i) (D.metric.basis i) := by
        rw [Finset.mul_sum]
    _ = -2 * D.scalarCurvature := by rw [hscal]

/-- **The pairing of the Ricci-flow velocity with Ricci is `-2 |Ric|²`**. -/
theorem pairingH_ricciFlowVelocity (D : RiemannCurvatureData V ι) :
    pairingH D (ricciFlowVelocity D) = -2 * ricciNormSq D := by
  unfold pairingH ricciNormSq
  calc ∑ i : ι, ∑ j : ι, (fun X Y : V => -2 * D.ricciForm X Y)
          (D.metric.basis i) (D.metric.basis j) * D.ricciForm (D.metric.basis i) (D.metric.basis j)
      = ∑ i : ι, ∑ j : ι, (-2 * D.ricciForm (D.metric.basis i) (D.metric.basis j))
          * D.ricciForm (D.metric.basis i) (D.metric.basis j) := by
        simp only
    _ = ∑ i : ι, -2 * ∑ j : ι, D.ricciForm (D.metric.basis i) (D.metric.basis j)
          * D.ricciForm (D.metric.basis i) (D.metric.basis j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = -2 * ∑ i : ι, ∑ j : ι, D.ricciForm (D.metric.basis i) (D.metric.basis j)
          * D.ricciForm (D.metric.basis i) (D.metric.basis j) := by
        rw [Finset.mul_sum]

/-! ## The evolution certificate -/

/-- **The scalar-curvature evolution certificate.**

The interface fields are `scalPath` (the scalar curvature along the flow), `scalDeriv` (its time
derivative `∂ₜ scal`), `lapScal` (`Δ scal`) and `divdivH` (`∇ⁱ∇ʲhᵢⱼ`). The remaining fields are
the stated flow equation `h = -2 Ric`, the flow equation on `scalPath`, the Lichnerowicz trace
variation, the contracted Bianchi identity, and the anchor at `t = 0`.

The variation and Bianchi fields are the deep manifold-level inputs; everything else is algebraic.
The main theorem `scalarDeriv_eq` turns them into `∂ₜ scal = Δ scal + 2 |Ric|²`. -/
structure ScalarEvolutionCertificate (D : RiemannCurvatureData V ι) (h : V → V → ℝ) where
  /-- The scalar curvature along the flow. -/
  scalPath : ℝ → ℝ
  /-- The time derivative `∂ₜ scal` as an interface field. -/
  scalDeriv : ℝ → ℝ
  /-- The Laplacian `Δ scal` as an interface field. -/
  lapScal : ℝ → ℝ
  /-- The double divergence `∇ⁱ∇ʲhᵢⱼ` of the velocity as an interface field. -/
  divdivH : ℝ → ℝ
  /-- **The stated flow equation** `h = -2 Ric`. -/
  velocity : IsRicciFlowVelocity D h
  /-- The flow equation for the scalar curvature: `scalDeriv` is `∂ₜ scal`. -/
  flow : ∀ t : ℝ, HasDerivAt scalPath (scalDeriv t) t
  /-- **The Lichnerowicz trace variation**
  `∂ₜ scal = -Δ(tr h) + ∇ⁱ∇ʲhᵢⱼ - ⟨h, Ric⟩`, with `Δ(tr h) = -2 Δ scal`. -/
  variation : ∀ t : ℝ,
    HasDerivAt scalPath (-(-2 * lapScal t) + divdivH t - pairingH D h) t
  /-- **The contracted Bianchi identity** for `h = -2 Ric`: `∇ⁱ∇ʲhᵢⱼ = -Δ scal`. -/
  bianchi : ∀ t : ℝ, divdivH t = - lapScal t
  /-- The anchor: at time `0` the path is the D7 scalar curvature of `D`. -/
  anchor : scalPath 0 = D.scalarCurvature

namespace ScalarEvolutionCertificate

variable {D : RiemannCurvatureData V ι} {h : V → V → ℝ}

/-- **The trace of the velocity is `-2 scal`** for any velocity satisfying the stated Ricci-flow
equation. -/
theorem traceH_eq (C : ScalarEvolutionCertificate D h) : traceH D h = -2 * D.scalarCurvature := by
  have hv : h = ricciFlowVelocity D := by
    funext X Y
    exact C.velocity X Y
  rw [hv, traceH_ricciFlowVelocity]

/-- **The pairing of the velocity with Ricci is `-2 |Ric|²`** for any velocity satisfying the
stated Ricci-flow equation. -/
theorem pairingH_eq (C : ScalarEvolutionCertificate D h) :
    pairingH D h = -2 * ricciNormSq D := by
  have hv : h = ricciFlowVelocity D := by
    funext X Y
    exact C.velocity X Y
  rw [hv, pairingH_ricciFlowVelocity]

/-- **The variation right-hand side reduces to `Δ scal + 2 |Ric|²`** using the trace, pairing and
contracted Bianchi relations. -/
theorem variation_rhs_eq (C : ScalarEvolutionCertificate D h) (t : ℝ) :
    -(-2 * C.lapScal t) + C.divdivH t - pairingH D h = C.lapScal t + 2 * ricciNormSq D := by
  rw [C.pairingH_eq, C.bianchi t]
  ring

/-- **The identity between the interface fields**: `∂ₜ scal = Δ scal + 2 |Ric|²`. -/
theorem scalarDeriv_eq (C : ScalarEvolutionCertificate D h) (t : ℝ) :
    C.scalDeriv t = C.lapScal t + 2 * ricciNormSq D := by
  have h1 : HasDerivAt C.scalPath (C.scalDeriv t) t := C.flow t
  have h2 : HasDerivAt C.scalPath (C.lapScal t + 2 * ricciNormSq D) t := by
    have hv := C.variation t
    rwa [C.variation_rhs_eq t] at hv
  exact h1.unique h2

/-- **The scalar-curvature evolution identity**:
`∂ₜ scal = Δ scal + 2 |Ric|²`, as a derivative statement. -/
theorem scalar_evolution (C : ScalarEvolutionCertificate D h) (t : ℝ) :
    HasDerivAt C.scalPath (C.lapScal t + 2 * ricciNormSq D) t := by
  have h := C.flow t
  rwa [C.scalarDeriv_eq t] at h

/-- **The identity is exact**: the derivative statement `∂ₜ scal = Δ scal + 2 |Ric|²` holds if
and only if the interface fields satisfy `scalDeriv = lapScal + 2 |Ric|²`. -/
theorem scalar_evolution_iff (C : ScalarEvolutionCertificate D h) (t : ℝ) :
    HasDerivAt C.scalPath (C.lapScal t + 2 * ricciNormSq D) t ↔
      C.scalDeriv t = C.lapScal t + 2 * ricciNormSq D := by
  constructor
  · intro hder
    exact (C.flow t).unique hder
  · intro heq
    have h := C.flow t
    rwa [heq] at h

/-- The identity packaged as a `∀ t` statement. -/
theorem scalar_evolution_forall (C : ScalarEvolutionCertificate D h) :
    ∀ t : ℝ, HasDerivAt C.scalPath (C.lapScal t + 2 * ricciNormSq D) t :=
  fun t => C.scalar_evolution t

/-- The scalar curvature at time `0` is the D7 scalar curvature of the datum. -/
theorem scalPath_zero (C : ScalarEvolutionCertificate D h) :
    C.scalPath 0 = D.scalarCurvature := C.anchor

end ScalarEvolutionCertificate

/-! ## The flat sanity check -/

/-- **A static flat certificate**: for a datum with vanishing Ricci form the evolution identity
holds with `scalPath = 0`, `scalDeriv = 0`, `lapScal = 0`, `divdivH = 0`. This shows the
certificate structure is inhabited. -/
noncomputable def flatCertificate (D : RiemannCurvatureData V ι)
    (hRic : ∀ X Y : V, D.ricciForm X Y = 0) (hscal : D.scalarCurvature = 0) :
    ScalarEvolutionCertificate D (fun _ _ => 0) where
  scalPath := fun _ => 0
  scalDeriv := fun _ => 0
  lapScal := fun _ => 0
  divdivH := fun _ => 0
  velocity := fun X Y => by rw [hRic X Y]; ring
  flow := fun t => hasDerivAt_const t 0
  variation := fun t => by
    have hp : pairingH D (fun _ _ => 0) = 0 := by
      unfold pairingH
      simp
    rw [hp]
    simpa using hasDerivAt_const (x := t) (c := 0)
  bianchi := fun t => by simp
  anchor := hscal.symm

end TensorLaplacian
end D7
end Poincare
