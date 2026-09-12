import Poincare.D7.RicciScalar.Product
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Poincare.D7.RicciScalar.Variation

**D7 Ricci/scalar layer, part 4: the variation interface for `d/dt scal(g(t))`.**

This module states — as explicit, unproved `Prop`s with named blockers — the variation of the
scalar curvature along a flow of metric-compatible torsion-free connection data. The two exact
missing dependencies are isolated:

1. **Evolution of the Levi-Civita connection** (`LeviCivitaEvolution`): the connection velocity
   `∂ₜ∇` exists and satisfies the linearized Koszul formula. The formula needs directional
   derivatives `dirh` of the metric-velocity tensor field; that first-order calculus is part of
   the structure, because the abstract algebraic setting has no base points.
2. **Commutation of the time derivative and the trace** (`TraceCommutationStatement`): the
   derivative of the Ricci trace `Ric_t(X,Y) = tr(Z ↦ R_t(Z,X)Y)` is the trace of the derivative
   of the endomorphism. This is stated as the existence of a Ricci velocity `Ricdot`.

What *is* proved here is the reduction `scalarVariation_of_traceCommutation`: once the Ricci
velocity `Ricdot` is supplied (i.e. once `d/dt` commutes with the trace), the scalar variation
`d/dt scal = ∑ᵢ Ricdot(eᵢ,eᵢ)` follows by differentiating the finite orthonormal-frame expansion
of the scalar curvature. The flow equation itself is the stated `MetricFlowEquation` /
`RicciFlowEquation`. The conclusion is `ScalarVariationStatement`.

The curvature velocity `curvVel` (the Leibniz expansion of `∂ₜ R`) and the
`CurvatureEvolutionStatement` are also stated, so that the chain
`Levi-Civita evolution → curvature velocity → Ricci velocity → scalar variation` is explicit.
None of these are proved; each has a named blocker and the docstrings record the exact gap.

All proofs in this file are complete for what is proved; the unproved items are `Prop`-valued
definitions and structures, never `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace RicciScalar

universe v w

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Flow paths -/

/-- **A path of metric-compatible torsion-free connection data with a time-independent
orthonormal frame.** The frame is fixed in time, so the orthonormal-basis expansion of the
scalar curvature can be differentiated termwise; this is the standard "fixed frame" setting for
the scalar-curvature variation. The bracket is also fixed in time (the Lie bracket of vector
fields is part of the background manifold, not of the metric). -/
structure FlowPath (V : Type v) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ι : Type w) [Fintype ι] [DecidableEq ι] where
  /-- The time-dependent connection datum. -/
  data : ℝ → RiemannCurvatureData V ι
  /-- The time-independent orthonormal frame. -/
  frame : Module.Basis ι ℝ V
  /-- Every metric datum of the path has `frame` as its orthonormal basis. -/
  frame_basis : ∀ t : ℝ, (data t).metric.basis = frame
  /-- The abstract bracket is time-independent (the background Lie bracket). -/
  bracket_fixed : ∀ (t : ℝ) (X Y : V),
    (data t).conn.lie.bracket X Y = (data 0).conn.lie.bracket X Y

namespace FlowPath

variable (F : FlowPath V ι)

/-- The scalar curvature of the path at time `t`. -/
noncomputable def scal (t : ℝ) : ℝ := (F.data t).scalarCurvature

/-- The Ricci contraction of the path at time `t`. -/
noncomputable def ricci (t : ℝ) (X Y : V) : ℝ := (F.data t).ricciForm X Y

/-- The metric form of the path at time `t`. -/
noncomputable def metricForm (t : ℝ) (X Y : V) : ℝ := (F.data t).metric.form X Y

/-- The connection of the path at time `t`. -/
noncomputable def nabla (t : ℝ) (X Y : V) : V := (F.data t).conn.nabla X Y

/-- The bracket of the path at time `t`. -/
noncomputable def bracket (t : ℝ) (X Y : V) : V := (F.data t).conn.lie.bracket X Y

/-- The `(1,3)` curvature of the path at time `t`. -/
noncomputable def curvature (t : ℝ) (X Y Z : V) : V := (F.data t).curvature X Y Z

/-- **The stated metric flow equation** `∂ₜ g_t(X,Y) = h_t(X,Y)`. -/
def MetricFlowEquation (h : ℝ → V → V → ℝ) : Prop :=
  ∀ (t : ℝ) (X Y : V), HasDerivAt (fun s : ℝ => F.metricForm s X Y) (h t X Y) t

/-- **The stated Ricci-flow equation** `∂ₜ g = -2 Ric`. -/
def RicciFlowEquation : Prop :=
  MetricFlowEquation F (fun t X Y => -2 * F.ricci t X Y)

/-! ## Missing dependency 1: evolution of the Levi-Civita connection -/

/-- **Missing dependency 1: evolution of the Levi-Civita connection.**

`connVel t X Y = ∂ₜ (∇_t)_X Y` is the connection velocity, with the linearized Koszul formula
`2 g(A X Y, Z) = (∇_X h)(Y,Z) + (∇_Y h)(X,Z) - (∇_Z h)(X,Y)` where
`h = ∂ₜ g` and `(∇_X h)(Y,Z) = dirh X Y Z - h(∇_X Y, Z) - h(Y, ∇_X Z)`. The directional
derivative `dirh` of the variation tensor field is exactly the first-order calculus that the
abstract algebraic setting does not provide; it is carried as data. No inhabitant of this
structure is constructed in this file. -/
structure LeviCivitaEvolution (h : ℝ → V → V → ℝ) where
  /-- The connection velocity `∂ₜ ∇`. -/
  connVel : ℝ → V → V → V
  /-- Additivity of the connection velocity in its first vector argument. -/
  connVel_add₁ : ∀ (t : ℝ) (X X' Y : V), connVel t (X + X') Y = connVel t X Y + connVel t X' Y
  /-- Homogeneity of the connection velocity in its first vector argument. -/
  connVel_smul₁ : ∀ (t : ℝ) (a : ℝ) (X Y : V), connVel t (a • X) Y = a • connVel t X Y
  /-- Additivity of the connection velocity in its second vector argument. -/
  connVel_add₂ : ∀ (t : ℝ) (X Y Y' : V), connVel t X (Y + Y') = connVel t X Y + connVel t X Y'
  /-- Homogeneity of the connection velocity in its second vector argument. -/
  connVel_smul₂ : ∀ (t : ℝ) (a : ℝ) (X Y : V), connVel t X (a • Y) = a • connVel t X Y
  /-- The connection velocity is the time derivative of the connection, tested on the
  coordinate functions of the time-independent frame (the abstract space carries no norm, so
  differentiability is stated componentwise). -/
  hasDeriv : ∀ (t : ℝ) (X Y : V) (i : ι),
    HasDerivAt (fun s : ℝ => F.frame.repr (F.nabla s X Y) i)
      (F.frame.repr (connVel t X Y) i) t
  /-- Directional derivative of the metric-velocity tensor field (the missing calculus). -/
  dirh : ℝ → V → V → V → ℝ
  /-- The linearized Koszul formula determining `∂ₜ∇` from `∂ₜ g`. -/
  koszul : ∀ (t : ℝ) (X Y Z : V),
    2 * F.metricForm t (connVel t X Y) Z =
      dirh t X Y Z - h t (F.nabla t X Y) Z - h t Y (F.nabla t X Z)
      + dirh t Y X Z - h t (F.nabla t Y X) Z - h t X (F.nabla t Y Z)
      - dirh t Z X Y + h t (F.nabla t Z X) Y + h t X (F.nabla t Z Y)

/-- **The evolution-of-Levi-Civita dependency, as an existence `Prop`.** -/
def LeviCivitaEvolutionStatement (h : ℝ → V → V → ℝ) : Prop :=
  Nonempty (LeviCivitaEvolution F h)

/-! ## The curvature and Ricci velocities -/

/-- **The curvature velocity** determined by a connection velocity: the Leibniz expansion of
`∂ₜ R(X,Y)Z = (∂ₜ∇)_X∇_Y Z + ∇_X(∂ₜ∇)_Y Z - (∂ₜ∇)_Y∇_X Z - ∇_Y(∂ₜ∇)_X Z -
(∂ₜ∇)_{[X,Y]}Z`, valid because the bracket is time-independent. -/
noncomputable def curvVel (A : ℝ → V → V → V) (t : ℝ) (X Y Z : V) : V :=
  A t X (F.nabla t Y Z) + F.nabla t X (A t Y Z) - A t Y (F.nabla t X Z)
    - F.nabla t Y (A t X Z) - A t (F.bracket t X Y) Z

/-- **The curvature-evolution statement** (state-only): the derivative of the `(1,3)` curvature
is the curvature velocity, tested on the frame coordinates. -/
def CurvatureEvolutionStatement (A : ℝ → V → V → V) : Prop :=
  ∀ (t : ℝ) (X Y Z : V) (i : ι),
    HasDerivAt (fun s : ℝ => F.frame.repr (F.curvature s X Y Z) i)
      (F.frame.repr (F.curvVel A t X Y Z) i) t

/-! ## Missing dependency 2: commutation of the time derivative and the trace -/

/-- **Missing dependency 2: commutation of the time derivative and the trace.**

There is a Ricci velocity `Ricdot` with `∂ₜ Ric_t(X,Y) = Ricdot_t(X,Y)`, where
`Ric_t(X,Y) = tr(Z ↦ R_t(Z,X)Y)` is the Ricci trace. The content of the statement is that the
time derivative passes through `LinearMap.trace`; the trace of the derivative of the endomorphism
is the derivative of the trace. No `Ricdot` is constructed in this file. -/
def TraceCommutationStatement : Prop :=
  ∃ Ricdot : ℝ → V → V → ℝ,
    ∀ (t : ℝ) (X Y : V), HasDerivAt (fun s : ℝ => F.ricci s X Y) (Ricdot t X Y) t

/-! ## The scalar variation statement and its reduction -/

/-- **The scalar variation conclusion**: `d/dt scal = ∑ᵢ Ricdot(eᵢ,eᵢ)`, the metric trace of
the Ricci velocity `Ricdot` in the time-independent frame. -/
def ScalarVariationStatement (Ricdot : ℝ → V → V → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt (fun s : ℝ => F.scal s)
    (∑ i : ι, Ricdot t (F.frame i) (F.frame i)) t

/-- **Reduction of the scalar variation to the trace-commutation dependency.**

If the Ricci form of the path has derivative `Ricdot`, then the scalar curvature has derivative
the frame trace of `Ricdot`. The proof differentiates the finite orthonormal-frame expansion of
the scalar curvature; the fixed frame is what makes the expansion time-independent. Thus the
only missing inputs are the trace-commutation hypothesis (which produces `Ricdot`) and the
Levi-Civita evolution (which computes `Ricdot` from `∂ₜ g`). -/
theorem scalarVariation_of_traceCommutation (Ricdot : ℝ → V → V → ℝ)
    (h : ∀ (t : ℝ) (X Y : V), HasDerivAt (fun s : ℝ => F.ricci s X Y) (Ricdot t X Y) t) :
    ScalarVariationStatement F Ricdot := by
  intro t
  have hscal : (fun s : ℝ => F.scal s) =
      fun s : ℝ => ∑ i : ι, F.ricci s (F.frame i) (F.frame i) := by
    funext s
    rw [scal, RiemannCurvatureData.scalarCurvature_eq_sum_basis]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.frame_basis s]
    rfl
  rw [hscal]
  have hfun : (∑ i : ι, fun s : ℝ => F.ricci s (F.frame i) (F.frame i)) =
      fun s : ℝ => ∑ i : ι, F.ricci s (F.frame i) (F.frame i) := by
    funext s
    simp [Finset.sum_apply]
  have hsum0 := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => h t (F.frame i) (F.frame i))
  rw [hfun] at hsum0
  have hderiv : (∑ i ∈ Finset.univ, Ricdot t (F.frame i) (F.frame i)) =
      ∑ i : ι, Ricdot t (F.frame i) (F.frame i) := by
    simp
  rw [hderiv] at hsum0
  exact hsum0

/-- From the trace-commutation dependency alone, some Ricci velocity satisfies the scalar
variation statement. -/
theorem scalarVariation_of_traceCommutationStatement (h : TraceCommutationStatement F) :
    ∃ Ricdot : ℝ → V → V → ℝ, ScalarVariationStatement F Ricdot := by
  obtain ⟨Ricdot, hR⟩ := h
  exact ⟨Ricdot, scalarVariation_of_traceCommutation F Ricdot hR⟩

/-- **The scalar variation under the Ricci-flow equation** (state-only): under
`∂ₜ g = -2 Ric`, the scalar curvature evolves by the frame trace of the Ricci velocity. -/
def RicciFlowScalarVariationStatement (Ricdot : ℝ → V → V → ℝ) : Prop :=
  RicciFlowEquation F → ScalarVariationStatement F Ricdot

/-- The Ricci-flow specialization of the reduction: given the Ricci velocity, the Ricci-flow
equation is irrelevant to the scalar-variation identity itself (it enters only through the
computation of `Ricdot`). -/
theorem ricciFlowScalarVariation_of_traceCommutation (Ricdot : ℝ → V → V → ℝ)
    (h : ∀ (t : ℝ) (X Y : V), HasDerivAt (fun s : ℝ => F.ricci s X Y) (Ricdot t X Y) t) :
    RicciFlowScalarVariationStatement F Ricdot :=
  fun _ => scalarVariation_of_traceCommutation F Ricdot h

/-! ## The bundled variation interface -/

/-- **The full scalar-variation interface.** The stated flow equation with velocity `h`, the
Levi-Civita evolution dependency, and the trace-commutation dependency together with the
conclusion. This is a `Prop` with no proof; it packages exactly the missing inputs. -/
def ScalarVariationInterface (h : ℝ → V → V → ℝ) : Prop :=
  MetricFlowEquation F h ∧ LeviCivitaEvolutionStatement F h ∧
    ∃ Ricdot : ℝ → V → V → ℝ,
      TraceCommutationStatement F ∧ ScalarVariationStatement F Ricdot

/-! ## Named blockers -/

/-- **Blocker `B-D7-RS-LEVICIVITA-EVOLUTION`.** The evolution of the Levi-Civita connection
under a metric flow requires the linearized Koszul formula, whose right-hand side contains
directional derivatives of the variation tensor field `h = ∂ₜ g`; the abstract algebraic
setting has no base points, so that first-order calculus is not available. -/
def BlockerLeviCivitaEvolution : String :=
  "B-D7-RS-LEVICIVITA-EVOLUTION: no first-order calculus (directional derivatives of the \
  variation tensor field h = d/dt g) in the abstract algebraic setting; the linearized Koszul \
  formula for d/dt nabla is not available."

/-- **Blocker `B-D7-RS-TRACE-COMMUTATION`.** The commutation of `d/dt` with
`LinearMap.trace` requires a differentiability theory for paths of endomorphisms and for the
metric raising map; the abstract datum provides no topology or smooth structure. -/
def BlockerTraceCommutation : String :=
  "B-D7-RS-TRACE-COMMUTATION: no differentiability/topology for paths of endomorphisms and the \
  metric raising map; d/dt of the Ricci trace is not available."

/-- **Blocker `B-D7-RS-SCALAR-VARIATION`.** The scalar variation identity itself is conditional
on the two dependencies above; the classical Ricci-flow formula `∂ₜ R = ΔR + 2|Ric|²` further
needs a Laplacian on tensor fields, which mathlib does not provide. -/
def BlockerScalarVariation : String :=
  "B-D7-RS-SCALAR-VARIATION: the scalar variation is conditional on the Levi-Civita evolution \
  and trace commutation; the classical formula d/dt R = Delta R + 2|Ric|^2 also needs a \
  Laplacian on tensor fields."

theorem BlockerLeviCivitaEvolution_ne_nil : BlockerLeviCivitaEvolution ≠ "" := by
  unfold BlockerLeviCivitaEvolution; simp

theorem BlockerTraceCommutation_ne_nil : BlockerTraceCommutation ≠ "" := by
  unfold BlockerTraceCommutation; simp

theorem BlockerScalarVariation_ne_nil : BlockerScalarVariation ≠ "" := by
  unfold BlockerScalarVariation; simp

/-! ## A non-vacuous constant path -/

/-- **The constant flow path**: a single datum repeated for all times. -/
noncomputable def constFlow (D : RiemannCurvatureData V ι) : FlowPath V ι where
  data := fun _ => D
  frame := D.metric.basis
  frame_basis := fun _ => rfl
  bracket_fixed := fun _ _ _ => rfl

/-- **The reduction is non-vacuous**: on the constant path, `Ricdot = 0` is a valid Ricci
velocity, and the reduction produces the (true) statement that the scalar curvature has
derivative `0`. -/
theorem constFlow_scalarVariation (D : RiemannCurvatureData V ι) :
    ScalarVariationStatement (constFlow D) (fun _ _ _ => 0) := by
  apply scalarVariation_of_traceCommutation
  intro t X Y
  have h0 : HasDerivAt (fun s : ℝ => (constFlow D).ricci s X Y) 0 t := by
    have hfun : (fun s : ℝ => (constFlow D).ricci s X Y) = fun _ : ℝ => D.ricciForm X Y :=
      rfl
    rw [hfun]
    exact hasDerivAt_const t (D.ricciForm X Y)
  simpa using h0

end FlowPath

end RicciScalar
end D7
end Poincare
