/-
Task `D9-parabolic-maximum-principle`: scalar heat-type sub/supersolution
interface over the abstract manifold-with-Laplacian layer of the D6 release.

This file consumes `Poincare.Longrun.Entropy.WeightedCalculus`, the abstract
layer already present in the release (gradient, Laplacian, metric pairing), and
adds the scalar heat-type operator

`L u = Δu + ⟨X, ∇u⟩ + b · u`

together with its subsolution / supersolution / solution predicates and the
comparison-principle statement.

Honesty boundary.  The operator datum and the predicates are definitions, and
the comparison principle is recorded as the `Prop`-valued definition
`ComparisonPrincipleStatement`: the pinned mathlib has no parabolic PDE theory
and no heat-kernel machinery, so the statement is *not* proved here.  The only
proofs in this file are structural lemmas and one completely explicit
non-vacuity instance for the zero operator on the one-point space (which is a
genuine, kernel-checked instance of the comparison statement, not a proof of
the general theorem).
-/
import Poincare.Longrun.Entropy.Bridge

namespace Poincare.D9.ParabolicMaximumPrinciple

open Poincare.Longrun.Entropy

universe u

/-! ## Operator data -/

/-- Interface data for the scalar heat-type operator
`L u = Δu + ⟨X, ∇u⟩ + b · u` on the abstract manifold-with-Laplacian layer.

* `calculus` supplies the Laplacian `Δ`, the abstract gradient and the metric
  pairing `⟨·, ·⟩` (the D6 `WeightedCalculus` layer);
* `drift` is the vector field `X` of the first-order term;
* `potential` is the coefficient `b` of the zeroth-order reaction term.

The data is deliberately *not* constrained by axioms; the analytic content is
kept in the statement-only properties of this module and of `StateOnly`. -/
structure HeatTypeData (X : Type u) where
  /-- The underlying manifold-with-Laplacian layer. -/
  calculus : WeightedCalculus X
  /-- The drift vector field `X`. -/
  drift : X → X
  /-- The coefficient `b` of the reaction term `b · u`. -/
  potential : X → ℝ

/-- The first-order drift term `⟨X, ∇u⟩` at a point. -/
def HeatTypeData.driftTerm {X : Type u} (H : HeatTypeData X) (u : X → ℝ) (x : X) : ℝ :=
  H.calculus.metric (H.drift x) (H.calculus.grad u x)

/-- The scalar heat-type operator `L u = Δu + ⟨X, ∇u⟩ + b · u` at a point. -/
def HeatTypeData.op {X : Type u} (H : HeatTypeData X) (u : X → ℝ) (x : X) : ℝ :=
  H.calculus.laplacian u x + H.driftTerm u x + H.potential x * u x

/-- Definitional expansion of the heat-type operator, showing the three terms
`Δu`, `⟨X, ∇u⟩` and `b · u` separately. -/
theorem HeatTypeData.op_apply {X : Type u} (H : HeatTypeData X) (u : X → ℝ) (x : X) :
    H.op u x
      = H.calculus.laplacian u x + H.calculus.metric (H.drift x) (H.calculus.grad u x)
        + H.potential x * u x :=
  rfl

/-! ## Sub/supersolutions -/

/-- `u` is a **subsolution** of the heat-type inequality
`∂ₜu ≤ Δu + ⟨X, ∇u⟩ + b · u`:

at every space-time point `(t, x)` the time derivative of `s ↦ u s x` exists and
is at most `L(u(t))` at `x`.  This is the `≤` direction of the equation. -/
def IsSubsolution {X : Type u} (H : HeatTypeData X) (u : ℝ → X → ℝ) : Prop :=
  ∀ t x, ∃ d : ℝ, HasDerivAt (fun s : ℝ => u s x) d t ∧ d ≤ H.op (u t) x

/-- `u` is a **supersolution** of the heat-type inequality
`∂ₜu ≥ Δu + ⟨X, ∇u⟩ + b · u`, i.e. the negation of the subsolution inequality. -/
def IsSupersolution {X : Type u} (H : HeatTypeData X) (u : ℝ → X → ℝ) : Prop :=
  ∀ t x, ∃ d : ℝ, HasDerivAt (fun s : ℝ => u s x) d t ∧ H.op (u t) x ≤ d

/-- `u` is a **classical solution** of the heat-type equation
`∂ₜu = Δu + ⟨X, ∇u⟩ + b · u`. -/
def IsSolution {X : Type u} (H : HeatTypeData X) (u : ℝ → X → ℝ) : Prop :=
  ∀ t x, HasDerivAt (fun s : ℝ => u s x) (H.op (u t) x) t

/-- Every classical solution is a subsolution. -/
theorem isSubsolution_of_isSolution {X : Type u} {H : HeatTypeData X} {u : ℝ → X → ℝ}
    (h : IsSolution H u) : IsSubsolution H u :=
  fun t x => ⟨H.op (u t) x, h t x, le_rfl⟩

/-- Every classical solution is a supersolution. -/
theorem isSupersolution_of_isSolution {X : Type u} {H : HeatTypeData X} {u : ℝ → X → ℝ}
    (h : IsSolution H u) : IsSupersolution H u :=
  fun t x => ⟨H.op (u t) x, h t x, le_rfl⟩

/-! ## The comparison-principle interface -/

/-- **Comparison-principle statement (interface only).**

On a closed manifold `X`, if the potential is nonpositive (`b ≤ 0`) and `u` is a
subsolution starting below a supersolution `v` (with continuous time slices),
then `u` stays below `v` for all forward times.

This is the classical parabolic comparison principle for the scalar heat-type
operator `L u = Δu + ⟨X, ∇u⟩ + b · u`.  It is recorded as a `Prop`-valued
definition and is *not* proved: the pinned mathlib has no parabolic PDE theory.
The nonpositive-potential hypothesis is what makes the constant `0` a
supersolution of the homogeneous inequality, hence what rules out exponential
growth of `u - v` in the reaction term. -/
def ComparisonPrincipleStatement {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (H : HeatTypeData X) : Prop :=
  (∀ x, H.potential x ≤ 0) →
    ∀ (T : ℝ) (u v : ℝ → X → ℝ),
      IsSubsolution H u → IsSupersolution H v →
      (∀ t, Continuous (u t)) → (∀ t, Continuous (v t)) →
      (∀ x, u 0 x ≤ v 0 x) →
      ∀ t, 0 ≤ t → t ≤ T → ∀ x, u t x ≤ v t x

/-! ## Non-vacuity: the zero datum on the one-point space -/

/-- The zero heat-type datum on the one-point space: zero calculus, zero drift,
zero potential. -/
def zeroHeatTypeData : HeatTypeData Unit where
  calculus := zeroCalculus
  drift := fun _ => ()
  potential := fun _ => 0

/-- The zero datum has zero heat-type operator, so its sub/supersolution
inequalities reduce to `∂ₜu ≤ 0` and `0 ≤ ∂ₜv` pointwise. -/
theorem zeroHeatTypeData_op (u : Unit → ℝ) (x : Unit) : zeroHeatTypeData.op u x = 0 := by
  simp [HeatTypeData.op, HeatTypeData.driftTerm, zeroHeatTypeData, zeroCalculus]

/-- The zero function solves the zero heat-type equation. -/
theorem isSolution_zeroHeatTypeData : IsSolution zeroHeatTypeData (fun _ _ => (0 : ℝ)) := by
  intro t x
  rw [zeroHeatTypeData_op]
  exact hasDerivAt_const t 0

/-- The zero function is a subsolution of the zero heat-type datum. -/
theorem isSubsolution_zeroHeatTypeData : IsSubsolution zeroHeatTypeData (fun _ _ => (0 : ℝ)) :=
  isSubsolution_of_isSolution isSolution_zeroHeatTypeData

/-- The zero function is a supersolution of the zero heat-type datum. -/
theorem isSupersolution_zeroHeatTypeData : IsSupersolution zeroHeatTypeData (fun _ _ => (0 : ℝ)) :=
  isSupersolution_of_isSolution isSolution_zeroHeatTypeData

/-- **Checked non-vacuity instance of the comparison interface.**

For the zero heat-type datum on the one-point space the comparison statement
holds.  Indeed a subsolution has `∂ₜu ≤ 0` and a supersolution has `0 ≤ ∂ₜv`
pointwise in time, so `u` is antitone and `v` is monotone; the mean-value
monotonicity lemma turns this into `u t ≤ u 0 ≤ v 0 ≤ v t`.  This is a genuine
instance of `ComparisonPrincipleStatement` (`X = Unit`, `L = 0`), which shows
that the interface is not an empty hypothesis bundle; it is not a proof of the
general statement. -/
theorem comparisonPrincipleStatement_zeroHeatTypeData :
    ComparisonPrincipleStatement zeroHeatTypeData := by
  intro _hpot _T u v hu hv _huc _hvc h0 t ht _hxT x
  -- rewrite the zero-operator bounds once, while the witnesses are still plain
  -- variables, so that no rewrite happens underneath a `Classical.choose`.
  have hu' : ∀ s x, ∃ d : ℝ, HasDerivAt (fun r : ℝ => u r x) d s ∧ d ≤ 0 := by
    intro s x
    obtain ⟨d, hd, hdle⟩ := hu s x
    exact ⟨d, hd, by rwa [zeroHeatTypeData_op] at hdle⟩
  have hv' : ∀ s x, ∃ d : ℝ, HasDerivAt (fun r : ℝ => v r x) d s ∧ 0 ≤ d := by
    intro s x
    obtain ⟨d, hd, hdle⟩ := hv s x
    exact ⟨d, hd, by rwa [zeroHeatTypeData_op] at hdle⟩
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => u r x - v r x)
        (Classical.choose (hu' s x) - Classical.choose (hv' s x)) s :=
    fun s => (Classical.choose_spec (hu' s x)).1.sub (Classical.choose_spec (hv' s x)).1
  have hnonpos :
      (fun s : ℝ => Classical.choose (hu' s x) - Classical.choose (hv' s x)) ≤ 0 := by
    intro s
    have h1 : Classical.choose (hu' s x) ≤ 0 := (Classical.choose_spec (hu' s x)).2
    have h2 : 0 ≤ Classical.choose (hv' s x) := (Classical.choose_spec (hv' s x)).2
    show Classical.choose (hu' s x) - Classical.choose (hv' s x) ≤ (0 : ℝ)
    linarith
  have hmono := antitone_of_hasDerivAt_nonpos hderiv hnonpos
  have ht' : u t x - v t x ≤ u 0 x - v 0 x := hmono ht
  linarith [h0 x]

/-! ## Axiom audit -/

#print axioms HeatTypeData
#print axioms HeatTypeData.driftTerm
#print axioms HeatTypeData.op
#print axioms HeatTypeData.op_apply
#print axioms IsSubsolution
#print axioms IsSupersolution
#print axioms IsSolution
#print axioms isSubsolution_of_isSolution
#print axioms isSupersolution_of_isSolution
#print axioms ComparisonPrincipleStatement
#print axioms zeroHeatTypeData
#print axioms zeroHeatTypeData_op
#print axioms isSolution_zeroHeatTypeData
#print axioms isSubsolution_zeroHeatTypeData
#print axioms isSupersolution_zeroHeatTypeData
#print axioms comparisonPrincipleStatement_zeroHeatTypeData

end Poincare.D9.ParabolicMaximumPrinciple
