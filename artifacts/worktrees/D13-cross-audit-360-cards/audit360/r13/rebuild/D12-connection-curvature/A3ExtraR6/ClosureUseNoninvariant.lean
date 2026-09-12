-- A3 round-6 independent consumer for the D12-connection-curvature closure.
-- Written by D13-cross-audit-360-cards; not derived from the producer card.
--
-- This is a *new* adversarial consumer of the claimed closure
-- `LeviCivitaExistenceStatement`:
--   * it builds a concrete 2-dimensional NON-bi-invariant model (standard dot
--     product, non-abelian bracket [e0,e1] = e0 + e1);
--   * shows the closure produces a Levi-Civita connection there
--     (`a3_noninvariant_leviCivita`), i.e. the closure is non-vacuous in exactly
--     the case where the historical BLOCKED docstring claimed extra invariance
--     was needed;
--   * shows the MILNOR connection differs from the mean connection
--     (`a3_milnor_ne_mean`) and that the mean connection is *not*
--     metric-compatible in this model (`a3_mean_not_metricCompatible`);
--   * proves the new uniqueness corollary `a3_leviCivita_unique`: every
--     Levi-Civita connection for a fixed (m, b) is the Milnor one.
import Poincare.D12.ConnectionCurvature

open scoped BigOperators

namespace A3R6

open Poincare Longrun Geometry
open Poincare.D12.ConnectionCurvature

universe v w

/-! ## A concrete non-bi-invariant 2-dimensional model -/

/-- The standard dot product on `Fin 2 → ℝ` (explicit 2-term formula). -/
noncomputable def dot2 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun X := {
    toFun Y := X 0 * Y 0 + X 1 * Y 1
    map_add' Y₁ Y₂ := by
      change X 0 * (Y₁ 0 + Y₂ 0) + X 1 * (Y₁ 1 + Y₂ 1) =
        (X 0 * Y₁ 0 + X 1 * Y₁ 1) + (X 0 * Y₂ 0 + X 1 * Y₂ 1)
      ring
    map_smul' a Y := by
      change X 0 * (a * Y 0) + X 1 * (a * Y 1) = a * (X 0 * Y 0 + X 1 * Y 1)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    change (X₁ 0 + X₂ 0) * Y 0 + (X₁ 1 + X₂ 1) * Y 1 =
      (X₁ 0 * Y 0 + X₁ 1 * Y 1) + (X₂ 0 * Y 0 + X₂ 1 * Y 1)
    ring
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    change (a * X 0) * Y 0 + (a * X 1) * Y 1 = a * (X 0 * Y 0 + X 1 * Y 1)
    ring

/-- The non-abelian bracket `[X,Y] = (X₀Y₁ − X₁Y₀) • (e₀ + e₁)` on `ℝ²`,
componentwise the constant vector with both entries `X₀Y₁ − X₁Y₀`. -/
noncomputable def bracket2 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun X := {
    toFun Y := fun _ => X 0 * Y 1 - X 1 * Y 0
    map_add' Y₁ Y₂ := by
      funext i
      change X 0 * (Y₁ 1 + Y₂ 1) - X 1 * (Y₁ 0 + Y₂ 0) =
        (X 0 * Y₁ 1 - X 1 * Y₁ 0) + (X 0 * Y₂ 1 - X 1 * Y₂ 0)
      ring
    map_smul' a Y := by
      funext i
      change X 0 * (a * Y 1) - X 1 * (a * Y 0) = a * (X 0 * Y 1 - X 1 * Y 0)
      ring
  }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    funext i
    change (X₁ 0 + X₂ 0) * Y 1 - (X₁ 1 + X₂ 1) * Y 0 =
      (X₁ 0 * Y 1 - X₁ 1 * Y 0) + (X₂ 0 * Y 1 - X₂ 1 * Y 0)
    ring
  map_smul' a X := by
    apply LinearMap.ext
    intro Y
    funext i
    change (a * X 0) * Y 1 - (a * X 1) * Y 0 = a * (X 0 * Y 1 - X 1 * Y 0)
    ring

/-- The bracket data: skew-symmetry is immediate; Jacobi is automatic in dimension 2
(checked here by `ring`). -/
noncomputable def lie2 : LieBracketData ℝ (Fin 2 → ℝ) where
  bracket := bracket2
  skew X Y := by
    funext i
    simp only [bracket2, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
    ring
  jacobi X Y Z := by
    funext i
    simp only [bracket2, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.zero_apply]
    ring

/-- The metric datum: standard dot product with the standard basis. -/
noncomputable def metric2 : MetricData (Fin 2 → ℝ) (Fin 2) where
  form := dot2
  symm X Y := by
    change X 0 * Y 0 + X 1 * Y 1 = Y 0 * X 0 + Y 1 * X 1
    ring
  pos_def X hX := by
    have hX' : X 0 ≠ 0 ∨ X 1 ≠ 0 := by
      by_contra h
      rw [not_or] at h
      apply hX
      ext i
      fin_cases i
      · exact not_not.mp h.1
      · exact not_not.mp h.2
    rcases hX' with h0 | h1
    · change 0 < X 0 * X 0 + X 1 * X 1
      nlinarith [mul_self_pos.mpr h0, mul_self_nonneg (X 1)]
    · change 0 < X 0 * X 0 + X 1 * X 1
      nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (X 0)]
  basis := Pi.basisFun ℝ (Fin 2)
  orthonormal i j := by
    simp only [dot2, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply]
    fin_cases i <;> fin_cases j <;> simp

/-- Explicit evaluation of the model bracket on `e₀, e₁`: `[e₀,e₁] = e₀ + e₁`. -/
theorem bracket2_e0_e1 :
    bracket2 (![1, 0] : Fin 2 → ℝ) ![0, 1] = ![1, 1] := by
  funext i
  fin_cases i <;> simp [bracket2]

/-- The model metric is **not** bracket-invariant:
`⟨[e₀,e₁],e₀⟩ + ⟨e₁,[e₀,e₀]⟩ = 1 ≠ 0`. -/
theorem a3_not_bracketInvariant : ¬ bracketInvariant metric2 lie2 := by
  intro h
  have hh := h (![1, 0] : Fin 2 → ℝ) ![0, 1] ![1, 0]
  have h1 : metric2.form (lie2.bracket ![1, 0] ![0, 1]) ![1, 0] = 1 := by
    rw [show lie2.bracket (![1, 0] : Fin 2 → ℝ) ![0, 1] = ![1, 1] from bracket2_e0_e1]
    simp [metric2, dot2]
  have h2 : metric2.form ![0, 1] (lie2.bracket (![1, 0] : Fin 2 → ℝ) ![1, 0]) = 0 := by
    have hz : lie2.bracket (![1, 0] : Fin 2 → ℝ) ![1, 0] = 0 := by
      funext i
      fin_cases i <;> simp [lie2, bracket2]
    rw [hz]
    simp [metric2, dot2]
  rw [h1, h2] at hh
  norm_num at hh

/-! ## New consequences of the closure -/

/-- The claimed closure holds at the non-bi-invariant model: a torsion-free,
metric-compatible connection exists even though the metric is not invariant. -/
theorem a3_noninvariant_leviCivita : LeviCivitaExistenceStatement metric2 lie2 :=
  leviCivitaExists metric2 lie2

/-- At this model the Milnor connection is *not* the mean connection. -/
theorem a3_milnor_ne_mean :
    milnorConnection metric2 lie2 ≠ (meanConnection lie2).nabla :=
  fun h => a3_not_bracketInvariant ((milnorConnection_eq_mean_iff metric2 lie2).mp h)

/-- At this model the mean connection is not metric-compatible. -/
theorem a3_mean_not_metricCompatible :
    ¬ IsMetricCompatible metric2 (meanConnection lie2).nabla :=
  fun h => a3_not_bracketInvariant ((meanConnection_isMetricCompatible_iff metric2 lie2).mp h)

/-- **New uniqueness corollary of the closure**: every Levi-Civita connection for a
fixed metric datum and bracket is the Milnor connection. -/
theorem a3_leviCivita_unique {V : Type v} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (m : MetricData V ι) (b : LieBracketData ℝ V) (d : LeviCivitaData m b) :
    d.nabla = milnorConnection m b :=
  leviCivita_nabla_unique m b d.isLeviCivita (milnorConnection_isLeviCivita m b)

end A3R6

#print axioms A3R6.a3_not_bracketInvariant
#print axioms A3R6.a3_noninvariant_leviCivita
#print axioms A3R6.a3_milnor_ne_mean
#print axioms A3R6.a3_mean_not_metricCompatible
#print axioms A3R6.a3_leviCivita_unique
