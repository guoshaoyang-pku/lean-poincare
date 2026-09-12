/-
D11 adversarial audit — non-vacuity probes.

Each block instantiates a D10 "unconditional" claim at concrete values and proves a
genuinely informative consequence, so the audited statements are not definitionally
trivial.  Written by the D11 auditor; imports only the D10 modules.
-/
import Poincare.D10.HeatKernelEuclidean.AxiomAudit
import Poincare.D10.GaussianToolbox.PrintAxioms
import Poincare.D10.MaximumPrincipleRN.AxiomAudit
import Poincare.D10.BochnerEuclidean.Axioms
import Poincare.D10.JacobiConstantCurvature.AxiomAudit
import Poincare.D10.TriangulationLowDim.Audit

set_option maxRecDepth 8000

open scoped Topology InnerProductSpace Real Laplacian
open Finset
open Poincare.D10.MaximumPrincipleRN
open Poincare.D10.BochnerEuclidean
open Poincare.D10.TriangulationLowDim
open Poincare.D10

namespace Poincare.Audit.D11

noncomputable section

/-! ## 1. HeatKernelEuclidean — the claims have content at concrete points -/

section HeatKernelProbe

open Poincare.D10.HeatKernelEuclidean

/-- The heat kernel is strictly positive and strictly below `1` at `(n = 1, t = 1, x = 0)`;
its value there is exactly `(4π) ^ (-1/2)`. -/
theorem heatKernel_probe_value : gaussianKernel 1 1 (0 : EuclideanSpace ℝ (Fin 1)) =
    (4 * Real.pi) ^ (-((1 : ℝ) / 2)) := by
  rw [gaussianKernel_apply]
  norm_num [Real.exp_zero]

theorem heatKernel_probe_pos : 0 < gaussianKernel 1 1 (0 : EuclideanSpace ℝ (Fin 1)) :=
  gaussianKernel_pos 1 (by norm_num) 0

theorem heatKernel_probe_lt_one : gaussianKernel 1 1 (0 : EuclideanSpace ℝ (Fin 1)) < 1 := by
  rw [heatKernel_probe_value]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * Real.pi),
    ← Real.sqrt_eq_rpow (4 * Real.pi)]
  rw [inv_eq_one_div, div_lt_one (Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi))]
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.pi_gt_three])

/-- The heat equation, instantiated at `(n = 1, t = 1, x = 0)`. -/
theorem heatEquation_probe :
    deriv (fun s : ℝ => gaussianKernel 1 s (0 : EuclideanSpace ℝ (Fin 1))) 1
      = Δ (gaussianKernel 1 1) 0 :=
  heat_equation 1 (by norm_num) 0

/-- Total mass, instantiated at `n = 1, t = 1`. -/
theorem mass_probe : (∫ x : EuclideanSpace ℝ (Fin 1), gaussianKernel 1 1 x) = 1 :=
  gaussianKernel_integral 1 (by norm_num)

/-- The semigroup identity at concrete `(n = 1, t = 1, s = 2, x = 0)`. -/
theorem semigroup_probe :
    (∫ y : EuclideanSpace ℝ (Fin 1), gaussianKernel 1 1 y * gaussianKernel 1 2 ((0 : EuclideanSpace ℝ (Fin 1)) - y))
      = gaussianKernel 1 (1 + 2) 0 :=
  gaussianKernel_convolution 1 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2) 0

/-- The same probe with the sum evaluated: `K₁ * K₂ = K₃`. -/
theorem semigroup_probe_three :
    (∫ y : EuclideanSpace ℝ (Fin 1), gaussianKernel 1 1 y * gaussianKernel 1 2 ((0 : EuclideanSpace ℝ (Fin 1)) - y))
      = gaussianKernel 1 3 0 := by
  have h := semigroup_probe
  rw [show (1 + 2 : ℝ) = 3 by norm_num] at h
  exact h

end HeatKernelProbe

/-! ## 2. GaussianToolbox — moments over the whole real line at concrete values -/

section GaussianProbe

open Poincare.GaussianToolbox

/-- `∫ x : ℝ, exp (-x²) = √π`: the `n = 0` moment is a positive number, not zero. -/
theorem gaussian_probe_moment_zero : (∫ x : ℝ, gaussianKernel 1 x) = Real.sqrt Real.pi :=
  integral_moment_zero

theorem gaussian_probe_moment_zero_pos : 0 < (∫ x : ℝ, gaussianKernel 1 x) := by
  rw [gaussian_probe_moment_zero]
  exact Real.sqrt_pos_of_pos Real.pi_pos

/-- The second moment over the whole line is `√π / 2`. -/
theorem gaussian_probe_moment_two : (∫ x : ℝ, x ^ 2 * gaussianKernel 1 x) = Real.sqrt Real.pi / 2 :=
  integral_moment_two

/-- The normalised density at `0` equals `1/√π`, a genuine value strictly between `0` and `1`. -/
theorem gaussian_probe_density : gaussianDensity 1 0 = 1 / Real.sqrt Real.pi := by
  rw [gaussianDensity, gaussianKernel_def]
  norm_num [Real.exp_zero]

theorem gaussian_probe_density_pos : 0 < gaussianDensity 1 0 := by
  rw [gaussian_probe_density]
  exact div_pos (by norm_num) (Real.sqrt_pos_of_pos Real.pi_pos)

theorem gaussian_probe_density_lt_one : gaussianDensity 1 0 < 1 := by
  rw [gaussian_probe_density]
  rw [div_lt_one (Real.sqrt_pos_of_pos Real.pi_pos)]
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.pi_gt_three])

/-- The variance of the normalised density at `a = 1` is `1/2`, its true variance. -/
theorem gaussian_probe_variance : gaussianVariance 1 = 1 / 2 := by norm_num [gaussianVariance]

/-- The second moment of the normalised density equals the variance `1/2`. -/
theorem gaussian_probe_density_moment :
    (∫ x : ℝ, x ^ 2 * gaussianDensity 1 x) = 1 / 2 := by
  rw [integral_gaussianDensity_mul_sq (a := 1) (by norm_num), gaussian_probe_variance]

/-- The multivariate Gaussian in dimension `2` integrates to `π` (over the whole `ℝ²`). -/
theorem gaussian_probe_multivariate :
    (∫ x : Fin 2 → ℝ, gaussianVec 2 x) = Real.pi := by
  rw [integral_gaussianVec_eq_pi_rpow 2]
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num]
  exact Real.rpow_one Real.pi

/-- The `n = 0`-dimensional normalised Gaussian has mass `1`: the mass-1 claim also holds
in the degenerate zero-dimensional case (the empty product is `1`, `(√π)^0 = 1`). -/
theorem gaussian_probe_multivariate_zero :
    (∫ x : Fin 0 → ℝ, gaussianVecNormalized 0 x) = 1 :=
  integral_gaussianVecNormalized 0

end GaussianProbe

/-! ## 3. JacobiConstantCurvature — explicit values of the solution branches -/

/-- The flat branch: `jacobiSol 0 5 = 5`. -/
theorem jacobi_probe_flat : jacobiSol 0 5 = 5 := by
  norm_num [jacobiSol, jacobiSolFlat]

/-- The spherical branch at `K = 2`, `t = π/(2√2)`: `sin(√2 t)/√2 = 1/√2`. -/
theorem jacobi_probe_sphere :
    jacobiSol 2 (Real.pi / 2 / Real.sqrt 2) = 1 / Real.sqrt 2 := by
  rw [jacobiSol_of_pos (by norm_num : (0 : ℝ) < 2), jacobiSolSphere]
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos_of_pos (by norm_num)).ne'
  have h : Real.sqrt 2 * (Real.pi / 2 / Real.sqrt 2) = Real.pi / 2 := by
    rw [← mul_div_assoc, mul_comm (Real.sqrt 2) (Real.pi / 2)]
    exact mul_div_cancel_right₀ (Real.pi / 2) hsqrt
  rw [h, Real.sin_pi_div_two]

/-- The first zero of the `K = 2` branch is `π/√2`. -/
theorem jacobi_probe_firstZero : jacobiSol 2 (Real.pi / Real.sqrt 2) = 0 :=
  jacobiSol_firstZero (by norm_num : (0 : ℝ) < 2)

/-- Rauch comparison at `K₁ = 0`, `K₂ = 2`, `t = π/(2√2)`: with
`jacobiSol 2 t = 1/√2 > 0` and `jacobiSol 0 t = t`, the inequality is informative. -/
theorem jacobi_probe_rauch :
    jacobiSol 2 (Real.pi / 2 / Real.sqrt 2) ≤ jacobiSol 0 (Real.pi / 2 / Real.sqrt 2) := by
  refine rauch_comparison (K₁ := 0) (K₂ := 2) (by norm_num) ?_ ?_
  · exact div_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      (le_of_lt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)))
  · intro _
    exact div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) (by positivity)

/-- At the comparison point both sides are explicit: `1/√2 ≤ π/(2√2)`, i.e. `√2 ≤ π/2 · √2` …
equivalently `1 ≤ π/2`, which holds since `π > 3`. -/
theorem jacobi_probe_rauch_values :
    jacobiSol 2 (Real.pi / 2 / Real.sqrt 2) = 1 / Real.sqrt 2 ∧
      jacobiSol 0 (Real.pi / 2 / Real.sqrt 2) = Real.pi / 2 / Real.sqrt 2 := by
  constructor
  · exact jacobi_probe_sphere
  · rw [jacobiSol_of_zero, jacobiSolFlat]

/-! ## 4. TriangulationLowDim — the computed values are informative, not tautologies -/

/-- The five Euler characteristics (kernel-checked conjunction restated). -/
theorem triangulation_probe_values :
    triangleDisk.eulerChar = 1 ∧ circleS1.eulerChar = 0 ∧
      tetrahedronBoundary.eulerChar = 2 ∧ octahedronBoundary.eulerChar = 2 ∧
      torus7.eulerChar = 0 :=
  d10_eulerChar_values

/-- The disk and the circle are genuinely different complexes (different face counts). -/
theorem triangulation_probe_distinct :
    triangleDisk.faces.card ≠ circleS1.faces.card := by
  rw [triangleDisk_faces_card, circleS1_faces_card]
  norm_num

/-- The torus is not the octahedron: `43 ≠ 27` faces. -/
theorem triangulation_probe_torus_ne_octa :
    torus7.faces.card ≠ octahedronBoundary.faces.card := by
  rw [torus7_faces_card, octahedronBoundary_faces_card]
  norm_num

/-- The torus genuinely contains the triangle `{0,1,3}` (an explicit face witness). -/
theorem triangulation_probe_torus_face :
    ({0, 1, 3} : Finset (Fin 7)) ∈ torus7.faces := by
  decide

/-- The torus has a triangle from each of the two cyclic facet families. -/
theorem triangulation_probe_torus_faces :
    ({0, 1, 3} : Finset (Fin 7)) ∈ torus7.faces ∧
      ({0, 2, 3} : Finset (Fin 7)) ∈ torus7.faces := by
  constructor
  · decide
  · decide

/-- `MoiseTriangulationTheorem` and `HeawoodTorusVertexBound` are `def`s of type `Prop`
(statement-only): a compile-time witness that they exist and are usable, not an assertion
of their truth. -/
example : MoiseTriangulationTheorem → HeawoodTorusVertexBound → True := fun _ _ => trivial

/-- `AdmitsFiniteTriangulation` is inhabited: the realisation of the circle triangulation
admits a finite triangulation. -/
theorem triangulation_probe_realization :
    AdmitsFiniteTriangulation (GeometricRealization circleS1) :=
  admitsFiniteTriangulation_realization circleS1

/-! ## 5. MaximumPrincipleRN — the weak maximum principle applied to a non-constant subsolution -/

section MaximumPrincipleProbe

open Set Filter
open scoped Topology

/-- The open unit ball of `ℝ¹` (any open bounded nonempty set works; the unit ball keeps the
boundary values explicit). -/
def unitBall1 : Set (Fin 1 → ℝ) := Metric.ball (0 : Fin 1 → ℝ) 1

lemma unitBall1_open : IsOpen unitBall1 := Metric.isOpen_ball

lemma unitBall1_bounded : Bornology.IsBounded unitBall1 := Metric.isBounded_ball

lemma unitBall1_ne : unitBall1.Nonempty := ⟨0, Metric.mem_ball_self (by norm_num)⟩

/-- The probe subsolution `u(x, t) = x₀ - t` on `ℝ¹ × ℝ`: non-constant, `u_t = -1`,
`Δu = 0`, hence `u_t - Δu = -1 ≤ 0`. -/
def probeU : (Fin 1 → ℝ) × ℝ → ℝ := fun p => p.1 0 - p.2

lemma probeU_continuous : Continuous probeU := by
  change Continuous (fun p : (Fin 1 → ℝ) × ℝ => p.1 0 - p.2)
  exact ((continuous_apply (0 : Fin 1)).comp continuous_fst).sub continuous_snd

lemma probeU_not_constant {T : ℝ} (hT : 0 < T) : probeU (0, 0) ≠ probeU (0, T) := by
  change (0 : Fin 1 → ℝ) 0 - 0 ≠ (0 : Fin 1 → ℝ) 0 - T
  norm_num
  exact ne_of_gt hT

lemma probeU_isHeatSubsolutionOn {T : ℝ} :
    IsHeatSubsolutionOn unitBall1 T probeU := by
  refine IsHeatSubsolutionOn.of_twoSided
    (td := fun (_ : Fin 1 → ℝ) (_ : ℝ) => (-1 : ℝ))
    (gx := fun (_ : Fin 1 → ℝ) (_ : ℝ) (_ : Fin 1) => (1 : ℝ))
    (gxx := fun (_ : Fin 1 → ℝ) (_ : ℝ) (_ : Fin 1) => (0 : ℝ))
    ?_ ?_ ?_ ?_
  · intro t _ x _
    change HasDerivAt (fun s : ℝ => x 0 - s) (-1) t
    have h : HasDerivAt (fun s : ℝ => x 0 - s) (0 - 1) t :=
      (hasDerivAt_const (x := t) (x 0)).sub (hasDerivAt_id t)
    simpa using h
  · intro t _ x _ i
    have hfun : (fun s : ℝ => probeU (Function.update x i s, t)) = fun s : ℝ => s - t := by
      funext s
      rw [show i = (0 : Fin 1) from Subsingleton.elim i 0]
      rfl
    rw [hfun]
    change HasDerivAt (fun s : ℝ => s - t) 1 (x i)
    have h : HasDerivAt (fun s : ℝ => s - t) 1 (x i) :=
      (hasDerivAt_id (x i)).sub_const t
    simpa using h
  · intro t _ x _ i
    change HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 (x i)
    exact hasDerivAt_const (x := x i) 1
  · intro t _ x _
    simp

/-- The parabolic boundary bound: on `∂(unitBall1 × [0,T])` the probe is `≤ 1`
(its values there are `x₀ - t` with `|x₀| ≤ 1`, `t ≥ 0`). -/
lemma probeU_boundary_le_one {T : ℝ} : ∀ q ∈ parabolicBoundary unitBall1 T, probeU q ≤ 1 := by
  intro q hq
  have hcyl := parabolicBoundary_subset_cylinder hq
  rw [mem_parabolicCylinder] at hcyl
  have hx : q.1 ∈ closure unitBall1 := hcyl.1
  have ht0 : 0 ≤ q.2 := hcyl.2.1
  have hcl : IsClosed (Metric.closedBall (0 : Fin 1 → ℝ) 1) := Metric.isClosed_closedBall
  have hsub : unitBall1 ⊆ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
    intro x hx
    exact Metric.mem_closedBall.mpr (le_of_lt hx)
  have hq : q.1 ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 := closure_minimal hsub hcl hx
  have hnorm : ‖q.1‖ ≤ 1 := by
    simpa [dist_eq_norm, sub_zero] using (Metric.mem_closedBall.mp hq)
  have hx0 : q.1 0 ≤ 1 := by
    have h1 : |q.1 0| ≤ ‖q.1‖ := norm_le_pi_norm q.1 0
    have h2 : q.1 0 ≤ |q.1 0| := le_abs_self _
    linarith
  change q.1 0 - q.2 ≤ 1
  linarith

/-- The boundary point `((1), 0)` of the unit cylinder, where the probe takes the value `1`. -/
lemma probe_boundary_point {T : ℝ} (hT : 0 < T) :
    (((fun _ : Fin 1 => (1 : ℝ)), (0 : ℝ)) : (Fin 1 → ℝ) × ℝ) ∈ parabolicBoundary unitBall1 T := by
  rw [parabolicBoundary_eq (le_of_lt hT)]
  right
  constructor
  · rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min ε 1
    have hδpos : 0 < δ := lt_min hε (by norm_num)
    have hδleε : δ ≤ ε := min_le_left ε 1
    have hδle1 : δ ≤ 1 := min_le_right ε 1
    refine ⟨fun _ : Fin 1 => 1 - δ / 2, ?_, ?_⟩
    · change (fun _ : Fin 1 => 1 - δ / 2) ∈ Metric.ball (0 : Fin 1 → ℝ) 1
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, pi_norm_const]
      have hpos : 0 ≤ 1 - δ / 2 := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      linarith
    · rw [dist_eq_norm]
      rw [show ((fun _ : Fin 1 => (1 : ℝ)) - (fun _ : Fin 1 => 1 - δ / 2) : Fin 1 → ℝ)
          = fun _ : Fin 1 => δ / 2 by
        funext i
        simp only [Pi.sub_apply]
        ring_nf]
      rw [pi_norm_const, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
  · rfl

/-- **The weak maximum principle applied to the non-constant subsolution** `u(x,t) = x₀ - t`
on the unit cylinder: `u ≤ 1` on the whole cylinder. -/
theorem probe_weak_maximum_principle {T : ℝ} (hT : 0 < T) :
    ∀ p ∈ parabolicCylinder unitBall1 T, probeU p ≤ 1 :=
  weak_maximum_principle (Ω := unitBall1) (T := T) (M := 1) (u := probeU)
    unitBall1_open unitBall1_bounded unitBall1_ne hT probeU_continuous.continuousOn
    probeU_isHeatSubsolutionOn probeU_boundary_le_one

/-- The supremum of the probe on the parabolic boundary is exactly `1` (attained at
`((1), 0)`), so the bound produced by the maximum principle is sharp. -/
theorem probe_boundary_sSup {T : ℝ} (hT : 0 < T) :
    sSup (probeU '' parabolicBoundary unitBall1 T) = 1 := by
  have hK : IsCompact (parabolicCylinder unitBall1 T) :=
    unitBall1_bounded.isCompact_closure.prod isCompact_Icc
  have hbdd : BddAbove (probeU '' parabolicBoundary unitBall1 T) :=
    (hK.bddAbove_image probeU_continuous.continuousOn).mono
      (image_mono parabolicBoundary_subset_cylinder)
  apply le_antisymm
  · apply csSup_le
    · exact ⟨1, ⟨((fun _ : Fin 1 => (1 : ℝ)), (0 : ℝ)), probe_boundary_point hT, by
        change (fun _ : Fin 1 => (1 : ℝ)) 0 - 0 = 1
        norm_num⟩⟩
    · rintro y ⟨q, hq, rfl⟩
      exact probeU_boundary_le_one q hq
  · apply le_csSup hbdd
    exact ⟨((fun _ : Fin 1 => (1 : ℝ)), (0 : ℝ)), probe_boundary_point hT, by
      change (fun _ : Fin 1 => (1 : ℝ)) 0 - 0 = 1
      norm_num⟩

/-- Supremum form at the interior point `(0, T)`: `-T ≤ 1` follows from the principle with
the sharp boundary value `1`. -/
theorem probe_sSup_form {T : ℝ} (hT : 0 < T) :
    ∀ p ∈ parabolicCylinder unitBall1 T, probeU p ≤ sSup (probeU '' parabolicBoundary unitBall1 T) :=
  weak_maximum_principle_sSup (Ω := unitBall1) (T := T) (u := probeU)
    unitBall1_open unitBall1_bounded unitBall1_ne hT probeU_continuous.continuousOn
    probeU_isHeatSubsolutionOn

/-- The conclusion is not automatic: the non-subsolution `v(x,t) = x₀ + 100t` violates the
bound `≤ 1` on the cylinder, so the subsolution hypotheses have content. -/
theorem probe_nonSubsolution_fails : ∃ T : ℝ, 0 < T ∧
    ¬ (∀ p ∈ parabolicCylinder unitBall1 T,
      (fun p : (Fin 1 → ℝ) × ℝ => p.1 0 + 100 * p.2) p ≤ 1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro h
  have hmem : ((0 : Fin 1 → ℝ), 1) ∈ parabolicCylinder unitBall1 1 :=
    ⟨subset_closure (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)), ⟨by norm_num, le_rfl⟩⟩
  have hbad := h ((0 : Fin 1 → ℝ), 1) hmem
  norm_num at hbad

end MaximumPrincipleProbe

/-! ## 6. BochnerEuclidean — the Bochner identity and its harmonic corollary at concrete values -/

section BochnerProbe

open Poincare.D10.BochnerEuclidean

/-- Coordinate derivatives are Kronecker deltas: `∂ᵢ(x ↦ xⱼ) = δᵢⱼ` (derived from the
continuous-linear viewpoint through `innerSL`). -/
lemma D_coord (i j : Fin n) : D i (fun x : E n => x j) = fun _ : E n => (if i = j then 1 else 0 : ℝ) := by
  funext x
  rw [D]
  have hfun : (fun x : E n => x j) =
      fun x : E n => ((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ j)) x := by
    funext y
    rw [innerSL_apply_apply]
    exact (Poincare.D10.HeatKernelEuclidean.inner_basisFun n j y).symm
  rw [hfun]
  change fderiv ℝ (⇑((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ j))) x (basis i) = if i = j then 1 else 0
  rw [ContinuousLinearMap.fderiv]
  rw [innerSL_apply_apply, Poincare.D10.HeatKernelEuclidean.inner_basisFun, basis_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

lemma coord_contDiffAt {x : E n} (i : Fin n) :
    ContDiffAt ℝ 1 (fun y : E n => y i) x := by
  have hfun : (fun y : E n => y i) =
      fun y : E n => ((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)) y := by
    funext y
    rw [innerSL_apply_apply]
    exact (Poincare.D10.HeatKernelEuclidean.inner_basisFun n i y).symm
  rw [hfun]
  exact ((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)).contDiff.contDiffAt

def probeQuad : E 2 → ℝ := fun x => x 0 ^ 2 - x 1 ^ 2

lemma probeQuad_contDiff : ContDiff ℝ 3 probeQuad := by
  unfold probeQuad
  fun_prop

lemma D_probeQuad (i : Fin 2) (x : E 2) :
    D i probeQuad x =
      (2 * x 0 * (if i = 0 then 1 else 0 : ℝ)) - (2 * x 1 * (if i = 1 then 1 else 0 : ℝ)) := by
  have hc0 : ContDiffAt ℝ 1 (fun y : E 2 => y 0) x := coord_contDiffAt (n := 2) (i := 0)
  have hc1 : ContDiffAt ℝ 1 (fun y : E 2 => y 1) x := coord_contDiffAt (n := 2) (i := 1)
  have hfun : probeQuad = fun y : E 2 => (y 0) ^ 2 + (-((y 1) ^ 2)) := by
    funext y
    rw [probeQuad, sub_eq_add_neg]
  rw [hfun]
  rw [D_add (hc0.pow 2) ((hc1.pow 2).neg)]
  rw [D_pow_two hc0 (i := i)]
  have hneg : D i (fun y : E 2 => -((y 1) ^ 2)) x = -D i (fun y : E 2 => (y 1) ^ 2) x := by
    rw [D]
    change fderiv ℝ (-(fun y : E 2 => (y 1) ^ 2)) x (basis i) = -D i (fun y : E 2 => (y 1) ^ 2) x
    rw [fderiv_neg]
    rfl
  rw [hneg, D_pow_two hc1 (i := i), D_coord i 0, D_coord i 1]
  fin_cases i <;> simp

lemma D2_probeQuad (i j : Fin 2) (x : E 2) :
    D i (D j probeQuad) x =
      (2 * (if i = 0 then 1 else 0 : ℝ) * (if j = 0 then 1 else 0 : ℝ))
        - (2 * (if i = 1 then 1 else 0 : ℝ) * (if j = 1 then 1 else 0 : ℝ)) := by
  have hfun : D j probeQuad = fun x : E 2 =>
      2 * x 0 * (if j = 0 then 1 else 0 : ℝ) - 2 * x 1 * (if j = 1 then 1 else 0 : ℝ) :=
    funext (D_probeQuad j)
  rw [hfun]
  have hfun2 : (fun x : E 2 => 2 * x 0 * (if j = 0 then 1 else 0 : ℝ) - 2 * x 1 * (if j = 1 then 1 else 0 : ℝ)) =
      fun x : E 2 => 2 * x 0 * (if j = 0 then 1 else 0 : ℝ) + (-(2 * x 1 * (if j = 1 then 1 else 0 : ℝ))) := by
    funext x
    rw [sub_eq_add_neg]
  rw [hfun2]
  have hc0 : ContDiffAt ℝ 1 (fun x : E 2 => x 0) x := coord_contDiffAt (n := 2) (i := 0)
  have hc1 : ContDiffAt ℝ 1 (fun x : E 2 => x 1) x := coord_contDiffAt (n := 2) (i := 1)
  have hf : ContDiffAt ℝ 1 (fun x : E 2 => 2 * x 0 * (if j = 0 then 1 else 0 : ℝ)) x := by
    fun_prop
  have hg : ContDiffAt ℝ 1 (fun x : E 2 => -(2 * x 1 * (if j = 1 then 1 else 0 : ℝ))) x := by
    fun_prop
  rw [D_add hf hg]
  have hA : D i (fun x : E 2 => 2 * x 0 * (if j = 0 then 1 else 0 : ℝ)) x
      = 2 * (if j = 0 then 1 else 0 : ℝ) * (if i = 0 then 1 else 0 : ℝ) := by
    calc
      D i (fun x : E 2 => 2 * x 0 * (if j = 0 then 1 else 0 : ℝ)) x
          = D i (fun x : E 2 => (2 * (if j = 0 then 1 else 0 : ℝ)) * x 0) x := by
            congr 1
            funext y
            ring
      _ = (2 * (if j = 0 then 1 else 0 : ℝ)) * D i (fun x : E 2 => x 0) x := by
            exact D_const_mul hc0 (2 * (if j = 0 then 1 else 0 : ℝ)) (i := i)
      _ = 2 * (if j = 0 then 1 else 0 : ℝ) * (if i = 0 then 1 else 0 : ℝ) := by
            rw [D_coord]
  have hB : D i (fun x : E 2 => -(2 * x 1 * (if j = 1 then 1 else 0 : ℝ))) x
      = -(2 * (if j = 1 then 1 else 0 : ℝ) * (if i = 1 then 1 else 0 : ℝ)) := by
    calc
      D i (fun x : E 2 => -(2 * x 1 * (if j = 1 then 1 else 0 : ℝ))) x
          = -D i (fun x : E 2 => 2 * x 1 * (if j = 1 then 1 else 0 : ℝ)) x := by
            rw [D]
            change fderiv ℝ (-(fun x : E 2 => 2 * x 1 * (if j = 1 then 1 else 0 : ℝ))) x (basis i)
              = -D i (fun x : E 2 => 2 * x 1 * (if j = 1 then 1 else 0 : ℝ)) x
            rw [fderiv_neg]
            rfl
      _ = -(2 * (if j = 1 then 1 else 0 : ℝ) * D i (fun x : E 2 => x 1) x) := by
            have hA' : D i (fun x : E 2 => 2 * x 1 * (if j = 1 then 1 else 0 : ℝ)) x
                = (2 * (if j = 1 then 1 else 0 : ℝ)) * D i (fun x : E 2 => x 1) x := by
              calc
                D i (fun x : E 2 => 2 * x 1 * (if j = 1 then 1 else 0 : ℝ)) x
                    = D i (fun x : E 2 => (2 * (if j = 1 then 1 else 0 : ℝ)) * x 1) x := by
                      congr 1
                      funext y
                      ring
                _ = (2 * (if j = 1 then 1 else 0 : ℝ)) * D i (fun x : E 2 => x 1) x := by
                      exact D_const_mul hc1 (2 * (if j = 1 then 1 else 0 : ℝ)) (i := i)
            rw [hA']
      _ = -(2 * (if j = 1 then 1 else 0 : ℝ) * (if i = 1 then 1 else 0 : ℝ)) := by
            rw [D_coord]
  rw [hA, hB]
  fin_cases i <;> fin_cases j <;> simp

lemma lap_probeQuad (x : E 2) : lap probeQuad x = 0 := by
  have h0 := D2_probeQuad (0 : Fin 2) (0 : Fin 2) x
  have h1 := D2_probeQuad (1 : Fin 2) (1 : Fin 2) x
  simp at h0 h1
  rw [lap, Fin.sum_univ_two, D_apply, D_apply, h0, h1]
  norm_num

lemma hessNormSq_probeQuad : hessNormSq probeQuad 0 = 8 := by
  rw [hessNormSq]
  have hij : ∀ i j : Fin 2, D i (D j probeQuad) 0 =
      (2 * (if i = 0 then 1 else 0 : ℝ) * (if j = 0 then 1 else 0 : ℝ))
        - (2 * (if i = 1 then 1 else 0 : ℝ) * (if j = 1 then 1 else 0 : ℝ)) := fun i j => D2_probeQuad i j 0
  simp only [Fin.sum_univ_two]
  rw [hij 0 0, hij 0 1, hij 1 0, hij 1 1]
  simp
  norm_num

theorem probeQuad_harmonic : Harmonic probeQuad := by
  intro x
  exact lap_probeQuad x

theorem probeQuad_bochner_at_zero :
    lap (fun y => ‖grad probeQuad y‖ ^ 2) 0 = 2 * hessNormSq probeQuad 0 + 2 * ⟪grad probeQuad 0, grad (lap probeQuad) 0⟫_ℝ :=
  bochner_identity probeQuad_contDiff 0

theorem probeQuad_subharmonic_at_zero :
    lap (fun y => ‖grad probeQuad y‖ ^ 2) 0 = 16 := by
  rw [harmonic_lap_gradNormSq probeQuad_contDiff probeQuad_harmonic 0, hessNormSq_probeQuad]
  norm_num

theorem probeQuad_subharmonic_at_zero_pos :
    0 < lap (fun y => ‖grad probeQuad y‖ ^ 2) 0 := by
  rw [probeQuad_subharmonic_at_zero]
  norm_num


/-- The energy density of the harmonic probe `x₀² - x₁²` is strictly subharmonic at `0`:
`Δ‖∇u‖²(0) = 16 > 0`, with `‖Hess u‖²(0) = 8`, `Δu = 0`. -/
theorem bochner_probe_summary :
    lap (fun y => ‖grad probeQuad y‖ ^ 2) 0 = 16 ∧
      hessNormSq probeQuad 0 = 8 ∧ Harmonic probeQuad ∧
      lap (fun y => ‖grad probeQuad y‖ ^ 2) 0 = 2 * hessNormSq probeQuad 0 +
        2 * ⟪grad probeQuad 0, grad (lap probeQuad) 0⟫_ℝ := by
  refine ⟨probeQuad_subharmonic_at_zero, ?_, ?_, ?_⟩
  · exact hessNormSq_probeQuad
  · exact probeQuad_harmonic
  · have hlapf : lap probeQuad = fun _ : E 2 => 0 := funext lap_probeQuad
    rw [harmonic_lap_gradNormSq probeQuad_contDiff probeQuad_harmonic 0, hessNormSq_probeQuad]
    rw [show ⟪grad probeQuad 0, grad (lap probeQuad) 0⟫_ℝ = 0 by
      rw [hlapf]
      simp [grad, D]]
    norm_num

end BochnerProbe

end

end Poincare.Audit.D11
