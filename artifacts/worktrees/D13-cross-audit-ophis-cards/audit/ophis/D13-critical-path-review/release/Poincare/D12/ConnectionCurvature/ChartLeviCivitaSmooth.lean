import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.StdBasis
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaForm

/-!
# Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth

**D12-connection-curvature: the smooth (x-dependent) chart Levi-Civita connection from
smooth metric coefficients on a real chart.**

This module completes the chart construction of `ChartLeviCivita`/`ChartLeviCivitaForm`
by making the chart point `x` a variable. On the real chart model space
`ChartPoint ι = ι → ℝ` (a finite-dimensional real vector space of chart coordinates,
dimension `card ι`) a **smooth chart metric datum** `SmoothChartData ι` consists of

* smooth coefficient families `g, gInv : ChartPoint ι → ι → ι → ℝ`
  (`ContDiff ℝ ∞`, the infinitely-smooth order; note that in this mathlib revision the
  smooth order is the `∞` of the two `ℕ∞ω` tops, not the analytic `⊤`);
* the pointwise dual-metric hypotheses `g_symm`, `gInv_symm`, `inv_mul`.

The metric derivative datum is **derived**, not assumed: `dFamily x i j k` is the actual
Frechet derivative `fderiv (G_{jk}) x (eᵢ)` of the coefficient function in the
coordinate direction `eᵢ = Pi.single i 1`. Its symmetry in the differentiated slots
(`dFamily_symm`, the `d_symm` hypothesis of the pointwise datum) is **proved** from the
pointwise symmetry of the coefficients by uniqueness of Frechet derivatives — no
Schwarz hypothesis is used anywhere in this module (second derivatives never appear).

From the datum the module constructs

* `christoffelFamily`: the Christoffel symbols `Γᵏᵢⱼ(x)` as functions on the chart;
* `nabla`: the covariant derivative on **smooth vector fields**
  `(∇_X Y)ᵏ(x) = ∂_{X(x)}Yᵏ(x) + Σᵢⱼ Γᵏᵢⱼ(x) Xⁱ(x) Yʲ(x)`;
* `lieBracket`: the Lie bracket of fields `[X,Y]ᵏ(x) = ∂_{X(x)}Yᵏ(x) − ∂_{Y(x)}Xᵏ(x)`;
* `formField`: the field pairing `gₓ(Y(x), Z(x))`.

and proves, with every proof reducing the derivative part to the (proved) Frechet
product rule and the Christoffel part to the pointwise algebraic identities of
`ChartLeviCivita`/`ChartLeviCivitaForm` instantiated at each `x`:

* **`christoffelFamily_smooth`** — the Christoffel symbols are smooth functions on the
  chart (the derivative datum is smooth because the Frechet derivative of a smooth
  function is smooth, using `ContDiff.fderiv_right` and the `ℕ∞ω` identity `∞ + 1 = ∞`);
* **`nabla_smooth`**, `lieBracket_smooth` — the connection and bracket map smooth fields
  to smooth fields;
* **`nabla_smul`** — the Leibniz rule `∇_X (f • Y) = f • ∇_X Y + X(f) • Y` for smooth
  scalar functions `f`, i.e. the connection is a derivation in the field slot;
* **`nabla_torsionFree`** — `∇_X Y − ∇_Y X = [X,Y]` (the derivative parts are exactly
  the Lie bracket; the Christoffel parts cancel by `christoffel_symm`);
* **`nabla_metricCompatible`** — for smooth fields `Y, Z`, at every chart point `x`:
  `fderiv (z ↦ g_z(Y(z),Z(z))) x (X(x)) = gₓ(∇_X Y(x), Z(x)) + gₓ(Y(x), ∇_X Z(x))`,
  i.e. metric compatibility of the smooth chart Levi-Civita connection with the actual
  Frechet derivative of the pairing on the left. The proof expands the pairing into
  coefficients, applies the proved three-factor Frechet product rule
  (`fderiv_mul_mul_apply`), and reduces the Christoffel part to
  `chartMetricCompatible_form` with the derived derivative datum
  (`dFormOf =` directional-derivative expansion via `fderiv_apply_eq_sum_single` and the
  triple-sum reindexing `sum_three_cycle`).

The classical source of the construction is do Carmo, *Riemannian Geometry*, Ch. 2, and
Lee, *Riemannian Manifolds*, Ch. 4–5. The algebraic core follows the DoCarmo formalized
library (frenzymath snapshot `bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0).

## Honest boundary

* The chart model is the **global coordinate space** `ι → ℝ` (one chart covering the
  model); a patched-atlas manifold statement is out of scope and recorded as a
  dependency.
* The datum does not assume positive definiteness: compatibility and torsion-freeness do
  not need it (the 1D model in `ChartModel1D` witnesses a positive instance).
* The curvature component formula (`Rⁱⱼₖₗ = ∂ₖΓⁱⱼₗ − ∂ₗΓⁱⱼₖ + …`) needs derivatives of
  the Christoffel family and is recorded as the next dependency (`next_dependency_requests`
  in the checkpoint), with the exact statement in this docstring's sibling card.
* No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` appears in this file.
-/

open scoped BigOperators
open scoped ContDiff

noncomputable section

namespace Poincare
namespace D12
namespace ConnectionCurvature

universe w

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The real chart model space:** the coordinates `ι → ℝ` of a real chart of
dimension `card ι`. -/
abbrev ChartPoint (ι : Type w) := ι → ℝ

/-- **Smooth vector fields on the chart:** functions from the chart to the coordinate
vectors. -/
abbrev VectorField (ι : Type w) := ChartPoint ι → ChartPoint ι

/-! ## Frechet-derivative and sum infrastructure -/

/-- The three-factor product rule for Frechet derivatives of `ℝ`-valued functions on the
chart model (derived from mathlib's two-factor `fderiv_mul`; the two differentiability
hypotheses of the middle product are discharged by `DifferentiableAt.mul`). -/
lemma fderiv_mul_mul_apply (f g h : ChartPoint ι → ℝ) (x v : ChartPoint ι)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (fun y => f y * g y * h y) x v
      = f x * g x * fderiv ℝ h x v + f x * h x * fderiv ℝ g x v
        + g x * h x * fderiv ℝ f x v := by
  have hgh : DifferentiableAt ℝ (fun y => g y * h y) x := hg.mul hh
  have h1 : fderiv ℝ (fun y => f y * (g y * h y)) x =
      f x • fderiv ℝ (fun y => g y * h y) x + (g x * h x) • fderiv ℝ f x :=
    fderiv_mul hf hgh
  have h2 : fderiv ℝ (fun y => g y * h y) x = g x • fderiv ℝ h x + h x • fderiv ℝ g x :=
    fderiv_mul hg hh
  have hfun : (fun y => f y * (g y * h y)) = fun y => f y * g y * h y := by
    funext y
    ring
  calc
    fderiv ℝ (fun y => f y * g y * h y) x v
        = fderiv ℝ (fun y => f y * (g y * h y)) x v := by rw [hfun]
    _ = (f x • fderiv ℝ (fun y => g y * h y) x + (g x * h x) • fderiv ℝ f x) v := by
          rw [h1]
    _ = (f x • (g x • fderiv ℝ h x + h x • fderiv ℝ g x) + (g x * h x) • fderiv ℝ f x) v := by
          rw [h2]
    _ = f x * g x * fderiv ℝ h x v + f x * h x * fderiv ℝ g x v
          + g x * h x * fderiv ℝ f x v := by
          simp
          ring

/-- Applying a linear map to a chart vector expands along the standard coordinate basis
`(Pi.single i 1)ᵢ` (the explicit finite-dimensional structure of the chart model). -/
lemma linMap_apply_eq_sum_single (L : ChartPoint ι →ₗ[ℝ] ℝ) (v : ChartPoint ι) :
    L v = ∑ k : ι, v k * L (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)) := by
  conv_lhs => rw [← (Pi.basisFun ℝ ι).sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_repr, Pi.basisFun_apply]

/-- The Frechet derivative in a field direction expands along the coordinate directions:
`∂_v f = Σₖ vᵏ ∂_{eₖ} f` (linearity of `fderiv` plus `linMap_apply_eq_sum_single`). -/
lemma fderiv_apply_eq_sum_single (f : ChartPoint ι → ℝ) (x v : ChartPoint ι) :
    fderiv ℝ f x v =
      ∑ k : ι, v k * fderiv ℝ f x (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ)) := by
  simpa using linMap_apply_eq_sum_single (fderiv ℝ f x : ChartPoint ι →L[ℝ] ℝ) v

/-- Splitting a double sum of a two-term summand into two double sums. -/
lemma sum_add_split (f g : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, (f i j + g i j)) = (∑ i : ι, ∑ j : ι, f i j) + ∑ i : ι, ∑ j : ι, g i j := by
  simp only [Finset.sum_add_distrib]

/-- **Triple-sum reindexing by the 3-cycle `(i,j,k) ↦ (k,i,j)`.** Both sides expand via
`Finset.sum_product'` to the same flat sum over the product type. -/
lemma sum_three_cycle (f : ι → ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, ∑ k : ι, f i j k) = ∑ k : ι, ∑ i : ι, ∑ j : ι, f k i j := by
  classical
  calc
    (∑ i : ι, ∑ j : ι, ∑ k : ι, f i j k)
        = ∑ q : ι × ι × ι, f q.1 q.2.1 q.2.2 := by
          calc
            (∑ i : ι, ∑ j : ι, ∑ k : ι, f i j k)
                = ∑ i : ι, ∑ p : ι × ι, f i p.1 p.2 := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset ι)) (f := fun j k => f i j k)).symm
            _ = ∑ q : ι × ι × ι, f q.1 q.2.1 q.2.2 := by
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset (ι × ι))) (f := fun i p => f i p.1 p.2)).symm
    _ = ∑ k : ι, ∑ i : ι, ∑ j : ι, f k i j := by
          calc
            (∑ q : ι × ι × ι, f q.1 q.2.1 q.2.2)
                = ∑ k : ι, ∑ p : ι × ι, f k p.1 p.2 := by
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset (ι × ι))) (f := fun k p => f k p.1 p.2))
            _ = ∑ k : ι, ∑ i : ι, ∑ j : ι, f k i j := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset ι)) (f := fun i j => f k i j))

/-- **Triple-sum reindexing moving the first sum to the last position:**
`∑ₖ ∑ᵢ ∑ⱼ f k i j = ∑ᵢ ∑ⱼ ∑ₖ f k i j` (the same flattening argument; this is the
two-step move used to align the derivative-of-metric triple sum with the
`Σₖ Xₖ ∂ₖ g_{ij}` coordinate expansion in `nabla_metricCompatible`). -/
lemma sum_cycle_first_to_last (f : ι → ι → ι → ℝ) :
    (∑ k : ι, ∑ i : ι, ∑ j : ι, f k i j) = ∑ i : ι, ∑ j : ι, ∑ k : ι, f k i j := by
  classical
  calc
    (∑ k : ι, ∑ i : ι, ∑ j : ι, f k i j)
        = ∑ q : ι × ι × ι, f q.1 q.2.1 q.2.2 := by
          calc
            (∑ k : ι, ∑ i : ι, ∑ j : ι, f k i j)
                = ∑ k : ι, ∑ p : ι × ι, f k p.1 p.2 := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset ι)) (f := fun i j => f k i j)).symm
            _ = ∑ q : ι × ι × ι, f q.1 q.2.1 q.2.2 := by
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset (ι × ι))) (f := fun k p => f k p.1 p.2)).symm
    _ = ∑ i : ι, ∑ j : ι, ∑ k : ι, f k i j := by
          calc
            (∑ q : ι × ι × ι, f q.1 q.2.1 q.2.2)
                = ∑ k : ι, ∑ p : ι × ι, f k p.1 p.2 := by
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset (ι × ι))) (f := fun k p => f k p.1 p.2))
            _ = ∑ p : ι × ι, ∑ k : ι, f k p.1 p.2 := by
                  rw [Finset.sum_comm]
            _ = ∑ i : ι, ∑ j : ι, ∑ k : ι, f k i j := by
                  simpa using (Finset.sum_product' (s := (Finset.univ : Finset ι))
                    (t := (Finset.univ : Finset ι)) (f := fun i j => ∑ k : ι, f k i j))

/-! ## The smooth chart datum and the derived derivative data -/

/-- **Smooth chart metric datum.** Smooth coefficient families `g`, `gInv` on the real
chart `ChartPoint ι` satisfying the dual-metric identities pointwise. The metric
derivative data is *derived* from `g` (see `dFamily`), not assumed. -/
structure SmoothChartData (ι : Type w) [Fintype ι] [DecidableEq ι] where
  /-- Metric coefficients `G_{ij}(x)`. -/
  g : ChartPoint ι → ι → ι → ℝ
  /-- Inverse-metric coefficients `G^{kl}(x)`. -/
  gInv : ChartPoint ι → ι → ι → ℝ
  /-- The coefficient families are infinitely smooth on the chart. -/
  g_smooth : ContDiff ℝ ∞ g
  /-- The inverse-metric coefficient families are infinitely smooth on the chart. -/
  gInv_smooth : ContDiff ℝ ∞ gInv
  /-- Pointwise symmetry of the metric coefficients. -/
  g_symm : ∀ x i j, g x i j = g x j i
  /-- Pointwise symmetry of the inverse-metric coefficients. -/
  gInv_symm : ∀ x i j, gInv x i j = gInv x j i
  /-- The pointwise dual-metric property: `Σₗ G^{kl}(x) G_{lj}(x) = δ_{kj}`. -/
  inv_mul : ∀ x k j, (∑ l : ι, gInv x k l * g x l j) = if k = j then 1 else 0

namespace SmoothChartData

variable (c : SmoothChartData ι)

/-- Each metric-coefficient component is a smooth function on the chart. -/
theorem g_component_smooth (i j : ι) :
    ContDiff ℝ ∞ (fun x : ChartPoint ι => c.g x i j) :=
  (contDiff_pi.mp ((contDiff_pi.mp c.g_smooth) i)) j

/-- Each inverse-metric-coefficient component is a smooth function on the chart. -/
theorem gInv_component_smooth (i j : ι) :
    ContDiff ℝ ∞ (fun x : ChartPoint ι => c.gInv x i j) :=
  (contDiff_pi.mp ((contDiff_pi.mp c.gInv_smooth) i)) j

/-- **The derived metric derivative datum:** `dFamily x i j k = ∂_{eᵢ} G_{jk}(x)`, the
Frechet derivative of the coefficient `G_{jk}` at `x` in the coordinate direction
`eᵢ = Pi.single i 1`. -/
def dFamily (x : ChartPoint ι) (i j k : ι) : ℝ :=
  fderiv ℝ (fun y : ChartPoint ι => c.g y j k) x (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))

/-- **Smoothness of the derived derivative datum.** The Frechet derivative of a smooth
coefficient is smooth (`ContDiff.fderiv_right`), using the `ℕ∞ω` identity
`∞ + 1 = ∞` (`ENat.coe_top_add_one`, a `simp` lemma). -/
theorem dFamily_smooth (i j k : ι) :
    ContDiff ℝ ∞ (fun x : ChartPoint ι => c.dFamily x i j k) := by
  have hgk : ContDiff ℝ (∞ + 1) (fun y : ChartPoint ι => c.g y j k) := by
    simpa using c.g_component_smooth j k
  have hfd : ContDiff ℝ ∞ (fun x : ChartPoint ι => fderiv ℝ (fun y : ChartPoint ι => c.g y j k) x) :=
    ContDiff.fderiv_right hgk le_rfl
  exact hfd.clm_apply (contDiff_const (c := Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))

/-- **The derived derivative datum is symmetric in the differentiated slots**
(`dFamily x i j k = dFamily x i k j`): the pointwise symmetry `g_symm` of the
coefficients forces equality of the two Frechet derivatives by function extensionality.
This discharges the `d_symm` field of the pointwise `ChartMetricCoefficients` — no
Schwarz hypothesis is used. -/
theorem dFamily_symm (x : ChartPoint ι) (i j k : ι) :
    c.dFamily x i j k = c.dFamily x i k j := by
  have hf : (fun y : ChartPoint ι => c.g y j k) = fun y => c.g y k j := by
    funext y
    exact c.g_symm y j k
  unfold dFamily
  rw [hf]

/-- **The pointwise chart-coefficient datum at `x`**, with the derivative data being the
actual Frechet derivatives of the coefficients. All four hypotheses of
`ChartMetricCoefficients` are discharged pointwise (`d_symm` by the *proved*
`dFamily_symm`). -/
def chartCoefficients (x : ChartPoint ι) : ChartMetricCoefficients ι where
  g := c.g x
  gInv := c.gInv x
  d := c.dFamily x
  g_symm := c.g_symm x
  gInv_symm := c.gInv_symm x
  inv_mul := c.inv_mul x
  d_symm := c.dFamily_symm x

/-! ## The Christoffel family and its smoothness -/

/-- **The Christoffel symbols as functions on the chart:**
`Γᵏᵢⱼ(x) = Σₗ G^{kl}(x) A_{lij}(x)` (the pointwise Christoffel symbols of
`ChartLeviCivita`). -/
def christoffelFamily (x : ChartPoint ι) (k i j : ι) : ℝ :=
  (c.chartCoefficients x).christoffel k i j

/-- Pointwise symmetry `Γᵏᵢⱼ(x) = Γᵏⱼᵢ(x)` (coordinate torsion-freeness), from the
pointwise `christoffel_symm`. -/
theorem christoffelFamily_symm (x : ChartPoint ι) (k i j : ι) :
    c.christoffelFamily x k i j = c.christoffelFamily x k j i := by
  unfold christoffelFamily
  exact ChartMetricCoefficients.christoffel_symm (c.chartCoefficients x) k i j

/-- **The Christoffel symbols are smooth functions on the chart.** This is the headline
smoothness theorem of the construction: from smooth coefficient families `(g, g⁻¹)` the
Christoffel family is built by finite sums of products of smooth components and the
smooth derived derivative datum. -/
theorem christoffelFamily_smooth (k i j : ι) :
    ContDiff ℝ ∞ (fun x : ChartPoint ι => c.christoffelFamily x k i j) := by
  have hΓ : (fun x : ChartPoint ι => c.christoffelFamily x k i j) = fun x =>
      ∑ l : ι, c.gInv x k l * ((2 : ℝ)⁻¹ *
        (c.dFamily x i j l + c.dFamily x j i l + -c.dFamily x l i j)) := by
    funext x
    simp only [christoffelFamily, chartCoefficients, ChartMetricCoefficients.christoffel,
      ChartMetricCoefficients.christoffelLower, sub_eq_add_neg, one_div]
  rw [hΓ]
  simpa using (ContDiff.sum (s := (Finset.univ : Finset ι)) (by
    intro l hl
    refine ContDiff.mul ?_ ?_
    · exact c.gInv_component_smooth k l
    · exact ContDiff.const_smul ((2 : ℝ)⁻¹)
        (ContDiff.add (ContDiff.add (c.dFamily_smooth i j l) (c.dFamily_smooth j i l))
          (ContDiff.neg (c.dFamily_smooth l i j)))))

/-- **The coordinate form of `∇g = 0` for the smooth datum, pointwise:** the derived
derivative of the coefficients is recovered from the Christoffel contraction
(`metricDerivative_christoffel` instantiated at every chart point). -/
theorem christoffelFamily_metricDerivative (x : ChartPoint ι) (i j k : ι) :
    c.dFamily x k i j = ∑ m : ι, (c.g x m j * c.christoffelFamily x m k i +
      c.g x i m * c.christoffelFamily x m k j) := by
  have h := ChartMetricCoefficients.metricDerivative_christoffel (c.chartCoefficients x) i j k
  simpa [christoffelFamily, chartCoefficients] using h

/-! ## The field-level connection -/

/-- **The smooth chart Levi-Civita covariant derivative on smooth fields:**
`(∇_X Y)ᵏ(x) = ∂_{X(x)}Yᵏ(x) + Σᵢⱼ Γᵏᵢⱼ(x) Xⁱ(x) Yʲ(x)`. -/
def nabla (X Y : VectorField ι) : VectorField ι :=
  fun x k => fderiv ℝ (fun z : ChartPoint ι => Y z k) x (X x) +
    ∑ i : ι, ∑ j : ι, c.christoffelFamily x k i j * X x i * Y x j

/-- The defining component formula of the field-level connection. -/
theorem nabla_apply (X Y : VectorField ι) (x : ChartPoint ι) (k : ι) :
    c.nabla X Y x k = fderiv ℝ (fun z : ChartPoint ι => Y z k) x (X x) +
      ∑ i : ι, ∑ j : ι, c.christoffelFamily x k i j * X x i * Y x j := rfl

/-- **The covariant derivative of smooth fields is a smooth field.** -/
theorem nabla_smooth {X Y : VectorField ι} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (c.nabla X Y) := by
  rw [contDiff_pi]
  intro k
  unfold nabla
  refine ContDiff.add ?_ ?_
  · have hYk : ContDiff ℝ (∞ + 1) (fun z : ChartPoint ι => Y z k) := by
      simpa using (contDiff_pi.mp hY) k
    have hfd : ContDiff ℝ ∞ (fun x : ChartPoint ι =>
        fderiv ℝ (fun z : ChartPoint ι => Y z k) x) := ContDiff.fderiv_right hYk le_rfl
    exact hfd.clm_apply hX
  · simpa using (ContDiff.sum (s := (Finset.univ : Finset ι)) (by
      intro i hi
      refine ContDiff.sum (s := (Finset.univ : Finset ι)) ?_
      intro j hj
      exact ContDiff.mul (ContDiff.mul (c.christoffelFamily_smooth k i j)
        ((contDiff_pi.mp hX) i)) ((contDiff_pi.mp hY) j)))

/-- **The Lie bracket of smooth fields on the chart** (coordinate formula):
`[X,Y]ᵏ(x) = ∂_{X(x)}Yᵏ(x) − ∂_{Y(x)}Xᵏ(x)`. -/
def lieBracket (_c : SmoothChartData ι) (X Y : VectorField ι) : VectorField ι :=
  fun x k => fderiv ℝ (fun z : ChartPoint ι => Y z k) x (X x) -
    fderiv ℝ (fun z : ChartPoint ι => X z k) x (Y x)

/-- The Lie bracket of smooth fields is a smooth field. -/
theorem lieBracket_smooth {X Y : VectorField ι} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (c.lieBracket X Y) := by
  rw [contDiff_pi]
  intro k
  unfold lieBracket
  refine ContDiff.sub ?_ ?_
  · have hYk : ContDiff ℝ (∞ + 1) (fun z : ChartPoint ι => Y z k) := by
      simpa using (contDiff_pi.mp hY) k
    exact (ContDiff.fderiv_right hYk le_rfl).clm_apply hX
  · have hXk : ContDiff ℝ (∞ + 1) (fun z : ChartPoint ι => X z k) := by
      simpa using (contDiff_pi.mp hX) k
    exact (ContDiff.fderiv_right hXk le_rfl).clm_apply hY

/-- **Torsion-freeness of the smooth chart Levi-Civita connection:**
`∇_X Y − ∇_Y X = [X,Y]` at every chart point. The derivative parts are exactly the Lie
bracket; the Christoffel parts cancel by `christoffelFamily_symm` (the same
coordinate-frame argument as `chartTorsionFree_form`, with no extra hypothesis). -/
theorem nabla_torsionFree (X Y : VectorField ι) (x : ChartPoint ι) (k : ι) :
    c.nabla X Y x k - c.nabla Y X x k = c.lieBracket X Y x k := by
  unfold nabla lieBracket
  have hΓ : (∑ i : ι, ∑ j : ι, c.christoffelFamily x k i j * Y x i * X x j) =
      ∑ i : ι, ∑ j : ι, c.christoffelFamily x k i j * X x i * Y x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [c.christoffelFamily_symm x k j i]
    ring
  rw [hΓ]
  ring

/-- On constant-coefficient fields the field-level connection agrees with the pointwise
Christoffel connection `nablaOf` of `ChartLeviCivitaForm` (the derivative part
vanishes). This is the consistency bridge between the smooth module and its algebraic
core. -/
theorem nabla_const_apply (X0 Y0 : ChartPoint ι) (x : ChartPoint ι) (k : ι) :
    c.nabla (fun _ : ChartPoint ι => X0) (fun _ : ChartPoint ι => Y0) x k =
      nablaOf (c.chartCoefficients x) X0 Y0 k := by
  simp only [nabla, nablaOf_apply, fderiv_const_apply, christoffelFamily]
  simp

/-- **The Leibniz rule in the field slot.** For a smooth scalar function `f` on the
chart and smooth fields, `∇_X (f • Y) = f • ∇_X Y + X(f) • Y` where
`X(f)(x) = fderiv f x (X x)`. The proof is the two-factor Frechet product rule in the
derivative slot plus the Christoffel part factoring out `f x`. -/
theorem nabla_smul (f : ChartPoint ι → ℝ) (hf : ContDiff ℝ 1 f)
    (X Y : VectorField ι) (hY : ContDiff ℝ 1 Y) (x : ChartPoint ι) :
    c.nabla X (f • Y) x = f x • c.nabla X Y x + fderiv ℝ f x (X x) • Y x := by
  ext k
  unfold nabla
  have hfun : (fun z : ChartPoint ι => (f • Y) z k) = fun z => f z * Y z k := by
    simp
  have hdiff_f : DifferentiableAt ℝ f x := hf.contDiffAt.differentiableAt_one
  have hdiff_Y : DifferentiableAt ℝ (fun z : ChartPoint ι => Y z k) x :=
    ((contDiff_pi.mp hY) k).contDiffAt.differentiableAt_one
  have hmul : fderiv ℝ (fun z : ChartPoint ι => f z * Y z k) x =
      f x • fderiv ℝ (fun z : ChartPoint ι => Y z k) x + (Y x k) • fderiv ℝ f x :=
    fderiv_mul hdiff_f hdiff_Y
  have hmulv : fderiv ℝ (fun z : ChartPoint ι => (f • Y) z k) x (X x)
      = f x * fderiv ℝ (fun z : ChartPoint ι => Y z k) x (X x) + Y x k * fderiv ℝ f x (X x) := by
    rw [hfun]
    calc
      fderiv ℝ (fun z => f z * Y z k) x (X x)
          = (f x • fderiv ℝ (fun z => Y z k) x + (Y x k) • fderiv ℝ f x) (X x) := by
            rw [hmul]
      _ = f x * fderiv ℝ (fun z => Y z k) x (X x) + Y x k * fderiv ℝ f x (X x) := by
            simp
  have hΓsmul : (∑ i : ι, ∑ j : ι, c.christoffelFamily x k i j * X x i * (f • Y) x j)
      = f x * (∑ i : ι, ∑ j : ι, c.christoffelFamily x k i j * X x i * Y x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hs : (f • Y) x j = f x * Y x j := by simp
    rw [hs]
    ring
  rw [hmulv, hΓsmul]
  simp
  ring

/-- **The metric pairing of fields at a chart point:** `gₓ(Y(x), Z(x))`. -/
def formField (x : ChartPoint ι) (Y Z : ChartPoint ι) : ℝ :=
  formOf (c.chartCoefficients x) Y Z

/-! ## Metric compatibility of the field-level connection -/

/-- **Metric compatibility of the smooth chart Levi-Civita connection.** For smooth
fields `Y, Z` and any field `X`, at every chart point `x`:

`fderiv (z ↦ g_z(Y(z), Z(z))) x (X(x)) = gₓ((∇_X Y)(x), Z(x)) + gₓ(Y(x), (∇_X Z)(x))`

— the derivative of the field pairing along `X(x)` is split by the (proved) three-factor
Frechet product rule into the pairing of `∇_X Y` with `Z` and of `Y` with `∇_X Z`. The
Christoffel part reduces, pointwise, to the algebraic identity
`chartMetricCompatible_form` with the *derived* derivative datum `dFamily` (whose
`d_symm` is `dFamily_symm`); the derivative-of-metric part is reindexed by
`fderiv_apply_eq_sum_single` and `sum_three_cycle`. No Schwarz hypothesis is used. -/
theorem nabla_metricCompatible (X Y Z : VectorField ι)
    (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (x : ChartPoint ι) :
    fderiv ℝ (fun z : ChartPoint ι => c.formField z (Y z) (Z z)) x (X x) =
      c.formField x (c.nabla X Y x) (Z x) + c.formField x (Y x) (c.nabla X Z x) := by
  have hdiff_g : ∀ i j : ι, DifferentiableAt ℝ (fun z : ChartPoint ι => c.g z i j) x := by
    intro i j
    exact ((ContDiff.of_le (c.g_component_smooth i j)
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt).differentiableAt_one
  have hdiff_Y : ∀ i : ι, DifferentiableAt ℝ (fun z : ChartPoint ι => Y z i) x := by
    intro i
    exact ((ContDiff.of_le ((contDiff_pi.mp hY) i)
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt).differentiableAt_one
  have hdiff_Z : ∀ i : ι, DifferentiableAt ℝ (fun z : ChartPoint ι => Z z i) x := by
    intro i
    exact ((ContDiff.of_le ((contDiff_pi.mp hZ) i)
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt).differentiableAt_one
  -- Left side: derivative of the pairing = double sum of three-factor product rules.
  have hL : fderiv ℝ (fun z : ChartPoint ι => c.formField z (Y z) (Z z)) x (X x)
      = ∑ i : ι, ∑ j : ι, (c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
          + c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
          + fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j) := by
    have hfZ : (fun z : ChartPoint ι => c.formField z (Y z) (Z z)) =
        fun z => ∑ i : ι, ∑ j : ι, c.g z i j * Y z i * Z z j := by
      funext z
      simp only [formField, formOf_apply, chartCoefficients]
    rw [hfZ]
    calc
      fderiv ℝ (fun z => ∑ i : ι, ∑ j : ι, c.g z i j * Y z i * Z z j) x (X x)
          = fderiv ℝ (∑ i ∈ (Finset.univ : Finset ι),
              (fun z => ∑ j : ι, c.g z i j * Y z i * Z z j)) x (X x) := by
            congr 2
            funext z
            simp
      _ = (∑ i ∈ (Finset.univ : Finset ι),
              fderiv ℝ (fun z => ∑ j : ι, c.g z i j * Y z i * Z z j) x) (X x) := by
            rw [fderiv_sum]
            intro i hi
            have hfun : (fun z => ∑ j : ι, c.g z i j * Y z i * Z z j)
                = ∑ j ∈ (Finset.univ : Finset ι), (fun z => c.g z i j * Y z i * Z z j) := by
              funext z
              simp
            rw [hfun]
            exact DifferentiableAt.sum (fun j hj => ((hdiff_g i j).mul (hdiff_Y i)).mul (hdiff_Z j))
      _ = ∑ i : ι, ∑ j : ι, (c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
            + c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
            + fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j) := by
            simp
            apply Finset.sum_congr rfl
            intro i hi
            have hbridge : fderiv ℝ (fun z : ChartPoint ι => ∑ j : ι, c.g z i j * Y z i * Z z j) x
                = fderiv ℝ (∑ j ∈ (Finset.univ : Finset ι),
                    (fun z : ChartPoint ι => c.g z i j * Y z i * Z z j)) x := by
              congr 1
              funext z
              simp
            rw [hbridge]
            rw [fderiv_sum]
            · simp
              apply Finset.sum_congr rfl
              intro j hj
              rw [fderiv_mul_mul_apply (f := fun z : ChartPoint ι => c.g z i j)
                (g := fun z : ChartPoint ι => Y z i) (h := fun z : ChartPoint ι => Z z j)
                (hf := hdiff_g i j) (hg := hdiff_Y i) (hh := hdiff_Z j) (v := X x)]
              ring
            · intro j hj
              exact ((hdiff_g i j).mul (hdiff_Y i)).mul (hdiff_Z j)
  -- Right side: the two pairings expanded into coefficient sums.
  have hRY : c.formField x (c.nabla X Y x) (Z x)
      = ∑ i : ι, ∑ j : ι, (c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
          + c.g x i j * (∑ a : ι, ∑ b : ι, c.christoffelFamily x i a b * X x a * Y x b) * Z x j) := by
    simp only [formField, formOf_apply, chartCoefficients]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold nabla
    ring
  have hRZ : c.formField x (Y x) (c.nabla X Z x)
      = ∑ i : ι, ∑ j : ι, (c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
          + c.g x i j * Y x i * (∑ a : ι, ∑ b : ι, c.christoffelFamily x j a b * X x a * Z x b)) := by
    simp only [formField, formOf_apply, chartCoefficients]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold nabla
    ring
  -- The Christoffel part equals the pointwise algebraic identity at x.
  have hGamma : (∑ i : ι, ∑ j : ι, c.g x i j *
          (∑ a : ι, ∑ b : ι, c.christoffelFamily x i a b * X x a * Y x b) * Z x j)
        + (∑ i : ι, ∑ j : ι, c.g x i j * Y x i *
          (∑ a : ι, ∑ b : ι, c.christoffelFamily x j a b * X x a * Z x b))
      = dFormOf (c.chartCoefficients x) (X x) (Y x) (Z x) := by
    have h := chartMetricCompatible_form (c.chartCoefficients x) (X x) (Y x) (Z x)
    simpa [formOf_apply, nablaOf_apply, christoffelFamily, chartCoefficients] using h
  -- The derivative-of-metric double sum equals dFormOf via the coordinate expansion.
  have hdForm : dFormOf (c.chartCoefficients x) (X x) (Y x) (Z x)
      = ∑ i : ι, ∑ j : ι, fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j := by
    calc
      dFormOf (c.chartCoefficients x) (X x) (Y x) (Z x)
          = ∑ i : ι, ∑ j : ι, ∑ k : ι, c.dFamily x i j k * X x i * Y x j * Z x k := by
            simp only [dFormOf, chartCoefficients]
      _ = ∑ k : ι, ∑ i : ι, ∑ j : ι, c.dFamily x k i j * X x k * Y x i * Z x j := by
            exact sum_three_cycle (fun k i j => c.dFamily x k i j * X x k * Y x i * Z x j)
      _ = ∑ i : ι, ∑ j : ι, (∑ k : ι, X x k * c.dFamily x k i j) * Y x i * Z x j := by
            rw [sum_cycle_first_to_last
              (fun k i j => c.dFamily x k i j * X x k * Y x i * Z x j)]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            have hm : (∑ k : ι, c.dFamily x k i j * X x k * Y x i * Z x j)
                = (∑ k : ι, (X x k * c.dFamily x k i j) * (Y x i * Z x j)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
            rw [hm, ← Finset.sum_mul]
            ring
      _ = ∑ i : ι, ∑ j : ι, fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [fderiv_apply_eq_sum_single (f := fun z : ChartPoint ι => c.g z i j)
              (x := x) (v := X x)]
            simp only [dFamily]
  -- Split the pairing expansions into the three canonical double sums.
  have hRsplit : c.formField x (c.nabla X Y x) (Z x) + c.formField x (Y x) (c.nabla X Z x)
      = (∑ i : ι, ∑ j : ι, c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
          + ∑ i : ι, ∑ j : ι, c.g x i j * (∑ a : ι, ∑ b : ι, c.christoffelFamily x i a b * X x a * Y x b) * Z x j)
        + (∑ i : ι, ∑ j : ι, c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
          + ∑ i : ι, ∑ j : ι, c.g x i j * Y x i * (∑ a : ι, ∑ b : ι, c.christoffelFamily x j a b * X x a * Z x b)) := by
    rw [hRY, hRZ]
    rw [sum_add_split (f := fun i j => c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j)
      (g := fun i j => c.g x i j * (∑ a : ι, ∑ b : ι, c.christoffelFamily x i a b * X x a * Y x b) * Z x j)]
    rw [sum_add_split (f := fun i j => c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x))
      (g := fun i j => c.g x i j * Y x i * (∑ a : ι, ∑ b : ι, c.christoffelFamily x j a b * X x a * Z x b))]
  -- Reassociate, replace the Christoffel sums by dFormOf, then by the derivative sum.
  have hR : c.formField x (c.nabla X Y x) (Z x) + c.formField x (Y x) (c.nabla X Z x)
      = ∑ i : ι, ∑ j : ι, c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
        + ∑ i : ι, ∑ j : ι, c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
        + ∑ i : ι, ∑ j : ι, fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j := by
    rw [hRsplit]
    rw [show ((∑ i : ι, ∑ j : ι, c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j)
        + ∑ i : ι, ∑ j : ι, c.g x i j * (∑ a : ι, ∑ b : ι, c.christoffelFamily x i a b * X x a * Y x b) * Z x j)
      + ((∑ i : ι, ∑ j : ι, c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x))
        + ∑ i : ι, ∑ j : ι, c.g x i j * Y x i * (∑ a : ι, ∑ b : ι, c.christoffelFamily x j a b * X x a * Z x b))
      = (∑ i : ι, ∑ j : ι, c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j)
        + ∑ i : ι, ∑ j : ι, c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
        + ((∑ i : ι, ∑ j : ι, c.g x i j * (∑ a : ι, ∑ b : ι, c.christoffelFamily x i a b * X x a * Y x b) * Z x j)
          + ∑ i : ι, ∑ j : ι, c.g x i j * Y x i * (∑ a : ι, ∑ b : ι, c.christoffelFamily x j a b * X x a * Z x b)) from by
      ring]
    rw [hGamma]
    rw [hdForm]
  -- Assemble: the left side expands to the same three canonical double sums.
  calc
    fderiv ℝ (fun z : ChartPoint ι => c.formField z (Y z) (Z z)) x (X x)
        = ∑ i : ι, ∑ j : ι, (c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
            + c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
            + fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j) := hL
    _ = ∑ i : ι, ∑ j : ι, c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
        + ∑ i : ι, ∑ j : ι, c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x)
        + ∑ i : ι, ∑ j : ι, fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j := by
          rw [sum_add_split (f := fun i j => c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j
              + c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x))
            (g := fun i j => fderiv ℝ (fun z : ChartPoint ι => c.g z i j) x (X x) * Y x i * Z x j)]
          rw [sum_add_split (f := fun i j => c.g x i j * fderiv ℝ (fun z : ChartPoint ι => Y z i) x (X x) * Z x j)
            (g := fun i j => c.g x i j * Y x i * fderiv ℝ (fun z : ChartPoint ι => Z z j) x (X x))]
    _ = c.formField x (c.nabla X Y x) (Z x) + c.formField x (Y x) (c.nabla X Z x) := hR.symm

end SmoothChartData

end ConnectionCurvature
end D12
end Poincare
