/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# The Banach space BUCn of bounded uniformly continuous functions on ℝⁿ

For genuine short-time existence of the semilinear heat equation
`∂ₜu = Δu + F(u)` the spatial state space must carry a complete norm for the
Banach fixed-point argument *and* support the strong continuity
`K_t * f → f` of the Gaussian heat semigroup as `t → 0⁺`. On the space
`BCFn n` of merely bounded continuous functions strong continuity fails
(a bounded continuous function is not recovered by its heat convolution at
time `0` unless it is uniformly continuous), while on the closed subspace of
**bounded uniformly continuous functions** it holds (proved in
`GaussianSemigroup.lean`).

This file constructs the spatial Banach space

  `BUCn n = { f : BCFn n | UniformContinuous f }`

as a bundled structure carrying the supremum norm of `BCFn n`, proves that it
is an ℝ-normed vector space and — via the standard ε/3 argument that uniform
limits of uniformly continuous functions are uniformly continuous — that it is
**complete**. No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`
is used.
-/
module

public import Poincare.D12.ParabolicLocal.GaussianConv
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.UniformMulAction

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace Poincare.D12.ParabolicLocal

/-! ## The bundled space -/

/-- A bounded uniformly continuous function on `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`): a bounded
continuous function together with the certificate of uniform continuity. -/
structure BUCf (n : ℕ) where
  /-- The underlying bounded continuous function. -/
  val : BCFn n
  /-- Uniform continuity of the underlying function. -/
  uniformContinuous_val : UniformContinuous (fun x : EuclideanSpace ℝ (Fin n) => val x)

/-- The spatial Banach space of the flat semilinear heat model: bounded uniformly continuous
functions on `ℝⁿ` with the supremum norm. -/
abbrev BUCn (n : ℕ) := BUCf n

namespace BUCf

variable {n : ℕ}

instance : Coe (BUCn n) (BCFn n) := ⟨BUCf.val⟩

instance : CoeFun (BUCn n) (fun _ => EuclideanSpace ℝ (Fin n) → ℝ) where
  coe f x := f.val x

theorem coe_apply (f : BUCn n) (x : EuclideanSpace ℝ (Fin n)) : f x = f.val x := rfl

@[simp]
theorem val_apply (f : BUCn n) (x : EuclideanSpace ℝ (Fin n)) : f.val x = f x := rfl

/-- Two BUC functions are equal when their underlying bounded continuous functions are
(the uniform-continuity certificates are proof-irrelevant). -/
@[ext]
theorem ext {f g : BUCn n} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  simp_all

/-! ## Algebraic and normed structure -/

instance : Zero (BUCn n) := ⟨⟨0, uniformContinuous_const⟩⟩
instance : Neg (BUCn n) := ⟨fun f => ⟨-f.val, f.uniformContinuous_val.neg⟩⟩
instance : Add (BUCn n) :=
  ⟨fun f g => ⟨f.val + g.val, f.uniformContinuous_val.add g.uniformContinuous_val⟩⟩
instance : SMul ℝ (BUCn n) := ⟨fun c f => ⟨c • f.val, f.uniformContinuous_val.const_smul c⟩⟩

@[simp]
theorem val_zero : (0 : BUCn n).val = 0 := rfl

@[simp]
theorem val_neg (f : BUCn n) : (-f).val = -f.val := rfl

@[simp]
theorem val_add (f g : BUCn n) : (f + g).val = f.val + g.val := rfl

@[simp]
theorem val_smul (c : ℝ) (f : BUCn n) : (c • f).val = c • f.val := rfl

instance : AddCommGroup (BUCn n) where
  add := (· + ·)
  add_assoc := by
    intro a b c
    apply ext
    simp only [val_add]
    exact add_assoc _ _ _
  zero := 0
  zero_add := by intro a; apply ext; simp
  add_zero := by intro a; apply ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg := Neg.neg
  neg_add_cancel := by
    intro a
    apply ext
    simp only [val_neg, val_add, val_zero]
    abel
  add_comm := by
    intro a b
    apply ext
    simp only [val_add]
    exact add_comm _ _

instance : Module ℝ (BUCn n) where
  smul := (· • ·)
  one_smul := by
    intro f
    apply ext
    simp only [val_smul]
    exact one_smul ℝ f.val
  mul_smul := by
    intro a b f
    apply ext
    simp only [val_smul]
    exact mul_smul a b f.val
  smul_add := by
    intro a f g
    apply ext
    simp only [val_smul, val_add]
    exact smul_add a f.val g.val
  add_smul := by
    intro a b f
    apply ext
    simp only [val_smul, val_add]
    exact add_smul a b f.val
  zero_smul := by
    intro f
    apply ext
    simp only [val_smul]
    exact zero_smul ℝ f.val
  smul_zero := by
    intro a
    apply ext
    simp only [val_smul, val_zero]
    exact smul_zero a

@[simp]
theorem val_sub (f g : BUCn n) : (f - g).val = f.val - g.val := rfl

/-- The norm on `BUCn n` is the supremum norm of the underlying `BCFn n` function. -/
noncomputable instance : NormedAddCommGroup (BUCn n) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => ‖f.val‖
      map_zero' := by
        rw [val_zero]
        exact norm_zero
      neg' := by
        intro f
        rw [val_neg]
        exact norm_neg _
      add_le' := by
        intro f g
        rw [val_add]
        exact norm_add_le _ _
      eq_zero_of_map_eq_zero' := by
        intro f h
        apply ext
        exact norm_eq_zero.mp h }

@[simp]
theorem norm_val (f : BUCn n) : ‖f.val‖ = ‖f‖ := rfl

/-- The norm of a bundled BUC function is the norm of its underlying BCF function. -/
@[simp]
theorem norm_mk (v : BCFn n) (h : UniformContinuous (fun x : EuclideanSpace ℝ (Fin n) => v x)) :
    ‖(⟨v, h⟩ : BUCn n)‖ = ‖v‖ := rfl

theorem norm_val' (f : BUCn n) : ‖f‖ = ‖f.val‖ := rfl

/-- The supremum metric on `BUCn n` coincides with the metric of the underlying `BCFn n`. -/
theorem dist_eq_dist_val (f g : BUCn n) : dist f g = dist f.val g.val := by
  rw [dist_eq_norm, dist_eq_norm, norm_val', val_sub]

/-- The supremum norm of a BUC function bounds its pointwise values. -/
theorem norm_coe_le_norm (f : BUCn n) (x : EuclideanSpace ℝ (Fin n)) : ‖f x‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_coe_le_norm f.val x

/-- The uniform-norm distance bounds the pointwise distance. -/
theorem dist_coe_le_dist (f g : BUCn n) (x : EuclideanSpace ℝ (Fin n)) :
    dist (f x) (g x) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(f.val - g.val) x‖ ≤ ‖f.val - g.val‖
  exact BoundedContinuousFunction.norm_coe_le_norm (f.val - g.val) x

noncomputable instance : NormedSpace ℝ (BUCn n) where
  norm_smul_le := by
    intro a f
    change ‖(a • f).val‖ ≤ ‖a‖ * ‖f.val‖
    simpa only [val_smul] using (norm_smul_le a f.val : ‖a • f.val‖ ≤ ‖a‖ * ‖f.val‖)

/-! ## Completeness -/

/-- **Uniform limits of uniformly continuous functions are uniformly continuous**: the ε/3
argument. If `g` is the uniform limit of the functions `F N` with `dist (F N) g < ε/3`, then
the uniform continuity modulus of `F N` at `ε/3` gives a modulus for `g` at `ε`. -/
theorem uniformContinuous_of_tendsto_uniform {F : ℕ → BUCn n} {g : BCFn n}
    (hg : Tendsto (fun k => (F k).val) atTop (𝓝 g)) :
    UniformContinuous (fun x : EuclideanSpace ℝ (Fin n) => g x) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  rcases Metric.tendsto_atTop.mp hg (ε / 3) hε3 with ⟨N, hN⟩
  rcases Metric.uniformContinuous_iff.mp (F N).uniformContinuous_val (ε / 3) hε3 with
    ⟨δ, hδ, hFN⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hgx : dist (g x) ((F N).val x) < ε / 3 := by
    have hle : ‖(F N).val x - g x‖ ≤ dist (F N).val g := by
      have hle' : ‖((F N).val - g) x‖ ≤ ‖(F N).val - g‖ :=
        BoundedContinuousFunction.norm_coe_le_norm ((F N).val - g) x
      rw [dist_eq_norm]
      exact hle'
    calc dist (g x) ((F N).val x)
        = dist ((F N).val x) (g x) := dist_comm _ _
      _ = ‖(F N).val x - g x‖ := by rw [dist_eq_norm]
      _ ≤ dist (F N).val g := hle
      _ < ε / 3 := hN N le_rfl
  have hgy : dist ((F N).val y) (g y) < ε / 3 := by
    have hle : ‖(F N).val y - g y‖ ≤ dist (F N).val g := by
      have hle' : ‖((F N).val - g) y‖ ≤ ‖(F N).val - g‖ :=
        BoundedContinuousFunction.norm_coe_le_norm ((F N).val - g) y
      rw [dist_eq_norm]
      exact hle'
    calc dist ((F N).val y) (g y)
        = ‖(F N).val y - g y‖ := by rw [dist_eq_norm]
      _ ≤ dist (F N).val g := hle
      _ < ε / 3 := hN N le_rfl
  have hmain : dist (g x) (g y)
      ≤ dist (g x) ((F N).val x) + dist ((F N).val x) ((F N).val y)
          + dist ((F N).val y) (g y) := by
    calc dist (g x) (g y)
        ≤ dist (g x) ((F N).val y) + dist ((F N).val y) (g y) := dist_triangle _ _ _
      _ ≤ dist (g x) ((F N).val x) + dist ((F N).val x) ((F N).val y)
            + dist ((F N).val y) (g y) :=
            add_le_add_left (dist_triangle (g x) ((F N).val x) ((F N).val y))
              (dist ((F N).val y) (g y))
  calc dist (g x) (g y)
      ≤ dist (g x) ((F N).val x) + dist ((F N).val x) ((F N).val y)
          + dist ((F N).val y) (g y) := hmain
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add hgx (hFN hxy)) hgy
    _ = ε := by ring

/-- **The Banach space `BUCn n` is complete.** A Cauchy sequence of bounded uniformly
continuous functions has a bounded continuous limit (completeness of `BCFn n`), and that limit
is uniformly continuous by `uniformContinuous_of_tendsto_uniform`. -/
noncomputable instance : CompleteSpace (BUCn n) :=
  UniformSpace.complete_of_cauchySeq_tendsto fun F hF => by
    have hFval : CauchySeq fun k => (F k).val := by
      rw [Metric.cauchySeq_iff] at hF ⊢
      intro ε hε
      rcases hF ε hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro k hk l hl
      simpa [dist_eq_dist_val] using hN k hk l hl
    rcases cauchySeq_tendsto_of_complete hFval with ⟨g, hg⟩
    have huc : UniformContinuous (fun x : EuclideanSpace ℝ (Fin n) => g x) :=
      uniformContinuous_of_tendsto_uniform (F := F) hg
    refine ⟨⟨g, huc⟩, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hg ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    simpa [dist_eq_dist_val] using hN k hk

end BUCf

end Poincare.D12.ParabolicLocal
