/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task t14)
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Poincare.Stage6.SphereSimplyConnected

**本模块不证明 `SimplyConnectedSpace 𝕊³`，也不引入任何公理。** 它把 Stage6 缺失的
「三维球面单连通性」接口固定下来：

* `sphereThreeSimplyConnected` —— **statement-only** 研究目标别名
  （`def : Prop := SimplyConnectedSpace 𝕊³`）；
* `sphereThreePiOneTrivial` —— 等价的目标写法 `∀ x, Subsingleton (π_ 1 𝕊³ x)`
  （即 π₁(𝕊³) = 0）；
* 一组**真实、无公理**的归约定理，把上述目标化到 mathlib 现有对象上
  （路径连通性、基本群、环路零伦、路径同伦类唯一、单个基点处的 π₁）。

## mathlib 现状（本仓库锁定的 rev `7974e751be`，`.lake/packages/mathlib`）

* `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`：
  `SimplyConnectedSpace` 类、`SimplyConnectedSpace.ofContractible`、
  `simply_connected_iff_paths_homotopic`、`simply_connected_iff_loops_nullhomotopic`；
  **没有**任何球面实例。
* `Mathlib/Analysis/Normed/Module/Connected.lean`：`isPathConnected_sphere`
  （实向量空间维数 > 1 的球面路径连通），**没有**单连通性。
* `Mathlib/Topology/Homotopy/HomotopyGroup.lean` 文件头 TODO 明确写着
  “Examples with `𝕊^n`: `π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`”
  —— `π_1 (𝕊³) = 0` 正属于这条未实现的 TODO。
* 全树搜索 `SimplyConnectedSpace` × `sphere`、`FundamentalGroup` × `sphere`、
  `ContractibleSpace` × `sphere` 均无命中（见 `docs/sphere_pi1_status.md` 记录的命令）。

上游已有对应的**未合并** PR
[leanprover-community/mathlib4#28246](https://github.com/leanprover-community/mathlib4/pull/28246)
（“the n-sphere is simply connected for n > 1”，2026-09-02 仍为 open，最后同步 master
2026-07-14；含 `VanKampen.lean` 164 行 + `SimplyConnectedSphere.lean` 193 行），
但它不在本项目锁定的 mathlib rev 中，故本文件不依赖它、也不复制它冒充本地成果。

因此本文件只交付接口与归约，不伪造证明。待上游合并（或在本包内适配移植该 PR）
之后，`sphereThreeSimplyConnected` 可直接由实例 `inferInstance` 关闭，
本文件的所有归约定理仍然有效。
-/

open scoped Topology
open Metric (sphere)

local macro:max "𝕊" noWs n:superscript(term) : term =>
  `(sphere (0 : EuclideanSpace ℝ (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

namespace Poincare

namespace Stage6

/-! ## Statement-only 研究目标 -/

/-- **STATEMENT-ONLY**：三维单位球面单连通性的研究目标别名。

这是 `def ... : Prop`，不是定理、不引入公理、也不是 `instance`：它的存在只是把
mathlib 目前缺失的 `SimplyConnectedSpace 𝕊³` 这一类型固定下来，供后续工作
（van Kampen / 覆盖空间 / 同伦群计算）原地替换为带证明的定理。**不得把它当作
已证明的单连通性使用。** -/
def sphereThreeSimplyConnected : Prop :=
  SimplyConnectedSpace 𝕊³

/-- **STATEMENT-ONLY**：`π₁(𝕊³) = 0` 的研究目标别名
（逐基点写成 `Subsingleton (π_ 1 𝕊³ x)`）。同样不是定理，也不是证明。 -/
def sphereThreePiOneTrivial : Prop :=
  ∀ x : 𝕊³, Subsingleton (π_ 1 𝕊³ x)

/-- 形状检查：别名定义性地就是 `SimplyConnectedSpace 𝕊³`，无内容损失。 -/
theorem sphereThreeSimplyConnected_iff_simplyConnectedSpace :
    sphereThreeSimplyConnected ↔ SimplyConnectedSpace 𝕊³ :=
  Iff.rfl

/-- 形状检查：`sphereThreePiOneTrivial` 定义性地就是逐基点 π₁ 的 subsingleton 陈述。 -/
theorem sphereThreePiOneTrivial_iff_forall_subsingleton_pi1 :
    sphereThreePiOneTrivial ↔ ∀ x : 𝕊³, Subsingleton (π_ 1 𝕊³ x) :=
  Iff.rfl

/-! ## 真实归约（均无公理；不依赖任何球面单连通性假设） -/

/-- `𝕊³` 路径连通：由 mathlib 的 `isPathConnected_sphere` 给出
（`EuclideanSpace ℝ (Fin 4)` 的实维数为 4 > 1）。这是下列归约所需的、真实可证的
一半内容。 -/
theorem pathConnectedSpace_sphereThree : PathConnectedSpace 𝕊³ := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  exact isPathConnected_sphere (by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    norm_num) 0 (by norm_num)

/-- 一般空间：单连通 ↔ 路径连通且各基点基本群为 subsingleton（即 π₁ 平凡）。

正向是 mathlib 实例；反向由 `simply_connected_iff_loops_nullhomotopic` 得到：
π₁ 平凡使每个环路与其常值环路同伦。这是把「π₁(𝕊³) = 0」升级为
`SimplyConnectedSpace 𝕊³` 的真实桥梁。 -/
theorem simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup
    (X : Type*) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔
      PathConnectedSpace X ∧ ∀ x : X, Subsingleton (FundamentalGroup X x) := by
  constructor
  · intro h
    exact ⟨@SimplyConnectedSpace.instPathConnectedSpace X _ h,
      fun x => @SimplyConnectedSpace.instSubsingletonFundamentalGroup X _ h x⟩
  · rintro ⟨hpc, hsub⟩
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨hpc, fun x γ => ?_⟩
    have hq : (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      @Subsingleton.elim (Path.Homotopic.Quotient x x) (hsub x) _ _
    exact Quotient.exact hq

/-- 一般空间：逐基点 π₁ 平凡 ↔ 逐基点基本群平凡（两者由
`HomotopyGroup.pi1MulEquivFundamentalGroup` 同构搬运）。 -/
theorem forall_subsingleton_pi1_iff_forall_subsingleton_fundamentalGroup
    (X : Type*) [TopologicalSpace X] :
    (∀ x : X, Subsingleton (π_ 1 X x)) ↔
      ∀ x : X, Subsingleton (FundamentalGroup X x) := by
  constructor
  · intro h x
    exact @Equiv.subsingleton (FundamentalGroup X x) (π_ 1 X x)
      (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).toEquiv.symm (h x)
  · intro h x
    exact @Equiv.subsingleton (π_ 1 X x) (FundamentalGroup X x)
      (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).toEquiv (h x)

/-- `𝕊³` 单连通 ↔ 各基点基本群平凡（利用 `𝕊³` 路径连通这一真实事实归约）。 -/
theorem sphereThreeSimplyConnected_iff_subsingleton_fundamentalGroup :
    sphereThreeSimplyConnected ↔ ∀ x : 𝕊³, Subsingleton (FundamentalGroup 𝕊³ x) := by
  rw [sphereThreeSimplyConnected]
  rw [simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup (X := 𝕊³)]
  exact and_iff_right pathConnectedSpace_sphereThree

/-- `𝕊³` 单连通 ↔ 单个基点处的基本群平凡（由路径连通性，基点可搬运）。 -/
theorem sphereThreeSimplyConnected_iff_subsingleton_fundamentalGroup_at (x₀ : 𝕊³) :
    sphereThreeSimplyConnected ↔ Subsingleton (FundamentalGroup 𝕊³ x₀) := by
  rw [sphereThreeSimplyConnected_iff_subsingleton_fundamentalGroup]
  constructor
  · intro h
    exact h x₀
  · intro h x
    exact @Equiv.subsingleton (FundamentalGroup 𝕊³ x) (FundamentalGroup 𝕊³ x₀)
      (@FundamentalGroup.fundamentalGroupMulEquivOfPathConnected 𝕊³ _ x x₀
        pathConnectedSpace_sphereThree).toEquiv h

/-- `𝕊³` 单连通 ↔ 每个环路与其常值环路同伦
（`simply_connected_iff_loops_nullhomotopic` 的球面版，路径连通性用
`pathConnectedSpace_sphereThree` 消去）。 -/
theorem sphereThreeSimplyConnected_iff_loops_nullhomotopic :
    sphereThreeSimplyConnected ↔
      ∀ (x : 𝕊³) (γ : Path x x), Path.Homotopic γ (Path.refl x) := by
  rw [sphereThreeSimplyConnected]
  rw [simply_connected_iff_loops_nullhomotopic]
  exact and_iff_right pathConnectedSpace_sphereThree

/-- `𝕊³` 单连通 ↔ 任意两点间的路径同伦类唯一
（`simply_connected_iff_paths_homotopic` 的球面版）。 -/
theorem sphereThreeSimplyConnected_iff_paths_homotopic :
    sphereThreeSimplyConnected ↔
      ∀ x y : 𝕊³, Subsingleton (Path.Homotopic.Quotient x y) := by
  rw [sphereThreeSimplyConnected]
  rw [simply_connected_iff_paths_homotopic]
  exact and_iff_right pathConnectedSpace_sphereThree

/-- `π₁(𝕊³) = 0`（逐基点写法）与 `SimplyConnectedSpace 𝕊³` 等价。 -/
theorem sphereThreePiOneTrivial_iff_simplyConnected :
    sphereThreePiOneTrivial ↔ sphereThreeSimplyConnected := by
  rw [sphereThreePiOneTrivial, sphereThreeSimplyConnected]
  rw [simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup (X := 𝕊³)]
  rw [and_iff_right pathConnectedSpace_sphereThree]
  exact forall_subsingleton_pi1_iff_forall_subsingleton_fundamentalGroup (X := 𝕊³)

/-- `π₁(𝕊³) = 0` 只需在**单个**基点处验证。 -/
theorem sphereThreePiOneTrivial_iff_subsingleton_pi1_at (x₀ : 𝕊³) :
    sphereThreePiOneTrivial ↔ Subsingleton (π_ 1 𝕊³ x₀) := by
  rw [sphereThreePiOneTrivial_iff_simplyConnected,
    sphereThreeSimplyConnected_iff_subsingleton_fundamentalGroup_at x₀]
  exact (@Equiv.subsingleton_congr (π_ 1 𝕊³ x₀) (FundamentalGroup 𝕊³ x₀)
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := 𝕊³) (x := x₀)).toEquiv).symm

end Stage6

end Poincare
