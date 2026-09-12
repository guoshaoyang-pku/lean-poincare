import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Poincare.Stage1.CurvatureAlgebra

/-!
# Poincare.Stage1.RiemannAdapter

**Stage1 抽象 `CurvatureOperator` 的 Riemann 几何适配接口（只固定接口，不构造曲率）**

本模块把 Stage1 的纯代数曲率算子接口 `Poincare.CurvatureAlgebra.CurvatureOperator`
与当前 mathlib 的流形 / 联络 / 内积 API 对接起来。它**只固定实例化接口**，
**不**构造联络的曲率张量，也**不**声称实现了 Levi-Civita 联络或几何 Ricci 张量。

## 当前 mathlib（本仓库锁定 revision `7974e751bece493b6ff508039423ca9fa2452fa8`）的事实

已存在、本文件直接使用：

* `ChartedSpace H M`（`Mathlib/Geometry/Manifold/ChartedSpace.lean:141`）；
* 切空间 `TangentSpace I x`（`Mathlib/Geometry/Manifold/IsManifold/Basic.lean:1035`，
  `TangentSpace I x` 是 `E` 的类型同义词，`AddCommGroup`/`Module ℝ` 等由 `deriving` 提供）
  与切丛的 `FiberBundle`/`VectorBundle` 实例
  （`Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:185,188`，需要 `[IsManifold I 1 M]`）；
* `CovariantDerivative I F V`（`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:366`），
  即 Koszul 联络（mathlib 没有单独名为 `Connection` 的声明）；
* 内积 / 度量 API：`RiemannianMetric`（`Mathlib/Topology/VectorBundle/Riemannian.lean:370`）、
  `RiemannianBundle`（同文件 `:420`；在 `Bundle` scope 下为纤维注册
  `NormedAddCommGroup`/`InnerProductSpace`，因此 `inner ℝ v w` 可用于切向量）、
  `IsContMDiffRiemannianBundle`（`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:67`）。

**不存在**（因此完整实例化无法完成，详见 `docs/riemann_adapter_status.md`）：

* mathlib 没有 `CovariantDerivative.curvature`，也没有任何 `curvature`/`Bianchi`/`Ricci`
  声明；在锁定的 `Mathlib/` 源树中检索 `curvature` 只命中
  `MeasureTheory/Measure/Doubling.lean:44` 的 docstring；
* 名为 `Connection` 的声明不存在；联络以 `CovariantDerivative` 表达，
  Levi-Civita 条件以 `CovariantDerivative.IsLeviCivitaConnection`
  （`.../CovariantDerivative/LeviCivita.lean:201`）表达；
* `CovariantDerivative.torsion` 存在（`.../CovariantDerivative/Torsion.lean:120`），
  但 torsion ≠ curvature。

## 本模块提供什么

* `PointwiseCurvature I M`：逐点 (1,3) 张量的类型缩写
  `∀ x, T_xM →ₗ[ℝ] T_xM →ₗ[ℝ] T_xM →ₗ[ℝ] T_xM`；
* `RiemannianCurvatureData E H I M`：适配结构。**几何背景（底空间模型 `(E, H, I)`、
  流形 `M`、切丛 `TangentSpace I`、内积 `[RiemannianBundle (TangentSpace I)]`）
  作为结构参数给出**（与 mathlib 自身的 `CovariantDerivative I F V`、
  `IsLeviCivitaConnection` 的参数风格一致：Lean 中带类型类的类型不适合作为普通字段）。
  字段为：
  * `cov`：联络（`CovariantDerivative I E (TangentSpace I)`）；
  * `curvatureAt`：逐点曲率算子（`PointwiseCurvature I M`，待填充的输入接口）；
  * `first_pair_skew`：第一对输入反对称 `R(X,Y)Z = -R(Y,X)Z`（待填充的证明字段）；
  * `first_bianchi`：第一 Bianchi `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`（待填充的证明字段）。
  后两个字段正是 Stage1 `CurvatureOperator` 的接口义务，因此未来 mathlib 提供
  `CovariantDerivative.curvature` 时，用它的反对称 / Bianchi 引理填充即可。
* `RiemannianCurvatureData.toCurvatureOperator`：把适配结构在某点化为 Stage1 的
  `CurvatureOperator ℝ (TangentSpace I x)`（真正的桥接函数）；
* `RiemannianCurvatureData.ofCurvature`：把“未来 `CovariantDerivative.curvature` 应提供的
  数据（逐点张量 + 两条对称性证明）”写成构造器，即缺失 API 的精确契约；
* `RiemannianCurvatureData.ofCurvatureOperators` 与
  `toCurvatureOperator_ofCurvatureOperators`：任意逐点 Stage1 算子族都可装入适配结构，
  且桥接后取回原算子（往返一致）；
* `RiemannianCurvatureData.zero`：给定任意联络，零曲率适配数据（真正编译的见证，
  说明接口可被满足；**不**表示几何曲率为零）；
* `curvatureForm` 及两条引理：用内积下降最后一个指标得到的 (0,4) 张量，证明其第一对
  反对称与第一 Bianchi。这两条只从 Stage1 接口字段推出；**没有**证明度量兼容性、
  第二 Bianchi 或任何 Ricci 对称性。

## 诚实边界

本文件**没有**实现联络的曲率张量（`curvatureAt` 是输入接口），**没有**实现
Levi-Civita 联络（mathlib 有 `leviCivitaConnection`，本文件不使用、也不声称由它得到曲率），
**没有**实现几何 Ricci 张量。全部证明完整，无 `sorry`/`axiom`/`unsafe`/`native_decide`。
-/

open Bundle
open scoped Bundle Manifold ContDiff Topology
open Poincare.CurvatureAlgebra

namespace Poincare
namespace RiemannAdapter

universe uE uH uM

/-- 逐点 (1,3) 型曲率算子的类型：在每个点 `x : M` 给出三线性映射
`T_xM → T_xM → T_xM → T_xM`（普通 `LinearMap`，与 Stage1 `CurvatureOperator` 的载体一致）。 -/
abbrev PointwiseCurvature {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] :=
  ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x

/-- **Stage1 ↔ Riemann 几何适配数据（最小接口）。**

几何背景以参数给出：模型空间 `E`、模型域 `H`、`ModelWithCorners I`、流形 `M`、
切丛 `TangentSpace I` 以及内积结构 `[RiemannianBundle (TangentSpace I)]`。

字段：

* `cov`：联络；
* `curvatureAt`：逐点 (1,3) 曲率算子。当前 mathlib 没有 `CovariantDerivative.curvature`，
  所以这是**待填充的输入接口**，而不是本文件构造出的对象；
* `first_pair_skew` / `first_bianchi`：Stage1 `CurvatureOperator` 的两条接口义务。

诚实声明：本结构**不**证明 `curvatureAt` 来自 `cov`（该命题在当前 mathlib 中甚至无法陈述，
因为曲率未定义），也**不**声称任何几何曲率结果。 -/
structure RiemannianCurvatureData
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type uE)] where
  /-- 联络（Koszul 联络；mathlib 中没有名为 `Connection` 的独立声明）。 -/
  cov : CovariantDerivative I E (TangentSpace I : M → Type uE)
  /-- 逐点曲率算子（待填充：当前 mathlib 没有联络曲率的定义）。 -/
  curvatureAt : PointwiseCurvature I M
  /-- 接口义务：第一对输入反对称 `R(X,Y)Z = -R(Y,X)Z`。 -/
  first_pair_skew : ∀ (x : M) (X Y Z : TangentSpace I x),
    curvatureAt x X Y Z = -curvatureAt x Y X Z
  /-- 接口义务：第一 Bianchi 恒等式 `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`。 -/
  first_bianchi : ∀ (x : M) (X Y Z : TangentSpace I x),
    curvatureAt x X Y Z + curvatureAt x Y Z X + curvatureAt x Z X Y = 0

namespace RiemannianCurvatureData

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type uE)]

/-! ### 桥接到 Stage1 `CurvatureOperator` -/

/-- **适配桥**：把某点的适配数据化为 Stage1 的抽象曲率算子
`CurvatureOperator ℝ (TangentSpace I x)`。两条接口义务直接由结构字段提供。 -/
noncomputable def toCurvatureOperator
    (D : RiemannianCurvatureData E H I M) (x : M) :
    CurvatureOperator ℝ (TangentSpace I x) where
  toTrilinear := D.curvatureAt x
  first_pair_skew := D.first_pair_skew x
  first_bianchi := D.first_bianchi x

/-- 桥接后在 Stage1 记法下的取值就是 `curvatureAt`。 -/
@[simp] lemma toCurvatureOperator_apply
    (D : RiemannianCurvatureData E H I M) (x : M) (X Y Z : TangentSpace I x) :
    D.toCurvatureOperator x X Y Z = D.curvatureAt x X Y Z := rfl

/-- **缺失 API 的精确契约**：若未来的 `CovariantDerivative.curvature` 能提供逐点张量 `κ`
以及第一对反对称与第一 Bianchi 的证明，则由此构造适配数据。
（本构造器不使用任何 `sorry`/`axiom`；它只把待填充的接口数据打包。） -/
def ofCurvature
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (κ : PointwiseCurvature I M)
    (hskew : ∀ (x : M) (X Y Z : TangentSpace I x), κ x X Y Z = -κ x Y X Z)
    (hbianchi : ∀ (x : M) (X Y Z : TangentSpace I x),
      κ x X Y Z + κ x Y Z X + κ x Z X Y = 0) :
    RiemannianCurvatureData E H I M where
  cov := cov
  curvatureAt := κ
  first_pair_skew := hskew
  first_bianchi := hbianchi

/-- **反向桥**：任意逐点的 Stage1 曲率算子族（连同联络）都可装入适配结构。 -/
noncomputable def ofCurvatureOperators
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (K : ∀ x : M, CurvatureOperator ℝ (TangentSpace I x)) :
    RiemannianCurvatureData E H I M where
  cov := cov
  curvatureAt := fun x => (K x).toTrilinear
  first_pair_skew := fun x X Y Z => (K x).first_pair_skew X Y Z
  first_bianchi := fun x X Y Z => (K x).first_bianchi X Y Z

/-- 反向桥接后再正向桥接，取回原来的 Stage1 算子。 -/
@[simp] lemma toCurvatureOperator_ofCurvatureOperators
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (K : ∀ x : M, CurvatureOperator ℝ (TangentSpace I x)) (x : M) :
    (ofCurvatureOperators cov K).toCurvatureOperator x = K x := by
  apply CurvatureOperator.ext
  ext X Y Z
  rfl

/-! ### 一致性见证（接口可被满足） -/

/-- **零曲率适配数据**：给定任意联络，逐点曲率取零，两条接口义务由 `simp` 证明。
这是接口非空的真正编译见证；**不**表示任何几何曲率为零，也**不**表示
`curvatureAt` 是 `cov` 的曲率。 -/
noncomputable def zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) :
    RiemannianCurvatureData E H I M where
  cov := cov
  curvatureAt := 0
  first_pair_skew := by intro x X Y Z; simp
  first_bianchi := by intro x X Y Z; simp

/-- 零曲率适配数据桥接到 Stage1 后就是 Stage1 的零算子。 -/
@[simp] lemma zero_toCurvatureOperator
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) (x : M) :
    (zero cov).toCurvatureOperator x = CurvatureOperator.zero := by
  apply CurvatureOperator.ext
  ext X Y Z
  rfl

/-! ### 用内积下降最后一个指标：(0,4) 张量接口

`curvatureForm D x X Y Z W := ⟨R(X,Y)Z, W⟩`。下面两条引理只使用
`RiemannianBundle` 给出的内积与 Stage1 接口字段，因此**不**声称任何
度量兼容性或额外对称性。 -/

/-- 用内积把 `curvatureAt` 的最后一个指标下降得到的 (0,4) 型张量。 -/
noncomputable def curvatureForm
    (D : RiemannianCurvatureData E H I M) (x : M) (X Y Z W : TangentSpace I x) : ℝ :=
  inner ℝ (D.curvatureAt x X Y Z) W

/-- (0,4) 张量在第一对输入上的反对称性（由 `first_pair_skew` 推出）。 -/
lemma curvatureForm_first_pair_skew
    (D : RiemannianCurvatureData E H I M) (x : M) (X Y Z W : TangentSpace I x) :
    D.curvatureForm x X Y Z W = - D.curvatureForm x Y X Z W := by
  simp [curvatureForm, D.first_pair_skew x X Y Z]

/-- (0,4) 张量的第一 Bianchi（循环和为零；由 `first_bianchi` 与内积的加法性推出）。 -/
lemma curvatureForm_first_bianchi
    (D : RiemannianCurvatureData E H I M) (x : M) (X Y Z W : TangentSpace I x) :
    D.curvatureForm x X Y Z W + D.curvatureForm x Y Z X W +
      D.curvatureForm x Z X Y W = 0 := by
  simp only [curvatureForm, ← inner_add_left, D.first_bianchi x X Y Z, inner_zero_left]

/-- 零曲率适配数据的 (0,4) 张量为零。 -/
@[simp] lemma zero_curvatureForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) (x : M)
    (X Y Z W : TangentSpace I x) :
    (zero cov).curvatureForm x X Y Z W = 0 := by
  simp [curvatureForm, zero]

end RiemannianCurvatureData

end RiemannAdapter
end Poincare
