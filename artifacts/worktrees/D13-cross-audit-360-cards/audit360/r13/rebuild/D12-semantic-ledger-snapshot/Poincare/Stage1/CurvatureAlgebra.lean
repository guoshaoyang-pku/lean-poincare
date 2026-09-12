import Mathlib.LinearAlgebra.Trace

/-!
# Poincare.Stage1.CurvatureAlgebra

**曲率代数（Stage1，抽象代数接口）**

本模块只处理**纯代数**的 `(1,3)` 型曲率算子接口，刻意不依赖流形分析：

* `CurvatureOperator R V`：带第一对输入反对称性与第一 Bianchi 恒等式（作为结构字段，
  即接口假设）的抽象 `R(X,Y)Z` 曲率算子。其底层载体是 `R`-模 `V` 上的三线性映射
  `V →ₗ[R] V →ₗ[R] V →ₗ[R] V`（mathlib 现成的 `LinearMap`，自带加法与标量乘法），
  所以“曲率算子”由**一个 carrier 类型**给出：底空间上点态加法/标量乘法并把
  反对称/Bianchi 当作额外结构字段。
* 由接口假设推出的引理：第一对输入的反对称等价形式（交换相加为零等）、
  第一 Bianchi 的循环和为零（即结构字段本身）、反向循环版本、
  以及由 (反对称 + 第一 Bianchi) 推出的“槽位对换”恒等式。
* 收缩接口：`endoRicci`（对固定 `(X,Y)` 的“取迹对象” `Z ↦ R(Z,X)Y`）、
  `ricci`（对上述自同态取 `LinearMap.trace`，在有限自由模上是基无关的）；
  有限基 + `Finset` 和的显式坐标实现 `ricciSum` 及与 `ricci` 的一致性定理。
* `ScalarContractionData`：标量曲率收缩所需的最小数据接口（“指标提升”）。
  本模块**没有**流形、联络、度量的概念，因此：
  * 这里的 `ricci`/`ricciSum` 是抽象的代数收缩（约定：把第一个输入槽与输出槽收缩），
    **不等于**黎曼几何中带度量的 Ricci 张量（后者还需要度量、正交标架与符号约定）；
  * `scalarCurvature` 需要调用方提供 `ScalarContractionData`（真正实例化来自后续
    带度量的 Stage），本模块**不**声称已实现几何上的数量曲率。

重要边界声明：本文件**不**证明、也不声称证明任何关于 Riemann 流形曲率的结果，
更不推出 Ricci flow 的任何内容。

## 命名与 mathlib 冲突检查（本仓库锁定的 mathlib commit `7974e751bece…`）

在 `Mathlib/` 源树中检索：`Bianchi`、`Ricci`、`Curvature*`、`RiemannCurvature*`
均无任何声明（仅 `MeasureTheory/Measure/Doubling.lean` 的 docstring 提到 “curvature”）。
本文件的所有顶层声明都放在 `Poincare.CurvatureAlgebra` 命名空间下，
不覆盖 mathlib 已有声明；`LinearMap.trace`/`Matrix.trace`/`Module.Basis` 等直接复用 mathlib。

## 编译记录（见 `docs/stage1_curvature_status.md` 与 `Stage1/README.md`）

- toolchain: `leanprover/lean4:v4.34.0-rc2`（commit `6a10ac8c22be`）
- mathlib: `poincare-lab` 依赖的 master revision `7974e751bece493b6ff508039423ca9fa2452fa8`
- 命令：`cd poincare-lab && lake build Poincare.Stage1.CurvatureAlgebra`
-/

open scoped BigOperators

namespace Poincare
namespace CurvatureAlgebra

universe u v w

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- 抽象 `(1,3)` 型曲率算子：给 `R`-模 `V` 上的三线性映射 `(X,Y,Z) ↦ R(X,Y)Z`
配上两个代数公理（作为结构字段，即本接口的假设）：

* `first_pair_skew`：第一对输入反对称 `R(X,Y)Z = -R(Y,X)Z`；
* `first_bianchi`：第一 Bianchi 恒等式（循环和为零）
  `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`。

注意：这里 `R` 是基环、`V` 是模，与流形无关；“曲率”一词仅表示“满足上述两条
代数恒等式的三线性映射”。-/
@[ext]
structure CurvatureOperator (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V]
    [Module R V] where
  /-- 底层三线性映射 `(X Y Z) ↦ R(X,Y)Z`（作为嵌套 `LinearMap`，因此
  全体三线性映射自动带点态加法与标量乘法）。-/
  toTrilinear : V →ₗ[R] V →ₗ[R] V →ₗ[R] V
  /-- 接口假设：第一对输入反对称 `R(X,Y)Z = -R(Y,X)Z`。-/
  first_pair_skew : ∀ X Y Z : V, toTrilinear X Y Z = -toTrilinear Y X Z
  /-- 接口假设：第一 Bianchi 恒等式（循环和为零）。-/
  first_bianchi : ∀ X Y Z : V,
    toTrilinear X Y Z + toTrilinear Y Z X + toTrilinear Z X Y = 0

namespace CurvatureOperator

/-- 允许把算子当作普通三元函数使用：`K X Y Z` 即 `R(X,Y)Z`。-/
instance : CoeFun (CurvatureOperator R V) (fun _ => V → V → V → V) where
  coe K X Y Z := K.toTrilinear X Y Z

/-! ## 第一对输入的反对称性（由接口字段导出的 API） -/

/-- 接口给出的反对称性（对 `K X Y Z` 记法重述）：`R(X,Y)Z = -R(Y,X)Z`。-/
lemma first_pair_skew_apply (K : CurvatureOperator R V) (X Y Z : V) :
    K X Y Z = -K Y X Z := by
  simpa using K.first_pair_skew X Y Z

/-- 反方向：`R(Y,X)Z = -R(X,Y)Z`。-/
lemma first_pair_skew_swap (K : CurvatureOperator R V) (X Y Z : V) :
    K Y X Z = -K X Y Z := by
  simpa using K.first_pair_skew Y X Z

/-- 反对称 ⇒ “交换第一对输入后与原项相加为零”。-/
lemma first_pair_skew_add_zero (K : CurvatureOperator R V) (X Y Z : V) :
    K X Y Z + K Y X Z = 0 := by
  rw [K.first_pair_skew_apply X Y Z]
  exact neg_add_cancel (K Y X Z)

/-- 反对称 ⇒ 交换顺序的相加也为零。-/
lemma first_pair_skew_add_zero' (K : CurvatureOperator R V) (X Y Z : V) :
    K Y X Z + K X Y Z = 0 := by
  rw [K.first_pair_skew_apply X Y Z]
  exact add_neg_cancel (K Y X Z)

/-! ## 第一 Bianchi 恒等式（循环和为零）及其派生引理 -/

/-- 第一 Bianchi 恒等式（对 `K X Y Z` 记法重述）：循环和为零。-/
lemma first_bianchi_cyclic (K : CurvatureOperator R V) (X Y Z : V) :
    K X Y Z + K Y Z X + K Z X Y = 0 := by
  simpa using K.first_bianchi X Y Z

/-- 反向循环 `(Z,Y,X)` 上的第一 Bianchi 恒等式。 -/
lemma first_bianchi_reverse_cyclic (K : CurvatureOperator R V) (X Y Z : V) :
    K Z Y X + K Y X Z + K X Z Y = 0 := by
  simpa using K.first_bianchi Z Y X

/-- 循环和为零（把三项的循环起点换到中间）。 -/
lemma first_bianchi_cyclic_swap (K : CurvatureOperator R V) (X Y Z : V) :
    K Y Z X + K Z X Y + K X Y Z = 0 := by
  rw [← K.first_bianchi_cyclic X Y Z]
  ac_rfl

/-- 由循环和为零解出第一项：
`R(X,Y)Z = -(R(Y,Z)X + R(Z,X)Y)`。-/
lemma first_bianchi_neg_sum (K : CurvatureOperator R V) (X Y Z : V) :
    K X Y Z = -(K Y Z X + K Z X Y) := by
  have h : K X Y Z + (K Y Z X + K Z X Y) = 0 := by
    simpa [add_assoc] using (K.first_bianchi X Y Z)
  exact eq_neg_of_add_eq_zero_left h

/-- 把反对称性用于第一 Bianchi 恒等式（取 `(X,Z,Y)`）后得到的代数恒等式：
`R(X,Z)Y = R(X,Y)Z + R(Y,Z)X`。
（可验证：对任何满足反对称 + 第一 Bianchi 的三线性映射都成立，
例如李括号型映射 `R(X,Y)Z := [[X,Y],Z]`。）-/
lemma first_bianchi_split (K : CurvatureOperator R V) (X Y Z : V) :
    K X Z Y = K X Y Z + K Y Z X := by
  -- 对 (X, Z, Y) 用第一 Bianchi：
  have h : K X Z Y + K Z Y X + K Y X Z = 0 := K.first_bianchi X Z Y
  -- 两项分别用反对称：
  rw [K.first_pair_skew_apply Z Y X, K.first_pair_skew_apply Y X Z] at h
  have h1 : K X Z Y + -K Y Z X = K X Y Z := by
    have hc := congrArg (fun t : V => t + K X Y Z) h
    simpa [add_assoc, neg_add_cancel, add_zero] using hc
  calc
    K X Z Y = K X Y Z + K Y Z X := by
      have h2 := congrArg (fun t : V => t + K Y Z X) h1
      simpa [add_assoc, neg_add_cancel, add_zero] using h2

/-! ## 零、加法、负、标量乘法（点态；底层是 mathlib 三线性映射模的结构） -/

/-- 零算子（恒为零的曲率算子，接口非空的一个平凡实例）。-/
def zero : CurvatureOperator R V where
  toTrilinear := 0
  first_pair_skew := by
    intro X Y Z
    simp
  first_bianchi := by
    intro X Y Z
    simp

/-- 点态加法：`(K + L)(X,Y)Z := K(X,Y)Z + L(X,Y)Z`。
反对称与第一 Bianchi 都是线性条件，故仍落在接口内。-/
def add (K L : CurvatureOperator R V) : CurvatureOperator R V where
  toTrilinear := K.toTrilinear + L.toTrilinear
  first_pair_skew := by
    intro X Y Z
    change K.toTrilinear X Y Z + L.toTrilinear X Y Z =
      -(K.toTrilinear Y X Z + L.toTrilinear Y X Z)
    rw [K.first_pair_skew X Y Z, L.first_pair_skew X Y Z, neg_add]
  first_bianchi := by
    intro X Y Z
    have hK : (K.toTrilinear X Y Z + K.toTrilinear Y Z X) + K.toTrilinear Z X Y = 0 :=
      K.first_bianchi X Y Z
    have hL : (L.toTrilinear X Y Z + L.toTrilinear Y Z X) + L.toTrilinear Z X Y = 0 :=
      L.first_bianchi X Y Z
    calc
      ((K.toTrilinear X Y Z + L.toTrilinear X Y Z) +
          (K.toTrilinear Y Z X + L.toTrilinear Y Z X)) +
          (K.toTrilinear Z X Y + L.toTrilinear Z X Y)
          = ((K.toTrilinear X Y Z + K.toTrilinear Y Z X) + K.toTrilinear Z X Y) +
              ((L.toTrilinear X Y Z + L.toTrilinear Y Z X) + L.toTrilinear Z X Y) := by
        ac_rfl
      _ = 0 + 0 := by rw [hK, hL]
      _ = 0 := by simp

/-- 点态负：`(-K)(X,Y)Z := -K(X,Y)Z`。-/
def neg (K : CurvatureOperator R V) : CurvatureOperator R V where
  toTrilinear := -K.toTrilinear
  first_pair_skew := by
    intro X Y Z
    change -(K.toTrilinear X Y Z) = -(-(K.toTrilinear Y X Z))
    rw [K.first_pair_skew X Y Z]
  first_bianchi := by
    intro X Y Z
    change (-(K.toTrilinear X Y Z) + -(K.toTrilinear Y Z X)) + -(K.toTrilinear Z X Y) = 0
    rw [← neg_add, ← neg_add, K.first_bianchi X Y Z, neg_zero]

/-- 点态标量乘法：`(a • K)(X,Y)Z := a • K(X,Y)Z`。-/
def smul (a : R) (K : CurvatureOperator R V) : CurvatureOperator R V where
  toTrilinear := a • K.toTrilinear
  first_pair_skew := by
    intro X Y Z
    change a • K.toTrilinear X Y Z = -(a • K.toTrilinear Y X Z)
    rw [K.first_pair_skew X Y Z, smul_neg]
  first_bianchi := by
    intro X Y Z
    change (a • K.toTrilinear X Y Z + a • K.toTrilinear Y Z X) +
        a • K.toTrilinear Z X Y = 0
    rw [← smul_add, ← smul_add, K.first_bianchi X Y Z, smul_zero]

/-! 点态运算满足模律（关键几条；全部可由底空间上的模律 + `ext` 逐点验证）。
注意：本阶段**不**把这些注册为 `AddCommGroup`/`Module` 类型类实例，
只把载体与律作为引理公开（注册实例留给后续使用方按需进行）。-/

theorem add_comm (K L : CurvatureOperator R V) : add K L = add L K := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.add_comm (K.toTrilinear X Y Z) (L.toTrilinear X Y Z)

theorem add_assoc (K L M : CurvatureOperator R V) : add (add K L) M = add K (add L M) := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.add_assoc (K.toTrilinear X Y Z) (L.toTrilinear X Y Z) (M.toTrilinear X Y Z)

theorem zero_add (K : CurvatureOperator R V) : add zero K = K := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.zero_add (K.toTrilinear X Y Z)

theorem add_zero (K : CurvatureOperator R V) : add K zero = K := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.add_zero (K.toTrilinear X Y Z)

theorem add_left_neg (K : CurvatureOperator R V) : add (neg K) K = zero := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact neg_add_cancel (K.toTrilinear X Y Z)

theorem add_neg_cancel (K : CurvatureOperator R V) : add K (neg K) = zero := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.add_neg_cancel (K.toTrilinear X Y Z)

theorem one_smul (K : CurvatureOperator R V) : smul (1 : R) K = K := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.one_smul R (K.toTrilinear X Y Z)

theorem zero_smul (K : CurvatureOperator R V) : smul (0 : R) K = zero := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.zero_smul R (K.toTrilinear X Y Z)

theorem smul_zero (a : R) : smul a (zero : CurvatureOperator R V) = zero := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.smul_zero a

theorem smul_smul (a b : R) (K : CurvatureOperator R V) :
    smul a (smul b K) = smul (a * b) K := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.smul_smul a b (K.toTrilinear X Y Z)

theorem smul_add (a : R) (K L : CurvatureOperator R V) :
    smul a (add K L) = add (smul a K) (smul a L) := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact _root_.smul_add a (K.toTrilinear X Y Z) (L.toTrilinear X Y Z)

theorem add_smul (a b : R) (K : CurvatureOperator R V) :
    add (smul a K) (smul b K) = smul (a + b) K := by
  apply CurvatureOperator.ext
  ext X Y Z
  exact (_root_.add_smul a b (K.toTrilinear X Y Z)).symm

/-! ## Ricci 收缩的最小接口与实现

“收缩”在纯代数层面只有一种现成的解释：对某个**自同态**取迹。
这里固定约定（与 do Carmo 风格的 `Ric(X,Y) = Σᵢ ⟨R(eᵢ,X)Y, eᵢ⟩` 在正交标架下一致）：
把第一个输入槽与输出槽收缩，即对自同态 `Z ↦ R(Z,X)Y` 取 `LinearMap.trace`。

- `endoRicci`：取迹对象（自同态），其线性性被验证；
- `ricci`：完整收缩（双线性型对象 `V →ₗ V →ₗ R`，两侧线性都被验证）；
- `scalarCurvature`：数量曲率接口 —— 需要调用方给出 `ScalarContractionData`
  （抽象的“指标提升”；真正实例化必须来自带度量的几何层）。

诚实边界：本小节**没有**度量、没有正交标架、没有流形。`ricci` 在无限维或
非自由模上会退化为 `LinearMap.trace` 的约定值 `0`（mathlib 的 `trace` 在不存在
有限基时定义为 `0`），所以“几何上有意义的 Ricci 张量”仍需后续有限维自由模 +
度量的设定。见 `Stage1/README.md` 与 `docs/stage1_curvature_status.md` 中的记录。 -/

section Contraction

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- 固定 `(X,Y)` 后由曲率算子给出的自同态 `Z ↦ R(Z,X)Y`
（第一个输入槽的“部分求值”）。这是 Ricci 收缩的取迹对象。-/
def endoRicci (K : CurvatureOperator R V) (X Y : V) : V →ₗ[R] V where
  toFun Z := K.toTrilinear Z X Y
  map_add' := by
    intro Z₁ Z₂
    rw [map_add (K.toTrilinear) Z₁ Z₂]
    rw [LinearMap.add_apply]
    rw [LinearMap.add_apply]
  map_smul' := by
    intro a Z
    change K.toTrilinear (a • Z) X Y = a • K.toTrilinear Z X Y
    rw [map_smul (K.toTrilinear) a Z]
    rw [LinearMap.smul_apply]
    rw [LinearMap.smul_apply]

/-- 第一个输入槽的“预收缩”自同态族在第二个槽上是线性的：
`Y ↦ endoRicci K X Y`。-/
def endoRicci₁ (K : CurvatureOperator R V) (X : V) : V →ₗ[R] V →ₗ[R] V where
  toFun Y := endoRicci K X Y
  map_add' := by
    intro Y₁ Y₂
    ext Z
    change K.toTrilinear Z X (Y₁ + Y₂) =
      K.toTrilinear Z X Y₁ + K.toTrilinear Z X Y₂
    rw [map_add (K.toTrilinear Z X) Y₁ Y₂]
  map_smul' := by
    intro a Y
    ext Z
    change K.toTrilinear Z X (a • Y) = a • K.toTrilinear Z X Y
    rw [map_smul (K.toTrilinear Z X) a Y]

/-- 完整“槽位轮换”三线性映射 `(X, Y, Z) ↦ R(Z, X, Y)`：
供 `ricci` 的 X-线性使用。-/
def endoRicci₂ (K : CurvatureOperator R V) : V →ₗ[R] V →ₗ[R] V →ₗ[R] V where
  toFun X := endoRicci₁ K X
  map_add' := by
    intro X₁ X₂
    apply LinearMap.ext
    intro Y
    apply LinearMap.ext
    intro Z
    change K.toTrilinear Z (X₁ + X₂) Y =
      K.toTrilinear Z X₁ Y + K.toTrilinear Z X₂ Y
    rw [map_add (K.toTrilinear Z) X₁ X₂]
    rw [LinearMap.add_apply]
  map_smul' := by
    intro a X
    apply LinearMap.ext
    intro Y
    apply LinearMap.ext
    intro Z
    change K.toTrilinear Z (a • X) Y = a • K.toTrilinear Z X Y
    rw [map_smul (K.toTrilinear Z) a X]
    rw [LinearMap.smul_apply]

/-- 固定 `X` 后 `Y ↦ ricci K X Y` 是线性的：`trace ∘ (Y ↦ endoRicci K X Y)`。-/
noncomputable def ricciHom (K : CurvatureOperator R V) (X : V) : V →ₗ[R] R where
  toFun Y := LinearMap.trace R V (endoRicci K X Y)
  map_add' := by
    intro Y₁ Y₂
    have hE : endoRicci K X (Y₁ + Y₂) = endoRicci K X Y₁ + endoRicci K X Y₂ := by
      exact map_add (endoRicci₁ K X) Y₁ Y₂
    change LinearMap.trace R V (endoRicci K X (Y₁ + Y₂)) =
      LinearMap.trace R V (endoRicci K X Y₁) + LinearMap.trace R V (endoRicci K X Y₂)
    rw [hE]
    rw [map_add]
  map_smul' := by
    intro a Y
    have hE : endoRicci K X (a • Y) = a • endoRicci K X Y := by
      exact map_smul (endoRicci₁ K X) a Y
    change LinearMap.trace R V (endoRicci K X (a • Y)) =
      a • LinearMap.trace R V (endoRicci K X Y)
    rw [hE]
    rw [map_smul]

/-- **Ricci 收缩**（抽象代数实现，约定收缩第一输入槽与输出槽）：
`ricci K X Y := trace (Z ↦ R(Z,X)Y)`。作为双线性型对象给出，两侧线性均已被验证。
在有限自由模上它等于坐标和 `∑ᵢ coordᵢ (R(eᵢ,X)Y)`（见 `ricci_eq_ricciSum`）。
⚠ 无度量几何含义；与黎曼几何 Ricci 张量的对应留待后续带度量 Stage。-/
noncomputable def ricci (K : CurvatureOperator R V) : V →ₗ[R] V →ₗ[R] R where
  toFun X := ricciHom K X
  map_add' := by
    intro X₁ X₂
    ext Y
    have hE : endoRicci K (X₁ + X₂) Y = endoRicci K X₁ Y + endoRicci K X₂ Y := by
      exact congrArg (fun f : V →ₗ[R] V →ₗ[R] V => f Y) (map_add (endoRicci₂ K) X₁ X₂)
    change LinearMap.trace R V (endoRicci K (X₁ + X₂) Y) =
      LinearMap.trace R V (endoRicci K X₁ Y) + LinearMap.trace R V (endoRicci K X₂ Y)
    rw [hE]
    rw [map_add]
  map_smul' := by
    intro a X
    ext Y
    have hE : endoRicci K (a • X) Y = a • endoRicci K X Y := by
      exact congrArg (fun f : V →ₗ[R] V →ₗ[R] V => f Y) (map_smul (endoRicci₂ K) a X)
    change LinearMap.trace R V (endoRicci K (a • X) Y) =
      a • LinearMap.trace R V (endoRicci K X Y)
    rw [hE]
    rw [map_smul]

/-- 数量曲率收缩所需的最小数据接口：把双线性型 `V × V → R` “提升指标”成自同态的
抽象（`raiseIndex`）。真正的实例必须由度量给出（如黎曼度量的 `sharp` 同构
`V ≃ V*`），本模块**不**提供也不假装提供该实例。-/
structure ScalarContractionData (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V]
    [Module R V] where
  raiseIndex : (V →ₗ[R] V →ₗ[R] R) →ₗ[R] V →ₗ[R] V

/-- **数量曲率收缩接口**：`scalarCurvature K d := trace (d.raiseIndex (ricci K))`。
仅当调用方提供真正来自度量的 `ScalarContractionData` 时才有几何意义；
本模块不声称已实现几何数量曲率。-/
noncomputable def scalarCurvature (K : CurvatureOperator R V)
    (d : ScalarContractionData R V) : R :=
  LinearMap.trace R V (d.raiseIndex (ricci K))

/-- 一致性检查：零算子的 `ricci` 收缩为零双线性型。 -/
lemma ricci_zero : ricci (zero : CurvatureOperator R V) = 0 := by
  apply LinearMap.ext
  intro X
  apply LinearMap.ext
  intro Y
  change LinearMap.trace R V (endoRicci (zero : CurvatureOperator R V) X Y) = 0
  have hEndo : endoRicci (zero : CurvatureOperator R V) X Y = 0 := by
    apply LinearMap.ext
    intro Z
    rfl
  rw [hEndo, map_zero]

/-- 一致性检查：零算子对任意（未来由度量给出的）`ScalarContractionData`
的数量曲率收缩为零。 -/
lemma scalarCurvature_zero (d : ScalarContractionData R V) :
    scalarCurvature (zero : CurvatureOperator R V) d = 0 := by
  unfold scalarCurvature
  rw [ricci_zero, map_zero]
  exact map_zero (LinearMap.trace R V)

end Contraction

/-! ### 有限维自由模：显式基底 + `Finset.univ` 的坐标收缩

在给定了有限基 `e : Module.Basis ι R V`（`ι` 有限）的前提下，`ricci` 的坐标形是
一个真正用 `Finset` 和（底层的 `Finset.univ`）写出的收缩：

`ricciSum e K X Y := ∑ i, e.repr (K (e i) X Y) i`。

并与 mathlib 的基无关迹 `LinearMap.trace` 一致（`ricci_eq_ricciSum`）。-/

section FiniteBasis

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- 对给定的有限基，`LinearMap.trace` 的坐标公式：
`trace L = ∑ i, e.repr (L (e i)) i`（对角线坐标和）。-/
lemma trace_eq_sum_diag (e : Module.Basis ι R V) (L : V →ₗ[R] V) :
    LinearMap.trace R V L = ∑ i : ι, e.repr (L (e i)) i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R e L]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

/-- 用有限基 + `Finset.univ`（经 `∑`）写出的 Ricci 收缩坐标实现
（约定同 `ricci`：收缩第一输入槽与输出槽）。-/
noncomputable def ricciSum (e : Module.Basis ι R V) (K : CurvatureOperator R V) (X Y : V) : R :=
  ∑ i : ι, e.repr (K (e i) X Y) i

/-- 坐标实现与 `LinearMap.trace` 实现一致（在有限自由模 + 该基下）。-/
lemma ricci_eq_ricciSum (e : Module.Basis ι R V) (K : CurvatureOperator R V) (X Y : V) :
    ricci K X Y = ricciSum e K X Y := by
  classical
  rw [ricciSum]
  change LinearMap.trace R V (endoRicci K X Y) = ∑ i : ι, e.repr (K (e i) X Y) i
  exact trace_eq_sum_diag e (endoRicci K X Y)

end FiniteBasis

end CurvatureOperator

end CurvatureAlgebra
end Poincare

