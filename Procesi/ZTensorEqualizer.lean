/-
  Procesi —— **等化子引理**：`K ⊗_Z K` 中 `x ⊗_t 1 = 1 ⊗_t x` 迫使 `x ∈ Z`

  来源：Saltman 1999, `raw/Saltman1999ch14.tex:321`（`thm:14.16` 的证明）——
  "Since `Z` is a field, it is clear that for `x ∈ K`, `x ∈ Z` if and only if
  `η_1(x) = η_2(x)`."

  **本件要说明的一件事：这条的最小前提是"`K` 在 `Z` 上自由"，不是"可分"。**
  `Z` 是域 ⟹ `K` 是自由 `Z`-模 ⟹ 取一组 `Z`-基，`K ⊗_Z K` 以 `{b ⊗ b'}` 为基，
  比较 `x ⊗ 1` 与 `1 ⊗ x` 的坐标即知：凡基元 `b ≠ 1` 的系数必须为 `0`。
  本节把这一步做成**坐标泛函**形态（不需要 `DecidableEq`、不需要 `baseChange`）：

  1. 取 `K` 的 `L`-基坐标泛函 `π`（在某 `(b.repr 1) i₀ ≠ 0` 处取值），归一化成 `π 1 = 1`；
  2. 把 `π ⊗ id` 接到张量上：`x ⊗ 1 ↦ algebraMap (π x)`、`1 ⊗ x ↦ algebraMap (π 1) * x = x`；
  3. 故 `x = algebraMap (π x) ∈ ⊥`，即 `x ∈ L`。

  **用途**：`(B)` 层的同一条（`EtaEqualizerHyp`）已由 `H2Final` §58 无条件证明；
  `(A)` 层的 `EqualizerHyp`（`GenericInv:3097`）在 `GenericInv` 里一直以"须 `K` 的一个
  `Z`-基含 `1`（或分离泛函 `K →ₗ[Z] Z`），本工作区未做"登记为未证。本件把它变成
  **无条件定理**（对**任意**中间域 `Z`，见 `equalizerHyp`）。

  **射程（勿夸大）**：本件只给等化子事实。`hZ`（`prop:14.19` 后半）**未证**；
  **H2 仍不是定理**。
-/

import Procesi.GenericInv

open scoped TensorProduct

namespace Procesi

/-! ## §1 一般域论形态（任意域扩张 `L → K`） -/

section General

variable {L K : Type*} [Field L] [Field K] [Algebra L K]

/-- **存在取值非零的 `L`-线性泛函**：取 `K` 的 `L`-基坐标，在 `1` 的坐标非零处取值。

`K` 是域故 `Module.Free.of_divisionRing` 给出基；`1 ≠ 0` 故其坐标函数不是零函数，
于是某个坐标在 `1` 处非零。 -/
theorem exists_dual_apply_one_ne_zero : ∃ π : K →ₗ[L] L, π 1 ≠ 0 := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex L K) L K := Module.Free.chooseBasis L K
  have hne : b.repr (1 : K) ≠ 0 := by
    intro h
    have h2 : b.repr (1 : K) = b.repr (0 : K) := by rw [h, map_zero]
    exact one_ne_zero (b.repr.injective h2)
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  exact ⟨b.coord i, by rw [Module.Basis.coord_apply]; exact Finsupp.mem_support_iff.mp hi⟩

#print axioms exists_dual_apply_one_ne_zero

/-- ★★★★★ **等化子的域论核心**：`x ⊗ 1 = 1 ⊗ x`（在 `K ⊗_L K` 中）⟹ `x ∈ L`。

**证明只读坐标**：把 `π ⊗ id`（`π` 归一化成 `π 1 = 1`）接到张量上，两侧分别得
`algebraMap (π x)` 与 `algebraMap (π 1) * x = x`。与 `char`、可分性、有限性**均无关**。 -/
theorem mem_bot_of_tmul_one_eq (x : K)
    (h : x ⊗ₜ[L] (1 : K) = (1 : K) ⊗ₜ[L] x) : x ∈ (⊥ : Subalgebra L K) := by
  classical
  obtain ⟨π₀, hπ₀⟩ := exists_dual_apply_one_ne_zero (L := L) (K := K)
  let π : K →ₗ[L] L := (π₀ 1)⁻¹ • π₀
  have hπ : π 1 = 1 := by
    simp only [π, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hπ₀
  have key : ∀ y : K,
      (TensorProduct.lid L K) (TensorProduct.map π (LinearMap.id : K →ₗ[L] K)
        (y ⊗ₜ[L] (1 : K))) = algebraMap L K (π y) := by
    intro y
    simp [Algebra.algebraMap_eq_smul_one]
  have key2 : ∀ y : K,
      (TensorProduct.lid L K) (TensorProduct.map π (LinearMap.id : K →ₗ[L] K)
        ((1 : K) ⊗ₜ[L] y)) = algebraMap L K (π 1) * y := by
    intro y
    simp [Algebra.smul_def]
  have h3 : algebraMap L K (π x) = algebraMap L K (π 1) * x := by
    rw [← key x, ← key2 x, h]
  rw [hπ, map_one, one_mul] at h3
  exact Algebra.mem_bot.mpr ⟨π x, h3⟩

#print axioms mem_bot_of_tmul_one_eq

end General

/-! ## §2 中间域形态（`C : IntermediateField F K`） -/

section Inter

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- ★★★★★ **中间域形态**：`C ≤ K` 是中间域，`x ⊗ 1 = 1 ⊗ x`（在 `K ⊗_C K` 中）⟹ `x ∈ C`。

这是 `prop:14.19`（`:456`）与 `thm:14.16`（`:321`）里"`η₁(x) = η₂(x) ⟺ x ∈ Z`"的
**`⟸` 方向**的完整内容，对**任意**中间域成立。 -/
theorem mem_intermediateField_of_tmul_one_eq (C : IntermediateField F K) {x : K}
    (h : x ⊗ₜ[↥C] (1 : K) = (1 : K) ⊗ₜ[↥C] x) : x ∈ C := by
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp (mem_bot_of_tmul_one_eq (L := ↥C) (K := K) x h)
  rw [← hy]
  exact y.2

#print axioms mem_intermediateField_of_tmul_one_eq

end Inter

/-! ## §3 应用：`(A)` 层的具名 Prop `EqualizerHyp` 是**无条件定理**

`GenericInv:3097` 的 `EqualizerHyp` 一直是 `(A)` 层（`thm:14.16`）的"唯一域论输入"，
其 docstring 登记"须 `K` 的一个 `Z`-基含 `1`（或分离泛函 `K →ₗ[Z] Z`），本工作区未做"。
本节按 §2 把它消掉：`etaK1 = includeLeft`、`etaK2 = includeRight` 都是 `def`，故
`EqualizerHyp F r n Z` 的假设**就是** `x ⊗ 1 = 1 ⊗ x`（定义等价），一行应用即可。

| 件 | 内容 |
|---|---|
| ★★★★★ `equalizerHyp` | **`EqualizerHyp F r n Z` 无条件成立**（对任意中间域 `Z`） |

**与 `(B)` 层的关系**：`(B)` 层的同一条 `EtaEqualizerHyp`（`H2Final:5527`）已由
`H2Final` §58（`mem_sprCenterImageField_of_eta_eq`／`etaEqualizerHyp_unconditional`）
无条件证明，用的是 `TensorProduct.finsuppScalarRight` ＋ `repr.baseChange` 的路线。
本件的 §1／§2 给的是同一条内容在**更一般载体**（任意域扩张／任意中间域）上的形态。

**射程（勿夸大）**：`(A)` 层的其余具名 Prop（`EqualizerHyp` 之外的 `XiBasisHyp`、
`MatrixRatioHyp`、`KPFixedLeZ`）**均未证**；`(A)` 层**不在** H2 的终点链上
（终点链见 `H2Final` §213／§214）；`hZ` **未证**；**H2 仍不是定理**。 -/

section Apply

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`EqualizerHyp` 是无条件定理**（`GenericInv:3097` 的具名 Prop 被淘汰）。 -/
theorem equalizerHyp (Z : IntermediateField F (SField F r n)) :
    EqualizerHyp F r n Z :=
  fun _x hx => mem_intermediateField_of_tmul_one_eq Z hx

#print axioms equalizerHyp

end Apply

end Procesi
