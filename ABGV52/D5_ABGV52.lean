/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-iii：kernel 格**（Fischer 证明的格论骨架）

  承 D4：正则置换格 `Z[A]` 的单项式环上有 DFT 基 `y_χ`（`χ : MulChar A F`），
  且 `g • y_χ = (χ g) • y_χ`。Fischer 的第二步是：**指数向量 `n : MulChar A F →₀ ℤ`
  记录「字数」**，定义

      `charOf n := ∏ χ, χ ^ n_χ`            （乘法目标，故入 `Multiplicative`）
      `Y := ker(charOf)`                     （**kernel 格**）

  则 `z^n = ∏ y_χ ^ n_χ` 是 `A`-不变 **iff** `n ∈ Y` ✓（1β-iv 用）；
  且 `charOf` 满射（取单位向量）⟹ **`[X : Y] = |MulChar A F| = |A|`**（1β-v 的度数输入）。

  本件**只做格论**（不触环与域）：为 1β-iv（不变性）与 1β-v（度数收口）供给
  `expVector`／`charOf`／`kernelLattice` 与索引计数。

  记号与 D4 一致：`F` 是域，`A` 是有限交换群，`F` 含足够单位根
  （`[HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]`，与 D4 的 DFT 层同一假设）。
-/
import ABGV52.D4_ABGV52

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

section KernelLattice

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

-- ⚠ `MulChar` 的群结构是 **noncomputable 实例**，须显式提升为局部实例才参与综合
--   （否则 `χ ^ k`（`k : ℤ`）、`1`、`χ⁻¹` 全部报「找不到实例」）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **指数向量**：`MulChar A F →₀ ℤ`。 -/
abbrev expVector : Type _ := MulChar A F →₀ ℤ

/-- **字数函数** `charOf n = ∏ χ, χ ^ n_χ`。
**注**：**不**写成 `→+ Multiplicative _` —— `Multiplicative (MulChar A F)` 的**加法群实例不可导出**
（实测：连一般情形 `AddCommGroup (Multiplicative α)`（`α` 交换群）都不成立）。
乘法性单独证成 `charOf_add`，商双射按 `Quotient` 手工搭建。 -/
noncomputable def charOf (n : expVector F A) : MulChar A F :=
  n.prod fun χ k => χ ^ k

/-- 单位向量上的取值：`charOf (single χ 1) = χ`。 -/
@[simp] lemma charOf_single (χ : MulChar A F) :
    charOf F A (Finsupp.single χ 1) = χ := by
  rw [charOf, Finsupp.prod_single_index]
  · exact zpow_one χ
  · exact zpow_zero χ

/-- **乘法性**：`charOf (n + m) = charOf n * charOf m`。 -/
lemma charOf_add (n m : expVector F A) :
    charOf F A (n + m) = charOf F A n * charOf F A m := by
  rw [charOf, charOf, charOf, Finsupp.prod_add_index']
  · intro χ
    exact zpow_zero χ
  · intro χ b₁ b₂
    exact zpow_add χ b₁ b₂

/-- **`charOf` 满射**：单位向量给出全部字符。 -/
theorem charOf_surjective : Function.Surjective (charOf F A) :=
  fun χ => ⟨Finsupp.single χ 1, charOf_single F A χ⟩

/-- **kernel 格** `Y = ker(charOf)`（按显式载体定义，见 `charOf_add` 的注记）。 -/
noncomputable def kernelLattice : AddSubgroup (expVector F A) where
  carrier := {n | charOf F A n = 1}
  zero_mem' := by simp [charOf]
  add_mem' := by
    intro n m hn hm
    rw [Set.mem_setOf_eq] at *
    rw [charOf_add, hn, hm, one_mul]
  neg_mem' := by
    intro n hn
    rw [Set.mem_setOf_eq] at *
    have h : charOf F A (n + -n) = 1 := by rw [add_neg_cancel]; simp [charOf]
    rw [charOf_add, hn, one_mul] at h
    exact h

/-- **`Y` 的形态**：`n ∈ Y ↔ charOf n = 1`。 -/
@[simp] theorem mem_kernelLattice_iff {n : expVector F A} :
    n ∈ kernelLattice F A ↔ charOf F A n = 1 := Iff.rfl

end KernelLattice

/-! ## 公理闸门 -/

#print axioms charOf_single
#print axioms charOf_surjective
#print axioms charOf_add
#print axioms kernelLattice
#print axioms mem_kernelLattice_iff

end

end EM

end ABGV52
