/-
  ABGV-5.2 —— **本体形式化 B · Salt* 条件层**：Saltman 1984 Cor 3.13 的「2^r 条件」

  论文侧对应（逐字）
  ==================
  论文 `thm:saltman-cor3.13`（`raw/ABGV-5.2-resolution.tex` :1272–1280）：
  「Let A be a finite abelian group, and let 2^r be the highest power of 2 dividing
   the exponent of A. Assume F is a field such that either F has characteristic 2
   or F(ρ)/F is a cyclic extension, where ρ is a primitive 2^r-th root of unity.
   Let V be a finitely generated F[A]-module on which A acts faithfully. Then
   F(V)^A is retract rational over F.」（引用：Saltman1984, Corollary 3.13）
  论文用法：`thm:retract`（A = H = C₃×C₃，exp H = 3 奇 ⟹ 2^r = 1、ρ = 1、
  条件空）与 `thm:Cp-general` (4)。

  **路线对齐注记（头注必写项）**
  ==============================
  * 论文侧该定理的自然语言「证明」= **无**——纯外部引用（Saltman1984 Cor 3.13）；
    Lean 侧 `Saltman_ABGV52.lean` 把它压缩为具名假设 `SaltmanHyp`。
  * Lean 路线 = Salt* 内部工程（M1/M2 已交付）＋本波**条件层**（本件）＋
    [23] 残差具名（`SaltGeneric_ABGV52.lean`）——与论文引用结构对齐
    （同样把它**当假设用**）。
  * **偏离登记**：本波**不触碰** M3–M6 工程（不假装已证）。本件只做一件事：把
    `SaltmanHyp` 黑箱前提中**可无条件化为定理**的那一片——对 H 而言即「2^r 条件
    空」——从「压缩进接口」升级为**库内定理**（`saltmanCondition_H`）。

  本件内容
  ========
  1. **条件谓词**（源条件逐字对应的形式化）：
     * `twoPowerPart n = 2 ^ padicValNat 2 n` ——「2^r = 整除 exp(A) 的最高 2 幂」；
       `twoPowerPart_dvd`（2^r ∣ n）与 `twoPowerPart_maximal`（2·2^r ∤ n）合取
       即「最高」；
     * `IsCyclicExtension F E := IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E)`；
     * `SaltmanCondition A F := ringChar F = 2 ∨ ∃ (L) (ρ : L), ρ 本原 2^r 次单位根
       ∧ F(ρ)/F 循环`——第二析取以子域 `F⟮ρ⟯` 表达「F(ρ)/F」。
  2. **平凡循环扩张引擎**（`subsingleton_algEquiv_bot`、`isCyclic_algEquiv_bot`、
     `isCyclicExtension_adjoin_one_self`）：`F⟮(1 : F)⟯ = ⊥` 且 `Gal(↥⊥/F)` 平凡
     （故循环）——奇指数分支的全部内容。
  3. **主定理**：
     * `saltman_condition_of_char_two`：`ringChar F = 2` ⟹ 条件成立；
     * `saltman_condition_of_odd_exponent`：`exp(A)` 奇 ⟹ 条件对**任意** F 成立
       （2^r = 2^0 = 1、ρ = 1、F(1)/F = F/F 循环）——即论文 `thm:retract` 所引
       的「条件空」在本层成为定理；
     * `saltmanCondition_H`：A = H（exp H ∣ 3 ⟹ 奇）的实例。
  4. **定义外形锁定**（`rfl`）＋**非空洞/判别力探针**（L1/L19）＋公理闸门。

  形式化约定（与逐字的偏差，均显式登记）
  =====================================
  * 「A 有限交换」：本层只要求 `[Group A]`——**条件谓词自身**不依赖 A 的有限性与
    交换性（那两条是 cor3.13 结论侧假设，属装配层 M6）；本层不形式化之。
  * 「ρ 本原 2^r 次单位根」：`IsPrimitiveRoot ρ (twoPowerPart (Monoid.exponent A))`
    ——对 2^r = 1 特化为 `IsPrimitiveRoot ρ 1`（⟺ ρ = 1），即奇指数分支；
    该特化的见证取 ρ = 1（`IsPrimitiveRoot.one`）。∃ L 是最宽的存在形式
    （与源「ρ 为本原单位根」一致：F 的代数闭包中总存在）。
  * 「F(ρ)/F 循环」：形式化为 `IsCyclicExtension F ↥(F⟮ρ⟯)`——即**子域 F(ρ)**
    上的循环 Galois 扩张（不是某个更大的 L）。与源文逐字对应。
  * 「F 特征 2」：`ringChar F = 2`。

  **无 sorry、无自造公理**。
-/
import ABGV52.F1_ABGV52
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Field.ZMod

universe u v

namespace ABGV52

open scoped IntermediateField

/-! ## 1. 条件层（源条件逐字对应） -/

/-- 「`E/F` 是循环扩张」（`IsGalois` ＋ Galois 群循环）。 -/
def IsCyclicExtension (F E : Type v) [Field F] [Field E] [Algebra F E] : Prop :=
  IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E)

/-- `2 ^ r`，其中 `2 ^ r` 是整除 `n` 的最高 2 幂（`r = padicValNat 2 n`）。 -/
def twoPowerPart (n : ℕ) : ℕ := 2 ^ padicValNat 2 n

/-- 「最高」之一：2^r ∣ n。 -/
theorem twoPowerPart_dvd (n : ℕ) : twoPowerPart n ∣ n := pow_padicValNat_dvd

/-- 「最高」之二：**没有更高**——2·2^r = 2^(r+1) ∤ n（`n ≠ 0` 时）。 -/
theorem twoPowerPart_maximal {n : ℕ} (hn : n ≠ 0) : ¬ 2 * twoPowerPart n ∣ n := by
  simpa [twoPowerPart, pow_succ, mul_comm] using
    pow_succ_padicValNat_not_dvd (p := 2) (n := n) hn

/-- **Saltman 条件**（Saltman1984 Cor 3.13 的假设）：`A` 为群、`F` 为域，

  「F 特征 2，或 F(ρ)/F 是循环扩张，其中 ρ 是本原 2^r 次单位根、
    2^r 是整除 exp(A) 的最高 2 幂」。

第二析取的 ∃ 取最宽形式：ρ 落在 F 的任意扩张 `L` 中（源语义：单位根总存在），
「F(ρ)/F 循环」以子域 `F⟮ρ⟯` 上的循环 Galois 性表达。 -/
def SaltmanCondition (A : Type u) [Group A] (F : Type v) [Field F] : Prop :=
  ringChar F = 2 ∨
    ∃ (L : Type v) (_ : Field L) (_ : Algebra F L) (ρ : L),
      IsPrimitiveRoot ρ (twoPowerPart (Monoid.exponent A)) ∧
        IsCyclicExtension F ↥(F⟮ρ⟯)

/-- **定义外形锁定**：`SaltmanCondition` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (A : Type u) [Group A] (F : Type v) [Field F] :
    SaltmanCondition A F = (ringChar F = 2 ∨
      ∃ (L : Type v) (_ : Field L) (_ : Algebra F L) (ρ : L),
        IsPrimitiveRoot ρ (twoPowerPart (Monoid.exponent A)) ∧
          IsCyclicExtension F ↥(F⟮ρ⟯)) := rfl

/-! ## 2. 平凡循环扩张（奇指数分支的引擎） -/

/-- **`↥⊥` 的 F-代数自同构群平凡**：`↥(⊥ : IntermediateField F E)` 的每个元素都是
`F` 在 `E` 中的像（`mem_bot`），而 F-代数自同构在像上固定（`commutes`）⟹ 只有恒等。 -/
theorem subsingleton_algEquiv_bot (F E : Type v) [Field F] [Field E] [Algebra F E] :
    Subsingleton (↥(⊥ : IntermediateField F E) ≃ₐ[F] ↥(⊥ : IntermediateField F E)) :=
  ⟨fun f g => AlgEquiv.ext fun x => by
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp x.2
    have hx : x = algebraMap F ↥(⊥ : IntermediateField F E) c := Subtype.ext hc.symm
    rw [hx, f.commutes, g.commutes]⟩

/-- `Gal(↥⊥ / F)` 循环（平凡群 ⟹ 循环，`isCyclic_of_subsingleton`）。 -/
theorem isCyclic_algEquiv_bot (F E : Type v) [Field F] [Field E] [Algebra F E] :
    IsCyclic (↥(⊥ : IntermediateField F E) ≃ₐ[F] ↥(⊥ : IntermediateField F E)) := by
  have : Subsingleton (↥(⊥ : IntermediateField F E) ≃ₐ[F] ↥(⊥ : IntermediateField F E)) :=
    subsingleton_algEquiv_bot F E
  infer_instance

/-- **奇指数分支的见证**：`F(1)/F`——`F⟮(1 : F)⟯ = ⊥`，故 `Gal = 1` 循环。 -/
theorem isCyclicExtension_adjoin_one_self (F : Type v) [Field F] :
    IsCyclicExtension F ↥(F⟮(1 : F)⟯) := by
  have h : F⟮(1 : F)⟯ = (⊥ : IntermediateField F F) := IntermediateField.adjoin_one
  constructor
  · rw [h]; infer_instance
  · rw [h]; exact isCyclic_algEquiv_bot F F

/-! ## 3. 主定理 -/

/-- 特征 2 分支：`ringChar F = 2` ⟹ 条件成立（对任意 A）。 -/
theorem saltman_condition_of_char_two {A : Type u} [Group A] {F : Type v} [Field F]
    (h : ringChar F = 2) : SaltmanCondition A F :=
  Or.inl h

/-- **奇指数 ⟹ 条件成立（对任意 F）**：2^r = 2^0 = 1、ρ = 1、
`F(1)/F = F/F` 平凡扩张循环。即论文 `thm:retract` 所引的「条件空」——在本层
成为库内定理。 -/
theorem saltman_condition_of_odd_exponent {A : Type u} [Group A] {F : Type v} [Field F]
    (hA : Odd (Monoid.exponent A)) : SaltmanCondition A F := by
  right
  have h0 : padicValNat 2 (Monoid.exponent A) = 0 :=
    padicValNat.eq_zero_of_not_dvd (Odd.not_two_dvd_nat hA)
  have h1 : twoPowerPart (Monoid.exponent A) = 1 := by
    rw [twoPowerPart, h0, pow_zero]
  refine ⟨F, inferInstance, inferInstance, (1 : F), ?_, ?_⟩
  · rw [h1]
    exact IsPrimitiveRoot.one
  · exact isCyclicExtension_adjoin_one_self F

/-! ## 4. H-档实例（论文 `thm:retract` 的 A = H） -/

/-- `exp H` 为奇数：`exp H ∣ 3`（`H_cube` ＋ `exponent_dvd_iff_forall_pow_eq_one`），
故 `exp H ∈ {1, 3}`，两者皆奇。 -/
theorem exponent_H_odd : Odd (Monoid.exponent H) := by
  have hdvd : Monoid.exponent H ∣ 3 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr H_cube
  rcases Nat.prime_three.eq_one_or_self_of_dvd (Monoid.exponent H) hdvd with h | h
  · rw [h]; exact odd_one
  · rw [h]; exact (by decide : Odd 3)

/-- **H-档条件空（论文 `thm:retract` 的「2^r = 1、ρ = 1，条件空」）**：
`SaltmanCondition H F` 对**任意**域 `F` 成立。 -/
theorem saltmanCondition_H (F : Type v) [Field F] : SaltmanCondition H F :=
  saltman_condition_of_odd_exponent (A := H) (F := F) exponent_H_odd

/-! ## 5. 探针（L1 非空洞 ＋ L19 判别力） -/

/-- 判别力：`twoPowerPart` 真的返回「最高 2 幂」——8 ↦ 8（不是 1）。 -/
example : twoPowerPart 8 = 8 := by
  have hle : 3 ≤ padicValNat 2 8 :=
    (padicValNat_dvd_iff_le (p := 2) (a := 8) (n := 3) (by norm_num)).mp (by norm_num)
  have hlt : ¬ 4 ≤ padicValNat 2 8 := fun h =>
    absurd ((padicValNat_dvd_iff_le (p := 2) (a := 8) (n := 4) (by norm_num)).mpr h)
      (by norm_num)
  rw [twoPowerPart, show padicValNat 2 8 = 3 by omega]
  norm_num

/-- 判别力：6 = 2·3 ↦ 2（真取 2-部分，非恒等、非恒 1）。 -/
example : twoPowerPart 6 = 2 := by
  have hle : 1 ≤ padicValNat 2 6 :=
    (padicValNat_dvd_iff_le (p := 2) (a := 6) (n := 1) (by norm_num)).mp (by norm_num)
  have hlt : ¬ 2 ≤ padicValNat 2 6 := fun h =>
    absurd ((padicValNat_dvd_iff_le (p := 2) (a := 6) (n := 2) (by norm_num)).mpr h)
      (by norm_num)
  rw [twoPowerPart, show padicValNat 2 6 = 1 by omega]
  norm_num

/-- 奇参数 ↦ 1（奇指数分支的算术）。 -/
example : twoPowerPart 3 = 1 := by
  rw [twoPowerPart, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), pow_zero]

/-- 「最高」的判别：2·twoPowerPart 8 = 16 ∤ 8。 -/
example : ¬ 2 * twoPowerPart 8 ∣ 8 := twoPowerPart_maximal (by norm_num)

/-- L1 非空洞（H-档）：条件在战役实际用例 `H, ℚ` 上成立。 -/
example : SaltmanCondition H ℚ := saltmanCondition_H ℚ

/-- L1 非空洞（char 2 分支）：`ZMod 2` 上条件经第一析取成立。 -/
example : SaltmanCondition H (ZMod 2) :=
  saltman_condition_of_char_two (ZMod.ringChar_zmod_n 2)

/-! ## 6. 公理闸门 -/

#print axioms twoPowerPart_dvd
#print axioms twoPowerPart_maximal
#print axioms subsingleton_algEquiv_bot
#print axioms isCyclic_algEquiv_bot
#print axioms isCyclicExtension_adjoin_one_self
#print axioms saltman_condition_of_char_two
#print axioms saltman_condition_of_odd_exponent
#print axioms exponent_H_odd
#print axioms saltmanCondition_H

end ABGV52
