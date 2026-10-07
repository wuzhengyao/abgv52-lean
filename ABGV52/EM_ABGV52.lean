/-
  ABGV-5.2 —— **具名假设档 1/3**：Endo--Miyata--Voskresenskii 判据（论文 `thm:endo-miyata`）

  口径（用户 2026-10-07 指令「ABGV5.2 还有 3 处需要形式化」之第一项）
  ================================================================
  论文 `thm:endo-miyata`（第三十改后**环境内仅存数学陈述**）：
    设 G 为有限群、M 为忠实 ℤ[G]-格、F 为特征 0 域；若 F(M)^G **稳定有理**，
    则 M 为**稳定置换** ℤ[G]-格。
  论文随后明说「**We use this criterion as a hypothesis**; it is not proved in this
  paper」——即外部输入（Endo--Miyata / Colliot-Thélène--Sansuc / Voskresenskii 判据；
  文献中无对 F(M)^G 形式的整句出处，见论文 §2 环境外评述段与 2026-09-30 引文勘误注释）。
  mathlib 无有理性/稳定有理性/稳定置换格的理论区段（本库的稳定置换为**具体定义**，
  见 `Hyp_ABGV52`）⟹ 按 G 档 `ProcesiHyp` 同款工艺给出**具名假设**：

    * `EMHyp` —— 判据的**定义外形**（通用形，对任意 `M : Rep ℤ H`）；
    * **类型锁定断言**（`rfl`）——外形一旦改动立即编译失败（阶段 5.5 第 5 条）；
    * **接线定理**：H 档（论文主情形，p = 3）与 P 档（p 一般）各一条，
      消费 `EMHyp` 推出有理性侧结论；
    * **非空洞探针**（L1）：假设类非空；
    * 公理闸门 `#print axioms`。

  方向说明（与论文第三十改对齐）
  ==============================
  论文第三十改后只陈述**单向**「稳定有理 ⟹ 稳定置换」，本外形与之逐字一致
  （既有匿名槽 `criterion : SRat K ↔ IsStablyPermutation M` 为**双向**；其一切使用
  均只取 `.mp` 方向，故单向形**足以**替代。既有匿名槽本轮**保持不动**——零改动、
  零回归；本件定理独立消费单向形，构成具名版主线）。

  **无 sorry、无自造公理**。
-/
import ABGV52.S5_ABGV52
import ABGV52.P6_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## 1. 具名假设外形 ＋ 类型锁定 -/

/-- **Endo--Miyata--Voskresenskii 判据（论文 `thm:endo-miyata`）的具名假设**
（H 档 / 论文主情形）：`F(M)^G` 稳定有理（以抽象谓词 `SRat K` 传入）⟹ `M` 稳定置换。 -/
def EMHyp (M : Rep ℤ H) (K : Type) (SRat : Type → Prop) : Prop :=
  SRat K → IsStablyPermutation M

/-- **类型锁定断言**：`EMHyp` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (M : Rep ℤ H) (K : Type) (SRat : Type → Prop) :
    EMHyp M K SRat = (SRat K → IsStablyPermutation M) := rfl

/-! ## 2. 接线（H 档：论文主情形） -/

/-- 论文 `thm:not-stably-rational` 的 EM 判据**具名假设版**（H 档）：
由 `EMHyp` 与 S5 已证的 `¬ IsStablyPermutation M_H_rep`（经 `C_9` 读数）得 `¬ SRat K`。 -/
theorem not_stably_rational_EM (K : Type) (SRat : Type → Prop)
    (hEM : EMHyp M_H_rep K SRat) : ¬ SRat K :=
  fun hK => not_stably_permutation_wired M_H_rep coh2IsoC9_M_H_rep (hEM hK)

/-! ## 3. 接线（P 档：p 一般；对应 `P` 档自有的稳定置换谓词） -/

variable (p : ℕ) [Fact p.Prime]

/-- **P 档（p 一般）的 EM 判据具名假设**：与 `EMHyp` 同形，但稳定置换取
`ABGV52.P.IsStablyPermutation`（P 档自有的参数化谓词；三套平行定义
（`Hyp`／`D1` 的 `EM`／`P`）系历史分层，各档内自洽，此处按档取用。
变量 `p` 显式（本档 `variable (p : ℕ)`；`P.IsStablyPermutation` 自身的 `p` 为隐式，
经 `M` 的类型定出）。 -/
def EMHypP (M : Rep ℤ (P.Hp p)) (K : Type) (SRat : Type → Prop) : Prop :=
  SRat K → P.IsStablyPermutation M

/-- **类型锁定断言**（P 档）。 -/
example (M : Rep ℤ (P.Hp p)) (K : Type) (SRat : Type → Prop) :
    EMHypP p M K SRat = (SRat K → P.IsStablyPermutation M) := rfl

/-- 论文 `thm:Cp-general` (3) 有理性侧的 EM 判据**具名假设版**：
由 `EMHypP` 与 P6 已证的 `¬ IsStablyPermutation (M_rep p)` 得 `¬ SRat K`。 -/
theorem cp_general_3b_EM (K : Type) (SRat : Type → Prop)
    (hEM : EMHypP p (P.M_rep p) K SRat) : ¬ SRat K :=
  fun hK => P.cp_general_3a p (hEM hK)

/-! ## 4. 非空洞探针（L1：假设类非空） -/

/-- 探针：取 `SRat := fun _ => IsStablyPermutation M_H_rep`，恒等即实例
（判据假设类非空，结论非空洞）。 -/
theorem EMHyp_satisfiable (K : Type) :
    EMHyp M_H_rep K (fun _ => IsStablyPermutation M_H_rep) :=
  fun h => h

/-! ## 5. 公理闸门 -/

#print axioms not_stably_rational_EM
#print axioms cp_general_3b_EM
#print axioms EMHyp_satisfiable

end ABGV52
