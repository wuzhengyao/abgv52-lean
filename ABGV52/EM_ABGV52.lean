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

  方向说明（与论文第四十二改对齐；2026-10-10 O1 修正）
  ================================================
  论文第三十改后只陈述**单向**；**第四十二改**把结论由 ⊕-形「stably permutation」
  更正为**序列形「quasi-permutation」**——⊕-形一般陈述为假（反例 G = C2、M = sign：
  F(M)^G 有理而 M 非 ⊕-稳定置换；机器核证件 `EMCounter_ABGV52.lean`；源精度与
  裁决备忘见 `wiki/proj-ABGV52-EM-criterion-correction.md`）。本外形与论文现行
  陈述逐字一致（`EM.IsQuasiPermutation`，见 `EMQuasi_ABGV52.lean`）；
  消费端 `not_stably_rational_EM` 现取 `EMQuasi.not_isQuasiPermutation_M_H_rep`
  （LES 反证——与论文新引理 `lem:not-quasi-perm` 同路线）。**B 档旧匿名槽
  `criterion : SRat K ↔ IsStablyPermutation M` 已收口（O1 传播，2026-10-10）**：
  定义层增 `Hyp.IsQuasiPermutation`（`Hyp_ABGV52.lean`），`Thm`／`Challenge`
  陈述对改锁修正序列形，消费端 `C8b.not_stably_rational_wired`／
  `S5.not_stably_rational_wired'` 重接线；层间桥 `EMQuasi.EM.isQuasiPermutation_iff`
  （`Iff.rfl`）。论文 `thm:not-stably-perm`（⊕-形）依然真且保留
  （`not_stably_permutation` 不动）。P 档槽（`PThm`／`PChallenge`／`P6` 的
  `criterion`）仍 ∝-stale：待 P 档 q-p 反证 `¬ IsQuasiPermutation (M_rep p)`（同路线）。

  **无 sorry、无自造公理**。
-/
import ABGV52.S5_ABGV52
import ABGV52.P6_ABGV52
import ABGV52.EMQuasi_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## 1. 具名假设外形 ＋ 类型锁定 -/

/-- **Endo--Miyata--Voskresenskii 判据（论文 `thm:endo-miyata`）的具名假设**
（H 档 / 论文主情形；**第四十二改后为修正序列形**）：`F(M)^G` 稳定有理
（以抽象谓词 `SRat K` 传入）⟹ `M` 是 quasi-permutation（序列形，
见 `EMQuasi_ABGV52.lean` 的 `EM.IsQuasiPermutation`）。 -/
def EMHyp (M : Rep ℤ H) (K : Type) (SRat : Type → Prop) : Prop :=
  SRat K → EM.IsQuasiPermutation H M

/-- **类型锁定断言**：`EMHyp` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (M : Rep ℤ H) (K : Type) (SRat : Type → Prop) :
    EMHyp M K SRat = (SRat K → EM.IsQuasiPermutation H M) := rfl

/-! ## 2. 接线（H 档：论文主情形） -/

/-- 论文 `thm:not-stably-rational` 的 EM 判据**具名假设版**（H 档；第四十二改重接线）：
由 `EMHyp`（修正序列形）与 `EMQuasi` 已证的 `¬ EM.IsQuasiPermutation H M_H_rep`
（Ext 协变 LES 反证，与论文新引理 `lem:not-quasi-perm` 同路线）得 `¬ SRat K`。 -/
theorem not_stably_rational_EM (K : Type) (SRat : Type → Prop)
    (hEM : EMHyp M_H_rep K SRat) : ¬ SRat K :=
  fun hK => not_isQuasiPermutation_M_H_rep (hEM hK)

/-! ## 3. 接线（P 档：p 一般；对应 `P` 档自有的稳定置换谓词） -/

variable (p : ℕ) [Fact p.Prime]

/-- **P 档（p 一般）的 EM 判据具名假设**（⚠ **∝-stale，第四十二改**：此形仍为
⊕-形「稳定置换」——已废弃的旧读法；P 档修正序列形（q-p）与其 LES 反证
**待下一波**（H 档已完成：`EMQuasi_ABGV52.lean`）。本形保留仅为历史与形状对照，
其消费端 `cp_general_3b_EM` 同标 ∝-stale。）：与 `EMHyp` 旧形同构，但稳定置换取
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

/-- 探针：取 `SRat := fun _ => EM.IsQuasiPermutation H M_H_rep`，恒等即实例
（判据假设类非空，结论非空洞；第四十二改后随修正形更新）。 -/
theorem EMHyp_satisfiable (K : Type) :
    EMHyp M_H_rep K (fun _ => EM.IsQuasiPermutation H M_H_rep) :=
  fun h => h

/-! ## 5. 公理闸门 -/

#print axioms not_stably_rational_EM
#print axioms cp_general_3b_EM
#print axioms EMHyp_satisfiable

end ABGV52
