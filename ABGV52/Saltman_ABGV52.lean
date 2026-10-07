/-
  ABGV-5.2 —— **具名假设档 2/3**：Saltman 1984 Corollary 3.13（retract rationality）

  口径（用户 2026-10-07 指令「ABGV5.2 还有 3 处需要形式化」之第二项）
  ================================================================
  论文 `thm:retract` 主链第 ③ 步与 `thm:Cp-general` (4) 引用 **Saltman 1984
  Corollary 3.13**（A = H；exp H = 3 奇 ⟹ 2^r = 1、ρ = 1，条件空）：配合几何识别
  （Procesi 1967）与忠实性（`prop:faithful-MH`）得 `Z_H(F,9)` retract rational。
  mathlib 无 retract rationality 理论 ⟹ 按 G 档 `ProcesiHyp` 同款工艺给出**具名假设**：

    * `SaltmanHyp` —— 接口外形「**忠实性输入 ⟹ retract 结论**」（其前提 exp 奇 /
      条件空 / 几何识别 / char F = 0 按论文口径**并入接口**——用户 2026-09-30 裁定，
      见 `P6_ABGV52` 头注与 `R1_ABGV52` 头注）；
    * **类型锁定断言**（`rfl`）；
    * **接线定理**：`SaltmanHyp` ＋ F1 解出的忠实性（`M_H_rho_injective`）⟹ `RRet K`；
    * **非空洞探针**（L1）：假设类非空；
    * 公理闸门。

  与既有匿名槽的关系：`R1.thm_retract_wired_inj`（打包式）与 `P6.cp_general_4`
  （p 一般、结论桩）本轮**保持不动**；本件给具名外形，接线定理与之等价（忠实性填槽
  方式相同——`M_H_rho_injective` 即 F1 的打包式忠实输入）。

  KB 笔记：`-Saltman1984-thm-cor3.13`。

  **无 sorry、无自造公理**。
-/
import ABGV52.F1_ABGV52

namespace ABGV52

/-! ## 1. 具名假设外形 ＋ 类型锁定 -/

/-- **Saltman 1984 Cor 3.13 的具名假设**（论文主链第 ③ 步的接口形）：
若 H 在 `M_H_rep` 上的作用**忠实**（`Function.Injective M_H_rep.ρ`），则 `K`
（＝ `Z_H(F,9)`）**retract rational**（以抽象谓词 `RRet K` 传入）。 -/
def SaltmanHyp (K : Type) (RRet : Type → Prop) : Prop :=
  Function.Injective M_H_rep.ρ → RRet K

/-- **类型锁定断言**：`SaltmanHyp` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (K : Type) (RRet : Type → Prop) :
    SaltmanHyp K RRet = (Function.Injective M_H_rep.ρ → RRet K) := rfl

/-! ## 2. 接线（忠实性输入由 F1 解出） -/

/-- 论文 `thm:retract` 的 Saltman **具名假设版**：忠实性由 F1 的
`M_H_rho_injective`（打包式；即 `prop:faithful-MH` 的初等直证）填槽。 -/
theorem thm_retract_Saltman (K : Type) (RRet : Type → Prop)
    (hS : SaltmanHyp K RRet) : RRet K :=
  hS M_H_rho_injective

/-! ## 3. 非空洞探针（L1：假设类非空） -/

/-- 探针：取 `RRet := fun _ => True`，假设类非空（结论非空洞）。 -/
theorem SaltmanHyp_satisfiable (K : Type) :
    SaltmanHyp K (fun _ => True) :=
  fun _ => trivial

/-! ## 4. 公理闸门 -/

#print axioms thm_retract_Saltman
#print axioms SaltmanHyp_satisfiable

end ABGV52
