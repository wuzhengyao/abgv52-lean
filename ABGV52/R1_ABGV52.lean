/-
  ABGV-5.2 —— R1 件：论文 `thm:retract`（p = 3 特化接线）

  论文：The field \(Z_H(F,9)\) is retract rational over \(F\)。证明四步：
    ① 几何识别 \(Z_H(F,9) \cong F(M|_H)^H\)（`rem:procesi-geometric`，Procesi 1967；char 0）；
    ② \(F(M|_H)^H \cong F(V)^H\)，\(V = M|_H \otimes_{\mathbb{Z}} F\)；
    ③ Saltman 1984 [Corollary 3.13]（\(A = H\)；exp 3 奇 ⟹ \(2^r = 1\)、\(\rho = 1\)、条件空）；
    ④ 忠实性：由 `prop:faithful-MH` 供给。

  本件口径（＝ P 档 P6 `cp_general_4` 的 p = 3 特化 ＋ 接线）
  ========================================================
    * `K`／`RRet` 抽象传入（mathlib 无 retract rationality 理论；`Z_H(F,9)` 亦不在开发中
      构造——与 S5 对 EM 判据的处置同款；Saltman 作带名假设为用户 2026-09-30 裁定）；
    * Saltman 接口形如「**忠实输入 ⟹ retract 结论**」——其前提（exp H = 3 奇 ⟹ 2^r = 1
      条件空；几何识别；char F = 0）按论文口径并入此接口；
    * **忠实性不设假设**：由 F1 件（`F1_ABGV52.lean`）的 `M_H_faithful`（点式）／
      `M_H_rho_injective`（打包式）**填槽**——与 P6 桩（平铺 `saltman_cor313 : RRet K`）
      相比，这是本件的接线增量。证明项显式经过 `P.cp_general_4`（p 一般形；其陈述与 p
      无关（假设桩），故「特化」是名目——p = 3 的实质内容在 C 档物件与 F1 忠实性）。
-/
import ABGV52.F1_ABGV52
import ABGV52.P6_ABGV52

namespace ABGV52

/-- **论文 `thm:retract`（p = 3 特化、接线版）**：设 `RRet : Type → Prop` 为「域在基域上
retract rational」之谓词（mathlib 无此理论，接口传入），且 Saltman 1984 Cor 3.13 在本设置下
成立——形式为「`H` 在 `M|_H` 上作用忠实 ⟹ `K` retract rational」（其余前提按论文口径并入
接口），则 `K` retract rational。**忠实性由 F1 解出**（`M_H_faithful`）。 -/
theorem thm_retract_wired (K : Type) (RRet : Type → Prop)
    (saltman_cor313 : (∀ h : H, h ≠ 1 →
      ∃ z : ↥(LinearMap.ker pi), M_H_rep.ρ h z ≠ z) → RRet K) :
    RRet K :=
  P.cp_general_4 K RRet (saltman_cor313 M_H_faithful)

/-- 同款（打包式槽）：以 `Function.Injective M_H_rep.ρ` 为 Saltman 的忠实输入。 -/
theorem thm_retract_wired_inj (K : Type) (RRet : Type → Prop)
    (saltman_cor313 : Function.Injective M_H_rep.ρ → RRet K) :
    RRet K :=
  P.cp_general_4 K RRet (saltman_cor313 M_H_rho_injective)

/-! ## 公理闸门 -/

#print axioms thm_retract_wired
#print axioms thm_retract_wired_inj

end ABGV52
