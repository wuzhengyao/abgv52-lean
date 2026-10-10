/-
  ABGV-5.2 —— S5：**接线**（把 S4 的 `stable_exp` 接回 Thm／C8b 的结论层）

  口径说明（为何不直接改 `Thm_ABGV52.lean`）：`Thm_ABGV52` 是 **T2 陈述锁定**件，
  只依赖定义层 `Hyp_ABGV52`，并由 `Challenge_ABGV52`（零 import 主链）独立重写、
  经检查器**逐条比对陈述类型**。若让它 import `S4`（进而 S3/S2/S1 的机械层），
  该比对的意义即被稀释。故**去假设版放在本件**，`Thm` 原文不动。

  内容：论文 `thm:not-stably-perm`／`thm:not-stably-rational` 的**去 `stable_exp` 假设版**
  （`stable_exp` 已由 S4 证明）。
-/
import ABGV52.S4_ABGV52
import ABGV52.C8b_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-- 论文 `thm:not-stably-perm`（**无 `stable_exp` 假设**；
`C_9` 读数仍为假设，其 Lean 实例见 `C8b` 的 `coh2IsoC9_M_H_rep`）。 -/
theorem not_stably_permutation_wired (M : Rep ℤ H) (h9 : Coh2IsoC9 M) :
    ¬ IsStablyPermutation M :=
  not_stably_permutation M stable_exp h9

/-- 论文 `thm:not-stably-rational`（第四十二改修正判据）：剩**修正判据（序列形）**与
`¬ IsQuasiPermutation M_H_rep` 两条输入。后者已由 `EMQuasi_ABGV52.lean` 证明
（本件不 import 它）；全闭合消费版见 `EM_ABGV52.lean` 的 `not_stably_rational_EM`。 -/
theorem not_stably_rational_wired' (K : Type) (SRat : Type → Prop)
    (hEM : SRat K → IsQuasiPermutation M_H_rep)
    (hnq : ¬ IsQuasiPermutation M_H_rep) : ¬ SRat K :=
  not_stably_rational M_H_rep K SRat hEM hnq

/-- 判别对（`C_9` **且** 指数不整除 3）在 `M|_H` 上，且判据版结论去假设。 -/
theorem discriminant_wired : Coh2IsoC9 M_H_rep ∧ ¬ Coh2ExpDvd3 M_H_rep :=
  discriminant_pair_M_H_rep

/-- 论文 `prop:M_H-not-permutation`：`M|_H` **不是**置换 `ℤ[H]`-格。

路线说明（结论与论文同，证明更短；两者输入相同）：
论文原文走 `Ext¹_{ℤ[H]}(I[H], ·) ≅ coh²(H, ·)`（长正合列 ＋ `ℤ[H]` 投射）＋
`lem:perm-class` 收窄到 `8ℤ[H] ⊕ ℤ`；本库改用**对全部置换格**成立的
`prop:perm-exponent`（`S4.perm_exp`，已证）：置换格 ⟹ `coh²` 指数整除 3；
而 `coh²(H, M|_H) ≅ C_9`（`C8b.coh2IsoC9_M_H_rep`）指数为 9 ⟹ 不相容
（`Thm.not_exp3_of_iso_C9`）。等价性：论文证明的判别量 `Ext¹(I[H], L)` 经连接
同态即 `coh²(H, L)`，且论文对一般置换格亦成立（`prop:perm-exponent` 紧随其后
用于 `thm:not-stably-perm`）。

注（读原文时的核对）：论文原证明末句隐含「`M|_H` 置换 ⟹ `M|_H ≅ 8ℤ[H] ⊕ ℤ`」
一步，该步须引 `prop:MH-char` ＋ `lem:perm-class`（第十三改已补显式引用）。
2026-10-01 第十四改起，论文在该证明后**并列第二证明**（`Second proof`）——即
本件路线：`prop:perm-exponent`（`S4.perm_exp`）＋ `coh²(H,M|_H) ≅ C₉`
（`C8b.coh2IsoC9_M_H_rep`）⟹ 矛盾。 -/
theorem M_H_not_permutation : ¬ IsPermutationLattice M_H_rep :=
  fun hP => not_exp3_of_iso_C9 M_H_rep coh2IsoC9_M_H_rep (perm_exp M_H_rep hP)

/-! ## 公理闸门 -/

#print axioms not_stably_permutation_wired
#print axioms not_stably_rational_wired'
#print axioms discriminant_wired
#print axioms M_H_not_permutation

end ABGV52
