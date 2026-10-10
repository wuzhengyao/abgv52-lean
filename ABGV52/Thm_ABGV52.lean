/-
  ABGV-5.2 —— B 档 · 定理层（**无 sorry、无自造公理**）

  形态说明（与论文的关系，务必读）
  ================================
  论文的完整证明需要 mathlib 没有的理论（flasque 格、D(G)/S(G)、不变域的有理性、
  Endo--Miyata/Voskresenskii 判据）。本文件按用户 2026-09-29 口径做成**无 sorry**：

    * 论文的**逻辑链**在 Lean 里被**真正证明**；
    * 论文的**外部输入**（数值读数 `coh²(H,M) ≅ C_9`；判据）作为定理的**显式假设**
      列出 —— 它们是参数，**不是公理**，更不是 `sorry`；
    * 故本文件证的是：「**若**（论文的两处输入成立）**则**（论文的结论成立）」，
      输入本身由 A 档（`proj-ABGV52-A-tier-certs`）以整数证书机器核对。

  `#print axioms` 断言（文件末）：三条主定理只依赖 propext / Classical.choice /
  Quot.sound —— 无 sorryAx、无自造公理。

  2026-10-10（O1 传播）：§2 有理性侧判据已改**修正序列形**（`IsQuasiPermutation`，
  定义层 `Hyp_ABGV52`）；旧 ⊕-形匿名槽已废（一般情形为假，`EMCounter_ABGV52.lean`；
  替换仅涉槽形状，§1 的 ⊕-形定理 `not_stably_permutation` 依然真且保留）。
-/
import ABGV52.Hyp_ABGV52

namespace ABGV52

/-! ## 0. 算术内核：`C_9` 与「指数整除 3」不相容 -/

/-- `ZMod 9` 中 `3 ≠ 0`。 -/
theorem three_ne_zero_zmod9 : (3 : ZMod 9) ≠ 0 := by decide

/-- 论文 `thm:not-stably-perm` 的算术内核：`coh² ≅ C_9` 排除「指数整除 3」。
（`ZMod 9` 有 9 阶元；若 `3` 消没一切元素则 `3 = 0`，矛盾。） -/
theorem not_exp3_of_iso_C9 (M : Rep ℤ H) (h : Coh2IsoC9 M) :
    ¬ Coh2ExpDvd3 M := by
  obtain ⟨e⟩ := h
  intro hexp
  have hx : e ((3 : ℤ) • e.symm 1) = e 0 := by rw [hexp (e.symm 1)]
  rw [map_zsmul, map_zero, e.apply_symm_apply, Int.smul_one_eq_cast] at hx
  exact three_ne_zero_zmod9 hx

/-- 论文 `prop:M_H-not-permutation` 的判别对内核：`C_9` **且** 指数不整除 3。 -/
theorem discriminant_pair (M : Rep ℤ H) (h9 : Coh2IsoC9 M) :
    Coh2IsoC9 M ∧ ¬ Coh2ExpDvd3 M :=
  ⟨h9, not_exp3_of_iso_C9 M h9⟩

/-! ## 1. 主链（论文 `prop:stable-exp` ＋ `thm:not-stably-perm`） -/

/-- 论文 `thm:not-stably-perm`：由「稳定置换 ⟹ 指数整除 3」与 `C_9` 读数得
`M` 非稳定置换。其中前者是论文 `prop:stable-exp`（其证明用 Shapiro 与加性），
此处作**显式假设**。 -/
theorem not_stably_permutation (M : Rep ℤ H)
    (stable_exp : ∀ L : Rep ℤ H, IsStablyPermutation L → Coh2ExpDvd3 L)
    (h9 : Coh2IsoC9 M) : ¬ IsStablyPermutation M :=
  fun hSP => not_exp3_of_iso_C9 M h9 (stable_exp M hSP)

/-! ## 2. 有理性侧（论文 `thm:not-stably-rational`；**修正判据（序列形）**作显式参数）

  第四十二改（O1）后论文路线：设 `K` 稳定有理，判据（假设）给 `M` 是 quasi-permutation；
  论文新引理 `lem:not-quasi-perm` 又给非 quasi-permutation，矛盾。本件为 T2 陈述锁，
  证明只做 modus tollens 骨架；`¬ IsQuasiPermutation M` 在 `M = M_H_rep` 的已证实例
  见 `EMQuasi_ABGV52.lean`（全闭合消费见 `EM_ABGV52.lean`）。 -/

/-- 论文 `thm:not-stably-rational`（第四十二改后形态）：设 `SRat` 表示「`K` 稳定有理」，
修正判据成立（`SRat K → IsQuasiPermutation M`；⊕-形旧读法一般情形已证为假，
见 `EMCounter_ABGV52.lean`），且 `M` 非 quasi-permutation（论文 `lem:not-quasi-perm`），
则 `K` 非稳定有理。 -/
theorem not_stably_rational (M : Rep ℤ H) (K : Type) (SRat : Type → Prop)
    (hEM : SRat K → IsQuasiPermutation M)
    (hnq : ¬ IsQuasiPermutation M) : ¬ SRat K :=
  fun hK => hnq (hEM hK)

/-! ## 3. 非空性见证（接口→定义的代价：`IsPermutationLattice` 确有实例） -/

/-- 置换格类**非空**：平凡表示 `Z`（= 单点 `H`-集的置换模）是置换格。
（这是把 `IsPermutationLattice` 从接口改为定义后**必须**提供的非空对照。） -/
theorem permutationLattice_nonempty :
    IsPermutationLattice (Rep.ofMulAction ℤ H PUnit) :=
  ⟨PUnit, inferInstance, inferInstance, ⟨CategoryTheory.Iso.refl _⟩⟩

/-! ## 4. 公理闸门（社区标准：无 sorry、无自造公理） -/

#print axioms not_exp3_of_iso_C9
#print axioms discriminant_pair
#print axioms not_stably_permutation
#print axioms not_stably_rational

end ABGV52
