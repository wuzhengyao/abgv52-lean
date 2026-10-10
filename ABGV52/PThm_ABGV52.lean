/-
  ABGV-5.2 —— **P 档 T2 陈述锁定**：`thm:Cp-general` 的**条件命题形态**

  口径（照 B 档工艺）：本件只锁**陈述**——把 `thm:Cp-general` 的四条写成
  「上同调输入 ＋ 转移界」显式假设下的条件命题（这才是可被独立重写对照的**公开陈述形态**；
  论文的 (3)(4) 本身即以此为条件）。证明直接调用 P 档已交付件（`perm_exp`／`stable_exp`）。

  ⚠ ∝-stale（O1 修正，2026-10-10）：`pThm_not_stably_rational`／`pThm_not_rational` 的
  `criterion` 参数为 **⊕-形旧判据**（一般情形已证为假，见 `EMCounter_ABGV52.lean`）；
  P 档修正序列形（q-p）与其 `¬q-p(M_rep p)` 反证**待下一波**（H 档同路线已完成：
  `EMQuasi_ABGV52.lean`；B 档陈述对已改锁，见 `Thm_ABGV52.lean` §2）。陈述暂不改锁——
  `PChallenge` 逐条比对须同轮改形；消费端 `EM_ABGV52.cp_general_3b_EM` 同标 ∝-stale。

  对应的独立重写件 = `PChallenge_ABGV52.lean`（**零 import 主链**，自足定义同形陈述）；
  检查器逐条比对两份文件的陈述类型（防「全文件一致的替换」）。
-/
import ABGV52.P6_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

/-- 论文 (2) 的抽象形：置换格上 `exp(coh²) ∣ p`。 -/
theorem pThm_perm_exp (L : Rep ℤ (Hp p)) (hL : IsPermutationLattice L) :
    Coh2ExpDvdp p L :=
  perm_exp L hL

/-- 论文 (3) 的第一句的抽象形：`coh² ≅ Z/p²` ＋ 转移界 ⟹ 非稳定置换。 -/
theorem pThm_not_stably_perm (M : Rep ℤ (Hp p))
    (h2 : Nonempty (↥(groupCohomology M 2) ≃ₗ[ℤ] ZMod (p * p)))
    (hexp : ∀ L : Rep ℤ (Hp p), IsPermutationLattice L → Coh2ExpDvdp p L) :
    ¬ IsStablyPermutation M := by
  obtain ⟨e⟩ := h2
  intro hSP
  have hkill : (p : ℤ) • (1 : ZMod (p * p)) = 0 := by
    have hx : (p : ℤ) • e.symm (1 : ZMod (p * p)) = 0 :=
      stable_exp M hSP _
    have := congrArg e hx
    simpa using this
  exact p_smul_one_zmod_ne_zero p hkill

/-- 论文 (3) 的有理性侧：再加 EM 判据（作假设）⟹ 非稳定有理。 -/
theorem pThm_not_stably_rational (M : Rep ℤ (Hp p)) (K : Type) (SRat : Type → Prop)
    (criterion : SRat K ↔ IsStablyPermutation M)
    (h2 : Nonempty (↥(groupCohomology M 2) ≃ₗ[ℤ] ZMod (p * p)))
    (hexp : ∀ L : Rep ℤ (Hp p), IsPermutationLattice L → Coh2ExpDvdp p L) :
    ¬ SRat K :=
  fun hK => pThm_not_stably_perm p M h2 hexp (criterion.mp hK)

/-- 论文 (3) 的「从而非有理」。 -/
theorem pThm_not_rational (M : Rep ℤ (Hp p)) (K : Type) (SRat : Type → Prop)
    (criterion : SRat K ↔ IsStablyPermutation M)
    (h2 : Nonempty (↥(groupCohomology M 2) ≃ₗ[ℤ] ZMod (p * p)))
    (hexp : ∀ L : Rep ℤ (Hp p), IsPermutationLattice L → Coh2ExpDvdp p L)
    (Rat : Type → Prop) (hRatSRat : Rat K → SRat K) : ¬ Rat K :=
  fun hK => pThm_not_stably_rational p M K SRat criterion h2 hexp (hRatSRat hK)

/-- 论文 (4)：以 Saltman 1984 Cor 3.13 为**带名假设**。 -/
theorem pThm_retract (K : Type) (RRet : Type → Prop) (saltman_cor313 : RRet K) : RRet K :=
  saltman_cor313

/-! ## 公理闸门 -/

#print axioms pThm_perm_exp
#print axioms pThm_not_stably_perm
#print axioms pThm_not_stably_rational
#print axioms pThm_not_rational
#print axioms pThm_retract

end ABGV52.P
