/-
  ABGV-5.2 —— **P 档 P6：装配论文 `thm:Cp-general` 的四条**

  论文（`raw/ABGV-5.2-resolution.tex:1192`）四条：
    (1) `coh²(H, M|_H) ≅ C_{p²}`；
    (2) 任意置换 `ℤ[H]`-格 `P`，`exp(coh²(H,P)) ∣ p`；
    (3) 于是 `M|_H` **非**稳定置换，且 `Z_H(F,p²)` **非**稳定有理（从而非有理）；
    (4) `Z_H(F,p²)` **retract rational**。

  对应本档已交付件
  ==============
    (1) ← `P4` 的 `H2_MH_equiv_zmod`；
    (2) ← `P5b` 的 `perm_exp`；
    (3) ← (1) ＋ `P5b` 的 `stable_exp`（若 `M|_H` 稳定置换，则 `p` 消没 `coh²`；但
        `coh² ≅ ZMod (p*p)` 含阶 `p²` 元素 ⟹ 矛盾）；有理性侧按论文走 EM 判据（作假设）；
    (4) ← **Saltman 1984 Cor 3.13 作显式假设**（用户 2026-09-30 裁定）：mathlib 无
        retract rationality 理论，本档不形式化该外部定理，只把「`K` 是 retract rational」
        作为**带名假设**传入，使假设表显式可见。

  ⚠ 口径：本件的 (3)(4) 是**条件命题**（前提为 EM 判据／Saltman 定理），与论文正文一致
  （论文亦把二者作假设／引用）。`(1)(2)` 及「非稳定置换」的 `(3a)` **无条件**。
-/
import ABGV52.P4_ABGV52
import ABGV52.P5b_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 论文 (1)：`coh²(H, M|_H) ≅ C_{p²}` -/

/-- **`thm:Cp-general` (1)**：`coh²(H, M|_H) ≅ C_{p²}`（＝ `P4` 的 `H2_MH_equiv_zmod`）。 -/
noncomputable def cp_general_1 :
    ↥(groupCohomology (M_rep p) 2) ≃ₗ[ℤ] ZMod (p * p) :=
  H2_MH_equiv_zmod p

/-! ## 2. 论文 (2)：置换格上 `exp(coh²) ∣ p` -/

/-- **`thm:Cp-general` (2)**：任意置换 `ℤ[H]`-格 `P`，`(p : ℤ)` 消没 `coh²(H,P)`
（＝ `P5b` 的 `perm_exp`）。 -/
theorem cp_general_2 (P : Rep ℤ (Hp p)) (hP : IsPermutationLattice P) :
    Coh2ExpDvdp p P :=
  perm_exp P hP

/-! ## 3. 论文 (3a)：`M|_H` 非稳定置换（**无条件**） -/

/-- `ZMod (p*p)` 中 `1` 不被 `p` 消没（`p ≥ 2` 时 `p ∤ p²`）。 -/
lemma p_smul_one_zmod_ne_zero : (p : ℤ) • (1 : ZMod (p * p)) ≠ 0 := by
  intro h
  have hcast : ((p : ℤ) : ZMod (p * p)) = 0 := by simpa using h
  have hdvd : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (p : ℤ) (p * p)).mp hcast
  have hp2 : 2 ≤ p := two_le_p p
  have hlt : (p : ℤ) < ((p * p : ℕ) : ℤ) := by
    have : p < p * p := by nlinarith
    exact_mod_cast this
  have hpos : (0 : ℤ) < (p : ℤ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  exact absurd (Int.le_of_dvd hpos hdvd) (by omega)

/-- **`thm:Cp-general` (3) 的第一句**：`M|_H` **非**稳定置换。 -/
theorem cp_general_3a : ¬ IsStablyPermutation (M_rep p) := by
  intro hSP
  have hkill : (p : ℤ) • (1 : ZMod (p * p)) = 0 := by
    have hx : (p : ℤ) • (H2_MH_equiv_zmod p).symm (1 : ZMod (p * p)) = 0 :=
      stable_exp (M_rep p) hSP _
    have := congrArg (H2_MH_equiv_zmod p) hx
    simpa using this
  exact p_smul_one_zmod_ne_zero p hkill

/-! ## 4. 论文 (3b)(3c)：`Z_H(F,p²)` 非稳定有理（从而非有理）——**以 EM 判据为假设** -/

/-- **`thm:Cp-general` (3) 的有理性侧**：设 `SRat` 表示「`K` 稳定有理」且 EM 判据成立
（`SRat K ↔ IsStablyPermutation M_rep`），则 `K` 非稳定有理。 -/
theorem cp_general_3b (K : Type) (SRat : Type → Prop)
    (criterion : SRat K ↔ IsStablyPermutation (M_rep p)) : ¬ SRat K :=
  fun hK => cp_general_3a p (criterion.mp hK)

/-- **`thm:Cp-general` (3) 的「从而非有理」**：再由「有理 ⟹ 稳定有理」得非有理。 -/
theorem cp_general_3c (K : Type) (SRat : Type → Prop)
    (criterion : SRat K ↔ IsStablyPermutation (M_rep p))
    (Rat : Type → Prop) (hRatSRat : Rat K → SRat K) : ¬ Rat K :=
  fun hK => cp_general_3b p K SRat criterion (hRatSRat hK)

/-! ## 5. 论文 (4)：`Z_H(F,p²)` retract rational ——**以 Saltman Cor 3.13 为显式假设** -/

/-- **`thm:Cp-general` (4)**：`Z_H(F,p²)` retract rational。

**口径（用户 2026-09-30 裁定）**：论文此处引用 **Saltman 1984 Cor 3.13**（外部已发表定理；
KB 有 `-Saltman1984-thm-cor3.13` 笔记）。mathlib 无 retract rationality 理论 ⟹ 本档
**不形式化该定理本身**，只把「`K` 是 retract rational」这一**结论**作为**带名假设**
`saltman_cor313` 传入，使假设表在类型里显式可见（与 C 档对 EM 判据的处置同款）。 -/
theorem cp_general_4 (K : Type) (RRet : Type → Prop) (saltman_cor313 : RRet K) : RRet K :=
  saltman_cor313

/-! ## 6. 公理闸门 -/

#print axioms cp_general_1
#print axioms cp_general_2
#print axioms p_smul_one_zmod_ne_zero
#print axioms cp_general_3a
#print axioms cp_general_3b
#print axioms cp_general_3c
#print axioms cp_general_4

end ABGV52.P
