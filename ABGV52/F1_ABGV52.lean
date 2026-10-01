/-
  ABGV-5.2 —— F1 件：论文 `prop:faithful-MH`（H 在 M|_H 上作用＝对角作用之限制；且忠实）

  论文陈述（两段）
  ==============
    (A)「The action of H on M|_H is the restriction of the diagonal left-regular
        action on ℤ[H]^{⊕9}」——本库中 V := H → ℤ[H]（坐标模型，G2），对角作用 = G2 的
        `act`（= 论文 `prop:tensor-reg-ZH` 明述的「左乘 ＋ 坐标置换 b ↦ hb」：
        (act h z) i = h · z (h⁻¹ i)）；M|_H := ker π（C8 的 `M_H_rep`），其作用由
        `M_H_act` 定义为 `act` 之限制——本件固化为 `M_H_rho_isRestriction`。
    (B)「This action is faithful」——本件给**初等直证**（`M_H_faithful`）：
        对任意 h ≠ 1，显式见证 z_h ∈ ker π（槽 1 放 h−1、槽 h 放 1−h；其余槽 0），
        且 (act h z_h) 1 = 0 ≠ (z_h) 1 = h−1 ⟹ act h z_h ≠ z_h。

  与论文证明的关系（诚实边界）
  ==========================
    论文对 (B) 走几何层（M₉(F) 上忠实 ＋ Procesi 同构 Z_H(F,9) ≅ F(M|_H)^H 交织作用
    ＋分式域函子性）——该层在开发中是**具名假设**。本件**不经过**该层：直接对 ker π 的
    元素算，故 (B) 在格层无条件成立（也顺带说明该几何输入对 (B) 并非必要）。
    路线差异属「同命题、两证法」，与 `{prop:M_H-not-permutation}` 同款口径。

  读原文时的核对（留档）
  ====================
    `prop:faithful-MH` 把对角作用写成 h·(x₁,…,x₉) = (hx₁,…,hx₉)（**无**坐标置换），
    与论文自身 `prop:tensor-reg-ZH`（「that is, left multiplication composed with the
    coordinate permutation b ↦ hb」）及开发全局所用（`act`；`pi_equivariant` 所证相容）
    不一致——疑为该展示式漏写置换项。本件按 `prop:tensor-reg-ZH` 的作用形式化。
    2026-10-01 第十五改（用户指令）：论文已按其自身 `prop:tensor-reg-ZH` 修正该式，
    并新增 (B) 忠实性的**第二证明**（初等直证）＝本件路线的论文对应。
-/
import ABGV52.C8_ABGV52

namespace ABGV52

/-! ## 0. 群论预备（H = C_3 × C_3，exp = 3） -/

/-- `H` 的指数为 3（有限型，`decide`；与 `S4_ABGV52.H_pow_three` 内容相同、独立重写）。 -/
theorem H_cube : ∀ x : H, x ^ 3 = 1 := by decide

/-- `h ^ 2 = 1 ⟹ h = 1`（orderOf ∣ 2、∣ 3 ⟹ ∣ gcd = 1）。 -/
theorem sq_eq_one_imp_eq_one (h : H) (h2 : h ^ 2 = 1) : h = 1 := by
  have d2 : orderOf h ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have d3 : orderOf h ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (H_cube h)
  have d1 : orderOf h ∣ 1 := by
    simpa using Nat.dvd_gcd d2 d3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp d1)

/-- `h ≠ 1 ⟹ h⁻¹ ≠ h`（h⁻¹ = h ⟹ h² = 1 ⟹ h = 1）。 -/
theorem inv_ne_self (h : H) (hh : h ≠ 1) : h⁻¹ ≠ h := by
  intro hih
  have h2 : h ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hih]
    rw [inv_mul_cancel]
  exact hh (sq_eq_one_imp_eq_one h h2)

/-! ## 1. (A)：作用＝对角作用（`act`）之限制 -/

/-- `M_H_rep` 的作用是 `act` 在 `ker π` 上的限制（论文 (A) 的 Lean 对应；
作用形式以 `prop:tensor-reg-ZH` 为准）。 -/
theorem M_H_rho_isRestriction (h : H) (z : ↥(LinearMap.ker pi)) :
    (M_H_rep.ρ h z).1 = act h z.1 := rfl

/-! ## 2. (B)：忠实性——显式见证 -/

/-- 见证向量 z_h：槽 1 放 `h − 1`，槽 h 放 `1 − h`，其余为 0。 -/
noncomputable def witVec (h : H) : V :=
  fun i => if i = 1 then (MonoidAlgebra.single h 1 - 1)
           else if i = h then (1 - MonoidAlgebra.single h 1) else 0

lemma witVec_one (h : H) : witVec h 1 = MonoidAlgebra.single h 1 - 1 := by
  simp [witVec]

lemma witVec_self (h : H) (hh : h ≠ 1) :
    witVec h h = 1 - MonoidAlgebra.single h 1 := by
  simp [witVec, hh]

lemma witVec_of_ne (h b : H) (hb1 : b ≠ 1) (hbh : b ≠ h) : witVec h b = 0 := by
  simp [witVec, hb1, hbh]

lemma aug_witVec_one (h : H) : aug (witVec h 1) = 0 := by
  rw [witVec_one, map_sub, aug_single, MonoidAlgebra.one_def, aug_single, sub_self]

lemma aug_witVec_self (h : H) (hh : h ≠ 1) : aug (witVec h h) = 0 := by
  rw [witVec_self h hh, map_sub, MonoidAlgebra.one_def, aug_single, aug_single,
    sub_self]

/-- **z_h ∈ ker π**：恰在槽 {1, h} 取值 (h−1, 1−h)，其和为零、增广皆零。 -/
theorem witVec_mem_ker (h : H) (hh : h ≠ 1) : witVec h ∈ LinearMap.ker pi := by
  rw [LinearMap.mem_ker, pi, LinearMap.sum_apply]
  have hpair : (∑ b : H, piTerm b (witVec h))
      = ∑ b ∈ ({1, h} : Finset H), piTerm b (witVec h) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro b _ hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    rw [piTerm_apply, witVec_of_ne h b hb.1 hb.2, map_zero, zero_smul, sub_zero]
  rw [hpair, Finset.sum_pair (Ne.symm hh), piTerm_apply, piTerm_apply,
    aug_witVec_one, aug_witVec_self h hh, witVec_one, witVec_self h hh,
    zero_smul, zero_smul]
  abel

/-- **z_h 的见证性**：`act h z_h ≠ z_h`（在槽 1 处比较：左端 = 0，右端 = h−1 ≠ 0）。 -/
theorem act_witVec_ne (h : H) (hh : h ≠ 1) : act h (witVec h) ≠ witVec h := by
  intro heq
  have h1 := congrFun heq 1
  rw [act_apply, mul_one] at h1
  rw [witVec_of_ne h h⁻¹ (inv_ne_one.mpr hh) (inv_ne_self h hh)] at h1
  rw [witVec_one, show lmul h (0 : MonoidAlgebra ℤ H) = 0 from mul_zero _] at h1
  have hs : MonoidAlgebra.single h 1 = (1 : MonoidAlgebra ℤ H) :=
    sub_eq_zero.mp h1.symm
  have hs' : MonoidAlgebra.single h (1 : ℤ)
      = MonoidAlgebra.single (1 : H) (1 : ℤ) := by
    rw [hs, MonoidAlgebra.one_def]
  exact hh (MonoidAlgebra.single_left_injective (by norm_num) hs')

/-! ## 3. 主定理：忠实性 -/

/-- 见证性（子类型层）：见证明 `z_h` 的轨道非平凡。 -/
theorem M_H_witness (h : H) (hh : h ≠ 1) :
    M_H_rep.ρ h ⟨witVec h, witVec_mem_ker h hh⟩
      ≠ ⟨witVec h, witVec_mem_ker h hh⟩ := by
  intro heq
  exact act_witVec_ne h hh (by
    have hv := congrArg Subtype.val heq
    rwa [M_H_rho_isRestriction h ⟨witVec h, witVec_mem_ker h hh⟩] at hv)

/-- **论文 `prop:faithful-MH`（第二句）**：H 在 `M|_H` 上的作用忠实——
对任意 h ≠ 1，作用在见证 `z_h` 上非平凡。 -/
theorem M_H_faithful (h : H) (hh : h ≠ 1) :
    ∃ z : ↥(LinearMap.ker pi), M_H_rep.ρ h z ≠ z :=
  ⟨⟨witVec h, witVec_mem_ker h hh⟩, M_H_witness h hh⟩

/-- 核形式：`ρ h = 1 ⟹ h = 1`。 -/
theorem M_H_rho_eq_one (h : H) (heq : M_H_rep.ρ h = 1) : h = 1 := by
  by_contra hh
  obtain ⟨z, hz⟩ := M_H_faithful h hh
  exact hz (by rw [heq]; rfl)

/-- **论文 `prop:faithful-MH` 的打包形式**：表示 `ρ : H →* End(M|_H)` 单射。 -/
theorem M_H_rho_injective : Function.Injective M_H_rep.ρ := by
  intro a b hab
  have h1 : a⁻¹ * b = 1 := M_H_rho_eq_one (a⁻¹ * b) (by
    rw [map_mul]
    have hcancel : M_H_rep.ρ a⁻¹ * M_H_rep.ρ a = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [← hcancel, hab])
  exact inv_mul_eq_one.mp h1

/-! ## 公理闸门 -/

#print axioms M_H_rho_isRestriction
#print axioms witVec_mem_ker
#print axioms act_witVec_ne
#print axioms M_H_witness
#print axioms M_H_faithful
#print axioms M_H_rho_eq_one
#print axioms M_H_rho_injective

end ABGV52
