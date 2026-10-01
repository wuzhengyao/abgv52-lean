/-
  ABGV-5.2 —— (2) 两条目 · **条目 1 续：`prop:MH-char` 的 ℚ-侧维数（`finrank ℚ = 73`）**

  承接 `MH_ABGV52.lean`（无条件部分：换基管道 ＋ `ℚ[H] ≅ I_ℚ ⊕ ℚ` 显式分裂 ＋ `finrank ℚ I_ℚ = 8`）。
  本件按其登记的 **∅-formalization-gap 路线 2（ℚ-模型直做）** 补上论文 `:760–808` 中
  `rk_ℤ M|_H = 73` 的 **ℚ-侧对应读数**：

    `finrank ℚ (ker π_ℚ) = 81 − 8 = 73`，

  其中 `π_ℚ : ℚ[H]^{⊕9} → ℚ[H]` 是论文 `prop:procesi-H` 的 `π|_H` 在 ℚ 上的**逐字复制**
  （同坐标、同公式 `Σ_b (z_b − ε(z_b)·b)`），`ker π_ℚ` 即 `M|_H ⊗ ℚ` 的 ℚ-模型。

  路线 2 的桥（**仍属已登记的 gap (α)+(β)**，本件不声称）
  ======================================================
  **【2026-10-01 更新（L4）】该桥已由 `BR_ABGV52.lean` 收口**：
  `eFinalLeft : ℚ ⊗[ℤ] ↥(ker pi) ≃ₗ[ℚ] (Fin 8 → R) × ℚ`（接本件
  `eMain`），并有字面右形式 `eFinalRight`／`bridge_MH_char` 与
  `finrank_ker_tensor : finrank ℚ (↥(ker pi) ⊗[ℤ] ℚ) = 73`；
  **H-等变层亦已收口**（`bridge_MH_char_equivariant : eFinalRight (g • z) =
  single g 1 • eFinalRight z`）。
  本段以下文字保留为历史登记。
  论文/ℤ-侧的 `M|_H ⊗[ℤ] ℚ` 与本件 `ker π_ℚ` 之间的识别需要
  (α) 一般子模的 `Module ℚ (M ⊗[ℤ] ℚ)` ＋ (β) `ker(f) ⊗ ℚ ≅ ker(f ⊗ id)`；
  本件给的是**结构等同的 ℚ-模型端**（dim 73 的读数在此端无条件成立）。
  与 `PC_ABGV52` 的关系：两件共用「73 = 81 − 8」这一算术链，但管道不同
  （PC 用 `Finset`/迹抽取，本件用 Procesi 复形的秩-零化度）。

  与 P 档（`P1_ABGV52`）的关系
  ============================
  本件 = `P1` 的 ℤ → ℚ 特化（p = 3，`H = C3 × C3`）；`P1` 一字未动；两件的证明骨架相同
  （`evalQ`／`piTermQ`／`piQ`／`deltaVec`／系数展开），差别仅在标量环与 `augQ` 的来源
  （本件复用 `MH.augQ`，经 `coeffLinearEquiv` ∘ `Finsupp.linearCombination` 定义）。
-/
import ABGV52.MH_ABGV52

namespace ABGV52.MQ

/-! ## 1. ℚ-侧 Procesi 复形（论文 `prop:procesi-H` 的 ℚ-模型） -/

/-- 环绕模 `ℚ[H]^{⊕9}`（坐标 = `H` 的元素，共 9 个）。 -/
abbrev VQ : Type := H → MonoidAlgebra ℚ H

/-- 取第 `b` 个坐标。 -/
noncomputable def evalQ (b : H) : VQ →ₗ[ℚ] MonoidAlgebra ℚ H where
  toFun z := z b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma evalQ_apply (b : H) (z : VQ) : evalQ b z = z b := rfl

/-- 单坐标贡献 `z ↦ z_b − ε(z_b)·b`。 -/
noncomputable def piTermQ (b : H) : VQ →ₗ[ℚ] MonoidAlgebra ℚ H :=
  evalQ b - (LinearMap.toSpanSingleton ℚ (MonoidAlgebra ℚ H)
    (MonoidAlgebra.single b (1 : ℚ))).comp ((MH.augQ).comp (evalQ b))

lemma piTermQ_apply (b : H) (z : VQ) :
    piTermQ b z = z b - MH.augQ (z b) • MonoidAlgebra.single b (1 : ℚ) := by
  simp only [piTermQ, LinearMap.sub_apply, evalQ_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]

/-- **Procesi 映射** `π_ℚ : ℚ[H]^{⊕9} → ℚ[H]`。 -/
noncomputable def piQ : VQ →ₗ[ℚ] MonoidAlgebra ℚ H := ∑ b : H, piTermQ b

/-! ## 2. 满射性：`range π_ℚ = I_ℚ`（论文 `prop:procesi-H` 的两方向） -/

lemma augQ_piTermQ (b : H) (z : VQ) : MH.augQ (piTermQ b z) = 0 := by
  rw [piTermQ_apply, map_sub, map_smul, MH.augQ_single, smul_eq_mul, mul_one, sub_self]

/-- 方向 ①：`range π_ℚ ⊆ I_ℚ`。 -/
theorem range_piQ_le : LinearMap.range piQ ≤ MH.IQ := by
  intro w hw
  obtain ⟨z, rfl⟩ := hw
  show MH.augQ (piQ z) = 0
  rw [piQ, LinearMap.sum_apply, map_sum]
  exact Finset.sum_eq_zero (fun b _ => augQ_piTermQ b z)

/-- 只在槽 `1` 放 `single h 1` 的向量。 -/
noncomputable def deltaVec (h : H) : VQ :=
  fun b => if b = 1 then MonoidAlgebra.single h (1 : ℚ) else 0

lemma piQ_deltaVec (h : H) : piQ (deltaVec h) = MonoidAlgebra.single h 1 - 1 := by
  rw [piQ, LinearMap.sum_apply, Finset.sum_eq_single (1 : H)]
  · rw [piTermQ_apply, deltaVec, if_pos rfl, MH.augQ_single, one_smul]
    rfl
  · intro b _ hb
    rw [piTermQ_apply, deltaVec, if_neg hb, map_zero, zero_smul, sub_zero]
  · intro hnot
    exact absurd (Finset.mem_univ (1 : H)) hnot

lemma smul_single_one (c : ℚ) (g : H) :
    c • MonoidAlgebra.single g (1 : ℚ) = MonoidAlgebra.single g c := by
  simp

lemma eq_sum_coeff_smul_single (w : MonoidAlgebra ℚ H) :
    w = ∑ g : H, (w.coeff g) • MonoidAlgebra.single g (1 : ℚ) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single w]
  rw [Finsupp.sum_fintype w.coeff (fun g c => MonoidAlgebra.single g c)
    (by intro g; simp)]
  exact Finset.sum_congr rfl (fun g _ => (smul_single_one (w.coeff g) g).symm)

lemma augQ_eq_sum_coeff (w : MonoidAlgebra ℚ H) :
    MH.augQ w = ∑ g : H, w.coeff g := by
  conv_lhs => rw [eq_sum_coeff_smul_single w]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun g _ => by rw [map_smul, MH.augQ_single, smul_eq_mul, mul_one])

lemma eq_sum_coeff_smul_sub_one (w : MonoidAlgebra ℚ H) (hw : MH.augQ w = 0) :
    w = ∑ g : H, (w.coeff g) • (MonoidAlgebra.single g (1 : ℚ) - 1) := by
  have hsplit : (∑ g : H, (w.coeff g) • (MonoidAlgebra.single g (1 : ℚ) - 1))
      = (∑ g : H, (w.coeff g) • MonoidAlgebra.single g (1 : ℚ))
        - (∑ g : H, (w.coeff g) • (1 : MonoidAlgebra ℚ H)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun g _ => smul_sub _ _ _)
  rw [hsplit, ← eq_sum_coeff_smul_single w]
  have hconst : (∑ g : H, (w.coeff g) • (1 : MonoidAlgebra ℚ H)) = (MH.augQ w) • 1 := by
    rw [augQ_eq_sum_coeff w, Finset.sum_smul]
  rw [hconst, hw, zero_smul, sub_zero]

/-- 方向 ②：`I_ℚ ⊆ range π_ℚ`（`I_ℚ` 被 `h − 1` 生成）。 -/
theorem range_piQ_ge : MH.IQ ≤ LinearMap.range piQ := by
  intro w hw
  have hw0 : MH.augQ w = 0 := hw
  rw [eq_sum_coeff_smul_sub_one w hw0]
  refine Submodule.sum_mem _ (fun g _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  exact ⟨deltaVec g, piQ_deltaVec g⟩

/-- **`range π_ℚ = I_ℚ`**（论文 `prop:procesi-H` 满射性的 ℚ-模型）。 -/
theorem range_piQ_eq : LinearMap.range piQ = MH.IQ :=
  le_antisymm range_piQ_le range_piQ_ge

/-! ## 3. 维数：`finrank ℚ (ker π_ℚ) = 73` -/

/-- `finrank ℚ ℚ[H] = 9`。 -/
lemma finrank_monoidAlgebra_Q : Module.finrank ℚ (MonoidAlgebra ℚ H) = 9 := by
  rw [LinearEquiv.finrank_eq (MonoidAlgebra.coeffLinearEquiv ℚ),
    Module.finrank_finsupp_self ℚ, MH.card_H]

/-- `finrank ℚ V = 81`（`9` 个坐标 × `9` 维）。 -/
lemma finrank_VQ : Module.finrank ℚ VQ = 81 := by
  show Module.finrank ℚ (H → MonoidAlgebra ℚ H) = 81
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, MH.card_H,
    finrank_monoidAlgebra_Q]
  norm_num

/-- **论文 `rk_ℤ M|_H = 73`／`prop:MH-char` 的 ℚ-侧读数**：
`finrank ℚ (ker π_ℚ) = 81 − 8 = 73`（秩-零化度 ＋ `range π_ℚ = I_ℚ` ＋ `finrank ℚ I_ℚ = 8`）。 -/
theorem finrank_ker_piQ : Module.finrank ℚ ↥(LinearMap.ker piQ) = 73 := by
  have h := LinearMap.finrank_range_add_finrank_ker piQ
  rw [range_piQ_eq, MH.finrank_IQ, finrank_VQ] at h
  omega

/-- **Procesi 短正合列的 ℚ-模型**：`0 → ker π_ℚ → V → I_ℚ → 0`（逐元素形）。 -/
theorem procesiQ_exact (z : ↥(LinearMap.ker piQ)) :
    piQ z.1 = 0 ∧ ∀ w : VQ, piQ w = 0 → w ∈ LinearMap.range (LinearMap.ker piQ).subtype :=
  ⟨z.2, fun w hw => ⟨⟨w, hw⟩, rfl⟩⟩

/-! ## 4. 公理闸门（无 sorry、无自造公理） -/

#print axioms range_piQ_eq
#print axioms finrank_VQ
#print axioms finrank_ker_piQ
#print axioms procesiQ_exact

end ABGV52.MQ
