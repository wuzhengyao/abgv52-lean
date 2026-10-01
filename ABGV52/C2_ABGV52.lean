/-
  ABGV-5.2 —— C 档第一刀 · 步 2：反向包含 `I[H] ≤ range π`

  论文的论证（Lean 化）
  ==================
    设 `w ∈ I[H]`，即 `ε(w) = 0`。把 `w` 按系数展开：
        w = Σ_g (w.coeff g) • (single g 1)          （`MonoidAlgebra.sum_coeff_single`）
          = Σ_g (w.coeff g) • (single g 1 − 1)      （因为 Σ_g (w.coeff g) = ε(w) = 0）
    而每个 `single g 1 − 1 = π (deltaVec g)` 落在 `range π` 内（步 1 的 `pi_deltaVec`），
    `range π` 是子模 ⟹ 上述 ℤ-线性组合仍落在 `range π` 内。

  与步 1 合起来得 **`range π = I[H]`**（论文 `prop:procesi-H` 的满射性）。
-/
import ABGV52.C1_ABGV52

namespace ABGV52

/-! ## 1. 系数展开与 `ε` 的系数和公式 -/

/-- `c • single g 1 = single g c`（`Z`-标量与 `single` 的交换）。 -/
lemma smul_single_one (c : ℤ) (g : H) :
    c • MonoidAlgebra.single g (1 : ℤ) = MonoidAlgebra.single g c := by
  simp

/-- `w = Σ_g (w.coeff g) • single g 1`（`Finsupp` 展开的全集形式）。 -/
lemma eq_sum_coeff_smul_single (w : MonoidAlgebra ℤ H) :
    w = ∑ g : H, (w.coeff g) • MonoidAlgebra.single g (1 : ℤ) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single w]
  rw [Finsupp.sum_fintype w.coeff (fun g c => MonoidAlgebra.single g c)
      (by intro g; simp)]
  exact Finset.sum_congr rfl (fun g _ => (smul_single_one (w.coeff g) g).symm)

/-- `ε(w) = Σ_g w.coeff g`（系数和），由线性性与 `aug_single` 推出，不展开定义。 -/
lemma aug_eq_sum_coeff (w : MonoidAlgebra ℤ H) :
    aug w = ∑ g : H, w.coeff g := by
  conv_lhs => rw [eq_sum_coeff_smul_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [aug_smul', aug_single, mul_one]

/-! ## 2. 分解：`w = Σ_g (w.coeff g) • (single g 1 − 1)`（当 `ε(w) = 0`） -/

lemma eq_sum_coeff_smul_sub_one (w : MonoidAlgebra ℤ H) (hw : aug w = 0) :
    w = ∑ g : H, (w.coeff g) • (MonoidAlgebra.single g (1 : ℤ) - 1) := by
  have hsplit : (∑ g : H, (w.coeff g) • (MonoidAlgebra.single g (1 : ℤ) - 1))
      = (∑ g : H, (w.coeff g) • MonoidAlgebra.single g (1 : ℤ))
        - (∑ g : H, (w.coeff g) • (1 : MonoidAlgebra ℤ H)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun g _ => smul_sub _ _ _)
  rw [hsplit, ← eq_sum_coeff_smul_single w]
  have hconst : (∑ g : H, (w.coeff g) • (1 : MonoidAlgebra ℤ H)) = (aug w) • 1 := by
    rw [aug_eq_sum_coeff, Finset.sum_smul]
  rw [hconst, hw, zero_smul, sub_zero]

/-! ## 3. 反向包含与等式 -/

theorem range_pi_ge : I_H ≤ LinearMap.range pi := by
  intro w hw
  have hw0 : aug w = 0 := (mem_I_H_iff w).mp hw
  rw [eq_sum_coeff_smul_sub_one w hw0]
  refine Submodule.sum_mem _ (fun g _ => ?_)
  exact Submodule.smul_mem _ _ (by
    rw [← pi_deltaVec g]
    exact LinearMap.mem_range_self pi (deltaVec g))

/-- **满射性**：`π` 的像恰是增广理想（论文 `prop:procesi-H`）。 -/
theorem range_pi_eq : LinearMap.range pi = I_H :=
  le_antisymm range_pi_le range_pi_ge

/-! ## 4. 公理闸门 -/

#print axioms eq_sum_coeff_smul_single
#print axioms aug_eq_sum_coeff
#print axioms eq_sum_coeff_smul_sub_one
#print axioms range_pi_eq

end ABGV52
