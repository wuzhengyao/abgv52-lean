/-
  ABGV-5.2 —— C 档第一刀 · 步 1：`π` 的像等于增广理想 `I[H]`

  这是论文 `prop:procesi-H` 中「π|_H 满射到 I[H]」的 Lean 版，也是后面算
  `rk_Z M|_H = 73`（用秩-零化度）的前提。

  两个方向
  ========
  ① `range π ⊆ I[H]`：每个坐标贡献 `πTerm b z = z b − ε(z b)·b` 的增广为 0
     （`aug (z b) − aug(z b)·aug b = aug(z b) − aug(z b) = 0`）；
  ② `I[H] ⊆ range π`：论文的论证 —— `h − 1` 有原像（取只在槽 `1` 放 `single h 1`
     的向量），而 `I[H]` 由所有 `h − 1` 生成。
-/
import ABGV52.G4_ABGV52

namespace ABGV52

/-! ## 1. 坐标贡献的增广为 0 -/

lemma aug_smul' (m : ℤ) (w : MonoidAlgebra ℤ H) : aug (m • w) = m * aug w :=
  map_smul aug m w

lemma aug_piTerm (b : H) (z : V) : aug (piTerm b z) = 0 := by
  rw [piTerm_apply, map_sub, aug_smul', aug_single]
  ring

/-! ## 2. 方向 ①：`range π ⊆ I[H]` -/

theorem range_pi_le : LinearMap.range pi ≤ I_H := by
  intro w hw
  obtain ⟨z, rfl⟩ := hw
  rw [I_H, LinearMap.mem_ker, pi, LinearMap.sum_apply, map_sum]
  exact Finset.sum_eq_zero (fun b _ => aug_piTerm b z)

/-! ## 3. 方向 ② 的第一步：`h − 1` 有原像 -/

/-- 只在槽 `1` 放 `single h 1` 的向量。 -/
noncomputable def deltaVec (h : H) : V := fun b => if b = 1 then MonoidAlgebra.single h 1 else 0

lemma pi_deltaVec (h : H) : pi (deltaVec h) = MonoidAlgebra.single h 1 - 1 := by
  rw [pi, LinearMap.sum_apply, Finset.sum_eq_single (1 : H)]
  · rw [piTerm_apply, deltaVec, if_pos rfl, aug_single, one_smul]
    rfl
  · intro b _ hb
    rw [piTerm_apply, deltaVec, if_neg hb, map_zero, zero_smul, sub_zero]
  · intro hnot
    exact absurd (Finset.mem_univ (1 : H)) hnot

/-\! ## 4. 公理闸门 -/

#print axioms aug_piTerm
#print axioms range_pi_le
#print axioms pi_deltaVec

end ABGV52
