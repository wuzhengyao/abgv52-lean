/-
  ABGV-5.2 —— G4：增广理想 `I[H]` 作为 `Rep ℤ H` 的具体构造

  背景（原缺口 G4）
  ================
  先前用 `Rep.leftRegular ℤ H` 时，其**载体不按 `H →₀ ℤ` 定义展开**（实测 `rfl` 失败），
  故 `I[H] = ker ε` 无法落地。本文件绕开该障碍：改用**自建正则模**
      `regZ := Rep.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)`
  —— 载体就是 `MonoidAlgebra ℤ H` 本身（与 `aug` 的定义域一致），于是：

      I[H] := ker ε   （`Submodule ℤ (MonoidAlgebra ℤ H)`）
      稳定性：`ε(lmul h w) = ε(w)`（G2b 的 `aug_lmul`）⟹ `I[H]` 是 H-不变子模
      诱导作用 ⟹ `I_H_rep : Rep ℤ H`

  与论文的对应：论文 `prop:procesi-H` 的 `I[H] = ker(ε : Z[H] → Z)`，且
  Procesi 序列 `0 → M|_H → Z[H]^{⊕9} → I[H] → 0` 中的第三项即 `I_H_rep`。
-/
import ABGV52.G2b_ABGV52

namespace ABGV52

/-! ## 1. 自建正则模（载体 = 群环本身） -/

/-- 论文的 `Z[H]` 作为 `Z[H]`-模（左乘）。载体即 `MonoidAlgebra ℤ H`。 -/
noncomputable def regZ : Rep ℤ H :=
  Rep.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)

/-! ## 2. `I[H] = ker ε` 的稳定性 -/

/-- **`I[H]` 在左乘下稳定**：`w ∈ ker ε ⟹ h·w ∈ ker ε`（用 `aug_lmul`）。 -/
theorem I_H_stable (h : H) {w : MonoidAlgebra ℤ H} (hw : w ∈ I_H) :
    lmul h w ∈ I_H := by
  rw [I_H, LinearMap.mem_ker] at hw ⊢
  rw [aug_lmul, hw]

/-! ## 3. `I[H]` 上的诱导作用与 `Rep` 结构 -/

/-- 诱导作用（用稳定性把结果留在子模内）。 -/
noncomputable def I_H_act (h : H) (w : ↥I_H) : ↥I_H :=
  ⟨lmul h w.1, I_H_stable h w.2⟩

noncomputable instance : DistribMulAction H ↥I_H where
  smul h w := I_H_act h w
  one_smul w := by
    apply Subtype.ext
    show lmul 1 w.1 = w.1
    exact one_mul w.1
  mul_smul a b w := by
    apply Subtype.ext
    show lmul (a * b) w.1 = lmul a (lmul b w.1)
    exact (lmul_mul a b w.1).symm
  smul_zero h := by
    apply Subtype.ext
    show lmul h (0 : MonoidAlgebra ℤ H) = 0
    exact lmul_zero h
  smul_add h x y := by
    apply Subtype.ext
    show lmul h (x.1 + y.1) = lmul h x.1 + lmul h y.1
    simp only [lmul, mul_add]

/-- **`I[H]` 作为 `Rep ℤ H`**（论文增广理想的 Lean 对象）。 -/
noncomputable def I_H_rep : Rep ℤ H :=
  Rep.ofDistribMulAction ℤ H ↥I_H

/-! ## 4. 一致性核对（`I[H]` 确为 `ε` 的核，且含 `h − 1` 型元素） -/

/-- `I[H]` 的元素恰是增广为零者（定义核对）。 -/
theorem mem_I_H_iff (w : MonoidAlgebra ℤ H) : w ∈ I_H ↔ aug w = 0 :=
  LinearMap.mem_ker

/-- 论文的生成元 `h − 1` 落在 `I[H]` 里。 -/
theorem single_sub_one_mem (h : H) :
    (MonoidAlgebra.single h (1 : ℤ) - 1 : MonoidAlgebra ℤ H) ∈ I_H := by
  rw [mem_I_H_iff, map_sub, aug_single, aug_one, sub_self]

/-! ## 5. 公理闸门 -/

#print axioms I_H_stable
#print axioms I_H_rep
#print axioms single_sub_one_mem

end ABGV52
