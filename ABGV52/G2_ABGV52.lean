/-
  ABGV-5.2 —— G2：Procesi 映射 `π|_H` 与其核 `M|_H` 的具体构造

  目标（论文 `prop:procesi-H` 的 Lean 对应物）
  ==========================================
    H = C_3 × C_3，R = Z[H] = MonoidAlgebra ℤ H；
    环绕模 V := Z[H]^9 —— 用**坐标模型** `H → R`（第 b 个坐标是 H 的元素 b 对应的槽），
      作用：(h • z) i = h · z (h⁻¹ * i)   （论文的置换作用）
    增广 ε : R → Z（系数和）；
    映射 π : V → R，  π z = Σ_{b ∈ H} ( z b − ε(z b) · b ) ∈ I[H]；
    核 M|_H := ker π（论文的 Procesi 限制；论文记 rk_Z = 73）。

  本文件先落地：作用、ε、π（并核对 π 的像落在 I[H] 里）。**等变性的证明**另文件。
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
-- ⚠ `H`／`C3` 的定义**改由 B 档定义层提供**（2026-09-30 接线）：
-- 原先 B 档（`Hyp_ABGV52.lean`）与 C 档（本文件）各写一份同名 `abbrev`，
-- 两套开发因此**无法在同一 Lean 文件中汇合**（`environment already contains 'ABGV52.H'`），
-- 而 `C8b` 的接线正需要两者同时在场。二者内容逐字相同（`Multiplicative (ZMod 3) × …`），
-- 故保留 B 档那一份、C 档改为导入——依赖方向 = C 档用 B 档的定义。
import ABGV52.Hyp_ABGV52

namespace ABGV52

/-! ## 1. `H` 在 `R = Z[H]` 上的左乘（论文的坐标作用所需） -/

/-- 左乘辅助定义。 -/
noncomputable def lmul (h : H) (z : MonoidAlgebra ℤ H) : MonoidAlgebra ℤ H :=
  MonoidAlgebra.single h 1 * z

lemma lmul_mul (a b : H) (w : MonoidAlgebra ℤ H) :
    lmul a (lmul b w) = lmul (a * b) w := by
  show MonoidAlgebra.single a 1 * (MonoidAlgebra.single b 1 * w)
      = MonoidAlgebra.single (a * b) 1 * w
  rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

noncomputable instance : DistribMulAction H (MonoidAlgebra ℤ H) where
  smul := lmul
  one_smul z := one_mul z
  mul_smul a b z := (lmul_mul a b z).symm
  smul_zero h := mul_zero _
  smul_add h z w := mul_add _ _ _

/-! ## 2. 环绕模 `V = Z[H]^9`（坐标模型 `H → R`） -/

/-- 环绕模（论文的 `Z[H]^{⊕9}`；坐标模型：`H → R`，第 `i` 个坐标是槽 `i`）。 -/
abbrev V : Type := H → MonoidAlgebra ℤ H

/-- **坐标作用**（论文的置换作用）：`(act h z) i = h · z (h⁻¹ * i)`。

**不**声明为类型类实例：`V = H → R` 上同时存在 Pi 的逐点作用，二者会争用 `•` 的
实例解析（实测 `rfl` 失败即其征兆）。故此处作**显式函数**，全文只用 `act`。 -/
noncomputable def act (h : H) (z : V) : V := fun i => lmul h (z (h⁻¹ * i))

@[simp] lemma act_apply (h : H) (z : V) (i : H) : act h z i = lmul h (z (h⁻¹ * i)) := rfl

lemma act_one (z : V) : act 1 z = z := by
  funext i; rw [act_apply, inv_one, one_mul]; exact one_mul (z i)

lemma act_mul (a b : H) (z : V) : act (a * b) z = act a (act b z) := by
  funext i
  rw [act_apply, act_apply, act_apply, lmul_mul, mul_inv_rev, mul_assoc]

lemma act_add (h : H) (z w : V) : act h (z + w) = act h z + act h w := by
  funext i; simp only [act_apply, Pi.add_apply, lmul, mul_add]

lemma act_zero (h : H) : act h (0 : V) = 0 := by
  funext i; rw [act_apply, Pi.zero_apply, Pi.zero_apply, lmul, mul_zero]

/-! ## 3. 增广 `ε` 与增广理想 `I[H]` -/

/-- 增广映射 `ε : R → Z`（系数和）。用 `MonoidAlgebra.liftNC` 造加法同态，再转
`Z`-线性映射（`MonoidAlgebra` 的载体不是字面 `Finsupp`，故不用 `Finsupp.linearCombination`）。 -/
noncomputable def aug : MonoidAlgebra ℤ H →ₗ[ℤ] ℤ :=
  (MonoidAlgebra.liftNC (AddMonoidHom.id ℤ) ((1 : H →* ℤ) : H → ℤ)).toIntLinearMap

/-- 增广理想 `I[H] = ker ε`。 -/
noncomputable def I_H : Submodule ℤ (MonoidAlgebra ℤ H) := LinearMap.ker aug

lemma aug_single (h : H) : aug (MonoidAlgebra.single h (1 : ℤ)) = 1 := by
  simp [aug]

/-! ## 4. Procesi 映射 `π` -/

/-- 取第 `b` 个坐标（`V = H → R` 的求值）。 -/
noncomputable def evalB (b : H) : V →ₗ[ℤ] MonoidAlgebra ℤ H where
  toFun z := z b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 单个坐标的贡献 `z ↦ z b − ε(z b) · b`；用 `LinearMap` 组合子构造，线性性自动。 -/
noncomputable def piTerm (b : H) : V →ₗ[ℤ] MonoidAlgebra ℤ H :=
  evalB b - (LinearMap.toSpanSingleton ℤ (MonoidAlgebra ℤ H)
    (MonoidAlgebra.single b (1 : ℤ))).comp (aug.comp (evalB b))

@[simp] lemma evalB_apply (b : H) (z : V) : evalB b z = z b := rfl

/-- `πTerm` 的求值形式（**不展开 `LinearMap` 结构**，供后续重写使用）。 -/
lemma piTerm_apply (b : H) (z : V) :
    piTerm b z = z b - aug (z b) • MonoidAlgebra.single b (1 : ℤ) := by
  simp only [piTerm, LinearMap.sub_apply, evalB_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]

/-- **Procesi 映射** `π : Z[H]^9 → Z[H]`，`π z = Σ_b (z b − ε(z b)·b)`。 -/
noncomputable def pi : V →ₗ[ℤ] MonoidAlgebra ℤ H :=
  ∑ b : H, piTerm b

/-\! ## 公理闸门（定义层亦须过闸） -/

#print axioms act
#print axioms aug
#print axioms pi

end ABGV52
