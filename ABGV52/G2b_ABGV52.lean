/-
  ABGV-5.2 —— G2 主体：`π` 的 H-等变性（论文 `prop:procesi-H` 的 Lean 核心）

  数学路线（把等变性化为**逐坐标**的局部计算）
  ==========================================
    记 (h • z) i = lmul h (z (h⁻¹ i))（坐标作用），π z = Σ_b (z b − ε(z b)·b)。
    左边按 b ↦ h·c 重索引（`Equiv.mulLeft`），于是只需逐 c 证明
        πTerm (h·c) (h • z) = lmul h (πTerm c z)，
    而这是恒等式：
        (h•z)(h·c) = lmul h (z c)； h·(h⁻¹·(h·c)) = c；
        ε(lmul h w) = ε w；        lmul h (single c 1) = single (h·c) 1。
  所需引理（mathlib 名已核）：`liftNC_mul`／`liftNC_one`、`smul_mul_assoc`、
  `mul_smul_comm`、`inv_mul_cancel_left`、`Equiv.sum_comp`、`Finset.mul_sum`、
  `LinearMap.sum_apply`。
-/
import ABGV52.G2_ABGV52

namespace ABGV52

/-- `lmul h` 记法：`lmul h w = single h 1 * w`（G2 已定义）。 -/
noncomputable abbrev lmulR (h : H) (w : MonoidAlgebra ℤ H) : MonoidAlgebra ℤ H := lmul h w

/-! ## 1. 增广的乘性与单位，及对左乘的不变性 -/

/-- 增广是幺环同态：`ε(x·y) = ε(x)·ε(y)`。 -/
lemma aug_mul (x y : MonoidAlgebra ℤ H) : aug (x * y) = aug x * aug y := by
  have h := MonoidAlgebra.liftNC_mul (k := ℤ) (G := H) (R := ℤ)
    (f := RingHom.id ℤ) (g := (1 : H →* ℤ)) x y
    (by intro a b _; exact Commute.all _ _)
  simpa [aug] using h

/-- `ε(1) = 1`。 -/
lemma aug_one : aug (1 : MonoidAlgebra ℤ H) = 1 := by
  have h := MonoidAlgebra.liftNC_one (k := ℤ) (G := H) (R := ℤ)
    (f := RingHom.id ℤ) (g := (1 : H →* ℤ))
  simpa [aug] using h

/-- 左乘不改变增广：`ε(h·w) = ε(w)`。 -/
lemma aug_lmul (h : H) (w : MonoidAlgebra ℤ H) : aug (lmul h w) = aug w := by
  rw [lmul, aug_mul, aug_single, one_mul]

/-! ## 2. `lmul` 与 `single`、标量、和差的关系 -/

/-- `lmul h (single c 1) = single (h·c) 1`。 -/
lemma lmul_single (h c : H) :
    lmul h (MonoidAlgebra.single c (1 : ℤ)) = MonoidAlgebra.single (h * c) (1 : ℤ) := by
  rw [lmul, MonoidAlgebra.single_mul_single, one_mul]

/-- `lmul h` 与 `Z`-标量交换。 -/
lemma lmul_smul (h : H) (m : ℤ) (w : MonoidAlgebra ℤ H) :
    lmul h (m • w) = m • lmul h w := by
  rw [lmul, lmul, mul_smul_comm]

/-- `lmul h` 保减法。 -/
lemma lmul_sub (h : H) (x y : MonoidAlgebra ℤ H) :
    lmul h (x - y) = lmul h x - lmul h y := by
  rw [lmul, lmul, lmul, mul_sub]

/-- `lmul h` 保有限和。 -/
lemma lmul_sum (h : H) (s : Finset H) (f : H → MonoidAlgebra ℤ H) :
    lmul h (∑ b ∈ s, f b) = ∑ b ∈ s, lmul h (f b) := by
  simp only [lmul, Finset.mul_sum]

/-! ## 3. 坐标作用的求值公式 -/

lemma act_apply_mul (h c : H) (z : V) : act h z (h * c) = lmul h (z c) := by
  rw [act_apply, inv_mul_cancel_left]

/-! ## 4. 逐坐标核心与主定理 -/

/-- **逐坐标核心**：`πTerm (h·c) (h • z) = lmul h (πTerm c z)`。 -/
lemma piTerm_act (h c : H) (z : V) :
    piTerm (h * c) (act h z) = lmul h (piTerm c z) := by
  rw [piTerm_apply, piTerm_apply, act_apply_mul, aug_lmul, lmul_sub, lmul_smul, lmul_single]

/-- **G2 主定理**：`π` 是 `H`-等变的，`π (h • z) = h · π z`。 -/
theorem pi_equivariant (h : H) (z : V) : pi (act h z) = lmul h (pi z) := by
  have hL : pi (act h z) = ∑ b : H, piTerm b (act h z) := by
    simp only [pi, LinearMap.sum_apply, Finset.sum_apply]
  have hR : lmul h (pi z) = ∑ c : H, lmul h (piTerm c z) := by
    have hz : pi z = ∑ c : H, piTerm c z := by
      simp only [pi, LinearMap.sum_apply, Finset.sum_apply]
    rw [hz]
    simp only [lmul, Finset.mul_sum]
  rw [hL, hR, ← Equiv.sum_comp (Equiv.mulLeft h) (fun b : H => piTerm b (act h z))]
  exact Finset.sum_congr rfl (fun c _ => piTerm_act h c z)

/-\! ## 5. 由等变性得 `M|_H = ker π` 的 H-稳定性 -/

/-- 左乘保持零元（`lmul h 0 = 0`）。 -/
lemma lmul_zero (h : H) : lmul h (0 : MonoidAlgebra ℤ H) = 0 := mul_zero _

/-- **核稳定**：`ker π` 在坐标作用下不变 —— 这是 `M|_H` 成为 `Z[H]`-模（论文的
Procesi 限制）的根据。 -/
theorem ker_pi_stable (h : H) {z : V} (hz : z ∈ LinearMap.ker pi) :
    act h z ∈ LinearMap.ker pi := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [pi_equivariant, hz, lmul_zero]

/-\! ## 6. 公理闸门（无 sorry、无自造公理） -/

#print axioms pi_equivariant
#print axioms ker_pi_stable

end ABGV52
