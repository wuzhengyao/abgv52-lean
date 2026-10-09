/-
  ABGV-5.2 —— **prop:faithful-MH 新证明（障碍论证）的形式化**（2026-10-08 用户令）

  论文第三十三改（2026-10-08，同日自查修正）将 prop:faithful-MH 第一证明实质
  重写为**障碍论证**。设 h ∈ H 在 M|_H = ker(π|_H) 上平凡。取 g ∉ {1, h, h⁻¹}；
  ℤ[H]^{⊕9} ≅ ℤ[H] ⊗ ℤ[H] 的两种提升 x₁ = g⊗δ₁ 与 x₂ = −(1⊗δ_g) 同映到 g−1；
  以 z := x₁ − x₂ = g⊗δ₁ + 1⊗δ_g 作输入：
    π|_H z = 0 且（htriv）h·z = z；
  在坐标 b' = hg 处求值：左端 = 0 + h（(h·x₂) 的 hg-坐标 = h⊗δ_{hg}），
  右端 = 0 + 0 —— 得 h = 0 矛盾（对角作用 h·(1⊗δ_g) = h⊗δ_{hg} 首因子为 h）。

  本件在**坐标模型** G → ℤ[G] 上形式化（⊗-坐标 ↔ 坐标函数：δ_b-系数即 b'-坐标，
  即 prop:tensor-reg-ZH 的右端描述）：
    * `aug`：增广同态 ℤ[G] →+ ℤ；
    * `piH`：π|_H(x) = Σ_b (x_b − ε(x_b)·b)（`AddMonoidHom`）；
    * `P`：单项式-δ 坐标元（`P c b` = 坐标 b 取 single c 1、余 0）；
    * 作用 `actMH`：坐标作用 (h·x)_{b'} = h · x_{h⁻¹ b'}（左乘 × 坐标置换）；
    * **主定理 `faithfulMH_obstruction`**：给定 g 的三条件与 h 在 ker(π|_H) 上
      平凡的假设，则 h = 1。
  抽象化：任意群 G（论文取 H = C₃×C₃）。

  **无 sorry、无自造公理**。
-/
import ABGV52.D3_ABGV52

namespace ABGV52
namespace FaithfulMH

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. 增广同态与 π|_H -/

/-- **增广同态** ε：系数和（`Σ_b z_b ↦ Σ_b z_b`）。 -/
noncomputable def aug : MonoidAlgebra ℤ G →+ ℤ where
  toFun z := ∑ b : G, z.coeff b
  map_zero' := by
    simp only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      Finset.sum_const_zero]
  map_add' x y := by
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finset.sum_add_distrib]

@[simp] lemma aug_zero : aug (0 : MonoidAlgebra ℤ G) = 0 := map_zero aug

@[simp] lemma aug_single (c : G) :
    aug (MonoidAlgebra.single c (1 : ℤ)) = 1 := by
  change (∑ b : G,
    (MonoidAlgebra.single c (1 : ℤ) : MonoidAlgebra ℤ G).coeff b) = 1
  rw [Finset.sum_eq_single c]
  · rw [MonoidAlgebra.coeff_single_apply, if_pos rfl]
  · intro b' _ hb'
    rw [MonoidAlgebra.coeff_single_apply, if_neg (fun hc => hb' hc.symm)]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- **π|_H**：`π|_H(x) = Σ_b (x_b − ε(x_b)·b)`（坐标函数 → ℤ[G]）。 -/
noncomputable def piH : (G → MonoidAlgebra ℤ G) →+ MonoidAlgebra ℤ G where
  toFun x := ∑ b : G, (x b - (aug (x b)) • MonoidAlgebra.single b (1 : ℤ))
  map_zero' := by
    simp only [Pi.zero_apply, aug_zero, zero_zsmul, sub_zero,
      Finset.sum_const_zero]
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.add_apply, map_add, add_zsmul]
    abel

/-- **单项式-δ 坐标元**：坐标 `b` 取 `single c 1`，其余为 0。 -/
noncomputable def P (c b : G) : G → MonoidAlgebra ℤ G :=
  fun b' => if b' = b then MonoidAlgebra.single c (1 : ℤ) else 0

@[simp] lemma P_apply_self (c b : G) :
    P c b b = MonoidAlgebra.single c (1 : ℤ) := by
  simp [P]

lemma P_apply_of_ne (c b b' : G) (h : b' ≠ b) : P c b b' = 0 := by
  simp [P, h]

/-- **π|_H 在单项式-δ 元上的取值**：`π(P c b) = c − b`。 -/
lemma piH_P (c b : G) :
    piH (P c b) = MonoidAlgebra.single c (1 : ℤ) - MonoidAlgebra.single b (1 : ℤ) := by
  change (∑ b' : G, (P c b b' - (aug (P c b b')) •
    MonoidAlgebra.single b' (1 : ℤ))) = _
  rw [Finset.sum_eq_single b]
  · rw [P_apply_self, aug_single, one_zsmul]
  · intro b' _ hb'
    rw [P_apply_of_ne c b b' hb', aug_zero, zero_zsmul, sub_zero]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-! ## 2. 坐标作用 -/

/-- **坐标作用**：`(h·x)_{b'} = h · x_{h⁻¹b'}`（左乘 × 坐标置换）。 -/
noncomputable instance actMH : DistribMulAction G (G → MonoidAlgebra ℤ G) where
  smul h x := fun b' => MonoidAlgebra.single h (1 : ℤ) * x (h⁻¹ * b')
  one_smul x := by
    funext b'
    show MonoidAlgebra.single (1 : G) (1 : ℤ) * x ((1 : G)⁻¹ * b') = x b'
    rw [inv_one, one_mul]
    show (1 : MonoidAlgebra ℤ G) * x b' = x b'
    rw [one_mul]
  mul_smul a b x := by
    funext b'
    show MonoidAlgebra.single (a * b) (1 : ℤ) * x ((a * b)⁻¹ * b')
      = MonoidAlgebra.single a (1 : ℤ)
          * (MonoidAlgebra.single b (1 : ℤ) * x (b⁻¹ * (a⁻¹ * b')))
    have hidx : (a * b)⁻¹ * b' = b⁻¹ * (a⁻¹ * b') := by
      rw [mul_inv_rev, mul_assoc]
    rw [hidx]
    rw [← mul_assoc (MonoidAlgebra.single a (1 : ℤ))
      (MonoidAlgebra.single b (1 : ℤ)) (x (b⁻¹ * (a⁻¹ * b')))]
    have hsingle : MonoidAlgebra.single a (1 : ℤ) * MonoidAlgebra.single b (1 : ℤ)
        = MonoidAlgebra.single (a * b) (1 : ℤ) := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hsingle]
  smul_zero h := by funext b'; exact mul_zero _
  smul_add h x y := by funext b'; exact mul_add _ _ _

/-- **作用在单项式-δ 元上**：`h·P c b = P (h·c) (h·b)`。 -/
lemma act_P (h c b : G) : h • P c b = P (h * c) (h * b) := by
  funext b'
  show MonoidAlgebra.single h (1 : ℤ)
      * (if h⁻¹ * b' = b then MonoidAlgebra.single c (1 : ℤ) else 0)
    = if b' = h * b then MonoidAlgebra.single (h * c) (1 : ℤ) else 0
  by_cases hb : b' = h * b
  · subst hb
    have hin : h⁻¹ * (h * b) = b := by group
    rw [if_pos hin, if_pos rfl, MonoidAlgebra.single_mul_single, mul_one]
  · rw [if_neg (by intro hc; exact hb (by rw [← hc]; group)),
      mul_zero, if_neg hb]

/-! ## 3. 主定理（障碍论证） -/

/-- **prop:faithful-MH（障碍论证）**：设 `h` 在 `M|_H = ker(π|_H)` 上平凡，
    且 `g ≠ 1`、`g ≠ h`、`g ≠ h⁻¹`。则 `h = 1`。 -/
theorem faithfulMH_obstruction (h g : G) (hg1 : g ≠ 1) (hgh : g ≠ h)
    (hgh' : g ≠ h⁻¹)
    (htriv : ∀ m : G → MonoidAlgebra ℤ G, piH m = 0 → h • m = m) :
    h = 1 := by
  by_cases h1 : h = 1
  · exact h1
  · exfalso
    -- z := P g 1 + P 1 g = x₁ − x₂（两个提升之差）
    have hz : piH (P g 1 + P 1 g) = 0 := by
      rw [map_add, piH_P, piH_P]
      abel
    have hfix := htriv (P g 1 + P 1 g) hz
    rw [smul_add, act_P, act_P, mul_one] at hfix
    -- 在坐标 b' = h * g 处求值
    have hcoord := congr_fun hfix (h * g)
    rw [Pi.add_apply, Pi.add_apply] at hcoord
    have e1 : P (h * g) h (h * g) = 0 := by
      rw [P_apply_of_ne _ _ _
        (by intro hc
            exact hg1 (mul_left_cancel
              (show h * g = h * 1 from by rw [mul_one]; exact hc)))]
    have e2 : P h (h * g) (h * g) = MonoidAlgebra.single h (1 : ℤ) := by
      rw [P_apply_self]
    have f1 : P g 1 (h * g) = 0 := by
      rw [P_apply_of_ne _ _ _ (by intro hc; exact hgh' (by
        have := congrArg (fun t => h⁻¹ * t) hc
        simpa [mul_assoc] using this))]
    have f2 : P 1 g (h * g) = 0 := by
      rw [P_apply_of_ne _ _ _
        (by intro hc
            exact h1 (mul_right_cancel
              (show h * g = 1 * g from by rw [one_mul]; exact hc)))]
    rw [e1, e2, f1, f2] at hcoord
    -- hcoord : 0 + single h 1 = 0 + 0
    have hzero : MonoidAlgebra.single h (1 : ℤ) = 0 := by
      simpa using hcoord
    exact one_ne_zero (MonoidAlgebra.single_eq_zero.mp hzero)

/-! ## 4. 公理闸门 -/

#print axioms aug
#print axioms piH
#print axioms P
#print axioms piH_P
#print axioms act_P
#print axioms faithfulMH_obstruction

end FaithfulMH
end ABGV52
