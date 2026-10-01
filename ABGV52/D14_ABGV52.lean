/-
  ABGV-5.2 —— C 档 · 块 1：**子块 1γ 的陈述为假**（机器验证的反例）

  wiki §2c 的 1γ 计划项：

    > `F(M ⊕ M')^G = F(M)^G · F(M')^G`（当作用忠实）

  **本件给出反例**（`F` 任意域，`G = C₂ × C₂`，格 `L2 = ℤ²` 带逐坐标符号作用）：

    * `w := x₀x₁ + (x₀x₁)⁻¹` —— 被**对角元** `σ_d = (−1,−1)` 固定；
    * 但 `w` 不被 `σ₀ := （只翻第一个坐标）` 固定，故 `w ∉ F(L2)^G`；
    * 而 `x₀+x₀⁻¹`、`x₁+x₁⁻¹` 被**全部 `g ∈ G` 固定**，故它们生成的子域
      `F(x₀+x₀⁻¹, x₁+x₁⁻¹)`（= 1γ 右端）⊆ `F(L2)^G`；
    * 于是 `w ∈ F(L2)^{⟨σ_d⟩}` 而 `w ∉ F(x₀+x₀⁻¹, x₁+x₁⁻¹)` ⟹ **1γ 假**。

  **几何含义**：对角型不变量（如 `x₀x₁ + (x₀x₁)⁻¹`）同时牵动两个坐标，**无法**由单坐标不变域生成。
  ⟹ 1γ 不能充当 `M ⊕ P ≅ Q`（稳定置换）的装配步；更正后的路线见 wiki §3p。

  **本件是负结果**（不给 (⇐) 链提供正向零件）。
-/
import ABGV52.D2_ABGV52
import Mathlib.Algebra.Group.TypeTags.Basic

open scoped Classical

namespace ABGV52

namespace EM

namespace GammaFails

noncomputable section

variable (F : Type*) [Field F]

/-- 反例的群：`C₂ × C₂`（坐标函数 `Fin 2 → Multiplicative (ZMod 2)`）。 -/
abbrev G2 : Type := Fin 2 → Multiplicative (ZMod 2)

/-- 反例的格：`ℤ²`。 -/
abbrev L2 : Type := Fin 2 → ℤ

/-- 符号特征 `C₂ → ℤˣ`（`1 ↦ 1`，非单位元 `↦ −1`）。 -/
def sgnHom : Multiplicative (ZMod 2) →* ℤˣ where
  toFun g := if g = 1 then 1 else -1
  map_one' := by simp
  map_mul' g h := by revert g h; decide

/-- `G2` 在 `L2` 上的**逐坐标符号作用**。 -/
instance instSMulL2 : SMul G2 L2 where
  smul g v := fun i => ((sgnHom (g i) : ℤˣ) : ℤ) * v i

@[simp] lemma smul_apply (g : G2) (v : L2) (j : Fin 2) :
    (g • v) j = ((sgnHom (g j) : ℤˣ) : ℤ) * v j := rfl

instance instDistribMulActionL2 : DistribMulAction G2 L2 where
  one_smul v := by ext i; simp
  mul_smul g h v := by
    ext i
    rw [smul_apply, smul_apply, smul_apply, Pi.mul_apply, map_mul, Units.val_mul]
    ring
  smul_zero g := by ext i; simp
  smul_add g v w := by
    ext i
    simp only [smul_apply, Pi.add_apply]
    ring

instance instSMulCommClassL2 : SMulCommClass G2 ℤ L2 where
  smul_comm g c v := by
    ext i
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- 坐标单项式 `x_i`（单项式环中）。 -/
noncomputable def xMono (i : Fin 2) : latticeAlgebra F L2 :=
  MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) 1

/-- 坐标变量 `x_i`（函数域 `F(L2)` 中）。 -/
noncomputable def x (i : Fin 2) : latticeFunctionField F L2 :=
  algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2) (xMono F i)

/-- 对角元 `σ_d = (−1,−1)`。 -/
def sDiag : G2 := fun _ => Multiplicative.ofAdd (1 : ZMod 2)

/-- 只翻第一个坐标的 `σ₀`。 -/
def sFst : G2 := fun i => if i = 0 then Multiplicative.ofAdd (1 : ZMod 2) else 1

/-- **反例元素** `w := x₀x₁ + (x₀x₁)⁻¹`。 -/
noncomputable def wElem : latticeFunctionField F L2 :=
  x F 0 * x F 1 + (x F 0 * x F 1)⁻¹

/-! ### 甲：符号取值与坐标作用 -/

lemma sgnHom_one : sgnHom (1 : Multiplicative (ZMod 2)) = 1 := by
  show (if (1 : Multiplicative (ZMod 2)) = 1 then (1 : ℤˣ) else -1) = 1
  rw [if_pos rfl]

lemma sgnHom_gen : sgnHom (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
  show (if (Multiplicative.ofAdd (1 : ZMod 2)) = 1 then (1 : ℤˣ) else -1) = -1
  rw [if_neg (by decide)]

lemma sgnHom_eq_free (g : Multiplicative (ZMod 2)) : sgnHom g = 1 ∨ sgnHom g = -1 := by
  by_cases h : g = 1
  · exact Or.inl (by rw [show sgnHom g = (if g = 1 then (1 : ℤˣ) else -1) from rfl, if_pos h])
  · exact Or.inr (by rw [show sgnHom g = (if g = 1 then (1 : ℤˣ) else -1) from rfl, if_neg h])

lemma sgnHom_eq_one_iff (g : Multiplicative (ZMod 2)) : sgnHom g = 1 ↔ g = 1 := by
  constructor
  · intro h
    by_contra hg
    rw [show sgnHom g = (if g = 1 then (1 : ℤˣ) else -1) from rfl, if_neg hg] at h
    exact absurd h (by decide)
  · intro h; rw [h]; exact sgnHom_one

lemma sFst_apply_zero : sFst 0 = Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [sFst, if_pos rfl]

lemma sFst_apply_one : sFst 1 = 1 := by
  rw [sFst, if_neg (by decide)]

lemma sDiag_apply (i : Fin 2) : sDiag i = Multiplicative.ofAdd (1 : ZMod 2) := rfl

/-- **不翻转时的坐标作用**：`g • e_i = e_i`（当 `g i = 1`）。 -/
lemma smul_piSingle_one (g : G2) (i : Fin 2) (h : g i = 1) :
    g • (Pi.single i (1 : ℤ) : L2) = Pi.single i (1 : ℤ) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [Pi.single_eq_of_ne hj]

/-- **翻转时的坐标作用**：`g • e_i = −e_i`（当 `sgnHom (g i) = −1`）。 -/
lemma smul_piSingle_neg (g : G2) (i : Fin 2) (h : sgnHom (g i) = -1) :
    g • (Pi.single i (1 : ℤ) : L2) = -(Pi.single i (1 : ℤ)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [smul_apply, Pi.single_eq_same, mul_one, Pi.neg_apply]
    rw [h]
    norm_num
  · simp [Pi.single_eq_of_ne hj]

/-! ### 乙：单项式层与函数域层的取值 -/

lemma smul_xMono_one (g : G2) (i : Fin 2) (h : g i = 1) : g • xMono F i = xMono F i := by
  show MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G2 L2 g) (xMono F i) = xMono F i
  rw [xMono, MonoidAlgebra.mapDomainRingEquiv_single, mulEquivOfSMul_apply]
  change MonoidAlgebra.single (Multiplicative.ofAdd (g • (Pi.single i (1 : ℤ) : L2))) 1
    = MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single i (1 : ℤ) : L2)) 1
  rw [smul_piSingle_one g i h]

lemma smul_xMono_neg (g : G2) (i : Fin 2) (h : sgnHom (g i) = -1) :
    g • xMono F i
      = MonoidAlgebra.single (Multiplicative.ofAdd (-(Pi.single i (1 : ℤ)))) 1 := by
  show MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G2 L2 g) (xMono F i) = _
  rw [xMono, MonoidAlgebra.mapDomainRingEquiv_single, mulEquivOfSMul_apply]
  change MonoidAlgebra.single (Multiplicative.ofAdd (g • (Pi.single i (1 : ℤ) : L2))) 1
    = MonoidAlgebra.single (Multiplicative.ofAdd (-(Pi.single i (1 : ℤ) : L2))) 1
  rw [smul_piSingle_neg g i h]

lemma smul_algebraMap_general (g : G2) (a : latticeAlgebra F L2) :
    g • algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2) a
      = algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2) (g • a) := by
  change (IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingEquiv G2 (latticeAlgebra F L2) g))
    (algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2) a) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    MulSemiringAction.toRingEquiv_apply_apply]

/-- 作用与求逆相容。 -/
lemma smul_inv_general (g : G2) (a : latticeFunctionField F L2) :
    g • a⁻¹ = (g • a)⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have h : (g • a⁻¹) * (g • a) = 1 := by
      rw [← smul_mul', inv_mul_cancel₀ ha, smul_one]
    exact eq_inv_of_mul_eq_one_right ((mul_comm _ _).trans h)

lemma smul_x_one (g : G2) (i : Fin 2) (h : g i = 1) : g • x F i = x F i := by
  rw [x, smul_algebraMap_general, smul_xMono_one F g i h]

lemma xMono_inv (i : Fin 2) :
    (MonoidAlgebra.single (Multiplicative.ofAdd (-(Pi.single i (1 : ℤ)))) 1 : latticeAlgebra F L2)
        * xMono F i = 1 := by
  rw [xMono, MonoidAlgebra.single_mul_single, ← ofAdd_add, neg_add_cancel]
  rw [MonoidAlgebra.one_def]
  simp

lemma smul_x_neg (g : G2) (i : Fin 2) (h : sgnHom (g i) = -1) :
    g • x F i = (x F i)⁻¹ := by
  have hx : algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2) (xMono F i)
        * algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2)
          (MonoidAlgebra.single (Multiplicative.ofAdd (-(Pi.single i (1 : ℤ)))) 1) = 1 := by
    rw [← map_mul, mul_comm (xMono F i), xMono_inv F i, map_one]
  rw [x, smul_algebraMap_general, smul_xMono_neg F g i h]
  exact eq_inv_of_mul_eq_one_right hx

/-! ### 丙：对角元固定 `w`；`x_i + x_i⁻¹` 被全群固定 -/

/-- `x_i ≠ 0`。 -/
lemma x_ne_zero (i : Fin 2) : x F i ≠ 0 := by
  have hunit : IsUnit (xMono F i) := by
    rw [xMono, ← MonoidAlgebra.of_apply]
    exact (Group.isUnit (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))).map
      (MonoidAlgebra.of F (Multiplicative L2))
  rw [x]
  exact fun h => hunit.ne_zero
    (IsFractionRing.injective (latticeAlgebra F L2) (latticeFunctionField F L2) (by rw [h, map_zero]))

/-- `σ₀` 在 `x₀x₁` 上的取值：`(x₀x₁) ↦ x₀⁻¹x₁`。 -/
lemma sFst_smul_mul : sFst • (x F 0 * x F 1) = (x F 0)⁻¹ * x F 1 := by
  rw [smul_mul', smul_x_neg F sFst 0 (by rw [sFst_apply_zero, sgnHom_gen]),
    smul_x_one F sFst 1 (by rw [sFst_apply_one])]

/-- `σ₀` 在 `w` 上的显式取值。 -/
lemma sFst_smul_wElem :
    sFst • wElem F = (x F 0)⁻¹ * x F 1 + ((x F 0)⁻¹ * x F 1)⁻¹ := by
  rw [wElem, smul_add, sFst_smul_mul, smul_inv_general, sFst_smul_mul]

/-- **对角元固定 `w`**。 -/
theorem sDiag_smul_wElem : sDiag • wElem F = wElem F := by
  have h0 : sDiag • x F 0 = (x F 0)⁻¹ :=
    smul_x_neg F sDiag 0 (by rw [sDiag_apply, sgnHom_gen])
  have h1 : sDiag • x F 1 = (x F 1)⁻¹ :=
    smul_x_neg F sDiag 1 (by rw [sDiag_apply, sgnHom_gen])
  have hA : sDiag • (x F 0 * x F 1) = (x F 0 * x F 1)⁻¹ := by
    rw [smul_mul', h0, h1, mul_inv]
  rw [wElem, smul_add, smul_inv_general, hA, inv_inv, add_comm]

/-- **`x_i + x_i⁻¹` 被全群固定**（`g` 或固定 `x_i`、或把它翻成逆元）。 -/
lemma smul_x_add_inv (g : G2) (i : Fin 2) :
    g • (x F i + (x F i)⁻¹) = x F i + (x F i)⁻¹ := by
  rcases sgnHom_eq_free (g i) with h | h
  · have hg : g i = 1 := (sgnHom_eq_one_iff (g i)).mp h
    rw [smul_add, smul_x_one F g i hg, smul_inv_general, smul_x_one F g i hg]
  · rw [smul_add, smul_x_neg F g i h, smul_inv_general, smul_x_neg F g i h, inv_inv, add_comm]

/-\! ### 丁：关键不等式 `σ₀ • w ≠ w` 与 1γ 反例 -/

/-- **单项式的 `k` 次幂**。 -/
lemma xMono_pow (i : Fin 2) (k : ℕ) :
    (xMono F i) ^ k
      = MonoidAlgebra.single (Multiplicative.ofAdd (k • (Pi.single i (1 : ℤ) : L2))) 1 := by
  induction k with
  | zero => rw [pow_zero, zero_smul, MonoidAlgebra.one_def]; simp
  | succ k ih =>
      rw [pow_succ, ih, xMono, MonoidAlgebra.single_mul_single, one_mul, ← ofAdd_add,
        ← succ_nsmul]

lemma xMono_zero : xMono F 0
    = MonoidAlgebra.single (Multiplicative.ofAdd ((1 : ℕ) • (Pi.single 0 (1 : ℤ) : L2))) (1 : F) := by
  rw [xMono, one_smul]

lemma xMono_one : xMono F 1
    = MonoidAlgebra.single (Multiplicative.ofAdd ((1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) (1 : F) := by
  rw [xMono, one_smul]

/-- **两个坐标单项式的幂之积**。 -/
lemma xMono_pow_mul (a b : ℕ) :
    (xMono F 0) ^ a * (xMono F 1) ^ b
      = MonoidAlgebra.single (Multiplicative.ofAdd
          (a • (Pi.single 0 (1 : ℤ) : L2) + b • (Pi.single 1 (1 : ℤ) : L2))) 1 := by
  rw [xMono_pow, xMono_pow, MonoidAlgebra.single_mul_single, one_mul, ← ofAdd_add]

/-- **幂乘单次幂**（`b = 1` 的形态）。 -/
lemma xMono_pow_mul_one (a : ℕ) :
    (xMono F 0) ^ a * xMono F 1
      = MonoidAlgebra.single (Multiplicative.ofAdd
          (a • (Pi.single 0 (1 : ℤ) : L2) + (1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) 1 := by
  rw [xMono_pow, xMono, MonoidAlgebra.single_mul_single, one_mul, one_smul, ← ofAdd_add]

/-- 指数向量的相异判据（逐坐标比较）。 -/
lemma exp_ne {a b c d : ℕ}
    (h : a ≠ c ∨ b ≠ d) :
    (a • (Pi.single 0 (1 : ℤ) : L2) + b • (Pi.single 1 (1 : ℤ) : L2))
      ≠ (c • (Pi.single 0 (1 : ℤ) : L2) + d • (Pi.single 1 (1 : ℤ) : L2)) := by
  intro hh
  rcases h with h | h
  · refine h ?_
    have h0 := congrFun hh 0
    simpa [Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] using h0
  · refine h ?_
    have h1 := congrFun hh 1
    simpa [Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] using h1

/-- 指数向量相异（`ofAdd` 包裹版）。 -/
lemma ofAdd_exp_ne {a b c d : ℕ} (h : a ≠ c ∨ b ≠ d) :
    Multiplicative.ofAdd (a • (Pi.single 0 (1 : ℤ) : L2) + b • (Pi.single 1 (1 : ℤ) : L2))
      ≠ Multiplicative.ofAdd (c • (Pi.single 0 (1 : ℤ) : L2)
        + d • (Pi.single 1 (1 : ℤ) : L2)) :=
  fun hh => exp_ne h (Multiplicative.ofAdd.injective hh)

/-- 具体指数相异（避免元变量推断歧义）。 -/
lemma ofAdd_ne_a : Multiplicative.ofAdd ((1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))
    ≠ Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
      + (3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2)) := by
  intro h
  have h1 := congrFun (Multiplicative.ofAdd.injective h) 0
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Pi.single_eq_same, smul_eq_mul, mul_one, mul_zero, add_zero] at h1
  exact absurd h1 (by norm_num)

lemma ofAdd_ne_b : Multiplicative.ofAdd ((3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))
    ≠ Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
      + (3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2)) := by
  intro h
  have h1 := congrFun (Multiplicative.ofAdd.injective h) 0
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Pi.single_eq_same, smul_eq_mul, mul_one, mul_zero, add_zero] at h1
  exact absurd h1 (by norm_num)

lemma ofAdd_ne_c : Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
      + (1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))
    ≠ Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
      + (3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2)) := by
  intro h
  have h1 := congrFun (Multiplicative.ofAdd.injective h) 1
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_same, smul_eq_mul, mul_one, mul_zero, add_zero] at h1
  exact absurd h1 (by norm_num)

/-- **单项式环中的关键不等式（`single` 形式，系数提取）**。 -/
lemma key_single_ne :
    MonoidAlgebra.single (Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
        + (3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) (1 : F)
      + MonoidAlgebra.single (Multiplicative.ofAdd ((1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) 1
    ≠ MonoidAlgebra.single (Multiplicative.ofAdd ((3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) 1
      + MonoidAlgebra.single (Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
        + (1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) 1 := by
  intro h
  have hc := congrArg (fun t : latticeAlgebra F L2 => t.coeff
    (Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
      + (3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2)))) h
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add,
    MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne ofAdd_ne_a.symm,
    Finsupp.single_eq_of_ne ofAdd_ne_b.symm,
    Finsupp.single_eq_of_ne ofAdd_ne_c.symm,
    add_zero, zero_add] at hc
  exact one_ne_zero hc

set_option maxHeartbeats 4000000 in
theorem sFst_smul_wElem_ne : sFst • wElem F ≠ wElem F := by
  intro h
  have hx0 : x F 0 ≠ 0 := x_ne_zero F 0
  have hx1 : x F 1 ≠ 0 := x_ne_zero F 1
  -- 两侧乘 `x₀x₁²` 清分母
  have h' : ((x F 0)⁻¹ * x F 1 + ((x F 0)⁻¹ * x F 1)⁻¹) * (x F 0 * (x F 1) ^ 2)
      = (x F 0 * x F 1 + (x F 0 * x F 1)⁻¹) * (x F 0 * (x F 1) ^ 2) := by
    rw [← sFst_smul_wElem F, h, wElem]
  have hL : ((x F 0)⁻¹ * x F 1 + ((x F 0)⁻¹ * x F 1)⁻¹) * (x F 0 * (x F 1) ^ 2)
      = (x F 1) ^ 3 + (x F 0) ^ 2 * x F 1 := by
    field_simp [hx0, hx1]
  have hR : (x F 0 * x F 1 + (x F 0 * x F 1)⁻¹) * (x F 0 * (x F 1) ^ 2)
      = (x F 0) ^ 2 * (x F 1) ^ 3 + x F 1 := by
    field_simp [hx0, hx1]
  rw [hL, hR] at h'
  -- 落到单项式环
  have hring : (xMono F 1) ^ 3 + (xMono F 0) ^ 2 * xMono F 1
      = (xMono F 0) ^ 2 * (xMono F 1) ^ 3 + xMono F 1 := by
    refine IsFractionRing.injective (latticeAlgebra F L2) (latticeFunctionField F L2) ?_
    show algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2)
        ((xMono F 1) ^ 3 + (xMono F 0) ^ 2 * xMono F 1)
      = algebraMap (latticeAlgebra F L2) (latticeFunctionField F L2)
        ((xMono F 0) ^ 2 * (xMono F 1) ^ 3 + xMono F 1)
    rw [map_add, map_mul, map_pow, map_pow, map_add, map_mul, map_pow, map_pow]
    show (x F 1) ^ 3 + (x F 0) ^ 2 * x F 1 = (x F 0) ^ 2 * (x F 1) ^ 3 + x F 1
    exact h'
  have hsingle : (xMono F 0) ^ 2 * (xMono F 1) ^ 3 + xMono F 1
      = MonoidAlgebra.single (Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
          + (3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) (1 : F)
        + MonoidAlgebra.single (Multiplicative.ofAdd ((1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) 1 := by
    rw [xMono_pow_mul, xMono_one]
  have hsingle' : (xMono F 1) ^ 3 + (xMono F 0) ^ 2 * xMono F 1
      = MonoidAlgebra.single (Multiplicative.ofAdd ((3 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) (1 : F)
        + MonoidAlgebra.single (Multiplicative.ofAdd ((2 : ℕ) • (Pi.single 0 (1 : ℤ) : L2)
          + (1 : ℕ) • (Pi.single 1 (1 : ℤ) : L2))) 1 := by
    rw [xMono_pow, xMono_pow_mul_one]
  exact key_single_ne F (by rw [← hsingle, ← hsingle']; exact hring.symm)

/-- `w` 不在全群不变量中。 -/
lemma wElem_not_mem : wElem F ∉ latticeInvariants F G2 L2 := by
  intro h
  exact sFst_smul_wElem_ne F ((mem_latticeInvariants_iff F G2 L2 (wElem F)).mp h sFst)

/-- **主定理：1γ 的反例（机器验证）**。

`w` 被对角元固定、但不被 `σ₀` 固定；而 `x_i + x_i⁻¹` 被全群固定，
故 `w` 落在 `F(L2)^G` 之外，更不在两者生成的子域（1γ 右端）中。 -/
theorem gamma_counterexample :
    sDiag • wElem F = wElem F ∧
      sFst • wElem F ≠ wElem F ∧
      wElem F ∉ Subfield.closure ({x F 0 + (x F 0)⁻¹, x F 1 + (x F 1)⁻¹} :
        Set (latticeFunctionField F L2)) := by
  refine ⟨sDiag_smul_wElem F, sFst_smul_wElem_ne F, ?_⟩
  intro hmem
  have hsub : ({x F 0 + (x F 0)⁻¹, x F 1 + (x F 1)⁻¹} : Set (latticeFunctionField F L2))
      ⊆ (latticeInvariants F G2 L2 : Set (latticeFunctionField F L2)) := by
    intro y hy
    rw [SetLike.mem_coe, mem_latticeInvariants_iff]
    rcases hy with hy | hy
    · rw [hy]; exact fun g => smul_x_add_inv F g 0
    · rw [hy]; exact fun g => smul_x_add_inv F g 1
  exact wElem_not_mem F ((Subfield.closure_le.mpr hsub) hmem)

/-\! ## 公理闸门 -/

#print axioms sDiag_smul_wElem
#print axioms sFst_smul_wElem_ne
#print axioms key_single_ne
#print axioms wElem_not_mem
#print axioms gamma_counterexample

end

end GammaFails

end EM

end ABGV52
