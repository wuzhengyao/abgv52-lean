/-
  ABGV-5.2 —— (2) 两条目 · **条目 1：`prop:MH-char` 的无条件部分**

  论文 `raw/ABGV-5.2-resolution.tex` `:760–808`（⚠-tex-sourced，L12/L16）：
    `M|_H ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ`，其中 `H = C_3 × C_3`、`M|_H = ker π`（Procesi 核）。

  本件交付（无条件部分）
  ======================
  §1 自建 ℤ→ℚ 换基管道：`(ι →₀ ℤ) ⊗[ℤ] ℚ ≃ₗ[ℚ] (ι →₀ ℚ)`（**mathlib 无现成件**：
     `Module ℚ` 在张积上不综合，因 mathlib 的 `TensorProduct` 只给「左因子」扩展标量；
     此处经 `finsuppScalarLeft` 把 ℚ-模结构**转移**到张积上）＋ 维数读数 `= card ι`；
  §2 法元 `N = Σ_h h`、幂等元 `e₀ = (1/9)·N`、增广 `ε`（系数和）、增广理想 `I_ℚ = ker ε`；
  §3 **显式分裂 `ℚ[H] ≅ I_ℚ ⊕ ℚ`**（`x ↦ (x − ε(x)·e₀, ε(x))`，逆 `(y,q) ↦ y + q·e₀`）
     ＋ `H`-等变（`e₀` 是 `H`-不动元，`ε` 是 `H`-不变量）＋ `finrank ℚ I_ℚ = 8`。
     论文此步以 Maschke 定理（`|H| = 9` 可逆）论证分裂；此处给出**显式**分裂元，不引 Maschke。
  §4 换基管道的读数：`finrank ℚ ((H →₀ ℤ) ⊗[ℤ] ℚ) = 9`（= `ℤ[H] ⊗ ℚ` 的维数）。

  ∅-formalization-gap（末步，未形式化——精确缺口 ＋ 两条可行路线）
  ============================================================
  **【2026-10-01 后续更新（L4 传播同步）】本段登记的 gap (α)+(β) 已由
  `BR_ABGV52.lean` 收口**（(α) 经 `comm` 转运 + `Function.Injective.module`；
  (β) 经 mathlib `LinearMap.tensorKerEquiv` + `Module.Flat ℤ ℚ`；自由桥
  `bridgeR`/`bridgeV`；交换方块 `square`）。字面结论：
  `Nonempty ((↥(LinearMap.ker pi) ⊗[ℤ] ℚ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ)` 与
  `finrank ℚ (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) = 73`（BR 的 `bridge_MH_char` /
  `finrank_ker_tensor`；**H-等变层亦已收口（2026-10-01 晚：`bridge_MH_char_equivariant`）**）。
  本段以下文字保留为历史登记。
  待形式化者：`M|_H ⊗[ℤ] ℚ ≅ 8·ℚ[H] ⊕ ℚ`（论文路线：将 Procesi 短正合列张量 ℚ，
  用 Maschke 分裂增广列，再经 `K₀(ℚ[H])` 记账）。精确缺口两条：
    * (α) `Module ℚ (M ⊗[ℤ] ℚ)`，`M` 为 `ℤ[H]^{⊕9}` 的**一般子模**：本件 §1 只建了
      finsupp 自由模（`ι →₀ ℤ`）情形；mathlib 无「右因子扩展标量」的一般实例
      （`TensorProduct.leftHasSMul` 要求 `SMul R' M`，而 `M` 是 ℤ-模）。
    * (β) `ker(f) ⊗ ℚ ≅ ker(f ⊗ id)`（ℚ 在 ℤ 上平坦 / 核无挠）。
  两条可行路线（择一）：
    路线 1（平展化）：建 (α) 的一般实例（`TensorProduct.map LinearMap.id (mulLeft q)`
      ＋ `TensorProduct.induction_on` 归纳公理）＋ (β)（`TensorProduct.rTensor_exact`
      或 `Submodule.torsion` 路线）⟹ 由 C 档/P 档已有 `Module.rank ℤ M|_H = 73`
      得 `finrank ℚ (M|_H ⊗ ℚ) = 73`，并由 SES 分裂得 `ℚ[H]^{⊕9} ≅ M|_H⊗ℚ ⊕ I_ℚ`。
    路线 2（ℚ-模型直做）：在 ℚ 上整体重建 P 档 `P1_ABGV52` 的 Procesi 复形
      （`π_ℚ`、`range π_ℚ = I_ℚ` 同一证明），以秩-零化度得 `finrank ℚ ker π_ℚ = 81 − 8 = 73`，
      再用 §1 的 `tensorQ` 与外部 `(Hp p →₀ ℤ) ⊗ ℚ ≅ Hp p →₀ ℚ` 作桥。
  末步（两条路线共同的剩余）：`M|_H ⊗ ℚ ≅ 8ℚ[H] ⊕ ℚ` 的**结构**结论须补
  「char 0 下特征标决定同构」或半单模直和消去——mathlib 二缺（§3ao 既有勘测）。
  本件**不含**任何 `sorry`；上述缺口以本文档登记，不冒充证明。
-/
import ABGV52.Hyp_ABGV52
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped TensorProduct

namespace ABGV52.MH

/-! ## 1. 自建 ℤ→ℚ 换基管道 -/

section BaseChange

variable (ι : Type*) [DecidableEq ι]

/-- **ℚ-模结构于 `(ι →₀ ℤ) ⊗[ℤ] ℚ`**（自建：经 `finsuppScalarLeft` 转移）。
mathlib 的 `TensorProduct` 只给左因子扩展标量，故须显式建（§3ao 管道缺口）。 -/
noncomputable instance instModuleQTensor : Module ℚ ((ι →₀ ℤ) ⊗[ℤ] ℚ) where
  smul q t := (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
    (q • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t))
  one_smul t := by
    change (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
      (1 • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t)) = t
    rw [one_smul, LinearEquiv.symm_apply_apply]
  mul_smul q r t := by
    change (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
      ((q * r) • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t)) =
        (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
          (q • (TensorProduct.finsuppScalarLeft ℤ ℚ ι
            ((TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
              (r • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t)))))
    rw [LinearEquiv.apply_symm_apply, mul_smul]
  smul_add q t₁ t₂ := by
    set e := TensorProduct.finsuppScalarLeft ℤ ℚ ι with he
    show e.symm (q • e (t₁ + t₂)) = e.symm (q • e t₁) + e.symm (q • e t₂)
    rw [map_add e t₁ t₂, smul_add, ← map_add e.symm (q • e t₁) (q • e t₂)]
  smul_zero q := by
    change (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
      (q • (TensorProduct.finsuppScalarLeft ℤ ℚ ι (0 : (ι →₀ ℤ) ⊗[ℤ] ℚ))) = 0
    rw [map_zero, smul_zero, map_zero]
  add_smul q r t := by
    change (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
      ((q + r) • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t)) =
        (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
          (q • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t)) +
        (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
          (r • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t))
    rw [← map_add, add_smul]
  zero_smul t := by
    change (TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
      (0 • (TensorProduct.finsuppScalarLeft ℤ ℚ ι t)) = 0
    rw [zero_smul, map_zero]

/-- **换基等价（自建）**：`(ι →₀ ℤ) ⊗[ℤ] ℚ ≃ₗ[ℚ] (ι →₀ ℚ)`。 -/
noncomputable def tensorQ : ((ι →₀ ℤ) ⊗[ℤ] ℚ) ≃ₗ[ℚ] (ι →₀ ℚ) :=
  { TensorProduct.finsuppScalarLeft ℤ ℚ ι with
    map_smul' := fun q t => by
      show (TensorProduct.finsuppScalarLeft ℤ ℚ ι)
        ((TensorProduct.finsuppScalarLeft ℤ ℚ ι).symm
          (q • (TensorProduct.finsuppScalarLeft ℤ ℚ ι) t)) =
        q • (TensorProduct.finsuppScalarLeft ℤ ℚ ι) t
      rw [LinearEquiv.apply_symm_apply] }

/-- 换基等价在基向量上的计算：`single i 1 ⊗ q ↦ single i q`。 -/
lemma tensorQ_tmul_single (i : ι) (q : ℚ) :
    tensorQ ι (Finsupp.single i (1 : ℤ) ⊗ₜ[ℤ] q) = Finsupp.single i q := by
  show (TensorProduct.finsuppScalarLeft ℤ ℚ ι) (Finsupp.single i (1 : ℤ) ⊗ₜ[ℤ] q)
    = Finsupp.single i q
  ext j
  rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply, Finsupp.single_apply,
    Finsupp.single_apply]
  by_cases hj : i = j
  · subst hj; simp
  · simp [hj]

end BaseChange

/-- **换基的维数读数**：`finrank ℚ ((ι →₀ ℤ) ⊗[ℤ] ℚ) = card ι`。 -/
theorem finrank_tensorQ (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.finrank ℚ ((ι →₀ ℤ) ⊗[ℤ] ℚ) = Fintype.card ι := by
  rw [LinearEquiv.finrank_eq (tensorQ ι)]
  exact Module.finrank_finsupp_self ℚ

/-! ## 2. 法元、幂等元 `e₀`、增广与增广理想 -/

/-- `|H| = 9`。 -/
lemma card_H : Fintype.card H = 9 := by
  simp [H, C3, ZMod.card]

/-- **法元** `N = Σ_{h∈H} h`（ℚ 系数写 `single h 1`）。 -/
noncomputable def normElQ : MonoidAlgebra ℚ H :=
  ∑ h : H, MonoidAlgebra.single h (1 : ℚ)

/-- **幂等元** `e₀ = (1/9)·N`（论文 `:788` 的分裂元）。 -/
noncomputable def e0 : MonoidAlgebra ℚ H := (1 / 9 : ℚ) • normElQ

/-- **增广** `ε`（系数和）。 -/
noncomputable def augQ : MonoidAlgebra ℚ H →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ fun _ : H => (1 : ℚ)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- **增广理想** `I_ℚ = ker ε`。 -/
noncomputable def IQ : Submodule ℚ (MonoidAlgebra ℚ H) := LinearMap.ker augQ

lemma augQ_single (h : H) (c : ℚ) :
    augQ (MonoidAlgebra.single h c) = c := by
  show Finsupp.linearCombination ℚ (fun _ : H => (1 : ℚ))
    ((MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single h c)) = c
  have h1 : (MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single h c)
      = Finsupp.single h c := rfl
  rw [h1, Finsupp.linearCombination_single]
  simp

lemma augQ_normElQ : augQ normElQ = 9 := by
  rw [normElQ, map_sum]
  simp [augQ_single, card_H]

lemma augQ_e0 : augQ e0 = 1 := by
  rw [e0, map_smul, augQ_normElQ, smul_eq_mul]
  norm_num

/-- `e₀` 在 `H`-左乘下不动。 -/
lemma lmulQ_e0 (h : H) :
    MonoidAlgebra.single h (1 : ℚ) * e0 = e0 := by
  have hN : MonoidAlgebra.single h (1 : ℚ) * normElQ = normElQ := by
    rw [normElQ, Finset.mul_sum]
    have h1 : (∑ x : H, MonoidAlgebra.single h (1 : ℚ) * MonoidAlgebra.single x 1)
        = ∑ x : H, MonoidAlgebra.single (h * x) (1 : ℚ) :=
      Finset.sum_congr rfl fun x _ => by rw [MonoidAlgebra.single_mul_single, one_mul]
    rw [h1]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun y : H => MonoidAlgebra.single y (1 : ℚ))
  rw [e0, Algebra.mul_smul_comm, hN]

/-- `ε` 在 `H`-左乘下不变。 -/
lemma augQ_lmulQ (h : H) (f : MonoidAlgebra ℚ H) :
    augQ (MonoidAlgebra.single h (1 : ℚ) * f) = augQ f := by
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single f]
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum_fintype f.coeff (fun g c => MonoidAlgebra.single g c)
    (by intro g; simp)]
  rw [Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.single_mul_single, one_mul, augQ_single, augQ_single]

/-! ## 3. 显式分裂 `ℚ[H] ≅ I_ℚ ⊕ ℚ` -/

/-- 分裂的正向：`x ↦ (x − ε(x)·e₀, ε(x))`。 -/
noncomputable def splitφ : MonoidAlgebra ℚ H →ₗ[ℚ] ↥IQ × ℚ where
  toFun f := (⟨f - augQ f • e0, by
    show augQ (f - augQ f • e0) = 0
    rw [map_sub, map_smul, augQ_e0, smul_eq_mul, mul_one, sub_self]⟩, augQ f)
  map_add' f g := by
    refine Prod.ext (Subtype.ext ?_) (map_add augQ f g)
    show (f + g) - augQ (f + g) • e0 = (f - augQ f • e0) + (g - augQ g • e0)
    rw [map_add, add_smul]
    abel
  map_smul' c f := by
    refine Prod.ext (Subtype.ext ?_) (map_smul augQ c f)
    show (c • f) - augQ (c • f) • e0 = c • (f - augQ f • e0)
    rw [map_smul, smul_sub, smul_eq_mul, ← mul_smul]

/-- 分裂的逆向：`(y, q) ↦ y + q·e₀`。 -/
noncomputable def splitψ : ↥IQ × ℚ →ₗ[ℚ] MonoidAlgebra ℚ H where
  toFun p := p.1.1 + p.2 • e0
  map_add' p p' := by
    show (p.1.1 + p'.1.1) + (p.2 + p'.2) • e0
      = (p.1.1 + p.2 • e0) + (p'.1.1 + p'.2 • e0)
    rw [add_smul]
    abel
  map_smul' c p := by
    show (c • p.1.1) + (c * p.2) • e0 = c • (p.1.1 + p.2 • e0)
    rw [mul_smul, smul_add]

lemma splitψ_splitφ (f : MonoidAlgebra ℚ H) : splitψ (splitφ f) = f := by
  show (f - augQ f • e0) + augQ f • e0 = f
  abel

lemma splitφ_splitψ (p : ↥IQ × ℚ) : splitφ (splitψ p) = p := by
  obtain ⟨⟨y, hy⟩, q⟩ := p
  have hy0 : augQ y = 0 := hy
  refine Prod.ext (Subtype.ext ?_) ?_
  · show (y + q • e0) - augQ (y + q • e0) • e0 = y
    rw [map_add, hy0, zero_add, map_smul, augQ_e0, smul_eq_mul, mul_one]
    abel
  · show augQ (y + q • e0) = q
    rw [map_add, hy0, zero_add, map_smul, augQ_e0, smul_eq_mul, mul_one]

/-- **显式分裂**：`ℚ[H] ≃ₗ[ℚ] I_ℚ ⊕ ℚ`（即论文 `ℚ[H] ≅ I_ℚ ⊕ ℚ` 的读出形）。 -/
noncomputable def augSplit : MonoidAlgebra ℚ H ≃ₗ[ℚ] ↥IQ × ℚ :=
  LinearEquiv.ofLinearMap splitφ splitψ
    (LinearMap.ext fun p => splitφ_splitψ p) (LinearMap.ext fun f => splitψ_splitφ f)

/-- 分裂对 `H`-左乘**等变**（正向；两分量分别验证）。 -/
theorem splitφ_lmulQ (h : H) (f : MonoidAlgebra ℚ H) :
    splitφ (MonoidAlgebra.single h (1 : ℚ) * f)
      = (⟨MonoidAlgebra.single h (1 : ℚ) * (splitφ f).1.1, by
          show augQ (MonoidAlgebra.single h (1 : ℚ) * (splitφ f).1.1) = 0
          rw [augQ_lmulQ]
          exact (splitφ f).1.2⟩,
        (splitφ f).2) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · show (MonoidAlgebra.single h 1 * f) - augQ (MonoidAlgebra.single h 1 * f) • e0
      = MonoidAlgebra.single h 1 * (f - augQ f • e0)
    rw [augQ_lmulQ, mul_sub, Algebra.mul_smul_comm, lmulQ_e0]
  · show augQ (MonoidAlgebra.single h (1 : ℚ) * f) = augQ f
    exact augQ_lmulQ h f

/-- **增广理想维数**：`finrank ℚ I_ℚ = 8`。 -/
theorem finrank_IQ : Module.finrank ℚ ↥IQ = 8 := by
  have h1 : Module.finrank ℚ (MonoidAlgebra ℚ H) = 9 := by
    rw [LinearEquiv.finrank_eq (MonoidAlgebra.coeffLinearEquiv ℚ),
      Module.finrank_finsupp_self ℚ, card_H]
  have h2 := LinearEquiv.finrank_eq augSplit
  rw [h1, Module.finrank_prod, Module.finrank_self] at h2
  omega

/-! ## 4. 换基管道对 `ℤ[H]` 的读数 -/

/-- `finrank ℚ (ℤ[H] ⊗[ℤ] ℚ) = 9`（= `ℚ[H]` 的维数；论文「张量 ℚ」一步的维数面）。 -/
theorem finrank_tensorQ_H : Module.finrank ℚ ((H →₀ ℤ) ⊗[ℤ] ℚ) = 9 := by
  rw [finrank_tensorQ, card_H]

/-! ## 5. 公理闸门（无 sorry、无自造公理） -/

#print axioms tensorQ
#print axioms tensorQ_tmul_single
#print axioms augQ_e0
#print axioms lmulQ_e0
#print axioms splitφ_splitψ
#print axioms augSplit
#print axioms splitφ_lmulQ
#print axioms finrank_IQ
#print axioms finrank_tensorQ_H

end ABGV52.MH
