/-
  ABGV-5.2 —— (2) 两条目 · **条目 1 收口：`prop:MH-char` 的桥缺口 (α)+(β)**

  论文 `raw/ABGV-5.2-resolution.tex` `:823–880`（⚠-tex-sourced，L12/L16）：
    `M|_H ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ`（ℚ[H]-模；H = C₃×C₃，M|_H = ker π）。
  论文证法 = 张 ℚ（平坦）＋ K₀ ＋ Maschke 半单。

  前置（已交付）：MH（换基管道、分裂）、MQ（`ker π_ℚ` 维数 73）、MI（**ℚ-模型结构结论**
  `↥(ker MQ.piQ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ`，主定理 `mainIso`）。
  **本件 = 登记的 ∅-formalization-gap (α)+(β) 收口**：把 MI 的 ℚ-模型结论沿**规范桥**
  搬到论文的字面对象 `↥(LinearMap.ker pi) ⊗[ℤ] ℚ`。

  ## 缺口与路线（逐条闭合）

  **(α)** `Module ℚ (M ⊗[ℤ] ℚ)`（mathlib 只给左因子 `ℚ ⊗ −` 扩展标量）。
    闭合：§1 —— `SMul` 定义于 `comm` 之共轭 ＋ `Function.Injective.module` 抬全模结构
    （同一函数在 `comm` 下即 ℚ-线性；`f` 用**结构字面量** `→+` 以免触发 ℤ-菱形）。
    **优先级 100** < MH 的 `instModuleQTensor`（1000）：`(ι →₀ ℤ) ⊗ ℚ` 仍解析到 MH 的实例。
  **(β)** `ker π ⊗[ℤ] ℚ ≅ ker (π ⊗[ℤ] ℚ)`（平坦性）。
    闭合：§2 —— `LinearMap.tensorKerEquiv`（`RingTheory/Flat/Equalizer.lean`）
    ＋ `Module.Flat ℤ ℚ`（本件实例化：`IsLocalization.flat` ＋ `Rat.isFractionRing`）。
  **自由桥**：§3 —— `bridgeR : ℚ ⊗[ℤ] ℤ[H] ≃ₗ[ℚ] ℚ[H]`（`congr`（经 `coeffLinearEquiv`
    转 finsupp）＋ `extendScalarsOfIsLocalization` ＋ `finsuppScalarRight`，**天生 ℚ-线性**）
    ＋ `bridgeV : ℚ ⊗[ℤ] V ≃ₗ[ℚ] VQ`（`piRight` ＋ 逐坐标 `bridgeR`）。
  **交换方块**：§4 —— `bridgeR (lTensor ℚ ℚ π t) = π_ℚ (bridgeV t)`
    （`TensorProduct.ext'` 归约到生成元 γ_{b,h}；两端各一条小计算）。
  **装配**：§5 核共轭同构 ＋ §6 主定理 `(↥(LinearMap.ker pi) ⊗[ℤ] ℚ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ`
    与维数读数 `finrank ℚ = 73`（登记缺口中「由 rank 得 finrank」的目标，此处以**同构**直达）。

  §7 **H-等变层**：`actKerLin`／`actTensorKer`（ker-因子上的 H-作用）＋ 系数桥
    `bridgeR_tmul_lmul`（系数扩张与左乘交换）／`bridgeV_tmul_act`（V-侧扩张与 `actFun` 交换）
    ⟹ `eFinalLeft_equivariant`；右形式经 `commUpgrade` 转运（作用按构造共轭）⟹
    `bridge_MH_char_equivariant`（＝论文 `prop:MH-char` 的 ℚ[H]-模同构措辞：
    `e (g • z) = single g 1 • e z`）。
-/
import ABGV52.MI_ABGV52
import ABGV52.G2b_ABGV52
import ABGV52.C8_ABGV52
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing

open TensorProduct

namespace ABGV52.BR

open ABGV52 ABGV52.MQ ABGV52.MI

/-! ## §0 基础设施：`ℚ` 平坦于 `ℤ` -/

/-- §0：`Module.Flat ℤ ℚ`（mathlib 判据：局部化平坦；`ℚ` = `ℤ` 的分式环）。 -/
instance instFlatZQ : Module.Flat ℤ ℚ :=
  IsLocalization.flat (S := ℚ) (p := nonZeroDivisors ℤ)

/-! ## §1 (α)：`X ⊗[ℤ] ℚ` 的 ℚ-模结构（经 `comm` 转运） -/

section Alpha

/-- §1 (α)：`X ⊗[ℤ] ℚ` 上的 ℚ-模结构（右因子扩展标量；经 `comm` 从左因子结构转运）。 -/
noncomputable instance (priority := 100) instModuleRightQ (X : Type) [AddCommGroup X]
    [Module ℤ X] : Module ℚ (X ⊗[ℤ] ℚ) := by
  letI : SMul ℚ (X ⊗[ℤ] ℚ) :=
    ⟨fun q t => (TensorProduct.comm ℤ X ℚ).symm (q • (TensorProduct.comm ℤ X ℚ) t)⟩
  exact Function.Injective.module ℚ
    { toFun := ⇑(TensorProduct.comm ℤ X ℚ)
      map_zero' := map_zero (TensorProduct.comm ℤ X ℚ)
      map_add' := map_add (TensorProduct.comm ℤ X ℚ) }
    (TensorProduct.comm ℤ X ℚ).injective
    (fun c x => by
      show TensorProduct.comm ℤ X ℚ
        ((TensorProduct.comm ℤ X ℚ).symm (c • TensorProduct.comm ℤ X ℚ x))
        = c • TensorProduct.comm ℤ X ℚ x
      rw [LinearEquiv.apply_symm_apply])

/-- §1 计算引理：转运结构的 `smul` 在纯张量上 = **右因子乘法**：`q • (x ⊗ r) = x ⊗ (q*r)`。 -/
lemma instModuleRightQ_smul_tmul (X : Type) [AddCommGroup X] [Module ℤ X]
    (q : ℚ) (x : X) (r : ℚ) : q • (x ⊗ₜ[ℤ] r) = x ⊗ₜ[ℤ] (q * r) := by
  rw [show q • (x ⊗ₜ[ℤ] r) = (TensorProduct.comm ℤ X ℚ).symm
      (q • TensorProduct.comm ℤ X ℚ (x ⊗ₜ[ℤ] r)) from rfl]
  rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rw [← TensorProduct.comm_tmul (R := ℤ) (M := X) (N := ℚ) x (q * r),
    LinearEquiv.symm_apply_apply]

/-- §1 转运的 ℚ-线性共轭：`comm` 升级为 ℚ-线性等价（右结构 = 左结构的转运）。 -/
noncomputable def commUpgrade (X : Type) [AddCommGroup X] [Module ℤ X] :
    (X ⊗[ℤ] ℚ) ≃ₗ[ℚ] (ℚ ⊗[ℤ] X) :=
  { TensorProduct.comm ℤ X ℚ with
    map_smul' := fun q x => by
      show TensorProduct.comm ℤ X ℚ (q • x) = q • TensorProduct.comm ℤ X ℚ x
      rw [show q • x = (TensorProduct.comm ℤ X ℚ).symm (q • TensorProduct.comm ℤ X ℚ x)
          from rfl, LinearEquiv.apply_symm_apply] }

end Alpha

/-! ## §2 (β)：`ker π ⊗[ℤ] ℚ ≅ ker (π ⊗[ℤ] ℚ)`（ℚ 平坦） -/

section Beta

/-- §2 (β)：核与 ℚ-扩张交换（mathlib `LinearMap.tensorKerEquiv` 逐字取用）。 -/
noncomputable def eTensorKer :
    ℚ ⊗[ℤ] ↥(LinearMap.ker pi) ≃ₗ[ℚ] ↥(AlgebraTensorModule.lTensor ℚ ℚ pi).ker :=
  LinearMap.tensorKerEquiv ℚ ℚ pi

end Beta

/-! ## §3 自由桥：`ℚ ⊗[ℤ] ℤ[H] ≅ ℚ[H]` 与 `ℚ ⊗[ℤ] V ≅ VQ` -/

section Free

/-- §3 系数桥（中转件）：`ℚ ⊗[ℤ] ℤ[H] ≃ₗ[ℚ] ℚ ⊗[ℤ] (H →₀ ℤ)`
（`coeffLinearEquiv` 与 `TensorProduct.congr` 复合后经 `extendScalarsOfIsLocalization`
升为 ℚ-线性；**同一函数**——`LinearMap.extendScalarsOfIsLocalization` 的 toFun 恒等）。 -/
noncomputable def bridgeRAux : ℚ ⊗[ℤ] MonoidAlgebra ℤ H ≃ₗ[ℚ] ℚ ⊗[ℤ] (H →₀ ℤ) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (MonoidAlgebra.coeffLinearEquiv ℤ)).extendScalarsOfIsLocalization
    (nonZeroDivisors ℤ) ℚ

/-- §3 自由桥（系数层）：`ℚ ⊗[ℤ] ℤ[H] ≃ₗ[ℚ] ℚ[H]`。 -/
noncomputable def bridgeR : ℚ ⊗[ℤ] MonoidAlgebra ℤ H ≃ₗ[ℚ] MonoidAlgebra ℚ H :=
  (bridgeRAux.trans (TensorProduct.finsuppScalarRight ℤ ℚ ℚ H)).trans
    (MonoidAlgebra.coeffLinearEquiv ℚ).symm

/-- §3 自由桥（`V = H → ℤ[H]` 层）：`ℚ ⊗[ℤ] V ≃ₗ[ℚ] VQ`（`piRight` ＋ 逐坐标）。 -/
noncomputable def bridgeV : ℚ ⊗[ℤ] V ≃ₗ[ℚ] VQ :=
  (TensorProduct.piRight ℤ ℚ ℚ (fun _ : H => MonoidAlgebra ℤ H)).trans
    (LinearEquiv.piCongrRight (fun _ : H => bridgeR))

/-- §3 计算引理（中转件，单点基）：`a ⊗ single h n ↦ a ⊗ single h n`（系数搬运同函数）。 -/
lemma bridgeRAux_tmul_single (a : ℚ) (h : H) (n : ℤ) :
    bridgeRAux (a ⊗ₜ[ℤ] MonoidAlgebra.single h n) = a ⊗ₜ[ℤ] Finsupp.single h n := by
  have h1 : bridgeRAux (a ⊗ₜ[ℤ] MonoidAlgebra.single h n)
      = (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (MonoidAlgebra.coeffLinearEquiv ℤ))
          (a ⊗ₜ[ℤ] MonoidAlgebra.single h n) := rfl
  rw [h1, TensorProduct.congr_tmul, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, LinearEquiv.refl_apply]

/-- §3 计算引理（单点基）：`a ⊗ single h n ↦ single h (n • a)`。 -/
lemma bridgeR_tmul_single (a : ℚ) (h : H) (n : ℤ) :
    bridgeR (a ⊗ₜ[ℤ] MonoidAlgebra.single h n) = n • MonoidAlgebra.single h a := by
  rw [show n • MonoidAlgebra.single h a = MonoidAlgebra.single h (n • a) from
    MonoidAlgebra.smul_single n h a]
  have hL : (MonoidAlgebra.coeffLinearEquiv ℚ) (bridgeR (a ⊗ₜ[ℤ] MonoidAlgebra.single h n))
      = TensorProduct.finsuppScalarRight ℤ ℚ ℚ H
          (bridgeRAux (a ⊗ₜ[ℤ] MonoidAlgebra.single h n)) := by
    rw [bridgeR, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  apply (MonoidAlgebra.coeffLinearEquiv ℚ).injective
  rw [hL, bridgeRAux_tmul_single, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single]
  ext i
  by_cases hi : h = i
  · subst hi
    simp [TensorProduct.finsuppScalarRight_apply_tmul_apply]
  · simp [TensorProduct.finsuppScalarRight_apply_tmul_apply, hi]

/-- §3 计算引理（坐标式）：`(bridgeV (a ⊗ v)) i = bridgeR (a ⊗ v i)`。 -/
lemma bridgeV_tmul_apply (a : ℚ) (v : V) (i : H) :
    bridgeV (a ⊗ₜ[ℤ] v) i = bridgeR (a ⊗ₜ[ℤ] v i) := by
  show (LinearEquiv.piCongrRight (fun _ : H => bridgeR))
    ((TensorProduct.piRight ℤ ℚ ℚ (fun _ : H => MonoidAlgebra ℤ H)) (a ⊗ₜ[ℤ] v)) i
    = bridgeR (a ⊗ₜ[ℤ] v i)
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    LinearEquiv.piCongrRight_apply]

/-- 生成元 `γ_{b,h}`：第 `b` 槽放 `single h 1`（**abbrev**：供 defeq 展开）。 -/
noncomputable abbrev gam (b h : H) : V := Pi.single b (MonoidAlgebra.single h (1 : ℤ))

/-- `gam` 的求值（同槽）。 -/
@[simp] lemma gam_apply_same (b h : H) :
    (gam b h : V) b = MonoidAlgebra.single h (1 : ℤ) :=
  Pi.single_eq_same (M := fun _ : H => MonoidAlgebra ℤ H) (i := b)
    (x := MonoidAlgebra.single h (1 : ℤ))

/-- `gam` 的求值（异槽）。 -/
@[simp] lemma gam_apply_ne {b h : H} {i : H} (hi : i ≠ b) :
    (gam b h : V) i = 0 :=
  Pi.single_eq_of_ne (M := fun _ : H => MonoidAlgebra ℤ H) (i := b) (i' := i) hi
    (MonoidAlgebra.single h (1 : ℤ))

/-- §3 计算引理（生成元）：`a ⊗ γ_{b,h} ↦ Pi.single b (single h a)`。 -/
lemma bridgeV_tmul_gam (a : ℚ) (b h : H) :
    bridgeV (a ⊗ₜ[ℤ] gam b h) = Pi.single b (MonoidAlgebra.single h a) := by
  funext i
  rw [bridgeV_tmul_apply]
  by_cases hi : i = b
  · rw [hi]
    rw [gam_apply_same b h, bridgeR_tmul_single, one_smul,
      Pi.single_eq_same (M := fun _ : H => MonoidAlgebra ℚ H) (i := b)
        (x := MonoidAlgebra.single h a)]
  · rw [gam_apply_ne (h := h) hi,
      Pi.single_eq_of_ne (M := fun _ : H => MonoidAlgebra ℚ H) (i := b) (i' := i) hi
        (MonoidAlgebra.single h a)]
    simp

end Free

/-! ## §4 交换方块：`π_ℚ` 是 `π` 沿自由桥的系数扩张 -/

section Square

/-- finsupp 层系数分解：`w = Σ_h (w h) • single h 1`。 -/
lemma finsupp_eq_sum_smul_single (w : H →₀ ℤ) :
    (∑ h : H, w h • Finsupp.single h (1 : ℤ)) = w := by
  conv_rhs => rw [← Finsupp.univ_sum_single w]
  exact Finset.sum_congr rfl fun h _ => by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `ℤ[H]` 的系数分解：`w = Σ_h (w.coeff h) • single h 1`（经 `coeffLinearEquiv` 搬运）。 -/
lemma monoidAlgebra_eq_sum_smul_single (w : MonoidAlgebra ℤ H) :
    (∑ h : H, w.coeff h • MonoidAlgebra.single h (1 : ℤ)) = w := by
  apply (MonoidAlgebra.coeffLinearEquiv ℤ).injective
  have hsum : (MonoidAlgebra.coeffLinearEquiv ℤ)
      (∑ h : H, w.coeff h • MonoidAlgebra.single h (1 : ℤ))
      = ∑ h : H, w.coeff h • Finsupp.single h (1 : ℤ) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun h _ => by
      rw [map_smul, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single]
  rw [hsum, MonoidAlgebra.coeffLinearEquiv_apply]
  exact finsupp_eq_sum_smul_single w.coeff

/-- `Pi.single b` 与系数分解相合：`Pi.single b w = Σ_h (w.coeff h) • γ_{b,h}`。 -/
lemma pi_single_eq_sum (b : H) (w : MonoidAlgebra ℤ H) :
    Pi.single b w = ∑ h : H, w.coeff h • gam b h := by
  funext i
  by_cases hib : i = b
  · rw [hib]
    rw [Pi.single_eq_same (M := fun _ : H => MonoidAlgebra ℤ H) (i := b) (x := w),
      Finset.sum_apply]
    simp only [Pi.smul_apply, gam_apply_same]
    exact (monoidAlgebra_eq_sum_smul_single w).symm
  · rw [Pi.single_eq_of_ne (M := fun _ : H => MonoidAlgebra ℤ H) (i := b) (i' := i) hib w,
      Finset.sum_apply]
    refine Eq.symm (Finset.sum_eq_zero fun h _ => ?_)
    rw [Pi.smul_apply, gam_apply_ne (h := h) hib, smul_zero]

/-- 坐标分解：`v = Σ_{b,h} (v b).coeff h • γ_{b,h}`。 -/
lemma decomp_v (v : V) :
    v = ∑ b : H, ∑ h : H, (v b).coeff h • gam b h := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  exact Finset.sum_congr rfl fun b _ => pi_single_eq_sum b (v b)

/-- 生成元上的 `π`（ℤ-端）：`π γ_{b,h} = single h 1 − single b 1`。 -/
lemma pi_gam (b h : H) :
    pi (gam b h) = MonoidAlgebra.single h (1 : ℤ) - MonoidAlgebra.single b (1 : ℤ) := by
  have h₁ : ∀ b' ∈ (Finset.univ : Finset H), b' ≠ b → piTerm b' (gam b h) = 0 := by
    intro b' _ hb'b
    simp only [piTerm_apply, gam_apply_ne (h := h) hb'b, map_zero, zero_smul, sub_zero]
  have h₂ : b ∉ (Finset.univ : Finset H) → piTerm b (gam b h) = 0 :=
    fun hb => absurd (Finset.mem_univ b) hb
  rw [pi, LinearMap.sum_apply, Finset.sum_eq_single b h₁ h₂, piTerm_apply,
    gam_apply_same b h, aug_single, one_smul]

/-- 生成元上的 `π_ℚ`（ℚ-端，系数 1）：`π_ℚ (Pi.single b (single h 1)) = single h 1 − single b 1`。 -/
lemma piQ_gam (b h : H) :
    MQ.piQ (Pi.single b (MonoidAlgebra.single h (1 : ℚ))) =
      MonoidAlgebra.single h (1 : ℚ) - MonoidAlgebra.single b (1 : ℚ) := by
  have h₁ : ∀ b' ∈ (Finset.univ : Finset H), b' ≠ b →
      MQ.piTermQ b' (Pi.single b (MonoidAlgebra.single h (1 : ℚ)) : VQ) = 0 := by
    intro b' _ hb'b
    simp only [MQ.piTermQ_apply,
      Pi.single_eq_of_ne (M := fun _ : H => MonoidAlgebra ℚ H) (i := b) (i' := b') hb'b
        (MonoidAlgebra.single h (1 : ℚ)),
      map_zero, zero_smul, sub_zero]
  have h₂ : b ∉ (Finset.univ : Finset H) →
      MQ.piTermQ b (Pi.single b (MonoidAlgebra.single h (1 : ℚ)) : VQ) = 0 :=
    fun hb => absurd (Finset.mem_univ b) hb
  rw [MQ.piQ, LinearMap.sum_apply, Finset.sum_eq_single b h₁ h₂, MQ.piTermQ_apply,
    Pi.single_eq_same, MH.augQ_single, one_smul]

/-- `Pi.single` 与 ℚ-标量相合（VQ 层）。 -/
lemma pi_single_smul (a : ℚ) (b h : H) :
    (Pi.single b (MonoidAlgebra.single h a) : VQ)
      = a • (Pi.single b (MonoidAlgebra.single h (1 : ℚ)) : VQ) := by
  funext i
  by_cases hib : i = b
  · rw [hib]
    rw [Pi.single_eq_same (M := fun _ : H => MonoidAlgebra ℚ H) (i := b)
        (x := MonoidAlgebra.single h a),
      Pi.smul_apply,
      Pi.single_eq_same (M := fun _ : H => MonoidAlgebra ℚ H) (i := b)
        (x := MonoidAlgebra.single h (1 : ℚ)),
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne (M := fun _ : H => MonoidAlgebra ℚ H) (i := b) (i' := i) hib
        (MonoidAlgebra.single h a),
      Pi.smul_apply,
      Pi.single_eq_of_ne (M := fun _ : H => MonoidAlgebra ℚ H) (i := b) (i' := i) hib
        (MonoidAlgebra.single h (1 : ℚ)),
      smul_zero]

/-- 生成元上的交换方块。 -/
lemma square_gam (a : ℚ) (b h : H) :
    bridgeR (AlgebraTensorModule.lTensor ℚ ℚ pi (a ⊗ₜ[ℤ] gam b h))
      = MQ.piQ (bridgeV (a ⊗ₜ[ℤ] gam b h)) := by
  rw [AlgebraTensorModule.lTensor_tmul, pi_gam, tmul_sub, map_sub, bridgeR_tmul_single,
    bridgeR_tmul_single, one_smul, one_smul, bridgeV_tmul_gam]
  rw [pi_single_smul, map_smul, piQ_gam, smul_sub, MonoidAlgebra.smul_single,
    MonoidAlgebra.smul_single]
  simp only [smul_eq_mul, mul_one]

/-- ≥ 链上各映射与 ℤ-标量交换（`AddMonoidHom.map_zsmul`，无隐式环）。 -/
lemma lTensor_zsmul (c : ℤ) (t : ℚ ⊗[ℤ] V) :
    AlgebraTensorModule.lTensor ℚ ℚ pi (c • t)
      = c • AlgebraTensorModule.lTensor ℚ ℚ pi t :=
  AddMonoidHom.map_zsmul (AlgebraTensorModule.lTensor ℚ ℚ pi).toAddMonoidHom c t

lemma bridgeR_zsmul (c : ℤ) (t : ℚ ⊗[ℤ] MonoidAlgebra ℤ H) :
    bridgeR (c • t) = c • bridgeR t :=
  AddMonoidHom.map_zsmul bridgeR.toLinearMap.toAddMonoidHom c t

lemma bridgeV_zsmul (c : ℤ) (t : ℚ ⊗[ℤ] V) :
    bridgeV (c • t) = c • bridgeV t :=
  AddMonoidHom.map_zsmul bridgeV.toLinearMap.toAddMonoidHom c t

lemma piQ_zsmul (c : ℤ) (z : VQ) : MQ.piQ (c • z) = c • MQ.piQ z :=
  AddMonoidHom.map_zsmul MQ.piQ.toAddMonoidHom c z

/-- 生成元（含 ℤ-系数）上的交换方块。 -/
lemma square_gam_zsmul (a : ℚ) (c : ℤ) (b h : H) :
    bridgeR (AlgebraTensorModule.lTensor ℚ ℚ pi (a ⊗ₜ[ℤ] (c • gam b h)))
      = MQ.piQ (bridgeV (a ⊗ₜ[ℤ] (c • gam b h))) := by
  rw [show a ⊗ₜ[ℤ] (c • gam b h) = c • (a ⊗ₜ[ℤ] gam b h) from
    TensorProduct.tmul_smul c a (gam b h)]
  rw [lTensor_zsmul, bridgeR_zsmul, bridgeV_zsmul, piQ_zsmul]
  exact congrArg (fun y => c • y) (square_gam a b h)

/-- **§4 交换方块**：`bridgeR (lTensor ℚ ℚ π t) = π_ℚ (bridgeV t)`，对一切 `t`。 -/
theorem square (t : ℚ ⊗[ℤ] V) :
    bridgeR (AlgebraTensorModule.lTensor ℚ ℚ pi t) = MQ.piQ (bridgeV t) := by
  have key : ∀ a : ℚ, ∀ v : V,
      bridgeR (AlgebraTensorModule.lTensor ℚ ℚ pi (a ⊗ₜ[ℤ] v))
        = MQ.piQ (bridgeV (a ⊗ₜ[ℤ] v)) := by
    intro a v
    conv_lhs => rw [decomp_v v]
    conv_rhs => rw [decomp_v v]
    conv_lhs => rw [tmul_sum]
    conv_lhs => rw [map_sum]
    conv_lhs => rw [map_sum]
    conv_rhs => rw [tmul_sum]
    conv_rhs => rw [map_sum]
    conv_rhs => rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    conv_lhs => rw [tmul_sum]
    conv_lhs => rw [map_sum]
    conv_lhs => rw [map_sum]
    conv_rhs => rw [tmul_sum]
    conv_rhs => rw [map_sum]
    conv_rhs => rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    exact square_gam_zsmul a ((v b).coeff h) b h
  have hFG : (AddMonoidHom.mk' (fun t => bridgeR (AlgebraTensorModule.lTensor ℚ ℚ pi t))
        (by simp [map_add]))
      = (AddMonoidHom.mk' (fun t => MQ.piQ (bridgeV t)) (by simp [map_add])) := by
    refine AddMonoidHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => exact key a v
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact congrArg (fun f : ℚ ⊗[ℤ] V →+ MonoidAlgebra ℚ H => f t) hFG

end Square

/-! ## §5 核的共轭同构：`ker (π ⊗[ℤ] ℚ) ≅ ker π_ℚ`（经 `bridgeV`） -/

section Conj

/-- §5 共轭核同构（§4 方块 ＋ `bridgeV` 的共轭）。 -/
noncomputable def conjKer :
    ↥(AlgebraTensorModule.lTensor ℚ ℚ pi).ker ≃ₗ[ℚ] ↥(LinearMap.ker MQ.piQ) where
  toFun y := ⟨bridgeV y.1, by
    rw [LinearMap.mem_ker, ← square y.1, y.2, map_zero]⟩
  invFun z := ⟨bridgeV.symm z.1, by
    rw [LinearMap.mem_ker]
    apply bridgeR.injective
    rw [map_zero bridgeR, square (bridgeV.symm z.1), LinearEquiv.apply_symm_apply]
    exact (LinearMap.mem_ker).mp z.2⟩
  left_inv y := Subtype.ext (LinearEquiv.symm_apply_apply bridgeV y.1)
  right_inv z := Subtype.ext (LinearEquiv.apply_symm_apply bridgeV z.1)
  map_add' y y' := Subtype.ext (map_add bridgeV y.1 y'.1)
  map_smul' c y := Subtype.ext (map_smul bridgeV c y.1)

/-- §5 链：`ℚ ⊗[ℤ] M|_H ≃ₗ[ℚ] ker π_ℚ`（(β) 件 ＋ 共轭）。 -/
noncomputable def eKerLeft :
    ℚ ⊗[ℤ] ↥(LinearMap.ker pi) ≃ₗ[ℚ] ↥(LinearMap.ker MQ.piQ) :=
  eTensorKer.trans conjKer

end Conj

/-! ## §6 装配：主定理与维数读数 -/

section Assembly

/-- §6 主定理（左形式）：`ℚ ⊗[ℤ] M|_H ≃ₗ[ℚ] (Fin 8 → R) × ℚ`（接 MI `eMain`）。 -/
noncomputable def eFinalLeft :
    ℚ ⊗[ℤ] ↥(LinearMap.ker pi) ≃ₗ[ℚ] (Fin 8 → R) × ℚ :=
  eKerLeft.trans MI.eMain

/-- §6 主定理（**论文形式**）：`M|_H ⊗[ℤ] ℚ ≃ₗ[ℚ] (Fin 8 → R) × ℚ`
（经 §1 的 ℚ-线性 `comm`）。 -/
noncomputable def eFinalRight :
    (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ :=
  (commUpgrade ↥(LinearMap.ker pi)).trans eFinalLeft

/-- **§6 主定理（`prop:MH-char` 的字面形，桥缺口 (α)+(β) 收口）**：
`M|_H ⊗[ℤ] ℚ ≅ (Fin 8 → R) × ℚ`（＝ `8·ℚ[H] ⊕ ℚ`；ℚ-线性同构）。 -/
theorem bridge_MH_char :
    Nonempty ((↥(LinearMap.ker pi) ⊗[ℤ] ℚ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ) :=
  ⟨eFinalRight⟩

/-- §6 维数读数（登记缺口的目标之一）：`finrank ℚ (M|_H ⊗[ℤ] ℚ) = 73`。 -/
theorem finrank_ker_tensor :
    Module.finrank ℚ (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) = 73 := by
  rw [LinearEquiv.finrank_eq eFinalRight, Module.finrank_prod, Module.finrank_self]
  have hpi : Module.finrank ℚ (Fin 8 → R) = 72 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin,
      MQ.finrank_monoidAlgebra_Q, nsmul_eq_mul]
    norm_num
  rw [hpi]

end Assembly

/-! ## §7 H-等变层：把 MI 的 `mainIso_equivariant` 沿桥转运

主线：ker-因子上的 H-作用（`actKerLin`，源自 C8 的 `M_H_act`）⟹ 张量作用 `actTensorKer`；
两条系数桥（`bridgeR_tmul_lmul`：系数扩张与左乘交换；`bridgeV_tmul_act`：V-侧扩张与
`actFun` 交换）⟹ 左形式等变 `eFinalLeft_equivariant`（对 `ℚ ⊗[ℤ] ker` 的纯张量归纳）；
右形式 `↥(ker) ⊗[ℤ] ℚ` 的作用经 `commUpgrade` **按构造**转运 ⟹
`bridge_MH_char_equivariant`（论文 `prop:MH-char` 的 ℚ[H]-模同构措辞）。 -/

section Equivariant

-- 局部提权：`TensorProduct.instModule` 的 ℤ-结构与 `AddCommGroup.toIntModule`
-- 在本节综合中反复争夺（§1 同款菱形）；提权使其一致取张量实例。
attribute [local instance 1500] TensorProduct.instModule

/-- H 在 `↥(ker pi)` 上的作用作为 ℤ-线性映射（源自 C8 的 `M_H_act`）。 -/
noncomputable def actKerLin (g : H) : ↥(LinearMap.ker pi) →ₗ[ℤ] ↥(LinearMap.ker pi) :=
  { toFun := M_H_act g
    map_add' := fun x y => Subtype.ext (act_add g x.1 y.1)
    map_smul' := fun n x => AddMonoidHom.map_zsmul
      (AddMonoidHom.mk' (M_H_act g) (fun x y => Subtype.ext (act_add g x.1 y.1))) n x }

lemma actKerLin_one : actKerLin (1 : H) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show act 1 x.1 = x.1
  exact act_one x.1

lemma actKerLin_mul (a b : H) :
    actKerLin (a * b) = (actKerLin a).comp (actKerLin b) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show act (a * b) x.1 = act a (act b x.1)
  exact act_mul a b x.1

/-- H 在 `ℚ ⊗[ℤ] ↥(ker pi)` 上的作用（ker-因子）。 -/
noncomputable def actTensorKer (g : H) :
    (ℚ ⊗[ℤ] ↥(LinearMap.ker pi)) →ₗ[ℤ] (ℚ ⊗[ℤ] ↥(LinearMap.ker pi)) :=
  TensorProduct.map LinearMap.id (actKerLin g)

lemma actTensorKer_one : actTensorKer (1 : H) = LinearMap.id := by
  show TensorProduct.map LinearMap.id (actKerLin (1 : H)) = LinearMap.id
  rw [actKerLin_one, TensorProduct.map_id]

lemma actTensorKer_mul (a b : H) :
    actTensorKer (a * b) = (actTensorKer a).comp (actTensorKer b) := by
  show TensorProduct.map LinearMap.id (actKerLin (a * b))
      = (TensorProduct.map LinearMap.id (actKerLin a)).comp
        (TensorProduct.map LinearMap.id (actKerLin b))
  rw [actKerLin_mul, ← TensorProduct.map_comp, LinearMap.id_comp]

lemma actTensorKer_tmul (g : H) (q : ℚ) (x : ↥(LinearMap.ker pi)) :
    actTensorKer g (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] M_H_act g x := by
  rw [actTensorKer, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

/-- 左形式上的 `DistribMulAction`（经 `actTensorKer`）。 -/
noncomputable instance instDistribMulActionKerL :
    DistribMulAction H (ℚ ⊗[ℤ] ↥(LinearMap.ker pi)) where
  smul g t := actTensorKer g t
  one_smul t := by
    show actTensorKer 1 t = t
    rw [actTensorKer_one, LinearMap.id_apply]
  mul_smul a b t := by
    show actTensorKer (a * b) t = actTensorKer a (actTensorKer b t)
    rw [actTensorKer_mul, LinearMap.comp_apply]
  smul_zero g := by
    show actTensorKer g 0 = 0
    rw [map_zero]
  smul_add g x y := by
    show actTensorKer g (x + y) = actTensorKer g x + actTensorKer g y
    rw [map_add]

/-- 系数式（`bridgeR` 的**坐标通式**）：`(bridgeR (a ⊗ p)).coeff i = (p.coeff i) • a`。 -/
lemma bridgeR_tmul_coeff (a : ℚ) (p : MonoidAlgebra ℤ H) (i : H) :
    (bridgeR (a ⊗ₜ[ℤ] p)).coeff i = p.coeff i • a := by
  show (MonoidAlgebra.coeffLinearEquiv ℚ) (bridgeR (a ⊗ₜ[ℤ] p)) i = p.coeff i • a
  have hL : (MonoidAlgebra.coeffLinearEquiv ℚ) (bridgeR (a ⊗ₜ[ℤ] p))
      = TensorProduct.finsuppScalarRight ℤ ℚ ℚ H
          (bridgeRAux (a ⊗ₜ[ℤ] p)) := by
    rw [bridgeR, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  have hA : bridgeRAux (a ⊗ₜ[ℤ] p)
      = a ⊗ₜ[ℤ] (MonoidAlgebra.coeffLinearEquiv ℤ) p := by
    show (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (MonoidAlgebra.coeffLinearEquiv ℤ))
        (a ⊗ₜ[ℤ] p) = a ⊗ₜ[ℤ] (MonoidAlgebra.coeffLinearEquiv ℤ) p
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [hL, hA, TensorProduct.finsuppScalarRight_apply_tmul_apply,
    MonoidAlgebra.coeffLinearEquiv_apply]

/-- `lmul` 的系数式：`(lmul g w).coeff y = w.coeff (g⁻¹ * y)`。 -/
lemma lmul_coeff (g y : H) (w : MonoidAlgebra ℤ H) :
    (lmul g w).coeff y = w.coeff (g⁻¹ * y) := by
  show (MonoidAlgebra.single g 1 * w).coeff y = w.coeff (g⁻¹ * y)
  rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (g⁻¹ * y) (fun m' _ => by
    constructor
    · intro h; rw [← h, inv_mul_cancel_left]
    · intro h; rw [h, mul_inv_cancel_left]),
    one_mul]

/-- **系数桥（核心）**：`bridgeR` 与左乘交换：
`bridgeR (q ⊗ lmul g w) = single g 1 * bridgeR (q ⊗ w)`。 -/
lemma bridgeR_tmul_lmul (q : ℚ) (g : H) (w : MonoidAlgebra ℤ H) :
    bridgeR (q ⊗ₜ[ℤ] lmul g w)
      = MonoidAlgebra.single g (1 : ℚ) * bridgeR (q ⊗ₜ[ℤ] w) := by
  apply MonoidAlgebra.ext
  ext y
  rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (g⁻¹ * y) (fun m' _ => by
    constructor
    · intro h; rw [← h, inv_mul_cancel_left]
    · intro h; rw [h, mul_inv_cancel_left]),
    one_mul, bridgeR_tmul_coeff, bridgeR_tmul_coeff, lmul_coeff]

/-- **V-侧系数桥（核心）**：`bridgeV` 与 `act`/`actFun` 交换。 -/
lemma bridgeV_tmul_act (q : ℚ) (g : H) (v : V) :
    bridgeV (q ⊗ₜ[ℤ] act g v) = MI.actFun g (bridgeV (q ⊗ₜ[ℤ] v)) := by
  funext i
  show bridgeR (q ⊗ₜ[ℤ] (act g v) i) = MI.actFun g (bridgeV (q ⊗ₜ[ℤ] v)) i
  rw [act_apply]
  change bridgeR (q ⊗ₜ[ℤ] lmul g (v (g⁻¹ * i)))
    = MonoidAlgebra.single g (1 : ℚ) * (bridgeV (q ⊗ₜ[ℤ] v)) (g⁻¹ * i)
  rw [bridgeV_tmul_apply, bridgeR_tmul_lmul]

/-- 左形式核同构在纯张量上的计算式。 -/
lemma eKerLeft_tmul (q : ℚ) (x : ↥(LinearMap.ker pi)) :
    eKerLeft (q ⊗ₜ[ℤ] x)
      = ⟨bridgeV (q ⊗ₜ[ℤ] x.1), (eKerLeft (q ⊗ₜ[ℤ] x)).2⟩ := by
  apply Subtype.ext
  show bridgeV (eTensorKer (q ⊗ₜ[ℤ] x)).1 = bridgeV (q ⊗ₜ[ℤ] x.1)
  rw [show (eTensorKer (q ⊗ₜ[ℤ] x)).1 = q ⊗ₜ[ℤ] x.1 from
    LinearMap.tensorKer_tmul ℚ ℚ pi q x]

/-- 全链（左形式）在纯张量上的计算式。 -/
lemma eFinalLeft_tmul (q : ℚ) (x : ↥(LinearMap.ker pi)) :
    eFinalLeft (q ⊗ₜ[ℤ] x)
      = MI.eMain ⟨bridgeV (q ⊗ₜ[ℤ] x.1), (eKerLeft (q ⊗ₜ[ℤ] x)).2⟩ := by
  rw [eFinalLeft, LinearEquiv.trans_apply]
  exact congrArg MI.eMain (eKerLeft_tmul q x)

/-- 目标侧（`(Fin 8 → R) × ℚ`）上 `single g 1` 的零。
**逐层 `show` 归约**（积 → Pi → 自层乘 / ℚ 层 `augQ` 乘）：目标侧的 `•` 由
`Prod.instSMul`/`instSMulOfMul` 供给，与 `smul_zero` 所取的 `SMulZeroClass.toSMul`
**非 defeq**（`× ℚ` 实例不一致），故须归约到乘法。 -/
lemma single_smul_zero (g : H) :
    MonoidAlgebra.single g (1 : ℚ) • (0 : (Fin 8 → R) × ℚ) = 0 := by
  show MonoidAlgebra.single g (1 : ℚ) • ((0 : Fin 8 → R), (0 : ℚ))
    = ((0 : Fin 8 → R), (0 : ℚ))
  rw [Prod.smul_mk]
  congr 1
  · funext i
    show ((MonoidAlgebra.single g (1 : ℚ) : MonoidAlgebra ℚ H) • (0 : Fin 8 → R)) i
      = (0 : Fin 8 → R) i
    rw [Pi.smul_apply]
    show MonoidAlgebra.single g (1 : ℚ) * (0 : MonoidAlgebra ℚ H) = 0
    rw [mul_zero]
  · show MH.augQ (MonoidAlgebra.single g (1 : ℚ)) * (0 : ℚ) = 0
    rw [mul_zero]

/-- 目标侧上 `single g 1` 的加法（同款逐层归约）。 -/
lemma single_smul_add (g : H) (A B : (Fin 8 → R) × ℚ) :
    MonoidAlgebra.single g (1 : ℚ) • (A + B)
      = MonoidAlgebra.single g (1 : ℚ) • A + MonoidAlgebra.single g (1 : ℚ) • B := by
  obtain ⟨A₁, A₂⟩ := A
  obtain ⟨B₁, B₂⟩ := B
  show MonoidAlgebra.single g (1 : ℚ) • ((A₁, A₂) + (B₁, B₂))
    = MonoidAlgebra.single g (1 : ℚ) • (A₁, A₂)
      + MonoidAlgebra.single g (1 : ℚ) • (B₁, B₂)
  rw [Prod.mk_add_mk, Prod.smul_mk, Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk]
  congr 1
  · funext i
    simp only [Pi.smul_apply, Pi.add_apply]
    show MonoidAlgebra.single g (1 : ℚ) * (A₁ i + B₁ i)
      = MonoidAlgebra.single g (1 : ℚ) * A₁ i + MonoidAlgebra.single g (1 : ℚ) * B₁ i
    rw [mul_add]
  · show MH.augQ (MonoidAlgebra.single g (1 : ℚ)) * (A₂ + B₂)
      = MH.augQ (MonoidAlgebra.single g (1 : ℚ)) * A₂
        + MH.augQ (MonoidAlgebra.single g (1 : ℚ)) * B₂
    rw [mul_add]

/-- **§7 主引理（左形式等变）**：`eFinalLeft (g • t) = single g 1 • eFinalLeft t`。 -/
theorem eFinalLeft_equivariant (g : H) (t : ℚ ⊗[ℤ] ↥(LinearMap.ker pi)) :
    eFinalLeft (g • t) = MonoidAlgebra.single g (1 : ℚ) • eFinalLeft t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, single_smul_zero]
  | tmul q x =>
      show eFinalLeft (g • (q ⊗ₜ[ℤ] x))
        = MonoidAlgebra.single g (1 : ℚ) • eFinalLeft (q ⊗ₜ[ℤ] x)
      rw [show g • (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] M_H_act g x from actTensorKer_tmul g q x,
        eFinalLeft_tmul q (M_H_act g x), eFinalLeft_tmul q x,
        ← MI.mainIso_equivariant g
          ⟨bridgeV (q ⊗ₜ[ℤ] x.1), (eKerLeft (q ⊗ₜ[ℤ] x)).2⟩]
      exact congrArg MI.eMain (Subtype.ext (bridgeV_tmul_act q g x.1))
  | add x y hx hy =>
      show eFinalLeft (g • (x + y))
        = MonoidAlgebra.single g (1 : ℚ) • eFinalLeft (x + y)
      rw [smul_add, map_add, hx, hy, map_add, single_smul_add]

end Equivariant

/-! ## §7b 右形式：H-作用经 `commUpgrade` 转运（按构造共轭） -/

section EquivariantRight

/-- 右形式 `↥(ker pi) ⊗[ℤ] ℚ` 上的 H-作用（经 `commUpgrade` 转运；与
`actTensorKer` 在 `commUpgrade` 之下共轭）。 -/
noncomputable def actRightKer (g : H) :
    (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) → (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) :=
  fun z => (commUpgrade ↥(LinearMap.ker pi)).symm
    (actTensorKer g ((commUpgrade ↥(LinearMap.ker pi)) z))

noncomputable instance instSMulKerR : SMul H (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) :=
  ⟨actRightKer⟩

lemma smul_kerR_apply (g : H) (z : ↥(LinearMap.ker pi) ⊗[ℤ] ℚ) :
    g • z = (commUpgrade ↥(LinearMap.ker pi)).symm
      (actTensorKer g ((commUpgrade ↥(LinearMap.ker pi)) z)) := rfl

lemma commUpgrade_smul (g : H) (z : ↥(LinearMap.ker pi) ⊗[ℤ] ℚ) :
    (commUpgrade ↥(LinearMap.ker pi)) (g • z)
      = actTensorKer g ((commUpgrade ↥(LinearMap.ker pi)) z) := by
  rw [smul_kerR_apply, LinearEquiv.apply_symm_apply]

/-- 右形式的 `DistribMulAction`（经 `Function.Injective.distribMulAction` 沿
`commUpgrade` 转运）。 -/
noncomputable instance instDistribMulActionKerR :
    DistribMulAction H (↥(LinearMap.ker pi) ⊗[ℤ] ℚ) :=
  Function.Injective.distribMulAction
    { toFun := ⇑(commUpgrade ↥(LinearMap.ker pi))
      map_zero' := map_zero (commUpgrade ↥(LinearMap.ker pi))
      map_add' := map_add (commUpgrade ↥(LinearMap.ker pi)) }
    (commUpgrade ↥(LinearMap.ker pi)).injective
    (fun g z => by
      show (commUpgrade ↥(LinearMap.ker pi)) (g • z)
        = actTensorKer g ((commUpgrade ↥(LinearMap.ker pi)) z)
      rw [smul_kerR_apply, LinearEquiv.apply_symm_apply])

/-- **§7 主定理（论文 `prop:MH-char` 的 ℚ[H]-模同构措辞）**：
`eFinalRight (g • z) = single g 1 • eFinalRight z`，对一切 `g`、`z`。 -/
theorem bridge_MH_char_equivariant (g : H) (z : ↥(LinearMap.ker pi) ⊗[ℤ] ℚ) :
    eFinalRight (g • z) = MonoidAlgebra.single g (1 : ℚ) • eFinalRight z := by
  show eFinalLeft ((commUpgrade ↥(LinearMap.ker pi)) (g • z))
    = MonoidAlgebra.single g (1 : ℚ) • eFinalRight z
  rw [commUpgrade_smul]
  exact eFinalLeft_equivariant g ((commUpgrade ↥(LinearMap.ker pi)) z)

end EquivariantRight

/-! ## 公理闸门（本件关键声明） -/

#print axioms instModuleRightQ
#print axioms commUpgrade
#print axioms eTensorKer
#print axioms bridgeRAux
#print axioms bridgeR
#print axioms bridgeV
#print axioms decomp_v
#print axioms pi_gam
#print axioms piQ_gam
#print axioms square_gam
#print axioms square
#print axioms conjKer
#print axioms eKerLeft
#print axioms eFinalLeft
#print axioms eFinalRight
#print axioms bridge_MH_char
#print axioms finrank_ker_tensor
#print axioms actKerLin
#print axioms actTensorKer
#print axioms bridgeR_tmul_coeff
#print axioms bridgeR_tmul_lmul
#print axioms bridgeV_tmul_act
#print axioms eKerLeft_tmul
#print axioms eFinalLeft_tmul
#print axioms eFinalLeft_equivariant
#print axioms instDistribMulActionKerL
#print axioms instDistribMulActionKerR
#print axioms bridge_MH_char_equivariant

end ABGV52.BR
