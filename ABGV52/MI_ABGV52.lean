/-
  ABGV-5.2 —— (2) 两条目 · **条目 1 续 2：`prop:MH-char` 的结构结论（ℚ-模型）**

  论文 `raw/ABGV-5.2-resolution.tex` `:760–808`（⚠-tex-sourced，L12/L16）：
    `M|_H ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ`，H = C₃×C₃。
  用户 2026-10-01 指令：mathlib 没有的话先搜 GitHub 高影响力仓库；仍没有则自己做。
  勘测结论：mathlib（含 flt-mathlib 分支）有 Maschke、`IsSemisimpleModule`、
  `isotypicComponent`/`IsIsotypicOfType` 全套；**无**「半单模直和消去／重数决定同构」；
  GitHub 高影响力仓库（mathlib4 PR 27428/29/27165/23963/18646/16216 等）亦未见
  「character/multiplicities determine iso」现成件 ⟹ **自建**（本件）。

  本件路线（**修正版**：原设计 §4–§6 的 isotypic 机器经实算**不需要**且含误——
  `e₂`（含 Φ）非标准 R-线性、`IsCompl E IQ''` 为假（π(Ψ(ê_y)) = y − y^∨，y = y^∨ 者给出非零交）——
  改走**显式路线**，全程 R-线性、零 isotypic 机器）：
    关键引理 `π(ê_b) = 1 − e_b`（π := piQ ∘ Φ⁻¹；ê_b = 单点向量）；
    §2 π 的 R-线性标准形 `piStd` ＋ 求和公式 `piStd z = Σ_b z_b(1 − e_b)`；
    §3 增广环同态 `augRingHom = ε`（⟹ ℚ 成平凡 R-模）、`π₁ : z ↦ (z|≠1, ε(z₁))`（ker π₁ = Ĩ）、
       `σ : y ↦ Σ_{b≠1} y_b(1 − e_b)`（range σ = I_ℚ）；
    §4 结构装配（全 R-线性）：`pi1(E) = K × ℚ`（K := ker σ）、Maschke 补 ×2 ⟹
       `E ≅ I_ℚ ⊕ K ⊕ ℚ ≅ R^{H∖1} ⊕ ℚ`（`eStructIso : ↥E ≃ₗ[R] (Fin 8 → R) × ℚ`）；
    §5 经 Φ 搬运 `ker π_ℚ ≅ E`（ℚ-线性）⟹ **主定理 `mainIso`**
       `Nonempty (↥(ker MQ.piQ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ)` ＋ **H-等变加注 `mainIso_equivariant`**
       （`eMain (actFun g z) = single g 1 • eMain z`；内容 = 「M|_H ⊗ ℚ ≅ 8ℚ[H] ⊕ ℚ 为 ℚ[H]-模同构」）。
  边界（诚实）：本条为 **ℚ-模型** 结构结论；到字面 `M|_H ⊗[ℤ] ℚ` 的桥仍属 MH 件登记的
  gap (α)+(β)，本件不声称。
  **【2026-10-01 更新（L4）】该桥已由 `BR_ABGV52.lean` 收口**：`eFinalRight` 把本件
  `eMain` 沿规范桥搬到字面对象（`bridge_MH_char`；`finrank_ker_tensor = 73`）。
  **（2026-10-01 晚更新）**：桥的 H-等变转运已完成——BR 的
  `bridge_MH_char_equivariant` 把本件 `mainIso_equivariant` 沿规范桥搬到了字面对象
  （本件 `mainIso_equivariant` 只覆盖 ℚ-模型端，此为它的转运）。

  交付记录（2026-10-01 本会话；**主定理已交付**）
  =============================================
  §0–§5 全部过编译（本件绿、0 sorry、`#print axioms` 全部三标准）；主定理 = `mainIso`，
  另附 R-线性结构件 `eStructIso` 与 H-等变件 `mainIso_equivariant`。
  与原设计（§2–§6：augSplitR／isotypic 路线）的偏差及原因：
    (a) `augSplitR`、`IQR`-R-线性分裂**不必要**（本路线只需 `augMul` ＋ `augRingHom`）；
    (b) isotypic 部件重数比较（原 §5 承重件）**不必要**——显式分解 `E ≅ I_ℚ ⊕ K ⊕ ℚ` 与
        `R^{H∖1} ≅ K ⊕ I_ℚ` 由 Maschke ＋ 两条显式正合列直接给出；
    (c) 原 §4 的 `e₂`（含 Φ）不是标准 R-线性、其 `IQ'' = Ψ(Ĩ)` 不标准稳定，且
        `E ⊓ IQ'' = 0` **为假**（实算 π(Ψ(ê_y)) = y − y^∨）。
  本轮 mathlib 事实（踩过才知）：
    * `Submodule.comapSubtypeEquivOfLe (h : p ≤ q) : ↥(p.comap q.subtype) ≃ₗ[R] ↥p`；
      `Submodule.prodEquivOfIsCompl (p q) (h) : (↥p × ↥q) ≃ₗ[R] E`；`LinearMap.ker_codRestrict`；
      `LinearMap.codRestrict` 的成员证明：`⟨x, rfl⟩` 型会因 `↑x` 与 `comp` 应用式的语法差而**失败**
      （改用 `show …; rw [LinearMap.comp_apply]; rfl`）；`Submodule.projection (p) (q) (hpq)` 的
      p q 为**显式**参数；`Submodule.projection_add_projection_eq_self`；
    * 子模积无 `prodEquiv`：`↥(p.prod q) ≅ ↥p × ↥q` 须手搓（本件 `prKQ`）；
    * `Finset.sum_subtype (s) (h : ∀ x, x ∈ s ↔ p x) (f) : ∑ a ∈ s, f a = ∑ a, f ↑a`（方向陷阱）；
      `Finset.sum_subset` 小集在左；`Finset.filter_subset`；
    * `Set.card_ne_eq : card {x | x ≠ a} = card α - 1`（子类型记法须 `show` 转写）；
      `Fintype.equivFinOfCardEq`；`LinearEquiv.funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M`；
    * **实例不一致陷阱**：`× ℚ` 型多处同形，但 ℚ 的 `Module R` 实例取法不同可使**同显示类型**语法不等
      （`prodCongr` 等的产物 vs 手写 ascription 对不上）⟹ 中间件**不写 ascription**、只锁最终类型；
    * `LinearEquiv.restrictScalars ℚ` 于本件可用（`IsScalarTower ℚ R` 自动综合）；
    * `Submodule.mem_prod`／`Submodule.mem_map`／`LinearMap.mem_range` 是 **iff**（非 defeq）——
      `x ∈ ker f` 到 `f x = 0` 的转换用 `show`（defeq 成立）；
    * `Pi.single_eq_of_ne` 方向与 `Finsupp.single_eq_of_ne` **相反**（直传 `i' ≠ i`，勿 `Ne.symm`）。
-/
import ABGV52.MQ_ABGV52
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.MonoidAlgebra.Module

namespace ABGV52.MI

open ABGV52 ABGV52.MQ

/-- 记号：`R = ℚ[H]`。 -/
abbrev R : Type := MonoidAlgebra ℚ H

/-! ## §0 双正则 H-作用（非标准作用，仅此一处；其后一律搬到标准结构） -/

/-- 双正则作用：`(g·z)_b = g·z_{g⁻¹b}`（乘法在值侧 × 位置平移同步）。 -/
noncomputable def actFun (g : H) : VQ →ₗ[ℚ] VQ where
  toFun z := fun b => MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * b)
  map_add' z z' := by
    funext b
    exact mul_add _ _ _
  map_smul' c z := by
    funext b
    show MonoidAlgebra.single g (1 : ℚ) * (c • z (g⁻¹ * b))
      = c • (MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * b))
    exact Algebra.mul_smul_comm c (MonoidAlgebra.single g (1 : ℚ)) (z (g⁻¹ * b))

lemma actFun_one_apply (z : VQ) (b : H) : actFun 1 z b = z b := by
  show MonoidAlgebra.single (1 : H) (1 : ℚ) * z ((1 : H)⁻¹ * b) = z b
  rw [inv_one, one_mul, ← MonoidAlgebra.one_def, one_mul]

lemma actFun_mul_apply (g h : H) (z : VQ) (b : H) :
    actFun (g * h) z b = actFun g (actFun h z) b := by
  show MonoidAlgebra.single (g * h) (1 : ℚ) * z ((g * h)⁻¹ * b)
      = MonoidAlgebra.single g (1 : ℚ) * (MonoidAlgebra.single h (1 : ℚ) * z (h⁻¹ * (g⁻¹ * b)))
  rw [mul_inv_rev, mul_assoc, ← mul_assoc (MonoidAlgebra.single g (1 : ℚ)),
    MonoidAlgebra.single_mul_single, one_mul]

/-! ## §1 轨道拆分同构 Φ：V ≅ V（标准结构）

`Φ_t(z) := Σ_x (z_{t·x}).coeff x • x`；逆 `Ψ_b(W) := Σ_x (W_{b·x⁻¹}).coeff x • x`。
来源：双正则作用在 `H × H` 上轨道为 `x⁻¹b = t`（9 条自由轨道），每条 ≅ 正则模。 -/

/-- 系数桥：`(single g 1 * w).coeff y = w.coeff (g⁻¹ * y)`。 -/
lemma coeff_single_mul_act (g : H) (w : R) (y : H) :
    (MonoidAlgebra.single g (1 : ℚ) * w).coeff y = w.coeff (g⁻¹ * y) := by
  rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (g⁻¹ * y) (fun m' _ => ?_), one_mul]
  constructor
  · intro h
    rw [← h, inv_mul_cancel_left]
  · intro h
    rw [h, mul_inv_cancel_left]

/-- Φ 的正向（线性层）。 -/
noncomputable def PhiL : VQ →ₗ[ℚ] VQ where
  toFun z := fun t => ∑ x : H, (z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ)
  map_add' z z' := by
    funext t
    show (∑ x : H, ((z (t * x)) + (z' (t * x))).coeff x • MonoidAlgebra.single x (1 : ℚ))
      = (∑ x : H, (z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ)) + ∑ x : H, (z' (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]
  map_smul' c z := by
    funext t
    show (∑ x : H, (c • z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ))
      = c • ∑ x : H, (z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_smul]

/-- Φ 的逆向（线性层）。 -/
noncomputable def PhiInvL : VQ →ₗ[ℚ] VQ where
  toFun W := fun b => ∑ x : H, (W (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ)
  map_add' W W' := by
    funext b
    show (∑ x : H, ((W (b * x⁻¹)) + (W' (b * x⁻¹))).coeff x • MonoidAlgebra.single x (1 : ℚ))
      = (∑ x : H, (W (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ)) + ∑ x : H, (W' (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]
  map_smul' c W := by
    funext b
    show (∑ x : H, (c • W (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ))
      = c • ∑ x : H, (W (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_smul]

/-- 和的系数：`(Σ f).coeff y = Σ (f ·).coeff y`。 -/
lemma coeff_sum_apply (f : H → R) (y : H) :
    (∑ i : H, f i).coeff y = ∑ i : H, (f i).coeff y := by
  classical
  induction (Finset.univ : Finset H) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]

/-- Φ 的系数公式：`(Φ z t).coeff y = (z (t*y)).coeff y`。 -/
lemma PhiL_coeff (z : VQ) (t y : H) :
    (PhiL z t).coeff y = (z (t * y)).coeff y := by
  show (∑ x : H, (z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ)).coeff y = _
  rw [coeff_sum_apply]
  rw [Finset.sum_eq_single y]
  · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
  · intro x _ hx
    rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, smul_eq_mul,
      Finsupp.single_eq_of_ne (Ne.symm hx), mul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

/-- Ψ 的系数公式：`(Ψ W b).coeff y = (W (b*y⁻¹)).coeff y`。 -/
lemma PhiInvL_coeff (W : VQ) (b y : H) :
    (PhiInvL W b).coeff y = (W (b * y⁻¹)).coeff y := by
  show (∑ x : H, (W (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ)).coeff y = _
  rw [coeff_sum_apply]
  rw [Finset.sum_eq_single y]
  · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
  · intro x _ hx
    rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, smul_eq_mul,
      Finsupp.single_eq_of_ne (Ne.symm hx), mul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

lemma PhiL_PhiInvL (W : VQ) : PhiL (PhiInvL W) = W := by
  funext t
  show (∑ x : H, ((PhiInvL W) (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ)) = W t
  conv_rhs => rw [eq_sum_coeff_smul_single (W t)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PhiInvL_coeff]
  congr 1
  rw [mul_inv_cancel_right]

lemma PhiInvL_PhiL (z : VQ) : PhiInvL (PhiL z) = z := by
  funext b
  show (∑ x : H, ((PhiL z) (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ)) = z b
  conv_rhs => rw [eq_sum_coeff_smul_single (z b)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PhiL_coeff]
  congr 1
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- **轨道拆分同构** `Φ : V ≅ V`（把 §0 的非标准作用搬到标准坐标结构）。 -/
noncomputable def Phi : VQ ≃ₗ[ℚ] VQ :=
  LinearEquiv.ofLinearMap PhiL PhiInvL
    (LinearMap.ext fun W => PhiL_PhiInvL W) (LinearMap.ext fun z => PhiInvL_PhiL z)

lemma Phi_apply (z : VQ) :
    Phi z = fun t => ∑ x : H, (z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ) := rfl

lemma Phi_symm_apply (W : VQ) :
    Phi.symm W = fun b => ∑ x : H, (W (b * x⁻¹)).coeff x • MonoidAlgebra.single x (1 : ℚ) :=
  rfl

/-- **等变性**：`Φ(g·z) = g • Φ(z)`（左 = 双正则作用，右 = 标准坐标作用）。 -/
theorem Phi_equivariant (g : H) (z : VQ) :
    Phi (actFun g z) = MonoidAlgebra.single g (1 : ℚ) • Phi z := by
  funext t
  show (∑ x : H, (MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * (t * x))).coeff x
      • MonoidAlgebra.single x (1 : ℚ))
    = MonoidAlgebra.single g (1 : ℚ) * ∑ x : H, (z (t * x)).coeff x
      • MonoidAlgebra.single x (1 : ℚ)
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft g)]
  rw [Finset.sum_congr rfl (fun x _ => by
    show (MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * (t * (g * x)))).coeff (g * x)
        • MonoidAlgebra.single (g * x) (1 : ℚ)
      = MonoidAlgebra.single g (1 : ℚ)
        * ((z (t * x)).coeff x • MonoidAlgebra.single x (1 : ℚ))
    have harg : g⁻¹ * (t * (g * x)) = t * x := by
      conv_lhs => rw [← mul_assoc, mul_comm g⁻¹ t, ← mul_assoc]
      rw [mul_assoc t g⁻¹ g, inv_mul_cancel, mul_one]
    rw [harg, coeff_single_mul_act, inv_mul_cancel_left]
    have h2 : MonoidAlgebra.single (g * x) (1 : ℚ)
        = MonoidAlgebra.single g (1 : ℚ) * MonoidAlgebra.single x (1 : ℚ) := by
      rw [MonoidAlgebra.single_mul_single, one_mul]
    rw [h2]
    exact (Algebra.mul_smul_comm _ _ _).symm)]
  rw [Finset.mul_sum]

/-- 等变性的逆向形式（供 §3 用）：`Φ⁻¹(g • W) = g·Φ⁻¹(W)`。 -/
theorem Phi_symm_equivariant (g : H) (W : VQ) :
    Phi.symm (MonoidAlgebra.single g (1 : ℚ) • W) = actFun g (Phi.symm W) := by
  apply Phi.injective
  rw [LinearEquiv.apply_symm_apply, Phi_equivariant g (Phi.symm W),
    LinearEquiv.apply_symm_apply]

/-! ## §2 π 的 R-线性标准形：`piStd = MQ.piQ ∘ Φ.symm`

`piStd` 是 `VQ → R` 的 **R-线性**映射（把 §0 的非标准作用经 `Φ` 搬到标准坐标结构；
这弥补了 `MQ.piQ` 本身对标准结构不 R-线性的问题）。
关键读数：`piStd ê_b = 1 − b`（`ê_b` = 单点向量），据此 `piStd z = Σ_b z_b(1 − e_b)`，
于是 `Ĩ := δIncl(I_ℚ)` 落入 `ker piStd`。 -/

lemma actFun_apply (g : H) (z : VQ) :
    actFun g z = fun b => MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * b) := rfl

theorem Phi_apply_evec (b : H) :
    Phi (Pi.single b (1 : R) : VQ) = (Pi.single b (1 : R) : VQ) := by
  funext t
  show PhiL (Pi.single b (1 : R) : VQ) t = (Pi.single b (1 : R) : VQ) t
  ext y
  rw [PhiL_coeff]
  by_cases hy : y = 1
  · rw [hy, mul_one]
  · have hL : ((Pi.single b (1 : R) : VQ) (t * y)).coeff y = 0 := by
      by_cases h1 : t * y = b
      · rw [h1, Pi.single_eq_same]
        show ((1 : R)).coeff y = 0
        rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hy]
      · rw [Pi.single_eq_of_ne h1, MonoidAlgebra.coeff_zero]
        simp
    have hR : ((Pi.single b (1 : R) : VQ) t).coeff y = 0 := by
      by_cases h2 : t = b
      · rw [h2, Pi.single_eq_same]
        show ((1 : R)).coeff y = 0
        rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hy]
      · rw [Pi.single_eq_of_ne h2, MonoidAlgebra.coeff_zero]
        simp
    rw [hL, hR]

theorem Psi_apply_evec (b : H) :
    Phi.symm (Pi.single b (1 : R) : VQ) = (Pi.single b (1 : R) : VQ) := by
  apply Phi.injective
  rw [LinearEquiv.apply_symm_apply, Phi_apply_evec]

theorem piQ_evec (b : H) :
    MQ.piQ (Pi.single b (1 : R) : VQ) = 1 - MonoidAlgebra.single b (1 : ℚ) := by
  rw [MQ.piQ, LinearMap.sum_apply, Finset.sum_eq_single b]
  · rw [MQ.piTermQ_apply, Pi.single_eq_same]
    have h1 : MH.augQ (1 : R) = 1 := by
      conv_lhs => rw [MonoidAlgebra.one_def]
      rw [MH.augQ_single]
    rw [h1, one_smul]
  · intro b' _ hb'
    rw [MQ.piTermQ_apply, Pi.single_eq_of_ne hb', map_zero, zero_smul, sub_zero]
  · intro hmem
    exact absurd (Finset.mem_univ b) hmem

theorem piQ_equivariant (g : H) (z : VQ) :
    MQ.piQ (actFun g z) = MonoidAlgebra.single g (1 : ℚ) * MQ.piQ z := by
  rw [MQ.piQ, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft g)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MQ.piTermQ_apply, MQ.piTermQ_apply, actFun_apply]
  show MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * (g * b))
      - MH.augQ (MonoidAlgebra.single g (1 : ℚ) * z (g⁻¹ * (g * b)))
        • MonoidAlgebra.single (g * b) (1 : ℚ)
    = MonoidAlgebra.single g (1 : ℚ)
        * (z b - MH.augQ (z b) • MonoidAlgebra.single b (1 : ℚ))
  rw [inv_mul_cancel_left, MH.augQ_lmulQ, mul_sub, Algebra.mul_smul_comm,
    MonoidAlgebra.single_mul_single, one_mul]

/-- **π 的标准 R-线性形**：`piStd = MQ.piQ ∘ Φ.symm`（R-线性；`Φ` 把非标准作用搬到标准结构）。 -/
noncomputable def piStd : VQ →ₗ[R] R where
  toFun z := MQ.piQ (Phi.symm z)
  map_add' z z' := by
    show MQ.piQ (Phi.symm (z + z')) = MQ.piQ (Phi.symm z) + MQ.piQ (Phi.symm z')
    rw [map_add, map_add]
  map_smul' r z := by
    show MQ.piQ (Phi.symm (r • z)) = r * MQ.piQ (Phi.symm z)
    conv_lhs => rw [MQ.eq_sum_coeff_smul_single r]
    rw [Finset.sum_smul]
    conv_lhs => rw [map_sum]
    conv_lhs => rw [map_sum]
    conv_rhs => rw [MQ.eq_sum_coeff_smul_single r]
    conv_rhs => rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_assoc, map_smul, map_smul, Phi_symm_equivariant, piQ_equivariant]
    exact (Algebra.smul_mul_assoc (r.coeff g) (MonoidAlgebra.single g (1 : ℚ))
      (MQ.piQ (Phi.symm z))).symm

theorem piStd_evec (b : H) :
    piStd (Pi.single b (1 : R) : VQ) = 1 - MonoidAlgebra.single b (1 : ℚ) := by
  show MQ.piQ (Phi.symm (Pi.single b (1 : R) : VQ)) = 1 - MonoidAlgebra.single b (1 : ℚ)
  rw [Psi_apply_evec, piQ_evec]

theorem sum_single_smul (z : VQ) :
    (∑ b : H, z b • (Pi.single b (1 : R) : VQ)) = z := by
  funext b'
  rw [Finset.sum_apply, Finset.sum_eq_single b']
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ b') hmem

/-- **π 的求和公式**：`piStd z = Σ_b z_b (1 − e_b)`。 -/
theorem piStd_apply (z : VQ) :
    piStd z = ∑ b : H, z b * (1 - MonoidAlgebra.single b (1 : ℚ)) := by
  conv_lhs => rw [← sum_single_smul z]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_smul, piStd_evec, smul_eq_mul]

/-! ### E 与 Ĩ ⊆ E -/

/-- `E := ker piStd`（`π` 的核；论文 `M|_H` 的 ℚ-模型，携带标准结构）。 -/
noncomputable def E : Submodule R VQ := LinearMap.ker piStd

/-- **ε 的乘法性**：`ε(rs) = ε(r)·ε(s)`（R-线性增广所必需；`r` 按系数展开归约到 `e_g`）。 -/
theorem augMul (r s : R) : MH.augQ (r * s) = MH.augQ r * MH.augQ s := by
  conv_lhs => rw [MQ.eq_sum_coeff_smul_single r]
  conv_lhs => rw [Finset.sum_mul]
  conv_lhs => rw [map_sum]
  conv_rhs => rw [MQ.augQ_eq_sum_coeff r, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [smul_mul_assoc, map_smul, MH.augQ_lmulQ, smul_eq_mul]

/-- 增广理想作 **R-子模**（`MH.IQ` 的 R-结构升级；闭包性 = `augMul`）。 -/
noncomputable def IQR : Submodule R R where
  carrier := MH.IQ
  zero_mem' := MH.IQ.zero_mem
  add_mem' := MH.IQ.add_mem
  smul_mem' r x hx := by
    have hx' : MH.augQ x = 0 := hx
    show MH.augQ (r * x) = 0
    rw [augMul, hx', mul_zero]

/-- 单坐标嵌入：`δ : x ↦ (x, 0, …, 0)`（R-线性）。 -/
noncomputable def deltaIncl : R →ₗ[R] VQ where
  toFun x := (Pi.single (1 : H) x : VQ)
  map_add' x x' := by
    funext b
    by_cases h : b = 1
    · subst h
      rw [Pi.single_eq_same, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.add_apply, Pi.single_eq_of_ne h,
        Pi.single_eq_of_ne h, add_zero]
  map_smul' r x := by
    funext b
    by_cases h : b = 1
    · subst h
      rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne h, Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero]

/-- `Ĩ := δIncl(I_ℚ)`（增广理想在坐标 1 的拷贝；R-子模）。 -/
noncomputable def IQt : Submodule R VQ := IQR.map deltaIncl

theorem deltaIncl_injective : Function.Injective (deltaIncl : R → VQ) := by
  intro x x' h
  have h1 : deltaIncl x (1 : H) = deltaIncl x' (1 : H) := congr_fun h 1
  simpa [deltaIncl, Pi.single_eq_same] using h1

/-- 关键读数：`δIncl(I_ℚ) ⊆ ker piStd`（`piStd (δ x) = x·(1−e₁) = 0`）。 -/
theorem IQt_le_E : IQt ≤ E := by
  rintro z ⟨x, _hx, rfl⟩
  show piStd (deltaIncl x) = 0
  rw [piStd_apply]
  rw [Finset.sum_eq_single (1 : H)]
  · show (Pi.single (1 : H) x : VQ) 1
        * (1 - MonoidAlgebra.single (1 : H) (1 : ℚ)) = 0
    rw [Pi.single_eq_same]
    have hone : MonoidAlgebra.single (1 : H) (1 : ℚ) = (1 : R) := MonoidAlgebra.one_def.symm
    rw [hone, sub_self, mul_zero]
  · intro b _ hb
    show (Pi.single (1 : H) x : VQ) b * (1 - MonoidAlgebra.single b (1 : ℚ)) = 0
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ (1 : H)) hmem

/-! ## §3 增广环同态、π₁ 与 σ

`ℚ` 经 `augRingHom = ε` 成为平凡 R-模（供 R-线性陈述用）。
`π₁ : z ↦ (z|≠1, ε(z₁))` 的核恰为 `Ĩ`；`σ : y ↦ Σ_{b≠1} y_b(1 − e_b)` 的像恰为 `I_ℚ`。 -/

@[simp] lemma deltaIncl_apply (x : R) : deltaIncl x = (Pi.single (1 : H) x : VQ) := rfl

/-- 增广作环同态（乘法性 = `augMul`）。 -/
noncomputable def augRingHom : R →+* ℚ where
  toFun := MH.augQ
  map_one' := by
    conv_lhs => rw [MonoidAlgebra.one_def]
    rw [MH.augQ_single]
  map_mul' := augMul
  map_zero' := map_zero MH.augQ
  map_add' := map_add MH.augQ

lemma augRingHom_apply (r : R) : augRingHom r = MH.augQ r := rfl

/-- 平凡 R-模结构于 `ℚ`（`ε` 经 `augRingHom` 作用）。 -/
noncomputable instance instModuleTriv : Module R ℚ := Module.compHom ℚ augRingHom

theorem pi1_apply_smul (r : R) (z : VQ) :
    (fun b : {b : H // b ≠ 1} => (r • z) b.1) = r • (fun b : {b : H // b ≠ 1} => z b.1) := by
  funext b
  rw [Pi.smul_apply]
  rfl

theorem pi1_aug_smul (r : R) (z : VQ) :
    MH.augQ ((r • z) 1) = r • MH.augQ (z 1) := by
  rw [Pi.smul_apply, smul_eq_mul, augMul]
  rfl

/-- `π₁ : VQ ↠ ({b // b ≠ 1} → R) × ℚ`（`z ↦ (z|≠1, ε(z₁))`；R-线性）。 -/
noncomputable def pi1 : VQ →ₗ[R] ({b : H // b ≠ 1} → R) × ℚ where
  toFun z := (fun b => z b.1, MH.augQ (z 1))
  map_add' z z' := by
    refine Prod.ext ?_ ?_
    · funext b
      rfl
    · exact map_add MH.augQ (z 1) (z' 1)
  map_smul' r z := by
    refine Prod.ext ?_ ?_
    · exact pi1_apply_smul r z
    · exact pi1_aug_smul r z

/-- **π₁ 的核**：`ker π₁ = Ĩ`（坐标 1 的 `I_ℚ` 拷贝）。 -/
theorem ker_pi1 : LinearMap.ker pi1 = IQt := by
  ext z
  constructor
  · intro hz
    have h1 : (fun b : {b : H // b ≠ 1} => z b.1) = 0 := congrArg Prod.fst hz
    have h2 : MH.augQ (z 1) = 0 := congrArg Prod.snd hz
    refine Submodule.mem_map.mpr ⟨z 1, h2, ?_⟩
    funext b
    by_cases hb : b = 1
    · subst hb
      rw [deltaIncl_apply, Pi.single_eq_same]
    · rw [deltaIncl_apply, Pi.single_eq_of_ne hb]
      exact (congr_fun h1 ⟨b, hb⟩).symm
  · rintro ⟨x, hx, rfl⟩
    refine Prod.ext ?_ ?_
    · funext b
      show (deltaIncl x) b.1 = 0
      rw [deltaIncl_apply, Pi.single_eq_of_ne b.2]
    · have hx' : MH.augQ x = 0 := hx
      show MH.augQ (deltaIncl x 1) = 0
      rw [deltaIncl_apply, Pi.single_eq_same]
      exact hx'

/-- `σ : y ↦ Σ_{b≠1} y_b(1 − e_b)`（LinearMap-和形，免手工 map_add'/map_smul'）。 -/
noncomputable def sigma : ({b : H // b ≠ 1} → R) →ₗ[R] R :=
  ∑ b : {b : H // b ≠ 1},
    (LinearMap.proj b).smulRight ((1 : R) - MonoidAlgebra.single b.1 (1 : ℚ))

theorem sigma_apply (y : {b : H // b ≠ 1} → R) :
    sigma y = ∑ b : {b : H // b ≠ 1}, y b • ((1 : R) - MonoidAlgebra.single b.1 (1 : ℚ)) := by
  rw [sigma, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [LinearMap.smulRight_apply]
  rfl

theorem one_sub_single_mem_IQR (g : H) :
    (1 : R) - MonoidAlgebra.single g (1 : ℚ) ∈ IQR := by
  show MH.augQ (1 - MonoidAlgebra.single g (1 : ℚ)) = 0
  rw [map_sub]
  have h1 : MH.augQ (1 : R) = 1 := by
    conv_lhs => rw [MonoidAlgebra.one_def]
    rw [MH.augQ_single]
  rw [h1, MH.augQ_single, sub_self]

theorem sigma_single (b : {b : H // b ≠ 1}) :
    sigma (Pi.single b (1 : R)) = 1 - MonoidAlgebra.single b.1 (1 : ℚ) := by
  rw [sigma_apply, Finset.sum_eq_single b]
  · rw [Pi.single_eq_same, one_smul]
  · intro b' _ hb'
    rw [Pi.single_eq_of_ne hb', zero_smul]
  · intro hmem
    exact absurd (Finset.mem_univ b) hmem

/-- **σ 的像**：`range σ = I_ℚ`（生成元 `1 − e_g` 的 R-张成恰为增广理想）。 -/
theorem range_sigma : LinearMap.range sigma = IQR := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨y, rfl⟩
    rw [sigma_apply]
    refine Submodule.sum_mem _ (fun b _ => ?_)
    exact Submodule.smul_mem _ _ (one_sub_single_mem_IQR b.1)
  · intro x hx
    have hspan : x ∈ Submodule.span R
        (Set.range (fun g : H => (1 : R) - MonoidAlgebra.single g (1 : ℚ))) := by
      rw [MQ.eq_sum_coeff_smul_sub_one x hx]
      refine Submodule.sum_mem
        (Submodule.span R (Set.range (fun g : H => (1 : R) - MonoidAlgebra.single g (1 : ℚ))))
        (fun g _ => ?_)
      have hmem0 : (1 : R) - MonoidAlgebra.single g (1 : ℚ) ∈
          Set.range (fun g : H => (1 : R) - MonoidAlgebra.single g (1 : ℚ)) := ⟨g, rfl⟩
      have hmem : (1 : R) - MonoidAlgebra.single g (1 : ℚ) ∈
          Submodule.span R (Set.range (fun g : H => (1 : R) - MonoidAlgebra.single g (1 : ℚ))) :=
        Submodule.subset_span (R := R) hmem0
      have hneg : MonoidAlgebra.single g (1 : ℚ) - 1
          = -((1 : R) - MonoidAlgebra.single g (1 : ℚ)) := by abel
      rw [hneg]
      have h1 : ((x.coeff g) • (1 : R)) • (-((1 : R) - MonoidAlgebra.single g (1 : ℚ)))
          ∈ Submodule.span R (Set.range (fun g : H => (1 : R) - MonoidAlgebra.single g (1 : ℚ))) :=
        Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)
      rwa [smul_assoc, one_smul] at h1
    have hgen : Set.range (fun g : H => (1 : R) - MonoidAlgebra.single g (1 : ℚ))
        ⊆ (LinearMap.range sigma : Set R) := by
      rintro w ⟨g, rfl⟩
      show ((1 : R) - MonoidAlgebra.single g (1 : ℚ)) ∈ LinearMap.range sigma
      by_cases h1 : g = 1
      · subst h1
        rw [MonoidAlgebra.one_def, sub_self]
        exact Submodule.zero_mem _
      · refine LinearMap.mem_range.mpr ⟨?_, ?_⟩
        · exact Pi.single ⟨g, h1⟩ (1 : R)
        · rw [sigma_single]
    exact Submodule.span_le.mpr hgen hspan

/-\! ## §4 E 的结构：`E ≅ I_ℚ ⊕ K ⊕ ℚ ≅ R^{H∖1} ⊕ ℚ`（全 R-线性）

`K := ker σ`；两条显式正合列（`π₁` 与 `σ`）＋ Maschke 补的投影同构完成装配；
`eStructIso : ↥E ≃ₗ[R] (Fin 8 → R) × ℚ` 即论文 `prop:MH-char` 的 ℚ-模型结构结论。 -/

/-- `K = ker σ`（`R^{H∖1}` 中的"关系"子模）。 -/
noncomputable def K : Submodule R ({b : H // b ≠ 1} → R) := LinearMap.ker sigma

theorem piStd_eq_sigma (z : VQ) :
    piStd z = sigma (fun b : {b : H // b ≠ 1} => z b.1) := by
  have hmul : (∑ b : H, z b * (1 - MonoidAlgebra.single b (1 : ℚ)))
      = ∑ b : H, z b • ((1 : R) - MonoidAlgebra.single b (1 : ℚ)) :=
    Finset.sum_congr rfl (fun b _ =>
      (smul_eq_mul (z b) ((1 : R) - MonoidAlgebra.single b (1 : ℚ))).symm)
  have h1 : (∑ b : H, z b • ((1 : R) - MonoidAlgebra.single b (1 : ℚ)))
      = ∑ b ∈ Finset.univ.filter (fun b : H => b ≠ 1),
          z b • ((1 : R) - MonoidAlgebra.single b (1 : ℚ)) :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => by
      have hx1 : x = 1 := by
        by_contra h
        exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
      subst hx1
      rw [MonoidAlgebra.one_def, sub_self, smul_eq_mul, mul_zero])).symm
  have h2 : (∑ b : {b : H // b ≠ 1},
        z b.1 • ((1 : R) - MonoidAlgebra.single b.1 (1 : ℚ)))
      = ∑ b ∈ Finset.univ.filter (fun b : H => b ≠ 1),
          z b • ((1 : R) - MonoidAlgebra.single b (1 : ℚ)) :=
    (Finset.sum_subtype (Finset.univ.filter (fun b : H => b ≠ 1)) (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩)
      (fun b : H => z b • ((1 : R) - MonoidAlgebra.single b (1 : ℚ)))).symm
  rw [piStd_apply, sigma_apply, hmul, h1, ← h2]

theorem pi1_map_E : Submodule.map pi1 E = K.prod ⊤ := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨z, hz, rfl⟩
    refine Submodule.mem_prod.mpr ⟨?_, trivial⟩
    have hz' : piStd z = 0 := hz
    show sigma (fun b : {b : H // b ≠ 1} => z b.1) = 0
    rw [← piStd_eq_sigma z]
    exact hz'
  · rintro ⟨y, c⟩ hw
    obtain ⟨hy, _⟩ := Submodule.mem_prod.mp hw
    have hy' : sigma y = 0 := hy
    refine ⟨fun b => if h : b = 1 then c • (1 : R) else y ⟨b, h⟩, ?_, ?_⟩
    · show piStd _ = 0
      rw [piStd_eq_sigma]
      have hy2 : (fun b : {b : H // b ≠ 1} =>
          (fun b => if h : b = 1 then c • (1 : R) else y ⟨b, h⟩) b.1) = y := by
        funext b
        show (if h : b.1 = 1 then c • (1 : R) else y ⟨b.1, h⟩) = y b
        rw [dif_neg b.2]
      rw [hy2, hy']
    · refine Prod.ext ?_ ?_
      · funext b
        show (if h : b.1 = 1 then c • (1 : R) else y ⟨b.1, h⟩) = y b
        rw [dif_neg b.2]
      · show MH.augQ (if h : (1 : H) = 1 then c • (1 : R) else y ⟨1, h⟩) = c
        rw [dif_pos rfl, map_smul]
        have h1 : MH.augQ (1 : R) = 1 := by
          conv_lhs => rw [MonoidAlgebra.one_def]
          rw [MH.augQ_single]
        rw [h1, smul_eq_mul, mul_one]

theorem pi1E_ker : LinearMap.ker (pi1.comp E.subtype) = IQt.comap E.subtype := by
  rw [LinearMap.ker_comp, ker_pi1]

theorem pi1E_range : LinearMap.range (pi1.comp E.subtype) = K.prod ⊤ := by
  rw [LinearMap.range_comp, Submodule.range_subtype, pi1_map_E]

noncomputable def prKQ : ↥(K.prod (⊤ : Submodule R ℚ)) ≃ₗ[R] ↥K × ℚ where
  toFun x := (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, x.1.2)
  invFun y := ⟨(y.1.1, y.2), Submodule.mem_prod.mpr ⟨y.1.2, trivial⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Prod.ext rfl rfl
  map_add' x x' := Prod.ext rfl rfl
  map_smul' c x := Prod.ext rfl rfl

/-- `IQt` 在 `E` 内的补（取定一个；Maschke）。 -/
noncomputable def CE : Submodule R ↥E :=
  Classical.choose (MonoidAlgebra.Submodule.exists_isCompl (IQt.comap E.subtype))

theorem CE_isCompl : IsCompl (IQt.comap E.subtype) CE :=
  Classical.choose_spec (MonoidAlgebra.Submodule.exists_isCompl (IQt.comap E.subtype))

theorem compl_iso (C' : Submodule R ↥E) (hC' : IsCompl (IQt.comap E.subtype) C') :
    Nonempty (↥C' ≃ₗ[R] ↥K × ℚ) := by
  have hmem_range : ∀ x : ↥E, (pi1.comp E.subtype) x ∈ K.prod ⊤ := by
    intro x
    rw [← pi1E_range]
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp
      C'.subtype) = ⊥ := by
    rw [LinearMap.ker_comp, LinearMap.ker_codRestrict, pi1E_ker]
    refine (Submodule.eq_bot_iff _).mpr (fun x hx => ?_)
    exact Subtype.ext (Submodule.disjoint_def.mp hC'.disjoint x.1 hx x.2)
  have hinj : Function.Injective
      (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype) := by
    intro x y hxy
    have hz : (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype)
        (x - y) = 0 := by
      have h1 : (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype)
            (x - y)
          = (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype) x
            - (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype) y :=
        map_sub _ x y
      rw [h1, hxy, sub_self]
    have hmem : x - y ∈ LinearMap.ker
        (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype) := hz
    rw [hker] at hmem
    have h0 : x - y = 0 := by simpa using hmem
    exact sub_eq_zero.mp h0
  have hsurj : Function.Surjective
      (((pi1.comp E.subtype).codRestrict (K.prod ⊤) hmem_range).comp C'.subtype) := by
    intro w
    have hw : (w : ({b : H // b ≠ 1} → R) × ℚ) ∈ LinearMap.range (pi1.comp E.subtype) := by
      rw [pi1E_range]
      exact w.property
    obtain ⟨e, he⟩ := hw
    refine ⟨⟨C'.projection (IQt.comap E.subtype) hC'.symm e,
      Submodule.projection_apply_mem hC'.symm e⟩, ?_⟩
    refine Subtype.ext ?_
    show (pi1.comp E.subtype) (C'.projection (IQt.comap E.subtype) hC'.symm e)
      = (w : ({b : H // b ≠ 1} → R) × ℚ)
    have hsum : (IQt.comap E.subtype).projection C' hC' e
        + C'.projection (IQt.comap E.subtype) hC'.symm e = e :=
      Submodule.projection_add_projection_eq_self hC' e
    have hz : (pi1.comp E.subtype) ((IQt.comap E.subtype).projection C' hC' e) = 0 := by
      have hmem : ((IQt.comap E.subtype).projection C' hC' e : ↥E) ∈ IQt.comap E.subtype :=
        Submodule.projection_apply_mem hC' e
      have hmem2 : ((IQt.comap E.subtype).projection C' hC' e : ↥E)
          ∈ LinearMap.ker (pi1.comp E.subtype) := by
        rw [pi1E_ker]
        exact hmem
      exact hmem2
    rw [← he]
    conv_rhs => rw [← hsum]
    rw [map_add, hz, zero_add]
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).trans prKQ⟩

/-- `E ≅ I_ℚ × (K × ℚ)`（取定 Maschke 补）。 -/
noncomputable def eE : ↥E ≃ₗ[R] ↥IQR × (↥K × ℚ) :=
  (Submodule.prodEquivOfIsCompl _ _ CE_isCompl).symm.trans
    (((Submodule.comapSubtypeEquivOfLe IQt_le_E).trans
      (Submodule.equivMapOfInjective deltaIncl deltaIncl_injective IQR).symm).prodCongr
      (Classical.choice (compl_iso CE CE_isCompl)))


/-- `K` 在 `R^{H∖1}` 内的补（取定一个；Maschke）。 -/
noncomputable def CK : Submodule R ({b : H // b ≠ 1} → R) :=
  Classical.choose (MonoidAlgebra.Submodule.exists_isCompl
    (K : Submodule R ({b : H // b ≠ 1} → R)))

theorem CK_isCompl : IsCompl (K : Submodule R ({b : H // b ≠ 1} → R)) CK :=
  Classical.choose_spec (MonoidAlgebra.Submodule.exists_isCompl
    (K : Submodule R ({b : H // b ≠ 1} → R)))

theorem hmemCK : ∀ x : ↥CK, (sigma.comp CK.subtype) x ∈ LinearMap.range sigma :=
  fun x => ⟨x.1, by
    show sigma (x : {b : H // b ≠ 1} → R) = (sigma.comp CK.subtype) x
    rw [LinearMap.comp_apply]
    rfl⟩

theorem eCK_ker : LinearMap.ker ((sigma.comp CK.subtype).codRestrict
    (LinearMap.range sigma) hmemCK) = ⊥ := by
  rw [LinearMap.ker_codRestrict, LinearMap.ker_comp]
  refine (Submodule.eq_bot_iff _).mpr (fun z hz' => ?_)
  exact Subtype.ext (Submodule.disjoint_def.mp CK_isCompl.disjoint z.1 hz' z.2)

/-- `CK ≅ range σ = I_ℚ`（σ 限制；σ|_K = 0 ⟹ 补上单射）。 -/
noncomputable def eCK : ↥CK ≃ₗ[R] ↥IQR :=
  (LinearEquiv.ofBijective
    ((sigma.comp CK.subtype).codRestrict (LinearMap.range sigma) hmemCK)
    ⟨by
      intro x y hxy
      have hz : ((sigma.comp CK.subtype).codRestrict (LinearMap.range sigma) hmemCK)
          (x - y) = 0 := by
        have h1 : ((sigma.comp CK.subtype).codRestrict (LinearMap.range sigma) hmemCK)
              (x - y)
            = ((sigma.comp CK.subtype).codRestrict (LinearMap.range sigma) hmemCK) x
              - ((sigma.comp CK.subtype).codRestrict (LinearMap.range sigma) hmemCK) y :=
          map_sub _ x y
        rw [h1, hxy, sub_self]
      have hmem : x - y ∈ LinearMap.ker
          ((sigma.comp CK.subtype).codRestrict (LinearMap.range sigma) hmemCK) := hz
      rw [eCK_ker] at hmem
      have h0 : x - y = 0 := by simpa using hmem
      exact sub_eq_zero.mp h0,
     by
      intro w
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp w.property
      refine ⟨⟨CK.projection K CK_isCompl.symm y,
        Submodule.projection_apply_mem CK_isCompl.symm y⟩, ?_⟩
      refine Subtype.ext ?_
      show sigma (CK.projection K CK_isCompl.symm y) = (w : R)
      have hsum : K.projection CK CK_isCompl y
          + CK.projection K CK_isCompl.symm y = y :=
        Submodule.projection_add_projection_eq_self CK_isCompl y
      have hz : sigma (K.projection CK CK_isCompl y) = 0 :=
        Submodule.projection_apply_mem CK_isCompl y
      rw [← hy]
      conv_rhs => rw [← hsum]
      rw [map_add, hz, zero_add]⟩).trans (LinearEquiv.ofEq _ _ range_sigma)

/-- `R^{H∖1} ≅ K × I_ℚ`。 -/
noncomputable def eK : ({b : H // b ≠ 1} → R) ≃ₗ[R] ↥K × ↥IQR :=
  (Submodule.prodEquivOfIsCompl _ _ CK_isCompl).symm.trans
    ((LinearEquiv.refl R ↥K).prodCongr eCK)

/-- `{b // b ≠ 1} ≃ Fin 8`。 -/
noncomputable def e8 : {b : H // b ≠ 1} ≃ Fin 8 :=
  Fintype.equivFinOfCardEq (by
    show Fintype.card {x : H | x ≠ 1} = 8
    rw [Set.card_ne_eq (1 : H), MH.card_H])


noncomputable def eH1 : ↥E ≃ₗ[R] (↥IQR × ↥K) × ℚ :=
  eE.trans (LinearEquiv.prodAssoc R ↥IQR ↥K ℚ).symm

noncomputable def eH2 := (LinearEquiv.prodComm R ↥IQR ↥K).prodCongr (LinearEquiv.refl R ℚ)

noncomputable def eH3 := eK.symm.prodCongr (LinearEquiv.refl R ℚ)

noncomputable def eH4 := (LinearEquiv.funCongrLeft R R e8.symm).prodCongr (LinearEquiv.refl R ℚ)

/-- **E ≅ (Fin 8 → R) × ℚ**（全 R-线性结构结论）。 -/
noncomputable def eStructIso : ↥E ≃ₗ[R] (Fin 8 → R) × ℚ :=
  eH1.trans (eH2.trans (eH3.trans eH4))


/-\! ## §5 主定理：`ker π_ℚ ≃ₗ[ℚ] (Fin 8 → R) × ℚ`（＋ H-等变加注）

经 `Φ` 把 §4 的 R-线性结构件搬到 `ker π_ℚ`（ℚ-线性）；`mainIso` = 主定理，
`mainIso_equivariant` = 与 `actFun`／目标标准 R-作用的相容（即 ℚ[H]-模同构的模型形）。 -/

theorem piStd_Phi (w : VQ) : piStd (Phi w) = MQ.piQ w := by
  show MQ.piQ (Phi.symm (Phi w)) = MQ.piQ w
  rw [LinearEquiv.symm_apply_apply]

theorem piStd_eq_piQ_symm (x : VQ) : piStd x = MQ.piQ (Phi.symm x) := rfl

/-- `ker π_ℚ ≅ E`（经 `Φ`；ℚ-线性）。 -/
noncomputable def eKer : ↥(LinearMap.ker MQ.piQ) ≃ₗ[ℚ] ↥E where
  toFun z := ⟨Phi z.1, by
    show piStd (Phi z.1) = 0
    rw [piStd_Phi]
    exact z.2⟩
  invFun x := ⟨Phi.symm x.1, by
    have hx : piStd x.1 = 0 := x.2
    show MQ.piQ (Phi.symm x.1) = 0
    rw [← piStd_eq_piQ_symm x.1]
    exact hx⟩
  left_inv z := Subtype.ext (LinearEquiv.symm_apply_apply Phi z.1)
  right_inv x := Subtype.ext (LinearEquiv.apply_symm_apply Phi x.1)
  map_add' z z' := Subtype.ext (map_add Phi z.1 z'.1)
  map_smul' c z := Subtype.ext (map_smul Phi c z.1)

/-- **主定理（ℚ-模型）**：`ker π_ℚ ≅ (Fin 8 → R) × ℚ`。 -/
noncomputable def eMain : ↥(LinearMap.ker MQ.piQ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ :=
  eKer.trans (eStructIso.restrictScalars ℚ)

theorem mainIso : Nonempty (↥(LinearMap.ker MQ.piQ) ≃ₗ[ℚ] (Fin 8 → R) × ℚ) :=
  ⟨eMain⟩

theorem actFun_mem_ker (g : H) (z : ↥(LinearMap.ker MQ.piQ)) :
    actFun g z.1 ∈ LinearMap.ker MQ.piQ := by
  rw [LinearMap.mem_ker, piQ_equivariant]
  have hz0 : MQ.piQ z.1 = 0 := z.2
  rw [hz0, mul_zero]

theorem eKer_equivariant (g : H) (z : ↥(LinearMap.ker MQ.piQ)) :
    eKer ⟨actFun g z.1, actFun_mem_ker g z⟩
      = MonoidAlgebra.single g (1 : ℚ) • (eKer z : ↥E) := by
  refine Subtype.ext ?_
  show Phi (actFun g z.1) = MonoidAlgebra.single g (1 : ℚ) • Phi z.1
  rw [Phi_equivariant]

/-- **H-等变加注**：主同构把 `actFun` 作用搬到目标的标准 R-作用。 -/
theorem mainIso_equivariant (g : H) (z : ↥(LinearMap.ker MQ.piQ)) :
    eMain ⟨actFun g z.1, actFun_mem_ker g z⟩
      = MonoidAlgebra.single g (1 : ℚ) • eMain z := by
  show eStructIso (eKer ⟨actFun g z.1, actFun_mem_ker g z⟩ : ↥E)
    = MonoidAlgebra.single g (1 : ℚ) • eStructIso (eKer z : ↥E)
  rw [eKer_equivariant]
  exact map_smul eStructIso (MonoidAlgebra.single g (1 : ℚ)) (eKer z : ↥E)

/-\! ## 公理闸门（全件；主定理 = `mainIso`，H-等变加注 = `mainIso_equivariant`） -/

#print axioms actFun_one_apply
#print axioms Phi_equivariant
#print axioms Phi_symm_equivariant
#print axioms Phi_apply_evec
#print axioms Psi_apply_evec
#print axioms piQ_equivariant
#print axioms piStd
#print axioms piStd_apply
#print axioms IQt_le_E
#print axioms augMul
#print axioms augRingHom
#print axioms ker_pi1
#print axioms range_sigma
#print axioms piStd_eq_sigma
#print axioms pi1_map_E
#print axioms compl_iso
#print axioms CE_isCompl
#print axioms eE
#print axioms CK_isCompl
#print axioms eCK
#print axioms eK
#print axioms eH1
#print axioms eStructIso
#print axioms eKer
#print axioms eMain
#print axioms mainIso
#print axioms mainIso_equivariant

end ABGV52.MI
