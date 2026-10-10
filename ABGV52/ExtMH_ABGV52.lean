/-
  ABGV-5.2 —— 论文 `prop:M_H-not-permutation` **主证明（Ext 路线）**：组装件

  论文锚点
  ========
    `raw/ABGV-5.2-resolution.tex:1560–1605`（⚠-tex-sourced，L12/L16）：
    设 `H = C_3 × C_3`、`M = M|_H`。增广短正合列 `0 → I[H] → Z[H] → Z → 0`
    的 `Hom_{ℤ[H]}(−,L)` 长正合列两端消没（`Z[H]` 射影）⟹ 连接同态
      `δ : Ext¹_{ℤ[H]}(I[H],L) → Ext²_{ℤ[H]}(ℤ,L) = coh²(H,L)`
    是同构。对两个 `L` 读数：
      (a) `L = M|_H`：`coh²(H,M|_H) ≅ C_9`（`C8` 的 `H2_MH_equiv_zmod9`）
          ⟹ `Ext¹(I[H],M|_H) ≅ C_9`；
      (b) 假设 `M|_H` 置换 ⟹（`prop:MH-char` ＋ `lem:perm-class`）
          `M|_H ≅ 8ℤ[H] ⊕ ℤ` ⟹ `Ext¹(I[H], 8ℤ[H]⊕ℤ) ≅ 0 ⊕ (C_3 × C_3)`
          （自由部 `coh²(H,ℤ[H]) = 0` 即 `C5`；平凡部 `coh²(H,ℤ) = C_3×C_3`
          即 `S2b`）。
    两读数矛盾（`C_9` 有 9 阶元而 `C_3 × C_3` 被 3 消没）⟹ `M|_H` 非置换格。

  本件构造（组装链）
  ================
    §1 `extOneIH_addEquiv_coh2`：复合桥（`ExtLES.extOneIH_addEquiv_extTwoTriv`
       ∘ `ExtBridge.extTwoTriv_addEquiv_coh2`）；
    §2 `extAddEquivOfIso`：沿 `Rep ℤ H` 同构搬运 `Ext` 第二变量（库内无成品，
       以 `Ext.mk₀`／`Ext.comp` 自建）；
    §3 读数 (a)：`extOneIH_M_H_addEquiv_zmod9 : Ext¹(I[H],M|_H) ≃+ ZMod 9`；
    §4 序障碍：`no_addEquiv_zmod9_prod`、`zmod9_not_three_killed`；
    §5 无条件形一 `M_H_not_permutation_via_ext`（借 `perm_exp`；主证明装配见 §11）；
    §6 读数 (b) 的末端读数：`extOneIH_TZ_addEquiv : Ext¹(I[H],ℤ) ≃+ Z/3 × Z/3`
       （复合桥 ＋ `S2b.H2_Z_equiv`）；
    §7 模型集侧：`modelPHRep = ℤ[ModelPH]`（`PC` 件）及自由部 `free8Rep = ℤ[Fin 8 × H]`；
       消没读数 `extOneIH_free8Rep_threeKilled`（自由部，近似论文 `C5` 位）与
       `extOneIH_modelPHRep_threeKilled`；
    §8 条件形主定理 `not_nonempty_iso_modelPHRep`：`M|_H ≅ ℤ[ModelPH]` ⟹ 矛盾
       （读数 (a) 沿同构搬运 ⟹ `Z/9` 被 3 消没，矛盾）；
    §9 双积拆分 `ℤ[ModelPH] ≅ 8ℤ[H] ⊞ ℤ`：`Finsupp` 系数分裂 ＋ 等变性
       （`modelPHIsoBiprod`）⟹ `extOneIH_modelPH_split`（`Ext.addEquivBiprod`）；
    §10 自由部消没（论文 `C5` 位，**全消没**）：Shapiro 同构
       `coindFree8Iso : ℤ[Fin 8 × H] ≅ coind_⊥^H(Fin 8 → ℤ)` ＋ `C7` 消没 ⟹
       `subsingleton_extOneIH_free8Rep`；
    §11 读数 (b) 完整形 `extOneIH_modelPH_addEquiv :
       Ext¹(I[H],ℤ[ModelPH]) ≃+ Z/3 × Z/3`（§9＋§10＋§7）与论文主证明的
       完整装配 `M_H_not_permutation_via_biprod`（`hw` 已由 `ExtMHUncond` 构造；
       无条件版 `M_H_not_permutation_main`）；
    §8（续）`M_H_not_permutation_via_modelPH`：把"假设链最后一环"隔离为显式假设
       （`prop:MH-char` ＋ `lem:perm-class` 的装配；该环已由 `ExtMHUncond` 闭合，见 §13）；
    §12 路线对照（含两 example 与接口核对）；§13 缺口登记（含 (i) 闭合记录）；
    §14 公理闸门。

  假设链（§8／§11 用）与论文链的差异（诚实登记；2026-10-10 按审查 A 精确化重写）
  =====================================================================
    论文 §(b) 的假设链为「`M|_H` 置换 ⟹ `M|_H ≅ 8ℤ[H] ⊕ ℤ`」＝
    `prop:MH-char`（`BR.bridge_MH_char`／`bridge_MH_char_equivariant`，ℚ-侧
    结构：`M|_H ⊗ ℚ ≅ 8ℚ[H] ⊕ ℚ`）＋ `lem:perm-class`（`PC.permClass`，
    入口 ℚ-侧：`Nonempty (ℚ[X] ≅ ℚ[ModelPH])`；出口 ℤ-侧）。本件中该环以显式
    假设 `hw` 隔离；本件交付时记「缺 `ℤ → ℚ` 换基一段胶水」，审查 A 精确化为
    **三段**：
      ① **换基**：`e₁`（`M|_H ≅ ℤ[X]`，由 `hP` 给出）沿 `−⊗[ℤ]ℚ` 换基，另有
         桥 `ℤ[X] ⊗ ℚ ≅ ℚ[X]`〔唯一字面意义的「换基」段；其存在由 `PC.permClass`
         停在 X-层引入——论文 `lem:perm-class` 是 P-层，不需要它〕；
      ② **打包**：把「裸 ℚ-线性同构 ＋ 等变引理」升级为货真价实的 `Rep ℚ H`
         同构（BR 侧无 `Rep` 对象，张量载体仅 SMul／DistribMulAction）；
      ③ **目标识别**：`(Fin 8 → ℚ[H]) × ℚ ≅ ℚ[ModelPH]`。
    **该环已闭合（2026-10-10，`ExtMHUncond_ABGV52`）**：`hasIso_modelPH_of_perm`
    显式构造（`bridgeRX`／`baseChangeE1`／`PhiQIso`／`splitQ`），主定理升级为
    无条件 `M_H_not_permutation_main`（见 §13(i)）。
    本件两条主定理的路线定位：
      * §5 `M_H_not_permutation_via_ext`：借 `S4.perm_exp`（论文
        `prop:perm-exponent`，即论文 **Second proof** 所用机制）关闭消没侧——
        无条件，但**不是**论文主证明（主证见 §11）；
      * §11 `M_H_not_permutation_via_biprod`：论文主证明的**逐环装配**
        （读数 (a) 沿 `hw` 给出的同构搬到 `ℤ[ModelPH]` 侧，与读数 (b)
        全形 `≃+ Z/3 × Z/3` 经 §4 序障碍矛盾）——**不用 `perm_exp`**；
        其 `hw` 现由 `ExtMHUncond_ABGV52` 构造 ⟹ 无条件版 `M_H_not_permutation_main`。
    与 `S5.M_H_not_permutation`（`Thm.not_exp3_of_iso_C9` 路线）相比，本件
    的**新增内容**是把论文主证明的载体层（`Ext¹(I[H],−)`、双积拆分、Shapiro
    消没、两读数矛盾）完整落成。
-/
import ABGV52.S5_ABGV52
import ABGV52.ExtLES_ABGV52
import ABGV52.ExtBridge_ABGV52
import ABGV52.S2b_ABGV52
import ABGV52.PC_ABGV52
import ABGV52.C7_ABGV52
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Group.PUnit

open CategoryTheory
open CategoryTheory.Abelian

namespace ABGV52

-- `ℤ` 上 `AddCommGroup.toIntModule` 与 `Rep.hV2` 争用 `Module ℤ ↥X`（同 C4/C8 处理）。
attribute [local instance 1500] Rep.hV2

-- （2026-10-10 审查 B：`haveI` 触发 style linter；同 ExtBridge 先例关闭。）
set_option linter.style.haveILetI false

/-! ## 1. 复合桥：`Ext¹(I[H],−) ≃+ coh²(H,−)` -/

/-- **复合桥**：`Ext¹_{ℤ[H]}(I[H],A) ≃+ Ext²_{ℤ[H]}(ℤ,A) ≃+ coh²(H,A)`。
第一步 = 增广短正合列的长正合列连接同态（`ExtLES`），第二步 = Yoneda/柱分解桥
（`ExtBridge`）。本件全部读数都经此桥。 -/
noncomputable def extOneIH_addEquiv_coh2 (A : Rep ℤ H) :
    Ext I_H_rep A 1 ≃+ ↥(groupCohomology A 2) :=
  (extOneIH_addEquiv_extTwoTriv A).trans (extTwoTriv_addEquiv_coh2 A)

/-! ## 2. 沿同构搬运 `Ext` 第二变量 -/

section Transport

variable {A B : Rep ℤ H}

/-- **沿 `Rep ℤ H` 同构搬运 `Ext` 的第二变量**：`A ≅ B` ⟹ `Ext X A n ≃+ Ext X B n`。
用 `Ext.comp` 与 `Ext.mk₀` 双射组装（库内 `Ext.addEquivBiprod` 等只覆盖积/双积，
无一般同构搬运成品）。 -/
noncomputable def extAddEquivOfIso (e : A ≅ B) (X : Rep ℤ H) (n : ℕ) :
    Ext X A n ≃+ Ext X B n where
  toFun α := α.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun β := β.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv α := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Ext.comp_mk₀_id]
  right_inv β := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
      Ext.comp_mk₀_id]
  map_add' α₁ α₂ := by
    simp only [Ext.add_comp]

end Transport

/-- `Ext` 搬运的求值式（供下游按 `Ext` 元素改写）。 -/
lemma extAddEquivOfIso_apply {A B : Rep ℤ H} (e : A ≅ B) (X : Rep ℤ H) (n : ℕ)
    (α : Ext X A n) :
    extAddEquivOfIso e X n α = α.comp (Ext.mk₀ e.hom) (add_zero n) :=
  rfl

/-! ## 3. 读数 (a)：`Ext¹(I[H],M|_H) ≃+ Z/9` -/

/-- **读数 (a)**：`Ext¹_{ℤ[H]}(I[H],M|_H) ≃+ Z/9`（复合桥 ＋ `C8` 的
`H2_MH_equiv_zmod9`）。 -/
noncomputable def extOneIH_M_H_addEquiv_zmod9 :
    Ext I_H_rep M_H_rep 1 ≃+ ZMod 9 :=
  (extOneIH_addEquiv_coh2 M_H_rep).trans H2_MH_equiv_zmod9.toAddEquiv

/-! ## 4. 序障碍：`Z/9 ≇ Z/3 × Z/3` -/

/-- `Z/9` 与 `Z/3 × Z/3` 之间不存在加法群同构（`Z/9` 有 9 阶元，而
`Z/3 × Z/3` 被 3 消没）。 -/
theorem no_addEquiv_zmod9_prod : ¬ Nonempty (ZMod 9 ≃+ (ZMod 3 × ZMod 3)) := by
  rintro ⟨e⟩
  have hkill : ∀ y : ZMod 3 × ZMod 3, (3 : ℤ) • y = 0 := by
    intro y
    have h1 : (3 : ℤ) • y.1 = 0 := by
      show ((3 : ℕ) : ℤ) • y.1 = 0
      rw [natCast_zsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have h2 : (3 : ℤ) • y.2 = 0 := by
      show ((3 : ℕ) : ℤ) • y.2 = 0
      rw [natCast_zsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    exact Prod.ext h1 h2
  have h' : e.symm ((3 : ℤ) • e 1) = e.symm 0 := congrArg e.symm (hkill (e 1))
  rw [map_zsmul, map_zero, e.symm_apply_apply] at h'
  have h5 : (3 : ℤ) • (1 : ZMod 9) = 3 := by decide
  rw [h5] at h'
  exact (by decide : (3 : ZMod 9) ≠ 0) h'

/-- `Z/9` 不被 3 消没（取元素 `1`）。 -/
theorem zmod9_not_three_killed : ¬ (∀ x : ZMod 9, (3 : ℤ) • x = 0) := by
  intro h
  have h1 : (3 : ZMod 9) ≠ 0 := by decide
  have h2 : (3 : ℤ) • (1 : ZMod 9) = 3 := by decide
  have h3 := h 1
  rw [h2] at h3
  exact h1 h3

/-! ## 5. 无条件形一：Ext 载体 ＋ `perm_exp`（＝论文 Second proof 的机制；
   论文主证明的装配见 §11，其 `hw` 现由 `ExtMHUncond_ABGV52` 构造——见 §13(i)） -/

/-- **`M|_H` 非置换格——无条件形一（Ext 载体）**：消没侧借 `S4.perm_exp`
（＝论文 **Second proof** 的机制；**不是**论文主证明的机制）：假设 `hP` 下读数 (a)
给出 `Ext¹(I[H],M|_H) ≅ Z/9`；`hP` 经 `perm_exp` 使 `coh²` 被 3 消没，经复合桥
搬进 `Ext¹(I[H],M|_H)` ⟹ `Z/9` 被 3 消没，与 `zmod9_not_three_killed` 矛盾。 -/
theorem M_H_not_permutation_via_ext : ¬ IsPermutationLattice M_H_rep := by
  intro hP
  have hkill : ∀ x : ↥(groupCohomology M_H_rep 2), (3 : ℤ) • x = 0 :=
    perm_exp M_H_rep hP
  have hkillExt : ∀ y : Ext I_H_rep M_H_rep 1, (3 : ℤ) • y = 0 := by
    intro y
    refine (extOneIH_addEquiv_coh2 M_H_rep).injective ?_
    rw [map_zsmul, map_zero]
    exact hkill _
  have hkill9 : ∀ x : ZMod 9, (3 : ℤ) • x = 0 := by
    intro x
    have h := hkillExt ((extOneIH_M_H_addEquiv_zmod9).symm x)
    have h2 : (extOneIH_M_H_addEquiv_zmod9).symm ((3 : ℤ) • x) = 0 := by
      rw [map_zsmul]
      exact h
    exact (extOneIH_M_H_addEquiv_zmod9).symm.injective (by rw [h2, map_zero])
  exact zmod9_not_three_killed hkill9

/-! ## 6. 读数 (b) 的末端读数：平凡部 `Ext¹(I[H],ℤ) ≃+ Z/3 × Z/3` -/

/-- **`Ext¹(I[H],ℤ) ≃+ Z/3 × Z/3`**：复合桥 ＋ `S2b.H2_Z_equiv`（论文 `lem:H2-Z`）。
对应论文读数 (b) 中"平凡部 `coh²(H,ℤ) = C₃ × C₃`"那一步（论文 `lem:H2-Z`；Lean 实例：`S2b`）。 -/
noncomputable def extOneIH_TZ_addEquiv :
    Ext I_H_rep (TZ H) 1 ≃+ (ZMod 3 × ZMod 3) :=
  (extOneIH_addEquiv_coh2 (TZ H)).trans H2_Z_equiv.toAddEquiv

/-- 沿复合桥搬运"`3` 消没"：`coh²` 侧 `3` 消没 ⟹ `Ext¹(I[H],−)` 侧 `3` 消没。 -/
theorem extOneIH_threeKilled_of_coh2 {A : Rep ℤ H} (h : Coh2ExpDvd3 A) :
    ∀ y : Ext I_H_rep A 1, (3 : ℤ) • y = 0 := by
  intro y
  refine (extOneIH_addEquiv_coh2 A).injective ?_
  rw [map_zsmul, map_zero]
  exact h _

/-! ## 7. 模型集侧：`ℤ[ModelPH]`、自由部与消没读数 -/

/-- 读数 (b) 的模型对象 `ℤ[ModelPH]`（`ModelPH = (Fin 8 × H) ⊔ 1`，`PC` 件）。 -/
noncomputable abbrev modelPHRep : Rep ℤ H := Rep.ofMulAction ℤ H PC.ModelPH

/-- 论文的"自由部" `8ℤ[H]`：置换模 `ℤ[Fin 8 × H]`。 -/
noncomputable abbrev free8Rep : Rep ℤ H := Rep.ofMulAction ℤ H (Fin 8 × H)

/-- 论文的"平凡部" `ℤ`：单点集的置换模 `ℤ[PUnit]`。 -/
noncomputable abbrev punitRep : Rep ℤ H := Rep.ofMulAction ℤ H PUnit

/-- `8ℤ[H]` 是置换格（`X = Fin 8 × H`）。 -/
theorem free8Rep_perm : IsPermutationLattice free8Rep :=
  ⟨Fin 8 × H, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- `ℤ[ModelPH]` 是置换格（`X = ModelPH`）。 -/
theorem modelPHRep_perm : IsPermutationLattice modelPHRep :=
  ⟨PC.ModelPH, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- 自由部 `3` 消没（`S4.perm_exp` 应用于 `ℤ[Fin 8 × H]`）。
**与论文的差异**：论文此处用 `C5`（`coh²(H,ℤ[H]) = 0`，Shapiro）得到**消没**；
本件取 `perm_exp` 得 **`3` 消没**——对矛盾足够（全消没形见 §10
`subsingleton_extOneIH_free8Rep`；缺口登记见 §13）。 -/
theorem free8Rep_threeKilled : Coh2ExpDvd3 free8Rep :=
  perm_exp free8Rep free8Rep_perm

/-- 模型集侧 `coh²` 被 `3` 消没。 -/
theorem modelPHRep_threeKilled : Coh2ExpDvd3 modelPHRep :=
  perm_exp modelPHRep modelPHRep_perm

/-- `Ext¹(I[H], 8ℤ[H])` 被 `3` 消没（论文此处置 `0`；全消没形见 §10
`subsingleton_extOneIH_free8Rep`）。 -/
theorem extOneIH_free8Rep_threeKilled :
    ∀ y : Ext I_H_rep free8Rep 1, (3 : ℤ) • y = 0 :=
  extOneIH_threeKilled_of_coh2 free8Rep_threeKilled

/-- `Ext¹(I[H], ℤ[ModelPH])` 被 `3` 消没（读数 (b) 的消没侧，条件形）。 -/
theorem extOneIH_modelPHRep_threeKilled :
    ∀ y : Ext I_H_rep modelPHRep 1, (3 : ℤ) • y = 0 :=
  extOneIH_threeKilled_of_coh2 modelPHRep_threeKilled

/-- 平凡部读数 `Ext¹(I[H], ℤ[PUnit]) ≃+ Z/3 × Z/3`：先沿
`ofMulActionSubsingletonIsoTrivial`（`PUnit` 单点 ⟹ 平凡表示）搬回 `ℤ`，再用 §6。 -/
noncomputable def extOneIH_punitRep_addEquiv :
    Ext I_H_rep punitRep 1 ≃+ (ZMod 3 × ZMod 3) :=
  (extAddEquivOfIso (Rep.ofMulActionSubsingletonIsoTrivial (k := ℤ) (G := H) PUnit)
    I_H_rep 1).trans extOneIH_TZ_addEquiv

/-! ## 8. 条件形主定理：`M|_H ≅ ℤ[ModelPH]` ⟹ 矛盾 -/

/-- **条件形**：若 `M|_H ≅ ℤ[ModelPH]`（论文假设链 `prop:MH-char` ＋ `lem:perm-class`
的末端结论），则矛盾——读数 (a) 沿同构搬到 `ℤ[ModelPH]` 侧给出
`Ext¹(I[H],ℤ[ModelPH]) ≅ Z/9`（`Z/9` 不被 3 消没），而该群又被 3 消没（§7）。 -/
theorem not_nonempty_iso_modelPHRep (h : Nonempty (M_H_rep ≅ modelPHRep)) : False := by
  obtain ⟨e⟩ := h
  have h9 : Nonempty (Ext I_H_rep modelPHRep 1 ≃+ ZMod 9) :=
    ⟨(extAddEquivOfIso e I_H_rep 1).symm.trans extOneIH_M_H_addEquiv_zmod9⟩
  obtain ⟨Φ⟩ := h9
  have hkill9 : ∀ x : ZMod 9, (3 : ℤ) • x = 0 := by
    intro x
    have h2 : Φ.symm ((3 : ℤ) • x) = 0 := by
      rw [map_zsmul]
      exact extOneIH_modelPHRep_threeKilled _
    exact Φ.symm.injective (by rw [h2, map_zero])
  exact zmod9_not_three_killed hkill9

/-- **假设链隔离形**：把论文证明"假设链最后一环"（`prop:MH-char` ＋ `lem:perm-class`
的装配：`M|_H` 置换 ⟹ `M|_H ≅ ℤ[ModelPH]`）取作显式假设，则末段闭合为
`¬ IsPermutationLattice M_H_rep`。该假设的**接线缺口**见 §13。 -/
theorem M_H_not_permutation_via_modelPH
    (hw : IsPermutationLattice M_H_rep → Nonempty (M_H_rep ≅ modelPHRep)) :
    ¬ IsPermutationLattice M_H_rep :=
  fun hP => not_nonempty_iso_modelPHRep (hw hP)

/-! ## 9. 双积拆分：`ℤ[ModelPH] ≅ 8ℤ[H] ⊞ ℤ`（`Ext.addEquivBiprod` 入口） -/

section SplitModelPH

/-- 乘积表示的显式承载：`8ℤ[H] × ℤ`（`free8Rep ⊞ punitRep` 的显式化）。 -/
noncomputable abbrev freeProdRep : Rep ℤ H := Rep.of (free8Rep.ρ.prod punitRep.ρ)

/-- **拆分线性同构**：`ℤ[ModelPH] ≅ₗ 8ℤ[H] × ℤ`（沿 `Sum` 分裂系数）。 -/
noncomputable def modelPHSplitLE : modelPHRep.V ≃ₗ[ℤ] freeProdRep.V :=
  (MonoidAlgebra.coeffLinearEquiv ℤ : modelPHRep.V ≃ₗ[ℤ] PC.ModelPH →₀ ℤ).trans <|
    ((Finsupp.sumFinsuppLEquivProdFinsupp ℤ :
        (PC.ModelPH →₀ ℤ) ≃ₗ[ℤ] ((Fin 8 × H) →₀ ℤ) × (PUnit →₀ ℤ)).trans <|
      ((MonoidAlgebra.coeffLinearEquiv ℤ :
          MonoidAlgebra ℤ (Fin 8 × H) ≃ₗ[ℤ] (Fin 8 × H) →₀ ℤ).symm.prodCongr
        (MonoidAlgebra.coeffLinearEquiv ℤ :
          MonoidAlgebra ℤ PUnit ≃ₗ[ℤ] PUnit →₀ ℤ).symm))

private lemma prodSplit_single_inl (p : Fin 8 × H) (r : ℤ) :
    (Finsupp.sumFinsuppLEquivProdFinsupp ℤ
        (Finsupp.single (Sum.inl p) r : PC.ModelPH →₀ ℤ))
      = (Finsupp.single p r, 0) := by
  refine Prod.ext ?_ ?_
  · refine Finsupp.ext fun q => ?_
    rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : q = p <;> simp [h]
  · refine Finsupp.ext fun u => ?_
    rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]
    rw [if_neg (fun h => by cases h)]
    rfl

private lemma prodSplit_single_inr (u : PUnit) (r : ℤ) :
    (Finsupp.sumFinsuppLEquivProdFinsupp ℤ
        (Finsupp.single (Sum.inr u) r : PC.ModelPH →₀ ℤ))
      = (0, Finsupp.single u r) := by
  refine Prod.ext ?_ ?_
  · refine Finsupp.ext fun q => ?_
    rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]
    rw [if_neg (fun h => by cases h)]
    rfl
  · refine Finsupp.ext fun u' => ?_
    rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : u' = u <;> simp [h]

/-- 拆分在自由部单点上的取值。 -/
lemma modelPHSplitLE_single_inl (p : Fin 8 × H) (r : ℤ) :
    modelPHSplitLE (MonoidAlgebra.single (Sum.inl p) r)
      = (MonoidAlgebra.single p r, 0) := by
  rw [modelPHSplitLE, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, prodSplit_single_inl,
    MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.coeffLinearEquiv_symm_apply]
  rfl

/-- 拆分在平凡部单点上的取值。 -/
lemma modelPHSplitLE_single_inr (u : PUnit) (r : ℤ) :
    modelPHSplitLE (MonoidAlgebra.single (Sum.inr u) r)
      = (0, MonoidAlgebra.single u r) := by
  rw [modelPHSplitLE, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, prodSplit_single_inr,
    MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.coeffLinearEquiv_symm_apply]
  rfl

lemma modelPHRep_rho_single (g : H) (m : PC.ModelPH) (r : ℤ) :
    (modelPHRep.ρ g) (MonoidAlgebra.single m r) = MonoidAlgebra.single (g • m) r := by
  change ((Representation.ofMulAction ℤ H PC.ModelPH) g) (MonoidAlgebra.single m r)
      = MonoidAlgebra.single (g • m) r
  rw [Representation.ofMulAction_single]

/-- 自由部单点上的显式作用（`Sum.inl` 支）。 -/
lemma modelPHRep_rho_single_inl (g : H) (p : Fin 8 × H) (r : ℤ) :
    (modelPHRep.ρ g) (MonoidAlgebra.single (Sum.inl p) r)
      = MonoidAlgebra.single (Sum.inl (g • p)) r := by
  rw [modelPHRep_rho_single]
  rfl

/-- 平凡部单点上的显式作用（`Sum.inr` 支）。 -/
lemma modelPHRep_rho_single_inr (g : H) (u : PUnit) (r : ℤ) :
    (modelPHRep.ρ g) (MonoidAlgebra.single (Sum.inr u) r)
      = MonoidAlgebra.single (Sum.inr u) r := by
  rw [modelPHRep_rho_single]
  rfl

lemma free8Rep_rho_single (g : H) (p : Fin 8 × H) (r : ℤ) :
    (free8Rep.ρ g) (MonoidAlgebra.single p r) = MonoidAlgebra.single (g • p) r := by
  change ((Representation.ofMulAction ℤ H (Fin 8 × H)) g) (MonoidAlgebra.single p r)
      = MonoidAlgebra.single (g • p) r
  rw [Representation.ofMulAction_single]

lemma punitRep_rho_single (g : H) (u : PUnit) (r : ℤ) :
    (punitRep.ρ g) (MonoidAlgebra.single u r) = MonoidAlgebra.single (g • u) r := by
  change ((Representation.ofMulAction ℤ H PUnit) g) (MonoidAlgebra.single u r)
      = MonoidAlgebra.single (g • u) r
  rw [Representation.ofMulAction_single]

lemma punitRep_rho_single_self (g : H) (u : PUnit) (r : ℤ) :
    (punitRep.ρ g) (MonoidAlgebra.single u r) = MonoidAlgebra.single u r := by
  rw [punitRep_rho_single, show g • u = u from Subsingleton.elim _ _]

lemma freeProdRep_rho_apply (g : H) (a : free8Rep.V) (b : punitRep.V) :
    (freeProdRep.ρ g) (a, b) = ((free8Rep.ρ g) a, (punitRep.ρ g) b) := rfl

/-- **逐点等变式**：拆分与两侧作用相容（单点展开）。 -/
lemma modelPHSplitLE_act (g : H) (w : modelPHRep.V) :
    modelPHSplitLE ((modelPHRep.ρ g) w)
      = (freeProdRep.ρ g) (modelPHSplitLE w) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    rcases m with p | u
    · rw [modelPHRep_rho_single_inl g p r]
      nth_rewrite 1 [modelPHSplitLE_single_inl (g • p) r]
      nth_rewrite 1 [modelPHSplitLE_single_inl p r]
      rw [freeProdRep_rho_apply, free8Rep_rho_single]
      exact Prod.ext rfl (map_zero (punitRep.ρ g)).symm
    · rw [modelPHRep_rho_single_inr g u r]
      nth_rewrite 1 [modelPHSplitLE_single_inr u r]
      nth_rewrite 1 [modelPHSplitLE_single_inr u r]
      rw [freeProdRep_rho_apply, punitRep_rho_single_self]
      exact Prod.ext (map_zero (free8Rep.ρ g)).symm rfl

/-- **等变式**：拆分与两侧作用相容（线性映射级）。 -/
lemma modelPHSplit_intertwining (g : H) :
    modelPHSplitLE.toLinearMap ∘ₗ (modelPHRep.ρ g)
      = (freeProdRep.ρ g) ∘ₗ modelPHSplitLE.toLinearMap := by
  refine LinearMap.ext fun w => ?_
  exact modelPHSplitLE_act g w

/-- **拆分同构**：`ℤ[ModelPH] ≅ 8ℤ[H] × ℤ`（表示级）。 -/
noncomputable def modelPHSplitEquiv : modelPHRep.ρ.Equiv freeProdRep.ρ :=
  Representation.Equiv.mk modelPHSplitLE modelPHSplit_intertwining

/-- **拆分同构**（`Rep` 级）：`ℤ[ModelPH] ≅ 8ℤ[H] × ℤ`。 -/
noncomputable def modelPHIsoFreeProd : modelPHRep ≅ freeProdRep :=
  Rep.mkIso modelPHSplitEquiv

/-- **双积同构**：`8ℤ[H] × ℤ ≅ 8ℤ[H] ⊞ ℤ`（`biprod.uniqueUpToIso`）。

双锥按 mathlib `Rep` 的双积实例同款显式给出（投影/含入为 `IntertwiningMap.fst` 等）；
全和恒等式 `inl ≫ fst + inr ≫ snd = id` 由 `IntertwiningMap.coprod_inl_inr` 关闭——
故此处**不打包为独立 def**（`change`/`simp` 需看到原始项，`def` 的 delta 展开不被 `simp` 执行）。 -/
noncomputable def freeProdIsoBiprod : freeProdRep ≅ (free8Rep ⊞ punitRep) :=
  Limits.biprod.uniqueUpToIso free8Rep punitRep <|
    Limits.isBinaryBilimitOfTotal
      { pt := freeProdRep
        fst := Rep.ofHom (.fst ℤ free8Rep.ρ punitRep.ρ)
        snd := Rep.ofHom (.snd ℤ free8Rep.ρ punitRep.ρ)
        inl := Rep.ofHom (.inl ℤ free8Rep.ρ punitRep.ρ)
        inr := Rep.ofHom (.inr ℤ free8Rep.ρ punitRep.ρ)
        inl_fst := by ext1; simp
        inl_snd := by ext1; simp [Rep.zero_hom]
        inr_fst := by ext1; simp [Rep.zero_hom]
        inr_snd := by ext1; simp }
      (by ext1; simp [Rep.add_hom])

/-- **`ModelPH` 表示 ≅ 双积**：`ℤ[ModelPH] ≅ 8ℤ[H] ⊞ ℤ`。 -/
noncomputable def modelPHIsoBiprod : modelPHRep ≅ (free8Rep ⊞ punitRep) :=
  modelPHIsoFreeProd.trans freeProdIsoBiprod

/-- **Ext¹ 拆分**：`Ext¹(I[H],ℤ[ModelPH]) ≃+ Ext¹(I[H],8ℤ[H]) × Ext¹(I[H],ℤ)`。 -/
noncomputable def extOneIH_modelPH_split :
    Ext I_H_rep modelPHRep 1 ≃+ (Ext I_H_rep free8Rep 1 × Ext I_H_rep punitRep 1) :=
  (extAddEquivOfIso modelPHIsoBiprod I_H_rep 1).trans Ext.addEquivBiprod

end SplitModelPH

/-! ## 10. 自由部消没（论文 `C5` 位，全消没）：`ℤ[Fin 8 × H] ≅ coind_⊥^H(Fin 8 → ℤ)` -/

section Free8Vanishing

/-- `⊥ : Subgroup H` 上的平凡表示（载体 `Fin 8 → ℤ`）。 -/
noncomputable abbrev triv8Bot : Rep ℤ ↥(⊥ : Subgroup H) :=
  Rep.trivial ℤ ↥(⊥ : Subgroup H) (Fin 8 → ℤ)

/-- `coind_⊥^H(Fin 8 → ℤ)`：函数 `H → (Fin 8 → ℤ)`，按**右平移**作用。 -/
noncomputable abbrev coindFree8 : Rep ℤ H := Rep.coind (⊥ : Subgroup H).subtype triv8Bot

lemma coindFree8_apply (h : H) (z : coindFree8.V) (x : H) :
    (coindFree8.ρ h z).1 x = z.1 (x * h) := by
  change (((Representation.coind (⊥ : Subgroup H).subtype triv8Bot.ρ) h) z).1 x
      = z.1 (x * h)
  rw [Representation.coind_apply]
  rfl

/-- 写子：`Φ(z) = Σ_x Σ_i z(x)(i) · single (i, x⁻¹) 1`。 -/
noncomputable def phiFree8Fun (z : coindFree8.V) : MonoidAlgebra ℤ (Fin 8 × H) :=
  ∑ x : H, ∑ i : Fin 8, (z.1 x i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ)

/-- 逆写子：`Ψ(w) = ((x, i) ↦ w.coeff (i, x⁻¹))`。 -/
noncomputable def psiFree8Fun (w : MonoidAlgebra ℤ (Fin 8 × H)) : coindFree8.V :=
  ⟨fun x i => w.coeff (i, x⁻¹), by
    intro g h
    have hg : (⊥ : Subgroup H).subtype g = 1 := by
      have : g = 1 := Subsingleton.elim g 1
      rw [this]
      rfl
    rw [hg, one_mul]
    rfl⟩

/-- **系数公式**：`(Φ z).coeff (i, y⁻¹) = z(y)(i)`。 -/
private lemma coeff_phiFree8 (z : coindFree8.V) (i : Fin 8) (y : H) :
    (phiFree8Fun z).coeff (i, y⁻¹) = z.1 y i := by
  rw [phiFree8Fun, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single y]
  · rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro j _ hj
      rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne (fun hij => hj (congrArg Prod.fst hij).symm), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · intro x _ hx
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne ?_, smul_zero]
    intro hpair
    exact hx (inv_injective (congrArg Prod.snd hpair).symm)
  · intro hy
    exact absurd (Finset.mem_univ y) hy

/-- `c • single p 1 = single p c`（`ℤ[Fin 8 × H]` 版）。 -/
private lemma smul_single_one_free8 (c : ℤ) (p : Fin 8 × H) :
    c • MonoidAlgebra.single p (1 : ℤ) = MonoidAlgebra.single p c := by
  simp

/-- `w = Σ_p (w.coeff p) • single p 1`（`ℤ[Fin 8 × H]` 版，同 `C2` 的全集展开）。 -/
private lemma eq_sum_coeff_smul_single_free8 (w : MonoidAlgebra ℤ (Fin 8 × H)) :
    w = ∑ p : Fin 8 × H, (w.coeff p) • MonoidAlgebra.single p (1 : ℤ) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single w]
  rw [Finsupp.sum_fintype w.coeff (fun p c => MonoidAlgebra.single p c)
      (by intro p; simp)]
  exact Finset.sum_congr rfl (fun p _ => (smul_single_one_free8 (w.coeff p) p).symm)

/-- `Φ ∘ Ψ = id`（`x ↦ x⁻¹` 重指标 ＋ 展平）。 -/
private lemma phiFree8_psiFree8 (w : MonoidAlgebra ℤ (Fin 8 × H)) :
    phiFree8Fun (psiFree8Fun w) = w := by
  have h1 : phiFree8Fun (psiFree8Fun w)
      = ∑ p : Fin 8 × H, (w.coeff p) • MonoidAlgebra.single p (1 : ℤ) := by
    have h2 : phiFree8Fun (psiFree8Fun w)
        = ∑ y : H, ∑ i : Fin 8, (w.coeff (i, y)) • MonoidAlgebra.single (i, y) (1 : ℤ) := by
      simp only [phiFree8Fun, psiFree8Fun]
      exact Equiv.sum_comp (Equiv.inv H)
        (fun y : H => ∑ i : Fin 8, (w.coeff (i, y)) • MonoidAlgebra.single (i, y) (1 : ℤ))
    have h3 : (∑ y : H, ∑ i : Fin 8, (w.coeff (i, y)) • MonoidAlgebra.single (i, y) (1 : ℤ))
        = ∑ p : Fin 8 × H, (w.coeff p) • MonoidAlgebra.single p (1 : ℤ) := by
      rw [Finset.sum_comm]
      simpa using (Fintype.sum_prod_type
        (fun p : Fin 8 × H => (w.coeff p) • MonoidAlgebra.single p (1 : ℤ))).symm
    rw [h2, h3]
  rw [h1, ← eq_sum_coeff_smul_single_free8 w]

/-- `Ψ ∘ Φ = id`（系数公式）。 -/
private lemma psiFree8_phiFree8 (z : coindFree8.V) : psiFree8Fun (phiFree8Fun z) = z := by
  refine Subtype.ext (funext fun x => funext fun i => ?_)
  show (phiFree8Fun z).coeff (i, x⁻¹) = z.1 x i
  rw [coeff_phiFree8]

/-- **等变式**（核心）：右平移 ↦ 置换作用。 -/
lemma phiFree8_act (h : H) (z : coindFree8.V) :
    phiFree8Fun (coindFree8.ρ h z) = (free8Rep.ρ h) (phiFree8Fun z) := by
  have hstep : phiFree8Fun (coindFree8.ρ h z)
      = ∑ x : H, ∑ i : Fin 8, (z.1 (x * h) i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ) := by
    simp only [phiFree8Fun]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ =>
      by rw [coindFree8_apply]
  have hreindex : (∑ x : H, ∑ i : Fin 8, (z.1 (x * h) i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ))
      = ∑ b : H, ∑ i : Fin 8, (z.1 b i) • MonoidAlgebra.single (i, h * b⁻¹) (1 : ℤ) := by
    have h1 := Equiv.sum_comp (Equiv.mulRight h)
      (fun b : H => ∑ i : Fin 8, (z.1 b i) • MonoidAlgebra.single (i, h * b⁻¹) (1 : ℤ))
    simpa [mul_assoc] using h1
  rw [hstep, hreindex, phiFree8Fun]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, free8Rep_rho_single]
  rfl

/-- 线性等价：`coind_⊥^H(Fin 8 → ℤ) ≅ ℤ[Fin 8 × H]`。 -/
noncomputable def phiFree8LE : coindFree8.V ≃ₗ[ℤ] free8Rep.V where
  toFun := phiFree8Fun
  invFun := psiFree8Fun
  left_inv := psiFree8_phiFree8
  right_inv := phiFree8_psiFree8
  map_add' z₁ z₂ := by
    change (∑ x : H, ∑ i : Fin 8, (z₁.1 x i + z₂.1 x i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ))
      = (∑ x : H, ∑ i : Fin 8, (z₁.1 x i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ))
        + ∑ x : H, ∑ i : Fin 8, (z₂.1 x i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul]
  map_smul' m z := by
    change (∑ x : H, ∑ i : Fin 8, (m • z.1 x i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ))
      = m • ∑ x : H, ∑ i : Fin 8, (z.1 x i) • MonoidAlgebra.single (i, x⁻¹) (1 : ℤ)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [smul_smul, smul_eq_mul]

/-- **等变式**（线性映射级）。 -/
lemma phiFree8_intertwining (h : H) :
    phiFree8LE.toLinearMap ∘ₗ (coindFree8.ρ h)
      = (free8Rep.ρ h) ∘ₗ phiFree8LE.toLinearMap := by
  refine LinearMap.ext fun z => ?_
  show phiFree8Fun (coindFree8.ρ h z) = (free8Rep.ρ h) (phiFree8Fun z)
  exact phiFree8_act h z

/-- **`coind_⊥^H(Fin 8 → ℤ) ≅ ℤ[Fin 8 × H]`**（逆转置 ＋ 单点展开）。 -/
noncomputable def coindFree8Iso : coindFree8 ≅ free8Rep :=
  Rep.mkIso (Representation.Equiv.mk phiFree8LE phiFree8_intertwining)

/-- **`H^{n+1}(H, ℤ[Fin 8 × H]) = 0`**（Shapiro ＋ 同构传递；`C7`）。 -/
theorem isZero_groupCohomology_free8Rep (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology free8Rep (n + 1)) :=
  (isZero_groupCohomology_coind triv8Bot n).of_iso (cohIsoOfIso coindFree8Iso (n + 1)).symm

/-- `H^2(H, ℤ[Fin 8 × H])` 的子单性（＝ 消没）。 -/
theorem subsingleton_groupCohomology_free8Rep :
    Subsingleton ↥(groupCohomology free8Rep 2) :=
  (ModuleCat.isZero_of_iff_subsingleton (R := ℤ)
    (M := ↥(groupCohomology free8Rep 2))).mp (isZero_groupCohomology_free8Rep 1)

/-- **`Ext¹(I[H], 8ℤ[H]) = 0`**（沿复合桥搬运消没；对应论文 (b) 的自由部）。 -/
theorem subsingleton_extOneIH_free8Rep : Subsingleton (Ext I_H_rep free8Rep 1) := by
  haveI : Subsingleton ↥(groupCohomology free8Rep 2) := subsingleton_groupCohomology_free8Rep
  exact ⟨fun a b => (extOneIH_addEquiv_coh2 free8Rep).injective (Subsingleton.elim _ _)⟩

end Free8Vanishing

/-! ## 11. 读数 (b) 完整形与论文主证明的完整装配 -/

section ReadingB

/-- 消没因子在序积中的投影：`M × N ≃+ N`（当 `M` 子单）。 -/
noncomputable def dropSubsingletonProd (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    (h : Subsingleton M) : M × N ≃+ N where
  toFun p := p.2
  invFun n := (0, n)
  left_inv p := Prod.ext (h.allEq 0 p.1) rfl
  right_inv _n := rfl
  map_add' _p _q := rfl

/-- **读数 (b) 完整形**：`Ext¹(I[H], ℤ[ModelPH]) ≃+ Z/3 × Z/3`。
双积拆分 ＋ 自由部消没（§10）＋ 平凡部读数（`extOneIH_punitRep_addEquiv`）。 -/
noncomputable def extOneIH_modelPH_addEquiv :
    Ext I_H_rep modelPHRep 1 ≃+ (ZMod 3 × ZMod 3) :=
  (extOneIH_modelPH_split.trans
    (dropSubsingletonProd (Ext I_H_rep free8Rep 1) (Ext I_H_rep punitRep 1)
      subsingleton_extOneIH_free8Rep)).trans extOneIH_punitRep_addEquiv

/-- **假设链隔离形（论文主证明的完整装配）**：若 `M|_H` 置换链给出
`M|_H ≅ ℤ[ModelPH]`（论文 `prop:MH-char` ＋ `lem:perm-class` 的末端结论，
显式取作假设），则读数 (a) 搬到 `ℤ[ModelPH]` 侧给出 `Ext¹ ≅ Z/9`，
与读数 (b) `Ext¹ ≅ Z/3 × Z/3` 经序障碍 `no_addEquiv_zmod9_prod` 矛盾。 -/
theorem M_H_not_permutation_via_biprod
    (hw : IsPermutationLattice M_H_rep → Nonempty (M_H_rep ≅ modelPHRep)) :
    ¬ IsPermutationLattice M_H_rep := by
  intro hP
  obtain ⟨e⟩ := hw hP
  have h9 : Nonempty (Ext I_H_rep modelPHRep 1 ≃+ ZMod 9) :=
    ⟨(extAddEquivOfIso e I_H_rep 1).symm.trans extOneIH_M_H_addEquiv_zmod9⟩
  obtain ⟨Φ⟩ := h9
  exact no_addEquiv_zmod9_prod ⟨Φ.symm.trans extOneIH_modelPH_addEquiv⟩

end ReadingB

/-! ## 12. 路线对照 -/

/-- 两条路线的**同一性**核对：本件的主定理与 `S5.M_H_not_permutation`
（论文 `Second proof` 路线）结论相同。 -/
example : ¬ IsPermutationLattice M_H_rep := M_H_not_permutation_via_ext

/-- 论文主证明装配（§11）的**外部可用性核对**：同一目标是 §11 定理的直接实例。 -/
example (hw : IsPermutationLattice M_H_rep → Nonempty (M_H_rep ≅ modelPHRep)) :
    ¬ IsPermutationLattice M_H_rep := M_H_not_permutation_via_biprod hw

/-- 消没侧与本件读数的**接口核对**：置换假设下 `Ext¹(I[H],M|_H)` 被 3 消没
（即论文 (b) 读数 `0 ⊕ (C₃ × C₃)` 的消没部分）。 -/
example (hP : IsPermutationLattice M_H_rep) :
    ∀ y : Ext I_H_rep M_H_rep 1, (3 : ℤ) • y = 0 := by
  intro y
  refine (extOneIH_addEquiv_coh2 M_H_rep).injective ?_
  rw [map_zsmul, map_zero]
  exact perm_exp M_H_rep hP _

/-- (b) 侧消没读数与 (a) 侧序障碍的**接口核对**：`Ext¹(I[H],ℤ[ModelPH])` 被 3 消没，
而 `Ext¹(I[H],M|_H) ≅ Z/9` 有 3 阶元。 -/
example : ∃ (x : ZMod 9), (3 : ℤ) • x ≠ 0 := ⟨1, by decide⟩

/-! ## 13. 缺口登记与闭合记录（诚实） -/

/-
  本阶段（Ext¹ 波）相对论文证明的登记（均不涉及 sorry／自造公理）。
  2026-10-10 审查 A 精确化 → 同日 `ExtMHUncond_ABGV52` 闭合：

  (i) 假设链（`IsPermutationLattice M_H_rep` ⟹ `M_H_rep ≅ modelPHRep`）：
      **已闭合（2026-10-10，`ExtMHUncond_ABGV52`）**。链＝三段（审查 A 的
      精确化）：① 换基（`baseChangeE1`：`e₁` 沿 `−⊗[ℤ]ℚ`；另有桥
      `bridgeRX`：`ℤ[X] ⊗ ℚ ≅ ℚ[X]`）——唯一字面意义的「换基」段，其存在由
      `PC.permClass` 停在 X-层引入（论文 `lem:perm-class` 是 P-层，不需要它）；
      ② 打包（`PhiQIso`：`Rep ℚ H` 同构——BR 原仅提供裸 ℚ-线性同构 ＋
      等变引理，张量载体无 `Rep` 对象）；③ 目标识别（`splitQ`：
      `(Fin 8 → ℚ[H]) × ℚ ≅ ℚ[ModelPH]`）。`hasIso_modelPH_of_perm` 即显式
      构造的 `hw`；无条件主定理 `M_H_not_permutation_main`。
      方法论注记（L10①）：`hw` 的域在开发内可证为空（S5），其**可满足性**检查
      退化——闭合的价值在**构造本身**（预定链的显式落地），非可满足性。

  (ii) 自由部：**已按论文强度闭合**（§10）。论文直接在 `8ℤ[H]`／`ℤ[H]^{⊕9}`
      上计算，自由部零化用 `C5`（`coh²(H, ℤ[H]) = 0`，Shapiro）；本件改从
      平凡子群的 Shapiro（`isZero_groupCohomology_coind`）经
      `coindFree8Iso : ℤ[Fin 8 × H] ≅ coind_⊥^H(Fin 8 → ℤ)` 一次给出**全消没**
      `Ext¹(I[H], 8ℤ[H]) = 0`（`Subsingleton`，强于 §7 的 3 消没）——机制相同
      （Shapiro），仅实例化方式不同（免去 8 重记账）。原"3 消没"读数（§7）
      保留（`M_H_not_permutation_via_ext` 用）。

  (iii) 读数 (b) 完整形：**已闭合**（§9＋§11）。`extOneIH_modelPH_split`
      （`Ext.addEquivBiprod`）＋ 自由部消没（§10）＋ 平凡部读数
      （`extOneIH_punitRep_addEquiv`，§7）⟹
      `extOneIH_modelPH_addEquiv : Ext¹(I[H], ℤ[ModelPH]) ≃+ Z/3 × Z/3`，
      与论文 `Ext¹(I[H], 8ℤ[H] ⊕ ℤ) ≅ C₃ × C₃` 同形（乘积形：消没因子被
      `dropSubsingletonProd` 投影掉）。**登记（审查 A 的 F8）**：该"同形"的
      展示依赖模型识别 `ℤ[Fin 8 × H] ≅ (ℤ[H])^⊕8`（工作区未将该直和形定义
      为 `Rep ℤ H`，故未形式化；其对应角色在闭合链中由 ℚ-侧拆分 `splitQ`
      〔`ExtMHUncond`〕承担）。

  论文主证明（Ext 路线）的**逐环对照**：
      长正合列塌缩 ⟷ §1 复合桥；沿同构搬运（装配内部）⟷ §2 `extAddEquivOfIso`；
      读数 (a) ⟷ §3；读数 (b) 自由部 `= 0` ⟷ §10；
      读数 (b) 平凡部 `C₃ × C₃` ⟷ §6＋§7＋§9（双积拆分）；
      末端矛盾 `C₉ ≇ C₃ × C₃` ⟷ §4 序障碍 ＋ §11 装配；
      假设链闭环 ⟷ `ExtMHUncond_ABGV52`（`hasIso_modelPH_of_perm`）。
-/

/-! ## 14. 公理闸门 -/

#print axioms extOneIH_addEquiv_coh2
#print axioms extAddEquivOfIso
#print axioms extAddEquivOfIso_apply
#print axioms extOneIH_M_H_addEquiv_zmod9
#print axioms no_addEquiv_zmod9_prod
#print axioms zmod9_not_three_killed
#print axioms M_H_not_permutation_via_ext
#print axioms extOneIH_TZ_addEquiv
#print axioms extOneIH_threeKilled_of_coh2
#print axioms free8Rep_perm
#print axioms modelPHRep_perm
#print axioms free8Rep_threeKilled
#print axioms modelPHRep_threeKilled
#print axioms extOneIH_free8Rep_threeKilled
#print axioms extOneIH_modelPHRep_threeKilled
#print axioms extOneIH_punitRep_addEquiv
#print axioms not_nonempty_iso_modelPHRep
#print axioms M_H_not_permutation_via_modelPH
#print axioms modelPHSplitLE
#print axioms modelPHSplitLE_act
#print axioms modelPHIsoFreeProd
#print axioms freeProdIsoBiprod
#print axioms modelPHIsoBiprod
#print axioms extOneIH_modelPH_split
#print axioms phiFree8LE
#print axioms phiFree8_act
#print axioms coindFree8Iso
#print axioms isZero_groupCohomology_free8Rep
#print axioms subsingleton_groupCohomology_free8Rep
#print axioms subsingleton_extOneIH_free8Rep
#print axioms dropSubsingletonProd
#print axioms extOneIH_modelPH_addEquiv
#print axioms M_H_not_permutation_via_biprod

end ABGV52
