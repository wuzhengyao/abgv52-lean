/-
  文件：ExtMHUncond_ABGV52.lean（纯新增件；同轮对 `ExtMH_ABGV52.lean` 的更新仅为
  闭合登记注释，不涉代码）
  目的：闭合 `ExtMH_ABGV52.lean` §13 登记的**唯一未闭合环 (i)**——
  「`hP : IsPermutationLattice M_H_rep` ⟹ `M_H_rep ≅ 8·ℤ[H] ⊞ ℤ`」中，
  从 ℤ-侧 `Rep ℤ H` 同构到 `PC.permClass` 所需 ℚ-侧入口之间
  尚缺的「`ℤ → ℚ` 换基」胶水。由此 §11 的条件主定理
  `M_H_not_permutation_via_biprod (hw : …)` 升级为**无条件**形
  `M_H_not_permutation_main`（显式构造 `hw` 本身：`hasIso_modelPH_of_perm`）。
  **认识论注记（L10①）**：`hw` 的域在开发内可证为空（S5），故其**可满足性**检查退化——
  本件的价值在**构造本身**（预定链的显式落地），不得读作「装配可实现性」的证据；详见
  `ExtMH_ABGV52.lean` §13(i)。
  **审查状态（2026-10-10）**：C（链保真／防伪）＋ D（独立数学核）双过；读数可取用，
  使用限制——「无条件」＝除 `hP` 外无假设；数学承重 ＝ 本件胶水 ＋ `BR.eFinalLeft`
  （`prop:MH-char`）／`PC.permClass`（`lem:perm-class`）／Ext 装配的既有审查状态，
  不得读作本件独立证明 MH-char。

  逐环对应（本文件 ↔ 论文 / 既有件）：
  · 环 1（§B，`bridgeRX`）：换基桥 `ℚ ⊗[ℤ] ℤ[X] ≅ ℚ[X]`；等变式
    `bridgeRX_mapTensor` / `bridgeRX_symm_mapTensor`：与 `Rep.ofMulAction`
    两侧作用（ℤ-侧 `mapTensorX`、ℚ-侧 `ρ`）相容。
  · 环 2（§C，`baseChangeE1`）：把 `e₁ : M_H_rep ≅ ℤ[X]` 沿 `ℤ → ℚ` 换基为
    `ℚ ⊗[ℤ] ker π ≅ ℚ ⊗[ℤ] ℤ[X]`；等变式 `baseChangeE1_mapTensor` /
    `baseChangeE1_symm_mapTensor`（`BR.actTensorKer` ↔ `mapTensorX`）。
  · 环 3（§E 用、BR 既有件）：`BR.eFinalLeft : ℚ ⊗[ℤ] ker π ≅ (Fin 8 → ℚ[H]) × ℚ`
    —— 即论文 `prop:MH-char` 的 ℚ-侧结构结论；等变式
    `BR.eFinalLeft_equivariant`（`single g 1 •`）。
  · 环 4（§D，`splitQ`）：`ℚ[ModelPH] ≅ (Fin 8 → ℚ[H]) × ℚ`（沿 `Sum` 分裂系数）；
    等变式 `splitQ_smul` / `splitQ_symm_smul`。
  · 环 5（§E，`PhiQ` / `PhiQIso`）：把 1–4 装配为 `Rep ℚ H` 层同构
    `ℚ[X] ≅ ℚ[ModelPH]`（等变性由 `PhiQ_equivariant` 逐环复合给出）。
  · 环 6（既有 `PC.permClass`，论文 `lem:perm-class`）：该 ℚ-侧入口 ⟹
    ℤ-侧 `ℤ[X] ≅ ℤ[ModelPH]`；与 `e₁` 复合即 `hw`。

  偏离登记：
  · `PhiQIso` 前置 `set_option maxRecDepth 4000 in`——仅放宽类型推断的递归
    深度（默认 1000 时 `Rep.mkIso (Representation.Equiv.mk …)` 的隐式参数
    统一超限），无数学内容。
  · `attribute [local instance 1500] TensorProduct.instModule`（文件顶部 :53）——
    仅调局部实例优先级（ℤ-菱形；`BR_ABGV52.lean` §7 同款先例），不触陈述。
  · `DecidableEq X` 由 `Classical.decEq` 提供（非计算性；公理集已含
    `Classical.choice`）。
  · `prodSplit_single_inl / inr` 为文件内重定义（`ExtMH_ABGV52.lean` §9 的
    同名件是 `private`，不可跨文件引用）。
  · **无 `sorry`、无自造公理**；文件末尾每个顶层声明附 `#print axioms`。
  · 编译命令偏离：`scripts/lean_ws` 无 lakefile / lean-toolchain，字面命令
    `cd scripts/lean_ws && lake env lean ABGV52/ExtMHUncond_ABGV52.lean`
    在本环境不可用；实际路径 = 经 `~/mathlib4` 项目的 `lake env` ＋ `LEAN_PATH`
    注入（同 `abgv52-lean-crosscheck.py` :176–179 的驱动；另见同轮报告）。
-/

import Mathlib
import ABGV52.BR_ABGV52
import ABGV52.PC_ABGV52
import ABGV52.ExtMH_ABGV52

open TensorProduct
open CategoryTheory

namespace ABGV52.ExtMHUncond

open ABGV52

attribute [local instance 1500] TensorProduct.instModule

/-! ## A 部分：预备（系数公式与 `lmapDomain` 作用公式） -/

noncomputable def bridgeRAuxX (X : Type) [DecidableEq X] :
    ℚ ⊗[ℤ] MonoidAlgebra ℤ X ≃ₗ[ℚ] ℚ ⊗[ℤ] (X →₀ ℤ) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (MonoidAlgebra.coeffLinearEquiv ℤ)).extendScalarsOfIsLocalization
    (nonZeroDivisors ℤ) ℚ

noncomputable def bridgeRX (X : Type) [DecidableEq X] :
    ℚ ⊗[ℤ] MonoidAlgebra ℤ X ≃ₗ[ℚ] MonoidAlgebra ℚ X :=
  ((bridgeRAuxX X).trans (TensorProduct.finsuppScalarRight ℤ ℚ ℚ X)).trans
    (MonoidAlgebra.coeffLinearEquiv ℚ).symm

lemma bridgeRX_tmul_coeff (X : Type) [DecidableEq X] (a : ℚ) (p : MonoidAlgebra ℤ X) (i : X) :
    (bridgeRX X (a ⊗ₜ[ℤ] p)).coeff i = p.coeff i • a := by
  show (MonoidAlgebra.coeffLinearEquiv ℚ) (bridgeRX X (a ⊗ₜ[ℤ] p)) i = p.coeff i • a
  have hL : (MonoidAlgebra.coeffLinearEquiv ℚ) (bridgeRX X (a ⊗ₜ[ℤ] p))
      = TensorProduct.finsuppScalarRight ℤ ℚ ℚ X
          (bridgeRAuxX X (a ⊗ₜ[ℤ] p)) := by
    rw [bridgeRX, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  have hA : bridgeRAuxX X (a ⊗ₜ[ℤ] p)
      = a ⊗ₜ[ℤ] (MonoidAlgebra.coeffLinearEquiv ℤ) p := by
    show (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (MonoidAlgebra.coeffLinearEquiv ℤ))
        (a ⊗ₜ[ℤ] p) = a ⊗ₜ[ℤ] (MonoidAlgebra.coeffLinearEquiv ℤ) p
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [hL, hA, TensorProduct.finsuppScalarRight_apply_tmul_apply,
    MonoidAlgebra.coeffLinearEquiv_apply]

lemma lmapDomain_smul_apply_smul (X : Type) [DecidableEq X] [MulAction H X]
    {A : Type} [Semiring A] (x : H) (f : X →₀ A) (y : X) :
    (Finsupp.lmapDomain A A (fun z : X => x • z) f) y = f (x⁻¹ • y) := by
  rw [Finsupp.lmapDomain_apply]
  have hinj : Function.Injective (fun z : X => x • z) := by
    intro a b hab
    calc a = x⁻¹ • (x • a) := (inv_smul_smul x a).symm
      _ = x⁻¹ • (x • b) := congrArg (fun z : X => x⁻¹ • z) hab
      _ = b := inv_smul_smul x b
  have h := Finsupp.mapDomain_apply hinj f (x⁻¹ • y)
  simpa only [smul_inv_smul] using h

lemma coeff_rho_Q (X : Type) [MulAction H X] (g : H) (w : MonoidAlgebra ℚ X) :
    ((Rep.ofMulAction ℚ H X).ρ g w).coeff
      = Finsupp.lmapDomain ℚ ℚ (fun z : X => g • z) w.coeff := by
  have h := PC.coeff_rho X g w
  simpa only [MonoidAlgebra.coeffLinearEquiv_apply] using h

/-! ## B 部分：换基桥 `ℚ ⊗[ℤ] ℤ[X] ≅ ℚ[X]`（对任意 `X`）及其等变性 -/

noncomputable def mapTensorX (X : Type) [MulAction H X] (g : H) :
    (ℚ ⊗[ℤ] MonoidAlgebra ℤ X) →ₗ[ℤ] (ℚ ⊗[ℤ] MonoidAlgebra ℤ X) :=
  TensorProduct.map LinearMap.id ((Rep.ofMulAction ℤ H X).ρ g)

lemma mapTensorX_tmul (X : Type) [MulAction H X] (g : H) (q : ℚ) (p : MonoidAlgebra ℤ X) :
    mapTensorX X g (q ⊗ₜ[ℤ] p) = q ⊗ₜ[ℤ] ((Rep.ofMulAction ℤ H X).ρ g p) := by
  rw [mapTensorX, TensorProduct.map_tmul, LinearMap.id_apply]

lemma bridgeRX_mapTensor (X : Type) [DecidableEq X] [MulAction H X] (g : H)
    (t : ℚ ⊗[ℤ] MonoidAlgebra ℤ X) :
    bridgeRX X (mapTensorX X g t) = (Rep.ofMulAction ℚ H X).ρ g (bridgeRX X t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul q p =>
      show bridgeRX X (mapTensorX X g (q ⊗ₜ[ℤ] p))
        = (Rep.ofMulAction ℚ H X).ρ g (bridgeRX X (q ⊗ₜ[ℤ] p))
      rw [mapTensorX_tmul]
      apply MonoidAlgebra.ext
      ext y
      rw [bridgeRX_tmul_coeff X q ((Rep.ofMulAction ℤ H X).ρ g p) y,
        PC.coeff_rho_Z, lmapDomain_smul_apply_smul X (A := ℤ) g p.coeff y,
        coeff_rho_Q X, lmapDomain_smul_apply_smul X (A := ℚ) g (bridgeRX X (q ⊗ₜ[ℤ] p)).coeff y,
        bridgeRX_tmul_coeff X q p (g⁻¹ • y)]
  | add x y hx hy =>
      show bridgeRX X (mapTensorX X g (x + y))
        = (Rep.ofMulAction ℚ H X).ρ g (bridgeRX X (x + y))
      simp only [map_add, hx, hy]

lemma bridgeRX_symm_mapTensor (X : Type) [DecidableEq X] [MulAction H X] (g : H)
    (w : MonoidAlgebra ℚ X) :
    (bridgeRX X).symm ((Rep.ofMulAction ℚ H X).ρ g w)
      = mapTensorX X g ((bridgeRX X).symm w) := by
  apply (bridgeRX X).injective
  calc (bridgeRX X) ((bridgeRX X).symm ((Rep.ofMulAction ℚ H X).ρ g w))
      = (Rep.ofMulAction ℚ H X).ρ g w :=
        LinearEquiv.apply_symm_apply (bridgeRX X) ((Rep.ofMulAction ℚ H X).ρ g w)
    _ = (Rep.ofMulAction ℚ H X).ρ g ((bridgeRX X) ((bridgeRX X).symm w)) :=
        congrArg ((Rep.ofMulAction ℚ H X).ρ g)
          (LinearEquiv.apply_symm_apply (bridgeRX X) w).symm
    _ = (bridgeRX X) (mapTensorX X g ((bridgeRX X).symm w)) :=
        (bridgeRX_mapTensor X g ((bridgeRX X).symm w)).symm

/-! ## C 部分：换基 `ℤ → ℚ`（对假设 `e₁ : M_H_rep ≅ ℤ[X]`） -/

noncomputable def e1Lin (X : Type) [MulAction H X] (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) :
    ↥(LinearMap.ker pi) ≃ₗ[ℤ] MonoidAlgebra ℤ X :=
  (Representation.equivOfIso e₁).toLinearEquiv

lemma e1Lin_equivariant (X : Type) [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) (g : H) (x : ↥(LinearMap.ker pi)) :
    e1Lin X e₁ (M_H_act g x) = (Rep.ofMulAction ℤ H X).ρ g (e1Lin X e₁ x) := by
  have h := Rep.hom_comm_apply e₁.hom g x
  exact h

noncomputable def baseChangeE1 (X : Type) [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) :
    ℚ ⊗[ℤ] ↥(LinearMap.ker pi) ≃ₗ[ℚ] ℚ ⊗[ℤ] MonoidAlgebra ℤ X :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (e1Lin X e₁)).extendScalarsOfIsLocalization
    (nonZeroDivisors ℤ) ℚ

lemma baseChangeE1_tmul (X : Type) [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) (q : ℚ) (x : ↥(LinearMap.ker pi)) :
    baseChangeE1 X e₁ (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] e1Lin X e₁ x := by
  have h1 : baseChangeE1 X e₁ (q ⊗ₜ[ℤ] x)
      = (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (e1Lin X e₁)) (q ⊗ₜ[ℤ] x) := rfl
  rw [h1, TensorProduct.congr_tmul, LinearEquiv.refl_apply]

lemma baseChangeE1_mapTensor (X : Type) [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) (g : H)
    (t : ℚ ⊗[ℤ] ↥(LinearMap.ker pi)) :
    baseChangeE1 X e₁ (BR.actTensorKer g t)
      = mapTensorX X g (baseChangeE1 X e₁ t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul q x =>
      show baseChangeE1 X e₁ (BR.actTensorKer g (q ⊗ₜ[ℤ] x))
        = mapTensorX X g (baseChangeE1 X e₁ (q ⊗ₜ[ℤ] x))
      rw [BR.actTensorKer_tmul, baseChangeE1_tmul, baseChangeE1_tmul, mapTensorX_tmul,
        e1Lin_equivariant]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma baseChangeE1_symm_mapTensor (X : Type) [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) (g : H)
    (u : ℚ ⊗[ℤ] MonoidAlgebra ℤ X) :
    (baseChangeE1 X e₁).symm (mapTensorX X g u)
      = BR.actTensorKer g ((baseChangeE1 X e₁).symm u) := by
  apply (baseChangeE1 X e₁).injective
  calc (baseChangeE1 X e₁) ((baseChangeE1 X e₁).symm (mapTensorX X g u))
      = mapTensorX X g u :=
        LinearEquiv.apply_symm_apply (baseChangeE1 X e₁) (mapTensorX X g u)
    _ = mapTensorX X g ((baseChangeE1 X e₁) ((baseChangeE1 X e₁).symm u)) :=
        congrArg (mapTensorX X g) (LinearEquiv.apply_symm_apply (baseChangeE1 X e₁) u).symm
    _ = (baseChangeE1 X e₁) (BR.actTensorKer g ((baseChangeE1 X e₁).symm u)) :=
        (baseChangeE1_mapTensor X e₁ g ((baseChangeE1 X e₁).symm u)).symm

/-! ## D 部分：ℚ-侧双积拆分 `ℚ[ModelPH] ≅ (Fin 8 → ℚ[H]) × ℚ` -/

lemma rhoQ_single (g : H) (m : PC.ModelPH) (r : ℚ) :
    ((Rep.ofMulAction ℚ H PC.ModelPH).ρ g) (MonoidAlgebra.single m r)
      = MonoidAlgebra.single (g • m) r := by
  change ((Representation.ofMulAction ℚ H PC.ModelPH) g) (MonoidAlgebra.single m r)
      = MonoidAlgebra.single (g • m) r
  rw [Representation.ofMulAction_single]

lemma rhoQ_single_inl (g : H) (p : Fin 8 × H) (r : ℚ) :
    ((Rep.ofMulAction ℚ H PC.ModelPH).ρ g) (MonoidAlgebra.single (Sum.inl p) r)
      = MonoidAlgebra.single (Sum.inl (g • p)) r := by
  rw [rhoQ_single]
  rfl

lemma rhoQ_single_inr (g : H) (u : PUnit) (r : ℚ) :
    ((Rep.ofMulAction ℚ H PC.ModelPH).ρ g) (MonoidAlgebra.single (Sum.inr u) r)
      = MonoidAlgebra.single (Sum.inr u) r := by
  rw [rhoQ_single]
  rfl

lemma prodSplit_single_inl (p : Fin 8 × H) (r : ℚ) :
    (Finsupp.sumFinsuppLEquivProdFinsupp ℚ
        (Finsupp.single (Sum.inl p) r : PC.ModelPH →₀ ℚ))
      = (Finsupp.single p r, 0) := by
  refine Prod.ext ?_ ?_
  · refine Finsupp.ext fun q => ?_
    rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : q = p <;> simp [h]
  · refine Finsupp.ext fun u => ?_
    rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]
    rw [if_neg (fun h => by cases h)]
    rfl

lemma prodSplit_single_inr (u : PUnit) (r : ℚ) :
    (Finsupp.sumFinsuppLEquivProdFinsupp ℚ
        (Finsupp.single (Sum.inr u) r : PC.ModelPH →₀ ℚ))
      = (0, Finsupp.single u r) := by
  refine Prod.ext ?_ ?_
  · refine Finsupp.ext fun q => ?_
    rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]
    rw [if_neg (fun h => by cases h)]
    rfl
  · refine Finsupp.ext fun u' => ?_
    rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : u' = u <;> simp [h]

noncomputable def splitFree : ((Fin 8 × H) →₀ ℚ) ≃ₗ[ℚ] (Fin 8 → MI.R) :=
  (Finsupp.curryLinearEquiv ℚ).trans <|
    ((Finsupp.linearEquivFunOnFinite ℚ (H →₀ ℚ) (Fin 8)).trans
      (LinearEquiv.piCongrRight fun _ : Fin 8 => (MonoidAlgebra.coeffLinearEquiv ℚ).symm))

lemma splitFree_single (p : Fin 8 × H) (r : ℚ) :
    splitFree (Finsupp.single p r) = Pi.single p.1 (MonoidAlgebra.single p.2 r) := by
  show (LinearEquiv.piCongrRight fun _ : Fin 8 => (MonoidAlgebra.coeffLinearEquiv ℚ).symm)
      ((Finsupp.linearEquivFunOnFinite ℚ (H →₀ ℚ) (Fin 8)) ((Finsupp.single p r).curry))
    = Pi.single p.1 (MonoidAlgebra.single p.2 r)
  rw [Finsupp.curry_single, Finsupp.linearEquivFunOnFinite_single]
  funext i
  rw [LinearEquiv.piCongrRight_apply]
  by_cases h : i = p.1
  · rw [h, Pi.single_eq_same, Pi.single_eq_same, MonoidAlgebra.coeffLinearEquiv_symm_apply]
    rfl
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

noncomputable def splitTriv : (PUnit →₀ ℚ) ≃ₗ[ℚ] ℚ :=
  (Finsupp.linearEquivFunOnFinite ℚ ℚ PUnit).trans (LinearEquiv.funUnique PUnit ℚ ℚ)

lemma splitTriv_single (u : PUnit) (r : ℚ) : splitTriv (Finsupp.single u r) = r := by
  show (LinearEquiv.funUnique PUnit ℚ ℚ)
      ((Finsupp.linearEquivFunOnFinite ℚ ℚ PUnit) (Finsupp.single u r)) = r
  rw [Finsupp.linearEquivFunOnFinite_single, LinearEquiv.funUnique_apply]
  show (Pi.single u r : PUnit → ℚ) (default : PUnit) = r
  rw [show (default : PUnit) = u from Subsingleton.elim _ _]
  exact Pi.single_eq_same (M := fun _ : PUnit => ℚ) u r

/-- **拆分线性同构**：`ℚ[ModelPH] ≅ₗ (Fin 8 → ℚ[H]) × ℚ`（沿 `Sum` 分裂系数）。 -/
noncomputable def splitQ : MonoidAlgebra ℚ PC.ModelPH ≃ₗ[ℚ] (Fin 8 → MI.R) × ℚ :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).trans <|
    ((Finsupp.sumFinsuppLEquivProdFinsupp ℚ :
        (PC.ModelPH →₀ ℚ) ≃ₗ[ℚ] ((Fin 8 × H) →₀ ℚ) × (PUnit →₀ ℚ)).trans <|
      splitFree.prodCongr splitTriv)

lemma splitQ_single_inl (p : Fin 8 × H) (r : ℚ) :
    splitQ (MonoidAlgebra.single (Sum.inl p) r)
      = (Pi.single p.1 (MonoidAlgebra.single p.2 r), 0) := by
  rw [splitQ, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, prodSplit_single_inl,
    splitFree_single, map_zero]

lemma splitQ_single_inr (u : PUnit) (r : ℚ) :
    splitQ (MonoidAlgebra.single (Sum.inr u) r) = (0, r) := by
  rw [splitQ, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, prodSplit_single_inr,
    splitTriv_single, map_zero]

/-- 目标侧（`(Fin 8 → R) × ℚ`）上 `single g 1` 的显式展开（逐层归约到乘法）。 -/
lemma single_smul_prod (g : H) (a : Fin 8 → MI.R) (b : ℚ) :
    MonoidAlgebra.single g (1 : ℚ) • (a, b)
      = (fun i => MonoidAlgebra.single g (1 : ℚ) * a i,
        MH.augQ (MonoidAlgebra.single g (1 : ℚ)) * b) := by
  show MonoidAlgebra.single g (1 : ℚ) • (a, b)
    = ((fun i => MonoidAlgebra.single g (1 : ℚ) * a i),
        MH.augQ (MonoidAlgebra.single g (1 : ℚ)) * b)
  rw [Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · funext i
    show ((MonoidAlgebra.single g (1 : ℚ) : MI.R) • a) i
      = MonoidAlgebra.single g (1 : ℚ) * a i
    rw [Pi.smul_apply]
    rfl
  · rfl

/-- **逐点等变式**：ℚ-侧拆分与两侧作用相容（单点展开）。 -/
lemma splitQ_smul (g : H) (w : MonoidAlgebra ℚ PC.ModelPH) :
    splitQ ((Rep.ofMulAction ℚ H PC.ModelPH).ρ g w)
      = MonoidAlgebra.single g (1 : ℚ) • splitQ w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, BR.single_smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, BR.single_smul_add]
  | single m r =>
      rcases m with p | u
      · rw [rhoQ_single_inl g p r]
        nth_rewrite 1 [splitQ_single_inl (g • p) r]
        nth_rewrite 1 [splitQ_single_inl p r]
        rw [single_smul_prod, MH.augQ_single, one_mul]
        refine Prod.ext ?_ rfl
        funext i
        show (Pi.single p.1 (MonoidAlgebra.single (g * p.2) r) : Fin 8 → MI.R) i
          = MonoidAlgebra.single g (1 : ℚ)
            * (Pi.single p.1 (MonoidAlgebra.single p.2 r) : Fin 8 → MI.R) i
        by_cases hi : i = p.1
        · subst hi
          rw [Pi.single_eq_same, Pi.single_eq_same, MonoidAlgebra.single_mul_single, one_mul]
        · rw [Pi.single_eq_of_ne (M := fun _ : Fin 8 => MI.R) (i := p.1) (i' := i) hi,
            Pi.single_eq_of_ne (M := fun _ : Fin 8 => MI.R) (i := p.1) (i' := i) hi, mul_zero]
      · rw [rhoQ_single_inr g u r]
        nth_rewrite 1 [splitQ_single_inr u r]
        nth_rewrite 1 [splitQ_single_inr u r]
        rw [single_smul_prod, MH.augQ_single, one_mul]
        refine Prod.ext ?_ rfl
        funext i
        show (0 : Fin 8 → MI.R) i
          = MonoidAlgebra.single g (1 : ℚ) * (0 : Fin 8 → MI.R) i
        rw [Pi.zero_apply]
        show (0 : MI.R) = MonoidAlgebra.single g (1 : ℚ) * (0 : MI.R)
        rw [mul_zero]

lemma splitQ_symm_smul (g : H) (v : (Fin 8 → MI.R) × ℚ) :
    splitQ.symm (MonoidAlgebra.single g (1 : ℚ) • v)
      = (Rep.ofMulAction ℚ H PC.ModelPH).ρ g (splitQ.symm v) := by
  apply splitQ.injective
  calc splitQ (splitQ.symm (MonoidAlgebra.single g (1 : ℚ) • v))
      = MonoidAlgebra.single g (1 : ℚ) • v :=
        LinearEquiv.apply_symm_apply splitQ _
    _ = MonoidAlgebra.single g (1 : ℚ) • splitQ (splitQ.symm v) := by
        rw [LinearEquiv.apply_symm_apply]
    _ = splitQ ((Rep.ofMulAction ℚ H PC.ModelPH).ρ g (splitQ.symm v)) :=
        (splitQ_smul g (splitQ.symm v)).symm

/-! ## E 部分：组装（`hw` 的构造） -/

/-- 装配：`ℚ[X] ≅ₗ ℚ[ModelPH]`，＝ 换基桥 ∘ 换基的 `e₁` ∘ `prop:MH-char` 的
ℚ-侧结构 ∘（拆分之逆）。 -/
noncomputable def PhiQ (X : Type) [DecidableEq X] [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) :
    MonoidAlgebra ℚ X ≃ₗ[ℚ] MonoidAlgebra ℚ PC.ModelPH :=
  ((bridgeRX X).symm).trans ((baseChangeE1 X e₁).symm.trans (BR.eFinalLeft.trans splitQ.symm))

lemma PhiQ_apply (X : Type) [DecidableEq X] [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) (w : MonoidAlgebra ℚ X) :
    PhiQ X e₁ w
      = splitQ.symm (BR.eFinalLeft ((baseChangeE1 X e₁).symm ((bridgeRX X).symm w))) := rfl

/-- `PhiQ` 是 `ℚ[H]`-线性的（逐环复合：桥 → 换基 → `eFinalLeft` → 拆分）。 -/
lemma PhiQ_equivariant (X : Type) [DecidableEq X] [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) (g : H) (w : MonoidAlgebra ℚ X) :
    PhiQ X e₁ ((Rep.ofMulAction ℚ H X).ρ g w)
      = (Rep.ofMulAction ℚ H PC.ModelPH).ρ g (PhiQ X e₁ w) := by
  have hstep : BR.eFinalLeft (BR.actTensorKer g ((baseChangeE1 X e₁).symm ((bridgeRX X).symm w)))
      = MonoidAlgebra.single g (1 : ℚ)
        • BR.eFinalLeft ((baseChangeE1 X e₁).symm ((bridgeRX X).symm w)) := by
    show BR.eFinalLeft (g • ((baseChangeE1 X e₁).symm ((bridgeRX X).symm w)))
      = MonoidAlgebra.single g (1 : ℚ)
        • BR.eFinalLeft ((baseChangeE1 X e₁).symm ((bridgeRX X).symm w))
    exact BR.eFinalLeft_equivariant g _
  simp only [PhiQ_apply]
  rw [bridgeRX_symm_mapTensor X g w,
    baseChangeE1_symm_mapTensor X e₁ g ((bridgeRX X).symm w), hstep,
    splitQ_symm_smul g
      (BR.eFinalLeft ((baseChangeE1 X e₁).symm ((bridgeRX X).symm w)))]

set_option maxRecDepth 4000 in
/-- `PhiQ` 的 `Rep ℚ H` 层包装：`ℚ[X] ≅ ℚ[ModelPH]`（`PC.permClass` 的入口）。 -/
noncomputable def PhiQIso (X : Type) [DecidableEq X] [MulAction H X]
    (e₁ : M_H_rep ≅ Rep.ofMulAction ℤ H X) :
    Rep.ofMulAction ℚ H X ≅ Rep.ofMulAction ℚ H PC.ModelPH :=
  Rep.mkIso (Representation.Equiv.mk (PhiQ X e₁)
    (fun g => LinearMap.ext (fun w => PhiQ_equivariant X e₁ g w)))

/-- **缺口 (i) 的闭合**：置换格假设 ⟹ `M_H_rep ≅ modelPHRep`（无条件，即 §11 的 `hw`）。 -/
theorem hasIso_modelPH_of_perm (hP : IsPermutationLattice M_H_rep) :
    Nonempty (M_H_rep ≅ modelPHRep) := by
  obtain ⟨X, hfin, hact, ⟨e₁⟩⟩ := hP
  have hdec : DecidableEq X := Classical.decEq X
  obtain ⟨eQ⟩ := PC.permClass X ⟨PhiQIso X e₁⟩
  exact ⟨e₁.trans eQ⟩

/-- **无条件主定理**：`¬ IsPermutationLattice M_H_rep`（＝ §11 条件主定理的 `hw` 已
被上一件构造，无需再假设）。 -/
theorem M_H_not_permutation_main : ¬ IsPermutationLattice M_H_rep :=
  M_H_not_permutation_via_biprod hasIso_modelPH_of_perm

/-! ## F 部分：公理闸门（每个顶层声明一条） -/

#print axioms bridgeRAuxX
#print axioms bridgeRX
#print axioms bridgeRX_tmul_coeff
#print axioms lmapDomain_smul_apply_smul
#print axioms coeff_rho_Q
#print axioms mapTensorX
#print axioms mapTensorX_tmul
#print axioms bridgeRX_mapTensor
#print axioms bridgeRX_symm_mapTensor
#print axioms e1Lin
#print axioms e1Lin_equivariant
#print axioms baseChangeE1
#print axioms baseChangeE1_tmul
#print axioms baseChangeE1_mapTensor
#print axioms baseChangeE1_symm_mapTensor
#print axioms rhoQ_single
#print axioms rhoQ_single_inl
#print axioms rhoQ_single_inr
#print axioms prodSplit_single_inl
#print axioms prodSplit_single_inr
#print axioms splitFree
#print axioms splitFree_single
#print axioms splitTriv
#print axioms splitTriv_single
#print axioms splitQ
#print axioms splitQ_single_inl
#print axioms splitQ_single_inr
#print axioms single_smul_prod
#print axioms splitQ_smul
#print axioms splitQ_symm_smul
#print axioms PhiQ
#print axioms PhiQ_apply
#print axioms PhiQ_equivariant
#print axioms PhiQIso
#print axioms hasIso_modelPH_of_perm
#print axioms M_H_not_permutation_main

end ABGV52.ExtMHUncond
