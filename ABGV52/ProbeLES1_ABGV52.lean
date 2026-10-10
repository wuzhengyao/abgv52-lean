/-
  ABGV-5.2 —— Ext LES 塌缩件：探针 1（临时件；v2 = 修正后全绿版）

  本件为 `ExtLES_ABGV52.lean` 勘路：论文 `prop:M_H-not-permutation` 证明第一步
  ——增广短正合列 `0 → I[H] → Z[H] → Z → 0` 的 `Hom(−,L)` 长正合列，两端因
  `Z[H]` 射影而消没，得 `Ext¹(I[H],L) ≃ Ext²(Z,L)`。三条待勘 ＋ 实测读数：

    ① `HasExt` 在 `Rep.{0} ℤ H` 上的宇宙合成：
       - v1(a) `infer_instance` **超时**——`hasExt_of_enoughProjectives` 刻意不是
         instance（见 EnoughProjectives.lean 头部 docstring）；
       - v1(b) `HasExt.standard _` 在 `Rep ℤ H` 上报宇宙不匹配——`Rep` 的载体
         宇宙成 metavariable；**钉住 `Rep.{0} ℤ H` 后**该路给出 `HasExt.{1}`；
       - v2 续坑：即便写明 `hasExt_of_enoughProjectives (Rep.{0} ℤ H) : HasExt.{0}`，
         w 未定时实例搜索仍先命中 `locallySmall_of_univLE : LocallySmall.{w} C`
         [UnivLE 链] 把 w 钉成 `max 1 ?u` ⟹ 报「`HasExt.{max 1 ?u.11}` 与
         `HasExt.{0}` 不匹配」。**须先以局部实例钉住**
         `local instance : LocallySmall.{0} (Rep.{0} ℤ H) := locallySmall_self (…)`
         （局部实例优先级 1000 胜过 mathlib 的 100）。
       - 定路：先钉 `LocallySmall.{0}`，再
         `hasExt_of_enoughProjectives (Rep.{0} ℤ H) : HasExt.{0}`
         （其余输入 = `Category.{0}` ✓ ＋ `EnoughProjectives (Rep.{max w u} k G)` ✓）。
         **取 {0}**：与桥件（左腿落 `ModuleCat.{0} ℤ`）同宇宙，两件可复合。
    ② 逐元素 LES 正合性 `Ext.contravariant_sequence_exact₁/₃` 可直接套用本场景
       （S = augComplex、Y = L）；连接同态 = `hS.extClass.precomp L h`，
       而 `precomp` 是 `bilinearComp` 的 abbrev ⟹ `δ x = extClass.comp x h`
       为 rfl 级；且 `Ext.comp` 的定义体不使用其 `h` 参数 ⟹ 不同 `h` 见证彼此
       defeq（连证明无关性都不需要）。
       ⚠ v1 陷阱：只 `open CategoryTheory` 时裸 `Ext` 解析到错误常量（报
       `Ring ↑I_H_rep` 一类怪错）；**须 `open CategoryTheory.Abelian`**。
       ⚠ v2 陷阱（**实例合成的句法匹配**）：exact₁/₃ 的结论把对象写作 `S.X₂`
       （= `augComplex.X₂`），而 `regZ` 是**普通 def**——实例搜索在
       `.instances` 透明度下**不展开普通 def**，故 `Subsingleton (Ext regZ L 1)`
       这一局部实例**匹配不上**目标 `Subsingleton (Ext augComplex.X₂ L 1)`
       （报 `synthInstanceFailed`）。**修法**：局部实例按目标出现的**句法拼写**
       声明（证明项仍用 `regZ`，ascription 由 default 透明度的 defeq 核对通过）。
       另：`Ext.comp` 定义体为 `SmallShiftedHom.comp α β (by lia)`——**不用其 `h`**
       ⟹ 不同 `h` 见证彼此 defeq（连证明无关性都不需要）。
    ③ `Projective regZ`：先造 `regZ ≅ Rep.leftRegular ℤ H`（恒等线性等价 ＋ 逐点
       等变），再 `Projective.of_iso e.symm Rep.leftRegular_projective`
       （`of_iso : (i : P ≅ Q) → Projective P → Projective Q`，见
       `Mathlib/CategoryTheory/Preadditive/Projective/Basic.lean:106`）。
       ⚠ v1 陷阱：`regZ` 是普通 `def`，`rw`／`simp` 在 `.instances` 透明度下
       **不展开它**（报「x + y has type MonoidAlgebra ℤ H but expected ↑regZ」）
       ——逐点引理须以**字面** `Representation.ofDistribMulAction/ofMulAction`
       为头部，用 `calc` ＋ 项级引理（项级精化可展开普通 def，tactic 模式匹配不可）。
-/
import ABGV52.C4_ABGV52
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

open CategoryTheory
open CategoryTheory.Abelian

namespace ABGV52

-- `ℤ` 上 `AddCommGroup.toIntModule` 与 `Rep.hV2` 争用 `Module ℤ ↥X`（同 C4 的处理）。
attribute [local instance 1500] Rep.hV2

/-! ## 探针 ①：`HasExt` 宇宙 -/

-- v2 实测修复：`Rep.{0} ℤ H` 的 `Category.{0}` 本可由 `locallySmall_self` 给出
-- `LocallySmall.{0}`，但 w 未定时实例搜索先命中 `locallySmall_of_univLE`
-- （`UnivLE` 链把 w 钉成 `max 1 ?u`）⟹ 结果 `HasExt.{max 1 ?u}` 与 `HasExt.{0}`
-- 不匹配（v1 报错原文）。定路 = 显式局部实例钉住 `{0}`（局部实例优先级 1000 > 100）。
local instance : LocallySmall.{0} (Rep.{0} ℤ H) :=
  locallySmall_self (C := Rep.{0} ℤ H)

example : HasExt.{0} (Rep.{0} ℤ H) := hasExt_of_enoughProjectives (Rep.{0} ℤ H)

example : HasExt.{1} (Rep.{0} ℤ H) := HasExt.standard _

-- 全局实例（交付件 `ExtLES_ABGV52.lean` 用；`HasExt` 是 Prop 值 abbrev，重名实例无害）
instance instHasExtRepLES : HasExt.{0} (Rep.{0} ℤ H) :=
  hasExt_of_enoughProjectives (Rep.{0} ℤ H)

/-! ## 探针 ③：`Projective regZ` -/

/-- 逐点等变（**字面头部**；`calc` ＋ 项级引理）。 -/
lemma probe_regZ_smul_eq (g : H) (w : MonoidAlgebra ℤ H) :
    (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g w
      = (Representation.ofMulAction ℤ H H) g w := by
  induction w using MonoidAlgebra.induction_linear with
  | zero =>
      calc (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g 0
          = 0 :=
            map_zero ((Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g)
        _ = (Representation.ofMulAction ℤ H H) g 0 :=
            (map_zero ((Representation.ofMulAction ℤ H H) g)).symm
  | add x y hx hy =>
      calc (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g (x + y)
          = (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g x
            + (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g y :=
            map_add ((Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g) x y
        _ = (Representation.ofMulAction ℤ H H) g x
            + (Representation.ofMulAction ℤ H H) g y := by rw [hx, hy]
        _ = (Representation.ofMulAction ℤ H H) g (x + y) :=
            (map_add ((Representation.ofMulAction ℤ H H) g) x y).symm
  | single m r =>
      calc (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g
              (MonoidAlgebra.single m r)
          = g • (MonoidAlgebra.single m r : MonoidAlgebra ℤ H) :=
            Representation.ofDistribMulAction_apply_apply g (MonoidAlgebra.single m r)
        _ = MonoidAlgebra.single g 1 * MonoidAlgebra.single m r := rfl
        _ = MonoidAlgebra.single (g * m) r := by
            rw [MonoidAlgebra.single_mul_single, one_mul]
        _ = (Representation.ofMulAction ℤ H H) g (MonoidAlgebra.single m r) :=
            (Representation.ofMulAction_single g m r).symm

/-- `regZ ≅ Rep.leftRegular ℤ H`。 -/
noncomputable def probe_regZIso : regZ ≅ Rep.leftRegular ℤ H :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ (MonoidAlgebra ℤ H)) (by
    intro g
    refine LinearMap.ext fun w => ?_
    show (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g w
        = (Representation.ofMulAction ℤ H H) g w
    exact probe_regZ_smul_eq g w))

/-- `regZ` 射影（经同构搬运 `Rep.leftRegular_projective`）。 -/
noncomputable instance probe_regZ_projective : Projective regZ :=
  Projective.of_iso probe_regZIso.symm (Rep.leftRegular_projective (k := ℤ) (G := H))

/-! ## 探针 ②：LES 片段 ＋ 塌缩核心步 -/

section LES

variable (L : Rep ℤ H)

/-- 连接同态 `δ : Ext¹(I[H],L) → Ext²(Z,L)`。 -/
noncomputable def probeDelta : Ext I_H_rep L 1 →+ Ext trivRep L 2 :=
  augComplex_shortExact.extClass.precomp L (rfl : 1 + 1 = 2)

-- δ 的定义展开（rfl 级）
example (x : Ext I_H_rep L 1) :
    probeDelta L x = augComplex_shortExact.extClass.comp x (rfl : 1 + 1 = 2) :=
  rfl

-- 逐元素正合（exact₁）：ker δ = im(Ext¹(Z[H]) → Ext¹(I[H]))
example (x : Ext I_H_rep L 1)
    (hx : augComplex_shortExact.extClass.comp x (rfl : 1 + 1 = 2) = 0) :
    ∃ (w : Ext regZ L 1), (Ext.mk₀ augComplex.f).comp w (zero_add 1) = x :=
  Ext.contravariant_sequence_exact₁ augComplex_shortExact L x (rfl : 1 + 1 = 2) hx

-- 逐元素正合（exact₃）：ker(Ext²(Z[H]) → Ext²(Z[G])) = im δ
example (z : Ext trivRep L 2)
    (hz : (Ext.mk₀ augComplex.g).comp z (zero_add 2) = 0) :
    ∃ (x : Ext I_H_rep L 1),
      augComplex_shortExact.extClass.comp x (rfl : 1 + 1 = 2) = z :=
  Ext.contravariant_sequence_exact₃ augComplex_shortExact L z hz (rfl : 1 + 1 = 2)

-- 两端消没（射影性 ＋ `subsingleton_of_projective`）
example : Subsingleton (Ext regZ L 1) := Ext.subsingleton_of_projective regZ L 0

example : Subsingleton (Ext regZ L 2) := Ext.subsingleton_of_projective regZ L 1

-- 注入性核心：差法 ＋ exact₁ ＋ 左端消没
example (x y : Ext I_H_rep L 1) (hxy : probeDelta L x = probeDelta L y) : x = y := by
  haveI : Subsingleton (Ext augComplex.X₂ L 1) := Ext.subsingleton_of_projective regZ L 0
  have hsub : probeDelta L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨w, hw⟩ :=
    Ext.contravariant_sequence_exact₁ augComplex_shortExact L (x - y)
      (rfl : 1 + 1 = 2) hsub
  have hw0 : (Ext.mk₀ augComplex.f).comp w (zero_add 1) = 0 := by
    rw [Subsingleton.elim w (0 : Ext regZ L 1)]
    exact Ext.comp_zero (Ext.mk₀ augComplex.f) L 1 1 (zero_add 1)
  exact sub_eq_zero.mp (hw.symm.trans hw0)

-- 满射性核心：exact₃ ＋ 右端消没
example (z : Ext trivRep L 2) : ∃ (x : Ext I_H_rep L 1), probeDelta L x = z := by
  haveI : Subsingleton (Ext augComplex.X₂ L 2) := Ext.subsingleton_of_projective regZ L 1
  have hz : (Ext.mk₀ augComplex.g).comp z (zero_add 2) = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ :=
    Ext.contravariant_sequence_exact₃ augComplex_shortExact L z hz (rfl : 1 + 1 = 2)
  exact ⟨x, hx⟩

-- 组装：`AddEquiv.ofBijective`
example : Nonempty (Ext I_H_rep L 1 ≃+ Ext trivRep L 2) := by
  have inj : Function.Injective (probeDelta L) := by
    intro x y hxy
    haveI : Subsingleton (Ext augComplex.X₂ L 1) := Ext.subsingleton_of_projective regZ L 0
    have hsub : probeDelta L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨w, hw⟩ :=
      Ext.contravariant_sequence_exact₁ augComplex_shortExact L (x - y)
        (rfl : 1 + 1 = 2) hsub
    have hw0 : (Ext.mk₀ augComplex.f).comp w (zero_add 1) = 0 := by
      rw [Subsingleton.elim w (0 : Ext regZ L 1)]
      exact Ext.comp_zero (Ext.mk₀ augComplex.f) L 1 1 (zero_add 1)
    exact sub_eq_zero.mp (hw.symm.trans hw0)
  have surj : Function.Surjective (probeDelta L) := by
    intro z
    haveI : Subsingleton (Ext augComplex.X₂ L 2) := Ext.subsingleton_of_projective regZ L 1
    have hz : (Ext.mk₀ augComplex.g).comp z (zero_add 2) = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ :=
      Ext.contravariant_sequence_exact₃ augComplex_shortExact L z hz (rfl : 1 + 1 = 2)
    exact ⟨x, hx⟩
  exact ⟨AddEquiv.ofBijective (probeDelta L) ⟨inj, surj⟩⟩

end LES

#print axioms probe_regZ_smul_eq
#print axioms probe_regZIso
#print axioms probe_regZ_projective

end ABGV52
