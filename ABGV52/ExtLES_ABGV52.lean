/-
  ABGV-5.2 —— 论文 `prop:M_H-not-permutation` 证明第一步：Ext 长正合列塌缩

  论文锚点
  ========
    增广短正合列 `0 → I[H] → Z[H] → Z → 0` 在 `Rep ℤ H` 中（`augComplex`，
    短正合性见 C4 的 `augComplex_shortExact`）；对其取 `Hom_{Rep}(−,L)` 型长正合列，
    两端因 `regZ = Z[H]` 射影而消没，连接同态
      δ : Ext¹(I[H],L) → Ext²(Z,L)
    遂为（加法群）同构——`prop:M_H-not-permutation` 证明中把待算的 Ext¹ 搬到
    已知形状的 Ext² 的那一步。

  本件构造
  ========
    * `instHasExtRepLES`：`Rep.{0} ℤ H` 的 `HasExt.{0}` 实例（宇宙取 0，
      与桥件相容——桥件左腿落在 `ModuleCat.{0} ℤ`）；
    * `regZ_rho_apply_eq` / `regZIsoLeftRegular` / `instProjectiveRegZ`：
      `regZ ≅ Rep.leftRegular ℤ H` ⟹ `Projective regZ`；
    * `extConnectingMap`：`δ = augComplex_shortExact.extClass.precomp L h`；
    * `extConnectingMap_injective`：差法 ＋ `Ext.contravariant_sequence_exact₁`
      ＋ 左端消没（`Ext.subsingleton_of_projective`）；
    * `extConnectingMap_surjective`：`Ext.contravariant_sequence_exact₃`
      ＋ 右端消没；
    * `extOneIH_addEquiv_extTwoTriv`：主定理（`AddEquiv.ofBijective` 组装）。

  路线与探针实测结论（探针件 `ProbeLES1_ABGV52.lean`，rc=0）
  ========================================================
    ① `HasExt.{0}` 不可由 `infer_instance` 得（`hasExt_of_enoughProjectives`
       刻意不是 instance）；且**必须先用局部实例钉住 `LocallySmall.{0}`**——
       否则 w 未定时实例搜索先命中 `locallySmall_of_univLE`（`UnivLE` 链把 w 钉成
       `max 1 ?u`），报「`HasExt.{max 1 ?u}` 与 `HasExt.{0}` 不匹配」。
    ② 逐元素 LES 正合性 `Ext.contravariant_sequence_exact₁/₃` 可直接套用
       （S = augComplex、Y = L）；`precomp` 是 `bilinearComp` 的 abbrev，
       且 `Ext.comp` 定义体 `SmallShiftedHom.comp α β (by lia)` **不用其 `h`**
       ⟹ `δ x = extClass.comp x h` 为 rfl 级、不同 `h` 见证彼此 defeq。
       ⚠ 陷阱：只 `open CategoryTheory` 时裸 `Ext` 解析到错误常量；
       **须 `open CategoryTheory.Abelian`**。
       ⚠ 陷阱（实例合成的句法匹配）：exact₁/₃ 的结论把对象写作 `augComplex.X₂`，
       而 `regZ` 是普通 `def`——实例搜索在 `.instances` 透明度下不展开普通 def，
       `Subsingleton (Ext regZ L 1)` 匹配不上目标 `Subsingleton (Ext augComplex.X₂ L 1)`
       ⟹ 局部实例按**目标句法拼写**声明（证明项仍用 `regZ`）。
    ③ `Projective regZ`：`regZ ≅ Rep.leftRegular ℤ H`（恒等线性等价 ＋ 逐点等变，
       见 `regZ_rho_apply_eq`），再 `Projective.of_iso e.symm
       Rep.leftRegular_projective`（`of_iso : P ≅ Q → Projective P → Projective Q`）。
       ⚠ 陷阱：`regZ` 是普通 `def`，`rw`／`simp` 在 `.instances` 透明度下不展开它；
       逐点引理须走字面头部 ＋ `change` ＋ `calc` ＋ 项级引理。
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

-- （2026-10-10 审查 B：两处 `haveI` 触发 style linter；同 ExtBridge 先例关闭。）
set_option linter.style.haveILetI false

/-! ## 1. `HasExt.{0}` 实例 -/

-- `Rep.{0} ℤ H` 的 `Category.{0}` 使 `locallySmall_self` 本可给出 `LocallySmall.{0}`，
-- 但 w 未定时实例搜索先命中 `locallySmall_of_univLE` 把 w 钉成 `max 1 ?u`；
-- 显式局部实例（优先级 1000 > mathlib 的 100）钉住 {0}。
local instance : LocallySmall.{0} (Rep.{0} ℤ H) :=
  locallySmall_self (C := Rep.{0} ℤ H)

/-- `Rep.{0} ℤ H` 有 `HasExt.{0}`（经 `EnoughProjectives` ＋ `LocallySmall.{0}`；
取宇宙 0 以便与桥件复合）。`HasExt` 是 Prop 值 abbrev，同名实例无冲突之虞。 -/
instance instHasExtRepLES : HasExt.{0} (Rep.{0} ℤ H) :=
  hasExt_of_enoughProjectives (Rep.{0} ℤ H)

/-! ## 2. `Projective regZ` -/

/-- 逐点等变：`regZ` 的左乘作用与 `Rep.leftRegular ℤ H` 的正则作用一致。
证明经 `change` 走到**字面头部**（`Representation.ofDistribMulAction/ofMulAction`）：
`regZ` 是普通 `def`，`rw`／`simp` 在 `.instances` 透明度下不展开它，
故不能在原头部上直接归纳；`change` 用 default 透明度的 defeq 换头。 -/
lemma regZ_rho_apply_eq (g : H) (w : MonoidAlgebra ℤ H) :
    regZ.ρ g w = (Rep.leftRegular ℤ H).ρ g w := by
  change (Representation.ofDistribMulAction ℤ H (MonoidAlgebra ℤ H)) g w
      = (Representation.ofMulAction ℤ H H) g w
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

/-- `regZ ≅ Rep.leftRegular ℤ H`（恒等线性等价，等变性即 `regZ_rho_apply_eq`）。 -/
noncomputable def regZIsoLeftRegular : regZ ≅ Rep.leftRegular ℤ H :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ (MonoidAlgebra ℤ H)) (by
    intro g
    refine LinearMap.ext fun w => ?_
    exact regZ_rho_apply_eq g w))

/-- `regZ` 射影（经 `regZIsoLeftRegular` 从 `Rep.leftRegular_projective` 搬运）。 -/
noncomputable instance instProjectiveRegZ : Projective regZ :=
  Projective.of_iso regZIsoLeftRegular.symm
    (Rep.leftRegular_projective (k := ℤ) (G := H))

/-! ## 3. 连接同态 `δ : Ext¹(I[H],L) → Ext²(Z,L)` -/

section LES

variable (L : Rep ℤ H)

/-- 连接同态 `δ : Ext¹(I[H],L) → Ext²(Z,L)`（增广短正合列的 LES 连接映射，
沿 `1 + 1 = 2`）。 -/
noncomputable def extConnectingMap : Ext I_H_rep L 1 →+ Ext trivRep L 2 :=
  augComplex_shortExact.extClass.precomp L (rfl : 1 + 1 = 2)

/-- `δ` 的定义展开（rfl 级：`precomp` 是 `bilinearComp` 的 abbrev）。 -/
lemma extConnectingMap_apply (x : Ext I_H_rep L 1) :
    extConnectingMap L x
      = augComplex_shortExact.extClass.comp x (rfl : 1 + 1 = 2) :=
  rfl

/-- **`δ` 是单射**。差法 ＋ `exact₁`（`ker δ = im(Ext¹(Z[H]) → Ext¹(I[H]))`）
＋ 左端消没（`regZ` 射影 ⟹ `Ext¹(regZ,−) = 0`：任何提升都是 `0` 的像）。 -/
lemma extConnectingMap_injective : Function.Injective (extConnectingMap L) := by
  intro x y hxy
  haveI : Subsingleton (Ext augComplex.X₂ L 1) :=
    Ext.subsingleton_of_projective regZ L 0
  have hsub : extConnectingMap L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨w, hw⟩ :=
    Ext.contravariant_sequence_exact₁ augComplex_shortExact L (x - y)
      (rfl : 1 + 1 = 2) hsub
  have hw0 : (Ext.mk₀ augComplex.f).comp w (zero_add 1) = 0 := by
    rw [Subsingleton.elim w (0 : Ext regZ L 1)]
    exact Ext.comp_zero (Ext.mk₀ augComplex.f) L 1 1 (zero_add 1)
  exact sub_eq_zero.mp (hw.symm.trans hw0)

/-- **`δ` 是满射**。`exact₃`（`ker(Ext²(Z[H]) → Ext²(Z)) = im δ`）
＋ 右端消没（`regZ` 射影 ⟹ `Ext²(regZ,−) = 0` ⟹ 保核条件自动成立）。 -/
lemma extConnectingMap_surjective : Function.Surjective (extConnectingMap L) := by
  intro z
  haveI : Subsingleton (Ext augComplex.X₂ L 2) :=
    Ext.subsingleton_of_projective regZ L 1
  have hz : (Ext.mk₀ augComplex.g).comp z (zero_add 2) = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ :=
    Ext.contravariant_sequence_exact₃ augComplex_shortExact L z hz (rfl : 1 + 1 = 2)
  exact ⟨x, hx⟩

end LES

/-! ## 4. 主定理：LES 塌缩 -/

/-- **Ext 长正合列塌缩**（`prop:M_H-not-permutation` 证明第一步）：
增广短正合列 `0 → I[H] → Z[H] → Z → 0` 的 `Hom_{Rep}(−,L)` 长正合列中，
两端因 `regZ = Z[H]` 射影而消没，连接同态给出加法群同构
`Ext¹(I[H],L) ≃+ Ext²(Z,L)`。 -/
noncomputable def extOneIH_addEquiv_extTwoTriv (L : Rep ℤ H) :
    Ext I_H_rep L 1 ≃+ Ext trivRep L 2 :=
  AddEquiv.ofBijective (extConnectingMap L)
    ⟨extConnectingMap_injective L, extConnectingMap_surjective L⟩

/-! ## 5. 公理闸门 -/

#print axioms regZ_rho_apply_eq
#print axioms regZIsoLeftRegular
#print axioms instProjectiveRegZ
#print axioms extConnectingMap
#print axioms extConnectingMap_apply
#print axioms extConnectingMap_injective
#print axioms extConnectingMap_surjective
#print axioms extOneIH_addEquiv_extTwoTriv

end ABGV52
