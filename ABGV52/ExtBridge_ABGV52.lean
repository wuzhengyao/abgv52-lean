/-
  ABGV-5.2 —— Ext 桥（新 Ext 版）：`Ext trivRep A 2 ≃+ ↥(groupCohomology A 2)`（v3）

  使命
  ====
  论文 `prop:M_H-not-permutation` 的证明第一步把 `H²(H, A)` 换算到 Ext 术语；需在
  新 Ext（`CategoryTheory.Abelian.Ext`，derived 版）与群上同调之间造桥：

      `extTwoTriv_addEquiv_coh2 (A : Rep.{0} ℤ H) :
          Ext trivRep A 2 ≃+ ↥(groupCohomology A 2)`

  旧 `CategoryTheory.Ext` 有库内 `ProjectiveResolution.isoExt` 桥；新 Ext 无对应版本，
  本件手工组装。新旧 Ext 同名重载：只 `open CategoryTheory` 时裸 `Ext` 解析到旧常量，
  须 `open CategoryTheory.Abelian`（另有同坑件 ProbeLES1）。

  路线（三段拼接）
  ================
    段一（本件造）`extAddEquivLinYonedaHomology`：
      `Ext X Y (n+1) ≃+ ↥((R.complex.linearYonedaObj ℤ Y).homology (n+1))`
      · 组装子 `toExtHom`：中段余圈 → `Ext X Y (n+1)`——`extMk` 取
        `f : X (n+1) ⟶ Y`、`d (n+2) (n+1) ≫ f = 0`（次数约定见「墙」）；
        零点由库引理 `extMk_zero` 供，加法由 `add_extMk` 供；
      · 商下降 `toExtQuotient`：`余圈 ⧸ 边界 →+ Ext X Y (n+1)`
        （`QuotientAddGroup.lift`（加法群级）；良定义 = `linYonedaBoundaries_le_ker`，
        消没 = `extMk_eq_zero_iff` 的余边界分解）；
      · 单射（差法 ＋ `extMk_eq_zero_iff`）；满射（`extMk_surjective`）；
      · 同调辨认：库内
        `moduleCatHomologyIso : S.homology ≅ S.moduleCatLeftHomologyData.H`
        （其 `H = 余圈 ⧸ 边界` 即本件之商）；取 `S := linYonedaSc R n`；
      · 首尾搬运：库内 `homologyIsoSc' n (n+1) (n+2) (prev_eq' rfl) (next_eq' rfl)
        : L.homology (n+1) ≅ (L.sc' n (n+1) (n+2)).homology`，取 `.symm` 定向；
      · 总装 = `AddEquiv.ofBijective`（单射 ＋ 满射）。
    段二（库内）：`groupCohomologyIso A 2 (Rep.barResolution ℤ H)`：
      `groupCohomology A 2 ≅
        ((Rep.barResolution ℤ H).complex.linearYonedaObj ℤ A).homology 2`
      （只有 `Iso` 版，无 `AddEquiv` 版；加法性走 `Iso.toLinearEquiv.toAddEquiv`）。
    段三（拼接，`n := 1`）：`Ext trivRep A 2 ≃+ …homology 2 ≃+ ↥(groupCohomology A 2)`。

  探针（ProbeEB1_ABGV52.lean 四问读数；本件沿用其全部可核实写法）
  ============================================================
    ① `HasExt.{0} (Rep.{0} ℤ H)`：`infer_instance` 不可得（库明言不作 instance 声明）；
       且 `LocallySmall.{?w}` 未定时 `hasExt_of_enoughProjectives` 会经
       `locallySmall_of_univLE` 先把 w 钉成 `max 1 ?u` ⟹ 与 `{0}` 不匹配。
       定路 = 局部实例先钉 `LocallySmall.{0}`（优先级 1000 胜库内 100），再显式
       `hasExt_of_enoughProjectives (Rep.{0} ℤ H) : HasExt.{0}`。取 {0} 的理由：
       左腿同调对象落在 `ModuleCat.{0} ℤ`（`Ext : Type 0` 方能与之同品类）。
    ② `groupCohomologyIso`：签名 `(A : Rep k G) (n : ℕ)
       (P : ProjectiveResolution (Rep.trivial k G k)) → groupCohomology A n ≅
       (P.complex.linearYonedaObj k A).homology n`。实例对齐：`Rep.instLinear` 与
       库内 `Linear.preadditiveIntLinear` 争 `Linear ℤ (Rep ℤ H)`
       （`groupCohomologyIso` 存储类型用前者）⟹
       `attribute [local instance 1500] Rep.instLinear`（同 C4 的 `Rep.hV2` 模式）。
    ③ 符号零偏差：`((linearYonedaObj ℤ Y).d (n+1) (n+2)).hom f
       = R.complex.d (n+2) (n+1) ≫ f`（纯前复合；
       `rw [ChainComplex.linearYonedaObj_d]; rfl`）——与 `extMk` 的 `hf` 方向一致，
       无需 `negOnePow` 修正。
    ④ `barResolution` 逐项形态：`(barResolution.complex).X n = (barComplex ℤ H).X n`
       （`rw [Rep.barResolution_complex]`）；`sc' n (n+1) (n+2)` 三字段 rfl；
       `homologyIsoSc'` 在 `n, n+1, n+2` 全显式可达
       （`(ComplexShape.up ℕ).prev_eq' rfl` 型实例化，与库内用法一致）。

  墙（陷阱登记；v1 → v3 实测）
  ===========================
    · `Ext` 重载：须 `open CategoryTheory.Abelian`（否则裸 `Ext` 解析到旧常量）。
    · `Ext.instAddCommGroup` 非可计算 ⟹ 全文件在 `noncomputable section` 内。
    · `extMk` 次数约定：**结果次数 = f 的次数**（`m` 只在侧条件出现）——故组装子取
      `f : R.complex.X (n+1) ⟶ Y`、`(m, hm) := (n+2, rfl)` 得 `Ext X Y (n+1)`。
    · `Submodule.Quotient.mk_surjective` 的 `p` 是**显式参数**（写成 `mk_surjective p x`，
      两参）；且域成员不是句法 `∃`——先 `rw [LinearMap.mem_range]` 再造见证。
    · **v1 实测三类失败（行 159–249 区；v3 对策随附）**：
      (a) **跨拼写 rw 在 `implicit` 透明度下失败**——同一载体三种 defeq 拼写
          （`↥S.X₂` ／ `R.complex.X (n+1) ⟶ Y` ／
          `(R.complex.X (n+1)).ρ.IntertwiningMap Y.ρ`）；`rw` 及其 motive 报
          "motive is not type correct"／"target expression is not type-correct under
          the `implicit` transparency level"，而 `change`／默认透明度通过
          （v1 实错 159/160/167/237）。**对策**：§1 全部助手以 `abbrev` 声明，
          **拼写唯一化 = 由体推型**（见 (d)）；证明里用 `change` 桥到
          `linearYonedaObj` 的 `d` 拼写（`sc'` 字段 rfl，探针 ④）。
      (b) **ℤ-模实例菱形**：合成取 `AddCommGroup.toIntModule ↥(…).ker`、typing rules
          取 `(…).ker.module`——报 "synthesized … is not definitionally equal to
          expression inferred by typing rules"（v1 实错 182/196/198/200/205/239）。
          **对策**：`attribute [local instance 1500] Submodule.module`（对齐两者）。
      (c) **映射律不用 `rw`、改用 `.trans` ＋ 合一赋值**：库引理（`add_extMk`／
          `extMk_zero`）直接 `rw` 进含变体的目标会撞 (a)；改用桥引理
          `linYonedaSc_extMk_congr`（`subst` ＋ `rfl`；`extMk` 的论证在本工具链
          rfl 级证明无关，探针实读）＋ `Eq.trans`——全部证明元变量由期望类型
          **合一赋值**解出（`_` 槽），连证明无关性都不需要。
      (d) **v2 实测一类失败：显式 ascription 重合成实例**——助手若写
          `(R.complex.X (n+1) ⟶ Y) →ₗ[ℤ] …` ascription，则 ascription 走**合成**
          得 `AddCommGroup.toIntModule`＋`Rep.instAddCommGroupHom` 链，而体
          （`ModuleCat` 对象的 `.hom`）**携带** `X₂.isModule`
          （`Linear.homModule` 经 `Linear ℤ (Rep ℤ H)`）——两者**非 defeq**
          （v2 实错 150/155/165；其下游 177/186/190/194/315 皆级联）。
          **对策（v3）**：助手与 `toExtQuotient` **一律由体推型**（不留
          `→ₗ[ℤ]`／`Submodule ℤ` ascription）；唯一保留的 ascription =
          `toExtHom` 的 `→+`（`where` 结构体逐字段对照声明型，不产生独立型冲突）。
    · **v5 实测两类失败（行 259–319 区；v6 对策随附）**：
      (e) **商下降不能用 `→ₗ[ℤ]`（两连墙）**：(i) `AddMonoidHom.toIntLinearMap` 的
          结果类型在 mathlib 定义处钉死 `AddCommGroup.toIntModule ↥(余圈)`，与
          `liftQ` 期望的域实例（子模实例 `(ker g).module`）**不 defeq**——实例烘在
          常量型里，ascription 救不了（v4 实错 262/266）；(ii) 改结构字面量后
          `map_smul'` 仍不可证：域 `↥(余圈)` 的 ℤ-作用是 `Rep` 态射模的**转运**
          结构（`DistribMulAction.toDistribSMul.toSMul`，`Rep/Basic.lean:620` 经
          `hom_injective.module`），与 `map_zsmul` 给出的 `ZSMul.toSMul` 非 defeq
          （v5 实错 269）。**对策**：全程走加法群——`QuotientAddGroup.lift` ＋
          **具名** `HN` 引理（`linYonedaBoundaries_le_ker`）：`lift_mk` 的 rfl 证明
          只对**同一** `HN` 项成立，故 HN 不能写匿名 lambda（`toExtQuotient_apply`
          无法引用）。子模商与加法商类型 defeq（`quotientAddGroupMk_eq_mk := rfl`），
          下游 `mk`／`mk_eq_zero`／`mk_surjective` 照用。
      (f) **`rw` 跨拼写失败（复发两处）**：`rw [extMk_eq_zero_iff] at h'` 与
          `rw [LinearMap.mem_ker]` 皆因 membership／类型在 `implicit` 透明度下
          匹配不到（v5 实错 297/313；与 (a) 同根）。**对策**：改显式 `.mp`／`.mpr`
          应用（默认透明度，rfl 级 defeq，探针实读）。另：`AddMonoidHom.mem_ker`
          的绑定名是 `x`、`LinearMap.mem_ker` 的是 `y`（v6 实错）。
    · 剩余风险：§3 拼装曾于 v1 报 heartbeats 超时（800000，末行 229）——v3 上下文
      全清后重试；若再超时则升 `maxHeartbeats`。

  偏差登记
  ========
    1. 本件**不改动任何既有文件**（含 `scripts/abgv52-lean-crosscheck.py`；
       注册由主循环收口）。
    2. 目标书写 `(A : Rep ℤ H)`，实现取 `Rep.{0} ℤ H`（桥件左腿须 `Ext : Type 0`，
       探针 ①）。
    3. `H`／`trivRep` = 工作区既有定义（经 `ABGV52.C4_ABGV52` import 链可见）。

  0 sorry、0 自造公理；`#print axioms` 闸门见 §5（预期恰
  `[propext, Classical.choice, Quot.sound]`）。
-/
import ABGV52.C4_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory
open CategoryTheory.Abelian

namespace ABGV52

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

-- 局部实例优先级：`Rep.hV2` 对 `ℤ` 的 `Module ℤ ↥X`；`Rep.instLinear`
-- （`groupCohomologyIso` 存储类型所需，同 C4 模式）；`Submodule.module`
-- （对齐 ℤ-模菱形，见头注「墙」(b)）。
attribute [local instance 1500] Rep.hV2
attribute [local instance 1500] Rep.instLinear
attribute [local instance 1500] Submodule.module

-- 桥件专用：`HasExt.{0}` 经 `LocallySmall.{0}` 钉住（探针 ①）。
local instance extBridgeLS : LocallySmall.{0} (Rep.{0} ℤ H) :=
  locallySmall_self (C := Rep.{0} ℤ H)
local instance extBridgeHasExt : HasExt.{0} (Rep.{0} ℤ H) :=
  hasExt_of_enoughProjectives (Rep.{0} ℤ H)

variable {X Y : Rep.{0} ℤ H}

/-! ## §1 记法：助手映射（由体推型；载体 = `ModuleCat` 对象的携带实例） -/

/-- 线性 Yoneda 复形 `Hom(R.complex.X ·, Y)`（逐项 = 态射模）。 -/
abbrev linYonedaComplex (R : ProjectiveResolution X) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  R.complex.linearYonedaObj ℤ Y

/-- 中段短复形 `L.sc' n (n+1) (n+2)`（其同调即 `L.homology (n+1)`）。 -/
abbrev linYonedaSc (R : ProjectiveResolution X) (n : ℕ) :
    ShortComplex (ModuleCat ℤ) :=
  (linYonedaComplex (X := X) (Y := Y) R).sc' n (n + 1) (n + 2)

/-- 余边界映射（推得型 `↑S.X₂ →ₗ[ℤ] ↑S.X₃`；求值 = 前复合 `d (n+2) (n+1) ≫ ·`）。 -/
abbrev linYonedaCoboundary (R : ProjectiveResolution X) (n : ℕ) :=
  (linYonedaSc (X := X) (Y := Y) R n).g.hom

/-- 边界映射（推得型 `↑S.X₁ →ₗ[ℤ] ↑S.X₂`；求值 = 前复合 `d (n+1) n ≫ ·`）。 -/
abbrev linYonedaBoundary (R : ProjectiveResolution X) (n : ℕ) :=
  (linYonedaSc (X := X) (Y := Y) R n).f.hom

/-- 中段余圈子模（推得型 `Submodule ℤ ↑S.X₂`；核元素 `.1` 即 `X (n+1) ⟶ Y`）。 -/
abbrev linYonedaKernel (R : ProjectiveResolution X) (n : ℕ) :=
  LinearMap.ker (linYonedaCoboundary (X := X) (Y := Y) R n)

/-- 上链 → 余圈（即 `moduleCatToCycles`；域 = `↑S.X₁`，余域 = 核子模）。 -/
abbrev linYonedaCochainToKernel (R : ProjectiveResolution X) (n : ℕ) :=
  (linYonedaSc (X := X) (Y := Y) R n).moduleCatToCycles

/-- 边界子模 `im(上链 → 余圈) ⊆ 余圈`。 -/
abbrev linYonedaBoundaries (R : ProjectiveResolution X) (n : ℕ) :=
  LinearMap.range (linYonedaCochainToKernel (X := X) (Y := Y) R n)

/-- 余边界映射求值 = 前复合（探针 ③：符号零偏差）。 -/
lemma linYonedaCoboundary_apply (R : ProjectiveResolution X) (n : ℕ)
    (f : R.complex.X (n + 1) ⟶ Y) :
    linYonedaCoboundary (X := X) (Y := Y) R n f
      = R.complex.d (n + 2) (n + 1) ≫ f := by
  change ((R.complex.linearYonedaObj ℤ Y).d (n + 1) (n + 2)).hom f = _
  rw [ChainComplex.linearYonedaObj_d]
  rfl

/-- 边界映射求值 = 前复合。 -/
lemma linYonedaBoundary_apply (R : ProjectiveResolution X) (n : ℕ)
    (f : R.complex.X n ⟶ Y) :
    linYonedaBoundary (X := X) (Y := Y) R n f
      = R.complex.d (n + 1) n ≫ f := by
  change ((R.complex.linearYonedaObj ℤ Y).d n (n + 1)).hom f = _
  rw [ChainComplex.linearYonedaObj_d]
  rfl

/-- 上链→余圈的坐标式（rfl 级；`codRestrict` 的投影）。 -/
lemma linYonedaCochainToKernel_coe (R : ProjectiveResolution X) (n : ℕ)
    (f : R.complex.X n ⟶ Y) :
    (linYonedaCochainToKernel (X := X) (Y := Y) R n f).1
      = linYonedaBoundary (X := X) (Y := Y) R n f := rfl

/-- 余圈元杀于余边界：`d (n+2) (n+1) ≫ z.1 = 0`（组装子的 `hf` 输入）。 -/
lemma linYonedaKernel_d_eq_zero (R : ProjectiveResolution X) (n : ℕ)
    (z : ↥(linYonedaKernel (X := X) (Y := Y) R n)) :
    R.complex.d (n + 2) (n + 1) ≫ z.1 = 0 := by
  have hz : linYonedaCoboundary (X := X) (Y := Y) R n z.1 = 0 :=
    LinearMap.mem_ker.mp z.2
  rw [linYonedaCoboundary_apply (X := X) (Y := Y) R n z.1] at hz
  exact hz

/-- 桥：同 `f`、不同 `hf` 见证的 `extMk` 相等（rfl 级证明无关；`subst` ＋ `rfl`）。 -/
lemma linYonedaSc_extMk_congr (R : ProjectiveResolution X) (n : ℕ)
    {f f' : R.complex.X (n + 1) ⟶ Y} (h : f = f')
    (hf : R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (hf' : R.complex.d (n + 2) (n + 1) ≫ f' = 0) :
    R.extMk f (n + 2) rfl hf = R.extMk f' (n + 2) rfl hf' := by
  subst h
  rfl

/-! ## §2 组装子与商下降 -/

/-- 组装子：中段余圈 → `Ext X Y (n+1)`（`extMk` 取值于 `X (n+1)` 的余圈）。 -/
def toExtHom (R : ProjectiveResolution X) (n : ℕ) :
    ↥(linYonedaKernel (X := X) (Y := Y) R n) →+ Ext X Y (n + 1) where
  toFun z :=
    R.extMk z.1 (n + 2) rfl (linYonedaKernel_d_eq_zero (X := X) (Y := Y) R n z)
  map_zero' := by
    exact (linYonedaSc_extMk_congr (X := X) (Y := Y) R n
        (Submodule.coe_zero (p := linYonedaKernel (X := X) (Y := Y) R n)) _ _).trans
      (ProjectiveResolution.extMk_zero (X := X) (Y := Y) (R := R) (n := n + 1)
        (n + 2) rfl)
  map_add' z w := by
    exact (linYonedaSc_extMk_congr (X := X) (Y := Y) R n
        (Submodule.coe_add z w) _ _).trans
      (ProjectiveResolution.add_extMk (X := X) (Y := Y) (R := R) z.1 w.1
        (n + 2) rfl _ _).symm

/-- 组装子的定义式（rfl 级）。 -/
lemma toExtHom_apply (R : ProjectiveResolution X) (n : ℕ)
    (z : ↥(linYonedaKernel (X := X) (Y := Y) R n)) :
    toExtHom (X := X) (Y := Y) R n z
      = R.extMk z.1 (n + 2) rfl
          (linYonedaKernel_d_eq_zero (X := X) (Y := Y) R n z) := rfl

/-- 消没性：`toExtHom` 在边界上为零（`extMk_eq_zero_iff` 供余边界分解）。 -/
lemma toExtHom_kill (R : ProjectiveResolution X) (n : ℕ)
    (x : ↥(linYonedaKernel (X := X) (Y := Y) R n))
    (hx : x ∈ linYonedaBoundaries (X := X) (Y := Y) R n) :
    toExtHom (X := X) (Y := Y) R n x = 0 := by
  rw [LinearMap.mem_range] at hx
  obtain ⟨g, hg⟩ := hx
  rw [← hg, toExtHom_apply]
  -- 不用 `rw [extMk_eq_zero_iff]`：目标里 `f` 的拼写是 `↥S.X₂`，rw 在 `implicit`
  -- 透明度下匹配不到（v3 实错 250；见头注「墙」(a)）；改显式 `.mpr` 应用，
  -- 类型检查走默认透明度（rfl 级 defeq，探针 ④）。
  refine (ProjectiveResolution.extMk_eq_zero_iff (X := X) (Y := Y) (R := R)
    (linYonedaCochainToKernel (X := X) (Y := Y) R n g).1 (n + 2) rfl _ n rfl).mpr ?_
  refine ⟨g, ?_⟩
  exact ((linYonedaCochainToKernel_coe (X := X) (Y := Y) R n g).trans
    (linYonedaBoundary_apply (X := X) (Y := Y) R n g)).symm

/-- 良定义性：边界 ⊆ `toExtHom` 的核（`AddMonoidHom` 级；逐元 = `toExtHom_kill`）。

**具名引理**（非匿名 lambda）：`QuotientAddGroup.lift` 是结构，`lift_mk` 的 rfl 证明
只在**同一** `HN` 项下成立——`toExtQuotient_apply` 须引用 def 体里的那一个（v6 设计，
头注「墙」(e)）。 -/
lemma linYonedaBoundaries_le_ker (R : ProjectiveResolution X) (n : ℕ) :
    (linYonedaBoundaries (X := X) (Y := Y) R n).toAddSubgroup
      ≤ (toExtHom (X := X) (Y := Y) R n).ker :=
  fun x hx => (AddMonoidHom.mem_ker (f := toExtHom (X := X) (Y := Y) R n)
    (x := x)).mpr (toExtHom_kill (X := X) (Y := Y) R n x hx)

/-- 商下降：`余圈 ⧸ 边界 →+ Ext X Y (n+1)`（加法群级；良定义 = `linYonedaBoundaries_le_ker`）。

不用 `Submodule.liftQ`（要 `→ₗ[ℤ]`）：`map_smul'` 不可证（「墙」(e)：域继承的 ℤ-作用
是 `Rep` 态射模的转运结构，∦ `ZSMul.toSMul`）。改走 mathlib `liftQ` 自身的底层构造
`QuotientAddGroup.lift`——纯 `AddMonoidHom`，全程无需 ℤ-模。 -/
def toExtQuotient (R : ProjectiveResolution X) (n : ℕ) :=
  QuotientAddGroup.lift ((linYonedaBoundaries (X := X) (Y := Y) R n).toAddSubgroup)
    (toExtHom (X := X) (Y := Y) R n)
    (linYonedaBoundaries_le_ker (X := X) (Y := Y) R n)

/-- 商下降的逐元计算式（在 `mk` 上；`QuotientAddGroup.lift_mk` ＋ 同一 `HN` 项）。 -/
lemma toExtQuotient_apply (R : ProjectiveResolution X) (n : ℕ)
    (z : ↥(linYonedaKernel (X := X) (Y := Y) R n)) :
    toExtQuotient (X := X) (Y := Y) R n (Submodule.Quotient.mk z)
      = toExtHom (X := X) (Y := Y) R n z :=
  QuotientAddGroup.lift_mk ((linYonedaBoundaries (X := X) (Y := Y) R n).toAddSubgroup)
    (linYonedaBoundaries_le_ker (X := X) (Y := Y) R n) z

/-- 单射：差法（相等拉成零）＋ `extMk_eq_zero_iff` 的余边界分解。 -/
lemma toExtQuotient_injective (R : ProjectiveResolution X) (n : ℕ) :
    Function.Injective (toExtQuotient (X := X) (Y := Y) R n) := by
  intro q₁ q₂ h
  have h' : toExtQuotient (X := X) (Y := Y) R n (q₁ - q₂) = 0 := by
    rw [map_sub, h, sub_self]
  have h0 : q₁ - q₂ = 0 := by
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
      (linYonedaBoundaries (X := X) (Y := Y) R n) (q₁ - q₂)
    rw [← hz] at h'
    rw [toExtQuotient_apply, toExtHom_apply] at h'
    -- 不用 `rw [extMk_eq_zero_iff]`：目标里 `f` 的拼写是 `↥S.X₂`，rw 在 `implicit`
    -- 透明度下匹配不到（v5 实错 297；头注「墙」(f)）；显式 `.mp` 走默认透明度。
    obtain ⟨g, hg⟩ := (ProjectiveResolution.extMk_eq_zero_iff (X := X) (Y := Y) (R := R)
      z.1 (n + 2) rfl (linYonedaKernel_d_eq_zero (X := X) (Y := Y) R n z) n rfl).mp h'
    have hmem : z ∈ linYonedaBoundaries (X := X) (Y := Y) R n := by
      rw [LinearMap.mem_range]
      refine ⟨g, ?_⟩
      exact Subtype.ext ((linYonedaCochainToKernel_coe (X := X) (Y := Y) R n g).trans
        ((linYonedaBoundary_apply (X := X) (Y := Y) R n g).trans hg))
    exact hz.symm.trans ((Submodule.Quotient.mk_eq_zero
      (linYonedaBoundaries (X := X) (Y := Y) R n)).mpr hmem)
  exact sub_eq_zero.mp h0

/-- 满射：`extMk_surjective` 给出余圈代表，落回商。 -/
lemma toExtQuotient_surjective (R : ProjectiveResolution X) (n : ℕ) :
    Function.Surjective (toExtQuotient (X := X) (Y := Y) R n) := by
  intro α
  obtain ⟨f, hf, hfa⟩ := ProjectiveResolution.extMk_surjective (X := X) (Y := Y)
    (R := R) α (n + 2) rfl
  -- 不用 `rw [LinearMap.mem_ker]`：membership 实例跨拼写在 `implicit` 透明度下
  -- 匹配不到（v5 实错 313；头注「墙」(f)）；改显式 `.mpr`（默认透明度）。
  have hmem : f ∈ linYonedaKernel (X := X) (Y := Y) R n :=
    (LinearMap.mem_ker (f := linYonedaCoboundary (X := X) (Y := Y) R n)
      (y := f)).mpr (by
        rw [linYonedaCoboundary_apply (X := X) (Y := Y) R n f]
        exact hf)
  refine ⟨Submodule.Quotient.mk
    (⟨f, hmem⟩ : ↥(linYonedaKernel (X := X) (Y := Y) R n)), ?_⟩
  rw [toExtQuotient_apply, toExtHom_apply]
  exact hfa

/-! ## §3 左腿总装 -/

/-- **左腿**：`Ext X Y (n+1) ≃+ ↥(L.homology (n+1))`，
`L = R.complex.linearYonedaObj ℤ Y`。总装 =（商下降）⁻¹ ∘（`H ≅ homology`）⁻¹，
首尾 = `homologyIsoSc'` 取 `.symm`。 -/
noncomputable def extAddEquivLinYonedaHomology (X Y : Rep.{0} ℤ H)
    (R : ProjectiveResolution X) (n : ℕ) :
    Ext X Y (n + 1) ≃+ ↥((R.complex.linearYonedaObj ℤ Y).homology (n + 1)) :=
  ((AddEquiv.ofBijective (toExtQuotient (X := X) (Y := Y) R n)
      ⟨toExtQuotient_injective (X := X) (Y := Y) R n,
        toExtQuotient_surjective (X := X) (Y := Y) R n⟩).symm.trans
    ((linYonedaSc (X := X) (Y := Y) R n).moduleCatHomologyIso.symm.toLinearEquiv.toAddEquiv)).trans
    (((R.complex.linearYonedaObj ℤ Y).homologyIsoSc' n (n + 1) (n + 2)
      ((ComplexShape.up ℕ).prev_eq' rfl)
      ((ComplexShape.up ℕ).next_eq' rfl)).symm.toLinearEquiv.toAddEquiv)

/-! ## §4 主声明：桥 -/

/-- **桥**：`Ext trivRep A 2 ≃+ ↥(groupCohomology A 2)`。左腿取 `X := trivRep`、
`Y := A`、`R := barResolution`、`n := 1`；右腿 = 库内 `groupCohomologyIso` 反向。 -/
noncomputable def extTwoTriv_addEquiv_coh2 (A : Rep.{0} ℤ H) :
    Ext trivRep A 2 ≃+ ↥(groupCohomology A 2) :=
  (extAddEquivLinYonedaHomology trivRep A (Rep.barResolution ℤ H) 1).trans
    ((groupCohomologyIso A 2 (Rep.barResolution ℤ H)).toLinearEquiv.toAddEquiv.symm)

/-! ## §5 `#print axioms` 闸门（预期恰 `[propext, Classical.choice, Quot.sound]`） -/

#print axioms linYonedaCoboundary_apply
#print axioms linYonedaBoundary_apply
#print axioms linYonedaCochainToKernel_coe
#print axioms linYonedaKernel_d_eq_zero
#print axioms linYonedaSc_extMk_congr
#print axioms toExtHom
#print axioms toExtHom_apply
#print axioms toExtHom_kill
#print axioms linYonedaBoundaries_le_ker
#print axioms toExtQuotient
#print axioms toExtQuotient_apply
#print axioms toExtQuotient_injective
#print axioms toExtQuotient_surjective
#print axioms extAddEquivLinYonedaHomology
#print axioms extTwoTriv_addEquiv_coh2

end

end ABGV52
