/-
  ABGV-5.2 —— ③ C″ 消费端接线（Procesi 档）
  ∝-re-scope（2026-10-10，论文第四十四改后）：由「`thm:retract` 的装配」
  改定位为「**开放问句（Z_H(F,9) 的 retract 有理性）的条件装配载体**」。

  ⚠ ∝-re-scope 横幅（读本件前必读）
  =================================
  【2026-10-11 追加更正（主循环）】论文 2026-10-11 版**已把该开放问句判否** ✓：
  `rem:retract-open` 已改名并改写为 `rem:retract-comparison`（仅保留 \(F(V)^H\) 与
  \(F(M|_H)^H\) 的对比论证），其位置由**新增定理** `thm:not-retract-rational`（4.13）
  取代 —— 「\(Z_H(F,9)\) 非 retract rational over \(F\)（char 0）」✓，另有新增判据
  `thm:retract-criterion`（4.12，\(F(M)^G\) RR \(\iff\) flabby 类可逆）✓。
  该结论走的是**另一条路**（flasque 消解商不 coflasque 的指数障碍，见论文 4.13 的证明），
  **不**经由本文件装配的旧路线 ✓。⟹ 本文件以下 ∝-re-scope 横幅中「判为开放」的措辞**已过时** ⚠，
  本文件保留为**旧路线的条件装配留痕** ✓；其结论**不得**引作论文主张 ✓（同上）。
  论文第四十四改撤下 `thm:retract`（现为 `rem:retract-open`，tex :1582）：
  「Whether \(Z_H(F,9)\) is retract rational over \(F\) is left open here.」
  ——Z_H(F,9) 的 retract 有理性**判为开放**；且被撤证法的第 ② 步
  「\(F(V)^H \cong F(M|_H)^H\)」被 Fischer 反证（rem:retract-open 逐字：
  \(F \ni \zeta_3\) 时线性侧 \(F(V)^H\) 纯超越，而单项侧 \(F(M|_H)^H\)
  非稳定有理）。⟹ 本件**不再是论文主张的形式化**，re-scope 为开放问句的
  **条件装配载体**：
    * 输入 1（C″，`Z ≃ₐ[K] K(t₁,…,t_k)`）：论文现文**仍断言**（tex :1449
      「Recall that \(Z_H(F,9)\) is rational over \(F(M|_H)^H\)」；
      p 档 :1699 同形）。
    * 输入 2（`SaltmanHypU`：K′ RR）＝**开放问句的 K′ 侧**——旧路线称该输入
      由 Cor 3.13＋识别 ② 供给；识别既假，此输入不再由论文供给
      （**也不再被否认**：论文现文对 K′ 侧 RR 无断言）。
    * 主定理 =「K′ 在 F 上 RR ⟹ Z 在 F 上 RR」（旧路线第 ④ 步「有理扩张
      传递」的库内严格版，`SaltmanRatOver.isRetractRational_of_isRationalOver`）。
  **合法的 Cor 3.13 论文实例 = 正则表示场**（rem:retract-open 对照句：
  \(F(V)^H\)，\(V = F[H]\)——线性形式、无需识别）；本件对 `base p F`
  （单项场）的 Saltman 实例化**仅作条件装配的输入位**保留，不代表论文内容。
  下游使用限制：本件结论**不得**引作「论文已证 Z_H(F,9) RR」；此外仍受
  §9.9 的 P 档 ∝-stale 限制（不涉本件语句，见 audit §9）。

  被撤路线的论文原文（pre44；供对照）
  ==================================
  论文旧 `thm:retract`（旧 :1541–1560；存档 `raw/ABGV-5.2-resolution.pre44.tex`）：
  「The field \(Z_H(F,9)\) is retract rational over \(F\).」
  其证明四步（**② 已判假——Fischer 反证，见横幅；③ 的适用性随 ② 失效**）：
    ① C″：`Z_H(F,9)` 在 `K := F(M|_H)^H` 上**有理**——`rem:procesi-geometric`
       （tex :718 起）：「it is \emph{rational} over \(F(M|_H)^H\)」（经
       Lenstra1974, Prop 1.4 作用在置换模 \(U|_H\) 上）；
    ② `K ≅ F(V)^H`（\(V = M|_H \otimes_{\mathbb{Z}} F\)）——**已判假**（44 改）；
    ③ Saltman 1984 Cor 3.13（\(A = H\)，exp 奇 ⟹ 2^r 条件空）⟹ `K` 在 `F` 上
       retract rational——**对单项场 K 的此实例化随 ② 失效**；合法实例 = 正则场；
    ④ 「Hence \(F(V)^H\), and therefore its rational extension \(Z_H(F,9)\),
       is retract rational over \(F\).」——「有理扩张保持 retract 有理性」。

  Lean 侧本件做什么（消费端接线；∝-re-scope 后口径）
  =================================================
  本件把第 ④ 步做成**主定理**，第 ① 步与「第 ③ 步的结论（K′ RR）」做成
  **接口输入**（② **不在件内**——旧路线中它连接 ①③，今判假；消费端不经过它）：

    * **输入 1（C″，K-线性强化形）**：`ProcesiHypStableK K Z` —— `Z ≃ₐ[K] K(t₁,…,t_k)`。
      基域 `K` 取 C″ 的具体基 `base p F := ↥(latticeInvariants F (Hp p) (ker φ))`
      （`↥(Subfield …)` 的 `Field` 实例由 `SubfieldClass.toField` 合成——见 §1 两条
      `inferInstance` 见证）。
    * **输入 2（Saltman 接口形）**：`SaltmanHypU K RRet`（忠实性输入 ⟹ 结论），
      即 `Saltman_ABGV52.lean` 的 `SaltmanHyp` 的 **universes 泛化**（Type-0 → Type u，
      外形逐字相同，`rfl` 锁定）；忠实性由 F1 的 `M_H_rho_injective` 填槽
      （`thm_retract_saltmanU`）。
    * **证明项**：File 1（`SaltRatOver_ABGV52.lean`）的双塔引理
      `isRetractRational_of_isRationalOver`（`IsRationalOver L K` ＋
      `IsRetractRational F L` ⟹ `IsRetractRational F K`）——即第 ④ 步的库内定理版。

  与 `ProcHyp_ABGV52.lean` 的关系：那里登记的 C″ 是**环同构形**
  （`ProcesiHypStable`：`Z ≃+* K(t₁,…,t_k)`，无代数相容性）。本件的输入是它的
  **K-线性强化形**（`≃ₐ[K]`），桥引理给出方向链
  `K-线性 ⟹ F-线性 ⟹ 环同构形`（§2），故消费端输入严格强于已登记外形；
  反方向（环同构 ⟹ 代数相容）不可证、也不需要——登记为接口事实（非静默弱化）。
  论文的 `rem:procesi-geometric` 给出的正是「在 `K` 上有理」，即 K-线性形——
  故本件的输入形式 = 论文实际形式，环同构形只是其弱化。

  接口登记与偏离（逐条）
  ====================
  ① **`[Algebra F (base p F)]` 取显式实例约束**：`Algebra F ↥(Subfield …)` **不能**由
     实例搜索合成（同 D9:45 已登记的「`Subfield.closure` 不含 `F` 的像」同型；
     实测 `inferInstance` 失败）。它是几何设置的环境结构（`K = F(M|_H)^H` 自带
     `F`-代数结构），作为主定理的实例假设传入——这是**数据**，不是弱化。
  ② **`SaltmanHypU` = Type-0 `SaltmanHyp` 的 universes 泛化**（泛化，非弱化）：
     定义体逐字相同（`Function.Injective M_H_rep.ρ → RRet K`），`rfl` 型锁对照
     Type-0 形（`saltmanHypU_typeLock`），并给 Type-0 兼容定理
     （`saltmanHypU_compat` = 原 `thm_retract_Saltman` 同陈述）。
  ③ **`Z` 抽象传入**：KB 不构造 `Z_H(F,9)`（同 R1 件与 S5 对 EM 判据的处置），
     `Z : Type u` 为参数、`[Algebra F Z]`／`[Algebra (base p F) Z]`／
     `[IsScalarTower F (base p F) Z]` 为环境数据。
  ④ **条件层与几何识别并入接口**（照 `Saltman_ABGV52.lean` 头注口径，用户
     2026-09-30 裁定）：Saltman 接口的其余前提（exp 奇／2^r 条件空、char 0、几何
     识别）压缩在 `SaltmanHyp` 外形内；条件层**本体**由 `SaltCond_ABGV52.lean`
     （`saltmanCondition_H`）独立交付，[23] 残差由 `SaltGeneric_ABGV52.lean` 登记
     ——本件不重开。
  ⑤ **H-等变层**：本件只锁定**不变层级**的 C′/C″（同 ProcHyp）；`H`-等变同构
     **未**在 Lean 中构造。论文 pre33 版 `prop:faithful-MH` 首证曾含 H-等变句、
     第三十三改已移除 ⟹ 本件与论文现文本路线一致。
  ⑥ **旧 `G.ProcesiHyp`（`GThm_ABGV52.lean:58`）已被取代**：其核只取 `↥(ker φ)`
     （秩 73，缺 `U = ℤ[Ω]` 分量），C′ 修正后为假形状；更正形在 `ProcHyp_ABGV52.lean`
     （`ProcesiHypExact`／`ProcesiHypStable`）。本件**不**引用旧外形；下游
     `G2p.ZH_iso` 链本轮未触碰（M7/M8 决策）。
  ⑦ **路线对齐（∝-re-scope 后口径）**：pre44 论文文本（旧 `thm:retract` 引
     `rem:procesi-geometric` 的「rational over \(F(M|_H)^H\)」＋ Saltman Cor 3.13
     ＋ 有理扩张传递）与本 Lean 路线（`ProcesiHypStableK`（= C″ K-线性）＋
     `SaltmanHypU` ＋ 双塔引理）曾**同路线、路线级偏差 0**；**44 改后该对齐终止**
     （`thm:retract` 撤下）——现文对应 = 顶横幅（C″ 仍断言〔tex :1449／:1699〕；
     K′ RR 输入为开放问句侧）；技术级字面偏差见 ①②③。

  **无 sorry、无自造公理**（公理闸门见 §6：逐条 `#print axioms` 均为
  `[propext, Classical.choice, Quot.sound]`）。
-/
import ABGV52.SaltRatOver_ABGV52
import ABGV52.ProcHyp_ABGV52
import ABGV52.Saltman_ABGV52

open ABGV52.P (Hp)

universe u

namespace ABGV52.ProcConsume

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. C″ 的基域与两种线性化外形

  `base p F := F(M|_H)^H = ↥(latticeInvariants F (Hp p) ↥(ker (phiFun p)))`。
  其 `Field` 实例由 `SubfieldClass.toField` 合成（两条 `inferInstance` 见证）；
  `Algebra F (base p F)` **无**实例（头注偏离 ①），故全程显式传入。 -/

/-- C″ 基域 `K = F(M|_H)^H`（论文**旧** `thm:retract` 的 `K`；现文出处：
tex :1449／:1699 的 `F(M|_H)^H`；∝-re-scope 见顶横幅）。 -/
abbrev base (F : Type u) [Field F] : Type u :=
  ↥(EM.latticeInvariants F (Hp p) ↥(LinearMap.ker (G.phiFun p)))

noncomputable example (F : Type u) [Field F] : Field (base p F) := inferInstance
noncomputable example (F : Type u) [Field F] : CommRing (base p F) := inferInstance

/-- **C″（K-线性形）**：`Z` 在 `K` 上有理（`Z ≃ₐ[K] K(t₁,…,t_k)`）。
论文 `rem:procesi-geometric` 的「rational over \(F(M|_H)^H\)」的逐字形式化；
与 `EM.IsRational` 定义级等价（`procesiHypStableK_typeLock`）。 -/
def ProcesiHypStableK (K : Type u) [Field K] (Z : Type u) [Field Z]
    [Algebra K Z] : Prop :=
  ∃ k : ℕ, Nonempty (Z ≃ₐ[K] EM.rationalFunctionField K k)

/-- **类型锁定（C″ K-线性）**：外形一旦改动，本 `rfl` 立即编译失败；
同时锁定与 `EM.IsRational` 的定义级等价。 -/
theorem procesiHypStableK_typeLock (K : Type u) [Field K] (Z : Type u) [Field Z]
    [Algebra K Z] : ProcesiHypStableK K Z = EM.IsRational K Z := rfl

/-- **C″（F-线性形）**：基域取 `base p F`，`Z` 在 `F` 上代数同构于 `K(t₁,…,t_k)`。
介于 K-线性形与环同构形之间（K-线性 ⟹ 本形，见 `procesiHypStableK_to_F`）。 -/
def ProcesiHypStableF (F : Type u) [Field F] [Algebra F (base p F)]
    (Z : Type u) [Field Z] [Algebra F Z] : Prop :=
  ∃ k : ℕ, Nonempty (Z ≃ₐ[F] EM.rationalFunctionField (base p F) k)

/-- **类型锁定（C″ F-线性）**：外形一旦改动，本 `rfl` 立即编译失败。 -/
theorem procesiHypStableF_typeLock (F : Type u) [Field F] [Algebra F (base p F)]
    (Z : Type u) [Field Z] [Algebra F Z] :
    ProcesiHypStableF p F Z = ∃ k : ℕ, Nonempty (Z ≃ₐ[F]
      EM.rationalFunctionField (base p F) k) := rfl

/-! ## 2. 桥：线性化方向链（K-线性 ⟹ F-线性 ⟹ 环同构形）

  与 `ProcHyp_ABGV52.lean` 已登记的 C″ 环同构形（`ProcesiHypStable`）的接口对账：
  消费端输入（K-线性）**严格强于**登记外形；每一环皆有库内定理。 -/

/-- 桥：K-线性形 vs File 1 的 `IsRationalOver`（定义级等价；消费入口）。 -/
theorem procesiHypStableK_isRationalOver (K : Type u) [Field K] (Z : Type u) [Field Z]
    [Algebra K Z] : ProcesiHypStableK K Z ↔ IsRationalOver K Z := Iff.rfl

/-- 桥：K-线性 ⟹ F-线性（`AlgEquiv.restrictScalars`；用 `IsScalarTower F base Z`）。 -/
theorem procesiHypStableK_to_F (F : Type u) [Field F] [Algebra F (base p F)]
    (Z : Type u) [Field Z] [Algebra F Z] [Algebra (base p F) Z]
    [IsScalarTower F (base p F) Z]
    (h : ProcesiHypStableK (base p F) Z) : ProcesiHypStableF p F Z := by
  obtain ⟨k, ⟨e⟩⟩ := h
  exact ⟨k, ⟨e.restrictScalars F⟩⟩

/-- 桥：F-线性 ⟹ `ProcHyp.ProcesiHypStable`（环同构形，C″ 登记形；
`AlgEquiv.toRingEquiv`）。 -/
theorem procesiHypStableF_to_procesiHyp (F : Type u) [Field F] [Algebra F (base p F)]
    (Z : Type u) [Field Z] [Algebra F Z]
    (h : ProcesiHypStableF p F Z) : ProcHyp.ProcesiHypStable p F Z := by
  obtain ⟨k, ⟨e⟩⟩ := h
  exact ⟨k, ⟨e.toRingEquiv⟩⟩

/-- 桥（复合）：K-线性 ⟹ `ProcHyp.ProcesiHypStable`。 -/
theorem procesiHypStableK_to_procesiHyp (F : Type u) [Field F] [Algebra F (base p F)]
    (Z : Type u) [Field Z] [Algebra F Z] [Algebra (base p F) Z]
    [IsScalarTower F (base p F) Z]
    (h : ProcesiHypStableK (base p F) Z) : ProcHyp.ProcesiHypStable p F Z :=
  procesiHypStableF_to_procesiHyp p F Z (procesiHypStableK_to_F p F Z h)

/-! ## 3. Saltman 接口的 universes 泛化（`SaltmanHypU`）

  `Saltman_ABGV52.lean` 的 `SaltmanHyp (K : Type) (RRet : Type → Prop)` 钉在
  Type 0；消费端基域 `base p F : Type u`。本节的 `SaltmanHypU` 是**逐字同体**的
  泛化（偏离 ②；泛化非弱化：`rfl` 型锁 ＋ Type-0 兼容定理）。 -/

/-- **Saltman 1984 Cor 3.13 的具名假设（universes 泛化）**：忠实性输入
（`Function.Injective M_H_rep.ρ`）⟹ `RRet K`。 -/
def SaltmanHypU (K : Type u) (RRet : Type u → Prop) : Prop :=
  Function.Injective M_H_rep.ρ → RRet K

/-- **类型锁定（兼容性）**：`SaltmanHypU` 在 Type-0 实例化 = `SaltmanHyp`（逐字同体）。 -/
theorem saltmanHypU_typeLock (K : Type) (RRet : Type → Prop) :
    SaltmanHypU K RRet = SaltmanHyp K RRet := rfl

/-- 接线：忠实性由 F1 的 `M_H_rho_injective` 填槽（同 `thm_retract_Saltman`，
universes 泛化版）。 -/
theorem thm_retract_saltmanU (K : Type u) (RRet : Type u → Prop)
    (hS : SaltmanHypU K RRet) : RRet K := hS M_H_rho_injective

/-- 兼容定理：Type-0 形（原 `SaltmanHyp`）经泛化接口复得——原接线不失效。 -/
theorem saltmanHypU_compat (K : Type) (RRet : Type → Prop) (hS : SaltmanHyp K RRet) :
    RRet K := thm_retract_saltmanU K RRet hS

/-! ## 4. 主定理（被撤路线 pre44 `thm:retract` 的消费端装配；
  ∝-re-scope 后 = 开放问句的条件载体，见顶横幅） -/

/-- 被撤路线的第 ③ 步形状——**∝-re-scope：对单项场 `K = F(M|_H)^H` 的此
实例化不再是论文内容**（识别 ② 被 Fischer 反证；Cor 3.13 的合法论文实例
= 正则表示场 `V = F[H]`，见 `rem:retract-open`）。本定理保留为**条件装配**
（`SaltmanHypU` 具名假设的消费接线；条件层已并入接口，见头注偏离 ④）。 -/
theorem saltman_base_retract (F : Type u) [Field F] [Algebra F (base p F)]
    (hSalt : SaltmanHypU (base p F) (fun _ => IsRetractRational F (base p F))) :
    IsRetractRational F (base p F) :=
  thm_retract_saltmanU _ _ hSalt

/-- **被撤路线（pre44 `thm:retract`）的消费端主定理；∝-re-scope 后 = 开放
问句的条件载体**：设
  * `Z` 在 `K = F(M|_H)^H` 上有理（输入 1，C″ K-线性形；**论文现文仍断言**，
    tex :1449）；
  * Saltman 接口成立（输入 2；**此即 K′ 侧开放输入**：K′ 在 `F` 上 retract
    rational——论文现文无断言，见顶横幅），
  则 `Z` 在 `F` 上 retract rational（旧路线第 ④ 步；证明经 File 1 的双塔引理
  `isRetractRational_of_isRationalOver`）。**不得**引作「论文已证 Z_H(F,9) RR」。 -/
theorem thm_retract_procesiStable (F : Type u) [Field F] [Algebra F (base p F)]
    (Z : Type u) [Field Z] [Algebra (base p F) Z] [Algebra F Z]
    [IsScalarTower F (base p F) Z]
    (hRat : ProcesiHypStableK (base p F) Z)
    (hSalt : SaltmanHypU (base p F) (fun _ => IsRetractRational F (base p F))) :
    IsRetractRational F Z :=
  isRetractRational_of_isRationalOver
    ((procesiHypStableK_isRationalOver (base p F) Z).mp hRat)
    (saltman_base_retract p F hSalt)

/-- **判别力探针（端到端点火）**：取 `Z := K(t₁,…,t_n)`（C″ 的右端本身）、
Saltman 侧取「`K` retract rational」的现成见证——主定理在满输入上给出
「有理扩张 `K(t₁,…,t_n)` 仍在 `F` 上 retract rational」（旧路线第 ④ 步形状；
探针——**不代表论文结论**；同时是 File 1 双塔引理在 Procesi 数据上的落地）。 -/
theorem thm_retract_procesiStable_probe (F : Type u) [Field F] [Algebra F (base p F)]
    (hRet : IsRetractRational F (base p F)) (n : ℕ) :
    IsRetractRational F (EM.rationalFunctionField (base p F) n) :=
  thm_retract_procesiStable p F (EM.rationalFunctionField (base p F) n)
    ⟨n, ⟨AlgEquiv.refl (R := base p F) (A₁ := EM.rationalFunctionField (base p F) n)⟩⟩
    (fun _ => hRet)

/-! ## 5. 非空洞探针（L1：各输入类均非空） -/

/-- 探针（输入 1，K-线性形）：取 `Z := K(t₁,…,t₀) ≅ K`，恒等同构即实例。 -/
theorem procesiHypStableK_satisfiable (K : Type u) [Field K] :
    ProcesiHypStableK K (EM.rationalFunctionField K 0) :=
  ⟨0, ⟨AlgEquiv.refl (R := K) (A₁ := EM.rationalFunctionField K 0)⟩⟩

/-- 探针（输入 1，F-线性形）：同上，基域取 `base p F`。 -/
theorem procesiHypStableF_satisfiable (F : Type u) [Field F] [Algebra F (base p F)] :
    ProcesiHypStableF p F (EM.rationalFunctionField (base p F) 0) :=
  ⟨0, ⟨AlgEquiv.refl (R := F) (A₁ := EM.rationalFunctionField (base p F) 0)⟩⟩

/-- 探针（输入 2）：取 `RRet := fun _ => True`，假设类非空。 -/
theorem saltmanHypU_satisfiable (K : Type u) : SaltmanHypU K (fun _ => True) :=
  fun _ => trivial

/-! ## 6. 公理闸门 -/

#print axioms ProcesiHypStableK
#print axioms procesiHypStableK_typeLock
#print axioms ProcesiHypStableF
#print axioms procesiHypStableF_typeLock
#print axioms procesiHypStableK_isRationalOver
#print axioms procesiHypStableK_to_F
#print axioms procesiHypStableF_to_procesiHyp
#print axioms procesiHypStableK_to_procesiHyp
#print axioms SaltmanHypU
#print axioms saltmanHypU_typeLock
#print axioms thm_retract_saltmanU
#print axioms saltmanHypU_compat
#print axioms saltman_base_retract
#print axioms thm_retract_procesiStable
#print axioms thm_retract_procesiStable_probe
#print axioms procesiHypStableK_satisfiable
#print axioms procesiHypStableF_satisfiable
#print axioms saltmanHypU_satisfiable

end ABGV52.ProcConsume
