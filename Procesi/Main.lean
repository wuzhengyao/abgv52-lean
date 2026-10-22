/-
  Procesi —— **接线层（Main）**：H2 的消费面 ＋ 射程登记

  本件做三件事：
    §1 `M ⊕ U` 上的 `SMulCommClass`（`H`-作用与 `ℤ`-纯量交换）——接线所需的最后一枚实例；
    §2 ★ **H2 ＋ 第二层 ⟹ `Z_H(F,9)` 于 `F(M|_H)^H` 有理**（＝论文 `rem:procesi-geometric`
       的"有理性"断言，在 `Z` 侧闭合）；
    §3 **射程登记**：H2 自 R774 起**已机检**（`UDKScalarMem.h2_unconditional`，具名假设清零），
       其非空洞性（结构束可居住）自 R779 起亦机检（`Nonvacuous.nonempty_genericDivisionData_two_nine`
       ＋ `h2_unconditional_nonvacuous`）；第一层（`Lattice.lean`）与第二层（`Lenstra.lean`）此前已机检。

  **诚实性口径（提示词 §7 红线）**：R774 之前，第三层（Procesi 中心定理）未机检，`zH_rational_of_procesi`
  的前提就是 H2、故为**条件定理**。**R774–R779 之后**，H2 与其非空洞性均已在 Lean 侧闭合
  （`UDKScalarMem.lean` ＋ `Nonvacuous.lean`），故 `zH_rational_of_procesi` 的 H2 前提**可以由
  `h2_unconditional` 供给**；但本件（接线层）自身的形态仍受下文"形态注"约束（`≃+*` 形）。
  **仍未证（均不在 H2 关键路径）**：Z 半、`M_n(K')^N ⊆ UDK'`、`UDKTensorHypK'`。

  形态注：`IsRational` 的 `≃ₐ` 形要求基域 `↥(latticeInvariantsAlg F H M)` 与顶域
  `↥(latticeInvariantsAlg F H (M⊕U))` 之间有 `Algebra` 实例（即一条**包含**
  `F(M|_H)^H ↪ F((M⊕U)|_H)^H`）；该包含尚未搭（两端分处不同的函数域类型）。
  故本件用工程既有约定：`ProcConsume` 的 `ProcesiHypStable` 即 `Z ≃+* K(t₁,…,t_k)` 形
  （`ProcConsume_ABGV52.lean:69` 逐字："`ProcesiHypStable`：`Z ≃+* K(t₁,…,t_k)`，
  无代数相容性"）。 `≃ₐ` 形是本层的**下一件**（见 `wiki/log.md`）。
-/
import Procesi.Lenstra
import Procesi.Lattice
import Procesi.Statement

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

set_option maxHeartbeats 1600000

/-! ## §1 `M ⊕ U` 上的 `SMulCommClass`（接线所需的最后一枚实例） -/

/-- `H`-作用与 `ℤ`-纯量在 `M ⊕ U` 上交换（逐分量，经 `Prod.ext`）。

**为何需要**：`ProcesiSubgroupHyp`（＝ H2 的 `H` 层形态）以 `[SMulCommClass H ℤ V]`
为参数；`ABGV52.ProcHyp` 的头注声称它由 `AddGroup.int_smulCommClass'` 自动合成，
但**实测类型类搜索失败**（`Mp2 p` 上 `SMul`／`Module` 的实例菱形）⟹ 本件显式给。 -/
instance smulCommClass_Mp2 : SMulCommClass (P.Hp 3) ℤ (ProcLat.Mp2 3) where
  smul_comm h n x := by
    refine Prod.ext ?_ ?_
    · exact SMulCommClass.smul_comm h n x.1
    · exact SMulCommClass.smul_comm h n x.2

/-! ## §2 ★ H2 ＋ 第二层 ⟹ `Z_H(F,9)` 于 `F(M|_H)^H` 有理 -/

/-- ★★★ **接线定理（本工作区的主交付）**：给定 H2 的 `H` 层形态
（`Z ≃ₐ[F] F((M ⊕ U)|_H)^H`，即 `ProcesiSubgroupHyp F H (M ⊕ U) Z`），
则 `Z` 于 `F(M|_H)^H` **有理**——且见证是**显式**的：`k` 个变元的有理函数域。

**读法**：第二层（`m3_procesi`，**无条件**）说的是
`F((M⊕U)|_H)^H ≅ F(M|_H)^H(t₁,…,t_k)`；本定理把它沿 H2 的同构搬到 `Z` 上。
逐字对照论文 `rem:procesi-geometric`：

> The field `Z_H(F,9)` … is *rational* over `F(M|_H)^H`.

**⟹ 论文这一层的有理性断言在 `Z` 侧闭合**（条件：H2；H2 的射程见 §3）。 -/
theorem zH_rational_of_procesi (F : Type) [Field F] (Z : Type) [Field Z] [Algebra F Z]
    (h : ProcesiSubgroupHyp F (P.Hp 3) (ProcLat.Mp2 3) Z) :
    ∃ k : ℕ, Nonempty (Z ≃+* EM.rationalFunctionField
      ↥(EM.latticeInvariants F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) k) := by
  obtain ⟨e⟩ := h
  obtain ⟨k, ⟨e2⟩⟩ := m3_procesi F
  exact ⟨k, ⟨e.toRingEquiv.trans
    ((EM.invariantsRingEquiv F (P.Hp 3) (ProcLat.Mp2 3)).symm.trans e2)⟩⟩

/-- **H2 的 `H` 层形态 ⟹ 抽象识别形**（`AGPR2020` `thm:14.4.4` 的实例化，
`H` 层版）：把具名假设接到它的**已出版母版**上。

**为何需要**：H2 若未竟，它的内容仍是 `AGPR2020` 的已出版定理；本件把"我们的 H2
⟹ 母版形状"机检，使论文可以如实写"H2 的内容即 `AGPR2020` §14.4.1"。 -/
theorem isInvariantFieldModel_of_procesiSubgroupHyp (F : Type) [Field F] (Z : Type)
    [Field Z] [Algebra F Z]
    (h : ProcesiSubgroupHyp F (P.Hp 3) (ProcLat.Mp2 3) Z) :
    IsInvariantFieldModel F Z := by
  obtain ⟨e⟩ := h
  exact ⟨P.Hp 3, inferInstance, ProcLat.Mp2 3, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨e⟩⟩

/-! ## §3 三层打包（**不作"已消去 H2"、也不作"射程已核"的声称**） -/

/-- **三层打包（**不是**射程验证器）**：把本工作区的三条**已证**命题打成一个 `Prop`。

**⚠ 读法（2026-10-18 外审后修正）**：本谓词
 (a) **三支全是已证命题的打包**，不含任何"射程"判定——第三支
     `ProcesiSubgroupHyp → IsInvariantFieldModel` 是 **∃-引入的平凡接线**，
     其真值与 H2 的真假**无关**；
 (b) **不含**本层唯一的**形态缺口**（`≃+*` vs `≃ₐ`；见 `Procesi/Alg.lean` 与
     `wiki/log.md` 的登记）⟹ **不得**把 `procesiLayers_holds` 的绿读作"射程闭合"。

* `lattice_ok`：第一层（格层）全部机检 —— `Lattice.lean`（18 条读数）；
* `lenstra_ok`：第二层（Lenstra）全部机检，**无条件** —— `Lenstra.lean` 的 `m3_procesi`；
* `procesi_named`：第三层（Procesi 中心定理）**仍是具名假设** —— 它就是
  `ProcesiSubgroupHyp`（其母版 ＝ `AGPR2020` `thm:14.4.4`，见
  `isInvariantFieldModel_of_procesiSubgroupHyp`）。**本件不声称已证**。

⟹ 提示词 §0 完成判据第 4 条取"退而求其次"支：H2 被**精确化到最忠实形式**
（`Z ≃ₐ[F] F((M⊕U)|_H)^H`，论文逐字），并成为**唯一**具名假设；§2 的第一／二层全部机检。 -/
def ProcesiLayers (F : Type) [Field F] : Prop :=
  -- (1) 第一层：`M ⊕ U` 的秩账 73 + 9 = 82（格层闭合）
  (Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ)
      + Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3)
      = Module.finrank ℚ (ProcLat.Mp2 3 ⊗[ℤ] ℚ))
  -- (2) 第二层：Lenstra 有理性的无条件见证存在
  ∧ (∃ k : ℕ, Nonempty (↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3)) ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (P.Hp 3)
        ↥(LinearMap.ker (G.phiFun 3))) k))
  -- (3) 第三层：H2 的忠实陈述（**具名假设**，不作定理）
  ∧ (∀ (Z : Type) [Field Z] [Algebra F Z],
      ProcesiSubgroupHyp F (P.Hp 3) (ProcLat.Mp2 3) Z → IsInvariantFieldModel F Z)

/-- 三层打包**为真**（三支各自已证；**不**表示 H2 已证，也**不**表示射程已核）。 -/
theorem procesiLayers_holds (F : Type) [Field F] : ProcesiLayers (F := F) :=
  ⟨rank_account_add, m3_procesi F, fun Z _ _ h => isInvariantFieldModel_of_procesiSubgroupHyp F Z h⟩

/-- 类型锁：三层打包的外形（一旦改动立即编译失败）。 -/
theorem procesiLayers_typeLock (F : Type) [Field F] :
    (ProcesiLayers (F := F)) =
      ((Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ)
          + Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3)
          = Module.finrank ℚ (ProcLat.Mp2 3 ⊗[ℤ] ℚ))
        ∧ (∃ k : ℕ, Nonempty (↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3)) ≃+*
            EM.rationalFunctionField ↥(EM.latticeInvariants F (P.Hp 3)
              ↥(LinearMap.ker (G.phiFun 3))) k))
        ∧ (∀ (Z : Type) [Field Z] [Algebra F Z],
            ProcesiSubgroupHyp F (P.Hp 3) (ProcLat.Mp2 3) Z → IsInvariantFieldModel F Z)) :=
  rfl

/-! ## §4 公理闸门 -/

#print axioms smulCommClass_Mp2
#print axioms zH_rational_of_procesi
#print axioms isInvariantFieldModel_of_procesiSubgroupHyp
#print axioms procesiLayers_holds
#print axioms procesiLayers_typeLock

end

end Procesi
