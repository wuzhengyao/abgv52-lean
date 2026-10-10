/-
  ABGV-5.2 —— **本体形式化 B · [23] 残差具名**（Saltman 1982，「generic object」）

  背景（蓝图 `wiki/proj-ABGV52-formalize-saltman.md` §1.1 步骤 14／§3.1 M5／§4.1）
  ==============================================================================
  Saltman1984 Cor 3.13 的证明链在步骤 14 处调用**外部输入 [23]**（Saltman 1982,
  Adv. in Math. 43, 250–283：「A 交换、F 满足 2^r 条件时 generic object 存在」——
  蓝图 §1.2：**2^r 条件只在此步进入**）。~~KB 无 [23] 源件~~ **已入 KB（2026-10-10 用户供源：`raw/Saltman1982.{tex,pdf}`，
  citekey `Saltman1982`，receipt `2b3ed6f6…`；文献笔记 [[1982-Saltman-generic-galois]]）**——
  pinpoint = [23] 印 p. 257／p. 265／pp. 274–275／p. 279 此后库内可核（⚠ 印刷页偏移未核）；
  2^r 条件句的源 = `theorem-2-1`（F(ρ(r))/F 循环）。具名形暂维持（内容消费待复核波）。⚠ 页偏移登记：
  Saltman1984 的印刷页 = PDF 页 **+ 164**（任务书原写「+220」有误——那是
  Saltman1987 的偏移）。

  **路线对齐注记（头注必写项）**
  ==============================
  * 论文侧该定理的自然语言「证明」= **无**——纯外部引用（Saltman1984 Cor 3.13）。
  * Lean 路线 = Salt* 内部工程（M1/M2 已交付）＋条件层（`SaltCond_ABGV52.lean`）
    ＋本件 [23] 残差具名——与论文引用结构对齐（同样把它**当假设用**）。
  * **偏离登记**：本波**不触碰** M3–M6 工程（不假装已证）。具体地——
    - M3（局部提升判据：thm1.3(c)＋thm3.8/3.9＋cor3.10(a)）：**未做**；
    - M4（§1 范畴语言：E(G)-类／lifting property／generic object）：**未做**；
    - M6（装配：thm3.12(b)＋端点识别）：**未做**。
    ⟹ 本件**不**声称「`GenericObjectExists ⟹ SaltmanHyp`」的**数学装配**已完成；
    该装配只在 M3/M4/M6 完成后才可得。本件做的是**重量分解**（见下表）与
    **H-档分解恒等式**（形状层，两个方向分别消耗 SaltCond 与 F1 的库内定理）。

  本件内容：`SaltmanHyp` 黑箱的「重量分解对账」
  =============================================
  | cor3.13 的输入 | Lean 载体 | 状态 |
  |---------------|-----------|------|
  | 2^r 条件 | `SaltmanCondition`（SaltCond） | **已证**：H-档对任意 F 成立 |
  | A 作用的忠实性 | `M_H_rho_injective`（F1） | **已证** |
  | [23]（generic object 存在）＋ M3/M4/M6 装配 | `GenericObjectExists`（本件） | **未证**（外部／工程） |

  在形状层，「条件层 ＋ 忠实性」剥离后**恰好**剩「条件 ⟹ 结论」——即
  `GenericObjectExists` 的定义体 `SaltmanCondition A F → RRet K`（条件出现在前提，
  因为源条件正是 [23] 的假设——2^r 条件在步骤 14 才被消费）。

  ⚠ **诚实性声明（本件要点）**：[23] 的**数学内容**（Saltman §1 范畴中 generic
  object 之构造）在当前语言分辨率下**不可形式化**（须先有 M4 的范畴语言），故本件
  把「[23] ＋其下游装配」**整体**按接口形具名。这不是说 [23] 的数学内容等于
  retract rationality 定理；把两者等起来的是**本层的形状**：若 [23]（连同
  M3/M4/M6）成立，则该接口成立。与 G 档 `ProcesiHyp`／EM 档 `EMHyp` 同款工艺：
  把外部输入按其**使用形**具名，并登记其真实数学内容与材料状态（L32 三步流程由
  主循环执行）。

  **无 sorry、无自造公理**。
-/
import ABGV52.Saltman_ABGV52
import ABGV52.SaltCond_ABGV52

universe u v

namespace ABGV52

/-! ## 1. [23] 残差的具名形式（形状层） -/

/-- **[23] 残差的具名形式**（形状层）：剥离条件层（SaltCond）与忠实性（F1）后，
cor3.13 链的剩余外部输入「[23]（generic object 存在）＋ M3/M4/M6 装配」的复合
使用形——「条件成立 ⟹ `K` retract rational」。

真实数学内容（**未形式化**，见头注诚实性声明）：Saltman 1982 在 §1 范畴
（E(A)／F-类）中构造 generic object；经 Prop 1.1(a)（M4）得 lifting property，
经 thm3.12（M3）得 retract rationality。本谓词以 A = H 的战役用例为准具名。 -/
def GenericObjectExists (A : Type u) [Group A] (F : Type v) [Field F]
    (K : Type) (RRet : Type → Prop) : Prop :=
  SaltmanCondition A F → RRet K

/-- **定义外形锁定**：`GenericObjectExists` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (A : Type u) [Group A] (F : Type v) [Field F] (K : Type) (RRet : Type → Prop) :
    GenericObjectExists A F K RRet = (SaltmanCondition A F → RRet K) := rfl

/-! ## 2. H-档分解恒等式（条件层与忠实性分别由 SaltCond／F1 剥离） -/

/-- **分解方向 1**（消耗 F1）：`SaltmanHyp ⟹ GenericObjectExists`——忠实性由
`M_H_rho_injective`（F1）填槽。 -/
theorem genericObjectExists_of_saltmanHyp (F : Type v) [Field F]
    (K : Type) (RRet : Type → Prop) (h : SaltmanHyp K RRet) :
    GenericObjectExists H F K RRet :=
  fun _ => h M_H_rho_injective

/-- **分解方向 2**（消耗 SaltCond）：`GenericObjectExists ⟹ SaltmanHyp`——条件层由
`saltmanCondition_H`（SaltCond）剥离。 -/
theorem saltmanHyp_of_genericObjectExists (F : Type v) [Field F]
    (K : Type) (RRet : Type → Prop) (h : GenericObjectExists H F K RRet) :
    SaltmanHyp K RRet :=
  fun _ => h (saltmanCondition_H F)

/-- **重量分解恒等式（H-档，形状层）**：`SaltmanHyp` 的外观 = 「[23] 残差」，**前提
是**条件层与忠实性已由库内定理剥离（两个方向各消耗一条——见上两条）。 -/
theorem saltmanHyp_iff_genericObjectExists (F : Type v) [Field F]
    (K : Type) (RRet : Type → Prop) :
    SaltmanHyp K RRet ↔ GenericObjectExists H F K RRet :=
  ⟨genericObjectExists_of_saltmanHyp F K RRet, saltmanHyp_of_genericObjectExists F K RRet⟩

/-! ## 3. 条件层剥离定理（H-档：条件前提可无条件移除） -/

/-- **条件剥离**：H-档上 `GenericObjectExists` 与裸结论 `RRet K` 等价——因为
`saltmanCondition_H` 使条件前提恒可真（= 论文「条件空」的库内形式）。 -/
theorem genericObjectExists_iff (F : Type v) [Field F] (K : Type) (RRet : Type → Prop) :
    GenericObjectExists H F K RRet ↔ RRet K :=
  ⟨fun h => h (saltmanCondition_H F), fun h _ => h⟩

/-! ## 4. 探针（L1 非空洞 ＋ L19 判别力） -/

/-- L1：残差假设类非空（取结论谓词 `fun _ => True`）。 -/
theorem genericObjectExists_satisfiable (F : Type v) [Field F] (K : Type) :
    GenericObjectExists H F K (fun _ => True) :=
  fun _ => trivial

/-- L19 判别力：假结论谓词下残差**不**成立（谓词非退化）。 -/
theorem not_genericObjectExists_false (F : Type v) [Field F] (K : Type) :
    ¬ GenericObjectExists H F K (fun _ => False) :=
  fun h => h (saltmanCondition_H F)

/-! ## 5. 公理闸门 -/

#print axioms genericObjectExists_of_saltmanHyp
#print axioms saltmanHyp_of_genericObjectExists
#print axioms saltmanHyp_iff_genericObjectExists
#print axioms genericObjectExists_iff
#print axioms genericObjectExists_satisfiable
#print axioms not_genericObjectExists_false

end ABGV52
