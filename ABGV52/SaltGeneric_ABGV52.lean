/-
  ABGV-5.2 —— **本体形式化 B · [23] 残差具名**（Saltman 1982，「generic object」）

  背景（蓝图 `wiki/proj-ABGV52-formalize-saltman.md` §1.1 步骤 14／§3.1 M5／§4.1）
  ==============================================================================
  Saltman1984 Cor 3.13 的证明链在步骤 14 处调用**外部输入 [23]**（Saltman 1982,
  Adv. in Math. 43, 250–283：「A 交换、F 满足 2^r 条件时 generic object 存在」——
  蓝图 §1.2：**2^r 条件只在此步进入**）。~~KB 无 [23] 源件~~ **已入 KB（2026-10-10 用户供源：`raw/Saltman1982.{tex,pdf}`，
  citekey `Saltman1982`，receipt `2b3ed6f6…`；文献笔记 [[1982-Saltman-generic-galois]]）**——
  pinpoint = [23] 印 p. 257／p. 265／pp. 274–275／p. 279 此后库内可核（**印刷页偏移已定案**：印刷页 = PDF 页 + 249 ✓，第 131 轮实测）；
  2^r 条件句的源 = `theorem-2-1`（F(ρ(r))/F 循环）。具名形暂维持（内容消费待复核波）。⚠ 页偏移登记：
  Saltman1984 的印刷页 = PDF 页 **+ 164**（任务书原写「+220」有误——那是
  Saltman1987 的偏移）。

  **路线对齐注记（头注必写项）**
  ==============================
  * 论文侧该定理的自然语言「证明」= **无**——纯外部引用（Saltman1984 Cor 3.13）。
  * Lean 路线 = Salt* 内部工程（M1/M2 已交付）＋条件层（`SaltCond_ABGV52.lean`）
    ＋本件 [23] 残差具名——与论文引用结构对齐（同样把它**当假设用**）。
  * **偏离登记（2026-10-12 第 131 轮更新）**：本件**仍不**声称「`GenericObjectExists ⟹
    SaltmanHyp`」的**数学装配**已完成。各里程碑的**现状态**如下（**逐条重核过，非沿用旧注**）——
    - **M3**（局部提升判据）：**已完整** ✓（状态笔记 §75.4：「`thm3.9` ⇄ `thm3.8`」✓；
      `def3.1`／`def3.2`／`lem3.3`／`cor3.4`／`lem3.5` 已在库 ✓，源文回证见 §75／§82）；
    - **M4**（§1 范畴语言）：**陈述层已完整** ✓（状态笔记 §93.3：§77.2 第 1–9 件 ✓；
      新件 `SaltClass_ABGV52.lean` ✓：`LinearStructure`→`Hom`／`IsIso`→`FStruct`／`IsFClass`→
      `HasLiftingProperty`→`RepresentingObject`／`GenericObject`／`DenselyRepresenting`→
      `RelativeLiftingProperty`／`RetractRational`／`FactorsRationally`→`Prop11aStatement`／
      `Prop11bStatement` ✓）。**⚠ 六件具名残余** ✗：`Thm13aStatement`／`Cor310aStatement`／
      `Cor310bStatement`／`Cor310Reduction`／`Prop11aStatement`／`Prop11bStatement` —— **只给陈述、
      不作证明** ✓（`SaltClass_ABGV52.lean` §8.9／§8.11／§8.12 ✓）；
    - **M6**（装配：thm3.12(b)＋端点识别）：**仍未做** ✗，但其**词汇已就位** ✓ ——
      本仓 `GenericExtension_ABGV52.lean` ✓ 已有 `RealizationProperty` ✓（源 `definition-1-1`(c) ✓）／
      `IsGenericExtension` ✓（`definition-1-1` 三款 ✓）／`IsRepresentingObjectEG` ✓／
      `IsGenericObjectEG` ✓（源 §1「representing object」＋「localized polynomial ring」✓）；
      **⚠ 本轮已锁两编码一致** ✓：`isGenericExtension_iff_isGenericObjectEG` ✓（同一谓词，只差合取次序 ✓）。
      ⟹ **M6 的真实缺口 ＝ 该对象的存在性定理** ✗（Saltman 1982 §1 的构造 ✓），
      **不是**词汇 ✓ —— 该存在性**本件未落** ✗。
    - **⚠ 上游 [23] 的页码偏移已定案** ✓（本轮）：`Saltman1982` 的**印刷页 ＝ PDF 页 + 249** ✓
      （实测：PDF 5 ＝ 印 **254** ✓；与刊载页域 250--283 ✓ 自洽 ✓）⟹ 原注「印刷页偏移未核」✗ **已结** ✓；
      头注上列 pinpoint（印 257／265／274--275／279 ✓）可据此折算为 PDF 8／16／25--26／30 ✓。
    ⟹ 本件做的是**重量分解**（见下表）与 **H-档分解恒等式**（形状层，两个方向分别消耗
    SaltCond 与 F1 的库内定理 ✓）。

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
import ABGV52.GenericExtension_ABGV52

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

/-! ## 4.1 [23] 的**源头具名**（Saltman 1982 `theorem-2-1`）—— **本轮逐字核** ✓

源 `raw/Saltman1982.{tex,pdf}`（citekey `Saltman1982` ✓，receipt `2b3ed6f6…` ✓，**印刷页 = PDF 页 + 249** ✓）：
**印 257**（＝ PDF 8 ✓）逐字 —— 「We begin by stating our **main theorem on the existence of generic
extensions for abelian groups**. Let `A` be a finite abelian group, and `F` a field of characteristic
prime to the order of `A`. Denote by `r` the highest power of 2 dividing the exponent of `A`.」✓ 紧接
**`THEOREM 2.1.`**「Suppose `F(\rho(r))/F` is a **cyclic** extension. Then **there is a generic Galois
extension for `A` over `F`**」✓（**本轮读图定案** ✓；与 tex `:214--219` **逐字符合** ✓）。
**⚠ 该源件的载体状态** ✓：2026-10-11 做过**字形级修正** ✓（`\times\to\rtimes` 21 处 ＋ 折叠段 `\wr` 滑落 2 处 ✓；
旧 tex 存档 `Saltman1982.tex.preGlyphfix` ✓）⟹ **显示数据**引用前须回 PDF 目视 ✓（L16 ✓）。 -/

/-- **[23] 存在性的见证数据** ✓（源 `theorem-2-1` 的「there is a generic Galois extension for `A` over `F`」✓）
—— 打包 `R`／`S` 及其全部实例 ✓（`\exists` **不接受实例绑定** ✗，附四十六 ⑳ ✓）。 -/
structure GenericExtensionWitness (F : Type v) [Field F] (A : Type u) [Group A] [Fintype A] where
  R : Type u
  S : Type u
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [algebraFR : Algebra F R]
  [algebraRS : Algebra R S]
  [algebraFS : Algebra F S]
  [tower : IsScalarTower F R S]
  [mulSemiringActionS : MulSemiringAction A S]
  /-- 源 `definition-1-1` 之前所需的**等变前提** ✓（`G`-作用与 `R`-作用交换 ✓）。 -/
  hRG : ∀ (g : A) (r : R) (t : S), g • (r • t) = r • (g • t)
  /-- 源：`S/R` 是 `A` 在 `F` 上的 **generic Galois extension** ✓（`definition-1-1` 三款 ✓；**在 `ABGV52.BTier` 命名空间** ✓）。 -/
  isGeneric : ABGV52.BTier.IsGenericExtension F A R S hRG

/-- **源 `theorem-2-1`（印 257 ✓ 逐字核）的具名陈述** ✓ —— **⚠ 具名残余：本件不作证明** ✗**。

**⚠ 前提的库内形** ✓：源的两条前提（`F` 的特征**与 `|A|` 互素** ✓；`F(\rho(r))/F` **循环** ✓，`r` ＝ `2`
整除 `\mathrm{exp}(A)` 的最高幂 ✓）由本仓既有的 **`SaltmanCondition A F`** ✓ 承载 ✓
（＝ `ringChar F = 2 \vee \exists\rho,\ \mathrm{IsPrimitiveRoot}\ \rho\ (\mathrm{twoPowerPart}\ (\mathrm{exponent}\ A))
\wedge \mathrm{IsCyclicExtension}\ F\ F\langle\rho\rangle` ✓，`SaltCond_ABGV52.lean:98` ✓）。
**⚠ 口径观察** ✓（**登记，本轮不改** ✗）：`SaltmanCondition` 的**第一析取支**是 `ringChar F = 2` ✓、
**第二支**只要求 `2`-部的本原根存在 ✓ —— 而源把「特征与 **`|A|`** 互素」✓（含**奇部** ✓）**单列**为假设 ✓
⟹ 库内条件**可能弱于**源 ✓（**未证** ✗）；登记于状态笔记 ✓。 -/
def Theorem21Statement (A : Type u) [Group A] [Fintype A] (F : Type v) [Field F] : Prop :=
  SaltmanCondition A F → Nonempty (GenericExtensionWitness F A)

/-- **外形锁定** ✓：`Theorem21Statement` 的**两段**（**含 `SaltmanCondition A F` 前提** ✓／
`Nonempty (GenericExtensionWitness F A)` ✓）逐字可取 ✓ —— **前提被吞或见证改形即失败** ✓
（**⚠ 前提须作独立假设传入** ✓：`Theorem21Statement` 是**蕴含** ✓，故锁形须显式给前提 ✓ —— 与
`Thm13aStatement.shape` ✓ 同一工艺 ✓）。 -/
theorem Theorem21Statement.shape (A : Type u) [Group A] [Fintype A] (F : Type v) [Field F]
    (h : Theorem21Statement A F) (hC : SaltmanCondition A F) :
    Nonempty (GenericExtensionWitness F A) :=
  h hC

/-! ## 5. 公理闸门 -/

#print axioms genericObjectExists_of_saltmanHyp
#print axioms saltmanHyp_of_genericObjectExists
#print axioms saltmanHyp_iff_genericObjectExists
#print axioms genericObjectExists_iff
#print axioms genericObjectExists_satisfiable
#print axioms not_genericObjectExists_false
#print axioms GenericExtensionWitness
#print axioms Theorem21Statement
#print axioms Theorem21Statement.shape

end ABGV52
