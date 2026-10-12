/-
  ABGV-5.2 —— **本体形式化 B · [23] 残差具名**（Saltman 1982，「generic object」）

  背景（蓝图 `wiki/proj-ABGV52-formalize-saltman.md` §1.1 步骤 14／§3.1 M5／§4.1）
  ==============================================================================
  Saltman1984 Cor 3.13 的证明链在步骤 14 处调用**外部输入 [23]**（Saltman 1982,
  Adv. in Math. 43, 250–283：「A 交换、F 满足 2^r 条件时 generic object 存在」——
  蓝图 §1.2：**2^r 条件只在此步进入**）。~~KB 无 [23] 源件~~ **已入 KB（2026-10-10 用户供源：`raw/Saltman1982.{tex,pdf}`，
  citekey `Saltman1982`，receipt `2b3ed6f6…`；文献笔记 [[1982-Saltman-generic-galois]]）**——
  pinpoint = [23] 印 p. 256／257／258／265／274／275／279 此后库内可核（**印刷页偏移已定案**：印刷页 = PDF 页 + 249 ✓，第 131 轮实测）；
  **⚠ 第 134 轮普查** ✓：Saltman1984 正文对 [23] 的**带页引用共 9 处／7 页** ✓
  —— 印 256（`:126` 论证式引用「arguing as in」）／257（`:771`）／258（`:906`）／265（`:983`）／
  274（`:110`＋`:573`）／275（`:116`）／279（`:973`）✓；旧注**只列 4 页** ✗（257／265／274–275／279）
  ⟹ **漏 256 与 258** ✓ **已补** ✓（`p. 283`／`p. 276` 经查属 `\cite{13}`／`\cite{21}` ✗，**非** [23] ✓）；
  **已逐字核（读图）** ✓ ＝ 印 254／**256**／257／258／**265**／274／275／**279**／**281**／**282**
  （＝ PDF 5／**7**／8／9／**16**／25／26／**30**／**32**／**33** ✓）；
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
      **⚠ 第 134 轮** ✓：本件另落**两条存在性路线**的**具名陈述** ✓ —— `Theorem21Statement` ✓（源印 257 ✓）
      ＋ `Theorem51Statement` ✓（源印 274--275 ✓，经 Noether 构造 ✓），**皆为具名残余** ✗（**不作证明** ✗）；
      并补 Noether 侧词汇 ✓（`IsRationalOver` ✓／`NoetherField` ✓）与 L1 探针 ✓。
      **⚠ 第 135 轮** ✓：落 **§4.4 的桥** ✓ —— `MulSemiringAction G (MvPolynomial G F)` ✓（mathlib **无** ✗，
      自建 ✓）＋ 其**分式域提升** ✓（`IsFractionRing.mulSemiringAction` ✓）＋ **源作用锁两件** ✓
      （`smul_X_noether` ✓：`\sigma(x_\tau) = x_{\sigma\tau}` ✓；`smul_C_noether` ✓：`G` 在 `F` 上平凡 ✓）
      ＋ **提升相容锁** ✓ ＋ **忠实性探针** ✓ ⟹ **`Theorem51Statement` 的实例化路径已通** ✓✅
      （`theorem51Statement_noetherField` ✓）；**⚠ 但两条存在性定理本身仍未证** ✗。
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

/-! ## 4.2 M6 的第二条路线：**Noether 构造**（源 `theorem-5-1`，印 274--275 ✓ **本轮逐字核**） -/

/-- **「`K` 在 `F` 上**有理**」** ✓（源印 274 ✓ 逐字：「**Noether's problem** is whether `L^G` is **rational
over `F`**」✓）—— 落为「与某个有理函数域同构」✓（`F(t_1,\dots ,t_n)` ✓ ＝
`FractionRing (MvPolynomial (Fin n) F)` ✓）。
**⚠ 载体取 `CommRing` 而非 `Field`** ✓（**登记** ✓）：源此处谈的是**固定域** ✓，而「固定域是域」须
Galois 理论 ✓（**本件未建** ✗）⟹ 谓词放宽到 `CommRing` ✓（对被同构的有理函数域而言，该形**更强** ✓）。 -/
def IsRationalOver (F K : Type u) [Field F] [CommRing K] [Algebra F K] : Prop :=
  ∃ (n : ℕ), Nonempty (K ≃ₐ[F] FractionRing (MvPolynomial (Fin n) F))

/-- 源印 274 的 **Noether 构造**的**函数域** ✓：`L = F(x_\sigma \mid \sigma \in G)` ✓
（＝多项式环 `MvPolynomial G F` 的**分式域** ✓）。
**⚠ 登记（第 134 轮记「无消费者」⟹ **第 135 轮已解除** ✓✅）**：本 `abbrev` **现有消费者** ✓ ——
**§4.4** ✓ 在其上落 `MulSemiringAction G` ✓ ＋ `SMulCommClass G F` ✓ 两件实例 ✓ 与提升相容锁 ✓，
并被 `theorem51Statement_noetherField` ✓ 用作源 `theorem-5-1` 的**特定** `L` ✓。
**⚠ 第 134 轮的登记内容（留痕）** ✓：当时「`Theorem51Statement` ✓ 量化 `L` ✓ 而**不用**本件 ✓；为**尚未落**的
「`FractionRing` 上的提升自同构」✓（源作用 `\sigma(x_\tau) = x_{\sigma\tau}` ✓ 的分式域提升 ✓）**预留** ✓
（mathlib 实测**无** `MulSemiringAction G (FractionRing (MvPolynomial G F))` ✗）⟹ **未落** ✗」——
该「未落」**已于第 135 轮落** ✓（mathlib **有** `IsFractionRing.mulSemiringAction` ✓ —— 第 134 轮的实测
**只**查了 `synthInstanceFailed` ✗，**未**查该 `def` 级 API ✗ ⟹ **工艺读数 ㊲** ✓）。 -/
abbrev NoetherField (F G : Type u) [Field F] : Type u := FractionRing (MvPolynomial G F)

/-- **L1 探针（载体非退化）** ✓：`NoetherField` 的 `CommRing` 实例可**直接合成** ✓（`inferInstance` ✓）
⟹ 该 `abbrev` **不是**空壳 ✓。**⚠ 须 `noncomputable`** ✓（该实例经 `AddMonoidAlgebra.commRing` ✓，**非**可计算 ✓ ——
一处编译期自纠 ✓）。 -/
noncomputable example (F G : Type u) [Field F] : CommRing (NoetherField F G) := inferInstance

/-- **源 `theorem-5-1`（印 274--275 ✓ 逐字核）的具名陈述** ✓ —— **⚠ 具名残余：本件不作证明** ✗**。

源逐字 ✓：「Let `F`, `L`, and `G` be as above, with `F` **infinite**. **If `L^G` is rational over `F`, then
there is a generic Galois extension for `G` over `F`**」✓（**印 275 上方** ✓；证明在**同页** ✓，用正规基技巧 ✓
「`f(b_1,\dots ,b_n)\neq 0` if and only if `z` generates a **normal basis**」✓）。

**⚠ 与源的**两处**偏离** ✓**（**登记** ✓；**二者皆放宽本陈述的**前提** ✓ ⟹ 数学上本陈述**强于**源 ✓；
**⚠ 「证本陈述 ⟹ 证源」的形式前提**：**第 134 轮记「未通」** ✗ ⟹ **第 135 轮已闭合** ✓✅** —— **§4.4** ✓
落 `MulSemiringAction G (NoetherField F G)` ✓ ＋ `SMulCommClass G F (NoetherField F G)` ✓ 两件实例 ⟹
源的**特定** `L`（＝`NoetherField F G` ✓）**可实例化** ✓，其**用点**由 `theorem51Statement_noetherField` ✓
显式给出 ✓（**⚠ 仅「形式前提」** ✓ —— `Theorem51Statement` 本身**仍是具名残余** ✗）。
**⚠ 第 134 轮补注** ✓：源印 **282** ✓
（＝ PDF 33 ✓）的 `Note added in proof` 明写「the results of **Theorem 5.3 and Corollary 5.4** should be
limited to **infinite** fields `F`. This implies that `F` should be assumed infinite in **Section 3**」✓
⟹ 无限性前提在源中是**承重**的 ✓（支持偏离 (ii) 的登记 ✓））：
**(i)** 源把 `L` **固定**为 `L = F(x_\sigma \mid \sigma \in G)` ✓、作用固定为 `\sigma(x_\tau) = x_{\sigma\tau}` ✓；
本件**量化** `L` 与作用 ✓ —— **⚠ 第 134 轮记「因 mathlib 无 `MulSemiringAction G (FractionRing (MvPolynomial G F))`
⟹ 自建须先造提升自同构 ⟹ 未落」** ✗ ⟹ **第 135 轮已解** ✓✅：mathlib **并无** `MvPolynomial` 上的实例 ✗（该实测**对** ✓），
但**有** `IsFractionRing.mulSemiringAction` ✓ —— 环自同构**诱导**分式域自同构 ✓ ⟹ 只需在 `MvPolynomial` 上自建 ✓
（§4.4 ✓）再**提升** ✓ 即可（**工艺读数 ㊲** ✓：`synthInstanceFailed` ✗ **不等于**该结构不可得 ✓ —— 须另查
**`def` 级 API** ✓）；`NoetherField` ✓ 现有消费者 ✓（见其登记 ✓）。
**(ii)** 源要 `F` **无限** ✓；本件**未设**该前提 ✓（若证明需要再补 ✓，**登记** ✓）。
**⚠ 源的另一处判别性事实** ✓（`remark` 印 275 ✓）：「The **converse** of `theorem-5-1` is **false**.
`C_{47}` has a generic extension over `Q`, but **Swan showed Noether's Problem false** for this group」✓
⟹ 本两条 M6 路线**互相独立** ✓（与 `theorem-2-1` ✓ 的条件不同 ✓），**登记** ✓。 -/
def Theorem51Statement (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra F L] [MulSemiringAction G L] [SMulCommClass G F L],
    IsRationalOver F ↥(FixedPoints.subalgebra F L G) → Nonempty (GenericExtensionWitness F G)

/-- **外形锁定 ①** ✓：`IsRationalOver` 的**用点形**逐字可取 ✓（有理函数域同构 ✓）。 -/
theorem IsRationalOver.shape {F K : Type u} [Field F] [CommRing K] [Algebra F K]
    (h : IsRationalOver F K) :
    ∃ (n : ℕ), Nonempty (K ≃ₐ[F] FractionRing (MvPolynomial (Fin n) F)) :=
  h

/-- **外形锁定 ②** ✓：`Theorem51Statement` 的**两段**（**固定域有理** ✓／**存在见证** ✓）逐字可取 ✓ ——
**⚠ 前提须作独立假设传入** ✓（㉝ ✓）。 -/
theorem Theorem51Statement.shape (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (h : Theorem51Statement F G) (L : Type u) [Field L] [Algebra F L] [MulSemiringAction G L]
    [SMulCommClass G F L] (hL : IsRationalOver F ↥(FixedPoints.subalgebra F L G)) :
    Nonempty (GenericExtensionWitness F G) :=
  h L hL

/-! ## 4.3 L1 探针与判别力登记（第 134 轮） -/

/-- **L1 非空洞探针** ✓（§3 工艺第 3 条 ✓）：`IsRationalOver` 的**假设类非空** ✓ —— **有理函数域自身有理** ✓
（取 `n = 0` 得 `F` 本身 ✓；一般 `n` 取恒等同构 ✓）。
**⚠ 判别力** ✓：本探针是**定理**（**非** `rfl` 平凡形 ✗）✓ ⟹ `IsRationalOver` 的右端被改坏即**编译失败** ✓，
故它**同时**充当该 `def` 的**外形锁** ✓。 -/
theorem isRationalOver_self (F : Type u) [Field F] (n : ℕ) :
    IsRationalOver F (FractionRing (MvPolynomial (Fin n) F)) :=
  ⟨n, ⟨AlgEquiv.refl⟩⟩

/-- **⚠ 登记（L19 判别力探针未落）** ✗：`IsRationalOver` 的**否定性**判别力探针（一条**可证的**
`¬ IsRationalOver F K` ✓）**本件未建** ✗ —— 需「有限环不能与有理函数域同构」类论证
（`F` 无限时 `F(t_1,\dots ,t_n)` 无限 ✓；**mathlib 侧未落** ✗）⟹ 按 **L8①** ✓：
本谓词的**阴性**读数**只用于生成、不得用于排除** ✓（L19 ✓）。 -/
theorem isRationalOver_discrimination_gap_registered : True := trivial

/-! ## 4.4 Noether 作用的**桥**（源印 274：「Let `G` act on `L` by letting `G` act trivially on `F` and by
setting `\sigma(x_\tau) = x_{\sigma\tau}`」✓）—— 第 135 轮 -/

section NoetherBridge

variable (F : Type u) [Field F] (G : Type u) [Group G]

/-- **Noether 作用的环自同构** ✓（源印 274 ✓）：`g` 在变量上按 `\tau \mapsto g\tau` ✓ 作用
（`MvPolynomial.renameEquiv F (Equiv.mulLeft g)` ✓）。
**⚠ mathlib 无现成实例** ✗（**实测**：`MulSemiringAction G (MvPolynomial G F)` 的 `synthInstanceFailed` ✗）；
mathlib 只给 `rename`／`renameEquiv` ✓（`rename_X` ✓：`(rename f) (X i) = X (f i)` ✓）⟹ 本件**自建** ✓。 -/
noncomputable def noetherRingHom : G →* (MvPolynomial G F ≃+* MvPolynomial G F) where
  toFun g := (MvPolynomial.renameEquiv F (Equiv.mulLeft g)).toRingEquiv
  map_one' := by ext p; simp
  map_mul' g h := by ext p; simp

/-- **`MvPolynomial` 上的 Noether 作用** ✓ —— 把 `noetherRingHom` 沿 `MulSemiringAction.compHom` ✓
拉回 ✓（与 mathlib `IsFractionRing.mulSemiringAction` ✓ **同一工艺** ✓）。 -/
noncomputable instance instNoetherActionMvPolynomial : MulSemiringAction G (MvPolynomial G F) :=
  MulSemiringAction.compHom (MvPolynomial G F) (noetherRingHom F G)

/-- **源作用锁 ①**（**源陈述逐字** ✓）：`\sigma(x_\tau) = x_{\sigma\tau}` ✓。
**⚠ 判别力** ✓：把右端 `g * τ` 改成 `τ * g` ✗ 或 `τ` ✗ 即**编译失败** ✓ ⟹ 该锁把作用**钉在源的作用上** ✓。 -/
theorem smul_X_noether (g τ : G) :
    g • (MvPolynomial.X τ : MvPolynomial G F) = MvPolynomial.X (g * τ) := by
  show (noetherRingHom F G g) (MvPolynomial.X τ) = MvPolynomial.X (g * τ)
  simp [noetherRingHom, MvPolynomial.rename_X]

/-- **源作用锁 ②**（**源陈述逐字** ✓）：源「letting `G` act **trivially** on `F`」✓ ⟹ `g` 在系数上平凡 ✓。 -/
theorem smul_C_noether (g : G) (c : F) :
    g • (MvPolynomial.C c : MvPolynomial G F) = MvPolynomial.C c := by
  show (noetherRingHom F G g) (MvPolynomial.C c) = MvPolynomial.C c
  simp [noetherRingHom]

/-- **忠实性（L19 判别力探针）** ✓：该作用**非平凡** ✓ —— 取 `p = X 1` 得 `X g = X h` ✓ ⟹ `g = h` ✓
（`MvPolynomial.X_injective` ✓）。
**⚠ 意义** ✓：若谓词层「作用」退化为**平凡作用** ✗ 则本条失败 ✓ ⟹ 本桥**不是**空壳 ✓。 -/
instance instFaithfulSMulMvPolynomial : FaithfulSMul G (MvPolynomial G F) :=
  ⟨fun {g h} hgh => by
    have h1 : g • (MvPolynomial.X (1 : G) : MvPolynomial G F)
        = h • (MvPolynomial.X (1 : G) : MvPolynomial G F) := by rw [hgh]
    simp only [smul_X_noether, mul_one] at h1
    exact MvPolynomial.X_injective h1⟩

/-- **`G` 与 `F` 的标量作用交换** ✓（作用经 **`F`-代数**自同构 ✓ ⟹ 与系数标量交换 ✓）。
**⚠ 用点** ✓：`IsFractionRing.smulCommClass` ✓ 与 `FixedPoints.subalgebra` ✓ 都需要它 ✓。 -/
instance instSMulCommClassMvPolynomial : SMulCommClass G F (MvPolynomial G F) where
  smul_comm g c p := by
    show (noetherRingHom F G g) (c • p) = c • (noetherRingHom F G g) p
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    simp [noetherRingHom]

/-- **桥：把 Noether 作用提升到分式域** ✓（mathlib `IsFractionRing.mulSemiringAction` ✓ ——
环自同构诱导分式域自同构 ✓）。 -/
noncomputable instance instNoetherActionNoetherField : MulSemiringAction G (NoetherField F G) :=
  IsFractionRing.mulSemiringAction G (MvPolynomial G F) (NoetherField F G)

/-- **`SMulCommClass` 随提升保留** ✓（mathlib `IsFractionRing.smulCommClass` ✓）。 -/
instance instSMulCommClassNoetherField : SMulCommClass G F (NoetherField F G) :=
  IsFractionRing.smulCommClass G F (MvPolynomial G F) F (NoetherField F G)

/-- **提升相容锁** ✓：分式域上的作用**限制回**多项式环的 Noether 作用 ✓
（`g • (algebraMap p) = algebraMap (g • p)` ✓）。
**⚠ 判别力** ✓：它把「随便一个分式域作用」✗ 与「**源作用之提升**」✓ 分开 ✓。 -/
theorem smul_algebraMap_noether (g : G) (p : MvPolynomial G F) :
    g • (algebraMap (MvPolynomial G F) (NoetherField F G) p)
      = algebraMap (MvPolynomial G F) (NoetherField F G) (g • p) := by
  show (IsFractionRing.ringEquivOfRingEquivHom (MvPolynomial G F) (NoetherField F G)
      ((MulSemiringAction.toRingEquiv G (MvPolynomial G F)) g)) (algebraMap _ _ p) = _
  rw [IsFractionRing.ringEquivOfRingEquivHom_apply,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- **L1 探针（忠实性随提升保留）** ✓（mathlib `IsFractionRing.faithfulSMul` ✓：作用在 `B` 上忠实
⟹ 在分式域上忠实 ✓）。 -/
instance instFaithfulSMulNoetherField : FaithfulSMul G (NoetherField F G) :=
  IsFractionRing.faithfulSMul G (MvPolynomial G F) (NoetherField F G)

/-- **§97.3 的实例化路径已闭合** ✓✅：源 `theorem-5-1` 的**特定** `L` ＝ `NoetherField F G` ✓
现**可实例化** ✓（`MulSemiringAction` ✓ ＋ `SMulCommClass` ✓ 两件实例齐 ✓）⟹ 「证 `Theorem51Statement`
即证源」的**形式前提**已通 ✓（**⚠ 仅形式前提** ✗ —— `Theorem51Statement` 本身**仍是具名残余** ✗）。 -/
theorem theorem51Statement_noetherField [Fintype G] (h : Theorem51Statement F G)
    (hL : IsRationalOver F ↥(FixedPoints.subalgebra F (NoetherField F G) G)) :
    Nonempty (GenericExtensionWitness F G) :=
  h (NoetherField F G) hL

end NoetherBridge

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
#print axioms IsRationalOver
#print axioms NoetherField
#print axioms Theorem51Statement
#print axioms IsRationalOver.shape
#print axioms Theorem51Statement.shape
#print axioms isRationalOver_self
#print axioms isRationalOver_discrimination_gap_registered
#print axioms noetherRingHom
#print axioms instNoetherActionMvPolynomial
#print axioms smul_X_noether
#print axioms smul_C_noether
#print axioms instFaithfulSMulMvPolynomial
#print axioms instSMulCommClassMvPolynomial
#print axioms instNoetherActionNoetherField
#print axioms instSMulCommClassNoetherField
#print axioms smul_algebraMap_noether
#print axioms instFaithfulSMulNoetherField
#print axioms theorem51Statement_noetherField

end ABGV52
