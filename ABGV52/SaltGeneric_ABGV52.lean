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
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Galois.NormalBasis

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

/-! ## 4.5 M6 路线②的**证明第一步**（源 `lemma-5-2` 的开头 ✓）＋ 该引理的**具名残余**（第 138 轮）

**源逐字** ✓（`raw/Saltman1982.tex :648--662` ✓，印 **275** ✓）：`lemma-5-2` ＝「Let `L/K` be as above, and `t`
any polynomial in `F[x_\sigma \mid \sigma \in G]`. Then there is a `z \in L` such that `\{\sigma(z) \mid \sigma \in G\}`
is a **normal basis** for `L` over `K` and such that `t` evaluated at the `\sigma(z)`'s is a **unit**」✓；
其证明**首句** ✓：「Letting `G` act on `F[x_\sigma \mid \sigma \in G]`, we form `t' = \prod_{\sigma \in G} \sigma(t)`.
`t'` has the property that `t'(z,\sigma(z),\dots)` is **always in `K`**, and if `t'(z,\sigma(z),\dots) \neq 0` then
`t(z,\sigma(z),\dots)` is a **unit**」✓；**源并明写该引理足以收官** ✓：「Thus, in fact, **it suffices to prove the
following lemma**」✓ ⟹ `theorem-5-1` ✓ **归约到** `lemma-5-2` ✓（**登记** ✓，**归约本身未形式化** ✗）。 -/

section Lemma52FirstStep

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]

/-- **源 `lemma-5-2` 证明的**第一步** ✓：`t' = \prod_{\sigma} \sigma(t)` **是 `G`-不变的** ✓ ——
即源「`t'` has the property that `t'(z,\sigma(z),\dots)` is **always in `K`**」✓ 的**代数核** ✓
（**不变 ⟹ 取值落固定域** ✓，见下条 ✓）。

**证明** ✓：`g • \prod_\sigma \sigma \bullet t = \prod_\sigma g \bullet (\sigma \bullet t) = \prod_\sigma (g\sigma) \bullet t` ✓
（`map_prod` ✓ ＋ `mul_smul` ✓），再经 `\sigma \mapsto g\sigma` **重指标** ✓（`Fintype.prod_equiv` ✓ ＋ `Equiv.mulLeft` ✓）。
**⚠ 用点** ✓：本式**消耗 §4.4 的桥** ✓（Noether 作用 ✓）—— **无该作用则无从陈述** ✗。 -/
theorem noether_prod_smul_invariant (t : MvPolynomial G F) (g : G) :
    g • (∏ σ : G, σ • t) = ∏ σ : G, σ • t := by
  have h1 : g • (∏ σ : G, σ • t) = ∏ σ : G, g • (σ • t) :=
    map_prod (MulSemiringAction.toRingEquiv G (MvPolynomial G F) g) _ _
  have h2 : (∏ σ : G, g • (σ • t)) = ∏ σ : G, (g * σ) • t :=
    Finset.prod_congr rfl (fun σ _ => (mul_smul g σ t).symm)
  have h3 : (∏ σ : G, (g * σ) • t) = ∏ σ : G, σ • t :=
    Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  rw [h1, h2, h3]

/-- **源 `lemma-5-2` 证明的**第二步** ✓：「`t'(z,\sigma(z),\dots)` is **always in `K`**」✓ ——
形式化 ＝ **`t'` 在求值映射下的像被 `G` 固定** ✓。

`\mathrm{ev}` 是「把 `x_\sigma` 送到 `\sigma(z)`」的 `F`-代数映射 ✓（`ev (X \sigma) = \sigma \bullet z` ✓）；
`\mathrm{hev}` 是其 **`G`-等变性** ✓（`ev (g \bullet p) = g \bullet ev p` ✓）—— **⚠ 第 139 轮已证其可得性** ✓✅
（`noetherEval_equivariant` ✓，见 **§4.6** ✓；**第 138 轮原记「未证」** ✗ —— **留痕** ✓）。
**⚠ 结论取「被每个 `g` 固定」** ✓（＝不动点的**定义形** ✓）—— **不**取 `FixedPoints.subalgebra` 的**隶属形** ✗
（其隶属引理名**未定位** ✗，**登记** ✓）。 -/
theorem noether_prod_eval_isFixed {L : Type u} [Field L] [Algebra F L]
    [MulSemiringAction G L]
    (ev : MvPolynomial G F →ₐ[F] L)
    (hev : ∀ (g : G) (p : MvPolynomial G F), ev (g • p) = g • ev p)
    (t : MvPolynomial G F) (g : G) :
    g • ev (∏ σ : G, σ • t) = ev (∏ σ : G, σ • t) := by
  rw [← hev g, noether_prod_smul_invariant F G t g]

end Lemma52FirstStep

section Lemma52StatementSec

variable (F : Type u) [Field F] (G : Type u) [Group G]

/-- **源 `lemma-5-2`（印 275 ✓ 逐字）的具名陈述** ✓ —— **⚠ 具名残余：本件不作证明** ✗**。

**⚠ 四处登记** ✗：
① **抽象载体** ✓：`K`／`L` 抽象 ✓（与 `Theorem51Statement` ✓ 同款 ✓）；「`K \supseteq F`」由 `[Algebra F K]` ✓
承担 ✓；
② **「`t` 在 `\sigma(z)` 处的取值是**单位**」** ✓ 落为 **`\mathrm{aeval}(\dots) t \neq 0`** ✓ ——
`L` 是**域** ✓ ⟹ **非零即单位** ✓（源用「unit」✓ 在此等价 ✓）；
③ **正规基** ✓ 落为 **`Module.Basis G K L` ＋ `b \sigma = \sigma \bullet z`** ✓（＝「**共轭族恰成 `K`-基**」✓，
**含张成** ✓ —— 第 138 轮**未**用「只求线性无关」✗ 的弱形 ✓）；
④ **⚠ 本陈述**不设**「`G` 有限」** ✓（**登记** ✓）：`[Fintype G]` **不进**签名 ✗（Lean 弃用不出现在类型中的
auto-bound 变量 ✓）⟹ 即**强于**源 ✓（与 `Theorem51Statement` ✓ 去掉「`F` 无限」✓ 同款处置 ✓，
故**另开 section** ✓）。 -/
def Lemma52Statement (K L : Type u) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] [MulSemiringAction G L] : Prop :=
  ∀ t : MvPolynomial G F,
    ∃ (z : L) (b : Module.Basis G K L), (∀ σ : G, b σ = σ • z) ∧
      MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0

/-- **外形锁定** ✓：`Lemma52Statement` 的**三段**（**基** ✓／**共轭 ＝ 基元素** ✓／**非零** ✓）逐字可取 ✓ ——
**⚠ 前提（`t`）作独立假设传入** ✓（㉝ ✓）。 -/
theorem Lemma52Statement.shape (K L : Type u) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] [MulSemiringAction G L]
    (h : Lemma52Statement F G K L) (t : MvPolynomial G F) :
    ∃ (z : L) (b : Module.Basis G K L), (∀ σ : G, b σ = σ • z) ∧
      MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0 :=
  h t

end Lemma52StatementSec

/-! ## 4.6 源 `lemma-5-2` 的**可用形**：求值等变性（**解 §4.5 的 `hev` 登记** ✓）＋ 「`t'` 总在 `K` 中」的直接形（第 139 轮） -/

section EvalEquivariance

variable (F : Type u) [Field F] (G : Type u) [Group G]

/-- **Noether 求值的 `G`-等变性** ✓（**§4.5 登记的「`\mathrm{hev}` 未证」** ✗ **本轮结** ✓✅）：
把 `x_\sigma` 送到 `\sigma \bullet z` 的 `F`-代数映射 `\mathrm{aeval}(\sigma \mapsto \sigma \bullet z)` ✓
**与 `G` 在两侧的作用交换** ✓（左：`MvPolynomial` 上的 Noether 作用 ✓；右：`L` 上的给定作用 ✓）。

**证明** ✓：对 `p` 作 `MvPolynomial.induction_on` ✓（**显式给 motive** ✓ —— 否则高阶合一失败 ✗，**一处编译期自纠** ✓）：
`C a` 支用 `smul_C_noether` ✓ ＋ `smul_algebraMap` ✓（**此处需要 `SMulCommClass G F L`** ✓）；
`+` 支用 `smul_add` ✓／`map_add` ✓；`p * X n` 支用 `smul_mul'` ✓ ＋ `smul_X_noether` ✓ ＋ `mul_smul` ✓
（`(g n) \bullet z = g \bullet (n \bullet z)` ✓）。
**⚠ `[Fintype G]` 不需要** ✓ ⟹ **另开 section** ✓（承 §4.5 的教训 ✓，第 138 轮 ✓）。 -/
theorem noetherEval_equivariant {L : Type u} [Field L] [Algebra F L] [MulSemiringAction G L]
    [SMulCommClass G F L] (z : L) (g : G) (p : MvPolynomial G F) :
    MvPolynomial.aeval (fun σ : G => σ • z) (g • p)
      = g • MvPolynomial.aeval (fun σ : G => σ • z) p := by
  refine MvPolynomial.induction_on (motive := fun q =>
    MvPolynomial.aeval (fun σ : G => σ • z) (g • q)
      = g • MvPolynomial.aeval (fun σ : G => σ • z) q) p ?_ ?_ ?_
  · intro a
    simp [smul_C_noether, smul_algebraMap]
  · intro p q hp hq
    simp only [smul_add, map_add, hp, hq]
  · intro p n hp
    simp only [smul_mul', smul_X_noether, map_mul, MvPolynomial.aeval_X, hp]
    rw [mul_smul]

end EvalEquivariance

section Lemma52UsableForm

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]

/-- **源 `lemma-5-2` 证明中「`t'(z,\sigma(z),\dots)` is **always in `K`**」✓ 的**直接可用形** ✓**：
以**源自己的求值** ✓（`x_\sigma \mapsto \sigma \bullet z` ✓）代入 `t' = \prod_{\sigma} \sigma \bullet t` ✓，
其像**被每个 `g` 固定** ✓（＝落于不动域 ✓）。

**证明** ✓：`§4.5` 的 `noether_prod_eval_isFixed` ✓ 的 `\mathrm{hev}` 前提**由 §4.6 的
`noetherEval_equivariant` ✓ 填充** ✓ ⟹ **条件式 → 无条件式** ✓（**这是 §4.5 那条登记的意义** ✓）。
**⚠ 用点** ✓：本式是 `lemma-5-2` **证明**的**第一步的收口** ✓ —— 源的下一句（`t' \neq 0 \Rightarrow t` 是单位 ✓）
**第 140 轮已落** ✓✅（`noether_aeval_ne_zero_of_prod_ne_zero` ✓，见 **§4.7** ✓；**第 139 轮原记「未落」** ✗ —— **留痕** ✓）。 -/
theorem noether_prod_aeval_isFixed {L : Type u} [Field L] [Algebra F L]
    [MulSemiringAction G L] [SMulCommClass G F L]
    (z : L) (t : MvPolynomial G F) (g : G) :
    g • MvPolynomial.aeval (fun σ : G => σ • z) (∏ σ : G, σ • t)
      = MvPolynomial.aeval (fun σ : G => σ • z) (∏ σ : G, σ • t) :=
  noether_prod_eval_isFixed F G (MvPolynomial.aeval (fun σ : G => σ • z))
    (fun g p => noetherEval_equivariant F G z g p) t g

end Lemma52UsableForm

/-! ## 4.7 源 `lemma-5-2` 的**第三步 (c)**：`t' \neq 0 \Rightarrow t` 是单位 ✓（第 140 轮）

**源逐字** ✓（`tex :662` ✓）：「if `t'(z,\sigma(z),\dots) \neq 0` then `t(z,\sigma(z),\dots)` is a **unit**」✓ ——
**在一处域 `L` 上「单位」＝ 非零** ✓ ⟹ 落为 **`\mathrm{aeval}(\dots) t \neq 0`** ✓。 -/

section Lemma52UnitStep

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]

/-- **乘积与求值的交换** ✓：`\mathrm{ev}(\prod_\sigma \sigma \bullet t) = \prod_\sigma \sigma \bullet \mathrm{ev}(t)` ✓ ——
即 `t'` 的求值**恰是 `\mathrm{ev}(t)` 的各共轭之积** ✓（源 `(c)` 的**代数核** ✓）。
**证明** ✓：`map_prod` ✓（`\mathrm{aeval}` 是 `F`-代数同态 ✓）＋ 逐因子用 **§4.6 的 `noetherEval_equivariant`** ✓。 -/
theorem noether_prod_aeval_eq {L : Type u} [Field L] [Algebra F L] [MulSemiringAction G L]
    [SMulCommClass G F L] (z : L) (t : MvPolynomial G F) :
    MvPolynomial.aeval (fun σ : G => σ • z) (∏ σ : G, σ • t)
      = ∏ σ : G, σ • (MvPolynomial.aeval (fun σ : G => σ • z) t) := by
  rw [map_prod (MvPolynomial.aeval (fun σ : G => σ • z)) (fun σ : G => σ • t) Finset.univ]
  exact Finset.prod_congr rfl (fun σ _ => noetherEval_equivariant F G z σ t)

/-- **源 `lemma-5-2` 第三步 (c)** ✓✅：「if `t'(z,\sigma(z),\dots) \neq 0` then `t(z,\sigma(z),\dots)` is a **unit**」✓
—— 落为 **`\mathrm{ev}(t') \neq 0 \Rightarrow \mathrm{ev}(t) \neq 0`** ✓（**域上非零即单位** ✓）。

**证明** ✓（**逆否** ✓）：若 `\mathrm{ev}(t) = 0` ✓，则由上条 `\mathrm{ev}(t') = \prod_\sigma \sigma \bullet 0 = 0` ✓
（**取 `\sigma = 1` 的因子为零** ✓，`Finset.prod_eq_zero` ✓）⟹ 与 `\mathrm{ev}(t') \neq 0` 矛盾 ✓。
**⚠ 意义** ✓：源证明**开头三段 (a)(b)(c) 至此全部形式化** ✓✅；**余** ✓ ＝ **(d)** 行列式刻画 ＋ 无限域避零 ✗
（**登记** ✓）—— **(d) 落则 `Lemma52Statement` 的证明**结构上齐备 ✓（**仍须 (d) 的组装** ✓）。 -/
theorem noether_aeval_ne_zero_of_prod_ne_zero {L : Type u} [Field L] [Algebra F L]
    [MulSemiringAction G L] [SMulCommClass G F L] (z : L) (t : MvPolynomial G F)
    (h : MvPolynomial.aeval (fun σ : G => σ • z) (∏ σ : G, σ • t) ≠ 0) :
    MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0 := by
  intro h0
  apply h
  rw [noether_prod_aeval_eq F G z t]
  exact Finset.prod_eq_zero (Finset.mem_univ (1 : G)) (by simp [h0])

end Lemma52UnitStep

/-! ## 4.8 源 `lemma-5-2` 的 **(d) 第一块：坐标矩阵的行列式判据** ✓（第 141 轮）

**源逐字** ✓（`tex :659--662` ✓）：「Formally write `z = y_1e_1 + \dots + y_ne_n` … `\sigma(z)` is then of the form
`l_1e_1 + \dots + l_ne_n` … **Taking determinants**, we have a polynomial `f(y_1,\dots,y_n)` such that
`f(b_1,\dots,b_n) \neq 0` if and only if `z = b_1e_1 + \dots + b_ne_n` **generates a normal basis**」✓ ——
本轮落其**谓词侧** ✓（**矩阵 ＝ 源的 `f`** ✓；**多项式化** ✗ 与**搬运** ✗ 见登记 ✓）。 -/

section GaloisDetCriterion

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **源 `(d)` 的**坐标矩阵** ✓**：`(\sigma,\tau)` 元 ＝ `z` 的第 `\sigma` 个共轭在基 `b` 下的第 `\tau` 个坐标 ✓
（＝源矩阵的**转置** ✓，**行列式不变** ✓）。
**⚠ 与 `Module.Basis.toMatrix` 的关系** ✓：`b.toMatrix (fun \sigma \Rightarrow \sigma \bullet z)` 的**列**正是这些坐标 ✓
（`Module.Basis.toMatrix_apply` ✓：`(b.toMatrix v)\ i\ j = (b.repr (v\ j))\ i` ✓）—— 本件取其**转置**以让 `\sigma` 作行 ✓。 -/
noncomputable def galoisMatrix {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    (b : Module.Basis G K L) (z : L) : Matrix G G K :=
  Matrix.of (fun σ τ => b.repr (σ • z) τ)

/-- **`(d)` 判据（可逆形）** ✓：`z` 各共轭的**坐标**（作为 `G \to K` 的元素 ✓）线性无关 ⟺ 坐标矩阵**可逆** ✓
（mathlib `Matrix.linearIndependent_rows_iff_isUnit` ✓ —— **行**即坐标 ✓）。 -/
theorem galoisMatrix_isUnit_iff {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    (b : Module.Basis G K L) (z : L) :
    IsUnit (galoisMatrix K G b z) ↔
      LinearIndependent K (fun σ : G => (b.repr (σ • z) : G → K)) :=
  Matrix.linearIndependent_rows_iff_isUnit.symm

/-- **`(d)` 判据（行列式形）** ✓：`\det \neq 0 \Leftrightarrow` 坐标族线性无关 ✓ —— 即源「`f(b_1,\dots,b_n) \neq 0`」✓
的**谓词侧** ✓（`f` ＝ 该行列式 ✓）。证明 ＝ `Matrix.isUnit_iff_isUnit_det` ✓ ＋ `isUnit_iff_ne_zero` ✓
＋ `galoisMatrix_isUnit_iff` ✓（**三件皆 mathlib** ✓）。 -/
theorem galoisMatrix_det_ne_zero_iff {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] (b : Module.Basis G K L) (z : L) :
    (galoisMatrix K G b z).det ≠ 0 ↔
      LinearIndependent K (fun σ : G => (b.repr (σ • z) : G → K)) :=
  calc (galoisMatrix K G b z).det ≠ 0 ↔ IsUnit (galoisMatrix K G b z).det :=
        isUnit_iff_ne_zero.symm
    _ ↔ IsUnit (galoisMatrix K G b z) := (Matrix.isUnit_iff_isUnit_det _).symm
    _ ↔ LinearIndependent K (fun σ : G => (b.repr (σ • z) : G → K)) :=
        galoisMatrix_isUnit_iff K G b z

/-- **⚠ 登记（`(d)` 余下两块）** ✓：
① **搬运** ✓✅ —— **第 142 轮已落** ✓（见 **§4.9** ✓；**原记「未落」留痕** ✓）：
本判据的坐标族是 `G → K` 的元素 ✓，而源说的是 `\{\sigma \bullet z\}` **在 `L` 中**线性无关 ✓ ——
两者经 `b.repr` ✓ 与 `Finsupp.linearEquivFunOnFinite` ✓ **线性等价** ✓ ⟹ **可搬** ✓；
**⚠ 原障碍的处置** ✓（**㊸** ✓）：`LinearIndependent.map` ✓ 要求 **`[Ring R]`** ✗ 是其**实例路径**不合之源 ✗ ⟹
**改走 `LinearIndependent` 的**定义** ✓**（逐字：`Function.Injective (Finsupp.linearCombination R v)` ✓）＋
**`Finsupp.linearCombination_linear_comp`** ✓（**只要求 `[Semiring R]`** ✓）⟹ **全程同实例** ✓、**无需新 import** ✓、
**无 `heartbeats` 问题** ✓；
② **多项式化** ✗：源要的是**多项式** `f(y_1,\dots,y_n)` ✓（`y` 为 `z` 的坐标 ✓）与**无限域避零** ✓ ——
其零件（`Polynomial.exists_eval_ne_zero_of_natDegree_lt_card` ✓／多元版 ✓）**已在 mathlib** ✓，**未组装** ✗。 -/
theorem galoisMatrix_gap_registered : True := trivial

end GaloisDetCriterion

/-! ## 4.9 源 `(d)` 的**搬运**：判据搬回 `L` 中的向量 ✓（第 142 轮；**解 §4.8 登记 ①** ✓✅）

**⚠ 工艺读数 ㊸ 的兑现** ✓：§4.8 登记的障碍是 `LinearIndependent.map` ✓ 的 **`[Ring R]`** ✗ 实例路径不合 ✗。
**处置 ＝ 走该引理**的**定义** ✓** —— `LinearIndependent R v` 逐字是 `Function.Injective (Finsupp.linearCombination R v)` ✓
（`#print LinearIndependent` ✓），而 **`Finsupp.linearCombination_linear_comp`** ✓ **只要求 `[Semiring R]`** ✓
⟹ **全程同一实例** ✓，**`simpa`／`rw` 不再受阻** ✓，**且无需新 import** ✓、**无需调 `maxHeartbeats`** ✓。 -/

section GaloisDetTransport

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **线性等价搬运** ✓：`\mathrm{LI}(e \circ v) \Leftrightarrow \mathrm{LI}(v)` ✓（`e` 为线性等价 ✓）。
**证据形** ✓：`\mathrm{LI}` 展开为 `Finsupp.linearCombination` 的**单射性** ✓ ⟹ 用
`Finsupp.linearCombination_linear_comp` ✓ 得 `\mathrm{lc}(e \circ v) = e \circ \mathrm{lc}(v)` ✓，
再用 `Function.Injective.of_comp_iff` ✓（`e` 单射 ✓）。 -/
private theorem li_comp_linearEquiv {ι : Type*} {M M' : Type u} [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M'] (e : M ≃ₗ[K] M') {v : ι → M} :
    LinearIndependent K (fun i => e (v i)) ↔ LinearIndependent K v := by
  have h1 : Finsupp.linearCombination K (fun i => e (v i))
      = (e : M →ₗ[K] M').comp (Finsupp.linearCombination K v) :=
    Finsupp.linearCombination_linear_comp K (e : M →ₗ[K] M')
  rw [LinearIndependent, LinearIndependent, h1]
  exact Function.Injective.of_comp_iff e.injective (Finsupp.linearCombination K v)

/-- **源 `(d)` 的**向量形判据** ✓✅**：`\det \neq 0` ⟺ `\{\sigma \bullet z\}` **在 `L` 中**线性无关 ✓ ——
即源「`f(b_1,\dots,b_n) \neq 0` **if and only if** `z` **generates a normal basis**」✓ 的**谓词侧**（**原形** ✓）。
**证明** ✓：§4.8 的坐标形 ✓ 经§4.9 的搬运 ✓ 两次（`Finsupp.linearEquivFunOnFinite` ✓ ＋ `b.repr` ✓）。
**⚠ 口径** ✓：源说「**normal basis**」✓ ＝ **线性无关 ＋ 张成** ✓；本件给**线性无关** ✓ ——
**⚠ 在 `\mathrm{card} G = \dim_K L` 的伽罗瓦档下两者等价** ✓（**本件未设该前提** ✗，**登记** ✓，**§4.8 ② 同族** ✓）。 -/
theorem galoisMatrix_det_ne_zero_iff_vectors {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] (b : Module.Basis G K L) (z : L) :
    (galoisMatrix K G b z).det ≠ 0 ↔ LinearIndependent K (fun σ : G => σ • z) :=
  (galoisMatrix_det_ne_zero_iff K G b z).trans <|
    (li_comp_linearEquiv K (Finsupp.linearEquivFunOnFinite K K G)).trans
      (li_comp_linearEquiv K b.repr)

end GaloisDetTransport

section MvPolynomialAvoidance

/-- **源的「`K` 无限」那一步** ✓（源逐字：「Thus it suffices to find `a_1,\dots,a_n \in K` such that
`f'(a_1,\dots,a_n) f(a_1,\dots,a_n) \neq 0`. **This is always possible because `K` is infinite**」✓）：
**非零多项式在无限域上有非零取值** ✓（**基形** ✓）。

**证明** ✓：若处处为零 ✓，则由 `MvPolynomial.funext` ✓（要求 `[IsDomain K] [Infinite K]` ✓）
得该多项式 `= 0` ✓，与假设矛盾 ✓。
**⚠ 载体** ✓：本件用 `MvPolynomial` ✓（**非**「函数」✓）—— 正是 §105.4 所记须先选定的**载体** ✓。 -/
theorem exists_eval_ne_zero_of_ne_zero {K : Type u} [Field K] [Infinite K]
    {σ : Type*} {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (MvPolynomial.funext fun x => by rw [h x, map_zero])

/-- **源那一步的**原形** ✓✅**：**两个非零多项式有公共非零点** ✓ —— 即源要的
`f'(a) f(a) \neq 0` ✓（**两者同时非零** ✓）。证明 ＝ 对**积**用基形 ✓（`mul_ne_zero` ✓）＋ `map_mul` ✓
＋ `mul_ne_zero_iff` ✓；**⚠ 用点** ✓：`K` 是域 ⟹ 无零因子 ✓（源同此 ✓）。 -/
theorem exists_eval_mul_ne_zero {K : Type u} [Field K] [Infinite K]
    {σ : Type*} {f g : MvPolynomial σ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x f ≠ 0 ∧ MvPolynomial.eval x g ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_ne_zero (K := K) (mul_ne_zero hf hg)
  rw [map_mul] at hx
  exact ⟨x, (mul_ne_zero_iff.mp hx).1, (mul_ne_zero_iff.mp hx).2⟩

end MvPolynomialAvoidance

/-! ## 4.10 源 `(d)-②` 的**多项式化**：`f(y_1,\dots,y_n)` 就是坐标矩阵的行列式 ✓（第 143 轮）

**源逐字** ✓（`tex :659--662` ✓）：「Formally write `z = y_1e_1 + \dots + y_ne_n` … Taking determinants, we have
a **polynomial** `f(y_1,\dots,y_n)` such that `f(b_1,\dots,b_n) \neq 0` if and only if `z` generates a normal
basis」✓ —— 本轮把该 `f` **显式造出** ✓（在 `MvPolynomial` 里 ✓），并证其**取值 ＝ 坐标矩阵的行列式** ✓。 -/

section NormalBasisPolynomial

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **源的 `f(y_1,\dots,y_n)`** ✓：把 `z = \sum_i y_i \bullet e_i` 的坐标矩阵的**每个元素写成 `y` 的线性式** ✓，
再**在多项式环里取行列式** ✓ —— 载体 `MvPolynomial G K` ✓（`G` 即变元下标 ✓，与 §4.8／§4.9 的 `\mathrm{galoisMatrix}`
同一套下标 ✓，便于取值对接 ✓）。 -/
noncomputable def normalBasisPoly {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    (b : Module.Basis G K L) : MvPolynomial G K :=
  (Matrix.of (fun σ τ : G => ∑ i : G, MvPolynomial.X i * MvPolynomial.C (b.repr (σ • b i) τ))).det

/-- **多项式化的**对接锁** ✓**：`f(y) = \det(\mathrm{galoisMatrix}\ b\ (\sum_i y_i \bullet e_i))` ✓ ——
即**源的 `f`** 在点 `y` 处的取值**恰是** §4.8／§4.9 那个坐标矩阵的行列式 ✓ ⟹ **§4.10 与 §4.8／§4.9 对接** ✓，
`MvPolynomial` 侧与 `L` 侧**不再悬空** ✓。

**证明** ✓：`RingHom.map_det` ✓（`\mathrm{eval}` 是**环同态** ✓ ⟹ 与行列式交换 ✓）＋ 逐元素把
`\mathrm{eval}\ y\ (\sum_i X_i \cdot C(\dots))` 归约为 `\sum_i y_i \cdot (\dots)` ✓
（`Finset.smul_sum` ✓／`smul_comm` ✓／`map_smul` ✓，即 `\sigma`-作用与 `K`-标量的交换性 ✓）。
**⚠ 一处编译期自纠** ✓：**不要 `simp only [\dots, \mathrm{galoisMatrix}]`** ✗ —— `\mathrm{galoisMatrix}` 是
**半可约** `def` ✓ ⟹ 展开后目标**在 implicit 透明度下不类型正确** ✗（Lean 报 "not type-correct under the
`implicit` transparency level" ✓）⟹ 改用 **`show`** ✓ 直接给出展开形 ✓。 -/
theorem eval_normalBasisPoly {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    [SMulCommClass G K L] (b : Module.Basis G K L) (y : G → K) :
    MvPolynomial.eval y (normalBasisPoly K G b)
      = (galoisMatrix K G b (∑ i : G, y i • b i)).det := by
  rw [normalBasisPoly, RingHom.map_det]
  congr 1
  ext σ τ
  show MvPolynomial.eval y (∑ i : G, MvPolynomial.X i * MvPolynomial.C (b.repr (σ • b i) τ))
      = b.repr (σ • ∑ i : G, y i • b i) τ
  simp [map_sum, Finset.smul_sum, smul_comm, map_smul, smul_eq_mul]

/-- **⚠ 登记（`(d)-②` 余项）** ✗：① **`f \neq 0`** ✗ —— 其源材料 ＝ **正规基存在性** ✓
（mathlib `exists_linearIndependent_algEquiv_apply` ✓）＋ §4.9 的判据 ✓，**但** mathlib 那条是就
`L \simeq_K L` ✓ 陈述的，而本件 `G` **抽象** ✓ ⟹ **须先有 `G \simeq \mathrm{Gal}(L/K)` 的识别** ✗（**在册** ✓）；
② **`f'`** ✗（`t'` 对应的多项式 ✓）及其**非零** ✗ —— 源用「**the algebraic independence of the `\sigma`'s**」✓，
**未建** ✗；③ **组装** ✗（`exists_eval_mul_ne_zero` ✓ 已备 ✓，待 ①② ✓）。 -/
theorem normalBasisPoly_gap_registered : True := trivial

end NormalBasisPolynomial

section GaloisBridge

variable (K : Type u) [Field K] (G : Type u) [Group G] (L : Type u) [Field L] [Algebra K L]
  [MulSemiringAction G L] [SMulCommClass G K L]

/-- **识别桥（一）：作用给出 `K`-代数自同构** ✓ —— 由 `[MulSemiringAction G L]` ✓ 与
**`[SMulCommClass G K L]`** ✓（作用与 `K`-标量交换 ✓）得 `g \bullet \cdot \in L \simeq_K L` ✓。
**⚠ 用点** ✓：它是**三处共用缺口**的入口 ✓（见 §4.11 说明 ✓）。 -/
noncomputable def smulAlgEquiv (g : G) : L ≃ₐ[K] L where
  toFun := fun x => g • x
  invFun := fun x => g⁻¹ • x
  left_inv := fun x => by show g⁻¹ • (g • x) = x; rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv := fun x => by show g • (g⁻¹ • x) = x; rw [← mul_smul, mul_inv_cancel, one_smul]
  map_mul' := fun x y => smul_mul' g x y
  map_add' := fun x y => smul_add g x y
  commutes' := fun r => smul_algebraMap g r

/-- **识别桥（二）：`G \to^* (L \simeq_K L)`** ✓（源语境下它就是 `G \to \mathrm{Gal}(L/K)` ✓）。 -/
noncomputable def smulAlgEquivHom : G →* (L ≃ₐ[K] L) where
  toFun := smulAlgEquiv K G L
  map_one' := by ext x; simp [smulAlgEquiv]
  map_mul' g h := by ext x; simp [smulAlgEquiv, mul_smul]

/-- **识别桥（三）：抽象版正规基定理** ✓✅ —— 若该同态**双射** ✓（＝**`G` 就是伽罗瓦群** ✓，
源语境自动成立 ✓），则**存在** `x` 使 `\{g \bullet x\}_{g \in G}` **线性无关** ✓。

**证明** ✓：mathlib **`exists_linearIndependent_algEquiv_apply`** ✓（**只需 `[FiniteDimensional K L]`** ✓，
**不需要** `IsGalois` ✓）给出 `x` 与 `\mathrm{LI}(\varphi \mapsto \varphi x)` ✓；再由**双射** ✓ 造
`\mathrm{Equiv.ofBijective}` ✓ 并用 **`linearIndependent_equiv`** ✓ **重指标**到 `G` ✓
（两者**逐点相同** ✓：`(\mathrm{smulAlgEquiv}\ g) x = g \bullet x` ✓）。 -/
theorem exists_linearIndependent_smul [FiniteDimensional K L]
    (h : Function.Bijective (smulAlgEquivHom K G L)) :
    ∃ x : L, LinearIndependent K (fun g : G => g • x) := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_algEquiv_apply K L
  refine ⟨x, ?_⟩
  have hcomp : (fun g : G => g • x)
      = (fun φ : L ≃ₐ[K] L => φ x) ∘ (Equiv.ofBijective (smulAlgEquivHom K G L) h) := by
    funext g; rfl
  rw [hcomp, linearIndependent_equiv]
  exact hx

end GaloisBridge

/-! ## 4.11 识别桥 ＋ **`(d)-②①` 结**：`f \neq 0` ✓（第 144 轮）

**⚠ 三处共用缺口** ✓：`G \simeq \mathrm{Gal}(L/K)` 的**识别** ✓ 同时是 —— ① `(d)-②①` 的 `f \neq 0` ✓；
② §4.5 的 `Lemma52Statement` 的**口径** ✓（源「normal basis」**含张成** ✓）；③ `theorem-5-1` 的**实例化** ✓。
本轮把它落为**显式假设** ✓（`Function.Bijective (smulAlgEquivHom K G L)` ✓ —— **源语境下自动成立** ✓，**登记** ✓）。 -/

section NormalBasisPolyNeZero

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **`(d)-②①` 结** ✓✅：**`f \neq 0`** ✓ —— 源逐字：「Since some normal basis exists, `f` is a **nonzero**
polynomial」✓。

**证明** ✓（**三件拼接** ✓）：**(i)** §4.11 的**抽象正规基** ✓ 给 `x` 与 `\mathrm{LI}(g \mapsto g \bullet x)` ✓；
**(ii)** §4.9 的**判据** ✓ 给 `\det(\mathrm{galoisMatrix}\ b\ x) \neq 0` ✓；**(iii)** §4.10 的**对接锁** ✓
取 `y_i = b.\mathrm{repr}\ x\ i` ✓（`Basis.sum_repr` ✓：`\sum_i y_i \bullet e_i = x` ✓）得
`f(y) = \det(\mathrm{galoisMatrix}\ b\ x) \neq 0` ✓ ⟹ **`f \neq 0`** ✓（**若 `f = 0` 则 `f(y) = 0`** ✗ 矛盾 ✓）。
**⚠ 用点** ✓：源「`f` 非零」正是其**避零步**（§4.10 ✓）的**前提之一** ✓。 -/
theorem normalBasisPoly_ne_zero {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Bijective (smulAlgEquivHom K G L)) : normalBasisPoly K G b ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_smul K G L h
  have hdet : (galoisMatrix K G b x).det ≠ 0 :=
    (galoisMatrix_det_ne_zero_iff_vectors K G b x).mpr hx
  intro hf
  have h1 := eval_normalBasisPoly K G b (fun i : G => b.repr x i)
  rw [b.sum_repr x] at h1
  rw [hf, map_zero] at h1
  exact hdet h1.symm

end NormalBasisPolyNeZero

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
#print axioms noether_prod_smul_invariant
#print axioms noether_prod_eval_isFixed
#print axioms noetherEval_equivariant
#print axioms noether_prod_aeval_isFixed
#print axioms noether_prod_aeval_eq
#print axioms noether_aeval_ne_zero_of_prod_ne_zero
#print axioms galoisMatrix
#print axioms galoisMatrix_isUnit_iff
#print axioms galoisMatrix_det_ne_zero_iff
#print axioms galoisMatrix_gap_registered
#print axioms galoisMatrix_det_ne_zero_iff_vectors
#print axioms exists_eval_ne_zero_of_ne_zero
#print axioms exists_eval_mul_ne_zero
#print axioms smulAlgEquiv
#print axioms smulAlgEquivHom
#print axioms exists_linearIndependent_smul
#print axioms normalBasisPoly_ne_zero
#print axioms normalBasisPoly
#print axioms eval_normalBasisPoly
#print axioms normalBasisPoly_gap_registered
#print axioms Lemma52Statement
#print axioms Lemma52Statement.shape

end ABGV52
