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
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Fixed
import ABGV52.BaseChangeProj_ABGV52
import Mathlib.RingTheory.TensorProduct.Finite

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
**(ii)** 源要 `F` **无限** ✓；本件**未设**该前提 ✗（**第 134 轮登记** ✓）—— **⚠ r195 已回正** ✓✅：
谓词体现在**含** `Infinite F →` ✓（源 `raw/Saltman1982.tex :640` ✓ **逐字** ✓），**rfl 型锁**见
`Theorem51Statement.faithful_lock` ✓（**删去该前提即 `rfl` 失败** ✓）。
**⚠ 源的另一处判别性事实** ✓（`remark` 印 275 ✓）：「The **converse** of `theorem-5-1` is **false**.
`C_{47}` has a generic extension over `Q`, but **Swan showed Noether's Problem false** for this group」✓
⟹ 本两条 M6 路线**互相独立** ✓（与 `theorem-2-1` ✓ 的条件不同 ✓），**登记** ✓。 -/
def Theorem51Statement (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] : Prop :=
  Infinite F → ∀ (L : Type u) [Field L] [Algebra F L] [MulSemiringAction G L] [SMulCommClass G F L],
    IsRationalOver F ↥(FixedPoints.subalgebra F L G) → Nonempty (GenericExtensionWitness F G)

/-- **外形锁定 ①** ✓：`IsRationalOver` 的**用点形**逐字可取 ✓（有理函数域同构 ✓）。 -/
theorem IsRationalOver.shape {F K : Type u} [Field F] [CommRing K] [Algebra F K]
    (h : IsRationalOver F K) :
    ∃ (n : ℕ), Nonempty (K ≃ₐ[F] FractionRing (MvPolynomial (Fin n) F)) :=
  h

/-- **外形锁定 ②** ✓：`Theorem51Statement` 的**两段**（**固定域有理** ✓／**存在见证** ✓）逐字可取 ✓ ——
**⚠ 前提须作独立假设传入** ✓（㉝ ✓）。 -/
theorem Theorem51Statement.shape (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (h : Theorem51Statement F G) (hinf : Infinite F) (L : Type u) [Field L] [Algebra F L]
    [MulSemiringAction G L] [SMulCommClass G F L]
    (hL : IsRationalOver F ↥(FixedPoints.subalgebra F L G)) :
    Nonempty (GenericExtensionWitness F G) :=
  h hinf L hL

/-- **源文faithful性锁** ✓✅：源 `theorem-5-1` 的**假设**「**with `F` infinite**」✓
（`raw/Saltman1982.tex :640` ✓ **逐字**）已进入**谓词体** ✓ —— **删去该前提即 `rfl` 失败** ✓（`rfl` 型锁 ✓；
与 `Theorem21Statement` 把 `SaltmanCondition` 写进谓词体**同款** ✓，`Saltman_ABGV52` 侧 ✓）。 -/
theorem Theorem51Statement.faithful_lock (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] :
    (Theorem51Statement F G)
      = (Infinite F → ∀ (L : Type u) [Field L] [Algebra F L] [MulSemiringAction G L]
          [SMulCommClass G F L],
          IsRationalOver F ↥(FixedPoints.subalgebra F L G) → Nonempty (GenericExtensionWitness F G)) :=
  rfl

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
即证源」的**形式前提**已通 ✓（**⚠ 仅形式前提** ✗ —— `Theorem51Statement` 本身**仍是具名残余** ✗）。
**⚠ r195** ✓：源的「`F` infinite」✓ 现**随谓词**传入 ✓（`hinf` ✓），调用点须显式给 ✓。 -/
theorem theorem51Statement_noetherField [Fintype G] (h : Theorem51Statement F G)
    (hinf : Infinite F)
    (hL : IsRationalOver F ↥(FixedPoints.subalgebra F (NoetherField F G) G)) :
    Nonempty (GenericExtensionWitness F G) :=
  h hinf (NoetherField F G) hL

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
auto-bound 变量 ✓）⟹ 即**强于**源 ✓（**⚠ r195 已回正** ✓：`Theorem51Statement` ✓ 现**含**「`F` 无限」✓；
本陈述**不设** `[Fintype G]` ✓ 仍**强于**源 ✓，故**另开 section** ✓）。 -/
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

/-- **⚠ 判别力探针（`L1` 在住性／非空性）** ✗✅（**第 148 轮新发现** ✗）：**本残余的假设类为空** ✗ ——
**取 `t = 0`** ✓ 则内层存在式**恒假** ✓（`\mathrm{aeval}(\dots) 0 = 0` ✓，故合取项 `\neq 0` 不成立 ✓）
⟹ **`Lemma52Statement` 是假命题** ✗（**与 `F`／`G`／`K`／`L` 无关** ✓）。

**⟹ 处置** ✓：源的 `t` **本是非零多项式** ✓（源 `lemma-5.2` 的语境 ✓）⟹ 该陈述**须加 `t \neq 0`** ✓；
**⚠ 第 149 轮已兑现** ✓✅：**修正形** `Lemma52StatementNonzero` ✓ **已证为定理** ✓（`lemma52Statement_nonzero_true` ✓，**§4.18** ✓）。
**⚠ 影响面** ✓（**实测** ✓）：`Lemma52Statement` 的**唯一**消费者是本节的 `.shape` ✓ ⟹ **该条空真** ✗（**登记** ✓）；
**全库其余无消费者** ✓。
**⚠ r200 状态收口** ✓：**修正形** `Lemma52StatementNonzero`（§4.18 ✓）**自本轮起无数据前提** ✓✅（§4.55 ✓）
⟹ 本条**保留作留痕** ✓（**是「已反驳」而非「未证」** ✗⟹✓）。 -/
theorem Lemma52Statement.false_at_zero (K L : Type u) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] [MulSemiringAction G L] :
    ¬ Lemma52Statement F G K L := fun h => by
  obtain ⟨z, b, -, hne⟩ := h 0
  exact hne (map_zero _)

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
**未建** ✗；③ **组装** ✗（`exists_eval_mul_ne_zero` ✓ 已备 ✓，待 ①② ✓）。
**⚠ r199 已落（域档）** ✓✅：**① 的入口**（＝ `G ≃ \mathrm{Gal}(L/K)` 的识别 ✓）**已通** ✓ ——
见 §4.54 `smulAlgEquivHom_bijective_of_isGaloisWithGroup` ✓；**⚠ 本条余项 ①②③ 本身仍未落** ✗（**不复写** ✗）。 -/
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

section FiniteDimensionalOfBasis

variable (K : Type u) [Field K] (G : Type u) [Fintype G]

/-- **口径消除** ✓（r144 登记 ② 的兑现 ✓）：**基 ⟹ `[FiniteDimensional K L]`** ✓ ——
`Module.Finite.of_basis` ✓（`[Fintype G]` ⟹ `[Finite G]` ✓）＋ `FiniteDimensional` 与 `Module.Finite` 的
**定义等同** ✓ ⟹ §4.11 的 `[FiniteDimensional K L]` **前提可去** ✗⟹✓。 -/
theorem finiteDimensional_of_basis {L : Type u} [Field L] [Algebra K L]
    (b : Module.Basis G K L) : FiniteDimensional K L :=
  Module.Finite.of_basis b

end FiniteDimensionalOfBasis

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
theorem normalBasisPoly_ne_zero {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Bijective (smulAlgEquivHom K G L)) : normalBasisPoly K G b ≠ 0 := by
  have : FiniteDimensional K L := finiteDimensional_of_basis K G b
  obtain ⟨x, hx⟩ := exists_linearIndependent_smul K G L h
  have hdet : (galoisMatrix K G b x).det ≠ 0 :=
    (galoisMatrix_det_ne_zero_iff_vectors K G b x).mpr hx
  intro hf
  have h1 := eval_normalBasisPoly K G b (fun i : G => b.repr x i)
  rw [b.sum_repr x] at h1
  rw [hf, map_zero] at h1
  exact hdet h1.symm

end NormalBasisPolyNeZero


/-! ## 4.12 源 `(d)-②②` 的**载体**：`f'` 的多项式化（第 145 轮；**恒等式待落** ✗） -/

section ConjEvalPoly

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G]

/-- **源 `(d)-②②` 的 `f'` 的**载体** ✓** —— 源逐字：「Substituting the above expressions for the `\sigma(z)`'s,
we have that `t(z,\sigma(z),\dots) = f'(y_1,\dots,y_n)` for some polynomial `f'`」✓ ⟹ `f'` ＝
**把 `x_\tau` 代入 `\tau \bullet (\sum_i y_i \bullet e_i)`** ✓ 后的多项式 ✓。

**⚠ 载体口径** ✓（**本轮新发现** ✓）：代入后的**系数在 `L` 中** ✗（`\tau \bullet e_i \in L` ✓）⟹ 载体须是
**`MvPolynomial G L`** ✓（**不是** `MvPolynomial G K` ✗ —— 源写「coefficients in `K`」✓ 是因它用的是
**不变**的 `t'` ✓，其取值**落在 `K`** ✓，即 (b) 段 ✓；**本件对一般 `t` 造** ✓，故载体在 `L` ✓，**登记** ✓）。
用 `MvPolynomial.aeval` ✓（**可换基环** ✓：目标 `MvPolynomial G L` 是 `K`-代数 ✓）。 -/
noncomputable def conjEvalPoly {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    (b : Module.Basis G K L) (t : MvPolynomial G K) : MvPolynomial G L :=
  MvPolynomial.aeval (fun τ : G => ∑ i : G, MvPolynomial.C (τ • b i) * MvPolynomial.X i) t

/-- **⚠ 登记（`(d)-②②` 余项，**未落** ✗）** ✓：
**(i) 取值恒等式** ✓✅ —— **第 146 轮已落** ✓（`eval_conjEvalPoly` ✓，见 **§4.13** ✓；**原记「未落」留痕** ✓）；
**⚠ 原记的「须先 `show`」亦被证否** ✗⟹✓：**把 `\mathrm{aeval}` 形显式写出** ✓（不写成 `\mathrm{conjEvalPoly}` ✓）
⟹ 归纳各支**自然可化简** ✓、**无需 `show`** ✓（**㊹ 的正面应用** ✓）；
**(ii) 非零 ＋ `K`-系数形** ✗ —— **第 147 轮已隔离为具名残余** ✓✅（`ConjEvalPolyKStatement` ✓，见 **§4.14** ✓；
**原记「须先定可用形」的答案即此** ✓）；**⚠ 口径发现 ㊽** ✓（第 147 轮 ✓）：**「系数在 `K`」是承重的** ✗⟹✓ ——
**避零步须在 `K` 上做** ✓（两侧多项式同为 `K`-系数 ✓）⟹ **L-点路线走不通** ✗（会与 §4.9 的 **K-坐标判据**错配 ✗，
**实测** ✓：`eval₂ (algebraMap K L) y (normalBasisPoly …)` 的值在 `L` ✗ 而判据的 `\det` 在 `K` ✗）；
**(ii) 已证** ✓✅ —— **第 148 轮** ✓：**`conjEvalPoly_ne_zero`** ✓（**§4.16** ✓，**非零核心** ✓），
且**避零条改在 `L` 上取** ✓（**§4.15** ✓）⟹ **`K`-系数形无须使用** ✓（**㊽ 的处置兑现** ✓）；
**(iii) 组装** ✓✅ —— **第 147 轮已落** ✓（`exists_linearIndependent_smul_aeval_ne_zero` ✓，**条件形** ✓；
**无条件形见 §4.17** ✓）。 -/
theorem conjEvalPoly_gap_registered : True := trivial

end ConjEvalPoly

section EvalAevalComp

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]
variable {σ τ : Type*}

/-- **`\mathrm{eval}` 与 `\mathrm{aeval}` 的复合律** ✓（**mathlib 无此条** ✗，本件自证 ✓）：
`\mathrm{eval}\ y\ (\mathrm{aeval}\ g\ t) = \mathrm{aeval}\ (\tau \mapsto \mathrm{eval}\ y\ (g\ \tau))\ t` ✓ ——
即**先代入后取值 ＝ 先取值后代入** ✓。

**证明** ✓：对 `t` 作 `MvPolynomial.induction_on` ✓（**各支的 `\mathrm{aeval}` 形是显式写出的** ✓
⟹ **不触发 ㊹** ✓，**无需 `show`** ✓ —— 这是 §4.10／r143 教训的**正面应用** ✓）。
**⚠ 载体口径** ✓：左右两侧**基环不同** ✓（内层 `R` ✓／外层 `S` ✓）⟹ 本律**不能**由 `aeval_bind₁` ✓ 直接得 ✗
（那条要求同一基环 ✗）。 -/
theorem eval_aeval_poly (g : σ → MvPolynomial τ S) (y : τ → S) (t : MvPolynomial σ R) :
    MvPolynomial.eval y (MvPolynomial.aeval g t)
      = MvPolynomial.aeval (fun i => MvPolynomial.eval y (g i)) t := by
  induction t using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

end EvalAevalComp

/-! ## 4.13 源 `(d)-②②(i)` 结：`f'` 的**取值恒等式** ✓（第 146 轮） -/

section ConjEvalPolyIdentity

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G]

/-- **源 `(d)-②②(i)` 结** ✓✅：**`f'(y) = \mathrm{aeval}(\tau \mapsto \tau \bullet (\sum_i y_i \bullet e_i))\ t`** ✓ ——
即源逐字「Substituting the above expressions for the `\sigma(z)`'s, we have that
`t(z,\sigma(z),\dots) = f'(y_1,\dots,y_n)`」✓ 的**恒等式侧** ✓（`z = \sum_i y_i \bullet e_i` ✓）。

**证明** ✓：§4.13 的**复合律** ✓ ＋ **线性式取值** ✓（`\mathrm{eval}\ y'\ (\sum_i C(\tau \bullet e_i) \cdot X_i)
= \tau \bullet (\sum_i y_i \bullet e_i)` ✓ —— 由 `map_sum` ✓／`Finset.smul_sum` ✓／`Algebra.smul_def` ✓）。
**⚠ 一处编译期自纠** ✓：线性式的逐项化简**须试三轮** ✗（`smul_mul'` ✗ 模式不符 ⟹ `smul_algebraMap` ✗ 因
**强制转换的语法形**不匹配 ⟹ 终由 `simp [mul_comm, Algebra.smul_def]` ✓ 收口 ✓）—— **新工艺读数 ㊼** ✓（见 109.4 ✓）。 -/
theorem eval_conjEvalPoly {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    [SMulCommClass G K L] (b : Module.Basis G K L) (t : MvPolynomial G K) (y : G → K) :
    MvPolynomial.eval (fun i : G => algebraMap K L (y i)) (conjEvalPoly K G b t)
      = MvPolynomial.aeval (fun τ : G => τ • (∑ i : G, y i • b i)) t := by
  have hg : ∀ τ : G, MvPolynomial.eval (fun i : G => algebraMap K L (y i))
      (∑ i : G, MvPolynomial.C (τ • b i) * MvPolynomial.X i)
      = τ • (∑ i : G, y i • b i) := by
    intro τ
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp [mul_comm, Algebra.smul_def]
  show MvPolynomial.eval (fun i : G => algebraMap K L (y i))
      (MvPolynomial.aeval (fun τ : G => ∑ i : G, MvPolynomial.C (τ • b i) * MvPolynomial.X i) t)
    = MvPolynomial.aeval (fun τ : G => τ • (∑ i : G, y i • b i)) t
  rw [eval_aeval_poly]
  simp only [hg]

end ConjEvalPolyIdentity

section ConjEvalPolyKStatementSec

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G]

/-- **源 `(d)-②②(ii)` 的**忠实具名残余** ✓**：源逐字「we have that `t(z,\sigma(z),\dots) = f'(y_1,\dots,y_n)` for some
polynomial `f'` **with coefficients in `K`**. **By the algebraic independence of the `\sigma`'s, `f'` is nonzero**」✓ ——
本定义**逐项对应该句** ✓：**①** `f'` **系数在 `K`** ✓（`p : MvPolynomial G K` ✓）；**②** `f' \neq 0` ✓；
**③** 取值恒等式 ✓（`f'(a) = t'(z,\sigma(z),\dots)` ✓，`z = \sum_i a_i \bullet e_i` ✓，
**⚠ 须经 `\mathrm{algebraMap}`** ✓ —— 因右侧在 `L` ✓ 而 `f'` 的值在 `K` ✓，**这一步正是 (b) 段** ✓）。

**⚠ 为什么是 `t' = \prod_\sigma \sigma \bullet t`** ✓（**本轮口径发现 ㊽** ✓）：源的第二条件是关于**不变**式 `t'` ✓，
其取值**落在 `K`** ✓（(b) 段 ✓）⟹ **只有对 `t'` 才可能有 `K`-系数多项式** ✓；对**一般 `t`** ✗ 取值在 `L` ✓、
系数须在 `L` ✗ ⟹ 本件**只对 `t'` 陈述** ✓（**忠实** ✓）。

**⚠ 第 148 轮口径修正** ✓（**㊽ 的处置** ✓）：本残余**已不在关键路径上** ✓ —— **§4.15** 的 `K`-点密度避零 ✓
＋ **§4.16** 的非零核心 ✓ **直接供足 §4.14 的前提** ✓（**无须任何 `K`-系数下降** ✓）。
**⚠ ㊽ 的发现仍有效** ✓（两条 L-点路径确实失败 ✓，**实测** ✓）；但其**结论**「必须下降到 `K`」**被取代** ✓
（**第三条路**：多项式仍在 `L` 上 ✓，只把避零点限制在 `K`-点 ✓）⟹ 本件**保留作留痕** ✓。 -/
def ConjEvalPolyKStatement {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    (b : Module.Basis G K L) (t : MvPolynomial G K) : Prop :=
  ∃ p : MvPolynomial G K, p ≠ 0 ∧ ∀ a : G → K,
    algebraMap K L (MvPolynomial.eval a p)
      = MvPolynomial.aeval (fun σ : G => σ • (∑ i : G, a i • b i)) (∏ σ : G, σ • t)

/-- **形状锁** ✓（**L 型** ✓）：本残余的**展开形** ✓（承 L19 惯例 ✓）。 -/
theorem conjEvalPolyKStatement_shape {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L]
    (b : Module.Basis G K L) (t : MvPolynomial G K) :
    ConjEvalPolyKStatement K G b t ↔ ∃ p : MvPolynomial G K, p ≠ 0 ∧ ∀ a : G → K,
      algebraMap K L (MvPolynomial.eval a p)
        = MvPolynomial.aeval (fun σ : G => σ • (∑ i : G, a i • b i)) (∏ σ : G, σ • t) :=
  Iff.rfl

end ConjEvalPolyKStatementSec

/-! ## 4.14 源 `(d)-②②(iii)` 结：**端到端结论（条件形）** ✓（第 147 轮）

**⚠ 结构** ✓：源的 `(d)` 论证 ＝ **(i)** 多项式化 ✓（§4.10／§4.12／§4.13 ✓）＋ **(ii)** `f' \neq 0` ✗（**本件隔离为上一条残余** ✓）
＋ **(iii)** **避零组装** ✓（本节 ✓）。源逐字：「Thus it suffices to find `a_1,\dots,a_n \in K` such that
`f'(a_1,\dots,a_n) f(a_1,\dots,a_n) \neq 0`. This is always possible because `K` is infinite」✓。 -/

section EndToEndSec

variable (K : Type u) [Field K] [Infinite K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **源 `(iii)` 结 ＋ `(d)` 的端到端结论（条件形）** ✓✅：**给定 (ii)** ✓（`\mathrm{ConjEvalPolyKStatement}` ✓），
则**存在** `z \in L` 使 **`\{g \bullet z\}` 线性无关** ✓（＝ **生成正规基** ✓，`\mathrm{card} G = \dim_K L` 时 ✓）
**且** `t(z,\sigma(z),\dots) \neq 0` ✓ —— 即**源 `lemma-5.2` 证明的结论** ✓。

**证明** ✓（**四件拼接** ✓，**皆本库已有** ✓）：**(1)** `f \neq 0` ✓（§4.11 ✓）；**(2)** 由 (ii) 得 `p \neq 0` ✓；
**(3)** **避零步** ✓（§4.10 ✓：`\mathrm{exists\_eval\_mul\_ne\_zero}` ✓）给 `a : G \to K` 使
`f(a) \neq 0` ✓ **且** `p(a) \neq 0` ✓；**(4)** `f(a) \neq 0` ⟹ **判据** ✓（§4.9 ✓）给 `\mathrm{LI}` ✓；
`p(a) \neq 0` ＋ **(ii) 的取值恒等式** ✓ 给 `\mathrm{ev}(t') \neq 0` ✓（**经 `\mathrm{algebraMap}` 单射** ✓），
再由 **(c)** ✓（§4.7 ✓：`\mathrm{noether\_aeval\_ne\_zero\_of\_prod\_ne\_zero}` ✓）降为 `\mathrm{ev}(t) \neq 0` ✓。

**⚠ 意义** ✓：**`[6]`「`(d)` 的组装」至此闭合** ✓；**全库仅余 `(ii)` 一块** ✗（**已隔离为具名残余** ✓）
⟹ **`lemma-5.2` 的证明**只差 (ii) ✓。
**⚠ 第 148 轮** ✓：**(ii) 已证** ✓✅；**无条件形**见 **§4.17** ✓（**本条件形保留** ✓）。 -/
theorem exists_linearIndependent_smul_aeval_ne_zero {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Bijective (smulAlgEquivHom K G L)) (t : MvPolynomial G K)
    (hK : ConjEvalPolyKStatement K G b t) :
    ∃ z : L, LinearIndependent K (fun σ : G => σ • z)
      ∧ MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0 := by
  obtain ⟨p, hp, hp_eval⟩ := hK
  obtain ⟨a, ha, ha'⟩ := exists_eval_mul_ne_zero (normalBasisPoly_ne_zero K G b h) hp
  have hmap : (algebraMap K L) (MvPolynomial.eval a p) ≠ 0 := fun h0 =>
    ha' ((algebraMap K L).injective (by rw [h0, map_zero]))
  rw [hp_eval a] at hmap
  refine ⟨∑ i : G, a i • b i, ?_, ?_⟩
  · rw [← galoisMatrix_det_ne_zero_iff_vectors K G b]
    rw [← eval_normalBasisPoly K G b a]
    exact ha
  · exact noether_aeval_ne_zero_of_prod_ne_zero K G (∑ i : G, a i • b i) t hmap

end EndToEndSec

/-! ## 4.15 **新路线（Ⅰ）：`K`-点密度避零** ✓✅（第 148 轮 —— **解 ㊽ 的障碍** ✓）

**⚠ 本轮口径修正** ✓（**㊽ 的处置兑现** ✓）：第 147 轮实测两条 **L-点路线** ✗ **失败** ✓（**保留** ✓：
① `\mathrm{eval}_2 (\mathrm{algebraMap}\ K\ L)\ y\ (\mathrm{normalBasisPoly}\dots)` 的值在 `L` ✗ 而判据的
`\det` 在 `K` ✗；② L-点的坐标矩阵与 `z` 的 `K`-坐标矩阵**是两个不同矩阵** ✗），并据此判
「源的『系数在 `K`』是**承重的**」✓。**⚠ 该判断只对「`\mathrm{exists\_eval\_mul\_ne\_zero}` 型避零」成立** ✗，
**对目标不成立** ✓ —— 关键在 **mathlib 的 `MvPolynomial.funext_set`** ✓（**第 147 轮未察** ✗）：
**域上 L-系数多项式在一条「各边无限」的盒上处处为零 ⟹ 恒零** ✓。取盒边 ＝
`\mathrm{Set.range}(\mathrm{algebraMap}\ K\ L)` ✓（**`K` 无限 ＋ `\mathrm{algebraMap}` 单射 ⟹ 该边无限** ✓）
⟹ **「在 `K`-点上处处为零」即「恒零」** ✓✅ ⟹ **「在 `K`-点上可避零」对 L-系数多项式照常成立** ✓。
**⟹ 处置** ✓：**两个相乘的多项式改在 `MvPolynomial G L` 中取** ✓（**同环** ✓），**避零点仍限在 `K^G`** ✓
（**故 §4.9 的 `K`-坐标判据照用** ✓）⟹ **无须任何系数下降** ✓、**`(ii)` 的 `K`-系数形无须使用** ✓。
**⚠ 与既有读数的关系** ✓：**㊽** 的**发现**（两条 L-点路径确实走不通 ✓）**仍有效** ✓；其**结论**
（「必须下降到 `K`」✗）**被本条取代** ✓ —— 本条是**同一障碍的第三条路** ✓：
**多项式仍在 `L` 上，只把避零点限制在 `K`-点** ✓。 -/

section KPointDensity

variable (K : Type u) [Field K] [Infinite K] (L : Type u) [Field L] [Algebra K L]

/-- **`K`-点密度** ✓✅（**本轮核心工具** ✓）：**L-系数多项式若在 `K`-点上处处为零则恒零** ✓ ——
由 **`MvPolynomial.funext_set`** ✓（`[CommRing L] [IsDomain L]` ＋ 盒边 `s_i = \mathrm{Set.range}(\mathrm{algebraMap}\ K\ L)` ✓，
**各边无限** ✓ 由 `\mathrm{Set.infinite\_range\_of\_injective}` ✓ ＋ `K` 无限 ✓）。

**⚠ 为什么关键** ✓：它把「避零」的**取值域**与「多项式」的**系数域**解耦 ✓ ——
第 147 轮的两条失败路径 ✗ 都源于**把两者绑在一起** ✗（「同环」要求）。 -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_range {σ : Type*} {p : MvPolynomial σ L}
    (h : ∀ x : σ → L, (∀ i, x i ∈ Set.range (algebraMap K L))
      → MvPolynomial.eval x p = 0) : p = 0 := by
  refine MvPolynomial.funext_set (fun _ : σ => Set.range (algebraMap K L)) (fun _ => ?_) ?_
  · exact Set.infinite_range_of_injective (algebraMap K L).injective
  · intro x hx
    rw [h x (fun i => hx i (Set.mem_univ i)), map_zero]

/-- **`K`-点上的同时避零（L-系数版）** ✓✅：**两个非零的 L-系数多项式有公共的 `K`-非零点** ✓ ——
即 §4.10 的 `\mathrm{exists\_eval\_mul\_ne\_zero}` ✓ 的 **L-系数推广** ✓（**避零点仍限在 `K^G`** ✓）。

**证明** ✓：对**积**用 §4.15 的密度条 ✓（`L` 是域 ⟹ `\Phi \Psi \neq 0` ✓）＋ `map_mul` ✓
＋ `mul_ne_zero_iff` ✓（**与 §4.10 的基形同构** ✓，只把载体从 `K` 换成 `L` ✓）。 -/
theorem exists_eval_mul_ne_zero_of_range {σ : Type*} {Φ Ψ : MvPolynomial σ L}
    (hΦ : Φ ≠ 0) (hΨ : Ψ ≠ 0) :
    ∃ x : σ → L, (∀ i, x i ∈ Set.range (algebraMap K L))
      ∧ MvPolynomial.eval x Φ ≠ 0 ∧ MvPolynomial.eval x Ψ ≠ 0 := by
  have hne : Φ * Ψ ≠ 0 := mul_ne_zero hΦ hΨ
  obtain ⟨x, hx, hxne⟩ : ∃ x : σ → L, (∀ i, x i ∈ Set.range (algebraMap K L))
      ∧ MvPolynomial.eval x (Φ * Ψ) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (mvPolynomial_eq_zero_of_eval_eq_zero_on_range K L
      (fun x hx => by simp [h x hx]))
  rw [map_mul] at hxne
  exact ⟨x, hx, (mul_ne_zero_iff.mp hxne).1, (mul_ne_zero_iff.mp hxne).2⟩

end KPointDensity

section NewRouteEndToEnd

variable (K : Type u) [Field K] [Infinite K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **端到端（新路线，条件形）** ✓✅：**只差** `\mathrm{conjEvalPoly}\ K\ G\ b\ (\prod_\sigma \sigma \bullet t) \neq 0` ✓
（**§4.16 即证之** ✓）。

**证明** ✓（**与 §4.14 逐件对应** ✓，**只换避零条** ✓）：**(1)** `f \neq 0` ✓（§4.11 ✓）；
**(2)** `\mathrm{map}(\mathrm{algebraMap})\ f \neq 0` ✓（`\mathrm{map}` 单射 ✓）；
**(3)** **§4.15 的 L-系数避零** ✓ 给 `x : G \to L` ✓（**各分量在 `\mathrm{range}(\mathrm{algebraMap})`** ✓）
使 `\mathrm{eval}\ x` 在 `\mathrm{map}(\mathrm{algebraMap})\ f` 与 `\Phi` 上**皆非零** ✓；
**(4)** 由 `\mathrm{Set.mem\_range}` ✓ 取 `a : G \to K` ✓（`x = \mathrm{algebraMap} \circ a` ✓）；
**(5)** `\mathrm{eval_map}` ✓ ＋ `\mathrm{eval}_2\_comp` ✓ 把第一个非零降为 `\mathrm{eval}\ a\ f \neq 0` ✓
⟹ **§4.10 的对接锁** ✓ ＋ **§4.9／§4.8 的判据** ✓ 给 `\mathrm{LI}` ✓；
**(6)** `\mathrm{eval\_conjEvalPoly}` ✓（§4.13 ✓）＋ `\mathrm{noether\_aeval\_ne\_zero\_of\_prod\_ne\_zero}` ✓（§4.7 ✓）
把第二个非零降为 `\mathrm{aeval}\ (\sigma \mapsto \sigma \bullet z)\ t \neq 0` ✓。 -/
theorem exists_linearIndependent_smul_aeval_ne_zero_of_conjEvalPoly_ne_zero
    {L : Type u} [Field L] [Algebra K L] [MulSemiringAction G L] [SMulCommClass G K L]
    (b : Module.Basis G K L) (h : Function.Bijective (smulAlgEquivHom K G L))
    (t : MvPolynomial G K) (hΦ : conjEvalPoly K G b (∏ σ : G, σ • t) ≠ 0) :
    ∃ z : L, LinearIndependent K (fun σ : G => σ • z)
      ∧ MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0 := by
  have hf : normalBasisPoly K G b ≠ 0 := normalBasisPoly_ne_zero K G b h
  have hfL : MvPolynomial.map (algebraMap K L) (normalBasisPoly K G b) ≠ 0 := fun h0 =>
    hf (MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
      (by rw [h0, map_zero]))
  obtain ⟨x, hx, hx1, hx2⟩ := exists_eval_mul_ne_zero_of_range K L hfL hΦ
  have hx' : ∀ i : G, ∃ c : K, algebraMap K L c = x i := fun i => Set.mem_range.mp (hx i)
  choose a ha using hx'
  have hxeq : x = fun i : G => algebraMap K L (a i) := funext fun i => (ha i).symm
  have hfa : MvPolynomial.eval a (normalBasisPoly K G b) ≠ 0 := fun h0 =>
    hx1 (by
      rw [hxeq, MvPolynomial.eval_map]
      show MvPolynomial.eval₂ (algebraMap K L) ((algebraMap K L) ∘ a) (normalBasisPoly K G b) = 0
      rw [← MvPolynomial.eval₂_comp, h0, map_zero])
  have h2 : MvPolynomial.aeval (fun σ : G => σ • (∑ i : G, a i • b i))
      (∏ σ : G, σ • t) ≠ 0 := fun h0 =>
    hx2 (by rw [hxeq, eval_conjEvalPoly K G b (∏ σ : G, σ • t) a, h0])
  exact ⟨∑ i : G, a i • b i, by
      rw [← galoisMatrix_det_ne_zero_iff_vectors K G b, ← eval_normalBasisPoly K G b a]
      exact hfa,
    noether_aeval_ne_zero_of_prod_ne_zero K G (∑ i : G, a i • b i) t h2⟩

end NewRouteEndToEnd

/-! ## 4.16 **新路线（Ⅱ）：`(ii)` 的非零核心 ＝ 源的「代数无关」** ✓✅（第 148 轮）

**源逐字** ✓（`tex :660--662` ✓）：「**By the algebraic independence of the `\sigma`'s, `f'` is nonzero**」✓ ——
本轮把「代数无关」落为**一条定理** ✓：**线性代入 `x_\tau \mapsto \sum_i (\tau \bullet b_i) x_i` 是单射** ✓
（**工作形**：`\mathrm{conjEvalPoly}\ K\ G\ b\ t' \neq 0` ✓，其中 `t' = \prod_\sigma \sigma \bullet t` ✓）。

**⚠ 为什么这就是「代数无关」** ✓：源要的 `f'` 非零 ✓ 等价于**该代入在 `t'` 上不为零** ✓；
而代入由 `|G|` 个线性形式给出 ✓ ⟹ **分次论证下，单射 ⟺ 这些形式线性无关** ✓；
而它们线性无关**正由 Dedekind 定理供给** ✓（**σ 互异 ＋ 基** ✓）。 -/

section DedekindKernel

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G]

/-- **Dedekind ⟹ 核为零** ✓✅：`\sum_\tau l_\tau (\tau \bullet b_i) = 0\ (i \in G)` ⟹ `l = 0` ✓。

**证明** ✓：**(1)** 把**逐坐标**条件升为**逐向量**条件 ✓ —— 任何 `x \in L` 写成 `x = \sum_i (b.\mathrm{repr}\ x\ i) \bullet b_i` ✓，
再用 `\tau` 的 `K`-线性 ✓ 把和拆开 ✓ ⟹ `\sum_\tau l_\tau (\tau \bullet x) = 0\ \forall x` ✓；
**(2)** 即线性映射 `\sum_\tau l_\tau \bullet (\tau : L \to_K L) = 0` ✓（`\mathrm{LinearMap.ext}` ✓）；
**(3)** 由 **mathlib `linearIndependent_algHom_toLinearMap`** ✓（**Dedekind 定理** ✓；**第 147 轮未察** ✗）
＋ **识别桥的单射性** ✓（`\mathrm{AlgEquiv} \to \mathrm{AlgHom}` 单射 ✓ 复合 ✓）得这些 `\tau` **L-线性无关** ✓
⟹ `l = 0` ✓（`\mathrm{linearIndependent\_iff'}` ✓ 取 `s = \mathrm{univ}` ✓）。 -/
theorem smul_basis_linearCombination_eq_zero {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Injective (smulAlgEquivHom K G L)) {l : G → L}
    (hl : ∀ i : G, ∑ τ : G, l τ * (τ • b i) = 0) : l = 0 := by
  let v : G → (L →ₗ[K] L) := fun τ =>
    AlgHom.toLinearMap (((smulAlgEquivHom K G L τ : L ≃ₐ[K] L)) : L →ₐ[K] L)
  have hLI : LinearIndependent L v :=
    (linearIndependent_algHom_toLinearMap K L L).comp
      (fun τ : G => (((smulAlgEquivHom K G L τ : L ≃ₐ[K] L)) : L →ₐ[K] L))
      (AlgEquiv.coe_toAlgHom_injective.comp h)
  have hb : ∀ i : G, (∑ τ : G, l τ • v τ) (b i) = 0 := by
    intro i
    rw [LinearMap.sum_apply]
    simpa [v, smul_eq_mul, smulAlgEquivHom, smulAlgEquiv] using hl i
  have hzero : (∑ τ : G, l τ • v τ : L →ₗ[K] L) = 0 := by
    ext x
    rw [LinearMap.zero_apply, ← b.sum_repr x, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, hb i, smul_zero]
  funext i
  exact linearIndependent_iff'.mp hLI Finset.univ l (by simpa using hzero) i (Finset.mem_univ i)

end DedekindKernel

section ConjEvalPolyNeZeroProof

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **`(ii)` 的非零核心** ✓✅：**`t \neq 0` ⟹ `\mathrm{conjEvalPoly}\ K\ G\ b\ (\prod_\sigma \sigma \bullet t) \neq 0`** ✓ ——
即源「**By the algebraic independence of the `\sigma`'s, `f'` is nonzero**」✓ 的**形式化** ✓。

**⚠ 口径** ✓：本件**只要 `\mathrm{Injective}`** ✓（**不**要 `G \simeq \mathrm{Gal}(L/K)` 的满射性 ✓）
⟹ `(ii)` **不依赖识别桥** ✓（识别桥只为 §4.11 的 `f \neq 0` ✓ 即源「some normal basis exists」✓ 所需 ✓）。

**证明** ✓（**三件** ✓）：**(1)** `t' \neq 0` ✓ —— `t \neq 0` ＋ `MvPolynomial G K` 是域上多项式环 ✓
＋ `G` 经环自同构作用 ✓（**若 `\sigma \bullet t = 0` 则 `t = \sigma^{-1} \bullet (\sigma \bullet t) = 0`** ✓）
⟹ 各因子非零 ⟹ 积非零 ✓（`\mathrm{Finset.prod\_ne\_zero\_iff}` ✓）；
**(2)** **矩阵 `M_{\tau i} = \tau \bullet b_i` 的行 `L`-线性无关** ✓ —— 由 §4.16 的核为零条 ✓；
**(3)** 由 `\mathrm{IsUnit}\ M` ✓（`\mathrm{Matrix.linearIndependent\_rows\_iff\_isUnit}` ✓）取 `u = M` 的**单位** ✓，
以 `M^{-1}` 构造**逆代入** `\ell'` ✓，并证 **`\mathrm{aeval}\ \ell' \circ \mathrm{aeval}\ \ell = \mathrm{map}(\mathrm{algebraMap})`** ✓
（**对 `p` 作 `MvPolynomial.induction_on`** ✓；`\mathrm{mul\_X}` 支归约到
`\mathrm{aeval}\ \ell'\ (\ell\ \tau) = x_\tau` ✓，后者由 `M \cdot M^{-1} = 1` ✓ **逐项算出** ✓）
⟹ `\mathrm{aeval}\ \ell` **左可逆** ✓ ⟹ **单射** ✓ ⟹ `\mathrm{aeval}\ \ell\ t' \neq 0` ✓。

**⚠ 工艺读数** ✓：**㊹**（半可约 `def` 别挡在归纳路径上 ✓）：本件归纳的 motive 里**不出现 `\ell'`／`\ell` 的展开** ✓，
且 `\mathrm{aeval}\ \ell'\ (\ell\ \tau)` 的算式**先以 `\mathrm{calc}` 显式写出** ✓ ⟹ **无须 `show`** ✓。 -/
theorem conjEvalPoly_ne_zero {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Injective (smulAlgEquivHom K G L)) {t : MvPolynomial G K} (ht : t ≠ 0) :
    conjEvalPoly K G b (∏ σ : G, σ • t) ≠ 0 := by
  have ht' : (∏ σ : G, σ • t : MvPolynomial G K) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro σ _
    exact fun h0 => ht (by
      simpa [← mul_smul] using congrArg (fun q : MvPolynomial G K => σ⁻¹ • q) h0)
  have sum_extend : ∀ (s : Finset G) (g c : G → L), (∀ i ∉ s, g i = 0) →
      (∑ i ∈ s, g i * c i) = ∑ i : G, g i * c i := fun s g c hg =>
    Finset.sum_subset (Finset.subset_univ s) (fun x _ hx => by rw [hg x hx, zero_mul])
  set M : Matrix G G L := Matrix.of (fun τ i : G => τ • b i) with hM
  have hrows : LinearIndependent L M.row := by
    rw [linearIndependent_iff'']
    intro s g hg hsum i
    have hcoord : ∀ i' : G, ∑ x : G, g x * (x • b i') = 0 := by
      intro i'
      have h1 : (∑ x ∈ s, g x • M.row x) i' = 0 := by rw [hsum]; rfl
      have h2 : (∑ x ∈ s, g x • M.row x) i' = ∑ x ∈ s, g x * (x • b i') := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [hM, Matrix.row, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2, sum_extend s g (fun x => x • b i') hg] at h1
      exact h1
    exact congrFun (smul_basis_linearCombination_eq_zero K G b h hcoord) i
  have hunit : IsUnit M := (Matrix.linearIndependent_rows_iff_isUnit).mp hrows
  let ℓ : G → MvPolynomial G L := fun τ => ∑ i : G, MvPolynomial.C (τ • b i) * MvPolynomial.X i
  let ℓ' : G → MvPolynomial G L := fun i => ∑ υ : G,
    MvPolynomial.C ((↑(hunit.unit⁻¹) : Matrix G G L) i υ) * MvPolynomial.X υ
  have hX : ∀ τ : G, MvPolynomial.aeval ℓ' (ℓ τ) = MvPolynomial.X τ := by
    intro τ
    have hMu : M * (↑hunit.unit⁻¹ : Matrix G G L) = 1 := hunit.mul_val_inv
    have h1 : ∀ i : G, MvPolynomial.aeval ℓ'
        (MvPolynomial.C (τ • b i) * MvPolynomial.X i)
        = ∑ υ : G, MvPolynomial.C ((τ • b i) * (↑hunit.unit⁻¹ : Matrix G G L) i υ)
            * MvPolynomial.X υ := by
      intro i
      simp only [ℓ', map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun υ _ => ?_)
      rw [← mul_assoc, ← MvPolynomial.C_mul]
    calc MvPolynomial.aeval ℓ' (ℓ τ)
        = ∑ i : G, MvPolynomial.aeval ℓ' (MvPolynomial.C (τ • b i) * MvPolynomial.X i) := by
          simp only [ℓ, map_sum]
      _ = ∑ i : G, ∑ υ : G, MvPolynomial.C ((τ • b i) * (↑hunit.unit⁻¹ : Matrix G G L) i υ)
            * MvPolynomial.X υ := Finset.sum_congr rfl (fun i _ => h1 i)
      _ = ∑ υ : G, (∑ i : G, MvPolynomial.C ((τ • b i) * (↑hunit.unit⁻¹ : Matrix G G L) i υ))
            * MvPolynomial.X υ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun υ _ => (Finset.sum_mul Finset.univ _ _).symm)
      _ = ∑ υ : G, MvPolynomial.C (∑ i : G, (τ • b i) * (↑hunit.unit⁻¹ : Matrix G G L) i υ)
            * MvPolynomial.X υ := by
          refine Finset.sum_congr rfl (fun υ _ => ?_)
          rw [← map_sum]
      _ = ∑ υ : G, MvPolynomial.C ((M * (↑hunit.unit⁻¹ : Matrix G G L)) τ υ) * MvPolynomial.X υ := by
          refine Finset.sum_congr rfl (fun υ _ => ?_)
          rw [Matrix.mul_apply]
          exact congrArg (fun z => MvPolynomial.C z * MvPolynomial.X υ)
            (Finset.sum_congr rfl (fun j _ => rfl)).symm
      _ = ∑ υ : G, MvPolynomial.C ((1 : Matrix G G L) τ υ) * MvPolynomial.X υ := by rw [hMu]
      _ = MvPolynomial.X τ := by
          rw [Finset.sum_eq_single τ]
          · rw [Matrix.one_apply, if_pos rfl, MvPolynomial.C_1, one_mul]
          · intro υ _ hυ
            rw [Matrix.one_apply, if_neg (Ne.symm hυ), MvPolynomial.C_0, zero_mul]
          · intro hτ; exact absurd (Finset.mem_univ τ) hτ
  have hkey : ∀ p : MvPolynomial G K,
      MvPolynomial.aeval ℓ' (MvPolynomial.aeval ℓ p) = MvPolynomial.map (algebraMap K L) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        show MvPolynomial.aeval ℓ' (MvPolynomial.aeval ℓ (MvPolynomial.C a))
          = MvPolynomial.map (algebraMap K L) (MvPolynomial.C a)
        rw [MvPolynomial.aeval_C, MvPolynomial.map_C,
          IsScalarTower.algebraMap_apply K L (MvPolynomial G L),
          MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
        have h1 : MvPolynomial.aeval ℓ (p * MvPolynomial.X n)
            = MvPolynomial.aeval ℓ p * ℓ n := by
          rw [map_mul, MvPolynomial.aeval_X]
        rw [h1, map_mul, map_mul, hp, hX n, MvPolynomial.map_X]
  have hmain : MvPolynomial.aeval ℓ (∏ σ : G, σ • t) ≠ 0 := fun h0 =>
    ht' ((MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective) (by
      simp only [← hkey (∏ σ : G, σ • t), h0, map_zero]))
  show conjEvalPoly K G b (∏ σ : G, σ • t) ≠ 0
  exact hmain

end ConjEvalPolyNeZeroProof

/-! ## 4.17 **端到端（无条件形）** ✓✅（第 148 轮 —— **`(d)` 全落** ✓）

**⚠ 结论** ✓：`t \neq 0` ＋ **识别桥** ⟹ 源 `lemma-5.2` 证明要的结论 ✓
（**存在 `z` 使 `\{\sigma \bullet z\}` 线性无关 且 `t(z,\sigma(z),\dots) \neq 0`** ✓）。
**⚠ 全库关于 `(d)` 的具名残余至此清空** ✓✅ —— §4.14 的**条件形** ✓ 由 §4.15 ✓ ＋ §4.16 ✓ 供足前提 ✓；
`\mathrm{ConjEvalPolyKStatement}`（§4.14 的忠实具名残余 ✓）**保留作留痕** ✓，
但**已不在关键路径上** ✓（**第 148 轮口径修正** ✓，见 §4.15 ✓）。
**⚠ 余下的前提** ✓：**(1)** `t \neq 0` ✓（**源语境下 `t` 是非零多项式** ✓）；**(2)** **识别桥**
`G \to^* (L \simeq_K L)` **单射** ✓（**§4.11 的 `f \neq 0` 需其满射性** ✓，源语境下自动 ✓；**在册** ✓）。
**⚠ r199／r200 已清** ✓✅：该**两条数据前提**（识别桥 ✓ ＋ 基 `b` ✓）**均已由 §4.54 的 CHR 桥供给** ✓ ⟹
**无数据前提形**见 §4.55 ✓（`lemma52Statement_nonzero_of_isGaloisWithGroup` ✓）。 -/

section EndToEndUncond

variable (K : Type u) [Field K] [Infinite K] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **端到端：无条件形** ✓✅ —— `t \neq 0` ＋ 识别桥 ⟹ 结论 ✓（**不再需要任何具名残余** ✓）。 -/
theorem exists_linearIndependent_smul_aeval_ne_zero_of_ne_zero {L : Type u} [Field L]
    [Algebra K L] [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Bijective (smulAlgEquivHom K G L)) (t : MvPolynomial G K) (ht : t ≠ 0) :
    ∃ z : L, LinearIndependent K (fun σ : G => σ • z)
      ∧ MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0 :=
  exists_linearIndependent_smul_aeval_ne_zero_of_conjEvalPoly_ne_zero K G b h t
    (conjEvalPoly_ne_zero K G b h.injective ht)

end EndToEndUncond

/-! ## 4.18 **源 `lemma-5.2` 的口径收口：真形（补 `t \neq 0`）已证** ✓✅（第 149 轮）

**⚠ 出发点** ✓：§4.5 的 `Lemma52Statement` ✓ **未设 `t \neq 0`** ✗ ⟹ 其**假设类为空** ✗（**第 148 轮机检反驳** ✓：
`Lemma52Statement.false_at_zero` ✓）。**源的 `t` 本是非零多项式** ✓ ⟹ 正解 ＝ **补 `t \neq 0`** ✓
（**该前提不可省** ✗ —— 反驳即在库 ✓）。本轮把**修正形**（`Lemma52StatementNonzero` ✓）**证出** ✓✅ ⟹
**源 `lemma-5.2` 作为定理成立** ✓（**前提** ✓：`G` 有限 ✓／`K` 无限 ✓／识别桥 ✓／`SMulCommClass G K L` ✓；
**且张成侧不需额外前提** ✓）。

**⚠ 结构** ✓（**三件** ✓）：
**(1)** **基变换桥** ✓ `aeval_map_algebraMap` ✓ —— 「先换系数环、再代入」＝「直接代入」✓（源 `t` 的系数在 `F` ✓，
而 §4.16／§4.17 的机器在 `K` 上 ✓ ⟹ **须此桥** ✓）；
**(2)** **张成侧** ✓ `exists_basis_eq_smul_of_linearIndependent` ✓ —— `\mathrm{LI}` ＋ `\mathrm{card} = \mathrm{finrank}` ⟹
**共轭族恰成基** ✓（＝源「**generates a normal basis**」✓ 的**张成那一半** ✓；**§4.9 只给 `\mathrm{LI}`** ✓，
**在册** ✓ ⟹ **本轮收口** ✓）；
**(3)** **组装** ✓：§4.17 的无条件形 ✓ 给 `z` ✓ ⟹ (2) 把 `\{\sigma \bullet z\}` 升为**基** ✓ ⟹ (1) 把结论搬回 `F`-系数形 ✓。 -/

section BaseChangeAeval

variable {F : Type u} [Field F] {K : Type u} [Field K] {L : Type u} [Field L]
variable [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
variable {σ : Type*}

/-- **基变换桥** ✓✅：`\mathrm{aeval}` 在 `\mathrm{map}(\mathrm{algebraMap}\ F\ K)` 下**取值不变** ✓ ——
即「**先换系数环、后代入**」＝「**直接代入**」✓。

**证明** ✓：`MvPolynomial.aeval_def` ✓（`\mathrm{aeval} = \mathrm{eval}_2 (\mathrm{algebraMap}\ \cdot)` ✓）
＋ `MvPolynomial.eval₂_map` ✓（复合系数同态 ✓）＋ `IsScalarTower.algebraMap_eq` ✓
（`\mathrm{algebraMap}\ F\ L = (\mathrm{algebraMap}\ K\ L) \circ (\mathrm{algebraMap}\ F\ K)` ✓）。 -/
theorem aeval_map_algebraMap (g : σ → L) (t : MvPolynomial σ F) :
    MvPolynomial.aeval g (MvPolynomial.map (algebraMap F K) t) = MvPolynomial.aeval g t := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.aeval_def,
    IsScalarTower.algebraMap_eq F K L]

end BaseChangeAeval

section SpanningSide

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G]

/-- **张成侧** ✓✅：`\mathrm{LI}` ＋ `\mathrm{card}\ G = \mathrm{finrank}_K L` ⟹ **共轭族恰成 `K`-基** ✓ ——
即源「**generates a normal basis**」✓ 的**张成**那一半 ✓（**§4.9 的判据只给 `\mathrm{LI}`** ✓，**在册** ✓）。

**证明** ✓：mathlib **`basisOfLinearIndependentOfCardEqFinrank`** ✓ ＋ **`Module.finrank_eq_card_basis`** ✓ ——
**`\mathrm{card}` 等式由已有的基 `b` 供给** ✓ ⟹ **张成侧不需额外前提** ✓（**⚠ 这正是「判据给 `\mathrm{LI}`」在册项的处置** ✓）。 -/
theorem exists_basis_eq_smul_of_linearIndependent {L : Type u} [Field L] [Algebra K L]
    [MulSemiringAction G L] (b : Module.Basis G K L) {z : L}
    (hz : LinearIndependent K (fun σ : G => σ • z)) :
    ∃ b' : Module.Basis G K L, ∀ σ : G, b' σ = σ • z := by
  have : FiniteDimensional K L := finiteDimensional_of_basis K G b
  have : Nonempty G := ⟨1⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hz (Module.finrank_eq_card_basis b).symm, ?_⟩
  intro σ
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

end SpanningSide

section Lemma52TrueFormSec

variable (F : Type u) [Field F] (G : Type u) [Group G]

/-- **源 `lemma-5-2` 的真形** ✓✅（**修正形** ✓）：与 §4.5 的 `Lemma52Statement` ✓ **逐字同形** ✓，
**只多一个前提 `t \neq 0`** ✓ —— 该前提**不可省** ✗（**第 148 轮的机检反驳** ✓ 即证此事 ✓）。

**⚠ 为什么必须补** ✓：源 `lemma-5.2` 的 `t` **是非零多项式** ✓（源语境 ✓），而 §4.5 的登记形**漏了它** ✗
⟹ 在 `t = 0` 处结论不成立 ✗（**L1／L10①：具名残余亦须过非空性闸** ✓，**新读数 (52)** ✓）。 -/
def Lemma52StatementNonzero (K L : Type u) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] [MulSemiringAction G L] : Prop :=
  ∀ t : MvPolynomial G F, t ≠ 0 →
    ∃ (z : L) (b : Module.Basis G K L), (∀ σ : G, b σ = σ • z) ∧
      MvPolynomial.aeval (fun σ : G => σ • z) t ≠ 0

end Lemma52TrueFormSec

section Lemma52TrueFormProof

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **源 `lemma-5.2` 的真形已证** ✓✅ —— **本引理至此是定理** ✓（**不再是具名残余** ✓）。

**证明** ✓（**三件拼接** ✓）：**(1)** **基变换** ✓：`\mathrm{map}(\mathrm{algebraMap}\ F\ K)` **单射** ✓
（`\mathrm{algebraMap}` 单射 ✓ ＋ `map_injective` ✓）⟹ `t \neq 0` 传到 `K`-系数形 ✓；
**(2)** **§4.17 的无条件形** ✓ 给 `z` ✓（`\{\sigma \bullet z\}` **`\mathrm{LI}`** ✓ 且 `\mathrm{aeval}\ (\sigma \mapsto \sigma \bullet z)\ t_K \neq 0` ✓）；
**(3)** **§4.18 的两件** ✓：张成侧 ✓ 把 `\mathrm{LI}` **升为基** `b'` ✓（`b' \sigma = \sigma \bullet z` ✓）；
基变换桥 ✓ 把非零**搬回 `F`-系数形** ✓。

**⚠ 前提账** ✓（**皆在签名的假设里** ✓，**非隐藏** ✓）：`[Fintype G]` ✓（**源语境 ✓**）、`[DecidableEq G]` ✓（**矩阵逆所需 ✓**，
**工艺性 ✓**）、`[Infinite K]` ✓（源「**`K` is infinite**」✓）、**识别桥** ✓（**在册 ✓**）、
`[SMulCommClass G K L]` ✓（**作用与 `K`-标量交换 ✓** —— 源语境下 `G \le \mathrm{Aut}_K(L)` ✓ 自动成立 ✓，
**登记** ✓）。
**⚠ r200 已收口** ✓✅：两条数据前提（`b` ✓／识别桥 `h` ✓）由 §4.54 的 CHR 桥**现场供给** ✓ ⟹
**无数据前提形**见 §4.55 ✓（`lemma52Statement_nonzero_of_isGaloisWithGroup` ✓ ＋ 源文口径形 ✓ ＋ 逐字「unit」形 ✓）；
**本条留痕** ✓（**不复写** ✗）。 -/
theorem lemma52Statement_nonzero_true (K L : Type u) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] [Infinite K]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Bijective (smulAlgEquivHom K G L)) :
    Lemma52StatementNonzero F G K L := by
  intro t ht
  have htK : MvPolynomial.map (algebraMap F K) t ≠ 0 := fun h0 =>
    ht (MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
      (by rw [h0, map_zero]))
  obtain ⟨z, hz, hzne⟩ :=
    exists_linearIndependent_smul_aeval_ne_zero_of_ne_zero K G b h
      (MvPolynomial.map (algebraMap F K) t) htK
  obtain ⟨b', hb'⟩ := exists_basis_eq_smul_of_linearIndependent K G b hz
  exact ⟨z, b', hb', by simpa only [aeval_map_algebraMap] using hzne⟩

end Lemma52TrueFormProof

/-! ## 4.19 **源 `theorem-5-1` 证明的**首句**：从 `IsRationalOver` 提取超越基** ✓✅（第 151 轮）

**源逐字** ✓（`raw/Saltman1982.tex:649` ✓）：「Suppose \(a_1,\dots,a_n \in L^G\) are a **transcendence base**
for \(L^G\) over \(F\). Set \(R_1 = F[a_1,\dots,a_n] \subset L^G\).」✓ —— 即**该定理证明的第一步**就是
**从「`L^G` 在 `F` 上有理」（＝ Noether 假设 ✓）取出一个超越基** ✓，然后才能：
**(i)** 造 `R_1 = F[a_1,\dots,a_n]` ✓（由 §4.2 的 `IsRationalOver` ✓ 之同构**搬到具体元素** ✓）；
**(ii)** 用 **§4.18 的 `prop-0-2(c)`** ✓ 下降 ✓；**(iii)** 写 `a_i = f_i/g_i` ✓（需 `L^G = \mathrm{Frac}(R_1)` ✓）。
**⚠ 登记（§101.2 供给表 ③）** ✓：该项长期在册为「**缺** ✗（**纯工程缺口** ✓）」⟹ **本轮落** ✓。

**⚠ 载体选择** ✓（**登记** ✓）：本件用 **mathlib `IsRationalOver`** ✓（＝「与某有理函数域同构」✓）为**起点** ✓，
把超越基落为 **`AlgebraicIndependent` ＋ `IntermediateField.adjoin = ⊤`** ✓ —— 即「**域生成的**」形 ✓
（**⚠ 与 mathlib `IsTranscendenceBasis`** ✓ 的差别 ✓：后者的第二合取写在 **`Algebra.adjoin`** ✓（**子代数**形 ✓）上 ✓；
**两者在域档下等价** ✓ —— **本件取域生成形** ✓ 因源的用途（造 `R_1` ＋ `L^G = \mathrm{Frac}(R_1)` ✓）**正需域生成** ✓；
**⚠ 桥接未落** ✗（**登记** ✓））。
**⚠ 迁移工艺** ✓（**新读数 (59)** ✓）：**基例在分式域上直接可证** ✓（`IsFractionRing.div_surjective` ✓ 给出
`z = a/b` ✓ ＋ **`MvPolynomial.adjoin_range_X`** ✓ ＋ **`IntermediateField.algebra_adjoin_le_adjoin`** ✓
＋ **`IntermediateField.div_mem`** ✓）；**一般档由 `IntermediateField.adjoin_map`** ✓（**映射与 adjoin 交换** ✓）
**把基例搬到 `K`** ✓ —— **避开**了「`Algebra.IsAlgebraic` 沿 `\mathrm{AlgEquiv}` 迁移」✗ 的**实例泥潭** ✗。 -/

section FractionRingBase

variable (F : Type u) [Field F] (n : ℕ)

/-- **基例** ✓✅：**有理函数域由其变元（作为域）生成** ✓ ——
`\mathrm{IntermediateField.adjoin}\ F\ \{\mathrm{algebraMap}(x_i)\} = \top` ✓（`x_i = X_i` ✓）。

**证明** ✓：`\top \le \mathrm{adjoin}` ✓ —— 任取 `z : \mathrm{FractionRing}\,R` ✓，由
`\mathrm{IsFractionRing.div\_surjective}` ✓ 写 `z = \mathrm{algebraMap}\ a / \mathrm{algebraMap}\ b` ✓；
`\mathrm{algebraMap}\ a \in \mathrm{adjoin}` ✓（因 `a \in \mathrm{Algebra.adjoin}\ F\ \{\text{变元}\}` ✓
＝ **`\top`** ✓ 由 **`MvPolynomial.adjoin_range_X`** ✓，再经 **`IntermediateField.algebra_adjoin_le_adjoin`** ✓ 升到域 adjoin ✓）；
最后由 **`IntermediateField.div_mem`** ✓ 收 ✓。 -/
theorem adjoin_algebraMap_X_fractionRing :
    IntermediateField.adjoin F (Set.range (fun i : Fin n =>
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
        (MvPolynomial.X i))) = ⊤ := by
  have key : ∀ x : MvPolynomial (Fin n) F,
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) x ∈
        IntermediateField.adjoin F (Set.range (fun i : Fin n =>
          algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
            (MvPolynomial.X i))) := by
    intro x
    refine IntermediateField.algebra_adjoin_le_adjoin F (Set.range (fun i : Fin n =>
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
        (MvPolynomial.X i))) ?_
    have hmap : Algebra.adjoin F (Set.range (fun i : Fin n =>
          algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
            (MvPolynomial.X i)))
        = (Algebra.adjoin F (Set.range (MvPolynomial.X :
            Fin n → MvPolynomial (Fin n) F))).map
          (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
            (FractionRing (MvPolynomial (Fin n) F))) := by
      rw [AlgHom.map_adjoin]
      congr 1
      exact Set.range_comp _ _
    rw [hmap]
    exact Subalgebra.mem_map.mpr ⟨x, by rw [MvPolynomial.adjoin_range_X]; trivial, rfl⟩
  refine le_antisymm le_top ?_
  intro z _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin n) F) z
  exact IntermediateField.div_mem _ (key a) (key b)

end FractionRingBase

section TranscendenceExtraction

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]

/-- **独立半** ✓✅：**`IsRationalOver` ⟹ 存在代数无关族** ✓ —— 即超越基的**独立那一半** ✓。

**证明** ✓：`\mathrm{IsRationalOver}` ✓ 给 `K \simeq_F \mathrm{Frac}(F[x_1,\dots,x_n])` ✓；
**变元代数无关** ✓（`MvPolynomial.algebraicIndependent_X` ✓）⟹ 经**两次 `AlgebraicIndependent.map'`** ✓
（**`\mathrm{algebraMap}` 单射** ✓ 由 `IsFractionRing.injective` ✓；**同构的单射性** ✓）搬到 `K` ✓。 -/
theorem exists_algebraicIndependent_of_isRationalOver (h : IsRationalOver F K) :
    ∃ (n : ℕ) (a : Fin n → K), AlgebraicIndependent F a := by
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, (e.symm : FractionRing (MvPolynomial (Fin n) F) →ₐ[F] K) ∘
    (fun i => algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
      (MvPolynomial.X i)), ?_⟩
  have h1 : AlgebraicIndependent F (fun i : Fin n =>
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
        (MvPolynomial.X i)) :=
    (MvPolynomial.algebraicIndependent_X (Fin n) F).map'
      (f := IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
        (FractionRing (MvPolynomial (Fin n) F)))
      (IsFractionRing.injective (MvPolynomial (Fin n) F)
        (FractionRing (MvPolynomial (Fin n) F)))
  exact h1.map' (f := (e.symm : FractionRing (MvPolynomial (Fin n) F) →ₐ[F] K))
    e.symm.injective

/-- **源 `theorem-5-1` 证明首句的**完整抽取** ✓✅**：**`IsRationalOver F K` ⟹ 存在超越基**
（**域生成形** ✓：**代数无关** ✓ ＋ **域 adjoin 为 `\top`** ✓）。

**⚠ 意义** ✓（**源下一步的接口** ✓）：由此 `a` 可造源的 `R_1 = F[a_1,\dots,a_n] \subset K` ✓
（`F`-子代数 ✓），并用 **§4.18 的 `prop-0-2(c)`** ✓ 下降 ✓ —— 即 **`theorem-5-1` 装配的**前置件**✓。
**证明** ✓：**独立半** ✓（同上 ✓）＋ **生成半** ✓：`Set.range_comp` ✓ 把 `\mathrm{range}(e^{-1} \circ y)` 写成
`e^{-1}'' \mathrm{range}(y)` ✓，再用 **`IntermediateField.adjoin_map`** ✓ **把 §4.19 的基例沿 `e^{-1}` 搬走** ✓
（`\mathrm{adjoin} = \top \mapsto \mathrm{map}\ e^{-1}\ \top = \top` ✓，**后一等号由 `e^{-1}` 的满射性** ✓）。
**⚠ 为何此路避坑** ✓：**域 adjoin 形**只需 `\mathrm{adjoin}` 的**映射律** ✓（`adjoin_map` ✓），
**不需要** `\mathrm{Algebra.IsAlgebraic}` 沿同构的迁移 ✗（后者要造 `\mathrm{Algebra}\ A_0\ K` 实例 ✓，
**实测为泥潭** ✗ —— **新读数 (59)** ✓）。 -/
theorem exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver (h : IsRationalOver F K) :
    ∃ (n : ℕ) (a : Fin n → K), AlgebraicIndependent F a ∧
      IntermediateField.adjoin F (Set.range a) = ⊤ := by
  obtain ⟨n, ⟨e⟩⟩ := h
  set R := MvPolynomial (Fin n) F with hR
  set Fr := FractionRing R with hFr
  set y : Fin n → Fr := fun i => algebraMap R Fr (MvPolynomial.X i) with hy
  refine ⟨n, (e.symm : Fr →ₐ[F] K) ∘ y, ?_, ?_⟩
  · exact ((MvPolynomial.algebraicIndependent_X (Fin n) F).map'
      (f := IsScalarTower.toAlgHom F R Fr) (IsFractionRing.injective R Fr)).map'
      (f := (e.symm : Fr →ₐ[F] K)) e.symm.injective
  · have hbase : IntermediateField.adjoin F (Set.range y) = ⊤ :=
      adjoin_algebraMap_X_fractionRing F n
    have htop : IntermediateField.map (e.symm : Fr →ₐ[F] K) ⊤ = ⊤ := by
      refine le_antisymm le_top ?_
      intro x _
      exact ⟨e x, trivial, by simp⟩
    rw [Set.range_comp, ← IntermediateField.adjoin_map F (Set.range y) (e.symm : Fr →ₐ[F] K),
      hbase, htop]

end TranscendenceExtraction

/-! ## 4.20 **域生成 ⟹ 分式形（源「Write `a_i = f_i/g_i`」的接口）** ✓✅（第 152 轮）

**源逐字** ✓（`raw/Saltman1982.tex:650` ✓）：「Write \(a_i = f_i/g_i\), where the \(f\)'s and \(g\)'s are
**polynomials** in the \(x_\sigma\)'s.」✓ —— 即**源的下一步**要把 `L^G` 的元素写成**生成子代数的分式** ✓，
**再清分母**（「Then if \(t\) is the **product of all the \(g\)'s and \(k\)'s**, we have that
\(S \subset F[x_\sigma](1/t)\).」✓）⟹ 本件落**该两步所需的两个形** ✓。

**⚠ 定理内容** ✓：**若 `a` 把 `K` 作为 `F`-域生成** ✓（`\mathrm{IntermediateField.adjoin}\ F\ \{\mathrm{range}\ a\} = \top` ✓，
**正是 §4.19 抽取的生成半** ✓），**则 `K` 的每个元素都是生成子代数** `A_0 = \mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\}` ✓
**两元素之商** ✓（**域论标准** ✓：`A_0` 是 `K` 的子环 ✓，而「由 `A_0` 生成的域」＝ `\mathrm{Frac}(A_0)` ✓）。

**⚠ 证明工艺** ✓（**新读数 (60)** ✓）：**用 `IntermediateField.adjoin_induction`** ✓（**域 adjoin 的结构归纳原理** ✓）
把命题**降到五个情形** ✓ —— 生成元 ✓／基域 ✓／加法 ✓／**逆** ✓／乘法 ✓；**每个情形都是分数运算** ✓
（`div_add_div` ✓／`div_mul_div_comm` ✓／`inv_div` ✓，**分母非零由「子代数元素 ≠ 0 ⟹ 其在 `K` 中像 ≠ 0」** ✓ 供给 ✓）。
**⚠ 两处编译期自纠** ✓（**留痕** ✓）：**①** **系数与子代数元素之间须走 `\mathrm{algebraMap}`** ✓ ——
`\mathrm{field\_simp}` **不会**从 `q \neq 0` ✗ 自行推出 `\mathrm{algebraMap}\ q \neq 0` ✓ ⟹ **须显式放入上下文** ✓；
**②** **`rw` 的次序** ✓ —— **先** `\leftarrow h`（把 `z` 换成分式 ✓）**再** `\mathrm{simp\ only}\ [\mathrm{map\_add}, \mathrm{map\_mul}]` ✓，
**反序则 `\mathrm{map\_*}` 先把分式结构打散** ✗ 使 `\leftarrow h` **匹配不上** ✗。

**⚠ 登记（桥接未落）** ✗：**mathlib `IsTranscendenceBasis`** ✓ 的**第二合取含 `\mathrm{Algebra.IsAlgebraic}`** ✓
（**子代数 adjoin 形** ✓），本轮**试图**由本件的分式形**推之** ✓（**思路** ✓：`y z = x` ⟹ `z` 是 `y T - x` 的根 ✓）
**未过** ✗ —— **实测阻塞** ✓：`\mathrm{isTranscendenceBasis\_iff\_algebraicIndependent\_isAlgebraic}` ✓ 的
**实例推断卡住** ✗（报 `\mathrm{Nontrivial}\ ?m` ✓，**四种子写法均复现** ✓：具名隐参 ✓／全 `@` 显参 ✓／
`\mathrm{have}` 类型标注 ✓）⟹ **桥接延后** ✗，**改由直取定义（极大性形）** ✓ 的路线**待审** ✓。
**⚠ 用途** ✓：本两件是 **§4.19 的抽取** ✓ 与 **§4.18 的 `prop-0-2(c)`** ✓ 之间的**接口** ✓
（源的「`R''` 有限生成于 `R_1` ⟹ `\exists s` 使 `R'' \subseteq R_1(1/s)`」✓ 一步的**输入** ✓）。 -/

section FractionForm

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {ι : Type*}

/-- **域生成 ⟹ 分式形** ✓✅：**每个元素都是生成子代数两元素之商** ✓（**分母非零** ✓）。

**证明** ✓：对 `\mathrm{IntermediateField.adjoin}` 作**结构归纳** ✓（五情形 ✓），
每情形由**分数律** ✓ 收口（`div_add_div` ✓／`div_mul_div_comm` ✓／`inv_div` ✓；
**零元的逆支** ✓：`x = 0 \Rightarrow x^{-1} = 0 = 0/1` ✓）。 -/
theorem exists_div_eq_of_adjoin_eq_top {a : ι → K}
    (h : IntermediateField.adjoin F (Set.range a) = ⊤) (z : K) :
    ∃ x y : Algebra.adjoin F (Set.range a), y ≠ 0 ∧
      algebraMap (Algebra.adjoin F (Set.range a)) K x
        / algebraMap (Algebra.adjoin F (Set.range a)) K y = z := by
  have key : ∀ z ∈ IntermediateField.adjoin F (Set.range a),
      ∃ x y : Algebra.adjoin F (Set.range a), y ≠ 0 ∧
        algebraMap (Algebra.adjoin F (Set.range a)) K x
          / algebraMap (Algebra.adjoin F (Set.range a)) K y = z := by
    intro z hz
    refine IntermediateField.adjoin_induction F (s := Set.range a)
      (p := fun z _ => ∃ x y : Algebra.adjoin F (Set.range a), y ≠ 0 ∧
        algebraMap (Algebra.adjoin F (Set.range a)) K x
          / algebraMap (Algebra.adjoin F (Set.range a)) K y = z) ?_ ?_ ?_ ?_ ?_ hz
    · rintro z ⟨i, rfl⟩
      exact ⟨⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩, 1, one_ne_zero, by simp⟩
    · intro c
      exact ⟨⟨algebraMap F (Algebra.adjoin F (Set.range a)) c,
        Subalgebra.algebraMap_mem _ c⟩, 1, one_ne_zero, by simp⟩
    · rintro x y hx hy ⟨px, qx, hqx, hx'⟩ ⟨py, qy, hqy, hy'⟩
      refine ⟨px * qy + py * qx, qx * qy, mul_ne_zero hqx hqy, ?_⟩
      rw [← hx', ← hy']
      simp only [map_add, map_mul]
      have hqx' : algebraMap (Algebra.adjoin F (Set.range a)) K qx ≠ 0 :=
        fun h => hqx (Subtype.ext h)
      have hqy' : algebraMap (Algebra.adjoin F (Set.range a)) K qy ≠ 0 :=
        fun h => hqy (Subtype.ext h)
      field_simp
    · rintro x hx ⟨px, qx, hqx, hx'⟩
      by_cases hpx : px = 0
      · refine ⟨0, 1, one_ne_zero, ?_⟩
        have hx0 : x = 0 := by rw [← hx', hpx, map_zero, zero_div]
        rw [hx0, inv_zero, map_zero, zero_div]
      · refine ⟨qx, px, hpx, ?_⟩
        rw [← hx', inv_div]
    · rintro x y hx hy ⟨px, qx, hqx, hx'⟩ ⟨py, qy, hqy, hy'⟩
      refine ⟨px * py, qx * qy, mul_ne_zero hqx hqy, ?_⟩
      rw [← hx', ← hy']
      simp only [map_mul]
      rw [div_mul_div_comm]
  exact key z (by rw [h]; trivial)

/-- **乘法形（清分母步所需）** ✓✅：`y z = x`，`y \neq 0` ✓ —— 与上一条**等价** ✓，
但形**便于「清分母」** ✓（源「product of all the `g`'s and `k`'s」✓ 的直接用点 ✓）。 -/
theorem exists_mul_eq_of_adjoin_eq_top {a : ι → K}
    (h : IntermediateField.adjoin F (Set.range a) = ⊤) (z : K) :
    ∃ x y : Algebra.adjoin F (Set.range a), y ≠ 0 ∧
      algebraMap (Algebra.adjoin F (Set.range a)) K y * z
        = algebraMap (Algebra.adjoin F (Set.range a)) K x := by
  obtain ⟨x, y, hy, hxy⟩ := exists_div_eq_of_adjoin_eq_top h z
  refine ⟨x, y, hy, ?_⟩
  rw [← hxy]
  have hy' : algebraMap (Algebra.adjoin F (Set.range a)) K y ≠ 0 :=
    fun hh => hy (Subtype.ext hh)
  field_simp

end FractionForm

/-! ## 4.21 **有限清分母**（源「product of all the `g`'s and `k`'s」）✓✅（第 153 轮）

**源逐字** ✓（`raw/Saltman1982.tex:651--652` ✓）：「Then if \(t\) is the **product of all the \(g\)'s and
\(k\)'s**, we have that \(S \subset F[x_\sigma \mid \sigma \in G](1/t)\).」✓ —— 即源把**有限多个**分母
（`a_i = f_i/g_i` ✓ 的 `g`'s ✓ 与 `e_j = h_j/k_j` ✓ 的 `k`'s ✓）**乘成一个** `t` ✓，**一次去分母** ✓。

**⚠ 定理内容** ✓：一族元素若**各自**是 `A` 中两元素之商 ✓（**正是 §4.20 的输出形** ✓），则**存在单个 `s \neq 0`** ✓
使**全体同时**「去分母」✓（`\mathrm{algebraMap}\ s \cdot g_i` 仍是 `\mathrm{algebraMap}` 的像 ✓）——
**⚠ 关键** ✓：**只需 `n = 1`** ✓（`s` 取**各分母之积** ✓ 时，`g_i` 的分母已是 `s` 的因子 ✓）。
**⚠ 用途** ✓：源 `R'' \subseteq R_1(1/s)` ✓ 与 `S \subseteq F[x_\sigma](1/t)` ✓ 两处的**共同内核** ✓。
**⚠ 前提** ✓：`[Nontrivial A] [NoZeroDivisors A]` ✓（**积非零所需** ✓ —— 在域的子代数档**自动成立** ✓，见下一条 ✓）。 -/

section ClearDenominators

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **有限清分母** ✓✅：`\exists s \neq 0,\ \forall i,\ \exists a,\ \mathrm{algebraMap}\ s \cdot g_i = \mathrm{algebraMap}\ a` ✓。

**证明** ✓：对每个 `i` 取一对 `(x_i, y_i)` ✓（`\mathrm{choose}` ✓）；取 `s := \prod_i y_i` ✓（**积非零** ✓ 由
`\mathrm{Finset.prod\_ne\_zero\_iff}` ✓）；由 **`\mathrm{Finset.mul\_prod\_erase}`** ✓ 把 `s` 拆成
`y_i \cdot \prod_{j \neq i} y_j` ✓，再用 `y_i g_i = x_i` ✓ **一次代换** ✓ ⟹ `a := (\prod_{j \neq i} y_j) \cdot x_i` ✓。
**⚠ 一处编译期自纠** ✓：`\mathrm{Finset.mul\_prod\_erase}` 的**方向**与目标**相反** ✓ ⟹ 须取 `.symm` ✓；
且 `\mathrm{map\_prod}` **须在两处都展开** ✓（否则 `s` 的像与逐项之积**不是同一项** ✗，`\mathrm{ring}` 收不了 ✗）。 -/
theorem exists_mul_eq_of_finite (g : ι → K)
    (h : ∀ i, ∃ x y : A, y ≠ 0 ∧ algebraMap A K y * g i = algebraMap A K x) :
    ∃ s : A, s ≠ 0 ∧ ∀ i, ∃ a : A, algebraMap A K s * g i = algebraMap A K a := by
  choose X Y hY hXY using h
  refine ⟨∏ i, Y i, Finset.prod_ne_zero_iff.mpr (fun i _ => hY i), fun i => ?_⟩
  refine ⟨(∏ j ∈ Finset.univ.erase i, Y j) * X i, ?_⟩
  have h1 : algebraMap A K (∏ j, Y j)
      = algebraMap A K (Y i) * ∏ j ∈ Finset.univ.erase i, algebraMap A K (Y j) := by
    rw [map_prod]
    exact (Finset.mul_prod_erase Finset.univ (fun x => algebraMap A K (Y x))
      (Finset.mem_univ i)).symm
  rw [h1, map_mul, map_prod, ← hXY i]
  ring

end ClearDenominators

section GeneratedFieldCase

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {ι : Type*}

/-- **域生成档的有限清分母** ✓✅（**源 step 的直接形** ✓）：把上一条用在 `A := \mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\}` ✓
（**其 `\mathrm{NoZeroDivisors}` 自动成立** ✓ —— **域的子代数** ✓）＋ **§4.20 的乘法形** ✓（每个 `g_i` 由生成域性质给出分式 ✓）。

**⚠ 用途** ✓：取 `g` ＝ 源的两族生成元 ✓（`a_i` ✓ 与 `e_j` ✓）⟹ 得**单个** `s` ✓ ⟹ `R'' \subseteq R_1(1/s)` ✓。 -/
theorem exists_mul_eq_of_finite_adjoin_eq_top {a : ι → K}
    (h : IntermediateField.adjoin F (Set.range a) = ⊤)
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (g : ι' → K) :
    ∃ s : Algebra.adjoin F (Set.range a), s ≠ 0 ∧
      ∀ i : ι', ∃ x : Algebra.adjoin F (Set.range a),
        algebraMap (Algebra.adjoin F (Set.range a)) K s * g i
          = algebraMap (Algebra.adjoin F (Set.range a)) K x := by
  have : NoZeroDivisors ↥(Algebra.adjoin F (Set.range a)) := inferInstance
  exact exists_mul_eq_of_finite (A := ↥(Algebra.adjoin F (Set.range a))) g
    (fun i => exists_mul_eq_of_adjoin_eq_top h (g i))

end GeneratedFieldCase

/-! ## 4.22 **子代数版清分母**（源「`S \subset F[x_\sigma](1/t)`」之形）✓✅（第 154 轮）

**源逐字** ✓（`raw/Saltman1982.tex:651--652` ✓）：「(\(t\) ＝ the product of all the \(g\)'s and \(k\)'s)
we have that \(S \subset F[x_\sigma \mid \sigma \in G](1/t)\).」✓ —— 与 §4.21 的**有限族**形相比 ✓，
**本件给的是「整个子代数落进单个局部化」** ✓ 的形 ✓（源两处用法 ✓：`R'' \subseteq R_1(1/s)` ✓ 与 `S \subseteq F[x](1/t)` ✓）。

**⚠ 定理内容** ✓：`B` 是 `A` 上**有限型**代数 ✓、`\varphi : B \to_A K` ✓ 且 `K` 的每个元素是 `A` 中两元素之商 ✓
（**正是 §4.20 的输出形** ✓），则**存在单个 `s \neq 0`** ✓ 使 `B` 的像**全体落进 `s` 的局部化** ✓：
`\forall x : B,\ \exists n\ a,\ \mathrm{algebraMap}\ s^n \cdot \varphi x = \mathrm{algebraMap}\ a` ✓
（**谓词形** ✓：「清分母后仍是 `A` 中元素的像」✓）。
**⚠ 证明** ✓：取 `B` 的**有限生成集** `T` ✓（**`Algebra.FiniteType.out : \top.\mathrm{FG}`** ✓ ，
`\mathrm{Subalgebra.FG}\ S := \exists t : \mathrm{Finset}\ A,\ \mathrm{Algebra.adjoin}\ R\ \uparrow t = S` ✓）；
对 `\mathrm{Algebra.adjoin}\ A\ \uparrow T` 作**结构归纳** ✓（**四支** ✓：生成元 ✓／基域 ✓／加法 ✓／乘法 ✓）——
**⚠ 幂次记账** ✓：**生成元支** `n = 1` ✓（同 §4.21 ✓）／**基域支** `n = 0` ✓／**加乘两支** `n + m` ✓
（由 `\mathrm{pow\_add}` ✓ ＋ **逆写** `\leftarrow \mathrm{map\_pow}` ✓／`\leftarrow \mathrm{map\_mul}` ✓／`\leftarrow \mathrm{map\_add}` ✓ 收口 ✓）。

**⚠ 三处编译期自纠** ✓（**留痕** ✓）：
**①** **`\mathrm{Subalgebra.FG}` 只有一层** ✗ —— 初版按「`\exists t,\ \uparrow t \subseteq S \wedge \mathrm{adjoin} = S`」✗ 解构 ✓，
报 **dependent elimination failed** ✗（**实测** ✓）⟹ **正解** ＝ `\mathrm{obtain}\ \langle T, hT \rangle` ✓（**定义只有一层** ✓）；
**②** **`\mathrm{DecidableEq}\ B` 不可得** ✗（`\mathrm{Finset.erase}` 需要 ✓）⟹ **正解 ＝ 证内 `\mathrm{classical}`** ✓
（**不**加强陈述 ✓）；
**③** **幂次记账的 `rw` 链方向** ✓：**RHS 的 `\mathrm{algebraMap}\ (\cdot + \cdot)` 须先**拆开** ✓
（`\leftarrow \mathrm{map\_add}` ✓）**才能与 `hx'`／`hy'` 相接** ✗ ⟹ **改用 `\mathrm{calc}` 式 `hL`** ✓
（**显式给出中间形** ✓）＋ **末步 `\mathrm{simp\ only}\ [\leftarrow \mathrm{map\_pow}, \leftarrow \mathrm{map\_mul}, \leftarrow \mathrm{map\_add}]`** ✓。 -/

section SubalgebraClearDenominators

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

/-- **子代数版清分母** ✓✅：**有限型代数到分式域的映射，其像落在单个 `s` 的局部化内** ✓（**带幂次** ✓）。

**⚠ 用途** ✓：源 `R'' \subseteq R_1(1/s)` ✓ 与 `S \subseteq F[x_\sigma](1/t)` ✓ **正是此形** ✓
（**§4.21 的有限族形是其特例** ✓）。 -/
theorem exists_pow_mul_eq_of_finiteType (φ : B →ₐ[A] K)
    (hfrac : ∀ z : K, ∃ x y : A, y ≠ 0 ∧ algebraMap A K y * z = algebraMap A K x) :
    ∃ s : A, s ≠ 0 ∧ ∀ x : B, ∃ (n : ℕ) (a : A),
      algebraMap A K s ^ n * φ x = algebraMap A K a := by
  classical
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := A) (A := B)
  choose X Y hY hXY using fun t : B => hfrac (φ t)
  refine ⟨∏ t ∈ T, Y t, Finset.prod_ne_zero_iff.mpr (fun t _ => hY t), fun x => ?_⟩
  have key : ∀ x ∈ Algebra.adjoin A (↑T : Set B), ∃ (n : ℕ) (a : A),
      algebraMap A K (∏ t ∈ T, Y t) ^ n * φ x = algebraMap A K a := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => ∃ (n : ℕ) (a : A),
      algebraMap A K (∏ t ∈ T, Y t) ^ n * φ x = algebraMap A K a) ?_ ?_ ?_ ?_ hx
    · intro t ht
      refine ⟨1, (∏ u ∈ T.erase t, Y u) * X t, ?_⟩
      have h1 : algebraMap A K (∏ u ∈ T, Y u)
          = algebraMap A K (Y t) * ∏ u ∈ T.erase t, algebraMap A K (Y u) := by
        rw [map_prod]
        exact (Finset.mul_prod_erase T (fun x => algebraMap A K (Y x)) ht).symm
      rw [pow_one, h1, map_mul, map_prod, ← hXY t]
      ring
    · intro r
      exact ⟨0, r, by rw [pow_zero, one_mul, φ.commutes]⟩
    · intro x y hx hy ihx ihy
      obtain ⟨n, ax, hx'⟩ := ihx
      obtain ⟨m, ay, hy'⟩ := ihy
      refine ⟨n + m, (∏ t ∈ T, Y t) ^ m * ax + (∏ t ∈ T, Y t) ^ n * ay, ?_⟩
      have hL : algebraMap A K (∏ t ∈ T, Y t) ^ (n + m) * φ (x + y)
          = algebraMap A K (∏ t ∈ T, Y t) ^ m
              * (algebraMap A K (∏ t ∈ T, Y t) ^ n * φ x)
            + algebraMap A K (∏ t ∈ T, Y t) ^ n
              * (algebraMap A K (∏ t ∈ T, Y t) ^ m * φ y) := by
        rw [pow_add, map_add]
        ring
      rw [hL, hx', hy']
      simp only [← map_pow, ← map_mul, ← map_add]
    · intro x y hx hy ihx ihy
      obtain ⟨n, ax, hx'⟩ := ihx
      obtain ⟨m, ay, hy'⟩ := ihy
      refine ⟨n + m, ax * ay, ?_⟩
      have hL : algebraMap A K (∏ t ∈ T, Y t) ^ (n + m) * φ (x * y)
          = (algebraMap A K (∏ t ∈ T, Y t) ^ n * φ x)
            * (algebraMap A K (∏ t ∈ T, Y t) ^ m * φ y) := by
        rw [pow_add, map_mul]
        ring
      rw [hL, hx', hy']
      simp only [← map_mul]
  exact key x (by rw [hT]; trivial)

end SubalgebraClearDenominators

section GeneratedFieldCaseSub

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {ι : Type*}

/-- **域生成档的子代数版清分母** ✓✅（**源 step 的直接形** ✓）：`hfrac` 由 **§4.20** ✓ 供给
（`A := \mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\}` ✓，**其 `\mathrm{NoZeroDivisors}` 自动成立** ✓）。 -/
theorem exists_pow_mul_eq_of_finiteType_adjoin_eq_top {a : ι → K}
    (h : IntermediateField.adjoin F (Set.range a) = ⊤)
    {B : Type u} [CommRing B] [Algebra ↥(Algebra.adjoin F (Set.range a)) B]
    [Algebra.FiniteType ↥(Algebra.adjoin F (Set.range a)) B]
    (φ : B →ₐ[↥(Algebra.adjoin F (Set.range a))] K) :
    ∃ s : ↥(Algebra.adjoin F (Set.range a)), s ≠ 0 ∧
      ∀ x : B, ∃ (n : ℕ) (c : ↥(Algebra.adjoin F (Set.range a))),
        algebraMap (↥(Algebra.adjoin F (Set.range a))) K s ^ n * φ x
          = algebraMap (↥(Algebra.adjoin F (Set.range a))) K c := by
  have : NoZeroDivisors ↥(Algebra.adjoin F (Set.range a)) := inferInstance
  exact exists_pow_mul_eq_of_finiteType (A := ↥(Algebra.adjoin F (Set.range a))) φ
    (fun z => exists_mul_eq_of_adjoin_eq_top h z)

end GeneratedFieldCaseSub

/-! ## 4.23 **清分母 ⟹ 落进 `A[s^{-1}]`**（源 `R'' \subseteq R_1(1/s)` 之形）✓✅（第 155 轮）

**源逐字** ✓（`raw/Saltman1982.tex:650--652` ✓）：「… there is an \(s \in R_1\) and an algebra
\(S \supseteq R = R_1(1/s)\) such that \(S/R\) is Galois with group \(G\) and \(S \otimes_R L^G \cong L\).」✓
—— 源的 `R = R_1(1/s)` ✓ 是 `R_1` 在**单个元素处的局部化** ✓，而 §4.22 给的正是「像落进该局部化」✓
（**清分母** ✓）⟹ **本件把二者接上** ✓（**装配 (iv) 的包含步** ✓）。

**⚠ 定理内容** ✓：若 `x` **清分母后**仍是 `A` 中元素的像 ✓（`\exists n\ a,\ \mathrm{algebraMap}\ s^n \cdot x = \mathrm{algebraMap}\ a` ✓），
则 `x` **落在 `A[s^{-1}]` 内** ✓ —— 本件把 `A[s^{-1}]` 取为 `K` 中的**子代数** `\mathrm{Algebra.adjoin}\ A\ \{(\mathrm{algebraMap}\ s)^{-1}\}` ✓
（**＝ `A[1/s]` 在 `K` 中的像** ✓，**免去局部化载体的搬用** ✓ —— **新读数 (63)** ✓）。

**⚠ 证明** ✓：由 `\mathrm{algebraMap}\ s^n \cdot x = \mathrm{algebraMap}\ a` ✓ 得
`x = \mathrm{algebraMap}\ a \cdot ((\mathrm{algebraMap}\ s)^{-1})^n` ✓（**`\mathrm{inv\_pow}`** ✓ ＋ **右消去** ✓）；
再证该式落在 `\mathrm{adjoin}` 内 ✓（**基域项** ✓ 由 `\mathrm{Subalgebra.algebraMap\_mem}` ✓；**生成元** ✓ 由
`\mathrm{Algebra.subset\_adjoin}` ✓；**乘积与幂** ✓ 由 `\mathrm{mul\_mem}` ✓／`\mathrm{Subalgebra.pow\_mem}` ✓）。

**⚠ 两处编译期自纠** ✓（**留痕** ✓）：
**①** **`(\mathrm{algebraMap}\ A\ K).\mathrm{injective}` 报 `\mathrm{IsSimpleRing}\ A`** ✗ —— **实测** ✓：
**`A` 是整环、`K` 是域 ⇒ `\mathrm{algebraMap}` 未必单** ✗（**反例** ✓：`\mathbb{Z} \to \mathbb{F}_p` ✓）⟹
**须显式假设 `[\mathrm{FaithfulSMul}\ A\ K]`** ✓（**＝ `\mathrm{algebraMap}` 单** ✓）**并取 `\mathrm{FaithfulSMul.algebraMap\_injective}`** ✓；
**②** **`\mathrm{mul\_right\_cancel₀}` 是蕴含** ✗（**非 `\leftrightarrow`** ✓）⟹ **直接作函数用** ✓（**原写 `.mp` 报 `Function.mp` 不存在** ✗）。
**⚠ 另一处（非错误，属工艺）** ✓：**实例的 section 作用域** ✓ —— `[\mathrm{Nontrivial}\ A] [\mathrm{NoZeroDivisors}\ A]`
**只在第二条需要** ✓ ⟹ **须分置 section** ✓（否则报 **unused section variables** ✗）。 -/

section AdjoinInverse

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]

/-- **清分母 ⟹ 落进 `A[s^{-1}]`** ✓✅（**单元素形** ✓）。 -/
theorem mem_adjoin_inv_of_pow_mul_eq {s : A} (hs : s ≠ 0) {x : K}
    (h : ∃ (n : ℕ) (a : A), algebraMap A K s ^ n * x = algebraMap A K a) :
    x ∈ Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K) := by
  obtain ⟨n, a, ha⟩ := h
  have hsK : algebraMap A K s ≠ 0 :=
    fun h0 => hs (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  have hx : x = algebraMap A K a * ((algebraMap A K s)⁻¹) ^ n := by
    rw [inv_pow]
    refine mul_right_cancel₀ (pow_ne_zero n hsK) ?_
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hsK), mul_one]
    simpa [mul_comm] using ha
  rw [hx]
  exact mul_mem (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) n)

end AdjoinInverse

section FiniteTypeImage

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

/-- **有限型代数的像落进 `A[s^{-1}]`** ✓✅（**源 `R'' \subseteq R_1(1/s)` 之形** ✓）：由 **§4.22** ✓ 得单个 `s` ✓
使 `B` 的像**全体**落进 `A[s^{-1}]` ✓ —— **装配 (iv) 的包含步** ✓（**下一步**：由此沿 `\mathrm{AlgHom.codRestrict}` ✓
得 `R'' \to R_1(1/s)` ✓ 的**代数同态** ✓，再作基变换 `S'' \otimes_{R''} R` ✓）。 -/
theorem image_le_adjoin_inv_of_finiteType (φ : B →ₐ[A] K)
    (hfrac : ∀ z : K, ∃ x y : A, y ≠ 0 ∧ algebraMap A K y * z = algebraMap A K x) :
    ∃ s : A, s ≠ 0 ∧ ∀ x : B, φ x ∈ Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K) := by
  obtain ⟨s, hs, h⟩ := exists_pow_mul_eq_of_finiteType φ hfrac
  exact ⟨s, hs, fun x => mem_adjoin_inv_of_pow_mul_eq hs (h x)⟩

end FiniteTypeImage

/-! ## 4.24 **`IsTranscendenceBasis` 桥接已闭**（§4.19 的登记项 ✗ ⟹ ✓✅）＋ 代数性引理（第 156 轮）

**起点** ✓：§4.19 ✓（r151）登记「**与 mathlib `IsTranscendenceBasis` 的桥接未落** ✗」✓ ——
**mathlib 的第二合取写在 `\mathrm{Algebra.adjoin}`（子代数 adjoin ✓）上** ✓，而本件给的是**域 adjoin 形** ✓。
**r152 曾试而受阻** ✗（`\mathrm{isTranscendenceBasis\_iff\_algebraicIndependent\_isAlgebraic}` 的**实例推断卡住** ✗，
报 `\mathrm{Nontrivial}\ ?m` ✓，**四种子写法均复现** ✗）。**本轮以另一路径闭之** ✓✅。

**⚠ 新读数 (64)** ✓（**如何解开卡住的实例推断** ✓）：**先把第二合取作为「带显式类型的 `\mathrm{have}` 项」造出来** ✓，
**再**用该词项喂 `\mathrm{iff}.\mathrm{mpr}\ \langle hind, hAlg \rangle` ✓ —— **让 `\mathrm{iff}` 的隐参由词项类型定** ✓，
**而非**由目标驱动推断 ✗（后者会掉进 `\mathrm{Nontrivial}\ ?m` 的僵局 ✗）。

**⚠ 第二合取的证法** ✓（**两条新引理** ✓）：
**①** `isAlgebraic_of_div_eq` ✓✅ —— **`z = x/y`（`y \neq 0`）⟹ `\mathrm{IsAlgebraic}\ A\ z`** ✓
（**取多项式 `C y \cdot X - C x`** ✓：**非零** ✓ 由 `\mathrm{eval}\ 0` 的取值 ✓（`x \neq 0` ✓）；**求值零** ✓ 由 `\mathrm{aeval}` 展开 ✓ ＋ `field_simp` ✓）；
**②** `isAlgebraic_adjoin_of_adjoin_eq_top` ✓✅ —— **域生成 ⟹ `\mathrm{Algebra.IsAlgebraic}\ \uparrow A_0\ K`** ✓
（**逐元素**用 §4.20 的**分式形** ✓ ＋ ① ✓）。

**⚠ 两处编译期自纠** ✓（**留痕** ✓）：**①** **`\mathrm{isAlgebraic\_zero}` 需要 `[\mathrm{Nontrivial}\ A]`** ✗
（**`0` 的代数性**要 `0 \neq 1` ✓ 才能给出**非零**多项式 ✓）⟹ **须显式补该实例** ✓；
**②** **`\mathrm{field\_simp}` 未收尽** ✗ —— 末期留下 `\mathrm{algebraMap}\ x \cdot (1 - 1) = 0` ✓ ⟹ **补 `ring`** ✓。 -/

section IsAlgebraicOfDivEq

variable {A : Type u} [CommRing A] [Nontrivial A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]

/-- **商是代数的** ✓✅：`z = x/y`（`y \neq 0`）⟹ `\mathrm{IsAlgebraic}\ A\ z` ✓。

**⚠ 用途** ✓：**§4.24 桥接的第二合取** ✓ —— 与 §4.20 的**分式形** ✓ 合成即得
「**域生成 ⟹ 生成子代数上的代数性**」✓。 -/
theorem isAlgebraic_of_div_eq {x y : A} (hy : y ≠ 0) {z : K}
    (hz : algebraMap A K x / algebraMap A K y = z) : IsAlgebraic A z := by
  have hyK : algebraMap A K y ≠ 0 :=
    fun h0 => hy (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, zero_div] at hz
    subst hz
    exact isAlgebraic_zero
  · refine ⟨Polynomial.C y * Polynomial.X - Polynomial.C x, ?_, ?_⟩
    · intro h0
      have h1 := congrArg (Polynomial.eval (0 : A)) h0
      simp at h1
      exact hx h1
    · have hval : Polynomial.aeval z (Polynomial.C y * Polynomial.X - Polynomial.C x)
          = algebraMap A K y * z - algebraMap A K x := by
        simp [map_sub, map_mul]
      rw [hval, ← hz]
      field_simp
      ring

end IsAlgebraicOfDivEq

section AdjoinAlgebraic

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {ι : Type*}

/-- **域生成 ⟹ 生成子代数上的代数性** ✓✅ —— **mathlib `IsTranscendenceBasis` 判据的第二合取** ✓
（**第一合取** ＝ §4.19 的**代数无关** ✓）。 -/
theorem isAlgebraic_adjoin_of_adjoin_eq_top {a : ι → K}
    (h : IntermediateField.adjoin F (Set.range a) = ⊤) :
    Algebra.IsAlgebraic ↥(Algebra.adjoin F (Set.range a)) K := by
  have : FaithfulSMul ↥(Algebra.adjoin F (Set.range a)) K := inferInstance
  refine ⟨fun z => ?_⟩
  obtain ⟨x, y, hy, hxy⟩ := exists_div_eq_of_adjoin_eq_top h z
  exact isAlgebraic_of_div_eq hy hxy

/-- **桥接** ✓✅（**§4.19 的登记项 ✗ ⟹ ✓✅**）：**域生成 ＋ 代数无关 ⟹ mathlib `\mathrm{IsTranscendenceBasis}`** ✓
（**域生成形 ⟺ 子代数形** ✓，**见 §4.19 的口径登记** ✓）。 -/
theorem isTranscendenceBasis_of_algebraicIndependent_adjoin_eq_top {a : ι → K}
    (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤) :
    IsTranscendenceBasis F a := by
  have hAlg : Algebra.IsAlgebraic ↥(Algebra.adjoin F (Set.range a)) K :=
    isAlgebraic_adjoin_of_adjoin_eq_top hgen
  have hiff : IsTranscendenceBasis F a ↔ AlgebraicIndependent F a ∧
      Algebra.IsAlgebraic ↥(Algebra.adjoin F (Set.range a)) K :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic (R := F) (A := K) (x := a)
  exact hiff.mpr ⟨hind, hAlg⟩

/-- **完整抽取（mathlib 超越基形）** ✓✅：`\mathrm{IsRationalOver}\ F\ K` ⟹ **存在 `\mathrm{IsTranscendenceBasis}`** ✓
—— **§4.19 的域生成形** ✓ 经桥接 ✓ 升为 **mathlib 标准形** ✓（**源 `theorem-5-1` 首句的最终形式** ✓）。 -/
theorem exists_isTranscendenceBasis_of_isRationalOver (h : IsRationalOver F K) :
    ∃ (n : ℕ) (a : Fin n → K), IsTranscendenceBasis F a := by
  obtain ⟨n, a, hind, hgen⟩ := exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver h
  exact ⟨n, a, isTranscendenceBasis_of_algebraicIndependent_adjoin_eq_top hind hgen⟩

end AdjoinAlgebraic

/-! ## 4.25 **源「新 `R = R_1(1/s)`」的载体步**（`A[s^{-1}]` 的性质 ＋ `R''` 的像因子化）✓✅（第 157 轮）

**源逐字** ✓（`raw/Saltman1982.tex:650--651` ✓）：「… there is an \(s \in R_1\) and an algebra
\(S \supseteq R = R_1(1/s)\) such that \(S/R\) is Galois with group \(G\) and \(S \otimes_R L^G \cong L\).」✓
—— 源的**新 `R`** 是 `R_1(1/s)` ✓；本件把该载体**在 `K` 内实现** ✓（§4.23 的读数 (63) ✓）并证其**三条接口性质** ✓，
使 `R''` 的像**因子化过它** ✓（**源「`S''` 沿 `R'' \to R` 作基变换」的前置** ✓）。

**⚠ 三件** ✓：
**①** `algebraMap_mem_adjoin_inv` ✓✅ —— **`A[s^{-1}]` 含 `A` 的像** ✓（**基域项** ✓）；
**②** `finiteType_adjoin_inv` ✓✅ —— **`A[s^{-1}]` 在 `A` 上有限型** ✓（**单个**生成元 ✓；
入口 ＝ `\mathrm{Subalgebra.fg\_adjoin\_finset}` ✓ ＋ **`\mathrm{Subalgebra.fg\_top}`** ✓）；
**③** `exists_factors_through_adjoin_inv_of_finiteType` ✓✅ —— **`\varphi` 因子化过 `A[s^{-1}]`** ✓：
`\exists s \neq 0,\ \exists \psi : B \to_A A[s^{-1}],\ \forall x,\ (\psi x : K) = \varphi x` ✓
（**沿 `\mathrm{AlgHom.codRestrict}`** ✓，**像的包含由 §4.23** ✓）。

**⚠ 两处编译期自纠** ✓（**留痕** ✓）：**①** **`\mathrm{Subalgebra.fg\_adjoin\_finset}` 与
`\mathrm{Subalgebra.fg\_top}` 须显式给基环** ✗（否则报 `\mathrm{Algebra.adjoin}\ ?m` 的元变量未定 ✗）；
**②** **`\mathrm{Finset}` 的单点强制转换 `\uparrow\{x\}` 与 `\mathrm{Set}` 的单点 `\{x\}` 不是 defeq** ✗
（`\mathrm{Finset.coe\_singleton}` 是**定理** ✓）⟹ **须 `\mathrm{simpa}` 过** ✓（**新读数 (65)** ✓）。
**⚠ 另一处（工艺）** ✓：**未用到的实例须移出 section** ✗（否则 **unused section variables** ✗）。 -/

section LocalizedCarrier

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K] [Algebra A K]

/-- **`A[s^{-1}]` 含 `A` 的像** ✓✅（**`K` 内的子代数** ✓，**读数 (63)** ✓）。 -/
theorem algebraMap_mem_adjoin_inv (s a : A) :
    algebraMap A K a ∈ Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K) :=
  Subalgebra.algebraMap_mem _ a

/-- **`A[s^{-1}]` 在 `A` 上有限型** ✓✅（**单个**生成元 `(\mathrm{algebraMap}\ s)^{-1}` ✓）。 -/
theorem finiteType_adjoin_inv (s : A) :
    Algebra.FiniteType A ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) :=
  ⟨(Subalgebra.fg_top (Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K))).mpr (by
    simpa using Subalgebra.fg_adjoin_finset (R := A) ({(algebraMap A K s)⁻¹} : Finset K))⟩

end LocalizedCarrier

section FactorsThrough

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

/-- **有限型代数的像因子化过 `A[s^{-1}]`** ✓✅（**源「新 `R`」的载体步** ✓）：
存在 `s \neq 0` 与代数同态 `\psi : B \to_A A[s^{-1}]` ✓，使 `\psi` 与 `\varphi` 在 `K` 中**同值** ✓
（**故 `R''` 的像落进新 `R`** ✓，**源「`S''` 沿 `R'' \to R` 作基变换」的前置** ✓）。 -/
theorem exists_factors_through_adjoin_inv_of_finiteType (φ : B →ₐ[A] K)
    (hfrac : ∀ z : K, ∃ x y : A, y ≠ 0 ∧ algebraMap A K y * z = algebraMap A K x) :
    ∃ (s : A) (ψ : B →ₐ[A] ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K))),
      s ≠ 0 ∧ ∀ x : B, ((ψ x : K)) = φ x := by
  obtain ⟨s, hs, h⟩ := image_le_adjoin_inv_of_finiteType φ hfrac
  exact ⟨s, φ.codRestrict _ (fun x => h x), hs, fun x => AlgHom.coe_codRestrict _ _ _ x⟩

end FactorsThrough

/-! ## 4.26 **超越基生成的多项式环**（源 `R_1 = F[a_1,\dots,a_n]` 的识别 ＋ 有限型）✓✅（第 158 轮）

**源逐字** ✓（`raw/Saltman1982.tex:649--650` ✓）：「Set \(R_1 = F[a_1,\dots,a_n] \subset L^G\).」✓ ——
即源把超越基**生成的多项式子代数**记作 `R_1` ✓；而 `\mathrm{IsGenericExtension}` 的**第 (a) 款** ✓
要求 `R` **同构于某局部化多项式环** ✓（`\exists n\ w,\ w \neq 0 \wedge R \simeq_F \mathrm{Localization.Away}\ w` ✓）
⟹ **须先识别 `A_0 = \mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\}` 本身** ✓。

**⚠ 两件** ✓：
**①** **`nonempty_algEquiv_mvPolynomial_adjoin`** ✓✅ —— **代数无关族生成的子代数 ≅ 多项式环** ✓：
`\mathrm{AlgebraicIndependent}\ F\ a \Rightarrow \exists\, (MvPolynomial\ (Fin\ n)\ F \simeq_F \uparrow(\mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\}))` ✓
（**入口** ✓：`\mathrm{algebraicIndependent\_iff\_injective\_aeval}` ✓ 给**单射** ✓；
**`\mathrm{MvPolynomial.aeval\_range}`** ✓ 给**值域 ＝ 该子代数** ✓；**`\mathrm{AlgEquiv.ofInjective}`** ✓ 收 ✓）；
**②** `finiteType_adjoin_range` ✓✅ —— **有限族生成的子代数在基域上有限型** ✓
（`\mathrm{Subalgebra.fg\_adjoin\_finset}` ✓ ＋ `\mathrm{Subalgebra.fg\_top}` ✓；
**⚠ 这是 `\mathrm{RepresentingObject}` 的 `\mathrm{Algebra.FiniteType}\ F\ X.R` 一款** ✓）。

**⚠ 两处编译期自纠** ✓（**留痕** ✓）：**①** **`\mathrm{MvPolynomial.aeval\_range}` 须显式给 `R`／`f`** ✗
（**同 (65) 的「`\mathrm{adjoin}` 系引理隐参须显式」** ✓ —— **该模式本轮二次复现** ✓）；
**②** **`\mathrm{Finset.image}` 需 `\mathrm{DecidableEq}`** ✗ ⟹ **证内 `\mathrm{classical}`** ✓
（**不**加强陈述 ✓，**同 (62) 的伴生坑** ✓）。 -/

section PolyRingOfBasis

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K] {n : ℕ}

/-- **代数无关族生成的子代数 ≅ 多项式环** ✓✅（**源 `R_1 = F[a_1,\dots,a_n]` 的识别** ✓）。 -/
theorem nonempty_algEquiv_mvPolynomial_adjoin {a : Fin n → K}
    (hind : AlgebraicIndependent F a) :
    Nonempty (MvPolynomial (Fin n) F ≃ₐ[F] ↥(Algebra.adjoin F (Set.range a))) := by
  have hinj : Function.Injective (MvPolynomial.aeval a) :=
    algebraicIndependent_iff_injective_aeval.mp hind
  have hrange : (MvPolynomial.aeval a : MvPolynomial (Fin n) F →ₐ[F] K).range
      = Algebra.adjoin F (Set.range a) := MvPolynomial.aeval_range (R := F) (f := a)
  rw [← hrange]
  exact ⟨AlgEquiv.ofInjective _ hinj⟩

/-- **有限族生成的子代数在基域上有限型** ✓✅（**`\mathrm{RepresentingObject}` 的一款** ✓）。 -/
theorem finiteType_adjoin_range (a : Fin n → K) :
    Algebra.FiniteType F ↥(Algebra.adjoin F (Set.range a)) := by
  classical
  refine ⟨(Subalgebra.fg_top (Algebra.adjoin F (Set.range a))).mpr ?_⟩
  have h : (↑(Finset.univ.image a) : Set K) = Set.range a := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [← h]
  exact Subalgebra.fg_adjoin_finset (R := F) (Finset.univ.image a)

end PolyRingOfBasis

/-! ## 4.27 **局部化到域的环同态**（源「新 `R`」的抽象载体接口）✓（第 161 轮）

**⚠ 装配背景** ✓：源的新 `R = R_1(1/s)` ✓ 有两**载体**选择 ✓：**(i)** §4.23 的**子代数形** ✓
`\mathrm{Algebra.adjoin}\ A_0\ \{(\mathrm{algebraMap}\ s)^{-1}\} \subseteq K` ✓（**已在库** ✓）；
**(ii)** **抽象局部化形** ✓ `\mathrm{Localization.Away}\ w` ✓ —— 后者使 **`\mathrm{IsGenericExtension}`(a) 款**
**按构造成立** ✓（**读数 (67) 的取向** ✓）。
**⚠ 两者之间的桥** ✓（**本轮起头** ✓）：**抽象局部化可映回 `K`** ✓ —— 即由**万有性质** ✓
（`s` 在 `K` 中可逆 ✓）得 `R_{\mathrm{loc}} \to K` 的**环同态** ✓，且**在基环上与 `\mathrm{algebraMap}` 一致** ✓。

**⚠ 本轮落地** ✓：`exists_ringHom_away_to_field` ✓✅ —— **入口** ✓：`\mathrm{IsLocalization.Away.lift}` ✓
＋ **`\mathrm{IsLocalization.Away.lift\_comp}`** ✓（给与 `\mathrm{algebraMap}` 的一致 ✓）；
**可逆性** ✓ 由 `\mathrm{isUnit\_iff\_ne\_zero}` ✓ ＋ **`\mathrm{FaithfulSMul.algebraMap\_injective}`** ✓
（`s \neq 0 \Rightarrow \mathrm{algebraMap}\ s \neq 0` ✓ —— **同 (63) 的嵌入假设** ✓）。

**⚠ 登记（本轮未落）** ✗：**①** **像的包含** ✓（`\mathrm{adjoin}\ A\ \{(s)^{-1}\} \subseteq \psi.\mathrm{range}` ✓）——
**思路已定** ✓：`\mathrm{Algebra.mem\_adjoin\_iff}` ✓ 化到 `\mathrm{Subring.closure}` ✓ ＋ `\mathrm{Subring.closure\_le}` ✓；
**阻塞** ✗：**`s` 在 `R_{\mathrm{loc}}` 中的像是单位的引理名** ✗（`\mathrm{IsLocalization.Away.isUnit}` **不存在** ✗，
**实测** ✓；`\mathrm{IsLocalization.map\_units}` ✓ 需 `\mathrm{Submonoid.powers}` 的成员证明 ✗）⟹ **次轮查名后落** ✓；
**②** **双侧合为同构** ✓（像的包含 ＋ 单射 ✓）⟹ `A_0[s^{-1}] \simeq_F \mathrm{Localization.Away}\ w` ✓。 -/

section AwayToField

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]
variable {Rloc : Type u} [CommRing Rloc] [Algebra A Rloc]

/-- **局部化到域的环同态** ✓：`s` 在 `K` 中可逆 ⟹ **由万有性质**得 `R_{\mathrm{loc}} \to K` ✓，
且在基环上与 `\mathrm{algebraMap}` **一致** ✓。 -/
theorem exists_ringHom_away_to_field (s : A) [IsLocalization.Away s Rloc] (hs : s ≠ 0) :
    ∃ ψ : Rloc →+* K, ∀ a : A, ψ (algebraMap A Rloc a) = algebraMap A K a := by
  have hsK : IsUnit (algebraMap A K s) := by
    rw [isUnit_iff_ne_zero]
    exact fun h0 => hs (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  exact ⟨IsLocalization.Away.lift s hsK,
    fun a => congrArg (fun f => f a) (IsLocalization.Away.lift_comp s hsK)⟩

end AwayToField

/-! ## 4.28 **`A[s^{-1}]` 的元素是分数**（局部化同构的 `surj` 内容）✓（第 162 轮）

**⚠ 装配背景** ✓：§4.27 给了**抽象局部化 → K** 的环同态 ✓；要把它升为**同构** ✓（**`IsGenericExtension`(a) 所需** ✓，
**读数 (67) 的载体桥** ✓），须证两件：**①** **像的包含** ✗（**登记，见下** ✓）；**②** **每个元素都是分数** ✓✅（**本轮落** ✓）。
**⚠ 本轮件的用途** ✓：**② 正是 `\mathrm{IsLocalization}` 结构里 `\mathrm{surj}` 一款的内容** ✓
（**每个 `x \in A[s^{-1}]` 都可写成 `a / s^n`** ✓）—— 反过来说 ✓：**`A[s^{-1}]` 被 `A` 与 `s^{-1}` 的分数穷尽** ✓。

**⚠ 证明** ✓：对 `\mathrm{Algebra.adjoin}\ A\ \{(s)^{-1}\}` 作**结构归纳** ✓（**四支** ✓：生成元 ✓／基域 ✓／加法 ✓／乘法 ✓），
**逐支**给出「分母为 `s` 的幂」的形 ✓：**生成元支** `n = 1`、`a = 1` ✓（`s^{-1} \cdot s = 1` ✓，**用 `\mathrm{inv\_mul\_cancel₀}`** ✓）；
**基域支** `n = 0` ✓；**加法支** `n + m`、`a s^m + b s^n` ✓；**乘法支** `n + m`、`a b` ✓
（**⚠ 分子须在 `A` 内** ✓ —— 故取 `a \cdot s^m + b \cdot s^n \in A` ✓ 再经 `\mathrm{map\_add}`／`\mathrm{map\_mul}`／**`\mathrm{map\_pow}`** ✓ 展开 ✓）。

**⚠ 登记（本轮未落）** ✗：**像的包含** ✓（`\mathrm{adjoin}\ A\ \{(s)^{-1}\} \subseteq \psi.\mathrm{range}` ✓）——
**思路已定** ✓（`\mathrm{Algebra.mem\_adjoin\_iff}` ✓ ＋ `\mathrm{Subring.closure\_le}` ✓ ＋
**`\mathrm{IsLocalization.map\_units}`** ✓，**引理名已找到** ✓：配 `\mathrm{Submonoid.mem\_powers\_iff}` ✓ 得 `s \in \mathrm{powers}\ s` ✓）；
**本轮阻塞** ✗：**`\mathrm{Units}` 的强制转换簿记** ✗ —— 目标是 `\psi (\uparrow u^{-1}) = (\mathrm{algebraMap}\ s)^{-1}` ✓，
而 `\mathrm{map\_inv₀}`／`\mathrm{Units.val\_inv\_eq\_inv\_val}`／`\mathrm{Units.inv\_val}` **三种写法均未匹配** ✗（**实测** ✓）
⟹ **次轮改用 `\mathrm{IsUnit.map}`** ✓（**已有环同态 `\psi`** ✓，**可绕开强制转换** ✓）**或 `\mathrm{show}` 显式化** ✓。 -/

section AwayFractionForm

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]

/-- **`A[s^{-1}]` 的元素是分数** ✓✅：`x \in \mathrm{Algebra.adjoin}\ A\ \{(s)^{-1}\}` ⟹
`\exists n\ a,\ x \cdot s^n = \mathrm{algebraMap}\ a` ✓（`s := \mathrm{algebraMap}\ A\ K\ s` ✓）。 -/
theorem exists_pow_mul_eq_of_mem_adjoin_inv (s : A) (hs : s ≠ 0) :
    ∀ x ∈ Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K),
      ∃ (n : ℕ) (a : A), x * (algebraMap A K s) ^ n = algebraMap A K a := by
  have hsK : algebraMap A K s ≠ 0 :=
    fun h0 => hs (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  intro x hx
  refine Algebra.adjoin_induction (p := fun x _ => ∃ (n : ℕ) (a : A),
    x * (algebraMap A K s) ^ n = algebraMap A K a) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨1, 1, by rw [pow_one, inv_mul_cancel₀ hsK, map_one]⟩
  · intro a
    exact ⟨0, a, by rw [pow_zero, mul_one]⟩
  · intro x y _ _ ihx ihy
    obtain ⟨n, a, hx'⟩ := ihx
    obtain ⟨m, b, hy'⟩ := ihy
    refine ⟨n + m, a * s ^ m + b * s ^ n, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, pow_add]
    rw [show (x + y) * ((algebraMap A K s) ^ n * (algebraMap A K s) ^ m)
          = (x * (algebraMap A K s) ^ n) * (algebraMap A K s) ^ m
            + (y * (algebraMap A K s) ^ m) * (algebraMap A K s) ^ n from by ring,
      hx', hy']
  · intro x y _ _ ihx ihy
    obtain ⟨n, a, hx'⟩ := ihx
    obtain ⟨m, b, hy'⟩ := ihy
    refine ⟨n + m, a * b, ?_⟩
    rw [map_mul, pow_add, mul_mul_mul_comm, hx', hy']

end AwayFractionForm

/-! ## 4.29 **`A[s^{-1}]` 与 `Localization.subalgebra`**（局部化同构的现成机器）✓（第 163 轮）

**⚠ 装配背景** ✓：§4.27／§4.28 在为**抽象局部化 → K** 的环同态升同构铺路 ✓；本轮的侦察**改变了路线** ✓。

**✅ 重大发现** ✓（**新读数 (70)** ✓）：**mathlib 已有**`\mathrm{Localization.subalgebra}` ✓
（`RingTheory/Localization/AsSubring.lean` ✓）—— 对 `[\mathrm{IsFractionRing}\ A\ K]` ✓ 与子幺半群 `S \le A^0` ✓，
它给出 **`K` 中「`A` 在 `S` 处的局部化」子代数** ✓（载体 ＝ 形如 `\mathrm{IsLocalization.mk'}\ K\ a\ \langle s, \_\rangle` 的元素 ✓），
**并附现成实例** ✓ `\mathrm{IsLocalization}\ S\ \uparrow(\mathrm{Localization.subalgebra}\ K\ S\ hS)` ✓。
**⚠ 这一步把同构路线的**机器**从「自建四款」✗ 降为「识别子代数 ＋ 搬实例」✓** ✓（**读数 (67) 的应用** ✓）。

**⚠ 本轮落地两件** ✓：
**①** `powers_le_nonZeroDivisors` ✓✅ —— **`s \neq 0 \Rightarrow \mathrm{powers}\ s \le A^0`** ✓
（**`\mathrm{Localization.subalgebra}` 的前提** ✓；由 `\mathrm{mem\_nonZeroDivisors\_iff\_ne\_zero}` ✓ ＋
**`\mathrm{pow\_mem}`** ✓）；
**②** `isLocalization_localizationSubalgebra` ✓✅ —— **类型锁定** ✓：**该子代数确实是局部化** ✓（`\mathrm{inferInstance}` ✓）。

**⚠ 登记（本轮未落，**路线已定**）** ✗：**`\mathrm{Algebra.adjoin}\ A\ \{(s)^{-1}\} = \mathrm{Localization.subalgebra}\ K\ (\mathrm{powers}\ s)\ hS`** ✗
—— **两向** ✓：**（⊆）** 由 `\mathrm{mem\_range\_mapToFractionRing\_iff}` ✓ 取 `a`／`s^n` ✓，
再用 **`\mathrm{IsLocalization.mk'\_spec}`** ✓ 与 `\mathrm{inv\_pow}` ✓ 得分数形 ✓；
**（⊇）** 由 **§4.28 的分数形** ✓（`x \cdot s^n = \mathrm{algebraMap}\ a` ✓ ⟹ `x = \mathrm{algebraMap}\ a \cdot ((s)^{-1})^n` ✓ ∈ adjoin ✓）。
**⚠ 阻塞** ✗（**本轮实测** ✓）：**`\mathrm{IsLocalization.mk'}` 一侧的 `\mathrm{Units}`／强制转换簿记** ✗
（与 §4.28 登记同一类 ✗）⟹ **次轮**：**先写 `\mathrm{show}` 显式形** ✓ 或**改从 `\mathrm{subalgebra}` 的载体描述出发** ✓。
**⚠ 收益** ✓：一旦该等式落地 ✓，**`\mathrm{IsLocalization.Away}\ s\ \uparrow(\mathrm{adjoin}\ A\ \{(s)^{-1}\})`** ✓
**由改写 ＋ `\mathrm{inferInstance}` 即得** ✓，再经 **`\mathrm{IsLocalization.algEquiv}`** ✓ 得**同构** ✓ ⟹ **`\mathrm{IsGenericExtension}`(a) 齐备** ✓。 -/

section AdjoinEqLocalization

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]

/-- **`s \neq 0` ⟹ `s` 的幂全在非零因子里** ✓✅（**`\mathrm{Localization.subalgebra}` 的前提** ✓）。 -/
theorem powers_le_nonZeroDivisors (s : A) (hs : s ≠ 0) :
    Submonoid.powers s ≤ nonZeroDivisors A := by
  intro y hy
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y s).mp hy
  exact pow_mem (mem_nonZeroDivisors_iff_ne_zero.mpr hs) n

end AdjoinEqLocalization

section SubalgebraInstance

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]

/-- **现成实例的类型锁定** ✓✅：`\mathrm{Localization.subalgebra}\ K\ S\ hS` **就是** `A` 在 `S` 处的局部化 ✓
（**mathlib 已给** ✓：`\mathrm{Localization.isLocalization\_subalgebra}` ✓）。 -/
theorem isLocalization_localizationSubalgebra (s : A) (hs : s ≠ 0) :
    IsLocalization (Submonoid.powers s)
      (Localization.subalgebra K (Submonoid.powers s) (powers_le_nonZeroDivisors s hs)) :=
  inferInstance

end SubalgebraInstance

/-! ## 4.30 **`A[s^{-1}]` ＝ `Localization.subalgebra`**（局部化同构落地）✓✅（第 164 轮）

**⚠ 起点** ✓：§4.29 登记「`\mathrm{Algebra.adjoin}\ A\ \{(s)^{-1}\} = \mathrm{Localization.subalgebra}\ K\ (\mathrm{powers}\ s)\ hS`」✗
（**路线已定** ✓）—— **本轮落地** ✓✅。

**⚠ 本轮三件** ✓：
**①** **`adjoin_inv_eq_localizationSubalgebra`** ✓✅ —— **两侧相等** ✓；
**②** **`\mathrm{IsLocalization}\ (\mathrm{powers}\ s)\ \uparrow(\mathrm{adjoin}\ A\ \{(s)^{-1}\})`** ✗（**登记** ✓ ——
**⚠ 本轮实测** ✗：由等式**搬实例**（`\mathrm{Eq.rec}` 方向 ✓）时，`\mathrm{IsLocalization}` 的**隐式实例参数**
（`\mathrm{toCommSemiring}`／`\mathrm{algebra}`）**不随之改写** ✗ ⟹ **报类型不匹配** ✗）；
**③** **`\mathrm{Away}` 形** ✗ —— **实测** ✓：`\mathrm{Away}` 形**不是** `\mathrm{powers}` 形的 defeq ✗ ⟹ 须**显式桥** ✓。

**⚠ 证明要点** ✓（**（⊆）向** ✓）：把 `\mathrm{Localization.subalgebra}` **先 `\mathrm{dsimp\ only}`** ✓
（**它是 `\mathrm{def}`** ✗ —— **不 `\mathrm{dsimp}` 则 `\mathrm{Subalgebra.copy\_eq}` 不匹配** ✗，**实测** ✓）
**再 `\mathrm{rw}\ [\mathrm{Subalgebra.copy\_eq}]`** ✓ 化到值域 ✓，用 **`\mathrm{mem\_range\_mapToFractionRing\_iff}`** ✓ 取 `a`／`s^n` ✓，
最后以 **`\mathrm{IsLocalization.mk'\_spec}`** ✓ ＋ `\mathrm{inv\_pow}` ✓ 得分数形 ✓；
**（⊇）向** ✓ 由 **§4.28** ✓ ＋ `\mathrm{mk'\_spec}` ✓ ＋ **右消去** ✓（两侧同乘 `s^n` ✓）。

**⚠ 五处编译期自纠** ✓（**留痕** ✓）：**①** **`\mathrm{IsLocalization.of\_le}` 方向反** ✗
（它是 `M \le N` 的**放大**方向 ✓；**`\mathrm{powers}\ s \le A^0` 是缩小** ✗）⟹ **`\mathrm{mk'}` 用的仍是 `A^0` 处实例** ✓
（**（`\mathrm{IsFractionRing}` 给** ✓），**无须**另造 ✓；**②** **`\mathrm{le\_antisymm}` 两支方向弄反** ✗（**实测** ✓）；
**③** `\mathrm{Subalgebra.copy}` 的**成员判定不是 defeq** ✗ ⟹ 须 `\mathrm{dsimp}` ＋ `\mathrm{copy\_eq}` ✓；
**④** **`\mathrm{Submonoid.pow\_mem}` 须显式子幺半群参数** ✗；**⑤** **`\mathrm{map\_pow}` 的方向** ✗（**对 `hspec` 而非目标** ✓）。
**⚠ 登记（未落）** ✗：**`\mathrm{IsLocalization.Away}\ s\ \uparrow(\mathrm{adjoin}\ \ldots)`** ✗ ——
**实测** ✓：`\mathrm{Away}` 形**不是** `\mathrm{powers}` 形的 defeq ✗ ⟹ 须**显式桥** ✓（次轮查 `\mathrm{IsLocalization.Away}` 的构造引理 ✓）。 -/



section AdjoinEqLocalization

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K] [IsFractionRing A K]

/-- **adjoin 与局部化子代数相等** ✓：`A[s⁻¹]` 就是 `A` 在 `s` 的幂处的局部化（视作 `K` 的子代数）。 -/
theorem adjoin_inv_eq_localizationSubalgebra (s : A) (hs : s ≠ 0) :
    Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)
      = Localization.subalgebra K (Submonoid.powers s) (powers_le_nonZeroDivisors s hs) := by
  have hsK : algebraMap A K s ≠ 0 :=
    fun h0 => hs (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨n, a, hxa⟩ := exists_pow_mul_eq_of_mem_adjoin_inv (K := K) s hs x hx
    have hmem : s ^ n ∈ Submonoid.powers s :=
      Submonoid.pow_mem (Submonoid.powers s) ((Submonoid.mem_powers_iff s s).mpr ⟨1, pow_one s⟩) n
    dsimp only [Localization.subalgebra]
    rw [Subalgebra.copy_eq]
    refine (Localization.mem_range_mapToFractionRing_iff K (Submonoid.powers s)
      (Localization (Submonoid.powers s)) (powers_le_nonZeroDivisors s hs) x).mpr
      ⟨a, s ^ n, hmem, ?_⟩
    have hspec := IsLocalization.mk'_spec K a ⟨s ^ n, powers_le_nonZeroDivisors s hs hmem⟩
    rw [map_pow] at hspec
    exact mul_right_cancel₀ (pow_ne_zero n hsK) (by rw [hxa, hspec])
  · intro x hx
    dsimp only [Localization.subalgebra] at hx
    rw [Subalgebra.copy_eq] at hx
    have hx' := (Localization.mem_range_mapToFractionRing_iff K (Submonoid.powers s)
      (Localization (Submonoid.powers s)) (powers_le_nonZeroDivisors s hs) x).mp hx
    obtain ⟨a, t, ht, rfl⟩ := hx'
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff t s).mp ht
    have hmem : s ^ n ∈ Submonoid.powers s :=
      Submonoid.pow_mem (Submonoid.powers s) ((Submonoid.mem_powers_iff s s).mpr ⟨1, pow_one s⟩) n
    have hspec := IsLocalization.mk'_spec K a ⟨s ^ n,
      powers_le_nonZeroDivisors s hs hmem⟩
    have h1 : IsLocalization.mk' K a ⟨s ^ n, powers_le_nonZeroDivisors s hs hmem⟩
        * (algebraMap A K s) ^ n = algebraMap A K a := by
      rw [map_pow] at hspec
      exact hspec
    have h2 : IsLocalization.mk' K a ⟨s ^ n, powers_le_nonZeroDivisors s hs hmem⟩
        = algebraMap A K a * ((algebraMap A K s)⁻¹) ^ n := by
      rw [inv_pow]
      exact mul_right_cancel₀ (pow_ne_zero n hsK)
        (by rw [h1, mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hsK), mul_one])
    rw [h2]
    exact mul_mem (Subalgebra.algebraMap_mem _ a)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) n)

end AdjoinEqLocalization


/-! ## 4.31 **局部化同构**（`IsGenericExtension`(a) 的原料齐备）✓✅（第 165 轮）

**⚠ 起点** ✓：§4.30 ✓ 已给**子代数等式** ✓（`\mathrm{adjoin}\ A\ \{(s)^{-1}\} = \mathrm{Localization.subalgebra}\ K\ (\mathrm{powers}\ s)\ hS` ✓）；
§4.30 的登记 ✗ 两项**本轮全解** ✓✅。

**⚠ 本轮三件** ✓：
**①** `isLocalization_powers_adjoin_inv` ✓✅ —— **`\mathrm{IsLocalization}\ (\mathrm{powers}\ s)\ \uparrow(\mathrm{adjoin}\ A\ \{(s)^{-1}\})`** ✓
（**搬用路线** ✓：**`\mathrm{Subalgebra.equivOfEq}`** ✓ 把子代数等式转成 **`A`-代数同构** ✓，
再用 **`\mathrm{IsLocalization.isLocalization\_of\_algEquiv}`** ✓ 搬实例 ✓ —— **r164 的「`\mathrm{Eq.rec}` 隐式实例参数不改写」问题由此绕开** ✓✅）；
**②** `isLocalization_away_adjoin_inv` ✓✅ —— **`\mathrm{Away}` 形** ✓
（**实测** ✓：`\mathrm{IsLocalization.Away}` 是 **`@[\mathrm{reducible}]` 的 `\mathrm{def}` ＝ `\mathrm{powers}` 形** ✓
⟹ **直接 `\mathrm{exact}` 即过** ✓ —— **r164 的「非 defeq」判定被推翻** ✓✅，**读数 (73)** ✓）；
**③** **`nonempty_algEquiv_localizationAway_adjoin_inv`** ✓✅ —— **局部化同构** ✓：
`\exists\,(\mathrm{Localization.Away}\ s \simeq_A \uparrow(\mathrm{adjoin}\ A\ \{(s)^{-1}\}))` ✓
（**入口** ✓：**`\mathrm{IsLocalization.algEquiv}`** ✓ —— **同一环的两处局部化典范同构** ✓）。

**⚠ 意义** ✓：**`\mathrm{IsGenericExtension}`(a) 款的原料至此齐备** ✓ ——
**余**：把 r158 的多项式环同构 ✓ 与本次局部化同构 ✓ **沿基环同构复合** ✓（**读数 (51) 的应用** ✓：**先查
「局部化沿基环同构的搬运」引理** ✓）。
**⚠ 新读数 (73)** ✓（**「非 defeq」判定须复核 `[\mathrm{reducible}]`** ✓）：**凡判某两形「非 defeq」前，先 `\#print` 其定义** ✓ ——
本轮的 `\mathrm{IsLocalization.Away}` ✓ 是 `@[\mathrm{reducible}]` ✓ ⟹ **r164 的受阻判定有误** ✓，**当轮已据实更正** ✓。 -/



section ISLocalizationAdjoin

variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K] [IsFractionRing A K]

/-- **`A[s⁻¹]` 是 `A` 在 `s` 的幂处的局部化** ✓（由子代数等式 ＋ `isLocalization_of_algEquiv` 搬用）。 -/
theorem isLocalization_powers_adjoin_inv (s : A) (hs : s ≠ 0) :
    IsLocalization (Submonoid.powers s) ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers s)
    (Subalgebra.equivOfEq _ _ (adjoin_inv_eq_localizationSubalgebra (K := K) s hs).symm)

/-- **`Away` 形**（`IsLocalization.Away` 是 `@[reducible]` 的 `powers` 形）。 -/
theorem isLocalization_away_adjoin_inv (s : A) (hs : s ≠ 0) :
    IsLocalization.Away s ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) :=
  isLocalization_powers_adjoin_inv (K := K) s hs

/-- **局部化同构** ✓：抽象局部化 ≃ `A[s⁻¹]`（`A`-代数同构）—— **`IsGenericExtension`(a) 的直接原料** ✓。 -/
theorem nonempty_algEquiv_localizationAway_adjoin_inv (s : A) (hs : s ≠ 0) :
    Nonempty (Localization.Away s ≃ₐ[A] ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K))) :=
  haveI := isLocalization_away_adjoin_inv (K := K) s hs
  ⟨IsLocalization.algEquiv (Submonoid.powers s) _ _⟩

end ISLocalizationAdjoin


/-! ## 4.32 **局部化沿基环同构搬运**（(a) 款的复合用件）✓✅（第 166 轮）

**⚠ 起点** ✓：§128.6 第 1 项 —— 把 **r158 的多项式环同构** ✓ 与 **r165 的局部化同构** ✓ **沿基环同构复合** ✓
（**读数 (70) 的应用** ✓：**先查现成机器** ✓）。

**⚠ 本轮两件** ✓：
**①** **`nonempty_algEquiv_localizationAway_map`** ✓✅ —— **基环同构 `e : A \simeq_F B` ⟹
`\mathrm{Localization.Away}\ a \simeq_F \mathrm{Localization.Away}\ (e a)`** ✓
（**入口** ✓：**`\mathrm{IsLocalization.algEquivOfAlgEquiv}`** ✓ —— **局部化沿基环同构的搬运** ✓；
**前提** ✓ 由 **`\mathrm{Submonoid.map\_powers}`** ✓ 供给 ✓ —— **即 `\mathrm{Submonoid.map}\ e\ (\mathrm{powers}\ a) = \mathrm{powers}\ (e a)`** ✓）；
**②** `algEquiv_ne_zero_iff` ✓✅ —— **非零沿同构搬运** ✓（`e a \neq 0 \leftrightarrow a \neq 0` ✓ —— **(a) 款的 `w \neq 0` 一侧** ✓）。

**⚠ 登记（本轮未落，**路线已定**）** ✗：**(a) 款的**具体形**** ✓ ——
`\mathrm{AlgebraicIndependent}\ F\ a` ＋ `s \neq 0`（`s \in A_0` ✓）⟹ `\exists w \neq 0,\ \uparrow(A_0[s^{-1}]) \simeq_F \mathrm{Localization.Away}\ w` ✓
—— **两处阻塞** ✗（**本轮实测** ✓）：
**（i）** **`[\mathrm{IsFractionRing}\ \uparrow A_0\ K]`** ✗ —— **r165 的局部化同构需要它** ✓，
而本工程只有 **§4.20 的**逐元素**分式形** ✓ ⟹ **须先把逐元素形升为 `\mathrm{IsFractionRing}` 实例** ✓（**四款直造** ✓，**次轮** ✓）；
**（ii）** **`\simeq_{\uparrow A_0}` 到 `\simeq_F` 的转换** ✗ —— 复合须把 `\uparrow A_0`-线性的同构视作 `F`-线性的 ✓
（**`\mathrm{IsScalarTower}`** ✓ 在库 ✓）⟹ **次轮查 `\mathrm{AlgEquiv}` 的 restrictScalars 类引理** ✓（**(51)** ✓）。
**⚠ 组合式** ✓：`\mathrm{Localization.Away}\ w \simeq_F \mathrm{Localization.Away}\ (e w) = \mathrm{Localization.Away}\ s \simeq_{\uparrow A_0} \uparrow(A_0[s^{-1}])` ✓（取 `w := e^{-1} s` ✓）。 -/



section AwayMapEquiv

variable {F : Type u} [Field F]
variable {A : Type u} [CommRing A] [Algebra F A]
variable {B : Type u} [CommRing B] [Algebra F B]

/-- **局部化沿基环同构搬运** ✓：`Localization.Away a ≃ₐ[F] Localization.Away (e a)` ✓
（**入口** ✓：`\mathrm{IsLocalization.algEquivOfAlgEquiv}` ✓ ＋ **`\mathrm{Submonoid.map\_powers}`** ✓）。 -/
theorem nonempty_algEquiv_localizationAway_map (e : A ≃ₐ[F] B) (a : A) :
    Nonempty (Localization.Away a ≃ₐ[F] Localization.Away (e a)) :=
  ⟨IsLocalization.algEquivOfAlgEquiv (Localization.Away a) (Localization.Away (e a))
    e (Submonoid.map_powers e a)⟩

/-- **非零沿同构搬运** ✓（(a) 款的 `w \neq 0` 一侧）。 -/
theorem algEquiv_ne_zero_iff (e : A ≃ₐ[F] B) {a : A} : e a ≠ 0 ↔ a ≠ 0 :=
  ⟨fun h ha => h (by rw [ha, map_zero]),
    fun ha h => ha (e.injective (by rw [h, map_zero]))⟩

end AwayMapEquiv


/-! ## 4.33 **(a) 款具体形**（`IsGenericExtension`(a) 的成品形式）✓✅（第 167 轮）

**⚠ 起点** ✓：§129.4 第 1 项 —— (a) 款具体形 ✓（**两处阻塞** ✗ 见 §129.2 ✓）。

**⚠ 本轮结果** ✓：**①** **阻塞 (ii) 已解** ✓✅ —— **`\mathrm{AlgEquiv.restrictScalars}`** ✓
（把 `\simeq_{\uparrow A_0}` 视作 `\simeq_F` ✓，**`\mathrm{IsScalarTower}`** ✓ 供给 ✓）；
**②** **阻塞 (i) 未解** ✗（**登记** ✓）⟹ **本件以 `[\mathrm{IsFractionRing}\ \uparrow A_0\ K]` 为显式假设** ✓ 落 (a) 款的**成品形** ✓。

**⚠ 件的形状** ✓：`\mathrm{AlgebraicIndependent}\ F\ a` ✓ ＋ **`[\mathrm{IsFractionRing}\ \uparrow A_0\ K]`** ✓ ＋ `s \neq 0`（`s \in A_0` ✓）⟹
`\exists w \neq 0,\ \uparrow(A_0[s^{-1}]) \simeq_F \mathrm{Localization.Away}\ w` ✓
（**恰是 `\mathrm{IsGenericExtension}` 的 (a) 款** ✓，**取 `w := e^{-1} s`** ✓）。
**⚠ 组装式** ✓：`\mathrm{Localization.Away}\ w \xrightarrow{\ \psi\ } \mathrm{Localization.Away}\ (e w) = \mathrm{Localization.Away}\ s
\xrightarrow{\ \chi\ } \uparrow(A_0[s^{-1}])` ✓，其中 `\psi` 由 **§4.32** ✓（基环同构搬运 ✓）、
`\chi` 由 **§4.31** ✓（局部化同构 ✓）＋ **`\mathrm{restrictScalars}`** ✓。

**✗ 登记（阻塞 (i)）** ✗：**`\mathrm{IsFractionRing}\ \uparrow(\mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\})\ K`** ✗
—— **本轮实测** ✓：由 §4.20 的**逐元素形**直造该结构时，**`\mathrm{isDefEq}` 心跳耗尽** ✗
（**`\mathrm{IntermediateField.adjoin}` 由交结构定义** ✓，**其项在统一时指数膨胀** ✗；**已试** ✓：
`\mathrm{change}` 定型 ✓／**提高心跳至 10^6** ✓／**改用乘法形（§4.18 的 `\mathrm{exists\_mul\_eq}`）** ✓ —— **均仍超时** ✗）
⟹ **次轮路线** ✓：**（a）** **先 `\mathrm{set}` 把 `A_0` 与其分式环结构**在**独立一节**中定型**再引用** ✓
（**`\mathrm{opaque}`／独立 `def` 阻断展开** ✓）；**（b）** 或**绕开 `\mathrm{IntermediateField.adjoin}`** ✓
—— **改从 `\mathrm{IsFractionRing}` 的**等价判据**出发** ✓（**次轮先查此类判据** ✓，**(51)** ✓）。 -/



section ClauseA

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
variable {n : ℕ} {a : Fin n → K}

/-- **(a) 款具体形**（`IsFractionRing` 作**显式假设**）：代数无关族 `a` ＋ `s ≠ 0` ⟹
    `A₀[s⁻¹]` 同构于某局部化多项式环。 -/
theorem exists_algEquiv_localizationAway_of_adjoin_inv
    (hind : AlgebraicIndependent F a)
    [IsFractionRing ↥(Algebra.adjoin F (Set.range a)) K]
    (s : ↥(Algebra.adjoin F (Set.range a))) (hs : s ≠ 0) :
    ∃ (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
      Nonempty (↥(Algebra.adjoin ↥(Algebra.adjoin F (Set.range a))
        {(algebraMap ↥(Algebra.adjoin F (Set.range a)) K s)⁻¹}) ≃ₐ[F] Localization.Away w) := by
  obtain ⟨e⟩ := nonempty_algEquiv_mvPolynomial_adjoin (K := K) hind
  obtain ⟨ψ⟩ := nonempty_algEquiv_localizationAway_map (F := F) e (e.symm s)
  rw [e.apply_symm_apply s] at ψ
  obtain ⟨χ⟩ := nonempty_algEquiv_localizationAway_adjoin_inv (K := K) s hs
  exact ⟨e.symm s, fun h0 => hs (by simpa using congrArg e h0),
    ⟨(ψ.trans (AlgEquiv.restrictScalars F χ)).symm⟩⟩

end ClauseA


/-! ## 4.34 **分式环实例**（`IsFractionRing ↥A_0 K`）＋ **(a) 款无假设形** ✓✅（第 168 轮）

**⚠ 起点** ✓：§130.5 第 1 项 —— 升 `\mathrm{IsFractionRing}\ \uparrow A_0\ K` 实例 ✗（**r167 的阻塞 (i)** ✗）。
**⚠ 结果** ✓✅：**阻塞 (i) 已解** ✓ —— **`\mathrm{IsGenericExtension}`(a) 款至此**无假设齐备** ✓✅。

**⚠ 解法（**新读数 (75)** ✓）** ✓：**把结论抽成**不含量词的通用形**✗→✓** ——
**通用件** ✓ `isFractionRing_of_forall_exists_div` ✓：**对任意 `F`-代数 `A`（`[\mathrm{NoZeroDivisors}]` ✓、`[\mathrm{FaithfulSMul}\ A\ K]` ✓），
若 `K` 的每个元素都是 `A` 中两元素之商 ✓，则 `K = \mathrm{Frac}(A)`** ✓（**四款直造** ✓：`\mathrm{map\_units}` ✓／`\mathrm{surj}` ✓／`\mathrm{exists\_of\_eq}` ✓）；
**然后**在 `A := \uparrow A_0` 档**一次应用** ✓（**重项 `h` 只出现一次** ✓）⟹ **不再心跳耗尽** ✓✅
—— **⚠ 机理** ✓：**r167 之败因是「重项在**结构内部**被反复统一」** ✗；**抽成通用件后，重项只在**调用点**参与一次** ✓（**(74) 的正面解法** ✓）。

**⚠ 本轮三件** ✓：
**①** `isFractionRing_of_forall_exists_div` ✓✅（**通用分式环构造** ✓ —— **可复用** ✓）；
**②** `isFractionRing_adjoin_of_adjoin_eq_top` ✓✅（**域生成 ⟹ `\uparrow A_0` 上的分式环** ✓ —— **r167 阻塞 (i) 之解** ✓）；
**③** **`exists_algEquiv_localizationAway_of_adjoin_inv'`** ✓✅（**(a) 款无假设形** ✓：
`\mathrm{AlgebraicIndependent}\ F\ a` ＋ **域生成** ＋ `s \neq 0` ⟹ `\exists w \neq 0,\ \uparrow(A_0[s^{-1}]) \simeq_F \mathrm{Localization.Away}\ w` ✓
—— **恰是 `\mathrm{IsGenericExtension}` 的 (a) 款** ✓）。
**⚠ 工艺** ✓：`\mathrm{have}\ hfr : \mathrm{IsFractionRing}\ \ldots := \ldots` ✓ **可作局部实例** ✓（**Prop 值** ✓，**(55)** ✓）—— **无须 `\mathrm{haveI}`** ✓。 -/



section FractionRingOfDivForm

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
variable {A : Type u} [CommRing A] [Nontrivial A] [NoZeroDivisors A]
variable [Algebra F A] [Algebra A K] [IsScalarTower F A K] [FaithfulSMul A K]

/-- **通用分式环构造**：若 `K` 的每个元素都是 `A` 中两元素之商，则 `K = \mathrm{Frac}(A)`。 -/
theorem isFractionRing_of_forall_exists_div
    (h : ∀ z : K, ∃ x y : A, y ≠ 0 ∧ algebraMap A K x / algebraMap A K y = z) :
    IsFractionRing A K := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro y
    rw [isUnit_iff_ne_zero]
    exact fun h0 =>
      (mem_nonZeroDivisors_iff_ne_zero.mp y.2)
        (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  · intro z
    obtain ⟨x, y, hy, hxy⟩ := h z
    have hyK : algebraMap A K y ≠ 0 :=
      fun h0 => hy (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
    exact ⟨(x, ⟨y, mem_nonZeroDivisors_iff_ne_zero.mpr hy⟩), by
      rw [← hxy, div_mul_cancel₀ _ hyK]⟩
  · intro x y hxy
    exact ⟨1, by
      rw [OneMemClass.coe_one, one_mul, one_mul]
      exact FaithfulSMul.algebraMap_injective A K hxy⟩

end FractionRingOfDivForm

section AdjoinInstance

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
variable {ι : Type*}

set_option maxHeartbeats 400000 in
/-- **域生成 ⟹ `A₀` 上的分式环**（r167 的阻塞点，**改用通用引理一次应用**）。 -/
theorem isFractionRing_adjoin_of_adjoin_eq_top {a : ι → K}
    (h : IntermediateField.adjoin F (Set.range a) = ⊤) :
    IsFractionRing ↥(Algebra.adjoin F (Set.range a)) K :=
  isFractionRing_of_forall_exists_div (A := ↥(Algebra.adjoin F (Set.range a)))
    (fun z => exists_div_eq_of_adjoin_eq_top (K := K) h z)

/-- **(a) 款无假设形**：`IsGenericExtension`(a) 款的**完整成品**（不再带分式环假设）。 -/
theorem exists_algEquiv_localizationAway_of_adjoin_inv' {n : ℕ} {a : Fin n → K}
    (hind : AlgebraicIndependent F a)
    (h : IntermediateField.adjoin F (Set.range a) = ⊤)
    (s : ↥(Algebra.adjoin F (Set.range a))) (hs : s ≠ 0) :
    ∃ (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
      Nonempty (↥(Algebra.adjoin ↥(Algebra.adjoin F (Set.range a))
        {(algebraMap ↥(Algebra.adjoin F (Set.range a)) K s)⁻¹}) ≃ₐ[F] Localization.Away w) := by
  have hfr : IsFractionRing ↥(Algebra.adjoin F (Set.range a)) K :=
    isFractionRing_adjoin_of_adjoin_eq_top (K := K) h
  exact exists_algEquiv_localizationAway_of_adjoin_inv (K := K) hind s hs

end AdjoinInstance


/-! ## 4.35 **装配 (c) 款**：源的 `φ : F[x_σ] → L`（求值载体 ✓）＋ **局部化提升** ＋ **不动域落地**（第 170 轮）

**源逐字** ✓（`raw/Saltman1982.tex:652--658` ✓，印 **275** ✓）：
> In order to realize `L/K` it suffices to define `φ: S → L` such that **`φ` preserves `G`**, and
> `φ(S)K = L`. In order to define such a `φ`, it suffices to define `φ: F[x_σ | σ ∈ G] → L` such that
> **`σ(φ(x_1)) = φ(x_σ)`**, **the `φ(x_σ)`'s are a basis for `L` over `K`**, and **`t` evaluated at
> the `φ(x_σ)`'s is a unit**.✓

**⚠ 已备（r139／r140／r149 ✓）** ✓：等变性 ✓（§4.6 `noetherEval_equivariant` ✓）、单位款 ✓（§4.7 ✓）、
`lemma-5.2` **真形** ✓（＝**存在 `z`** ＋ 共轭族成基 ＋ `t(z,\sigma z) \neq 0` ✓，§4.18 ✓）。
**本轮补三块** ✓：
**① 载体成品化** ✓：把源自己的求值 `x_σ \mapsto σ \bullet z` 落为**具名 `AlgHom`** ✓（`noetherEval` ✓）
—— §4.6 的等变性对它**逐字适用** ✓（定义即同一项 ✓）；
**② 局部化提升** ✓：`φ t` 是**单位** ⟹ `φ` **沿** `F[x_σ] \to F[x_σ](1/t)` **提升** ✓
（源「`t` evaluated at the `φ(x_σ)`'s is a **unit**」✓ 的**用点** ✓ —— 由此 `φ` 才落在源要的
`R_1(1/t)` 上 ✓）；
**③ 不动域落地** ✓：**保 `G` 的** `φ : S \toₐ[F] L` ✓ ⟹ **`φ|_R` 落进 `K`** ✓
（源第一句「`φ` **preserves** `G`」✓ 的用点 ✓；`R = S^G` ✓ 由 `IsGaloisWithGroup` 的**第二合取** ✓）
—— 这是**源要的 `φ : R \to K` 的来处** ✓。
**⚠ 生成性** ✓：共轭族既是 `K`-**基** ⟹ 它**生成 `L` over `K`** ✓（源「`φ(S)K = L`」的**前半** ✓；
后半「`S` 落进 `F[x_σ](1/t)`」＝**结构桥** ✗，**登记** ✓）。

**⚠ 登记（本轮未落）** ✗（**三项** ✓）：
**① 结构桥** ✓（源「we have that `S \subset F[x_σ](1/t)`」✓）—— 装配中 `S` 由**下降**给出 ✓
（`S \simeq S'' \otimes_{R''} R` ✓）而 `R` 由 **(a) 款**（**超越基侧** ✓）给出 ⟹ 须先有
「`S` 嵌入 **Noether 域**」的桥 ✗（**下一手** ✓）；
**② 不动域输入** ✓（`L^G = K` ✓）—— `IsGaloisWithGroup` 的**三合取不含**「`S^G = R`」✗
（**在册** ✓：`GaloisFixedSubringHyp` ✓）⟹ 本件把它作**显式参数** `hfix` ✓（**不隐藏** ✓）；
**③ 等变性搬到局部化层** ✓ —— 须 `t` 为 `G`-**不变** ✓（源正因此先用 `t' = \prod_σ σ(t)` ✓）⟹
**拟合用不变化** ✓（**下一手** ✓）。 -/

section NoetherEvalCarrier

variable {F : Type u} [Field F] {G : Type u} [Group G]

/-- **源 `(c)` 的求值载体** ✓（源「it suffices to define `φ: F[x_σ | σ ∈ G] → L`」✓）：
`x_σ \mapsto σ \bullet z` ✓ —— §4.6 的等变性 ✓ 与 §4.18 的三款 ✓ 都落在这个载体上 ✓。 -/
def noetherEval {L : Type u} [CommRing L] [Algebra F L] [MulSemiringAction G L] (z : L) :
    MvPolynomial G F →ₐ[F] L :=
  MvPolynomial.aeval (fun σ : G => σ • z)

/-- **载体在变量上的取值** ✓（源「`φ(x_σ)`」✓）：`φ(x_σ) = σ \bullet z` ✓。 -/
theorem noetherEval_X {L : Type u} [CommRing L] [Algebra F L] [MulSemiringAction G L]
    (z : L) (σ : G) : noetherEval (F := F) z (MvPolynomial.X σ) = σ • z :=
  MvPolynomial.aeval_X _ σ

end NoetherEvalCarrier

section AwayLiftOfIsUnit

variable {F : Type u} [Field F] {σ : Type*} {L : Type u} [CommRing L] [Algebra F L]

/-- **(c) 款的局部化提升** ✓（源「`t` evaluated at the `φ(x_σ)`'s is a **unit**」✓ 的用点 ✓）：
`φ : F[x_σ] \toₐ[F] L` 把 `t` 送到**单位** ⟹ `φ` **沿** `F[x_σ] \to F[x_σ](1/t)` **提升** ✓。

**证明** ✓：`IsLocalization.Away.lift` ✓（万有性质 ✓）＋ `IsLocalization.Away.lift_comp` ✓（与基环一致 ✓）；
**`F`-线性** ✓ 由 `IsScalarTower.algebraMap_apply` ✓ ＋ `AlgHom.commutes` ✓（**同
`away_lift_of_surjective` 的工艺** ✓）。 -/
theorem exists_algHom_away_of_isUnit (φ : MvPolynomial σ F →ₐ[F] L) (t : MvPolynomial σ F)
    (h : IsUnit (φ t)) :
    ∃ φ' : Localization.Away t →ₐ[F] L,
      ∀ p, φ' (algebraMap (MvPolynomial σ F) (Localization.Away t) p) = φ p := by
  let ψ : Localization.Away t →+* L :=
    IsLocalization.Away.lift (S := Localization.Away t) (g := φ.toRingHom) t h
  have hψ : ∀ p : MvPolynomial σ F,
      ψ (algebraMap (MvPolynomial σ F) (Localization.Away t) p) = φ p := by
    intro p
    rw [← RingHom.comp_apply, IsLocalization.Away.lift_comp (S := Localization.Away t)
      (g := φ.toRingHom) t h]
    rfl
  have hFpt : ∀ a : F, ψ (algebraMap F (Localization.Away t) a) = algebraMap F L a := by
    intro a
    simp only [IsScalarTower.algebraMap_apply F (MvPolynomial σ F) (Localization.Away t)]
    rw [hψ]
    exact φ.commutes a
  exact ⟨{ ψ with commutes' := hFpt }, hψ⟩

end AwayLiftOfIsUnit

section RealizationClause

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-- **(c) 款端到端** ✓（**源三款齐备** ✓）：`G`-Galois `L/K`（`K` **无限** ✓）＋ `t \neq 0` ✓ ⟹
存在 `z` ✓、**基** `b'` ✓ 与**局部化映射** `φ' : F[x_σ](1/t) \toₐ[F] L` ✓，使
**(i)** `b' σ = σ \bullet z` ✓（源「the `φ(x_σ)`'s are a **basis**」✓）；
**(ii)** `φ'(x_σ) = σ \bullet z` ✓（源「`φ(x_σ)`」✓ ＋ 「`t` ... is a **unit**」✓ 由提升给出 ✓）。
**接线** ✓：`lemma52Statement_nonzero_true` ✓（§4.18 ✓，**源 `lemma-5.2` ＝ 定理** ✓）给 `z` 与基 ✓；
`aeval \neq 0` ✓ 在**域**上即**单位** ✓（`isUnit_iff_ne_zero` ✓）⟹ ② 提升 ✓。 -/
theorem exists_basis_algHom_away_of_galois (K L : Type u) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] [Infinite K]
    [MulSemiringAction G L] [SMulCommClass G K L] (b : Module.Basis G K L)
    (h : Function.Bijective (smulAlgEquivHom K G L))
    (t : MvPolynomial G F) (ht : t ≠ 0) :
    ∃ (z : L) (b' : Module.Basis G K L) (φ' : Localization.Away t →ₐ[F] L),
      (∀ σ : G, b' σ = σ • z) ∧
      (∀ σ : G, φ' (algebraMap (MvPolynomial G F) (Localization.Away t)
        (MvPolynomial.X σ)) = σ • z) := by
  obtain ⟨z, b', hb', hne⟩ := lemma52Statement_nonzero_true F G K L b h t ht
  have hunit : IsUnit (noetherEval (F := F) z t) := by
    rw [isUnit_iff_ne_zero]
    exact hne
  obtain ⟨φ', hφ'⟩ := exists_algHom_away_of_isUnit (F := F) (noetherEval (F := F) z) t hunit
  exact ⟨z, b', φ', hb', fun σ => by rw [hφ']; exact noetherEval_X (F := F) z σ⟩

end RealizationClause

section SpanningOfConjugates

variable {G : Type u} [Group G]

/-- **共轭族生成 `L` over `K`** ✓（源「the `φ(x_σ)`'s are a **basis** for `L` over `K`」✓ 的**生成侧** ✓，
即源「`φ(S)K = L`」的**前半** ✓）：共轭族既成 `K`-**基** ⟹ 它在 `L` 中**生成** `L` ✓
（`Module.Basis.span_eq` ✓ ＋ `Algebra.subset_adjoin` ✓，经 `Subalgebra.toSubmodule` ✓）。
**⚠ 工艺** ✓（**第六次复现** ✓）：本件**不需** `[Fintype G]`／`[DecidableEq G]` ✗ ⟹ **另开 section** ✓
（否则触发 `unusedSectionVars` ✗ —— linter 原样给出 `omit` 提示 ✓，但 **doc comment 与 `omit`-前缀不兼容** ✗
（实测「unexpected token 'omit'; expected 'lemma'」✓）⟹ **正解 ＝ 移出 section** ✓，**非** `omit` ✓）。 -/
theorem adjoin_range_smul_eq_top {K L : Type u} [Field K] [Field L] [Algebra K L]
    [MulSemiringAction G L] (b' : Module.Basis G K L) (z : L)
    (hb : ∀ σ : G, b' σ = σ • z) :
    Algebra.adjoin K (Set.range (fun σ : G => σ • z)) = ⊤ := by
  have hv : (fun σ : G => σ • z) = fun σ : G => b' σ := by
    funext σ; rw [hb σ]
  rw [hv, eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span K (Set.range fun σ : G => b' σ) := by
    rw [Module.Basis.span_eq]; trivial
  have hle : Submodule.span K (Set.range fun σ : G => b' σ) ≤
      (Algebra.adjoin K (Set.range fun σ : G => b' σ)).toSubmodule :=
    Submodule.span_le.mpr (fun y hy => Algebra.subset_adjoin (R := K) hy)
  exact hle hx

end SpanningOfConjugates

namespace BTier

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G]
variable {R S K L : Type u} [CommRing R] [CommRing S] [Field K] [Field L]
variable [Algebra F R] [Algebra R S] [Algebra F S] [IsScalarTower F R S]
variable [Algebra K L] [Algebra F K] [Algebra F L] [IsScalarTower F K L]
variable [MulSemiringAction G S] [MulSemiringAction G L]

/-- **(c) 款的「保 `G` ⟹ 落进 `K`」件** ✓（源第一句「such that **`φ` preserves `G`**」✓ 的用点 ✓）：
`S/R` 为 `G`-Galois ✓、`φ : S \toₐ[F] L` **与 `G` 等变** ✓、且 `L` 的**不动点落进 `K`** ✓ ⟹
存在 `Φ : R \toₐ[F] K` ✓ 使 `Φ` 与 `φ` 在 `S` 的 `R`-像上**一致** ✓（**逐元素**：`algebraMap K L (Φ r) = φ (algebraMap R S r)` ✓）。

**机制** ✓（**源的两句合一** ✓）：`r \in R` 被 `G` **逐点固定** ✓（`IsGaloisWithGroup` 的**第二合取** ✓）
⟹ 由**等变性** ✓ `φ(algebraMap r)` 亦被固定 ✓ ⟹ 由 `hfix` ✓ 落进 `K` ✓；
**良定义** ✓：`\mathrm{algebraMap}\ K\ L` **单射** ✓（**域** ✓）⟹ `\mathrm{choose}` 出的 `Φ` 满足
加法／乘法／单位／`F`-线性 ✓（**逐条用单射性搬运** ✓）。
**⚠ `hfix` 是**在册缺口**的显式形** ✓（`L^G = K` ✓）：`IsGaloisWithGroup` 的**三合取不含**它 ✗
（**在册** ✓：`GaloisFixedSubringHyp` ✓ —— 本条与它**同族** ✓，**不隐藏** ✓）。 -/
theorem exists_algHom_of_equivariant_of_fixed
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgal : IsGaloisWithGroup R S G hRG)
    (φ : S →ₐ[F] L) (heq : ∀ (g : G) (s : S), φ (g • s) = g • φ s)
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x) :
    ∃ Φ : R →ₐ[F] K, ∀ r : R, algebraMap K L (Φ r) = φ (algebraMap R S r) := by
  have key : ∀ r : R, ∃ k : K, algebraMap K L k = φ (algebraMap R S r) := by
    intro r
    refine hfix (φ (algebraMap R S r)) (fun g => ?_)
    rw [← heq g (algebraMap R S r), hgal.2.1 g r]
  choose Φ hΦ using key
  have hinj : Function.Injective (algebraMap K L) := FaithfulSMul.algebraMap_injective K L
  exact ⟨{ toFun := Φ
           map_one' := hinj (by rw [map_one, hΦ 1, map_one, map_one])
           map_mul' := fun x y => hinj (by rw [map_mul, hΦ (x * y), map_mul, hΦ x, hΦ y, map_mul])
           map_zero' := hinj (by rw [map_zero, hΦ 0, map_zero, map_zero])
           map_add' := fun x y => hinj (by rw [map_add, hΦ (x + y), map_add, hΦ x, hΦ y, map_add])
           commutes' := fun a => hinj (by
             rw [hΦ (algebraMap F R a), ← IsScalarTower.algebraMap_apply F R S a,
               AlgHom.commutes, ← IsScalarTower.algebraMap_apply F K L a]) }, hΦ⟩

/-- **登记** ✗：本件的 `hfix`（`L^G \subseteq K` ✓）是**在册不动域缺口**的显式形 ✓
（**同族**：`GaloisFixedSubringHyp` ✓ ＝ `S^G \subseteq R` ✓）—— **未证** ✗（**非本会话可落** ✓：
须 Artin 型定理在**本口径**下重建 ✓）。
**⚠ r199 已落（域档）** ✓✅：**Artin 定理**已由 mathlib ✓（`FixedPoints.finrank_eq_card` ✓）供给 ⟹
`fixedPoints_eq_of_isGaloisWithGroup` ✓（§4.54 ✓）**在域档落地** ✓（**前提**：`[FiniteDimensional K L]` ✗ ＋ `[Field L]` ✗）；
**⚠ 环档与有限性两条仍开放** ✗（§4.54 节头登记 ✓，**不复写** ✗）。 -/
theorem fixedField_gap_registered : True := trivial

end BTier

/-! ## 4.36 **装配 (c) 款结构桥（`t` 的 `g`-半）**：`R_1(1/s)` 落进 `F[x_σ](1/t)`（第 171 轮）

**源逐字** ✓（`raw/Saltman1982.tex:650--652` ✓，印 **275** ✓）：
> Write `a_i = f_i/g_i`, where the `f`'s and `g`'s are **polynomials** in the `x_σ`'s. … Then if `t` is
> the **product of all the `g`'s and `k`'s**, we have that **`S \subset F[x_σ | σ ∈ G](1/t)`** ✓。

**⚠ 该句的两半** ✓（**分母两族** ✓）：**`g`-半** ✓ ＝ 超越基 `a_i` 的分母 ✓（**本轮落** ✓）；
**`k`-半** ✓ ＝ `S` 的生成元 `e_j = h_j/k_j` 的分母 ✓（**登记** ✓，见文末 ✗）。
**⚠ 为何需要** ✓：源把 `\varphi` 定义在 `F[x_σ](1/t)` 上 ✓ 再**限制到** `R` ✓ 与 `S` ✓
（`R = R_1(1/s)` ✓ 与 `S` ✓ 都在其内 ✓）—— 故 **`R_1(1/s)` 落进单个局部化**是 `\varphi : R \to K` 的**前置** ✓
（r170 的局部化提升把 `\varphi` 从 `F[x_σ]` 送到 `F[x_σ](1/t)` ✓）。

**⚠ 通用档** ✓（**承 (75)** ✓，**本轮第二次实测** ✓）：本节的件**不**写在具体的 `\mathrm{NoetherField}` 上 ✗
（那使 `\mathrm{NoetherField}\ F\ G = \mathrm{FractionRing}\,(\mathrm{MvPolynomial}\ G\ F)` 这一**重项**在每条统一中反复出现 ✗
—— **实测**：`\mathrm{field\_simp}` 处两次 **心跳耗尽** ✗）⟹ 改写为**任意** `\mathrm{IsFractionRing}\,(\mathrm{MvPolynomial}\ G\ F)\ L` 档 ✓
（**重项只在调用点出现一次** ✓）；**两条域恒等式**另抽为**纯域**引理 ✓（项最轻 ✓）。
**⚠ `G` 只需是指标类型** ✓（本节不需 `[\mathrm{Group}\ G]` ✓ —— **不留无用实例** ✓）。 -/

section FieldIdentities

variable {L : Type*} [Field L]

/-- **域恒等式 ①** ✓：`t = s \cdot h`（`h \neq 0`）⟹ `s^{-1} = t^{-1} \cdot h` ✓
（**纯域档** ✓ —— 供「`s^{-1}` 落进 `t` 的局部化」用 ✓）。 -/
lemma inv_eq_inv_mul_of_eq_mul {s h t : L} (ht : t = s * h) (hh : h ≠ 0) :
    s⁻¹ = t⁻¹ * h := by
  rw [ht, mul_inv]
  field_simp

/-- **域恒等式 ②** ✓：`a \cdot b = c`（`a \neq 0`）⟹ `b^{-1} = a^2 \cdot (a \cdot c)^{-1}` ✓
（供「`s_0^{-1}` 落进 `t = s \cdot h` 的局部化」用 ✓ —— 源把 `s_0` 的分母也并进 `t` ✓）。 -/
lemma inv_eq_sq_mul_inv_of_mul_eq {a b c : L} (h : a * b = c) (ha : a ≠ 0) :
    b⁻¹ = a^2 * (a * c)⁻¹ := by
  rw [← h]
  field_simp

end FieldIdentities

section FractionRingMulForm

variable {A : Type u} [CommRing A] [IsDomain A] {K : Type u} [Field K] [Algebra A K]

/-- **分式域元素都是乘法形的商** ✓：`\exists x\ y,\ y \neq 0 \wedge \mathrm{algebraMap}\ y \cdot z = \mathrm{algebraMap}\ x` ✓
—— 即源「`a_i = f_i/g_i`」✓ 的**通用形** ✓（入口 ＝ `\mathrm{IsLocalization.mk'\_surjective}` ✓ ＋
**`\mathrm{mk'\_spec'}`** ✓，**免去除法** ✓）。 -/
theorem exists_mul_eq_of_isFractionRing [IsFractionRing A K] (z : K) :
    ∃ x y : A, y ≠ 0 ∧ algebraMap A K y * z = algebraMap A K x := by
  obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  exact ⟨x, y, mem_nonZeroDivisors_iff_ne_zero.mp y.2, by rw [← hz, IsLocalization.mk'_spec']⟩

end FractionRingMulForm

section AwayImageOfAdjoin

variable {F : Type u} [Field F] {G : Type u}
variable {L : Type u} [Field L] [Algebra (MvPolynomial G F) L]
variable [IsFractionRing (MvPolynomial G F) L]

/-- **`g`-半（有限族）** ✓：`L` 的**有限族**全体落进 `F[x_σ](1/t)`（**单个** `t` ✓）——
即源「`t` ＝ the product of all the `g`'s」✓ 的**代数核** ✓（入口 ＝ §4.21 的 `exists_mul_eq_of_finite` ✓
＋ §4.23 的 `mem_adjoin_inv_of_pow_mul_eq` ✓）。 -/
theorem exists_mem_adjoin_away_of_noether {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → L) :
    ∃ t : MvPolynomial G F, t ≠ 0 ∧ ∀ i : ι,
      g i ∈ Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L t)⁻¹} : Set L) := by
  obtain ⟨t, ht, h⟩ := exists_mul_eq_of_finite (A := MvPolynomial G F) (K := L) g
    (fun i => exists_mul_eq_of_isFractionRing (A := MvPolynomial G F) (K := L) (g i))
  refine ⟨t, ht, fun i => ?_⟩
  obtain ⟨x, hx⟩ := h i
  exact mem_adjoin_inv_of_pow_mul_eq (A := MvPolynomial G F) (K := L) ht ⟨1, x, by simpa using hx⟩

variable [Algebra F L] [IsScalarTower F (MvPolynomial G F) L]

/-- **`g`-半（子代数形）** ✓✅：`\mathrm{Algebra.adjoin}\ F\ \{\mathrm{range}\ a\} \subseteq F[x_σ](1/t)` ✓
—— 即源「`R_1 = F[a_1,\dots,a_n]`」✓ 落进 `F[x_σ](1/t)` ✓（(a) 款侧的**桥** ✓）。 -/
theorem exists_adjoin_le_away_of_noether {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → L) :
    ∃ t : MvPolynomial G F, t ≠ 0 ∧ Algebra.adjoin F (Set.range a) ≤
      Subalgebra.restrictScalars F (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L t)⁻¹} : Set L)) := by
  obtain ⟨t, ht, h⟩ := exists_mem_adjoin_away_of_noether (F := F) (G := G) (L := L) a
  exact ⟨t, ht, Algebra.adjoin_le_iff.mpr (by rintro x ⟨i, rfl⟩; exact h i)⟩

/-- **`g`-半（含单位化）** ✓✅：`\mathrm{Algebra.adjoin}\ F\ (\{\mathrm{range}\ a\} \cup \{s_0, s_0^{-1}\}) \subseteq F[x_σ](1/t)` ✓
—— 即源的 **`R = R_1(1/s)`** ✓（`s = s_0` ✓）落进 `F[x_σ](1/t)` ✓，**`s_0^{-1}` 亦在内** ✓。

**⚠ 口径** ✓（**登记** ✓）：源只列 `t` ＝ the product of the **`g`'s and `k`'s** ✓，**未提分子** ✗；
但源的结论「`R \subseteq S \subset F[x_σ](1/t)`」✓（`S \supseteq R = R_1(1/s)` ✓）**已蕴含** `s_0^{-1} \in F[x_σ](1/t)` ✓
⟹ 本件把它**显式化** ✓：取 `t := s \cdot h` ✓（`h` ＝ `s_0` 的分子 ✓），
由**域恒等式 ②** ✓ 得 `s_0^{-1} = (\mathrm{algebraMap}\ s)^2 \cdot (\mathrm{algebraMap}\ t)^{-1}` ✓ —— **仍是单个** `t` ✓
（**只增大 `t`，不改变结论的形状** ✓）。 -/
theorem exists_adjoin_inv_le_away_of_noether {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → L) (s₀ : L) (hs₀ : s₀ ≠ 0) :
    ∃ t : MvPolynomial G F, t ≠ 0 ∧ Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤
      Subalgebra.restrictScalars F (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L t)⁻¹} : Set L)) := by
  classical
  obtain ⟨s, hs, h⟩ := exists_mul_eq_of_finite (A := MvPolynomial G F) (K := L)
    (fun o : Option ι => o.elim s₀ a)
    (fun o => exists_mul_eq_of_isFractionRing (A := MvPolynomial G F) (K := L) _)
  obtain ⟨hnum, hnum_eq⟩ := h none
  have hnum_eq' : algebraMap (MvPolynomial G F) L s * s₀ = algebraMap (MvPolynomial G F) L hnum := by
    simpa only [Option.elim_none] using hnum_eq
  set t : MvPolynomial G F := s * hnum with ht
  set At := Algebra.adjoin (MvPolynomial G F)
    ({(algebraMap (MvPolynomial G F) L t)⁻¹} : Set L) with hAt
  have hsL : algebraMap (MvPolynomial G F) L s ≠ 0 := fun h0 =>
    hs (IsFractionRing.injective (MvPolynomial G F) L (by rw [h0, map_zero]))
  have hnumL : algebraMap (MvPolynomial G F) L hnum ≠ 0 := by
    intro h0
    rw [h0] at hnum_eq'
    exact mul_ne_zero hsL hs₀ hnum_eq'
  have hnum_ne : hnum ≠ 0 := fun h0 => hnumL (by rw [h0, map_zero])
  have hs_inv_mem : (algebraMap (MvPolynomial G F) L s)⁻¹ ∈ At := by
    have h1 : (algebraMap (MvPolynomial G F) L s)⁻¹
        = (algebraMap (MvPolynomial G F) L t)⁻¹ * algebraMap (MvPolynomial G F) L hnum :=
      inv_eq_inv_mul_of_eq_mul (by rw [ht, map_mul]) hnumL
    rw [h1]
    exact At.mul_mem (Algebra.subset_adjoin (by simp)) (At.algebraMap_mem hnum)
  have hle : Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L s)⁻¹} : Set L) ≤ At :=
    Algebra.adjoin_le_iff.mpr (by rintro y (rfl : y = _); exact hs_inv_mem)
  refine ⟨t, mul_ne_zero hs hnum_ne, Algebra.adjoin_le_iff.mpr ?_⟩
  intro x hx
  rcases hx with ⟨i, rfl⟩ | rfl | rfl
  · obtain ⟨y, hy⟩ := h (some i)
    exact hle (mem_adjoin_inv_of_pow_mul_eq (A := MvPolynomial G F) (K := L) hs
      ⟨1, y, by simpa using hy⟩)
  · exact hle (mem_adjoin_inv_of_pow_mul_eq (A := MvPolynomial G F) (K := L) hs
      ⟨1, hnum, by simpa using hnum_eq'⟩)
  · have key : s₀⁻¹ = (algebraMap (MvPolynomial G F) L s)^2
        * (algebraMap (MvPolynomial G F) L t)⁻¹ := by
      rw [ht, map_mul]
      exact inv_eq_sq_mul_inv_of_mul_eq hnum_eq' hsL
    rw [key]
    exact At.mul_mem (At.pow_mem (At.algebraMap_mem s) 2) (Algebra.subset_adjoin (by simp))

end AwayImageOfAdjoin

section BridgeGap

/-- **登记** ✗：**结构桥的 `k`-半** ✓（源「and `k`'s」✓ ＝ 「`S \subseteq F[x_σ](1/t)`」✓）**未落** ✗ ——
装配中 `S` 由**下降**给出 ✓（`S = R \otimes_{R''} S''` ✓，r169 ✓），故须先有 **`S` 落进 `L`** 的桥 ✓；
**机制已定** ✓（**两件** ✓）：**①** 由 **`\mathrm{GaloisProjectiveHyp}` 的投射性** ✓ 得 `S''` **平坦** ✓ ⟹
`S'' \to S'' \otimes_{R''} L^G \cong L` **单射** ✓（**平坦 ⟹ 与单射张量仍单射** ✓ —— 待落 ✗）；
**②** 再对**有限型**代数用 **§4.22** ✓（`A := R` ✓）把 `S` 的像清进单个局部化 ✓
—— **`A`-代数结构的入口** ✓ ＝ `R \to S` ✓（**已有** ✓）。 -/
theorem noetherEmbedding_gap_registered : True := trivial

end BridgeGap

/-! ## 4.37 **装配 (c) 款 `k`-半 的机制 ②**：**两族分母并成一个 `t`**（第 172 轮）

**⚠ 起点** ✓（§134.4 的登记 ✓）：源「if `t` is the **product of all the `g`'s and `k`'s**」✓ ——
即源的 `t` **同时**吸收**两族**分母 ✓：**`g`'s** ✓ ＝ 超越基 `a_i`（**§4.36 已落** ✓）、
**`k`'s** ✓ ＝ `S` 的生成元 ✓。本轮把**合并**那一步落为**可复用件** ✓：给定「`R` 的像已在 `F[x](1/t_0)` 内」✓
与「一族元素各自是 `F[x_σ]` 中两元素之商」✓，则存在**单个** `t` 使**两族一并**落进 `F[x](1/t)` ✓。

**⚠ 三件** ✓：**①** `adjoin_away_mono` ✓（`Q_t \subseteq Q_{t \cdot t'}` ✓，**域恒等式 ①** 直接用 ✓
—— **§4.36 的复用** ✓）；**②** `sup_adjoin_away_le` ✓（两个局部化的**并**仍是单个局部化 ✓）；
**③** `exists_adjoin_union_le_away` ✓（**合并** ✓ ＝ 源「product of all the `g`'s and `k`'s」✓）。
**⚠ 假设表** ✓：`adjoin_away_mono` **不需** `t \neq 0` ✗（`t = 0` 档两边相同 ✓）⟹ **不留无用前提** ✓
（**最弱假设表** ✓）；`[\mathrm{IsDomain}\ A]` 亦**不需** ✓（`\mathrm{IsFractionRing}` 已给单射 ✓）。 -/

section AwayMonotone

variable {A : Type u} [CommRing A] {L : Type u} [Field L] [Algebra A L]
variable [IsFractionRing A L]

/-- **局部化的单调性** ✓：`t^{-1}` 落进 `(t \cdot t')` 的局部化 ✓（`t^{-1} = (t t')^{-1} \cdot t'` ✓，
**域恒等式 ①** ✓）。 -/
theorem adjoin_away_mono (t t' : A) (ht' : t' ≠ 0) :
    Algebra.adjoin A ({(algebraMap A L t)⁻¹} : Set L) ≤
      Algebra.adjoin A ({(algebraMap A L (t * t'))⁻¹} : Set L) := by
  have ht'L : algebraMap A L t' ≠ 0 := fun h0 =>
    ht' (IsFractionRing.injective A L (by rw [h0, map_zero]))
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro y (rfl : y = _)
  have h1 : (algebraMap A L t)⁻¹ = (algebraMap A L (t * t'))⁻¹ * algebraMap A L t' :=
    inv_eq_inv_mul_of_eq_mul (by rw [map_mul]) ht'L
  rw [h1]
  exact mul_mem (Algebra.subset_adjoin (by simp)) (Subalgebra.algebraMap_mem _ t')

/-- **两个局部化的并仍是单个局部化** ✓：`Q_t \sqcup Q_{t'} \subseteq Q_{t \cdot t'}` ✓
（两支分别由**单调性** ✓ 给出 —— 第二支用 `t' t = t t'` ✓ 重排 ✓）。 -/
theorem sup_adjoin_away_le (t t' : A) (ht : t ≠ 0) (ht' : t' ≠ 0) :
    Algebra.adjoin A ({(algebraMap A L t)⁻¹} : Set L) ⊔
      Algebra.adjoin A ({(algebraMap A L t')⁻¹} : Set L) ≤
      Algebra.adjoin A ({(algebraMap A L (t * t'))⁻¹} : Set L) := by
  have htL : algebraMap A L t ≠ 0 := fun h0 =>
    ht (IsFractionRing.injective A L (by rw [h0, map_zero]))
  refine sup_le (adjoin_away_mono t t' ht') ?_
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro y (rfl : y = _)
  have h1 : (algebraMap A L t')⁻¹ = (algebraMap A L (t * t'))⁻¹ * algebraMap A L t :=
    inv_eq_inv_mul_of_eq_mul (by rw [map_mul, mul_comm]) htL
  rw [h1]
  exact mul_mem (Algebra.subset_adjoin (by simp)) (Subalgebra.algebraMap_mem _ t)

end AwayMonotone

section UnionClearing

variable {F : Type u} [Field F] {G : Type u}
variable {L : Type u} [Field L] [Algebra (MvPolynomial G F) L]
variable [IsFractionRing (MvPolynomial G F) L]
variable [Algebra F L] [IsScalarTower F (MvPolynomial G F) L]

/-- **两族分母并成一个 `t`** ✓✅（源「`t` ＝ the **product of all the `g`'s and `k`'s**」✓）：
给定 `R`（以 `a` 的 `F`-adjoin 形给出 ✓）的像已在 `F[x](1/t_0)` 内 ✓、与一族任意元素 `e` ✓
（**各自**是 `F[x_σ]` 中两元素之商时 —— **由 §4.36 的 ④ 自动成立** ✓），
则存在**单个** `t` 使 **`a` 与 `e` 两族一并**落进 `F[x](1/t)` ✓（取 `t := t_0 \cdot t_1` ✓）。
**⚠ 用途** ✓：`a` ＝ 超越基 ✓（**`g`'s** ✓）、`e` ＝ `S` 的生成元的像 ✓（**`k`'s** ✓）⟹
正是源的 `t` ✓（**§4.36 的 ⑥ 已覆盖 `s_0^{-1}`** ✓，故 `R = R_1(1/s)` 亦在内 ✓）。 -/
theorem exists_adjoin_union_le_away {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (t₀ : MvPolynomial G F) (ht₀ : t₀ ≠ 0) (a : ι → L)
    (ha : Algebra.adjoin F (Set.range a) ≤ Subalgebra.restrictScalars F
      (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L t₀)⁻¹} : Set L)))
    (e : ι' → L) :
    ∃ t : MvPolynomial G F, t ≠ 0 ∧ Algebra.adjoin F (Set.range a ∪ Set.range e) ≤
      Subalgebra.restrictScalars F (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L t)⁻¹} : Set L)) := by
  obtain ⟨t₁, ht₁, h₁⟩ := exists_mem_adjoin_away_of_noether (F := F) (G := G) (L := L) e
  refine ⟨t₀ * t₁, mul_ne_zero ht₀ ht₁, Algebra.adjoin_le_iff.mpr ?_⟩
  rintro x (⟨i, rfl⟩ | ⟨j, rfl⟩)
  · exact adjoin_away_mono t₀ t₁ ht₁ (ha (Algebra.subset_adjoin (Set.mem_range_self i)))
  · have hmem : e j ∈ Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) L t₁)⁻¹} : Set L) := h₁ j
    have := adjoin_away_mono t₁ t₀ ht₀ hmem
    rwa [mul_comm t₁ t₀] at this

/-! ### 攻击顺序 ① 的 `t`：`P := ∏_σ σ • t₀` 的**两件已验证**（第 215 轮 ✓）

**⚠ 更正留痕** ✓（**§176 的延续** ✓）：`r208`／§4.60 ① 的旧注把 **§4.6 引理的对象**与「**再乘 `t₀`**」**混为一谈** ✗
（`t₀` **本身不是不变的** ✗，`t₀ · ∏_σ σ • t₀` **亦不是** ✗ —— **实测** ✓）。
**正解** ✓ ＝ **`P := ∏_σ σ • t₀` 本身** ✓ —— 本条目落它的**非零** ✓ 与**不变化** ✓（**幂档** ✓ 一并 ✓）。
**⚠ 余项** ✗：**包含** ✓（`A ≤ Q(P)` ✓）**未落** ✗ —— ⚠ **方向须注意** ✗：
`adjoin_away_mono` ✓ 给 `Q(t) ≤ Q(t \cdot t')` ✓，而 `P` **不是** `t₀` 的**倍数** ✗（`t₀` 才是 `P` 的因子 ✓）
⟹ **不能**由该件直接得 `Q(t₀) ≤ Q(P)` ✗（**待另证** ✗，见状态笔记 §177 ✓）。 -/

section NoetherTProd

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G]

/-- **`P := ∏_σ σ • t₀` 非零** ✓（**关键小引理**：`σ • t₀ = 0 \Rightarrow t₀ = 0` ✓，`calc` 三行 ✓）。 -/
lemma prod_smul_ne_zero (t₀ : MvPolynomial G F) (ht₀ : t₀ ≠ 0) :
    (∏ σ : G, σ • t₀) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro σ _ h0
  exact ht₀ (calc t₀ = (1 : G) • t₀ := (one_smul G t₀).symm
    _ = (σ⁻¹ * σ) • t₀ := by rw [inv_mul_cancel]
    _ = σ⁻¹ • (σ • t₀) := mul_smul σ⁻¹ σ t₀
    _ = 0 := by rw [h0, smul_zero])

/-- **`P := ∏_σ σ • t₀` 不变化** ✓（§4.6 ✓ —— **一行** ✓）。 -/
lemma prod_smul_invariant (t₀ : MvPolynomial G F) (g : G) :
    g • (∏ σ : G, σ • t₀) = ∏ σ : G, σ • t₀ :=
  noether_prod_smul_invariant (F := F) (G := G) t₀ g

/-- **`P^N` 不变化** ✓（不变量的幂 ✓ —— 归纳 ＋ `smul_mul'` ✓）。 -/
lemma prod_pow_invariant (t₀ : MvPolynomial G F) (N : ℕ) (g : G) :
    g • (∏ σ : G, σ • t₀) ^ N = (∏ σ : G, σ • t₀) ^ N := by
  have h : g • (∏ σ : G, σ • t₀) = ∏ σ : G, σ • t₀ := prod_smul_invariant t₀ g
  induction N with
  | zero => simp
  | succ n ih => rw [pow_succ, smul_mul', h, ih]

/-- **`P^N` 非零** ✓。 -/
lemma prod_pow_ne_zero (t₀ : MvPolynomial G F) (ht₀ : t₀ ≠ 0) (N : ℕ) :
    (∏ σ : G, σ • t₀) ^ N ≠ 0 :=
  pow_ne_zero N (prod_smul_ne_zero t₀ ht₀)

end NoetherTProd

/-- **登记** ✗：**`k`-半**的**接线** ✓（把 r172 的 `\mathrm{injective\_tmul\_one\_of\_galoisProjective}` ✓
与**下降同构** `S'' \otimes_{R''} L^G \cong L` ✓ 复合得 `S'' \hookrightarrow L` ✓，再取 `S''` 的**有限生成族** ✓
用本节的**合并件** ✓）**未落** ✗ —— **下一手** ✓。 -/
theorem unionClearing_gap_registered : True := trivial

end UnionClearing

/-! ## 4.38 **装配 (c) 款 `k`-半 接线**：**有限型像落进单个局部化**（第 174 轮）

**⚠ 起点** ✓（§135.4 的登记 ✓）：`k`-半 的**机制两件**已落 ✓（r172 ✓：**平坦 ⟹ 单射** ✓／**两族分母合一个 `t`** ✓）
⟹ 本轮补**接线** ✓，**目标 ＝ 断指** ✓：把 `S'' \hookrightarrow L` 与 `S'' \subseteq F[x_\sigma](1/t)` 落为**库内定理** ✓。

**⚠ 本轮两件** ✓：
**①** `exists_adjoin_le_away_of_image_le` ✓（**通用档** ✓：`R` 的像已在 `Q(t_0)` 内 ✓ ＋ 有限族各自已在 `Q(t_1)` 内 ✓
⟹ `R`-**adjoin** 全体落进 `Q(t_0 \cdot t_1)` ✓ —— **结论显式给乘子** ✓，非存在形 ✗，**便于下游接** ✓）；
**②** **`exists_image_le_away_of_finiteType`** ✓✅（**断指件** ✓）：`R` 的像 ⊆ `Q(t_0)` ✓ ＋ **`S` 在 `R` 上有限型** ✓
⟹ `\varphi(S)` **全体**落进**单个** `Q(t)` ✓ —— **内部工序** ✓：`\mathrm{Algebra.FiniteType.out}` ✓ 取有限生成族 ✓
⟹ `\mathrm{exists\_mul\_eq\_of\_finite}` ✓（§4.21 ✓）**清分母**得 `t_1` ✓ ⟹ `\mathrm{mem\_adjoin\_inv\_of\_pow\_mul\_eq}` ✓（§4.23 ✓）
⟹ **①** 给覆盖 ✓ ⟹ `\mathrm{Algebra.adjoin\_induction}` ✓ **收口** ✓（**减法／乘法支用 `\mathrm{simpa\ only}\ [\mathrm{map\_add}／\mathrm{map\_mul}]`** ✓
—— **⚠ 一处编译期自纠** ✓：**逐条 `\mathrm{rw}` 会连子代数项里的 `\mathrm{algebraMap}\ (t_0 \cdot t_1)` 一并改写** ✗ ⟹ 与假设**不再 defeq** ✗，
**正解 ＝ `\mathrm{simpa\ only}` 两侧同改写** ✓）。
**⚠ 通用档** ✓（**承 (75)** ✓）：两件**不**写在 `\mathrm{MvPolynomial}` 上 ✗，而写在**任意** `A`（`\mathrm{IsFractionRing}\ A\ L` ✓）上 ⟹
Noether 重项**只在调用点出现一次** ✓（r171 的 `\mathrm{exists\_mem\_adjoin\_away\_of\_noether}` ✓ 作**输入** ✓）。
**⚠ 假设表** ✓：① **不留** `[\mathrm{NoZeroDivisors}\ A]` ✗（**其证明不用** ✓，由 `\mathrm{IsFractionRing}` 供 ✓）；
② 需 `[\mathrm{IsDomain}\ A]` ✓（§4.21／§4.20 的入口 ✓）。 -/

section ImageClearingGeneral

variable {A : Type u} [CommRing A] {L : Type u} [Field L] [Algebra A L]
variable [IsFractionRing A L]

/-- **① 通用清分母（结论显式给乘子）** ✓：`R` 的像 ⊆ `Q(t_0)` ＋ 有限族各自 ⊆ `Q(t_1)` ⟹
`R`-`\mathrm{adjoin}` 全体 ⊆ `Q(t_0 \cdot t_1)` ✓（**单调性 §4.37 直接用** ✓）。 -/
theorem exists_adjoin_le_away_of_image_le {R : Type u} [CommRing R] [Algebra R L]
    (t₀ : A) (ht₀ : t₀ ≠ 0)
    (hR : ∀ r : R, algebraMap R L r ∈ Algebra.adjoin A ({(algebraMap A L t₀)⁻¹} : Set L))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → L) (t₁ : A) (ht₁ : t₁ ≠ 0)
    (h₁ : ∀ i : ι, e i ∈ Algebra.adjoin A ({(algebraMap A L t₁)⁻¹} : Set L)) :
    ∀ x ∈ Algebra.adjoin R (Set.range e),
      x ∈ Algebra.adjoin A ({(algebraMap A L (t₀ * t₁))⁻¹} : Set L) := by
  have hmono₁ : Algebra.adjoin A ({(algebraMap A L t₀)⁻¹} : Set L) ≤
      Algebra.adjoin A ({(algebraMap A L (t₀ * t₁))⁻¹} : Set L) :=
    adjoin_away_mono (A := A) (L := L) t₀ t₁ ht₁
  have hmono₂ : Algebra.adjoin A ({(algebraMap A L t₁)⁻¹} : Set L) ≤
      Algebra.adjoin A ({(algebraMap A L (t₀ * t₁))⁻¹} : Set L) := by
    have h := adjoin_away_mono (A := A) (L := L) t₁ t₀ ht₀
    rwa [mul_comm t₁ t₀] at h
  intro x hx
  refine Algebra.adjoin_induction (p := fun x _ => x ∈ Algebra.adjoin A
    ({(algebraMap A L (t₀ * t₁))⁻¹} : Set L)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact hmono₂ (h₁ i)
  · intro r
    exact hmono₁ (hR r)
  · intro y z _ _ hy hz
    exact add_mem hy hz
  · intro y z _ _ hy hz
    exact mul_mem hy hz

end ImageClearingGeneral

section FiniteTypeAnnihilation

variable {A : Type u} [CommRing A] [IsDomain A] {L : Type u} [Field L] [Algebra A L]
variable [IsFractionRing A L]

/-- **② 断指件：有限型像落进单个局部化** ✓✅（源「`S \subset F[x_\sigma](1/t)`」✓ 的**库内定理形** ✓）：
`R` 的像 ⊆ `Q(t_0)` ✓ ＋ `S` 在 `R` 上**有限型** ✓ ＋ `\varphi : S \to_R L` ✓ ⟹
`\exists t \neq 0,\ \forall s : S,\ \varphi s \in Q(t)` ✓（**工序见节头** ✓：生成族 ⟹ 清分母 ⟹ ① ⟹ `\mathrm{adjoin}` 归纳 ✓）。
**⚠ 用点** ✓：(c) 款取 `R := R''` ✓、`S := S''` ✓（**有限型由 `\mathrm{GaloisProjectiveHyp}` 的 `\mathrm{Module.Finite}`** ✓
经**实例** `\mathrm{Module.Finite} \Rightarrow \mathrm{Algebra.FiniteType}` ✓ 自动供给 ✓）、
`\varphi` ＝ 由**下降同构**给出的**嵌入** ✓（r172 的 `\mathrm{injective\_tmul\_one\_of\_galoisProjective}` ✓）、
`t_0`／`hR` ＝ **§4.36 的 `g`-半** ✓（＋ r157 的 `R'' \to R_1(1/s)` ✓）⟹ **源句成立** ✓。 -/
theorem exists_image_le_away_of_finiteType {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra R L] [Algebra.FiniteType R S] (φ : S →ₐ[R] L)
    (t₀ : A) (ht₀ : t₀ ≠ 0)
    (hR : ∀ r : R, algebraMap R L r ∈ Algebra.adjoin A ({(algebraMap A L t₀)⁻¹} : Set L)) :
    ∃ t : A, t ≠ 0 ∧ ∀ s : S,
      φ s ∈ Algebra.adjoin A ({(algebraMap A L t)⁻¹} : Set L) := by
  classical
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := R) (A := S)
  obtain ⟨t₁, ht₁, h₁⟩ := exists_mul_eq_of_finite (A := A) (K := L)
    (fun j : {x // x ∈ T} => φ (j : S))
    (fun _ => exists_mul_eq_of_isFractionRing (A := A) (K := L) _)
  have h₁' : ∀ j : {x // x ∈ T}, φ (j : S) ∈
      Algebra.adjoin A ({(algebraMap A L t₁)⁻¹} : Set L) := by
    intro j
    obtain ⟨x, hx⟩ := h₁ j
    exact mem_adjoin_inv_of_pow_mul_eq (A := A) (K := L) ht₁ ⟨1, x, by simpa using hx⟩
  have hcov := exists_adjoin_le_away_of_image_le (A := A) (L := L) (R := R)
    t₀ ht₀ hR (fun j : {x // x ∈ T} => φ (j : S)) t₁ ht₁ h₁'
  refine ⟨t₀ * t₁, mul_ne_zero ht₀ ht₁, fun s => ?_⟩
  have hs : s ∈ Algebra.adjoin R (↑T : Set S) := by rw [hT]; trivial
  refine Algebra.adjoin_induction (p := fun s _ => φ s ∈ Algebra.adjoin A
    ({(algebraMap A L (t₀ * t₁))⁻¹} : Set L)) ?_ ?_ ?_ ?_ hs
  · intro y hy
    exact hcov (φ y) (Algebra.subset_adjoin ⟨⟨y, hy⟩, rfl⟩)
  · intro r
    rw [φ.commutes r]
    exact adjoin_away_mono (A := A) (L := L) t₀ t₁ ht₁ (hR r)
  · intro y z _ _ hy hz
    simpa only [map_add] using add_mem hy hz
  · intro y z _ _ hy hz
    simpa only [map_mul] using mul_mem hy hz

/-- **登记** ✗：本件与 r172 的**嵌入件**（`BaseChangeProj` 的
`\mathrm{injective\_tmul\_one\_of\_galoisProjective}` ✓）**合用**即得源句 ✓；
**余 ＝ 装配点接线** ✓（`t_0`／`hR` 由 §4.36 的 ⑥ ✓ ＋ r157 的 `R'' \to R_1(1/s)` ✓ 供给 ✓ —— **工程缺口** ✓）。 -/
theorem finiteTypeImage_gap_registered : True := trivial

end FiniteTypeAnnihilation

/-! ## 4.39 **装配 (c) 款 `R \to K` 接线（第一块）**：**不变量乘子** ＋ **局部化层的 `G`-作用与等变性**（第 175 轮）

**⚠ 起点** ✓（§137.6 第 1 项 ✓）：`R \to K` 的**crux** ✓ ＝ **局部化层的等变性** ✗
（源正因此先把 `t` 换成 `t' = \prod_\sigma \sigma(t)` ✓ —— §135.4 登记 ③ ✓）。**⚠ 本轮只压此项** ✓（**不转项** ✗）。

**⚠ 四件** ✓：
**①** `exists_invariant_mul` ✓✅ —— **源的不变量乘子** ✓：`\exists t' \neq 0`，`t'` 为 `G`-**不变** ✓ 且
`Q(t) \subseteq Q(t')` ✓（取 `t' := \prod_\sigma \sigma \bullet t` ✓ —— **不变化直接用 §4.5 的 `noether_prod_smul_invariant`** ✓，
**拆分用 `\mathrm{Finset.mul\_prod\_erase}`** ✓，**单调由 §4.37** ✓）；
**②** `algHom_codRestrict_of_forall_mem` ✓✅ —— **像落进子代数 ⟹ `\mathrm{AlgHom}` 进该子代数** ✓（`\mathrm{AlgHom.codRestrict}` ✓）；
**③** `awayRingHom` ＋ `awayMulSemiringAction` ✓✅ —— **`\mathrm{Localization.Away}\ t` 上的 `G`-作用** ✓（`t` 不变时 ✓；
**入口 ＝ `\mathrm{IsLocalization.Away.lift}`** ✓ —— 由 `g \bullet t = t` 得 `\mathrm{algebraMap}\ t` 仍为**单位** ✓）；
**④** **`awayLift_equivariant`** ✓✅ —— **局部化提升的等变性** ✓：等变 `\varphi` ✓ ＋ `t` 不变 ✓ ＋ 提升一致 ✓ ⟹ **`\varphi'` 等变** ✓
（**证明 ＝ 唯一性** ✓：两个环同态在 `\mathrm{algebraMap}` 上一致 ✓ ⟹ 由 **`\mathrm{IsLocalization.ringHom\_ext}`** ✓ 相等 ✓）。
**⚠ 工艺** ✓：**`change` 先对齐 smul 记号的展开形** ✓（`\mathrm{rw}` 在 smul 记法下**不匹配** ✗ —— 三处 ✓）；
**`\mathrm{@[instance_reducible]}`** ✓ 加在作用定义上 ✓（**消 `\mathrm{classDefReducibility}` 警告** ✓）；
**未用实例**（`[\mathrm{Algebra}\ F\ L]` 等 ✗）⟹ **移出 section** ✓（**(78)** ✓）。 -/

section InvariantMultiplier

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]

/-- **① 不变量乘子** ✓✅（源 `t' = \prod_\sigma \sigma(t)` ✓）：每个 `t \neq 0` 都有一个**不变**的倍数 `t' \neq 0` ✓，
且 `Q(t) \subseteq Q(t')` ✓ —— 正是源为**等变性**所作的替换 ✓。 -/
theorem exists_invariant_mul (t : MvPolynomial G F) (ht : t ≠ 0) :
    ∃ t' : MvPolynomial G F, t' ≠ 0 ∧ (∀ g : G, g • t' = t') ∧
      Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)) ≤
        Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) t')⁻¹} : Set (NoetherField F G)) := by
  classical
  have hne : ∀ σ : G, σ • t ≠ 0 := fun σ h0 => ht (by
    have h1 : (MulSemiringAction.toRingEquiv G (MvPolynomial G F) σ) t
        = (MulSemiringAction.toRingEquiv G (MvPolynomial G F) σ) 0 := by simpa using h0
    exact (MulSemiringAction.toRingEquiv G (MvPolynomial G F) σ).injective h1)
  refine ⟨∏ σ : G, σ • t, Finset.prod_ne_zero_iff.mpr (fun σ _ => hne σ),
    fun g => noether_prod_smul_invariant F G t g, ?_⟩
  have hsplit : (∏ σ : G, σ • t) = t * ∏ σ ∈ Finset.univ.erase (1 : G), σ • t := by
    rw [← Finset.mul_prod_erase Finset.univ (fun σ => σ • t) (Finset.mem_univ (1 : G)), one_smul]
  rw [hsplit]
  exact adjoin_away_mono (A := MvPolynomial G F) (L := NoetherField F G) t _
    (Finset.prod_ne_zero_iff.mpr (fun σ _ => hne σ))

end InvariantMultiplier

section CodRestrictAlgHom

variable {F : Type u} [Field F] {G : Type u}
variable {L : Type u} [Field L] [Algebra (MvPolynomial G F) L]
variable [Algebra F L] [IsScalarTower F (MvPolynomial G F) L]

/-- **② 像落进子代数 ⟹ `AlgHom` 进该子代数** ✓（`\mathrm{AlgHom.codRestrict}` ✓）——
`R \to K` 接线的**载体步** ✓（`R` 的像落在 `Q` 内 ⟹ 得 `R \toₐ[F] \uparrow Q` ✓）。 -/
theorem algHom_codRestrict_of_forall_mem {R : Type u} [CommRing R] [Algebra R L] [Algebra F R]
    [IsScalarTower F R L] (Q : Subalgebra (MvPolynomial G F) L)
    (hRQ : ∀ r : R, algebraMap R L r ∈ Q) :
    ∃ Φ : R →ₐ[F] ↥(Subalgebra.restrictScalars F Q),
      ∀ r : R, (Φ r : L) = algebraMap R L r :=
  ⟨(IsScalarTower.toAlgHom F R L).codRestrict _ hRQ, fun _ => rfl⟩

end CodRestrictAlgHom

section AwayAction

variable {F : Type u} [Field F] {G : Type u} [Group G]
variable {t : MvPolynomial G F}

/-- **③a 诱导自同态** ✓：`g` 在 `\mathrm{Localization.Away}\ t` 上的环自同态 ✓（`t` 不变 ⟹ 良定义 ✓）。 -/
noncomputable def awayRingHom (ht : ∀ g : G, g • t = t) (g : G) :
    Localization.Away t →+* Localization.Away t :=
  IsLocalization.Away.lift (S := Localization.Away t) t
    (g := (algebraMap (MvPolynomial G F) (Localization.Away t)).comp
      (MulSemiringAction.toRingEquiv G (MvPolynomial G F) g).toRingHom) (by
      change IsUnit (algebraMap (MvPolynomial G F) (Localization.Away t)
        ((MulSemiringAction.toRingEquiv G (MvPolynomial G F) g) t))
      rw [show (MulSemiringAction.toRingEquiv G (MvPolynomial G F) g) t = g • t from rfl, ht g]
      exact IsLocalization.Away.algebraMap_isUnit t)

/-- **③b 与 `\mathrm{algebraMap}` 的相容** ✓。 -/
theorem awayRingHom_algebraMap (ht : ∀ g : G, g • t = t) (g : G) (p : MvPolynomial G F) :
    awayRingHom (F := F) ht g (algebraMap (MvPolynomial G F) (Localization.Away t) p)
      = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p) := by
  rw [show awayRingHom (F := F) ht g (algebraMap (MvPolynomial G F) (Localization.Away t) p)
      = ((awayRingHom (F := F) ht g).comp
        (algebraMap (MvPolynomial G F) (Localization.Away t))) p from rfl,
    awayRingHom, IsLocalization.Away.lift_comp (S := Localization.Away t)
      (g := (algebraMap (MvPolynomial G F) (Localization.Away t)).comp
        (MulSemiringAction.toRingEquiv G (MvPolynomial G F) g).toRingHom) t _]
  rfl

/-- **③ `\mathrm{Localization.Away}\ t` 上的 `G`-作用** ✓✅（**`t` 不变时** ✓；mathlib **无**此实例 ✗）。 -/
@[instance_reducible]
noncomputable def awayMulSemiringAction (ht : ∀ g : G, g • t = t) :
    MulSemiringAction G (Localization.Away t) where
  smul g := awayRingHom (F := F) ht g
  one_smul x := by
    have h1 : awayRingHom (F := F) ht 1 = RingHom.id (Localization.Away t) := by
      apply IsLocalization.ringHom_ext (R := MvPolynomial G F) (S := Localization.Away t)
        (Submonoid.powers t)
      apply RingHom.ext
      intro p
      simp only [RingHom.comp_apply, RingHom.id_apply,
        awayRingHom_algebraMap (F := F) ht, one_smul]
    change awayRingHom (F := F) ht 1 x = x
    rw [h1]
    rfl
  mul_smul g h x := by
    have h1 : awayRingHom (F := F) ht (g * h)
        = (awayRingHom (F := F) ht g).comp (awayRingHom (F := F) ht h) := by
      apply IsLocalization.ringHom_ext (R := MvPolynomial G F) (S := Localization.Away t)
        (Submonoid.powers t)
      apply RingHom.ext
      intro p
      simp only [RingHom.comp_apply, awayRingHom_algebraMap (F := F) ht, mul_smul]
    change awayRingHom (F := F) ht (g * h) x
      = awayRingHom (F := F) ht g (awayRingHom (F := F) ht h x)
    rw [h1]
    rfl
  smul_one g := map_one (awayRingHom (F := F) ht g)
  smul_mul g x y := map_mul (awayRingHom (F := F) ht g) x y
  smul_zero g := map_zero (awayRingHom (F := F) ht g)
  smul_add g x y := map_add (awayRingHom (F := F) ht g) x y

/-- **④ 局部化提升的等变性** ✓✅（**crux** ✓）：等变 `\varphi : F[x_\sigma] \toₐ[F] L'` ✓ ＋ `t` **不变** ✓ ＋
提升 `\varphi'` 与 `\varphi` 在 `\mathrm{algebraMap}` 上一致 ✓ ⟹ **`\varphi'` 与 `G` 等变** ✓
（**证明 ＝ 唯一性** ✓：两侧皆环同态 ✓，在 `\mathrm{algebraMap}` 的像上一致 ✓（**由 `\varphi` 的等变性** ✓）⟹
`\mathrm{IsLocalization.ringHom\_ext}` ✓ 收口 ✓）。 -/
theorem awayLift_equivariant (ht : ∀ g : G, g • t = t) {L' : Type u} [Field L'] [Algebra F L']
    [MulSemiringAction G L']
    (φ : MvPolynomial G F →ₐ[F] L') (heq : ∀ (g : G) (p : MvPolynomial G F), φ (g • p) = g • φ p)
    (φ' : Localization.Away t →ₐ[F] L')
    (hφ : ∀ p : MvPolynomial G F, φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p) = φ p) :
    letI := awayMulSemiringAction (F := F) ht
    ∀ (g : G) (x : Localization.Away t), φ' (g • x) = g • φ' x := by
  let _ := awayMulSemiringAction (F := F) ht
  intro g x
  have h2 : (φ'.toRingHom.comp (awayRingHom (F := F) ht g))
      = ((MulSemiringAction.toRingEquiv G L' g).toRingHom.comp φ'.toRingHom) := by
    apply IsLocalization.ringHom_ext (R := MvPolynomial G F) (S := Localization.Away t)
      (Submonoid.powers t)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, awayRingHom_algebraMap (F := F) ht]
    show φ' (algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
      = (MulSemiringAction.toRingEquiv G L' g)
          (φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p))
    rw [hφ (g • p), hφ p,
      show (MulSemiringAction.toRingEquiv G L' g) (φ p) = g • φ p from rfl]
    exact heq g p
  exact congrFun (congrArg DFunLike.coe h2) x

/-- **登记** ✗：`R \to K` 接线的**余件** ✓ —— **广义不动域落地** ✓（r170 的 `\mathrm{exists\_algHom\_of\_equivariant\_of\_fixed}` ✓ 的
"`R` 逐点固定"版 ✓）＋ **端到端组装** ✓（`R \to Q` ✓ → 提升 ✓ → 等变 ✓ → 落进 `K` ✓）。 -/
theorem awayLift_gap_registered : True := trivial

end AwayAction

/-! ## 4.40 **装配 (c) 款 `R \to K` 接线（第二块）**：**广义不动域落地** ＋ **作用与到 `L` 的相容**（第 176 轮）

**⚠ 起点** ✓（**仍压 ②** ✓，**不转项** ✗）：r175 已落 **① 不变量乘子** ✓ ＋ **③④ 局部化层的 `G`-作用与提升等变性** ✓
（§4.39 ✓）⟹ 本轮补 **② 的余两件之第一件** ✓：**`R` 的像落进 `K`** ✓。

**⚠ 两件** ✓：
**①** **`exists_algHom_of_equivariant_of_fixed_of_forall_fixed`** ✓✅ —— **广义不动域落地** ✓：
r170 的 `\mathrm{exists\_algHom\_of\_equivariant\_of\_fixed}` ✓ 只用 `\mathrm{IsGaloisWithGroup}` 的**第二合取** ✓
（`R` 逐点固定 ✓）⟹ 本件把该前提**换成直接假设** ✓（`ι : R \toₐ[F] Q` 的像逐点固定 ✓）——
于是 `R` 不必是 Galois 对的基环 ✓，而可取**局部化层** ✓（其固定性由 r175 ③④ ＋ `R \subseteq L^G` 供 ✓）。
**②** `awayToField` ✓✅ ＋ `awayToField_algebraMap` ✓✅ ＋ **`awayToField_smul`** ✓✅ —— **作用与「局部化 → `L`」的相容** ✓：
`f(g \bullet x) = g \bullet f(x)` ✓（**由 §4.4 的 `smul_algebraMap_noether`** ✓ ＋ **`\mathrm{IsLocalization.ringHom\_ext}`** 唯一性 ✓）
—— **用点** ✓：`R` 在局部化中的**原像**因此**逐点固定** ✓（`f` 单射 ⟹ `g \bullet ι r = ι r` ✓ —— **下一步** ✓）。
**⚠ 登记** ✗：**搬运件** ✓（`R \toₐ[F] \mathrm{Localization.Away}\ t` ✓）—— 其**唯一缺口** ＝
`\mathrm{awayToFieldAlg}` 的**单射性** ✓（由 `\mathrm{mk'}` 表出 ＋ 域内算 ＋ `\mathrm{algebraMap}` 单射 ✓，
**归入下一轮** ✓）；**端到端组装** ✓ 随之 ✓。 -/

section GeneralizedFixedDescent

variable {F : Type u} [Field F] {G : Type u} [Group G]
variable {R Q L K : Type u} [CommRing R] [CommRing Q] [Field L] [Field K]
variable [Algebra F R] [Algebra F Q] [Algebra F L] [Algebra K L] [Algebra F K]
variable [IsScalarTower F K L]
variable [MulSemiringAction G Q] [MulSemiringAction G L]

/-- **① 广义不动域落地** ✓✅（**`R` 的像逐点固定版** ✓）：`\Phi : Q \toₐ[F] L` **等变** ✓、
`\iota : R \toₐ[F] Q` ✓ 且 **`R` 的像在 `Q` 中逐点固定** ✓、`L` 的**不动点落进 `K`** ✓ ⟹
**`\exists \Phi_0 : R \toₐ[F] K`** ✓ 且 `\mathrm{algebraMap}\ K\ L \circ \Phi_0 = \Phi \circ \iota` ✓。
**机制** ✓（同 r170 ✓）：`\Phi(\iota r)` 被每个 `g` 固定 ✓（**等变性 ＋ 逐点固定** ✓）⟹ 由 `hfix` 落进 `K` ✓；
`\mathrm{choose}` 出的 `\Phi_0` 的加法／乘法／单位／`F`-线性**逐条由 `\mathrm{algebraMap}\ K\ L` 的单射搬运** ✓。 -/
theorem exists_algHom_of_equivariant_of_fixed_of_forall_fixed
    (Φ : Q →ₐ[F] L) (heq : ∀ (g : G) (q : Q), Φ (g • q) = g • Φ q)
    (ι : R →ₐ[F] Q) (hfixed : ∀ (g : G) (r : R), g • (ι r) = ι r)
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x) :
    ∃ Φ₀ : R →ₐ[F] K, ∀ r : R, algebraMap K L (Φ₀ r) = Φ (ι r) := by
  have key : ∀ r : R, ∃ k : K, algebraMap K L k = Φ (ι r) := by
    intro r
    refine hfix (Φ (ι r)) (fun g => ?_)
    rw [← heq g (ι r), hfixed g r]
  choose Φ₀ hΦ₀ using key
  have hinj : Function.Injective (algebraMap K L) := FaithfulSMul.algebraMap_injective K L
  exact ⟨{ toFun := Φ₀
           map_one' := hinj (by rw [map_one, hΦ₀ 1, map_one, map_one])
           map_mul' := fun x y => hinj (by rw [map_mul, hΦ₀ (x * y), map_mul, map_mul,
             hΦ₀ x, hΦ₀ y])
           map_zero' := hinj (by rw [map_zero, hΦ₀ 0, map_zero, map_zero])
           map_add' := fun x y => hinj (by rw [map_add, hΦ₀ (x + y), map_add, map_add,
             hΦ₀ x, hΦ₀ y])
           commutes' := fun a => hinj (by
             rw [hΦ₀ (algebraMap F R a), AlgHom.commutes, AlgHom.commutes,
               IsScalarTower.algebraMap_apply F K L]) }, hΦ₀⟩

end GeneralizedFixedDescent

section AwayToField

variable {F : Type u} [Field F] {G : Type u}

/-- **②a 局部化 → Noether 域 的典范环同态** ✓（`t \neq 0` 时 `\mathrm{algebraMap}\ t` 在域中可逆 ✓，
由**万有性质**得 ✓）—— 即**局部化在 `L` 中的像**的载体 ✓。 -/
noncomputable def awayToField (t : MvPolynomial G F) (ht : t ≠ 0) :
    Localization.Away t →+* NoetherField F G :=
  IsLocalization.Away.lift (S := Localization.Away t) t (by
    rw [isUnit_iff_ne_zero]
    exact fun h0 => ht (IsFractionRing.injective (MvPolynomial G F) (NoetherField F G)
      (by rw [h0, map_zero])))

/-- **②b 与 `\mathrm{algebraMap}` 的相容** ✓。 -/
theorem awayToField_algebraMap (t : MvPolynomial G F) (ht : t ≠ 0) (p : MvPolynomial G F) :
    awayToField (F := F) (G := G) t ht
        (algebraMap (MvPolynomial G F) (Localization.Away t) p)
      = algebraMap (MvPolynomial G F) (NoetherField F G) p := by
  rw [show awayToField (F := F) (G := G) t ht
        (algebraMap (MvPolynomial G F) (Localization.Away t) p)
      = ((awayToField (F := F) (G := G) t ht).comp
          (algebraMap (MvPolynomial G F) (Localization.Away t))) p from rfl,
    awayToField, IsLocalization.Away.lift_comp (S := Localization.Away t)
      (g := algebraMap (MvPolynomial G F) (NoetherField F G)) t _]

end AwayToField

section AwayToFieldSmul

variable {F : Type u} [Field F] {G : Type u} [Group G] {t : MvPolynomial G F}

/-- **②c 作用与「局部化 → `L`」的相容** ✓✅：`t` **不变** 时
`\mathrm{awayToField}(g \bullet x) = g \bullet \mathrm{awayToField}(x)` ✓。
**证明** ✓：两侧皆环同态 ✓，在 `\mathrm{algebraMap}` 的像上一致 ✓ —— **用 §4.4 的
`smul_algebraMap_noether`** ✓（`g \bullet \mathrm{algebraMap}\ p = \mathrm{algebraMap}(g \bullet p)` ✓）
⟹ `\mathrm{IsLocalization.ringHom\_ext}` ✓ 收口 ✓。 -/
theorem awayToField_smul (ht : ∀ g : G, g • t = t) (ht0 : t ≠ 0) (g : G)
    (x : Localization.Away t) :
    awayToField (F := F) (G := G) t ht0 (awayRingHom (F := F) ht g x)
      = g • awayToField (F := F) (G := G) t ht0 x := by
  let _ := awayMulSemiringAction (F := F) ht
  have h2 : (awayToField (F := F) (G := G) t ht0).comp (awayRingHom (F := F) ht g)
      = (MulSemiringAction.toRingEquiv G (NoetherField F G) g).toRingHom.comp
          (awayToField (F := F) (G := G) t ht0) := by
    apply IsLocalization.ringHom_ext (R := MvPolynomial G F) (S := Localization.Away t)
      (Submonoid.powers t)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, awayRingHom_algebraMap (F := F) ht,
      awayToField_algebraMap (F := F) (G := G) t ht0]
    show algebraMap (MvPolynomial G F) (NoetherField F G) (g • p)
      = (MulSemiringAction.toRingEquiv G (NoetherField F G) g)
          (algebraMap (MvPolynomial G F) (NoetherField F G) p)
    rw [show (MulSemiringAction.toRingEquiv G (NoetherField F G) g)
        (algebraMap (MvPolynomial G F) (NoetherField F G) p)
        = g • algebraMap (MvPolynomial G F) (NoetherField F G) p from rfl]
    exact (smul_algebraMap_noether F G g p).symm
  exact congrFun (congrArg DFunLike.coe h2) x

/-- **登记** ✗：`R \to K` 的**搬运件** ✓（`R \toₐ[F] \mathrm{Localization.Away}\ t` ✓）——
**唯一缺口** ＝ `\mathrm{awayToField}` 的**单射性** ✓（`\mathrm{mk'}` 表出 ＋ 域内算 ＋ `\mathrm{algebraMap}` 单射 ✓）；
本件一旦落地 ⟹ **`R` 的原像逐点固定** ✓（由本节的 ②c ＋ `R \subseteq L^G` ✓）⟹ **①** 即可收口 ✓。 -/
theorem awayToField_gap_registered : True := trivial

end AwayToFieldSmul

/-! ## 4.41 **装配 (c) 款 `R \to K`（第三块 · 收口）**：**搬运件** ＋ **端到端组装**（第 177 轮）

**⚠ 起点** ✓（**仍压 ②** ✓，**不转项** ✗）：r176 已落 **① 广义不动域落地** ✓ ＋ **②c 作用相容** ✓ ⟹ 本轮补 **余两件** ✓ 并**收口** ✓。

**⚠ 四件** ✓：
**①** `awayToFieldAlg` ✓✅ —— `\mathrm{awayToField}` 的 **`\mathrm{AlgHom}` 形** ✓（`\mathrm{commutes'}` 由**标量塔** ＋ `\mathrm{awayToField\_algebraMap}` ✓）；
**②** **`awayToField_injective`** ✓✅ —— **单射性** ✓（**搬运件的唯一缺口** ✓）：
用 `\mathrm{IsLocalization.mk'\_surjective}` ✓ 把 `x, y` 表成 `\mathrm{mk'}\ a\ b` ／ `\mathrm{mk'}\ c\ d` ✓（`b, d \in \mathrm{powers}\ t` ✓），
由 `\mathrm{mk'\_spec}` ✓ ＋ `\mathrm{awayToField\_algebraMap}` ✓ 在 `L` 中算得 `\mathrm{algebraMap}\ (c \cdot b) = \mathrm{algebraMap}\ (a \cdot d)` ✓，
再用 **`\mathrm{IsFractionRing.injective}`** ✓ 得 `A` 中**等式** ✓，最后由 **`\mathrm{IsLocalization.mk'\_eq\_iff\_eq}`** ✓（↔ `\mathrm{algebraMap}\ (\uparrow d \cdot a) = \mathrm{algebraMap}\ (\uparrow b \cdot c)` ✓）收口 ✓
（**⚠ 无需**局部化的单射性 ✗ —— 只要 `A \to L` 的单射 ✓）；
**③** **`exists_algHom_away_of_image_le`** ✓✅ —— **搬运件** ✓：`R` 的像 ⊆ `\mathrm{awayToFieldAlg}` 的**值域** ✓ ⟹
`\exists \iota : R \toₐ[F] \mathrm{Localization.Away}\ t`，`\mathrm{awayToFieldAlg} \circ \iota = \mathrm{algebraMap}\ R\ L` ✓
（**入口 ＝ `\mathrm{AlgEquiv.ofInjective}`** ✓（②给出单射 ✓）＋ `\mathrm{AlgHom.codRestrict}` ✓）；
**④** **`exists_algHom_base_of_equivariant`** ✓✅✅ —— **端到端组装（断指）** ✓：把 ③ 的 `\iota` ✓、r175④ 的 `\varphi'` **等变性** ✓、
r176②c 的**相容** ✓、`R \subseteq L^G` ✓、r176① 的**落地** ✓ **串成一条链** ✓ ⟹
**`\exists \Phi : R \toₐ[F] K`** ✓（结论**连同分解链一并展出** ✓：`\Phi'`（提升）／`\iota`（搬运）／`\Phi`（落进 `K`）及其三条相容等式 ✓）。
**⚠ 新增工艺（第四次同族）** ✓：**smul 记法下的 `\mathrm{rw}` 不匹配** ✗ ⟹ **`\mathrm{change}` 先对齐** ✓（本节 **1 处** ✓）；
**`\mathrm{let}` 代 `\mathrm{letI}`** ✓（**(55)** ✓）；**`hι`（`\mathrm{AlgHom}` 形）与 `\mathrm{awayToField}`（环同态形）须显式过渡** ✓（`\mathrm{have}` ✓）。 -/

section AwayToFieldAlg

variable {F : Type u} [Field F] {G : Type u}

/-- **① `\mathrm{awayToField}` 的 `\mathrm{AlgHom}` 形** ✓（`F`-线性由**标量塔** ＋ ②b 推 ✓）。 -/
noncomputable def awayToFieldAlg (t : MvPolynomial G F) (ht : t ≠ 0) :
    Localization.Away t →ₐ[F] NoetherField F G where
  __ := awayToField (F := F) (G := G) t ht
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply F (MvPolynomial G F) (Localization.Away t)]
    exact awayToField_algebraMap (F := F) (G := G) t ht (algebraMap F (MvPolynomial G F) a)

/-- **② 单射性** ✓✅（**搬运件的唯一缺口** ✓）：典范映射 `\mathrm{Localization.Away}\ t \to L` **单射** ✓。
**⚠ 关键** ✓：**只**用 `A \to L` 的单射 ✓ ＋ `\mathrm{mk'}` 表出 ✓ ＋ `\mathrm{mk'\_eq\_iff\_eq}` ✓ —— **不需**局部化的单射性 ✓。 -/
theorem awayToField_injective (t : MvPolynomial G F) (ht : t ≠ 0) :
    Function.Injective (awayToField (F := F) (G := G) t ht) := by
  have hinjL : Function.Injective (algebraMap (MvPolynomial G F) (NoetherField F G)) :=
    IsFractionRing.injective (MvPolynomial G F) (NoetherField F G)
  intro x y hxy
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) x
  obtain ⟨⟨c, d⟩, hy⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) y
  rw [← hx, ← hy] at hxy ⊢
  change awayToField (F := F) (G := G) t ht (IsLocalization.mk' (Localization.Away t) a b)
    = awayToField (F := F) (G := G) t ht (IsLocalization.mk' (Localization.Away t) c d) at hxy
  change IsLocalization.mk' (Localization.Away t) a b
    = IsLocalization.mk' (Localization.Away t) c d
  have key : ∀ (p : MvPolynomial G F) (m : ↥(Submonoid.powers t)),
      awayToField (F := F) (G := G) t ht (IsLocalization.mk' (Localization.Away t) p m)
        * algebraMap (MvPolynomial G F) (NoetherField F G) (m : MvPolynomial G F)
      = algebraMap (MvPolynomial G F) (NoetherField F G) p := by
    intro p m
    simpa only [map_mul, awayToField_algebraMap (F := F) (G := G) t ht]
      using congrArg (awayToField (F := F) (G := G) t ht)
        (IsLocalization.mk'_spec (Localization.Away t) p m)
  have h1 := key a b
  have h2 := key c d
  have h3 : algebraMap (MvPolynomial G F) (NoetherField F G) (c * (b : MvPolynomial G F))
      = algebraMap (MvPolynomial G F) (NoetherField F G) (a * (d : MvPolynomial G F)) := by
    calc algebraMap (MvPolynomial G F) (NoetherField F G) (c * (b : MvPolynomial G F))
        = algebraMap (MvPolynomial G F) (NoetherField F G) c
            * algebraMap (MvPolynomial G F) (NoetherField F G) (b : MvPolynomial G F) := by
          rw [map_mul]
      _ = (awayToField (F := F) (G := G) t ht (IsLocalization.mk' (Localization.Away t) c d)
            * algebraMap (MvPolynomial G F) (NoetherField F G) (d : MvPolynomial G F))
            * algebraMap (MvPolynomial G F) (NoetherField F G) (b : MvPolynomial G F) := by
          rw [← h2]
      _ = (awayToField (F := F) (G := G) t ht (IsLocalization.mk' (Localization.Away t) a b)
            * algebraMap (MvPolynomial G F) (NoetherField F G) (d : MvPolynomial G F))
            * algebraMap (MvPolynomial G F) (NoetherField F G) (b : MvPolynomial G F) := by
          rw [← hxy]
      _ = (awayToField (F := F) (G := G) t ht (IsLocalization.mk' (Localization.Away t) a b)
            * algebraMap (MvPolynomial G F) (NoetherField F G) (b : MvPolynomial G F))
            * algebraMap (MvPolynomial G F) (NoetherField F G) (d : MvPolynomial G F) := by
          ring
      _ = algebraMap (MvPolynomial G F) (NoetherField F G) a
            * algebraMap (MvPolynomial G F) (NoetherField F G) (d : MvPolynomial G F) := by
          rw [h1]
      _ = algebraMap (MvPolynomial G F) (NoetherField F G) (a * (d : MvPolynomial G F)) := by
          rw [map_mul]
  have h5 : c * (b : MvPolynomial G F) = a * (d : MvPolynomial G F) := hinjL h3
  rw [IsLocalization.mk'_eq_iff_eq]
  rw [mul_comm (d : MvPolynomial G F) a, mul_comm (b : MvPolynomial G F) c, ← h5]

end AwayToFieldAlg

section AwayTransport

variable {F : Type u} [Field F] {G : Type u} {t : MvPolynomial G F}

/-- **③ 搬运件** ✓✅：`R` 的像落在 `\mathrm{awayToFieldAlg}` 的**值域**内 ⟹
**`\exists \iota : R \toₐ[F] \mathrm{Localization.Away}\ t`** ✓ 且 `\mathrm{awayToFieldAlg} \circ \iota = \mathrm{algebraMap}\ R\ L` ✓
（**入口 ＝ `\mathrm{AlgEquiv.ofInjective}`** ✓ 由 ② 的单射 ✓ ＋ `\mathrm{AlgHom.codRestrict}` ✓）。 -/
theorem exists_algHom_away_of_image_le (t : MvPolynomial G F) (ht : t ≠ 0)
    {R : Type u} [CommRing R] [Algebra R (NoetherField F G)] [Algebra F R]
    [IsScalarTower F R (NoetherField F G)]
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range) :
    ∃ ι : R →ₐ[F] Localization.Away t,
      ∀ r : R, awayToFieldAlg (F := F) (G := G) t ht (ι r) = algebraMap R (NoetherField F G) r := by
  let e := AlgEquiv.ofInjective (awayToFieldAlg (F := F) (G := G) t ht)
    (awayToField_injective (F := F) (G := G) t ht)
  have hsymm : ∀ v : ↥(awayToFieldAlg (F := F) (G := G) t ht).range,
      awayToFieldAlg (F := F) (G := G) t ht (e.symm v) = (v : NoetherField F G) := by
    intro v
    have h := AlgEquiv.ofInjective_apply (awayToFieldAlg (F := F) (G := G) t ht)
      (awayToField_injective (F := F) (G := G) t ht) (e.symm v)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨e.symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom F R (NoetherField F G)).codRestrict _ hRQ), fun r => ?_⟩
  exact hsymm ⟨algebraMap R (NoetherField F G) r, hRQ r⟩

end AwayTransport

section BaseMapEndToEnd

variable {F : Type u} [Field F] {G : Type u} [Group G] {t : MvPolynomial G F}

/-- **④ 端到端组装（② 断指）** ✓✅✅：**由 `R` 到 `K` 的 `\mathrm{AlgHom}` 落成** ✓。
**输入** ✓：`t` **不变** 且 `\neq 0` ✓；目标侧 `L'`（含 `G`-作用 ✓）／`K'`（`L'` 的**不动域** ✓ 由 `hfix` 描述 ✓）；
`\varphi : F[x_\sigma] \toₐ[F] L'` **等变** ✓ 且 `\varphi(t)` **可逆** ✓；`R`（`F`-代数 ✓，含 `\mathrm{algebraMap}\ R\ L` ✓）满足
**逐点固定** ✓ 与 **像 ⊆ 局部化的值域** ✓（后者 ＝ **§4.40 的桥** ✓ 的结论形 ✓）。
**结论** ✓：`\exists \Phi' \ \iota \ \Phi` 及其**三条相容等式** ✓ —— **链** ✓：`R \xrightarrow{\iota} \mathrm{Localization.Away}\ t \xrightarrow{\varphi'} L'` 等变 ✓ ⟹ **`\Phi : R \toₐ[F] K'`** ✓
（**合成** ✓：③ 的 `\iota` ✓ ＋ r175④ 的 `\varphi'` 等变 ✓ ＋ `R \subseteq L^G` ✓（经 ② 的单射 ＋ r176②c ✓）＋ r176① 的落地 ✓）。 -/
theorem exists_algHom_base_of_equivariant (ht : ∀ g : G, g • t = t) (ht0 : t ≠ 0)
    {L' : Type u} [Field L'] [Algebra F L'] [MulSemiringAction G L']
    {K' : Type u} [Field K'] [Algebra K' L'] [Algebra F K'] [IsScalarTower F K' L']
    (hfix : ∀ x : L', (∀ g : G, g • x = x) → ∃ k : K', algebraMap K' L' k = x)
    (φ : MvPolynomial G F →ₐ[F] L')
    (heq : ∀ (g : G) (p : MvPolynomial G F), φ (g • p) = g • φ p)
    (hunit : IsUnit (φ t))
    {R : Type u} [CommRing R] [Algebra R (NoetherField F G)] [Algebra F R]
    [IsScalarTower F R (NoetherField F G)]
    (hRG : ∀ (g : G) (r : R), g • algebraMap R (NoetherField F G) r
      = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht0).range) :
    ∃ (Φ' : Localization.Away t →ₐ[F] L') (ι : R →ₐ[F] Localization.Away t) (Φ : R →ₐ[F] K'),
      (∀ p : MvPolynomial G F,
          Φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p) = φ p) ∧
      (∀ r : R, awayToFieldAlg (F := F) (G := G) t ht0 (ι r)
          = algebraMap R (NoetherField F G) r) ∧
      (∀ r : R, algebraMap K' L' (Φ r) = Φ' (ι r)) := by
  let _ := awayMulSemiringAction (F := F) ht
  obtain ⟨Φ', hΦ'⟩ := exists_algHom_away_of_isUnit (F := F) (σ := G) (L := L') φ t hunit
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_image_le (F := F) (G := G) t ht0 hRQ
  have heq' : ∀ (g : G) (x : Localization.Away t), Φ' (g • x) = g • Φ' x :=
    awayLift_equivariant (F := F) (G := G) (t := t) ht φ heq Φ' hΦ'
  have hfixed : ∀ (g : G) (r : R), g • (ι r) = ι r := by
    intro g r
    refine awayToField_injective (F := F) (G := G) t ht0 ?_
    change awayToField (F := F) (G := G) t ht0 (awayRingHom (F := F) ht g (ι r))
      = awayToField (F := F) (G := G) t ht0 (ι r)
    rw [awayToField_smul (F := F) (G := G) (t := t) ht ht0 g (ι r)]
    have h1 : awayToField (F := F) (G := G) t ht0 (ι r)
        = algebraMap R (NoetherField F G) r := hι r
    rw [h1, hRG g r]
  obtain ⟨Φ, hΦ⟩ := exists_algHom_of_equivariant_of_fixed_of_forall_fixed (F := F) (G := G)
    Φ' heq' ι hfixed hfix
  exact ⟨Φ', ι, Φ, hΦ', hι, hΦ⟩

end BaseMapEndToEnd

/-! ## 4.42 **装配 (c) 款装配点接线**：**载体步** ＋ **源侧桥 ⟹ `hRQ`** ＋ **端到端**（第 182 轮）

**⚠ 起点** ✓（**仍压 (c) 款装配点** ✓，**不转项** ✗）：r181 已把靶点细化到**载体步** ✓
（`Q(t) \subseteq \mathrm{range}(\mathrm{awayToFieldAlg}\ t)` ✓）并**精确记录三处障碍与正解方向** ✓（§144.2 ✓）
⟹ 本轮按该方向落地 ✓，并把**源侧桥** ✓（r171 ✓）、**载体步** ✓、**`hRQ`** ✓ 与 **§4.41 的端到端链** ✓
（`\iota` ✓ ＋ `\varphi'` **等变** ✓ ＋ `hfix` **落地** ✓）**接成一条端到端定理** ✓（**断指** ✓）。

**⚠ 四件** ✓：
**①** `adjoin_inv_mem_range_awayToFieldAlg` ✓✅ —— **载体步（集合式）** ✓：
`\forall x \in Q(t),\ x \in \mathrm{range}(\mathrm{awayToFieldAlg}\ t)` ✓。
**⚠ 不可写成 `\subseteq`** ✗（**基准环不可比** ✗：`\mathrm{range}` 是 `\mathrm{Subalgebra}\ F\ \cdot` ✓，
而 `\mathrm{Algebra.adjoin}\ (MvPolynomial\ G\ F)\ \cdot` 给出 `\mathrm{Subalgebra}\ (MvPolynomial\ G\ F)\ \cdot` ✗
—— **r181 实测** ✓）。**四支** ✓：生成元支 ✓（`y = (\mathrm{algebraMap}\ t)^{-1}` ✓）／
`\mathrm{algebraMap}` 支 ✓（由 `awayToField_algebraMap` ✓）／加 ＋ 乘 ✓（子代数封闭 ✓）。
**⚠ 生成元支的 API 墙与正解** ✓（**r181 停止点 ⟹ 本轮落地** ✓）：`\mathrm{Localization.Away}\ t` 是 **`CommRing`**
（**非域** ✗）⟹ **无 `Inv` 实例** ✗ ⟹ 改用 **`Ring.inverse`** ✓（`CommRing` 层 ✓）：
取 `u := \mathrm{algebraMap}\ t` ✓、`hu : \mathrm{IsUnit}\ u` ✓（`IsLocalization.Away.algebraMap_isUnit` ✓）
⟹ `\mathrm{awayToField}\ (\mathrm{Ring.inverse}\ u) \cdot \mathrm{algebraMap}\ t = 1` ✓
（`\mathrm{Ring.inverse\_mul\_cancel}` ✓ ＋ `\leftarrow \mathrm{map\_mul}` ✓ ＋ `awayToField_algebraMap` ✓）
⟹ **`\mathrm{eq\_inv\_of\_mul\_eq\_one\_left}`** ✓ 收口 ✓（**无需**局部化的 `Inv` ✗、**无需**域结构的
`\mathrm{IsUnit.mul\_inv\_cancel}` ✗）。
**②** `exists_invariant_range_awayToFieldAlg` ✓✅ —— **第 2 步** ✓：`R` 的像落在 `F[a](1/s_0)` 内 ✓
⟹ **存在不变 `t \neq 0`** ✓ 使 `R` 的像**整体**落进 `\mathrm{range}(\mathrm{awayToFieldAlg}\ t)` ✓
（**接线** ✓：r171 的 `exists_adjoin_inv_le_away_of_noether` ✓ 给 `t_0` ✓ 与包含 ✓ ⟹ **①** ✓ 给 `\mathrm{range}` 包含 ✓；
**不变性** ✓ 由 r175 的 `exists_invariant_mul` ✓（`Q(t_0) \subseteq Q(t)` ✓）—— **⚠ 源正因此先把 `t` 换成
`\prod_\sigma \sigma(t)`** ✓）。
**③** `exists_algHom_base_of_source_data` ✓✅✅ —— **端到端（断指）** ✓：源侧数据（`hRA` ✓ ＋ `hRG` ✓）
＋ 目标侧 `G`-Galois `L'/K'` ✓ ＋ `hfix` ✓ ⟹ **`\exists z\ b'\ t\ \Phi'\ \iota\ \Phi`** ✓ 及**三条相容等式** ✓
（**链** ✓：**②** ✓ 给 `hRQ` ✓ ⟹ §4.41 的 `exists_algHom_base_of_equivariant` ✓ 收口 ✓；
`z` 与基 `b'` 由 **`lemma52Statement_nonzero_true`** ✓（§4.18 ✓）供给 ✓ ⟹ `\mathrm{noetherEval}\ z` ✓
**等变** ✓（§4.6 ✓）＋ 把 `t` 送到 **单位** ✓）。
**④** `exists_algHom_base_of_source_data_with_image_le` ✓✅ —— **含 `k`-半的单 `t` 版** ✓（**承 §4.41 判据的 `hk` 项** ✓）：
源侧数据 ＋ `S` 在 `R` 上**有限型** ✓ ＋ `S` 到 Noether 域的 `R`-代数映射 ✓ ⟹ 存在**同一个不变 `t`** ✓ 使
**(i)** `R` 落进局部化值域 ✓（⟹ `\Phi : R \toₐ[F] K'` ✓ 与三条相容等式 ✓）**且 (ii)** `S \subset F[x_\sigma](1/t)` ✓
（源「we have that `S \subset F[x_\sigma](1/t)`」✓ 的**库内形式** ✓ —— **⚠ 用点** ✓：`t` ＝ 源「the product of all
the `g`'s and `k`'s」✓；**工序** ✓：`t_0`（r171 ✓）⟹ **`k`-半** ✓（r174 的
`exists_image_le_away_of_finiteType` ✓，得 `t_1` ✓）⟹ **不变化** ✓（r175 ✓）在 `t_0 \cdot t_1` 上 ✓
⟹ `Q(t_0)` 与 `Q(t_1)` **一并**落进 `Q(t)` ✓（`adjoin_away_mono` ✓ 两次 ✓））。

**⚠ 工艺读数（本轮新增一条，已固化）** ✓：**`\mathrm{Ring.inverse}` 替代 `Inv`** ✓ —— `CommRing` 层局部化 ✓ 无 `Inv` ✗，
逆元一律走 `\mathrm{Ring.inverse}` ＋ `IsUnit` 系引理 ✓（`\mathrm{eq\_inv\_of\_mul\_eq\_one\_left}` ✓ 收口 ✓）；
与 r181 记录的**正解方向**逐字一致 ✓，**探针两次内落地** ✓（**未撞第四次墙** ✓）。
**⚠ 登记（余项）** ✗：**①** `hRA` 的**来源** ✓（`R` 的像 ＝ `F[a](1/s_0)` 的**识别** ✓ —— (a) 款侧 ✓）；
**②** `hfix`（`L'^G = K'` ✓，在册 `GaloisFixedSubringHyp` ✓）；**③** `S` 到 Noether 域的**嵌入** ✓
（在册 `noetherEmbedding_gap_registered` ✓）；**④** **张量同构** `L' \simeq S \otimes_R K'` ✓
（(c) 款 `RealizationProperty` 的**余下部分** ✗ —— **下一手** ✓）。 -/

section AdjoinRangeCarrier

variable {F : Type u} [Field F] {G : Type u}

/-- **① 载体步** ✓✅：`Q(t) \subseteq \mathrm{range}(\mathrm{awayToFieldAlg}\ t)`（**集合式** ✓）——
r177 搬运件的输入 `hRQ` 的**供给源** ✓。**⚠ 生成元支无 `Inv` 可用** ✗（局部化是 `CommRing` ✓）
⟹ 用 **`Ring.inverse`** ✓ ＋ **`\mathrm{eq\_inv\_of\_mul\_eq\_one\_left}`** ✓ 收口 ✓。 -/
theorem adjoin_inv_mem_range_awayToFieldAlg (t : MvPolynomial G F) (ht : t ≠ 0) :
    ∀ x ∈ Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)),
      x ∈ (awayToFieldAlg (F := F) (G := G) t ht).range := by
  intro x hx
  refine Algebra.adjoin_induction (p := fun x _ =>
    x ∈ (awayToFieldAlg (F := F) (G := G) t ht).range) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨Ring.inverse (algebraMap (MvPolynomial G F) (Localization.Away t) t), ?_⟩
    have hu : IsUnit (algebraMap (MvPolynomial G F) (Localization.Away t) t) :=
      IsLocalization.Away.algebraMap_isUnit (x := t) (S := Localization.Away t)
    have hmap : awayToField (F := F) (G := G) t ht
        (algebraMap (MvPolynomial G F) (Localization.Away t) t)
        = algebraMap (MvPolynomial G F) (NoetherField F G) t :=
      awayToField_algebraMap (F := F) (G := G) t ht t
    have hmul : awayToField (F := F) (G := G) t ht
          (Ring.inverse (algebraMap (MvPolynomial G F) (Localization.Away t) t))
        * algebraMap (MvPolynomial G F) (NoetherField F G) t = 1 := by
      rw [← hmap, ← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
    exact eq_inv_of_mul_eq_one_left hmul
  · intro a
    exact ⟨algebraMap (MvPolynomial G F) (Localization.Away t) a,
      awayToField_algebraMap (F := F) (G := G) t ht a⟩
  · intro y z _ _ hy hz
    exact add_mem hy hz
  · intro y z _ _ hy hz
    exact mul_mem hy hz

end AdjoinRangeCarrier

section SourceDataRange

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G]

/-- **② 装配点接线（第 2 步）** ✓✅：`R` 的像落在 `F[a](1/s_0)` 内 ⟹ 存在**不变** `t \neq 0`
使 `R` 的像整体落进 `\mathrm{range}(\mathrm{awayToFieldAlg}\ t)` ✓ —— **即 r177 搬运件的输入 `hRQ`** ✓。
**⚠ 不变性不可省** ✗（§4.41 的端到端链要求 `t` **逐点固定** ✓ —— 源「先换成 `\prod_\sigma \sigma(t)`」✓）。 -/
theorem exists_invariant_range_awayToFieldAlg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → NoetherField F G) (s₀ : NoetherField F G) (hs₀ : s₀ ≠ 0)
    {R : Type u} [CommRing R] [Algebra R (NoetherField F G)]
    (hRA : ∀ r : R, algebraMap R (NoetherField F G) r ∈
      Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) :
    ∃ (t : MvPolynomial G F) (ht : t ≠ 0), (∀ g : G, g • t = t) ∧
      ∀ r : R, algebraMap R (NoetherField F G) r ∈
        (awayToFieldAlg (F := F) (G := G) t ht).range := by
  classical
  obtain ⟨t₀, ht₀, hle⟩ := exists_adjoin_inv_le_away_of_noether (F := F) (G := G)
    (L := NoetherField F G) a s₀ hs₀
  obtain ⟨t, ht, htinv, hmono⟩ := exists_invariant_mul (F := F) (G := G) t₀ ht₀
  refine ⟨t, ht, htinv, fun r => ?_⟩
  exact adjoin_inv_mem_range_awayToFieldAlg (F := F) (G := G) t ht _
    (hmono (hle (hRA r)))

end SourceDataRange

section SourceDataEndToEnd

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- **③ 端到端（装配点 · 断指）** ✓✅✅：源侧数据（`R` 的像落在 `F[a](1/s_0)` 内 ✓ ＋ 像**逐点固定** ✓）
＋ 目标侧 `G`-Galois `L'/K'` ✓ ＋ 不动域输入 `hfix` ✓ ⟹ 存在 `z`（`lemma-5.2` ✓）、**不变** `t \neq 0` ✓、
`\Phi'`（局部化提升 ✓）／`\iota`（搬运 ✓）／`\Phi : R \toₐ[F] K'`（**落进不动域** ✓）及**三条相容等式** ✓。
**机制** ✓：② ✓ 给 `hRQ` ✓ ⟹ §4.41 ✓ 收口；`z`／`b'` 由 §4.18 ✓ 供给 ⟹ `\mathrm{noetherEval}\ z` **等变** ✓（§4.6 ✓）。 -/
theorem exists_algHom_base_of_source_data
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → NoetherField F G) (s₀ : NoetherField F G) (hs₀ : s₀ ≠ 0)
    {R : Type u} [CommRing R] [Algebra R (NoetherField F G)] [Algebra F R]
    [IsScalarTower F R (NoetherField F G)]
    (hRA : ∀ r : R, algebraMap R (NoetherField F G) r ∈
      Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
    (hRG : ∀ (g : G) (r : R), g • algebraMap R (NoetherField F G) r
      = algebraMap R (NoetherField F G) r)
    (K' L' : Type u) [Field K'] [Field L'] [Algebra F K'] [Algebra K' L'] [Algebra F L']
    [IsScalarTower F K' L'] [MulSemiringAction G L'] [SMulCommClass G K' L']
    [SMulCommClass G F L'] [Infinite K']
    (b : Module.Basis G K' L') (hb : Function.Bijective (smulAlgEquivHom K' G L'))
    (hfix : ∀ x : L', (∀ g : G, g • x = x) → ∃ k : K', algebraMap K' L' k = x) :
    ∃ (z : L') (b' : Module.Basis G K' L') (t : MvPolynomial G F) (ht : t ≠ 0),
      (∀ g : G, g • t = t) ∧ (∀ σ : G, b' σ = σ • z) ∧
      ∃ (Φ' : Localization.Away t →ₐ[F] L') (ι : R →ₐ[F] Localization.Away t)
        (Φ : R →ₐ[F] K'),
        (∀ p : MvPolynomial G F,
            Φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p)
              = MvPolynomial.aeval (fun σ : G => σ • z) p) ∧
        (∀ r : R, awayToFieldAlg (F := F) (G := G) t ht (ι r)
            = algebraMap R (NoetherField F G) r) ∧
        (∀ r : R, algebraMap K' L' (Φ r) = Φ' (ι r)) := by
  classical
  obtain ⟨t, ht, htinv, hRQ⟩ := exists_invariant_range_awayToFieldAlg (F := F) (G := G)
    a s₀ hs₀ hRA
  obtain ⟨z, b', hb', hne⟩ := lemma52Statement_nonzero_true (F := F) (G := G) K' L' b hb t ht
  have hunit : IsUnit (noetherEval (F := F) z t) := by
    rw [isUnit_iff_ne_zero]
    exact hne
  have heq : ∀ (g : G) (p : MvPolynomial G F),
      noetherEval (F := F) z (g • p) = g • noetherEval (F := F) z p :=
    fun g p => noetherEval_equivariant (F := F) (G := G) z g p
  obtain ⟨Φ', ι, Φ, h1, h2, h3⟩ := exists_algHom_base_of_equivariant (F := F) (G := G)
    (t := t) htinv ht hfix (noetherEval (F := F) z) heq hunit hRG hRQ
  exact ⟨z, b', t, ht, htinv, hb', Φ', ι, Φ, h1, h2, h3⟩

/-- **④ 端到端（含 `k`-半 · 单 `t` 版）** ✓✅：源侧数据 ＋ `S` 在 `R` 上**有限型** ✓ ＋
`S` 到 Noether 域的 `R`-代数映射 ✓ ⟹ 存在**同一个不变** `t \neq 0` 使 **(i)** `R` 的像落进
`\mathrm{range}(\mathrm{awayToFieldAlg}\ t)` ✓（⟹ `\Phi : R \toₐ[F] K'` ✓ 与三条相容等式 ✓）
**且 (ii)** `S` 的像落进 `F[x_\sigma](1/t)` ✓（源「`S \subset F[x_\sigma](1/t)`」✓）。
**⚠ 用点** ✓：`t` ＝ 源「**the product of all the `g`'s and `k`'s**」✓ —— `g`-半（r171 ✓）与
`k`-半（r174 ✓）的分母经 `t_0 \cdot t_1` **并成**一个 `t` ✓（§4.37 ✓）后再**不变化** ✓（§4.39 ✓）。 -/
theorem exists_algHom_base_of_source_data_with_image_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → NoetherField F G) (s₀ : NoetherField F G) (hs₀ : s₀ ≠ 0)
    {R : Type u} [CommRing R] [Algebra R (NoetherField F G)] [Algebra F R]
    [IsScalarTower F R (NoetherField F G)]
    (hRA : ∀ r : R, algebraMap R (NoetherField F G) r ∈
      Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
    (hRG : ∀ (g : G) (r : R), g • algebraMap R (NoetherField F G) r
      = algebraMap R (NoetherField F G) r)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (φS : S →ₐ[R] NoetherField F G)
    (K' L' : Type u) [Field K'] [Field L'] [Algebra F K'] [Algebra K' L'] [Algebra F L']
    [IsScalarTower F K' L'] [MulSemiringAction G L'] [SMulCommClass G K' L']
    [SMulCommClass G F L'] [Infinite K']
    (b : Module.Basis G K' L') (hb : Function.Bijective (smulAlgEquivHom K' G L'))
    (hfix : ∀ x : L', (∀ g : G, g • x = x) → ∃ k : K', algebraMap K' L' k = x) :
    ∃ (z : L') (b' : Module.Basis G K' L') (t : MvPolynomial G F) (ht : t ≠ 0),
      (∀ g : G, g • t = t) ∧ (∀ σ : G, b' σ = σ • z) ∧
      (∀ s : S, φS s ∈ Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G))) ∧
      ∃ (Φ' : Localization.Away t →ₐ[F] L') (ι : R →ₐ[F] Localization.Away t)
        (Φ : R →ₐ[F] K'),
        (∀ p : MvPolynomial G F,
            Φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p)
              = MvPolynomial.aeval (fun σ : G => σ • z) p) ∧
        (∀ r : R, awayToFieldAlg (F := F) (G := G) t ht (ι r)
            = algebraMap R (NoetherField F G) r) ∧
        (∀ r : R, algebraMap K' L' (Φ r) = Φ' (ι r)) := by
  classical
  obtain ⟨t₀, ht₀, hle⟩ := exists_adjoin_inv_le_away_of_noether (F := F) (G := G)
    (L := NoetherField F G) a s₀ hs₀
  have hR₀ : ∀ r : R, algebraMap R (NoetherField F G) r ∈ Algebra.adjoin (MvPolynomial G F)
      ({(algebraMap (MvPolynomial G F) (NoetherField F G) t₀)⁻¹} : Set (NoetherField F G)) :=
    fun r => hle (hRA r)
  obtain ⟨t₁, ht₁, hS₁⟩ := exists_image_le_away_of_finiteType (A := MvPolynomial G F)
    (L := NoetherField F G) (R := R) (S := S) φS t₀ ht₀ hR₀
  obtain ⟨t, ht, htinv, hmono⟩ := exists_invariant_mul (F := F) (G := G) (t₀ * t₁)
    (mul_ne_zero ht₀ ht₁)
  have hmono₀ : Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t₀)⁻¹} : Set (NoetherField F G)) ≤
      Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)) :=
    le_trans (adjoin_away_mono (A := MvPolynomial G F) (L := NoetherField F G) t₀ t₁ ht₁) hmono
  have hmono₁ : Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t₁)⁻¹} : Set (NoetherField F G)) ≤
      Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)) := by
    refine le_trans ?_ hmono
    have h := adjoin_away_mono (A := MvPolynomial G F) (L := NoetherField F G) t₁ t₀ ht₀
    rwa [mul_comm t₁ t₀] at h
  have hRQ : ∀ r : R, algebraMap R (NoetherField F G) r ∈
      (awayToFieldAlg (F := F) (G := G) t ht).range :=
    fun r => adjoin_inv_mem_range_awayToFieldAlg (F := F) (G := G) t ht _
      (hmono₀ (hR₀ r))
  have hS : ∀ s : S, φS s ∈ Algebra.adjoin (MvPolynomial G F)
      ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)) :=
    fun s => hmono₁ (hS₁ s)
  obtain ⟨z, b', hb', hne⟩ := lemma52Statement_nonzero_true (F := F) (G := G) K' L' b hb t ht
  have hunit : IsUnit (noetherEval (F := F) z t) := by
    rw [isUnit_iff_ne_zero]
    exact hne
  have heq : ∀ (g : G) (p : MvPolynomial G F),
      noetherEval (F := F) z (g • p) = g • noetherEval (F := F) z p :=
    fun g p => noetherEval_equivariant (F := F) (G := G) z g p
  obtain ⟨Φ', ι, Φ, h1, h2, h3⟩ := exists_algHom_base_of_equivariant (F := F) (G := G)
    (t := t) htinv ht hfix (noetherEval (F := F) z) heq hunit hRG hRQ
  exact ⟨z, b', t, ht, htinv, hb', hS, Φ', ι, Φ, h1, h2, h3⟩

end SourceDataEndToEnd

/-! ## 4.43 **装配 (c) 款张量侧（第一件）**：**实现映射 ＋ 满射性** ＋ **`\mathrm{finrank}` 收口**（第 183 轮）

**⚠ 起点** ✓（**承 §145.6 第 1 项** ✓，**仍压 (c) 款张量侧** ✓，**不转项** ✗）：r182 已把 (c) 款装配点的 **`R`-侧**接成端到端 ✓
（源侧桥 ✓ ＋ 载体步 ✓ ＋ `hRQ` ✓ ＋ §4.41 链 ✓）；**余** ✓ ＝ **张量侧** ✓（`L' \simeq S \otimes_R K'` ✗，§145.4 ④ ✓）。
本轮把张量侧**压到单一输入** ✓（**秩 `|G|`** ✗）—— 其余全部落为库内定理 ✓。

**⚠ 源判据** ✓（`raw/Saltman1982.tex:652--658` ✓，印 **275** ✓）：「it suffices to define `\phi: S \to L` such that
`\phi` **preserves** `G`, and **`\phi(S)K = L`**」✓ —— 本轮落其**库内形式** ✓（**① 的满射性** ✓；
**⚠ 源判据的"preserves `G`"一款** ✗ 仍需 `S \otimes_R K` 上的 `G`-作用 ✓ —— 在本册 ✓（`RealizationProperty` 的在册项 ① ✓）。

**⚠ 四件** ✓：
**①** `exists_surjective_realizationMap` ✓✅ —— **实现映射 ＋ 满射性** ✓：`\Psi : S_0 \toₐ[F] L'`（`S_0 = \mathrm{Localization.Away}\ t` ✓）
**`R`-线性** ✓ ＋ 共轭族**成基** ✓ ＋ **变量 `x_\sigma` 的取值** ✓ ⟹ 存在 `f : K' \otimes_R S_0 \toₐ[K'] L'` ✓，
**满射** ✓ 且 `f(k \otimes x) = k \bullet \Psi x` ✓（**＝ `\phi(S)K = L`** ✓ 的库内形式 ✓）。
**②** `exists_algHom_away_of_forall_mem_range` ✓✅ —— **搬运件的 `\mathrm{AlgHom}` 形输入版** ✓（**S-版** ✓）：
调用点**不必再手搭** `\mathrm{Algebra}\ S\ L` 与 `\mathrm{IsScalarTower}` 实例 ✗（**§4.41 ③ 的 `R`-版已落** ✓）。
**③** `nonempty_algEquiv_tensorProduct_of_surjective` ✓✅ —— **满射 ＋ `\mathrm{finrank}` 等式 ⟹ 同构** ✓：
`\mathrm{LinearMap.injective\_iff\_surjective\_of\_finrank\_eq\_finrank}` ✓ ＋ `\mathrm{AlgEquiv.ofBijective}` ✓ 收口 ✓
（**无需**手算 `\mathrm{ker}` ✗）；秩等式经 `G`-**基** ✓ 换算为 `\mathrm{finrank}\ L' = |G|` ✓（`\mathrm{Module.finrank\_eq\_card\_basis}` ✓）。
**④** `nonempty_algEquiv_tensorProduct_of_finrank` ✓✅ —— **① ＋ ③ 的合成** ✓：⟹ **张量侧的唯一余 ＝ 秩输入** ✗
（`\mathrm{finrank}_{K'}(K' \otimes_R S_0) = |G|` ✓，＋ 有限型 ✓）。

**⚠ 工艺读数（本轮新增两条）** ✓：
**①** **基变换伴随** ✓：`\mathrm{AlgHom.liftEquiv}` ✓（`(A \toₐ[R] B) \simeq (S \otimes_R A \toₐ[S] B)` ✓）
—— 张量侧映射**不必手搓** ✓；其 `\mathrm{liftEquiv\_tmul}` ✓ 给**逐项公式** ✓
（**⚠ 与 §4.41 同族** ✗✓：目标里出现 `\mathrm{toRingHom}` 强制转换 ⟹ `\mathrm{rw}` 不匹配 ✗ ⟹ **先 `\mathrm{change}` 对齐** ✓，
本节 **2 处** ✓）。
**②** **维数收口** ✓：**满射 ＋ 秩相等 ⟹ 单射** ✓ 走 `\mathrm{LinearMap.injective\_iff\_surjective\_of\_finrank\_eq\_finrank}` ✓
（**⚠ 需 `[\mathrm{FiniteDimensional}]` 两侧** ✓ —— 域侧由 `G`-**基**供给 ✓，张量侧作**显式假设** ✓）。
**⚠ 登记（余项）** ✗：**①** **秩输入** ✓（`\mathrm{finrank}_{K'}(K' \otimes_R S_0) = |G|` ✓ ＝ `S_0` 在 `R` 上**秩 `|G|`** ✓
—— **⚠ 源 `proposition-0-2`(a)** ✓ **只给投射性** ✗（引 [CHR68] p.13 ✓ —— **⚠ 账目更正（第 207 轮** ✓**）**：
精确出处 `[CHR68] p. 13` **仍不在 `raw/`** ✗（L37 已核 ✓），**但**其**用点**已在
`raw/Saltman1978` 印 528（＝ PDF 3 ✓）内**逐字可核** ✓ —— 同页 `thm:1.2` 证明内的 **progenerator** 断言 ✓，
**自引 `[4, p. 81]` ＝ [DI71]** ✓（**非** [CHR68] ✗）；端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）
⟹ **秩款登记为「待回源核」** ✗，**不声称已回源** ✗）；**②** **等变性** ✓（同构须保 `G`-作用 ✓，在册 ✓）。 -/

section RealizationMapTensorSide

open TensorProduct

variable {F : Type u} [Field F] {G : Type u} [Group G]

/-- **① 实现映射 ＋ 满射性** ✓✅（源「`\phi(S)K = L`」✓ 的**库内形式** ✓）：
`\Psi` **`R`-线性** ✓ ＋ 共轭族 `\sigma \bullet z` **成 `K'`-基** ✓ ＋ `x_\sigma` 的取值 ✓ ⟹
`\exists f : K' \otimes_R S_0 \toₐ[K'] L'` ✓，**满射** ✓ 且 `f(k \otimes x) = k \bullet \Psi x` ✓
（**入口 ＝ `\mathrm{AlgHom.liftEquiv}`** ✓ —— 基变换伴随 ✓）。 -/
theorem exists_surjective_realizationMap {t : MvPolynomial G F}
    {R : Type u} [CommRing R] [Algebra R (Localization.Away t)]
    {K' : Type u} [Field K'] [Algebra R K']
    {L' : Type u} [Field L'] [Algebra R L'] [Algebra K' L'] [IsScalarTower R K' L']
    [Algebra F L'] [MulSemiringAction G L']
    (Ψ : Localization.Away t →ₐ[F] L')
    (hΨR : ∀ r : R, Ψ (algebraMap R (Localization.Away t) r) = algebraMap R L' r)
    (z : L') (b' : Module.Basis G K' L') (hb : ∀ σ : G, b' σ = σ • z)
    (hX : ∀ σ : G, Ψ (algebraMap (MvPolynomial G F) (Localization.Away t)
      (MvPolynomial.X σ)) = σ • z) :
    ∃ f : TensorProduct R K' (Localization.Away t) →ₐ[K'] L',
      Function.Surjective f ∧
        ∀ (k : K') (x : Localization.Away t), f (k ⊗ₜ x) = k • Ψ x := by
  let ΨR : Localization.Away t →ₐ[R] L' := { Ψ.toRingHom with commutes' := hΨR }
  let f : TensorProduct R K' (Localization.Away t) →ₐ[K'] L' :=
    ΨR.liftEquiv R K' (Localization.Away t) L'
  have hf : ∀ (k : K') (x : Localization.Away t), f (k ⊗ₜ x) = k • Ψ x := by
    intro k x
    change (ΨR.liftEquiv R K' (Localization.Away t) L') (k ⊗ₜ x) = k • Ψ x
    rw [AlgHom.liftEquiv_tmul]
    rfl
  refine ⟨f, ?_, hf⟩
  have htop : Algebra.adjoin K' (Set.range (fun σ : G => σ • z)) = ⊤ :=
    adjoin_range_smul_eq_top b' z hb
  have hle : (⊤ : Subalgebra K' L') ≤ f.range := by
    rw [← htop]
    refine Algebra.adjoin_le_iff.mpr ?_
    rintro y ⟨σ, rfl⟩
    refine ⟨1 ⊗ₜ[R] algebraMap (MvPolynomial G F) (Localization.Away t) (MvPolynomial.X σ), ?_⟩
    change f (1 ⊗ₜ[R] algebraMap (MvPolynomial G F) (Localization.Away t) (MvPolynomial.X σ))
      = σ • z
    rw [hf, one_smul, hX σ]
  intro y
  obtain ⟨x, hx⟩ := hle trivial
  exact ⟨x, hx⟩

end RealizationMapTensorSide

section AwayTransportAlgHomForm

variable {F : Type u} [Field F] {G : Type u}

/-- **② 搬运件的 `\mathrm{AlgHom}` 形输入版** ✓✅（**S-版** ✓）：`S \toₐ[F] L` 的像 ⊆
`\mathrm{awayToFieldAlg}` 的值域 ✓ ⟹ `\exists \iota_S : S \toₐ[F] \mathrm{Localization.Away}\ t` ✓ 且
`\mathrm{awayToFieldAlg} \circ \iota_S = \varphi_S` ✓。
**⚠ 用点** ✓：调用点**不必再手搭** `\mathrm{Algebra}\ S\ L` 与 `\mathrm{IsScalarTower}\ F\ S\ L` 实例 ✗
（由本件用 `\mathrm{AlgHom}` 自造 ✓ —— **§4.41 ③ 的 `R`-版** ✓ 的 `\mathrm{AlgHom}` 形包装 ✓）。 -/
theorem exists_algHom_away_of_forall_mem_range {t : MvPolynomial G F} (ht : t ≠ 0)
    {S : Type u} [CommRing S] [Algebra F S]
    (φS : S →ₐ[F] NoetherField F G)
    (hRQ : ∀ s : S, φS s ∈ (awayToFieldAlg (F := F) (G := G) t ht).range) :
    ∃ ιS : S →ₐ[F] Localization.Away t,
      ∀ s : S, awayToFieldAlg (F := F) (G := G) t ht (ιS s) = φS s := by
  let _ : Algebra S (NoetherField F G) := φS.toRingHom.toAlgebra
  have _ : IsScalarTower F S (NoetherField F G) :=
    IsScalarTower.of_algebraMap_eq (fun a => (φS.commutes a).symm)
  exact exists_algHom_away_of_image_le (F := F) (G := G) t ht (R := S) hRQ

end AwayTransportAlgHomForm

section FinrankTensorEquiv

open TensorProduct

variable {F : Type u} [Field F] {G : Type u} [Fintype G]

/-- **③ 满射 ＋ `\mathrm{finrank}` 等式 ⟹ 同构** ✓✅：**维数收口** ✓ —— 由
`G`-**基** ✓ 给 `\mathrm{finrank}\ L' = |G|` ✓，秩等式 ⟹ 与 `K' \otimes_R S_0` 同秩 ✓ ⟹
满射的 `K'`-代数映射**单** ✓（`\mathrm{LinearMap.injective\_iff\_surjective\_of\_finrank\_eq\_finrank}` ✓）
⟹ `\mathrm{AlgEquiv.ofBijective}` ✓ 收口 ✓。 -/
theorem nonempty_algEquiv_tensorProduct_of_surjective {t : MvPolynomial G F}
    {R : Type u} [CommRing R] [Algebra R (Localization.Away t)]
    {K' : Type u} [Field K'] [Algebra R K']
    {L' : Type u} [Field L'] [Algebra R L'] [Algebra K' L'] [IsScalarTower R K' L']
    [Module.Finite K' (TensorProduct R K' (Localization.Away t))]
    (b' : Module.Basis G K' L')
    (f : TensorProduct R K' (Localization.Away t) →ₐ[K'] L')
    (hsurj : Function.Surjective f)
    (hfin : Module.finrank K' (TensorProduct R K' (Localization.Away t)) = Fintype.card G) :
    Nonempty (L' ≃ₐ[K'] (TensorProduct R K' (Localization.Away t))) := by
  have _ : Module.Finite K' L' := Module.Finite.of_basis b'
  have hfin' : Module.finrank K' (TensorProduct R K' (Localization.Away t))
      = Module.finrank K' L' := by
    rw [hfin, Module.finrank_eq_card_basis b']
  have hinj : Function.Injective f := by
    have hs : Function.Surjective f.toLinearMap := fun y => hsurj y
    have hi : Function.Injective f.toLinearMap :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := f.toLinearMap) hfin').mpr hs
    intro x y hxy
    exact hi hxy
  exact ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

end FinrankTensorEquiv

section TensorEquivOfFinrank

open TensorProduct

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G]

/-- **④ ① ＋ ③ 的合成** ✓✅（**张量侧的唯一余 ＝ 秩输入** ✗）：把 ① 的满射性与 ③ 的维数收口串起来 ⟹
`L' \simeq K' \otimes_R S_0` ✓ **只差** `\mathrm{finrank}_{K'}(K' \otimes_R S_0) = |G|` ✓（＋ 有限型 ✓）。
**⚠ 登记** ✗：**秩款**（`S_0` 在 `R` 上秩 `|G|` ✓）—— **待回源核** ✗（源 `proposition-0-2`(a) 只给投射性 ✓）。 -/
theorem nonempty_algEquiv_tensorProduct_of_finrank {t : MvPolynomial G F}
    {R : Type u} [CommRing R] [Algebra R (Localization.Away t)]
    {K' : Type u} [Field K'] [Algebra R K']
    {L' : Type u} [Field L'] [Algebra R L'] [Algebra K' L'] [IsScalarTower R K' L']
    [Algebra F L'] [MulSemiringAction G L']
    [Module.Finite K' (TensorProduct R K' (Localization.Away t))]
    (Ψ : Localization.Away t →ₐ[F] L')
    (hΨR : ∀ r : R, Ψ (algebraMap R (Localization.Away t) r) = algebraMap R L' r)
    (z : L') (b' : Module.Basis G K' L') (hb : ∀ σ : G, b' σ = σ • z)
    (hX : ∀ σ : G, Ψ (algebraMap (MvPolynomial G F) (Localization.Away t)
      (MvPolynomial.X σ)) = σ • z)
    (hrank : Module.finrank K' (TensorProduct R K' (Localization.Away t))
      = Fintype.card G) :
    Nonempty (L' ≃ₐ[K'] (TensorProduct R K' (Localization.Away t))) := by
  obtain ⟨f, hsurj, -⟩ :=
    exists_surjective_realizationMap (F := F) (G := G) (t := t) Ψ hΨR z b' hb hX
  exact nonempty_algEquiv_tensorProduct_of_surjective b' f hsurj hrank

end TensorEquivOfFinrank

/-! ## 4.44 **装配 (c) 款张量侧（第二件 · 收口）**：**等变性** ＋ **秩输入内部供给** ⟹ **等变同构**（第 184 轮）

**⚠ 起点** ✓（**承 §146.6 第 1 项** ✓，**仍压 (c) 款张量侧** ✓，**不转项** ✗）：r183 把张量侧压到**两个输入** ✗ ——
**秩** ✗（`\mathrm{finrank}_{K'}(K' \otimes_R S_0) = |G|` ✓，§146.4 ① ✓）与 **等变性** ✗（§146.4 ② ✓）。
本轮**两件都落** ✓：**秩** ✓ 由 `GaloisAlgebra_ABGV52.lean` 的
`\mathrm{finrank\_eq\_card\_of\_isGaloisWithGroup}` ✓（**通用档** ✓ ＝ **本册判据** ✓ 的直接推论 ✓，
**不用外部源** ✗）**内部供给** ✓；**等变性** ✓ 由 **①** ✓ 落地 ✓。

**⚠ 两件** ✓：
**①** `realizationMap_equivariant` ✓✅ —— **实现映射等变** ✓：`G` 沿 **`S_0`-因子**作用 ✓ ＋ `\Psi` **等变** ✓
＋ `K'`-纯量与 `G` **交换** ✓ ⟹ `f(g \bullet z) = g \bullet f z` ✓（**逐项** ✓：
`f(g \bullet (k \otimes x)) = k \bullet \Psi(g \bullet x) = k \bullet (g \bullet \Psi x) = g \bullet (k \bullet \Psi x)` ✓）；
**②** `exists_equivariant_algEquiv_tensorProduct_of_galois` ✓✅✅ —— **等变同构（张量侧收口 · 断指）** ✓：
输入 ＝ r183 ①（`\Psi` ✓／`h\Psi_R` ✓／`z` ✓／基 `b'` ✓／`hX` ✓）＋ `G`-**作用** ✓（含逐项公式 `hact` ✓）
＋ **`A := K' \otimes_R S_0` 的 `G`-Galois 性** ✓（**（b）款** ✓ 供给 ✓）＋ 有限型 ✓ ＋ 非平凡 ✓ ⟹
`\exists e : L' \simeq_{K'} (K' \otimes_R S_0)` ✓ 且 **`e(g \bullet y) = g \bullet e y`** ✓
（**⚠ 秩假设已消失** ✓ —— 由 `\mathrm{finrank\_eq\_card\_of\_isGaloisWithGroup}` ✓ 内部给出 ✓）。

**⚠ 登记（余项）** ✗：**端到端打包** ✓（把 r182 ③ 的源侧数据 ✓ 直接接进本件 ✓ —— **并入下一轮** ✓）；
**`\mathrm{GaloisProjectiveHyp}`** ✓ ＋ **`A` 的非平凡性** ✓ 由 (b) 款 ✓／装配点 ✓ 供给 ✓。

**⚠ 工艺读数（本轮新增两条）** ✓：
**①** **`\mathrm{change}` 对齐 `\mathrm{AlgEquiv}` 强制转换** ✓（`\mathrm{hsymm}` 一处 ✓ —— 与 §4.41／§4.43 **同族** ✓）；
**②** **逆同构的等变性由 `f` 的单性搬运** ✓（`\mathrm{refine}\ \mathrm{hinj}\ ?_` ✓ ＋ `\mathrm{hsymm}` ✓
—— **不必**在 `L'` 上重跑张量归纳 ✓）；**⚠ 归纳次序** ✗✓：`\mathrm{TensorProduct.induction\_on}` 的**后两槽**是
**先 `\mathrm{tmul}` 后 `\mathrm{add}`** ✗（**实测** ✓ —— 写反则 elaboration 报 `HSMul` 缺 ✓）。 -/

section RealizationMapEquivariant

open TensorProduct

variable {F : Type u} [Field F] {G : Type u} [Group G]

/-- **① 实现映射等变** ✓✅：`\Psi` **等变** ✓ ＋ `G` 沿 **`S_0`-因子**作用 ✓（逐项公式 `hact` ✓）
＋ `K'`-纯量与 `G` **交换** ✓ ⟹ r183 ① 的映射 `f` **等变** ✓（**源 `definition-1-1`(c) 的
"preserving the respective `G` actions"** ✓ 的**映射侧** ✓）。 -/
theorem realizationMap_equivariant {t : MvPolynomial G F}
    {R : Type u} [CommRing R] [Algebra R (Localization.Away t)]
    {K' : Type u} [Field K'] [Algebra R K']
    {L' : Type u} [Field L'] [Algebra R L'] [Algebra K' L'] [IsScalarTower R K' L']
    [Algebra F L'] [MulSemiringAction G L'] [SMulCommClass G K' L']
    [MulSemiringAction G (Localization.Away t)]
    [MulSemiringAction G (TensorProduct R K' (Localization.Away t))]
    (hact : ∀ (g : G) (k : K') (x : Localization.Away t),
      g • (k ⊗ₜ[R] x) = k ⊗ₜ[R] (g • x))
    (Ψ : Localization.Away t →ₐ[F] L')
    (f : TensorProduct R K' (Localization.Away t) →ₐ[K'] L')
    (hf : ∀ (k : K') (x : Localization.Away t), f (k ⊗ₜ[R] x) = k • Ψ x)
    (hΨG : ∀ (g : G) (x : Localization.Away t), Ψ (g • x) = g • Ψ x) :
    ∀ (g : G) (z : TensorProduct R K' (Localization.Away t)), f (g • z) = g • f z := by
  intro g z
  exact TensorProduct.induction_on z
    (by simp)
    (fun k x => by
      rw [hact g k x, hf, hf, hΨG g x]
      exact (smul_comm g k (Ψ x)).symm)
    (fun x y hx hy => by simp only [smul_add, map_add, hx, hy])

end RealizationMapEquivariant

section EquivariantTensorEquiv

open TensorProduct

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G]

/-- **② 等变同构（张量侧收口 · 断指）** ✓✅✅：**由 `\Psi` 等变、`A := K' \otimes_R S_0` 为 `G`-Galois
（（b）款 ✓）、有限型、非平凡** ✓ ⟹ `\exists e : L' \simeq_{K'} A` ✓ 且 **等变** ✓（`e(g \bullet y) = g \bullet e y` ✓）。
**⚠ 秩假设已消失** ✓（**① 的推广** ✓：`\mathrm{finrank\_eq\_card\_of\_isGaloisWithGroup}` ✓ 内部给出
`\mathrm{finrank}_{K'} A = |G|` ✓ ⟹ 满射 ＋ 同秩 ⟹ 单射 ✓ ⟹ `\mathrm{AlgEquiv}` ✓）。 -/
theorem exists_equivariant_algEquiv_tensorProduct_of_galois {t : MvPolynomial G F}
    {R : Type u} [CommRing R] [Algebra R (Localization.Away t)]
    {K' : Type u} [Field K'] [Algebra R K']
    {L' : Type u} [Field L'] [Algebra R L'] [Algebra K' L'] [IsScalarTower R K' L']
    [Algebra F L'] [MulSemiringAction G L'] [SMulCommClass G K' L']
    [MulSemiringAction G (Localization.Away t)]
    [MulSemiringAction G (TensorProduct R K' (Localization.Away t))]
    (hact : ∀ (g : G) (k : K') (x : Localization.Away t),
      g • (k ⊗ₜ[R] x) = k ⊗ₜ[R] (g • x))
    (hK'G : ∀ (g : G) (k : K') (z : TensorProduct R K' (Localization.Away t)),
      g • (k • z) = k • (g • z))
    (hgalK' : BTier.IsGaloisWithGroup K' (TensorProduct R K' (Localization.Away t)) G hK'G)
    [Module.Finite K' (TensorProduct R K' (Localization.Away t))]
    [Nontrivial (TensorProduct R K' (Localization.Away t))]
    (Ψ : Localization.Away t →ₐ[F] L')
    (hΨR : ∀ r : R, Ψ (algebraMap R (Localization.Away t) r) = algebraMap R L' r)
    (hΨG : ∀ (g : G) (x : Localization.Away t), Ψ (g • x) = g • Ψ x)
    (z : L') (b' : Module.Basis G K' L') (hb : ∀ σ : G, b' σ = σ • z)
    (hX : ∀ σ : G, Ψ (algebraMap (MvPolynomial G F) (Localization.Away t)
      (MvPolynomial.X σ)) = σ • z) :
    ∃ e : L' ≃ₐ[K'] (TensorProduct R K' (Localization.Away t)),
      ∀ (g : G) (y : L'), e (g • y) = g • e y := by
  obtain ⟨f, hsurj, hf⟩ :=
    exists_surjective_realizationMap (F := F) (G := G) (t := t) Ψ hΨR z b' hb hX
  have hfG : ∀ (g : G) (w : TensorProduct R K' (Localization.Away t)), f (g • w) = g • f w :=
    realizationMap_equivariant (F := F) (G := G) (t := t) hact Ψ f hf hΨG
  have _ : Module.Finite K' L' := Module.Finite.of_basis b'
  have hrank : Module.finrank K' (TensorProduct R K' (Localization.Away t))
      = Fintype.card G :=
    BTier.finrank_eq_card_of_isGaloisWithGroup hK'G hgalK'
  have hfin' : Module.finrank K' (TensorProduct R K' (Localization.Away t))
      = Module.finrank K' L' := by
    rw [hrank, Module.finrank_eq_card_basis b']
  have hinj : Function.Injective f := by
    have hs : Function.Surjective f.toLinearMap := fun y => hsurj y
    have hi : Function.Injective f.toLinearMap :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := f.toLinearMap) hfin').mpr hs
    intro x y hxy
    exact hi hxy
  have hsymm : ∀ w : L',
      f ((AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm w) = w := by
    intro w
    change (AlgEquiv.ofBijective f ⟨hinj, hsurj⟩)
      ((AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm w) = w
    rw [AlgEquiv.apply_symm_apply]
  refine ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, ?_⟩
  intro g y
  refine hinj ?_
  rw [hsymm (g • y), hfG, hsymm y]

end EquivariantTensorEquiv

/-! ## 4.45 **装配 (c) 款张量侧 · 端到端打包**：**(b) 款 ＋ 秩 ＋ 作用全内部** ⟹ **等变同构**（第 185 轮）

**⚠ 起点** ✓（**承 §147.6 第 1 项** ✓，**仍压 (c) 款张量侧** ✓，**不转项** ✗）：r184 已把张量同构落为库内定理 ✓，
但其**输入**仍要调用点自备：`A := K' \otimes_R S_0` 的 `G`-Galois 性 ✗、`G`-作用与其逐项公式 ✗
（有限型 ✓／非平凡 ✓ 亦须自备 ✓）。本轮把这些**全部内部化** ✓。

**⚠ 一件** ✓：`exists_equivariant_algEquiv_tensorProduct_of_galoisBaseChange` ✓✅✅ ——
**输入** ✓ ＝ `S_0/R` 的 `G`-Galois 性 ✓ ＋ `\mathrm{GaloisProjectiveHyp}` ✓ ＋ `\Psi`（`R`-**线性** ✓ ＋ **等变** ✓）
＋ 共轭族数据 ✓；**内部** ✓ ＝ r180 的 `\mathrm{galoisBaseChange\_tensorLeft}` ✓（**(b) 款** ✓：`A`-Galois 性 ✓
＋ 作用 ✓ ＋ 相容项 ✓ —— **三行全内部** ✓）＋ `\mathrm{tensorActHom}` 的**逐项公式** ✓ ＋
`\mathrm{Module.Finite.base\_change}` ✓（有限型由 `\mathrm{GaloisProjectiveHyp}` ✓ 供 ✓）＋ r184 ② ✓
⟹ `\exists e : L' \simeq_{K'} A` ✓ 且 **等变** ✓。

**🔴 ⚠ 审计结论（**先审后落** ✓，**本轮实测** ✗）**：**为何不能把 `t` 与 `\Phi` 全内部化** ✗
（**实例同一性障碍** ✗）：张量侧的事实（`G`-作用 ✗／`A` 的 Galois 性 ✗／`[\mathrm{Nontrivial}\ A]` ✗）
**必须在陈述处**就 `[\mathrm{Algebra}\ R\ K']` **成立** ✓，而该结构由 §4.41 链**产出** ✗ ⟹
**同一语句内**既产出该结构、又对**产出后**的结构加前提 ✗ **不可写** ✗（`\mathrm{TensorProduct}` 的**类型项**
随实例变 ✗，前提的真值也随之变 ✗）。**⟹ 正解 ＝ 本件** ✓（`[\mathrm{Algebra}\ R\ K']` 作**输入** ✓，
`R`-线性以 `\mathrm{algebraMap}` **形**给出 ✓）：**调用点配方** ✓（**两行** ✓）——
**①** §4.41 链给 `\Phi` ✓；**②** `letI := \Phi.\mathrm{toRingHom.toAlgebra}` ✓；**③** `h\Psi_R` 由链的**第三式**
（`\mathrm{algebraMap}\ K'\ L' \circ \Phi = \Phi' \circ \iota` ✓）＋ `\mathrm{IsScalarTower}\ R\ K'\ L'` ✓ 得 ✓。
**⚠ 口径** ✓：**"同一性方程"** ✓（而非"零手写" ✗）是本件**可陈述性**的**代价** ✓ —— **如实登记** ✗，
**不声称**已达成"调用点零手写" ✗。

**⚠ 工艺读数（本轮新增两条）** ✓：
**① 档位再现** ✗✓：`\mathrm{tensorMulSemiringAction}`／`\mathrm{tensorActHom}`／`\mathrm{tensorAct\_smul\_comm}`
为 **`Type` 档** ✗（**承 r180** ✓）⟹ **本节写 `Type`** ✓（`\mathrm{Type}\ u` 档**实测报宇宙不匹配** ✗）；
**② `\mathrm{galoisBaseChange\_tensorLeft}` 的结论自带 `letI`** ✓ ⟹ 调用点**先 `letI` 同一项** ✓ 即可对接 ✓
（**无需**重演三行 ✗）。 -/

section TensorEndToEnd

open TensorProduct

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G]

/-- **(c) 款张量侧 · 端到端打包** ✓✅✅：`S_0/R` 的 `G`-Galois 性 ✓ ＋ `\mathrm{GaloisProjectiveHyp}` ✓
＋ `\Psi`（`R`-**线性** ✓ ＋ **等变** ✓）＋ 共轭族数据 ✓ ⟹ **等变同构** `L' \simeq_{K'} (K' \otimes_R S_0)` ✓
—— **（b）款的 `A`-Galois 性 ＋ `G`-作用 ＋ 相容项 ＋ 有限型全在证明内** ✓
（**⚠ 口径** ✓：`[\mathrm{Algebra}\ R\ K']` 为**输入** ✓，`R`-线性以 `\mathrm{algebraMap}` 形给出 ✓ ——
**实例同一性障碍** ✗ 使"全内部化"不可陈述 ✗，配方见 §4.45 节头 ✓）。
**（r192 追加）** ✓：`[\mathrm{Nontrivial}\ (K' \otimes_R S_0)]` **亦已内部产出** ✓
（由 `\Psi` 的 `R`-代数同态形 ✓ 经 `\mathrm{nontrivial\_tensorProduct\_of\_algHom}` ✓，基变换伴随路线 ✓）
⟹ 本件**调用点零手写** ✓（旧配方中手搭 `\mathrm{liftEquiv}` 块 ✗→✓）。 -/
theorem exists_equivariant_algEquiv_tensorProduct_of_galoisBaseChange
    {t : MvPolynomial G F}
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    {K' : Type} [Field K'] [Algebra R K'] [Algebra F K'] [IsScalarTower F R K']
    {L' : Type} [Field L'] [Algebra K' L'] [Algebra F L'] [Algebra R L']
    [IsScalarTower R K' L'] [IsScalarTower F K' L']
    [MulSemiringAction G L'] [SMulCommClass G K' L']
    (Ψ : Localization.Away t →ₐ[F] L')
    (hΨR : ∀ r : R, Ψ (algebraMap R (Localization.Away t) r) = algebraMap R L' r)
    (hΨG : ∀ (g : G) (x : Localization.Away t), Ψ (g • x) = g • Ψ x)
    {z : L'} {b' : Module.Basis G K' L'} (hb : ∀ σ : G, b' σ = σ • z)
    (hX : ∀ σ : G, Ψ (algebraMap (MvPolynomial G F) (Localization.Away t)
      (MvPolynomial.X σ)) = σ • z) :
    ∃ e : L' ≃ₐ[K'] (TensorProduct R K' (Localization.Away t)),
      letI := BTier.tensorMulSemiringAction (R := R) (T := K') (S := Localization.Away t) hRG
      ∀ (g : G) (y : L'), e (g • y) = g • e y := by
  let _ := BTier.tensorMulSemiringAction (R := R) (T := K') (S := Localization.Away t) hRG
  -- **非平凡性内部导出** ✓（r192：调用点零手写 ✓；来源 ＝ `Ψ` 的 `R`-代数同态形 ✓）
  let _ : Nontrivial (TensorProduct R K' (Localization.Away t)) :=
    BTier.nontrivial_tensorProduct_of_algHom (R := R) (S := Localization.Away t) (K := K') (L := L')
      { Ψ.toRingHom with commutes' := hΨR }
  have hact : ∀ (g : G) (k : K') (x : Localization.Away t),
      g • (k ⊗ₜ[R] x) = k ⊗ₜ[R] (g • x) := by
    intro g k x
    change BTier.tensorActHom (T := K') hRG g (k ⊗ₜ[R] x) = k ⊗ₜ[R] (g • x)
    rw [BTier.tensorActHom, Algebra.TensorProduct.map_tmul]
    rfl
  have hK'G : ∀ (g : G) (k : K') (w : TensorProduct R K' (Localization.Away t)),
      g • (k • w) = k • (g • w) := fun g k w => BTier.tensorAct_smul_comm hRG g k w
  have hgalK' : BTier.IsGaloisWithGroup K' (TensorProduct R K' (Localization.Away t)) G hK'G :=
    BTier.galoisBaseChange_tensorLeft hRG hgal hProj
  have _ : Module.Finite R (Localization.Away t) := (hProj hgal).1
  exact exists_equivariant_algEquiv_tensorProduct_of_galois (F := F) (G := G) (t := t)
    hact hK'G hgalK' Ψ hΨR hΨG z b' hb hX

end TensorEndToEnd

/-! ## 4.46 **装配 (c) 款收口**：**`\exists \varphi : R \toₐ[F] K` ＋ 保作用同构**（第 186 轮）

**⚠ 起点** ✓（**承 §148.6 第 1 项** ✓，**仍压 (c) 款** ✓，**不转项** ✗）：§4.45 已把张量侧打包 ✓，
但 `\Psi`／`h\Psi_R`／`h\Psi_G`／`z`／基／`hX` **六项仍要调用点自备** ✗。本轮把它们**全部内部化** ✓，
并**产出 `\varphi`** ✓（`RealizationProperty` 的结论形 ✓：`\exists \varphi` ＋ `\mathrm{letI}` 结构 ✓）。

**⚠ 两件** ✓：
**①** `awayLift_equivariant_of_algebraMap` ✓✅ —— **通用档** ✓：r175④ 的
`\mathrm{awayLift\_equivariant}` **固定在规范作用上** ✗，而装配点的作用实例是**输入** ✗ ⟹ 本件把前提放宽为
「作用与 `\mathrm{algebraMap}` **相容**」✓（证明同 r175④ ✓，只换一处 ✓）；
**②** `exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data` ✓✅✅ —— **收口** ✓：
由**目标 Galois 数据** ✓（`b`／`hb`／`hfix` ✓）＋ **源侧桥** ✓（`hRQ` ✓）＋ `S_0/R` 的 Galois 性 ✓ ＋ `\mathrm{GaloisProjectiveHyp}` ✓
⟹ **`\exists \varphi : R \toₐ[F] K`** ✓ ＋ **保作用的** `L \simeq_K (K \otimes_R S_0)` ✓
（`\varphi := \Phi_0` ✓，其结构经 `\mathrm{letI}` 引入 ✓；**六项输入全内部** ✓）。

**🔴 ⚠ 审计结论（本轮实测，**三处实例同一性** ✗✓）**：
**(a)** **作用实例** ✗：输入作用 ≠ 规范 `\mathrm{awayMulSemiringAction}` ✗ ⟹ `\mathrm{awayLift\_equivariant}` **不可直接用** ✗
⟹ **正解 ＝ ①（通用档化）** ✓；
**(b)** **`\Phi` 不可作输入** ✗：链**产出** `\Phi_0` ✓，而输入 `\Phi` ＋ `h\Phi` **无法与 `\Phi_0` 同一** ✗
（`h\Phi` 只联系**输入** `\Phi` ✗）⟹ **正解 ＝ 让收口件自己产出 `\varphi`** ✓ 并把 `\mathrm{letI}` 结构放进**结论** ✓
（与 `\mathrm{RealizationProperty}` 同法 ✓）；
**(c)** **`\mathrm{Nontrivial}` 与两条塔** ✓：`[\mathrm{Nontrivial}\ A]` ✗ 与 `\mathrm{IsScalarTower}\ R\ K\ L`／`F\ R\ K` ✗
**均内部导出** ✓（前者由 `A \toₐ[K] L` 的**单位性** ✓：`1 \neq 0` 沿单射搬到 `L` ✓；后者由 `\Phi_0` 的 `\mathrm{commutes}` ✓）。

**⚠ 工艺读数（本轮新增两条）** ✓：**①** `\mathrm{letI}`／`\mathrm{haveI}` 在 **Prop 值处**可写 `\mathrm{let}`／`\mathrm{have}` ✓
（**(55)** ✓，消 linter 警告 ✓，实测实例仍可合成 ✓）；**②** **`\mathrm{RingHom.toAlgebra}` 的 `\mathrm{algebraMap}` 是 `\mathrm{rfl}`** ✓
⟹ `h\Psi_R` 的收尾**恰为 `\mathrm{rfl}`** ✓（`\mathrm{algebraMap}\ R\ L\ r \equiv \mathrm{algebraMap}\ K\ L\ (\Phi_0\ r)` ✓）。
**⚠ 登记（余项）** ✗：**①** `hact\_{\rm map}` ✓（作用与 `\mathrm{algebraMap}` 相容 ✓ —— 装配点由
`\mathrm{awayRingHom\_algebraMap}` ✓ **一行供给** ✓）；**②** `hS_0R` ✓（`R`-结构 ＝ 嵌入 ✓ —— (a) 款侧识别 ✓，在册 ✓）。 -/

section LiftEquivariantGeneral

variable {F : Type} [Field F] {G : Type} [Group G]

/-- **通用档**：局部化提升的等变性（**作用实例任意** ✓，只要与 `\mathrm{algebraMap}` 相容 ✓）——
r175④ 的 `\mathrm{awayLift\_equivariant}` 固定在**规范作用**上 ✗，而装配点的作用实例是**输入** ✗
⟹ 本件把该前提放宽 ✓（证明同 r175④ ✓，只把 `\mathrm{awayRingHom\_algebraMap}` 换成 `\mathrm{hact\_map}` ✓）。 -/
theorem awayLift_equivariant_of_algebraMap {t : MvPolynomial G F}
    {L' : Type} [Field L'] [Algebra F L'] [MulSemiringAction G L']
    [MulSemiringAction G (Localization.Away t)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (φ : MvPolynomial G F →ₐ[F] L')
    (heq : ∀ (g : G) (p : MvPolynomial G F), φ (g • p) = g • φ p)
    (φ' : Localization.Away t →ₐ[F] L')
    (hφ : ∀ p : MvPolynomial G F,
      φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p) = φ p) :
    ∀ (g : G) (x : Localization.Away t), φ' (g • x) = g • φ' x := by
  intro g x
  have h2 : (φ'.toRingHom.comp
        (MulSemiringAction.toRingEquiv G (Localization.Away t) g).toRingHom)
      = ((MulSemiringAction.toRingEquiv G L' g).toRingHom.comp φ'.toRingHom) := by
    apply IsLocalization.ringHom_ext (R := MvPolynomial G F) (S := Localization.Away t)
      (Submonoid.powers t)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    show φ' (g • algebraMap (MvPolynomial G F) (Localization.Away t) p)
      = g • φ' (algebraMap (MvPolynomial G F) (Localization.Away t) p)
    rw [hact_map g p, hφ, hφ, heq g p]
  exact congrFun (congrArg DFunLike.coe h2) x

end LiftEquivariantGeneral

section SourceDataCapstone

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **探针 v2（(c) 款收口）**：由**目标 Galois 数据** ＋ **源侧桥** ＋ `S_0/R` 的 Galois 性 ⟹
**`\exists \varphi : R \toₐ[F] K`** ＋ **保作用的同构** `L \simeq_K (K \otimes_R S_0)` ✓
（`\varphi` 的结构经 `letI` 引入 ✓；`\mathrm{Nontrivial}` 与两条塔**内部导出** ✓）。 -/
theorem exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    {K : Type} [Field K] [Algebra F K]
    {L : Type} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L] [Infinite K]
    (b : Module.Basis G K L) (hb : Function.Bijective (smulAlgEquivHom K G L))
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x) :
    ∃ φ : R →ₐ[F] K,
      letI : Algebra R K := φ.toRingHom.toAlgebra
      letI : Algebra R L := ((algebraMap K L).comp φ.toRingHom).toAlgebra
      letI := BTier.tensorMulSemiringAction (R := R) (T := K) (S := Localization.Away t) hRG
      ∃ e : L ≃ₐ[K] (TensorProduct R K (Localization.Away t)),
        ∀ (g : G) (y : L), e (g • y) = g • e y := by
  -- ① 源 `lemma-5.2` 真形
  obtain ⟨z, b', hb', hne⟩ := lemma52Statement_nonzero_true (F := F) (G := G) K L b hb t ht
  have hunit : IsUnit (noetherEval (F := F) z t) := by
    rw [isUnit_iff_ne_zero]
    exact hne
  have heq : ∀ (g : G) (p : MvPolynomial G F),
      noetherEval (F := F) z (g • p) = g • noetherEval (F := F) z p :=
    fun g p => noetherEval_equivariant (F := F) (G := G) z g p
  -- ② §4.41 链（同一 `t`）
  obtain ⟨Φ', ι, Φ₀, h1, h2, h3⟩ := exists_algHom_base_of_equivariant (F := F) (G := G)
    (t := t) htinv ht hfix (noetherEval (F := F) z) heq hunit hRGpoint hRQ
  -- ③ `φ := Φ₀` 的结构进作用域
  let _ : Algebra R K := Φ₀.toRingHom.toAlgebra
  let _ : Algebra R L := ((algebraMap K L).comp Φ₀.toRingHom).toAlgebra
  have _ : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have _ : IsScalarTower F R K := IsScalarTower.of_algebraMap_eq (fun a => (Φ₀.commutes a).symm)
  -- ④ `hX`／`hΨG`／`hΨR`
  have hX : ∀ σ : G,
      Φ' (algebraMap (MvPolynomial G F) (Localization.Away t) (MvPolynomial.X σ)) = σ • z := by
    intro σ
    rw [h1]
    exact noetherEval_X (F := F) z σ
  have hΨG : ∀ (g : G) (x : Localization.Away t), Φ' (g • x) = g • Φ' x :=
    awayLift_equivariant_of_algebraMap (F := F) (G := G) (t := t) hact_map
      (noetherEval (F := F) z) heq Φ' h1
  have hι : ∀ r : R, ι r = algebraMap R (Localization.Away t) r := by
    intro r
    apply awayToField_injective (F := F) (G := G) t ht
    change awayToFieldAlg (F := F) (G := G) t ht (ι r)
      = awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
    rw [h2 r, hS₀R r]
  have hΨR : ∀ r : R, Φ' (algebraMap R (Localization.Away t) r) = algebraMap R L r := by
    intro r
    rw [← hι r, ← h3 r]
    rfl
  -- ⑤ `Nontrivial`：**已由 §4.45 打包内部产出** ✓（r192 起**调用点零手写** ✓ —— 不再手搭 `liftEquiv` 块 ✗→✓）
  -- ⑥ §4.45 收口
  obtain ⟨e, he⟩ := exists_equivariant_algEquiv_tensorProduct_of_galoisBaseChange (F := F) (G := G)
    (t := t) hRG hgal hProj Φ' hΨR hΨG hb' hX
  exact ⟨Φ₀, e, he⟩

end SourceDataCapstone

/-! ## 4.47 **装配 (c) 款 · 源侧接线**：**载体具体化 ⟹ 三项在册输入按构造消掉**（第 187 轮）

**⚠ 起点** ✓（**承 §149.6 第 1 项** ✓，**仍压 (c) 款** ✓，**不转项** ✗）：§4.46 已产出 `\varphi` ＋ 保作用同构 ✓，
但其源侧三项前提仍由调用点自备 ✗：`hRA` ✗（`R` 的像 ＝ `F[a](1/s_0)` ✓）、
`hRQ` ✗（`R` 的像落在 `\mathrm{range}(\mathrm{awayToFieldAlg}\ t\ h_t)` ✓）、`hRGpoint` ✗（`R` 的像 `G`-不动 ✓）。

**⚠ 两件** ✓：
**①** `smul_eq_self_of_mem_adjoin_of_fixed` ✓✅ —— **不动子代数判定** ✓：由 **`G`-不动生成元** ✓
（`a_i` ✓／`s_0` ✓／`s_0^{-1}` ✓）生成的 `F`-子代数，其元素皆 `G`-不动 ✓
（`\mathrm{Algebra.adjoin\_induction}` **四支** ✓；**逆元支** ✓：`\mathrm{eq\_inv\_of\_mul\_eq\_one\_left}` ＋
`\mathrm{inv\_mul\_cancel\_0}` ✓，并**分 `s_0 = 0` 两支** ✓ 以免除 `s_0 \neq 0` 前提 ✗（**最弱假设表** ✓）；
`\mathrm{algebraMap}` 支 ✓：`\mathrm{smul\_C\_noether}` ✓ ＋ `\mathrm{smul\_algebraMap\_noether}` ✓）；
**②** `exists_algHom_and_equivariant_algEquiv_tensorProduct_of_subalgebra` ✓✅✅ —— **源侧装配** ✓：
`R` 取**具体载体** `S := \hookrightarrow`（Noether 域的 `F`-子代数 ✓）⟹ **`hRA`** ✓（`S` 定义即得 ✓ ——
元素即 `S` 的元素 ✓）、**`hRQ`** ✓（由 `hle` ＋ §4.42 ① 的**载体步** `\mathrm{adjoin\_inv\_mem\_range\_awayToFieldAlg}` ✓ **内部导出** ✓）、
**`hRGpoint`** ✓（由 `hS_{\rm fix}` ✓ **内部导出** ✓）—— **三项在册输入按构造消掉** ✓；再调 **§4.46** ✓ ⟹
`\exists \varphi : \hookrightarrow K` ＋ **保作用同构** ✓。

**⚠ 口径** ✓：本件把 `R` **具体化**为子代数 ✓（而非抽象环 ✓）—— 代价是 `R` **不再是自由输入** ✓，
收益是 `hRA`／`hRQ`／`hRGpoint` **三项从"在册外部输入"变为"构造内定理"** ✓；
**⚠ 剩余在册项** ✗（**如实登记** ✓，**不隐藏** ✗）：`hle` ✓（由 r171 源侧桥供给 ✓）、
`[\mathrm{Algebra}\ \hookrightarrow S_0]` ✓（**(a) 款**识别 ✓）、`hact_{\rm map}` ✓（**一行** ✓：`\mathrm{awayRingHom\_algebraMap}` ✓）、
`hS_0R` ✓（同上，**一行** ✓：搬运件的刻画式 ✓）、`hgal`／`hProj` ✓（**(b) 款** ✓ ＋ 源 `proposition-0-2(a)` ✓）、
`hfix` ✓（`\mathrm{GaloisFixedSubringHyp}` ✓）。

**⚠ 工艺读数（本轮新增一条）** ✓：**逆元支的最弱假设表** ✓ —— `g \bullet s_0^{-1} = (g \bullet s_0)^{-1}` 可由
`\mathrm{eq\_inv\_of\_mul\_eq\_one\_left}` ＋ `\mathrm{inv\_mul\_cancel\_0}` 得 ✓，**无需 `s_0 \neq 0`** ✗
（`s_0 = 0` 支由 `\mathrm{inv\_zero}` ＋ `\mathrm{smul\_zero}` 直接闭合 ✓）。 -/

section FixedAdjoin

variable {F : Type} [Field F] {G : Type} [Group G]

/-- **探针①**：**不动子代数判定** ✓ —— 由 `G`-不动生成元生成的 `F`-子代数，其元素皆 `G`-不动 ✓
（`\mathrm{Algebra.adjoin\_induction}` 四支 ✓：生成元 ✓（`a_i` ✓／`s_0` ✓／`s_0^{-1}` ✓）／
`\mathrm{algebraMap}` ✓（常量不动 ✓）／和 ✓／积 ✓）。 -/
theorem smul_eq_self_of_mem_adjoin_of_fixed {ι : Type*}
    {a : ι → NoetherField F G} {s₀ : NoetherField F G}
    (ha_fix : ∀ (g : G) (i : ι), g • a i = a i) (hs₀_fix : ∀ (g : G), g • s₀ = s₀) :
    ∀ (g : G) {x : NoetherField F G},
      x ∈ Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) → g • x = x := by
  intro g x hx
  refine Algebra.adjoin_induction (p := fun x _ => g • x = x) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨i, rfl⟩ | hy
    · exact ha_fix g i
    · rcases hy with rfl | rfl
      · exact hs₀_fix g
      · by_cases h0 : s₀ = 0
        · rw [h0, inv_zero, smul_zero]
        · have h1 : g • s₀⁻¹ * (g • s₀) = 1 := by
            rw [← smul_mul', inv_mul_cancel₀ h0, smul_one]
          rw [eq_inv_of_mul_eq_one_left h1, hs₀_fix g]
  · intro c
    have h := smul_algebraMap_noether (F := F) (G := G) g (MvPolynomial.C c)
    rw [smul_C_noether] at h
    simp only [MvPolynomial.C_eq_algebraMap] at h
    exact h
  · intro x y _ _ hx hy
    rw [smul_add, hx, hy]
  · intro x y _ _ hx hy
    rw [smul_mul', hx, hy]

end FixedAdjoin

section SourceAssembly

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **探针②（源侧装配）** ✓：`R` 取**具体载体** `S`（Noether 域的 `F`-子代数 ✓）⟹
`hRA` ✓（`S` 定义即得 ✓）／`hRQ` ✓（由 `hle` ＋ §4.42 ① 的**载体步**内部导出 ✓）／
`hRGpoint` ✓（由 `hS_fix` 内部导出 ✓）—— **三项在册输入按构造消掉** ✓；
再调 **§4.46** ✓ ⟹ `\exists \varphi : \hookrightarrow K` ＋ **保作用同构** ✓。 -/
theorem exists_algHom_and_equivariant_algEquiv_tensorProduct_of_subalgebra
    {S : Subalgebra F (NoetherField F G)}
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ (g : G), g • t = t)
    (hle : S ≤ Subalgebra.restrictScalars F (Algebra.adjoin (MvPolynomial G F)
      ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G))))
    (hS_fix : ∀ (g : G) {x : NoetherField F G}, x ∈ S → g • x = x)
    [Algebra ↥S (Localization.Away t)]
    [IsScalarTower F ↥S (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : ↥S) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup ↥S (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp ↥S (Localization.Away t) G hRG)
    (hS₀R : ∀ r : ↥S,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap ↥S (Localization.Away t) r)
        = algebraMap ↥S (NoetherField F G) r)
    {K : Type} [Field K] [Algebra F K]
    {L : Type} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L] [Infinite K]
    (b : Module.Basis G K L) (hb : Function.Bijective (smulAlgEquivHom K G L))
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x) :
    ∃ φ : ↥S →ₐ[F] K,
      letI : Algebra ↥S K := φ.toRingHom.toAlgebra
      letI : Algebra ↥S L := ((algebraMap K L).comp φ.toRingHom).toAlgebra
      letI := BTier.tensorMulSemiringAction (R := ↥S) (T := K) (S := Localization.Away t) hRG
      ∃ e : L ≃ₐ[K] (TensorProduct ↥S K (Localization.Away t)),
        ∀ (g : G) (y : L), e (g • y) = g • e y := by
  -- ① `hRQ`：由 `hle` ＋ 载体步内部导出 ✓
  have hRQ : ∀ r : ↥S,
      algebraMap ↥S (NoetherField F G) r
        ∈ (awayToFieldAlg (F := F) (G := G) t ht).range := by
    intro r
    exact adjoin_inv_mem_range_awayToFieldAlg (F := F) (G := G) t ht (r : NoetherField F G)
      (hle r.property)
  -- ② `hRGpoint`：由 `hS_fix` 内部导出 ✓
  have hRGpoint : ∀ (g : G) (r : ↥S),
      g • algebraMap ↥S (NoetherField F G) r = algebraMap ↥S (NoetherField F G) r := by
    intro g r
    exact hS_fix g r.property
  -- ③ §4.46
  exact exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data (R := ↥S) ht htinv
    hact_map hRG hgal hProj hS₀R hRQ hRGpoint b hb hfix

end SourceAssembly

/-! ## 4.48 **装配 (a) 款 · 落到 §4.47 的载体** ✓✅（第 188 轮）

**⚠ 起点** ✓（**承 §150.6 第 1 项** ✓，**仍压 `(a)` 款** ✓，**不转项** ✗）：§4.47 把 `R` 取为子代数载体
`S := \hookrightarrow F[a, s_0, s_0^{-1}]` ✓，而 **(a) 款**（`\mathrm{IsGenericExtension}` 第一款 ✓）要求
`S \simeq_F \mathrm{Localization.Away}\ w` ✓ —— 此前只对 `\uparrow(A_0[s^{-1}])`（**以 `A_0` 为基** ✓）成立 ✗。

**⚠ 一件** ✓：`exists_algEquiv_localizationAway_of_adjoin_union_inv` ✓✅✅ ——
**代数无关族** ✓ ＋ **域生成** ✓ ＋ `s_0 \neq 0` ✓ ＋ **`s_0 \in F[a]`** ✓ ⟹
`\exists w \neq 0,\ \hookrightarrow F[a, s_0, s_0^{-1}] \simeq_F \mathrm{Localization.Away}\ w` ✓
—— **`S` 满足 (a) 款** ✓；与 §4.47 合读 ⟹ **(a) 款与 (c) 款落在同一载体上** ✓。

**⚠ 手法** ✓（**读数 (70)** ✓：**先查现成机器** ✗→✓）：**载体桥免证** ✓ —— **mathlib 现成件**
`\mathrm{Algebra.adjoin\_union\_eq\_adjoin\_adjoin}` ✓（`\mathrm{adjoin}\ R\ (s \cup t) = (\mathrm{adjoin}\ (\mathrm{adjoin}\ R\ s)\ t).\mathrm{restrictScalars}\ R` ✓）
一次给出 ✓；再由 **`s_0 \in A_0`** ✓ **约去 `\{s_0\}`** ✓（`\mathrm{adjoin}\ \uparrow A_0\ \{s_0, s_0^{-1}\} = \mathrm{adjoin}\ \uparrow A_0\ \{s_0^{-1}\}` ✓，
`\mathrm{adjoin\_le\_iff}` 两支 ✓）；最后用 **r168 ③** `\mathrm{exists\_algEquiv\_localizationAway\_of\_adjoin\_inv'}` ✓
（**(a) 款无假设形** ✓）＋ `\mathrm{Subalgebra.equivOfEq}` ✓ 搬运 ✓。

**⚠ 工艺读数（本轮新增两条）** ✓：
**① `\mathrm{rintro}\ \dots\ (\mathrm{rfl} \mid \mathrm{rfl})` 陷阱** ✗✓：当假设形如 `y = s_0`（**两侧皆局部变量** ✓）时，
`\mathrm{rfl}` **模式会替换掉 `s_0` 本身** ✗（`\mathrm{cases}` 择一侧替换 ✗）⟹ 其后的 `s_0` **变成未知标识符** ✗
（**报错为 `Unknown identifier` 而非类型错误** ✗，**极具误导性** ✗）—— **正解** ✓：`\mathrm{rintro}\ y\ (hy \mid hy)` ✓ ＋ `\mathrm{rw}\ [hy]` ✓（**只动目标** ✓，**不动上下文** ✓）；
**② `\mathrm{let}` 缩写 ＋ `\mathrm{show}`** ✓：重项（`\mathrm{adjoin}\ \uparrow A_0\ \{\dots\}` ✓）在**陈述处出现一次** ✓、
证明内以 `\mathrm{let}\ T` 缩写 ✓ 并用 `\mathrm{show} \dots = T` ✓ 对齐 ✓ ⟹ **避免重项反复统一** ✓（**承 (74)／(75)** ✓）。
**⚠ 前提表** ✓（**最弱假设** ✓）：`hind` ✓／`hgen` ✓／`hs_0` ✓／`hs_0 \in F[a]` ✓ —— **无多余前提** ✗
（`\mathrm{AlgebraicIndependent}` 支**不可去** ✗：`\mathrm{MvPolynomial}` 同构之所在 ✓）。 -/

section ClauseACarrier

variable {F : Type} [Field F] {K : Type} [Field K] [Algebra F K]

/-- **探针（(a) 款落到 §4.47 的载体 `S`）** ✓：代数无关族 `a` ＋ 域生成 ✓ ＋ `s_0 \neq 0` ✓ ＋
**`s_0 \in F[a]`** ✓ ⟹ **`S := \hookrightarrow F[a, s_0, s_0^{-1}]` 同构于某局部化多项式环** ✓。 -/
theorem exists_algEquiv_localizationAway_of_adjoin_union_inv {n : ℕ} {a : Fin n → K}
    (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤)
    {s₀ : K} (hs₀ : s₀ ≠ 0) (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a)) :
    ∃ (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
      Nonempty (↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) ≃ₐ[F] Localization.Away w) := by
  classical
  -- ① (a) 款无假设形（r168 ③）
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_algEquiv_localizationAway_of_adjoin_inv' (K := K)
    hind hgen ⟨s₀, hs₀_mem⟩ (fun h => hs₀ (congrArg Subtype.val h))
  -- ② 载体桥（`s₀ ∈ A_0` ⟹ `{s₀}` 可约）
  have h2 : Algebra.adjoin ↥(Algebra.adjoin F (Set.range a)) {s₀, s₀⁻¹}
      = Algebra.adjoin ↥(Algebra.adjoin F (Set.range a))
          {(algebraMap ↥(Algebra.adjoin F (Set.range a)) K
            (⟨s₀, hs₀_mem⟩ : ↥(Algebra.adjoin F (Set.range a))))⁻¹} := by
    let T : Subalgebra ↥(Algebra.adjoin F (Set.range a)) K :=
      Algebra.adjoin ↥(Algebra.adjoin F (Set.range a))
        {(algebraMap ↥(Algebra.adjoin F (Set.range a)) K
          (⟨s₀, hs₀_mem⟩ : ↥(Algebra.adjoin F (Set.range a))))⁻¹}
    show Algebra.adjoin ↥(Algebra.adjoin F (Set.range a)) {s₀, s₀⁻¹} = T
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro y (hy | hy)
      · rw [hy]
        exact Subalgebra.algebraMap_mem T (⟨s₀, hs₀_mem⟩ : ↥(Algebra.adjoin F (Set.range a)))
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    · rw [Algebra.adjoin_le_iff]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Algebra.subset_adjoin (by simp)
  have h1 := Algebra.adjoin_union_eq_adjoin_adjoin F (Set.range a) {s₀, s₀⁻¹}
  refine ⟨w, hw, ?_⟩
  exact ⟨(Subalgebra.equivOfEq _ _
    (h1.trans (congrArg (Subalgebra.restrictScalars F) h2))).trans e⟩

end ClauseACarrier

/-! ## 4.49 **装配 (c) 款 · 源文取向收口**：**`L \cong S_0 \otimes_R K`**（源 `definition-1-1`(c) 的**逐字取向** ✓）（第 193 轮）

**⚠ 起点** ✓（**承 §4.46** 的 `L \simeq_K (K \otimes_R S_0)` ✓；r182 登记的**余项 ④** ✗）：源文写
「`L \cong S \otimes_\phi K`」（`raw/Saltman1982.tex :159` ✓，**`S` 在前** ✓），而 §4.46 产出的是 **`K \otimes_R S_0`** ✗
—— 两取向**非 defeq** ✗（§34.6 头注 ✓）。

**⚠ 本轮（断指）** ✓：以 r191 的**取向同构** ✓（`\mathrm{tensorProductComm}` ✓，`K \otimes_R S_0 \simeq_K S_0 \otimes_R K` ✓）
**复合** ✓ §4.46 的等变同构 ✓ ⟹ **源文取向的保作用同构** ✓；**逆取向的等变性** ✓ 由 `\mathrm{tensorProductComm\_symm\_equivariant}` ✓
**单性搬运** ✓（**不重证** ✗）。

**⚠ 登记（谓词形缺口，精确化** ✗）：`\mathrm{RealizationProperty}`（`GenericExtension\_ABGV52` ✓ 的 `definition-1-1`(c) 编码 ✓）
量词域是 **`[\mathrm{CommRing}\ L]`** ✓（源文在**交换代数**语境下写 "Galois extension" ✓），
而本册 **装配链**（§4.41--§4.49 ✓）所需的**逐点数据**为 **`[\mathrm{Field}\ L]`** ✗ ＋ `[\mathrm{Infinite}\ K]` ✗
＋ **正规基** `b`／`hb` ✓ ＋ `hfix` ✓（在册 `\mathrm{GaloisFixedSubringHyp}` ✓）⟹
**谓词形 (c) 款**（`\forall K\ L` 仅由 `\mathrm{IsGaloisWithGroup}\ K\ L\ G\ hKL` 出发 ✓）**本册未落** ✗
—— **不声称**已闭 ✗；登记为 `\mathrm{realizationProperty\_gap\_registered}` ✓。 -/

section SourceOrientationCapstone

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **(c) 款 · 源文取向收口** ✓✅：**§4.46 的全部数据** ✓ ⟹ **`\exists \varphi : R \toₐ[F] K`** ＋
**保作用的同构** `L \simeq_K (S_0 \otimes_R K)` ✓ —— **源文取向** ✓（`S` 在前 ✓，`definition-1-1`(c) ✓）。
**⚠ 本件 ＝ 复合件** ✓（**不重证** ✗）：§4.46 的等变同构 ✓ ＋ r191 的取向同构（及其逆的等变性 ✓）。 -/
theorem exists_algHom_and_equivariant_algEquiv_tensorProduct_sourceOrientation
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    {K : Type} [Field K] [Algebra F K]
    {L : Type} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L] [Infinite K]
    (b : Module.Basis G K L) (hb : Function.Bijective (smulAlgEquivHom K G L))
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x) :
    ∃ φ : R →ₐ[F] K,
      letI : Algebra R K := φ.toRingHom.toAlgebra
      letI : Algebra R L := ((algebraMap K L).comp φ.toRingHom).toAlgebra
      letI : Algebra K (TensorProduct R (Localization.Away t) K) :=
        Algebra.TensorProduct.rightAlgebra
      letI : MulSemiringAction G (TensorProduct R (Localization.Away t) K) :=
        BTier.bcTensorMulSemiringAction (R := R) (S := Localization.Away t) (T := K) hRG
      ∃ e : L ≃ₐ[K] (TensorProduct R (Localization.Away t) K),
        ∀ (g : G) (y : L), e (g • y) = g • e y := by
  obtain ⟨φ, e, he⟩ := exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data
    (F := F) (G := G) (t := t) ht htinv hact_map hRG hgal hProj hS₀R hRQ hRGpoint b hb hfix
  refine ⟨φ, ?_⟩
  let _ : Algebra R K := φ.toRingHom.toAlgebra
  let _ : Algebra R L := ((algebraMap K L).comp φ.toRingHom).toAlgebra
  let _ : Algebra K (TensorProduct R (Localization.Away t) K) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := Localization.Away t) (B := K)
  let _ : MulSemiringAction G (TensorProduct R (Localization.Away t) K) :=
    BTier.bcTensorMulSemiringAction (R := R) (S := Localization.Away t) (T := K) hRG
  let _ : MulSemiringAction G (TensorProduct R K (Localization.Away t)) :=
    BTier.tensorMulSemiringAction (R := R) (T := K) (S := Localization.Away t) hRG
  refine ⟨e.trans (BTier.tensorProductComm (R := R) (S := Localization.Away t) (T := K)), ?_⟩
  intro g y
  show BTier.tensorProductComm (R := R) (S := Localization.Away t) (T := K) (e (g • y))
    = g • BTier.tensorProductComm (R := R) (S := Localization.Away t) (T := K) (e y)
  rw [he g y]
  exact BTier.tensorProductComm_equivariant (R := R) (S := Localization.Away t) (T := K)
    hRG g (e y)

/-- **登记** ✗：**(c) 款的谓词形缺口** ✓ —— `RealizationProperty` 的量词域 `[\mathrm{CommRing}\ L]` ✓
与装配链所需的 `[\mathrm{Field}\ L]` ✗／`[\mathrm{Infinite}\ K]` ✗／正规基 ✓／`hfix` ✓ 不匹配 ⟹
**谓词形未落** ✗（**不声称**已闭 ✗）。 -/
theorem realizationProperty_gap_registered : True := trivial

end SourceOrientationCapstone

/-! ## 4.50 **谓词形 (c) 款的缺口收敛**：`[Infinite K]` 的内部导出 ＋ `F` 无限性的**口径偏离登记**（第 194 轮）

**⚠ 起点** ✓（**承 §156.6 第 1 项** ✓）：§4.49 登记了**谓词形 (c) 款缺口** ✗ —— `RealizationProperty` 的 ∀-形给
`[CommRing L]` ✓，而装配链需 `[Field L]` ✗／`[Infinite K]` ✗／**正规基** ✓／`hfix` ✓。

**⚠ 源文核对** ✓（**先审后落** ✓，本轮逐字）：
**①** 源 `theorem-5-1` 的**假设**含「**with `F` infinite**」✓（`raw/Saltman1982.tex :640` ✓ 逐字）——
而库内 `Theorem51Statement`（本件 `:254` ✓）**不含** ✗ ⟹ **口径偏离：库内陈述强于源** ✗（**登记** ✓；**⚠ 第 195 轮已回正** ✓✅ —— 谓词体加 `Infinite F →` ✓，锁见 `Theorem51Statement.faithful_lock` ✓）。
**②** 源 `lemma-5-2` 的证明**显式**用「This is always possible **because `K` is infinite**」✓（`:662` ✓）——
而 `K` 的无限性**由 `F` 无限派生** ✓（`K \supseteq F` ✓，域扩张 ✓）⟹ **`[Infinite K]` 非独立假设** ✓，**本轮落地该派生** ✓。

**⚠ 正规基一条（登记，未落** ✗）：源**直接引用**「**Since some normal basis exists**」✓（`:662` ✓，**未证** ✗）；
mathlib **有**该定理 ✓（`Mathlib/FieldTheory/Galois/NormalBasis.lean` ✓，`IsGalois.normalBasis` ✓），
但其指标是 **`L \simeqₐ[K] L`** ✗（**不是**抽象 `G` ✗）⟹ 要与本册的 `b : Module.Basis G K L` 对接，
**须先有 `G \simeq \mathrm{Gal}(L/K)`** ✗（＝ `hfix` 的**缺失半** ✓，在册 `GaloisFixedSubringHyp` ✗）
⟹ **登记为外部经典** ✗（**不声称**已落 ✗）。
**⚠ r199 已回收此条** ✓✅：源 `proposition-0-5(c)` ✓ **正是**该条（**证在 §0** ✓）⟹ **源侧不缺** ✓、
缺口在**库内桥** ✗ —— 已由 §4.54 ✓（**CHR 桥（域档）** ✓）**落地** ✓（`exists_normalBasis_of_isGaloisWithGroup` ✓）；
**本条留痕** ✓（**不复写** ✗）。 -/

section InfiniteTargetData

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]

/-- **目标侧 `[Infinite K]` 的内部导出** ✓✅：`F` 无限 ✓ ＋ `K \supseteq F` ✓（`K` 是域 ✓）⟹ **`K` 无限** ✓
（`\mathrm{algebraMap}\ F\ K` **单射** ✓ ⟹ 沿单射**前推**无限性 ✓）。
**⚠ 与源一致** ✓：源 `lemma-5-2` 的证明正用此 ✓（「because `K` is infinite」✓，由 `theorem-5-1` 的
「with `F` infinite」✓ 派生 ✓）—— 故此项**不是**外部假设 ✓。 -/
theorem infinite_of_algebra_of_infinite [Infinite F] : Infinite K :=
  Infinite.of_injective (algebraMap F K) (FaithfulSMul.algebraMap_injective F K)

/-- **登记** ✗：**口径偏离（库内强于源）** —— 源 `theorem-5-1` 假设「`F` infinite」✓（`raw/Saltman1982.tex :640` ✓ 逐字），
而 `Theorem51Statement`（本件 `:254` ✓）**不含** ✗（**⚠ r195 已回正** ✓）；**⚠ 后果** ✓：装配 (c) 款须 `[Infinite K]` ✗
（源证明显式需要 ✓；本件上方 `infinite_of_algebra_of_infinite` ✓ 给出**其派生** ✓），
但**无**「`F` infinite」则 `[Infinite K]` **不可派生** ✗ ⟹ 谓词形 (c) 款**未落** ✗（**不声称**已闭 ✗）。 -/
theorem theorem51Statement_infiniteField_gap_registered : True := trivial

end InfiniteTargetData

/-! ## 4.51 **源 `theorem-5-1` 的条件总装（第一步）**：**见证打包** ＋ **(c) 款域档**（第 196 轮）

**⚠ 起点** ✓（**承 §158.7 第 1 项** ✓）：§4.46／§4.47／§4.48 已把 (c) 款的**逐点**装配做齐 ✓，
但**谓词形**（`RealizationProperty` 的 **`[CommRing L]`** ∀-形 ✓，＝ `definition-1-1`(c) 的编码 ✓）**未落** ✗（§157.2 ④ ✓）。

**⚠ 本轮（断指）** ✓：**两条** ✓ ——
**①** **见证打包** ✓✅：**三款齐** ⟹ `Nonempty (GenericExtensionWitness F G)` ✓
（**⚠ 库内首件** ✗→✓：`GenericExtensionWitness` 此前**只在陈述侧**出现 ✓，**无任何构造件** ✗ —— `∃` 不接受实例绑定 ⟹ 须**显式打包** ✓）；
**②** **(c) 款的域档** ✓✅：量词域收为 **`[Field L]`** ✓（＝ 源 §5 的**用点形** ✓），由**装配链**（§4.46 ✓）
＋ **逐点数据**（正规基 `b`／`hb` ✓ ＋ `hfix` ✓）＋ **`F` 无限**（⟹ `K` 无限 ✓，r194 ✓）供给 ✓。

**⚠ 登记（真卡点** ✗）：**代数档**（`[CommRing L]` ✓，即 `definition-1-1`(c) 的编码 ✓）**仍缺** ✗ —— 须**代数版（CHR）理论** ✗
（`GaloisFixedSubringHyp` ✓／正规基**以 `G` 为指标** ✓／域档假设 ✓三条在册 ✓，见 §157.2 ②③④ ✓）。

**⚠ 另一发现（登记** ✓）：装配链与**逐点数据**的**陈述**还需 `[SMulCommClass G K L]`／`[SMulCommClass G F L]` ✗
（`smulAlgEquivHom K G L` 的**类型**即需前者 ✓）—— 二者**可由 `hKL` ＋ 塔在证明体内派生** ✓
（`hKL` 即 `SMulCommClass G K L` ✓；`F`-档由 `IsScalarTower.algebraMap_smul` ✓ ＋ `hKL` ✓），
但**逐点数据的假设表**须**显式带**这两项 ✓（否则该假设**不可陈述** ✗）⟹ **登记** ✓（非谓词层缺口 ✓）。 -/

section SourceDataToWitness

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **(c) 款的域档形** ✓：`RealizationProperty`（`definition-1-1`(c) ✓）把量词域收为 **`[Field L]`** ✓ ——
**⚠ 用途** ✓：这是**装配链能供给**的形 ✓（§4.46 ✓）；**代数档**（`[CommRing L]` ✗）**仍缺** ✗（**登记** ✓）。 -/
def RealizationPropertyField (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] : Prop :=
  ∀ (K : Type) [Field K] [Algebra F K]
    (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L]
    (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
    BTier.IsGaloisWithGroup K L G hKL →
      ∃ (φ : R →ₐ[F] K),
        letI : Algebra R K := φ.toRingHom.toAlgebra
        Nonempty (L ≃ₐ[K] (TensorProduct R K S))

/-- **(c) 款域档 · 源侧总装** ✓✅：**§4.46 的全部源侧数据** ✓ ＋ **`F` 无限** ✓ ＋ **逐点数据** ✓
⟹ **`RealizationPropertyField F G R S_0`** ✓（`S_0 := Localization.Away t` ✓）。
**⚠ 不重证** ✓：逐点调用 §4.46 ✓；`K` 的无限性由 r194 的派生件 ✓ 供给；两条 `SMulCommClass` 由 `hKL` ＋ 塔**现场派生** ✓。 -/
theorem realizationPropertyField_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    (hdata : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L]
      (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
      BTier.IsGaloisWithGroup K L G hKL →
        ∃ (_b : Module.Basis G K L), Function.Bijective (smulAlgEquivHom K G L) ∧
          ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x) :
    RealizationPropertyField F G R (Localization.Away t) := by
  intro K _ _ L _ _ _ _ _ hKL hgalKL
  let _ : SMulCommClass G K L := ⟨fun g k x => hKL g k x⟩
  let _ : SMulCommClass G F L := ⟨fun g f x => by
    rw [← IsScalarTower.algebraMap_smul K f x, ← IsScalarTower.algebraMap_smul K f (g • x),
      hKL g (algebraMap F K f) x]⟩
  obtain ⟨b, hb, hfix⟩ := hdata K L hKL hgalKL
  let _ : Infinite K := infinite_of_algebra_of_infinite (F := F) (K := K)
  obtain ⟨φ, e, _he⟩ := exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data
    (F := F) (G := G) (t := t) ht htinv hact_map hRG hgal hProj hS₀R hRQ hRGpoint b hb hfix
  refine ⟨φ, ?_⟩
  let _ : Algebra R K := φ.toRingHom.toAlgebra
  exact ⟨e⟩

end SourceDataToWitness

section WitnessPackaging

variable {F : Type v} [Field F] {G : Type u} [Group G] [Fintype G]

/-- **见证打包** ✓✅：`IsGenericExtension` 的**三款齐** ✓ ⟹ `Nonempty (GenericExtensionWitness F G)` ✓
（**⚠ 库内首件** ✓；`∃` 不接受实例绑定 ⟹ 见证须**显式打包** ✓）。 -/
theorem nonempty_genericExtensionWitness_of_clauses {R S : Type u}
    [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))
    (hb : BTier.IsGaloisWithGroup R S G hRG) (hc : BTier.RealizationProperty F G R S) :
    Nonempty (GenericExtensionWitness F G) :=
  ⟨{ R := R, S := S, hRG := hRG, isGeneric := ⟨ha, hb, hc⟩ }⟩

end WitnessPackaging

/-! ## 4.52 **端点对接**：**三款在同一载体上齐备**（**`(c)` 走域档**）＋ **口径裁决点登记**（第 197 轮）

**⚠ 起点** ✓（**承 §159.6 第 1 项** ✓）：§4.47／§4.48 的**具体载体** ✓ ＋ **(b) 款**（r180／r191／r192 ✓）＋ §4.51 的**域档 (c)** ✓。

**🔴 可达性审计（本轮实测** ✗，**承 r196 判据纪律** ✓）：**「端点对接 ⟹ 见证」不可达** ✗ ——
`GenericExtensionWitness.isGeneric` 的**类型**是 `IsGenericExtension`（本件 `:179` ✓），其**第三合取**为
**`RealizationProperty`**（`GenericExtension_ABGV52 :46` ✓，**`[CommRing L]` 档** ✗）⟹ **域档 (c) 不能充当** ✗
⟹ 本轮**下调**为「**三款在同一载体上齐备（`(c)` 走域档）**」✓ ＋ **登记该裁决点** ✗（**不声称**见证已成 ✗）。

**⚠ 源文两读（**逐字** ✓，**交人类裁决** ✗）：源 `definition-1-1`(c)（`raw/Saltman1982.tex :159` ✓）写
「Let `K` be a **field** containing `F` and let `L/K` be a **Galois extension** with group `G`」✓ ——
**读一（环扩张** ✓**）**：源 §0 的框架是**交换环**的 Galois 理论 ✓（`:56` ✓「the Galois theory of commutative rings」✓；
`theorem-1-2` 的证明用 `L \cong K\{y^p - y - a\}` ✓（`:174` ✓，**代数**形 ✓））⟹ `L` 可为**环** ✓（**库内现行编码** ✓）；
**读二（域扩张** ✓**）**：经典用法 ✓，且 `theorem-5-1` 的**用点**正是**域** ✓（`:646` ✓／`:662` ✓：正规基、单位、`K` 无限 ✓）
⟹ `L` 为**域** ✓（**域档** ✓）。**⚠ 两读下 (c) 款强度不同** ✗：读一 ＝ **谓词形** ✓（**装配链未落** ✗）；
读二 ＝ **域档** ✓（**本轮齐备** ✓）。 -/

section EndpointClausesField

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **端点合取（域档 `(c)`）** ✓✅：**同一具体载体**上 **(a) 款** ✓（`∃ w \neq 0,\ R \simeq_F \mathrm{Localization.Away}\ w` ✓，如 r188 ✓）
＋ **(b) 款** ✓（`\mathrm{IsGaloisWithGroup}\ R\ S_0\ G\ hRG` ✓）＋ **(c) 款域档** ✓（§4.51 ✓）**三款齐备** ✓ ——
即 **`\mathrm{IsGenericExtension}` 的三合取在域档下的形** ✓（**⚠ 与 `\mathrm{IsGenericExtension}` 之别仅在 `(c)` 的档** ✗，见节头审计 ✓）。 -/
theorem isGenericExtensionClausesField_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    (hdata : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L]
      (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
      BTier.IsGaloisWithGroup K L G hKL →
        ∃ (_b : Module.Basis G K L), Function.Bijective (smulAlgEquivHom K G L) ∧
          ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x)
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
      w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) :
    (∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
        w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
      BTier.IsGaloisWithGroup R (Localization.Away t) G hRG ∧
      RealizationPropertyField F G R (Localization.Away t) :=
  ⟨ha, hgal,
    realizationPropertyField_of_sourceData (F := F) (G := G) (t := t) ht htinv hact_map hRG hgal
      hProj hS₀R hRQ hRGpoint hinf hdata⟩

/-- **登记** ✗：**口径裁决点** —— `definition-1-1`(c) 的「`L/K` is a Galois extension」有**两读** ✓
（**环** ✓／**域** ✓，逐字证据见节头 ✓）；库内 `RealizationProperty`（`GenericExtension_ABGV52 :26` ✓）取**从严**的**环读** ✓
⟹ **谓词形** ✓（**未落** ✗）；**域读**下 `(c)` 即**域档** ✓（本件上方 ✓）。
**⚠ 裁决后果** ✓：取**域读** ⟹ thm `5.1` 的装配在 **(a) ＋ (b) ＋ 域档 `(c)`** 下**齐备** ✓
（**仍缺** `hfix` ✓ 与**正规基** ✓ **两项在册输入** ✗，§157.2 ②③ ✓）；取**环读** ⟹ 须**代数版（CHR）理论** ✗。
**⚠ r198 已裁** ✓✅（**同轮同步散文** ✓）：**环读忠实** ✓（源印 254 明写 `L` **不必**是域 ✓，**PDF 页级** ✓），
**域读被源文排除** ✗ ⟹ 域档**只能**作**弱化档** ✗ —— 详见 §4.53 `definition11c_reading_decided` ✓
（**本登记留痕** ✓，**不复写** ✗）。 -/
theorem definition11c_reading_gap_registered : True := trivial

end EndpointClausesField

/-! ## 4.53 **`definition-1-1`(c) 的口径裁决定案（源文自证）** ＋ **域档弱化档见证**（第 198 轮）

**⚠ 起点** ✓（**承 §4.52 的裁决点** ✗）：§4.52 登记 `definition-1-1`(c) 有**两读** ✓（环 ✓／域 ✓），交人类裁决 ✗
（源 `raw/Saltman1982.tex :159` ✓）。

**🔴 本轮裁决定案** ✓（**源文自证** ✓，**PDF 页级目视** ✓）：`raw/Saltman1982.pdf` **第 5 页** ＝ **印刷页 254** ✓ 逐字 ——
「Turning to the case `R = K` is a field, let `L/K` be Galois with group `G`. **We emphasize that here and in the rest of
the paper, `L` is not necessarily a field.** Of course, `L` is the direct sum of fields.」✓
同页 `proposition-0-5`：**(b)**「The automorphisms in `G` are algebraically independent over `K`」✓、
**(c)**「`L` has a normal basis over `K`. That is, `L⁺ ≅ K[G]` as `K[G]` modules.」✓ —— **两条均对一般（非域）`L`** ✓。
⟹ **①** `definition-1-1`(c) 落在同篇「the rest of the paper」之内 ✓ ⟹ 「`L/K` is a Galois extension with group `G`」
**只能作环读** ✓（`L` **不必**是域 ✓）⟹ **库内 `RealizationProperty`**（`GenericExtension_ABGV52 :26` ✓，`[CommRing L]` ✓）
**忠实** ✓（**不需回正** ✓）；⟹ **②** **域读被源文排除** ✗ ⟹ `RealizationPropertyField`（§4.51 ✓）**不是** (c) 的读法 ✓，
**只能**作**弱化档** ✓（**库内弱于源** ✗，**登记** ✓）⟹ 本节落的**见证**（③--⑦ ✓）是**弱化档见证** ✗（**非**源结论 ✗）。

**⚠ 由此纠正 §4.50 的一处登记** ✓（**留痕** ✓）：§4.50 记「正规基：源**直接引用**、**未证** ✗」——
**本轮实测** ✓：源 `proposition-0-5(c)` ✓ **正是**该条（**证在 §0** ✓，据 `[Jac74] p. 283` ＋
「the same arguments that apply when `L` is a field」✓）；**(b)** 代数无关性 ✓ 正是 `lemma-5-2` 证明所引
「By the algebraic independence of the `σ`'s」✓（`:662` ✓）⟹ **源侧不缺** ✓ ⟹ 缺口在**库内桥** ✗：
mathlib 的正规基定理**指标**是 `L ≃ₐ[K] L` ✗ ⟷ **抽象 `G`** ✗，且 CHR 不动环（在册 `GaloisFixedSubringHyp` ✓）**未证** ✗
（**在册** ✓，**不声称**已落 ✗）。

**⚠ 页号回填（登记** ✓，**下一轮** ✗）：`definition-1-1` 逐字在 **印 255**（＝ **PDF 第 6 页** ✓，本轮**目视** ✓ ——
「DEFINITION 1.1 …… (c) Let `K` be a field containing `F` and let `L/K` be a Galois extension with group `G`」✓），
而 `GenericExtension_ABGV52` 头注写「印 **254**」✗（**差一页** ✗）⟹ **回填待办** ✓（**本轮单文件** ✓，**不动他件** ✗）；
**偏移口径** ✓ ＝ **印 ＝ PDF ＋ 249** ✓（本轮三点复核：PDF 4／5／6 ⟷ 印 253／254／255 ✓）。

**⚠ 端点结论** ✓（**不声称** ✗）：**弱化档见证可达** ✓（⑦ ✓）；**源 `theorem-5-1` 的结论**（＝ (c) **环档**）**未证** ✗ ——
**缺**环档 `hdata` 三条（`G`-指标正规基 ✓／`G ≅ Gal(L/K)` ✓／不动点 ✓），**均库内桥** ✗（登记 ✓）。 -/

/-- **裁决定案** ✓：`definition-1-1`(c) 的读法 —— **环读忠实** ✓（源印 254 逐字「and in the rest of the paper, `L` is not
necessarily a field」✓，**PDF 页级** ✓），**域读被源文排除** ✗ ⟹ 域档谓词**只能**作**弱化档** ✓（**库内弱于源** ✗）。
**⚠** 故本节落的见证是**弱化档见证** ✗：**源 `theorem-5-1` 的结论未证** ✗（**缺**环档 `hdata` 三条，均库内桥 ✗）。 -/
theorem definition11c_reading_decided : True := trivial

/-- **域档孪生谓词**（**弱化档** ✗）：`IsGenericExtension`（`GenericExtension_ABGV52 :40` ✓）的**同一三合取** ✓，
唯第三款取 `RealizationPropertyField` ✓（＝ 量词 `L` 收为**域** ✗）。
**⚠ 口径** ✓：**非**源 `definition-1-1`(c) ✓（源印 254 明写 `L` **不必**是域 ✗）；本件**只作弱化档** ✓，
**用途** ✓ ＝ 承载**装配链能供给**的形 ✓（§4.46／§4.51 ✓）。 -/
def IsGenericExtensionField (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
  BTier.IsGaloisWithGroup R S G hRG ∧
  RealizationPropertyField F G R S

/-- **外形锁** ✓（`rfl` 型 ✓）：域档谓词与**三合取展开体逐字相同** ✓ —— 合取内容或次序漂移 ✗ 即编译失败 ✓。
**⚠ 判别力（L43／r195 纪律）** ✓：**变异件负例已实跑** ✓（`.abgv52-scratch/probe-r198b.lean` ✓）——
**变异件 A**（第三合取换回**源形** `RealizationProperty` ✗）与**变异件 B**（第三合取**删去** ✗）**均使本 `rfl` 失败** ✓
（读数 ＝ 两处 `Not a definitional equality` ✓，`rc=1` ✓）⟹ 本锁**能**分辨「弱化档」与「源形」✓。 -/
theorem IsGenericExtensionField.shape {F : Type*} [Field F] {G : Type*} [Group G] [Fintype G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (IsGenericExtensionField F G R S hRG)
      = ((∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
            Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
          BTier.IsGaloisWithGroup R S G hRG ∧ RealizationPropertyField F G R S) :=
  rfl

/-- **两读强度序（可证方向）** ✓：**环读 ⟹ 域读** ✓ —— 源形 (c)（`[CommRing L]` ✓）在**域**上特化即域档 ✓
（`[Field L]` **蕴含** `[CommRing L]` ✓，故把域档的量词实例喂给源形即可 ✓）。
**⚠ 方向性** ✓：本条**只**给「源形 ⟹ 弱化档」✓；**逆方向**（域档 ⟹ 源形 ✗）**未证** ✗ —— 那正是**环档缺口** ✓（登记 ✓）。
**⚠ 意义** ✓：`§4.53` 的裁决由此**形式化** ✓ —— 域档**弱于**源形 ✓（**⚠ 不断言「严格」** ✗：不反向**未证** ✗，故**不声称**严格性 ✗）。 -/
theorem realizationPropertyField_of_realizationProperty {F : Type*} [Field F] {G : Type*} [Group G]
    [Fintype G] {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] (h : BTier.RealizationProperty F G R S) :
    RealizationPropertyField F G R S := by
  intro K _ _ L _ _ _ _ _ hKL hgal
  exact h K L hKL hgal

/-- **谓词层同款** ✓：`IsGenericExtension` ⟹ `IsGenericExtensionField` ✓（三款逐款搬运 ✓，第三款用上行 ✓）。 -/
theorem isGenericExtensionField_of_isGenericExtension {F : Type*} [Field F] {G : Type*} [Group G]
    [Fintype G] {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    {hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)}
    (h : BTier.IsGenericExtension F G R S hRG) : IsGenericExtensionField F G R S hRG :=
  ⟨h.1, h.2.1, realizationPropertyField_of_realizationProperty h.2.2⟩

/-- **弱化档见证数据** ✗：与 `GenericExtensionWitness`（本件 `:166` ✓）**同款打包** ✓，唯 `isGeneric` 取**域档**谓词 ✗。
**⚠ 口径** ✓：本结构承载的是**弱化档**见证 ✗（**非**源 `theorem-2-1`／`theorem-5-1` 的见证 ✓）。 -/
structure GenericExtensionWitnessField (F : Type v) [Field F] (A : Type u) [Group A] [Fintype A] where
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
  /-- **弱化档**三款 ✓（第三款取**域读** ✗）。 -/
  isGeneric : IsGenericExtensionField F A R S hRG

/-- **弱化档见证打包** ✓：三款齐（第三款**域档** ✗）⟹ `Nonempty (GenericExtensionWitnessField F G)` ✓
（与 §4.51 的 `nonempty_genericExtensionWitness_of_clauses` ✓ **同款** ✓ —— `∃` 不接受实例绑定 ⟹ 须显式打包 ✓）。 -/
theorem nonempty_genericExtensionWitnessField_of_clauses {F : Type v} [Field F] {G : Type u}
    [Group G] [Fintype G] {R S : Type u}
    [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))
    (hb : BTier.IsGaloisWithGroup R S G hRG) (hc : RealizationPropertyField F G R S) :
    Nonempty (GenericExtensionWitnessField F G) :=
  ⟨{ R := R, S := S, hRG := hRG, isGeneric := ⟨ha, hb, hc⟩ }⟩

section WeakFieldEndpoint

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **域档谓词 · 源侧总装** ✓：**§4.52 的三款齐备**（＝ `isGenericExtensionClausesField_of_sourceData` ✓ 的结论 ✓）
**逐步同型** ✓ ⟹ `IsGenericExtensionField F G R (Localization.Away t)` ✓（**rfl 级对接** ✓，**不重证** ✓）。
**⚠ 档位** ✓：结论是**弱化档** ✗（**非**源 `definition-1-1`(c) 的形态 ✓，见节头裁决 ✓）。 -/
theorem isGenericExtensionField_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    (hdata : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L]
      (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
      BTier.IsGaloisWithGroup K L G hKL →
        ∃ (_b : Module.Basis G K L), Function.Bijective (smulAlgEquivHom K G L) ∧
          ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x)
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
      w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) :
    IsGenericExtensionField F G R (Localization.Away t) hRG :=
  isGenericExtensionClausesField_of_sourceData (F := F) (G := G) (t := t) ht htinv hact_map hRG hgal
    hProj hS₀R hRQ hRGpoint hinf hdata ha

/-- **弱化档见证可达** ✓✅（**库内首件** ✓）：同一批源侧数据 ⟹ `Nonempty (GenericExtensionWitnessField F G)` ✓。
**⚠ 断言强度 ≤ 证据层级** ✓：本条**只**给**弱化档**见证 ✗ —— **源 `theorem-5-1` 的结论未证** ✗
（**缺**环档 `hdata` 三条 ✓，均**库内桥** ✗，登记于下 ✓）。 -/
theorem nonempty_genericExtensionWitnessField_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    (hdata : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L]
      (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
      BTier.IsGaloisWithGroup K L G hKL →
        ∃ (_b : Module.Basis G K L), Function.Bijective (smulAlgEquivHom K G L) ∧
          ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x)
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
      w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) :
    Nonempty (GenericExtensionWitnessField F G) :=
  ⟨{ R := R, S := Localization.Away t, hRG := hRG,
     isGeneric := isGenericExtensionField_of_sourceData (F := F) (G := G) (t := t) ht htinv
       hact_map hRG hgal hProj hS₀R hRQ hRGpoint hinf hdata ha }⟩

end WeakFieldEndpoint

/-- **登记** ✗：**源形见证缺口** —— `theorem-5-1` 的结论（`Nonempty (GenericExtensionWitness F G)` ✓，
＝ (c) **环档** ✓）**未证** ✗ ⟹ 弱化档见证（本件上方 ✓）**不能**充当之 ✗
（`GenericExtensionWitness.isGeneric` 的**类型**是 `BTier.IsGenericExtension` ✓，第三合取为 `RealizationProperty` ✓，**环档** ✗）。
**⚠ 缺的三条（均库内桥** ✗**）** ✓：**①** `G`-指标**正规基** `b : Module.Basis G K L` ✗（源 `proposition-0-5(c)` ✓
**已给** ✓ —— 印 254 ✓「`L⁺ ≅ K[G]` as `K[G]` modules」✓；缺的是 mathlib 指标 `L ≃ₐ[K] L` ✗ ⟷ **抽象 `G`** ✗ 的桥 ✓）；
**②** `G ≅ Gal(L/K)` ✗（＝ `hfix` 的缺失半 ✓，与在册 `GaloisFixedSubringHyp` ✓ 同族 ✓）；
**③** 不动点条件 `L^G = K` ✗（同族 ✓）。
**⚠ 后果** ✓：**环档**装配须上述三条 ✓（**本会话不落** ✗，**不声称**已落 ✗）。 -/
theorem genericExtensionWitnessField_gap_registered : True := trivial

/-! ## 4.54 **CHR 桥（域档）**：`G ≅ Gal(L/K)` ＋ `G`-指标正规基 ＋ 不动点（第 199 轮）

**⚠ 起点** ✓（**承 §4.53 的下一手** ✓）：§4.53 把 `hdata`（r196 ✓）的三条登记为**缺口** ✗ ——
**①** `G`-指标**正规基** ✗／**②** `G ≅ \mathrm{Gal}(L/K)` ✗／**③** 不动点 `L^G = K` ✗；
且 §4.10（`normalBasisPoly_gap_registered` ✓）与 §4.35（`fixedField_gap_registered` ✓）两条登记**均指向**
「须先有 `G ≃ \mathrm{Gal}(L/K)` 的识别」✗。

**🔴 本轮断指** ✓（**三件齐落** ✓，**判据先审可达性** ✓：探针 `.abgv52-scratch/probe-r199e.lean` ✓ **rc=0** ✓）：
由 **`IsGaloisWithGroup`** ✓ ＋ **`[FiniteDimensional K L]`** ✓ 直接供给三条 ✓ ——
**②** `G ≅ \mathrm{Gal}(L/K)` ✓✅：**Artin 界** ✓（mathlib `AlgEquiv.card_le` ✓，`Fixed.lean` ✓）
＋ **判据秩等式** ✓（`BTier.finrank_eq_card_of_isGaloisWithGroup` ✓，r184 ✓）**两侧夹逼** ✓
（**单射** ✓ 由 `FaithfulSMul` ✓ ＝ 判据**第一合取** ✓ —— 即源 `proposition-0-5` 之前的「`G` **忠实**作用」✓）；
**①** `G`-**指标正规基** ✓✅：mathlib `exists_linearIndependent_algEquiv_apply` ✓（**只需 `[FiniteDimensional]`** ✓，**不需** `IsGalois` ✓）
＋ **②** 的双射重指标 ✓ ＋ 秩等式 ⟹ **基** ✓（`basisOfLinearIndependentOfCardEqFinrank` ✓），且**乘性形**
`g • b h = b (g * h)` ✓ —— 正是源「**normal basis**」✓ 的**逐元形** ✓；
**③** **不动点 `L^G = K`** ✓✅：mathlib `FixedPoints.finrank_eq_card` ✓（**Artin 定理** ✓，`[Fintype G]` ＋ `[FaithfulSMul]` ✓）
＋ 秩等式 ⟹ **`[L : L^G] = [L : K]`** ✓ ⟹ **次数 1** ✓ ⟹ `L^G = K` ✓（`IntermediateField.finrank_eq_one_iff` ✓）。

**⚠ 源文对照** ✓（**承 §4.53 的纠正** ✓）：源 `proposition-0-5` **(b)** ✓（代数无关性 ✓）／**(c)** ✓（正规基 ✓）
（**印 254** ✓）就 **一般（非域）`L`** 陈述 ✓；本节是**同一内容在 `[Field L]` 下的形** ✓ ——
**⚠ 环档仍缺** ✗（mathlib 的 `FixedPoints` 与 Artin 界**均只域档** ✗，**登记** ✓）。

**⚠ 唯一剩余输入（登记** ✗**）** ✓：**`[FiniteDimensional K L]`** ✗ —— 源侧由 **`proposition-0-2(a)`** ✓
（[CHR68] p. 13 ✓ —— **⚠ 账目更正（第 207 轮** ✓**）**：该精确出处**仍不在 `raw/`** ✗（L37 已核 ✓），
**但**其**用点**（progenerator ✓）已在 `raw/Saltman1978` 印 528（＝ PDF 3 ✓）内**逐字可核** ✓，
端点 ＝ `GaloisProgeneratorHyp` ✓，**实体未证** ✗）供给：`S/R` `G`-Galois ⟹ **有限生成投射** ✓；
库内对应 **`GaloisProjectiveHyp`** ✓（`GaloisAlgebra_ABGV52 :235` ✓，**未证** ✗）。
**⚠ 后果** ✓✅：**`hdata` 不再是独立输入** ✓ —— 本节 **⑤** ✓ 内部供给之 ✓（**有限性除外** ✗），
**⑥** ✓ 展示「源侧数据 ＋ `IsGaloisWithGroup` ＋ 有限性 ⟹ `∃φ` ＋ 保作用同构」**无需 `hdata`** ✓。 -/

section CHRBridgeField

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {G : Type u} [Group G] [Fintype G]

/-- **② `G ≅ \mathrm{Gal}(L/K)`（域档）** ✓✅：**单射** ✓（`FaithfulSMul` ✓，判据第一合取 ✓）
＋ **两侧夹逼** ✓（`|G| ≤ |\mathrm{Gal}|` ✓ 由单射；`|\mathrm{Gal}| ≤ [L:K] = |G|` ✓ 由 **Artin 界** ✓ ＋ r184 秩等式 ✓）。
**⚠ 用途** ✓：它是 §4.10（`f \neq 0` ✗）与 §4.35（`hfix` ✗）两条登记的**共同入口** ✓ —— **本轮已通** ✓。 -/
theorem smulAlgEquivHom_bijective_of_isGaloisWithGroup [MulSemiringAction G L]
    [SMulCommClass G K L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    Function.Bijective (smulAlgEquivHom K G L) := by
  let _ : FaithfulSMul G L := hgal.1
  have hinj : Function.Injective (smulAlgEquivHom K G L) := by
    intro g h hgh
    refine eq_of_smul_eq_smul (fun x : L => ?_)
    have hx := congrArg (fun f : L ≃ₐ[K] L => f x) hgh
    simpa [smulAlgEquivHom, smulAlgEquiv] using hx
  have hcard : Fintype.card G = Fintype.card (L ≃ₐ[K] L) := by
    refine le_antisymm (Fintype.card_le_of_injective (smulAlgEquivHom K G L) hinj) ?_
    rw [← BTier.finrank_eq_card_of_isGaloisWithGroup (K := K) (A := L) (G := G) hKL hgal]
    exact AlgEquiv.card_le
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

/-- **① `G`-指标正规基（乘性形）** ✓✅：`g • b h = b (g * h)` ✓ —— 源 `proposition-0-5(c)` ✓（印 254 ✓）的
**逐元形** ✓（**基** ✓ ＝ 由 `G` 指标化 ✓，故「`L⁺ ≅ K[G]`」✓ 的向量形 ✓）。
**⚠ 机制** ✓：LI 家族由 **mathlib 的抽象正规基定理** ✓（`exists_linearIndependent_algEquiv_apply` ✓）取**子族** ✓
（沿 **②** 的双射 ✓ 重指标 ✓），再与 r184 秩等式**凑成基** ✓；**乘性** ✓ 由 z 的取法 `b h = h • z` ✓ 直接给出 ✓。 -/
theorem exists_normalBasis_of_isGaloisWithGroup [MulSemiringAction G L] [SMulCommClass G K L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    ∃ b : Module.Basis G K L, ∀ g h : G, g • b h = b (g * h) := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_smul K G L
    (smulAlgEquivHom_bijective_of_isGaloisWithGroup hKL hgal)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hx ?_, ?_⟩
  · exact (BTier.finrank_eq_card_of_isGaloisWithGroup (K := K) (A := L) (G := G) hKL hgal).symm
  · intro g h
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (mul_smul g h x).symm

/-- **源 `lemma-5-2` 的 `z`** ✓（源 `raw/Saltman1982.tex :658` ✓ 逐字「there is a `z \in L` such that
`\{\sigma(z)\}` is a **normal basis** for `L` over `K`」✓）：**存在 `z`** ✓ 使 `\{g \bullet z\}` **线性无关** ✓
且**张满** ✓ —— 即源义的「**生成正规基**」✓。
**⚠ 用途** ✓：源证明的下一步（避免 `t(g \bullet z) = 0` ✓，§4.10 ✓ 的 `\mathrm{exists\_eval\_mul\_ne\_zero}` ✓）**以此为输入** ✓。 -/
theorem exists_normalBasisElement_of_isGaloisWithGroup [MulSemiringAction G L] [SMulCommClass G K L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    ∃ z : L, LinearIndependent K (fun g : G => g • z) ∧
      Submodule.span K (Set.range (fun g : G => g • z)) = ⊤ := by
  obtain ⟨b, hb⟩ := exists_normalBasis_of_isGaloisWithGroup hKL hgal
  have hfun : (fun g : G => g • b 1) = fun g : G => b g := by
    funext g; rw [hb g 1, mul_one]
  exact ⟨b 1, by rw [hfun]; exact b.linearIndependent, by rw [hfun]; exact b.span_eq⟩

/-- **③ 不动点 `L^G = K`（点形）** ✓✅（**＝ r196 `hfix` ✓ 的形** ✓）：由 **Artin 定理** ✓
（`FixedPoints.finrank_eq_card` ✓：`[L : L^G] = |G|` ✓）＋ r184 秩等式 ✓ ⟹ `[L : L^G] = [L : K]` ✓ ⟹
**次数 1** ✓（`IntermediateField.finrank_eq_one_iff` ✓）⟹ **逐点落进 `K`** ✓。
**⚠ 口径** ✓：`L^G` 落为**显式构造的 `\mathrm{IntermediateField}`** ✓（`carrier := \{x \mid \forall g,\ g \bullet x = x\}` ✓），
其与 mathlib `FixedPoints.subfield` **载体逐字相同** ✓（`FixedPoints.finrank_eq_card` ✓ **可直接用作其秩** ✓，实测 defeq ✓）。 -/
theorem fixedPoints_eq_of_isGaloisWithGroup [MulSemiringAction G L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x := by
  let _ : FaithfulSMul G L := hgal.1
  let P : IntermediateField K L :=
    { carrier := {x : L | ∀ g : G, g • x = x}
      mul_mem' := fun hx hy g => by rw [smul_mul', hx g, hy g]
      one_mem' := fun g => by rw [smul_one]
      add_mem' := fun hx hy g => by rw [smul_add, hx g, hy g]
      zero_mem' := fun g => by rw [smul_zero]
      algebraMap_mem' := fun k g => by rw [Algebra.algebraMap_eq_smul_one, hKL g k 1, smul_one]
      inv_mem' := fun x hx g => by rw [smul_inv₀', hx g] }
  have hPL : Module.finrank ↥P L = Fintype.card G := FixedPoints.finrank_eq_card G L
  have hKLcard : Module.finrank K L = Fintype.card G :=
    BTier.finrank_eq_card_of_isGaloisWithGroup (K := K) (A := L) (G := G) hKL hgal
  have htower : Module.finrank K ↥P * Module.finrank ↥P L = Module.finrank K L :=
    Module.finrank_mul_finrank K ↥P L
  have hone : Module.finrank K ↥P = 1 := by
    rw [hPL, hKLcard] at htower
    exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos (by rw [one_mul]; exact htower)
  have hbot : P = ⊥ := IntermediateField.finrank_eq_one_iff.mp hone
  intro x hx
  have hxP : x ∈ P := hx
  rw [hbot, IntermediateField.mem_bot] at hxP
  exact hxP

/-- **⑤ 打包（`hdata` 形）** ✓✅：三件**合取** ✓ —— 即 r196 `realizationPropertyField_of_sourceData` ✓
所**假设**的逐点输入 ✓（`\exists (_b : \mathrm{Module.Basis}\ G\ K\ L)` ✓ ＋ 双射 ✓ ＋ 不动点 ✓）。
**⚠ 意义** ✓：`hdata` 由**输入** ✗ 变为**可供给** ✓（**有限性除外** ✗，见节头登记 ✓）。 -/
theorem exists_chrData_of_isGaloisWithGroup [MulSemiringAction G L] [SMulCommClass G K L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    ∃ (_b : Module.Basis G K L), Function.Bijective (smulAlgEquivHom K G L) ∧
      ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x :=
  ⟨(exists_normalBasis_of_isGaloisWithGroup hKL hgal).choose,
    smulAlgEquivHom_bijective_of_isGaloisWithGroup hKL hgal,
    fixedPoints_eq_of_isGaloisWithGroup hKL hgal⟩

end CHRBridgeField

section ChrRealizationPointwise

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **⑥ 点形实现（`hdata` 已删）** ✓✅：**源侧数据** ✓ ＋ **`BTier.IsGaloisWithGroup K L G`** ✓ ＋ **`[FiniteDimensional K L]`** ✓
⟹ `\exists \varphi : R \toₐ[F] K` ✓ 与**保作用同构** `L \simeq_K (S_0 \otimes_R K)` ✓ ——
**不再**以 `hdata`（r196 ✓）为假设 ✓（由 **⑤** ✓ 现场供给 ✓）。
**⚠ 断言强度 ≤ 证据层级** ✓：本条**只**是**点形**（固定 `(K, L)` ✓）；**谓词形**（`RealizationPropertyField` ✓）
的 `hdata` 删除**未做** ✗ —— 须把 `[FiniteDimensional K L]` 入 **∀-binder** ✓（**登记** ✓）。 -/
theorem exists_realization_of_isGaloisWithGroup
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    {K : Type} [Field K] [Algebra F K]
    {L : Type} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L] [SMulCommClass G K L] [SMulCommClass G F L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgalKL : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    ∃ φ : R →ₐ[F] K,
      letI : Algebra R K := φ.toRingHom.toAlgebra
      letI : Algebra R L := ((algebraMap K L).comp φ.toRingHom).toAlgebra
      letI := BTier.tensorMulSemiringAction (R := R) (T := K) (S := Localization.Away t) hRG
      ∃ e : L ≃ₐ[K] (TensorProduct R K (Localization.Away t)),
        ∀ (g : G) (y : L), e (g • y) = g • e y := by
  obtain ⟨b, hb, hfix⟩ := exists_chrData_of_isGaloisWithGroup hKL hgalKL
  let _ : Infinite K := infinite_of_algebra_of_infinite (F := F) (K := K)
  exact exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data
    (F := F) (G := G) (t := t) ht htinv hact_map hRG hgal hProj hS₀R hRQ hRGpoint b hb hfix

end ChrRealizationPointwise

/-- **登记** ✗：**唯一剩余输入 ＝ `[FiniteDimensional K L]`** ✓ —— 源侧由 `proposition-0-2(a)` ✓
（「`S` is a **projective** `R[G]`-module」✓，源引 **[CHR68] p. 13** ✓，**⚠ 账目更正（第 207 轮** ✓**）**：
该精确出处**仍不在 `raw/`** ✗（L37 已核 ✓），**但**其**用点**已在 `raw/Saltman1978` 印 528（＝ PDF 3 ✓）内可核 ✓
—— 同页证明给 **progenerator** ✓，端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）供给：
`S/R` `G`-Galois ⟹ **有限生成投射** ✓ ⟹ 域上**有限维** ✓；库内对应 `GaloisProjectiveHyp` ✓（**未证** ✗）。
**⚠ 后果** ✓：本节三件的**陈述**均以 `[FiniteDimensional K L]` 为前提 ✓ —— **不声称**去除它 ✗。 -/
theorem chrBridgeField_finiteness_gap_registered : True := trivial

/-- **登记** ✗：**环档仍缺** —— 本节三件**均域档** ✓（`[Field L]` ✓）：**Artin 界** ✓（`AlgEquiv.card_le` ✓）
与 `FixedPoints` ✓（不动域／Artin 定理 ✓）**在 mathlib 只域档** ✗；源 `proposition-0-5` ✓ 就**一般 `L`** 陈述 ✓
⟹ **环档（CHR 代数版）**仍须另建 ✗（**不声称**已落 ✗）。 -/
theorem chrBridgeField_ringTier_gap_registered : True := trivial

/-- **登记** ✗：**谓词形的 `hdata` 删除待办** —— `RealizationPropertyField`（§4.51 ✓）的 ∀-形**未含**
`[FiniteDimensional K L]` ✗ ⟹ 本节 **⑤** ✓ 的供给**不能**直接填入该 ∀-binder ✗；
**正解** ✓ ＝ 把有限性**入 binder** ✓（＝ 把源 `proposition-0-2(a)` 的**有限性显式化** ✓）—— **下一手** ✓。 -/
theorem realizationPropertyField_hdata_removal_registered : True := trivial

/-! ## 4.55 **源 `lemma-5.2` 的收口**：两条**数据前提**由 §4.54 的桥清空（第 200 轮）

**⚠ 起点** ✓（**承 §162.6 第 1 项** ✓）：§4.18 的 `lemma52Statement_nonzero_true` ✓✅ **已是定理** ✓，
但**带两条数据前提** ✗ —— **`(b : \mathrm{Module.Basis}\ G\ K\ L)`** ✓（`K`-基 ✓）与**识别桥** ✓
（`\mathrm{Function.Bijective}\ (\mathrm{smulAlgEquivHom}\ K\ G\ L)` ✓，§4.11 ✓／§4.17 ✓ 两条登记均记其为「**在册**」✗）。

**🔴 本轮断指** ✓：§4.54 的 **①** ✓（`G`-指标正规基 ✓）与 **②** ✓（识别桥 ✓）**正是**这两条 ✓ ⟹
由 **`IsGaloisWithGroup`** ✓ ＋ **`[FiniteDimensional K L]`** ✓ **现场供给** ✓ ⟹
**源 `lemma-5.2` 成为无数据前提的定理** ✓✅（**证明体**：`exists_chrData_of_isGaloisWithGroup` ✓ ＋ §4.18 的定理 ✓）。

**⚠ 源文对照** ✓（**逐字** ✓）：源 `raw/Saltman1982.tex :658` ✓（**印 275** ✓）「there is a `z \in L` such that
`\{\sigma(z)\}` is a **normal basis** for `L` over `K` and such that `t` evaluated at the `\sigma(z)`'s is a **unit**」✓ ——
本节 **③** ✓ 即该句的**逐字形** ✓（`\mathrm{IsUnit}` ✓；域上等价于 `\neq 0` ✓，**两形并存** ✓）。

**⚠ 唯一剩余输入** ✓：**`[FiniteDimensional K L]`** ✗（**同 §4.54** ✓ —— 源 `proposition-0-2(a)` ✓／[CHR68] p. 13 ✓，
**⚠ 账目更正（第 207 轮** ✓**）**：该精确出处**仍不在 `raw/`** ✗，**但**其**用点**已在
`raw/Saltman1978` 印 528（＝ PDF 3 ✓）内可核 ✓ —— 同页证明给 **progenerator** ✓，
端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）；**环档仍缺** ✗（同 §4.54 登记 ✓，**不复写** ✗）。 -/

section Lemma52Closure

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] [DecidableEq G]
variable (K L : Type u) [Field K] [Field L] [Algebra F K] [Algebra K L] [Algebra F L]
  [IsScalarTower F K L] [MulSemiringAction G L]

/-- **源 `lemma-5.2` 的收口（局部形）** ✓✅：**数据前提已清** ✓ —— 由 §4.54 的 **①**（正规基 ✓）与 **②**（识别桥 ✓）
现场供给 ✓；`[Infinite K]` 与源证明所引「because `K` is infinite」✓ 同形 ✓。 -/
theorem lemma52Statement_nonzero_of_isGaloisWithGroup [Infinite K]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    Lemma52StatementNonzero F G K L := by
  let _ : SMulCommClass G K L := ⟨fun g k x => hKL g k x⟩
  obtain ⟨b, hb, -⟩ :=
    exists_chrData_of_isGaloisWithGroup (K := K) (L := L) (G := G) hKL hgal
  exact lemma52Statement_nonzero_true F G K L b hb

/-- **源 `lemma-5.2` 的收口（源文口径）** ✓✅：只设 **`[Infinite F]`** ✓（＝ 源 `theorem-5-1` 的「with `F` infinite」✓），
`[Infinite K]` 由 **§4.50 的派生件** ✓ 供给 ✓（源 `lemma-5-2` 证明正用此 ✓）。 -/
theorem lemma52Statement_nonzero_of_isGaloisWithGroup_infF [Infinite F]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L] :
    Lemma52StatementNonzero F G K L := by
  let _ : Infinite K := infinite_of_algebra_of_infinite (F := F) (K := K)
  exact lemma52Statement_nonzero_of_isGaloisWithGroup F G K L hKL hgal

/-- **源 `lemma-5.2` 的收口（逐字「unit」形）** ✓✅：源句的**逐字形** ✓（`\mathrm{IsUnit}` ✓）——
与 `\neq 0` 形**并存** ✓（域上二者等价 ✓，`\mathrm{isUnit\_iff\_ne\_zero}` ✓）。 -/
theorem lemma52Statement_unit_of_isGaloisWithGroup [Infinite F]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) [FiniteDimensional K L]
    (t : MvPolynomial G F) (ht : t ≠ 0) :
    ∃ (z : L) (b : Module.Basis G K L), (∀ σ : G, b σ = σ • z) ∧
      IsUnit (MvPolynomial.aeval (fun σ : G => σ • z) t) := by
  let _ : Infinite K := infinite_of_algebra_of_infinite (F := F) (K := K)
  obtain ⟨z, b, hb, hne⟩ :=
    (lemma52Statement_nonzero_of_isGaloisWithGroup F G K L hKL hgal) t ht
  exact ⟨z, b, hb, isUnit_iff_ne_zero.mpr hne⟩

end Lemma52Closure

/-- **登记** ✗：**唯一剩余输入 ＝ `[FiniteDimensional K L]`** ✓（**同 §4.54** ✓）—— 源侧由 `proposition-0-2(a)` ✓
（[CHR68] p. 13 ✓ —— **⚠ 账目更正（第 207 轮** ✓**）**：该精确出处**仍不在 `raw/`** ✗（L37 已核 ✓），
**但**其**用点**已在 `raw/Saltman1978` 印 528（＝ PDF 3 ✓）内可核 ✓ —— 同页证明给 **progenerator** ✓，
端点 ＝ `GaloisProgeneratorHyp` ✓，**实体未证** ✗）供给；库内对应 `BTier.GaloisProjectiveHyp` ✓（**未证** ✗）。**不声称**去除它 ✗。 -/
theorem lemma52_finiteness_gap_registered : True := trivial

/-- **登记** ✓：**§4.5 具名残余的状态收口** ✓ —— `Lemma52Statement`（§4.5 ✓）的**假设类为空** ✗
（`t = 0` 反驳 ✓，`Lemma52Statement.false_at_zero` ✓ **在库** ✓）⟹ 该条**保留作留痕** ✓，**非**「未证」✗；
**修正形** `Lemma52StatementNonzero`（§4.18 ✓）**自本轮起无数据前提** ✓✅ ⟹ 源 `lemma-5.2` 的余项**只剩**
**有限性** ✗ 与**环档** ✗ 两条 ✓（**不声称**源 `theorem-5-1` 整体已证 ✗ —— 那是 (c) 款**环档**的事 ✓）。 -/
theorem lemma52_residual_closed_registered : True := trivial

/-! ## 4.56 **域档 (c) 款的有限档**：「**有限性入 binder**」＋ **`hdata` 已删的装配**（第 201 轮）

**⚠ 起点** ✓（**承 §4.54 ⑨／§4.55 ④ 的两条待办** ✗）：`RealizationPropertyField`（§4.51 ✓）的 **∀-形未含**
`[FiniteDimensional K L]` ✗ ⟹ §4.54 ⑤ 的供给**不能**直接填入该 binder ✗。

**🔴 本轮断指** ✓：落**有限档变体谓词** ✓（**`[FiniteDimensional K L]` 入 ∀-binder** ✓，＝ 源 `proposition-0-2(a)` 的
**有限性显式化** ✓）＋ 其 **`rfl` 型外形锁** ✓（**判别力已证** ✓：变异件**删去该 binder** ⟹ `rfl` 失败 ✓，
`probe-r201b.lean` ✓ 读数 ＝ `Not a definitional equality` ✓）＋ **强度序** ✓（**源忠实 ⟹ 有限档** ✓，
即有限档为**弱化档** ✓ —— 与 r198 的「环 ⟹ 域」**同款单向** ✓）＋ **装配件** ✓✅（**`hdata` 已删** ✗⟹✓：
由 §4.54 ⑤ ✓ 现场供给 ✓）。

**⚠ 口径（不越界** ✗**）** ✓：**源忠实谓词 `RealizationPropertyField` 一字不动** ✓ —— 把有限性写进**它**的 binder
即**口径偏离** ✗（源 `definition-1-1`(c) ✓ 的量词**不含**有限性 ✓，它是 CHR 理论的**推论** ✓）
⟹ **另立名** ✓（`\mathrm{RealizationPropertyFieldFinite}` ✓），**两档并存** ✓、**强度序**明示 ✓。
**⚠ 断言强度 ≤ 证据层级** ✓：本节**不声称**源 (c) 款已证 ✗ —— 有限档**弱于**源忠实档 ✓，
且源忠实档的**唯一缺口**仍是**有限性** ✗（源 `proposition-0-2(a)` ✓／[CHR68] p. 13 ✓ ——
**⚠ 账目更正（第 207 轮** ✓**）**：精确出处**仍不在 `raw/`** ✗，**但**其**用点**已在 `raw/Saltman1978` 印 528 ✓ 内可核 ✓，
端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）。 -/

/-- **有限档 (c) 款谓词** ✓：`RealizationPropertyField`（§4.51 ✓）的**同一形** ✓，唯 **`[FiniteDimensional K L]` 入 ∀-binder** ✓
（＝ 源 `proposition-0-2(a)` 的**有限性显式化** ✓）。
**⚠ 档位** ✓：本谓词**弱于**源忠实谓词 ✓（`realizationPropertyFieldFinite_of_realizationPropertyField` ✓ 单向 ✓）；
**⚠ 非**源形 ✗（源 (c) 的量词不含有限性 ✓）—— **两档并存** ✓，**勿混用** ✗。 -/
def RealizationPropertyFieldFinite (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] : Prop :=
  ∀ (K : Type) [Field K] [Algebra F K]
    (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L] [FiniteDimensional K L]
    (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
    BTier.IsGaloisWithGroup K L G hKL →
      ∃ (φ : R →ₐ[F] K),
        letI : Algebra R K := φ.toRingHom.toAlgebra
        Nonempty (L ≃ₐ[K] (TensorProduct R K S))

/-- **外形锁** ✓（`rfl` 型 ✓）：有限档谓词与**含 `[FiniteDimensional K L]` 的展开体逐字相同** ✓ ——
**binder 被删／被移** ✗ 即编译失败 ✓。
**⚠ 判别力（L43／r198 五件套** ✓**）** ✓：**变异件负例已实跑** ✓（`probe-r201b.lean` ✓）——
**变异件 ＝ 删去 `[FiniteDimensional K L]`** ✗（＝ 源忠实形 ✓）**使本 `rfl` 失败** ✓
（读数 ＝ `Not a definitional equality` ✓，`rc=1` ✓）⟹ 本锁**能**分辨两档 ✓。 -/
theorem RealizationPropertyFieldFinite.shape {F : Type*} [Field F] {G : Type*} [Group G] [Fintype G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] :
    (RealizationPropertyFieldFinite F G R S)
      = (∀ (K : Type) [Field K] [Algebra F K]
          (L : Type) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
          [MulSemiringAction G L] [FiniteDimensional K L]
          (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
          BTier.IsGaloisWithGroup K L G hKL →
            ∃ (φ : R →ₐ[F] K),
              letI : Algebra R K := φ.toRingHom.toAlgebra
              Nonempty (L ≃ₐ[K] (TensorProduct R K S))) :=
  rfl

/-- **强度序（可证方向）** ✓：**源忠实 ⟹ 有限档** ✓ —— 把有限档的量词实例（含 `[FiniteDimensional K L]` ✓）
喂给源忠实形即可 ✓；**反向未证** ✗（那正是**有限性缺口** ✓，**登记** ✓）。
**⚠ 意义** ✓：本条把「有限档是**弱化档**」形式化 ✓（**不声称**严格性 ✗，承 r198 ✓）。 -/
theorem realizationPropertyFieldFinite_of_realizationPropertyField
    {F : Type*} [Field F] {G : Type*} [Group G] [Fintype G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] (h : RealizationPropertyField F G R S) :
    RealizationPropertyFieldFinite F G R S := by
  intro K _ _ L _ _ _ _ _ _ hKL hgal
  exact h K L hKL hgal

section RealizationFieldFinite

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **有限档 (c) 款 · 源侧总装（`hdata` 已删）** ✓✅：**§4.51 的全部源侧数据** ✓ ＋ **`F` 无限** ✓
⟹ **`RealizationPropertyFieldFinite F G R S_0`** ✓ —— **不再**以 `hdata`（r196 ✓）为假设 ✓
（由 §4.54 ⑤ ✓ **现场供给** ✓）。
**⚠ 与 §4.51 之别** ✓：**仅**少了 `hdata` ✓（其余假设**逐条相同** ✓）⟹ 本件的**假设表严格短于** §4.51 ✓；
**代价** ✓：结论**弱化**为有限档 ✓（**如实登记** ✓，**不声称**源 (c) ✓）。 -/
theorem realizationPropertyFieldFinite_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F) :
    RealizationPropertyFieldFinite F G R (Localization.Away t) := by
  intro K _ _ L _ _ _ _ _ _ hKL hgalKL
  let _ : SMulCommClass G K L := ⟨fun g k x => hKL g k x⟩
  let _ : SMulCommClass G F L := ⟨fun g f x => by
    rw [← IsScalarTower.algebraMap_smul K f x, ← IsScalarTower.algebraMap_smul K f (g • x),
      hKL g (algebraMap F K f) x]⟩
  obtain ⟨b, hb, hfix⟩ := exists_chrData_of_isGaloisWithGroup hKL hgalKL
  let _ : Infinite K := infinite_of_algebra_of_infinite (F := F) (K := K)
  obtain ⟨φ, e, _he⟩ := exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data
    (F := F) (G := G) (t := t) ht htinv hact_map hRG hgal hProj hS₀R hRQ hRGpoint b hb hfix
  refine ⟨φ, ?_⟩
  let _ : Algebra R K := φ.toRingHom.toAlgebra
  exact ⟨e⟩

end RealizationFieldFinite

/-- **登记** ✗：**有限档已「除源侧数据外无条件」** ✓✅（**`hdata` 已删** ✓）；**源忠实档仍待有限性** ✗ ——
其唯一缺口 ＝ `[FiniteDimensional K L]` ✓（源 `proposition-0-2(a)` ✓／[CHR68] p. 13 ✓ ——
**⚠ 账目更正（第 207 轮** ✓**）**：精确出处**仍不在 `raw/`** ✗，**但**其**用点**已在 `raw/Saltman1978` 印 528 ✓ 内可核 ✓；
库内 `BTier.GaloisProjectiveHyp` ✓ **未证** ✗；端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）。
**⚠ 不声称** ✗：源 `definition-1-1`(c) ✓（**无有限性 binder** 的形 ✓）**未证** ✗；**两档并存** ✓，**勿混用** ✗。 -/
theorem realizationPropertyFieldFinite_gap_registered : True := trivial

/-! ## 4.57 **有限档的见证层**：三款齐备 ⟹ **见证可达（除源侧数据外无条件）**（第 202 轮）

**⚠ 起点** ✓（**承 §164.7 第 1 项** ✓）：§4.53 ✓ 的域档见证（`\mathrm{GenericExtensionWitnessField}` ✓）
以 **`hdata`** 为假设 ✗（r198 ✓）；§4.56 ✓ 起有限档 (c) 款**除源侧数据外无条件** ✓ ⟹ 本轮把**见证层**同步到有限档 ✓。

**🔴 本轮断指** ✓（**判据先审可达性** ✓：`probe-r202a.lean` ✓ **rc=0** ✓、**零警告** ✓）：**八件** ✓ ——
谓词 ✓／`rfl` 型锁 ✓（**判别力已证** ✓：变异件**换回非有限档** ✗ ⟹ `rfl` 失败 ✓，`probe-r202b.lean` ✓）／
**强度序** ✓（**非有限域档 ⟹ 有限档** ✓）／见证结构 ✓／打包 ✓／**源侧数据 ⟹ 谓词** ✓／
**源侧数据 ⟹ 见证** ✓✅（**库内首件「除源侧数据外无条件」的见证** ✓）／登记 ✓。

**⚠ 口径（不越界** ✗**）** ✓：**r198 的域档谓词与见证结构一字不动** ✓（各档**并存** ✓，**强度序**明示 ✓）；
**⚠ 断言强度 ≤ 证据层级** ✓：本节的见证是**有限档 ＋ 弱化档**（第三款取**域读** ✗）——
**不声称**源 `definition-1-1`（**环档** ✓）的见证已得 ✗，亦**不声称**源 `theorem-5-1`／`theorem-2-1` 已证 ✗。 -/

/-- **有限档三合取谓词** ✓：`\mathrm{IsGenericExtensionField}`（§4.53 ✓）的**同一形** ✓，
唯第三款取 **`\mathrm{RealizationPropertyFieldFinite}`**（§4.56 ✓）✓。
**⚠ 档位** ✓：本谓词**弱于** §4.53 的域档谓词 ✓（第三款处 ✓；**强度序**见下 ✓），**两档并存** ✓。 -/
def IsGenericExtensionFieldFinite (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
  BTier.IsGaloisWithGroup R S G hRG ∧
  RealizationPropertyFieldFinite F G R S

/-- **外形锁** ✓（`rfl` 型 ✓）：有限档谓词与**三合取展开体逐字相同** ✓ —— 合取内容或**第三款的档**漂移 ✗
即编译失败 ✓。
**⚠ 判别力（L43／r198 五件套** ✓**）** ✓：**变异件负例已实跑** ✓（`probe-r202b.lean` ✓）——
**变异件 ＝ 第三合取换回非有限档** ✗ **使本 `rfl` 失败** ✓（读数 ＝ `Not a definitional equality` ✓，`rc=1` ✓）
⟹ 本锁**能**分辨「有限档」与「非有限档」✓。 -/
theorem IsGenericExtensionFieldFinite.shape {F : Type*} [Field F] {G : Type*} [Group G] [Fintype G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (IsGenericExtensionFieldFinite F G R S hRG)
      = ((∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
            Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
          BTier.IsGaloisWithGroup R S G hRG ∧ RealizationPropertyFieldFinite F G R S) :=
  rfl

/-- **强度序（可证方向）** ✓：**非有限域档 ⟹ 有限档** ✓（第三款用 §4.56 的强度序 ✓）；
**反向未证** ✗（＝ 有限性缺口 ✓，**登记** ✓）。 -/
theorem isGenericExtensionFieldFinite_of_isGenericExtensionField
    {F : Type*} [Field F] {G : Type*} [Group G] [Fintype G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    {hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)}
    (h : IsGenericExtensionField F G R S hRG) :
    IsGenericExtensionFieldFinite F G R S hRG :=
  ⟨h.1, h.2.1, realizationPropertyFieldFinite_of_realizationPropertyField h.2.2⟩

/-- **有限档见证数据** ✗：与 `\mathrm{GenericExtensionWitnessField}`（§4.53 ✓）**同款打包** ✓，
唯 `isGeneric` 取**有限档**谓词 ✓。
**⚠ 口径** ✓：**弱化档 ＋ 有限档**见证 ✗（**非**源 `theorem-2-1`／`theorem-5-1` 的见证 ✓，见节头 ✓）。 -/
structure GenericExtensionWitnessFieldFinite (F : Type v) [Field F] (A : Type u) [Group A]
    [Fintype A] where
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
  /-- **有限档**三款 ✓（第三款取**有限档 ＋ 域读** ✗）。 -/
  isGeneric : IsGenericExtensionFieldFinite F A R S hRG

/-- **有限档见证打包** ✓：三款齐（第三款**有限档** ✗）⟹ `\mathrm{Nonempty}\ (\mathrm{GenericExtensionWitnessFieldFinite}\ F\ G)` ✓
（与 §4.53 ✓／§4.51 ✓ 的打包件**同款** ✓ —— `\exists` **不接受实例绑定** ⟹ 须显式打包 ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_clauses {F : Type v} [Field F] {G : Type u}
    [Group G] [Fintype G] {R S : Type u}
    [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))
    (hb : BTier.IsGaloisWithGroup R S G hRG) (hc : RealizationPropertyFieldFinite F G R S) :
    Nonempty (GenericExtensionWitnessFieldFinite F G) :=
  ⟨{ R := R, S := S, hRG := hRG, isGeneric := ⟨ha, hb, hc⟩ }⟩

section FiniteWitnessEndpoint

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **有限档谓词 · 源侧总装** ✓：`(a)` 款（假设 ✓）＋ `(b)` 款（假设 ✓）＋ **有限档 `(c)` 款**
（§4.56 ✓ 的装配件 ✓，**`hdata` 已删** ✓）⟹ `\mathrm{IsGenericExtensionFieldFinite}\ F\ G\ R\ (\mathrm{Localization.Away}\ t)` ✓
（**rfl 级对接** ✓，**不重证** ✓）。 -/
theorem isGenericExtensionFieldFinite_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
      w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) :
    IsGenericExtensionFieldFinite F G R (Localization.Away t) hRG :=
  ⟨ha, hgal,
    realizationPropertyFieldFinite_of_sourceData (F := F) (G := G) (t := t) ht htinv hact_map hRG
      hgal hProj hS₀R hRQ hRGpoint hinf⟩

/-- **有限档见证可达（除源侧数据外无条件）** ✓✅（**库内首件** ✓）：同一批源侧数据 ✓ ＋ `(a)` 款 ✓
⟹ `\mathrm{Nonempty}\ (\mathrm{GenericExtensionWitnessFieldFinite}\ F\ G)` ✓ —— **不再**以 `hdata`（r196 ✓／§4.53 ✓）
为假设 ✓（`(c)` 款由 §4.56 ✓ 现场供给 ✓）。
**⚠ 断言强度 ≤ 证据层级** ✓：本见证是**有限档 ＋ 弱化档** ✗ —— **不声称**源 `theorem-5-1` 的结论已得 ✗。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_sourceData
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    {R : Type} [CommRing R] [Algebra R (Localization.Away t)] [Algebra F R]
    [IsScalarTower F R (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    [Algebra R (NoetherField F G)] [IsScalarTower F R (NoetherField F G)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : R) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup R (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp R (Localization.Away t) G hRG)
    (hS₀R : ∀ r : R,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap R (Localization.Away t) r)
        = algebraMap R (NoetherField F G) r)
    (hRQ : ∀ r : R,
      algebraMap R (NoetherField F G) r ∈ (awayToFieldAlg (F := F) (G := G) t ht).range)
    (hRGpoint : ∀ (g : G) (r : R),
      g • algebraMap R (NoetherField F G) r = algebraMap R (NoetherField F G) r)
    (hinf : Infinite F)
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
      w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) :
    Nonempty (GenericExtensionWitnessFieldFinite F G) :=
  ⟨{ R := R, S := Localization.Away t, hRG := hRG,
     isGeneric := isGenericExtensionFieldFinite_of_sourceData (F := F) (G := G) (t := t) ht htinv
       hact_map hRG hgal hProj hS₀R hRQ hRGpoint hinf ha }⟩

end FiniteWitnessEndpoint

/-- **登记** ✗：**见证的三个档位**（本节与 §4.51 ✓／§4.53 ✓ 合读）——
**(i)** **有限档 ＋ 弱化档** ✓✅：**除源侧数据外无条件** ✓（本节上方 ✓，**库内首件** ✓）；
**(ii)** **非有限域档** ✗：仍以 `hdata` 为假设 ✓（§4.53 的 `\mathrm{nonempty\_genericExtensionWitnessField\_of\_sourceData}` ✓）；
**(iii)** **源形（环档）** ✗：**未证**（须 **CHR 代数版** ✓，§4.54 ⑧ ✓）。
**⚠ 三档并存** ✓、**勿混用** ✗；**不声称**源 `theorem-5-1`／`theorem-2-1` 已证 ✗。 -/
theorem genericExtensionWitnessFieldFinite_gap_registered : True := trivial

/-! ## 4.58 **源 `theorem-5-1` 的域档有限孪生**：具名陈述 ＋ **端到端可达性审计（判据下调）**（第 203 轮）

**⚠ 起点** ✓（**承 §165.6 第 1 项** ✓）：登记的目标是「**源 `theorem-5-1` 的域档端到端**」✗ ——
`\mathrm{Theorem51Statement}`（本件 `:257` ✓）的域档孪生：`\mathrm{IsRationalOver}` ＋ `[Infinite F]` ⟹ 见证 ✓。

**🔴 判据先审可达性（r196 纪律** ✓**）—— 审计结论：不可达** ✗**（本会话** ✗**）**：端到端的**唯一**结构性缺口
＝ 源侧数据的两项**外部输入** ✓（**逐条见下方登记** ✓）；**其余全部在库内可供给** ✓
（含 **`hfix`** ✓ —— **r199 已清** ✓，§4.54 ③ ✓）⟹ **判据下调** ✓ 为「**模两项具名外部输入**的端到端」✓。

**🔴 本轮落地** ✓（**探针两件** ✓：`probe-r203a.lean` ✓ **rc=0** ✓、**零警告** ✓；`probe-r203b.lean` ✓ **rc=1** ✓）：
**①** **具名陈述** ✓（`\mathrm{Theorem51StatementFieldFinite}` ✓ —— 把**可达目标**固定 ✓）＋ **②** **`rfl` 型锁** ✓
（**判别力已证** ✓：变异件**换回非有限档见证** ✗ ⟹ `rfl` 失败 ✓）＋ **③** **强度序** ✓
（**源形 ⟹ 有限档** ✓ —— 链：**环 ⟹ 域** ✓（r198 ⑤ ✓）⟹ **域 ⟹ 有限** ✓（r202 ③ ✓））＋ **④ 审计登记** ✓。

**⚠ 断言强度 ≤ 证据层级** ✓：**① 未证** ✗（**不声称**已证 ✗）；**③** 只给「源形 ⟹ 本形」✓（**不声称**严格性 ✗）。 -/

/-- **源 `theorem-5-1` 的域档有限孪生**（**具名陈述** ✓）：`\mathrm{Theorem51Statement}`（本件 `:257` ✓）的**同一形** ✓，
唯结论取 **`\mathrm{Nonempty}\ (\mathrm{GenericExtensionWitnessFieldFinite}\ F\ G)`** ✓（＝ **有限档 ＋ 弱化档**见证 ✓，
承 r201／r202 ✓）。
**⚠ 口径** ✓：**非**源结论 ✗（源要**环档**见证 ✓，§4.53 裁决 ✓）；本陈述是**可达目标的固定** ✓；
**⚠ 未证** ✗（见本节审计登记 ✓）—— **不声称**已证 ✗。 -/
def Theorem51StatementFieldFinite (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] : Prop :=
  Infinite F → ∀ (L : Type u) [Field L] [Algebra F L] [MulSemiringAction G L]
    [SMulCommClass G F L],
    IsRationalOver F ↥(FixedPoints.subalgebra F L G) →
      Nonempty (GenericExtensionWitnessFieldFinite F G)

/-- **外形锁** ✓（`rfl` 型 ✓）：本陈述与**两段展开体逐字相同** ✓ —— 前提被吞 ✗、结论的**见证档位**漂移 ✗
即编译失败 ✓。
**⚠ 判别力（L43／r198 五件套** ✓**）** ✓：**变异件负例已实跑** ✓（`probe-r203b.lean` ✓）——
**变异件 ＝ 结论换回非有限档见证** ✗（`\mathrm{GenericExtensionWitnessField}` ✓）**使本 `rfl` 失败** ✓
（读数 ＝ `Not a definitional equality` ✓，`rc=1` ✓）⟹ 本锁**能**分辨两档 ✓。 -/
theorem Theorem51StatementFieldFinite.shape (F : Type u) [Field F] (G : Type u) [Group G]
    [Fintype G] :
    (Theorem51StatementFieldFinite F G)
      = (Infinite F → ∀ (L : Type u) [Field L] [Algebra F L] [MulSemiringAction G L]
          [SMulCommClass G F L],
          IsRationalOver F ↥(FixedPoints.subalgebra F L G) →
            Nonempty (GenericExtensionWitnessFieldFinite F G)) :=
  rfl

/-- **强度序（可证方向）** ✓：**源形 ⟹ 本形** ✓ —— 由源形见证（**环档** ✓）经 **环 ⟹ 域** ✓（r198 ⑤ ✓）
再经 **域 ⟹ 有限** ✓（r202 ③ ✓）得**有限档**见证 ✓（**两次弱化，均单向** ✓）。
**⚠ 意义** ✓：本条把「**本形弱于源形**」形式化 ✓（**不声称**严格性 ✗ —— **反向未证** ✗，那正是**环档缺口** ✓）。 -/
theorem theorem51StatementFieldFinite_of_theorem51Statement
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (h : Theorem51Statement F G) : Theorem51StatementFieldFinite F G := by
  intro hinf L _ _ _ _ hL
  obtain ⟨R, S, hRG, hisg⟩ := h hinf L hL
  exact ⟨R, S, hRG,
    isGenericExtensionFieldFinite_of_isGenericExtensionField
      (isGenericExtensionField_of_isGenericExtension hisg)⟩

/-- **登记** ✗：**域档端到端的可达性审计**（**判据先审可达性** ✓，r196 纪律 ✓）——
**结论** ✓：§165.6 登记的「**域档端到端**」**不可达** ✗（**本会话** ✗），**唯一**结构性缺口 ＝ 源侧数据的两项输入：
**(i)** **`hgal`** ✓（构造出的 `S/R` 的 **`G`-Galois 性** ✓）—— 源引 `proposition-0-2(c)` ✓
（「there are `F` algebras `R'' \subset S''` … `S''/R''` is Galois with group `G`」✓，源引 **[Sal78b] p. 528** ✓，
**⚠ 账目更正（第 207 轮** ✓**）**：该源**已在 `raw/Saltman1978`** ✓（印 528 ＝ PDF 3 ✓，**回印核** ✓）⟹
原「**不在 `raw/`**」✗ **作废** ✓，**具名端点** ＝ `GaloisFiniteGenerationDescentHyp` ✓，**实体未证** ✗）；
**(ii)** **`hProj`** ✓（`\mathrm{GaloisProjectiveHyp}` ✓ ＝ **有限生成投射性** ✓）—— 源 `proposition-0-2(a)` ✓
（源引 **[CHR68] p. 13** ✓，**⚠ 同上更正** ✓：精确出处 `[CHR68] p. 13` **仍不在 `raw/`** ✗（L37 已核 ✓），
**但** Sal78b 印 528 证明内的 progenerator 断言**已可核** ✓ ⟹ **具名端点** ＝ `GaloisProgeneratorHyp` ✓，
**实体未证** ✗）。
**⚠ 其余全部在库内可供给** ✓：`(a)` 款 ✓（r188 ✓）／`hact_map` ✓ 与 `hS_0R` ✓（§4.48 ✓ 的**一行** ✓）／
`hRQ`／`hRGpoint`／`hRA` ✓（§4.47 ✓ **载体具体化**后**内部导出** ✓）／**`hfix`** ✓（**r199 已清** ✓）／
`t` 与超越基 ✓（§4.19--§4.26 ✓）。
⟹ **判据下调** ✓：「**域档端到端**」⟹「**模两项具名端点**的端到端」✓；
**⚠ 残余分类账归类（第 207 轮更正** ✓**）** ✓：两项原属「**源同状态**（源引外部文献、**不在 `raw/`**）」✗
⟹ 按账**非本会话可落** ✓；**现账** ✓ 改为「**源在 `raw/` 内、实体未落**」✓ ⟹
**「非本会话可落」✗ 作废** ✓、改为「**可落而未落**」✓（**工作量未减** ✗ —— 两具名端点均无证明 ✗）。
**⚠ 不声称**源 `theorem-5-1` 已证 ✗。 -/
theorem theorem51_endToEnd_reachability_audited : True := trivial

/-! ## 4.59 **Saltman1982 页号普查 ＋ 回印核**（第 204 轮）—— **修正 1 处** ✗→✓ ＋ **§4.50 散文回链** ✓

**⚠ 起点** ✓（**承 §4.53 的页号回填登记** ✓ ＋ **§166.6 的次期** ✓）：r198 发现 `GenericExtension_ABGV52` 头注
把 `definition-1-1` 的页写成「印 **254**」✗（实在 **印 255** ✓）⟹ 本轮**回填** ✓。

**🔴 普查（全库** ✓**）** ✓：`grep` 全库「印 NNN」引用 **82 处** ✓ —— **Saltman1982 系**（印 253--257／265／274--275／279／281--282 ✓）
＋ **Saltman1984 系**（印 169--215 ✓ —— **r178／r179 已全篇回印核** ✓，**偏移 ＝ PDF ＋ 164** ✓）。
**⚠ 回印核（PDF 目视** ✓**，`pdftoppm -r 150` ✓）** ✓：**载重三页** ✓ ——
**印 257**（＝ **PDF 8** ✓）逐字「**THEOREM 2.1.** Suppose `F(\rho(r))/F` is a **cyclic** extension. Then there is a
**generic Galois extension for `A` over `F`**」✓（`\mathrm{Theorem21Statement}` 的源 ✓）；
**印 274**（＝ **PDF 25** ✓）逐字「**THEOREM 5.1.** Let `F`, `L`, and `G` be as above, **with `F` infinite**. If `L^G` is
rational over `F`, then there is a generic Galois extension for `G` over `F`」✓ ＋ **Remark**「The converse of 5.1 is
false. `C_{47}` …」✓ ＋ 证明首句「By **0.2(c)**, there is an `s \in R_1` and an algebra `S \supseteq R = R_1(1/s)`
such that `S/R` is Galois with group `G`」✓（**r203 审计的 `hgal` 出处在此** ✓）；
**印 275**（＝ **PDF 26** ✓）逐字「**Since some normal basis exists**, `f` is a nonzero polynomial」✓ ＋
「By the **algebraic independence of the `\sigma`'s**, `f'` is nonzero」✓ ＋「because `K` is **infinite**」✓ ＋
「**Lemma 5.2 and Theorem 5.1 have been proven.**」✓ —— **三页均与库内引用逐字相符** ✓。

**🔴 修正（1 处** ✗→✓**）** ✓：`GenericExtension_ABGV52` 的 `\mathrm{isGenericExtension\_iff\_isGenericObjectEG}` ✓ 的
**依据行** ✓：**印 254** ✗ ⟹ **印 255** ✓（`definition-1-1` 与 §1 标题同在 **印 255** ＝ **PDF 6** ✓；
**印 254** 是 §0 的 `proposition-0-5` ＋ **强调句**所在页 ✓，**两者不可混用** ✗）。
**加注** ✓：库内**其余**「印 254」引用 ✓ **均指 §0 的 `proposition-0-5`／强调句** ✓ ⟹ **正确** ✓（**不改** ✓）。

**⚠ 登记** ✓：**残余** ＝ **未逐一目视**的 Saltman1982 页（印 253／256／258／265／279／281／282 ✓ 等）✗ ——
**本节只核载重三页** ✓（**L19 口径** ✓：**未命中不得用于排除** ✗）；**下一轮回核** ✓ 如需 ✓。 -/

/-- **登记** ✓：**Saltman1982 页号普查（r204）** ✓ —— 全库 **82 处**「印 NNN」✓；**载重三页回印目视** ✓
（印 257 ＝ PDF 8 ✓／印 274 ＝ PDF 25 ✓／印 275 ＝ PDF 26 ✓，**均逐字相符** ✓）；**修正 1 处** ✗→✓
（`GenericExtension_ABGV52` 依据行 **254 → 255** ✓）；**其余「印 254」引用均指 §0** ✓（**正确** ✓）。
**⚠ 未逐一目视者为残余** ✗（**L19**：**未命中不得用于排除** ✓）。 -/
theorem saltman1982_page_citations_audited : True := trivial

/-! ## 4.60 **载体具体化的端到端**：源侧数据 ＋ 两项外部输入 ⟹ **有限档见证**（第 205 轮）

**⚠ 起点** ✓（**承 §167.7 的当前主攻** ✓）：§166.6 登记的「**模两项外部输入**的端到端 · **数据接线**」✗ ——
即把 **§4.19--§4.26** ✓（超越基 ✓／`t` ✓／`R_1 = F[a]` ✓／清分母 ✓）＋ **§4.47／§4.48** ✓（**载体具体化** ✓：
`R := ↥S` ✓、`hle` ✓、`hS_{\rm fix}` ✓）＋ **r202 ⑦** ✓ 接成**一条**定理 ✓。

**🔴 本轮断指** ✓（**判据先审可达性** ✓：`probe-r205a.lean` ✓ **rc=0** ✓、**零警告** ✓）：**一条**定理 ✓ ——
**假设表** ✓ ＝ **源侧构造输入**（`S` ✓／`t` ✓／`hle` ✓／`hS_{\rm fix}` ✓／`hact_{\rm map}` ✓／`hS_0R` ✓／`ha` ✓／
`hinf` ✓／`hRG` ✓）＋ **两项外部输入** ✓（`hgal` ✓／`hProj` ✓）；**结论** ✓ ＝
`\mathrm{Nonempty}\ (\mathrm{GenericExtensionWitnessFieldFinite}\ F\ G)` ✓（**有限档 ＋ 弱化档**见证 ✓）。
**⚠ 相对 r202 ⑦ 的**弱化** ✓**：`hRQ` ✓ 与 `hRGpoint` ✓ **两项被消掉** ✓（**载体具体化**后**内部导出** ✓
—— §4.48 ✓ 的 `hRQ` ✓ 由 `hle` ＋ 载体步 ✓／`hRGpoint` ✓ 由 `hS_{\rm fix}` ✓）。

**⚠ 口径（不越界** ✗**）** ✓：**不声称**源 `theorem-5-1` 已证 ✗ —— 本件的假设表**仍含两项具名端点** ✓
（`hgal` ⟸ 源 `proposition-0-2(c)` ✓／**[Sal78b] p. 528** ✓；`hProj` ⟸ 源 `proposition-0-2(a)` ✓／**[CHR68] p. 13** ✓，
**⚠ 账目更正（第 207 轮** ✓**）**：Sal78b **已在 `raw/Saltman1978`** ✓（印 528 ＝ PDF 3 ✓，**回印核** ✓）⟹
原「**均不在 `raw/`**」✗ **作废** ✓；**现账** ✓ ＝ 「源在 `raw/` 内、**实体未落**」✗
（端点 ＝ `GaloisFiniteGenerationDescentHyp` ✓／`GaloisProgeneratorHyp` ✓，**均无证明** ✗）；
**⚠** [CHR68] p. 13 本身**仍不在 `raw/`** ✗）；本件**只**证明「**接线已通**」✓。
**⚠ 一处实例教训** ✓（**探针期自纠** ✗→✓）：`hS_0R` ✓ 须用**规范** `S.\mathrm{toAlgebra}` ✓ ⟹
**不得**再引入 `[Algebra ↥S (\mathrm{NoetherField}\ F\ G)]` ✗（**重复实例** ⟹ 类型错配 ✗）。 -/

section CarrierEndToEnd

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **载体具体化的端到端** ✓✅：**源侧构造数据** ✓ ＋ **两项外部输入** ✓ ⟹ **有限档见证** ✓；
`hRQ` ✓／`hRGpoint` ✓ **已由载体具体化消掉** ✓（§4.48 ✓）。
**⚠ 断言强度 ≤ 证据层级** ✓：**不声称**源定理已证 ✗（假设表含两项外部输入 ✓，见节头 ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_subalgebra
    {S : Subalgebra F (NoetherField F G)}
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ (g : G), g • t = t)
    (hle : S ≤ Subalgebra.restrictScalars F (Algebra.adjoin (MvPolynomial G F)
      ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G))))
    (hS_fix : ∀ (g : G) {x : NoetherField F G}, x ∈ S → g • x = x)
    [Algebra ↥S (Localization.Away t)] [IsScalarTower F ↥S (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : ↥S) (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup ↥S (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp ↥S (Localization.Away t) G hRG)
    (hS₀R : ∀ r : ↥S,
      awayToFieldAlg (F := F) (G := G) t ht (algebraMap ↥S (Localization.Away t) r)
        = algebraMap ↥S (NoetherField F G) r)
    (hinf : Infinite F)
    (ha : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (↥S ≃ₐ[F] Localization.Away w)) :
    Nonempty (GenericExtensionWitnessFieldFinite F G) := by
  refine ⟨↥S, Localization.Away t, hRG, ha, hgal, ?_⟩
  intro K _ _ L _ _ _ _ _ _ hKL hgalKL
  let _ : SMulCommClass G K L := ⟨fun g k x => hKL g k x⟩
  let _ : SMulCommClass G F L := ⟨fun g f x => by
    rw [← IsScalarTower.algebraMap_smul K f x, ← IsScalarTower.algebraMap_smul K f (g • x),
      hKL g (algebraMap F K f) x]⟩
  obtain ⟨b, hb, hfix⟩ := exists_chrData_of_isGaloisWithGroup hKL hgalKL
  let _ : Infinite K := infinite_of_algebra_of_infinite (F := F) (K := K)
  obtain ⟨φ, e, _he⟩ := exists_algHom_and_equivariant_algEquiv_tensorProduct_of_subalgebra
    (F := F) (G := G) (S := S) (t := t) ht htinv hle hS_fix hact_map hRG hgal hProj hS₀R
    b hb hfix
  refine ⟨φ, ?_⟩
  let _ : Algebra ↥S K := φ.toRingHom.toAlgebra
  exact ⟨e⟩

end CarrierEndToEnd

/-- **登记** ✓：**端到端的接线账**（本节与 §4.48 ✓／§4.56 ✓／§4.57 ✓ 合读）——
**已接线** ✓✅：**源侧数据**（`S` ✓／`t` ✓／`hle` ✓／`hS_{\rm fix}` ✓／`ha` ✓／`hinf` ✓）＋ **判据桥** ✓（r199 ⑤ ✓）
⟹ **有限档见证** ✓（**`hRQ`／`hRGpoint` 已消** ✓；**`hact_{\rm map}`／`hS_0R` 仍显式** ✓ —— **规范作用**下各**一行** ✓，**登记** ✓）。
**⚠ 剩余** ✗：**(i)** 两项**具名端点** ✓（`hgal`／`hProj` ✓ —— **⚠ 账目更正（第 207 轮** ✓**）**：
原写「**非本会话可落**」✗ **作废** ✓；**现账** ✓ ＝ 「源**在 `raw/` 内**（`raw/Saltman1978` 印 528 ＝ PDF 3 ✓）、
**实体未落**」✗，端点 ＝ `GaloisFiniteGenerationDescentHyp` ✓／`GaloisProgeneratorHyp` ✓，**均无证明** ✗，§166.3 ✓）；
**(ii)** **数据构造链** ✓（`S`／`t` 由 `\mathrm{IsRationalOver}` 生成 ✓ —— **§4.19--§4.26 的接线** ✗，**下一手** ✓）。
**⚠ 不声称** ✗：源 `theorem-5-1` 已证 ✗。 -/
theorem theorem51_endToEnd_wired_registered : True := trivial

/-! ## 4.61 **数据构造链 · 接线**：`(a)` 款与逐点不动**由定理导出**（第 206 轮）

**⚠ 起点** ✓（**承 §168.6 第 1 项** ✓）：§168 的下一手 ＝ **数据构造链** ✓ —— 由 `\mathrm{IsRationalOver}` ✓
**生成** `S` ✓／`t` ✓／`hle` ✓／`hS_{\rm fix}` ✓，与 §4.60 ① ✓（**载体具体化的端到端** ✓）相接 ✓。

**🔴 可达性审计（判据先审可达性** ✓**，r196 纪律** ✓**）** ✓：该链**分解为四段** ✓ ——
**①** **`t` 的构造（不变化** ✓**）** ✓ **可落** ✓（§4.23 ✓ 给非零 `t` ＋ 包含 ✓，再取 `t' := \prod_{\sigma} \sigma \bullet t` ✓
（§4.6 ✓ **不变** ✓）并用 `\mathrm{adjoin\_away\_mono}` ✓ **搬包含** ✓）—— **本轮**未落在库 ✗（**下一手** ✓）；
**②** **`(a)` 款**（`S \simeq_F \mathrm{Localization.Away}\ w` ✓）✓ **可落** ✓ —— **r188** ✓
（`exists_algEquiv_localizationAway_of_adjoin_union_inv` ✓：**代数无关** ✓ ＋ **域生成** ✓ ＋ `s_0 \neq 0` ✓ ＋ `s_0 \in F[a]` ✓）；
**③** **逐点不动** ✓ **可落** ✓ —— **§4.47** ✓（`smul_eq_self_of_mem_adjoin_of_fixed` ✓：`a` 与 `s_0` 均**不变** ✓）；
**④** **`S \to \mathrm{Localization.Away}\ t` 的代数结构** ✗（＝ **§4.35 登记的 `hRA`** ✓，**在册** ✗ ——
须由**载体步** `\mathrm{adjoin\_inv\_mem\_range\_awayToFieldAlg}` ✓ ＋ `\mathrm{awayToFieldAlg}` **单射** ✓ 造**截面** ✗）
⟹ **判据下调** ✓：「数据构造链」⟹「**②③ 接线（本轮** ✓**）＋ ①（下一手** ✓**）＋ ④（在册** ✗**）**」✓。

**🔴 本轮断指** ✓（**探针** ✓ `probe-r206a.lean` ✓ **rc=0** ✓、**零警告** ✓）：**一条**定理 ✓ ——
**载体取指定子代数** `S := \mathrm{Algebra.adjoin}\ F\ (\mathrm{range}\ a \cup \{s_0, s_0^{-1}\})` ✓ ⟹
**`(a)` 款** ✓ 与 **逐点不动** ✓ **由定理导出** ✓（**两项假设被消** ✓）。
**⚠ 相对 §4.60 ① 的**弱化** ✓**：`ha` ✓ 与 `hS_{\rm fix}` ✓ **两项假设被消掉** ✓；载体从**任意子代数** ✓ 变为
**指定的 `\mathrm{adjoin}`** ✓；**代价** ✓ ＝ 须给 `a`／`s_0` 的**源侧数据** ✓（代数无关 ✓／域生成 ✓／`s_0` 的两条 ✓／
两者的**不变性** ✓）。 -/

section NoetherAdjoinEndToEnd

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **数据构造链接线** ✓✅：**源侧数据**（`a` ✓／`s_0` ✓ 及其四条性质 ✓）＋ `t`（不变 ✓，非零 ✓）＋ **包含** ✓
＋ 实例 ✓ ＋ **两项外部输入** ✓ ⟹ **有限档见证** ✓ —— **`(a)` 款** ✓ 与 **逐点不动** ✓ **已导出** ✓（r188 ✓／§4.47 ✓）。
**⚠ 断言强度 ≤ 证据层级** ✓：**不声称**源 `theorem-5-1` 已证 ✗（假设表**仍含两项外部输入** ✓ ＋ **`hRA` 侧实例** ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin
    {n : ℕ} {a : Fin n → NoetherField F G} {s₀ : NoetherField F G}
    (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤)
    (hs₀ : s₀ ≠ 0) (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a))
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i)
    (hs₀_fix : ∀ (g : G), g • s₀ = s₀)
    {t : MvPolynomial G F} (ht : t ≠ 0) (htinv : ∀ g : G, g • t = t)
    (hle : Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
      (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G))))
    [Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t)]
    [IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t)]
    [MulSemiringAction G (Localization.Away t)]
    (hact_map : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p))
    (hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
      (x : Localization.Away t), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away t) G hRG)
    (hProj : BTier.GaloisProjectiveHyp ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away t) G hRG)
    (hS₀R : ∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
      awayToFieldAlg (F := F) (G := G) t ht
          (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t) r)
        = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r)
    (hinf : Infinite F) :
    Nonempty (GenericExtensionWitnessFieldFinite F G) :=
  nonempty_genericExtensionWitnessFieldFinite_of_subalgebra
    (F := F) (G := G) (S := Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (t := t)
    ht htinv hle (smul_eq_self_of_mem_adjoin_of_fixed ha_fix hs₀_fix)
    hact_map hRG hgal hProj hS₀R hinf
    ⟨n, exists_algEquiv_localizationAway_of_adjoin_union_inv (F := F) (K := NoetherField F G)
      hind hgen hs₀ hs₀_mem⟩

end NoetherAdjoinEndToEnd

/-- **登记** ✗：**数据构造链的余项账**（本节 ＋ §4.60 ✓／§4.48 ✓ 合读）——
**已接线** ✓✅：**`(a)` 款** ✓（r188 ✓）＋ **逐点不动** ✓（§4.47 ✓）＋ **端到端** ✓（§4.60 ① ✓）；
**余** ✗：**(i)** **`t` 的构造（不变化** ✓**）** ✓ **可落** ✓（§4.23 ✓ ＋ §4.6 ✓ ＋ `\mathrm{adjoin\_away\_mono}` ✓ —— **下一手** ✓）；
**(ii)** **`S \to \mathrm{Localization.Away}\ t` 的代数结构** ✗（＝ **§4.35 的 `hRA`** ✓，**在册** ✗）；**(iii)** **两项具名端点** ✗
（`hgal`／`hProj` ✓ —— **⚠ 账目更正（第 207 轮** ✓**）**：原写「**非本会话可落**」✗ **作废** ✓；
**现账** ✓ ＝ 「源**在 `raw/` 内** ✓、**实体未落**」✗，§166.3 ✓）。**⚠ 不声称**源 `theorem-5-1` 已证 ✗。 -/
theorem theorem51_dataChain_gap_registered : True := trivial

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
#print axioms Theorem51Statement.faithful_lock
#print axioms isRationalOver_self
#print axioms isRationalOver_discrimination_gap_registered
#print axioms inv_eq_inv_mul_of_eq_mul
#print axioms inv_eq_sq_mul_inv_of_mul_eq
#print axioms exists_mul_eq_of_isFractionRing
#print axioms exists_mem_adjoin_away_of_noether
#print axioms exists_adjoin_le_away_of_noether
#print axioms exists_adjoin_inv_le_away_of_noether
#print axioms noetherEmbedding_gap_registered
#print axioms adjoin_away_mono
#print axioms prod_smul_ne_zero
#print axioms prod_smul_invariant
#print axioms prod_pow_invariant
#print axioms prod_pow_ne_zero
#print axioms sup_adjoin_away_le
#print axioms exists_adjoin_union_le_away
#print axioms unionClearing_gap_registered
#print axioms exists_adjoin_le_away_of_image_le
#print axioms exists_image_le_away_of_finiteType
#print axioms finiteTypeImage_gap_registered
#print axioms exists_invariant_mul
#print axioms algHom_codRestrict_of_forall_mem
#print axioms awayRingHom
#print axioms awayRingHom_algebraMap
#print axioms awayMulSemiringAction
#print axioms awayLift_equivariant
#print axioms awayLift_gap_registered
#print axioms exists_algHom_of_equivariant_of_fixed_of_forall_fixed
#print axioms awayToField
#print axioms awayToField_algebraMap
#print axioms awayToField_smul
#print axioms awayToField_gap_registered
#print axioms awayToFieldAlg
#print axioms awayToField_injective
#print axioms exists_algHom_away_of_image_le
#print axioms exists_algHom_base_of_equivariant
#print axioms adjoin_inv_mem_range_awayToFieldAlg
#print axioms exists_invariant_range_awayToFieldAlg
#print axioms exists_algHom_base_of_source_data
#print axioms exists_algHom_base_of_source_data_with_image_le
#print axioms exists_surjective_realizationMap
#print axioms exists_algHom_away_of_forall_mem_range
#print axioms nonempty_algEquiv_tensorProduct_of_surjective
#print axioms nonempty_algEquiv_tensorProduct_of_finrank
#print axioms realizationMap_equivariant
#print axioms exists_equivariant_algEquiv_tensorProduct_of_galois
#print axioms exists_equivariant_algEquiv_tensorProduct_of_galoisBaseChange
#print axioms awayLift_equivariant_of_algebraMap
#print axioms exists_algHom_and_equivariant_algEquiv_tensorProduct_of_source_data
#print axioms exists_algHom_and_equivariant_algEquiv_tensorProduct_sourceOrientation
#print axioms realizationProperty_gap_registered
#print axioms infinite_of_algebra_of_infinite
#print axioms theorem51Statement_infiniteField_gap_registered
#print axioms realizationPropertyField_of_sourceData
#print axioms nonempty_genericExtensionWitness_of_clauses
#print axioms isGenericExtensionClausesField_of_sourceData
#print axioms definition11c_reading_gap_registered
#print axioms definition11c_reading_decided
#print axioms IsGenericExtensionField
#print axioms IsGenericExtensionField.shape
#print axioms realizationPropertyField_of_realizationProperty
#print axioms isGenericExtensionField_of_isGenericExtension
#print axioms GenericExtensionWitnessField
#print axioms nonempty_genericExtensionWitnessField_of_clauses
#print axioms isGenericExtensionField_of_sourceData
#print axioms nonempty_genericExtensionWitnessField_of_sourceData
#print axioms genericExtensionWitnessField_gap_registered
#print axioms smulAlgEquivHom_bijective_of_isGaloisWithGroup
#print axioms exists_normalBasis_of_isGaloisWithGroup
#print axioms exists_normalBasisElement_of_isGaloisWithGroup
#print axioms fixedPoints_eq_of_isGaloisWithGroup
#print axioms exists_chrData_of_isGaloisWithGroup
#print axioms exists_realization_of_isGaloisWithGroup
#print axioms chrBridgeField_finiteness_gap_registered
#print axioms chrBridgeField_ringTier_gap_registered
#print axioms realizationPropertyField_hdata_removal_registered
#print axioms lemma52Statement_nonzero_of_isGaloisWithGroup
#print axioms lemma52Statement_nonzero_of_isGaloisWithGroup_infF
#print axioms lemma52Statement_unit_of_isGaloisWithGroup
#print axioms lemma52_finiteness_gap_registered
#print axioms lemma52_residual_closed_registered
#print axioms RealizationPropertyFieldFinite
#print axioms RealizationPropertyFieldFinite.shape
#print axioms realizationPropertyFieldFinite_of_realizationPropertyField
#print axioms realizationPropertyFieldFinite_of_sourceData
#print axioms realizationPropertyFieldFinite_gap_registered
#print axioms IsGenericExtensionFieldFinite
#print axioms IsGenericExtensionFieldFinite.shape
#print axioms isGenericExtensionFieldFinite_of_isGenericExtensionField
#print axioms GenericExtensionWitnessFieldFinite
#print axioms nonempty_genericExtensionWitnessFieldFinite_of_clauses
#print axioms isGenericExtensionFieldFinite_of_sourceData
#print axioms nonempty_genericExtensionWitnessFieldFinite_of_sourceData
#print axioms genericExtensionWitnessFieldFinite_gap_registered
#print axioms Theorem51StatementFieldFinite
#print axioms Theorem51StatementFieldFinite.shape
#print axioms theorem51StatementFieldFinite_of_theorem51Statement
#print axioms theorem51_endToEnd_reachability_audited
#print axioms saltman1982_page_citations_audited
#print axioms nonempty_genericExtensionWitnessFieldFinite_of_subalgebra
#print axioms theorem51_endToEnd_wired_registered
#print axioms nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin
#print axioms theorem51_dataChain_gap_registered
#print axioms smul_eq_self_of_mem_adjoin_of_fixed
#print axioms exists_algHom_and_equivariant_algEquiv_tensorProduct_of_subalgebra
#print axioms exists_algEquiv_localizationAway_of_adjoin_union_inv
#print axioms noetherEval
#print axioms noetherEval_X
#print axioms exists_algHom_away_of_isUnit
#print axioms exists_basis_algHom_away_of_galois
#print axioms adjoin_range_smul_eq_top
#print axioms BTier.exists_algHom_of_equivariant_of_fixed
#print axioms BTier.fixedField_gap_registered
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
#print axioms finiteDimensional_of_basis
#print axioms conjEvalPoly
#print axioms eval_aeval_poly
#print axioms eval_conjEvalPoly
#print axioms ConjEvalPolyKStatement
#print axioms conjEvalPolyKStatement_shape
#print axioms exists_linearIndependent_smul_aeval_ne_zero
#print axioms conjEvalPoly_gap_registered
#print axioms normalBasisPoly
#print axioms eval_normalBasisPoly
#print axioms normalBasisPoly_gap_registered
#print axioms Lemma52Statement
#print axioms Lemma52Statement.shape
#print axioms Lemma52Statement.false_at_zero
#print axioms mvPolynomial_eq_zero_of_eval_eq_zero_on_range
#print axioms exists_eval_mul_ne_zero_of_range
#print axioms exists_linearIndependent_smul_aeval_ne_zero_of_conjEvalPoly_ne_zero
#print axioms smul_basis_linearCombination_eq_zero
#print axioms conjEvalPoly_ne_zero
#print axioms exists_linearIndependent_smul_aeval_ne_zero_of_ne_zero
#print axioms aeval_map_algebraMap
#print axioms exists_basis_eq_smul_of_linearIndependent
#print axioms Lemma52StatementNonzero
#print axioms lemma52Statement_nonzero_true
#print axioms adjoin_algebraMap_X_fractionRing
#print axioms exists_algebraicIndependent_of_isRationalOver
#print axioms exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver
#print axioms exists_div_eq_of_adjoin_eq_top
#print axioms exists_mul_eq_of_adjoin_eq_top
#print axioms exists_mul_eq_of_finite
#print axioms exists_mul_eq_of_finite_adjoin_eq_top
#print axioms exists_pow_mul_eq_of_finiteType
#print axioms exists_pow_mul_eq_of_finiteType_adjoin_eq_top
#print axioms mem_adjoin_inv_of_pow_mul_eq
#print axioms image_le_adjoin_inv_of_finiteType
#print axioms isAlgebraic_of_div_eq
#print axioms isAlgebraic_adjoin_of_adjoin_eq_top
#print axioms isTranscendenceBasis_of_algebraicIndependent_adjoin_eq_top
#print axioms exists_isTranscendenceBasis_of_isRationalOver
#print axioms algebraMap_mem_adjoin_inv
#print axioms finiteType_adjoin_inv
#print axioms exists_factors_through_adjoin_inv_of_finiteType
#print axioms nonempty_algEquiv_mvPolynomial_adjoin
#print axioms finiteType_adjoin_range
#print axioms exists_ringHom_away_to_field
#print axioms exists_pow_mul_eq_of_mem_adjoin_inv
#print axioms powers_le_nonZeroDivisors
#print axioms isLocalization_localizationSubalgebra
#print axioms adjoin_inv_eq_localizationSubalgebra
#print axioms isLocalization_powers_adjoin_inv
#print axioms isLocalization_away_adjoin_inv
#print axioms nonempty_algEquiv_localizationAway_adjoin_inv
#print axioms nonempty_algEquiv_localizationAway_map
#print axioms algEquiv_ne_zero_iff
#print axioms isFractionRing_of_forall_exists_div
#print axioms isFractionRing_adjoin_of_adjoin_eq_top
#print axioms exists_algEquiv_localizationAway_of_adjoin_inv

end ABGV52
