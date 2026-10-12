/-
  ABGV-5.2 · B 档 · M4 —— **Saltman 1984 §1 的「线性结构」语言**（第 115–130 轮；**新文件**）

  **来源** ✓：Saltman 1984, *Retract rational fields and cyclic Galois extensions*,
  §1 ("General nonsense")。**载体核验** ✓（L12／L16 ＋ L39 ②）：`raw/Saltman1984.pdf`
  **PDF 页 5 ＝ 印版 169** ✓（偏移 `+164` ✓ 复验 ✓），本轮 **300 dpi 读图逐字核** ✓：

  > Let \(R\) be a commutative ring and \(M\) an \(R\) module. We set \(M^{(0)} = R\) and
  > we set \(M^{(r)}\) to be the \(r\)-fold tensor product of \(M\) over \(R\). We define a
  > *linear structure* to be a tuple of the form
  > \(\mathcal{M} = \langle R, M, f_{1},\dots ,f_{r}\rangle\)
  > where \(R, M\) are as above and \(f_{i} : M^{(s_{i})} \to M^{(t_{i})}\) are \(R\) module
  > maps. We will say such an \(\mathcal{M}\) is over \(R\) and will occasionally write
  > \(\mathcal{M} / R\). The *type* of \(\mathcal{M}\) is the sequence
  > \((s_{1},t_{1}),\dots ,(s_{r},t_{r})\).

  ## 🚨 tex／印版**陈述级偏离**（本轮新发现 ✓；L16 ＋ L39 ②）

  `raw/Saltman1984.tex:92` ✓（`⚠-tex-sourced` ✗）把该句写成「\(f_{i}:M^{(i)}\to M^{(i)}\)」
  —— **两支上标皆退化为 `(i)`** ✗；**印版 169 ✓ 实为 `f_{i} : M^{(s_{i})} \to M^{(t_{i})}`** ✓。
  同段第二处同型 ✓：tex `:98` 写「\(f_{i}:M^{(s)}\to M^{(t)}\)」＋
  「\(g_{i}\circ \psi^{(s)} = \psi^{(s)}\circ f_{i}\)」✗（`s_{i}`／`t_{i}` 的下标 `i` **丢** ✓，
  等号右侧的 `t` **误成 `s`** ✗），而**印版 169 ✓ 实为**
  「\(f_{i} : M^{(s_{i})} \to M^{(t_{i})}\)」＋「\(g_{i}\circ \psi^{(s_{i})} = \psi^{(t_{i})}\circ f_{i}\)」✓
  （本轮同页读图核 ✓）。⟹ 只读 tex 会把 `f_{i}` 的**类型下标**读成 `M^{(i)} \to M^{(i)}`，
  与**同句**给出的类型序列 `(s_{i},t_{i})` **自相矛盾** ✓ —— 该矛盾在 tex 层**不可见** ✗
  （两句都被 OCR 退化到同一形状 ✓）。**本件按印版落** ✓。

  ## ✅ 回填处置（2026-10-12，**用户指令** ✓；第 118--119 轮 ✓）

  用户令「**修改 `Saltman1984.tex` 使得符合 PDF**」✓ ⟹ **tex 已按印版逐字回填** ✓。
  **第 118 轮** ✓：§1 共 **5 处** ✓（`:92` ✓／`:98` ✓／`:104` ✓／`:106` ✓／`:137` ✓），
  **全部为 OCR 丢失下标或撇号** ✓。
  **第 119 轮** ✓：① **§3 承重陈述逐句核** ✓ —— `def3.1`（印 180 ✓）／`def3.2`（印 181 ✓）／
  `lem3.3`（印 181 ✓）／`cor3.4`（印 182 ✓）／`lem3.5`（印 182 ✓）**逐字符合** ✓；
  ② 新增回填 **`:412`** ✓：`\begin{lemma}[Swan]` → `\begin{lemma}` ＋ **`\cite{27}`** ✓
  （印版该位是**引用 `[27]`** ✓，转换件把它换成了作者名标题 ✗）；③ 新增回填 **`:159`** ✓：
  `\equiv` → **`\cong`** ✓（**用户裁定** ✓；全 tex `\equiv` 共 31 处，其余皆散文「equivalent」
  或 `\not\equiv` ✓，**未动** ✓）。
  旧件存档 `raw/Saltman1984.tex.preConformance` ✓、旧 receipt 存档
  `raw/Saltman1984.receipt.preConformance.json` ✓，receipt 已再生 ✓
  （原 tex sha `27ccd530…` → 现 `7ba24311…` ✓）。

  **⚠ 上文「tex 退化形」为历史记录** ✓（＝回填**前**的状态 ✓），**不再是现状态** ✓；
  **⚠ 口径** ✓：tex 中若干处**比印版更全或更正确** ✓（印 181「`T` is of `R`」脱字 ✓、
  印 181 证明中「`S(1/s_1)`」脱下标 ✓）—— 此类**不**回填 ✓（**不把印版笔误写进 tex** ✓），逐处登记 ✓；
  **⚠ 审计范围** ✓：已**逐句核** ＝ **§1**（印 169--172 = PDF 5--8 ✓）＋ **§3 的上述五条**（印 180--182 ✓）；
  **其余页（印 183--215）未审** ✗ ⟹ 按 `∅-unchecked` 对待 ✓（**不作「已符合」的声称** ✗）。

  ## 本件内容（§77.2 施工单**第 1–3 件**（第 3 件部分 ✓））

  | 件 | 内容 | 读法 |
  |---|---|---|
  | `LinearStructure` ✓ | 源 §1 的线性结构：`R, M` ＋ `r : ℕ` ＋ `s t : Fin r → ℕ` ＋ `f : ∀ i, TensorPower R (s i) M →ₗ[R] TensorPower R (t i) M` | 逐字 ✓ |
  | `LinearStructure.type` ✓ | 源「`type` ＝ 序列 `(s₁,t₁),…,(s_r,t_r)`」 | 逐字 ✓ |
  | `tensorPower_zero_equiv` ✓ | 源「`M^{(0)} = R`」 | **同构** ✓（非定义相等 ✗，**偏离登记** ✓） |
  | 类型锁定 ✓ ＋ L1 探针 ✓ | 构造子外形锁 ✓／`type` 锁 ✓ ＋ 实例探针 ✓ | 第 1 件 ✓ |
  | `tensorPowerMapSL` ✓ ＋ `_tprod`／`_id`／`_comp` ✓ | 源「the **induced map** `M^{(r)} → N^{(r)}`」✓ 的**半线性档** ✓（mathlib **缺件** ✗ ⟹ **自建** ✓）；生成元刻画 ✓／恒等 ✓／**函子性** ✓ | 第 2 件的前置 API ✓ |
  | `Hom` ✓ ＋ `Hom.id`／`Hom.comp` ✓ ＋ **范畴律** ✓ | 源的同态 `(φ, ψ)` ✓（**按印版形** ✓：`g_i ∘ ψ^{(s_i)} = ψ^{(t_i)} ∘ f_i` ✓）＋ 源「form a category in the usual way」✓ 的**恒等** ✓／**复合** ✓／`comp_id` ✓／`id_comp` ✓／`comp_assoc` ✓ | 第 2 件 ✓ |
  | `IsIso` ✓ ＋ `toHom`／`refl`／**`symm`** ✓ | 源的同构 ✓（`S = R` ✓、`φ = id` ✓、`ψ` 可逆 ✓）＋「an invertible **morphism**」✓ 的 morphism 支 ✓／恒等档 ✓／**逆支** ✓（`IsIso.symm` ✓：逆的保持条件已证 ✓） | 第 2 件 ✓ |
  | `tensorProductRightModule` ✓ ＋ `tensorPowerBaseChange` ✓ ＋ `_tmul` ✓ | 源的**基变换** ✓：`M ⊗_φ S` ✓（印版 169 ✓）＋ `f_i ⊗ 1` ✓（印版 170 ✓「well defined」✓）—— **保源序** ✓；**缺口处置** ✓：mathlib 无次因子取向的 `S`-模结构 ✗ ⟹ 沿 `comm` **搬运** ✓（`AddEquiv.module` ＋ `AddEquiv.linearEquiv` ✓） | 第 3 件（**部分** ✓） |
  | **`tensorPowerBaseChangeEquiv`** ✓ ＋ 三件中间引理 ✓ | 源的「`(M ⊗_φ S)^{(n)}` is **identified with** `M^{(n)} ⊗_φ S`」✓（印版 170 ✓）—— `⨂[S]^n (M ⊗[R] S) ≃ₗ[S] (⨂[R]^n M) ⊗[R] S` ✓，**保源序** ✓；mathlib **无**现成件 ✗ ⟹ **自建**（逐槽 `comm` → (★) 递归 → `comm` 回序 ✓）。**⚠ 生成元语义核未过** ✗（登记 ✓） | 第 3 件（**部分** ✓） |
  | **`LinearStructure.baseChange`** ✓ ＋ **`FStruct.baseChange`** ✓ ＋ 两锁两探针 ✓ | 源的**基变换** ✓（印 169--170 ✓）：`M ⊗_φ S` 的线性结构 ✓（`f_i` 支 ＝ 源序下的 `f_i ⊗ 1` ✓，用「identified with」iso ✓ **两面夹住** ✓）＋ **`F` 结构基变换** ✓（`[IsScalarTower F R S]` ✓ 即「`φ` 是 `F`-映射」✓） | 第 3 件（**部分** ✓） |
  | **`DescentData`** ✓ ＋ **`IsFClass`** ✓ ＋ 三锁 ＋ 一探针 ✓ | 源的 **`F`-类** ✓（印版 170 ✓）—— 三条：**同构封闭** ✓／**基变换封闭** ✓／**下降＋有限生成** ✓（`DescentData` 打包 ✓：`R' ⊆ R''` ✓／`Algebra.FiniteType` ✓／`M'' ⊗_{R''} R ≅ M` ✓）；**⚠ 模的宇宙与底环同为 `u`** ✓（保基变换宇宙不变 ✓） | 第 3 件 ✓ |
  | **`LiftingData`** ✓ ＋ **`HasLiftingProperty`** ✓ ＋ 一锁一探针 ✓ | 源的**提升性质** ✓（印版 170 ✓）：局部 `F` 代数 `T` ✓／结构 over **剩余域** `T/M` ✓／存在 `\mathcal{M}'/T ∈ C` ✓／**基回同构且 `T/M`-线性** ✓（四支逐一落 ✓） | 第 4 件 ✓ |
  | **`Realization`** ✓ ＋ **`RepresentingObject`** ✓ ＋ `IsSpecialization` ✓ ＋ **`GenericObject`** ✓ ＋ 三锁两探针 ✓ | 源的**表示／一般对象／特化** ✓（印版 170 ✓）：仿射 ✓（＝有限生成 `F`-代数 ✓）／对每域 `K` 上 `\mathcal{N}/K ∈ C` 存在 `F`-映射 `\phi` ✓（`Realization` ✓）／`R ≅ F[x_1,…,x_n](1/r)` ✓ | 第 5 件（**部分** ✓） |
  | **`DenselyRepresenting`** ✓ ＋ 三锁一探针 ✓ | 源的**稠密表示对象** ✓（印版 171 ✓ **本轮逐句核** ✓）：**是表示对象** ✓ ∧ **`R` 是整环** ✓ ∧ **对任意 `0 ≠ s`，`\\mathcal{M} ⊗_R R(1/s)` 仍是表示对象** ✓ | 第 5 件 ✓ |
  | **`Hom.IsFLinear`／`IsSurjective`／`IsLocal`／`IsLocalSurjection`** ✓ ＋ **`ProjectiveObjectFor`**／**`ProjectiveObjectIn`**／**`LocalProjective`** ✓ ＋ 四锁一探针 ✓ | 源的**态射性质与投射对象** ✓（印版 171--173 ✓，**本轮逐句核** ✓）：满射（`\\phi`／`\\psi` **皆满**）✓／local（单位原像仍是单位 ✓）✓／投射对象（源明写**不**要求 `\\mathcal{P}\\in\\mathcal{C}` ✓）✓／在类中的投射 ✓／局部投射（**含 `C P`** ✓ ＋ **局部**满射 ✓） | 第 6 件 ✓ |
  | **`RepresentingObject.isSpecialization`** ✓ ＋ **`Thm13aStatement`** ✓（**具名残余** ✗）＋ 一锁 ✓ | 源的**特化收尾** ✓（印 170 ✓：表示对象 ⟹ 每域上在类中的对象是其**特化** ✓）＋ **`thm1.3(a)`** ✓（印 172 底 ✓，**只给陈述、不作证明** ✗，其识别引理未落 ✗；**(b)(c)(d) 范围外** ✗ —— 依赖 `\\mathcal{{E}}(G)`／`\\mathcal{{A}}(n)` 定义 ✓） | 第 7 件 ✓ |
  | **`RelativeLiftingProperty`** ✓ ＋ **`RetractRational`**／**`FactorsRationally`**（`def3.1`／`def3.2` ✓）＋ **`Cor310aStatement`**／**`Cor310bStatement`**（**具名残余** ✗）＋ 六锁 ✓ | 源的**相对提升** ✓（印 172 底 ✓）／**有理性收缩**与**有理分解** ✓（印 180--182 ✓）／**`cor3.10` 两支** ✓（印 186 ✓ **逐支核** ✓）—— **只给陈述、不作证明** ✗ | 第 8 件（**陈述全部落** ✓） |
  | **`HasGenericObject`**／**`HasDenselyRepresenting`**（陈述层口径 ✓）＋ **`Prop11aStatement`**／**`Prop11bStatement`**（**具名残余** ✗）＋ 四锁 ✓ | 源的 **`prop1.1`（a）（b）** ✓（印 171 ✓ **逐字核** ✓）—— (a) 有一般对象 ⟹ 有提升性质 ✓；(b) 有稠密表示 ＋ 有提升性质 ⟹ 有一般对象 ✓。**⚠ 源明写 omit the proof** ✓ | 第 9 件 ✓ |
  | `FStruct` ✓ ＋ 两把类型锁 ✓ ＋ 三个探针 ✓ | 源的 `F` 结构 ✓：「An `F` structure is a linear structure `M/R` such that **`F ⊂ R`**」✓（印版 170 ✓）—— 落为**打包**结构 ✓（`R`／`M` 及实例随 `str` 打包 ✓） | 第 3 件（**部分** ✓） |

  **施工单余项** ✗（本件**不**触碰 ✓，**不作声称** ✓）：
  ① 第 3 件的**其余部分** ✗：**`FClass`**（源四条：同类型 ✓／**同构封闭** ✓／**基变换封闭** ✓／
  **下降／有限生成** ✓）**未落** ✗。**⚠ 缺口已处置** ✓（§8 ✓）：次因子取向的 `S`-模结构**已**沿 `comm`
  搬运 ✓（`AddEquiv.module` ＋ `AddEquiv.linearEquiv` ✓），源的 `f_i ⊗ 1` **已落** ✓（**保源序** ✓）。
  **⚠ 上述 iso 与基变换已落** ✓（§8.1／§8.2／§8.3 ✓）—— **`LinearStructure.baseChange`** ✓ ＋
  **`FStruct.baseChange`** ✓ 均已编译 ✓（§8.2／§8.3 ✓）；
  **⚠ 该 iso 的生成元语义核未过** ✗（卡点逐字见 §8.1 ✓）⟹ **`baseChange` 一族一并按 `∅-unchecked`** ✓ 对待；
  **✅ 第 3 件已完整落** ✓（`FStruct` ✓＋基变换三件套 ✓＋`baseChange` ✓＋`FClass` ✓）；
  **⚠ 但两条登记在案** ✗：**(a)** §8.1 的 iso **生成元语义核未过** ✗ ⟹ `baseChange` 一族按 `∅-unchecked` ✓；
  **(b)** `IsFClass` **只证了定义外形可满足** ✓（空类 ✓），**未证**任何**非空** `F`-类满足它 ✓
  （源以 `\cite{18}`／`\cite{7}`／`\cite{22}` 作据 ✓，本件未涉 ✗）；
  ② **第 4 件已落** ✓（`LiftingData` ✓ ＋ `HasLiftingProperty` ✓）；**第 5 件已落** ✓✅
  （`Realization` ✓／`RepresentingObject` ✓／`IsSpecialization` ✓／`GenericObject` ✓／
  **`DenselyRepresenting`** ✓ —— 其定义在**印版 171** ✓（**非 172** ✗，上轮登记已更正 ✓），**本轮已逐句核** ✓）；
  ③ **第 6／7／8 件已落** ✓（第 8 件的**陈述**全部落 ✓）；**第 9 件已落** ✓
  （`HasGenericObject` ✓／`HasDenselyRepresenting` ✓／`Prop11aStatement` ✓／`Prop11bStatement` ✓ ＋ 四锁 ✓）
  —— **⚠ 第 8／9 件全部为具名残余：只给陈述、不作证明** ✗
  ⟹ **M4 施工单（§77.2 第 1–9 件）的**陈述层**到此全部落** ✓✅；
  **余项** ✗：**(i)** 六件具名残余的**证明**（`Thm13aStatement` ✓／`Cor310aStatement` ✓／
  `Cor310bStatement` ✓／`Cor310Reduction` ✓／`Prop11aStatement` ✓／`Prop11bStatement` ✓ —— 其桥是印 181--182 的
  `lem3.3`／`cor3.4`／`lem3.5` ✓ ＋ 印 172 底的 **Hom-集识别** ✓）；
  **(ii)** `thm1.3`(b)(c)(d) **范围外** ✗（须 `\mathcal{E}(G)`／`\mathcal{A}(n)` ✓）；
  **(iii)** §8.1 的 iso **生成元语义核** ✗。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Subalgebra.Basic

open TensorProduct
open scoped TensorProduct

universe u v

namespace ABGV52

/-! ## 1. 源 §1：线性结构（印版 169 ✓） -/

/-- **源 §1 的线性结构** ✓（印版 169 ✓；§77.2 施工单**第 1 件** ✓）：元组
`⟨R, M, f₁, …, f_r⟩`，其中 `M^{(n)}` ＝ `M` 的 `n` 重张量幂（`TensorPower R n M` ✓）、
`f_i : M^{(s_i)} → M^{(t_i)}` 是 `R`-线性映射 ✓（源 `R` module maps ✓）。

**形式化约定** ✓（逐字对应，无收紧 ✓）：源的 `⟨R, M, f₁, …, f_r⟩` 之 `R, M` 落为**参数** ✓；
`f` 的**指标族**落为 `Fin r → ⋯` ✓；`s t : Fin r → ℕ` 即源的**类型序列**
`(s₁,t₁),…,(s_r,t_r)` ✓（见 `LinearStructure.type` ✓）。 -/
structure LinearStructure (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] (r : ℕ) (s t : Fin r → ℕ) where
  /-- 源逐字：`f_i : M^{(s_i)} → M^{(t_i)}` 是 `R` module maps ✓（印版 169 ✓）。 -/
  f : ∀ i : Fin r, TensorPower R (s i) M →ₗ[R] TensorPower R (t i) M

/-- **源 §1 的 `type`** ✓（印版 169 ✓：「The *type* of `M` is the sequence
`(s₁,t₁),…,(s_r,t_r)`」✓）：线性结构的类型 ＝ 其 `f` 的**类型序列** ✓。 -/
def LinearStructure.type {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {r : ℕ} {s t : Fin r → ℕ} (_M : LinearStructure R M r s t) :
    Fin r → ℕ × ℕ :=
  fun i => (s i, t i)

/-! ## 2. 源「`M^{(0)} = R`」（印版 169 ✓） -/

/-- **源「`M^{(0)} = R`」的库内形式** ✓（印版 169 ✓）：`M` 的 `0` 重张量幂**同构**于 `R` ✓。

**⚠ 偏离登记** ✓（L16／L39 ②）：mathlib 的 `TensorPower R 0 M` ＝ **空族张量积**
`⨂[R] (_ : Fin 0), M` ✓，与 `R` **同构** ✓ 而**非**定义相等 ✗ ⟹ 源的「`M^{(0)} = R`」
在本库按**同构**读 ✓（`PiTensorProduct.isEmptyEquiv` ✓）。

**用途** ✓：源允许 `s_i = 0`（此时 `f_i` 的源是 `M^{(0)}` ＝ `R` ✓）；该支的载体
即此同构像 ✓。**⚠ 作用域** ✓：本件**不**搬运任何 `f_i`（第 1 件无 `f` 的定义域约束 ✓），
只登记源把 `M^{(0)}` 认作 `R` 的**库内桥** ✓。 -/
def tensorPower_zero_equiv (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] : TensorPower R 0 M ≃ₗ[R] R :=
  PiTensorProduct.isEmptyEquiv (R := R) (s := fun _ : Fin 0 => M)

/-! ## 3. 类型锁定（阶段 5.5 第 5 条变体 ✓）与 L1 探针 ✓ -/

/-- **定义外形锁定** ✓（构造子档）：`LinearStructure` 的**构造子签名**一旦被改动
（参数次序、`s t` 的位置或 `f` 的字段类型），本 `rfl` 立即编译失败 ✓ ——
即 §77.2 表内逐字给出的签名被**钉死** ✓。 -/
theorem LinearStructure_typeLock (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] (r : ℕ) (s t : Fin r → ℕ)
    (f : ∀ i : Fin r, TensorPower R (s i) M →ₗ[R] TensorPower R (t i) M) :
    (LinearStructure.mk f : LinearStructure R M r s t).f = f :=
  rfl

/-- **`type` 的逐字形状锁** ✓：源「`type` ＝ `(s₁,t₁),…,(s_r,t_r)`」一旦被改动
（如换成 `(t_i,s_i)` 或丢一列 ✓），本 `rfl` 立即编译失败 ✓。 -/
theorem LinearStructure_type_typeLock (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] (r : ℕ) (s t : Fin r → ℕ)
    (f : ∀ i : Fin r, TensorPower R (s i) M →ₗ[R] TensorPower R (t i) M) :
    (LinearStructure.mk f : LinearStructure R M r s t).type = fun i => (s i, t i) :=
  rfl

/-- **L1 探针** ✓（**非空洞** ✓）：源 §1 所举三类例子（`R` 代数 ✓／`G`-Galois 扩张 ✓／
带多重线性型的 `R` 模 ✓）的**最简实体** ✓ —— 取 `r = 1`、`s 0 = t 0 = 1` ✓、
`f 0 = id` ✓（`M^{(1)} → M^{(1)}` 的恒等 ✓）⟹ 结构在 `r ≥ 1` 上**可实例化** ✓。 -/
def linearStructureProbe (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] : LinearStructure R M 1 (fun _ => 1) (fun _ => 1) where
  f _ := LinearMap.id

/-- **L1 探针（`r = 0` 档）** ✓：`f` 族**空**时结构仍合法 ✓（源未排除 `r = 0` ✓）
—— 与上条的 `r = 1` 档合读 ⟹ 参数域 `(r, s, t)` 在两端**皆非空** ✓。 -/
def linearStructureProbeZero (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] : LinearStructure R M 0 (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → ℕ) where
  f := fun i => Fin.elim0 i

/-- **参数域非空（合并读数）** ✓（L1 ✓）：`r = 0` 与 `r = 1` 两档**同时**可实例化 ✓。 -/
theorem linearStructureProbe_nonempty (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] :
    (Nonempty (LinearStructure R M 0 (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → ℕ)) ∧
      Nonempty (LinearStructure R M 1 (fun _ => 1) (fun _ => 1))) :=
  ⟨⟨linearStructureProbeZero R M⟩, ⟨linearStructureProbe R M⟩⟩

/-! ## 4. 源 §1 的「诱导映射」`ψ^{(n)}`（**半线性档** ✓；§78.6 登记的前置 API ✓） -/

section TensorPowerMap

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]
variable {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- **`σ`-半线性映射诱导的张量幂映射** ✓：源 §1（印版 169 ✓）的「Define `ψ^{(0)}` to be `φ`,
and `ψ^{(r)}` to be the **induced map** `M^{(r)} → N^{(r)}`」✓ —— 把 `ψ : M →ₛₗ[σ] N` 提升为
`ψ^{(n)} : M^{(n)} →ₛₗ[σ] N^{(n)}` ✓，在生成元上的值见 `tensorPowerMapSL_tprod` ✓。

**⚠ 库内缺口登记** ✓（§78.6 的侦察结论 ✓）：mathlib **无**半线性档的张量幂映射 ✗ ——
`PiTensorProduct.map` 只收 **`R`-线性**族 ✓；`MultilinearMap.restrictScalars` 要求**定义域**
亦为 `A`-模 ✗（本处 `M` 只是 `R`-模 ✓）⟹ **不适用** ✓。故本件**自建** ✓ 并登记 ✗。

**构造** ✓：`(aᵢ)ᵢ ↦ ⨂ᵢ ψ(aᵢ)` 是 `R`-**多重线性**的 ✓ —— 目标 `N^{(n)}` 经
`Module.compHom _ σ` ✓ 读作 `R`-模 ✓（其中 `c • y` 与该 `S`-模的 `σ c • y` **定义相等** ✓，
这是本构造的关键 ✓）；加性支由 `ψ` 加性 ✓、`R`-标量支由 `ψ (c • x) = σ c • ψ x` ✓ 与
`tprod` 的 `S`-多重线性 ✓ 合成 ✓；再经 `PiTensorProduct.lift` ✓ 得 `R`-线性映射 ✓，
其 `S`-半线性性由定义处的 `map_smul'` 直接给出 ✓。 -/
noncomputable def tensorPowerMapSL (σ : R →+* S) (ψ : M →ₛₗ[σ] N) (n : ℕ) :
    TensorPower R n M →ₛₗ[σ] TensorPower S n N :=
  letI : Module R (TensorPower S n N) := Module.compHom (TensorPower S n N) σ
  let L : TensorPower R n M →ₗ[R] TensorPower S n N :=
    PiTensorProduct.lift
      { toFun := fun m => PiTensorProduct.tprod S (fun i => ψ (m i))
        map_update_add' := by
          intro _ m i x y
          have h : ∀ j z, ψ (Function.update m i z j) =
              Function.update (fun k => ψ (m k)) i (ψ z) j :=
            fun j z => Function.apply_update (fun k => ψ) m i z j
          simp only [h, map_add]
          exact (PiTensorProduct.tprod S).map_update_add _ i _ _
        map_update_smul' := by
          intro _ m i c x
          have h : ∀ j z, ψ (Function.update m i z j) =
              Function.update (fun k => ψ (m k)) i (ψ z) j :=
            fun j z => Function.apply_update (fun k => ψ) m i z j
          simp only [h, map_smulₛₗ]
          exact (PiTensorProduct.tprod S).map_update_smul _ i (σ c) _ }
  { toFun := L
    map_add' := L.map_add
    map_smul' := fun c x => L.map_smul c x }

set_option linter.style.haveILetI false in
/-- **生成元刻画** ✓：`ψ^{(n)} (⨂ᵢ aᵢ) = ⨂ᵢ ψ(aᵢ)` ✓ —— 即源「induced map」的**读法** ✓。
**⚠ 用途** ✓：`Hom` 的恒等档 ✓ 的唯一计算入口 ✓。 -/
theorem tensorPowerMapSL_tprod (σ : R →+* S) (ψ : M →ₛₗ[σ] N) (n : ℕ)
    (m : Fin n → M) :
    tensorPowerMapSL σ ψ n (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod S (fun i => ψ (m i)) := by
  letI : Module R (TensorPower S n N) := Module.compHom (TensorPower S n N) σ
  rw [tensorPowerMapSL]
  exact PiTensorProduct.lift.tprod _

/-- **恒等档** ✓（源「form a category in the usual way」✓ 的恒等支 ✓）：
`σ = RingHom.id R`、`ψ = id` 时 `ψ^{(n)} = id` ✓。 -/
theorem tensorPowerMapSL_id (n : ℕ) :
    tensorPowerMapSL (RingHom.id R) (LinearMap.id : M →ₗ[R] M) n = LinearMap.id := by
  apply PiTensorProduct.ext
  ext f
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    tensorPowerMapSL_tprod]
  rfl

set_option linter.style.haveILetI false in
/-- **复合档** ✓（源「form a category in the usual way」✓ 的复合支 ✓）：
`(ψ₂ ∘ ψ₁)^{(n)} = ψ₂^{(n)} ∘ ψ₁^{(n)}` ✓ —— 即 `n ↦ ψ^{(n)}` 对复合**函子性** ✓。
**⚠ 用途** ✓：`Hom` 的复合 ✓ 与 `IsIso` 的逆 ✓ 的唯一计算入口 ✓。

**⚠ 口径** ✓：`σ₁₃` 显式给出 ✓ 并附 `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃` ✓ —— mathlib 只为
**恒等档**（`ids`／`right_ids` ✓）注册该类型类 ✓，一般 `σ₁₃` 由**调用方供给** ✓。 -/
theorem tensorPowerMapSL_comp {T : Type u} [CommRing T] {P : Type v} [AddCommGroup P]
    [Module T P] (σ₁₂ : R →+* S) (σ₂₃ : S →+* T) (σ₁₃ : R →+* T)
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (ψ₁ : M →ₛₗ[σ₁₂] N) (ψ₂ : N →ₛₗ[σ₂₃] P) (n : ℕ) :
    tensorPowerMapSL σ₁₃ (ψ₂.comp ψ₁) n =
      (tensorPowerMapSL σ₂₃ ψ₂ n).comp (tensorPowerMapSL σ₁₂ ψ₁ n) := by
  apply LinearMap.ext
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smulₛₗ, tensorPowerMapSL_tprod, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorPowerMap

/-! ## 5. 源 §1：线性结构的**同态**（印版 169 ✓） -/

section HomStructure

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]
variable {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
variable {r : ℕ} {s t : Fin r → ℕ}

/-- **源 §1 的同态** ✓（印版 169 ✓；**按印版形** ✓ —— tex `:98` 已于第 118 轮按印版回填 ✓，见头注 ✓）：
`M/R` 与 `N/S` **类型相同** ✓ 时的同态 `Ψ : M → N` ＝ 一对 `(φ, ψ)` ✓，其中
`φ : R → S` 是**环同态** ✓、`ψ : M → N` 是 **`φ`-半线性** ✓、且
**保持**两边的 `f_i`／`g_i` ✓：`g_i ∘ ψ^{(s_i)} = ψ^{(t_i)} ∘ f_i` ✓
（`ψ^{(n)}` ＝ `tensorPowerMapSL φ ψ n` ✓）。

**⚠ 类型参数** ✓：源的「same type」落为**两个结构共享同一组** `r, s, t` ✓
（`M₁ : LinearStructure R M r s t` 与 `N₁ : LinearStructure S N r s t` ✓）。 -/
structure Hom (M₁ : LinearStructure R M r s t) (N₁ : LinearStructure S N r s t) where
  /-- 源逐字：`φ : R → S` is a ring homomorphism ✓。 -/
  phi : R →+* S
  /-- 源逐字：`ψ : M → N` is a `φ`-semilinear ✓。 -/
  psi : M →ₛₗ[phi] N
  /-- 源逐字：`g_i ∘ ψ^{(s_i)} = ψ^{(t_i)} ∘ f_i` ✓（**印版形** ✓）。 -/
  comm : ∀ i : Fin r,
    (N₁.f i).comp (tensorPowerMapSL phi psi (s i)) =
      (tensorPowerMapSL phi psi (t i)).comp (M₁.f i)

/-- **`Hom` 的定义外形锁定** ✓（构造子档）：`phi`／`psi`／`comm` 的**类型与次序**一旦漂移
（如把 `ψ` 写成 `R`-线性而非 `φ`-半线性 ✗、或把保持条件的方向写反 ✗），本两条 `rfl`
立即编译失败 ✓。 -/
theorem Hom_typeLock (M₁ : LinearStructure R M r s t) (N₁ : LinearStructure S N r s t)
    (φ : R →+* S) (ψ : M →ₛₗ[φ] N)
    (h : ∀ i : Fin r, (N₁.f i).comp (tensorPowerMapSL φ ψ (s i)) =
      (tensorPowerMapSL φ ψ (t i)).comp (M₁.f i)) :
    (Hom.mk φ ψ h : Hom M₁ N₁).phi = φ :=
  rfl

theorem Hom_typeLock_psi (M₁ : LinearStructure R M r s t) (N₁ : LinearStructure S N r s t)
    (φ : R →+* S) (ψ : M →ₛₗ[φ] N)
    (h : ∀ i : Fin r, (N₁.f i).comp (tensorPowerMapSL φ ψ (s i)) =
      (tensorPowerMapSL φ ψ (t i)).comp (M₁.f i)) :
    (Hom.mk φ ψ h : Hom M₁ N₁).psi = ψ :=
  rfl

/-- **恒等同态** ✓（源「the class of all linear structures of a fixed type form a category
in the usual way」✓ 的恒等 ✓）：取 `S := R`、`φ := RingHom.id R`、`ψ := id` ✓；
保持条件由 `tensorPowerMapSL_id` ✓ 化归为 `id` 的两侧消去 ✓。 -/
def Hom.id (M₁ : LinearStructure R M r s t) : Hom M₁ M₁ where
  phi := RingHom.id R
  psi := LinearMap.id
  comm := by
    intro i
    rw [tensorPowerMapSL_id, tensorPowerMapSL_id]
    simp

/-- **L1 探针** ✓（**非空洞** ✓）：`Hom` 在**任意** `(r, s, t)` 上可实例化 ✓（`Hom.id` ✓）。 -/
theorem Hom_nonempty (M₁ : LinearStructure R M r s t) : Nonempty (Hom M₁ M₁) :=
  ⟨Hom.id M₁⟩

/-- **L1 探针（一般 `φ` 档 ✓）**：`r = 0` 时保持条件**空** ✓ ⟹ 对**任意**环同态
`φ : R →+* S` 与任意 **`φ`-半线性** `ψ` 都有同态 ✓ ⟹ 源的**半线性支**（`R ≠ S` ✓、
`φ ≠ id` ✓）**非空洞** ✓。 -/
def Hom_probeGeneral (φ : R →+* S) (ψ : M →ₛₗ[φ] N) :
    Hom (linearStructureProbeZero R M) (linearStructureProbeZero S N) where
  phi := φ
  psi := ψ
  comm := fun i => Fin.elim0 i

/-- **复合** ✓（源「form a category in the usual way」✓ 的复合支 ✓）：
`(Φ : N → P) ∘ (Ψ : M → N)` 的 `φ`／`ψ` 逐支复合 ✓，保持条件由 `tensorPowerMapSL_comp` ✓
（函子性 ✓）与两侧的 `comm` ✓ 沿结合律拼接 ✓。 -/
def Hom.comp {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure S N r s t}
    {T : Type u} [CommRing T] {P : Type v} [AddCommGroup P] [Module T P]
    {P₁ : LinearStructure T P r s t} (Ψ : Hom M₁ N₁) (Φ : Hom N₁ P₁) : Hom M₁ P₁ :=
  letI : RingHomCompTriple Ψ.phi Φ.phi (Φ.phi.comp Ψ.phi) := ⟨rfl⟩
  { phi := Φ.phi.comp Ψ.phi
    psi := Φ.psi.comp Ψ.psi
    comm := by
      intro i
      calc (P₁.f i).comp (tensorPowerMapSL (Φ.phi.comp Ψ.phi) (Φ.psi.comp Ψ.psi) (s i))
          = (P₁.f i).comp ((tensorPowerMapSL Φ.phi Φ.psi (s i)).comp
              (tensorPowerMapSL Ψ.phi Ψ.psi (s i))) := by
            rw [tensorPowerMapSL_comp]
        _ = ((P₁.f i).comp (tensorPowerMapSL Φ.phi Φ.psi (s i))).comp
              (tensorPowerMapSL Ψ.phi Ψ.psi (s i)) := by
            rw [← LinearMap.comp_assoc]
        _ = ((tensorPowerMapSL Φ.phi Φ.psi (t i)).comp (N₁.f i)).comp
              (tensorPowerMapSL Ψ.phi Ψ.psi (s i)) := by
            rw [Φ.comm i]
        _ = (tensorPowerMapSL Φ.phi Φ.psi (t i)).comp
              ((N₁.f i).comp (tensorPowerMapSL Ψ.phi Ψ.psi (s i))) := by
            rw [LinearMap.comp_assoc]
        _ = (tensorPowerMapSL Φ.phi Φ.psi (t i)).comp
              ((tensorPowerMapSL Ψ.phi Ψ.psi (t i)).comp (M₁.f i)) := by
            rw [Ψ.comm i]
        _ = ((tensorPowerMapSL Φ.phi Φ.psi (t i)).comp
              (tensorPowerMapSL Ψ.phi Ψ.psi (t i))).comp (M₁.f i) := by
            rw [← LinearMap.comp_assoc]
        _ = (tensorPowerMapSL (Φ.phi.comp Ψ.phi) (Φ.psi.comp Ψ.psi) (t i)).comp
              (M₁.f i) := by
            rw [tensorPowerMapSL_comp] }

/-- **范畴律：右单位** ✓（源「form a category in the usual way」✓ 的**单位律**支 ✓）：
`Ψ ∘ id = Ψ` ✓。 -/
theorem Hom.comp_id {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure S N r s t}
    (Ψ : Hom M₁ N₁) : Ψ.comp (Hom.id N₁) = Ψ :=
  rfl

/-- **范畴律：左单位** ✓：`id ∘ Ψ = Ψ` ✓。 -/
theorem Hom.id_comp {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure S N r s t}
    (Ψ : Hom M₁ N₁) : (Hom.id M₁).comp Ψ = Ψ :=
  rfl

/-- **范畴律：结合律** ✓：`(Ξ ∘ Ψ) ∘ Φ = Ξ ∘ (Ψ ∘ Φ)` ✓
（`RingHom` 与 `LinearMap` 的复合均按 `fun x => f (g x)` 展开 ✓ ⟹ `rfl` 可判 ✓）。 -/
theorem Hom.comp_assoc {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure S N r s t}
    {T : Type u} [CommRing T] {P : Type v} [AddCommGroup P] [Module T P]
    {P₁ : LinearStructure T P r s t}
    {U : Type u} [CommRing U] {Q : Type v} [AddCommGroup Q] [Module U Q]
    {Q₁ : LinearStructure U Q r s t}
    (Ξ : Hom M₁ N₁) (Ψ : Hom N₁ P₁) (Φ : Hom P₁ Q₁) :
    (Ξ.comp Ψ).comp Φ = Ξ.comp (Ψ.comp Φ) :=
  rfl

end HomStructure

/-! ## 6. 源 §1：线性结构的**同构**（印版 169 ✓） -/

section IsIsoStructure

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {r : ℕ} {s t : Fin r → ℕ}

/-- **源 §1 的同构** ✓（印版 169 ✓ 逐字）：「An **isomorphism** `(φ,ψ) : M/R → N/S` will be an
invertible morphism which is `R` linear. That is, we insist that **`S = R`** ✓, that **`φ` is the
identity** ✓, and that **`ψ^{-1} : N → M` exists** ✓」—— 三条落为：两端**同一**底环 `R` ✓、
`ψ` 是 `R`-**线性等价** ✓（可逆 ✓ ＋ `R`-线性 ✓）、且保持 `f_i`／`g_i` ✓（此时
`ψ^{(n)}` 由 `tensorPowerMapSL (RingHom.id R)` ✓ 给出 ✓）。 -/
structure IsIso (M₁ : LinearStructure R M r s t) (N₁ : LinearStructure R N r s t) where
  /-- 源：`S = R` ✓、`φ = id` ✓、`ψ^{-1}` 存在 ✓ ⟹ `ψ` 是 `R`-线性等价 ✓。 -/
  psi : M ≃ₗ[R] N
  /-- 源：保持 `f_i`／`g_i` ✓（`φ = id` ✓）。 -/
  comm : ∀ i : Fin r,
    (N₁.f i).comp (tensorPowerMapSL (RingHom.id R) (psi : M →ₗ[R] N) (s i)) =
      (tensorPowerMapSL (RingHom.id R) (psi : M →ₗ[R] N) (t i)).comp (M₁.f i)

/-- **同构 → 同态** ✓：源「an invertible **morphism**」✓ 的 morphism 支 ✓
（`φ := RingHom.id R` ✓、`ψ` 取 `psi` 的线性支 ✓）。 -/
def IsIso.toHom {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure R N r s t}
    (e : IsIso M₁ N₁) : Hom M₁ N₁ where
  phi := RingHom.id R
  psi := (e.psi : M →ₗ[R] N)
  comm := e.comm

/-- **恒等同构** ✓（源「`ψ^{-1}` exists」✓ 的退化档：`ψ := id` ✓、`ψ^{-1} = id` ✓）。 -/
def IsIso.refl (M₁ : LinearStructure R M r s t) : IsIso M₁ M₁ where
  psi := LinearEquiv.refl R M
  comm := by
    intro i
    change (M₁.f i).comp
        (tensorPowerMapSL (RingHom.id R) (LinearMap.id : M →ₗ[R] M) (s i)) =
      (tensorPowerMapSL (RingHom.id R) (LinearMap.id : M →ₗ[R] M) (t i)).comp (M₁.f i)
    rw [tensorPowerMapSL_id, tensorPowerMapSL_id]
    simp

/-- **`IsIso` 的定义外形锁定** ✓：`psi` 的**类型**（`R`-线性等价 ✓，而非仅线性映射 ✗、
亦非跨底环 ✗）一旦漂移，本 `rfl` 立即编译失败 ✓。 -/
theorem IsIso_typeLock (M₁ : LinearStructure R M r s t) (N₁ : LinearStructure R N r s t)
    (ψ : M ≃ₗ[R] N)
    (h : ∀ i : Fin r,
      (N₁.f i).comp (tensorPowerMapSL (RingHom.id R) (ψ : M →ₗ[R] N) (s i)) =
        (tensorPowerMapSL (RingHom.id R) (ψ : M →ₗ[R] N) (t i)).comp (M₁.f i)) :
    ((IsIso.mk ψ h : IsIso M₁ N₁).psi : M →ₗ[R] N) = (ψ : M →ₗ[R] N) :=
  rfl

/-- **L1 探针** ✓（**非空洞** ✓）：`IsIso` 在**任意** `(r, s, t)` 上可实例化 ✓（`refl` ✓）。 -/
theorem IsIso_nonempty (M₁ : LinearStructure R M r s t) : Nonempty (IsIso M₁ M₁) :=
  ⟨IsIso.refl M₁⟩

/-- **`ψ^{(n)}` 的左逆档** ✓：`(ψ^{-1})^{(n)} ∘ ψ^{(n)} = id` ✓ —— 由
`tensorPowerMapSL_comp` ✓（函子性 ✓）与 `tensorPowerMapSL_id` ✓（恒等档 ✓）给出 ✓。
**⚠ 用途** ✓：`IsIso.symm` ✓ 的消去子 ✓。 -/
theorem tensorPowerMapSL_symm_comp (φ : M ≃ₗ[R] N) (n : ℕ) :
    (tensorPowerMapSL (RingHom.id R) (φ.symm : N →ₗ[R] M) n).comp
      (tensorPowerMapSL (RingHom.id R) (φ : M →ₗ[R] N) n) = LinearMap.id := by
  rw [← tensorPowerMapSL_comp (RingHom.id R) (RingHom.id R) (RingHom.id R)
    (φ : M →ₗ[R] N) (φ.symm : N →ₗ[R] M) n]
  have h : (φ.symm : N →ₗ[R] M).comp (φ : M →ₗ[R] N) = LinearMap.id := by
    ext x
    simp
  rw [h, tensorPowerMapSL_id]

/-- **`ψ^{(n)}` 的右逆档** ✓：`ψ^{(n)} ∘ (ψ^{-1})^{(n)} = id` ✓。 -/
theorem tensorPowerMapSL_comp_symm (φ : M ≃ₗ[R] N) (n : ℕ) :
    (tensorPowerMapSL (RingHom.id R) (φ : M →ₗ[R] N) n).comp
      (tensorPowerMapSL (RingHom.id R) (φ.symm : N →ₗ[R] M) n) = LinearMap.id := by
  rw [← tensorPowerMapSL_comp (RingHom.id R) (RingHom.id R) (RingHom.id R)
    (φ.symm : N →ₗ[R] M) (φ : M →ₗ[R] N) n]
  have h : (φ : M →ₗ[R] N).comp (φ.symm : N →ₗ[R] M) = LinearMap.id := by
    ext x
    simp
  rw [h, tensorPowerMapSL_id]

/-- **逆** ✓（源「an invertible morphism which is `R` linear」✓ 的**逆支** ✓）：
「**逆仍是同构**」✓ —— 即逆 `ψ^{-1}` 也满足保持条件 ✓。
**证法** ✓（**逐点** ✓，绕开结合律改写的不定向性 ✓）：设 `A, B` 为两侧的 `f_i`／`g_i` ✓、
`P := ψ^{(s_i)}` ✓、`Q := ψ^{(t_i)}` ✓、`P' := (ψ^{-1})^{(s_i)}` ✓、`Q' := (ψ^{-1})^{(t_i)}` ✓；
由 `P ∘ P' = id` ✓、`Q' ∘ Q = id` ✓（两条逆档 ✓）与 `B ∘ P = Q ∘ A` ✓（`e.comm i` ✓）得
`Q' (B y) = Q' (B (P (P' y))) = Q' (Q (A (P' y))) = A (P' y)` ✓。 -/
def IsIso.symm {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure R N r s t}
    (e : IsIso M₁ N₁) : IsIso N₁ M₁ where
  psi := e.psi.symm
  comm := by
    intro i
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply]
    have h1 : tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (s i)
        (tensorPowerMapSL (RingHom.id R) (e.psi.symm : N →ₗ[R] M) (s i) y) = y := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (tensorPowerMapSL_comp_symm e.psi (s i)) y
    have h2 : ∀ x, tensorPowerMapSL (RingHom.id R) (e.psi.symm : N →ₗ[R] M) (t i)
        (tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (t i) x) = x := by
      intro x
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (tensorPowerMapSL_symm_comp e.psi (t i)) x
    have hc : ∀ z, N₁.f i (tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (s i) z) =
        tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (t i) (M₁.f i z) :=
      fun z => LinearMap.congr_fun (e.comm i) z
    have key1 : N₁.f i y = N₁.f i (tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (s i)
        (tensorPowerMapSL (RingHom.id R) (e.psi.symm : N →ₗ[R] M) (s i) y)) := by rw [h1]
    have key2 : N₁.f i (tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (s i)
        (tensorPowerMapSL (RingHom.id R) (e.psi.symm : N →ₗ[R] M) (s i) y)) =
        tensorPowerMapSL (RingHom.id R) (e.psi : M →ₗ[R] N) (t i)
          (M₁.f i (tensorPowerMapSL (RingHom.id R) (e.psi.symm : N →ₗ[R] M) (s i) y)) :=
      hc _
    rw [key1, key2, h2]

/-- **L1 探针（逆支）** ✓：`IsIso` 的**逆**存在 ✓（每组同构给出一组反向同构 ✓）。 -/
theorem IsIso_symm_nonempty {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure R N r s t}
    (e : IsIso M₁ N₁) : Nonempty (IsIso N₁ M₁) :=
  ⟨e.symm⟩

end IsIsoStructure

/-! ## 7. 源 §1：`F` 结构（印版 170 ✓） -/

section FStruct

variable (F : Type u) [Field F]

/-- **源 §1 的 `F` 结构** ✓（印版 170 ✓ 逐字：「An `F` structure is a linear structure `M/R` such that
`F ⊂ R`」✓）：固定类型 `(r, s, t)` 的、底环含 `F` 的线性结构 ✓。

**⚠ 形式化约定** ✓：「`F ⊂ R`」落为 **`[Algebra F R]`** ✓ —— 对**非零** `R`，`algebraMap F R` 自动**单** ✓
（域无非平凡理想 ✓、`1 ≠ 0` ✓）⟹ 与「`F` 是 `R` 的子环」**同义** ✓；源的 `F ⊂ R` **本身**排除 `R = 0` ✓
（**加性收紧，非放宽** ✓，登记 ✓）。

**⚠ 打包口径** ✓：本件把源「class of `F` structures」的元素落在**打包结构**上 ✓（`R`／`M` 及其实例
随 `str` 一起打包 ✓）—— 理由 ✓：类的后续四条封闭性（**同构** ✓／**基变换** ✓／**下降** ✓）
**都会改变底环** ✓，未打包形（`C : ∀ R [CommRing R] …, Prop`）会让每次搬运都重新装配类型类 ✓。 -/
structure FStruct (r : ℕ) (s t : Fin r → ℕ) where
  /-- 底环 ✓（源的 `R` ✓；「`F ⊂ R`」由 `algebra` 支承载 ✓）。 -/
  R : Type u
  [commRing : CommRing R]
  [algebra : Algebra F R]
  /-- 承载模 ✓（源的 `M` ✓）。 -/
  M : Type v
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  /-- 线性结构本体 ✓（源 §1 的 `⟨R, M, f₁, …, f_r⟩` ✓）。 -/
  str : LinearStructure R M r s t

attribute [instance] FStruct.commRing FStruct.algebra FStruct.addCommGroup FStruct.module

/-- **定义外形锁定** ✓（构造子档）：`FStruct` 的字段与次序一旦漂移（如把实例支拆出打包 ✗、
或把 `str` 提到 `R`／`M` 之前 ✗），本两条 `rfl` 立即编译失败 ✓。 -/
theorem FStruct_typeLock (R : Type u) [CommRing R] [Algebra F R] (M : Type v)
    [AddCommGroup M] [Module R M] (str : LinearStructure R M r s t) :
    (FStruct.mk (F := F) R M str : FStruct F r s t).R = R :=
  rfl

theorem FStruct_typeLock_str (R : Type u) [CommRing R] [Algebra F R] (M : Type v)
    [AddCommGroup M] [Module R M] (str : LinearStructure R M r s t) :
    (FStruct.mk (F := F) R M str : FStruct F r s t).str = str :=
  rfl

/-- **L1 探针** ✓（**非空洞** ✓）：取 `R := F` ✓（此时「`F ⊂ R`」退化为 `F ⊆ F` ✓）、`M := F` ✓、
`r = 1`、`s 0 = t 0 = 1`、`f 0 = id` ✓ ⟹ **`F` 结构类非空** ✓（源 §1 三类例子之最简实体 ✓）。 -/
def fStructProbe : FStruct F 1 (fun _ => 1) (fun _ => 1) where
  R := F
  M := F
  str := linearStructureProbe F F

/-- **L1 探针（合并读数）** ✓：`F` 结构在 `r = 1` 档**可实例化** ✓。 -/
theorem FStruct_nonempty : Nonempty (FStruct.{u, u} F 1 (fun _ => 1) (fun _ => 1)) :=
  ⟨fStructProbe F⟩

/-- **L1 探针（任意底环档 ✓）**：对**任意**满足 `[Algebra F R]` 的 `R` 与任意线性结构 ✓，
`FStruct.mk` 给出一个 `F` 结构 ✓ ⟹ 非空洞性**不**依赖 `R = F` 的特殊选取 ✓。 -/
theorem FStruct_nonempty_of (R : Type u) [CommRing R] [Algebra F R] (M : Type v)
    [AddCommGroup M] [Module R M] (str : LinearStructure R M r s t) :
    Nonempty (FStruct.{u, v} F r s t) :=
  ⟨FStruct.mk (F := F) R M str⟩

end FStruct

/-! ## 8. 源 §1：基变换 `M ⊗_φ S`（印版 169--170 ✓） -/

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- **【缺口处置】`M ⊗[R] S` 的 `S`-模结构** ✓（源 §1 的 `M ⊗_φ S` ✓，印版 169 ✓ 逐字：
`\mathcal{M} \otimes_{\phi} S = \langle S, M \otimes_{\phi} S, f_{1} \otimes 1, \dots ,f_{r} \otimes 1\rangle` ✓）。

**⚠ 库内缺口登记** ✓（**实测** ✓，§82.5 ✓）：mathlib **只有首因子取向** ✓
（`Module S (S ⊗[R] M)` ✓ 有实例 ✓）、**无次因子取向** ✗（`Module S (M ⊗[R] S)` 与
`SMul S (M ⊗[R] S)` 皆 `synthInstanceFailed` ✗）⟹ 本件沿 `TensorProduct.comm R M S` ✓
（`R`-线性等价 ✓）用 **`AddEquiv.module`** ✓ 把 `S`-模结构**搬运**到源的序 ✓。
**搬运后的 `s • ·` 正是源所要的** ✓：`comm (m ⊗ₜ t) = t ⊗ₜ m` ✓ ⟹ 首因子作用 ✓ ⟹ `comm.symm` 回搬
⟹ `s • (m ⊗ₜ t) = m ⊗ₜ (s * t)` ✓。

**⚠ 作用域** ✓：`scoped instance` ✓（须 `open scoped ABGV52` ✓ 激活 ✓）—— 避免与 mathlib 在
**首因子取向**的实例形成**菱形** ✓（`M := S` 档两者皆可适用 ✓）。 -/
scoped instance tensorProductRightModule : Module S (M ⊗[R] S) :=
  (TensorProduct.comm R M S).toAddEquiv.module S

open scoped ABGV52

/-- **源 §1 的 `f_i ⊗ 1`** ✓（印版 170 ✓ 逐字：「so `f_{i} ⊗ 1 : (M ⊗ S)^{(s_{i})} → (M ⊗ S)^{(t_{i})}`
is **well defined**」✓）：由 `f : M^{(a)} → M^{(b)}` 给出
`f ⊗ 1 : M^{(a)} ⊗_R S →_S M^{(b)} ⊗_R S` ✓。
**构造** ✓：把 mathlib 的 `AlgebraTensorModule.map` ✓（**首因子 `S`-线性** ✓、**次因子 `R`-线性** ✓ ——
正是 `id ⊗ f` 的两支 ✓）用 **`comm` 的 `S`-线性形** ✓（`AddEquiv.linearEquiv` ✓：搬运结构后
`comm` 自动 `S`-线性 ✓）**两面夹住** ✓ ⟹ `S`-线性性**免费**得 ✓。
**⚠ 用途** ✓：`S`-**半线性**档的 `tensorPowerMapSL`（§4 ✓）在此**不需要** ✓ —— 基变换只需 `R`-线性
`f` ✓ 与**新底环的模结构** ✓。 -/
noncomputable def tensorPowerBaseChange {a b : ℕ}
    (f : TensorPower R a M →ₗ[R] TensorPower R b M) :
    TensorPower R a M ⊗[R] S →ₗ[S] TensorPower R b M ⊗[R] S :=
  ((TensorProduct.comm R (TensorPower R b M) S).toAddEquiv.linearEquiv S).symm.toLinearMap.comp
    ((AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) f).comp
      ((TensorProduct.comm R (TensorPower R a M) S).toAddEquiv.linearEquiv S).toLinearMap)

/-- **生成元刻画** ✓：`(f ⊗ 1) (x ⊗ₜ s) = (f x) ⊗ₜ s` ✓ —— 即源「`f_i ⊗ 1`」的**用点形** ✓
（源只用它说「well defined」✓；本件把它作 **L1 探针 ＋ 计算入口** ✓）。 -/
theorem tensorPowerBaseChange_tmul {a b : ℕ}
    (f : TensorPower R a M →ₗ[R] TensorPower R b M) (x : TensorPower R a M) (s : S) :
    tensorPowerBaseChange (S := S) f (x ⊗ₜ[R] s) = f x ⊗ₜ[R] s := by
  simp [tensorPowerBaseChange, TensorProduct.comm_tmul, AlgebraTensorModule.map_tmul]

/-- **L1 探针** ✓：`tensorPowerBaseChange` 在**任意** `R`-线性 `f`、任意 `S` 上**可实例化** ✓
（上式即见证 ✓）⟹ 非空洞 ✓。 -/
theorem tensorPowerBaseChange_nonempty (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type v) [AddCommGroup M] [Module R M] (a b : ℕ)
    (f : TensorPower R a M →ₗ[R] TensorPower R b M) :
    Nonempty (TensorPower R a M ⊗[R] S →ₗ[S] TensorPower R b M ⊗[R] S) :=
  ⟨tensorPowerBaseChange (S := S) f⟩


/-! ### 8.1 源「`(M ⊗_φ S)^{(n)}` identified with `M^{(n)} ⊗_φ S`」（印版 170 ✓） -/

/-- **(★) 的基例 `n = 0`** ✓：`⨂[S]^0 (S ⊗[R] M)` 与 `S ⊗[R] ⨂[R]^0 M` 两边都典范同构于 `S` ✓
（`PiTensorProduct.isEmptyEquiv` ✓ ＋ `AlgebraTensorModule.rid` ✓）。 -/
noncomputable def tensorPowerBaseChangeAuxZero :
    TensorPower S 0 (S ⊗[R] M) ≃ₗ[S] S ⊗[R] TensorPower R 0 M :=
  (PiTensorProduct.isEmptyEquiv (Fin 0) (R := S) (s := fun _ => S ⊗[R] M)).trans
    ((AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (PiTensorProduct.isEmptyEquiv (Fin 0) (R := R) (s := fun _ => M))).trans
      (AlgebraTensorModule.rid R S S)).symm

/-- **(★) 的归纳支** ✓：`(⨂[S]^n X) ⊗[S] X ≃ₗ[S] S ⊗[R] (A ⊗[R] M)` ✓，
其中 `X = S ⊗[R] M` ✓、`A = ⨂[R]^n M` ✓。
**用件** ✓：`AlgebraTensorModule.congr` ✓／`TensorProduct.comm` ✓／`cancelBaseChange` ✓（**基变换**）／
`assoc` ✓／`TensorProduct.comm R` ✓。
**⚠ 口径** ✓（子代理实测 ✓）：`cancelBaseChange` **不能**用「首因子只是 `R`-模」的档 ✗
（它要求首因子是 `A`-模 ✓）⟹ 可行的序是 `(S ⊗[R] A) ⊗[S] X ≅ X ⊗[S] (S ⊗[R] A)` ✓（`comm S` ✓）
再 `cancelBaseChange R S S X A` ✓；`assoc` 的环参数须给**同环档** ✓（`(A := R) (B := S)` ✓）。 -/
noncomputable def tensorPowerBaseChangeAuxStep (n : ℕ)
    (ih : TensorPower S n (S ⊗[R] M) ≃ₗ[S] S ⊗[R] TensorPower R n M) :
    TensorPower S n (S ⊗[R] M) ⊗[S] (S ⊗[R] M) ≃ₗ[S]
      S ⊗[R] (TensorPower R n M ⊗[R] M) :=
  (AlgebraTensorModule.congr ih (LinearEquiv.refl S (S ⊗[R] M))).trans
    ((TensorProduct.comm S (S ⊗[R] TensorPower R n M) (S ⊗[R] M)).trans
      ((AlgebraTensorModule.cancelBaseChange (R := R) (A := S) (B := S)
          (M := S ⊗[R] M) (N := TensorPower R n M)).trans
        ((AlgebraTensorModule.assoc (R := R) (A := R) (B := S) (M := S)
            (P := M) (Q := TensorPower R n M)).trans
          (AlgebraTensorModule.congr (LinearEquiv.refl S S)
            (TensorProduct.comm R M (TensorPower R n M))))))

/-- **(★)** ✓：`⨂[S]^n (S ⊗[R] M) ≃ₗ[S] S ⊗[R] ⨂[R]^n M` ✓（对 `n` 递归 ✓）。
**用件** ✓：`TensorPower.mulEquiv` ✓／`subsingletonEquiv` ✓／归纳假设 ✓／`AlgebraTensorModule.congr` ✓。 -/
noncomputable def tensorPowerBaseChangeAux :
    (n : ℕ) → TensorPower S n (S ⊗[R] M) ≃ₗ[S] S ⊗[R] TensorPower R n M
  | 0 => tensorPowerBaseChangeAuxZero
  | n + 1 =>
      (TensorPower.mulEquiv (R := S) (M := S ⊗[R] M) (n := n) (m := 1)).symm
        |>.trans ((AlgebraTensorModule.congr (LinearEquiv.refl S (TensorPower S n (S ⊗[R] M)))
              (PiTensorProduct.subsingletonEquiv (R := S) (s := fun _ : Fin 1 => S ⊗[R] M) 0)).trans
          ((tensorPowerBaseChangeAuxStep n (tensorPowerBaseChangeAux n)).trans
            (AlgebraTensorModule.congr (LinearEquiv.refl S S)
              ((AlgebraTensorModule.congr (LinearEquiv.refl R (TensorPower R n M))
                  (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => M) 0).symm).trans
                (TensorPower.mulEquiv (R := R) (M := M) (n := n) (m := 1))))))

/-- **源 §1（印版 170 ✓ 逐字）：「where `(M ⊗_φ S)^{(n)}` is identified with `M^{(n)} ⊗_φ S`」** ✓✅：
`⨂[S]^n (M ⊗[R] S) ≃ₗ[S] (⨂[R]^n M) ⊗[R] S` ✓ —— **保源的因子序** ✓ `M ⊗[R] S` ✓。
**路线** ✓（三段复合 ✓）：① 逐槽 `comm` ✓（`PiTensorProduct.congr` ✓）⟹ `⨂[S]^n (S ⊗[R] M)` ✓；
② **(★)** ✓（`tensorPowerBaseChangeAux` ✓）；③ `comm` 回源序 ✓（`S ⊗[R] ⨂[R]^n M ≃ ⨂[R]^n M ⊗[R] S` ✓）。
**⚠ 库内缺口** ✓：mathlib **无**现成件 ✗（`PiTensorProduct`／`TensorPower` 两目录无 `cancelBaseChange`／
`baseChange` ✓，实测 ✓）⟹ **自建** ✓。
**⚠ 语义核（未做，登记** ✗**）** ✓：**生成元刻画** ✗（`tprod S (fun i => m i ⊗ₜ s i) ↦ tprod R m ⊗ₜ ∏ᵢ s i` ✓）
**尚未证** ✗ —— **卡点逐字** ✓：一般 `n` 需 **`TensorPower.mulEquiv.symm` 在 `tprod` 上的引理** ✗
（mathlib **无**打包件 ✓：`TensorPower.mulEquiv_tprod`／`gMul_tprod_tprod`／`mulEquiv_symm_apply_tprod`／
`PiTensorProduct.congr_apply` **皆 unknown identifier** ✓）；`n = 0` 档另需绕开
`TensorPower` 单位元的 **`OfNat` 缺失** ✗（用 `TensorPower.gOne_def`／`tprod S Fin.elim0` ✓）。
**⚠ 本件的定位** ✓：**构造已落且编译通过（仅三标准公理 ✓）**，而其**生成元语义核尚未过** ✗
⟹ 下游若据此件承重，须按 **`∅-unchecked`** ✓ 对待（L21／L44 ✓）。 -/
noncomputable def tensorPowerBaseChangeEquiv (n : ℕ) :
    TensorPower S n (M ⊗[R] S) ≃ₗ[S] TensorPower R n M ⊗[R] S :=
  (PiTensorProduct.congr (fun _ : Fin n => (TensorProduct.comm R M S).toAddEquiv.linearEquiv S)).trans
    ((tensorPowerBaseChangeAux n).trans
      ((TensorProduct.comm R (TensorPower R n M) S).toAddEquiv.linearEquiv S).symm)


/-! ### 8.2 源 §1 的**线性结构基变换**（印版 169--170 ✓） -/

/-- **源 §1 的基变换** ✓（印版 169 ✓ 逐字：「`\mathcal{M}\otimes_{\phi}S = \langle S, M\otimes_{\phi}S,
f_{1}\otimes 1,\dots ,f_{r}\otimes 1\rangle`」✓）：把 `X : LinearStructure R M r s t` 沿 `R → S`
推到 `LinearStructure S (M ⊗[R] S) r s t` ✓，其 `f_i` 支 ＝ **源序下的 `f_i ⊗ 1`** ✓。

**构造** ✓：把 `tensorPowerBaseChange (X.f i)` ✓（§8 ✓，`M^{(s_i)} ⊗ S → M^{(t_i)} ⊗ S` ✓）用印 170 的
**「identified with」iso** ✓（§8.1 的 `tensorPowerBaseChangeEquiv` ✓）**两面夹住** ✓ ⟹ 得到
`⨂[S]^(s_i) (M ⊗[R] S) →ₗ[S] ⨂[S]^(t_i) (M ⊗[R] S)` ✓ —— 正是 `LinearStructure S (M ⊗[R] S) r s t`
的 `f` 字段所要的型 ✓。
**⚠ 口径** ✓：源把 `(M ⊗_φ S)^{(n)}` 与 `M^{(n)} ⊗_φ S` **认同** ✓ ⟹ 本件即该认同下搬运的结果 ✓；
**⚠ §8.1 的生成元语义核未过** ✗ ⟹ **本件同样按 `∅-unchecked`** ✓ 对待（L21／L44 ✓）。 -/
noncomputable def LinearStructure.baseChange {r : ℕ} {s t : Fin r → ℕ}
    (X : LinearStructure R M r s t) : LinearStructure S (M ⊗[R] S) r s t where
  f i := (tensorPowerBaseChangeEquiv (R := R) (S := S) (M := M) (t i)).symm.toLinearMap.comp
    ((tensorPowerBaseChange (R := R) (S := S) (X.f i)).comp
      (tensorPowerBaseChangeEquiv (R := R) (S := S) (M := M) (s i)).toLinearMap)

/-- **外形锁定** ✓：基变换的 `f` 支**逐字**是上条的复合（`tensorPowerBaseChange` 被两头夹住 ✓）——
公式一旦漂移（如漏掉某一侧的 `comm`／`equiv` ✗），本 `rfl` 立即编译失败 ✓。 -/
theorem LinearStructure.baseChange_typeLock {r : ℕ} {s t : Fin r → ℕ}
    (X : LinearStructure R M r s t) (i : Fin r) :
    (X.baseChange (S := S)).f i =
      (tensorPowerBaseChangeEquiv (R := R) (S := S) (M := M) (t i)).symm.toLinearMap.comp
        ((tensorPowerBaseChange (R := R) (S := S) (X.f i)).comp
          (tensorPowerBaseChangeEquiv (R := R) (S := S) (M := M) (s i)).toLinearMap) :=
  rfl

/-- **L1 探针** ✓（**非空洞** ✓）：对**任意** `X` 与任意 `[Algebra R S]` ✓，基变换**可实例化** ✓。 -/
theorem LinearStructure.baseChange_nonempty {r : ℕ} {s t : Fin r → ℕ}
    (X : LinearStructure R M r s t) : Nonempty (LinearStructure S (M ⊗[R] S) r s t) :=
  ⟨X.baseChange (S := S)⟩

/-! ### 8.3 源 §1 的 **`F` 结构基变换**（印版 170 ✓） -/

/-- **源 §1 的 `F` 结构基变换** ✓（源「an `F` map `\phi : R \to S` with `S` commutative」✓，印 170 ✓）：
把 `X : FStruct F r s t` 沿 `F`-映射 `R → S` 推到 `S` 上的 `F` 结构 ✓ —— `R := S` ✓、
`M := X.M ⊗[X.R] S` ✓、`str := X.str.baseChange` ✓。
**⚠ 形式化约定** ✓：源的 `\phi` 是**任意** `F`-映射 ✓；本件用 **`[Algebra X.R S]` ＋
`[IsScalarTower F X.R S]`** ✓ 落 —— 后者**正是**「`\phi` 是 `F`-映射」的库内形 ✓
（即 `algebraMap F S = algebraMap X.R S ∘ algebraMap F X.R` ✓）。 -/
noncomputable def FStruct.baseChange {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct F r s t) (S : Type u) [CommRing S] [Algebra F S] [Algebra X.R S]
    [IsScalarTower F X.R S] : FStruct F r s t where
  R := S
  M := X.M ⊗[X.R] S
  str := X.str.baseChange (R := X.R) (S := S)

/-- **外形锁定** ✓：基变换后的**底环**必为 `S` ✓ —— 漂移即 `rfl` 失败 ✓。 -/
theorem FStruct.baseChange_typeLock {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct F r s t) (S : Type u) [CommRing S] [Algebra F S] [Algebra X.R S]
    [IsScalarTower F X.R S] :
    (X.baseChange S).R = S :=
  rfl

/-- **L1 探针** ✓（**非空洞** ✓）：对任意 `X` 与任意满足 `[IsScalarTower F X.R S]` 的 `S` ✓，
`F` 结构基变换**可实例化** ✓。 -/
theorem FStruct.baseChange_nonempty {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct.{u, v} F r s t) (S : Type u) [CommRing S] [Algebra F S] [Algebra X.R S]
    [IsScalarTower F X.R S] : Nonempty (FStruct.{u, max u v} F r s t) :=
  ⟨X.baseChange S⟩


/-! ### 8.4 源 §1 的 **`F`-类**（印版 170 ✓） -/

/-- **源 §1 ③ 的「下降数据」** ✓（印版 170 ✓：「there is a `\mathcal{M}^{\prime\prime}/R^{\prime\prime}
\in \mathcal{C}` such that `R^{\prime}\subseteq R^{\prime\prime}\subseteq R`; `R^{\prime\prime}` is
**finitely generated as a ring over** `R^{\prime}` and
`\mathcal{M}^{\prime\prime}\otimes_{R^{\prime\prime}}R\cong \mathcal{M}`」✓）。
**⚠ 为何打包** ✓：`\exists` 的绑定列表**不接受实例绑定** `[..]` ✗（实测 ✓），而 `M''` 的
`AddCommGroup`／`Module` 实例是**数据** ✓（`∃` 里必须给出 ✓）⟹ 打包为结构 ✓（其实例字段 ✓）。
**用件** ✓：`Subalgebra` ✓／`Algebra.FiniteType` ✓／`Subalgebra.inclusion` ✓（`Algebra ↥R' ↥R''` 实例
由它显式供给 ✓ —— `∃`/结构内部无法 `letI` ✓，故 `finite` 字段用 `@Algebra.FiniteType … (…)` 显式传参 ✓）。 -/
structure DescentData {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct.{u, u} F r s t) (R' : Subalgebra F X.R) where
  /-- 源：`R^{\prime\prime}` ✓。 -/
  R'' : Subalgebra F X.R
  /-- 源：`R^{\prime}\subseteq R^{\prime\prime}` ✓（`R^{\prime\prime}\subseteq R` 由「是 `X.R` 的子代数」自动 ✓）。 -/
  le : R' ≤ R''
  /-- 源：`\mathcal{M}^{\prime\prime}` ✓。 -/
  M'' : Type u
  [addCommGroup : AddCommGroup M'']
  [module : Module ↥R'' M'']
  /-- 源：`\mathcal{M}^{\prime\prime}/R^{\prime\prime}` 是**线性结构** ✓。 -/
  str : LinearStructure ↥R'' M'' r s t
  /-- 源：`R^{\prime\prime}` 在 `R^{\prime}` 上**有限生成** ✓。 -/
  finite : @Algebra.FiniteType ↥R' ↥R'' _ _ ((Subalgebra.inclusion le).toRingHom.toAlgebra)
  /-- 源：`\mathcal{M}^{\prime\prime}\otimes_{R^{\prime\prime}}R\cong \mathcal{M}` ✓（`IsIso` ✓，同底环 `X.R` ✓）。 -/
  iso : IsIso (str.baseChange (S := X.R)) X.str

/-- **源 §1 的 `F`-类** ✓（印版 170 ✓ 逐字：「An `F`-class `\mathcal{C}` is a class of `F` structures
closed under (`F` linear) isomorphisms such that it has **two additional properties**. **First**, if
`\mathcal{M}/R\in \mathcal{C}` and `\phi :R\to S` is an `F` map with `S` commutative, then
`\mathcal{M}\otimes_{\phi}S\in \mathcal{C}`. **Secondly**, if `\mathcal{M}/R\in \mathcal{C}` and
`R^{\prime}\subseteq R` is a subring, then there is a `\mathcal{M}^{\prime\prime}/R^{\prime\prime}
\in \mathcal{C}` such that …」✓）。

**三条** ✓（源把 ① 计入定义 ✓、② ③ 即 the two additional properties ✓）：
**① 同构封闭** ✓（`IsIso` ✓）；**② 基变换封闭** ✓（`FStruct.baseChange` ✓）；
**③ 下降 ＋ 有限生成** ✓（前提 `C X` ✓ ⟹ `Nonempty (DescentData X R')` ✓，`DescentData` 内含
`R' ⊆ R''` ✓／有限生成 ✓／`M'' ⊗_{R''} R ≅ M` ✓ **三条合取** ✓ —— **不得截支** ✓，L39 ✓）。

**⚠ 形式化约定** ✓（**登记** ✓）：源在**无宇宙分层**的语境里说话 ✓；Lean 里基变换把 `M ⊗[R] S` 送进
`Type (max v u)` ✗ ⟹ **本件要求模的宇宙与底环相同** ✓（`FStruct.{u, u}` ✓），使**基变换保持宇宙不变** ✓、
`C` 得为**单一谓词** ✓（否则 ② 的 `C (X.baseChange S)` 与 ① 的 `C ⟨R, M, X⟩` 不同宇宙 ✗）。
**⚠ `∅-unchecked` 传染** ✓：② 支建立在 §8.1 的 iso 上 ✓ ⟹ 沿 §86.2 的登记 ✓。 -/
def IsFClass {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  (∀ (R : Type u) [CommRing R] [Algebra F R] (M N : Type u) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] (X : LinearStructure R M r s t)
      (Y : LinearStructure R N r s t), IsIso X Y → C ⟨R, M, X⟩ → C ⟨R, N, Y⟩) ∧
  (∀ (X : FStruct.{u, u} F r s t) (S : Type u) [CommRing S] [Algebra F S] [Algebra X.R S]
      [IsScalarTower F X.R S], C X → C (X.baseChange S)) ∧
  (∀ (X : FStruct.{u, u} F r s t) (R' : Subalgebra F X.R), C X → Nonempty (DescentData X R'))

/-- **外形锁定 ①（同构封闭支）** ✓：`IsFClass` 的**第一合取**逐字可取 ✓ —— 合取次序或支内容一旦漂移即失败 ✓。 -/
theorem IsFClass.iso_closed {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : IsFClass C) :
    ∀ (R : Type u) [CommRing R] [Algebra F R] (M N : Type u) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] (X : LinearStructure R M r s t)
      (Y : LinearStructure R N r s t), IsIso X Y → C ⟨R, M, X⟩ → C ⟨R, N, Y⟩ :=
  h.1

/-- **外形锁定 ②（基变换封闭支）** ✓。 -/
theorem IsFClass.baseChange_closed {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : IsFClass C) :
    ∀ (X : FStruct.{u, u} F r s t) (S : Type u) [CommRing S] [Algebra F S] [Algebra X.R S]
      [IsScalarTower F X.R S], C X → C (X.baseChange S) :=
  h.2.1

/-- **外形锁定 ③（下降／有限生成支）** ✓：前提 `C X` ✓ 下给出**下降数据** ✓（`R' ⊆ R''` ✓／有限生成 ✓／
`M'' ⊗_{R''} R ≅ M` ✓ 三条**一并**锁定 ✓）。 -/
theorem IsFClass.descent {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : IsFClass C)
    (X : FStruct.{u, u} F r s t) (R' : Subalgebra F X.R) (hX : C X) :
    Nonempty (DescentData X R') :=
  h.2.2 X R' hX

/-- **L1 探针** ✓（**定义外形可满足** ✓）：**空类**是一个 `F`-类 ✓ —— 三条**逐条**可验 ✓
（①②由前提 `C _ = False` ✓ 直接消去 ✓；③由前提 `C X = False` ✓ 消去 ✓）。
**⚠ 定位** ✓：本探针只证「`IsFClass` 的**三条合取不自相矛盾**」✓；
**⚠ 不证** ✗：**非空**的 `F`-类（如源的 `\mathcal{A}(F,n)` ✓／`\mathcal{E}(G)` ✓）满足三条 ✓ ——
源以 `\cite{18}` p. 35 ／ `\cite{7}` p. 85 ／ `\cite{22}` p. 528 作据 ✓，**本件未涉** ✗
（按 `∅-unchecked` ✓ 对待）。 -/
theorem isFClass_false {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ} :
    IsFClass (F := F) (r := r) (s := s) (t := t) (fun _ => False) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _ M N _ _ _ _ X Y _ hX
    exact False.elim hX
  · intro X S _ _ _ _ hX
    exact False.elim hX
  · intro X R' hX
    exact False.elim hX


/-! ### 8.5 源 §1 的**提升性质**（印版 170 ✓） -/

/-- **源 §1 的提升数据** ✓（印版 170 ✓：「whenever `T`, `M` is a **local** `F` algebra and
`\mathcal{M}\in \mathcal{C}` is over `T / M`, then there is a `\mathcal{M}^{\prime}/T\in \mathcal{C}`
such that `\mathcal{M}^{\prime}\otimes_{T}T / M\cong \mathcal{M}`」✓）。

**⚠ 记号** ✓：源的 `T`, `M` ＝ **局部环 `T` 与其极大理想 `M`** ✓（`\mathcal{M}` ✓ 才是结构 ✓，
与理想 `M` 不同字形 ✓）；`T / M` ＝ **剩余域** ✓ ⟹ 落为 `IsLocalRing.ResidueField T` ✓。
**⚠ 为何打包** ✓：`N` 的 `AddCommGroup`／`Module T` 实例是**数据** ✓，而 `\exists` **不接受实例绑定** ✗
（附四十六 ⑳ ✓）⟹ 打包为结构 ✓。 -/
structure LiftingData {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) (T : Type u) [CommRing T] [Algebra F T] [IsLocalRing T]
    (M' : Type u) [AddCommGroup M'] [Module (IsLocalRing.ResidueField T) M']
    (X : LinearStructure (IsLocalRing.ResidueField T) M' r s t) where
  /-- 源：`\mathcal{M}^{\prime}` 的载体 ✓。 -/
  N : Type u
  [addCommGroup : AddCommGroup N]
  [module : Module T N]
  /-- 源：`\mathcal{M}^{\prime}/T` 是**线性结构** ✓（底环为 `T` ✓，不是 `T/M` ✓）。 -/
  str : LinearStructure T N r s t
  /-- 源：`\mathcal{M}^{\prime}/T\in \mathcal{C}` ✓。 -/
  mem : C ⟨T, N, str⟩
  /-- 源：`\mathcal{M}^{\prime}\otimes_{T}T / M\cong \mathcal{M}` ✓，**同构是 `T / M`-线性** ✓
  （「the isomorphism being `T / M` linear, by definition」✓）—— 落为同底环 `T/M` ✓ 的 `IsIso` ✓。 -/
  iso : IsIso (str.baseChange (S := IsLocalRing.ResidueField T)) X

/-- **源 §1 的提升性质** ✓（印版 170 ✓ 逐字：「We say an `F` class `\mathcal{C}` has the **lifting
property** if whenever `T`, `M` is a **local** `F` algebra and `\mathcal{M}\in \mathcal{C}` is over
`T / M`, then there is a `\mathcal{M}^{\prime}/T\in \mathcal{C}` such that
`\mathcal{M}^{\prime}\otimes_{T}T / M\cong \mathcal{M}`」✓）。

**四条分支** ✓（**逐一落** ✓，L39 ✓）：① `T` 是**局部 `F` 代数** ✓（`[IsLocalRing T]` ＋ `[Algebra F T]` ✓）；
② `\mathcal{M}` **over `T/M`** ✓（底环取 `IsLocalRing.ResidueField T` ✓）；③ **存在** `\mathcal{M}'/T\in\mathcal{C}` ✓
（`LiftingData.str` ✓ ＋ `.mem` ✓）；④ **基变换回 `\mathcal{M}`** ✓（`.iso` ✓）。
**⚠ 前提** ✓：源在 `\mathcal{M}\in\mathcal{C}` ✓ 下断言 ⟹ 落为 `C ⟨…⟩ →` ✓（**不得吞前提** ✓，§87.3 ✓）。
**⚠ `∅-unchecked` 传染** ✓：④ 支经 `baseChange` ✓ ⟹ 沿 §86.2／§87.4 的登记 ✓。 -/
def HasLiftingProperty {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra F T] [IsLocalRing T]
    (M' : Type u) [AddCommGroup M'] [Module (IsLocalRing.ResidueField T) M']
    (X : LinearStructure (IsLocalRing.ResidueField T) M' r s t),
    C ⟨IsLocalRing.ResidueField T, M', X⟩ → Nonempty (LiftingData C T M' X)

/-- **外形锁定** ✓：`HasLiftingProperty` 的**用点形**逐字可取 ✓ —— 四条分支或前提一旦漂移即失败 ✓
（「局部 `F` 代数」✓／「over `T/M`」✓／「存在 `\mathcal{M}'/T\in\mathcal{C}`」✓／「基回同构」✓）。 -/
theorem HasLiftingProperty.lift {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : HasLiftingProperty C)
    (T : Type u) [CommRing T] [Algebra F T] [IsLocalRing T]
    (M' : Type u) [AddCommGroup M'] [Module (IsLocalRing.ResidueField T) M']
    (X : LinearStructure (IsLocalRing.ResidueField T) M' r s t)
    (hX : C ⟨IsLocalRing.ResidueField T, M', X⟩) :
    Nonempty (LiftingData C T M' X) :=
  h T M' X hX

/-- **L1 探针** ✓（**定义外形可满足** ✓）：**空类**具有提升性质 ✓ —— 前提 `C _ = False` ✓ 直接消去 ✓。
**⚠ 定位** ✓：本探针只证「`HasLiftingProperty` 的**形状不自相矛盾**」✓；
**⚠ 不证** ✗：**非空**的 `F`-类（如源的 `\mathcal{A}(F,n)` ✓／`\mathcal{E}(G)` ✓）是否**真**具此性质 ✓ ——
那**正是** §3 的 `thm3.11`／`thm3.12` 与 `cor3.10` 整条链的内容 ✓，**本件未涉** ✗（按 `∅-unchecked` ✓）。 -/
theorem hasLiftingProperty_false {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ} :
    HasLiftingProperty (F := F) (r := r) (s := s) (t := t) (fun _ => False) := by
  intro T _ _ _ M' _ _ X hX
  exact False.elim hX


/-! ### 8.6 源 §1 的**表示对象／一般对象／特化**（印版 170 ✓） -/

/-- **源 §1 的「实现」数据** ✓（印版 170 ✓：「if `R` is an **affine** `F` algebra and if whenever
`\mathcal{N}/K\in \mathcal{C}` with `K` a field, then there is an `F` map `\phi :R\to K` such that
`\mathcal{N}\cong \mathcal{M}\otimes_{\phi}K`」✓）。

**⚠ 为何打包** ✓：`\phi :R\to K` 是**存在量词**下的 ✓，而 Lean 里它对应**实例**
（`Algebra X.R K` ✓ ＋ `IsScalarTower F X.R K` ✓ ＝ 「`\phi` 是 `F`-映射」✓，与 §8.3 同口径 ✓），
而 `\exists` **不接受实例绑定** ✗（附四十六 ⑳ ✓）⟹ 打包为结构 ✓（实例字段 ✓ 供后随字段使用 ✓）。 -/
structure Realization {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct.{u, u} F r s t) (K : Type u) [Field K] [Algebra F K]
    (N : Type u) [AddCommGroup N] [Module K N] (Y : LinearStructure K N r s t) where
  [algebra : Algebra X.R K]
  [tower : IsScalarTower F X.R K]
  /-- 源：`\mathcal{N}\cong \mathcal{M}\otimes_{\phi}K` ✓（同底环 `K` ✓ 的 `IsIso` ✓；
  用 `X.str.baseChange` ✓ 而非 `(X.baseChange K).str` ✓ —— 后者底环是投影 ✗，实例搜索不化约 ✓）。 -/
  iso : IsIso (X.str.baseChange (S := K)) Y

/-- **源 §1 的表示对象** ✓（印版 170 ✓ 逐字：「`\mathcal{M}/R\in \mathcal{C}` is a **representing object**
for `\mathcal{C}` if `R` is an **affine** `F` algebra and if whenever `\mathcal{N}/K\in \mathcal{C}` with
`K` a field, then there is an `F` map `\phi :R\to K` such that
`\mathcal{N}\cong \mathcal{M}\otimes_{\phi}K`」✓）。

**两条** ✓（**逐一落** ✓，L39 ✓）：① **`R` 是仿射 `F` 代数** ✓（落为 `Algebra.FiniteType F X.R` ✓ ——
**⚠ 口径** ✓：Saltman 的「affine」＝ **有限生成 `F`-代数** ✓，登记 ✓）；② 对**每个域 `K`** ✓ 上的
`\mathcal{N}/K\in\mathcal{C}` ✓，**存在 `\phi : R\to K`** ✓（`Realization` ✓）使
`\mathcal{N}\cong \mathcal{M}\otimes_{\phi}K` ✓。
**⚠ 前提** ✓：源在 `\mathcal{N}\in\mathcal{C}` ✓ 下断言 ⟹ 落为 `C ⟨…⟩ →` ✓（**不得吞前提** ✓，§87.3 ✓）。 -/
def RepresentingObject {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) (X : FStruct.{u, u} F r s t) : Prop :=
  Algebra.FiniteType F X.R ∧
    ∀ (K : Type u) [Field K] [Algebra F K] (N : Type u) [AddCommGroup N] [Module K N]
      (Y : LinearStructure K N r s t), C ⟨K, N, Y⟩ → Nonempty (Realization X K N Y)

/-- **源 §1 的特化** ✓（印版 170 ✓：「In this circumstance we say that `\mathcal{N}/K` is a
**specialization** of `\mathcal{M}/R` and that `\phi` **realizes** `\mathcal{N}/K`」✓）——
即「存在 `\phi` 使 `\mathcal{N}\cong \mathcal{M}\otimes_{\phi}K`」✓，与 `Realization` 同内容 ✓（源只给名 ✓）。 -/
def IsSpecialization {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct.{u, u} F r s t) (K : Type u) [Field K] [Algebra F K]
    (N : Type u) [AddCommGroup N] [Module K N] (Y : LinearStructure K N r s t) : Prop :=
  Nonempty (Realization X K N Y)

/-- **源 §1 的一般对象** ✓（印版 170 ✓ 逐字：「Finally, a **generic object** `\mathcal{M}/R\in \mathcal{C}`
is a representing object such that `R` has the form `F[x_{1},\dots ,x_{n}](1 / r)`; that is, such that
`R` is a **localized polynomial ring**」✓）—— 落为 `RepresentingObject` ✓ ＋
**`\exists n, r`，`R \cong F[x_1,\dots ,x_n](1/r)`** ✓（`Localization.Away r` ✓ ＋ `AlgEquiv` ✓）。 -/
def GenericObject {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) (X : FStruct.{u, u} F r s t) : Prop :=
  RepresentingObject C X ∧
    ∃ (n : ℕ) (r : MvPolynomial (Fin n) F), Nonempty (Localization.Away r ≃ₐ[F] X.R)

/-- **外形锁定 ①（仿射支）** ✓：`RepresentingObject` 的**第一合取**逐字可取 ✓。 -/
theorem RepresentingObject.affine {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : RepresentingObject C X) : Algebra.FiniteType F X.R :=
  h.1

/-- **外形锁定 ②（实现支）** ✓：源「whenever `\mathcal{N}/K\in\mathcal{C}` …there is `\phi` …」✓ 逐字可取 ✓
（**含前提 `C ⟨K, N, Y⟩`** ✓）。 -/
theorem RepresentingObject.specializes {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : RepresentingObject C X) :
    ∀ (K : Type u) [Field K] [Algebra F K] (N : Type u) [AddCommGroup N] [Module K N]
      (Y : LinearStructure K N r s t), C ⟨K, N, Y⟩ → Nonempty (Realization X K N Y) :=
  h.2

/-- **外形锁定 ③（一般对象两支）** ✓：`GenericObject` ＝ **表示对象** ✓ ∧ **局部化多项式环形** ✓。 -/
theorem GenericObject.isRepresenting {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : GenericObject C X) : RepresentingObject C X :=
  h.1

/-- **L1 探针 ①** ✓（**非空洞** ✓，且**前提可满足** ✓）：给定**仿射** `X` ✓，`X` 是**空类**的表示对象 ✓
（② 支由前提 `C _ = False` ✓ 消去 ✓）；**⚠ 这一条同时**证「① 支 `Algebra.FiniteType F X.R` 并非自动成立」
✓（它出现在假设里 ✓，不是定理 ✓）。 -/
theorem representingObject_false_of_affine {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct.{u, u} F r s t) (h : Algebra.FiniteType F X.R) :
    RepresentingObject (F := F) (r := r) (s := s) (t := t) (fun _ => False) X :=
  ⟨h, fun _ _ _ _ _ _ _ hY => False.elim hY⟩

/-- **L1 探针 ②** ✓（**具体见证** ✓，**非空洞** ✓）：取 `R := F` ✓（**仿射** ✓）与 `r = 0` ✓ 的**平凡结构** ✓，
它是**空类**的**表示对象** ✓ —— 即源 §1 该定义**确有实例** ✓（**⚠ 只对空类** ✓；非空类的表示对象存在性
**正是** §3 的 `thm3.11`／`thm3.12` 的内容 ✓，**本件未涉** ✗）。 -/
theorem representingObject_probe {F : Type u} [Field F] :
    RepresentingObject
      (F := F) (r := 0) (s := Fin.elim0) (t := Fin.elim0) (fun _ => False)
      ⟨F, F, (⟨fun i => Fin.elim0 i⟩ :
        LinearStructure F F 0 Fin.elim0 Fin.elim0)⟩ :=
  ⟨inferInstance, fun _ _ _ _ _ _ _ hY => False.elim hY⟩


/-! ### 8.7 源 §1 的**稠密表示对象**（印版 171 ✓） -/

/-- **源 §1 的稠密表示对象** ✓（印版 171 ✓ 逐字：「A representing object `\mathcal{M}/R\in \mathcal{C}` is
called **densely representing** if `R` is a **domain** and if for any `0\neq s\in R`, then
`\mathcal{M}\otimes_{R}R(1 / s)` is a representing object」✓ —— **该页本轮已逐句核** ✓，与 tex `:114` ✓
**逐字符合** ✓）。

**三条** ✓（**逐一落** ✓，L39 ✓）：① **是表示对象** ✓（`RepresentingObject` ✓）；② **`R` 是整环** ✓
（`IsDomain X.R` ✓）；③ **对任意 `0\neq s\in R`** ✓，`\mathcal{M}\otimes_{R}R(1 / s)` ✓
（＝沿 `R\to R(1/s)` 的**基变换** ✓，即 `X.baseChange (Localization.Away s)` ✓）**仍是表示对象** ✓。
**⚠ 前提** ✓：源在 `0\neq s` ✓ 下断言 ⟹ 落为 `a\neq 0\to` ✓（**不得吞前提** ✓，§87.3 ✓）。
**⚠ `∅-unchecked` 传染** ✓：①③ 两支经 `RepresentingObject` ✓（其 ② 支经 `baseChange` ✓）⟹ 沿登记 ✓。 -/
def DenselyRepresenting {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) (X : FStruct.{u, u} F r s t) : Prop :=
  RepresentingObject C X ∧ IsDomain X.R ∧
    ∀ (a : X.R), a ≠ 0 → RepresentingObject C (X.baseChange (Localization.Away a))

/-- **外形锁定 ①（表示支）** ✓。 -/
theorem DenselyRepresenting.isRepresenting {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : DenselyRepresenting C X) : RepresentingObject C X :=
  h.1

/-- **外形锁定 ②（整环支）** ✓。 -/
theorem DenselyRepresenting.isDomain {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : DenselyRepresenting C X) : IsDomain X.R :=
  h.2.1

/-- **外形锁定 ③（局部化支）** ✓：源「for any `0\neq s\in R`, then `\mathcal{M}\otimes_{R}R(1 / s)` is a
representing object」✓ 逐字可取 ✓（**含前提 `a\neq 0`** ✓）。 -/
theorem DenselyRepresenting.away {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : DenselyRepresenting C X) (a : X.R) (ha : a ≠ 0) :
    RepresentingObject C (X.baseChange (Localization.Away a)) :=
  h.2.2 a ha

/-- **L1 探针** ✓（**形状可满足** ✓）：给定**基**表示对象 ✓、**整环** ✓、及**各局部化的有限生成性** ✓，
则 `X` 是**空类**的稠密表示对象 ✓（③ 支的 `RepresentingObject` 由 `representingObject_false_of_affine` ✓
与有限生成假设给出 ✓）；**⚠ 这一条同时说明** ✓：③ 支**不是**自动的 ✓（它要**每个** `R(1/s)` 仍仿射 ✓）。 -/
theorem denselyRepresenting_false_of {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (X : FStruct.{u, u} F r s t) (h : RepresentingObject (F := F) (fun _ => False) X)
    (hd : IsDomain X.R)
    (h2 : ∀ (a : X.R), a ≠ 0 → Algebra.FiniteType F (Localization.Away a)) :
    DenselyRepresenting (F := F) (fun _ => False) X :=
  ⟨h, hd, fun a ha =>
    representingObject_false_of_affine (X.baseChange (Localization.Away a)) (h2 a ha)⟩


/-! ### 8.8 源 §1 的**态射性质／投射对象／局部投射**（印版 171--173 ✓） -/

section Morphisms

variable {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module S N]
variable {M₁ : LinearStructure R M r s t} {N₁ : LinearStructure S N r s t}

/-- 源 §1：「The class of all `F` structures of a fixed type form a category where **we insist that all
homomorphisms be `F` linear**」✓（印 169 ✓）—— 落为 `\phi` 与两个 `F`-结构映射相容 ✓。
**⚠ 为何必需** ✓：§8.6--8.8 的类 `C` 是 **`F`-结构**的类 ✓，而 §5 的 `Hom` ✓ 是**一般**环同态档 ✓
（源 §1 开篇的定义 ✓）⟹ `F`-线性须**另加** ✓。 -/
def Hom.IsFLinear (Φ : Hom M₁ N₁) : Prop :=
  Φ.phi.comp (algebraMap F R) = algebraMap F S

/-- **源 §1 的满射** ✓（印 171 ✓ 逐字：「A **surjection** `(\phi ,\psi):\mathcal{M}\to \mathcal{N}` is a
morphism such that `\psi ,\phi` are surjections **as set maps**」✓）—— **两支皆满** ✓，**不得只取一支** ✓。 -/
def Hom.IsSurjective (Φ : Hom M₁ N₁) : Prop :=
  Function.Surjective Φ.phi ∧ Function.Surjective Φ.psi

/-- **源 §1 的 local 态射** ✓（印 172 ✓ 逐字：「Define a morphism `(\phi ,\psi):\mathcal{M} / R\to
\mathcal{N} / S` to be **local** if `\phi^{- 1}(S^{*}) = R^{*}`. That is, if **the preimage of every unit in
`S` is a unit in `R`**」✓）—— 落为源给出的**第二个**等价形 ✓（原像判据 ✓）。 -/
def Hom.IsLocal (Φ : Hom M₁ N₁) : Prop :=
  ∀ a : R, IsUnit (Φ.phi a) → IsUnit a

/-- **局部满射** ✓（印 172 ✓：「for all **local surjections** `\Psi`」✓ ＝ 局部 ∧ 满射 ∧ `F`-线性 ✓）。 -/
def Hom.IsLocalSurjection (Φ : Hom M₁ N₁) : Prop :=
  Hom.IsFLinear (F := F) Φ ∧ Φ.IsSurjective ∧ Φ.IsLocal

end Morphisms

section Projective

variable {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}

/-- **源 §1 的投射对象** ✓（印 171 ✓ 逐字：「If `\mathcal{P}` is an `F` structure of the same type as those
in `\mathcal{C}`, then `\mathcal{P}` is a **projective object** for `\mathcal{C}` if whenever
`\Delta :\mathcal{P}\to \mathcal{N}` and `\Psi :\mathcal{M}\to \mathcal{N}` are morphisms, where `\Psi` is a
**surjection** and `\mathcal{M},\mathcal{N}\in \mathcal{C}`, then there is a
`\Delta ':\mathcal{P}\to \mathcal{M}` such that `\Delta = \Psi\circ \Delta '`」✓）。

**⚠ 源明写不要求 `\mathcal{P}\in\mathcal{C}`** ✓（「We emphasize that, as with `R(F,n,r)`, we do **not** ask
that `\mathcal{P}` be in `\mathcal{C}`」✓，印 171 ✓）⟹ **本件不设 `C P`** ✓（它与 `ProjectiveObjectIn` ✓ 分列 ✓）。
**⚠ 分支** ✓：① `\Psi` **满** ✓；② `\mathcal{M},\mathcal{N}\in\mathcal{C}` ✓；③ **存在** `\Delta'` ✓；
④ **等式 `\Delta = \Psi\circ \Delta'`** ✓ —— **四条全落** ✓（L39 ✓）。 -/
def ProjectiveObjectFor (C : FStruct.{u, u} F r s t → Prop)
    (P : FStruct.{u, u} F r s t) : Prop :=
  ∀ (M N : FStruct.{u, u} F r s t) (Δ : Hom P.str N.str) (Ψ : Hom M.str N.str),
    Hom.IsFLinear (F := F) Ψ → Ψ.IsSurjective → C M → C N →
      ∃ (Δ' : Hom P.str M.str), Hom.IsFLinear (F := F) Δ' ∧ Δ = Δ'.comp Ψ

/-- **源 §1 的在 `\mathcal{C}` 中的投射对象** ✓（印 171 ✓ 逐字：「We say that `\mathcal{P}` is a projective
object **in** `\mathcal{C}` if `\mathcal{P}\in \mathcal{C}`」✓）—— **两支** ✓（`ProjectiveObjectFor` ✓ ∧
`C P` ✓），**不得与上条合并** ✓。 -/
def ProjectiveObjectIn (C : FStruct.{u, u} F r s t → Prop)
    (P : FStruct.{u, u} F r s t) : Prop :=
  ProjectiveObjectFor C P ∧ C P

/-- **源 §1 的局部投射** ✓（印 172 ✓ 逐字：「If `\mathcal{C}` is a category of `F` structures, then
`\mathcal{P}\in \mathcal{C}` is a **local projective** if for all **local surjections**
`\Psi :\mathcal{M}\to \mathcal{N}`, and all `\Delta :\mathcal{P}\to \mathcal{N}`, there is a
`\Delta ':\mathcal{P}\to \mathcal{M}` such that `\Delta = \Psi\circ \Delta '`」✓ —— **句子完于印 172 底**
✓，**本轮已核** ✓）。

**⚠ 与 `ProjectiveObjectFor` 的两处差别** ✓：**(a)** 源在此**要求 `\mathcal{P}\in\mathcal{C}`** ✓（「`\mathcal{P}\in\mathcal{C}` is a local projective」✓）——
故首合取为 `C P` ✓（**这也是空类探针写不出的原因** ✓，见下 ✓）；**(b)** `\Psi` 限为**局部**满射 ✓。
**⚠ 分支** ✓：① `C P` ✓；② `\Psi` **局部满射** ✓；③ `\mathcal{M},\mathcal{N}\in\mathcal{C}` ✓（源在 category 语境下 ✓）；
④ 存在 `\Delta'` ✓；⑤ 等式 ✓ —— **五条全落** ✓。 -/
def LocalProjective (C : FStruct.{u, u} F r s t → Prop)
    (P : FStruct.{u, u} F r s t) : Prop :=
  C P ∧
    ∀ (M N : FStruct.{u, u} F r s t) (Ψ : Hom M.str N.str) (Δ : Hom P.str N.str),
      Hom.IsLocalSurjection (F := F) Ψ → C M → C N →
        ∃ (Δ' : Hom P.str M.str), Hom.IsFLinear (F := F) Δ' ∧ Δ = Δ'.comp Ψ

/-- **外形锁定 ①（投射对象支）** ✓：`ProjectiveObjectIn` 的**第一合取**逐字可取 ✓。 -/
theorem ProjectiveObjectIn.projectiveFor {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {P : FStruct.{u, u} F r s t}
    (h : ProjectiveObjectIn C P) : ProjectiveObjectFor C P :=
  h.1

/-- **外形锁定 ②（在类中支）** ✓。 -/
theorem ProjectiveObjectIn.mem {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {P : FStruct.{u, u} F r s t}
    (h : ProjectiveObjectIn C P) : C P :=
  h.2

/-- **外形锁定 ③（局部投射＝在类中 ＋ 局部提升）** ✓：`LocalProjective` 的**两合取**逐字可取 ✓
（源「`\mathcal{P}\in\mathcal{C}` is a local projective」✓ ⟹ 首合取 `C P` **是定义的一部分** ✓）。 -/
theorem LocalProjective.mem {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {P : FStruct.{u, u} F r s t}
    (h : LocalProjective C P) : C P :=
  h.1

/-- **外形锁定 ④（局部投射的提升支）** ✓：**五条分支** ✓（`C P` 之外）一并锁定 ✓。 -/
theorem LocalProjective.lifts {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {P : FStruct.{u, u} F r s t}
    (h : LocalProjective C P) :
    ∀ (M N : FStruct.{u, u} F r s t) (Ψ : Hom M.str N.str) (Δ : Hom P.str N.str),
      Hom.IsLocalSurjection (F := F) Ψ → C M → C N →
        ∃ (Δ' : Hom P.str M.str), Hom.IsFLinear (F := F) Δ' ∧ Δ = Δ'.comp Ψ :=
  h.2

/-- **L1 探针** ✓（**形状可满足** ✓）：**空类**的**投射对象**是**任意** `P` ✓ —— 前提 `C M` ✓ 被消去 ✓。
**⚠ 这一条同时说明** ✓：`ProjectiveObjectFor` **不**含 `C P` ✓（与源的强调一致 ✓）。
**⚠ 不能照办者** ✗：`ProjectiveObjectIn`／`LocalProjective` **都含 `C P`** ✓ ⟹ **空类下写不出探针** ✗
（它们的非空性须**非空**的 `F`-类 ✓，即源的 `\mathcal{A}(F,n)`／`\mathcal{E}(G)` ✓ —— **本件未涉** ✗，`∅-unchecked` ✓）。 -/
theorem projectiveObjectFor_false {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (P : FStruct.{u, u} F r s t) :
    ProjectiveObjectFor (F := F) (fun _ => False) P := by
  intro M N Δ Ψ _ _ hM _
  exact False.elim hM


/-! ### 8.9 源 §1 的**特化收尾**与 `thm1.3(a)` 的**具名残余**（印版 170／172 底 ✓） -/

/-- **源 §1 的特化（收尾）** ✓（印 170 ✓ 逐字：「In this circumstance we say that `\mathcal{N}/K` is a
**specialization** of `\mathcal{M}/R` and that `\phi` **realizes** `\mathcal{N}/K`」✓）——
「In this circumstance」✓ 指**上句的表示对象** ✓ ⟹ 落为：**表示对象 ⟹ 每个域上在类中的对象都是它的特化** ✓，
且**实现者正是 `Realization` 里的 `\phi`** ✓（打包在实例字段中 ✓）。
**⚠ 前提** ✓：源在 `\mathcal{N}/K\in\mathcal{C}` ✓ 与 `K` **是域** ✓ 下说话 ⟹ 两条**都在语句里** ✓。 -/
theorem RepresentingObject.isSpecialization {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} {X : FStruct.{u, u} F r s t}
    (h : RepresentingObject C X) (K : Type u) [Field K] [Algebra F K]
    (N : Type u) [AddCommGroup N] [Module K N] (Y : LinearStructure K N r s t)
    (hY : C ⟨K, N, Y⟩) : IsSpecialization X K N Y :=
  h.2 K N Y hY

/-- **源 `thm1.3(a)`（印 172 底 ✓）的具名陈述** ✓ —— **⚠ 具名残余（named residual）：本件不作证明** ✗**。

源逐字 ✓：「(a) Let `\mathcal{C}` be an `F` class, and `\mathcal{P} / R\in \mathcal{C}` a local projective.
If `0\neq s\in R`, then `\mathcal{P}\otimes_{R}R(1 / s) / R(1 / s)\in \mathcal{C}` is a local projective」✓
（**印 172 底本轮已逐句核** ✓）。

**⚠ 为何只给陈述** ✗：其**证明**（源印 172 底 ✓）用「`\Hom(\mathcal{M}\otimes_R R(1/s),\mathcal{N}/S)` **可识别为**
`\Hom(\mathcal{M}/R,\mathcal{N}/S)` 中满足 `\phi (s)\in S` 是单位者的子集」✓ —— 该**识别**是 `thm1.3(a)` 的**实质**
✓，本身是一阶实质定理 ✗，**本件未落** ✗ ⟹ 按 **`∅-unchecked`** ✓ 对待（L21／L44 ✓）。
**⚠ 另三支** ✓：源 (b) `F[x_1,\dots ,x_n](1/s)` ✓／(c) `G`-Galois ✓／(d) Azumaya ✓ —— **依赖 `\mathcal{E}(G)`／
`\mathcal{A}(n)` 两个 `F`-类的定义** ✗（源印 170 只**提及**它们 ✓，定义在 §3／§5 ✓）
⟹ **本件不涉** ✗，**登记为范围外** ✓。

**⚠ 用件** ✓：`IsFClass C` ✓（供 ② 支 `C (P\otimes_R R(1/s))` ✓）＋ `LocalProjective C P` ✓。 -/
def Thm13aStatement {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  IsFClass C → ∀ (P : FStruct.{u, u} F r s t), LocalProjective C P →
    ∀ (a : P.R), a ≠ 0 → LocalProjective C (P.baseChange (Localization.Away a))

/-- **外形锁定** ✓：`Thm13aStatement` **四段**（`IsFClass C` ✓／`LocalProjective C P` ✓／`a\neq 0` ✓／
结论 `LocalProjective C (P\otimes_R R(1/s))` ✓）**一并**锁定 ✓ —— 与源 (a) 的四支**逐字对应** ✓。 -/
theorem Thm13aStatement.shape {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : Thm13aStatement C) (hC : IsFClass C) :
    ∀ (P : FStruct.{u, u} F r s t), LocalProjective C P →
      ∀ (a : P.R), a ≠ 0 → LocalProjective C (P.baseChange (Localization.Away a)) :=
  h hC


/-! ### 8.10 源 §1／§3 的定义：**相对提升**（印 172 底 ✓）／**有理性收缩**（`def3.1` ✓）／
**有理分解**（`def3.2` ✓） -/

section RelativeLifting

variable {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}

/-- **源的相对提升性质** ✓（印 172 底 ✓ 逐字：「Suppose `\mathcal{C}` and `\mathcal{C}^{\prime}` are both `F`
classes of the same type and `\mathcal{C}\subseteq \mathcal{C}^{\prime}`. We say that
`(\mathcal{C},\mathcal{C}^{\prime})` have the lifting property if for every local `F` algebra `T`, `M` and every
`\mathcal{M}\in \mathcal{C}` over `T / M` there is a `\mathcal{M}^{\prime}/T\in \mathcal{C}^{\prime}` such that
`\mathcal{M}^{\prime}\otimes_{T}T / M\cong \mathcal{M}`」✓ —— **该页本轮（r127）已逐句核** ✓）。

**三条** ✓（**逐一落** ✓）：① **两类同型** ✓（同为 `FStruct.{u,u} F r s t` ✓ ⇒ 自动 ✓）；
② **`\mathcal{C}\subseteq \mathcal{C}^{\prime}`** ✓（落为**逐点含入** ✓）；③ **提升目标在 `\mathcal{C}^{\prime}`** ✓
（`LiftingData C'` ✓ —— 与绝对档 `HasLiftingProperty C` ✓ 的**唯一**差别 ✓）。 -/
def RelativeLiftingProperty (C C' : FStruct.{u, u} F r s t → Prop) : Prop :=
  (∀ X, C X → C' X) ∧
    ∀ (T : Type u) [CommRing T] [Algebra F T] [IsLocalRing T]
      (M' : Type u) [AddCommGroup M'] [Module (IsLocalRing.ResidueField T) M']
      (X : LinearStructure (IsLocalRing.ResidueField T) M' r s t),
      C ⟨IsLocalRing.ResidueField T, M', X⟩ → Nonempty (LiftingData C' T M' X)

/-- **外形锁定** ✓：`RelativeLiftingProperty` 的**两合取**（含入 ✓／提升 ✓）逐字可取 ✓ ——
含入被吞或提升目标换回 `C` ✗ 即失败 ✓。 -/
theorem RelativeLiftingProperty.inclusion {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C C' : FStruct.{u, u} F r s t → Prop} (h : RelativeLiftingProperty C C') :
    ∀ X, C X → C' X :=
  h.1

/-- **外形锁定** ✓：提升支逐字可取 ✓（**目标在 `C'`** ✓）。 -/
theorem RelativeLiftingProperty.lifts {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C C' : FStruct.{u, u} F r s t → Prop} (h : RelativeLiftingProperty C C') :
    ∀ (T : Type u) [CommRing T] [Algebra F T] [IsLocalRing T]
      (M' : Type u) [AddCommGroup M'] [Module (IsLocalRing.ResidueField T) M']
      (X : LinearStructure (IsLocalRing.ResidueField T) M' r s t),
      C ⟨IsLocalRing.ResidueField T, M', X⟩ → Nonempty (LiftingData C' T M' X) :=
  h.2

end RelativeLifting

section RetractRational

/-- **源 `def3.1` 的见证数据** ✓（印 180--182 ✓ **逐字核**）：「Let `K\supseteq F` be fields. `K / F` is called
**retract rational** if and only if `K` is the **quotient field** of an `F` algebra domain `S\subseteq K`, such
that there are `F` algebra maps `\phi :S\to F[x_{1},\dots ,x_{n}](1 / w)` and
`\psi :F[x_{1},\dots ,x_{n}](1 / w)\to S` where `F[x_{1},\dots ,x_{n}](1 / w)` is a **localized polynomial
ring** and `\psi \circ \phi` is the **identity** on `S`」✓）。

**⚠ 为何打包** ✓：`S` 的实例（`CommRing`／`IsDomain`／`Algebra F`／`Algebra S K`／`IsFractionRing S K` ✓）
是**数据** ✓，而 `\exists` 不接受实例绑定 ✗（附四十六 ⑳ ✓）⟹ 打包 ✓。
**三家** ✓：`K` 是 `S` 的**商域** ✓（`IsFractionRing S K` ✓）／`S\subseteq K` ✓（`Algebra S K` ＋
`IsScalarTower F S K` ✓）／**收缩** `\psi\circ\phi = \mathrm{id}_S` ✓（**逐点**形 ✓）。 -/
structure RetractRationalData (F K : Type u) [Field F] [Field K] [Algebra F K] where
  S : Type u
  [commRing : CommRing S]
  [isDomain : IsDomain S]
  [algebra : Algebra F S]
  [algebraK : Algebra S K]
  [tower : IsScalarTower F S K]
  [isFractionRing : IsFractionRing S K]
  n : ℕ
  w : MvPolynomial (Fin n) F
  phi : S →ₐ[F] Localization.Away w
  psi : Localization.Away w →ₐ[F] S
  /-- 源：`\psi \circ \phi` is the **identity** on `S` ✓。 -/
  comp : ∀ s : S, psi (phi s) = s

/-- **源 `def3.1`：有理性收缩** ✓（`K/F` is called **retract rational** ✓）—— 即**见证数据非空** ✓。 -/
def RetractRational (F K : Type u) [Field F] [Field K] [Algebra F K] : Prop :=
  Nonempty (RetractRationalData F K)

/-- **源 `def3.2` 的见证数据** ✓（印 180--182 ✓ **逐字核**）：「Let `S`, `R` be `F` algebra domains, and let
`\phi :S\to R` be an `F` algebra map. We say `\phi` **factors rationally** if and only if there is a
**localized polynomial ring** `F[x_{1},\dots ,x_{n}](1 / w)`, a `0\neq r\in R`, and `F` algebra maps
`\psi :S\to F[x_{1},\dots ,x_{n}](1 / w)` and `\eta :F[x_{1},\dots ,x_{n}](1 / w)\to R(1 / r)` such that
`\phi = \eta \circ \psi`」✓）。

**⚠ `IsDomain` 取显式假设而非实例** ✓（源「Let `S`, `R` be `F` algebra **domains**」✓ 是**前提** ✓；
且在 `cor3.10(b)` 的语句里它以**蕴含**出现 ✓ ⟹ 若作实例则实例搜索失败 ✗，实测 ✓）。

**⚠ 末等的形状** ✓：`\phi = \eta\circ\psi` ✓ 中 `\phi` 的**陪域是 `R`** ✓ 而 `\eta\circ\psi` 的**陪域是 `R(1/r)`** ✓
⟹ 落为**逐点等式** `\eta (\psi s) = \mathrm{algebraMap}\,R\,R(1/r)\,(\phi s)` ✓（源式中的隐含强制 ✓，**登记** ✓）。 -/
structure FactorsRationallyData {F S R : Type u} [Field F] [CommRing S]
    [CommRing R] [Algebra F S] [Algebra F R] (hS : IsDomain S) (hR : IsDomain R)
    (φ : S →ₐ[F] R) where
  n : ℕ
  w : MvPolynomial (Fin n) F
  r : R
  hr : r ≠ 0
  psi : S →ₐ[F] Localization.Away w
  eta : Localization.Away w →ₐ[F] Localization.Away r
  /-- 源：`\phi = \eta \circ \psi` ✓（逐点形，含 `R\to R(1/r)` 的隐含强制 ✓）。 -/
  comp : ∀ s : S, eta (psi s) = algebraMap R (Localization.Away r) (φ s)

/-- **源 `def3.2`：有理分解** ✓（`\phi` **factors rationally** ✓）—— 即**见证数据非空** ✓。 -/
def FactorsRationally {F S R : Type u} [Field F] [CommRing S]
    [CommRing R] [Algebra F S] [Algebra F R] (hS : IsDomain S) (hR : IsDomain R)
    (φ : S →ₐ[F] R) : Prop :=
  Nonempty (FactorsRationallyData hS hR φ)


/-! ### 8.11 源 `cor3.10` 的**具名残余**（印 186 ✓ **本轮已逐支核**；证明在印 186 底 ✓） -/

/-- **源 `cor3.10(a)` 的具名陈述** ✓（印 186 ✓ 逐字核：「Let `\mathcal{C}` be an `F` class, `\mathcal{P} / R\in \mathcal{C}`
a **local projective object which is also densely representing**. If `K` is the **quotient field of `R`**, then
`\mathcal{C}` has the **lifting property** if and only if `K / F` is **retract rational**」✓）。

**⚠ 具名残余：本件不作证明** ✗（源自己说「(a) is a special case of (b)」✓，见 §8.11 末 ✓）。
**用件** ✓：`LocalProjective` ✓／`DenselyRepresenting` ✓／`HasLiftingProperty` ✓／`RetractRational` ✓
（`def3.1` ✓）；**⚠ `K` 是 `R` 的商域** ✓ 落为 `[IsFractionRing P.R K]` ✓ ＋ `[Algebra P.R K]` ✓
＋ `[IsScalarTower F P.R K]` ✓（**`S\subseteq K` 的库内形** ✓）。 -/
def Cor310aStatement {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  ∀ (P : FStruct.{u, u} F r s t), LocalProjective C P → DenselyRepresenting C P →
    ∀ (K : Type u) [Field K] [Algebra F K] [Algebra P.R K] [IsScalarTower F P.R K]
      [IsFractionRing P.R K],
      (HasLiftingProperty C ↔ RetractRational F K)

/-- **源 `cor3.10(b)` 的假设数据** ✓（印 186 ✓ 逐字核：「Suppose `R`**,** `S` are `F` algebra **affine
domains**, and `\phi :S\to R` is an `F` algebra map such that `\mathcal{M}\cong \mathcal{P}\otimes_{S}R`
**over `R`**」✓）。

**⚠ 为何打包** ✓：`\phi` 诱导的 `Algebra S R`（＋ `IsScalarTower F S R` ✓）是**实例** ✓，而 `\exists`／
语句里无法 `letI` ✓（附四十六 ⑳ ✓）⟹ 打包 ✓；`\phi` 本身与之一并记入 ✓（`phi_eq` ✓ 说明二者是**同一个映射** ✓）。 -/
structure Cor310bData {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (M P : FStruct.{u, u} F r s t) where
  [algebra : Algebra P.R M.R]
  [tower : IsScalarTower F P.R M.R]
  /-- 源：`\phi :S\to R` ✓。 -/
  φ : P.R →ₐ[F] M.R
  /-- `\phi` **就是**上面那个 `Algebra` 结构的映射 ✓（**登记** ✓：源的 `\phi` 是给定的 `F`-映射 ✓）。 -/
  phi_eq : ∀ x : P.R, φ x = algebraMap P.R M.R x
  /-- 源：`\mathcal{M}\cong \mathcal{P}\otimes_{S}R` **over `R`** ✓（同底环 `M.R` ✓ 的 `IsIso` ✓）。 -/
  iso : IsIso (P.str.baseChange (S := M.R)) M.str

/-- **源 `cor3.10(b)` 的具名陈述** ✓（印 186 ✓ 逐字核：「Let `\mathcal{C}\subseteq \mathcal{C}^{\prime}` be `F`
classes of the same type, let `\mathcal{M} / R\in \mathcal{C}` be a **densely representing object**, and let
`\mathcal{P} / S\in \mathcal{C}^{\prime}` be a **local projective object**. Suppose `R`, `S` are `F` algebra
**affine domains** … Then `(\mathcal{C},\mathcal{C}^{\prime})` has the **(relative) lifting property** if and only if
`\phi` **factors rationally**」✓）。

**⚠ 具名残余：本件不作证明** ✗。**四条前提逐一落** ✓（L39 ✓）：① **两类同型 ＋ 含入** ✓（由
`RelativeLiftingProperty` ✓ 自带 ✓）；② `\mathcal{M}/R` **稠密表示** ✓（`DenselyRepresenting C M` ✓）；
③ `\mathcal{P}/S` **局部投射** ✓（`LocalProjective C' P` ✓）；④ **`R,S` 仿射整环** ✓
（`Algebra.FiniteType` ✓ ＋ `IsDomain` ✓ —— **两支各写** ✓）。 -/
def Cor310bStatement {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C C' : FStruct.{u, u} F r s t → Prop) : Prop :=
  ∀ (M P : FStruct.{u, u} F r s t)
    (_hM : DenselyRepresenting C M) (_hP : LocalProjective C' P)
    (_haM : Algebra.FiniteType F M.R) (hdM : IsDomain M.R)
    (_haP : Algebra.FiniteType F P.R) (hdP : IsDomain P.R),
    ∀ D : Cor310bData M P,
      (RelativeLiftingProperty C C' ↔ FactorsRationally hdP hdM D.φ)

/-- **外形锁定 ①** ✓：`Cor310aStatement` 的**用点形**逐字可取 ✓（含 **`K` 是商域** ✓ 与
**提升 ⟺ 有理性收缩** ✓）。 -/
theorem Cor310aStatement.shape {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : Cor310aStatement C)
    (P : FStruct.{u, u} F r s t) (hP : LocalProjective C P) (hD : DenselyRepresenting C P)
    (K : Type u) [Field K] [Algebra F K] [Algebra P.R K] [IsScalarTower F P.R K]
    [IsFractionRing P.R K] :
    (HasLiftingProperty C ↔ RetractRational F K) :=
  h P hP hD K

/-- **外形锁定 ②** ✓：`Cor310bStatement` 的**四条前提 ＋ 等价**逐字可取 ✓。 -/
theorem Cor310bStatement.shape {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C C' : FStruct.{u, u} F r s t → Prop} (h : Cor310bStatement C C')
    (M P : FStruct.{u, u} F r s t)
    (hM : DenselyRepresenting C M) (hP : LocalProjective C' P)
    (haM : Algebra.FiniteType F M.R) (hdM : IsDomain M.R)
    (haP : Algebra.FiniteType F P.R) (hdP : IsDomain P.R) (D : Cor310bData M P) :
    (RelativeLiftingProperty C C' ↔ FactorsRationally hdP hdM D.φ) :=
  h M P hM hP haM hdM haP hdP D

/-- **源 `cor3.10` 证明的首句** ✓（印 186 底 ✓ 逐字：「As before, **(a) is a special case of (b)**」✓）——
**具名残余** ✗：**本件不作证明** ✓（其证明须 `RetractRational`／`FactorsRationally` 之间的桥 ✓，
即源印 181--182 的 `lem3.3`／`cor3.4`／`lem3.5` ✓ —— **本件未落** ✗，按 `∅-unchecked` ✓ 对待）。 -/
def Cor310Reduction {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  Cor310aStatement C


/-! ### 8.12 源 `prop1.1` 的**具名残余**（印 171 ✓ **逐字核**）—— M4 施工单末件 -/

/-- **「`\mathcal{C}` has a generic object」的口径** ✓（**登记** ✓）：源的**定义句**把主语写成
「a generic object `\mathcal{M}/R\in \mathcal{C}`」✓，而源的**陈述句**一律写「`\mathcal{C}` **has** a … object」✓
（`prop1.1`（a）（b）✓、印 171 ✓）⟹ **本件的约定** ✓：**三个性质谓词（`RepresentingObject` ✓／
`GenericObject` ✓／`DenselyRepresenting` ✓）不含 `C X`** ✓（它们是**性质** ✓），而**「类有…对象」在陈述层**
显式写出 `\exists X, C X \wedge (\cdot)` ✓。
**⚠ 在册的一处不一致** ✗：`LocalProjective` ✓ **含 `C P`** ✓ —— 依据是源在同一句里把它写成
「`\mathcal{P}\in \mathcal{C}` is a **local projective**」✓（**名词** ✓），且 `thm1.3`／`cor3.10` 随后以
「local projective **object**」**不加限定**地用 ✓（印 172 底／186 ✓）；**登记** ✓，**本轮不改** ✓。 -/
def HasGenericObject {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  ∃ X : FStruct.{u, u} F r s t, C X ∧ GenericObject C X

/-- 「`\mathcal{C}` has a densely representing object」✓（同上口径 ✓）。 -/
def HasDenselyRepresenting {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  ∃ X : FStruct.{u, u} F r s t, C X ∧ DenselyRepresenting C X

/-- **源 `prop1.1(a)` 的具名陈述** ✓（印 171 ✓ 逐字核：「**PROPOSITION 1.1.** Let `\mathcal{C}` be an `F`-class,
**(a)** if `\mathcal{C}` has a **generic object**, then `\mathcal{C}` has the **lifting property**」✓）——
**⚠ 具名残余：本件不作证明** ✗（源印 171 ✓ 明写「We will **omit the proof** because it is a trivial
generalization of the argument of `\cite{23}`, p. 275」✓ —— **源本身不给证明** ✓，**登记** ✓）。 -/
def Prop11aStatement {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  HasGenericObject C → HasLiftingProperty C

/-- **源 `prop1.1(b)` 的具名陈述** ✓（印 171 ✓ 逐字核：「**(b)** if `\mathcal{C}` has a **densely representing
object**, and `\mathcal{C}` has the **lifting property**, then `\mathcal{C}` has a **generic object**」✓）——
**⚠ 具名残余：本件不作证明** ✗（**两条前提各写** ✓：**有稠密表示对象** ✓ ＋ **有提升性质** ✓ —— L39 ✓）。 -/
def Prop11bStatement {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    (C : FStruct.{u, u} F r s t → Prop) : Prop :=
  HasDenselyRepresenting C → HasLiftingProperty C → HasGenericObject C

/-- **外形锁定 ①** ✓：`Prop11aStatement` 的**两段**（**有**一般对象 ✓／**得**提升性质 ✓）逐字可取 ✓。 -/
theorem Prop11aStatement.shape {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : Prop11aStatement C) :
    HasGenericObject C → HasLiftingProperty C :=
  h

/-- **外形锁定 ②** ✓：`Prop11bStatement` 的**三段**（**有**稠密表示 ✓／**有**提升性质 ✓／
**得**一般对象 ✓）逐字可取 ✓。 -/
theorem Prop11bStatement.shape {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : Prop11bStatement C) :
    HasDenselyRepresenting C → HasLiftingProperty C → HasGenericObject C :=
  h

/-- **外形锁定 ③** ✓：「has a generic object」＝ **存在类中的一般对象** ✓（`C X` **显式** ✓ —— 见 §8.12 口径 ✓）。 -/
theorem HasGenericObject.exists {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : HasGenericObject C) :
    ∃ X : FStruct.{u, u} F r s t, C X ∧ GenericObject C X :=
  h

/-- **外形锁定 ④** ✓：「has a densely representing object」＝ **存在类中的稠密表示对象** ✓。 -/
theorem HasDenselyRepresenting.exists {F : Type u} [Field F] {r : ℕ} {s t : Fin r → ℕ}
    {C : FStruct.{u, u} F r s t → Prop} (h : HasDenselyRepresenting C) :
    ∃ X : FStruct.{u, u} F r s t, C X ∧ DenselyRepresenting C X :=
  h

end RetractRational

end Projective

end BaseChange

/-! ## 9. 公理闸门 -/

#print axioms tensorProductRightModule
#print axioms tensorPowerBaseChange
#print axioms tensorPowerBaseChangeAuxZero
#print axioms tensorPowerBaseChangeAuxStep
#print axioms tensorPowerBaseChangeAux
#print axioms tensorPowerBaseChangeEquiv
#print axioms LinearStructure.baseChange
#print axioms LinearStructure.baseChange_typeLock
#print axioms LinearStructure.baseChange_nonempty
#print axioms FStruct.baseChange
#print axioms FStruct.baseChange_typeLock
#print axioms FStruct.baseChange_nonempty
#print axioms DescentData
#print axioms IsFClass
#print axioms IsFClass.iso_closed
#print axioms IsFClass.baseChange_closed
#print axioms IsFClass.descent
#print axioms isFClass_false
#print axioms LiftingData
#print axioms HasLiftingProperty
#print axioms HasLiftingProperty.lift
#print axioms hasLiftingProperty_false
#print axioms Realization
#print axioms RepresentingObject
#print axioms IsSpecialization
#print axioms GenericObject
#print axioms RepresentingObject.affine
#print axioms RepresentingObject.specializes
#print axioms GenericObject.isRepresenting
#print axioms representingObject_false_of_affine
#print axioms representingObject_probe
#print axioms DenselyRepresenting
#print axioms DenselyRepresenting.isRepresenting
#print axioms DenselyRepresenting.isDomain
#print axioms DenselyRepresenting.away
#print axioms denselyRepresenting_false_of
#print axioms Hom.IsFLinear
#print axioms Hom.IsSurjective
#print axioms Hom.IsLocal
#print axioms Hom.IsLocalSurjection
#print axioms ProjectiveObjectFor
#print axioms ProjectiveObjectIn
#print axioms LocalProjective
#print axioms ProjectiveObjectIn.projectiveFor
#print axioms ProjectiveObjectIn.mem
#print axioms LocalProjective.mem
#print axioms LocalProjective.lifts
#print axioms projectiveObjectFor_false
#print axioms RepresentingObject.isSpecialization
#print axioms Thm13aStatement
#print axioms Thm13aStatement.shape
#print axioms RelativeLiftingProperty
#print axioms RelativeLiftingProperty.inclusion
#print axioms RelativeLiftingProperty.lifts
#print axioms RetractRationalData
#print axioms RetractRational
#print axioms FactorsRationallyData
#print axioms FactorsRationally
#print axioms Cor310aStatement
#print axioms Cor310bData
#print axioms Cor310bStatement
#print axioms Cor310aStatement.shape
#print axioms Cor310bStatement.shape
#print axioms Cor310Reduction
#print axioms HasGenericObject
#print axioms HasDenselyRepresenting
#print axioms Prop11aStatement
#print axioms Prop11bStatement
#print axioms Prop11aStatement.shape
#print axioms Prop11bStatement.shape
#print axioms HasGenericObject.exists
#print axioms HasDenselyRepresenting.exists
#print axioms tensorPowerBaseChange_tmul
#print axioms tensorPowerBaseChange_nonempty
#print axioms fStructProbe
#print axioms FStruct_typeLock
#print axioms FStruct_typeLock_str
#print axioms FStruct_nonempty
#print axioms FStruct_nonempty_of
#print axioms tensorPower_zero_equiv
#print axioms LinearStructure_typeLock
#print axioms LinearStructure_type_typeLock
#print axioms linearStructureProbe
#print axioms linearStructureProbeZero
#print axioms linearStructureProbe_nonempty
#print axioms tensorPowerMapSL
#print axioms tensorPowerMapSL_tprod
#print axioms tensorPowerMapSL_id
#print axioms tensorPowerMapSL_comp
#print axioms Hom_typeLock
#print axioms Hom_typeLock_psi
#print axioms Hom.id
#print axioms Hom.comp
#print axioms Hom.comp_id
#print axioms Hom.id_comp
#print axioms Hom.comp_assoc
#print axioms Hom_nonempty
#print axioms Hom_probeGeneral
#print axioms IsIso.toHom
#print axioms IsIso.refl
#print axioms IsIso_typeLock
#print axioms IsIso_nonempty
#print axioms tensorPowerMapSL_symm_comp
#print axioms tensorPowerMapSL_comp_symm
#print axioms IsIso.symm
#print axioms IsIso_symm_nonempty

end ABGV52

