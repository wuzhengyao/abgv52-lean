/-
  ABGV-5.2 · B 档 · M4 —— **Saltman 1984 §1 的「线性结构」语言**（第 115–123 轮；**新文件**）

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
  | `FStruct` ✓ ＋ 两把类型锁 ✓ ＋ 三个探针 ✓ | 源的 `F` 结构 ✓：「An `F` structure is a linear structure `M/R` such that **`F ⊂ R`**」✓（印版 170 ✓）—— 落为**打包**结构 ✓（`R`／`M` 及实例随 `str` 打包 ✓） | 第 3 件（**部分** ✓） |

  **施工单余项** ✗（本件**不**触碰 ✓，**不作声称** ✓）：
  ① 第 3 件的**其余部分** ✗：**`FClass`**（源四条：同类型 ✓／**同构封闭** ✓／**基变换封闭** ✓／
  **下降／有限生成** ✓）**未落** ✗。**⚠ 缺口已处置** ✓（§8 ✓）：次因子取向的 `S`-模结构**已**沿 `comm`
  搬运 ✓（`AddEquiv.module` ＋ `AddEquiv.linearEquiv` ✓），源的 `f_i ⊗ 1` **已落** ✓（**保源序** ✓）。
  **⚠ 上述 iso 与基变换已落** ✓（§8.1／§8.2／§8.3 ✓）—— **`LinearStructure.baseChange`** ✓ ＋
  **`FStruct.baseChange`** ✓ 均已编译 ✓（§8.2／§8.3 ✓）；
  **⚠ 该 iso 的生成元语义核未过** ✗（卡点逐字见 §8.1 ✓）⟹ **`baseChange` 一族一并按 `∅-unchecked`** ✓ 对待；
  **⚠ 第 3 件的其余** ✗：**`FClass`**（源四条 ✓）**未落** ✗；
  ② 第 **4–9** 件（`HasLiftingProperty` → `RepresentingObject`／`GenericObject`／`DenselyRepresenting` →
  `ProjectiveObjectForClass`／`LocalProjective` → `Specialization` → `cor3.10(b)` ⟹ `cor3.10(a)`
  → `prop1.1(a)` 具名残余）**均未落** ✗ ⟹ **`cor3.10(a)` 仍未形式化** ✗。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

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

