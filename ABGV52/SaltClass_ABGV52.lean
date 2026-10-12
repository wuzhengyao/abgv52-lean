/-
  ABGV-5.2 · B 档 · M4 —— **Saltman 1984 §1 的「线性结构」语言**（第 115 轮；**新文件**）

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

  ## 本件内容（§77.2 施工单**第 1 件** ✓）

  | 件 | 内容 | 读法 |
  |---|---|---|
  | `LinearStructure` ✓ | 源 §1 的线性结构：`R, M` ＋ `r : ℕ` ＋ `s t : Fin r → ℕ` ＋ `f : ∀ i, TensorPower R (s i) M →ₗ[R] TensorPower R (t i) M` | 逐字 ✓ |
  | `LinearStructure.type` ✓ | 源「`type` ＝ 序列 `(s₁,t₁),…,(s_r,t_r)`」 | 逐字 ✓ |
  | `tensorPower_zero_equiv` ✓ | 源「`M^{(0)} = R`」 | **同构** ✓（非定义相等 ✗，**偏离登记** ✓） |
  | 类型锁定 ✓ ＋ L1 探针 ✓ | 构造子外形锁 ✓／`type` 锁 ✓ ＋ 实例探针 ✓ | 见 §3 |

  **施工单余项** ✗（本件**不**触碰 ✓，**不作声称** ✓）：第 2–9 件
  （`Hom`／`IsIso` → `FStruct`／`FClass` → `HasLiftingProperty` → `RepresentingObject`／
  `DenselyRepresenting` → `ProjectiveObjectForClass`／`LocalProjective` → `Specialization`
  → `cor3.10(b)` ⟹ `cor3.10(a)` → `prop1.1(a)` 具名残余）**均未落** ✗。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import Mathlib.LinearAlgebra.TensorPower.Basic

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

/-! ## 4. 公理闸门 -/

#print axioms tensorPower_zero_equiv
#print axioms LinearStructure_typeLock
#print axioms LinearStructure_type_typeLock
#print axioms linearStructureProbe
#print axioms linearStructureProbeZero
#print axioms linearStructureProbe_nonempty

end ABGV52
