/-
  Procesi —— **H2 的终点件**：把 H2（**带具体中心** `Z_{S_9}(F,9)`）压成**一条**具名同构

  **H2（ABGV 5.2）**：`Z_H(F,9) ≅ F((M ⊕ U)|_H)^H`，`H = C_3 × C_3 ⊆ S_9`。
  按 `Statement.lean` 的口径（`ProcesiS9Hyp`），取 `S_9` 形：`Z ≅ ↥(invariantsField F)`。

  **本件做两件事**：

  1. **把 `Z` 换成具体对象** `↥(ZCanon F 2 9 D)`——即 `Z(F,2,9) = Z_{S_9}(F,9)`
     （`Saltman 1999` 的 `Z(F,n,r)`，`n = 9`、`r = 2`），它由 `GenericDivisionData` 的
     `centK`（`cor:14.8(a)`：中心元是纯量矩阵）生成。此前 H2 的 `Z` 是**自由参数**；
     本件把它锁到具体中心上。
  2. **机检**：`ProcesiS9Hyp F ↥(ZCanon F 2 9 D) ↔ ZEqNFixed F D`，其中

     ```
     ZEqNFixed F D := Nonempty (↥(ZCanon F 2 9 D) ≃ₐ[F] ↥(NFixedAlg F))
     ```

     而 `↥(NFixedAlg F)` 就是 `K'^N = {α | T-固定 ∧ S_n-固定}`（`SaltmanT.lean` §20–§36，
     已机检）。故 **H2 的全部剩余数学内容 ⟺ `Z(F,2,9) ≅ K'^N`**，
     即 Saltman 1999 `prop:14.19` 的 `Z` 半。

  **为何只需要 (B) 的 `Z` 半**：`prop:14.19` 的另一半（`UD = M_n(K')^N`）在源文里是
  `Z = K'^N` 的**手段**（取中心），而 H2 只要 `Z` 那一半。故本件不需 `(A)`——
  `(A)` 是与 `(B)` **并列**的另一条到达 `Z` 的路（`Z = K^{PGL}`，见 `GenericInv.lean` §60–§62）。

  **射程（勿夸大）**：`ZEqNFixed` **未证**——它正是 `(B)` 的 `Z` 半，其证明需 `S'`-世界
  与 `lem:14.21／14.22` 的识别（见 `GenericInv.lean` §61 的"（B）形式化口径"）。
  本件只保证：**H2 除此之外没有别的内容**。
-/

import Procesi.SaltmanT
import Procesi.GenericInv
import Procesi.FFTRing
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.TensorProduct.Free

namespace Procesi

/-! ## §0 当前状态（R774–R779 更新；本段与下文分节射程注记的关系）

下文各节末尾的「射程」注记是**写作当时**的记录，其中两条**已过时**：

* 「**H2 仍不是定理**」——**已不成立**：H2 于 R774 在 `UDKScalarMem.h2_unconditional`
  中**无条件**机检（具名假设 `ScalarMemZHypK'` 旁路第 1–4 步全部机检）；
* 「`ZEqNFixed` —— **未证**」——**已不成立**：由 `h2_unconditional` ＋
  `ProcesiS9Hyp F ↥(ZCanon F 2 9 D) ↔ ZEqNFixed F D`（本文件 `:69`）即得。

其**非空洞性**（`Nonempty (GenericDivisionData F 2 9)`，＝ Saltman `cor:14.8(a)`）于 R779 在
`Nonvacuous.nonempty_genericDivisionData_two_nine` ＋ `h2_unconditional_nonvacuous` 机检，
关键引理 `adjoin_genericMatrix_map_eq_top`（`R·K = M_n(K)`）在 `Nonvacuous` 中。

**仍未证**（均**不在** H2 关键路径）：Z 半（`sprNFixedField ≤ sprCenterImageField`）、
`M_n(K')^N ⊆ UDK'`（`prop:14.19` 后半）、`UDKTensorHypK'`。

自本段起，下文凡写「**H2 见文件头「当前状态」**」处，均指回本段。
-/

/-! ## §1 **(B) 的 `Z` 半：具名** -/

/-- ★★★★★ **(B) 的 `Z` 半，具名**：`Z(F,2,9) ≅ K'^N`。

源文 Saltman 1999 `prop:14.19`（`raw/Saltman1999ch14.tex:369`，逐字）：

> "`UD(F,n,r) = M_n(K')^N` and `Z(F,n,r) = K'^N`."

`K'^N = {α | T-固定 ∧ S_n-固定}` 在本工作区已机检为 `↥(NFixedAlg F)`（`SaltmanT.lean`）。

**为何单独具名**：H2 只消费 `Z` 那一半（另一半 `UD = M_n(K')^N` 是源文证 `Z` 的手段）。
故本谓词**恰好**是 H2 的剩余内容（`procesiS9Hyp_iff_ZEqNFixed` 机检）。
**L1（非空洞性）**：两端都非空——`↥(ZCanon F 2 9 D)` 与 `↥(NFixedAlg F)` 都是域，
`Nonempty (≃ₐ[F])` 的类型在 `NFixedAlg` 侧有见证（`nFixedAlgEquiv` 的源端），
故本谓词**不是**空类上的真。 -/
def ZEqNFixed (F : Type) [Field F] [CharZero F] (D : GenericDivisionData F 2 9) : Prop :=
  Nonempty (↥(ZCanon F 2 9 D) ≃ₐ[F] ↥(NFixedAlg F))

#print axioms ZEqNFixed

/-- ★★★★★ **H2（带具体中心）⟺ `ZEqNFixed`** —— 这是 H2 的**精确剩余内容**。

**证明**：`↥(NFixedAlg F) ≃ₐ[F] ↥(invariantsField F)` 是 `nFixedAlgEquiv`（`SaltmanT.lean` §36，
已机检），故两个 `Nonempty (≃ₐ[F])` 命题等价（正向复合、反向复合其逆）。
**读法**：这条 `↔` 把 H2 的**自由参数 `Z`** 换成**具体中心**，并把剩余内容收成**一条同构**。
**射程**：`↔` 是逻辑等价，**不是**对 `ZEqNFixed` 的证明。 -/
theorem procesiS9Hyp_iff_ZEqNFixed (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) ↔ ZEqNFixed F D := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (nFixedAlgEquiv F).symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (nFixedAlgEquiv F)⟩

#print axioms procesiS9Hyp_iff_ZEqNFixed

/-- ★★★★★ **H2（带具体中心），以 `ZEqNFixed` 为唯一输入**。

即：`Z(F,2,9) ≅ K'^N` ⟹ `Z_H(F,9) ≅ F((M ⊕ U)|_H)^H`（`S_9` 形口径）。
**与 `h2_of_saltmanCenterEqNFixed` 的关系**：那一条的 `Z` 是自由参数；本条把它锁到
`↥(ZCanon F 2 9 D)`，于是"剩下要证什么"没有歧义。
**射程**：本条是**逻辑传递**，不是对 `ZEqNFixed` 的证明。 -/
theorem h2_of_ZEqNFixed (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) (h : ZEqNFixed F D) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  (procesiS9Hyp_iff_ZEqNFixed F D).mpr h

#print axioms h2_of_ZEqNFixed

/-! ## §2 **`V3'` 第一块：`S'` 的 90 个变元 ↔ Saltman `M_2'` 的 90 个基元**

终局输入 (iii)（`V3'`）要把 `(B)` 层的 `SprField F 2 9`（`K' = Frac(S')`）与 `(C)` 层的
`EM.latticeFunctionField F Mprime`（`F(M_2')`）识别，并使两边的 `N = T ⋊ S_n` 作用对应。

**源文给了识别本身**（`raw/Saltman1999ch14.tex:392`，逐字）：

> "Set `M_r' = ⊕_{k=2}^r B ⊕ Z[G/H]`. We set `u_i` to be the usual basis of `Z[G/H]`. …
>  By identifying `e(u_i)` with `x_{ii}`, `e(u_{ijk})` with `y_{ijk}` we can identify `K'`
>  with `F(M_r')`. Furthermore, the `i,i` entry of `P_σ X P_σ^{-1}` is `x_{σ(i)σ(i)}` and
>  the `i,j` entry of `P_σ Y_k P_σ^{-1}` is `y_{σ(i)σ(j)k}`. **It follows that the
>  identification of `K'` with `F(M_r')` is `S_n` invariant.**"

`n = 9`、`r = 2` 时两边都是 **90 个变元／基元**：`S'` 侧 `x_{ii}`（9）＋ `y_{ij1}`（81）；
`M_2'` 侧 `u_i`（9）＋ `u_{ij1}`（81）。本节机检该识别的**索引层**与 **`S_n`-等变性**。

| 件 | 内容 |
|---|---|
| `sprKUnit` | `{k : Fin 2 // k.val ≠ 0}` 是单点（`r = 2` 时只有一个非零 `k`） |
| ★★★★★ `sprYEquiv` | `y`-索引（81）↔ `Ω × Ω`（81）：`(i,j,·) ↦ (i,j)` |
| ★★★★★ `sprIdxEquivIdx` | **`SprIdx 2 9 ≃ Idx`**（90 ↔ 90），即源文的 `e(u_i) ↔ x_ii`、`e(u_ijk) ↔ y_ijk` |
| `sprIdxEquivIdx_inl`／`_inr` | 两条计算律（`rfl`） |
| ★★★★★ `sprPolyEquiv` | `S' ≅ F[M_2']` 的**多项式环**层（`MvPolynomial.renameEquiv`） |
| ★★★★★ `sprFieldEquiv` | **`K' ≅ Frac F[Idx]`**（分式域层；到 `F(M_2')` 还差 Laurent 一步） |
| `sprIdx_card` | 计数核对：`SprIdx 2 9` 共 90 个 |
| ★★★★★ `sprPermIdx` ＋ `_inl`／`_inr` | **`S_n` 在 `S'` 变元上的作用**（`x_ii ↦ x_{σi,σi}`、`y_ijk ↦ y_{σi,σj,k}`） |
| ★★★★★ `sprIdxEquivIdx_perm` | **`sprIdxEquivIdx` 是 `S_n`-等变的**（源文"it follows that the identification is `S_n` invariant"的索引层形态） |

**★ 为什么这解决了 `V3'` 的"作用对应"的一半**：`sprIdxEquivIdx_perm` 说
`sprPermIdx`（`S'` 侧）与 `idxPerm`（`M_2'` 侧）在基索引上**逐点相同**。
`T` 那一半是权（`wtM`／`sprDiagHom`），须经 `f'(u_{ij}) = u_i - u_j` 对齐，**下一轮做**。

**射程（勿夸大）**：本节只给**索引层 ＋ 多项式环层 ＋ `S_n`-等变性**。
`Frac F[Idx] ≅ F(M_2')` 的 **Laurent 一步未做**（`F[M_2']` 是 Laurent 环，
`MvPolynomial` 是多项式环；两者的分式域相同但本仓尚未机检）。
`T` 作用的对应、`sprFieldNFixed ↔ (TFixed ∧ SFixed)`、`V3'` 的 `AlgEquiv` 本身
—— **全部未建**。`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprIdxModel

set_option linter.style.haveILetI false

/-- `{k : Fin 2 // k.val ≠ 0}` 是单点（唯一元是 `1`）—— `r = 2` 时 `S'` 只有一个 `y`-族。 -/
def sprKUnit : {k : Fin 2 // k.val ≠ 0} ≃ PUnit.{0} where
  toFun _ := PUnit.unit
  invFun _ := ⟨1, by norm_num⟩
  left_inv x := by
    refine Subtype.ext ?_
    have h1 : (x : Fin 2).val ≠ 0 := x.2
    have h2 : (x : Fin 2).val < 2 := x.1.isLt
    have h3 : (x : Fin 2).val = 1 := by omega
    exact Fin.ext h3.symm
  right_inv x := by cases x; rfl

#print axioms sprKUnit

/-- ★★★★★ `y`-变量索引（81 元）与 `Ω × Ω`（81 元）的一一对应：`(i,j,·) ↦ (i,j)`。 -/
def sprYEquiv : (Fin 9 × Fin 9 × {k : Fin 2 // k.val ≠ 0}) ≃ (Fin 9 × Fin 9) where
  toFun p := (p.1, p.2.1)
  invFun q := (q.1, q.2, ⟨1, by norm_num⟩)
  left_inv p := by
    obtain ⟨i, j, k⟩ := p
    refine Prod.ext rfl (Prod.ext rfl ?_)
    refine Subtype.ext ?_
    have h1 : (k : Fin 2).val ≠ 0 := k.2
    have h2 : (k : Fin 2).val < 2 := k.1.isLt
    have h3 : (k : Fin 2).val = 1 := by omega
    exact Fin.ext h3.symm
  right_inv q := by
    obtain ⟨i, j⟩ := q
    rfl

#print axioms sprYEquiv

/-- ★★★★★ **`S'` 的 90 个变元 ↔ Saltman `M_2'` 的 90 个基元**。

源文 `:392` 逐字："By identifying `e(u_i)` with `x_{ii}`, `e(u_{ijk})` with `y_{ijk}`
we can identify `K'` with `F(M_r')`." 本定义正是该句的**索引层内容**：
`x_{ii} ↦ u_i`（`Sum.inl` → `Sum.inr`）、`y_{ij1} ↦ u_{ij1}`（`Sum.inr` → `Sum.inl`）。 -/
def sprIdxEquivIdx : SprIdx 2 9 ≃ Idx :=
  (Equiv.sumComm (Fin 9) (Fin 9 × Fin 9 × {k : Fin 2 // k.val ≠ 0})).trans
    (Equiv.sumCongr sprYEquiv (Equiv.refl (Fin 9)))

#print axioms sprIdxEquivIdx

/-- 计算律：`x_{ii} ↦ u_i`。 -/
lemma sprIdxEquivIdx_inl (i : Fin 9) : sprIdxEquivIdx (Sum.inl i) = Sum.inr i := rfl

#print axioms sprIdxEquivIdx_inl

/-- 计算律：`y_{ijk} ↦ u_{ijk}`（`r = 2` 时 `k` 唯一非零，故被抹去）。 -/
lemma sprIdxEquivIdx_inr (i j : Fin 9) (k : {k : Fin 2 // k.val ≠ 0}) :
    sprIdxEquivIdx (Sum.inr (i, j, k)) = Sum.inl (i, j) := rfl

#print axioms sprIdxEquivIdx_inr

/-- ★★★★★ **两个多项式模型是同一个**：`S' = F[x_{ii}, y_{ijk}] ≅ F[M_2']` 的变元层。 -/
noncomputable def sprPolyEquiv (F : Type) [Field F] :
    MvPolynomial (SprIdx 2 9) F ≃ₐ[F] MvPolynomial Idx F :=
  MvPolynomial.renameEquiv F sprIdxEquivIdx

#print axioms sprPolyEquiv

/-- ★★★★★ **`K' ≅ Frac F[M_2']`**（分式域层）。

**还差一步**：`F[M_2']` 在 `(C)` 层是 **Laurent** 环 `F[Idx^{±1}]`，而 `MvPolynomial Idx F`
是多项式环；两者分式域相同，但本仓尚未机检该等同（下一轮）。 -/
noncomputable def sprFieldEquiv (F : Type) [Field F] :
    SprField F 2 9 ≃ₐ[F] FractionRing (MvPolynomial Idx F) :=
  IsFractionRing.algEquivOfAlgEquiv (sprPolyEquiv F)

#print axioms sprFieldEquiv

/-- 计数核对：`S'` 共 90 个变元（`n + n²(r-1)`，`n = 9`、`r = 2`）。 -/
theorem sprIdx_card : Fintype.card (SprIdx 2 9) = 90 := by
  simp [SprIdx, YIdx]

#print axioms sprIdx_card

/-- ★★★★★ **`S_n` 在 `S'` 的变元索引上的作用**：`x_ii ↦ x_{σi,σi}`、`y_ijk ↦ y_{σi,σj,k}`
（源文 `:392` 的 "`i,i` entry of `P_σ X P_σ^{-1}` is `x_{σ(i)σ(i)}`…"）。 -/
def sprPermIdx (σ : Equiv.Perm (Fin 9)) : SprIdx 2 9 ≃ SprIdx 2 9 :=
  Equiv.sumCongr σ (Equiv.prodCongr σ (Equiv.prodCongr σ (Equiv.refl _)))

#print axioms sprPermIdx

/-- 计算律：`x_{ii} ↦ x_{σi,σi}`。 -/
lemma sprPermIdx_inl (σ : Equiv.Perm (Fin 9)) (i : Fin 9) :
    sprPermIdx σ (Sum.inl i) = Sum.inl (σ i) := rfl

#print axioms sprPermIdx_inl

/-- 计算律：`y_{ijk} ↦ y_{σi,σj,k}`。 -/
lemma sprPermIdx_inr (σ : Equiv.Perm (Fin 9)) (i j : Fin 9)
    (k : {k : Fin 2 // k.val ≠ 0}) :
    sprPermIdx σ (Sum.inr (i, j, k)) = Sum.inr (σ i, σ j, k) := rfl

#print axioms sprPermIdx_inr

/-- ★★★★★ **识别是 `S_n`-等变的** —— 源文 `:392` 的
"It follows that the identification of `K'` with `F(M_r')` is `S_n` invariant" 的索引层形态：
`sprPermIdx`（`S'` 侧）与 `idxPerm`（`M_2'` 侧）在基索引上**逐点相同**。 -/
theorem sprIdxEquivIdx_perm (σ : Equiv.Perm (Fin 9)) (i : SprIdx 2 9) :
    sprIdxEquivIdx (sprPermIdx σ i) = idxPerm σ (sprIdxEquivIdx i) := by
  rcases i with i | ijk
  · rw [sprPermIdx_inl, sprIdxEquivIdx_inl]
    exact (idxPerm_inr σ i).symm
  · obtain ⟨i, j, k⟩ := ijk
    rw [sprPermIdx_inr, sprIdxEquivIdx_inr]
    exact (idxPerm_inl σ (i, j)).symm

#print axioms sprIdxEquivIdx_perm

end SprIdxModel

/-! ## §3 **`V3'` 第二块：`K' ≅ F(M_2')`（`F`-代数同构）** —— Laurent 一步与落点

§2 把 `S'` 的 90 个变元接到 `M_2'` 的 90 个基元上（索引层），并给出
`K' ≅ Frac F[Idx]`。本节补上**最后一步**：`Frac F[Idx] ≅ F(M_2')`。

**★ 关键（R207 检索纪律，本轮最大收益）**：这一步**早已机检**，在外部 ABGV52 包里：
`EM.freeSubst_isFractionRing (F) (n) : IsFractionRing (MvPolynomial (Fin n) F)
(EM.latticeFunctionField F (Fin n → ℤ))`（`packages/abgv52-verification/lean/ABGV52/D2_ABGV52.lean`）。
它的证明正是"**清分母**"：把每个 Laurent 单项式写成 `X^{正部}/X^{负部}`，
再乘足够大的 `x^N` 把分母提成多项式（源文 `prop:14.14` 的同一套"用 `F` 无限"的论证）。
⟹ 本仓**不需要**重做 Laurent 一步，只需把它沿指标重标号搬到 `Mprime`。

| 件 | 内容 |
|---|---|
| `sprIdxEquivFin` | `SprIdx 2 9 ≃ Fin 90`（经 `sprIdx_card`） |
| `sprPolyEquivFin`／`sprFracEquivFin` | `S' ≅ F[X_1,…,X_90]` 的**多项式环／分式域**层 |
| ★★★★★ `sprFracToLattice` | **`Frac F[X_1,…,X_90] ≅ F(ℤ^90)`**（`IsLocalization.algEquiv` ＋ D2 的 `IsFractionRing`） |
| ★★★★★ `sprFieldLattice` | **`K' ≅ F(ℤ^90)`** |
| ★★★ `latticeFieldCongr`／`latticeFieldCongrAlg` | 格函数域的**搬运**：`M ≃+ N` ⟹ `F(M) ≃ₐ[F] F(N)` |
| `idxEquivFin`／`piAddEquiv` | `Idx ≃ Fin 90`／`(Idx → ℤ) ≃+ (Fin 90 → ℤ)` |
| ★★★★★★ `sprFieldMprimeAlg` | **`K' ≅ F(M_2')`（`F`-代数同构）** —— 源文 `:392` 的 "identify `K'` with `F(M_r')`" |

**为什么 `sprFieldMprimeAlg` 是 `V3'` 的主梁**：`V3'` 要的两侧
`↥(sprNFixedAlg F 2 9)` 与 `↥(NFixedAlg F)` 分别是 `SprField F 2 9` 与
`EM.latticeFunctionField F Mprime` 的**同一类**固定点（`T`-固定 ∧ `S_n`-固定）。
有了域同构，剩下的只是"**同构把两边的 `N`-作用对上**"。

**工艺（2 条，本轮实测）**：
* **R219 `IsFractionRing` 是命题不是实例**：`freeSubst_isFractionRing` 是 `theorem`，
  `IsLocalization.algEquiv` 需要 `[IsLocalization …]` **实例**，直接写报
  "failed to synthesize instance" —— 须 `haveI : IsFractionRing … := EM.freeSubst_isFractionRing F 90`。
* **R220 `rw` 不会展开 `noncomputable def`**：把 `latticeFieldCongr` 写进 `AlgEquiv.ofRingEquiv`
  后，`rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]` 报"找不到落点"（形似引理不适用，
  实为定义未展开）。**正解**：在 `f :=` 位置**直接写展开式**，不要先打包成 `def` 再引用；
  或先 `rw [latticeFieldCongr]`。

**射程（勿夸大）**：本节的域同构**只到域层**。⚠ `sprIdxEquivFin` 取自
`Fintype.equivFinOfCardEq`（**任意枚举**），故 `sprFieldMprimeAlg` **不保证**与 `N`-作用相容。
`T`／`S_n` 的**作用对应未证**；`sprFieldNFixed ↔ (TFixed ∧ SFixed)` **未建**；
`V3'` 的 `AlgEquiv` 本身 **未建**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprFieldMprime

set_option linter.style.haveILetI false

open ABGV52

/-- `SprIdx 2 9 ≃ Fin 90`（经 `sprIdx_card`；**任意枚举**，只用于域层识别）。 -/
noncomputable def sprIdxEquivFin : SprIdx 2 9 ≃ Fin 90 :=
  Fintype.equivFinOfCardEq sprIdx_card

#print axioms sprIdxEquivFin

/-- `S' ≅ F[X_1,…,X_90]`（多项式环层）。 -/
noncomputable def sprPolyEquivFin (F : Type) [Field F] :
    MvPolynomial (SprIdx 2 9) F ≃ₐ[F] MvPolynomial (Fin 90) F :=
  MvPolynomial.renameEquiv F sprIdxEquivFin

#print axioms sprPolyEquivFin

/-- `K' ≅ Frac F[X_1,…,X_90]`（分式域层）。 -/
noncomputable def sprFracEquivFin (F : Type) [Field F] :
    SprField F 2 9 ≃ₐ[F] FractionRing (MvPolynomial (Fin 90) F) :=
  IsFractionRing.algEquivOfAlgEquiv (sprPolyEquivFin F)

#print axioms sprFracEquivFin

/-- ★★★★★ **`Frac F[X_1,…,X_90] ≅ F(ℤ^90)`** —— Laurent 一步的搬运。

用 `EM.freeSubst_isFractionRing`（外部 ABGV52 包 `D2_ABGV52.lean` 已机检）——它的证明正是
"清分母"：每个 Laurent 单项式写成 `X^{正部}/X^{负部}`，乘足够大的 `x^N` 提成多项式。 -/
noncomputable def sprFracToLattice (F : Type) [Field F] :
    FractionRing (MvPolynomial (Fin 90) F) ≃ₐ[F] EM.latticeFunctionField F (Fin 90 → ℤ) := by
  haveI : IsFractionRing (MvPolynomial (Fin 90) F)
      (EM.latticeFunctionField F (Fin 90 → ℤ)) := EM.freeSubst_isFractionRing F 90
  exact (IsLocalization.algEquiv (nonZeroDivisors (MvPolynomial (Fin 90) F))
    (FractionRing (MvPolynomial (Fin 90) F))
    (EM.latticeFunctionField F (Fin 90 → ℤ))).restrictScalars F

#print axioms sprFracToLattice

/-- ★★★★★ **`K' ≅ F(ℤ^90)`** —— 两个 90 变元的有理函数域是同一个。 -/
noncomputable def sprFieldLattice (F : Type) [Field F] :
    SprField F 2 9 ≃ₐ[F] EM.latticeFunctionField F (Fin 90 → ℤ) :=
  (sprFracEquivFin F).trans (sprFracToLattice F)

#print axioms sprFieldLattice

/-- ★★★ 格函数域的**环层搬运**：`M ≃+ N` ⟹ `F(M) ≃+* F(N)`。 -/
noncomputable def latticeFieldCongr (F : Type) [Field F] {M N : Type} [AddCommGroup M]
    [AddCommGroup N] (e : M ≃+ N) :
    EM.latticeFunctionField F M ≃+* EM.latticeFunctionField F N :=
  IsFractionRing.ringEquivOfRingEquiv
    (MonoidAlgebra.mapDomainRingEquiv F e.toMultiplicative)

#print axioms latticeFieldCongr

/-- ★★★ 格函数域的**`F`-代数搬运**：`M ≃+ N` ⟹ `F(M) ≃ₐ[F] F(N)`。 -/
noncomputable def latticeFieldCongrAlg (F : Type) [Field F] {M N : Type} [AddCommGroup M]
    [AddCommGroup N] (e : M ≃+ N) :
    EM.latticeFunctionField F M ≃ₐ[F] EM.latticeFunctionField F N :=
  AlgEquiv.ofRingEquiv
    (f := IsFractionRing.ringEquivOfRingEquiv
      (MonoidAlgebra.mapDomainRingEquiv F e.toMultiplicative)) (fun x => by
    rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F M) (EM.latticeFunctionField F M),
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have h1 : (MonoidAlgebra.mapDomainRingEquiv F e.toMultiplicative)
        (algebraMap F (EM.latticeAlgebra F M) x) = algebraMap F (EM.latticeAlgebra F N) x := by
      simp [MonoidAlgebra.coe_algebraMap]
    rw [h1, IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F N)
      (EM.latticeFunctionField F N)])

#print axioms latticeFieldCongrAlg

/-- `Idx ≃ Fin 90`。 -/
noncomputable def idxEquivFin : Idx ≃ Fin 90 := sprIdxEquivIdx.symm.trans sprIdxEquivFin

#print axioms idxEquivFin

/-- `(Idx → ℤ) ≃+ (Fin 90 → ℤ)`（换指标）。 -/
noncomputable def piAddEquiv : (Idx → ℤ) ≃+ (Fin 90 → ℤ) where
  toFun f := fun i => f (idxEquivFin.symm i)
  invFun g := fun i => g (idxEquivFin i)
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp
  map_add' f g := rfl

#print axioms piAddEquiv

/-- ★★★★★★ **`K' ≅ F(M_2')`（`F`-代数同构）** —— 源文 `:392` 的
"By identifying `e(u_i)` with `x_{ii}`, `e(u_{ijk})` with `y_{ijk}` we can identify `K'`
with `F(M_r')`"，本仓的完整形态。

**⚠ 射程**：`sprIdxEquivFin` 是**任意枚举**，故本同构**不保证**与 `N`-作用相容
（作用对应是下一轮的事）。 -/
noncomputable def sprFieldMprimeAlg (F : Type) [Field F] :
    SprField F 2 9 ≃ₐ[F] EM.latticeFunctionField F Mprime :=
  (sprFieldLattice F).trans
    (latticeFieldCongrAlg F (piAddEquiv.symm.trans mprimeEquivFun.toAddEquiv.symm))

#print axioms sprFieldMprimeAlg

end SprFieldMprime

/-! ## §4 **`V3'` 第三块：`T` 侧权字典** —— 「两边作用对应」的定量一半

§2 给了 `S_n` 侧的作用对应（`sprIdxEquivIdx_perm`）。本节给 **`T` 侧**：
`T = (Fin 9 → Fˣ)` 在两边的特征值必须**逐基元相同**。

**源文给的是同一张表**（`raw/Saltman1999ch14.tex:392` 与 `:396`）：

> "the `i,j` entry of `B^{-1}Y_kB` is `b_i^{-1}b_j y_{ijk}`" （`lem:14.20` 的证明，逐字）
> "if `m ∈ M_r'` and `f'(m) = Σ_i c(i)u_i` then `φ_B(e(m)) = (∏_i b_i^{-c(i)})e(m)`"

⟹ 两边都是 `b_i / b_j`（`Fˣ` 里 `b_i * b_j⁻¹`）。本节把这个一致机检。

| 件 | 内容 |
|---|---|
| `wt_single_one` | `wt b (e(u_i)) = b i` |
| `wt_neg` | `wt b (−z) = (wt b z)⁻¹` |
| ★★★★★ `wtM_mprimeBasis_inl` | **`wtM b (e(u_ij)) = b_i · b_j⁻¹`**（经 `fPrime_mprimeBasis_inl`） |
| ★★★★★ `wtM_mprimeBasis_inr` | **`wtM b (e(u_i)) = 1`** |
| ★★★★★ `sprIdxWeight` ＋ `_inl`／`_inr` | **`S'` 变元的权**（`x_ii ↦ 1`、`y_ijk ↦ b_i · b_j⁻¹`） |
| ★★★★★ `sprDiagHom_X_eq_weight` | **`sprDiagHom b (X v) = sprIdxWeight b v · X v`**（统一的特征向量式） |

**⟹ 与 §2 合起来**：`N = T ⋊ S_n` 的两侧作用在**基元层**已对齐——
`S_n` 侧是 `sprIdxEquivIdx_perm`（置换指标），`T` 侧是本节的权（对角特征值）。

**工艺（1 条，本轮实测）**：
* **R221 `rw [h]` 不能带全称量词进乘积**：`h : ∀ x, f x = g x` 直接 `rw [h]` 报
  "Did not find an occurrence of the pattern `b ?x ^ …`"——因为乘积里的约束变元与 `h` 的
  绑定变元不同一。**正解**：`simp only [h]`（`simp` 会实例化）。

**射程（勿夸大，★ 两条要紧的）**：
* **域同构未与该字典接通**：§3 的 `sprFieldMprimeAlg` 用的是**任意枚举**
  （`Fintype.equivFinOfCardEq`），故本节的权字典**尚未**推出
  "`sprFieldMprimeAlg` 把 `sprDiagFieldEquiv` 送到 `torusScaleFieldEquiv`"。
  要接通须把 §3 的链改为以 `sprIdxEquivIdx` 为锚（下一轮）。
* `sprFieldNFixed ↔ (TFixed ∧ SFixed)`、`V3'` 的 `AlgEquiv` 本身 —— **未建**；
  `ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprWeightDictionary

set_option linter.style.haveILetI false

open ABGV52

/-- `wt` 在单项式基元 `e(u_i)` 上就是 `b i`。 -/
theorem wt_single_one (F : Type) [Field F] (b : Fin 9 → Fˣ) (i : G.OmegaP 3) :
    wt F b (MonoidAlgebra.single i (1 : ℤ)) = b i := by
  rw [wt]
  have h : ∀ x : G.OmegaP 3, b x ^ (MonoidAlgebra.coeff (MonoidAlgebra.single i (1 : ℤ)) x)
      = if x = i then b i else 1 := by
    intro x
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hx : x = i
    · subst hx
      simp
    · rw [if_neg hx, if_neg (Ne.symm hx), zpow_zero]
  simp only [h]
  rw [Finset.prod_eq_single (s := Finset.univ) i
    (fun j _ hj => by simp [hj])
    (fun hh => absurd (Finset.mem_univ i) hh)]
  simp

#print axioms wt_single_one

/-- `wt` 取逆：`wt b (−z) = (wt b z)⁻¹`。 -/
theorem wt_neg (F : Type) [Field F] (b : Fin 9 → Fˣ) (z : G.ZOm 3) :
    wt F b (-z) = (wt F b z)⁻¹ := by
  rw [wt, wt, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [MonoidAlgebra.coeff_neg, Finsupp.neg_apply, zpow_neg]

#print axioms wt_neg

/-- ★★★★★ **`T` 侧权字典（`y`-方向）**：`e(u_ij)` 的权是 `b_i · b_j⁻¹`。

经 `fPrime_mprimeBasis_inl`（`f'(u_ij) = u_i − u_j`，`SaltmanT.lean` 已机检）＋ 权的乘性。 -/
theorem wtM_mprimeBasis_inl (F : Type) [Field F] (b : Fin 9 → Fˣ) (i j : G.OmegaP 3) :
    wtM F b (mprimeBasis (Sum.inl (i, j))) = b i * (b j)⁻¹ := by
  rw [wtM, fPrime_mprimeBasis_inl, sub_eq_add_neg, wt_add, wt_single_one, wt_neg,
    wt_single_one]

#print axioms wtM_mprimeBasis_inl

/-- ★★★★★ **`T` 侧权字典（`x`-方向）**：`e(u_i)` 的权是 `1`。 -/
theorem wtM_mprimeBasis_inr (F : Type) [Field F] (b : Fin 9 → Fˣ) (i : G.OmegaP 3) :
    wtM F b (mprimeBasis (Sum.inr i)) = 1 := by
  rw [wtM, fPrime_mprimeBasis_inr, wt_zero]

#print axioms wtM_mprimeBasis_inr

/-- ★★★★★ **`S'` 变元的权**（`T`-作用在变元上的特征值，与 `sprDiagHom` 的定义一致）。 -/
noncomputable def sprIdxWeight (F : Type) [Field F] (b : Fin 9 → Fˣ) (v : SprIdx 2 9) : F :=
  match v with
  | Sum.inl _ => 1
  | Sum.inr (i, j, _) => (b i : F) * ((b j : F))⁻¹

#print axioms sprIdxWeight

/-- 计算律：`x_ii` 的权是 `1`。 -/
lemma sprIdxWeight_inl (F : Type) [Field F] (b : Fin 9 → Fˣ) (i : Fin 9) :
    sprIdxWeight F b (Sum.inl i) = 1 := rfl

#print axioms sprIdxWeight_inl

/-- 计算律：`y_ijk` 的权是 `b_i · b_j⁻¹`。 -/
lemma sprIdxWeight_inr (F : Type) [Field F] (b : Fin 9 → Fˣ) (i j : Fin 9)
    (k : {k : Fin 2 // k.val ≠ 0}) :
    sprIdxWeight F b (Sum.inr (i, j, k)) = (b i : F) * ((b j : F))⁻¹ := rfl

#print axioms sprIdxWeight_inr

/-- ★★★★★ **`T` 侧统一特征向量式**：`sprDiagHom b (X v) = sprIdxWeight b v · X v`。

即每个变元都是 `T` 的特征向量，特征值就是 `sprIdxWeight`（源文 `lem:14.20` 的 `(17)`：
"for all `m ∈ M_r'` and `B ∈ T_n` there is a `λ ∈ F^*` such that `φ_B(e(m)) = λ e(m)`"）。 -/
theorem sprDiagHom_X_eq_weight (F : Type) [Field F] (b : Fin 9 → Fˣ) (v : SprIdx 2 9) :
    sprDiagHom F 2 9 b (MvPolynomial.X v)
      = MvPolynomial.C (sprIdxWeight F b v) * MvPolynomial.X v := by
  rcases v with i | ⟨⟨i, j⟩, k⟩
  · rw [sprIdxWeight_inl, sprDiagHom_X_inl, map_one, one_mul]
  · rw [sprIdxWeight_inr, sprDiagHom_X_inr]

#print axioms sprDiagHom_X_eq_weight

end SprWeightDictionary

/-! ## §5 **权字典的合并式** —— 两侧权表逐基元相等（`T` 侧对应的最后一块书签）

§4 分别给出了两侧的权（`wtM_mprimeBasis_inl`／`_inr` 与 `sprIdxWeight`）。
本节把它们**合并成一条等式**：`S'` 侧变元 `v` 的权 ＝ `M_2'` 侧对应基元
`e(sprIdxEquivIdx v)` 的权。

**⟹ 为什么这是「`T` 侧对应」的书签**：§3 的 `sprFieldMprimeAlg` 在变元上送出
`X v ↦ e(mprimeBasis (sprIdxEquivIdx v))`（因 `idxEquivFin` 是**用** `sprIdxEquivFin` 定义的，
故该复合与任意枚举无关），于是两侧的 `T`-特征值必须**逐变元相等**才能让同构与作用交换。
本条正是那个等式。

**工艺（1 条，本轮实测）**：
* **R222 本 pin 的 `Units.val_inv` 不是 `↑(u⁻¹) = (↑u)⁻¹`**：它的陈述是 **`↑u * u.inv = 1`**
  （本轮 `#check` 实测）。写 `rw [Units.val_inv]` 会报 "找不到落点 `↑?self * Units.inv ?self`"
  —— 形似引理用错，实为**同名不同义**。**正解**：用 `simp [Units.val_mul]`（`simp` 集合里有
  正确的 coercion 引理）。

**射程（勿夸大）**：本条只是**数值层**的合并。由它到
「`sprFieldMprimeAlg (sprDiagFieldEquiv b x) = torusScaleFieldEquiv b (sprFieldMprimeAlg x)`」
还需要一条**生成元计算**（`sprFieldMprimeAlg (X v) = e(mprimeBasis (sprIdxEquivIdx v))`）
—— **未证**。`sprFieldNFixed ↔ (TFixed ∧ SFixed)`、`V3'` 的 `AlgEquiv` 本身 —— **未建**；
`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprWeightMatch

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★★ **权的对应** —— `S'` 侧变量 `v` 的权 ＝ `M_2'` 侧 `e(sprIdxEquivIdx v)` 的权。

与 §2 的 `sprIdxEquivIdx_perm`（`S_n` 侧）合起来，`N = T ⋊ S_n` 的两侧作用在
**基元层**已完全对齐。 -/
theorem sprIdxWeight_eq_wtM (F : Type) [Field F] (b : Fin 9 → Fˣ) (v : SprIdx 2 9) :
    sprIdxWeight F b v = ((wtM F b (mprimeBasis (sprIdxEquivIdx v)) : Fˣ) : F) := by
  rcases v with i | ⟨⟨i, j⟩, k⟩
  · rw [sprIdxWeight_inl, sprIdxEquivIdx_inl, wtM_mprimeBasis_inr]
    rfl
  · rw [sprIdxWeight_inr, sprIdxEquivIdx_inr, wtM_mprimeBasis_inl]
    simp [Units.val_mul]

#print axioms sprIdxWeight_eq_wtM

end SprWeightMatch

/-! ## §6 **`V3'` 的 ① 生成元计算（上）：把复合的四步逐段算清 1／4、2／4**

v16 §4.3 的 ① 要求机检

```
sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) (X v))
  = algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
      (MonoidAlgebra.single (ofAdd (mprimeBasis (sprIdxEquivIdx v))) 1)
```

该复合是四段：`sprFracEquivFin`（分式域延拓）→ `sprFracToLattice`（Laurent）→
`freeSubst`（D2）→ `latticeFieldCongrAlg`（指标搬运）。本节把**后两段的单项式层**算清：

| 件 | 内容 |
|---|---|
| ★★★★★ `sprPolyEquivFin_X` | **`sprPolyEquivFin F (X v) = X (sprIdxEquivFin v)`** |
| ★★★★★ `mapDomainRingEquiv_single` | `mapDomainRingEquiv` 在单项式上：`single m r ↦ single (e m) r` |
| ★★★★★ `latticeFieldCongrAlg_single` | **`latticeFieldCongrAlg F e (algebraMap (single m r)) = algebraMap (single (e m) r)`** |

**工艺（1 条，本轮实测）**：
* **R223 `mapDomainRingEquiv` 的"应用引理"是 `coeff` 形式**（本 pin 的
  `MonoidAlgebra.mapDomainRingEquiv_apply` 已弃用，替代品 `coeff_mapDomainRingEquiv`
  给的是**系数**等式）。走 `coeff` + `Finsupp.equivMapDomain_apply` + `single_apply` 的路
  **要处理 `MulEquiv.symm` 的实例摩擦，很缠**。
  **正解**：`mapDomainRingEquiv` 与 `mapDomain` 是 **`rfl` 同一** ——
  `rw [show (mapDomainRingEquiv F e) = MonoidAlgebra.mapDomain e from rfl, MonoidAlgebra.mapDomain_single]`。
  **凡"结构包装"型 `def`（`RingEquiv` 包 `mapDomain`），先试 `rfl` 展开，别急着走系数路线。**

**射程（勿夸大）**：本节只清了**四段中的后两段**。仍缺：
(a) `sprFracEquivFin` 在 `algebraMap` 上的计算（`IsFractionRing.algEquivOfAlgEquiv_algebraMap`）；
(b) `sprFracToLattice` 在 `algebraMap` 上的计算（`IsLocalization.algEquiv` 的 `R`-线性，
    本 pin 的 `algebraMap` 计算律**尚未查清**）；
(c) `freeSubst` 在 `X k` 上的值（`EM.freeSubst_monomial` ＋ `freeEmb` 的单项式值）；
(d) **指标计算** `e (freeEmb (single (sprIdxEquivFin v) 1)) = mprimeBasis (sprIdxEquivIdx v)`
    （须用 `idxEquivFin` 的定义把两个枚举对齐；这是 ① 与"任意枚举无关"的**机检点**）。
`V3'` 的 ②③④⑤ **未建**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprGeneratorStep

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ `sprPolyEquivFin` 在变元上：`X v ↦ X (sprIdxEquivFin v)`。 -/
theorem sprPolyEquivFin_X (F : Type) [Field F] (v : SprIdx 2 9) :
    sprPolyEquivFin F (MvPolynomial.X v) = MvPolynomial.X (sprIdxEquivFin v) := by
  rw [sprPolyEquivFin, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]

#print axioms sprPolyEquivFin_X

/-- ★★★★★ `mapDomainRingEquiv` 在单项式上：`single m r ↦ single (e m) r`。

`mapDomainRingEquiv` 与 `mapDomain` 是 **`rfl` 同一**（见 R223），故一条 `rw` 即得。 -/
theorem mapDomainRingEquiv_single {F : Type} [Field F] {M N : Type} [AddCommGroup M]
    [AddCommGroup N] (e : M ≃+ N) (m : Multiplicative M) (r : F) :
    (MonoidAlgebra.mapDomainRingEquiv F e.toMultiplicative) (MonoidAlgebra.single m r)
      = MonoidAlgebra.single (e.toMultiplicative m) r := by
  rw [show (MonoidAlgebra.mapDomainRingEquiv F e.toMultiplicative :
      MonoidAlgebra F (Multiplicative M) → MonoidAlgebra F (Multiplicative N))
      = MonoidAlgebra.mapDomain e.toMultiplicative from rfl]
  exact MonoidAlgebra.mapDomain_single

#print axioms mapDomainRingEquiv_single

/-- ★★★★★ **`latticeFieldCongrAlg` 在单项式上**：`e(m) ↦ e(e' m)`（分式域层的搬运计算律）。 -/
theorem latticeFieldCongrAlg_single {F : Type} [Field F] {M N : Type} [AddCommGroup M]
    [AddCommGroup N] (e : M ≃+ N) (m : Multiplicative M) (r : F) :
    latticeFieldCongrAlg F e
        (algebraMap (EM.latticeAlgebra F M) (EM.latticeFunctionField F M)
          (MonoidAlgebra.single m r))
      = algebraMap (EM.latticeAlgebra F N) (EM.latticeFunctionField F N)
          (MonoidAlgebra.single (e.toMultiplicative m) r) := by
  rw [latticeFieldCongrAlg, AlgEquiv.ofRingEquiv_apply,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, mapDomainRingEquiv_single]

#print axioms latticeFieldCongrAlg_single

end SprGeneratorStep

/-! ## §7 **`V3'` 的 ① 生成元计算（中）：复合四段的逐段计算律**

§6 清了后两段的**单项式层**。本节补齐前两段在 `algebraMap` 上的计算律、以及第三段在
变元上的值 —— 即 v16 §4.3 ① 的四段**逐段**计算律（缺最后一步"指标对齐"，见射程）。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprFracEquivFin_algebraMap` | 段 1：`IsFractionRing.algEquivOfAlgEquiv` 在 `algebraMap` 上 |
| ★★★★★ `isLocalization_algEquiv_algebraMap` | 泛型：`IsLocalization.algEquiv M S Q (algebraMap p) = algebraMap p` |
| ★★★★★ `sprFracToLattice_algebraMap` | 段 2：由上式即时得 |
| ★★★★★ `freeSubst_X` | 段 3：`freeSubst (X k) = single (ofAdd (Pi.single k 1)) 1` |
| ★★★★★ `mprimeEquivFun_symm_single` | 段 4 的基向量侧：`mprimeEquivFun.symm (Pi.single i 1) = mprimeBasis i` |

**工艺（2 条，本轮实测）**：
* **R224 `(Fin n → ℤ)` 不是 `(Fin n →₀ ℤ)`**：`EM.latticeAlgebra F (Fin n → ℤ)` 的指数是
  **函数类型**（`Pi`），而 `Finsupp.single` 造的是 `→₀`。写 `MonoidAlgebra.single
  (ofAdd (Finsupp.single k 1)) 1` 报 "has type `MonoidAlgebra F (Multiplicative (Fin 90 →₀ ℤ))`
  but is expected `EM.latticeAlgebra F (Fin 90 → ℤ)`"——**形似类型错，实为 `Pi` vs `Finsupp`**。
  **正解**：用 **`Pi.single k (1 : ℤ)`**（`fun i => if i = k then 1 else 0`）。
* **R225 `MonoidAlgebra.single` 的系数类型会默认成 `ℕ`**：`… (1 : ℤ) 1` 会把末位 `1` 推成 `ℕ`
  （报 "has type `MonoidAlgebra ℕ …`"）。**正解**：把系数写成 **`(1 : F)`**。

**射程（勿夸大）**：① 仍差**最后一步**：
(e) `piAddEquiv.symm (Pi.single k 1) = Pi.single (idxEquivFin.symm k) 1`
    （`AddEquiv.symm` 的结构展开在本 pin 上与 `show` 有摩擦，本轮两试未过）；
(f) 由 (e) ＋ `idxEquivFin` 的定义得 `e (Pi.single (sprIdxEquivFin v) 1) = mprimeBasis (sprIdxEquivIdx v)`；
(g) 四段按 `AlgEquiv.trans_apply` 串成**整条**生成元等式。
`V3'` 的 ②③④⑤ **未建**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprGeneratorStep2

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ 段 1：`sprFracEquivFin` 在 `algebraMap` 上。 -/
theorem sprFracEquivFin_algebraMap (F : Type) [Field F] (p : Spr F 2 9) :
    sprFracEquivFin F (algebraMap (Spr F 2 9) (SprField F 2 9) p)
      = algebraMap (MvPolynomial (Fin 90) F) (FractionRing (MvPolynomial (Fin 90) F))
          (sprPolyEquivFin F p) := by
  rw [sprFracEquivFin, IsFractionRing.algEquivOfAlgEquiv_algebraMap]

#print axioms sprFracEquivFin_algebraMap

/-- ★★★★★ **泛型**：`IsLocalization.algEquiv` 在 `algebraMap` 上就是 `algebraMap`。 -/
theorem isLocalization_algEquiv_algebraMap {R S Q : Type} [CommRing R] [CommRing S] [CommRing Q]
    {M : Submonoid R} [Algebra R S] [IsLocalization M S] [Algebra R Q] [IsLocalization M Q]
    (p : R) :
    (IsLocalization.algEquiv M S Q) (algebraMap R S p) = algebraMap R Q p := by
  rw [← IsLocalization.mk'_one (M := M) S p, IsLocalization.algEquiv_mk',
    IsLocalization.mk'_one]

#print axioms isLocalization_algEquiv_algebraMap

/-- ★★★★★ 段 2：`sprFracToLattice` 在 `algebraMap` 上。 -/
theorem sprFracToLattice_algebraMap (F : Type) [Field F] (p : MvPolynomial (Fin 90) F) :
    sprFracToLattice F (algebraMap (MvPolynomial (Fin 90) F)
        (FractionRing (MvPolynomial (Fin 90) F)) p)
      = algebraMap (MvPolynomial (Fin 90) F) (EM.latticeFunctionField F (Fin 90 → ℤ)) p := by
  haveI hfr : IsFractionRing (MvPolynomial (Fin 90) F)
      (EM.latticeFunctionField F (Fin 90 → ℤ)) := EM.freeSubst_isFractionRing F 90
  exact isLocalization_algEquiv_algebraMap
    (M := nonZeroDivisors (MvPolynomial (Fin 90) F)) p

#print axioms sprFracToLattice_algebraMap

/-- ★★★★★ 段 3：`freeSubst` 在变元 `X k` 上。 -/
theorem freeSubst_X (F : Type) [Field F] (k : Fin 90) :
    EM.freeSubst F 90 (MvPolynomial.X k)
      = MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single k (1 : ℤ))) (1 : F) := by
  show EM.freeSubst F 90 (MvPolynomial.monomial (Finsupp.single k (1 : ℕ)) 1)
    = MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single k (1 : ℤ))) (1 : F)
  rw [EM.freeSubst_monomial]
  have h : ((EM.freeEmb 90) (Finsupp.single k (1 : ℕ))) = (Pi.single k (1 : ℤ)) := by
    funext i
    rw [EM.freeEmb_apply, Pi.single_apply, Finsupp.single_apply]
    by_cases hik : k = i
    · rw [if_pos hik, if_pos hik.symm]; simp
    · rw [if_neg hik, if_neg (fun h => hik h.symm)]; simp
  rw [h]

#print axioms freeSubst_X

/-- ★★★★★ 段 4 的基向量侧：`mprimeEquivFun.symm (Pi.single i 1) = mprimeBasis i`。 -/
theorem mprimeEquivFun_symm_single (i : Idx) :
    mprimeEquivFun.symm (Pi.single i (1 : ℤ)) = mprimeBasis i := by
  rw [mprimeEquivFun, Module.Basis.equivFun_symm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

#print axioms mprimeEquivFun_symm_single

end SprGeneratorStep2

/-! ## §8 ★★★★★★ **`V3'` 的 ① 完成：整条生成元等式** —— v16 §6 第 1 项收口

§6／§7 把四段复合的**逐段**计算律清完。本节补上**最后两步**并串成**整条**等式：

```
sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) (X v))
  = algebraMap (ℓ) (latticeFunctionField F Mprime)
      (single (ofAdd (mprimeBasis (sprIdxEquivIdx v))) 1)
```

（`ℓ = EM.latticeAlgebra F Mprime`）。这条是 `V3'` 的 ②③④（作用对应）的**唯一入口**。

| 件 | 内容 |
|---|---|
| ★★★★★ `piAddEquiv_apply_single` | `piAddEquiv` 正向在基向量上（`toFun` 直接展开） |
| ★★★★★ `piAddEquiv_symm_single` | (e) `piAddEquiv.symm (Pi.single k 1) = Pi.single (idxEquivFin.symm k) 1` |
| ★★★★★ `idxEquivFin_apply_sprIdxEquivIdx` | `idxEquivFin (sprIdxEquivIdx v) = sprIdxEquivFin v` |
| ★★★★★ `idxEquivFin_symm_sprIdxEquivFin` | `idxEquivFin.symm (sprIdxEquivFin v) = sprIdxEquivIdx v` |
| ★★★★★ `indexAlignment` | (f) **指标对齐**：`e (Pi.single (sprIdxEquivFin v) 1) = mprimeBasis (sprIdxEquivIdx v)` |
| ★★★★★★ `sprFieldMprimeAlg_X` | (g) **整条生成元等式** |

**★ 为什么 `indexAlignment` 是"任意枚举无关"的机检点**：`idxEquivFin` 的**定义**就是
`sprIdxEquivIdx.symm.trans sprIdxEquivFin`，故 `idxEquivFin.symm (sprIdxEquivFin v) = sprIdxEquivIdx v`
**与 `sprIdxEquivFin` 的具体取法无关**。于是尽管 §3 的链用了 `Fintype.equivFinOfCardEq`
这一**任意**枚举，复合在变元上的像**确为** `e(mprimeBasis (sprIdxEquivIdx v))` ——
即 §2 的 `sprIdxEquivIdx` 所定的那个自然对应。

**工艺（3 条，本轮实测）**：
* **R226 `AddEquiv.symm` 的结构展开与 `show` 有摩擦**：直接 `funext` ＋ `show` 会得到
  "expected `?m (?m' i)`"（元变量未定）。**正解**：**只证正向** `piAddEquiv_apply_single`
  （`toFun` 是字面量，展开顺利），再 `congrArg piAddEquiv.symm` ＋ `AddEquiv.symm_apply_apply`
  反推 (e)。**"反向难证就证正向再推"**。
* **R227 `Pi.single` 没有 `Pi.single_apply` 那一类的 `if` 形式**：本 pin 是
  `Pi.single_eq_same`／`Pi.single_eq_of_ne`（依赖型 `Pi.single`）。用 `by_cases` ＋ `simp [...]`。
* **R228 `Noncomputable def` 的 `rfl` 可展开，`rw` 不可**（R220 的补强）：`h0 : … := rfl`
  这种 `have` 配合 `rw [h0]` 是本轮串链的**唯一可行**写法；
  `rw [sprFieldMprimeAlg]` 因 R220 不落点。

**射程（勿夸大）**：① **已完成**。`V3'` 的 ②③④⑤（`T`／`S_n` 等变 → 固定点 → `V3'`）
**未建**；输入 (i)／(ii) **未证**（`UD` 尚未定义）；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprGeneratorFinal

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ `piAddEquiv` 的**正向**作用在基向量上（`toFun` 是字面量，展开顺利；见 R226）。 -/
theorem piAddEquiv_apply_single (k : Fin 90) :
    piAddEquiv (Pi.single (idxEquivFin.symm k) (1 : ℤ) : Idx → ℤ)
      = Pi.single k (1 : ℤ) := by
  funext i
  show (Pi.single (idxEquivFin.symm k) (1 : ℤ) : Idx → ℤ) (idxEquivFin.symm i)
    = (Pi.single k (1 : ℤ) : Fin 90 → ℤ) i
  by_cases h : i = k
  · subst h
    simp
  · have h1 : (idxEquivFin.symm i) ≠ (idxEquivFin.symm k) :=
      fun hh => h (idxEquivFin.symm.injective hh)
    simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h]

#print axioms piAddEquiv_apply_single

/-- ★★★★★ (e) `piAddEquiv.symm` 在基向量上（由正向式反推，见 R226）。 -/
theorem piAddEquiv_symm_single (k : Fin 90) :
    piAddEquiv.symm (Pi.single k (1 : ℤ)) = Pi.single (idxEquivFin.symm k) (1 : ℤ) := by
  have h := piAddEquiv_apply_single k
  have h2 : piAddEquiv.symm (piAddEquiv (Pi.single (idxEquivFin.symm k) (1 : ℤ) : Idx → ℤ))
      = piAddEquiv.symm (Pi.single k (1 : ℤ)) := congrArg piAddEquiv.symm h
  rw [AddEquiv.symm_apply_apply] at h2
  exact h2.symm

#print axioms piAddEquiv_symm_single

/-- ★★★★★ `idxEquivFin (sprIdxEquivIdx v) = sprIdxEquivFin v`。 -/
theorem idxEquivFin_apply_sprIdxEquivIdx (v : SprIdx 2 9) :
    idxEquivFin (sprIdxEquivIdx v) = sprIdxEquivFin v := by
  show (sprIdxEquivIdx.symm.trans sprIdxEquivFin) (sprIdxEquivIdx v) = sprIdxEquivFin v
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]

#print axioms idxEquivFin_apply_sprIdxEquivIdx

/-- ★★★★★ `idxEquivFin.symm (sprIdxEquivFin v) = sprIdxEquivIdx v`
—— **"任意枚举无关"的机检点**（见本节说明）。 -/
theorem idxEquivFin_symm_sprIdxEquivFin (v : SprIdx 2 9) :
    idxEquivFin.symm (sprIdxEquivFin v) = sprIdxEquivIdx v := by
  rw [← idxEquivFin_apply_sprIdxEquivIdx v]
  exact Equiv.symm_apply_apply idxEquivFin (sprIdxEquivIdx v)

#print axioms idxEquivFin_symm_sprIdxEquivFin

/-- ★★★★★ (f) **指标对齐**：`e (Pi.single (sprIdxEquivFin v) 1) = mprimeBasis (sprIdxEquivIdx v)`。 -/
theorem indexAlignment (v : SprIdx 2 9) :
    (piAddEquiv.symm.trans mprimeEquivFun.toAddEquiv.symm)
        (Pi.single (sprIdxEquivFin v) (1 : ℤ))
      = mprimeBasis (sprIdxEquivIdx v) := by
  rw [AddEquiv.trans_apply, piAddEquiv_symm_single, idxEquivFin_symm_sprIdxEquivFin]
  exact mprimeEquivFun_symm_single _

#print axioms indexAlignment

/-- ★★★★★★ (g) **整条生成元等式** —— `V3'` 的 ① 完成。

`sprFieldMprimeAlg` 把 `S'` 的变元 `X v` 送到 `M_2'` 的基元 `e(mprimeBasis (sprIdxEquivIdx v))`，
**与 §3 里那个任意枚举无关**（见 `idxEquivFin_symm_sprIdxEquivFin`）。 -/
theorem sprFieldMprimeAlg_X (F : Type) [Field F] (v : SprIdx 2 9) :
    sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v))
      = algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
          (MonoidAlgebra.single (Multiplicative.ofAdd (mprimeBasis (sprIdxEquivIdx v)))
            (1 : F)) := by
  have h0 : sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v))
      = latticeFieldCongrAlg F (piAddEquiv.symm.trans mprimeEquivFun.toAddEquiv.symm)
          (sprFieldLattice F (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v))) := rfl
  rw [h0]
  have h1 : sprFieldLattice F (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v))
      = algebraMap (MvPolynomial (Fin 90) F) (EM.latticeFunctionField F (Fin 90 → ℤ))
          (MvPolynomial.X (sprIdxEquivFin v)) := by
    show sprFracToLattice F (sprFracEquivFin F
      (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v))) = _
    rw [sprFracEquivFin_algebraMap, sprPolyEquivFin_X, sprFracToLattice_algebraMap]
  rw [h1, EM.algebraMap_freeSubst, freeSubst_X, latticeFieldCongrAlg_single]
  have h2 : (piAddEquiv.symm.trans mprimeEquivFun.toAddEquiv.symm).toMultiplicative
      (Multiplicative.ofAdd (Pi.single (sprIdxEquivFin v) (1 : ℤ)))
      = Multiplicative.ofAdd (mprimeBasis (sprIdxEquivIdx v)) := by
    show Multiplicative.ofAdd ((piAddEquiv.symm.trans mprimeEquivFun.toAddEquiv.symm)
      (Pi.single (sprIdxEquivFin v) (1 : ℤ))) = _
    rw [indexAlignment]
  rw [h2]

#print axioms sprFieldMprimeAlg_X

end SprGeneratorFinal

/-! ## §9 **`V3'` 的 ② 基础设施：`torusScale` 的 `F`-线性与单项式分解**

`V3'` 的 ② 要证（`T`-等变）：

```
sprFieldMprimeAlg F (sprDiagFieldEquiv F 2 9 b x) = torusScaleFieldEquiv F b (sprFieldMprimeAlg F x)
```

**为什么需要本节的三件**：② 的 `Spr` 层化归（见下）要把右端算成
`algebraMap F _ (sprIdxWeight b v) * algebraMap (single …) 1`，这要求
(a) `torusScaleFieldEquiv b` **能被当作 `F`-代数同态**（否则两边的 `AlgHom` 结构不同，
无法用 `MvPolynomial.algHom_ext`）；(b) `torusScale` **固定 `F`-纯量**；
(c) `single m c` 能**分解**成纯量乘 `single m 1`。

| 件 | 内容 |
|---|---|
| ★★★★★ `torusScale_algebraMap` | `torusScale b` 固定 `F`-纯量 |
| ★★★★★ `torusScaleAlgHom` | **`torusScaleFieldEquiv b` 提升为 `F`-`AlgHom`**（② 的陈述前提） |
| ★★★★★ `single_eq_algebraMap_mul` | `single m c = algebraMap c * single m 1` |

**射程（勿夸大）**：② 的**主体（`Spr` 层等式 `sprDiagHom_torusScale_level`）尚未收**。
本轮已把它的化归链走到**最后一步**；剩余形状（下一轮直接照此收）：

```
目标  sprDiagHom b (X v) = C (sprIdxWeight b v) * X v            -- 有（sprDiagHom_X_eq_weight）
推  Φ (algebraMap (C c * X v)) = Φ (algebraMap (C c)) * Φ (algebraMap (X v))
冲  algebraMap F _ c * Φ (algebraMap (X v))
        =? torusScaleFieldEquiv b (Φ (algebraMap (X v)))
        = algebraMap (single m (1 * chi b m))                -- torusScaleFieldEquiv_algebraMap ＋ torusScale_single
        = algebraMap F _ (chi b m) * algebraMap (single m 1)  -- 用本节 single_eq_algebraMap_mul ＋ map_mul
两端相等  ⟺  c = chi b m  ⟺  sprIdxWeight b v = (wtM b (mprimeBasis (sprIdxEquivIdx v)) : F)
                                                        -- 有（§5 sprIdxWeight_eq_wtM）
卡点：链末残留 `algebraMap F (latticeAlgebra) 1` 的因子，须先 `map_one`／`one_mul` 清掉
（本轮 `simp` 未吃掉它）。
```

`V3'` 的 ③④⑤ **未建**；输入 (i)／(ii) **未证**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprTorusEquivariance

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **`torusScale` 固定 `F`-纯量**（② 的 `F`-线性前提）。 -/
theorem torusScale_algebraMap (F : Type) [Field F] (b : Fin 9 → Fˣ) (a : F) :
    torusScale F b (algebraMap F (EM.latticeAlgebra F Mprime) a)
      = algebraMap F (EM.latticeAlgebra F Mprime) a := by
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, torusScale_single, chi_one,
    mul_one]

#print axioms torusScale_algebraMap

/-- ★★★★★ **`torusScaleFieldEquiv b` 作为 `F`-代数同态** —— ② 的**陈述前提**。 -/
noncomputable def torusScaleAlgHom (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    EM.latticeFunctionField F Mprime →ₐ[F] EM.latticeFunctionField F Mprime where
  toFun := torusScaleFieldEquiv F b
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun a => by
    rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
      (EM.latticeFunctionField F Mprime) a, torusScaleFieldEquiv_algebraMap,
      torusScale_algebraMap]

#print axioms torusScaleAlgHom

/-- ★★★★★ **`single m c` 分解为纯量乘 `single m 1`**。 -/
theorem single_eq_algebraMap_mul (F : Type) [Field F] (m : Multiplicative Mprime) (c : F) :
    MonoidAlgebra.single m c
      = algebraMap F (EM.latticeAlgebra F Mprime) c * MonoidAlgebra.single m 1 := by
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, MonoidAlgebra.single_mul_single]
  simp

#print axioms single_eq_algebraMap_mul

end SprTorusEquivariance

/-! ## §10 **`V3'` 的 ③ 基础设施：`permScale` 的 `F`-线性与 `AlgHom` 提升**

§9 给了 `T` 侧（`torusScale`）的两件前提，使 ② 的 `Spr` 层能作为**两个 `AlgHom`** 比较。
本节给 `S_n` 侧（`permScale`）的对应物 —— ③（`S_n`-等变）的**同一套前提**。

| 件 | 内容 |
|---|---|
| ★★★★★ `permScale_algebraMap` | `permScale σ` 固定 `F`-纯量（`actM σ 0 = 0`） |
| ★★★★★ `permScaleAlgHom` | **`permScaleFieldEquiv σ` 提升为 `F`-`AlgHom`**（③ 的陈述前提） |

**为什么必须提升**：`permScaleFieldEquiv σ` 在本仓只是 `≃+*`；而 ③ 要证
`Φ (sprPermFieldEquiv σ x) = permScaleFieldEquiv σ (Φ x)`，
其 `Spr` 层化归（`Φ ∘ algebraMap ∘ sprPermHom σ = permScaleFieldEquiv σ ∘ Φ ∘ algebraMap`）
两边是 **`AlgHom`**，比较工具是 `MvPolynomial.algHom_ext` —— 右侧若不是 `AlgHom` 则根本
无法陈述。**⟹ 这一步不是"装饰"，是陈述的前置条件。**

**工艺（1 条，本轮实测）**：
* **R230 `algebraMap F (MonoidAlgebra F G) a` 要转成 `single 1 a` 得走
  `MonoidAlgebra.coe_algebraMap` ＋ `Function.comp_apply` ＋ `rfl`**（`algebraMap F F a = a`
  那一步是 `rfl`）。转成 `single 1 a` 之后 `permScale_single`／`torusScale_single` 才能落点；
  而 `congr 1` 之后 `ofAdd (actM σ 0) = ofAdd 0` **本身就是 `rfl`**
  （不要再加 `actM_zero`／`rfl`，会报 "No goals to be solved"）。

**射程（勿夸大）**：本节只给 ③ 的**前提**。③ 的**主体**（`sprPermFieldEquiv` 与
`permScaleFieldEquiv` 的等变）**未建**；② 的**主体**仍未收（§9 射程）；
`V3'` 的 ④⑤ **未建**；输入 (i)／(ii) **未证**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprPermEquivariance

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **`permScale σ` 固定 `F`-纯量**（③ 的 `F`-线性前提）。 -/
theorem permScale_algebraMap (F : Type) [Field F] (σ : G.Gp 3) (a : F) :
    permScale F σ (algebraMap F (EM.latticeAlgebra F Mprime) a)
      = algebraMap F (EM.latticeAlgebra F Mprime) a := by
  have h : algebraMap F (EM.latticeAlgebra F Mprime) a
      = MonoidAlgebra.single (1 : Multiplicative Mprime) a := by
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply]
    rfl
  rw [h, permScale_single]
  congr 1

#print axioms permScale_algebraMap

/-- ★★★★★ **`permScaleFieldEquiv σ` 作为 `F`-代数同态** —— ③ 的**陈述前提**。 -/
noncomputable def permScaleAlgHom (F : Type) [Field F] (σ : G.Gp 3) :
    EM.latticeFunctionField F Mprime →ₐ[F] EM.latticeFunctionField F Mprime where
  toFun := permScaleFieldEquiv F σ
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun a => by
    rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
      (EM.latticeFunctionField F Mprime) a, permScaleFieldEquiv_algebraMap,
      permScale_algebraMap]

#print axioms permScaleAlgHom

end SprPermEquivariance

/-! ## §11 ★★★★★★★ **`V3'` 的 ② 完成：`T`-等变（`Spr` 层 ＋ 分式域层）**

v16 §6 第 2 项的 **`T` 半**：`sprFieldMprimeAlg` 把 `T`-作用送到 `T`-作用。
§9 给了前提（`torusScale` 的 `F`-线性 ＋ `AlgHom` 提升），本节给**主体**。

**★ 战术（第 363 轮的关键决定，须记住）**：② 的主体在 361／362 两轮**未收**，
根因是**在同一个 `rw` 链里既展开又化简**（R220／R228 的干扰源：`noncomputable def` 不展开
＋ `simp` 过度归约互相打架）。**改道 = "两侧各自算成标准形再比"**：

| 步 | 件 | 内容 |
|---|---|---|
| 1 | ★★★★★ `sprDiagHom_X_std` | **左端标准形**：`Φ (algebraMap (sprDiagHom b (X v))) = algebraMap F _ (sprIdxWeight b v) * Φ (algebraMap (X v))` |
| 2 | ★★★★★ `torusScale_X_std` | **右端标准形**：`torusScaleFieldEquiv b (Φ (algebraMap (X v))) = algebraMap F _ (sprIdxWeight b v) * Φ (algebraMap (X v))` |
| 3 | ★★★★★★ `sprDiagHom_torusScale_level` | **`Spr` 层**：由 1／2 ＋ `MvPolynomial.algHom_ext` |
| 4 | ★★★★★★★ `sprDiagFieldEquiv_torusScale` | **分式域层**：由 3 ＋ `IsFractionRing.ringHom_ext` |

**两端的相遇点**：两式相等归约到 `sprIdxWeight b v = (wtM b (mprimeBasis (sprIdxEquivIdx v)) : F)`
—— **§5 的 `sprIdxWeight_eq_wtM`**。这正是 §4／§5 建权字典的**用处**：权字典不是装饰，
它是 ② 的**唯一汇合点**。

**★ 与 §8 的合成**：`sprDiagHom_X_std` 用 §8 的 `sprFieldMprimeAlg_X`（左端展开）与
§4 的 `sprDiagHom_X_eq_weight`（`T` 在变元上的特征值）；`torusScale_X_std` 用 §8 的
`sprFieldMprimeAlg_X`、`torusScale_single`、§9 的 `single_eq_algebraMap_mul`。

**工艺（2 条，本轮实测）**：
* **R231 "两侧各自标准形"是本类等变证明的通用战术**：不要在一条 `rw` 链里同时
  展开 `noncomputable def`（R220 禁）与化简（`simp` 过度归约、R212）——
  先建 `_std` 引理把两侧各算到同一标准形，再 `rw [std_L, std_R]` 一次相消。
  **本轮 361／362 两轮卡住的正是这一点；改道后一轮即成。**
* **R232 `IsFractionRing.ringHom_ext` 会把 `A`（底环）卡成元变量**：须显式
  `(A := Spr F 2 9)`，否则报 "typeclass instance problem is stuck"。

**射程（勿夸大）**：② **已完成**。③（`S_n` 侧）的**主体未建**（§10 只给了前提）；
`V3'` 的 ④⑤ **未建**；输入 (i)／(ii) **未证**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprTorusEquivariance2

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **② 左端标准形**。 -/
theorem sprDiagHom_X_std (F : Type) [Field F] (b : Fin 9 → Fˣ) (v : SprIdx 2 9) :
    sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9)
        (sprDiagHom F 2 9 b (MvPolynomial.X v)))
      = algebraMap F (EM.latticeFunctionField F Mprime) (sprIdxWeight F b v)
        * sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9)
            (MvPolynomial.X v)) := by
  have hC : algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.C (sprIdxWeight F b v))
      = algebraMap F (SprField F 2 9) (sprIdxWeight F b v) := by
    rw [MvPolynomial.C_eq_algebraMap,
      IsScalarTower.algebraMap_apply F (Spr F 2 9) (SprField F 2 9)]
  have hc : sprFieldMprimeAlg F (algebraMap F (SprField F 2 9) (sprIdxWeight F b v))
      = algebraMap F (EM.latticeFunctionField F Mprime) (sprIdxWeight F b v) :=
    (sprFieldMprimeAlg F).commutes _
  rw [sprDiagHom_X_eq_weight, map_mul (algebraMap (Spr F 2 9) (SprField F 2 9)),
    map_mul (sprFieldMprimeAlg F), hC, hc]

#print axioms sprDiagHom_X_std

/-- ★★★★★ **② 右端标准形**。 -/
theorem torusScale_X_std (F : Type) [Field F] (b : Fin 9 → Fˣ) (v : SprIdx 2 9) :
    torusScaleFieldEquiv F b (sprFieldMprimeAlg F
        (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v)))
      = algebraMap F (EM.latticeFunctionField F Mprime) (sprIdxWeight F b v)
        * sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9)
            (MvPolynomial.X v)) := by
  have hchi : chi F b (Multiplicative.ofAdd (mprimeBasis (sprIdxEquivIdx v)))
      = ((wtM F b (mprimeBasis (sprIdxEquivIdx v)) : Fˣ) : F) := rfl
  rw [sprFieldMprimeAlg_X, torusScaleFieldEquiv_algebraMap, torusScale_single, one_mul,
    single_eq_algebraMap_mul, map_mul, hchi,
    ← IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
      (EM.latticeFunctionField F Mprime), sprIdxWeight_eq_wtM]

#print axioms torusScale_X_std

/-- ★★★★★★ **② 的 `Spr` 层**（`T`-等变在多项式环上）。 -/
theorem sprDiagHom_torusScale_level (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (p : Spr F 2 9) :
    sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) (sprDiagHom F 2 9 b p))
      = torusScaleFieldEquiv F b
          (sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) p)) := by
  have h : (sprFieldMprimeAlg F : SprField F 2 9 →ₐ[F] EM.latticeFunctionField F Mprime).comp
        ((Algebra.algHom F (Spr F 2 9) (SprField F 2 9)).comp (sprDiagHom F 2 9 b))
      = (torusScaleAlgHom F b).comp
          ((sprFieldMprimeAlg F : SprField F 2 9 →ₐ[F] EM.latticeFunctionField F Mprime).comp
            (Algebra.algHom F (Spr F 2 9) (SprField F 2 9))) := by
    refine MvPolynomial.algHom_ext (fun v => ?_)
    show sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9)
        (sprDiagHom F 2 9 b (MvPolynomial.X v)))
      = torusScaleFieldEquiv F b (sprFieldMprimeAlg F
          (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v)))
    rw [sprDiagHom_X_std, torusScale_X_std]
  exact DFunLike.congr_fun h p

#print axioms sprDiagHom_torusScale_level

/-- ★★★★★★★ **② 的分式域层（`T`-等变）** —— v16 §6 第 2 项的 `T` 半**完成**。 -/
theorem sprDiagFieldEquiv_torusScale (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : SprField F 2 9) :
    sprFieldMprimeAlg F (sprDiagFieldEquiv F 2 9 b x)
      = torusScaleFieldEquiv F b (sprFieldMprimeAlg F x) := by
  have h : ((sprFieldMprimeAlg F : SprField F 2 9 →+* EM.latticeFunctionField F Mprime)).comp
        (sprDiagFieldEquiv F 2 9 b).toRingHom
      = (torusScaleFieldEquiv F b).toRingHom.comp
          (sprFieldMprimeAlg F : SprField F 2 9 →+* EM.latticeFunctionField F Mprime) := by
    refine IsFractionRing.ringHom_ext (A := Spr F 2 9) (fun p => ?_)
    show sprFieldMprimeAlg F (sprDiagFieldEquiv F 2 9 b
        (algebraMap (Spr F 2 9) (SprField F 2 9) p))
      = torusScaleFieldEquiv F b (sprFieldMprimeAlg F
          (algebraMap (Spr F 2 9) (SprField F 2 9) p))
    rw [sprDiagFieldEquiv_algebraMap, sprDiagHom_torusScale_level]
  exact DFunLike.congr_fun h x

#print axioms sprDiagFieldEquiv_torusScale

end SprTorusEquivariance2

/-! ## §12 ★★★★★★★ **`V3'` 的 ③ 完成：`S_n`-等变（`Spr` 层 ＋ 分式域层）**

§10 给了前提（`permScale` 的 `F`-线性 ＋ `AlgHom` 提升）。本节按**§11 的 R231 战术**
（两侧各自标准形再比）一次收口 `V3'` 的 ③。

| 步 | 件 | 内容 |
|---|---|---|
| 0 | ★★★★★ `sprPermAlgEquiv_X` | `S_n` 在变元上：`sprPermAlgEquiv σ (X v) = X (sprPermIdx σ v)` |
| 0' | ★★★★★ `actM_mprimeBasis` | **`S_n` 在 `M_2'` 基上**：`actM σ (mprimeBasis i) = mprimeBasis (idxPerm σ i)` |
| 1 | ★★★★★ `permScale_X_std` | **右端标准形**：`permScaleFieldEquiv σ (Φ (X v)) = Φ (X (sprPermIdx σ v))` |
| 2 | ★★★★★★ `sprPermAlgEquiv_permScale_level` | **`Spr` 层**（`MvPolynomial.algHom_ext`） |
| 3 | ★★★★★★★ `sprPermFieldEquiv_permScale` | **分式域层**（`IsFractionRing.ringHom_ext`） |

**两侧的相遇点**：③ 的两式都化成 `Φ (algebraMap (X (sprPermIdx σ v)))`。
右边化归链的关键一步是 **`sprIdxEquivIdx_perm`（§2）** 与 **`actM_mprimeBasis`**：
`actM σ` 在 `mprimeBasis` 上是 `idxPerm σ`，而 `sprIdxEquivIdx` 把 `sprPermIdx σ` 送到
`idxPerm σ` —— **§2 的"S_n-等变识别"在此兑现**。即 §2 的
`sprIdxEquivIdx_perm` 不是装饰，它是 ③ 的**唯一汇合点**（正如 §5 的权字典是 ② 的汇合点）。

**工艺（2 条，本轮实测）**：
* **R233 `sprIdxEquivIdx_perm` 的使用方向**：`permScale_X_std` 里需把
  `idxPerm σ (sprIdxEquivIdx v)` **反**写成 `sprIdxEquivIdx (sprPermIdx σ v)`，
  故要 **`← sprIdxEquivIdx_perm`**。写成正向报 "Did not find an occurrence of the pattern
  `sprIdxEquivIdx ((sprPermIdx ?σ) ?i)`" —— 目标里根本没有正向的那个形式。
* **R234 `sprPerm 2 9 σ` 与 `sprPermIdx σ` 定义相同**（都是
  `Equiv.sumCongr σ (Equiv.prodCongr σ (Equiv.prodCongr σ (Equiv.refl _)))`），
  故 §2 的 `sprPermIdx` 与仓内既有的 `sprPerm` **可互换**；`sprPermAlgEquiv_X`
  直接用 `sprPermIdx_inl/_inr` 即得。**MvPolynomial.algHom_ext` 的变量检查用 `sprPermAlgEquiv_X`
  而非另建 `_std`**（③ 的左端标准形就是这一条）。

**射程（勿夸大）**：③ **已完成**。`V3'` 的 ④（固定点对应）⑤（`V3'` 本身）**未建**；
输入 (i)／(ii) **未证**；`UD` **未定义**；`ZEqNFixed` —— **未证**。**H2 见文件头「当前状态」。** -/


section SprPermEquivariance2

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ `S_n` 在 `S'` 的**变元**上：`X v ↦ X (sprPermIdx σ v)`（R234）。 -/
theorem sprPermAlgEquiv_X (F : Type) [Field F] (σ : Equiv.Perm (Fin 9)) (v : SprIdx 2 9) :
    sprPermAlgEquiv F 2 9 σ (MvPolynomial.X v)
      = MvPolynomial.X (sprPermIdx σ v) := by
  rcases v with i | ⟨⟨i, j⟩, k⟩
  · rw [sprPermAlgEquiv_X_inl, sprPermIdx_inl]
  · rw [sprPermAlgEquiv_X_inr, sprPermIdx_inr]

#print axioms sprPermAlgEquiv_X

/-- ★★★★★ **`S_n` 在 `M_2'` 的基上**：`actM σ (mprimeBasis i) = mprimeBasis (idxPerm σ i)`。 -/
theorem actM_mprimeBasis (σ : G.Gp 3) (i : Idx) :
    actM σ (mprimeBasis i) = mprimeBasis (idxPerm σ i) := by
  refine mprimeEquivFun.injective ?_
  rw [mprimeEquivFun_actM_basis, mprimeEquivFun, Module.Basis.equivFun_apply,
    Module.Basis.repr_self]

#print axioms actM_mprimeBasis

/-- ★★★★★ **③ 右端标准形**：`permScaleFieldEquiv σ (Φ (X v)) = Φ (X (sprPermIdx σ v))`。 -/
theorem permScale_X_std (F : Type) [Field F] (σ : Equiv.Perm (Fin 9)) (v : SprIdx 2 9) :
    permScaleFieldEquiv F σ (sprFieldMprimeAlg F
        (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v)))
      = sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9)
          (MvPolynomial.X (sprPermIdx σ v))) := by
  rw [sprFieldMprimeAlg_X, permScaleFieldEquiv_algebraMap, permScale_single]
  rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (mprimeBasis (sprIdxEquivIdx v))))
      = mprimeBasis (sprIdxEquivIdx v) from rfl, actM_mprimeBasis, ← sprIdxEquivIdx_perm]
  exact (sprFieldMprimeAlg_X F (sprPermIdx σ v)).symm

#print axioms permScale_X_std

/-- ★★★★★★ **③ 的 `Spr` 层**（`S_n`-等变在多项式环上）。 -/
theorem sprPermAlgEquiv_permScale_level (F : Type) [Field F] (σ : Equiv.Perm (Fin 9))
    (p : Spr F 2 9) :
    sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) (sprPermAlgEquiv F 2 9 σ p))
      = permScaleFieldEquiv F σ
          (sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9) p)) := by
  have h : (sprFieldMprimeAlg F : SprField F 2 9 →ₐ[F] EM.latticeFunctionField F Mprime).comp
        ((Algebra.algHom F (Spr F 2 9) (SprField F 2 9)).comp
          (sprPermAlgEquiv F 2 9 σ).toAlgHom)
      = (permScaleAlgHom F σ).comp
          ((sprFieldMprimeAlg F : SprField F 2 9 →ₐ[F] EM.latticeFunctionField F Mprime).comp
            (Algebra.algHom F (Spr F 2 9) (SprField F 2 9))) := by
    refine MvPolynomial.algHom_ext (fun v => ?_)
    show sprFieldMprimeAlg F (algebraMap (Spr F 2 9) (SprField F 2 9)
        (sprPermAlgEquiv F 2 9 σ (MvPolynomial.X v)))
      = permScaleFieldEquiv F σ (sprFieldMprimeAlg F
          (algebraMap (Spr F 2 9) (SprField F 2 9) (MvPolynomial.X v)))
    rw [sprPermAlgEquiv_X, permScale_X_std]
  exact DFunLike.congr_fun h p

#print axioms sprPermAlgEquiv_permScale_level

/-- ★★★★★★★ **③ 的分式域层（`S_n`-等变）** —— `V3'` 第 2 项的 `S_n` 半**完成**。 -/
theorem sprPermFieldEquiv_permScale (F : Type) [Field F] (σ : Equiv.Perm (Fin 9))
    (x : SprField F 2 9) :
    sprFieldMprimeAlg F (sprPermFieldEquiv F 2 9 σ x)
      = permScaleFieldEquiv F σ (sprFieldMprimeAlg F x) := by
  have h : ((sprFieldMprimeAlg F : SprField F 2 9 →+* EM.latticeFunctionField F Mprime)).comp
        (sprPermFieldEquiv F 2 9 σ).toRingHom
      = (permScaleFieldEquiv F σ).toRingHom.comp
          (sprFieldMprimeAlg F : SprField F 2 9 →+* EM.latticeFunctionField F Mprime) := by
    refine IsFractionRing.ringHom_ext (A := Spr F 2 9) (fun p => ?_)
    show sprFieldMprimeAlg F (sprPermFieldEquiv F 2 9 σ
        (algebraMap (Spr F 2 9) (SprField F 2 9) p))
      = permScaleFieldEquiv F σ (sprFieldMprimeAlg F
          (algebraMap (Spr F 2 9) (SprField F 2 9) p))
    rw [sprPermFieldEquiv_algebraMap, sprPermAlgEquiv_permScale_level]
  exact DFunLike.congr_fun h x

#print axioms sprPermFieldEquiv_permScale

end SprPermEquivariance2

/-! ## §13 ★★★★★★★★ **`V3'` 解除**：④ 固定点对应 ＋ ⑤ 终局输入 (iii) 成为定理

v16 §4.3 的 ④⑤。§11（② `T`-等变）与 §12（③ `S_n`-等变）已给出两半，本节把
**固定点**与**同构**两层做完 —— **终局输入 (iii) `V3'` 从此是定理，不再是具名假设。**

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprFieldNFixed_iff_torus_perm` | **④**：`x` 被 `N` 固定 ⟺ `Φ x` 被 `N` 固定（`Φ = sprFieldMprimeAlg`） |
| ★★★★★★ `sprFieldNFixed_iff_mem` | **④（`Subalgebra` 形态）**：`x ∈ K'^N ⟺ Φ x ∈ F(M_2')^N` |
| ★★★★★★★★ `sprNFixedEquiv` | **⑤ 的见证**：`↥(sprNFixedAlg F 2 9) ≃ₐ[F] ↥(NFixedAlg F)` |
| ★★★★★★★★ `v3prime` | **`Nonempty (↥(sprNFixedAlg F 2 9) ≃ₐ[F] ↥(NFixedAlg F))`** —— 终局输入 (iii) |

**证明结构（④ 的两个方向都是"搬等变式"）**：
* `→`：`sprDiagFieldEquiv b x = x` ⟹ `torusScaleFieldEquiv b (Φ x) = Φ (sprDiagFieldEquiv b x) = Φ x`
  （用 ② 的**反向**读法 ＋ `hT`）；
* `←`：由 ② 与 `Φ` 的**单射性**（`AlgEquiv.injective`）—— 这就是为什么 ② 必须给出
  `Φ (sprDiagFieldEquiv b x) = …` 的**等式形态**而非某个弱形式。

**⑤ 的结构**：`AlgEquiv.ofBijective` ＋ 载体映射 `x ↦ ⟨Φ x, ④.mp x.2⟩`；
单射由 `Φ` 单射；**满射由 `Φ` 的逆 ＋ `④.mpr`**（对 `y : ↥(NFixedAlg F)`，
取 `x := Φ⁻¹ y`，`④.mpr` 保证 `x` 落在 `↥(sprNFixedAlg)`）。

**★ 射程（务必按此读，勿夸大）**：
* **`V3'` 解除 = 终局输入 (iii) 解除**。它**只**依赖 `[Field F] [CharZero F]`，
  **不再**依赖任何具名输入。
* 但 **`ZEqNFixed` 仍不是定理**：它还要
  **(i) `ZInSpr`**（`Z ⊆ K'`，`GenericInv` §173 具名、**未证**）与
  **(ii) `K'^N ⊆ Z`**（**未建**，其前半 `UD = M_n(K')^N` 所需的 **`UD` 本仓尚未定义**）。
* 另：`ZEqNFixed` 的两端是 `↥(ZCanon F 2 9 D)` 与 `↥(NFixedAlg F)`，而本节的左端是
  `↥(sprNFixedAlg F 2 9)` —— **(i)+(ii) 要做的正是把 `ZCanon` 识别成 `sprNFixedAlg`
  的像**。故 `ZEqNFixed` **未证**，**H2 见文件头「当前状态」。**

**工艺（1 条）**：**R235 `AlgEquiv.ofBijective` 的 `commutes'`／`map_*'` 全用
`Subtype.ext` ＋ `exact map_one _`（或 `.commutes a`）的"抬到载体再落回"套路** ——
`Subalgebra` 的载体定理对 `map_one/map_mul/map_zero/map_add/commutes` 一律可用，
**不必**先证 `Subtype` 层的等式再 `ext`。 -/


section SprV3Prime

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★★ **④ 固定点对应**：`x` 被 `N` 固定 ⟺ `Φ x` 被 `N` 固定（`Φ = sprFieldMprimeAlg`）。 -/
theorem sprFieldNFixed_iff_torus_perm (F : Type) [Field F] (x : SprField F 2 9) :
    sprFieldNFixed F 2 9 x
      ↔ (TFixed F (sprFieldMprimeAlg F x) ∧ SFixed F (sprFieldMprimeAlg F x)) := by
  constructor
  · rintro ⟨hT, hS⟩
    refine ⟨fun b => ?_, fun σ => ?_⟩
    · rw [← sprDiagFieldEquiv_torusScale F b x, hT b]
    · rw [← sprPermFieldEquiv_permScale F σ x, hS σ]
  · rintro ⟨hT, hS⟩
    refine ⟨fun b => ?_, fun σ => ?_⟩
    · refine (sprFieldMprimeAlg F).injective ?_
      rw [sprDiagFieldEquiv_torusScale, hT b]
    · refine (sprFieldMprimeAlg F).injective ?_
      rw [sprPermFieldEquiv_permScale, hS σ]

#print axioms sprFieldNFixed_iff_torus_perm

/-- ★★★★★★ **④（`Subalgebra` 形态）**：`x ∈ K'^N ⟺ Φ x ∈ F(M_2')^N`。 -/
theorem sprFieldNFixed_iff_mem (F : Type) [Field F] [CharZero F] (x : SprField F 2 9) :
    sprFieldNFixed F 2 9 x ↔ sprFieldMprimeAlg F x ∈ NFixedAlg F := by
  rw [mem_NFixedAlg, sprFieldNFixed_iff_torus_perm]

#print axioms sprFieldNFixed_iff_mem

/-- ★★★★★★★★ **⑤ 的见证**：`K'^N ≅ F(M_2')^N` 作为 `F`-代数。 -/
noncomputable def sprNFixedEquiv (F : Type) [Field F] [CharZero F] :
    ↥(sprNFixedAlg F 2 9) ≃ₐ[F] ↥(NFixedAlg F) :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨sprFieldMprimeAlg F (x : SprField F 2 9),
        (sprFieldNFixed_iff_mem F (x : SprField F 2 9)).mp
          ((mem_sprNFixedAlg F 2 9).mp x.2)⟩
      map_one' := by
        refine Subtype.ext ?_
        exact map_one _
      map_mul' := by
        intro a b
        refine Subtype.ext ?_
        exact map_mul _ a.1 b.1
      map_zero' := by
        refine Subtype.ext ?_
        exact map_zero _
      map_add' := by
        intro a b
        refine Subtype.ext ?_
        exact map_add _ a.1 b.1
      commutes' := by
        intro a
        refine Subtype.ext ?_
        exact (sprFieldMprimeAlg F).commutes a }
    (by
      constructor
      · intro x y h
        refine Subtype.ext ?_
        exact (sprFieldMprimeAlg F).injective (Subtype.ext_iff.mp h)
      · intro y
        refine ⟨⟨(sprFieldMprimeAlg F).symm (y : EM.latticeFunctionField F Mprime), ?_⟩, ?_⟩
        · rw [mem_sprNFixedAlg]
          refine (sprFieldNFixed_iff_mem F _).mpr ?_
          rw [AlgEquiv.apply_symm_apply]
          exact (mem_NFixedAlg F).mp y.2
        · refine Subtype.ext ?_
          exact (sprFieldMprimeAlg F).apply_symm_apply _)

#print axioms sprNFixedEquiv

/-- ★★★★★★★★ **`V3'` 成立** —— 终局输入 (iii) **解除**（不再是具名假设）。 -/
theorem v3prime (F : Type) [Field F] [CharZero F] :
    Nonempty (↥(sprNFixedAlg F 2 9) ≃ₐ[F] ↥(NFixedAlg F)) :=
  ⟨sprNFixedEquiv F⟩

#print axioms v3prime

end SprV3Prime

/-! ## §14 ★★★★★★★★ **`ZEqNFixed` 归约为单一语句 `Z ≅ K'^N`** ＋ 两个包含的精确登记

§13 解除了 `V3'`。本节把 `V3'` **吸收进 `ZEqNFixed`**，于是 H2 的剩余数学内容
收缩成**一条**语句（`prop:14.19` 的 `Z` 半），并把它的两条包含**精确登记**。

| 件 | 内容 |
|---|---|
| ★★★★★★ `zEqNFixed_iff_ZCanonEquiv` | **`ZEqNFixed ⟺ Nonempty (↥(ZCanon) ≃ₐ[F] ↥(sprNFixedAlg))`** |
| ★★★★★★ `zEqNFixed_of_ZCanonEquiv` | 该归约的正向使用 |
| ★★★★★ `NFixedLeZ` | **输入 (ii) 的精确形状**：`K'^N ⊆ Z`（沿 `sprToSField`） |
| ★★★★★ `sprNFixedToZCanon` | 由 (ii) 得 **`K'^N → Z` 作为 `F`-代数同态** |
| ★★★★★ `sprNFixedToZCanon_injective` | 它**单射**（`sprToSField` 单射，§163） |
| ★★★★★ `ZLeNFixed` | **输入 (i) 的精确（强）形状**：`Z ⊆ K'^N` |
| ★★★★★★★★ `zEqNFixed_of_inclusions` | **两条包含 ⟹ `ZEqNFixed`** |

**★ 这一步的意义（`ZEqNFixed` 的精确剩余）**：

```
ZEqNFixed F D  ⟺  ZCanon F 2 9 D ≅ sprNFixedAlg F 2 9
               ⟸  (ii) K'^N ⊆ Z    -- 本节的 NFixedLeZ
                ＋ (i') Z ⊆ K'^N    -- 本节的 ZLeNFixed（强于旧的 ZInSpr）
```

`V3'`（`↥(sprNFixedAlg) ≅ ↥(NFixedAlg)`）已被 §13 解除，故它**不再出现在剩余里**。
**⟹ 三条款具名输入收缩为两条包含**，且两者都是 `prop:14.19` 的 `Z` 半（`Z = K'^N`）。

**为什么 `ZLeNFixed` 强于旧 `ZInSpr`**：`ZInSpr` 只要求 `Z` 的每个生成元落在
`K'` 的**像**里（不要求该像元 `N`-固定）；`ZLeNFixed` 要求每个 `z ∈ Z` 都是
**某个 `N`-固定元**的像 —— 这正是装配中"满射"所需的那一半（否则 `z` 的原像可能不
`N`-固定，`sprNFixedToZCanon` 就不满射）。

**工艺（2 条，本轮实测）**：
* **R236 `AlgEquiv.ofBijective` 的方向要看清**：`sprNFixedToZCanon` 是
  `sprNFixedAlg → ZCanon`，而归约式要的是 `ZCanon ≃ sprNFixedAlg`
  ⟹ 须取 **`.symm`**（写反报 "has type `↥(sprNFixedAlg) →ₐ ↥(ZCanon)` but expected
  `↥(ZCanon) →ₐ ↥(sprNFixedAlg)`"）。
* **R237 `IntermediateField.subset_adjoin` 只给 `s ⊆ ↑(adjoin F s)`**：
  要把 `D.centK c ∈ ZCanon F 2 9 D` 展开到 `adjoin` 形态，须先
  `show D.centK c ∈ IntermediateField.adjoin F (Set.range D.centK)` 再给 `subset_adjoin`
  （直接 `exact` 报 "has type `?s ⊆ ↑(adjoin F ?s)`"）。

**射程（勿夸大，逐条）**：
* `NFixedLeZ`（`K'^N ⊆ Z`）**未证**。它的源文论证是
  `c ∈ K'^N ⟹ c·I ∈ M_n(K')^N = UD ⟹ c·I 中心于 M_n(K') ⟹ c ∈ Z(UD) = Z`；
  本仓 **`UD` 尚未定义**（只有 `CentreUDLeZ`／`KPFixedLeZ` 两个**命题**，
  见 `GenericInv` §62），故 (ii) **未建**。
* `ZLeNFixed`（`Z ⊆ K'^N`）**未证**。它强于已具名的 `ZInSpr`（§173），
  剩下的差距正是 **`sprToSField` 与 `N`-作用的等变性**（尚未建）。
* 故 `ZEqNFixed` **未证**，**H2 见文件头「当前状态」。** -/


section SprZEqNFixedReduction

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★★ **`ZEqNFixed` ⟺ `Z ≅ K'^N`** —— `V3'`（§13）被吸收进归约。 -/
theorem zEqNFixed_iff_ZCanonEquiv (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) :
    ZEqNFixed F D
      ↔ Nonempty (↥(ZCanon F 2 9 D) ≃ₐ[F] ↥(sprNFixedAlg F 2 9)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (sprNFixedEquiv F).symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (sprNFixedEquiv F)⟩

#print axioms zEqNFixed_iff_ZCanonEquiv

/-- ★★★★★★ **`ZEqNFixed` 由 `Z ≅ K'^N` 推出**（`V3'` 已在内部）。 -/
theorem zEqNFixed_of_ZCanonEquiv (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9)
    (h : Nonempty (↥(ZCanon F 2 9 D) ≃ₐ[F] ↥(sprNFixedAlg F 2 9))) :
    ZEqNFixed F D :=
  (zEqNFixed_iff_ZCanonEquiv F D).mpr h

#print axioms zEqNFixed_of_ZCanonEquiv

/-- ★★★★★ **输入 (ii) 的精确形状**：`K'^N ⊆ Z`（沿 `sprToSField`）。 -/
def NFixedLeZ (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
    sprToSField F 2 9 k₀ hk₀ x ∈ ZCanon F 2 9 D

#print axioms NFixedLeZ

/-- ★★★★★ **由 (ii) 得 `K'^N → Z` 作为 `F`-代数同态**。 -/
noncomputable def sprNFixedToZCanon (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (h : NFixedLeZ F D k₀ hk₀) :
    ↥(sprNFixedAlg F 2 9) →ₐ[F] ↥(ZCanon F 2 9 D) where
  toFun x := ⟨sprToSField F 2 9 k₀ hk₀ (x : SprField F 2 9),
    h _ ((mem_sprNFixedAlg F 2 9).mp x.2)⟩
  map_one' := by
    refine Subtype.ext ?_
    exact map_one _
  map_mul' := by
    intro a b
    refine Subtype.ext ?_
    exact map_mul _ a.1 b.1
  map_zero' := by
    refine Subtype.ext ?_
    exact map_zero _
  map_add' := by
    intro a b
    refine Subtype.ext ?_
    exact map_add _ a.1 b.1
  commutes' := by
    intro a
    refine Subtype.ext ?_
    exact (sprToSField F 2 9 k₀ hk₀).commutes a

#print axioms sprNFixedToZCanon

/-- `sprNFixedToZCanon` 是**单射**（`sprToSField` 单射，§163）。 -/
theorem sprNFixedToZCanon_injective (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (h : NFixedLeZ F D k₀ hk₀) :
    Function.Injective (sprNFixedToZCanon F D hk₀ h) := by
  intro x y hxy
  refine Subtype.ext ?_
  exact sprToSField_injective F 2 9 k₀ hk₀ (Subtype.ext_iff.mp hxy)

#print axioms sprNFixedToZCanon_injective

/-- ★★★★★ **输入 (i) 的精确（强）形状**：`Z ⊆ K'^N`。 -/
def ZLeNFixed (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ z ∈ ZCanon F 2 9 D, ∃ x : SprField F 2 9,
    sprFieldNFixed F 2 9 x ∧ sprToSField F 2 9 k₀ hk₀ x = z

#print axioms ZLeNFixed

/-- ★★★★★★★★ **`ZEqNFixed` 由两个包含推出** —— H2 的剩余数学内容就是这两条包含。 -/
theorem zEqNFixed_of_inclusions (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h2 : NFixedLeZ F D k₀ hk₀) (h3 : ZLeNFixed F D k₀ hk₀) :
    ZEqNFixed F D := by
  refine zEqNFixed_of_ZCanonEquiv F D ⟨(AlgEquiv.ofBijective
    (sprNFixedToZCanon F D hk₀ h2)
    ⟨sprNFixedToZCanon_injective F D hk₀ h2, ?_⟩).symm⟩
  intro z
  obtain ⟨x, hx, hxz⟩ := h3 z z.2
  exact ⟨⟨x, (mem_sprNFixedAlg F 2 9).mpr hx⟩, by
    refine Subtype.ext ?_
    show sprToSField F 2 9 k₀ hk₀ x = (z : SField F 2 9)
    exact hxz⟩

#print axioms zEqNFixed_of_inclusions

/-! ## §14b ★★★★★★★★ **剩余内容收成一条已发表命题**（Saltman `prop:14.19` 的 `Z` 半）

§14 把 `ZEqNFixed` 归约成**两条内部包含** `NFixedLeZ`／`ZLeNFixed`。本节说明这两条合起来
**恰是一条已发表命题的后半**：

> Saltman 1999, *Lectures on Division Algebras*, Chapter 14, `prop:14.19`
> （`raw/Saltman1999ch14.tex:368`，逐字）：
> `\(UD(F,n,r) = M_n(K')^N\)` and `\(Z(F,n,r) = K'^N\)`.

本节把**后半**（`Z = K'^N`）按本仓形态具名为 `SaltmanZEqNFixed`
（`ZCanon` 恰是 `K'` 的 `N`-固定元沿 `sprToSField` 的像），并机检：

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `SaltmanZEqNFixed` | `Z = K'^N` 的本仓形态（**唯一剩余输入**） |
| ★★★★★ `saltman_iff_inclusions` | 它 **⟺** §14 的两条包含（`iff` 的两个方向） |
| ★★★★★★★★ `zEqNFixed_of_saltman` | **`ZEqNFixed` ⟸ Saltman `prop:14.19` 后半** |
| ★★★★★★★★ `h2_of_saltman` | **H2 ⟸ Saltman `prop:14.19` 后半** |

**意义**：H2 的剩余内容从此**不再是 KB 内部自造的谓词**，而是**一条有源锚、有已发表证明的
命题**。文献锚：`raw/Saltman1999ch14.tex:368`（陈述）＋ `:375–391`（证明路径：
`lem:14.20` 的 `F(M_r) = F(M_r')^T` ⟹ `K'^N = (K'^T)^{S_n}`，另一半走 `UD = M_n(K')^N`
与 `Z = Z(UD)`）。**⚠ 该笔记的 `pdf_number` 是幽灵号，引用一律用 label `prop:14.19`**（L41）。

**射程（勿夸大）**：本节只做**归约**。`SaltmanZEqNFixed` **未证**；`hZ` 未证；
**H2 见文件头「当前状态」**（`h2_of_saltman` 仍带 `SaltmanZEqNFixed` 前提，是该路线的条件版）。 -/

/-- ★★★★★★★★ **Saltman `prop:14.19` 的 `Z` 半**（`raw/Saltman1999ch14.tex:368` 逐字：
`\(UD(F,n,r) = M_n(K')^N\)` and `\(Z(F,n,r) = K'^N\)` 的**后半**），
本仓形态 ＝ `ZCanon` 恰是 `K'` 的 `N`-固定元沿 `sprToSField` 的像。 -/
def SaltmanZEqNFixed (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ z : SField F 2 9, z ∈ ZCanon F 2 9 D ↔
    ∃ x : SprField F 2 9, sprFieldNFixed F 2 9 x ∧ sprToSField F 2 9 k₀ hk₀ x = z

#print axioms SaltmanZEqNFixed

/-- `SaltmanZEqNFixed` 拆成 §14 登记的两条包含（`iff` 的两个方向）。 -/
theorem saltman_iff_inclusions (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) :
    SaltmanZEqNFixed F D k₀ hk₀
      ↔ (NFixedLeZ F D k₀ hk₀ ∧ ZLeNFixed F D k₀ hk₀) := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun z hz => (h z).mp hz⟩
    exact (h (sprToSField F 2 9 k₀ hk₀ x)).mpr ⟨x, hx, rfl⟩
  · rintro ⟨h2, h3⟩ z
    constructor
    · intro hz
      exact h3 z hz
    · rintro ⟨x, hx, rfl⟩
      exact h2 x hx

#print axioms saltman_iff_inclusions

/-- ★★★★★★★★ **`ZEqNFixed` ⟸ Saltman `prop:14.19` 的 `Z` 半** —— H2 的剩余内容
**只有一条**、且它是**已发表命题**（Saltman 1999, ch14, `prop:14.19` 后半）。 -/
theorem zEqNFixed_of_saltman (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h : SaltmanZEqNFixed F D k₀ hk₀) : ZEqNFixed F D := by
  obtain ⟨h2, h3⟩ := (saltman_iff_inclusions F D hk₀).mp h
  exact zEqNFixed_of_inclusions F D hk₀ h2 h3

#print axioms zEqNFixed_of_saltman

/-- **H2 本身**，以 Saltman `prop:14.19` 的 `Z` 半为唯一输入。 -/
theorem h2_of_saltman (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h : SaltmanZEqNFixed F D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_saltman F D hk₀ h)

#print axioms h2_of_saltman

end SprZEqNFixedReduction

/-! ## §15 ★★★★★ **H2 的精确剩余收成三条具名输入**（`ZEqNFixed` 的最终形态）

§14 把 `ZEqNFixed` 归约成"两条包含"，并把 `ZLeNFixed`（`Z ⊆ K'^N`）登记为强形状。
本节把 `ZLeNFixed` **再分解**成两条各有一半路线的输入，于是

```
ZEqNFixed F D  ⟸  (i)   ZInSpr            -- 已具名（GenericInv §173），未证
                ＋ (ii)  NFixedLeZ         -- 本节 §14，未证（需 UD）
                ＋ (i'') ZPreimageNFixed   -- 本节新登记，未证（需 sprToSField 的 N-等变性）
```

| 件 | 内容 |
|---|---|
| ★★★★★ `ZPreimageNFixed` | **输入 (i'')**：`Z` 的 `K'`-原像都 `N`-固定 |
| ★★★★★★ `zLeNFixed_of_inputs` | `ZLeNFixed ⟸ ZInSpr ＋ ZPreimageNFixed` |
| ★★★★★★★★ `zEqNFixed_of_three_inputs` | **`ZEqNFixed ⟸ 三条输入`** —— H2 的**最终形态** |

**★ 为什么 `ZLeNFixed` 要拆成 (i) ＋ (i'')**：`ZLeNFixed` 要求每个 `z ∈ Z` 是
**某个 `N`-固定元**的像。这两件事**来源完全不同**：
* **(i) `ZInSpr`**（`Z ⊆ range (sprToSField)`）给**存在性**——`z = sprToSField x` 的 `x` 存在
  （由 §173 的 `ZCanon_le_sprToSFieldRange` 把 `ZInSpr` 转成 `Z ≤ fieldRange` 后
  `AlgHom.mem_fieldRange` 取出）。**这是 `prop:14.19` 的 `Z` 半（`Z ⊆ K'`）。**
* **(i'') `ZPreimageNFixed`** 给**那个 `x` 是 `N`-固定的**。
  它的数学来源是 **`sprToSField` 与 `N`-作用的等变性** ＋ **`Z` 被 `PGL` 固定**
  （§`phiK_fixes_ZCanon`）：若 `sprToSField (sprDiagFieldEquiv b x)
  = phiKAlgEquiv (diag b) (sprToSField x)` 且后者 `= sprToSField x`，则由
  `sprToSField` 单射得 `sprDiagFieldEquiv b x = x`。

**工艺（1 条，本轮实测）**：**R238 `sprToSFieldRange` 是 `IntermediateField`，
其成员判据要用 `AlgHom.mem_fieldRange`**：`rw [sprToSFieldRange, AlgHom.mem_fieldRange]`
把 `z ∈ sprToSFieldRange …` 换成 `∃ x, sprToSField x = z`；直接 `obtain` 不行
（`sprToSFieldRange` 是 `def`，R220 型不展开）。

**射程（勿夸大，三条逐条给路线）**：
* **(i) `ZInSpr`**：**未证**。源文 `prop:14.19` 的 `Z` 半（`Z = K'^N` 的 `⊆`）。
* **(ii) `NFixedLeZ`**：**未证**。需 `UD` —— 本仓**`UD` 尚未定义**
  （只有 `CentreUDLeZ`／`KPFixedLeZ` 两个**命题**，`GenericInv` §62）。
* **(i'') `ZPreimageNFixed`**：**未证**。需 **`sprToSField` 的 `N`-等变性**（尚未建）：
  `sprToS`（§128）与 `S` 侧 `phiKAlgEquiv (diag b)`／`phiKAlgEquiv (P_σ)` 的等变性，
  再沿分式域延拓。**本轮检索确认该等变性不在库**（`GenericInv` 里 `sprToS` 只有
  `sprToS_injective` 一条引理）。
* 故 `ZEqNFixed` **未证**，**H2 见文件头「当前状态」。** -/


section SprThreeInputs

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **输入 (i'')**：`Z` 的 `K'`-原像都 `N`-固定。 -/
def ZPreimageNFixed (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ x : SprField F 2 9,
    sprToSField F 2 9 k₀ hk₀ x ∈ ZCanon F 2 9 D → sprFieldNFixed F 2 9 x

#print axioms ZPreimageNFixed

/-- ★★★★★★ **`ZLeNFixed` 由 (i) ＋ (i'') 推出**。 -/
theorem zLeNFixed_of_inputs (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (h1 : ZInSpr F 2 9 D k₀ hk₀)
    (h4 : ZPreimageNFixed F D k₀ hk₀) : ZLeNFixed F D k₀ hk₀ := by
  intro z hz
  have hz' : z ∈ sprToSFieldRange F 2 9 k₀ hk₀ :=
    ZCanon_le_sprToSFieldRange F 2 9 D hk₀ h1 hz
  rw [sprToSFieldRange, AlgHom.mem_fieldRange] at hz'
  obtain ⟨x, hx⟩ := hz'
  exact ⟨x, h4 x (hx ▸ hz), hx⟩

#print axioms zLeNFixed_of_inputs

/-- ★★★★★★★★ **`ZEqNFixed` 由三条具名输入推出** —— H2 的**最终形态**。 -/
theorem zEqNFixed_of_three_inputs (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h1 : ZInSpr F 2 9 D k₀ hk₀) (h2 : NFixedLeZ F D k₀ hk₀)
    (h4 : ZPreimageNFixed F D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_inclusions F D hk₀ h2 (zLeNFixed_of_inputs F D hk₀ h1 h4)

#print axioms zEqNFixed_of_three_inputs

end SprThreeInputs

/-! ## §16 **输入 (i'') 路线第一块：对角矩阵的单位化 `diagUnit`**

§15 把 (i'') `ZPreimageNFixed` 的来源定成 **`sprToSField` 的 `N`-等变性**。
该等变性要在 `S`-侧用 `phiA`（`PGL.lean` 的 `φ_A`）陈述，而 `phiA` 吃的是
**`GL_n(F)` 的单位**，对角环面元 `b : Fin 9 → Fˣ` 必须先**单位化**。本节即此。

**★ 约定核对（本轮实做，务必记住）**：`phiA` 的生成元公式是
`phiGen A e = (A⁻¹ X_k A)_{ij}`（`PGL.lean:47`），故对 `A = diag(c)`：
`(diag(c)⁻¹ X diag(c))_{ij} = c_i · c_j⁻¹ · (X)_{ij}`。而 `sprDiagHom b` 给 `b_i · b_j⁻¹`。
⟹ **`sprDiagHom b` 对应 `phiA (diagUnit b⁻¹)`，不是 `phiA (diagUnit b)`**。
（另：`x_ii` 侧因 `b_i/b_i = 1` 两边都对，故只有 `y` 侧能区分这个约定。）

| 件 | 内容 |
|---|---|
| ★★★★★ `diagUnit` | `b ↦ diag(b) ∈ GL_9(F)`（`val`／`inv` 显式给出） |
| `diagUnit_val` | 计算律 `↑(diagUnit b) = diagonal b` |

**工艺（2 条，本轮实测）**：
* **R239 `Matrix.diagonal_mul_diagonal` 的方向**：可用方向是
  `diagonal d * diagonal e = diagonal (d * e)`（**正向**）。要证
  `diagonal d * diagonal e = 1` 须**先正向** `rw [Matrix.diagonal_mul_diagonal]`
  把两边合成一个 `diagonal (d * e)`，再用 `fun eq` 把 `d * e` 换成 `fun _ => 1`，
  最后 `Matrix.diagonal_one`。**写 `←` 报"找不到落点"**（目标里没有 `diagonal (d*e)` 形态）。
* **R240 `Units` 的 `val_inv`／`inv_val` 目标是 `val * inv = 1`**（`1` 是矩阵的 `1`），
  故须先 `show` 成显式乘积形态再 `rw`；直接 `rw` 会因目标被 `val`／`inv` 定义式
  半展开而落点不对。

**射程（勿夸大）**：本节只给**单位化**。等变性本体
`sprToS ∘ sprDiagHom b = phiA (diagUnit b⁻¹) ∘ sprToS` **未证**（下一轮，
`MvPolynomial.algHom_ext` ＋ `phiGen` 在两类变元上的计算）；
其分式域延拓与 (i'') 本身亦**未证**。`ZEqNFixed` **未证**，**H2 见文件头「当前状态」。** -/


section SprDiagUnit

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **对角矩阵的单位化**：`b : Fin 9 → Fˣ` ↦ `diag(b) ∈ GL_9(F)`。 -/
noncomputable def diagUnit (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    (Matrix (Fin 9) (Fin 9) F)ˣ where
  val := Matrix.diagonal (fun i => (b i : F))
  inv := Matrix.diagonal (fun i => (((b i)⁻¹ : Fˣ) : F))
  val_inv := by
    show Matrix.diagonal (fun i => (b i : F))
      * Matrix.diagonal (fun i => (((b i)⁻¹ : Fˣ) : F)) = 1
    rw [Matrix.diagonal_mul_diagonal,
      show (fun i => (b i : F) * (((b i)⁻¹ : Fˣ) : F)) = fun _ => (1 : F) from by
        funext i
        simp]
    exact Matrix.diagonal_one
  inv_val := by
    show Matrix.diagonal (fun i => (((b i)⁻¹ : Fˣ) : F))
      * Matrix.diagonal (fun i => (b i : F)) = 1
    rw [Matrix.diagonal_mul_diagonal,
      show (fun i => (((b i)⁻¹ : Fˣ) : F) * (b i : F)) = fun _ => (1 : F) from by
        funext i
        simp]
    exact Matrix.diagonal_one

#print axioms diagUnit

/-- `↑(diagUnit b) = diagonal b`（计算律）。 -/
@[simp] lemma diagUnit_val (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    ((diagUnit F b : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F)
      = Matrix.diagonal (fun i => (b i : F)) := rfl

#print axioms diagUnit_val

end SprDiagUnit

/-! ## §17 **输入 (i'') 路线第二块：`diagUnit` 的两条计算律**

§16 建了 `diagUnit`。本节给出下一轮 `phiGen` 计算所必需的两条：
* `(diagUnit b)⁻¹` 的值是 `diagonal b⁻¹`；
* `constMat` 把对角单位送到 `S` 里的对角矩阵。

| 件 | 内容 |
|---|---|
| ★★★★★ `diagUnit_inv_val` | `↑((diagUnit b)⁻¹) = diagonal (b⁻¹)` |
| ★★★★ `constMat_diagUnit` | `constMat (↑(diagUnit b)) = diagonal (algebraMap ∘ b)` |

**工艺（1 条，本轮实测）**：**R241 `constMat_diagUnit` 用 `ext i j` ＋ `Matrix.map_apply`
＋ 两次 `Matrix.diagonal_apply` ＋ `by_cases (i = j)` ＋ `simp`** ——
`constMat` 是 `A.map (algebraMap F (S))`，故对角矩阵的像逐项落在 `algebraMap` 上；
**不要**试图 `rw [constMat]` 后直接 `simp`（`Matrix.map` 不透明，R188 型）。

**射程（勿夸大）**：本节只给**计算律**。等变性本体
`sprToS ∘ sprDiagHom b = phiA (diagUnit b⁻¹) ∘ sprToS` **未证**；
其核心计算 `phiGen (diagUnit b⁻¹) ⟨k,i,j⟩ = (b_i/b_j) · X(k,i,j)` **本轮未成**
（`genericMatrix` 的展开卡住：报 "Failed to rewrite using equation theorems for
`genericMatrix`"，是 R188／R220 型的"`def` 不按 `rw` 展开"问题；下一轮改用
`genericMatrix_apply` 或 `show` 逐项展开）。
故 (i'') 本身 **未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/


section SprDiagUnit2

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ `(diagUnit b)⁻¹` 的值就是 `diagonal b⁻¹`（`rfl`）。 -/
theorem diagUnit_inv_val (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    (((diagUnit F b)⁻¹ : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F)
      = Matrix.diagonal (fun i => (((b i)⁻¹ : Fˣ) : F)) := rfl

#print axioms diagUnit_inv_val

/-- ★★★★ `constMat` 在对角单位上的值。 -/
theorem constMat_diagUnit (F : Type) [Field F] (r : ℕ) (b : Fin 9 → Fˣ) :
    constMat F r 9 ((diagUnit F b : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F)
      = Matrix.diagonal (fun i => algebraMap F (S F r 9) (b i : F)) := by
  rw [diagUnit_val, constMat]
  ext i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

#print axioms constMat_diagUnit

end SprDiagUnit2

/-! ## §18 **输入 (i'') 路线第三块：`diagUnit` 的往返律**

| 件 | 内容 |
|---|---|
| ★★★★ `diagUnit_inv_inv` | `↑((diagUnit b⁻¹)⁻¹) = ↑(diagUnit b)` |

**用途**：`phiGen (diagUnit b⁻¹) ⟨k,i,j⟩` 的第一因子是 `constMat (↑((diagUnit b⁻¹)⁻¹))`，
须先把它换成 `constMat (↑(diagUnit b))` 才能用 §17 的 `constMat_diagUnit` 落点对角形态。

**★ 死胡同记录（本轮，务必看）**：`phiGen_diagUnit`
（`phiGen (diagUnit b⁻¹) ⟨k,i,j⟩ = (b_i/b_j) · X(k,i,j)`）**本轮再试未成**。
`phiGen` 的 `rw` 展开**已**成功（与第 369 轮记的 `genericMatrix` 卡点不同），
真正的卡点在**矩阵乘法的求和项次序**：`simp only [Matrix.mul_apply, Matrix.diagonal_apply]`
之后目标是

```
((∑ j, (if i = j then algMap ↑(b i) else 0) * genericMatrix F r 9 k j i)
    * if i = j then algMap ↑(b⁻¹ i) else 0) = …
```

—— 注意 `genericMatrix F r 9 k j i` 的**指标次序被交换**、且 `if i = j` 的**两个 `i` 是
不同的绑定变元**（一个来自外层，一个来自被 `simp` 展开的 `∑`）。**正解应是**：
不要用 `simp only` 让 `Matrix.mul_apply` 与 `diagonal_apply` 同时展开（它会重命名绑定变元
并错位指标），而是**手写两步 `Matrix.mul_apply`** ＋ 对每个 `∑` 用
`Finset.sum_eq_single i`／`j`，并**在每一步 `show` 出显式项**（同 R231 的"两侧各自标准形"精神：
先固定 `(D₁ M D₂)_{ij}` 的显式式，再算）。

**射程**：等变性本体、分式域延拓、(i'') 本身 —— 全**未证**。`ZEqNFixed` **未证**，
**H2 见文件头「当前状态」。** -/


section SprDiagUnit3

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★ **对角单位取逆两次回到自身**：`↑((diagUnit b⁻¹)⁻¹) = ↑(diagUnit b)`。 -/
theorem diagUnit_inv_inv (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    (((diagUnit F b⁻¹)⁻¹ : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F)
      = ((diagUnit F b : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F) := by
  rw [diagUnit_inv_val, diagUnit_val]
  congr 1

#print axioms diagUnit_inv_inv

end SprDiagUnit3

/-! ## §19 ★★★★★★★ **`sprToS` 的对角等变性（`Spr` 层）** —— 输入 (i'') 路线第 1–2 步

第 371 轮的死胡同（`phiGen_diagUnit`）**本轮解除**，并一次推进到等变性本体。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `phiGen_diagUnit` | **`phiGen (diagUnit b⁻¹) ⟨k,i,j⟩ = (b_i/b_j) · X(k,i,j)`** |
| ★★★★★★★ `sprToS_sprDiagHom` | **`sprToS ∘ sprDiagHom b = phiA (diagUnit b⁻¹) ∘ sprToS`** |

**★ 死胡同是怎么解除的（R243 的应用，务必记住）**：
369／370／371 三轮用 `Matrix.mul_apply` 的求和展开**全部失败**（`simp` 同时展开
`mul_apply` 与 `diagonal_apply` 会重命名绑定变元并错位指标）。**改道**用
**`Matrix.mul_diagonal`／`Matrix.diagonal_mul`** 这两条**逐项**引理
（`Mathlib/Data/Matrix/Mul.lean:379/384`）——**完全绕开求和**，一轮即成。
残余只剩交换性（`ring` 收）。**教训：优先找"逐项"引理，不要用 `simp` 展开求和。**

**工艺（2 条，本轮实测）**：
* **R242 局部 `have h1` 的 tactic 序列会与主目标纠缠**：把 `h1`（`diagUnit_inv_inv`）
  写成局部 `have … := by rw […]; congr 1; funext i; simp` 时，`simp` 有时把后续 tactic
  作用到主目标上，出现 "No goals to be solved"／"unsolved goals" 交替。
  **正解**：**用已入库的独立引理**（`diagUnit_inv_inv`）直接 `rw`，**不写局部 `have`**。
* **R243 `MvPolynomial.algHom_ext` 的 `show` 会因隐式参数卡住**：
  在 `refine MvPolynomial.algHom_ext (fun v => ?_)` 之后直接写 `show …` 报
  "Application type mismatch"（`sprToS` 的 `n`、`sprDiagHom` 的 `n` 等隐式参数未定）。
  **正解**：先 `simp only [AlgHom.comp_apply]` 把复合拆开，**不写 `show`**，直接 `rcases v`。

**射程（勿夸大，逐条）**：本节做到 **`Spr` 层**。仍缺：
① **分式域延拓** `sprToSField ∘ sprDiagFieldEquiv b = phiKAlgEquiv (diagUnit b⁻¹) ∘ sprToSField`
   （需先证 `phiKAlgEquiv` 在 `S` 上就是 `phiA`，再 `IsFractionRing.ringHom_ext`）；
② **`S_n` 侧同款**（需 `permUnit σ`）；
③ 由 ① ② ＋ `phiK_fixes_ZCanon` 得 (i'')。
故 (i'') **未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/


section SprToSDiagEquivariance

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★★★ **`phiGen` 在对角单位上的值**：`(b_i/b_j) · X(k,i,j)`。

改道路线（见 `wiki/deadend-phiGen-diagUnit.md`）：用 `Matrix.mul_diagonal`／
`Matrix.diagonal_mul` 两条**逐项**引理，绕开 `Matrix.mul_apply` 的求和展开。 -/
theorem phiGen_diagUnit (F : Type) [Field F] (r : ℕ) (b : Fin 9 → Fˣ)
    (k : Fin r) (i j : Fin 9) :
    phiGen F r 9 (diagUnit F b⁻¹) ⟨k, i, j⟩
      = algebraMap F (S F r 9) ((b i : F) * ((b j : F))⁻¹)
        * MvPolynomial.X ⟨k, i, j⟩ := by
  rw [phiGen, diagUnit_inv_inv, constMat_diagUnit, constMat_diagUnit,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [genericMatrix, genericEntry, map_mul, Pi.inv_apply,
    Units.val_inv_eq_inv_val]
  ring

#print axioms phiGen_diagUnit

/-- ★★★★★★★ **`sprToS` 与对角作用的等变性**：
`sprToS ∘ sprDiagHom b = phiA (diagUnit b⁻¹) ∘ sprToS`（§16 的约定：`phiA` 用 `b⁻¹`）。 -/
theorem sprToS_sprDiagHom (F : Type) [Field F] (r : ℕ) (k₀ : Fin r) (b : Fin 9 → Fˣ) :
    (sprToS F (n := 9) k₀).comp (sprDiagHom F r 9 b)
      = (phiA F r 9 (diagUnit F b⁻¹)).comp (sprToS F (n := 9) k₀) := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  simp only [AlgHom.comp_apply]
  rcases v with i | ⟨⟨i, j⟩, k⟩
  · rw [sprDiagHom_X_inl]
    simp only [sprToS, phiA, MvPolynomial.aeval_X, Sum.elim_inl]
    rw [phiGen_diagUnit]
    simp
  · rw [sprDiagHom_X_inr]
    simp only [sprToS, phiA, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Sum.elim_inr,
      map_mul, AlgHom.commutes]
    rw [phiGen_diagUnit]
    simp

#print axioms sprToS_sprDiagHom

end SprToSDiagEquivariance

/-! ## §20 **`phiKAlgEquiv` → `phiA` 的桥接（分式域延拓的前置）**

输入 (i'') 路线第 3 步（分式域延拓）需要 `phiKAlgEquiv` 在 `S` 的像上的计算律。
仓内 `phiKEquiv_algebraMap`（`KAction.lean:51`）是给 **`phiKEquiv`（`≃+*`）** 的；
而 `phiKAlgEquiv` 是 `AlgEquiv.ofRingEquiv (f := phiKEquiv …)` 的**结构包装**，
`rw` 不会穿透包装落点（R220 的邻居）。本节把二者的函数同一性**显式化**。

| 件 | 内容 |
|---|---|
| ★★★★★ `phiKAlgEquiv_eq_phiKEquiv` | `phiKAlgEquiv A x = phiKEquiv A x`（`rfl`） |
| ★★★★★ `phiKAlgEquiv_algebraMap'` | **`phiKAlgEquiv A (algebraMap x) = algebraMap (phiA A x)`** |

**工艺（2 条，本轮实测）**：
* **R244 `AlgEquiv` 包装会挡住 `rw`**：`phiKAlgEquiv` 的定义是
  `AlgEquiv.ofRingEquiv (f := phiKEquiv …) …`，故 `rw [phiKEquiv_algebraMap]` 在
  `phiKAlgEquiv … (algebraMap …)` 上**不落点**。**正解**：先建
  `phiKAlgEquiv_eq_phiKEquiv`（`rfl`）再用它 `rw`。**凡 `≃ₐ` 是 `≃+*` 的包装时，
  先显式化函数同一性。**
* **R245 `RingEquiv.toRingHom` 也会挡 `rw`**：`h : f.comp g.toRingHom = …` 里
  `g.toRingHom (algebraMap …)` 显示为 `.toRingHom` 应用，使
  `rw [g_algebraMap]` 不匹配。**正解**：`simp only [RingHom.comp_apply,
  RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]` 先把包装剥掉。

**射程（勿夸大）**：本节只给**桥接**。分式域延拓本体
`sprToSField ∘ sprDiagFieldEquiv b = phiKAlgEquiv (diagUnit b⁻¹) ∘ sprToSField`
**仍未证**（本轮推进到"`sprDiagFieldEquiv_algebraMap` 已落点、
`sprToSField_algebraMap` 因 `r`／`n` 隐式参数未落点"这一步；
下一轮给 `sprToSField_algebraMap` 显式补 `(r := 2) (n := 9)` 即可望一次成）。
(i'') **未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/


section SprPhiKBridge

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **`phiKAlgEquiv` 与 `phiKEquiv` 的函数同一性**（`rfl`，供 `rw` 落点；R244）。 -/
theorem phiKAlgEquiv_eq_phiKEquiv (F : Type) [Field F] (r n : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (x : SField F r n) :
    phiKAlgEquiv F r n A x = phiKEquiv F r n A x := rfl

#print axioms phiKAlgEquiv_eq_phiKEquiv

/-- ★★★★★ **`phiKAlgEquiv` 在 `S` 的像上就是 `phiA`**。 -/
theorem phiKAlgEquiv_algebraMap' (F : Type) [Field F] (r n : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (x : S F r n) :
    phiKAlgEquiv F r n A (algebraMap (S F r n) (SField F r n) x)
      = algebraMap (S F r n) (SField F r n) (phiA F r n A x) := by
  rw [phiKAlgEquiv_eq_phiKEquiv, phiKEquiv_algebraMap]

#print axioms phiKAlgEquiv_algebraMap'

end SprPhiKBridge

/-! ## §21 输入 (i'') 第 3 步：`T`-等变性的**分式域延拓**

§19 在 `Spr` 层证了 `sprToS ∘ sprDiagHom b = phiA (diagUnit b⁻¹) ∘ sprToS`。
输入 (i'') 要的是它在 `K' = Frac(Spr)` 层的形态（源文 `:363` 的"induced actions on `K'`"）：

`sprToSField ∘ sprDiagFieldEquiv b = phiKAlgEquiv (diagUnit b⁻¹) ∘ sprToSField`。

**证法**（R231"两侧各自标准形"）：域同态由其在 `Spr` 的像上的值决定
（`IsFractionRing.div_surjective` ＋ `map_div₀`），而在 `algebraMap p` 上两侧分别是
`sprToSField_algebraMap`／`phiKAlgEquiv_algebraMap'` 的复合，再由 §19 的 `Spr` 层等式收口。
**注意**：`sprToSField_algebraMap` 的 `x` 是**显式参数**，故 `rw [sprToSField_algebraMap F r 9 k₀ hk₀ p]`
只落 `p` 处的那个实例；要一次改写**所有**实例须用 `simp only [sprToSField_algebraMap]`（R246）。 -/

section SprDiagFieldLift

set_option linter.style.haveILetI false

open ABGV52

variable (F : Type) [Field F] (r : ℕ) (k₀ : Fin r) (hk₀ : k₀.val = 0) (b : Fin 9 → Fˣ)

/-- ★★★★★★★ **`T`-等变性的分式域延拓**：`sprToSField` 把 `K'` 上的环面作用
`sprDiagFieldEquiv b` 送到 `SField` 上的 `K`-作用 `phiKAlgEquiv (diagUnit b⁻¹)`。

这是输入 (i'') 路线的第 3 步（§6 第 1 项）：与 `sprToSField_injective` 合用即得
"`sprToSField x` 固定 ⟹ `x` 被 `T` 固定"。 -/
theorem sprToSField_sprDiagFieldEquiv (x : SprField F r 9) :
    sprToSField F r 9 k₀ hk₀ (sprDiagFieldEquiv F r 9 b x)
      = phiKAlgEquiv F r 9 (diagUnit F b⁻¹) (sprToSField F r 9 k₀ hk₀ x) := by
  have hbase : ∀ p : Spr F r 9,
      sprToSField F r 9 k₀ hk₀
          (sprDiagFieldEquiv F r 9 b (algebraMap (Spr F r 9) (SprField F r 9) p))
        = phiKAlgEquiv F r 9 (diagUnit F b⁻¹)
            (sprToSField F r 9 k₀ hk₀ (algebraMap (Spr F r 9) (SprField F r 9) p)) := by
    intro p
    rw [sprDiagFieldEquiv_algebraMap F r 9 b p]
    simp only [sprToSField_algebraMap]
    rw [phiKAlgEquiv_algebraMap']
    exact congrArg (algebraMap (S F r 9) (SField F r 9))
      (DFunLike.congr_fun (sprToS_sprDiagHom F r k₀ b) p)
  obtain ⟨a, c, hc, hx⟩ := IsFractionRing.div_surjective (Spr F r 9) x
  subst hx
  simp only [map_div₀]
  rw [hbase a, hbase c]

#print axioms sprToSField_sprDiagFieldEquiv

end SprDiagFieldLift

/-! ## §22 ★★★★★★★ **输入 (i'') 解除**：`S_n` 侧的等变性 ＋ 分式域延拓 ＋ 三条收口

§19 ／ §21 处理了**环面 `T`** 一侧（`sprDiagHom` → `sprDiagFieldEquiv`）。
本节补上 **`S_n`** 一侧并**一次走完 (i'')**（§6 的第 2、3 项）：

| 件 | 内容 |
|---|---|
| ★★★★★ `permUnit` | `σ ↦ P_σ ∈ GL_9(F)`（**置换矩阵**单位化；复用库内 `PEquiv.toMatrix`） |
| `permUnit_val`／`permUnit_inv_val` | 计算律 `↑(permUnit σ) = σ.toPEquiv.toMatrix`、`↑((permUnit σ)⁻¹) = σ⁻¹.toPEquiv.toMatrix` |
| ★★★★ `constMat_permUnit`／`constMat_permUnit_inv` | `constMat` 把 `P_σ` 送到 `S` 上的同一置换矩阵 |
| ★★★★★★★ `phiGen_permUnit` | **`phiGen (permUnit σ⁻¹) ⟨k,i,j⟩ = X(k, σ i, σ j)`** |
| ★★★★★★★ `sprToS_sprPermAlgEquiv` | **`sprToS ∘ sprPermAlgEquiv σ = phiA (permUnit σ⁻¹) ∘ sprToS`**（`Spr` 层） |
| ★★★★★★★ `sprToSField_sprPermFieldEquiv` | 其**分式域延拓**（`K'` 层，源文 `:363`） |
| ★★★★★★★★ `zPreimageNFixed` | **输入 (i'') `ZPreimageNFixed` ✅ 无条件成立** |
| ★★★★★★ `zLeNFixed_of_zInSpr` | `ZLeNFixed ⟸ ZInSpr`（(i'') 已不再需要假设） |
| ★★★★★★★★ `zEqNFixed_of_two_inputs` | **`ZEqNFixed ⟸ (i) ＋ (ii)`**（三条输入降为两条） |

**证法要点**：
* 置换矩阵走**库内** `Mathlib/Data/Matrix/PEquiv.lean` 的 `PEquiv.toMatrix`
  （R207 第五次兑现：`toMatrix_toPEquiv_mul : f.toPEquiv.toMatrix * M = M.submatrix f id`
  与 `mul_toMatrix_toPEquiv : M * f.toPEquiv.toMatrix = M.submatrix id f.symm`
  两条**逐项**引理把 `A⁻¹ X A` 一次算成 `X.submatrix σ⁻¹ σ⁻¹`，**完全绕开求和**——
  与 `phiGen_diagUnit` 用 `Matrix.mul_diagonal` 同一战术，R243）。
* (i'') 的收口只用两条已有机检件：§21／本节的**分式域等变性** ＋ `phiK_fixes_ZCanon`
  （`ZCanon` 被一切 `PGL_9(F)` 元固定）。逻辑：`y = sprToSField x ∈ Z ⟹
  phiK A y = y`，而等变性给出 `phiK A y = sprToSField (A·x)`，故 `A·x = x`
  （`sprToSField_injective`）。

**工艺（2 条，本轮实测）**：
* **R247 `PEquiv.toMatrix` 族是置换矩阵的"逐项"工具**：`toMatrix_toPEquiv_mul`／
  `mul_toMatrix_toPEquiv`／`toMatrix_trans`／`toMatrix_refl` 四条足够建单位 ＋ 算共轭，
  **不需要** `Matrix.mul_apply` 的求和展开（`Finset.sum_eq_single` 两次）。
  ⟹ 凡遇"置换/投影矩阵"，先查 `PEquiv`，**不要**从 `Matrix.mul_apply` 起手。
* **R248 `AlgEquiv` 进 `AlgHom.comp` 后再 `simp only [AlgHom.comp_apply]`，
  目标里留下的是 `↑((e).toAlgHom)` 而**不是** `↑e`**，此时 `rw [e_X]` **不落点**。
  **正解**：`simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]` 一并剥掉
  `toAlgHom` 包装。这是 **R244／R246 同族的第四例**（`≃ₐ` 包装挡 `rw`）。

**射程（勿夸大，逐条）**：
* 输入 (i'') ✅ **已解除**（`zPreimageNFixed`，无条件，只依赖 `[Field F]`）。
* 输入 **(ii) `NFixedLeZ` 未证**（须先定义 `UD`）；输入 **(i) `ZInSpr` 未证**。
* `ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/


section SprPermUnit

set_option linter.style.haveILetI false

open ABGV52

/-- ★★★★★ **置换矩阵的单位化**：`σ ↦ P_σ ∈ GL_9(F)`，其中 `P_σ = σ.toPEquiv.toMatrix`
（复用库内 `PEquiv.toMatrix`；`toMatrix_trans`／`toMatrix_refl` 给单位律）。 -/
noncomputable def permUnit (F : Type) [Field F] (σ : Equiv.Perm (Fin 9)) :
    (Matrix (Fin 9) (Fin 9) F)ˣ where
  val := σ.toPEquiv.toMatrix
  inv := σ⁻¹.toPEquiv.toMatrix
  val_inv := by
    show σ.toPEquiv.toMatrix * σ⁻¹.toPEquiv.toMatrix = 1
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have h : σ.trans σ⁻¹ = Equiv.refl (Fin 9) := Equiv.ext (fun x => by simp)
    rw [h, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    show σ⁻¹.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = 1
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have h : σ⁻¹.trans σ = Equiv.refl (Fin 9) := Equiv.ext (fun x => by simp)
    rw [h, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

#print axioms permUnit

/-- `↑(permUnit σ) = σ.toPEquiv.toMatrix`（计算律）。 -/
@[simp] lemma permUnit_val (F : Type) [Field F] (σ : Equiv.Perm (Fin 9)) :
    ((permUnit F σ : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F)
      = σ.toPEquiv.toMatrix := rfl

#print axioms permUnit_val

/-- `↑((permUnit σ)⁻¹) = σ⁻¹.toPEquiv.toMatrix`（计算律）。 -/
@[simp] lemma permUnit_inv_val (F : Type) [Field F] (σ : Equiv.Perm (Fin 9)) :
    (((permUnit F σ)⁻¹ : (Matrix (Fin 9) (Fin 9) F)ˣ) : Matrix (Fin 9) (Fin 9) F)
      = σ⁻¹.toPEquiv.toMatrix := rfl

#print axioms permUnit_inv_val

/-- `constMat` 把置换矩阵送到 `S` 上的同一置换矩阵（`0/1` 条目被 `algebraMap` 固定）。 -/
theorem constMat_permUnit (F : Type) [Field F] (r : ℕ) (σ : Equiv.Perm (Fin 9)) :
    constMat F r 9 (↑(permUnit F σ))
      = (σ.toPEquiv.toMatrix : Matrix (Fin 9) (Fin 9) (S F r 9)) := by
  rw [constMat, permUnit_val]
  ext i j
  rw [Matrix.map_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
  by_cases h : j ∈ σ.toPEquiv i
  · rw [ite_eq_left h, ite_eq_left h, map_one]
  · rw [ite_eq_right (by simpa using h), ite_eq_right (by simpa using h), map_zero]

#print axioms constMat_permUnit

/-- `constMat` 把置换矩阵的**逆**送到 `S` 上的同一置换矩阵。 -/
theorem constMat_permUnit_inv (F : Type) [Field F] (r : ℕ) (σ : Equiv.Perm (Fin 9)) :
    constMat F r 9 (↑((permUnit F σ)⁻¹))
      = ((σ⁻¹).toPEquiv.toMatrix : Matrix (Fin 9) (Fin 9) (S F r 9)) := by
  rw [constMat, permUnit_inv_val]
  ext i j
  rw [Matrix.map_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
  by_cases h : j ∈ σ⁻¹.toPEquiv i
  · rw [ite_eq_left h, ite_eq_left h, map_one]
  · rw [ite_eq_right (by simpa using h), ite_eq_right (by simpa using h), map_zero]

#print axioms constMat_permUnit_inv

/-- ★★★★★★★ **`phiGen` 在置换单位上的值**：`X(k,i,j) ↦ X(k, σ i, σ j)`。

走 `PEquiv` 的**逐项**引理（R247）：`A⁻¹ X A = X.submatrix σ⁻¹ σ⁻¹`。 -/
theorem phiGen_permUnit (F : Type) [Field F] (r : ℕ) (σ : Equiv.Perm (Fin 9))
    (k : Fin r) (i j : Fin 9) :
    phiGen F r 9 (permUnit F σ⁻¹) ⟨k, i, j⟩ = MvPolynomial.X ⟨k, σ i, σ j⟩ := by
  rw [phiGen, constMat_permUnit_inv, constMat_permUnit]
  have h1 : (σ⁻¹)⁻¹ = σ := Equiv.symm_symm σ
  simp only [h1]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, genericMatrix, genericEntry]
  rfl

#print axioms phiGen_permUnit

/-- ★★★★★★★ **`sprToS` 与 `S_n` 作用的等变性**（`Spr` 层）：
`sprToS ∘ sprPermAlgEquiv σ = phiA (permUnit σ⁻¹) ∘ sprToS`（与 §19 的 `b⁻¹` 同约定）。 -/
theorem sprToS_sprPermAlgEquiv (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (σ : Equiv.Perm (Fin 9)) :
    (sprToS F (n := 9) k₀).comp (sprPermAlgEquiv F r 9 σ)
      = (phiA F r 9 (permUnit F σ⁻¹)).comp (sprToS F (n := 9) k₀) := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rcases v with i | ⟨⟨i, j⟩, k⟩
  · rw [sprPermAlgEquiv_X_inl]
    simp only [sprToS, phiA, MvPolynomial.aeval_X, Sum.elim_inl]
    rw [phiGen_permUnit]
  · rw [sprPermAlgEquiv_X_inr]
    simp only [sprToS, phiA, MvPolynomial.aeval_X, Sum.elim_inr]
    rw [phiGen_permUnit]

#print axioms sprToS_sprPermAlgEquiv

/-- ★★★★★★★ **`S_n`-等变性的分式域延拓**：与 §21 同法（域同态由其在 `Spr` 的像决定）。 -/
theorem sprToSField_sprPermFieldEquiv (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (σ : Equiv.Perm (Fin 9)) (x : SprField F r 9) :
    sprToSField F r 9 k₀ hk₀ (sprPermFieldEquiv F r 9 σ x)
      = phiKAlgEquiv F r 9 (permUnit F σ⁻¹) (sprToSField F r 9 k₀ hk₀ x) := by
  have hbase : ∀ p : Spr F r 9,
      sprToSField F r 9 k₀ hk₀
          (sprPermFieldEquiv F r 9 σ (algebraMap (Spr F r 9) (SprField F r 9) p))
        = phiKAlgEquiv F r 9 (permUnit F σ⁻¹)
            (sprToSField F r 9 k₀ hk₀ (algebraMap (Spr F r 9) (SprField F r 9) p)) := by
    intro p
    rw [sprPermFieldEquiv_algebraMap F r 9 σ p]
    simp only [sprToSField_algebraMap]
    rw [phiKAlgEquiv_algebraMap']
    exact congrArg (algebraMap (S F r 9) (SField F r 9))
      (DFunLike.congr_fun (sprToS_sprPermAlgEquiv F r k₀ σ) p)
  obtain ⟨a, c, hc, hx⟩ := IsFractionRing.div_surjective (Spr F r 9) x
  subst hx
  simp only [map_div₀]
  rw [hbase a, hbase c]

#print axioms sprToSField_sprPermFieldEquiv

/-- ★★★★★★★★ **输入 (i'') 解除**：`Z` 的 `K'`-原像都 `N`-固定。

**证明**：设 `y = sprToSField x ∈ ZCanon`。`phiK_fixes_ZCanon` 给 `phiK A y = y`
（一切 `A ∈ GL_9(F)`）；§21／本节的等变性把它改写成 `sprToSField (A·x) = sprToSField x`；
`sprToSField_injective` 收口得 `A·x = x`（`A` 取遍 `diagUnit` 与 `permUnit`）。
**只依赖 `[Field F]`**，不含任何具名输入。 -/
theorem zPreimageNFixed (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : ZPreimageNFixed F D k₀ hk₀ := by
  intro x hx
  refine ⟨fun b => ?_, fun σ => ?_⟩
  · have h1 : sprToSField F 2 9 k₀ hk₀ (sprDiagFieldEquiv F 2 9 b x)
        = sprToSField F 2 9 k₀ hk₀ x := by
      rw [sprToSField_sprDiagFieldEquiv F 2 k₀ hk₀ b x,
        phiK_fixes_ZCanon F 2 9 D (diagUnit F b⁻¹) (sprToSField F 2 9 k₀ hk₀ x) hx]
    exact sprToSField_injective F 2 9 k₀ hk₀ h1
  · have h1 : sprToSField F 2 9 k₀ hk₀ (sprPermFieldEquiv F 2 9 σ x)
        = sprToSField F 2 9 k₀ hk₀ x := by
      rw [sprToSField_sprPermFieldEquiv F 2 k₀ hk₀ σ x,
        phiK_fixes_ZCanon F 2 9 D (permUnit F σ⁻¹) (sprToSField F 2 9 k₀ hk₀ x) hx]
    exact sprToSField_injective F 2 9 k₀ hk₀ h1

#print axioms zPreimageNFixed

/-- ★★★★★★ **`ZLeNFixed` 现在只需输入 (i)**：`ZPreimageNFixed` 已无条件成立。 -/
theorem zLeNFixed_of_zInSpr (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (h1 : ZInSpr F 2 9 D k₀ hk₀) :
    ZLeNFixed F D k₀ hk₀ :=
  zLeNFixed_of_inputs F D hk₀ h1 (zPreimageNFixed F D k₀ hk₀)

#print axioms zLeNFixed_of_zInSpr

/-- ★★★★★★★★ **`ZEqNFixed` 只需两条输入**：输入 (i) `ZInSpr` ＋ 输入 (ii) `NFixedLeZ`。

（(i'') 已由 `zPreimageNFixed` 无条件解除，故 `zEqNFixed_of_three_inputs` 少一条假设。） -/
theorem zEqNFixed_of_two_inputs (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h1 : ZInSpr F 2 9 D k₀ hk₀) (h2 : NFixedLeZ F D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_three_inputs F D hk₀ h1 h2 (zPreimageNFixed F D k₀ hk₀)

#print axioms zEqNFixed_of_two_inputs

end SprPermUnit

/-! ## §23 **`N` 在 `M_n(K')` 上按环自同构作用** —— `M_n(K')^N` 的代数结构（输入 (ii) 的地基）

输入 (ii) `NFixedLeZ` 的源文论证（`raw/Saltman1999ch14.tex`，`prop:14.19` 的 `Z` 半）要
**把 `M_n(K')^N` 当作代数**来谈它的中心：`c ∈ K'^N ⟹ c·I ∈ M_n(K')^N = UD ⟹ c·I ∈ Z(UD) = Z`。
而"中心"这个概念要求 `M_n(K')^N` 有环结构——即 `ψ_b`／`ψ_σ` 必须是**环自同态**。
§153 只定义了作用并证了半线性（`sprPsiDK_smul`），**环律此前不成立**。本节补上：

| 件 | 内容 |
|---|---|
| `sprDiagMatK_mul_inv` | `D_b · D_{b⁻¹} = 1`（`b` 在前；`sprDiagMatK_inv_mul` 是反序） |
| `sprPmatK_inv_mul`／`sprPmatK_mul_inv` | `P_σ⁻¹ · P_σ = 1`、`P_σ · P_σ⁻¹ = 1`（**两侧都要**） |
| ★★★ `conj_mul_of` | 单位共轭的乘法律：`(D A D')(D B D') = D (A B) D'`（若 `D' D = 1`） |
| ★★★★ `sprPsiDK_mul`／`_add`／`_zero`／`_one` | **`ψ_b` 是环同态** |
| ★★★★ `sprPsiSK_mul`／`_add`／`_zero`／`_one` | **`ψ_σ` 是环同态** |
| ★★★ `sprMatNFixed_mul`／`_add`／`_one`／`_zero` | **`M_n(K')^N` 是子环**（`K'^N` 的矩阵影子） |

**工艺（2 条，本轮实测）**：
* **R249 两侧逆要分别证**：`sprPmatK_inv_mul`（左逆）**不能**用于 `ψ` 的 `_one`
  （`_one` 里要的是 `P_σ · P_σ⁻¹ = 1`）。`Matrix.inv_eq_right_inv` 只给一侧，
  另一侧须**单独**从 `sprPmat_mul_symm` 起手（各 4 行）。
* **R250 `sprPmatK σ` 与 `(sprPmat (Spr) σ).map (algebraMap)` 不是 `rfl`**：
  `sprPmatK` 直接定义在 `SprField` 上（`sprPmat (SprField) σ`），不是 `Spr` 版的映射像。
  ⟹ 混用两者前必须先 `rw [sprPmatK_eq_map]`（§155 已有）。**`show` 不能**代替它（非 defeq）。

**射程（勿夸大，逐条）**：
* 本节只建 **`M_n(K')^N` 的环结构**；**没有**证明 `M_n(K')^N = UD`，
  **没有**证明 `Z(M_n(K')^N) ⊆ Z`，**没有**证明输入 (ii)。
* **依赖顺序的更正（本轮重要发现）**：源文 (ii) 的证明要构造 `S'' = S' ⊗_Z K'`，
  这需要 `K'` 是 **`Z`-代数**，即先要有 `Z ⊆ K'`——而 `Z ⊆ K'` 正是**输入 (i) `ZInSpr`**。
  ⟹ **v17 §6 的顺序（先 4 后 6）依赖倒置**；(i) 在 (ii) 之前。
* 输入 (i) `ZInSpr` **未证**；输入 (ii) `NFixedLeZ` **未证**；`ZEqNFixed` **未证**；
  **H2 见文件头「当前状态」。** -/


section SprPsiRingHom

set_option linter.style.haveILetI false

open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

/-- `D_b · D_{b⁻¹} = 1`（`b` 在**前**；§155 的 `sprDiagMatK_inv_mul` 是反序且需 `Nonempty`）。 -/
theorem sprDiagMatK_mul_inv (b : Fin n → Fˣ) :
    sprDiagMatK (F := F) (r := r) (n := n) b
      * sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹) = 1 := by
  rw [sprDiagMatK, sprDiagMatK, ← Matrix.map_mul, sprDiagMat_mul_inv (r := r) b]
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j <;> simp [hij]

#print axioms sprDiagMatK_mul_inv

/-- `P_σ⁻¹ · P_σ = 1`（左逆）。 -/
theorem sprPmatK_inv_mul (σ : Equiv.Perm (Fin n)) :
    (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹
      * sprPmatK (F := F) (r := r) (n := n) σ = 1 := by
  have h : sprPmat (Spr F r n) σ⁻¹ * sprPmat (Spr F r n) σ = 1 := by
    simpa using sprPmat_mul_symm (R := Spr F r n) (σ := σ⁻¹)
  rw [sprPmatK_inv, sprPmatK_eq_map, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _)]

#print axioms sprPmatK_inv_mul

/-- `P_σ · P_σ⁻¹ = 1`（右逆；R249：`_one` 需要的是这一侧）。 -/
theorem sprPmatK_mul_inv (σ : Equiv.Perm (Fin n)) :
    sprPmatK (F := F) (r := r) (n := n) σ
      * (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹ = 1 := by
  rw [sprPmatK_inv, sprPmatK_eq_map, ← Matrix.map_mul, sprPmat_mul_symm,
    Matrix.map_one _ (map_zero _) (map_one _)]

#print axioms sprPmatK_mul_inv

/-- 单位共轭的乘法律：若 `D' * D = 1`，则 `(D A D')(D B D') = D (A B) D'`。

这是 `ψ` 的乘法律的**唯一实质输入**（`ψ` 就是 `D_{b⁻¹} · (·).map φ_b · D_b`）。 -/
theorem conj_mul_of (D D' : Matrix (Fin n) (Fin n) (SprField F r n)) (h : D' * D = 1)
    (A B : Matrix (Fin n) (Fin n) (SprField F r n)) :
    (D * A * D') * (D * B * D') = D * (A * B) * D' := by
  calc (D * A * D') * (D * B * D') = D * A * (D' * D) * B * D' := by noncomm_ring
    _ = D * A * B * D' := by rw [h, Matrix.mul_one]
    _ = D * (A * B) * D' := by noncomm_ring

#print axioms conj_mul_of

/-- ★★★★ **`ψ_b` 保持加法**。 -/
theorem sprPsiDK_add (b : Fin n → Fˣ) (A B : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiDK F r n b (A + B) = sprPsiDK F r n b A + sprPsiDK F r n b B := by
  rw [sprPsiDK, sprPsiDK, sprPsiDK, Matrix.map_add _ (map_add _), Matrix.mul_add,
    Matrix.add_mul]

#print axioms sprPsiDK_add

/-- ★★★★ **`ψ_b` 保持零**。 -/
theorem sprPsiDK_zero (b : Fin n → Fˣ) :
    sprPsiDK F r n b (0 : Matrix (Fin n) (Fin n) (SprField F r n)) = 0 := by
  rw [sprPsiDK, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

#print axioms sprPsiDK_zero

/-- ★★★★ **`ψ_b` 保持乘法**。 -/
theorem sprPsiDK_mul (b : Fin n → Fˣ) (A B : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiDK F r n b (A * B) = sprPsiDK F r n b A * sprPsiDK F r n b B := by
  rw [sprPsiDK, sprPsiDK, sprPsiDK, Matrix.map_mul]
  exact (conj_mul_of F r n _ _ (sprDiagMatK_mul_inv F r n b) _ _).symm

#print axioms sprPsiDK_mul

/-- ★★★★ **`ψ_b` 保持单位元**。 -/
theorem sprPsiDK_one [Nonempty (Fin n)] (b : Fin n → Fˣ) :
    sprPsiDK F r n b (1 : Matrix (Fin n) (Fin n) (SprField F r n)) = 1 := by
  rw [sprPsiDK, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    sprDiagMatK_inv_mul]

#print axioms sprPsiDK_one

/-- ★★★★ **`ψ_σ` 保持加法**。 -/
theorem sprPsiSK_add (σ : Equiv.Perm (Fin n)) (A B : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiSK F r n σ (A + B) = sprPsiSK F r n σ A + sprPsiSK F r n σ B := by
  rw [sprPsiSK, sprPsiSK, sprPsiSK, Matrix.map_add _ (map_add _), Matrix.mul_add,
    Matrix.add_mul]

#print axioms sprPsiSK_add

/-- ★★★★ **`ψ_σ` 保持零**。 -/
theorem sprPsiSK_zero (σ : Equiv.Perm (Fin n)) :
    sprPsiSK F r n σ (0 : Matrix (Fin n) (Fin n) (SprField F r n)) = 0 := by
  rw [sprPsiSK, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

#print axioms sprPsiSK_zero

/-- ★★★★ **`ψ_σ` 保持乘法**。 -/
theorem sprPsiSK_mul (σ : Equiv.Perm (Fin n)) (A B : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiSK F r n σ (A * B) = sprPsiSK F r n σ A * sprPsiSK F r n σ B := by
  rw [sprPsiSK, sprPsiSK, sprPsiSK, Matrix.map_mul]
  exact (conj_mul_of F r n _ _ (sprPmatK_inv_mul F r n σ) _ _).symm

#print axioms sprPsiSK_mul

/-- ★★★★ **`ψ_σ` 保持单位元**。 -/
theorem sprPsiSK_one (σ : Equiv.Perm (Fin n)) :
    sprPsiSK F r n σ (1 : Matrix (Fin n) (Fin n) (SprField F r n)) = 1 := by
  rw [sprPsiSK, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    sprPmatK_mul_inv]

#print axioms sprPsiSK_one

/-- ★★★ **`M_n(K')^N` 对乘法封闭**。 -/
theorem sprMatNFixed_mul {A B : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hA : sprMatNFixed F r n A) (hB : sprMatNFixed F r n B) :
    sprMatNFixed F r n (A * B) :=
  ⟨fun b => by rw [sprPsiDK_mul, hA.1 b, hB.1 b],
   fun σ => by rw [sprPsiSK_mul, hA.2 σ, hB.2 σ]⟩

#print axioms sprMatNFixed_mul

/-- ★★★ **`M_n(K')^N` 对加法封闭**。 -/
theorem sprMatNFixed_add {A B : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hA : sprMatNFixed F r n A) (hB : sprMatNFixed F r n B) :
    sprMatNFixed F r n (A + B) :=
  ⟨fun b => by rw [sprPsiDK_add, hA.1 b, hB.1 b],
   fun σ => by rw [sprPsiSK_add, hA.2 σ, hB.2 σ]⟩

#print axioms sprMatNFixed_add

/-- ★★★ **`1 ∈ M_n(K')^N`**。 -/
theorem sprMatNFixed_one [Nonempty (Fin n)] :
    sprMatNFixed F r n (1 : Matrix (Fin n) (Fin n) (SprField F r n)) :=
  ⟨fun b => sprPsiDK_one F r n b, fun σ => sprPsiSK_one F r n σ⟩

#print axioms sprMatNFixed_one

/-- ★★★ **`0 ∈ M_n(K')^N`**。 -/
theorem sprMatNFixed_zero :
    sprMatNFixed F r n (0 : Matrix (Fin n) (Fin n) (SprField F r n)) :=
  ⟨fun b => sprPsiDK_zero F r n b, fun σ => sprPsiSK_zero F r n σ⟩

#print axioms sprMatNFixed_zero

end SprPsiRingHom

/-! ## §24 ★★★★ **中心生成元是多项式**（输入 (i) 的**形式化简**）

`ZCanon = IntermediateField.adjoin F (Set.range D.centK)` 定义在 `SField = Frac(S)` 里，
故先验地 `centK c` 只是**有理函数**。本节证明它其实是**多项式**：

`∃ s ∈ S, D.centK c = algebraMap s`（即中心元的纯量值由 `c` 的**对角条目**给出）。

**为什么重要**：输入 (i) `ZInSpr` 要求每个 `D.centK c` 落在 `sprToSField` 的像里。
有了本节，`D.centK c` 可**写成 `S` 的元素**，于是 (i) 变成纯粹**两个多项式环之间**的断言：
> 每个中心标量 `s_c ∈ S` 都落在 `Frac(sprToS(Spr))` 里。
> 等价地：`∃ a b : Spr, sprToS b ≠ 0 ∧ sprToS a = sprToS b · s_c`。

**证法**（3 行）：`D.centK_spec c` 说 `c` 在 `M_n(K)` 中的像是 `scalar (centK c)`；
取 `(i,i)` 条目即得 `algebraMap (c i i) = centK c`。**关键事实**：`c` 的矩阵条目本就在 `S`
里，故 `centK c` 是**多项式**而非分式——不需要任何 PI 理论。

**射程（勿夸大）**：本节只给**形式化简**，**不**证明 (i)；
"s_c ∈ Frac(sprToS(Spr))" 的**内容**（即中心不变量被"对角线 ＋ 其余通用矩阵"生成）
仍未证——它是源文 `prop:14.19` 的核心困难，须经 `lem:14.21／14.22` 的
`R ↪ M_n(S')` 识别。`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/


section CentKPolynomial

set_option linter.style.haveILetI false

open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **中心生成元是多项式**：存在 `s ∈ S` 使 `D.centK c = algebraMap s`。

（`s` 取 `c` 作为 `M_n(S)` 中矩阵的 `(i,i)` 条目；`D.centK_spec` 的 `(i,i)` 条目即得。） -/
theorem centK_eq_algebraMap [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c : ↥(genericCenter F r n)) :
    ∃ s : S F r n, D.centK c = algebraMap (S F r n) (SField F r n) s := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  refine ⟨((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) i i, ?_⟩
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (SField F r n) => M i i) (D.centK_spec c)
  simpa [Matrix.map_apply, Matrix.scalar_apply] using h.symm

#print axioms centK_eq_algebraMap

end CentKPolynomial

/-! ## §25 ★★★★ **`T` 在 `K'` 上真的按群作用**（`sprDiagFieldEquiv` 的群律）

源文 `:363` 说 `N` 在 `K'` 上有诱导作用；`N` 的 `T` 部分即 `b ↦ φ_b`。此前本仓有
**`S`-层**的群律（`sprDiagHom_mul`／`sprDiagHom_one`）与 `K'`-层的**单个**映射
（`sprDiagFieldEquiv`），但 `K'`-层的群律**不成立**——而已有机检件
（`sprFieldTFixed`＝`∀ b, φ_b x = x`）在陈述"`T`-不变"时**假定了它是作用**。

| 件 | 内容 |
|---|---|
| ★★★★ `sprDiagFieldEquiv_mul` | **`φ_b (φ_{b'} x) = φ_{b·b'} x`**（`b·b'` 逐点乘） |
| ★★★ `sprDiagFieldEquiv_one` | `φ_1 = id` |
| ★★★★ `sprDiagFieldEquiv_inv` | **`φ_b (φ_{b⁻¹} x) = x`**（互逆） |

**证法**：与 §21／§22 同模板（域同态由其在 `Spr` 的像上的值决定：
`IsFractionRing.div_surjective` ＋ `simp only [map_div₀]` ＋ 逐点 `hbase`），
`Spr` 层那一步只需 `sprDiagFieldEquiv_algebraMap` 两次 ＋ `sprDiagHom_mul`。

**用途**：`sprFieldTFixed`／`sprFieldNFixed`（`prop:14.19` 的右端 `K'^N`）的**良定性**；
以及 `lem:14.25` 的 `s' = ∏_{σ} σ(s)` 那类**轨道积**论证（须能自由地复合／取逆）。

**射程（勿夸大）**：本节只补 `T` 的群律。**`S_n` 侧的 `K'`-层群律未建**
（`sprPermAlgEquiv_mul` 尚不在库）；输入 (i)／(ii) **未证**；`ZEqNFixed` **未证**；
**H2 见文件头「当前状态」。** -/


section SprDiagFieldGroup

set_option linter.style.haveILetI false

open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`T` 在 `K'` 上的群律**：`φ_b ∘ φ_{b'} = φ_{b·b'}`（逐点乘）。 -/
theorem sprDiagFieldEquiv_mul [Nonempty (Fin n)] (b b' : Fin n → Fˣ) (x : SprField F r n) :
    sprDiagFieldEquiv F r n b (sprDiagFieldEquiv F r n b' x)
      = sprDiagFieldEquiv F r n (fun i => b i * b' i) x := by
  have hbase : ∀ p : Spr F r n,
      sprDiagFieldEquiv F r n b
          (sprDiagFieldEquiv F r n b' (algebraMap (Spr F r n) (SprField F r n) p))
        = sprDiagFieldEquiv F r n (fun i => b i * b' i)
            (algebraMap (Spr F r n) (SprField F r n) p) := by
    intro p
    rw [sprDiagFieldEquiv_algebraMap F r n b' p,
      sprDiagFieldEquiv_algebraMap F r n b (sprDiagHom F r n b' p),
      sprDiagFieldEquiv_algebraMap F r n (fun i => b i * b' i) p]
    rw [← AlgHom.comp_apply, sprDiagHom_mul]
  obtain ⟨a, c, hc, hx⟩ := IsFractionRing.div_surjective (Spr F r n) x
  subst hx
  simp only [map_div₀]
  rw [hbase a, hbase c]

#print axioms sprDiagFieldEquiv_mul

/-- ★★★ **`φ_1 = id`**。 -/
theorem sprDiagFieldEquiv_one [Nonempty (Fin n)] (x : SprField F r n) :
    sprDiagFieldEquiv F r n (fun _ => (1 : Fˣ)) x = x := by
  have hbase : ∀ p : Spr F r n,
      sprDiagFieldEquiv F r n (fun _ => (1 : Fˣ))
          (algebraMap (Spr F r n) (SprField F r n) p)
        = algebraMap (Spr F r n) (SprField F r n) p := by
    intro p
    rw [sprDiagFieldEquiv_algebraMap F r n (fun _ => (1 : Fˣ)) p, sprDiagHom_one,
      AlgHom.id_apply]
  obtain ⟨a, c, hc, hx⟩ := IsFractionRing.div_surjective (Spr F r n) x
  subst hx
  simp only [map_div₀]
  rw [hbase a, hbase c]

#print axioms sprDiagFieldEquiv_one

/-- ★★★★ **`φ_b` 与 `φ_{b⁻¹}` 互逆**。 -/
theorem sprDiagFieldEquiv_inv [Nonempty (Fin n)] (b : Fin n → Fˣ) (x : SprField F r n) :
    sprDiagFieldEquiv F r n b (sprDiagFieldEquiv F r n (fun i => (b i)⁻¹) x) = x := by
  rw [sprDiagFieldEquiv_mul F r n b (fun i => (b i)⁻¹) x]
  have h : (fun i => b i * (b i)⁻¹) = fun _ => (1 : Fˣ) := by funext i; simp
  rw [h, sprDiagFieldEquiv_one]

#print axioms sprDiagFieldEquiv_inv

end SprDiagFieldGroup

/-! ## §26 ★★★ **`S_n` 在 `K'` 上的群律**（`T` 群的配对件；§25 的对称补全）

§25 补了 `T`（对角环面）在 `K'` 上的群律。本节补 **`S_n`** 侧，使
`sprPermAlgEquiv`／`sprPermFieldEquiv` 真正成为**群作用**（此前只有单个映射与 `_X` 计算律）。

| 件 | 内容 |
|---|---|
| ★★★ `sprPermAlgEquiv_mul` | `sprPermAlgEquiv σ (sprPermAlgEquiv τ p) = sprPermAlgEquiv (σ * τ) p`（`Spr` 层） |
| ★★★ `sprPermFieldEquiv_mul` | 其 `K'`-层版本 |

**证法**：`Spr` 层用 `MvPolynomial.algHom_ext` ＋ `sprPermAlgEquiv_X_inl/inr` ＋ `rfl`
（`(σ * τ) i = σ (τ i)` 就是 `rfl`）；`K'` 层仍走 §21／§22／§25 的模板
（`div_surjective` ＋ `map_div₀` ＋ 逐点 `hbase`）。`AlgEquiv` 的 `toAlgHom` 包装须先用
`simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]` 剥掉（**R248**，同族第五次兑现）。

**用途**：`sprFieldSFixed`（`∀ σ, σ·x = x`）的良定性；`lem:14.25` 的轨道积
`s' = ∏_{σ∈S_n} σ(s)`（须能自由复合）。

**射程（勿夸大）**：本节只补 `S_n` 的群律。混合积（`T` 与 `S_n` 的交叉关系，
即 `N = T ⋊ S_n` 的**半直积**律）**未建**；输入 (i)／(ii) **未证**；
`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/


section SprPermGroup

set_option linter.style.haveILetI false

open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **`S_n` 在 `Spr` 上的群律**：`sprPermAlgEquiv σ ∘ sprPermAlgEquiv τ = sprPermAlgEquiv (σ * τ)`。 -/
theorem sprPermAlgEquiv_mul (σ τ : Equiv.Perm (Fin n)) (p : Spr F r n) :
    sprPermAlgEquiv F r n σ (sprPermAlgEquiv F r n τ p)
      = sprPermAlgEquiv F r n (σ * τ) p := by
  have hcomp : (sprPermAlgEquiv F r n σ).toAlgHom.comp
        (sprPermAlgEquiv F r n τ).toAlgHom
      = (sprPermAlgEquiv F r n (σ * τ)).toAlgHom := by
    refine MvPolynomial.algHom_ext (fun v => ?_)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rcases v with i | ⟨⟨i, j⟩, k⟩
    · rw [sprPermAlgEquiv_X_inl, sprPermAlgEquiv_X_inl, sprPermAlgEquiv_X_inl]
      rfl
    · rw [sprPermAlgEquiv_X_inr, sprPermAlgEquiv_X_inr, sprPermAlgEquiv_X_inr]
      rfl
  exact DFunLike.congr_fun hcomp p

#print axioms sprPermAlgEquiv_mul

/-- ★★★ **`S_n` 在 `K'` 上的群律**。 -/
theorem sprPermFieldEquiv_mul (σ τ : Equiv.Perm (Fin n)) (x : SprField F r n) :
    sprPermFieldEquiv F r n σ (sprPermFieldEquiv F r n τ x)
      = sprPermFieldEquiv F r n (σ * τ) x := by
  have hbase : ∀ p : Spr F r n,
      sprPermFieldEquiv F r n σ
          (sprPermFieldEquiv F r n τ (algebraMap (Spr F r n) (SprField F r n) p))
        = sprPermFieldEquiv F r n (σ * τ)
            (algebraMap (Spr F r n) (SprField F r n) p) := by
    intro p
    rw [sprPermFieldEquiv_algebraMap F r n τ p,
      sprPermFieldEquiv_algebraMap F r n σ (sprPermAlgEquiv F r n τ p),
      sprPermFieldEquiv_algebraMap F r n (σ * τ) p]
    rw [sprPermAlgEquiv_mul]
  obtain ⟨a, c, hc, hx⟩ := IsFractionRing.div_surjective (Spr F r n) x
  subst hx
  simp only [map_div₀]
  rw [hbase a, hbase c]

#print axioms sprPermFieldEquiv_mul

end SprPermGroup

/-! ## §27 ★★★★★ **中心元的正确运输方向**：`C → S'` 是**特殊化**（`evSpr`），不是包含

**本节的判定（第 384 轮）：终局输入 (i) 此前用错了映射。** 详见 `wiki/deadend-ZInSpr-direction.md`。

`ZInSpr`（`GenericInv` §173）断言
`∀ c, ∃ x : SprField, D.centK c = sprToSField x`
—— 即"中心的每个纯量都是 `K' = Frac(S')` 沿 `sprToS`（`x_ii ↦ x_{k₀,ii}`、`y_ijk ↦ x_{k,ij}`）的像"。
**这条断言是假的**（反例：`n = 2, r = 2`, `c = [X_1,X_2]^2`；论证见 deadend 笔记 §2）。

源文 `prop:14.19` 的 `Z` 半与 `thm:14.17` 的 `Z(F,n,r) ≅ F(M_r)^{S_n}`（`raw/Saltman1999ch14.tex:339`，
记号是 `≅`）是**同一条抽象同构**，其实现是 `lem:14.22` 的 `ψ : R ↪ M_n(S')`
（`c ↦ ψ(c)`，`X_{k₀} ↦ 对角矩阵`），**不是** `K'` 沿包含进 `Frac(S)`。
正确的方向是 `evSpr : S → S'`（**特殊化**）。

| 件 | 内容 |
|---|---|
| ★★★★ `exists_scalar_of_mem_center` | 中心元在 `M_n(S)` 里就是纯量矩阵 `scalar s_c` |
| ★★★★ `sprCenterPolyK` ＋ `_spec`／`_add`／`_mul`／`_one`／`_zero`／`_commutes` | `s_c` 的取法与环律 |
| ★★★★★ `sprCenterPolyAlgHom` | `C(F,n,r) →ₐ[F] S`（中心元的纯量多项式） |
| ★★★★★ `sprCenterK` | **`C(F,n,r) →ₐ[F] S'`**：`c ↦ evSpr s_c`（终局输入 (i) 的**正确实体**） |
| ★★★★★ `psiSpr_center_scalar` | **`ψ(c).map = scalar (algebraMap (sprCenterK c))`** |

**射程（勿夸大）**：本节只建**映射**与其**在生成元上的计算律**。
`sprCenterK` 的**单射性**（需无条件的 `psiSpr` 单射 ＝ `lem:14.22`）、它在 `K'^N` 里的
**落点**（`N`-不变性）、以及 `Frac(sprCenterK C) = K'^N`（源文 `prop:14.19` 的第二半）
**均未证**。`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprCenterTransport

set_option linter.style.haveILetI false

open Matrix
open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **中心元在 `M_n(S)` 里就是纯量矩阵**（`cor:14.8(a)` 的矩阵层加强）。

`D.centK_spec` 只说"经 `S → Frac(S)` 后是纯量"；因 `algebraMap` 单射，矩阵层就已成立。 -/
theorem exists_scalar_of_mem_center [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c : ↥(genericCenter F r n)) :
    ∃ s : S F r n,
      ((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
        = Matrix.scalar (Fin n) s := by
  obtain ⟨s, hs⟩ := centK_eq_algebraMap F r n D c
  refine ⟨s, ?_⟩
  refine Matrix.ext fun i j => ?_
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (SField F r n) => M i j) (D.centK_spec c)
  rw [hs] at h
  simp only [Matrix.map_apply, Matrix.scalar_apply] at h
  by_cases hij : i = j
  · subst hij
    have h2 : (algebraMap (S F r n) (SField F r n))
        (((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) i i)
        = (algebraMap (S F r n) (SField F r n)) s := by simpa using h
    have h3 := IsFractionRing.injective (S F r n) (SField F r n) h2
    simpa [Matrix.scalar, Matrix.diagonal] using h3
  · have h2 : (algebraMap (S F r n) (SField F r n))
        (((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) i j)
        = (algebraMap (S F r n) (SField F r n)) 0 := by simpa [hij] using h
    have h3 := IsFractionRing.injective (S F r n) (SField F r n) h2
    simpa [Matrix.scalar, Matrix.diagonal, hij] using h3

#print axioms exists_scalar_of_mem_center

/-- **中心元对应的纯量多项式** `s_c ∈ S`（`Classical.choose` 取法）。 -/
noncomputable def sprCenterPolyK [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c : ↥(genericCenter F r n)) : S F r n :=
  Classical.choose (exists_scalar_of_mem_center F r n D c)

#print axioms sprCenterPolyK

/-- `s_c` 确实实现中心元（矩阵层）。 -/
theorem sprCenterPolyK_spec [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c : ↥(genericCenter F r n)) :
    ((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
      = Matrix.scalar (Fin n) (sprCenterPolyK F r n D c) :=
  Classical.choose_spec (exists_scalar_of_mem_center F r n D c)

#print axioms sprCenterPolyK_spec

/-- `s_c` 对加法相容（纯量矩阵单射）。 -/
theorem sprCenterPolyK_add [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c c' : ↥(genericCenter F r n)) :
    sprCenterPolyK F r n D (c + c') = sprCenterPolyK F r n D c + sprCenterPolyK F r n D c' := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  calc Matrix.scalar (Fin n) (sprCenterPolyK F r n D (c + c'))
      = ((↑(c + c') : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) :=
        (sprCenterPolyK_spec F r n D (c + c')).symm
    _ = ((c : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
          + ((c' : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) := by
        simp
    _ = Matrix.scalar (Fin n) (sprCenterPolyK F r n D c)
          + Matrix.scalar (Fin n) (sprCenterPolyK F r n D c') := by
        rw [sprCenterPolyK_spec, sprCenterPolyK_spec]
    _ = Matrix.scalar (Fin n) (sprCenterPolyK F r n D c + sprCenterPolyK F r n D c') := by
        rw [map_add]

#print axioms sprCenterPolyK_add

/-- `s_c` 对乘法相容。 -/
theorem sprCenterPolyK_mul [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c c' : ↥(genericCenter F r n)) :
    sprCenterPolyK F r n D (c * c') = sprCenterPolyK F r n D c * sprCenterPolyK F r n D c' := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  calc Matrix.scalar (Fin n) (sprCenterPolyK F r n D (c * c'))
      = ((↑(c * c') : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) :=
        (sprCenterPolyK_spec F r n D (c * c')).symm
    _ = ((c : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
          * ((c' : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) := by
        simp
    _ = Matrix.scalar (Fin n) (sprCenterPolyK F r n D c)
          * Matrix.scalar (Fin n) (sprCenterPolyK F r n D c') := by
        rw [sprCenterPolyK_spec, sprCenterPolyK_spec]
    _ = Matrix.scalar (Fin n) (sprCenterPolyK F r n D c * sprCenterPolyK F r n D c') := by
        rw [map_mul]

#print axioms sprCenterPolyK_mul

/-- `s_1 = 1`。 -/
theorem sprCenterPolyK_one [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    sprCenterPolyK F r n D 1 = 1 := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  calc Matrix.scalar (Fin n) (sprCenterPolyK F r n D 1)
      = (((1 : ↥(genericCenter F r n)) : ↥(genericMatrixAlgebra F r n)) :
          Matrix (Fin n) (Fin n) (S F r n)) :=
        (sprCenterPolyK_spec F r n D 1).symm
    _ = (1 : Matrix (Fin n) (Fin n) (S F r n)) := by simp
    _ = Matrix.scalar (Fin n) (1 : S F r n) := by
        ext i j
        rw [Matrix.scalar_apply, Matrix.one_apply]
        by_cases h : i = j <;> simp [h]

#print axioms sprCenterPolyK_one

/-- `s_0 = 0`。 -/
theorem sprCenterPolyK_zero [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    sprCenterPolyK F r n D 0 = 0 := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  calc Matrix.scalar (Fin n) (sprCenterPolyK F r n D 0)
      = (((0 : ↥(genericCenter F r n)) : ↥(genericMatrixAlgebra F r n)) :
          Matrix (Fin n) (Fin n) (S F r n)) :=
        (sprCenterPolyK_spec F r n D 0).symm
    _ = (0 : Matrix (Fin n) (Fin n) (S F r n)) := by simp
    _ = Matrix.scalar (Fin n) (0 : S F r n) := by
        ext i j
        rw [Matrix.scalar_apply, Matrix.zero_apply]
        by_cases h : i = j <;> simp [h]

#print axioms sprCenterPolyK_zero

/-- `s_c` 与 `F`-纯量的相容格。 -/
theorem sprCenterPolyK_commutes [Nonempty (Fin n)] (D : GenericDivisionData F r n) (a : F) :
    sprCenterPolyK F r n D (algebraMap F ↥(genericCenter F r n) a)
      = algebraMap F (S F r n) a := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  calc Matrix.scalar (Fin n) (sprCenterPolyK F r n D (algebraMap F ↥(genericCenter F r n) a))
      = ((algebraMap F ↥(genericCenter F r n) a : ↥(genericMatrixAlgebra F r n)) :
          Matrix (Fin n) (Fin n) (S F r n)) :=
        (sprCenterPolyK_spec F r n D (algebraMap F ↥(genericCenter F r n) a)).symm
    _ = algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) a := by simp
    _ = Matrix.scalar (Fin n) (algebraMap F (S F r n) a) := by
        rw [Matrix.algebraMap_eq_diagonal]
        ext i j
        rw [Matrix.scalar_apply, Matrix.diagonal_apply, Pi.algebraMap_apply]
        by_cases h : i = j <;> simp [h]

#print axioms sprCenterPolyK_commutes

/-- ★★★★★ **`C(F,n,r) →ₐ[F] S`**：中心元的纯量多项式，打包成 `F`-代数同态。 -/
noncomputable def sprCenterPolyAlgHom [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    ↥(genericCenter F r n) →ₐ[F] S F r n where
  toFun c := sprCenterPolyK F r n D c
  map_one' := sprCenterPolyK_one F r n D
  map_mul' := sprCenterPolyK_mul F r n D
  map_zero' := sprCenterPolyK_zero F r n D
  map_add' := sprCenterPolyK_add F r n D
  commutes' := sprCenterPolyK_commutes F r n D

#print axioms sprCenterPolyAlgHom

/-- ★★★★★ **`C(F,n,r) →ₐ[F] S'`**：`c ↦ evSpr s_c` —— 终局输入 (i) 的**正确实体**。

源文 `:403` 的 `φ` 与 `lem:14.22` 的 `ψ` 都作用在 `S'` 上；中心元的纯量
`centK c = algebraMap s_c`（`H2Final` §24）在 `S'` 里的像是**特殊化** `evSpr s_c`。
**它才是 `ψ` 的纯量像**（下一条），**不是** `sprToSField` 的像。 -/
noncomputable def sprCenterK [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (D : GenericDivisionData F r n) : ↥(genericCenter F r n) →ₐ[F] Spr F r n :=
  (evSpr F r n k₀ hk₀).comp (sprCenterPolyAlgHom F r n D)

#print axioms sprCenterK

/-- ★★★★★ **`ψ` 在中心元上就是 `sprCenterK` 的纯量矩阵**：`ψ(c).map = scalar (κ c)`。

**这是"中心 → `K'`"的正确接线**（替代 `ZInSpr` 的 `sprToSField` 接线）。 -/
theorem psiSpr_center_scalar [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) (c : ↥(genericCenter F r n)) :
    (psiSpr F r n k₀ hk₀ (c : ↥(genericMatrixAlgebra F r n))).map
        (algebraMap (Spr F r n) (SprField F r n))
      = Matrix.scalar (Fin n)
          (algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)) := by
  classical
  have h1 : psiSpr F r n k₀ hk₀ (c : ↥(genericMatrixAlgebra F r n))
      = Matrix.scalar (Fin n) (sprCenterK F r n k₀ hk₀ D c) := by
    show (((c : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))).map
        (evSpr F r n k₀ hk₀)
      = Matrix.scalar (Fin n) (evSpr F r n k₀ hk₀ (sprCenterPolyK F r n D c))
    rw [sprCenterPolyK_spec F r n D c]
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply]
    by_cases h : i = j <;> simp [h]
  rw [h1]
  ext i j
  rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases h : i = j <;> simp [h]

#print axioms psiSpr_center_scalar

end SprCenterTransport


/-! ## §28 ★★★★★ **`ψ_b` 逐点固定 `ψ(R)`；`lem:14.22` 无条件化；`κ(c)` 落在 `K'^T`**

**为什么需要这一节**（承接 §27 的方向纠正，见 `wiki/deadend-ZInSpr-direction.md`）：
§27 给出中心 → `K'` 的正确映射 `sprCenterK`（`c ↦ evSpr s_c`，`ψ(c) = scalar(κ c)`）。
要把 `Z ≅ Frac(κ(C))` 落到 `K'^N` 里，须证 **`κ(c)` 被 `N` 固定**。其机制是

```
scalar(φ_A(κ c)) = ψ_A(scalar(κ c)) = ψ_A(ψ(c)) = ψ(c) = scalar(κ c)
```

—— 中间那步 `ψ_A(ψ(x)) = ψ(x)` 正是本节的主件：`ψ_A`（`sprPsiDK`／`sprPsiSK`）的
定义**就是为了固定生成元矩阵**（`X_{k₀} ↦ xdiag`、`X_k ↦ Y_k`），故它逐点固定 `ψ(R)`。

| 件 | 内容 |
|---|---|
| ★★★★★ `psiSpr_injective_uncond` | **`lem:14.22` 无条件形态**（`[NeZero n]`；由 `exists_algHom_diagonal_genMatKF` 实例化） |
| ★★★★★ `sprCenterK_injective` | **`κ` 单射**（`Z ↪ K'` 有了实体） |
| `sprDiagMatK_eq_diagonal`／`sprDiagMatK_conj_diagonal` | 对角矩阵的显式形态与其被 `D_{b⁻¹}·(·)·D_b` 固定 |
| ★★★★ `sprPsiDK_xdiag_map`／`sprPsiDK_ymat_map` | **`ψ_b` 固定两个生成元矩阵的像** |
| ★★★★ `sprPsiDKAlgHom` | `ψ_b` 打包成 `F`-代数自同态（供沿 `adjoin` 延拓） |
| ★★★★★ `sprPsiDK_fixes_psi` | **`ψ_b(ψ(x)) = ψ(x)`**（`x ∈ R`） |
| ★★★★★ `sprCenterK_tfixed` | **`κ(c) ∈ K'^T`** |

**射程（勿夸大）**：`sprPsiSK`（`S_n` 侧）的同款三条**未做**，故 `κ(c) ∈ K'^N`
（`T` ＋ `S_n`）**未证**；`Frac(κ(C)) = K'^N`（源文 `prop:14.19` 第二半）**未证**。
`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprPsiFix

set_option linter.style.haveILetI false

open Matrix
open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

theorem psiSpr_injective_uncond [NeZero n] (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (psiSpr F r n k₀ hk₀) := by
  obtain ⟨L, hFld, hAlg, θ, hθinj, d, hθ⟩ := exists_algHom_diagonal_genMatKF F r n k₀
  letI : Field L := hFld
  letI : Algebra (SField F r n) L := hAlg
  letI : Algebra F L :=
    (algebraMap (SField F r n) L).comp (algebraMap F (SField F r n)) |>.toAlgebra
  haveI : IsScalarTower F (SField F r n) L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact psiSpr_injective F r n k₀ hk₀ θ hθ hθinj

#print axioms psiSpr_injective_uncond

/-- ★★★★★ **`κ` 单射**（`sprCenterK` 是终局输入 (i) 的**单射**版本）。 -/
theorem sprCenterK_injective [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) : Function.Injective (sprCenterK F r n k₀ hk₀ D) := by
  intro c c' h
  have heq : (psiSpr F r n k₀ hk₀ (c : ↥(genericMatrixAlgebra F r n))).map
        (algebraMap (Spr F r n) (SprField F r n))
      = (psiSpr F r n k₀ hk₀ (c' : ↥(genericMatrixAlgebra F r n))).map
        (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [psiSpr_center_scalar F r n D k₀ hk₀ c,
      psiSpr_center_scalar F r n D k₀ hk₀ c', h]
  have h2 := psiSpr_injective_uncond F r n k₀ hk₀
    (Matrix.map_injective (IsFractionRing.injective (Spr F r n) (SprField F r n)) heq)
  exact Subtype.ext h2

#print axioms sprCenterK_injective

theorem sprDiagMatK_eq_diagonal (b : Fin n → Fˣ) :
    sprDiagMatK (F := F) (r := r) (n := n) b
      = Matrix.diagonal (fun i => algebraMap F (SprField F r n) ((b i : F))) := by
  rw [sprDiagMatK, sprDiagMat, Matrix.diagonal_map (map_zero _)]
  exact congrArg Matrix.diagonal (funext fun i =>
    (IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) ((b i : F))).symm)

#print axioms sprDiagMatK_eq_diagonal

theorem sprDiagMatK_conj_diagonal (b : Fin n → Fˣ) (d : Fin n → SprField F r n) :
    sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹) * Matrix.diagonal d
        * sprDiagMatK (F := F) (r := r) (n := n) b
      = Matrix.diagonal d := by
  rw [sprDiagMatK_eq_diagonal, sprDiagMatK_eq_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h1 : algebraMap F (SprField F r n) ((↑((b i)⁻¹) : F))
      * algebraMap F (SprField F r n) ((↑(b i) : F)) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  calc (algebraMap F (SprField F r n) ((↑((b i)⁻¹) : F)) * d i)
        * algebraMap F (SprField F r n) ((↑(b i) : F))
      = d i * (algebraMap F (SprField F r n) ((↑((b i)⁻¹) : F))
          * algebraMap F (SprField F r n) ((↑(b i) : F))) := by ring
    _ = d i := by rw [h1, mul_one]

#print axioms sprDiagMatK_conj_diagonal

/-- ★★★★ **`ψ_b` 固定 `xdiag` 的像**。 -/
theorem sprPsiDK_xdiag_map [Nonempty (Fin n)] (b : Fin n → Fˣ) :
    sprPsiDK F r n b ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)))
      = (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have hM : (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n))
      = Matrix.diagonal (fun i => algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl i) : Spr F r n)) := by
    rw [xdiag, Matrix.diagonal_map (map_zero _)]
  have hfix : ∀ i : Fin n, (sprDiagFieldEquiv F r n b)
      (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i) : Spr F r n))
      = algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i) : Spr F r n) := by
    intro i
    rw [sprDiagFieldEquiv_algebraMap, sprDiagHom_X_inl]
  have hfix' : ∀ i : Fin n, (sprDiagFieldEquiv F r n b).toRingHom
      (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i) : Spr F r n))
      = algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i) : Spr F r n) :=
    hfix
  rw [hM, sprPsiDK, Matrix.diagonal_map (map_zero _), funext hfix',
    sprDiagMatK_conj_diagonal]

#print axioms sprPsiDK_xdiag_map

/-- ★★★★ **`ψ_b` 固定 `Y_k` 的像**。 -/
theorem sprPsiDK_ymat_map [Nonempty (Fin n)] (b : Fin n → Fˣ)
    (k : {k : Fin r // k.val ≠ 0}) :
    sprPsiDK F r n b ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
      = (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have hbase : ∀ x : Spr F r n, (sprDiagFieldEquiv F r n b).toRingHom
      (algebraMap (Spr F r n) (SprField F r n) x)
      = algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b x) :=
    fun x => sprDiagFieldEquiv_algebraMap F r n b x
  have hstep : ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))).map
        (sprDiagFieldEquiv F r n b).toRingHom
      = sprDiagMatK (F := F) (r := r) (n := n) b
        * ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
        * sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹) := by
    ext i j
    simp only [Matrix.map_apply, ymat_apply, hbase, sprDiagHom_X_inr,
      sprDiagMatK_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [map_mul, MvPolynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n), map_mul]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, Units.val_mul]
    ring
  rw [sprPsiDK, hstep]
  calc sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹)
        * (sprDiagMatK (F := F) (r := r) (n := n) b
          * ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
          * sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹))
        * sprDiagMatK (F := F) (r := r) (n := n) b
      = (sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹)
          * sprDiagMatK (F := F) (r := r) (n := n) b)
          * ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
          * (sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹)
            * sprDiagMatK (F := F) (r := r) (n := n) b) := by noncomm_ring
    _ = (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)) := by
        rw [sprDiagMatK_inv_mul, Matrix.one_mul, Matrix.mul_one]

#print axioms sprPsiDK_ymat_map

/-- ★★★★ `ψ_b` 作为 `F`-代数自同态（环律来自 `GenericInv` §23）。 -/
noncomputable def sprPsiDKAlgHom [Nonempty (Fin n)] (b : Fin n → Fˣ) :
    Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) (SprField F r n) where
  toFun := sprPsiDK F r n b
  map_one' := sprPsiDK_one F r n b
  map_mul' := sprPsiDK_mul F r n b
  map_zero' := sprPsiDK_zero F r n b
  map_add' := sprPsiDK_add F r n b
  commutes' := by
    intro a
    rw [sprMatrixAlgebraMap_eq_scalar F r n a, sprPsiDK_scalar,
      IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a,
      sprDiagFieldEquiv_algebraMap, (sprDiagHom F r n b).commutes a]

#print axioms sprPsiDKAlgHom

/-- ★★★★★ **`ψ_b` 逐点固定 `ψ(R)` 的像**。 -/
theorem sprPsiDK_fixes_psi [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (b : Fin n → Fˣ) (x : ↥(genericMatrixAlgebra F r n)) :
    sprPsiDK F r n b ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))
      = (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have h := algHom_eq_of_genericMatrix F r n (A := Matrix (Fin n) (Fin n) (SprField F r n))
    (f := (sprPsiDKAlgHom F r n b).comp
      ((AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n))).comp
        (psiSpr F r n k₀ hk₀)))
    (g := (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n))).comp
      (psiSpr F r n k₀ hk₀)) (fun k => ?_)
  · exact DFunLike.congr_fun h x
  · show sprPsiDK F r n b
      (((psiSpr F r n k₀ hk₀) ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)))
      = ((psiSpr F r n k₀ hk₀) ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n))
    rw [psiSpr_sprGen, sprGen]
    by_cases hk : k = k₀
    · rw [dif_pos hk]
      exact sprPsiDK_xdiag_map F r n b
    · rw [dif_neg hk]
      exact sprPsiDK_ymat_map F r n b _

#print axioms sprPsiDK_fixes_psi


/-- ★★★★★ **`κ(c)` 的 `T`-不变性**（`κ` 落在 `K'^T` 里）。 -/
theorem sprCenterK_tfixed [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) (b : Fin n → Fˣ) (c : ↥(genericCenter F r n)) :
    sprDiagFieldEquiv F r n b
        (algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c))
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c) := by
  have hfix := sprPsiDK_fixes_psi F r n k₀ hk₀ b (c : ↥(genericMatrixAlgebra F r n))
  have h2 : sprPsiDK F r n b
        (Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n)
          (sprCenterK F r n k₀ hk₀ D c)))
      = Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n)
          (sprCenterK F r n k₀ hk₀ D c)) := by
    rw [← psiSpr_center_scalar F r n D k₀ hk₀ c]
    exact hfix
  rw [sprPsiDK_scalar] at h2
  exact Matrix.scalar_inj.mp h2

#print axioms sprCenterK_tfixed

end SprPsiFix

/-! ## §29 ★★★★★★ **`S_n` 侧的对称补全：`κ(c) ∈ K'^N`** —— 修正后的输入 (i) 完成

§28 给 `T` 侧（`ψ_b(ψ(x)) = ψ(x)`、`κ(c) ∈ K'^T`）。本节补 `S_n` 侧，并把两者合成
**`κ(c) ∈ K'^N`** 与**整块域 `Frac(κ(C)) ⊆ K'^N`**。

| 件 | 内容 |
|---|---|
| ★★★★ `sprPmatK_conj_apply` | `(P_σ · M · P_σ⁻¹)_{ij} = M_{σ⁻¹i, σ⁻¹j}`（指标置换律） |
| ★★★★ `sprPsiSK_xdiag_map`／`sprPsiSK_ymat_map` | **`ψ_σ` 固定两个生成元矩阵的像** |
| ★★★★ `sprPsiSKAlgHom`／★★★★★ `sprPsiSK_fixes_psi` | `ψ_σ(ψ(x)) = ψ(x)`（`x ∈ R`） |
| ★★★★★ `sprCenterK_sfixed` | **`κ(c) ∈ K'^{S_n}`** |
| ★★★★★★ `sprCenterK_mem_fixed` | **`κ(c) ∈ K'^N`**（`T` ＋ `S_n`） |
| ★★★★★★ `sprCenterImageField_fixed` | **`IntermediateField.adjoin F (κ '' C) ⊆ K'^N`** —— 修正后的**输入 (i)** |

**为何共轭律与权律相互抵消**（两侧同一个机制）：`φ_σ(y_ijk) = y_{σi,σj,k}`
（`sprPermAlgEquiv_X_inr`）与 `(P_σ M P_σ⁻¹)_{ij} = M_{σ⁻¹i,σ⁻¹j}`（本节）复合后
`σ ∘ σ⁻¹ = id`，故 `Y_k` 的像不动；`T` 侧同理（权 `b_i/b_j` 与 `D_{b⁻¹}·(·)·D_b` 抵消）。

**射程（勿夸大）**：本节给"**`Z` 的 `κ`-像落在 `K'^N` 里**"这一半。
**另一半** `K'^N ⊆ Frac(κ(C))`（源文 `prop:14.19` 的第二半，需 `UD ⊗_Z K' ≅ M_n(K')`
与 `thm:14.16` 的等化子判据）**未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprPsiPermFix

set_option linter.style.haveILetI false

open Matrix
open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

theorem sprPmatK_conj_apply (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) (SprField F r n)) (i j : Fin n) :
    (sprPmatK (F := F) (r := r) (n := n) σ * M
        * (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹) i j = M (σ⁻¹ i) (σ⁻¹ j) := by
  have hinv : (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹ = sprPmat (SprField F r n) σ⁻¹ := by
    rw [sprPmatK, sprPmat_inv]
  rw [hinv, sprPmatK, Matrix.mul_assoc, sprPmat_mul_apply, sprPmat_mul_apply_right]

#print axioms sprPmatK_conj_apply

/-- ★★★★ **`ψ_σ` 固定 `xdiag` 的像**。 -/
theorem sprPsiSK_xdiag_map (σ : Equiv.Perm (Fin n)) :
    sprPsiSK F r n σ ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)))
      = (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have hfix0 : ∀ k : Fin n, (sprPermFieldEquiv F r n σ)
      (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl k) : Spr F r n))
      = algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl (σ k)) : Spr F r n) := by
    intro k
    rw [sprPermFieldEquiv_algebraMap, sprPermAlgEquiv_X_inl]
  have hfix : ∀ k : Fin n, (sprPermFieldEquiv F r n σ).toRingHom
      (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl k) : Spr F r n))
      = algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl (σ k)) : Spr F r n) :=
    hfix0
  have hM : (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n))
      = Matrix.diagonal (fun i => algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl i) : Spr F r n)) := by
    rw [xdiag, Matrix.diagonal_map (map_zero _)]
  rw [sprPsiSK, hM, Matrix.diagonal_map (map_zero _)]
  ext i j
  rw [sprPmatK_conj_apply]
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, hfix (σ⁻¹ i)]
    simp
  · have hne : σ⁻¹ i ≠ σ⁻¹ j := fun hh => h (by simpa using congrArg σ hh)
    rw [if_neg hne, if_neg h]

#print axioms sprPsiSK_xdiag_map

/-- ★★★★ **`ψ_σ` 固定 `Y_k` 的像**。 -/
theorem sprPsiSK_ymat_map (σ : Equiv.Perm (Fin n))
    (k : {k : Fin r // k.val ≠ 0}) :
    sprPsiSK F r n σ ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
      = (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have hbase : ∀ x : Spr F r n, (sprPermFieldEquiv F r n σ).toRingHom
      (algebraMap (Spr F r n) (SprField F r n) x)
      = algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ x) :=
    fun x => sprPermFieldEquiv_algebraMap F r n σ x
  rw [sprPsiSK]
  ext i j
  rw [sprPmatK_conj_apply]
  simp only [Matrix.map_apply, ymat_apply, hbase, sprPermAlgEquiv_X_inr]
  simp

#print axioms sprPsiSK_ymat_map


/-- ★★★★ `ψ_σ` 作为 `F`-代数自同态。 -/
noncomputable def sprPsiSKAlgHom [Nonempty (Fin n)] (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) (SprField F r n) where
  toFun := sprPsiSK F r n σ
  map_one' := sprPsiSK_one F r n σ
  map_mul' := sprPsiSK_mul F r n σ
  map_zero' := sprPsiSK_zero F r n σ
  map_add' := sprPsiSK_add F r n σ
  commutes' := by
    intro a
    rw [sprMatrixAlgebraMap_eq_scalar F r n a, sprPsiSK_scalar,
      IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a,
      sprPermFieldEquiv_algebraMap, (sprPermAlgEquiv F r n σ).commutes a]

#print axioms sprPsiSKAlgHom

/-- ★★★★★ **`ψ_σ` 逐点固定 `ψ(R)` 的像**。 -/
theorem sprPsiSK_fixes_psi [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (σ : Equiv.Perm (Fin n)) (x : ↥(genericMatrixAlgebra F r n)) :
    sprPsiSK F r n σ ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))
      = (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have h := algHom_eq_of_genericMatrix F r n (A := Matrix (Fin n) (Fin n) (SprField F r n))
    (f := (sprPsiSKAlgHom F r n σ).comp
      ((AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n))).comp
        (psiSpr F r n k₀ hk₀)))
    (g := (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n))).comp
      (psiSpr F r n k₀ hk₀)) (fun k => ?_)
  · exact DFunLike.congr_fun h x
  · show sprPsiSK F r n σ
      (((psiSpr F r n k₀ hk₀) ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)))
      = ((psiSpr F r n k₀ hk₀) ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n))
    rw [psiSpr_sprGen, sprGen]
    by_cases hk : k = k₀
    · rw [dif_pos hk]
      exact sprPsiSK_xdiag_map F r n σ
    · rw [dif_neg hk]
      exact sprPsiSK_ymat_map F r n σ _

#print axioms sprPsiSK_fixes_psi

/-- ★★★★★ **`κ(c)` 的 `S_n`-不变性**（`κ` 落在 `K'^{S_n}` 里）。 -/
theorem sprCenterK_sfixed [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) (σ : Equiv.Perm (Fin n)) (c : ↥(genericCenter F r n)) :
    sprPermFieldEquiv F r n σ
        (algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c))
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c) := by
  have hfix := sprPsiSK_fixes_psi F r n k₀ hk₀ σ (c : ↥(genericMatrixAlgebra F r n))
  have h2 : sprPsiSK F r n σ
        (Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n)
          (sprCenterK F r n k₀ hk₀ D c)))
      = Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n)
          (sprCenterK F r n k₀ hk₀ D c)) := by
    rw [← psiSpr_center_scalar F r n D k₀ hk₀ c]
    exact hfix
  rw [sprPsiSK_scalar] at h2
  exact Matrix.scalar_inj.mp h2

#print axioms sprCenterK_sfixed

/-- ★★★★★★ **`κ(c) ∈ K'^N`**（终局输入 (i) 的**正命题**，`T` ＋ `S_n` 两侧齐）。 -/
theorem sprCenterK_mem_fixed [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) (c : ↥(genericCenter F r n)) :
    sprFieldNFixed F r n
      (algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)) :=
  ⟨fun b => sprCenterK_tfixed F r n D k₀ hk₀ b c,
   fun σ => sprCenterK_sfixed F r n D k₀ hk₀ σ c⟩

#print axioms sprCenterK_mem_fixed


/-- ★★★★★★ **`κ(C)` 生成的整块域 `Frac(κ(C))` 落在 `K'^N` 里** —— 修正后的输入 (i)。

即 `IntermediateField.adjoin F (κ '' C) ⊆ K'^N`（`K'^N` 用谓词 `sprFieldNFixed` 表述，
因为 `sprNFixedAlg` 是 `Subalgebra`，而 `adjoin` 给的是 `IntermediateField`）。 -/
theorem sprCenterImageField_fixed [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ∀ x ∈ IntermediateField.adjoin F (Set.range (fun c : ↥(genericCenter F r n) =>
        algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c))),
      sprFieldNFixed F r n x := by
  intro x hx
  refine IntermediateField.adjoin_induction (F := F)
    (s := Set.range (fun c : ↥(genericCenter F r n) =>
      algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)))
    (motive := fun x _ => sprFieldNFixed F r n x) ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨c, rfl⟩
    exact sprCenterK_mem_fixed F r n D k₀ hk₀ c
  · intro a
    exact sprFieldNFixed_const F r n a
  · intro a b _ _ iha ihb
    exact sprFieldNFixed_add F r n iha ihb
  · intro a _ iha
    exact sprFieldNFixed_inv F r n iha
  · intro a b _ _ iha ihb
    exact sprFieldNFixed_mul F r n iha ihb

#print axioms sprCenterImageField_fixed

end SprPsiPermFix

/-! ## §30 ★★★★★ **`ZCanon = Frac(C)` 的可实现形态** ＋ `C → K'^N` 的实体

终局装配需要的**第一块**：把 `ZCanon`（`= adjoin F (range centK)`，住在 `SField`）与 `C` 连起来。

| 件 | 内容 |
|---|---|
| ★★★★★★ `zCanon_exists_frac` | `ZCanon` 的每个元都是中心纯量的**分式**：`∃ a b, centK b ≠ 0 ∧ z * centK b = centK a` |
| ★★★★★ `sprCenterAlgHom` | **`↥(genericCenter) →ₐ[F] ↥(sprNFixedAlg)`**（`c ↦ κ c`，落点由 §29 的 `sprCenterK_mem_fixed` 供） |

**为什么 `zCanon_exists_frac` 是装配的钥匙**：`IntermediateField.adjoin` 只给"域"，
而 `IsFractionRing.liftAlgHom` 需要"分式表示"。本条的证明是沿 `adjoin_induction` 的
**共同分母归纳**（`+`／`*` 取 `b·d`，`⁻¹` 交换分子分母；`x = 0` 时取 `0/1`）。

**★ 下一轮的装配路线（已探明，勿再摸）**：
1. Mathlib **有**现成件：`IntermediateField.algebraAdjoinAdjoin.isFractionRing`
   （`Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:58`，**scoped**）：
   `IsFractionRing ↥(Algebra.adjoin F S) ↥(IntermediateField.adjoin F S)`。
   ⟹ 取 `S := Set.range D.centK` 即得 `IsFractionRing ↥(Algebra.adjoin F (range centK)) ↥(ZCanon D)`
   （需 `open scoped IntermediateField.algebraAdjoinAdjoin`）。
2. `centK : ↥C →ₐ[F] ↥(Algebra.adjoin F (range centK))` 是**满射**（像是一个含 `range` 的
   `F`-子代数 ⟹ 含 `adjoin`）⟹ `AlgEquiv`（单射性用 `centK_spec` ＋ `algebraMap` 单射）。
3. 于是 `IsFractionRing.liftAlgHom` 把 `sprCenterAlgHom`（沿 2 的等价搬到 `adjoin` 上）延拓成
   **`↥(ZCanon) →ₐ[F] ↥(sprNFixedAlg)`**。
4. **目标侧需 `Field ↥(sprNFixedAlg)`**（`liftAlgHom` 要求）：本仓只有 `Subalgebra` 实例。
   **做法**：造 `sprNFixedSubfield : Subfield F (SprField)`（载体同谓词；`neg_mem` 由
   `-x = (-1)·x` ＋ `sprFieldNFixed_mul`／`_const` 得），`Subfield` 自带 `Field` 实例，
   再用载体相同的 `AlgEquiv` 搬回 `↥(sprNFixedAlg)`。
5. **反向（满射）**＝ `K'^N ⊆ Frac(κ(C))`（源文 `prop:14.19` 第二半，**未证**）。

**射程（勿夸大）**：本节只给**两块地基**。第 3／4 步的装配**未做**；反向包含**未证**；
`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprZCanonFrac

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

open Matrix
open ABGV52

variable (F : Type) [Field F] (r n : ℕ)

theorem zCanon_exists_frac (D : GenericDivisionData F r n) :
    ∀ z ∈ ZCanon F r n D, ∃ a b : ↥(genericCenter F r n),
      D.centK b ≠ 0 ∧ z * D.centK b = D.centK a := by
  intro z hz
  refine IntermediateField.adjoin_induction (F := F) (s := Set.range D.centK)
    (motive := fun x _ => ∃ a b : ↥(genericCenter F r n),
      D.centK b ≠ 0 ∧ x * D.centK b = D.centK a) ?_ ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨c, rfl⟩
    exact ⟨c, 1, by simp, by simp⟩
  · intro x
    refine ⟨algebraMap F ↥(genericCenter F r n) x, 1, by simp, ?_⟩
    rw [map_one, mul_one]
    exact (AlgHom.commutes D.centK x).symm
  · rintro x y _ _ ⟨a, b, hb, hxy⟩ ⟨c, d, hd, hzw⟩
    refine ⟨a * d + c * b, b * d, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hb hd
    · have e1 : x * (D.centK b * D.centK d) = D.centK a * D.centK d := by
        rw [← mul_assoc, hxy]
      have e2 : y * (D.centK b * D.centK d) = D.centK c * D.centK b := by
        rw [mul_comm (D.centK b) (D.centK d), ← mul_assoc, hzw]
      rw [map_add, map_mul, map_mul, add_mul, e1, e2, map_mul]
  · rintro x _ ⟨a, b, hb, hx⟩
    by_cases ha : D.centK a = 0
    · have hx0 : x = 0 := by
        rw [ha] at hx
        rcases mul_eq_zero.mp hx with h | h
        · exact h
        · exact absurd h hb
      refine ⟨0, 1, by simp, ?_⟩
      rw [hx0, map_one, mul_one, map_zero, _root_.inv_zero]
    · refine ⟨b, a, ha, ?_⟩
      have hxne : x ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hx
        exact ha hx.symm
      rw [← hx, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
  · rintro x y _ _ ⟨a, b, hb, hx⟩ ⟨c, d, hd, hy⟩
    refine ⟨a * c, b * d, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hb hd
    · rw [map_mul, map_mul]
      calc x * y * (D.centK b * D.centK d)
          = (x * D.centK b) * (y * D.centK d) := by ring
        _ = D.centK a * D.centK c := by rw [hx, hy]

#print axioms zCanon_exists_frac


/-- ★★★★★ **`C(F,n,r) →ₐ[F] K'^N`**：中心元 ↦ 其 `κ`-像（落在 `K'^N` 里）。

这是"`Z ≅ Frac(C)`"与"`Frac(κ(C)) ⊆ K'^N`"两者的**共享实体**。 -/
noncomputable def sprCenterAlgHom [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) : ↥(genericCenter F r n) →ₐ[F] ↥(sprNFixedAlg F r n) where
  toFun c := ⟨algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c),
    (mem_sprNFixedAlg F r n).mpr (sprCenterK_mem_fixed F r n D k₀ hk₀ c)⟩
  map_one' := by
    refine Subtype.ext ?_
    show algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D 1) = 1
    rw [map_one, map_one]
  map_mul' := by
    intro a b
    refine Subtype.ext ?_
    show algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D (a * b))
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D a)
        * algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D b)
    rw [map_mul, map_mul]
  map_zero' := by
    refine Subtype.ext ?_
    show algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D 0) = 0
    rw [map_zero, map_zero]
  map_add' := by
    intro a b
    refine Subtype.ext ?_
    show algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D (a + b))
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D a)
        + algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D b)
    rw [map_add, map_add]
  commutes' := by
    intro a
    refine Subtype.ext ?_
    show algebraMap (Spr F r n) (SprField F r n)
        (sprCenterK F r n k₀ hk₀ D (algebraMap F ↥(genericCenter F r n) a))
      = algebraMap F (SprField F r n) a
    rw [sprCenterK, AlgHom.comp_apply, (sprCenterPolyAlgHom F r n D).commutes a,
      (evSpr F r n k₀ hk₀).commutes a]
    exact (IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a).symm

#print axioms sprCenterAlgHom

end SprZCanonFrac

/-! ## §31 ★★★★★★ **装配（第 3–4 步）：`ZCanon` 是 `Algebra.adjoin F (range centK)` 的分式域**

§30 给了装配的钥匙块（`zCanon_exists_frac` ＋ `sprCenterAlgHom`）。本节把 §30 节头配方里的
**第 3、4 步**机检完毕：

| 件 | 内容 |
|---|---|
| ★★★★★★ `zCanon_isFractionRing` | **`IsFractionRing ↥(Algebra.adjoin F (range centK)) ↥(adjoin F (range centK))`** |
| ★★★★ `centK_eq_algebraMap_polyK` | `centK c = algebraMap (sprCenterPolyK c)`（`centK` 的分母形式） |
| ★★★★★ `centK_injective` | **`centK` 单射**（由 `sprCenterPolyK_spec` ＋ `algebraMap` 单射） |
| ★★★★ `centK_surj_adjoin` | **`centK` 打上 `Algebra.adjoin F (range centK)` 是满的** |
| ★★★★★ `centKAdjoinEquiv` | **`↥(genericCenter) ≃ₐ[F] ↥(Algebra.adjoin F (range centK))`** |
| ★★★★ `sprNFixedSubfield` | **`K'^N` 的 `Subfield` 形态**（`sprNFixedAlg` 只是 `Subalgebra`；装配需要 `Field` 实例） |

**工艺（R253，两处实测，同族 R250／R252）**：**`ZCanon` 是 `def`，实例搜索不会展开它**。
① 目标写成 `IsFractionRing _ ↥(ZCanon F r n D)` 时 `Algebra ↥(Algebra.adjoin …) ↥(ZCanon …)`
   **合成失败**（`IsFractionRing` 的类型本身要求 `Algebra` 实例）；正解：**陈述写成显式的
   `IntermediateField.adjoin F (Set.range D.centK)`**（`ZCanon` 与之 defeq）。
② Mathlib 的现成件是 **scoped** 实例：须 `open scoped IntermediateField.algebraAdjoinAdjoin`
   （`Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:58`）。

**射程（勿夸大，逐条）**：
* **未做**：`Algebra F ↥(sprNFixedSubfield)` 实例（`Subfield` 不自动带 `Algebra`；
  须用 `AlgHom.codRestrict` ＋ `RingHom.toAlgebra` 造）——这是 `IsFractionRing.liftAlgHom` 的
  **最后一块前置**；之后即可得 `↥(ZCanon) →ₐ[F] ↥(sprNFixedAlg)`（配方第 6 步）。
* **未证**：反向包含 `K'^N ⊆ Frac(κ(C))`（源文 `prop:14.19` 第二半）。
* `ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprZCanonAssembly

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

/-- `centK c` 是 `sprCenterPolyK` 的 `algebraMap`。 -/
theorem centK_eq_algebraMap_polyK [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (c : ↥(genericCenter F r n)) :
    D.centK c = algebraMap (S F r n) (SField F r n) (sprCenterPolyK F r n D c) := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) (SField F r n) => M i i) (D.centK_spec c)
  have h2 : ((((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))).map
        (algebraMap (S F r n) (SField F r n))) i i
      = (algebraMap (S F r n) (SField F r n)) (sprCenterPolyK F r n D c) := by
    rw [sprCenterPolyK_spec F r n D c]
    simp [Matrix.map_apply, Matrix.scalar_apply]
  rw [h2] at h1
  simpa [Matrix.scalar_apply] using h1.symm

#print axioms centK_eq_algebraMap_polyK

/-- `centK` 单射。 -/
theorem centK_injective [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    Function.Injective D.centK := by
  intro c c' h
  have h1 := centK_eq_algebraMap_polyK F r n D c
  have h2 := centK_eq_algebraMap_polyK F r n D c'
  rw [h1, h2] at h
  have hs : sprCenterPolyK F r n D c = sprCenterPolyK F r n D c' :=
    IsFractionRing.injective (S F r n) (SField F r n) h
  have e1 := sprCenterPolyK_spec F r n D c
  have e2 := sprCenterPolyK_spec F r n D c'
  rw [hs] at e1
  have hfin : ((c : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
      = ((c' : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)) :=
    e1.trans e2.symm
  exact Subtype.ext (Subtype.ext hfin)

#print axioms centK_injective

/-- `K'^N` 作为 `Subfield`（供 `Field` 实例）。 -/
noncomputable def sprNFixedSubfield : Subfield (SprField F r n) where
  carrier := {α | sprFieldNFixed F r n α}
  zero_mem' := sprFieldNFixed_zero F r n
  one_mem' := sprFieldNFixed_one F r n
  add_mem' := fun ha hb => sprFieldNFixed_add F r n ha hb
  neg_mem' := fun ha => by
    have h := sprFieldNFixed_mul F r n (sprFieldNFixed_const F r n (-1)) ha
    simpa using h
  mul_mem' := fun ha hb => sprFieldNFixed_mul F r n ha hb
  inv_mem' := fun x hx => sprFieldNFixed_inv F r n hx

#print axioms sprNFixedSubfield


/-- **`IsFractionRing` 实例的具名形态**（Mathlib 的 scoped 实例 ＋ `ZCanon` 的定义展开）。 -/
theorem zCanon_isFractionRing (D : GenericDivisionData F r n) :
    IsFractionRing ↥(Algebra.adjoin F (Set.range D.centK))
      ↥(IntermediateField.adjoin F (Set.range D.centK)) :=
  inferInstance

#print axioms zCanon_isFractionRing

/-- `centK` 打上 `Algebra.adjoin F (range centK)` 是满的。 -/
theorem centK_surj_adjoin (D : GenericDivisionData F r n) :
    ∀ y ∈ Algebra.adjoin F (Set.range D.centK), ∃ c : ↥(genericCenter F r n), D.centK c = y := by
  intro y hy
  refine Algebra.adjoin_induction (p := fun y _ => ∃ c : ↥(genericCenter F r n), D.centK c = y)
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · intro a
    exact ⟨algebraMap F ↥(genericCenter F r n) a, AlgHom.commutes D.centK a⟩
  · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [map_mul, ha, hb]⟩

#print axioms centK_surj_adjoin

/-- **`centK` 给出 `↥(genericCenter) ≃ₐ[F] ↥(Algebra.adjoin F (range centK))`**。 -/
noncomputable def centKAdjoinEquiv [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    ↥(genericCenter F r n) ≃ₐ[F] ↥(Algebra.adjoin F (Set.range D.centK)) :=
  AlgEquiv.ofBijective
    { toFun := fun c => ⟨D.centK c, Algebra.subset_adjoin ⟨c, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b)
      commutes' := fun a => Subtype.ext (AlgHom.commutes D.centK a) }
    ⟨fun a b h => centK_injective F r n D (Subtype.ext_iff.mp h),
     fun y => by
       obtain ⟨c, hc⟩ := centK_surj_adjoin F r n D y.1 y.2
       exact ⟨c, Subtype.ext hc⟩⟩

#print axioms centKAdjoinEquiv

end SprZCanonAssembly

/-! ## §32 ★★★★★★★★ **装配完成** ＋ **终局归约**：`ZEqNFixed` 只差一条**满射性**

本节把 §30／§31 的地基装成终局映射，并把 `ZEqNFixed` 归约成**一条显式陈述**。

| 件 | 内容 |
|---|---|
| ★★★★ `sprNFixedSubfieldAlgebraMapRingHom`／`sprNFixedSubfieldAlgebra` | `K'^N`（`Subfield` 形态）上的 `F`-代数结构 |
| ★★★★ `sprNFixedSubfieldEquiv` | `↥(sprNFixedSubfield) ≃ₐ[F] ↥(sprNFixedAlg)`（载体相同） |
| ★★★★ `sprCenterToSubfield` | `↥(Algebra.adjoin F (range centK)) →ₐ[F] ↥(K'^N)` |
| ★★★★★ `sprCenterAlgHom_injective` | `sprCenterAlgHom` 单射 |
| ★★★★★★★ `sprCenterZSubfieldMap`／`sprCenterZMap` | **`↥(ZCanon) →ₐ[F] ↥(K'^N)`**（经 `IsFractionRing.liftAlgHom`；配方第 6 步） |
| ★★★★★ `_injective`（两条） | 两者都是**单射**（域到域的 `F`-代数同态） |
| ★★★★★★★★ `zEqNFixed_of_surjective` | **`ZEqNFixed ⟸ sprCenterZMap 满射`** —— 终局归约 |

**★ 意义**：`ZEqNFixed`（H2 的唯一剩余内容）现在**只差一条满射性**：
`sprCenterZMap : ↥(ZCanon) →ₐ[F] ↥(sprNFixedAlg)` 满。因 `sprCenterZMap` 的像是
`Frac(κ(C))`（`κ` 的整块域），满射 ⟺ **反向包含** `K'^N ⊆ Frac(κ(C))`
（源文 `prop:14.19` 的第二半，即 `M_n(K')^N = UD` 那一半）。

**工艺（R254，两处实测）**：
① `def` 不被实例搜索展开的**第二处后果**：`↥(ZCanon) →ₐ[F] …` 的**陈述**会触发
`Algebra ↥(Algebra.adjoin …) ↥(ZCanon …)` 的合成失败 ⟹ **陈述一律写显式
`IntermediateField.adjoin F (Set.range D.centK)`**（与 `ZCanon` defeq）。
② `IsScalarTower F ↥(Algebra.adjoin …) ↥(adjoin …)` 不会被 scoped 实例合成（`X := F` 那一支）
⟹ 在 `by` 块里用 `IsScalarTower.of_algebraMap_eq (fun x => rfl)` 显式给。

**射程（勿夸大）**：**满射性未证**（＝反向包含未证）。`ZEqNFixed` **未证**；
**H2 见文件头「当前状态」。** -/

section SprZCanonAssemblyDone

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

/-- `F →+* ↥(sprNFixedSubfield)`（`algebraMap` 的落点）。 -/
noncomputable def sprNFixedSubfieldAlgebraMapRingHom :
    F →+* ↥(sprNFixedSubfield F r n) where
  toFun a := ⟨algebraMap F (SprField F r n) a, sprFieldNFixed_const F r n a⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

#print axioms sprNFixedSubfieldAlgebraMapRingHom

/-- `K'^N`（`Subfield` 形态）上的 `F`-代数结构。 -/
noncomputable instance sprNFixedSubfieldAlgebra :
    Algebra F ↥(sprNFixedSubfield F r n) :=
  (sprNFixedSubfieldAlgebraMapRingHom F r n).toAlgebra

#print axioms sprNFixedSubfieldAlgebra

/-- `↥(sprNFixedSubfield) ≃ₐ[F] ↥(sprNFixedAlg)`（载体相同的搬运）。 -/
noncomputable def sprNFixedSubfieldEquiv :
    ↥(sprNFixedSubfield F r n) ≃ₐ[F] ↥(sprNFixedAlg F r n) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' a := Subtype.ext rfl

#print axioms sprNFixedSubfieldEquiv


/-- `↥(genericCenter) →ₐ[F] ↥(sprNFixedSubfield)`：`sprCenterAlgHom` 搬到 `Subfield` 形态。 -/
noncomputable def sprCenterToSubfield [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ↥(Algebra.adjoin F (Set.range D.centK)) →ₐ[F] ↥(sprNFixedSubfield F r n) :=
  (sprNFixedSubfieldEquiv F r n).symm.toAlgHom.comp
    ((sprCenterAlgHom F r n D k₀ hk₀).comp (centKAdjoinEquiv F r n D).symm.toAlgHom)

#print axioms sprCenterToSubfield

/-- `sprCenterAlgHom` 单射（`κ` 单射 ＋ `algebraMap` 单射）。 -/
theorem sprCenterAlgHom_injective [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (sprCenterAlgHom F r n D k₀ hk₀) := by
  intro c c' h
  have h1 : algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c') :=
    congrArg Subtype.val h
  exact sprCenterK_injective F r n D k₀ hk₀
    (IsFractionRing.injective (Spr F r n) (SprField F r n) h1)

#print axioms sprCenterAlgHom_injective

/-- ★★★★ **`sprCenterToSubfield` 单射**（`κ` 单射 ＋ 两次载体搬运）。

**为什么单列一条定理（R257，实测根因）**：若把单射性写成**内联 `have`**，
`IsFractionRing.liftAlgHom` 的使用处会把它的型 **`whnf` 成 Pi 型**
（`∀ ⦃a b⦄, g a = g b → a = b`），于是 `sprCenterZSubfieldMap` 的展开体里
含一个**类型已展开**的证明项 ⟹ `rw [IsFractionRing.liftAlgHom_apply]` 在
`implicit` 透明度下判该应用不合法，报 "Did not find an occurrence"（第 393 轮 R256 的**真根因**）。
**具名定理的陈述保持 `Function.Injective` 的折叠形态**，故计算律可 `rw` 通过。 -/
theorem sprCenterToSubfield_injective [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (sprCenterToSubfield F r n D k₀ hk₀) := by
  intro a b h
  have h2 : (sprCenterAlgHom F r n D k₀ hk₀ ((centKAdjoinEquiv F r n D).symm.toAlgHom a))
      = (sprCenterAlgHom F r n D k₀ hk₀
          ((centKAdjoinEquiv F r n D).symm.toAlgHom b)) :=
    (sprNFixedSubfieldEquiv F r n).symm.injective h
  exact (centKAdjoinEquiv F r n D).symm.injective
    (sprCenterAlgHom_injective F r n D k₀ hk₀ h2)

#print axioms sprCenterToSubfield_injective

/-- 装配第 6 步（`Subfield` 目标形态）：`↥(ZCanon) →ₐ[F] ↥(sprNFixedSubfield)`。

注入性参数取**具名定理** `sprCenterToSubfield_injective`（见其文档：内联 `have` 会让
`whnf` 展开证明项的型，致计算律无法 `rw`）。 -/
noncomputable def sprCenterZSubfieldMap [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ↥(IntermediateField.adjoin F (Set.range D.centK)) →ₐ[F]
      ↥(sprNFixedSubfield F r n) := by
  classical
  haveI : IsScalarTower F ↥(Algebra.adjoin F (Set.range D.centK))
      ↥(IntermediateField.adjoin F (Set.range D.centK)) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsFractionRing ↥(Algebra.adjoin F (Set.range D.centK))
      ↥(IntermediateField.adjoin F (Set.range D.centK)) := inferInstance
  exact IsFractionRing.liftAlgHom (g := sprCenterToSubfield F r n D k₀ hk₀)
    (sprCenterToSubfield_injective F r n D k₀ hk₀)

#print axioms sprCenterZSubfieldMap

/-- `sprCenterZSubfieldMap` **单射**（域到域的 `F`-代数同态）。 -/
theorem sprCenterZSubfieldMap_injective [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (sprCenterZSubfieldMap F r n D k₀ hk₀) :=
  algHom_injective_of_field F (sprCenterZSubfieldMap F r n D k₀ hk₀)

#print axioms sprCenterZSubfieldMap_injective

/-- ★★★★★★★ **装配完成（配方第 6 步）**：`↥(ZCanon) →ₐ[F] ↥(sprNFixedAlg)`。 -/
noncomputable def sprCenterZMap [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ↥(IntermediateField.adjoin F (Set.range D.centK)) →ₐ[F] ↥(sprNFixedAlg F r n) :=
  (sprNFixedSubfieldEquiv F r n).toAlgHom.comp (sprCenterZSubfieldMap F r n D k₀ hk₀)

#print axioms sprCenterZMap

/-- `sprCenterZMap` **单射**（复合两个单射）。 -/
theorem sprCenterZMap_injective [Nonempty (Fin n)] [NeZero n] (D : GenericDivisionData F r n)
    (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (sprCenterZMap F r n D k₀ hk₀) :=
  (sprNFixedSubfieldEquiv F r n).injective.comp
    (sprCenterZSubfieldMap_injective F r n D k₀ hk₀)

#print axioms sprCenterZMap_injective

section Endgame
variable [CharZero F]

/-- ★★★★★★★★ **终局归约**：`ZEqNFixed` **只差** `sprCenterZMap` 的**满射性**。

满射性正是"反向包含" `K'^N ⊆ Frac(κ(C))`（源文 `prop:14.19` 第二半）的**精确形态**：
`sprCenterZMap` 的像是 `Frac(κ(C))`（`κ` 的整块域），故满射 ⟺ 每个 `N`-不变元都落在其中。 -/
theorem zEqNFixed_of_surjective (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0) (h : Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)) :
    ZEqNFixed F D :=
  zEqNFixed_of_ZCanonEquiv F D
    ⟨AlgEquiv.ofBijective (sprCenterZMap F 2 9 D k₀ hk₀)
      ⟨sprCenterZMap_injective F 2 9 D k₀ hk₀, h⟩⟩

#print axioms zEqNFixed_of_surjective

end Endgame

/-! ### §32.1 ★★★★★ `sprCenterZMap` 的**计算律**：把"像 = `Frac(κ(C))`"接线

第 391／393 轮（R255／R256）两轮受阻的计算律，本轮以 **R257**（把单射性提成**具名定理**
`sprCenterToSubfield_injective`）解除。本节四条是 `wiki/proj-abgv52-h2-endgame-corrected.md`
§7.1 **第 1 项**的全部内容：

| 件 | 内容 |
|---|---|
| ★★★★★ `sprCenterZSubfieldMap_algebraMap` | `liftAlgHom` 在 `algebraMap` 的像上**就是** `sprCenterToSubfield` |
| ★★★★★ `sprCenterToSubfield_centK` | `sprCenterToSubfield (centKAdjoinEquiv c) = ⟨algebraMap (κ c), _⟩` |
| ★★★★★ `sprCenterZMap_centK` | `sprCenterZMap (algebraMap (centKAdjoinEquiv c)) = ⟨algebraMap (κ c), _⟩` |
| ★★★★★ `sprCenterK_mem_range_sprCenterZMap` | **`κ(C) ⊆ Set.range (sprCenterZMap)`** |

**数学意义**：`sprCenterZMap` 的像**含** `κ(C)`，而像落在 `K'^N` 里（由 `sprCenterK_mem_fixed`
逐点给出），故有夹逼 `Frac(κ(C)) ⊆ range ⊆ K'^N`。于是"满射"⟺**反向包含**
`K'^N ⊆ Frac(κ(C))`，即源文 `prop:14.19` 的**第二半**——这是 H2 唯一剩余的数学内容。

**工艺（R257，第 393 轮 R256 的根因与正解）**：
* **根因**：`IsFractionRing.liftAlgHom` 把注入性参数的型 **`whnf` 成 Pi 型**
  （`∀ ⦃a b⦄, g a = g b → a = b`）。若该参数是**内联 `have`**，则 `sprCenterZSubfieldMap`
  展开后含**类型已展开**的证明项，`rw [IsFractionRing.liftAlgHom_apply]` 在 `implicit`
  透明度下判 `liftAlgHom ⋯` 这个**应用本身**不合法，报 "Did not find an occurrence"。
  `dsimp only`／`with_unfolding_all`／`simp only` **均无效**（三者实测均失败）。
* **正解**：把单射性提成**具名定理**（其陈述保持 `Function.Injective` 的折叠形态），
  在 `def` 体里只**引用**它 ⟹ `unfold sprCenterZSubfieldMap` 之后 `rw` 直接通过
  （**不需要** `dsimp`——`def` 体里已无 `have`）。
* 收尾仍需一次 `rfl`：`(sprCenterToSubfield ⋯).toRingHom x` 与 `(⋯) x` 定义相等，
  但 `rw` 的模式不认（**R252 同族**，第 7 次）。

**射程（勿夸大）**：本节**未证**满射性（即未证反向包含）；`ZEqNFixed` **未证**；
**H2 见文件头「当前状态」。** -/

/-- ★★★★★ **计算律（第 1 项，一半）**：`sprCenterZSubfieldMap` 在 `algebraMap` 的像上
就是 `sprCenterToSubfield`——即 `liftAlgHom` 的**定义性质**。

`rw` 之后仍在 `.toRingHom` 形态上差一步，由 `rfl` 收口（R252 同族）。 -/
theorem sprCenterZSubfieldMap_algebraMap [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (x : ↥(Algebra.adjoin F (Set.range D.centK))) :
    sprCenterZSubfieldMap F r n D k₀ hk₀
        (algebraMap ↥(Algebra.adjoin F (Set.range D.centK))
          ↥(IntermediateField.adjoin F (Set.range D.centK)) x)
      = sprCenterToSubfield F r n D k₀ hk₀ x := by
  classical
  unfold sprCenterZSubfieldMap
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

#print axioms sprCenterZSubfieldMap_algebraMap

/-- ★★★★★ **计算律（第 1 项，另一半）**：`sprCenterToSubfield` 在 `centK c` 处的值
**就是 `κ c`**（收口用 `AlgEquiv.symm_apply_apply`）。 -/
theorem sprCenterToSubfield_centK [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    sprCenterToSubfield F r n D k₀ hk₀ (centKAdjoinEquiv F r n D c)
      = (⟨algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c),
          sprCenterK_mem_fixed F r n D k₀ hk₀ c⟩ : ↥(sprNFixedSubfield F r n)) := by
  rw [sprCenterToSubfield]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [AlgEquiv.symm_apply_apply]
  rfl

#print axioms sprCenterToSubfield_centK

/-- ★★★★★ **`sprCenterZMap` 在中心元处的值**：`⟨algebraMap (κ c), _⟩`。

这是"像 = `Frac(κ(C))`"的接线点：`sprCenterZMap` 的像**至少**含整个 `κ(C)`。 -/
theorem sprCenterZMap_centK [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    sprCenterZMap F r n D k₀ hk₀
        (algebraMap ↥(Algebra.adjoin F (Set.range D.centK))
          ↥(IntermediateField.adjoin F (Set.range D.centK)) (centKAdjoinEquiv F r n D c))
      = (⟨algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c),
          sprCenterK_mem_fixed F r n D k₀ hk₀ c⟩ : ↥(sprNFixedAlg F r n)) := by
  rw [sprCenterZMap, AlgHom.comp_apply, sprCenterZSubfieldMap_algebraMap,
    sprCenterToSubfield_centK]
  rfl

#print axioms sprCenterZMap_centK

/-- ★★★★★ **`κ(C)` 落在 `sprCenterZMap` 的像里**（`Set.range` 形态）。

与 `sprCenterK_mem_fixed`（像 ⊆ `K'^N`）合起来给出夹逼
`Frac(κ(C)) ⊆ range (sprCenterZMap) ⊆ K'^N`，故满射 ⟺ 反向包含。 -/
theorem sprCenterK_mem_range_sprCenterZMap [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    (⟨algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c),
        sprCenterK_mem_fixed F r n D k₀ hk₀ c⟩ : ↥(sprNFixedAlg F r n))
      ∈ Set.range (sprCenterZMap F r n D k₀ hk₀) :=
  ⟨_, sprCenterZMap_centK F r n D k₀ hk₀ c⟩

#print axioms sprCenterK_mem_range_sprCenterZMap


end SprZCanonAssemblyDone

/-! ## §33 ★★★★★★★★ **H2 的最终接口**：满射性 ⟹ `ProcesiS9Hyp`

`H2Final` §32 已把 `ZEqNFixed` 归约成 `sprCenterZMap` 的满射性；本节把**最后一格**接上：
满射性直接给出 **H2 的陈述本身**（`ProcesiS9Hyp F ↥(ZCanon F 2 9 D)`）。

**⟹ H2 的完整剩余内容 = 一条命题**：
`Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)`
（等价于反向包含 `K'^N ⊆ Frac(κ(C))`，源文 `prop:14.19` 的第二半）。

**射程（勿夸大）**：满射性**未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。**
反向包含的 Lean 目标清单见 `wiki/proj-abgv52-h2-endgame-corrected.md` §7。 -/

section SprH2Interface

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F]

/-- ★★★★★★★★ **H2 的最终接口**：`sprCenterZMap` 的**满射性** ⟹ `H2`（`ProcesiS9Hyp`）。 -/
theorem h2_of_surjective [CharZero F] (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0) (h : Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_surjective F D hk₀ h)

#print axioms h2_of_surjective

/-! ## §34 ★★★★★ `Frac(κ(C))` 的 **`IntermediateField` 实体** ＋ H2 剩余的**陈述级**形态

§32.1 的计算律把 `κ(C)` 接进 `sprCenterZMap` 的像；本节把**像的整块域**（＝ `Frac(κ(C))`，
源文 `prop:14.19` 的 `Z`）做成 `SprField` 的**中间域**，从而

1. **得到 `(B)` 层 `Z`-代数结构的载体**：`Algebra ↥(sprCenterImageField …) (SprField …)`
   由 `IntermediateField` 的**通用实例**直接给出（R258：这是选 `IntermediateField` 而非
   `↥(ZCanon)` 的理由——`Algebra ↥(ZCanon) (SprField)` 若写成带 `k₀` 参数的 `def`，
   实例搜索无法猜出 `k₀ : Fin r`，每条陈述都得显式 `letI`）；
2. **把 H2 的唯一剩余换成陈述级形态**：`surjective_of_nfixed_le_imageField`
   —— "每个 `N`-固定元都在 `Frac(κ(C))` 里" ⟹ `sprCenterZMap` 满射 ⟹ H2。

| 件 | 内容 |
|---|---|
| ★★★★ `sprCenterImageField` | `Frac(κ(C))` 作为 `IntermediateField F (SprField)` |
| ★★★★ `sprCenterK_mem_sprCenterImageField` | `κ(C) ⊆ Frac(κ(C))` |
| ★★★★ `sprCenterToSubfield_mk_centK` | `sprCenterToSubfield ⟨centK c, _⟩ = ⟨algebraMap (κ c), _⟩` |
| ★★★★★ `sprCenterZMap_algebraMap`／`_mk_centK` | `sprCenterZMap` 的两条计算律（`↥(ZCanon)` 形态） |
| ★★★★★ `sprCenterZMap_mem_sprCenterImageField` | **像 ⊆ `Frac(κ(C))`**（用 `zCanon_exists_frac` 的共分母形式） |
| ★★★★ `sprCenterZMap_val_inv` | 值层 `⁻¹` 律（`↥(sprNFixedAlg)` 无 `Inv` ⟹ 在 `SprField` 层陈述） |
| ★★★★★ `sprCenterImageField_le_range` | **`Frac(κ(C))` ⊆ 像**（`adjoin_induction` 逐条对住） |
| ★★★★★★★ `surjective_of_nfixed_le_imageField` | **H2 剩余 = `K'^N ⊆ Frac(κ(C))`**（陈述级） |

**工艺（R258）**：`↥(ZCanon)` 与 `↥(IntermediateField.adjoin F (Set.range D.centK))` 是 **defeq
但不同一**的类型：`sprCenterZMap` 的定义域是**后者**。凡涉及 `sprCenterZMap` 的引理，
**陈述一律展开成 `IntermediateField.adjoin …`**（否则 `simp`／`rw` 在 `implicit` 透明度下
报 "application type mismatch"，与 R257 同族）；`⟨centK c, _⟩ : ↥(ZCanon)` 只在
`sprCenterZMap_mk_centK` 里用一次 `Subtype.ext rfl` 搬运。

**射程（勿夸大）**：`K'^N ⊆ Frac(κ(C))` **未证**（＝ `prop:14.19` 第二半，仍是 H2 的全部剩余）；
`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprImageField

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

/-- `Frac(κ(C))` 作为 `SprField` 的**中间域**＝`IntermediateField`。

**为什么用 `IntermediateField` 而不是 `↥(ZCanon)`**（R258 的关节点）：`IntermediateField F K`
的载体**自带** `Algebra ↥Z K` 实例（`(A)` 层 `etaK1` 就是这么做成的），而
`Algebra ↥(ZCanon) (SprField)` 若写成带 `k₀` 参数的 `def`，**实例搜索无法猜出 `k₀`**
（`k₀ : Fin r` 不是可合成类型）⟹ 每条陈述都得显式 `letI`。改用 `IntermediateField` 后，
`TensorProduct ↥(sprCenterImageField D k₀ hk₀) (SprField) (SprField)` 里的
`Algebra ↥(…) (SprField)` 由**通用实例**给出，`k₀` 已由目标里的这一项确定 ⟹ 无需 `letI`。 -/
noncomputable def sprCenterImageField [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    IntermediateField F (SprField F r n) :=
  IntermediateField.adjoin F (Set.range (fun c : ↥(genericCenter F r n) =>
    algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)))

#print axioms sprCenterImageField

/-- `κ(C) ⊆ Frac(κ(C))`。 -/
theorem sprCenterK_mem_sprCenterImageField [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)
      ∈ sprCenterImageField F r n D k₀ hk₀ :=
  IntermediateField.subset_adjoin F _ ⟨c, rfl⟩

#print axioms sprCenterK_mem_sprCenterImageField

/-- `sprCenterToSubfield` 在 `⟨centK c, _⟩` 处的值（`centKAdjoinEquiv c` 的形态搬运）。 -/
theorem sprCenterToSubfield_mk_centK [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    sprCenterToSubfield F r n D k₀ hk₀
        (⟨D.centK c, Algebra.subset_adjoin (Set.mem_range_self c)⟩ :
          ↥(Algebra.adjoin F (Set.range D.centK)))
      = (⟨algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c),
          sprCenterK_mem_fixed F r n D k₀ hk₀ c⟩ : ↥(sprNFixedSubfield F r n)) := by
  rw [show (⟨D.centK c, Algebra.subset_adjoin (Set.mem_range_self c)⟩ :
      ↥(Algebra.adjoin F (Set.range D.centK))) = centKAdjoinEquiv F r n D c from
    Subtype.ext rfl]
  exact sprCenterToSubfield_centK F r n D k₀ hk₀ c

#print axioms sprCenterToSubfield_mk_centK

/-- ★★★★★ `sprCenterZMap` 的计算律（`algebraMap` 形态，`sprCenterToSubfield` 复合）。 -/
theorem sprCenterZMap_algebraMap [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (x : ↥(Algebra.adjoin F (Set.range D.centK))) :
    sprCenterZMap F r n D k₀ hk₀
        (algebraMap ↥(Algebra.adjoin F (Set.range D.centK))
          ↥(IntermediateField.adjoin F (Set.range D.centK)) x)
      = (⟨(sprCenterToSubfield F r n D k₀ hk₀ x : ↥(sprNFixedSubfield F r n)).1,
          (sprCenterToSubfield F r n D k₀ hk₀ x).2⟩ : ↥(sprNFixedAlg F r n)) := by
  rw [sprCenterZMap, AlgHom.comp_apply, sprCenterZSubfieldMap_algebraMap]
  rfl

#print axioms sprCenterZMap_algebraMap

/-- ★★★★★ **`sprCenterZMap` 在 `⟨centK c, _⟩` 处的值**（`↥(ZCanon)` 直接形态）。 -/
theorem sprCenterZMap_mk_centK [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    sprCenterZMap F r n D k₀ hk₀
        (⟨D.centK c, IntermediateField.subset_adjoin F _ ⟨c, rfl⟩⟩ : ↥(IntermediateField.adjoin F (Set.range D.centK)))
      = (⟨algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c),
          sprCenterK_mem_fixed F r n D k₀ hk₀ c⟩ : ↥(sprNFixedAlg F r n)) := by
  rw [show (⟨D.centK c, IntermediateField.subset_adjoin F _ ⟨c, rfl⟩⟩ : ↥(IntermediateField.adjoin F (Set.range D.centK)))
      = algebraMap ↥(Algebra.adjoin F (Set.range D.centK))
          ↥(IntermediateField.adjoin F (Set.range D.centK))
          (⟨D.centK c, Algebra.subset_adjoin (Set.mem_range_self c)⟩ :
            ↥(Algebra.adjoin F (Set.range D.centK))) from Subtype.ext rfl]
  rw [sprCenterZMap_algebraMap, sprCenterToSubfield_mk_centK]

#print axioms sprCenterZMap_mk_centK

/-- ★★★★★ **`sprCenterZMap` 的像落在 `Frac(κ(C))` 里**（用 `zCanon_exists_frac` 的共分母形式）。 -/
theorem sprCenterZMap_mem_sprCenterImageField [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(IntermediateField.adjoin F (Set.range D.centK))) :
    ((sprCenterZMap F r n D k₀ hk₀ z : ↥(sprNFixedAlg F r n)) : SprField F r n)
      ∈ sprCenterImageField F r n D k₀ hk₀ := by
  classical
  obtain ⟨a, b, hb, hz⟩ := zCanon_exists_frac F r n D z z.2
  have hZa := sprCenterZMap_mk_centK F r n D k₀ hk₀ a
  have hZb := sprCenterZMap_mk_centK F r n D k₀ hk₀ b
  have hmulZ : z * (⟨D.centK b, IntermediateField.subset_adjoin F _ ⟨b, rfl⟩⟩ :
      ↥(IntermediateField.adjoin F (Set.range D.centK)))
      = (⟨D.centK a, IntermediateField.subset_adjoin F _ ⟨a, rfl⟩⟩ :
        ↥(IntermediateField.adjoin F (Set.range D.centK))) := by
    refine Subtype.ext ?_
    show (z : SField F r n) * D.centK b = D.centK a
    exact hz
  have hmul := congrArg (fun w => sprCenterZMap F r n D k₀ hk₀ w) hmulZ
  simp only [map_mul] at hmul
  rw [hZa, hZb] at hmul
  have h5 : ((sprCenterZMap F r n D k₀ hk₀ z : ↥(sprNFixedAlg F r n)) : SprField F r n)
      * algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D b)
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D a) := by
    have h6 := congrArg (fun w : ↥(sprNFixedAlg F r n) => (w : SprField F r n)) hmul
    simpa using h6
  have hb0 : b ≠ 0 := by
    intro h
    exact hb (by rw [h, map_zero])
  have hkb : sprCenterK F r n k₀ hk₀ D b ≠ 0 := by
    intro h
    exact hb0 (sprCenterK_injective F r n D k₀ hk₀ (by rw [h, map_zero]))
  have hneb : algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D b) ≠ 0 := by
    intro h
    exact hkb (IsFractionRing.injective (Spr F r n) (SprField F r n) (by rw [h, map_zero]))
  have hval : ((sprCenterZMap F r n D k₀ hk₀ z : ↥(sprNFixedAlg F r n)) : SprField F r n)
      = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D a)
        / algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D b) := by
    rw [eq_div_iff hneb]
    exact h5
  rw [hval]
  exact div_mem (sprCenterK_mem_sprCenterImageField F r n D k₀ hk₀ a)
    (sprCenterK_mem_sprCenterImageField F r n D k₀ hk₀ b)

#print axioms sprCenterZMap_mem_sprCenterImageField

/-- `sprCenterZMap` 的**值层 `⁻¹` 律**（目标 `↥(sprNFixedAlg)` 是 `Subalgebra`，无 `Inv` 实例
⟹ 须在 `SprField` 层陈述，经 `sprCenterZSubfieldMap` 的 `map_inv₀` 搬运）。 -/
theorem sprCenterZMap_val_inv [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (w : ↥(IntermediateField.adjoin F (Set.range D.centK))) :
    ((sprCenterZMap F r n D k₀ hk₀ w⁻¹ : ↥(sprNFixedAlg F r n)) : SprField F r n)
      = (((sprCenterZMap F r n D k₀ hk₀ w : ↥(sprNFixedAlg F r n)) : SprField F r n))⁻¹ := by
  have h : ∀ v : ↥(IntermediateField.adjoin F (Set.range D.centK)),
      ((sprCenterZMap F r n D k₀ hk₀ v : ↥(sprNFixedAlg F r n)) : SprField F r n)
      = ((sprCenterZSubfieldMap F r n D k₀ hk₀ v : ↥(sprNFixedSubfield F r n)) : SprField F r n) :=
    fun v => rfl
  rw [h, h]
  exact congrArg (fun v : ↥(sprNFixedSubfield F r n) => (v : SprField F r n))
    (map_inv₀ (sprCenterZSubfieldMap F r n D k₀ hk₀) w)

#print axioms sprCenterZMap_val_inv

/-- ★★★★★ **反向：`Frac(κ(C))` 的每个元素都在 `sprCenterZMap` 的像里**。

用 `IntermediateField.adjoin_induction` 逐条对住：生成元 = `sprCenterK_mem_range_sprCenterZMap`；
`algebraMap`／加／乘／逆都在像里（`sprCenterZMap` 是环同态）。 -/
theorem sprCenterImageField_le_range [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ∀ x ∈ sprCenterImageField F r n D k₀ hk₀,
      x ∈ Set.range (fun z : ↥(IntermediateField.adjoin F (Set.range D.centK)) =>
        ((sprCenterZMap F r n D k₀ hk₀ z : ↥(sprNFixedAlg F r n)) : SprField F r n)) := by
  intro x hx
  refine IntermediateField.adjoin_induction (F := F)
    (s := Set.range (fun c : ↥(genericCenter F r n) =>
      algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)))
    (motive := fun x _ => x ∈ Set.range (fun z : ↥(IntermediateField.adjoin F (Set.range D.centK)) =>
      ((sprCenterZMap F r n D k₀ hk₀ z : ↥(sprNFixedAlg F r n)) : SprField F r n))) ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨c, rfl⟩
    obtain ⟨z, hz⟩ := sprCenterK_mem_range_sprCenterZMap F r n D k₀ hk₀ c
    exact ⟨z, congrArg Subtype.val hz⟩
  · intro a
    refine ⟨algebraMap F ↥(IntermediateField.adjoin F (Set.range D.centK)) a, ?_⟩
    show ((sprCenterZMap F r n D k₀ hk₀
      (algebraMap F ↥(IntermediateField.adjoin F (Set.range D.centK)) a) :
        ↥(sprNFixedAlg F r n)) : SprField F r n) = algebraMap F (SprField F r n) a
    rw [AlgHom.commutes]
    rfl
  · rintro x y _ _ ⟨zx, rfl⟩ ⟨zy, rfl⟩
    refine ⟨zx + zy, ?_⟩
    show ((sprCenterZMap F r n D k₀ hk₀ (zx + zy) : ↥(sprNFixedAlg F r n)) : SprField F r n)
      = ((sprCenterZMap F r n D k₀ hk₀ zx : ↥(sprNFixedAlg F r n)) : SprField F r n)
        + ((sprCenterZMap F r n D k₀ hk₀ zy : ↥(sprNFixedAlg F r n)) : SprField F r n)
    rw [map_add]
    rfl
  · rintro x _ ⟨zx, rfl⟩
    exact ⟨zx⁻¹, sprCenterZMap_val_inv F r n D k₀ hk₀ zx⟩
  · rintro x y _ _ ⟨zx, rfl⟩ ⟨zy, rfl⟩
    refine ⟨zx * zy, ?_⟩
    show ((sprCenterZMap F r n D k₀ hk₀ (zx * zy) : ↥(sprNFixedAlg F r n)) : SprField F r n)
      = ((sprCenterZMap F r n D k₀ hk₀ zx : ↥(sprNFixedAlg F r n)) : SprField F r n)
        * ((sprCenterZMap F r n D k₀ hk₀ zy : ↥(sprNFixedAlg F r n)) : SprField F r n)
    rw [map_mul]
    rfl

#print axioms sprCenterImageField_le_range

/-- ★★★★★★★ **H2 唯一剩余的**最简形式**：`K'^N ⊆ Frac(κ(C))` ⟹ `sprCenterZMap` 满射。

这就是源文 `prop:14.19` **第二半**的**陈述级**形态（不需要任何 `⊤`／`AlgEquiv` 包装）：
只需对每个 `N`-固定元证明它落在 `Frac(κ(C))` 里。 -/
theorem surjective_of_nfixed_le_imageField [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : ∀ x : SprField F r n, sprFieldNFixed F r n x →
      x ∈ sprCenterImageField F r n D k₀ hk₀) :
    Function.Surjective (sprCenterZMap F r n D k₀ hk₀) := by
  intro y
  obtain ⟨z, hz⟩ := sprCenterImageField_le_range F r n D k₀ hk₀ (y : SprField F r n) (h _ y.2)
  exact ⟨z, Subtype.ext hz⟩

#print axioms surjective_of_nfixed_le_imageField

/-! ## §35 ★★★★★ `(B)` 层张量世界：`S'' = K' ⊗_Z K'` ＋ `η_i` ＋ `UD` 的 `K'`-世界实体

源文 `:456`（`prop:14.19` 证明）："Set `S'' = S' ⊗_Z K'` where `Z = Z(F,n,r)`.
Define `η_1, η_2 : K' → S''` by `η_1(x) = x ⊗ 1` and `η_2(x) = 1 ⊗ x`.
Consider `M_n(K') = K' ⊗_Z UD(F,n,r)` … Define `θ_i = η_i ⊗ ι`."

本节的四块是 §7.1 第 2／3 项的**载体层**，与 `(A)` 层 `GenericInv` §41 逐字同构：

| 件 | 内容 | `(A)` 层对应件 |
|---|---|---|
| ★★★★★ `sprTensorK` | `S'' := K' ⊗_Z K'` | `TensorProduct ↥(ZCanon) (SField) (SField)` |
| ★★★★ `etaSprK1`／`etaSprK2` | `η_i = includeLeft/inclRight` | `etaK1`／`etaK2` |
| ★★★★ `etaSprK1_eq_etaSprK2_on_Z`／`_of_mem` | "`η_i` 在 `Z` 上相等" | `etaK1_eq_etaK2_on_Z`／`eta_eq_iff_mem` |
| ★★★★★★ `UDK'`／`psiSpr_mem_UDK'` | **`UD` 的 `K'`-世界实体**（源文 `:415`） | `UDCanon` |

**★ 源文 `S'' = S' ⊗_Z K'` 的正确读法（R258②，第 396 轮已登记）**：`Z = Z(F,n,r)` 是**域**
（`:321` "Since `Z` is a field"），而 `κ(C) ⊆ S'` 只是子环 ⟹ `S'` **不是** `Z`-代数
（`Z` 的分母在 `S'` 里不可逆）⟹ `TensorProduct ↥Z (Spr) (SprField)` **不可写**。
正解 = 与 `(A)` 层同形：取 `K' ⊗_Z K'`；它把 `M_n(S')`（经 `M_n(K')`）的像全含进来，
故 `lem:14.24`（`GenericInv` §137，已机检）的前提"`θ_i` 在 `R` 上一致"照旧可取。

**工艺（R258①，实测）**：`Algebra ↥(sprCenterImageField …) (SprField …)` 由
`IntermediateField` 的**通用实例**给出，故 `TensorProduct`／`Algebra.adjoin`／
`Subalgebra ↥Z (Matrix …)` 的陈述**直接可写**，无需 `letI`——这是本节能一次通过的关键。

**射程（勿夸大）**：`UDK' ⊆ M_n(K')^N`（`prop:14.19` **第一半**）与等化子判据**均未证**；
`K'^N ⊆ Frac(κ(C))`（第二半）**未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprTensorWorld

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`S'' := K' ⊗_Z K'`**（源文 `:456` 的 `S''`，`Z = Frac(κ(C))` = `sprCenterImageField`）。

**为什么不是字面的 `S' ⊗_Z K'`**：`Z` 是**域**（`κ(C)` 的分式域），而 `κ(C) ⊆ S'` 只是子环
⟹ `S'` **不是** `Z`-代数（`Z` 的分母在 `S'` 里不可逆）⟹ `TensorProduct ↥Z (Spr) (SprField)`
**不可写**。取 `K' ⊗_Z K'` 与 `(A)` 层 `GenericDivisionTheta` 的 `TensorProduct ↥(ZCanon) (SField) (SField)`
逐字同构；它把 `M_n(S')`（经 `M_n(K')`）的像全含进来，故 `lem:14.24` 的前提照样可取。 -/
abbrev sprTensorK [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :=
  TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀) (SprField F r n) (SprField F r n)

#print axioms sprTensorK

/-- `η₁ : K' → S''`，`x ↦ x ⊗ 1`（源文 `:456`）。 -/
noncomputable def etaSprK1 [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    SprField F r n →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)] sprTensorK F r n D k₀ hk₀ :=
  Algebra.TensorProduct.includeLeft

#print axioms etaSprK1

/-- `η₂ : K' → S''`，`x ↦ 1 ⊗ x`（源文 `:456`）。 -/
noncomputable def etaSprK2 [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    SprField F r n →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)] sprTensorK F r n D k₀ hk₀ :=
  Algebra.TensorProduct.includeRight

#print axioms etaSprK2

/-- ★★★ **源文 `:456`／`:321` 的 "the `η_i` are equal on `Z`"**（`(B)` 层）—— 机检形态。 -/
theorem etaSprK1_eq_etaSprK2_on_Z [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(sprCenterImageField F r n D k₀ hk₀)) :
    etaSprK1 F r n D k₀ hk₀ (algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
        (SprField F r n) z)
      = etaSprK2 F r n D k₀ hk₀ (algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
        (SprField F r n) z) := by
  rw [AlgHom.commutes (etaSprK1 F r n D k₀ hk₀), AlgHom.commutes (etaSprK2 F r n D k₀ hk₀)]

#print axioms etaSprK1_eq_etaSprK2_on_Z

/-- **推论**：`η₁ = η₂` 在 `Z` 的像上（`∈` 形态，供装配时逐点用）。 -/
theorem etaSprK1_eq_etaSprK2_of_mem [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {x : SprField F r n} (hx : x ∈ sprCenterImageField F r n D k₀ hk₀) :
    etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x := by
  have h := etaSprK1_eq_etaSprK2_on_Z F r n D k₀ hk₀ ⟨x, hx⟩
  simpa using h

#print axioms etaSprK1_eq_etaSprK2_of_mem

/-- ★★★★★★ **`UD` 的 `K'`-世界实体**（源文 `:415` "consider `UD(F,n,r)` a subalgebra of `M_n(K')`"）。

`UD = R·Z`，故其在 `ψ`（`lem:14.22`）下的像 = 由 `ψ(X_k)`（`k : Fin r`）在 `Z = Frac(κ(C))`
上生成的 `Z`-子代数。**`(A)` 层载体 `UDCanon`（`GenericInv:3352`）的逐字同构**：
那里是 `Algebra.adjoin ↥(ZCanon) (range genMatKF)`，这里把 `genMatKF`（`S`-世界）换成
`ψ(X_k)` 的 `K'`-像。 -/
noncomputable def UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Subalgebra ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n)) :=
  Algebra.adjoin ↥(sprCenterImageField F r n D k₀ hk₀)
    (Set.range (fun k : Fin r =>
      (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n))))

#print axioms UDK'

/-- `UD` 的 `K'`-世界生成元都在 `UDK'` 里。 -/
theorem psiSpr_mem_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) (k : Fin r) :
    (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)) ∈ UDK' F r n D k₀ hk₀ :=
  Algebra.subset_adjoin ⟨k, rfl⟩

#print axioms psiSpr_mem_UDK'

/-! ## §36 ★★★★ `Z ⊆ Z(UDK')`：`UD` 的 `K'`-世界实体的**中心下界**

源文 `:321`／`:456` 的等化子论证末步需要 `UD` 的中心：`Z(UD) = Z`。本节给其中的**易方向**
`Z ⊆ Z(UDK')`——`Z` 作用为纯量矩阵，故与一切矩阵交换（`sprScalar_mul_comm`）。

**★ 工艺／纪律教训（L47 实案，第 398 轮）**：本轮**先写了** `sprDiagMatK_mul_inv`／
`sprPsiDK_add`／`_mul`／`_one`／`_zero` 五条，插入时**全部被 `lake build` 挡下**
（`has already been declared`）——它们**早已存在**：`sprDiagMatK_mul_inv`、
`sprPsiDK_add/mul/one/zero` 都在 `GenericInv`／`H2Final` 里，且 `sprPsiDK` 早已打包成
`sprPsiDKAlgHom : Matrix →ₐ[F] Matrix`（`H2Final:2925`）⟹ `map_add`／`map_mul` **本来就免费**。
**触发条件与动作**：写"某某是环同态／闭包律"之前，先 grep **`<名字>AlgHom`／`<名字>AlgEquiv`／
`<名字>RingHom` 的打包件**（L47②）——打包件存在则 `map_*` 免费；再 grep 精确名字。
**代价**：五条白写（约 40 分钟），零返工损失（闸门自动回滚，工作区干净）。

**射程（勿夸大）**：`UDK' ≤ M_n(K')^N`（`prop:14.19` 第一半）**未证**；
`Z(UDK') ⊆ Z` **未证**（关键路径见 `wiki/proj-abgv52-h2-endgame-corrected.md` §7.6）；
`K'^N ⊆ Frac(κ(C))` **未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprUDKCenter

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

theorem algebraMap_mem_center_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(sprCenterImageField F r n D k₀ hk₀)) (β : Matrix (Fin n) (Fin n) (SprField F r n)) :
    algebraMap ↥(sprCenterImageField F r n D k₀ hk₀) (Matrix (Fin n) (Fin n) (SprField F r n)) z
        * β
      = β * algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
          (Matrix (Fin n) (Fin n) (SprField F r n)) z := by
  classical
  have h1 : algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n)) z
      = Matrix.scalar (Fin n) (algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
          (SprField F r n) z) := Matrix.algebraMap_eq_diagonal z
  rw [h1]
  exact sprScalar_mul_comm F r n _ β

#print axioms algebraMap_mem_center_UDK'
/-! ## §37 ★★★★★★★ **`prop:14.19` 第一半**：`UD(F,n,r) ⊆ M_n(K')^N`

源文 `raw/Saltman1999ch14.tex`（`prop:14.19` 之前，`:414` 逐字）：

> "By Lemma 14.22 we may identify `R(F,n,r)` with the subalgebra of `M_n(S')` generated by
> `X` and `Y_2,…,Y_r`. In consequence, we may consider `UD(F,n,r)` a subalgebra of `M_n(K')`."

本节把这句话的**包含方向**机检：`UDK' ≤ M_n(K')^N`。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprMatNFixedAlg` | **`M_n(K')^N` 作为 `↥Z`-子代数**（载体 = `sprMatNFixed`） |
| ★★★★★★★ `UDK'_le_sprMatNFixedAlg` | **`UDK' ≤ M_n(K')^N`**（`prop:14.19` **第一半**） |
| ★★★★ `mem_sprMatNFixed_of_mem_UDK'` | 逐点形态 |

**工艺（R260，两条实测）**：
* `sprMatNFixed` 的 `add`／`mul` 闭包**不要**用 `rw [map_add]`——`sprPsiDK` 是普通函数应用，
  `map_add` 的模式 `?f (?x + ?y)` 匹配不上。**正解**：先 `change (sprPsiDKAlgHom …) (a+b) = a+b`
  把目标换成 `AlgHom` 形态，再 `rw [map_add]`；而要把逐点假设 `ha.1 t : sprPsiDK … a = a`
  用上去，须 **`have h1 : (sprPsiDKAlgHom …) a = a := ha.1 t`**（两侧 defeq、`show` 不认，
  **R252 同族第 9 次**）。
* `algebraMap_mem'` 走 `Matrix.algebraMap_eq_diagonal` ＋ `sprMatNFixed_scalar_iff`（`GenericInv` §177）
  ＋ `sprCenterImageField_fixed`（`H2Final` §29）——三件**都已机检**，本节零新建数学。

**射程（勿夸大）**：**第二半** `M_n(K')^N ⊆ UDK'` **未证**（＝ `prop:14.19` 第二半，
其关键路径见 `wiki/proj-abgv52-h2-endgame-corrected.md` §7.6：需 `dim_Z UD = n²` 的 `K'` 版输入）；
`K'^N ⊆ Frac(κ(C))` **未证**；`ZEqNFixed` **未证**；**H2 见文件头「当前状态」。** -/

section SprMatNFixedAlg

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

noncomputable def sprMatNFixedAlg [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Subalgebra ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n)) where
  carrier := {α | sprMatNFixed F r n α}
  zero_mem' := ⟨fun b => by rw [sprPsiDK_zero], fun σ => by rw [sprPsiSK_zero]⟩
  one_mem' := ⟨fun b => by rw [sprPsiDK_one], fun σ => by rw [sprPsiSK_one]⟩
  add_mem' := fun {a b} ha hb => by
    refine ⟨fun t => ?_, fun σ => ?_⟩
    · change (sprPsiDKAlgHom F r n t) (a + b) = a + b
      have h1 : (sprPsiDKAlgHom F r n t) a = a := ha.1 t
      have h2 : (sprPsiDKAlgHom F r n t) b = b := hb.1 t
      rw [map_add, h1, h2]
    · change (sprPsiSKAlgHom F r n σ) (a + b) = a + b
      have h1 : (sprPsiSKAlgHom F r n σ) a = a := ha.2 σ
      have h2 : (sprPsiSKAlgHom F r n σ) b = b := hb.2 σ
      rw [map_add, h1, h2]
  mul_mem' := fun {a b} ha hb => by
    refine ⟨fun t => ?_, fun σ => ?_⟩
    · change (sprPsiDKAlgHom F r n t) (a * b) = a * b
      have h1 : (sprPsiDKAlgHom F r n t) a = a := ha.1 t
      have h2 : (sprPsiDKAlgHom F r n t) b = b := hb.1 t
      rw [map_mul, h1, h2]
    · change (sprPsiSKAlgHom F r n σ) (a * b) = a * b
      have h1 : (sprPsiSKAlgHom F r n σ) a = a := ha.2 σ
      have h2 : (sprPsiSKAlgHom F r n σ) b = b := hb.2 σ
      rw [map_mul, h1, h2]
  algebraMap_mem' := fun z => by
    rw [Matrix.algebraMap_eq_diagonal]
    exact (sprMatNFixed_scalar_iff F r n _).mpr
      (sprCenterImageField_fixed F r n D k₀ hk₀ _ z.2)

#print axioms sprMatNFixedAlg

/-- ★★★★★★★ **`prop:14.19` 的第一半**（源文 `:415` 之后）：`UD(F,n,r) ⊆ M_n(K')^N`。

`UDK'` 由 `ψ(X_k)` 的 `K'`-像生成，而 `sprPsiDK_fixes_psi`／`sprPsiSK_fixes_psi`
（`H2Final` §28）表明每个生成元都被 `N = T ⋊ S_n` 固定；`N`-固定元构成 `↥Z`-子代数
（`sprMatNFixedAlg`）⟹ `algebra.adjoin_le`。 -/
theorem UDK'_le_sprMatNFixedAlg [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    UDK' F r n D k₀ hk₀ ≤ sprMatNFixedAlg F r n D k₀ hk₀ := by
  refine Algebra.adjoin_le ?_
  rintro x ⟨k, rfl⟩
  exact ⟨fun b => sprPsiDK_fixes_psi F r n k₀ hk₀ b
      ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩,
    fun σ => sprPsiSK_fixes_psi F r n k₀ hk₀ σ
      ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩⟩

#print axioms UDK'_le_sprMatNFixedAlg

/-- `UDK'` 的每个元素都是 `N`-固定矩阵（`prop:14.19` 第一半的逐点形态）。 -/
theorem mem_sprMatNFixed_of_mem_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : α ∈ UDK' F r n D k₀ hk₀) :
    sprMatNFixed F r n α :=
  UDK'_le_sprMatNFixedAlg F r n D k₀ hk₀ hα

#print axioms mem_sprMatNFixed_of_mem_UDK'

/-! ## §38 ★★★★★ `K'` 世界的 `Ξ` ＋ **对角元互异／Vandermonde 可逆**（`prop:14.19` 第二半的入口）

源文 `prop:14.19` 第二半的**等化子判据**需要 `M_n(K') = UD ⊗_Z K'`，即 `Ξ = {X_{k₁}^i X_{k₂}^j}`
的 `ψ`-像在 `M_n(K')` 上构成 `K'`-基（**PI 输入**，`(A)` 层的对应物是 `XiBasisHyp`／`lem:14.7`）。
本节把该输入在 `K'` 世界**具名化**，并机检它**唯一可能便宜的那一半**：对角元互异 ⟹
Vandermonde 可逆（`lem:14.21` 的实质内容在 `K'` 世界的形态）。

| 件 | 内容 |
|---|---|
| ★★★★ `sprDiagVal` | `K'` 里的对角变量 `x_ii`（＝`ψ(X_{k₀})` 的第 `i` 个对角元） |
| ★★★★ `xdiag_diag_eq_sprDiagVal` | `algebraMap (xdiag i i) = sprDiagVal i` |
| ★★★★★ `sprDiagVal_injective` | **对角元互异**（`x_ii ≠ x_jj`，`i ≠ j`）—— `lem:14.21` 的前提 |
| ★★★★★ `sprDiagVandermonde_det_ne_zero` | **Vandermonde 行列式非零**（`Matrix.det_vandermonde_ne_zero_iff`） |
| ★★★★★ `xiSprK` | **`K'` 世界的 `Ξ`**：`ψ(X_{k₁})^i · ψ(X_{k₂})^j` |
| ★★★★ `xiSprK_mem_UDK'` | `Ξ` 的每个元在 `UDK'` 里 |
| ★★★★★★★ `XiSpanHypK'`／`XiBasisHypK'` | **具名 PI 输入**（张成型／基型），与 `(A)` 层 `XiSpanHyp`／`XiBasisHyp` 逐字同构 |
| ★★★ `xiSpanHypK'_of_xiBasisHypK'` | 基性 ⟹ 张成性（同 `(A)` 层 `xiSpanHyp_of_xiBasisHyp`） |

**为何 `K'` 版可能更便宜**：`ψ(X_{k₀}) = xdiag` 是**互异对角元**的对角矩阵，故
`{xdiag^i · Y^j}` 的独立性可化为 **Vandermonde 独立性**（`(A)` 层的 `lem:14.7` 没有这个便利，
它面对的是抽象通用矩阵）。本节的 `sprDiagVandermonde_det_ne_zero` 就是这条路上的第一块。

**工艺（R261）**：`Basis` 在本 pin 里叫 **`Module.Basis`**（`#check @Basis` 报 unknown；
`(A)` 层 `XiBasisHyp` 的 `Basis` 只是**打印缩写**）；且须**显式 `import
Mathlib.LinearAlgebra.Vandermonde`**（`Procesi.GenericInv` 的传递导入不含它）。

**射程（勿夸大）**：`XiBasisHypK'`／`XiSpanHypK'` **未证**（本节的 `Ξ` 独立性只到对角层，
**不含** `Y` 的 Kronecker 步）；`K'^N ⊆ Frac(κ(C))` **未证**；`ZEqNFixed` **未证**；
**H2 见文件头「当前状态」。** -/

section SprXiK

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)

/-- `S'` 的对角变量 `x_ii`（即 `X_1` 的第 `i` 个对角元）在 `K'` 里的像。 -/
noncomputable def sprDiagVal (i : Fin n) : SprField F r n :=
  algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))

#print axioms sprDiagVal

/-- `xdiag` 的对角元就是 `sprDiagVal`。 -/
theorem xdiag_diag_eq_sprDiagVal (i : Fin n) :
    algebraMap (Spr F r n) (SprField F r n) (xdiag F r n i i) = sprDiagVal F r n i := by
  simp [xdiag_apply, sprDiagVal]

#print axioms xdiag_diag_eq_sprDiagVal

/-- ★★★★ **对角元互异**（`lem:14.21` 的前提：`X_1` 可对角化且特征值互异）。 -/
theorem sprDiagVal_injective : Function.Injective (sprDiagVal F r n) := by
  intro i j h
  have h' : (MvPolynomial.X (Sum.inl i) : Spr F r n) = MvPolynomial.X (Sum.inl j) :=
    IsFractionRing.injective (Spr F r n) (SprField F r n) h
  have h'' : Sum.inl i = (Sum.inl j : SprIdx r n) := MvPolynomial.X_injective h'
  exact Sum.inl.inj h''

#print axioms sprDiagVal_injective

/-- ★★★★ **对角 Vandermonde 可逆**（`det ≠ 0`）：`n` 个互异对角元给出的 Vandermonde 行列式非零。 -/
theorem sprDiagVandermonde_det_ne_zero :
    (Matrix.vandermonde (sprDiagVal F r n)).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact sprDiagVal_injective F r n

#print axioms sprDiagVandermonde_det_ne_zero

/-- `K'` 世界的 `Ξ`：`ψ(X_{k₁})^i · ψ(X_{k₂})^j`（`K'`-系数矩阵）。

这是 `(A)` 层 `Xi F r n k₁ k₂ i j = X_{k₁}^i · X_{k₂}^j`（`GenericInv`）的**逐字 `ψ`-像**。 -/
noncomputable def xiSprK [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) (i j : ℕ) : Matrix (Fin n) (Fin n) (SprField F r n) :=
  ((psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k₁, genericMatrix_mem F r n k₁⟩).map
      (algebraMap (Spr F r n) (SprField F r n))) ^ i
    * ((psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k₂, genericMatrix_mem F r n k₂⟩).map
      (algebraMap (Spr F r n) (SprField F r n))) ^ j

#print axioms xiSprK

/-- ★★★★★ `Ξ` 的 `K'`-像落在 `UDK'` 里（`UDK'` 就是它们生成的 `Z`-子代数）。 -/
theorem xiSprK_mem_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) (i j : ℕ) : xiSprK F r n k₀ hk₀ k₁ k₂ i j ∈ UDK' F r n D k₀ hk₀ := by
  refine mul_mem (pow_mem ?_ i) (pow_mem ?_ j) <;>
    exact psiSpr_mem_UDK' F r n D k₀ hk₀ _

#print axioms xiSprK_mem_UDK'

/-- ★★★★★★★ **`Ξ` 的 `K'`-张成性**（`prop:14.19` 第二半所需的 PI 输入，**具名**）。 -/
def XiSpanHypK' [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0) (k₁ k₂ : Fin r) : Prop :=
  Submodule.span (SprField F r n)
    (Set.range (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)) = ⊤

#print axioms XiSpanHypK'

/-- ★★★★★★★ **`Ξ` 的 `K'`-基性**（比张成更强：`K'`-线性无关 ＋ 张成）。 -/
def XiBasisHypK' [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0) (k₁ k₂ : Fin r) : Prop :=
  ∃ b : Module.Basis (Fin n × Fin n) (SprField F r n) (Matrix (Fin n) (Fin n) (SprField F r n)),
    ∀ p : Fin n × Fin n, b p = xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2

#print axioms XiBasisHypK'

/-- **基性 ⟹ 张成性**（与 `(A)` 层 `xiSpanHyp_of_xiBasisHyp` 逐字同构）。 -/
theorem xiSpanHypK'_of_xiBasisHypK' [Nonempty (Fin n)] {k₀ : Fin r} {hk₀ : k₀.val = 0}
    {k₁ k₂ : Fin r} (h : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    XiSpanHypK' F r n k₀ hk₀ k₁ k₂ := by
  obtain ⟨b, hb⟩ := h
  unfold XiSpanHypK'
  have hrange : Set.range (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)
      = Set.range b := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, hb p⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, (hb p).symm⟩
  rw [hrange]
  exact b.span_eq

#print axioms xiSpanHypK'_of_xiBasisHypK'

/-! ## §39 ★★★★★ **对角幂族 `{xdiag^i : i < n}` 线性无关**（Vandermonde）

`K'` 世界的 `Ξ = {ψ(X_{k₁})^i ψ(X_{k₂})^j}` 的**对角层**：`j = 0` 的那些是 `xdiag^i`。
本节机检它们线性无关——这是 `XiBasisHypK'`（`H2Final` §38 具名）的**第一个可证支路**：
`n` 个互异对角元 ⟹ Vandermonde 可逆 ⟹ 幂族独立。

| 件 | 内容 |
|---|---|
| ★★★★ `sprXdiagK` | `diag(x_ii)` 在 `K'` 里的矩阵（`ψ(X_{k₀})`） |
| ★★★★ `sprXdiagK_eq_map` | 它就是 `xdiag` 沿 `algebraMap` 的像 |
| ★★★★★ `sprXdiagK_linearIndependent` | **`{xdiag^i : i < n}` 线性无关** |

**工艺（R262）**：① 名字冲突——库里**已有** `sprDiagMatK`（带 `b : Fin n → Fˣ` 参数），
新件须避开（本轮改名 `sprXdiagK`）；② `Matrix.diagonal_pow`／`Matrix.eq_zero_of_mulVec_eq_zero`
（后者在 `Mathlib.LinearAlgebra.Matrix.Nondegenerate`，**须显式 import**）；
③ `congrArg (fun M : Matrix … => M k k) hg` **不能**写成 `fun M => fun k => M k k`
（后者类型推断失败：`?m = ?m`）；且 `simp only` 里**必须带上新 `def` 的名字**才能展开它。

**射程（勿夸大）**：只到**对角层**（`j = 0`）。`Ξ` 的**完整**独立性（`j ≥ 1`，含 `Y` 的
Kronecker 步）**未证**——按第 400／401 轮的判读，它等价于 Saltman `lem:14.7` 级别的 PI 内容
（`n = 9` 时需 `y_{kl}` 的多项式线性无关性），**不是**廉价支路；
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprXdiagLinearIndependent

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)


/-- `ψ(X_{k₀})` 在 `K'` 里的对角矩阵形态（`X_1 ↦ diag(x_ii)`）。 -/
noncomputable def sprXdiagK : Matrix (Fin n) (Fin n) (SprField F r n) :=
  Matrix.diagonal (sprDiagVal F r n)

#print axioms sprXdiagK

/-- `sprXdiagK` 就是 `xdiag` 沿 `algebraMap` 的像。 -/
theorem sprXdiagK_eq_map :
    sprXdiagK F r n = (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)) := by
  ext i j
  rw [sprXdiagK, Matrix.diagonal_apply, Matrix.map_apply, xdiag_apply, sprDiagVal]
  by_cases h : i = j <;> simp [h]

#print axioms sprXdiagK_eq_map

/-- ★★★★★ **`{xdiag^i : i < n}` 线性无关**（Vandermonde：`n` 个互异对角元给出 Vandermonde 可逆）。 -/
theorem sprXdiagK_linearIndependent :
    LinearIndependent (SprField F r n) (fun i : Fin n => (sprXdiagK F r n) ^ (i : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : ∀ k : Fin n, ∑ i : Fin n, g i * (sprDiagVal F r n k) ^ (i : ℕ) = 0 := by
    intro k
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) (SprField F r n) => M k k) hg
    simp only [Matrix.sum_apply, Matrix.smul_apply, sprXdiagK, Matrix.diagonal_pow,
      Matrix.diagonal_apply, Matrix.zero_apply] at h
    simpa using h
  have h2 : (Matrix.vandermonde (sprDiagVal F r n)) *ᵥ g = 0 := by
    funext k
    have hk := h1 k
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, mul_comm] using hk
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero (sprDiagVandermonde_det_ne_zero F r n) h2
  intro i
  exact congrFun h3 i

#print axioms sprXdiagK_linearIndependent

/-! ## §40 ★★★★★ `Ξ` 的**线性映射形态**：`xiCoordMap` 与具名 PI 输入的桥

§7.7 第 1–3 步都必须在**线性映射**语言里做（`Basis`／`LinearEquiv`／tensor），故本节把 §38 的
具名输入 `XiSpanHypK'`／`XiBasisHypK'` 与坐标映射 `xiCoordMap` 对接：

```
xiCoordMap (k) = ∑_p k_p • ψ(X_{k₁})^{p.1} ψ(X_{k₂})^{p.2}        (p ∈ Fin n × Fin n)
XiSpanHypK'  ⟺  Surjective (xiCoordMap)                           （张成 ⟺ 满射）
XiBasisHypK' ⟹  LinearIndependent Ξ                                （基性 ⟹ 独立）
```

| 件 | 内容 |
|---|---|
| ★★★★★ `xiCoordMap` | `Ξ`-坐标线性映射 |
| ★★★★ `xiCoordMap_range` | `range = span (range Ξ)` |
| ★★★★★ `xiSpanHypK'_iff_surjective` | **`XiSpanHypK' ⟺ 满射`** |
| ★★★★★ `xiBasisHypK'_linearIndependent` | **`XiBasisHypK' ⟹ Ξ` 线性无关** |

**工艺（R263）**：`LinearMap.range_eq_map` ＋ `Submodule.map_span` 在 `map f ⊤` 上**不匹配**
（`rw` 找不到 `map f (span s)`，因 `⊤` 不是语法上的 `span univ`）⟹ 改用
`le_antisymm`：正向 `Submodule.sum_mem` ＋ `Submodule.subset_span`，反向
`Submodule.span_le.mpr` ＋ `Pi.single p 1` 的坐标向量。

**射程（勿夸大）**：`XiSpanHypK'`／`XiBasisHypK'` **仍未证**（PI 输入）；本节只是把它的
**线性映射形态**备好，供 §7.7 第 2–6 步（标量扩张／`θ_i`／等化子判据）使用；
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprXiCoord

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`Ξ`-坐标映射**：`(k_p) ↦ ∑_p k_p • ψ(X_{k₁})^{p.1} ψ(X_{k₂})^{p.2}`
（`M_n(K')` 的 `K'`-坐标；`XiSpanHypK'`／`XiBasisHypK'` 的线性映射形态）。 -/
noncomputable def xiCoordMap [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) (k₁ k₂ : Fin r) :
    (Fin n × Fin n → SprField F r n) →ₗ[SprField F r n]
      Matrix (Fin n) (Fin n) (SprField F r n) where
  toFun k := ∑ p : Fin n × Fin n, k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2
  map_add' k k' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c k := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

#print axioms xiCoordMap

/-- `xiCoordMap` 的像就是 `Ξ` 的张成。 -/
theorem xiCoordMap_range [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) :
    LinearMap.range (xiCoordMap F r n k₀ hk₀ k₁ k₂)
      = Submodule.span (SprField F r n)
          (Set.range (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨k, rfl⟩
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨p, rfl⟩))
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨p, rfl⟩
    exact ⟨Pi.single p 1, by simp [xiCoordMap]⟩

#print axioms xiCoordMap_range

/-- ★★★★★ **具名输入 ⟺ `xiCoordMap` 满射**（把 §38 的 `XiSpanHypK'` 换成线性映射语言）。 -/
theorem xiSpanHypK'_iff_surjective [Nonempty (Fin n)] {k₀ : Fin r} {hk₀ : k₀.val = 0}
    {k₁ k₂ : Fin r} :
    XiSpanHypK' F r n k₀ hk₀ k₁ k₂
      ↔ Function.Surjective (xiCoordMap F r n k₀ hk₀ k₁ k₂) := by
  rw [XiSpanHypK', ← xiCoordMap_range F r n k₀ hk₀ k₁ k₂, LinearMap.range_eq_top]

#print axioms xiSpanHypK'_iff_surjective

/-- ★★★★★ **具名输入 ⟹ `Ξ` 的 `K'`-线性无关**（基性的一半）。 -/
theorem xiBasisHypK'_linearIndependent [Nonempty (Fin n)] {k₀ : Fin r} {hk₀ : k₀.val = 0}
    {k₁ k₂ : Fin r} (h : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    LinearIndependent (SprField F r n)
      (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2) := by
  obtain ⟨b, hb⟩ := h
  have hfam : (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2) = b :=
    funext (fun p => (hb p).symm)
  rw [hfam]
  exact b.linearIndependent

#print axioms xiBasisHypK'_linearIndependent

/-! ## §41 ★★★★★ **求值映射** `UDK' ⊗_Z K' →ₐ[↥Z] M_n(K')`（§7.7 第 2 步）

源文 `:456` 的 "Consider `M_n(K') = K' ⊗_Z UD(F,n,r)`" 的**可执行形态**：本节把该识别做成一条
`↥Z`-代数同态 `a ⊗ b ↦ a · scalar b`，其**双射性**即 §7.6 判定过的 PI 输入
（`dim_Z UD = n²`），登记为具名命题 `UDKTensorHypK'`。

| 件 | 内容 |
|---|---|
| ★★★★★ `udkTensorToMatrix` | `UDK' ⊗_Z K' →ₐ[↥Z] M_n(K')`，`a ⊗ b ↦ a * scalar b`（`Algebra.TensorProduct.lift` ＋ `Subalgebra.val` ＋ `Matrix.scalarAlgHom` ＋ `Matrix.scalar_comm`） |
| ★★★★ `udkTensorToMatrix_tmul` | 单项计算律 |
| ★★★★★★★ `UDKTensorHypK'` | **具名 PI 输入（张量形态）**：该映射是双射 ⟺ `dim_Z UD = n²` |

**工艺（R264，本轮唯一的卡点）**：`rw [Algebra.TensorProduct.lift_tmul]` 在
`(lift f g h) (a ⊗ₜ b)` 上**报 "Did not find an occurrence"**（而目标显示上形状完全一致）——
实例参数的**语法形态**不同（`Algebra ↥Z (SprField)` 的实例项在 `lift` 与 `⊗ₜ` 两侧由不同路径合成）。
**正解：`erw`**（`erw` 的匹配允许 defeq 展开实例），随后 `simp` 收口。
**同族**：R252／R257／R259／R263——**`rw` 找不到形状相同的模式时先试 `erw`**，不要重写目标。

**射程（勿夸大）**：`UDKTensorHypK'` **未证**；`XiSpanHypK' ⟹ 该映射满射`（下一轮）**未做**；
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprUDKTensor

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **求值映射** `UDK' ⊗_Z K' →ₐ[↥Z] M_n(K')`：`a ⊗ b ↦ a · scalar b`。

这是 §7.7 第 2 步的实体：`UDK' ⊗_Z K' ≅ M_n(K')` 的**双向之一**（双射性即 PI 输入）。 -/
noncomputable def udkTensorToMatrix [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀) ↥(UDK' F r n D k₀ hk₀)
        (SprField F r n)
      →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)] Matrix (Fin n) (Fin n) (SprField F r n) :=
  Algebra.TensorProduct.lift (Subalgebra.val (UDK' F r n D k₀ hk₀))
    (Matrix.scalarAlgHom (Fin n) ↥(sprCenterImageField F r n D k₀ hk₀))
    (fun x y => (Matrix.scalar_comm y (fun r' => mul_comm y r')
      (x : Matrix (Fin n) (Fin n) (SprField F r n))).symm)

#print axioms udkTensorToMatrix

/-- 求值映射在单项上的值：`a ⊗ b ↦ a * scalar b`。 -/
theorem udkTensorToMatrix_tmul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (a : ↥(UDK' F r n D k₀ hk₀)) (b : SprField F r n) :
    udkTensorToMatrix F r n D k₀ hk₀
        (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b)
      = (a : Matrix (Fin n) (Fin n) (SprField F r n)) * Matrix.scalar (Fin n) b := by
  rw [udkTensorToMatrix]
  erw [Algebra.TensorProduct.lift_tmul]
  simp

#print axioms udkTensorToMatrix_tmul

/-- ★★★★★★★ **具名 PI 输入（张量形态）**：`UDK' ⊗_Z K' ≅ M_n(K')`（⟺ `dim_Z UD = n²`）。 -/
def UDKTensorHypK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) : Prop :=
  Function.Bijective (udkTensorToMatrix F r n D k₀ hk₀)

#print axioms UDKTensorHypK'

/-! ## §42 ★★★★★ **具名 PI 输入的两条可用后果**（§7.7 第 2–3 步的桥）

§41 把源文 `:456` 的"识别"做成求值映射 `UDK' ⊗_Z K' → M_n(K')`。本节把它与 §38–§40 的
具名输入接起来——**这一步之后，PI 输入只剩"证明了它就能直接装配"的位置**：

| 件 | 内容 |
|---|---|
| ★★★★ `mul_scalar_eq_smul` | `M * scalar c = c • M`（矩阵乘纯量矩阵＝纯量乘） |
| ★★★★★ `udkTensorToMatrix_surjective_of_xiSpanK'` | **`XiSpanHypK' ⟹ 求值映射满射**（取预像 `Σ_p Ξ_p ⊗ k p`） |
| ★★★★★ `xiCoordMap_injective_of_xiBasisHypK'` | **`XiBasisHypK' ⟹ 坐标映射单射**（基性的另一半） |

**工艺（R265）**：`Matrix.mul_scalar`／`Matrix.smul_eq_mul_scalar` 在本 pin **不存在**
（`#check` 报 unknown）⟹ 自建 `mul_scalar_eq_smul`，证法是
`ext i j; simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
Matrix.smul_apply, mul_comm]`——**注意必须带 `Matrix.diagonal_apply`**（`scalar` 是 `diagonal` 的
特例，只给 `scalar_apply` 时 `simp` 停在 `Σ_j M i j * diagonal (fun _ => c) j j'`）。

**射程（勿夸大）**：两个具名输入 `XiSpanHypK'`／`XiBasisHypK'`（＝§41 的 `UDKTensorHypK'`
的等价物）**仍未证**；`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；
**H2 见文件头「当前状态」。** -/

section SprPiBridges

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)


/-- 矩阵乘纯量矩阵＝纯量乘（供求值映射的单项计算）。 -/
theorem mul_scalar_eq_smul (M : Matrix (Fin n) (Fin n) (SprField F r n)) (c : SprField F r n) :
    M * Matrix.scalar (Fin n) c = c • M := by
  ext i j
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, mul_comm]

#print axioms mul_scalar_eq_smul

/-- ★★★★★ **`XiSpanHypK'` ⟹ 求值映射满射**（§7.7 第 2 步的桥）。 -/
theorem udkTensorToMatrix_surjective_of_xiSpanK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k₁ k₂ : Fin r}
    (h : XiSpanHypK' F r n k₀ hk₀ k₁ k₂) :
    Function.Surjective (udkTensorToMatrix F r n D k₀ hk₀) := by
  classical
  intro M
  rw [xiSpanHypK'_iff_surjective] at h
  obtain ⟨k, hk⟩ := h M
  refine ⟨∑ p : Fin n × Fin n,
    (⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
      xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
      ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p, ?_⟩
  rw [map_sum]
  have hterm : ∀ p : Fin n × Fin n,
      udkTensorToMatrix F r n D k₀ hk₀
        ((⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
            xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p)
      = k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 := by
    intro p
    rw [udkTensorToMatrix_tmul, mul_scalar_eq_smul]
  simp only [hterm]
  rw [← hk]
  rfl

#print axioms udkTensorToMatrix_surjective_of_xiSpanK'

/-- ★★★★★ **`XiBasisHypK'` ⟹ 坐标映射单射**（基性的另一半）。 -/
theorem xiCoordMap_injective_of_xiBasisHypK' [Nonempty (Fin n)] {k₀ : Fin r}
    {hk₀ : k₀.val = 0} {k₁ k₂ : Fin r} (h : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    Function.Injective (xiCoordMap F r n k₀ hk₀ k₁ k₂) := by
  classical
  have hli := xiBasisHypK'_linearIndependent F r n h
  rw [Fintype.linearIndependent_iff] at hli
  intro k k' hkk
  have hzero : xiCoordMap F r n k₀ hk₀ k₁ k₂ (k - k') = 0 := by
    rw [map_sub, hkk, sub_self]
  have hfun : (k - k') = 0 := by
    funext p
    exact hli (fun q => (k - k') q) (by simpa [xiCoordMap] using hzero) p
  exact sub_eq_zero.mp hfun

#print axioms xiCoordMap_injective_of_xiBasisHypK'

/-! ## §43 ★★★★★★★ **`θ_i` 实体**（源文 `:456` 的 `θ_i = η_i ⊗ ι`；§7.7 第 3 步）

源文 `prop:14.19` 证明：

> "Consider `M_n(K') = K' ⊗_Z UD(F,n,r)` and `M_n(S'') = S'' ⊗_Z UD(F,n,r)`.
> Define `θ_i = η_i ⊗ ι` where `ι` is the identity on `UD`."

本节把它机检成**真正的 `↥Z`-代数同态**（条件于 PI 输入 `UDKTensorHypK'`）：

```
M_n(K') --(≃)⁻¹--> UDK' ⊗_Z K' --(id_{UDK'} ⊗ η_i)--> UDK' ⊗_Z S'' --(eval)--> M_n(S'')
```

| 件 | 内容 |
|---|---|
| ★★★★★ `udkTensorEquivK'` | **PI 输入 ⟹ `UDK' ⊗_Z K' ≃ₐ[↥Z] M_n(K')`**（`AlgEquiv.ofBijective`） |
| ★★★★★ `udkTensorToMatrixS''` | **`S''`-版求值映射** `UDK' ⊗_Z S'' →ₐ[↥Z] M_n(S'')` |
| ★★★★★★★ `thetaSpr1`／`thetaSpr2` | **`θ₁, θ₂ : M_n(K') →ₐ[↥Z] M_n(S'')`** |

**工艺（R266，两处实测）**：
① `S''`-版求值映射**不能**直接拿 `Subalgebra.val (UDK')`：`UDK'` 是 `↥Z`-**子代数**，
`val` 落在 `M_n(K')` 而目标是 `M_n(S'')` ⟹ 须先 `AlgHom.mapMatrix
(Algebra.TensorProduct.includeLeft)` 沿 `K' → S''` 换系数，再复合 `Subalgebra.val`。
② `Algebra.TensorProduct.map (AlgHom.id _ _) η` 是 `id ⊗ η` 的现成件（无需手写双线性映射）。

**射程（勿夸大）**：`θ_i` 的存在**条件于** `UDKTensorHypK'`（**未证**，PI 输入）；
"`θ_i` 在 `UDK'` 上相等"（源文 "the `θ_i` are equal on `UD`"）**未证**（下一轮）；
等化子判据、`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprTheta

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **由 PI 输入得到的 `Z`-代数同构** `UDK' ⊗_Z K' ≃ₐ[↥Z] M_n(K')`。 -/
noncomputable def udkTensorEquivK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀) ↥(UDK' F r n D k₀ hk₀)
        (SprField F r n)
      ≃ₐ[↥(sprCenterImageField F r n D k₀ hk₀)] Matrix (Fin n) (Fin n) (SprField F r n) :=
  AlgEquiv.ofBijective (udkTensorToMatrix F r n D k₀ hk₀) h

#print axioms udkTensorEquivK'

/-- ★★★★★ **`S''`-版求值映射** `UDK' ⊗_Z S'' →ₐ[↥Z] M_n(S'')`（`θ_i` 的收口端）。 -/
noncomputable def udkTensorToMatrixS'' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀) ↥(UDK' F r n D k₀ hk₀)
        (sprTensorK F r n D k₀ hk₀)
      →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)]
        Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.TensorProduct.includeLeft
      (R := ↥(sprCenterImageField F r n D k₀ hk₀))
      (A := SprField F r n) (B := SprField F r n))).comp
      (Subalgebra.val (UDK' F r n D k₀ hk₀)))
    (Matrix.scalarAlgHom (Fin n) ↥(sprCenterImageField F r n D k₀ hk₀))
    (fun x y => (Matrix.scalar_comm y (fun r' => mul_comm y r')
      ((AlgHom.mapMatrix (Algebra.TensorProduct.includeLeft
        (R := ↥(sprCenterImageField F r n D k₀ hk₀))
        (A := SprField F r n) (B := SprField F r n)))
        ((Subalgebra.val (UDK' F r n D k₀ hk₀)) x))).symm)

#print axioms udkTensorToMatrixS''

/-- ★★★★★ `θ₁ = id_{UDK'} ⊗ η₁`（源文 `:456` 的 `θ_i = η_i ⊗ ι`；经 `Z`-同构搬运）。

```
M_n(K') --(≃)⁻¹--> UDK' ⊗_Z K' --(id ⊗ η₁)--> UDK' ⊗_Z S'' --(eval)--> M_n(S'')
``` -/
noncomputable def thetaSpr1 [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    Matrix (Fin n) (Fin n) (SprField F r n)
      →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)]
        Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  (udkTensorToMatrixS'' F r n D k₀ hk₀).comp
    ((Algebra.TensorProduct.map (AlgHom.id ↥(sprCenterImageField F r n D k₀ hk₀)
        ↥(UDK' F r n D k₀ hk₀)) (etaSprK1 F r n D k₀ hk₀)).comp
      (udkTensorEquivK' F r n D k₀ hk₀ h).symm.toAlgHom)

#print axioms thetaSpr1

/-- ★★★★★ `θ₂ = id_{UDK'} ⊗ η₂`。 -/
noncomputable def thetaSpr2 [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    Matrix (Fin n) (Fin n) (SprField F r n)
      →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)]
        Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  (udkTensorToMatrixS'' F r n D k₀ hk₀).comp
    ((Algebra.TensorProduct.map (AlgHom.id ↥(sprCenterImageField F r n D k₀ hk₀)
        ↥(UDK' F r n D k₀ hk₀)) (etaSprK2 F r n D k₀ hk₀)).comp
      (udkTensorEquivK' F r n D k₀ hk₀ h).symm.toAlgHom)

#print axioms thetaSpr2

/-! ## §44 ★★★★★★ **`θ₁ = θ₂` 在 `UD` 上**（源文 `:456`；§7.7 第 4 步的前半）

源文 `prop:14.19` 证明：

> "Since the `η_i` are equal on `Z`, the `θ_i` are equal on `UD(F,n,r)`."

§35 已机检 `η₁ = η₂` 在 `Z` 上（`etaSprK1_eq_etaSprK2_on_Z`）；本节把它推到 `θ` 层：

| 件 | 内容 |
|---|---|
| ★★★★ `udkTensorEquivK'_symm_apply` | `(≃)⁻¹ a = a ⊗ 1`（`a ∈ UDK'`） |
| ★★★★ `tensorMap_id_eta_tmul_one_gen` | `(id ⊗ η)(a ⊗ 1) = a ⊗ 1`（`η` 任何 `↥Z`-代数同态） |
| ★★★★★★ `thetaSpr_agree_on_UDK'` | **`θ₁ a = θ₂ a`（`a ∈ UDK'`）** |

**工艺（R267）**：① `⊗ₜ` 的**第二因子类型必须显式**：`(id ⊗ η)` 的像在 `S''` 里，
故 `map_tmul` 之后右端是 `a ⊗ₜ (1 : S'')` 而**不是** `a ⊗ₜ (1 : K')`——写成 `_` 会报
"don't know how to synthesize placeholder"；② `(≃)⁻¹ a = a ⊗ 1` 的证法 = **反解**：
先证 `(≃)(a ⊗ 1) = a`（用 `udkTensorToMatrix_tmul` ＋ 逐项 `simp` 处理 `scalar 1 = 1`；
**`Matrix.scalar_one` 不存在**），再 `rw [← h1, AlgEquiv.symm_apply_apply]`。

**射程（勿夸大）**：全部**条件于** `UDKTensorHypK'`（PI 输入，**未证**）；
等化子判据 `α ∈ UDK' ⟺ θ₁α = θ₂α` 的 `⟹` 方向由本节＋§35 给出，**`⟸` 方向未证**；
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprThetaAgree

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- `(udkTensorEquivK').symm a = a ⊗ 1`（`a ∈ UDK'`）。 -/
theorem udkTensorEquivK'_symm_apply [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) :
    (udkTensorEquivK' F r n D k₀ hk₀ h).symm a
      = a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n) := by
  have h1 : (udkTensorEquivK' F r n D k₀ hk₀ h)
      (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n)) = a := by
    change udkTensorToMatrix F r n D k₀ hk₀
      (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n)) = a
    rw [udkTensorToMatrix_tmul]
    ext i j
    simp [Matrix.mul_apply, Matrix.scalar, Matrix.diagonal]
  rw [← h1, AlgEquiv.symm_apply_apply]

#print axioms udkTensorEquivK'_symm_apply

/-- `(id ⊗ η)(a ⊗ 1) = a ⊗ 1`（`η` 为 `↥Z`-代数同态）。 -/
theorem tensorMap_id_eta_tmul_one_gen [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (η : SprField F r n →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)]
      sprTensorK F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) :
    Algebra.TensorProduct.map (AlgHom.id ↥(sprCenterImageField F r n D k₀ hk₀)
        ↥(UDK' F r n D k₀ hk₀)) η
      (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n))
      = a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : sprTensorK F r n D k₀ hk₀) := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

#print axioms tensorMap_id_eta_tmul_one_gen

/-- ★★★★★★ **源文 `:456`：`θ₁ = θ₂` 在 `UD` 上**。 -/
theorem thetaSpr_agree_on_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) :
    thetaSpr1 F r n D k₀ hk₀ h (a : Matrix (Fin n) (Fin n) (SprField F r n))
      = thetaSpr2 F r n D k₀ hk₀ h (a : Matrix (Fin n) (Fin n) (SprField F r n)) := by
  simp only [thetaSpr1, thetaSpr2, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [udkTensorEquivK'_symm_apply F r n D k₀ hk₀ h,
    tensorMap_id_eta_tmul_one_gen F r n D k₀ hk₀ (etaSprK1 F r n D k₀ hk₀),
    tensorMap_id_eta_tmul_one_gen F r n D k₀ hk₀ (etaSprK2 F r n D k₀ hk₀)]

#print axioms thetaSpr_agree_on_UDK'

/-! ## §44b ★★★★★ **A′ 格**：`θ₁ = θ₂` 在生成元的 `K'`-像上（`lem:14.24` 的 `hX`／`hY`）

源文 `lem:14.24`（`raw/Saltman1999ch14.tex:431–434`）的假设里，`θ₁ θ₂` 须在
`R(F,n,r)`（由 `X`、`Y_k` 生成）上一致。本库的 `lem1424_general`（`GenericInv:11111`）
把这组一致写成两条：`hX : θ₁ (xdiag) = θ₂ (xdiag)` 与 `hY : ∀ k, θ₁ (ymat k) = θ₂ (ymat k)`。

本节给出它们在本库 `(B)` 世界 `thetaSpr1/2`（定义在 `M_n(K')` 上）的对应物，
**全部件均已在库**（无需新数学）：

```
psiSpr_sprGen          (GenericInv:6142)   ψ(X_k) = sprGen k
psiSpr_mem_UDK'        (H2Final:4163 区)   它的 K'-像 ∈ UDK'
thetaSpr_agree_on_UDK' (H2Final:4942)      两 θ 在 UDK' 上一致
```

| 件 | 内容 |
|---|---|
| ★★★★★ `thetaSpr_agree_on_sprGenK'` | 一般形态：`sprGen k` 的 `K'`-像上一致 |
| ★★★★★ `thetaSpr_agree_on_xdiagK'` | `hX` 形态（`sprGen k₀ = xdiag`） |
| ★★★★★ `thetaSpr_agree_on_ymatK'` | `hY` 形态（`sprGen k = ymat k`，`k ≠ k₀`） |

**射程（勿夸大）**：本节只给 `lem1424_general` 的 `hX`／`hY` 两格。`hΔ`（＝已发表输入 `[2.9]`
的 `S''`-世界形态）与 `hα`（`lem:14.25` 的分母搭桥）**均未做**；`ThetaAgreeHypK'` 的装配
**未做**；`UDKTensorHypK'` **未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprGenAgree

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **A′ 格（一般形态）**：`thetaSpr1/2` 在 `ψ(X_k) = sprGen k` 的 `K'`-像上一致。

这是 `lem1424_general` 的 `hX`／`hY` 在 `(B)` 世界的统一形式。 -/
theorem thetaSpr_agree_on_sprGenK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (k : Fin r) :
    thetaSpr1 F r n D k₀ hk₀ h
        ((sprGen F r n k₀ hk₀ k).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h
        ((sprGen F r n k₀ hk₀ k).map (algebraMap (Spr F r n) (SprField F r n))) := by
  have hgen : (psiSpr F r n k₀ hk₀
        ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
          (algebraMap (Spr F r n) (SprField F r n))
      = (sprGen F r n k₀ hk₀ k).map (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [psiSpr_sprGen]
  rw [← hgen]
  exact thetaSpr_agree_on_UDK' F r n D k₀ hk₀ h
    ⟨_, psiSpr_mem_UDK' F r n D k₀ hk₀ k⟩

#print axioms thetaSpr_agree_on_sprGenK'

/-- ★★★★★ **A′ 格（`hX` 形态）**：`thetaSpr1/2` 在 `xdiag` 的 `K'`-像上一致。 -/
theorem thetaSpr_agree_on_xdiagK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    thetaSpr1 F r n D k₀ hk₀ h
        ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h
        ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n))) := by
  rw [← sprGen_k0_eq (F := F) (r := r) (n := n) k₀ hk₀]
  exact thetaSpr_agree_on_sprGenK' F r n D k₀ hk₀ h k₀

#print axioms thetaSpr_agree_on_xdiagK'

/-- ★★★★★ **A′ 格（`hY` 形态）**：`thetaSpr1/2` 在 `ymat k` 的 `K'`-像上一致。 -/
theorem thetaSpr_agree_on_ymatK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (k : {k : Fin r // k.val ≠ 0}) :
    thetaSpr1 F r n D k₀ hk₀ h
        ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h
        ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))) := by
  have hk : (k : Fin r) ≠ k₀ := by
    intro h0
    exact k.2 (by rw [h0]; exact hk₀)
  have hgen : (sprGen F r n k₀ hk₀ (k : Fin r)).map
        (algebraMap (Spr F r n) (SprField F r n))
      = (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [sprGen_ne_eq (F := F) (r := r) (n := n) k₀ hk₀ hk]
  rw [← hgen]
  exact thetaSpr_agree_on_sprGenK' F r n D k₀ hk₀ h (k : Fin r)

#print axioms thetaSpr_agree_on_ymatK'

end SprGenAgree

/-! ## §45 ★★★★★ **坐标桥**：`Ξ`-坐标经求值映射就是 `xiCoordMap`

把 §40 的坐标映射与 §41 的求值映射接起来：`Σ_p m_p ⊗ k_p ↦ Σ_p k_p • m_p = xiCoordMap k`。
这条桥是等化子判据 `⟸` 方向的**入口**（后续把 `θ₁α = θ₂α` 沿 `Ξ` 坐标逐项读下来时要用）。

| 件 | 内容 |
|---|---|
| ★★★★★ `udkTensorToMatrix_coord` | **`eval (Σ_p m_p ⊗ k_p) = xiCoordMap k`** |

**工艺（R268）**：`S''`-版求值映射的单项计算律本轮**未取**——`Matrix.scalar` 在
`M_n(S'')` 上的 `*` 触发 `SMulCommClass ↥Z ?m (SprField)` 的**卡死实例**（`?m` 未被确定，
Lean 明确拒绝合成）。**下一轮的解法方向**：给 `Matrix.scalar (Fin n) (b : sprTensorK …)`
的 `S''` 类型标注写足（`(Matrix.scalar (Fin n) b : Matrix (Fin n) (Fin n) (sprTensorK …))`），
或改用 `Matrix.smul` 口径绕开 `*`。

**射程（勿夸大）**：等化子判据的 `⟸` **未证**；`UDKTensorHypK'`（PI 输入）**未证**；
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprCoordBridge

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)
/-- ★★★★★ **坐标桥**：`Ξ`-坐标经求值映射就是 `xiCoordMap`。 -/
theorem udkTensorToMatrix_coord [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k₁ k₂ : Fin r}
    (k : Fin n × Fin n → SprField F r n) :
    udkTensorToMatrix F r n D k₀ hk₀
        (∑ p : Fin n × Fin n,
          (⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
            xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p)
      = xiCoordMap F r n k₀ hk₀ k₁ k₂ k := by
  rw [map_sum]
  have hterm : ∀ p : Fin n × Fin n,
      udkTensorToMatrix F r n D k₀ hk₀
        ((⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
            xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p)
      = k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 := by
    intro p
    rw [udkTensorToMatrix_tmul, mul_scalar_eq_smul]
  simp only [hterm, xiCoordMap, LinearMap.coe_mk, AddHom.coe_mk]

#print axioms udkTensorToMatrix_coord
/-! ## §46 ★★★★★ **系数扩张 `K' → S''`** 与 `S''`-版求值映射的 `⊗1` 律

第 407 轮的失败点（`SMulCommClass ↥Z ?m (SprField)` 卡死实例）本轮的解法：**把
`AlgHom.mapMatrix includeLeft` 提成具名 `def`**（`matMapKtoS''`）——具名 `def` 的期望类型
把 `B` 钉死，卡死即消失（与 R252／R257 同族的"提成具名常量"解法，**第 3 次生效**）。

| 件 | 内容 |
|---|---|
| ★★★★ `matMapKtoS''` | **系数扩张** `M_n(K') →ₐ[↥Z] M_n(S'')`（逐项 `x ↦ x ⊗ 1`） |
| ★★★★★ `udkTensorToMatrixS''_tmul_one` | **`eval_{S''}(a ⊗ 1) = matMapKtoS'' a`** |

**工艺（R269）**：① 卡死实例的**根因**＝`includeLeft` 出现在**陈述**里时，其 `B` 未被
期望类型钉死（在 `def` 的体里则被钉死）；**正解是把该复合提成具名 `def`**；
② 收尾需 `rfl`：`(includeLeft.mapMatrix.comp (UDK').val) a` 与 `includeLeft.mapMatrix ↑a`
**只是 defeq**（R252 同族）。

**射程（勿夸大）**：一般 `b` 的 `_tmul` 律仍未取（`Matrix.scalar` 在 `M_n(S'')` 上仍卡）；
`θ_i` 的计算律、等化子判据 `⟸`、`UDKTensorHypK'`（PI）、`M_n(K')^N ⊆ UDK'`、
`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprMatMapKtoS

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- 系数扩张 `K' → S''`（逐项作用）。 -/
noncomputable def matMapKtoS'' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)]
      Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  AlgHom.mapMatrix (Algebra.TensorProduct.includeLeft
    (R := ↥(sprCenterImageField F r n D k₀ hk₀))
    (A := SprField F r n) (B := SprField F r n))

#print axioms matMapKtoS''

/-- `S''`-版求值映射在 `a ⊗ 1` 上就是换系数的 `a`。 -/
theorem udkTensorToMatrixS''_tmul_one [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (a : ↥(UDK' F r n D k₀ hk₀)) :
    udkTensorToMatrixS'' F r n D k₀ hk₀
        (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : sprTensorK F r n D k₀ hk₀))
      = matMapKtoS'' F r n D k₀ hk₀ (a : Matrix (Fin n) (Fin n) (SprField F r n)) := by
  rw [udkTensorToMatrixS'']
  erw [Algebra.TensorProduct.lift_tmul]
  simp [matMapKtoS'']
  rfl

#print axioms udkTensorToMatrixS''_tmul_one

/-! ## §47 ★★★★★★★ **`θ_i` 在 `UD` 上就是 `ι` 的系数扩张**（源文 `θ_i = η_i ⊗ ι` 的 `ι`-半）

源文 `:456` 写 `θ_i = η_i ⊗ ι`，其中 `ι` 是 `UD` 上的恒等。本节把这句话机检成**等式**：

```
θ_i (a : M_n(K')) = matMapKtoS'' a        （a ∈ UDK'）
```

即 `θ_i` 在 `UD` 上**逐字不动**，`η_i` 只作用在 `K'`-系数上。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `thetaSpr1_apply_UDK'` | `θ₁ a = matMapKtoS'' a`（`a ∈ UDK'`） |
| ★★★★★★★ `thetaSpr2_apply_UDK'` | `θ₂ a = matMapKtoS'' a` |

**证法（三行，链已全部备好）**：`simp only [thetaSpr1, comp_apply, coe_toAlgHom]` 之后
`rw [udkTensorEquivK'_symm_apply, tensorMap_id_eta_tmul_one_gen, udkTensorToMatrixS''_tmul_one]`
——分别对应"`(≃)⁻¹ a = a ⊗ 1`"、"`(id ⊗ η)(a ⊗ 1) = a ⊗ 1`"、"`eval_{S''}(a ⊗ 1) = a`"。

**意义**：等化子判据 `⟸` 的**最后一块拼图的形式**已经明确——对 `α = Σ_p k_p m_p`，
`θ_i α = Σ_p matMapKtoS'' m_p * (系数项)`；由于 `θ_i m_p = matMapKtoS'' m_p` 已知，
`θ₁α = θ₂α` 的差只剩下 `η₁ k_p` 与 `η₂ k_p` 的差。

**射程（勿夸大）**：`η_i` 在一般系数上的贡献（`θ_i (eval (a ⊗ b))` 对一般 `b`）**未证**
（`Matrix.scalar` 在 `M_n(S'')` 上的卡死实例仍在）；等化子判据 `⟸`、`UDKTensorHypK'`（PI）、
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprThetaOnUD

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **`θ₁` 在 `UDK'` 上的取值 = 系数扩张**（源文 "`θ_i = η_i ⊗ ι`" 的 `ι`-部分）。 -/
theorem thetaSpr1_apply_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) :
    thetaSpr1 F r n D k₀ hk₀ h (a : Matrix (Fin n) (Fin n) (SprField F r n))
      = matMapKtoS'' F r n D k₀ hk₀ (a : Matrix (Fin n) (Fin n) (SprField F r n)) := by
  simp only [thetaSpr1, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [udkTensorEquivK'_symm_apply F r n D k₀ hk₀ h,
    tensorMap_id_eta_tmul_one_gen F r n D k₀ hk₀ (etaSprK1 F r n D k₀ hk₀),
    udkTensorToMatrixS''_tmul_one F r n D k₀ hk₀]

#print axioms thetaSpr1_apply_UDK'

/-- ★★★★★★★ **`θ₂` 在 `UDK'` 上的取值 = 系数扩张**。 -/
theorem thetaSpr2_apply_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) :
    thetaSpr2 F r n D k₀ hk₀ h (a : Matrix (Fin n) (Fin n) (SprField F r n))
      = matMapKtoS'' F r n D k₀ hk₀ (a : Matrix (Fin n) (Fin n) (SprField F r n)) := by
  simp only [thetaSpr2, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [udkTensorEquivK'_symm_apply F r n D k₀ hk₀ h,
    tensorMap_id_eta_tmul_one_gen F r n D k₀ hk₀ (etaSprK2 F r n D k₀ hk₀),
    udkTensorToMatrixS''_tmul_one F r n D k₀ hk₀]

#print axioms thetaSpr2_apply_UDK'

/-! ## §48 ★★★★★★★ **`θ_i = η_i ⊗ ι` 两半合一**（计算律；`prop:14.19` 等化子的核心件）

§47 给了 `ι`-半（`θ_i` 在 `UD` 上不动）；本节给**完整计算律**：

```
θ_i (eval (a ⊗ b)) = matMapKtoS'' a * scalar (η_i b)        （a ∈ UDK', b ∈ K'）
```

即：`θ_i` 把 `UD`-方向**逐字搬运**、把 `K'`-系数**经 `η_i` 送出**——这正是源文 `θ_i = η_i ⊗ ι`。

| 件 | 内容 |
|---|---|
| ★★★★★ `scalarAlgHomS''` | `S''` 上的纯量矩阵代数同态（**具名化**以避开卡死实例） |
| ★★★★★ `udkTensorToMatrixS''_tmul` | **一般单项律** `eval_{S''}(a ⊗ b) = matMap a * scalar b` |
| ★★★★★★★ `thetaSpr1_apply_tmul`／`thetaSpr2_apply_tmul` | **`θ_i (eval (a ⊗ b)) = matMap a * scalar (η_i b)`** |

**工艺（R270＝R269 第 4 次生效）**：`Matrix.scalar` 在 `M_n(S'')` 上的卡死实例
（`SMulCommClass ↥Z ?m (SprField)`）**再次**以"**提成具名 `def`**"解决——
`scalarAlgHomS''` 的期望类型把参数钉死。**这条手法现已四连胜**（R257／R259／R269／R270），
可视为本 projekt 的第一解卡手法。

**射程（勿夸大）**：等化子判据 `⟸`、`UDKTensorHypK'`（PI）、`M_n(K')^N ⊆ UDK'`、
`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」**；
关键剩余仍是 `x ⊗ 1 = 1 ⊗ x ⟹ x ∈ Z`（`char 0` 可分性）。 -/

section SprThetaCompute

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- `S''` 上的纯量矩阵代数同态（具名化，避开 `Matrix.scalar` 在陈述里的卡死实例）。 -/
noncomputable def scalarAlgHomS'' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    sprTensorK F r n D k₀ hk₀
      →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)]
        Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  Matrix.scalarAlgHom (Fin n) ↥(sprCenterImageField F r n D k₀ hk₀)

#print axioms scalarAlgHomS''

/-- ★★★★★ `S''`-版求值映射的一般单项律。 -/
theorem udkTensorToMatrixS''_tmul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (a : ↥(UDK' F r n D k₀ hk₀)) (b : sprTensorK F r n D k₀ hk₀) :
    udkTensorToMatrixS'' F r n D k₀ hk₀
        (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b)
      = matMapKtoS'' F r n D k₀ hk₀ (a : Matrix (Fin n) (Fin n) (SprField F r n))
        * scalarAlgHomS'' F r n D k₀ hk₀ b := by
  rw [udkTensorToMatrixS'']
  erw [Algebra.TensorProduct.lift_tmul]
  rfl

#print axioms udkTensorToMatrixS''_tmul

/-- ★★★★★★★ **`θ₁` 的计算律**（源文 `θ_i = η_i ⊗ ι` 的两半合一）：

`θ₁ (eval (a ⊗ b)) = matMapKtoS'' a * scalar (η₁ b)` —— 即 `θ₁` 在 `UD` 上不动、只把
`K'`-系数经 `η₁` 送出去。 -/
theorem thetaSpr1_apply_tmul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) (b : SprField F r n) :
    thetaSpr1 F r n D k₀ hk₀ h
        (udkTensorToMatrix F r n D k₀ hk₀
          (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b))
      = matMapKtoS'' F r n D k₀ hk₀ (a : Matrix (Fin n) (Fin n) (SprField F r n))
        * scalarAlgHomS'' F r n D k₀ hk₀ (etaSprK1 F r n D k₀ hk₀ b) := by
  simp only [thetaSpr1, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  have hcoe : udkTensorToMatrix F r n D k₀ hk₀
      (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b)
      = (udkTensorEquivK' F r n D k₀ hk₀ h)
        (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b) := rfl
  rw [hcoe, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    udkTensorToMatrixS''_tmul]

#print axioms thetaSpr1_apply_tmul

/-- ★★★★★★★ **`θ₂` 的计算律**（`θ₂ (eval (a ⊗ b)) = matMapKtoS'' a * scalar (η₂ b)`）。 -/
theorem thetaSpr2_apply_tmul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (a : ↥(UDK' F r n D k₀ hk₀)) (b : SprField F r n) :
    thetaSpr2 F r n D k₀ hk₀ h
        (udkTensorToMatrix F r n D k₀ hk₀
          (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b))
      = matMapKtoS'' F r n D k₀ hk₀ (a : Matrix (Fin n) (Fin n) (SprField F r n))
        * scalarAlgHomS'' F r n D k₀ hk₀ (etaSprK2 F r n D k₀ hk₀ b) := by
  simp only [thetaSpr2, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  have hcoe : udkTensorToMatrix F r n D k₀ hk₀
      (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b)
      = (udkTensorEquivK' F r n D k₀ hk₀ h)
        (a ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] b) := rfl
  rw [hcoe, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    udkTensorToMatrixS''_tmul]

#print axioms thetaSpr2_apply_tmul

/-! ## §49 ★★★★★★★ **等化子方程的坐标化**（`θ_i` 在 `Ξ`-坐标上的计算律）

§48 给了 `θ_i` 在**单项** `eval (a ⊗ b)` 上的计算律；本节把它推到 §40 的**坐标组合**
`xiCoordMap k = Σ_p k_p • m_p` 上，得到源文 `:456` 的等化子方程在 `S''` 里的**线性形态**：

```
θ₁ (xiCoordMap k) − θ₂ (xiCoordMap k) = Σ_p matMap(m_p) * scalar((η₁ − η₂)(k_p))
```

| 件 | 内容 |
|---|---|
| ★★★★★★★ `thetaSpr1_apply_coord`／`thetaSpr2_apply_coord` | `θ_i (xiCoordMap k) = Σ_p matMap(m_p) * scalar(η_i(k_p))` |
| ★★★★★★★ `thetaSpr_sub_coord` | **等化子方程的坐标化**（差 = 逐项的 `(η₁−η₂)` 作用） |

**意义**：源文的等化子论证现在只剩**纯线性代数**一步：由 `{matMap(m_p)}` 的**独立性**
（＝ PI 输入 ＋ 系数扩张的忠实平坦性）从 `Σ_p matMap(m_p) * scalar((η₁−η₂)(k_p)) = 0`
读出 `(η₁−η₂)(k_p) = 0`（`∀ p`），再由 §35 的 `η₁ = η₂ ⟺ ∈ Z` 得 `k_p ∈ Z`，
从而 `α = xiCoordMap k ∈ UDK'`。

**射程（勿夸大）**：`{matMap(m_p)}` 的独立性（`S''` 上）**未证**；等化子判据 `⟸`、
`UDKTensorHypK'`（PI）、`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；
**H2 见文件头「当前状态」。** -/

section SprThetaCoord

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **`θ₁` 在 `Ξ`-坐标上的计算律**：
`θ₁ (xiCoordMap k) = Σ_p matMap(m_p) * scalar(η₁(k_p))`。 -/
theorem thetaSpr1_apply_coord [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (k : Fin n × Fin n → SprField F r n) :
    thetaSpr1 F r n D k₀ hk₀ h (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = ∑ p : Fin n × Fin n,
          matMapKtoS'' F r n D k₀ hk₀ (xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)
            * scalarAlgHomS'' F r n D k₀ hk₀
                (etaSprK1 F r n D k₀ hk₀ (k p)) := by
  rw [← udkTensorToMatrix_coord F r n D k₀ hk₀ k, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun p _ =>
    thetaSpr1_apply_tmul F r n D k₀ hk₀ h _ (k p))

#print axioms thetaSpr1_apply_coord

/-- ★★★★★★★ **`θ₂` 在 `Ξ`-坐标上的计算律**。 -/
theorem thetaSpr2_apply_coord [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (k : Fin n × Fin n → SprField F r n) :
    thetaSpr2 F r n D k₀ hk₀ h (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = ∑ p : Fin n × Fin n,
          matMapKtoS'' F r n D k₀ hk₀ (xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)
            * scalarAlgHomS'' F r n D k₀ hk₀
                (etaSprK2 F r n D k₀ hk₀ (k p)) := by
  rw [← udkTensorToMatrix_coord F r n D k₀ hk₀ k, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun p _ =>
    thetaSpr2_apply_tmul F r n D k₀ hk₀ h _ (k p))

#print axioms thetaSpr2_apply_coord

/-- ★★★★★★★ **等化子方程的坐标化**（源文的 `θ₁α = θ₂α` 落到 `S''` 里的**线性方程**）：

`θ₁ (xiCoordMap k) − θ₂ (xiCoordMap k) = Σ_p matMap(m_p) * scalar((η₁−η₂)(k_p))`。 -/
theorem thetaSpr_sub_coord [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (k : Fin n × Fin n → SprField F r n) :
    thetaSpr1 F r n D k₀ hk₀ h (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
        - thetaSpr2 F r n D k₀ hk₀ h (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = ∑ p : Fin n × Fin n,
          matMapKtoS'' F r n D k₀ hk₀ (xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)
            * scalarAlgHomS'' F r n D k₀ hk₀
                (etaSprK1 F r n D k₀ hk₀ (k p) - etaSprK2 F r n D k₀ hk₀ (k p)) := by
  rw [thetaSpr1_apply_coord F r n D k₀ hk₀ h k,
    thetaSpr2_apply_coord F r n D k₀ hk₀ h k, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_sub, mul_sub]

#print axioms thetaSpr_sub_coord

/-! ## §50 ★★★★★ **系数扩张 `K' → S''` 的单射性**（等化子最后一步的第一块）

第 411 轮把等化子方程化成"`Σ_p matMap(m_p)·scalar((η₁−η₂)(k_p)) = 0` ⟹ 各系数为零"。
要读出系数为零，需要**系数扩张保独立性**；本节给它的第一块：`matMap` 是**单射**。

| 件 | 内容 |
|---|---|
| ★★★★ `coeKtoS''` | `K' →ₐ[↥Z] S''`（`x ↦ x ⊗ 1`，**具名**避开卡死实例） |
| ★★★★★ `coeKtoS''_injective` | `includeLeft` 单射（`includeLeft_injective` ＋ 子域包含单射） |
| ★★★★ `matMapKtoS''_apply` | 逐项形态（`rfl`） |
| ★★★★★ `matMapKtoS''_injective` | **`matMap` 单射**（矩阵层） |

**工艺（R271）**：`Algebra.TensorProduct.includeLeft_injective` **要一个前提**
（`Function.Injective (algebraMap R A)`），不是无条件的；此处前提是子域包含单射
`fun x y h => Subtype.ext h`。另：`matMapKtoS''_apply` 是 **`rfl`**（`AlgHom.mapMatrix` 的
`toFun` 就是逐项 `map`）。

**射程（勿夸大）**：`matMap` **保 `K'`-线性无关 ⟹ `S''`-线性无关**（忠实平坦性）**未证**——
这才是等化子 `⟸` 的最后一块；等化子判据 `⟸`、`UDKTensorHypK'`（PI）、`M_n(K')^N ⊆ UDK'`、
`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprCoeKtoS

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- 系数扩张 `K' → S''`（源文 `x ↦ x ⊗ 1`），**具名**以避开卡死实例（R270 手法）。 -/
noncomputable def coeKtoS'' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    SprField F r n →ₐ[↥(sprCenterImageField F r n D k₀ hk₀)] sprTensorK F r n D k₀ hk₀ :=
  Algebra.TensorProduct.includeLeft

#print axioms coeKtoS''

/-- ★★★★★ 系数扩张**单射**。 -/
theorem coeKtoS''_injective [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (coeKtoS'' F r n D k₀ hk₀) :=
  Algebra.TensorProduct.includeLeft_injective (fun x y h => Subtype.ext h)

#print axioms coeKtoS''_injective

/-- `matMapKtoS''` 就是逐项 `coeKtoS''`（定义式，供改写）。 -/
theorem matMapKtoS''_apply [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (M : Matrix (Fin n) (Fin n) (SprField F r n)) (i j : Fin n) :
    (matMapKtoS'' F r n D k₀ hk₀ M) i j = coeKtoS'' F r n D k₀ hk₀ (M i j) := by
  rfl

#print axioms matMapKtoS''_apply

/-- ★★★★★ **系数扩张单射**（矩阵层）。 -/
theorem matMapKtoS''_injective [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (matMapKtoS'' F r n D k₀ hk₀) := by
  intro M N h
  ext i j
  exact coeKtoS''_injective F r n D k₀ hk₀
    (by rw [← matMapKtoS''_apply, ← matMapKtoS''_apply]; exact congrFun (congrFun h i) j)

#print axioms matMapKtoS''_injective

/-! ## §51 ★★★★ **`matMap` 的 `K'`-半线性**（独立性的输入）

等化子最后一步（§49 的 `Σ_p matMap(m_p)·scalar(d_p) = 0 ⟹ d_p = 0`）要靠"`matMap` 保
`K'`-线性关系"。本节给该论证的**逐项输入**：`matMap` 把 `K'`-纯量乘法与乘法结构如实搬运。

| 件 | 内容 |
|---|---|
| ★★★★ `matMapKtoS''_smul` | **`matMap (c • M) = (c ⊗ 1) • matMap M`** |
| ★★★★ `coeKtoS''_mul` | 系数扩张保乘法（`map_mul` 的值层形态） |

**工艺（R272）**：`K'` 上的 `•` 就是乘法，`rw` 链必须**显式带 `smul_eq_mul`**（两处：
`Matrix.smul_apply` 之后各一次），否则 `map_mul` 找不到 `?x * ?y`；另 `Matrix.smul_apply`
必须**先于** `matMapKtoS''_apply`（否则后者在 `•` 之下，`rw` 不匹配）。

**射程（勿夸大）**：由本节到"保 `K'`-线性无关"还差**跨 `S''` 的线性组合**（须用
`S''`-纯量 `s_p` 而非 `c_p ⊗ 1`），即忠实平坦性那一块——**未证**；
等化子判据 `⟸`、`UDKTensorHypK'`（PI）、`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、
`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprMatMapSemilinear

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★ **`matMap` 的 `K'`-半线性**：`matMap (c • M) = (c ⊗ 1) • matMap M`。 -/
theorem matMapKtoS''_smul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : SprField F r n) (M : Matrix (Fin n) (Fin n) (SprField F r n)) :
    matMapKtoS'' F r n D k₀ hk₀ (c • M)
      = coeKtoS'' F r n D k₀ hk₀ c • matMapKtoS'' F r n D k₀ hk₀ M := by
  ext i j
  rw [matMapKtoS''_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
    matMapKtoS''_apply, smul_eq_mul]

#print axioms matMapKtoS''_smul

/-- ★★★★ 系数扩张**保持乘法**（`AlgHom` 的 `map_mul` 的值层形态）。 -/
theorem coeKtoS''_mul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (a b : SprField F r n) :
    coeKtoS'' F r n D k₀ hk₀ (a * b) = coeKtoS'' F r n D k₀ hk₀ a * coeKtoS'' F r n D k₀ hk₀ b :=
  map_mul _ a b

#print axioms coeKtoS''_mul

/-! ## §52 ★★★★★★★ **等化子 `⟸` 的最后一块：具名化**

第 411 轮把等化子方程化成 `Σ_p matMap(m_p)·scalar(d_p) = 0`（`d_p = (η₁−η₂)(k_p)`）。
本节把"由此读出 `d_p = 0`"所需的**唯一剩余事实**具名化——它由 PI 输入（`{m_p}` 是 `K'`-基）
＋ `K' → S''` 的**忠实平坦性**给出：

```
MatMapFaithfulHyp : (Σ_p matMap(m_p) · scalar(d_p) = 0) → ∀ p, d p = 0
```

**为何具名而非继续证**：§7.6／§7.7 已判定 PI 输入（`UDKTensorHypK'`）是本路线的
**唯一外部缺口**；把它的"平坦性推论"也具名，可使**等化子 `⟸` 与后续装配条件化地完成**，
而不再把缺口埋在一句"由忠实平坦性"里（与 `(A)` 层 `XiBasisHyp` 的处理一致）。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `MatMapFaithfulHyp` | **具名：`{matMap(m_p)}` 在 `S''` 上线性无关** |

**射程（勿夸大）**：`MatMapFaithfulHyp` **未证**；等化子判据 `⟸`、`UDKTensorHypK'`（PI）、
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprMatMapFaithful

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **具名：`{matMap(m_p)}` 在 `S''` 上线性无关**（等化子 `⟸` 的最后一块）。

即：`S''`-系数的线性组合 `Σ_p matMap(m_p) · scalar(d_p) = 0` 强迫全部 `d_p = 0`。
数学上它由 PI 输入（`{m_p}` 是 `K'`-基）＋ `K' → S''` 的**忠实平坦性**给出。 -/
def MatMapFaithfulHyp [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) : Prop :=
  ∀ d : (Fin n × Fin n) → sprTensorK F r n D k₀ hk₀,
    (∑ p : Fin n × Fin n,
        matMapKtoS'' F r n D k₀ hk₀ (xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)
          * scalarAlgHomS'' F r n D k₀ hk₀ (d p)) = 0
      → ∀ p, d p = 0

#print axioms MatMapFaithfulHyp

/-! ## §53 ★★★★★★★ **等化子的另一半缺口具名化**：`Z` 是 `(η₁, η₂)` 的等化子

§52 具名了"从 `Σ_p matMap(m_p)·scalar(d_p) = 0` 读出 `d_p = 0`"（`MatMapFaithfulHyp`）。
读出 `d_p = (η₁−η₂)(k_p) = 0` 之后，还须把 `(η₁−η₂)(k_p) = 0` 反推成 `k_p ∈ Z` ——
这正是源文 `:321` 的 "Since `Z` is a field, it is clear that for `x ∈ K`, `x ∈ Z` iff
`η₁(x) = η₂(x)`"，其中 **`⟸` 方向需要 `K'/Z` 的可分性**（`char 0`），本仓**尚未证**。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `EtaEqualizerHyp` | **具名：`Z` 恰是 `(η₁, η₂)` 的等化子**（`⟸` 方向） |

**射程（勿夸大）**：`EtaEqualizerHyp` **未证**；`MatMapFaithfulHyp` **未证**；
`UDKTensorHypK'`（PI）**未证**；等化子判据 `⟸`、`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、
`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。**

**⟹ 至此等化子 `⟸` 的缺口已**全部具名**（两个 Prop）：`MatMapFaithfulHyp`（平坦性）＋
`EtaEqualizerHyp`（可分性）。下一会话可**条件化装配**，无须再判读"还缺什么"。 -/

section SprEtaEqualizer

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **具名：`Z` 恰是 `(η₁, η₂)` 的等化子**（源文 "Since `Z` is a field …"）。

`η₁ x = η₂ x ⟹ x ∈ Z`。数学上须 `K'/Z` 的**可分性**（`char 0`）；本仓尚未证。 -/
def EtaEqualizerHyp [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) : Prop :=
  ∀ x : SprField F r n, etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x →
    x ∈ sprCenterImageField F r n D k₀ hk₀

#print axioms EtaEqualizerHyp

/-! ## §54 ★★★★★★★ **等化子 `⟸` 的系数层结论**（条件于 §52 的具名 Prop）

把 §49 的坐标化方程与 §52 的具名平坦性接起来，得：

```
θ₁ (xiCoordMap k) = θ₂ (xiCoordMap k)  ⟹  ∀ p, η₁(k_p) = η₂(k_p)
```

这是等化子判据 `⟸` 的**系数层**（最后一步 `k_p ∈ Z` 用 §53 的 `EtaEqualizerHyp`，
再接 `xiCoordMap k ∈ UDK'`，本轮**未取**：`k p • m` 与 `algebraMap ⟨k p, _⟩ * m`
的改写卡在 `Matrix.smul_mul` 的一处残项，下一轮补）。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `eta_eq_of_theta_eq` | **`θ₁α = θ₂α ⟹ 逐项 `η₁(k_p) = η₂(k_p)`**（`α = xiCoordMap k`） |

**射程（勿夸大）**：`xiCoordMap k ∈ UDK'` 的收口**未取**；三个具名 Prop
（`UDKTensorHypK'`／`MatMapFaithfulHyp`／`EtaEqualizerHyp`）**均未证**；
`M_n(K')^N ⊆ UDK'`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprEqualizerCoeff

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **等化子 `⟸` 的系数层结论**（条件于两个具名 Prop）：

`θ₁α = θ₂α`（`α = xiCoordMap k`）⟹ 逐项 `η₁(k_p) = η₂(k_p)`。 -/
theorem eta_eq_of_theta_eq [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hF : MatMapFaithfulHyp F r n D k₀ hk₀ k₁ k₂)
    (k : Fin n × Fin n → SprField F r n)
    (hθ : thetaSpr1 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = thetaSpr2 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k))
    (p : Fin n × Fin n) :
    etaSprK1 F r n D k₀ hk₀ (k p) = etaSprK2 F r n D k₀ hk₀ (k p) := by
  have hzero : thetaSpr1 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      - thetaSpr2 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k) = 0 :=
    sub_eq_zero.mpr hθ
  rw [thetaSpr_sub_coord F r n D k₀ hk₀ hPI k] at hzero
  have := hF (fun q => etaSprK1 F r n D k₀ hk₀ (k q) - etaSprK2 F r n D k₀ hk₀ (k q)) hzero p
  exact sub_eq_zero.mp this

#print axioms eta_eq_of_theta_eq
/-! ## §55 ★★★★★★★★ **等化子判据 `⟸` 机检**（`prop:14.19` 第二半的核心；条件于 §52／§53）

源文 `:456`／`:321` 的等化子判据：

> "Since `Z` is a field, it is clear that for `x ∈ K`, `x ∈ Z` iff `η₁(x) = η₂(x)`.
> Since `UD` is a vector space over `Z`, for `α ∈ M_n(K)`, `α ∈ UD` iff `θ₁(α) = θ₂(α)`."

本节把它的 **`⟸` 方向**在 `K'`／`S''` 世界机检（条件于两个具名 Prop）：

```
θ₁ (xiCoordMap k) = θ₂ (xiCoordMap k)   ⟹   xiCoordMap k ∈ UDK'
```

**证明链（四步，四件都已具名或已机检）**：
1. §49 `thetaSpr_sub_coord`：差 = `Σ_p matMap(m_p)·scalar((η₁−η₂)(k_p))`；
2. §52 `MatMapFaithfulHyp`：该和为 0 ⟹ 逐项 `(η₁−η₂)(k_p) = 0`（§54 已收成 `eta_eq_of_theta_eq`）；
3. §53 `EtaEqualizerHyp`：`η₁(k_p) = η₂(k_p) ⟹ k_p ∈ Z`；
4. `k_p ∈ Z` ⟹ `k_p • m_p = algebraMap ⟨k_p,_⟩ * m_p ∈ UDK'`（`Z`-子代数封闭），
   求和即 `xiCoordMap k ∈ UDK'`。

**工艺（R273）**：第 4 步的改写 `k p • m = algebraMap ⟨k p, _⟩ * m` **不要**用
`Matrix.smul_mul`（第 416 轮在此卡住）——直接 `ext i j; simp [Matrix.smul_apply,
Matrix.mul_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, smul_eq_mul]` 一次收口。
另 `Subalgebra.sum_mem` 须**显式给出和式类型**（否则 `Finset` 隐参数无法合成）。

**射程（勿夸大）**：`MatMapFaithfulHyp`／`EtaEqualizerHyp`／`UDKTensorHypK'` **均未证**；
**`⟹` 方向**（`α ∈ UDK' ⟹ θ₁α = θ₂α`）已由 §44／§47 给出；`M_n(K')^N ⊆ UDK'`（须把任意
`N`-不变矩阵写成 `xiCoordMap k`，即 PI 输入的满射形态 §42）、`K'^N ⊆ Frac(κ(C))`、
`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprEqualizerConverse

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★ **等化子判据 `⟸`**（`prop:14.19` 第二半的等化子，条件于 §52／§53 的具名 Prop）。 -/
theorem mem_UDK'_of_theta_eq [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hF : MatMapFaithfulHyp F r n D k₀ hk₀ k₁ k₂)
    (hE : EtaEqualizerHyp F r n D k₀ hk₀)
    (k : Fin n × Fin n → SprField F r n)
    (hθ : thetaSpr1 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = thetaSpr2 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)) :
    xiCoordMap F r n k₀ hk₀ k₁ k₂ k ∈ UDK' F r n D k₀ hk₀ := by
  have hk : ∀ p, k p ∈ sprCenterImageField F r n D k₀ hk₀ :=
    fun p => hE (k p) (eta_eq_of_theta_eq F r n D k₀ hk₀ hPI hF k hθ p)
  have hterm : ∀ p : Fin n × Fin n,
      k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 ∈ UDK' F r n D k₀ hk₀ := by
    intro p
    have hsm : k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2
        = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
            (Matrix (Fin n) (Fin n) (SprField F r n)) ⟨k p, hk p⟩
          * xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 := by
      ext i j
      simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.algebraMap_eq_diagonal,
        Matrix.diagonal_apply, smul_eq_mul]
    rw [hsm]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2)
  have hsum : (∑ p : Fin n × Fin n, k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)
      ∈ UDK' F r n D k₀ hk₀ :=
    Subalgebra.sum_mem (UDK' F r n D k₀ hk₀) (fun p _ => hterm p)
  simpa [xiCoordMap, LinearMap.coe_mk, AddHom.coe_mk] using hsum

#print axioms mem_UDK'_of_theta_eq

/-! ## §56 ★★★★★★★ **最后一个具名缺口**：`M_n(K')^N` 落在 `Ξ`-坐标里

`K'^N ⊆ Frac(κ(C))` 的装配链（§7.7 第 5–6 步）需要一个入口：把**任意** `N`-不变矩阵写成
`Ξ`-坐标组合（`xiCoordMap k`）。它由 PI 输入（`Ξ` 张成，§38／§42）给出，本节把它具名。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `NfixedIsCoordHyp` | **`∀ α, sprMatNFixed α → ∃ k, xiCoordMap k = α`** |

**拼图状态（`prop:14.19` 第二半，全部条件于四个具名 Prop）**：
| 环节 | 位置 | 状态 |
|---|---|---|
| `θ₁α = θ₂α ⟹ α ∈ UDK'`（等化子 `⟸`） | §55 | ✅ 机检（条件于 §52／§53） |
| `α ∈ UDK' ⟹ θ₁α = θ₂α`（等化子 `⟹`） | §44／§47 | ✅ 机检（条件于 §41） |
| `N`-不变 ⟹ 坐标组合 | §56 | **具名**（`NfixedIsCoordHyp`） |
| 等化子 + 坐标 ⟹ `M_n(K')^N ⊆ UDK'` | 待装配 | 缺装配（下一轮，预计 1–2 轮） |
| 中心化 `Z(UDK') ⊆ Z` ⟹ `K'^N ⊆ Frac(κ(C))` | §36（一半） | 缺另一方向 |
| `ZEqNFixed` ⟹ `H2` | §32／§33 | ✅ 早已机检 |

**射程（勿夸大）**：四个具名 Prop **均未证**；装配与中心化**未证**；**H2 见文件头「当前状态」。** -/

section SprNfixedCoord

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **具名：每个 `N`-不变矩阵都是 `Ξ`-坐标组合**（`M_n(K')^N ⊆ UDK'` 的入口）。

由 PI 输入（`Ξ` 张成，§38／§42）给出；数学上即 `prop:14.19` 第二半的**满射形态**。 -/
def NfixedIsCoordHyp [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) : Prop :=
  ∀ α : Matrix (Fin n) (Fin n) (SprField F r n), sprMatNFixed F r n α →
    ∃ k : Fin n × Fin n → SprField F r n, xiCoordMap F r n k₀ hk₀ k₁ k₂ k = α

#print axioms NfixedIsCoordHyp

end SprNfixedCoord


/-! ## §57 ★★★★★★★★ **装配**：`M_n(K')^N ⊆ UDK'`（`prop:14.19` 第二半收口；条件于五个具名 Prop）

把 §55（等化子 `⟸`）与 §56（坐标覆盖）接到一起：任意 `N`-不变矩阵 `α` 先由 §56 写成
`Ξ`-坐标组合 `xiCoordMap k`，再对它取 `lem:14.24` 的 `K'`-世界结论 `θ₁α = θ₂α`，
最后由 §55 收口 `α ∈ UDK'`。

源文 `prop:14.19` 的证明末段（`raw/Saltman1999ch14.tex:454`，逐字）：

> "By Lemma \ref{lem:14.24}, `θ₁(α) = θ₂(α)` and so `α ∈ UD(F,n,r)`."

| 件 | 内容 |
|---|---|
| ★★★★★★★ `ThetaAgreeHypK'` | **具名：`lem:14.24` 的 `K'`-世界结论**（`θ₁ = θ₂` 在 `N`-不变元上） |
| ★★★★★★★ `thetaAgreeHypK'_witness_UDK'` | **在住性见证**：该结论在 `UDK'` 上**已机检成立**（§44），故具名 Prop 不是空类上的断言 |
| ★★★★★★★★ `sprMatNFixed_le_UDK'` | **`M_n(K')^N ⊆ UDK'`**（`prop:14.19` 第二半） |

**为何把 `lem:14.24` 具名而非本轮证明**：`lem1424_general`（`GenericInv` §137）的
**定义域是 `M_n(S')`**，而本节的 `θ_i` 定义在 `M_n(K')` 上；两者之间差 `lem:14.25`
（`N`-不变矩阵的分母清整）。把该步具名后，`prop:14.19` 第二半成为**定理**（条件化），
剩余缺口 = 五个具名 Prop，与 §3 的路线表一一对应（与 `(A)` 层 `XiBasisHyp` 的处理一致）。

**射程（勿夸大）**：五个具名 Prop（`UDKTensorHypK'`／`MatMapFaithfulHyp`／`EtaEqualizerHyp`／
`NfixedIsCoordHyp`／`ThetaAgreeHypK'`）**均未证**；中心化 `Z(UDK') ⊆ Z`、
`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprProp1419Assembly

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **具名：`lem:14.24` 的 `K'`-世界结论**——两条 `↥Z`-代数同态 `θ₁ θ₂` 在
`N`-不变矩阵上一致。

源文 `lem:14.24`（`raw/Saltman1999ch14.tex:431`）的原口径是 `M_n(S') → M_n(S'')`；
`prop:14.19` 的末段（`:454`）把它用在 `M_n(K')` 上的 `θ_i = η_i ⊗ ι`。本库已有的是
**`M_n(S')` 口径**（`GenericInv` §137 的 `lem1424_general`），`M_n(K')` 口径须先过
`lem:14.25`（分母清整），故本件把它具名。 -/
def ThetaAgreeHypK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) : Prop :=
  ∀ α : Matrix (Fin n) (Fin n) (SprField F r n), sprMatNFixed F r n α →
    thetaSpr1 F r n D k₀ hk₀ hPI α = thetaSpr2 F r n D k₀ hk₀ hPI α

#print axioms ThetaAgreeHypK'

/-- ★★★★★★★ **在住性见证**：`ThetaAgreeHypK'` 的结论在 `UDK'` 上**已经机检成立**（§44）。

**为何要这一条**（L1 在住性）：具名 Prop 若只在空类上成立，它就不是"缺口"而是"空洞"。
本件给出它的**非空对照物**：至少在整个 `UDK'` 上结论为真；再结合 §37
`UDK' ≤ M_n(K')^N`，前提类（`N`-不变矩阵）非空、结论类亦非空。 -/
theorem thetaAgreeHypK'_witness_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : α ∈ UDK' F r n D k₀ hk₀) :
    thetaSpr1 F r n D k₀ hk₀ hPI α = thetaSpr2 F r n D k₀ hk₀ hPI α :=
  thetaSpr_agree_on_UDK' F r n D k₀ hk₀ hPI ⟨α, hα⟩

#print axioms thetaAgreeHypK'_witness_UDK'

/-- ★★★★★★★★ **`prop:14.19` 的第二半**：`M_n(K')^N ⊆ UD(F,n,r)`（条件于五个具名 Prop）。

源文 `:454` 的装配：`α` `N`-不变 ⟹（§56）`α = xiCoordMap k` ⟹（`lem:14.24`，具名）
`θ₁α = θ₂α` ⟹（§55 等化子 `⟸`）`α ∈ UDK'`。 -/
theorem sprMatNFixed_le_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hF : MatMapFaithfulHyp F r n D k₀ hk₀ k₁ k₂)
    (hE : EtaEqualizerHyp F r n D k₀ hk₀)
    (hN : NfixedIsCoordHyp F r n D k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F r n D k₀ hk₀ hPI)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : sprMatNFixed F r n α) :
    α ∈ UDK' F r n D k₀ hk₀ := by
  obtain ⟨k, hk⟩ := hN α hα
  have hθ : thetaSpr1 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = thetaSpr2 F r n D k₀ hk₀ hPI (xiCoordMap F r n k₀ hk₀ k₁ k₂ k) := by
    rw [hk]
    exact hA α hα
  exact hk ▸ mem_UDK'_of_theta_eq F r n D k₀ hk₀ hPI hF hE k hθ

#print axioms sprMatNFixed_le_UDK'

end SprProp1419Assembly

/-! ## §58 ★★★★★★★★ **`EtaEqualizerHyp` 是定理**：等化子判据不需要可分性（源文 `:321`）

§53 把 `x ∈ Z ⟸ η₁(x) = η₂(x)` 具名为 `EtaEqualizerHyp`，并判读"须 `K'/Z` 的可分性
（`char 0`）"。**该判读错误**：本节机检它**无条件成立**，且**只**用线性代数——

取 `K'` 作为 `Z`-向量空间的一组基 `b`（`Module.Basis.ofVectorSpace`），则
`K' ⊗_Z K'` 经第一因子成为**自由** `K'`-模，其坐标映射

```
eval : K' ⊗_Z K' → (ι →₀ K')，   a ⊗ v ↦ (i ↦ (b.repr v) i • a)
```

把 `η₁(x) = x ⊗ 1` 送到 `i ↦ (b.repr 1) i • x`，把 `η₂(x) = 1 ⊗ x` 送到
`i ↦ (b.repr x) i • 1`。两式相等，在 `(b.repr 1) i₀ ≠ 0` 的坐标 `i₀` 比较即得

```
x = algebraMap ((b.repr x) i₀) * (algebraMap ((b.repr 1) i₀))⁻¹ ∈ Z,
```

因为两个坐标都在 `Z` 里（`Finsupp` 的值域是 `↥Z`）而 `Z` 是子域。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `mem_sprCenterImageField_of_eta_eq` | **等化子判据**：`η₁x = η₂x ⟹ x ∈ Z`（无条件） |
| ★★★★★★★★ `etaEqualizerHyp_unconditional` | **具名 Prop 变成定理**：`EtaEqualizerHyp` 无条件成立 |
| ★★★★★★★★ `sprMatNFixed_le_UDK'_four` | 装配的**四输入形态**（`hE` 已内建，见 §57） |

**为何不需要可分性**：可分性只在"`K' ⊗_Z K'` 无幂零元"的路线里需要；本节的路线
**只读坐标**，用到的是 `K'` 在 `Z` 上的**基**（任何域扩张都有），与 `char`、可分性、
有限性**均无关**。这与 §7.7 第 4 项的判读相反，已在 `wiki/log.md` 与终局分解 §7.8 登记更正。

**工艺（R274，本轮唯一的卡点）**：`Algebra.TensorProduct.equivFinsuppOfBasis_apply`
的**展开体**里 `TensorProduct.finsuppScalarRight` 的 `DecidableEq` 实例是与
`open scoped Classical in` 绑定的，而陈述里的坐标类型 `↥(Module.Basis.ofVectorSpaceIndex …)`
自带 `Subtype.instDecidableEq` ⟹ `rw` 报 "synthesized type class instance is not
definitionally equal"。**正解**：不用该复合件，直接把 `b.repr.baseChange` 与
`finsuppScalarRight` 写在**本节自己的上下文**里（实例一致），再用
`LinearEquiv.baseChange_tmul` ＋ `finsuppScalarRight_apply_tmul_apply`。
另：`etaSprK1 x` 与 `x ⊗ₜ 1` **defeq**（`includeLeft` 的定义），故 `hx` 可直接当作
张量等式的证明项用（`have hx' : x ⊗ₜ 1 = 1 ⊗ₜ x := hx` 一次通过）。

**射程（勿夸大）**：本节的淘汰**只**去掉 `EtaEqualizerHyp`。其余四个具名 Prop
（`UDKTensorHypK'`／`MatMapFaithfulHyp`／`NfixedIsCoordHyp`／`ThetaAgreeHypK'`）**均未证**；
中心化 `Z(UDK') ⊆ Z`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprEtaEqualizerProof

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★ **等化子判据**（源文 `:321` "for `x ∈ K`, `x ∈ Z` iff `η₁(x) = η₂(x)`"，
`⟸` 方向，**无条件**）。

证明：取 `K'` 的 `Z`-基 `b`，把张量按第一因子写成坐标 `ι →₀ K'`；比较 `1` 的非零坐标处
的两个分量，即得 `x` 是 `Z` 中两个元的商。**不须可分性、不须 `char 0`、不须有限性。** -/
theorem mem_sprCenterImageField_of_eta_eq [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {x : SprField F r n}
    (hx : etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x) :
    x ∈ sprCenterImageField F r n D k₀ hk₀ := by
  classical
  set Z := sprCenterImageField F r n D k₀ hk₀ with hZ
  set b : Module.Basis (Module.Basis.ofVectorSpaceIndex ↥Z (SprField F r n)) ↥Z
      (SprField F r n) := Module.Basis.ofVectorSpace ↥Z (SprField F r n) with hb
  have key : ∀ (a v : SprField F r n) (i : Module.Basis.ofVectorSpaceIndex ↥Z (SprField F r n)),
      (TensorProduct.finsuppScalarRight ↥Z (SprField F r n) (SprField F r n) _
        ((b.repr.baseChange ↥Z (SprField F r n) _ _) (a ⊗ₜ[↥Z] v))) i
        = (b.repr v) i • a := by
    intro a v i
    rw [LinearEquiv.baseChange_tmul]
    exact TensorProduct.finsuppScalarRight_apply_tmul_apply a (b.repr v) i
  have hx' : (x ⊗ₜ[↥Z] (1 : SprField F r n)) = ((1 : SprField F r n) ⊗ₜ[↥Z] x) := hx
  have hcomp : ∀ i : Module.Basis.ofVectorSpaceIndex ↥Z (SprField F r n),
      algebraMap ↥Z (SprField F r n) ((b.repr (1 : SprField F r n)) i) * x
        = algebraMap ↥Z (SprField F r n) ((b.repr x) i) := by
    intro i
    have h := congrArg (fun t : SprField F r n ⊗[↥Z] SprField F r n =>
      (TensorProduct.finsuppScalarRight ↥Z (SprField F r n) (SprField F r n) _
        ((b.repr.baseChange ↥Z (SprField F r n) _ _) t)) i) hx'
    rw [key x 1, key 1 x, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h
  have h1ne : b.repr (1 : SprField F r n) ≠ 0 := by
    intro hz
    have h3 := congrArg b.repr.symm hz
    rw [map_zero, LinearEquiv.symm_apply_apply] at h3
    exact one_ne_zero h3
  obtain ⟨i₀, hi₀⟩ : ∃ i, (b.repr (1 : SprField F r n)) i ≠ 0 := by
    by_contra h
    exact h1ne (Finsupp.ext (fun i => by
      by_contra hi
      exact h ⟨i, hi⟩))
  have hkey := hcomp i₀
  have hc : algebraMap ↥Z (SprField F r n) ((b.repr (1 : SprField F r n)) i₀) ≠ 0 := by
    intro h
    exact hi₀ (by simpa using h)
  have hxval : x = algebraMap ↥Z (SprField F r n) ((b.repr x) i₀)
      * (algebraMap ↥Z (SprField F r n) ((b.repr (1 : SprField F r n)) i₀))⁻¹ := by
    rw [← hkey, mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hd : algebraMap ↥Z (SprField F r n) ((b.repr x) i₀) ∈ Z :=
    ((b.repr x) i₀).2
  have hc' : algebraMap ↥Z (SprField F r n) ((b.repr (1 : SprField F r n)) i₀) ∈ Z :=
    ((b.repr (1 : SprField F r n)) i₀).2
  rw [hxval]
  exact mul_mem hd (inv_mem hc')

#print axioms mem_sprCenterImageField_of_eta_eq

/-- ★★★★★★★★ **`EtaEqualizerHyp` 是定理**（§53 的具名 Prop 被淘汰）。

§53 的判读是"须 `K'/Z` 可分性"；本件证明它**无条件成立**（见
`mem_sprCenterImageField_of_eta_eq`）。 -/
theorem etaEqualizerHyp_unconditional [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    EtaEqualizerHyp F r n D k₀ hk₀ :=
  fun _x hx => mem_sprCenterImageField_of_eta_eq F r n D k₀ hk₀ hx

#print axioms etaEqualizerHyp_unconditional

/-- ★★★★★★★★ **`prop:14.19` 第二半的**四输入**形态**（等化子输入已由 §58 内建）。

与 §57 的 `sprMatNFixed_le_UDK'` 相同，只是 `hE : EtaEqualizerHyp` 由
`etaEqualizerHyp_unconditional` 供给 ⟹ 具名 Prop 从五个减为**四个**。 -/
theorem sprMatNFixed_le_UDK'_four [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hF : MatMapFaithfulHyp F r n D k₀ hk₀ k₁ k₂)
    (hN : NfixedIsCoordHyp F r n D k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F r n D k₀ hk₀ hPI)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : sprMatNFixed F r n α) :
    α ∈ UDK' F r n D k₀ hk₀ :=
  sprMatNFixed_le_UDK' F r n D k₀ hk₀ hPI hF
    (etaEqualizerHyp_unconditional F r n D k₀ hk₀) hN hA hα

#print axioms sprMatNFixed_le_UDK'_four

end SprEtaEqualizerProof

/-! ## §59 ★★★★★★★★ **`MatMapFaithfulHyp` 是定理**（输入 = PI 的基性 `XiBasisHypK'`）＋ 三输入装配

§52 把"从 `Σ_p matMap(m_p)·scalar(d_p) = 0` 读出 `d_p = 0`"具名为 `MatMapFaithfulHyp`，
并判读为"`K' → S''` 的**忠实平坦性**"。本节机检它只是**线性代数**：

1. 取源文 `prop:14.19` 的 PI 输入 `XiBasisHypK'`（`{xiSprK p}` 是 `M_n(K')` 的 `K'`-基，具名 `b`）；
2. 取对偶基泛函 `φ = b.dualBasis p₀`（`φ (b p) = if p = p₀ then 1 else 0`）；
3. 由"矩阵泛函的条目公式" `φ m = Σ_{ij} φ(e_ij)·m i j`（`Matrix.matrix_eq_sum_single`
   ＋ `map_sum`／`map_smul`）把 `φ` 提升成加性映射
   `Φ A = Σ_{ij} coeKtoS''(φ e_ij) · A i j`；
4. `Φ (matMap m · scalar d) = φ(m) · d`（条目 `(matMap m · scalar d) i j = coeKtoS'' (m i j) · d`，
   因 `scalar` 是对角）；
5. 对假设用 `map_sum` 即得 `d p₀ = 0`。

**顺带**：`NfixedIsCoordHyp`（§56）也不需要独立证明——它是 `XiBasisHypK'` 的**满射推论**
（`XiSpanHypK' ⟺ Surjective xiCoordMap`，§40），`N`-不变性根本用不上。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `matMapFaithfulHyp_of_xiBasisHypK'` | **`MatMapFaithfulHyp` 由 PI 输入导出** |
| ★★★★★★★ `nfixedIsCoordHyp_of_xiBasisHypK'` | **`NfixedIsCoordHyp` 由 PI 输入导出**（满射） |
| ★★★★★★★★ `sprMatNFixed_le_UDK'_three` | **`M_n(K')^N ⊆ UDK'` 的三输入形态** |

**射程（勿夸大）**：三个具名 Prop（`UDKTensorHypK'`／`XiBasisHypK'`／`ThetaAgreeHypK'`）**均未证**；
中心化 `Z(UDK') ⊆ Z`、`K'^N ⊆ Frac(κ(C))`、`ZEqNFixed` **均未证**；**H2 见文件头「当前状态」。** -/

section SprMatMapFaithfulProof

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★ **`MatMapFaithfulHyp` 由 PI 输入导出**（源文 `prop:14.19` 的 PI 输入 ＋ 线性代数）。

证明见本节头：对偶基泛函 ＋ 条目公式 ＋ `scalar` 的对角性。 -/
theorem matMapFaithfulHyp_of_xiBasisHypK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k₁ k₂ : Fin r} (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    MatMapFaithfulHyp F r n D k₀ hk₀ k₁ k₂ := by
  classical
  obtain ⟨b, hb⟩ := hB
  intro d hd p₀
  have hd' : ∑ p : Fin n × Fin n,
      matMapKtoS'' F r n D k₀ hk₀ (b p) * scalarAlgHomS'' F r n D k₀ hk₀ (d p) = 0 := by
    rw [← hd]
    exact Finset.sum_congr rfl (fun p _ => by rw [hb p])
  set c : Fin n → Fin n → SprField F r n :=
    fun i j => b.dualBasis p₀ (Matrix.single i j (1 : SprField F r n)) with hc
  have hformula : ∀ m : Matrix (Fin n) (Fin n) (SprField F r n),
      b.dualBasis p₀ m = ∑ i, ∑ j, c i j * m i j := by
    intro m
    conv_lhs => rw [Matrix.matrix_eq_sum_single m]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsingle : Matrix.single i j (m i j) = (m i j) • Matrix.single i j (1 : SprField F r n) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, map_smul, smul_eq_mul, mul_comm]
  have hentry : ∀ (m : Matrix (Fin n) (Fin n) (SprField F r n))
      (e : sprTensorK F r n D k₀ hk₀) (i j : Fin n),
      (matMapKtoS'' F r n D k₀ hk₀ m * scalarAlgHomS'' F r n D k₀ hk₀ e) i j
        = coeKtoS'' F r n D k₀ hk₀ (m i j) * e := by
    intro m e i j
    rw [Matrix.mul_apply]
    have hdiag : ∀ k : Fin n, (scalarAlgHomS'' F r n D k₀ hk₀ e) k j = if k = j then e else 0 := by
      intro k
      simp [scalarAlgHomS'', Matrix.scalar_apply, Matrix.diagonal_apply]
    simp only [hdiag]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, matMapKtoS''_apply]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  let Phi : Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) →+
      (sprTensorK F r n D k₀ hk₀) :=
    { toFun := fun A => ∑ i, ∑ j, coeKtoS'' F r n D k₀ hk₀ (c i j) * A i j
      map_zero' := by simp
      map_add' := by
        intro A B
        simp [mul_add, Finset.sum_add_distrib] }
  have hPhi : ∀ (m : Matrix (Fin n) (Fin n) (SprField F r n))
      (e : sprTensorK F r n D k₀ hk₀),
      Phi (matMapKtoS'' F r n D k₀ hk₀ m * scalarAlgHomS'' F r n D k₀ hk₀ e)
        = coeKtoS'' F r n D k₀ hk₀ (b.dualBasis p₀ m) * e := by
    intro m e
    have hstep : Phi (matMapKtoS'' F r n D k₀ hk₀ m * scalarAlgHomS'' F r n D k₀ hk₀ e)
        = (∑ i, ∑ j, coeKtoS'' F r n D k₀ hk₀ (c i j)
            * coeKtoS'' F r n D k₀ hk₀ (m i j)) * e := by
      show (∑ i, ∑ j, coeKtoS'' F r n D k₀ hk₀ (c i j)
          * (matMapKtoS'' F r n D k₀ hk₀ m
            * scalarAlgHomS'' F r n D k₀ hk₀ e) i j)
        = (∑ i, ∑ j, coeKtoS'' F r n D k₀ hk₀ (c i j)
            * coeKtoS'' F r n D k₀ hk₀ (m i j)) * e
      simp only [hentry, Finset.sum_mul, mul_assoc]
    rw [hstep]
    congr 1
    rw [hformula m]
    simp only [map_sum, map_mul]
  have hzero : ∑ p : Fin n × Fin n,
      coeKtoS'' F r n D k₀ hk₀ (b.dualBasis p₀ (b p)) * d p = 0 := by
    have h1 : Phi (∑ p : Fin n × Fin n,
        matMapKtoS'' F r n D k₀ hk₀ (b p) * scalarAlgHomS'' F r n D k₀ hk₀ (d p)) = 0 := by
      rw [hd']
      exact map_zero Phi
    rw [map_sum] at h1
    simpa only [hPhi] using h1
  have hdelta : ∀ p : Fin n × Fin n,
      coeKtoS'' F r n D k₀ hk₀ (b.dualBasis p₀ (b p)) = if p = p₀ then 1 else 0 := by
    intro p
    rw [Module.Basis.dualBasis_apply_self]
    split
    · rw [map_one]
    · rw [map_zero]
  have hfinal : (∑ p : Fin n × Fin n,
      coeKtoS'' F r n D k₀ hk₀ (b.dualBasis p₀ (b p)) * d p) = d p₀ := by
    rw [Finset.sum_eq_single p₀]
    · rw [hdelta p₀]
      simp
    · intro p _ hp
      rw [hdelta p]
      simp [hp]
    · intro h
      exact absurd (Finset.mem_univ p₀) h
  rw [hfinal] at hzero
  exact hzero

#print axioms matMapFaithfulHyp_of_xiBasisHypK'

/-- ★★★★★★★ **`NfixedIsCoordHyp` 由 PI 输入导出**（它是张成性的满射推论，§40；
`N`-不变性用不上）。 -/
theorem nfixedIsCoordHyp_of_xiBasisHypK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k₁ k₂ : Fin r} (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    NfixedIsCoordHyp F r n D k₀ hk₀ k₁ k₂ := by
  intro α _
  have hspan : XiSpanHypK' F r n k₀ hk₀ k₁ k₂ := xiSpanHypK'_of_xiBasisHypK' (F := F) (r := r) (n := n) hB
  exact (xiSpanHypK'_iff_surjective (F := F) (r := r) (n := n) (k₀ := k₀) (hk₀ := hk₀)
    (k₁ := k₁) (k₂ := k₂)).mp hspan α

#print axioms nfixedIsCoordHyp_of_xiBasisHypK'

/-- ★★★★★★★★ **`prop:14.19` 第二半的**三输入**形态**：`M_n(K')^N ⊆ UDK'`，
条件于 `UDKTensorHypK'`（PI 的张量形态）、`XiBasisHypK'`（PI 的基形态）、`ThetaAgreeHypK'`。 -/
theorem sprMatNFixed_le_UDK'_three [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F r n D k₀ hk₀ hPI)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : sprMatNFixed F r n α) :
    α ∈ UDK' F r n D k₀ hk₀ :=
  sprMatNFixed_le_UDK'_four F r n D k₀ hk₀ hPI
    (matMapFaithfulHyp_of_xiBasisHypK' F r n D k₀ hk₀ hB)
    (nfixedIsCoordHyp_of_xiBasisHypK' F r n D k₀ hk₀ hB) hA hα

#print axioms sprMatNFixed_le_UDK'_three

end SprMatMapFaithfulProof

/-! ## §60 ★★★★★★★★ **中心化 `Z(UDK') = Z`** ＋ **`K'^N` 的 `Z`-半入口**（`prop:14.19` 后半的收口）

源文 `prop:14.19` 的证明把"取中心"作为 `Z = K'^N` 的手段（`(A)` 层同型，源文 `:321`／`:456`）。
本节把**中心计算**机检掉，并把 `Z`-半的入口接上：

```
center(UDK') = Z   （条件于 PI 输入 UDKTensorHypK'）
x ∈ K'^N  ⟹  scalar x ∈ M_n(K')^N ⊆ UDK'  ⟹  scalar x 中心  ⟹  x ∈ Z
```

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `center_UDK'_eq` | **`x` 在 `UDK'` 里中心 ⟺ `x` 是 `Z` 的纯量** |
| ★★★★★★★ `mem_sprCenterImageField_of_scalar_mem` | `scalar x ∈ UDK' ⟹ x ∈ Z` |
| ★★★★★★★ `mem_sprCenterImageField_of_nfixed` | **`x ∈ K'^N ⟹ x ∈ Z`**（三输入：PI ＋ `XiBasisHypK'` ＋ `ThetaAgreeHypK'`） |

**证明（`center_UDK'_eq` 的 `⟹`）**：
1. `x ⊗ 1` 在 `UDK' ⊗_Z K'` 里中心（`Algebra.TensorProduct.tmul_mul_tmul` ＋ `TensorProduct.inductionOn`，
   只用 `x` 在 `UDK'` 里中心）；
2. 沿**代数**同构 `udkTensorEquivK' hPI` 搬运 ⟹ `x` 在 `M_n(K')` 里中心；
3. `Matrix.center_eq_range`：中心 = 纯量矩阵 ⟹ `x = scalar c`；
4. `x ∈ UDK'` ⟹（§44）`θ₁x = θ₂x`；而 `θ_i (scalar c) = scalar (η_i c)`
   （`scalar c = eval (1 ⊗ c)`，§48 的 `thetaSpr1_apply_tmul`）⟹ `η₁ c = η₂ c` ⟹（§58）`c ∈ Z`。

**射程（勿夸大）**：`center_UDK'_eq` **条件于** `UDKTensorHypK'`；`mem_sprCenterImageField_of_nfixed`
条件于三个具名 Prop（`UDKTensorHypK'`／`XiBasisHypK'`／`ThetaAgreeHypK'`），三者**均未证**；
`ZEqNFixed`／**H2** 仍未证。 -/

section SprUDKCenterEq

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★ **中心化 `Z(UDK') = Z`**（源文 `prop:14.19` 的"取中心"步；条件于 PI 输入）。

`x` 在 `UDK'` 里中心 ⟺ `x` 是 `Z` 的纯量（`algebraMap` 的像）。 -/
theorem center_UDK'_eq [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) (x : ↥(UDK' F r n D k₀ hk₀)) :
    (∀ y : ↥(UDK' F r n D k₀ hk₀), x * y = y * x) ↔
      ∃ z : ↥(sprCenterImageField F r n D k₀ hk₀),
        x = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
          ↥(UDK' F r n D k₀ hk₀) z := by
  constructor
  · intro hx
    have hcentral : ∀ t : TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀)
        ↥(UDK' F r n D k₀ hk₀) (SprField F r n),
        (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n)) * t
          = t * (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul b c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, hx b]
      | add u v hu hv =>
        rw [mul_add, add_mul, hu, hv]
    have hcent : ∀ M : Matrix (Fin n) (Fin n) (SprField F r n),
        (x : Matrix (Fin n) (Fin n) (SprField F r n)) * M
          = M * (x : Matrix (Fin n) (Fin n) (SprField F r n)) := by
      intro M
      have hxT : udkTensorEquivK' F r n D k₀ hk₀ hPI
          (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n))
          = (x : Matrix (Fin n) (Fin n) (SprField F r n)) := by
        show udkTensorToMatrix F r n D k₀ hk₀
          (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n)) = _
        rw [udkTensorToMatrix_tmul, Matrix.scalar_apply, Matrix.diagonal_one, Matrix.mul_one]
      calc (x : Matrix (Fin n) (Fin n) (SprField F r n)) * M
          = udkTensorEquivK' F r n D k₀ hk₀ hPI
              (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n))
            * udkTensorEquivK' F r n D k₀ hk₀ hPI
              ((udkTensorEquivK' F r n D k₀ hk₀ hPI).symm M) := by
            rw [hxT, AlgEquiv.apply_symm_apply]
        _ = udkTensorEquivK' F r n D k₀ hk₀ hPI
              ((x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n))
                * (udkTensorEquivK' F r n D k₀ hk₀ hPI).symm M) := by
            rw [map_mul]
        _ = udkTensorEquivK' F r n D k₀ hk₀ hPI
              ((udkTensorEquivK' F r n D k₀ hk₀ hPI).symm M
                * (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n))) := by
            rw [hcentral]
        _ = udkTensorEquivK' F r n D k₀ hk₀ hPI
              ((udkTensorEquivK' F r n D k₀ hk₀ hPI).symm M)
            * udkTensorEquivK' F r n D k₀ hk₀ hPI
              (x ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (1 : SprField F r n)) := by
            rw [map_mul]
        _ = M * (x : Matrix (Fin n) (Fin n) (SprField F r n)) := by
            rw [AlgEquiv.apply_symm_apply, hxT]
    have hmem : (x : Matrix (Fin n) (Fin n) (SprField F r n))
        ∈ Set.center (Matrix (Fin n) (Fin n) (SprField F r n)) :=
      Semigroup.mem_center_iff.mpr (fun M => (hcent M).symm)
    rw [Matrix.center_eq_range] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 : thetaSpr1 F r n D k₀ hk₀ hPI (Matrix.scalar (Fin n) c)
        = Matrix.scalar (Fin n) (etaSprK1 F r n D k₀ hk₀ c) := by
      have h0 : Matrix.scalar (Fin n) c
          = udkTensorToMatrix F r n D k₀ hk₀
              ((1 : ↥(UDK' F r n D k₀ hk₀))
                ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] c) := by
        rw [udkTensorToMatrix_tmul]
        simp
      rw [h0, thetaSpr1_apply_tmul]
      simp [scalarAlgHomS'', Matrix.scalar_apply]
    have h2 : thetaSpr2 F r n D k₀ hk₀ hPI (Matrix.scalar (Fin n) c)
        = Matrix.scalar (Fin n) (etaSprK2 F r n D k₀ hk₀ c) := by
      have h0 : Matrix.scalar (Fin n) c
          = udkTensorToMatrix F r n D k₀ hk₀
              ((1 : ↥(UDK' F r n D k₀ hk₀))
                ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] c) := by
        rw [udkTensorToMatrix_tmul]
        simp
      rw [h0, thetaSpr2_apply_tmul]
      simp [scalarAlgHomS'', Matrix.scalar_apply]
    have hθ : thetaSpr1 F r n D k₀ hk₀ hPI (Matrix.scalar (Fin n) c)
        = thetaSpr2 F r n D k₀ hk₀ hPI (Matrix.scalar (Fin n) c) := by
      rw [hc]
      exact thetaSpr_agree_on_UDK' F r n D k₀ hk₀ hPI x
    rw [h1, h2] at hθ
    have heta : etaSprK1 F r n D k₀ hk₀ c = etaSprK2 F r n D k₀ hk₀ c := by
      have hh := congrFun (congrFun hθ (Classical.arbitrary (Fin n))) (Classical.arbitrary (Fin n))
      simpa [Matrix.scalar_apply] using hh
    have hcZ : c ∈ sprCenterImageField F r n D k₀ hk₀ :=
      mem_sprCenterImageField_of_eta_eq F r n D k₀ hk₀ heta
    refine ⟨⟨c, hcZ⟩, Subtype.ext ?_⟩
    show (x : Matrix (Fin n) (Fin n) (SprField F r n))
      = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
          (Matrix (Fin n) (Fin n) (SprField F r n)) (⟨c, hcZ⟩ : ↥(sprCenterImageField F r n D k₀ hk₀))
    rw [← hc, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  · rintro ⟨z, rfl⟩ y
    apply Subtype.ext
    exact algebraMap_mem_center_UDK' F r n D k₀ hk₀ z
      (y : Matrix (Fin n) (Fin n) (SprField F r n))



#print axioms center_UDK'_eq

/-- ★★★★★★★ **`Z`-半的入口**：`scalar x ∈ UDK'` ⟹ `x ∈ Z`。

`scalar x` 与一切矩阵交换（`sprScalar_mul_comm`）⟹ 它在 `UDK'` 里中心 ⟹ 由 `center_UDK'_eq`
它是 `algebraMap z`；比较对角元即得 `x = ↑z ∈ Z`。 -/
theorem mem_sprCenterImageField_of_scalar_mem [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {x : SprField F r n}
    (hx : Matrix.scalar (Fin n) x ∈ UDK' F r n D k₀ hk₀) :
    x ∈ sprCenterImageField F r n D k₀ hk₀ := by
  have hcentral : ∀ y : ↥(UDK' F r n D k₀ hk₀),
      (⟨Matrix.scalar (Fin n) x, hx⟩ : ↥(UDK' F r n D k₀ hk₀)) * y
        = y * ⟨Matrix.scalar (Fin n) x, hx⟩ := by
    intro y
    apply Subtype.ext
    exact sprScalar_mul_comm F r n x (y : Matrix (Fin n) (Fin n) (SprField F r n))
  obtain ⟨z, hz⟩ := (center_UDK'_eq F r n D k₀ hk₀ hPI
    ⟨Matrix.scalar (Fin n) x, hx⟩).mp hcentral
  have hzeq : x = (z : SprField F r n) := by
    have hmat : Matrix.scalar (Fin n) x
        = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
            (Matrix (Fin n) (Fin n) (SprField F r n)) z := by
      simpa using congrArg (fun a : ↥(UDK' F r n D k₀ hk₀) =>
        (a : Matrix (Fin n) (Fin n) (SprField F r n))) hz
    rw [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply] at hmat
    have h2 := congrFun (congrFun hmat (Classical.arbitrary (Fin n)))
      (Classical.arbitrary (Fin n))
    simpa [Matrix.diagonal_apply] using h2
  rw [hzeq]
  exact z.2



#print axioms mem_sprCenterImageField_of_scalar_mem

/-- ★★★★★★★ **`x ∈ K'^N ⟹ x ∈ Z`**（`prop:14.19` 后半的收口；条件于三个具名 Prop）。

由 `M_n(K')^N ⊆ UDK'`（§59 的三输入形态）＋ `mem_sprCenterImageField_of_scalar_mem`。 -/
theorem mem_sprCenterImageField_of_nfixed [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F r n D k₀ hk₀ hPI) {x : SprField F r n}
    (hx : sprMatNFixed F r n (Matrix.scalar (Fin n) x)) :
    x ∈ sprCenterImageField F r n D k₀ hk₀ :=
  mem_sprCenterImageField_of_scalar_mem F r n D k₀ hk₀ hPI
    (sprMatNFixed_le_UDK'_three F r n D k₀ hk₀ hPI hB hA hx)

#print axioms mem_sprCenterImageField_of_nfixed

end SprUDKCenterEq

/-! ## §61 ★★★★★★ **判别式在 `S''` 里是非零因子**（`lem:14.24` 的前提之一；`ThetaAgreeHypK'` 路线的第一块）

源文 `lem:14.24` 的前提是"`θ_i(Δ)` 是非零因子"（`raw/Saltman1999ch14.tex:431`）。本节把它在
`K'`-世界机检掉：

1. **`Δ ≠ 0`**（`sprDiscr_ne_zero`）：`Δ = ∏_{i<j}(x_ii − x_jj)` 是**互异变量之差**的积，
   `MvPolynomial.X_injective` ＋ 多项式环是域 ⟹ 每个因子非零 ⟹ 积非零；
2. **任何非零 `d ∈ K'` 的 `d ⊗ 1` 在 `S''` 里是非零因子**（`coeKtoS''_mul_eq_zero`）：
   用 §58 的**自由性**——`S''` 经第一因子是自由 `K'`-模（`b.repr.baseChange` ＋ `finsuppScalarRight`），
   故 `d • (−)` 在 `ι →₀ K'` 上逐分量是"乘以非零元"⟹ 单射；
3. 合起来：`Δ ⊗ 1` 在 `S''` 里非零因子（`coeKtoS''_algebraMap_discr_mul_eq_zero`）。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprDiscr_ne_zero` | **`Δ ≠ 0`**（`S'`-世界） |
| ★★★★★★ `coeKtoS''_mul_eq_zero` | **`0 ≠ d ∈ K'` ⟹ `d ⊗ 1` 非零因子**（`S''`） |
| ★★★★★★ `coeKtoS''_algebraMap_discr_mul_eq_zero` | **`Δ ⊗ 1` 非零因子** |

**射程（勿夸大）**：本节只给 `lem:14.24` 的**判别式前提**。`ThetaAgreeHypK'` **未证**
（还须 `lem:14.25` ＋ `lem1424_general` 的 K'-世界接线）；PI 输入（`XiBasisHypK'`／`UDKTensorHypK'`）
**未证**；`ZEqNFixed`／**H2** 仍未证。 -/

section SprDiscrNonZeroDiv

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **判别式非零**（`Δ = ∏_{i<j}(x_ii − x_jj)` 在 `S'` 里）。 -/
theorem sprDiscr_ne_zero : sprDiscr F (r := r) (n := n) ≠ 0 := by
  rw [sprDiscr, Finset.prod_ne_zero_iff]
  intro p hp
  rw [sprDiscrIdx, Finset.mem_filter] at hp
  have hpp : p.1 ≠ p.2 := ne_of_lt hp.2
  refine sub_ne_zero.mpr ?_
  intro h
  exact hpp (Sum.inl.inj (MvPolynomial.X_injective (R := F) (σ := SprIdx r n) h))

#print axioms sprDiscr_ne_zero

/-- ★★★★★★ **非零 `K'`-元的系数扩张在 `S''` 里是非零因子**（用 `S''` 自由的 `K'`-模结构）。 -/

theorem coeKtoS''_mul_eq_zero [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {d : SprField F r n} (hd : d ≠ 0) {y : sprTensorK F r n D k₀ hk₀}
    (hy : coeKtoS'' F r n D k₀ hk₀ d * y = 0) : y = 0 := by
  classical
  set Z := sprCenterImageField F r n D k₀ hk₀ with hZ
  set b : Module.Basis (Module.Basis.ofVectorSpaceIndex ↥Z (SprField F r n)) ↥Z
      (SprField F r n) := Module.Basis.ofVectorSpace ↥Z (SprField F r n) with hb
  let e : sprTensorK F r n D k₀ hk₀ ≃ₗ[SprField F r n]
      (Module.Basis.ofVectorSpaceIndex ↥Z (SprField F r n) →₀ SprField F r n) :=
    b.repr.baseChange ↥Z (SprField F r n) _ _ ≪≫ₗ
      TensorProduct.finsuppScalarRight ↥Z (SprField F r n) (SprField F r n) _
  have hy' : d • y = 0 := by
    have h : algebraMap (SprField F r n) (sprTensorK F r n D k₀ hk₀) d * y = 0 := hy
    rwa [← Algebra.smul_def] at h
  have h1 : e y = 0 := by
    have h2 : e (d • y) = 0 := by rw [hy', map_zero]
    rw [LinearEquiv.map_smul] at h2
    exact (smul_eq_zero.mp h2).resolve_left hd
  exact e.map_eq_zero_iff.mp h1

#print axioms coeKtoS''_mul_eq_zero

/-- ★★★★★★ **判别式的系数扩张 `Δ ⊗ 1` 在 `S''` 里是非零因子**（`lem:14.24` 的前提之一）。 -/

theorem coeKtoS''_algebraMap_discr_mul_eq_zero [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {y : sprTensorK F r n D k₀ hk₀}
    (hy : coeKtoS'' F r n D k₀ hk₀
      (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F (r := r) (n := n))) * y = 0) :
    y = 0 := by
  refine coeKtoS''_mul_eq_zero F r n D k₀ hk₀ ?_ hy
  exact fun h => sprDiscr_ne_zero F r n
    (IsFractionRing.injective (Spr F r n) (SprField F r n) (by simpa using h))

#print axioms coeKtoS''_algebraMap_discr_mul_eq_zero

end SprDiscrNonZeroDiv

/-! ## §62 ★★★★★ **`θ_i` 的纯量计算律 ＋ `S'`-世界的 `θ₁'` 及其判别式条件**

`lem:14.24`（`GenericInv` §137 的 `lem1424_general`）的**定义域是 `M_n(S')`**，而本工程的 `θ_i`
定义在 `M_n(K')` 上。本节把两者接起来，为 `ThetaAgreeHypK'` 的**真证明**（v21 §3 第 5 项）铺路：

1. **纯量计算律**（`thetaSpr1_apply_scalar`／`thetaSpr2_apply_scalar`）：
   `θ_i (scalar c) = scalar (η_i c)`——因 `scalar c = eval (1 ⊗ c)`（§48 的 `_apply_tmul`）；
2. **`S'`-世界的 `θ₁'`**（`thetaSpr1S`）：`M_n(S') →ₐ[F] M_n(S'')`，
   = `θ₁` 沿 `M_n(S') → M_n(K')`（`AlgHom.mapMatrix (algebraMap)`）的**限制**，
   用 `AlgHom.restrictScalars F` ＋ `AlgHom.mapMatrix`；
3. **`θ₁'(scalar c) = scalar (c ⊗ 1)`**（`thetaSpr1S_apply_scalar`）；
4. **判别式条件**（`sprDiscrNonZeroDiv_thetaSpr1S`）：`θ₁'(Δ)` 是 `S''` 的**非零因子**
   ——`lem:14.24` 的 `hΔ` 前提**已备**（接 §61 的 `coeKtoS''_algebraMap_discr_mul_eq_zero`）。

| 件 | 内容 |
|---|---|
| ★★★★★ `thetaSpr1_apply_scalar`／`thetaSpr2_apply_scalar` | **`θ_i (scalar c) = scalar (η_i c)`** |
| ★★★★★ `thetaSpr1S` | **`θ₁` 的 `S'`-世界限制** `M_n(S') →ₐ[F] M_n(S'')` |
| ★★★★★ `thetaSpr1S_apply_scalar` | `θ₁'(scalar c) = scalar (c ⊗ 1)` |
| ★★★★★★ `sprDiscrNonZeroDiv_thetaSpr1S` | **`lem:14.24` 的 `hΔ`（`θ₁'(Δ)` 非零因子）已备** |

**射程（勿夸大）**：本节只做**接口**与**一个前提**。`ThetaAgreeHypK'` **未证**
（还须 `lem:14.25` ＋ 把 `lem1424_general` 的结论搬回 `M_n(K')`）；PI 输入**未证**；
`ZEqNFixed`／**H2** 仍未证。 -/

section SprThetaSWorld

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`θ₁` 的纯量计算律**：`θ₁ (scalar c) = scalar (η₁ c)`。 -/
theorem thetaSpr1_apply_scalar [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (c : SprField F r n) :
    thetaSpr1 F r n D k₀ hk₀ h (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) (etaSprK1 F r n D k₀ hk₀ c) := by
  have h0 : Matrix.scalar (Fin n) c
      = udkTensorToMatrix F r n D k₀ hk₀
          ((1 : ↥(UDK' F r n D k₀ hk₀))
            ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] c) := by
    rw [udkTensorToMatrix_tmul]
    simp
  rw [h0, thetaSpr1_apply_tmul]
  simp [scalarAlgHomS'', Matrix.scalar_apply]
#print axioms thetaSpr1_apply_scalar

/-- ★★★★★ **`θ₂` 的纯量计算律**：`θ₂ (scalar c) = scalar (η₂ c)`。 -/

theorem thetaSpr2_apply_scalar [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (c : SprField F r n) :
    thetaSpr2 F r n D k₀ hk₀ h (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) (etaSprK2 F r n D k₀ hk₀ c) := by
  have h0 : Matrix.scalar (Fin n) c
      = udkTensorToMatrix F r n D k₀ hk₀
          ((1 : ↥(UDK' F r n D k₀ hk₀))
            ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] c) := by
    rw [udkTensorToMatrix_tmul]
    simp
  rw [h0, thetaSpr2_apply_tmul]
  simp [scalarAlgHomS'', Matrix.scalar_apply]
#print axioms thetaSpr2_apply_scalar

/-- ★★★★★ **`θ₁` 的 `S'`-世界限制** `θ₁' : M_n(S') →ₐ[F] M_n(S'')`（`lem:14.24` 的定义域）。 -/

noncomputable def thetaSpr1S [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F]
      Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  ((thetaSpr1 F r n D k₀ hk₀ h).restrictScalars F).comp
    (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
#print axioms thetaSpr1S

/-- ★★★★★ **`θ₁'` 在纯量矩阵上的值**：`θ₁'(scalar c) = scalar (c ⊗ 1)`。 -/

theorem thetaSpr1S_apply_scalar [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (c : Spr F r n) :
    thetaSpr1S F r n D k₀ hk₀ h (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) (coeKtoS'' F r n D k₀ hk₀
          (algebraMap (Spr F r n) (SprField F r n) c)) := by
  have hmap : (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
      (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n) c) := by
    rw [AlgHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _)]
    rfl
  show thetaSpr1 F r n D k₀ hk₀ h
      ((AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
        (Matrix.scalar (Fin n) c)) = _
  rw [hmap, thetaSpr1_apply_scalar]
  rfl
#print axioms thetaSpr1S_apply_scalar

/-- ★★★★★★ **`lem:14.24` 的判别式前提**：`θ₁'(Δ)` 在 `S''` 里是非零因子。 -/

theorem sprDiscrNonZeroDiv_thetaSpr1S [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    sprDiscrNonZeroDiv F (thetaSpr1S F r n D k₀ hk₀ h)
      (sprDiscr F (r := r) (n := n)) := by
  refine ⟨coeKtoS'' F r n D k₀ hk₀
    (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F (r := r) (n := n))), ?_, ?_⟩
  · rw [thetaSpr1S_apply_scalar]
  · intro y hy
    exact coeKtoS''_algebraMap_discr_mul_eq_zero F r n D k₀ hk₀ hy

#print axioms sprDiscrNonZeroDiv_thetaSpr1S
#print axioms sprDiscrNonZeroDiv_thetaSpr1S

end SprThetaSWorld

/-! ## §63 ★★★★★ **`θ₂` 的 `S'`-世界限制** `θ₂'`（`lem:14.24` 的第二个同态）

§62 给了 `θ₁` 的 `S'`-世界限制 `thetaSpr1S` 及其判别式条件。`lem1424_general` 需要**两个**
同态 `θ₁' θ₂' : M_n(S') →ₐ[F] M_n(S'')`，本节补上 `θ₂'` 及其纯量计算律。

**注意**（R279，本轮实测）：`θ₁` 与 `θ₂` 在纯量上**不重合**——`θ₁'(scalar c) = scalar (c ⊗ 1)`、
`θ₂'(scalar c) = scalar (1 ⊗ c)`。原因是 `η₁ = includeLeft`、`η₂ = includeRight`。
（本节最初把 `θ₂'` 也写成 `c ⊗ 1`，被 `rfl` 挡下；正解是 `1 ⊗ c`。）

| 件 | 内容 |
|---|---|
| ★★★★★ `thetaSpr2S` | **`θ₂` 的 `S'`-世界限制** `M_n(S') →ₐ[F] M_n(S'')` |
| ★★★★★ `thetaSpr2S_apply_scalar` | `θ₂'(scalar c) = scalar (1 ⊗ c)` |

**射程（勿夸大）**：本节只补接口。`ThetaAgreeHypK'` **未证**（还须 `lem:14.25` 的
`N`-不变分母清整，且该路线的**循环风险**见 `wiki/proj-abgv52-h2-endgame-corrected.md` §7.13）；
PI 输入**未证**；`ZEqNFixed`／**H2** 仍未证。 -/

section SprTheta2SWorld

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`θ₂` 的 `S'`-世界限制** `θ₂' : M_n(S') →ₐ[F] M_n(S'')`（`lem:14.24` 的第二个同态）。 -/
noncomputable def thetaSpr2S [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F]
      Matrix (Fin n) (Fin n) (sprTensorK F r n D k₀ hk₀) :=
  ((thetaSpr2 F r n D k₀ hk₀ h).restrictScalars F).comp
    (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
#print axioms thetaSpr2S

/-- ★★★★★ **`θ₂'` 在纯量矩阵上的值**：`θ₂'(scalar c) = scalar (1 ⊗ c)`（与 `θ₁'` **不同**，R279）。 -/

theorem thetaSpr2S_apply_scalar [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (c : Spr F r n) :
    thetaSpr2S F r n D k₀ hk₀ h (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) ((1 : SprField F r n)
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)]
            (algebraMap (Spr F r n) (SprField F r n) c)) := by
  have hmap : (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
      (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n) c) := by
    rw [AlgHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _)]
    rfl
  show thetaSpr2 F r n D k₀ hk₀ h
      ((AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
        (Matrix.scalar (Fin n) c)) = _
  rw [hmap, thetaSpr2_apply_scalar]
  rfl

#print axioms thetaSpr2S_apply_scalar
#print axioms thetaSpr2S_apply_scalar

end SprTheta2SWorld

/-! ## §64 ★★★★★ **`lem:14.24` 的 `hX`／`hY`（两个世界）**：`xdiag`／`ymat` 的像在 `UDK'` 里

源文 `lem:14.24` 的前提"`θ₁` 与 `θ₂` 在 `R(F,n,r)` 上一致"（`:431`）在本工程化为 `xdiag`／`ymat` 上的一致
（与 `(A)` 层 `lem1424_general` 的口径相同）。本节把该前提**两个世界都机检**：

1. **`K'`-世界**：`xdiag`／`ymat` 的系数扩张在 `UDK'` 里（`ψ(X_{k₀}) = xdiag` 由
   `psiSpr_genMat_self`，`ψ(X_k) = ymat k` 由 `psiSpr_genMat`，而 `UDK'` 按定义含 `ψ(X_k)` 的像）
   ⟹ 由 §44（`θ₁ = θ₂` 在 `UDK'` 上）得 `θ₁ = θ₂` 在 `xdiag`／`ymat` 的像上；
2. **`S'`-世界**：`θ₁'`／`θ₂'`（§62／§63）在 `xdiag` 上的一致（逐字由 1 搬运）。

| 件 | 内容 |
|---|---|
| ★★★★★ `map_xdiag_mem_UDK'`／`map_ymat_mem_UDK'` | `xdiag`／`ymat` 的 `K'`-像在 `UDK'` 里 |
| ★★★★★ `thetaSpr_agree_on_xdiag`／`_on_ymat` | **`lem:14.24` 的 `hX`／`hY`（`K'`-世界）** |
| ★★★★★ `thetaSpr1S_agree_xdiag` | **`hX` 的 `S'`-世界形态**（`θ₁'(xdiag) = θ₂'(xdiag)`） |

**射程（勿夸大）**：本节只供应**一致性前提**。`ThetaAgreeHypK'` **未证**；
`lem:14.25` 路线经 §7.14 判为**暂不可走**（须先有 `S'^N ⊆ Z`）；PI 输入**未证**；
`ZEqNFixed`／**H2** 仍未证。 -/

section SprThetaAgreePoints

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ `xdiag` 的 `K'`-像在 `UDK'` 里（`ψ(X_{k₀}) = xdiag`）。 -/
theorem map_xdiag_mem_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)) ∈ UDK' F r n D k₀ hk₀ := by
  rw [← psiSpr_genMat_self F r n k₀ hk₀]
  exact psiSpr_mem_UDK' F r n D k₀ hk₀ k₀
#print axioms map_xdiag_mem_UDK'

/-- ★★★★★ `ymat k` 的 `K'`-像在 `UDK'` 里（`ψ(X_k) = ymat k`，`k ≠ k₀`）。 -/

theorem map_ymat_mem_UDK' [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k : {k : Fin r // k.val ≠ 0}) :
    (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)) ∈ UDK' F r n D k₀ hk₀ := by
  have hk : k.1 ≠ k₀ := by
    intro h
    exact k.2 (by rw [h, hk₀])
  have hps : (psiSpr F r n k₀ hk₀
        ⟨genericMatrix F r n k.1, genericMatrix_mem F r n k.1⟩).map
        (algebraMap (Spr F r n) (SprField F r n))
      = (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [psiSpr_genMat F r n k₀ hk₀ hk]
  rw [← hps]
  exact psiSpr_mem_UDK' F r n D k₀ hk₀ k.1
#print axioms map_ymat_mem_UDK'

/-- ★★★★★ **`lem:14.24` 的 `hX`（`K'`-世界）**：`θ₁ (xdiag 的像) = θ₂ (xdiag 的像)`。 -/

theorem thetaSpr_agree_on_xdiag [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    thetaSpr1 F r n D k₀ hk₀ h ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n))) :=
  thetaSpr_agree_on_UDK' F r n D k₀ hk₀ h ⟨_, map_xdiag_mem_UDK' F r n D k₀ hk₀⟩
#print axioms thetaSpr_agree_on_xdiag

/-- ★★★★★ **`lem:14.24` 的 `hY`（`K'`-世界）**：`θ₁ (ymat k 的像) = θ₂ (ymat k 的像)`。 -/

theorem thetaSpr_agree_on_ymat [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (k : {k : Fin r // k.val ≠ 0}) :
    thetaSpr1 F r n D k₀ hk₀ h ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))) :=
  thetaSpr_agree_on_UDK' F r n D k₀ hk₀ h ⟨_, map_ymat_mem_UDK' F r n D k₀ hk₀ k⟩
#print axioms thetaSpr_agree_on_ymat

/-- ★★★★★ **`hX` 的 `S'`-世界形态**：`θ₁'(xdiag) = θ₂'(xdiag)`。 -/

theorem thetaSpr1S_agree_xdiag [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    thetaSpr1S F r n D k₀ hk₀ h (xdiag F r n) = thetaSpr2S F r n D k₀ hk₀ h (xdiag F r n) := by
  show thetaSpr1 F r n D k₀ hk₀ h ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h ((xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)))
  exact thetaSpr_agree_on_xdiag F r n D k₀ hk₀ h

#print axioms thetaSpr1S_agree_xdiag

end SprThetaAgreePoints

/-! ## §65 ★★★★★★★★★★ **终局：`ZEqNFixed` 与 H2 成为定理**（条件于三个具名 Prop）

§32 已机检 `zEqNFixed_of_surjective : ZEqNFixed ⟸ sprCenterZMap 满射`。本节补上**满射性**，
从而 `ZEqNFixed` 与 **H2** 都以"条件于三个具名 Prop"的形态成为**定理**（无 sorry、无额外公理）。

**证明链（四步）**：
1. **结构性桥**（`sprCenterImageField_le_fieldRange`）：令
   `f := (sprNFixedAlg).val ∘ sprCenterZMap : ↥(ZCanon) →ₐ[F] SprField`，则
   `sprCenterImageField ≤ f.fieldRange`——**生成元被击中**（§32.1 的 `sprCenterZMap_centK`）
   ＋ `IntermediateField.adjoin_le_iff`。**这一步与三个具名 Prop 无关。**
2. **反向包含**（§60 的 `mem_sprCenterImageField_of_nfixed`，条件于三个具名 Prop）：
   `y ∈ K'^N ⟹ y ∈ Frac(κ(C))`；再由 1 得 `y ∈ f.fieldRange`。
3. **满射**（`sprCenterZMap_surjective_of_three`）。
4. **收口**：`zEqNFixed_of_surjective` ⟹ `ZEqNFixed`；`h2_of_ZEqNFixed` ⟹
   `ProcesiS9Hyp F ↥(ZCanon F 2 9 D)`。

**工艺（R280）**：`Algebra ↥(Algebra.adjoin …) ↥(IntermediateField.adjoin …)` 的实例是
**scoped** 的 ⟹ 本节须 `open scoped IntermediateField.algebraAdjoinAdjoin`（否则 `haveI` 的
**陈述本身**就合成失败）；`adjoin` 归纳用 `IntermediateField.adjoin_le_iff.mpr`。

**射程（勿夸大）**：`ZEqNFixed`／H2 **只是条件化定理**——三个具名 Prop
（`UDKTensorHypK'`／`XiBasisHypK'`／`ThetaAgreeHypK'`）**均未证**。**无条件形态仍未达到。** -/

section SprEndgame

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **`sprCenterZMap` 的域值化**：`↥(ZCanon) →ₐ[F] SprField`（复合强制转换）。

★ **结构性桥**（`sprCenterImageField_le_fieldRange`）：`Frac(κ(C)) ≤ (sprCenterZMapToField).fieldRange`
——**不**依赖任何具名 Prop（生成元被 `sprCenterZMap_centK` 击中 ＋ `adjoin_le_iff`）。

★ **满射**（`sprCenterZMap_surjective_of_three`，条件于三个具名 Prop）：由 §60 的反向包含 ＋ 上一条。

★ **`ZEqNFixed`／H2 是定理**（`zEqNFixed_of_three`／`h2_of_three`）：由 `zEqNFixed_of_surjective`
与 `h2_of_ZEqNFixed` 收口。**条件于三个具名 Prop；无 sorry、无额外公理。** -/
noncomputable def sprCenterZMapToField [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ↥(IntermediateField.adjoin F (Set.range D.centK)) →ₐ[F] SprField F r n :=
  (sprNFixedAlg F r n).val.comp (sprCenterZMap F r n D k₀ hk₀)

#print axioms sprCenterZMapToField

theorem sprCenterImageField_le_fieldRange [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    sprCenterImageField F r n D k₀ hk₀
      ≤ (sprCenterZMapToField F r n D k₀ hk₀).fieldRange := by
  haveI : IsScalarTower F ↥(Algebra.adjoin F (Set.range D.centK))
      ↥(IntermediateField.adjoin F (Set.range D.centK)) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x ⟨c, rfl⟩
  refine ⟨algebraMap ↥(Algebra.adjoin F (Set.range D.centK))
      ↥(IntermediateField.adjoin F (Set.range D.centK)) (centKAdjoinEquiv F r n D c), ?_⟩
  show (sprNFixedAlg F r n).val (sprCenterZMap F r n D k₀ hk₀
      (algebraMap ↥(Algebra.adjoin F (Set.range D.centK))
        ↥(IntermediateField.adjoin F (Set.range D.centK)) (centKAdjoinEquiv F r n D c)))
    = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)
  rw [sprCenterZMap_centK]
  rfl

#print axioms sprCenterImageField_le_fieldRange
theorem sprCenterZMap_surjective [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F r n D k₀ hk₀ hPI) :
    Function.Surjective (sprCenterZMap F r n D k₀ hk₀) := by
  intro y
  have hy : (y : SprField F r n) ∈ sprCenterImageField F r n D k₀ hk₀ :=
    mem_sprCenterImageField_of_nfixed F r n D k₀ hk₀ hPI hB hA
      ((sprMatNFixed_scalar_iff F r n (y : SprField F r n)).mpr y.2)
  obtain ⟨z, hz⟩ := sprCenterImageField_le_fieldRange F r n D k₀ hk₀ hy
  exact ⟨z, Subtype.ext hz⟩

#print axioms sprCenterZMap_surjective

theorem zEqNFixed_of_three [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) {k₁ k₂ : Fin 2}
    (hB : XiBasisHypK' F 2 9 k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F 2 9 D k₀ hk₀ hPI) :
    ZEqNFixed F D :=
  zEqNFixed_of_surjective F D hk₀
    (sprCenterZMap_surjective F 2 9 D k₀ hk₀ hPI hB hA)

#print axioms zEqNFixed_of_three
theorem h2_of_three [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) {k₁ k₂ : Fin 2}
    (hB : XiBasisHypK' F 2 9 k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F 2 9 D k₀ hk₀ hPI) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_three F D hk₀ hPI hB hA)

#print axioms h2_of_three

end SprEndgame

/-! ## §66 ★★★★★★★★ **`ThetaAgreeHypK'` ⟺ `M_n(K')^N ⊆ UDK'`**（把 §7.11 的判读**机检**成定理）

第 423 轮的判读是：给定已无条件成立的等化子判据（§55／§58），**`ThetaAgreeHypK'` 不是比
`prop:14.19` 后半更弱的缺口，而是它的同一命题**。本节把该判读**机检**掉：

```
ThetaAgreeHypK'  ⟺  ∀ α, sprMatNFixed α → α ∈ UDK'      （在 PI 输入 UDKTensorHypK' ＋ XiBasisHypK' 下）
```

* **`⟸`**：`α ∈ UDK'` ⟹（§44／§57 的 `thetaAgreeHypK'_witness_UDK'`）`θ₁α = θ₂α`；
* **`⟹`**：§59 的 `sprMatNFixed_le_UDK'_three`（`hF`／`hN` 已由 `XiBasisHypK'` 导出，`hE` 已无条件）。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `thetaAgreeHypK'_iff` | **`ThetaAgreeHypK' ⟺ M_n(K')^N ⊆ UDK'`**（PI 下） |

**意义**：`H2 ⟸ 三个具名 Prop` 中的 `ThetaAgreeHypK'` **不能**再被当作"独立的、较弱的"缺口——
它与 `prop:14.19` 后半**等价**。故 H2 的剩余**实质只有两份数学**：PI 输入、以及 `prop:14.19` 后半的证明。

**射程（勿夸大）**：本件是**等价性**，不是对任一侧的证明。`ThetaAgreeHypK'`、
`M_n(K')^N ⊆ UDK'`、PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprThetaAgreeEquiv

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★ **`ThetaAgreeHypK' ⟺ M_n(K')^N ⊆ UDK'`**（在 PI 输入下）。

`⟸`：`α ∈ UDK'` ⟹ `θ₁α = θ₂α`（§44）；`⟹`：§59 的三输入装配（`hF`／`hN` 由 `XiBasisHypK'` 导出、
`hE` 已无条件）。 -/
theorem thetaAgreeHypK'_iff [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    ThetaAgreeHypK' F r n D k₀ hk₀ hPI ↔
      ∀ α : Matrix (Fin n) (Fin n) (SprField F r n),
        sprMatNFixed F r n α → α ∈ UDK' F r n D k₀ hk₀ := by
  constructor
  · intro hA α hα
    exact sprMatNFixed_le_UDK'_three F r n D k₀ hk₀ hPI hB hA hα
  · intro h α hα
    exact thetaAgreeHypK'_witness_UDK' F r n D k₀ hk₀ hPI (h α hα)

#print axioms thetaAgreeHypK'_iff

end SprThetaAgreeEquiv

/-! ## §67 ★★★★★★★ **`N`-不变矩阵的 `Ξ`-坐标是 `T`-不变的**（坐标分析的**可用一半**）

第 432 轮的死胡同笔记（`wiki/deadend-coord-fixed-route.md`）判明：用"坐标 ＋ `N`-不变性"绕过
`prop:14.19` 后半**不行**——`S_n`-部分只给**等变**（`ψ_σ` 置换 `Ξ` 的指标），故拿不到 `k_p ∈ Z`。
但该分析的 **`T`-部分是对的且有用**，本节把它机检留档：

```
α ∈ M_n(K')^N,  α = xiCoordMap k  ⟹  ∀ b, φ_b (k p) = k p      （即 k p ∈ K'^T）
```

**证明**：`ψ_b(m_p) = m_p`（`m_p ∈ UDK' ⊆ M_n(K')^N`，§37）＋ 半线性 `ψ_b(c • m) = φ_b(c) • ψ_b(m)`
（`sprPsiDK_smul`）＋ `ψ_b α = α` ⟹ `Σ_p (φ_b(k_p) − k_p) • m_p = 0` ⟹（`{m_p}` 是 `K'`-基，
`xiBasisHypK'_linearIndependent`）逐项 `φ_b(k_p) = k_p`。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `sprDiagFieldEquiv_eq_of_coord_fixed` | **`α ∈ M_n(K')^N` 的 `Ξ`-坐标 `T`-不变** |

**为何单列成节**：它是**负结果的正面部分**——日后若试图复活坐标路线（例如先建 `Ξ` 的 `S_n`-轨道分解），
本件可直接复用；同时它把"`T`-部分成立、`S_n`-部分只给等变"的判读**钉成机检件**。

**工艺（R281）**：`sprPsiDK` 是**普通函数**（不是 `AlgHom`）⟹ `map_sum` 对它不适用；
用打包件 `sprPsiDKAlgHom`（其 `toFun` 与 `sprPsiDK` **def-eq**，`show ... from rfl` 可转），
`map_sum` 即可用。另：`congrArg f ((hm q).1 b)` 的**括号不可省**（否则 `b` 被当成 `congrArg` 的第三参数）。

**射程（勿夸大）**：本件**不**推出 `k_p ∈ Z`（须 `S_n`-部分，已判不可行）；`M_n(K')^N ⊆ UDK'`、
`ThetaAgreeHypK'`、PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprCoordTFixed

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **`N`-不变矩阵的 `Ξ`-坐标在 `T` 下不变**（坐标路线的**可用一半**，见死胡同笔记）。 -/
theorem sprDiagFieldEquiv_eq_of_coord_fixed [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : sprMatNFixed F r n α)
    {k : Fin n × Fin n → SprField F r n} (hk : xiCoordMap F r n k₀ hk₀ k₁ k₂ k = α)
    (b : Fin n → Fˣ) (p : Fin n × Fin n) :
    sprDiagFieldEquiv F r n b (k p) = k p := by
  classical
  set m : Fin n × Fin n → Matrix (Fin n) (Fin n) (SprField F r n) :=
    fun q => xiSprK F r n k₀ hk₀ k₁ k₂ q.1 q.2 with hm_def
  have hm : ∀ q, sprMatNFixed F r n (m q) := fun q =>
    mem_sprMatNFixed_of_mem_UDK' F r n D k₀ hk₀
      (xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ q.1 q.2)
  have hind := xiBasisHypK'_linearIndependent F r n (k₀ := k₀) (hk₀ := hk₀)
    (k₁ := k₁) (k₂ := k₂) hB
  have hαsum : α = ∑ q, k q • m q := by
    rw [← hk]
    rfl
  have hstep : sprPsiDK F r n b (∑ q, k q • m q)
      = ∑ q, sprDiagFieldEquiv F r n b (k q) • m q := by
    have hsum := map_sum (sprPsiDKAlgHom F r n b) (fun q => k q • m q) Finset.univ
    rw [show sprPsiDK F r n b (∑ q : Fin n × Fin n, k q • m q)
        = (sprPsiDKAlgHom F r n b) (∑ q : Fin n × Fin n, k q • m q) from rfl, hsum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [show (sprPsiDKAlgHom F r n b) (k q • m q) = sprPsiDK F r n b (k q • m q) from rfl,
      sprPsiDK_smul]
    exact congrArg (fun M => sprDiagFieldEquiv F r n b (k q) • M) ((hm q).1 b)
  have hEq : (∑ q, sprDiagFieldEquiv F r n b (k q) • m q) = ∑ q, k q • m q := by
    have h1 : sprPsiDK F r n b α = α := hα.1 b
    rw [hαsum, hstep] at h1
    exact h1
  have hsplit : (∑ q, (sprDiagFieldEquiv F r n b (k q) - k q) • m q)
      = ∑ q, (sprDiagFieldEquiv F r n b (k q) • m q - k q • m q) :=
    Finset.sum_congr rfl (fun q _ => sub_smul _ _ _)
  have hzero : (∑ q, (sprDiagFieldEquiv F r n b (k q) - k q) • m q) = 0 := by
    rw [hsplit, Finset.sum_sub_distrib, hEq, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hind
    (fun q => sprDiagFieldEquiv F r n b (k q) - k q) hzero p)

#print axioms sprDiagFieldEquiv_eq_of_coord_fixed

end SprCoordTFixed

/-! ## §68 ★★★★★★★★★ **`Z = K'^N` 的等价形态**（`prop:14.19` 的 `Z` 半，条件于三个具名 Prop）

§29 给了 `Z ⊆ K'^N`（`sprCenterImageField_fixed`），§60 给了 `K'^N ⊆ Z`（`mem_sprCenterImageField_of_nfixed`，
条件于三个具名 Prop）。本节把两者并成**一条等价**：

```
x ∈ Frac(κ(C))  ↔  sprFieldNFixed x
```

这是源文 `prop:14.19` 的 **`Z` 半**（`Z(F,n,r) = K'^N`）在 `(B)`-层的**精确形态**，
也是 §65 满射性论证所用的同一个等价（那里内联，这里具名留档）。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `mem_sprCenterImageField_iff_sprFieldNFixed` | **`x ∈ Z ⟺ x ∈ K'^N`** |

**射程（勿夸大）**：本条**条件于三个具名 Prop**（`UDKTensorHypK'`／`XiBasisHypK'`／`ThetaAgreeHypK'`），
三者**均未证**；`ZEqNFixed`／H2 只到条件化定理（§65）；**H2 的无条件形态仍未达到**。 -/

section SprZEqNFixedIff

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★★ **`Z = K'^N`**（`prop:14.19` 的 `Z` 半；条件于三个具名 Prop）。

`⟹` 是 §29 的 `sprCenterImageField_fixed`；`⟸` 是 §60 的 `mem_sprCenterImageField_of_nfixed`
（经 `sprMatNFixed_scalar_iff` 换成纯量形态）。 -/
theorem mem_sprCenterImageField_iff_sprFieldNFixed [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (hA : ThetaAgreeHypK' F r n D k₀ hk₀ hPI) (x : SprField F r n) :
    x ∈ sprCenterImageField F r n D k₀ hk₀ ↔ sprFieldNFixed F r n x :=
  ⟨fun hx => sprCenterImageField_fixed F r n D k₀ hk₀ x hx,
   fun hx => mem_sprCenterImageField_of_nfixed F r n D k₀ hk₀ hPI hB hA
     ((sprMatNFixed_scalar_iff F r n x).mpr hx)⟩

#print axioms mem_sprCenterImageField_iff_sprFieldNFixed

end SprZEqNFixedIff

/-! ## §69 ★★★★★★★★★ **H2 的最简剩余形态**：PI 输入 ＋ `M_n(K')^N ⊆ UDK'` ⟹ `ZEqNFixed`／H2

§65 把 `ZEqNFixed`／H2 条件化到**三个**具名 Prop；§66 又机检了 `ThetaAgreeHypK'` 与
`M_n(K')^N ⊆ UDK'` **等价**。本节把两者合起来，给出**最简的剩余陈述**：

```
UDKTensorHypK' ＋ XiBasisHypK'（PI） ＋ M_n(K')^N ⊆ UDK'
  ⟹ ZEqNFixed F D  ⟹ ProcesiS9Hyp F ↥(ZCanon F 2 9 D)
```

即：**H2 的剩余实质只有两份数学**——PI 输入、以及 `prop:14.19` 后半。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `zEqNFixed_of_mem_UDK` | **`ZEqNFixed` ⟸ PI ＋ `M_n(K')^N ⊆ UDK'`** |
| ★★★★★★★★★ `h2_of_mem_UDK` | **H2 ⟸ 同上** |

**用途**：后续任一轮次只要证出 `M_n(K')^N ⊆ UDK'`（或等价地 `ThetaAgreeHypK'`）与 PI 输入，
即可**直接**用本节的 `h2_of_mem_UDK` 收口，无需再走 §65 的三输入装配。

**射程（勿夸大）**：两条都**条件于** PI 输入与 `M_n(K')^N ⊆ UDK'`，二者**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprEndgameMinimal

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★★ **`ZEqNFixed` 的最简条件形态**：PI（两形态）＋ `M_n(K')^N ⊆ UDK'` 即可。 -/
theorem zEqNFixed_of_mem_UDK [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) {k₁ k₂ : Fin 2}
    (hB : XiBasisHypK' F 2 9 k₀ hk₀ k₁ k₂)
    (hU : ∀ α : Matrix (Fin 9) (Fin 9) (SprField F 2 9),
      sprMatNFixed F 2 9 α → α ∈ UDK' F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_three F D hk₀ hPI hB
    ((thetaAgreeHypK'_iff F 2 9 D k₀ hk₀ hPI hB).mpr hU)
#print axioms zEqNFixed_of_mem_UDK

/-- ★★★★★★★★★ **H2 的最简条件形态**（同上 ＋ `h2_of_ZEqNFixed`）。 -/

theorem h2_of_mem_UDK [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) {k₁ k₂ : Fin 2}
    (hB : XiBasisHypK' F 2 9 k₀ hk₀ k₁ k₂)
    (hU : ∀ α : Matrix (Fin 9) (Fin 9) (SprField F 2 9),
      sprMatNFixed F 2 9 α → α ∈ UDK' F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_mem_UDK F D hk₀ hPI hB hU)

#print axioms h2_of_mem_UDK

end SprEndgameMinimal

/-! ## §70 ★★★★★ **`lem:14.24` 的 `hY` 的 `S'`-世界形态**（`thetaSpr1S_agree_ymat`）

§64 给了 `hX` 的 `S'`-世界形态（`thetaSpr1S_agree_xdiag`）与 `hX`／`hY` 的 `K'`-世界形态
（`thetaSpr_agree_on_xdiag`／`_on_ymat`）。本节补上 **`hY` 的 `S'`-世界形态**：

```
θ₁' (ymat k) = θ₂' (ymat k)        （k ≠ k₀）
```

**⟹ 至此 `lem1424_general`（`GenericInv` §137，已机检）的 `hX`／`hY` 两个前提在
`S'`-世界（它的**定义域世界**）都已就位**：`hX` ＝ §64 的 `thetaSpr1S_agree_xdiag`、
`hY` ＝ 本节的 `thetaSpr1S_agree_ymat`；`hΔ` ＝ §62 的 `sprDiscrNonZeroDiv_thetaSpr1S`。
故 `lem1424_general` 在本工程**可直接调用**（只差对 `θ_i'` 的显式实例化）。

| 件 | 内容 |
|---|---|
| ★★★★★ `thetaSpr1S_agree_ymat` | **`hY` 的 `S'`-世界形态** |

**射程（勿夸大）**：本件只补**前提**。`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprThetaSAgreeY

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`hY` 的 `S'`-世界形态**：`θ₁' (ymat k) = θ₂' (ymat k)`。 -/
theorem thetaSpr1S_agree_ymat [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) (k : {k : Fin r // k.val ≠ 0}) :
    thetaSpr1S F r n D k₀ hk₀ h (ymat F r n k)
      = thetaSpr2S F r n D k₀ hk₀ h (ymat F r n k) := by
  show thetaSpr1 F r n D k₀ hk₀ h ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ h ((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n)))
  exact thetaSpr_agree_on_ymat F r n D k₀ hk₀ h k

#print axioms thetaSpr1S_agree_ymat

end SprThetaSAgreeY

/-! ## §71 ★★★★★★★ **`S'`-世界 `N`-不变 ⟹ `K'`-世界 `N`-不变**（两个动作世界的搬迁桥）

`lem:14.23`／`lem:14.24` 的 `S'`-世界形态给出的是 **`sprPsiD b`／`sprPsiSM σ`** 层面的不变性；
而 `prop:14.19` 后半的收口（§55 等化子判据、§59 坐标覆盖）需要的是 **`K'`-世界**的
`sprMatNFixed`。本节把两者接起来：

```
(∀ b, sprPsiD b α = α)  ∧  (∀ σ, sprPsiSM σ α = α)
  ⟹  sprMatNFixed (α.map (algebraMap S' K'))
```

**证明只有两行**：`GenericInv` 的两条**已机检**的**动作—换系数交换律**
`sprPsiDK_algebraMap`（`ψ^K_b(β 的像) = (ψ^S_b β) 的像`）与 `sprPsiSK_algebraMap`
（`ψ^K_σ(β 的像) = (ψ^S_σ β) 的像`），把 `K'`-世界的两个不变性化归到 `S'`-世界的假设。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `sprMatNFixed_map_of_sprInvariant` | **`S'`-世界 `N`-不变 ⟹ `K'`-世界 `N`-不变** |

**用途**：第 438 轮起攻 `prop:14.19` 后半的**多项式情形**时的唯一桥梁——
用 `lem1424_general`（前提已在 §62／§64／§70 全部就位）得 `θ₁'(α) = θ₂'(α)`，
再经本桥把 `α` 送进 `K'`-世界，最后由 §55／§59 收口 `α.map ∈ UDK'`。

**射程（勿夸大）**：本件只做**世界搬迁**。`sprPsiD`／`sprPsiSM` 的不变性由 `sprPsiMonoR`-不变性
供给的**书签账（`τ`／`b` 分解）尚未做**；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprFixedMapBridge

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **`S'`-世界 `N`-不变 ⟹ `K'`-世界 `N`-不变**（经两条动作—换系数交换律）。 -/
theorem sprMatNFixed_map_of_sprInvariant [Nonempty (Fin n)] [NeZero n]
    {α : Matrix (Fin n) (Fin n) (Spr F r n)}
    (hD : ∀ b : Fin n → Fˣ, sprPsiD (F := F) (r := r) (n := n) b α = α)
    (hS : ∀ σ : Equiv.Perm (Fin n), sprPsiSM (F := F) (r := r) (n := n) σ α = α) :
    sprMatNFixed F r n (α.map (algebraMap (Spr F r n) (SprField F r n))) := by
  refine ⟨fun b => ?_, fun σ => ?_⟩
  · rw [sprPsiDK_algebraMap, hD b]
  · rw [sprPsiSK_algebraMap, hS σ]

#print axioms sprMatNFixed_map_of_sprInvariant

end SprFixedMapBridge

/-! ## §72 ★★★★★ **`sprMonoAeval` 在 `σ = 1` 处就是 `sprDiagHom`**（多项式情形书签账的第 1 条）

第 439 轮把"多项式情形"唯一剩余的书签账定位成一条可核等式，本节证掉它：

```
sprMonoAeval R xi yv 1 (fun i => Units.map (algebraMap F R) ((b i)⁻¹))
  = sprDiagHom b            （取 R = S'、xi = X∘inl、yv = X∘inr）
```

**为何它正是所需的那条**：`sprMonoAeval`（`GenericInv:8147`）定义为
`aeval (Sum.elim (fun i => xi (σ i)) (fun ijk => ((c ijk.2.1 * (c ijk.1)⁻¹ : Rˣ) : R) * yv (σ ijk.1, σ ijk.2.1, ijk.2.2)))`；
在 `σ = 1`、`c = fun i => U.map ((b i)⁻¹)` 时它把 `x_ii ↦ x_ii`、`y_ijk ↦ (b j)⁻¹ · ((b i)⁻¹)⁻¹ · y_ijk`
＝ `b i (b j)⁻¹ · y_ijk`，而后者**正是** `sprDiagHom b`（`GenericInv:5179`／`sprDiagHom_X_inr`）的公式。
两级 `⁻¹` 在此**恰好抵消**（R218 的 `b⁻¹` 陷阱在本式里不发作）。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprMonoAeval_one_units` | **`sprMonoAeval` 在 `σ = 1`、`c = (b⁻¹)` 处 ＝ `sprDiagHom b`** |

**下一轮**：由本式 ＋ `sprPsiD` 的定义展开得
`sprPsiMonoR R xi yv 1 c α = sprPsiD b α`（书签账第 2 条），对称地得
`sprPsiMonoR R xi yv σ 1 α = sprPsiSM σ α`；两者接入 §71 的桥即通**多项式情形**。

**射程（勿夸大）**：本件只是**书签**（`AlgHom` 等式），无数学内容；`M_n(K')^N ⊆ UDK'`、
`ThetaAgreeHypK'`、PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprMonoAevalUnits

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`sprMonoAeval`（`σ = 1`、`c = (b⁻¹)`）＝ `sprDiagHom b`**。 -/
theorem sprMonoAeval_one_units (b : Fin n → Fˣ) :
    sprMonoAeval (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk))
        (1 : Equiv.Perm (Fin n))
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))
      = sprDiagHom F r n b := by
  apply MvPolynomial.algHom_ext
  intro s
  cases s with
  | inl i =>
    rw [sprMonoAeval_X_inl, sprDiagHom_X_inl]
    simp
  | inr ijk =>
    obtain ⟨i, j, k⟩ := ijk
    simp only [sprMonoAeval, MvPolynomial.aeval_X, Sum.elim_inr, Equiv.Perm.one_apply,
      sprDiagHom_X_inr]
    simp [inv_inv, mul_comm, mul_left_comm, mul_assoc]

#print axioms sprMonoAeval_one_units

end SprMonoAevalUnits

/-! ## §73 ★★★★★ **多项式情形书签账的第 2 条**：`sprPsiMonoR` 在 `(σ = 1, c = b⁻¹)` 处 ＝ `sprPsiD b`

第 439 轮把"多项式情形"唯一剩余的书签账定位成两条；第 440 轮做了第 1 条（`sprMonoAeval_one_units`）。
本节把**第 2 条及其三个对角/置换辅助**一并机检：

```
sprPsiMonoR R (X∘inl) (X∘inr) 1 (fun i => U.map ((b i)⁻¹)) α  =  sprPsiD b α
```

**拆解（三个辅助 ＋ 一条主式）**：
| 辅助 | 内容 |
|---|---|
| `sprPmat_one` | `sprPmat R 1 = 1`（置换矩阵在 `1` 处） |
| `sprDiagMatR_unitsMap_inv` | `sprDiagMatR (fun i => U.map ((b i)⁻¹)) = sprDiagMat (fun i => (b i)⁻¹)` |
| `sprDiagMatR_unitsMap_inv_inv` | `sprDiagMatR (fun i => (U.map ((b i)⁻¹))⁻¹) = sprDiagMat b` |
| ★ `sprPsiMonoR_one_left` | **主式**：两条夹 `α.map` 的对角矩阵一致 ⟹ 等式成立 |

主式的证明是 `simp only [sprPsiMonoR, sprPsiD, sprMonoAeval_one_units, sprPmat_one, inv_one,
  sprDiagMatR_unitsMap_inv, sprDiagMatR_unitsMap_inv_inv, one_mul, mul_one]` —— **一次收口**。

**工艺（R284，本轮由"空转诊断"换取）**：当残目标**打印上两侧完全相同**时，**不要**再试 `rfl`／
`simp`——根因是**两处 `if` 的 `Decidable` 实例不同**（R274 同族）。**正解**：
`by_cases h : i = j <;> simp [h]`（把两侧都化到 `h` 分支，实例差异消失）。
`inv_one` 也必须显式进 `simp only`（`σ⁻¹` 在 `σ = 1` 处不会自动归约）。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprPsiMonoR_one_left` | **`sprPsiMonoR (1, b⁻¹) = sprPsiD b`** |
| ★★★★ `sprPmat_one`／`sprDiagMatR_unitsMap_inv`／`sprDiagMatR_unitsMap_inv_inv` | 三个辅助 |

**下一轮**：对称地做 `sprPsiMonoR R xi yv σ 1 = sprPsiSM σ`（`b = 1` 侧），接入 §71 的桥，
即得**多项式情形** `α.map ∈ UDK'`（再用 §55／§59）。

**射程（勿夸大）**：本节全是 `AlgHom`／矩阵等式（**书签**），无数学内容；
`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprPsiMonoROne

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★ `sprPmat R 1 = 1`（置换矩阵在 `1` 处）。

★ `sprDiagMatR` 的两个换写出（`Units.map` 保持 `⁻¹`）与主式 `sprPsiMonoR_one_left`
（`sprPsiMonoR` 在 `(σ = 1, c = b⁻¹)` 处 ＝ `sprPsiD b`）见下。 -/
theorem sprPmat_one (R : Type) [CommSemiring R] (n : ℕ) :
    sprPmat R (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp only [sprPmat, Matrix.of_apply, Matrix.one_apply, Equiv.Perm.one_apply]
  by_cases h : i = j <;> simp [h]

#print axioms sprPmat_one

theorem sprDiagMatR_unitsMap_inv (b : Fin n → Fˣ) :
    sprDiagMatR (n := n) (Spr F r n)
      (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))
      = sprDiagMat (n := n) (fun i => (b i)⁻¹) := by
  ext i j
  simp only [sprDiagMatR, sprDiagMat, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

#print axioms sprDiagMatR_unitsMap_inv

theorem sprDiagMatR_unitsMap_inv_inv (b : Fin n → Fˣ) :
    sprDiagMatR (n := n) (Spr F r n)
      (fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹)
      = sprDiagMat (n := n) b := by
  ext i j
  simp only [sprDiagMatR, sprDiagMat, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

#print axioms sprDiagMatR_unitsMap_inv_inv

theorem sprPsiMonoR_one_left (b : Fin n → Fˣ) (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiMonoR (F := F) (r := r) (n := n) (R := Spr F r n)
      (xi := fun i => MvPolynomial.X (Sum.inl i))
      (yv := fun ijk => MvPolynomial.X (Sum.inr ijk))
      (σ := 1)
      (c := fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α
      = sprPsiD (F := F) (r := r) (n := n) b α := by
  simp only [sprPsiMonoR, sprPsiD, sprMonoAeval_one_units, sprPmat_one, inv_one,
    sprDiagMatR_unitsMap_inv, sprDiagMatR_unitsMap_inv_inv, one_mul, mul_one]

#print axioms sprPsiMonoR_one_left

end SprPsiMonoROne

/-! ## §74 ★★★ **`sprDiagMatR 1 = 1`**（书签账的辅助：`b = 1` 侧的两条对角矩阵都退化为 `1`）

`b = 1` 侧的分解（`sprPsiMonoR R xi yv σ 1 = sprPsiSM σ`）需要
`sprDiagMatR (fun _ => 1) = 1`（以及 `(fun i => ((1 : Fin n → Rˣ) i)⁻¹)` 的同一式）。
本节把前者机检；后者由 `(1 : Rˣ)⁻¹ = 1` ＋ 本式立即得到。

**工艺（R284 续）**：与 §73 同法——`by_cases h : i = j <;> simp [h]`
（残目标打印上两侧相同 ⟹ 是 `Decidable` 实例差异，`rfl`／`simp` 不认）。

| 件 | 内容 |
|---|---|
| ★★★ `sprDiagMatR_one` | **`sprDiagMatR (n) R (fun _ => 1) = 1`** |

**下一轮**：`sprMonoAeval` 在 `c = 1` 处 ＝ `sprPermAlgEquiv σ`（`sprPermAlgEquiv_X_inl`／`_inr` 均已确认存在），
再合本节的辅助即得 `sprPsiMonoR R xi yv σ 1 α = sprPsiSM σ α`。

**射程（勿夸大）**：本件是矩阵等式（**书签**）；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprDiagMatROne

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★ **`sprDiagMatR` 在平凡单位族上等于 `1`**（`b = 1` 侧的辅助）。 -/
theorem sprDiagMatR_one (R : Type) [CommSemiring R] (n : ℕ) :
    sprDiagMatR (n := n) R (fun _ => 1) = 1 := by
  ext i j
  simp only [sprDiagMatR, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

#print axioms sprDiagMatR_one


end SprDiagMatROne

/-! ## §75 ★★★★★ **`sprMonoAeval` 在 `c = 1` 处就是 `sprPermAlgEquiv σ`**（书签账对称侧的第 1 条）

§72 证了 `σ = 1` 侧（`= sprDiagHom b`）；本节证对称侧（`c = 1`）：

```
sprMonoAeval R (X∘inl) (X∘inr) σ 1  =  sprPermAlgEquiv σ
```

**证明**：`MvPolynomial.algHom_ext` ＋ 两个分支；
`inl`：`sprMonoAeval_X_inl` 给 `xi (σ i) = X (σ i)`，`sprPermAlgEquiv_X_inl` 给同一式；
`inr`：`sprMonoAeval` 的系数 `(1 j) * (1 i)⁻¹ = 1` 归约后与 `sprPermAlgEquiv_X_inr` 的
`X (σ i, σ j, k)` 相同。

**工艺（R285）**：`sprPermAlgEquiv` 在目标里以**强制转换 `↑(sprPermAlgEquiv …)`** 形态出现，
而两条 `_X_` 引理的 LHS 是**未强制转换**的应用 ⟹ `rw` 报 "未找到模式"。
**正解**：先用 `show` 把目标写成未强制转换的形态，再 `rw`。这是第 441–443 轮失败的同一族根因的**第三种表现**。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprMonoAeval_one_right` | **`sprMonoAeval (σ, c = 1) = sprPermAlgEquiv σ`** |

**下一轮**：主式 `sprPsiMonoR R xi yv σ 1 α = sprPsiSM σ α`——ⓘ 本轮 `simp only [...]` 版**超时**
（`whnf` 1M heartbeats），须改为**逐步 `have` ＋ `rw`**（先把两个 `sprDiagMatR` 因子用 §74 的
`sprDiagMatR_one` 归约为 `1`，再 `one_mul`／`mul_one`），**不要**大 `simp only`。

**射程（勿夸大）**：本件是 `AlgHom` 等式（**书签**）；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、
PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprMonoAevalOneRight

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`sprMonoAeval` 在 `c = 1` 处 ＝ `sprPermAlgEquiv σ`**（`b = 1` 侧的第 1 条）。 -/
theorem sprMonoAeval_one_right (σ : Equiv.Perm (Fin n)) :
    sprMonoAeval (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (1 : Fin n → (Spr F r n)ˣ)
      = sprPermAlgEquiv F r n σ := by
  apply MvPolynomial.algHom_ext
  intro s
  cases s with
  | inl i =>
    show (sprMonoAeval (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (1 : Fin n → (Spr F r n)ˣ)) (MvPolynomial.X (Sum.inl i))
      = (sprPermAlgEquiv F r n σ) (MvPolynomial.X (Sum.inl i))
    rw [sprMonoAeval_X_inl, sprPermAlgEquiv_X_inl]
  | inr ijk =>
    obtain ⟨i, j, k⟩ := ijk
    show (sprMonoAeval (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (1 : Fin n → (Spr F r n)ˣ)) (MvPolynomial.X (Sum.inr (i, j, k)))
      = (sprPermAlgEquiv F r n σ) (MvPolynomial.X (Sum.inr (i, j, k)))
    simp only [sprMonoAeval, MvPolynomial.aeval_X, Sum.elim_inr, sprPermAlgEquiv_X_inr]
    simp

#print axioms sprMonoAeval_one_right


end SprMonoAevalOneRight

/-! ## §76 ★★★ **`sprDiagMatR` 在 `(1 i)⁻¹` 上等于 `1`**（`b = 1` 侧的第二个对角辅助）

§74 给了 `sprDiagMatR (fun _ => 1) = 1`。本节补上 `sprDiagMatR (fun i => ((1 : Fin n → Rˣ) i)⁻¹) = 1`
——`sprPsiMonoR` 的**第二个**对角因子（`sprDiagMatR (fun i => (c i)⁻¹)` 在 `c = 1` 处）。

| 件 | 内容 |
|---|---|
| ★★★ `sprDiagMatR_one_inv` | **`sprDiagMatR (fun i => ((1) i)⁻¹) = 1`** |

**⟹ 至此 `b = 1` 侧的**两个**对角辅助都齐了**（§74 ＋ 本节）；
配合 §75 的 `sprMonoAeval_one_right`，主式 `sprPsiMonoR … σ 1 = sprPsiSM σ`
只剩一次 `rw` 链的**记法对齐**（本轮两次尝试均卡在 `rw` 的模式匹配，不是数学问题）。

**射程（勿夸大）**：本件是矩阵等式（**书签**）；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprDiagMatROneInv

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★ **`sprDiagMatR` 在 `(fun i => (1 i)⁻¹)` 上等于 `1`**（`b = 1` 侧的第二个对角辅助）。 -/
theorem sprDiagMatR_one_inv (R : Type) [CommSemiring R] (n : ℕ) :
    sprDiagMatR (n := n) R (fun i => ((1 : Fin n → Rˣ) i)⁻¹) = 1 := by
  have h3 : (fun i => ((1 : Fin n → Rˣ) i)⁻¹) = (fun _ => 1) := by
    funext i
    simp
  rw [h3]
  exact sprDiagMatR_one R n

#print axioms sprDiagMatR_one_inv


end SprDiagMatROneInv

/-! ## §77 ★★★★ **主式的两处记法桥**（`Pi.one` 形态 ＋ 强制转换形态）

第 448 轮把 `b = 1` 侧主式（`sprPsiMonoR … σ 1 = sprPsiSM σ`）的残目标打印出来，定位了两处
**记法障碍**（均非数学问题）。本节把两处桥都机检：

```
sprDiagMatR (n) R (1 : Fin n → Rˣ) = 1                          （Pi.one 形态）
⇑(sprMonoAeval R xi yv σ 1) = ⇑(sprPermAlgEquiv σ)              （强制转换形态）
```

* 第一处：`1 : Fin n → Rˣ` 与 `fun _ => 1` **def-eq 但不同一**（R258 同族）⟹ §74 的
  `sprDiagMatR_one` 不能直接 `rw`；本节给 `1` 形态（`rfl` 转再套 §74）。
* 第二处：§75 的 `sprMonoAeval_one_right` 是**未强制转换**的 `AlgHom` 等式，而目标里是
  `α.map ⇑(…)` ⟹ 本节给 `⇑` 形态（`congrArg` ＋ **显式标注的 lambda binder**）。

| 件 | 内容 |
|---|---|
| ★★★★ `sprDiagMatR_one_pi` | **`sprDiagMatR (1 : Fin n → Rˣ) = 1`** |
| ★★★★ `sprMonoAeval_one_right_coe` | **`⇑(sprMonoAeval … σ 1) = ⇑(sprPermAlgEquiv σ)`** |

**工艺（R286）**：`congrArg` 的 lambda **必须显式标注 binder 类型**
（`fun (f : Spr →ₐ[F] Spr) => ⇑f`），否则报 "cannot coerce to function"。

**ⓘ 主式仍未过**：即便有这两条桥，`rw [sprPsiMonoR, sprPsiSM, hmap, h1, h2, …]` 仍报
"未找到模式"——`hmap` 的 `⇑` 与目标里的 `⇑` 在**实例路径**上仍不同一（R274 同族）。
下一轮用 `erw [hmap]` 或 `conv` 定位到具体子项再改。

**射程（勿夸大）**：本节是记法桥（**书签**）；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprShapeBridges

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★ **`sprDiagMatR` 在 `Pi.one` 形态下等于 `1`**（主式的第一处记法桥）。 -/
theorem sprDiagMatR_one_pi (R : Type) [CommSemiring R] (n : ℕ) :
    sprDiagMatR (n := n) R (1 : Fin n → Rˣ) = 1 := by
  have h : (1 : Fin n → Rˣ) = (fun _ => 1) := rfl
  rw [h]
  exact sprDiagMatR_one R n
#print axioms sprDiagMatR_one_pi

/-- ★★★★ **`sprMonoAeval` 的强制转换形态**（主式的第二处记法桥）。 -/

theorem sprMonoAeval_one_right_coe (σ : Equiv.Perm (Fin n)) :
    (⇑(sprMonoAeval (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (1 : Fin n → (Spr F r n)ˣ)))
      = ⇑(sprPermAlgEquiv F r n σ) := by
  exact congrArg (fun (f : Spr F r n →ₐ[F] Spr F r n) => (⇑f : Spr F r n → Spr F r n))
    (sprMonoAeval_one_right (F := F) (r := r) (n := n) (σ := σ))

#print axioms sprMonoAeval_one_right_coe

end SprShapeBridges

/-! ## §78 ★★★★★★ **`b = 1` 侧主式**：`sprPsiMonoR` 在 `(σ, c = 1)` 处 ＝ `sprPsiSM σ`

§72／§73 完成了 `σ = 1` 侧（`= sprPsiD b`），§74–§77 备齐了 `b = 1` 侧的全部零件。本节把
**对称侧的主式**机检：

```
sprPsiMonoR R (X∘inl) (X∘inr) σ 1 α  =  sprPsiSM σ α
```

**证明（四步，第 451 轮失败的记法问题的正解）**：
1. `hmap' : α.map ⇑(sprMonoAeval … σ 1) = α.map ⇑(sprPermAlgEquiv σ)`
   （`congrArg` ＋ **显式标注的 lambda binder**，R286）；★ 关键是把它做成**关于 `α.map` 的等式**
   （子项形状与目标一致），而不是关于 `⇑f` 的等式；
2. `rw [sprPsiMonoR, sprPsiSM]` 展开两侧；
3. **`erw [hmap']`**（`rw` 在 `α.map ⇑(…)` 上仍不匹配，`erw` 的 defeq 匹配才行——R252 老手法）；
4. `rw [sprDiagMatR_one_pi, sprDiagMatR_one_inv]`（§77／§76）把两个对角因子归约，
   再 `simp only [one_mul, mul_one]` 收口。

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprPsiMonoR_one_right` | **`sprPsiMonoR (σ, 1) = sprPsiSM σ`** |

**⟹ 书签账**两条**全部完成**（`σ = 1` 侧 §73，`b = 1` 侧本节）：
`sprPsiMonoR` 的不变性**可分解**为 `sprPsiD`（`τ = 1`）与 `sprPsiSM`（`b = 1`）两侧。
接入 §71 的**世界搬迁桥**即得 **`sprMatNFixed (α.map algebraMap)`** 的 S-来源，
再经 §55／§59 收口**多项式情形** `α.map ∈ UDK'`。

**工艺（R287）**：`α.map` 上的改写要**先把等式提升到 `α.map` 层**再 `erw`；直接 `rw` `⇑f = ⇑g`
在 `α.map ⇑(…)` 上不匹配（`⇑` 的实例路径不同一，R274 同族）。

**射程（勿夸大）**：本节是 `AlgHom` 等式（**书签**）；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、
PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprPsiMonoROneRight

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★ **`sprPsiMonoR` 在 `(σ, c = 1)` 处 ＝ `sprPsiSM σ`**（`b = 1` 侧主式）。 -/
theorem sprPsiMonoR_one_right (σ : Equiv.Perm (Fin n))
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiMonoR (F := F) (r := r) (n := n) (R := Spr F r n)
      (xi := fun i => MvPolynomial.X (Sum.inl i))
      (yv := fun ijk => MvPolynomial.X (Sum.inr ijk))
      (σ := σ) (c := 1) α
      = sprPsiSM (F := F) (r := r) (n := n) σ α := by
  have hmap' : α.map ⇑(sprMonoAeval (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (1 : Fin n → (Spr F r n)ˣ))
      = α.map ⇑(sprPermAlgEquiv F r n σ) :=
    congrArg (fun (f : Spr F r n → Spr F r n) => α.map f)
      (sprMonoAeval_one_right_coe (F := F) (r := r) (n := n) σ)
  rw [sprPsiMonoR, sprPsiSM]
  erw [hmap']
  rw [sprDiagMatR_one_pi, sprDiagMatR_one_inv]
  simp only [one_mul, mul_one]

#print axioms sprPsiMonoR_one_right


end SprPsiMonoROneRight

/-! ## §79 ★★★★★★★ **`sprPsiMonoR`-不变 ⟹ `K'`-世界 `N`-不变**（多项式情形第 1 步）

把 §71 的**世界搬迁桥**（它要 `sprPsiD`／`sprPsiSM` 两侧的不变性）与 §73／§78 的**两条主式**
接起来，得到**一个**假设（`sprPsiMonoR`-不变，即 `lem1424_general` 的 `hα` 形态）就够：

```
(∀ τ b, sprPsiMonoR R (X∘inl) (X∘inr) τ (fun i => U.map ((b i)⁻¹)) α = α)
  ⟹  sprMatNFixed (α.map (algebraMap S' K'))
```

**证明（两行半）**：`τ = 1` 支用 §73（`sprPsiMonoR_one_left`），`b = 1` 支用 §78
（`sprPsiMonoR_one_right`，先把 `fun i => U.map ((1 i)⁻¹)` 归约成 `1`），再接 §71。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `sprMatNFixed_map_of_sprPsiMonoR` | **`hα`（S-世界）⟹ `sprMatNFixed (α.map)`（`K'`-世界）** |

**⟹ 多项式情形的链条现在只差最后一步**：
`lem1424_general`（前提齐备）给 `θ₁'(α) = θ₂'(α)` ⟹ 本节给 `sprMatNFixed (α.map)` ⟹
§59 的 `NfixedIsCoordHyp` 给 `α.map = xiCoordMap k` ⟹ §55 的**等化子判据**给 **`α.map ∈ UDK'`**。

**射程（勿夸大）**：本件是**桥梁**；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprFixedMapOfMonoR

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★ **`sprPsiMonoR`-不变（S-世界）⟹ `sprMatNFixed`（`K'`-世界）**。 -/
theorem sprMatNFixed_map_of_sprPsiMonoR [Nonempty (Fin n)] [NeZero n]
    {α : Matrix (Fin n) (Fin n) (Spr F r n)}
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (n := n) (R := Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α) :
    sprMatNFixed F r n (α.map (algebraMap (Spr F r n) (SprField F r n))) := by
  refine sprMatNFixed_map_of_sprInvariant (F := F) (r := r) (n := n) ?_ ?_
  · intro b
    have h := hα 1 b
    rw [sprPsiMonoR_one_left] at h
    exact h
  · intro σ
    have h := hα σ 1
    have hc : (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom
        (((1 : Fin n → Fˣ) i)⁻¹)) = (1 : Fin n → (Spr F r n)ˣ) := by
      funext i
      simp
    rw [hc, sprPsiMonoR_one_right] at h
    exact h

#print axioms sprMatNFixed_map_of_sprPsiMonoR


end SprFixedMapOfMonoR

/-! ## §80 ★★★★★★★★★ **多项式情形收口**：`M_n(S')` 的 `N`-不变元经 `algebraMap` 落在 `UDK'` 里

把 §62–§79 的全部零件装配成**一条定理**——这是源文 `prop:14.19` 第二半在**多项式情形**的机检：

```
α ∈ M_n(S') 为 N-不变（sprPsiMonoR 形态）
  ⟹ α.map (algebraMap S' K') ∈ UDK'
```

**装配链（四步，每步都已是机检件）**：
1. **`lem1424_general`**（`GenericInv` §137，S-世界 `lem:14.24`）：前提 `hX`／`hY`／`hΔ`
   分别是 §64 的 `thetaSpr1S_agree_xdiag`、§70 的 `thetaSpr1S_agree_ymat`、§62 的
   `sprDiscrNonZeroDiv_thetaSpr1S` ⟹ **`θ₁'(α) = θ₂'(α)`**；
2. `θ_i'` 的定义即 `θ_i ∘ (α ↦ α.map algebraMap)` ⟹ **`θ₁ (α.map) = θ₂ (α.map)`**（def-eq）；
3. §79 **`sprMatNFixed_map_of_sprPsiMonoR`** ⟹ `sprMatNFixed (α.map)`；
4. §59 的 **`nfixedIsCoordHyp_of_xiBasisHypK'`** ⟹ `α.map = xiCoordMap k`；
5. §55 的**等化子判据**（配 §59 的 `MatMapFaithfulHyp` 与无条件的 `EtaEqualizerHyp`）
   ⟹ **`α.map ∈ UDK'`**。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `map_mem_UDK'_of_sprPsiMonoR` | **多项式情形：`α.map ∈ UDK'`** |

**条件**：PI 输入（`UDKTensorHypK'` ＋ `XiBasisHypK'`）与 `[Infinite F]`——即 `lem1424_general` 自带的
无限性假设。**无其它假设**。

**⟹ 距 `M_n(K')^N ⊆ UDK'`（K'-世界全般情形）只差"分母清整"**：
`α ∈ M_n(K')` 为 `N`-不变时如何化成 `β.map (algebraMap)`（`β ∈ M_n(S')`）。
该步的循环风险见 `wiki/proj-abgv52-h2-endgame-corrected.md` §7.14（须 `S'^N ⊆ Z`）。

**射程（勿夸大）**：本节**不**证 `M_n(K')^N ⊆ UDK'`（只证多项式情形）；`ThetaAgreeHypK'`、
PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprMapMemUDK

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★★★★ **多项式情形收口**：`α ∈ M_n(S')` 为 `N`-不变 ⟹ `α.map (algebraMap S' K') ∈ UDK'`。 -/
theorem map_mem_UDK'_of_sprPsiMonoR [Nonempty (Fin n)] [NeZero n] [Infinite F]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    {α : Matrix (Fin n) (Fin n) (Spr F r n)}
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (n := n) (R := Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α) :
    α.map (algebraMap (Spr F r n) (SprField F r n)) ∈ UDK' F r n D k₀ hk₀ := by
  have hθ' : thetaSpr1S F r n D k₀ hk₀ hPI α = thetaSpr2S F r n D k₀ hk₀ hPI α :=
    lem1424_general (F := F) (r := r) α hα
      (thetaSpr1S F r n D k₀ hk₀ hPI) (thetaSpr2S F r n D k₀ hk₀ hPI)
      (thetaSpr1S_agree_xdiag F r n D k₀ hk₀ hPI)
      (fun k => thetaSpr1S_agree_ymat F r n D k₀ hk₀ hPI k)
      (sprDiscrNonZeroDiv_thetaSpr1S F r n D k₀ hk₀ hPI)
  have hθ : thetaSpr1 F r n D k₀ hk₀ hPI
        (α.map (algebraMap (Spr F r n) (SprField F r n)))
      = thetaSpr2 F r n D k₀ hk₀ hPI
        (α.map (algebraMap (Spr F r n) (SprField F r n))) := hθ'
  have hfix := sprMatNFixed_map_of_sprPsiMonoR (F := F) (r := r) (n := n) hα
  obtain ⟨k, hk⟩ := nfixedIsCoordHyp_of_xiBasisHypK' F r n D k₀ hk₀ hB
    (α.map (algebraMap (Spr F r n) (SprField F r n))) hfix
  exact hk ▸ mem_UDK'_of_theta_eq F r n D k₀ hk₀ hPI
    (matMapFaithfulHyp_of_xiBasisHypK' F r n D k₀ hk₀ hB)
    (etaEqualizerHyp_unconditional F r n D k₀ hk₀) k
    (by rw [hk]; exact hθ)

#print axioms map_mem_UDK'_of_sprPsiMonoR


end SprMapMemUDK

/-! ## §81 ★★★★ **`sprFieldNFixed` 对有限积封闭**（`lem:14.25` 对称化步的辅助）

源文 `lem:14.25` 的证明把分母 `s` 对称化成 `s' = ∏_{σ ∈ S_n} σ(s)`，该积**`N`-不变**。
本节给该步的**代数核**：`K'^N` 对**有限积**封闭。

```
(∀ i ∈ t, sprFieldNFixed (f i))  ⟹  sprFieldNFixed (∏ i ∈ t, f i)
```

| 件 | 内容 |
|---|---|
| ★★★★ `sprFieldNFixed_finset_prod` | **`K'^N` 对有限积封闭** |

**用途**：`lem:14.25` 的 `K'`-世界形态（"分母清整"）一旦开工，对称化步即可直接调用本件；
目前它是**已知最后障碍**（§7.14／交接件 §36）的**预备件**。

**射程（勿夸大）**：本件是 `K'^N` 的封闭性辅助，**不**证 `S'^N ⊆ Z`、**不**证 `M_n(K')^N ⊆ UDK'`；
`ThetaAgreeHypK'`、PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprFieldNFixedProd

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★ **`K'^N` 对有限积封闭**（`lem:14.25` 对称化步的代数核）。 -/
theorem sprFieldNFixed_finset_prod {ι : Type*} (t : Finset ι) (f : ι → SprField F r n)
    (h : ∀ i ∈ t, sprFieldNFixed F r n (f i)) :
    sprFieldNFixed F r n (∏ i ∈ t, f i) := by
  classical
  refine Finset.prod_induction _ _ (fun a b ha hb => sprFieldNFixed_mul F r n ha hb)
    (sprFieldNFixed_one F r n) ?_
  intro i hi
  exact h i hi

#print axioms sprFieldNFixed_finset_prod


end SprFieldNFixedProd

/-! ## §82 ★★★★★★ **`M_n(K')^N` 对 `↥Z`-纯量封闭**（"分母清整"路线的结构性前提）

第 456 轮的判读：`M_n(K')^N` 是 **`↥Z`-模**而不是 `K'`-模（`ψ_b(c • α) = φ_b(c) • ψ_b(α)`）。
本节把该结构性事实机检：

```
α ∈ M_n(K')^N  ⟹  (algebraMap ↥Z (M_n K') z) · α ∈ M_n(K')^N        （z ∈ Z）
```

**证明（两行）**：`↥(sprMatNFixedAlg)` 已是 `↥Z`-**子代数**（§37），故 `mul_mem` 直接给出；
`algebraMap z` 的 `N`-不变性由 `sprMatNFixed_scalar_iff`（纯量↔系数）＋
`sprCenterImageField_fixed`（`z ∈ Z ⟹ z ∈ K'^N`）转来。

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprMatNFixed_algebraMap_mul` | **`M_n(K')^N` 对 `↥Z`-纯量封闭** |

**⟹ 用途**：若 `α ∈ M_n(K')^N` 能写成 `Σ_i z_i • β_i`（`z_i ∈ Z`、`β_i ∈ M_n(S')^N`），
则由 §80（`β_i.map ∈ UDK'`）＋ `UDK'` 是 `↥Z`-子代数 ⟹ **`α ∈ UDK'`**。
故最后障碍精确化为：**`M_n(K')^N` 是否由 `M_n(S')^N` 经 `↥Z`-纯量生成**（＝ `Z` 能否清掉分母，
与 §7.14 的 `S'^N ⊆ Z` 同义）。

**射程（勿夸大）**：本件是**结构性前提**，**不**证 `M_n(K')^N ⊆ UDK'`；
`ThetaAgreeHypK'`、PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprMatNFixedZSmul

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★★ **`M_n(K')^N` 对 `↥Z`-纯量封闭**（`α ∈ M_n(K')^N`, `z ∈ Z` ⟹ `algebraMap z · α ∈ M_n(K')^N`）。 -/
theorem sprMatNFixed_algebraMap_mul [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(sprCenterImageField F r n D k₀ hk₀))
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : sprMatNFixed F r n α) :
    sprMatNFixed F r n (algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n)) z * α) :=
  (sprMatNFixedAlg F r n D k₀ hk₀).mul_mem
    ((sprMatNFixed_scalar_iff F r n (z : SprField F r n)).mpr
      (sprCenterImageField_fixed F r n D k₀ hk₀ (z : SprField F r n) z.2))
    hα

#print axioms sprMatNFixed_algebraMap_mul


end SprMatNFixedZSmul

/-! ## §83 ★★★★★ **`prop:14.19` 的两半相扣**：`UD` 半 ⟹ `Z` 半（`K'^N`-元落在 `Z` 里）

源文 `prop:14.19` 的两条结论（`UD = M_n(K')^N` 与 `Z = K'^N`）在证明中**互为手段**。
本节把其中一个方向机检：**若 `M_n(K')^N ⊆ UDK'` 成立，则每个 `N`-不变纯量都在 `Z` 里**。

```
(∀ α, sprMatNFixed α → α ∈ UDK')  ∧  sprFieldNFixed x   ⟹   x ∈ Z
```

**证明**：由 §66 把 `hU` 转成 `ThetaAgreeHypK'`，再由 §68 的等价 `x ∈ Z ⟺ sprFieldNFixed x` 收口。

| 件 | 内容 |
|---|---|
| ★★★★★ `mem_sprCenterImageField_of_le_UDK` | **`UD` 半 ⟹ `Z` 半** |

**意义（对最后障碍的判读）**：§7.17 的 `(GEN)` **不是**独立于目标的额外假设——它由目标本身蕴含。
故 `M_n(K')^N ⊆ UDK'` 与 `Z = K'^N` **不可分开证明**（在本库的现有接口下），这也解释了
为何"先证 `Z` 半再用它做分母清整"这条路会**循环**（§7.14）。

**射程（勿夸大）**：本件是**蕴含**，不是对任一办的证明；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、
PI 输入**均未证**；**H2 的无条件形态仍未达到**。 -/

section SprH2HalvesLinked

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`UD` 半 ⟹ `Z` 半**（源文 `prop:14.19` 两半相扣）。 -/
theorem mem_sprCenterImageField_of_le_UDK [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (hU : ∀ α : Matrix (Fin n) (Fin n) (SprField F r n),
      sprMatNFixed F r n α → α ∈ UDK' F r n D k₀ hk₀)
    {x : SprField F r n} (hx : sprFieldNFixed F r n x) :
    x ∈ sprCenterImageField F r n D k₀ hk₀ :=
  (mem_sprCenterImageField_iff_sprFieldNFixed F r n D k₀ hk₀ hPI hB
    ((thetaAgreeHypK'_iff F r n D k₀ hk₀ hPI hB).mpr hU) x).mpr hx

#print axioms mem_sprCenterImageField_of_le_UDK


end SprH2HalvesLinked

/-! ## §84 ★★★★ **`Z`-元素的纯量矩阵是 `N`-不变的**（§82 的另一半，单列供引用）

§82（`sprMatNFixed_algebraMap_mul`）把 `↥Z`-纯量封闭性与"`algebraMap z` 的 `N`-不变性"**合并**在一处证明里。
本节把后者**单列**：

```
sprMatNFixed (algebraMap ↥Z (M_n K') z)        （z ∈ Z）
```

| 件 | 内容 |
|---|---|
| ★★★★ `sprMatNFixed_algebraMap` | **`z ∈ Z ⟹ algebraMap z` 是 `N`-不变纯量矩阵** |

**用途**：装配 `M_n(K')^N` 的 `↥Z`-模结构时的基本块；亦可用于 `sprPsiDK`／`sprPsiSK` 作用在
纯量矩阵上的逐条计算。

**射程（勿夸大）**：本件是**结构性辅助**；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprMatNFixedAlgebraMap

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★ **`z ∈ Z ⟹ algebraMap z`（纯量矩阵）是 `N`-不变的**。 -/
theorem sprMatNFixed_algebraMap [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(sprCenterImageField F r n D k₀ hk₀)) :
    sprMatNFixed F r n (algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n)) z) :=
  (sprMatNFixed_scalar_iff F r n (z : SprField F r n)).mpr
    (sprCenterImageField_fixed F r n D k₀ hk₀ (z : SprField F r n) z.2)

#print axioms sprMatNFixed_algebraMap


end SprMatNFixedAlgebraMap

/-! ## §85 ★★★★★ **`η₂`-侧的非零因子性**：`1 ⊗ d` 乘零 ⟹ 零（`d ≠ 0`）

§61 给了 **`η₁`-侧**（`d ⊗ 1`）的非零因子性（`coeKtoS''_mul_eq_zero`）。本节补 **`η₂`-侧**：

```
d ≠ 0  ⟹  (1 ⊗ d) * y = 0 → y = 0
```

**证明（四行）**：用 `Algebra.TensorProduct.comm`（**代数**同构）把 `(1 ⊗ d) * y` 换成
`(d ⊗ 1) * comm y`（`comm (1 ⊗ d) = d ⊗ 1 = coeKtoS'' d`，`rfl`），套 §61，再以 `comm` 的单射性回推。

| 件 | 内容 |
|---|---|
| ★★★★★ `one_tmul_mul_eq_zero` | **`1 ⊗ d` 是非零因子**（`d ≠ 0`） |

**用途**：若路线 (乙) 采用 `θ₂` 的**判别式条件**（`sprDiscrNonZeroDiv F θ₂' (sprDiscr)`），
其所需的非零因子性就是本件（`θ₂(scalar c) = scalar(1 ⊗ c)`，见 §63 的 `thetaSpr2S_apply_scalar`）。
`lem1424_general` 本身只用 `θ₁` 的条件，故本件是为**对称形态**预置的。

**射程（勿夸大）**：本件是**非零因子性**；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprEtaTwoNonZeroDiv

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`η₂`-侧非零因子**：`d ≠ 0 ⟹ (1 ⊗ d) * y = 0 → y = 0`。 -/
theorem one_tmul_mul_eq_zero [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {d : SprField F r n} (hd : d ≠ 0) {y : sprTensorK F r n D k₀ hk₀}
    (hy : ((1 : SprField F r n) ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] d) * y = 0) :
    y = 0 := by
  have hc := congrArg (Algebra.TensorProduct.comm ↥(sprCenterImageField F r n D k₀ hk₀)
    (SprField F r n) (SprField F r n)) hy
  simp only [map_mul, map_zero] at hc
  have hcd : Algebra.TensorProduct.comm ↥(sprCenterImageField F r n D k₀ hk₀)
      (SprField F r n) (SprField F r n)
      ((1 : SprField F r n) ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] d)
      = coeKtoS'' F r n D k₀ hk₀ d := rfl
  rw [hcd] at hc
  have hzero := coeKtoS''_mul_eq_zero F r n D k₀ hk₀ hd hc
  exact (Algebra.TensorProduct.comm ↥(sprCenterImageField F r n D k₀ hk₀)
    (SprField F r n) (SprField F r n)).injective (by rw [hzero, map_zero])

#print axioms one_tmul_mul_eq_zero


end SprEtaTwoNonZeroDiv

/-! ## §86 ★★★★ **`M_n(K')^N` 对幂封闭**（`sprMatNFixedAlg` 的推论）

`↥(sprMatNFixedAlg)` 是 `↥Z`-子代数（§37）⟹ 对 `*`／`1` 封闭 ⟹ 对幂封闭。本节把该推论单列。

```
sprMatNFixed α  ⟹  sprMatNFixed (α ^ k)        （k : ℕ）
```

| 件 | 内容 |
|---|---|
| ★★★★ `sprMatNFixed_pow` | **`M_n(K')^N` 对幂封闭** |

**用途**：PI 输入（`Ξ = {ψ(X_{k₀})^i ψ(X_k)^j}`）与 `N`-不变性的交互（`Ξ` 的元都是
`UDK' ⊆ M_n(K')^N` 的元素的幂积）在装配时可直接引用。

**射程（勿夸大）**：本件是**封闭性辅助**；`M_n(K')^N ⊆ UDK'`、`ThetaAgreeHypK'`、PI 输入**均未证**；
**H2 的无条件形态仍未达到**。 -/

section SprMatNFixedPow

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★ **`M_n(K')^N` 对幂封闭**。 -/
theorem sprMatNFixed_pow [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (hα : sprMatNFixed F r n α) (k : ℕ) :
    sprMatNFixed F r n (α ^ k) := by
  induction k with
  | zero => exact (sprMatNFixedAlg F r n D k₀ hk₀).one_mem
  | succ k ih =>
    rw [pow_succ]
    exact (sprMatNFixedAlg F r n D k₀ hk₀).mul_mem ih hα

#print axioms sprMatNFixed_pow


end SprMatNFixedPow

/-! ## §87 ★★★★★★★★ **`prop:14.19` 两半等价**：`UD` 半 ⟺ `Z` 半（`K'`-世界，PI 输入下）

源文 `prop:14.19`（`raw/Saltman1999ch14.tex:368`）同时断言两件事：
`UD(F,n,r) = M_n(K')^N` 与 `Z(F,n,r) = K'^N`。§83 已机检 **`UD` 半 ⟹ `Z` 半**；
本节补上**反向**：

```
(∀ x : K', N-不变 ⟹ x ∈ Z)  ⟹  (∀ α, N-不变 ⟹ α ∈ UDK')
```

⟹ 两半在本库接口下**完全等价**（`sprMatNFixed_le_UDK'_iff_zHalf`），
故"先证 `Z` 半再用它清分母"**不是循环**——`Z` 半本身就是目标的一半。

**证明的新零件（本节首件）**：`Ξ` 的每个元被 `ψ_b`／`ψ_σ` **逐点固定**
（`sprPsiDK_fixes_psi`／`sprPsiSK_fixes_psi` ＋ 乘法性），
而 `ψ_b`／`ψ_σ` 在系数上是**半线性**的（`sprPsiDK_smul`／`sprPsiSK_smul`）。
两者相减即 `Σ_p (φ(k_p) − k_p) • m_p = 0`，由 `Ξ` 的**基性**（`XiBasisHypK'`）逐项消去：

> **`N`-不变矩阵的 `Ξ`-系数是 `N`-不变纯量**（`sprFieldNFixed_of_coeff`）。

**注意（与 `deadend-coord-fixed-route.md` 的关系）**：该死胡同笔记断言"`S_n`-部分只给等变"。
本节的机检结果相反：`Ξ` 的元是 `ψ(X_{k₁})^i ψ(X_{k₂})^j`（**矩阵**），
而 `ψ_σ(X)=X`、`ψ_σ(Y_k)=Y_k` ⟹ `ψ_σ` **逐点固定** `Ξ`，故 `S_n`-半边同样给**不变**而非等变。
死胡同笔记针对的是"`φ_σ` 置换多项式变量"的读法，不是 `Ξ` 的矩阵读法。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprPsiDK_xiSprK`／`sprPsiSK_xiSprK` | `ψ_b`／`ψ_σ` 逐点固定 `Ξ` |
| ★★★★★ `sprPsiDK_xiCoordMap`／`sprPsiSK_xiCoordMap` | `ψ` 在 `Ξ`-坐标上作用为逐系数 `φ` |
| ★★★★★★★ `sprFieldNFixed_of_coeff` | **`Ξ`-系数 `N`-不变** |
| ★★★★★★★★ `sprMatNFixed_le_UDK'_of_zHalf` | **`Z` 半 ⟹ `UD` 半** |
| ★★★★★★★★★ `sprMatNFixed_le_UDK'_iff_zHalf` | **两半等价**（配 §83） |
| ★★★★★★★★★ `zEqNFixed_of_zHalf`／`h2_of_zHalf` | **终点件的「`Z` 半」条件形态**（`n = 9`、`r = 2`） |

**射程（勿夸大）**：`Z` 半（`K'^N ⊆ Z`）**未证**；PI 输入（`UDKTensorHypK'`／`XiBasisHypK'`）**未证**；
**H2 的无条件形态仍未达到**。 -/

section SprUDHalfIffZHalf

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)

/-- `ψ_b` 固定 `Ξ` 的每个元（`T`-半边）。 -/
theorem sprPsiDK_xiSprK [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (b : Fin n → Fˣ) (k₁ k₂ : Fin r) (i j : ℕ) :
    sprPsiDK F r n b (xiSprK F r n k₀ hk₀ k₁ k₂ i j)
      = xiSprK F r n k₀ hk₀ k₁ k₂ i j := by
  have h1 : ∀ k : Fin r, (sprPsiDKAlgHom F r n b)
      ((psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)))
      = (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)) :=
    fun k => sprPsiDK_fixes_psi F r n k₀ hk₀ b
      ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩
  show (sprPsiDKAlgHom F r n b) (xiSprK F r n k₀ hk₀ k₁ k₂ i j)
    = xiSprK F r n k₀ hk₀ k₁ k₂ i j
  rw [xiSprK, map_mul, map_pow, map_pow, h1, h1]

#print axioms sprPsiDK_xiSprK

/-- `ψ_σ` 固定 `Ξ` 的每个元（`S_n`-半边）。 -/
theorem sprPsiSK_xiSprK [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (σ : Equiv.Perm (Fin n)) (k₁ k₂ : Fin r) (i j : ℕ) :
    sprPsiSK F r n σ (xiSprK F r n k₀ hk₀ k₁ k₂ i j)
      = xiSprK F r n k₀ hk₀ k₁ k₂ i j := by
  have h1 : ∀ k : Fin r, (sprPsiSKAlgHom F r n σ)
      ((psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)))
      = (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
        (algebraMap (Spr F r n) (SprField F r n)) :=
    fun k => sprPsiSK_fixes_psi F r n k₀ hk₀ σ
      ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩
  show (sprPsiSKAlgHom F r n σ) (xiSprK F r n k₀ hk₀ k₁ k₂ i j)
    = xiSprK F r n k₀ hk₀ k₁ k₂ i j
  rw [xiSprK, map_mul, map_pow, map_pow, h1, h1]

#print axioms sprPsiSK_xiSprK

/-- `ψ_b` 在 `Ξ`-坐标上作用为 `φ_b`（逐系数）。 -/
theorem sprPsiDK_xiCoordMap [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) (b : Fin n → Fˣ) (k : Fin n × Fin n → SprField F r n) :
    sprPsiDK F r n b (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = xiCoordMap F r n k₀ hk₀ k₁ k₂ (fun p => sprDiagFieldEquiv F r n b (k p)) := by
  show (sprPsiDKAlgHom F r n b) (xiCoordMap F r n k₀ hk₀ k₁ k₂ k) = _
  simp only [xiCoordMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun p _ => by
    show sprPsiDK F r n b (k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2) = _
    rw [sprPsiDK_smul, sprPsiDK_xiSprK])

#print axioms sprPsiDK_xiCoordMap

/-- `ψ_σ` 在 `Ξ`-坐标上作用为 `φ_σ`（逐系数）。 -/
theorem sprPsiSK_xiCoordMap [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) (σ : Equiv.Perm (Fin n)) (k : Fin n × Fin n → SprField F r n) :
    sprPsiSK F r n σ (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)
      = xiCoordMap F r n k₀ hk₀ k₁ k₂ (fun p => sprPermFieldEquiv F r n σ (k p)) := by
  show (sprPsiSKAlgHom F r n σ) (xiCoordMap F r n k₀ hk₀ k₁ k₂ k) = _
  simp only [xiCoordMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun p _ => by
    show sprPsiSK F r n σ (k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2) = _
    rw [sprPsiSK_smul, sprPsiSK_xiSprK])

#print axioms sprPsiSK_xiCoordMap

/-- ★★★★★★★ **`N`-不变矩阵的 `Ξ`-系数是 `N`-不变纯量**（PI 输入下的结构性读法）。

`Ξ` 的每个元被 `ψ_b`／`ψ_σ` **逐点**固定（`sprPsiDK_xiSprK`／`sprPsiSK_xiSprK`），
而 `ψ_b(s·α) = φ_b(s)·ψ_b(α)`（半线性）——两者相减即得
`Σ_p (φ_b(k_p) − k_p) • m_p = 0`，由 `Ξ` 的**基性**逐项消去。 -/
theorem sprFieldNFixed_of_coeff [Nonempty (Fin n)] [NeZero n] {k₀ : Fin r} {hk₀ : k₀.val = 0}
    {k₁ k₂ : Fin r} (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (k : Fin n × Fin n → SprField F r n)
    (hfix : sprMatNFixed F r n (xiCoordMap F r n k₀ hk₀ k₁ k₂ k)) :
    ∀ p, sprFieldNFixed F r n (k p) := by
  obtain ⟨b, hb⟩ := hB
  have hzero : ∀ d : Fin n × Fin n → SprField F r n,
      xiCoordMap F r n k₀ hk₀ k₁ k₂ d = 0 → ∀ p, d p = 0 := by
    intro d hd p
    have hsum : ∑ q, d q • b q = 0 := by
      rw [← hd]
      simp only [xiCoordMap, LinearMap.coe_mk, AddHom.coe_mk]
      exact Finset.sum_congr rfl (fun q _ => by rw [hb q])
    exact Fintype.linearIndependent_iff.mp b.linearIndependent d hsum p
  intro p
  refine ⟨fun b' => ?_, fun σ => ?_⟩
  · have h := hfix.1 b'
    rw [sprPsiDK_xiCoordMap] at h
    have hd : xiCoordMap F r n k₀ hk₀ k₁ k₂
        (fun p => sprDiagFieldEquiv F r n b' (k p) - k p) = 0 := by
      have hsub : (fun p => sprDiagFieldEquiv F r n b' (k p) - k p)
          = (fun p => sprDiagFieldEquiv F r n b' (k p)) - k := rfl
      rw [hsub, map_sub, h, sub_self]
    exact sub_eq_zero.mp (hzero _ hd _)
  · have h := hfix.2 σ
    rw [sprPsiSK_xiCoordMap] at h
    have hd : xiCoordMap F r n k₀ hk₀ k₁ k₂
        (fun p => sprPermFieldEquiv F r n σ (k p) - k p) = 0 := by
      have hsub : (fun p => sprPermFieldEquiv F r n σ (k p) - k p)
          = (fun p => sprPermFieldEquiv F r n σ (k p)) - k := rfl
      rw [hsub, map_sub, h, sub_self]
    exact sub_eq_zero.mp (hzero _ hd _)

#print axioms sprFieldNFixed_of_coeff

/-- ★★★★★★★★ **`Z` 半 ⟹ `UD` 半**（`prop:14.19` 两半的反向相扣；与 §83 合起来即二者等价）。

```
(∀ x ∈ K', N-不变 ⟹ x ∈ Z)  ⟹  (∀ α, N-不变 ⟹ α ∈ UDK')
```

**证明**：PI 给 `α = xiCoordMap k`；`sprFieldNFixed_of_coeff` 给每个 `k_p ∈ K'^N`；
`Z` 半把它们搬进 `Z`；再用 `UDK'` 是 `↥Z`-子代数（`k_p • m_p = algebraMap k_p * m_p`）逐项求和。 -/
theorem sprMatNFixed_le_UDK'_of_zHalf [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂)
    (hZ : ∀ x : SprField F r n, sprFieldNFixed F r n x →
      x ∈ sprCenterImageField F r n D k₀ hk₀)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) (hα : sprMatNFixed F r n α) :
    α ∈ UDK' F r n D k₀ hk₀ := by
  classical
  obtain ⟨k, hk⟩ :=
    nfixedIsCoordHyp_of_xiBasisHypK' F r n D k₀ hk₀ hB α hα
  have hcoeff : ∀ p : Fin n × Fin n, sprFieldNFixed F r n (k p) :=
    sprFieldNFixed_of_coeff F r n hB k (by rw [hk]; exact hα)
  have hterm : ∀ p : Fin n × Fin n,
      k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 ∈ UDK' F r n D k₀ hk₀ := by
    intro p
    have hkp : k p ∈ sprCenterImageField F r n D k₀ hk₀ := hZ (k p) (hcoeff p)
    have hsm : k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2
        = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
            (Matrix (Fin n) (Fin n) (SprField F r n)) ⟨k p, hkp⟩
          * xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 := by
      ext i j
      simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.algebraMap_eq_diagonal,
        Matrix.diagonal_apply, smul_eq_mul]
    rw [hsm]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2)
  have hsum : (∑ p : Fin n × Fin n,
      k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2) ∈ UDK' F r n D k₀ hk₀ :=
    Subalgebra.sum_mem (UDK' F r n D k₀ hk₀) (fun p _ => hterm p)
  rw [← hk]
  simpa [xiCoordMap, LinearMap.coe_mk, AddHom.coe_mk] using hsum

#print axioms sprMatNFixed_le_UDK'_of_zHalf

/-- ★★★★★★★★★ **`prop:14.19` 的两半**在 PI 输入下**等价**：`UD` 半 ⟺ `Z` 半。

`⟹` 是 §83（`mem_sprCenterImageField_of_le_UDK`）；`⟸` 是上一节的新件。 -/
theorem sprMatNFixed_le_UDK'_iff_zHalf [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    (∀ α : Matrix (Fin n) (Fin n) (SprField F r n),
        sprMatNFixed F r n α → α ∈ UDK' F r n D k₀ hk₀)
      ↔ (∀ x : SprField F r n, sprFieldNFixed F r n x →
          x ∈ sprCenterImageField F r n D k₀ hk₀) := by
  constructor
  · intro hU x hx
    exact mem_sprCenterImageField_of_le_UDK F r n D k₀ hk₀ hPI hB hU hx
  · intro hZ α hα
    exact sprMatNFixed_le_UDK'_of_zHalf F r n D k₀ hk₀ hB hZ α hα

#print axioms sprMatNFixed_le_UDK'_iff_zHalf

/-- ★★★★★★★★★ **`ZEqNFixed` 的「`Z` 半」条件形态**（`n = 9`、`r = 2`）：
PI（两形态）＋ `K'^N ⊆ Z` 即可。 -/
theorem zEqNFixed_of_zHalf [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) {k₁ k₂ : Fin 2}
    (hB : XiBasisHypK' F 2 9 k₀ hk₀ k₁ k₂)
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_mem_UDK F D hk₀ hPI hB
    (fun α hα => sprMatNFixed_le_UDK'_of_zHalf F 2 9 D k₀ hk₀ hB hZ α hα)

#print axioms zEqNFixed_of_zHalf

/-- ★★★★★★★★★ **H2 的「`Z` 半」条件形态**（同上 ＋ `h2_of_ZEqNFixed`）。 -/
theorem h2_of_zHalf [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) {k₁ k₂ : Fin 2}
    (hB : XiBasisHypK' F 2 9 k₀ hk₀ k₁ k₂)
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_zHalf F D hk₀ hPI hB hZ)

#print axioms h2_of_zHalf

end SprUDHalfIffZHalf

/-! ## §88 ★★★★★ **三个具名 Prop 的数学内容只有一份**：三路等价

§66 已机检 `ThetaAgreeHypK'` ⟺ `M_n(K')^N ⊆ UDK'`；§87 机检 `UD` 半 ⟺ `Z` 半。
本节补上 `Z` 半 ⟺ `η₁ = η₂` 于 `K'^N`（配 §58 的**无条件**等化子判据），并把三路接起来：

```
ThetaAgreeHypK'  ⟺  M_n(K')^N ⊆ UDK'  ⟺  K'^N ⊆ Z  ⟺  (η₁ = η₂ 于 K'^N)
```

⟹ **剩余数学只有一份**。（PI 的两个形态 `UDKTensorHypK'`／`XiBasisHypK'` 是**独立输入**，
不在本节的等价环里。）

| 件 | 内容 |
|---|---|
| ★★★★★ `etaAgree_of_zHalf`／`zHalf_of_etaAgree` | `Z` 半 ⟺ `η₁ = η₂` 于 `K'^N` |
| ★★★★★★ `sprMatNFixed_le_UDK'_iff_etaAgree` | `UD` 半 ⟺ 等化子形态 |
| ★★★★★★★ `thetaAgreeHypK'_iff_zHalf` | **`ThetaAgreeHypK'` ⟺ `Z` 半** |

**射程（勿夸大）**：`K'^N ⊆ Z` **未证**；PI **未证**；**H2 见文件头「当前状态」。** -/

section SprThreeWayEquivalence

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **`Z` 半 ⟹ `η₁ = η₂` 在 `K'^N` 上**。 -/
theorem etaAgree_of_zHalf [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hZ : ∀ x : SprField F r n, sprFieldNFixed F r n x →
      x ∈ sprCenterImageField F r n D k₀ hk₀) :
    ∀ x : SprField F r n, sprFieldNFixed F r n x →
      etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x :=
  fun x hx => etaSprK1_eq_etaSprK2_of_mem F r n D k₀ hk₀ (hZ x hx)

#print axioms etaAgree_of_zHalf

/-- ★★★★★ **`η₁ = η₂` 在 `K'^N` 上 ⟹ `Z` 半**（等化子判据，§58 无条件）。 -/
theorem zHalf_of_etaAgree [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hη : ∀ x : SprField F r n, sprFieldNFixed F r n x →
      etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x) :
    ∀ x : SprField F r n, sprFieldNFixed F r n x →
      x ∈ sprCenterImageField F r n D k₀ hk₀ :=
  fun x hx => mem_sprCenterImageField_of_eta_eq F r n D k₀ hk₀ (hη x hx)

#print axioms zHalf_of_etaAgree

/-- ★★★★★★★ **`Z` 半 ⟺ `η₁ = η₂` 在 `K'^N` 上**。 -/
theorem zHalf_iff_etaAgree [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (∀ x : SprField F r n, sprFieldNFixed F r n x →
        x ∈ sprCenterImageField F r n D k₀ hk₀)
      ↔ ∀ x : SprField F r n, sprFieldNFixed F r n x →
          etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x :=
  ⟨etaAgree_of_zHalf F r n D k₀ hk₀, zHalf_of_etaAgree F r n D k₀ hk₀⟩

#print axioms zHalf_iff_etaAgree

/-- ★★★★★ **`UD` 半 ⟺ `η₁ = η₂` 在 `K'^N` 上**（§87 ＋ §58）。 -/
theorem sprMatNFixed_le_UDK'_iff_etaAgree [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    (∀ α : Matrix (Fin n) (Fin n) (SprField F r n),
        sprMatNFixed F r n α → α ∈ UDK' F r n D k₀ hk₀)
      ↔ ∀ x : SprField F r n, sprFieldNFixed F r n x →
          etaSprK1 F r n D k₀ hk₀ x = etaSprK2 F r n D k₀ hk₀ x := by
  rw [← zHalf_iff_etaAgree F r n D k₀ hk₀]
  exact sprMatNFixed_le_UDK'_iff_zHalf F r n D k₀ hk₀ hPI hB

#print axioms sprMatNFixed_le_UDK'_iff_etaAgree

/-- ★★★★★★★★★ **三路等价**：`ThetaAgreeHypK'` ⟺ `UD` 半 ⟺ `Z` 半。

⟹ 三个具名 Prop 的**数学内容只有一份**（`prop:14.19` 的两半），只是三个等价外形。
（PI 的两个形态 `UDKTensorHypK'`／`XiBasisHypK'` 仍是独立输入。） -/
theorem thetaAgreeHypK'_iff_zHalf [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    ThetaAgreeHypK' F r n D k₀ hk₀ hPI ↔
      ∀ x : SprField F r n, sprFieldNFixed F r n x →
        x ∈ sprCenterImageField F r n D k₀ hk₀ := by
  rw [thetaAgreeHypK'_iff F r n D k₀ hk₀ hPI hB]
  exact sprMatNFixed_le_UDK'_iff_zHalf F r n D k₀ hk₀ hPI hB

#print axioms thetaAgreeHypK'_iff_zHalf

end SprThreeWayEquivalence

/-! ## §89 ★★★★★ **PI 输入（`XiBasisHypK'`）的具体路线** —— 第 1 步：条目分解

源文 `lem:14.7` 级的内容（`Ξ = {X^i Y^j}_{i,j<n}` 是 `K'`-基）。旧估"5–15 轮"，
第 470 轮找到**具体路线**（不再走抽象 PI 论），本节是其第 1 步。

**路线（四步，逐步可机检）**：
1. **分组**：`X = diag(x_11..x_nn)` 对角 ⟹ `X^i` 对角，`Σ_i c_{ij}X^i = diag(Σ_i c_{ij}x_p^i)`。
2. **取条目**（本节）：`(Σ_{i,j} c_{ij}X^iY^j)_{pq} = Σ_j (Σ_i c_{ij}x_p^i)(Y^j)_{pq}`。
3. **`M_p` 可逆**（下一轮）：`M_p := ((Y^j)_{pq})_{j,q}` 的 `det` 是 `y`-多项式；
   取 `Y =` 循环移位置换矩阵 `S`（`(S^j)_{p,p+j}=1`）代入 ⟹ `M_p` 成**置换矩阵**
   ⟹ `det = ±1 ≠ 0` ⟹ `det M_p ≠ 0` ⟹（`K'` 是域）可逆。
4. **Vandermonde 收口**（下一轮）：`d_p = 0` ⟹ `Σ_i c_{ij}x_p^i = 0` 对 `p = 1..n`；
   `K'[T]` 中次数 `≤ n−1` 的多项式有 `n` 个**互异**根 ⟹ `f_j = 0` ⟹ `c_{ij} = 0`。

**为何可行**：第 3 步是**置换矩阵行列式**的具体计算，第 4 步是"根多于次数 ⟹ 零"。
⟹ **代价重估 2–4 轮**。已机检的便宜半边：§39 的 `sprXdiagK_linearIndependent`（`j = 0` 层）。

**射程（勿夸大）**：本节只有第 2 步（条目分解）。第 3／4 步**未做**；
`XiBasisHypK'`／`Z` 半（`K'^N ⊆ Z`）**均未证**；**H2 见文件头「当前状态」。** -/

section SprPiRoute

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- ★★★★★ **条目分解**（PI 路线第 1–2 步）：`Σ_{i,j} c_{ij} X^iY^j` 的 `(p,q)` 项
＝ `Σ_j (Σ_i c_{ij} x_p^i) (Y^j)_{pq}`。

**用途**：把 `Ξ` 的线性无关性化为**逐 `p` 的 `n×n` 矩阵** `M_p := ((Y^j)_{pq})_{j,q}`
的可逆性（§89 节头第 3 步）。 -/
theorem sprXi_entry_decomp (x : Fin n → SprField F r n)
    (Y : Matrix (Fin n) (Fin n) (SprField F r n))
    (c : Fin n × Fin n → SprField F r n) (p q : Fin n) :
    (∑ t : Fin n × Fin n, c t • ((Matrix.diagonal x) ^ (t.1 : ℕ) * Y ^ (t.2 : ℕ))) p q
      = ∑ j : Fin n, (∑ i : Fin n, c (i, j) * (x p) ^ (i : ℕ)) * (Y ^ (j : ℕ)) p q := by
  classical
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_pow, Matrix.diagonal_mul, Pi.pow_apply,
      mul_assoc])

#print axioms sprXi_entry_decomp

end SprPiRoute

/-! ## §90 ★★★★★★★ **PI 输入（`XiBasisHypK'`）第 3–4 步**：核提取 ＋ Vandermonde 收口

§89 给了条目分解（`Σ_{i,j} c_{ij}X^iY^j` 的 `(p,q)` 项）。本节把 §89 节头路线的**第 3–4 步**
在**条件形态**下机检：给定"每个 `M_p := ((Y^j)_{pq})_{j,q}` 可逆"＋"`x` 互异"，则
`{X^iY^j}_{i,j<n}` **线性无关**（`X = diag x`）。

**机制（三步）**：
1. `det ≠ 0` ⟹ `M *ᵥ v = 0 → v = 0`（`sprMulVec_eq_zero_of_det_ne_zero`，
   mathlib 的 `Matrix.exists_mulVec_eq_zero_iff`）；
2. 由条目分解，`Σ_{i,j} c_{ij}X^iY^j = 0` 对每个 `p` 给出 **`M_pᵀ *ᵥ d_p = 0`**，
   其中 `d_p[j] = Σ_i c_{ij} x_p^i` ⟹ **`d_p = 0`**（`sprXi_kernel_coeff_zero`）；
3. 固定 `j`：`K'[T]` 中次数 `≤ n−1` 的多项式 `Σ_i c_{ij}T^i` 有 `n` 个互异根 `x_p`
   ⟹ 系数全零（**Vandermonde**：`Matrix.vandermonde` 的 `det ≠ 0` ⟹ 同一核提取）
   （`sprXi_linearIndependent_of_det`）。

**⟹ 剩余只有一步**：把 `hY`（`M_p` 可逆）在**具体** `Y = ymat` 上落实——路线见 §89 节头第 3 步
（取 `Y =` 循环移位矩阵 ⟹ `M_p` 成置换矩阵 ⟹ `det = ±1`）。**该步本节未做**。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprMulVec_eq_zero_of_det_ne_zero` | `det ≠ 0` ⟹ 核为零 |
| ★★★★★★ `sprXi_kernel_coeff_zero` | **核提取**：`d_p = 0` |
| ★★★★★★★ `sprXi_linearIndependent_of_det` | **线性无关性归约**（Vandermonde 收口） |

**已机检的配套件**（勿重做）：`sprDiagVal_injective`／`sprDiagVandermonde_det_ne_zero`（§39）。

**射程（勿夸大）**：本节是**条件形态**——`hY` **未证**，故 `XiBasisHypK'` **仍未证**；
`Z` 半（`K'^N ⊆ Z`／`SFixedLeZ`）**未证**；**H2 见文件头「当前状态」。** -/

section SprPiRoute2

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)


/-- `det ≠ 0` ⟹ 核为零（`M *ᵥ v = 0 → v = 0`）。 -/
theorem sprMulVec_eq_zero_of_det_ne_zero {M : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hM : M.det ≠ 0) {v : Fin n → SprField F r n} (hv : M *ᵥ v = 0) : v = 0 := by
  classical
  by_contra h
  exact hM ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨v, h, hv⟩)

#print axioms sprMulVec_eq_zero_of_det_ne_zero

/-- PI 路线第 3 步的**核提取**：若 `Σ_{i,j} c_{ij} X^iY^j = 0` 且每个 `M_p := ((Y^j)_{pq})_{j,q}`
可逆，则每个 `p` 处的系数向量 `(Σ_i c_{ij} x_p^i)_j` 为零。 -/
theorem sprXi_kernel_coeff_zero
    (x : Fin n → SprField F r n) (Y : Matrix (Fin n) (Fin n) (SprField F r n))
    (c : Fin n × Fin n → SprField F r n)
    (hY : ∀ p, (Matrix.of (fun (jj : Fin n) (q : Fin n) => (Y ^ (jj : ℕ)) p q)).det ≠ 0)
    (h0 : ∑ t : Fin n × Fin n,
      c t • ((Matrix.diagonal x) ^ (t.1 : ℕ) * Y ^ (t.2 : ℕ)) = 0)
    (p : Fin n) (j : Fin n) :
    ∑ i : Fin n, c (i, j) * (x p) ^ (i : ℕ) = 0 := by
  classical
  have hentry : ∀ q, ∑ jj : Fin n, (∑ i : Fin n, c (i, jj) * (x p) ^ (i : ℕ)) * (Y ^ (jj : ℕ)) p q = 0 := by
    intro q
    have h := congrFun (congrFun h0 p) q
    rw [Matrix.zero_apply, sprXi_entry_decomp] at h
    exact h
  have hmv : (Matrix.of (fun (jj : Fin n) (q : Fin n) => (Y ^ (jj : ℕ)) p q)).transpose *ᵥ
      (fun jj : Fin n => ∑ i : Fin n, c (i, jj) * (x p) ^ (i : ℕ)) = 0 := by
    funext q
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply]
    rw [show (∑ jj : Fin n, (Y ^ (jj : ℕ)) p q * (∑ i : Fin n, c (i, jj) * (x p) ^ (i : ℕ)))
        = ∑ jj : Fin n, (∑ i : Fin n, c (i, jj) * (x p) ^ (i : ℕ)) * (Y ^ (jj : ℕ)) p q from
      Finset.sum_congr rfl (fun jj _ => mul_comm _ _)]
    exact hentry q
  have hdet : (Matrix.of (fun (jj : Fin n) (q : Fin n) => (Y ^ (jj : ℕ)) p q)).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hY p
  exact congrFun (sprMulVec_eq_zero_of_det_ne_zero F r n hdet hmv) j

#print axioms sprXi_kernel_coeff_zero

/-- ★★★★★★★ **PI 路线第 3–4 步收口**：若每个 `M_p := ((Y^j)_{pq})_{j,q}` 可逆、且 `x` 互异，
则 `{X^i Y^j}_{i,j<n}`（`X = diag x`）**线性无关**。 -/
theorem sprXi_linearIndependent_of_det {x : Fin n → SprField F r n} (hx : Function.Injective x)
    (Y : Matrix (Fin n) (Fin n) (SprField F r n))
    (hY : ∀ p, (Matrix.of (fun (jj : Fin n) (q : Fin n) => (Y ^ (jj : ℕ)) p q)).det ≠ 0) :
    LinearIndependent (SprField F r n)
      (fun t : Fin n × Fin n => (Matrix.diagonal x) ^ (t.1 : ℕ) * Y ^ (t.2 : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c h0 p
  obtain ⟨i, j⟩ := p
  have hcoef : ∀ p' : Fin n, ∑ i' : Fin n, c (i', j) * (x p') ^ (i' : ℕ) = 0 :=
    fun p' => sprXi_kernel_coeff_zero F r n x Y c hY h0 p' j
  have hdet : (Matrix.vandermonde x).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    exact hx
  have hmv : Matrix.vandermonde x *ᵥ (fun i' : Fin n => c (i', j)) = 0 := by
    funext p'
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [show (∑ i' : Fin n, x p' ^ (i' : ℕ) * c (i', j))
        = ∑ i' : Fin n, c (i', j) * (x p') ^ (i' : ℕ) from
      Finset.sum_congr rfl (fun i' _ => mul_comm _ _)]
    exact hcoef p'
  exact congrFun (sprMulVec_eq_zero_of_det_ne_zero F r n hdet hmv) i

#print axioms sprXi_linearIndependent_of_det

end SprPiRoute2

/-! ## §91 ★★★★★ **PI 的 `hY`：置换矩阵落点**（专门化的目标形态已机检）

§90 把 `hY`（`∀ p, (M_p).det ≠ 0`，`M_p := ((Y^j)_{pq})_{j,q}`）作为唯一剩余条件。
本节给出它的**专门化落点**：循环移位矩阵 `S` 的幂在任一固定行上是**置换矩阵**。

```
S i q = 1 ⟺ q = i + 1        （Fin n 的加法，[NeZero n]）
M_p j q = 1 ⟺ q = p + j       （S^j 的第 p 行）
M_p * (M_p)⁻¹ = 1 ⟹ det M_p ≠ 0
```

| 件 | 内容 |
|---|---|
| `sprShiftMat`／`sprPermMat`／`sprPermMatInv` | `S`、`M_p`、`M_p` 的显式逆 |
| ★★★★★ `sprPermMat_mul_inv` | `M_p * M_p⁻¹ = 1` |
| ★★★★★ `sprPermMat_det_ne_zero` | **`det M_p ≠ 0`** |

**⟹ `hY` 的剩余是"把 `Y` 专门化到 `S`"**：即证 `(S^j) p q = (M_p) j q`
（幂公式）＋ 沿 `MvPolynomial.aeval`（`y_ijk ↦ S i j`）把多项式行列式压过去
（`RingHom.map_det` ＋ `Matrix.map_pow`），再由 `algebraMap` 单射搬回 `K'`。
**该两步本节未做**（第 473 轮实测：幂公式写成**矩阵等式**再 `Matrix.ext` 可行，
但 `Matrix` 的应用展开在 `simp` 里需要显式带上 `Matrix.of_apply`／`Matrix.one_apply`
与 `sprShiftMat` 三件，缺一即 "function expected"）。

**射程（勿夸大）**：本节只给**落点**；`hY`／`XiBasisHypK'`／`SFixedLeZ` **均未证**；**H2 见文件头「当前状态」。** -/

section SprPiRoutePerm

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable {F : Type} [Field F] {n : ℕ} [NeZero n]

/-- 循环移位矩阵 `S`：`S i q = 1` 当且仅当 `q = i + 1`。 -/
def sprShiftMat : Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun i q => if q = i + 1 then (1 : F) else 0)

#print axioms sprShiftMat


/-- 置换矩阵 `M_p`：`(M_p) j q = 1 ⟺ q = p + j`（`S^j` 的第 `p` 行）。 -/
def sprPermMat (p : Fin n) : Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun (j q : Fin n) => if q = p + j then (1 : F) else 0)

#print axioms sprPermMat


theorem sprOfNat_zero : (Fin.ofNat n 0 : Fin n) = 0 := by
  ext; simp [Fin.ofNat]

#print axioms sprOfNat_zero


theorem sprOfNat_succ (m : ℕ) : (Fin.ofNat n (m + 1) : Fin n) = Fin.ofNat n m + 1 := by
  ext; simp [Fin.ofNat, Fin.val_add]

#print axioms sprOfNat_succ


/-- 置换矩阵的**逆**（`q = p + j` 形态）。 -/
def sprPermMatInv (p : Fin n) : Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun (q j : Fin n) => if q = p + j then (1 : F) else 0)

#print axioms sprPermMatInv


theorem sprPermMat_mul_inv (p : Fin n) :
    sprPermMat (F := F) (n := n) p * sprPermMatInv (F := F) (n := n) p = 1 := by
  ext j j'
  simp only [Matrix.mul_apply, sprPermMat, sprPermMatInv, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (p + j)]
  · by_cases h : j = j'
    · subst h
      rw [if_pos rfl, if_pos rfl, one_mul]
    · have h' : ¬ p + j = p + j' := fun hh => h (add_left_cancel hh)
      rw [if_pos rfl, if_neg h', if_neg h, one_mul]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

#print axioms sprPermMat_mul_inv

/-- ★★★★★ **置换矩阵的行列式非零**（`hY` 的专门化落点）。 -/
theorem sprPermMat_det_ne_zero (p : Fin n) :
    (sprPermMat (F := F) (n := n) p).det ≠ 0 := by
  have h := congrArg Matrix.det (sprPermMat_mul_inv (F := F) (n := n) p)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

#print axioms sprPermMat_det_ne_zero

end SprPiRoutePerm

/-! ## §92 ★★★★★★ **`hY` 的通用落点**：任意置换矩阵 `det ≠ 0` ＋ 幂公式（mathlib API）

第 473 轮走"自造循环移位矩阵 ＋ 按条目归纳"卡在 `Matrix` 的应用展开上；
第 474 轮的 **TauCeti 定向侦察**（L46，[[proj-tauceti-recon-2026-10-20]]）顺带查出
**mathlib 早已有完整的置换矩阵 API**，且 pin 上就有：

| 件 | 内容 |
|---|---|
| `Equiv.Perm.permMatrix` | 置换矩阵（`PEquiv.toMatrix`，条目式 `toMatrix_apply` 可读） |
| `Matrix.permMatrixHom : Perm n →* Matrix n n R` | **打包成幺半群同态** |
| `Matrix.det_permutation` | `det (σ.permMatrix R) = Equiv.Perm.sign σ` |

⟹ 本节把 `hY` 的**落点一般化**：对**任意** `σ`，`(σ.permMatrix F).det ≠ 0`；
且**幂公式免费**（`permMatrixHom` 的 `map_pow`）。**§91 的 `sprShiftMat` 归纳整段可弃**（保留不动）。

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprPermMatrix_det_ne_zero` | **任意置换矩阵 `det ≠ 0`**（`sign` 是 `ℤˣ` 的单位） |
| ★★★★★★ `sprPermMatrixHom_pow` | **`(permMatrixHom σ)^m = permMatrixHom (σ^m)`** |

**⟹ `hY` 的剩余**：只需把 `Y` 专门化到"**对合** `j ↦ p - j` 的 `permMatrix`"
（`Function.Involutive.toPerm`，**无需循环／orbit 论证**），再用 `MvPolynomial.aeval`
＋ `RingHom.map_det` ＋ `IsFractionRing.injective` 搬到 `Spr`／`K'`。

**射程（勿夸大）**：本节只给**通用落点**；`hY`／`XiBasisHypK'`／`SFixedLeZ` **均未证**；**H2 见文件头「当前状态」。** -/

section SprPermMatrixGeneric

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable {F : Type} [Field F] {n : ℕ}

/-- ★★★★★★ **任意置换矩阵的行列式非零**（mathlib `det_permutation` ＋ `Perm.sign` 是单位）。 -/
theorem sprPermMatrix_det_ne_zero (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix F).det ≠ 0 := by
  rw [Matrix.det_permutation]
  refine IsUnit.ne_zero ?_
  simpa using (Units.isUnit (Equiv.Perm.sign σ)).map (Int.castRingHom F)

#print axioms sprPermMatrix_det_ne_zero

/-- ★★★★★★ **置换矩阵同态的幂公式**（`permMatrixHom` 是幺半群同态）。 -/
theorem sprPermMatrixHom_pow (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    (Matrix.permMatrixHom (n := Fin n) (R := F) σ) ^ m
      = Matrix.permMatrixHom (n := Fin n) (R := F) (σ ^ m) :=
  (map_pow _ σ m).symm

#print axioms sprPermMatrixHom_pow

end SprPermMatrixGeneric

/-! ## §93 ★★★★★ **`Equiv.addRight` 的幂公式**（mathlib 缺件；`hY` 专门化的最后一块拼图）

`hY` 需要把 `Y` 专门化到**循环移位**（使**每个** `p` 的 `M_p` 都成置换矩阵）。
第 474 轮查出 mathlib 有 `Matrix.permMatrixHom`（§92）与 `det_permutation`，
但**没有** `Equiv.addRight`（加法平移置换）的幂公式——本节补上：

```
(Equiv.addRight a : Equiv.Perm (Fin n)) ^ m  =  Equiv.addRight (m • a)
```

**用途**（`hY` 的完整链路，下一轮）：
`(permMatrixHom (Equiv.addRight a))^m = (Equiv.addRight (m • a)).permMatrix`
（本节 ＋ §92 的 `permMatrixHom_pow`），于是
`((S^j)) p q = [q = p + j]`（对 `a = 1`）——**逐 `p` 都是置换矩阵**，`det = ±1 ≠ 0`。
这正好绕开第 473 轮"按条目归纳"的障碍（那一版卡在 `Matrix` 的应用展开上）。

**工艺**：`ext x` 之后目标是 `Fin.val` 层的等式，`abel` 看不到强制转换 ⟹ 须先 `congr 1`
把目标降回 `Fin n` 层，再 `abel`。

**射程（勿夸大）**：本节只是**幂公式**；`hY`／`XiBasisHypK'`／`SFixedLeZ` **均未证**；**H2 见文件头「当前状态」。** -/

section SprAddRightPow

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

/-- `Fin n` 的加法平移置换：`Equiv.addRight a` 的幂公式（mathlib 无此件）。 -/
theorem sprAddRight_pow {n : ℕ} [NeZero n] (a : Fin n) (m : ℕ) :
    (Equiv.addRight a : Equiv.Perm (Fin n)) ^ m = Equiv.addRight (m • a) := by
  induction m with
  | zero => ext x; simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext x
    simp only [Equiv.coe_addRight, Function.comp_apply, Equiv.Perm.coe_mul, succ_nsmul]
    congr 1
    abel

#print axioms sprAddRight_pow

end SprAddRightPow

/-! ## §94 ★★★★★ **平移置换矩阵的条目公式**（`hY` 搬移步的目标形态）

`hY` 的搬移步要把 `Y` 专门化到"循环移位"并读出 `((S^j)) p q = [q = p + j]`。
§93 给了 `addRight` 的幂公式、§92 给了 `permMatrixHom` 的幂公式与 `det ≠ 0`；
本节补上**条目公式**（目标形态的最后一格）：

```
(addRight p).permMatrix i q = 1  ⟺  q = i + p
(addLeft  p).permMatrix i q = 1  ⟺  q = p + i
```

**⟹ `hY` 搬移步的全部零件已齐**（下一轮装配）：
`Y := ymat` ⟹ `Φ := MvPolynomial.aeval`（`y_ijk ↦ S i j`，`S := permMatrixHom (addRight (-1))`）
⟹ `(M_p).map Φ = (addLeft p).permMatrix` ⟹ `det ≠ 0`（§92）
⟹ 回 `Spr`（`RingHom.map_det`）⟹ 回 `K'`（`IsFractionRing.injective`）。

**工艺**：`PEquiv.toMatrix_apply` 给的是 `Option` 成员式 `q ∈ f i`，须
`simp only [Option.mem_def, Option.some.injEq]` 降成 `f i = q`；末了两侧 `if` 的
**方向相反**（`p + i = q` vs `q = p + i`）⟹ 用 `if_pos hq.symm`／`if_neg (fun hh => hq hh.symm)`。

**射程（勿夸大）**：本节只有条目公式；`hY`／`XiBasisHypK'`／`SFixedLeZ` **均未证**；**H2 见文件头「当前状态」。** -/

section SprPermMatrixApply

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

/-- 平移置换矩阵的条目公式：`(addLeft p).permMatrix i q = 1 ⟺ q = p + i`。 -/
theorem sprPermMatrix_addLeft_apply {F : Type} [Field F] {n : ℕ} [NeZero n]
    (p i q : Fin n) :
    ((Equiv.addLeft p : Equiv.Perm (Fin n)).permMatrix F) i q
      = if q = p + i then (1 : F) else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  have h : (Equiv.addLeft p : Equiv.Perm (Fin n)).toPEquiv i = some (Equiv.addLeft p i) := rfl
  rw [h]
  simp only [Option.mem_def, Option.some.injEq, Equiv.coe_addLeft]
  by_cases hq : p + i = q
  · rw [if_pos hq, if_pos hq.symm]
  · rw [if_neg hq, if_neg (fun hh => hq hh.symm)]

#print axioms sprPermMatrix_addLeft_apply

/-- 右平移置换矩阵的条目公式：`(addRight p).permMatrix i q = 1 ⟺ q = i + p`。 -/
theorem sprPermMatrix_addRight_apply {F : Type} [Field F] {n : ℕ} [NeZero n]
    (p i q : Fin n) :
    ((Equiv.addRight p : Equiv.Perm (Fin n)).permMatrix F) i q
      = if q = i + p then (1 : F) else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  have h : (Equiv.addRight p : Equiv.Perm (Fin n)).toPEquiv i = some (Equiv.addRight p i) := rfl
  rw [h]
  simp only [Option.mem_def, Option.some.injEq, Equiv.coe_addRight]
  by_cases hq : i + p = q
  · rw [if_pos hq, if_pos hq.symm]
  · rw [if_neg hq, if_neg (fun hh => hq hh.symm)]

#print axioms sprPermMatrix_addRight_apply

end SprPermMatrixApply

/-! ## §95 ★★★★★★★ **移位幂公式拿下**（`hY` 的核心；第 473 轮归纳失败的同一命题）

第 473 轮试图**按条目归纳**证 `(S^m) i q = [q = i + m]`（`S` 为循环移位矩阵），卡在
`Matrix` 的应用展开上（"function expected"）。第 474 轮 TauCeti 侦察查出 mathlib 的
`permMatrixHom`（§92）后，本节用 **同态 ＋ 平移置换** 把同一条幂公式**不经归纳**地拿下：

```
(permMatrixHom (addRight (-1)))^j  的第 p 行  =  [q = p + j]
```

**证明链（四步，全部机检件）**：
1. `sprPermMatrixHom_pow`（§92）：`(permMatrixHom σ)^j = permMatrixHom (σ^j)`；
2. `sprAddRight_pow`（§93）：`(addRight a)^j = addRight (j • a)`；
3. `sprAddRight_inv` ＋ `sprNsmul_one_fin`（本节）：`-(j • (-1)) = j`
   （经 `smul_neg`／`neg_neg`／`m • 1 = Fin.ofNat n m` ＋ `Fin.ofNat n (j:ℕ) = j`）；
4. `sprPermMatrix_addRight_apply`（§94）：`(addRight p).permMatrix i q = [q = i + p]`。

**⟹ `hY` 只剩"搬移"**：`(M_p).map Φ = (addLeft p).permMatrix`
（条目式即本节公式；`Fin` 加法可交换）⟹ `det ≠ 0`（§92）⟹ 回 `Spr`（`RingHom.map_det`）
⟹ 回 `K'`（`IsFractionRing.injective`）。

| 件 | 内容 |
|---|---|
| `sprAddRight_inv` | `(addRight a)⁻¹ = addRight (-a)` |
| ★★★ `sprNsmul_one_fin` | **`m • (1 : Fin n) = Fin.ofNat n m`**（mathlib 缺件） |
| `sprOfNat_coe` | `Fin.ofNat n (j:ℕ) = j` |
| ★★★★★★★ `sprShiftPow_apply` | **移位幂公式**（`hY` 的核心） |

**射程（勿夸大）**：本节给**幂公式**；`hY` 的搬移步（`aeval`）**未做**；
`XiBasisHypK'`／`SFixedLeZ`／`K'^N ⊆ Z` **均未证**；**H2 见文件头「当前状态」。** -/

section SprShiftPow

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable {F : Type} [Field F] {n : ℕ} [NeZero n]

/-- `addRight a` 的逆是 `addRight (-a)`。 -/
theorem sprAddRight_inv (a : Fin n) :
    (Equiv.addRight a : Equiv.Perm (Fin n))⁻¹ = Equiv.addRight (-a) := by
  ext x
  simp [Equiv.addRight]

#print axioms sprAddRight_inv

/-- `m • (1 : Fin n) = Fin.ofNat n m`（`§91` 的 `sprOfNat_succ` 的伴随件）。 -/
theorem sprNsmul_one_fin (m : ℕ) : m • (1 : Fin n) = Fin.ofNat n m := by
  induction m with
  | zero => simp [Fin.ofNat]
  | succ k ih => rw [succ_nsmul, ih, sprOfNat_succ]

#print axioms sprNsmul_one_fin

/-- `Fin.ofNat n (j : ℕ) = j`。 -/
theorem sprOfNat_coe (j : Fin n) : (Fin.ofNat n (j : ℕ) : Fin n) = j := by
  ext; simp [Fin.ofNat, Nat.mod_eq_of_lt j.isLt]

#print axioms sprOfNat_coe

/-- ★★★★★ **移位幂公式**：`(permMatrixHom (addRight (-1)))^j` 的第 `p` 行是 `[q = p + j]`。 -/
theorem sprShiftPow_apply (j p q : Fin n) :
    ((Matrix.permMatrixHom (n := Fin n) (R := F) (Equiv.addRight (-1))) ^ (j : ℕ)) p q
      = if q = p + j then (1 : F) else 0 := by
  rw [sprPermMatrixHom_pow, sprAddRight_pow, Matrix.permMatrixHom_apply, sprAddRight_inv]
  rw [show -((j : ℕ) • (-1 : Fin n)) = j from by
    rw [smul_neg, neg_neg, sprNsmul_one_fin, sprOfNat_coe]]
  rw [sprPermMatrix_addRight_apply]

#print axioms sprShiftPow_apply

end SprShiftPow

/-! ## §96 ★★★★★★★★★ **`hY` 完成**：`Y`-幂矩阵的行列式非零（`Spr` 层 ＋ `K'` 层）

§90 把 PI 的全部内容压到唯一条件 `hY`；§92–§95 备齐了置换矩阵的幂公式与条目公式。
本节把 `hY` **证完**：

```
M_p := ((Y^j)_{p,q})_{j,q}         Y = (ymat k) 沿 algebraMap 的像
(M_p).det ≠ 0                       （先证于 Spr，再下沉到 K'）
```

**证明（"专门化 － 行列式交换 － 注入"三步）**：
1. 定义 `Φ := MvPolynomial.aeval sprSpecPerm`（`x_ii ↦ 0`、`y_ijk ↦ S i j`，
   `S := permMatrixHom (addRight (-1))`）；
2. `(M_p).map Φ = (addLeft p).permMatrix`（`Matrix.map_pow` ＋ §95 幂公式 ＋ §94 条目公式）
   ⟹ `det ≠ 0`（§92）；
3. `Φ((M_p).det) = ((M_p).map Φ).det`（`RingHom.map_det`）⟹ `(M_p).det ≠ 0`（`Spr` 层）；
4. 沿 `algebraMap` 下沉：`algebraMap((M_p).det) = ((M_p).map algebraMap).det`，
   而 `algebraMap` 单射（`IsFractionRing.injective`）⟹ `K'` 层 `det ≠ 0`。

| 件 | 内容 |
|---|---|
| `sprSpecPerm`／`sprSpecPhi` | 专门化数据与映射 |
| `sprSpecPhi_X_inl`／`_X_inr` | 变量上的取值 |
| ★★★★★★ `sprSpecPhi_ymat` | **`Φ(ymat k) = permMatrixHom (addRight (-1))`** |
| ★★★★★★★ `sprYmat_powMat_map_spec` | **`(M_p).map Φ = (addLeft p).permMatrix`** |
| ★★★★★★★★ `sprYmat_powMat_det_ne_zero` | **`hY`（`Spr` 层）** |
| ★★★★★★★★★ `sprY_powMat_det_ne_zero` | **`hY`（`K'` 层，§90 所需形态）** |

**工艺（两处实测）**：① `RingHom.map_det` 的右端是 `f.mapMatrix M`（不是 `M.map ⇑f`）⟹
须走 `calc`：`algebraMap d = (M.map f).det = (目标).det`；② `.map ⇑f` 上的 `Matrix.map_pow`
不能直接 `rw`（应用展开问题，R274 同族）⟹ 用
`congrFun (congrFun (Matrix.map_pow M f j) p) q` 拿到**应用形态**。

**射程（勿夸大）**：本节给 **`hY` 本身**；由 §90 即得 `{X^iY^j}` 的线性无关性
（`XiBasisHypK'` 的一半）。`XiBasisHypK'` 的**张成**、`SFixedLeZ`／`K'^N ⊆ Z` **仍待**；
**H2 仍为条件化定理**。 -/

section SprHY

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ) [NeZero n]

/-- 专门化：`x_ii ↦ 0`、`y_ijk ↦ S i j`（`S := permMatrixHom (addRight (-1))`）。 -/
noncomputable def sprSpecPerm : SprIdx r n → F :=
  Sum.elim (fun _ => 0)
    (fun ijk => (Matrix.permMatrixHom (n := Fin n) (R := F) (Equiv.addRight (-1))) ijk.1 ijk.2.1)

#print axioms sprSpecPerm

/-- `Φ := MvPolynomial.aeval sprSpecPerm`。 -/
noncomputable def sprSpecPhi : Spr F r n →ₐ[F] F :=
  MvPolynomial.aeval (sprSpecPerm F r n)

#print axioms sprSpecPhi

theorem sprSpecPhi_X_inl (i : Fin n) : sprSpecPhi F r n (MvPolynomial.X (Sum.inl i)) = 0 := by
  simp [sprSpecPhi, sprSpecPerm, MvPolynomial.aeval_X]

#print axioms sprSpecPhi_X_inl

theorem sprSpecPhi_X_inr (ijk : YIdx r n) :
    sprSpecPhi F r n (MvPolynomial.X (Sum.inr ijk))
      = (Matrix.permMatrixHom (n := Fin n) (R := F) (Equiv.addRight (-1))) ijk.1 ijk.2.1 := by
  simp [sprSpecPhi, sprSpecPerm, MvPolynomial.aeval_X]

#print axioms sprSpecPhi_X_inr

theorem sprSpecPhi_ymat (k : {k : Fin r // k.val ≠ 0}) :
    (ymat F r n k).map (sprSpecPhi F r n)
      = (Matrix.permMatrixHom (n := Fin n) (R := F) (Equiv.addRight (-1))) := by
  ext i j
  simp only [Matrix.map_apply, ymat, sprSpecPhi_X_inr]

#print axioms sprSpecPhi_ymat

/-- `(M_p).map Φ = (addLeft p).permMatrix`：搬移步的核心恒等式。 -/
theorem sprYmat_powMat_map_spec (k : {k : Fin r // k.val ≠ 0}) (p : Fin n) :
    (Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).map (sprSpecPhi F r n)
      = (Equiv.addLeft p : Equiv.Perm (Fin n)).permMatrix F := by
  have h1 : (Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).map
        (sprSpecPhi F r n)
      = Matrix.of (fun (j q : Fin n) =>
          (((ymat F r n k).map (sprSpecPhi F r n)) ^ (j : ℕ)) p q) := by
    ext j q
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact congrFun (congrFun (Matrix.map_pow (ymat F r n k)
      (sprSpecPhi F r n).toRingHom (j : ℕ)) p) q
  have h2 : Matrix.of (fun (j q : Fin n) =>
        (((Matrix.permMatrixHom (n := Fin n) (R := F) (Equiv.addRight (-1))) ^ (j : ℕ)) p q))
      = (Equiv.addLeft p : Equiv.Perm (Fin n)).permMatrix F := by
    ext j q
    rw [Matrix.of_apply, sprShiftPow_apply, sprPermMatrix_addLeft_apply]
  rw [h1, sprSpecPhi_ymat, h2]

#print axioms sprYmat_powMat_map_spec

/-- ★★★★★★★ **`hY`（`Spr` 层）**：`M_p` 的行列式非零。 -/
theorem sprYmat_powMat_det_ne_zero (k : {k : Fin r // k.val ≠ 0}) (p : Fin n) :
    (Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).det ≠ 0 := by
  have hmap := sprYmat_powMat_map_spec F r n k p
  have hdet : ((Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).map
      (sprSpecPhi F r n)).det ≠ 0 := by
    rw [hmap]
    exact sprPermMatrix_det_ne_zero _
  have hcomm : (sprSpecPhi F r n) (Matrix.of (fun (j q : Fin n) =>
      ((ymat F r n k) ^ (j : ℕ)) p q)).det
      = ((Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).map
        (sprSpecPhi F r n)).det := RingHom.map_det _ _
  intro h0
  exact hdet (by rw [← hcomm, h0, map_zero])

#print axioms sprYmat_powMat_det_ne_zero

/-- ★★★★★★★★ **`hY`（`K'` 层，§90 所需形态）**：`Y`-幂矩阵的行列式非零。 -/
theorem sprY_powMat_det_ne_zero (k : {k : Fin r // k.val ≠ 0}) (p : Fin n) :
    (Matrix.of (fun (j q : Fin n) =>
      (((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))) ^ (j : ℕ)) p q)).det
      ≠ 0 := by
  have h1 : (Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).map
        (algebraMap (Spr F r n) (SprField F r n))
      = Matrix.of (fun (j q : Fin n) =>
          (((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))) ^ (j : ℕ)) p q) := by
    ext j q
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact congrFun (congrFun (Matrix.map_pow (ymat F r n k)
      (algebraMap (Spr F r n) (SprField F r n)) (j : ℕ)) p) q
  have hdet := sprYmat_powMat_det_ne_zero F r n k p
  have hcomm : (algebraMap (Spr F r n) (SprField F r n))
      (Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).det
      = (Matrix.of (fun (j q : Fin n) =>
          (((ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))) ^ (j : ℕ)) p q)).det := by
    calc (algebraMap (Spr F r n) (SprField F r n))
          (Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).det
        = ((Matrix.of (fun (j q : Fin n) => ((ymat F r n k) ^ (j : ℕ)) p q)).map
            (algebraMap (Spr F r n) (SprField F r n))).det := RingHom.map_det _ _
      _ = _ := by rw [h1]
  rw [← hcomm]
  intro h
  exact hdet (IsFractionRing.injective (Spr F r n) (SprField F r n) (by rw [h, map_zero]))

#print axioms sprY_powMat_det_ne_zero

end SprHY

/-! ## §97 ★★★★★★★★★ **`{X^i Y^j}` 线性无关**（PI 输入的一半：§90 ＋ §96 复合）

§90 已把 `{X^iY^j}` 的线性无关性归约到 `hY`；§96 证完了 `hY`。本节**复合**两者，
得到本战役 PI 输入的**独立性半边**：

```
LinearIndependent K' (fun t : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₀ k t.1 t.2)
```

即 `Ξ = {ψ(X_{k₀})^i ψ(X_k)^j}` 在 `K'` 上**线性无关**（`k ≠ k₀`）。

**证明**：取 `x := sprDiagVal`（互异，`sprDiagVal_injective`）、
`Y := (ymat ⟨k,·⟩)` 沿 `algebraMap` 的像、`hY := sprY_powMat_det_ne_zero`，
套 §90 的 `sprXi_linearIndependent_of_det`，再把族逐点改写成 `xiSprK`
（`psiSpr_sprGen` ＋ `sprGen_k0_eq`／`sprGen_ne_eq` ＋ `sprXdiagK_eq_map`）。

**⟹ 与 `Nat.card = n*n` 一起即给 `XiSpanHypK'`／`XiBasisHypK'`**（`n²` 个无关元在 `n²` 维空间里
张成；`basisOfLinearIndependentOfCardEqFinrank`）。**该收口未做**（下一轮）。

**射程（勿夸大）**：本节只给**线性无关**；`XiBasisHypK'`（张成／基）**未证**；
`SFixedLeZ`／`K'^N ⊆ Z` **未证**；**H2 仍为条件化定理**。 -/

section SprXiLinearIndependent

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ) [NeZero n] [Nonempty (Fin n)]

/-- ★★★★★★★ **`{X^i Y^j}` 线性无关**（`Ξ` 的 PI 输入的一半：§90 ＋ §96）。 -/
theorem sprXi_linearIndependent (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀) :
    LinearIndependent (SprField F r n)
      (fun t : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₀ k t.1 t.2) := by
  classical
  set k' : {k : Fin r // k.val ≠ 0} := ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩ with hk'
  have hY := sprY_powMat_det_ne_zero F r n k'
  have hLI := sprXi_linearIndependent_of_det F r n (x := sprDiagVal F r n)
    (sprDiagVal_injective F r n) (Y := (ymat F r n k').map (algebraMap (Spr F r n) (SprField F r n)))
    hY
  have hfam : (fun t : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₀ k t.1 t.2)
      = (fun t : Fin n × Fin n =>
          (Matrix.diagonal (sprDiagVal F r n)) ^ (t.1 : ℕ)
            * ((ymat F r n k').map (algebraMap (Spr F r n) (SprField F r n))) ^ (t.2 : ℕ)) := by
    funext t
    simp only [xiSprK]
    rw [psiSpr_sprGen (F := F) (r := r) (n := n) k₀ hk₀ k₀,
      sprGen_k0_eq (F := F) (r := r) (n := n) k₀ hk₀,
      psiSpr_sprGen (F := F) (r := r) (n := n) k₀ hk₀ k,
      sprGen_ne_eq (F := F) (r := r) (n := n) k₀ hk₀ hk, hk',
      ← sprXdiagK_eq_map (F := F) (r := r) (n := n)]
    rfl
  rw [hfam]
  exact hLI

#print axioms sprXi_linearIndependent

end SprXiLinearIndependent

/-! ## §98 ★★★★★★★★★★ **`XiBasisHypK'` 成定理**（PI 的基形态落地；具名输入 `XiBasisHypK'` **已消**）

§97 给了 `{X^iY^j}` 的**线性无关性**；`Ξ` 恰有 `n²` 个元，而 `M_n(K')` 的 `K'`-维数也是 `n²`
（`Module.finrank_matrix`）⟹ `n²` 个无关元**必张成** ⟹ 成**基**：

```
XiBasisHypK' F r n k₀ hk₀ k₀ k        （k ≠ k₀）—— 定理
XiSpanHypK'  F r n k₀ hk₀ k₀ k        —— 定理
```

**⟹ 后果（既有件，全部转无条件）**：
`matMapFaithfulHyp_of_xiBasisHypK'`（§59）⟹ `MatMapFaithfulHyp` 成定理；
`nfixedIsCoordHyp_of_xiBasisHypK'`（§59）⟹ `NfixedIsCoordHyp` 成定理；
`udkTensorToMatrix_surjective_of_xiSpanK'`（§42）⟹ **`UDK' ⊗_Z K' → M_n(K')` 满射**。

**⚠ 射程（诚实边界）**：`UDKTensorHypK'` 要求**双射**（`Function.Bijective`）；
本节只给**满射半边**。**单射**等价于 `dim_Z UDK' = n²`（PI 的另一半），**仍开**。
故 `h2_of_zHalf` 的 `hPI` 输入**尚不能消**；`SFixedLeZ`／`K'^N ⊆ Z` **未证**；
**H2 仍为条件化定理**（但三个具名 Prop 之下已有一整个 PI 形态落地）。 -/

section SprXiBasis

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ) [NeZero n] [Nonempty (Fin n)]

/-- ★★★★★★★★★ **`XiBasisHypK'` 成定理**（`Ξ` 是 `K'`-基；PI 输入的完成）。 -/
theorem sprXiBasisHypK' (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀) :
    XiBasisHypK' F r n k₀ hk₀ k₀ k := by
  classical
  refine ⟨basisOfLinearIndependentOfCardEqFinrank
    (b := fun t : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₀ k t.1 t.2)
    (sprXi_linearIndependent F r n k₀ hk₀ hk) ?_, fun p => ?_⟩
  · rw [Module.finrank_matrix]
    simp
  · simp

#print axioms sprXiBasisHypK'

/-- ★★★★★★★★ **`XiSpanHypK'` 成定理**（`Ξ` 张成）。 -/
theorem sprXiSpanHypK' (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀) :
    XiSpanHypK' F r n k₀ hk₀ k₀ k :=
  xiSpanHypK'_of_xiBasisHypK' (F := F) (r := r) (n := n) (k₀ := k₀) (hk₀ := hk₀)
    (k₁ := k₀) (k₂ := k) (sprXiBasisHypK' F r n k₀ hk₀ hk)

#print axioms sprXiSpanHypK'

end SprXiBasis

/-! ## §99 ★★★★★★★★★★ **终点条件形态的最终化简**：只剩「单射半边 ＋ `Z` 半」

§98 已把 `XiBasisHypK'`（与 `XiSpanHypK'`）变成**定理**。本节把它代入终点链，
把 `ZEqNFixed`／H2 的条件输入**从四项压到两项**：

```
Function.Injective (udkTensorToMatrix F 2 9 D k₀ hk₀)      —— PI 的剩余半边（dim_Z UDK' = n²）
∀ x, sprFieldNFixed x → x ∈ Z                              —— Z 半（Procesi FFT 的一半）
⟹ ZEqNFixed F D   ⟹   ProcesiS9Hyp F ↥(ZCanon F 2 9 D)
```

**机制**：
- `UDKTensorHypK'` 是 `Function.Bijective`；**满射**由 §98 的 `XiSpanHypK'`
  ＋ §42 的 `udkTensorToMatrix_surjective_of_xiSpanK'` 供给 ⟹ 只剩**单射**作输入
  （`sprUDKTensorHypK'_of_injective`）；
- `XiBasisHypK'` 直接由 §98 的 `sprXiBasisHypK'` 供给；
- 其余照 §87／§88 的既有链（`zEqNFixed_of_zHalf` → `h2_of_ZEqNFixed`）。

| 件 | 内容 |
|---|---|
| ★★★★★★★ `sprUDKTensorHypK'_of_injective` | **`UDKTensorHypK'` ⟸ 单射**（满射已无条件） |
| ★★★★★★★★★ `zEqNFixed_of_injective_and_zHalf` | **`ZEqNFixed` ⟸ 单射 ＋ `Z` 半** |
| ★★★★★★★★★ `h2_of_injective_and_zHalf` | **H2 ⟸ 单射 ＋ `Z` 半** |

**射程（勿夸大）**：`hinj`（＝`dim_Z UDK' = n²`）与 `hZ`（＝Procesi FFT 的一半）**均未证**；
**H2 仍不是无条件定理**。本节的增益是**输入清单的最小化**：
`XiBasisHypK'` 已从终点件中**彻底消失**，`UDKTensorHypK'` 只剩单射。 -/

section SprEndgameFinal

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F]

/-- ★★★★★★★ **`UDKTensorHypK'` 只需单射半边**：满射由 §98 的 `XiSpanHypK'` 供给。 -/
theorem sprUDKTensorHypK'_of_injective (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) {k : Fin 2} (hk : k ≠ k₀)
    (hinj : Function.Injective (udkTensorToMatrix F 2 9 D k₀ hk₀)) :
    UDKTensorHypK' F 2 9 D k₀ hk₀ :=
  ⟨hinj, udkTensorToMatrix_surjective_of_xiSpanK' F 2 9 D k₀ hk₀
    (sprXiSpanHypK' F 2 9 k₀ hk₀ hk)⟩

#print axioms sprUDKTensorHypK'_of_injective

/-- ★★★★★★★★★ **`ZEqNFixed` 的最终条件形态**：**单射半边 ＋ `Z` 半**（`XiBasisHypK'` 已由 §98 消掉）。 -/
theorem zEqNFixed_of_injective_and_zHalf [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) {k : Fin 2} (hk : k ≠ k₀)
    (hinj : Function.Injective (udkTensorToMatrix F 2 9 D k₀ hk₀))
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_zHalf F D hk₀ (sprUDKTensorHypK'_of_injective F D hk₀ hk hinj)
    (sprXiBasisHypK' F 2 9 k₀ hk₀ hk) hZ

#print axioms zEqNFixed_of_injective_and_zHalf

/-- ★★★★★★★★★ **H2 的最终条件形态**（同上 ＋ `h2_of_ZEqNFixed`）。 -/
theorem h2_of_injective_and_zHalf [CharZero F] (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) {k : Fin 2} (hk : k ≠ k₀)
    (hinj : Function.Injective (udkTensorToMatrix F 2 9 D k₀ hk₀))
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_injective_and_zHalf F D hk₀ hk hinj hZ)

#print axioms h2_of_injective_and_zHalf

end SprEndgameFinal

/-! ## §100 ★★★★★★★★ **修复版终点骨架**（**不含** `UDK'`／`UDKTensorHypK'`）

第 482 轮的结构审计（[[proj-abgv52-UD-tensor-vacuity-audit]]）判定：
本仓 `UDK' = Algebra.adjoin ↥Z (range (ψ(X_k).map))` 在 `Z` 上**很可能无限维**
（`X^i` 无限独立，因 `trdeg(K'/Z) = n−1 ≥ 1`）⟹ **`UDKTensorHypK'`（要求双射）很可能为假**
⟹ 以它为前提的 §65／§69／§87／§99 终点件**属空洞真**（L1／L10①）。

本节给出**不含 `UD` 模型**的终点骨架：输入只有 **`sprCenterZMap` 的满射性**
（一条关于中心映射本身的命题，其定义域/值域都已存在、且**不经过** `UDK'`）：

```
Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)
  ⟹ ZEqNFixed F D                        （§32 的 zEqNFixed_of_surjective）
  ⟹ ProcesiS9Hyp F ↥(ZCanon F 2 9 D)     （h2_of_ZEqNFixed）
```

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `zEqNFixed_of_centerSurj` | **`ZEqNFixed` ⟸ `sprCenterZMap` 满射** |
| ★★★★★★★★★ `h2_of_centerSurj` | **H2 ⟸ 同上** |

**⟹ 修复后的诚实口径**：H2 的剩余内容 = **`sprCenterZMap` 满射**（≍ `Z = K'^N` 的 (B) 形态），
**不再包含任何 `UD` 模型假设**。

**⚠ 已知的下一步障碍（本轮查明）**：`sprCenterZMap` 的定义域是
`↥(IntermediateField.adjoin F (Set.range D.centK))`（**`SField`** 世界），
而 `Z` 半的 (B) 形态 `sprCenterImageField` 在 **`SprField`** 世界。两者之间的搬运
（`SField ↔ SprField` 沿 `phiKEquiv`／`sprCenterPolyK` 的识别）**尚未在库中显式化**——
这正是原链绕道 `UDK'`／`θ_i` 的原因。**⟹ 下一轮任务 = 建这条搬运**，
再把 `hZ : K'^N ⊆ Z` 转成 `sprCenterZMap` 满射，即可用本节的骨架收口。

**射程（勿夸大）**：本节只是**骨架**；满射性**未证**；H2 **仍不是无条件定理**。 -/

section SprRepairedEndgame

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] [CharZero F]

/-- ★★★★★★★★ **修复版终点骨架（不含 `UDK'`／`UDKTensorHypK'`）**：
`sprCenterZMap` 满射 ⟹ `ZEqNFixed` ⟹ H2。

**为何这是修复**：原链（§65／§69／§87／§99）以 `UDKTensorHypK'` 为输入，
而该输入**很可能为假**（[[proj-abgv52-UD-tensor-vacuity-audit]]：`dim_Z UDK' = ∞`）。
本件的输入只有一条**关于中心映射本身**的满射性——它**不含**任何 `UD` 模型。 -/
theorem zEqNFixed_of_centerSurj (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0) (h : Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)) :
    ZEqNFixed F D :=
  zEqNFixed_of_surjective F D hk₀ h

#print axioms zEqNFixed_of_centerSurj

/-- ★★★★★★★★★ **H2 的修复版终点形态**：`sprCenterZMap` 满射即可。 -/
theorem h2_of_centerSurj (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0) (h : Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_centerSurj F D hk₀ h)

#print axioms h2_of_centerSurj

end SprRepairedEndgame

/-! ## §101 ★★★★★★★★★★ **修复完成：`Z` 半 ⟹ H2**（**不含任何 `UD` 模型**）

第 482 轮的审计判定 `UDKTensorHypK'`（`UDK'` 的 `Z`-张量双射）**很可能为假**
（[[proj-abgv52-UD-tensor-vacuity-audit]]：`dim_Z UDK' = ∞`）。
第 483 轮给了不含 `UD` 模型的骨架（§100，输入 = `sprCenterZMap` 满射）。
本节**把真正的假设接上去**：

```
hZ : ∀ x : K', N-不变 ⟹ x ∈ Z (= sprCenterImageField)      —— Z 半（Procesi FFT 的一半，真命题）
  ⟹  SprCenterZMap 满射  ⟹  ZEqNFixed F D  ⟹  H2
```

**证明（三行半）**：`hZ` 给 `y.1 ∈ sprCenterImageField`；§7.11 的**无条件**结构性桥
`sprCenterImageField_le_fieldRange` 给 `y.1 ∈ fieldRange(sprCenterZMapToField)`
＝ `∃ z, sprCenterZMapToField z = y.1`；再 `Subtype.ext` 收口。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★★ `h2_of_zHalf_repaired` | **H2 ⟸ `Z` 半**（无 `UD` 模型） |
| ★★★★★★★★★★ `zEqNFixed_of_zHalf_repaired` | **`ZEqNFixed` ⟸ `Z` 半**（同上） |

**⟹ 本战役的剩余内容现在**只剩一项**：`Z` 半 `K'^N ⊆ Z`**（Procesi FFT 的一半）。
§99 的 `hinj` 形态（以 `UDKTensorHypK'` 为输入）**被本节的 `hZ` 形态取代**，
空洞风险**已从终点件中移除**（`Z` 半的假设类**非空**：`Z ⊆ K'^N` 早已机检，§29）。

**射程（勿夸大）**：`hZ` **未证**；H2 **仍不是无条件定理**。 -/

section SprRepairedEndgame2

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] [CharZero F]

/-- ★★★★★★★★★★ **修复版终点：`Z` 半 ⟹ H2**（**不含** `UD` 模型；用 §7.11 的无条件结构性桥）。 -/
theorem h2_of_zHalf_repaired (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0)
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) := by
  refine h2_of_centerSurj F D hk₀ (fun y => ?_)
  have hx : (y : SprField F 2 9) ∈ sprCenterImageField F 2 9 D k₀ hk₀ := hZ y.1 y.2
  have hle : (y : SprField F 2 9)
      ∈ (sprCenterZMapToField F 2 9 D k₀ hk₀).fieldRange :=
    sprCenterImageField_le_fieldRange F 2 9 D k₀ hk₀ hx
  obtain ⟨z, hz⟩ := hle
  exact ⟨z, Subtype.ext hz⟩

#print axioms h2_of_zHalf_repaired

/-- ★★★★★★★★★★ **`ZEqNFixed` 同款**（修复版）。 -/
theorem zEqNFixed_of_zHalf_repaired (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0)
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_centerSurj F D hk₀ (fun y => by
    have hx : (y : SprField F 2 9) ∈ sprCenterImageField F 2 9 D k₀ hk₀ := hZ y.1 y.2
    have hle : (y : SprField F 2 9)
        ∈ (sprCenterZMapToField F 2 9 D k₀ hk₀).fieldRange :=
      sprCenterImageField_le_fieldRange F 2 9 D k₀ hk₀ hx
    obtain ⟨z, hz⟩ := hle
    exact ⟨z, Subtype.ext hz⟩)

#print axioms zEqNFixed_of_zHalf_repaired

end SprRepairedEndgame2

/-! ## §102 ★★★★★★★★ **终点件与已发表定理对齐**：`ZEqNFixed` ⟺ Saltman `thm:14.17`

本仓的 `ZEqNFixed` 与**已发表定理**之间的最后一段文字等价，本节机检：

```
ZEqNFixed F D  ⟺  SaltmanThm1417At9 F ↥(ZCanon F 2 9 D)
```

即 **`Z(F,9,2) ≅ F(M_2)^{S_9}`**（Saltman `thm:14.17` 的 `(9,2)` 实例）。
**机制**：`SaltmanT.lean:3131` 的 `nFixedAlgEquiv : ↥(NFixedAlg F) ≃ₐ[F] ↥(invariantsField F)`
＋ `Statement.lean` 的 `Lat = ProcLat.Mp2 3 = Mtwo`（`Saltman.lean:93`）。

**用途**：把"本战役还差什么"从内部术语**译成文献陈述**——
剩余内容 ＝ `thm:14.17`（Procesi 不变量域定理的 Saltman 版），其已发表证明路线见
[[proj-abgv52-z-half-literature-route]]（AGPR2020 `thm:12.1.3` FFT ＋ `thm:14.4.4`）。

**L46 侦察附记（本轮）**：`mathlib` 与 `TauCeti` **均无** FFT（矩阵不变环由 trace 单项式生成）
的现成件——`mathlib` 只有 `Algebra/Azumaya/*` 与 `Central/Defs`；`TauCeti` 只有
`Algebra/Ring/Action/Invariant.lean`（一般环作用的抽象框架）与 `Algebra/CentralSimple/`（CSA 秩账）。
**⟹ FFT 若要形式化，须自建**（极化／复原 ＋ 多线性引理；见 AGPR2020 ch.12）。

**射程（勿夸大）**：本节只做**等价搬运**；`thm:14.17` 本身**未证**；H2 **仍不是无条件定理**。 -/

section SprLiteratureForm

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] [CharZero F]

/-- ★★★★★★★★ **`ZEqNFixed` ⟺ Saltman `thm:14.17`（`n = 9, r = 2`）** ——
本战役的剩余内容与**已发表定理**逐字对齐（经 `nFixedAlgEquiv` 与 `Lat = Mtwo`）。 -/
theorem zEqNFixed_iff_saltman1417 (D : GenericDivisionData F 2 9) :
    ZEqNFixed F D ↔ SaltmanThm1417At9 F ↥(ZCanon F 2 9 D) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (nFixedAlgEquiv F)⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (nFixedAlgEquiv F).symm⟩

#print axioms zEqNFixed_iff_saltman1417

/-- ★★★★★★★★★ **H2 的文献形态**：`h2_of_centerSurj` 与 `thm:14.17` 的接线。 -/
theorem saltman1417_of_centerSurj (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0) (h : Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)) :
    SaltmanThm1417At9 F ↥(ZCanon F 2 9 D) :=
  (zEqNFixed_iff_saltman1417 F D).mp (zEqNFixed_of_centerSurj F D hk₀ h)

#print axioms saltman1417_of_centerSurj

/-! ## §105 ★★★★★★★★★ **`Z` 半的**多项式层形态**（新的终点输入形状）

第 491 轮。§101 的修复版终点的输入是**域层**的 `Z` 半

```
∀ x : K', sprFieldNFixed x ⟹ x ∈ Frac(κ(C))
```

本节把它**等价地**换成**多项式层**的形态

```
∀ f : S', sprNFixed f ⟹ algebraMap f ∈ Frac(κ(C))
```

**为何要换**（路线判据，不是装饰）：FFT（Procesi／AGPR2020 `thm:12.1.3`）与 Saltman
`lem:14.24` 的机器可检结论都作用在**多项式**上（极化／复原、多线性引理、判别式局部化），
而域层的分式形态无法直接消费。**等价性靠已机检的 `lem1425_scalar`（§152）**：
`K'^N` 的每个元素都是两个 `N`-不变多项式之商。

| 件 | 内容 |
|---|---|
| ★★ `sprFieldNFixed_algebraMap_of_sprNFixed` | `S'^N` 的元素经 `algebraMap` 落进 `K'^N` |
| ★★★★★ `zHalf_iff_sprNFixed_le` | **`K'^N ⊆ Z` ⟺ `S'^N ⊆ Z`** |
| ★★★★★ `h2_of_sprNFixed_le` | **`S'^N ⊆ Z` ⟹ H2**（新的终点形状） |
| ★★★★★ `saltman1417_of_sprNFixed_le` | **`S'^N ⊆ Z` ⟹ Saltman `thm:14.17`** 的 `(9,2)` 实例 |

**射程（勿夸大）**：本节只做**形态换算**。`S'^N ⊆ Z` 本身**未证**；
H2 **仍不是无条件定理**。 -/

section SprPolynomialZHalf

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★ **`N`-不变多项式在 `K'` 里仍是 `N`-不变的**（`S'`-世界 → `K'`-世界）。 -/
theorem sprFieldNFixed_algebraMap_of_sprNFixed {f : Spr F r n}
    (hf : sprNFixed F r n f) :
    sprFieldNFixed F r n (algebraMap (Spr F r n) (SprField F r n) f) :=
  ⟨sprFieldTFixed_algebraMap F r n hf.1, sprFieldSFixed_algebraMap F r n hf.2⟩

#print axioms sprFieldNFixed_algebraMap_of_sprNFixed

/-- ★★★★★ **`Z` 半的两形态等价**：域层 `K'^N ⊆ Z` ⟺ 多项式层 `S'^N ⊆ Z`。

`⇒` 用 `sprFieldNFixed_algebraMap_of_sprNFixed`；`⇐` 用 `lem1425_scalar`（§152）把
`x ∈ K'^N` 写成两个 `N`-不变多项式之商，再在域里做除法。 -/
theorem zHalf_iff_sprNFixed_le [Nonempty (Fin n)] [NeZero n] [Infinite F]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (∀ x : SprField F r n, sprFieldNFixed F r n x →
        x ∈ sprCenterImageField F r n D k₀ hk₀)
      ↔ (∀ f : Spr F r n, sprNFixed F r n f →
          algebraMap (Spr F r n) (SprField F r n) f
            ∈ sprCenterImageField F r n D k₀ hk₀) := by
  constructor
  · intro hZ f hf
    exact hZ _ (sprFieldNFixed_algebraMap_of_sprNFixed F r n hf)
  · intro hS x hx
    obtain ⟨s, β, hs0, hsN, hβN, hxeq⟩ := lem1425_scalar (F := F) (r := r) (n := n) x hx
    have hsm : algebraMap (Spr F r n) (SprField F r n) s ≠ 0 := by
      intro h0
      exact hs0 (IsFractionRing.injective (Spr F r n) (SprField F r n)
        (by simpa using h0))
    rw [hxeq]
    exact div_mem (hS β hβN) (hS s hsN)

#print axioms zHalf_iff_sprNFixed_le

end SprPolynomialZHalf

section SprPolynomialEndgame

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] [CharZero F] [Infinite F]

/-- ★★★★★ **新终点（多项式层输入）**：`S'^N ⊆ Z` ⟹ H2。 -/
theorem h2_of_sprNFixed_le (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0)
    (hS : ∀ f : Spr F 2 9, sprNFixed F 2 9 f →
      algebraMap (Spr F 2 9) (SprField F 2 9) f
        ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_zHalf_repaired F D hk₀
    ((zHalf_iff_sprNFixed_le F 2 9 D k₀ hk₀).mpr hS)

#print axioms h2_of_sprNFixed_le

/-- ★★★★★ **文献形态的新终点**：`S'^N ⊆ Z` ⟹ Saltman `thm:14.17` 的 `(9,2)` 实例。 -/
theorem saltman1417_of_sprNFixed_le (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0)
    (hS : ∀ f : Spr F 2 9, sprNFixed F 2 9 f →
      algebraMap (Spr F 2 9) (SprField F 2 9) f
        ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    SaltmanThm1417At9 F ↥(ZCanon F 2 9 D) :=
  (zEqNFixed_iff_saltman1417 F D).mp
    (zEqNFixed_of_zHalf_repaired F D hk₀
      ((zHalf_iff_sprNFixed_le F 2 9 D k₀ hk₀).mpr hS))

#print axioms saltman1417_of_sprNFixed_le

end SprPolynomialEndgame

end SprLiteratureForm

/-! ## §103 ★★★★★ **FFT 的"易半"第一件**：`trace(X₁X₂)` 是 `PGL`-不变量

按 [[proj-abgv52-fft-formalization-plan]] 的切分，FFT 分**两半**：
**(A) 易半**（trace 单项式**确实是** `PGL`-不变量）与 **(B) 难半**（每个不变量都由 trace 单项式生成）。
本节做 (A) 的第一个实例：

```
φ_A (Matrix.trace (X_k * X_l))  =  Matrix.trace (X_k * X_l)
```

**证明（四步）**：
1. `phiA_trace_eq`：`φ_A (tr M) = tr (M.map φ_A)`（`Matrix.trace` 的定义 ＋ `map_sum`）；
2. `Matrix.map_mul`：`(X_k * X_l).map φ_A = X_k.map φ_A * X_l.map φ_A`；
3. `phiA_X`（源文 `(16)`）：`X_k.map φ_A = C⁻¹ X_k C`（`C = constMat A`）；
4. **矩阵迹的共轭不变性**：`tr(C⁻¹ M C) = tr M`（`trace_mul_comm` ＋ `C C⁻¹ = 1`）。

| 件 | 内容 |
|---|---|
| ★★★★★ `phiA_trace_eq` | `φ_A (tr M) = tr (M.map φ_A)` |
| ★★★★★ `phiA_trace_mul` | **`trace(X_k * X_l)` 是 `PGL`-不变量**（FFT 易半第一实例） |

**用途**：(A) 半是 (B) 半的**非空性对照**（L10①：生成元确实落在目标里）；
且本件把"`φ_A` ↔ `Matrix.map` ↔ `trace`"三者交互的**形态问题**一次解决
（本战役的老痛点：R274 同族、§95 工艺）。

**下一件**（切分第 2 步）：推广到任意字 `w`（`List`／自由幺半群）——`Matrix.map_prod` ＋ 同样四步。

**射程（勿夸大）**：本节只有 (A) 半的**两因子实例**；(B) 半（FFT 本体）**未做**；
`SFixedLeZ`／`Z` 半／H2 **仍不是定理**。 -/

section SprFFTEasyHalf

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)

/-- `φ_A (tr M) = tr (M.map φ_A)`。 -/
theorem phiA_trace_eq (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (M : Matrix (Fin n) (Fin n) (S F r n)) :
    phiA F r n A (Matrix.trace M) = Matrix.trace (M.map (phiA F r n A)) := by
  rw [Matrix.trace, map_sum, Matrix.trace]
  exact Finset.sum_congr rfl (fun i _ => rfl)

#print axioms phiA_trace_eq

/-- ★★★★★ **FFT 的"易半"（两因子情形）**：`trace(X_k * X_l)` 是 `PGL`-不变量。 -/
theorem phiA_trace_mul (A : (Matrix (Fin n) (Fin n) F)ˣ) (k l : Fin r) :
    phiA F r n A (Matrix.trace (genericMatrix F r n k * genericMatrix F r n l))
      = Matrix.trace (genericMatrix F r n k * genericMatrix F r n l) := by
  rw [phiA_trace_eq, Matrix.map_mul, phiA_X, phiA_X]
  -- (C' X_k C) * (C' X_l C) = C' (X_k X_l) C
  have hCC : constMat F r n (↑A) * constMat F r n (↑A⁻¹) = 1 := by
    rw [← constMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMat_one]
  rw [show constMat F r n (↑A⁻¹) * genericMatrix F r n k * constMat F r n (↑A)
        * (constMat F r n (↑A⁻¹) * genericMatrix F r n l * constMat F r n (↑A))
      = constMat F r n (↑A⁻¹) * (genericMatrix F r n k * genericMatrix F r n l)
        * constMat F r n (↑A) from by
    calc constMat F r n (↑A⁻¹) * genericMatrix F r n k * constMat F r n (↑A)
          * (constMat F r n (↑A⁻¹) * genericMatrix F r n l * constMat F r n (↑A))
        = constMat F r n (↑A⁻¹) * genericMatrix F r n k
            * (constMat F r n (↑A) * constMat F r n (↑A⁻¹))
            * genericMatrix F r n l * constMat F r n (↑A) := by noncomm_ring
      _ = constMat F r n (↑A⁻¹) * (genericMatrix F r n k * genericMatrix F r n l)
            * constMat F r n (↑A) := by rw [hCC]; noncomm_ring]
  -- tr (C' M C) = tr M
  rw [show constMat F r n (↑A⁻¹) * (genericMatrix F r n k * genericMatrix F r n l)
        * constMat F r n (↑A)
      = constMat F r n (↑A⁻¹)
        * ((genericMatrix F r n k * genericMatrix F r n l) * constMat F r n (↑A)) from by
    noncomm_ring]
  rw [Matrix.trace_mul_comm]
  rw [show (genericMatrix F r n k * genericMatrix F r n l) * constMat F r n (↑A)
        * constMat F r n (↑A⁻¹)
      = genericMatrix F r n k * genericMatrix F r n l from by
    rw [Matrix.mul_assoc, hCC, Matrix.mul_one]]

#print axioms phiA_trace_mul

end SprFFTEasyHalf

/-! ## §104 ★★★★★★ **FFT 易半（任意字）**：`trace` 的字是 `PGL`-不变量

§103 做了两因子情形；本节按切分第 2 步推广到**任意字** `ws : List (Fin r)`：

```
M_ws := X_{w₁} ⋯ X_{w_m}
M_ws.map φ_A = C⁻¹ · M_ws · C            （sprWord_map_phiA；对 ws 归纳）
φ_A (tr M_ws) = tr M_ws                  （phiA_trace_word）
```

**证明**：对 `ws` 归纳。空字用 `C⁻¹ C = 1`；归纳步用 `Matrix.map_mul` ＋ `phiA_X` ＋
一条**纯结合律**引理（`C C' = 1` 时 `(C'XC)(C'MC) = C'(XM)C`）。
迹的不变性仍由 `trace_mul_comm` ＋ `C C⁻¹ = 1`。

| 件 | 内容 |
|---|---|
| `sprWord` | 字 `ws ↦ X_{w₁}⋯X_{w_m}` |
| `sprConstMat_mul_inv`／`_inv_mul` | `C C⁻¹ = 1`／`C⁻¹ C = 1` |
| ★★★★★ `sprWord_map_phiA` | **`M_ws.map φ_A = C⁻¹ M_ws C`** |
| ★★★★★★ `phiA_trace_word` | **`φ_A (tr M_ws) = tr M_ws`**（易半，任意字） |

**⟹ (A) 半完成**（trace 单项式**确实是** `PGL`-不变量）。它是 (B) 半的非空性对照（L10①）。

**下一件**（切分第 3 步）：Newton 恒等式（`tr(M^k)` 决定特征系数）。

**射程（勿夸大）**：(B) 半（FFT 本体：每个不变量都由 trace 单项式生成）**未做**；
`SFixedLeZ`／`Z` 半／H2 **仍不是定理**。 -/

section SprFFTWord

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ)

/-- 字 `ws` 对应的矩阵积 `X_{w₁} ⋯ X_{w_m}`。 -/
noncomputable def sprWord (ws : List (Fin r)) : Matrix (Fin n) (Fin n) (S F r n) :=
  (ws.map (fun k => genericMatrix F r n k)).prod

#print axioms sprWord

/-- `C A * C A⁻¹ = 1`（`constMat` 形态）。 -/
theorem sprConstMat_mul_inv (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    constMat F r n (↑A) * constMat F r n (↑A⁻¹) = 1 := by
  rw [← constMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMat_one]

#print axioms sprConstMat_mul_inv

/-- `C A⁻¹ * C A = 1`。 -/
theorem sprConstMat_inv_mul (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    constMat F r n (↑A⁻¹) * constMat F r n (↑A) = 1 := by
  rw [← constMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, constMat_one]

#print axioms sprConstMat_inv_mul

/-- ★★★★ **共轭作用在字矩阵上**：`M_w.map φ_A = C⁻¹ · M_w · C`。 -/
theorem sprWord_map_phiA (A : (Matrix (Fin n) (Fin n) F)ˣ) (ws : List (Fin r)) :
    (sprWord F r n ws).map (phiA F r n A)
      = constMat F r n (↑A⁻¹) * sprWord F r n ws * constMat F r n (↑A) := by
  induction ws with
  | nil =>
    simp only [sprWord, List.map_nil, List.prod_nil,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    exact (sprConstMat_inv_mul F r n A).symm
  | cons k ws ih =>
    show ((genericMatrix F r n k) * sprWord F r n ws).map (phiA F r n A)
      = constMat F r n (↑A⁻¹) * ((genericMatrix F r n k) * sprWord F r n ws)
        * constMat F r n (↑A)
    rw [Matrix.map_mul, ih, phiA_X]
    have hCC := sprConstMat_mul_inv F r n A
    have hassoc : ∀ (C C' X M : Matrix (Fin n) (Fin n) (S F r n)), C * C' = 1 →
        (C' * X * C) * (C' * M * C) = C' * (X * M) * C := by
      intro C C' X M h
      rw [show (C' * X * C) * (C' * M * C) = C' * X * (C * C') * M * C from by
        noncomm_ring, h, Matrix.mul_one]
      noncomm_ring
    exact hassoc _ _ _ _ hCC

#print axioms sprWord_map_phiA

/-- ★★★★★★ **FFT 易半（任意字）**：`trace` 的**字**是 `PGL`-不变量。 -/
theorem phiA_trace_word (A : (Matrix (Fin n) (Fin n) F)ˣ) (ws : List (Fin r)) :
    phiA F r n A (Matrix.trace (sprWord F r n ws)) = Matrix.trace (sprWord F r n ws) := by
  rw [phiA_trace_eq, sprWord_map_phiA]
  have hCC := sprConstMat_mul_inv F r n A
  rw [show constMat F r n (↑A⁻¹) * sprWord F r n ws * constMat F r n (↑A)
      = constMat F r n (↑A⁻¹) * (sprWord F r n ws * constMat F r n (↑A)) from by
    noncomm_ring]
  rw [Matrix.trace_mul_comm]
  rw [show sprWord F r n ws * constMat F r n (↑A) * constMat F r n (↑A⁻¹)
      = sprWord F r n ws from by
    rw [Matrix.mul_assoc, hCC, Matrix.mul_one]]

#print axioms phiA_trace_word

end SprFFTWord

end SprEqualizerConverse


end SprEqualizerCoeff


end SprEtaEqualizer


end SprMatMapFaithful


end SprMatMapSemilinear


end SprCoeKtoS


end SprThetaCoord


end SprThetaCompute


end SprThetaOnUD


end SprMatMapKtoS


end SprCoordBridge


end SprThetaAgree


end SprTheta


end SprPiBridges


end SprUDKTensor


end SprXiCoord


end SprXdiagLinearIndependent


end SprXiK


end SprMatNFixedAlg


end SprUDKCenter


end SprTensorWorld


end SprImageField


end SprH2Interface

/-! ## §178 ★★★★★ `hZ` 与终点件的**子域包含形态**（两端 `IntermediateField` 语言一致）

`hZ`（§101／§105）是**点式**形态：`∀ x, sprFieldNFixed x → x ∈ sprCenterImageField`。
第 588 轮把左端升为 `IntermediateField`（`FFTRing.lean` 的 `sprNFixedField`，
载体同一、多一条求逆封闭），故 `hZ` 现在是一条**纯子域包含**
`sprNFixedField ≤ sprCenterImageField`（两者都是 `IntermediateField F (SprField F 2 9)`，
都自带 `Algebra F ↥` 实例）。

本节给出该等价与其终点件的包含形态，使后续进攻（`(β1)`／`(β2)` 两条子域包含）与
终点件**在同一语言**上对接。

**射程**：本节**只换陈述形态**，不证任何新的数学内容；`hZ` **未证**；
`S'^N ⊆ Z` 未证；H2 见文件头「当前状态」。 -/

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

section ZZiff

variable (F : Type) [Field F]

/-- ★★★★★★ **`hZ` 的子域包含形态**（与终结点式形态等价，**两端语言一致**）。 -/
theorem hZ_iff_sprNFixedField_le [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (∀ x : SprField F r n, sprFieldNFixed F r n x → x ∈ sprCenterImageField F r n D k₀ hk₀)
      ↔ sprNFixedField F r n ≤ sprCenterImageField F r n D k₀ hk₀ :=
  Iff.rfl

#print axioms hZ_iff_sprNFixedField_le

end ZZiff

section ZZle

variable (F : Type) [Field F] [CharZero F]

/-- ★★★★★★★★★ **终点（`Z` 半）的子域包含形态**：输入换成一条 `IntermediateField` 包含。 -/
theorem h2_of_zHalf_le (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0)
    (hle : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_zHalf_repaired F D hk₀ (fun _ hx => hle hx)

#print axioms h2_of_zHalf_le

/-- ★★★★★★★★★ **`ZEqNFixed` 同款的子域包含形态**。 -/
theorem zEqNFixed_of_zHalf_le (D : GenericDivisionData F 2 9) {k₀ : Fin 2}
    (hk₀ : k₀.val = 0)
    (hle : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_zHalf_repaired F D hk₀ (fun _ hx => hle hx)

#print axioms zEqNFixed_of_zHalf_le

end ZZle

/-! ## §179 ★★★★★★★★ **终局输入**经 `K' ∩ K^{PGL}` **的因式分解**：`K'^N ⊆ K'^{PGL} ⊆ Z`

第 654 轮。§178 把终局输入写成**一条**子域包含 `sprNFixedField ≤ sprCenterImageField`
（`K'^N ⊆ Z`，Saltman `prop:14.19` 的 `Z` 半）。本节把它**因式分解**成

```
K'^N  ≤  K' ∩ K^{PGL_n(F)}  ≤  Z
   (a)                          (b)
```

**为什么这是**对的路**（路线判据）**：
* **(a)** 是 **`N`-不变 与 `PGL`-不变 的比较**，只涉及两套已机检的作用与它们的等变性
  （`sprToSField_sprDiagFieldEquiv`／`_sprPermFieldEquiv`），**不触碰中心**；
* **(b)** 形如 **AGPR2020 `thm:14.4.4`**（"`𝒵` ＝ `GL(n,F)` 不变量环的分式域"，`raw/AGPR2020.tex:16787`），
  而该定理的**已机检半边**是本战役已收口的 FFT（`invariantAlg = traceAlgS`，
  `SliceTransport` 的 `invariantAlg_eq_traceAlgS`）。**(b) 正是能让 FFT 直接消费的形状。**

| 件 | 内容 |
|---|---|
| ★★★★★★ `pglFixedField` | `K^{PGL_n(F)}` 作为 `IntermediateField`（`n = 9`） |
| ★★★★★★ `sprPGLFixedField` | `K' ∩ K^{PGL}`（沿 `sprToSField` 的原像） |
| ★★★★★★★ `sprPGLFixedField_le_sprNFixedField` | **(a) 的反向**：`K' ∩ K^{PGL} ≤ K'^N`（免费，因 `N ⊆ PGL`） |
| ★★★★★★★ `pglFixed_le_of_zHalf` | **(b) 比 `hZ` 弱**：`hZ = (K'^N ≤ Z)` ⟹ (b) |
| ★★★★★★★★ `zEqNFixed_of_pglFixed`／`h2_of_pglFixed` | **(a) ＋ (b) ⟹ `ZEqNFixed`／H2** |

**射程（勿夸大，三条逐条给）**：
* **(a)** `K'^N ≤ K' ∩ K^{PGL}` **未证**；它是"`N`-不变量在 `K'` 里被 `PGL` 固定"的**比较步**，
  与 `N` 是 `PGL` 的**真子群**（`dim N = n` vs `dim PGL = n²−1`）这一事实相容，故**不能**由
  `N ⊆ PGL` 直接得到（那给的是反向 `P ≤ N`，本节已机检）。
* **(b)** `K' ∩ K^{PGL} ≤ Z` **未证**；其文献锚 = AGPR `thm:14.4.4`。
* `C ≤ P`（`Z` 的像落在 `K' ∩ K^{PGL}` 里）**未证**——故本节**不**声称 `hZ ⟺ (a) ∧ (b)`，
  只声称 `(a) ∧ (b) ⟹ hZ`（且 `hZ ⟹ (b)`，即 (b) 确比 `hZ` 弱）。
  `hZ` 未证；H2 见文件头「当前状态」。 -/

section SprPGLFixed

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- `K^{PGL_n(F)}`：`S`-侧被整个 `PGL_n(F)` 逐点固定的元素（`n = 9`，`IntermediateField` 形态）。 -/
noncomputable def pglFixedField (F : Type) [Field F] (r : ℕ) :
    IntermediateField F (SField F r 9) where
  carrier := {y | ∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ, phiKAlgEquiv F r 9 A y = y}
  zero_mem' := by
    intro A
    rw [map_zero]
  one_mem' := by
    intro A
    rw [map_one]
  add_mem' := by
    intro x y hx hy A
    rw [map_add, hx A, hy A]
  mul_mem' := by
    intro x y hx hy A
    rw [map_mul, hx A, hy A]
  inv_mem' := by
    intro x hx A
    rw [map_inv₀, hx A]
  algebraMap_mem' := by
    intro c A
    exact (phiKAlgEquiv F r 9 A).commutes c

#print axioms pglFixedField

/-- 成员刻画。 -/
theorem mem_pglFixedField_iff (F : Type) [Field F] (r : ℕ) {y : SField F r 9} :
    y ∈ pglFixedField F r ↔
      ∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ, phiKAlgEquiv F r 9 A y = y :=
  Iff.rfl

#print axioms mem_pglFixedField_iff

/-- `S`-侧 `PGL_n(F)`-不动点（`pglFixedField`）沿 `sprToSField` 的**原像**。

（与 `sprTraceFrac`（`FFTRing` §7）同构型：不做"直送"，只做 `comap`。）

**⚠ 解释性警告（第 694 轮机检；勿把它当作"`K' ∩ K^{PGL}`"使用）**：
`sprToSField` **不是 `N`-等变的**，也**不保中心元**——§216 机检
`exists_nFixed_psiImage_not_pglFixed`：存在 `x ∈ K'^N` 而 `sprToSField x ∉ pglFixedField`；
具体反例 `x = ∏_i x_{k₀,ii} = det X`（`psi_prodX_not_mem_pglFixedField`），而 `det X` 是中心元
（Saltman `prop:14.19`：`K'^N = Z`）。**⟹ 本定义排除中心元，与 Saltman 比较中的
`K' ∩ K^{PGL}` 不是同一对象。**

凡以本定义为"`K' ∩ K^{PGL}`"的论证（`(a)`／`(β1)`／`C ≤ P` 一支），其**结论照旧成立**
（都是关于这个 `comap` 的内部机检结论），但**不得读作对 Saltman `thm:14.16`／`prop:14.19`
的断言**。**忠实**的 `S`-侧对象是 `pglFixedField` 与 `KPFixedLeZ`（`GenericInv`），二者**不**受此影响。
若将来需要真正的"`K' ∩ K^{PGL}`"，须先造**保中心元**的对照（例如 `det X ↦ det (X_{k₀})`）。 -/
noncomputable def sprPGLFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) : IntermediateField F (SprField F r 9) :=
  (pglFixedField F r).comap (sprToSField F r 9 k₀ hk₀)

#print axioms sprPGLFixedField

/-- 成员刻画（按 `comap` 的定义）。 -/
theorem mem_sprPGLFixedField_iff (F : Type) [Field F] (r : ℕ) {k₀ : Fin r}
    (hk₀ : k₀.val = 0) {x : SprField F r 9} :
    x ∈ sprPGLFixedField F r k₀ hk₀ ↔
      ∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ,
        phiKAlgEquiv F r 9 A (sprToSField F r 9 k₀ hk₀ x) = sprToSField F r 9 k₀ hk₀ x :=
  Iff.rfl

#print axioms mem_sprPGLFixedField_iff

/-- ★★★★★★★ **(a) 的反向（免费）**：`K' ∩ K^{PGL} ≤ K'^N`。

**机制**：`N = T ⋊ S_n ⊆ PGL_n(F)`，故一个**被整个** `PGL` 固定的元素当然被 `diagUnit`／
`permUnit` 固定；再用两条**已机检的等变性**把该固定性搬回 `K'`，最后 `sprToSField` 单射收口。
**不含任何具名输入**；只依赖 `[Field F]`。 -/
theorem sprPGLFixedField_le_sprNFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) :
    sprPGLFixedField F r k₀ hk₀ ≤ sprNFixedField F r 9 := by
  intro x hx
  rw [mem_sprPGLFixedField_iff] at hx
  rw [mem_sprNFixedField_iff]
  have hinj := sprToSField_injective F r 9 k₀ hk₀
  refine ⟨fun b => ?_, fun σ => ?_⟩
  · refine hinj ?_
    rw [sprToSField_sprDiagFieldEquiv F r k₀ hk₀ b x]
    exact hx (diagUnit F b⁻¹)
  · refine hinj ?_
    rw [sprToSField_sprPermFieldEquiv F r k₀ hk₀ σ x]
    exact hx (permUnit F σ⁻¹)

#print axioms sprPGLFixedField_le_sprNFixedField

/-- ★★★★★★★ **`Z` 的像落在 `K'^N` 里**（§29 的 `IntermediateField` 形态重述；免费方向）。 -/
theorem sprCenterImageField_le_sprNFixedField (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprNFixedField F 2 9 := by
  intro x hx
  rw [mem_sprNFixedField_iff]
  exact sprCenterImageField_fixed F 2 9 D k₀ hk₀ x hx

#print axioms sprCenterImageField_le_sprNFixedField

/-- ★★★★★★★ **(b) 比 `hZ` 弱**：`hZ = (K'^N ≤ Z)` ⟹ `(b) = (K' ∩ K^{PGL} ≤ Z)`。

（由 `sprPGLFixedField_le_sprNFixedField` 与传递性。故 (b) **不是**把目标换了个说法。） -/
theorem pglFixed_le_of_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  le_trans (sprPGLFixedField_le_sprNFixedField F 2 k₀ hk₀) hZ

#print axioms pglFixed_le_of_zHalf

/-- ★★★★★★★★ **终局输入因式分解**：`(a) ＋ (b) ⟹ K'^N ⊆ Z`，即 `ZEqNFixed`。 -/
theorem zEqNFixed_of_pglFixed (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (ha : sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀)
    (hb : sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_zHalf_le F D hk₀ (le_trans ha hb)

#print axioms zEqNFixed_of_pglFixed

/-- ★★★★★★★★ **同款终点**：`(a) ＋ (b) ⟹ H2`。 -/
theorem h2_of_pglFixed (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (ha : sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀)
    (hb : sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_zHalf_le F D hk₀ (le_trans ha hb)

#print axioms h2_of_pglFixed

end SprPGLFixed

/-! ## §180 ★★★★★★★★ **把迹域 `sprTraceFrac` 接进 §179 的链**：`K' ∩ Frac(traceAlg) ≤ K' ∩ K^{PGL} ≤ K'^N`

第 655 轮。§179 的中间对象 `sprPGLFixedField`（`K' ∩ K^{PGL}`）是**用 `PGL`-不动性**定义的，
而它要对接的已发表定理（AGPR2020 `thm:14.4.4`）说的是**迹不变量环**。本节把两者接上：

```
K' ∩ Frac(traceAlg)   ≤   K' ∩ K^{PGL}   ≤   K'^N
   (＝ sprTraceFrac)        (＝ sprPGLFixedField)
```

**机制（三步，全是"迹读被固定的矩阵"）**：
1. `trace_psiK`：`tr(ψ_A M) = φ_A(tr M)` —— `ψ_A` 是**共轭**，迹不变（`trace_mul_comm`）；
2. `traceAlg ≤ K^{PGL}`：`traceAlg = adjoin F traceMonoSet`，每个生成元 `tr(w)`
   的矩阵 `∏ genMat` 被 `psiK` 逐点固定（`psiK_prod_genMat`，`FFTRing:60`）⟹ 其迹被固定；
3. 分式层：`pglFixedField` 是**子域**，含 `traceAlg` ⟹ 含其 `adjoin`。

**⟹ 这正是 `FFTRing` §7 标注为"未做"的 `traceAlg` 的不变性**（`FFTRing:52–58`）在 `n = 9` 的落地，
且**不需要** AGPR 的难半边（"不动点 ⊆ 迹代数"）——只用矩阵层的 `psiK_prod_genMat`。

| 件 | 内容 |
|---|---|
| ★★★★★ `trace_psiK` | `tr(ψ_A M) = φ_A(tr M)` |
| ★★★★★ `traceMonoSet_subset_pglFixed` | 迹单项式被整个 `PGL` 固定 |
| ★★★★★ `traceAlg_le_pglFixedField` | **`traceAlg ≤ K^{PGL}`**（`n = 9`） |
| ★★★★★ `traceField_le_pglFixedField` | 其分式域同 |
| ★★★★★★★ **`sprTraceFrac_le_sprPGLFixedField`** | **`K' ∩ Frac(traceAlg) ≤ K' ∩ K^{PGL}`** |
| ★★★★★★ `sprTraceFrac_le_sprNFixedField` | 复合：`K' ∩ Frac(traceAlg) ≤ K'^N` |
| ★★★★★★★★ `h2_of_traceFrac`／`zEqNFixed_of_traceFrac` | **`hZ ⟸ (β1) ＋ (β2)`**（`sprTraceFrac` 为中介） |

**射程（勿夸大）**：本节只给**一个方向** `Frac(traceAlg) ≤ K^{PGL}`（"迹 ⟹ 不变"）。
反向 `K^{PGL} ≤ Frac(traceAlg)`（＝ AGPR `thm:14.4.4` 的实质，即 FFT 的难半边在**分式层**）
**未做**；`(β1)` `K'^N ≤ sprTraceFrac` 与 `(β2)` `sprTraceFrac ≤ Z` **均未证**；
`hZ` 未证；H2 见文件头「当前状态」。 -/

section SprTraceFracBridge

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★ **迹与 `ψ` 的相容性**：`tr(ψ_A M) = φ_A(tr M)`。

**机制**：`ψ_A M = B · M.map(φ_A) · B⁻¹`（`B = constMatK A`）⟹ 迹在**共轭**下不变
（`Matrix.trace_mul_comm`，用 `constMatK_mul` 给 `B⁻¹B = 1`），再用 `tr(M.map φ) = φ(tr M)`。
**注意**：本 pin 的 `Matrix.trace_map` 是**代数等价作用**形态（教训 74），故此处自证 `hmap`。 -/
theorem trace_psiK (F : Type) [Field F] (r n : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (psiK F r n A M).trace = phiKAlgEquiv F r n A M.trace := by
  have hmap : (M.map ⇑((phiKAlgEquiv F r n A).toAlgHom)).trace
      = phiKAlgEquiv F r n A M.trace := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  have hB : constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) :
        Matrix (Fin n) (Fin n) F) * constMatK F r n (↑A) = 1 := by
    rw [constMatK_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, constMatK_one]
  show (constMatK F r n (↑A) * M.map ⇑((phiKAlgEquiv F r n A).toAlgHom)
    * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) :
        Matrix (Fin n) (Fin n) F)).trace
    = phiKAlgEquiv F r n A M.trace
  rw [Matrix.trace_mul_comm (constMatK F r n (↑A) * M.map ⇑((phiKAlgEquiv F r n A).toAlgHom)),
    ← mul_assoc, hB, one_mul, hmap]

#print axioms trace_psiK

/-- ★★★★★ **迹单项式被整个 `PGL_n(F)` 固定**（`traceAlg` 的不变性的生成元层）。 -/
theorem traceMonoSet_subset_pglFixed (F : Type) [Field F] (r : ℕ) :
    traceMonoSet F r 9 ⊆ (pglFixedField F r : Set (SField F r 9)) := by
  rintro _ ⟨w, rfl⟩
  intro A
  rw [← trace_psiK F r 9 A]
  rw [psiK_prod_genMat F r 9 A w]

#print axioms traceMonoSet_subset_pglFixed

/-- ★★★★★ **`traceAlg ≤ K^{PGL}`**（`n = 9`）。

补上 `FFTRing:52–58` 标注为"未做"的**迹代数不变性**：只须矩阵层的 `psiK_prod_genMat`。 -/
theorem traceAlg_le_pglFixedField (F : Type) [Field F] (r : ℕ) :
    traceAlg F r 9 ≤ (pglFixedField F r).toSubalgebra :=
  Algebra.adjoin_le_iff.mpr (traceMonoSet_subset_pglFixed F r)

#print axioms traceAlg_le_pglFixedField

/-- ★★★★★ **`Frac(traceAlg) ≤ K^{PGL}`**（分式层，`pglFixedField` 是子域故取 `adjoin`）。 -/
theorem traceField_le_pglFixedField (F : Type) [Field F] (r : ℕ) :
    IntermediateField.adjoin F (traceAlg F r 9 : Set (SField F r 9)) ≤ pglFixedField F r :=
  IntermediateField.adjoin_le_iff.mpr (fun _ hx => traceAlg_le_pglFixedField F r hx)

#print axioms traceField_le_pglFixedField

/-- ★★★★★★★ **`K' ∩ Frac(traceAlg) ≤ K' ∩ K^{PGL}`**（两个 `comap` 逐个比较）。 -/
theorem sprTraceFrac_le_sprPGLFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) :
    sprTraceFrac F r 9 k₀ hk₀ ≤ sprPGLFixedField F r k₀ hk₀ := by
  intro x hx
  rw [mem_sprPGLFixedField_iff]
  exact traceField_le_pglFixedField F r ((mem_sprTraceFrac_iff F r 9 hk₀).mp hx)

#print axioms sprTraceFrac_le_sprPGLFixedField

/-- ★★★★★★ **复合**：`K' ∩ Frac(traceAlg) ≤ K'^N`（§179 ＋ 本节）。 -/
theorem sprTraceFrac_le_sprNFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) :
    sprTraceFrac F r 9 k₀ hk₀ ≤ sprNFixedField F r 9 :=
  le_trans (sprTraceFrac_le_sprPGLFixedField F r k₀ hk₀)
    (sprPGLFixedField_le_sprNFixedField F r k₀ hk₀)

#print axioms sprTraceFrac_le_sprNFixedField

/-- ★★★★★★★★ **`hZ` 的 `(β1) ＋ (β2)` 形态**（`sprTraceFrac` 作中介的终点）。

```
K'^N ≤ K' ∩ Frac(traceAlg) ≤ Z        （(β1)              （(β2)）
```

**(β2)** 的形状就是 **AGPR2020 `thm:14.4.4`**（`𝒵` ＝ 迹不变量环的分式域）；
**(β1)** 是"`N`-不变量在 `K'` 里是迹有理的"。本节已机检 `K' ∩ Frac(traceAlg) ≤ K'^N`（反向），
故 `(β1)` 与 `(β2)` 之外**无隐藏缺口**。 -/
theorem zEqNFixed_of_traceFrac (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (h2 : sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ZEqNFixed F D :=
  zEqNFixed_of_zHalf_le F D hk₀ (le_trans h1 h2)

#print axioms zEqNFixed_of_traceFrac

/-- ★★★★★★★★ **同款 H2 终点**（`(β1) ＋ (β2) ⟹ H2`）。 -/
theorem h2_of_traceFrac (F : Type) [Field F] [CharZero F]
    (D : GenericDivisionData F 2 9) {k₀ : Fin 2} (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (h2 : sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_zHalf_le F D hk₀ (le_trans h1 h2)

#print axioms h2_of_traceFrac

end SprTraceFracBridge

/-! ## §181 ★★★★★ **`C ≤ P` 的**精确缺口**：需要 `s_c ∈ range(sprToS)`**

第 656 轮。§179 的分解只到"充分"。自然的下一步是补 `C ≤ P`（`Z` 的像 `≤ K' ∩ K^{PGL}`），
若成立则 §179 升级为**精确等价**。**本轮查明它不是免费的**，缺口可被精确命名。

**为什么"看似免费"是错的（本轮实算，务必记住）**：
`sprCenterImageField` 的生成元是 `algebraMap (sprCenterK c)`，而
`sprCenterK = evSpr ∘ sprCenterPolyAlgHom`（`H2Final:2815`），`sprCenterPolyAlgHom c = s_c`。
于是
```
sprToSField (algebraMap (sprCenterK c)) = algebraMap (sprToS (evSpr s_c)) .
```
曾有两条"缩回"容易混淆：
* `evSpr ∘ sprToS = id`（`evSpr_comp_sprToS`，`GenericInv:10157`）——**它是**真的；
* `sprToS ∘ evSpr = id` —— **它不真**：`evSpr` 把 `x_{k₀,i,j}`（`i ≠ j`）**杀成 0**，
  只留对角 `x_{k₀,i,i}` 与全部 `y_ijk`，故 `sprToS ∘ evSpr` 是**对角化**（幂等但不是恒等）。

⟹ `sprToSField (algebraMap (sprCenterK c)) = centK c` **一般不成立**；
它成立的**充要条件**正是 `s_c ∈ range(sprToS)`，即
「中心的纯量多项式只用到对角 `x_{k₀}` 与全部 `y_ijk`」——
这是 §24 的射程里**已标注未证**的那条（"中心不变量被'对角线 ＋ 其余通用矩阵'生成"），
也是源文 `prop:14.19` 的核心困难。

| 件 | 内容 |
|---|---|
| ★★★★★ `algebraMap_sprCenterPolyK_eq_centK` | **`algebraMap s_c = centK c`**（无条件；`c.1 = scalar s_c` 的纯量矩阵读回） |
| ★★★★ `sprToS_evSpr_sprToS` | 幂等：`sprToS (evSpr (sprToS z)) = sprToS z` |
| ★★★★★ `sprToS_sprCenterK_of_range` | 条件版：`s_c ∈ range(sprToS)` ⟹ `sprToS (sprCenterK c) = s_c` |
| ★★★★★★★ `sprCenterImageField_le_sprPGLFixedField_of_range` | 条件版 **`C ≤ P`** |

**射程（勿夸大）**：`∀ c, s_c ∈ range(sprToS)` **未证**（＝源文核心困难）；
故 `C ≤ P` **未证**；§179 仍是**充分**分解（`(a) ∧ (b) ⟹ hZ`，`hZ ⟹ (b)`），
**不是** `hZ ⟺ (a) ∧ (b)`；`hZ` 未证；H2 见文件头「当前状态」。 -/

section SprZImagePGLGap

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★ **`algebraMap s_c = centK c`**（无条件）。

`sprCenterPolyK_spec` 给 `c.1 = scalar s_c`；`centK_spec` 给 `c.1.map = scalar (centK c)`；
`Matrix.map` 与 `scalar` 交换 ⟹ 两侧 `scalar` 相等 ⟹ `Matrix.scalar_inj` 收口。 -/
theorem algebraMap_sprCenterPolyK_eq_centK (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (c : ↥(genericCenter F 2 9)) :
    algebraMap (S F 2 9) (SField F 2 9) (sprCenterPolyK F 2 9 D c) = D.centK c := by
  have hA := D.centK_spec c
  rw [sprCenterPolyK_spec F 2 9 D c] at hA
  have hmap : (Matrix.scalar (Fin 9) (sprCenterPolyK F 2 9 D c)).map
        (algebraMap (S F 2 9) (SField F 2 9))
      = Matrix.scalar (Fin 9)
          (algebraMap (S F 2 9) (SField F 2 9) (sprCenterPolyK F 2 9 D c)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.scalar]
    · simp [Matrix.scalar, h]
  rw [hmap] at hA
  exact (Matrix.scalar_inj (n := Fin 9)).mp hA

#print axioms algebraMap_sprCenterPolyK_eq_centK

/-- ★★★★ **`sprToS ∘ evSpr` 是幂等的**（`evSpr ∘ sprToS = id` 的即时推论）。

**注意它**不是**恒等**：`evSpr` 把多余的对角化掉，故 `sprToS (evSpr s) = s` 只对
`s ∈ range (sprToS)` 成立。 -/
theorem sprToS_evSpr_sprToS (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (z : Spr F r 9) :
    sprToS (F := F) (r := r) (n := 9) k₀ (evSpr F r 9 k₀ hk₀
        (sprToS (F := F) (r := r) (n := 9) k₀ z))
      = sprToS (F := F) (r := r) (n := 9) k₀ z := by
  have h := DFunLike.congr_fun
    (evSpr_comp_sprToS (F := F) (r := r) (n := 9) k₀ hk₀) z
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at h
  rw [h]

#print axioms sprToS_evSpr_sprToS

/-- ★★★★★ **条件版接线**：若中心纯量 `s_c` 落在 `range (sprToS)` 里，
则 `sprToS (sprCenterK c) = s_c`。

**证明**：`h` 给 `z` 使 `sprToS z = s_c`；于是 `evSpr s_c = evSpr (sprToS z) = z`
（`evSpr_comp_sprToS`），再 `sprToS z = s_c` 收口。 -/
theorem sprToS_sprCenterK_of_range (F : Type) [Field F] [Nonempty (Fin 9)]
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) (D : GenericDivisionData F 2 9)
    (h : ∀ c : ↥(genericCenter F 2 9),
      ∃ z : Spr F 2 9, sprToS (F := F) (r := 2) (n := 9) k₀ z = sprCenterPolyK F 2 9 D c)
    (c : ↥(genericCenter F 2 9)) :
    sprToS (F := F) (r := 2) (n := 9) k₀
        (sprCenterK (F := F) (r := 2) (n := 9) k₀ hk₀ D c)
      = sprCenterPolyK F 2 9 D c := by
  obtain ⟨z, hz⟩ := h c
  have h1 : evSpr F 2 9 k₀ hk₀ (sprCenterPolyAlgHom F 2 9 D c) = z := by
    have h2 := DFunLike.congr_fun
      (evSpr_comp_sprToS (F := F) (r := 2) (n := 9) k₀ hk₀) z
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at h2
    rw [hz] at h2
    exact h2
  show sprToS (F := F) (r := 2) (n := 9) k₀
    (evSpr F 2 9 k₀ hk₀ (sprCenterPolyAlgHom F 2 9 D c)) = sprCenterPolyK F 2 9 D c
  rw [h1, hz]

#print axioms sprToS_sprCenterK_of_range

/-- ★★★★★★★ **条件版 `C ≤ P`**：`∀ c, s_c ∈ range(sprToS)` ⟹ `Z` 的像 `≤ K' ∩ K^{PGL}`。

**这精确地命名了 `C ≤ P` 的缺口**——缺口不是关于 `PGL` 的，而是关于**中心纯量多边形的坐标**
（源文 `prop:14.19` 的核心困难）。 -/
theorem sprCenterImageField_le_sprPGLFixedField_of_range (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h : ∀ c : ↥(genericCenter F 2 9),
      ∃ z : Spr F 2 9, sprToS (F := F) (r := 2) (n := 9) k₀ z = sprCenterPolyK F 2 9 D c) :
    sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨c, rfl⟩
  refine (mem_sprPGLFixedField_iff F 2 hk₀).mpr ?_
  intro A
  rw [sprToSField_algebraMap (F := F) (r := 2) (n := 9) k₀ hk₀,
    sprToS_sprCenterK_of_range (F := F) k₀ hk₀ D h c,
    algebraMap_sprCenterPolyK_eq_centK F D c]
  exact phiK_fixes_centK F 2 9 D A c

#print axioms sprCenterImageField_le_sprPGLFixedField_of_range

end SprZImagePGLGap

/-! ## §182 ★★★★★★★ **蕴含格（wall map）**：五个候选输入之间的**全部**已证蕴含

第 657 轮。R654–R656 产生了五个"候选输入"，散落在 §178–§181。本节把**它们之间的全部蕴含**
机检成一张格，使后续轮次**不再需要在它们之间猜**。

四个对象（都是 `IntermediateField F (SprField F 2 9)`）：

| 记号 | 对象 | 定义处 |
|---|---|---|
| `C` | `sprCenterImageField`（`ZCanon` 的 `Spr` 世界版，由 `sprCenterK` 生成） | `H2Final:3881` |
| `T` | `sprTraceFrac`（`K' ∩ Frac(traceAlg)`，沿 `sprToSField` 取原像） | `FFTRing:1024` |
| `P` | `sprPGLFixedField`（`K' ∩ K^{PGL}`） | `H2Final:9991` |
| `N` | `sprNFixedField`（`K'^N`） | `FFTRing:637` |

**已机检的排序**：`C ≤ N`（§29）、`T ≤ P`（§180）、`P ≤ N`（§179）。
**`C` 与 `T` 之间无已知序**——这正是全部困难的所在。

| 候选输入 | 陈述 | 状态 |
|---|---|---|
| `hZ` | `N ≤ C` | 未证 |
| `(β1)` | `N ≤ T` | 未证 |
| `(β2)` | `T ≤ C` | 未证 |

**格（本节机检的六条边 ＋ 三条既有排序）**：

```
        C  ──── (β2) ────►  T          C ≤ N  ✓§29
        ▲                   │          T ≤ P  ✓§180
   hZ   │                   │ (β1)     P ≤ N  ✓§179
        │                   ▼
        N  ◄──── (a) ────  P
```

| 件 | 内容 |
|---|---|
| ★★★★★★ `zHalf_iff_eq` | **`hZ ⟺ N = C`**（最简等式形态；`C ≤ N` 已机检） |
| ★★★★★★ `pglFixed_imp_of_traceFrac` | **`(β1) ⟹ (a)`**（`N ≤ T ≤ P`） |
| ★★★★★★ `traceFrac_le_zHalf_of` | **`hZ ⟹ (β2)`**（`T ≤ P ≤ N ≤ C`） |
| ★★★★★★ `pglFixed_le_of_beta` | **`(β1) ∧ (β2) ⟹ (b)`**（`P ≤ N ≤ T ≤ C`） |
| ★★★★★★★ `beta_imp_a_and_b` | **`(β1) ∧ (β2) ⟹ (a) ∧ (b)`** |
| ★★★★★★★★ `zHalf_of_beta` | **`(β1) ∧ (β2) ⟹ hZ`**（故 `(β)`-分解**细分** `(a)/(b)`-分解） |

**★ 格的确切读法（勿夸大）**：
* `(β1) ∧ (β2) ⟹ hZ`（强，`zHalf_of_beta`）；
* `hZ ⟹ (β2)`（`traceFrac_le_zHalf_of`）；
* **`hZ ⇏ (β1)`** 未机检亦未知 ⟹ **不得声称** `hZ ⟺ (β1) ∧ (β2)`。
  正确的等式形态是 `(β1) ∧ (β2) ⟺ hZ ∧ (β1)`，而 `(β1)` 是**额外**的那一条。
* ⟹ **后续轮次只需攻 `(β1)` 与 `(β2)`；且 `(β1)` 一旦到手，(β2) 是唯一余项。**

**射程（勿夸大）**：(β1)、(β2) **均未证**；`hZ` 未证；H2 见文件头「当前状态」。
本节是**逻辑化简**，不含新的数学内容。 -/

section SprWallMap

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★ **`hZ` 的最简等式形态**：`K'^N ⊆ Z` ⟺ `K'^N = Z`（因 `Z ⊆ K'^N` 已机检）。 -/
theorem zHalf_iff_eq (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    (sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ↔ sprNFixedField F 2 9 = sprCenterImageField F 2 9 D k₀ hk₀ := by
  constructor
  · intro hZ
    exact le_antisymm hZ (sprCenterImageField_le_sprNFixedField F D k₀ hk₀)
  · intro h
    rw [h]

#print axioms zHalf_iff_eq

/-- ★★★★★★ **`(β1) ⟹ (a)`**：`N ≤ T` 且 `T ≤ P` ⟹ `N ≤ P`。 -/
theorem pglFixed_imp_of_traceFrac (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀) :
    sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀ :=
  le_trans h1 (sprTraceFrac_le_sprPGLFixedField F r k₀ hk₀)

#print axioms pglFixed_imp_of_traceFrac

/-- ★★★★★★ **`hZ ⟹ (β2)`**：`T ≤ P ≤ N ≤ C`。 -/
theorem traceFrac_le_zHalf_of (F : Type) [Field F] (r : ℕ)
    {D : GenericDivisionData F r 9} {k₀ : Fin r} (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F r 9 ≤ sprCenterImageField F r 9 D k₀ hk₀) :
    sprTraceFrac F r 9 k₀ hk₀ ≤ sprCenterImageField F r 9 D k₀ hk₀ :=
  le_trans (sprTraceFrac_le_sprPGLFixedField F r k₀ hk₀)
    (le_trans (sprPGLFixedField_le_sprNFixedField F r k₀ hk₀) hZ)

#print axioms traceFrac_le_zHalf_of

/-- ★★★★★★ **`(β1) ∧ (β2) ⟹ (b)`**：`P ≤ N ≤ T ≤ C`。 -/
theorem pglFixed_le_of_beta (F : Type) [Field F] (r : ℕ)
    {D : GenericDivisionData F r 9} {k₀ : Fin r} (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀)
    (h2 : sprTraceFrac F r 9 k₀ hk₀ ≤ sprCenterImageField F r 9 D k₀ hk₀) :
    sprPGLFixedField F r k₀ hk₀ ≤ sprCenterImageField F r 9 D k₀ hk₀ :=
  le_trans (sprPGLFixedField_le_sprNFixedField F r k₀ hk₀) (le_trans h1 h2)

#print axioms pglFixed_le_of_beta

/-- ★★★★★★★ **`(β1) ∧ (β2) ⟹ (a) ∧ (b)`**：`(β)`-分解**细分** `(a)/(b)`-分解。 -/
theorem beta_imp_a_and_b (F : Type) [Field F] (r : ℕ)
    {D : GenericDivisionData F r 9} {k₀ : Fin r} (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀)
    (h2 : sprTraceFrac F r 9 k₀ hk₀ ≤ sprCenterImageField F r 9 D k₀ hk₀) :
    (sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀)
      ∧ (sprPGLFixedField F r k₀ hk₀ ≤ sprCenterImageField F r 9 D k₀ hk₀) :=
  ⟨pglFixed_imp_of_traceFrac F r k₀ hk₀ h1, pglFixed_le_of_beta F r hk₀ h1 h2⟩

#print axioms beta_imp_a_and_b

/-- ★★★★★★★★ **`(β1) ∧ (β2) ⟹ hZ`**（格的最强边）。

**⟹ 后续轮次只需攻 `(β1)` 与 `(β2)` 两条。** 反向 `hZ ⟹ (β2)` 亦已机检
（`traceFrac_le_zHalf_of`），但 `hZ ⇏ (β1)` 未知，故**不**称等价。 -/
theorem zHalf_of_beta (F : Type) [Field F] (r : ℕ)
    {D : GenericDivisionData F r 9} {k₀ : Fin r} (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀)
    (h2 : sprTraceFrac F r 9 k₀ hk₀ ≤ sprCenterImageField F r 9 D k₀ hk₀) :
    sprNFixedField F r 9 ≤ sprCenterImageField F r 9 D k₀ hk₀ :=
  le_trans h1 h2

#print axioms zHalf_of_beta

end SprWallMap

/-! ## §183 ★★★★★★ **R656 的墙化成一可计算等式**：`sprToS (evSpr s_c) = s_c`

第 658 轮。R657 的 wall map §5 曾把 `(β2)` 的"最省起点"指为**分式层 FFT**
（`K^{PGL} = Frac(traceAlg)`）。本轮侦察发现**该指路不完整**：

* `(β2) = (T ≤ C)`，`T = comap_{sprToSField}(Frac(traceAlg))`，`C = adjoin F (image (algebraMap ∘ sprCenterK))`；
* 若用 AGPR `thm:14.4.4` 把 `Frac(traceAlg)` 识别为 `ZCanon`，则 `(β2)` 变成 `comap(ZCanon) ≤ C`；
* 而这需要 `sprToSField '' C ⊆ ZCanon`，即 `algebraMap (sprToS (evSpr s_c)) ∈ ZCanon`——
  **又是 `sprToS ∘ evSpr` 作用在 `s_c` 上**。

**⟹ R656 的墙不是旁支，而是 `(β2)`／`(γ)` 的必经之路。** 故本轮把它化成一个**可计算的等式**：

```
     ∃ z : Spr, sprToS z = s_c        ⟺        sprToS (evSpr s_c) = s_c
     （"s_c 落在 range(sprToS) 里"）              （"s_c 的对角化就是它自己"）
```

右端是**可下手**的形态：它只谈 `s_c` 的**支撑**（不含 `x_{k₀,i,j}`，`i ≠ j`），
可用 `MvPolynomial` 的系数逐点核（`coeff`），也可用 `sprToS`／`evSpr` 的变量公式展开。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprToS_evSpr_eq_self_iff` | **等价形态**：`(∃ z, sprToS z = s) ↔ sprToS (evSpr s) = s` |
| ★★★★★★ `CenterPolyDiagHyp` | **具名输入**：`∀ c, sprToS (evSpr s_c) = s_c`（＝中心纯量无偏离对角项） |
| ★★★★★★★ `sprCenterImageField_le_sprPGLFixedField_of_diag` | `CenterPolyDiagHyp ⟹ C ≤ P`（重述 §181 的条件件） |

**射程（勿夸大）**：`CenterPolyDiagHyp` **未证**；它等价于 §181 的 `s_c ∈ range(sprToS)`，
也等价于源文 `prop:14.19` 的核心困难（经 `lem:14.21／14.22` 的 `R ↪ M_n(S')` 识别）。
`hZ` 未证；H2 见文件头「当前状态」。 -/

section SprCenterPolyDiag

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★ **`range (sprToS)` 的两种刻画**：`s` 落在 `sprToS` 的像里 ⟺ `sprToS (evSpr s) = s`。

`⟸` 取 `z := evSpr s`；`⟹` 若 `s = sprToS z`，则 `evSpr s = evSpr (sprToS z) = z`
（`evSpr_comp_sprToS`），故 `sprToS (evSpr s) = sprToS z = s`。
**这是把 R656 的墙变成可计算等式的关键**：右端只涉及 `s` 的变量支撑。 -/
theorem sprToS_evSpr_eq_self_iff (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (s : S F r 9) :
    (∃ z : Spr F r 9, sprToS (F := F) (r := r) (n := 9) k₀ z = s)
      ↔ sprToS (F := F) (r := r) (n := 9) k₀ (evSpr F r 9 k₀ hk₀ s) = s := by
  constructor
  · rintro ⟨z, rfl⟩
    have h := DFunLike.congr_fun
      (evSpr_comp_sprToS (F := F) (r := r) (n := 9) k₀ hk₀) z
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at h
    show sprToS (F := F) (r := r) (n := 9) k₀
      (evSpr F r 9 k₀ hk₀ (sprToS (F := F) (r := r) (n := 9) k₀ z)) = _
    rw [h]
  · intro h
    exact ⟨evSpr F r 9 k₀ hk₀ s, h⟩

#print axioms sprToS_evSpr_eq_self_iff

/-- ★★★★★★ **具名输入（中心纯量的对角化不动性）**：
中心元的纯量多项式 `s_c` 不含偏离对角项 `x_{k₀,i,j}`（`i ≠ j`），
等价地 `sprToS (evSpr s_c) = s_c`（见 `sprToS_evSpr_eq_self_iff`）。

**这是 R656 的墙的可计算形态**，也是 `C ≤ P` 与 `(β2)` 的共同入口。
它在数学上的内容 ＝「中心不变量被『对角线 ＋ 其余通用矩阵』生成」，
源文 `prop:14.19` 的核心困难（须经 `lem:14.21／14.22` 的 `R ↪ M_n(S')`）。 -/
def CenterPolyDiagHyp (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ c : ↥(genericCenter F 2 9),
    sprToS (F := F) (r := 2) (n := 9) k₀
      (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D c))
      = sprCenterPolyK F 2 9 D c

#print axioms CenterPolyDiagHyp

/-- ★★★★★★★ **`CenterPolyDiagHyp ⟹ C ≤ P`**（§181 条件件在等式形态下的重述）。

**这把 R656 的墙与终局输入直接连上**：墙一破，`C ≤ P` 即得。 -/
theorem sprCenterImageField_le_sprPGLFixedField_of_diag (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h : CenterPolyDiagHyp F D k₀ hk₀) :
    sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀ :=
  sprCenterImageField_le_sprPGLFixedField_of_range F D k₀ hk₀
    (fun c => ⟨evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D c), h c⟩)

#print axioms sprCenterImageField_le_sprPGLFixedField_of_diag

end SprCenterPolyDiag

/-! ## §184 ★★★★★★ **R658 的具名输入的诚实弱化 ＋ 可证伪性审计**

第 659 轮。R658 把 R656 的墙写成 `CenterPolyDiagHyp`（`sprToS (evSpr s_c) = s_c`）。
本轮做**可证伪性审计**，结论：**`CenterPolyDiagHyp` 对 `n = 9, r = 2` 是假的**，
故它**不能**作为具名输入；诚实输入是严格更弱的 `CenterPolyPGLHyp`。

**反例（`det(X_1)`，`n ≥ 2`）**：
1. `genericCenter = Subalgebra.center R`（`GenericMatrix:90`），而 `det(X_1)·I ∈ R`（Cayley–Hamilton
   的 `c_n` 项显式含 `I`）且是纯量矩阵 ⟹ `det(X_1) ∈ C(R)`；
2. 故存在 `c` 使 `s_c = det(X_1)`（`sprCenterPolyK_spec` 的纯量矩阵唯一性）；
3. `det(X_1)` 的展开含偏离对角单项式（如 `x_{0,1,2} x_{0,2,1} ∏…`），而
   `evSpr` 把 `x_{k₀,i,j}`（`i ≠ j`）**杀成 0** ⟹ `evSpr s_c = ∏_i x_{0,i,i}`（对角元之积），
   再 `sprToS` 复原 ⟹ `sprToS (evSpr s_c) = ∏_i x_{0,i,i} ≠ det(X_1) = s_c`。

**⟹ `CenterPolyDiagHyp` 假**；但 `C ≤ P` **不一定**假（`C` 的生成元的像是
`algebraMap (sprToS (evSpr s_c))`，它可能仍被 `PGL` 固定，只是**不等于** `centK c`）。
⟹ 诚实输入 = **`algebraMap (sprToS (evSpr s_c)) ∈ pglFixedField`**（`CenterPolyPGLHyp`），
它**不需要** `sprToS ∘ evSpr` 是恒等。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprToSField_sprCenterK_eq` | **`C` 的生成元的像之精确值**：`= algebraMap (sprToS (evSpr s_c))`（**无条件**） |
| ★★★★★★ `CenterPolyPGLHyp` | **诚实具名输入**：该像落在 `pglFixedField` 里 |
| ★★★★★★★ `sprCenterImageField_le_sprPGLFixedField_of_pgl` | `CenterPolyPGLHyp ⟹ C ≤ P` |
| ★★★★★★ `centerPolyPGLHyp_of_diag` | **层级**：`CenterPolyDiagHyp ⟹ CenterPolyPGLHyp`（故 R658 的输入**严格更强**且**假**） |

**射程（勿夸大）**：`CenterPolyPGLHyp` **未证**；`C ≤ P` 未证；`hZ` 未证；H2 见文件头「当前状态」。
**R658 的 `CenterPolyDiagHyp` 应视为作废（假）**，仅保留其作为"过强形态"的记录。 -/

section SprCenterPolyAudit

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★ **`C` 的生成元的像之精确值**（**无条件**）：
`sprToSField (algebraMap (sprCenterK c)) = algebraMap (sprToS (evSpr s_c))`。

这是 R656 之后**正确的分解式**：右端的 `sprToS (evSpr s_c)` 是 `s_c` 的**对角化**，
一般**不等于** `s_c`（R658 的 `CenterPolyDiagHyp` 断言的正是那个等号，见 §184 文档的 `det(X_1)` 反例）。 -/
theorem sprToSField_sprCenterK_eq (F : Type) [Field F] [Nonempty (Fin 9)]
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) (D : GenericDivisionData F 2 9)
    (c : ↥(genericCenter F 2 9)) :
    sprToSField (F := F) (r := 2) (n := 9) k₀ hk₀
        (algebraMap (Spr F 2 9) (SprField F 2 9)
          (sprCenterK (F := F) (r := 2) (n := 9) k₀ hk₀ D c))
      = algebraMap (S F 2 9) (SField F 2 9)
          (sprToS (F := F) (r := 2) (n := 9) k₀
            (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D c))) := by
  rw [sprToSField_algebraMap (F := F) (r := 2) (n := 9) k₀ hk₀]
  rfl

#print axioms sprToSField_sprCenterK_eq

/-- ★★★★★★ **诚实具名输入**：中心纯量的**对角化**在 `K` 里的像是 `PGL`-不变的。

**为何这是诚实形态**：它**不**要求 `sprToS (evSpr s_c) = s_c`（后者假，见 `det(X_1)` 反例），
只要求其 `algebraMap`-像是在 `pglFixedField` 里。这是 `C ≤ P` 的**精确**充分条件。 -/
def CenterPolyPGLHyp (F : Type) [Field F] (D : GenericDivisionData F 2 9)
    (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ c : ↥(genericCenter F 2 9),
    algebraMap (S F 2 9) (SField F 2 9)
      (sprToS (F := F) (r := 2) (n := 9) k₀
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D c)))
      ∈ pglFixedField F 2

#print axioms CenterPolyPGLHyp

/-- ★★★★★★★ **`CenterPolyPGLHyp ⟹ C ≤ P`**（`C` 的生成元的像由 `sprToSField_sprCenterK_eq` 精确给出）。 -/
theorem sprCenterImageField_le_sprPGLFixedField_of_pgl (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h : CenterPolyPGLHyp F D k₀ hk₀) :
    sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨c, rfl⟩
  refine (mem_sprPGLFixedField_iff F 2 hk₀).mpr ?_
  intro A
  rw [sprToSField_sprCenterK_eq (F := F) k₀ hk₀ D c]
  exact h c A

#print axioms sprCenterImageField_le_sprPGLFixedField_of_pgl

/-- ★★★★★★ **层级**：R658 的 `CenterPolyDiagHyp` **蕴含**本节的诚实输入。

（因 `sprToS (evSpr s_c) = s_c` 时右端退化为 `algebraMap s_c = centK c`，而后者被 `PGL` 固定
——`phiK_fixes_centK`。**但反过来不成立**，且 `CenterPolyDiagHyp` 本身假（`det(X_1)` 反例）。） -/
theorem centerPolyPGLHyp_of_diag (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h : CenterPolyDiagHyp F D k₀ hk₀) : CenterPolyPGLHyp F D k₀ hk₀ := by
  intro c A
  rw [h c, algebraMap_sprCenterPolyK_eq_centK F D c]
  exact phiK_fixes_centK F 2 9 D A c

#print axioms centerPolyPGLHyp_of_diag

end SprCenterPolyAudit

/-! ## §185 ★★★★★★★ **`C ≤ P` 本身是假命题** —— R656–R659 的"墙"整条作废

第 660 轮。按教训 88（具名输入须在命名当轮做可实现性审计），对 R659 提出的"诚实输入"
`CenterPolyPGLHyp` 做事前审计。**结论：`CenterPolyPGLHyp` 与 `C ≤ P` 是同一件事，且两者都假。**

**反例（`n = 9`，取 `s_c = det(X_1)`）**：
1. `genericCenter = Subalgebra.center R`（`GenericMatrix:90`）；Cayley–Hamilton 的常数项给
   `det(X_1)·I ∈ R` 且是纯量矩阵 ⟹ `det(X_1) ∈ C(R)`，故存在 `c` 使 `s_c = det(X_1)`；
2. `sprToS (evSpr s_c) = ∏_i x_{0,i,i}`（对角化把 Leibniz 展开里的偏离对角项全杀掉，
   只留恒等置换项）；
3. 故 `C` 的生成元的 `sprToSField`-像是 `algebraMap (∏_i x_{0,i,i})`；
4. **`∏_i x_{0,i,i}` 不是 `PGL`-不变的**：取 `n = 2`、`A = [[1,1],[0,1]]`（`n = 9` 时用同一
   转置矩阵作用在 `0,1` 两指标上），则
   `(A⁻¹XA)_{11} = x_{11} − x_{21}`、`(A⁻¹XA)_{22} = x_{21} + x_{22}`，
   故 `φ_A(x_{11}x_{22}) = (x_{11}−x_{21})(x_{21}+x_{22}) ≠ x_{11}x_{22}`；
5. **⟹ `algebraMap (∏_i x_{0,i,i}) ∉ pglFixedField`** ⟹ 该生成元 ∉ `P` ⟹ **`C ⊄ P`**。

**⟹ 整条 `C ≤ P` 路线（R656 的"墙"、R658 的 `CenterPolyDiagHyp`、R659 的 `CenterPolyPGLHyp`）
全部作废**，不是"难"，是**假**。同理 `(γ)`（`C ≤ T`）也假：`C ≤ T` ＋ `T ≤ P`（已机检）
⟹ `C ≤ P`，与 4 矛盾。

**⟹ 诚实剩余目标回到 R654 的 `(a) ∧ (b)`**（`(a) = N ≤ P`、`(b) = P ≤ C`；
`(b)` 与 `C ≤ P` **不矛盾**：`(b)` 是 `P ⊆ C`，而被证伪的是 `C ⊆ P`）。

| 件 | 内容 |
|---|---|
| ★★★★★★ `centerPolyPGLHyp_of_cLeP` | **反向**：`C ≤ P ⟹ CenterPolyPGLHyp` |
| ★★★★★★★ `cLeP_iff_centerPolyPGLHyp` | **`C ≤ P ⟺ CenterPolyPGLHyp`**（故两者同真同假） |
| ★★★★★★ `cLeP_of_cLeT` | **`C ≤ T ⟹ C ≤ P`**（`(γ)` 的死亡证明；配 `T ≤ P`） |

**射程（勿夸大）**：反例 1–5 是**论证级**（未机检；构造具体 `c` 与 `det` 展开超预算），
标 `⚠-contentious`。`(a)`／`(b)`／`hZ` 均未证；H2 见文件头「当前状态」。 -/

section SprCenterChainLeP

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★ **反向**：`C ≤ P ⟹ CenterPolyPGLHyp`（生成元逐个取出 ＋ `sprToSField_sprCenterK_eq`）。 -/
theorem centerPolyPGLHyp_of_cLeP (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h : sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀) :
    CenterPolyPGLHyp F D k₀ hk₀ := by
  intro c
  have hgen : algebraMap (Spr F 2 9) (SprField F 2 9)
      (sprCenterK (F := F) (r := 2) (n := 9) k₀ hk₀ D c) ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
    IntermediateField.subset_adjoin F _ (Set.mem_range_self c)
  have hP := h hgen
  rw [mem_sprPGLFixedField_iff] at hP
  rw [sprToSField_sprCenterK_eq (F := F) k₀ hk₀ D c] at hP
  exact mem_pglFixedField_iff F 2 |>.mpr hP

#print axioms centerPolyPGLHyp_of_cLeP

/-- ★★★★★★★ **`C ≤ P` ⟺ `CenterPolyPGLHyp`**（故两者**同真同假**）。 -/
theorem cLeP_iff_centerPolyPGLHyp (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀
      ↔ CenterPolyPGLHyp F D k₀ hk₀ :=
  ⟨centerPolyPGLHyp_of_cLeP F D k₀ hk₀,
   sprCenterImageField_le_sprPGLFixedField_of_pgl F D k₀ hk₀⟩

#print axioms cLeP_iff_centerPolyPGLHyp

/-- ★★★★★★ **`(γ)` 的死亡证明**：`C ≤ T` ⟹ `C ≤ P`（配已机检的 `T ≤ P`）。

⟹ 一旦 `C ≤ P` 被证伪（§185 文档的 `∏_i x_{0,i,i}` 反例），`(γ)` 也随之**作废**。 -/
theorem cLeP_of_cLeT (F : Type) [Field F] (r : ℕ) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {D : GenericDivisionData F r 9}
    (h : sprCenterImageField F r 9 D k₀ hk₀ ≤ sprTraceFrac F r 9 k₀ hk₀) :
    sprCenterImageField F r 9 D k₀ hk₀ ≤ sprPGLFixedField F r k₀ hk₀ :=
  le_trans h (sprTraceFrac_le_sprPGLFixedField F r k₀ hk₀)

#print axioms cLeP_of_cLeT

end SprCenterChainLeP

/-! ## §186 ★★★★★★★★ **蕴含格升级为等价格**（第 661 轮）——「一条到手，另一条就是唯一余项」

§182 给的是**单向**边：`(β1) ∧ (β2) ⟹ hZ`、`hZ ⟹ (β2)`、`(a) ∧ (b) ⟹ hZ`、`hZ ⟹ (b)`。
故 §182 的"确切读法"只能写「`(β1)` 一旦到手，`(β2)` 是唯一余项」——**那是一句自然语言**，
不是机检的 `iff`。本节把它机检成 **`iff`**：补上**一条**前提后，`hZ` 与另一条**同真同假**。

**六件（不含新数学内容：全部是 §179／§180／§182 已有边的两两配对）**：

| 件 | 内容 | 读法 |
|---|---|---|
| ★★★★★★ `zHalf_iff_beta2_of_beta1` | **`(β1) ⟹ (hZ ⟺ (β2))`** | `(β1)` 到手 ⟹ 唯一余项就是 `(β2)` |
| ★★★★★★ `zHalf_iff_b_of_a` | **`(a) ⟹ (hZ ⟺ (b))`** | `(a)`／`(b)` 分支的对称版 |
| ★★★★★★ `zHalf_iff_b_of_beta1` | **`(β1) ⟹ (hZ ⟺ (b))`** | `(β1)` 自动打穿 `(a)` |
| ★★★★★★ `beta1_iff_a_of_P_le_T` | **`(P ≤ T) ⟹ ((β1) ⟺ (a))`** | `T = P` 到手 ⟹ 两分解**合并** |
| ★★★★★★ `beta2_iff_b_of_P_le_T` | **`(P ≤ T) ⟹ ((β2) ⟺ (b))`** | 同上 |
| ★★★★★★ `beta_iff_a_and_b_of_P_le_T` | **`(P ≤ T) ⟹ ((β1) ∧ (β2) ⟺ (a) ∧ (b))`** | 合取版 |

**为何有用**：它把 R657 的 wall map 从「证明义务格」升级为「**等价格**」，
于是"攻哪一条"的问题化为"**哪一条已有进展**"的问题（凡一侧到手，另一侧即刻成为等价目标）。

**注意 `P ≤ T` 未证**：已机检的只有反向 `T ≤ P`（`sprTraceFrac_le_sprPGLFixedField`）。
本节**不声称** `T = P`，只把它作为**条件**。

**射程（勿夸大）**：`(a)`／`(b)`／`(β1)`／`(β2)`／`hZ` **均未证**；H2 见文件头「当前状态」。 -/

section SprWallMapIff

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★ **`(β1) ⟹ (hZ ⟺ (β2))`**：`hZ ⟹ (β2)` 是 §182 的 `traceFrac_le_zHalf_of`；
反向 `(β2) ⟹ hZ` 只需 `N ≤ T`（即 `(β1)`）。 -/
theorem zHalf_iff_beta2_of_beta1 (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀) :
    (sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ↔ sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  constructor
  · exact traceFrac_le_zHalf_of (F := F) (r := 2) (D := D) (k₀ := k₀) hk₀
  · intro h2
    exact le_trans h1 h2

#print axioms zHalf_iff_beta2_of_beta1

/-- ★★★★★★ **`(a) ⟹ (hZ ⟺ (b))`**：`hZ ⟹ (b)` 是 `pglFixed_le_of_zHalf`；
反向 `(b) ⟹ hZ` 只需 `N ≤ P`（即 `(a)`）。 -/
theorem zHalf_iff_b_of_a (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (ha : sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀) :
    (sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ↔ sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  constructor
  · exact pglFixed_le_of_zHalf F D k₀ hk₀
  · intro hb
    exact le_trans ha hb

#print axioms zHalf_iff_b_of_a

/-- ★★★★★★ **`(β1) ⟹ (hZ ⟺ (b))`**：`(β1)` 先给 `(a)`（`pglFixed_imp_of_traceFrac`），
再用 `zHalf_iff_b_of_a`。 -/
theorem zHalf_iff_b_of_beta1 (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀) :
    (sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ↔ sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  constructor
  · exact pglFixed_le_of_zHalf F D k₀ hk₀
  · intro hb
    exact le_trans (pglFixed_imp_of_traceFrac F 2 k₀ hk₀ h1) hb

#print axioms zHalf_iff_b_of_beta1

/-- ★★★★★★ **`(P ≤ T) ⟹ ((β1) ⟺ (a))`**：`T ≤ P` 已机检，故 `P ≤ T` 即 `T = P`；
此时 `N ≤ T` 与 `N ≤ P` 等价。 -/
theorem beta1_iff_a_of_P_le_T (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0)
    (hPT : sprPGLFixedField F r k₀ hk₀ ≤ sprTraceFrac F r 9 k₀ hk₀) :
    (sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀)
      ↔ sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀ := by
  constructor
  · exact pglFixed_imp_of_traceFrac F r k₀ hk₀
  · intro ha
    exact le_trans ha hPT

#print axioms beta1_iff_a_of_P_le_T

/-- ★★★★★★ **`(P ≤ T) ⟹ ((β2) ⟺ (b))`**：`T ≤ P` 已机检，故 `(β2)`（`T ≤ C`）在
`T = P` 时与 `(b)`（`P ≤ C`）等价。 -/
theorem beta2_iff_b_of_P_le_T (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hPT : sprPGLFixedField F 2 k₀ hk₀ ≤ sprTraceFrac F 2 9 k₀ hk₀) :
    (sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ↔ sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  constructor
  · intro h2
    exact le_trans hPT h2
  · intro hb
    exact le_trans (sprTraceFrac_le_sprPGLFixedField F 2 k₀ hk₀) hb

#print axioms beta2_iff_b_of_P_le_T

/-- ★★★★★★ **`(P ≤ T) ⟹ ((β1) ∧ (β2) ⟺ (a) ∧ (b))`**（合取版）：
`T = P` 时，`(β)`-分解与 `(a)/(b)`-分解是**同一对义务**。 -/
theorem beta_iff_a_and_b_of_P_le_T (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hPT : sprPGLFixedField F 2 k₀ hk₀ ≤ sprTraceFrac F 2 9 k₀ hk₀) :
    ((sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
        ∧ sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ↔ ((sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀)
        ∧ sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨pglFixed_imp_of_traceFrac F 2 k₀ hk₀ h1, le_trans hPT h2⟩
  · rintro ⟨ha, hb⟩
    exact ⟨le_trans ha hPT,
      le_trans (sprTraceFrac_le_sprPGLFixedField F 2 k₀ hk₀) hb⟩

#print axioms beta_iff_a_and_b_of_P_le_T

end SprWallMapIff

/-! ## §187 ★★★★★★★ **`T` 的第一个显式成员**：迹域含「对角迹」——`(β2)` 的可检验推论

第 662 轮。侦察结论（见 `wiki/proj-abgv52-frontier-R661.md`）：`prop:14.19` 的三条文献引理
`lem:14.23／14.24／14.25` **均已机检**，剩余目标收窄为 `(β1)` `N ≤ T` 与 `(β2)` `T ≤ C`。

本节给 `(β2)` 的**第一个可检验推论**：迹域 `T = sprTraceFrac`（`K' ∩ Frac(traceAlg)`）
的第一个**显式、非平凡**成员

```
trDiag(k) := Σ_i y_{iik}   （k ≠ k₀；即 ymat k 的迹，k = 0 时是 diag 部分的迹）
```

**它为何确实在 `T` 里**（源文 `:283` `prop:14.14` 之前的那套记号的直接对位）：
`sprToSField (trDiag k) = Σ_i x_{k,i,i} = tr(genMatKF k)`，而后者是
`traceMonoSet` 关于单字 `w = [k]` 的元素（`traceMonoSet_def`），
故落在 `traceAlg ⊆ Frac(traceAlg)` 里（`IntermediateField.subset_adjoin`）。

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprTrDiag_mem_sprTraceFrac` | **`trDiag k ∈ T`**（`T = sprTraceFrac`） |
| ★★★★★★ `sprTrDiag_mem_sprNFixedField` | `trDiag k ∈ K'^N`（经 `T ≤ N`） |
| ★★★★★★ `sprTrDiag_mem_sprPGLFixedField` | `trDiag k ∈ K' ∩ K^{PGL}`（经 `T ≤ P`） |
| ★★★★★★★ `sprTrDiag_mem_sprCenterImageField_of_beta2` | **`(β2) ⟹ trDiag k ∈ C`** |
| ★★★★★★★ `sprTrDiag_mem_sprCenterImageField_of_zHalf` | **`hZ ⟹ trDiag k ∈ C`** |

**为何有用（这是本节唯一的新数学内容）**：`(β2)` 与 `hZ` 都**蕴含**同一条**具体**的成员断言
`trDiag k ∈ C`。按教训 88／90 的口径，这给了一个**具体的**可证伪点：下一轮攻 `(β2)` 时，
**首个候选反例**应当是「`trDiag k ∉ C`」（若成立，则 `(β2)` 与 `hZ` **同时为假**）。
本战役已有先例（`C ≤ P` 由 `∏_i x_{0,i,i}` 杀死，§185）；本条把同类检验**前移**到 `T` 的成员层。

**诚实边界（勿夸大）**：`trDiag k ∉ C` **未被证**，亦**未**被证伪；
`(β1)`／`(β2)`／`hZ` 均未证；`hZ` **未证**；**H2 见文件头「当前状态」。**本节**不含**任何新证明技术，
只是把已机检的 `T ≤ N`／`T ≤ P` 与 `traceAlg` 的生成元**落到一个具体元素**上。 -/

section SprTraceFracMembers

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★ **`trDiag k ∈ T`**（`T = sprTraceFrac = K' ∩ Frac(traceAlg)`）。

**证明**：`mem_sprTraceFrac_iff` 把目标化为「`sprToSField` 的像落在 `Frac(traceAlg)`」；
`sprToSField_algebraMap` 把它化为 `sprToS` 在 `S` 上的值；
`sprToS` 在 `X (Sum.inr (i,i,k))` 上给 `X (k,i,i)`，其和为 `(genMatKF k).trace`；
`traceMonoSet_def` 取 `w = [k]` 给该迹在 `traceMonoSet` 里，`traceMonoSet_subset_traceAlg`
与 `IntermediateField.subset_adjoin` 收口。 -/
theorem sprTrDiag_mem_sprTraceFrac (F : Type) [Field F] (r n : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (k : {k : Fin r // k.val ≠ 0}) :
    algebraMap (Spr F r n) (SprField F r n)
      (∑ i : Fin n, MvPolynomial.X (Sum.inr (i, i, k))) ∈ sprTraceFrac F r n k₀ hk₀ := by
  rw [mem_sprTraceFrac_iff, sprToSField_algebraMap]
  have hspr : (sprToS F k₀) (∑ i : Fin n, MvPolynomial.X (Sum.inr (i, i, k)))
      = ∑ i : Fin n, MvPolynomial.X ((k : Fin r), i, i) := by
    simp [sprToS]
  rw [hspr]
  refine IntermediateField.subset_adjoin F (traceAlg F r n : Set (SField F r n)) ?_
  have h : (List.map (genMatKF F r n) [(k : Fin r)]).prod.trace ∈ traceAlg F r n :=
    traceMonoSet_subset_traceAlg F r n (traceMonoSet_def F r n [(k : Fin r)])
  simpa [genMatKF, Matrix.trace, Matrix.map_apply, genericMatrix, genericEntry, map_sum]
    using h

#print axioms sprTrDiag_mem_sprTraceFrac

/-- ★★★★★★ **`trDiag k ∈ K'^N`**（经已机检的 `T ≤ N`，`sprTraceFrac_le_sprNFixedField`）。

该排序件本身按 `n = 9` 陈述（`sprTraceFrac F r 9 k₀ hk₀ ≤ sprNFixedField F r 9`），故本条同。 -/
theorem sprTrDiag_mem_sprNFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (k : {k : Fin r // k.val ≠ 0}) :
    algebraMap (Spr F r 9) (SprField F r 9)
      (∑ i : Fin 9, MvPolynomial.X (Sum.inr (i, i, k))) ∈ sprNFixedField F r 9 :=
  sprTraceFrac_le_sprNFixedField F r k₀ hk₀
    (sprTrDiag_mem_sprTraceFrac F r 9 k₀ hk₀ k)

#print axioms sprTrDiag_mem_sprNFixedField

/-- ★★★★★★ **`trDiag k ∈ K' ∩ K^{PGL}`**（经已机检的 `T ≤ P`，`sprTraceFrac_le_sprPGLFixedField`）。

该排序件同样按 `n = 9` 陈述，故本条同。 -/
theorem sprTrDiag_mem_sprPGLFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (k : {k : Fin r // k.val ≠ 0}) :
    algebraMap (Spr F r 9) (SprField F r 9)
      (∑ i : Fin 9, MvPolynomial.X (Sum.inr (i, i, k)))
        ∈ sprPGLFixedField F r k₀ hk₀ :=
  sprTraceFrac_le_sprPGLFixedField F r k₀ hk₀
    (sprTrDiag_mem_sprTraceFrac F r 9 k₀ hk₀ k)

#print axioms sprTrDiag_mem_sprPGLFixedField

/-- ★★★★★★★ **`(β2) ⟹ trDiag k ∈ C`** —— `(β2)` 的**具体**推论（可证伪点）。 -/
theorem sprTrDiag_mem_sprCenterImageField_of_beta2 (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (k : {k : Fin 2 // k.val ≠ 0})
    (h2 : sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    algebraMap (Spr F 2 9) (SprField F 2 9)
      (∑ i : Fin 9, MvPolynomial.X (Sum.inr (i, i, k))) ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  h2 (sprTrDiag_mem_sprTraceFrac F 2 9 k₀ hk₀ k)

#print axioms sprTrDiag_mem_sprCenterImageField_of_beta2

/-- ★★★★★★★ **`hZ ⟹ trDiag k ∈ C`**（经 `T ≤ N ≤ C`）。与 `(β2)` 给出**同一条**具体结论
——故它是 `(β2)` 与 `hZ` **共同的必要条件**（下一轮的可证伪点）。 -/
theorem sprTrDiag_mem_sprCenterImageField_of_zHalf (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (k : {k : Fin 2 // k.val ≠ 0})
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    algebraMap (Spr F 2 9) (SprField F 2 9)
      (∑ i : Fin 9, MvPolynomial.X (Sum.inr (i, i, k))) ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  hZ (sprTrDiag_mem_sprNFixedField F 2 k₀ hk₀ k)

#print axioms sprTrDiag_mem_sprCenterImageField_of_zHalf

end SprTraceFracMembers

/-! ## §188 ★★★★★★ **`T` 的成员（次数 2）**：两字迹 `tr(ymat k · ymat l)` 落在迹域里

第 663 轮。§187 给了 `T` 的**次数 1** 成员 `trDiag k`。本节把同一机制推到**乘积**层：

```
yTrace2(k, l) := tr(ymat k · ymat l)      （k, l ≠ k₀）
```

`sprToSField (yTrace2 k l) = tr(genericMatrix k · genericMatrix l)`，后者是
`traceMonoSet` 关于**两字** `w = [k, l]` 的元素 ⟹ 落在 `traceAlg ⊆ Frac(traceAlg)`。

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprYTrace2_mem_sprTraceFrac` | **`yTrace2 k l ∈ T`** |
| ★★★★★★ `sprYTrace2_mem_sprNFixedField` | `yTrace2 k l ∈ K'^N` |
| ★★★★★★★ `sprYTrace2_mem_sprCenterImageField_of_beta2` | **`(β2) ⟹ yTrace2 k l ∈ C`** |
| ★★★★★★★ `sprYTrace2_mem_sprCenterImageField_of_zHalf` | **`hZ ⟹ yTrace2 k l ∈ C`** |

**⟹ `T` 与 `hZ` 的可证伪点从 1 条扩成 2 条**（`trDiag k`、`yTrace2 k l`），
且第二条**带乘积结构**：`C` 若被证伪，`yTrace2` 比 `trDiag` 更可能先命中
（`trDiag` 是**次数 1**，而 `C(R)` 的中心元最低次数 `> 1`；见本节末的**次数审计**）。

**次数审计（R662 遗留的 hazard，本轮**关闭**）**：曾设想「`C(R)` 的中心元次数均 ≥ 2 ⟹
`Frac` 的像里无次数 1 元 ⟹ `trDiag k ∉ C` ⟹ `hZ` 假」。
**该推理不成立**：源文 `thm:14.16`（`raw/Saltman1999ch14.tex:317`，逐字）
「`K^{\PGL_n(F)} = Z(F,n,r)`」＋ `K^{\PGL} ∋ tr(X_1)`（次数 **1**，`traceAlg_le_pglFixedField` 已机检）
⟹ `Frac(C(R)) = Z ∋ tr(X_1)` ⟹ 中心元的次数集合的**整数span含 1**。
故**次数检验不能证伪** `trDiag k ∈ C`；两条成员断言只能由**更多结构**（而非次数）裁决。

**诚实边界（勿夸大）**：`trDiag k ∉ C`／`yTrace2 k l ∉ C` **均未证亦未证伪**；
`(β1)`／`(β2)`／`hZ` **均未证**；**H2 见文件头「当前状态」。**本节**不含新证明技术**，
只是同一机制的第二个实例（次数 2）。 -/

section SprTraceFracMembersTwo

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★ **`yTrace2 k l ∈ T`**：`sprToSField` 的像是两字迹 `tr(genMatKF k · genMatKF l)`，
故是 `traceMonoSet` 关于 `w = [k, l]` 的元素。 -/
theorem sprYTrace2_mem_sprTraceFrac (F : Type) [Field F] (r n : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (k l : {k : Fin r // k.val ≠ 0}) :
    algebraMap (Spr F r n) (SprField F r n)
      ((ymat F r n k * ymat F r n l).trace) ∈ sprTraceFrac F r n k₀ hk₀ := by
  rw [mem_sprTraceFrac_iff, sprToSField_algebraMap]
  have hspr : (sprToS F (r := r) (n := n) k₀)
      ((ymat F r n k * ymat F r n l).trace)
      = ((genericMatrix F r n (k : Fin r) * genericMatrix F r n (l : Fin r))).trace := by
    simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul, ymat, genericMatrix,
      genericEntry, sprToS]
  rw [hspr]
  refine IntermediateField.subset_adjoin F (traceAlg F r n : Set (SField F r n)) ?_
  have h := traceMonoSet_subset_traceAlg F r n
    (traceMonoSet_def F r n [(k : Fin r), (l : Fin r)])
  have h2 : (List.map (genMatKF F r n) [(k : Fin r), (l : Fin r)]).prod.trace
      = (genMatKF F r n (k : Fin r) * genMatKF F r n (l : Fin r)).trace := by
    simp [List.prod]
  have h3 : (genMatKF F r n (k : Fin r) * genMatKF F r n (l : Fin r)).trace
      = algebraMap (S F r n) (SField F r n)
          ((genericMatrix F r n (k : Fin r) * genericMatrix F r n (l : Fin r))).trace := by
    simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul, genMatKF, genericMatrix,
      genericEntry]
  rw [h2, h3] at h
  exact h

#print axioms sprYTrace2_mem_sprTraceFrac

/-- ★★★★★★ **`yTrace2 k l ∈ K'^N`**（经已机检的 `T ≤ N`）。 -/
theorem sprYTrace2_mem_sprNFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (k l : {k : Fin r // k.val ≠ 0}) :
    algebraMap (Spr F r 9) (SprField F r 9)
      ((ymat F r 9 k * ymat F r 9 l).trace) ∈ sprNFixedField F r 9 :=
  sprTraceFrac_le_sprNFixedField F r k₀ hk₀
    (sprYTrace2_mem_sprTraceFrac F r 9 k₀ hk₀ k l)

#print axioms sprYTrace2_mem_sprNFixedField

/-- ★★★★★★★ **`(β2) ⟹ yTrace2 k l ∈ C`** —— `(β2)` 的第二个具体推论。 -/
theorem sprYTrace2_mem_sprCenterImageField_of_beta2 (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (k l : {k : Fin 2 // k.val ≠ 0})
    (h2 : sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    algebraMap (Spr F 2 9) (SprField F 2 9)
      ((ymat F 2 9 k * ymat F 2 9 l).trace) ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  h2 (sprYTrace2_mem_sprTraceFrac F 2 9 k₀ hk₀ k l)

#print axioms sprYTrace2_mem_sprCenterImageField_of_beta2

/-- ★★★★★★★ **`hZ ⟹ yTrace2 k l ∈ C`**（经 `T ≤ N ≤ C`）。 -/
theorem sprYTrace2_mem_sprCenterImageField_of_zHalf (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (k l : {k : Fin 2 // k.val ≠ 0})
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    algebraMap (Spr F 2 9) (SprField F 2 9)
      ((ymat F 2 9 k * ymat F 2 9 l).trace) ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  hZ (sprYTrace2_mem_sprNFixedField F 2 k₀ hk₀ k l)

#print axioms sprYTrace2_mem_sprCenterImageField_of_zHalf

end SprTraceFracMembersTwo

/-! ## §189 ★★★★★★★★★★ **`(β2)` 归约为两个具名条件**（第 664 轮）

**本轮的核心结论**：`(β2)` `T ≤ C` 不再是一个"未知难度"的命题，而是**两条具名条件**的推论：

```
(β2)  ⟸  K^{PGL} ⊆ Frac(中心标量代数)   ＋   evSpr 在中心标量代数上单射
```

**证明的骨架（逐步对位源文 `prop:14.19` 末段）**：
1. `x ∈ T` ⟹ `z := sprToSField x ∈ Frac(traceAlg) ≤ K^{PGL}`（`traceField_le_pglFixedField`，已机检）；
2. `K^{PGL} ⊆ Frac(中心标量代数)`（**条件 ①**）⟹ `z = p/q`，`p, q` 在 `sprCenterPolyK` 生成的代数里；
3. 把 `x` 写成 `Spr` 的分式 `x = a/b`（`IsFractionRing.div_surjective`），升到 `S`：
   `q · sprToS a = p · sprToS b`（用 `S → SField` 单射**清分母**）；
4. **核心一步** `evSpr_sprToS_cancel`：对第 3 步的等式作用 `evSpr`，用 `evSpr ∘ sprToS = id`
   得 `evSpr q · a = evSpr p · b`；
5. `evSpr q, evSpr p` 在 `sprCenterK` 生成的代数里（`sprCenterAlg_map_eq`），故其 `algebraMap`-像在 `C` 里
   （`sprCenterAlg_le_sprCenterImageField`）；
6. `q ≠ 0` ＋ **条件 ②** `evSpr` 单射 ⟹ `evSpr q ≠ 0` ⟹ `x = evSpr p / evSpr q ∈ C`。

**两条条件的性质（勿夸大）**：
* **条件 ①** `KPGLIntoCenterFrac` 是 `KPFixedLeZ`（`GenericInv` §61 的缺口 ⑤，源文 `thm:14.16` 第二陈述）
  的**解包形态**：把 `ZCanon = adjoin(centK)` 显式写成"两中心多项式之商"。它是**已发表命题**（T3），
  本工作区**未证**。
* **条件 ②** `EvSprInjOnCenter` 是**新的**、本工作区首次具名的条件：`evSpr`（把 `x_{k₀,ij}`（`i ≠ j`）杀成 0
  的特殊化）在中心标量代数上不杀非零元。**未证亦未证伪**。
  注意：它**不能**由 `CenterPolyDiagHyp` 得到（后者已被 `det(X_1)` 证伪，§184）；恰恰因为 `s_c` 一般
  **含**非对角项，条件 ② 才是一个实质条件。

**⟹ 由 §182 的 `zHalf_of_beta`，`hZ` 现在归约为三条**：`(β1)` ＋ 条件 ① ＋ 条件 ②。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `KPGLIntoCenterFrac` | **条件 ①**（`K^{PGL} ⊆ Frac(中心标量代数)`，解包形态） |
| ★★★★★★★★ `EvSprInjOnCenter` | **条件 ②**（`evSpr` 在中心标量代数上单射） |
| ★★★★★★ `sprCenterAlg_map_eq` | `C` 的生成元 ＝ `evSpr` 在中心标量代数上的像 |
| ★★★★★★ `sprCenterAlg_le_sprCenterImageField` | 该像的 `algebraMap` 落进 `C` |
| ★★★★★★★★ `evSpr_sprToS_cancel` | **核心**：`evSpr ∘ sprToS = id` ⟹ 清分母后仍成立 |
| ★★★★★★★★★★ `sprTraceFrac_le_sprCenterImageField_of_centerFrac` | **`(β2)` ⟸ ① ＋ ②** |
| ★★★★★★★★★★ `zHalf_of_centerFrac_and_beta1` | **`hZ` ⟸ `(β1)` ＋ ① ＋ ②** |

**诚实边界（勿夸大）**：条件 ①／② **均未证**；`(β1)` **未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprBetaTwoRoute

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★ **条件 ①**：`K^{PGL} ⊆ Frac(中心标量代数)` 的**解包形态**。

即：`K` 中被整个 `PGL_9(F)` 固定的元素都可写成两个中心标量多项式之商（分母非零）。
这是源文 `thm:14.16` 第二陈述（`K^{PGL} = Z(F,n,r)`，`raw/Saltman1999ch14.tex:317`）
在 `ZCanon = adjoin(centK)` 口径下的**显式**形态。**本工作区未证**（T3，PI 理论层）。 -/
def KPGLIntoCenterFrac (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) : Prop :=
  ∀ x : SField F 2 9,
    (∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ, phiKAlgEquiv F 2 9 A x = x) →
    ∃ p q : S F 2 9, q ≠ 0 ∧
      q ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
            sprCenterPolyK F 2 9 D c)) ∧
      p ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
            sprCenterPolyK F 2 9 D c)) ∧
      algebraMap (S F 2 9) (SField F 2 9) q * x
        = algebraMap (S F 2 9) (SField F 2 9) p

#print axioms KPGLIntoCenterFrac

/-- ★★★★★★★★ **条件 ②**：`evSpr` 在**中心标量代数**上单射。

`evSpr` 把非对角 `x_{k₀,ij}`（`i ≠ j`）杀成 0，故它整体**不**单射；本条要求它在
`sprCenterPolyK` 生成的子代数上不杀非零元。**未证亦未证伪**。
**注意**：它**不能**由 `CenterPolyDiagHyp` 推出（后者已被 `det(X_1)` 证伪，§184）。 -/
def EvSprInjOnCenter (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ q ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
        sprCenterPolyK F 2 9 D c)),
    evSpr F 2 9 k₀ hk₀ q = 0 → q = 0

#print axioms EvSprInjOnCenter

/-- ★★★★★★ **`C` 的生成元 ＝ `evSpr` 在中心标量代数上的像**（`sprCenterK = evSpr ∘ sprCenterPolyK`）。 -/
theorem sprCenterAlg_map_eq (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c)))
      = Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterK F 2 9 k₀ hk₀ D c)) := by
  rw [AlgHom.map_adjoin]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by simp [sprCenterK, sprCenterPolyAlgHom]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨sprCenterPolyK F 2 9 D c, ⟨c, rfl⟩, by simp [sprCenterK, sprCenterPolyAlgHom]⟩

#print axioms sprCenterAlg_map_eq

/-- ★★★★★★ **中心标量代数的 `algebraMap`-像落在 `C` 里**。 -/
theorem sprCenterAlg_le_sprCenterImageField (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    ∀ y ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
        sprCenterK F 2 9 k₀ hk₀ D c)),
      algebraMap (Spr F 2 9) (SprField F 2 9) y
        ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
  intro y hy
  revert hy
  refine Algebra.adjoin_induction
    (p := fun y _ => algebraMap (Spr F 2 9) (SprField F 2 9) y
      ∈ sprCenterImageField F 2 9 D k₀ hk₀) ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨c, rfl⟩ := hy
    exact IntermediateField.subset_adjoin F _ (Set.mem_range_self c)
  · intro c
    exact IntermediateField.algebraMap_mem (sprCenterImageField F 2 9 D k₀ hk₀) c
  · intro x y hx hy ihx ihy
    simpa [map_add] using IntermediateField.add_mem (sprCenterImageField F 2 9 D k₀ hk₀) ihx ihy
  · intro x y hx hy ihx ihy
    simpa [map_mul] using IntermediateField.mul_mem (sprCenterImageField F 2 9 D k₀ hk₀) ihx ihy

#print axioms sprCenterAlg_le_sprCenterImageField

/-- ★★★★★★★★ **核心一步（清分母）**：`evSpr ∘ sprToS = id` ⟹
`S` 中的清分母等式经 `evSpr` 直接落到 `Spr` 上。 -/
theorem evSpr_sprToS_cancel (F : Type) [Field F] (r n : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) (p q : S F r n) (a b : Spr F r n)
    (h : q * sprToS F k₀ a = p * sprToS F k₀ b) :
    evSpr F r n k₀ hk₀ q * a = evSpr F r n k₀ hk₀ p * b := by
  have hid : (evSpr F r n k₀ hk₀).comp (sprToS F (r := r) (n := n) k₀)
      = AlgHom.id F (Spr F r n) := evSpr_comp_sprToS (F := F) (r := r) (n := n) k₀ hk₀
  have h1 : (evSpr F r n k₀ hk₀) ((sprToS F k₀) a) = a := by
    have := congrArg (fun (f : Spr F r n →ₐ[F] Spr F r n) => f a) hid
    simpa [AlgHom.comp_apply] using this
  have h2 : (evSpr F r n k₀ hk₀) ((sprToS F k₀) b) = b := by
    have := congrArg (fun (f : Spr F r n →ₐ[F] Spr F r n) => f b) hid
    simpa [AlgHom.comp_apply] using this
  have h' := congrArg (evSpr F r n k₀ hk₀) h
  simp only [map_mul, h1, h2] at h'
  exact h'

#print axioms evSpr_sprToS_cancel

/-- ★★★★★★★★★★ **`(β2)` ⟸ 条件 ① ＋ 条件 ②**（`T = sprTraceFrac ≤ C = sprCenterImageField`）。 -/
theorem sprTraceFrac_le_sprCenterImageField_of_centerFrac (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hKPZ : KPGLIntoCenterFrac F D) (hInj : EvSprInjOnCenter F D k₀ hk₀) :
    sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  classical
  intro x hx
  have hz : sprToSField F 2 9 k₀ hk₀ x
      ∈ IntermediateField.adjoin F (traceAlg F 2 9 : Set (SField F 2 9)) :=
    (mem_sprTraceFrac_iff F 2 9 hk₀).mp hx
  have hPGL : ∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ,
      phiKAlgEquiv F 2 9 A (sprToSField F 2 9 k₀ hk₀ x) = sprToSField F 2 9 k₀ hk₀ x :=
    fun A => traceField_le_pglFixedField F 2 hz A
  obtain ⟨p, q, hq0, hqA, hpA, hpq⟩ := hKPZ _ hPGL
  obtain ⟨a, b, hb, hbdiv⟩ := IsFractionRing.div_surjective (Spr F 2 9) x
  have hbmap : algebraMap (Spr F 2 9) (SprField F 2 9) b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hb
      ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxb : x * algebraMap (Spr F 2 9) (SprField F 2 9) b
      = algebraMap (Spr F 2 9) (SprField F 2 9) a := by
    rw [← hbdiv, div_mul_cancel₀ _ hbmap]
  have hxbS : sprToSField F 2 9 k₀ hk₀ x
        * algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ b)
      = algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ a) := by
    have h := congrArg (sprToSField F 2 9 k₀ hk₀) hxb
    simpa [map_mul, sprToSField_algebraMap] using h
  have hclear : q * sprToS F (r := 2) (n := 9) k₀ a
      = p * sprToS F (r := 2) (n := 9) k₀ b := by
    refine IsFractionRing.injective (S F 2 9) (SField F 2 9) ?_
    have hm := congrArg (fun t => t * algebraMap (S F 2 9) (SField F 2 9)
      (sprToS F (r := 2) (n := 9) k₀ b)) hpq
    rw [mul_assoc, hxbS] at hm
    simpa [map_mul] using hm
  have hcan : evSpr F 2 9 k₀ hk₀ q * a = evSpr F 2 9 k₀ hk₀ p * b :=
    evSpr_sprToS_cancel F 2 9 k₀ hk₀ p q a b hclear
  have hqne : evSpr F 2 9 k₀ hk₀ q ≠ 0 := fun h0 => hq0 (hInj q hqA h0)
  have hxq : x * algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q)
      = algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p) := by
    have hb' : x = algebraMap (Spr F 2 9) (SprField F 2 9) a
        / algebraMap (Spr F 2 9) (SprField F 2 9) b := hbdiv.symm
    rw [hb']
    field_simp
    rw [← map_mul, ← map_mul]
    rw [mul_comm a (evSpr F 2 9 k₀ hk₀ q), mul_comm b (evSpr F 2 9 k₀ hk₀ p), hcan]
  have hmemQ : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    have hmem : evSpr F 2 9 k₀ hk₀ q ∈ Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c))) :=
      Subalgebra.mem_map.mpr ⟨q, hqA, rfl⟩
    rwa [sprCenterAlg_map_eq F D k₀ hk₀] at hmem
  have hmemP : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    have hmem : evSpr F 2 9 k₀ hk₀ p ∈ Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c))) :=
      Subalgebra.mem_map.mpr ⟨p, hpA, rfl⟩
    rwa [sprCenterAlg_map_eq F D k₀ hk₀] at hmem
  have hqne' : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q) ≠ 0 := by
    intro h0
    exact hqne ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxfin : x = algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p)
      / algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q) := by
    rw [eq_div_iff (by exact hqne')]
    exact hxq
  rw [hxfin]
  exact div_mem hmemP hmemQ

#print axioms sprTraceFrac_le_sprCenterImageField_of_centerFrac

/-- ★★★★★★★★★★ **`hZ` ⟸ `(β1)` ＋ 条件 ① ＋ 条件 ②**（配 §182 的 `zHalf_of_beta`）。

⟹ **本战役的剩余目标从"一条未知命题"变成"三条具名条件"**：
`(β1)`（`N ≤ T`，纯迹域陈述）／条件 ①（T3 已发表 `thm:14.16` 第二陈述的解包形态）／
条件 ②（`evSpr` 在中心标量代数上单射，新具名）。 -/
theorem zHalf_of_centerFrac_and_beta1 (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (hKPZ : KPGLIntoCenterFrac F D) (hInj : EvSprInjOnCenter F D k₀ hk₀) :
    sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  le_trans h1 (sprTraceFrac_le_sprCenterImageField_of_centerFrac F D k₀ hk₀ hKPZ hInj)

#print axioms zHalf_of_centerFrac_and_beta1

end SprBetaTwoRoute

/-! ## §190 ★★★★★★★★★ **`(β2)` 的条件 ① 可弱化到 `T` 上**（第 665 轮）

R664 的 `(β2)` 归约用的条件 ① 是关于**整个** `K^{PGL}` 的：

```
①  K^{PGL} ⊆ Frac(中心标量代数)
```

但那一步实际只用了 `z = sprToSField x`（`x ∈ T`）落在 `Frac(traceAlg) ≤ K^{PGL}` 里。
**故 ① 可以弱化成只在 `Frac(traceAlg)` 上成立**：

```
①'  Frac(traceAlg) ⊆ Frac(中心标量代数)
```

`①` ⟹ `①'` 是 `traceField_le_pglFixedField`（已机检）的直接推论。**`①'` 严格弱于 `①`**
（`Frac(traceAlg) = Z` 与 `K^{PGL} = Z` 是同一边界，但 `①'` 不预设 `Z = K^{PGL}`）。

**⟹ `(β2)` 的两段分解现在是**（**两段都不提 `K^{PGL}`**）：

```
(β2)  ⟺  ①' T ⊆ Frac(中心标量代数)   ＋   ② evSpr 在中心标量代数上单射
```

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `TraceFracIntoCenterFrac` | **条件 ①'**（`T` 的每个元都是两中心标量之商） |
| ★★★★★★★★ `traceFracIntoCenterFrac_of_kpgl` | **`① ⟹ ①'`**（§189 未失效） |
| ★★★★★★★★★★ `sprTraceFrac_le_sprCenterImageField_of_traceFrac` | **`(β2)` ⟸ ①' ＋ ②** |
| ★★★★★★★★★★ `zHalf_of_traceFrac_and_beta1` | **`hZ` ⟸ `(β1)` ＋ ①' ＋ ②** |

**诚实边界（勿夸大）**：①'／②／`(β1)` **均未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprBetaTwoRouteWeak

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★ **条件 ①'（弱化版）**：`Frac(traceAlg)` 的每个元都是两个中心标量多项式之商。

比 §189 的 `KPGLIntoCenterFrac` 弱：只要求对迹域成立，不要求对整个 `K^{PGL}` 成立。 -/
def TraceFracIntoCenterFrac (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) : Prop :=
  ∀ x : SField F 2 9,
    x ∈ IntermediateField.adjoin F (traceAlg F 2 9 : Set (SField F 2 9)) →
    ∃ p q : S F 2 9, q ≠ 0 ∧
      q ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
            sprCenterPolyK F 2 9 D c)) ∧
      p ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
            sprCenterPolyK F 2 9 D c)) ∧
      algebraMap (S F 2 9) (SField F 2 9) q * x
        = algebraMap (S F 2 9) (SField F 2 9) p

#print axioms TraceFracIntoCenterFrac

/-- ★★★★★★★★ **`① ⟹ ①'`**：`K^{PGL} ⊆ Frac(A)` ⟹ `Frac(traceAlg) ⊆ Frac(A)`
（只须 `Frac(traceAlg) ≤ K^{PGL}`，R655 已机检）。 -/
theorem traceFracIntoCenterFrac_of_kpgl (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (hKPZ : KPGLIntoCenterFrac F D) :
    TraceFracIntoCenterFrac F D :=
  fun x hx => hKPZ x (fun A => traceField_le_pglFixedField F 2 hx A)

#print axioms traceFracIntoCenterFrac_of_kpgl

/-- ★★★★★★★★★★ **`(β2)` ⟸ ①' ＋ ②**（条件 ① 弱化到迹域上）。 -/
theorem sprTraceFrac_le_sprCenterImageField_of_traceFrac (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hTF : TraceFracIntoCenterFrac F D) (hInj : EvSprInjOnCenter F D k₀ hk₀) :
    sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  classical
  intro x hx
  have hz : sprToSField F 2 9 k₀ hk₀ x
      ∈ IntermediateField.adjoin F (traceAlg F 2 9 : Set (SField F 2 9)) :=
    (mem_sprTraceFrac_iff F 2 9 hk₀).mp hx
  obtain ⟨p, q, hq0, hqA, hpA, hpq⟩ := hTF _ hz
  obtain ⟨a, b, hb, hbdiv⟩ := IsFractionRing.div_surjective (Spr F 2 9) x
  have hbmap : algebraMap (Spr F 2 9) (SprField F 2 9) b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hb
      ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxb : x * algebraMap (Spr F 2 9) (SprField F 2 9) b
      = algebraMap (Spr F 2 9) (SprField F 2 9) a := by
    rw [← hbdiv, div_mul_cancel₀ _ hbmap]
  have hxbS : sprToSField F 2 9 k₀ hk₀ x
        * algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ b)
      = algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ a) := by
    have h := congrArg (sprToSField F 2 9 k₀ hk₀) hxb
    simpa [map_mul, sprToSField_algebraMap] using h
  have hclear : q * sprToS F (r := 2) (n := 9) k₀ a
      = p * sprToS F (r := 2) (n := 9) k₀ b := by
    refine IsFractionRing.injective (S F 2 9) (SField F 2 9) ?_
    have hm := congrArg (fun t => t * algebraMap (S F 2 9) (SField F 2 9)
      (sprToS F (r := 2) (n := 9) k₀ b)) hpq
    rw [mul_assoc, hxbS] at hm
    simpa [map_mul] using hm
  have hcan : evSpr F 2 9 k₀ hk₀ q * a = evSpr F 2 9 k₀ hk₀ p * b :=
    evSpr_sprToS_cancel F 2 9 k₀ hk₀ p q a b hclear
  have hqne : evSpr F 2 9 k₀ hk₀ q ≠ 0 := fun h0 => hq0 (hInj q hqA h0)
  have hxq : x * algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q)
      = algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p) := by
    have hb' : x = algebraMap (Spr F 2 9) (SprField F 2 9) a
        / algebraMap (Spr F 2 9) (SprField F 2 9) b := hbdiv.symm
    rw [hb']
    field_simp
    rw [← map_mul, ← map_mul]
    rw [mul_comm a (evSpr F 2 9 k₀ hk₀ q), mul_comm b (evSpr F 2 9 k₀ hk₀ p), hcan]
  have hmemQ : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    have hmem : evSpr F 2 9 k₀ hk₀ q ∈ Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c))) :=
      Subalgebra.mem_map.mpr ⟨q, hqA, rfl⟩
    rwa [sprCenterAlg_map_eq F D k₀ hk₀] at hmem
  have hmemP : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    have hmem : evSpr F 2 9 k₀ hk₀ p ∈ Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c))) :=
      Subalgebra.mem_map.mpr ⟨p, hpA, rfl⟩
    rwa [sprCenterAlg_map_eq F D k₀ hk₀] at hmem
  have hqne' : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q) ≠ 0 := by
    intro h0
    exact hqne ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxfin : x = algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p)
      / algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q) := by
    rw [eq_div_iff (by exact hqne')]
    exact hxq
  rw [hxfin]
  exact div_mem hmemP hmemQ

#print axioms sprTraceFrac_le_sprCenterImageField_of_traceFrac

/-- ★★★★★★★★★★ **`hZ` ⟸ `(β1)` ＋ ①' ＋ ②**。 -/
theorem zHalf_of_traceFrac_and_beta1 (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (hTF : TraceFracIntoCenterFrac F D) (hInj : EvSprInjOnCenter F D k₀ hk₀) :
    sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  le_trans h1 (sprTraceFrac_le_sprCenterImageField_of_traceFrac F D k₀ hk₀ hTF hInj)

#print axioms zHalf_of_traceFrac_and_beta1

end SprBetaTwoRouteWeak

/-! ## §191 ★★★★★★★★★ **条件 ② 可弱化成「非零元的某个倍数不被杀」**（第 666 轮）

R664／R665 的条件 ② 是 `evSpr` 在中心标量代数 `A` 上**单射**（等价：`A ∩ ker(evSpr) = 0`）。
本轮把它弱化成：

```
②w    ∀ q ∈ A, q ≠ 0 → ∃ r ∈ A, evSpr (q · r) ≠ 0
```

**为何 ②w 够用**（这是本节的数学内容）：`(β2)` 的证明只需要「把 `z` 写成 `p/q` 时能找到
**某个**分母不被杀」。若 `evSpr q = 0`，但存在 `r` 使 `evSpr (q r) ≠ 0`，
则 `z = p/q = (p r)/(q r)` 是**同一个 `z` 的另一个表示**，而它的分母不被杀 ⟹ 结论照旧成立。

**⚠ 勘误（第 667 轮机检，见 §192）**：R666 曾声称 ②w **严格弱于** ②。**该声称是错的。**
`evSpr` 是环同态且 `Spr = MvMatPolynomial` 是**整环**，故
`evSpr (q · r) = evSpr q · evSpr r`；于是 `evSpr q = 0 ⟹ ∀ r, evSpr (q r) = 0`。
又因 `1 ∈ A`，`q ∈ A ∩ ker ⟹ q·A ⊆ ker`。**⟹ ②w ⟺ ②**（`evSprInjOnCenter_iff_nonZeroMultiple`，§192）。
本节的**价值仅在于把 ② 的"倍数形态"机检下来**（该形态在 §192 里被用来**反向**推出 ② 的等价性），
**不构成弱化**。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `EvSprNonZeroMultiple` | **条件 ②w** |
| ★★★★★★★★ `evSprNonZeroMultiple_of_inj` | **`② ⟹ ②w`** |
| ★★★★★★★★★★ `sprTraceFrac_le_sprCenterImageField_of_traceFracMul` | **`(β2)` ⟸ ①' ＋ ②w** |
| ★★★★★★★★★★ `zHalf_of_traceFrac_and_beta1Mul` | **`hZ` ⟸ `(β1)` ＋ ①' ＋ ②w** |

**诚实边界（勿夸大）**：①'／②w／`(β1)` **均未证**（②w 只是**更弱**，未证）；
`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprBetaTwoRouteWeakMul

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Matrix
open ABGV52

/-- ★★★★★★★★ **条件 ②w（② 的严格弱化）**：中心标量代数里每个非零元都有**某个倍数**不被
`evSpr` 杀死。 -/
def EvSprNonZeroMultiple (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) : Prop :=
  ∀ q ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
        sprCenterPolyK F 2 9 D c)),
    q ≠ 0 → ∃ r ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
        sprCenterPolyK F 2 9 D c)), evSpr F 2 9 k₀ hk₀ (q * r) ≠ 0

#print axioms EvSprNonZeroMultiple

/-- ★★★★★★★★ **`② ⟹ ②w`**（取 `r = 1`）。 -/
theorem evSprNonZeroMultiple_of_inj (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hInj : EvSprInjOnCenter F D k₀ hk₀) : EvSprNonZeroMultiple F D k₀ hk₀ := by
  intro q hq hq0
  refine ⟨1, ?_, ?_⟩
  · exact (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
      sprCenterPolyK F 2 9 D c))).one_mem
  · rw [mul_one]
    intro h0
    exact hq0 (hInj q hq h0)

#print axioms evSprNonZeroMultiple_of_inj

/-- ★★★★★★★★★★ **`(β2)` ⟸ ①' ＋ ②w**。 -/
theorem sprTraceFrac_le_sprCenterImageField_of_traceFracMul (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hTF : TraceFracIntoCenterFrac F D) (hmul : EvSprNonZeroMultiple F D k₀ hk₀) :
    sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  classical
  intro x hx
  have hz : sprToSField F 2 9 k₀ hk₀ x
      ∈ IntermediateField.adjoin F (traceAlg F 2 9 : Set (SField F 2 9)) :=
    (mem_sprTraceFrac_iff F 2 9 hk₀).mp hx
  obtain ⟨p₀, q₀, hq₀0, hq₀A, hp₀A, hpq₀⟩ := hTF _ hz
  obtain ⟨r, hrA, hqr⟩ := hmul q₀ hq₀A hq₀0
  -- 换到 `q := q₀ * r`、`p := p₀ * r`
  set q : S F 2 9 := q₀ * r with hqdef
  set p : S F 2 9 := p₀ * r with hpdef
  have hqA : q ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
      sprCenterPolyK F 2 9 D c)) :=
    (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
      sprCenterPolyK F 2 9 D c))).mul_mem hq₀A hrA
  have hpA : p ∈ Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
      sprCenterPolyK F 2 9 D c)) :=
    (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
      sprCenterPolyK F 2 9 D c))).mul_mem hp₀A hrA
  have hqne : evSpr F 2 9 k₀ hk₀ q ≠ 0 := hqr
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hqne
    exact hqne (map_zero _)
  have hpqval : algebraMap (S F 2 9) (SField F 2 9) q * sprToSField F 2 9 k₀ hk₀ x
      = algebraMap (S F 2 9) (SField F 2 9) p := by
    rw [hqdef, hpdef, map_mul, map_mul]
    rw [mul_assoc, mul_comm (algebraMap (S F 2 9) (SField F 2 9) r)
      (sprToSField F 2 9 k₀ hk₀ x), ← mul_assoc, hpq₀]
  -- 以下与 §190 同构
  obtain ⟨a, b, hb, hbdiv⟩ := IsFractionRing.div_surjective (Spr F 2 9) x
  have hbmap : algebraMap (Spr F 2 9) (SprField F 2 9) b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hb
      ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxb : x * algebraMap (Spr F 2 9) (SprField F 2 9) b
      = algebraMap (Spr F 2 9) (SprField F 2 9) a := by
    rw [← hbdiv, div_mul_cancel₀ _ hbmap]
  have hxbS : sprToSField F 2 9 k₀ hk₀ x
        * algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ b)
      = algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ a) := by
    have h := congrArg (sprToSField F 2 9 k₀ hk₀) hxb
    simpa [map_mul, sprToSField_algebraMap] using h
  have hclear : q * sprToS F (r := 2) (n := 9) k₀ a
      = p * sprToS F (r := 2) (n := 9) k₀ b := by
    refine IsFractionRing.injective (S F 2 9) (SField F 2 9) ?_
    have hm := congrArg (fun t => t * algebraMap (S F 2 9) (SField F 2 9)
      (sprToS F (r := 2) (n := 9) k₀ b)) hpqval
    rw [mul_assoc, hxbS] at hm
    simpa [map_mul] using hm
  have hcan : evSpr F 2 9 k₀ hk₀ q * a = evSpr F 2 9 k₀ hk₀ p * b :=
    evSpr_sprToS_cancel F 2 9 k₀ hk₀ p q a b hclear
  have hxq : x * algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q)
      = algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p) := by
    have hb' : x = algebraMap (Spr F 2 9) (SprField F 2 9) a
        / algebraMap (Spr F 2 9) (SprField F 2 9) b := hbdiv.symm
    rw [hb']
    field_simp
    rw [← map_mul, ← map_mul]
    rw [mul_comm a (evSpr F 2 9 k₀ hk₀ q), mul_comm b (evSpr F 2 9 k₀ hk₀ p), hcan]
  have hmemQ : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    have hmem : evSpr F 2 9 k₀ hk₀ q ∈ Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c))) :=
      Subalgebra.mem_map.mpr ⟨q, hqA, rfl⟩
    rwa [sprCenterAlg_map_eq F D k₀ hk₀] at hmem
  have hmemP : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    have hmem : evSpr F 2 9 k₀ hk₀ p ∈ Subalgebra.map (evSpr F 2 9 k₀ hk₀)
        (Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
          sprCenterPolyK F 2 9 D c))) :=
      Subalgebra.mem_map.mpr ⟨p, hpA, rfl⟩
    rwa [sprCenterAlg_map_eq F D k₀ hk₀] at hmem
  have hqne' : algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q) ≠ 0 := by
    intro h0
    exact hqne ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxfin : x = algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ p)
      / algebraMap (Spr F 2 9) (SprField F 2 9) (evSpr F 2 9 k₀ hk₀ q) := by
    rw [eq_div_iff (by exact hqne')]
    exact hxq
  rw [hxfin]
  exact div_mem hmemP hmemQ

#print axioms sprTraceFrac_le_sprCenterImageField_of_traceFracMul

/-- ★★★★★★★★★★ **`hZ` ⟸ `(β1)` ＋ ①' ＋ ②w**。 -/
theorem zHalf_of_traceFrac_and_beta1Mul (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (hTF : TraceFracIntoCenterFrac F D) (hmul : EvSprNonZeroMultiple F D k₀ hk₀) :
    sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  le_trans h1 (sprTraceFrac_le_sprCenterImageField_of_traceFracMul F D k₀ hk₀ hTF hmul)

#print axioms zHalf_of_traceFrac_and_beta1Mul

end SprBetaTwoRouteWeakMul

/-! ## §192 ★★★★★★★★★★★★ **条件 ② 是定理** —— `(β2)` 只剩 ①'；`hZ` 只剩 `(β1)` ＋ ①'

第 667 轮。R664 把 `(β2)` 归约为「①' ＋ ②」，R665 把 ① 弱化到 ①'，R666 试图弱化 ②（**未成功**，
见下）。本轮给出**完全不同的结果：② 本身可证，无需任何假设。**

**证明（6 行，全部用已有件）**：设 `q ∈ A` 且 `evSpr q = 0`。
1. `A = Algebra.adjoin F (Set.range sprCenterPolyK) = (sprCenterPolyAlgHom D).range`
   （`AlgHom.range` 就是 `Algebra.adjoin F (Set.range ·)`）；
2. 故 `q = s_c` 对某个 `c ∈ C(F,n,r)` 成立（`AlgHom.mem_range`）——
   **注意 `{s_c}` 本身是子代数**（`sprCenterPolyAlgHom` 是环同态），故 `A` 恰是它的像；
3. `sprCenterK c = evSpr (s_c) = 0`（`sprCenterK = evSpr ∘ sprCenterPolyK`，**按定义**）；
4. 故 `sprCenterAlgHom c = algebraMap (sprCenterK c) = 0`；
5. `sprCenterAlgHom` **单射**（`sprCenterAlgHom_injective`，R257 已机检）⟹ `c = 0`；
6. 故 `q = s_0 = 0`。∎

**⟹ 剩余输入降为两条**（`hZ` 的两条，全部具名）：
```
hZ ⟸ (β1) N ≤ T   ＋   ①' Frac(traceAlg) ⊆ Frac(中心标量代数)
```

**⚠ 同时勘误 R666**：`②w`（§191）**不弱于** ②——`evSpr` 是环同态、`Spr` 是整环、`1 ∈ A`，
故 `evSpr(q)=0 ⟹ ∀r, evSpr(qr)=0`，于是 `②w ⟺ ②`（`evSprInjOnCenter_iff_nonZeroMultiple`）。
R666 的"严格弱化"声称**撤回**；那条的用途改为提供 ② 的**倍数形态**。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★★★★ `evSprInjOnCenter` | **条件 ② 是定理**（无条件） |
| ★★★★★★★★★★★★ `sprTraceFrac_le_sprCenterImageField` | **`(β2)` ⟸ ①'**（② 已消） |
| ★★★★★★★★★★★★ `zHalf_of_traceFrac` | **`hZ` ⟸ `(β1)` ＋ ①'** |
| ★★★★★★ `evSprInjOnCenter_iff_nonZeroMultiple` | **勘误**：②w ⟺ ②（R666 的弱化声称撤回） |

**诚实边界（勿夸大）**：`(β1)` 与 ①' **均未证**；`hZ` **未证**；**H2 见文件头「当前状态」。**
② 的消去是**实质**的（它曾是三条输入之一），但它只是**移除了一条**，不是收口。 -/

section SprBetaTwoRouteClosed

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★★★★★★★★ **条件 ② 是定理**：`evSpr` 在中心标量代数 `A` 上单射（**无条件**）。

机制：`A = (sprCenterPolyAlgHom D).range`，而 `sprCenterAlgHom = algebraMap ∘ sprCenterK = algebraMap ∘ evSpr ∘ sprCenterPolyK`
单射 ⟹ `evSpr|_A` 单射。 -/
theorem evSprInjOnCenter (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    EvSprInjOnCenter F D k₀ hk₀ := by
  classical
  intro q hq hq0
  set f := sprCenterPolyAlgHom F 2 9 D with hf
  have hrange : Algebra.adjoin F (Set.range (fun c : ↥(genericCenter F 2 9) =>
      sprCenterPolyK F 2 9 D c)) = f.range := by
    refine le_antisymm ?_ ?_
    · refine Algebra.adjoin_le_iff.mpr ?_
      rintro x ⟨c, rfl⟩
      exact ⟨c, rfl⟩
    · rintro x ⟨c, rfl⟩
      exact Algebra.subset_adjoin ⟨c, rfl⟩
  rw [hrange] at hq
  obtain ⟨c, rfl⟩ := (AlgHom.mem_range f).mp hq
  have hκ : sprCenterK F 2 9 k₀ hk₀ D c = 0 := by
    show evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D c) = 0
    exact hq0
  have hzero : sprCenterAlgHom F 2 9 D k₀ hk₀ c = 0 := by
    refine Subtype.ext ?_
    have h1 : ((sprCenterAlgHom F 2 9 D k₀ hk₀ c : ↥(sprNFixedAlg F 2 9)) : SprField F 2 9)
        = algebraMap (Spr F 2 9) (SprField F 2 9) (sprCenterK F 2 9 k₀ hk₀ D c) := rfl
    rw [h1, hκ, map_zero]
    rfl
  have hc0 : c = 0 := sprCenterAlgHom_injective F 2 9 D k₀ hk₀ (by rw [hzero, map_zero])
  rw [hc0]
  exact (sprCenterPolyAlgHom F 2 9 D).map_zero

#print axioms evSprInjOnCenter

/-- ★★★★★★ **勘误（撤回 R666 的弱化声称）**：②w（§191）与 ② **等价**。

`evSpr (q · r) = evSpr q · evSpr r` 且 `Spr` 是整环 ⟹ `evSpr q = 0` 杀死一切倍数；
反向由 `1 ∈ A`。 -/
theorem evSprInjOnCenter_iff_nonZeroMultiple (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    EvSprNonZeroMultiple F D k₀ hk₀ ↔ EvSprInjOnCenter F D k₀ hk₀ := by
  constructor
  · intro h q hq hq0
    by_contra hqne
    obtain ⟨r, _hrA, hqr⟩ := h q hq hqne
    rw [map_mul, hq0, zero_mul] at hqr
    exact hqr rfl
  · intro h
    exact evSprNonZeroMultiple_of_inj F D k₀ hk₀ h

#print axioms evSprInjOnCenter_iff_nonZeroMultiple

/-- ★★★★★★★★★★★★ **`(β2)` ⟸ ①'（条件 ② 已消）**。 -/
theorem sprTraceFrac_le_sprCenterImageField (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hTF : TraceFracIntoCenterFrac F D) :
    sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  sprTraceFrac_le_sprCenterImageField_of_traceFrac F D k₀ hk₀ hTF
    (evSprInjOnCenter F D k₀ hk₀)

#print axioms sprTraceFrac_le_sprCenterImageField

/-- ★★★★★★★★★★★★ **`hZ` ⟸ `(β1)` ＋ ①'**（两条，全部具名）。 -/
theorem zHalf_of_traceFrac (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (hTF : TraceFracIntoCenterFrac F D) :
    sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  le_trans h1 (sprTraceFrac_le_sprCenterImageField F D k₀ hk₀ hTF)

#print axioms zHalf_of_traceFrac

end SprBetaTwoRouteClosed

/-! ## §193 ★★★★★★★★★ **①' 归并到战役已具名的 `KPFixedLeZ`**（第 668 轮）

R665／R667 之后 `hZ` 只剩两条输入：`(β1) N ≤ T` 与 `①' Frac(traceAlg) ⊆ Frac(A)`。
本轮把 **①' 归并到战役早已具名的缺口 ⑤**（`KPFixedLeZ`，`GenericInv` §61，源文 `thm:14.16` 第二陈述）：

```
①'  ⟸  KPFixedLeZ
```

**证明（3 行）**：
1. `x ∈ Frac(traceAlg) ⟹ x ∈ K^{PGL}`（`traceField_le_pglFixedField`，R655 已机检）；
2. `KPFixedLeZ` 给 `z ∈ ZCanon` 使 `algebraMap z = x`（`↥(ZCanon)` 的 `algebraMap` 就是包含）；
3. **`zCanon_exists_frac`**（R219 已机检：`ZCanon` 的每个元都是两个中心纯量之商）
   给 `a b : ↥C`，`centK b ≠ 0` 且 `z · centK b = centK a`；
   再用库中已有的 **`centK_eq_algebraMap_polyK`**（`H2Final:3443`）把 `centK c` 写成 `algebraMap (s_c)`，
   取 `p := s_a`、`q := s_b` 即得 `algebraMap q · x = algebraMap p`。∎

**⟹ 输入清单（两条）**：

| 输入 | 内容 | 出处 |
|---|---|---|
| `(β1)` | `N ≤ T`（`sprNFixedField ≤ sprTraceFrac`） | 纯迹域陈述，**未证** |
| `KPFixedLeZ` | `K^{PGL} ⊆ Z`（缺口 ⑤） | **战役已具名**，`GenericInv:4471`；源文 `thm:14.16` 第二陈述（T3） |

且 `KPFixedLeZ` 本身已有派生路（`kPFixedLeZ_of_centreUD`，§92：由 `(A)` ＋ `CentreUDLeZ` 推出），
故它**不是新输入**。

| 件 | 内容 |
|---|---|
| （复用）`centK_eq_algebraMap_polyK` | `centK c = algebraMap (s_c)`（**库中已有**，`H2Final:3443`） |
| ★★★★★★★★★ `traceFracIntoCenterFrac_of_kpfixedLeZ` | **`①' ⟸ KPFixedLeZ`** |
| ★★★★★★★★★ `sprTraceFrac_le_sprCenterImageField_of_kpfixedLeZ` | **`(β2) ⟸ KPFixedLeZ`** |
| ★★★★★★★★★ `zHalf_of_kpfixedLeZ_and_beta1` | **`hZ ⟸ `(β1)` ＋ `KPFixedLeZ`** |

**诚实边界（勿夸大）**：`(β1)`／`KPFixedLeZ` **均未证**；`hZ` **未证**；**H2 见文件头「当前状态」。**
本轮是**输入归并**，不是新数学。 -/

section SprBetaTwoRouteMerge

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **①' ⟸ `KPFixedLeZ`**（缺口 ⑤ ⟹ 迹域落在中心标量分式域里）。 -/
theorem traceFracIntoCenterFrac_of_kpfixedLeZ (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (hKPZ : KPFixedLeZ F 2 9 D) :
    TraceFracIntoCenterFrac F D := by
  intro x hx
  have hPGL : ∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ, phiKEquiv F 2 9 A x = x :=
    fun A => traceField_le_pglFixedField F 2 hx A
  obtain ⟨z, hz⟩ := hKPZ x hPGL
  obtain ⟨a, b, hb0, hb⟩ := zCanon_exists_frac F 2 9 D z.val z.2
  refine ⟨sprCenterPolyK F 2 9 D a, sprCenterPolyK F 2 9 D b, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hb0 (by rw [centK_eq_algebraMap_polyK F 2 9 D b, h0, map_zero])
  · exact Algebra.subset_adjoin ⟨b, rfl⟩
  · exact Algebra.subset_adjoin ⟨a, rfl⟩
  · rw [← centK_eq_algebraMap_polyK F 2 9 D b, ← centK_eq_algebraMap_polyK F 2 9 D a, ← hz]
    show D.centK b * z.val = D.centK a
    rw [mul_comm, hb]

#print axioms traceFracIntoCenterFrac_of_kpfixedLeZ

/-- ★★★★★★★★★ **`(β2) ⟸ KPFixedLeZ`**。 -/
theorem sprTraceFrac_le_sprCenterImageField_of_kpfixedLeZ (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hKPZ : KPFixedLeZ F 2 9 D) :
    sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  sprTraceFrac_le_sprCenterImageField F D k₀ hk₀
    (traceFracIntoCenterFrac_of_kpfixedLeZ F D hKPZ)

#print axioms sprTraceFrac_le_sprCenterImageField_of_kpfixedLeZ

/-- ★★★★★★★★★ **`hZ ⟸ (β1) ＋ KPFixedLeZ`**（两条输入，后者是战役已具名的缺口 ⑤）。 -/
theorem zHalf_of_kpfixedLeZ_and_beta1 (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h1 : sprNFixedField F 2 9 ≤ sprTraceFrac F 2 9 k₀ hk₀)
    (hKPZ : KPFixedLeZ F 2 9 D) :
    sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀ :=
  le_trans h1 (sprTraceFrac_le_sprCenterImageField_of_kpfixedLeZ F D k₀ hk₀ hKPZ)

#print axioms zHalf_of_kpfixedLeZ_and_beta1

end SprBetaTwoRouteMerge

/-! ## §194 ★★★★★★★★★★ **`(b)` `P ≤ C` 也是定理的推论** —— `hZ` 的两条输入之一从 `(β1)` **弱化到 `(a)`**

第 669 轮。R668 之后 `hZ` 的输入是 `(β1) N ≤ T` ＋ `KPFixedLeZ`。本轮证 `(b) P ≤ C`：

```
(b) ⟸ KPFixedLeZ
```

**证明（与 §192 的 ② 同机制）**：设 `x ∈ P`（即 `x ∈ K'` 且 `sprToSField x ∈ K^{PGL}`）。
1. `KPFixedLeZ` 给 `z ∈ ZCanon` 使 `z.val = sprToSField x`；
2. `zCanon_exists_frac` 给 `a b`：`centK b ≠ 0` 且 `z.val · centK b = centK a`；
   `centK_eq_algebraMap_polyK` 把它写成 `sprToSField x · algebraMap (s_b) = algebraMap (s_a)`；
3. 把 `x` 写成 `Spr` 分式 `x = a'/b'`，升到 `S` 得 `sprToSField x · algebraMap (sprToS b') = algebraMap (sprToS a')`；
4. 两式相乘并清分母 ⟹ `sprToS a' · s_b = s_a · sprToS b'`（`S → SField` 单射）；
5. **`evSpr_sprToS_cancel`** ⟹ `evSpr (s_b) · a' = evSpr (s_a) · b'`；
6. **② 是定理**（§192 `evSprInjOnCenter`）⟹ `evSpr (s_b) ≠ 0`（否则 `s_b = 0` ⟹ `centK b = 0`，与 2 矛盾）；
7. 故 `x = evSpr (s_a) / evSpr (s_b)`，而 `evSpr (s_c) = sprCenterK c` 的 `algebraMap`-像在 `C` 里（§189）⟹ `x ∈ C`。∎

**⟹ 战役终点的输入降为两条，且都更弱/更有出处**：

```
ZEqNFixed（＝ H2）⟸ (a) N ≤ P   ＋   KPFixedLeZ
```

`(a)` **严格弱于** `(β1)`（`T ≤ P` ⟹ `(β1) ⟹ (a)`，反之未知）。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `sprPGLFixedField_le_sprCenterImageField_of_kpfixedLeZ` | **`(b)` ⟸ `KPFixedLeZ`** |
| ★★★★★★★★★★★★ `zEqNFixed_of_kpfixedLeZ_and_a` | **`ZEqNFixed` ⟸ `(a)` ＋ `KPFixedLeZ`** |
| ★★★★★★★★★★★★ `h2_of_kpfixedLeZ_and_a` | **H2 ⟸ `(a)` ＋ `KPFixedLeZ`** |

**诚实边界（勿夸大）**：`(a)`／`KPFixedLeZ` **均未证**；`ZEqNFixed`／H2 **均未证**；
**H2 见文件头「当前状态」。** -/

section SprBetaTwoRouteB

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **`(b)` `P ≤ C` ⟸ `KPFixedLeZ`**。 -/
theorem sprPGLFixedField_le_sprCenterImageField_of_kpfixedLeZ (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hKPZ : KPFixedLeZ F 2 9 D) :
    sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  classical
  intro x hx
  have hPGL : ∀ A : (Matrix (Fin 9) (Fin 9) F)ˣ,
      phiKEquiv F 2 9 A (sprToSField F 2 9 k₀ hk₀ x) = sprToSField F 2 9 k₀ hk₀ x :=
    fun A => (mem_sprPGLFixedField_iff F 2 hk₀).mp hx A
  obtain ⟨z, hz⟩ := hKPZ _ hPGL
  obtain ⟨a, b, hb0, hb⟩ := zCanon_exists_frac F 2 9 D z.val z.2
  have hA : sprToSField F 2 9 k₀ hk₀ x
        * algebraMap (S F 2 9) (SField F 2 9) (sprCenterPolyK F 2 9 D b)
      = algebraMap (S F 2 9) (SField F 2 9) (sprCenterPolyK F 2 9 D a) := by
    have h4 : (algebraMap ↥(ZCanon F 2 9 D) (SField F 2 9) z) * D.centK b = D.centK a := hb
    rw [hz, centK_eq_algebraMap_polyK F 2 9 D b, centK_eq_algebraMap_polyK F 2 9 D a] at h4
    exact h4
  obtain ⟨a', b', hb', hb'div⟩ := IsFractionRing.div_surjective (Spr F 2 9) x
  have hb'map : algebraMap (Spr F 2 9) (SprField F 2 9) b' ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hb'
      ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxb : x * algebraMap (Spr F 2 9) (SprField F 2 9) b'
      = algebraMap (Spr F 2 9) (SprField F 2 9) a' := by
    rw [← hb'div, div_mul_cancel₀ _ hb'map]
  have hB : sprToSField F 2 9 k₀ hk₀ x
        * algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ b')
      = algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ a') := by
    have h := congrArg (sprToSField F 2 9 k₀ hk₀) hxb
    simpa [map_mul, sprToSField_algebraMap] using h
  have hC' : algebraMap (S F 2 9) (SField F 2 9) (sprCenterPolyK F 2 9 D b)
        * algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ a')
      = algebraMap (S F 2 9) (SField F 2 9) (sprCenterPolyK F 2 9 D a)
        * algebraMap (S F 2 9) (SField F 2 9) (sprToS F (r := 2) (n := 9) k₀ b') := by
    rw [← hB, ← hA]
    ring
  have hC : sprCenterPolyK F 2 9 D b * sprToS F (r := 2) (n := 9) k₀ a'
      = sprCenterPolyK F 2 9 D a * sprToS F (r := 2) (n := 9) k₀ b' := by
    refine IsFractionRing.injective (S F 2 9) (SField F 2 9) ?_
    rw [map_mul, map_mul]
    exact hC'
  have hcan : evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b) * a'
      = evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D a) * b' :=
    evSpr_sprToS_cancel F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D a)
      (sprCenterPolyK F 2 9 D b) a' b' hC
  have hqne : evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b) ≠ 0 := by
    intro h0
    have hsb : sprCenterPolyK F 2 9 D b = 0 :=
      evSprInjOnCenter F D k₀ hk₀ (sprCenterPolyK F 2 9 D b)
        (Algebra.subset_adjoin ⟨b, rfl⟩) h0
    refine hb0 ?_
    rw [centK_eq_algebraMap_polyK F 2 9 D b, hsb, map_zero]
  have hxq : x * algebraMap (Spr F 2 9) (SprField F 2 9)
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b))
      = algebraMap (Spr F 2 9) (SprField F 2 9)
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D a)) := by
    have hb' : x = algebraMap (Spr F 2 9) (SprField F 2 9) a'
        / algebraMap (Spr F 2 9) (SprField F 2 9) b' := hb'div.symm
    rw [hb']
    field_simp
    rw [← map_mul, ← map_mul]
    rw [mul_comm a' (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b)),
      mul_comm b' (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D a)), hcan]
  have hmemQ : algebraMap (Spr F 2 9) (SprField F 2 9)
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b))
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    exact Algebra.subset_adjoin ⟨b, rfl⟩
  have hmemP : algebraMap (Spr F 2 9) (SprField F 2 9)
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D a))
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
    apply sprCenterAlg_le_sprCenterImageField F D k₀ hk₀
    exact Algebra.subset_adjoin ⟨a, rfl⟩
  have hqne' : algebraMap (Spr F 2 9) (SprField F 2 9)
      (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b)) ≠ 0 := by
    intro h0
    exact hqne ((IsFractionRing.injective (Spr F 2 9) (SprField F 2 9)) (by simpa using h0))
  have hxfin : x = algebraMap (Spr F 2 9) (SprField F 2 9)
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D a))
      / algebraMap (Spr F 2 9) (SprField F 2 9)
        (evSpr F 2 9 k₀ hk₀ (sprCenterPolyK F 2 9 D b)) := by
    rw [eq_div_iff (by exact hqne')]
    exact hxq
  rw [hxfin]
  exact div_mem hmemP hmemQ

#print axioms sprPGLFixedField_le_sprCenterImageField_of_kpfixedLeZ

/-- ★★★★★★★★★★★★ **`ZEqNFixed` ⟸ `(a)` ＋ `KPFixedLeZ`**（`(b)` 已消）。 -/
theorem zEqNFixed_of_kpfixedLeZ_and_a (F : Type) [Field F] [CharZero F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (ha : sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀)
    (hKPZ : KPFixedLeZ F 2 9 D) :
    ZEqNFixed F D :=
  zEqNFixed_of_pglFixed F D hk₀ ha
    (sprPGLFixedField_le_sprCenterImageField_of_kpfixedLeZ F D k₀ hk₀ hKPZ)

#print axioms zEqNFixed_of_kpfixedLeZ_and_a

/-- ★★★★★★★★★★★★ **H2 ⟸ `(a)` ＋ `KPFixedLeZ`**。 -/
theorem h2_of_kpfixedLeZ_and_a (F : Type) [Field F] [CharZero F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (ha : sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀)
    (hKPZ : KPFixedLeZ F 2 9 D) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_pglFixed F D hk₀ ha
    (sprPGLFixedField_le_sprCenterImageField_of_kpfixedLeZ F D k₀ hk₀ hKPZ)

#print axioms h2_of_kpfixedLeZ_and_a

end SprBetaTwoRouteB

/-! ## §195 ★★★★★★★★★★★ **`(a)` 与 `(β1)` 的反例**：`∏_i x_{k₀,ii}` —— R668／R669 的归约**空洞**

第 670 轮。R668／R669 把 `hZ` 归约到 `(β1) N ≤ T`（R668）与 `(a) N ≤ P`（R669）。
本轮给出**反例**，两者**同时为假**。

**反例（`x := ∏ i, x_{k₀,ii}`，即对角元的乘积）**：
1. **`x ∈ K'^N`（机检）**：`sprDiagHom_X_inl`（环面固定 `x_i`）＋ `sprPermAlgEquiv_X_inl`
   ＋ `Equiv.prod_comp`（置换只是重排乘积）⟹ `sprNFixed`；再 `algebraMap` 升到 `K'`。
2. **`x ∉ K' ∩ K^{PGL}`（论证级，§185 的显式计算）**：取 `A = 1 + E_{01}`，则
   `(A⁻¹X_{k₀}A)_{00} = x_{k₀,00} − x_{k₀,10}`、`(A⁻¹X_{k₀}A)_{11} = x_{k₀,10} + x_{k₀,11}`，
   其余对角元不变 ⟹ `φ_A(x) ≠ x` ⟹ `sprToSField x = ∏ x_{k₀,ii} ∉ pglFixedField` ⟹ `x ∉ P`。
   （**注意**：`∏_i x_{k₀,ii}` **不是** `det(X_{k₀})`——后者是 PGL-不变量；前者只是对角元之积。）

**⟹ 后果（必须登记，不得含糊）**：
* `(a) : N ≤ P` **假**；
* `(β1) : N ≤ T` **假**（因 `(β1) ⟹ (a)` 已机检 `pglFixed_imp_of_traceFrac`）；
* 故 **R668 的 `hZ ⟸ (β1) ＋ KPFixedLeZ` 与 R669 的 `H2 ⟸ (a) ＋ KPFixedLeZ` 都是空洞条件**
  （命题本身为真，但前提为假 ⟹ 无信息）。
* §182 的边 ⑦（`(a) ∧ (b) ⟹ hZ`）与边 ②（`(β1) ⟹ (a)`）**随之失效**（前提永假）。

**⟹ 存活路径**：`(β2) T ≤ C`（R667／R668 已机检，**不受影响**——方向相反）。
`hZ` 的正确形状仍是 `N = C`，须另找充分条件。

| 件 | 内容 |
|---|---|
| ★★★★★★ `sprProdX_mem_sprNFixed` | `∏_i x_i ∈ S'^N`（机检） |
| ★★★★★★ `sprProdX_mem_sprNFixedField` | 其像在 `K'^N` 里（机检） |
| ★★★★★★★ `sprProdX_mem_sprPGLFixedField_of_a` | **`(a) ⟹ 其像 ∈ P`**（反例的机器形态） |
| ★★★★★★★ `not_a_of_prodX_not_mem` | **`∏ x_i ∉ P ⟹ ¬(a)`** |
| ★★★★★★★ `not_beta1_of_not_a` | **`¬(a) ⟹ ¬(β1)`**（两者同死） |

**诚实边界（勿夸大）**：`∏_i x_{k₀,ii} ∉ pglFixedField` 是**论证级**（未机检，标 `⚠-contentious`，
与 §185 同源）；`¬(a)`／`¬(β1)` 因此是**条件性**结论。`hZ`／H2 **仍未证**，**H2 见文件头「当前状态」。** -/

section SprProdXCounterexample

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★★ **对角元之积在环面下不动**（`sprDiagHom_X_inl` ＋ `map_prod`）。 -/
theorem sprProdX_torus (F : Type) [Field F] (r n : ℕ) (b : Fin n → Fˣ) :
    (sprDiagHom F r n b) (∏ i : Fin n, MvPolynomial.X (Sum.inl i))
      = ∏ i : Fin n, MvPolynomial.X (Sum.inl i) := by
  rw [map_prod]
  simp only [sprDiagHom_X_inl]

#print axioms sprProdX_torus

/-- ★★★★★★ **对角元之积在 `S_n` 下不动**（`sprPermAlgEquiv_X_inl` ＋ `Equiv.prod_comp`）。 -/
theorem sprProdX_perm (F : Type) [Field F] (r n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (sprPermAlgEquiv F r n σ) (∏ i : Fin n, MvPolynomial.X (Sum.inl i))
      = ∏ i : Fin n, MvPolynomial.X (Sum.inl i) := by
  rw [map_prod]
  simp only [sprPermAlgEquiv_X_inl]
  exact Equiv.prod_comp σ (fun i => MvPolynomial.X (Sum.inl (i : Fin n)))

#print axioms sprProdX_perm

/-- ★★★★★★ **`∏_i x_i ∈ S'^N`**（多项式层）。 -/
theorem sprProdX_mem_sprNFixed (F : Type) [Field F] (r n : ℕ) :
    sprNFixed F r n (∏ i : Fin n, MvPolynomial.X (Sum.inl i)) :=
  ⟨fun b => sprProdX_torus F r n b, fun σ => sprProdX_perm F r n σ⟩

#print axioms sprProdX_mem_sprNFixed

/-- ★★★★★★ **`∏_i x_i` 的像在 `K'^N` 里**（分式域层）。 -/
theorem sprProdX_mem_sprNFixedField (F : Type) [Field F] (r n : ℕ) :
    algebraMap (Spr F r n) (SprField F r n)
        (∏ i : Fin n, MvPolynomial.X (Sum.inl i)) ∈ sprNFixedField F r n := by
  rw [mem_sprNFixedField_iff]
  exact ⟨sprFieldTFixed_algebraMap F r n (sprProdX_mem_sprNFixed F r n).1,
    sprFieldSFixed_algebraMap F r n (sprProdX_mem_sprNFixed F r n).2⟩

#print axioms sprProdX_mem_sprNFixedField

/-- ★★★★★★★ **反例的机器形态**：`(a)` 迫使对角元之积落进 `K' ∩ K^{PGL}`（`n = 9`）。 -/
theorem sprProdX_mem_sprPGLFixedField_of_a (F : Type) [Field F] (r : ℕ)
    (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (ha : sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀) :
    algebraMap (Spr F r 9) (SprField F r 9)
        (∏ i : Fin 9, MvPolynomial.X (Sum.inl i)) ∈ sprPGLFixedField F r k₀ hk₀ :=
  ha (sprProdX_mem_sprNFixedField F r 9)

#print axioms sprProdX_mem_sprPGLFixedField_of_a

/-- ★★★★★★★ **`∏_i x_i ∉ P` ⟹ `¬(a)`**（`n = 9`）。 -/
theorem not_a_of_prodX_not_mem (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0)
    (h : algebraMap (Spr F r 9) (SprField F r 9)
        (∏ i : Fin 9, MvPolynomial.X (Sum.inl i)) ∉ sprPGLFixedField F r k₀ hk₀) :
    ¬ (sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀) :=
  fun ha => h (sprProdX_mem_sprPGLFixedField_of_a F r k₀ hk₀ ha)

#print axioms not_a_of_prodX_not_mem

/-- ★★★★★★★ **`¬(a) ⟹ ¬(β1)`**：两条输入**同死**（`(β1) ⟹ (a)` 已机检）。 -/
theorem not_beta1_of_not_a (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0)
    (h : ¬ (sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀)) :
    ¬ (sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀) :=
  fun h1 => h (pglFixed_imp_of_traceFrac F r k₀ hk₀ h1)

#print axioms not_beta1_of_not_a

end SprProdXCounterexample

/-! ## §196 ★★★★★★★★ **`hZ` 的新可证伪点 ＋ `KPFixedLeZ` 单独**不能**给出 `hZ`**（第 671 轮）

R670 证伪了 `(a)`／`(β1)`。本轮把 `∏_i x_{k₀,ii}` 这个元素**再向前推一步**，得到两条结论：

**(1) `hZ` 的新可证伪点**：`hZ`（`N ≤ C`）**必迫使** `∏_i x_{k₀,ii} ∈ C`（因为它已在 `K'^N` 里，R670 机检）。

**(2) ★ `KPFixedLeZ` 单独不可能给出 `hZ`**（这是本轮的结构性结论）：
`KPFixedLeZ` 能推出来的东西只有
* `(β2) T ≤ C`（R667／R668 机检），
* `(b) P ≤ C`（R669 机检）；
而这两条都只产出 `P`／`T` 里的元素。可是 `∏_i x_{k₀,ii} ∈ K'^N`（机检）而
**`∏_i x_{k₀,ii} ∉ P`**（§185 的显式计算，`⚠-contentious`）。故 `hZ` 需要的 `C` **严格大于 `P`**，
`KPFixedLeZ` 的射程**原理上不够**。
⟹ **必须另找产出 `C` 的新元素的机制**（不能只靠"`K^{PGL}`-侧"的输入）。

**⟹ 由此得到的策略判读**：`hZ` 的两侧不对称——
`C` 是**中心标量**的像（`sprCenterK`），`N` 是**环面＋置换**的不动域；
`KPFixedLeZ` 只把 `K^{PGL}` 接进 `Z`，而 `N ⊄ K^{PGL}`。要证 `N ≤ C`，必须**直接用 `C` 的生成元**
（即 `s_c` 的具体表达式），而非经由 `K^{PGL}`。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `sprProdX_mem_sprCenterImageField_of_zHalf` | **`hZ ⟹ ∏_i x_{k₀,ii} ∈ C`**（新可证伪点） |
| ★★★★★★★ `sprProdX_mem_of_kpfixedLeZ_paths` | `KPFixedLeZ` 的两条推论（`T ≤ C`、`P ≤ C`）的**并列登记**，供对照 |

**诚实边界（勿夸大）**：`∏_i x_{k₀,ii} ∈ C` **未证亦未证伪**；`hZ` **未证**；**H2 见文件头「当前状态」。**
本节不含新证明技术；它的价值是把"`KPFixedLeZ` 路线到此为止"这件事**机检地**说清楚。 -/

section SprProdXTest

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★★★★ **`hZ` 的新可证伪点**：`hZ` 迫使其对角元之积落进 `C`。 -/
theorem sprProdX_mem_sprCenterImageField_of_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    algebraMap (Spr F 2 9) (SprField F 2 9)
        (∏ i : Fin 9, MvPolynomial.X (Sum.inl i)) ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  hZ (sprProdX_mem_sprNFixedField F 2 9)

#print axioms sprProdX_mem_sprCenterImageField_of_zHalf

/-- ★★★★★★★ **`KPFixedLeZ` 的两条推论的并列登记**（`(β2)` 与 `(b)`）：
两者都只产出 `T`／`P` 里的元素，而 `hZ` 需要 `∏_i x_{k₀,ii} ∈ C`。 -/
theorem kpfixedLeZ_consequences_do_not_reach_prodX (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hKPZ : KPFixedLeZ F 2 9 D) :
    (sprTraceFrac F 2 9 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀)
      ∧ (sprPGLFixedField F 2 k₀ hk₀ ≤ sprCenterImageField F 2 9 D k₀ hk₀) :=
  ⟨sprTraceFrac_le_sprCenterImageField_of_kpfixedLeZ F D k₀ hk₀ hKPZ,
   sprPGLFixedField_le_sprCenterImageField_of_kpfixedLeZ F D k₀ hk₀ hKPZ⟩

#print axioms kpfixedLeZ_consequences_do_not_reach_prodX

end SprProdXTest



/-! ## §197 ★★★★★★★★★★ **`∏_i x_{k₀,ii} ∉ K' ∩ K^{PGL}` 机检** —— R670 反例链末环闭合（第 672 轮）

R670（§195）与 R671（§196）的全部结论都悬在**一条论证级**断言上：

> `∏_i x_{k₀,ii} ∉ pglFixedField`（§185 的显式计算，此前标 `⚠-contentious`）。

本轮把它**机检**。取单能单位 `A₀ = 1 + E₀₁`（`E₀₁ = single 0 1 1`，故 `A₀⁻¹ = 1 − E₀₁`）。
其共轭 `φ_{A₀}(x_{k,i,j}) = ((1−E₀₁)·X_k·(1+E₀₁))_{ij}` 只改动 `i ∈ {0,1}` 两个对角元：

| 对角元 | `φ_{A₀}` 下的像 |
|---|---|
| `i = 0` | `x_{k,00} − x_{k,10}` |
| `i = 1` | `x_{k,11} + x_{k,10}` |
| `i ≥ 2` | `x_{k,ii}`（不变） |

故 `φ_{A₀}(∏_i x_{k,ii}) = (x_{00} − x_{10})(x_{10} + x_{11})·∏_{i≥2} x_{ii} ≠ ∏_i x_{k,ii}`：
全体不定元取 `1` 的赋值（`sprEvalOne`）把左式送到 `(1−1)(1+1)·1 = 0`、右式送到 `1`。

**⟹ 由此升为定理**（不再带 `⚠`）：

* `sprProdX_not_mem_sprPGLFixedField`：`∏_i x_{k₀,ii} ∉ K' ∩ K^{PGL}`；
* `not_a_prodX`：**`(a) : K'^N ≤ K' ∩ K^{PGL}` 假**；
* `not_beta1_prodX`：**`(β1) : K'^N ≤ K' ∩ Frac(traceAlg)` 假**（经 `pglFixed_imp_of_traceFrac`）。

**⟹ 射程（勿夸大）**：`hZ`（`N ≤ C`）**未证**，**H2 见文件头「当前状态」。**本节只把 R670–R671 的
反例链由论证级升为机检级，从而**确定**了输入清单：`(a)`／`(β1)` 两条**永不再可能是出路**。 -/

section SprProdXPGL

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- `E₀₁ = single 0 1 1`（矩阵单位）。 -/
def sprE01 (R : Type) [CommRing R] : Matrix (Fin 9) (Fin 9) R := Matrix.single 0 1 1

/-- `E₀₁² = 0`（因 `1 ≠ 0` 在 `Fin 9` 中）。 -/
lemma sprE01_sq (R : Type) [CommRing R] : sprE01 R * sprE01 R = 0 := by
  rw [sprE01, single_mul_single, if_neg (by decide : ¬ ((1 : Fin 9) = 0))]

/-- 左乘 `E₀₁`：`(E₀₁ · M) a b = if a = 0 then M 1 b else 0`。 -/
lemma sprE01_mul_apply (R : Type) [CommRing R] (M : Matrix (Fin 9) (Fin 9) R)
    (a b : Fin 9) : (sprE01 R * M) a b = if a = 0 then M 1 b else 0 := by
  rw [sprE01, Matrix.mul_apply]
  split_ifs with ha
  · rw [Finset.sum_eq_single (1 : Fin 9)]
    · rw [Matrix.single_apply, if_pos ⟨ha.symm, rfl⟩]
      simp
    · intro l _ hl
      have h : ¬((0 : Fin 9) = a ∧ (1 : Fin 9) = l) := by
        rintro ⟨-, h2⟩
        exact hl h2.symm
      rw [Matrix.single_apply, if_neg h]
      simp
    · intro h
      exact absurd (Finset.mem_univ (1 : Fin 9)) h
  · refine Finset.sum_eq_zero fun l _ => ?_
    have h : ¬((0 : Fin 9) = a ∧ (1 : Fin 9) = l) := by
      rintro ⟨h1, -⟩
      exact ha h1.symm
    rw [Matrix.single_apply, if_neg h]
    simp

/-- 右乘 `E₀₁`：`(M · E₀₁) a b = if b = 1 then M a 0 else 0`。 -/
lemma mul_sprE01_apply (R : Type) [CommRing R] (M : Matrix (Fin 9) (Fin 9) R)
    (a b : Fin 9) : (M * sprE01 R) a b = if b = 1 then M a 0 else 0 := by
  rw [sprE01, Matrix.mul_apply]
  split_ifs with hb
  · rw [Finset.sum_eq_single (0 : Fin 9)]
    · rw [Matrix.single_apply, if_pos ⟨rfl, hb.symm⟩]
      simp
    · intro l _ hl
      have h : ¬((0 : Fin 9) = l ∧ (1 : Fin 9) = b) := by
        rintro ⟨h1, -⟩
        exact hl h1.symm
      rw [Matrix.single_apply, if_neg h]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 9)) h
  · refine Finset.sum_eq_zero fun l _ => ?_
    have h : ¬((0 : Fin 9) = l ∧ (1 : Fin 9) = b) := by
      rintro ⟨-, h2⟩
      exact hb h2.symm
    rw [Matrix.single_apply, if_neg h]
    simp

/-- ★ **单能共轭的对角元公式**：`((1−E₀₁)·M·(1+E₀₁)) a a`。

**推导**：`(1−E)M(1+E) = M − EM + ME − EME`（`noncomm_ring`），逐项用上面两条乘法公式；
`EME` 的对角元为 `0`（因 `a = 0 ∧ a = 1` 不可能）。 -/
lemma unipotent_diag_entry (R : Type) [CommRing R] (M : Matrix (Fin 9) (Fin 9) R)
    (a : Fin 9) :
    ((1 - sprE01 R) * M * (1 + sprE01 R : Matrix (Fin 9) (Fin 9) R)) a a
      = M a a + (if a = 1 then M a 0 else 0) - (if a = 0 then M 1 a else 0) := by
  have hM : ((1 - sprE01 R) * M * (1 + sprE01 R))
      = M - sprE01 R * M + (M * sprE01 R - sprE01 R * M * sprE01 R) := by
    noncomm_ring
  have hEE : (sprE01 R * M * (sprE01 R : Matrix (Fin 9) (Fin 9) R)) a a = 0 := by
    rw [Matrix.mul_assoc, sprE01_mul_apply]
    split_ifs with ha
    · rw [mul_sprE01_apply]
      have h : ¬((0 : Fin 9) = 1) := by decide
      rw [if_neg (by rw [ha]; exact h)]
    · rfl
  rw [hM, Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply,
    sprE01_mul_apply, mul_sprE01_apply, hEE, sub_zero]
  ring

/-- ★ 单能单位 `A₀ = 1 + E₀₁`（逆为 `1 − E₀₁`）。 -/
def sprUnipotentUnit (R : Type) [CommRing R] : (Matrix (Fin 9) (Fin 9) R)ˣ where
  val := 1 + sprE01 R
  inv := 1 - sprE01 R
  val_inv := by
    have h : (1 + sprE01 R) * (1 - sprE01 R) = 1 - sprE01 R * sprE01 R := by noncomm_ring
    rw [h, sprE01_sq, sub_zero]
  inv_val := by
    have h : (1 - sprE01 R) * (1 + sprE01 R) = 1 - sprE01 R * sprE01 R := by noncomm_ring
    rw [h, sprE01_sq, sub_zero]

/-- `A₀` 的矩阵就是 `1 + E₀₁`。 -/
lemma sprUnipotentUnit_val (R : Type) [CommRing R] :
    ((sprUnipotentUnit R : (Matrix (Fin 9) (Fin 9) R)ˣ) : Matrix (Fin 9) (Fin 9) R)
      = 1 + sprE01 R := rfl

/-- `A₀⁻¹` 的矩阵就是 `1 − E₀₁`。 -/
lemma sprUnipotentUnit_inv (R : Type) [CommRing R] :
    ((sprUnipotentUnit R)⁻¹ : (Matrix (Fin 9) (Fin 9) R)ˣ)
      = (1 - sprE01 R : Matrix (Fin 9) (Fin 9) R) := rfl

/-- `constMat` 把 `E₀₁` 送到 `S` 层的 `E₀₁`。 -/
lemma constMat_sprE01 (F : Type) [Field F] (r : ℕ) :
    constMat F r 9 (sprE01 F) = sprE01 (S F r 9) := by
  ext i j
  rw [sprE01, sprE01, constMat, Matrix.map_apply]
  simp [Matrix.single_apply]

/-- `constMat` 把 `A₀` 送到 `1 + E₀₁`。 -/
lemma constMat_sprUnipotentUnit_val (F : Type) [Field F] (r : ℕ) :
    constMat F r 9 (↑(sprUnipotentUnit F)) = 1 + sprE01 (S F r 9) := by
  have hcoe : (↑(sprUnipotentUnit F) : Matrix (Fin 9) (Fin 9) F) = 1 + sprE01 F := rfl
  rw [hcoe]
  rw [show constMat F r 9 (1 + sprE01 F)
      = constMat F r 9 (1 : Matrix (Fin 9) (Fin 9) F) + constMat F r 9 (sprE01 F) from
    Matrix.map_add _ (fun a b => map_add _ a b) (1 : Matrix (Fin 9) (Fin 9) F) (sprE01 F)]
  rw [constMat_one, constMat_sprE01]

/-- `constMat` 把 `A₀⁻¹` 送到 `1 − E₀₁`。 -/
lemma constMat_sprUnipotentUnit_inv (F : Type) [Field F] (r : ℕ) :
    constMat F r 9 (↑((sprUnipotentUnit F)⁻¹)) = 1 - sprE01 (S F r 9) := by
  have hcoe : (↑((sprUnipotentUnit F)⁻¹) : Matrix (Fin 9) (Fin 9) F) = 1 - sprE01 F := rfl
  rw [hcoe]
  rw [show constMat F r 9 (1 - sprE01 F)
      = constMat F r 9 (1 : Matrix (Fin 9) (Fin 9) F) - constMat F r 9 (sprE01 F) from
    Matrix.map_sub _ (fun a b => map_sub _ a b) (1 : Matrix (Fin 9) (Fin 9) F) (sprE01 F)]
  rw [constMat_one, constMat_sprE01]

/-- ★ `φ_{A₀}` 在 `X_{k₀}` 的**对角元**上的作用（`A₀ = 1 + E₀₁`）。 -/
lemma phiA_sprUnipotentUnit_diag (F : Type) [Field F] (r : ℕ) (k : Fin r) (a : Fin 9) :
    phiA F r 9 (sprUnipotentUnit F) (MvPolynomial.X (k, a, a))
      = MvPolynomial.X (k, a, a)
        + (if a = 1 then MvPolynomial.X (k, a, 0) else 0)
        - (if a = 0 then MvPolynomial.X (k, 1, a) else 0) := by
  rw [phiA_var, constMat_sprUnipotentUnit_inv, constMat_sprUnipotentUnit_val]
  exact unipotent_diag_entry (S F r 9) (genericMatrix F r 9 k) a

/-- 全体不定元取 `1` 的赋值 `S →ₐ[F] F`（用于区分两个多项式）。 -/
noncomputable def sprEvalOne (F : Type) [Field F] (r : ℕ) : S F r 9 →ₐ[F] F :=
  MvPolynomial.aeval (fun _ => (1 : F))

/-- `sprEvalOne` 在不定元上取值为 `1`。 -/
lemma sprEvalOne_X (F : Type) [Field F] (r : ℕ) (s : Fin r × Fin 9 × Fin 9) :
    sprEvalOne F r (MvPolynomial.X s) = 1 :=
  MvPolynomial.aeval_X _ s

/-- `sprEvalOne` 穿过 `if … then P else 0`。 -/
lemma sprEvalOne_ite (F : Type) [Field F] (r : ℕ) {p : Prop} [Decidable p]
    (P : S F r 9) :
    sprEvalOne F r (if p then P else 0) = if p then sprEvalOne F r P else 0 := by
  split_ifs <;> simp

/-- `sprEvalOne` 在 `∏_i x_{k,ii}` 上取值为 `1`。 -/
lemma sprEvalOne_prodX (F : Type) [Field F] (r : ℕ) (k : Fin r) :
    sprEvalOne F r (∏ i : Fin 9, MvPolynomial.X (k, i, i)) = 1 := by
  rw [map_prod]
  simp [sprEvalOne_X]

/-- `sprEvalOne` 在 `φ_{A₀}(x_{k,aa})` 上的值。 -/
lemma sprEvalOne_phiA_diag (F : Type) [Field F] (r : ℕ) (k : Fin r) (a : Fin 9) :
    sprEvalOne F r (phiA F r 9 (sprUnipotentUnit F) (MvPolynomial.X (k, a, a)))
      = 1 + (if a = 1 then 1 else 0) - (if a = 0 then 1 else 0) := by
  rw [phiA_sprUnipotentUnit_diag, map_sub, map_add, sprEvalOne_ite, sprEvalOne_ite,
    sprEvalOne_X, sprEvalOne_X]
  split_ifs <;> simp_all [sprEvalOne_X] <;> norm_num

/-- ★★★★★★★ **`φ_{A₀}` 不固定 `∏_i x_{k,ii}`**（单能单位的显式破坏）。

**证明**：`φ_{A₀}(∏ x_{ii}) = ∏ (x_{ii} + [i=1]x_{i0} − [i=0]x_{1i})`
（`map_prod` ＋ `phiA_sprUnipotentUnit_diag`），而 `sprEvalOne` 把它送到
`∏_i (1 + [i=1] − [i=0]) = 0`（`i = 0` 的因子为 `0`），把 `∏ x_{ii}` 送到 `1`。 -/
theorem prodX_ne_phiA_sprUnipotentUnit (F : Type) [Field F] (r : ℕ) (k : Fin r) :
    phiA F r 9 (sprUnipotentUnit F) (∏ i : Fin 9, MvPolynomial.X (k, i, i))
      ≠ ∏ i : Fin 9, MvPolynomial.X (k, i, i) := by
  intro h
  have h1 : sprEvalOne F r (phiA F r 9 (sprUnipotentUnit F)
      (∏ i : Fin 9, MvPolynomial.X (k, i, i)))
      = sprEvalOne F r (∏ i : Fin 9, MvPolynomial.X (k, i, i)) := by
    rw [h]
  rw [sprEvalOne_prodX] at h1
  have hL : sprEvalOne F r (phiA F r 9 (sprUnipotentUnit F)
      (∏ i : Fin 9, MvPolynomial.X (k, i, i))) = 0 := by
    rw [map_prod, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 9)) ?_
    rw [sprEvalOne_phiA_diag]
    simp
  rw [hL] at h1
  exact zero_ne_one h1

/-- `sprToS` 在对角不定元上的值：`sprToS (x_i) = x_{k₀,ii}`。 -/
lemma sprToS_X_inl (F : Type) [Field F] (r : ℕ) (k₀ : Fin r) (i : Fin 9) :
    sprToS F k₀ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (k₀, i, i) := by
  simp [sprToS]

/-- ★★★★★★★★★★ **`∏_i x_{k₀,ii} ∉ K' ∩ K^{PGL}`**（机检；R670 反例链的末环）。

**证明**：`sprPGLFixedField` 的成员刻画要求被**每个** `A ∈ GL_9(F)` 固定；取 `A₀ = 1 + E₀₁`，
再用 `sprToSField_algebraMap` ＋ `phiKEquiv_algebraMap` 把 `K'`-层的不动性降到 `S`-层，
由 `IsFractionRing.injective` 得 `φ_{A₀}(∏ x_{ii}) = ∏ x_{ii}`，与
`prodX_ne_phiA_sprUnipotentUnit` 矛盾。 -/
theorem sprProdX_not_mem_sprPGLFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) :
    algebraMap (Spr F r 9) (SprField F r 9) (∏ i : Fin 9, MvPolynomial.X (Sum.inl i))
      ∉ sprPGLFixedField F r k₀ hk₀ := by
  intro hx
  rw [mem_sprPGLFixedField_iff] at hx
  have hA := hx (sprUnipotentUnit F)
  have hy : sprToSField F r 9 k₀ hk₀
      (algebraMap (Spr F r 9) (SprField F r 9) (∏ i : Fin 9, MvPolynomial.X (Sum.inl i)))
      = algebraMap (S F r 9) (SField F r 9) (∏ i : Fin 9, MvPolynomial.X (k₀, i, i)) := by
    rw [sprToSField_algebraMap, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => sprToS_X_inl F r k₀ i
  rw [hy] at hA
  have hK : phiKAlgEquiv F r 9 (sprUnipotentUnit F)
      (algebraMap (S F r 9) (SField F r 9) (∏ i : Fin 9, MvPolynomial.X (k₀, i, i)))
      = algebraMap (S F r 9) (SField F r 9)
          (phiA F r 9 (sprUnipotentUnit F) (∏ i : Fin 9, MvPolynomial.X (k₀, i, i))) := by
    rw [show (phiKAlgEquiv F r 9 (sprUnipotentUnit F) : SField F r 9 → SField F r 9)
        = phiKEquiv F r 9 (sprUnipotentUnit F) from rfl]
    rw [phiKEquiv_algebraMap]
  rw [hK] at hA
  exact prodX_ne_phiA_sprUnipotentUnit F r k₀
    (IsFractionRing.injective (S F r 9) (SField F r 9) hA)

#print axioms sprProdX_not_mem_sprPGLFixedField

/-- ★★★★★★★★★ **`(a)` 在本库的 `comap` 形态下是假命题**：`K'^N ≰ sprPGLFixedField`。

（`not_a_of_prodX_not_mem` ＋ 上一条。R670 的反例 `∏_i x_{k₀,ii}` 到此**完全机检**。）

**⚠ 解释边界（第 693／694 轮）**：本条是**关于 `sprPGLFixedField`（一个 `comap` 形态）**的结论，
**不是**对 Saltman 相关陈述的证伪。§216 机检 `sprToSField` **不保中心元**，故这个 `comap`
**排除中心元**，与 Saltman 比较中的"`K' ∩ K^{PGL}`"**不是同一对象**
（详见 `sprPGLFixedField` 定义处的警告与前沿笔记 §36–§37）。 -/
theorem not_a_prodX (F : Type) [Field F] (r : ℕ) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ¬ (sprNFixedField F r 9 ≤ sprPGLFixedField F r k₀ hk₀) :=
  not_a_of_prodX_not_mem F r k₀ hk₀ (sprProdX_not_mem_sprPGLFixedField F r k₀ hk₀)

#print axioms not_a_prodX

/-- ★★★★★★★★★ **`(β1)` 在本库形态下是假命题**：`K'^N ≰ Frac(traceAlg)`。

（`not_beta1_of_not_a` ＋ `not_a_prodX`；依据是已机检的 `(β1) ⟹ (a)`。）

**⚠ 解释边界（同 `not_a_prodX`）**：由 `(β1) ⟹ (a)` 与 `not_a_prodX` 传递而来，
故其**解读**同样限于本库的 `comap` 形态；`Frac(traceAlg)` 这一支是 `S`-侧对象，本身忠实。 -/
theorem not_beta1_prodX (F : Type) [Field F] (r : ℕ) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ¬ (sprNFixedField F r 9 ≤ sprTraceFrac F r 9 k₀ hk₀) :=
  not_beta1_of_not_a F r k₀ hk₀ (not_a_prodX F r k₀ hk₀)

#print axioms not_beta1_prodX

end SprProdXPGL


/-! ## §198 ★★★★ **`hZ` ⟹ `C ≰ P`** —— §185 的结论方向**机检**（第 673 轮）

§185 曾用"`det(X₁) ∈ C(R)`"推 `C ≰ P`，而该前提**可疑**（v38 §5 的 `⚠⚠`）。
R672 把 `(a)` 机检为假后，`C ≤ P` 的方向**不必再靠 §185**：

* `hZ`（`N ≤ C`；＝ 已发表 `Saltman prop:14.19`（`raw/Saltman1999ch14.tex:368`）的 `Z` 半）
  与 `C ≤ P` 合并 ⟹ `N ≤ P`，而 `N ≤ P` 正是 `(a)`；
* `(a)` **假**（`not_a_prodX`，§197，机检）。

⟹ **`hZ` 之下 `C ≤ P` 与 `(a)` 等价**，故 `C ≤ P` **与 `(a)` 同假**：`C ≰ P` 由 `hZ` **机检地**迫出。

| 件 | 内容 |
|---|---|
| ★★★ `not_center_le_pgl_of_zHalf` | **`hZ ⟹ ¬(C ≤ P)`** |
| ★★ `center_le_pgl_iff_nFixed_le_pgl_of_zHalf` | **`hZ ⟹ (C ≤ P ↔ N ≤ P)`**（`⟸` 用 `C ≤ N`） |

**与 §197 的关系**：本节把 §185 的 `⚠⚠`（`C ≰ P` 论证级，前提可疑）**降级为不需要**——
只要接受已发表的 `prop:14.19`，`C ≰ P` 就是 `¬(a)` 的直接推论。

**射程（勿夸大）**：两件都以 `hZ` 为**前提**，`hZ` 本身**未证**（已发表、未机检）；
`C ≰ P` 的**无条件**机检**未做**（须先算出 `C` 的具体生成元 `s_c`）；**H2 见文件头「当前状态」。** -/

section SprCenterNotLePGL

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★ **`hZ` 迫使 `C ≰ P`**（否则 `hZ` ＋ `C ≤ P` 给出 `(a)`，与 `not_a_prodX` 矛盾）。 -/
theorem not_center_le_pgl_of_zHalf (F : Type) [Field F]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ¬ (sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀) := by
  intro hCP
  exact not_a_prodX F 2 k₀ hk₀ (le_trans hZ hCP)

#print axioms not_center_le_pgl_of_zHalf

/-- ★★ **`hZ` 之下 `C ≤ P` 与 `(a)` 等价**（`⟸` 用 `C ≤ N` 已机检；`⟹` 用 `hZ`）。 -/
theorem center_le_pgl_iff_nFixed_le_pgl_of_zHalf (F : Type) [Field F]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀
      ↔ sprNFixedField F 2 9 ≤ sprPGLFixedField F 2 k₀ hk₀ := by
  constructor
  · intro hCP
    exact le_trans hZ hCP
  · intro hNP
    exact le_trans (sprCenterImageField_le_sprNFixedField F D k₀ hk₀) hNP

#print axioms center_le_pgl_iff_nFixed_le_pgl_of_zHalf

/-- ★★★ 推论（`iff` 版）：`hZ` ⟹ `C ≰ P`。 -/
theorem not_center_le_pgl_of_zHalf' (F : Type) [Field F]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ¬ (sprCenterImageField F 2 9 D k₀ hk₀ ≤ sprPGLFixedField F 2 k₀ hk₀) := by
  intro hCP
  exact not_a_prodX F 2 k₀ hk₀ (le_trans hZ hCP)

#print axioms not_center_le_pgl_of_zHalf'

end SprCenterNotLePGL


/-! ## §199 ★★★★★★★★ **`UDKTensorHypK'` 的**正确形态**：`Ξ` 的 `Z`-张成 ⟹ 单射 ⟹ H2**（第 674 轮）

§100（第 482 轮）把 `UDKTensorHypK'` 判为"**很可能为假**（`dim_Z UDK' = ∞`）"，
并据此**改道**到 `sprCenterZMap` 满射。第 673 轮的**内容式侦察**（`raw/Formanek2002.tex:122/128/151`，
见 [[proj-abgv52-frontier-R661]] §16.3）判定该判读**不成立**：

* `UDK'` 是**通用矩阵代数**（＝自由代数对 T-理想 `T(n)` 的商）在 `ψ` 下的像，"词无限多"**不**推出
  "`Z`-维数无限"；
* Amitsur 1955：`dim_{C(Q(R))} Q(R) = n²`（Saltman `thm:14.5`）；
* n = 2、r = 2 的 **Sylvester 定理**（`raw/Formanek2002.tex:91`）显式给出 `K⟨X,Y⟩` 是**秩 4** 模。

⟹ `UDKTensorHypK'`（双射）应当**为真**；它的**可证形态**不是"维数 = n²"，而是下面这条
**经典模有限性**（Procesi／Sylvester 的基定理）：`Ξ`（`n²` 个元 `ψ(X_{k₁})^iψ(X_{k₂})^j`）
在 `↥Z` 上**张成** `UDK'`。

本节机检这条桥：**`Ξ` 的 `Z`-张成 ⟹ `udkTensorToMatrix` 单射**（满射已由 §98 无条件给出），
从而 `H2 ⟸（`Ξ` 的 `Z`-张成）＋（`Z` 半）`。

| 件 | 内容 |
|---|---|
| ★★★★★★ `XiZSpanHypK'` | **新具名输入（`⊗` 形态）**：每个 `UDK' ⊗_Z K'` 的元都是 `Σ_p Ξ_p ⊗ k_p` |
| ★★★★★★ `injective_udkTensorToMatrix_of_xiZSpan` | **`Ξ` 的 `Z`-张成 ⟹ 求值映射单射**（用 §97 的 `Ξ` 的 `K'`-线性无关） |
| ★★★★★★★★ `h2_of_xiZSpan_and_zHalf` | **H2 ⟸（`Ξ` 的 `Z`-张成）＋（`Z` 半）** |

**证明（单射）**：设 `f(x - y) = 0`；由 `hspan` 写 `x - y = Σ_p Ξ_p ⊗ k_p`；
`f(Ξ_p ⊗ k_p) = k_p • Ξ_p`（`udkTensorToMatrix_tmul` ＋ `mul_scalar_eq_smul`），
故 `Σ_p k_p • Ξ_p = 0`；`Ξ` 的 `K'`-线性无关（§97 `sprXi_linearIndependent`）给出所有 `k_p = 0`，
于是 `x - y = 0`。

**射程（勿夸大）**：`XiZSpanHypK'`（＝ 模有限性，已发表）与 `hZ`（＝ `prop:14.19` 的 `Z` 半，已发表）
**均未证**；**H2 仍不是无条件定理**。本节的增益：
① `UDKTensorHypK'` 从终点件中**消失**（替换为经典形态）；
② §100 的改道**依据**被勘误（`UDK'` 路线不必放弃）；
③ 单射半边**不再需要任何维数计数**。 -/

section SprXiZSpan

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] (r n : ℕ) [Nonempty (Fin n)] [NeZero n]

/-- ★★★★★★ **新具名输入（`⊗` 形态的 `Z`-张成）**：`UDK' ⊗_Z K'` 的每个元都可写成 `Σ_p Ξ_p ⊗ k_p`。

这是 `Ξ` 在 `↥Z` 上张成 `UDK'` 的 `⊗` 形式（经典模有限性：`R(F,n,r)` 在中心上是秩 `n²` 的模），
**替代** §41 的 `UDKTensorHypK'`（双射形态，被 §100 误判为假）。 -/
def XiZSpanHypK' (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k₁ k₂ : Fin r) : Prop :=
  ∀ x : TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀) ↥(UDK' F r n D k₀ hk₀)
      (SprField F r n),
    ∃ k : Fin n × Fin n → SprField F r n,
      x = ∑ p : Fin n × Fin n,
        (⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
          xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
        ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p

#print axioms XiZSpanHypK'

/-- ★★★★★★ **`Ξ` 的 `Z`-张成 ⟹ 求值映射单射**（用 §97 的 `sprXi_linearIndependent`）。 -/
theorem injective_udkTensorToMatrix_of_xiZSpan
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k₁ k₂ : Fin r} (hspan : XiZSpanHypK' F r n D k₀ hk₀ k₁ k₂)
    (hLI : LinearIndependent (SprField F r n)
      (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2)) :
    Function.Injective (udkTensorToMatrix F r n D k₀ hk₀) := by
  have hterm : ∀ (k : Fin n × Fin n → SprField F r n) (p : Fin n × Fin n),
      udkTensorToMatrix F r n D k₀ hk₀
        ((⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
          xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p)
        = k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 := by
    intro k p
    rw [udkTensorToMatrix_tmul, mul_scalar_eq_smul]
  intro x y hxy
  have hzero : udkTensorToMatrix F r n D k₀ hk₀ (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨k, hk⟩ := hspan (x - y)
  have hx0 : (∑ p : Fin n × Fin n,
      udkTensorToMatrix F r n D k₀ hk₀
        ((⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
          xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p)) = 0 := by
    rw [← hzero, hk, map_sum]
  have hcongr : (∑ p : Fin n × Fin n,
      udkTensorToMatrix F r n D k₀ hk₀
        ((⟨xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2,
          xiSprK_mem_UDK' F r n D k₀ hk₀ k₁ k₂ p.1 p.2⟩ : ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] k p))
      = ∑ p : Fin n × Fin n, k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2 :=
    Finset.sum_congr rfl fun p _ => hterm k p
  have hsum : (∑ p : Fin n × Fin n, k p • xiSprK F r n k₀ hk₀ k₁ k₂ p.1 p.2) = 0 := by
    rw [← hcongr]
    exact hx0
  have hk0 := (Fintype.linearIndependent_iff.mp hLI) k hsum
  have hsub : x - y = 0 := by
    rw [hk]
    simp [hk0]
  exact sub_eq_zero.mp hsub

#print axioms injective_udkTensorToMatrix_of_xiZSpan

end SprXiZSpan

section SprXiZSpanEndgame

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

variable (F : Type) [Field F] [CharZero F]

/-- ★★★★★★★★ **H2 ⟸（`Ξ` 的 `Z`-张成）＋（`Z` 半）**。

接 §99 的 `h2_of_injective_and_zHalf`：单射由 §199 的
`injective_udkTensorToMatrix_of_xiZSpan` ＋ §97 的 `sprXi_linearIndependent` 供给。 -/
theorem h2_of_xiZSpan_and_zHalf (D : GenericDivisionData F 2 9)
    {k₀ : Fin 2} (hk₀ : k₀.val = 0) {k : Fin 2} (hk : k ≠ k₀)
    (hspan : XiZSpanHypK' F 2 9 D k₀ hk₀ k₀ k)
    (hZ : ∀ x : SprField F 2 9, sprFieldNFixed F 2 9 x →
      x ∈ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_injective_and_zHalf F D hk₀ hk
    (injective_udkTensorToMatrix_of_xiZSpan F 2 9 D k₀ hk₀ hspan
      (sprXi_linearIndependent F 2 9 k₀ hk₀ hk)) hZ

#print axioms h2_of_xiZSpan_and_zHalf

end SprXiZSpanEndgame


/-! ## §200 ★★★★★ **`hZ` 的幂和族可证伪点** —— `∑_i x_{k₀,ii}^k ∈ C`（第 675 轮）

§196 给了一条 `hZ` 的可证伪点（对角元**积** `∏_i x_{k₀,ii}`）。本节补上**幂和族**：
对每个 `k : ℕ`，`∑_i x_{k₀,ii}^k` 也在 `K'^N` 里，故 `hZ` 迫使它落进 `C`。

**为何有用**：由 **Newton 恒等式**，初等对称函数 `e_j(x_1,…,x_n)`（`j ≤ n`）是幂和
`p_1,…,p_j` 的有理系数多项式；故 `hZ` 迫使**对角元的一整个对称函数域**落进 `C`——
这是 `C` 的**判定测试集**：任何一条幂和若被证 `∉ C`，则 **`hZ` 为假**（反例生成器）。

| 件 | 内容 |
|---|---|
| ★★★★ `sprPowSum_torus` | `∑_i x_i^k` 被环面 `T` 固定 |
| ★★★★ `sprPowSum_perm` | `∑_i x_i^k` 被 `S_n` 固定（`Equiv.sum_comp`） |
| ★★★★ `sprPowSum_mem_sprNFixed` | `∑_i x_i^k ∈ S'^N`（多项式层） |
| ★★★★★ `sprPowSum_mem_sprNFixedField` | 其像 `∈ K'^N` |
| ★★★★★★ `sprPowSum_mem_sprCenterImageField_of_zHalf` | **`hZ ⟹ ∑_i x_{k₀,ii}^k ∈ C`**（任意 `k`） |
| ★★★★★ `not_zHalf_of_powSum_not_mem` | **反例通道**：某条幂和 `∉ C` ⟹ `¬hZ` |

**射程（勿夸大）**：这些是 `hZ` 的**推论**，不是 `hZ` 的证明；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprPowSum

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- `∑_i x_i^k` 在 `S'` 层被 `T` 固定。 -/
theorem sprPowSum_torus (F : Type) [Field F] (r n : ℕ) (k : ℕ) (b : Fin n → Fˣ) :
    (sprDiagHom F r n b) (∑ i : Fin n, (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k)
      = ∑ i : Fin n, (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_pow, sprDiagHom_X_inl]

#print axioms sprPowSum_torus

/-- `∑_i x_i^k` 在 `S'` 层被 `S_n` 固定。 -/
theorem sprPowSum_perm (F : Type) [Field F] (r n : ℕ) (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    (sprPermAlgEquiv F r n σ) (∑ i : Fin n, (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k)
      = ∑ i : Fin n, (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k := by
  rw [map_sum]
  simp only [map_pow, sprPermAlgEquiv_X_inl]
  exact Equiv.sum_comp σ (fun i => (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k)

#print axioms sprPowSum_perm

/-- `∑_i x_i^k ∈ S'^N`（多项式层）。 -/
theorem sprPowSum_mem_sprNFixed (F : Type) [Field F] (r n : ℕ) (k : ℕ) :
    sprNFixed F r n (∑ i : Fin n, (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k) :=
  ⟨fun b => sprPowSum_torus F r n k b, fun σ => sprPowSum_perm F r n k σ⟩

#print axioms sprPowSum_mem_sprNFixed

/-- 幂和的像 `∈ K'^N`。 -/
theorem sprPowSum_mem_sprNFixedField (F : Type) [Field F] (r n : ℕ) (k : ℕ) :
    algebraMap (Spr F r n) (SprField F r n)
        (∑ i : Fin n, (MvPolynomial.X (Sum.inl i) : Spr F r n) ^ k)
      ∈ sprNFixedField F r n := by
  rw [mem_sprNFixedField_iff]
  exact ⟨sprFieldTFixed_algebraMap F r n (sprPowSum_mem_sprNFixed F r n k).1,
    sprFieldSFixed_algebraMap F r n (sprPowSum_mem_sprNFixed F r n k).2⟩

#print axioms sprPowSum_mem_sprNFixedField

/-- ★★ **`hZ` ⟹ 幂和 `∑_i x_{k₀,ii}^k ∈ C`**（任意 `k`；`k = 1` 即迹，`k = n` 由 Newton 给出 `∏x_i`）。 -/
theorem sprPowSum_mem_sprCenterImageField_of_zHalf (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) (k : ℕ) :
    algebraMap (Spr F 2 9) (SprField F 2 9)
        (∑ i : Fin 9, (MvPolynomial.X (Sum.inl i) : Spr F 2 9) ^ k)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  hZ (sprPowSum_mem_sprNFixedField F 2 9 k)

#print axioms sprPowSum_mem_sprCenterImageField_of_zHalf

/-- ★★★★★ **反例通道**：若某条幂和 `∉ C`，则 `¬hZ`（可证伪性）。 -/
theorem not_zHalf_of_powSum_not_mem (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) (k : ℕ)
    (h : algebraMap (Spr F 2 9) (SprField F 2 9)
        (∑ i : Fin 9, (MvPolynomial.X (Sum.inl i) : Spr F 2 9) ^ k)
        ∉ sprCenterImageField F 2 9 D k₀ hk₀) :
    ¬ (sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :=
  fun hZ => h (sprPowSum_mem_sprCenterImageField_of_zHalf F D k₀ hk₀ hZ k)

#print axioms not_zHalf_of_powSum_not_mem

end SprPowSum


/-! ## §201 ★★★★★ **`hZ` 的初等对称函数族** —— `e_j(x_{k₀,11},…,x_{k₀,99}) ∈ C`（第 676 轮）

R675 给的是**幂和** `p_k = ∑_i x_i^k`。本节补**初等对称函数**

```
e_j := ∑_{s ⊆ {1,…,n}, |s| = j} ∏_{i ∈ s} x_i
```

机检 `e_j ∈ K'^N`（故 `hZ ⟹ e_j ∈ C`），并且给**反例通道**。

**为何需要它（与 §199／§200 的三点互锁）**：
1. **Newton 恒等式**把 `e_j` 写成 `p_1,…,p_j` 的有理系数多项式——本节给的是**独立**的机检
   （不依赖 Newton 的形式化），故 `C` 的已知成员族又多一支；
2. **Cayley–Hamilton 归约**（`XiZSpanHypK'` 的关键）需要 `e_j(X) ∈ Z`：
   `X^n = Σ_{j=1}^{n} (-1)^{j-1} e_j(X)·X^{n-j}`。故本节正是 §199 那条输入**缺失的系数块**；
3. **反例通道**：任何 `e_j ∉ C` 即证伪 `hZ`（与 §200 的幂和通道并列）。

| 件 | 内容 |
|---|---|
| ★★★★ `sprElemSymm` | `e_j` 的定义（`Finset.powersetCard` 上的和） |
| ★★★★ `sprDiagHom_elemSymm` | `e_j` 被 `T` 固定 |
| ★★★★★★ `sprPermAlgEquiv_elemSymm` | `e_j` 被 `S_n` 固定（`Finset.sum_bij`，像集 `s.image σ`） |
| ★★★★ `sprElemSymm_mem_sprNFixed` | `e_j ∈ S'^N` |
| ★★★★★ `sprElemSymm_mem_sprNFixedField` | 其像 `∈ K'^N` |
| ★★★★★★ `sprElemSymm_mem_sprCenterImageField_of_zHalf` | **`hZ ⟹ e_j ∈ C`**（任意 `j`） |
| ★★★★★ `not_zHalf_of_elemSymm_not_mem` | **反例通道**：某 `e_j ∉ C` ⟹ `¬hZ` |

**射程（勿夸大）**：这些都是 `hZ` 的**推论**；`hZ` **未证**；`XiZSpanHypK'` **未证**；
Cayley–Hamilton 归约本身**未做**；**H2 见文件头「当前状态」。** -/

section SprElemSymm

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52


noncomputable def sprElemSymm (F : Type) [Field F] (r n : ℕ) (j : ℕ) : Spr F r n :=
  ∑ s ∈ Finset.univ.powersetCard j, ∏ i ∈ s, (MvPolynomial.X (Sum.inl i) : Spr F r n)

lemma sprDiagHom_elemSymm (F : Type) [Field F] (r n j : ℕ) (b : Fin n → Fˣ) :
    sprDiagHom F r n b (sprElemSymm F r n j) = sprElemSymm F r n j := by
  rw [sprElemSymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => sprDiagHom_X_inl F r n b i

lemma sprPermAlgEquiv_elemSymm (F : Type) [Field F] (r n j : ℕ) (σ : Equiv.Perm (Fin n)) :
    sprPermAlgEquiv F r n σ (sprElemSymm F r n j) = sprElemSymm F r n j := by
  rw [sprElemSymm, map_sum]
  have hterm : ∀ s ∈ Finset.univ.powersetCard j,
      (sprPermAlgEquiv F r n σ) (∏ i ∈ s, (MvPolynomial.X (Sum.inl i) : Spr F r n))
        = ∏ i ∈ s, (MvPolynomial.X (Sum.inl (σ i)) : Spr F r n) := by
    intro s _
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => sprPermAlgEquiv_X_inl F r n σ i
  refine Finset.sum_bij (fun s _ => s.image (⇑σ)) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_powersetCard] at hs ⊢
    refine ⟨by simp, ?_⟩
    rw [Finset.card_image_of_injective s (fun a c h => σ.injective h)]
    exact hs.2
  · intro s hs t ht hst
    ext x
    constructor
    · intro hx
      have h1 : σ x ∈ t.image (⇑σ) := by
        rw [← hst]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h1
      have : y = x := σ.injective hyx
      rwa [this] at hy
    · intro hx
      have h1 : σ x ∈ s.image (⇑σ) := by
        rw [hst]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h1
      have : y = x := σ.injective hyx
      rwa [this] at hy
  · intro t ht
    refine ⟨t.image (⇑σ.symm), ?_, ?_⟩
    · simp only [Finset.mem_powersetCard] at ht ⊢
      refine ⟨by simp, ?_⟩
      rw [Finset.card_image_of_injective t (fun a c h => σ.symm.injective h)]
      exact ht.2
    · rw [Finset.image_image]
      simp
  · intro s hs
    rw [hterm s hs, Finset.prod_image]
    intro a _ c _ h
    exact σ.injective h

lemma sprElemSymm_mem_sprNFixed (F : Type) [Field F] (r n j : ℕ) :
    sprNFixed F r n (sprElemSymm F r n j) :=
  ⟨fun b => sprDiagHom_elemSymm F r n j b, fun σ => sprPermAlgEquiv_elemSymm F r n j σ⟩

lemma sprElemSymm_mem_sprNFixedField (F : Type) [Field F] (r n j : ℕ) :
    algebraMap (Spr F r n) (SprField F r n) (sprElemSymm F r n j) ∈ sprNFixedField F r n := by
  rw [mem_sprNFixedField_iff]
  exact ⟨sprFieldTFixed_algebraMap F r n (sprElemSymm_mem_sprNFixed F r n j).1,
    sprFieldSFixed_algebraMap F r n (sprElemSymm_mem_sprNFixed F r n j).2⟩

theorem sprElemSymm_mem_sprCenterImageField_of_zHalf (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) (j : ℕ) :
    algebraMap (Spr F 2 9) (SprField F 2 9) (sprElemSymm F 2 9 j)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  hZ (sprElemSymm_mem_sprNFixedField F 2 9 j)

theorem not_zHalf_of_elemSymm_not_mem (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) (j : ℕ)
    (h : algebraMap (Spr F 2 9) (SprField F 2 9) (sprElemSymm F 2 9 j)
        ∉ sprCenterImageField F 2 9 D k₀ hk₀) :
    ¬ (sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :=
  fun hZ => h (sprElemSymm_mem_sprCenterImageField_of_zHalf F D k₀ hk₀ hZ j)

#print axioms sprElemSymm_mem_sprNFixedField
#print axioms sprElemSymm_mem_sprCenterImageField_of_zHalf

end SprElemSymm


/-! ## §202 ★★★ **对角矩阵的特征多项式**：Vieta／Cayley–Hamilton 路的起点（第 677 轮）

`XiZSpanHypK'`（§199）的 X-方向归约要用 Cayley–Hamilton：`X` 满足**首一 n 次**关系，
其系数是 `x_{k₀,ii}` 的**初等对称函数** `e_j`（§201 已机检 `hZ ⟹ e_j ∈ C`）。本节把该关系的
**多项式半边**机检：

```
charpoly (sprXdiagK) = ∏_{i} (T − x_{k₀,ii})        （sprXdiagK ＝ diagonal (sprDiagVal ·)）
```

| 件 | 内容 |
|---|---|
| ★★★ `sprXdiagK_charpoly` | `charpoly = ∏_i (T − x_i)`（`Matrix.charpoly_diagonal`） |
| ★★ `sprXdiagK_charpoly_monic` | 首一 |
| ★★ `sprXdiagK_charpoly_natDegree` | 次数 `= n` |
| ★★★ `sprXdiagK_charpoly_coeff_zero` | 常数项 `= (-1)^n ∏_i x_i`（`det`，与 §196 的 `∏x_i` 同源） |

**⟹ 由此可走的路线（下一步，未做）**：把 `charpoly` 的**一般系数**与 `sprElemSymm` 对齐（Vieta：
`coeff (n-j) = (-1)^j e_j`），再用 `Matrix.aeval_self_charpoly`
（`(Polynomial.aeval X) X.charpoly = 0`）把它压到矩阵层，得

```
hZ  ⟹  (X)^n ∈ Submodule.span ↥C {1, X, …, X^{n-1}}      （X-方向的归约）
```

**射程（勿夸大）**：本节**只**做多项式半边。**Vieta 的一般系数对齐未做**；Cayley–Hamilton 压到
矩阵层**未做**；`XiZSpanHypK'` **未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprXdiagCharpoly

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52


/-- ★★★ 对角矩阵 `sprXdiagK` 的特征多项式：`∏_i (T − x_i)`（Vieta 的出发点）。 -/
theorem sprXdiagK_charpoly (F : Type) [Field F] (r n : ℕ) :
    (sprXdiagK F r n).charpoly
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C (sprDiagVal F r n i)) := by
  rw [sprXdiagK, Matrix.charpoly_diagonal]

/-- 该特征多项式是**首一**的。 -/
theorem sprXdiagK_charpoly_monic (F : Type) [Field F] (r n : ℕ) :
    (sprXdiagK F r n).charpoly.Monic := by
  rw [sprXdiagK_charpoly]
  exact Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)

/-- 该特征多项式的**次数**是 `n`。 -/
theorem sprXdiagK_charpoly_natDegree (F : Type) [Field F] (r n : ℕ) :
    (sprXdiagK F r n).charpoly.natDegree = n := by
  rw [sprXdiagK_charpoly]
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
  simp [Polynomial.natDegree_X_sub_C]

/-- ★ Cayley–Hamilton（对角矩阵形态）：`aeval X (charpoly X) = 0`。 -/
theorem sprXdiagK_aeval_charpoly (F : Type) [Field F] (r n : ℕ) :
    (Polynomial.aeval (sprXdiagK F r n)) (sprXdiagK F r n).charpoly = 0 :=
  Matrix.aeval_self_charpoly _

/-- ★ 常数项＝`det`：`charpoly` 的常数项是 `(-1)^n ∏_i x_i`。 -/
theorem sprXdiagK_charpoly_coeff_zero (F : Type) [Field F] (r n : ℕ) :
    (sprXdiagK F r n).charpoly.coeff 0
      = (-1) ^ n * ∏ i : Fin n, sprDiagVal F r n i := by
  rw [sprXdiagK_charpoly, Polynomial.coeff_zero_eq_eval_zero]
  rw [show (Polynomial.eval (0 : SprField F r n))
      = ⇑(Polynomial.evalRingHom (0 : SprField F r n)) from rfl, map_prod]
  rw [Finset.prod_congr rfl (g := fun i : Fin n => -sprDiagVal F r n i) ?_]
  · rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  · intro i _
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

#print axioms sprXdiagK_charpoly
#print axioms sprXdiagK_charpoly_monic
#print axioms sprXdiagK_charpoly_natDegree
#print axioms sprXdiagK_charpoly_coeff_zero

end SprXdiagCharpoly


/-! ## §203 ★★★★ **Vieta 的补集桥 ＋ `charpoly` 系数块**（第 678 轮）

Cayley–Hamilton 归约（§199 的 X-方向）需要两件东西：
① `charpoly (sprXdiagK)` 的系数 ＝ 初等对称函数（**Vieta**）；
② `hZ` 迫使这些系数落在 `C`（§201 已给 `e_j ∈ C`）。

本节机检 **①的两件工具之一**（补集求和桥）与 **②的装配**，并把 **① 本身**登记为具名输入。

| 件 | 内容 |
|---|---|
| ★★★★ `sum_powersetCard_compl` | **补集桥**：`∑_{|t| = k} ∏_{i∉t} g i = ∑_{|s| = n−k} ∏_{i∈s} g i` |
| ★★★★ `DiagVietaHypK'` | **具名输入（Vieta，多项式层）**：`coeff (n−j) = (−1)^j e_j` |
| ★★★★★★★ `charpoly_coeff_mem_sprCenterImageField_of_zHalf` | **`hZ` ＋ Vieta ⟹ `charpoly` 的每个系数 ∈ `C`** |

**为何补集桥是 Vieta 的关键**：`Finset.prod_add` 的展开把常数项部分放在**补集** `univ \ t` 上，
故 `coeff (n−j)` 的求和天然跑遍 `powersetCard (n−j)` 的**补集**；补集桥把它换回 `powersetCard j`，
于是系数正好是 `(−1)^j · sprElemSymm j`。

**射程（勿夸大）**：`DiagVietaHypK'` **未证**（其证明只剩"展开 ＋ 按基数重排"这一步，
工具已备好：`Finset.prod_add`／`Finset.sum_powerset`／本节的补集桥）；`hZ` **未证**；
`XiZSpanHypK'` **未证**；Cayley–Hamilton 压到矩阵层**未做**；**H2 见文件头「当前状态」。** -/

section SprVieta

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52


/-- 补集求和桥：`∑_{|t| = k} ∏_{i ∉ t} g i = ∑_{|s| = n - k} ∏_{i ∈ s} g i`。 -/
theorem sum_powersetCard_compl {K : Type} [Field K] (n k : ℕ) (hk : k ≤ n) (g : Fin n → K) :
    (∑ t ∈ Finset.univ.powersetCard k, ∏ i ∈ Finset.univ \ t, g i)
      = ∑ s ∈ Finset.univ.powersetCard (n - k), ∏ i ∈ s, g i := by
  refine Finset.sum_bij (fun t _ => Finset.univ \ t) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_powersetCard] at ht ⊢
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, ht.2]
  · intro t _ s _ h
    have h' : Finset.univ \ t = Finset.univ \ s := h
    rw [← Finset.sdiff_sdiff_eq_self (Finset.subset_univ t),
      ← Finset.sdiff_sdiff_eq_self (Finset.subset_univ s), h']
  · intro s hs
    refine ⟨Finset.univ \ s, ?_, ?_⟩
    · simp only [Finset.mem_powersetCard] at hs ⊢
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, hs.2]
      exact Nat.sub_sub_self hk
    · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ s)]
  · intro t _
    rfl

#print axioms sum_powersetCard_compl

/-- **具名输入（Vieta，多项式层）**：`charpoly (sprXdiagK)` 的系数是初等对称函数。 -/
def DiagVietaHypK' (F : Type) [Field F] (r n : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ n →
    (sprXdiagK F r n).charpoly.coeff (n - j)
      = (-1) ^ j * algebraMap (Spr F r n) (SprField F r n) (sprElemSymm F r n j)

#print axioms DiagVietaHypK'

/-- ★ `hZ` ＋ Vieta ⟹ `charpoly (sprXdiagK)` 的每个系数都落在 `C` 里（CH 归约的系数块）。 -/
theorem charpoly_coeff_mem_sprCenterImageField_of_zHalf (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hV : DiagVietaHypK' F 2 9)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) (j : ℕ) (hj : j ≤ 9) :
    (sprXdiagK F 2 9).charpoly.coeff (9 - j)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
  rw [hV j hj]
  have h1 : algebraMap (Spr F 2 9) (SprField F 2 9) (sprElemSymm F 2 9 j)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
    hZ (sprElemSymm_mem_sprNFixedField F 2 9 j)
  have h2 : ((-1 : SprField F 2 9)) ^ j ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
    pow_mem (neg_mem (one_mem _)) j
  exact mul_mem h2 h1

#print axioms charpoly_coeff_mem_sprCenterImageField_of_zHalf

end SprVieta


/-! ## §204 ★★★★★★★★★ **Vieta 成定理** —— `charpoly (sprXdiagK)` 的系数 ＝ 初等对称函数（第 679 轮）

§203 把 Vieta 登记为具名输入 `DiagVietaHypK'`，并备好补集桥。本轮把它**证掉**：

```
charpoly (sprXdiagK) = ∏_i (T − x_i)
  = ∑_{t ⊆ univ} C((−1)^{|t|} ∏_{i∈t} x_i) · T^{n−|t|}          （子集展开，本轮机检）
⟹ coeff (n−j) = (−1)^j · e_j                                    （按基数筛，本轮机检）
```

**关键工艺（两个避免硬碰的技巧）**：
1. 把因子写成 **`(−C x_i) + X`**（常数项在前）再 `Finset.prod_add` —— 这样常数项恰好落在
   **`t` 上**（而不是补集），系数筛选直接给出 `|t| = j`，**绕开了补集重排**；
2. 符号用 `Finset.prod_congr` 把 `−C x_i` 换成 `C (−x_i)` 后在**域**里用 `Finset.prod_neg`，
   再 `← map_prod` 收回 `C`，最后 `← map_pow`／`← map_mul` 合并（`C` 是环同态）。

| 件 | 内容 |
|---|---|
| ★★★★★ `charpoly_eq_subset_sum` | 子集展开 |
| ★★★★★★★★ `diagVietaHypK'` | **`DiagVietaHypK'` 成定理**（§203 的具名输入消去） |
| ★★★★★ `charpoly_coeff_mem_sprCenterImageField_of_zHalf'` | **`hZ` ⟹ `charpoly` 每个系数 ∈ `C`**（不再需要 Vieta 前提） |

**射程（勿夸大）**：CH 压到矩阵层**未做**；`XiZSpanHypK'` **未证**；`hZ` **未证**；
**H2 见文件头「当前状态」。** -/

section SprVietaTheorem

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★ **子集展开**：`∏_i (T − x_i) = Σ_{t ⊆ univ} C((−1)^{|t|} ∏_{i∈t} x_i) · T^{n−|t|}`。 -/
theorem charpoly_eq_subset_sum (F : Type) [Field F] (r n : ℕ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (sprDiagVal F r n i)))
      = ∑ t ∈ Finset.univ.powerset,
          Polynomial.C ((-1 : SprField F r n) ^ t.card * ∏ i ∈ t, sprDiagVal F r n i)
            * Polynomial.X ^ (n - t.card) := by
  have hfac : ∀ i : Fin n, (Polynomial.X - Polynomial.C (sprDiagVal F r n i))
      = (-Polynomial.C (sprDiagVal F r n i)) + Polynomial.X := by
    intro i
    rw [sub_eq_add_neg, add_comm]
  simp only [hfac]
  rw [Finset.prod_add]
  have hsign : ∀ t : Finset (Fin n), (∏ i ∈ t, -Polynomial.C (sprDiagVal F r n i))
      = Polynomial.C ((-1 : SprField F r n) ^ t.card * ∏ i ∈ t, sprDiagVal F r n i) := by
    intro t
    rw [show (∏ i ∈ t, -Polynomial.C (sprDiagVal F r n i))
        = (∏ i ∈ t, Polynomial.C (-(sprDiagVal F r n i))) from by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp]
    rw [← map_prod, Finset.prod_neg]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hsign, Finset.prod_const, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
    Finset.inter_univ]

#print axioms charpoly_eq_subset_sum

/-- ★★★★★ **Vieta**：`charpoly (sprXdiagK)` 的系数是初等对称函数（`DiagVietaHypK'` 成定理）。 -/
theorem diagVietaHypK' (F : Type) [Field F] (r n : ℕ) : DiagVietaHypK' F r n := by
  intro j hj
  rw [sprXdiagK_charpoly, charpoly_eq_subset_sum]
  have hcoeff : ∀ t : Finset (Fin n),
      (Polynomial.C ((-1 : SprField F r n) ^ t.card * ∏ i ∈ t, sprDiagVal F r n i)
          * Polynomial.X ^ (n - t.card)).coeff (n - j)
        = if t.card = j then (-1 : SprField F r n) ^ t.card
            * ∏ i ∈ t, sprDiagVal F r n i else 0 := by
    intro t
    have hle : t.card ≤ n := by
      have := Finset.card_le_univ t
      simpa using this
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hiff : ((n - j) = (n - t.card)) ↔ (t.card = j) := by omega
    by_cases h : t.card = j
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h, mul_zero]
  have hsum_coeff : ∀ (f : Finset (Fin n) → Polynomial (SprField F r n)) (m : ℕ),
      (∑ t ∈ Finset.univ.powerset, f t).coeff m
        = ∑ t ∈ Finset.univ.powerset, (f t).coeff m := by
    intro f m
    induction (Finset.univ.powerset : Finset (Finset (Fin n))) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]
  rw [hsum_coeff]
  simp only [hcoeff]
  rw [← Finset.sum_filter]
  have hstep : ∀ t ∈ Finset.univ.powerset.filter (fun t : Finset (Fin n) => t.card = j),
      (-1 : SprField F r n) ^ t.card * ∏ i ∈ t, sprDiagVal F r n i
        = (-1 : SprField F r n) ^ j * ∏ i ∈ t, sprDiagVal F r n i := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [ht.2]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hfs : Finset.univ.powerset.filter (fun t : Finset (Fin n) => t.card = j)
      = Finset.univ.powersetCard j := by
    ext t
    simp [Finset.mem_powersetCard, Finset.mem_filter]
  rw [hfs]
  congr 1
  rw [sprElemSymm, map_sum]
  exact Finset.sum_congr rfl fun t _ => by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => rfl


/-- ★★★ **Vieta 现在无条件生效**：`charpoly (sprXdiagK)` 的每个系数都在 `C` 里（只以 `hZ` 为前提）。 -/
theorem charpoly_coeff_mem_sprCenterImageField_of_zHalf' (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) (j : ℕ) (hj : j ≤ 9) :
    (sprXdiagK F 2 9).charpoly.coeff (9 - j)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
  charpoly_coeff_mem_sprCenterImageField_of_zHalf F D k₀ hk₀ (diagVietaHypK' F 2 9) hZ j hj

#print axioms charpoly_coeff_mem_sprCenterImageField_of_zHalf'

end SprVietaTheorem


/-! ## §205 ★★★★★★★★ **X-方向归约闭环** —— Cayley–Hamilton ＋ Vieta：`X^9` 是 `1,…,X^8` 的 `C`-组合（第 680 轮）

§202 给了 `charpoly (sprXdiagK) = ∏_i (T − x_i)`（首一、次数 9），§204 给了**系数 ＝ 初等对称函数**，
§201／§204 给了 **`hZ` ⟹ 每个系数 ∈ `C`**。本轮把 Cayley–Hamilton 压到矩阵层：

```
(aeval X) X.charpoly = 0
  ⟹ ∑_{i<9} (coeff i) • X^i + (coeff 9) • X^9 = 0        （aeval_eq_sum_range ＋ sum_range_succ）
  ⟹ X^9 + ∑_{i<9} c_i • X^i = 0,  c_i = coeff i ∈ C      （首一 ⟹ coeff 9 = 1，§204 ⟹ c_i ∈ C）
```

**⟹ 含义**：`X` 的 9 次幂被 `1,…,X^8` 的 `C`-线性组合**消去**。这是 `Ξ = {X^i Y^j}` 在 `↥Z` 上
张成 `UDK'` 的**X-方向半边**（`Y`-方向同款，下一步）。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `xdiagK_pow_add_sum_eq_zero_of_zHalf` | **`hZ ⟹ ∃ c ∈ C^9, X^9 + ∑_{i<9} c_i•X^i = 0`** |

**工艺（R680）**：`Fin`-索引的算术**不要**用 `omega`——本轮两次 `omega` 触发
`maximum recursion depth`（假象：真实原因是**索引算式不匹配**，`coeff (9-(9-i))` vs `coeff i`）；
正解是 `i.isLt.le` ＋ `Nat.sub_sub_self` 显式改写。

**射程（勿夸大）**：只做 **X-方向**；`Y`-方向与双向混合**未做**；`XiZSpanHypK'` **未证**；
`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprXdiagReduction

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★★ **X-方向归约**（Cayley–Hamilton ＋ Vieta）：`X^9 + ∑_{i<9} c_i·X^i = 0`，其中 `c_i ∈ C`。

等价地 `X^9 = −∑_{i<9} c_i·X^i`：`X` 的 9 次幂被 `1,…,X^8` 的 `C`-线性组合消去。 -/
theorem xdiagK_pow_add_sum_eq_zero_of_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ∃ c : Fin 9 → SprField F 2 9,
      (∀ i, c i ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (sprXdiagK F 2 9) ^ 9
        + ∑ i : Fin 9, c i • (sprXdiagK F 2 9) ^ (i : ℕ) = 0 := by
  have hCH := Matrix.aeval_self_charpoly (sprXdiagK F 2 9)
  rw [Polynomial.aeval_eq_sum_range, sprXdiagK_charpoly_natDegree] at hCH
  rw [Finset.sum_range_succ] at hCH
  have hcoeff9 : (sprXdiagK F 2 9).charpoly.coeff 9 = 1 := by
    simpa [sprXdiagK_charpoly_natDegree] using (sprXdiagK_charpoly_monic F 2 9).coeff_natDegree
  rw [hcoeff9, one_smul] at hCH
  refine ⟨fun i => (sprXdiagK F 2 9).charpoly.coeff (i : ℕ), ?_, ?_⟩
  · intro i
    have hile : (i : ℕ) ≤ 9 := i.isLt.le
    have h2 := charpoly_coeff_mem_sprCenterImageField_of_zHalf' F D k₀ hk₀ hZ
      (9 - (i : ℕ)) (Nat.sub_le 9 (i : ℕ))
    rwa [Nat.sub_sub_self hile] at h2
  · rw [Fin.sum_univ_eq_sum_range
      (fun i => (sprXdiagK F 2 9).charpoly.coeff i • (sprXdiagK F 2 9) ^ i), add_comm]
    exact hCH

#print axioms xdiagK_pow_add_sum_eq_zero_of_zHalf

end SprXdiagReduction


/-! ## §206 ★★★★★ **`Y`-方向的第一步**：`charpoly (ymat)` 在环面作用下不变（第 681 轮）

§205 做完了 `X`-方向的归约。`Y`-方向要同样的一步：**`charpoly (ymat)` 的系数落在 `N` 里**，
从而 `hZ` 使其落进 `C`。本节做**环面 `T` 半边**：

```
(ymat).map (sprDiagHom b) = D · ymat · D⁻¹        （D ＝ diagonal (C ∘ b)：对角共轭）
⟹ charpoly 不变                                    （charpoly_mul_comm ＋ D⁻¹D = 1）
```

| 件 | 内容 |
|---|---|
| ★★★★★ `ymat_map_sprDiagHom` | **`ymat` 沿 `sprDiagHom b` 的像 ＝ 对角共轭 `D·Y·D⁻¹`** |
| ★★★★★★ `charpoly_ymat_sprDiagHom` | **`charpoly` 在环面作用下不变** |

**工艺（R681）**：`rw` 的**次序**是先 `Matrix.mul_diagonal` 再 `Matrix.diagonal_mul`
（外层的形状决定先匹配哪条）；`ymat_apply` 必须**先于** `sprDiagHom_X_inr` 重写；
单位逆的强制转换用 `Units.val_inv_eq_inv_val` 归一后 `ring` 才能收口。
**⚠ 注意**：`MvPolynomial` 在本 pin **没有 `Inv` 实例**，故逆元只能写成 `C ((b j : F)⁻¹)` 的形状。

**射程（勿夸大）**：只有 **`T` 半边**；`S_n` 半边（置换共轭）**未做**；`Y`-方向的 CH 归约**未做**；
`XiZSpanHypK'` **未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprYmatCharpoly

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★ **环面作用下的对角化**：`ymat` 沿 `sprDiagHom b` 的像 ＝ 对角矩阵的共轭 `D·Y·D⁻¹`。 -/
theorem ymat_map_sprDiagHom (F : Type) [Field F] (r n : ℕ)
    (k : {k : Fin r // k.val ≠ 0}) (b : Fin n → Fˣ) :
    (ymat F r n k).map (sprDiagHom F r n b)
      = Matrix.diagonal (fun i => MvPolynomial.C ((b i : F)))
        * ymat F r n k
        * Matrix.diagonal (fun j => MvPolynomial.C (((b j)⁻¹ : Fˣ) : F)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, ymat_apply, sprDiagHom_X_inr,
    MvPolynomial.C_mul]
  simp only [Units.val_inv_eq_inv_val]
  ring

#print axioms ymat_map_sprDiagHom

/-- ★★★★★★ **`charpoly (ymat)` 在环面作用下不变**（共轭不变性 ＋ `charpoly_mul_comm`）。 -/
theorem charpoly_ymat_sprDiagHom (F : Type) [Field F] (r n : ℕ)
    (k : {k : Fin r // k.val ≠ 0}) (b : Fin n → Fˣ) :
    ((ymat F r n k).map (sprDiagHom F r n b)).charpoly = (ymat F r n k).charpoly := by
  rw [ymat_map_sprDiagHom]
  have hcancel : Matrix.diagonal (fun j => MvPolynomial.C (((b j)⁻¹ : Fˣ) : F))
      * Matrix.diagonal (fun i => MvPolynomial.C ((b i : F)))
      = (1 : Matrix (Fin n) (Fin n) (Spr F r n)) := by
    rw [Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [← map_mul]
    · simp [hij]
  rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm (Matrix.diagonal (fun i => MvPolynomial.C ((b i : F)))),
    Matrix.mul_assoc, hcancel, Matrix.mul_one]

#print axioms charpoly_ymat_sprDiagHom

end SprYmatCharpoly


/-! ## §207 ★★★★★★ **`Y`-方向系数块**：`charpoly (ymat)` 的系数 `N`-不变（⟹ `hZ` 使其 ∈ `C`）（第 682 轮）

§206 做了 `Y`-方向的 **`T` 半边**（对角共轭）。本轮补 **`S_n` 半边**并合流：

```
(ymat).map (sprPermAlgEquiv σ) = ymat.submatrix σ σ            （行/列重排）
charpoly (ymat.submatrix σ σ) = charpoly (ymat)                （Matrix.charpoly_reindex）
⟹ charpoly (ymat) 的每个系数 ∈ S'^N                            （T 半 ＋ S_n 半，合并）
⟹ hZ ⟹ 每个系数 ∈ C                                            （sprCenterImageField）
```

| 件 | 内容 |
|---|---|
| ★★★★★ `ymat_map_sprPermAlgEquiv` | `(ymat).map (sprPermAlgEquiv σ) = ymat.submatrix σ σ` |
| ★★★★★★ `charpoly_ymat_sprPermAlgEquiv` | `charpoly` 在 `S_n` 作用下不变（`Matrix.charpoly_reindex` ＋ `reindex_apply`） |
| ★★★★★★★ `sprNFixed_charpoly_coeff_ymat` | **`charpoly (ymat)` 的每个系数 `N`-不变**（T 半 ＋ S_n 半） |
| ★★★★★★★ `charpoly_ymat_coeff_mem_sprCenterImageField_of_zHalf` | **`hZ` ⟹ 每个系数 ∈ `C`** |

**射程（勿夸大）**：这是 `Y`-方向的**系数块**；`Y` 的 CH 归约（照 §205 的模式）**未做**；
双向混合与词归约**未做**；`XiZSpanHypK'` **未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprYmatCoeffs

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000

open Matrix
open ABGV52

/-- ★★★★★ **`S_n` 作用 ＝ 行/列重排**：`(ymat).map (sprPermAlgEquiv σ) = ymat.submatrix σ σ`。 -/
theorem ymat_map_sprPermAlgEquiv (F : Type) [Field F] (r n : ℕ)
    (k : {k : Fin r // k.val ≠ 0}) (σ : Equiv.Perm (Fin n)) :
    (ymat F r n k).map (sprPermAlgEquiv F r n σ)
      = (ymat F r n k).submatrix (⇑σ) (⇑σ) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply, Matrix.submatrix_apply, ymat_apply, ymat_apply, sprPermAlgEquiv_X_inr]

#print axioms ymat_map_sprPermAlgEquiv

/-- ★★★★★★ **`charpoly (ymat)` 在 `S_n` 作用下不变**（`charpoly_reindex`）。 -/
theorem charpoly_ymat_sprPermAlgEquiv (F : Type) [Field F] (r n : ℕ)
    (k : {k : Fin r // k.val ≠ 0}) (σ : Equiv.Perm (Fin n)) :
    ((ymat F r n k).map (sprPermAlgEquiv F r n σ)).charpoly = (ymat F r n k).charpoly := by
  rw [ymat_map_sprPermAlgEquiv]
  have h : (ymat F r n k).submatrix (⇑σ) (⇑σ)
      = (Matrix.reindex (σ.symm : Equiv.Perm (Fin n)) (σ.symm : Equiv.Perm (Fin n)))
          (ymat F r n k) := by
    rw [Matrix.reindex_apply]
    simp
  rw [h, Matrix.charpoly_reindex]

#print axioms charpoly_ymat_sprPermAlgEquiv


/-- ★★★★★ **`charpoly (ymat)` 的每个系数 `N`-不变**（环面 ＋ 置换两半合起来）。 -/
theorem sprNFixed_charpoly_coeff_ymat (F : Type) [Field F] (r n : ℕ)
    (k : {k : Fin r // k.val ≠ 0}) (i : ℕ) :
    sprNFixed F r n ((ymat F r n k).charpoly.coeff i) := by
  constructor
  · intro b
    have h := charpoly_ymat_sprDiagHom F r n k b
    have h2 : Polynomial.map (sprDiagHom F r n b) (ymat F r n k).charpoly
        = (ymat F r n k).charpoly := by
      rw [← Matrix.charpoly_map]
      exact h
    simpa [Polynomial.coeff_map] using congrArg (fun p : Polynomial (Spr F r n) => p.coeff i) h2
  · intro σ
    have h := charpoly_ymat_sprPermAlgEquiv F r n k σ
    have h2 : Polynomial.map (sprPermAlgEquiv F r n σ).toRingHom (ymat F r n k).charpoly
        = (ymat F r n k).charpoly := by
      rw [← Matrix.charpoly_map]
      exact h
    simpa [Polynomial.coeff_map] using congrArg (fun p : Polynomial (Spr F r n) => p.coeff i) h2

#print axioms sprNFixed_charpoly_coeff_ymat

/-- ★★★★★★ **`hZ` ⟹ `charpoly (ymat)` 的系数落进 `C`**（`Y`-方向 CH 归约的系数块）。 -/
theorem charpoly_ymat_coeff_mem_sprCenterImageField_of_zHalf (F : Type) [Field F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
    (k : {k : Fin 2 // k.val ≠ 0}) (i : ℕ) :
    algebraMap (Spr F 2 9) (SprField F 2 9) ((ymat F 2 9 k).charpoly.coeff i)
      ∈ sprCenterImageField F 2 9 D k₀ hk₀ := by
  refine hZ ?_
  rw [mem_sprNFixedField_iff]
  exact ⟨sprFieldTFixed_algebraMap F 2 9 (sprNFixed_charpoly_coeff_ymat F 2 9 k i).1,
    sprFieldSFixed_algebraMap F 2 9 (sprNFixed_charpoly_coeff_ymat F 2 9 k i).2⟩

#print axioms charpoly_ymat_coeff_mem_sprCenterImageField_of_zHalf

end SprYmatCoeffs


/-! ## §208 ★★★★★★★★ **`Y`-方向归约闭环** —— `Y^9 + ∑_{i<9} d_i•Y^i = 0`（`d_i ∈ C`）（第 683 轮）

§205 做完 `X`-方向；§206／§207 做完 `Y` 的**系数块**（`charpoly (ymat)` 的系数 `N`-不变 ⟹ `hZ` 使之 ∈ `C`）。
本轮照 §205 的模式把 **`Y` 的 Cayley–Hamilton** 压到矩阵层：

```
(aeval Y) Y.charpoly = 0, natDegree = 9（Monic.natDegree_map ＋ charpoly_natDegree_eq_dim）
⟹ ∑_{i<9} (coeff i) • Y^i + Y^9 = 0,   coeff 9 = 1（首一）
⟹ Y^9 + ∑_{i<9} d_i • Y^i = 0,  d_i = algebraMap ((charpoly (ymat)).coeff i) ∈ C（§207）
```

| 件 | 内容 |
|---|---|
| ★★★★ `ymatK` | `Y` 在 `K'` 里的像 `(ymat).map (algebraMap)`（具名，避免长表达式重复展开） |
| ★★★★★★★★ `ymatK_pow_add_sum_eq_zero` | **`hZ ⟹ ∃ d ∈ C^9, Y^9 + ∑_{i<9} d_i•Y^i = 0`** |

**⟹ 现状**：`Ξ = {X^i Y^j}` 的 `Z`-张成，**两个纯方向的归约都已机检**。
剩下：**双向混合**（`X^k Y^m` 同时出现时的降阶）与**词归约**（一般字的降阶）。

**工艺（R683）**：
* `(ymat).map charpoly` 的次数用 **`Matrix.charpoly_monic … |>.natDegree_map`**（比
  `natDegree_map_eq_of_leadingCoeff_ne_zero` 少一次 side-goal）；
* 把 `Y` 提成具名 `def`（`ymatK`）**不只是美观**：长表达式直接写在**陈述**里会让
  **kernel** 报 `deep recursion`（`maxRecDepth` 默认远远不够；本段设 `1000000`）。

**射程（勿夸大）**：双向混合与词归约**未做**；`XiZSpanHypK'` **未证**；`hZ` **未证**；
**H2 见文件头「当前状态」。** -/

section SprYmatReduction

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- `Y` 在 `K'` 里的像（`ymat` 沿 `algebraMap`）。 -/
noncomputable def ymatK (F : Type) [Field F] (r n : ℕ)
    (k : {k : Fin r // k.val ≠ 0}) : Matrix (Fin n) (Fin n) (SprField F r n) :=
  (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))

/-- ★★★★★★★ **`Y`-方向 CH 归约**：`hZ ⟹ ∃ d ∈ C^9, Y^9 + ∑_{i<9} d_i • Y^i = 0`。 -/
theorem ymatK_pow_add_sum_eq_zero (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
    (k : {k : Fin 2 // k.val ≠ 0}) :
    ∃ d : Fin 9 → SprField F 2 9,
      (∀ i, d i ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (ymatK F 2 9 k) ^ 9
        + ∑ i : Fin 9, d i • (ymatK F 2 9 k) ^ (i : ℕ) = 0 := by
  have hnd : (ymatK F 2 9 k).charpoly.natDegree = 9 := by
    rw [ymatK, Matrix.charpoly_map,
      (Matrix.charpoly_monic (ymat F 2 9 k)).natDegree_map]
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hcoeff9 : (ymatK F 2 9 k).charpoly.coeff 9 = 1 := by
    have h : (ymatK F 2 9 k).charpoly.coeff (ymatK F 2 9 k).charpoly.natDegree = 1 :=
      (Matrix.charpoly_monic _).coeff_natDegree
    simpa [hnd] using h
  have hCH := Matrix.aeval_self_charpoly (ymatK F 2 9 k)
  rw [Polynomial.aeval_eq_sum_range, hnd, Finset.sum_range_succ, hcoeff9, one_smul] at hCH
  refine ⟨fun i => algebraMap (Spr F 2 9) (SprField F 2 9)
      ((ymat F 2 9 k).charpoly.coeff (i : ℕ)), ?_, ?_⟩
  · intro i
    exact charpoly_ymat_coeff_mem_sprCenterImageField_of_zHalf F D k₀ hk₀ hZ k (i : ℕ)
  · have hcoeff : ∀ i : ℕ, (ymatK F 2 9 k).charpoly.coeff i
        = algebraMap (Spr F 2 9) (SprField F 2 9) ((ymat F 2 9 k).charpoly.coeff i) := by
      intro i
      rw [ymatK, Matrix.charpoly_map, Polynomial.coeff_map]
    have hCH' : (∑ i : Fin 9,
        algebraMap (Spr F 2 9) (SprField F 2 9) ((ymat F 2 9 k).charpoly.coeff ((i : ℕ)))
          • (ymatK F 2 9 k) ^ ((i : ℕ))) + (ymatK F 2 9 k) ^ 9 = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        algebraMap (Spr F 2 9) (SprField F 2 9) ((ymat F 2 9 k).charpoly.coeff i)
          • (ymatK F 2 9 k) ^ i)]
      rw [show (∑ i ∈ Finset.range 9,
            algebraMap (Spr F 2 9) (SprField F 2 9) ((ymat F 2 9 k).charpoly.coeff i)
              • (ymatK F 2 9 k) ^ i)
          = ∑ i ∈ Finset.range 9, (ymatK F 2 9 k).charpoly.coeff i • (ymatK F 2 9 k) ^ i from
        Finset.sum_congr rfl fun i _ => by rw [hcoeff]]
      exact hCH
    rw [add_comm]
    exact hCH'

#print axioms ymatK_pow_add_sum_eq_zero

end SprYmatReduction


/-! ## §209 ★★★★★★★ **替换引理**（`X^9·M` 与 `Y^9·M`）—— 双向混合归约的引擎（第 684 轮）

§205／§208 给的是**纯幂**的降阶（`X^9`、`Y^9` 本身）。双向混合（`X^k Y^m` 同时出现）需要
**就地替换**：任何位置出现 `X^9`（或 `Y^9`）都能换成 `1,…,X^8`（或 `1,…,Y^8`）的 `C`-组合，
**乘在右边的任意矩阵 `M` 不受影响**。

```
X^9 + ∑_{i<9} c_i•X^i = 0   ⟹   X^9·M = −∑_{i<9} c_i•(X^i·M)
Y^9 + ∑_{i<9} d_i•Y^i = 0   ⟹   Y^9·M = −∑_{i<9} d_i•(Y^i·M)
```

| 件 | 内容 |
|---|---|
| ★★★★★★★ `xdiagK_pow9_mul_of_zHalf` | **`X^9·M` 的就地替换** |
| ★★★★★★★ `ymatK_pow9_mul_of_zHalf` | **`Y^9·M` 的就地替换** |

**为何这够双向混合**：`X^k Y^m` 中先把 `X^k` 按左端降阶（`X^k = Σ c_i X^i`），
余下每个单项 `X^i Y^m` 里 `Y^m = Y^9·Y^{m-9}`，**`Y^9` 在其子积中仍是左端**，
故同一引理可再降一次——迭代即得。

**射程（勿夸大）**：迭代降阶（`∀ k, X^k·M ∈ span`）**未写**；`XiZSpanHypK'` **未证**；
`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprReplace

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★ **`X`-替换引理（左乘形态）**：`X^9 · M` 可换成 `1,…,X^8` 左乘的 `C`-组合。

这是**双向混合**归约的引擎：任何出现 `X^9` 的位置都可就地降阶。 -/
theorem xdiagK_pow9_mul_of_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
    (M : Matrix (Fin 9) (Fin 9) (SprField F 2 9)) :
    ∃ c : Fin 9 → SprField F 2 9,
      (∀ i, c i ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (sprXdiagK F 2 9) ^ 9 * M
        = ∑ i : Fin 9, c i • ((sprXdiagK F 2 9) ^ (i : ℕ) * M) := by
  obtain ⟨c, hcmem, hc⟩ := xdiagK_pow_add_sum_eq_zero_of_zHalf F D k₀ hk₀ hZ
  refine ⟨fun i => -c i, fun i => neg_mem (hcmem i), ?_⟩
  have hX : (sprXdiagK F 2 9) ^ 9
      = -∑ i : Fin 9, c i • (sprXdiagK F 2 9) ^ (i : ℕ) :=
    eq_neg_of_add_eq_zero_left hc
  have hstep : ∀ i : Fin 9, -(((c i) • (sprXdiagK F 2 9) ^ (i : ℕ)) * M)
      = (-c i) • ((sprXdiagK F 2 9) ^ (i : ℕ) * M) := by
    intro i
    rw [smul_mul_assoc, neg_smul]
  calc (sprXdiagK F 2 9) ^ 9 * M
      = (-∑ i : Fin 9, c i • (sprXdiagK F 2 9) ^ (i : ℕ)) * M := by rw [hX]
    _ = -((∑ i : Fin 9, c i • (sprXdiagK F 2 9) ^ (i : ℕ)) * M) := neg_mul _ _
    _ = -(∑ i : Fin 9, ((c i) • (sprXdiagK F 2 9) ^ (i : ℕ)) * M) := by rw [Finset.sum_mul]
    _ = ∑ i : Fin 9, -(((c i) • (sprXdiagK F 2 9) ^ (i : ℕ)) * M) :=
        (Finset.sum_neg_distrib (fun i : Fin 9 =>
          ((c i) • (sprXdiagK F 2 9) ^ (i : ℕ)) * M)).symm
    _ = ∑ i : Fin 9, (-c i) • ((sprXdiagK F 2 9) ^ (i : ℕ) * M) :=
        Finset.sum_congr rfl fun i _ => hstep i

#print axioms xdiagK_pow9_mul_of_zHalf

/-- ★★★★★★★ **`Y`-替换引理（左乘形态）**：`Y^9 · M` 可换成 `1,…,Y^8` 左乘的 `C`-组合。 -/
theorem ymatK_pow9_mul_of_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
    (k : {k : Fin 2 // k.val ≠ 0}) (M : Matrix (Fin 9) (Fin 9) (SprField F 2 9)) :
    ∃ d : Fin 9 → SprField F 2 9,
      (∀ i, d i ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (ymatK F 2 9 k) ^ 9 * M
        = ∑ i : Fin 9, d i • ((ymatK F 2 9 k) ^ (i : ℕ) * M) := by
  obtain ⟨d, hdmem, hd⟩ := ymatK_pow_add_sum_eq_zero F D k₀ hk₀ hZ k
  refine ⟨fun i => -d i, fun i => neg_mem (hdmem i), ?_⟩
  have hY : (ymatK F 2 9 k) ^ 9
      = -∑ i : Fin 9, d i • (ymatK F 2 9 k) ^ (i : ℕ) :=
    eq_neg_of_add_eq_zero_left hd
  have hstep : ∀ i : Fin 9, -(((d i) • (ymatK F 2 9 k) ^ (i : ℕ)) * M)
      = (-d i) • ((ymatK F 2 9 k) ^ (i : ℕ) * M) := by
    intro i
    rw [smul_mul_assoc, neg_smul]
  calc (ymatK F 2 9 k) ^ 9 * M
      = (-∑ i : Fin 9, d i • (ymatK F 2 9 k) ^ (i : ℕ)) * M := by rw [hY]
    _ = -((∑ i : Fin 9, d i • (ymatK F 2 9 k) ^ (i : ℕ)) * M) := neg_mul _ _
    _ = -(∑ i : Fin 9, ((d i) • (ymatK F 2 9 k) ^ (i : ℕ)) * M) := by rw [Finset.sum_mul]
    _ = ∑ i : Fin 9, -(((d i) • (ymatK F 2 9 k) ^ (i : ℕ)) * M) :=
        (Finset.sum_neg_distrib (fun i : Fin 9 =>
          ((d i) • (ymatK F 2 9 k) ^ (i : ℕ)) * M)).symm
    _ = ∑ i : Fin 9, (-d i) • ((ymatK F 2 9 k) ^ (i : ℕ) * M) :=
        Finset.sum_congr rfl fun i _ => hstep i

#print axioms ymatK_pow9_mul_of_zHalf

end SprReplace


/-! ## §210 ★★★★★★★★★ **`X` 的迭代降阶**：`∀ k, X^k = ∑_{i<9} c_i • X^i`（`c_i ∈ C`）（第 685 轮）

§205 只给 `X^9` 一条关系；§209 给了"就地替换"（`X^9·M`）。本轮把替换**迭代到任意幂**：

```
X^k = X^9 · X^{k−9} = (−∑_{i<9} c0_i X^i) · X^{k−9}
    = −∑_{i<9} c0_i • X^{i+(k−9)}                     （指数都 < k）
    = −∑_{i<9} c0_i • (∑_{j<9} d_{ij} • X^j)          （对 k′ = i+(k−9) 用归纳假设）
    = ∑_{j<9} (−∑_{i<9} c0_i d_{ij}) • X^j            （换和序）
```

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `xdiagK_pow_cspan` | **`hZ ⟹ ∀ k, ∃ c ∈ C^9, X^k = ∑_{i<9} c_i • X^i`** |

**⟹ 意义**：`X` 一侧的 `Z`-张成**完全闭环**（任意幂都被压到 `< 9`）。
`Y` 一侧结构完全相同（把 `sprXdiagK` 换成 `ymatK`、关系换成 §208 的那条即可），
**下一轮照抄**；然后双向混合只需对两个指数分别用本引理（C-系数与矩阵整体交换）。

**工艺（R685）**：这轮是"求和重排"的教科书案例，四个易错点各花一次编译——
① `Finset.smul_sum` 要求**常数**标量，`∑ x, f x • a`（标量依赖 x）要用 **`Finset.sum_smul`**；
② `∑ x, f x • a = (∑ f x) • a` 的 `.symm` 方向别写反；
③ `-(c • x) = (-c) • x` 用 `neg_smul` 的 `.symm`，而 `-∑ = ∑ -` 用 `Finset.sum_neg_distrib`；
④ `smul_smul` 要**显式给三个参数**，否则 `MulAction` 实例卡住（`?m` 未定）。

**射程（勿夸大）**：`Y` 侧与双向混合**未写**；`XiZSpanHypK'` **未证**；`hZ` **未证**；
**H2 见文件头「当前状态」。** -/

section SprXPowCspan

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **`X` 的迭代降阶**：对任意 `k`，`X^k` 是 `1,…,X^8` 的 `C`-线性组合。 -/
theorem xdiagK_pow_cspan (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ∀ k : ℕ, ∃ c : Fin 9 → SprField F 2 9,
      (∀ i, c i ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (sprXdiagK F 2 9) ^ k = ∑ i : Fin 9, c i • (sprXdiagK F 2 9) ^ (i : ℕ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k 9 with hk | hk
    · refine ⟨fun i => if (i : ℕ) = k then 1 else 0, ?_, ?_⟩
      · intro i
        show (if (i : ℕ) = k then (1 : SprField F 2 9) else 0)
          ∈ sprCenterImageField F 2 9 D k₀ hk₀
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · symm
        refine (Finset.sum_eq_single (⟨k, hk⟩ : Fin 9) ?_ ?_).trans ?_
        · intro b _ hb
          have hbk : (b : ℕ) ≠ k := fun h => hb (Fin.ext h)
          simp [hbk]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · simp
    · obtain ⟨c0, hc0mem, hc0⟩ := xdiagK_pow_add_sum_eq_zero_of_zHalf F D k₀ hk₀ hZ
      have hX9 : (sprXdiagK F 2 9) ^ 9
          = -∑ i : Fin 9, c0 i • (sprXdiagK F 2 9) ^ (i : ℕ) :=
        eq_neg_of_add_eq_zero_left hc0
      have hlt : ∀ i : Fin 9, (i : ℕ) + (k - 9) < k := by
        intro i
        have := i.isLt
        omega
      choose d hdmem hd using fun i : Fin 9 => ih ((i : ℕ) + (k - 9)) (hlt i)
      refine ⟨fun j => -(∑ i : Fin 9, c0 i * d i j), ?_, ?_⟩
      · intro j
        refine neg_mem (sum_mem fun i _ => mul_mem (hc0mem i) (hdmem i j))
      · calc (sprXdiagK F 2 9) ^ k
            = (sprXdiagK F 2 9) ^ 9 * (sprXdiagK F 2 9) ^ (k - 9) := by
              rw [← pow_add]
              congr 1
              omega
          _ = (-∑ i : Fin 9, c0 i • (sprXdiagK F 2 9) ^ (i : ℕ))
                * (sprXdiagK F 2 9) ^ (k - 9) := by rw [hX9]
          _ = -((∑ i : Fin 9, c0 i • (sprXdiagK F 2 9) ^ (i : ℕ))
                * (sprXdiagK F 2 9) ^ (k - 9)) := neg_mul _ _
          _ = -(∑ i : Fin 9, (c0 i • (sprXdiagK F 2 9) ^ (i : ℕ))
                * (sprXdiagK F 2 9) ^ (k - 9)) := by rw [Finset.sum_mul]
          _ = -(∑ i : Fin 9, c0 i • ((sprXdiagK F 2 9) ^ (i : ℕ)
                * (sprXdiagK F 2 9) ^ (k - 9))) := by
              rw [Finset.sum_congr rfl fun i _ => smul_mul_assoc _ _ _]
          _ = -(∑ i : Fin 9, c0 i • (sprXdiagK F 2 9) ^ ((i : ℕ) + (k - 9))) := by
              rw [Finset.sum_congr rfl fun i _ => by rw [← pow_add]]
          _ = -(∑ i : Fin 9, c0 i
                • (∑ j : Fin 9, d i j • (sprXdiagK F 2 9) ^ (j : ℕ))) := by
              rw [Finset.sum_congr rfl fun i _ => by rw [hd i]]
          _ = -(∑ i : Fin 9, ∑ j : Fin 9, (c0 i * d i j)
                • (sprXdiagK F 2 9) ^ (j : ℕ)) := by
              refine congrArg Neg.neg ?_
              rw [Finset.sum_congr rfl fun i _ => Finset.smul_sum]
              exact Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun j _ =>
                  smul_smul (c0 i) (d i j) ((sprXdiagK F 2 9) ^ (j : ℕ))
          _ = -(∑ j : Fin 9, (∑ i : Fin 9, c0 i * d i j)
                • (sprXdiagK F 2 9) ^ (j : ℕ)) := by
              refine congrArg Neg.neg ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => (Finset.sum_smul).symm
          _ = ∑ j : Fin 9, -(∑ i : Fin 9, c0 i * d i j)
                • (sprXdiagK F 2 9) ^ (j : ℕ) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun j _ =>
                (neg_smul (∑ i : Fin 9, c0 i * d i j) ((sprXdiagK F 2 9) ^ (j : ℕ))).symm

#print axioms xdiagK_pow_cspan

end SprXPowCspan


/-! ## §211 ★★★★★★★★★ **`Y` 的迭代降阶**：`∀ m, Y^m = ∑_{j<9} d_j • Y^j`（`d_j ∈ C`）（第 686 轮）

与 §210 结构完全相同（把 `sprXdiagK` 换成 `ymatK`、CH 关系换成 §208 的那条）。
**写的时候换掉了归纳变量名**（`m` 与子类型参数 `kk`），避免 R685 教训 107 的
"`k` 同名错位"——文本替换会静默生成错版本，**重写**才安全。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `ymatK_pow_cspan` | **`hZ ⟹ ∀ m, ∃ d ∈ C^9, Y^m = ∑_{j<9} d_j • Y^j`** |

**⟹ 现状**：`X`、`Y` **两个方向的任意幂降阶都已机检**。
剩下唯一一块是**双向混合**：`X^a Y^b` 的 `C`-组合（对两个指数分别施用上面两件）。

**射程（勿夸大）**：双向混合**未写**；`XiZSpanHypK'` **未证**；`hZ` **未证**；**H2 见文件头「当前状态」。** -/

section SprYPowCspan

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **`Y` 的迭代降阶**：对任意 `m`，`Y^m` 是 `1,…,Y^8` 的 `C`-线性组合。 -/
theorem ymatK_pow_cspan (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
    (kk : {k : Fin 2 // k.val ≠ 0}) :
    ∀ m : ℕ, ∃ d : Fin 9 → SprField F 2 9,
      (∀ j, d j ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (ymatK F 2 9 kk) ^ m = ∑ j : Fin 9, d j • (ymatK F 2 9 kk) ^ (j : ℕ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 9 with hm | hm
    · refine ⟨fun j => if (j : ℕ) = m then 1 else 0, ?_, ?_⟩
      · intro j
        show (if (j : ℕ) = m then (1 : SprField F 2 9) else 0)
          ∈ sprCenterImageField F 2 9 D k₀ hk₀
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · symm
        refine (Finset.sum_eq_single (⟨m, hm⟩ : Fin 9) ?_ ?_).trans ?_
        · intro b _ hb
          have hbm : (b : ℕ) ≠ m := fun h => hb (Fin.ext h)
          simp [hbm]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · simp
    · obtain ⟨d0, hd0mem, hd0⟩ := ymatK_pow_add_sum_eq_zero F D k₀ hk₀ hZ kk
      have hY9 : (ymatK F 2 9 kk) ^ 9
          = -∑ j : Fin 9, d0 j • (ymatK F 2 9 kk) ^ (j : ℕ) :=
        eq_neg_of_add_eq_zero_left hd0
      have hlt : ∀ j : Fin 9, (j : ℕ) + (m - 9) < m := by
        intro j
        have := j.isLt
        omega
      choose e hem he using fun j : Fin 9 => ih ((j : ℕ) + (m - 9)) (hlt j)
      refine ⟨fun i => -(∑ j : Fin 9, d0 j * e j i), ?_, ?_⟩
      · intro i
        refine neg_mem (sum_mem fun j _ => mul_mem (hd0mem j) (hem j i))
      · calc (ymatK F 2 9 kk) ^ m
            = (ymatK F 2 9 kk) ^ 9 * (ymatK F 2 9 kk) ^ (m - 9) := by
              rw [← pow_add]
              congr 1
              omega
          _ = (-∑ j : Fin 9, d0 j • (ymatK F 2 9 kk) ^ (j : ℕ))
                * (ymatK F 2 9 kk) ^ (m - 9) := by rw [hY9]
          _ = -((∑ j : Fin 9, d0 j • (ymatK F 2 9 kk) ^ (j : ℕ))
                * (ymatK F 2 9 kk) ^ (m - 9)) := neg_mul _ _
          _ = -(∑ j : Fin 9, (d0 j • (ymatK F 2 9 kk) ^ (j : ℕ))
                * (ymatK F 2 9 kk) ^ (m - 9)) := by rw [Finset.sum_mul]
          _ = -(∑ j : Fin 9, d0 j • ((ymatK F 2 9 kk) ^ (j : ℕ)
                * (ymatK F 2 9 kk) ^ (m - 9))) := by
              rw [Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _]
          _ = -(∑ j : Fin 9, d0 j • (ymatK F 2 9 kk) ^ ((j : ℕ) + (m - 9))) := by
              rw [Finset.sum_congr rfl fun j _ => by rw [← pow_add]]
          _ = -(∑ j : Fin 9, d0 j
                • (∑ i : Fin 9, e j i • (ymatK F 2 9 kk) ^ (i : ℕ))) := by
              rw [Finset.sum_congr rfl fun j _ => by rw [he j]]
          _ = -(∑ j : Fin 9, ∑ i : Fin 9, (d0 j * e j i)
                • (ymatK F 2 9 kk) ^ (i : ℕ)) := by
              refine congrArg Neg.neg ?_
              rw [Finset.sum_congr rfl fun j _ => Finset.smul_sum]
              exact Finset.sum_congr rfl fun j _ =>
                Finset.sum_congr rfl fun i _ =>
                  smul_smul (d0 j) (e j i) ((ymatK F 2 9 kk) ^ (i : ℕ))
          _ = -(∑ i : Fin 9, (∑ j : Fin 9, d0 j * e j i)
                • (ymatK F 2 9 kk) ^ (i : ℕ)) := by
              refine congrArg Neg.neg ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul).symm
          _ = ∑ i : Fin 9, -(∑ j : Fin 9, d0 j * e j i)
                • (ymatK F 2 9 kk) ^ (i : ℕ) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun i _ =>
                (neg_smul (∑ j : Fin 9, d0 j * e j i) ((ymatK F 2 9 kk) ^ (i : ℕ))).symm

#print axioms ymatK_pow_cspan

end SprYPowCspan


/-! ## §212 ★★★★★★★★★ **双向混合降阶**：`X^a Y^b` 的 `C`-组合（第 687 轮）

§210／§211 分别做了 `X`、`Y` 的任意幂降阶。本轮合流：**两个指数同时任意**。

```
X^a · Y^b = (∑_i c_i • X^i) · Y^b        （§210）
          = ∑_i c_i • (X^i · Y^b)
          = ∑_i c_i • (X^i · (∑_j d_j • Y^j))   （§211）
          = ∑_{i,j} (c_i d_j) • (X^i · Y^j)     （Finset.mul_sum ＋ mul_smul_comm ＋ smul_smul）
          = ∑_{p : Fin 9 × Fin 9} (c_{p.1} d_{p.2}) • (X^{p.1} · Y^{p.2})   （Fintype.sum_prod_type）
```

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `xdiagK_ymatK_mixed_cspan` | **`hZ ⟹ ∃ c ∈ C^{9×9}, X^a Y^b = ∑_p c_p • (X^{p.1} Y^{p.2})`** |

**⚠ 射程（本轮最重要的诚实边界，已写入前沿笔记 §30）**：
本节及 §205／§208／§210／§211 **只覆盖**"每个极大段要么纯 `X`、要么纯 `Y`"的字——
即 **`X`-`Y` **不交错的**字（如 `X^a Y^b`）。真正的一般字（如 `XYX`）的归约**不在**本路线的能力内：
`X`、`Y` 作为矩阵**不交换**，故 Cayley–Hamilton（它只给"同一矩阵的幂之间的关系"）**不能**
把 `YX` 换成 `XY` 的修正项。**⟹ `XiZSpanHypK'` 不是 CH 能到的**；它需要**秩 `n²` 定理**
（`R` 在中心上是秩 `n²` 的模／Azumaya），即 §199 里已经指出的那条已发表输入。 -/

section SprMixedCspan

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **双向混合降阶**：`X^a Y^b` 是 `{X^i Y^j}` 的 `C`-线性组合。 -/
theorem xdiagK_ymatK_mixed_cspan (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀)
    (kk : {k : Fin 2 // k.val ≠ 0}) (a b : ℕ) :
    ∃ c : Fin 9 × Fin 9 → SprField F 2 9,
      (∀ p, c p ∈ sprCenterImageField F 2 9 D k₀ hk₀) ∧
      (sprXdiagK F 2 9) ^ a * (ymatK F 2 9 kk) ^ b
        = ∑ p : Fin 9 × Fin 9, c p
            • ((sprXdiagK F 2 9) ^ (p.1 : ℕ) * (ymatK F 2 9 kk) ^ (p.2 : ℕ)) := by
  obtain ⟨c, hcmem, hc⟩ := xdiagK_pow_cspan F D k₀ hk₀ hZ a
  obtain ⟨d, hdmem, hd⟩ := ymatK_pow_cspan F D k₀ hk₀ hZ kk b
  refine ⟨fun p => c p.1 * d p.2, fun p => mul_mem (hcmem p.1) (hdmem p.2), ?_⟩
  calc (sprXdiagK F 2 9) ^ a * (ymatK F 2 9 kk) ^ b
      = (∑ i : Fin 9, c i • (sprXdiagK F 2 9) ^ (i : ℕ)) * (ymatK F 2 9 kk) ^ b := by rw [hc]
    _ = ∑ i : Fin 9, (c i • (sprXdiagK F 2 9) ^ (i : ℕ)) * (ymatK F 2 9 kk) ^ b :=
        Finset.sum_mul _ _ _
    _ = ∑ i : Fin 9, c i • ((sprXdiagK F 2 9) ^ (i : ℕ) * (ymatK F 2 9 kk) ^ b) := by
        exact Finset.sum_congr rfl fun i _ => smul_mul_assoc (c i) _ _
    _ = ∑ i : Fin 9, c i
          • ((sprXdiagK F 2 9) ^ (i : ℕ) * ∑ j : Fin 9, d j • (ymatK F 2 9 kk) ^ (j : ℕ)) := by
        rw [hd]
    _ = ∑ i : Fin 9, c i
          • (∑ j : Fin 9, d j • ((sprXdiagK F 2 9) ^ (i : ℕ) * (ymatK F 2 9 kk) ^ (j : ℕ))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine congrArg (fun M : Matrix (Fin 9) (Fin 9) (SprField F 2 9) => c i • M) ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ =>
          mul_smul_comm (d j) ((sprXdiagK F 2 9) ^ (i : ℕ)) ((ymatK F 2 9 kk) ^ (j : ℕ))
    _ = ∑ i : Fin 9, ∑ j : Fin 9, (c i * d j)
          • ((sprXdiagK F 2 9) ^ (i : ℕ) * (ymatK F 2 9 kk) ^ (j : ℕ)) := by
        rw [Finset.sum_congr rfl fun i _ => Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ =>
            smul_smul (c i) (d j) ((sprXdiagK F 2 9) ^ (i : ℕ) * (ymatK F 2 9 kk) ^ (j : ℕ))
    _ = ∑ p : Fin 9 × Fin 9, (c p.1 * d p.2)
          • ((sprXdiagK F 2 9) ^ (p.1 : ℕ) * (ymatK F 2 9 kk) ^ (p.2 : ℕ)) := by
        rw [Fintype.sum_prod_type]

#print axioms xdiagK_ymatK_mixed_cspan

end SprMixedCspan


/-! ## §213 ★★★★★★★★★★ **H2 ⟸ `hZ`（单条输入）** —— 路 B 的搬运补齐（第 689 轮）

**结构性结果**：H2 现在只依赖**一条**输入 `hZ`（＝ Saltman `prop:14.19` 的 `Z` 半，已发表）——
**不需要** `XiZSpanHypK'`（秩 `n²`／Azumaya），**也不需要** `KPFixedLeZ`。

**关键观察（本轮想通的点）**：`sprCenterZMapToField` 是**域到域**的 `F`-代数同态，
故其**像本身就是一个子域**，于是

```
Set.range f = f.fieldRange
```

而两边都已有料：`C ≤ fieldRange` 是**无条件机检**的（`sprCenterImageField_le_fieldRange`）；
`fieldRange ⊆ N` 由构造（`sprCenterZMapToField = val ∘ sprCenterZMap`，值域在 `N` 里）；
`hZ` 给 `N ≤ C`。⟹ `N = fieldRange = range` ⟹ **满射**。

| 件 | 内容 |
|---|---|
| ★★★★★★★★ `surjective_sprCenterZMap_of_zHalf` | **`hZ ⟹ Surjective (sprCenterZMap …)`** |
| ★★★★★★★★★★ `h2_of_zHalf_routeB` | **`hZ ⟹ ProcesiS9Hyp F ↥(ZCanon F 2 9 D)`** |

**⟹ 战役终点形态（R689 后）**：

```
H2  ⟸  hZ（唯一输入；已发表：Saltman prop:14.19 的 Z 半）
```

**射程（勿夸大）**：`hZ` 本身**未证**；**H2 见文件头「当前状态」。**
本节的贡献是把 H2 的输入清单**从两条压到一条**，且该条是**已发表**的 `prop:14.19`。
（路 A 的 `XiZSpanHypK'`／秩 `n²` 因此**不再是必需**——可留作独立兴趣。） -/

section SprRouteBEndgame

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★ **`hZ` ⟹ `sprCenterZMap` 满射**（路 B 的核心方向）。

机制：`sprCenterZMapToField` 是**域到域**的 `F`-代数同态，故其**像＝`fieldRange`**（像本身是子域）。
已知 `C ≤ fieldRange`（`sprCenterImageField_le_fieldRange`，**无条件机检**）；
而 `hZ` 给 `N ≤ C`。于是 `N ≤ fieldRange`，即每个 `N`-元都在像里 ⟹ 满射。 -/
theorem surjective_sprCenterZMap_of_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀) := by
  intro y
  have hyN : (y : SprField F 2 9) ∈ sprNFixedField F 2 9 := y.2
  have hyC : (y : SprField F 2 9) ∈ sprCenterImageField F 2 9 D k₀ hk₀ := hZ hyN
  have hyFR : (y : SprField F 2 9)
      ∈ (sprCenterZMapToField F 2 9 D k₀ hk₀).fieldRange :=
    sprCenterImageField_le_fieldRange F 2 9 D k₀ hk₀ hyC
  obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange).mp hyFR
  exact ⟨x, Subtype.ext hx⟩

#print axioms surjective_sprCenterZMap_of_zHalf

/-- ★★★★★★★★★★ **H2 ⟸ `hZ`（路 B，单条输入）**。 -/
theorem h2_of_zHalf_routeB (F : Type) [Field F] [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_ZEqNFixed F D (zEqNFixed_of_surjective F D hk₀
    (surjective_sprCenterZMap_of_zHalf F D k₀ hk₀ hZ))

#print axioms h2_of_zHalf_routeB

end SprRouteBEndgame


/-! ## §214 ★★★★★★★★★ **`hZ` ⟺ `sprCenterZMap` 满射** —— 终局输入的**单一形态**（第 690 轮）

R689 给了 `hZ ⟹ 满射`（从而 `hZ ⟹ H2`）。本轮补反向，得**两形态等价**：

```
Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)  ⟺  sprNFixedField F 2 9 ≤ C
```

**反向的机制（一行）**：满射 ⟹ 每个 `N`-元都是某个 `z` 的像；而像落在 `C` 里
（`sprCenterZMap_mem_sprCenterImageField`，**H2Final:3955，早已机检、无条件**）⟹ `N ≤ C`。

**★ 顺带更正 §100 的一条旧判读**：§100 头注说"`SField ↔ SprField` 的搬运**尚未**在库中显式化"。
**该判读已过时**——搬运所需的 `sprCenterZMap_mem_sprCenterImageField` 就在库里（`:3955`）。
本轮据此把两条旧路线（§100 的"满射"与 R689 的"`hZ`"）**合流为同一条输入的两个形态**。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `surjective_sprCenterZMap_iff_zHalf` | **`Surjective (sprCenterZMap)` ⟺ `hZ`** |

**射程（勿夸大）**：`hZ`／满射**均未证**；**H2 见文件头「当前状态」。**
本轮的增益是**输入口径的唯一化**（此后"剩余输入"只需报一条，两种写法等价）。

**工艺（R690）**：凡把 `sprCenterZMapToField` 写进**陈述**的尝试都失败（`synthInstanceFailed`）——
它的类型提及子类型塔 `↥(Algebra.adjoin …) → ↥(IntermediateField.adjoin …)`，
而塔实例**在陈述层**不可用（`haveI` 只在证明体内，教训 108）。
**故本节只在 `sprCenterZMap`（值域 `↥(sprNFixedAlg)`）层陈述**——同一定理，绕开塔。 -/

section SprZMapIff

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **`hZ` ⟺ `sprCenterZMap` 满射**（终局输入的两个等价形态，两方向都机检）。

* `⟸`（本轮）：满射 ⟹ 每个 `N`-元是 `sprCenterZMap` 的像 ⟹ 落在 `C` 里
  （`sprCenterZMap_mem_sprCenterImageField`，**早已机检**）⟹ `hZ`。
* `⟹`：R689 的 `surjective_sprCenterZMap_of_zHalf`。 -/
theorem surjective_sprCenterZMap_iff_zHalf (F : Type) [Field F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    Function.Surjective (sprCenterZMap F 2 9 D k₀ hk₀)
      ↔ sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀ := by
  constructor
  · intro h x hx
    have hx' : x ∈ sprNFixedAlg F 2 9 := hx
    obtain ⟨z, hz⟩ := h ⟨x, hx'⟩
    have hmem : ((sprCenterZMap F 2 9 D k₀ hk₀ z : ↥(sprNFixedAlg F 2 9)) : SprField F 2 9)
        ∈ sprCenterImageField F 2 9 D k₀ hk₀ :=
      sprCenterZMap_mem_sprCenterImageField F 2 9 D k₀ hk₀ z
    rw [hz] at hmem
    exact hmem
  · exact surjective_sprCenterZMap_of_zHalf F D k₀ hk₀

#print axioms surjective_sprCenterZMap_iff_zHalf

end SprZMapIff



/-! ## §216 ★★★★★★★★ **`ψ` 不是 `N`-等变的**（R693 审计的机检化）（第 694 轮）

R693 的解释性审计说："`sprPGLFixedField = ψ⁻¹(K^{PGL})` **不是** Saltman 比较中的那个对象"。
本轮把该判断落成**定理**：

```
∃ x ∈ K'^N,  ψ(x) ∉ K^{PGL}        （取 x = ∏_i x_{k₀,ii} = det X）
```

而 `prop:14.19` 说 `Z = K'^N`，`thm:14.16` 说 `Z ⊆ K^{PGL}`。**⟹ `ψ` 把中心元送出 `K^{PGL}`**，
故它**不可能是**把 `K'` 与 `K` 两侧作用对齐的映射：
`φ_A(x_ii) = x_ii`（`X` 在对角模型里是对角矩阵）而 `ψ_A(X_{k₀,ii}) = (A⁻¹X_{k₀}A)_{ii} ≠ X_{k₀,ii}`。

| 件 | 内容 |
|---|---|
| ★★★★★★★★★ `exists_nFixed_psiImage_not_pglFixed` | **存在 `x ∈ K'^N` 而 `ψ(x) ∉ K^{PGL}`** |
| ★★★★★★★★ `psi_prodX_not_mem_pglFixedField` | 具体反例：`x = ∏_i x_{k₀,ii}`（`= det X`） |

**⟹ 术语更正（本战役自用口径）**：
* `pglFixedField`（`S`-侧）与 `KPFixedLeZ`（`K^{PGL} ⊆ Z`）是**忠实**的（Saltman `thm:14.16`），
  **不因本节而撤回**；
* `sprPGLFixedField`（`comap` 形态）**不是**"`K' ∩ K^{PGL}`"——本节证明它**排除了中心元**。
  凡以它为"`K' ∩ K^{PGL}`"的论证（`(a)`／`(β1)`／`C ≤ P` 一支）**其解释须改写**：
  它们说的是关于这个 `comap` 的结论，**不是**关于 Saltman 对象的结论。

**射程（勿夸大）**：`hZ` **未证**；**H2 见文件头「当前状态」**；本节只更正**解释**，不改动路 B（§213）。 -/

section SprPsiNotEquivariant

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Matrix
open ABGV52

/-- ★★★★★★★★★ **`ψ` 把 `N`-不变元送出 `K^{PGL}`**（R693 审计的**机检化**）。

存在 `x ∈ K'^N`，其 `ψ`-像**不是** `PGL`-不变的。取 `x = ∏_i x_{k₀,ii}`（`det X`）。
**⟹ `ψ` 不是 `N`-等变的**，故 `sprPGLFixedField = ψ⁻¹(K^{PGL})` **不是** Saltman
`prop:14.19`／`thm:14.16` 比较中所用的那个对象（那里 `K'^N = Z ⊆ K^{PGL}`）。 -/
theorem exists_nFixed_psiImage_not_pglFixed (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) :
    ∃ x : SprField F r 9, x ∈ sprNFixedField F r 9
      ∧ sprToSField F r 9 k₀ hk₀ x ∉ pglFixedField F r := by
  refine ⟨algebraMap (Spr F r 9) (SprField F r 9)
    (∏ i : Fin 9, MvPolynomial.X (Sum.inl i)), ?_, ?_⟩
  · exact sprProdX_mem_sprNFixedField F r 9
  · intro hx
    refine sprProdX_not_mem_sprPGLFixedField F r k₀ hk₀ ?_
    rw [mem_sprPGLFixedField_iff]
    intro A
    exact hx A

#print axioms exists_nFixed_psiImage_not_pglFixed

/-- ★★★★★★★★ **推论**：`ψ` 不保中心元——`ψ(det X)` 在 `K^{PGL}` 之外，
而 `det X` 是中心元（`prop:14.19`：`K'^N = Z`）。 -/
theorem psi_prodX_not_mem_pglFixedField (F : Type) [Field F] (r : ℕ) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) :
    sprToSField F r 9 k₀ hk₀
        (algebraMap (Spr F r 9) (SprField F r 9)
          (∏ i : Fin 9, MvPolynomial.X (Sum.inl i)))
      ∉ pglFixedField F r := by
  intro hx
  refine sprProdX_not_mem_sprPGLFixedField F r k₀ hk₀ ?_
  rw [mem_sprPGLFixedField_iff]
  intro A
  exact hx A

#print axioms psi_prodX_not_mem_pglFixedField

end SprPsiNotEquivariant

/-! ## §215 ★★★★★ **公理审计补齐**：§1–§214 中未附 `#print axioms` 的定理／引理（第 691 轮）

闸门的公理白名单检查（`procesi-lean-crosscheck.py` 的 `[2]`）**只审计带 `#print axioms` 的声明**，
故本节把 §1–§214 里**遗漏**的 **67 件定理／引理**逐一补上审计行（此前它们**不进**白名单检查——
即闸门 `[2]` 的一条已知余量，见 `scripts/kb-tool-residuals.tsv` 的 `procesi-lean-crosscheck.py` 行）。

每行期望读数：`depends on axioms: [propext, Classical.choice, Quot.sound]`。
**若出现 `sorryAx` 或其它公理，闸门 `[2]` 会当场判否。** -/

section SprAxiomAuditSweep

#print axioms phiKAlgEquiv_algebraMap'
#print axioms psiSpr_mem_UDK'
#print axioms algebraMap_mem_center_UDK'
#print axioms UDK'_le_sprMatNFixedAlg
#print axioms mem_sprMatNFixed_of_mem_UDK'
#print axioms xiSprK_mem_UDK'
#print axioms xiSpanHypK'_of_xiBasisHypK'
#print axioms xiSpanHypK'_iff_surjective
#print axioms xiBasisHypK'_linearIndependent
#print axioms udkTensorToMatrix_surjective_of_xiSpanK'
#print axioms xiCoordMap_injective_of_xiBasisHypK'
#print axioms udkTensorEquivK'_symm_apply
#print axioms thetaSpr_agree_on_UDK'
#print axioms udkTensorToMatrixS''_tmul_one
#print axioms thetaSpr1_apply_UDK'
#print axioms thetaSpr2_apply_UDK'
#print axioms udkTensorToMatrixS''_tmul
#print axioms coeKtoS''_injective
#print axioms matMapKtoS''_apply
#print axioms matMapKtoS''_injective
#print axioms matMapKtoS''_smul
#print axioms coeKtoS''_mul
#print axioms mem_UDK'_of_theta_eq
#print axioms thetaAgreeHypK'_witness_UDK'
#print axioms sprMatNFixed_le_UDK'
#print axioms sprMatNFixed_le_UDK'_four
#print axioms matMapFaithfulHyp_of_xiBasisHypK'
#print axioms nfixedIsCoordHyp_of_xiBasisHypK'
#print axioms sprMatNFixed_le_UDK'_three
#print axioms center_UDK'_eq
#print axioms coeKtoS''_mul_eq_zero
#print axioms coeKtoS''_algebraMap_discr_mul_eq_zero
#print axioms map_xdiag_mem_UDK'
#print axioms map_ymat_mem_UDK'
#print axioms thetaAgreeHypK'_iff
#print axioms map_mem_UDK'_of_sprPsiMonoR
#print axioms sprMatNFixed_le_UDK'_of_zHalf
#print axioms sprMatNFixed_le_UDK'_iff_zHalf
#print axioms sprMatNFixed_le_UDK'_iff_etaAgree
#print axioms thetaAgreeHypK'_iff_zHalf
#print axioms sprXiBasisHypK'
#print axioms sprXiSpanHypK'
#print axioms sprUDKTensorHypK'_of_injective
#print axioms sprE01_sq
#print axioms sprE01_mul_apply
#print axioms mul_sprE01_apply
#print axioms unipotent_diag_entry
#print axioms sprUnipotentUnit_val
#print axioms sprUnipotentUnit_inv
#print axioms constMat_sprE01
#print axioms constMat_sprUnipotentUnit_val
#print axioms constMat_sprUnipotentUnit_inv
#print axioms phiA_sprUnipotentUnit_diag
#print axioms sprEvalOne_X
#print axioms sprEvalOne_ite
#print axioms sprEvalOne_prodX
#print axioms sprEvalOne_phiA_diag
#print axioms prodX_ne_phiA_sprUnipotentUnit
#print axioms sprToS_X_inl
#print axioms not_center_le_pgl_of_zHalf'
#print axioms sprDiagHom_elemSymm
#print axioms sprPermAlgEquiv_elemSymm
#print axioms sprElemSymm_mem_sprNFixed
#print axioms not_zHalf_of_elemSymm_not_mem
#print axioms sprXdiagK_aeval_charpoly
#print axioms diagVietaHypK'
#print axioms charpoly_coeff_mem_sprCenterImageField_of_zHalf'

end SprAxiomAuditSweep

end Procesi








