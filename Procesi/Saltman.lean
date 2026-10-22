/-
  Procesi —— **H2 的源头：Saltman 1999, Ch. 14（`thm:14.17`）的逐字转写**

  ## 源（`raw/` 只读）

  * **印刷版**：`raw/Saltman1999ch14.pdf`（15 页；本件按 L12／L16 以 **PDF** 为准逐字核对，
    抽取页见 `.pscratch/pdf/saltman14.txt`）；
  * **转录版**：`raw/Saltman1999ch14.tex:328–341`。

  逐字（`thm:14.17`）：

  > Let `G = Sₙ`, `H = S_{n−1}` the subgroup fixing `1`. … `ℤ[G/H]` is the free group on
  > `u_i`, `1 ≤ i ≤ n`, and `I[G/H] ⊂ ℤ[G/H]` the sublattice spanned by all `u_i − u_j`.
  > **Set `B` to be the permutation lattice with basis `u_ij`, `1 ≤ i,j ≤ n`, where
  > `σ(u_ij) = u_{σ(i)σ(j)}`.** … There is a `G`-module surjection `B → I[G/H]` given by
  > `u_ij ↦ u_i − u_j`. We define the lattice `M_r` as follows. There is a surjection
  > `⊕_{k=1}^r B → I[G/H]` … Let `Y_r` be the kernel of this map and set
  > `M_r = Y_r ⊕ ℤ[G/H]`.
  > **Theorem 14.17.** `Z(F,n,r) ≅ F(M_r)^{S_n}`.

  ## 印刷版有误（用户裁决 2026-10-18；`raw/Saltman1999ch14.tex` 已更正）

  `thm:14.17` 后的 Remark 说 `trdeg = (r−1)n²+1`；而按印刷的 `M_r = ker(⊕_{k=1}^r B → I) ⊕ ℤ[G/H]`
  计算，`rank M_r = rn² + 1`——**相差 `n²`**。**用户裁决：PDF 该处有误。** 独立佐证：
  `AGPR2020` `cor:14.4.5` 给 `trdeg = (m−1)n²+1`（`m` ＝ 通用矩阵个数），与本工作区
  `finrank_Z_Mp2 = 82`（`n = 9`）一致。
  **更正**（`raw/Saltman1999ch14.tex` 三处，均带 `% [KB 勘误]` 注释；偏差登记于
  `raw/Saltman1999ch14.receipt.json`）：`M_r` 与 `M_r'` 定义中的 `⊕_{k=1}^r B → ⊕_{k=2}^r B`、
  `lem:14.18` 的 `⊕_{k=2}^r B → ⊕_{k=3}^r B`，即 `B` 的份数 ＝ 非对角通用矩阵的个数 `r−1`。
  于是 `r = 2`（＝论文的**两个**通用矩阵）时 `M_2 = ker(B → I[G/H]) ⊕ ℤ[G/H]`，即**一份** `B`，
  `rank M_2 = n²+1 = 82`。" 

  ## 与论文格的关系（本件的机器核对）

  * 论文 `U = ℤ[Ω]` ↔ Saltman `ℤ[G/H]`（两者秩 `n = 9`）；
  * 论文 `U ⊗ U`（基 `e_α ⊗ e_β`）↔ Saltman `B`（基 `u_ij`）——`G.phiFun_single` 逐字给出同一公式；
  * 论文 `φ(e_α ⊗ e_β) = e_α − e_β` ↔ Saltman `u_ij ↦ u_i − u_j`——**同一个映射**；
  * 论文 `M = ker φ` ↔ Saltman `Y_2`（`r = 2` 时的一份 `B` 的核）；
  * **论文 `M ⊕ U` ＝ Saltman `M_2`**（`rfl`；秩 82，`finrank_Z_Mp2`）。

  **⟹ H2 就是 `thm:14.17` 在 `n = 9, r = 2` 的实例**（`procesiS9Hyp_iff_saltman`，`Iff.rfl`）。
  这一层不改 H2 的真假，只把"具名假设"的**文献身份**钉死到可上溯的已发表定理上。
-/
import Procesi.Statement
import Procesi.Lattice

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

universe u

/-! ## §1 Saltman 的格（`n = 9 = p²`、`p = 3`；逐字对应） -/

/-- Saltman 的 `B`：基 `u_ij`、`σ(u_ij) = u_{σ(i)σ(j)}` 的**置换格**。

**与论文的对应**：`B = U ⊗ U`（`U = ℤ[Ω]`），基 `u_ij ↔ e_i ⊗ e_j`；
置换性由 `tensorBasis`（`(Ω × Ω)` 索引）机检。 -/
abbrev BSaltman : Type := G.ZOm 3 ⊗[ℤ] G.ZOm 3

/-- Saltman 的 `ℤ[G/H]`（基 `u_i`）＝论文的 `U = ℤ[Ω]`。 -/
abbrev ZGH : Type := G.ZOm 3

/-- Saltman 的 `I[G/H]`（`u_i − u_j` 张成）＝论文的 `I[Ω] = ker ε`。 -/
abbrev IGH : Type := ↥(G.IOmega 3)

/-- Saltman 的 `G`-模满射 `B → I[G/H]`，`u_ij ↦ u_i − u_j`（＝论文的 `φ`）。 -/
def fSaltman : BSaltman →ₗ[ℤ] G.ZOm 3 := G.phiFun 3

/-- 逐字核对：`fSaltman` 在基上就是 `u_ij ↦ u_i − u_j`。 -/
theorem fSaltman_single (a b : G.OmegaP 3) :
    fSaltman (MonoidAlgebra.single a 1 ⊗ₜ[ℤ] MonoidAlgebra.single b 1)
      = MonoidAlgebra.single a 1 - MonoidAlgebra.single b 1 :=
  G.phiFun_single 3 a b

/-- `fSaltman` 的像是 `I[G/H]`（`range_phiFun_eq`）。 -/
theorem fSaltman_range : LinearMap.range fSaltman = G.IOmega 3 :=
  G.range_phiFun_eq 3

/-- Saltman 的 `Y_2`（`r = 2` 时的核）＝论文的 `M = ker φ`。 -/
abbrev YSaltman : Type := ↥(LinearMap.ker (G.phiFun 3))

/-- ★★ **Saltman 的 `M_2`**（`r = 2`）：`Y_2 ⊕ ℤ[G/H]`。

**与论文的对应**：`M_2 = M ⊕ U`（`rfl`；见 `Mtwo_eq_Mp2`）。 -/
abbrev Mtwo : Type := YSaltman × ZGH

/-- ★ **`M_2` 就是论文的 `M ⊕ U`**（定义相等，`rfl`）。 -/
theorem Mtwo_eq_Mp2 : Mtwo = ProcLat.Mp2 3 := rfl

/-- ★ **秩账**：`rank M_2 = n² + 1 = 82`（`n = 9`）——与 Saltman 的 Remark `(r−1)n²+1`（`r = 2`）
及 `AGPR2020` `cor:14.4.5`（`m = 2`）一致。 -/
theorem rank_Mtwo : Module.finrank ℤ Mtwo = 82 := finrank_Z_Mp2

/-! ## §2 `thm:14.17` 在 `(n, r) = (9, 2)` 的逐字形 -/

/-- **Saltman `thm:14.17`（`n = 9, r = 2`）的逐字形**：
`Z(F,9,2) ≅ F(M_2)^{S_9}`，其中 `M_2` 是 Saltman 的格（`= M ⊕ U`，§1）。

`Z` ＝ `Z(F,9,2)`（两个通用矩阵的通用除法代数的中心的分式域），以抽象域参数传入
——**构造它**正是 `thm:14.4.4`／`thm:14.16` 那一层的内容（见 `wiki/proj-ABGV52-procesi-campaign` 的待办）。 -/
def SaltmanThm1417At9 (F : Type u) [Field F] (Z : Type u) [Field Z] [Algebra F Z] : Prop :=
  Nonempty (Z ≃ₐ[F] ↥(EM.latticeInvariantsAlg F S9 Mtwo))

/-- ★★★ **H2 ＝ `thm:14.17` 的 `(9,2)` 实例**（两者是**同一个命题**）：本工作区的
`ProcesiS9Hyp` 与 Saltman 的 `thm:14.17`（`n = 9`, `r = 2`）**逐字相同**。 -/
theorem procesiS9Hyp_iff_saltman (F : Type u) [Field F] (Z : Type u) [Field Z]
    [Algebra F Z] :
    ProcesiS9Hyp F Z ↔ SaltmanThm1417At9 F Z := Iff.rfl

/-- 类型锁：`SaltmanThm1417At9` 的外形。 -/
theorem saltmanThm1417At9_typeLock (F : Type u) [Field F] (Z : Type u) [Field Z]
    [Algebra F Z] :
    (SaltmanThm1417At9 F Z)
      = Nonempty (Z ≃ₐ[F] ↥(EM.latticeInvariantsAlg F S9 Mtwo)) := rfl

/-! ## §3 公理闸门 -/

#print axioms fSaltman_single
#print axioms fSaltman_range
#print axioms Mtwo_eq_Mp2
#print axioms rank_Mtwo
#print axioms procesiS9Hyp_iff_saltman
#print axioms saltmanThm1417At9_typeLock

end

end Procesi
