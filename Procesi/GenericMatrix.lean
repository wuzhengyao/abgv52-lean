/-
  Procesi —— **D4 前置（第一层）**：通用矩阵代数 `R = F⟨ξ₁,…,ξ_r⟩` 的定义 ＋ 库内桥

  **本件的射程（勿夸大）**：只给 D4（Saltman `thm:14.16`＝(A)／`prop:14.19`＝(B)）的
  **定义层与库内桥**，**不**证明 (A)／(B)。D4 的裁决（可行性、缺口、解除动作）见
  `wiki/proj-D4-procesi-center-recon.md`。

  **为何需要这些定义**：Saltman `thm:14.16` 的对象是
  `Z(F,n,r) = C(Q(R))`（通用除环的中心），而 `R = F{X} ⊆ M_n(F(x_{ij}^k))` 是**通用矩阵环**
  （`raw/Formanek2002.tex` §"Rings related to the ring of `n×n` generic matrices" 逐字：
  > They are all `K`-subalgebras of `M_n(K(x_{ij}^k))`, and their centers are all `K`-subalgebras
  > of `K(x_{ij}^k)`, where `α ∈ K(x_{ij}^k)` is identified with the scalar matrix `α·I`.
  > These rings are: `R = K{X}`, the ring of generic matrices; `C(R)`, the center of `R`; …；
  > `Q(R)`, the generic division ring; `C(Q(R))`, the center of `Q(R)`.）
  故构造 `Z(F,n,r)` 的第一步就是本件的 `genericMatrixAlgebra` 与 `genericCenter`。

  **库内桥（有限维代数中心）**：`M_n(R)`（`R` 交换）的中心**作为子代数**恰是纯量矩阵
  （＝ `⊥`）。mathlib 只给**集合层**（`Matrix.center_eq_range`）；本件把它升成
  `Subalgebra` 层，供 (A) 的「中心 ⊆ 纯量」一步消费。

  **⚠ D4 的真正障碍（本件**不**解决，见 recon 件）**：
  1. `Z(F,n,r) = Frac(C(R))` 需 **中心多项式**（Formanek 1972／Razmyslov 1973；
     `raw/Formanek2002.tex` 同段逐字：「`C(Q(R))` is the field of quotients of `C(R)`」）
     ——mathlib 本 pin **无** PI 理论（内容式检索 `PolynomialIdentity` 命中 0）；
  2. `R` 是**域**（Amitsur 1955）——同样依赖 PI 理论；
  3. `Q(R)` 是**非交换** Ore 局部化（mathlib 有 `OreLocalization` 与 `OreSet`，但**无**
     「域的 Ore 商除环」实例化）；
  4. `(A)` 的 `PGL_n(F)`-作用与 `lem:14.13`／`thm:14.15`、`(B)` 的 `lem:14.21–14.25`
     均为研究级论证；
  5. `UD(F,n,H)` 的**定义**在 `ABGV2011` §5，而该来源**不在 `raw/`**（材料缺口）。
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace Procesi

open Matrix

/-! ## §1 通用矩阵与通用矩阵代数 `R = F⟨ξ₁,…,ξ_r⟩` -/

variable (F : Type) [Field F]

/-- 第 `k` 个 `n×n` 通用矩阵的 `(i,j)` 元：`F` 上的不定元 `x^{k}_{ij}`。 -/
noncomputable def genericEntry (r n : ℕ) (k : Fin r) (i j : Fin n) :
    MvPolynomial (Fin r × Fin n × Fin n) F :=
  MvPolynomial.X ⟨k, i, j⟩

/-- 第 `k` 个 `n×n` **通用矩阵** `ξ_k`（元素在多项式环 `F[x]` 中）。 -/
noncomputable def genericMatrix (r n : ℕ) (k : Fin r) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F) :=
  fun i j => genericEntry F r n k i j

/-- ★ **通用矩阵代数** `R = F⟨ξ₁,…,ξ_r⟩`：由 `r` 个通用矩阵生成的 `F`-子代数
（`F`-系数非交换多项式在 `M_n(F[x])` 中的像）。

**与 Formanek 的对应**：`raw/Formanek2002.tex` 的 `R = K{X}`（"the ring of generic matrices"）。 -/
noncomputable def genericMatrixAlgebra (r n : ℕ) :
    Subalgebra F (Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F)) :=
  Algebra.adjoin F (Set.range (genericMatrix F r n))

/-- 每个通用矩阵都在 `R` 里（生成的起点）。 -/
lemma genericMatrix_mem (r n : ℕ) (k : Fin r) :
    genericMatrix F r n k ∈ genericMatrixAlgebra F r n :=
  Algebra.subset_adjoin (Set.mem_range_self k)

/-- 纯量矩阵（`algebraMap F` 的像）在 `R` 里。 -/
lemma algebraMap_mem_genericMatrixAlgebra (r n : ℕ) (c : F) :
    algebraMap F (Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F)) c
      ∈ genericMatrixAlgebra F r n :=
  Subalgebra.algebraMap_mem _ c

/-- **归纳原理**：要证 `R` 中所有元素满足 `p`，只需证 `p` 对生成元、`algebraMap`、
加法与乘法封闭（`Algebra.adjoin_induction` 的直接转写）。 -/
theorem genericMatrixAlgebra_induction (r n : ℕ)
    {p : (x : Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F)) →
      x ∈ genericMatrixAlgebra F r n → Prop}
    (mem : ∀ (x : Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F))
      (hx : x ∈ Set.range (genericMatrix F r n)), p x (Algebra.subset_adjoin hx))
    (alg : ∀ c : F, p (algebraMap F _ c) (algebraMap_mem_genericMatrixAlgebra F r n c))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Subalgebra.add_mem _ hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (Subalgebra.mul_mem _ hx hy))
    {x : Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F)}
    (hx : x ∈ genericMatrixAlgebra F r n) : p x hx :=
  Algebra.adjoin_induction mem alg add mul hx

/-! ## §2 中心 `C(R)` -/

/-- ★ **通用矩阵代数的中心** `C(R)`：`Subalgebra.center`（`C(R) = {a ∈ R | ∀ b ∈ R, ab = ba}`）。 -/
noncomputable abbrev genericCenter (r n : ℕ) : Subalgebra F ↥(genericMatrixAlgebra F r n) :=
  Subalgebra.center F ↥(genericMatrixAlgebra F r n)

/-- `C(R)` 的成员刻画：与 `R` 的所有元素交换。 -/
lemma mem_genericCenter_iff (r n : ℕ) {A : ↥(genericMatrixAlgebra F r n)} :
    A ∈ genericCenter F r n ↔ ∀ B : ↥(genericMatrixAlgebra F r n), B * A = A * B :=
  Subalgebra.mem_center_iff

/-- 中心的元素与每个通用矩阵交换（"中心 ⊆ 各生成元的换位子零"）。 -/
lemma commute_genericMatrix_of_mem_genericCenter (r n : ℕ) {A : ↥(genericMatrixAlgebra F r n)}
    (hA : A ∈ genericCenter F r n) (k : Fin r) :
    (⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩ : ↥(genericMatrixAlgebra F r n)) * A
      = A * ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩ :=
  (Subalgebra.mem_center_iff.mp hA) _

/-- 纯量在中心里（`F` 的中心性）：`⊥ ≤ C(R)`。 -/
lemma bot_le_genericCenter (r n : ℕ) :
    (⊥ : Subalgebra F ↥(genericMatrixAlgebra F r n)) ≤ genericCenter F r n := by
  intro A hA
  rw [Algebra.mem_bot] at hA
  obtain ⟨c, rfl⟩ := hA
  exact Subalgebra.algebraMap_mem _ c

#print axioms genericEntry
#print axioms genericMatrix
#print axioms genericMatrixAlgebra
#print axioms genericMatrix_mem
#print axioms algebraMap_mem_genericMatrixAlgebra
#print axioms genericMatrixAlgebra_induction
#print axioms genericCenter
#print axioms mem_genericCenter_iff
#print axioms commute_genericMatrix_of_mem_genericCenter
#print axioms bot_le_genericCenter

/-! ## §3 库内桥（有限维代数中心）：`M_n(R)` 的中心 = 纯量矩阵

mathlib 的 `Matrix.center_eq_range` 是**集合层**：`Set.center (Matrix n n R) = Set.range (scalar n)`。
本节把它升成 **`Subalgebra` 层**：`Subalgebra.center R (Matrix n n R) = ⊥`
（`⊥` 的载体正是 `algebraMap` 的像 ＝ 纯量矩阵）。这是 (A) 里「中心 ⊆ 纯量」那一步
在**有限维（`R` 交换）情形**的可用件。 -/

section MatrixCenter

variable (R : Type) [CommSemiring R] (n : ℕ)

/-- ★★ **库内桥**：`M_n(R)` 的中心**作为子代数**等于纯量矩阵子代数（`⊥`）。 -/
theorem matrixCenter_eq_bot :
    Subalgebra.center R (Matrix (Fin n) (Fin n) R) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro M hM
  rw [Subalgebra.mem_center_iff] at hM
  have hrange : M ∈ Set.range (scalar (Fin n) : R → Matrix (Fin n) (Fin n) R) :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr (fun i j => hM (Matrix.single i j 1))
  obtain ⟨r, rfl⟩ := hrange
  rw [Algebra.mem_bot]
  exact ⟨r, rfl⟩

/-- 中心的元素必是纯量矩阵（(A) 的「中心 ⊆ 纯量」在有限维情形的**可用形式**）。 -/
theorem exists_eq_scalar_of_mem_matrixCenter {M : Matrix (Fin n) (Fin n) R}
    (hM : M ∈ Subalgebra.center R (Matrix (Fin n) (Fin n) R)) :
    ∃ r : R, M = scalar (Fin n) r := by
  have h := matrixCenter_eq_bot R n
  rw [h, Algebra.mem_bot] at hM
  obtain ⟨r, hr⟩ := hM
  exact ⟨r, hr.symm⟩

#print axioms matrixCenter_eq_bot
#print axioms exists_eq_scalar_of_mem_matrixCenter

end MatrixCenter

end Procesi
