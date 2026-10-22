/-
  Procesi —— **PI 基础设施（S1）：Formanek 中心多项式的"交换伴随"**

  **来源（逐字）**：`raw/AGPR2020.tex` §10.2（"Central polynomials"）：
  * 定义（tex `:12028`）：中心多项式 ＝ 无常数项的非交换多项式，在 `n×n` 矩阵上**只取纯量值**
    且**不恒零**；
  * 构造（tex `eq:10.4`）：对交换多项式
    `g(x_0,…,x_N) = Σ_m c_m x_0^{m_0} ⋯ x_N^{m_N}` 令
    `ḡ(X, Y_0, …, Y_{N-1}) := Σ_m c_m · X^{m_0} Y_0 X^{m_1} ⋯ Y_{N-1} X^{m_N}`；
  * 判据（`lem:10.2.3`）与主定理（`thm:10.2.4`）见施工图
    [[proj-abgv52-pi-infra-plan-2026-10-22]]（S2–S4）。

  **本件内容（S1）**：`wordOf`（单项词，`eq:10.4` 的被加项）＋ `formanekEval`（`eq:10.4`）
  ＋ 两条对角律（`diagonal_mul_single`／`diagonal_pow_mul_single`，`eq:10.3` 的原子步）。

  **⚠ 载体状态（L12）**：本条陈述取自 `raw/AGPR2020.tex`（用户由 PDF 转化）；**印刷页尚未目视核**
  ⟹ 标 `⚠-tex-sourced`，引用定案前须按 L12／L39 回 `raw/AGPR2020.pdf` 核陈述完整性。
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.MvPolynomial.Basic

namespace Procesi

open Matrix

variable {K : Type*} [CommRing K]

/-- 对角矩阵乘矩阵单位：`diag x * E_{pq}(r) = E_{pq}(x p * r)`（`eq:10.3` 的原子步）。 -/
theorem diagonal_mul_single {N : ℕ} (x : Fin N → K) (p q : Fin N) (r : K) :
    Matrix.diagonal x * Matrix.single p q r = Matrix.single p q (x p * r) := by
  ext a b
  simp only [Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne, Matrix.diagonal_apply,
    Matrix.single, Matrix.of_apply]
  by_cases hb : b = q
  · subst hb
    by_cases ha : a = p
    · subst ha; simp
    · simp [ha, Ne.symm ha]
  · simp [hb, Ne.symm hb]

#print axioms diagonal_mul_single

/-- 对角幂乘矩阵单位：`(diag x)^a * E_{pq}(r) = E_{pq}((x p)^a * r)`。 -/
theorem diagonal_pow_mul_single {N : ℕ} (x : Fin N → K) (a : ℕ) (p q : Fin N) (r : K) :
    Matrix.diagonal x ^ a * Matrix.single p q r = Matrix.single p q ((x p) ^ a * r) := by
  induction a generalizing r with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, diagonal_mul_single, ih, ← mul_assoc, ← pow_succ]

#print axioms diagonal_pow_mul_single

/-- **单项词**（AGPR `eq:10.4` 的被加项），**ℕ-索引**左折叠：
`∏_{k<N} (X^{n k} · Y_k) · X^{n N}`。

**为何 ℕ-索引而非 `Fin (N+1)`-索引**：`Fin (N+1)`-索引做归纳会撞"类型随 `N` 变化"；
ℕ-索引让链式求值（`ChainProd.wordOfNat_chain`）的归纳落回 `ℕ`（R741–R742 实测）。 -/
noncomputable def wordOf (N : ℕ) (n : ℕ → ℕ) (X : Matrix (Fin N) (Fin N) K)
    (Y : Fin N → Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  ((List.range N).map (fun k =>
    if h : k < N then X ^ (n k) * Y ⟨k, h⟩ else 1)).prod * X ^ (n N)

/-- **Formanek 的交换伴随**（AGPR `eq:10.4`）：把交换多项式 `g` 的每个单项
`c · x_0^{m_0}⋯x_N^{m_N}` 送到 `c • (X^{m_0} Y_0 ⋯ Y_{N-1} X^{m_N})`。 -/
noncomputable def formanekEval (N : ℕ) (g : MvPolynomial (Fin (N + 1)) K)
    (X : Matrix (Fin N) (Fin N) K) (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    Matrix (Fin N) (Fin N) K :=
  ∑ m ∈ g.support, g.coeff m •
    wordOf N (fun k => if h : k < N + 1 then m ⟨k, h⟩ else 0) X Y

end Procesi
