/-
  Procesi —— ★★★★★ **`hspan` 的数值层（L1 的实质部分）**：`R·K = M_n(K)` 的**独立性**

  **目标**（[[deadend-genericCenter-eq-F]] §3 的路线 A，喂 `Cor148.lean`）：
  ```
  hspan : Algebra.adjoin (SField F 2 n) (range (fun k : Fin 2 => (genericMatrix F 2 n k).map ι)) = ⊤
  ```
  本件机检**数值独立层**（L1 的"唯一实质"部分），`hspan` 本身在下一件（`L1d`：LI ⟹ span ⟹ adjoin）。

  **路线**（避开 Saltman 的循环代数特化，改用"一个点上的基"）：
  1. 取 `n²` 个词 `W_ij := X₀^i · X₁ · X₀^j`（`i j : Fin n`），矩阵 `phiS`（行 `(i,j)`、列 `(p,q)`）；
  2. **特化** `evalAt : S →ₐ[F] F`：`x_{0,p,q} ↦ δ_{pq}·(p : F)`、`x_{1,p,q} ↦ 1`，
     即 `X₀ ↦ diagonal (λ : p ↦ p)`、`X₁ ↦ J`（全 1）；
  3. 特化后 `(phiS).map evalAt` 的 `((i,j),(p,q))` 元 = `λ_p^i · λ_q^j`
     （`phiS_map_evalAt` ＋ `diag_mul_one_mul_diag`）；
  4. 该矩阵 = `Vᵀ ⊗ₖ Vᵀ`（`V` = Vandermonde），`det = (det V)^{2·n²} ≠ 0`
     （`det_kronecker` ＋ `det_vandermonde_ne_zero_iff`，`λ` 单射用 `CharZero`）；
  5. **det 转移**：`evalAt (det phiS) = det (phiS.map evalAt) ≠ 0` ⟹ `det phiS ≠ 0`（`S` 是整环）。

  **⟹ 已机检**：`psi`／`psi_apply`／`det_psi_ne_zero`／`wWord`／`phiS`／`phiS_map_evalAt`／
  `det_phiS_ne_zero`（全部零 `sorryAx`）。
  **⟹ 后续（已完成）**：`det (phiS.map ι) ≠ 0` 与 `hspan` 已于 R779 在
  `Nonvacuous.det_phiS_map_ne_zero`／`adjoin_genericMatrix_map_eq_top` 机检——
  **不**走 `LinearIndependent`（`SField = OreLocalization` 的实例菱形会使 mathlib 的 LI 引理
  与本仓陈述类型不同），改走**矩阵求逆**（`M⁻¹ * M = 1` ⟹ 矩阵单位是行的 `K`-组合）。
  终局：`Nonvacuous.nonempty_genericDivisionData_two_nine`／`h2_unconditional_nonvacuous`。
-/

import Procesi.Cor148
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Matrix
open scoped Kronecker

namespace Procesi

variable (F : Type) [Field F]

/-- `λ p = (p : F)`（`Fin n → F`）。 -/
def lam (n : ℕ) : Fin n → F := fun p => ((p.val : ℕ) : F)

#print axioms lam

theorem lam_injective [CharZero F] (n : ℕ) : Function.Injective (lam F n) := by
  intro p q h
  simp only [lam] at h
  have h' : (p.val : ℕ) = (q.val : ℕ) := Nat.cast_injective h
  exact Fin.ext h'

#print axioms lam_injective

/-- `diagonal a * J * diagonal b` 的逐项公式（`J` = 全 1 矩阵）。 -/
lemma diag_mul_one_mul_diag (n : ℕ) (i j : Fin n) (p q : Fin n) :
    ((Matrix.diagonal (lam F n ^ i.val) : Matrix (Fin n) (Fin n) F)
      * (Matrix.of (fun _ _ => (1 : F)) : Matrix (Fin n) (Fin n) F)
      * (Matrix.diagonal (lam F n ^ j.val) : Matrix (Fin n) (Fin n) F)) p q
      = lam F n p ^ i.val * lam F n q ^ j.val := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, mul_one]
  simp only [Pi.pow_apply]

#print axioms diag_mul_one_mul_diag

/-- 特化：`x_{0,p,q} ↦ if p = q then (p : F) else 0`；`x_{1,p,q} ↦ 1`。 -/
noncomputable def evalAt (n : ℕ) : S F 2 n →ₐ[F] F :=
  MvPolynomial.aeval (fun p : Fin 2 × Fin n × Fin n =>
    if p.1 = 0 then (if p.2.1 = p.2.2 then ((p.2.1).val : F) else 0) else 1)

#print axioms evalAt

theorem genericMatrix_map_evalAt_zero (n : ℕ) :
    (genericMatrix F 2 n 0).map (evalAt F n)
      = Matrix.diagonal (lam F n) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.map_apply, genericMatrix, genericEntry, evalAt, Matrix.diagonal, lam]
  · simp [Matrix.map_apply, genericMatrix, genericEntry, evalAt, Matrix.diagonal, hij, lam]

#print axioms genericMatrix_map_evalAt_zero

theorem genericMatrix_map_evalAt_one (n : ℕ) :
    (genericMatrix F 2 n 1).map (evalAt F n) = Matrix.of (fun _ _ => (1 : F)) := by
  ext i j
  simp [Matrix.map_apply, genericMatrix, genericEntry, evalAt]

#print axioms genericMatrix_map_evalAt_one

/-- 数值矩阵 `Ψ (i,j) (p,q) = λ_p^i · λ_q^j`（两个 Vandermonde 的 Kronecker 积）。 -/
noncomputable def psi (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) F :=
  (Matrix.vandermonde (lam F n))ᵀ ⊗ₖ (Matrix.vandermonde (lam F n))ᵀ

#print axioms psi

theorem psi_apply (n : ℕ) (i j p q : Fin n) :
    psi F n (i, j) (p, q) = (lam F n p) ^ i.val * (lam F n q) ^ j.val := by
  simp [psi, Matrix.kronecker_apply, Matrix.transpose_apply, Matrix.vandermonde]

#print axioms psi_apply

theorem det_psi_ne_zero [CharZero F] (n : ℕ) : (psi F n).det ≠ 0 := by
  have hV : (Matrix.vandermonde (lam F n)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (lam_injective F n)
  rw [psi, Matrix.det_kronecker, Matrix.det_transpose]
  exact mul_ne_zero (pow_ne_zero _ hV) (pow_ne_zero _ hV)

#print axioms det_psi_ne_zero



/-- `W_ij := X₀^i · X₁ · X₀^j`（Saltman `Ξ` 的 Lean 形态，`L1` 的张成族）。 -/
noncomputable def wWord (n : ℕ) (i j : Fin n) : Matrix (Fin n) (Fin n) (S F 2 n) :=
  (genericMatrix F 2 n 0) ^ i.val * genericMatrix F 2 n 1 * (genericMatrix F 2 n 0) ^ j.val

#print axioms wWord

/-- 结构矩阵：行索引 `(i,j)`，列索引 `(p,q)`，元素 `(W_ij) p q`。 -/
noncomputable def phiS (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) (S F 2 n) :=
  fun ij pq => wWord F n ij.1 ij.2 pq.1 pq.2

#print axioms phiS

theorem phiS_map_evalAt (n : ℕ) :
    (phiS F n).map (evalAt F n) = psi F n := by
  ext ij pq
  obtain ⟨i, j⟩ := ij
  obtain ⟨p, q⟩ := pq
  rw [Matrix.map_apply, psi_apply]
  have h1 : (wWord F n i j).map (evalAt F n)
      = ((genericMatrix F 2 n 0).map (evalAt F n)) ^ i.val
        * ((genericMatrix F 2 n 1).map (evalAt F n))
        * ((genericMatrix F 2 n 0).map (evalAt F n)) ^ j.val := by
    have hp1 : ((genericMatrix F 2 n 0) ^ i.val).map ⇑(evalAt F n)
        = ((genericMatrix F 2 n 0).map ⇑(evalAt F n)) ^ i.val :=
      Matrix.map_pow (genericMatrix F 2 n 0) (evalAt F n).toRingHom i.val
    have hp2 : ((genericMatrix F 2 n 0) ^ j.val).map ⇑(evalAt F n)
        = ((genericMatrix F 2 n 0).map ⇑(evalAt F n)) ^ j.val :=
      Matrix.map_pow (genericMatrix F 2 n 0) (evalAt F n).toRingHom j.val
    simp only [wWord, Matrix.map_mul, hp1, hp2]
  show (wWord F n i j).map (evalAt F n) p q = _
  rw [h1, genericMatrix_map_evalAt_zero, genericMatrix_map_evalAt_one,
    Matrix.diagonal_pow, Matrix.diagonal_pow]
  exact diag_mul_one_mul_diag F n i j p q

#print axioms phiS_map_evalAt

theorem det_phiS_ne_zero [CharZero F] (n : ℕ) : (phiS F n).det ≠ 0 := by
  intro h
  have h2 : (evalAt F n) ((phiS F n).det) = 0 := by rw [h, map_zero]
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, phiS_map_evalAt] at h2
  exact det_psi_ne_zero F n h2

#print axioms det_phiS_ne_zero

end Procesi
