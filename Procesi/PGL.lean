/-
  Procesi —— **(A)+(B) 形式化 S1：`PGL_n(F)` 在 `S`／`M_n(S)` 上的作用**

  **来源（逐字，label 引用；L41）**：`raw/Saltman1999ch14.tex`，§「We begin with the definition
  and basic properties of `PGL_n(F)`」段：
  > Let `A ∈ GL_n(F)`. Define `φ_A : S → S` by setting `φ_A(x_{ijk})` to be the `i,j` entry of
  > the matrix `A^{-1} X_k A`. … `A^{-1}X_kA = M_n(φ_A)(X_k)` (16) … `φ_B ∘ φ_A = φ_{BA}` …
  > Define `ψ_B : M_n(S) → M_n(S)` by `ψ_B(Y) = B (M_n(φ_B)(Y)) B^{-1}` … `ψ_B ψ_A = ψ_{BA}`.

  **约定（照原文，勿再犹豫；曾改错一次并已纠正）**：本件取 Saltman 的约定
  `φ_A(x_{ijk}) = (A⁻¹ X_k A)_{ij}`、`ψ_A(Y) = A · M_n(φ_A)(Y) · A⁻¹`，于是
  **`φ_B ∘ φ_A = φ_{BA}`、`ψ_B ∘ ψ_A = ψ_{BA}`**（对 `A` 是**反**同态，即右作用）。
  **动作**取左作用形：`A ↦ φ_{A⁻¹}`（`A ↦ A⁻¹` 是群双射，固定点集不变）。
  **为何不能用"同态"约定**（第一版曾用 `φ_A = (A X A⁻¹)`，已废弃）：那样
  `φ_B∘φ_A = φ_{AB}`，但 `ψ_B(ψ_A(Y)) = BA · Y.map φ_{AB} · (BA)⁻¹` ——**常数因子是 `BA`、
  替换是 `φ_{AB}`，两者下标不一致**，`ψ` 的复合律无法写成 `ψ_{?}`；而原文的（反）约定下
  两者一致（`BA` 与 `φ_{BA}`），`ψ_B∘ψ_A = ψ_{BA}` 成立。**这是必须照原文的地方。**

  **本件的射程**：**S1 的代数层 ＋ S2 的 `ψ` 层**——`φ_A`（`AlgHom`）、源文 `(16)`、
  余圈 `φ_B∘φ_A = φ_{BA}`、`ψ_A`（`M_n(S)` 的环自同态）及其余圈 `ψ_B∘ψ_A = ψ_{BA}`。
  **未做**（后续阶段）：`GL_n` 的 `MulSemiringAction` 打包、`PGL_n` 商、延到 `K`／`M_n(K)`、
  `lem:14.12`–`thm:14.16`、`prop:14.19`。施工单见 `wiki/proj-AB-formalization-plan.md`。
-/
import Procesi.GenericMatrix
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.NoncommRing

open Matrix

namespace Procesi

noncomputable section

set_option maxHeartbeats 1600000

variable (F : Type) [Field F] (r n : ℕ)

/-- 多项式环 `S = F[x_{ijk}]`（`r` 份通用矩阵的条目）。 -/
abbrev S (F : Type) [CommSemiring F] (r n : ℕ) := MvPolynomial (Fin r × Fin n × Fin n) F

/-- 常矩阵 `A : M_n(F)` 在 `M_n(S)` 中的像。 -/
noncomputable def constMat (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) (S F r n) :=
  A.map (algebraMap F (S F r n))

/-- `φ_A` 在不定元上的值：`x_{ijk} ↦ (A X_k A^{-1})_{ij}`（同态约定，见文件头）。 -/
noncomputable def phiGen (A : (Matrix (Fin n) (Fin n) F)ˣ) (e : Fin r × Fin n × Fin n) : S F r n :=
  (constMat F r n (↑A⁻¹) * genericMatrix F r n e.1 * constMat F r n (↑A)) e.2.1 e.2.2

/-- ★ **`φ_A : S →ₐ[F] S`**（`A ∈ GL_n(F)`，源文 `φ_A(x_{ijk}) = (A⁻¹X_kA)_{ij}`）。
**互逆**：`φ_{A⁻¹} ∘ φ_A = φ_1 = id`（`phiA_comp` ＋ `phiA_one`）。 -/
noncomputable def phiA (A : (Matrix (Fin n) (Fin n) F)ˣ) : S F r n →ₐ[F] S F r n :=
  MvPolynomial.aeval (phiGen F r n A)

/-- ★★ **源文 `(16)`**：`M_n(φ_A)(X_k) = A X_k A^{-1}`。 -/
lemma phiA_X (A : (Matrix (Fin n) (Fin n) F)ˣ) (k : Fin r) :
    (genericMatrix F r n k).map (phiA F r n A)
      = constMat F r n (↑A⁻¹) * genericMatrix F r n k * constMat F r n (↑A) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  show MvPolynomial.aeval (phiGen F r n A) (MvPolynomial.X ⟨k, i, j⟩)
      = (constMat F r n (↑A⁻¹) * genericMatrix F r n k * constMat F r n (↑A)) i j
  rw [MvPolynomial.aeval_X]
  rfl

/-- `φ_A` 固定常矩阵（`A` 的条目在 `F` 里）。 -/
lemma constMat_map (A : (Matrix (Fin n) (Fin n) F)ˣ) (C : Matrix (Fin n) (Fin n) F) :
    (constMat F r n C).map (phiA F r n A) = constMat F r n C := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  show phiA F r n A (algebraMap F (S F r n) (C i j)) = algebraMap F (S F r n) (C i j)
  exact (phiA F r n A).commutes _

/-- `constMat 1 = 1`。 -/
lemma constMat_one : constMat F r n (1 : Matrix (Fin n) (Fin n) F) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- `constMat` 是环同态（矩阵乘法的 `map`）。 -/
lemma constMat_mul (C D : Matrix (Fin n) (Fin n) F) :
    constMat F r n (C * D) = constMat F r n C * constMat F r n D :=
  Matrix.map_mul

/-- `φ_B` 穿过常矩阵（左右夹的常矩阵被固定）。 -/
lemma map_mul_constMat (B : (Matrix (Fin n) (Fin n) F)ˣ)
    (C D : Matrix (Fin n) (Fin n) F) (k : Fin r) :
    (constMat F r n C * genericMatrix F r n k * constMat F r n D).map (phiA F r n B)
      = constMat F r n C * (genericMatrix F r n k).map (phiA F r n B) * constMat F r n D := by
  rw [Matrix.map_mul, Matrix.map_mul, constMat_map, constMat_map]

/-- 逐元形式：`φ_B((C X_k D)_{ij}) = (C · (X_k.map φ_B) · D)_{ij}`。 -/
lemma phiA_apply_entry (B : (Matrix (Fin n) (Fin n) F)ˣ)
    (C D : Matrix (Fin n) (Fin n) F) (k : Fin r) (i j : Fin n) :
    phiA F r n B ((constMat F r n C * genericMatrix F r n k * constMat F r n D) i j)
      = (constMat F r n C * (genericMatrix F r n k).map (phiA F r n B) * constMat F r n D) i j := by
  have h : ((constMat F r n C * genericMatrix F r n k * constMat F r n D).map
      (phiA F r n B)) i j
      = phiA F r n B ((constMat F r n C * genericMatrix F r n k * constMat F r n D) i j) :=
    Matrix.map_apply
  rw [map_mul_constMat] at h
  exact h.symm

/-- `φ_A` 在不定元上的展开式（`phiGen` 的 `AlgHom` 版）。 -/
lemma phiA_var (A : (Matrix (Fin n) (Fin n) F)ˣ) (k : Fin r) (i j : Fin n) :
    phiA F r n A (MvPolynomial.X ⟨k, i, j⟩)
      = (constMat F r n (↑A⁻¹) * genericMatrix F r n k * constMat F r n (↑A)) i j := by
  rw [phiA, MvPolynomial.aeval_X]
  rfl

/-- ★★ **余圈（照原文，反同态）**：`φ_B ∘ φ_A = φ_{B*A}`。 -/
lemma phiA_comp (A B : (Matrix (Fin n) (Fin n) F)ˣ) :
    (phiA F r n B).comp (phiA F r n A) = phiA F r n (B * A) := by
  apply MvPolynomial.algHom_ext
  intro e
  obtain ⟨k, i, j⟩ := e
  rw [AlgHom.comp_apply, phiA_var, phiA_apply_entry, phiA_X, phiA_var]
  refine congrArg (fun M : Matrix (Fin n) (Fin n) (S F r n) => M i j) ?_
  have hv : (↑(B * A) : Matrix (Fin n) (Fin n) F) =
      (↑B : Matrix (Fin n) (Fin n) F) * (↑A : Matrix (Fin n) (Fin n) F) := Units.val_mul B A
  have hi : (↑((B * A)⁻¹) : Matrix (Fin n) (Fin n) F) =
      (↑A⁻¹ : Matrix (Fin n) (Fin n) F) * (↑B⁻¹ : Matrix (Fin n) (Fin n) F) := by
    rw [mul_inv_rev, Units.val_mul]
  rw [hv, hi, constMat_mul, constMat_mul]
  noncomm_ring

/-- `φ_1 = id`。 -/
lemma phiA_one : phiA F r n (1 : (Matrix (Fin n) (Fin n) F)ˣ) = AlgHom.id F (S F r n) := by
  apply MvPolynomial.algHom_ext
  intro e
  obtain ⟨k, i, j⟩ := e
  rw [AlgHom.id_apply, phiA_var, Units.val_one, inv_one, Units.val_one,
    constMat_one, one_mul, mul_one]
  rfl

#print axioms phiA
#print axioms phiA_X
#print axioms constMat_map
#print axioms constMat_one
#print axioms constMat_mul
#print axioms map_mul_constMat
#print axioms phiA_apply_entry
#print axioms phiA_var
#print axioms phiA_comp
#print axioms phiA_one

/-! ## `ψ_A`：`M_n(S)` 上的环自同态 -/

/-- 共轭是乘性的（给 `D * C = 1`）。 -/
lemma conj_mul {C D : Matrix (Fin n) (Fin n) (S F r n)} (h : D * C = 1)
    (Y Z : Matrix (Fin n) (Fin n) (S F r n)) :
    C * (Y * Z) * D = (C * Y * D) * (C * Z * D) := by
  have key : C * Y * (D * C) * Z * D = C * (Y * Z) * D := by
    rw [h, mul_one]
    noncomm_ring
  rw [← key]
  noncomm_ring

/-- ★ **`ψ_A : M_n(S) →+* M_n(S)`**，`ψ_A(Y) = A · M_n(φ_A)(Y) · A⁻¹`（源文定义）。 -/
noncomputable def psiA (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    Matrix (Fin n) (Fin n) (S F r n) →+* Matrix (Fin n) (Fin n) (S F r n) where
  toFun Y := constMat F r n (↑A) * Y.map (phiA F r n A) * constMat F r n (↑A⁻¹)
  map_one' := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one, ← constMat_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, constMat_one]
  map_mul' Y Z := by
    rw [Matrix.map_mul]
    have h : constMat F r n (↑A⁻¹) * constMat F r n (↑A) = 1 := by
      rw [← constMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, constMat_one]
    have key : constMat F r n (↑A) * Y.map (phiA F r n A) *
        (constMat F r n (↑A⁻¹) * constMat F r n (↑A)) * Z.map (phiA F r n A) *
          constMat F r n (↑A⁻¹)
        = constMat F r n (↑A) * (Y.map (phiA F r n A) * Z.map (phiA F r n A)) *
          constMat F r n (↑A⁻¹) := by
      rw [h, mul_one]
      noncomm_ring
    rw [← key]
    noncomm_ring
  map_zero' := by
    rw [Matrix.map_zero _ (map_zero _)]
    simp
  map_add' Y Z := by
    rw [Matrix.map_add (phiA F r n A) (fun a b => map_add _ _ _) Y Z]
    noncomm_ring

lemma psiA_apply (A : (Matrix (Fin n) (Fin n) F)ˣ) (Y : Matrix (Fin n) (Fin n) (S F r n)) :
    psiA F r n A Y = constMat F r n (↑A) * Y.map (phiA F r n A) * constMat F r n (↑A⁻¹) := rfl

/-- ★★ **余圈（照原文）**：`ψ_B ∘ ψ_A = ψ_{B*A}`。 -/
lemma psiA_comp (A B : (Matrix (Fin n) (Fin n) F)ˣ) :
    (psiA F r n B).comp (psiA F r n A) = psiA F r n (B * A) := by
  apply RingHom.ext
  intro Y
  rw [RingHom.comp_apply, psiA_apply, psiA_apply, psiA_apply]
  have hcomp : ⇑(phiA F r n B) ∘ ⇑(phiA F r n A) = ⇑(phiA F r n (B * A)) := by
    funext x
    rw [Function.comp_apply]
    exact congrArg (fun f : S F r n →ₐ[F] S F r n => f x) (phiA_comp F r n A B)
  rw [Matrix.map_mul, Matrix.map_mul, constMat_map, constMat_map, Matrix.map_map, hcomp]
  have hv : (↑(B * A) : Matrix (Fin n) (Fin n) F) =
      (↑B : Matrix (Fin n) (Fin n) F) * (↑A : Matrix (Fin n) (Fin n) F) := Units.val_mul B A
  have hi : (↑((B * A)⁻¹) : Matrix (Fin n) (Fin n) F) =
      (↑A⁻¹ : Matrix (Fin n) (Fin n) F) * (↑B⁻¹ : Matrix (Fin n) (Fin n) F) := by
    rw [mul_inv_rev, Units.val_mul]
  rw [hv, hi, constMat_mul, constMat_mul]
  noncomm_ring

/-- `ψ_1 = id`。 -/
lemma psiA_one : psiA F r n (1 : (Matrix (Fin n) (Fin n) F)ˣ) = RingHom.id _ := by
  apply RingHom.ext
  intro Y
  rw [RingHom.id_apply, psiA_apply, phiA_one, Units.val_one, inv_one, Units.val_one,
    constMat_one, one_mul, mul_one]
  exact Matrix.map_id Y

#print axioms conj_mul
#print axioms psiA
#print axioms psiA_comp
#print axioms psiA_one

end

end Procesi
