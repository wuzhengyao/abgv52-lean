/-
  Procesi —— **(A)+(B) S3 的准备层：`PGL_n(F)` 在分式域 `K = Frac(S)` 上的作用**

  **原文（逐字）**：`raw/Saltman1999ch14.tex`（`lem:14.13` 前的段落）：
  > That is, we have defined an action of `PGL_n(F)` on `S`. In an obvious way this action
  > extends to an action on the field of fractions `K` of `S`.

  **本件**：把 `PGL.lean` 的 `φ_A : S →ₐ[F] S` 打包为**代数自同构** `phiAEquiv`，
  再经 `IsFractionRing.ringEquivOfRingEquiv` 提升为 `K ≃+* K`（`phiKEquiv`）——
  与 `SaltmanT.lean` §2m（`torusScaleFieldEquiv`）**同一手法**。

  **用途**：`lem:14.13`（`a ∈ K^{PGL_n} ⟹ a = f/g`，`f,g ∈ S^{PGL_n}`）的固定点条件
  `phiKEquiv A a = a`；以及 `prop:14.14`（generic 不变性）的定义域。

  **射程**：只做 `K` 层作用。`lem:14.13` 本体（UFD／次数论证）在下一件。
-/
import Procesi.PGL
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

open Matrix

namespace Procesi

noncomputable section

variable (F : Type) [Field F] (r n : ℕ)

/-- `S = F[x_{ijk}]` 的分式域 `K = Frac(S)`（Saltman 的 `K`）。 -/
abbrev SField (F : Type) [Field F] (r n : ℕ) := FractionRing (S F r n)

/-- ★★ **`φ_A : S ≃ₐ[F] S`**：`A ∈ GL_n(F)` 时 `phiA A` 是 `F`-代数自同构，
逆为 `phiA A⁻¹`（互逆性即 `phiA_comp` ＋ `phiA_one`）。

**注**：这同时说明 `φ_A` 是**单射**（`lem:14.13` 的"次数不变"论证要用）。 -/
noncomputable def phiAEquiv (A : (Matrix (Fin n) (Fin n) F)ˣ) : S F r n ≃ₐ[F] S F r n :=
  AlgEquiv.ofAlgHom (phiA F r n A) (phiA F r n A⁻¹)
    (by rw [phiA_comp, mul_inv_cancel, phiA_one])
    (by rw [phiA_comp, inv_mul_cancel, phiA_one])

#print axioms phiAEquiv

/-- ★★ **`φ_A` 在分式域上的作用**：`K ≃+* K`（`IsFractionRing.ringEquivOfRingEquiv`）。 -/
noncomputable def phiKEquiv (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    SField F r n ≃+* SField F r n :=
  IsFractionRing.ringEquivOfRingEquiv (phiAEquiv F r n A).toRingEquiv

#print axioms phiKEquiv

/-- `phiKEquiv` 在 `S` 的像上就是 `phiA`（`_algebraMap` 规则）。 -/
lemma phiKEquiv_algebraMap (A : (Matrix (Fin n) (Fin n) F)ˣ) (x : S F r n) :
    phiKEquiv F r n A (algebraMap (S F r n) (SField F r n) x)
      = algebraMap (S F r n) (SField F r n) (phiA F r n A x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (phiAEquiv F r n A).toRingEquiv x

#print axioms phiKEquiv_algebraMap

/-- 常矩阵的纯量情形：`constMat (scalar c) = scalar (algebraMap c)`。 -/
lemma constMat_scalar (c : F) :
    constMat F r n (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) (algebraMap F (S F r n) c) := by
  apply Matrix.ext
  intro i j
  rw [constMat, Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

#print axioms constMat_scalar

/-- **纯量不动（不定元层）**：`u ∈ Fˣ` 的纯量矩阵给出恒等替换（原文："if `A` is a scalar
matrix then `φ_A` is the identity"）。 -/
lemma phiGen_scalar (u : Fˣ) (e : Fin r × Fin n × Fin n) :
    phiGen F r n (GeneralLinearGroup.scalar (Fin n) u) e = MvPolynomial.X e := by
  obtain ⟨k, i, j⟩ := e
  have hinv : (↑((GeneralLinearGroup.scalar (Fin n) u)⁻¹) : Matrix (Fin n) (Fin n) F)
      = Matrix.scalar (Fin n) ((u⁻¹ : Fˣ) : F) := by
    rw [show (GeneralLinearGroup.scalar (Fin n) u)⁻¹ = GeneralLinearGroup.scalar (Fin n) u⁻¹
      from (map_inv _ u).symm, GeneralLinearGroup.coe_scalar]
  have hcoe : (↑(GeneralLinearGroup.scalar (Fin n) u) : Matrix (Fin n) (Fin n) F)
      = Matrix.scalar (Fin n) (u : F) := GeneralLinearGroup.coe_scalar u
  rw [phiGen, hinv, hcoe, constMat_scalar, constMat_scalar]
  simp only [Matrix.scalar_apply]
  rw [← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  rfl

#print axioms phiGen_scalar

/-- ★★ **纯量作用平凡（`S` 层）**：`φ_{u·1} = id`。这是 `lem:14.13` 里
"`λ(A)` 只依赖 `A` 在 `PGL_n(F)` 中的像"的依据。 -/
lemma phiA_scalar (u : Fˣ) :
    phiA F r n (GeneralLinearGroup.scalar (Fin n) u) = AlgHom.id F (S F r n) := by
  apply MvPolynomial.algHom_ext
  intro e
  rw [phiA, MvPolynomial.aeval_X, AlgHom.id_apply, phiGen_scalar]

#print axioms phiA_scalar

/-- ★★ **纯量作用平凡（`K` 层）**。 -/
lemma phiKEquiv_scalar (u : Fˣ) (x : SField F r n) :
    phiKEquiv F r n (GeneralLinearGroup.scalar (Fin n) u) x = x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S F r n) x
  rw [map_div₀, phiKEquiv_algebraMap, phiKEquiv_algebraMap, phiA_scalar, AlgHom.id_apply,
    AlgHom.id_apply]

#print axioms phiKEquiv_scalar


end

end Procesi
