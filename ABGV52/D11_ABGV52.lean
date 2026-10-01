/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-viii：逆 DFT 是 `Φ₀` 的截面**

  目标（§3 第 1 步）：**`Φ₀ ∘ ψ = polyToFF`** —— 逆 DFT `ψ` 是对角求值 `Φ₀` 在多项式模型上的截面。

    * **`uX`**：`u_a := |A|⁻¹ ∑_χ χ(a) z_χ`（逆 DFT 在单项式层的像，取对角模型的**元素**——无需单位）；
    * **`psiPoly`**：多项式模型 → 对角模型，`X_a ↦ u_a`（`MvPolynomial.aeval`）；
    * **`phiDiag_comp_psiPoly`**：**截面上恒等式**（生成元层由 D4 的 `sum_smul_dftVec` ＋ 特征正交性给）；
    * **`psiPoly_injective`**：由上式 ＋ D8 的 `polyToFF_injective` 推出。

  **余下（见 wiki §3l）**：② 多项式模型的 `A`-作用（`rename`）＋ 与 `K` 的相容；ψ 的等变性（`g • u_a = u_{g·a}`）；
  ③ `K ≅ FractionRing (MvPolynomial A F)` 的典范同构 ＋ 等变性（`Probe54.probe_frac_equivariance`）；
  ④ 汇编：不变元 ⟹ 多项式的清分母表示 ⟹ `ψ` 送进 `Y`-张成（丙-3）⟹ `Φ₀`（D10）送进 `diagSubfield`。
-/
import ABGV52.D10_ABGV52

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

section PsiPoly

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **`u_a := |A|⁻¹ ∑_χ χ(a) z_χ`**（逆 DFT 在单项式层的像）。 -/
noncomputable def uX (a : A) : diagAlgebra F A :=
  (Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F, (χ a) • zMono F A (Finsupp.single χ 1)

/-- **`ψ`**：多项式模型 `F[X_a]` → 对角模型 `F[z_χ^{±}]`，`X_a ↦ u_a`。 -/
noncomputable def psiPoly : MvPolynomial A F →ₐ[F] diagAlgebra F A :=
  MvPolynomial.aeval (fun a => uX F A a)

/-- `ψ` 在变量上的取值。 -/
lemma psiPoly_X (a : A) : psiPoly F A (MvPolynomial.X a) = uX F A a :=
  MvPolynomial.aeval_X (uX F A) a

/-- **截面上恒等式**：`Φ₀ ∘ ψ = polyToFF`（两侧都是 `F`-代数同态，在变量上一致）。

变量层的计算 = **特征正交性**：`|A|⁻¹ ∑_χ χ(a) Φ₀(z_χ) = |A|⁻¹ ∑_χ χ(a) dftVecFF χ = x_a`，
末步 = D4 的 `sum_smul_dftVec`（在 `K` 中经 `algebraMap_smul_regular` 搬运）。 -/
theorem phiDiag_comp_psiPoly :
    (phiDiag F A).comp (psiPoly F A) = polyToFF F A := by
  refine MvPolynomial.algHom_ext fun a => ?_
  have hne : (Fintype.card A : F) ≠ 0 := NeZero.ne _
  have hsum : (∑ χ : MulChar A F, (χ a) • dftVecFF F A χ)
      = (Fintype.card A : F) • algebraMap (latticeAlgebra F (A → ℤ))
          (latticeFunctionField F (A → ℤ)) (regMono F A a 1) := by
    have h := congrArg (algebraMap (latticeAlgebra F (A → ℤ))
      (latticeFunctionField F (A → ℤ))) (sum_smul_dftVec F A a)
    simp only [map_sum] at h
    rw [algebraMap_smul_regular] at h
    have h2 : (∑ χ : MulChar A F, algebraMap (latticeAlgebra F (A → ℤ))
        (latticeFunctionField F (A → ℤ)) ((χ a) • dftVec F A χ))
        = ∑ χ : MulChar A F, (χ a) • dftVecFF F A χ :=
      Finset.sum_congr rfl fun χ _ => by rw [dftVecFF, algebraMap_smul_regular]
    rw [← h2]
    exact h
  rw [AlgHom.comp_apply, psiPoly_X, polyToFF_apply, polySubst_X]
  rw [uX, map_smul, map_sum]
  have hterm : ∀ χ : MulChar A F,
      phiDiag F A ((χ a) • zMono F A (Finsupp.single χ 1)) = (χ a) • dftVecFF F A χ := by
    intro χ
    rw [map_smul, phiDiag_zMono, diagMono_single, zpow_one]
  rw [Finset.sum_congr rfl fun χ _ => hterm χ]
  rw [hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- **`ψ` 单射**：由 `Φ₀ ∘ ψ = polyToFF` 与 D8 的 `polyToFF_injective` 推出。 -/
theorem psiPoly_injective : Function.Injective (psiPoly F A) := by
  intro p q hpq
  refine polyToFF_injective F A ?_
  rw [← phiDiag_comp_psiPoly F A, AlgHom.comp_apply, AlgHom.comp_apply, hpq]

end PsiPoly

/-! ## 公理闸门 -/

#print axioms uX
#print axioms psiPoly
#print axioms phiDiag_comp_psiPoly
#print axioms psiPoly_injective

end

end EM

end ABGV52
