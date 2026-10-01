/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-x（终环）：`IsRational` 收口**

  目标：**`IsRational F ↥(latticeInvariantsAlg F A (A → ℤ))`** —— 子块 1β 的最后一条余量（wiki §3n 的路线 A）。

  链条（四段）：

    * **① Ψ**：`ψ` 沿分式域的上延（靶 `diagFrac = Frac F[z_χ^{±}]`）。「非零 ↦ 非零」由 `psiPoly_injective`
      （D11）与 `algebraMap` 单射合成给；
    * **② 生成元层恒等式**：`Ψ(dftVecFF χ) = z_χ` —— **心脏** = `Probe55.sum_inv_smul_uX`（**逆 DFT 的左逆**）；
    * **③ 主恒等式**：**`Ψ ∘ Φ₀ = algebraMap`** ⟹ **`Φ₀` 单射**（`Φ₀` = D10 的 `phiDiag`）。
      收口走 `MonoidAlgebra.induction_on`，其 `of`-支靠**单项式乘积分解**
      `algebraMap (z^m) = ∏_χ (z_χ)^{m_χ}`（`Finsupp.prod_add_index'` ＋ `Int.induction_on` 处理 ℤ-幂）；
    * **④ `IsRational`**：`Y = kernelLattice` 取 ℤ-基 `e_1..e_r`（`Submodule.basisOfPid`，`r = kernelRank`）
      ⟹ `F(Y) ≅ F(t_1,…,t_r)`（`MonoidAlgebra.domCongr` 搬 `Y ≅ ℤ^r` ＋ D2 的自由格结论）；
      而 `Φ₀` 限制到 `F[Y]` 的分式域上延**值域恰为** `diagSubfield = F(M)^A`（D12）⟹ 结论。

  **工艺注**：`IsFractionRing.liftAlgHom` 直接在 `K = latticeFunctionField F (A → ℤ)` 上接线——
  D8 登记的 `instAlgebraPolyFF` ＋ `polyToFF_isFractionRing` 使 `IsScalarTower F (MvPolynomial A F) K`
  成立（本轮探针实证），故**无需**经 `FractionRing.algEquiv` 搬回。
-/
import ABGV52.D12_ABGV52
import ABGV52.Probe55

open scoped Classical

namespace ABGV52

namespace EM

noncomputable section

/-! ## 1. `Ψ`：逆 DFT 沿分式域的上延 -/

section Psi

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **对角模型的分式域** `F(Z_χ)`。 -/
abbrev diagFrac : Type _ := FractionRing (diagAlgebra F A)

/-- `z_χ` 在分式域中的像（`z^χ = zMono (single χ 1)`）。 -/
noncomputable def zeta (χ : MulChar A F) : diagFrac F A :=
  algebraMap (diagAlgebra F A) (diagFrac F A) (zMono F A (Finsupp.single χ 1))

omit [Fintype A] [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] in
/-- `zMono (single χ 1)` 是单位（单项式环的基单项式）。 -/
lemma zMono_single_one_isUnit (χ : MulChar A F) :
    IsUnit (zMono F A (Finsupp.single χ 1)) := by
  rw [zMono, ← MonoidAlgebra.of_apply]
  exact (Group.isUnit (Multiplicative.ofAdd (Finsupp.single χ 1))).map
    (MonoidAlgebra.of F (Multiplicative (MulChar A F →₀ ℤ)))

/-- `z_χ ≠ 0`（整环入其分式域）。 -/
lemma zeta_ne_zero (χ : MulChar A F) : zeta F A χ ≠ 0 := by
  rw [zeta]
  intro h
  refine (zMono_single_one_isUnit F A χ).ne_zero
    (IsFractionRing.injective (diagAlgebra F A) (diagFrac F A) ?_)
  rw [h, map_zero]

/-- `p ↦ algebraMap (ψ p)` 单射（`ψ` 单射 ＋ 分式域的单射性）。 -/
lemma psiPoly_algebraMap_injective :
    Function.Injective fun p : MvPolynomial A F =>
      algebraMap (diagAlgebra F A) (diagFrac F A) (psiPoly F A p) := by
  intro x y hxy
  exact psiPoly_injective F A
    (IsFractionRing.injective (diagAlgebra F A) (diagFrac F A) hxy)

/-- **`Ψ`**：`ψ` 沿分式域的上延（`IsFractionRing.liftAlgHom`）。

  在 `algebraMap`-层取值为 `algebraMap (ψ p)`；`K` 侧的 `MvPolynomial`-代数结构由 D8 的
  `instAlgebraPolyFF` 登记，故 `IsFractionRing.liftAlgHom` 可直接作用于 `K`。 -/
noncomputable def Psi : latticeFunctionField F (A → ℤ) →ₐ[F] diagFrac F A :=
  letI := polyToFF_isFractionRing F A
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom F (diagAlgebra F A) (diagFrac F A)).comp (psiPoly F A))
    (psiPoly_algebraMap_injective F A)

/-- `Ψ` 在 `algebraMap`-层的取值。 -/
lemma Psi_algebraMap (p : MvPolynomial A F) :
    Psi F A (algebraMap (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) p)
      = algebraMap (diagAlgebra F A) (diagFrac F A) (psiPoly F A p) := by
  haveI := polyToFF_isFractionRing F A
  exact IsFractionRing.lift_algebraMap (psiPoly_algebraMap_injective F A) p

/-- `polyToFF`-形态的取值引理（`algebraMap_polyFF` 是 rfl，仅为可读性）。 -/
lemma Psi_polyToFF (p : MvPolynomial A F) :
    Psi F A (polyToFF F A p)
      = algebraMap (diagAlgebra F A) (diagFrac F A) (psiPoly F A p) := by
  rw [← algebraMap_polyFF]
  exact Psi_algebraMap F A p

end Psi

/-! ## 2. 生成元层恒等式与 `z^m` 的乘积分解

  **心脏**：`Ψ(y_χ) = z_χ`（`Probe55.sum_inv_smul_uX`）。搬运走单项式层：
  `dftVecFF χ = ∑_a algebraMap (regMono a ((χ a)⁻¹))`，逐项用 `Psi_algebraMap_regMono`。 -/

section Generators

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

omit [Fintype A] [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] in
/-- `regMono a c = c • regMono a 1`（系数与纯量）。 -/
lemma regMono_eq_smul (a : A) (c : F) :
    regMono F A a c = c • regMono F A a 1 := by
  rw [regMono, regMono, MonoidAlgebra.smul_single]
  simp

/-- `K` 中的单项式 `x_a^c` 是 `polyToFF (C c * X a)`。 -/
lemma regMono_algebraMap_eq (a : A) (c : F) :
    algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ))
        (regMono F A a c)
      = polyToFF F A (MvPolynomial.C c * MvPolynomial.X a) := by
  rw [polyToFF_apply, map_mul, polySubst_X,
    show polySubst F A (MvPolynomial.C c)
        = algebraMap F (latticeAlgebra F (A → ℤ)) c from AlgHom.commutes _ c,
    show algebraMap F (latticeAlgebra F (A → ℤ)) c = c • 1
      from Algebra.algebraMap_eq_smul_one c,
    smul_mul_assoc, one_mul, regMono_eq_smul, algebraMap_smul_regular]

/-- `Ψ` 在单项式 `x_a^c` 上的取值：送进 `c • u_a`。 -/
lemma Psi_algebraMap_regMono (a : A) (c : F) :
    Psi F A (algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ))
        (regMono F A a c))
      = algebraMap (diagAlgebra F A) (diagFrac F A) (c • uX F A a) := by
  rw [regMono_algebraMap_eq, Psi_polyToFF, map_mul, psiPoly_C, psiPoly_X,
    show algebraMap F (diagAlgebra F A) c = c • 1 from Algebra.algebraMap_eq_smul_one c,
    smul_mul_assoc, one_mul]

set_option maxHeartbeats 1000000 in
/-- **生成元层恒等式**：`Ψ(y_χ) = z_χ`（逆 DFT 的左逆 `Probe55.sum_inv_smul_uX`）。

  `dftVecFF χ = ∑_a algebraMap (regMono a ((χ a)⁻¹))`，逐项送进 `c • u_a`，
  再合并为 `algebraMap (∑_a (χ a)⁻¹ • u_a) = algebraMap (z_χ)`。 -/
theorem Psi_dftVecFF (χ : MulChar A F) :
    Psi F A (dftVecFF F A χ) = zeta F A χ := by
  have h1 : dftVecFF F A χ
      = ∑ a : A, algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ))
          (regMono F A a ((χ a)⁻¹)) := by
    unfold dftVecFF dftVec
    simp only [map_sum]
  calc Psi F A (dftVecFF F A χ)
      = ∑ a : A, Psi F A (algebraMap (latticeAlgebra F (A → ℤ))
          (latticeFunctionField F (A → ℤ)) (regMono F A a ((χ a)⁻¹))) := by
        rw [h1, map_sum]
    _ = ∑ a : A, algebraMap (diagAlgebra F A) (diagFrac F A) ((χ a)⁻¹ • uX F A a) :=
        Finset.sum_congr rfl fun a _ => Psi_algebraMap_regMono F A a ((χ a)⁻¹)
    _ = algebraMap (diagAlgebra F A) (diagFrac F A)
          (∑ a : A, (χ a)⁻¹ • uX F A a) := by
        simp only [map_sum]
    _ = algebraMap (diagAlgebra F A) (diagFrac F A)
          (zMono F A (Finsupp.single χ 1)) := by
        rw [Probe55.sum_inv_smul_uX F A χ]
    _ = zeta F A χ := rfl

/-- **ℤ-幂**：`algebraMap (z^{k·χ}) = z_χ^k`（`Int.induction_on`；负向用 `z^{-χ} · z^χ = 1`）。 -/
lemma zeta_zpow_single (χ : MulChar A F) (k : ℤ) :
    algebraMap (diagAlgebra F A) (diagFrac F A) (zMono F A (Finsupp.single χ k))
      = (zeta F A χ) ^ k := by
  induction k using Int.induction_on with
  | zero => rw [Finsupp.single_zero, zMono_zero, map_one, zpow_zero]
  | succ k ih =>
      rw [Finsupp.single_add χ (k : ℤ) 1, zMono_add, map_mul, ih,
        show algebraMap (diagAlgebra F A) (diagFrac F A) (zMono F A (Finsupp.single χ 1))
          = zeta F A χ from rfl,
        ← zpow_add_one₀ (zeta_ne_zero F A χ)]
  | pred k ih =>
      have h1 : Finsupp.single χ (-(k : ℤ) - 1)
          = Finsupp.single χ (-(k : ℤ)) + Finsupp.single χ (-1) := by
        rw [← Finsupp.single_add]
        congr 1
      have hprod : zMono F A (Finsupp.single χ (-1)) * zMono F A (Finsupp.single χ 1) = 1 := by
        rw [← zMono_add,
          show Finsupp.single χ (-1) + Finsupp.single χ 1 = 0 from by
            rw [← Finsupp.single_add]; norm_num,
          zMono_zero]
      have hinv : algebraMap (diagAlgebra F A) (diagFrac F A) (zMono F A (Finsupp.single χ (-1)))
          = (zeta F A χ)⁻¹ := by
        have h2 : algebraMap (diagAlgebra F A) (diagFrac F A)
              (zMono F A (Finsupp.single χ (-1))) * zeta F A χ = 1 := by
          rw [zeta, ← map_mul, hprod, map_one]
        exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h2)
      rw [h1, zMono_add, map_mul, ih, hinv, ← zpow_sub_one₀ (zeta_ne_zero F A χ) (-(k : ℤ))]

/-- 乘积在指数上可加。 -/
lemma prod_zeta_add (m m' : expVector F A) :
    (m + m').prod (fun χ k => (zeta F A χ) ^ k)
      = (m.prod fun χ k => (zeta F A χ) ^ k) * (m'.prod fun χ k => (zeta F A χ) ^ k) :=
  Finsupp.prod_add_index' (fun χ => zpow_zero (zeta F A χ))
    (fun χ b₁ b₂ => zpow_add₀ (zeta_ne_zero F A χ) b₁ b₂)

/-- 单指数情形。 -/
lemma prod_zeta_single (χ : MulChar A F) (k : ℤ) :
    (Finsupp.single χ k).prod (fun χ k => (zeta F A χ) ^ k) = (zeta F A χ) ^ k :=
  Finsupp.prod_single_index (zpow_zero (zeta F A χ))

/-- **单项式乘积分解**：`algebraMap (z^m) = ∏_χ z_χ^{m_χ}`。 -/
lemma algebraMap_zMono_eq_prod (m : expVector F A) :
    algebraMap (diagAlgebra F A) (diagFrac F A) (zMono F A m)
      = m.prod (fun χ k => (zeta F A χ) ^ k) := by
  induction m using Finsupp.induction_linear with
  | zero => rw [Finsupp.prod_zero_index, zMono_zero, map_one]
  | add m₁ m₂ h₁ h₂ => rw [zMono_add, map_mul, h₁, h₂, prod_zeta_add]
  | single χ k => rw [zeta_zpow_single, prod_zeta_single]

end Generators

/-! ## 3. `Ψ ∘ Φ₀ = algebraMap` ⟹ `Φ₀` 单射 -/

section Composite

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- `Ψ` 送 ℤ-幂（`dftVecFF χ ≠ 0`，经 `map_zpow₀`）。 -/
lemma Psi_zpow_dftVecFF (χ : MulChar A F) (k : ℤ) :
    Psi F A ((dftVecFF F A χ) ^ k) = (zeta F A χ) ^ k := by
  rw [map_zpow₀, Psi_dftVecFF]

/-- **单项式层**：`Ψ (Φ₀ (z^m)) = algebraMap (z^m)`。 -/
lemma Psi_diagMono (m : expVector F A) :
    Psi F A (diagMono F A m) = m.prod (fun χ k => (zeta F A χ) ^ k) := by
  induction m using Finsupp.induction_linear with
  | zero => rw [Finsupp.prod_zero_index, diagMono, Finsupp.prod_zero_index, map_one]
  | add m₁ m₂ h₁ h₂ => rw [diagMono_add, map_mul, h₁, h₂, prod_zeta_add]
  | single χ k => rw [prod_zeta_single, diagMono_single]; exact Psi_zpow_dftVecFF F A χ k

/-- **主恒等式**：`Ψ ∘ Φ₀ = algebraMap`（两侧都是 `F`-代数同态，在基单项式 `z^m` 上比较）。 -/
theorem Psi_comp_phiDiag :
    (Psi F A).comp (phiDiag F A)
      = IsScalarTower.toAlgHom F (diagAlgebra F A) (diagFrac F A) := by
  refine AlgHom.ext fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      show Psi F A (phiDiag F A (MonoidAlgebra.single m 1))
        = IsScalarTower.toAlgHom F (diagAlgebra F A) (diagFrac F A) (MonoidAlgebra.single m 1)
      rw [show (MonoidAlgebra.single m 1 : diagAlgebra F A) = zMono F A m.toAdd from rfl,
        phiDiag_zMono, Psi_diagMono,
        show IsScalarTower.toAlgHom F (diagAlgebra F A) (diagFrac F A) (zMono F A m.toAdd)
          = algebraMap (diagAlgebra F A) (diagFrac F A) (zMono F A m.toAdd) from rfl,
        algebraMap_zMono_eq_prod]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul r x hx => rw [map_smul, map_smul, hx]

/-- **`Φ₀` 单射**（由主恒等式 ＋ 分式域的单射性）。 -/
theorem phiDiag_injective : Function.Injective (phiDiag F A) := by
  intro x y hxy
  have h2 : IsScalarTower.toAlgHom F (diagAlgebra F A) (diagFrac F A) x
      = IsScalarTower.toAlgHom F (diagAlgebra F A) (diagFrac F A) y := by
    rw [← Psi_comp_phiDiag, AlgHom.comp_apply, AlgHom.comp_apply, hxy]
  exact IsFractionRing.injective (diagAlgebra F A) (diagFrac F A) h2

end Composite

/-! ## 4. `IsRational` 收口

  `Y = kernelLattice ⊆ expVector` 取 ℤ-基 `e_1..e_r`（`r = kernelRank`）：

    * `F(Y) ≅ F(t_1,…,t_r)`：`MonoidAlgebra.domCongr` 把 `Y ≅ ℤ^r` 搬到单项式环，
      再经分式域搬运接到 D2 的自由格结论；
    * `F(Y) ≅ ↥(latticeInvariantsAlg …)`：`Φ₀|_(F[Y])` 沿分式域上延，值域恰为 `F(Y)`（D12）。

  **⚠ 关键实例**：`latticeAlgebra F ↥Y` 的整环性不被类型类综合自动找到（`↥Y` 是子模，
  mathlib 无 `UniqueProds` 实例）——必须由 `instIsDomainKernelAlgebra` 经 `phiKernel` 的单射
  从 `K` 拉回（否则 `IsFractionRing.lift` 的 `[Field K]` 落到弱实例上，`RingHom.fieldRange` 不相容）。 -/

section Rational

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- `Y` 视作 `ℤ`-子模。 -/
noncomputable def kernelSubmodule : Submodule ℤ (expVector F A) :=
  AddSubgroup.toIntSubmodule (kernelLattice F A)

def kernelIncl : Multiplicative ↥(kernelSubmodule F A) →* Multiplicative (expVector F A) where
  toFun m := Multiplicative.ofAdd (m.toAdd : expVector F A)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma kernelIncl_injective : Function.Injective (kernelIncl F A) := by
  intro m n h
  have h2 : (m.toAdd : expVector F A) = (n.toAdd : expVector F A) :=
    Multiplicative.ofAdd.injective h
  exact Subtype.ext h2

noncomputable def phiKernel :
    latticeAlgebra F ↥(kernelSubmodule F A) →ₐ[F] latticeFunctionField F (A → ℤ) :=
  (phiDiag F A).comp (MonoidAlgebra.mapDomainAlgHom F F (kernelIncl F A))

lemma phiKernel_apply_single (m : ↥(kernelSubmodule F A)) :
    phiKernel F A (MonoidAlgebra.single (Multiplicative.ofAdd m) 1)
      = diagMono F A (m : expVector F A) := by
  show phiDiag F A (MonoidAlgebra.mapDomainAlgHom F F (kernelIncl F A)
    (MonoidAlgebra.single (Multiplicative.ofAdd m) 1)) = _
  rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    show kernelIncl F A (Multiplicative.ofAdd m)
      = Multiplicative.ofAdd (m : expVector F A) from rfl]
  exact phiDiag_zMono F A (m : expVector F A)

lemma phiKernel_apply_of (m : Multiplicative ↥(kernelSubmodule F A)) :
    phiKernel F A (MonoidAlgebra.of F (Multiplicative ↥(kernelSubmodule F A)) m)
      = diagMono F A (m.toAdd : expVector F A) := by
  rw [MonoidAlgebra.of_apply]
  exact phiKernel_apply_single F A m.toAdd

lemma phiKernel_injective : Function.Injective (phiKernel F A) := by
  intro x y hxy
  have h1 : MonoidAlgebra.mapDomain (kernelIncl F A) x
      = MonoidAlgebra.mapDomain (kernelIncl F A) y := phiDiag_injective F A hxy
  exact MonoidAlgebra.mapDomain_injective (kernelIncl_injective F A) h1

instance instIsDomainKernelAlgebra : IsDomain (latticeAlgebra F ↥(kernelSubmodule F A)) :=
  Function.Injective.isDomain (phiKernel F A) (phiKernel_injective F A)

lemma phiKernel_mem_diagSubfield (x : latticeAlgebra F ↥(kernelSubmodule F A)) :
    phiKernel F A x ∈ diagSubfield F A := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      rw [phiKernel_apply_of]
      exact Subfield.subset_closure (Or.inr ⟨m.toAdd, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Subfield.add_mem _ hx hy
  | smul r x hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inl ⟨r, rfl⟩)) hx


noncomputable def kernelRank : ℕ :=
  (Submodule.basisOfPid Finsupp.basisSingleOne (kernelSubmodule F A)).1

noncomputable def kernelBasis : Module.Basis (Fin (kernelRank F A)) ℤ ↥(kernelSubmodule F A) :=
  (Submodule.basisOfPid Finsupp.basisSingleOne (kernelSubmodule F A)).2

noncomputable def kernelMulEquiv :
    Multiplicative ↥(kernelSubmodule F A) ≃* Multiplicative (Fin (kernelRank F A) → ℤ) :=
  AddEquiv.toMultiplicative
    ((kernelBasis F A).repr.trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (kernelRank F A)))).toAddEquiv

noncomputable def kernelFracEquiv :
    latticeFunctionField F ↥(kernelSubmodule F A)
      ≃ₐ[F] latticeFunctionField F (Fin (kernelRank F A) → ℤ) :=
  IsFractionRing.algEquivOfAlgEquiv (MonoidAlgebra.domCongr F F (kernelMulEquiv F A))


noncomputable instance instFieldInvariantsAlg : Field ↥(latticeInvariantsAlg F A (A → ℤ)) :=
  inferInstanceAs (Field ↥(latticeInvariants F A (A → ℤ)))

theorem diagSubfield_eq_invariantsAlg :
    (diagSubfield F A : Set (latticeFunctionField F (A → ℤ)))
      = (latticeInvariantsAlg F A (A → ℤ) : Set (latticeFunctionField F (A → ℤ))) :=
  (congrArg (fun s : Subfield (latticeFunctionField F (A → ℤ)) =>
      (s : Set (latticeFunctionField F (A → ℤ)))) (diagSubfield_eq_latticeInvariants F A)).trans
    (latticeInvariants_carrier_eq F A (A → ℤ))


/-- `Y` 的两种载体（`AddSubgroup` 形态与 `Submodule` 形态）给出同一生成集。 -/
lemma phiKernel_witness_kernel (m : ↥(kernelLattice F A)) :
    phiKernel F A (MonoidAlgebra.single
      (Multiplicative.ofAdd (⟨m.1, m.2⟩ : ↥(kernelSubmodule F A))) 1)
      = diagMono F A (m : expVector F A) := by
  rw [phiKernel_apply_single]

theorem lift_fieldRange_eq_diagSubfield :
    (IsFractionRing.lift (phiKernel_injective F A)
      : latticeFunctionField F ↥(kernelSubmodule F A) →+*
        latticeFunctionField F (A → ℤ)).fieldRange = diagSubfield F A := by
  rw [IsFractionRing.lift_fieldRange]
  refine le_antisymm ?_ ?_
  · refine Subfield.closure_le.mpr fun y hy => ?_
    rw [SetLike.mem_coe] at hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range (phiKernel F A)).mp hy
    exact phiKernel_mem_diagSubfield F A x
  · refine Subfield.closure_le.mpr ?_
    rintro y (⟨c, rfl⟩ | ⟨m, rfl⟩)
    · refine Subfield.subset_closure ((AlgHom.mem_range (phiKernel F A)).mpr ?_)
      exact ⟨algebraMap F (latticeAlgebra F ↥(kernelSubmodule F A)) c, by
        rw [AlgHom.commutes]⟩
    · refine Subfield.subset_closure ((AlgHom.mem_range (phiKernel F A)).mpr ?_)
      exact ⟨MonoidAlgebra.single (Multiplicative.ofAdd (⟨m.1, m.2⟩ : ↥(kernelSubmodule F A))) 1,
        phiKernel_witness_kernel F A m⟩


lemma kernel_lift_mem (x : latticeFunctionField F ↥(kernelSubmodule F A)) :
    IsFractionRing.liftAlgHom (phiKernel_injective F A) x
      ∈ latticeInvariantsAlg F A (A → ℤ) := by
  change IsFractionRing.liftAlgHom (phiKernel_injective F A) x
    ∈ (latticeInvariantsAlg F A (A → ℤ) : Set (latticeFunctionField F (A → ℤ)))
  rw [← diagSubfield_eq_invariantsAlg]
  show IsFractionRing.lift (phiKernel_injective F A) x ∈ diagSubfield F A
  obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj
    (nonZeroDivisors (latticeAlgebra F ↥(kernelSubmodule F A))) x
  have hb0 : (b : latticeAlgebra F ↥(kernelSubmodule F A)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hbne : phiKernel F A (b : latticeAlgebra F ↥(kernelSubmodule F A)) ≠ 0 := fun h =>
    hb0 (phiKernel_injective F A (by rw [h, map_zero]))
  have hx : IsFractionRing.lift (phiKernel_injective F A) x
      = phiKernel F A a
        * (phiKernel F A (b : latticeAlgebra F ↥(kernelSubmodule F A)))⁻¹ := by
    have h := congrArg (IsFractionRing.lift (phiKernel_injective F A)) hb
    rw [map_mul, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at h
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hbne).mpr h
  rw [hx]
  exact Subfield.mul_mem _ (phiKernel_mem_diagSubfield F A a)
    (Subfield.inv_mem _ (phiKernel_mem_diagSubfield F A _))

lemma injective_of_field {K' L : Type*} [Field K'] [Ring L] [Nontrivial L]
    (f : K' →+* L) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  have h0 : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h1 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hmul : (x - y) * (x - y)⁻¹ = 1 := mul_inv_cancel₀ h0
  have h2 : (1 : L) = 0 := by rw [← map_one f, ← hmul, map_mul, h1, zero_mul]
  exact one_ne_zero h2


noncomputable def kernelFracEquivInvariantsAlg :
    latticeFunctionField F ↥(kernelSubmodule F A)
      ≃ₐ[F] ↥(latticeInvariantsAlg F A (A → ℤ)) :=
  AlgEquiv.ofBijective
    ((IsFractionRing.liftAlgHom (phiKernel_injective F A)).codRestrict
      (latticeInvariantsAlg F A (A → ℤ)) (kernel_lift_mem F A))
    ⟨fun _ _ hxy => injective_of_field _ (Subtype.ext_iff.mp hxy), fun z => by
      have hz : (z : latticeFunctionField F (A → ℤ))
          ∈ (IsFractionRing.lift (phiKernel_injective F A)
              : latticeFunctionField F ↥(kernelSubmodule F A) →+*
                latticeFunctionField F (A → ℤ)).fieldRange := by
        rw [lift_fieldRange_eq_diagSubfield]
        change (z : latticeFunctionField F (A → ℤ))
          ∈ (diagSubfield F A : Set (latticeFunctionField F (A → ℤ)))
        rw [diagSubfield_eq_invariantsAlg]
        exact z.2
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hz
      exact ⟨x, Subtype.ext hx⟩⟩

theorem isRational_latticeInvariantsAlg :
    IsRational F ↥(latticeInvariantsAlg F A (A → ℤ)) := by
  obtain ⟨n, ⟨e⟩⟩ := isRational_latticeFunctionField_free F (kernelRank F A)
  exact ⟨n, ⟨(kernelFracEquivInvariantsAlg F A).symm.trans
    ((kernelFracEquiv F A).trans e)⟩⟩

end Rational

/-! ## 公理闸门 -/

#print axioms Psi
#print axioms Psi_dftVecFF
#print axioms zeta_zpow_single
#print axioms algebraMap_zMono_eq_prod
#print axioms Psi_comp_phiDiag
#print axioms phiDiag_injective
#print axioms phiKernel_injective
#print axioms instIsDomainKernelAlgebra
#print axioms kernelMulEquiv
#print axioms kernelFracEquiv
#print axioms lift_fieldRange_eq_diagSubfield
#print axioms kernel_lift_mem
#print axioms kernelFracEquivInvariantsAlg
#print axioms isRational_latticeInvariantsAlg

end

end EM

end ABGV52
