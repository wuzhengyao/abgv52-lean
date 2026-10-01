/-
  ABGV-5.2 —— **G 档 G2（p-一般）：子群步 \(F(M|_H)^H\cong F(M_{\mathrm{rep}})^H\) ＋ 装配**

  闸门读数（2026-09-30，已过闸）：lean rc=0／error=0／无 sorry；
  `#print axioms` **十条均为** `[propext, Classical.choice, Quot.sound]`（含 §1′ 的五条工具实例与主定理 `ZH_iso`）。

  命名说明：C 档（p=3）已占用 `G2_ABGV52`／`G2b_ABGV52`／`G4_ABGV52`（namespace `ABGV52`，
  \(H=C_3\times C_3\) 来自 B 档）。本件是**参数化 G 档**（namespace `ABGV52.G`，\(H=C_p\times C_p\)
  来自 P 档），故另立 `G2p`。

  论文锚：`rem:procesi-geometric`（`raw/ABGV-5.2-resolution.tex:592`）——
  \(Z_H(F,9) = F(M)^H \cong F(M|_H)^H\)，其中 \(F(M)\) 是格 \(M\) 的函数域、作用由
  \(M\) 的 \(\mathbb Z[S_9]\)-模结构诱导；论文明确**只用到该正合列与这一等同**。

  本件三段：
    ① **子群步（代数层，无条件）**：G1c 的 `Miso : M|_θ ≅ M_rep` 诱导单项式环同构
       `latticeAlgebra F ↥(ker φ) ≃+* latticeAlgebra F ↥(ker π)`，且**与 H-作用交换**；
    ② **子群步（函数域层＋不变量层）**：沿分式域延拓并取不动点 —— 即
       `F(M|_θ)^H ≅ F(M_rep)^H`（右端＝ D 档已有的 `latticeInvariants F (Hp p) M_rep`）；
    ③ **装配**：以 **Procesi 1967** 的 \(Z_H(F,p^2)\cong F(M|_H)^H\) 为**带名假设**，
       得 \(Z_H(F,p^2)\cong F(M_{\mathrm{rep}})^H\)。

  **②③④ 原本依赖的 `UniqueProds (Multiplicative ↥(ker ·))`（「格代数是整环」）已在本件 §1′ 补成
  实例**（mathlib 无此实例；本轮实跑＋负例对照确认，见 §1′ 注释）⟹ **①–④ 全部无条件**。
-/
import ABGV52.D1_ABGV52
import ABGV52.P1_ABGV52
import ABGV52.G1c_ABGV52
import Mathlib.LinearAlgebra.DirectSum.Finsupp

open scoped TensorProduct
open CategoryTheory

namespace ABGV52.G

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 子群步（代数层）：\(F[M|_\theta]\cong F[M_{\mathrm{rep}}]\)，**无条件** -/

/-- `kerEquiv` 在 `Multiplicative` 侧的乘法等价（加法等价 ↔ 乘法等价）。 -/
noncomputable def kerMulEquiv : Multiplicative ↥(LinearMap.ker (phiFun p)) ≃*
    Multiplicative ↥(LinearMap.ker (ABGV52.P.pi p)) where
  toFun x := Multiplicative.ofAdd ((kerEquiv p) x.toAdd)
  invFun y := Multiplicative.ofAdd ((kerEquiv p).symm y.toAdd)
  left_inv x := by
    show Multiplicative.ofAdd ((kerEquiv p).symm ((kerEquiv p) x.toAdd)) = x
    simp
  right_inv y := by
    show Multiplicative.ofAdd ((kerEquiv p) ((kerEquiv p).symm y.toAdd)) = y
    simp
  map_mul' x y := by
    show Multiplicative.ofAdd ((kerEquiv p) (x.toAdd + y.toAdd))
      = Multiplicative.ofAdd ((kerEquiv p) x.toAdd + (kerEquiv p) y.toAdd)
    rw [map_add]

/-- `Mres` 的作用在元素上即 `DistribMulAction` 的 `•`（`rfl` 级）。 -/
lemma Mres_rho_apply (h : ABGV52.P.Hp p) (x : ↥(LinearMap.ker (phiFun p))) :
    (Mres p).ρ h x = h • x := rfl

lemma Mrep_rho_apply (h : ABGV52.P.Hp p) (y : ↥(LinearMap.ker (ABGV52.P.pi p))) :
    (ABGV52.P.M_rep p).ρ h y = h • y := rfl

/-- `kerEquiv` 的逐点等变性（直接由 G1c 的 `PhiLM_equivariant` 读出）。 -/
lemma kerEquiv_smul_apply (h : ABGV52.P.Hp p) (x : ↥(LinearMap.ker (phiFun p))) :
    kerEquiv p (h • x) = h • (kerEquiv p x) := by
  apply Subtype.ext
  show PhiLM p (TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) x.1)
    = ABGV52.P.act p h (PhiLM p x.1)
  exact PhiLM_equivariant p h x.1

lemma kerMulEquiv_smul (h : ABGV52.P.Hp p)
    (x : Multiplicative ↥(LinearMap.ker (phiFun p))) :
    kerMulEquiv p (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p)
        ↥(LinearMap.ker (phiFun p)) h x)
      = ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p)
          ↥(LinearMap.ker (ABGV52.P.pi p)) h (kerMulEquiv p x) := by
  show Multiplicative.ofAdd ((kerEquiv p) (h • x.toAdd))
    = Multiplicative.ofAdd (h • ((kerEquiv p) x.toAdd))
  rw [kerEquiv_smul_apply p h x.toAdd]

/-- **子群步（代数层）**：\(F[M|_\theta]\cong F[M_{\mathrm{rep}}]\)。 -/
noncomputable def latticeAlgEquiv (F : Type*) [Field F] :
    ABGV52.EM.latticeAlgebra F ↥(LinearMap.ker (phiFun p)) ≃+*
      ABGV52.EM.latticeAlgebra F ↥(LinearMap.ker (ABGV52.P.pi p)) :=
  MonoidAlgebra.mapDomainRingEquiv F (kerMulEquiv p)

/-- **等变性（代数层）**。 -/
lemma latticeAlgEquiv_smul (F : Type*) [Field F] (h : ABGV52.P.Hp p)
    (x : ABGV52.EM.latticeAlgebra F ↥(LinearMap.ker (phiFun p))) :
    latticeAlgEquiv p F (h • x) = h • (latticeAlgEquiv p F x) := by
  have hme :
      (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p)) h).trans
          (kerMulEquiv p)
        = (kerMulEquiv p).trans
          (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p)
            ↥(LinearMap.ker (ABGV52.P.pi p)) h) :=
    MulEquiv.ext fun x => kerMulEquiv_smul p h x
  have h1 : latticeAlgEquiv p F (h • x)
      = MonoidAlgebra.mapDomainRingEquiv F
          ((ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p)) h).trans
            (kerMulEquiv p)) x := by
    show ((MonoidAlgebra.mapDomainRingEquiv F
            (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p)) h)).trans
          (MonoidAlgebra.mapDomainRingEquiv F (kerMulEquiv p))) x
      = MonoidAlgebra.mapDomainRingEquiv F
          ((ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p)) h).trans
            (kerMulEquiv p)) x
    rw [MonoidAlgebra.mapDomainRingEquiv_trans]
  have h2 : h • (latticeAlgEquiv p F x)
      = MonoidAlgebra.mapDomainRingEquiv F
          ((kerMulEquiv p).trans
            (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p)
              ↥(LinearMap.ker (ABGV52.P.pi p)) h)) x := by
    show ((MonoidAlgebra.mapDomainRingEquiv F (kerMulEquiv p)).trans
          (MonoidAlgebra.mapDomainRingEquiv F
            (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p)
              ↥(LinearMap.ker (ABGV52.P.pi p)) h))) x
      = MonoidAlgebra.mapDomainRingEquiv F
          ((kerMulEquiv p).trans
            (ABGV52.EM.mulEquivOfSMul (ABGV52.P.Hp p)
              ↥(LinearMap.ker (ABGV52.P.pi p)) h)) x
    rw [MonoidAlgebra.mapDomainRingEquiv_trans]
  rw [h1, h2, hme]

/-! ## 1′. 工具实例：补 mathlib 的 `UniqueSums` 缺口（使 ②③④ **无条件**）

  mathlib 现状（**实跑**）：`UniqueSums` 对 `ℤ`／`Π`（`Fin n → ℤ`）**有实例**，
  但对 `Finsupp`／包装群环 `MonoidAlgebra`／`Vp`／张积**均无**（负例对照 `Multiplicative (ZMod 2)`
  亦无 ⟹ 非「凡群可推断」的假实例）。本段补三个工具实例，把链条接通：

    `Fin n → ℤ` ✓ → `ι →₀ ℤ` ✓ → `MonoidAlgebra ℤ M` ✓ → `Π`（`Vp`）✓ → 张积（经显式同构）✓。

  数学依据：这些加法群都是**挠自由阿贝尔群**（自由阿贝尔群或其子群）⟹ 唯一和成立。 -/

/-- 有限型 `ℤ`-系数自由模的唯一和（经 `Finsupp ≃ (ι → ℤ)`）。 -/
instance uniqueSums_finsupp {ι : Type*} [Fintype ι] : UniqueSums (ι →₀ ℤ) :=
  (AddEquiv.uniqueSums_iff (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).toAddEquiv).mpr inferInstance

/-- 群环（包装结构 `MonoidAlgebra`）的唯一和（经 `coeffLinearEquiv` 搬到 `Finsupp`）。 -/
instance uniqueSums_monoidAlgebra {M : Type*} [Fintype M] :
    UniqueSums (MonoidAlgebra ℤ M) :=
  (AddEquiv.uniqueSums_iff (MonoidAlgebra.coeffLinearEquiv ℤ).toAddEquiv).mpr inferInstance

/-- 张积侧同构 `ℤ[Ω] ⊗ ℤ[Ω] ≅ (Ω × Ω →₀ ℤ)`（包装 → Finsupp → 张积-函数 → 消去 `ℤ ⊗ ℤ`）。 -/
noncomputable def zomTensorEquiv :
    (ZOm p) ⊗[ℤ] (ZOm p) ≃ₗ[ℤ] ((OmegaP p × OmegaP p) →₀ ℤ) :=
  (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv ℤ)
      (MonoidAlgebra.coeffLinearEquiv ℤ)).trans
    (finsuppTensorFinsupp' ℤ (OmegaP p) (OmegaP p))

instance uniqueSums_zomTensor : UniqueSums ((ZOm p) ⊗[ℤ] (ZOm p)) :=
  (AddEquiv.uniqueSums_iff (zomTensorEquiv p).toAddEquiv).mpr inferInstance

/-- `ker φ` 上的唯一和（沿子模包含拉回）。 -/
instance uniqueSums_kerPhi : UniqueSums ↥(LinearMap.ker (phiFun p)) :=
  UniqueSums.of_injective_addHom
    { toFun := fun x => (x.1 : (ZOm p) ⊗[ℤ] (ZOm p)), map_add' := fun _ _ => rfl }
    Subtype.val_injective inferInstance

/-- `ker π` 上的唯一和（沿子模包含拉回）。 -/
instance uniqueSums_kerPi : UniqueSums ↥(LinearMap.ker (ABGV52.P.pi p)) :=
  UniqueSums.of_injective_addHom
    { toFun := fun x => (x.1 : ABGV52.P.Vp p), map_add' := fun _ _ => rfl }
    Subtype.val_injective inferInstance

/-! ## 2. 子群步（函数域层 ＋ 不变量层） -/

/-- `H` 在 `F(M)` 上的作用，写成显式环自同构（＝ D 档 `MulSemiringAction` 实例的载体）。 -/
noncomputable def ffActionHom (F : Type*) [Field F]
    (M : Type*) [AddCommGroup M] [Module ℤ M] [DistribMulAction (ABGV52.P.Hp p) M]
    [SMulCommClass (ABGV52.P.Hp p) ℤ M] [UniqueProds (Multiplicative M)]
    (h : ABGV52.P.Hp p) :
    ABGV52.EM.latticeFunctionField F M ≃+* ABGV52.EM.latticeFunctionField F M :=
  IsFractionRing.ringEquivOfRingEquivHom (ABGV52.EM.latticeAlgebra F M)
    (ABGV52.EM.latticeFunctionField F M) (ABGV52.EM.latticeAlgebraActionHom F (ABGV52.P.Hp p) M h)

/-- **子群步（函数域层）**：\(F(M|_\theta)\cong F(M_{\mathrm{rep}})\)。 -/
noncomputable def latticeFFEquiv (F : Type*) [Field F]
    :
    ABGV52.EM.latticeFunctionField F ↥(LinearMap.ker (phiFun p)) ≃+*
      ABGV52.EM.latticeFunctionField F ↥(LinearMap.ker (ABGV52.P.pi p)) :=
  IsFractionRing.ringEquivOfRingEquiv (latticeAlgEquiv p F)

/-- **等变性（函数域层）**：由 `IsFractionRing` 的环同态外延化归到 `algebraMap`。 -/
lemma latticeFFEquiv_smul (F : Type*) [Field F]
    (h : ABGV52.P.Hp p)
    (x : ABGV52.EM.latticeFunctionField F ↥(LinearMap.ker (phiFun p))) :
    latticeFFEquiv p F (h • x) = h • (latticeFFEquiv p F x) := by
  have htrans :
      (ABGV52.EM.latticeAlgebraActionHom F (ABGV52.P.Hp p)
          ↥(LinearMap.ker (phiFun p)) h).trans (latticeAlgEquiv p F)
        = (latticeAlgEquiv p F).trans
          (ABGV52.EM.latticeAlgebraActionHom F (ABGV52.P.Hp p)
            ↥(LinearMap.ker (ABGV52.P.pi p)) h) :=
    RingEquiv.ext fun a => latticeAlgEquiv_smul p F h a
  have hcomp : (latticeFFEquiv p F).trans
        (ffActionHom p F ↥(LinearMap.ker (ABGV52.P.pi p)) h)
      = (ffActionHom p F ↥(LinearMap.ker (phiFun p)) h).trans (latticeFFEquiv p F) := by
    rw [latticeFFEquiv, ffActionHom, ffActionHom,
      IsFractionRing.ringEquivOfRingEquivHom_apply,
      IsFractionRing.ringEquivOfRingEquivHom_apply,
      ← IsFractionRing.ringEquivOfRingEquiv_comp,
      ← IsFractionRing.ringEquivOfRingEquiv_comp, htrans]
  have hpt := (RingEquiv.ext_iff.mp hcomp) x
  exact hpt.symm

/-! ## 3. 子群步（不变量层）：\(F(M|_\theta)^H\cong F(M_{\mathrm{rep}})^H\) -/

/-- **子群步（不变量层）**：两格的 \(H\)-不变量域同构
（右端即 D 档对 `M_rep` 已有的 `latticeInvariants`）。 -/
noncomputable def invariantsEquiv (F : Type*) [Field F] :
    ↥(ABGV52.EM.latticeInvariants F (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p))) ≃+*
      ↥(ABGV52.EM.latticeInvariants F (ABGV52.P.Hp p)
        ↥(LinearMap.ker (ABGV52.P.pi p))) where
  toFun x := ⟨latticeFFEquiv p F x.1, by
    rw [ABGV52.EM.mem_latticeInvariants_iff]
    intro h
    have hx : h • x.1 = x.1 :=
      (ABGV52.EM.mem_latticeInvariants_iff F (ABGV52.P.Hp p) _ x.1).mp x.2 h
    rw [← latticeFFEquiv_smul p F h x.1, hx]⟩
  invFun y := ⟨(latticeFFEquiv p F).symm y.1, by
    rw [ABGV52.EM.mem_latticeInvariants_iff]
    intro h
    have hy : h • y.1 = y.1 :=
      (ABGV52.EM.mem_latticeInvariants_iff F (ABGV52.P.Hp p) _ y.1).mp y.2 h
    refine (latticeFFEquiv p F).injective ?_
    rw [latticeFFEquiv_smul p F h ((latticeFFEquiv p F).symm y.1),
      (latticeFFEquiv p F).apply_symm_apply y.1]
    exact hy⟩
  left_inv x := Subtype.ext ((latticeFFEquiv p F).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((latticeFFEquiv p F).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext ((latticeFFEquiv p F).map_mul x.1 y.1)
  map_add' x y := Subtype.ext ((latticeFFEquiv p F).map_add x.1 y.1)

/-! ## 4. 装配：以 **Procesi 1967** 为带名假设

  论文 `rem:procesi-geometric`（`:592`）：\(Z_H(F,p^2)\cong F(M|_H)^H\)。
  该同构是 Procesi 1967 的定理，本档按裁定**作带名假设**传入（同 EM 判据／Saltman Cor 3.13 款）。 -/

/-- **装配（G2 主定理）**：设 \(Z_H(F,p^2)\cong F(M|_\theta)^H\)（**Procesi 1967，带名假设**），
则由子群步得 \(Z_H(F,p^2)\cong F(M_{\mathrm{rep}})^H\)。 -/
theorem ZH_iso (F : Type*) [Field F]
    (Z : Type*) [Field Z]
    (hProcesi : Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (ABGV52.P.Hp p)
      ↥(LinearMap.ker (phiFun p))))) :
    Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (ABGV52.P.Hp p)
      ↥(LinearMap.ker (ABGV52.P.pi p)))) := by
  obtain ⟨e⟩ := hProcesi
  exact ⟨e.trans (invariantsEquiv p F)⟩

/-! ## 5. 公理闸门 -/

#print axioms uniqueSums_finsupp
#print axioms uniqueSums_monoidAlgebra
#print axioms uniqueSums_zomTensor
#print axioms uniqueSums_kerPhi
#print axioms uniqueSums_kerPi
#print axioms kerMulEquiv
#print axioms latticeAlgEquiv_smul
#print axioms latticeFFEquiv_smul
#print axioms invariantsEquiv
#print axioms ZH_iso

end ABGV52.G
