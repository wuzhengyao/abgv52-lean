/-
  ABGV-5.2 —— **G 档 G1c：限制识别 \(M|_\theta \cong M_{\mathrm{rep}}\)**（承重）

  闸门读数（2026-09-30，已过闸）：lean rc=0／error=0／无 sorry；
  `#print axioms` 三条均为 `[propext, Classical.choice, Quot.sound]`。
  补记（2026-10-09）：§9 打包后 `#print axioms` 共 **9 条**，全三标准（切片 48:51 复跑绿）。

  论文锚（`raw/ABGV-5.2-resolution.tex`）：
    `:624` prop:U-restrict-canonical —— \(U|_H \cong \mathbb Z[H]\)，\(e_{h\cdot\omega_0}\mapsto h\)；
    `:666` prop:tensor-reg-ZH —— \(\mathbb Z[H]\otimes_{\mathbb Z}\mathbb Z[H]\cong\mathbb Z[H]^{\oplus 9}\)（**显式对应**
           \(x\otimes g\mapsto\)「\(g\)-坐标取 \(x\)」，左式取对角作用、右式取左乘配坐标置换）；
    `:716` prop:procesi-H —— 在上述识别下 \(\varphi\) **变成** \(\pi|_H:\mathbb Z[H]^{\oplus 9}\to I[H]\)。

  本件施工（\(H = C_p\times C_p\) 见 P1，\(\Omega = \mathrm{Fin}(p^2)\) 见 G1b）：
    ① 取双射 \(e : H \simeq \Omega\)（＝论文选基点 \(\omega_0\)），沿 \(e\) 搬运左乘得 **正则作用**
       `MulAction (Hp p) (OmegaP p)` 与嵌入 \(\theta : H\hookrightarrow S_{p^2}\)；
    ② \(M|_\theta\) 作 `Rep ℤ (Hp p)`（G1b 的核 \(\ker\varphi\) 承搬运后的作用）；
    ③ 显式同构 \(\Phi:\mathbb Z[\Omega]\otimes\mathbb Z[\Omega]\cong Vp\)，证 \(G\)-等变且 \(\pi\circ\Phi=-\varphi\)；
    ④ 于是 \(\Phi\) 限制为 `Rep ℤ (Hp p)` 同构 \(M|_\theta \cong M_{\mathrm{rep}}\)（P1 的 \(\ker\pi\)）。
    ⑤ **`prop:tensor-reg-ZH` 单一声明打包（§9，2026-10-09 补）**：`tensorDiagRepr`／`tensorDiagRep`
       ＋等变 `PhiT_comm` ⟹ `PhiRepIso : tensorDiagRep ≅ VRep`（论文 `:666` 的 `Rep` 级单声明）。
-/
import ABGV52.P1_ABGV52
import ABGV52.G1b_ABGV52
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RepresentationTheory.Intertwining

open scoped TensorProduct
open CategoryTheory

namespace ABGV52.G

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 双射 \(e : H \simeq \Omega\) 与正则作用、嵌入 \(\theta\) -/

/-- 取定一个双射 \(e : H \simeq \Omega\)（论文「选基点 \(\omega_0\)」的 Lean 化身）。
两端基数都是 \(p^2\)（P1 的 `card_Hp`）。 -/
noncomputable def eHO : ABGV52.P.Hp p ≃ OmegaP p :=
  Fintype.equivFinOfCardEq (ABGV52.P.card_Hp p)

/-- \(H\) 在 \(\Omega\) 上的**正则作用**：沿 `eHO` 搬运左乘。 -/
noncomputable instance mulActionHO : MulAction (ABGV52.P.Hp p) (OmegaP p) where
  smul h ω := eHO p (h * (eHO p).symm ω)
  one_smul ω := by
    show eHO p (1 * (eHO p).symm ω) = ω
    rw [one_mul, Equiv.apply_symm_apply]
  mul_smul a b ω := by
    show eHO p ((a * b) * (eHO p).symm ω)
      = eHO p (a * (eHO p).symm (eHO p (b * (eHO p).symm ω)))
    rw [mul_assoc, Equiv.symm_apply_apply]

/-- **正则嵌入** \(\theta : H\hookrightarrow S_{p^2}\)（＝上述作用的置换表示）。 -/
noncomputable def thetaH : ABGV52.P.Hp p →* Equiv.Perm (OmegaP p) :=
  MulAction.toPermHom (ABGV52.P.Hp p) (OmegaP p)

lemma thetaH_apply (h : ABGV52.P.Hp p) (ω : OmegaP p) :
    thetaH p h ω = eHO p (h * (eHO p).symm ω) := rfl

/-- \(e\) 是 \(H\)-等变双射（由构造）。 -/
lemma eHO_smul (h : ABGV52.P.Hp p) (x : ABGV52.P.Hp p) :
    eHO p (h * x) = h • eHO p x := by
  show eHO p (h * x) = eHO p (h * (eHO p).symm (eHO p x))
  rw [Equiv.symm_apply_apply]

/-- \(H\) 在 \(\mathbb Z[\Omega]\) 上的作用（＝沿 \(\theta\) 的限制）。 -/
noncomputable abbrev UH : Rep ℤ (ABGV52.P.Hp p) :=
  Rep.ofMulAction ℤ (ABGV52.P.Hp p) (OmegaP p)

/-- \(\theta\) 的置换作用与 `UH` 的作用一致：两者都是「按同一个置换重指标」。 -/
lemma U_rho_theta (h : ABGV52.P.Hp p) : (U p).ρ (thetaH p h) = (UH p).ρ h := rfl

/-! ## 2. \(M|_\theta\) 作为 `Rep ℤ (Hp p)` -/

lemma phiFun_ker_stable_H (h : ABGV52.P.Hp p) {x : (ZOm p) ⊗[ℤ] (ZOm p)}
    (hx : x ∈ LinearMap.ker (phiFun p)) :
    TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) x ∈ LinearMap.ker (phiFun p) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← U_rho_theta p h, phiFun_equivariant p (thetaH p h) x, hx, map_zero]

noncomputable def Mres_act (h : ABGV52.P.Hp p) (x : ↥(LinearMap.ker (phiFun p))) :
    ↥(LinearMap.ker (phiFun p)) :=
  ⟨TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) x.1, phiFun_ker_stable_H p h x.2⟩

noncomputable instance : DistribMulAction (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p)) where
  smul h x := Mres_act p h x
  one_smul x := by
    apply Subtype.ext
    show TensorProduct.map ((UH p).ρ (1 : ABGV52.P.Hp p))
      ((UH p).ρ (1 : ABGV52.P.Hp p)) x.1 = x.1
    rw [map_one]
    change TensorProduct.map (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p)
      (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) x.1 = x.1
    simp only [TensorProduct.map_id, LinearMap.id_apply]
  mul_smul a b x := by
    apply Subtype.ext
    show TensorProduct.map ((UH p).ρ (a * b)) ((UH p).ρ (a * b)) x.1
        = TensorProduct.map ((UH p).ρ a) ((UH p).ρ a)
            (TensorProduct.map ((UH p).ρ b) ((UH p).ρ b) x.1)
    rw [Rep.ρ_mul, TensorProduct.map_comp]
    rfl
  smul_zero h := by
    apply Subtype.ext
    show TensorProduct.map ((UH p).ρ h) ((UH p).ρ h)
      (0 : (ZOm p) ⊗[ℤ] (ZOm p)) = 0
    simp
  smul_add h x y := by
    apply Subtype.ext
    show TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) (x.1 + y.1)
        = TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) x.1
          + TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) y.1
    rw [map_add]

/-- **\(M|_\theta = \ker\varphi\) 承 \(H\)-作用**（论文 `:716` 的 \(M|_H\)）。 -/
noncomputable def Mres : Rep ℤ (ABGV52.P.Hp p) :=
  Rep.ofDistribMulAction ℤ (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p))

/-! ## 3. 群环侧的小工具（\(\mathbb Z[H]\) 的系数引理） -/

lemma coeff_sum_H {ι : Type*} [Fintype ι]
    (g : ι → MonoidAlgebra ℤ (ABGV52.P.Hp p)) :
    MonoidAlgebra.coeff (∑ i, g i) = ∑ i, MonoidAlgebra.coeff (g i) :=
  map_sum ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) g Finset.univ

lemma coeff_smul_H (m : ℤ) (g : MonoidAlgebra ℤ (ABGV52.P.Hp p)) :
    MonoidAlgebra.coeff (m • g) = m • MonoidAlgebra.coeff g :=
  map_smul ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) m g

lemma coeff_add_H (x y : MonoidAlgebra ℤ (ABGV52.P.Hp p)) :
    MonoidAlgebra.coeff (x + y) = MonoidAlgebra.coeff x + MonoidAlgebra.coeff y :=
  map_add ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) x y

/-- `Finsupp.sum_single` 的全集形式。 -/
lemma sum_single_univ_H (l : ABGV52.P.Hp p →₀ ℤ) :
    (∑ a : ABGV52.P.Hp p, Finsupp.single a (l a)) = l := by
  conv_rhs => rw [← Finsupp.sum_single l]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx, Finsupp.single_zero])).symm

/-- \(\mathbb Z[H]\) 的单点展开（G1b `self_eq_sum_single` 的 \(H\)-侧孪生）。 -/
lemma self_eq_sum_single_H (w : MonoidAlgebra ℤ (ABGV52.P.Hp p)) :
    w = ∑ a ∈ w.coeff.support, MonoidAlgebra.single a (w.coeff a) := by
  have h1 : w.coeff = ∑ a ∈ w.coeff.support, Finsupp.single a (w.coeff a) := by
    conv_lhs => rw [← Finsupp.sum_single w.coeff]
    rfl
  have key : (MonoidAlgebra.coeffLinearEquiv ℤ).symm w.coeff =
      ∑ a ∈ w.coeff.support, MonoidAlgebra.single a (w.coeff a) := by
    conv_lhs => rw [h1]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [LinearEquiv.symm_apply_eq, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single]
  have hw : w = (MonoidAlgebra.coeffLinearEquiv ℤ).symm w.coeff := by
    rw [← MonoidAlgebra.ofCoeff_coeff w]
    rfl
  conv_lhs => rw [hw, key]

/-- 单点展开的 `•` 形式（`π` 的展开要用）。 -/
lemma sum_coeff_smul_single_H (w : MonoidAlgebra ℤ (ABGV52.P.Hp p)) :
    (∑ a : ABGV52.P.Hp p, w.coeff a • MonoidAlgebra.single a (1 : ℤ)) = w := by
  refine MonoidAlgebra.coeff_injective ?_
  rw [coeff_sum_H]
  have h : ∀ a : ABGV52.P.Hp p,
      MonoidAlgebra.coeff (w.coeff a • MonoidAlgebra.single a (1 : ℤ)) =
        Finsupp.single a (w.coeff a) := by
    intro a
    rw [coeff_smul_H, MonoidAlgebra.coeff_single, Finsupp.smul_single', mul_one]
  simp only [h]
  exact sum_single_univ_H p w.coeff

/-! ## 4. 系数搬运 \(e_L : \mathbb Z[\Omega]\cong\mathbb Z[H]\) -/

/-- 系数层的搬运（\(e\) 的重指标）。 -/
noncomputable def eLF : (OmegaP p →₀ ℤ) ≃ₗ[ℤ] (ABGV52.P.Hp p →₀ ℤ) :=
  Finsupp.domLCongr (eHO p).symm

lemma eLF_apply (l : OmegaP p →₀ ℤ) (a : ABGV52.P.Hp p) :
    eLF p l a = l (eHO p a) := by
  rw [eLF, Finsupp.domLCongr_apply]
  show Finsupp.equivMapDomain (eHO p).symm l a = _
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]

/-- 群环层的搬运 \(e_L : \mathbb Z[\Omega]\cong\mathbb Z[H]\)。 -/
noncomputable def eL : ZOm p ≃ₗ[ℤ] MonoidAlgebra ℤ (ABGV52.P.Hp p) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).trans
    ((eLF p).trans (MonoidAlgebra.coeffLinearEquiv ℤ).symm)

lemma eL_coeff (f : ZOm p) (a : ABGV52.P.Hp p) :
    (eL p f).coeff a = MonoidAlgebra.coeff f (eHO p a) := by
  have h1 : (eL p f).coeff = (eLF p) (MonoidAlgebra.coeff f) := by
    rw [eL, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    exact LinearEquiv.apply_symm_apply (MonoidAlgebra.coeffLinearEquiv ℤ)
      (eLF p (MonoidAlgebra.coeff f))
  rw [h1, eLF_apply]

/-- \(\mathbb Z[H]\)-索引与 \(\mathbb Z[\Omega]\)-索引经 \(e\) 互换的单点读数。 -/
lemma single_eHO (ω : OmegaP p) (a : ABGV52.P.Hp p) :
    Finsupp.single ω (1 : ℤ) (eHO p a) =
      Finsupp.single ((eHO p).symm ω) (1 : ℤ) a := by
  by_cases h : a = (eHO p).symm ω
  · rw [h, Equiv.apply_symm_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (a := ω) (a' := eHO p a) (b := (1 : ℤ))
        (fun hc => h (by rw [← hc, Equiv.symm_apply_apply])),
      Finsupp.single_eq_of_ne (a := (eHO p).symm ω) (a' := a) (b := (1 : ℤ)) h]

lemma eL_single (ω : OmegaP p) :
    eL p (MonoidAlgebra.single ω (1 : ℤ)) =
      MonoidAlgebra.single ((eHO p).symm ω) (1 : ℤ) := by
  refine MonoidAlgebra.coeff_injective ?_
  ext a
  rw [eL_coeff, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single]
  exact single_eHO p ω a

lemma eL_aug (f : ZOm p) : ABGV52.P.aug p (eL p f) = augF p f := by
  rw [ABGV52.P.aug_eq_sum_coeff, augF_apply]
  simp_rw [eL_coeff]
  exact Equiv.sum_comp (eHO p) (fun ω : OmegaP p => MonoidAlgebra.coeff f ω)

/-- \(e_L\) 与 \(H\)-作用交换（群环侧用 P1 的 `lmul`）。 -/
lemma eL_lmul (h : ABGV52.P.Hp p) (f : ZOm p) :
    eL p ((UH p).ρ h f) = ABGV52.P.lmul p h (eL p f) := by
  refine MonoidAlgebra.coeff_injective ?_
  ext a
  rw [eL_coeff, Representation.coeff_ofMulAction, ← eHO_smul p h⁻¹ a, ← eL_coeff,
    ABGV52.P.lmul, MonoidAlgebra.coeff_single_mul_apply, one_mul]

/-! ## 5. 泛型系数工具（任意索引型 \(M\)） -/

section Generic
variable {M : Type*}

lemma coeff_sum_g {ι : Type*} [Fintype ι] (g : ι → MonoidAlgebra ℤ M) :
    MonoidAlgebra.coeff (∑ i, g i) = ∑ i, MonoidAlgebra.coeff (g i) :=
  map_sum ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) g Finset.univ

lemma coeff_smul_g (m : ℤ) (g : MonoidAlgebra ℤ M) :
    MonoidAlgebra.coeff (m • g) = m • MonoidAlgebra.coeff g :=
  map_smul ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) m g

lemma sum_single_univ_g [Fintype M] (l : M →₀ ℤ) :
    (∑ a : M, Finsupp.single a (l a)) = l := by
  conv_rhs => rw [← Finsupp.sum_single l]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx, Finsupp.single_zero])).symm

lemma sum_coeff_smul_single_g [Fintype M] (f : MonoidAlgebra ℤ M) :
    (∑ a : M, f.coeff a • MonoidAlgebra.single a (1 : ℤ)) = f := by
  have key : ∀ a : M, MonoidAlgebra.coeff (f.coeff a • MonoidAlgebra.single a (1 : ℤ))
      = Finsupp.single a (f.coeff a) := by
    intro a
    rw [coeff_smul_g, MonoidAlgebra.coeff_single, Finsupp.smul_single', mul_one]
  refine MonoidAlgebra.coeff_injective ?_
  rw [coeff_sum_g]
  rw [Finset.sum_congr rfl fun a _ => key a]
  exact sum_single_univ_g f.coeff

end Generic

/-! ## 6. 显式同构 \(\Phi : \mathbb Z[\Omega]\otimes\mathbb Z[\Omega]\cong Vp\) -/

/-- \(\Phi\) 的双线性前身：\(f\otimes g\mapsto\bigl(a\mapsto (e_Lf)(a)\cdot e_L(g)\bigr)\)。 -/
noncomputable def PhiBilin : ZOm p →ₗ[ℤ] ZOm p →ₗ[ℤ] ABGV52.P.Vp p where
  toFun f :=
    { toFun := fun g a => (eL p f).coeff a • (eL p g)
      map_add' := fun g₁ g₂ => by
        funext a
        simp only [Pi.add_apply, map_add, smul_add]
      map_smul' := fun m g => by
        funext a
        rw [Pi.smul_apply, (eL p).map_smul, smul_comm]
        rfl }
  map_add' f₁ f₂ := by
    refine LinearMap.ext fun g => funext fun a => ?_
    change (eL p (f₁ + f₂)).coeff a • (eL p g)
        = (eL p f₁).coeff a • (eL p g) + (eL p f₂).coeff a • (eL p g)
    rw [show (eL p (f₁ + f₂)).coeff a
        = (eL p f₁).coeff a + (eL p f₂).coeff a from by
      rw [(eL p).map_add, coeff_add_H, Finsupp.add_apply]]
    exact add_smul _ _ _
  map_smul' m f := by
    refine LinearMap.ext fun g => funext fun a => ?_
    change (eL p (m • f)).coeff a • (eL p g)
        = (RingHom.id ℤ) m • ((eL p f).coeff a • (eL p g))
    rw [show (eL p (m • f)).coeff a = m * (eL p f).coeff a from by
      rw [(eL p).map_smul, coeff_smul_H, Finsupp.smul_apply]
      simp]
    rw [mul_smul]
    rfl

noncomputable def PhiLM : (ZOm p) ⊗[ℤ] (ZOm p) →ₗ[ℤ] ABGV52.P.Vp p :=
  TensorProduct.lift (PhiBilin p)

lemma PhiLM_tmul (f g : ZOm p) (a : ABGV52.P.Hp p) :
    PhiLM p (f ⊗ₜ[ℤ] g) a = (eL p f).coeff a • (eL p g) :=
  congrFun (TensorProduct.lift.tmul f g) a

/-- \(\Phi\) 的显式逆：\(z\mapsto\sum_a e_{e(a)}\otimes e_L^{-1}(z_a)\)。 -/
noncomputable def PsiLM : ABGV52.P.Vp p →ₗ[ℤ] (ZOm p) ⊗[ℤ] (ZOm p) where
  toFun z := ∑ a : ABGV52.P.Hp p,
    MonoidAlgebra.single (eHO p a) (1 : ℤ) ⊗ₜ[ℤ] (eL p).symm (z a)
  map_add' z z' := by
    simp only [Pi.add_apply, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' m z := by
    simp only [Pi.smul_apply, map_smul, TensorProduct.tmul_smul, Finset.smul_sum]
    rfl

/-- 逆的另一半计算：\(\sum_a (e_Lf)(a)\cdot e_{e(a)} = f\)。 -/
lemma sum_eL_coeff_smul_single (f : ZOm p) :
    (∑ a : ABGV52.P.Hp p, (eL p f).coeff a • MonoidAlgebra.single (eHO p a) (1 : ℤ)) = f := by
  have h : ∀ a : ABGV52.P.Hp p,
      (eL p f).coeff a • MonoidAlgebra.single (eHO p a) (1 : ℤ)
        = MonoidAlgebra.coeff f (eHO p a) • MonoidAlgebra.single (eHO p a) (1 : ℤ) := by
    intro a
    rw [eL_coeff]
  rw [Finset.sum_congr rfl fun a _ => h a]
  rw [Equiv.sum_comp (eHO p) (fun ω : OmegaP p =>
    MonoidAlgebra.coeff f ω • MonoidAlgebra.single ω (1 : ℤ))]
  exact sum_coeff_smul_single_g f

/-- `Vp` 的第 `b` 个坐标投影。 -/
noncomputable def evalVp (b : ABGV52.P.Hp p) :
    ABGV52.P.Vp p →ₗ[ℤ] MonoidAlgebra ℤ (ABGV52.P.Hp p) where
  toFun z := z b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma sum_apply_Vp {ι : Type*} [Fintype ι] (g : ι → ABGV52.P.Vp p)
    (b : ABGV52.P.Hp p) : (∑ i, g i) b = ∑ i, g i b :=
  map_sum (evalVp p b) g Finset.univ

lemma PhiT_left_inv (z : ABGV52.P.Vp p) : PhiLM p (PsiLM p z) = z := by
    have hz : PsiLM p z = ∑ a : ABGV52.P.Hp p,
        MonoidAlgebra.single (eHO p a) (1 : ℤ) ⊗ₜ[ℤ] (eL p).symm (z a) := rfl
    rw [hz, map_sum]
    funext b
    rw [sum_apply_Vp p]
    have hterm : ∀ a : ABGV52.P.Hp p,
        (PhiLM p (MonoidAlgebra.single (eHO p a) (1 : ℤ) ⊗ₜ[ℤ] (eL p).symm (z a))) b
          = if a = b then z b else 0 := by
      intro a
      rw [PhiLM_tmul, eL_single, Equiv.symm_apply_apply, (eL p).apply_symm_apply,
        MonoidAlgebra.coeff_single]
      by_cases h : a = b
      · rw [if_pos h, h, Finsupp.single_eq_same, one_smul]
      · rw [if_neg h, Finsupp.single_eq_of_ne (a := a) (a' := b) (b := (1 : ℤ))
          (Ne.symm h), zero_smul]
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_ite_eq']
    simp

lemma PhiT_right_inv (x : (ZOm p) ⊗[ℤ] (ZOm p)) : PsiLM p (PhiLM p x) = x := by
    induction x using TensorProduct.induction_on with
    | zero =>
        have h0 : PhiLM p (0 : (ZOm p) ⊗[ℤ] (ZOm p)) = 0 := map_zero _
        rw [h0]
        simp [PsiLM]
    | tmul f g =>
        have hz : PsiLM p (PhiLM p (f ⊗ₜ[ℤ] g)) = ∑ a : ABGV52.P.Hp p,
            MonoidAlgebra.single (eHO p a) (1 : ℤ) ⊗ₜ[ℤ]
              ((eL p).symm ((PhiLM p (f ⊗ₜ[ℤ] g)) a)) := rfl
        rw [hz]
        simp only [PhiLM_tmul, (eL p).symm.map_smul, (eL p).symm_apply_apply,
          TensorProduct.tmul_smul]
        exact ((TensorProduct.sum_tmul Finset.univ
            (fun x : ABGV52.P.Hp p =>
              (eL p f).coeff x • MonoidAlgebra.single (eHO p x) (1 : ℤ)) g).symm).trans
          (congrArg (fun w => w ⊗ₜ[ℤ] g) (sum_eL_coeff_smul_single p f))
    | add x y hx hy =>
        change PsiLM p (PhiLM p (x + y)) = x + y
        rw [map_add (PhiLM p), (PsiLM p).map_add, hx, hy]

/-- **论文 `:666`＋`:716` 的显式识别**：\(\Phi\) 是 \(H\)-模同构
\(\mathbb Z[\Omega]^{\otimes 2}\cong Vp\)（等变性与 \(\pi\circ\Phi=-\varphi\) 见下节）。 -/
noncomputable def PhiT : (ZOm p) ⊗[ℤ] (ZOm p) ≃ₗ[ℤ] ABGV52.P.Vp p where
  toFun := PhiLM p
  invFun := PsiLM p
  left_inv := PhiT_right_inv p
  right_inv := PhiT_left_inv p
  map_add' := (PhiLM p).map_add
  map_smul' := (PhiLM p).map_smul

/-! ## 7. \(\Phi\) 把 \(\varphi\) 送成 \(-\pi\)，且与 \(H\)-作用交换 -/

lemma pi_apply (z : ABGV52.P.Vp p) :
    ABGV52.P.pi p z = ∑ b : ABGV52.P.Hp p,
      (z b - ABGV52.P.aug p (z b) • MonoidAlgebra.single b (1 : ℤ)) := by
  rw [ABGV52.P.pi, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun b _ => ABGV52.P.piTerm_apply p b z

/-- **论文 `:716` 的核心识别**：在 \(\Phi\) 下 \(\varphi\) 变成 \(-\pi\)。 -/
lemma pi_PhiLM (x : (ZOm p) ⊗[ℤ] (ZOm p)) :
    ABGV52.P.pi p (PhiLM p x) = -eL p (phiFun p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [pi_apply, phiFun_tmul]
      have hterm : ∀ b : ABGV52.P.Hp p,
          (PhiLM p (f ⊗ₜ[ℤ] g) b
              - ABGV52.P.aug p (PhiLM p (f ⊗ₜ[ℤ] g) b)
                • MonoidAlgebra.single b (1 : ℤ))
            = (eL p f).coeff b • (eL p g)
              - (ABGV52.P.aug p (eL p g) * (eL p f).coeff b)
                • MonoidAlgebra.single b (1 : ℤ) := by
        intro b
        rw [PhiLM_tmul, ABGV52.P.aug_smul',
          mul_comm ((eL p f).coeff b) (ABGV52.P.aug p (eL p g))]
      rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_sub_distrib]
      have h1 : (∑ b : ABGV52.P.Hp p, (eL p f).coeff b • (eL p g))
          = ABGV52.P.aug p (eL p f) • (eL p g) := by
        rw [← Finset.sum_smul, ABGV52.P.aug_eq_sum_coeff]
      have h2 : (∑ b : ABGV52.P.Hp p,
            (ABGV52.P.aug p (eL p g) * (eL p f).coeff b)
              • MonoidAlgebra.single b (1 : ℤ))
          = ABGV52.P.aug p (eL p g) • (eL p f) := by
        rw [← sum_coeff_smul_single_H p (ABGV52.P.aug p (eL p g) • (eL p f))]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [coeff_smul_H, Finsupp.smul_apply]
        simp
      have h3 : -eL p ((augF p) g • f - (augF p) f • g)
          = (augF p f) • (eL p g) - (augF p g) • (eL p f) := by
        rw [show (eL p) ((augF p) g • f - (augF p) f • g)
              = (eL p) ((augF p) g • f) - (eL p) ((augF p) f • g) from
            map_sub (eL p).toLinearMap _ _,
          neg_sub,
          show (eL p) ((augF p) f • g) = (augF p f) • (eL p g) from
            map_smul (eL p).toLinearMap _ _,
          show (eL p) ((augF p) g • f) = (augF p g) • (eL p f) from
            map_smul (eL p).toLinearMap _ _]
      rw [h1, h2, eL_aug, eL_aug, h3]
  | add x y hx hy =>
      rw [map_add (PhiLM p), map_add (ABGV52.P.pi p), hx, hy, map_add (phiFun p),
        show (eL p) (phiFun p x + phiFun p y)
            = (eL p) (phiFun p x) + (eL p) (phiFun p y) from
          map_add (eL p).toLinearMap _ _,
        neg_add]

lemma PhiLM_equivariant (h : ABGV52.P.Hp p) (x : (ZOm p) ⊗[ℤ] (ZOm p)) :
    PhiLM p (TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) x) = ABGV52.P.act p h (PhiLM p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, ABGV52.P.act_zero]
  | tmul f g =>
      funext b
      rw [TensorProduct.map_tmul, PhiLM_tmul, ABGV52.P.act_apply, PhiLM_tmul,
        eL_lmul, eL_lmul, ABGV52.P.lmul_smul, ABGV52.P.lmul,
        MonoidAlgebra.coeff_single_mul_apply, one_mul]
  | add x y hx hy => simp only [map_add, ABGV52.P.act_add, hx, hy]

/-! ## 8. 核同构 \(M|_\theta\cong M_{\mathrm{rep}}\) -/

noncomputable def kerEquiv :
    ↥(LinearMap.ker (phiFun p)) ≃ₗ[ℤ] ↥(LinearMap.ker (ABGV52.P.pi p)) where
  toFun x := ⟨PhiLM p x.1, by
    rw [LinearMap.mem_ker, pi_PhiLM, LinearMap.mem_ker.mp x.2, map_zero, neg_zero]⟩
  invFun y := ⟨PsiLM p y.1, by
    rw [LinearMap.mem_ker]
    have h := pi_PhiLM p (PsiLM p y.1)
    rw [PhiT_left_inv p y.1, LinearMap.mem_ker.mp y.2] at h
    exact (eL p).injective (by rw [map_zero]; exact neg_eq_zero.mp h.symm)⟩
  left_inv x := Subtype.ext (PhiT_right_inv p x.1)
  right_inv y := Subtype.ext (PhiT_left_inv p y.1)
  map_add' x y := Subtype.ext (map_add (PhiLM p) x.1 y.1)
  map_smul' m x := Subtype.ext (map_smul (PhiLM p) m x.1)

lemma kerEquiv_comm (h : ABGV52.P.Hp p) :
    (kerEquiv p).toLinearMap ∘ₗ (Mres p).ρ h
      = (ABGV52.P.M_rep p).ρ h ∘ₗ (kerEquiv p).toLinearMap := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact PhiLM_equivariant p h x.1

/-- **G1c 主定理**：\(M|_\theta\cong M_{\mathrm{rep}}\)（论文 `:716` 的 \(M|_H\) ＝ P1 的 \(\ker\pi\)）。 -/
noncomputable def Miso : Mres p ≅ ABGV52.P.M_rep p :=
  Rep.mkIso (Representation.Equiv.mk
    (ρ := (Mres p).ρ) (σ := (ABGV52.P.M_rep p).ρ) (kerEquiv p) (kerEquiv_comm p))

/-! ## 9. `prop:tensor-reg-ZH` 的单一声明打包（论文 `:666` 的 `Rep` 级同构；2026-10-09 补）

论文 `:666`（`prop:tensor-reg-ZH`）：\(\mathbb Z[H]\otimes_{\mathbb Z}\mathbb Z[H]\cong\mathbb Z[H]^{\oplus 9}\)
（左式对角作用）。本节把 §6–§7 的内容（`PhiT` ＋ `PhiLM_equivariant`）打包为**单一** `Rep` 同构
声明 `PhiRepIso`——\(\Omega\)-侧显式模型（`ZOm ⊗ ZOm ≅ Vp`）；\(H\)-侧字面形式经 §3–§4 的
`e_L` 等变搬运即得。 -/

/-- 对角作用 \(h\cdot(x\otimes y)=hx\otimes hy\) 的表示（两因子同用 `UH` 的 `ρ`）。 -/
noncomputable def tensorDiagRepr :
    Representation ℤ (ABGV52.P.Hp p) ((ZOm p) ⊗[ℤ] (ZOm p)) where
  toFun h := TensorProduct.map ((UH p).ρ h) ((UH p).ρ h)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    change (TensorProduct.map ((UH p).ρ (1 : ABGV52.P.Hp p))
      ((UH p).ρ (1 : ABGV52.P.Hp p))) x = x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul f g =>
        rw [TensorProduct.map_tmul, map_one]
        rfl
    | add x y hx hy => rw [map_add, hx, hy]
  map_mul' a b := by
    refine LinearMap.ext fun x => ?_
    change (TensorProduct.map ((UH p).ρ (a * b)) ((UH p).ρ (a * b))) x
      = (TensorProduct.map ((UH p).ρ a) ((UH p).ρ a))
          ((TensorProduct.map ((UH p).ρ b) ((UH p).ρ b)) x)
    have h : ∀ y : ZOm p, ((UH p).ρ (a * b)) y = ((UH p).ρ a) (((UH p).ρ b) y) := by
      intro y
      rw [map_mul]
      rfl
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul f g =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
          h f, h g]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- 对角作用下的 \(\mathbb Z[\Omega]^{\otimes 2}\) 作为 `Rep ℤ (Hp p)`。 -/
noncomputable abbrev tensorDiagRep : Rep ℤ (ABGV52.P.Hp p) :=
  Rep.of (tensorDiagRepr p)

/-- \(\Phi\) 与作用交换（由 `PhiLM_equivariant` 逐点读出）。 -/
lemma PhiT_comm (h : ABGV52.P.Hp p) :
    (PhiT p).toLinearMap ∘ₗ (tensorDiagRepr p h)
      = ((ABGV52.P.VRep p).ρ h) ∘ₗ (PhiT p).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  show PhiLM p (TensorProduct.map ((UH p).ρ h) ((UH p).ρ h) x)
      = ABGV52.P.act p h (PhiLM p x)
  exact PhiLM_equivariant p h x

/-- **`prop:tensor-reg-ZH` 打包（论文 `:666`）**：对角作用下的
\(\mathbb Z[\Omega]^{\otimes 2} \cong Vp = \mathbb Z[H]^{\oplus p^2}\)
作为 `Rep ℤ (Hp p)` 同构的单一声明。 -/
noncomputable def PhiRepIso : tensorDiagRep p ≅ ABGV52.P.VRep p :=
  Rep.mkIso (Representation.Equiv.mk
    (ρ := tensorDiagRepr p) (σ := (ABGV52.P.VRep p).ρ) (PhiT p) (PhiT_comm p))

/-! ## 10. 公理闸门 -/

#print axioms pi_PhiLM
#print axioms PhiLM_equivariant
#print axioms kerEquiv
#print axioms kerEquiv_comm
#print axioms Miso
#print axioms tensorDiagRepr
#print axioms tensorDiagRep
#print axioms PhiT_comm
#print axioms PhiRepIso

end ABGV52.G
