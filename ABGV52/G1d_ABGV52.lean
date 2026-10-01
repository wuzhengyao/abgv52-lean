/-
  ABGV-5.2 —— **G 档 G1d：θ-无关性**（论文 `prop:U-restrict-canonical` ＋ `prop:embedding-independence`）

  论文锚（`raw/ABGV-5.2-resolution.tex`）：
    `:624` **prop:U-restrict-canonical** —— 识别 `U|_H ≅ ℤ[H]`（`e_{h·ω₀} ↦ h`）在换基点下
          只差 `ℤ[H]` 的一个模自同构；故 `M|_H` 的**同构类**与基点无关；
    `:644` **prop:embedding-independence** —— 两个传递嵌入 `ι₁, ι₂` 给出
          `M|_{ι₁(H)} ≅ M|_{ι₂(H)}`（同为 `ℤ[H]`-模）。

  本件施工（参数 \(p\)）：
    * 把 G1c 的构造**对基点参数化**：`e : H ≃ Ω` ⟹ 正则作用 `actOf e` ⟹ `UOf e` ⟹ `MresOf e`；
    * 对任意两基点 `e₁ e₂`，用 `σ := e₂ ∘ e₁.symm ∈ Perm Ω` 诱导的搬运 `tauLin` 把
      \(e_1\)-作用共轭成 \(e_2\)-作用，证 `tauLin` 与 \(\varphi\) 交换；
    * 于是 `tauLin ⊗ tauLin` 限制为 **`MresOf e₁ ≅ MresOf e₂`**（＝ `:644`）；
    * 复合 G1c 的 `Miso` 得 **`MresOf e ≅ M_rep`**（对**任意**基点），即 `:624` 的「同构类与基点无关」。

  工程注：`↑(UOf p e)` 与 `ZOm p` 虽 defeq，但**混用两侧会触发 `Module ℤ` 实例菱形**
  （实测 `TensorProduct.map` 处报 `Int.instSemiring` vs `Int.instCommSemiring.toSemiring`）；
  故凡涉及 `UOf` 侧的等变性一律**就地重证**（`augF_smul_Of`／`phiFun_equivariant_Of`），
  不经 `U` 侧的 `phiFun_equivariant` 转接。
-/
import ABGV52.G1c_ABGV52
import ABGV52.G2p_ABGV52

open scoped TensorProduct
open CategoryTheory

namespace ABGV52.G

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 对基点参数化的构造 -/

/-- 由双射 `e : H ≃ Ω` 搬运左乘得的**正则作用**（显式结构，便于参数化）。 -/
noncomputable def actOf (e : ABGV52.P.Hp p ≃ OmegaP p) :
    MulAction (ABGV52.P.Hp p) (OmegaP p) where
  smul h ω := e (h * e.symm ω)
  one_smul ω := by
    show e (1 * e.symm ω) = ω
    rw [one_mul, Equiv.apply_symm_apply]
  mul_smul a b ω := by
    show e ((a * b) * e.symm ω) = e (a * e.symm (e (b * e.symm ω)))
    rw [mul_assoc, Equiv.symm_apply_apply]

/-- 核对：`eHO` 处与 G1c 的实例一致（构造逐字相同）。 -/
lemma actOf_eHO : actOf p (eHO p) = mulActionHO p := rfl

/-- `H` 在 `ℤ[Ω]` 上的参数化作用（**`abbrev`**：载体须对 elaborator 透明，否则与 `ZOm p`
混用时报「`↑(UOf p e)` vs `ZOm p`」型错误）。 -/
noncomputable abbrev UOf (e : ABGV52.P.Hp p ≃ OmegaP p) : Rep ℤ (ABGV52.P.Hp p) :=
  letI := actOf p e
  Rep.ofMulAction ℤ (ABGV52.P.Hp p) (OmegaP p)

/-- 参数化置换 `θ(e)(h)`。 -/
noncomputable def permOf (e : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p) :
    Equiv.Perm (OmegaP p) :=
  letI := actOf p e
  MulAction.toPermHom (ABGV52.P.Hp p) (OmegaP p) h

/-- **增广在参数化作用下不变**（G1c 的 `augF_smul` 之参数化）。 -/
lemma augF_smul_Of (e : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p) (f : ZOm p) :
    augF p ((UOf p e).ρ h f) = augF p f := by
  letI := actOf p e
  rw [augF_apply, augF_apply]
  have hh : ∀ a : OmegaP p, MonoidAlgebra.coeff ((UOf p e).ρ h f) a
      = MonoidAlgebra.coeff f (h⁻¹ • a) :=
    fun a => Representation.coeff_ofMulAction h f a
  simp only [hh]
  exact Equiv.sum_comp (MulAction.toPerm h⁻¹)
    (fun a : OmegaP p => MonoidAlgebra.coeff f a)

/-- **\(\varphi\) 在参数化作用下等变**（G1c 的 `phiFun_equivariant` 之参数化）。 -/
lemma phiFun_equivariant_Of (e : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p)
    (x : ↑(UOf p e) ⊗[ℤ] ↑(UOf p e)) :
    phiFun p (TensorProduct.map ((UOf p e).ρ h) ((UOf p e).ρ h) x)
      = (UOf p e).ρ h (phiFun p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [TensorProduct.map_tmul, phiFun_tmul, phiFun_tmul, augF_smul_Of, augF_smul_Of]
      conv_rhs => rw [map_sub, map_smul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 核稳定性（参数化）。 -/
lemma ker_stable_Of (e : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p)
    {x : ↑(UOf p e) ⊗[ℤ] ↑(UOf p e)} (hx : x ∈ LinearMap.ker (phiFun p)) :
    TensorProduct.map ((UOf p e).ρ h) ((UOf p e).ρ h) x ∈ LinearMap.ker (phiFun p) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [phiFun_equivariant_Of p e h x, hx, map_zero]

/-- `M|_θ(e) = ker φ` 承参数化作用（对角作用）。 -/
noncomputable def MresRepOf (e : ABGV52.P.Hp p ≃ OmegaP p) :
    Representation ℤ (ABGV52.P.Hp p) ↥(LinearMap.ker (phiFun p)) where
  toFun h :=
    { toFun := fun x => ⟨TensorProduct.map ((UOf p e).ρ h) ((UOf p e).ρ h) x.1,
        ker_stable_Of p e h x.2⟩
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
      map_smul' := fun m x => Subtype.ext (map_smul _ m x.1) }
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show TensorProduct.map ((UOf p e).ρ 1) ((UOf p e).ρ 1) x.1 = x.1
    rw [map_one]
    change TensorProduct.map (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p)
      (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) x.1 = x.1
    simp only [TensorProduct.map_id, LinearMap.id_apply]
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show TensorProduct.map ((UOf p e).ρ (a * b)) ((UOf p e).ρ (a * b)) x.1
        = TensorProduct.map ((UOf p e).ρ a) ((UOf p e).ρ a)
            (TensorProduct.map ((UOf p e).ρ b) ((UOf p e).ρ b) x.1)
    rw [Rep.ρ_mul, TensorProduct.map_comp]
    rfl

/-- **参数化的限制** `M|_θ(e)`。 -/
noncomputable abbrev MresOf (e : ABGV52.P.Hp p ≃ OmegaP p) : Rep ℤ (ABGV52.P.Hp p) :=
  Rep.of (MresRepOf p e)

/-- 基点取 `eHO` 时与 G1c 的 `Mres` 同构（同构取恒等）。 -/
noncomputable def MresOf_iso_Mres : MresOf p (eHO p) ≅ Mres p :=
  Rep.mkIso (Representation.Equiv.mk (ρ := (MresOf p (eHO p)).ρ) (σ := (Mres p).ρ)
    (LinearEquiv.refl ℤ ↥(LinearMap.ker (phiFun p))) (by intro h; rfl))

/-! ## 2. \(\sigma\)-搬运：把 \(e_1\)-作用共轭成 \(e_2\)-作用 -/

/-- 连接两基点的 `Ω`-置换 \(\sigma = e_2\circ e_1^{-1}\)。 -/
noncomputable def sigmaOf (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) : OmegaP p ≃ OmegaP p :=
  (e₁.symm).trans e₂

lemma sigmaOf_symm (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) :
    (sigmaOf p e₁ e₂).symm = (e₂.symm).trans e₁ := rfl

/-- \(\sigma\) 诱导的 `ℤ[Ω]` 线性等价（`single ω 1 ↦ single (σ ω) 1`）。
用 mathlib 自带的 `MonoidAlgebra.mapDomainLinearEquiv`（`Rep` 层面的搬运就是它）。 -/
noncomputable def tauLin (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) : ZOm p ≃ₗ[ℤ] ZOm p :=
  MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ (sigmaOf p e₁ e₂)

lemma tauLin_coeff (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (f : ZOm p) (ω : OmegaP p) :
    (tauLin p e₁ e₂ f).coeff ω
      = MonoidAlgebra.coeff f ((sigmaOf p e₁ e₂).symm ω) := by
  rw [tauLin, MonoidAlgebra.coeff_mapDomainLinearEquiv]
  exact Finsupp.equivMapDomain_apply (sigmaOf p e₁ e₂) (MonoidAlgebra.coeff f) ω

/-- 往返回（合成律）：`τ₂₁ ∘ τ₁₂ = id`（逐系数）。 -/
lemma tauLin_comp_apply (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (f : ZOm p) :
    tauLin p e₂ e₁ (tauLin p e₁ e₂ f) = f := by
  refine MonoidAlgebra.coeff_injective ?_
  ext ω
  rw [tauLin_coeff, tauLin_coeff]
  congr 1
  rw [sigmaOf_symm, sigmaOf_symm]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- 搬运在张量上诱导的线性映射 `τ ⊗ τ`。
**唯一**一处 `TensorProduct.map` 与 `LinearEquiv` 的强制相遇处——把脆弱的实例统一
（`Module ℤ (ZOm ⊗ ZOm)` 菱形）与强制解析都隔离在此，其余引理一律经 `tauT` 说话。 -/
noncomputable def tauT (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) :
    (ZOm p) ⊗[ℤ] (ZOm p) →ₗ[ℤ] (ZOm p) ⊗[ℤ] (ZOm p) :=
  TensorProduct.map (tauLin p e₁ e₂).toLinearMap (tauLin p e₁ e₂).toLinearMap

@[simp] lemma tauT_tmul (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (f g : ZOm p) :
    tauT p e₁ e₂ (f ⊗ₜ[ℤ] g) = tauLin p e₁ e₂ f ⊗ₜ[ℤ] tauLin p e₁ e₂ g := by
  rw [tauT]
  exact TensorProduct.map_tmul _ _ f g

/-- 往返回（张量版）。 -/
lemma tauT_comp (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (v : (ZOm p) ⊗[ℤ] (ZOm p)) :
    tauT p e₂ e₁ (tauT p e₁ e₂ v) = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [tauT_tmul]
      rw [tauLin_comp_apply, tauLin_comp_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `ρ` 的系数读数（参数化）：一个 `letI` 隔离，避免两侧实例互斥。 -/
lemma UOf_rho_coeff (e : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p) (f : ZOm p)
    (a : OmegaP p) :
    MonoidAlgebra.coeff ((UOf p e).ρ h f) a
      = MonoidAlgebra.coeff f (e (h⁻¹ * e.symm a)) := by
  letI := actOf p e
  exact Representation.coeff_ofMulAction h f a

/-- **`tauLin` 与 `φ` 交换**（在基向量上）⟹ 把 `ker φ` 送到 `ker φ`。 -/
lemma tauLin_aug (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (f : ZOm p) :
    augF p (tauLin p e₁ e₂ f) = augF p f := by
  rw [augF_apply, augF_apply]
  simp only [tauLin_coeff]
  exact Equiv.sum_comp (sigmaOf p e₁ e₂).symm
    (fun a : OmegaP p => MonoidAlgebra.coeff f a)

/-- **\(\tau\) 把 \(e_1\)-作用共轭成 \(e_2\)-作用**。 -/
lemma tauLin_equivariant (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p)
    (f : ZOm p) :
    tauLin p e₁ e₂ ((UOf p e₁).ρ h f) = (UOf p e₂).ρ h (tauLin p e₁ e₂ f) := by
  refine MonoidAlgebra.coeff_injective ?_
  ext ω
  rw [tauLin_coeff, UOf_rho_coeff, UOf_rho_coeff, tauLin_coeff]
  congr 1
  rw [sigmaOf_symm]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- **`φ` 在 `τ ⊗ τ` 下不变**（`φ (τ⊗τ x) = τ (φ x)`）。 -/
lemma tauLin_phi (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p)
    (x : (ZOm p) ⊗[ℤ] (ZOm p)) :
    phiFun p (tauT p e₁ e₂ x) = tauLin p e₁ e₂ (phiFun p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [tauT_tmul, phiFun_tmul, phiFun_tmul, tauLin_aug, tauLin_aug]
      conv_rhs => rw [map_sub, map_smul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ## 3. 主定理：θ-无关性 -/

/-- `τ ⊗ τ` 限制到 `ker φ` 上的线性等价。 -/
noncomputable def kerTauEquiv (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) :
    ↥(LinearMap.ker (phiFun p)) ≃ₗ[ℤ] ↥(LinearMap.ker (phiFun p)) where
  toFun x := ⟨tauT p e₁ e₂ x.1, by
    rw [LinearMap.mem_ker, tauLin_phi, LinearMap.mem_ker.mp x.2, map_zero]⟩
  invFun y := ⟨tauT p e₂ e₁ y.1, by
    rw [LinearMap.mem_ker, tauLin_phi, LinearMap.mem_ker.mp y.2, map_zero]⟩
  left_inv x := by
    obtain ⟨v, _⟩ := x
    apply Subtype.ext
    show tauT p e₂ e₁ (tauT p e₁ e₂ v) = v
    exact tauT_comp p e₁ e₂ v
  right_inv y := by
    obtain ⟨v, _⟩ := y
    apply Subtype.ext
    show tauT p e₁ e₂ (tauT p e₂ e₁ v) = v
    exact tauT_comp p e₂ e₁ v
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' m x := Subtype.ext (map_smul _ m x.1)

/-- 交换性（**环境张量上的纯等式**，不涉及子类型——避免诱导时把成员性证明卷进 motive）。 -/
lemma tauT_rho_comm (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p)
    (v : (ZOm p) ⊗[ℤ] (ZOm p)) :
    tauT p e₁ e₂ (TensorProduct.map ((UOf p e₁).ρ h) ((UOf p e₁).ρ h) v)
      = TensorProduct.map ((UOf p e₂).ρ h) ((UOf p e₂).ρ h) (tauT p e₁ e₂ v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [TensorProduct.map_tmul, tauT_tmul]
      rw [tauLin_equivariant p e₁ e₂ h f, tauLin_equivariant p e₁ e₂ h g]
  | add a b ha hb => simp only [map_add, ha, hb]

lemma kerTauEquiv_comm (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) (h : ABGV52.P.Hp p) :
    (kerTauEquiv p e₁ e₂).toLinearMap ∘ₗ (MresRepOf p e₁) h
      = (MresRepOf p e₂) h ∘ₗ (kerTauEquiv p e₁ e₂).toLinearMap := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact tauT_rho_comm p e₁ e₂ h x.1

/-- **θ-无关性（＝论文 `:644` `prop:embedding-independence`）**：
任意两基点给出的限制 \(M|_\theta\) 作为 `Rep ℤ (Hp p)` 同构。 -/
noncomputable def MresOf_iso (e₁ e₂ : ABGV52.P.Hp p ≃ OmegaP p) :
    MresOf p e₁ ≅ MresOf p e₂ :=
  Rep.mkIso (Representation.Equiv.mk (ρ := MresRepOf p e₁) (σ := MresRepOf p e₂)
    (kerTauEquiv p e₁ e₂) (kerTauEquiv_comm p e₁ e₂))

/-- **θ-无关性的可用形式（＝论文 `:624` 的「同构类与基点无关」）**：
**任意**基点给出的 \(M|_\theta\) 都与 P 档的 `M_rep` 同构。 -/
noncomputable def MresOf_iso_Mrep (e : ABGV52.P.Hp p ≃ OmegaP p) :
    MresOf p e ≅ ABGV52.P.M_rep p :=
  (MresOf_iso p e (eHO p)).trans ((MresOf_iso_Mres p).trans (Miso p))

/-! ## 4. 公理闸门 -/

#print axioms tauLin_coeff
#print axioms tauLin_comp_apply
#print axioms tauT
#print axioms tauT_tmul
#print axioms tauT_comp
#print axioms UOf_rho_coeff
#print axioms tauLin_aug
#print axioms tauLin_equivariant
#print axioms tauLin_phi
#print axioms kerTauEquiv
#print axioms tauT_rho_comm
#print axioms kerTauEquiv_comm
#print axioms MresOf_iso
#print axioms MresOf_iso_Mrep

end ABGV52.G
