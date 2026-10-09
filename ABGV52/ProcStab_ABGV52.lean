/-
  ABGV-5.2 —— **C 轨里程碑 M3：在 Procesi 数据上实例化 A 轨机器（消解桥 (c) 的 M3 假设）**

  背景。`ProcHyp_ABGV52.lean` 的桥 (c) `procesiHypStable_of_exact_of_ratOver` 把 M3
  （Lenstra (1.4) 的格层内容）作为**显式假设参数**。本件把 A 轨（`EMRouteS_ABGV52`）
  已交付的机器 `s2Interface_of_data'` 实例化到 Procesi 数据上，从而消解该假设。

  数据（蓝图 §3.2）：
    * `G := Hp p`（`C_p × C_p`，`Fintype`）；
    * `M := ↥(LinearMap.ker (G.phiFun p))`（M1 的核格，ℤ-秩 = p⁴ − p² + 1）；
    * `P := G.ZOm p = ℤ[Ω]`（`Ω = Fin (p*p)`）；
    * 基 `B := MonoidAlgebra.basis (G.OmegaP p) ℤ`，置换 `ρ := G.thetaH p`。

  三个目标的交付状态：
    ① **无条件**：`s2Interface_procesi` ＋ 基域搬运 `K0EquivInvariants` ＋
       `exists_ratOver_semiInvariants`（M3 的**半函数域（机器）形**：机器输出的
       `↥(l(N)^H)` 在 `↥(l(M)^H)` 上有理）；
    ② **具名件（目标 2 未解消）**：`TwoStepInterface` —— 对象层二步识别
       `F(M×P)^H ≅ (F[M][P])^H`（`EMRouteS` 偏差 3 ＝ 蓝图桥 b/T1）**未在 A 轨交付**；
       本件按「未证明者登记为具名命题 ＋ 类型锁定 ＋ 接线定理」的纪律落盘，并给出
       `twoStepInterface_of_ambient`：A 轨 T1 的环境同构（等变）一旦交付，本具名件即得；
    ③ **收口（模具名件版）**：`procesiHypStable_of_exact_of_twoStep`（C′ ＋ 具名件 ⟹ C″）。

  与蓝图的逐条偏差：
    ① 蓝图 §3.2 T2 的「先证 M3 再组装」被 A 轨机器的**直接实例化**取代：机器内部已含
       `W_fixed_extraction` ＋ `isRational_fixedPoints`（本件不再重复证明）。
    ② 目标 2 的**直和形**（`F(M ⊕ P)`）未解消：mathlib 的 `Sum` 上无 `AddCommGroup`
       实例；`ProcLat` 早已用 `×` 承载 `Mp2`（其头注登记同款偏离），本件沿用以 `×`
       形注册具名件（`ProcLat.Mp2 p` ＝ `↥(ker φ) × ZOm p`，ℚ-秩 p⁴+1）。
    ③ `ZOm p` 上的 `H`-作用（`DistribMulAction (Hp p) (G.ZOm p)`）由**本件新装**
       （全库此前无此实例：`G1c` 只装 `↥(ker φ)` 上的作用、`ProcHyp` 只装 `Mp2 p`
       上的作用）。装法 ＝ 经 `(G.UH p).ρ`（正则作用），与 `ProcHyp` 的
       `smul_Hp_Mp2_snd` 逐字一致（第二分量 ＝ `UH` 作用）。
    ④ 忠实性 `FaithfulSMul (Hp p) ↥(ker (G.phiFun p))` **不走** F1 件的 p = 3 特化
       （`M_H_faithful`）、**也不走** G 轨桥；本件给**参数化初等直证**（§2）：任意素 p，
       取被 h 移动的 ω（经 `eHO` 搬运左乘 ＋ `eHO` 单射），见证
       `z = e_ω⊗e_ω − e_{hω}⊗e_{hω} ∈ ker φ`，用双线性系数泛函 `Λ_{ω,ω}`（经
       `TensorProduct.lid` 装配，**不用环乘法** —— `Fin (p*p)` 无乘法，`ZOm p`
       无环结构）分离出 `Λ(z) = 1` 而 `Λ(h·z) ∈ {0, −1} ≠ 1`。
    ⑤ 基域搬运链 ＝ `invariantsAlgEquivK0` 取逆接 `invariantsSubfieldAlgEquiv`
       （≃ₐ[F]），再经 `rationalFunctionFieldAlgEquiv` 落到 `↥(latticeInvariants F (Hp p) M)`。
    ⑥ 无 sorry、无自造公理；`#print axioms` 闸门见 §7。

  派发书风险清单的逐条实测读数（前置实测件 `ProbePS1.lean` rc = 0）：
    * `UniqueProds (Multiplicative ↥(ker φ))`：环境实例（G2p `uniqueSums_kerPhi`）✓；
    * `UniqueProds (Multiplicative (ZOm p))`：环境实例（G2p `uniqueSums_monoidAlgebra`）✓；
    * `DistribMulAction (Hp p) ↥(ker φ)`：G1c 全局实例 ✓；
    * `SMulCommClass (Hp p) ℤ ↥(ker φ)`：由 `AddGroup.int_smulCommClass'` 合成 ✓；
    * `Basis ＋ hρ`：`permBasis_ZOm`（§3，逐字 `U_rho_theta` 的 rfl 形）✓；
    * 忠实性：§2 直证 ✓；基域搬运：§4 ✓。
-/
import ABGV52.ProcHyp_ABGV52
import ABGV52.EMRouteS_ABGV52

open scoped TensorProduct
open ABGV52.P (Hp)

namespace ABGV52.ProcStab

variable (p : ℕ) [Fact p.Prime]

noncomputable section

/-! ## 1. `ZOm p` 上的 `H`-作用（本件新装）

  装法与 `EMRouteS` 的 `instDistribMulActionRep`（`Rep` 载体经 `L.ρ`）同款：
  逐字段验证。作用公式（单项式层）经 `Representation.ofMulAction_single` 得到。 -/

noncomputable instance instDistribMulActionHpZOm : DistribMulAction (Hp p) (G.ZOm p) where
  smul h x := (G.UH p).ρ h x
  one_smul x := by
    show (G.UH p).ρ (1 : Hp p) x = x
    rw [map_one]
    rfl
  mul_smul a b x := by
    show (G.UH p).ρ (a * b) x = (G.UH p).ρ a ((G.UH p).ρ b x)
    rw [map_mul]
    rfl
  smul_zero h := ((G.UH p).ρ h).map_zero
  smul_add h x y := ((G.UH p).ρ h).map_add x y

/-- 作用公式（`Rep.ofMulAction` 的 `ZOm p`-载体形）。 -/
lemma rho_single (h : Hp p) (a : G.OmegaP p) (c : ℤ) :
    (G.UH p).ρ h (MonoidAlgebra.single a c) = MonoidAlgebra.single (h • a) c :=
  Representation.ofMulAction_single h a c

/-- 作用公式（`•` 形态，供 `hρ` 化简）。 -/
lemma smul_ZOm_single (h : Hp p) (a : G.OmegaP p) (c : ℤ) :
    h • (MonoidAlgebra.single a c : G.ZOm p) = MonoidAlgebra.single (h • a) c :=
  rho_single p h a c

/-! ## 2. 忠实性：`FaithfulSMul (Hp p) ↥(ker (phiFun p))`（参数化初等直证）

  策略：反设 h 在 ker φ 上处处不动。取 ω 被 h 移动（`exists_smul_ne`）；
  见证 `z = e_ω⊗e_ω − e_{hω}⊗e_{hω}` 在 ker φ 内（`phiFun_single`）；
  用系数泛函 `Λ_{ω,ω}`（双线性，经 `TensorProduct.lid`）分离：`Λ(z) = 1`，
  而 `Λ(h·z) = 0 − [h²ω = ω]·1 ∈ {0, −1} ≠ 1`，与 h 的不动性矛盾。 -/

/-- 系数抽出泛函 `Λ_x`（第 x 个坐标）。 -/
noncomputable def coeffLin (x : G.OmegaP p) : G.ZOm p →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ (fun i : G.OmegaP p => if i = x then (1 : ℤ) else 0)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

omit [Fact p.Prime] in
lemma coeffLin_single (x a : G.OmegaP p) (c : ℤ) :
    coeffLin p x (MonoidAlgebra.single a c) = if a = x then c else 0 := by
  change (Finsupp.linearCombination ℤ (fun i : G.OmegaP p => if i = x then (1 : ℤ) else 0))
    (MonoidAlgebra.coeff (MonoidAlgebra.single a c)) = if a = x then c else 0
  rw [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
  by_cases h : a = x
  · simp [h]
  · simp [h]

/-- 双线性系数泛函 `Λ_{x,y}`（配 `TensorProduct.lid`；**不用环乘法**）。 -/
noncomputable def coeffTensor (x y : G.OmegaP p) :
    (G.ZOm p) ⊗[ℤ] (G.ZOm p) →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map (coeffLin p x) (coeffLin p y))

omit [Fact p.Prime] in
lemma coeffTensor_tmul (x y a b : G.OmegaP p) (c d : ℤ) :
    coeffTensor p x y (MonoidAlgebra.single a c ⊗ₜ[ℤ] MonoidAlgebra.single b d)
      = (if a = x then c else 0) * (if b = y then d else 0) := by
  show (TensorProduct.lid ℤ ℤ) (TensorProduct.map (coeffLin p x) (coeffLin p y)
      (MonoidAlgebra.single a c ⊗ₜ[ℤ] MonoidAlgebra.single b d)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, coeffLin_single, coeffLin_single]
  simp

/-- 对角单项式经 `ρ ⊗ ρ` 后的封闭形（供 `Λ` 求值）。 -/
lemma map_rho_single (h : Hp p) (a : G.OmegaP p) (c : ℤ) :
    TensorProduct.map ((G.UH p).ρ h) ((G.UH p).ρ h)
        (MonoidAlgebra.single a c ⊗ₜ[ℤ] MonoidAlgebra.single a c)
      = MonoidAlgebra.single (h • a) c ⊗ₜ[ℤ] MonoidAlgebra.single (h • a) c := by
  rw [TensorProduct.map_tmul, rho_single p h a c]

/-- `H` 在 `Ω` 上作用忠实（经 `eHO` 搬运左乘 ＋ `eHO` 单射）。 -/
lemma exists_smul_ne (h : Hp p) (hne : h ≠ 1) : ∃ ω : G.OmegaP p, h • ω ≠ ω := by
  by_contra hcon
  have hfix : ∀ ω : G.OmegaP p, h • ω = ω := fun ω => by
    by_contra hω
    exact hcon ⟨ω, hω⟩
  refine hne ?_
  apply (G.eHO p).injective
  rw [← mul_one h, G.eHO_smul p h 1, hfix (G.eHO p 1)]

/-- **忠实性**（参数化初等直证；任意素 p）。 -/
theorem faithfulSMul_kerPhi : FaithfulSMul (Hp p) ↥(LinearMap.ker (G.phiFun p)) := by
  rw [faithfulSMul_iff]
  intro h hfix
  by_contra hne
  obtain ⟨ω, hω⟩ := exists_smul_ne p h hne
  set z : (G.ZOm p) ⊗[ℤ] (G.ZOm p) :=
    MonoidAlgebra.single ω (1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single ω (1 : ℤ) -
      MonoidAlgebra.single (h • ω) (1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single (h • ω) (1 : ℤ)
    with hz_def
  have hz : z ∈ LinearMap.ker (G.phiFun p) := by
    rw [hz_def, LinearMap.mem_ker]
    simp only [map_sub, G.phiFun_single, sub_self]
  have h1 : coeffTensor p ω ω z = 1 := by
    rw [hz_def, map_sub, coeffTensor_tmul, coeffTensor_tmul]
    rw [if_pos (rfl : ω = ω), if_neg hω]
    norm_num
  have h2 : coeffTensor p ω ω (TensorProduct.map ((G.UH p).ρ h) ((G.UH p).ρ h) z) ≠ 1 := by
    rw [hz_def, map_sub, map_rho_single p h ω 1, map_rho_single p h (h • ω) 1, map_sub,
      coeffTensor_tmul, coeffTensor_tmul, if_neg hω]
    by_cases hb : h • (h • ω) = ω
    · rw [if_pos hb]
      norm_num
    · rw [if_neg hb]
      norm_num
  have hneq : TensorProduct.map ((G.UH p).ρ h) ((G.UH p).ρ h) z ≠ z := by
    intro hEq
    exact h2 (by rw [hEq]; exact h1)
  have h_act : TensorProduct.map ((G.UH p).ρ h) ((G.UH p).ρ h) z = z :=
    congrArg (fun w : ↥(LinearMap.ker (G.phiFun p)) => (w : (G.ZOm p) ⊗[ℤ] (G.ZOm p)))
      (hfix ⟨z, hz⟩)
  exact hneq h_act

/-! ## 3. 置换基数据：`B = MonoidAlgebra.basis` 与 `ρ = thetaH` -/

/-- 机器输入 `(B, ρ, hρ)` 的 `hρ` 字段（逐字 `U_rho_theta` 的 rfl 形，经单项式层化简）。 -/
theorem permBasis_ZOm (σ : Hp p) (i : G.OmegaP p) :
    EM.mulEquivOfSMul (Hp p) (G.ZOm p) σ
        (EM.permMono (P := G.ZOm p) (MonoidAlgebra.basis (G.OmegaP p) ℤ) i)
      = EM.permMono (P := G.ZOm p) (MonoidAlgebra.basis (G.OmegaP p) ℤ)
        (G.thetaH p σ i) := by
  rw [EM.mulEquivOfSMul_apply]
  show Multiplicative.ofAdd (σ • (MonoidAlgebra.basis (G.OmegaP p) ℤ) i)
      = Multiplicative.ofAdd ((MonoidAlgebra.basis (G.OmegaP p) ℤ) (G.thetaH p σ i))
  congr 1
  simp only [MonoidAlgebra.basis_apply, smul_ZOm_single]
  rfl

/-! ## 4. 目标 1（无条件）：A 轨机器在 Procesi 格上的实例化 -/

/-- **机器实例化**：Procesi 数据满足 A 轨 §7 的全部前提，故 `S2Interface` 无条件成立。 -/
theorem s2Interface_procesi (F : Type*) [Field F] :
    EM.RouteS.S2Interface (F := F) (G := Hp p) (M := ↥(LinearMap.ker (G.phiFun p)))
      (P := G.ZOm p) :=
  EM.RouteS.s2Interface_of_data' (F := F) (G := Hp p)
    (M := ↥(LinearMap.ker (G.phiFun p))) (P := G.ZOm p)
    (MonoidAlgebra.basis (G.OmegaP p) ℤ) (G.thetaH p) (permBasis_ZOm p)
    (faithfulSMul_kerPhi p)

/-- 基域搬运 `↥K0 ≃ₐ[F] ↥(latticeInvariants F (Hp p) M)`（机器输出侧 → M3 目标侧）。 -/
noncomputable def K0EquivInvariants (F : Type*) [Field F] :
    ↥(EM.K0 (G := Hp p) (F := F) (M := ↥(LinearMap.ker (G.phiFun p))) (P := G.ZOm p)) ≃ₐ[F]
      ↥(EM.latticeInvariants F (Hp p) ↥(LinearMap.ker (G.phiFun p))) :=
  (EM.RouteS.invariantsAlgEquivK0 (F := F) (G := Hp p)
      (M := ↥(LinearMap.ker (G.phiFun p))) (P := G.ZOm p)).symm.trans
    (EM.RouteS.invariantsSubfieldAlgEquiv (F := F) (G := Hp p)
      (M := ↥(LinearMap.ker (G.phiFun p))))

/-- **目标 1（无条件）**：`↥(l(N)^H) ≃+* ↥(l(M)^H)(t₁,…,t_k)` ——
即 M3 的**半函数域（机器）形**（机器 `IsRational` 见证经基域搬运落到 M3 的基域上）。 -/
theorem exists_ratOver_semiInvariants (F : Type*) [Field F] :
    ∃ k : ℕ, Nonempty (↥(FixedPoints.subfield (Hp p)
        (EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p)))
          (P := G.ZOm p))) ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))) k) := by
  obtain ⟨k, ⟨e⟩⟩ := s2Interface_procesi p F
  exact ⟨k, ⟨(e.toRingEquiv).trans
    (EM.RouteS.rationalFunctionFieldAlgEquiv (F := F) (K0EquivInvariants p F) k).toRingEquiv⟩⟩

/-! ## 5. 目标 2（具名件）：对象层二步识别

  `F(M×P)^H`（`latticeInvariants`，左）与机器的 `↥(l(N)^H)`（右）之间的**环境域层**
  同构 ＝ A 轨偏差 3 的未竟处（`l(N) ≡ F(M⊕P)`，蓝图桥 b/T1）。本件不证明它，
  只具名注册 ＋ 类型锁定 ＋ 给出接线定理（T1 的环境同构 ⟹ 本具名件）。 -/

/-- **具名件（目标 2）**：`↥(F(M×P)^H) ≃+* ↥(l(N)^H)`（对象层二步识别，`+*` 形态）。 -/
def TwoStepInterface (F : Type*) [Field F] : Prop :=
  Nonempty (↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) ≃+*
    ↥(FixedPoints.subfield (Hp p)
      (EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p)))
        (P := G.ZOm p))))

/-- **类型锁定（目标 2）**：外形一旦被改动，本 `rfl` 立即编译失败。 -/
theorem twoStepInterface_typeLock (F : Type*) [Field F] :
    TwoStepInterface (p := p) F = Nonempty
      (↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) ≃+*
        ↥(FixedPoints.subfield (Hp p)
          (EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p)))
            (P := G.ZOm p)))) := rfl

/-- 不动点子域的函子性：等变环同构诱导不变量域的同构。 -/
def fixedPointsRingEquiv {G' : Type*} [Group G'] {X Y : Type*} [Field X] [Field Y]
    [MulSemiringAction G' X] [MulSemiringAction G' Y] (Φ : X ≃+* Y)
    (hΦ : ∀ (σ : G') (x : X), Φ (σ • x) = σ • Φ x) :
    ↥(FixedPoints.subfield G' X) ≃+* ↥(FixedPoints.subfield G' Y) := by
  have hmemX : ∀ x : X, x ∈ FixedPoints.subfield G' X ↔ ∀ σ : G', σ • x = x := by
    intro x
    rw [FixedPoints.subfield]
    exact MulAction.mem_fixedPoints
  have hmemY : ∀ y : Y, y ∈ FixedPoints.subfield G' Y ↔ ∀ σ : G', σ • y = y := by
    intro y
    rw [FixedPoints.subfield]
    exact MulAction.mem_fixedPoints
  have hΦsymm : ∀ (σ : G') (y : Y), Φ.symm (σ • y) = σ • Φ.symm y := by
    intro σ y
    apply Φ.injective
    rw [RingEquiv.apply_symm_apply, hΦ σ (Φ.symm y), RingEquiv.apply_symm_apply]
  refine
    { toFun := fun x => ⟨Φ x.1, (hmemY (Φ x.1)).mpr fun σ => ?_⟩
      invFun := fun y => ⟨Φ.symm y.1, (hmemX (Φ.symm y.1)).mpr fun σ => ?_⟩
      left_inv := fun x => Subtype.ext (Φ.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (Φ.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (Φ.map_add' x.1 y.1)
      map_mul' := fun x y => Subtype.ext (Φ.map_mul' x.1 y.1) }
  · rw [← hΦ σ x.1]
    exact congrArg Φ ((hmemX x.1).mp x.2 σ)
  · rw [← hΦsymm σ y.1]
    exact congrArg Φ.symm ((hmemY y.1).mp y.2 σ)

/-- **T1 接线**：A 轨偏差 3 的环境域层等变同构（`l(N) ≅ F(M×P)`，等变）⟹ 具名件。 -/
theorem twoStepInterface_of_ambient (F : Type*) [Field F]
    (Φ : EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p)))
        (P := G.ZOm p) ≃+*
      EM.latticeFunctionField F (ProcLat.Mp2 p))
    (hΦ : ∀ (σ : Hp p)
      (x : EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p)))
        (P := G.ZOm p)), Φ (σ • x) = σ • Φ x) :
    TwoStepInterface (p := p) F :=
  ⟨(fixedPointsRingEquiv (G' := Hp p) Φ hΦ).symm⟩

/-! ## 6. 目标 3（模具名件版）：C′ ＋ 具名件 ⟹ C″ -/

/-- **M3 的直和形（具名件版）**：目标 2 的具名件 ＋ 目标 1（无条件）⟹ M3 逐字外形。 -/
theorem m3_of_twoStep (F : Type*) [Field F] (b : TwoStepInterface (p := p) F) :
    ∃ k : ℕ, Nonempty (↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))) k) := by
  obtain ⟨b⟩ := b
  obtain ⟨k, ⟨e⟩⟩ := exists_ratOver_semiInvariants p F
  exact ⟨k, ⟨b.trans e⟩⟩

/-- **目标 3（收口）**：`ProcesiHypExact` ＋ 具名件 ⟹ `ProcesiHypStable`（无条件版之
  模具名件形态；桥 (c) 的 M3 假设已由 §4 消解，此定理只是把具名件代入）。 -/
theorem procesiHypStable_of_exact_of_twoStep (F : Type*) [Field F] (Z : Type*) [Field Z]
    (hExact : ProcHyp.ProcesiHypExact (p := p) F Z)
    (b : TwoStepInterface (p := p) F) :
    ProcHyp.ProcesiHypStable (p := p) F Z :=
  ProcHyp.procesiHypStable_of_exact_of_ratOver (p := p) F Z hExact (m3_of_twoStep p F b)

/-! ## 7. 公理闸门 -/

#print axioms instDistribMulActionHpZOm
#print axioms rho_single
#print axioms smul_ZOm_single
#print axioms coeffLin
#print axioms coeffLin_single
#print axioms coeffTensor
#print axioms coeffTensor_tmul
#print axioms map_rho_single
#print axioms exists_smul_ne
#print axioms faithfulSMul_kerPhi
#print axioms permBasis_ZOm
#print axioms s2Interface_procesi
#print axioms K0EquivInvariants
#print axioms exists_ratOver_semiInvariants
#print axioms TwoStepInterface
#print axioms twoStepInterface_typeLock
#print axioms fixedPointsRingEquiv
#print axioms twoStepInterface_of_ambient
#print axioms m3_of_twoStep
#print axioms procesiHypStable_of_exact_of_twoStep

end

end ABGV52.ProcStab
