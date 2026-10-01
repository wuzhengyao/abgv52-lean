/-
  ABGV-5.2 —— S3：`prop:stable-exp` 的**置换格**侧

  两条：
    (c) **Shapiro 桥**：`ℤ[H/K] ≅ Coind_K^H(ℤ)`（mathlib 无现成桥 ⟹ 显式构造），
        配 `groupCohomology.coindIso` 与 `threeKills_coh2` 得
        「`3` 消没 `coh²(H, ℤ[H/K])`」；
    (d) **轨道分解**：有限 `H`-集 `X` 的轨道的**幂等分解**
        `Σ_ω 𝟙_{O_ω} = 𝟙`（每项经 `ℤ[H/K_ω]` 分解）⟹ `3` 消没 `coh²(H, ℤ[X])`。

  工艺要点（五条，均为本轮实测）：
    * **载体双层**：`Rep k H` 的置换模载体是 `MonoidAlgebra k X`（一字段**结构**，
      `X →₀ k` 加包装），与 `Finsupp` **不是定义相等** ⟹ 一律用
      `MonoidAlgebra.coeffLinearEquiv` 共轭到 `Finsupp` 层做计算
      （`Representation.ofMulAction_def` 正是 `coeff ∘ ρ ∘ coeff⁻¹ = lmapDomain`）。
    * **陪集：用 `Quotient.lift` 而**非** `Quotient.out`**——`out` 写出的公式
      良定义/等变性都要额外交代，而 `Quotient.lift` 把良定义性一次性收进一个引理，
      等变性用 `Quotient.inductionOn'` 归到代表元（`q = mk a`）后是纯结合律。
    * **`Decidable` 只能靠 `classical`**：`Subgroup` 的成员判定**没有**非经典实例
      ⟹ 含 `if x ∈ K` 的**陈述**无法在无 `classical` 时展开；一律在 **tactic 体内**
      先 `classical` 再用 `show` 写出 `if` 形式（`shapiroFun` 本体用 `by classical`）。
    * **`Quotient.lift_mk` 的隐参要写全**：`Quotient.lift_mk _ _ a` 里的 `_` 无法定
      setoid ⟹ 必须把 `f` 与**同一个** `h` 显式写出（`rfl` 级等式）。
    * **`Finsupp.mapDomain` 的取值**：`(mapDomain f w) (f a) = w a` 只在**像点**上给值
      （`mapDomain_apply` 要先给单射性）；一般点先用 `smul_inv_smul` 搬回像点。
-/
import ABGV52.S2_ABGV52
import Mathlib.RepresentationTheory.Coinduced

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-- `(h · ·)` 的单射性（`Finsupp.mapDomain_apply` 用）。 -/
lemma smulLeft_injective (K : Subgroup H) (h : H) :
    Function.Injective (fun x : H ⧸ K => h • x) :=
  fun a b hab => by
    have := congrArg (fun x => h⁻¹ • x) hab
    simpa using this

/-! ## (c) Shapiro 桥：`ℤ[H/K] ≅ Coind_K^H(ℤ)` -/

/-- 置换模 `ℤ[H/K]`（左陪集 `H ⧸ K` 上的置换表示）。 -/
noncomputable abbrev permHK (K : Subgroup H) : Rep ℤ H := Rep.ofMulAction ℤ H (H ⧸ K)

/-- Shapiro 的对偶侧：`Coind_K^H(ℤ)`。 -/
noncomputable abbrev coindK (K : Subgroup H) : Rep ℤ H :=
  Rep.coind K.subtype (Rep.trivial ℤ ↥K ℤ)

/-- `Coind_K^H(ℤ)` 的载体（`K`-左不变函数 `H → ℤ`）。 -/
noncomputable abbrev CoindCarrier (K : Subgroup H) : Type :=
  Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ)

/-- `K`-不变性的展开形式。 -/
lemma coind_inv (K : Subgroup H) (f : CoindCarrier K) :
    ∀ (k : ↥K) (y : H), f.1 (↑k * y) = f.1 y := fun k y =>
  (Representation.mem_coindV K.subtype (Representation.trivial ℤ ↥K ℤ) f.1).mp f.2 k y

/-- `Coind` 侧作用的展开形式：`(h · f) y = f (y * h)`。 -/
lemma coind_apply (K : Subgroup H) (h : H) (f : CoindCarrier K) (y : H) :
    ((coindK K).ρ h f).1 y = f.1 (y * h) := rfl

/-! ### (c.1) 基像 `Φ(q) = [y · out q ∈ K]` -/

/-- 基像的「代表元版」：`Φ̃(a) (y) = [y · a ∈ K]`。 -/
noncomputable def shapiroFun (K : Subgroup H) (a : H) : H → ℤ := by
  classical
  exact fun y => if y * a ∈ K then (1 : ℤ) else 0

lemma shapiroFun_wellDef (K : Subgroup H) {a a' : H}
    (h : (QuotientGroup.mk a : H ⧸ K) = QuotientGroup.mk a') :
    shapiroFun K a = shapiroFun K a' := by
  classical
  rw [QuotientGroup.eq] at h
  funext y
  have hiff : (y * a ∈ K) ↔ (y * a' ∈ K) := by
    have key : y * a' = (y * a) * (a⁻¹ * a') := by
      have h2 : a' = a * (a⁻¹ * a') := by group
      conv_lhs => rw [h2]
      rw [mul_assoc]
    rw [key]
    exact (K.mul_mem_cancel_right h).symm
  show (if y * a ∈ K then (1 : ℤ) else 0) = (if y * a' ∈ K then (1 : ℤ) else 0)
  by_cases hx : y * a ∈ K
  · rw [if_pos hx, if_pos (hiff.mp hx)]
  · rw [if_neg hx, if_neg fun hc => hx (hiff.mpr hc)]

set_option maxHeartbeats 1000000 in
/-- `Φ̃(a)` 是 `K`-**左**不变的。 -/
lemma shapiroFun_mem (K : Subgroup H) (a : H) :
    shapiroFun K a ∈ Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ) := by
  classical
  rw [Representation.mem_coindV]
  intro k y
  show (if (↑k * y) * a ∈ K then (1 : ℤ) else 0) = (if y * a ∈ K then (1 : ℤ) else 0)
  rw [show (↑k * y) * a = ↑k * (y * a) from mul_assoc ↑k y a]
  by_cases hx : ↑k * (y * a) ∈ K
  · rw [if_pos hx, if_pos ((K.mul_mem_cancel_left k.2).mp hx)]
  · rw [if_neg hx, if_neg fun hc => hx (K.mul_mem k.2 hc)]

/-- 基像的陪集版（`Quotient.lift`，良定义性一次收口）。 -/
noncomputable def shapiroLifted (K : Subgroup H) (q : H ⧸ K) : H → ℤ :=
  Quotient.lift (shapiroFun K) (fun a a' hab => shapiroFun_wellDef K (Quotient.sound' hab)) q

@[simp] lemma shapiroLifted_mk (K : Subgroup H) (a : H) :
    shapiroLifted K (QuotientGroup.mk a) = shapiroFun K a :=
  Quotient.lift_mk (shapiroFun K)
    (fun a a' hab => shapiroFun_wellDef K (Quotient.sound' hab)) a

lemma shapiroLifted_mem (K : Subgroup H) (q : H ⧸ K) :
    shapiroLifted K q ∈ Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ) := by
  induction q using Quotient.inductionOn' with
  | h a => rw [shapiroLifted_mk]; exact shapiroFun_mem K a

/-- Shapiro 桥的基像：`Φ(q) ∈ Coind_K^H(ℤ)`。 -/
noncomputable def shapiroBasis (K : Subgroup H) (q : H ⧸ K) : CoindCarrier K :=
  ⟨shapiroLifted K q, shapiroLifted_mem K q⟩

@[simp] lemma shapiroBasis_mk (K : Subgroup H) (a : H) :
    (shapiroBasis K (QuotientGroup.mk a)).1 = shapiroFun K a :=
  shapiroLifted_mk K a

/-- **`Φ` 的等变性**：`Φ(h · q) = h · Φ(q)`。 -/
lemma shapiroBasis_smul (K : Subgroup H) (h : H) (q : H ⧸ K) :
    (coindK K).ρ h (shapiroBasis K q) = shapiroBasis K (h • q) := by
  classical
  apply Subtype.ext
  funext y
  show (shapiroBasis K q).1 (y * h) = (shapiroBasis K (h • q)).1 y
  induction q using Quotient.inductionOn' with
  | h a =>
    rw [show h • (QuotientGroup.mk a : H ⧸ K) = QuotientGroup.mk (h * a) from rfl]
    rw [shapiroBasis_mk, shapiroBasis_mk]
    show (if (y * h) * a ∈ K then (1 : ℤ) else 0) = (if y * (h * a) ∈ K then (1 : ℤ) else 0)
    rw [show (y * h) * a = y * (h * a) from mul_assoc y h a]

/-- `Finsupp` 侧的 Shapiro 桥：`(H ⧸ K →₀ ℤ) →ₗ Coind_K^H(ℤ)`，`single q 1 ↦ Φ(q)`。 -/
noncomputable def shapiroLift (K : Subgroup H) :
    ((H ⧸ K) →₀ ℤ) →ₗ[ℤ] CoindCarrier K :=
  (Finsupp.lift (CoindCarrier K) ℤ (H ⧸ K)) (shapiroBasis K)

lemma shapiroLift_single (K : Subgroup H) (q : H ⧸ K) :
    shapiroLift K (Finsupp.single q 1) = shapiroBasis K q := by
  rw [shapiroLift, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **等变性的 `Finsupp` 层形式**（线性映射层）：`lift Φ` 与 `H`-作用交换。 -/
lemma shapiroLift_mapDomain (K : Subgroup H) (h : H) :
    (shapiroLift K).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = ((coindK K).ρ h).comp (shapiroLift K) := by
  refine (Finsupp.lift (CoindCarrier K) ℤ (H ⧸ K)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show shapiroLift K (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single q 1))
      = (coindK K).ρ h (shapiroLift K (Finsupp.single q 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, shapiroLift_single, shapiroLift_single,
    shapiroBasis_smul]

/-- Shapiro 桥 `ℤ[H/K] ⟶ Coind_K^H(ℤ)`。 -/
noncomputable def shapiroHom (K : Subgroup H) : permHK K ⟶ coindK K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    ((shapiroLift K).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)
    (by
      intro h
      refine LinearMap.ext (fun w => ?_)
      show shapiroLift K ((MonoidAlgebra.coeffLinearEquiv ℤ) ((permHK K).ρ h w))
          = (coindK K).ρ h (shapiroLift K ((MonoidAlgebra.coeffLinearEquiv ℤ) w))
      rw [show (MonoidAlgebra.coeffLinearEquiv ℤ) ((permHK K).ρ h w)
            = Finsupp.lmapDomain ℤ ℤ (h • ·) ((MonoidAlgebra.coeffLinearEquiv ℤ) w) from by
        rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rfl]
      exact congrArg (fun (f : ((H ⧸ K) →₀ ℤ) →ₗ[ℤ] CoindCarrier K) => f _)
        (shapiroLift_mapDomain K h)))

/-! ### (c.2) 对偶侧与复合恒等式 -/

/-- 对偶侧的代表元版：`f ↦ (a ↦ f(a⁻¹))`。 -/
noncomputable def shapiroOfCoindRaw (K : Subgroup H) (f : CoindCarrier K) : H → ℤ :=
  fun a => f.1 (a⁻¹)

lemma shapiroOfCoindRaw_wellDef (K : Subgroup H) (f : CoindCarrier K) {a a' : H}
    (h : (QuotientGroup.mk a : H ⧸ K) = QuotientGroup.mk a') :
    shapiroOfCoindRaw K f a = shapiroOfCoindRaw K f a' := by
  rw [QuotientGroup.eq] at h
  show f.1 (a⁻¹) = f.1 (a'⁻¹)
  rw [show a'⁻¹ = (a⁻¹ * a')⁻¹ * a⁻¹ from by group]
  exact (coind_inv K f ⟨(a⁻¹ * a')⁻¹, K.inv_mem h⟩ a⁻¹).symm

/-- 对偶侧的陪集版（`Quotient.lift`，用 `K`-左不变性）。 -/
noncomputable def shapiroOfCoindFun (K : Subgroup H) (f : CoindCarrier K) : (H ⧸ K) → ℤ :=
  Quotient.lift (shapiroOfCoindRaw K f)
    (fun a a' hab => shapiroOfCoindRaw_wellDef K f (Quotient.sound' hab))

@[simp] lemma shapiroOfCoindFun_mk (K : Subgroup H) (f : CoindCarrier K) (a : H) :
    shapiroOfCoindFun K f (QuotientGroup.mk a) = f.1 (a⁻¹) :=
  Quotient.lift_mk (shapiroOfCoindRaw K f)
    (fun a a' hab => shapiroOfCoindRaw_wellDef K f (Quotient.sound' hab)) a

/-- `Finsupp` 侧的逆映射：`f ↦ (q ↦ f(a⁻¹))`（`q = aK`）。 -/
noncomputable def shapiroOfCoindLift (K : Subgroup H) :
    CoindCarrier K →ₗ[ℤ] ((H ⧸ K) →₀ ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (H ⧸ K)).symm.toLinearMap.comp
    ({ toFun := shapiroOfCoindFun K
       map_add' := fun f g => by
         funext q
         induction q using Quotient.inductionOn' with
         | h a => simp
       map_smul' := fun c f => by
         funext q
         induction q using Quotient.inductionOn' with
         | h a => simp } : CoindCarrier K →ₗ[ℤ] (H ⧸ K → ℤ))

@[simp] lemma shapiroOfCoindLift_apply (K : Subgroup H) (f : CoindCarrier K) (a : H) :
    shapiroOfCoindLift K f (QuotientGroup.mk a) = f.1 (a⁻¹) := by
  rw [shapiroOfCoindLift, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact shapiroOfCoindFun_mk K f a

/-- **逆映射的等变性**（`Finsupp` 层，辅助形式：只在 `h · q'` 上验证）。 -/
lemma shapiroOfCoindLift_smul_aux (K : Subgroup H) (h : H) (f : CoindCarrier K)
    (q' : H ⧸ K) :
    shapiroOfCoindLift K ((coindK K).ρ h f) (h • q')
      = Finsupp.mapDomain (h • ·) (shapiroOfCoindLift K f) (h • q') := by
  induction q' using Quotient.inductionOn' with
  | h b =>
    rw [Finsupp.mapDomain_apply (smulLeft_injective K h) (shapiroOfCoindLift K f) b]
    rw [show h • (QuotientGroup.mk b : H ⧸ K) = QuotientGroup.mk (h * b) from rfl]
    rw [shapiroOfCoindLift_apply, shapiroOfCoindLift_apply, coind_apply]
    show f.1 ((h * b)⁻¹ * h) = f.1 (b⁻¹)
    rw [show (h * b)⁻¹ * h = b⁻¹ from by group]

/-- **逆映射的等变性**（`Finsupp` 层）。 -/
lemma shapiroOfCoindLift_smul (K : Subgroup H) (h : H) (f : CoindCarrier K) :
    shapiroOfCoindLift K ((coindK K).ρ h f)
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (shapiroOfCoindLift K f) := by
  ext q
  rw [Finsupp.lmapDomain_apply]
  rw [show q = h • (h⁻¹ • q) from (smul_inv_smul h q).symm]
  exact shapiroOfCoindLift_smul_aux K h f (h⁻¹ • q)

/-- Shapiro 桥的对偶侧 `Coind_K^H(ℤ) ⟶ ℤ[H/K]`。 -/
noncomputable def shapiroOfCoind (K : Subgroup H) : coindK K ⟶ permHK K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    ((MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (shapiroOfCoindLift K))
    (by
      intro h
      refine LinearMap.ext (fun f => ?_)
      show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
            (shapiroOfCoindLift K ((coindK K).ρ h f))
          = (permHK K).ρ h ((MonoidAlgebra.coeffLinearEquiv ℤ).symm (shapiroOfCoindLift K f))
      rw [shapiroOfCoindLift_smul K h f]
      rw [show (permHK K).ρ h ((MonoidAlgebra.coeffLinearEquiv ℤ).symm (shapiroOfCoindLift K f))
            = (MonoidAlgebra.coeffLinearEquiv ℤ).symm
              (Finsupp.lmapDomain ℤ ℤ (h • ·) (shapiroOfCoindLift K f)) from by
        rw [Representation.ofMulAction_def]
        simp]))

/-- **复合恒等式（`Finsupp` 层）**：`δ ∘ γ = 𝟙`。

在基上：`δ(γ(e_{aK}))(bK) = [(b⁻¹ · a) ∈ K] = [bK = aK]`。 -/
theorem shapiroOfCoindLift_comp_shapiroLift (K : Subgroup H) :
    (shapiroOfCoindLift K).comp (shapiroLift K)
      = LinearMap.id (R := ℤ) (M := (H ⧸ K) →₀ ℤ) := by
  classical
  refine (Finsupp.lift ((H ⧸ K) →₀ ℤ) ℤ (H ⧸ K)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show shapiroOfCoindLift K (shapiroLift K (Finsupp.single q 1)) = Finsupp.single q 1
  rw [shapiroLift_single]
  show shapiroOfCoindLift K (shapiroBasis K q) = Finsupp.single q 1
  ext q'
  induction q using Quotient.inductionOn' with
  | h a =>
    induction q' using Quotient.inductionOn' with
    | h b =>
      rw [shapiroOfCoindLift_apply, shapiroBasis_mk, Finsupp.single_apply]
      have hiff : ((QuotientGroup.mk a : H ⧸ K) = QuotientGroup.mk b) ↔ b⁻¹ * a ∈ K := by
        rw [QuotientGroup.eq]
        exact ⟨fun h => by simpa using K.inv_mem h, fun h => by simpa using K.inv_mem h⟩
      rw [show shapiroFun K a b⁻¹ = (if b⁻¹ * a ∈ K then (1 : ℤ) else 0) from rfl]
      by_cases hb : b⁻¹ * a ∈ K
      · rw [if_pos hb, if_pos (hiff.mpr hb)]
      · rw [if_neg hb, if_neg fun hc => hb (hiff.mp hc)]

/-- **Shapiro 桥的复合 = 恒等**（在 `ℤ[H/K]` 侧）。 -/
theorem shapiroHom_comp (K : Subgroup H) :
    shapiroHom K ≫ shapiroOfCoind K = 𝟙 (permHK K) := by
  apply Rep.hom_ext
  rw [Rep.hom_comp, Rep.hom_id]
  apply Representation.IntertwiningMap.ext
  show ((shapiroOfCoind K).hom.toLinearMap.comp (shapiroHom K).hom.toLinearMap)
      = LinearMap.id
  refine LinearMap.ext (fun w => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (shapiroOfCoindLift K (shapiroLift K ((MonoidAlgebra.coeffLinearEquiv ℤ) w))) = w
  rw [show shapiroOfCoindLift K (shapiroLift K ((MonoidAlgebra.coeffLinearEquiv ℤ) w))
        = (MonoidAlgebra.coeffLinearEquiv ℤ) w from
      congrArg (fun (f : ((H ⧸ K) →₀ ℤ) →ₗ[ℤ] ((H ⧸ K) →₀ ℤ)) =>
        f ((MonoidAlgebra.coeffLinearEquiv ℤ) w)) (shapiroOfCoindLift_comp_shapiroLift K)]
  exact LinearEquiv.symm_apply_apply _ _

/-! ### (c.3) 转移：`3` 消没 `coh²(H, ℤ[H/K])` -/

/-- **retract 引理**：若 `γ ≫ δ = 𝟙_A` 且 `3` 消没 `coh²(B)`，则 `3` 消没 `coh²(A)`。 -/
theorem kills_of_retract {A B : Rep ℤ H} (γ : A ⟶ B) (δ : B ⟶ A) (h : γ ≫ δ = 𝟙 A)
    (hB : Coh2ExpDvd3 B) : Coh2ExpDvd3 A := by
  intro x
  have hid : (groupCohomology.map (MonoidHom.id H) δ 2).hom
      ((groupCohomology.map (MonoidHom.id H) γ 2).hom x) = x := by
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, h, groupCohomology.map_id]
    rfl
  have h3 : (3 : ℤ) • (groupCohomology.map (MonoidHom.id H) γ 2).hom x = 0 := hB _
  calc (3 : ℤ) • x
      = (3 : ℤ) • (groupCohomology.map (MonoidHom.id H) δ 2).hom
          ((groupCohomology.map (MonoidHom.id H) γ 2).hom x) := by rw [hid]
    _ = (groupCohomology.map (MonoidHom.id H) δ 2).hom
          ((3 : ℤ) • (groupCohomology.map (MonoidHom.id H) γ 2).hom x) :=
        (map_zsmul (groupCohomology.map (MonoidHom.id H) δ 2).hom 3 _).symm
    _ = 0 := by rw [h3, map_zero]

/-- **`3` 消没 `coh²(H, ℤ[H/K])`**（Shapiro ＋ 子群上指数整除 3）。

路线：`coh²(H, ℤ[H/K]) ←^{γ_*} coh²(H, Coind_K^H ℤ) ≅ coh²(K, ℤ)`，
而 `K ≤ H = C₃×C₃` 的指数整除 3。 -/
theorem threeKills_permHK (K : Subgroup H) (hH : ∀ x : H, x ^ 3 = 1) :
    Coh2ExpDvd3 (permHK K) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  exact kills_of_retract (shapiroHom K) (shapiroOfCoind K) (shapiroHom_comp K)
    (smul_three_eq_zero_of_linearEquiv'
      (groupCohomology.coindIso (S := K) (Rep.trivial ℤ ↥K ℤ) 2).toLinearEquiv
      (threeKills_coh2 ↥K fun x => by
        apply Subtype.ext
        simpa using hH (x : H)))

/-! ## 公理闸门 -/

#print axioms shapiroFun
#print axioms shapiroBasis
#print axioms shapiroLift_mapDomain
#print axioms shapiroOfCoindLift_smul
#print axioms shapiroOfCoindLift_comp_shapiroLift
#print axioms shapiroHom_comp
#print axioms kills_of_retract
#print axioms threeKills_permHK

end ABGV52
