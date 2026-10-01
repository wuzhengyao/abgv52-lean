/-
  ABGV-5.2 —— S4：`perm_exp` 与 `stable_exp`（论文 `prop:stable-exp`）

  数学内容：有限 `H`-集 `X` 的置换模 `ℤ[X]` 满足 `3 · coh²(H, ℤ[X]) = 0`；
  再配 S1 的转移引理得 `stable_exp`。

  路线 = **轨道幂等分解**（**不用**双积/有限直和 API）：
    * 轨道商 `Ω = X/H`（有限类型），每个 `ω` 取代表元 `b_ω`、稳定子 `K_ω`；
    * `α_ω : ℤ[X] ⟶ ℤ[H/K_ω]`（取 `O_ω` 上的分量）、`β_ω : ℤ[H/K_ω] ⟶ ℤ[X]`（映回）；
    * `β_ω ≫ α_ω = 𝟙`（`ℤ[H/K_ω]` 上）与 **`Σ_ω (α_ω ≫ β_ω) = 𝟙`**（`ℤ[X]` 上）；
    * 于是 `x = Σ_ω (α_ω ≫ β_ω)_* x`，而每项经 `coh²(H, ℤ[H/K_ω])` 分解，
      后者被 `3` 零化（S3 的 `threeKills_permHK`）⟹ 逐项零 ⟹ `3x = 0`。

  工艺要点：
    * 载体双层（`MonoidAlgebra` vs `Finsupp`）同 S3 ⟹ 一律共轭到 `Finsupp` 层计算；
    * `OrbitQ` 无 `Fintype`/`DecidableEq` 实例 ⟹ `Fintype.ofFinite` ＋ `Classical.decEq`；
    * `α_ω` 的等变性需要「陪集 ≃ 轨道的 `.symm` 等变性」= `ofQuotientStabilizer_smul`；
    * 等变性一律**先证 `Finsupp` 层的线性映射等式**、再 `congr 1` + `LinearMap.congr_fun`
      搬回 `MonoidAlgebra` 层（避免在复合里做 `congrArg` 的 λ 类型标注）。
-/
import ABGV52.S3_ABGV52
import Mathlib.GroupTheory.GroupAction.Quotient

open CategoryTheory CategoryTheory.Limits

-- 组装段的大项归一较慢（命名常量前的实测：>4M 心跳）
set_option maxHeartbeats 800000

namespace ABGV52

/-- **`Rep` 态射的有限和在点上的取值**：`(∑ f) u = ∑ f u`。

**工艺**：语句用 `Rep` 的**函数强制**（`(∑ f) u`），**不写** `.hom.toLinearMap`——
后者触发 `AddCommGroup.toIntModule` 与 `Rep.hV2` 的实例菱形（实测 `synthInstanceFailed`）；
而 `∑` 的项也不预先取 `.hom`，一律留在 `Rep.Hom` 层。 -/
lemma repHom_sum_apply {ι : Type} (s : Finset ι) {A B : Rep ℤ H} (f : ι → (A ⟶ B)) (u : A) :
    (∑ i ∈ s, f i) u = ∑ i ∈ s, (f i) u := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show (ConcreteCategory.hom (f a)) u + (ConcreteCategory.hom (∑ x ∈ s, f x)) u
        = (ConcreteCategory.hom (f a)) u + ∑ x ∈ s, (ConcreteCategory.hom (f x)) u
      rw [ih]

/-! ## 0. 有限和版函子性 -/

/-- `groupCohomology.map` 对**有限和**的加性（`cohMap_add` 的 `Finset` 版）。 -/
lemma cohMap_sum {ι : Type} (s : Finset ι) {A B : Rep ℤ H} (f : ι → (A ⟶ B)) (n : ℕ) :
    groupCohomology.map (MonoidHom.id H) (∑ i ∈ s, f i) n
      = ∑ i ∈ s, groupCohomology.map (MonoidHom.id H) (f i) n := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact (groupCohomology.functor ℤ H n).map_zero A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohMap_add, ih]

/-! ## 1. 轨道商与稳定子 -/

section Orbit

variable (X : Type) [Fintype X] [MulAction H X]

/-- 轨道商 `X/H`。 -/
abbrev OrbitQ : Type := MulAction.orbitRel.Quotient H X

/-- `OrbitQ` 的 `Fintype`/`DecidableEq`（mathlib 未给；`noncomputable local instance`）。 -/
noncomputable local instance orbitQFintype : Fintype (OrbitQ X) := Fintype.ofFinite _
noncomputable local instance orbitQDecEq : DecidableEq (OrbitQ X) := Classical.decEq _

/-- `x` 所在的轨道。 -/
noncomputable abbrev orb (x : X) : OrbitQ X := Quotient.mk'' x

/-- 轨道 `ω` 的代表元。 -/
noncomputable def orbRep (ω : OrbitQ X) : X := Quotient.out ω

/-- 轨道 `ω` 的稳定子。 -/
noncomputable def orbStab (ω : OrbitQ X) : Subgroup H :=
  MulAction.stabilizer H (orbRep X ω)

/-- 轨道 ≃ 陪集空间。 -/
noncomputable def orbPsi (ω : OrbitQ X) :
    MulAction.orbit H (orbRep X ω) ≃ H ⧸ orbStab X ω :=
  MulAction.orbitEquivQuotientStabilizer H (orbRep X ω)

lemma orbRep_eq (ω : OrbitQ X) : orb X (orbRep X ω) = ω := Quotient.out_eq' ω

/-- **`ψ.symm` 的等变性**（= `ofQuotientStabilizer_smul`）。 -/
lemma orbPsi_symm_smul (ω : OrbitQ X) (h : H) (q : H ⧸ orbStab X ω) :
    ((orbPsi X ω).symm (h • q) : X) = h • ((orbPsi X ω).symm q : X) :=
  MulAction.ofQuotientStabilizer_smul H (orbRep X ω) h q

/-- **`ψ` 的等变性**（`⟨h · x, _⟩` 形式，避免 `h • ⟨x, _⟩` 的语法展开）。 -/
lemma orbPsi_smul_apply (ω : OrbitQ X) (h : H) (x : X)
    (hx : x ∈ MulAction.orbit H (orbRep X ω))
    (hx' : h • x ∈ MulAction.orbit H (orbRep X ω)) :
    orbPsi X ω ⟨h • x, hx'⟩ = h • orbPsi X ω ⟨x, hx⟩ := by
  apply (orbPsi X ω).symm.injective
  refine Subtype.ext ?_
  show (((orbPsi X ω).symm (orbPsi X ω ⟨h • x, hx'⟩)) : X)
      = (((orbPsi X ω).symm (h • orbPsi X ω ⟨x, hx⟩)) : X)
  rw [Equiv.symm_apply_apply, orbPsi_symm_smul X ω h (orbPsi X ω ⟨x, hx⟩), Equiv.symm_apply_apply]

/-! ## 2. `Finsupp` 层的两个映射 -/

/-- `α` 的基像：`x ↦ [x ∈ O_ω] · single (ψ x) 1`。 -/
noncomputable def orbAlphaBasis (ω : OrbitQ X) (x : X) : (H ⧸ orbStab X ω) →₀ ℤ := by
  classical
  exact if hx : orb X x = ω then
    Finsupp.single (orbPsi X ω ⟨x, MulAction.orbitRel_apply.mp
      (Quotient.exact (hx.trans (orbRep_eq X ω).symm))⟩) 1
  else 0

/-- `β` 的基像：`single q 1 ↦ single (ψ.symm q) 1`。 -/
noncomputable def orbBetaBasis (ω : OrbitQ X) (q : H ⧸ orbStab X ω) : X →₀ ℤ :=
  Finsupp.single ((orbPsi X ω).symm q : X) 1

/-- `α`（`Finsupp` 层）。 -/
noncomputable def orbAlphaL (ω : OrbitQ X) :
    (X →₀ ℤ) →ₗ[ℤ] ((H ⧸ orbStab X ω) →₀ ℤ) :=
  (Finsupp.lift ((H ⧸ orbStab X ω) →₀ ℤ) ℤ X) (orbAlphaBasis X ω)

/-- `β`（`Finsupp` 层）。 -/
noncomputable def orbBetaL (ω : OrbitQ X) :
    ((H ⧸ orbStab X ω) →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ) :=
  (Finsupp.lift (X →₀ ℤ) ℤ (H ⧸ orbStab X ω)) (orbBetaBasis X ω)

lemma orbAlphaL_single (ω : OrbitQ X) (x : X) :
    orbAlphaL X ω (Finsupp.single x 1) = orbAlphaBasis X ω x := by
  rw [orbAlphaL, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

lemma orbBetaL_single (ω : OrbitQ X) (q : H ⧸ orbStab X ω) :
    orbBetaL X ω (Finsupp.single q 1) = orbBetaBasis X ω q := by
  rw [orbBetaL, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **`α` 的等变性**（`Finsupp` 层）。 -/
lemma orbAlphaL_mapDomain (ω : OrbitQ X) (h : H) :
    (orbAlphaL X ω).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = (Finsupp.lmapDomain ℤ ℤ (h • ·)).comp (orbAlphaL X ω) := by
  classical
  refine (Finsupp.lift ((H ⧸ orbStab X ω) →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show orbAlphaL X ω (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single x 1))
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbAlphaL X ω (Finsupp.single x 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbAlphaL_single, orbAlphaL_single]
  show orbAlphaBasis X ω (h • x) = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbAlphaBasis X ω x)
  have horb : orb X (h • x) = orb X x :=
    Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x h))
  rw [orbAlphaBasis, orbAlphaBasis]
  by_cases hx : orb X x = ω
  · have hx' : orb X (h • x) = ω := horb.trans hx
    rw [dif_pos hx', dif_pos hx, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      show orbPsi X ω ⟨h • x, _⟩ = h • orbPsi X ω ⟨x, _⟩ from orbPsi_smul_apply X ω h x _ _]
  · have hx' : ¬ (orb X (h • x) = ω) := fun hc => hx (horb ▸ hc)
    rw [dif_neg hx', dif_neg hx, Finsupp.lmapDomain_apply]
    simp

/-- **`β` 的等变性**（`Finsupp` 层）。 -/
lemma orbBetaL_mapDomain (ω : OrbitQ X) (h : H) :
    (orbBetaL X ω).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = (Finsupp.lmapDomain ℤ ℤ (h • ·)).comp (orbBetaL X ω) := by
  refine (Finsupp.lift (X →₀ ℤ) ℤ (H ⧸ orbStab X ω)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show orbBetaL X ω (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single q 1))
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbBetaL X ω (Finsupp.single q 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbBetaL_single, orbBetaL_single]
  show orbBetaBasis X ω (h • q) = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbBetaBasis X ω q)
  rw [orbBetaBasis, orbBetaBasis, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    show ((orbPsi X ω).symm (h • q) : X) = h • ((orbPsi X ω).symm q : X) from
      orbPsi_symm_smul X ω h q]

/-! ## 3. `Rep` 层的两个态射 -/

/-- `α_ω : ℤ[X] ⟶ ℤ[H/K_ω]` 的底层线性映射（共轭到 `MonoidAlgebra` 层）。 -/
noncomputable def orbAlphaLinear (ω : OrbitQ X) :
    MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ (H ⧸ orbStab X ω) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((orbAlphaL X ω).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

/-- `β_ω : ℤ[H/K_ω] ⟶ ℤ[X]` 的底层线性映射。 -/
noncomputable def orbBetaLinear (ω : OrbitQ X) :
    MonoidAlgebra ℤ (H ⧸ orbStab X ω) →ₗ[ℤ] MonoidAlgebra ℤ X :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((orbBetaL X ω).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

/-- 共轭下「左作用 = `lmapDomain`」。 -/
lemma coeff_rho (Y : Type) [MulAction H Y] (h : H) (w : MonoidAlgebra ℤ Y) :
    (MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ H Y).ρ h w)
      = Finsupp.lmapDomain ℤ ℤ (h • ·) ((MonoidAlgebra.coeffLinearEquiv ℤ) w) := by
  rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- 共轭下「右作用 = `lmapDomain`」（在参数上）。 -/
lemma coeff_rho_symm (Y : Type) [MulAction H Y] (h : H) (v : Y →₀ ℤ) :
    (Rep.ofMulAction ℤ H Y).ρ h ((MonoidAlgebra.coeffLinearEquiv ℤ).symm v)
      = (MonoidAlgebra.coeffLinearEquiv ℤ).symm (Finsupp.lmapDomain ℤ ℤ (h • ·) v) := by
  rw [Representation.ofMulAction_def]
  simp

/-- `α_ω` 的等变性。 -/
lemma orbAlphaLinear_comm (ω : OrbitQ X) (h : H) :
    (orbAlphaLinear X ω).comp ((Rep.ofMulAction ℤ H X).ρ h)
      = ((permHK (orbStab X ω)).ρ h).comp (orbAlphaLinear X ω) := by
  refine LinearMap.ext (fun w => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbAlphaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ H X).ρ h w)))
    = ((permHK (orbStab X ω)).ρ h)
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbAlphaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) w)))
  rw [coeff_rho, coeff_rho_symm]
  congr 1
  exact LinearMap.congr_fun (orbAlphaL_mapDomain X ω h) ((MonoidAlgebra.coeffLinearEquiv ℤ) w)

/-- `β_ω` 的等变性。 -/
lemma orbBetaLinear_comm (ω : OrbitQ X) (h : H) :
    (orbBetaLinear X ω).comp ((permHK (orbStab X ω)).ρ h)
      = ((Rep.ofMulAction ℤ H X).ρ h).comp (orbBetaLinear X ω) := by
  refine LinearMap.ext (fun u => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbBetaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) ((permHK (orbStab X ω)).ρ h u)))
    = ((Rep.ofMulAction ℤ H X).ρ h)
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u)))
  rw [coeff_rho, coeff_rho_symm]
  congr 1
  exact LinearMap.congr_fun (orbBetaL_mapDomain X ω h) ((MonoidAlgebra.coeffLinearEquiv ℤ) u)

/-- `α_ω : ℤ[X] ⟶ ℤ[H/K_ω]`。 -/
noncomputable def orbAlpha (ω : OrbitQ X) :
    Rep.ofMulAction ℤ H X ⟶ permHK (orbStab X ω) :=
  Rep.ofHom (Representation.IntertwiningMap.mk (orbAlphaLinear X ω) (orbAlphaLinear_comm X ω))

/-- `β_ω : ℤ[H/K_ω] ⟶ ℤ[X]`。 -/
noncomputable def orbBeta (ω : OrbitQ X) :
    permHK (orbStab X ω) ⟶ Rep.ofMulAction ℤ H X :=
  Rep.ofHom (Representation.IntertwiningMap.mk (orbBetaLinear X ω) (orbBetaLinear_comm X ω))

/-! ## 4. 两个复合恒等式 -/

/-- **`α ∘ β = id`**（`Finsupp` 层）。 -/
lemma orbAlphaL_comp_orbBetaL (ω : OrbitQ X) :
    (orbAlphaL X ω).comp (orbBetaL X ω) = LinearMap.id := by
  classical
  refine (Finsupp.lift ((H ⧸ orbStab X ω) →₀ ℤ) ℤ (H ⧸ orbStab X ω)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply]
  show orbAlphaL X ω (orbBetaL X ω (Finsupp.single q 1)) = Finsupp.single q 1
  rw [orbBetaL_single, orbBetaBasis, orbAlphaL_single]
  show orbAlphaBasis X ω (((orbPsi X ω).symm q : MulAction.orbit H (orbRep X ω)) : X)
      = Finsupp.single q 1
  have horb : orb X (((orbPsi X ω).symm q : MulAction.orbit H (orbRep X ω)) : X) = ω := by
    conv_rhs => rw [show ω = orb X (orbRep X ω) from (orbRep_eq X ω).symm]
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr ((orbPsi X ω).symm q).2)
  rw [orbAlphaBasis, dif_pos horb]
  congr 1
  exact Equiv.apply_symm_apply (orbPsi X ω) q

/-- **`Σ_ω (β_ω ∘ α_ω) = 𝟙`**（`Finsupp` 层）；在基向量 `single x 1` 上取值即
「落在 `O_{orb x}` 的那一项留下 `single x 1`，其余为零」。 -/
lemma sum_orbBetaL_comp_orbAlphaL :
    (∑ ω : OrbitQ X, (orbBetaL X ω).comp (orbAlphaL X ω)) = LinearMap.id := by
  classical
  refine (Finsupp.lift (X →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show (∑ ω : OrbitQ X, (orbBetaL X ω).comp (orbAlphaL X ω)) (Finsupp.single x 1)
      = Finsupp.single x 1
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (orb X x)]
  · rw [LinearMap.comp_apply, orbAlphaL_single, orbAlphaBasis, dif_pos rfl, orbBetaL_single,
      orbBetaBasis]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply (orbPsi X (orb X x)) ⟨x, _⟩)
  · intro b _ hb
    rw [LinearMap.comp_apply, orbAlphaL_single, orbAlphaBasis, dif_neg (fun hc => hb hc.symm),
      map_zero]
  · intro h
    exact absurd (Finset.mem_univ (orb X x)) h

/-- **`β_ω ≫ α_ω = 𝟙`**（在 `ℤ[H/K_ω]` 上）。 -/
theorem orbBeta_comp_orbAlpha (ω : OrbitQ X) :
    orbBeta X ω ≫ orbAlpha X ω = 𝟙 (permHK (orbStab X ω)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun u => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbAlphaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ)
        ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
          (orbBetaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))))) = u
  rw [LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply, orbAlphaL_comp_orbBetaL,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- **`Σ_ω (α_ω ≫ β_ω) = 𝟙`**（在 `ℤ[X]` 上）。 -/
theorem sum_orbAlpha_comp_orbBeta :
    (∑ ω : OrbitQ X, orbAlpha X ω ≫ orbBeta X ω)
      = 𝟙 (Rep.ofMulAction ℤ H X) := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun u => ?_)
  show (∑ ω : OrbitQ X, orbAlpha X ω ≫ orbBeta X ω) u
      = (𝟙 (Rep.ofMulAction ℤ H X)) u
  rw [repHom_sum_apply]
  have hterm : ∀ ω : OrbitQ X, (orbAlpha X ω ≫ orbBeta X ω) u
      = (MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaL X ω (orbAlphaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))) := by
    intro ω
    show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ)
          ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
            (orbAlphaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Rep.id_apply]
  rw [← map_sum]
  rw [show (∑ ω : OrbitQ X, orbBetaL X ω (orbAlphaL X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u)))
        = ∑ ω : OrbitQ X, (orbBetaL X ω).comp (orbAlphaL X ω)
            ((MonoidAlgebra.coeffLinearEquiv ℤ) u)
      from Finset.sum_congr rfl (fun ω _ => (LinearMap.comp_apply _ _ _).symm)]
  rw [show (∑ ω : OrbitQ X, (orbBetaL X ω).comp (orbAlphaL X ω)
          ((MonoidAlgebra.coeffLinearEquiv ℤ) u))
        = (∑ ω : OrbitQ X, (orbBetaL X ω).comp (orbAlphaL X ω))
          ((MonoidAlgebra.coeffLinearEquiv ℤ) u) from (LinearMap.sum_apply _ _ _).symm,
    sum_orbBetaL_comp_orbAlphaL, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-! ## 5. 组装：`perm_exp` 与 `stable_exp` -/

/-- **命名中间态射**（组装期一律走这些常量，避免大项反复展开导致归一爆炸）。 -/
noncomputable def orbE (ω : OrbitQ X) : Rep.ofMulAction ℤ H X ⟶ Rep.ofMulAction ℤ H X :=
  orbAlpha X ω ≫ orbBeta X ω

/-- `α_ω` 在 `coh²` 上诱导的映射。 -/
noncomputable def orbAlphaCoh (ω : OrbitQ X) :
    groupCohomology (Rep.ofMulAction ℤ H X) 2 ⟶ groupCohomology (permHK (orbStab X ω)) 2 :=
  groupCohomology.map (MonoidHom.id H) (orbAlpha X ω) 2

/-- `β_ω` 在 `coh²` 上诱导的映射。 -/
noncomputable def orbBetaCoh (ω : OrbitQ X) :
    groupCohomology (permHK (orbStab X ω)) 2 ⟶ groupCohomology (Rep.ofMulAction ℤ H X) 2 :=
  groupCohomology.map (MonoidHom.id H) (orbBeta X ω) 2

/-- `E_ω` 在 `coh²` 上诱导的映射（**直接定义为复合**，省去与 `map (E_ω)` 的等式搬运）。 -/
noncomputable def orbCoh (ω : OrbitQ X) :
    groupCohomology (Rep.ofMulAction ℤ H X) 2 ⟶ groupCohomology (Rep.ofMulAction ℤ H X) 2 :=
  orbAlphaCoh X ω ≫ orbBetaCoh X ω

lemma sum_orbE : (∑ ω : OrbitQ X, orbE X ω) = 𝟙 (Rep.ofMulAction ℤ H X) :=
  sum_orbAlpha_comp_orbBeta X

lemma cohMap_sum_orbE :
    groupCohomology.map (MonoidHom.id H) (∑ ω : OrbitQ X, orbE X ω) 2
      = ∑ ω : OrbitQ X, orbCoh X ω := by
  rw [cohMap_sum Finset.univ (fun ω : OrbitQ X => orbE X ω) 2]
  exact Finset.sum_congr rfl (fun ω _ =>
    groupCohomology.map_id_comp (orbAlpha X ω) (orbBeta X ω) 2)

/-- `ModuleCat` 态射的有限和在点上的取值（同 `repHom_sum_apply` 的工艺）。 -/
lemma moduleCat_sum_hom_apply {ι : Type} (s : Finset ι) {M N : ModuleCat ℤ}
    (f : ι → (M ⟶ N)) (x : M) : ((∑ i ∈ s, f i)).hom x = ∑ i ∈ s, (f i).hom x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show ((f a).hom + ((∑ x_1 ∈ s, f x_1)).hom) x
        = (f a).hom x + ∑ x_1 ∈ s, (f x_1).hom x
      rw [LinearMap.add_apply, ih]

/-- **`ℤ`-标量与有限和交换**（走 `ZSMul` 实例，避开 `ZSMul.toSMul` 与 `Module.toSMul`
的实例分叉——后者使 `rw [Finset.smul_sum]` 报「找不到模式」，见 §工艺要点）。 -/
lemma zsmul_finset_sum {ι M : Type} [AddCommGroup M] (n : ℤ) (s : Finset ι) (f : ι → M) :
    n • (∑ i ∈ s, f i) = ∑ i ∈ s, n • f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zsmul_add, ih]

/-- `H = C₃ × C₃` 的指数整除 3（有限型，`decide`）。 -/
theorem H_pow_three : ∀ x : H, x ^ 3 = 1 := by decide

/-- **`3` 消没 `coh²(H, ℤ[X])`**（有限 `H`-集 `X`）。

组装（**不用**双积）：轨道幂等分解 `Σ_ω E_ω = 𝟙` 给出 `x = Σ_ω (E_ω)_* x`；
每项经 `coh²(H, ℤ[H/K_ω])` 分解，后者被 `3` 零化（S3 的 `threeKills_permHK`）
⟹ 逐项零 ⟹ `3x = 0`。 -/
theorem threeKills_ofMulAction : Coh2ExpDvd3 (Rep.ofMulAction ℤ H X) := by
  classical
  have hH : ∀ x : H, x ^ 3 = 1 := H_pow_three
  intro x
  have hsplit : x = ∑ ω : OrbitQ X, (orbCoh X ω).hom x := by
    calc x = (groupCohomology.map (MonoidHom.id H) (𝟙 (Rep.ofMulAction ℤ H X)) 2).hom x := by
          rw [groupCohomology.map_id]; rfl
      _ = (groupCohomology.map (MonoidHom.id H) (∑ ω : OrbitQ X, orbE X ω) 2).hom x := by
          rw [show (𝟙 (Rep.ofMulAction ℤ H X)) = ∑ ω : OrbitQ X, orbE X ω
                from (sum_orbE X).symm]
      _ = (∑ ω : OrbitQ X, orbCoh X ω).hom x := by rw [cohMap_sum_orbE]
      _ = ∑ ω : OrbitQ X, (orbCoh X ω).hom x := moduleCat_sum_hom_apply Finset.univ _ x
  have hterm : ∀ ω : OrbitQ X, (3 : ℤ) • (orbCoh X ω).hom x = 0 := by
    intro ω
    have h3 : (3 : ℤ) • (orbAlphaCoh X ω).hom x = 0 := threeKills_permHK (orbStab X ω) hH _
    rw [show (orbCoh X ω).hom x
          = (orbBetaCoh X ω).hom ((orbAlphaCoh X ω).hom x) from by
      rw [orbCoh, ModuleCat.comp_apply]]
    rw [← map_zsmul, h3, map_zero]
  calc (3 : ℤ) • x
      = (3 : ℤ) • ∑ ω : OrbitQ X, (orbCoh X ω).hom x := by conv_lhs => rw [hsplit]
    _ = ∑ ω : OrbitQ X, (3 : ℤ) • (orbCoh X ω).hom x :=
        zsmul_finset_sum (3 : ℤ) Finset.univ _
    _ = 0 := Finset.sum_eq_zero fun ω _ => hterm ω

end Orbit

/-! ## 6. `perm_exp` 与 `stable_exp` -/

/-- **论文 `prop:perm-exponent`**：置换格 `L` 上 `3` 消没 `coh²`。 -/
theorem perm_exp (L : Rep ℤ H) (hL : IsPermutationLattice L) : Coh2ExpDvd3 L := by
  obtain ⟨X, hF, hA, ⟨e⟩⟩ := hL
  letI : Fintype X := hF
  letI : MulAction H X := hA
  exact kills_of_iso e.symm (threeKills_ofMulAction X)

/-- **论文 `prop:stable-exp`**：稳定置换格 `L` 上 `3` 消没 `coh²`。

由 S1 的转移引理 `kills_of_biprod_iso` 从 `Q = L ⊞ P` 拉回。 -/
theorem stable_exp (L : Rep ℤ H) (hL : IsStablyPermutation L) : Coh2ExpDvd3 L := by
  obtain ⟨P, Q, hP, hQ, ⟨e⟩⟩ := hL
  exact kills_of_biprod_iso L P Q e (perm_exp Q hQ)

/-! ## 公理闸门 -/

#print axioms orbBeta_comp_orbAlpha
#print axioms sum_orbAlpha_comp_orbBeta
#print axioms threeKills_ofMulAction
#print axioms perm_exp
#print axioms stable_exp

end ABGV52
