/-
  ABGV-5.2 —— 缺口 1（首要）：`lem:invertible-coflasque`（2.6）**全子群形**的一般群层

  问题
  ====
  2.6 的逐字结论：有限群 `H` 的 `ℤ[H]`-格 `M` 若是某置换格的直和项，则对**一切**子群
  `K ≤ H` 有 `coh¹(K, M|_K) = 0`（即 `M` 是 coflasque，`def:flasque-coflasque`）。

  工程既有层（`S2`／`S3`／`S4`／`EMQuasi`）已把 Shapiro 桥 `ℤ[H/K] ⟶ Coind_K^H(ℤ)` 与
  轨道幂等分解做完，但**固定在顶层群 `H = C₃ × C₃`** 上；2.6 的全子群形要求在**任意
  子群**（即任意有限群）上运行同一套机器。本件即该推广——把两块逐条搬到变量群
  `G`（`[Group G] [Fintype G]`）上：

    * `subsingleton_permCosetG`：`coh¹(G, ℤ[G/K]) = 0`（任意子群 `K ≤ G`；Shapiro）；
    * `subsingleton_ofMulAction_coh1G`：`coh¹(G, ℤ[X]) = 0`（任意有限 `G`-集 `X`；轨道分解）；
    * `subsingleton_perm_coh1G`：`coh¹(G, L) = 0`（任意置换 `ℤ[G]`-格 `L`）；
    * `isPermutationLattice_res`：置换格沿子群限制仍是置换格（`K`-轨道分解的存在形）；
    * `subsingleton_coh1_res_of_permutation`：**2.6 全子群形的缺失前提**
      （`Flasque_ABGV52.SubgroupPermCoh1Hyp`）——由此成为**定理**（不再是假设）。

  与既有件的关系（不重复造轮子，逐条对应）
  ======================================
    * §2 的构造与证明是 `S3_ABGV52.lean` §(c) 的**逐条推广**（`H` → 变量 `G`）；
    * §5 的轨道幂等分解是 `S4_ABGV52.lean` §1–5 的**度 1 版**（`3`-零化 → `Subsingleton`），
      组装段与 `EMQuasi_ABGV52.lean` §4b 同形（`subsingleton_permHK` → `subsingleton_permCosetG`）；
    * §3 的 `coh¹(K, ℤ) = 0` 是 `EMQuasi_ABGV52.lean` §4 同名件的变量群版
      （基数论证 ＋ `H1IsoOfIsTrivial`）。

  **无 sorry、无自造公理**；`#print axioms` 门见 §8。
-/
import ABGV52.S4_ABGV52
import ABGV52.D1_ABGV52
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

open CategoryTheory CategoryTheory.Limits

-- 组装段的大项归一较慢（同 S4 的实测）。
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace ABGV52

/-! ## §1 一般有限群：函子性与运输工具

`S1_ABGV52`／`EMQuasi_ABGV52` 的同名件固定顶层群 `H`；本节的版本对任意群 `G` 陈述。 -/

section Tools

variable {G : Type} [Group G]

/-- `cochainsMap` 对表示态射加法的加性（`S1_ABGV52.cochainsMap_add` 的一般群版）。 -/
lemma cochainsMap_add_gen {A B : Rep.{0,0,0} ℤ G} (φ ψ : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)
      = groupCohomology.cochainsMap (MonoidHom.id G) φ
        + groupCohomology.cochainsMap (MonoidHom.id G) ψ :=
  (groupCohomology.cochainsFunctor ℤ G).map_add

/-- **`map` 的 `ℤ`-加性**（`S1_ABGV52.cohMap_add` 的一般群版）。 -/
lemma cohMap_add_gen {A B : Rep.{0,0,0} ℤ G} (φ ψ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (φ + ψ) n
      = groupCohomology.map (MonoidHom.id G) φ n
        + groupCohomology.map (MonoidHom.id G) ψ n := by
  show HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)) n
      = HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) φ) n
        + HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) ψ) n
  rw [cochainsMap_add_gen, HomologicalComplex.homologyMap_add]

/-- `groupCohomology.map` 对**有限和**的加性（`S4_ABGV52.cohMap_sum` 的一般群版）。 -/
lemma cohMap_sum_gen {ι : Type} (s : Finset ι) {A B : Rep.{0,0,0} ℤ G}
    (f : ι → (A ⟶ B)) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (∑ i ∈ s, f i) n
      = ∑ i ∈ s, groupCohomology.map (MonoidHom.id G) (f i) n := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact (groupCohomology.functor ℤ G n).map_zero A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohMap_add_gen, ih]

/-- `ModuleCat` 态射的有限和在点上的取值（`EMQuasi_ABGV52.moduleCat_sum_hom_apply`
的一般群版）。 -/
lemma moduleCat_sum_hom_apply_gen {ι : Type} (s : Finset ι) {M N : ModuleCat ℤ}
    (f : ι → (M ⟶ N)) (x : M) : ((∑ i ∈ s, f i)).hom x = ∑ i ∈ s, (f i).hom x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show ((f a).hom + ((∑ x_1 ∈ s, f x_1)).hom) x
        = (f a).hom x + ∑ x_1 ∈ s, (f x_1).hom x
      rw [LinearMap.add_apply, ih]

/-- **`Rep` 态射的有限和在点上的取值**（`S4_ABGV52.repHom_sum_apply` 的一般群版）：
`(∑ f) u = ∑ f u`。语句用 `Rep` 的函数强制，避开 `AddCommGroup.toIntModule` 与
`Rep.hV2` 的实例菱形（S4 的工艺要点）。 -/
lemma repHom_sum_apply_gen {ι : Type} (s : Finset ι) {A B : Rep.{0,0,0} ℤ G}
    (f : ι → (A ⟶ B)) (u : A) : (∑ i ∈ s, f i) u = ∑ i ∈ s, (f i) u := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show (ConcreteCategory.hom (f a)) u + (ConcreteCategory.hom (∑ x ∈ s, f x)) u
        = (ConcreteCategory.hom (f a)) u + ∑ x ∈ s, (ConcreteCategory.hom (f x)) u
      rw [ih]

/-- `Subsingleton` 沿 `LinearEquiv` 拉回（靶侧已知；`EMQuasi` 同名件的一般群版）。 -/
theorem subsingleton_of_linearEquiv_gen {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : Subsingleton W) :
    Subsingleton V := by
  haveI := h
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- **`Subsingleton` 经收缩（retract）拉回**（度 1；`EMQuasi_ABGV52.subsingleton_coh1_of_retract`
与 `Flasque_ABGV52.subsingleton_cohomology_one_of_retract` 的一般群版）。 -/
theorem subsingleton_coh1_of_retract_gen {A B : Rep.{0,0,0} ℤ G} (γ : A ⟶ B) (δ : B ⟶ A)
    (h : γ ≫ δ = 𝟙 A) (hB : Subsingleton (cohOf G B 1)) :
    Subsingleton (cohOf G A 1) := by
  haveI := hB
  have hid : ∀ z : cohOf G A 1,
      (groupCohomology.map (MonoidHom.id G) δ 1).hom
        ((groupCohomology.map (MonoidHom.id G) γ 1).hom z) = z := by
    intro z
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, h, groupCohomology.map_id]
    rfl
  refine ⟨fun x y => ?_⟩
  calc x = (groupCohomology.map (MonoidHom.id G) δ 1).hom
        ((groupCohomology.map (MonoidHom.id G) γ 1).hom x) := (hid x).symm
    _ = (groupCohomology.map (MonoidHom.id G) δ 1).hom
        ((groupCohomology.map (MonoidHom.id G) γ 1).hom y) := by
        rw [Subsingleton.elim ((groupCohomology.map (MonoidHom.id G) γ 1).hom x)
          ((groupCohomology.map (MonoidHom.id G) γ 1).hom y)]
    _ = y := hid y

/-- 表示同构诱导的上同调**线性等价**（`S1_ABGV52.cohLinearEquivOfIso` 的一般群版）。 -/
noncomputable def cohLinearEquivOfIso_gen {A B : Rep.{0,0,0} ℤ G} (e : A ≅ B) (n : ℕ) :
    cohOf G A n ≃ₗ[ℤ] cohOf G B n where
  toFun := (groupCohomology.map (MonoidHom.id G) e.hom n).hom
  invFun := (groupCohomology.map (MonoidHom.id G) e.inv n).hom
  left_inv x := by
    show (groupCohomology.map (MonoidHom.id G) e.inv n).hom
      ((groupCohomology.map (MonoidHom.id G) e.hom n).hom x) = x
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, e.hom_inv_id,
      groupCohomology.map_id]
    rfl
  right_inv x := by
    show (groupCohomology.map (MonoidHom.id G) e.hom n).hom
      ((groupCohomology.map (MonoidHom.id G) e.inv n).hom x) = x
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, e.inv_hom_id,
      groupCohomology.map_id]
    rfl
  map_add' := fun x y => (groupCohomology.map (MonoidHom.id G) e.hom n).hom.map_add x y
  map_smul' := fun c x => (groupCohomology.map (MonoidHom.id G) e.hom n).hom.map_smul c x

end Tools

/-! ## §2 一般有限群：Shapiro 桥 `ℤ[G/K] ⟶ Coind_K^G(ℤ)`

逐条推广 `S3_ABGV52.lean` §(c)：陪集置换模的基像 `Φ(aK)(y) = [y · a ∈ K]`、
对偶侧 `f ↦ (aK ↦ f(a⁻¹))`、以及复合恒等式 `δ ∘ γ = 𝟙`。 -/

section Shapiro

variable {G : Type} [Group G] [Fintype G]

/-- `(h · ·)` 的单射性（`Finsupp.mapDomain_apply` 用）。 -/
lemma smulLeft_injectiveG (K : Subgroup G) (h : G) :
    Function.Injective (fun x : G ⧸ K => h • x) :=
  fun a b hab => by
    have := congrArg (fun x => h⁻¹ • x) hab
    simpa using this

/-- 陪集置换模 `ℤ[G/K]`（左陪集 `G ⧸ K` 上的置换表示）。 -/
noncomputable abbrev permCosetG (K : Subgroup G) : Rep.{0,0,0} ℤ G :=
  Rep.ofMulAction ℤ G (G ⧸ K)

/-- Shapiro 的对偶侧：`Coind_K^G(ℤ)`。 -/
noncomputable abbrev coindKG (K : Subgroup G) : Rep.{0,0,0} ℤ G :=
  Rep.coind K.subtype (Rep.trivial ℤ ↥K ℤ)

/-- `Coind_K^G(ℤ)` 的载体（`K`-左不变函数 `G → ℤ`）。 -/
noncomputable abbrev coindCarrierG (K : Subgroup G) : Type :=
  Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ)

/-- `Fintype`／`DecidableEq`（`G` 有限、`K` 任意子群；mathlib 未给陪集空间的实例）。 -/
noncomputable local instance fintypeQuotG (K : Subgroup G) : Fintype (G ⧸ K) :=
  Fintype.ofFinite _
noncomputable local instance decEqQuotG (K : Subgroup G) : DecidableEq (G ⧸ K) :=
  Classical.decEq _

/-- `K`-不变性的展开形式。 -/
lemma coindG_inv (K : Subgroup G) (f : coindCarrierG K) :
    ∀ (k : ↥K) (y : G), f.1 (↑k * y) = f.1 y := fun k y =>
  (Representation.mem_coindV K.subtype (Representation.trivial ℤ ↥K ℤ) f.1).mp f.2 k y

/-- `Coind` 侧作用的展开形式：`(h · f) y = f (y * h)`。 -/
lemma coindG_apply (K : Subgroup G) (h : G) (f : coindCarrierG K) (y : G) :
    ((coindKG K).ρ h f).1 y = f.1 (y * h) := rfl

/-- 基像的「代表元版」：`Φ̃(a) (y) = [y · a ∈ K]`。 -/
noncomputable def shapiroFunG (K : Subgroup G) (a : G) : G → ℤ := by
  classical
  exact fun y => if y * a ∈ K then (1 : ℤ) else 0

lemma shapiroFunG_wellDef (K : Subgroup G) {a a' : G}
    (h : (QuotientGroup.mk a : G ⧸ K) = QuotientGroup.mk a') :
    shapiroFunG K a = shapiroFunG K a' := by
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
lemma shapiroFunG_mem (K : Subgroup G) (a : G) :
    shapiroFunG K a ∈ Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ) := by
  classical
  rw [Representation.mem_coindV]
  intro k y
  show (if (↑k * y) * a ∈ K then (1 : ℤ) else 0) = (if y * a ∈ K then (1 : ℤ) else 0)
  rw [show (↑k * y) * a = ↑k * (y * a) from mul_assoc ↑k y a]
  by_cases hx : ↑k * (y * a) ∈ K
  · rw [if_pos hx, if_pos ((K.mul_mem_cancel_left k.2).mp hx)]
  · rw [if_neg hx, if_neg fun hc => hx (K.mul_mem k.2 hc)]

/-- 基像的陪集版（`Quotient.lift`，良定义性一次收口）。 -/
noncomputable def shapiroLiftedG (K : Subgroup G) (q : G ⧸ K) : G → ℤ :=
  Quotient.lift (shapiroFunG K) (fun a a' hab => shapiroFunG_wellDef K (Quotient.sound' hab)) q

@[simp] lemma shapiroLiftedG_mk (K : Subgroup G) (a : G) :
    shapiroLiftedG K (QuotientGroup.mk a) = shapiroFunG K a :=
  Quotient.lift_mk (shapiroFunG K)
    (fun a a' hab => shapiroFunG_wellDef K (Quotient.sound' hab)) a

lemma shapiroLiftedG_mem (K : Subgroup G) (q : G ⧸ K) :
    shapiroLiftedG K q ∈ Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ) := by
  induction q using Quotient.inductionOn' with
  | h a => rw [shapiroLiftedG_mk]; exact shapiroFunG_mem K a

/-- Shapiro 桥的基像：`Φ(q) ∈ Coind_K^G(ℤ)`。 -/
noncomputable def shapiroBasisG (K : Subgroup G) (q : G ⧸ K) : coindCarrierG K :=
  ⟨shapiroLiftedG K q, shapiroLiftedG_mem K q⟩

@[simp] lemma shapiroBasisG_mk (K : Subgroup G) (a : G) :
    (shapiroBasisG K (QuotientGroup.mk a)).1 = shapiroFunG K a :=
  shapiroLiftedG_mk K a

/-- **`Φ` 的等变性**：`Φ(h · q) = h · Φ(q)`。 -/
lemma shapiroBasisG_smul (K : Subgroup G) (h : G) (q : G ⧸ K) :
    (coindKG K).ρ h (shapiroBasisG K q) = shapiroBasisG K (h • q) := by
  classical
  apply Subtype.ext
  funext y
  show (shapiroBasisG K q).1 (y * h) = (shapiroBasisG K (h • q)).1 y
  induction q using Quotient.inductionOn' with
  | h a =>
    rw [show h • (QuotientGroup.mk a : G ⧸ K) = QuotientGroup.mk (h * a) from rfl]
    rw [shapiroBasisG_mk, shapiroBasisG_mk]
    show (if (y * h) * a ∈ K then (1 : ℤ) else 0) = (if y * (h * a) ∈ K then (1 : ℤ) else 0)
    rw [show (y * h) * a = y * (h * a) from mul_assoc y h a]

/-- `Finsupp` 侧的 Shapiro 桥：`(G ⧸ K →₀ ℤ) →ₗ Coind_K^G(ℤ)`，`single q 1 ↦ Φ(q)`。 -/
noncomputable def shapiroLiftG (K : Subgroup G) :
    ((G ⧸ K) →₀ ℤ) →ₗ[ℤ] coindCarrierG K :=
  (Finsupp.lift (coindCarrierG K) ℤ (G ⧸ K)) (shapiroBasisG K)

lemma shapiroLiftG_single (K : Subgroup G) (q : G ⧸ K) :
    shapiroLiftG K (Finsupp.single q 1) = shapiroBasisG K q := by
  rw [shapiroLiftG, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **等变性的 `Finsupp` 层形式**（线性映射层）：`lift Φ` 与 `G`-作用交换。 -/
lemma shapiroLiftG_mapDomain (K : Subgroup G) (h : G) :
    (shapiroLiftG K).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = ((coindKG K).ρ h).comp (shapiroLiftG K) := by
  refine (Finsupp.lift (coindCarrierG K) ℤ (G ⧸ K)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show shapiroLiftG K (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single q 1))
      = (coindKG K).ρ h (shapiroLiftG K (Finsupp.single q 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, shapiroLiftG_single, shapiroLiftG_single,
    shapiroBasisG_smul]

/-- Shapiro 桥 `ℤ[G/K] ⟶ Coind_K^G(ℤ)`。 -/
noncomputable def shapiroHomG (K : Subgroup G) : permCosetG K ⟶ coindKG K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    ((shapiroLiftG K).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)
    (by
      intro h
      refine LinearMap.ext (fun w => ?_)
      show shapiroLiftG K ((MonoidAlgebra.coeffLinearEquiv ℤ) ((permCosetG K).ρ h w))
          = (coindKG K).ρ h (shapiroLiftG K ((MonoidAlgebra.coeffLinearEquiv ℤ) w))
      rw [show (MonoidAlgebra.coeffLinearEquiv ℤ) ((permCosetG K).ρ h w)
            = Finsupp.lmapDomain ℤ ℤ (h • ·) ((MonoidAlgebra.coeffLinearEquiv ℤ) w) from by
        rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rfl]
      exact congrArg (fun (f : ((G ⧸ K) →₀ ℤ) →ₗ[ℤ] coindCarrierG K) => f _)
        (shapiroLiftG_mapDomain K h)))

/-- 对偶侧的代表元版：`f ↦ (a ↦ f(a⁻¹))`。 -/
noncomputable def shapiroOfCoindRawG (K : Subgroup G) (f : coindCarrierG K) : G → ℤ :=
  fun a => f.1 (a⁻¹)

lemma shapiroOfCoindRawG_wellDef (K : Subgroup G) (f : coindCarrierG K) {a a' : G}
    (h : (QuotientGroup.mk a : G ⧸ K) = QuotientGroup.mk a') :
    shapiroOfCoindRawG K f a = shapiroOfCoindRawG K f a' := by
  rw [QuotientGroup.eq] at h
  show f.1 (a⁻¹) = f.1 (a'⁻¹)
  rw [show a'⁻¹ = (a⁻¹ * a')⁻¹ * a⁻¹ from by group]
  exact (coindG_inv K f ⟨(a⁻¹ * a')⁻¹, K.inv_mem h⟩ a⁻¹).symm

/-- 对偶侧的陪集版（`Quotient.lift`，用 `K`-左不变性）。 -/
noncomputable def shapiroOfCoindFunG (K : Subgroup G) (f : coindCarrierG K) : (G ⧸ K) → ℤ :=
  Quotient.lift (shapiroOfCoindRawG K f)
    (fun a a' hab => shapiroOfCoindRawG_wellDef K f (Quotient.sound' hab))

@[simp] lemma shapiroOfCoindFunG_mk (K : Subgroup G) (f : coindCarrierG K) (a : G) :
    shapiroOfCoindFunG K f (QuotientGroup.mk a) = f.1 (a⁻¹) :=
  Quotient.lift_mk (shapiroOfCoindRawG K f)
    (fun a a' hab => shapiroOfCoindRawG_wellDef K f (Quotient.sound' hab)) a

/-- `Finsupp` 侧的逆映射：`f ↦ (q ↦ f(a⁻¹))`（`q = aK`）。 -/
noncomputable def shapiroOfCoindLiftG (K : Subgroup G) :
    coindCarrierG K →ₗ[ℤ] ((G ⧸ K) →₀ ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (G ⧸ K)).symm.toLinearMap.comp
    ({ toFun := shapiroOfCoindFunG K
       map_add' := fun f g => by
         funext q
         induction q using Quotient.inductionOn' with
         | h a => simp
       map_smul' := fun c f => by
         funext q
         induction q using Quotient.inductionOn' with
         | h a => simp } : coindCarrierG K →ₗ[ℤ] (G ⧸ K → ℤ))

@[simp] lemma shapiroOfCoindLiftG_apply (K : Subgroup G) (f : coindCarrierG K) (a : G) :
    shapiroOfCoindLiftG K f (QuotientGroup.mk a) = f.1 (a⁻¹) := by
  rw [shapiroOfCoindLiftG, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact shapiroOfCoindFunG_mk K f a

/-- **逆映射的等变性**（`Finsupp` 层，辅助形式：只在 `h · q'` 上验证）。 -/
lemma shapiroOfCoindLiftG_smul_aux (K : Subgroup G) (h : G) (f : coindCarrierG K)
    (q' : G ⧸ K) :
    shapiroOfCoindLiftG K ((coindKG K).ρ h f) (h • q')
      = Finsupp.mapDomain (h • ·) (shapiroOfCoindLiftG K f) (h • q') := by
  induction q' using Quotient.inductionOn' with
  | h b =>
    rw [Finsupp.mapDomain_apply (smulLeft_injectiveG K h) (shapiroOfCoindLiftG K f) b]
    rw [show h • (QuotientGroup.mk b : G ⧸ K) = QuotientGroup.mk (h * b) from rfl]
    rw [shapiroOfCoindLiftG_apply, shapiroOfCoindLiftG_apply, coindG_apply]
    show f.1 ((h * b)⁻¹ * h) = f.1 (b⁻¹)
    rw [show (h * b)⁻¹ * h = b⁻¹ from by group]

/-- **逆映射的等变性**（`Finsupp` 层）。 -/
lemma shapiroOfCoindLiftG_smul (K : Subgroup G) (h : G) (f : coindCarrierG K) :
    shapiroOfCoindLiftG K ((coindKG K).ρ h f)
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (shapiroOfCoindLiftG K f) := by
  ext q
  rw [Finsupp.lmapDomain_apply]
  rw [show q = h • (h⁻¹ • q) from (smul_inv_smul h q).symm]
  exact shapiroOfCoindLiftG_smul_aux K h f (h⁻¹ • q)

/-- Shapiro 桥的对偶侧 `Coind_K^G(ℤ) ⟶ ℤ[G/K]`。 -/
noncomputable def shapiroOfCoindG (K : Subgroup G) : coindKG K ⟶ permCosetG K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    ((MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (shapiroOfCoindLiftG K))
    (by
      intro h
      refine LinearMap.ext (fun f => ?_)
      show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
            (shapiroOfCoindLiftG K ((coindKG K).ρ h f))
          = (permCosetG K).ρ h
              ((MonoidAlgebra.coeffLinearEquiv ℤ).symm (shapiroOfCoindLiftG K f))
      rw [shapiroOfCoindLiftG_smul K h f]
      rw [show (permCosetG K).ρ h
              ((MonoidAlgebra.coeffLinearEquiv ℤ).symm (shapiroOfCoindLiftG K f))
            = (MonoidAlgebra.coeffLinearEquiv ℤ).symm
              (Finsupp.lmapDomain ℤ ℤ (h • ·) (shapiroOfCoindLiftG K f)) from by
        rw [Representation.ofMulAction_def]
        simp]))

/-- **复合恒等式（`Finsupp` 层）**：`δ ∘ γ = 𝟙`。

在基上：`δ(γ(e_{aK}))(bK) = [(b⁻¹ · a) ∈ K] = [bK = aK]`。 -/
theorem shapiroOfCoindLiftG_comp_shapiroLiftG (K : Subgroup G) :
    (shapiroOfCoindLiftG K).comp (shapiroLiftG K)
      = LinearMap.id (R := ℤ) (M := (G ⧸ K) →₀ ℤ) := by
  classical
  refine (Finsupp.lift ((G ⧸ K) →₀ ℤ) ℤ (G ⧸ K)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show shapiroOfCoindLiftG K (shapiroLiftG K (Finsupp.single q 1)) = Finsupp.single q 1
  rw [shapiroLiftG_single]
  show shapiroOfCoindLiftG K (shapiroBasisG K q) = Finsupp.single q 1
  ext q'
  induction q using Quotient.inductionOn' with
  | h a =>
    induction q' using Quotient.inductionOn' with
    | h b =>
      rw [shapiroOfCoindLiftG_apply, shapiroBasisG_mk, Finsupp.single_apply]
      have hiff : ((QuotientGroup.mk a : G ⧸ K) = QuotientGroup.mk b) ↔ b⁻¹ * a ∈ K := by
        rw [QuotientGroup.eq]
        exact ⟨fun h => by simpa using K.inv_mem h, fun h => by simpa using K.inv_mem h⟩
      rw [show shapiroFunG K a b⁻¹ = (if b⁻¹ * a ∈ K then (1 : ℤ) else 0) from rfl]
      by_cases hb : b⁻¹ * a ∈ K
      · rw [if_pos hb, if_pos (hiff.mpr hb)]
      · rw [if_neg hb, if_neg fun hc => hb (hiff.mp hc)]

/-- **Shapiro 桥的复合 = 恒等**（在 `ℤ[G/K]` 侧）：`γ ≫ δ = 𝟙`。 -/
theorem shapiroHomG_comp (K : Subgroup G) :
    shapiroHomG K ≫ shapiroOfCoindG K = 𝟙 (permCosetG K) := by
  apply Rep.hom_ext
  rw [Rep.hom_comp, Rep.hom_id]
  apply Representation.IntertwiningMap.ext
  show ((shapiroOfCoindG K).hom.toLinearMap.comp (shapiroHomG K).hom.toLinearMap)
      = LinearMap.id
  refine LinearMap.ext (fun w => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (shapiroOfCoindLiftG K (shapiroLiftG K ((MonoidAlgebra.coeffLinearEquiv ℤ) w))) = w
  rw [show shapiroOfCoindLiftG K (shapiroLiftG K ((MonoidAlgebra.coeffLinearEquiv ℤ) w))
        = (MonoidAlgebra.coeffLinearEquiv ℤ) w from
      congrArg (fun (f : ((G ⧸ K) →₀ ℤ) →ₗ[ℤ] ((G ⧸ K) →₀ ℤ)) =>
        f ((MonoidAlgebra.coeffLinearEquiv ℤ) w)) (shapiroOfCoindLiftG_comp_shapiroLiftG K)]
  exact LinearEquiv.symm_apply_apply _ _

end Shapiro

/-! ## §3 一般有限群：`coh¹(K, ℤ) = 0`

`EMQuasi_ABGV52.lean` §4 的变量群版（`K` 为任意有限群）：`coh¹(K,ℤ) ≅ Hom(K,ℤ)`，
后者由基数论证逐点零化。 -/

section TrivCoh

/-- 有限群到 `ℤ` 的加法同态逐点为零（基数论证：`card • x = 0` ＋ 无零因子）。 -/
theorem addHom_Z_apply_zero (K : Type) [Group K] [Fintype K]
    (f : Additive K →+ ↥(Rep.trivial ℤ K ℤ)) (x : Additive K) : f x = 0 := by
  have hx : Fintype.card (Additive K) • x = 0 := card_nsmul_eq_zero
  have h1 := map_nsmul f (Fintype.card (Additive K)) x
  rw [hx, map_zero] at h1
  have h2 : (Fintype.card (Additive K) : ℤ) * f x = 0 := by
    simpa only [Int.nsmul_eq_mul] using h1.symm
  have hc : (Fintype.card (Additive K) : ℤ) ≠ 0 := by
    haveI : Nonempty (Additive K) := ⟨Additive.ofMul 1⟩
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp h2).resolve_left hc

/-- `Hom(K, ℤ)` 上的 `Subsingleton`（逐点为零）。 -/
theorem subsingleton_addHom_Z (K : Type) [Group K] [Fintype K] :
    Subsingleton (Additive K →+ ↥(Rep.trivial ℤ K ℤ)) := by
  refine ⟨fun f g => ?_⟩
  ext x
  exact (addHom_Z_apply_zero K f x).trans (addHom_Z_apply_zero K g x).symm

/-- **任意有限群上 `coh¹(K, ℤtriv)` 消没**：`coh¹(K,ℤ) ≅ Hom(K,ℤ)`
（`H1IsoOfIsTrivial`），后者被逐点零化。 -/
theorem subsingleton_coh1_triv (K : Type) [Group K] [Fintype K] :
    Subsingleton (cohOf K (Rep.trivial ℤ K ℤ) 1) := by
  haveI : Subsingleton (Additive K →+ ↥(Rep.trivial ℤ K ℤ)) := subsingleton_addHom_Z K
  refine ⟨fun x y => ?_⟩
  exact (groupCohomology.H1IsoOfIsTrivial (k := ℤ) (G := K)
    (A := Rep.trivial ℤ K ℤ)).toLinearEquiv.injective (Subsingleton.elim _ _)

end TrivCoh

/-! ## §4 一般有限群：陪集置换格上 `coh¹` 消没（Shapiro 收缩） -/

section PermCoset

variable {G : Type} [Group G] [Fintype G]

/-- **`coh¹(G, ℤ[G/K]) = 0`**（`S3_ABGV52.subsingleton_permHK` 的一般群版）：
Shapiro 收缩 `ℤ[G/K] → Coind_K^G(ℤ) → ℤ[G/K]` ＋ `coh¹(G, Coind_K^G ℤ) ≅ coh¹(K,ℤ) = 0`。 -/
theorem subsingleton_permCosetG (K : Subgroup G) :
    Subsingleton (cohOf G (permCosetG K) 1) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  exact subsingleton_coh1_of_retract_gen (shapiroHomG K) (shapiroOfCoindG K)
    (shapiroHomG_comp K)
    (subsingleton_of_linearEquiv_gen
      (groupCohomology.coindIso (S := K) (Rep.trivial ℤ ↥K ℤ) 1).toLinearEquiv
      (subsingleton_coh1_triv ↥K))

end PermCoset

/-! ### §4b 共轭下的作用公式（只需 `[Group G]`，供 §8 复用） -/

section CoeffRhoG

variable {G : Type} [Group G]

/-- 共轭下「左作用 = `lmapDomain`」。 -/
lemma coeff_rhoG (Y : Type) [MulAction G Y] (h : G) (w : MonoidAlgebra ℤ Y) :
    (MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ G Y).ρ h w)
      = Finsupp.lmapDomain ℤ ℤ (h • ·) ((MonoidAlgebra.coeffLinearEquiv ℤ) w) := by
  rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- 共轭下「右作用 = `lmapDomain`」（在参数上）。 -/
lemma coeff_rhoG_symm (Y : Type) [MulAction G Y] (h : G) (v : Y →₀ ℤ) :
    (Rep.ofMulAction ℤ G Y).ρ h ((MonoidAlgebra.coeffLinearEquiv ℤ).symm v)
      = (MonoidAlgebra.coeffLinearEquiv ℤ).symm (Finsupp.lmapDomain ℤ ℤ (h • ·) v) := by
  rw [Representation.ofMulAction_def]
  simp

end CoeffRhoG

/-! ## §5 一般有限群：轨道幂等分解（度 1）

`S4_ABGV52.lean` §1–5 的度 1 版（`3`-零化 → `Subsingleton`），组装段与
`EMQuasi_ABGV52.lean` §4b 同形。 -/

section OrbitG

variable {G : Type} [Group G] [Fintype G]
variable (X : Type) [Fintype X] [MulAction G X]

/-- 轨道商 `X/G`（本节写作 `OrbQ`）。`G` 必须**显式**出现在类型里：若写成
不带 `G` 的 `abbrev`，`Fintype (OrbQ)` 之类的实例综合会因 `MulAction ?G X` 卡住
（`G` 是变量、不再是 S4 那样的具体群）。 -/
local notation "OrbQ" => MulAction.orbitRel.Quotient G X

/-- `OrbQ` 的 `Fintype`/`DecidableEq`（mathlib 未给；`noncomputable local instance`）。 -/
noncomputable local instance orbitQGFintype : Fintype (OrbQ) := Fintype.ofFinite _
noncomputable local instance orbitQGDecEq : DecidableEq (OrbQ) := Classical.decEq _

/-- `x` 所在的轨道。 -/
noncomputable abbrev orbG (x : X) : OrbQ := Quotient.mk'' x

/-- 轨道 `ω` 的代表元。 -/
noncomputable def orbRepG (ω : OrbQ) : X := Quotient.out ω

/-- 轨道 `ω` 的稳定子。 -/
noncomputable def orbStabG (ω : OrbQ) : Subgroup G :=
  MulAction.stabilizer G (orbRepG X ω)

/-- 轨道 ≃ 陪集空间。 -/
noncomputable def orbPsiG (ω : OrbQ) :
    MulAction.orbit G (orbRepG X ω) ≃ G ⧸ orbStabG X ω :=
  MulAction.orbitEquivQuotientStabilizer G (orbRepG X ω)

lemma orbRepG_eq (ω : OrbQ) : orbG X (orbRepG X ω) = ω := Quotient.out_eq' ω

/-- **`ψ.symm` 的等变性**（= `ofQuotientStabilizer_smul`）。 -/
lemma orbPsiG_symm_smul (ω : OrbQ) (h : G) (q : G ⧸ orbStabG X ω) :
    ((orbPsiG X ω).symm (h • q) : X) = h • ((orbPsiG X ω).symm q : X) :=
  MulAction.ofQuotientStabilizer_smul G (orbRepG X ω) h q

/-- **`ψ` 的等变性**（`⟨h · x, _⟩` 形式，避免 `h • ⟨x, _⟩` 的语法展开）。 -/
lemma orbPsiG_smul_apply (ω : OrbQ) (h : G) (x : X)
    (hx : x ∈ MulAction.orbit G (orbRepG X ω))
    (hx' : h • x ∈ MulAction.orbit G (orbRepG X ω)) :
    orbPsiG X ω ⟨h • x, hx'⟩ = h • orbPsiG X ω ⟨x, hx⟩ := by
  apply (orbPsiG X ω).symm.injective
  refine Subtype.ext ?_
  show (((orbPsiG X ω).symm (orbPsiG X ω ⟨h • x, hx'⟩)) : X)
      = (((orbPsiG X ω).symm (h • orbPsiG X ω ⟨x, hx⟩)) : X)
  rw [Equiv.symm_apply_apply, orbPsiG_symm_smul X ω h (orbPsiG X ω ⟨x, hx⟩),
    Equiv.symm_apply_apply]

/-! ### §5.1 `Finsupp` 层的两个映射 -/

/-- `α` 的基像：`x ↦ [x ∈ O_ω] · single (ψ x) 1`。 -/
noncomputable def orbAlphaBasisG (ω : OrbQ) (x : X) : (G ⧸ orbStabG X ω) →₀ ℤ := by
  classical
  exact if hx : orbG X x = ω then
    Finsupp.single (orbPsiG X ω ⟨x, MulAction.orbitRel_apply.mp
      (Quotient.exact (hx.trans (orbRepG_eq X ω).symm))⟩) 1
  else 0

/-- `β` 的基像：`single q 1 ↦ single (ψ.symm q) 1`。 -/
noncomputable def orbBetaBasisG (ω : OrbQ) (q : G ⧸ orbStabG X ω) : X →₀ ℤ :=
  Finsupp.single ((orbPsiG X ω).symm q : X) 1

/-- `α`（`Finsupp` 层）。 -/
noncomputable def orbAlphaLG (ω : OrbQ) :
    (X →₀ ℤ) →ₗ[ℤ] ((G ⧸ orbStabG X ω) →₀ ℤ) :=
  (Finsupp.lift ((G ⧸ orbStabG X ω) →₀ ℤ) ℤ X) (orbAlphaBasisG X ω)

/-- `β`（`Finsupp` 层）。 -/
noncomputable def orbBetaLG (ω : OrbQ) :
    ((G ⧸ orbStabG X ω) →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ) :=
  (Finsupp.lift (X →₀ ℤ) ℤ (G ⧸ orbStabG X ω)) (orbBetaBasisG X ω)

lemma orbAlphaLG_single (ω : OrbQ) (x : X) :
    orbAlphaLG X ω (Finsupp.single x 1) = orbAlphaBasisG X ω x := by
  rw [orbAlphaLG, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

lemma orbBetaLG_single (ω : OrbQ) (q : G ⧸ orbStabG X ω) :
    orbBetaLG X ω (Finsupp.single q 1) = orbBetaBasisG X ω q := by
  rw [orbBetaLG, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **`α` 的等变性**（`Finsupp` 层）。 -/
lemma orbAlphaLG_mapDomain (ω : OrbQ) (h : G) :
    (orbAlphaLG X ω).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = (Finsupp.lmapDomain ℤ ℤ (h • ·)).comp (orbAlphaLG X ω) := by
  classical
  refine (Finsupp.lift ((G ⧸ orbStabG X ω) →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show orbAlphaLG X ω (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single x 1))
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbAlphaLG X ω (Finsupp.single x 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbAlphaLG_single, orbAlphaLG_single]
  show orbAlphaBasisG X ω (h • x) = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbAlphaBasisG X ω x)
  have horb : orbG X (h • x) = orbG X x :=
    Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x h))
  rw [orbAlphaBasisG, orbAlphaBasisG]
  by_cases hx : orbG X x = ω
  · have hx' : orbG X (h • x) = ω := horb.trans hx
    rw [dif_pos hx', dif_pos hx, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      show orbPsiG X ω ⟨h • x, _⟩ = h • orbPsiG X ω ⟨x, _⟩ from orbPsiG_smul_apply X ω h x _ _]
  · have hx' : ¬ (orbG X (h • x) = ω) := fun hc => hx (horb ▸ hc)
    rw [dif_neg hx', dif_neg hx, Finsupp.lmapDomain_apply]
    simp

/-- **`β` 的等变性**（`Finsupp` 层）。 -/
lemma orbBetaLG_mapDomain (ω : OrbQ) (h : G) :
    (orbBetaLG X ω).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = (Finsupp.lmapDomain ℤ ℤ (h • ·)).comp (orbBetaLG X ω) := by
  refine (Finsupp.lift (X →₀ ℤ) ℤ (G ⧸ orbStabG X ω)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show orbBetaLG X ω (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single q 1))
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbBetaLG X ω (Finsupp.single q 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbBetaLG_single, orbBetaLG_single]
  show orbBetaBasisG X ω (h • q) = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbBetaBasisG X ω q)
  rw [orbBetaBasisG, orbBetaBasisG, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    show ((orbPsiG X ω).symm (h • q) : X) = h • ((orbPsiG X ω).symm q : X) from
      orbPsiG_symm_smul X ω h q]

/-! ### §5.2 `Rep` 层的两个态射 -/

/-- `α_ω : ℤ[X] ⟶ ℤ[G/K_ω]` 的底层线性映射（共轭到 `MonoidAlgebra` 层）。 -/
noncomputable def orbAlphaLinearG (ω : OrbQ) :
    MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ (G ⧸ orbStabG X ω) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((orbAlphaLG X ω).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

/-- `β_ω : ℤ[G/K_ω] ⟶ ℤ[X]` 的底层线性映射。 -/
noncomputable def orbBetaLinearG (ω : OrbQ) :
    MonoidAlgebra ℤ (G ⧸ orbStabG X ω) →ₗ[ℤ] MonoidAlgebra ℤ X :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((orbBetaLG X ω).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

/-- `α_ω` 的等变性。 -/
lemma orbAlphaLinearG_comm (ω : OrbQ) (h : G) :
    (orbAlphaLinearG X ω).comp ((Rep.ofMulAction ℤ G X).ρ h)
      = ((permCosetG (orbStabG X ω)).ρ h).comp (orbAlphaLinearG X ω) := by
  refine LinearMap.ext (fun w => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbAlphaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ G X).ρ h w)))
    = (permCosetG (orbStabG X ω)).ρ h
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbAlphaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) w)))
  rw [coeff_rhoG, coeff_rhoG_symm]
  congr 1
  exact LinearMap.congr_fun (orbAlphaLG_mapDomain X ω h) ((MonoidAlgebra.coeffLinearEquiv ℤ) w)

/-- `β_ω` 的等变性。 -/
lemma orbBetaLinearG_comm (ω : OrbQ) (h : G) :
    (orbBetaLinearG X ω).comp ((permCosetG (orbStabG X ω)).ρ h)
      = ((Rep.ofMulAction ℤ G X).ρ h).comp (orbBetaLinearG X ω) := by
  refine LinearMap.ext (fun u => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbBetaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) ((permCosetG (orbStabG X ω)).ρ h u)))
    = ((Rep.ofMulAction ℤ G X).ρ h)
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u)))
  rw [coeff_rhoG, coeff_rhoG_symm]
  congr 1
  exact LinearMap.congr_fun (orbBetaLG_mapDomain X ω h) ((MonoidAlgebra.coeffLinearEquiv ℤ) u)

/-- `α_ω : ℤ[X] ⟶ ℤ[G/K_ω]`。 -/
noncomputable def orbAlphaG (ω : OrbQ) :
    Rep.ofMulAction ℤ G X ⟶ permCosetG (orbStabG X ω) :=
  Rep.ofHom (Representation.IntertwiningMap.mk (orbAlphaLinearG X ω) (orbAlphaLinearG_comm X ω))

/-- `β_ω : ℤ[G/K_ω] ⟶ ℤ[X]`。 -/
noncomputable def orbBetaG (ω : OrbQ) :
    permCosetG (orbStabG X ω) ⟶ Rep.ofMulAction ℤ G X :=
  Rep.ofHom (Representation.IntertwiningMap.mk (orbBetaLinearG X ω) (orbBetaLinearG_comm X ω))

/-! ### §5.3 两个复合恒等式 -/

/-- **`α ∘ β = id`**（`Finsupp` 层）。 -/
lemma orbAlphaLG_comp_orbBetaLG (ω : OrbQ) :
    (orbAlphaLG X ω).comp (orbBetaLG X ω) = LinearMap.id := by
  classical
  refine (Finsupp.lift ((G ⧸ orbStabG X ω) →₀ ℤ) ℤ (G ⧸ orbStabG X ω)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply]
  show orbAlphaLG X ω (orbBetaLG X ω (Finsupp.single q 1)) = Finsupp.single q 1
  rw [orbBetaLG_single, orbBetaBasisG, orbAlphaLG_single]
  show orbAlphaBasisG X ω (((orbPsiG X ω).symm q : MulAction.orbit G (orbRepG X ω)) : X)
      = Finsupp.single q 1
  have horb : orbG X (((orbPsiG X ω).symm q : MulAction.orbit G (orbRepG X ω)) : X) = ω := by
    conv_rhs => rw [show ω = orbG X (orbRepG X ω) from (orbRepG_eq X ω).symm]
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr ((orbPsiG X ω).symm q).2)
  rw [orbAlphaBasisG, dif_pos horb]
  congr 1
  exact Equiv.apply_symm_apply (orbPsiG X ω) q

/-- **`Σ_ω (β_ω ∘ α_ω) = 𝟙`**（`Finsupp` 层）；在基向量 `single x 1` 上取值即
「落在 `O_{orb x}` 的那一项留下 `single x 1`，其余为零」。 -/
lemma sum_orbBetaLG_comp_orbAlphaLG :
    (∑ ω : OrbQ, (orbBetaLG X ω).comp (orbAlphaLG X ω)) = LinearMap.id := by
  classical
  refine (Finsupp.lift (X →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show (∑ ω : OrbQ, (orbBetaLG X ω).comp (orbAlphaLG X ω)) (Finsupp.single x 1)
      = Finsupp.single x 1
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (orbG X x)]
  · rw [LinearMap.comp_apply, orbAlphaLG_single, orbAlphaBasisG, dif_pos rfl, orbBetaLG_single,
      orbBetaBasisG]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply (orbPsiG X (orbG X x)) ⟨x, _⟩)
  · intro b _ hb
    rw [LinearMap.comp_apply, orbAlphaLG_single, orbAlphaBasisG, dif_neg (fun hc => hb hc.symm),
      map_zero]
  · intro h
    exact absurd (Finset.mem_univ (orbG X x)) h

/-- **`β_ω ≫ α_ω = 𝟙`**（在 `ℤ[G/K_ω]` 上）。 -/
theorem orbBetaG_comp_orbAlphaG (ω : OrbQ) :
    orbBetaG X ω ≫ orbAlphaG X ω = 𝟙 (permCosetG (orbStabG X ω)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun u => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbAlphaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ)
        ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
          (orbBetaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))))) = u
  rw [LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply, orbAlphaLG_comp_orbBetaLG,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- **`Σ_ω (α_ω ≫ β_ω) = 𝟙`**（在 `ℤ[X]` 上）。 -/
theorem sum_orbAlphaG_comp_orbBetaG :
    (∑ ω : OrbQ, orbAlphaG X ω ≫ orbBetaG X ω)
      = 𝟙 (Rep.ofMulAction ℤ G X) := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun u => ?_)
  show (∑ ω : OrbQ, orbAlphaG X ω ≫ orbBetaG X ω) u
      = (𝟙 (Rep.ofMulAction ℤ G X)) u
  rw [repHom_sum_apply_gen]
  have hterm : ∀ ω : OrbQ, (orbAlphaG X ω ≫ orbBetaG X ω) u
      = (MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaLG X ω (orbAlphaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))) := by
    intro ω
    show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ)
          ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
            (orbAlphaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Rep.id_apply]
  rw [← map_sum]
  rw [show (∑ ω : OrbQ, orbBetaLG X ω (orbAlphaLG X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u)))
        = ∑ ω : OrbQ, (orbBetaLG X ω).comp (orbAlphaLG X ω)
            ((MonoidAlgebra.coeffLinearEquiv ℤ) u)
      from Finset.sum_congr rfl (fun ω _ => (LinearMap.comp_apply _ _ _).symm)]
  rw [show (∑ ω : OrbQ, (orbBetaLG X ω).comp (orbAlphaLG X ω)
          ((MonoidAlgebra.coeffLinearEquiv ℤ) u))
        = (∑ ω : OrbQ, (orbBetaLG X ω).comp (orbAlphaLG X ω))
          ((MonoidAlgebra.coeffLinearEquiv ℤ) u) from (LinearMap.sum_apply _ _ _).symm,
    sum_orbBetaLG_comp_orbAlphaLG, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-! ### §5.4 组装：`coh¹(G, ℤ[X]) = 0` -/

/-- **命名中间态射**（组装期一律走这些常量，避免大项反复展开导致归一爆炸）。 -/
noncomputable def orbEG (ω : OrbQ) : Rep.ofMulAction ℤ G X ⟶ Rep.ofMulAction ℤ G X :=
  orbAlphaG X ω ≫ orbBetaG X ω

/-- `α_ω` 在 `coh¹` 上诱导的映射。 -/
noncomputable def orbAlphaCoh1G (ω : OrbQ) :
    groupCohomology (Rep.ofMulAction ℤ G X) 1 ⟶ groupCohomology (permCosetG (orbStabG X ω)) 1 :=
  groupCohomology.map (MonoidHom.id G) (orbAlphaG X ω) 1

/-- `β_ω` 在 `coh¹` 上诱导的映射。 -/
noncomputable def orbBetaCoh1G (ω : OrbQ) :
    groupCohomology (permCosetG (orbStabG X ω)) 1 ⟶ groupCohomology (Rep.ofMulAction ℤ G X) 1 :=
  groupCohomology.map (MonoidHom.id G) (orbBetaG X ω) 1

/-- `E_ω` 在 `coh¹` 上诱导的映射（直接定义为复合）。 -/
noncomputable def orbCoh1G (ω : OrbQ) :
    groupCohomology (Rep.ofMulAction ℤ G X) 1
      ⟶ groupCohomology (Rep.ofMulAction ℤ G X) 1 :=
  orbAlphaCoh1G X ω ≫ orbBetaCoh1G X ω

lemma sum_orbEG : (∑ ω : OrbQ, orbEG X ω) = 𝟙 (Rep.ofMulAction ℤ G X) :=
  sum_orbAlphaG_comp_orbBetaG X

lemma cohMap_sum_orbEG :
    groupCohomology.map (MonoidHom.id G) (∑ ω : OrbQ, orbEG X ω) 1
      = ∑ ω : OrbQ, orbCoh1G X ω := by
  rw [cohMap_sum_gen Finset.univ (fun ω : OrbQ => orbEG X ω) 1]
  exact Finset.sum_congr rfl (fun ω _ =>
    groupCohomology.map_id_comp (orbAlphaG X ω) (orbBetaG X ω) 1)

/-- **`coh¹(G, ℤ[X]) = 0`**（有限 `G`-集 `X`；`EMQuasi_ABGV52.subsingleton_ofMulAction_coh1`
的一般群版）。

组装（**不用**双积）：轨道幂等分解 `Σ_ω E_ω = 𝟙` 给出 `x = Σ_ω (E_ω)_* x`；
每项经 `coh¹(G, ℤ[G/K_ω])` 分解，后者消没（`subsingleton_permCosetG`）⟹ 逐项零。 -/
theorem subsingleton_ofMulAction_coh1G :
    Subsingleton (cohOf G (Rep.ofMulAction ℤ G X) 1) := by
  classical
  refine ⟨fun x y => ?_⟩
  have hsplit : ∀ z : cohOf G (Rep.ofMulAction ℤ G X) 1,
      z = ∑ ω : OrbQ, (orbCoh1G X ω).hom z := by
    intro z
    calc z = (groupCohomology.map (MonoidHom.id G) (𝟙 (Rep.ofMulAction ℤ G X)) 1).hom z := by
          rw [groupCohomology.map_id]; rfl
      _ = (groupCohomology.map (MonoidHom.id G) (∑ ω : OrbQ, orbEG X ω) 1).hom z := by
          rw [show (𝟙 (Rep.ofMulAction ℤ G X)) = ∑ ω : OrbQ, orbEG X ω
                from (sum_orbEG X).symm]
      _ = (∑ ω : OrbQ, orbCoh1G X ω).hom z := by rw [cohMap_sum_orbEG]
      _ = ∑ ω : OrbQ, (orbCoh1G X ω).hom z :=
          moduleCat_sum_hom_apply_gen Finset.univ _ z
  calc x = ∑ ω : OrbQ, (orbCoh1G X ω).hom x := hsplit x
    _ = ∑ ω : OrbQ, (orbCoh1G X ω).hom y := by
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        haveI : Subsingleton (cohOf G (permCosetG (orbStabG X ω)) 1) :=
          subsingleton_permCosetG (orbStabG X ω)
        have hω : (orbAlphaCoh1G X ω).hom x = (orbAlphaCoh1G X ω).hom y :=
          Subsingleton.elim _ _
        rw [show (orbCoh1G X ω).hom x
              = (orbBetaCoh1G X ω).hom ((orbAlphaCoh1G X ω).hom x) from by
          rw [orbCoh1G, ModuleCat.comp_apply]]
        rw [hω]
        rw [show (orbBetaCoh1G X ω).hom ((orbAlphaCoh1G X ω).hom y)
              = (orbCoh1G X ω).hom y from by
          rw [orbCoh1G, ModuleCat.comp_apply]]
    _ = y := (hsplit y).symm

end OrbitG

/-! ## §6 一般有限群：置换格上 `coh¹` 消没 -/

section PermLattice

variable {G : Type} [Group G] [Fintype G]

/-- **置换 `ℤ[G]`-格上 `coh¹` 消没**（`EMQuasi_ABGV52.subsingleton_perm_coh1` 的一般群版）：
展开 `IsPermutationLattice` 后经轨道分解。 -/
theorem subsingleton_perm_coh1G (L : Rep.{0,0,0} ℤ G) (hL : EM.IsPermutationLattice G L) :
    Subsingleton (cohOf G L 1) := by
  obtain ⟨X, hF, hA, ⟨e⟩⟩ := hL
  letI : Fintype X := hF
  letI : MulAction G X := hA
  exact subsingleton_of_linearEquiv_gen (cohLinearEquivOfIso_gen e 1)
    (subsingleton_ofMulAction_coh1G X)

end PermLattice

/-! ## §7 `H` 侧：限制仍是置换格 ⟹ 2.6 全子群形的缺失前提

置换格 `P ≅ ℤ[X]` 沿子群 `K ≤ H` 限制后是 `ℤ[X]`（同一 `X`，`K`-作用为限制作用），
故仍是置换格；配 §6 得 `coh¹(K, P|_K) = 0`。 -/

section Hside

/-- **限制不改变置换模**：`(ℤ[G X])|_K = ℤ[K X]`（`K`-作用为限制作用，
两者定义相等，故同构取 `Iso.refl`）。 -/
noncomputable def resOfMulActionIsoG {G : Type} [Group G] (K : Subgroup G) (X : Type)
    [MulAction G X] :
    Rep.res K.subtype (Rep.ofMulAction ℤ G X) ≅ Rep.ofMulAction ℤ ↥K X :=
  Iso.refl _

/-- **置换格沿子群限制仍是置换格**（`EM.IsPermutationLattice` 的 `Rep.res` 封闭性）。 -/
theorem isPermutationLattice_res {G : Type} [Group G] (K : Subgroup G)
    (P : Rep.{0,0,0} ℤ G) (hP : EM.IsPermutationLattice G P) :
    EM.IsPermutationLattice ↥K (Rep.res K.subtype P) := by
  obtain ⟨X, hF, hA, ⟨e⟩⟩ := hP
  letI : Fintype X := hF
  letI : MulAction G X := hA
  exact ⟨X, hF, inferInstance, ⟨(Rep.resFunctor K.subtype).mapIso e ≪≫ resOfMulActionIsoG K X⟩⟩

/-- `Hyp_ABGV52.IsPermutationLattice`（`H`-专用）与 `EM.IsPermutationLattice H` 的定义级桥
（两者体逐字相同；本件不导入 `EMQuasi` 的桥，故此处重声明一条）。 -/
theorem permutationLattice_bridge_H (P : Rep.{0,0,0} ℤ H) :
    EM.IsPermutationLattice H P ↔ _root_.ABGV52.IsPermutationLattice P :=
  Iff.rfl

/-- **2.6 全子群形的缺失前提（现为定理）**：`H` 的置换 `ℤ[H]`-格限制到任意子群
`K ≤ H` 后 `coh¹` 消没。

证明：`P|_K` 是置换 `ℤ[K]`-格（`isPermutationLattice_res`）⟹ §6 的
`subsingleton_perm_coh1G` 在群 `↥K` 上给出消没。 -/
theorem subsingleton_coh1_res_of_permutation (K : Subgroup H) (P : Rep.{0,0,0} ℤ H)
    (hP : _root_.ABGV52.IsPermutationLattice P) :
    Subsingleton ↥(groupCohomology (Rep.res K.subtype P) 1) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  exact subsingleton_perm_coh1G (Rep.res K.subtype P)
    (isPermutationLattice_res K P ((permutationLattice_bridge_H P).mpr hP))

end Hside

/-! ## §8 置换格对 `⊞` 封闭（`def:flasque-class`（2.4）传递性所需）

核心恒等式：`ℤ[X] ⊞ ℤ[Y] ≅ ℤ[X ⊕ Y]`（右端取 `Sum` 上的**对角** `G`-作用）。
证明走 `biprod.desc`／`biprod.lift`：四个分量映射 `ℤ[X] → ℤ[X⊕Y] ← ℤ[Y]` 与
`ℤ[X] ↤ ℤ[X⊕Y] → ℤ[Y]` 在 `Finsupp` 层用 `Finsupp.lmapDomain`（含入）
与 `Finsupp.lift`（取分量）显式给出，等变性经 `coeff` 共轭（`monoLin`）归到
`Finsupp.mapDomain` 的函子性。 -/

section BiprodClosure

variable {G : Type} [Group G]

/-- `Sum` 上的**对角** `G`-作用的底层函数（mathlib 未给 `MulAction G (X ⊕ Y)` 实例；
置换模的直和要走 `ℤ[X] ⊞ ℤ[Y] ≅ ℤ[X ⊕ Y]`，故必须显式供给）。 -/
def sumSmul (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) : X ⊕ Y → X ⊕ Y :=
  Sum.elim (fun x => Sum.inl (g • x)) (fun y => Sum.inr (g • y))

/-- 公理一（**在实例之外**先证：实例字面量内的 `•` 对 `simp` 不可见，见探针实测）。 -/
lemma sumSmul_one (X Y : Type) [MulAction G X] [MulAction G Y] (z : X ⊕ Y) :
    sumSmul X Y (1 : G) z = z := by
  cases z <;> simp [sumSmul]

/-- 公理二（同上，在实例之外先证）。 -/
lemma sumSmul_mul (X Y : Type) [MulAction G X] [MulAction G Y] (g h : G) (z : X ⊕ Y) :
    sumSmul X Y (g * h) z = sumSmul X Y g (sumSmul X Y h z) := by
  cases z <;> simp [sumSmul, mul_smul]

instance instMulActionSum (X Y : Type) [MulAction G X] [MulAction G Y] :
    MulAction G (X ⊕ Y) where
  smul g := sumSmul X Y g
  one_smul z := sumSmul_one X Y z
  mul_smul g h z := sumSmul_mul X Y g h z

@[simp] theorem sum_smul_inl (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) (x : X) :
    g • (Sum.inl x : X ⊕ Y) = Sum.inl (g • x) := rfl

@[simp] theorem sum_smul_inr (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) (y : Y) :
    g • (Sum.inr y : X ⊕ Y) = Sum.inr (g • y) := rfl

/-- `coeff` 共轭：把 `Finsupp` 层的线性映射搬到 `MonoidAlgebra` 层
（`S3`／`S4` 的「载体双层」工艺）。 -/
noncomputable def monoLin {X Z : Type} (L : (X →₀ ℤ) →ₗ[ℤ] (Z →₀ ℤ)) :
    MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Z :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    (L.comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

lemma monoLin_id {X : Type} :
    monoLin (LinearMap.id (R := ℤ) (M := X →₀ ℤ)) = LinearMap.id := by
  refine LinearMap.ext (fun w => ?_)
  simp [monoLin]

lemma monoLin_comp {X Z W : Type} (L : (X →₀ ℤ) →ₗ[ℤ] (Z →₀ ℤ))
    (M : (Z →₀ ℤ) →ₗ[ℤ] (W →₀ ℤ)) :
    (monoLin M).comp (monoLin L) = monoLin (M.comp L) := by
  refine LinearMap.ext (fun w => ?_)
  simp [monoLin]

lemma monoLin_add {X Z : Type} (L M : (X →₀ ℤ) →ₗ[ℤ] (Z →₀ ℤ)) :
    monoLin (L + M) = monoLin L + monoLin M := by
  refine LinearMap.ext (fun w => ?_)
  simp [monoLin]

/-- **`coeff` 共轭后的等变性**（`S4` 的 `coeff_rho`／`orbAlphaLinear_comm` 工艺）：
`Finsupp` 层与 `mapDomain` 交换 ⟹ `MonoidAlgebra` 层与 `G`-作用交换。 -/
lemma monoLin_comm {X Z : Type} [MulAction G X] [MulAction G Z]
    (L : (X →₀ ℤ) →ₗ[ℤ] (Z →₀ ℤ))
    (hL : ∀ (g : G) (v : X →₀ ℤ),
      L (Finsupp.mapDomain (g • ·) v) = Finsupp.mapDomain (g • ·) (L v))
    (g : G) :
    (monoLin L).comp ((Rep.ofMulAction ℤ G X).ρ g)
      = ((Rep.ofMulAction ℤ G Z).ρ g).comp (monoLin L) := by
  refine LinearMap.ext (fun w => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (L ((MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ G X).ρ g w)))
    = (Rep.ofMulAction ℤ G Z).ρ g
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm (L ((MonoidAlgebra.coeffLinearEquiv ℤ) w)))
  rw [coeff_rhoG, coeff_rhoG_symm]
  congr 1
  exact hL g ((MonoidAlgebra.coeffLinearEquiv ℤ) w)

/-! ### §8.1 四个分量映射（`Finsupp` 层） -/

/-- `ℤ[X] → ℤ[X ⊕ Y]`：`single x r ↦ single (inl x) r`。 -/
noncomputable def fspInl (X Y : Type) : (X →₀ ℤ) →ₗ[ℤ] ((X ⊕ Y) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Sum.inl : X → X ⊕ Y)

/-- `ℤ[Y] → ℤ[X ⊕ Y]`：`single y r ↦ single (inr y) r`。 -/
noncomputable def fspInr (X Y : Type) : (Y →₀ ℤ) →ₗ[ℤ] ((X ⊕ Y) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Sum.inr : Y → X ⊕ Y)

/-- `ℤ[X ⊕ Y] → ℤ[X]`：取 `X`-分量。 -/
noncomputable def fspFst (X Y : Type) : ((X ⊕ Y) →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ) :=
  (Finsupp.lift (X →₀ ℤ) ℤ (X ⊕ Y))
    (Sum.elim (fun x => Finsupp.single x (1 : ℤ)) (fun _ => 0))

/-- `ℤ[X ⊕ Y] → ℤ[Y]`：取 `Y`-分量。 -/
noncomputable def fspSnd (X Y : Type) : ((X ⊕ Y) →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ) :=
  (Finsupp.lift (Y →₀ ℤ) ℤ (X ⊕ Y))
    (Sum.elim (fun _ => 0) (fun y => Finsupp.single y (1 : ℤ)))

lemma fspInl_apply (X Y : Type) (v : X →₀ ℤ) :
    fspInl X Y v = Finsupp.mapDomain (Sum.inl : X → X ⊕ Y) v := rfl

lemma fspInr_apply (X Y : Type) (v : Y →₀ ℤ) :
    fspInr X Y v = Finsupp.mapDomain (Sum.inr : Y → X ⊕ Y) v := rfl

@[simp] lemma fspInl_single (X Y : Type) (x : X) (r : ℤ) :
    fspInl X Y (Finsupp.single x r) = Finsupp.single (Sum.inl x) r := by
  rw [fspInl_apply, Finsupp.mapDomain_single]

@[simp] lemma fspInr_single (X Y : Type) (y : Y) (r : ℤ) :
    fspInr X Y (Finsupp.single y r) = Finsupp.single (Sum.inr y) r := by
  rw [fspInr_apply, Finsupp.mapDomain_single]

@[simp] lemma fspFst_inl (X Y : Type) (x : X) (r : ℤ) :
    fspFst X Y (Finsupp.single (Sum.inl x) r) = Finsupp.single x r := by
  rw [fspFst, Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

@[simp] lemma fspFst_inr (X Y : Type) (y : Y) (r : ℤ) :
    fspFst X Y (Finsupp.single (Sum.inr y) r) = 0 := by
  rw [fspFst, Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

@[simp] lemma fspSnd_inl (X Y : Type) (x : X) (r : ℤ) :
    fspSnd X Y (Finsupp.single (Sum.inl x) r) = 0 := by
  rw [fspSnd, Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

@[simp] lemma fspSnd_inr (X Y : Type) (y : Y) (r : ℤ) :
    fspSnd X Y (Finsupp.single (Sum.inr y) r) = Finsupp.single y r := by
  rw [fspSnd, Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

/-! ### §8.2 等变性（`Finsupp` 层） -/

lemma fspInl_equiv (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) (v : X →₀ ℤ) :
    fspInl X Y (Finsupp.mapDomain (g • ·) v)
      = Finsupp.mapDomain (g • ·) (fspInl X Y v) := by
  rw [fspInl_apply, fspInl_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

lemma fspInr_equiv (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) (v : Y →₀ ℤ) :
    fspInr X Y (Finsupp.mapDomain (g • ·) v)
      = Finsupp.mapDomain (g • ·) (fspInr X Y v) := by
  rw [fspInr_apply, fspInr_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

lemma fspFst_mapDomain (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) :
    (fspFst X Y).comp (Finsupp.lmapDomain ℤ ℤ (g • ·))
      = (Finsupp.lmapDomain ℤ ℤ (g • ·)).comp (fspFst X Y) := by
  classical
  refine (Finsupp.lift (X →₀ ℤ) ℤ (X ⊕ Y)).symm.injective ?_
  funext z
  rcases z with x | y <;> simp [Finsupp.lift_symm_apply, Finsupp.mapDomain_single]

lemma fspFst_equiv (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) (v : (X ⊕ Y) →₀ ℤ) :
    fspFst X Y (Finsupp.mapDomain (g • ·) v)
      = Finsupp.mapDomain (g • ·) (fspFst X Y v) :=
  LinearMap.congr_fun (fspFst_mapDomain X Y g) v

lemma fspSnd_mapDomain (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) :
    (fspSnd X Y).comp (Finsupp.lmapDomain ℤ ℤ (g • ·))
      = (Finsupp.lmapDomain ℤ ℤ (g • ·)).comp (fspSnd X Y) := by
  classical
  refine (Finsupp.lift (Y →₀ ℤ) ℤ (X ⊕ Y)).symm.injective ?_
  funext z
  rcases z with x | y <;> simp [Finsupp.lift_symm_apply, Finsupp.mapDomain_single]

lemma fspSnd_equiv (X Y : Type) [MulAction G X] [MulAction G Y] (g : G) (v : (X ⊕ Y) →₀ ℤ) :
    fspSnd X Y (Finsupp.mapDomain (g • ·) v)
      = Finsupp.mapDomain (g • ·) (fspSnd X Y v) :=
  LinearMap.congr_fun (fspSnd_mapDomain X Y g) v

/-! ### §8.3 复合恒等式（`Finsupp` 层）

四条「分量复合」＋一条「分解」。每条都用 `Finsupp.lift` 的泛性质把验证收到基向量
`single z 1` 上（`Finsupp.lift_symm_apply`）。 -/

lemma fspFst_comp_fspInl (X Y : Type) :
    (fspFst X Y).comp (fspInl X Y) = LinearMap.id := by
  refine (Finsupp.lift (X →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  simp [Finsupp.lift_symm_apply]

lemma fspSnd_comp_fspInl (X Y : Type) :
    (fspSnd X Y).comp (fspInl X Y) = 0 := by
  refine (Finsupp.lift (Y →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  simp [Finsupp.lift_symm_apply]

lemma fspFst_comp_fspInr (X Y : Type) :
    (fspFst X Y).comp (fspInr X Y) = 0 := by
  refine (Finsupp.lift (X →₀ ℤ) ℤ Y).symm.injective ?_
  funext y
  simp [Finsupp.lift_symm_apply]

lemma fspSnd_comp_fspInr (X Y : Type) :
    (fspSnd X Y).comp (fspInr X Y) = LinearMap.id := by
  refine (Finsupp.lift (Y →₀ ℤ) ℤ Y).symm.injective ?_
  funext y
  simp [Finsupp.lift_symm_apply]

/-- **分解恒等式**：`w = (w 的 X-分量) + (w 的 Y-分量)`。 -/
lemma fspInl_comp_fspFst_add (X Y : Type) :
    (fspInl X Y).comp (fspFst X Y) + (fspInr X Y).comp (fspSnd X Y) = LinearMap.id := by
  classical
  refine (Finsupp.lift ((X ⊕ Y) →₀ ℤ) ℤ (X ⊕ Y)).symm.injective ?_
  funext z
  simp only [Finsupp.lift_symm_apply, LinearMap.add_apply, LinearMap.comp_apply]
  rcases z with x | y <;> simp

/-! ### §8.4 `Rep` 层的四个态射与同构 `ℤ[X] ⊞ ℤ[Y] ≅ ℤ[X ⊕ Y]` -/

/-- `ℤ[X] ⟶ ℤ[X ⊕ Y]`（含入）。 -/
noncomputable def sumInlHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    Rep.ofMulAction ℤ G X ⟶ Rep.ofMulAction ℤ G (X ⊕ Y) :=
  Rep.ofHom (Representation.IntertwiningMap.mk (monoLin (fspInl X Y))
    (monoLin_comm (fspInl X Y) (fun g v => fspInl_equiv X Y g v)))

/-- `ℤ[Y] ⟶ ℤ[X ⊕ Y]`（含入）。 -/
noncomputable def sumInrHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    Rep.ofMulAction ℤ G Y ⟶ Rep.ofMulAction ℤ G (X ⊕ Y) :=
  Rep.ofHom (Representation.IntertwiningMap.mk (monoLin (fspInr X Y))
    (monoLin_comm (fspInr X Y) (fun g v => fspInr_equiv X Y g v)))

/-- `ℤ[X ⊕ Y] ⟶ ℤ[X]`（取 `X`-分量）。 -/
noncomputable def sumFstHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    Rep.ofMulAction ℤ G (X ⊕ Y) ⟶ Rep.ofMulAction ℤ G X :=
  Rep.ofHom (Representation.IntertwiningMap.mk (monoLin (fspFst X Y))
    (monoLin_comm (fspFst X Y) (fun g v => fspFst_equiv X Y g v)))

/-- `ℤ[X ⊕ Y] ⟶ ℤ[Y]`（取 `Y`-分量）。 -/
noncomputable def sumSndHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    Rep.ofMulAction ℤ G (X ⊕ Y) ⟶ Rep.ofMulAction ℤ G Y :=
  Rep.ofHom (Representation.IntertwiningMap.mk (monoLin (fspSnd X Y))
    (monoLin_comm (fspSnd X Y) (fun g v => fspSnd_equiv X Y g v)))

@[simp] lemma sumInlHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G X)) :
    sumInlHom X Y w = monoLin (fspInl X Y) w := rfl

@[simp] lemma sumInrHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G Y)) :
    sumInrHom X Y w = monoLin (fspInr X Y) w := rfl

@[simp] lemma sumFstHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G (X ⊕ Y))) :
    sumFstHom X Y w = monoLin (fspFst X Y) w := rfl

@[simp] lemma sumSndHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G (X ⊕ Y))) :
    sumSndHom X Y w = monoLin (fspSnd X Y) w := rfl

lemma sumFstHom_sumInlHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G X)) : sumFstHom X Y (sumInlHom X Y w) = w := by
  rw [sumFstHom_apply, sumInlHom_apply, ← LinearMap.comp_apply, monoLin_comp,
    fspFst_comp_fspInl, monoLin_id, LinearMap.id_apply]

lemma sumSndHom_sumInlHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G X)) : sumSndHom X Y (sumInlHom X Y w) = 0 := by
  rw [sumSndHom_apply, sumInlHom_apply, ← LinearMap.comp_apply, monoLin_comp,
    fspSnd_comp_fspInl]
  rfl

lemma sumFstHom_sumInrHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G Y)) : sumFstHom X Y (sumInrHom X Y w) = 0 := by
  rw [sumFstHom_apply, sumInrHom_apply, ← LinearMap.comp_apply, monoLin_comp,
    fspFst_comp_fspInr]
  rfl

lemma sumSndHom_sumInrHom_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G Y)) : sumSndHom X Y (sumInrHom X Y w) = w := by
  rw [sumSndHom_apply, sumInrHom_apply, ← LinearMap.comp_apply, monoLin_comp,
    fspSnd_comp_fspInr, monoLin_id, LinearMap.id_apply]

lemma sumInlHom_sumFstHom_add_apply (X Y : Type) [MulAction G X] [MulAction G Y]
    (w : ↥(Rep.ofMulAction ℤ G (X ⊕ Y))) :
    sumInlHom X Y (sumFstHom X Y w) + sumInrHom X Y (sumSndHom X Y w) = w := by
  rw [sumInlHom_apply, sumInrHom_apply, sumFstHom_apply, sumSndHom_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, monoLin_comp, monoLin_comp,
    ← LinearMap.add_apply, ← monoLin_add, fspInl_comp_fspFst_add, monoLin_id,
    LinearMap.id_apply]

/-- 分量复合（`Rep` 层）：`sumInlHom ≫ sumFstHom = 𝟙 ℤ[X]`。 -/
lemma sumInlHom_comp_sumFstHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    sumInlHom X Y ≫ sumFstHom X Y = 𝟙 (Rep.ofMulAction ℤ G X) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun w => ?_)
  show sumFstHom X Y (sumInlHom X Y w) = w
  exact sumFstHom_sumInlHom_apply X Y w

/-- 分量复合（`Rep` 层）：`sumInrHom ≫ sumSndHom = 𝟙 ℤ[Y]`。 -/
lemma sumInrHom_comp_sumSndHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    sumInrHom X Y ≫ sumSndHom X Y = 𝟙 (Rep.ofMulAction ℤ G Y) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun w => ?_)
  show sumSndHom X Y (sumInrHom X Y w) = w
  exact sumSndHom_sumInrHom_apply X Y w

/-- 分量复合（`Rep` 层）：`sumInlHom ≫ sumSndHom = 0`。 -/
lemma sumInlHom_comp_sumSndHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    sumInlHom X Y ≫ sumSndHom X Y
      = (0 : Rep.ofMulAction ℤ G X ⟶ Rep.ofMulAction ℤ G Y) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun w => ?_)
  simpa using sumSndHom_sumInlHom_apply X Y w

/-- 分量复合（`Rep` 层）：`sumInrHom ≫ sumFstHom = 0`。 -/
lemma sumInrHom_comp_sumFstHom (X Y : Type) [MulAction G X] [MulAction G Y] :
    sumInrHom X Y ≫ sumFstHom X Y
      = (0 : Rep.ofMulAction ℤ G Y ⟶ Rep.ofMulAction ℤ G X) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun w => ?_)
  simpa using sumFstHom_sumInrHom_apply X Y w

/-- **分解恒等式（`Rep` 层）**：`sumFstHom ≫ sumInlHom + sumSndHom ≫ sumInrHom = 𝟙`。 -/
lemma sumFstHom_comp_sumInlHom_add (X Y : Type) [MulAction G X] [MulAction G Y] :
    sumFstHom X Y ≫ sumInlHom X Y + sumSndHom X Y ≫ sumInrHom X Y
      = 𝟙 (Rep.ofMulAction ℤ G (X ⊕ Y)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun w => ?_)
  show sumInlHom X Y (sumFstHom X Y w) + sumInrHom X Y (sumSndHom X Y w) = w
  exact sumInlHom_sumFstHom_add_apply X Y w

/-- **`biprod.desc f g = fst ≫ f + snd ≫ g`**（把 `desc` 写成两个投影项之和）。 -/
lemma biprod_desc_eq_fst_snd {A B C : Rep.{0,0,0} ℤ G} (f : A ⟶ C) (g : B ⟶ C) :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by
  apply biprod.hom_ext'
  · rw [Preadditive.comp_add, biprod.inl_desc, biprod.inl_fst_assoc, biprod.inl_snd_assoc]
    simp
  · rw [Preadditive.comp_add, biprod.inr_desc, biprod.inr_fst_assoc, biprod.inr_snd_assoc]
    simp

/-- `desc f g ≫ h = fst`（当 `f ≫ h = 𝟙`、`g ≫ h = 0`）。 -/
lemma biprod_desc_comp_eq_fst {A B C : Rep.{0,0,0} ℤ G} (f : A ⟶ C) (g : B ⟶ C)
    (h : C ⟶ A) (h₁ : f ≫ h = 𝟙 A) (h₂ : g ≫ h = 0) :
    biprod.desc f g ≫ h = biprod.fst := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_desc, h₁, biprod.inl_fst]
  · rw [← Category.assoc, biprod.inr_desc, h₂, biprod.inr_fst]

/-- `desc f g ≫ k = snd`（当 `f ≫ k = 0`、`g ≫ k = 𝟙`）。 -/
lemma biprod_desc_comp_eq_snd {A B C : Rep.{0,0,0} ℤ G} (f : A ⟶ C) (g : B ⟶ C)
    (k : C ⟶ B) (h₁ : f ≫ k = 0) (h₂ : g ≫ k = 𝟙 B) :
    biprod.desc f g ≫ k = biprod.snd := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_desc, h₁, biprod.inl_snd]
  · rw [← Category.assoc, biprod.inr_desc, h₂, biprod.inr_snd]

/-- **直和恒等式**：`desc f g ≫ lift h k = 𝟙`（四条分量恒等式 ⟹ 双积恒等）。 -/
lemma biprod_desc_comp_lift_eq_id {A B C : Rep.{0,0,0} ℤ G} (f : A ⟶ C) (g : B ⟶ C)
    (h : C ⟶ A) (k : C ⟶ B) (h₁ : f ≫ h = 𝟙 A) (h₂ : g ≫ h = 0)
    (h₃ : f ≫ k = 0) (h₄ : g ≫ k = 𝟙 B) :
    biprod.desc f g ≫ biprod.lift h k = 𝟙 (A ⊞ B) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, biprod_desc_comp_eq_fst f g h h₁ h₂, Category.id_comp]
  · rw [Category.assoc, biprod.lift_snd, biprod_desc_comp_eq_snd f g k h₃ h₄, Category.id_comp]

/-- **直和恒等式（反向）**：`lift h k ≫ desc f g = 𝟙`（用分解恒等式 `h ≫ f + k ≫ g = 𝟙`）。 -/
lemma biprod_lift_comp_desc_eq_id {A B C : Rep.{0,0,0} ℤ G} (f : A ⟶ C) (g : B ⟶ C)
    (h : C ⟶ A) (k : C ⟶ B) (h₅ : h ≫ f + k ≫ g = 𝟙 C) :
    biprod.lift h k ≫ biprod.desc f g = 𝟙 C := by
  rw [biprod_desc_eq_fst_snd, Preadditive.comp_add, ← Category.assoc, biprod.lift_fst,
    ← Category.assoc, biprod.lift_snd]
  exact h₅

/-- **核心同构**：`ℤ[X] ⊞ ℤ[Y] ≅ ℤ[X ⊕ Y]`（右端为 `Sum` 上的对角作用）。 -/
noncomputable def permSumIso (X Y : Type) [MulAction G X] [MulAction G Y] :
    Rep.ofMulAction ℤ G X ⊞ Rep.ofMulAction ℤ G Y ≅ Rep.ofMulAction ℤ G (X ⊕ Y) where
  hom := biprod.desc (sumInlHom X Y) (sumInrHom X Y)
  inv := biprod.lift (sumFstHom X Y) (sumSndHom X Y)
  hom_inv_id := biprod_desc_comp_lift_eq_id (sumInlHom X Y) (sumInrHom X Y)
    (sumFstHom X Y) (sumSndHom X Y) (sumInlHom_comp_sumFstHom X Y)
    (sumInrHom_comp_sumFstHom X Y) (sumInlHom_comp_sumSndHom X Y)
    (sumInrHom_comp_sumSndHom X Y)
  inv_hom_id := biprod_lift_comp_desc_eq_id (sumInlHom X Y) (sumInrHom X Y)
    (sumFstHom X Y) (sumSndHom X Y) (sumFstHom_comp_sumInlHom_add X Y)

/-- **置换格对 `⊞` 封闭**（`def:flasque-class`（2.4）相似关系传递性所需）：
两个置换格的直和仍是置换格（取 `X ⊕ Y`，对角作用）。 -/
theorem isPermutationLattice_biprod {P Q : Rep.{0,0,0} ℤ G}
    (hP : EM.IsPermutationLattice G P) (hQ : EM.IsPermutationLattice G Q) :
    EM.IsPermutationLattice G (P ⊞ Q) := by
  obtain ⟨X, hF, hA, ⟨e₁⟩⟩ := hP
  obtain ⟨Y, hG, hB, ⟨e₂⟩⟩ := hQ
  letI : Fintype X := hF
  letI : MulAction G X := hA
  letI : Fintype Y := hG
  letI : MulAction G Y := hB
  exact ⟨X ⊕ Y, inferInstance, inferInstance,
    ⟨biprod.mapIso e₁ e₂ ≪≫ permSumIso X Y⟩⟩

end BiprodClosure

/-! ## §9 公理闸门 -/

#print axioms shapiroHomG_comp
#print axioms subsingleton_coh1_triv
#print axioms subsingleton_permCosetG
#print axioms subsingleton_ofMulAction_coh1G
#print axioms subsingleton_perm_coh1G
#print axioms isPermutationLattice_res
#print axioms subsingleton_coh1_res_of_permutation
#print axioms permSumIso
#print axioms isPermutationLattice_biprod

end ABGV52
