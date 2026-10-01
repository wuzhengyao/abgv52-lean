/-
  ABGV-5.2 —— **P 档 P5b：显式 Shapiro 桥 ＋ 轨道分解**（C 档 `S3` ＋ `S4` 的 p 版）

  内容
  ====
    §0  p 版谓词（`IsPermutationLattice`／`IsStablyPermutation`）＋ 指数 `p` 的群事实
        （`Hp_pow_p : ∀ x : Hp p, x ^ p = 1`；C 档 `H_pow_three` 用 `by decide`，
        p 参数化后改用 `ZMod` 的 `p • x = 0`）；
    §1  （S3）**显式 Shapiro 桥** `ℤ[H/K] ≅ coind_⊥^H(ℤ)`（写子用 `Quotient.lift`），
        `kills_of_retract`（收缩引理）⟹ **`pKills_permHK`**；
    §2  （S4）**轨道分解**（`orbE`／`orbAlpha`／`orbBeta`／`orbCoh`）⟹
        `pKills_ofMulAction`（置换模）⟹ **`perm_exp`**（`prop:perm-exponent` 的 p 版）⟹
        **`stable_exp`**（论文 `prop:stable-exp` 的 p 版）。

  p-通用性：§1／§2 的论证只用到群公理、`Rep.ofMulAction` 的轨道结构、
  `MonoidAlgebra` 与 `Finset.sum` 的有限性 ⟹ 与 C 档逐字同构，仅换类型与常数。
-/
import ABGV52.P5a_ABGV52
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.TypeTags.Basic

open CategoryTheory CategoryTheory.Limits

namespace ABGV52.P

variable {p : ℕ} [Fact p.Prime]

/-! ## 0. p 版谓词与指数事实 -/

/-- **置换 `ℤ[Hp p]`-格**（论文 `def:lattice` 的 p 版）。 -/
def IsPermutationLattice (P : Rep ℤ (Hp p)) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : MulAction (Hp p) X),
    Nonempty (P ≅ Rep.ofMulAction ℤ (Hp p) X)

/-- **稳定置换格**（论文 `def:lattice` 的 p 版）。 -/
def IsStablyPermutation (L : Rep ℤ (Hp p)) : Prop :=
  ∃ (P Q : Rep ℤ (Hp p)), IsPermutationLattice P ∧ IsPermutationLattice Q ∧
    Nonempty (L ⊞ P ≅ Q)

/-- `Multiplicative (ZMod p)` 的一切元素 `p` 次幂为 1（加性侧：`p • x = 0`）。 -/
lemma zmodp_pow_p (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  have h0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  have htoadd : ∀ n : ℕ, (a ^ n).toAdd = n • a.toAdd := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [pow_succ, toAdd_mul, ih, succ_nsmul]
  have h : (a ^ p).toAdd = (1 : Multiplicative (ZMod p)).toAdd := by
    rw [htoadd p, nsmul_eq_mul, h0, zero_mul]
    rfl
  exact Multiplicative.toAdd.injective h

/-- **`Hp p` 的指数整除 `p`**（C 档 `H_pow_three` 的 p 版）。 -/
theorem Hp_pow_p : ∀ x : Hp p, x ^ p = 1 := by
  intro x
  obtain ⟨a, b⟩ := x
  exact Prod.ext (zmodp_pow_p a) (zmodp_pow_p b)

/-- `(h · ·)` 的单射性（`Finsupp.mapDomain_apply` 用）。 -/
lemma smulLeft_injective (K : Subgroup (Hp p)) (h : (Hp p)) :
    Function.Injective (fun x : (Hp p) ⧸ K => h • x) :=
  fun a b hab => by
    have := congrArg (fun x => h⁻¹ • x) hab
    simpa using this

/-! ## (c) Shapiro 桥：`ℤ[(Hp p)/K] ≅ Coind_K^(Hp p)(ℤ)` -/

/-- 置换模 `ℤ[(Hp p)/K]`（左陪集 `(Hp p) ⧸ K` 上的置换表示）。 -/
noncomputable abbrev permHK (K : Subgroup (Hp p)) : Rep ℤ (Hp p) := Rep.ofMulAction ℤ (Hp p) ((Hp p) ⧸ K)

/-- Shapiro 的对偶侧：`Coind_K^(Hp p)(ℤ)`。 -/
noncomputable abbrev coindK (K : Subgroup (Hp p)) : Rep ℤ (Hp p) :=
  Rep.coind K.subtype (Rep.trivial ℤ ↥K ℤ)

/-- `Coind_K^(Hp p)(ℤ)` 的载体（`K`-左不变函数 `(Hp p) → ℤ`）。 -/
noncomputable abbrev CoindCarrier (K : Subgroup (Hp p)) : Type :=
  Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ)

/-- `K`-不变性的展开形式。 -/
lemma coind_inv (K : Subgroup (Hp p)) (f : CoindCarrier K) :
    ∀ (k : ↥K) (y : (Hp p)), f.1 (↑k * y) = f.1 y := fun k y =>
  (Representation.mem_coindV K.subtype (Representation.trivial ℤ ↥K ℤ) f.1).mp f.2 k y

/-- `Coind` 侧作用的展开形式：`(h · f) y = f (y * h)`。 -/
lemma coind_apply (K : Subgroup (Hp p)) (h : (Hp p)) (f : CoindCarrier K) (y : (Hp p)) :
    ((coindK K).ρ h f).1 y = f.1 (y * h) := rfl

/-! ### (c.1) 基像 `Φ(q) = [y · out q ∈ K]` -/

/-- 基像的「代表元版」：`Φ̃(a) (y) = [y · a ∈ K]`。 -/
noncomputable def shapiroFun (K : Subgroup (Hp p)) (a : (Hp p)) : (Hp p) → ℤ := by
  classical
  exact fun y => if y * a ∈ K then (1 : ℤ) else 0

lemma shapiroFun_wellDef (K : Subgroup (Hp p)) {a a' : (Hp p)}
    (h : (QuotientGroup.mk a : (Hp p) ⧸ K) = QuotientGroup.mk a') :
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
lemma shapiroFun_mem (K : Subgroup (Hp p)) (a : (Hp p)) :
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
noncomputable def shapiroLifted (K : Subgroup (Hp p)) (q : (Hp p) ⧸ K) : (Hp p) → ℤ :=
  Quotient.lift (shapiroFun K) (fun a a' hab => shapiroFun_wellDef K (Quotient.sound' hab)) q

@[simp] lemma shapiroLifted_mk (K : Subgroup (Hp p)) (a : (Hp p)) :
    shapiroLifted K (QuotientGroup.mk a) = shapiroFun K a :=
  Quotient.lift_mk (shapiroFun K)
    (fun a a' hab => shapiroFun_wellDef K (Quotient.sound' hab)) a

lemma shapiroLifted_mem (K : Subgroup (Hp p)) (q : (Hp p) ⧸ K) :
    shapiroLifted K q ∈ Representation.coindV K.subtype (Representation.trivial ℤ ↥K ℤ) := by
  induction q using Quotient.inductionOn' with
  | h a => rw [shapiroLifted_mk]; exact shapiroFun_mem K a

/-- Shapiro 桥的基像：`Φ(q) ∈ Coind_K^(Hp p)(ℤ)`。 -/
noncomputable def shapiroBasis (K : Subgroup (Hp p)) (q : (Hp p) ⧸ K) : CoindCarrier K :=
  ⟨shapiroLifted K q, shapiroLifted_mem K q⟩

@[simp] lemma shapiroBasis_mk (K : Subgroup (Hp p)) (a : (Hp p)) :
    (shapiroBasis K (QuotientGroup.mk a)).1 = shapiroFun K a :=
  shapiroLifted_mk K a

/-- **`Φ` 的等变性**：`Φ(h · q) = h · Φ(q)`。 -/
lemma shapiroBasis_smul (K : Subgroup (Hp p)) (h : (Hp p)) (q : (Hp p) ⧸ K) :
    (coindK K).ρ h (shapiroBasis K q) = shapiroBasis K (h • q) := by
  classical
  apply Subtype.ext
  funext y
  show (shapiroBasis K q).1 (y * h) = (shapiroBasis K (h • q)).1 y
  induction q using Quotient.inductionOn' with
  | h a =>
    rw [show h • (QuotientGroup.mk a : (Hp p) ⧸ K) = QuotientGroup.mk (h * a) from rfl]
    rw [shapiroBasis_mk, shapiroBasis_mk]
    show (if (y * h) * a ∈ K then (1 : ℤ) else 0) = (if y * (h * a) ∈ K then (1 : ℤ) else 0)
    rw [show (y * h) * a = y * (h * a) from mul_assoc y h a]

/-- `Finsupp` 侧的 Shapiro 桥：`((Hp p) ⧸ K →₀ ℤ) →ₗ Coind_K^(Hp p)(ℤ)`，`single q 1 ↦ Φ(q)`。 -/
noncomputable def shapiroLift (K : Subgroup (Hp p)) :
    (((Hp p) ⧸ K) →₀ ℤ) →ₗ[ℤ] CoindCarrier K :=
  (Finsupp.lift (CoindCarrier K) ℤ ((Hp p) ⧸ K)) (shapiroBasis K)

lemma shapiroLift_single (K : Subgroup (Hp p)) (q : (Hp p) ⧸ K) :
    shapiroLift K (Finsupp.single q 1) = shapiroBasis K q := by
  rw [shapiroLift, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **等变性的 `Finsupp` 层形式**（线性映射层）：`lift Φ` 与 `(Hp p)`-作用交换。 -/
lemma shapiroLift_mapDomain (K : Subgroup (Hp p)) (h : (Hp p)) :
    (shapiroLift K).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = ((coindK K).ρ h).comp (shapiroLift K) := by
  refine (Finsupp.lift (CoindCarrier K) ℤ ((Hp p) ⧸ K)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show shapiroLift K (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single q 1))
      = (coindK K).ρ h (shapiroLift K (Finsupp.single q 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, shapiroLift_single, shapiroLift_single,
    shapiroBasis_smul]

/-- Shapiro 桥 `ℤ[(Hp p)/K] ⟶ Coind_K^(Hp p)(ℤ)`。 -/
noncomputable def shapiroHom (K : Subgroup (Hp p)) : permHK K ⟶ coindK K :=
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
      exact congrArg (fun (f : (((Hp p) ⧸ K) →₀ ℤ) →ₗ[ℤ] CoindCarrier K) => f _)
        (shapiroLift_mapDomain K h)))

/-! ### (c.2) 对偶侧与复合恒等式 -/

/-- 对偶侧的代表元版：`f ↦ (a ↦ f(a⁻¹))`。 -/
noncomputable def shapiroOfCoindRaw (K : Subgroup (Hp p)) (f : CoindCarrier K) : (Hp p) → ℤ :=
  fun a => f.1 (a⁻¹)

lemma shapiroOfCoindRaw_wellDef (K : Subgroup (Hp p)) (f : CoindCarrier K) {a a' : (Hp p)}
    (h : (QuotientGroup.mk a : (Hp p) ⧸ K) = QuotientGroup.mk a') :
    shapiroOfCoindRaw K f a = shapiroOfCoindRaw K f a' := by
  rw [QuotientGroup.eq] at h
  show f.1 (a⁻¹) = f.1 (a'⁻¹)
  rw [show a'⁻¹ = (a⁻¹ * a')⁻¹ * a⁻¹ from by group]
  exact (coind_inv K f ⟨(a⁻¹ * a')⁻¹, K.inv_mem h⟩ a⁻¹).symm

/-- 对偶侧的陪集版（`Quotient.lift`，用 `K`-左不变性）。 -/
noncomputable def shapiroOfCoindFun (K : Subgroup (Hp p)) (f : CoindCarrier K) : ((Hp p) ⧸ K) → ℤ :=
  Quotient.lift (shapiroOfCoindRaw K f)
    (fun a a' hab => shapiroOfCoindRaw_wellDef K f (Quotient.sound' hab))

@[simp] lemma shapiroOfCoindFun_mk (K : Subgroup (Hp p)) (f : CoindCarrier K) (a : (Hp p)) :
    shapiroOfCoindFun K f (QuotientGroup.mk a) = f.1 (a⁻¹) :=
  Quotient.lift_mk (shapiroOfCoindRaw K f)
    (fun a a' hab => shapiroOfCoindRaw_wellDef K f (Quotient.sound' hab)) a

/-- `Finsupp` 侧的逆映射：`f ↦ (q ↦ f(a⁻¹))`（`q = aK`）。 -/
noncomputable def shapiroOfCoindLift (K : Subgroup (Hp p)) :
    CoindCarrier K →ₗ[ℤ] (((Hp p) ⧸ K) →₀ ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ ((Hp p) ⧸ K)).symm.toLinearMap.comp
    ({ toFun := shapiroOfCoindFun K
       map_add' := fun f g => by
         funext q
         induction q using Quotient.inductionOn' with
         | h a => simp
       map_smul' := fun c f => by
         funext q
         induction q using Quotient.inductionOn' with
         | h a => simp } : CoindCarrier K →ₗ[ℤ] ((Hp p) ⧸ K → ℤ))

@[simp] lemma shapiroOfCoindLift_apply (K : Subgroup (Hp p)) (f : CoindCarrier K) (a : (Hp p)) :
    shapiroOfCoindLift K f (QuotientGroup.mk a) = f.1 (a⁻¹) := by
  rw [shapiroOfCoindLift, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact shapiroOfCoindFun_mk K f a

/-- **逆映射的等变性**（`Finsupp` 层，辅助形式：只在 `h · q'` 上验证）。 -/
lemma shapiroOfCoindLift_smul_aux (K : Subgroup (Hp p)) (h : (Hp p)) (f : CoindCarrier K)
    (q' : (Hp p) ⧸ K) :
    shapiroOfCoindLift K ((coindK K).ρ h f) (h • q')
      = Finsupp.mapDomain (h • ·) (shapiroOfCoindLift K f) (h • q') := by
  induction q' using Quotient.inductionOn' with
  | h b =>
    rw [Finsupp.mapDomain_apply (smulLeft_injective K h) (shapiroOfCoindLift K f) b]
    rw [show h • (QuotientGroup.mk b : (Hp p) ⧸ K) = QuotientGroup.mk (h * b) from rfl]
    rw [shapiroOfCoindLift_apply, shapiroOfCoindLift_apply, coind_apply]
    show f.1 ((h * b)⁻¹ * h) = f.1 (b⁻¹)
    rw [show (h * b)⁻¹ * h = b⁻¹ from by group]

/-- **逆映射的等变性**（`Finsupp` 层）。 -/
lemma shapiroOfCoindLift_smul (K : Subgroup (Hp p)) (h : (Hp p)) (f : CoindCarrier K) :
    shapiroOfCoindLift K ((coindK K).ρ h f)
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (shapiroOfCoindLift K f) := by
  ext q
  rw [Finsupp.lmapDomain_apply]
  rw [show q = h • (h⁻¹ • q) from (smul_inv_smul h q).symm]
  exact shapiroOfCoindLift_smul_aux K h f (h⁻¹ • q)

/-- Shapiro 桥的对偶侧 `Coind_K^(Hp p)(ℤ) ⟶ ℤ[(Hp p)/K]`。 -/
noncomputable def shapiroOfCoind (K : Subgroup (Hp p)) : coindK K ⟶ permHK K :=
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
theorem shapiroOfCoindLift_comp_shapiroLift (K : Subgroup (Hp p)) :
    (shapiroOfCoindLift K).comp (shapiroLift K)
      = LinearMap.id (R := ℤ) (M := ((Hp p) ⧸ K) →₀ ℤ) := by
  classical
  refine (Finsupp.lift (((Hp p) ⧸ K) →₀ ℤ) ℤ ((Hp p) ⧸ K)).symm.injective ?_
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
      have hiff : ((QuotientGroup.mk a : (Hp p) ⧸ K) = QuotientGroup.mk b) ↔ b⁻¹ * a ∈ K := by
        rw [QuotientGroup.eq]
        exact ⟨fun h => by simpa using K.inv_mem h, fun h => by simpa using K.inv_mem h⟩
      rw [show shapiroFun K a b⁻¹ = (if b⁻¹ * a ∈ K then (1 : ℤ) else 0) from rfl]
      by_cases hb : b⁻¹ * a ∈ K
      · rw [if_pos hb, if_pos (hiff.mpr hb)]
      · rw [if_neg hb, if_neg fun hc => hb (hiff.mp hc)]

/-- **Shapiro 桥的复合 = 恒等**（在 `ℤ[(Hp p)/K]` 侧）。 -/
theorem shapiroHom_comp (K : Subgroup (Hp p)) :
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
      congrArg (fun (f : (((Hp p) ⧸ K) →₀ ℤ) →ₗ[ℤ] (((Hp p) ⧸ K) →₀ ℤ)) =>
        f ((MonoidAlgebra.coeffLinearEquiv ℤ) w)) (shapiroOfCoindLift_comp_shapiroLift K)]
  exact LinearEquiv.symm_apply_apply _ _

/-! ### (c.3) 转移：`3` 消没 `coh²((Hp p), ℤ[(Hp p)/K])` -/

/-- **retract 引理**：若 `γ ≫ δ = 𝟙_A` 且 `3` 消没 `coh²(B)`，则 `3` 消没 `coh²(A)`。 -/
theorem kills_of_retract {A B : Rep ℤ (Hp p)} (γ : A ⟶ B) (δ : B ⟶ A) (h : γ ≫ δ = 𝟙 A)
    (hB : Coh2ExpDvdp p B) : Coh2ExpDvdp p A := by
  intro x
  have hid : (groupCohomology.map (MonoidHom.id (Hp p)) δ 2).hom
      ((groupCohomology.map (MonoidHom.id (Hp p)) γ 2).hom x) = x := by
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, h, groupCohomology.map_id]
    rfl
  have h3 : (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) γ 2).hom x = 0 := hB _
  calc (p : ℤ) • x
      = (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) δ 2).hom
          ((groupCohomology.map (MonoidHom.id (Hp p)) γ 2).hom x) := by rw [hid]
    _ = (groupCohomology.map (MonoidHom.id (Hp p)) δ 2).hom
          ((p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) γ 2).hom x) :=
        (map_zsmul (groupCohomology.map (MonoidHom.id (Hp p)) δ 2).hom p _).symm
    _ = 0 := by rw [h3, map_zero]

/-- **`3` 消没 `coh²((Hp p), ℤ[(Hp p)/K])`**（Shapiro ＋ 子群上指数整除 3）。

路线：`coh²((Hp p), ℤ[(Hp p)/K]) ←^{γ_*} coh²((Hp p), Coind_K^(Hp p) ℤ) ≅ coh²(K, ℤ)`，
而 `K ≤ (Hp p) = C₃×C₃` 的指数整除 3。 -/
theorem pKills_permHK (K : Subgroup (Hp p)) (hH : ∀ x : (Hp p), x ^ p = 1) :
    Coh2ExpDvdp p (permHK K) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  exact kills_of_retract (shapiroHom K) (shapiroOfCoind K) (shapiroHom_comp K)
    (smul_p_eq_zero_of_linearEquiv' (p := p)
      (groupCohomology.coindIso (S := K) (Rep.trivial ℤ ↥K ℤ) 2).toLinearEquiv
      (pKills_coh2 (p := p) ↥K fun x => by
        apply Subtype.ext
        simpa using hH (x : (Hp p))))

/-- **`Rep` 态射的有限和在点上的取值**：`(∑ f) u = ∑ f u`。

**工艺**：语句用 `Rep` 的**函数强制**（`(∑ f) u`），**不写** `.hom.toLinearMap`——
后者触发 `AddCommGroup.toIntModule` 与 `Rep.hV2` 的实例菱形（实测 `synthInstanceFailed`）；
而 `∑` 的项也不预先取 `.hom`，一律留在 `Rep.Hom` 层。 -/
lemma repHom_sum_apply {ι : Type} (s : Finset ι) {A B : Rep ℤ (Hp p)} (f : ι → (A ⟶ B)) (u : A) :
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
lemma cohMap_sum {ι : Type} (s : Finset ι) {A B : Rep ℤ (Hp p)} (f : ι → (A ⟶ B)) (n : ℕ) :
    groupCohomology.map (MonoidHom.id (Hp p)) (∑ i ∈ s, f i) n
      = ∑ i ∈ s, groupCohomology.map (MonoidHom.id (Hp p)) (f i) n := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact (groupCohomology.functor ℤ (Hp p) n).map_zero A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohMap_add, ih]

/-! ## 1. 轨道商与稳定子 -/

section Orbit

variable (X : Type) [Fintype X] [MulAction (Hp p) X]

/-- 轨道商 `X/(Hp p)`。 -/
abbrev OrbitQ : Type := MulAction.orbitRel.Quotient (Hp p) X

/-- `OrbitQ` 的 `Fintype`/`DecidableEq`（mathlib 未给；`noncomputable local instance`）。 -/
noncomputable local instance orbitQFintype : Fintype (OrbitQ (p := p) X) := Fintype.ofFinite _
noncomputable local instance orbitQDecEq : DecidableEq (OrbitQ (p := p) X) := Classical.decEq _

/-- `x` 所在的轨道。 -/
noncomputable abbrev orb (x : X) : OrbitQ (p := p) X := Quotient.mk'' x

/-- 轨道 `ω` 的代表元。 -/
noncomputable def orbRep (ω : OrbitQ (p := p) X) : X := Quotient.out ω

/-- 轨道 `ω` 的稳定子。 -/
noncomputable def orbStab (ω : OrbitQ (p := p) X) : Subgroup (Hp p) :=
  MulAction.stabilizer (Hp p) (orbRep (p := p) X ω)

/-- 轨道 ≃ 陪集空间。 -/
noncomputable def orbPsi (ω : OrbitQ (p := p) X) :
    MulAction.orbit (Hp p) (orbRep (p := p) X ω) ≃ (Hp p) ⧸ orbStab (p := p) X ω :=
  MulAction.orbitEquivQuotientStabilizer (Hp p) (orbRep (p := p) X ω)

lemma orbRep_eq (ω : OrbitQ (p := p) X) : orb (p := p) X (orbRep (p := p) X ω) = ω := Quotient.out_eq' ω

/-- **`ψ.symm` 的等变性**（= `ofQuotientStabilizer_smul`）。 -/
lemma orbPsi_symm_smul (ω : OrbitQ (p := p) X) (h : (Hp p)) (q : (Hp p) ⧸ orbStab (p := p) X ω) :
    ((orbPsi (p := p) X ω).symm (h • q) : X) = h • ((orbPsi (p := p) X ω).symm q : X) :=
  MulAction.ofQuotientStabilizer_smul (Hp p) (orbRep (p := p) X ω) h q

/-- **`ψ` 的等变性**（`⟨h · x, _⟩` 形式，避免 `h • ⟨x, _⟩` 的语法展开）。 -/
lemma orbPsi_smul_apply (ω : OrbitQ (p := p) X) (h : (Hp p)) (x : X)
    (hx : x ∈ MulAction.orbit (Hp p) (orbRep (p := p) X ω))
    (hx' : h • x ∈ MulAction.orbit (Hp p) (orbRep (p := p) X ω)) :
    orbPsi (p := p) X ω ⟨h • x, hx'⟩ = h • orbPsi (p := p) X ω ⟨x, hx⟩ := by
  apply (orbPsi (p := p) X ω).symm.injective
  refine Subtype.ext ?_
  show (((orbPsi (p := p) X ω).symm (orbPsi (p := p) X ω ⟨h • x, hx'⟩)) : X)
      = (((orbPsi (p := p) X ω).symm (h • orbPsi (p := p) X ω ⟨x, hx⟩)) : X)
  rw [Equiv.symm_apply_apply, orbPsi_symm_smul X ω h (orbPsi (p := p) X ω ⟨x, hx⟩), Equiv.symm_apply_apply]

/-! ## 2. `Finsupp` 层的两个映射 -/

/-- `α` 的基像：`x ↦ [x ∈ O_ω] · single (ψ x) 1`。 -/
noncomputable def orbAlphaBasis (ω : OrbitQ (p := p) X) (x : X) : ((Hp p) ⧸ orbStab (p := p) X ω) →₀ ℤ := by
  classical
  exact if hx : orb (p := p) X x = ω then
    Finsupp.single (orbPsi (p := p) X ω ⟨x, MulAction.orbitRel_apply.mp
      (Quotient.exact (hx.trans (orbRep_eq X ω).symm))⟩) 1
  else 0

/-- `β` 的基像：`single q 1 ↦ single (ψ.symm q) 1`。 -/
noncomputable def orbBetaBasis (ω : OrbitQ (p := p) X) (q : (Hp p) ⧸ orbStab (p := p) X ω) : X →₀ ℤ :=
  Finsupp.single ((orbPsi (p := p) X ω).symm q : X) 1

/-- `α`（`Finsupp` 层）。 -/
noncomputable def orbAlphaL (ω : OrbitQ (p := p) X) :
    (X →₀ ℤ) →ₗ[ℤ] (((Hp p) ⧸ orbStab (p := p) X ω) →₀ ℤ) :=
  (Finsupp.lift (((Hp p) ⧸ orbStab (p := p) X ω) →₀ ℤ) ℤ X) (orbAlphaBasis (p := p) X ω)

/-- `β`（`Finsupp` 层）。 -/
noncomputable def orbBetaL (ω : OrbitQ (p := p) X) :
    (((Hp p) ⧸ orbStab (p := p) X ω) →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ) :=
  (Finsupp.lift (X →₀ ℤ) ℤ ((Hp p) ⧸ orbStab (p := p) X ω)) (orbBetaBasis (p := p) X ω)

lemma orbAlphaL_single (ω : OrbitQ (p := p) X) (x : X) :
    orbAlphaL (p := p) X ω (Finsupp.single x 1) = orbAlphaBasis (p := p) X ω x := by
  rw [orbAlphaL, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

lemma orbBetaL_single (ω : OrbitQ (p := p) X) (q : (Hp p) ⧸ orbStab (p := p) X ω) :
    orbBetaL (p := p) X ω (Finsupp.single q 1) = orbBetaBasis (p := p) X ω q := by
  rw [orbBetaL, Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]

/-- **`α` 的等变性**（`Finsupp` 层）。 -/
lemma orbAlphaL_mapDomain (ω : OrbitQ (p := p) X) (h : (Hp p)) :
    (orbAlphaL (p := p) X ω).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = (Finsupp.lmapDomain ℤ ℤ (h • ·)).comp (orbAlphaL (p := p) X ω) := by
  classical
  refine (Finsupp.lift (((Hp p) ⧸ orbStab (p := p) X ω) →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show orbAlphaL (p := p) X ω (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single x 1))
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbAlphaL (p := p) X ω (Finsupp.single x 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbAlphaL_single, orbAlphaL_single]
  show orbAlphaBasis (p := p) X ω (h • x) = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbAlphaBasis (p := p) X ω x)
  have horb : orb (p := p) X (h • x) = orb (p := p) X x :=
    Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x h))
  rw [orbAlphaBasis, orbAlphaBasis]
  by_cases hx : orb (p := p) X x = ω
  · have hx' : orb (p := p) X (h • x) = ω := horb.trans hx
    rw [dif_pos hx', dif_pos hx, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      show orbPsi (p := p) X ω ⟨h • x, _⟩ = h • orbPsi (p := p) X ω ⟨x, _⟩ from orbPsi_smul_apply X ω h x _ _]
  · have hx' : ¬ (orb (p := p) X (h • x) = ω) := fun hc => hx (horb ▸ hc)
    rw [dif_neg hx', dif_neg hx, Finsupp.lmapDomain_apply]
    simp

/-- **`β` 的等变性**（`Finsupp` 层）。 -/
lemma orbBetaL_mapDomain (ω : OrbitQ (p := p) X) (h : (Hp p)) :
    (orbBetaL (p := p) X ω).comp (Finsupp.lmapDomain ℤ ℤ (h • ·))
      = (Finsupp.lmapDomain ℤ ℤ (h • ·)).comp (orbBetaL (p := p) X ω) := by
  refine (Finsupp.lift (X →₀ ℤ) ℤ ((Hp p) ⧸ orbStab (p := p) X ω)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show orbBetaL (p := p) X ω (Finsupp.lmapDomain ℤ ℤ (h • ·) (Finsupp.single q 1))
      = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbBetaL (p := p) X ω (Finsupp.single q 1))
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbBetaL_single, orbBetaL_single]
  show orbBetaBasis (p := p) X ω (h • q) = Finsupp.lmapDomain ℤ ℤ (h • ·) (orbBetaBasis (p := p) X ω q)
  rw [orbBetaBasis, orbBetaBasis, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    show ((orbPsi (p := p) X ω).symm (h • q) : X) = h • ((orbPsi (p := p) X ω).symm q : X) from
      orbPsi_symm_smul X ω h q]

/-! ## 3. `Rep` 层的两个态射 -/

/-- `α_ω : ℤ[X] ⟶ ℤ[(Hp p)/K_ω]` 的底层线性映射（共轭到 `MonoidAlgebra` 层）。 -/
noncomputable def orbAlphaLinear (ω : OrbitQ (p := p) X) :
    MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ ((Hp p) ⧸ orbStab (p := p) X ω) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((orbAlphaL (p := p) X ω).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

/-- `β_ω : ℤ[(Hp p)/K_ω] ⟶ ℤ[X]` 的底层线性映射。 -/
noncomputable def orbBetaLinear (ω : OrbitQ (p := p) X) :
    MonoidAlgebra ℤ ((Hp p) ⧸ orbStab (p := p) X ω) →ₗ[ℤ] MonoidAlgebra ℤ X :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((orbBetaL (p := p) X ω).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

/-- 共轭下「左作用 = `lmapDomain`」。 -/
lemma coeff_rho (Y : Type) [MulAction (Hp p) Y] (h : (Hp p)) (w : MonoidAlgebra ℤ Y) :
    (MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ (Hp p) Y).ρ h w)
      = Finsupp.lmapDomain ℤ ℤ (h • ·) ((MonoidAlgebra.coeffLinearEquiv ℤ) w) := by
  rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- 共轭下「右作用 = `lmapDomain`」（在参数上）。 -/
lemma coeff_rho_symm (Y : Type) [MulAction (Hp p) Y] (h : (Hp p)) (v : Y →₀ ℤ) :
    (Rep.ofMulAction ℤ (Hp p) Y).ρ h ((MonoidAlgebra.coeffLinearEquiv ℤ).symm v)
      = (MonoidAlgebra.coeffLinearEquiv ℤ).symm (Finsupp.lmapDomain ℤ ℤ (h • ·) v) := by
  rw [Representation.ofMulAction_def]
  simp

/-- `α_ω` 的等变性。 -/
lemma orbAlphaLinear_comm (ω : OrbitQ (p := p) X) (h : (Hp p)) :
    (orbAlphaLinear (p := p) X ω).comp ((Rep.ofMulAction ℤ (Hp p) X).ρ h)
      = ((permHK (orbStab (p := p) X ω)).ρ h).comp (orbAlphaLinear (p := p) X ω) := by
  refine LinearMap.ext (fun w => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbAlphaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ (Hp p) X).ρ h w)))
    = ((permHK (orbStab (p := p) X ω)).ρ h)
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbAlphaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) w)))
  rw [coeff_rho, coeff_rho_symm]
  congr 1
  exact LinearMap.congr_fun (orbAlphaL_mapDomain X ω h) ((MonoidAlgebra.coeffLinearEquiv ℤ) w)

/-- `β_ω` 的等变性。 -/
lemma orbBetaLinear_comm (ω : OrbitQ (p := p) X) (h : (Hp p)) :
    (orbBetaLinear (p := p) X ω).comp ((permHK (orbStab (p := p) X ω)).ρ h)
      = ((Rep.ofMulAction ℤ (Hp p) X).ρ h).comp (orbBetaLinear (p := p) X ω) := by
  refine LinearMap.ext (fun u => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbBetaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) ((permHK (orbStab (p := p) X ω)).ρ h u)))
    = ((Rep.ofMulAction ℤ (Hp p) X).ρ h)
      ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u)))
  rw [coeff_rho, coeff_rho_symm]
  congr 1
  exact LinearMap.congr_fun (orbBetaL_mapDomain X ω h) ((MonoidAlgebra.coeffLinearEquiv ℤ) u)

/-- `α_ω : ℤ[X] ⟶ ℤ[(Hp p)/K_ω]`。 -/
noncomputable def orbAlpha (ω : OrbitQ (p := p) X) :
    Rep.ofMulAction ℤ (Hp p) X ⟶ permHK (orbStab (p := p) X ω) :=
  Rep.ofHom (Representation.IntertwiningMap.mk (orbAlphaLinear (p := p) X ω) (orbAlphaLinear_comm X ω))

/-- `β_ω : ℤ[(Hp p)/K_ω] ⟶ ℤ[X]`。 -/
noncomputable def orbBeta (ω : OrbitQ (p := p) X) :
    permHK (orbStab (p := p) X ω) ⟶ Rep.ofMulAction ℤ (Hp p) X :=
  Rep.ofHom (Representation.IntertwiningMap.mk (orbBetaLinear (p := p) X ω) (orbBetaLinear_comm X ω))

/-! ## 4. 两个复合恒等式 -/

/-- **`α ∘ β = id`**（`Finsupp` 层）。 -/
lemma orbAlphaL_comp_orbBetaL (ω : OrbitQ (p := p) X) :
    (orbAlphaL (p := p) X ω).comp (orbBetaL (p := p) X ω) = LinearMap.id := by
  classical
  refine (Finsupp.lift (((Hp p) ⧸ orbStab (p := p) X ω) →₀ ℤ) ℤ ((Hp p) ⧸ orbStab (p := p) X ω)).symm.injective ?_
  funext q
  rw [Finsupp.lift_symm_apply]
  show orbAlphaL (p := p) X ω (orbBetaL (p := p) X ω (Finsupp.single q 1)) = Finsupp.single q 1
  rw [orbBetaL_single, orbBetaBasis, orbAlphaL_single]
  show orbAlphaBasis (p := p) X ω (((orbPsi (p := p) X ω).symm q : MulAction.orbit (Hp p) (orbRep (p := p) X ω)) : X)
      = Finsupp.single q 1
  have horb : orb (p := p) X (((orbPsi (p := p) X ω).symm q : MulAction.orbit (Hp p) (orbRep (p := p) X ω)) : X) = ω := by
    conv_rhs => rw [show ω = orb (p := p) X (orbRep (p := p) X ω) from (orbRep_eq X ω).symm]
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr ((orbPsi (p := p) X ω).symm q).2)
  rw [orbAlphaBasis, dif_pos horb]
  congr 1
  exact Equiv.apply_symm_apply (orbPsi (p := p) X ω) q

/-- **`Σ_ω (β_ω ∘ α_ω) = 𝟙`**（`Finsupp` 层）；在基向量 `single x 1` 上取值即
「落在 `O_{orb x}` 的那一项留下 `single x 1`，其余为零」。 -/
lemma sum_orbBetaL_comp_orbAlphaL :
    (∑ ω : OrbitQ (p := p) X, (orbBetaL (p := p) X ω).comp (orbAlphaL (p := p) X ω)) = LinearMap.id := by
  classical
  refine (Finsupp.lift (X →₀ ℤ) ℤ X).symm.injective ?_
  funext x
  rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
  show (∑ ω : OrbitQ (p := p) X, (orbBetaL (p := p) X ω).comp (orbAlphaL (p := p) X ω)) (Finsupp.single x 1)
      = Finsupp.single x 1
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (orb (p := p) X x)]
  · rw [LinearMap.comp_apply, orbAlphaL_single, orbAlphaBasis, dif_pos rfl, orbBetaL_single,
      orbBetaBasis]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply (orbPsi (p := p) X (orb (p := p) X x)) ⟨x, _⟩)
  · intro b _ hb
    rw [LinearMap.comp_apply, orbAlphaL_single, orbAlphaBasis, dif_neg (fun hc => hb hc.symm),
      map_zero]
  · intro h
    exact absurd (Finset.mem_univ (orb (p := p) X x)) h

/-- **`β_ω ≫ α_ω = 𝟙`**（在 `ℤ[(Hp p)/K_ω]` 上）。 -/
theorem orbBeta_comp_orbAlpha (ω : OrbitQ (p := p) X) :
    orbBeta (p := p) X ω ≫ orbAlpha (p := p) X ω = 𝟙 (permHK (orbStab (p := p) X ω)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun u => ?_)
  show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
      (orbAlphaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ)
        ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
          (orbBetaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))))) = u
  rw [LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply, orbAlphaL_comp_orbBetaL,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- **`Σ_ω (α_ω ≫ β_ω) = 𝟙`**（在 `ℤ[X]` 上）。 -/
theorem sum_orbAlpha_comp_orbBeta :
    (∑ ω : OrbitQ (p := p) X, orbAlpha (p := p) X ω ≫ orbBeta (p := p) X ω)
      = 𝟙 (Rep.ofMulAction ℤ (Hp p) X) := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext (fun u => ?_)
  show (∑ ω : OrbitQ (p := p) X, orbAlpha (p := p) X ω ≫ orbBeta (p := p) X ω) u
      = (𝟙 (Rep.ofMulAction ℤ (Hp p) X)) u
  rw [repHom_sum_apply]
  have hterm : ∀ ω : OrbitQ (p := p) X, (orbAlpha (p := p) X ω ≫ orbBeta (p := p) X ω) u
      = (MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaL (p := p) X ω (orbAlphaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))) := by
    intro ω
    show (MonoidAlgebra.coeffLinearEquiv ℤ).symm
        (orbBetaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ)
          ((MonoidAlgebra.coeffLinearEquiv ℤ).symm
            (orbAlphaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u))))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Rep.id_apply]
  rw [← map_sum]
  rw [show (∑ ω : OrbitQ (p := p) X, orbBetaL (p := p) X ω (orbAlphaL (p := p) X ω ((MonoidAlgebra.coeffLinearEquiv ℤ) u)))
        = ∑ ω : OrbitQ (p := p) X, (orbBetaL (p := p) X ω).comp (orbAlphaL (p := p) X ω)
            ((MonoidAlgebra.coeffLinearEquiv ℤ) u)
      from Finset.sum_congr rfl (fun ω _ => (LinearMap.comp_apply _ _ _).symm)]
  rw [show (∑ ω : OrbitQ (p := p) X, (orbBetaL (p := p) X ω).comp (orbAlphaL (p := p) X ω)
          ((MonoidAlgebra.coeffLinearEquiv ℤ) u))
        = (∑ ω : OrbitQ (p := p) X, (orbBetaL (p := p) X ω).comp (orbAlphaL (p := p) X ω))
          ((MonoidAlgebra.coeffLinearEquiv ℤ) u) from (LinearMap.sum_apply _ _ _).symm,
    sum_orbBetaL_comp_orbAlphaL, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-! ## 5. 组装：`perm_exp` 与 `stable_exp` -/

/-- **命名中间态射**（组装期一律走这些常量，避免大项反复展开导致归一爆炸）。 -/
noncomputable def orbE (ω : OrbitQ (p := p) X) : Rep.ofMulAction ℤ (Hp p) X ⟶ Rep.ofMulAction ℤ (Hp p) X :=
  orbAlpha (p := p) X ω ≫ orbBeta (p := p) X ω

/-- `α_ω` 在 `coh²` 上诱导的映射。 -/
noncomputable def orbAlphaCoh (ω : OrbitQ (p := p) X) :
    groupCohomology (Rep.ofMulAction ℤ (Hp p) X) 2 ⟶ groupCohomology (permHK (orbStab (p := p) X ω)) 2 :=
  groupCohomology.map (MonoidHom.id (Hp p)) (orbAlpha (p := p) X ω) 2

/-- `β_ω` 在 `coh²` 上诱导的映射。 -/
noncomputable def orbBetaCoh (ω : OrbitQ (p := p) X) :
    groupCohomology (permHK (orbStab (p := p) X ω)) 2 ⟶ groupCohomology (Rep.ofMulAction ℤ (Hp p) X) 2 :=
  groupCohomology.map (MonoidHom.id (Hp p)) (orbBeta (p := p) X ω) 2

/-- `E_ω` 在 `coh²` 上诱导的映射（**直接定义为复合**，省去与 `map (E_ω)` 的等式搬运）。 -/
noncomputable def orbCoh (ω : OrbitQ (p := p) X) :
    groupCohomology (Rep.ofMulAction ℤ (Hp p) X) 2 ⟶ groupCohomology (Rep.ofMulAction ℤ (Hp p) X) 2 :=
  orbAlphaCoh (p := p) X ω ≫ orbBetaCoh (p := p) X ω

lemma sum_orbE : (∑ ω : OrbitQ (p := p) X, orbE (p := p) X ω) = 𝟙 (Rep.ofMulAction ℤ (Hp p) X) :=
  sum_orbAlpha_comp_orbBeta X

lemma cohMap_sum_orbE :
    groupCohomology.map (MonoidHom.id (Hp p)) (∑ ω : OrbitQ (p := p) X, orbE (p := p) X ω) 2
      = ∑ ω : OrbitQ (p := p) X, orbCoh (p := p) X ω := by
  rw [cohMap_sum Finset.univ (fun ω : OrbitQ (p := p) X => orbE (p := p) X ω) 2]
  exact Finset.sum_congr rfl (fun ω _ =>
    groupCohomology.map_id_comp (orbAlpha (p := p) X ω) (orbBeta (p := p) X ω) 2)

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

/-- **`3` 消没 `coh²((Hp p), ℤ[X])`**（有限 `(Hp p)`-集 `X`）。

组装（**不用**双积）：轨道幂等分解 `Σ_ω E_ω = 𝟙` 给出 `x = Σ_ω (E_ω)_* x`；
每项经 `coh²((Hp p), ℤ[(Hp p)/K_ω])` 分解，后者被 `3` 零化（S3 的 `pKills_permHK`）
⟹ 逐项零 ⟹ `3x = 0`。 -/
theorem pKills_ofMulAction : Coh2ExpDvdp p (Rep.ofMulAction ℤ (Hp p) X) := by
  classical
  have hH : ∀ x : (Hp p), x ^ p = 1 := Hp_pow_p
  intro x
  have hsplit : x = ∑ ω : OrbitQ (p := p) X, (orbCoh (p := p) X ω).hom x := by
    calc x = (groupCohomology.map (MonoidHom.id (Hp p)) (𝟙 (Rep.ofMulAction ℤ (Hp p) X)) 2).hom x := by
          rw [groupCohomology.map_id]; rfl
      _ = (groupCohomology.map (MonoidHom.id (Hp p)) (∑ ω : OrbitQ (p := p) X, orbE (p := p) X ω) 2).hom x := by
          rw [show (𝟙 (Rep.ofMulAction ℤ (Hp p) X)) = ∑ ω : OrbitQ (p := p) X, orbE (p := p) X ω
                from (sum_orbE X).symm]
      _ = (∑ ω : OrbitQ (p := p) X, orbCoh (p := p) X ω).hom x := by rw [cohMap_sum_orbE]
      _ = ∑ ω : OrbitQ (p := p) X, (orbCoh (p := p) X ω).hom x := moduleCat_sum_hom_apply Finset.univ _ x
  have hterm : ∀ ω : OrbitQ (p := p) X, (p : ℤ) • (orbCoh (p := p) X ω).hom x = 0 := by
    intro ω
    have h3 : (p : ℤ) • (orbAlphaCoh (p := p) X ω).hom x = 0 := pKills_permHK (orbStab (p := p) X ω) hH _
    rw [show (orbCoh (p := p) X ω).hom x
          = (orbBetaCoh (p := p) X ω).hom ((orbAlphaCoh (p := p) X ω).hom x) from by
      rw [orbCoh, ModuleCat.comp_apply]]
    rw [← map_zsmul, h3, map_zero]
  calc (p : ℤ) • x
      = (p : ℤ) • ∑ ω : OrbitQ (p := p) X, (orbCoh (p := p) X ω).hom x := by conv_lhs => rw [hsplit]
    _ = ∑ ω : OrbitQ (p := p) X, (p : ℤ) • (orbCoh (p := p) X ω).hom x :=
        zsmul_finset_sum (p : ℤ) Finset.univ _
    _ = 0 := Finset.sum_eq_zero fun ω _ => hterm ω

end Orbit

/-! ## 6. `perm_exp` 与 `stable_exp` -/

/-- **论文 `prop:perm-exponent`**：置换格 `L` 上 `3` 消没 `coh²`。 -/
theorem perm_exp (L : Rep ℤ (Hp p)) (hL : IsPermutationLattice L) : Coh2ExpDvdp p L := by
  obtain ⟨X, hF, hA, ⟨e⟩⟩ := hL
  letI : Fintype X := hF
  letI : MulAction (Hp p) X := hA
  exact kills_of_iso (p := p) e.symm (pKills_ofMulAction X)

/-- **论文 `prop:stable-exp`**：稳定置换格 `L` 上 `3` 消没 `coh²`。

由 S1 的转移引理 `kills_of_biprod_iso` 从 `Q = L ⊞ P` 拉回。 -/
theorem stable_exp (L : Rep ℤ (Hp p)) (hL : IsStablyPermutation L) : Coh2ExpDvdp p L := by
  obtain ⟨P, Q, hP, hQ, ⟨e⟩⟩ := hL
  exact kills_of_biprod_iso (p := p) L P Q e (perm_exp Q hQ)

/-! ## 3. 公理闸门 -/

#print axioms pKills_permHK
#print axioms Hp_pow_p
#print axioms pKills_ofMulAction
#print axioms perm_exp
#print axioms stable_exp

end ABGV52.P
