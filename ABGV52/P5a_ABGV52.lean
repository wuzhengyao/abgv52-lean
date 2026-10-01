/-
  ABGV-5.2 —— **P 档 P5a：转移 ＋ `0 → ℤ → ℚ → ℚ/ℤ → 0` 的机器**（C 档 `S1` ＋ `S2` 的 p 版）

  内容
  ====
    §1–4（＝ S1 的 p 版，`Hp p` 上）：
      函子性的 `ℤ`-加性；双积的「p 消没」继承；同构传递；**转移引理**
      （`L ⊞ P ≅ Q` ＋ `p` 消没 `coh²(Q)` ⟹ `p` 消没 `coh²(L)`）。
    §5–9（＝ S2 的 p 版；**S2 本就对任意有限群 `K` 通用**，此处只把末尾的
      「`3` 消没 `coh²(K,ℤ)`」换成「`p` 消没」）：
      `ℚ` 系数转移（`sum ∘ const = cardHom` ⟹ `H^{n+1}(K,ℚ) = 0`）；
      `0 → ℤ → ℚ → ℚ/ℤ → 0` 短正合 ＋ 连接同构 `H¹(K,ℚ/ℤ) ≅ H²(K,ℤ)`；
      **`pKills_coh2`**：`∀ x : K, x ^ p = 1` ⟹ `(p : ℤ)` 消没 `coh²(K, ℤtriv)`。

  p-通用性：S1 全段只用到群公理与函子性；S2 的 `ℚ` 段与 `ℚ/ℤ` 段逐字同构，
  唯一带 `3` 的是 §8 的三条引理（换成 `p` 后证明逐字不变：`zpow_natCast` ＋ 群假设）。
-/
import ABGV52.P1_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

open CategoryTheory CategoryTheory.Limits

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

/-- **论文 `prop:stable-exp` 的结论形态（p 版）**：`(p : ℤ)` 消没 `coh²(Hp p, M)`。 -/
noncomputable def Coh2ExpDvdp (A : Rep ℤ (Hp p)) : Prop :=
  ∀ x : ↥(groupCohomology A 2), (p : ℤ) • x = 0

/-! ## 1. 函子性的 `ℤ`-加性 -/

lemma cochainsMap_add {A B : Rep ℤ (Hp p)} (φ ψ : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id (Hp p)) (φ + ψ)
      = groupCohomology.cochainsMap (MonoidHom.id (Hp p)) φ
        + groupCohomology.cochainsMap (MonoidHom.id (Hp p)) ψ :=
  (groupCohomology.cochainsFunctor ℤ (Hp p)).map_add

lemma cohMap_add {A B : Rep ℤ (Hp p)} (φ ψ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id (Hp p)) (φ + ψ) n
      = groupCohomology.map (MonoidHom.id (Hp p)) φ n
        + groupCohomology.map (MonoidHom.id (Hp p)) ψ n := by
  show HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id (Hp p)) (φ + ψ)) n
      = HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id (Hp p)) φ) n
        + HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id (Hp p)) ψ) n
  rw [cochainsMap_add, HomologicalComplex.homologyMap_add]

/-! ## 2. 双积的「p 消没」继承 -/

theorem kills_biprod {A B : Rep ℤ (Hp p)} (hA : Coh2ExpDvdp p A) (hB : Coh2ExpDvdp p B) :
    Coh2ExpDvdp p (A ⊞ B) := by
  intro x
  have htotal : (biprod.fst : A ⊞ B ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ B)
      + (biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inr : B ⟶ A ⊞ B) = 𝟙 (A ⊞ B) :=
    biprod.total
  have hx : x = (groupCohomology.map (MonoidHom.id (Hp p)) (biprod.inl : A ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id (Hp p)) (biprod.fst : A ⊞ B ⟶ A) 2).hom x)
      + (groupCohomology.map (MonoidHom.id (Hp p)) (biprod.inr : B ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id (Hp p)) (biprod.snd : A ⊞ B ⟶ B) 2).hom x) := by
    have h := congrArg (fun f => (groupCohomology.map (MonoidHom.id (Hp p)) f 2).hom x) htotal
    simp only [cohMap_add p, groupCohomology.map_id_comp, groupCohomology.map_id,
      ModuleCat.id_apply] at h
    exact h.symm
  have h1 : (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) (biprod.inl : A ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id (Hp p)) (biprod.fst : A ⊞ B ⟶ A) 2).hom x) = 0 := by
    rw [← map_zsmul, hA]
    exact map_zero _
  have h2 : (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) (biprod.inr : B ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id (Hp p)) (biprod.snd : A ⊞ B ⟶ B) 2).hom x) = 0 := by
    rw [← map_zsmul, hB]
    exact map_zero _
  rw [hx, zsmul_add, h1, h2, add_zero]

/-! ## 3. 同构传递 -/

noncomputable def cohLinearEquivOfIso {A B : Rep ℤ (Hp p)} (e : A ≅ B) (n : ℕ) :
    ↥(groupCohomology A n) ≃ₗ[ℤ] ↥(groupCohomology B n) where
  toFun := (groupCohomology.map (MonoidHom.id (Hp p)) e.hom n).hom
  invFun := (groupCohomology.map (MonoidHom.id (Hp p)) e.inv n).hom
  left_inv x := by
    show (groupCohomology.map (MonoidHom.id (Hp p)) e.inv n).hom
      ((groupCohomology.map (MonoidHom.id (Hp p)) e.hom n).hom x) = x
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, e.hom_inv_id,
      groupCohomology.map_id]
    rfl
  right_inv x := by
    show (groupCohomology.map (MonoidHom.id (Hp p)) e.hom n).hom
      ((groupCohomology.map (MonoidHom.id (Hp p)) e.inv n).hom x) = x
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, e.inv_hom_id,
      groupCohomology.map_id]
    rfl
  map_add' := fun x y => (groupCohomology.map (MonoidHom.id (Hp p)) e.hom n).hom.map_add x y
  map_smul' := fun c x => (groupCohomology.map (MonoidHom.id (Hp p)) e.hom n).hom.map_smul c x

theorem kills_of_iso {A B : Rep ℤ (Hp p)} (e : A ≅ B) (hA : Coh2ExpDvdp p A) :
    Coh2ExpDvdp p B := by
  intro x
  obtain ⟨y, rfl⟩ := (cohLinearEquivOfIso p e 2).surjective x
  exact (map_zsmul (cohLinearEquivOfIso p e 2).toLinearMap (p : ℤ) y).symm.trans
    ((congrArg (cohLinearEquivOfIso p e 2) (hA y)).trans (map_zero _))

/-! ## 4. 转移引理 -/

/-- **转移引理**（论文 `prop:stable-exp` 的证明骨架，p 版）。 -/
theorem kills_of_biprod_iso (L P Q : Rep ℤ (Hp p)) (e : L ⊞ P ≅ Q)
    (hQ : Coh2ExpDvdp p Q) : Coh2ExpDvdp p L := by
  intro x
  set φ : L ⟶ Q := (biprod.inl : L ⟶ L ⊞ P) ≫ e.hom with hφ
  set ψ : Q ⟶ L := e.inv ≫ (biprod.fst : L ⊞ P ⟶ L) with hψ
  have hcomp : φ ≫ ψ = 𝟙 L := by
    rw [hφ, hψ, Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp,
      biprod.inl_fst]
  have hid : (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom
      ((groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x) = x := by
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, hcomp,
      groupCohomology.map_id]
    rfl
  have hp : (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x = 0 := hQ _
  calc (p : ℤ) • x
      = (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom
          ((groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x) := by rw [hid]
    _ = (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom
          ((p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x) :=
        (map_zsmul (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom (p : ℤ) _).symm
    _ = (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom 0 := by rw [hp]
    _ = 0 := map_zero _

/-! ## 5. 标量版函子性（`ℕ`-标量） -/

lemma cohMap_nsmul {A B : Rep ℤ (Hp p)} (φ : A ⟶ B) (n m : ℕ) :
    groupCohomology.map (MonoidHom.id (Hp p)) (n • φ) m
      = n • groupCohomology.map (MonoidHom.id (Hp p)) φ m := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
            exact (groupCohomology.functor ℤ (Hp p) m).map_zero A B
  | succ k ih => rw [succ_nsmul, succ_nsmul, cohMap_add, ih]

/-! ## 6. 一般有限群上的转移：`ℚ` 系数（S2 §2–6 的 p 版，逐字同构） -/

section TrivQ

variable (K : Type) [Group K] [Fintype K]

/-- `K` 上的上同调载体。 -/
abbrev cohOf (M : Rep ℤ K) (q : ℕ) : Type := (groupCohomology M q : Type)

/-- `ℤ` 上的平凡 `K`-表示（载体 `ℚ`）。 -/
noncomputable abbrev QT : Rep ℤ K := Rep.trivial ℤ K ℚ

/-- `Coind_⊥^K(ℚ)`（载体 = 全体函数 `K → ℚ`）。 -/
noncomputable abbrev QC : Rep ℤ K :=
  Rep.coind (⊥ : Subgroup K).subtype (Rep.trivial ℤ ↥(⊥ : Subgroup K) ℚ)

noncomputable def constHom : QT K ⟶ QC K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => ⟨fun _ => q, by
        intro g h
        show q = q
        rfl⟩
      map_add' := fun a b => by ext k; rfl
      map_smul' := fun a b => by ext k; rfl }
    (by intro h; ext k; rfl))

noncomputable def sumHom : QC K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun f => ∑ k : K, (f : K → ℚ) k
      map_add' := fun a b => by
        simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun a b => by
        simp only [Submodule.coe_smul, Pi.smul_apply, Finset.smul_sum]
        rfl }
    (by
      intro h
      ext f
      show (∑ k : K, (f : K → ℚ) (k * h)) = ∑ k : K, (f : K → ℚ) k
      exact Equiv.sum_comp (Equiv.mulRight h) (fun k => (f : K → ℚ) k)))

noncomputable def cardHom : QT K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => (Fintype.card K : ℚ) * q
      map_add' := fun a b => by ring
      map_smul' := fun a b => by simp only [RingHom.id_apply]; ring }
    (by intro h; ext q; rfl))

noncomputable def invCardHom : QT K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => ((Fintype.card K : ℚ))⁻¹ * q
      map_add' := fun a b => by ring
      map_smul' := fun a b => by simp only [RingHom.id_apply]; ring }
    (by intro h; ext q; rfl))

lemma constHom_comp_sumHom : constHom K ≫ sumHom K = cardHom K := by
  apply Rep.hom_ext
  ext q
  show (∑ _ : K, q) = (Fintype.card K : ℚ) * q
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma cardHom_comp_invCardHom : cardHom K ≫ invCardHom K = 𝟙 (QT K) := by
  have hcard : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply Rep.hom_ext
  ext q
  simp only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.toLinearMap_id,
    LinearMap.id_apply, cardHom, invCardHom]
  show ((Fintype.card K : ℚ))⁻¹ * ((Fintype.card K : ℚ) * q) = q
  field_simp

theorem isZero_QC (n : ℕ) : IsZero (groupCohomology (QC K) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial ℤ ↥(⊥ : Subgroup K) ℚ) n).of_iso
    (groupCohomology.coindIso (S := (⊥ : Subgroup K))
      (Rep.trivial ℤ ↥(⊥ : Subgroup K) ℚ) (n + 1))

lemma map_cardHom_eq_zero (n : ℕ) :
    groupCohomology.map (A := QT K) (B := QT K) (MonoidHom.id K) (cardHom K) (n + 1) = 0 := by
  rw [← constHom_comp_sumHom K, groupCohomology.map_id_comp]
  have hsum : groupCohomology.map (A := QC K) (B := QT K) (MonoidHom.id K) (sumHom K) (n + 1)
      = 0 :=
    (isZero_QC K n).eq_of_src _ 0
  rw [hsum, comp_zero]

theorem isZero_QT (n : ℕ) : IsZero (groupCohomology (QT K) (n + 1)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show x = 0
  calc x = (groupCohomology.map (MonoidHom.id K) (𝟙 (QT K)) (n + 1)).hom x := by
        rw [groupCohomology.map_id]; rfl
    _ = (groupCohomology.map (MonoidHom.id K) (cardHom K ≫ invCardHom K) (n + 1)).hom x := by
        rw [cardHom_comp_invCardHom]
    _ = (groupCohomology.map (MonoidHom.id K) (invCardHom K) (n + 1)).hom
          ((groupCohomology.map (MonoidHom.id K) (cardHom K) (n + 1)).hom x) := by
        rw [groupCohomology.map_id_comp, ModuleCat.comp_apply]
    _ = 0 := by
        rw [map_cardHom_eq_zero K n]
        simp

/-! ## 7. `0 → ℤ → ℚ → ℚ/ℤ → 0`（`Rep ℤ K` 中）及其长正合列 -/

attribute [local instance 1500] Rep.hV2

noncomputable abbrev TZ : Rep ℤ K := Rep.trivial ℤ K ℤ

/-- `ℚ/ℤ`（= `ℚ ⧸ ℤ·1`）。 -/
abbrev QZ : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

noncomputable abbrev TQD : Rep ℤ K := Rep.trivial ℤ K (QZ)

noncomputable def zToQHom : TZ K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    (Int.castAddHom ℚ).toIntLinearMap
    (by intro h; ext n; rfl))

noncomputable def qToQuotHom : QT K ⟶ TQD K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => QuotientAddGroup.mk q
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
    (by intro h; ext q; rfl))

@[simp] lemma zToQHom_apply (n : ℤ) : (zToQHom K).hom n = ((n : ℤ) : ℚ) := rfl
@[simp] lemma qToQuotHom_apply (q : ℚ) : (qToQuotHom K).hom q = QuotientAddGroup.mk q := rfl

lemma mk_eq_zero_iff (q : ℚ) :
    (QuotientAddGroup.mk q : QZ) = 0 ↔ q ∈ AddSubgroup.zmultiples (1 : ℚ) := by
  have h : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q : QZ)
      = QuotientAddGroup.mk q := rfl
  rw [← h, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']

lemma mem_zmultiples_one_iff (q : ℚ) :
    q ∈ AddSubgroup.zmultiples (1 : ℚ) ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩

lemma mk_intCast_eq_zero (n : ℤ) :
    (QuotientAddGroup.mk ((n : ℤ) : ℚ) : QZ) = QuotientAddGroup.mk (0 : ℚ) :=
  (mk_eq_zero_iff _).mpr ((mem_zmultiples_one_iff _).mpr ⟨n, rfl⟩)

noncomputable def qzComplex : ShortComplex (Rep ℤ K) :=
  ShortComplex.mk (zToQHom K) (qToQuotHom K) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    exact mk_intCast_eq_zero n)

instance : CategoryTheory.Mono (zToQHom K) := by
  rw [Rep.mono_iff_injective]
  intro a b h
  exact Int.cast_injective h

instance : CategoryTheory.Epi (qToQuotHom K) := by
  rw [Rep.epi_iff_surjective]
  intro y
  have h : Set.range (QuotientAddGroup.mk : ℚ → QZ) = Set.univ := QuotientAddGroup.range_mk
  obtain ⟨q, hq⟩ := (Set.range_eq_univ.mp h) y
  exact ⟨q, by rw [qToQuotHom_apply]; exact hq⟩

lemma qzComplexMod_exact :
    ((qzComplex K).map (forget₂ (Rep ℤ K) (ModuleCat ℤ))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact (mem_zmultiples_one_iff x).mp ((mk_eq_zero_iff x).mp hx)

theorem qzComplex_exact : (qzComplex K).Exact :=
  ((qzComplex K).exact_map_iff_of_faithful (forget₂ (Rep ℤ K) (ModuleCat ℤ))).mp
    (qzComplexMod_exact K)

theorem qzComplex_shortExact : (qzComplex K).ShortExact :=
  ShortComplex.ShortExact.mk' (qzComplex_exact K)
    (inferInstanceAs (CategoryTheory.Mono (zToQHom K)))
    (inferInstanceAs (CategoryTheory.Epi (qToQuotHom K)))

/-- **连接同态是同构**：`H¹(K,ℚ/ℤ) ≅ H²(K,ℤ)`。 -/
noncomputable def coh1QZ_iso_coh2Z :
    groupCohomology (TQD K) 1 ≅ groupCohomology (TZ K) 2 :=
  @asIso _ _ _ _ (groupCohomology.δ (qzComplex_shortExact K) 1 2 rfl)
    (groupCohomology.isIso_δ_of_isZero (qzComplex_shortExact K) 1
      (isZero_QT K 0) (isZero_QT K 1))

/-! ## 8. `p` 消没（C 档此处为 `3`；三条引理的证明逐字不变） -/

lemma p_smul_additive_eq_zero (hK : ∀ x : K, x ^ p = 1) (x : Additive K) :
    (p : ℤ) • x = (0 : Additive K) := by
  rw [← toMul_eq_one, toMul_zsmul]
  rw [show (p : ℤ) = ((p : ℕ) : ℤ) from rfl, zpow_natCast]
  exact hK x.toMul

lemma p_smul_hom_eq_zero (hK : ∀ x : K, x ^ p = 1)
    (φ : Additive K →+ TQD K) : (p : ℤ) • φ = 0 := by
  refine AddMonoidHom.ext (fun (x : Additive K) => ?_)
  rw [AddMonoidHom.smul_apply]
  rw [show (p : ℤ) • φ x = φ ((p : ℤ) • x) from (map_zsmul φ (p : ℤ) x).symm]
  rw [p_smul_additive_eq_zero p K hK x, map_zero]
  rfl

lemma smul_p_eq_zero_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : ∀ v : V, (p : ℤ) • v = 0) :
    ∀ w : W, (p : ℤ) • w = 0 := by
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  exact (map_zsmul e.toLinearMap (p : ℤ) v).symm.trans ((congrArg e (h v)).trans (map_zero _))

lemma smul_p_eq_zero_of_linearEquiv' {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : ∀ w : W, (p : ℤ) • w = 0) :
    ∀ v : V, (p : ℤ) • v = 0 := by
  intro v
  obtain ⟨w, rfl⟩ := e.symm.surjective v
  exact (map_zsmul e.symm.toLinearMap (p : ℤ) w).symm.trans
    ((congrArg e.symm (h w)).trans (map_zero _))

/-- **有限群 `K`（指数整除 `p`）上 `p` 消没 `coh²(K, ℤtriv)`**（论文 `prop:perm-exponent` 的核）。 -/
theorem pKills_coh2 (hK : ∀ x : K, x ^ p = 1) :
    ∀ x : cohOf K (TZ K) 2, (p : ℤ) • x = 0 :=
  smul_p_eq_zero_of_linearEquiv p (coh1QZ_iso_coh2Z K).toLinearEquiv
    (smul_p_eq_zero_of_linearEquiv' p
      (groupCohomology.H1IsoOfIsTrivial (TQD K)).toLinearEquiv
      (p_smul_hom_eq_zero p K hK))

end TrivQ

/-! ## 9. 公理闸门 -/

#print axioms kills_biprod
#print axioms kills_of_iso
#print axioms kills_of_biprod_iso
#print axioms isZero_QT
#print axioms qzComplex_shortExact
#print axioms coh1QZ_iso_coh2Z
#print axioms pKills_coh2

end ABGV52.P
