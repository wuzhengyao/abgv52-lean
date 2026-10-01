/-
  ABGV-5.2 —— S2（一）：`prop:perm-exponent` 的系数计算

  论文路线（`raw/ABGV-5.2-resolution.tex:973`）：置换格 `P ≅ ⊕_i ℤ[H/K_i]`，
  Shapiro 给 `coh²(H, ℤ[H/K]) ≅ coh²(K, ℤ)`，而各子群上 `exp(coh²(K,ℤ)) ∣ 3`。

  本件证**统一版本**：设 `K` 为**指数整除 3** 的有限群，则 `3` 消没 `coh²(K, ℤtriv)`。

  路线 = 论文 `lem:H2-Z` 的 ℚ/ℤ 路线，但对**任意**这样的 `K` 通用：
    * `0 → ℤ → ℚ → ℚ/ℤ → 0` 的长正合列 ＋ `H^m(K,ℚ) = 0`（m ≥ 1）⟹ `coh²(K,ℤ) ≅ coh¹(K,ℚ/ℤ)`；
    * `coh¹(K,ℚ/ℤ) ≅ Hom(K,ℚ/ℤ)`（`H1IsoOfIsTrivial`）；
    * `K` 指数整除 3 ⟹ `Hom(K,ℚ/ℤ)` 被 `3` 零化。

  `H^m(K,ℚ) = 0` 两步：
    ① **转移**：`ℚtriv →^{const} Coind_⊥^K(ℚ) →^{sum} ℚtriv` 复合 = `cardHom`（乘 `|K|`），
       中间项经 Shapiro（`coindIso`）与平凡群消没**为零** ⟹ `cardHom` 作用于 `H^m` 为零；
    ② `ℚ` 上 `cardHom` 可逆（逆 = `invCardHom`）⟹ `H^m = 0`。
-/
import ABGV52.S1_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## 1. 标量版函子性：`n • φ` 的诱导映射是 `n •` -/

/-- **`ℕ`-标量版**：`map (n • φ) = n • map φ`（对 `n` 归纳，用 `cohMap_add`）。 -/
lemma cohMap_nsmul {A B : Rep ℤ H} (φ : A ⟶ B) (n m : ℕ) :
    groupCohomology.map (MonoidHom.id H) (n • φ) m
      = n • groupCohomology.map (MonoidHom.id H) φ m := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
            exact (groupCohomology.functor ℤ H m).map_zero A B
  | succ k ih => rw [succ_nsmul, succ_nsmul, cohMap_add, ih]

/-! ## 2. 一般有限群上的转移：`ℚ` 系数 -/

section TrivQ

variable (K : Type) [Group K] [Fintype K]

/-- `K` 上的上同调载体（`Hyp_ABGV52` 的 `coh` 固定于 `H`，此处泛化）。 -/
abbrev cohOf (K : Type) [Group K] (M : Rep ℤ K) (q : ℕ) : Type := (groupCohomology M q : Type)

/-- `ℤ` 上的平凡 `K`-表示（载体 `ℚ`）。 -/
noncomputable abbrev QT : Rep ℤ K := Rep.trivial ℤ K ℚ

/-- `Coind_⊥^K(ℚ)`（载体 = 全体函数 `K → ℚ`，因 `⊥` 的条件空）。 -/
noncomputable abbrev QC : Rep ℤ K :=
  Rep.coind (⊥ : Subgroup K).subtype (Rep.trivial ℤ ↥(⊥ : Subgroup K) ℚ)

/-- 常值映射 `ℚ → Coind_⊥^K(ℚ)`（常函数不变，故等变）。 -/
noncomputable def constHom : QT K ⟶ QC K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => ⟨fun _ => q, by
        intro g h
        show q = q
        rfl⟩
      map_add' := fun a b => by ext k; rfl
      map_smul' := fun a b => by ext k; rfl }
    (by intro h; ext k; rfl))

/-- 求和映射 `Coind_⊥^K(ℚ) → ℚ`（`f ↦ Σ_k f k`；等变性 = 重指标）。 -/
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

/-- 乘 `|K|`（`ℚ` 上的 `ℤ`-线性等变映射）。 -/
noncomputable def cardHom : QT K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => (Fintype.card K : ℚ) * q
      map_add' := fun a b => by ring
      map_smul' := fun a b => by simp only [RingHom.id_apply]; ring }
    (by intro h; ext q; rfl))

/-- 乘 `|K|⁻¹`（同上）。 -/
noncomputable def invCardHom : QT K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => ((Fintype.card K : ℚ))⁻¹ * q
      map_add' := fun a b => by ring
      map_smul' := fun a b => by simp only [RingHom.id_apply]; ring }
    (by intro h; ext q; rfl))

/-! ## 3. 复合恒等式 `sum ∘ const = cardHom`，`invCardHom ∘ cardHom = 𝟙` -/

/-- **转移复合**：`sumHom ∘ constHom = cardHom`（逐点 `Σ_k q = |K| * q`）。 -/
lemma constHom_comp_sumHom : constHom K ≫ sumHom K = cardHom K := by
  apply Rep.hom_ext
  ext q
  show (∑ _ : K, q) = (Fintype.card K : ℚ) * q
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `cardHom` 的右逆：`cardHom ≫ invCardHom = 𝟙`。 -/
lemma cardHom_comp_invCardHom : cardHom K ≫ invCardHom K = 𝟙 (QT K) := by
  have hcard : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply Rep.hom_ext
  ext q
  simp only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.toLinearMap_id, LinearMap.id_apply,
    cardHom, invCardHom]
  show ((Fintype.card K : ℚ))⁻¹ * ((Fintype.card K : ℚ) * q) = q
  field_simp

/-! ## 4. `H^m(K, Coind_⊥^K ℚ) = 0`（Shapiro ＋ 平凡群） -/

/-- 中间项消没：`H^{n+1}(K, Coind_⊥^K ℚ) = 0`。 -/
theorem isZero_QC (n : ℕ) : IsZero (groupCohomology (QC K) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial ℤ ↥(⊥ : Subgroup K) ℚ) n).of_iso
    (groupCohomology.coindIso (S := (⊥ : Subgroup K))
      (Rep.trivial ℤ ↥(⊥ : Subgroup K) ℚ) (n + 1))

/-! ## 5. `cardHom` 在 `H^{n+1}(K, ℚtriv)` 上为零（转移） -/

/-- `map cardHom = map (sum ∘ const) = map sum ≫ map const = 0`（后者经过零对象）。 -/
lemma map_cardHom_eq_zero (n : ℕ) :
    groupCohomology.map (A := QT K) (B := QT K) (MonoidHom.id K) (cardHom K) (n + 1) = 0 := by
  rw [← constHom_comp_sumHom K, groupCohomology.map_id_comp]
  have hsum : groupCohomology.map (A := QC K) (B := QT K) (MonoidHom.id K) (sumHom K) (n + 1)
      = 0 :=
    (isZero_QC K n).eq_of_src _ 0
  rw [hsum, comp_zero]

/-! ## 6. `H^{n+1}(K, ℚtriv) = 0`（除以 `|K|`） -/

/-- **`H^{n+1}(K, ℚtriv) = 0`**：`x = (invCard ∘ card)(x) = invCard(0) = 0`。 -/
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

/-- `ℤ` 上的平凡 `K`-表示（载体 `ℤ`）。 -/
noncomputable abbrev TZ : Rep ℤ K := Rep.trivial ℤ K ℤ

/-- `ℚ/ℤ`（= `ℚ ⧸ ℤ·1`）。 -/
abbrev QZ : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- `ℚ/ℤ` 上的平凡 `K`-表示。 -/
noncomputable abbrev TQD : Rep ℤ K := Rep.trivial ℤ K (QZ)

/-- 含入 `ℤ ↪ ℚ`（平凡表示之间，等变性平凡）。 -/
noncomputable def zToQHom : TZ K ⟶ QT K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    (Int.castAddHom ℚ).toIntLinearMap
    (by intro h; ext n; rfl))

/-- 商映射 `ℚ ↠ ℚ/ℤ`（平凡表示之间，等变性平凡）。 -/
noncomputable def qToQuotHom : QT K ⟶ TQD K :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    { toFun := fun q => QuotientAddGroup.mk q
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
    (by intro h; ext q; rfl))

@[simp] lemma zToQHom_apply (n : ℤ) : (zToQHom K).hom n = ((n : ℤ) : ℚ) := rfl
@[simp] lemma qToQuotHom_apply (q : ℚ) : (qToQuotHom K).hom q = QuotientAddGroup.mk q := rfl

/-- 商映射的核恰是 `ℤ·1`（用 `QuotientAddGroup.ker_mk'`，避免商关系 `eq` 的**取向歧义**）。 -/
lemma mk_eq_zero_iff (q : ℚ) :
    (QuotientAddGroup.mk q : QZ) = 0 ↔ q ∈ AddSubgroup.zmultiples (1 : ℚ) := by
  have h : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q : QZ) = QuotientAddGroup.mk q :=
    rfl
  rw [← h, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']

/-- `q ∈ ℤ·1` 的逐元素形式。 -/
lemma mem_zmultiples_one_iff (q : ℚ) :
    q ∈ AddSubgroup.zmultiples (1 : ℚ) ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩

/-- `mk (n : ℚ) = 0`。 -/
lemma mk_intCast_eq_zero (n : ℤ) :
    (QuotientAddGroup.mk ((n : ℤ) : ℚ) : QZ) = QuotientAddGroup.mk (0 : ℚ) :=
  (mk_eq_zero_iff _).mpr ((mem_zmultiples_one_iff _).mpr ⟨n, rfl⟩)

/-- 短复形 `0 → ℤ → ℚ → ℚ/ℤ → 0`（在 `Rep ℤ K` 中）。 -/
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

/-- 忘记到 `ModuleCat ℤ` 后的像正合。 -/
lemma qzComplexMod_exact :
    ((qzComplex K).map (forget₂ (Rep ℤ K) (ModuleCat ℤ))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact (mem_zmultiples_one_iff x).mp ((mk_eq_zero_iff x).mp hx)

/-- **`qzComplex` 正合**。 -/
theorem qzComplex_exact : (qzComplex K).Exact :=
  ((qzComplex K).exact_map_iff_of_faithful (forget₂ (Rep ℤ K) (ModuleCat ℤ))).mp
    (qzComplexMod_exact K)

/-- **`0 → ℤ → ℚ → ℚ/ℤ → 0` 是短正合列**。 -/
theorem qzComplex_shortExact : (qzComplex K).ShortExact :=
  ShortComplex.ShortExact.mk' (qzComplex_exact K)
    (inferInstanceAs (CategoryTheory.Mono (zToQHom K)))
    (inferInstanceAs (CategoryTheory.Epi (qToQuotHom K)))

/-- **连接同态是同构**：`H¹(K,ℚ/ℤ) ≅ H²(K,ℤ)`（两端 `ℚ` 系数消没）。 -/
noncomputable def coh1QZ_iso_coh2Z :
    groupCohomology (TQD K) 1 ≅ groupCohomology (TZ K) 2 :=
  @asIso _ _ _ _ (groupCohomology.δ (qzComplex_shortExact K) 1 2 rfl)
    (groupCohomology.isIso_δ_of_isZero (qzComplex_shortExact K) 1
      (isZero_QT K 0) (isZero_QT K 1))

/-! ## 8. `Hom(K,ℚ/ℤ)` 被 `3` 零化 ⟹ `coh²(K,ℤ)` 被 `3` 零化 -/

/-- `Additive K` 中一切元素被 `3` 零化（指数整除 3 ⟹ `3 • x = 0`）。

**工艺**：`rw [← toMul_eq_one, toMul_zsmul]` 把 `Additive` 侧的 `ℤ`-标量换成乘法侧
的 `zpow`，再用 `zpow_natCast` 与假设 `hK` 对齐——避开 `Additive K` 上
「`TypeTags` 实例 vs `AddGroup` 实例」的 `SMul ℤ` 分叉（`rw`/`map_zsmul` 在该分叉下报「找不到模式」）。 -/
lemma three_smul_additive_eq_zero (hK : ∀ x : K, x ^ 3 = 1) (x : Additive K) :
    (3 : ℤ) • x = (0 : Additive K) := by
  rw [← toMul_eq_one, toMul_zsmul]
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
  exact hK x.toMul

/-- `Hom(K,ℚ/ℤ)` 中一切元素被 `3` 零化（用 `hK`）。

**工艺**：`refine AddMonoidHom.ext (fun (x : Additive K) => ?_)` —— 显式类型标注使 `x`
在语法上就是 `Additive K`（`intro x` 会把类型化归成 `K`，使 `map_zsmul` 的实例合成失败）。 -/
lemma three_smul_hom_eq_zero (hK : ∀ x : K, x ^ 3 = 1)
    (φ : Additive K →+ TQD K) : (3 : ℤ) • φ = 0 := by
  refine AddMonoidHom.ext (fun (x : Additive K) => ?_)
  rw [AddMonoidHom.smul_apply]
  rw [show (3 : ℤ) • φ x = φ ((3 : ℤ) • x) from (map_zsmul φ 3 x).symm]
  rw [three_smul_additive_eq_zero K hK x, map_zero]
  rfl

/-- 「`3` 消没」沿 `LinearEquiv` **推出**：`V` 被零化 ⟹ `W` 被零化（`S1` 的 `kills_of_iso` 同款工艺）。 -/
lemma smul_three_eq_zero_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : ∀ v : V, (3 : ℤ) • v = 0) :
    ∀ w : W, (3 : ℤ) • w = 0 := by
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  exact (map_zsmul e.toLinearMap 3 v).symm.trans ((congrArg e (h v)).trans (map_zero _))

/-- 「`3` 消没」沿 `LinearEquiv` **拉回**：`W` 被零化 ⟹ `V` 被零化。 -/
lemma smul_three_eq_zero_of_linearEquiv' {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : ∀ w : W, (3 : ℤ) • w = 0) :
    ∀ v : V, (3 : ℤ) • v = 0 := by
  intro v
  obtain ⟨w, rfl⟩ := e.symm.surjective v
  exact (map_zsmul e.symm.toLinearMap 3 w).symm.trans
    ((congrArg e.symm (h w)).trans (map_zero _))

/-- **有限群 `K`（指数整除 3）上 `3` 消没 `coh²(K, ℤtriv)`。**

链：`coh²(K,ℤ) ≅ coh¹(K,ℚ/ℤ) ≅ Hom(K,ℚ/ℤ)`，后者被 `3` 零化。 -/
theorem threeKills_coh2 (hK : ∀ x : K, x ^ 3 = 1) :
    ∀ x : cohOf K (TZ K) 2, (3 : ℤ) • x = 0 :=
  smul_three_eq_zero_of_linearEquiv (coh1QZ_iso_coh2Z K).toLinearEquiv
    (smul_three_eq_zero_of_linearEquiv'
      (groupCohomology.H1IsoOfIsTrivial (TQD K)).toLinearEquiv
      (three_smul_hom_eq_zero K hK))

/-! ## 9. 公理闸门 -/

#print axioms zToQHom
#print axioms qToQuotHom
#print axioms qzComplex_shortExact
#print axioms coh1QZ_iso_coh2Z
#print axioms three_smul_hom_eq_zero
#print axioms threeKills_coh2
#print axioms constHom_comp_sumHom
#print axioms cardHom_comp_invCardHom
#print axioms isZero_QC
#print axioms map_cardHom_eq_zero
#print axioms isZero_QT

end TrivQ

end ABGV52
