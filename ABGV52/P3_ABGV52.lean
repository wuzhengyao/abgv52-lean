/-
  ABGV-5.2 —— **P 档 P3：`coh¹(H, I[H]) ≅ Z/p²`**（C 档 `C4` ＋ `C6` 的 p 版）

  内容
  ====
    ① 增广短复形 `0 → I[H] → Z[H] → Z → 0` 在 `Rep ℤ (Hp p)` 中**短正合**（C4）；
    ② 其长正合列 5 项片段 `H⁰(I) → H⁰(Z[H]) →^{ε} H⁰(Z) →^{δ} H¹(I) → H¹(Z[H])`（C6 §2）；
    ③ 逐项计算：`H⁰(Z[H]) = ℤ·N`（法元，正则表示的不变量）；`ε(N) = |H| = p·p`；
    ④ ⟹ **`H¹(H, I[H]) ≅ Z/p²`**（论文 `lem:H1-IH` 的 p 版）。

  p-通用性：本文件与 C4／C6 逐字同构，**唯一真数学改动**是 `aug_normEl`：
  常数 `9` 换成 `p * p`（用 P1 的 `card_Hp`）；其余（法元、不变量、长正合列、
  `Int.quotientSpanNatEquivZMod`）皆与 `p` 无关的结构论证。
-/
import ABGV52.P2_ABGV52
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.QuotientRing

open CategoryTheory

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

-- 两个实例菱形消歧（与 C 档同款）：`Rep.hV2` 与 `AddCommGroup.toIntModule`；
-- 以及商模的 `Module ℤ`（使 `≃ₗ[ℤ]` 的表述与项合成共用同一实例）。
attribute [local instance 1500] Rep.hV2
attribute [local instance 1500] Submodule.Quotient.module

/-! ## 1. 平凡表示与增广态射 -/

/-- `ℤ` 上的平凡表示。 -/
noncomputable abbrev trivRep : Rep ℤ (Hp p) := Rep.trivial ℤ (Hp p) ℤ

lemma aug_intertwining_elem (g : Hp p) (w : MonoidAlgebra ℤ (Hp p)) :
    aug p ((regZ p).ρ g w) = (trivRep p).ρ g (aug p w) := by
  have h : (regZ p).ρ g w = lmul p g w := rfl
  rw [h, aug_lmul]
  rfl

lemma aug_intertwining (g : Hp p) :
    aug p ∘ₗ ((regZ p).ρ g) = ((trivRep p).ρ g) ∘ₗ aug p := by
  ext w
  exact aug_intertwining_elem p g w

/-- **增广作为 `Rep ℤ (Hp p)` 的态射**。 -/
noncomputable def augHom : regZ p ⟶ trivRep p :=
  Rep.ofHom (Representation.IntertwiningMap.mk (aug p) (aug_intertwining p))

@[simp] lemma augHom_apply (w : MonoidAlgebra ℤ (Hp p)) : (augHom p).hom w = aug p w := rfl

/-- `I[H] ↪ Z[H]`（子模包含）作为 `Rep` 态射。 -/
noncomputable def inclHom : I_H_rep p ⟶ regZ p :=
  Rep.ofHom (Representation.IntertwiningMap.mk (I_H p).subtype (by
    intro g
    ext w
    rfl))

@[simp] lemma inclHom_apply (w : ↥(I_H p)) : (inclHom p).hom w = w.1 := rfl

/-- 增广短复形 `0 → I[H] → Z[H] → ℤ → 0`。 -/
noncomputable def augComplex : CategoryTheory.ShortComplex (Rep ℤ (Hp p)) :=
  CategoryTheory.ShortComplex.mk (inclHom p) (augHom p) (by
    ext w
    show aug p w.1 = 0
    exact (LinearMap.mem_ker).mp w.2)

instance : CategoryTheory.Mono (inclHom p) := by
  rw [Rep.mono_iff_injective]
  intro x y h
  exact Subtype.ext h

lemma augHom_surjective : Function.Surjective (augHom p).hom := fun n =>
  ⟨n • (1 : MonoidAlgebra ℤ (Hp p)), by
    show aug p (n • (1 : MonoidAlgebra ℤ (Hp p))) = n
    rw [map_smul, aug_one, smul_eq_mul, mul_one]⟩

instance : CategoryTheory.Epi (augHom p) :=
  (Rep.epi_iff_surjective (augHom p)).mpr (augHom_surjective p)

noncomputable abbrev augComplexMod : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
  (augComplex p).map (forget₂ (Rep ℤ (Hp p)) (ModuleCat ℤ))

lemma augComplexMod_exact : (augComplexMod p).Exact := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : aug p x = 0 := hx
  exact ⟨⟨x, (LinearMap.mem_ker).mpr hx'⟩, rfl⟩

/-- **增广短复形短正合**（(b).1 第 1 步的 p 版）。 -/
theorem augComplex_shortExact : (augComplex p).ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.mk'
    (((augComplex p).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ (Hp p)) (ModuleCat ℤ))).mp (augComplexMod_exact p))
    (inferInstanceAs (CategoryTheory.Mono (inclHom p)))
    (inferInstanceAs (CategoryTheory.Epi (augHom p)))

/-! ## 2. 法元 `N = Σ_h h` 与正则模的不变量 -/

/-- 法元 `N = Σ_{h} h`。 -/
noncomputable def normEl : MonoidAlgebra ℤ (Hp p) :=
  ∑ h : Hp p, MonoidAlgebra.single h (1 : ℤ)

lemma lmul_normEl (h : Hp p) : lmul p h (normEl p) = normEl p := by
  have h1 : lmul p h (normEl p)
      = ∑ x : Hp p, MonoidAlgebra.single (h * x) (1 : ℤ) := by
    rw [normEl, lmul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [← lmul, lmul_single]
  rw [h1]
  exact Equiv.sum_comp (Equiv.mulLeft h)
    (fun y : Hp p => MonoidAlgebra.single y (1 : ℤ))

/-- **`ε(N) = |H| = p·p`**（本波的唯一常数改动；C 档此处为 `9`）。 -/
lemma aug_normEl : aug p (normEl p) = p * p := by
  rw [normEl, map_sum]
  simp only [aug_single]
  rw [Finset.sum_const, Finset.card_univ, card_Hp p]
  simp

/-- **正则模的不变量**：`(Z[H])^H = ℤ·N`。 -/
lemma mem_invariants_regZ_iff (w : MonoidAlgebra ℤ (Hp p)) :
    w ∈ (regZ p).ρ.invariants ↔ ∃ c : ℤ, w = c • normEl p := by
  constructor
  · intro hw
    refine ⟨w.coeff 1, ?_⟩
    have hconst : ∀ x : Hp p, w.coeff x = w.coeff 1 := by
      intro x
      have hx : lmul p x w = w := (Representation.mem_invariants (regZ p).ρ w).mp hw x
      have hc := congrArg (fun v : MonoidAlgebra ℤ (Hp p) => v.coeff x) hx
      rw [show lmul p x w = MonoidAlgebra.single x 1 * w from rfl,
        MonoidAlgebra.coeff_single_mul_apply] at hc
      simpa using hc.symm
    have hexp : w = ∑ x : Hp p, (w.coeff 1) • MonoidAlgebra.single x (1 : ℤ) := by
      conv_lhs => rw [eq_sum_coeff_smul_single p w]
      exact Finset.sum_congr rfl fun x _ => by rw [hconst x]
    calc w = ∑ x : Hp p, (w.coeff 1) • MonoidAlgebra.single x (1 : ℤ) := hexp
      _ = (w.coeff 1) • ∑ x : Hp p, MonoidAlgebra.single x (1 : ℤ) :=
            (Finset.smul_sum).symm
      _ = (w.coeff 1) • normEl p := rfl
  · rintro ⟨c, rfl⟩
    refine (Representation.mem_invariants (regZ p).ρ (c • normEl p)).mpr fun h => ?_
    show lmul p h (c • normEl p) = c • normEl p
    rw [lmul_smul, lmul_normEl]

/-! ## 3. 增广序列的长正合列（5 项） -/

open HomologicalComplex in
noncomputable def augLES : ComposableArrows (ModuleCat ℤ) 5 :=
  HomologySequence.composableArrows₅
    (groupCohomology.map_cochainsFunctor_shortExact (augComplex_shortExact p)) 0 1 (by norm_num)

open HomologicalComplex in
theorem augLES_exact : (augLES p).Exact :=
  HomologySequence.composableArrows₅_exact _ 0 1 (by norm_num)

/-- 片段中第 2 支（`H⁰(Z[H]) → H⁰(ℤ)`）。 -/
noncomputable abbrev augH0Map : groupCohomology (regZ p) 0 ⟶ groupCohomology (trivRep p) 0 :=
  (augLES p).map' 1 2

/-- 片段中第 3 支（`δ : H⁰(ℤ) → H¹(I)`）。 -/
noncomputable abbrev augDelta :
    groupCohomology (trivRep p) 0 ⟶ groupCohomology (I_H_rep p) 1 :=
  (augLES p).map' 2 3

theorem augH0Map_range_eq_ker :
    LinearMap.range (augH0Map p).hom = LinearMap.ker (augDelta p).hom := by
  have h : ((augLES p).sc' (augLES_exact p).toIsComplex 1 2 3).Exact :=
    (augLES_exact p).exact' 1 2 3 (by norm_num) (by norm_num) (by norm_num)
  exact (CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker
    ((augLES p).sc' (augLES_exact p).toIsComplex 1 2 3)).mp h

theorem augDelta_surjective : Function.Surjective (augDelta p).hom :=
  (ModuleCat.epi_iff_surjective (augDelta p)).mp
    (groupCohomology.epi_δ_of_isZero (augComplex_shortExact p) 0
      (isZero_groupCohomology_regZ p 0))

noncomputable def H1_IH_quot_equiv :
    (↥(groupCohomology (trivRep p) 0) ⧸ LinearMap.range (augH0Map p).hom) ≃ₗ[ℤ]
      ↥(groupCohomology (I_H_rep p) 1) :=
  (Submodule.quotEquivOfEq (LinearMap.ker (augDelta p).hom) (LinearMap.range (augH0Map p).hom)
      (augH0Map_range_eq_ker p).symm).symm.trans
    (LinearMap.quotKerEquivOfSurjective (augDelta p).hom (augDelta_surjective p))

/-! ## 4. 逐项计算 -/

noncomputable abbrev iota : ℤ →ₗ[ℤ] ↥(groupCohomology (trivRep p) 0) :=
  (groupCohomology.H0IsoOfIsTrivial (trivRep p)).inv.hom

lemma H0Iso_iota (n : ℤ) :
    ((groupCohomology.H0Iso (trivRep p)).hom.hom (iota p n)).1 = n := by
  have h : iota p n = (ConcreteCategory.hom (groupCohomology.H0Iso (trivRep p)).inv)
      ⟨n, by rw [Representation.invariants_eq_top]; trivial⟩ :=
    groupCohomology.H0IsoOfIsTrivial_inv_apply (A := trivRep p) n
  rw [h]
  simp

noncomputable abbrev toW (x : ↥(groupCohomology (regZ p) 0)) : MonoidAlgebra ℤ (Hp p) :=
  ((groupCohomology.H0Iso (regZ p)).hom.hom x).1

lemma toW_mem (x : ↥(groupCohomology (regZ p) 0)) : toW p x ∈ (regZ p).ρ.invariants :=
  ((groupCohomology.H0Iso (regZ p)).hom.hom x).2

lemma H0Iso_augH0Map (x : ↥(groupCohomology (regZ p) 0)) :
    ((groupCohomology.H0Iso (trivRep p)).hom.hom ((augH0Map p).hom x)).1 = aug p (toW p x) := by
  have h := groupCohomology.map_id_comp_H0Iso_hom_apply (G := Hp p) (k := ℤ) (augHom p) x
  have h2 : (groupCohomology.map (MonoidHom.id (Hp p)) (augHom p) 0).hom x
      = (augH0Map p).hom x := rfl
  rw [← h2, h]
  rfl

/-- **核心引理**：`H⁰(Z[H]) → H⁰(ℤ)` 的像恰是 `p·p·ℤ`。 -/
lemma iota_mem_range_iff (n : ℤ) :
    iota p n ∈ LinearMap.range (augH0Map p).hom ↔ n ∈ Ideal.span ({(p * p : ℤ)} : Set ℤ) := by
  have key : ∀ x : ↥(groupCohomology (regZ p) 0),
      ((groupCohomology.H0Iso (trivRep p)).hom.hom ((augH0Map p).hom x)).1
        = aug p (toW p x) := fun x => H0Iso_augH0Map p x
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := (mem_invariants_regZ_iff p _).mp (toW_mem p x)
    have h3 : aug p (toW p x) = n := by
      rw [← key x, hx, H0Iso_iota]
    rw [hc, map_smul, aug_normEl, smul_eq_mul] at h3
    exact Ideal.mem_span_singleton.mpr ⟨c, by rw [← h3]; ring⟩
  · intro hn
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hn
    refine ⟨(groupCohomology.H0Iso (regZ p)).inv.hom
      ⟨c • normEl p, (mem_invariants_regZ_iff p _).mpr ⟨c, rfl⟩⟩, ?_⟩
    have heq : (groupCohomology.H0Iso (trivRep p)).hom.hom
          ((augH0Map p).hom ((groupCohomology.H0Iso (regZ p)).inv.hom
            ⟨c • normEl p, (mem_invariants_regZ_iff p _).mpr ⟨c, rfl⟩⟩))
        = (groupCohomology.H0Iso (trivRep p)).hom.hom (iota p n) := by
      refine Subtype.ext ?_
      rw [key, H0Iso_iota]
      simp only [toW, Iso.inv_hom_id_apply, map_smul, aug_normEl, smul_eq_mul]
      rw [hc]; ring
    simpa only [Iso.hom_inv_id_apply] using
      congrArg ((groupCohomology.H0Iso (trivRep p)).inv.hom) heq

/-! ## 5. 主结论：`H¹(H, I[H]) ≅ Z/p²` -/

/-- 复合 `ℤ →^{ι} H⁰(H, ℤ) →^{δ} H¹(H, I[H])`。 -/
noncomputable abbrev psi : ℤ →ₗ[ℤ] ↥(groupCohomology (I_H_rep p) 1) :=
  (augDelta p).hom.comp (iota p)

lemma iota_surjective : Function.Surjective (iota p) := by
  intro z
  refine ⟨((groupCohomology.H0Iso (trivRep p)).hom.hom z).1, ?_⟩
  have heq : (groupCohomology.H0Iso (trivRep p)).hom.hom
        (iota p (((groupCohomology.H0Iso (trivRep p)).hom.hom z).1))
      = (groupCohomology.H0Iso (trivRep p)).hom.hom z :=
    Subtype.ext (H0Iso_iota p (((groupCohomology.H0Iso (trivRep p)).hom.hom z).1))
  simpa only [Iso.hom_inv_id_apply] using
    congrArg ((groupCohomology.H0Iso (trivRep p)).inv.hom) heq

lemma psi_ker : LinearMap.ker (psi p) = Ideal.span ({(p * p : ℤ)} : Set ℤ) := by
  ext n
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    refine (iota_mem_range_iff p n).mp ?_
    rw [augH0Map_range_eq_ker p]
    exact h
  · intro h
    have h2 : iota p n ∈ LinearMap.range (augH0Map p).hom := (iota_mem_range_iff p n).mpr h
    rw [augH0Map_range_eq_ker p] at h2
    exact h2

lemma psi_surjective : Function.Surjective (psi p) := by
  intro y
  obtain ⟨x, hx⟩ := augDelta_surjective p y
  obtain ⟨n, rfl⟩ := iota_surjective p x
  exact ⟨n, hx⟩

/-- **论文 `lem:H1-IH` 的 p 版**：`H¹(H, I[H]) ≅ Z/p²`。 -/
noncomputable def H1_IH_equiv_zmod :
    ↥(groupCohomology (I_H_rep p) 1) ≃ₗ[ℤ] ZMod (p * p) :=
  (LinearMap.quotKerEquivOfSurjective (psi p) (psi_surjective p)).symm.trans
    ((Submodule.quotEquivOfEq (LinearMap.ker (psi p)) (Ideal.span ({(p * p : ℤ)} : Set ℤ))
        (psi_ker p)).trans
      (Int.quotientSpanNatEquivZMod (p * p)).toAddEquiv.toIntLinearEquiv)

/-! ## 6. 公理闸门 -/

#print axioms augComplex_shortExact
#print axioms mem_invariants_regZ_iff
#print axioms aug_normEl
#print axioms augH0Map_range_eq_ker
#print axioms augDelta_surjective
#print axioms iota_mem_range_iff
#print axioms psi_ker
#print axioms H1_IH_equiv_zmod

end ABGV52.P
