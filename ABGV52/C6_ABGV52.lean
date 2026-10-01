/-
  ABGV-5.2 —— C 档 (b).1 第 2–3 步：`H¹(H, I[H]) ≅ Z/9`（增广序列的长正合列）

  路线（= 论文 `lem:H1-IH` 的 Lean 化）
  ==================================
    对 `0 → I[H] → Z[H] → Z → 0`（C4 已证短正合）取长正合列：
      `H⁰(I) → H⁰(Z[H]) →^{ε} H⁰(Z) →^{δ} H¹(I) → H¹(Z[H]) = 0`，
    消没项由 C5。逐项计算：
      * `H⁰(Z[H]) = Z[H]^H = Z·N`（法元 `N = Σ_h h`，本文件 §1）；
      * `H⁰(Z) = Z`（平凡作用）；
      * 上述映射把 `N` 送到 `ε(N) = 9`（§2）；
    ⟹ `H¹(I) ≅ Z/9Z`（§4，经 `LinearMap.quotKerEquivOfSurjective`）。

  本文件：§1 法元与不变量；§2 `ε(N) = 9`；§3 长正合列与 `δ` 的满射性；§4 同构。
-/
import ABGV52.C4_ABGV52
import ABGV52.C5_ABGV52
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.QuotientRing

open CategoryTheory

namespace ABGV52

-- `Z` 上商模的 `Module ℤ` 与 `AddCommGroup.toIntModule` 冲突（与 C4 的 `Rep.hV2` 同型）：
-- 把商模实例提到高优先级，使 `≃ₗ[ℤ]` 的表述与项合成用同一实例。
attribute [local instance 1500] Submodule.Quotient.module

/-! ## 1. 法元 `N = Σ_h h` 与正则模的不变量 -/

/-- 法元 `N = Σ_{h∈H} h`（写成 `single h 1` 的和）。 -/
noncomputable def normEl : MonoidAlgebra ℤ H :=
  ∑ h : H, MonoidAlgebra.single h (1 : ℤ)

/-- 左乘保法元（`h` 置换 `H`）。 -/
lemma lmul_normEl (h : H) : lmul h normEl = normEl := by
  have h1 : lmul h normEl
      = ∑ x : H, MonoidAlgebra.single (h * x) (1 : ℤ) := by
    rw [normEl, lmul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [← lmul, lmul_single]
  rw [h1]
  exact Equiv.sum_comp (Equiv.mulLeft h)
    (fun y : H => MonoidAlgebra.single y (1 : ℤ))

/-- `ε(N) = |H| = 9`。 -/
lemma aug_normEl : aug normEl = 9 := by
  rw [normEl, map_sum]
  simp only [aug_single]
  rw [Finset.sum_const, Finset.card_univ, show Fintype.card H = 9 from by decide]
  norm_num

/-- **正则模的不变量**：`(Z[H])^H = Z·N`。 -/
lemma mem_invariants_regZ_iff (w : MonoidAlgebra ℤ H) :
    w ∈ regZ.ρ.invariants ↔ ∃ c : ℤ, w = c • normEl := by
  constructor
  · intro hw
    refine ⟨w.coeff 1, ?_⟩
    have hconst : ∀ x : H, w.coeff x = w.coeff 1 := by
      intro x
      have hx : lmul x w = w := (Representation.mem_invariants regZ.ρ w).mp hw x
      have hc := congrArg (fun v : MonoidAlgebra ℤ H => v.coeff x) hx
      rw [show lmul x w = MonoidAlgebra.single x 1 * w from rfl,
        MonoidAlgebra.coeff_single_mul_apply] at hc
      simpa using hc.symm
    have hexp : w = ∑ x : H, (w.coeff 1) • MonoidAlgebra.single x (1 : ℤ) := by
      conv_lhs => rw [eq_sum_coeff_smul_single w]
      exact Finset.sum_congr rfl fun x _ => by rw [hconst x]
    calc w = ∑ x : H, (w.coeff 1) • MonoidAlgebra.single x (1 : ℤ) := hexp
      _ = (w.coeff 1) • ∑ x : H, MonoidAlgebra.single x (1 : ℤ) :=
            (Finset.smul_sum).symm
      _ = (w.coeff 1) • normEl := rfl
  · rintro ⟨c, rfl⟩
    refine (Representation.mem_invariants regZ.ρ (c • normEl)).mpr fun h => ?_
    show lmul h (c • normEl) = c • normEl
    rw [lmul_smul, lmul_normEl]

/-! ## 2. 增广序列的长正合列（5 项） -/

open HomologicalComplex in
/-- `0 → I[H] → Z[H] → Z → 0` 的长正合列的 5 项片段：
`H⁰(I) → H⁰(Z[H]) → H⁰(Z) →^{δ} H¹(I) → H¹(Z[H]) → H¹(Z)`。 -/
noncomputable def augLES : ComposableArrows (ModuleCat ℤ) 5 :=
  HomologySequence.composableArrows₅
    (groupCohomology.map_cochainsFunctor_shortExact augComplex_shortExact) 0 1 (by norm_num)

open HomologicalComplex in
theorem augLES_exact : augLES.Exact :=
  HomologySequence.composableArrows₅_exact _ 0 1 (by norm_num)

/-- 片段中第 2 支（`H⁰(Z[H]) → H⁰(Z)`）。 -/
noncomputable abbrev augH0Map : groupCohomology regZ 0 ⟶ groupCohomology trivRep 0 :=
  augLES.map' 1 2

/-- 片段中第 3 支（`δ : H⁰(Z) → H¹(I)`）。 -/
noncomputable abbrev augDelta : groupCohomology trivRep 0 ⟶ groupCohomology I_H_rep 1 :=
  augLES.map' 2 3

/-- **正合性**：`range(H⁰(Z[H]) → H⁰(Z)) = ker δ`。 -/
theorem augH0Map_range_eq_ker :
    LinearMap.range augH0Map.hom = LinearMap.ker augDelta.hom := by
  have h : (augLES.sc' augLES_exact.toIsComplex 1 2 3).Exact :=
    augLES_exact.exact' 1 2 3 (by norm_num) (by norm_num) (by norm_num)
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker
    (augLES.sc' augLES_exact.toIsComplex 1 2 3)).mp h

/-- `δ` 是满射（因 `H¹(H, Z[H]) = 0`）。 -/
theorem augDelta_surjective : Function.Surjective augDelta.hom :=
  (ModuleCat.epi_iff_surjective augDelta).mp
    (groupCohomology.epi_δ_of_isZero augComplex_shortExact 0
      (isZero_groupCohomology_regZ 0))

/-- **`H¹(H, I[H]) ≅ H⁰(H, Z) ⧸ range(H⁰(Z[H]) → H⁰(Z))`**。 -/
noncomputable def H1_IH_quot_equiv :
    (↥(groupCohomology trivRep 0) ⧸ LinearMap.range augH0Map.hom) ≃ₗ[ℤ]
      ↥(groupCohomology I_H_rep 1) :=
  (Submodule.quotEquivOfEq (LinearMap.ker augDelta.hom) (LinearMap.range augH0Map.hom)
      augH0Map_range_eq_ker.symm).symm.trans
    (LinearMap.quotKerEquivOfSurjective augDelta.hom augDelta_surjective)

/-! ## 3. 关键计算：`H⁰(H, Z) ≅ Z` 与 `range(H⁰(Z[H]) → H⁰(Z))` -/

/-- `Z` 上的平凡作用 ⟹ `H⁰(H, Z) ≅ Z`（不变量为全体）。 -/
noncomputable abbrev iota : ℤ →ₗ[ℤ] ↥(groupCohomology trivRep 0) :=
  (groupCohomology.H0IsoOfIsTrivial trivRep).inv.hom

/-- `H0Iso` 下 `ι` 的像就是原来的整数。 -/
lemma H0Iso_iota (n : ℤ) :
    ((groupCohomology.H0Iso trivRep).hom.hom (iota n)).1 = n := by
  have h : iota n = (ConcreteCategory.hom (groupCohomology.H0Iso trivRep).inv)
      ⟨n, by rw [Representation.invariants_eq_top]; trivial⟩ :=
    groupCohomology.H0IsoOfIsTrivial_inv_apply (A := trivRep) n
  rw [h]
  simp

/-- 把 `H⁰(regZ)` 的元素经 `H0Iso` 送到 `Z[H]` 中的取值（落在不变量子模里）。 -/
noncomputable abbrev toW (x : ↥(groupCohomology regZ 0)) : MonoidAlgebra ℤ H :=
  ((groupCohomology.H0Iso regZ).hom.hom x).1

lemma toW_mem (x : ↥(groupCohomology regZ 0)) : toW x ∈ regZ.ρ.invariants :=
  ((groupCohomology.H0Iso regZ).hom.hom x).2

/-- `H⁰(augHom)` 与 `aug` 在不变量上的关系（`map_id_comp_H0Iso_hom_apply` 的形式）。 -/
lemma H0Iso_augH0Map (x : ↥(groupCohomology regZ 0)) :
    ((groupCohomology.H0Iso trivRep).hom.hom (augH0Map.hom x)).1 = aug (toW x) := by
  have h := groupCohomology.map_id_comp_H0Iso_hom_apply (G := H) (k := ℤ) augHom x
  have h2 : (groupCohomology.map (MonoidHom.id H) augHom 0).hom x = augH0Map.hom x := rfl
  rw [← h2, h]
  rfl

/-- **核心引理**：`H⁰(Z[H]) → H⁰(Z)` 的像恰是 `9Z`。 -/
lemma iota_mem_range_iff (n : ℤ) :
    iota n ∈ LinearMap.range augH0Map.hom ↔ n ∈ Ideal.span ({9} : Set ℤ) := by
  have key : ∀ x : ↥(groupCohomology regZ 0),
      ((groupCohomology.H0Iso trivRep).hom.hom (augH0Map.hom x)).1
        = aug (toW x) := fun x => H0Iso_augH0Map x
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := (mem_invariants_regZ_iff _).mp (toW_mem x)
    have h3 : aug (toW x) = n := by
      rw [← key x, hx, H0Iso_iota]
    rw [hc, map_smul, aug_normEl, smul_eq_mul] at h3
    exact Ideal.mem_span_singleton.mpr ⟨c, by rw [← h3]; ring⟩
  · intro hn
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hn
    refine ⟨(groupCohomology.H0Iso regZ).inv.hom
      ⟨c • normEl, (mem_invariants_regZ_iff _).mpr ⟨c, rfl⟩⟩, ?_⟩
    have heq : (groupCohomology.H0Iso trivRep).hom.hom
          (augH0Map.hom ((groupCohomology.H0Iso regZ).inv.hom
            ⟨c • normEl, (mem_invariants_regZ_iff _).mpr ⟨c, rfl⟩⟩))
        = (groupCohomology.H0Iso trivRep).hom.hom (iota n) := by
      refine Subtype.ext ?_
      rw [key, H0Iso_iota]
      simp only [toW, Iso.inv_hom_id_apply, map_smul, aug_normEl, smul_eq_mul]
      rw [hc]; ring
    simpa only [Iso.hom_inv_id_apply] using
      congrArg ((groupCohomology.H0Iso trivRep).inv.hom) heq

/-! ## 4. 主结论：`H¹(H, I[H]) ≅ Z/9` -/

/-- 复合 `Z →^{ι} H⁰(H, Z) →^{δ} H¹(H, I[H])`。 -/
noncomputable abbrev psi : ℤ →ₗ[ℤ] ↥(groupCohomology I_H_rep 1) :=
  augDelta.hom.comp iota

/-- `ι : Z → H⁰(H, Z)` 满射（它是同构的逆）。 -/
lemma iota_surjective : Function.Surjective iota := by
  intro z
  refine ⟨((groupCohomology.H0Iso trivRep).hom.hom z).1, ?_⟩
  have heq : (groupCohomology.H0Iso trivRep).hom.hom
        (iota (((groupCohomology.H0Iso trivRep).hom.hom z).1))
      = (groupCohomology.H0Iso trivRep).hom.hom z :=
    Subtype.ext (H0Iso_iota (((groupCohomology.H0Iso trivRep).hom.hom z).1))
  simpa only [Iso.hom_inv_id_apply] using
    congrArg ((groupCohomology.H0Iso trivRep).inv.hom) heq

/-- `ψ` 的核恰是 `9Z`。 -/
lemma psi_ker : LinearMap.ker psi = Ideal.span ({9} : Set ℤ) := by
  ext n
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    refine (iota_mem_range_iff n).mp ?_
    rw [augH0Map_range_eq_ker]
    exact h
  · intro h
    have h2 : iota n ∈ LinearMap.range augH0Map.hom := (iota_mem_range_iff n).mpr h
    rw [augH0Map_range_eq_ker] at h2
    exact h2

lemma psi_surjective : Function.Surjective psi := by
  intro y
  obtain ⟨x, hx⟩ := augDelta_surjective y
  obtain ⟨n, rfl⟩ := iota_surjective x
  exact ⟨n, hx⟩

/-- **论文 `lem:H1-IH`**：`H¹(H, I[H]) ≅ Z/9`。 -/
noncomputable def H1_IH_equiv_zmod9 : ↥(groupCohomology I_H_rep 1) ≃ₗ[ℤ] ZMod 9 :=
  (LinearMap.quotKerEquivOfSurjective psi psi_surjective).symm.trans
    ((Submodule.quotEquivOfEq (LinearMap.ker psi) (Ideal.span ({9} : Set ℤ)) psi_ker).trans
      (Int.quotientSpanNatEquivZMod 9).toAddEquiv.toIntLinearEquiv)

/-! ## 5. 公理闸门 -/

#print axioms mem_invariants_regZ_iff
#print axioms aug_normEl
#print axioms augH0Map_range_eq_ker
#print axioms augDelta_surjective
#print axioms H0Iso_iota
#print axioms H0Iso_augH0Map
#print axioms iota_mem_range_iff
#print axioms psi_ker
#print axioms H1_IH_equiv_zmod9

end ABGV52
