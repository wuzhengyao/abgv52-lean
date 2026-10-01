/-
  ABGV-5.2 —— C 档 (b).2 第 2–3 步：`H²(H, M|_H) ≅ C_9`（论文 `lem:H2-MH`）

  路线
  ====
    * 把 `M|_H = ker π` 造成 `Rep ℤ H`（用 G2b 的 `ker_pi_stable`），得 **Procesi 序列**
      `0 → M|_H → V → I[H] → 0` 在 `Rep ℤ H` 中**短正合**（第三项用 C2 的 `range_pi_eq`）；
    * 取长正合列 `H¹(M) → H¹(V) → H¹(I) →^{δ} H²(M) → H²(V) → H²(I)`；
    * `H¹(V) = H²(V) = 0`（C7）⟹ `δ` 既单又满 ⟹ **`H²(M) ≅ H¹(I)`**；
    * 与 C6 的 `H¹(I) ≅ Z/9` 合成 ⟹ **`H²(H, M|_H) ≅ Z/9`**。
-/
import ABGV52.C7_ABGV52

open CategoryTheory

namespace ABGV52

-- 与 C4 同款的实例菱形消歧（`ℤ` 上 `AddCommGroup.toIntModule` vs `Rep.hV2`）。
attribute [local instance 1500] Rep.hV2

/-! ## 1. `M|_H = ker π` 作为 `Rep ℤ H` -/

noncomputable def M_H_act (h : H) (z : ↥(LinearMap.ker pi)) : ↥(LinearMap.ker pi) :=
  ⟨act h z.1, ker_pi_stable h z.2⟩

noncomputable instance : DistribMulAction H ↥(LinearMap.ker pi) where
  smul h z := M_H_act h z
  one_smul z := by
    apply Subtype.ext
    show act 1 z.1 = z.1
    exact act_one z.1
  mul_smul a b z := by
    apply Subtype.ext
    show act (a * b) z.1 = act a (act b z.1)
    exact act_mul a b z.1
  smul_zero h := by
    apply Subtype.ext
    show act h (0 : V) = 0
    exact act_zero h
  smul_add h x y := by
    apply Subtype.ext
    show act h (x.1 + y.1) = act h x.1 + act h y.1
    exact act_add h x.1 y.1

/-- **Procesi 限制 `M|_H = ker π` 作为 `Rep ℤ H`**。 -/
noncomputable def M_H_rep : Rep ℤ H :=
  Rep.ofDistribMulAction ℤ H ↥(LinearMap.ker pi)

/-! ## 2. Procesi 序列 `0 → M|_H → V → I[H] → 0` -/

/-- 包含 `M|_H ↪ V`。 -/
noncomputable def inclM : M_H_rep ⟶ VRep :=
  Rep.ofHom (Representation.IntertwiningMap.mk (LinearMap.ker pi).subtype (by
    intro h
    ext z
    rfl))

@[simp] lemma inclM_apply (z : M_H_rep.V) : inclM.hom z = z.1 := rfl

/-- `π` 以 `I[H]` 为靶（用 C2 的 `range_pi_eq`）。 -/
noncomputable def piToI : V →ₗ[ℤ] ↥I_H :=
  pi.codRestrict I_H fun z => range_pi_le (LinearMap.mem_range_self pi z)

/-- `π : V → I[H]` 作为 `Rep ℤ H` 的态射。 -/
noncomputable def piHom : VRep ⟶ I_H_rep :=
  Rep.ofHom (Representation.IntertwiningMap.mk piToI (by
    intro h
    refine LinearMap.ext fun z => ?_
    exact Subtype.ext (pi_equivariant h z)))

/-- **Procesi 短复形** `0 → M|_H → V → I[H] → 0`。 -/
noncomputable def procesiComplex : CategoryTheory.ShortComplex (Rep ℤ H) :=
  CategoryTheory.ShortComplex.mk inclM piHom (by
    ext z
    exact Subtype.ext ((LinearMap.mem_ker).mp z.2))

/-! ## 3. 短正合性 -/

instance : CategoryTheory.Mono inclM := by
  rw [Rep.mono_iff_injective]
  intro x y h
  exact Subtype.ext h

lemma piToI_surjective : Function.Surjective piToI := by
  intro w
  have hw : (w : MonoidAlgebra ℤ H) ∈ LinearMap.range pi := range_pi_eq.symm ▸ w.2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩

instance : CategoryTheory.Epi piHom :=
  (Rep.epi_iff_surjective piHom).mpr piToI_surjective

/-- 忘记到 `ModuleCat ℤ` 的像。 -/
noncomputable abbrev procesiComplexMod : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
  procesiComplex.map (forget₂ (Rep ℤ H) (ModuleCat ℤ))

lemma procesiComplexMod_exact : procesiComplexMod.Exact := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : (piToI x : ↥I_H) = 0 := hx
  have hx'' : ((piToI x : ↥I_H) : MonoidAlgebra ℤ H) = 0 := by rw [hx']; rfl
  exact ⟨⟨x, (LinearMap.mem_ker).mpr hx''⟩, rfl⟩

/-- **Procesi 序列正合**（经忠实忘记函子反射）。 -/
theorem procesiComplex_exact : procesiComplex.Exact :=
  (procesiComplex.exact_map_iff_of_faithful (forget₂ (Rep ℤ H) (ModuleCat ℤ))).mp
    procesiComplexMod_exact

/-- **Procesi 序列短正合**（论文 `prop:procesi-H`）。 -/
theorem procesiComplex_shortExact : procesiComplex.ShortExact :=
  ShortComplex.ShortExact.mk' procesiComplex_exact
    (inferInstanceAs (CategoryTheory.Mono inclM))
    (inferInstanceAs (CategoryTheory.Epi piHom))

/-! ## 4. 长正合列：`δ : H¹(I) → H²(M)` 是同构 -/

open HomologicalComplex in
/-- Procesi 序列长正合列的 5 项片段
`H¹(M) → H¹(V) → H¹(I) →^{δ} H²(M) → H²(V) → H²(I)`。 -/
noncomputable def procesiLES : ComposableArrows (ModuleCat ℤ) 5 :=
  HomologySequence.composableArrows₅
    (groupCohomology.map_cochainsFunctor_shortExact procesiComplex_shortExact) 1 2 (by norm_num)

/-- 连接同态 `δ : H¹(H, I[H]) → H²(H, M|_H)`。 -/
noncomputable abbrev procesiDelta :
    groupCohomology I_H_rep 1 ⟶ groupCohomology M_H_rep 2 :=
  groupCohomology.δ procesiComplex_shortExact 1 2 rfl

-- 此处 `letI` 是必需的（`isIso_of_mono_of_epi` 走实例表），故关掉该风格 lint。
set_option linter.style.haveILetI false in
/-- **`δ` 是同构**：`H¹(V) = 0` 给单射（`mono_δ_of_isZero`），`H²(V) = 0` 给满射
（`epi_δ_of_isZero`），二者都是 C7 的推论。 -/
theorem isIso_procesiDelta : IsIso procesiDelta := by
  letI h1 : CategoryTheory.Mono procesiDelta :=
    groupCohomology.mono_δ_of_isZero procesiComplex_shortExact 1
      (isZero_groupCohomology_VRep 0)
  letI h2 : CategoryTheory.Epi procesiDelta :=
    groupCohomology.epi_δ_of_isZero procesiComplex_shortExact 1
      (isZero_groupCohomology_VRep 1)
  exact isIso_of_mono_of_epi procesiDelta

attribute [local instance] isIso_procesiDelta

/-! ## 5. 主结论：`H²(H, M|_H) ≅ Z/9` -/

/-- **论文 `lem:H2-MH`**：`H²(H, M|_H) ≅ C_9`，Lean 版写为 `≅ ZMod 9`。 -/
noncomputable def H2_MH_equiv_zmod9 :
    ↥(groupCohomology M_H_rep 2) ≃ₗ[ℤ] ZMod 9 :=
  (asIso procesiDelta).symm.toLinearEquiv.trans H1_IH_equiv_zmod9

/-! ## 6. 公理闸门 -/

#print axioms M_H_rep
#print axioms procesiComplex_shortExact
#print axioms isIso_procesiDelta
#print axioms H2_MH_equiv_zmod9

end ABGV52
