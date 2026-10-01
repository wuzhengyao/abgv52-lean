/-
  ABGV-5.2 —— C 档 (b)：把增广序列造成 `Rep ℤ H` 的短复形

  目标（(b).1 的第 1 步）
  ===================
    短正合列 `0 → I[H] → Z[H] → Z → 0` 在 `Rep ℤ H` 中，用于其长正合列推出
    `coh^1(H, I[H]) ≅ coker(H^0(Z[H]) → H^0(Z)) ≅ Z/9`。

  本文件先落地：
    * `trivRep`：`Z` 上的平凡表示；
    * `augHom : regZ ⟶ trivRep`：增广作为 `Rep` 态射（等变性即 G2b 的 `aug_lmul`）；
    * `inclHom : I_H_rep ⟶ regZ`：子模包含；
    * `augComplex`：上述三者构成的短复形（`f ≫ g = 0` 由 `I_H = ker aug` 定义直接给出）。
-/
import ABGV52.G4_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace ABGV52

open CategoryTheory

-- **实例菱形消歧**：`ℤ` 上 `AddCommGroup.toIntModule` 与 `Rep.hV2` 同为 `Module ℤ ↥X`
-- 的候选，使 `Rep` 的 `ConcreteCategory`（进而 `forget₂ (Rep ℤ H) (ModuleCat ℤ)`）无法合成。
-- 把 `Rep.hV2` 提到高优先级即消除歧义（本文件全程 `k = ℤ`）。
attribute [local instance 1500] Rep.hV2

/-! ## 1. 平凡表示与增广态射 -/

/-- `Z` 上的平凡表示。 -/
noncomputable abbrev trivRep : Rep ℤ H := Rep.trivial ℤ H ℤ

/-- 逐元素形式：`ε (g · w) = ε w`（右端为平凡作用）。
**逐元素陈述可避开 `↑regZ` 与 `MonoidAlgebra ℤ H`「定义相等但非句法相等」的重写障碍。** -/
lemma aug_intertwining_elem (g : H) (w : MonoidAlgebra ℤ H) :
    aug (regZ.ρ g w) = trivRep.ρ g (aug w) := by
  have h : regZ.ρ g w = lmul g w := rfl
  rw [h, aug_lmul]
  rfl

/-- 增广 `ε : Z[H] → Z` 的等变性（`IntertwiningMap` 所需形态）。 -/
lemma aug_intertwining (g : H) :
    aug ∘ₗ (regZ.ρ g) = (trivRep.ρ g) ∘ₗ aug := by
  ext w
  exact aug_intertwining_elem g w

/-- **增广作为 `Rep ℤ H` 的态射**。 -/
noncomputable def augHom : regZ ⟶ trivRep :=
  Rep.ofHom (Representation.IntertwiningMap.mk aug aug_intertwining)

/-- 态射在元素上的作用就是 `aug`。 -/
@[simp] lemma augHom_apply (w : MonoidAlgebra ℤ H) : augHom.hom w = aug w := rfl

/-! ## 2. 包含 `I[H] ↪ Z[H]` -/

/-- `I[H] ↪ Z[H]`（子模包含）作为 `Rep` 态射。 -/
noncomputable def inclHom : I_H_rep ⟶ regZ :=
  Rep.ofHom (Representation.IntertwiningMap.mk I_H.subtype (by
    intro g
    ext w
    rfl))

@[simp] lemma inclHom_apply (w : ↥I_H) : inclHom.hom w = w.1 := rfl

/-! ## 3. 短复形及其零复合 -/

/-- 增广短复形 `0 → I[H] → Z[H] → Z → 0`。 -/
noncomputable def augComplex : CategoryTheory.ShortComplex (Rep ℤ H) :=
  CategoryTheory.ShortComplex.mk inclHom augHom (by
    ext w
    show aug w.1 = 0
    exact (LinearMap.mem_ker).mp w.2)

/-! ## 4. 单态射与满态射（用 `Rep` 的判据） -/

instance : CategoryTheory.Mono inclHom := by
  rw [Rep.mono_iff_injective]
  intro x y h
  exact Subtype.ext h

/-- `ε` 的满射性（本文件自足；与 C3 的 `aug_surjective` 同证）。 -/
lemma augHom_surjective : Function.Surjective augHom.hom := fun n =>
  ⟨n • (1 : MonoidAlgebra ℤ H), by
    show aug (n • (1 : MonoidAlgebra ℤ H)) = n
    rw [map_smul, aug_one, smul_eq_mul, mul_one]⟩

instance : CategoryTheory.Epi augHom :=
  (Rep.epi_iff_surjective augHom).mpr augHom_surjective

/-! ## 5. 正合性（逐元素形式；范畴包装见下节） -/

/-- **正合性的内容（逐元素）**：`v ∈ ker ε ⟹ v ∈ range(incl)`。 -/
theorem augComplex_exact_elem (v : MonoidAlgebra ℤ H) (hv : augHom.hom v = 0) :
    ∃ w : ↥I_H, inclHom.hom w = v :=
  ⟨⟨v, (LinearMap.mem_ker).mpr hv⟩, rfl⟩

/-- 反向包含：`range(incl) ⊆ ker(aug)`（即短复形的零复合）。 -/
theorem augComplex_zero_on_I (w : ↥I_H) : augHom.hom (inclHom.hom w) = 0 :=
  (LinearMap.mem_ker).mp w.2

/-! ## 6. 范畴包装：`augComplex` 是短正合列

  路线：忘记到 `ModuleCat ℤ`（忠实函子反射 `Exact`）＋ `moduleCat_exact_iff_range_eq_ker`。
  被验证的交换代数是「`range(incl) = I[H] = ker(aug)`」，与 §5 的逐元素形式同一内容。 -/

/-- 忘记函子 `Rep ℤ H ⥤ ModuleCat ℤ` 下的像。 -/
noncomputable abbrev augComplexMod : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
  augComplex.map (forget₂ (Rep ℤ H) (ModuleCat ℤ))

/-- 逐元素形式：忘记函子的像上 `ker g ⊆ range f`（内容 = §5 的正合性）。 -/
lemma augComplexMod_exact : augComplexMod.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : aug x = 0 := hx
  exact ⟨⟨x, (LinearMap.mem_ker).mpr hx'⟩, rfl⟩

/-- **`augComplex` 正合**（经忠实忘记函子反射）。 -/
theorem augComplex_exact : augComplex.Exact :=
  (augComplex.exact_map_iff_of_faithful (forget₂ (Rep ℤ H) (ModuleCat ℤ))).mp
    augComplexMod_exact

/-- **增广短复形是短正合列**（(b).1 的第 1 步落地）。 -/
theorem augComplex_shortExact : augComplex.ShortExact :=
  ShortComplex.ShortExact.mk' augComplex_exact
    (inferInstanceAs (CategoryTheory.Mono inclHom))
    (inferInstanceAs (CategoryTheory.Epi augHom))

/-! ## 7. 公理闸门 -/

#print axioms aug_intertwining
#print axioms augHom
#print axioms inclHom
#print axioms augComplex_exact_elem
#print axioms augComplex_zero_on_I
#print axioms augComplexMod_exact
#print axioms augComplex_exact
#print axioms augComplex_shortExact

end ABGV52
