/-
  ABGV-5.2 —— **平凡群基例：一切模皆 flasque**（Tate 层 T1，2026-10-11）

  **用途**：命名假设 `FlasqueClassWellDefinedHyp` 在 `PUnit` 档的反例需要两半，本件给出其中
  「**平凡群上一切模皆 flasque**」这一半 ✓（另一半 `ℤ/2 ≁ ℤ` 见假设状态笔记的登记 ✗）。

  **路线**：`G` 为平凡群（`[Subsingleton G]`）时 `M.ρ.norm = 1` ✓ ⟹ `M.norm.asHom.toModuleCatHom = 𝟙` ✓
  ⟹ **`Mono M.tateNorm`** ✓；Tate 复形在 `-1` 处 `d (-1) 0 = tateNorm` ✓ ⟹ 该处 **`cycles`（核）为零** ✓
  ⟹ 由 `homologyπ` 是 **epi** 与 `IsZero.of_epi` 得 **该处同调为零** ✓ ⟹ `Ĥ^{-1} = 0` ⟹ flasque ✓。

  **无 sorry、无自造公理**；公理门见 §4。**不修改任何旧接口** ✗。
-/
import ABGV52.Flasque_ABGV52
import ABGV52.TateLayer_ABGV52
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

attribute [local instance 1500] Rep.hV2

variable (G : Type) [Group G] [Fintype G] [Subsingleton G]

/-! ## §1 三步：`norm = 1` ⟹ `norm = 𝟙` ⟹ `Mono tateNorm` -/

/-- 平凡群下 `tateNorm` 是单射 ✓。 -/
theorem tateNorm_mono_of_subsingleton (M : Rep.{0,0,0} ℤ G) : Mono M.tateNorm := by
  have hnorm : M.ρ.norm = 1 := by
    rw [Representation.norm]; rw [Finset.sum_eq_single (1 : G)]
    · simp
    · intro b _ hb; exact absurd (Subsingleton.elim b 1) hb
    · intro h; exact absurd (Finset.mem_univ 1) h
  have hnorm' : M.norm.asHom.toModuleCatHom = 𝟙 (ModuleCat.of ℤ M.V) := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    show (M.norm.asHom.hom) x = x
    rw [Rep.norm_apply, hnorm]; rfl
  show Mono ((groupHomology.chainsIso₀ M).hom ≫ M.norm.asHom.toModuleCatHom ≫
    (groupCohomology.cochainsIso₀ M).inv)
  rw [hnorm']
  simp only [Category.id_comp]
  infer_instance

/-! ## §2 该处同调为零 ⟹ `Ĥ^{-1} = 0` -/

/-- Tate 复形在 `-1` 处的同调为零 ✓（`cycles` 是 `d (-1) 0 = tateNorm` 的核，mono ⟹ 核为零；
再由 `homologyπ` 是 epi 与 `IsZero.of_epi` 推得）。 -/
theorem isZero_homology_neg_one_of_subsingleton (M : Rep.{0,0,0} ℤ G) :
    IsZero ((tateComplex M).homology (-1)) := by
  have hmono : Mono ((tateComplex M).d (-1) 0) := by
    rw [tateComplex_d_neg_one]
    exact tateNorm_mono_of_subsingleton G M
  haveI := hmono
  have hnext : (ComplexShape.up ℤ).next (-1) = 0 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk (-1) 0 (by norm_num))
  have hcyc : IsZero ((tateComplex M).cycles (-1)) :=
    KernelFork.IsLimit.isZero_of_mono ((tateComplex M).cyclesIsKernel (-1) 0 hnext)
  exact IsZero.of_epi ((tateComplex M).homologyπ (-1)) hcyc

/-- **`PUnit` 档的专门化** ✓（反例要用的形）：平凡群 `PUnit` 上 Tate 复形在 `-1` 处同调为零 ⟹
`Ĥ^{-1}(1, M) = 0` ✓。 -/
theorem isZero_homology_neg_one_punit (M : Rep.{0,0,0} ℤ PUnit) :
    IsZero ((tateComplex M).homology (-1)) :=
  isZero_homology_neg_one_of_subsingleton PUnit M

/-- **T1 主结论（引姊妹件）** ✓：`TateLayer_ABGV52.isFlasque_punit` 给出全称形
`IsFlasque PUnit M` ✓；本件保留 `isZero (homology (-1))` 形作为**独立路线的复核** ✓。 -/
theorem isFlasque_punit_via_tateLayer (M : Rep.{0,0,0} ℤ PUnit) : IsFlasque PUnit M :=
  isFlasque_punit M

/-- **登记的收口缺口（已由姊妹件收口 ✓，此处仅存历史）** ✗：把上述 `IsZero` 翻成 `IsFlasque G M`（形如
`∀ K : Subgroup G, Subsingleton (tateHMinusOneSub G K M)`）时，在
`@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K) (Rep.res K.subtype M) (-1)` 处
**实例位序**未打通 ✗**本轮逐字报错** ✓（三次尝试）：
① 不显式给 `Fintype ↥K` 时：`failed to synthesize instance: Fintype ↥K` ✗；
② 给了 `Fintype.ofFinite ↥K` 后，`show Subsingleton ↥((tateComplex (Rep.res K.subtype M)).homology (-1))` 报
`'show' tactic failed … is not definitionally equal to target Subsingleton (tateHMinusOneSub G K M)` ✗
—— 即 **`tateHMinusOneSub` 的展开与 `(tateComplex _).homology (-1)` 不是 defeq** ✗。
**第三次尝试** ✗：用 `dsimp only [tateCohomology, tateCohomologyFunctor, tateComplexFunctor, tateComplex]` 展开后，
目标变成 **函子结构字面** `IsZero (({ obj := fun M => (tateComplexConnectData M).cochainComplex, map := … }).obj …)` ✗，
仍与 `IsZero ((tateComplex _).homology (-1))` **不 defeq** ✗（逐字报错在案 ✓）。
**下一手** ✗：把上一节的 `IsZero` 结论**直接以 `tateCohomology` 形**重述（先 `#print tateCohomologyFunctor` 看
`tateComplex` 与 `(tateComplexFunctor R G).obj M` 的关系 ✗），或构造两者之间的**显式 iso** 再用 `IsZero.of_iso` ✓；
也可直接以 `tateHMinusOneSub` 为对象重证一遍 §2（那里同样的模板只需换目标形 ✓）。 -/
theorem isFlasque_wrapper_gap_registered : True := trivial

/-! ## §4 公理闸门 -/

#print axioms tateNorm_mono_of_subsingleton
#print axioms isZero_homology_neg_one_of_subsingleton
#print axioms isZero_homology_neg_one_punit
#print axioms isFlasque_punit_via_tateLayer
#print axioms isFlasque_wrapper_gap_registered

end ABGV52
