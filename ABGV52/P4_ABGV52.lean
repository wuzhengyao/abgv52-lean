/-
  ABGV-5.2 —— **P 档 P4：`coh²(H, M|_H) ≅ Z/p²`**（C 档 `C3` ＋ `C8` 的 p 版）

  内容
  ====
    ① 秩：`rank Z[H] = p²`、`rank Vp = p⁴`、`rank I[H] = p² − 1`、
       **`rank (ker π) = p⁴ − p² + 1`**（论文 `prop:procesi-H` 的秩读数，p 版）；
    ② Procesi 序列的长正合列 5 项片段 ＋ 连接同态 `δ : H¹(I) → H²(M)`；
    ③ `δ` 是同构（`H¹(Vp) = H²(Vp) = 0`，P2）；
    ④ ⟹ **`H²(H, M|_H) ≅ Z/p²`**（论文 `lem:H2-MH` 的 p 版）。

  p-通用性：与 C3／C8 逐字同构，常数替换为 `9 → p*p`、`81 → (p*p)*(p*p)`、`8 → p*p − 1`、
  `73 → (p*p)*(p*p) − (p*p − 1)`。**注意**：秩等式的右端须写成 `((… : ℕ) : Cardinal)`——
  直接写 `p * p` 会被解析为 **Cardinal 乘法** `↑p * ↑p`（C 档写常数 `9`／`81` 时无此歧义）。
-/
import ABGV52.P3_ABGV52
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open CategoryTheory

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

attribute [local instance 1500] Rep.hV2

/-- `2 ≤ p`（`Fact p.Prime` 的直接推论，秩的算术用）。 -/
lemma two_le_p : 2 ≤ p := (Fact.out : p.Prime).two_le

/-! ## 0. 有限基数的消去小引理（self-contained） -/

/-- **有限基数消去**：若 `a` 是自然数、`x < ℵ₀` 且 `a + x = b`（`b` 自然数），则 `x = ↑(b - a)`。 -/
lemma cardinal_eq_of_add_eq_nat (a b : ℕ) (x : Cardinal) (hx : x < Cardinal.aleph0)
    (h : (a : Cardinal) + x = (b : Cardinal)) (hba : b - a ≠ 0) : x = (b - a : ℕ) := by
  have hnat : a + x.toNat = b := by
    have hc := congrArg Cardinal.toNat h
    rw [Cardinal.toNat_add (Cardinal.natCast_lt_aleph0) hx,
        Cardinal.toNat_natCast, Cardinal.toNat_natCast] at hc
    exact hc
  have hxa : x.toNat = b - a := by omega
  exact (Cardinal.toNat_eq_iff hba).mp hxa

/-! ## 1. 基数与 `Z[H]` 的秩 -/

/-- `MonoidAlgebra ℤ (Hp p)` 的标准基（指标集 `Hp p`）。 -/
noncomputable def basisRH : Module.Basis (Hp p) ℤ (MonoidAlgebra ℤ (Hp p)) :=
  MonoidAlgebra.basis (Hp p) ℤ

/-- **`Z[H]` 的 `ℤ`-秩是 `p²`。** -/
theorem rank_monoidAlgebra :
    Module.rank ℤ (MonoidAlgebra ℤ (Hp p)) = ((p * p : ℕ) : Cardinal) := by
  have h := Module.Basis.mk_eq_rank'' (basisRH p)
  rw [Cardinal.mk_fintype, card_Hp p] at h
  exact h.symm

/-! ## 2. 环绕模 `Vp p = Z[H]^{⊕p²}` 的秩 -/

/-- `Vp p` 与 `Hp p →₀ Z[H]` 的 `ℤ`-线性等价（秩引理针对 `Finsupp` 型）。 -/
noncomputable def VEquiv : Vp p ≃ₗ[ℤ] (Hp p →₀ MonoidAlgebra ℤ (Hp p)) :=
  (Finsupp.linearEquivFunOnFinite ℤ (MonoidAlgebra ℤ (Hp p)) (Hp p)).symm

/-- **`Vp p` 的 `ℤ`-秩是 `(p·p)·(p·p) = p⁴`。** -/
theorem rank_V : Module.rank ℤ (Vp p) = (((p * p) * (p * p) : ℕ) : Cardinal) := by
  rw [(VEquiv p).rank_eq, rank_finsupp, Cardinal.mk_fintype, card_Hp p,
    rank_monoidAlgebra p]
  simp only [Cardinal.lift_id, Nat.cast_mul]

/-! ## 3. 增广理想 `I[H]` 的秩 -/

lemma aug_surjective : Function.Surjective (aug p) := fun n =>
  ⟨(n : ℤ) • (1 : MonoidAlgebra ℤ (Hp p)), by
    rw [map_smul, aug_one, smul_eq_mul, mul_one]⟩

theorem rank_range_aug : Module.rank ℤ ↥(LinearMap.range (aug p)) = 1 := by
  rw [LinearMap.range_eq_top.mpr (aug_surjective p)]
  simp

/-- **`I[H]` 的 `ℤ`-秩是 `p² − 1`**（秩-零化度 ＋ 有限基数消去）。 -/
theorem rank_I_H : Module.rank ℤ ↥(I_H p) = ((p * p - 1 : ℕ) : Cardinal) := by
  have h := LinearMap.rank_range_add_rank_ker (aug p)
  rw [rank_range_aug p, rank_monoidAlgebra p] at h
  have hx : Module.rank ℤ ↥(LinearMap.ker (aug p)) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (Submodule.rank_le (LinearMap.ker (aug p))) ?_
    rw [rank_monoidAlgebra p]
    exact Cardinal.natCast_lt_aleph0
  have hone : 1 < p * p := by nlinarith [two_le_p p]
  have hba : p * p - 1 ≠ 0 := by omega
  have hres := cardinal_eq_of_add_eq_nat 1 (p * p) _ hx (by simpa using h) hba
  show Module.rank ℤ ↥(LinearMap.ker (aug p)) = ((p * p - 1 : ℕ) : Cardinal)
  exact hres

/-! ## 4. 主结论（秩）：`rk_Z (ker π) = p⁴ − p² + 1` -/

/-- **论文 `prop:procesi-H` 的秩读数（p 版）**：`M|_H = ker π` 的 `ℤ`-秩为 `p⁴ − p² + 1`。 -/
theorem rank_ker_pi :
    Module.rank ℤ ↥(LinearMap.ker (pi p)) = (((p * p) * (p * p) - (p * p - 1) : ℕ) : Cardinal) := by
  have h := LinearMap.rank_range_add_rank_ker (pi p)
  rw [range_pi_eq p, rank_I_H p, rank_V p] at h
  have hx : Module.rank ℤ ↥(LinearMap.ker (pi p)) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (Submodule.rank_le (LinearMap.ker (pi p))) ?_
    rw [rank_V p]
    exact Cardinal.natCast_lt_aleph0
  have hB : 1 ≤ p * p := by nlinarith [two_le_p p]
  have hbig : p * p < (p * p) * (p * p) := by nlinarith [two_le_p p]
  have hba : (p * p) * (p * p) - (p * p - 1) ≠ 0 := by omega
  exact cardinal_eq_of_add_eq_nat (p * p - 1) ((p * p) * (p * p)) _ hx (by simpa using h) hba

/-- 论文原样形式：`rk_Z M|_H = p⁴ − p² + 1`。 -/
theorem rank_ker_pi_pow :
    Module.rank ℤ ↥(LinearMap.ker (pi p)) = ((p ^ 4 - p ^ 2 + 1 : ℕ) : Cardinal) := by
  have hnat : (p * p) * (p * p) - (p * p - 1) = p ^ 4 - p ^ 2 + 1 := by
    have hB : 1 ≤ p * p := by nlinarith [two_le_p p]
    have hC : p * p ≤ (p * p) * (p * p) := by nlinarith [two_le_p p]
    have hp2 : p ^ 2 = p * p := by ring
    have hp4 : p ^ 4 = (p * p) * (p * p) := by ring
    rw [hp2, hp4]
    have hsucc : p * p - 1 + 1 = p * p := Nat.sub_add_cancel hB
    omega
  rw [rank_ker_pi p, hnat]

/-! ## 5. Procesi 序列的长正合列与 `δ` 的同构性 -/

open HomologicalComplex in
noncomputable def procesiLES : ComposableArrows (ModuleCat ℤ) 5 :=
  HomologySequence.composableArrows₅
    (groupCohomology.map_cochainsFunctor_shortExact (procesiComplex_shortExact p)) 1 2
    (by norm_num)

/-- 连接同态 `δ : H¹(H, I[H]) → H²(H, M|_H)`。 -/
noncomputable abbrev procesiDelta :
    groupCohomology (I_H_rep p) 1 ⟶ groupCohomology (M_rep p) 2 :=
  groupCohomology.δ (procesiComplex_shortExact p) 1 2 rfl

set_option linter.style.haveILetI false in
/-- **`δ` 是同构**：`H¹(Vp) = 0` 给单射，`H²(Vp) = 0` 给满射（P2 的零化）。 -/
theorem isIso_procesiDelta : IsIso (procesiDelta p) := by
  letI h1 : CategoryTheory.Mono (procesiDelta p) :=
    groupCohomology.mono_δ_of_isZero (procesiComplex_shortExact p) 1
      (isZero_groupCohomology_VRep p 0)
  letI h2 : CategoryTheory.Epi (procesiDelta p) :=
    groupCohomology.epi_δ_of_isZero (procesiComplex_shortExact p) 1
      (isZero_groupCohomology_VRep p 1)
  exact isIso_of_mono_of_epi (procesiDelta p)

attribute [local instance] isIso_procesiDelta

/-! ## 6. 主结论：`H²(H, M|_H) ≅ Z/p²` -/

/-- **论文 `lem:H2-MH` 的 p 版**：`H²(H, M|_H) ≅ C_{p²}`，Lean 版写为 `≅ ZMod (p*p)`。 -/
noncomputable def H2_MH_equiv_zmod :
    ↥(groupCohomology (M_rep p) 2) ≃ₗ[ℤ] ZMod (p * p) :=
  (asIso (procesiDelta p)).symm.toLinearEquiv.trans (H1_IH_equiv_zmod p)

/-! ## 7. 公理闸门 -/

#print axioms cardinal_eq_of_add_eq_nat
#print axioms rank_monoidAlgebra
#print axioms rank_V
#print axioms rank_I_H
#print axioms rank_ker_pi
#print axioms rank_ker_pi_pow
#print axioms isIso_procesiDelta
#print axioms H2_MH_equiv_zmod

end ABGV52.P
