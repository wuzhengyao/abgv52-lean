/-
  ABGV-5.2 —— C 档第一刀 · 步 3：`Z`-秩的计算（秩 73）

  技术路线（`Z` 非除环 ⟹ 用 `Module.rank`（基数），不用 `finrank`）
  ==============================================================
    * 秩-零化度：`LinearMap.rank_range_add_rank_ker`（需 `HasRankNullity ℤ`，
      由 `IsDomain.hasRankNullity` 提供，见 `Dimension/Localization.lean`）；
    * `Z[H]` 的秩 9：`MonoidAlgebra.basis H ℤ` ＋ `Module.Basis.mk_eq_rank''`；
    * `V = Z[H]^9` 的秩 81：`V ≃ₗ H →₀ Z[H]`（`Finsupp.linearEquivFunOnFinite`）
      ＋ `rank_finsupp`；
    * `I[H]` 的秩 8：对 `aug` 用秩-零化度（`aug` 满射 ⟹ 像秩 1）；
    * **基数消去**：由 `8 + x = 81` 得 `x = 73` —— 先由 `Submodule.rank_le` 得
      `x ≤ 81 < ℵ₀`（有限性），再过 `Cardinal.toNat`（`toNat_add` 需两侧 `< ℵ₀`）
      ＋ `Cardinal.toNat_eq_iff` 回到基数等式。
-/
import ABGV52.C2_ABGV52
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace ABGV52

/-! ## 0. 有限基数的消去小引理 -/

/-- **有限基数消去**（本步的关键：mathlib 无 `Cardinal.add_left_cancel`，此处自证）：
若 `a` 是自然数（有限）、`x < ℵ₀` 且 `a + x = b`（`b` 自然数），则 `x = ↑(b - a)`。 -/
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

lemma card_H : Fintype.card H = 9 := by decide

/-- `MonoidAlgebra ℤ H` 的标准基（指标集 `H`）。 -/
noncomputable def basisRH : Module.Basis H ℤ (MonoidAlgebra ℤ H) :=
  MonoidAlgebra.basis H ℤ

/-- **`Z[H]` 的 `Z`-秩是 9。** -/
theorem rank_monoidAlgebra : Module.rank ℤ (MonoidAlgebra ℤ H) = 9 := by
  have h := Module.Basis.mk_eq_rank'' basisRH
  rw [Cardinal.mk_fintype, card_H] at h
  exact h.symm

/-! ## 2. 环绕模 `V = Z[H]^9` 的秩 -/

/-- `V` 与 `H →₀ Z[H]` 的 `Z`-线性等价（秩引理针对 `Finsupp` 型）。 -/
noncomputable def VEquiv : V ≃ₗ[ℤ] (H →₀ MonoidAlgebra ℤ H) :=
  (Finsupp.linearEquivFunOnFinite ℤ (MonoidAlgebra ℤ H) H).symm

/-- **`V` 的 `Z`-秩是 81。** -/
theorem rank_V : Module.rank ℤ V = 81 := by
  rw [VEquiv.rank_eq, rank_finsupp, Cardinal.mk_fintype, card_H, rank_monoidAlgebra]
  norm_num

/-! ## 3. 增广理想 `I[H]` 的秩 -/

lemma aug_surjective : Function.Surjective aug := fun n =>
  ⟨(n : ℤ) • (1 : MonoidAlgebra ℤ H), by
    rw [map_smul, aug_one, smul_eq_mul, mul_one]⟩

theorem rank_range_aug : Module.rank ℤ ↥(LinearMap.range aug) = 1 := by
  rw [LinearMap.range_eq_top.mpr aug_surjective]
  simp

/-- **`I[H]` 的 `Z`-秩是 8**（对 `aug` 用秩-零化度 ＋ 有限基数消去）。 -/
theorem rank_I_H : Module.rank ℤ ↥I_H = 8 := by
  have h := LinearMap.rank_range_add_rank_ker aug
  rw [rank_range_aug, rank_monoidAlgebra] at h
  have hx : Module.rank ℤ ↥(LinearMap.ker aug) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (Submodule.rank_le (LinearMap.ker aug)) ?_
    rw [rank_monoidAlgebra]
    exact Cardinal.natCast_lt_aleph0
  have hres := cardinal_eq_of_add_eq_nat 1 9 _ hx (by simpa using h) (by norm_num)
  show Module.rank ℤ ↥(LinearMap.ker aug) = 8
  exact hres

/-! ## 4. 主结论：`rk_Z (ker π) = 73` -/

/-- **论文 `prop:procesi-H` 的秩读数**：`M|_H = ker π` 的 `Z`-秩为 73。 -/
theorem rank_ker_pi : Module.rank ℤ ↥(LinearMap.ker pi) = 73 := by
  have h := LinearMap.rank_range_add_rank_ker pi
  rw [range_pi_eq, rank_I_H, rank_V] at h
  have hx : Module.rank ℤ ↥(LinearMap.ker pi) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (Submodule.rank_le (LinearMap.ker pi)) ?_
    rw [rank_V]
    exact (by norm_num : (81 : Cardinal) < Cardinal.aleph0)
  have hres := cardinal_eq_of_add_eq_nat 8 81 _ hx (by simpa using h) (by norm_num)
  simpa using hres

/-! ## 5. 公理闸门 -/

#print axioms cardinal_eq_of_add_eq_nat
#print axioms rank_monoidAlgebra
#print axioms rank_V
#print axioms rank_I_H
#print axioms rank_ker_pi

end ABGV52
