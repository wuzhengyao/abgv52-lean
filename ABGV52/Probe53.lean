import ABGV52.D9_ABGV52

open scoped Classical

namespace ABGV52

namespace EM
namespace Probe53

-- ===== 甲：API 侦察（一般引理所需）=====
#check @IsLocalization.surj
#check @IsFractionRing.div_surjective
#check @IsFractionRing.injective
#check @IsLocalization.injective
#check @mem_nonZeroDivisors_iff_ne_zero
#check @Finset.mul_prod_erase
#check @Finset.prod_ne_zero_iff
#check @MulSemiringAction.toRingEquiv
#check @map_prod
#check @smul_mul'

-- ===== 乙：一般引理本体（`Frac(R)^G = Frac(R^G)` 的清分母形）=====

/-- **一般引理（清分母形）**：`K = Frac(R)`，`G` 有限、经 `G`-作用与 `algebraMap` 相容作用在 `K` 上；
则每个 `G`-不变元 `z ∈ K` 可写成**两个 `G`-不变元之比**。

证明三行：`z = P/Q` ⟹ `Q̃ := ∏_g g·Q` 不变、`P̃ := z·Q̃ = P·∏_{g≠1} g·Q ∈ R` 且不变 ⟹ `z = P̃/Q̃`。 -/
theorem probe_fixed_fraction
    (G : Type*) [Group G] [Fintype G]
    (R : Type*) [CommRing R] [IsDomain R] [MulSemiringAction G R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [MulSemiringAction G K]
    (hcompat : ∀ (g : G) (r : R), g • algebraMap R K r = algebraMap R K (g • r))
    {z : K} (hz : ∀ g : G, g • z = z) :
    ∃ a b : R, (∀ g : G, g • a = a) ∧ (∀ g : G, g • b = b) ∧ b ≠ 0 ∧
      z * algebraMap R K b = algebraMap R K a := by
  obtain ⟨y, hy⟩ := IsLocalization.surj (nonZeroDivisors R) z
  set P : R := y.1 with hP
  set Q : R := (y.2 : R) with hQ
  have hQne : Q ≠ 0 := by rw [hQ]; exact mem_nonZeroDivisors_iff_ne_zero.mp y.2.2
  have hPQ : z * algebraMap R K Q = algebraMap R K P := by rw [hQ, hP]; exact hy
  set QtR : R := ∏ g : G, g • Q with hQtR
  set PtR : R := P * ∏ g ∈ Finset.univ.erase (1 : G), g • Q with hPtR
  -- Q̃ 在 `R` 中不变（`g ↦ g₀ * g` 是群的双射）
  have hQtR_inv : ∀ g₀ : G, g₀ • QtR = QtR := by
    intro g₀
    have h1 : g₀ • QtR = ∏ g : G, (g₀ * g) • Q := by
      rw [hQtR, show g₀ • (∏ g : G, g • Q) = ∏ g : G, g₀ • (g • Q) from
        map_prod (MulSemiringAction.toRingEquiv G R g₀) _ _]
      exact Finset.prod_congr rfl fun g _ => by rw [mul_smul]
    rw [h1]
    exact Finset.prod_bij (fun g _ => g₀ * g) (fun g _ => Finset.mem_univ _)
      (fun a _ b _ hab => mul_left_cancel hab)
      (fun b _ => ⟨g₀⁻¹ * b, Finset.mem_univ _, by group⟩) (fun g _ => rfl)
  have hQtR_ne : QtR ≠ 0 := by
    rw [hQtR]
    refine Finset.prod_ne_zero_iff.mpr fun g _ h => hQne ?_
    have h2 := congrArg (fun x : R => g⁻¹ • x) h
    rwa [smul_zero, ← mul_smul, inv_mul_cancel, one_smul] at h2
  have hQtR_split : QtR = Q * ∏ g ∈ Finset.univ.erase (1 : G), g • Q := by
    rw [hQtR, (Finset.mul_prod_erase Finset.univ (fun g : G => g • Q)
      (Finset.mem_univ (1 : G))).symm, one_smul]
  -- 关键恒等式：`P̃` 的像 = `z · (Q̃ 的像)`
  have hkey : algebraMap R K PtR = z * algebraMap R K QtR := by
    rw [hPtR, hQtR_split]
    simp only [map_mul, map_prod]
    rw [← hPQ, mul_assoc]
  -- `P̃` 不变（用 `algebraMap` 单射 + 特征向量运算）
  have hPtR_inv : ∀ g₀ : G, g₀ • PtR = PtR := by
    intro g₀
    refine IsFractionRing.injective R K ?_
    rw [← hcompat g₀ PtR, hkey, smul_mul', hz g₀, hcompat g₀ QtR, hQtR_inv g₀]
  exact ⟨PtR, QtR, hPtR_inv, hQtR_inv, hQtR_ne, hkey.symm⟩

end Probe53
end EM

end ABGV52

/-\! ## 公理闸门 -/

#print axioms ABGV52.EM.Probe53.probe_fixed_fraction
