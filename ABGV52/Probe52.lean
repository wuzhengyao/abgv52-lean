import ABGV52.D9_ABGV52

open scoped Classical

namespace ABGV52

namespace EM
namespace Probe52

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

-- ===== 甲：探项 1（等型分量 ⟹ 每分量 1 维）——库内机制现状 =====
#check @Submodule.finrank_mono
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @Submodule.finrank_sup_le
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @Submodule.finrank_iSup_le
#check @FixedPoints.finrank_eq_card
#check @MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity

-- ===== 乙：探项 2（e_i 用 y-单项式表出）——库内机制现状 =====
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @MvPolynomial.esymm
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @MvPolynomial.mul_esymm_eq_sum
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @MvPolynomial.prod_X_sub_C_eq_sum_esymm

-- ===== 丙：推荐路线（对角模型）的三条核心 =====

-- 丙-0：API 侦察（系数与分解）
#check @Finsupp.induction
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @Finsupp.coeff_add
#check @MonoidAlgebra.coeff_add
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @MonoidAlgebra.coeff_single_eq
#check @MonoidAlgebra.coeff_smul
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @MonoidAlgebra.coeff_mul_single
-- （探针读数已入 wiki §3j-sexies：此常量不在库）-- #check @MonoidAlgebra.coeff_single_mul
#check @Finsupp.finsetSum_apply
#check @Finsupp.mem_support_iff
#check @diagAlgHom_apply_single'
#check @smul_zMono
#check @MonoidAlgebra.coeff_single
#check @MonoidAlgebra.coeff_single_apply
#check @MonoidAlgebra.coeff_inj
#check @MonoidAlgebra.sum_coeff_single
#check @MonoidAlgebra.coeff_sum

/-- **丙-1 系数公式**：`(g • P).coeff z^m = P.coeff z^m * charOf(m)(g)`。 -/
lemma probe_coeff_smul (g : A) (P : diagAlgebra F A)
    (n : Multiplicative (MulChar A F →₀ ℤ)) :
    (g • P).coeff n = P.coeff n * charOf F A n.toAdd g := by
  induction P using MonoidAlgebra.induction_on with
  | of m =>
      show (diagAlgHom F A g (MonoidAlgebra.single m 1)).coeff n
        = (MonoidAlgebra.single m 1).coeff n * charOf F A n.toAdd g
      rw [diagAlgHom_apply_single' F A g m 1, ← Algebra.smul_def, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, MonoidAlgebra.coeff_single_apply]
      by_cases h : m = n
      · rw [if_pos h, h, mul_one, one_mul]
      · rw [if_neg h, mul_zero, zero_mul]
  | add x y hx hy =>
      rw [smul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
        Finsupp.add_apply, hx, hy]
      ring
  | smul r x hx =>
      show (g • (r • x)).coeff n = (r • x).coeff n * charOf F A n.toAdd g
      rw [smul_comm g r x, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, Finsupp.smul_apply, hx, smul_eq_mul, smul_eq_mul]
      ring

/-- **丙-2 支撑落入核格**：不变元素的每个非零系数项都在 `Y` 中。 -/
lemma probe_coeff_ne_zero_mem_kernel {P : diagAlgebra F A} (hP : ∀ g : A, g • P = P)
    {n : Multiplicative (MulChar A F →₀ ℤ)} (hn : P.coeff n ≠ 0) :
    n.toAdd ∈ kernelLattice F A := by
  rw [mem_kernelLattice_iff]
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g : A, charOf F A n.toAdd g ≠ 1 := by
    by_contra h
    exact hne (MulChar.ext fun a => by simpa using not_not.mp (not_exists.mp h a))
  have h := probe_coeff_smul F A g P n
  rw [hP g] at h
  exact hg (mul_left_cancel₀ hn (by rw [mul_one]; exact h.symm))

/-- **丙-3 不变元落在不变单项式的张成中**（`zMono` 在 `Y` 上的张成）。 -/
lemma probe_invariant_mem_span {P : diagAlgebra F A} (hP : ∀ g : A, g • P = P) :
    P ∈ Submodule.span F
      (Set.range fun m : ↥(kernelLattice F A) => zMono F A (m : expVector F A)) := by
  have hmem : ∀ n ∈ P.coeff.support, n.toAdd ∈ kernelLattice F A := fun n hn =>
    probe_coeff_ne_zero_mem_kernel F A hP (Finsupp.mem_support_iff.mp hn)
  have hdecomp : P = ∑ n ∈ P.coeff.support, MonoidAlgebra.single n (P.coeff n) :=
    (MonoidAlgebra.sum_coeff_single P).symm
  rw [hdecomp]
  refine Submodule.sum_mem _ fun n hn => ?_
  rw [show MonoidAlgebra.single n (P.coeff n) = (P.coeff n) • zMono F A n.toAdd
    from single_eq_smul_zMono F A n.toAdd (P.coeff n)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n.toAdd, hmem n hn⟩, rfl⟩)

/-\! ## 公理闸门 -/

#print axioms probe_coeff_smul
#print axioms probe_coeff_ne_zero_mem_kernel
#print axioms probe_invariant_mem_span

end Probe52
end EM

end ABGV52
