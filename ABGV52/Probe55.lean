import ABGV52.D12_ABGV52

open scoped Classical

namespace ABGV52

namespace EM
namespace Probe55

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

-- ===== 甲：`Φ₀` 单射的两条路线侦察（API 直读）=====
-- 路线 A（全单射，本探针主张）：构造 `Ψ := psiPoly 在分式域上的上延`（靶 = diagFrac），
--   再证 `Ψ ∘ Φ₀ = id` ⟹ `Φ₀` 单射（**无需**分 `m ∈ Y` / `m ∉ Y`）。
-- 路线 B（用户建议）：用 `smul_diagMono` 的特征向量性先清 `m ∉ Y`，余下 `m ∈ Y` 是实质。
#check @IsFractionRing.liftAlgHom
#check @IsLocalization.liftAlgHom
#check @IsFractionRing.lift
#check @IsLocalization.lift
#check @smul_diagMono
#check @charOf_single

/-- **正交性（心脏）**：`∑_a (χ a)⁻¹ • u_a = z_χ`（`u_a = |A|⁻¹ ∑_ψ ψ(a) z_ψ`）。

即逆 DFT 的**左逆恒等式**——它是 `Ψ ∘ Φ₀ = id` 的生成元层（也印证 D11 的截面恒等式在单项式层的形状）。 -/
lemma sum_inv_smul_uX (χ : MulChar A F) :
    ∑ a : A, (χ a)⁻¹ • uX F A a = zMono F A (Finsupp.single χ 1) := by
  have hne : (Fintype.card A : F) ≠ 0 := NeZero.ne _
  have hexp : ∀ a : A, (χ a)⁻¹ • uX F A a
      = (Fintype.card A : F)⁻¹ •
          ∑ ψ : MulChar A F, (ψ a * (χ a)⁻¹) • zMono F A (Finsupp.single ψ 1) := by
    intro a
    show (χ a)⁻¹ • ((Fintype.card A : F)⁻¹ •
        ∑ ψ : MulChar A F, (ψ a) • zMono F A (Finsupp.single ψ 1)) = _
    rw [smul_smul, mul_comm, ← smul_smul, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [smul_smul, mul_comm]
  rw [Finset.sum_congr rfl fun a _ => hexp a]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hfac : (∑ ψ : MulChar A F,
        ∑ a : A, (ψ a * (χ a)⁻¹) • zMono F A (Finsupp.single ψ 1))
      = ∑ ψ : MulChar A F,
          (∑ a : A, ψ a * (χ a)⁻¹) • zMono F A (Finsupp.single ψ 1) :=
    Finset.sum_congr rfl fun ψ _ => Finset.sum_smul.symm
  rw [hfac]
  rw [Finset.sum_eq_single χ]
  · rw [Finset.sum_congr rfl (fun a _ => mul_inv_cancel₀ (mulChar_apply_ne_zero F A χ a)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  · intro ψ _ hψ
    have hzero : (∑ a : A, ψ a * (χ a)⁻¹) = 0 := by
      have hcongr : (∑ a : A, ψ a * (χ a)⁻¹) = ∑ a : A, (ψ * χ⁻¹) a :=
        Finset.sum_congr rfl fun a _ => by rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
      rw [hcongr]
      exact MulChar.sum_eq_zero_of_ne_one (χ := ψ * χ⁻¹) (fun hc => hψ (mul_inv_eq_one.mp hc))
    rw [hzero, zero_smul]
  · intro hχ
    exact absurd (Finset.mem_univ χ) hχ

/-\! ## 公理闸门 -/

#print axioms sum_inv_smul_uX

end Probe55
end EM

end ABGV52
