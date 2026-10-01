/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-v：DFT 变元代换的收口**（③ 的第 2 段完成）

  承 D7。本件把「DFT 变元代换」从**单射**升级为**同构**，并接到函数域上：

  * **反向复合恒等** `dftSubstPoly ∘ dftInvPoly = id`（与 D7 的正向**同型**：
    求和重排 ＋ **对偶正交性** `∑_χ χ a = |A|δ_{a,1}`）；
  * ⟹ **`dftAlgEquivPoly : MvPolynomial (MulChar A F) F ≃ₐ[F] MvPolynomial A F`**
    （多项式层 DFT ＝ 变元代换）；
  * ⟹ 其**分式域搬运** `FractionRing (MvPolynomial (MulChar A F) F) ≃ₐ[F] FractionRing (MvPolynomial A F)`；
  * ⟹ **清分母**（D2 `freeSubst_clear` 的一般化：`Fin n` → 任意有限群 `A`，经 `posPartA`／`freeUnitA`）
    ⟹ `polyToFF_isFractionRing : IsFractionRing (MvPolynomial A F) (latticeFunctionField F (A → ℤ))`
    ⟹ **分数域层的 DFT 变元代换（同构）**
    `dftAlgEquiv : FractionRing (MvPolynomial (MulChar A F) F) ≃ₐ[F] latticeFunctionField F (A → ℤ)`。

  **⚠ 未完成**：`dftAlgEquiv` 的**等变性**（分数域层）未证（D7 只证到 `dftSubst` 层）；
  `diagMono` 桥（`dftSubst (单项式) = diagMono`）亦未证。
-/
import ABGV52.D7_ABGV52

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

/-\! ## 1. 反向复合恒等与多项式层变元代换 -/

section Reverse

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **对偶正交性**（特征群求和版）：`∑_χ χ a = |A|`（`a = 1`）／`0`（否则）。 -/
theorem sum_mulChar_apply_eq_ite (a : A) :
    ∑ χ : MulChar A F, χ a = if a = 1 then (Fintype.card A : F) else 0 := by
  by_cases h : a = 1
  · subst h
    rw [if_pos rfl, Finset.sum_congr rfl fun χ _ => map_one χ, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity A F, Nat.card_eq_fintype_card,
      Fintype.card_congr (unitsEquivSelf A)]
  · rw [if_neg h, sum_mulChar_eq_zero F A h]

lemma dftSubstPoly_C (r : F) :
    dftSubstPoly F A (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.aeval_C _ r

/-- **DFT 复合恒等（反向·逐生成元）**：`dftSubstPoly (dftInvPoly (X a)) = X a`（与正向同型）。 -/
lemma dftSubstPoly_dftInvPoly_X (a : A) :
    dftSubstPoly F A (dftInvPoly F A (MvPolynomial.X a)) = MvPolynomial.X a := by
  haveI := neZero_card_cast_of_hasEnoughRootsOfUnity F A
  rw [dftInvPoly_X]
  have h1 : dftSubstPoly F A ((Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F,
        MvPolynomial.C (χ a) * MvPolynomial.X χ)
      = (Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F,
          MvPolynomial.C (χ a) * (∑ b : A, MvPolynomial.C ((χ b)⁻¹) * MvPolynomial.X b) := by
    rw [show (Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F,
        MvPolynomial.C (χ a) * MvPolynomial.X χ
      = MvPolynomial.C ((Fintype.card A : F)⁻¹) * ∑ χ : MulChar A F,
        MvPolynomial.C (χ a) * MvPolynomial.X χ from by
      rw [Algebra.smul_def, MvPolynomial.C_eq_algebraMap]]
    rw [show (Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F,
        MvPolynomial.C (χ a) * (∑ b : A, MvPolynomial.C ((χ b)⁻¹) * MvPolynomial.X b)
      = MvPolynomial.C ((Fintype.card A : F)⁻¹) * ∑ χ : MulChar A F,
        MvPolynomial.C (χ a) * (∑ b : A, MvPolynomial.C ((χ b)⁻¹) * MvPolynomial.X b)
      from by rw [Algebra.smul_def, MvPolynomial.C_eq_algebraMap]]
    rw [map_mul, dftSubstPoly_C, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun χ _ => by
      rw [map_mul, dftSubstPoly_C, dftSubstPoly_X]
  rw [h1]
  have h2 : ∀ χ : MulChar A F, MvPolynomial.C (χ a) *
        (∑ b : A, MvPolynomial.C ((χ b)⁻¹) * MvPolynomial.X b)
      = ∑ b : A, MvPolynomial.C (χ a * (χ b)⁻¹) * MvPolynomial.X b := by
    intro χ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [← mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl fun χ _ => h2 χ]
  rw [Finset.sum_comm]
  have h3 : ∀ b : A, (∑ χ : MulChar A F, MvPolynomial.C (χ a * (χ b)⁻¹) *
        MvPolynomial.X b)
      = MvPolynomial.C (if a * b⁻¹ = 1 then (Fintype.card A : F) else 0) * MvPolynomial.X b := by
    intro b
    rw [← Finset.sum_mul, ← map_sum]
    congr 1
    have hval : ∀ χ : MulChar A F, χ a * (χ b)⁻¹ = χ (a * b⁻¹) := by
      intro χ
      rw [map_mul, map_inv]
    rw [Finset.sum_congr rfl fun χ _ => hval χ, sum_mulChar_apply_eq_ite]
  rw [Finset.sum_congr rfl fun b _ => h3 b]
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [if_neg (fun hc : a * b⁻¹ = 1 => hb (mul_inv_eq_one.mp hc).symm)]
      simp)
      (fun h => absurd (Finset.mem_univ a) h)]
  rw [if_pos (mul_inv_cancel a), Algebra.smul_def, MvPolynomial.C_eq_algebraMap,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ (NeZero.ne _), map_one, one_mul]

/-- **复合恒等（反向）**：`dftSubstPoly ∘ dftInvPoly = id`。 -/
theorem dftSubstPoly_comp_dftInvPoly :
    (dftSubstPoly F A).comp (dftInvPoly F A)
      = AlgHom.id F (MvPolynomial A F) :=
  MvPolynomial.algHom_ext fun a => dftSubstPoly_dftInvPoly_X F A a

/-- **多项式层的 DFT 变元代换（同构）**：`MvPolynomial (MulChar A F) F ≃ₐ[F] MvPolynomial A F`。 -/
noncomputable def dftAlgEquivPoly :
    MvPolynomial (MulChar A F) F ≃ₐ[F] MvPolynomial A F :=
  AlgEquiv.ofAlgHom (dftSubstPoly F A) (dftInvPoly F A)
    (dftSubstPoly_comp_dftInvPoly F A) (dftInvPoly_comp_dftSubstPoly F A)

lemma dftAlgEquivPoly_X (χ : MulChar A F) :
    dftAlgEquivPoly F A (MvPolynomial.X χ)
      = ∑ a : A, MvPolynomial.C ((χ a)⁻¹) * MvPolynomial.X a :=
  dftSubstPoly_X F A χ

end Reverse


/-\! ## 2. 分式域搬运（多项式层 → 分式域） -/

section FractionTransport

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

/-- 多项式层的变元代换诱导**分式域层**的同构。 -/
noncomputable def dftAlgEquivFraction :
    FractionRing (MvPolynomial (MulChar A F) F) ≃ₐ[F] FractionRing (MvPolynomial A F) :=
  IsFractionRing.algEquivOfAlgEquiv (dftAlgEquivPoly F A)

end FractionTransport

/-\! ## 3. 清分母（D2 `freeSubst_clear` 的一般化：`Fin n` → 任意有限群 `A`） -/

section Clearing

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
-- ⚠ 本段数学上不需要单位根假设；此处携带它是因 D7 的 `polySubst*` 引理签名自带该假设。
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

/-- 常数指数向量 `N·1`（清分母用的乘子）。 -/
def constIntA (N : ℕ) : A → ℤ := fun _ => (N : ℤ)

/-- 整向量逐分量取绝对值，读成 `ℕ`-指数向量（清分母用的「正部」）。 -/
noncomputable def posPartA (g : A → ℤ) : A →₀ ℕ :=
  Finset.univ.sum (fun a : A => Finsupp.single a ((g a).natAbs))

lemma posPartA_apply (g : A → ℤ) (a : A) : posPartA A g a = (g a).natAbs := by
  rw [posPartA, Finsupp.finsetSum_apply, Finset.sum_eq_single a]
  · exact Finsupp.single_eq_same
  · intro b _ hb; exact Finsupp.single_eq_of_ne hb.symm
  · intro h; exact absurd (Finset.mem_univ a) h

/-- `posPartA` 与 `finsuppEmb` 在非负锥上互逆。 -/
lemma finsuppEmb_posPart (g : A → ℤ) (hg : ∀ a, 0 ≤ g a) :
    finsuppEmb (A := A) (posPartA A g) = g := by
  ext a
  rw [finsuppEmb_apply, posPartA_apply]
  exact Int.natAbs_of_nonneg (hg a)

/-- 清分母用的乘子 `x^N = ∏_a x_a^N`（是 `F[ℤ^A]` 中单位）。 -/
noncomputable def freeUnitA (N : ℕ) : latticeAlgebra F (A → ℤ) :=
  MonoidAlgebra.single (Multiplicative.ofAdd (constIntA A N)) 1

lemma freeUnitA_isUnit (N : ℕ) : IsUnit (freeUnitA F A N) := by
  rw [freeUnitA, ← MonoidAlgebra.of_apply]
  exact (Group.isUnit (Multiplicative.ofAdd (constIntA A N))).map
    (MonoidAlgebra.of F (Multiplicative (A → ℤ)))

lemma polySubst_monomial_const (k : ℕ) :
    polySubst F A (MvPolynomial.monomial (posPartA A (constIntA A k)) 1)
      = freeUnitA F A k := by
  rw [polySubst_monomial, freeUnitA,
    finsuppEmb_posPart (A := A) (constIntA A k) (fun a => by simp [constIntA])]

/-- **升级**：把 `c · x^{N₀} ∈ im polySubst` 升到大乘子 `x^N`（`N₀ ≤ N`）。 -/
lemma polySubst_clear_mono {c : latticeAlgebra F (A → ℤ)} {N₀ : ℕ}
    {p : MvPolynomial A F} (hp : polySubst F A p = c * freeUnitA F A N₀)
    {N : ℕ} (hN : N₀ ≤ N) :
    polySubst F A (p * MvPolynomial.monomial (posPartA A (constIntA A (N - N₀))) 1)
      = c * freeUnitA F A N := by
  have hv : constIntA A N₀ + constIntA A (N - N₀) = constIntA A N := by
    ext a
    simp only [constIntA, Pi.add_apply]
    rw [← Nat.cast_add, Nat.add_sub_cancel' hN]
  rw [map_mul, polySubst_monomial_const, hp, mul_assoc, freeUnitA, freeUnitA,
    MonoidAlgebra.single_mul_single, ← ofAdd_add, hv, one_mul, freeUnitA]

lemma polySubst_mono {c : latticeAlgebra F (A → ℤ)} {N₀ : ℕ}
    {p : MvPolynomial A F} (hp : polySubst F A p = c * freeUnitA F A N₀)
    (N : ℕ) (hN : N₀ ≤ N) :
    ∃ p' : MvPolynomial A F, polySubst F A p' = c * freeUnitA F A N :=
  ⟨p * MvPolynomial.monomial (posPartA A (constIntA A (N - N₀))) 1,
    polySubst_clear_mono F A hp hN⟩

/-- **清分母（主引理）**：`F[ℤ^A]` 的每个元素乘以够大的 `x^N` 都落在多项式像里。 -/
theorem polySubst_clear (c : latticeAlgebra F (A → ℤ)) :
    ∃ (N : ℕ) (p : MvPolynomial A F), polySubst F A p = c * freeUnitA F A N := by
  induction c using MonoidAlgebra.induction_on with
  | of m =>
    set g : A → ℤ := m.toAdd with hg
    set N : ℕ := ∑ a : A, (g a).natAbs with hNdef
    have hN : ∀ a : A, 0 ≤ g a + (N : ℤ) := by
      intro a
      have h1 : (g a).natAbs ≤ N :=
        Finset.single_le_sum (f := fun b : A => (g b).natAbs) (fun b _ => Nat.zero_le _)
          (Finset.mem_univ a)
      have h2 : -(g a) ≤ ((g a).natAbs : ℤ) := by
        rw [← Int.natAbs_neg (g a)]
        exact Int.le_natAbs
      have h3 : ((g a).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
      linarith
    rw [MonoidAlgebra.of_apply]
    refine ⟨N, MvPolynomial.monomial (posPartA A (g + constIntA A N)) 1, ?_⟩
    have hm : Multiplicative.ofAdd g = m := by simp [hg]
    rw [polySubst_monomial, finsuppEmb_posPart (A := A) _ (fun a => by
        simpa [constIntA] using hN a),
      freeUnitA, ← hm, MonoidAlgebra.single_mul_single, ← ofAdd_add]
    simp
  | add x y hx hy =>
    obtain ⟨N₁, p₁, hp₁⟩ := hx
    obtain ⟨N₂, p₂, hp₂⟩ := hy
    obtain ⟨p₁', hp₁'⟩ := polySubst_mono F A hp₁ (max N₁ N₂) (le_max_left _ _)
    obtain ⟨p₂', hp₂'⟩ := polySubst_mono F A hp₂ (max N₁ N₂) (le_max_right _ _)
    exact ⟨max N₁ N₂, p₁' + p₂', by rw [map_add, hp₁', hp₂', add_mul]⟩
  | smul r x hx =>
    obtain ⟨N, p, hp⟩ := hx
    exact ⟨N, MvPolynomial.C r * p,
      by rw [map_mul, MvPolynomial.C_eq_algebraMap, AlgHom.commutes, hp,
        smul_mul_assoc, Algebra.smul_def]⟩

end Clearing

/-\! ## 4. 分数域层的 DFT 变元代换 -/

section FractionAlgEquiv

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

/-- 多项式环经 `polyToFF` 作用在函数域上（登记为实例，供 `FractionRing` 派生）。 -/
noncomputable instance instAlgebraPolyFF :
    Algebra (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) :=
  (polyToFF F A).toRingHom.toAlgebra

lemma algebraMap_polyFF (p : MvPolynomial A F) :
    algebraMap (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) p = polyToFF F A p := rfl

/-- **`F(ℤ^A)` 是多项式环的分式域**（D2 结论的一般化，用清分母引理）。 -/
theorem polyToFF_isFractionRing [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] :
    IsFractionRing (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) := by
  have hfs : FaithfulSMul (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    exact polyToFF_injective F A hxy
  refine IsFractionRing.of_field _ _ ?_
  intro z
  obtain ⟨⟨a, b⟩, hb⟩ :=
    IsLocalization.surj (nonZeroDivisors (latticeAlgebra F (A → ℤ))) z
  have hb0 : (b : latticeAlgebra F (A → ℤ)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hS : algebraMap (latticeAlgebra F (A → ℤ))
      (latticeFunctionField F (A → ℤ)) (b : latticeAlgebra F (A → ℤ)) ≠ 0 := by
    intro h
    refine hb0 (IsFractionRing.injective (latticeAlgebra F (A → ℤ))
      (latticeFunctionField F (A → ℤ)) ?_)
    rw [h, map_zero]
  have hz : z = algebraMap _ _ a
      / algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ))
          (b : latticeAlgebra F (A → ℤ)) :=
    (eq_div_iff hS).mpr hb
  obtain ⟨N₁, p, hp⟩ := polySubst_clear F A a
  obtain ⟨N₂, q, hq⟩ := polySubst_clear F A (b : latticeAlgebra F (A → ℤ))
  obtain ⟨p', hp'⟩ := polySubst_mono F A hp (max N₁ N₂) (le_max_left _ _)
  obtain ⟨q', hq'⟩ := polySubst_mono F A hq (max N₁ N₂) (le_max_right _ _)
  have hU : algebraMap (latticeAlgebra F (A → ℤ))
      (latticeFunctionField F (A → ℤ)) (freeUnitA F A (max N₁ N₂)) ≠ 0 := by
    intro h
    refine (freeUnitA_isUnit F A (max N₁ N₂)).ne_zero
      (IsFractionRing.injective (latticeAlgebra F (A → ℤ))
        (latticeFunctionField F (A → ℤ)) ?_)
    rw [h, map_zero]
  have haeq : algebraMap (latticeAlgebra F (A → ℤ))
        (latticeFunctionField F (A → ℤ)) a
      = algebraMap (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) p'
        / algebraMap (latticeAlgebra F (A → ℤ))
            (latticeFunctionField F (A → ℤ)) (freeUnitA F A (max N₁ N₂)) := by
    rw [eq_div_iff hU, ← map_mul, ← hp', algebraMap_polyFF]
    rfl
  have hbeq : algebraMap (latticeAlgebra F (A → ℤ))
        (latticeFunctionField F (A → ℤ)) (b : latticeAlgebra F (A → ℤ))
      = algebraMap (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) q'
        / algebraMap (latticeAlgebra F (A → ℤ))
            (latticeFunctionField F (A → ℤ)) (freeUnitA F A (max N₁ N₂)) := by
    rw [eq_div_iff hU, ← map_mul, ← hq', algebraMap_polyFF]
    rfl
  exact ⟨p', q', by rw [hz, haeq, hbeq, div_div_div_cancel_right₀ hU]⟩

/-- **DFT 变元代换（分数域层，同构）**：
`FractionRing (MvPolynomial (MulChar A F) F) ≃ₐ[F] latticeFunctionField F (A → ℤ)`。 -/
noncomputable def dftAlgEquiv [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] :
    FractionRing (MvPolynomial (MulChar A F) F) ≃ₐ[F] latticeFunctionField F (A → ℤ) := by
  haveI := polyToFF_isFractionRing F A
  exact (dftAlgEquivFraction F A).trans
    ((FractionRing.algEquiv (MvPolynomial A F)
      (latticeFunctionField F (A → ℤ))).restrictScalars F)

end FractionAlgEquiv

/-\! ## 5. 公理闸门 -/

#print axioms sum_mulChar_apply_eq_ite
#print axioms dftSubstPoly_dftInvPoly_X
#print axioms dftSubstPoly_comp_dftInvPoly
#print axioms dftAlgEquivPoly
#print axioms dftAlgEquivFraction
#print axioms constIntA
#print axioms posPartA
#print axioms finsuppEmb_posPart
#print axioms freeUnitA
#print axioms freeUnitA_isUnit
#print axioms polySubst_monomial_const
#print axioms polySubst_clear_mono
#print axioms polySubst_mono
#print axioms polySubst_clear
#print axioms polyToFF_isFractionRing
#print axioms dftAlgEquiv

end

end EM

end ABGV52
