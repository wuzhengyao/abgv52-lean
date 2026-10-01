/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-ii：DFT 层**（Fischer 的引擎）

  设 `A` 是**有限交换群**、`F` 是含足够单位根的域。本件在**正则置换格**
  `M = Z[A] = (A → ℤ)`（`A` 经左乘作用）的单项式环 `F[M]` 上构造
  **离散 Fourier 基** `dftVec χ = ∑ a, single e_a (χ a⁻¹)`（`χ : MulChar A F`），并证：

    * `smul_regMono`：作用在单项式上 = 平移指标（`g • e_a = e_{ga}`）；
    * `smul_dftVec`：**特征向量性** `g • y_χ = (χ g) • y_χ`；
    * `sum_mulChar_eq_zero`：**特征正交性**（`a ≠ 1` 时字符群求和为 `0`）；
    * `sum_smul_dftVec`：**逆 DFT** `∑ χ, (χ a) • y_χ = |A| • single e_a 1`。

  逆 DFT ⟹ `{y_χ}` 张成；特征向量性 ⟹ `A` 在其上**同时对角化**。

  **⚠ 结构性注记（本轮踩到，防复踩）**：`A` 在自身上的**左乘不是 `A` 的幺半群自同构**
  （`a*(bc) ≠ (ab)(ac)`），故作用**不能**走 `MonoidAlgebra F A` 上的 `mapDomain`；
  它**是格 `Z[A]` 的加法自同构**，故正确载体是 `latticeAlgebra F (A → ℤ)`（D1 框架），
  作用经 `mulEquivOfSMul` ＋ `mapDomain` 给出。

  **⚠ 变量序注记**：本件显式参数序一律 `(F, A, …)`（段内 `variable` 声明序即自动绑定序）。
  **⚠ 系数可为零**：`single x c = single y c` 在 `c = 0` 时**不蕴含** `x = y`，
  故本件一律**重写系数**而不用 `congr` 深入 `single`（D3/D4 前两版各踩一次）。
-/
import ABGV52.D3_ABGV52
import Mathlib.NumberTheory.MulChar.Duality

namespace ABGV52

namespace EM

open scoped Classical

section RegularLattice

variable (A : Type*) [CommGroup A] [Fintype A]

/-- **正则格的左乘作用**：`(g • m) b = m (g⁻¹ * b)`（即把基 `e_a` 送到 `e_{ga}`）。 -/
instance instDistribMulActionRegularLattice : DistribMulAction A (A → ℤ) where
  smul g m := fun b => m (g⁻¹ * b)
  one_smul m := by
    funext b
    show m ((1 : A)⁻¹ * b) = m b
    rw [inv_one, one_mul]
  mul_smul g h m := by
    funext b
    show m ((g * h)⁻¹ * b) = m (h⁻¹ * (g⁻¹ * b))
    rw [mul_inv_rev, mul_assoc]
  smul_zero g := by
    funext b
    show (0 : A → ℤ) (g⁻¹ * b) = 0
    rfl
  smul_add g m n := by
    funext b
    show (m + n) (g⁻¹ * b) = m (g⁻¹ * b) + n (g⁻¹ * b)
    rfl

/-- 正则格作用与 `ℤ`-纯量交换。 -/
instance instSMulCommClassRegularLattice : SMulCommClass A ℤ (A → ℤ) where
  smul_comm g c m := by
    funext b
    show (c • m) (g⁻¹ * b) = c • m (g⁻¹ * b)
    rfl

end RegularLattice

section DFT

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

/-- `F[Z[A]]`：正则置换格的单项式环（＝ `|A|` 个变元的 Laurent 环）。 -/
abbrev regularAlgebra : Type _ := latticeAlgebra F (A → ℤ)

/-- `MulChar A F` 在「足够单位根」假设下有限：经双对偶 `≃* Aˣ` 搬运。 -/
noncomputable instance instFintypeMulChar [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] :
    Fintype (MulChar A F) :=
  Fintype.ofEquiv Aˣ (Classical.choice (MulChar.mulEquiv_units A F)).symm

/-- 单项式 `single e_a c` 的简写。 -/
noncomputable def regMono (a : A) (c : F) : regularAlgebra F A :=
  MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single a 1)) c

/-- 作用在单项式上的**一般形式**：指标经 `mulEquivOfSMul` 平移，系数不动。 -/
lemma smul_single_general (g : A) (m : Multiplicative (A → ℤ)) (c : F) :
    g • MonoidAlgebra.single m c
      = MonoidAlgebra.single (mulEquivOfSMul A (A → ℤ) g m) c := by
  show MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul A (A → ℤ) g)
      (MonoidAlgebra.single m c) = _
  rw [MonoidAlgebra.mapDomainRingEquiv_single]

/-- 左乘作用在基向量上的显式形式：`g • e_a = e_{ga}`。 -/
lemma smul_piSingle (g a : A) : g • (Pi.single a 1 : A → ℤ) = Pi.single (g * a) 1 := by
  funext b
  show (Pi.single a 1 : A → ℤ) (g⁻¹ * b) = (Pi.single (g * a) 1 : A → ℤ) b
  rw [Pi.single_apply, Pi.single_apply]
  by_cases h : b = g * a
  · rw [if_pos h, if_pos (by rw [h, inv_mul_cancel_left])]
  · rw [if_neg h, if_neg (fun hc => h (by rw [← hc, mul_inv_cancel_left]))]

/-- 作用在单项式上：`g • single e_a c = single e_{ga} c`。 -/
lemma smul_regMono (g a : A) (c : F) : g • regMono F A a c = regMono F A (g * a) c := by
  have h : mulEquivOfSMul A (A → ℤ) g (Multiplicative.ofAdd (Pi.single a 1))
      = Multiplicative.ofAdd (Pi.single (g * a) 1) := by
    rw [mulEquivOfSMul_apply]
    show Multiplicative.ofAdd (g • (Pi.single a 1 : A → ℤ))
      = Multiplicative.ofAdd (Pi.single (g * a) 1)
    rw [smul_piSingle]
  rw [regMono, smul_single_general, h, regMono]

/-- 纯量在单项式上：`c • single e_a d = single e_a (c*d)`。 -/
lemma smul_regMono_eq (c : F) (a : A) (d : F) :
    c • regMono F A a d = regMono F A a (c * d) := by
  rw [regMono, Algebra.smul_def, MonoidAlgebra.coe_algebraMap]
  show MonoidAlgebra.single (1 : Multiplicative (A → ℤ)) c
      * MonoidAlgebra.single (Multiplicative.ofAdd (Pi.single a 1)) d = _
  rw [MonoidAlgebra.single_mul_single, one_mul]
  rfl

/-- 单项式族对系数求和可穿过 `single`。 -/
lemma sum_regMono [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] (b : A)
    (f : MulChar A F → F) :
    ∑ χ : MulChar A F, regMono F A b (f χ) = regMono F A b (∑ χ, f χ) := by
  have key : ∀ s : Finset (MulChar A F),
      ∑ χ ∈ s, regMono F A b (f χ) = regMono F A b (∑ χ ∈ s, f χ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, regMono, MonoidAlgebra.single_zero]
    | insert χ s hχ ih =>
        rw [Finset.sum_insert hχ, Finset.sum_insert hχ, ih, regMono, regMono, regMono,
          MonoidAlgebra.single_add]
  exact key Finset.univ

/-- **DFT 向量** `y_χ = ∑ a, single e_a ((χ a)⁻¹)`。 -/
noncomputable def dftVec (χ : MulChar A F) : regularAlgebra F A :=
  ∑ a : A, regMono F A a ((χ a)⁻¹)

/-- **特征向量性**：`g • y_χ = (χ g) • y_χ`。 -/
theorem smul_dftVec (g : A) (χ : MulChar A F) :
    g • dftVec F A χ = (χ g) • dftVec F A χ := by
  have h1 : g • dftVec F A χ = ∑ a : A, regMono F A (g * a) ((χ a)⁻¹) := by
    rw [dftVec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_regMono F A g a ((χ a)⁻¹)
  have h2 : ∑ a : A, regMono F A (g * a) ((χ a)⁻¹)
      = ∑ b : A, regMono F A b ((χ (g⁻¹ * b))⁻¹) := by
    refine Finset.sum_bij (fun a _ => g * a) (fun a _ => Finset.mem_univ _)
      (fun a _ c _ h => mul_left_cancel h)
      (fun b _ => ⟨g⁻¹ * b, Finset.mem_univ _, by group⟩) (fun a _ => ?_)
    rw [show g⁻¹ * (g * a) = a from by group]
  have h3 : (χ g) • dftVec F A χ = ∑ b : A, regMono F A b (χ g * (χ b)⁻¹) := by
    rw [dftVec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_regMono_eq F A (χ g) b ((χ b)⁻¹)
  rw [h1, h2, h3]
  exact Finset.sum_congr rfl fun b _ => by
    rw [show (χ (g⁻¹ * b))⁻¹ = χ g * (χ b)⁻¹ from by
      rw [map_mul, map_inv χ g, mul_inv_rev, inv_inv, mul_comm]]

/-- **特征正交性**：`a ≠ 1` 时 `∑ χ, χ a = 0`。 -/
theorem sum_mulChar_eq_zero [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]
    {a : A} (ha : a ≠ 1) : ∑ χ : MulChar A F, χ a = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity A F ha
  have hre : ∀ χ : MulChar A F, (χ₀ * χ) a = χ₀ a * χ a := fun χ => MulChar.mul_apply _ _ _
  have hbij : ∑ χ : MulChar A F, (χ₀ * χ) a = ∑ χ : MulChar A F, χ a :=
    Fintype.sum_equiv (Equiv.mulLeft χ₀) _ _ (fun χ => by rw [Equiv.coe_mulLeft, hre])
  have h1 : (1 - χ₀ a) * ∑ χ : MulChar A F, χ a = 0 := by
    rw [sub_mul, one_mul, Finset.mul_sum]
    rw [show ∑ χ : MulChar A F, χ₀ a * χ a = ∑ χ : MulChar A F, (χ₀ * χ) a from
      (Finset.sum_congr rfl fun χ _ => (hre χ).symm)]
    rw [hbij, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hχ₀.symm)

/-- **逆 DFT**：`∑ χ, (χ a) • y_χ = |A| • single e_a 1`。 -/
theorem sum_smul_dftVec [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] (a : A) :
    ∑ χ : MulChar A F, (χ a) • dftVec F A χ
      = (Fintype.card A : F) • regMono F A a 1 := by
  have hstep : ∀ χ : MulChar A F,
      (χ a) • dftVec F A χ = ∑ b : A, regMono F A b (χ (a * b⁻¹)) := by
    intro χ
    rw [dftVec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_regMono_eq]
    rw [show χ a * (χ b)⁻¹ = χ (a * b⁻¹) from by rw [map_mul, map_inv]]
  rw [Finset.sum_congr rfl (fun χ _ => hstep χ), Finset.sum_comm]
  have hinner : ∀ b : A, (∑ χ : MulChar A F, regMono F A b (χ (a * b⁻¹)))
      = regMono F A b (∑ χ : MulChar A F, χ (a * b⁻¹)) :=
    fun b => sum_regMono F A b (fun χ => χ (a * b⁻¹))
  have hswap : (∑ b : A, ∑ χ : MulChar A F, regMono F A b (χ (a * b⁻¹)))
      = ∑ b : A, regMono F A b (∑ χ : MulChar A F, χ (a * b⁻¹)) :=
    Finset.sum_congr rfl fun b _ => hinner b
  rw [hswap]
  have hcard : (∑ _χ : MulChar A F, (1 : F)) = (Fintype.card A : F) := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity A F, Nat.card_eq_fintype_card]
    have h1 : Fintype.card Aˣ = Fintype.card A :=
      Fintype.card_congr
        { toFun := fun u => (u : A)
          invFun := fun a => Units.mkOfMulEqOne a a⁻¹ (mul_inv_cancel a)
          left_inv := fun u => Units.ext rfl
          right_inv := fun a => rfl }
    rw [h1, nsmul_eq_mul, mul_one]
  have ha_term : regMono F A a (∑ χ : MulChar A F, χ (a * a⁻¹))
      = (Fintype.card A : F) • regMono F A a 1 := by
    rw [mul_inv_cancel, Finset.sum_congr rfl (fun χ _ => by rw [map_one]), hcard]
    rw [show regMono F A a (Fintype.card A : F)
          = regMono F A a ((Fintype.card A : F) * 1) from by rw [mul_one]]
    rw [← smul_regMono_eq F A (Fintype.card A : F) a 1]
  rw [← ha_term]
  refine Finset.sum_eq_single
    (f := fun b : A => regMono F A b (∑ χ : MulChar A F, χ (a * b⁻¹))) a ?_ ?_
  · intro b _ hb
    rw [show (∑ χ : MulChar A F, χ (a * b⁻¹)) = 0 from
      sum_mulChar_eq_zero F A (fun hc => hb (by
        have h := congrArg (· * b) hc
        rw [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h
        exact h.symm))]
    rw [regMono, MonoidAlgebra.single_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

end DFT

/-! ## 公理闸门 -/

#print axioms instDistribMulActionRegularLattice
#print axioms instSMulCommClassRegularLattice
#print axioms smul_single_general
#print axioms smul_piSingle
#print axioms smul_regMono
#print axioms smul_regMono_eq
#print axioms sum_regMono
#print axioms dftVec
#print axioms smul_dftVec
#print axioms sum_mulChar_eq_zero
#print axioms sum_smul_dftVec

end EM

end ABGV52
