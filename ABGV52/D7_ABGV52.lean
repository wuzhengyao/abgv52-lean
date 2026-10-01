/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-iv：对角模型 ＋ DFT 变元代换（③ 的第 1、2 段）**

  目标（用户 2026-09-30 口径）：落地 ③ 度数收口的两段前置。

  **第 1 段 · 对角模型** `diagAlgebra F A := MonoidAlgebra F (Multiplicative (MulChar A F →₀ ℤ))`
  （即 `F[z_χ^{±}]`，基单项式 `z^m = ∏_χ z_χ^{m_χ}`）。其上的 **`A`-作用是对角的**
  `z_χ ↦ χ(g) · z_χ` —— **不是格作用**（对角作用不移动指数而乘系数，
  D1 的 `MulSemiringAction` 由格 `M` 的加法作用诱导，此处**对不上**）⟹ **手建**
  `diagMonoidHom`／`diagAlgHom`／`diagRingEquiv`／`diagActionHom`（样板同 D1 的 `latticeAlgebraActionHom`）。
  关键引理 **`smul_zMono`**：`g • z^m = (charOf m g) • z^m`（**特征向量性**，`charOf` 承 D6）
  ⟹ `z^m` 是 `A`-不变 **iff** `m ∈ Y`（`zMono_mem_invariants_iff`）。

  **⚠ 本轮新增假设** `[NeZero (Fintype.card A : F)]`（＝ `|A| ≠ 0` in `F`）：
  第 2 段的变元代换需要它（`|A|` 可逆 ⟺ DFT 矩阵可逆；`char F ∣ |A|` 时
  `∑_χ χ(a) y_χ = |A| x_a = 0` 使 `y_χ` 线性相关，代换**不**单射）。
  本件同时给出 **`neZero_card_cast_of_hasEnoughRootsOfUnity`**：该假设由 D4–D6 已用的
  `[HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]` **推出**（Cauchy ＋ 对偶 ＋ Frobenius），
  故不削弱既有陈述的射程。
-/
import ABGV52.D6_ABGV52
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

/-! ## 1. `|A| ≠ 0` in `F`（由「足够单位根」推出） -/

section NeZero

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

/-- `A ≃* Aˣ`（群与其单位群）。 -/
noncomputable def unitsMulEquivSelf : A ≃* Aˣ where
  toFun a := ⟨a, a⁻¹, mul_inv_cancel a, inv_mul_cancel a⟩
  invFun u := u
  left_inv a := rfl
  right_inv u := Units.ext rfl
  map_mul' a b := Units.ext rfl

/-- **`NeZero (Fintype.card A : F)`**：足够单位根 ⟹ `char F ∤ |A|`。

论证：`(|A| : F) = 0` ⟹ `p := ringChar F ∣ |A|`（`ringChar.spec`），且 `p ≠ 0`（否则 `|A| = 0`）。
Cauchy 给阶 `p` 的 `a ∈ A`（故 `a ≠ 1`、`a^p = 1`）；对偶（`exists_apply_ne_one_...`）给
`χ` 使 `χ a ≠ 1`，于是 `(χ a)^p = χ (a^p) = 1`；
但 `char F = p` 时 `(χ a - 1)^p = (χ a)^p - 1 = 0` ⟹ `χ a = 1`，矛盾。 -/
theorem neZero_card_cast_of_hasEnoughRootsOfUnity
    [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] :
    NeZero (Fintype.card A : F) := by
  rw [neZero_iff]
  intro hzero
  have hdvd : ringChar F ∣ Fintype.card A := (ringChar.spec F (Fintype.card A)).mp hzero
  have hp0 : ringChar F ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) Fintype.card_ne_zero
  have hpprime : Nat.Prime (ringChar F) := CharP.char_prime_of_ne_zero F hp0
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hpprime⟩
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (ringChar F) hdvd
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact hpprime.ne_one ha.symm
  have hap : a ^ ringChar F = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity A F ha1
  have hχp : (χ a) ^ ringChar F = 1 := by rw [← map_pow, hap, map_one]
  have hsub : (χ a - 1) ^ ringChar F = 0 := by
    rw [sub_pow_char (χ a) 1, hχp, one_pow, sub_self]
  exact hχ (sub_eq_zero.mp ((pow_eq_zero_iff hpprime.ne_zero).mp hsub))

/-- `|A| ≠ 0` in `F` **作为实例**（由单位根假设自动综合，供 `dftInvPoly` 一类使用）。 -/
instance instNeZeroCardCast [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] :
    NeZero (Fintype.card A : F) :=
  neZero_card_cast_of_hasEnoughRootsOfUnity F A

end NeZero

/-! ## 2. 对角模型 `F[z_χ^{±}]` 与其对角 `A`-作用 -/

section DiagModel

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **对角模型** `F[z_χ^{±}]`：以特征群为指数的 Laurent 单项式环。 -/
abbrev diagAlgebra : Type _ := MonoidAlgebra F (Multiplicative (MulChar A F →₀ ℤ))

/-- 基单项式 `z^m = ∏_χ z_χ^{m_χ}`。 -/
noncomputable def zMono (m : MulChar A F →₀ ℤ) : diagAlgebra F A :=
  MonoidAlgebra.single (Multiplicative.ofAdd m) 1

lemma zMono_zero : zMono F A 0 = 1 := by
  rw [zMono, show Multiplicative.ofAdd (0 : MulChar A F →₀ ℤ) = 1 from rfl,
    ← MonoidAlgebra.of_apply, map_one]

lemma zMono_add (m m' : MulChar A F →₀ ℤ) :
    zMono F A (m + m') = zMono F A m * zMono F A m' := by
  rw [zMono, zMono, zMono, ofAdd_add, MonoidAlgebra.single_mul_single, mul_one]

/-- 单项式与纯量的关系：`single (ofAdd m) c = c • z^m`。 -/
lemma single_eq_smul_zMono (m : MulChar A F →₀ ℤ) (c : F) :
    MonoidAlgebra.single (Multiplicative.ofAdd m) c = c • zMono F A m := by
  rw [zMono, Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    MonoidAlgebra.single_mul_single]
  simp

/-- `charOf` 的加性取值（对角作用的乘法律用）。 -/
lemma charOf_apply_add (n m : expVector F A) (g : A) :
    charOf F A (n + m) g = charOf F A n g * charOf F A m g := by
  rw [charOf_add, MulChar.mul_apply]

/-- **对角作用的单项式层公式** `z^m ↦ charOf(m)(g) · z^m`（作为乘法幺半群同态）。 -/
noncomputable def diagMonoidHom (g : A) :
    Multiplicative (MulChar A F →₀ ℤ) →* diagAlgebra F A where
  toFun n := algebraMap F (diagAlgebra F A) (charOf F A n.toAdd g) * zMono F A n.toAdd
  map_one' := by
    show algebraMap F (diagAlgebra F A) (charOf F A (1 : Multiplicative _).toAdd g)
      * zMono F A (1 : Multiplicative _).toAdd = 1
    rw [show (1 : Multiplicative (MulChar A F →₀ ℤ)).toAdd = 0 from rfl, charOf_zero,
      MulChar.one_apply (Group.isUnit g), map_one, zMono_zero, mul_one]
  map_mul' n m := by
    show algebraMap F (diagAlgebra F A) (charOf F A (n * m).toAdd g) * zMono F A (n * m).toAdd
      = (algebraMap F (diagAlgebra F A) (charOf F A n.toAdd g) * zMono F A n.toAdd)
        * (algebraMap F (diagAlgebra F A) (charOf F A m.toAdd g) * zMono F A m.toAdd)
    rw [show (n * m).toAdd = n.toAdd + m.toAdd from rfl, charOf_apply_add, zMono_add,
      map_mul (algebraMap F (diagAlgebra F A))]
    ring

lemma diagMonoidHom_apply (g : A) (n : Multiplicative (MulChar A F →₀ ℤ)) :
    diagMonoidHom F A g n
      = algebraMap F (diagAlgebra F A) (charOf F A n.toAdd g) * zMono F A n.toAdd := rfl

/-- 对角作用在单项式上的显式式（`c = 1` 的情形由 `smul_zMono` 给）。 -/
lemma diagAlgHom_single (g : A) (m : MulChar A F →₀ ℤ) (c : F) :
    (MonoidAlgebra.lift F (diagAlgebra F A) (Multiplicative (MulChar A F →₀ ℤ))
        (diagMonoidHom F A g)) (MonoidAlgebra.single (Multiplicative.ofAdd m) c)
      = algebraMap F (diagAlgebra F A) (charOf F A m g) * MonoidAlgebra.single
          (Multiplicative.ofAdd m) c := by
  rw [MonoidAlgebra.lift_single, diagMonoidHom_apply, single_eq_smul_zMono, mul_smul_comm]
  rfl

/-- 对角作用作为 `F`-代数自同态。 -/
noncomputable def diagAlgHom (g : A) : diagAlgebra F A →ₐ[F] diagAlgebra F A :=
  MonoidAlgebra.lift F (diagAlgebra F A) (Multiplicative (MulChar A F →₀ ℤ))
    (diagMonoidHom F A g)

lemma diagAlgHom_apply_single (g : A) (m : MulChar A F →₀ ℤ) (c : F) :
    diagAlgHom F A g (MonoidAlgebra.single (Multiplicative.ofAdd m) c)
      = algebraMap F (diagAlgebra F A) (charOf F A m g) * MonoidAlgebra.single
          (Multiplicative.ofAdd m) c :=
  diagAlgHom_single F A g m c

lemma diagAlgHom_apply_single' (g : A) (m : Multiplicative (MulChar A F →₀ ℤ)) (c : F) :
    diagAlgHom F A g (MonoidAlgebra.single m c)
      = algebraMap F (diagAlgebra F A) (charOf F A m.toAdd g) * MonoidAlgebra.single m c :=
  diagAlgHom_single F A g m.toAdd c

/-- 对角作用在「纯量 × 单项式」上的显式式（复合律的收口引理）。 -/
lemma diagAlgHom_apply_smul_single (g : A) (a : F) (m : MulChar A F →₀ ℤ) :
    diagAlgHom F A g (algebraMap F (diagAlgebra F A) a
        * MonoidAlgebra.single (Multiplicative.ofAdd m) 1)
      = algebraMap F (diagAlgebra F A) (a * charOf F A m g)
        * MonoidAlgebra.single (Multiplicative.ofAdd m) 1 := by
  rw [map_mul, AlgHom.commutes, diagAlgHom_apply_single, ← mul_assoc, ← map_mul]

lemma diagAlgHom_inv_comp (g : A) :
    (diagAlgHom F A g⁻¹).comp (diagAlgHom F A g) = AlgHom.id F (diagAlgebra F A) := by
  refine AlgHom.ext fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      show (diagAlgHom F A g⁻¹) ((diagAlgHom F A g)
        (MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1))
        = MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1
      rw [diagAlgHom_apply_single, diagAlgHom_apply_smul_single,
        ← map_mul (charOf F A m.toAdd) g g⁻¹, mul_inv_cancel, map_one, map_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul r x hx => rw [map_smul, map_smul, hx]

lemma diagAlgHom_comp_inv (g : A) :
    (diagAlgHom F A g).comp (diagAlgHom F A g⁻¹) = AlgHom.id F (diagAlgebra F A) := by
  refine AlgHom.ext fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      show (diagAlgHom F A g) ((diagAlgHom F A g⁻¹)
        (MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1))
        = MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1
      rw [diagAlgHom_apply_single, diagAlgHom_apply_smul_single,
        ← map_mul (charOf F A m.toAdd) g⁻¹ g, inv_mul_cancel, map_one, map_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul r x hx => rw [map_smul, map_smul, hx]

/-- **对角自同构** `z_χ ↦ χ(g) · z_χ`（`g⁻¹` 给出逆）。 -/
noncomputable def diagAlgEquiv (g : A) : diagAlgebra F A ≃ₐ[F] diagAlgebra F A where
  toFun := diagAlgHom F A g
  invFun := diagAlgHom F A g⁻¹
  left_inv x := by
    have h := congrArg (fun f : diagAlgebra F A →ₐ[F] diagAlgebra F A => f x)
      (diagAlgHom_inv_comp F A g)
    simpa using h
  right_inv x := by
    have h := congrArg (fun f : diagAlgebra F A →ₐ[F] diagAlgebra F A => f x)
      (diagAlgHom_comp_inv F A g)
    simpa using h
  map_mul' := map_mul (diagAlgHom F A g)
  map_add' := map_add (diagAlgHom F A g)
  commutes' := AlgHom.commutes (diagAlgHom F A g)

/-- `diagAlgEquiv` 在单项式上的取值（＝ `diagAlgHom`）。 -/
lemma diagAlgEquiv_apply_single (g : A) (m : MulChar A F →₀ ℤ) (c : F) :
    diagAlgEquiv F A g (MonoidAlgebra.single (Multiplicative.ofAdd m) c)
      = algebraMap F (diagAlgebra F A) (charOf F A m g) * MonoidAlgebra.single
          (Multiplicative.ofAdd m) c :=
  diagAlgHom_apply_single F A g m c

/-- **对角 `A`-作用**：`z_χ ↦ χ(g) · z_χ`（手建，非格作用）。 -/
noncomputable instance instMulSemiringActionDiag : MulSemiringAction A (diagAlgebra F A) where
  smul g x := diagAlgEquiv F A g x
  one_smul x := by
    show diagAlgHom F A 1 x = x
    induction x using MonoidAlgebra.induction_on with
    | of m =>
        show diagAlgHom F A 1 (MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1)
          = MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1
        rw [diagAlgHom_apply_single, map_one (charOf F A m.toAdd),
          map_one (algebraMap F (diagAlgebra F A)), one_mul]
    | add x y hx hy => rw [map_add, hx, hy]
    | smul r x hx => rw [map_smul, hx]
  mul_smul g h x := by
    show diagAlgHom F A (g * h) x = diagAlgHom F A g (diagAlgHom F A h x)
    induction x using MonoidAlgebra.induction_on with
    | of m =>
        show diagAlgHom F A (g * h) (MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1)
          = diagAlgHom F A g (diagAlgHom F A h
              (MonoidAlgebra.single (Multiplicative.ofAdd m.toAdd) 1))
        rw [diagAlgHom_apply_single, diagAlgHom_apply_single, diagAlgHom_apply_smul_single,
          map_mul]
        ring
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | smul r x hx => rw [map_smul, map_smul, map_smul, hx]
  smul_zero g := map_zero (diagAlgEquiv F A g)
  smul_add g x y := map_add (diagAlgEquiv F A g) x y
  smul_one g := map_one (diagAlgEquiv F A g)
  smul_mul g x y := map_mul (diagAlgEquiv F A g) x y

/-- 对角作用固定 `F`-纯量 ⟹ `SMulCommClass A F`。 -/
instance instSMulCommClassDiag : SMulCommClass A F (diagAlgebra F A) where
  smul_comm g c x := by
    show diagAlgEquiv F A g (c • x) = c • diagAlgEquiv F A g x
    rw [map_smul]

/-- **`smul_zMono`（特征向量性）**：`g • z^m = (charOf m g) • z^m`。 -/
theorem smul_zMono (g : A) (m : MulChar A F →₀ ℤ) :
    g • zMono F A m = (charOf F A m g) • zMono F A m := by
  show diagAlgHom F A g (MonoidAlgebra.single (Multiplicative.ofAdd m) 1)
    = (charOf F A m g) • zMono F A m
  rw [diagAlgHom_apply_single, Algebra.smul_def, MonoidAlgebra.coe_algebraMap,
    Function.comp_apply, show algebraMap F F (charOf F A m g) = charOf F A m g from rfl, zMono]

/-- **不变性判据**：`z^m` 被 `g` 固定 **iff** `charOf m g = 1`。 -/
theorem smul_zMono_eq_iff (g : A) (m : MulChar A F →₀ ℤ) :
    g • zMono F A m = zMono F A m ↔ charOf F A m g = 1 := by
  rw [smul_zMono, ← single_eq_smul_zMono F A m, zMono, MonoidAlgebra.single_right_inj]

/-- **`z^m` 是 `A`-不变 iff `m ∈ Y`**（`Y = kernelLattice`，D5）。 -/
theorem zMono_mem_invariants_iff (m : MulChar A F →₀ ℤ) :
    (∀ g : A, g • zMono F A m = zMono F A m) ↔ m ∈ kernelLattice F A := by
  constructor
  · intro h
    by_contra hY
    have hne : charOf F A m ≠ 1 := fun hc => hY hc
    obtain ⟨g, hg⟩ : ∃ g : A, charOf F A m g ≠ 1 := by
      by_contra h
      exact hne (MulChar.ext fun a => by simpa using not_not.mp (not_exists.mp h a))
    exact hg ((smul_zMono_eq_iff F A g m).mp (h g))
  · intro hY g
    exact (smul_zMono_eq_iff F A g m).mpr (by rw [show charOf F A m = 1 from hY,
      MulChar.one_apply (Group.isUnit g)])

/-- **不变性（单项式层）**：`m ∈ Y ⟹ z^m` 是 `A`-不变。 -/
theorem zMono_mem_invariants {m : MulChar A F →₀ ℤ} (h : m ∈ kernelLattice F A) :
    ∀ g : A, g • zMono F A m = zMono F A m :=
  (zMono_mem_invariants_iff F A m).mpr h

end DiagModel

/-\! ## 3. DFT 变元代换（多项式层）与 `dftSubst` -/

section DFTSubst

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- 指数嵌入 `A →₀ ℕ ↪ A → ℤ`（D2 `freeEmb` 的一般化）。 -/
noncomputable def finsuppEmb : (A →₀ ℕ) →+ (A → ℤ) where
  toFun s := fun a => (s a : ℤ)
  map_zero' := by ext a; simp
  map_add' s t := by ext a; simp [Finsupp.add_apply, Nat.cast_add]

@[simp] lemma finsuppEmb_apply (s : A →₀ ℕ) (a : A) : finsuppEmb (A := A) s a = (s a : ℤ) := rfl

lemma finsuppEmb_injective : Function.Injective (finsuppEmb (A := A)) := by
  intro s t h
  ext a
  exact Int.ofNat_inj.mp (congrFun h a)

lemma finsuppEmb_single (a : A) :
    finsuppEmb (A := A) (Finsupp.single a 1) = Pi.single a (1 : ℤ) := by
  ext b
  rw [finsuppEmb_apply, Finsupp.single_apply, Pi.single_apply]
  by_cases h : b = a
  · simp [h]
  · simp [h, Ne.symm h]

/-- **多项式环 → Laurent 环**：`X_a ↦ x_a`（D2 `freeSubst` 的一般化）。 -/
noncomputable def polySubst : MvPolynomial A F →ₐ[F] latticeAlgebra F (A → ℤ) :=
  (MonoidAlgebra.mapDomainAlgHom F F (finsuppEmb (A := A)).toMultiplicative).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (A →₀ ℕ)).toAlgHom

lemma polySubst_apply (p : MvPolynomial A F) :
    polySubst F A p = MonoidAlgebra.mapDomain (⇑(finsuppEmb (A := A)).toMultiplicative)
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (A →₀ ℕ) p) := rfl

theorem polySubst_injective : Function.Injective (polySubst F A) :=
  (MonoidAlgebra.mapDomain_injective (R := F) (finsuppEmb_injective (A := A))).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (A →₀ ℕ)).injective

lemma polySubst_monomial (s : A →₀ ℕ) (c : F) :
    polySubst F A (MvPolynomial.monomial s c)
      = MonoidAlgebra.single (Multiplicative.ofAdd (finsuppEmb (A := A) s)) c := by
  rw [polySubst_apply, (MvPolynomial.single_eq_monomial s c).symm,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.mapDomain_single,
    AddMonoidHom.toMultiplicative_apply_apply]
  simp

lemma polySubst_X (a : A) : polySubst F A (MvPolynomial.X a) = regMono F A a 1 := by
  rw [MvPolynomial.X, polySubst_monomial, finsuppEmb_single]
  rfl

/-- `F[M] → F(M)`（局部化嵌入，作为 `F`-代数同态）。 -/
noncomputable def algToFF : latticeAlgebra F (A → ℤ) →ₐ[F] latticeFunctionField F (A → ℤ) where
  toFun := algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ))
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := (IsScalarTower.algebraMap_apply F (latticeAlgebra F (A → ℤ))
    (latticeFunctionField F (A → ℤ)) r).symm

/-- **多项式环 → 函数域**：`X_a ↦ x_a`。 -/
noncomputable def polyToFF : MvPolynomial A F →ₐ[F] latticeFunctionField F (A → ℤ) :=
  (algToFF F A).comp (polySubst F A)

lemma polyToFF_apply (p : MvPolynomial A F) :
    polyToFF F A p = algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ))
      (polySubst F A p) := rfl

theorem polyToFF_injective : Function.Injective (polyToFF F A) := by
  intro p q h
  rw [polyToFF_apply, polyToFF_apply] at h
  exact polySubst_injective F A
    (IsFractionRing.injective (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ)) h)

/-- **DFT 代换（多项式层）**：`X_χ ↦ ∑_a (χ a)⁻¹ X_a`（D4 `dftVec` 的多项式版）。 -/
noncomputable def dftSubstPoly : MvPolynomial (MulChar A F) F →ₐ[F] MvPolynomial A F :=
  MvPolynomial.aeval fun χ => ∑ a : A, MvPolynomial.C ((χ a)⁻¹) * MvPolynomial.X a

lemma dftSubstPoly_X (χ : MulChar A F) :
    dftSubstPoly F A (MvPolynomial.X χ)
      = ∑ a : A, MvPolynomial.C ((χ a)⁻¹) * MvPolynomial.X a :=
  MvPolynomial.aeval_X _ χ

/-- **反向线性代换**：`X_a ↦ |A|⁻¹ ∑_χ χ(a) X_χ`。 -/
noncomputable def dftInvPoly : MvPolynomial A F →ₐ[F] MvPolynomial (MulChar A F) F :=
  MvPolynomial.aeval fun a =>
    (Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F,
      MvPolynomial.C (χ a) * MvPolynomial.X χ

/-- 特征正交性（群求和版）：`∑_a χ a = |A|`（`χ = 1`）或 `0`（否则）。 -/
theorem sum_mulChar_eq_ite (χ : MulChar A F) :
    ∑ a : A, χ a = if χ = 1 then (Fintype.card A : F) else 0 := by
  by_cases h : χ = 1
  · subst h
    rw [if_pos rfl, Finset.sum_congr rfl fun a _ => MulChar.one_apply (Group.isUnit a),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]

lemma dftInvPoly_C (r : F) :
    dftInvPoly F A (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.aeval_C _ r

lemma dftInvPoly_X (a : A) :
    dftInvPoly F A (MvPolynomial.X a)
      = (Fintype.card A : F)⁻¹ • ∑ χ : MulChar A F,
          MvPolynomial.C (χ a) * MvPolynomial.X χ :=
  MvPolynomial.aeval_X _ a

/-- **DFT 复合恒等（正向·逐生成元）**：`dftInvPoly (dftSubstPoly (X χ)) = X χ`。
「先 DFT 代换再反向线性代换」在生成元上还原 —— **特征正交性**（`∑_a (ψχ⁻¹)(a) = |A|δ`）
是全部内容。 -/
lemma dftInvPoly_dftSubstPoly_X (χ : MulChar A F) :
    dftInvPoly F A (dftSubstPoly F A (MvPolynomial.X χ)) = MvPolynomial.X χ := by
  haveI := neZero_card_cast_of_hasEnoughRootsOfUnity F A
  rw [dftSubstPoly_X]
  have h1 : dftInvPoly F A (∑ a : A, MvPolynomial.C ((χ a)⁻¹) * MvPolynomial.X a)
      = ∑ a : A, MvPolynomial.C ((χ a)⁻¹) *
          ((Fintype.card A : F)⁻¹ • ∑ ψ : MulChar A F,
            MvPolynomial.C (ψ a) * MvPolynomial.X ψ) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_mul, dftInvPoly_C, dftInvPoly_X]
  rw [h1]
  have h2 : ∀ a : A, MvPolynomial.C ((χ a)⁻¹) *
        ((Fintype.card A : F)⁻¹ • ∑ ψ : MulChar A F,
          MvPolynomial.C (ψ a) * MvPolynomial.X ψ)
      = ∑ ψ : MulChar A F,
          MvPolynomial.C ((Fintype.card A : F)⁻¹ * ((χ a)⁻¹ * ψ a)) *
            MvPolynomial.X ψ := by
    intro a
    rw [Algebra.smul_def, MvPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun ψ _ => by
      rw [map_mul, map_mul, map_mul]
      ring
  rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
  have h3 : ∀ ψ : MulChar A F,
      ∑ a : A, MvPolynomial.C ((Fintype.card A : F)⁻¹ * ((χ a)⁻¹ * ψ a)) *
          MvPolynomial.X ψ
        = MvPolynomial.C (if ψ = χ then 1 else 0) * MvPolynomial.X ψ := by
    intro ψ
    rw [← Finset.sum_mul, ← map_sum]
    have hC : (∑ a : A, (Fintype.card A : F)⁻¹ * ((χ a)⁻¹ * ψ a))
        = (if ψ = χ then 1 else 0) := by
      have hχψ : ∀ a : A, (Fintype.card A : F)⁻¹ * ((χ a)⁻¹ * ψ a)
          = (Fintype.card A : F)⁻¹ * (ψ * χ⁻¹) a := by
        intro a
        rw [MulChar.mul_apply, mulChar_inv_apply]
        ring
      rw [Finset.sum_congr rfl fun a _ => hχψ a, ← Finset.mul_sum, sum_mulChar_eq_ite]
      by_cases h : ψ = χ
      · rw [if_pos h, if_pos (by rw [h, mul_inv_cancel]), inv_mul_cancel₀ (NeZero.ne _)]
      · rw [if_neg h, if_neg (fun hc => h (mul_inv_eq_one.mp hc)), mul_zero]
    rw [hC]
  rw [Finset.sum_congr rfl fun ψ _ => h3 ψ,
    Finset.sum_eq_single χ (fun ψ _ hψ => by rw [if_neg hψ, MvPolynomial.C_0, zero_mul])
      (fun h => absurd (Finset.mem_univ χ) h)]
  simp

/-- **复合恒等（正向）**：`dftInvPoly ∘ dftSubstPoly = id`。 -/
theorem dftInvPoly_comp_dftSubstPoly :
    (dftInvPoly F A).comp (dftSubstPoly F A)
      = AlgHom.id F (MvPolynomial (MulChar A F) F) :=
  MvPolynomial.algHom_ext fun χ => dftInvPoly_dftSubstPoly_X F A χ

/-- **DFT 代换单射**：＝ `y_χ := ∑_a (χ a)⁻¹ x_a` 的**代数无关性**（变元代换的实质）。 -/
theorem dftSubstPoly_injective : Function.Injective (dftSubstPoly F A) :=
  Function.LeftInverse.injective fun p => by
    have h := AlgHom.congr_fun (dftInvPoly_comp_dftSubstPoly F A) p
    simpa using h

/-- **DFT 代换（入函数域 `F(M)`）**：`X_χ ↦ y_χ`。 -/
noncomputable def dftSubst : MvPolynomial (MulChar A F) F →ₐ[F] latticeFunctionField F (A → ℤ) :=
  (polyToFF F A).comp (dftSubstPoly F A)

lemma dftSubst_X (χ : MulChar A F) : dftSubst F A (MvPolynomial.X χ) = dftVecFF F A χ := by
  show polyToFF F A (dftSubstPoly F A (MvPolynomial.X χ)) = dftVecFF F A χ
  rw [dftSubstPoly_X, map_sum, dftVecFF, dftVec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show MvPolynomial.C ((χ a)⁻¹) * MvPolynomial.X a = ((χ a)⁻¹) • MvPolynomial.X a from by
        rw [Algebra.smul_def, MvPolynomial.C_eq_algebraMap]]
  rw [map_smul, polyToFF_apply, polySubst_X, ← algebraMap_smul_regular]
  congr 1
  simpa using smul_regMono_eq F A ((χ a)⁻¹) a 1

theorem dftSubst_injective : Function.Injective (dftSubst F A) :=
  (polyToFF_injective F A).comp (dftSubstPoly_injective F A)

end DFTSubst

/-\! ## 4. 源侧对角作用与 `dftSubst` 的等变性 -/

section Equivariance

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- `MvPolynomial` 上的**对角作用**：`X_χ ↦ χ(g) · X_χ`。 -/
noncomputable def diagMPolyHom (g : A) :
    MvPolynomial (MulChar A F) F →ₐ[F] MvPolynomial (MulChar A F) F :=
  MvPolynomial.aeval fun χ => MvPolynomial.C (χ g) * MvPolynomial.X χ

lemma diagMPolyHom_X (g : A) (χ : MulChar A F) :
    diagMPolyHom F A g (MvPolynomial.X χ) = MvPolynomial.C (χ g) * MvPolynomial.X χ :=
  MvPolynomial.aeval_X _ χ

lemma diagMPolyHom_C (g : A) (c : F) :
    diagMPolyHom F A g (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes, ← MvPolynomial.C_eq_algebraMap]

/-- 逆代换：`X_χ ↦ (χ g)⁻¹ · X_χ`。 -/
noncomputable def diagMPolyHomInv (g : A) :
    MvPolynomial (MulChar A F) F →ₐ[F] MvPolynomial (MulChar A F) F :=
  MvPolynomial.aeval fun χ => MvPolynomial.C ((χ g)⁻¹) * MvPolynomial.X χ

lemma diagMPolyHomInv_X (g : A) (χ : MulChar A F) :
    diagMPolyHomInv F A g (MvPolynomial.X χ)
      = MvPolynomial.C ((χ g)⁻¹) * MvPolynomial.X χ :=
  MvPolynomial.aeval_X _ χ

lemma diagMPolyHomInv_C (g : A) (c : F) :
    diagMPolyHomInv F A g (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes, ← MvPolynomial.C_eq_algebraMap]

lemma diagMPolyHom_comp_inv (g : A) :
    (diagMPolyHom F A g).comp (diagMPolyHomInv F A g)
      = AlgHom.id F (MvPolynomial (MulChar A F) F) := by
  refine MvPolynomial.algHom_ext fun χ => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply, diagMPolyHomInv_X, map_mul, diagMPolyHom_C,
    diagMPolyHom_X, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (mulChar_apply_ne_zero F A χ g),
    map_one, one_mul]

lemma diagMPolyHom_inv_comp (g : A) :
    (diagMPolyHomInv F A g).comp (diagMPolyHom F A g)
      = AlgHom.id F (MvPolynomial (MulChar A F) F) := by
  refine MvPolynomial.algHom_ext fun χ => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply, diagMPolyHom_X, map_mul, diagMPolyHomInv_C,
    diagMPolyHomInv_X, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (mulChar_apply_ne_zero F A χ g), map_one, one_mul]

/-- 对角的 `F`-代数自同构 `X_χ ↦ χ(g)·X_χ`。 -/
noncomputable def diagMPolyEquiv (g : A) :
    MvPolynomial (MulChar A F) F ≃ₐ[F] MvPolynomial (MulChar A F) F where
  toFun := diagMPolyHom F A g
  invFun := diagMPolyHomInv F A g
  left_inv x := by
    have h := AlgHom.congr_fun (diagMPolyHom_inv_comp F A g) x
    simpa using h
  right_inv x := by
    have h := AlgHom.congr_fun (diagMPolyHom_comp_inv F A g) x
    simpa using h
  map_mul' := map_mul (diagMPolyHom F A g)
  map_add' := map_add (diagMPolyHom F A g)
  commutes' := AlgHom.commutes (diagMPolyHom F A g)

/-- 源侧对角作用（手建，同 D1 的样板）。 -/
noncomputable instance instMulSemiringActionMPoly :
    MulSemiringAction A (MvPolynomial (MulChar A F) F) where
  smul g p := diagMPolyEquiv F A g p
  one_smul x := by
    show diagMPolyHom F A 1 x = x
    have halg : diagMPolyHom F A 1 = AlgHom.id F (MvPolynomial (MulChar A F) F) := by
      refine MvPolynomial.algHom_ext fun χ => ?_
      rw [AlgHom.id_apply, diagMPolyHom_X, show χ (1 : A) = 1 from map_one χ,
        MvPolynomial.C_1, one_mul]
    rw [halg, AlgHom.id_apply]
  mul_smul g h x := by
    show diagMPolyHom F A (g * h) x = diagMPolyHom F A g (diagMPolyHom F A h x)
    have halg : diagMPolyHom F A (g * h)
        = (diagMPolyHom F A g).comp (diagMPolyHom F A h) := by
      refine MvPolynomial.algHom_ext fun χ => ?_
      simp only [AlgHom.comp_apply, diagMPolyHom_X, diagMPolyHom_C, map_mul]
      ring
    rw [halg, AlgHom.comp_apply]
  smul_zero g := map_zero (diagMPolyHom F A g)
  smul_add g x y := map_add (diagMPolyHom F A g) x y
  smul_one g := map_one (diagMPolyHom F A g)
  smul_mul g x y := map_mul (diagMPolyHom F A g) x y

/-- 对角作用固定 `F`-纯量 ⟹ `SMulCommClass`。 -/
instance instSMulCommClassMPoly : SMulCommClass A F (MvPolynomial (MulChar A F) F) where
  smul_comm g c x := by
    show diagMPolyEquiv F A g (c • x) = c • diagMPolyEquiv F A g x
    rw [map_smul]

/-- **等变性**：`dftSubst (g • p) = g • dftSubst p`（生成元上由 D6 的 `smul_dftVecFF` 给）。 -/
theorem dftSubst_smul (g : A) (p : MvPolynomial (MulChar A F) F) :
    dftSubst F A (g • p) = g • dftSubst F A p := by
  have hgen : ∀ χ : MulChar A F,
      dftSubst F A (g • MvPolynomial.X χ) = g • dftSubst F A (MvPolynomial.X χ) := by
    intro χ
    show dftSubst F A (diagMPolyHom F A g (MvPolynomial.X χ))
      = g • dftSubst F A (MvPolynomial.X χ)
    rw [diagMPolyHom_X, map_mul,
      show dftSubst F A (MvPolynomial.C (χ g))
        = algebraMap F (latticeFunctionField F (A → ℤ)) (χ g) from
        AlgHom.commutes (dftSubst F A) (χ g),
      dftSubst_X, ← Algebra.smul_def]
    exact (smul_dftVecFF F A g χ).symm
  induction p using MvPolynomial.induction_on with
  | C a =>
      show dftSubst F A (diagMPolyHom F A g (MvPolynomial.C a))
        = g • dftSubst F A (MvPolynomial.C a)
      rw [diagMPolyHom_C,
        show dftSubst F A (MvPolynomial.C a)
          = algebraMap F (latticeFunctionField F (A → ℤ)) a from
          AlgHom.commutes (dftSubst F A) a,
        smul_algebraMap_latticeFunctionField F A (A → ℤ) g a]
  | add p q hp hq =>
      rw [show g • (p + q) = g • p + g • q from map_add (diagMPolyEquiv F A g) p q,
        show dftSubst F A (p + q) = dftSubst F A p + dftSubst F A q from
          map_add (dftSubst F A) p q,
        show dftSubst F A (g • p + g • q) = dftSubst F A (g • p) + dftSubst F A (g • q) from
          map_add (dftSubst F A) (g • p) (g • q),
        show g • (dftSubst F A p + dftSubst F A q)
            = g • dftSubst F A p + g • dftSubst F A q from
          (MulSemiringAction.toRingEquiv A (latticeFunctionField F (A → ℤ)) g).map_add
            (dftSubst F A p) (dftSubst F A q),
        hp, hq]
  | mul_X p χ hp =>
      rw [show g • (p * MvPolynomial.X χ) = (g • p) * (g • MvPolynomial.X χ) from
            map_mul (diagMPolyEquiv F A g) p (MvPolynomial.X χ),
        show dftSubst F A (p * MvPolynomial.X χ)
            = dftSubst F A p * dftSubst F A (MvPolynomial.X χ) from
          map_mul (dftSubst F A) p (MvPolynomial.X χ),
        show dftSubst F A (g • p * g • MvPolynomial.X χ)
            = dftSubst F A (g • p) * dftSubst F A (g • MvPolynomial.X χ) from
          map_mul (dftSubst F A) (g • p) (g • MvPolynomial.X χ),
        show g • (dftSubst F A p * dftSubst F A (MvPolynomial.X χ))
            = g • dftSubst F A p * g • dftSubst F A (MvPolynomial.X χ) from
          (MulSemiringAction.toRingEquiv A (latticeFunctionField F (A → ℤ)) g).map_mul
            (dftSubst F A p) (dftSubst F A (MvPolynomial.X χ)),
        hgen χ, hp]

end Equivariance

/-\! ## 5. 公理闸门 -/

#print axioms unitsMulEquivSelf
#print axioms neZero_card_cast_of_hasEnoughRootsOfUnity
#print axioms zMono
#print axioms zMono_zero
#print axioms zMono_add
#print axioms single_eq_smul_zMono
#print axioms charOf_apply_add
#print axioms diagMonoidHom
#print axioms diagMonoidHom_apply
#print axioms diagAlgHom_single
#print axioms diagAlgHom
#print axioms diagAlgHom_apply_single
#print axioms diagAlgHom_apply_smul_single
#print axioms diagAlgHom_inv_comp
#print axioms diagAlgHom_comp_inv
#print axioms diagAlgEquiv
#print axioms diagAlgEquiv_apply_single
#print axioms smul_zMono
#print axioms smul_zMono_eq_iff
#print axioms zMono_mem_invariants_iff
#print axioms zMono_mem_invariants
#print axioms finsuppEmb
#print axioms polySubst
#print axioms polySubst_injective
#print axioms polySubst_monomial
#print axioms polySubst_X
#print axioms algToFF
#print axioms polyToFF
#print axioms polyToFF_injective
#print axioms dftSubstPoly
#print axioms dftSubstPoly_X
#print axioms dftInvPoly
#print axioms sum_mulChar_eq_ite
#print axioms dftInvPoly_C
#print axioms dftInvPoly_X
#print axioms dftInvPoly_dftSubstPoly_X
#print axioms dftInvPoly_comp_dftSubstPoly
#print axioms dftSubstPoly_injective
#print axioms dftSubst
#print axioms dftSubst_X
#print axioms dftSubst_injective
#print axioms diagMPolyHom
#print axioms diagMPolyHom_X
#print axioms diagMPolyEquiv
#print axioms dftSubst_smul

end

end EM

end ABGV52
