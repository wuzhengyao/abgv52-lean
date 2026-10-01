/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-iii：Fischer 收口（索引 ＋ 不变性）**

  承 D5（`charOf`／`kernelLattice`）与 D4（`dftVec`／`smul_dftVec`）。本件交付两件事：

  **① 索引 `[X : Y] = |A|`**（`card_kernelLattice_eq_card`）：
  `charOf : X → MulChar A F` **不是** `→+` 同态（`Multiplicative (MulChar A F)` 的加法群
  实例不可导出，D5 陷阱 13），故**手工搭商双射** `quotientKernelEquiv`：
    * 正向 `[n] ↦ charOf n`（良定义性由 `charOf_add` 与 `leftRel_apply` 给）；
    * 逆向 `χ ↦ [single χ 1]`（由 `charOf_single` 给）；
  再用 `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity` ＋ 自建 `Aˣ ≃ A`
  得 `Nat.card (X ⧸ Y) = Fintype.card A`。

  **② 不变性 `F(Y) ⊆ F(M)^A`**（`diagMono_mem_invariants`）：
  `diagMono n := ∏_χ y_χ ^ n_χ`（`y_χ` = `dftVec χ` 在函数域中的像）。主引理
  `smul_diagMono`（**特征向量性**）：`g • diagMono n = (charOf n g) • diagMono n`；
  ⟹ `n ∈ Y`（即 `charOf n = 1`）时 `diagMono n` 是 `A`-不变的。

  **⚠ 结构性注记（本轮实测，值得记）**：`diagMono` 的**乘法性**需要 `y_χ ≠ 0`
  —— `zpow_add` 只对 `Group` 存在，域上只有 `zpow_add₀`（带 `≠ 0` 前提）
  ⟹ **`dftVec ≠ 0`（`dftVec_ne_zero`）不是装饰性的**，它是 `smul_diagMono` 归纳的前提；
  其证明走**系数提取**：`dftVec χ` 在基向量 `e_1` 处的系数是 `(χ 1)⁻¹ = 1 ≠ 0`
  （⚠ 须在 `MonoidAlgebra` 层用 `MonoidAlgebra.coeff`／`coeff_sum`／`coeff_single`，
  `MonoidAlgebra` 在 mathlib 中**不是** `Finsupp` 的函数式缩写，无 `DFunLike` 强制转换）。

  **未在本件交付（诚实登记，见 wiki §3g 余量）**：③ **度数收口**
  （`F(Y) = F(M)^A` ＋ `IsRational F ↥(latticeInvariantsAlg F A (A → ℤ))`）——
  需先建对角模型 `F[z_χ^{±}]`（其 `A`-作用是对角的，**非格作用**，D1 框架不适用，
  须手建 `MulSemiringAction`）＋ 其与 `F[M]` 的 `A`-等变 `AlgEquiv`（DFT 变元代换），
  再证 `[F(M) : F(Y)] ≤ |A|`（用本件的索引），经 D3 的 `finrank_invariants` 收口。
  **本轮已先付该债务之一**：`FaithfulSMul A (regularFunctionField F A)`（`faithfulSMul_regular`，
  D3 `finrank_invariants` 的前提）已证。**但本件仍不声称已证 ③**（变元代换与度数收口未做）。
-/
import ABGV52.D5_ABGV52

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

/-! ## 0. 小工具（无 `Fintype` 依赖） -/

section PiSingle

variable {A : Type*}

/-- `Pi.single` 在**指标**上单射（值取 `1`）：`a ≠ b ⟹ single a 1 ≠ single b 1`。
（⚠ `Pi.single_injective` 是**取值**方向的单射，不适用。） -/
lemma piSingle_ne_of_ne {a b : A} (h : a ≠ b) :
    (Pi.single a (1 : ℤ) : A → ℤ) ≠ Pi.single b (1 : ℤ) := by
  intro habs
  have h2 : (Pi.single b (1 : ℤ) : A → ℤ) a = 1 := by
    rw [← habs]
    exact Pi.single_eq_same a 1
  rw [Pi.single_eq_of_ne h] at h2
  exact one_ne_zero h2.symm

/-- 指标嵌入 `a ↦ ofAdd (Pi.single a 1)` 单射（`dftVec` 系数提取用）。 -/
lemma ofAdd_piSingle_injective :
    Function.Injective (fun a : A =>
      (Multiplicative.ofAdd (Pi.single a (1 : ℤ)) : Multiplicative (A → ℤ))) := by
  intro a b h
  by_contra hab
  exact piSingle_ne_of_ne hab (Multiplicative.ofAdd.injective h)

end PiSingle

section Tools

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

-- ⚠ `MulChar` 的群结构是 noncomputable 实例，须显式提升才参与综合（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

omit [Fintype A] in
/-- 字符取值非零：`χ a * χ a⁻¹ = χ 1 = 1 ≠ 0`。 -/
lemma mulChar_apply_ne_zero (χ : MulChar A F) (a : A) : χ a ≠ 0 := by
  intro h
  have h1 : χ a * χ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact one_ne_zero h1.symm

omit [Fintype A] in
/-- `χ⁻¹` 逐点取逆（`MulChar.inv_apply` 是 `CommMonoidWithZero` 版；此处 `A` 是群，须自证）。 -/
lemma mulChar_inv_apply (χ : MulChar A F) (a : A) : χ⁻¹ a = (χ a)⁻¹ := by
  have h : χ⁻¹ * χ = 1 := inv_mul_cancel χ
  have h2 := congrArg (fun ψ : MulChar A F => ψ a) h
  rw [MulChar.mul_apply, MulChar.one_apply (Group.isUnit a)] at h2
  exact eq_inv_of_mul_eq_one_left h2

omit [Fintype A] in
/-- 自然数幂的逐点取值。 -/
lemma mulChar_pow_apply (χ : MulChar A F) (m : ℕ) (a : A) : (χ ^ m) a = (χ a) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MulChar.one_apply (Group.isUnit a)]
  | succ m ih => rw [pow_succ, MulChar.mul_apply, ih, pow_succ]

omit [Fintype A] in
/-- **整数幂的逐点取值** `(χ ^ k) a = (χ a) ^ k`（本件 `smul_diagMono` 的收口引理）。 -/
lemma mulChar_zpow_apply (χ : MulChar A F) (k : ℤ) (a : A) : (χ ^ k) a = (χ a) ^ k := by
  cases k with
  | ofNat m =>
      rw [show χ ^ (Int.ofNat m) = (χ : MulChar A F) ^ m from zpow_natCast χ m,
        show (χ a) ^ (Int.ofNat m) = (χ a) ^ m from zpow_natCast (χ a) m]
      exact mulChar_pow_apply F A χ m a
  | negSucc m =>
      rw [zpow_negSucc, zpow_negSucc, mulChar_inv_apply F A (χ ^ (m + 1)) a,
        mulChar_pow_apply F A χ (m + 1) a]

omit [Fintype A] in
/-- `charOf 0 = 1`。 -/
lemma charOf_zero : charOf F A 0 = 1 := by
  rw [charOf, Finsupp.prod_zero_index]

/-- `charOf` 的负元律：`charOf (-n) = (charOf n)⁻¹`。 -/
lemma charOf_neg (n : expVector F A) : charOf F A (-n) = (charOf F A n)⁻¹ := by
  have h : charOf F A n * charOf F A (-n) = 1 := by
    rw [← charOf_add, add_neg_cancel, charOf_zero]
  exact eq_inv_of_mul_eq_one_right h

end Tools

/-! ## 1. 索引：`X ⧸ Y ≃ MulChar A F` 与 `[X : Y] = |A|` -/

section Index

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **商映射的正向** `[n] ↦ charOf n`：良定义性由 `charOf_add` 给
（`-a + b ∈ Y ⟹ charOf a = charOf b`）。 -/
noncomputable def quotientKernelToFun :
    (expVector F A ⧸ kernelLattice F A) → MulChar A F :=
  fun q => Quotient.liftOn' q (fun n => charOf F A n)
    (fun a b hab => by
      have hch : charOf F A (-a + b) = 1 := QuotientAddGroup.leftRel_apply.mp hab
      calc charOf F A a = charOf F A a * charOf F A (-a + b) := by rw [hch, mul_one]
        _ = charOf F A (a + (-a + b)) := (charOf_add F A a (-a + b)).symm
        _ = charOf F A b := by rw [add_neg_cancel_left])

/-- **商映射的逆向** `χ ↦ [single χ 1]`。 -/
noncomputable def quotientKernelInvFun :
    MulChar A F → (expVector F A ⧸ kernelLattice F A) :=
  fun χ => QuotientAddGroup.mk (Finsupp.single χ 1)

lemma quotientKernel_right_inv (χ : MulChar A F) :
    quotientKernelToFun F A (quotientKernelInvFun F A χ) = χ := by
  show charOf F A (Finsupp.single χ 1) = χ
  exact charOf_single F A χ

lemma quotientKernel_left_inv (q : expVector F A ⧸ kernelLattice F A) :
    quotientKernelInvFun F A (quotientKernelToFun F A q) = q := by
  refine QuotientAddGroup.induction_on q ?_
  intro n
  change QuotientAddGroup.mk (Finsupp.single (charOf F A n) 1) = QuotientAddGroup.mk n
  rw [QuotientAddGroup.eq]
  show charOf F A (-(Finsupp.single (charOf F A n) 1) + n) = 1
  rw [charOf_add, charOf_neg, charOf_single, inv_mul_cancel]

/-- **商双射** `X ⧸ Y ≃ MulChar A F`（手工搭建，`charOf` 不是 `→+`，见 D5 陷阱 13）。 -/
noncomputable def quotientKernelEquiv :
    (expVector F A ⧸ kernelLattice F A) ≃ MulChar A F where
  toFun := quotientKernelToFun F A
  invFun := quotientKernelInvFun F A
  left_inv q := quotientKernel_left_inv F A q
  right_inv χ := quotientKernel_right_inv F A χ

end Index

section Card

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

/-- `Aˣ ≃ A`（`Fintype.card_units` 是 `GroupWithZero` 版；群情形须自建）。 -/
noncomputable def unitsEquivSelf : Aˣ ≃ A where
  toFun u := u
  invFun a := ⟨a, a⁻¹, mul_inv_cancel a, inv_mul_cancel a⟩
  left_inv := fun _ => Units.ext rfl
  right_inv := fun _ => rfl

/-- **索引定理** `[X : Y] = |A|`：`Nat.card (X ⧸ Y) = Fintype.card A`。

`X ⧸ Y ≃ MulChar A F`（`quotientKernelEquiv`）＋ `Nat.card (MulChar A F) = Nat.card Aˣ`
（双对偶，须 `HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)`）＋ `Aˣ ≃ A`（`unitsEquivSelf`）。 -/
theorem card_kernelLattice_eq_card [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)] :
    Nat.card (expVector F A ⧸ kernelLattice F A) = Fintype.card A := by
  rw [Nat.card_congr (quotientKernelEquiv F A),
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity A F,
    Nat.card_congr (unitsEquivSelf A), Nat.card_eq_fintype_card]

end Card

/-! ## 2. 不变性：`diagMono` 与 `smul_diagMono` -/

section Diagonal

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]

attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- `F[Z[A]]` 的**函数域**（D1 的 `latticeFunctionField` 在正则置换格上的实例）。 -/
abbrev regularFunctionField : Type _ := latticeFunctionField F (A → ℤ)

/-- `dftVec χ` 的**系数向量**（`MonoidAlgebra` 无 `DFunLike`，须走 `coeff`）。 -/
lemma coeff_dftVec (χ : MulChar A F) :
    (dftVec F A χ).coeff
      = ∑ a : A, Finsupp.single
          (Multiplicative.ofAdd (Pi.single a (1 : ℤ)) : Multiplicative (A → ℤ)) ((χ a)⁻¹) := by
  rw [dftVec, MonoidAlgebra.coeff_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [regMono, MonoidAlgebra.coeff_single]

/-- **`dftVec χ ≠ 0`**（系数提取：在基向量 `e_1` 处的系数为 `(χ 1)⁻¹ = 1`）。

⚠ 这个引理是**承重的**：`diagMono` 的乘法性只用得到 `zpow_add₀`（域上无 `zpow_add`），
而它需要非零前提。见文件头注记。 -/
lemma dftVec_ne_zero (χ : MulChar A F) : dftVec F A χ ≠ 0 := by
  intro h
  have hc := coeff_dftVec F A χ
  rw [h, MonoidAlgebra.coeff_zero] at hc
  have hsingle : (Finsupp.single
        (Multiplicative.ofAdd (Pi.single (1 : A) (1 : ℤ) : A → ℤ) : Multiplicative (A → ℤ))
        ((χ 1)⁻¹))
      (Multiplicative.ofAdd (Pi.single (1 : A) (1 : ℤ) : A → ℤ) :
        Multiplicative (A → ℤ)) = 1 := by
    rw [Finsupp.single_eq_same, map_one, inv_one]
  have h1 : (∑ a : A, Finsupp.single
        (Multiplicative.ofAdd (Pi.single a (1 : ℤ)) : Multiplicative (A → ℤ))
        ((χ a)⁻¹))
      (Multiplicative.ofAdd (Pi.single (1 : A) (1 : ℤ) : A → ℤ) :
        Multiplicative (A → ℤ)) = 1 := by
    rw [← hsingle, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_single
      (f := fun a : A => (Finsupp.single
        (Multiplicative.ofAdd (Pi.single a (1 : ℤ)) : Multiplicative (A → ℤ))
        ((χ a)⁻¹))
        (Multiplicative.ofAdd (Pi.single (1 : A) (1 : ℤ) : A → ℤ) :
          Multiplicative (A → ℤ))) (1 : A) ?_ ?_
    · intro b _ hb
      rw [Finsupp.single_eq_of_ne
        (fun hc' => hb (ofAdd_piSingle_injective hc').symm)]
    · intro hb
      exact absurd (Finset.mem_univ (1 : A)) hb
  rw [← hc] at h1
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h1
  exact one_ne_zero h1.symm

/-- `dftVec χ` 在函数域中的像 `y_χ`。 -/
noncomputable def dftVecFF (χ : MulChar A F) : regularFunctionField F A :=
  algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) (dftVec F A χ)

/-- `y_χ ≠ 0`（`algebraMap` 单射 ＋ `dftVec_ne_zero`）。 -/
lemma dftVecFF_ne_zero (χ : MulChar A F) : dftVecFF F A χ ≠ 0 := by
  intro h
  apply dftVec_ne_zero F A χ
  apply IsFractionRing.injective (latticeAlgebra F (A → ℤ)) (regularFunctionField F A)
  rw [dftVecFF] at h
  simpa using h

/-- `algebraMap` 与 `A`-作用交换。 -/
lemma smul_algebraMap_regular (g : A) (x : latticeAlgebra F (A → ℤ)) :
    g • algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) x
      = algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) (g • x) := by
  change (IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingEquiv A (latticeAlgebra F (A → ℤ)) g))
    (algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) x) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- `algebraMap` 与 `F`-纯量交换。 -/
lemma algebraMap_smul_regular (c : F) (x : latticeAlgebra F (A → ℤ)) :
    algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) (c • x)
      = c • algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply F (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) c]

/-- **特征向量性（函数域版）**：`g • y_χ = (χ g) • y_χ`（D4 `smul_dftVec` 的上延）。 -/
theorem smul_dftVecFF (g : A) (χ : MulChar A F) :
    g • dftVecFF F A χ = (χ g) • dftVecFF F A χ := by
  rw [dftVecFF, smul_algebraMap_regular, smul_dftVec, ← algebraMap_smul_regular]

/-- `a ↦ x_a`（单项式 `regMono a 1` 在函数域中的像）单射（`3` 的忠实性用）。 -/
lemma algebraMap_regMono_injective :
    Function.Injective fun a : A =>
      algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) (regMono F A a 1) := by
  intro a b h
  by_contra hab
  have h1 : regMono F A a 1 = regMono F A b 1 :=
    IsFractionRing.injective (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) h
  rw [regMono, regMono] at h1
  have h2 := MonoidAlgebra.single_left_injective (one_ne_zero (α := F)) h1
  exact piSingle_ne_of_ne hab (Multiplicative.ofAdd.injective h2)

/-- 作用在单项式上的显式形式（函数域版）：`g • x_a = x_{g a}`。 -/
lemma smul_algebraMap_regMono (g a : A) :
    g • algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A) (regMono F A a 1)
      = algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A)
          (regMono F A (g * a) 1) := by
  rw [smul_algebraMap_regular, smul_regMono]

/-- **`A` 在正则格函数域上忠实作用**（③ 度数收口的前置债务，本轮先付）。

证明：`g` 若逐点固定，则固定基单项式 `x_1`；由 `smul_algebraMap_regMono` 得
`x_g = x_1`，再由 `algebraMap_regMono_injective` 得 `g = 1`。 -/
theorem faithfulSMul_regular : FaithfulSMul A (regularFunctionField F A) := by
  refine ⟨fun {g₁ g₂} h => ?_⟩
  have h1 := h (algebraMap (latticeAlgebra F (A → ℤ)) (regularFunctionField F A)
    (regMono F A 1 1))
  rw [smul_algebraMap_regMono, smul_algebraMap_regMono, mul_one, mul_one] at h1
  exact algebraMap_regMono_injective F A h1

/-- **对角单项式** `∏_χ y_χ ^ n_χ`（Fischer 的 `F(Y)` 的生成元，`n` 为指数向量）。 -/
noncomputable def diagMono (n : expVector F A) : regularFunctionField F A :=
  n.prod fun χ k => (dftVecFF F A χ) ^ k

lemma diagMono_single (χ : MulChar A F) (k : ℤ) :
    diagMono F A (Finsupp.single χ k) = (dftVecFF F A χ) ^ k :=
  Finsupp.prod_single_index (zpow_zero (dftVecFF F A χ))

/-- **乘法性**（用 `dftVecFF_ne_zero`：域上只有 `zpow_add₀`，须非零前提）。 -/
lemma diagMono_add (n m : expVector F A) :
    diagMono F A (n + m) = diagMono F A n * diagMono F A m :=
  Finsupp.prod_add_index' (fun χ => zpow_zero (dftVecFF F A χ))
    (fun χ b₁ b₂ => zpow_add₀ (dftVecFF_ne_zero F A χ) b₁ b₂)

/-- 纯量在幂上的作用：`(c • y)^k = c^k • y^k`。 -/
lemma smul_zpow_apply (c : F) (y : regularFunctionField F A) (k : ℤ) :
    (c • y) ^ k = c ^ k • y ^ k := by
  rw [Algebra.smul_def, mul_zpow,
    ← map_zpow₀ (algebraMap F (regularFunctionField F A)) c k]
  exact (Algebra.smul_def (c ^ k) (y ^ k)).symm

omit [Fintype A] in
/-- 单个坐标上的取值：`charOf (single χ k) = χ ^ k`（D5 `charOf_single` 的 `zpow` 版）。 -/
lemma charOf_single_zpow (χ : MulChar A F) (k : ℤ) :
    charOf F A (Finsupp.single χ k) = χ ^ k :=
  Finsupp.prod_single_index (zpow_zero χ)

/-- **`charOf` 的逐点形式**：`charOf n g = ∏_χ (χ g) ^ n_χ`。 -/
lemma charOf_apply (n : expVector F A) (g : A) :
    charOf F A n g = n.prod fun χ k => (χ g) ^ k := by
  induction n using Finsupp.induction with
  | zero =>
      rw [charOf, Finsupp.prod_zero_index, Finsupp.prod_zero_index,
        MulChar.one_apply (Group.isUnit g)]
  | single_add χ k n _ _ ih =>
      have hsplit : (Finsupp.single χ k + n).prod (fun ψ j => (ψ g) ^ j)
          = (χ g) ^ k * n.prod (fun ψ j => (ψ g) ^ j) := by
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          exact zpow_zero (χ g)
        · intro ψ
          exact zpow_zero (ψ g)
        · intro ψ b₁ b₂
          exact zpow_add₀ (mulChar_apply_ne_zero F A ψ g) b₁ b₂
      rw [charOf_add, MulChar.mul_apply, charOf_single_zpow, ih, hsplit, mulChar_zpow_apply]

/-- **`smul_diagMono`（本件主定理）**：`g • diagMono n = (charOf n g) • diagMono n`。

归纳：`single_add` 步由 `diagMono_add` ＋ `smul_dftVecFF`（`g • y_χ^k = (χ g)^k • y_χ^k`）
＋ `smul_mul_smul`（纯量重分配）合成。 -/
theorem smul_diagMono (g : A) (n : expVector F A) :
    g • diagMono F A n = (charOf F A n g) • diagMono F A n := by
  rw [charOf_apply]
  induction n using Finsupp.induction with
  | zero => rw [diagMono, Finsupp.prod_zero_index, Finsupp.prod_zero_index, smul_one, one_smul]
  | single_add χ k n _ _ ih =>
      have hsplit : (Finsupp.single χ k + n).prod (fun ψ j => (ψ g) ^ j)
          = (χ g) ^ k * n.prod (fun ψ j => (ψ g) ^ j) := by
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          exact zpow_zero (χ g)
        · intro ψ
          exact zpow_zero (ψ g)
        · intro ψ b₁ b₂
          exact zpow_add₀ (mulChar_apply_ne_zero F A ψ g) b₁ b₂
      have hy : g • (dftVecFF F A χ) ^ k = (χ g) ^ k • (dftVecFF F A χ) ^ k := by
        have h1 : g • (dftVecFF F A χ) ^ k = (g • dftVecFF F A χ) ^ k :=
          map_zpow₀ (MulSemiringAction.toRingEquiv A (regularFunctionField F A) g)
            (dftVecFF F A χ) k
        rw [h1, smul_dftVecFF, smul_zpow_apply]
      rw [diagMono_add, smul_mul', ih, diagMono_single, hsplit, hy, smul_mul_smul]

/-- **② 不变性**：`n ∈ Y`（即 `charOf n = 1`）⟹ `diagMono n` 是 `A`-不变的。

（`F(Y) ⊆ F(M)^A` 的单项式层实现；度数收口 `F(Y) = F(M)^A` 见 wiki §3g 的余量登记。） -/
theorem diagMono_mem_invariants {n : expVector F A} (hn : n ∈ kernelLattice F A) :
    diagMono F A n ∈ latticeInvariantsAlg F A (A → ℤ) := by
  rw [mem_latticeInvariantsAlg_iff]
  intro g
  rw [smul_diagMono]
  have h1 : charOf F A n = 1 := hn
  rw [h1, MulChar.one_apply (Group.isUnit g), one_smul]

end Diagonal

/-! ## 3. 公理闸门 -/

#print axioms piSingle_ne_of_ne
#print axioms ofAdd_piSingle_injective
#print axioms charOf_single_zpow
#print axioms mulChar_apply_ne_zero
#print axioms mulChar_inv_apply
#print axioms mulChar_pow_apply
#print axioms mulChar_zpow_apply
#print axioms charOf_zero
#print axioms charOf_neg
#print axioms quotientKernelToFun
#print axioms quotientKernelInvFun
#print axioms quotientKernel_right_inv
#print axioms quotientKernel_left_inv
#print axioms quotientKernelEquiv
#print axioms unitsEquivSelf
#print axioms card_kernelLattice_eq_card
#print axioms coeff_dftVec
#print axioms dftVec_ne_zero
#print axioms dftVecFF
#print axioms dftVecFF_ne_zero
#print axioms smul_algebraMap_regular
#print axioms algebraMap_smul_regular
#print axioms smul_dftVecFF
#print axioms algebraMap_regMono_injective
#print axioms smul_algebraMap_regMono
#print axioms faithfulSMul_regular
#print axioms diagMono
#print axioms diagMono_single
#print axioms diagMono_add
#print axioms smul_zpow_apply
#print axioms charOf_apply
#print axioms smul_diagMono
#print axioms diagMono_mem_invariants

end

end EM

end ABGV52
