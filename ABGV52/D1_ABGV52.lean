/-
  ABGV-5.2 —— C 档 · 第二处显式假设（Endo--Miyata--Voskresenskii 判据）· **块 0**

  块 0 = 对象层（零数学风险，纯接口）：
    * `IsRational` / `IsStablyRational`：域论谓词（**具体定义**，非公理）；
    * `IsPermutationLattice` / `IsStablyPermutation`：一般有限群 `G` 的 `Z[G]`-格谓词；
    * 非空性对照（L1）：`F` 自身有理 ⟹ 稳定有理；平凡表示是置换格。

  与 B 档的关系：B 档的 `Hyp_ABGV52.IsStablyPermutation` 是 `H = C_3 × C_3` 的特例；
  本档在**一般** `G` 上做，二者以后用桥引理相连。

  命名空间取 `ABGV52.EM`（EM = Endo--Miyata），避免与 B 档同名定义冲突。
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.RepresentationTheory.Rep.Basic

open CategoryTheory

namespace ABGV52

namespace EM

/-! ## 1. 有理性与稳定有理性（域论谓词） -/

/-- `F` 上有限个变元的有理函数域 `F(t₁,…,tₙ)`。 -/
abbrev rationalFunctionField (F : Type*) [Field F] (n : ℕ) : Type _ :=
  FractionRing (MvPolynomial (Fin n) F)

/-- **`K` 在 `F` 上有理**：`K` 同构于 `F` 上有限个变元的有理函数域。 -/
def IsRational (F : Type*) [Field F] (K : Type*) [Field K] [Algebra F K] : Prop :=
  ∃ n : ℕ, Nonempty (K ≃ₐ[F] rationalFunctionField F n)

/-- **`K` 在 `F` 上稳定有理**：`K` 上再添有限个变元后有理。 -/
def IsStablyRational (F : Type*) [Field F] (K : Type*) [Field K] [Algebra F K] : Prop :=
  ∃ n m : ℕ,
    Nonempty (rationalFunctionField K n ≃ₐ[F] rationalFunctionField F m)

/-- **零变元的有理函数域是基域自身**（`F(t₁,…,t₀) ≅ F`）。 -/
noncomputable def rationalFunctionFieldZero (F : Type*) [Field F] :
    rationalFunctionField F 0 ≃ₐ[F] F :=
  (IsFractionRing.algEquivOfAlgEquiv (R := F) (MvPolynomial.isEmptyAlgEquiv F (Fin 0))).trans
    (FractionRing.algEquiv F F)

/-- **非空性对照（L1）**：域是自身的零变元有理函数域。 -/
theorem isRational_self (F : Type*) [Field F] : IsRational F F :=
  ⟨0, ⟨(rationalFunctionFieldZero F).symm⟩⟩

/-- **非空性对照（L1）**：有理 ⟹ 稳定有理（添零个变元）。 -/
theorem IsRational.isStablyRational {F K : Type*} [Field F] [Field K] [Algebra F K]
    (h : IsRational F K) : IsStablyRational F K := by
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨0, n, ?_⟩
  refine ⟨?_⟩
  exact ((rationalFunctionFieldZero K).restrictScalars F).trans e

/-! ## 2. 置换格与稳定置换格（一般群 `G`） -/

/-- **置换 `Z[G]`-格**：同构于某有限 `G`-集 `X` 的置换模 `Z[X]`。 -/
def IsPermutationLattice (G : Type*) [Group G] (P : Rep ℤ G) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : MulAction G X),
    Nonempty (P ≅ Rep.ofMulAction ℤ G X)

/-- **稳定置换格**：`∃ P Q` 置换，`L ⊕ P ≅ Q`。 -/
def IsStablyPermutation (G : Type*) [Group G] (L : Rep ℤ G) : Prop :=
  ∃ P Q : Rep ℤ G,
    IsPermutationLattice G P ∧ IsPermutationLattice G Q ∧ Nonempty (L ⊞ P ≅ Q)

/-- **非空性对照（L1）**：平凡表示是置换格（取单点 `G`-集）。 -/
theorem isPermutationLattice_trivial (G : Type*) [Group G] :
    IsPermutationLattice G (Rep.ofMulAction ℤ G PUnit) :=
  ⟨PUnit, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

-- 待办（块 1）：`IsPermutationLattice G L → IsStablyPermutation G L`（取 `P = 0`、`Q = L`），
-- 需要 `L ⊞ 0 ≅ L` 的 `biprod` API —— 与块 1 的 `⊞` 理论一并落地。

/-! ## 3. 格函数域 `F(M)` 与不变量域 `F(M)^G`

  `M` 是 `Z[G]`-格（加法群 ＋ `G`-作用 ＋ `ℤ`-线性相容）。写作
  `F[M] = MonoidAlgebra F (Multiplicative M)`（单项式环），`F(M) = Frac F[M]`。 -/

section Field

variable (F : Type*) [Field F]
variable (G : Type*) [Group G]
variable (M : Type*) [AddCommGroup M] [Module ℤ M]
  [DistribMulAction G M] [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]

/-- `g` 在 `Multiplicative M` 上诱导的**乘法**自同构（由格的加法作用诱导）。 -/
noncomputable def mulEquivOfSMul (g : G) : Multiplicative M ≃* Multiplicative M where
  toFun x := Multiplicative.ofAdd (g • x.toAdd)
  invFun x := Multiplicative.ofAdd (g⁻¹ • x.toAdd)
  left_inv x := by
    show Multiplicative.ofAdd (g⁻¹ • (g • x.toAdd)) = x
    rw [smul_smul, inv_mul_cancel, one_smul]
    simp
  right_inv x := by
    show Multiplicative.ofAdd (g • (g⁻¹ • x.toAdd)) = x
    rw [smul_smul, mul_inv_cancel, one_smul]
    simp
  map_mul' x y := by
    show Multiplicative.ofAdd (g • (x * y).toAdd)
      = Multiplicative.ofAdd (g • x.toAdd) * Multiplicative.ofAdd (g • y.toAdd)
    rw [show (x * y).toAdd = x.toAdd + y.toAdd from rfl, smul_add]
    rfl

omit [Module ℤ M] [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] in
@[simp] lemma mulEquivOfSMul_apply (g : G) (x : Multiplicative M) :
    mulEquivOfSMul G M g x = Multiplicative.ofAdd (g • x.toAdd) := rfl

/-- **`F[M]`**：格 `M` 的群代数（单项式环）。 -/
abbrev latticeAlgebra : Type _ := MonoidAlgebra F (Multiplicative M)

noncomputable def latticeAlgebraEquiv (g : G) :
    latticeAlgebra F M ≃+* latticeAlgebra F M :=
  MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G M g)

noncomputable def latticeAlgebraActionHom :
    G →* (latticeAlgebra F M ≃+* latticeAlgebra F M) where
  toFun g := latticeAlgebraEquiv F G M g
  map_one' := by
    have h1 : mulEquivOfSMul G M (1 : G) = MulEquiv.refl (Multiplicative M) := by
      ext x
      simp [mulEquivOfSMul]
    rw [latticeAlgebraEquiv, h1]
    refine RingEquiv.ext fun x => MonoidAlgebra.ext ?_
    simp [MonoidAlgebra.mapDomainRingEquiv]
  map_mul' g h := by
    have hcomp : mulEquivOfSMul G M (g * h)
        = (mulEquivOfSMul G M h).trans (mulEquivOfSMul G M g) := by
      ext x
      show (g * h) • x.toAdd = g • (h • x.toAdd)
      rw [mul_smul]
    simp only [latticeAlgebraEquiv, hcomp, MonoidAlgebra.mapDomainRingEquiv_trans]
    refine RingEquiv.ext fun x => MonoidAlgebra.ext ?_
    simp [MonoidAlgebra.mapDomainRingEquiv]

/-- **`F[M]` 上的 `G`-作用**（`g · x^m = x^{g·m}`，系数不动）。 -/
noncomputable instance : MulSemiringAction G (latticeAlgebra F M) :=
  MulSemiringAction.compHom (latticeAlgebra F M) (latticeAlgebraActionHom F G M)

/-- **`F(M)`**：格 `M` 的函数域 `Frac F[M]`。 -/
abbrev latticeFunctionField : Type _ := FractionRing (latticeAlgebra F M)

/-- **`F(M)` 上的 `G`-作用**（由 `F[M]` 上的作用经分式域延拓）。 -/
noncomputable instance : MulSemiringAction G (latticeFunctionField F M) :=
  MulSemiringAction.compHom (latticeFunctionField F M)
    ((IsFractionRing.ringEquivOfRingEquivHom (latticeAlgebra F M)
      (latticeFunctionField F M)).comp (latticeAlgebraActionHom F G M))

/-- **不变量域 `F(M)^G`**（论文 `thm:endo-miyata` 的左端）。 -/
noncomputable abbrev latticeInvariants : Subfield (latticeFunctionField F M) :=
  FixedPoints.subfield G (latticeFunctionField F M)

theorem mem_latticeInvariants_iff (x : latticeFunctionField F M) :
    x ∈ latticeInvariants F G M ↔ ∀ g : G, g • x = x := by
  rw [latticeInvariants, FixedPoints.subfield]
  exact MulAction.mem_fixedPoints

end Field

/-\! ## 4. 公理闸门 -/

#print axioms isRational_self
#print axioms IsRational.isStablyRational
#print axioms isPermutationLattice_trivial
#print axioms mulEquivOfSMul
#print axioms latticeAlgebraActionHom
#print axioms latticeInvariants
#print axioms mem_latticeInvariants_iff

end EM

end ABGV52
