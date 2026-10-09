/-
  ABGV-5.2 —— **本体形式化 A · M4c §5／§6（EMIndep）**：`Yf` 族的代数独立性 ＋ `IsRational` 封装

  目标（`wiki/proj-ABGV52-formalize-em.md` §3.4 §5／§6）：
    §5：`AlgebraicIndependent ↥K₀ (Yf ·)`——Lenstra (1.4) 的数学心脏；
    §6：`IsRational ↥K₀ ↥(l(N)^G)`（§5 ＋ `aevalEquivField` ＋ `Esm_eq_fixedPoints` 封装）。

  路线（A1–A3 ＋ B）：
    A1：`l` 上 `Yb` 族（`Yb i = (y i).1`）代数独立——单式机器：
        `Yb` 族 = 单项式基族 `xm` 经换基线性代入 σ 的像；σ 单射由显式左逆 τ 给出
        （KEY 恒等式：两基 repr 互逆 `∑_j c_i j · d_j k = δ_i k`），而 `aeval xm`
        单射（`xm` 的单项式在 `l[MP]` 中系数可读）。
    A2：沿 `algebraMap l[MP] l(N)` 推到 `l(N)`（`AlgebraicIndependent.map'`），
        再 `AlgebraicIndependent.restrictScalars` 降到 `↥l^G`。
    A3：沿桥 `lGToK0 : ↥l^G →+* ↥K₀` 搬到 `↥K₀`（`AlgebraicIndependent.ringHom_of_comp_eq`）。
    B：`(hYf).aevalEquivField.symm` ＋ `Esm_eq_fixedPoints` ＋ `lNG` ⟹ `IsRational`。

  与蓝图写法的偏差（逐条）：
    ① 蓝图 §5 只写"可逆线性代入"；本件把它落为显式 σ／τ ＋ KEY 恒等式（τ∘σ = id）。
    ② 蓝图 §6 写"`∃ n, l(N)^G ≃ₐ[↥K₀] FractionRing (MvPolynomial (Fin n) ↥K₀)`"；
       本件按 `D1_ABGV52.IsRational` 的定义形输出（`∃ n, Nonempty (K ≃ₐ[F] rationalFunctionField F n)`）。
    ③ 追加导入 `Mathlib.RingTheory.AlgebraicIndependent.Basic`（`Adjoin.lean` 只导入
       `...Defs`，而本件需 `AlgebraicIndependent.restrictScalars`／`ringHom_of_comp_eq`／`map'`）。
    ④ 蓝图 §6 的"`adjoin = fixed`"一步由 `EMDegree_ABGV52.Esm_eq_fixedPoints`（集合层）供给；
       本件另补 `Esm = lNG`（`IntermediateField` 层，`le_antisymm` ＋ `Subfield.ext` 风格转换）
       ——`IntermediateField.equivOfEq` 需要后者才能接入。
    ⑤ `algebraicIndependent_Yf`／`isRational_fixedPoints` 带**自动纳入**的实例参数
       `[FaithfulSMul G (latticeFunctionField F M)]`（落入 `FixedPoints.subfield` 与
       `Esm_eq_fixedPoints` 的前提，属 section 变量；对 `isRational` 的调用方而言是真实前提）。

  纪律：全具名参数；每步即刻重编译。**无 sorry、无自造公理**（尾部 `#print axioms` 闸门逐条核验）。
-/
import ABGV52.EMDegree_ABGV52
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.Basic

open scoped BigOperators

namespace ABGV52
namespace EM

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]
variable {ι : Type*} [Fintype ι]

section Main
variable (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
variable (hρ : ∀ (σ : G) (i : ι),
  mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
variable (n : ℕ) (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
variable (hyfix : ∀ (i : Fin n) (σ : G),
  semiAlgEquiv (M := M) σ (y i).1 = (y i).1)
variable (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
variable (hy_indep : LinearIndependent (latticeFunctionField F M) y)
variable [FaithfulSMul G (latticeFunctionField F M)]

/-! ## 1. 单项式机器：`xm` 族与 `aeval xm` 的单射性 -/

/-- 单项式指数 → 群元：`x^d := ∏_j x_j^{d_j}`（B-坐标展开）。 -/
noncomputable def monoPow (B : Module.Basis ι ℤ P) (d : ι →₀ ℕ) : Multiplicative P :=
  d.prod fun j k => permMono (P := P) B j ^ k

theorem monoPow_add (B : Module.Basis ι ℤ P) (d₁ d₂ : ι →₀ ℕ) :
    monoPow (P := P) B (d₁ + d₂)
      = monoPow (P := P) B d₁ * monoPow (P := P) B d₂ := by
  simp only [monoPow]
  rw [Finsupp.prod_add_index' (fun a => pow_zero _) (fun a b₁ b₂ => pow_add _ _ _)]

theorem monoPow_single (B : Module.Basis ι ℤ P) (j : ι) (k : ℕ) :
    monoPow (P := P) B (Finsupp.single j k) = permMono (P := P) B j ^ k := by
  show (Finsupp.single j k).prod (fun j k => permMono (P := P) B j ^ k)
      = permMono (P := P) B j ^ k
  rw [Finsupp.prod_single_index (h := fun j k => permMono (P := P) B j ^ k) (pow_zero _)]

/-- **单项式族单射**：`d ↦ ∏_j x_j^{d_j}` 单射（B-坐标唯一展开）。 -/
theorem monoPow_injective (B : Module.Basis ι ℤ P) :
    Function.Injective (monoPow (P := P) B) := by
  intro d d' h
  have h2 : (B.repr).symm (Finsupp.mapRange (Nat.cast : ℕ → ℤ) (by simp) d)
      = (B.repr).symm (Finsupp.mapRange (Nat.cast : ℕ → ℤ) (by simp) d') := by
    have h' := congrArg Multiplicative.toAdd h
    have he : ∀ e : ι →₀ ℕ, monoPow (P := P) B e
        = Multiplicative.ofAdd
            ((B.repr).symm (Finsupp.mapRange (Nat.cast : ℕ → ℤ) (by simp) e)) := by
      intro e
      rw [permMono_prod_expansion (P := P) B (Finsupp.mapRange (Nat.cast : ℕ → ℤ) (by simp) e)]
      simp only [monoPow]
      rw [Finsupp.prod_mapRange_index (fun a => zpow_zero _)]
      exact Finsupp.prod_congr fun a _ => (zpow_natCast _ _).symm
    simpa [he, toAdd_ofAdd] using h'
  exact Finsupp.mapRange_injective (Nat.cast : ℕ → ℤ) (by simp) Nat.cast_injective
    ((B.repr).symm.injective h2)

/-- **单项式族 `xm`**：`x_i := single (permMono B i) 1`（作为 `l[MP]` 的元素）。 -/
noncomputable def xm (B : Module.Basis ι ℤ P) :
    ι → MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) :=
  fun i => MonoidAlgebra.single (permMono (P := P) B i) (1 : latticeFunctionField F M)

/-- 单式族的乘法可见形：`∏_j (x_j)^{k_j} = single (x^d) 1`。 -/
theorem prod_xm_eq_single (B : Module.Basis ι ℤ P) (d : ι →₀ ℕ) :
    d.prod (fun i k => xm (F := F) (M := M) (P := P) B i ^ k)
      = MonoidAlgebra.single (monoPow (P := P) B d) (1 : latticeFunctionField F M) := by
  classical
  induction d using Finsupp.induction with
  | zero =>
      rw [Finsupp.prod_zero_index, monoPow, Finsupp.prod_zero_index, MonoidAlgebra.one_def]
  | single_add j k d hj hk ih =>
      rw [Finsupp.prod_add_index' (fun a => pow_zero _) (fun a b₁ b₂ => pow_add _ _ _),
        Finsupp.prod_single_index
          (h := fun i k => (xm (F := F) (M := M) (P := P) B i) ^ k) (pow_zero _), ih,
        monoPow_add, monoPow_single]
      rw [show xm (F := F) (M := M) (P := P) B j
          = MonoidAlgebra.single (permMono (P := P) B j) (1 : latticeFunctionField F M)
          from rfl]
      rw [MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.single_mul_single, one_mul]

/-- `aeval xm` 在单项式上的值（系数可读形）。 -/
theorem aeval_xm_monomial (B : Module.Basis ι ℤ P) (d : ι →₀ ℕ)
    (c : latticeFunctionField F M) :
    MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
        (MvPolynomial.monomial d c)
      = MonoidAlgebra.single (monoPow (P := P) B d) c := by
  rw [MvPolynomial.aeval_monomial, prod_xm_eq_single]
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self_apply]
  rw [MonoidAlgebra.single_mul_single, one_mul, mul_one]

/-- `aeval xm` 的系数展开式（按 `support` 求和）。 -/
theorem aeval_xm_as_sum (B : Module.Basis ι ℤ P)
    (p : MvPolynomial ι (latticeFunctionField F M)) :
    MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B) p
      = ∑ v ∈ p.support,
          MonoidAlgebra.single (monoPow (P := P) B v) (MvPolynomial.coeff v p) := by
  have h1 : MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B) p
      = MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
          (∑ v ∈ p.support, MvPolynomial.monomial v (MvPolynomial.coeff v p)) :=
    congrArg (fun z : MvPolynomial ι (latticeFunctionField F M) =>
      MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B) z) (MvPolynomial.as_sum p)
  rw [h1, map_sum]
  exact Finset.sum_congr rfl fun v _ =>
    aeval_xm_monomial (F := F) (M := M) (P := P) B v (MvPolynomial.coeff v p)

/-- **`aeval xm` 单射**（`xm` 的单项式互异，故 `MonoidAlgebra` 系数逐项可读）。 -/
theorem aeval_xm_injective (B : Module.Basis ι ℤ P) :
    Function.Injective (MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
      : MvPolynomial ι (latticeFunctionField F M) →ₐ[latticeFunctionField F M]
        MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) := by
  classical
  intro p q hpq
  have hcoeff : ∀ v : ι →₀ ℕ, MvPolynomial.coeff v p = MvPolynomial.coeff v q := by
    intro v
    have hpq' : MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B) p
        = MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B) q := hpq
    rw [aeval_xm_as_sum (F := F) (M := M) (P := P) B p,
      aeval_xm_as_sum (F := F) (M := M) (P := P) B q] at hpq'
    have h10 := congrArg (fun z : MonoidAlgebra (latticeFunctionField F M)
        (Multiplicative P) => z.coeff (monoPow (P := P) B v)) hpq'
    have h1 : (∑ v' ∈ p.support, (if v' = v then MvPolynomial.coeff v' p else 0))
        = (∑ v' ∈ q.support, (if v' = v then MvPolynomial.coeff v' q else 0)) := by
      simpa [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_zero,
        Finsupp.single_apply, (monoPow_injective (P := P) B).eq_iff,
        Finsupp.zero_apply] using h10
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq'] at h1
    by_cases hpv : v ∈ p.support
    · rw [if_pos hpv] at h1
      by_cases hqv : v ∈ q.support
      · rwa [if_pos hqv] at h1
      · rw [if_neg hqv] at h1
        exact h1.trans (MvPolynomial.notMem_support_iff.mp hqv).symm
    · rw [if_neg hpv] at h1
      have hp0 := MvPolynomial.notMem_support_iff.mp hpv
      by_cases hqv : v ∈ q.support
      · rw [if_pos hqv] at h1
        exact hp0.trans h1
      · exact hp0.trans (MvPolynomial.notMem_support_iff.mp hqv).symm
  exact MvPolynomial.ext p q hcoeff

/-! ## 2. 换基基座：置换族线性无关、`W` 的两组基、分量恒等式 -/

/-- `permMono B` 单射（拉自基 `B` 的单射性）。 -/
theorem permMono_injective (B : Module.Basis ι ℤ P) :
    Function.Injective (permMono (P := P) B) := by
  intro a b h
  exact B.injective (by
    have h' := congrArg Multiplicative.toAdd h
    simpa [permMono, toAdd_ofAdd] using h')

/-- 置换族 `permMonoSub` 在 `l` 上线性无关（拉自 `l[MP]` 的单式基）。 -/
theorem linearIndependent_permMonoSub (B : Module.Basis ι ℤ P) :
    LinearIndependent (latticeFunctionField F M)
      (permMonoSub (F := F) (M := M) (P := P) B) := by
  have hcomp : (Submodule.subtype (W (F := F) (M := M) (P := P) B))
      ∘ permMonoSub (F := F) (M := M) (P := P) B
      = ⇑(MonoidAlgebra.basis (Multiplicative P) (latticeFunctionField F M))
        ∘ permMono (P := P) B := by
    funext j
    simp [permMonoSub, MonoidAlgebra.basis_apply]
  refine LinearIndependent.of_comp (v := permMonoSub (F := F) (M := M) (P := P) B)
    (Submodule.subtype (W (F := F) (M := M) (P := P) B)) ?_
  rw [hcomp]
  exact (MonoidAlgebra.basis (Multiplicative P) (latticeFunctionField F M)).linearIndependent.comp
    (permMono (P := P) B) (permMono_injective (P := P) B)

/-- `W` 的第一组基：置换族 `permMonoSub`。 -/
noncomputable def byb (B : Module.Basis ι ℤ P) :
    Module.Basis ι (latticeFunctionField F M) ↥(W (F := F) (M := M) (P := P) B) :=
  Module.Basis.mk (linearIndependent_permMonoSub (F := F) (M := M) (P := P) B)
    (by rw [span_permMono_range_eq_top (F := F) (M := M) (P := P) B])

/-- `W` 的第二组基：给定的 `y` 族（由 `hy_span`／`hy_indep` 定义）。 -/
noncomputable def bx (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) :
    Module.Basis (Fin n) (latticeFunctionField F M) ↥(W (F := F) (M := M) (P := P) B) :=
  Module.Basis.mk hy_indep (by rw [hy_span])

theorem byb_apply (B : Module.Basis ι ℤ P) (j : ι) :
    (byb (F := F) (M := M) (P := P) B) j
      = permMonoSub (F := F) (M := M) (P := P) B j := by
  simp [byb]

theorem bx_apply (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) (k : Fin n) :
    (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep) k = y k := by
  simp [bx]

/-- `bx.repr (y k) = single k 1`（第二组基下 `y` 的坐标）。 -/
theorem bx_repr_self (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) (k : Fin n) :
    (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr (y k)
      = Finsupp.single k 1 := by
  simpa [bx_apply] using
    Module.Basis.repr_self (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep) k

/-- `y i` 的 `byb`-坐标展开（单项式形式，作为 `l[MP]` 的元素）。 -/
theorem sum_repr_val (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) (i : Fin n) :
    ((y i).1 : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      = ∑ j : ι, MonoidAlgebra.single (permMono (P := P) B j)
          ((byb (F := F) (M := M) (P := P) B).repr (y i) j) := by
  have hsum : (∑ j : ι, ((byb (F := F) (M := M) (P := P) B).repr (y i)) j
      • (permMonoSub (F := F) (M := M) (P := P) B j)) = y i := by
    simpa [byb_apply] using
      Module.Basis.sum_repr (byb (F := F) (M := M) (P := P) B) (y i)
  have h2 : Submodule.subtype (W (F := F) (M := M) (P := P) B)
      (∑ j : ι, ((byb (F := F) (M := M) (P := P) B).repr (y i)) j
        • (permMonoSub (F := F) (M := M) (P := P) B j))
      = (∑ j : ι, MonoidAlgebra.single (permMono (P := P) B j)
          ((byb (F := F) (M := M) (P := P) B).repr (y i) j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    change ((byb (F := F) (M := M) (P := P) B).repr (y i)) j
      • MonoidAlgebra.single (permMono (P := P) B j) (1 : latticeFunctionField F M)
      = MonoidAlgebra.single (permMono (P := P) B j)
          ((byb (F := F) (M := M) (P := P) B).repr (y i) j)
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [← hsum]
  exact h2

/-- **KEY 恒等式**：两组基的 repr 互逆（`∑_j c_kj·d_ji = δ_ki`）。 -/
theorem key_identity (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) (k i : Fin n) :
    (∑ j : ι, ((byb (F := F) (M := M) (P := P) B).repr (y k) j)
      * ((bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr
          ((byb (F := F) (M := M) (P := P) B) j) i))
      = if k = i then 1 else 0 := by
  classical
  have hB : (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr (y k) i
      = if k = i then 1 else 0 := by
    rw [bx_repr_self (F := F) (M := M) (P := P) B n y hy_span hy_indep k,
      Finsupp.single_apply]
  have hsum : (∑ j : ι, ((byb (F := F) (M := M) (P := P) B).repr (y k)) j
      • ((byb (F := F) (M := M) (P := P) B) j)) = y k :=
    Module.Basis.sum_repr (byb (F := F) (M := M) (P := P) B) (y k)
  have h4 : (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr (y k)
      = ∑ j : ι, ((byb (F := F) (M := M) (P := P) B).repr (y k)) j
          • ((bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr
              ((byb (F := F) (M := M) (P := P) B) j)) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  have hlin : (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr (y k) i
      = ∑ j : ι, ((byb (F := F) (M := M) (P := P) B).repr (y k)) j
          * ((bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr
              ((byb (F := F) (M := M) (P := P) B) j) i) := by
    have h5 := congrArg (fun z : Fin n →₀ latticeFunctionField F M => z i) h4
    simpa [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul] using h5
  exact hlin.symm.trans hB

/-! ## 3. σ／τ 换基：可逆线性代入与 `Yb` 族代数独立 -/

/-- `∑_j C(a_j)·(C(b_j)·X_i) = C(∑_j a_j·b_j)·X_i`（系数并入常数项；KEY 恒等式的装配件）。 -/
theorem sum_C_mul_C_mul_X {ι' : Type*} [Fintype ι'] {σ : Type*}
    (a b : ι' → latticeFunctionField F M) (i : σ) :
    (∑ j : ι', MvPolynomial.C (a j) * (MvPolynomial.C (b j) * MvPolynomial.X i))
      = MvPolynomial.C (∑ j : ι', a j * b j) * MvPolynomial.X i := by
  have h1 : ∀ j : ι', MvPolynomial.C (a j) * (MvPolynomial.C (b j) * MvPolynomial.X i)
      = MvPolynomial.C (a j * b j) * MvPolynomial.X i := by
    intro j
    rw [← mul_assoc, ← MvPolynomial.C_mul]
  have h2 : (∑ j : ι', MvPolynomial.C (a j) * (MvPolynomial.C (b j) * MvPolynomial.X i))
      = ∑ j : ι', MvPolynomial.C (a j * b j) * MvPolynomial.X i :=
    Finset.sum_congr rfl fun j _ => h1 j
  have hC : (MvPolynomial.C (∑ j : ι', a j * b j) : MvPolynomial σ (latticeFunctionField F M))
      = ∑ j : ι', MvPolynomial.C (a j * b j) := by
    rw [map_sum]
  rw [h2, ← Finset.sum_mul, hC]

/-- 代入同态 σ（换基）：`X_i ↦ ∑_j C(c_ij)·X_j`。 -/
noncomputable def sigmaMapOf (c : Fin n → ι → latticeFunctionField F M) :
    MvPolynomial (Fin n) (latticeFunctionField F M) →ₐ[latticeFunctionField F M]
      MvPolynomial ι (latticeFunctionField F M) :=
  MvPolynomial.aeval fun i => ∑ j : ι, MvPolynomial.C (c i j) * MvPolynomial.X j

/-- σ 在生成元上的值。 -/
theorem sigmaMapOf_X (c : Fin n → ι → latticeFunctionField F M) (i : Fin n) :
    sigmaMapOf (F := F) (M := M) (n := n) c (MvPolynomial.X i)
      = ∑ j : ι, MvPolynomial.C (c i j) * MvPolynomial.X j := by
  rw [sigmaMapOf, MvPolynomial.aeval_X]

/-- 逆代入同态 τ：`X_j ↦ ∑_i C(d_ji)·X_i`。 -/
noncomputable def tauMapOf (d : ι → Fin n → latticeFunctionField F M) :
    MvPolynomial ι (latticeFunctionField F M) →ₐ[latticeFunctionField F M]
      MvPolynomial (Fin n) (latticeFunctionField F M) :=
  MvPolynomial.aeval fun j => ∑ i : Fin n, MvPolynomial.C (d j i) * MvPolynomial.X i

/-- τ 在生成元上的值。 -/
theorem tauMapOf_X (d : ι → Fin n → latticeFunctionField F M) (j : ι) :
    tauMapOf (F := F) (M := M) (n := n) d (MvPolynomial.X j)
      = ∑ i : Fin n, MvPolynomial.C (d j i) * MvPolynomial.X i := by
  rw [tauMapOf, MvPolynomial.aeval_X]

set_option maxHeartbeats 1000000 in
/-- **τ∘σ = id**：KEY 恒等式（两组基的 repr 互逆）⟹ σ 有显式左逆。 -/
theorem tauMapOf_sigmaMapOf (c : Fin n → ι → latticeFunctionField F M)
    (d : ι → Fin n → latticeFunctionField F M)
    (hid : ∀ (i k : Fin n), (∑ j : ι, c i j * d j k) = if i = k then 1 else 0) :
    (tauMapOf (F := F) (M := M) (n := n) d).comp
        (sigmaMapOf (F := F) (M := M) (n := n) c)
      = AlgHom.id (latticeFunctionField F M)
          (MvPolynomial (Fin n) (latticeFunctionField F M)) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  show MvPolynomial.aeval (fun j : ι => ∑ k : Fin n,
        MvPolynomial.C (d j k) * MvPolynomial.X k)
      (MvPolynomial.aeval (fun i' : Fin n => ∑ j : ι,
        MvPolynomial.C (c i' j) * MvPolynomial.X j) (MvPolynomial.X i))
      = MvPolynomial.X i
  rw [MvPolynomial.aeval_X]
  change MvPolynomial.aeval (fun j : ι => ∑ k : Fin n,
        MvPolynomial.C (d j k) * MvPolynomial.X k)
      (∑ j : ι, MvPolynomial.C (c i j) * MvPolynomial.X j) = MvPolynomial.X i
  have h1 : MvPolynomial.aeval (fun j : ι => ∑ k : Fin n,
        MvPolynomial.C (d j k) * MvPolynomial.X k)
      (∑ j : ι, MvPolynomial.C (c i j) * MvPolynomial.X j)
      = ∑ j : ι, MvPolynomial.C (c i j)
          * (∑ k : Fin n, MvPolynomial.C (d j k) * MvPolynomial.X k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  have h2 : (∑ j : ι, MvPolynomial.C (c i j)
        * (∑ k : Fin n, MvPolynomial.C (d j k) * MvPolynomial.X k))
      = ∑ j : ι, ∑ k : Fin n, MvPolynomial.C (c i j)
          * (MvPolynomial.C (d j k) * MvPolynomial.X k) :=
    Finset.sum_congr rfl fun j _ => Finset.mul_sum Finset.univ
      (fun k : Fin n => MvPolynomial.C (d j k) * MvPolynomial.X k) (MvPolynomial.C (c i j))
  have h3 : (∑ j : ι, ∑ k : Fin n, MvPolynomial.C (c i j)
        * (MvPolynomial.C (d j k) * MvPolynomial.X k))
      = ∑ k : Fin n, ∑ j : ι, MvPolynomial.C (c i j)
          * (MvPolynomial.C (d j k) * MvPolynomial.X k) :=
    Finset.sum_comm
  have h4 : (∑ k : Fin n, ∑ j : ι, MvPolynomial.C (c i j)
        * (MvPolynomial.C (d j k) * MvPolynomial.X k))
      = ∑ k : Fin n, MvPolynomial.C (if i = k then 1 else 0) * MvPolynomial.X k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_C_mul_C_mul_X (F := F) (M := M) (i := k) (a := fun j => c i j) (b := fun j => d j k)]
    rw [hid i k]
  have h5 : (∑ k : Fin n, MvPolynomial.C (if i = k then 1 else 0) * MvPolynomial.X k
        : MvPolynomial (Fin n) (latticeFunctionField F M))
      = MvPolynomial.X i := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, MvPolynomial.C_1, one_mul]
    · intro k _ hk
      rw [if_neg (fun h : i = k => hk h.symm), MvPolynomial.C_0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2, h3, h4]
  exact h5

/-- **σ 单射**（τ 为显式左逆；无需 `Function.Injective.comp` 的型类配合）。 -/
theorem sigmaMapOf_injective (c : Fin n → ι → latticeFunctionField F M)
    (d : ι → Fin n → latticeFunctionField F M)
    (hid : ∀ (i k : Fin n), (∑ j : ι, c i j * d j k) = if i = k then 1 else 0) :
    Function.Injective (sigmaMapOf (F := F) (M := M) (n := n) c) := by
  have hcomp := tauMapOf_sigmaMapOf (F := F) (M := M) (n := n) c d hid
  have hleft : ∀ r : MvPolynomial (Fin n) (latticeFunctionField F M),
      tauMapOf (F := F) (M := M) (n := n) d
        (sigmaMapOf (F := F) (M := M) (n := n) c r) = r := by
    intro r
    have h := congrArg (fun φ : MvPolynomial (Fin n) (latticeFunctionField F M)
        →ₐ[latticeFunctionField F M] MvPolynomial (Fin n) (latticeFunctionField F M) => φ r) hcomp
    simpa [AlgHom.comp_apply, AlgHom.id_apply] using h
  intro p q hpq
  calc p = tauMapOf (F := F) (M := M) (n := n) d
        (sigmaMapOf (F := F) (M := M) (n := n) c p) := (hleft p).symm
    _ = tauMapOf (F := F) (M := M) (n := n) d
        (sigmaMapOf (F := F) (M := M) (n := n) c q) := by rw [hpq]
    _ = q := hleft q

/-- `aeval xm` 在 `C c · X_j` 上的值（系数可读形）。 -/
theorem aeval_xm_C_mul_X (B : Module.Basis ι ℤ P) (j : ι)
    (c : latticeFunctionField F M) :
    MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
        (MvPolynomial.C c * MvPolynomial.X j)
      = MonoidAlgebra.single (permMono (P := P) B j) c := by
  rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [show xm (F := F) (M := M) (P := P) B j
      = MonoidAlgebra.single (permMono (P := P) B j) (1 : latticeFunctionField F M) from rfl]
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self_apply]
  rw [MonoidAlgebra.single_mul_single, one_mul, mul_one]

/-- **`aeval xm` 与 σ 在生成元上相容**：`aeval xm (σ (X_i)) = Yb_i`。 -/
theorem aeval_xm_sigmaMapOf_X (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) (i : Fin n) :
    MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
        (sigmaMapOf (F := F) (M := M) (n := n)
          (fun i j => (byb (F := F) (M := M) (P := P) B).repr (y i) j)
          (MvPolynomial.X i))
      = ((y i).1 : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) := by
  rw [sigmaMapOf_X]
  rw [map_sum]
  refine (Finset.sum_congr rfl fun j _ =>
    aeval_xm_C_mul_X (F := F) (M := M) (P := P) B j
      ((byb (F := F) (M := M) (P := P) B).repr (y i) j)).trans ?_
  exact (sum_repr_val (F := F) (M := M) (P := P) B n y hy_span hy_indep i).symm

set_option maxHeartbeats 1000000 in
/-- **A1 主引理**：`Yb` 族（`i ↦ (y i).1`，即 `y` 作为 `l[MP]` 元素）在 `l` 上代数独立。
证明：`aeval Yb = (aeval xm).comp σ`（生成元上逐项恒等）＋ `σ` 单射 ＋ `aeval xm` 单射。 -/
theorem algebraicIndependent_Yb (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) :
    AlgebraicIndependent (latticeFunctionField F M) (fun i : Fin n => (y i).1) := by
  show Function.Injective (MvPolynomial.aeval (fun i : Fin n => (y i).1)
    : MvPolynomial (Fin n) (latticeFunctionField F M) →ₐ[latticeFunctionField F M]
      MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
  have hcomp : (MvPolynomial.aeval (fun i : Fin n => (y i).1)
      : MvPolynomial (Fin n) (latticeFunctionField F M) →ₐ[latticeFunctionField F M]
        MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      = (MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
        : MvPolynomial ι (latticeFunctionField F M) →ₐ[latticeFunctionField F M]
          MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)).comp
        (sigmaMapOf (F := F) (M := M) (n := n)
          (fun i j => (byb (F := F) (M := M) (P := P) B).repr (y i) j)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    show MvPolynomial.aeval (fun i : Fin n => (y i).1) (MvPolynomial.X i)
      = MvPolynomial.aeval (xm (F := F) (M := M) (P := P) B)
          (sigmaMapOf (F := F) (M := M) (n := n)
            (fun i j => (byb (F := F) (M := M) (P := P) B).repr (y i) j)
            (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    exact (aeval_xm_sigmaMapOf_X (F := F) (M := M) (P := P) (B := B) (n := n) (y := y)
      (hy_span := hy_span) (hy_indep := hy_indep) i).symm
  rw [hcomp]
  intro p q hpq
  exact sigmaMapOf_injective (F := F) (M := M) (n := n)
    (fun i j => (byb (F := F) (M := M) (P := P) B).repr (y i) j)
    (fun j i => (bx (F := F) (M := M) (P := P) B n y hy_span hy_indep).repr
      ((byb (F := F) (M := M) (P := P) B) j) i)
    (fun i k => key_identity (F := F) (M := M) (P := P) B n y hy_span hy_indep i k)
    (aeval_xm_injective (F := F) (M := M) (P := P) B hpq)

/-! ## 4. §5 主定理：`Yf` 族在 `↥K₀` 上代数独立 -/

set_option maxHeartbeats 1000000 in
/-- **A2＋A3（§5 主定理）**：`Yf` 族在 `↥K₀` 上代数独立——Lenstra (1.4) 的数学心脏。

路线：`algebraicIndependent_Yb`（`l` 上）沿 `algebraMap l[MP] l(N)` 推为 `l(N)` 上
（`AlgebraicIndependent.map'` ＋ 分式环单射），再 `restrictScalars` 降到 `↥l^G`，
最后沿桥 `lGToK0 : ↥l^G →+* ↥K₀` 搬到 `↥K₀`（`AlgebraicIndependent.ringHom_of_comp_eq`，
需 `lGToK0` 满射——由 `FixedPoints.subfield` 的定义直得）。 -/
theorem algebraicIndependent_Yf (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) :
    AlgebraicIndependent ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (fun i : Fin n => Yf (F := F) (M := M) (P := P) B n y i) := by
  have hAI_l : AlgebraicIndependent (latticeFunctionField F M)
      (fun i : Fin n =>
        algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P)) (y i).1) :=
    (algebraicIndependent_Yb (F := F) (M := M) (P := P) B n y hy_span hy_indep).map'
      (f := IsScalarTower.toAlgHom (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)))
      (IsFractionRing.injective (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)))
  have hAI_lG : AlgebraicIndependent ↥(FixedPoints.subfield G (latticeFunctionField F M))
      (fun i : Fin n =>
        algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P)) (y i).1) :=
    AlgebraicIndependent.restrictScalars (fun a b h => Subtype.ext h) hAI_l
  have hsurj : Function.Surjective (lGToK0 (G := G) (F := F) (M := M) (P := P)) := by
    intro x
    obtain ⟨c, hc, hcx⟩ := Subfield.mem_map.mp
      (show (x : semiFunctionField (F := F) (M := M) (P := P))
          ∈ (FixedPoints.subfield G (latticeFunctionField F M)).map
            (algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)))
        from x.2)
    exact ⟨⟨c, hc⟩, Subtype.ext
      ((lGToK0_coe (G := G) (F := F) (M := M) (P := P) ⟨c, hc⟩).trans hcx)⟩
  have hcompat :
      (algebraMap ↥(K0 (G := G) (F := F) (M := M) (P := P))
        (semiFunctionField (F := F) (M := M) (P := P))).comp
        (lGToK0 (G := G) (F := F) (M := M) (P := P))
      = (RingHom.id (semiFunctionField (F := F) (M := M) (P := P))).comp
        (algebraMap ↥(FixedPoints.subfield G (latticeFunctionField F M))
          (semiFunctionField (F := F) (M := M) (P := P))) := by
    ext c
    show algebraMap ↥(K0 (G := G) (F := F) (M := M) (P := P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (lGToK0 (G := G) (F := F) (M := M) (P := P) c)
      = algebraMap ↥(FixedPoints.subfield G (latticeFunctionField F M))
        (semiFunctionField (F := F) (M := M) (P := P)) c
    rw [lGToK0_coe (G := G) (F := F) (M := M) (P := P) c]
    rfl
  have hAI_K0 : AlgebraicIndependent ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (fun i : Fin n =>
        algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P)) (y i).1) :=
    AlgebraicIndependent.ringHom_of_comp_eq
      (f := lGToK0 (G := G) (F := F) (M := M) (P := P))
      (g := RingHom.id (semiFunctionField (F := F) (M := M) (P := P)))
      hAI_lG hsurj Function.injective_id hcompat
  show AlgebraicIndependent ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (fun i : Fin n =>
        algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P)) (y i).1)
  exact hAI_K0

/-! ## 5. §6 主定理：不动点域的有理性（`IsRational` 封装） -/

set_option maxHeartbeats 1000000 in
/-- **B（§6 主定理）**：`l(N)^G` 在 `↥K₀` 上有理性。

路线：`SlI_eq_adjoin_primitive` 取本原元 `θ`；`Esm_eq_fixedPoints` 得
`Esm = l(N)^G`（集合层）；`algebraicIndependent_Yf` 经 `aevalEquivField` 给出
`FractionRing (MvPolynomial (Fin n) ↥K₀) ≃ₐ[↥K₀] ↥Esm`；
再把 `↥l(N)^G` 与 `↥Esm`（=`lNG`）用保持代数的显式同构相接（两边同为 `l(N)` 子型，
`map_*` 全是 `Subtype.ext rfl`，往返由 `AlgHom.ext` 给出）。 -/
theorem isRational_fixedPoints (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
    (hyfix : ∀ (i : Fin n) (σ : G),
      semiAlgEquiv (M := M) σ (y i).1 = (y i).1)
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hy_indep : LinearIndependent (latticeFunctionField F M) y) :
    IsRational ↥(K0 (G := G) (F := F) (M := M) (P := P))
      ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) := by
  obtain ⟨θ, hθ, hSlI⟩ := SlI_eq_adjoin_primitive (F := F) (G := G) (M := M) (P := P)
  have hAI := algebraicIndependent_Yf (G := G) (F := F) (M := M) (P := P)
    B n y hy_span hy_indep
  have hEsm : (Esm (G := G) (F := F) (M := M) (P := P) B n y :
      Set (semiFunctionField (F := F) (M := M) (P := P)))
      = (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) :
        Set (semiFunctionField (F := F) (M := M) (P := P))) :=
    Esm_eq_fixedPoints (F := F) (M := M) (P := P) (B := B) (n := n) (y := y)
      hy_span hyfix θ hSlI hθ
  have hEqIF : Esm (G := G) (F := F) (M := M) (P := P) B n y
      = lNG (G := G) (F := F) (M := M) (P := P) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : x ∈ (Esm (G := G) (F := F) (M := M) (P := P) B n y :
          Set (semiFunctionField (F := F) (M := M) (P := P))) := hx
      have hx'' : x ∈ (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) :
          Set (semiFunctionField (F := F) (M := M) (P := P))) := hEsm ▸ hx'
      show x ∈ (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) :
          Set (semiFunctionField (F := F) (M := M) (P := P)))
      exact hx''
    · intro x hx
      have hx' : x ∈ (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) :
          Set (semiFunctionField (F := F) (M := M) (P := P))) := hx
      show x ∈ (Esm (G := G) (F := F) (M := M) (P := P) B n y :
          Set (semiFunctionField (F := F) (M := M) (P := P)))
      rw [hEsm]
      exact hx'
  let fwd : ↥(lNG (G := G) (F := F) (M := M) (P := P))
      →ₐ[↥(K0 (G := G) (F := F) (M := M) (P := P))]
      ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) :=
    { toFun := fun z => ⟨(z : semiFunctionField (F := F) (M := M) (P := P)), z.2⟩
      map_one' := Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      commutes' := fun a => Subtype.ext rfl }
  let bwd : ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))
      →ₐ[↥(K0 (G := G) (F := F) (M := M) (P := P))]
      ↥(lNG (G := G) (F := F) (M := M) (P := P)) :=
    { toFun := fun z => ⟨(z : semiFunctionField (F := F) (M := M) (P := P)), z.2⟩
      map_one' := Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      commutes' := fun a => Subtype.ext rfl }
  refine ⟨n, ⟨?_⟩⟩
  exact (AlgEquiv.ofAlgHom fwd bwd
      (AlgHom.ext fun z => Subtype.ext rfl)
      (AlgHom.ext fun z => Subtype.ext rfl)).symm.trans
    ((IntermediateField.equivOfEq hEqIF).symm.trans hAI.aevalEquivField.symm)

end Main

end EM
end ABGV52

/-! ## 6. `#print axioms` 闸门（每条声明须只出 `propext`／`Classical.choice`／`Quot.sound`） -/

#print axioms ABGV52.EM.monoPow
#print axioms ABGV52.EM.monoPow_add
#print axioms ABGV52.EM.monoPow_single
#print axioms ABGV52.EM.monoPow_injective
#print axioms ABGV52.EM.xm
#print axioms ABGV52.EM.prod_xm_eq_single
#print axioms ABGV52.EM.aeval_xm_monomial
#print axioms ABGV52.EM.aeval_xm_as_sum
#print axioms ABGV52.EM.aeval_xm_injective
#print axioms ABGV52.EM.permMono_injective
#print axioms ABGV52.EM.linearIndependent_permMonoSub
#print axioms ABGV52.EM.byb
#print axioms ABGV52.EM.bx
#print axioms ABGV52.EM.byb_apply
#print axioms ABGV52.EM.bx_apply
#print axioms ABGV52.EM.bx_repr_self
#print axioms ABGV52.EM.sum_repr_val
#print axioms ABGV52.EM.key_identity
#print axioms ABGV52.EM.sum_C_mul_C_mul_X
#print axioms ABGV52.EM.sigmaMapOf
#print axioms ABGV52.EM.sigmaMapOf_X
#print axioms ABGV52.EM.tauMapOf
#print axioms ABGV52.EM.tauMapOf_X
#print axioms ABGV52.EM.tauMapOf_sigmaMapOf
#print axioms ABGV52.EM.sigmaMapOf_injective
#print axioms ABGV52.EM.aeval_xm_C_mul_X
#print axioms ABGV52.EM.aeval_xm_sigmaMapOf_X
#print axioms ABGV52.EM.algebraicIndependent_Yb
#print axioms ABGV52.EM.algebraicIndependent_Yf
#print axioms ABGV52.EM.isRational_fixedPoints
