/-
  ABGV-5.2 —— 稳定有理性的**闭包砖块**（为消去 `EMHyp` 波预置脚手架）

  **动机**（主循环 2026-10-11）：`EMHyp` 的剩余块是「稳定有理性 ⟹ `ρ(M)` 可逆」
  （flasque 类的双有理不变性）。该波需要一批**稳定有理性自身的闭包性质**作基础；
  本件把其中**可立即证明**的几条落地，其余（加变元的塔式同构）登记为目标。

  **无 sorry、无自造公理**；`#print axioms` 门见 §3。
-/
import ABGV52.D1_ABGV52
import Mathlib.Algebra.MvPolynomial.Equiv

namespace ABGV52

open CategoryTheory

universe u

/-! ## §1 基本闭包性质 -/

/-- **有理 ⟹ 稳定有理**（`n = 0` 支，用工程已有的 `EM.rationalFunctionFieldZero`）。 -/
theorem isStablyRational_of_isRational (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] (h : EM.IsRational F K) : EM.IsStablyRational F K := by
  obtain ⟨n, ⟨e⟩⟩ := h
  exact ⟨0, n, ⟨((EM.rationalFunctionFieldZero K).restrictScalars F).trans e⟩⟩

/-- **自反（非空洞对照 L1）**：基域在自身上稳定有理。 -/
theorem isStablyRational_self (F : Type*) [Field F] : EM.IsStablyRational F F :=
  isStablyRational_of_isRational F F (EM.isRational_self F)

/-- **沿 `F`-代数同构搬运**（目标 G0，2026-10-11 已证 ✓）：稳定有理性只依赖
`F`-同构类。路线：`MvPolynomial.mapAlgEquiv (Fin n) e`（mathlib
`Algebra/MvPolynomial/Equiv.lean:170`）给出**分子环**同构，再经
`IsFractionRing.algEquivOfAlgEquiv`（`RingTheory/Localization/FractionRing.lean:533`）
提升到分式域。 -/
theorem stablyRational_of_algEquiv {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] (e : K ≃ₐ[F] L) (h : EM.IsStablyRational F K) :
    EM.IsStablyRational F L := by
  obtain ⟨n, m, ⟨φ⟩⟩ := h
  refine ⟨n, m, ⟨?_⟩⟩
  -- 显式传参：`IsFractionRing.algEquivOfAlgEquiv` 的隐式名 `K`／`L` 指**分式域**，
  -- 与本定理的字段变量同名，必须显式点名以免相撞。
  exact (IsFractionRing.algEquivOfAlgEquiv (R := F)
      (A := MvPolynomial (Fin n) K) (B := MvPolynomial (Fin n) L)
      (K := EM.rationalFunctionField K n) (L := EM.rationalFunctionField L n)
      (MvPolynomial.mapAlgEquiv (Fin n) e)).symm.trans φ

/-- **同构不变形**（`↔` 形，便于下游两向使用）。 -/
theorem isStablyRational_iff_of_algEquiv {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] (e : K ≃ₐ[F] L) :
    EM.IsStablyRational F K ↔ EM.IsStablyRational F L :=
  ⟨stablyRational_of_algEquiv e, stablyRational_of_algEquiv e.symm⟩

/-! ## §2 登记目标（未证；逐字卡点）

**目标 G0（沿基变换搬运）** —— ✅ **已证** ✓（见 §1 的 `stablyRational_of_algEquiv`／`isStablyRational_iff_of_algEquiv`；关键 API 实测为 `MvPolynomial.mapAlgEquiv` ＋ `IsFractionRing.algEquivOfAlgEquiv`）。以下为**当时的**排查留痕：
**应有路线**：`K(t₁..t_n) ≃ₐ[F] L(t₁..t_n)` 由 `IsFractionRing.algEquivOfAlgEquiv`（mathlib `RingTheory/Localization/FractionRing.lean:533`，**已核实存在** ✓）沿**分子环**同构提升；
**卡点（2026-10-11 实测更新）**：需要 `MvPolynomial (Fin n) K ≃ₐ[F] MvPolynomial (Fin n) L`（系数同构的提升）。实测：
- 包路径为 **`Mathlib.Algebra.MvPolynomial.Basic`** ✓（`Mathlib.Data.MvPolynomial.*` 已迁移 ✗，用旧路径会报 `object file ... does not exist`）；
- 在**本版 mathlib** 中 `#check` 实测：`MvPolynomial.map` **不存在** ✗、`MvPolynomial.map_map` **不存在** ✗、`MvPolynomial.renameEquiv` **不存在** ✗（三者均报 `Unknown constant`）⟹ 系数提升 API 的**实际名字待查**（下一步：在 `Mathlib/Algebra/MvPolynomial/` 下按 `map`／`rename`／`Equiv` 检索，或改用 `MvPolynomial.aeval` 自行构造 `AlgEquiv.ofAlgHom` 双向）；
- 本件首版误用了不存在的 `MvPolynomial.algEquivOfAlgEquiv` ✗，**已撤回** ✓。本件**不假装证明** ✗。

（未证；逐字卡点）

**目标 G1（加变元封闭）**：`EM.IsStablyRational F K ⟹ EM.IsStablyRational F (K(t₁,…,t_k))`
—— 即 `∃ n m, K(t) ≅ F(x)` ⟹ `∃ n' m, K(t,s) ≅ F(x)`。
**应有路线**：`F(K(t₁..t_n))(s₁..s_k) ≅ K(t₁..t_{n+k})`（多项式环的变元拼接 ＋ 分式环塔式搬运）。
**卡点**：需要 `FractionRing (MvPolynomial (Fin n) (FractionRing (MvPolynomial (Fin k) K)))`
与 `FractionRing (MvPolynomial (Fin (n+k)) K)` 之间的同构 —— mathlib 侧有
`MvPolynomial.finSumEquiv`／`rename` 类工具（工程 `SaltRatOver_ABGV52.lean:25–121` 已用
`Fin.castAdd` ＋ `MvPolynomial.rename` 做过**同型**的搬运），但**分式环塔**的
`IsFractionRing` 实例拼接需另建引理；本件**不假装证明** ✗。

**目标 G2（塔式传递）**：`EM.IsStablyRational F K ⟹ EM.IsStablyRational K L ⟹ EM.IsStablyRational F L`
（先证 `L` 在 `F` 上稳定有理；须处理两层变元与 `Algebra` 塔）—— 同为后续波次目标 ✗。
-/

/-! ## §2.5 第 370 轮：**G1/G2 的两块砖** —— 砖②（系数延拓）已落 ✓

**G1／G2 的公共机制** ✓：两块砖
**砖②**：同构 `K ≃ₐ[F] L` 可**延拓**到有理函数域 `K(t_n) ≃ₐ[F] L(t_n)` ✓（本轮 ✓）；
**砖①**：塔**展平** `(K(t_k))(s_n) ≅ K(u_{k+n})` ✓（**未落** ✗ —— 见 §2 的卡点，mathlib 侧 `MvPolynomial.finSumEquiv` **不存在** ✗，
须用 `MvPolynomial.renameEquiv` ＋ `Fin k ⊕ Fin n ≃ Fin (k+n)` 自建 ✓）。
**⚠ 不声称** ✗：本节的**砖②**不依赖砖① ✓ 独立可用 ✓；但 **G1／G2 本身仍未证** ✗。 -/

/-- **砖②（系数延拓）** ✓：`K ≃ₐ[F] L` ⟹ **`K(t_n) ≃ₐ[F] L(t_n)`** ✓。
**路线** ✓（与 G0 同工艺 ✓）：`MvPolynomial.mapAlgEquiv (Fin n) φ` 给**分子环**同构 ✓，
再经 `IsFractionRing.algEquivOfAlgEquiv` ✓ 提升到分式域 ✓。 -/
theorem rationalFunctionField_algEquivMap {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] (φ : K ≃ₐ[F] L) (n : ℕ) :
    Nonempty (EM.rationalFunctionField K n ≃ₐ[F] EM.rationalFunctionField L n) :=
  ⟨IsFractionRing.algEquivOfAlgEquiv (R := F)
    (A := MvPolynomial (Fin n) K) (B := MvPolynomial (Fin n) L)
    (K := EM.rationalFunctionField K n) (L := EM.rationalFunctionField L n)
    (MvPolynomial.mapAlgEquiv (Fin n) φ)⟩

#print axioms rationalFunctionField_algEquivMap

/-! ## §2.6 第 371 轮：**砖① 提为具名假设** ＋ **G1 条件化**

**mathlib 侧实测** ✗：`Mathlib/Algebra/MvPolynomial/` 与 `Mathlib/RingTheory/Localization/FractionRing.lean`
**完全没有交集** ✓（按**内容**检索而非按名字猜 —— L46 §2 ✓）⟹ **「多项式环上的局部化」桥须自建** ✗。
**应有证法（已定，下一轮执行）** ✓：`IsLocalization (nonZeroDivisors A) (MvPolynomial σ (FractionRing A))` ✓ ——
`surj` 用**清分母**：`p : MvPolynomial σ (Frac A)` 的系数 `c_i = a_i / s_i` ✓，
取支集上的**有限积** `S := Π s_i ∈ nonZeroDivisors A` ✓ ⟹ `S * p` 的系数落在 `A` 的像里 ✓ ⟹ `p = (S*p)/S` ✓；
`map_units` 显然 ✓；`eq_iff_exists` 由域上消去 ✓。
**⚠ 本轮处置** ✗（B 档 ✓）：把砖① 提为**具名、类型锁定**的假设 `RationalFunctionFieldTowerHyp` ✓，
并证出 **G1 条件于它** ✓ —— 于是 **G1 的残余 ＝ 这一块砖** ✓（砖②第 370 轮已无条件 ✓）。

**⚠ 不声称** ✗：`RationalFunctionFieldTowerHyp` **未证** ✗（mathlib 缺件 ✓，证法已定 ✓）；**G2 仍未有条件形** ✗（下一轮）。 -/

/-- **砖①（塔展平，具名假设）** ✓：`(K(t_k))(s_n) ≅_F K(u_{k+n})` ✓。 -/
def RationalFunctionFieldTowerHyp (F : Type*) [Field F] (K : Type*) [Field K] [Algebra F K] :
    Prop :=
  ∀ k n : ℕ,
    Nonempty (EM.rationalFunctionField (EM.rationalFunctionField K k) n ≃ₐ[F]
      EM.rationalFunctionField K (k + n))

/-- **外形锁定** ✓：砖① 的外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem rationalFunctionFieldTowerHyp_typeLock (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] :
    (RationalFunctionFieldTowerHyp F K) =
      (∀ k n : ℕ,
        Nonempty (EM.rationalFunctionField (EM.rationalFunctionField K k) n ≃ₐ[F]
          EM.rationalFunctionField K (k + n))) := rfl

/-- **G1（加变元封闭）条件化** ✓：砖① ＋ `IsStablyRational F K` ⟹ **`IsStablyRational F (K(t_k))`** ✓。
**证法链** ✓：`(K(t_k))(s_n) ≅ K(u_{k+n}) ≅ K(u_{n+k}) ≅ (K(t_n))(s_k) ≅ (F(x_m))(s_k) ≅ F(x_{m+k})`
（砖① 三次 ✓ ＋ 砖② 一次 ✓ ＋ 变元序交换一次 ✓）。 -/
theorem isStablyRational_rationalFunctionField (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] (hyp : RationalFunctionFieldTowerHyp F K)
    (hypF : RationalFunctionFieldTowerHyp F F) (k : ℕ)
    (h : EM.IsStablyRational F K) : EM.IsStablyRational F (EM.rationalFunctionField K k) := by
  classical
  obtain ⟨n, m, hφ⟩ := h
  refine ⟨n, m + k, ?_⟩
  -- 变元序：K(u_{k+n}) ≅ K(u_{n+k})（只差 `Nat.add_comm` ✓）
  have hswap : Nonempty (EM.rationalFunctionField K (k + n) ≃ₐ[F]
      EM.rationalFunctionField K (n + k)) := by
    rw [Nat.add_comm k n]
    exact ⟨AlgEquiv.refl⟩
  exact ⟨(Classical.choice (hyp k n)).trans
    ((Classical.choice hswap).trans
      ((Classical.choice (hyp n k)).symm.trans
        ((Classical.choice (rationalFunctionField_algEquivMap (Classical.choice hφ) k)).trans
          (Classical.choice (hypF m k)))))⟩

/-- **砖①a（多项式层塔展平）** ✓ **无条件**：`K[x_1..x_k][y_1..y_n] ≅ K[u_1..u_{k+n}]` ✓
（**变元拼接** ✓，`K`-代数同构 ✓）。
**路线** ✓：`MvPolynomial.sumAlgEquiv` ✓（`K[S₁⊕S₂] ≅ K[S₁][S₂]` ✓）＋
`MvPolynomial.renameEquiv` ✓（沿 `finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n+k)` ✓）＋
`finCongr (Nat.add_comm n k)` ✓（变元序 ✓）。
**⚠ 意义** ✓：这是**砖① 的无分母一半** ✓ —— 砖①（有理函数域塔展平 ✓）**只剩下一个局部化步骤** ✗：
`FractionRing (MvPolynomial σ (FractionRing A)) ≅ FractionRing (MvPolynomial σ A)` ✓
（＝「多项式环上的局部化」✗，mathlib 无 ✓，证法见 §2.6 的清分母计划 ✓）。 -/
theorem mvPolynomial_tower (K : Type*) [CommRing K] (k n : ℕ) :
    Nonempty (MvPolynomial (Fin n) (MvPolynomial (Fin k) K) ≃ₐ[K]
      MvPolynomial (Fin (k + n)) K) :=
  ⟨(MvPolynomial.sumAlgEquiv K (Fin n) (Fin k)).symm.trans
    ((MvPolynomial.renameEquiv K (finSumFinEquiv (m := n) (n := k))).trans
      (MvPolynomial.renameEquiv K (finCongr (Nat.add_comm n k))))⟩

/-! ### 砖①的**清分母**零件（第 373 轮）

**砖① 剩余步骤** ✗ ＝ 证 `IsLocalization ((nonZeroDivisors A).map C) (MvPolynomial σ (FractionRing A))` ✓
（**多项式环上的局部化** ✓）；其 `surj'` 用**支集上有限积清分母** ✓。本轮先落其**两块必需零件** ✓。 -/

/-- **砖①零件 1** ✓：**非零因子在多项式环中的像（`C a`）仍是非零因子** ✓（逐系数验证 ✓）。 -/
theorem C_mem_nonZeroDivisors {A : Type*} [CommRing A] [IsDomain A] {σ : Type*} {a : A}
    (ha : a ∈ nonZeroDivisors A) : MvPolynomial.C a ∈ nonZeroDivisors (MvPolynomial σ A) := by
  rw [mem_nonZeroDivisors_iff] at ha ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · ext v
    have h := congrArg (fun q => q.coeff v) hx
    exact ha.1 (x.coeff v) (by simpa using h)
  · ext v
    have h := congrArg (fun q => q.coeff v) hx
    rw [mul_comm x (MvPolynomial.C a), MvPolynomial.coeff_C_mul] at h
    have h2 : a * x.coeff v = 0 := h
    rw [mul_comm] at h2
    exact ha.2 (x.coeff v) h2

/-- **砖①零件 2** ✓：**非零因子在分式环中是单位** ✓（`IsLocalization.map_units` ✓）。 -/
theorem isUnit_algebraMap_fractionRing {A : Type*} [CommRing A] [IsDomain A] {a : A}
    (ha : a ∈ nonZeroDivisors A) : IsUnit (algebraMap A (FractionRing A) a) :=
  IsLocalization.map_units (FractionRing A) ⟨a, ha⟩

#print axioms C_mem_nonZeroDivisors
#print axioms isUnit_algebraMap_fractionRing
#print axioms mvPolynomial_tower
#print axioms rationalFunctionFieldTowerHyp_typeLock
#print axioms isStablyRational_rationalFunctionField

/-! ## §3 公理闸门 -/

#print axioms isStablyRational_of_isRational
#print axioms isStablyRational_self
#print axioms stablyRational_of_algEquiv
#print axioms isStablyRational_iff_of_algEquiv

end ABGV52
