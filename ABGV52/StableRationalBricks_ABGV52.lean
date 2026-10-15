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

/-! ## §3 公理闸门 -/

#print axioms isStablyRational_of_isRational
#print axioms isStablyRational_self
#print axioms stablyRational_of_algEquiv
#print axioms isStablyRational_iff_of_algEquiv

end ABGV52
