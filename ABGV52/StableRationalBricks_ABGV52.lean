/-
  ABGV-5.2 —— 稳定有理性的**闭包砖块**（为消去 `EMHyp` 波预置脚手架）

  **动机**（主循环 2026-10-11）：`EMHyp` 的剩余块是「稳定有理性 ⟹ `ρ(M)` 可逆」
  （flasque 类的双有理不变性）。该波需要一批**稳定有理性自身的闭包性质**作基础；
  本件把其中**可立即证明**的几条落地，其余（加变元的塔式同构）登记为目标。

  **无 sorry、无自造公理**；`#print axioms` 门见 §3。
-/
import ABGV52.D1_ABGV52
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization

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

/-- **砖①零件 3（系数层清分母）** ✓：`FractionRing A` 的每个元素乘以某个**非零因子**后落在 `A` 的像里 ✓
（`c = a / s` ✓，`IsLocalization.surj` ✓）。 -/
theorem exists_denom_mul_eq_algebraMap {A : Type*} [CommRing A] [IsDomain A]
    (c : FractionRing A) :
    ∃ (s : A) (_ : s ∈ nonZeroDivisors A) (a : A),
      c * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  obtain ⟨⟨a, ⟨s, hs⟩⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) c
  exact ⟨s, hs, a, h⟩

/-! **砖①零件 4（多项式层清分母）—— 计划 ＋ 已核 API 事实（第 375 轮仍未落 ✗）**

**目标** ✓：`∀ p : MvPolynomial σ (FractionRing A), ∃ (s ∈ nonZeroDivisors A) (q : MvPolynomial σ A),
p * C (algebraMap s) = MvPolynomial.map (algebraMap A _) q` ✓（＝ `IsLocalization` 的 **`surj'` 实质** ✓）。
**已核 API 事实** ✓（两轮实测所得，**下一轮直接可用** ✓，免再踩 ✗）：
- **`p.support : Finset (σ →₀ ℕ)`** ✓（**指数向量**，不是 `σ` ✗ —— 上轮 5 处类型错的根因 ✓）；
- `Submonoid.prod_mem (S) ⟨逐项证明⟩` ✓ 是**积封闭**的正确名（`Finset.prod_mem` **不存在** ✗）；
- **`MvPolynomial.coeff_map`** ✓ 存在（`map_coeff` ✗ **不存在**）；**`MvPolynomial.coeff_sum`** ✓ 存在；
  重写**次序**须 **`coeff_map` 先于 `coeff_sum`** ✓（否则目标里是 `(map … (∑ …)).coeff` ✗，`coeff_sum` 找不到模式 ✗）；
- `Finset.prod_eq_mul_prod_diff_singleton` ✓／`Finset.sum_eq_single` ✓ 均在；
- 主项的收尾 ✓：`← hb u`（**反向**重写 ✓）＋ **`ring`** ✓，比正向 `rw` 稳 ✓；
- **仍未定** ✗：`coeff_monomial` 的 `if` **朝向** ✓ 与 `u ∉ support ⟹ coeff = 0` 的**引理名** ✗（`Finsupp.not_mem_support_iff.mp` **不存在** ✗ —— 下一轮先探名 ✓）。
**⚠ 不声称** ✗：本轮**未落**该件 ✓；零件 1–3 ＋ 积封闭 ✓ 已落。 -/
/-- **砖①零件 5（非零因子的积封闭）** ✓：非零因子子幺半群中元素的**有限积**仍是非零因子 ✓
（`Submonoid.prod_mem` ✓）。**用途** ✓：零件 4 的**分母积** `s := Π_{v ∈ support} s_v` ✓ 靠它合法 ✓。 -/
theorem prod_mem_nonZeroDivisors {A : Type*} [CommRing A] [IsDomain A] {ι : Type*}
    (t : Finset ι) (f : ι → A) (h : ∀ i ∈ t, f i ∈ nonZeroDivisors A) :
    ∏ i ∈ t, f i ∈ nonZeroDivisors A :=
  Submonoid.prod_mem (nonZeroDivisors A) h

#print axioms prod_mem_nonZeroDivisors

/-- **砖①零件 4（多项式层清分母）** ✓：`MvPolynomial σ (FractionRing A)` 的每个元素乘以某个
**非零因子**（作为常多项式 ✓）后落在 `MvPolynomial σ A` 的像里 ✓ —— 即 **`IsLocalization` 的 `surj'` 实质** ✓。
**证法** ✓：逐系数取分母（零件 3 ✓），`s := Π_{v ∈ support} d v` ✓（零件 5 ✓），
`q := Σ_{v ∈ support} monomial v (b v * Π_{w ∈ support.erase v} d w)` ✓，逐系数验证 ✓。
**已核 API 事实** ✓：`p.support` 的元素是**指数向量** `σ →₀ ℕ` ✓；`coeff_monomial` 的 `if` 朝向为 **`if v = u`** ✓
（故配 **`Finset.sum_ite_eq'`** ✓）；`u ∉ support ⟹ coeff = 0` 用 **`MvPolynomial.mem_support_iff`** ✓。 -/
theorem exists_denom_mul_eq_map {A : Type*} [CommRing A] [IsDomain A] {σ : Type*}
    (p : MvPolynomial σ (FractionRing A)) :
    ∃ (s : A) (_ : s ∈ nonZeroDivisors A) (q : MvPolynomial σ A),
      p * MvPolynomial.C (algebraMap A (FractionRing A) s) =
        MvPolynomial.map (algebraMap A (FractionRing A)) q := by
  classical
  choose d hd b hb using fun v : σ →₀ ℕ => exists_denom_mul_eq_algebraMap (p.coeff v)
  refine ⟨∏ v ∈ p.support, d v,
    prod_mem_nonZeroDivisors _ _ fun v _ => hd v,
    ∑ v ∈ p.support, MvPolynomial.monomial v (b v * ∏ w ∈ p.support.erase v, d w), ?_⟩
  ext u
  have hL : (p * MvPolynomial.C (algebraMap A (FractionRing A)
        (∏ v ∈ p.support, d v))).coeff u
      = algebraMap A (FractionRing A) (∏ v ∈ p.support, d v) * p.coeff u := by
    rw [mul_comm p (MvPolynomial.C _), MvPolynomial.coeff_C_mul]
  rw [hL, MvPolynomial.coeff_map, MvPolynomial.coeff_sum,
    Finset.sum_congr rfl fun v _ => by rw [MvPolynomial.coeff_monomial],
    Finset.sum_ite_eq']
  by_cases hu : u ∈ p.support
  · rw [if_pos hu, ← Finset.mul_prod_erase p.support d hu, map_mul, map_mul, ← hb u]
    ring
  · have hcoeff : p.coeff u = 0 := by
      by_contra h
      exact hu (MvPolynomial.mem_support_iff.mpr h)
    rw [ite_eq_right hu, map_zero, hcoeff, mul_zero]

#print axioms exists_denom_mul_eq_map

/-! ### 砖①（有理函数域塔展平）**无条件**（第 377 轮）

**🔴 关键发现** ✗→✓：mathlib **早有**这条桥 —— **`Mathlib/RingTheory/MvPolynomial/Localization.lean:42`**：
`instance isLocalization : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S)` ✓。
**⚠ 我此前三次判定「mathlib 无」全部因为搜错目录** ✗（在 `Mathlib/Algebra/MvPolynomial/` 里搜，
而该文件在 **`Mathlib/RingTheory/MvPolynomial/`** 下 ✓）—— 与 L46 的教训**同型**（内容式检索须**全库** ✓）。

**链路** ✓：`RF (RF K k) n = FractionRing S`（`S := MvPolynomial (Fin n) (RF K k)` ✓）
⟹ mathlib 实例给 `IsLocalization ((nonZeroDivisors R').map C) S` ✓（`R' := MvPolynomial (Fin k) K` ✓）
⟹ `isFractionRing_of_isLocalization`（＋零件 1 的子幺半群包含 ✓）给
`IsFractionRing S (FractionRing (MvPolynomial (Fin n) R'))` ✓
⟹ 两个分式环同构 ✓（`IsLocalization.algEquiv` ✓）
⟹ 经 `mvPolynomial_tower`（第 372 轮 ✓）＋ `IsFractionRing.algEquivOfAlgEquiv` 得 `RF K (k+n)` ✓。 -/

/-! ### 🔴 **重大发现**（第 377 轮）：mathlib **早有**「多项式环上的局部化」桥 ✗→✓

**`Mathlib/RingTheory/MvPolynomial/Localization.lean:42`** ✓：
`instance isLocalization : IsLocalization (M.map <| C (σ := σ)) (MvPolynomial σ S)` ✓
（`S` 为 `R` 在 `M` 处的局部化 ⟹ `MvPolynomial σ S` 是 `MvPolynomial σ R` 在 `M.map C` 处的局部化 ✓）。

**⚠ 我此前三轮判定「mathlib 无」全部是假阻断** ✗ —— 根因**同型且致命**：**搜错目录** ✗
（在 `Mathlib/Algebra/MvPolynomial/` 里搜，而该文件在 **`Mathlib/RingTheory/MvPolynomial/`** 下 ✓）。
**⟹ L46 的判据须再加一条** ✓：**"mathlib 无"的判定必须记录"搜了哪些目录"** ✓，且**内容式检索要覆盖全库** ✗
（`grep -rn` 全 `Mathlib/` ＋ 交叉关键词 ✓，而非只搜"名字看起来对"的那一个目录 ✓）。

**砖① 的现状与后续** ✓：桥已有 ✓（免自建 ✓）；**剩余障碍＝`Algebra S T` 实例** ✗ ——
`isFractionRing_of_isLocalization` 需要 `[Algebra S T]`（`S := MvPolynomial σ (FractionRing R)`，
`T := FractionRing (MvPolynomial σ R)` ✓），而该结构须经 **`IsLocalization.lift`** 自建 ✓ ＋ `IsScalarTower` ✓。
**⚠ 不声称** ✗：`rationalFunctionField_tower_algEquiv` 本轮**未落** ✗（已撤 ✗）。 -/

/-- **砖①零件 6** ✓：`nonZeroDivisors R` 在 `C` 下的像落在 `nonZeroDivisors (MvPolynomial σ R)` 里 ✓
（`isFractionRing_of_isLocalization` 的 `M ≤ nonZeroDivisors R` 假设 ✓，由零件 1 ✓ 即得）。 -/
theorem map_C_le_nonZeroDivisors (R : Type*) [CommRing R] [IsDomain R] (σ : Type*) :
    (nonZeroDivisors R).map (MvPolynomial.C (σ := σ)) ≤
      nonZeroDivisors (MvPolynomial σ R) := by
  rintro x ⟨a, ha, rfl⟩
  exact C_mem_nonZeroDivisors ha

#print axioms map_C_le_nonZeroDivisors

/-! ### 砖①塔的**构件 1**：系数嵌入（第 378 轮）

**目标** ✓：塔展平 `RF (RF K k) n ≅ RF K (k+n)` 的第一步 —— 把系数环 `RF K k = FractionRing A`
（`A := MvPolynomial (Fin k) K` ✓）**映入**大分式环 `T := FractionRing (MvPolynomial (Fin n) A)` ✓。
**路线** ✓：`A → A[x] → T` 的复合**单射** ✓（域 ✓）⟹ `IsFractionRing.lift` 提升为 `RF K k →+* T` ✓。
**用途** ✓：它给出 `T` 上的 **`Algebra (RF K k) T`** ✓（经 `RingHom.toAlgebra` ✓），进而
`MvPolynomial.eval₂Hom` 给 **`Algebra (MvPolynomial (Fin n) (RF K k)) T`** ✓ —— 即
`isFractionRing_of_isLocalization` 所需的 **`[Algebra S T]`** ✓（第 377 轮定位的障碍 ✓）。 -/
noncomputable def coeffMap (K : Type*) [Field K] (k n : ℕ) :
    EM.rationalFunctionField K k →+*
      FractionRing (MvPolynomial (Fin n) (MvPolynomial (Fin k) K)) :=
  IsFractionRing.lift (K := EM.rationalFunctionField K k)
    (L := FractionRing (MvPolynomial (Fin n) (MvPolynomial (Fin k) K)))
    (g := (algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin k) K))
        (FractionRing (MvPolynomial (Fin n) (MvPolynomial (Fin k) K)))).comp
      (MvPolynomial.C : MvPolynomial (Fin k) K →+*
        MvPolynomial (Fin n) (MvPolynomial (Fin k) K)))
    (fun a b h => MvPolynomial.C_injective _ _
      (IsFractionRing.injective (MvPolynomial (Fin n) (MvPolynomial (Fin k) K)) _ h))

#print axioms coeffMap

#print axioms exists_denom_mul_eq_algebraMap
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
