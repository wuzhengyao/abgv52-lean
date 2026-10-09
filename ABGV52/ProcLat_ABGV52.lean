/-
  ABGV-5.2 —— **C 轨（Procesi）· M1：修正格 M₂ = M ⊕ U 与秩账（p⁴+1）**

  任务规格 = `wiki/proj-ABGV52-formalize-procesi.md` §3.2 T1（M1 里程碑）。
  **口径**：蓝图 T1 已按**第三十二改后**的修正 C′ 写就（§1.3-(ii)）——
  格为 `M₂ := M ⊕ U`（`M = ker φ`，`U = ℤ[Ω]`），秩 `p⁴+1`（p=3 时 82）；
  `M` 自身的秩 `p⁴−p²+1`（p=3 时 73）作为**分量读数**保留（论文 `:683`
  的 `rk_ℤ M = 73` 本身为真）。本件即按该口径形式化，逐条见 §1–§6。

  为何不用字面 73 作 M₂：`rem:procesi-geometric` 的原字面陈述
  `Z_H(F,9) ≅ F(M|_H)^H`（rk 73）与中心定理的来源（Saltman1999ch14
  `thm:14.17` ＋ 其 Remark `(r-1)n²+1`；Formanek2002 印刷 p.314）
  矛盾——trdeg 应为 n²+1 = 82；修正为 M₂ = M ⊕ U 后秩账 73 + 9 = 82 闭合
  （Saltman `lem:14.18`；Beneish1998 `:71` 的 `G_n ⊕ U_n ⊕ U_n` 同款）。
  本件 `finrank_Mp2` 机器核验的正是这条修正秩账。

  数学路线（§3，不依赖几何侧 M4–M6）：
    * ℤ-侧正合 `range φ = ker ε`（G1b 已证 `range_phiFun_eq`）；
    * ℚ 平坦于 ℤ（BR 的 `instFlatZQ`）⟹ `lTensor` 保持正合（`Module.Flat.lTensor_exact`）；
    * 两次 rank-nullity：`finrank (ker ε_ℚ) = p² − 1`、`finrank (ker φ_ℚ) = p⁴ − (p² − 1)`；
    * 自由桥 `ℚ ⊗[ℤ] ℤ[Ω] ≃ (Ω →₀ ℚ)`（BR §3 模式）读 `finrank ℚ (ℚ ⊗ Z[Ω]) = p²`；
    * `commUpgrade` ＋ `tensorKerEquiv` 换回字面对象 `ker φ ⊗[ℤ] ℚ`。

  载体实现说明（与蓝图写法的两处偏差，均已在报告中说明）：
    * 蓝图写 `⊕`；本版 mathlib 的 `Sum` 上无 `AddCommGroup` 实例，双积在
      `Type` 层由 `Prod`（`×`）承载——即范畴论意义上的双积同款对象；
    * `Mp2` 用 `abbrev`（非 `def`）：实例解析需在 reducible 透明度展开
      （与 G1b 的 `ZOm`／`U` 同风格）；定义外形不变（§4 的 `rfl` 锁定）。

  本件不触碰几何侧（M4–M6）：M5/M6 是本体难点，M1–M3 独立有用
  （论文实际消费的稳定形 C″ 只需 M1–M3）。
  **无 sorry、无自造公理**（§7 公理闸门）。
-/
import ABGV52.BR_ABGV52
import ABGV52.G1b_ABGV52
import Mathlib.LinearAlgebra.TensorProduct.Prod

open scoped TensorProduct
open TensorProduct

namespace ABGV52.ProcLat

variable (p : ℕ) [Fact p.Prime]

/-! ## §1 自由桥与秩读数 -/

/-- 系数层中转（BR §3 同式）：`ℚ ⊗[ℤ] ℤ[Ω] ≃ₗ[ℚ] ℚ ⊗[ℤ] (Ω →₀ ℤ)`
（经 `coeffLinearEquiv` 换到 `Finsupp` 侧）。 -/
noncomputable def bridgeUAux :
    ℚ ⊗[ℤ] G.ZOm p ≃ₗ[ℚ] ℚ ⊗[ℤ] (G.OmegaP p →₀ ℤ) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (MonoidAlgebra.coeffLinearEquiv ℤ)).extendScalarsOfIsLocalization
    (nonZeroDivisors ℤ) ℚ

/-- 自由桥：`ℚ ⊗[ℤ] ℤ[Ω] ≃ₗ[ℚ] (Ω →₀ ℚ)`（两侧均 `p²` 维）。 -/
noncomputable def bridgeU : ℚ ⊗[ℤ] G.ZOm p ≃ₗ[ℚ] (G.OmegaP p →₀ ℚ) :=
  (bridgeUAux p).trans (TensorProduct.finsuppScalarRight ℤ ℚ ℚ (G.OmegaP p))

/-- 双张量分配桥（异基 `distribBaseChange`）：
`ℚ ⊗[ℤ] (ℤ[Ω] ⊗ ℤ[Ω]) ≃ₗ[ℚ] (ℚ ⊗ ℤ[Ω]) ⊗[ℚ] (ℚ ⊗ ℤ[Ω])`。 -/
noncomputable def eDom : ℚ ⊗[ℤ] (G.ZOm p ⊗[ℤ] G.ZOm p) ≃ₗ[ℚ]
    (ℚ ⊗[ℤ] G.ZOm p) ⊗[ℚ] (ℚ ⊗[ℤ] G.ZOm p) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ (G.ZOm p) (G.ZOm p)

omit [Fact (Nat.Prime p)] in
/-- 秩读数：`finrank ℚ (ℚ ⊗[ℤ] ℤ[Ω]) = p²`（`Ω = Fin (p·p)`）。 -/
theorem finrank_tensorU : Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm p) = p * p := by
  rw [LinearEquiv.finrank_eq (bridgeU p), Module.finrank_finsupp_self ℚ]
  simp [G.OmegaP]

omit [Fact (Nat.Prime p)] in
/-- 秩读数：`finrank ℚ (ℚ ⊗[ℤ] (ℤ[Ω] ⊗ ℤ[Ω])) = (p²)·(p²)`（写成乘积形，§3 直接消费）。 -/
theorem finrank_tensorUU :
    Module.finrank ℚ (ℚ ⊗[ℤ] (G.ZOm p ⊗[ℤ] G.ZOm p)) = p * p * (p * p) := by
  rw [LinearEquiv.finrank_eq (eDom p), Module.finrank_tensorProduct, finrank_tensorU]

/-! ## §2 有限维转运（rank-nullity 与 finrank_prod 的实例前提） -/

/-- `ℚ ⊗[ℤ] ℤ[Ω]` 有限维（沿 `bridgeU` 自 `(Ω →₀ ℚ)` 转运）。 -/
noncomputable instance instFiniteDimensionalTensorU : FiniteDimensional ℚ (ℚ ⊗[ℤ] G.ZOm p) :=
  (bridgeU p).symm.finiteDimensional

/-- `ℚ ⊗[ℤ] (ℤ[Ω] ⊗ ℤ[Ω])` 有限维（沿 `eDom` 自双重张积转运）。 -/
noncomputable instance instFiniteDimensionalTensorUU :
    FiniteDimensional ℚ (ℚ ⊗[ℤ] (G.ZOm p ⊗[ℤ] G.ZOm p)) :=
  (eDom p).symm.finiteDimensional

/-- `ℚ ⊗[ℤ] ker φ` 有限维（沿 `tensorKerEquiv` 自核子模转运）。 -/
noncomputable instance instFiniteDimensionalTensorKer :
    FiniteDimensional ℚ (ℚ ⊗[ℤ] ↥(LinearMap.ker (G.phiFun p))) :=
  (LinearMap.tensorKerEquiv ℚ ℚ (G.phiFun p)).symm.finiteDimensional

/-! ## §3 主秩引理：`finrank ℚ (ker φ ⊗[ℤ] ℚ) = p⁴ − p² + 1` -/

/-- **M 的 ℚ-秩**：`Module.finrank ℚ (↥(ker φ) ⊗[ℤ] ℚ) = p⁴ − p² + 1`（p=3 时 73）。

路线（蓝图 §3.2 T1 的「ℚ-基变换 ＋ rank-nullity ＋ 显式算 `range`」）：
ℤ-侧 `range φ = ker ε`（G1b `range_phiFun_eq`）⟹ ℚ 平坦 ⟹ ℚ-侧正合；
第一次 rank-nullity：`finrank (ker ε_ℚ) = p² − 1`（`range ε_ℚ = ⊤`，靶秩 1）；
第二次 rank-nullity：`finrank (ker φ_ℚ) = p²·p² − (p² − 1)`；
最后由 `commUpgrade` ＋ `tensorKerEquiv` 把 `ker φ_ℚ` 换成 `↥(ker φ) ⊗[ℤ] ℚ`。 -/
theorem finrank_ker_phiFun :
    Module.finrank ℚ (↥(LinearMap.ker (G.phiFun p)) ⊗[ℤ] ℚ) = p ^ 4 - p ^ 2 + 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- (0) ℤ-侧正合：`range φ = ker ε`
  have hZ : Function.Exact (G.phiFun p) (G.augF p) :=
    LinearMap.exact_iff.mpr (G.range_phiFun_eq p).symm
  -- (1) ℚ 平坦于 ℤ ⟹ `lTensor` 保持正合
  have hQ : Function.Exact (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun p))
      (AlgebraTensorModule.lTensor ℚ ℚ (G.augF p)) :=
    Module.Flat.lTensor_exact ℚ hZ
  have hker : LinearMap.ker (AlgebraTensorModule.lTensor ℚ ℚ (G.augF p))
      = LinearMap.range (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun p)) :=
    LinearMap.exact_iff.mp hQ
  -- (2) 增广 ℚ-侧满射（`single ω₀` 截面）⟹ `range` 为全空间，靶 = `ℚ ⊗[ℤ] ℤ`（秩 1）
  have hsurj : Function.Surjective (AlgebraTensorModule.lTensor ℚ ℚ (G.augF p)) :=
    LinearMap.lTensor_surjective ℚ (fun n =>
      ⟨MonoidAlgebra.single (G.omega0 p) n, G.augF_single p (G.omega0 p) n⟩)
  have hrange1 : Module.finrank ℚ
      (LinearMap.range (AlgebraTensorModule.lTensor ℚ ℚ (G.augF p))) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top ℚ (ℚ ⊗[ℤ] ℤ),
      LinearEquiv.finrank_eq (AlgebraTensorModule.rid ℤ ℚ ℚ), Module.finrank_self]
  -- (3) rank-nullity（ε）：`finrank (ker ε_ℚ) = p² − 1`
  have hker1 : Module.finrank ℚ (LinearMap.ker (AlgebraTensorModule.lTensor ℚ ℚ (G.augF p)))
      = p * p - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (AlgebraTensorModule.lTensor ℚ ℚ (G.augF p))
    rw [hrange1, finrank_tensorU] at h
    omega
  -- (4) 经正合性换算：`finrank (range φ_ℚ) = p² − 1`
  have hrange2 : Module.finrank ℚ
      (LinearMap.range (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun p))) = p * p - 1 := by
    rw [← hker]
    exact hker1
  -- (5) rank-nullity（φ）：`finrank (ker φ_ℚ) = p²·p² − (p² − 1)`
  have hker2 : Module.finrank ℚ
      (LinearMap.ker (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun p)))
      = p * p * (p * p) - (p * p - 1) := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun p))
    rw [hrange2, finrank_tensorUU] at h
    omega
  -- (6) 换回字面对象并化简算术：`(p²)·(p²) − (p² − 1) = p⁴ − p² + 1`
  calc Module.finrank ℚ (↥(LinearMap.ker (G.phiFun p)) ⊗[ℤ] ℚ)
      = Module.finrank ℚ (ℚ ⊗[ℤ] ↥(LinearMap.ker (G.phiFun p))) :=
        LinearEquiv.finrank_eq (BR.commUpgrade ↥(LinearMap.ker (G.phiFun p)))
    _ = Module.finrank ℚ ↥(LinearMap.ker (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun p))) :=
        LinearEquiv.finrank_eq (LinearMap.tensorKerEquiv ℚ ℚ (G.phiFun p))
    _ = p * p * (p * p) - (p * p - 1) := hker2
    _ = p ^ 4 - p ^ 2 + 1 := by
        have h4 : p * p * (p * p) = p ^ 4 := by ring
        have hs : p * p = p ^ 2 := (pow_two p).symm
        have h1 : 1 ≤ p ^ 2 := by nlinarith
        have h2 : p ^ 2 ≤ p ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        rw [h4, hs]
        omega

/-! ## §4 修正格 `M₂ = M ⊕ U`（C′ 精确形）与 `G`-作用 -/

/-- **修正格**（蓝图 §1.3-(ii) 的 C′）：`M₂ = ker φ × ℤ[Ω]`，秩 `p⁴+1`。

载体：蓝图写 `⊕`；本版 mathlib 的 `Sum` 上无 `AddCommGroup` 实例，
双积由 `Prod`（`×`）承载（`AddCommGroup`／`Module ℤ` 逐分量）。 -/
abbrev Mp2 : Type := ↥(LinearMap.ker (G.phiFun p)) × G.ZOm p

/-- 类型锁定（`rfl`）：`Mp2 p` 的定义外形 = `ker φ × ℤ[Ω]`。 -/
example : Mp2 p = (↥(LinearMap.ker (G.phiFun p)) × G.ZOm p) := rfl

/-- `Mp2` 上的 `G`-作用：第一分量用 G1b 的 `ker φ` 作用，第二分量用 `U` 的 `ρ`。 -/
noncomputable instance instSMulMp2 : SMul (G.Gp p) (Mp2 p) :=
  ⟨fun g x => (g • x.1, (G.U p).ρ g x.2)⟩

/-- 作用公式（展开引理，`rfl` 级）。 -/
lemma smul_Mp2_apply (g : G.Gp p) (x : Mp2 p) :
    g • x = (g • x.1, (G.U p).ρ g x.2) := rfl

/-- `Mp2` 上的 `DistribMulAction`（逐分量验证；乘法律用 `Rep.ρ_mul`）。 -/
noncomputable instance instDistribMulActionMp2 : DistribMulAction (G.Gp p) (Mp2 p) where
  smul := (instSMulMp2 p).smul
  one_smul x := by
    refine Prod.ext ?_ ?_
    · show (1 : G.Gp p) • x.1 = x.1
      exact one_smul _ _
    · show (G.U p).ρ (1 : G.Gp p) x.2 = x.2
      rw [map_one]
      rfl
  mul_smul a b x := by
    refine Prod.ext ?_ ?_
    · show (a * b) • x.1 = a • (b • x.1)
      exact mul_smul a b x.1
    · show (G.U p).ρ (a * b) x.2 = (G.U p).ρ a ((G.U p).ρ b x.2)
      rw [Rep.ρ_mul]
      rfl
  smul_zero g := by
    refine Prod.ext ?_ ?_
    · show g • (0 : ↥(LinearMap.ker (G.phiFun p))) = 0
      exact smul_zero g
    · show (G.U p).ρ g (0 : G.ZOm p) = 0
      exact map_zero _
  smul_add g x y := by
    refine Prod.ext ?_ ?_
    · show g • (x.1 + y.1) = g • x.1 + g • y.1
      exact smul_add g x.1 y.1
    · show (G.U p).ρ g (x.2 + y.2) = (G.U p).ρ g x.2 + (G.U p).ρ g y.2
      exact map_add _ _ _

/-- **修正格作为 `Rep ℤ G`**（M1 的装配目标；M2 起经 `D1` 的 `latticeAlgebra` 消费）。 -/
noncomputable def Mp2Rep : Rep ℤ (G.Gp p) :=
  Rep.ofDistribMulAction ℤ (G.Gp p) (Mp2 p)

/-! ## §5 修正格的秩账：`finrank ℚ (M₂ ⊗[ℤ] ℚ) = p⁴ + 1` -/

/-- **M₂ 的 ℚ-秩**：`Module.finrank ℚ (Mp2 p ⊗[ℤ] ℚ) = p⁴ + 1`（p=3 时 82）。

秩账 = 分量之和：`(p⁴−p²+1) + p² = p⁴+1`（C′ 的核心读数 `73 + 9 = 82`）。 -/
theorem finrank_Mp2 : Module.finrank ℚ (Mp2 p ⊗[ℤ] ℚ) = p ^ 4 + 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hkerQ : Module.finrank ℚ (ℚ ⊗[ℤ] ↥(LinearMap.ker (G.phiFun p)))
      = p ^ 4 - p ^ 2 + 1 :=
    (LinearEquiv.finrank_eq (BR.commUpgrade ↥(LinearMap.ker (G.phiFun p)))).symm.trans
      (finrank_ker_phiFun p)
  calc Module.finrank ℚ (Mp2 p ⊗[ℤ] ℚ)
      = Module.finrank ℚ ((ℚ ⊗[ℤ] ↥(LinearMap.ker (G.phiFun p)))
          × (ℚ ⊗[ℤ] G.ZOm p)) :=
        LinearEquiv.finrank_eq ((BR.commUpgrade (Mp2 p)).trans
          (TensorProduct.prodRight ℤ ℚ ℚ _ _))
    _ = Module.finrank ℚ (ℚ ⊗[ℤ] ↥(LinearMap.ker (G.phiFun p)))
          + Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm p) := Module.finrank_prod
    _ = (p ^ 4 - p ^ 2 + 1) + p * p := by rw [hkerQ, finrank_tensorU]
    _ = p ^ 4 + 1 := by
        have hmle : p ^ 2 ≤ p ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have hs : p * p = p ^ 2 := (pow_two p).symm
        rw [hs, add_assoc, add_comm (1 : ℕ) (p ^ 2), ← add_assoc,
          Nat.sub_add_cancel hmle]

/-! ## §6 p = 3 特化（分量 9、M 秩 73、M₂ 秩 82） -/

section P3

/-- 本节局部实例：`3` 是素数（`Nat.prime_three`）。 -/
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- p = 3：分量 `ℚ ⊗[ℤ] ℤ[Ω]` 的秩 = 9（即 `p²`；`3 * 3` 与 `9` 定义相等）。 -/
theorem finrank_tensorU_three : Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3) = 9 :=
  finrank_tensorU 3

/-- p = 3：**M 的秩 = 73**（= `3⁴ − 3² + 1`；论文 `:683` 的 `rk_ℤ M = 73` 读数）。 -/
theorem finrank_ker_phiFun_three :
    Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ) = 73 := by
  have h := finrank_ker_phiFun 3
  norm_num at h
  exact h

/-- p = 3：**M₂ = M ⊕ U 的秩 = 82**（修正 C′ 的秩账 `73 + 9 = 82 = n² + 1`，n = 9）。 -/
theorem finrank_Mp2_three : Module.finrank ℚ (Mp2 3 ⊗[ℤ] ℚ) = 82 := by
  have h := finrank_Mp2 3
  norm_num at h
  exact h

end P3

/-! ## §7 公理闸门 -/

#print axioms bridgeUAux
#print axioms bridgeU
#print axioms eDom
#print axioms finrank_tensorU
#print axioms finrank_tensorUU
#print axioms instFiniteDimensionalTensorU
#print axioms instFiniteDimensionalTensorUU
#print axioms instFiniteDimensionalTensorKer
#print axioms finrank_ker_phiFun
#print axioms Mp2
#print axioms instSMulMp2
#print axioms smul_Mp2_apply
#print axioms instDistribMulActionMp2
#print axioms Mp2Rep
#print axioms finrank_Mp2
#print axioms finrank_tensorU_three
#print axioms finrank_ker_phiFun_three
#print axioms finrank_Mp2_three

end ABGV52.ProcLat
