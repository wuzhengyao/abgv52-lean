/-
  ABGV-5.2 —— EM 判据（论文 `thm:endo-miyata`）一般陈述的反例 · 机器核证
  ====================================================================

  ## 0. 路线对齐（必读）

  * 论文侧依据（逐字，**第四十二改前版本** `raw/ABGV-5.2-resolution.pre42.tex`；
    rev42 已依本件结论把该定理改序列形——见 `wiki/proj-ABGV52-EM-criterion-correction.md`）：
    - `thm:endo-miyata`（行 554–566）：设 `G` 有限、`M` 是 `G` 忠实作用的
      `ℤ[G]`-格、`F` 特征零；若 `F(M)^G` 在 `F` 上稳定有理，则 `M` 是
      稳定置换格。
    - 「稳定置换」按 `def:lattice`（行 450–462）之定义：`∃ P Q` 置换格，
      `M ⊕ P ≅ Q`。本文件用 D1 的 `IsStablyPermutation C2 M` 承载，其定义
      逐字为 `∃ P Q, IsPermutationLattice G P ∧ IsPermutationLattice G Q ∧
      Nonempty (M ⊞ P ≅ Q)`。
    - 论文对该判据的自然语言「证明」：**无**——原文自陈（行 573–574）：
      「We use this criterion as a hypothesis; it is not proved in this
      paper.」⟹ 本文件**不是**对论文任何一条证明的形式化；它是**对论文
      逐字陈述（在 `def:lattice` 的 ⊕-读法下、按原文一般性：任意有限 `G`、
      char 0）的反例的机器核证**。

  * 反例：`G = C₂ = Multiplicative (ZMod 2)`；`M = ℤ` 带符号作用
    `σ : m ↦ −m`（忠实，§1）；`F = ℚ`。`F(M) = Frac ℚ[ℤ] ≅ ℚ(x^{±1})`，
    `σ·x = x⁻¹`，`F(M)^G = ℚ(x + x⁻¹) ≅ ℚ(t)`（§5；先证 `IsRational`
    —— 比论文假设「稳定有理」更强，见偏差 D1）。

  * 非稳定置换装置 = `(1−σ)`-商不变量 `Q(L) := L ⧸ (1−σ)L`：
    `Q(置换格)` 无挠，而 `Q(sgn)` 含 2-挠（`w₀ = inl 1` 的类）。§2–§4 以
    「系数/反对称」形式落地该论证（与「Q 的函子性 + Q(sgn) = ℤ/2 vs
    无挠」的不变量写法互推，见 §4 注释与偏差 D5）。

  ## 1. 偏差登记（逐条，均不静默弱化）

  D1. 本件证的是**更强**的反例形式：`F(M)^G` 的 `IsRational`（而非仅
      `IsStablyRational`）。由 D1 的 `IsRational.isStablyRational`，
      稳定有理假设 a fortiori 成立 ⟹ 反驳成立。
  D2. 符号作用以逐点 if-式给出（`1 ↦ id`、`τ ↦ −id`），实现分两层：
      `sgnLM`（线性映射层）＋ `sgnRho := MonoidHom`（乘法层）。未采用的
      等价路线：经单位群 `ℤˣ` 的符号 `sgn : C₂ →* ℤˣ` 再合成 `Units`-作用；
      两路线在载体 `ℤ` 上逐点相同（`↑(−1 : ℤˣ) = −1`），可互推。
  D3. 论文行号按 **pre42 版本**（第四十二改前）：`def:lattice` :450–462；
      `thm:endo-miyata` :554–566；「as a hypothesis」句 :573–574。（rev42 后
      分别为 :447–464／:567／:587–588；本件反例所针对之 ⊕-形陈述即 pre42 文面，
      rev42 之举出与修正正以本件为据。）
  D4. 接口偏差：主定理（§6）的 ∃-语句额外携带
      `(_ : UniqueProds (Multiplicative ↥M))`——D1 的 `latticeInvariants`
      变量块以此为实例（Frac 模型所需）；对 `sgnRep`（载体 `ℤ`）由 `ℤ` 的
      `UniqueSums` 实例自动满足，数学内容无变更。（§6 已按此实现：
      `em_criterion_refuted` 逐字携带此 binder。）
  D5. 不变量「部件 (a)–(e)」以系数形式落地：(a) 函子性落为 §2 的
      `hom_maps_invSub` ＋ §3 的系数搬运；(b)(c)(d) 合并为 §3/§4 的系数
      命题——置换格侧的同构把 `sgnRep` 侧的 2-挠元素提到 `1 = 2x` 的算术
      矛盾（§4 末）。互推关系见 §4 注释。
  D6. `set_option linter.style.haveILetI false`、`linter.unusedSectionVars
      false`（与 EMRouteS/EMConsume 同款）；`attribute [local instance 2000]
      Rep.hV2`（`⊞` 与 `ℤ`-module 结构统一，同款）。无 `maxHeartbeats`
      偏差（未使用）。
  D7. 交付状态：**§1–§6 全部交付**——§1–§4（`sgnRep` 忠实 ＋
      `¬ IsStablyPermutation C2 sgnRep`）；§5（`F(M)^G` 的 `IsRational`：
      `isRational_invariantsIF` 与 `isRational_invariantsAlg` 两形，
      载体 `rfl`-相等）；§6（∃-主定理 `em_criterion_refuted`）。原计划
      [α]–[ε] 中 [α]/[β] 的 `toLaurent` ＋二次塔路线与 [δ] 的 Chebyshev
      对称化路线**未采用**，实际路线 = 直接系数提取（`algY` 幂二项展开的
      `aeval` 系数读数 ⟹ `transcendental_algY`，经
      `IsFractionRing.injective` 提升为 `transcendental_fY`）＋ `Vsub`
      装置（`Fy`-坐标显式化，闭合 [δ]）＋ `aevalEquivField`（[γ]/[ε]）。
      最终公理闸门（文末 §8）全部 ⊆ {propext, Classical.choice,
      Quot.sound}；0 sorry。
  D8. 实现注记（两处局部装置，均在文件内可见）：① `Rep.of` 是 `abbrev`
      （可约），故 `↥sgnRep` 归约为 `ℤ`，类型类搜索无法把
      `RouteS.instDistribMulActionRep` 的 `↥?L` 与 `ℤ` 合一——故在 `sgnRep`
      上**直接声明局部实例** `instDistribMulActionSgnRep : DistribMulAction
      C2 ℤ`（作用 = `sgnRep.ρ`，即 `sgnRho`）；② `MonoidAlgebra.single`
      经 `MonoidAlgebra.coeff_single`（`rfl`）转 `Finsupp.single`，再用
      `Finsupp.single_apply`（避开已弃用的 `coeff_single_apply`）。
  D9. 形态偏差：`IsRational` 的 `K` 以 `↥(latticeInvariantsIF …)`
      （`IntermediateField` 形态，§6 内 `abbrev`）与
      `↥(latticeInvariantsAlg …)`（`Subalgebra` 形态）两形给出——D1 的
      `latticeInvariants` 是 `Subfield`（无 `Algebra ℚ ↥·`），而
      `Subalgebra` 无 `Field ↥·`，故造两形态（载体与 `Subfield` 形逐字
      相同、`rfl`-相等）。主定理用 `Subalgebra` 形：变量 `M` 下
      `IntermediateField` 形触发 `Algebra ℚ ↥·` 合成超时
      （20000 heartbeats）。
  D10. 实现注记（§5–§6 两处装置）：① **ℚ-代数实例歧义＋局部优先级钉**：
      `Algebra ℚ (rationalFunctionField ℚ 1)` 有两个**非定义相等**的实例
      （`DivisionRing.toRatAlgebra` 与 `OreLocalization.instAlgebra`）；
      `AlgEquiv.trans` 的结果类型**重新合成**该实例槽（默认抢先取前者），
      与 `IsRational` 目标（D1 所记录者，后者）不 defeq ⟹ 在
      `section InstancePriorityPin` 内以
      `attribute [local instance 2000] OreLocalization.instAlgebra` 钉住
      （段外自动复原）；② **∃-望远镜 binder 实例性**：主定理
      `∃ (_ : UniqueProds …)` 的 binder 注册为实例，体内
      `IsRational ℚ ↥(latticeInvariantsAlg …)` 方能合成 `Algebra`／`Field`
      （形状测试 `example` 见 §7）。

  ## 2. ⚠-contentious（待用户裁决）

  本件只断言：**`thm:endo-miyata` 的一般陈述（按原文：任意有限 `G`、
  char 0）为假**。论文主线所用特例（`H = C₃ × C₃`、`M|_H`）的结论**另论**。
  **不得**读作「论文主定理为假」——论文主定理的特例断言与判据作为假设的
  使用，均不受本件影响。
-/
import ABGV52.EMRouteS_ABGV52
import ABGV52.EMConsume_ABGV52
import ABGV52.EMTrans_ABGV52
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.Algebra.Polynomial.AlgebraMap

open CategoryTheory Limits
open scoped Polynomial

namespace ABGV52

namespace EM

namespace EMCounter

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance 2000] Rep.hV2

/-! ## 0. 反例群 `C₂` 与符号格 `sgnRep` -/

/-- 反例群：`C₂ = Multiplicative (ZMod 2)`。 -/
abbrev C2 : Type := Multiplicative (ZMod 2)

/-- 生成元 `τ ∈ C₂`（对应 `1 ∈ ZMod 2`）。 -/
abbrev tau : C2 := Multiplicative.ofAdd 1

/-- `C₂` 的元素只有 `1` 与 `τ`。 -/
theorem C2_eq_one_or (g : C2) : g = 1 ∨ g = tau := by
  revert g
  decide

/-- `τ ≠ 1`。 -/
theorem tau_ne_one : tau ≠ (1 : C2) := by
  decide

/-- `τ · τ = 1`。 -/
theorem tau_mul_tau : tau * tau = (1 : C2) := by
  decide

/-- `τ⁻¹ = τ`。 -/
theorem tau_inv_eq : tau⁻¹ = tau :=
  inv_eq_of_mul_eq_one_right tau_mul_tau

/-- `τ · (τ · m) = m`（任何 `C₂`-集）。 -/
theorem tau_smul_tau {α : Type*} [MulAction C2 α] (m : α) : tau • (tau • m) = m := by
  rw [← mul_smul, tau_mul_tau, one_smul]

/-- 符号作用的线性映射层：`1 ↦ id`、`τ ↦ −id`（逐点 `m ↦ ±m`）。 -/
def sgnLM (g : C2) : ℤ →ₗ[ℤ] ℤ where
  toFun m := if g = 1 then m else -m
  map_add' a b := by
    show (if g = 1 then a + b else -(a + b))
      = (if g = 1 then a else -a) + (if g = 1 then b else -b)
    by_cases h : g = 1
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, neg_add]
  map_smul' c a := by
    show (if g = 1 then c • a else -(c • a)) = c • (if g = 1 then a else -a)
    by_cases h : g = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, smul_neg]

/-- `sgnLM 1 = id`（逐点）。 -/
theorem sgnLM_apply_one (m : ℤ) : sgnLM 1 m = m := by
  show (if (1 : C2) = 1 then m else -m) = m
  rw [if_pos rfl]

/-- `sgnLM τ = −id`（逐点）。 -/
theorem sgnLM_apply_tau (m : ℤ) : sgnLM tau m = -m := by
  show (if tau = 1 then m else -m) = -m
  rw [if_neg tau_ne_one]

/-- 符号作用 `σ : C₂ →* (ℤ →ₗ[ℤ] ℤ)`：`1 ↦ id`、`τ ↦ −id`。 -/
def sgnRho : C2 →* (ℤ →ₗ[ℤ] ℤ) where
  toFun := sgnLM
  map_one' := by
    apply LinearMap.ext
    intro m
    simp only [sgnLM_apply_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro m
    rcases C2_eq_one_or g with rfl | rfl <;> rcases C2_eq_one_or h with rfl | rfl
    · rw [one_mul]
      change sgnLM 1 m = sgnLM 1 (sgnLM 1 m)
      simp only [sgnLM_apply_one]
    · rw [one_mul]
      change sgnLM tau m = sgnLM 1 (sgnLM tau m)
      simp only [sgnLM_apply_one]
    · rw [mul_one]
      change sgnLM tau m = sgnLM tau (sgnLM 1 m)
      simp only [sgnLM_apply_one]
    · rw [tau_mul_tau]
      change sgnLM 1 m = sgnLM tau (sgnLM tau m)
      simp only [sgnLM_apply_one, sgnLM_apply_tau, neg_neg]

/-- **符号格** `sgn = ℤ`（`τ ↦ −1`）。 -/
abbrev sgnRep : Rep ℤ C2 := Rep.of sgnRho

/-- `C₂` 在 `sgnRep` 载体上的作用。`Rep.of` 是可约 `abbrev`，载体归约为 `ℤ`
⟹ 类型类搜索合不上 `RouteS.instDistribMulActionRep` 的 `↥?L`，故在此直接声明。 -/
local instance instDistribMulActionSgnRep : DistribMulAction C2 ℤ :=
  RouteS.instDistribMulActionRep sgnRep

/-- `τ` 在 `sgnRep` 上按 `−1` 作用（`ρ` 形）。 -/
theorem sgnRep_rho_tau (m : ↥sgnRep) : sgnRep.ρ tau m = -m :=
  sgnLM_apply_tau m

/-- `τ` 在 `sgnRep` 上按 `−1` 作用（`•` 形）。 -/
theorem sgnRep_smul_tau (m : ↥sgnRep) : tau • m = -m :=
  sgnRep_rho_tau m

/-- **`sgnRep` 是忠实 `C₂`-模**（`τ` 在 `1 : ℤ` 上按 `−1` 作用）。 -/
theorem sgnRep_faithful : FaithfulSMul C2 ↥sgnRep :=
  ⟨fun {g₁ g₂} h => by
    rcases C2_eq_one_or g₁ with rfl | rfl <;> rcases C2_eq_one_or g₂ with rfl | rfl
    · rfl
    · exfalso
      have hc := h (1 : ↥sgnRep)
      rw [one_smul, sgnRep_smul_tau] at hc
      have hc' : (1 : ℤ) = -(1 : ℤ) := hc
      omega
    · exfalso
      have hc := h (1 : ↥sgnRep)
      rw [one_smul, sgnRep_smul_tau] at hc
      have hc' : -(1 : ℤ) = (1 : ℤ) := hc
      omega
    · rfl⟩

/-! ## 2. `(1−σ)`-商不变量 `Q(L) = L ⧸ (1−σ)L`：分子与函子性 -/

/-- `Q(L)` 的分子：`(1−σ)`-像子模 `(1−σ)L ⊆ L`。 -/
def invSub (L : Rep ℤ C2) : Submodule ℤ ↥L :=
  LinearMap.range (LinearMap.id - L.ρ tau)

/-- 成员判定：`x ∈ (1−σ)L ↔ ∃ y, y − σ y = x`。 -/
theorem mem_invSub_iff (L : Rep ℤ C2) (x : ↥L) :
    x ∈ invSub L ↔ ∃ y : ↥L, y - L.ρ tau y = x := by
  rw [invSub, LinearMap.mem_range]
  exact exists_congr fun y => by rw [LinearMap.sub_apply, LinearMap.id_apply]

/-- **函子性 (a)**：格同构把 `(1−σ)L` 送进 `(1−σ)L′`（⟹ `Q` 在 `Rep` 上
函子性；沿同构为满射即 `Q(L) ≃+ Q(L′)` 的一半）。 -/
theorem hom_maps_invSub {L L' : Rep ℤ C2} (φ : L ⟶ L') {x : ↥L}
    (hx : x ∈ invSub L) : φ.hom x ∈ invSub L' := by
  rw [mem_invSub_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨φ.hom y, ?_⟩
  rw [map_sub, Rep.hom_comm_apply φ tau y]

/-! ## 3. 系数层：`ρ τ` 的系数搬运与反对称性 -/

section QuotientLemmas

variable {X : Type*} [Fintype X] [MulAction C2 X]

/-- `ρ τ` 在单项式基上的作用：`x^m ↦ x^{τ·m}`。 -/
theorem rho_tau_single (x : X) (r : ℤ) :
    (Rep.ofMulAction ℤ C2 X).ρ tau (MonoidAlgebra.single x r)
      = MonoidAlgebra.single (tau • x) r :=
  Representation.ofMulAction_single tau x r

/-- `ρ τ` 的系数搬运：`(ρ τ f).coeff m = f.coeff (τ·m)`。 -/
theorem coeff_rho_tau (f : MonoidAlgebra ℤ X) (m : X) :
    ((Rep.ofMulAction ℤ C2 X).ρ tau f).coeff m = f.coeff (tau • m) := by
  classical
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add]
      simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
  | single x r =>
      rw [show (Rep.ofMulAction ℤ C2 X).ρ tau (MonoidAlgebra.single x r)
            = MonoidAlgebra.single (tau • x) r from rho_tau_single x r,
        MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : tau • x = m
      · rw [if_pos h, if_pos (show x = tau • m by rw [← h, tau_smul_tau])]
      · rw [if_neg h, if_neg (show ¬(x = tau • m) by
          intro hx
          exact h (by rw [hx, tau_smul_tau]))]

/-- **`(1−σ)`-像的系数反对称性**：`y ∈ (1−σ)ℤ[X] ⟹
y.coeff (τ·m) = −y.coeff m`。 -/
theorem coeff_anti_of_mem_invSub {y : MonoidAlgebra ℤ X}
    (hy : y ∈ invSub (Rep.ofMulAction ℤ C2 X)) (m : X) :
    y.coeff (tau • m) = -y.coeff m := by
  obtain ⟨u, hu⟩ := (mem_invSub_iff (Rep.ofMulAction ℤ C2 X) y).mp hy
  have h1 : u.coeff m - u.coeff (tau • m) = y.coeff m := by
    have h := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff m) hu
    rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_rho_tau u m] at h
    exact h
  have h2 : u.coeff (tau • m) - u.coeff m = y.coeff (tau • m) := by
    have h := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff (tau • m)) hu
    rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_rho_tau u (tau • m),
      tau_smul_tau] at h
    exact h
  omega

/-- **反向**：系数反对称的 `y` 必属于 `(1−σ)`-像。构造取
`u.coeff m = y.coeff m`（`m` 为轨道代表元）否则 `0`；轨道分解只有
「`m = rep m`」与「`τ·m = rep m`」两种情形。 -/
theorem exists_sub_of_coeff_anti {y : MonoidAlgebra ℤ X}
    (h : ∀ m : X, y.coeff (tau • m) = -y.coeff m) :
    ∃ u : MonoidAlgebra ℤ X,
      u - (Rep.ofMulAction ℤ C2 X).ρ tau u = y := by
  classical
  let rep : X → X := fun m =>
    Quotient.out (Quotient.mk'' m : Quotient (MulAction.orbitRel C2 X))
  have rep_mem_orbit : ∀ m : X, m ∈ MulAction.orbit C2 (rep m) := fun m => by
    have h1 : (Quotient.mk'' m : Quotient (MulAction.orbitRel C2 X))
        = Quotient.mk'' (rep m) :=
      (Quotient.out_eq' (Quotient.mk'' m : Quotient (MulAction.orbitRel C2 X))).symm
    exact MulAction.orbitRel_apply.mp (Quotient.exact' h1)
  have hcover : ∀ m : X, m = rep m ∨ tau • m = rep m := fun m => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (rep_mem_orbit m)
    rcases C2_eq_one_or g with rfl | rfl
    · exact Or.inl (by simpa using hg.symm)
    · refine Or.inr ?_
      calc tau • m = tau • (tau • rep m) := by rw [hg]
        _ = rep m := tau_smul_tau (rep m)
  have rep_const : ∀ m : X, rep (tau • m) = rep m := fun m => by
    have h1 : (Quotient.mk'' (tau • m) : Quotient (MulAction.orbitRel C2 X))
        = Quotient.mk'' m :=
      Quotient.sound'
        ((MulAction.orbitRel_apply).mpr (MulAction.mem_orbit_iff.mpr ⟨tau, rfl⟩))
    exact congrArg Quotient.out h1
  let u : MonoidAlgebra ℤ X := MonoidAlgebra.ofCoeff
    (Finsupp.equivFunOnFinite.symm fun m : X =>
      if m = rep m then y.coeff m else 0)
  have u_coeff : ∀ m : X, u.coeff m = (if m = rep m then y.coeff m else 0) :=
    fun m => rfl
  refine ⟨u, ?_⟩
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_rho_tau u m,
    u_coeff m, u_coeff (tau • m)]
  by_cases hmR : m = rep m
  · by_cases hτ : tau • m = rep m
    · have h2 : tau • m = m := hτ.trans hmR.symm
      have h1 : y.coeff (tau • m) = -y.coeff m := h m
      rw [if_pos hmR, if_pos (show tau • m = rep (tau • m) by
        rw [rep_const m]; exact hτ)]
      rw [h2] at h1 ⊢
      omega
    · rw [if_pos hmR, if_neg (show ¬(tau • m = rep (tau • m)) by
        rw [rep_const m]; exact hτ)]
      ring
  · have hτ : tau • m = rep m := (hcover m).resolve_left hmR
    rw [if_neg hmR, if_pos (show tau • m = rep (tau • m) by
      rw [rep_const m]; exact hτ)]
    have h1 : y.coeff (tau • m) = -y.coeff m := h m
    omega

/-- 系数反对称 ⟹ `y ∈ (1−σ)`-像（装配形）。 -/
theorem mem_invSub_of_coeff_anti {y : MonoidAlgebra ℤ X}
    (h : ∀ m : X, y.coeff (tau • m) = -y.coeff m) :
    y ∈ invSub (Rep.ofMulAction ℤ C2 X) := by
  obtain ⟨u, hu⟩ := exists_sub_of_coeff_anti h
  exact (mem_invSub_iff (Rep.ofMulAction ℤ C2 X) y).mpr ⟨u, hu⟩

end QuotientLemmas

/-! ## 4. `sgnRep` 不是稳定置换格

  **与不变量写法 (a)–(e) 的互推（偏差 D5 的说明）**：
  设 `e : sgnRep ⊞ P ≅ ℤ[X]`（`Q = ℤ[X]` 置换格）、`w₀ = inl 1`。则
  ① `σ·w₀ = −w₀`（§1）；② 沿 `e` 推到 `f ∈ ℤ[X]`：系数满足反对称
  `f.coeff (τ·m) = −f.coeff m`（§3 `coeff_rho_tau`）；③ 反向构造
  `u − σu = f`（§3 `exists_sub_of_coeff_anti`——它正是「`(1−σ)ℤ[X]`
  含所有反对称元」，即 `Q(ℤ[X])` 无挠在系数层的等价形式）；④ 沿 `e⁻¹`
  推回并用 `fst`：`fst w₀ = 1 = 2·fst(e⁻¹u)`，在 `ℤ` 中不可能。
  不变量写法（`Q(sgn) = ℤ/2` 经 `Q(P) ≅ Q(ℤ[X])` 无挠）的每一步在此都有
  对应：§2 `hom_maps_invSub` = 函子性 (a)，§3 两条系数引理 = (b)(c)(d)
  的合并形式，§4 末 = (e) 装配。两写法推出同一结论
  `¬ IsStablyPermutation`，故可互推。 -/

/-- **`sgnRep` 非稳定置换**：`sgnRep ⊞ P` 与任何置换格（同构于某
`Rep.ofMulAction ℤ C2 X`）不同构。 -/
theorem sgnRep_not_stablyPermutation : ¬ IsStablyPermutation C2 sgnRep := by
  intro h
  obtain ⟨P, Q, -, hQ, ⟨e⟩⟩ := h
  obtain ⟨X, hXf, hXa, ⟨eX⟩⟩ := hQ
  letI : Fintype X := hXf
  letI : MulAction C2 X := hXa
  let e' : sgnRep ⊞ P ≅ Rep.ofMulAction ℤ C2 X := e ≪≫ eX
  let w₀ : ↥(sgnRep ⊞ P) := (biprod.inl (X := sgnRep) (Y := P)).hom (1 : ↥sgnRep)
  let f : ↥(Rep.ofMulAction ℤ C2 X) := e'.hom.hom w₀
  have hw₀τ : (sgnRep ⊞ P).ρ tau w₀ = -w₀ := by
    rw [show w₀ = (biprod.inl (X := sgnRep) (Y := P)).hom (1 : ↥sgnRep) from rfl,
      ← Rep.hom_comm_apply (biprod.inl (X := sgnRep) (Y := P)) tau (1 : ↥sgnRep),
      sgnRep_rho_tau (1 : ↥sgnRep), map_neg]
  have hfτ : (Rep.ofMulAction ℤ C2 X).ρ tau f = -f := by
    rw [show f = e'.hom.hom w₀ from rfl,
      ← Rep.hom_comm_apply e'.hom tau w₀, hw₀τ, map_neg]
  have hcoeff : ∀ m : X, (f : MonoidAlgebra ℤ X).coeff (tau • m)
      = -((f : MonoidAlgebra ℤ X).coeff m) := by
    intro m
    have hc := congrArg (fun z : ↥(Rep.ofMulAction ℤ C2 X) => z.coeff m) hfτ
    rw [coeff_rho_tau f m, MonoidAlgebra.coeff_neg, Finsupp.neg_apply] at hc
    exact hc
  obtain ⟨g, hg⟩ :=
    exists_sub_of_coeff_anti (y := (f : MonoidAlgebra ℤ X)) hcoeff
  have hw : w₀ = e'.inv.hom g - (sgnRep ⊞ P).ρ tau (e'.inv.hom g) := by
    calc w₀ = e'.inv.hom f := (Iso.hom_inv_id_apply e' w₀).symm
      _ = e'.inv.hom (g - (Rep.ofMulAction ℤ C2 X).ρ tau g) := by rw [hg]
      _ = e'.inv.hom g - e'.inv.hom ((Rep.ofMulAction ℤ C2 X).ρ tau g) := by
            rw [map_sub]
      _ = e'.inv.hom g - (sgnRep ⊞ P).ρ tau (e'.inv.hom g) := by
            rw [Rep.hom_comm_apply]
  have hF := congrArg
    (fun z : ↥(sgnRep ⊞ P) => (biprod.fst (X := sgnRep) (Y := P)).hom z) hw
  rw [map_sub] at hF
  rw [Rep.hom_comm_apply] at hF
  have hw₀fst : (biprod.fst (X := sgnRep) (Y := P)).hom w₀ = 1 := by
    rw [show w₀ = (biprod.inl (X := sgnRep) (Y := P)).hom (1 : ↥sgnRep) from rfl]
    exact Consume.biprod_inl_fst_apply sgnRep P (1 : ↥sgnRep)
  rw [hw₀fst, sgnRep_rho_tau] at hF
  have hFz : (1 : ℤ) = (biprod.fst (X := sgnRep) (Y := P)).hom (e'.inv.hom g)
      + (biprod.fst (X := sgnRep) (Y := P)).hom (e'.inv.hom g) := by
    rw [sub_neg_eq_add] at hF
    exact hF
  omega

/-! ## 5. 公理闸门（§1–§4 已落声明） -/

#print axioms C2_eq_one_or
#print axioms tau_ne_one
#print axioms tau_mul_tau
#print axioms tau_inv_eq
#print axioms tau_smul_tau
#print axioms sgnLM
#print axioms sgnLM_apply_one
#print axioms sgnLM_apply_tau
#print axioms sgnRho
#print axioms sgnRep
#print axioms sgnRep_rho_tau
#print axioms sgnRep_smul_tau
#print axioms sgnRep_faithful
#print axioms invSub
#print axioms mem_invSub_iff
#print axioms hom_maps_invSub
#print axioms rho_tau_single
#print axioms coeff_rho_tau
#print axioms coeff_anti_of_mem_invSub
#print axioms exists_sub_of_coeff_anti
#print axioms mem_invSub_of_coeff_anti
#print axioms sgnRep_not_stablyPermutation

/-! ## 6. §5：`F(M)^G ≅ ℚ(fY)` 的有理性（阶段 1：`R₁`/`K₁` 基础设施）

  路线（与原文计划的 [α]–[ε] 对应见头注 D7）：不经 `toLaurent` 与二次塔，
  改用（i）`algY` 幂的二项展开 ＋ `aeval` 系数读数证 `algY` 超越（[α]/[β]
  合并）；（ii）`IsFractionRing.injective` 提升到 `K₁`；（iii）`Vsub` 装置
  显式化 `Fy`-坐标闭合定点域等式（[δ]）；（iv）`aevalEquivField` 收口
  （[γ]/[ε]）。 -/

-- 实例可用性守卫（`SMulCommClass`／`UniqueProds`，D1 的 `latticeInvariants`
-- 变量块所需）。
example : SMulCommClass C2 ℤ ↥sgnRep := inferInstance
example : UniqueProds (Multiplicative ↥sgnRep) := inferInstance

/-- `ℚ[ℤ]`（符号格 `sgnRep` 的群代数 = Laurent 多项式环）。 -/
abbrev R1 : Type := latticeAlgebra ℚ ↥sgnRep

example : IsDomain R1 := inferInstance

/-- `Frac ℚ[ℤ] = ℚ(x)`（符号格函数域）。 -/
abbrev K1 : Type := latticeFunctionField ℚ ↥sgnRep

example : Field K1 := inferInstance
example : Algebra R1 K1 := inferInstance
example : IsFractionRing R1 K1 := inferInstance

/-! ### R1 层：单项式与幂 -/

def algX : R1 := MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℚ)

def algXi : R1 := MonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) (1 : ℚ)

def algY : R1 := algX + algXi

theorem algX_pow (n : ℕ) : (algX : R1) ^ n
    = MonoidAlgebra.single (Multiplicative.ofAdd (n : ℤ)) 1 := by
  rw [algX, MonoidAlgebra.single_pow, one_pow]
  congr 1
  rw [← ofAdd_nsmul n (1 : ℤ)]
  simp

theorem algXi_pow (n : ℕ) : (algXi : R1) ^ n
    = MonoidAlgebra.single (Multiplicative.ofAdd (-(n : ℤ))) 1 := by
  rw [algXi, MonoidAlgebra.single_pow, one_pow]
  congr 1
  rw [← ofAdd_nsmul n (-1 : ℤ)]
  simp

theorem natCast_single (n : ℕ) :
    ((n : R1)) = MonoidAlgebra.single (1 : Multiplicative ℤ) (n : ℚ) := by
  rw [← map_natCast (algebraMap ℚ R1) n, algebraMap_latticeAlgebra_eq_single]

theorem algX_mul_algXi : (algX : R1) * algXi = 1 := by
  rw [algX, algXi, MonoidAlgebra.single_mul_single, ← ofAdd_add,
    show (1 : ℤ) + (-1) = 0 by norm_num, ofAdd_zero, one_mul,
    ← MonoidAlgebra.one_def]

theorem algXi_mul_algX : (algXi : R1) * algX = 1 := by
  rw [algX, algXi, MonoidAlgebra.single_mul_single, ← ofAdd_add,
    show (-1 : ℤ) + 1 = 0 by norm_num, ofAdd_zero, one_mul,
    ← MonoidAlgebra.one_def]

theorem algY_mul_algX : (algY : R1) * algX = algX * algX + 1 := by
  rw [algY, add_mul, algXi_mul_algX]

/-! ### R1 层：`algY^k` 的二项展开与系数提取 -/

theorem algY_pow (k : ℕ) : (algY : R1) ^ k
    = ∑ m ∈ Finset.range (k + 1),
        MonoidAlgebra.single (Multiplicative.ofAdd ((m : ℤ) - ((k - m : ℕ) : ℤ)))
          ((k.choose m : ℚ)) := by
  rw [algY, add_pow]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [algX_pow m, algXi_pow (k - m), natCast_single (k.choose m),
    MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, ← ofAdd_add]
  congr 1
  · simp only [mul_one, sub_eq_add_neg]
  · ring

theorem coeff_algY_pow_of_lt {i N : ℕ} (h : i < N) :
    ((algY : R1) ^ i).coeff (Multiplicative.ofAdd (-(N : ℤ))) = 0 := by
  rw [algY_pow i, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply,
    if_neg (by
      intro hc
      have hc' := congrArg Multiplicative.toAdd hc
      simp only [toAdd_ofAdd] at hc'
      have hb' : b ≤ i := by
        have := Finset.mem_range.mp hb
        omega
      omega)]

theorem coeff_algY_pow_self (N : ℕ) :
    ((algY : R1) ^ N).coeff (Multiplicative.ofAdd (-(N : ℤ))) = 1 := by
  rw [algY_pow N, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))
    (fun b hb hb0 => by
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply,
        if_neg (by
          intro hc
          have hc' := congrArg Multiplicative.toAdd hc
          simp only [toAdd_ofAdd] at hc'
          have hb' : b ≤ N := by
            have := Finset.mem_range.mp hb
            omega
          omega)])]
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply,
    if_pos (by congr 1; simp)]
  simp

/-! ### R1 层：`aeval` 的系数读数与超越性 -/

theorem aeval_algY_coeff (p : ℚ[X]) :
    (Polynomial.aeval algY p).coeff (Multiplicative.ofAdd (-(p.natDegree : ℤ)))
      = p.leadingCoeff := by
  rw [Polynomial.aeval_eq_sum_range]
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single_of_mem p.natDegree
    (Finset.mem_range.mpr (by omega))]
  · rw [MonoidAlgebra.coeff_smul_apply, coeff_algY_pow_self, smul_eq_mul, mul_one,
      Polynomial.coeff_natDegree]
  · intro b hb hbN
    rw [MonoidAlgebra.coeff_smul_apply, coeff_algY_pow_of_lt (i := b)
      (N := p.natDegree) (by
        have := Finset.mem_range.mp hb
        omega), smul_zero]

theorem transcendental_algY : Transcendental ℚ (algY : R1) := by
  rw [transcendental_iff]
  intro p hp
  by_contra hp0
  have hc := aeval_algY_coeff p
  rw [hp] at hc
  simp only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp0) hc.symm

/-! ### K1 层：分式域中的 `x, x⁻¹, y = x + x⁻¹` -/

def fX : K1 := algebraMap R1 K1 algX

def fXi : K1 := algebraMap R1 K1 algXi

def fY : K1 := algebraMap R1 K1 algY

theorem fY_eq : fY = fX + fXi := by
  rw [fY, fX, fXi, algY, map_add]

theorem fX_mul_fXi : fX * fXi = 1 := by
  rw [fX, fXi, ← map_mul, algX_mul_algXi, map_one]

theorem fXi_mul_fX : fXi * fX = 1 := by
  rw [fX, fXi, ← map_mul, algXi_mul_algX, map_one]

theorem fY_mul_fX : fY * fX = fX * fX + 1 := by
  rw [fY, fX, ← map_mul, algY_mul_algX, map_add, map_mul, map_one]

-- 诊断：`toAlgHom` 与 `algebraMap` 的 defeq 在直接陈述时是否成立
example (x : R1) : (IsScalarTower.toAlgHom ℚ R1 K1) x = algebraMap R1 K1 x := rfl

theorem aeval_fY_eq (p : ℚ[X]) :
    Polynomial.aeval fY p = algebraMap R1 K1 (Polynomial.aeval algY p) := by
  simp only [Polynomial.aeval_eq_sum_range]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Algebra.smul_def]
  rw [map_mul, map_pow, fY, ← IsScalarTower.algebraMap_apply]

theorem transcendental_fY : Transcendental ℚ (fY : K1) := by
  rw [transcendental_iff]
  intro p hp
  have h1 : algebraMap R1 K1 (Polynomial.aeval algY p) = algebraMap R1 K1 0 := by
    rw [map_zero, ← aeval_fY_eq]
    exact hp
  have h2 : Polynomial.aeval algY p = 0 := IsFractionRing.injective R1 K1 h1
  exact transcendental_iff.mp transcendental_algY p h2

theorem algebraicIndependent_fY : AlgebraicIndependent ℚ ![fY] :=
  algebraicIndependent_iff_transcendental.mpr transcendental_fY

/-! ### 系数工具（单项式 = `x^{±n} · 纯量`） -/

theorem single_mul_single_one (m : Multiplicative ℤ) (r : ℚ) :
    MonoidAlgebra.single m (1 : ℚ) * MonoidAlgebra.single (1 : Multiplicative ℤ) r
      = MonoidAlgebra.single m r := by
  rw [MonoidAlgebra.single_mul_single, mul_one, one_mul]

theorem single_ofAdd_of_nonneg {k : ℤ} (h : 0 ≤ k) (r : ℚ) :
    MonoidAlgebra.single (Multiplicative.ofAdd k) r
      = (algX : R1) ^ k.toNat * algebraMap ℚ R1 r := by
  rw [algX_pow, algebraMap_latticeAlgebra_eq_single, ← single_mul_single_one,
    Int.toNat_of_nonneg h]

theorem single_ofAdd_of_neg {k : ℤ} (h : k < 0) (r : ℚ) :
    MonoidAlgebra.single (Multiplicative.ofAdd k) r
      = (algXi : R1) ^ (-k).toNat * algebraMap ℚ R1 r := by
  rw [algXi_pow, algebraMap_latticeAlgebra_eq_single, ← single_mul_single_one,
    show (-((-k).toNat : ℤ)) = k from by
      rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ -k by omega)]
      ring]

/-! ### `τ` 在生成元上的作用 -/

theorem latticeAlgebraEquiv_tau_algX :
    latticeAlgebraEquiv ℚ C2 ↥sgnRep tau algX = algXi := by
  show MonoidAlgebra.mapDomainRingEquiv ℚ (mulEquivOfSMul C2 ↥sgnRep tau)
      (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℚ))
    = MonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) (1 : ℚ)
  rw [MonoidAlgebra.mapDomainRingEquiv_single, mulEquivOfSMul_apply, toAdd_ofAdd,
    sgnRep_smul_tau]

theorem latticeAlgebraEquiv_tau_algXi :
    latticeAlgebraEquiv ℚ C2 ↥sgnRep tau algXi = algX := by
  show MonoidAlgebra.mapDomainRingEquiv ℚ (mulEquivOfSMul C2 ↥sgnRep tau)
      (MonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) (1 : ℚ))
    = MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : ℚ)
  rw [MonoidAlgebra.mapDomainRingEquiv_single, mulEquivOfSMul_apply, toAdd_ofAdd,
    sgnRep_smul_tau]
  simp only [neg_neg]

theorem tau_smul_fX : tau • (fX : K1) = fXi := by
  rw [fX, fXi, latticeAction_algebraMap, latticeAlgebraEquiv_tau_algX]

theorem tau_smul_fXi : tau • (fXi : K1) = fX := by
  rw [fX, fXi, latticeAction_algebraMap, latticeAlgebraEquiv_tau_algXi]

theorem tau_smul_fY : tau • (fY : K1) = fY := by
  rw [fY_eq, smul_add, tau_smul_fX, tau_smul_fXi, add_comm fXi fX]

/-! ### 不变域（`IntermediateField` 形态；见头注 D9）及其生成元 -/

/-- **`F(M)^G` 的 `IntermediateField` 形态**（`Algebra ℚ ↥·` 与 `Field ↥·`
齐备；载体与 `latticeInvariants`（`Subfield` 形态）逐字相同）。 -/
noncomputable abbrev latticeInvariantsIF (M : Rep ℤ C2) [UniqueProds (Multiplicative ↥M)] :
    IntermediateField ℚ (latticeFunctionField ℚ ↥M) :=
  (latticeInvariants ℚ C2 ↥M).toIntermediateField fun c => by
    rw [mem_latticeInvariants_iff]
    intro g
    exact smul_algebraMap_latticeFunctionField (F := ℚ) (G := C2) (M := ↥M) g c

/-- 反例处的简写：`F(M)^G`（`M = sgnRep`）。 -/
noncomputable abbrev sgnLIi : IntermediateField ℚ K1 := latticeInvariantsIF sgnRep

theorem mem_sgnLIi (x : K1) : x ∈ sgnLIi ↔ ∀ g : C2, g • x = x :=
  mem_latticeInvariants_iff (F := ℚ) (G := C2) (M := ↥sgnRep) x

theorem fY_mem_sgnLIi : (fY : K1) ∈ sgnLIi :=
  (mem_sgnLIi fY).mpr fun g => by
    rcases C2_eq_one_or g with rfl | rfl
    · rw [one_smul]
    · exact tau_smul_fY

/-- `Fy = ℚ(fY)`（`fY = fX + fX⁻¹`）。 -/
noncomputable abbrev Fy : IntermediateField ℚ K1 :=
  IntermediateField.adjoin ℚ (Set.range ![fY])

theorem fY_mem_Fy : (fY : K1) ∈ Fy :=
  IntermediateField.subset_adjoin ℚ (Set.range ![fY]) ⟨0, by simp⟩

theorem Fy_le_sgnLIi : Fy ≤ sgnLIi := by
  rw [Fy, IntermediateField.adjoin_le_iff]
  rintro y ⟨i, rfl⟩
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  exact fY_mem_sgnLIi

theorem fX_ne_fXi : (fX : K1) ≠ fXi := by
  intro h
  have h' : algX = algXi := IsFractionRing.injective R1 K1 h
  have hc := congrArg (fun z : R1 => z.coeff (Multiplicative.ofAdd (1 : ℤ))) h'
  rw [algX, algXi, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finsupp.single_apply,
    if_pos (by simp)] at hc
  rw [if_neg (by
    intro hc2
    have h3 := congrArg Multiplicative.toAdd hc2
    simp only [toAdd_ofAdd] at h3
    omega)] at hc
  exact one_ne_zero hc

theorem fXi_eq_fY_sub : (fXi : K1) = fY - fX := by
  rw [eq_sub_iff_add_eq, add_comm, ← fY_eq]

theorem fX_sq : (fX : K1) * fX = fY * fX - 1 := by
  rw [fY_mul_fX]
  ring

theorem fX_notMem_Fy : (fX : K1) ∉ Fy := by
  intro hx
  have hfix : tau • (fX : K1) = fX := (mem_sgnLIi fX).mp (Fy_le_sgnLIi hx) tau
  rw [tau_smul_fX] at hfix
  exact fX_ne_fXi hfix.symm

/-! ### Vsub 装置（`Fy`-坐标显式化，闭合原计划 [δ]） -/

/-- `V = Fy + Fy·fX` 的载体（`Fy`-坐标显式化装置）。 -/
def VsubCarrier : Set K1 :=
  {z | ∃ a b : K1, a ∈ (Fy : Set K1) ∧ b ∈ (Fy : Set K1) ∧ z = a + b * fX}

theorem mem_VsubCarrier (z : K1) :
    z ∈ VsubCarrier ↔ ∃ a b : K1, a ∈ (Fy : Set K1) ∧ b ∈ (Fy : Set K1) ∧
      z = a + b * fX := Iff.rfl

theorem VsubCarrier_zero : (0 : K1) ∈ VsubCarrier :=
  ⟨0, 0, Fy.zero_mem, Fy.zero_mem, by rw [zero_mul, add_zero]⟩

theorem VsubCarrier_one : (1 : K1) ∈ VsubCarrier :=
  ⟨1, 0, Fy.one_mem, Fy.zero_mem, by rw [zero_mul, add_zero]⟩

theorem VsubCarrier_neg {z : K1} (hz : z ∈ VsubCarrier) : -z ∈ VsubCarrier := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  exact ⟨-a, -b, Fy.neg_mem ha, Fy.neg_mem hb, by rw [neg_add, neg_mul]⟩

theorem VsubCarrier_add {z w : K1} (hz : z ∈ VsubCarrier) (hw : w ∈ VsubCarrier) :
    z + w ∈ VsubCarrier := by
  obtain ⟨a₁, b₁, ha₁, hb₁, rfl⟩ := hz
  obtain ⟨a₂, b₂, ha₂, hb₂, rfl⟩ := hw
  refine ⟨a₁ + a₂, b₁ + b₂, Fy.add_mem ha₁ ha₂, Fy.add_mem hb₁ hb₂, ?_⟩
  rw [add_mul]
  ring

theorem VsubCarrier_mul {z w : K1} (hz : z ∈ VsubCarrier) (hw : w ∈ VsubCarrier) :
    z * w ∈ VsubCarrier := by
  obtain ⟨a₁, b₁, ha₁, hb₁, rfl⟩ := hz
  obtain ⟨a₂, b₂, ha₂, hb₂, rfl⟩ := hw
  refine ⟨a₁ * a₂ - b₁ * b₂, b₁ * b₂ * fY + a₁ * b₂ + b₁ * a₂, ?_, ?_, ?_⟩
  · exact Fy.sub_mem (Fy.mul_mem ha₁ ha₂) (Fy.mul_mem hb₁ hb₂)
  · exact Fy.add_mem (Fy.add_mem (Fy.mul_mem (Fy.mul_mem hb₁ hb₂) fY_mem_Fy)
      (Fy.mul_mem ha₁ hb₂)) (Fy.mul_mem hb₁ ha₂)
  · calc (a₁ + b₁ * fX) * (a₂ + b₂ * fX)
        = a₁ * a₂ + (a₁ * b₂ + b₁ * a₂) * fX + b₁ * b₂ * (fX * fX) := by ring
      _ = a₁ * a₂ + (a₁ * b₂ + b₁ * a₂) * fX + b₁ * b₂ * (fY * fX - 1) := by
            rw [fX_sq]
      _ = (a₁ * a₂ - b₁ * b₂) + (b₁ * b₂ * fY + a₁ * b₂ + b₁ * a₂) * fX := by ring

theorem VsubCarrier_inv {z : K1} (hz : z ∈ VsubCarrier) : z⁻¹ ∈ VsubCarrier := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  by_cases h0 : a + b * fX = 0
  · rw [h0, inv_zero]
    exact VsubCarrier_zero
  · have hfixa : tau • a = a := (mem_sgnLIi a).mp (Fy_le_sgnLIi ha) tau
    have hfixb : tau • b = b := (mem_sgnLIi b).mp (Fy_le_sgnLIi hb) tau
    have hconj : tau • (a + b * fXi) = a + b * fX := by
      rw [smul_add, smul_mul', hfixa, hfixb, tau_smul_fXi]
    have hconj_ne : a + b * fXi ≠ 0 := by
      intro hc
      apply h0
      calc a + b * fX = tau • (a + b * fXi) := hconj.symm
        _ = tau • 0 := by rw [hc]
        _ = 0 := smul_zero tau
    have hN_ne : (a + b * fX) * (a + b * fXi) ≠ 0 := mul_ne_zero h0 hconj_ne
    have hmul₁ : (a + b * fX) * ((a + b * fXi) *
        ((a + b * fX) * (a + b * fXi))⁻¹) = 1 := by
      rw [← mul_assoc, mul_inv_cancel₀ hN_ne]
    have hz_inv : (a + b * fX)⁻¹
        = (a + b * fXi) * ((a + b * fX) * (a + b * fXi))⁻¹ :=
      inv_eq_of_mul_eq_one_right hmul₁
    have hEq : (a + b * fX) * (a + b * fXi) = a * a + (a * b) * fY + b * b := by
      calc (a + b * fX) * (a + b * fXi)
          = a * a + (a * b) * (fX + fXi) + (b * b) * (fX * fXi) := by ring
        _ = a * a + (a * b) * fY + (b * b) * 1 := by rw [← fY_eq, fX_mul_fXi]
        _ = a * a + (a * b) * fY + b * b := by ring
    have hN_mem : (a + b * fX) * (a + b * fXi) ∈ Fy := by
      rw [hEq]
      exact Fy.add_mem
        (Fy.add_mem (Fy.mul_mem ha ha) (Fy.mul_mem (Fy.mul_mem ha hb) fY_mem_Fy))
        (Fy.mul_mem hb hb)
    refine ⟨(a + b * fY) * ((a + b * fX) * (a + b * fXi))⁻¹,
      -(b * ((a + b * fX) * (a + b * fXi))⁻¹), ?_, ?_, ?_⟩
    · exact Fy.mul_mem (Fy.add_mem ha (Fy.mul_mem hb fY_mem_Fy)) (Fy.inv_mem hN_mem)
    · exact Fy.neg_mem (Fy.mul_mem hb (Fy.inv_mem hN_mem))
    · rw [hz_inv, fXi_eq_fY_sub]
      ring

/-- `V = Fy[fX]`（`K1` 的子域；将是 `⊤`）。 -/
noncomputable def Vsub : Subfield K1 where
  carrier := VsubCarrier
  zero_mem' := VsubCarrier_zero
  add_mem' := fun hz hw => VsubCarrier_add hz hw
  neg_mem' := fun hz => VsubCarrier_neg hz
  one_mem' := VsubCarrier_one
  mul_mem' := fun hz hw => VsubCarrier_mul hz hw
  inv_mem' := fun _ hx => VsubCarrier_inv hx

theorem mem_Vsub {z : K1} :
    z ∈ Vsub ↔ ∃ a b : K1, a ∈ (Fy : Set K1) ∧ b ∈ (Fy : Set K1) ∧
      z = a + b * fX := Iff.rfl

theorem fX_mem_Vsub : (fX : K1) ∈ Vsub :=
  ⟨0, 1, Fy.zero_mem, Fy.one_mem, by rw [zero_add, one_mul]⟩

theorem fXi_mem_Vsub : (fXi : K1) ∈ Vsub := by
  rw [fXi_eq_fY_sub]
  exact ⟨fY, -1, fY_mem_Fy, Fy.neg_mem Fy.one_mem, by ring⟩

theorem Fy_le_Vsub : (Fy : Set K1) ⊆ (Vsub : Set K1) := by
  intro z hz
  exact ⟨z, 0, hz, Fy.zero_mem, by rw [zero_mul, add_zero]⟩

theorem algebraMap_mem_Vsub (x : R1) : algebraMap R1 K1 x ∈ Vsub := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact Vsub.zero_mem
  | add x y hx hy => rw [map_add]; exact Vsub.add_mem hx hy
  | single m r =>
      cases m using Multiplicative.rec with
      | ofAdd k =>
        by_cases hk : 0 ≤ k
        · rw [single_ofAdd_of_nonneg hk, map_mul, map_pow]
          refine Vsub.mul_mem (Vsub.pow_mem fX_mem_Vsub _) ?_
          rw [← IsScalarTower.algebraMap_apply]
          exact Fy_le_Vsub (Fy.algebraMap_mem r)
        · rw [single_ofAdd_of_neg (k := k) (not_le.mp hk), map_mul, map_pow]
          refine Vsub.mul_mem (Vsub.pow_mem fXi_mem_Vsub _) ?_
          rw [← IsScalarTower.algebraMap_apply]
          exact Fy_le_Vsub (Fy.algebraMap_mem r)

theorem top_le_Vsub : (⊤ : Subfield K1) ≤ Vsub := by
  intro z _
  obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := R1) (K := K1) z
  rw [← hxy, div_eq_mul_inv]
  exact Vsub.mul_mem (algebraMap_mem_Vsub x) (Vsub.inv_mem (algebraMap_mem_Vsub y))

theorem Vsub_eq_top : Vsub = ⊤ := by
  rw [eq_top_iff]
  intro z hz
  exact top_le_Vsub hz

/-! ### `F(M)^G = ℚ(fY)` 与有理性 -/

theorem sgnLIi_le_Fy : sgnLIi ≤ Fy := by
  intro z hz
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_Vsub.mp (top_le_Vsub (Subfield.mem_top z))
  have hfix : tau • (a + b * fX) = a + b * fX :=
    (mem_sgnLIi (a + b * fX)).mp hz tau
  have h1 : tau • (a + b * fX) = a + b * fXi := by
    rw [smul_add, smul_mul', (mem_sgnLIi a).mp (Fy_le_sgnLIi ha) tau,
      (mem_sgnLIi b).mp (Fy_le_sgnLIi hb) tau, tau_smul_fX]
  rw [h1] at hfix
  have hb0 : b = 0 := by
    have h4 : b * fXi = b * fX := add_left_cancel hfix
    have h3 : b * (fXi - fX) = 0 := by rw [mul_sub, h4, sub_self]
    rcases mul_eq_zero.mp h3 with h5 | h5
    · exact h5
    · exact absurd h5 (sub_ne_zero.mpr (Ne.symm fX_ne_fXi))
  rw [hb0, zero_mul, add_zero]
  exact ha

theorem sgnLIi_eq_Fy : sgnLIi = Fy :=
  le_antisymm sgnLIi_le_Fy Fy_le_sgnLIi

theorem invariantsAlg_eq_Fy_toSubalgebra :
    latticeInvariantsAlg ℚ C2 ↥sgnRep = Fy.toSubalgebra := by
  apply SetLike.ext
  intro x
  rw [mem_latticeInvariantsAlg_iff, ← mem_sgnLIi, sgnLIi_eq_Fy]
  exact Iff.rfl

section InstancePriorityPin

/- 局部实例优先级钉：`Algebra ℚ (rationalFunctionField ℚ 1)` 有两个**非定义相等**的
实例（`DivisionRing.toRatAlgebra` 与 `OreLocalization.instAlgebra`）。`AlgEquiv.trans`
的**结果类型**会重新合成该实例槽——默认抢先取 `DivisionRing.toRatAlgebra`，而 `IsRational`
的目标（由 D1 的记录所定）是 `OreLocalization.instAlgebra`，二者不 defeq ⟹ 报
"synthesized … / inferred …"。把 `OreLocalization.instAlgebra` 提为局部 2000 使
合成结果恒为该常量，两侧一致。 -/
attribute [local instance 2000] OreLocalization.instAlgebra

/-- `F(M)^G ≅ ℚ(t)`：先经 `sgnLIi = Fy` 的等域替换，再用 `fY` 的代数独立性。 -/
noncomputable def sgnLIiEquiv :=
  (IntermediateField.equivOfEq sgnLIi_eq_Fy).trans
    algebraicIndependent_fY.aevalEquivField.symm

theorem isRational_invariantsIF : IsRational ℚ ↥sgnLIi :=
  ⟨1, ⟨sgnLIiEquiv⟩⟩

/-- 不变量代数（`Subalgebra` 形）的域结构：与 `Subfield` 形的载体 `rfl`-相等。泛型声明
（对一切 `M`），供 §7 的 ∃-量化使用。 -/
noncomputable instance instFieldInvariantsAlgOf (M : Rep ℤ C2)
    [UniqueProds (Multiplicative ↥M)] :
    Field ↥(latticeInvariantsAlg ℚ C2 ↥M) :=
  inferInstanceAs (Field ↥(latticeInvariants ℚ C2 ↥M))

/-- `↥(latticeInvariantsAlg ℚ C2 ↥sgnRep) ≅ ℚ(t)`（同 `sgnLIiEquiv`，经实例优先级钉）。 -/
noncomputable def invariantsAlgEquiv :=
  (Subalgebra.equivOfEq _ _ invariantsAlg_eq_Fy_toSubalgebra).trans
    algebraicIndependent_fY.aevalEquivField.symm

theorem isRational_invariantsAlg :
    IsRational ℚ ↥(latticeInvariantsAlg ℚ C2 ↥sgnRep) :=
  ⟨1, ⟨invariantsAlgEquiv⟩⟩

end InstancePriorityPin

/-! ## 7. §6：形状测试与 ∃-主定理 -/

/-- 形状测试：`∃ (_ : C), …` 望远镜 binder 注册为**实例**（体内可用 `UniqueProds`）。
用 `latticeInvariantsAlg`（`Subalgebra`）形而不用 `latticeInvariantsIF`（`IntermediateField`）形：
后者在变量 `M` 下触发 `Algebra ℚ ↥·` 的合成超时（20000 heartbeats）。 -/
noncomputable example (M : Rep ℤ C2) :
    (∃ (_ : UniqueProds (Multiplicative ↥M)),
      IsRational ℚ ↥(latticeInvariantsAlg ℚ C2 ↥M)) → True := fun _ => trivial

/-- **EM 判据（`thm:endo-miyata`）一般陈述的反例**（∃-形主定理）。 -/
theorem em_criterion_refuted :
    ∃ M : Rep ℤ C2, ∃ (_ : UniqueProds (Multiplicative ↥M)),
      FaithfulSMul C2 ↥M ∧ IsRational ℚ ↥(latticeInvariantsAlg ℚ C2 ↥M) ∧
        ¬ IsStablyPermutation C2 M := by
  refine ⟨sgnRep, inferInstance, sgnRep_faithful, isRational_invariantsAlg,
    sgnRep_not_stablyPermutation⟩

/-! ## 8. 公理闸门（§5–§6 新增件） -/

#print axioms transcendental_algY
#print axioms transcendental_fY
#print axioms algebraicIndependent_fY
#print axioms sgnLIi_eq_Fy
#print axioms isRational_invariantsIF
#print axioms isRational_invariantsAlg
#print axioms em_criterion_refuted

end

end EMCounter

end EM

end ABGV52
