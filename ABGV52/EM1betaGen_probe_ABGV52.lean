/-
  M6-E 非空性探针（L1 ＋ L10①）：M6-A「1β-general 特征分解层」假设类可实现。
  ═══════════════════════════════════════════════════════════════════════════
  角色：**探针（证书件），非内容交付**。为 M6-A 主件
  （`EM1betaGen_basis_ABGV52.lean` 的 §2 `section Chars`）之 section 假设类
  提供**显式可实现见证**；不作任何 M6 结论的自我验证。

  目标类（除 `F` 侧条件外）：
    `G` 有限交换群；`Q := (G → ℤ) × (G → ℤ)`（正则格直和，即设计文档
    §1.5(b) 的格型）上五类实例；`ι := G ⊕ G`；并 `(B, κ, hκ)` 三件套同时
    可实现。

  见证（模板 = `EMRouteS_ABGV52.lean:593` `exists_permBasis_regular` 的
  双因子积版本）：
    `B := (Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G)`（两因子正则基的积基），
    `κ := MulAction.toPermHom G (G ⊕ G)`（左乘作用沿 `G ⊕ G` 两分量同时运输），
    `hκ` = M6-A 相容条件：`mulEquivOfSMul G Q σ` 把 `permMono B i` 送到
    `permMono B (κ σ i)`。

  机制独立性（L-D 对照）：本件的非空性由两条独立机制给出——① 显式见证
  构造（§1：B 的显式定义 + hκ 的逐分支计算）；② 实例合成（§2/§3）。
  M6-A 内部的计数机制（轨道-稳定子）与无关性机制（Gram 对角化）在本件
  不出现。§4 消费例仅示"M6-A 关键引理与 M6-C 主定理可作用于此见证"，
  不参与非空性认证。

  F 侧：§3 示 `HasEnoughRootsOfUnity ℂ (Monoid.exponent Gˣ)` 可由实例合成
  取得（`IsSepClosed ℂ` ← `IsAlgClosed ℂ`；`NeZero` 链经有限群指数）。
-/
import ABGV52.EM1betaGen_basis_ABGV52
import ABGV52.EM1betaGen_rational_ABGV52
import ABGV52.EMRouteS_ABGV52
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace ABGV52

namespace EM

open scoped Classical

set_option maxHeartbeats 400000

variable (G : Type*) [CommGroup G] [Fintype G]

/-! ## 1. 显式见证 `(B, κ, hκ)`（非空性证书） -/

/-- 双因子积见证：`Q := (G → ℤ) × (G → ℤ)` 上存在 M6-A 所需的基-置换数据
（`B` = 两因子正则基的积基；`κ` = 左乘置换；`hκ` 为相容条件）。 -/
theorem exists_permBasis_prodProd :
    ∃ (B : Module.Basis (G ⊕ G) ℤ ((G → ℤ) × (G → ℤ)))
      (κ : G →* Equiv.Perm (G ⊕ G)),
      ∀ (σ : G) (i : G ⊕ G),
        mulEquivOfSMul G ((G → ℤ) × (G → ℤ)) σ
            (permMono (P := (G → ℤ) × (G → ℤ)) B i)
          = permMono (P := (G → ℤ) × (G → ℤ)) B (κ σ i) := by
  classical
  refine ⟨(Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G), MulAction.toPermHom G (G ⊕ G), ?_⟩
  intro σ i
  rw [mulEquivOfSMul_apply]
  show Multiplicative.ofAdd (σ • ((Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G)) i)
    = Multiplicative.ofAdd
        (((Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G))
          (MulAction.toPermHom G (G ⊕ G) σ i))
  congr 1
  have hperm : MulAction.toPermHom G (G ⊕ G) σ i = σ • i := by
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  rw [hperm]
  -- 单因子块事实（逐字镜像 `exists_permBasis_regular` 的核心计算）
  have hblock : ∀ (τ y : G), τ • (Pi.basisFun ℤ G) y = (Pi.basisFun ℤ G) (τ • y) := by
    intro τ y
    funext b
    show (Pi.basisFun ℤ G y) (τ⁻¹ * b) = (Pi.basisFun ℤ G) (τ * y) b
    rw [Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases hb : τ⁻¹ * b = y
    · have hb' : b = τ * y := (inv_mul_eq_iff_eq_mul (a := τ) (b := b) (c := y)).mp hb
      subst hb'
      rw [inv_mul_cancel_left, Pi.single_eq_same, Pi.single_eq_same]
    · have hb' : b ≠ τ * y := fun h => hb (by rw [h, inv_mul_cancel_left])
      rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb']
  have hpairL : ∀ (x : G),
      ((Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G)) (Sum.inl x)
        = ((Pi.basisFun ℤ G) x, (0 : G → ℤ)) := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [Module.Basis.prod_apply_inl_fst]
    · rw [Module.Basis.prod_apply_inl_snd]
  have hpairR : ∀ (x : G),
      ((Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G)) (Sum.inr x)
        = ((0 : G → ℤ), (Pi.basisFun ℤ G) x) := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [Module.Basis.prod_apply_inr_fst]
    · rw [Module.Basis.prod_apply_inr_snd]
  cases i with
  | inl x =>
    rw [Sum.smul_inl, hpairL x, hpairL (σ • x), Prod.smul_mk, smul_zero]
    exact congrArg (fun z => (z, (0 : G → ℤ))) (hblock σ x)
  | inr x =>
    rw [Sum.smul_inr, hpairR x, hpairR (σ • x), Prod.smul_mk, smul_zero]
    exact congrArg (fun z => ((0 : G → ℤ), z)) (hblock σ x)

/-! ## 2. 实例合成（假设类其余部分的落点） -/

example : AddCommGroup ((G → ℤ) × (G → ℤ)) := inferInstance

example : Module ℤ ((G → ℤ) × (G → ℤ)) := inferInstance

example : DistribMulAction G ((G → ℤ) × (G → ℤ)) := inferInstance

example : SMulCommClass G ℤ ((G → ℤ) × (G → ℤ)) := inferInstance

example : UniqueProds (Multiplicative ((G → ℤ) × (G → ℤ))) := inferInstance

example : Fintype (G ⊕ G) := inferInstance

/-! ## 3. F 侧条件（ζ 可满足性） -/

noncomputable example : HasEnoughRootsOfUnity ℂ (Monoid.exponent Gˣ) := inferInstance

/-! ## 4. 消费例（不参与非空性认证） -/

/-- M6-A 关键引理 `YSub_linearIndependent` 在 §1 见证上的端到端应用
（`F := ℂ`、`Q := (G → ℤ) × (G → ℤ)`、`ι := G ⊕ G`）。 -/
noncomputable example :
    LinearIndependent ℂ
      (YSub (F := ℂ) (G := G) (Q := (G → ℤ) × (G → ℤ)) (ι := G ⊕ G)
        ((Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G))
        (MulAction.toPermHom G (G ⊕ G))) :=
  YSub_linearIndependent (F := ℂ) (G := G) (Q := (G → ℤ) × (G → ℤ)) (ι := G ⊕ G)
    ((Pi.basisFun ℤ G).prod (Pi.basisFun ℤ G)) (MulAction.toPermHom G (G ⊕ G))

/-- **案例可实现（L10①）**：M6-C 主定理在 §1 见证上端到端应用——整条假设类
（实例底座 ＋ ζ ＋ `(B, κ, hκ)`）**同时**可被实例化（比逐项见证强一档；
`G : Type` 系主定理宇宙钉（`Rep.{0}`，已登记）所必需——非疏漏）。
与上例并列：不参与非空性认证。 -/
example (G : Type) [CommGroup G] [Fintype G] :
    IsRational ℂ
      ↥(latticeInvariantsAlg ℂ G ((G → ℤ) × (G → ℤ))) := by
  obtain ⟨B, κ, hκ⟩ := exists_permBasis_prodProd (G := G)
  exact isRational_latticeInvariantsAlg_of_permBasis (F := ℂ) (G := G)
    (Q := (G → ℤ) × (G → ℤ)) (ι := G ⊕ G) (B := B) (κ := κ) hκ

/-! ## 5. 公理闸门 -/

#print axioms exists_permBasis_prodProd

end EM

end ABGV52
