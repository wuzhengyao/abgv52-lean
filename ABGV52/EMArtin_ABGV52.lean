/-
  ABGV-5.2 —— **本体形式化 A · M1（EMArtin）**：Artin（忠实 ⟹ Galois ⟹ 基数为 |G|）

  目标（蓝图 `wiki/proj-ABGV52-formalize-em.md` §3.1 M1／§3.3 T1）：
    #3 忠实性传递（M 忠实 ⟹ F(M) 忠实）＋ #1 Galois 接线 ＋
    #2 [F(M) : F(M)^G] = |G| ＋ #4 Gal(F(M)/F(M)^G) ≅ G ＋ 非空洞探针。
  **路线 S 与扭化读法的公共地基。**

  mathlib 侧锚（2026-10-08 实跑核）：
    * `FixedPoints.finrank_eq_card [Fintype G] [FaithfulSMul G F]`（FieldTheory/Fixed:346）；
    * `FixedPoints.toAlgHom_bijective`／`FixedPoints.toAlgHomEquiv`（:356/:368，
      即 #4 的现成形态）；
    * `IsGalois.of_fixed_field`（#1）；
    * 传递链的组件：`MonoidAlgebra.single_left_inj`（Defs:235）、
      `IsFractionRing.ringEquivOfRingEquiv_algebraMap`（FractionRing:437）。

  策略说明（忠实传递的两步）：
    A. **格代数层**：`g • single m r = single (g • m) r`（单项式作用显式公式）
       ＋ `single_left_inj` ⟹ 忠实性从 M 继承到 `F[M]`；
    B. **函数域层**：`g • algebraMap a = algebraMap (g • a)`（=`ringEquivOfRingEquiv_algebraMap`）
       反推（faithfulness 沿**单**射等变映射**上升**：若 g 在 F(M) 上平凡则先在 F[M]
       上平凡）+ `algebraMap` 单射 ⟹ 忠实性继承到 `F(M)`。

  探针（L1）：G = C₃ × C₃ 经**正则作用** `(h • f) i = f (h⁻¹ * i)` 于置换格
  M = ℤ[H] = (H → ℤ)；结论 `[ℚ(H) : ℚ(H)^G] = 9 = |G|`（论文栖息地的最小例）。

  **无 sorry、无自造公理**。
-/
import ABGV52.D1_ABGV52
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.ZMod.Basic

namespace ABGV52
namespace EM

variable (F : Type*) [Field F]
variable (G : Type*) [Group G]
variable (M : Type*) [AddCommGroup M] [Module ℤ M]
  [DistribMulAction G M] [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]

/-! ## 1. 单项式作用公式（格代数层） -/

/-- **单项式作用**：`g • single m r = single (g • m) r`（作用经
`latticeAlgebraEquiv = mapDomainRingEquiv (mulEquivOfSMul g)` 定义）。 -/
lemma latticeAlgebra_smul_single (g : G) (m : M) (r : F) :
    g • MonoidAlgebra.single (Multiplicative.ofAdd m) r
      = MonoidAlgebra.single (Multiplicative.ofAdd (g • m)) r := by
  show latticeAlgebraEquiv F G M g (MonoidAlgebra.single (Multiplicative.ofAdd m) r)
    = MonoidAlgebra.single (Multiplicative.ofAdd (g • m)) r
  simp only [latticeAlgebraEquiv, MonoidAlgebra.mapDomainRingEquiv_single,
    mulEquivOfSMul_apply]
  rfl

/-- 格代数上的作用即 `latticeAlgebraEquiv` 的作用（`rfl` 级）。 -/
lemma latticeAlgebra_smul_def (g : G) (a : latticeAlgebra F M) :
    g • a = latticeAlgebraEquiv F G M g a := rfl

/-! ## 2. 忠实传递（两步） -/

/-- **A：格代数层**——M 的作用忠实 ⟹ 单项式环 `F[M]` 上作用忠实。 -/
theorem faithfulSMul_latticeAlgebra (hfaith : FaithfulSMul G M) :
    FaithfulSMul G (latticeAlgebra F M) := by
  rw [faithfulSMul_iff]
  intro g hg
  by_contra hne
  have hex : ∃ m : M, g • m ≠ m := by
    by_contra h
    push_neg at h
    exact hne ((faithfulSMul_iff.mp hfaith) g h)
  obtain ⟨m, hm⟩ := hex
  have hsingle : MonoidAlgebra.single (Multiplicative.ofAdd (g • m)) (1 : F)
      = MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : F) := by
    rw [← latticeAlgebra_smul_single (F := F) (G := G) (M := M) g m (1 : F)]
    exact hg _
  have hof : Multiplicative.ofAdd (g • m) = Multiplicative.ofAdd m :=
    (MonoidAlgebra.single_left_inj (by exact one_ne_zero)).mp hsingle
  exact hm (Multiplicative.ofAdd.injective hof)

/-- **B：函数域层**——忠实性经 `algebraMap` 上升到分式域。 -/
theorem faithfulSMul_latticeFunctionField (hfaith : FaithfulSMul G M) :
    FaithfulSMul G (latticeFunctionField F M) := by
  rw [faithfulSMul_iff]
  intro g hg
  -- 由函数域上的平凡性反推格代数上的平凡性
  have hbase : ∀ a : latticeAlgebra F M, g • a = a := by
    intro a
    apply IsFractionRing.injective (latticeAlgebra F M) (latticeFunctionField F M)
    have h1 : g • algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a
        = algebraMap (latticeAlgebra F M) (latticeFunctionField F M) (g • a) := by
      show IsFractionRing.ringEquivOfRingEquiv
          (latticeAlgebraEquiv F G M g) (algebraMap (latticeAlgebra F M)
            (latticeFunctionField F M) a) = _
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      rw [latticeAlgebra_smul_def]
    rw [← h1]
    exact hg _
  exact (faithfulSMul_iff.mp (faithfulSMul_latticeAlgebra (F := F) (G := G) (M := M) hfaith)) g hbase

/-! ## 3. M1 主结论（Artin 三件套） -/

/-- **#2 基数**：`[F(M) : F(M)^G] = |G|`（mathlib `FixedPoints.finrank_eq_card`）。 -/
theorem artin_finrank [Fintype G] (hfaith : FaithfulSMul G M) :
    Module.finrank ↥(latticeInvariants F G M) (latticeFunctionField F M)
      = Fintype.card G := by
  haveI := faithfulSMul_latticeFunctionField (F := F) (G := G) (M := M) hfaith
  exact FixedPoints.finrank_eq_card (G := G) (F := latticeFunctionField F M)

/-- **#1 Galois**：`F(M)/F(M)^G` 是 Galois 扩张（Stacks 09I3 第一半；
无需忠实——忠实供基数）。 -/
theorem artin_isGalois [Finite G] (hfaith : FaithfulSMul G M) :
    IsGalois ↥(latticeInvariants F G M) (latticeFunctionField F M) := by
  haveI := faithfulSMul_latticeFunctionField (F := F) (G := G) (M := M) hfaith
  infer_instance

/-- **#4 Galois 群 ≅ G**：典范映射 `G → (F(M) →ₐ[F(M)^G] F(M))` 是双射
（mathlib `FixedPoints.toAlgHomEquiv`）。 -/
noncomputable def artin_galEquiv [Finite G] (hfaith : FaithfulSMul G M) :
    G ≃ (latticeFunctionField F M →ₐ[↥(latticeInvariants F G M)]
      (latticeFunctionField F M)) := by
  haveI := faithfulSMul_latticeFunctionField (F := F) (G := G) (M := M) hfaith
  exact FixedPoints.toAlgHomEquiv (G := G) (F := latticeFunctionField F M)

/-! ## 4. 非空洞探针（L1）：G = C₃ × C₃ 经正则作用于置换格 ℤ[H] = (H → ℤ) -/

section Probe

/-- 探针群：`H = C₃ × C₃`（论文栖息地的最小非平凡例子）。 -/
abbrev H9 : Type := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

/-- **正则（坐标置换）作用**：`(h • f) i = f (h⁻¹ * i)`——即置换格 `ℤ[H]` 上的
`G`-作用（与论文所用置换模同型）。 -/
local instance regAction : DistribMulAction H9 (H9 → ℤ) where
  smul h f := fun i => f (h⁻¹ * i)
  one_smul f := by
    funext i
    show f ((1 : H9)⁻¹ * i) = f i
    simp only [inv_one, one_mul]
  mul_smul a b f := by
    funext i
    show f ((a * b)⁻¹ * i) = f (b⁻¹ * (a⁻¹ * i))
    simp only [mul_inv_rev, mul_assoc]
  smul_zero h := by funext i; rfl
  smul_add h f g := by funext i; rfl

/-- 正则作用与 `ℤ`-标量乘法相容（点态交换）。 -/
local instance : SMulCommClass H9 ℤ (H9 → ℤ) where
  smul_comm h m f := by funext i; rfl

/-- 正则作用在 `ℤ[H]` 上**忠实**：非平凡元把 δ₁ 搬到 δ_h ≠ δ₁。
（命名带 `H9` 后缀：与 `D6_ABGV52.lean:312` 的同名件 `faithfulSMul_regular` 区隔——
二者类型不同而名同，曾致「同时导入 D13 链与 EM 链」的模块重复定义；2026-10-08 主循环改名。） -/
theorem faithfulSMul_H9_reg : FaithfulSMul H9 (H9 → ℤ) := by
  rw [faithfulSMul_iff]
  intro h hh
  by_contra hne
  have h1 := congr_fun (hh (fun j : H9 => if j = 1 then (1 : ℤ) else 0)) h
  have h2 : (1 : ℤ) = 0 := by
    rw [show (h • (fun j : H9 => if j = 1 then (1 : ℤ) else 0)) h
          = (fun j : H9 => if j = 1 then (1 : ℤ) else 0) (h⁻¹ * h) from rfl] at h1
    simpa [hne] using h1
  exact one_ne_zero h2

/-- **探针结论**：`[ℚ(H) : ℚ(H)^G] = 9 = |G|`（Artin 定理在置换格
`ℤ[C₃ × C₃]` 上的实例化）。 -/
example : Module.finrank ↥(latticeInvariants ℚ H9 (H9 → ℤ))
    (latticeFunctionField ℚ (H9 → ℤ)) = 9 := by
  rw [artin_finrank ℚ H9 (H9 → ℤ) faithfulSMul_H9_reg]
  decide

end Probe

/-! ## 5. 公理闸门 -/

#print axioms faithfulSMul_latticeAlgebra
#print axioms faithfulSMul_latticeFunctionField
#print axioms artin_finrank
#print axioms artin_isGalois
#print axioms artin_galEquiv

end EM
end ABGV52
