/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-i：接口层**

  块 1 = (⇐)：稳定置换 ⟹ 稳定有理（＝论文 `thm:endo-miyata-converse`）。
  1β-i 只做**零数学风险的接口**，为 1β（Fischer）与 1γ（复合域）铺路：

    * `algebraMap_latticeAlgebra_eq_single`：`F[M]` 的纯量即 `single 1`；
    * `instSMulCommClassLatticeAlgebra`：作用经**系数不动**的环自同构 ⟹ 与 `F`-纯量交换；
    * `smul_algebraMap_latticeFunctionField`：`G` 逐点固定 `algebraMap F (F(M))` 的像；
    * `instSMulCommClassLatticeFunctionField`：上延到 `F(M)`；
    * `latticeInvariantsAlg`：不变量域的 `Subalgebra` 形态（`IsRational` 的陈述需要 `Algebra F`）；
    * `invariantsRingEquiv`：`Subfield` 形态与 `Subalgebra` 形态的等价（同一载体）；
    * `finrank_invariants`：`[F(M) : F(M)^G] = |G|`（承接 `FixedPoints.finrank_eq_card`）。

  未在此件落地（推迟到 1δ，与 `⊞` 理论一并办）：`IsPermutationLattice → IsStablyPermutation`
  —— 需要 `L ⊞ 0 ≅ L` 的 biproduct API（`Rep` 无 `Zero` 实例，取 `P = ofMulAction ℤ G PEmpty`）。

  记号与块 0 一致：`M` 是 `Z[G]`-格，`F[M]` 是单项式环，`F(M) = Frac F[M]`。
-/
import ABGV52.D2_ABGV52
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic

namespace ABGV52

namespace EM

section Interface

variable (F : Type*) [Field F]
variable (G : Type*) [Group G]
variable (M : Type*) [AddCommGroup M] [Module ℤ M]
  [DistribMulAction G M] [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]

/-! ## 1. 纯量与交换性 -/

omit [Module ℤ M] [UniqueProds (Multiplicative M)] in
/-- `algebraMap F F[M] c = single 1 c`。 -/
lemma algebraMap_latticeAlgebra_eq_single (c : F) :
    algebraMap F (latticeAlgebra F M) c
      = MonoidAlgebra.single (1 : Multiplicative M) c := by
  rw [MonoidAlgebra.coe_algebraMap]
  rfl

/-- 作用经 `mapDomainRingEquiv` 给出、系数不动，故 `G`-作用与 `F`-纯量交换。 -/
instance instSMulCommClassLatticeAlgebra :
    SMulCommClass G F (latticeAlgebra F M) where
  smul_comm g c x := by
    show g • (c • x) = c • (g • x)
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    change MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G M g)
        (algebraMap F (latticeAlgebra F M) c) = _
    rw [algebraMap_latticeAlgebra_eq_single, MonoidAlgebra.mapDomainRingEquiv_single,
      MulEquiv.map_one]

omit [Module ℤ M] [UniqueProds (Multiplicative M)] in
/-- `G` 固定 `algebraMap F F[M]` 的像（作用不动系数）。 -/
lemma smul_algebraMap_latticeAlgebra (g : G) (c : F) :
    g • algebraMap F (latticeAlgebra F M) c
      = algebraMap F (latticeAlgebra F M) c := by
  rw [algebraMap_latticeAlgebra_eq_single]
  change MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G M g)
      (MonoidAlgebra.single (1 : Multiplicative M) c) = _
  rw [MonoidAlgebra.mapDomainRingEquiv_single, MulEquiv.map_one]

/-- `G` 逐点固定 `algebraMap F (F(M))` 的像（经标量塔与分式域上延）。 -/
lemma smul_algebraMap_latticeFunctionField (g : G) (c : F) :
    g • algebraMap F (latticeFunctionField F M) c
      = algebraMap F (latticeFunctionField F M) c := by
  rw [IsScalarTower.algebraMap_apply F (latticeAlgebra F M) (latticeFunctionField F M) c]
  change (IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingEquiv G (latticeAlgebra F M) g))
    (algebraMap (latticeAlgebra F M) (latticeFunctionField F M)
      (algebraMap F (latticeAlgebra F M) c)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  exact smul_algebraMap_latticeAlgebra F G M g c

/-- 上延到函数域：作用不动纯量。 -/
instance instSMulCommClassLatticeFunctionField :
    SMulCommClass G F (latticeFunctionField F M) where
  smul_comm g c x := by
    show g • (c • x) = c • (g • x)
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_latticeFunctionField]

/-! ## 2. 不变量域的两种形态 -/

/-- **不变量域的 `Subalgebra` 形态**：`IsRational` 的陈述形态需要 `Algebra F ↥·`。 -/
noncomputable def latticeInvariantsAlg : Subalgebra F (latticeFunctionField F M) :=
  FixedPoints.subalgebra F (latticeFunctionField F M) G

/-- 两种形态**载体相同**（`FixedPoints` 的两种包装）。 -/
theorem latticeInvariants_carrier_eq :
    (latticeInvariants F G M : Set (latticeFunctionField F M))
      = (latticeInvariantsAlg F G M : Set (latticeFunctionField F M)) := rfl

/-- 两种形态之间的恒等环等价。

**注**：此处只能给 `≃+*`，不能给 `≃ₐ[F]` —— `Subfield` 在 mathlib 中**没有**
`Algebra F ↥·` 实例（`FixedPoints.subfield` 的 `Algebra` 是**反向**的：基域是被固定的子域）。
这正是 `IsRational` 的陈述必须走 `latticeInvariantsAlg`（`Subalgebra` 形态）的原因。 -/
noncomputable def invariantsRingEquiv :
    ↥(latticeInvariants F G M) ≃+* ↥(latticeInvariantsAlg F G M) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem mem_latticeInvariantsAlg_iff (x : latticeFunctionField F M) :
    x ∈ latticeInvariantsAlg F G M ↔ ∀ g : G, g • x = x :=
  MulAction.mem_fixedPoints

/-- **`[F(M) : F(M)^G] = |G|`**（`FixedPoints.finrank_eq_card` 的直接搬运）。 -/
theorem finrank_invariants [Fintype G] [FaithfulSMul G (latticeFunctionField F M)] :
    Module.finrank ↥(latticeInvariants F G M) (latticeFunctionField F M) = Fintype.card G :=
  FixedPoints.finrank_eq_card G (latticeFunctionField F M)

end Interface

/-! ## 4. 公理闸门 -/

#print axioms algebraMap_latticeAlgebra_eq_single
#print axioms instSMulCommClassLatticeAlgebra
#print axioms smul_algebraMap_latticeAlgebra
#print axioms smul_algebraMap_latticeFunctionField
#print axioms instSMulCommClassLatticeFunctionField
#print axioms latticeInvariantsAlg
#print axioms latticeInvariants_carrier_eq
#print axioms invariantsRingEquiv
#print axioms mem_latticeInvariantsAlg_iff
#print axioms finrank_invariants

end EM

end ABGV52
