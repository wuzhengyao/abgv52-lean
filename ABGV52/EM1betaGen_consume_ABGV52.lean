/-
# M6-D（接线）：一般置换 `Q` 有理性接入「路线 S」装配 —— `EM1betaGen_consume_ABGV52.lean`

**目标（本件）**：把 `EMConsume_ABGV52.lean`（T2）的主推论
`isStablyRational_of_isStablyPermutationRegular`（只消费**正则子块**
`IsStablyPermutationRegular`，即 `∃ P 置换格, M ⊞ P ≅ 正则格`）升级为**一般稳定置换**
输入 `IsStablyPermutation G M`（`∃ P Q 置换格, M ⊞ P ≅ Q`），S4 槽由 D13-正则版
（`isRational_latticeInvariantsAlg_regular`）换成 **M6-C 一般版**
（`isRational_latticeInvariantsAlg_of_permBasis`）——即设计件
`wiki/proj-ABGV52-M6-1beta-general-design.md` §4.3／§6 的 M6-D 行。

**五件（对照派发书 §2）**：
- (a) `s34Interface_of_fischer_permutation`：S4 字段由 M6-C
  主定理供给（取 `Q`、`(B, κ, hκ)`、ζ），经 `RouteS.s34Interface_of_bridge`（`:419`）进入
  `S34Interface`（`:363`）——即 `s34Interface_of_fischer_regular`（`EMRouteS:553`）的 Q-版。
- (b) `phiAddEquivQ`／`latticeAddEquivQ`：桥数据 `↥M × ↥P ≃+ ↥Q`（`EMConsume.eReg`
  三段复合骨架照搬，第三段换为一般 `φ : M ⊞ P ≅ Q` 的 iso 段等价）。
- (c) `bridgeQ`：桥 `b` 的 Q-版（`Bridge.chiAbs` ＋ `EMTrans.latticeInvariantsAlgTransport`），
  对 `EMBridge.bridgeB` 的逐行推广（`G → ℤ` ↦ `Q`）。
- (d) `isStablyRational_of_isStablyPermutation`：主推论（一般版）；退化对照
  `isStablyRational_of_isStablyPermutationRegular'`（T2 主推论经一般版重证）。
- (e) 类型锁 ＋ `#print axioms` 闸门（§5／§6）。

**复用读数（对照既有件）**：
`EMConsume.biprodProdAddEquiv`（双积-积等价，`:116`）／`instSMulCommClassRepCarrier`
（菱形桥，`:45`）／`uniqueProds_multiplicative_carrier`（`:59`）；`EMBridge.chiAbs`（`:877`）；
`EMTrans.latticeInvariantsAlgTransport`（`:207`）／`isRational_latticeInvariantsAlg_iff`（`:251`）；
`EMRouteS.exists_permBasis_of_isPermutationLattice`（`:173`）／`s34Interface_of_bridge`（`:419`）／
`s2Interface_of_data'`（`:453`）／`isStablyRational_of_S2`（`:380`）；M6-C
`isRational_latticeInvariantsAlg_of_permBasis`（`EM1betaGen_rational:545`）。

**菱形处置（`EMConsume:2-8` 同款）**：目标位内层 `ℤ`-smul 经 `ZSMul.toSMul`、
`Rep.hV2` 侧经 module 结构，二者非 defeq；本件以
`attribute [local instance 2000] Rep.hV2` 统一 module 结构优先级。

**无 sorry、无自造公理、不修改任何既有文件**。
-/
import ABGV52.EMConsume_ABGV52
import ABGV52.EM1betaGen_rational_ABGV52

open CategoryTheory Limits

namespace ABGV52

namespace EM

namespace M6Consume

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

variable {G : Type} [CommGroup G] [Fintype G]

attribute [local instance 2000] Rep.hV2

/-! ## 1. iso 段的加法等价与等变性（一般 `Q` 版）

`EMConsume.phiAddEquiv` 的靶固定为 `↥(Rep.ofMulAction ℤ G G)`（`:214`）；本节给出一般
`φ : M ⊞ P ≅ Q` 的靶 `↥Q` 版本，并把 `EMConsume.eReg` 的三段复合骨架（双积-积等价 ∘
iso 段 ∘ 系数等价）中第三段换为一般 `Q`（无需系数识别）。 -/

/-- `φ : M ⊞ P ≅ Q` 给出的载体加法等价 `↥(M ⊞ P) ≃+ ↥Q`。 -/
def phiAddEquivQ (M P Q : Rep ℤ G) (φ : M ⊞ P ≅ Q) :
    ↥(M ⊞ P) ≃+ ↥Q :=
  { toFun := fun x => φ.hom.hom x
    invFun := fun s => φ.inv.hom s
    map_add' := fun x y => (φ.hom.hom.toLinearMap).map_add x y
    left_inv := fun x => Iso.hom_inv_id_apply φ x
    right_inv := fun s => Iso.inv_hom_id_apply φ s }

/-- 其等变性（即 `φ` 的交织性）。 -/
theorem phiAddEquivQ_rho (M P Q : Rep ℤ G) (φ : M ⊞ P ≅ Q) (g : G)
    (x : ↥(M ⊞ P)) :
    phiAddEquivQ M P Q φ ((M ⊞ P).ρ g x) = Q.ρ g (phiAddEquivQ M P Q φ x) :=
  Rep.hom_comm_apply φ.hom g x

/-- **桥数据（一般 `Q` 版）**：`↥M × ↥P ≃+ ↥Q`（`EMConsume.eReg` 三段复合的前两段）。 -/
def latticeAddEquivQ (M P Q : Rep ℤ G) (φ : M ⊞ P ≅ Q) :
    ↥M × ↥P ≃+ ↥Q :=
  (Consume.biprodProdAddEquiv M P).trans (phiAddEquivQ M P Q φ)

/-- `latticeAddEquivQ` 的等变性（对积作用与 `Q` 的 `Rep`-作用）。 -/
theorem latticeAddEquivQ_equivariant (M P Q : Rep ℤ G) (φ : M ⊞ P ≅ Q) (g : G)
    (z : ↥M × ↥P) : latticeAddEquivQ M P Q φ (g • z) = g • latticeAddEquivQ M P Q φ z := by
  calc latticeAddEquivQ M P Q φ (g • z)
      = phiAddEquivQ M P Q φ (Consume.biprodProdAddEquiv M P (g • z)) := rfl
    _ = phiAddEquivQ M P Q φ
          ((M ⊞ P).ρ g (Consume.biprodProdAddEquiv M P z)) := by
          rw [Consume.biprodProdAddEquiv_equivariant]
    _ = Q.ρ g (phiAddEquivQ M P Q φ (Consume.biprodProdAddEquiv M P z)) := by
          rw [phiAddEquivQ_rho]
    _ = g • latticeAddEquivQ M P Q φ z := rfl

/-! ## 2. 桥 `b` 的 Q-版（`EMBridge.bridgeB` 的 `G → ℤ ↦ Q` 推广）

`EMBridge.bridgeB`（`:920`）的靶 `(G → ℤ)` 换为一般 `Q`；两段复用与 `bridgeB` 逐字相同
（`EMTrans.latticeInvariantsAlgTransport.symm` ＋ `EMBridge.chiAbs.symm`），把「等变加法等价
`↥M × ↥P ≃+ ↥Q`」这一**数据**（第 1 节第三节段）代进去即得。 -/

section Bridge

variable {F : Type} [Field F]

variable (M P Q : Rep.{0} ℤ G)
variable [UniqueProds (Multiplicative ↥M)] [UniqueProds (Multiplicative ↥P)]
  [UniqueProds (Multiplicative ↥Q)]

set_option maxHeartbeats 8000000 in
/-- **桥（Q-版）**：`F(Q)^G ≃ₐ[F] l(N)^G`（S3 载运 ＋ χ）。 -/
noncomputable def bridgeQ (φ : M ⊞ P ≅ Q) :
    ↥(latticeInvariantsAlg F G ↥Q)
      ≃ₐ[F] ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := ↥M) (P := ↥P))) :=
  (latticeInvariantsAlgTransport (F := F) (G := G) (M := ↥M × ↥P) (M' := ↥Q)
      (latticeAddEquivQ M P Q φ) (latticeAddEquivQ_equivariant M P Q φ)).symm.trans
    (Bridge.chiAbs (F := F) (M := ↥M) (P := ↥P)).symm

set_option maxHeartbeats 8000000 in
/-- 类型锁定：`bridgeQ` 的声明类型一旦漂移，本 `rfl` 立即编译失败。 -/
theorem bridgeQ_typeLock (φ : M ⊞ P ≅ Q) :
    (bridgeQ (F := F) (G := G) M P Q φ :
        ↥(latticeInvariantsAlg F G ↥Q)
          ≃ₐ[F] ↥(FixedPoints.subfield G
            (semiFunctionField (F := F) (M := ↥M) (P := ↥P))))
      = bridgeQ (F := F) (G := G) M P Q φ := rfl

end Bridge

/-! ## 3. S4 槽 Q-版：`s34Interface_of_fischer_permutation`

`EMRouteS.s34Interface_of_fischer_regular`（`:553`）的 Q-版：S4 槽由
**M6-C 一般置换基主定理**（`EM1betaGen_rational:545`）供给（置换基数据 `(B, κ, hκ)` 落于 `↥Q`），
桥取第 2 节的 `bridgeQ`。`S34Interface` 的形状（`EMRouteS:363`）本就不 pin `(G → ℤ)`
（其 `M`／`P` 是半线性对），故无需新接口定义，只换构造子。 -/

section Fischer

variable {F : Type} [Field F]

variable (M P Q : Rep.{0} ℤ G)
variable [UniqueProds (Multiplicative ↥M)] [UniqueProds (Multiplicative ↥P)]
  [UniqueProds (Multiplicative ↥Q)]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
variable {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ ↥Q) (κ : G →* Equiv.Perm ι)

/-- **S4 接线（Q-版）**：`Q` 上置换基数据 ＋ 等价 `φ : M ⊞ P ≅ Q` ⟹ `S34Interface`。 -/
theorem s34Interface_of_fischer_permutation
    (φ : M ⊞ P ≅ Q)
    (hκ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G ↥Q σ (permMono (P := ↥Q) B i) = permMono (P := ↥Q) B (κ σ i)) :
    RouteS.S34Interface (F := F) (G := G) (M := ↥M) (P := ↥P) :=
  RouteS.s34Interface_of_bridge (F := F) (G := G) (M := ↥M) (P := ↥P) (N := ↥Q)
    (bridgeQ (F := F) (G := G) M P Q φ)
    (isRational_latticeInvariantsAlg_of_permBasis (F := F) (G := G) (Q := ↥Q)
      (ι := ι) (B := B) (κ := κ) hκ)

set_option maxHeartbeats 8000000 in
/-- 类型锁定（接口形状）：与本节构造子的结论外形一致（rfl 级别）。 -/
theorem s34Interface_permutation_typeLock :
    (RouteS.S34Interface (F := F) (G := G) (M := ↥M) (P := ↥P))
      = IsRational F
          ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := ↥M) (P := ↥P))) := rfl

end Fischer

/-! ## 4. 主推论（一般版）：`IsStablyPermutation`（D1）的完整消费

与 T2 `Consume.isStablyRational_of_isStablyPermutationRegular` 的差异：输入谓词由
`IsStablyPermutationRegular`（只允许 `Q = 正则格`）放广为 `IsStablyPermutation`
（`∃ P Q` 置换，`M ⊞ P ≅ Q`）；`Q` 侧的 S4 槽由 M6-C 一般置换基主定理供给
（正则版的 S4 槽是 D13 正则格 Fischer）。 -/

section Main

variable {F : Type} [Field F]

variable (M : Rep.{0} ℤ G)
variable [FaithfulSMul G ↥M] [UniqueProds (Multiplicative ↥M)]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]

/-- **主推论（一般置换 `Q` 版）**：`IsStablyPermutation G M` ＋ `M` 侧忠实性、
`UniqueProds` ⟹ `F(M)^G` 稳定有理。所有 S3 数据（`P`、`Q` 两侧）与格等价均在内部构造。 -/
theorem isStablyRational_of_isStablyPermutation
    (h : IsStablyPermutation G M) :
    IsStablyRational F ↥(latticeInvariantsAlg F G ↥M) := by
  obtain ⟨P, Q, hP, hQ, ⟨φ⟩⟩ := h
  obtain ⟨XP, hXP, hActP, BP, ρP, hρP⟩ :=
    RouteS.exists_permBasis_of_isPermutationLattice P hP
  letI : Fintype XP := hXP
  letI : MulAction G XP := hActP
  haveI hUP : UniqueProds (Multiplicative ↥P) :=
    Consume.uniqueProds_multiplicative_carrier P BP
  obtain ⟨XQ, hXQ, hActQ, BQ, κQ, hκQ⟩ :=
    RouteS.exists_permBasis_of_isPermutationLattice Q hQ
  letI : Fintype XQ := hXQ
  letI : MulAction G XQ := hActQ
  haveI hUQ : UniqueProds (Multiplicative ↥Q) :=
    Consume.uniqueProds_multiplicative_carrier Q BQ
  refine RouteS.isStablyRational_of_S2 (F := F) (G := G) (M := ↥M) (P := ↥P) ?_ ?_
  · exact RouteS.s2Interface_of_data' (F := F) (G := G) (M := ↥M) (P := ↥P)
      (B := BP) (ρ := ρP) (hρ := hρP) (hfaith := inferInstance)
  · exact s34Interface_of_fischer_permutation (F := F) (G := G) (M := M) (P := P) (Q := Q)
      (φ := φ) (B := BQ) (κ := κQ) (hκ := hκQ)

/-- **退化对照**：T2 主推论（正则子情形）由一般版重证——`IsStablyPermutationRegular.toIsStablyPermutation`
（`EMConsume:260`）把正则子块嵌入一般谓词（取 `Q = 正则格`）。 -/
theorem isStablyRational_of_isStablyPermutationRegular'
    (h : Consume.IsStablyPermutationRegular M) :
    IsStablyRational F ↥(latticeInvariantsAlg F G ↥M) :=
  isStablyRational_of_isStablyPermutation (F := F) (G := G) M h.toIsStablyPermutation

/-- 类型锁定（主推论的假设外形 ＝ D1 `IsStablyPermutation` 展开形）。 -/
theorem isStablyPermutation_hyp_typeLock :
    (IsStablyPermutation G M)
      = (∃ P Q : Rep ℤ G,
          IsPermutationLattice G P ∧ IsPermutationLattice G Q ∧ Nonempty (M ⊞ P ≅ Q)) :=
  rfl

end Main

/-! ## 5. 公理闸门（本文件全部新声明） -/

#print axioms phiAddEquivQ
#print axioms phiAddEquivQ_rho
#print axioms latticeAddEquivQ
#print axioms latticeAddEquivQ_equivariant
#print axioms bridgeQ
#print axioms bridgeQ_typeLock
#print axioms s34Interface_of_fischer_permutation
#print axioms s34Interface_permutation_typeLock
#print axioms isStablyRational_of_isStablyPermutation
#print axioms isStablyRational_of_isStablyPermutationRegular'
#print axioms isStablyPermutation_hyp_typeLock

end

end M6Consume

end EM

end ABGV52
