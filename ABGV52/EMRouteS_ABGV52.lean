/-
# M5（Route S 装配）：`EMRouteS_ABGV52.lean` —— Phase 1 ＋ Phase 2（2026-10-08）

**目标（本件）**：为 EM 判据 (⇐) 方向的机器化提供 **Route S 装配**——

```
IsStablyPermutation G M → IsStablyRational F ↥(latticeInvariants F G M)
```

（论文 §1.2 路线 S：S1 Artin ＋ S2 Saltman `corollary:1.4`(i) ＋ S3 载运 ＋ S4 Fischer ＋ S5 组装。）

**蓝图来源**：`wiki/proj-ABGV52-formalize-em.md` §1.2（路线 S）／§3.4「M5 装配设计」。
S5 组装算式 `F(M)^G(t_1..t_n) ≅ F(M⊕P)^G ≅ F(Q)^G ≅ F(s_1..s_m)`（三 ≅ = S2／S3／S4），
机器形 = `isStablyRational_of_S2`（§5）。

**Phase 1（已交付）**：**不导入** `EMIndep`；S2 以**具名接口假设** `S2Interface` 代替
（逐字同 `IsRational ↥K0 ↥(l(N)^G)`）。组装算式（§5）、S3 接线（§2、§6）、基域搬运
（§6 基 `↥K0` → 组装基 `F`，§3、§4）、接口类型锁定（§5）、L1 探针与公理闸门落地。

**Phase 2（本次，2026-10-08）**：
- import `EMIndep_ABGV52`：§7 以**真定理** `isRational_fixedPoints` 消解 Phase 1 的
  `S2Interface`（适配 `s2Interface_of_data`／`s2Interface_of_data'`：经 `W_fixed_extraction`
  提取 `y`，`hyfix` 记号经 `Subtype.ext_iff.mp` 转换；其自动实例前提 `FaithfulSMul G (F(M))`
  由 `faithfulSMul_latticeFunctionField`（M1）从 `FaithfulSMul G M` 供给）。
- import `D13_ABGV52`：§10 接线 S4 Fischer（`isRational_latticeInvariantsAlg`，**只到正则格**）。
- **主定理按 A13 以子情形收口**：`isStablyRational_of_regularSubcase`（＋子域形
  `isStablyRational_of_regularSubcase_subfield`）。假设 = `[CommGroup G]`、足够单位根、
  `FaithfulSMul G M`、置换基数据 `(B, ρ, hρ)`（§6 形）、桥
  `b : ↥(latticeInvariantsAlg F G (G → ℤ)) ≃ₐ[F] ↥(l(N)^G)`。
- L1 复合探针（§10）：正则格上 `S2Interface` **无条件**可实例化
  （`s2Interface_regular_nonvacuous`）。

**偏差登记（对照蓝图，逐条；2026-10-08 Phase 2 更新）**：
1. **[已修复] D13 不可导入（模块重复定义）**：`ABGV52.EM.faithfulSMul_regular` 曾同时定义于
   `D6_ABGV52.lean:312` 与 `EMArtin_ABGV52.lean`；主循环已把后者改名
   `faithfulSMul_H9_reg`（`EMArtin_ABGV52.lean:153`，2026-10-08）⟹ D13 链可导入。
   本件已 import `EMIndep`／`D13` 并接线（§7／§10）。
2. **`SMulCommClass G ℤ ↥L`（`Rep` 载体）未提供**：目标位内层 `ℤ`-smul 经 `ZSMul.toSMul`、
   `LinearMap.map_smul` 侧经 `DistribMulAction.toDistribSMul.toSMul`，二者非 defeq（实例菱形）⟹
   核心桥 `core_bridge` **不含**该假设（其证明不需要）；登记为余量项。
3. **`l(N) ≡ F(M⊕P)` 命名约定**（蓝图接线②）：绝对识别 `l(N) ≅ F(M⊕P)`（二步局部化）**未做**；
   本文件 `l(N)` 取 `semiFunctionField F M P = Frac(F(M)[P])`，射程陈述按「F(M⊕P)」之名读。
   **Phase 2**：§10 的桥 `b` 即此识别的残余（连同 S3 载运落点，合为具名假设）。
4. **`latticeInvariants`（D1 Subfield 形）↔ `latticeInvariantsAlg`（D3 Subalgebra 形）对齐**：
   D1 的 `latticeInvariants` 无 `Algebra F ↥·` 实例，`IsRational` 陈述须走 `latticeInvariantsAlg`
   （D3 §2）；二者载体 rfl 相等（`latticeInvariants_carrier_eq`）＋ `invariantsRingEquiv`。
   本文件主定理以 Alg 形给出，并附子域形推论；子域形的 `Algebra F ↥·` 实例
   （`instAlgebraLatticeInvariants`）与搬运等价（`invariantsSubfieldAlgEquiv`）由本文件补出（§3）。
5. **S4 射程（A13）**：Fischer 目前**只到正则格**（D13，`A → ℤ`）；一般置换 `Q` 需 M6
   （不在本件射程）。**Phase 2**：正则格 Fischer 已接线至 `S34Interface`（§10
   `s34Interface_of_fischer_regular`）；其到 `↥(l(N)^G)` 的落点还差桥 `b`（偏差 3）。
6. **接口 ＝ 具名假设**（定理的假设，非公理）：**无 sorry、无自造公理**；`#print axioms` 闸门
   见 §9／§11。**Phase 2**：`S2Interface` 已由 §7 的真定理消解。
7. **[Phase 2 新登记] 主定理的收口形**：`IsStablyPermutation G M` 的**完整消费**未做——
   S3 桥 `exists_permBasis_of_isPermutationLattice` 的输出落在 `↥L`（`Rep` 载体），
   缺 `SMulCommClass G ℤ ↥L`／`UniqueProds (Multiplicative ↥L)`（与偏差 2 同源）⟹ 主定理以
   `(B, ρ, hρ)` 数据形收口（§10）。

**记号**：`l := latticeFunctionField F M`（`F(M)`）、`l(N) := semiFunctionField F M P`
（`Frac(F(M)[P])`）、`K0 := K0 (G := G) (F := F) (M := M) (P := P)`（`l^G` 在 `l(N)` 中的像，
`EMDegree` §1）。
-/
import ABGV52.EMTrans_ABGV52
import ABGV52.EMFixed_ABGV52
import ABGV52.EMDegree_ABGV52
import ABGV52.EMIndep_ABGV52
import ABGV52.D13_ABGV52
import Mathlib.Algebra.MvPolynomial.Equiv

open CategoryTheory

namespace ABGV52

namespace EM

namespace RouteS

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]

/-! ## 0. `Rep ℤ G` 载体上的 `DistribMulAction`（S3 载运用）

`Rep ℤ G` 的载体 `↥L` 经 `L.ρ` 携带 `G`-作用。偏差登记（2）：**不提供**
`SMulCommClass G ℤ ↥L` —— 目标位内层 `ℤ`-smul 经 `ZSMul.toSMul`、
`LinearMap.map_smul` 侧经 `DistribMulAction.toDistribSMul.toSMul`，二者非 defeq（实例菱形）。 -/

attribute [local instance 2000] Rep.hV2

instance instDistribMulActionRep (L : Rep ℤ G) : DistribMulAction G L where
  smul g l := L.ρ g l
  one_smul l := by
    show L.ρ 1 l = l
    rw [map_one]
    rfl
  mul_smul g h l := by
    show L.ρ (g * h) l = L.ρ g (L.ρ h l)
    rw [map_mul]
    rfl
  smul_zero g := (L.ρ g).map_zero
  smul_add g x y := (L.ρ g).map_add x y

/-! ## 1. 基域搬运：`IsRational`／`IsStablyRational` 沿 `≃ₐ[F]` -/

/-- `rationalFunctionField` 沿系数域等价 `≃ₐ[F]` 变基。 -/
def rationalFunctionFieldAlgEquiv {K K' : Type*} [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] (e : K ≃ₐ[F] K') (n : ℕ) :
    rationalFunctionField K n ≃ₐ[F] rationalFunctionField K' n :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv (Fin n) e)

/-- 有理性沿系数域等价搬运。 -/
theorem isRational_of_algEquiv {K K' : Type*} [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] (e : K ≃ₐ[F] K') (h : IsRational F K) : IsRational F K' := by
  obtain ⟨n, ⟨φ⟩⟩ := h
  exact ⟨n, ⟨e.symm.trans φ⟩⟩

/-- 有理性沿系数域等价可逆（`iff` 形式）。 -/
theorem isRational_of_algEquiv_iff {K K' : Type*} [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] (e : K ≃ₐ[F] K') : IsRational F K ↔ IsRational F K' :=
  ⟨isRational_of_algEquiv e, isRational_of_algEquiv e.symm⟩

/-- 稳定有理性沿系数域等价搬运。 -/
theorem isStablyRational_of_algEquiv {K K' : Type*} [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] (e : K ≃ₐ[F] K') (h : IsStablyRational F K) :
    IsStablyRational F K' := by
  obtain ⟨n, m, ⟨φ⟩⟩ := h
  exact ⟨n, m, ⟨(rationalFunctionFieldAlgEquiv e n).symm.trans φ⟩⟩

/-- 稳定有理性沿系数域等价可逆（`iff` 形式）。 -/
theorem isStablyRational_of_algEquiv_iff {K K' : Type*} [Field K] [Field K']
    [Algebra F K] [Algebra F K'] (e : K ≃ₐ[F] K') :
    IsStablyRational F K ↔ IsStablyRational F K' :=
  ⟨isStablyRational_of_algEquiv e, isStablyRational_of_algEquiv e.symm⟩

/-! ## 2. S3 接线：置换格 → 置换基 ＋ 置换律（§6 假设形） -/

/-- **核心桥**（抽象层）：`G`-模 `P` 经等变线性同构 `e` 从带 `G`-置换基 `bY` 的模拉回，
得 `P` 的置换基 `B` 与置换律（§6 的 `(B, ρ, hρ)` 形）。**桥引理，非假设**。 -/
theorem core_bridge
    (P : Type*) [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
    (Y : Type*) [AddCommGroup Y] [Module ℤ Y] [DistribMulAction G Y]
    (X : Type*) [Fintype X] [MulAction G X]
    (bY : Module.Basis X ℤ Y) (hbY : ∀ (g : G) (i : X), g • (bY i) = bY (g • i))
    (e : P ≃ₗ[ℤ] Y) (he : ∀ (g : G) (p : P), e (g • p) = g • e p) :
    ∃ (B : Module.Basis X ℤ P) (ρ : G →* Equiv.Perm X),
      ∀ (σ : G) (i : X),
        mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i) := by
  refine ⟨bY.map e.symm, MulAction.toPermHom G X, ?_⟩
  intro σ i
  rw [mulEquivOfSMul_apply]
  show Multiplicative.ofAdd (σ • (bY.map e.symm) i)
    = Multiplicative.ofAdd ((bY.map e.symm) (MulAction.toPermHom G X σ i))
  have hperm : MulAction.toPermHom G X σ i = σ • i := by
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  congr 1
  rw [hperm, Module.Basis.map_apply, Module.Basis.map_apply]
  apply e.injective
  rw [he σ (e.symm (bY i)), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact hbY σ i

/-- **S3 桥**（`Rep` 层）：`IsPermutationLattice G L`（`D1:64`）的见证 `X` 被显式取出，
接线到置换 `ℤ`-基 `Module.Basis X ℤ ↥L` 与 `ρ : G →* Equiv.Perm X`（§6 假设形）。
B 所对的基础模为 `MonoidAlgebra ℤ X` 而非 `X →₀ ℤ`（mathlib 单字段结构）。 -/
theorem exists_permBasis_of_isPermutationLattice (L : Rep ℤ G)
    (h : IsPermutationLattice G L) :
    ∃ (X : Type) (_ : Fintype X) (_ : MulAction G X)
      (B : Module.Basis X ℤ ↥L) (ρ : G →* Equiv.Perm X),
      ∀ (σ : G) (i : X),
        mulEquivOfSMul G ↥L σ (permMono (P := ↥L) B i)
          = permMono (P := ↥L) B (ρ σ i) := by
  obtain ⟨X, hX, hAct, ⟨φ⟩⟩ := h
  letI : DistribMulAction G ↥(Rep.ofMulAction ℤ G X) :=
    instDistribMulActionRep (Rep.ofMulAction ℤ G X)
  let eLin : ↥L ≃ₗ[ℤ] ↥(Rep.ofMulAction ℤ G X) :=
    { toFun := fun l => φ.hom.hom l
      invFun := fun s => φ.inv.hom s
      left_inv := fun l => Iso.hom_inv_id_apply φ l
      right_inv := fun s => Iso.inv_hom_id_apply φ s
      map_add' := fun a b => map_add φ.hom.hom a b
      map_smul' := fun c a => (φ.hom.hom.toLinearMap).map_smul' c a }
  have he : ∀ (g : G) (p : ↥L), eLin (g • p) = g • eLin p := by
    intro g p
    show φ.hom.hom (L.ρ g p) = (Rep.ofMulAction ℤ G X).ρ g (φ.hom.hom p)
    exact Rep.hom_comm_apply φ.hom g p
  have hbY : ∀ (g : G) (i : X),
      g • ((MonoidAlgebra.basis X ℤ :
          Module.Basis X ℤ ↥(Rep.ofMulAction ℤ G X)) i)
        = (MonoidAlgebra.basis X ℤ :
          Module.Basis X ℤ ↥(Rep.ofMulAction ℤ G X)) (g • i) := by
    intro g i
    rw [MonoidAlgebra.basis_apply, MonoidAlgebra.basis_apply]
    exact Representation.ofMulAction_single g i 1
  refine ⟨X, hX, hAct, ?_⟩
  exact core_bridge (G := G) ↥L ↥(Rep.ofMulAction ℤ G X) X
    (MonoidAlgebra.basis X ℤ) hbY eLin he

/-! ## 3. `lGToK0` 双射与基域搬运 `↥(F(M)^G) ≃ₐ[F] ↥K0` -/

/-- `l ↪ l(N)`（`l(N) := Frac(l[P])`，`l` 为域）。 -/
theorem algebraMap_lattice_injective :
    Function.Injective (algebraMap (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P))) := by
  intro a b hab
  rw [IsScalarTower.algebraMap_apply (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)) a,
      IsScalarTower.algebraMap_apply (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)) b] at hab
  have h2 := IsFractionRing.injective
    (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (semiFunctionField (F := F) (M := M) (P := P)) hab
  simpa [MonoidAlgebra.coe_algebraMap] using h2

/-- `lGToK0 : ↥(l^G) →+* ↥K0` 是双射（`K0` 按定义即 `l^G` 的像）。 -/
theorem lGToK0_bijective :
    Function.Bijective (lGToK0 (F := F) (G := G) (M := M) (P := P)) := by
  constructor
  · intro a b hab
    have h := congrArg
      (fun z : ↥(K0 (G := G) (F := F) (M := M) (P := P)) =>
        (z : semiFunctionField (F := F) (M := M) (P := P))) hab
    exact Subtype.ext (algebraMap_lattice_injective (F := F) (M := M) (P := P) h)
  · intro z
    have hz : (z : semiFunctionField (F := F) (M := M) (P := P))
        ∈ (FixedPoints.subfield G (latticeFunctionField F M)).map
          (algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P))) := z.2
    obtain ⟨c, hc, hcz⟩ := Subfield.mem_map.mp hz
    exact ⟨⟨c, hc⟩, Subtype.ext hcz⟩

/-- `lGToK0` 的 `RingEquiv` 包装（S5 基域搬运用）。 -/
noncomputable def lGToK0RingEquiv :
    ↥(FixedPoints.subfield G (latticeFunctionField F M)) ≃+*
      ↥(K0 (G := G) (F := F) (M := M) (P := P)) :=
  RingEquiv.ofBijective (lGToK0 (F := F) (G := G) (M := M) (P := P))
    (lGToK0_bijective (F := F) (G := G) (M := M) (P := P))

theorem mem_fixed_lattice_iff (x : latticeFunctionField F M) :
    x ∈ FixedPoints.subfield G (latticeFunctionField F M) ↔ ∀ σ : G, σ • x = x := by
  rw [FixedPoints.subfield]
  exact MulAction.mem_fixedPoints

/-- 纯量 `F` 的像落在 `K0` 内。 -/
theorem algebraMapF_mem_K0 (c : F) :
    algebraMap F (semiFunctionField (F := F) (M := M) (P := P)) c
      ∈ K0 (G := G) (F := F) (M := M) (P := P) := by
  rw [show K0 (G := G) (F := F) (M := M) (P := P)
      = (FixedPoints.subfield G (latticeFunctionField F M)).map
        (algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P))) from rfl]
  rw [Subfield.mem_map]
  exact ⟨algebraMap F (latticeFunctionField F M) c,
    (mem_fixed_lattice_iff (F := F) (G := G) (M := M)
      (algebraMap F (latticeFunctionField F M) c)).mpr
      (fun σ => smul_algebraMap_latticeFunctionField (F := F) (G := G) (M := M) σ c),
    IsScalarTower.algebraMap_apply F (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P)) c⟩

/-- `F →+* ↥K0`（经 `l(N)`）。 -/
noncomputable def algebraMapK0 : F →+*
    ↥(K0 (G := G) (F := F) (M := M) (P := P)) where
  toFun c := ⟨algebraMap F (semiFunctionField (F := F) (M := M) (P := P)) c,
    algebraMapF_mem_K0 (F := F) (G := G) (M := M) (P := P) c⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- `K0` 上的 `F`-代数结构（`IsRational ↥K0 ·` 与 S5 组装所需）。 -/
noncomputable instance instAlgebraK0 : Algebra F
    ↥(K0 (G := G) (F := F) (M := M) (P := P)) :=
  (algebraMapK0 (F := F) (G := G) (M := M) (P := P)).toAlgebra

/-- **基域搬运**：`↥(latticeInvariantsAlg F G M) ≃ₐ[F] ↥K0`（`invariantsRingEquiv`
接 `lGToK0RingEquiv`）。 -/
noncomputable def invariantsAlgEquivK0 :
    ↥(latticeInvariantsAlg F G M) ≃ₐ[F]
      ↥(K0 (G := G) (F := F) (M := M) (P := P)) :=
  AlgEquiv.ofRingEquiv
    (f := (invariantsRingEquiv (F := F) (G := G) (M := M)).symm.trans
      (lGToK0RingEquiv (F := F) (G := G) (M := M) (P := P)))
    (fun c => Subtype.ext (IsScalarTower.algebraMap_apply F
      (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P)) c))

/-- `↥(latticeInvariants F G M)`（子域形）上的 `F`-代数结构：mathlib 对 `Subfield` 形
无 `Algebra F ↥·` 实例，经 `invariantsRingEquiv` 从子代数形转运（偏差登记 4）。 -/
noncomputable instance instAlgebraLatticeInvariants :
    Algebra F ↥(latticeInvariants F G M) :=
  ((invariantsRingEquiv (F := F) (G := G) (M := M)).symm.toRingHom.comp
    (algebraMap F ↥(latticeInvariantsAlg F G M))).toAlgebra

/-- 子代数形 → 子域形载体的 `F`-代数同构（`IsStablyRational` 沿其搬运）。 -/
noncomputable def invariantsSubfieldAlgEquiv :
    ↥(latticeInvariantsAlg F G M) ≃ₐ[F] ↥(latticeInvariants F G M) :=
  AlgEquiv.ofRingEquiv
    (f := (invariantsRingEquiv (F := F) (G := G) (M := M)).symm)
    (fun _ => Subtype.ext rfl)

/-! ## 4. `↥(l(N)^G)` 上的 `F`-代数结构与标量塔 -/

/-- 纯量 `F` 的像被 `G` 逐点固定（上延到 `l(N)`）。 -/
theorem algebraMapF_mem_fixedSemi (c : F) :
    algebraMap F (semiFunctionField (F := F) (M := M) (P := P)) c
      ∈ FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) := by
  rw [mem_fixed_iff (F := F) (M := M) (P := P)]
  intro σ
  rw [IsScalarTower.algebraMap_apply F (latticeFunctionField F M)
    (semiFunctionField (F := F) (M := M) (P := P)) c]
  rw [IsScalarTower.algebraMap_apply (latticeFunctionField F M)
    (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (semiFunctionField (F := F) (M := M) (P := P))
    (algebraMap F (latticeFunctionField F M) c)]
  rw [smul_algebraMap_semiAlg, semiAlgEquiv_algebraMap_lattice]
  rw [show coeffRingEquiv (M := M) σ (algebraMap F (latticeFunctionField F M) c)
      = σ • algebraMap F (latticeFunctionField F M) c from rfl]
  rw [smul_algebraMap_latticeFunctionField]

/-- `F →+* ↥(l(N)^G)`。 -/
noncomputable def algebraMapFixedSemi : F →+*
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) where
  toFun c := ⟨algebraMap F (semiFunctionField (F := F) (M := M) (P := P)) c,
    algebraMapF_mem_fixedSemi (F := F) (G := G) (M := M) (P := P) c⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- `↥(l(N)^G)` 上的 `F`-代数结构（`IsRational F ↥(l(N)^G)` 与组装所需）。 -/
noncomputable instance instAlgebraFixedSemi : Algebra F
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) :=
  (algebraMapFixedSemi (F := F) (G := G) (M := M) (P := P)).toAlgebra

/-- 标量塔 `F ≤ ↥K0 ≤ ↥(l(N)^G)`（`restrictScalars` 沿组装链换基）。 -/
noncomputable instance instIsScalarTowerK0 : IsScalarTower F
    ↥(K0 (G := G) (F := F) (M := M) (P := P))
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) :=
  IsScalarTower.of_algebraMap_eq (fun c => Subtype.ext rfl)

/-! ## 5. 具名接口 ＋ S5 组装

`S2Interface` 逐字同 Saltman `corollary:1.4`(i) 目标形（`l(N)^G` 在 `↥K0` 上有理）——Phase 2
已由 §7 的真定理消解（接口保留为组装算式与类型锁定的形状）；`S34Interface` 为 S3∘S4 复合
（载运 ＋ Fischer）之具名假设，射程见文件头偏差 5。 -/

/-- **S2 接口**（具名假设）：`l(N)^G` 有理于 `↥K0` —— 即 Saltman `corollary:1.4`(i)
「`F(M⊕P,G)` 有理于 `F(M,G)`」的 `l(N) ≡ F(M⊕P)` 陈述形。 -/
def S2Interface : Prop :=
  IsRational ↥(K0 (G := G) (F := F) (M := M) (P := P))
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))

/-- **S3∘S4 接口**（具名假设）：`l(N)^G` 有理于 `F`（载运到 `F(Q)^G` ＋ Fischer）。 -/
def S34Interface : Prop :=
  IsRational F
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))

example : S2Interface (F := F) (G := G) (M := M) (P := P)
    = IsRational ↥(K0 (G := G) (F := F) (M := M) (P := P))
        ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) := rfl

example : S34Interface (F := F) (G := G) (M := M) (P := P)
    = IsRational F
        ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) := rfl

/-- **S5 组装**：`F(M)^G(t_1..t_n) ≅ F(M⊕P)^G ≅ F(Q)^G ≅ F(s_1..s_m)` 的 Lean 算式：
`rationalFunctionField ↥(latticeInvariantsAlg F G M) n`
→（`invariantsAlgEquivK0`）`rationalFunctionField ↥K0 n`
→（`S2Interface`，取 `.restrictScalars F`）`↥(l(N)^G)`
→（`S34Interface`）`rationalFunctionField F m`。 -/
theorem isStablyRational_of_S2
    (hS2 : S2Interface (F := F) (G := G) (M := M) (P := P))
    (h34 : S34Interface (F := F) (G := G) (M := M) (P := P)) :
    IsStablyRational F ↥(latticeInvariantsAlg F G M) := by
  obtain ⟨n, ⟨e2⟩⟩ := hS2
  obtain ⟨m, ⟨e3⟩⟩ := h34
  refine ⟨n, m, ⟨?_⟩⟩
  exact ((rationalFunctionFieldAlgEquiv
      (invariantsAlgEquivK0 (F := F) (G := G) (M := M) (P := P)) n).trans
    ((e2.restrictScalars F).symm)).trans e3

/-- M5 目标（D1 `latticeInvariants` 子域形）：沿 `invariantsSubfieldAlgEquiv`
从 `latticeInvariantsAlg` 形搬运（偏差登记 4）。 -/
theorem isStablyRational_of_S2_subfield
    (hS2 : S2Interface (F := F) (G := G) (M := M) (P := P))
    (h34 : S34Interface (F := F) (G := G) (M := M) (P := P)) :
    IsStablyRational F ↥(latticeInvariants F G M) :=
  isStablyRational_of_algEquiv
    (invariantsSubfieldAlgEquiv (F := F) (G := G) (M := M))
    (isStablyRational_of_S2 hS2 h34)

/-! ## 6. S3／S4 接线样板（Phase 2 的插入点形状） -/

/-- **S3 载运（接线）**：有理性沿等变加法同构搬运（`EMTrans` §4
`isRational_latticeInvariantsAlg_iff`）。 -/
theorem isRational_latticeInvariantsAlg_of_transport
    {N N' : Type*} [AddCommGroup N] [Module ℤ N] [DistribMulAction G N]
    [SMulCommClass G ℤ N] [UniqueProds (Multiplicative N)]
    [AddCommGroup N'] [Module ℤ N'] [DistribMulAction G N'] [SMulCommClass G ℤ N']
    [UniqueProds (Multiplicative N')] (e : N ≃+ N')
    (he : ∀ (g : G) (n : N), e (g • n) = g • e n)
    (h : IsRational F ↥(latticeInvariantsAlg F G N')) :
    IsRational F ↥(latticeInvariantsAlg F G N) :=
  (isRational_latticeInvariantsAlg_iff (F := F) (G := G) e he).mpr h

/-- **S3∘S4 → `S34Interface`（接线形状）**：把 `Q` 侧的 Fischer 结论
（`IsRational F ↥(latticeInvariantsAlg F G N)`，`N ≅ M ⊕ P`）沿桥
`↥(latticeInvariantsAlg F G N) ≃ₐ[F] ↥(l(N)^G)` 搬到 `S34Interface`。
Phase 2 的接线点：桥（`l(N) ↔` 单格不变量，未做）＋ Fischer（D13，正则格）。 -/
theorem s34Interface_of_bridge
    {N : Type*} [AddCommGroup N] [Module ℤ N] [DistribMulAction G N]
    [SMulCommClass G ℤ N] [UniqueProds (Multiplicative N)]
    (b : ↥(latticeInvariantsAlg F G N) ≃ₐ[F]
      ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))))
    (h : IsRational F ↥(latticeInvariantsAlg F G N)) :
    S34Interface (F := F) (G := G) (M := M) (P := P) :=
  isRational_of_algEquiv b h

/-! ## 7. S2 接线（Phase 2）：以真定理消解 `S2Interface`

`isRational_fixedPoints`（`EMIndep_ABGV52.lean` §5）的 `hyfix` 用 `semiAlgEquiv` 记号，
而 `W_fixed_extraction`（`EMRational_ABGV52.lean` §3）输出 `actW … .smul` 形；二者相差一层
子类型投影（`actW` 的 `smul` 即 `⟨semiAlgEquiv σ w.1, _⟩`），以 `Subtype.ext_iff.mp` 转换。 -/

section S2Data

variable {ι : Type*} [Fintype ι]

/-- **S2 接线（数据形）**：置换基数据 ＋ `FaithfulSMul G (F(M))` ⟹ `S2Interface`
（Saltman `corollary:1.4`(i) 的机器化：真定理 `isRational_fixedPoints`）。 -/
theorem s2Interface_of_data
    (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    [FaithfulSMul G (latticeFunctionField F M)] :
    S2Interface (F := F) (G := G) (M := M) (P := P) := by
  obtain ⟨n, y, hyfix, hy_span, hy_indep⟩ :=
    W_fixed_extraction (F := F) (M := M) B ρ hρ
  exact isRational_fixedPoints (F := F) (G := G) (M := M) (P := P) B n y
    (fun i σ => Subtype.ext_iff.mp (hyfix i σ)) hy_span hy_indep

/-- **S2 接线（忠实性自 `M` 推出）**：EM 域类前提 `FaithfulSMul G M` 经
`faithfulSMul_latticeFunctionField`（M1）上升为 `FaithfulSMul G (F(M))`。 -/
theorem s2Interface_of_data'
    (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    (hfaith : FaithfulSMul G M) :
    S2Interface (F := F) (G := G) (M := M) (P := P) := by
  haveI := faithfulSMul_latticeFunctionField (F := F) (G := G) (M := M) hfaith
  exact s2Interface_of_data (F := F) (G := G) (M := M) (P := P) B ρ hρ

end S2Data

/-! ## 8. L1 非空洞探针与类型锁定 -/

/-- L1（谓词非空洞）：`IsRational` 有真实实例。 -/
theorem isRational_rationalFunctionField (A : Type*) [Field A] (n : ℕ) :
    IsRational A (rationalFunctionField A n) :=
  ⟨n, ⟨AlgEquiv.refl⟩⟩

/-- L1（谓词非空洞）：`IsStablyRational` 有真实实例。 -/
theorem isStablyRational_rationalFunctionField (A : Type*) [Field A] (n : ℕ) :
    IsStablyRational A (rationalFunctionField A n) :=
  (isRational_rationalFunctionField A n).isStablyRational

/-- L1（§2 桥非空洞）：平凡置换格（单点 `G`-集）上有真实的
`(B, ρ, hρ)` 见证——`exists_permBasis_of_isPermutationLattice` 实跑。
（`L` 经 `∃` 抽象绑定：对具体 `Rep.ofMulAction` 项，类型类合成无法反演 `↑` 系数
—— `inferInstance` 对 `DistribMulAction G ↥(Rep.ofMulAction …)` 失败 —— 故实例参数
在陈述层抽象合成、由代换复用。） -/
theorem exists_permBasis_trivial :
    ∃ (L : Rep ℤ G) (_ : IsPermutationLattice G L),
      ∃ (X : Type) (_ : Fintype X) (_ : MulAction G X)
        (B : Module.Basis X ℤ ↥L) (ρ : G →* Equiv.Perm X),
        ∀ (σ : G) (i : X),
          mulEquivOfSMul G ↥L σ (permMono (P := ↥L) B i)
            = permMono (P := ↥L) B (ρ σ i) := by
  refine ⟨Rep.ofMulAction ℤ G (PUnit : Type), isPermutationLattice_trivial G, ?_⟩
  exact exists_permBasis_of_isPermutationLattice _ (isPermutationLattice_trivial G)

/-! ## 9. 公理闸门（Phase 1 声明 ＋ §7 适配） -/

#print axioms instDistribMulActionRep
#print axioms mem_fixed_lattice_iff
#print axioms algebraMapF_mem_K0
#print axioms algebraMapF_mem_fixedSemi
#print axioms rationalFunctionFieldAlgEquiv
#print axioms isRational_of_algEquiv
#print axioms isRational_of_algEquiv_iff
#print axioms isStablyRational_of_algEquiv
#print axioms isStablyRational_of_algEquiv_iff
#print axioms core_bridge
#print axioms exists_permBasis_of_isPermutationLattice
#print axioms algebraMap_lattice_injective
#print axioms lGToK0_bijective
#print axioms lGToK0RingEquiv
#print axioms algebraMapK0
#print axioms instAlgebraK0
#print axioms invariantsAlgEquivK0
#print axioms instAlgebraLatticeInvariants
#print axioms invariantsSubfieldAlgEquiv
#print axioms algebraMapFixedSemi
#print axioms instAlgebraFixedSemi
#print axioms instIsScalarTowerK0
#print axioms isStablyRational_of_S2
#print axioms isStablyRational_of_S2_subfield
#print axioms isRational_latticeInvariantsAlg_of_transport
#print axioms s34Interface_of_bridge
#print axioms s2Interface_of_data
#print axioms s2Interface_of_data'
#print axioms isRational_rationalFunctionField
#print axioms isStablyRational_rationalFunctionField
#print axioms exists_permBasis_trivial

end

/-! ## 10. Phase 2 主定理收口（A13 子情形：`Q = 单块正则`）

射程（A13）：D13 的 Fischer 只到正则格 `A → ℤ`（偏差 5）；`G` 为交换群（D13 需 `CommGroup`）。
本节把 §7 的 S2 接线与正则格 Fischer 复合，收口主定理；桥 `b` 是 S3∘S4 二步局部化识别
（偏差 3）的具名残余。L1：正则格数据上 `S2Interface` 无条件可实例化（§10 末三件）。 -/

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F]
variable {G : Type*} [CommGroup G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]

/-- **S4 接线（正则格）**：`F` 有足够单位根时正则格不变量域有理
（`D13_ABGV52.lean:456` `isRational_latticeInvariantsAlg` 在 `A := G` 的实例化）。 -/
theorem isRational_latticeInvariantsAlg_regular
    [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)] :
    IsRational F ↥(latticeInvariantsAlg F G (G → ℤ)) :=
  isRational_latticeInvariantsAlg (F := F) (A := G)

/-- **S3∘S4 → `S34Interface`（正则格 ＋ 桥）**：Fischer 结论沿桥 `b` 搬到 `↥(l(N)^G)`。 -/
theorem s34Interface_of_fischer_regular
    [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    (b : ↥(latticeInvariantsAlg F G (G → ℤ)) ≃ₐ[F]
      ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))) :
    S34Interface (F := F) (G := G) (M := M) (P := P) :=
  s34Interface_of_bridge (F := F) (G := G) (M := M) (P := P) (N := (G → ℤ)) b
    (isRational_latticeInvariantsAlg_regular (F := F) (G := G))

/-- **主定理（A13 子情形：`Q = 单块正则`）**：置换基数据（S3 形）＋ 忠实性 ＋
包含正则格的 S3∘S4 桥 ⟹ `F(M)^G` 稳定有理。 -/
theorem isStablyRational_of_regularSubcase
    [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    (hfaith : FaithfulSMul G M)
    {ι : Type*} [Fintype ι] (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    (b : ↥(latticeInvariantsAlg F G (G → ℤ)) ≃ₐ[F]
      ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))) :
    IsStablyRational F ↥(latticeInvariantsAlg F G M) :=
  isStablyRational_of_S2
    (s2Interface_of_data' (F := F) (G := G) (M := M) (P := P) B ρ hρ hfaith)
    (s34Interface_of_fischer_regular (F := F) (G := G) (M := M) (P := P) b)

/-- 主定理之子域形（D1 `latticeInvariants`，偏差 4 的搬运形式）。 -/
theorem isStablyRational_of_regularSubcase_subfield
    [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    (hfaith : FaithfulSMul G M)
    {ι : Type*} [Fintype ι] (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    (b : ↥(latticeInvariantsAlg F G (G → ℤ)) ≃ₐ[F]
      ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))) :
    IsStablyRational F ↥(latticeInvariants F G M) :=
  isStablyRational_of_algEquiv
    (invariantsSubfieldAlgEquiv (F := F) (G := G) (M := M))
    (isStablyRational_of_regularSubcase (F := F) (G := G) (M := M) (P := P)
      hfaith B ρ hρ b)

/-- **L1（数据非空洞）**：正则格 `G → ℤ` 上置换基数据 `(B, ρ, hρ)` **无条件**存在
（`Pi.basisFun` ＋ `MulAction.toPermHom`）。 -/
theorem exists_permBasis_regular :
    ∃ (B : Module.Basis G ℤ (G → ℤ)) (ρ : G →* Equiv.Perm G),
      ∀ (σ : G) (i : G),
        mulEquivOfSMul G (G → ℤ) σ (permMono (P := (G → ℤ)) B i)
          = permMono (P := (G → ℤ)) B (ρ σ i) := by
  classical
  refine ⟨Pi.basisFun ℤ G, MulAction.toPermHom G G, ?_⟩
  intro σ i
  rw [mulEquivOfSMul_apply]
  show Multiplicative.ofAdd (σ • (Pi.basisFun ℤ G) i)
    = Multiplicative.ofAdd ((Pi.basisFun ℤ G) (MulAction.toPermHom G G σ i))
  congr 1
  have hperm : MulAction.toPermHom G G σ i = σ * i := by
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_eq_mul]
  rw [hperm]
  funext b
  show (Pi.basisFun ℤ G i) (σ⁻¹ * b) = (Pi.basisFun ℤ G) (σ * i) b
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  by_cases hb : σ⁻¹ * b = i
  · have hb' : b = σ * i := (inv_mul_eq_iff_eq_mul (a := σ) (b := b) (c := i)).mp hb
    subst hb'
    rw [inv_mul_cancel_left, Pi.single_eq_same, Pi.single_eq_same]
  · have hb' : b ≠ σ * i := fun h => hb (by rw [h, inv_mul_cancel_left])
    rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb']

/-- **L1（忠实性可满足）**：正则格上 `G` 作用忠实（`δ₁` 的轨道分离）。 -/
theorem faithfulSMul_regularLattice : FaithfulSMul G (G → ℤ) := by
  classical
  rw [faithfulSMul_iff]
  intro g hg
  by_contra hne
  have h1 := congr_fun (hg (fun j : G => if j = 1 then (1 : ℤ) else 0)) g
  have h2 : (1 : ℤ) = 0 := by
    rw [show (g • (fun j : G => if j = 1 then (1 : ℤ) else 0)) g
          = (fun j : G => if j = 1 then (1 : ℤ) else 0) (g⁻¹ * g) from rfl] at h1
    simp [hne] at h1
  exact one_ne_zero h2

/-- **L1（复合探针）**：正则格数据（`M = P = G → ℤ`）上 `S2Interface` **无条件**可实例化
——Saltman S2 在本子情形无残余前提（S3 数据由 `exists_permBasis_regular` 供给，
忠实性由 `faithfulSMul_regularLattice` 供给）。 -/
theorem s2Interface_regular_nonvacuous :
    S2Interface (F := F) (G := G) (M := (G → ℤ)) (P := (G → ℤ)) := by
  obtain ⟨B, ρ, hρ⟩ := exists_permBasis_regular (G := G)
  exact s2Interface_of_data' (F := F) (G := G) (M := (G → ℤ)) (P := (G → ℤ))
    B ρ hρ faithfulSMul_regularLattice

end

/-! ## 11. Phase 2 公理闸门（§10 声明） -/

#print axioms isRational_latticeInvariantsAlg_regular
#print axioms s34Interface_of_fischer_regular
#print axioms isStablyRational_of_regularSubcase
#print axioms isStablyRational_of_regularSubcase_subfield
#print axioms exists_permBasis_regular
#print axioms faithfulSMul_regularLattice
#print axioms s2Interface_regular_nonvacuous

end RouteS

end EM

end ABGV52
