/-
# EMBridge（EM 轨 T1）：桥 `b` 的消解 —— 绝对识别 `l(N) ≅ F(M ⊕ P)` ＋ S3 落点（2026-10-08）

**目标（本件）**：消解 `EMRouteS_ABGV52.lean` 主定理 `isStablyRational_of_regularSubcase`
的唯一具名残余假设（偏差登记 3／5 合并件）

```
b : ↥(latticeInvariantsAlg F G (G → ℤ)) ≃ₐ[F] ↥(FixedPoints.subfield G (semiFunctionField F M P))
```

即把该假设变成**定理**：新主定理以格等价数据
`e : M × P ≃+ (G → ℤ)`（等变）＋ S3 数据 `(B, ρ, hρ)` 为输入，**无条件构造** `b`。

**分解（三步）**：
1. **(i) 绝对识别** `semiFunctionField F M P ≅ F(M × P)`：
   - §1 **δ**：`F[Multiplicative (M × P)] ≃ₐ[F] (F[Multiplicative M])[Multiplicative P]`
     （`domCongr`（分量重排）＋ `curryAlgEquiv`——mathlib「两步 MonoidAlgebra」）；
   - §2 **系数局部化步** `Frac((Frac F[M])[P]) ≅ Frac((F[M])[P])`：
     经 `IsFractionRing.of_field`（商式满射）＋**系数清算引理**（`Clearing`）＋
     `IsFractionRing.lift`（沿显式 `gX` 提升，公式可控）。
2. **(ii) 等变性**：`β₁ := J' ≪ δ-载运` 沿 `semiAlgEquiv`-作用与
   `latticeAlgebraActionHom`-作用的逐点对比（§3；生成元归约 =
   `IsFractionRing.ringHom_ext` ＋ `mPartAlgHom`-等变性 ＋ χ-等变性）。
3. **(iii) S3 落点**：`M × P ≅ (G → ℤ)` 的等变 `AddEquiv e` ⟹ 不变量域载运
   （`EMTrans.latticeInvariantsAlgTransport`，已有）＋ 固定域层运输（§4）⟹ **桥 b**。

**主定理（§5）**：`isStablyRational_of_regularSubcase_bridged`——与
`EMRouteS.isStablyRational_of_regularSubcase` 同结论、去桥假设（`e` ＋ `he` 代之）。

**偏差登记**：
1. 本件**不改动** `EMRouteS_ABGV52.lean`（其具名桥保留为历史接口）；消解以**新定理**给出。
2. `UniqueProds (Multiplicative (M × P))` 由两分量经 `MulEquiv.uniqueProds_iff`
   （`Prod.instUniqueProds`）**推导**（实例 `instUniqueProdsMultiplicativeProd`），
   不作假设。
3. 射程声明（A13）：S4 Fischer 仍只到正则格（D13）；本件只消 S3∘S4 侧的桥 `b`。

**无 sorry、无自造公理**；`#print axioms` 闸门见 §6。
-/
import ABGV52.EMRouteS_ABGV52

namespace ABGV52

namespace EM

namespace Bridge

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]

/-! ## 0. 乘积格的 `UniqueProds`（自两分量推导） -/

/-- `Multiplicative (M × P) ≃* Multiplicative P × Multiplicative M`（分量重排）。 -/
def multiProdEquiv : Multiplicative (M × P) ≃* Multiplicative P × Multiplicative M where
  toFun x := (Multiplicative.ofAdd x.toAdd.2, Multiplicative.ofAdd x.toAdd.1)
  invFun y := Multiplicative.ofAdd (y.2.toAdd, y.1.toAdd)
  left_inv x := by
    show (Multiplicative.ofAdd ((Multiplicative.ofAdd (x.toAdd.2, x.toAdd.1)).toAdd.2),
      Multiplicative.ofAdd ((Multiplicative.ofAdd (x.toAdd.2, x.toAdd.1)).toAdd.1)) = x
    exact Prod.ext rfl rfl
  right_inv y := by
    show (Multiplicative.ofAdd ((Multiplicative.ofAdd (y.2.toAdd, y.1.toAdd)).toAdd.2),
      Multiplicative.ofAdd ((Multiplicative.ofAdd (y.2.toAdd, y.1.toAdd)).toAdd.1)) = y
    exact Prod.ext rfl rfl
  map_mul' x y := rfl

@[simp] lemma multiProdEquiv_apply (x : Multiplicative (M × P)) :
    multiProdEquiv (M := M) (P := P) x
      = (Multiplicative.ofAdd x.toAdd.2, Multiplicative.ofAdd x.toAdd.1) := rfl

@[simp] lemma multiProdEquiv_symm_apply (y : Multiplicative P × Multiplicative M) :
    (multiProdEquiv (M := M) (P := P)).symm y
      = Multiplicative.ofAdd (y.2.toAdd, y.1.toAdd) := rfl

/-- 乘积格的 `UniqueProds`（供 `F[Multiplicative (M × P)]` 的分式域结构用；
由两分量的 `UniqueProds (Multiplicative ·)` 经 `Prod.instUniqueProds` ＋ `MulEquiv` 搬运）。 -/
instance instUniqueProdsMultiplicativeProd : UniqueProds (Multiplicative (M × P)) :=
  (MulEquiv.uniqueProds_iff (multiProdEquiv (M := M) (P := P))).mpr inferInstance

/-! ## 1. δ：`F[Multiplicative (M × P)] ≃ₐ[F] (F[Multiplicative M])[Multiplicative P]`

两步 MonoidAlgebra 分解（`curryAlgEquiv` ＋ 分量重排 `domCongr`）。
**注意**：`MonoidAlgebra.curryAlgEquiv : A[M × N] ≃ₐ[R] A[N][M]`
（外层指标 `M`）；取 `M := Multiplicative P`、`N := Multiplicative M`
（配合 `multiProdEquiv` 的分量序）使外层为 `P`、系数为 `F[Multiplicative M]`。 -/

/-- `domCongr` 在单项式上的公式（`mapDomainRingEquiv_single` 的包装）。 -/
lemma domCongr_single_apply
    (e : Multiplicative (M × P) ≃* Multiplicative P × Multiplicative M)
    (x : Multiplicative (M × P)) (a : F) :
    MonoidAlgebra.domCongr F F e (MonoidAlgebra.single x a)
      = MonoidAlgebra.single (e x) a := by
  show MonoidAlgebra.mapDomainRingEquiv F e (MonoidAlgebra.single x a) = _
  rw [MonoidAlgebra.mapDomainRingEquiv_single]

/-- `latticeAlgebraEquiv` 在单项式上的公式（`latticeAlgebraEquiv` 是 `domCongr` 的
`mulEquivOfSMul` 实例化）。 -/
lemma latticeAlgebraEquiv_single (σ : G) (m : Multiplicative M) (a : F) :
    latticeAlgebraEquiv F G M σ (MonoidAlgebra.single m a)
      = MonoidAlgebra.single (mulEquivOfSMul G M σ m) a :=
  MonoidAlgebra.mapDomainRingEquiv_single _ a m

/-- **两步分解** δ：`F[Multiplicative (M × P)] ≃ₐ[F] F[Multiplicative M][Multiplicative P]`。 -/
noncomputable def splitAlgEquiv :
    MonoidAlgebra F (Multiplicative (M × P)) ≃ₐ[F]
      MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P) :=
  (MonoidAlgebra.domCongr F F (multiProdEquiv (M := M) (P := P))).trans
    (MonoidAlgebra.curryAlgEquiv F)

/-- δ 的单项式公式。 -/
lemma splitAlgEquiv_single (x : Multiplicative (M × P)) (a : F) :
    splitAlgEquiv (M := M) (P := P) (MonoidAlgebra.single x a)
      = MonoidAlgebra.single (Multiplicative.ofAdd x.toAdd.2)
          (MonoidAlgebra.single (Multiplicative.ofAdd x.toAdd.1) a) := by
  rw [splitAlgEquiv, AlgEquiv.trans_apply, domCongr_single_apply]
  rw [show multiProdEquiv (M := M) (P := P) x
      = (Multiplicative.ofAdd x.toAdd.2, Multiplicative.ofAdd x.toAdd.1) from rfl]
  rw [MonoidAlgebra.curryAlgEquiv_single]

/-! ## 2. M-分量嵌入 `mPartAlgHom`（单项式 `m ↦ (m, 0)`）及其等变性 -/

/-- 单项式嵌入 `Multiplicative M →* F[Multiplicative (M × P)]`（`m ↦ x^{(m,0)}`）。 -/
noncomputable def mPartMonoidHom :
    Multiplicative M →* MonoidAlgebra F (Multiplicative (M × P)) where
  toFun m := MonoidAlgebra.single (Multiplicative.ofAdd (m.toAdd, 0)) 1
  map_one' := by
    show MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), (0 : P))) (1 : F) = 1
    rw [show (Multiplicative.ofAdd ((0 : M), (0 : P)) : Multiplicative (M × P)) = 1 from
      rfl]
    exact MonoidAlgebra.one_def.symm
  map_mul' m n := by
    show MonoidAlgebra.single (Multiplicative.ofAdd ((m * n).toAdd, 0)) (1 : F)
      = MonoidAlgebra.single (Multiplicative.ofAdd (m.toAdd, 0)) (1 : F)
        * MonoidAlgebra.single (Multiplicative.ofAdd (n.toAdd, 0)) (1 : F)
    rw [MonoidAlgebra.single_mul_single]
    rw [show (Multiplicative.ofAdd (m.toAdd, (0 : P))
        * Multiplicative.ofAdd (n.toAdd, (0 : P)) : Multiplicative (M × P))
        = Multiplicative.ofAdd ((m * n).toAdd, (0 : P)) from by
      show Multiplicative.ofAdd ((m.toAdd, (0 : P)) + (n.toAdd, (0 : P)))
        = Multiplicative.ofAdd ((m * n).toAdd, (0 : P))
      rw [show ((m.toAdd, (0 : P)) + (n.toAdd, (0 : P)) : M × P)
          = (m.toAdd + n.toAdd, (0 : P)) from by simp]
      rw [show (m * n).toAdd = m.toAdd + n.toAdd from rfl]]
    rw [mul_one]

/-- **M-分量嵌入** `F[M] →ₐ[F] F[Multiplicative (M × P)]`（系数不动，单项式 `m ↦ (m, 0)`）。
经 `MonoidAlgebra.lift`（= 单项式同态的代数提升；`lift_of`／`commutes'` 给可计算性）。 -/
noncomputable def mPartAlgHom :
    MonoidAlgebra F (Multiplicative M) →ₐ[F] MonoidAlgebra F (Multiplicative (M × P)) :=
  MonoidAlgebra.lift F (MonoidAlgebra F (Multiplicative (M × P))) (Multiplicative M)
    (mPartMonoidHom (F := F) (M := M) (P := P))

/-- `mPartAlgHom` 的单项式公式（分解律 `single = algebraMap * of` ＋ `lift_of`）。 -/
lemma mPartAlgHom_single (m : Multiplicative M) (a : F) :
    mPartAlgHom (M := M) (P := P) (MonoidAlgebra.single m a)
      = MonoidAlgebra.single (Multiplicative.ofAdd (m.toAdd, 0)) a := by
  rw [MonoidAlgebra.single_eq_algebraMap_mul_of (R := F) (M := Multiplicative M) m a]
  rw [map_mul]
  rw [show mPartAlgHom (M := M) (P := P)
        (algebraMap F (MonoidAlgebra F (Multiplicative M)) a)
      = algebraMap F (MonoidAlgebra F (Multiplicative (M × P))) a from
    (mPartAlgHom (M := M) (P := P)).commutes' a]
  rw [show mPartAlgHom (M := M) (P := P) (MonoidAlgebra.of F (Multiplicative M) m)
      = MonoidAlgebra.of F (Multiplicative (M × P)) (Multiplicative.ofAdd (m.toAdd, 0)) from
    MonoidAlgebra.lift_of (mPartMonoidHom (F := F) (M := M) (P := P)) m]
  rw [← MonoidAlgebra.single_eq_algebraMap_mul_of (R := F)
    (M := Multiplicative (M × P)) (Multiplicative.ofAdd (m.toAdd, 0)) a]

/-! ## 3. δ.symm 在两类单项式上的公式（供 λ-公式与等变性用） -/

/-- δ.symm 在「P-单项式」上的公式（系数 1）。 -/
lemma splitAlgEquiv_symm_single_P (p : Multiplicative P) :
    (splitAlgEquiv (M := M) (P := P)).symm
        (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M)))
      = MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), p.toAdd)) (1 : F) := by
  apply (splitAlgEquiv (M := M) (P := P)).injective
  rw [AlgEquiv.apply_symm_apply, splitAlgEquiv_single]
  rfl

/-- δ.symm 在「M-系数单项式」上的公式（系数 `single m 1`）。 -/
lemma splitAlgEquiv_symm_single_one_of (m : Multiplicative M) :
    (splitAlgEquiv (M := M) (P := P)).symm
        (MonoidAlgebra.single (1 : Multiplicative P)
          (MonoidAlgebra.single m (1 : F)))
      = MonoidAlgebra.single (Multiplicative.ofAdd (m.toAdd, 0)) (1 : F) := by
  apply (splitAlgEquiv (M := M) (P := P)).injective
  rw [AlgEquiv.apply_symm_apply, splitAlgEquiv_single]
  rfl

/-- δ 在 M-分量嵌入上的公式（`δ ∘ η = single 1`）。 -/
lemma splitAlgEquiv_mPart (a : MonoidAlgebra F (Multiplicative M)) :
    splitAlgEquiv (M := M) (P := P) (mPartAlgHom (M := M) (P := P) a)
      = MonoidAlgebra.single (1 : Multiplicative P) a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, MonoidAlgebra.single_add, hx, hy]
  | single m c =>
      rw [mPartAlgHom_single, splitAlgEquiv_single]
      rfl

/-- δ.symm 在「M-系数一般元」上的公式。 -/
lemma splitAlgEquiv_symm_single_one (a : MonoidAlgebra F (Multiplicative M)) :
    (splitAlgEquiv (M := M) (P := P)).symm
        (MonoidAlgebra.single (1 : Multiplicative P) a)
      = mPartAlgHom (M := M) (P := P) a := by
  apply (splitAlgEquiv (M := M) (P := P)).injective
  rw [AlgEquiv.apply_symm_apply, splitAlgEquiv_mPart]

/-- `mPartAlgHom` 的等变性：`η(g • a) = g • η(a)`（两轴单项式作用逐点一致）。 -/
lemma mPartAlgHom_equivariant (σ : G) (a : MonoidAlgebra F (Multiplicative M)) :
    mPartAlgHom (M := M) (P := P) (latticeAlgebraEquiv F G M σ a)
      = latticeAlgebraEquiv F G (M × P) σ (mPartAlgHom (M := M) (P := P) a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]
  | single m c =>
      rw [latticeAlgebraEquiv_single, mPartAlgHom_single, mPartAlgHom_single,
        latticeAlgebraEquiv_single, mulEquivOfSMul_apply]
      change MonoidAlgebra.single (Multiplicative.ofAdd (σ • m.toAdd, (0 : P))) c
          = MonoidAlgebra.single (Multiplicative.ofAdd (σ • (m.toAdd, (0 : P)))) c
      rw [show (σ • (m.toAdd, (0 : P))) = (σ • m.toAdd, σ • (0 : P)) from rfl, smul_zero]

/-! ## 4. 系数局部化步：`C := (F[M])[P] ↪ X := (F(M))[P]`，清算与 `IsFractionRing C semi` -/

/-- **系数扩张** `C →ₐ[F] X`（`A ↪ Frac A`、单项式不动；
`C = (F[M])[P]`、`X = (F(M))[P]`、`l = F(M)`）。 -/
noncomputable def hmap :
    MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P) →ₐ[F]
      MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) :=
  MonoidAlgebra.mapAlgHom (M := Multiplicative P)
    (IsScalarTower.toAlgHom F (MonoidAlgebra F (Multiplicative M))
      (latticeFunctionField F M))

/-- `hmap` 的单项式公式。 -/
lemma hmap_single (p : Multiplicative P) (a : MonoidAlgebra F (Multiplicative M)) :
    hmap (M := M) (P := P) (MonoidAlgebra.single p a)
      = MonoidAlgebra.single p (algebraMap (MonoidAlgebra F (Multiplicative M))
          (latticeFunctionField F M) a) :=
  MonoidAlgebra.mapAlgHom_single
    (f := IsScalarTower.toAlgHom F (MonoidAlgebra F (Multiplicative M))
      (latticeFunctionField F M)) (m := p) (a := a)

set_option maxHeartbeats 1000000 in
/-- `hmap` 单射（系数提取 ＋ `Frac` 单射）。 -/
lemma hmap_injective : Function.Injective (hmap (F := F) (M := M) (P := P)) := by
  intro x y hxy
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro p
  apply IsFractionRing.injective (MonoidAlgebra F (Multiplicative M))
    (latticeFunctionField F M)
  show (MonoidAlgebra.mapAlgHom (M := Multiplicative P)
      (IsScalarTower.toAlgHom F (MonoidAlgebra F (Multiplicative M))
        (latticeFunctionField F M)) x).coeff p
    = (MonoidAlgebra.mapAlgHom (M := Multiplicative P)
      (IsScalarTower.toAlgHom F (MonoidAlgebra F (Multiplicative M))
        (latticeFunctionField F M)) y).coeff p
  exact congrArg (fun z : MonoidAlgebra (latticeFunctionField F M)
    (Multiplicative P) => z.coeff p) hxy

/-- `single 1 β ≠ 0`（当 `β ≠ 0`；`single_eq_zero`）。 -/
lemma single_one_ne_zero (β : MonoidAlgebra F (Multiplicative M)) (hβ : β ≠ 0) :
    MonoidAlgebra.single (1 : Multiplicative P) β ≠ 0 :=
  fun h => hβ ((MonoidAlgebra.single_eq_zero).mp h)

set_option maxHeartbeats 20000000 in
/-- **系数清算**：`X` 的元素乘恰当「系数分母」后落入 `C` 的像。 -/
lemma clearing (x : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) :
    ∃ (β : MonoidAlgebra F (Multiplicative M))
      (x₀ : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)),
      β ≠ 0 ∧ x * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β)
        = hmap (M := M) (P := P) x₀ := by
  induction x using MonoidAlgebra.induction_on with
  | of p =>
      rw [show MonoidAlgebra.of (latticeFunctionField F M) (Multiplicative P) p
          = MonoidAlgebra.single p (1 : latticeFunctionField F M) from rfl]
      refine ⟨1, MonoidAlgebra.single p 1, one_ne_zero, ?_⟩
      rw [show hmap (M := M) (P := P)
            (MonoidAlgebra.single (1 : Multiplicative P)
              (1 : MonoidAlgebra F (Multiplicative M))) = 1 from by
          rw [hmap_single, map_one]
          exact MonoidAlgebra.one_def.symm,
        show hmap (M := M) (P := P)
            (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M)))
          = MonoidAlgebra.single p (1 : latticeFunctionField F M) from by
          rw [hmap_single, map_one]]
      rw [mul_one]
  | add x y hx hy =>
      obtain ⟨β₁, x₁, hβ₁, hx₁⟩ := hx
      obtain ⟨β₂, x₂, hβ₂, hx₂⟩ := hy
      refine ⟨β₁ * β₂,
        x₁ * MonoidAlgebra.single (1 : Multiplicative P) β₂
          + x₂ * MonoidAlgebra.single (1 : Multiplicative P) β₁,
        mul_ne_zero hβ₁ hβ₂, ?_⟩
      rw [show hmap (M := M) (P := P)
            (x₁ * MonoidAlgebra.single (1 : Multiplicative P) β₂
              + x₂ * MonoidAlgebra.single (1 : Multiplicative P) β₁)
          = hmap (M := M) (P := P) (x₁ * MonoidAlgebra.single (1 : Multiplicative P) β₂)
            + hmap (M := M) (P := P) (x₂ * MonoidAlgebra.single (1 : Multiplicative P) β₁)
          from map_add _ _ _]
      rw [show hmap (M := M) (P := P) (x₁ * MonoidAlgebra.single (1 : Multiplicative P) β₂)
          = hmap (M := M) (P := P) x₁
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂)
          from map_mul _ _ _]
      rw [show hmap (M := M) (P := P) (x₂ * MonoidAlgebra.single (1 : Multiplicative P) β₁)
          = hmap (M := M) (P := P) x₂
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁)
          from map_mul _ _ _]
      rw [show hmap (M := M) (P := P)
            (MonoidAlgebra.single (1 : Multiplicative P) (β₁ * β₂))
          = MonoidAlgebra.single (1 : Multiplicative P)
              (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M)
                (β₁ * β₂)) from hmap_single 1 (β₁ * β₂)]
      rw [show (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M)
              (β₁ * β₂))
          = algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) β₁
            * algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) β₂
          from map_mul _ _ _]
      rw [show MonoidAlgebra.single (1 : Multiplicative P)
            (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) β₁
              * algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) β₂)
          = hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁)
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂) from by
          simp only [hmap_single, MonoidAlgebra.single_mul_single, one_mul]]
      rw [add_mul]
      rw [show x * (hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁)
              * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂))
          = (x * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁))
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂) from
        (mul_assoc x _ _).symm]
      rw [show y * (hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁)
              * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂))
          = (y * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂))
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁) from by
        ac_rfl]
      rw [hx₁, hx₂]
  | smul r x hx =>
      obtain ⟨β, x₀, hβ, hx₀⟩ := hx
      obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective
        (A := MonoidAlgebra F (Multiplicative M)) (K := latticeFunctionField F M) r
      have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
      have hr : r * algebraMap (MonoidAlgebra F (Multiplicative M))
            (latticeFunctionField F M) b
          = algebraMap (MonoidAlgebra F (Multiplicative M))
            (latticeFunctionField F M) a := by
        rw [← hdiv]
        exact div_mul_cancel₀ _ (fun h0 => hb' (IsFractionRing.injective
          (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M)
          (by rw [h0, map_zero])))
      refine ⟨b * β, x₀ * MonoidAlgebra.single (1 : Multiplicative P) a,
        mul_ne_zero hb' hβ, ?_⟩
      rw [show hmap (M := M) (P := P) (x₀ * MonoidAlgebra.single (1 : Multiplicative P) a)
          = hmap (M := M) (P := P) x₀
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) a)
          from map_mul _ _ _]
      rw [show hmap (M := M) (P := P)
            (MonoidAlgebra.single (1 : Multiplicative P) (b * β))
          = MonoidAlgebra.single (1 : Multiplicative P)
              (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M)
                (b * β)) from hmap_single 1 (b * β)]
      rw [show hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) a)
          = MonoidAlgebra.single (1 : Multiplicative P)
              (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) a)
          from hmap_single 1 a]
      rw [show (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M)
              (b * β))
          = algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) b
            * algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) β
          from map_mul _ _ _]
      rw [show MonoidAlgebra.single (1 : Multiplicative P)
            (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) b
              * algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) β)
          = MonoidAlgebra.single (1 : Multiplicative P)
              (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) b)
            * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β) from by
          simp only [hmap_single, MonoidAlgebra.single_mul_single, one_mul]]
      rw [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Function.comp_apply,
        Algebra.algebraMap_self_apply]
      rw [show (MonoidAlgebra.single (1 : Multiplicative P) r * x)
              * (MonoidAlgebra.single (1 : Multiplicative P)
                  (algebraMap (MonoidAlgebra F (Multiplicative M))
                    (latticeFunctionField F M) b)
                * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β))
            = (MonoidAlgebra.single (1 : Multiplicative P) r
                * MonoidAlgebra.single (1 : Multiplicative P)
                  (algebraMap (MonoidAlgebra F (Multiplicative M))
                    (latticeFunctionField F M) b))
              * (x * hmap (M := M) (P := P)
                  (MonoidAlgebra.single (1 : Multiplicative P) β)) from by
        ac_rfl]
      rw [hx₀]
      rw [MonoidAlgebra.single_mul_single, one_mul, hr]
      rw [show MonoidAlgebra.single (1 : Multiplicative P)
            (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) a)
            * hmap (M := M) (P := P) x₀
          = hmap (M := M) (P := P) x₀
            * MonoidAlgebra.single (1 : Multiplicative P)
              (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) a)
          from mul_comm _ _]

/-- `C →+* semiFunctionField`（系数扩张 ＋ 分式域；`C = (F[M])[P]`）。 -/
noncomputable def algebraMapCSemi :
    MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P) →+*
      semiFunctionField (F := F) (M := M) (P := P) :=
  (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (semiFunctionField (F := F) (M := M) (P := P))).comp (hmap (F := F) (M := M) (P := P))

noncomputable instance instAlgebraCSemi :
    Algebra (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) :=
  (algebraMapCSemi (F := F) (M := M) (P := P)).toAlgebra

instance instFaithfulSMulCSemi :
    FaithfulSMul (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab =>
    hmap_injective (F := F) (M := M) (P := P)
      (IsFractionRing.injective (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)) hab)

/-- **系数局部化步**（`IsFractionRing.of_field`）：`semiFunctionField` 是 `C` 的分式环
（商式满射 = 清算 ＋ 交叉相乘）。 -/
theorem isFractionRing_C_semi :
    IsFractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) := by
  refine IsFractionRing.of_field
    (R := MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
    (K := semiFunctionField (F := F) (M := M) (P := P)) fun z => ?_
  obtain ⟨x, y, hy, hzy⟩ := IsFractionRing.div_surjective
    (A := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (K := semiFunctionField (F := F) (M := M) (P := P)) z
  obtain ⟨β₁, x₀, hβ₁, hx₀⟩ := clearing (F := F) (M := M) (P := P) x
  obtain ⟨β₂, y₀, hβ₂, hy₀⟩ := clearing (F := F) (M := M) (P := P) y
  have hy' : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  have hd₁ : hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁) ≠ 0 :=
    fun h0 => single_one_ne_zero (M := M) (P := P) β₁ hβ₁
      (hmap_injective (F := F) (M := M) (P := P) (by rw [h0, map_zero]))
  have hd₂ : hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂) ≠ 0 :=
    fun h0 => single_one_ne_zero (M := M) (P := P) β₂ hβ₂
      (hmap_injective (F := F) (M := M) (P := P) (by rw [h0, map_zero]))
  have hyA : algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) y ≠ 0 :=
    fun h0 => hy' (IsFractionRing.injective
      (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) (by rw [h0, map_zero]))
  have hD : algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P))
      ((y * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂))
        * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁)) ≠ 0 :=
    fun h0 => mul_ne_zero (mul_ne_zero hy' hd₂) hd₁ (IsFractionRing.injective
      (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) (by rw [h0, map_zero]))
  refine ⟨x₀ * MonoidAlgebra.single (1 : Multiplicative P) β₂,
    y₀ * MonoidAlgebra.single (1 : Multiplicative P) β₁, ?_⟩
  rw [← hzy]
  have hN : algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (x₀ * MonoidAlgebra.single (1 : Multiplicative P) β₂)
      = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        ((x * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁))
          * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂)) := by
    show algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (hmap (M := M) (P := P) (x₀ * MonoidAlgebra.single (1 : Multiplicative P) β₂)) = _
    rw [map_mul, ← hx₀]
  have hD' : algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (y₀ * MonoidAlgebra.single (1 : Multiplicative P) β₁)
      = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        ((y * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂))
          * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁)) := by
    show algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (hmap (M := M) (P := P) (y₀ * MonoidAlgebra.single (1 : Multiplicative P) β₁)) = _
    rw [map_mul, ← hy₀]
  rw [hN, hD']
  rw [div_eq_div_iff hyA hD]
  rw [← map_mul, ← map_mul]
  rw [show x * ((y * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂))
          * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁))
      = ((x * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₁))
          * hmap (M := M) (P := P) (MonoidAlgebra.single (1 : Multiplicative P) β₂)) * y from by
    ac_rfl]

/-\! ## 5. C-作用、`δ.symm`-作用交换、`J : semi ≃ₐ[F] FractionRing C` -/

/-- `C` 上的「半线性」环等价：`single p a ↦ single (σp) (σ·a)`（系数轴 `latticeAlgebraEquiv`）。 -/
noncomputable def cRingEquiv (σ : G) :
    MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P) ≃+*
      MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P) :=
  (MonoidAlgebra.mapDomainRingEquiv (MonoidAlgebra F (Multiplicative M))
    (mulEquivOfSMul G P σ)).trans
    (MonoidAlgebra.mapRingEquiv (Multiplicative P) (latticeAlgebraEquiv F G M σ))

/-- `cRingEquiv` 的单项式公式。 -/
lemma cRingEquiv_single (σ : G) (p : Multiplicative P)
    (a : MonoidAlgebra F (Multiplicative M)) :
    cRingEquiv (M := M) (P := P) σ (MonoidAlgebra.single p a)
      = MonoidAlgebra.single (mulEquivOfSMul G P σ p) (latticeAlgebraEquiv F G M σ a) := by
  show (MonoidAlgebra.mapRingEquiv (Multiplicative P) (latticeAlgebraEquiv F G M σ))
    ((MonoidAlgebra.mapDomainRingEquiv (MonoidAlgebra F (Multiplicative M))
      (mulEquivOfSMul G P σ)) (MonoidAlgebra.single p a)) = _
  rw [MonoidAlgebra.mapDomainRingEquiv_single, MonoidAlgebra.mapRingEquiv_single]

set_option maxHeartbeats 2000000 in
/-- 半函数域作用与 `hmap` 交换：`σ • hmap c = hmap (cRingEquiv σ c)`。 -/
lemma semiAlgEquiv_hmap (σ : G)
    (c : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :
    semiAlgEquiv (G := G) (M := M) σ (hmap (F := F) (M := M) (P := P) c)
      = hmap (F := F) (M := M) (P := P) (cRingEquiv (M := M) (P := P) σ c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero (f := cRingEquiv (M := M) (P := P) σ),
        map_zero (f := hmap (F := F) (M := M) (P := P)),
        map_zero (f := semiAlgEquiv (G := G) (M := M) σ)]
  | add x y hx hy =>
      rw [map_add (f := hmap (F := F) (M := M) (P := P)),
        map_add (f := cRingEquiv (M := M) (P := P) σ),
        map_add (f := semiAlgEquiv (G := G) (M := M) σ), hx, hy,
        map_add (f := hmap (F := F) (M := M) (P := P))]
  | single p a =>
      rw [hmap_single, semiAlgEquiv_single,
        show cRingEquiv (M := M) (P := P) σ (MonoidAlgebra.single p a)
          = MonoidAlgebra.single (mulEquivOfSMul G P σ p) (latticeAlgebraEquiv F G M σ a) from
        cRingEquiv_single (M := M) (P := P) σ p a,
        hmap_single]
      congr 1
      rw [show coeffRingEquiv (M := M) σ
            (algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M) a)
          = algebraMap (MonoidAlgebra F (Multiplicative M)) (latticeFunctionField F M)
              (latticeAlgebraEquiv F G M σ a) from by
        rw [coeffRingEquiv_apply]
        exact latticeAction_algebraMap (F := F) (G := G) (M := M) σ a]

set_option maxHeartbeats 2000000 in
/-- 半函数域作用在 `C`-像上的公式（`EMFixed.smul_algebraMap_semiAlg` ＋ `semiAlgEquiv_hmap`）。 -/
lemma semiAction_algebraMap_C (σ : G)
    (c : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :
    σ • algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)) c
      = algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (cRingEquiv (M := M) (P := P) σ c) := by
  have h1 : σ • algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (hmap (F := F) (M := M) (P := P) c)
      = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))
        (semiAlgEquiv (G := G) (M := M) σ (hmap (F := F) (M := M) (P := P) c)) :=
    smul_algebraMap_semiAlg (F := F) (M := M) (P := P) σ (hmap (F := F) (M := M) (P := P) c)
  refine h1.trans ?_
  rw [semiAlgEquiv_hmap]
  rfl

set_option maxHeartbeats 4000000 in
/-- **(ι) `δ.symm` 与作用交换**：`δ.symm (σ·y) = σ·(δ.symm y)`（两轴单项式公式 ＋ η-等变性）。 -/
lemma splitAlgEquiv_symm_comm (σ : G)
    (y : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :
    (splitAlgEquiv (M := M) (P := P)).symm (cRingEquiv (M := M) (P := P) σ y)
      = latticeAlgebraEquiv F G (M × P) σ
          ((splitAlgEquiv (M := M) (P := P)).symm y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
      rw [show cRingEquiv (M := M) (P := P) σ 0 = 0 from map_zero _,
        show (splitAlgEquiv (M := M) (P := P)).symm 0 = 0 from map_zero _,
        show latticeAlgebraEquiv F G (M × P) σ 0 = 0 from map_zero _]
  | add x y hx hy =>
      rw [show cRingEquiv (M := M) (P := P) σ (x + y)
            = cRingEquiv (M := M) (P := P) σ x + cRingEquiv (M := M) (P := P) σ y from
          map_add _ _ _,
        show (splitAlgEquiv (M := M) (P := P)).symm
            (cRingEquiv (M := M) (P := P) σ x + cRingEquiv (M := M) (P := P) σ y)
            = (splitAlgEquiv (M := M) (P := P)).symm (cRingEquiv (M := M) (P := P) σ x)
              + (splitAlgEquiv (M := M) (P := P)).symm (cRingEquiv (M := M) (P := P) σ y) from
          map_add _ _ _,
        show (splitAlgEquiv (M := M) (P := P)).symm (x + y)
            = (splitAlgEquiv (M := M) (P := P)).symm x
              + (splitAlgEquiv (M := M) (P := P)).symm y from map_add _ _ _,
        show latticeAlgebraEquiv F G (M × P) σ
            ((splitAlgEquiv (M := M) (P := P)).symm x
              + (splitAlgEquiv (M := M) (P := P)).symm y)
            = latticeAlgebraEquiv F G (M × P) σ ((splitAlgEquiv (M := M) (P := P)).symm x)
              + latticeAlgebraEquiv F G (M × P) σ ((splitAlgEquiv (M := M) (P := P)).symm y)
          from map_add _ _ _, hx, hy]
  | single p a =>
      rw [show MonoidAlgebra.single p a
          = MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M))
            * MonoidAlgebra.single (1 : Multiplicative P) a from by
        rw [MonoidAlgebra.single_mul_single, mul_one, one_mul]]
      rw [show cRingEquiv (M := M) (P := P) σ
            (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M))
              * MonoidAlgebra.single (1 : Multiplicative P) a)
          = cRingEquiv (M := M) (P := P) σ
              (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M)))
            * cRingEquiv (M := M) (P := P) σ
              (MonoidAlgebra.single (1 : Multiplicative P) a) from
        map_mul _ _ _]
      rw [show cRingEquiv (M := M) (P := P) σ
            (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M)))
          = MonoidAlgebra.single (mulEquivOfSMul G P σ p)
              (1 : MonoidAlgebra F (Multiplicative M)) from by
        rw [cRingEquiv_single, map_one]]
      rw [show cRingEquiv (M := M) (P := P) σ
            (MonoidAlgebra.single (1 : Multiplicative P) a)
          = MonoidAlgebra.single (1 : Multiplicative P)
              (latticeAlgebraEquiv F G M σ a) from by
        rw [cRingEquiv_single, map_one]]
      rw [show (splitAlgEquiv (M := M) (P := P)).symm
            (MonoidAlgebra.single (mulEquivOfSMul G P σ p)
                (1 : MonoidAlgebra F (Multiplicative M))
              * MonoidAlgebra.single (1 : Multiplicative P)
                (latticeAlgebraEquiv F G M σ a))
          = (splitAlgEquiv (M := M) (P := P)).symm
              (MonoidAlgebra.single (mulEquivOfSMul G P σ p)
                (1 : MonoidAlgebra F (Multiplicative M)))
            * (splitAlgEquiv (M := M) (P := P)).symm
              (MonoidAlgebra.single (1 : Multiplicative P)
                (latticeAlgebraEquiv F G M σ a)) from map_mul _ _ _,
        show (splitAlgEquiv (M := M) (P := P)).symm
            (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M))
              * MonoidAlgebra.single (1 : Multiplicative P) a)
          = (splitAlgEquiv (M := M) (P := P)).symm
              (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M)))
            * (splitAlgEquiv (M := M) (P := P)).symm
              (MonoidAlgebra.single (1 : Multiplicative P) a) from map_mul _ _ _]
      rw [splitAlgEquiv_symm_single_P, splitAlgEquiv_symm_single_one]
      rw [mPartAlgHom_equivariant]
      rw [show (splitAlgEquiv (M := M) (P := P)).symm
            (MonoidAlgebra.single p (1 : MonoidAlgebra F (Multiplicative M)))
          = MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), p.toAdd)) (1 : F) from
        splitAlgEquiv_symm_single_P (M := M) (P := P) p,
        show (splitAlgEquiv (M := M) (P := P)).symm
            (MonoidAlgebra.single (1 : Multiplicative P) a)
          = mPartAlgHom (M := M) (P := P) a from
        splitAlgEquiv_symm_single_one (M := M) (P := P) a]
      rw [show latticeAlgebraEquiv F G (M × P) σ
            (MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), p.toAdd)) (1 : F)
              * mPartAlgHom (M := M) (P := P) a)
          = latticeAlgebraEquiv F G (M × P) σ
              (MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), p.toAdd)) (1 : F))
            * latticeAlgebraEquiv F G (M × P) σ (mPartAlgHom (M := M) (P := P) a) from
          map_mul _ _ _]
      rw [show latticeAlgebraEquiv F G (M × P) σ
            (MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), p.toAdd)) (1 : F))
          = MonoidAlgebra.single
              (mulEquivOfSMul G (M × P) σ (Multiplicative.ofAdd ((0 : M), p.toAdd))) (1 : F) from
        MonoidAlgebra.mapDomainRingEquiv_single _ (1 : F) _]
      rw [mulEquivOfSMul_apply]
      change MonoidAlgebra.single (Multiplicative.ofAdd ((0 : M), σ • p.toAdd)) (1 : F)
          * latticeAlgebraEquiv F G (M × P) σ (mPartAlgHom (M := M) (P := P) a)
        = MonoidAlgebra.single (Multiplicative.ofAdd (σ • ((0 : M), p.toAdd))) (1 : F)
          * latticeAlgebraEquiv F G (M × P) σ (mPartAlgHom (M := M) (P := P) a)
      rw [show (σ • ((0 : M), p.toAdd)) = (σ • (0 : M), σ • p.toAdd) from rfl, smul_zero]

/-- 基域比较：`algebraMap F semi c = algebraMap C semi (algebraMap F C c)`。 -/
lemma algebraMap_F_semi_eq_C (c : F) :
    algebraMap F (semiFunctionField (F := F) (M := M) (P := P)) c
      = algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P))
          (algebraMap F (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P)) c) := by
  rw [IsScalarTower.algebraMap_apply F
    (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (semiFunctionField (F := F) (M := M) (P := P)) c]
  show algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P))
      (algebraMap F (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) c)
    = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P))
      (hmap (F := F) (M := M) (P := P)
        (algebraMap F (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
          (Multiplicative P)) c))
  congr 1
  rw [show algebraMap F (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) c
      = MonoidAlgebra.single (1 : Multiplicative P)
          (algebraMap F (latticeFunctionField F M) c) from by
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply]]
  rw [show algebraMap F (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
        (Multiplicative P)) c
      = MonoidAlgebra.single (1 : Multiplicative P)
          (algebraMap F (MonoidAlgebra F (Multiplicative M)) c) from by
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply]]
  rw [hmap_single]
  congr 1

instance instIsFractionRingCSemi :
    IsFractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) :=
  isFractionRing_C_semi (F := F) (M := M) (P := P)

/-- `J : semi ≃ₐ[F] FractionRing C`（`IsLocalization.algEquiv` 逆，基域降至 `F`）。 -/
noncomputable def J : semiFunctionField (F := F) (M := M) (P := P) ≃ₐ[F]
    FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :=
  AlgEquiv.ofRingEquiv
    (f := (IsLocalization.algEquiv (nonZeroDivisors
      (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
      (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
      (semiFunctionField (F := F) (M := M) (P := P))).symm.toRingEquiv)
    (fun c => by
      show (IsLocalization.algEquiv (nonZeroDivisors
          (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
          (semiFunctionField (F := F) (M := M) (P := P))).symm
          (algebraMap F (semiFunctionField (F := F) (M := M) (P := P)) c)
        = algebraMap F (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) c
      rw [algebraMap_F_semi_eq_C (F := F) (M := M) (P := P) c]
      rw [show (IsLocalization.algEquiv (nonZeroDivisors
            (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
            (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
            (semiFunctionField (F := F) (M := M) (P := P))).symm
            (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
              (semiFunctionField (F := F) (M := M) (P := P))
              (algebraMap F (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
                (Multiplicative P)) c))
          = algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
              (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
                (Multiplicative P)))
              (algebraMap F (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
                (Multiplicative P)) c) from
        AlgEquiv.commutes' _ _]
      rw [IsScalarTower.algebraMap_apply F
        (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
        (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
          (Multiplicative P))) c])

/-- `J` 在 `C`-像上的公式。 -/
lemma J_algebraMap (c : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :
    J (F := F) (M := M) (P := P)
        (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P)) c)
      = algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) c :=
  AlgEquiv.commutes' (IsLocalization.algEquiv (nonZeroDivisors
    (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
    (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)))
    (semiFunctionField (F := F) (M := M) (P := P))).symm c

/-- `FractionRing C` 上的转运作用（沿 `J` 从半函数域作用转运）。 -/
noncomputable def cFracAction (σ : G) :
    FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) ≃+*
      FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :=
  (J (F := F) (M := M) (P := P)).toRingEquiv.symm.trans
    (((MulSemiringAction.toRingEquiv G
        (semiFunctionField (F := F) (M := M) (P := P)) σ)).trans
      (J (F := F) (M := M) (P := P)).toRingEquiv)

set_option maxHeartbeats 2000000 in
/-- 转运作用在 `C`-像上的公式。 -/
lemma cFracAction_algebraMap (σ : G)
    (c : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :
    cFracAction (F := F) (M := M) (P := P) σ
        (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) c)
      = algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) (cRingEquiv (M := M) (P := P) σ c) := by
  show J (F := F) (M := M) (P := P)
      (σ • (J (F := F) (M := M) (P := P)).symm
        (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) c)) = _
  rw [show (J (F := F) (M := M) (P := P)).symm
        (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) c)
      = algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P)) c from
    (AlgEquiv.symm_apply_eq (J (F := F) (M := M) (P := P))).mpr
      (J_algebraMap (F := F) (M := M) (P := P) c).symm]
  rw [semiAction_algebraMap_C]
  exact J_algebraMap (F := F) (M := M) (P := P) (cRingEquiv (M := M) (P := P) σ c)

/-- `J` 与作用交换（转运定义为构造性）。 -/
lemma J_equivariant (σ : G) (x : semiFunctionField (F := F) (M := M) (P := P)) :
    J (F := F) (M := M) (P := P) (σ • x)
      = cFracAction (F := F) (M := M) (P := P) σ (J (F := F) (M := M) (P := P) x) := by
  show J (F := F) (M := M) (P := P) (σ • x)
    = J (F := F) (M := M) (P := P)
        (σ • (J (F := F) (M := M) (P := P)).symm (J (F := F) (M := M) (P := P) x))
  rw [AlgEquiv.symm_apply_apply]

/-\! ## 6. λ（δ-载运）、β₁、固定域层（χ）与桥 `b` -/

/-- λ：`FractionRing C ≃ₐ[F] latticeFunctionField F (M × P)`（δ-载运）。 -/
noncomputable def lambdaEquiv :
    FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) ≃ₐ[F]
      latticeFunctionField F (M × P) :=
  IsFractionRing.algEquivOfAlgEquiv ((splitAlgEquiv (M := M) (P := P)).symm)

/-- λ 在 `C`-像上的公式。 -/
lemma lambdaEquiv_algebraMap
    (c : MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P)) :
    lambdaEquiv (F := F) (M := M) (P := P)
        (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
          (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
            (Multiplicative P))) c)
      = algebraMap (MonoidAlgebra F (Multiplicative (M × P)))
          (latticeFunctionField F (M × P)) ((splitAlgEquiv (M := M) (P := P)).symm c) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (h := (splitAlgEquiv (M := M) (P := P)).symm) c

set_option maxHeartbeats 4000000 in
/-- λ 的等变性：`λ (σ▷y) = σ • λ y`（经 ι 落回格作用）。 -/
lemma lambdaEquiv_equivariant (σ : G)
    (y : FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))) :
    lambdaEquiv (F := F) (M := M) (P := P) (cFracAction (F := F) (M := M) (P := P) σ y)
      = σ • lambdaEquiv (F := F) (M := M) (P := P) y := by
  let F₁ : FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
      (Multiplicative P)) →+* latticeFunctionField F (M × P) :=
    (lambdaEquiv (F := F) (M := M) (P := P)).toRingHom.comp
      (cFracAction (F := F) (M := M) (P := P) σ).toRingHom
  let F₂ : FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
      (Multiplicative P)) →+* latticeFunctionField F (M × P) :=
    (MulSemiringAction.toRingEquiv G (latticeFunctionField F (M × P)) σ).toRingHom.comp
      (lambdaEquiv (F := F) (M := M) (P := P)).toRingHom
  have h : F₁ = F₂ := by
    apply IsFractionRing.ringHom_ext (A := MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
      (Multiplicative P))
    intro c
    show lambdaEquiv (F := F) (M := M) (P := P)
        (cFracAction (F := F) (M := M) (P := P) σ
          (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
            (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
              (Multiplicative P))) c))
      = σ • lambdaEquiv (F := F) (M := M) (P := P)
          (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
            (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
              (Multiplicative P))) c)
    rw [cFracAction_algebraMap]
    rw [lambdaEquiv_algebraMap (F := F) (M := M) (P := P)
      (cRingEquiv (M := M) (P := P) σ c)]
    rw [splitAlgEquiv_symm_comm]
    rw [show σ • lambdaEquiv (F := F) (M := M) (P := P)
          (algebraMap (MonoidAlgebra (MonoidAlgebra F (Multiplicative M)) (Multiplicative P))
            (FractionRing (MonoidAlgebra (MonoidAlgebra F (Multiplicative M))
              (Multiplicative P))) c)
        = σ • algebraMap (MonoidAlgebra F (Multiplicative (M × P)))
            (latticeFunctionField F (M × P)) ((splitAlgEquiv (M := M) (P := P)).symm c) from by
      rw [lambdaEquiv_algebraMap (F := F) (M := M) (P := P) c]]
    rw [latticeAction_algebraMap]
  exact RingHom.congr_fun h y

/-- β₁：绝对识别 `semi ≃ₐ[F] F(M × P)`（`J ≪ λ`）。 -/
noncomputable def beta1 :
    semiFunctionField (F := F) (M := M) (P := P) ≃ₐ[F] latticeFunctionField F (M × P) :=
  (J (F := F) (M := M) (P := P)).trans (lambdaEquiv (F := F) (M := M) (P := P))

/-- β₁ 的等变性。 -/
lemma beta1_equivariant (σ : G) (x : semiFunctionField (F := F) (M := M) (P := P)) :
    beta1 (F := F) (M := M) (P := P) (σ • x)
      = σ • beta1 (F := F) (M := M) (P := P) x := by
  rw [beta1, AlgEquiv.trans_apply, J_equivariant (F := F) (M := M) (P := P) σ x]
  rw [lambdaEquiv_equivariant (F := F) (M := M) (P := P) σ
    (J (F := F) (M := M) (P := P) x)]
  rw [AlgEquiv.trans_apply]

set_option maxHeartbeats 8000000 in
/-- χ：固定域层的绝对识别 `semi^G ≃ₐ[F] F(M × P)^G`（Alg 形；`codRestrict` ＋ `ofBijective`）。 -/
noncomputable def chiAbs :
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))
      ≃ₐ[F] ↥(latticeInvariantsAlg F G (M × P)) :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective
      (((beta1 (F := F) (M := M) (P := P)).toRingHom.comp
          (FixedPoints.subfield G
            (semiFunctionField (F := F) (M := M) (P := P))).subtype).codRestrict
        (latticeInvariantsAlg F G (M × P))
        (fun x => (mem_latticeInvariantsAlg_iff (F := F) (G := G) (M := M × P)
            ((beta1 (F := F) (M := M) (P := P)) x)).mpr (fun g => by
          rw [← beta1_equivariant (F := F) (M := M) (P := P) g x]
          congr 1
          exact (mem_fixed_iff (F := F) (M := M) (P := P)
            (x : semiFunctionField (F := F) (M := M) (P := P))).mp x.2 g)))
      ⟨fun x y hxy => Subtype.ext
          ((beta1 (F := F) (M := M) (P := P)).injective (Subtype.ext_iff.mp hxy)),
        fun y => by
          obtain ⟨x, hx⟩ := (beta1 (F := F) (M := M) (P := P)).surjective
            (y : latticeFunctionField F (M × P))
          refine ⟨⟨x, (mem_fixed_iff (F := F) (M := M) (P := P) x).mpr (fun g => ?_)⟩,
            Subtype.ext hx⟩
          apply (beta1 (F := F) (M := M) (P := P)).injective
          rw [beta1_equivariant, hx]
          exact (mem_latticeInvariantsAlg_iff (F := F) (G := G) (M := M × P)
            (y : latticeFunctionField F (M × P))).mp y.2 g⟩)
    (fun c => Subtype.ext (by
      show (beta1 (F := F) (M := M) (P := P))
          ((algebraMap F (FixedPoints.subfield G
              (semiFunctionField (F := F) (M := M) (P := P))) c :
            ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)))) :
            semiFunctionField (F := F) (M := M) (P := P))
        = algebraMap F (latticeFunctionField F (M × P)) c
      exact (beta1 (F := F) (M := M) (P := P)).commutes' c))

variable {F : Type*} [Field F]
variable {G : Type*} [CommGroup G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]

/-- **桥 `b`**：`F(ℤ[G])^G ≃ₐ[F] semi^G`（S3 载运 ＋ χ；正则格落点）。 -/
noncomputable def bridgeB (e : M × P ≃+ (G → ℤ))
    (he : ∀ (g : G) (x : M × P), e (g • x) = g • e x) :
    ↥(latticeInvariantsAlg F G (G → ℤ))
      ≃ₐ[F] ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) :=
  (latticeInvariantsAlgTransport (F := F) (G := G) (M := M × P) (M' := G → ℤ) e he).symm.trans
    (chiAbs (F := F) (M := M) (P := P)).symm

/-- **主定理（A13 子情形 `Q = 单块正则`；桥 `b` 已消解）**：
S3 数据 `(B, ρ, hρ)` ＋ 忠实性 ＋ 格等价 `e : M × P ≃+ (G → ℤ)`（等变）
⟹ `F(M)^G` 稳定有理。与 `EMRouteS.isStablyRational_of_regularSubcase` 同结论、
然而**无桥假设**（`b` 由 `bridgeB` 构造）。 -/
theorem isStablyRational_of_regularSubcase_bridged
    [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    (hfaith : FaithfulSMul G M)
    {ι : Type*} [Fintype ι] (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    (e : M × P ≃+ (G → ℤ)) (he : ∀ (g : G) (x : M × P), e (g • x) = g • e x) :
    IsStablyRational F ↥(latticeInvariantsAlg F G M) :=
  RouteS.isStablyRational_of_regularSubcase (F := F) (G := G) (M := M) (P := P)
    hfaith B ρ hρ (bridgeB (F := F) (M := M) (P := P) e he)

/-! ## 7. 公理闸门 -/

#print axioms multiProdEquiv
#print axioms splitAlgEquiv
#print axioms splitAlgEquiv_single
#print axioms mPartAlgHom
#print axioms mPartAlgHom_single
#print axioms mPartAlgHom_equivariant
#print axioms splitAlgEquiv_mPart
#print axioms hmap
#print axioms clearing
#print axioms isFractionRing_C_semi
#print axioms cRingEquiv
#print axioms semiAlgEquiv_hmap
#print axioms semiAction_algebraMap_C
#print axioms splitAlgEquiv_symm_comm
#print axioms J
#print axioms cFracAction
#print axioms J_equivariant
#print axioms lambdaEquiv
#print axioms lambdaEquiv_equivariant
#print axioms beta1
#print axioms beta1_equivariant
#print axioms chiAbs
#print axioms bridgeB
#print axioms isStablyRational_of_regularSubcase_bridged

end

end Bridge

end EM

end ABGV52
