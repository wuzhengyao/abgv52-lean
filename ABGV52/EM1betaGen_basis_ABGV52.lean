/-
  ABGV-5.2 —— 本体形式化 A · **M6-A（1β-general：特征分解层）**

  设计件：`wiki/proj-ABGV52-M6-1beta-general-design.md` §4.1／§4.2 步 1–2／§6。

  目标：对任意有限交换群 `G` 与任意 `G`-格 `Q`（带置换基 `B : Basis ι ℤ Q`
  与置换律 `κ`／`hκ`），把单项式张成的稳定子空间 `W = span_F {x^{e_i}}` 分解为
  **逐轨道**的特征基 `Y_{i,χ}`（`χ` 在稳定子 `S_i` 上取 1）：

    * §1：`Wb` 的定义、`G`-稳定性、`dim_F Wb = |ι|`、单项式族 `F`-无关；
    * §2：`Yalg`（`F[Q]` 层）／`Y`（`F(Q)` 层）、非零性、特征向量性、成对无关
      （特征正交性；**逐轨道**、**禁块复合**）、计数 `∑ |S_i| = |X|`（对偶 ＋
      轨道-稳定子，与无关性**机制不同**，L-D）⟹ `{Y}` 是 `Wb` 的 `F`-基。

  **架构约束（用户裁定）**：禁块复合 `F(Q)^G = ∏_i F(Q_i)^G`（1γ 已由
  `D14_ABGV52.lean:391` 证伪）；本件一律逐轨道。

  前提（§4.1）：`F` 域、`G` 有限交换群、`Q` 为 `ℤ[G]`-格（`UniqueProds` 供
  `MonoidAlgebra` 无零因子）、`ζ`-假定 `[HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]`
  （§2 用：字符群有限 ＋ 基数非零（引理 P））。

  范围注（A13）：本件给**基**与**计数**；`IsRational` 结论（M6-B）经
  `latticeInvariantsAlg` 的生成性在其上另建。

  **无 sorry、无自造公理**。
-/
import ABGV52.EMRational_ABGV52
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Data.Finset.Sigma

namespace ABGV52

namespace EM

open scoped Classical

set_option maxHeartbeats 400000

/-! ## 0. 轨道／稳定子记号与引理 P（基数非零） -/

/-- `κ` 诱导的轨道关系（经 `MulAction.compHom`）。 -/
noncomputable def orbitRelκ {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) : Setoid ι :=
  letI : MulAction G ι := MulAction.compHom ι κ
  MulAction.orbitRel G ι

/-- `κ` 下 `i` 的轨道。 -/
noncomputable def orbitκ {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i : ι) : Set ι :=
  letI : MulAction G ι := MulAction.compHom ι κ
  MulAction.orbit G i

/-- `κ` 下 `i` 的稳定子。 -/
noncomputable def stabκ {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i : ι) : Subgroup G :=
  letI : MulAction G ι := MulAction.compHom ι κ
  MulAction.stabilizer G i

/-- 稳定子取 1 的字符集 `S_i = {χ : MulChar G F // χ|_{Stab(x_i)} = 1}`
（此处先给载体集合，子类型 `↥Sset` 即设计中的 `S_i`）。 -/
def Sset {G : Type*} [CommGroup G] {F : Type*} [Field F] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i : ι) : Set (MulChar G F) :=
  {χ | ∀ σ : G, κ σ i = i → χ σ = 1}

/-- 稳定子成员的 `κ`-刻画。 -/
theorem mem_stabκ_iff {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i : ι) (σ : G) : σ ∈ stabκ κ i ↔ κ σ i = i := by
  letI : MulAction G ι := MulAction.compHom ι κ
  change σ ∈ MulAction.stabilizer G i ↔ κ σ i = i
  rw [MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def]
  exact Iff.rfl

/-- 轨道成员的 `κ`-刻画。 -/
theorem mem_orbitκ_iff {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i j : ι) : j ∈ orbitκ κ i ↔ ∃ σ : G, κ σ i = j := by
  letI : MulAction G ι := MulAction.compHom ι κ
  change j ∈ MulAction.orbit G i ↔ ∃ σ : G, κ σ i = j
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (MulAction.compHom_smul_def κ σ i).symm.trans hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (MulAction.compHom_smul_def κ σ i).trans hσ⟩

/-- 轨道关系的 `κ`-刻画（`rw [MulAction.orbitRel_apply]` 因 `letI` 包裹失配，
经此桥使用；轨道划分计数 `∑_c |orbit c| = |ι|` 依赖它）。 -/
theorem orbitRelκ_iff {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i j : ι) : (orbitRelκ κ).r i j ↔ ∃ σ : G, κ σ j = i := by
  letI : MulAction G ι := MulAction.compHom ι κ
  change (MulAction.orbitRel G ι) i j ↔ ∃ σ : G, κ σ j = i
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (MulAction.compHom_smul_def κ σ j).symm.trans hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (MulAction.compHom_smul_def κ σ j).trans hσ⟩

/-- **`S_i` = 对偶子群**（核心桥）：`χ` 在稳定子 `Stab(x_i)` 上取 1，当且仅当
`χ` 落在 `Stab(x_i)ˣ` 的对偶子群内（字符对偶，经 `Units.coeHom` 搬运）。 -/
theorem mem_Sset_iff {G : Type*} [CommGroup G] [Fintype G] {F : Type*} [Field F]
    {ι : Type*} [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    (κ : G →* Equiv.Perm ι) (i : ι) (χ : MulChar G F) :
    χ ∈ Sset κ i ↔
      χ ∈ (MulChar.subgroupOrderIsoSubgroupMulChar G F
        ((stabκ κ i).comap (Units.coeHom G))).ofDual := by
  constructor
  · intro hχ
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    intro m hm
    exact hχ (m : G) ((mem_stabκ_iff κ i (m : G)).mp ((Subgroup.mem_comap).mp hm))
  · intro hχ σ hσ
    rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff] at hχ
    have hm : Units.mkOfMulEqOne σ σ⁻¹ (mul_inv_cancel σ) ∈
        (stabκ κ i).comap (Units.coeHom G) := by
      rw [Subgroup.mem_comap]
      show (↑(Units.mkOfMulEqOne σ σ⁻¹ (mul_inv_cancel σ)) : G) ∈ stabκ κ i
      rw [Units.val_mkOfMulEqOne]
      exact (mem_stabκ_iff κ i σ).mpr hσ
    have := hχ _ hm
    rwa [Units.val_mkOfMulEqOne] at this

/-- `Gˣ`-轨道与 `G`-轨道一致（单位群经 `Units.coeHom`）。 -/
theorem orbitκ_units_eq {G : Type*} [CommGroup G] [Fintype G] {ι : Type*}
    (κ : G →* Equiv.Perm ι) (i : ι) :
    orbitκ (κ.comp (Units.coeHom G)) i = orbitκ κ i := by
  letI : MulAction G ι := MulAction.compHom ι κ
  letI : MulAction Gˣ ι := MulAction.compHom ι (κ.comp (Units.coeHom G))
  have hU : ∀ (u : Gˣ) (x : ι), u • x = κ (↑u) x := fun u x =>
    (MulAction.compHom_smul_def (κ.comp (Units.coeHom G)) u x).trans rfl
  have hG : ∀ (σ : G) (x : ι), σ • x = κ σ x := fun σ x =>
    (MulAction.compHom_smul_def κ σ x).trans rfl
  ext j
  constructor
  · intro hj
    obtain ⟨u, hu⟩ := (MulAction.mem_orbit_iff).mp hj
    exact (MulAction.mem_orbit_iff).mpr
      ⟨(u : G), (hG ↑u i).trans ((hU u i).symm.trans hu)⟩
  · intro hj
    obtain ⟨σ, hσ⟩ := (MulAction.mem_orbit_iff).mp hj
    exact (MulAction.mem_orbit_iff).mpr
      ⟨Units.mkOfMulEqOne σ σ⁻¹ (mul_inv_cancel σ),
        (hU _ i).trans ((hG σ i).symm.trans hσ)⟩

/-- **(P)** 单位群基数在 `F` 中非零（由「足够单位根」）。走 `ringChar`：
素特征 `p = ringChar F` 由 `CharP.char_prime_of_ne_zero`（无需 `Finite F`），
再经 Cauchy 定理取 `p`-阶元嵌入 `Monoid.exponent Gˣ`。 -/
theorem natCast_card_units_ne_zero {F : Type*} [Field F] {G : Type*} [CommGroup G]
    [Fintype G] [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)] :
    ((Fintype.card Gˣ : ℕ) : F) ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (Monoid.exponent Gˣ)
  haveI : NeZero (Monoid.exponent Gˣ) := Monoid.neZero_exponent_of_finite
  have hcast : NeZero ((Monoid.exponent Gˣ : ℕ) : F) := IsPrimitiveRoot.neZero' hζ
  have hexp : ((Monoid.exponent Gˣ : ℕ) : F) ≠ 0 := hcast.out
  intro h0
  have hrdvd : ringChar F ∣ Fintype.card Gˣ := ringChar.dvd h0
  have hr0 : ringChar F ≠ 0 := by
    intro hr
    have h1 : Fintype.card Gˣ = 0 := by
      have h := hrdvd
      rw [hr] at h
      obtain ⟨k, hk⟩ := h
      rw [zero_mul] at hk
      exact hk
    exact (Fintype.card_pos_iff.mpr ⟨1⟩).ne' h1
  have hrp : Nat.Prime (ringChar F) := CharP.char_prime_of_ne_zero F hr0
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hrp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (ringChar F) hrdvd
  have hdvd2 : ringChar F ∣ Monoid.exponent Gˣ := hx ▸ Monoid.order_dvd_exponent x
  obtain ⟨m, hm⟩ := hdvd2
  have hrcast : ((ringChar F : ℕ) : F) = 0 := (ringChar.spec F (ringChar F)).mpr (dvd_refl _)
  have hzero : ((Monoid.exponent Gˣ : ℕ) : F) = 0 := by
    rw [hm, Nat.cast_mul, hrcast, zero_mul]
  exact hexp hzero

/-- **(P′)** 群基数在 `F` 中非零。 -/
theorem natCast_card_ne_zero {F : Type*} [Field F] {G : Type*} [CommGroup G]
    [Fintype G] [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)] :
    ((Fintype.card G : ℕ) : F) ≠ 0 := by
  have hcard : Fintype.card Gˣ = Fintype.card G :=
    Fintype.card_congr
      { toFun := fun u => (u : G)
        invFun := fun a => Units.mkOfMulEqOne a a⁻¹ (mul_inv_cancel a)
        left_inv := fun u => Units.ext rfl
        right_inv := fun a => rfl }
  rw [← hcard]
  exact natCast_card_units_ne_zero (F := F) (G := G)

/-- **(P″)** 除数形式：`n ∣ |G|` ⟹ `(n : F) ≠ 0`。 -/
theorem natCast_ne_zero_of_dvd {F : Type*} [Field F] {G : Type*} [CommGroup G]
    [Fintype G] [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    {n : ℕ} (hn : n ∣ Fintype.card G) : (n : F) ≠ 0 := by
  intro hn0
  have h0 : ((Fintype.card G : ℕ) : F) ≠ 0 := natCast_card_ne_zero (F := F) (G := G)
  obtain ⟨k, hk⟩ := hn
  exact h0 (by rw [hk, Nat.cast_mul, hn0, zero_mul])

/-! ## 1. 基部：单项式、`Wb` 层、`F(Q)` 搬运 -/

section Basis

variable (F : Type*) [Field F]
variable (G : Type*) [CommGroup G] [Fintype G]
variable (Q : Type*) [AddCommGroup Q] [Module ℤ Q] [DistribMulAction G Q]
  [SMulCommClass G ℤ Q] [UniqueProds (Multiplicative Q)]
variable (ι : Type*) [Fintype ι]
variable (B : Module.Basis ι ℤ Q) (κ : G →* Equiv.Perm ι)

/-- `F[Q] →ₗ[F] F(Q)`：`algebraMap` 作为 `F`-线性映射（`ker = ⊥` 供无关性搬运）。 -/
noncomputable def algToField : latticeAlgebra F Q →ₗ[F] latticeFunctionField F Q :=
  (IsScalarTower.toAlgHom F (latticeAlgebra F Q) (latticeFunctionField F Q)).toLinearMap

/-- 基单项式在 `F[Q]` 中的提升 `x^{e_i}`。 -/
noncomputable def monoAlg (i : ι) : latticeAlgebra F Q :=
  MonoidAlgebra.single (permMono (P := Q) B i) (1 : F)

/-- 基单项式在 `F(Q)` 中的像 `x^{e_i}`。 -/
noncomputable def mono (i : ι) : latticeFunctionField F Q :=
  algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) (monoAlg F Q ι B i)

/-- **`Wb`**：单项式张成的 `F`-子空间（设计中的 `W = span_F {x^{e_x}}`）。 -/
noncomputable def Wb : Submodule F (latticeFunctionField F Q) :=
  Submodule.span F (Set.range (mono F Q ι B))

theorem mono_mem (i : ι) : mono F Q ι B i ∈ Wb F Q ι B :=
  Submodule.subset_span ⟨i, rfl⟩

/-- `g` 作用在提升单项式上 = 指标按 `κ` 平移（系数不动）；`hκ` 为置换律
（`mulEquivOfSMul G Q σ` 把基元 `e_i` 送到 `e_{κ σ i}`，即 `(B, κ)` 相容）。 -/
theorem smul_monoAlg
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (σ : G) (i : ι) :
    σ • monoAlg F Q ι B i = monoAlg F Q ι B (κ σ i) := by
  show MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G Q σ)
      (MonoidAlgebra.single (permMono (P := Q) B i) (1 : F)) = _
  rw [MonoidAlgebra.mapDomainRingEquiv_single]
  rw [hκ]
  rfl

/-- `F[Q]`-层作用与 `algToField` 交换（分式域搬运；D1 作用经
`IsFractionRing.ringEquivOfRingEquiv` 延拓）。 -/
theorem smul_algebraMap_eq (σ : G) (x : latticeAlgebra F Q) :
    σ • (algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) x)
      = algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) (σ • x) := by
  change (IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingEquiv G (latticeAlgebra F Q) σ))
    (algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) x) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- `g` 作用在 `F(Q)` 单项式上：`σ • x^{e_i} = x^{e_{κ σ i}}`。 -/
theorem smul_mono
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (σ : G) (i : ι) : σ • mono F Q ι B i = mono F Q ι B (κ σ i) := by
  show σ • (algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) (monoAlg F Q ι B i))
      = algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) (monoAlg F Q ι B (κ σ i))
  rw [smul_algebraMap_eq, smul_monoAlg (F := F) (hκ := hκ)]

/-- **`Wb` 的 `G`-稳定性**。 -/
theorem Wb_smul_mem
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (σ : G) {w : latticeFunctionField F Q} (hw : w ∈ Wb F Q ι B) :
    σ • w ∈ Wb F Q ι B := by
  refine Submodule.span_induction (p := fun x _ => σ • x ∈ Wb F Q ι B) ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [smul_mono (F := F) (hκ := hκ)]
    exact mono_mem F Q ι B (κ σ i)
  · rw [smul_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ ihx ihy
    rw [smul_add]
    exact Submodule.add_mem _ ihx ihy
  · intro c x _ ih
    rw [smul_comm]
    exact Submodule.smul_mem _ c ih

/-- `permMono` 单射（基分量单射）。
**命名注**（2026-10-09 实编译捕获）：本件原名 `permMono_injective`，与
`EMIndep_ABGV52.lean:184` 的同名声明撞名——两件同时导入（本件 ＋ `EMRouteS`）
会报「environment already contains」；故本件改用 `permMono_injective_basis`。 -/
theorem permMono_injective_basis : Function.Injective (permMono (P := Q) B) := fun i j h =>
  B.injective (Multiplicative.ofAdd.injective h)

/-- 提升单项式族在 `F[Q]` 中 `F`-无关（标准基沿单射指标取子族）。 -/
theorem monoAlg_linearIndependent : LinearIndependent F (monoAlg F Q ι B) := by
  have h := (MonoidAlgebra.basis (Multiplicative Q) F).linearIndependent.comp
    (permMono (P := Q) B) (permMono_injective_basis (B := B))
  have hcomp : (⇑(MonoidAlgebra.basis (Multiplicative Q) F)) ∘ (permMono (P := Q) B)
      = monoAlg F Q ι B := by
    funext i
    simp only [Function.comp_apply, monoAlg, MonoidAlgebra.basis_apply]
  rw [hcomp] at h
  exact h

/-- 单项式族在 `F(Q)` 中 `F`-无关（经 `algToField` 搬运）。 -/
theorem mono_linearIndependent : LinearIndependent F (mono F Q ι B) := by
  have hker : (algToField F Q).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (IsFractionRing.injective (latticeAlgebra F Q) (latticeFunctionField F Q))
  have h := (monoAlg_linearIndependent F Q ι B).map' (algToField F Q) hker
  have hcomp : (algToField F Q) ∘ (monoAlg F Q ι B) = mono F Q ι B := by
    funext i
    rfl
  rwa [hcomp] at h

/-- `dim_F Wb = |ι|`。 -/
theorem finrank_Wb : Module.finrank F ↥(Wb F Q ι B) = Fintype.card ι :=
  finrank_span_eq_card (mono_linearIndependent F Q ι B)

/-- `Wb` 有限维（单项式族有限）。 -/
theorem finiteDimensional_Wb : FiniteDimensional F ↥(Wb F Q ι B) :=
  FiniteDimensional.span_of_finite F (Set.finite_range (mono F Q ι B))

/-! ## 1.5 `Wb` 的单项式子类型基与 `hκ`-自由的 `twist` -/

section BasisSub

/-- 单项式在 `Wb` 中的提升。 -/
noncomputable def monoSub (i : ι) : ↥(Wb F Q ι B) :=
  ⟨mono F Q ι B i, mono_mem F Q ι B i⟩

/-- `monoSub` 在 `Wb` 中 `F`-无关（系数经子类型搬回 `F(Q)` 后用 §1 结论）。 -/
theorem monoSub_linearIndependent : LinearIndependent F (monoSub F Q ι B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, g j • mono F Q ι B j = 0 := by
    have h := congrArg (fun w : ↥(Wb F Q ι B) => (w : latticeFunctionField F Q)) hg
    simpa [monoSub, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using h
  exact (Fintype.linearIndependent_iff.mp (mono_linearIndependent F Q ι B)) g hg' i

/-- `Wb` 的单项式基（由无关性 ＋ 计数 ＝ 秩构造）。 -/
noncomputable def monoBasis : Module.Basis ι F ↥(Wb F Q ι B) := by
  haveI : FiniteDimensional F ↥(Wb F Q ι B) := finiteDimensional_Wb F Q ι B
  exact basisOfLinearIndependentOfCardEqFinrank' (monoSub F Q ι B)
    (monoSub_linearIndependent F Q ι B) (finrank_Wb F Q ι B).symm

/-- `monoBasis` 在指标上的取值（回归 `monoSub`）。 -/
@[simp] theorem monoBasis_apply (i : ι) : monoBasis F Q ι B i = monoSub F Q ι B i := by
  haveI : FiniteDimensional F ↥(Wb F Q ι B) := finiteDimensional_Wb F Q ι B
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := F) (monoSub F Q ι B)
    (monoSub_linearIndependent F Q ι B) (finrank_Wb F Q ι B).symm) i

/-- `hκ`-自由的「指标平移」算子（在 `monoBasis` 上按 `κ` 置换单项式）。 -/
noncomputable def twist (σ : G) : ↥(Wb F Q ι B) →ₗ[F] ↥(Wb F Q ι B) :=
  (monoBasis F Q ι B).constr F (fun i => monoSub F Q ι B (κ σ i))

/-- `twist` 在单项式子上的取值。 -/
theorem twist_monoSub (σ : G) (i : ι) :
    twist F G Q ι B κ σ (monoSub F Q ι B i) = monoSub F Q ι B (κ σ i) := by
  have h := Module.Basis.constr_basis (monoBasis F Q ι B) F
    (fun j => monoSub F Q ι B (κ σ j)) i
  rw [monoBasis_apply F Q ι B i] at h
  exact h

end BasisSub

/-! ## 2. 特征基 `Y_{i,χ}`（逐轨道） -/

section Chars

variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]

/-- 指标集：轨道代表（商 `ι/orbitRelκ`） × 代表处的稳定子字符 `S_{out c}`。 -/
abbrev Idx : Type _ := Σ c : Quotient (orbitRelκ κ), ↥(Sset (F := F) κ (Quotient.out c))

/-- `Y_{i,χ}` 在 `Wb` 层（单项式基下的 `F`-组合）。 -/
noncomputable def YSub (p : Idx F G ι κ) : ↥(Wb F Q ι B) :=
  ∑ σ : G, ((p.2 : MulChar G F) σ)⁻¹ • monoSub F Q ι B (κ σ (Quotient.out p.1))

/-- `Y_{i,χ}` 在 `F(Q)` 层。 -/
noncomputable def Y (p : Idx F G ι κ) : latticeFunctionField F Q :=
  ∑ σ : G, ((p.2 : MulChar G F) σ)⁻¹ • mono F Q ι B (κ σ (Quotient.out p.1))

/-- `Y` 是 `YSub` 的坐标（逐项 `Submodule.coe_smul`）。 -/
theorem Y_coe (p : Idx F G ι κ) :
    Y F G Q ι B κ p = ((YSub F G Q ι B κ p : ↥(Wb F Q ι B)) : latticeFunctionField F Q) := by
  rw [Y, YSub]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Submodule.coe_smul]
  rfl

/-- 抽取泛函 `Y_p ↦ 系数(x^{e_{κσ i_p}})`：在 `monoBasis` 上沿 `κ`-原像取字符值。 -/
noncomputable def dualY (p : Idx F G ι κ) : ↥(Wb F Q ι B) →ₗ[F] F :=
  (monoBasis F Q ι B).constr F (fun j =>
    if h : ∃ σ : G, κ σ (Quotient.out p.1) = j then
      (p.2 : MulChar G F) (Classical.choose h) else 0)

/-- 抽取泛函在单项式上的取值（`constr_basis`）。 -/
theorem dualY_coord (p : Idx F G ι κ) (i : ι) :
    dualY F G Q ι B κ p (monoSub F Q ι B i) =
      if h : ∃ σ : G, κ σ (Quotient.out p.1) = i then
        (p.2 : MulChar G F) (Classical.choose h) else 0 := by
  have h := Module.Basis.constr_basis (monoBasis F Q ι B) F
    (fun j => if h : ∃ σ : G, κ σ (Quotient.out p.1) = j then
      (p.2 : MulChar G F) (Classical.choose h) else 0) i
  rw [monoBasis_apply F Q ι B i] at h
  exact h

/-- 同一轨道中的任意两个实现给出相同的字符值（稳定条件 `χ ∈ S_i` 的用点）。 -/
theorem char_eq_of_witness (p : Idx F G ι κ) {σ τ : G}
    (h : κ σ (Quotient.out p.1) = κ τ (Quotient.out p.1)) :
    (p.2 : MulChar G F) σ = (p.2 : MulChar G F) τ := by
  have hS : ∀ ρ : G, κ ρ (Quotient.out p.1) = Quotient.out p.1 →
      (p.2 : MulChar G F) ρ = 1 := p.2.2
  have hmem : (p.2 : MulChar G F) (τ⁻¹ * σ) = 1 := by
    apply hS
    rw [map_mul, Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, ← map_mul,
      inv_mul_cancel, map_one]
    rfl
  calc (p.2 : MulChar G F) σ
      = (p.2 : MulChar G F) (τ * (τ⁻¹ * σ)) :=
        (congrArg (fun ρ => (p.2 : MulChar G F) ρ) (mul_inv_cancel_left τ σ)).symm
    _ = (p.2 : MulChar G F) τ * (p.2 : MulChar G F) (τ⁻¹ * σ) := by rw [map_mul]
    _ = (p.2 : MulChar G F) τ := by rw [hmem, mul_one]

/-! ### 2.1 特征正交与轨道计数

计数机制 = **轨道-稳定子**（`card_orbitκ`）＋ **对偶子群基数**（`card_Sset`）——
与 §2.3 的无关性机制（**特征正交**，经 `dualY` 配对的 Gram 对角化）**相互独立**（L-D）。 -/

/-- `MulChar G F` 的 `Fintype`（对偶群同构；与 `D4_ABGV52` 的 `instFintypeMulChar` 同式）。
    §2 的求和 `∑ χ : ↥(Sset …)` 与 `card_Idx` 需要它。 -/
noncomputable instance instFintypeMulCharBasis : Fintype (MulChar G F) :=
  Fintype.ofEquiv Gˣ (Classical.choice (MulChar.mulEquiv_units G F)).symm

/-- 字符正交关系：`∑_σ χ₀(σ)⁻¹ χ₁(σ) = |G|`（当 `χ₁ = χ₀`），否则 `0`。 -/
theorem sum_char_orthog (χ₀ χ₁ : MulChar G F) :
    (∑ σ : G, (χ₀ σ)⁻¹ * χ₁ σ)
      = if χ₁ = χ₀ then ((Fintype.card G : ℕ) : F) else 0 := by
  have hpt : ∀ σ : G, (χ₀ σ)⁻¹ * χ₁ σ = ((χ₀⁻¹) * χ₁) σ := fun σ => by
    rw [MulChar.mul_apply, ← MulChar.inv_apply_eq_inv' χ₀ σ]
  rw [Finset.sum_congr rfl fun σ _ => hpt σ]
  by_cases h : χ₀⁻¹ * χ₁ = 1
  · rw [h, MulChar.sum_one_eq_card_units]
    rw [if_pos (inv_mul_eq_one.mp h).symm]
    have hcard : Fintype.card Gˣ = Fintype.card G :=
      Fintype.card_congr
        { toFun := fun u => (u : G)
          invFun := fun a => Units.mkOfMulEqOne a a⁻¹ (mul_inv_cancel a)
          left_inv := fun u => Units.ext rfl
          right_inv := fun a => rfl }
    rw [hcard]
  · rw [if_neg (fun hc : χ₁ = χ₀ => h (inv_mul_eq_one.mpr hc.symm)),
      MulChar.sum_eq_zero_of_ne_one h]

/-- 轨道划分计数（`Quotient.out` 取代表）：`∑_c |orbit(out c)| = |ι|`。 -/
theorem orbit_partition_card :
    Fintype.card ι
      = ∑ c : Quotient (orbitRelκ κ), Fintype.card ↥(orbitκ κ (Quotient.out c)) := by
  calc Fintype.card ι
      = Fintype.card (Σ c : Quotient (orbitRelκ κ),
          {i // (⟦i⟧ : Quotient (orbitRelκ κ)) = c}) :=
        (Fintype.card_congr
          (Equiv.sigmaFiberEquiv
            (f := fun i : ι => (⟦i⟧ : Quotient (orbitRelκ κ))))).symm
    _ = ∑ c, Fintype.card {i // (⟦i⟧ : Quotient (orbitRelκ κ)) = c} :=
        Fintype.card_sigma
    _ = ∑ c, Fintype.card ↥(orbitκ κ (Quotient.out c)) := by
        refine Finset.sum_congr rfl fun c _ =>
          Fintype.card_congr (Equiv.subtypeEquivRight ?_)
        intro i
        constructor
        · intro h
          rw [mem_orbitκ_iff]
          have h' : (⟦i⟧ : Quotient (orbitRelκ κ)) = ⟦Quotient.out c⟧ :=
            h.trans (Quotient.out_eq c).symm
          exact (orbitRelκ_iff κ i (Quotient.out c)).mp (Quotient.exact h')
        · intro h
          have h2 : (orbitRelκ κ).r i (Quotient.out c) :=
            (orbitRelκ_iff κ i (Quotient.out c)).mpr
              ((mem_orbitκ_iff κ (Quotient.out c) i).mp h)
          exact (Quotient.sound h2).trans (Quotient.out_eq c)

/-- 稳定子字符数 = 稳定子指数（字符对偶：把 `(Stab κ i)ˣ` 的对偶子群基数换回指数）。 -/
theorem card_Sset (i : ι) : Fintype.card ↥(Sset (F := F) κ i) = (stabκ κ i).index := by
  have hcard := Fintype.card_congr
    (Equiv.subtypeEquivRight (fun χ : MulChar G F => mem_Sset_iff κ i χ))
  calc Fintype.card ↥(Sset (F := F) κ i)
      = Fintype.card ↥((MulChar.subgroupOrderIsoSubgroupMulChar G F
          ((stabκ κ i).comap (Units.coeHom G))).ofDual) := hcard
    _ = Nat.card ↥((MulChar.subgroupOrderIsoSubgroupMulChar G F
          ((stabκ κ i).comap (Units.coeHom G))).ofDual) :=
        Nat.card_eq_fintype_card.symm
    _ = Nat.card (Gˣ ⧸ ((stabκ κ i).comap (Units.coeHom G))) :=
        MulChar.card_subgroupOrderIsoSubgroupMulChar
    _ = ((stabκ κ i).comap (Units.coeHom G)).index :=
        (Subgroup.index_eq_card _).symm
    _ = (stabκ κ i).index := by
        refine Subgroup.index_comap_of_surjective (H := stabκ κ i)
          (f := Units.coeHom G) ?_
        intro x
        exact ⟨Units.mkOfMulEqOne x x⁻¹ (mul_inv_cancel x), rfl⟩

/-- 轨道—稳定子（在 `MulAction.compHom` 层）：`|orbit(x_i)| = [G : Stab(x_i)]`。 -/
theorem card_orbitκ (i : ι) : Fintype.card ↥(orbitκ κ i) = (stabκ κ i).index := by
  letI : MulAction G ι := MulAction.compHom ι κ
  change Fintype.card ↥(MulAction.orbit G i) = (MulAction.stabilizer G i).index
  rw [Fintype.card_congr (MulAction.orbitEquivQuotientStabilizer G i)]
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]

/-- 指标集基数 = `|ι|`（逐轨道双计数：`∑ |S_out c| = ∑ |orbit(out c)| = |ι|`）。 -/
theorem card_Idx : Fintype.card (Idx F G ι κ) = Fintype.card ι := by
  calc Fintype.card (Idx F G ι κ)
      = ∑ c : Quotient (orbitRelκ κ),
          Fintype.card ↥(Sset (F := F) κ (Quotient.out c)) :=
        Fintype.card_sigma
    _ = ∑ c : Quotient (orbitRelκ κ), (stabκ κ (Quotient.out c)).index :=
        Finset.sum_congr rfl fun c _ => card_Sset F G ι κ (Quotient.out c)
    _ = ∑ c : Quotient (orbitRelκ κ),
          Fintype.card ↥(orbitκ κ (Quotient.out c)) :=
        Finset.sum_congr rfl fun c _ => (card_orbitκ G ι κ (Quotient.out c)).symm
    _ = Fintype.card ι := (orbit_partition_card G ι κ).symm

/-! ### 2.2 配对抽取（Gram 对角化：`dualY_p(Y_q)` 的显式值）

机制 = **特征正交**（`sum_char_orthog`）＋ **`κ`-原像抽取**（`dualY_coord`）——
与 §2.1 的计数机制（轨道-稳定子 ＋ 对偶子群基数）**相互独立**（L-D），
供 §2.3 的无关性（Gram 对角化）用。 -/

/-- 配对：`dualY_p(Y_q)`——同轨道层经特征正交得 `|G|`（当字符一致），否则 `0`。 -/
theorem dualY_pair (p q : Idx F G ι κ) :
    dualY F G Q ι B κ p (YSub F G Q ι B κ q)
      = if p.1 = q.1 then
          (if (p.2 : MulChar G F) = (q.2 : MulChar G F) then
            ((Fintype.card G : ℕ) : F) else 0)
          else 0 := by
  rw [YSub, map_sum]
  by_cases hc : p.1 = q.1
  · rw [if_pos hc]
    have hout : Quotient.out p.1 = Quotient.out q.1 := congrArg Quotient.out hc
    have hpt : ∀ σ : G, dualY F G Q ι B κ p
        (((q.2 : MulChar G F) σ)⁻¹ • monoSub F Q ι B (κ σ (Quotient.out q.1)))
        = ((q.2 : MulChar G F) σ)⁻¹ * (p.2 : MulChar G F) σ := fun σ => by
      have h0 : ∃ ρ : G, κ ρ (Quotient.out p.1) = κ σ (Quotient.out q.1) :=
        ⟨σ, congrArg (fun j : ι => κ σ j) hout⟩
      have h1 : (p.2 : MulChar G F) (Classical.choose h0)
          = (p.2 : MulChar G F) σ :=
        char_eq_of_witness F G ι κ p
          ((Classical.choose_spec h0).trans
            (congrArg (fun j : ι => κ σ j) hout.symm))
      rw [map_smul, dualY_coord F G Q ι B κ p (κ σ (Quotient.out q.1)),
        dif_pos h0, smul_eq_mul]
      show ((q.2 : MulChar G F) σ)⁻¹ * (p.2 : MulChar G F) (Classical.choose h0)
        = ((q.2 : MulChar G F) σ)⁻¹ * (p.2 : MulChar G F) σ
      rw [h1]
    have hs : (∑ σ : G, dualY F G Q ι B κ p
        (((q.2 : MulChar G F) σ)⁻¹ • monoSub F Q ι B (κ σ (Quotient.out q.1))))
        = ∑ σ : G, ((q.2 : MulChar G F) σ)⁻¹ * (p.2 : MulChar G F) σ :=
      Finset.sum_congr rfl fun σ _ => hpt σ
    exact hs.trans (sum_char_orthog F G (q.2) (p.2))
  · rw [if_neg hc]
    have hpt : ∀ σ : G, dualY F G Q ι B κ p
        (((q.2 : MulChar G F) σ)⁻¹ • monoSub F Q ι B (κ σ (Quotient.out q.1)))
        = 0 := fun σ => by
      have h0 : ¬∃ ρ : G, κ ρ (Quotient.out p.1) = κ σ (Quotient.out q.1) := by
        rintro ⟨ρ, hρ⟩
        have h2 : (orbitRelκ κ).r (Quotient.out p.1) (Quotient.out q.1) :=
          (orbitRelκ_iff κ (Quotient.out p.1) (Quotient.out q.1)).mpr
            ⟨ρ⁻¹ * σ, by
              rw [map_mul, Equiv.Perm.mul_apply, ← hρ, ← Equiv.Perm.mul_apply,
                ← map_mul, inv_mul_cancel, map_one]
              rfl⟩
        exact hc ((Quotient.out_eq p.1).symm.trans
          ((Quotient.sound h2).trans (Quotient.out_eq q.1)))
      rw [map_smul, dualY_coord F G Q ι B κ p (κ σ (Quotient.out q.1)),
        dif_neg h0, smul_eq_mul, mul_zero]
    exact (Finset.sum_congr rfl fun σ _ => hpt σ).trans
      (Finset.sum_eq_zero fun _ _ => rfl)

/-- 自对偶配对：`dualY_q(Y_q) = |G|`。 -/
theorem dualY_pair_self (q : Idx F G ι κ) :
    dualY F G Q ι B κ q (YSub F G Q ι B κ q) = ((Fintype.card G : ℕ) : F) := by
  rw [dualY_pair F G Q ι B κ q q]
  rw [if_pos rfl, if_pos rfl]

/-- 配对抽取（对角化）：`∑_p g(p)·dualY_q(Y_p) = |G|·g(q)`。 -/
theorem pair_extract (q : Idx F G ι κ) (g : Idx F G ι κ → F) :
    (∑ p : Idx F G ι κ, g p * dualY F G Q ι B κ q (YSub F G Q ι B κ p))
      = ((Fintype.card G : ℕ) : F) * g q := by
  have h1 : (∑ p : Idx F G ι κ, g p * dualY F G Q ι B κ q (YSub F G Q ι B κ p))
      = (∑ p : Idx F G ι κ, g p * (if q.1 = p.1 then
          (if (q.2 : MulChar G F) = (p.2 : MulChar G F) then
            ((Fintype.card G : ℕ) : F) else 0) else 0)) :=
    Finset.sum_congr rfl fun p _ => by rw [dualY_pair F G Q ι B κ q p]
  rw [h1, Fintype.sum_sigma]
  refine (Finset.sum_eq_single q.1 ?_ ?_).trans ?_
  · intro c _ hc
    have hcχ : ∀ χ : ↥(Sset (F := F) κ (Quotient.out c)),
        g ⟨c, χ⟩ * (if q.1 = (⟨c, χ⟩ : Idx F G ι κ).1 then
          (if (q.2 : MulChar G F) = ((⟨c, χ⟩ : Idx F G ι κ).2 : MulChar G F)
            then ((Fintype.card G : ℕ) : F) else 0) else 0) = 0 := fun χ => by
      rw [if_neg (fun h : q.1 = (⟨c, χ⟩ : Idx F G ι κ).1 => hc h.symm), mul_zero]
    exact Finset.sum_eq_zero fun χ _ => hcχ χ
  · intro h
    exact absurd (Finset.mem_univ q.1) h
  · have h2 : (∑ χ : ↥(Sset (F := F) κ (Quotient.out q.1)),
        g ⟨q.1, χ⟩ * (if q.1 = (⟨q.1, χ⟩ : Idx F G ι κ).1 then
          (if (q.2 : MulChar G F) = ((⟨q.1, χ⟩ : Idx F G ι κ).2 : MulChar G F)
            then ((Fintype.card G : ℕ) : F) else 0) else 0))
        = (∑ χ : ↥(Sset (F := F) κ (Quotient.out q.1)),
          g ⟨q.1, χ⟩ * (if (q.2 : MulChar G F) =
            ((⟨q.1, χ⟩ : Idx F G ι κ).2 : MulChar G F)
            then ((Fintype.card G : ℕ) : F) else 0)) :=
      Finset.sum_congr rfl fun χ _ => by
        rw [if_pos (rfl : q.1 = (⟨q.1, χ⟩ : Idx F G ι κ).1)]
    refine h2.trans ?_
    refine (Finset.sum_eq_single q.2 ?_ ?_).trans ?_
    · intro χ _ hχ
      rw [if_neg (fun h : (q.2 : MulChar G F) =
          ((⟨q.1, χ⟩ : Idx F G ι κ).2 : MulChar G F) =>
        hχ (Subtype.ext h).symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ q.2) h
    · rw [if_pos (rfl : (q.2 : MulChar G F) =
          ((⟨q.1, q.2⟩ : Idx F G ι κ).2 : MulChar G F))]
      exact mul_comm _ _

/-! ### 2.3 特征基：非零／特征性／无关性／基（capstone）

非零机制 = **配对抽取的自对偶**（`dualY_pair_self`）；特征性机制 = **重指标**
（`Fintype.sum_bijective` ＋ 系数链 `χ(τ⁻¹ρ)⁻¹ = χ(τ)χ(ρ)⁻¹`）；无关性机制 =
**Gram 对角化**（`pair_extract`）——与 §2.1 计数（轨道-稳定子 ＋ 对偶子群基数）、
§2.2 配对（特征正交）均不共用自证管道（L-D）。 -/

/-- `Y_{i,χ} ≠ 0`：经 `dualY` 自配对读数为 `|G| ≠ 0`。 -/
theorem YSub_ne_zero (p : Idx F G ι κ) : YSub F G Q ι B κ p ≠ 0 := by
  intro h
  have h1 := dualY_pair_self F G Q ι B κ p
  rw [h, map_zero] at h1
  exact natCast_card_ne_zero (F := F) (G := G) h1.symm

/-- `Y_{i,χ} ≠ 0`（`F(Q)` 层）。 -/
theorem Y_ne_zero (p : Idx F G ι κ) : Y F G Q ι B κ p ≠ 0 := by
  rw [Y_coe F G Q ι B κ p]
  exact fun h => YSub_ne_zero F G Q ι B κ p (Subtype.ext h)

/-- **特征性**：`σ • Y_{i,χ} = χ(σ) • Y_{i,χ}`（重指标 ＋ 系数链 `χ(τ⁻¹ρ)⁻¹ = χ(τ)χ(ρ)⁻¹`）。 -/
theorem Y_smul
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (τ : G) (p : Idx F G ι κ) :
    τ • Y F G Q ι B κ p = (p.2 : MulChar G F) τ • Y F G Q ι B κ p := by
  have h1 : τ • Y F G Q ι B κ p
      = ∑ σ : G, ((p.2 : MulChar G F) σ)⁻¹
          • (τ • mono F Q ι B (κ σ (Quotient.out p.1))) := by
    rw [Y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm]
  have h2 : (∑ σ : G, ((p.2 : MulChar G F) σ)⁻¹
        • (τ • mono F Q ι B (κ σ (Quotient.out p.1))))
      = ∑ σ : G, ((p.2 : MulChar G F) σ)⁻¹
          • mono F Q ι B (κ (τ * σ) (Quotient.out p.1)) :=
    Finset.sum_congr rfl fun σ _ => by
      have hσ : τ • mono F Q ι B (κ σ (Quotient.out p.1))
          = mono F Q ι B (κ (τ * σ) (Quotient.out p.1)) := by
        rw [smul_mono (F := F) (hκ := hκ), map_mul, Equiv.Perm.mul_apply]
      rw [hσ]
  have h3 : (∑ σ : G, ((p.2 : MulChar G F) σ)⁻¹
        • mono F Q ι B (κ (τ * σ) (Quotient.out p.1)))
      = ∑ ρ : G, ((p.2 : MulChar G F) τ * ((p.2 : MulChar G F) ρ)⁻¹)
          • mono F Q ι B (κ ρ (Quotient.out p.1)) := by
    refine (Fintype.sum_bijective (fun σ : G => τ * σ) (Equiv.mulLeft τ).bijective
      (fun σ : G => ((p.2 : MulChar G F) σ)⁻¹
        • mono F Q ι B (κ (τ * σ) (Quotient.out p.1)))
      (fun ρ : G => ((p.2 : MulChar G F) (τ⁻¹ * ρ))⁻¹
        • mono F Q ι B (κ (τ * (τ⁻¹ * ρ)) (Quotient.out p.1)))
      (fun σ => by
        have e1 : τ⁻¹ * (τ * σ) = σ := inv_mul_cancel_left τ σ
        have e2 : (p.2 : MulChar G F) (τ⁻¹ * (τ * σ)) = (p.2 : MulChar G F) σ :=
          congrArg (fun x : G => (p.2 : MulChar G F) x) e1
        have e3 : κ (τ * (τ⁻¹ * (τ * σ))) (Quotient.out p.1)
            = κ (τ * σ) (Quotient.out p.1) :=
          congrArg (fun x : G => κ (τ * x) (Quotient.out p.1)) e1
        rw [e2, e3])).trans ?_
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hc : ((p.2 : MulChar G F) (τ⁻¹ * ρ))⁻¹
        = (p.2 : MulChar G F) τ * ((p.2 : MulChar G F) ρ)⁻¹ := by
      rw [map_mul, map_inv (p.2 : MulChar G F) τ, mul_inv_rev, inv_inv, mul_comm]
    have e4 : κ (τ * (τ⁻¹ * ρ)) (Quotient.out p.1) = κ ρ (Quotient.out p.1) :=
      congrArg (fun x : G => κ x (Quotient.out p.1)) (mul_inv_cancel_left τ ρ)
    rw [hc, e4]
  have h4 : (p.2 : MulChar G F) τ • Y F G Q ι B κ p
      = ∑ ρ : G, ((p.2 : MulChar G F) τ * ((p.2 : MulChar G F) ρ)⁻¹)
          • mono F Q ι B (κ ρ (Quotient.out p.1)) := by
    rw [Y, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_smul _ _ _
  exact (h1.trans (h2.trans h3)).trans h4.symm

/-- `Y`-族在 `Wb` 中 `F`-无关（Gram 对角化：`pair_extract` 抽取 ＋ `|G| ≠ 0`）。 -/
theorem YSub_linearIndependent : LinearIndependent F (YSub F G Q ι B κ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hpush : dualY F G Q ι B κ q (∑ p : Idx F G ι κ, g p • YSub F G Q ι B κ p)
      = ∑ p : Idx F G ι κ, g p * dualY F G Q ι B κ q (YSub F G Q ι B κ p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, smul_eq_mul]
  have h0 : (∑ p : Idx F G ι κ, g p * dualY F G Q ι B κ q (YSub F G Q ι B κ p)) = 0 := by
    have h := congrArg (fun w : ↥(Wb F Q ι B) => dualY F G Q ι B κ q w) hg
    rw [map_zero, hpush] at h
    exact h
  rw [pair_extract F G Q ι B κ q g] at h0
  exact (mul_eq_zero.mp h0).resolve_left (natCast_card_ne_zero (F := F) (G := G))

/-- **capstone**：`{Y_{i,χ}}` 构成 `Wb` 的 `F`-基（无关性 ＋ 计数 = 秩）。 -/
noncomputable def YBasis : Module.Basis (Idx F G ι κ) F ↥(Wb F Q ι B) := by
  haveI : FiniteDimensional F ↥(Wb F Q ι B) := finiteDimensional_Wb F Q ι B
  exact basisOfLinearIndependentOfCardEqFinrank' (YSub F G Q ι B κ)
    (YSub_linearIndependent F G Q ι B κ)
    ((card_Idx F G ι κ).trans (finrank_Wb F Q ι B).symm)

/-- `YBasis` 在指标上的取值（回归 `YSub`）。 -/
@[simp] theorem YBasis_apply (p : Idx F G ι κ) :
    YBasis F G Q ι B κ p = YSub F G Q ι B κ p := by
  haveI : FiniteDimensional F ↥(Wb F Q ι B) := finiteDimensional_Wb F Q ι B
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := F)
    (YSub F G Q ι B κ) (YSub_linearIndependent F G Q ι B κ)
    ((card_Idx F G ι κ).trans (finrank_Wb F Q ι B).symm)) p

end Chars

/-! ## 3. 公理闸门（分段） -/

#print axioms orbitRelκ
#print axioms orbitκ
#print axioms stabκ
#print axioms Sset
#print axioms mem_stabκ_iff
#print axioms mem_orbitκ_iff
#print axioms orbitRelκ_iff
#print axioms mem_Sset_iff
#print axioms orbitκ_units_eq
#print axioms natCast_card_units_ne_zero
#print axioms natCast_card_ne_zero
#print axioms natCast_ne_zero_of_dvd
#print axioms algToField
#print axioms monoAlg
#print axioms mono
#print axioms Wb
#print axioms mono_mem
#print axioms smul_monoAlg
#print axioms smul_algebraMap_eq
#print axioms smul_mono
#print axioms Wb_smul_mem
#print axioms permMono_injective_basis
#print axioms monoAlg_linearIndependent
#print axioms mono_linearIndependent
#print axioms finrank_Wb
#print axioms finiteDimensional_Wb

-- §2.1 特征正交与轨道计数（Chunk 1）
#print axioms instFintypeMulCharBasis
#print axioms sum_char_orthog
#print axioms orbit_partition_card
#print axioms card_Sset
#print axioms card_orbitκ
#print axioms card_Idx

-- §2.2 配对抽取（Chunk 2）
#print axioms dualY_pair
#print axioms dualY_pair_self
#print axioms pair_extract

-- §2.3 特征基（Chunk 3）
#print axioms YSub_ne_zero
#print axioms Y_ne_zero
#print axioms Y_smul
#print axioms YSub_linearIndependent
#print axioms YBasis
#print axioms YBasis_apply

end Basis

end EM

end ABGV52
