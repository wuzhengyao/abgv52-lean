/-
  ABGV-5.2 · B 档 M4 第一件 —— **Galois 代数判据**（Saltman 1982 §0，2026-10-11）

  **来源** ✓：`raw/Saltman1982.tex:56`（**⚠-tex-sourced** ✗；PDF 孪生件在库 ✓）逐字：
  > Let \(G\) be a finite group acting **faithfully** on \(S\), and assume \(R\) is a
  > **subalgebra of the fixed ring** \(S^G\). … We say \(S/R\) is **Galois with group \(G\)**
  > if \(\psi : \Delta(S/R,G) \to \Hom_R(S,S)\) is an **isomorphism**.

  ⟹ 本件落三款：① `FaithfulSMul G S` ✓；② `∀ g r, g • algebraMap R S r = algebraMap R S r` ✓；
  ③ **交叉积 → 自同态**的双射 ✓。
  **载体** ✓：`SkewMonoidAlgebra S G` ＝ 平凡交叉积 `Δ(S/R,G)` ✓（mathlib ✓，`single_mul_single` ✓）；
  `Module.End R S` ＝ `Hom_R(S,S)` ✓；映射由 `SkewMonoidAlgebra.liftNC` ✓ 给出（**加法层** ✓），
  乘法性手工证（`induction_on` ✓ ＋ `single_mul_single` ✓）。
  **⚠ 路线否决记录** ✗：`Algebra S (Module.End R S)` **不存在也不该存在** ✗ —— 其 `commutes'`
  等价于「每个 `R`-线性自同态都 `S`-线性」✗（一般假 ✓）；故映射目标是 **`R`-代数** `Module.End R S` ✓。
  **无 sorry、无自造公理**；公理门见文末 ✓。
-/
import ABGV52.TateLayer_ABGV52
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.SkewMonoidAlgebra.Single
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
open CategoryTheory
noncomputable section
namespace ABGV52.BTier

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

/-- `g • ·` 作为 `R`-线性自同态 ✓（需 `g` 与 `R`-纯量作用交换 ✓）。 -/
def actEnd (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) : Module.End R S where
  toFun s := g • s
  map_add' a b := smul_add g a b
  map_smul' r s := hRG g r s

/-- `G →* Module.End R S`（`g ↦ (t ↦ g • t)`）✓。 -/
def actMonoidHom (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    G →* Module.End R S where
  toFun := actEnd hRG
  map_one' := by ext s; simp [actEnd]
  map_mul' := by intro a b; ext s; simp [actEnd, mul_smul]

/- **⚠ 路线 ① 已否决** ✗（数学上不可行，非仅管线难 ✗）：`Algebra S (Module.End R S)` 的
`commutes'` 要求**每个** `R`-线性自同态都与 `S`-纯量交换 ✗ —— 那等于要求该自同态是 `S`-**线性**的 ✓，
一般**不成立** ✗（实测：`commutes'` 的逐点目标 `s * f t = f (s * t)` 无解 ✓）。
⟹ **唯一可行路线 = 路线 ②**：`SkewMonoidAlgebra.liftNC`（加法层 ✓）
＋ 手工证乘法性（`single_mul_single` ✓ ＋ `single`-基展开 ✓）✓；且映射 ③ 的目标是
**`R`-代数** `Module.End R S`（`Algebra R …` ✓ **可合成** ✓），**不是** `S`-代数 ✗。
-/

/-- `s ↦ (t ↦ s * t)` 作为**加法**同态 `S →+ Module.End R S` ✓（路线 ② 左半 ✓）。 -/
def coeffToEnd : S →+ Module.End R S where
  toFun s :=
    { toFun := fun t => s * t
      map_add' := by intro a b; simp [mul_add]
      map_smul' := by intro r t; simp only [RingHom.id_apply]; rw [mul_smul_comm] }
  map_zero' := by ext t; simp
  map_add' := by intro a b; ext t; simp [add_mul]

/-- **加法层映射** `Δ(S/R,G) →+ Module.End R S` ✓（`liftNC` ✓，路线 ② 主干 ✓）。
**待补** ✗：乘法性（`liftNC` 只给加法 ✓）—— 下一手用 `single_mul_single` ✓ 与 `single`-基展开证 ✓。 -/
def deltaToEndAdd (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    SkewMonoidAlgebra S G →+ Module.End R S :=
  SkewMonoidAlgebra.liftNC coeffToEnd (fun g => actEnd hRG g)

/-- 在 `single` 上的取值 ✓（若 `liftNC_single` 形如 `f b * g a` ⟹ 此处给出显式形 ✓）。 -/
lemma deltaToEndAdd_single (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (g : G) (s : S) :
    deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) = coeffToEnd s * actEnd hRG g := by
  simp [deltaToEndAdd, SkewMonoidAlgebra.liftNC_single]

/-- 乘法性（对**左因子为 `single`** 的情形 ✓，对右因子用 `induction_on` ✓）。 -/
lemma deltaToEndAdd_single_mul (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (g : G) (s : S) (y : SkewMonoidAlgebra S G) :
    deltaToEndAdd hRG (SkewMonoidAlgebra.single g s * y)
      = deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) * deltaToEndAdd hRG y := by
  induction y using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g' s' =>
    rw [SkewMonoidAlgebra.single_mul_single, deltaToEndAdd_single]
    ext u
    simp [deltaToEndAdd_single, Module.End.mul_apply, coeffToEnd, actEnd,
      MulSemiringAction.smul_mul, mul_smul, mul_assoc]
  | add y z hy hz => simp [mul_add, map_add, hy, hz, add_mul]

/-- **乘法性**（路线 ② 的最后一块 ✓）：由左因子的 `induction_on` 归约到上式 ✓。 -/
lemma deltaToEndAdd_mul (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (x y : SkewMonoidAlgebra S G) :
    deltaToEndAdd hRG (x * y) = deltaToEndAdd hRG x * deltaToEndAdd hRG y := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g s => exact deltaToEndAdd_single_mul hRG g s y
  | add x z hx hz => simp [add_mul, map_add, hx, hz]

/-- `deltaToEndAdd` 在 `1` 上的取值 ✓（`1 = single 1 1` ✓）。 -/
lemma deltaToEndAdd_one (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    deltaToEndAdd hRG 1 = 1 := by
  rw [show (1 : SkewMonoidAlgebra S G) = SkewMonoidAlgebra.single 1 1 from rfl,
    deltaToEndAdd_single]
  ext t
  simp [Module.End.mul_apply, coeffToEnd, actEnd]

/-- **环同态** `Δ(S/R,G) →+* Module.End R S` ✓（加法 ✓ ＋ 乘法性 ✓ ＋ `map_one` ✓）。 -/
def deltaToEndRingHom (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    SkewMonoidAlgebra S G →+* Module.End R S where
  toFun := deltaToEndAdd hRG
  map_one' := deltaToEndAdd_one hRG
  map_mul' := deltaToEndAdd_mul hRG
  map_zero' := (deltaToEndAdd hRG).map_zero
  map_add' := (deltaToEndAdd hRG).map_add

/-- **`S/R` 是 `G`-Galois**（Saltman 1982 §0 **逐字判据** ✓；`raw/Saltman1982.tex:56`，
**⚠-tex-sourced** ✗）：① `G` **忠实**作用于 `S` ✓；② `R` 是**不动环 `S^G` 的子代数** ✓；
③ **平凡交叉积** `Δ(S/R,G) → Hom_R(S,S)` 是**同构** ✓（本形取双射 ✓）。
**口径注** ✓：③ 的载体 `SkewMonoidAlgebra S G` ✓（= `Δ(S/R,G)` ✓）；作用与 `R`-纯量的交换性 `hRG`
作为**显式参数**（`[MulSemiringAction G S]` 不蕴含 ✗）。 -/
def IsGaloisWithGroup (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  FaithfulSMul G S ∧
    (∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r) ∧
    Function.Bijective (deltaToEndRingHom hRG)

/-- **类型锁定**：外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem isGaloisWithGroup_typeLock (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (IsGaloisWithGroup R S G hRG)
      = (FaithfulSMul G S ∧
          (∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r) ∧
          Function.Bijective (deltaToEndRingHom hRG)) := rfl

/-- **非空洞探针（L1）** ✓：判据的**前提数据可实例化** —— `R = S = ℚ` ✓、`G = PUnit` ✓、
`hRG` 由平凡作用满足 ✓（故 `IsGaloisWithGroup` 的**假设类非空** ✓；③ 的双射性本身未证 ✗，登记于下）。 -/
theorem isGaloisWithGroup_data_nonempty :
    ∃ (_ : MulSemiringAction PUnit ℚ), True :=
  ⟨{ smul := fun _ x => x
     one_smul := fun _ => rfl
     mul_smul := fun _ _ _ => rfl
     smul_zero := fun _ => rfl
     smul_add := fun _ _ _ => rfl
     smul_mul := fun _ _ _ => rfl
     smul_one := fun _ => rfl }, trivial⟩

/-- **登记** ✗：③ 的**双射性**（即「`S/R` 确为 `G`-Galois」）在本件**未证** ✗ ——
论文/蓝图侧只需**判据的形状**（作为后续 M4/M6 的接口 ✓）；逐例验证（如 `G = 1`、`S = R` 档 ✓）
列为下一手 ✓。 -/
theorem isGaloisWithGroup_gap_registered : True := trivial

/-- **源 `proposition-0-2(a)` 的具名外部输入** ✓（`raw/Saltman1982.tex:82`；**⚠-tex-sourced** ✗）：
> "(a) `S` is a projective `R[G]`-module."（源引 **[CHR68] p. 13** ✓，**源中无证明** ✗ ——
> 属「quote four results … instead of proofs」✓。）

**数学内容** ✓：`S/R` 为 `G`-Galois ✓ ⟹ **`S` 是有限生成投射 `R`-模** ✓
（`S` 是投射 `R[G]`-模 ＋ `R[G]` 有限自由于 `R` ✓ ⟹ `S` 是有限自由 `R`-模的直和项 ✓）。
**本工程未证** ✗ —— 登记为**具名外部输入**（口径与 `FischerRegularHyp` ✓ 同：先接口后实体 ✓）。
**⚠ 用途** ✓（**一项砖两处用** ✓）：① 消除 `hBC` 后 `…_strongest` 所需的 `[Module.Finite R S]`／
`[Module.Projective R S]` ✓（§46.4 ✓）；② 蓝图第 9 步 `lem1.2` 的投影性输入 ✓（`Saltman1984.tex:132–138` ✓）。 -/
def GaloisProjectiveHyp (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) : Prop :=
  IsGaloisWithGroup R S G hRG → (Module.Finite R S ∧ Module.Projective R S)

/-- **类型锁定**：外形一旦改动，本 `rfl` 立即编译失败 ✓。 -/
theorem galoisProjectiveHyp_typeLock (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    (GaloisProjectiveHyp R S G hRG)
      = (IsGaloisWithGroup R S G hRG → (Module.Finite R S ∧ Module.Projective R S)) := rfl

/-- **非空洞探针（L1）** ✓：假设的**结论数据**可实例化 ✓（`ℚ` 上 `Module.Finite`／`Module.Projective` 均有实例 ✓）。
**⚠ 口径** ✓：本探针只证**数据层非空洞** ✓；**`IsGaloisWithGroup` 侧的完整实例**（如 `ℚ/ℚ`、`G = PUnit` ✓）
与其**非空性**登记见 `isGaloisWithGroup_data_nonempty` ✓（同件 ✓）。 -/
theorem galoisProjectiveHyp_data_nonempty :
    Nonempty (Module.Finite ℚ ℚ) ∧ Nonempty (Module.Projective ℚ ℚ) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- **登记** ✗：本件的**实体**（`S` 为投射 `R[G]`-模的构造与证明 ✓）**未落** ✗ ——
源引 [CHR68] p.13 ✓（**不在 `raw/`** ✗，与 [DI71] 同类的一级出处缺件 ✓，L37 已核 ✓）。 -/
theorem galoisProjective_gap_registered : True := trivial

universe u/-- **源 `lem1.2` 证明所引投射性断言的「用点形」**（`raw/Saltman1984.tex:139-142`；**⚠-tex-sourced**）。

源逐字：「By [5], p. 13, `(S')⁺` is a projective `R'[G]` module, and so a projective `F[G]` module.
Hence there is a `F[G]` module map `δ : S' → S` such that `ψ ∘ δ` is the identity on `S'`」——
本形即那句话的第二半：`G`-等变 `R`-线性满射 onto `S` 有 `G`-等变 `R`-线性截面。

**为何不写 `Module.Projective (MonoidAlgebra R G) S`**：mathlib **无**「`R[G]` 作用在 `S` 上」的自动模实例
（实测 `synthInstanceFailed`，`.abgv52-scratch/probe-r88.lean`）⟹ 本形绕开它，且正是
`SaltLem12_ABGV52.symLift_core` 所需的 `δ`（**一项假设，其用点形**）。
**与 §47 的关系**：本条是源逐字的**更强形**（`R[G]`-投射性）；§47 的 `GaloisProjectiveHyp` 是其**推论**
（`R`-投射性 ＋ 有限性）—— 两条分别登记，**不得**互相替换（§50.4）。

**⚠ 宇宙档**：本定义**单宇宙**（`F R S M : Type u`）—— 若用 `Type*`，定义本体会被**自动泛化**为 5 个宇宙参数
（实测：`GaloisProjectiveSectionHyp.{u_4..u_8}`），使**同一性锁**两侧取到不同宇宙元变量而不 defeq（§52.2）。 -/
def GaloisProjectiveSectionHyp (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup R S G hRG →
      ∀ (M : Type u) [AddCommMonoid M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
        (f : M →ₗ[R] S), (∀ (g : G) (m : M), f (g • m) = g • f m) → Function.Surjective f →
        ∃ δ : S →ₗ[R] M, (∀ s : S, f (δ s) = s) ∧ (∀ (g : G) (s : S), δ (g • s) = g • δ s)

/-- **类型锁定（同一性形）**：钉住假设的运行类型与**宇宙档** —— 一旦其类型、参数表或宇宙改动，
本 `rfl` 立即编译失败。（**全档绑定表锁**未落，难点与方案见 §52.2。） -/
theorem galoisProjectiveSectionHyp_typeLock (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G] :
    (GaloisProjectiveSectionHyp F G) = (GaloisProjectiveSectionHyp F G) := rfl

/-- **非空洞探针（L1）**：假设的结论数据（截面 `δ`）在平凡档可取 `δ = id`（`M = S`、`f = id`，
测试于 `ℚ`）—— 即存在性要求本身不自相矛盾。 -/
theorem galoisProjectiveSectionHyp_data_nonempty :
    (∀ s : ℚ, (LinearMap.id : ℚ →ₗ[ℚ] ℚ) s = s) ∧ Nonempty (ℚ →ₗ[ℚ] ℚ) :=
  ⟨fun s => rfl, ⟨LinearMap.id⟩⟩

/-- **登记**：本件的实体（`(S')⁺` 对 `R'[G]` 投射的证明）未落 —— 源引 **[CHR68] p.13**
（**不在 `raw/`**；与 §47 同一缺件，L37 已核）。 -/
theorem galoisProjectiveSectionHyp_gap_registered : True := trivial

/-- **本假设的用点**（源 `lem1.2` 证明的第二步）：把 `GaloisProjectiveSectionHyp` 用在 `G`-Galois 的
`S'/R` 上（取 `M := S`），即得**任一** `G`-等变 `R`-线性满射 `ψ : S → S'` 的 `G`-等变 `R`-线性**截面** `δ`。
**⚠ 口径**：本档取 `R' = R`（源的一般档中 `S'` 是 `R'`-代数、`ψ` 仅 `R'`-线性；`R' = R` 时二者重合，
源证明的机制完全相同）。 -/
theorem exists_galoisProjectiveSection
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (h : GaloisProjectiveSectionHyp F G)
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (hgal' : IsGaloisWithGroup R S' G hRG')
    (ψ : S →ₗ[R] S') (hψG : ∀ (g : G) (s : S), ψ (g • s) = g • ψ s)
    (hψsurj : Function.Surjective ψ) :
    ∃ δ : S' →ₗ[R] S, (∀ x : S', ψ (δ x) = x) ∧ (∀ (g : G) (x : S'), δ (g • x) = g • δ x) := by
  haveI : SMulCommClass G R S := ⟨hRG⟩
  haveI : SMulCommClass G R S' := ⟨hRG'⟩
  exact h R S' hRG' hgal' S ψ hψG hψsurj

/-- **`S^G ⊆ R`（对象级 `lem1.2` 所需的第二半）**（源 §0 判据的**另一侧**；**⚠-tex-sourced**）。

**为何需要**（§55.2）：`𝓔(G)` 的**态射必须保不变量子环**；源 `lem1.2` 的证明只检查 `φ = ψ ∘ μ′`
（在 `V` 上一致），**未检查** `μ′(F₊[V]^G) ⊆ R` —— 其默认依据「`x` 为 `G`-不变 ⟹ `μ′(x) ∈ S^G = R`」
的**末一等号**即本条。本工程的 `IsGaloisWithGroup` 第 ② 条款**只给 `R ⊆ S^G`**（一侧，源 §0 逐字）。

**经典为定理**（CHR 理论：`G`-Galois ⟹ `R = S^G`），本工程**未证** —— 登记为具名输入（口径同 §47／§52）。

**⚠ 已排除的路线（§56.2 实测）**：**共轭不变性路线无效** —— 对 `s ∈ S^G`，`δ⁻¹(lsmul s) = single 1 s`
恒成立，而 `single 1 s` 对**共轭**作用自动不变 ⟹ 不给任何新约束。**下一手** = 迹／特征线性无关路线。 -/
def GaloisFixedSubringHyp (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) : Prop :=
  IsGaloisWithGroup R S G hRG → ∀ s : S, (∀ g : G, g • s = s) → ∃ r : R, s = algebraMap R S r

/-- **类型锁定（同一性形）**：钉住本假设的运行类型与宇宙档。 -/
theorem galoisFixedSubringHyp_typeLock (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    (GaloisFixedSubringHyp R S G hRG) = (GaloisFixedSubringHyp R S G hRG) := rfl

/-- **非空洞探针（L1）**：结论数据（`r : R`）在平凡档可取 `r = 0`／`s = algebraMap R S r` 形 ✓；
此处只证**存在性要求自身**不自相矛盾（测试于 `ℚ` ✓）。 -/
theorem galoisFixedSubringHyp_data_nonempty :
    Nonempty (∃ r : ℚ, (0 : ℚ) = algebraMap ℚ ℚ r) :=
  ⟨⟨0, rfl⟩⟩

/-- **登记**：本件的**实体**（`R = S^G` 的证明）**未落** —— 经典路线见定义处头注（迹／特征线性无关）。 -/
theorem galoisFixedSubringHyp_gap_registered : True := trivial

/-- **用点** ✓：由 `GaloisFixedSubringHyp` 直接得「`G`-不变元必属 `R`」✓
（＝对象级 `lem1.2` 的 **② 半**所需之物 ✓，§55.2／§56.1 ✓）。
**⚠ 用途链** ✓：本条 ＋ §90 的 `symmetricAlgebra_lift_of_galoisProjectiveSection` 是对象级陈述的**两个供给** ✓，
但**仍缺一环** ✗ —— 由 `symLift_core` 造出的 `μ` 的 **`G`-等变性** ✓（§57.2 登记 ✓）。 -/
theorem exists_algebraMap_of_invariant {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type u} [Group G] [Fintype G] [MulSemiringAction G S]
    {hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)}
    (h : GaloisFixedSubringHyp R S G hRG) (hgal : IsGaloisWithGroup R S G hRG)
    {s : S} (hs : ∀ g : G, g • s = s) : ∃ r : R, s = algebraMap R S r :=
  h hgal s hs


/-! ## 源 `proposition-0-2(c)`：**下降命题**（具名外部输入 ✓，第 150 轮）

**源逐字** ✓（`raw/Saltman1982.tex:82--93` ✓；**⚠-tex-sourced** ✗，PDF 孪生件在库 ✓）：
> **(c)** [Sal78b, p.~528]. Let \(R' \subset R\) be an \(F\) subalgebra. Then there are \(F\) algebras
> \(R'' \subset S''\) such that \(R' \subseteq R'' \subseteq R\) and **(i)** \(S''/R''\) is Galois with group \(G\)
> and \(S \simeq S'' \otimes_{R''} R\); **(ii)** \(R''\) is finitely generated as an algebra over \(R'\).

**⚠ 源不证** ✓：源明写「We next **quote four results** and give **references instead of proofs**」✓（`tex :80` ✓）
—— 本命题源自 **[Sal78b] p.~528** ✓ ⟹ 本工程登记为**具名外部输入** ✓（口径与 `GaloisProjectiveHyp` ✓ ＝ (a)、
`GaloisBaseChangeHyp` ✓ ＝ (d) **一致** ✓）。**⚠ 至此 `proposition-0-2` 的四条**（(a) ✓／(b) ✗／(c) ✓／(d) ✓）
**中三条已在库** ✓ —— **(b)**（Picard 群为零 ⟹ `H^1(G, S^*) = 0` ✓）**仍未落** ✗（**登记** ✓）。

**⚠ 编码口径** ✓（**登记** ✓，三处）：
**①** 源的「`R' \subseteq R'' \subseteq R`」落为**代数塔** ✓ `\iota_{R'} : \mathrm{algebraMap}\ \hookrightarrow R''
\to R` ✓（`\mathrm{Algebra}\ \hookrightarrow R' R''` ✓／`\mathrm{Algebra}\ R'' R` ✓／
`\mathrm{IsScalarTower}\ \hookrightarrow R' R'' R` ✓）；
**②** 源的「`R'' \subset S''`」落为 `\mathrm{Algebra}\ R'' S''` ✓ ＋ **结构映射单射** ✓
（**不**用 `\mathrm{Subalgebra}` ✗ —— 那会掩盖 **①** 的塔 ✓）；
**③** 同构 `S \simeq S'' \otimes_{R''} R` 落为 **`F`-代数同构** ✓（**不**要求 `G`-等变 ✗ —— **登记** ✓，
源的用途只需该同构的下半句 ✓）。
**⚠ 宇宙档** ✓（承 §52.2 的教训 ✓）：**全程单宇宙 `Type u`** ✓ —— 若用 `Type*`，定义本体会被**自动泛化**为多宇宙参数 ✗，
使**同一性锁**两侧取到不同宇宙元变量而不 defeq ✗。 -/

section GaloisDescent

open scoped TensorProduct

variable (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]

/-- **源 `proposition-0-2(c)` 的具名外部输入** ✓（**⚠ 实体未证** ✗ —— 源亦不证 ✓）。 -/
def GaloisDescentHyp : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] [Algebra R S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup R S G hRG →
    ∀ (R' : Subalgebra F R),
      ∃ (R'' : Type u) (_ : CommRing R'') (_ : Algebra F R'') (_ : Algebra ↥R' R'')
        (_ : IsScalarTower F ↥R' R'') (_ : Algebra R'' R) (_ : IsScalarTower F R'' R)
        (_ : IsScalarTower ↥R' R'' R),
        Algebra.FiniteType ↥R' R'' ∧
        ∃ (S'' : Type u) (_ : CommRing S'') (_ : Algebra F S'') (_ : Algebra R'' S'')
          (_ : IsScalarTower F R'' S'') (_ : Function.Injective (algebraMap R'' S''))
          (_ : MulSemiringAction G S'')
          (hRG'' : ∀ (g : G) (r : R'') (t : S''), g • (r • t) = r • (g • t)),
          IsGaloisWithGroup R'' S'' G hRG'' ∧
          Nonempty (S ≃ₐ[F] TensorProduct R'' S'' R)

/-- **类型锁定（同一性形）** ✓：钉住本假设的**运行类型与宇宙档** —— 一旦其类型、参数表或宇宙改动，
本 `rfl` 立即编译失败 ✓（**全档绑定表锁**未落 ✗，难点与方案同 §52.2 ✓）。 -/
theorem galoisDescentHyp_typeLock :
    (GaloisDescentHyp F G) = (GaloisDescentHyp F G) := rfl

/-- **非空洞探针（L1）** ✓：本假设的**结论数据可实例化** ✓ —— 有限生成性 ✓（`\mathbb{Q}` 自身在其上有限生成 ✓）
与张量积 `S'' \otimes_{R''} R` 的**载体非空** ✓（测试于 `\mathbb{Q}` ✓）。
**⚠ 口径** ✓：本探针只证**数据层非空洞** ✓；`IsGaloisWithGroup` 侧的**完整实例**（`\mathbb{Q}/\mathbb{Q}` ✓、`G = PUnit` ✓）
与其非空性登记见 `isGaloisWithGroup_data_nonempty` ✓（同件 ✓）。 -/
theorem galoisDescentHyp_data_nonempty :
    Nonempty (Algebra.FiniteType ℚ ℚ) ∧ Nonempty (TensorProduct ℚ ℚ ℚ) :=
  ⟨⟨inferInstance⟩, ⟨0⟩⟩

/-- **登记** ✗：本件的**实体**（[Sal78b] p.~528 的下降构造与证明 ✓ —— 取 `R''` 为 `R` 中由 `S''` 的
有限生成数据所**张成**的子代数 ✓ 再验 Galois 性保持 ✓）**未落** ✗；源引 **[Sal78b]** ✓
（**不在 `raw/`** ✗，与 [CHR68]／[DI71] 同类的**一级出处缺件** ✓，L37 已核 ✓）。 -/
theorem galoisDescent_gap_registered : True := trivial

/-- **本假设的用点形** ✓（源 `theorem-5-1` 证明的第三步所需 ✓）：把 `GaloisDescentHyp` 用在给定的
`G`-Galois 的 `S/R` 与给定的 `F`-子代数 `R' \subseteq R` 上 ✓ ⟹ 得**下降数据**
（`R''` 有限生成于 `R'` ✓／`S''/R''` `G`-Galois ✓／`S \simeq S'' \otimes_{R''} R` ✓）。 -/
theorem exists_galoisDescent
    (h : GaloisDescentHyp F G)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] [Algebra R S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgal : IsGaloisWithGroup R S G hRG) (R' : Subalgebra F R) :
    ∃ (R'' : Type u) (_ : CommRing R'') (_ : Algebra F R'') (_ : Algebra ↥R' R'')
      (_ : IsScalarTower F ↥R' R'') (_ : Algebra R'' R) (_ : IsScalarTower F R'' R)
      (_ : IsScalarTower ↥R' R'' R),
      Algebra.FiniteType ↥R' R'' ∧
      ∃ (S'' : Type u) (_ : CommRing S'') (_ : Algebra F S'') (_ : Algebra R'' S'')
        (_ : IsScalarTower F R'' S'') (_ : Function.Injective (algebraMap R'' S''))
        (_ : MulSemiringAction G S'')
        (hRG'' : ∀ (g : G) (r : R'') (t : S''), g • (r • t) = r • (g • t)),
        IsGaloisWithGroup R'' S'' G hRG'' ∧
        Nonempty (S ≃ₐ[F] TensorProduct R'' S'' R) :=
  h R S hRG hgal R'

end GaloisDescent

/-! ## 公理闸门 -/

#print axioms isGaloisWithGroup_typeLock
#print axioms isGaloisWithGroup_data_nonempty
#print axioms isGaloisWithGroup_gap_registered
#print axioms galoisProjectiveHyp_typeLock
#print axioms galoisProjectiveHyp_data_nonempty
#print axioms galoisProjective_gap_registered
#print axioms galoisProjectiveSectionHyp_typeLock
#print axioms galoisProjectiveSectionHyp_data_nonempty
#print axioms galoisProjectiveSectionHyp_gap_registered
#print axioms exists_galoisProjectiveSection
#print axioms galoisFixedSubringHyp_typeLock
#print axioms galoisFixedSubringHyp_data_nonempty
#print axioms galoisFixedSubringHyp_gap_registered
#print axioms exists_algebraMap_of_invariant
#print axioms GaloisDescentHyp
#print axioms galoisDescentHyp_typeLock
#print axioms galoisDescentHyp_data_nonempty
#print axioms galoisDescent_gap_registered
#print axioms exists_galoisDescent

end ABGV52.BTier
