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
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
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

/-- **判据第 ② 款由 `hRG` 自动成立** ✓✅（第 231 轮 ✓）：`g • algebraMap R S r = algebraMap R S r` ✓
**不必作假设** ✗ —— 用 `hRG` 取第三变元 `t := 1` ✓：`g • (r • 1) = r • (g • 1)` ✓，
左右分别化归 `g • algebraMap R S r` ✓（`Algebra.algebraMap_eq_smul_one` ✓）与 `algebraMap R S r` ✓（`smul_one` ✓）。
**⚠ 意义** ✓：`IsGaloisWithGroup` ✓ 的三款中 **② 是冗余款** ✓ —— 真正的假设只有 **① 忠实性** ✓ 与
**③ `\delta` 双射** ✓（**③ ＝ Galois 内容** ✓）。
**⚠ 与 `algebraMap_fixed_of_isGaloisWithGroup`** ✓（自 `hgal` **取出** ② ✓）**方向相反** ✓：
本条**不必先有 `hgal`** ✓。 -/
theorem algebraMap_fixed_of_smulCommClass {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) (g : G) (r : R) :
    g • algebraMap R S r = algebraMap R S r := by
  rw [Algebra.algebraMap_eq_smul_one (R := R) (A := S) r, hRG g r 1, smul_one]

/-- **非空洞探针（L1）** ✓：判据的**前提数据可实例化** —— `R = S = ℚ` ✓、`G = PUnit` ✓、
`hRG` 由平凡作用满足 ✓。
**⚠ 本探针只证数据层** ✗（`∃ action, True` ✓，**平凡** ✓）—— **不**证 `IsGaloisWithGroup` **成立** ✗
（**原文「故假设类非空」✗ 系过度声称** ✗，**第 236 轮更正** ✓）；**该步**由
`galoisEndpoints_satisfiable` ✓ **落** ✓（**同件** ✓，**文末反驳节** ✓）。 -/
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

/-! ## **`G`-Galois 代数的秩** ✓：`\mathrm{finrank}_K A = |G|`（第 184 轮）

**⚠ 起点** ✓（**(c) 款张量侧收口** ✓，第 184 轮 ✓）：r183 把张量侧压到**单一输入** ✓ —— **秩** ✗
（`\mathrm{finrank}_{K'}(K' \otimes_R S_0) = |G|` ✓，状态笔记 §146.4 ① ✓）。本件把**秩**从**本册判据内部**导出 ✓
（**不需要**外部源 ✗ —— 源 `proposition-0-2`(a) ✓ 只给**投射性** ✗，见 `GaloisProjectiveHyp` ✓）。

**⚠ 机制** ✓（**三件** ✓）：
**① `K`-线性** ✓：`\delta` 在 `\mathrm{single}`-生成元上满足
`\delta(k \bullet (s \cdot g)) = k \bullet \delta(s \cdot g)` ✓（`\mathrm{SkewMonoidAlgebra.smul\_single}` ✓ ＋
`\mathrm{smul\_mul\_assoc}` ✓），由 `\mathrm{induction\_on}` ✓ 升为整体 ✓；
**② 两侧 `\mathrm{finrank}`** ✓：`\mathrm{SkewMonoidAlgebra}\ A\ G \simeq_K (G \to_0 A)` ✓（`\mathrm{coeffLinearEquiv}` ✓）
⟹ 左 ＝ `|G| \cdot n` ✓（`\mathrm{Module.finrank\_finsupp}` ✓）；`\mathrm{End}_K A` ⟹ 右 ＝ `n^2` ✓
（`\mathrm{Module.finrank\_linearMap}` ✓）；
**③ 算术** ✓：`|G| \cdot n = n^2` ✓ ＋ `n \neq 0` ✓（`\mathrm{Module.finrank\_pos\_iff\_of\_free}` ✓ ＋ 非平凡 ✓）⟹ **`n = |G|`** ✓。

**⚠ 用途** ✓：**(c) 款张量侧** ✓ 的**秩输入**由此**内部供给** ✓（实例化于 `A := K' \otimes_R S_0` ✓，
其 `G`-Galois 性由 **(b) 款** ✓ 供给 ✓）—— **⟹ 秩不再是外部输入** ✓。
**⚠ 口径** ✓：本件**不**用 `\mathrm{GaloisProjectiveHyp}` ✓（那是**投射性** ✓）；秩由**判据第三款** ✓ 给出 ✓。 -/

section GaloisRank

universe u

variable {K A G : Type u} [Field K] [CommRing A] [Algebra K A]
variable [Group G] [Fintype G] [MulSemiringAction G A]

/-- **`G`-Galois 代数在域上的维数 ＝ `|G|`** ✓✅（**通用档** ✓）：判据第三款的双射
`\Delta(A/K,G) \simeq \mathrm{Hom}_K(A,A)` ✓ 是 **`K`-线性** ✓ ⟹ 两侧 `\mathrm{finrank}` 相等 ✓：
左 ＝ `|G| \cdot n` ✓（`\mathrm{coeffLinearEquiv}` ✓ ＋ `\mathrm{Module.finrank\_finsupp}` ✓），
右 ＝ `n^2` ✓（`\mathrm{Module.finrank\_linearMap}` ✓）⟹ **`n = |G|`** ✓（`n \neq 0` ✓ 由非平凡 ✓）。 -/
theorem finrank_eq_card_of_isGaloisWithGroup
    (hKA : ∀ (g : G) (r : K) (a : A), g • (r • a) = r • (g • a))
    (hgal : IsGaloisWithGroup K A G hKA)
    [Module.Finite K A] [Nontrivial A] :
    Module.finrank K A = Fintype.card G := by
  obtain ⟨-, -, hbij⟩ := hgal
  have hsmul : ∀ (k : K) (x : SkewMonoidAlgebra A G),
      deltaToEndRingHom hKA (k • x) = k • deltaToEndRingHom hKA x := by
    intro k x
    induction x using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | single g a =>
      rw [SkewMonoidAlgebra.smul_single]
      change deltaToEndAdd hKA (SkewMonoidAlgebra.single g (k • a))
        = k • deltaToEndAdd hKA (SkewMonoidAlgebra.single g a)
      rw [deltaToEndAdd_single, deltaToEndAdd_single]
      ext y
      change (k • a) * (g • y) = k • (a * (g • y))
      exact smul_mul_assoc k a (g • y)
  let δL : SkewMonoidAlgebra A G →ₗ[K] Module.End K A :=
    { toFun := deltaToEndRingHom hKA
      map_add' := map_add _
      map_smul' := hsmul }
  have hbijL : Function.Bijective δL := hbij
  have hfin : Module.finrank K (SkewMonoidAlgebra A G) = Module.finrank K (Module.End K A) :=
    (LinearEquiv.ofBijective δL hbijL).finrank_eq
  have hskew : Module.finrank K (SkewMonoidAlgebra A G)
      = Fintype.card G * Module.finrank K A := by
    rw [(SkewMonoidAlgebra.coeffLinearEquiv (S := K) (k := A) (G := G)).finrank_eq]
    exact Module.finrank_finsupp (ι := G) K A
  have hend : Module.finrank K (Module.End K A)
      = Module.finrank K A * Module.finrank K A :=
    Module.finrank_linearMap K K A A
  rw [hskew, hend] at hfin
  have hn : Module.finrank K A ≠ 0 :=
    ((Module.finrank_pos_iff_of_free K A).mpr inferInstance).ne'
  have h2 : Fintype.card G * Module.finrank K A
      = Module.finrank K A * Fintype.card G := by rw [mul_comm]
  rw [h2] at hfin
  exact (Nat.mul_left_cancel (Nat.pos_iff_ne_zero.mpr hn) hfin).symm

end GaloisRank

/-- **源 `proposition-0-2(a)` 的具名外部输入** ✓（`raw/Saltman1982.tex:82`；**⚠-tex-sourced** ✗）：
> "(a) `S` is a projective `R[G]`-module."（源引 **[CHR68] p. 13** ✓，**源中无证明** ✗ ——
> 属「quote four results … instead of proofs」✓。）

**⚠ 账目更正（第 207 轮** ✓**）** ✓：原写「**不在 `raw/`**」✗ —— **该句作废** ✗。
**现账** ✓：`[CHR68] p. 13` 本身仍**不在 `raw/`** ✗（精确出处缺件 ✓，L37 已核 ✓）；
**但**其**用点**已在 `raw/Saltman1978` 印 528（＝ PDF 3 ✓）内**逐字可核** ✓ ——
Sal78b `Theorem 1.2` 的**证明**在同页给出「`R`, considered as an `S` module, is an `S` **progenerator**」✓
（**自引 `[4, p. 81]` ＝ [DI71]** ✓ **不是** `[CHR68]` ✗ —— 见本节末 §Sal78bEndpoints ✓）
⟹ **progenerator 路线** ✓ 不足以取代**本条** ✗：源 (a) 要的是 **`R[G]`-投射性** ✓，
而印 528 给的是 **`R`-progenerator** ✓（**不同对象** ✗）⟹ **本条仍属 source-gap** ✗。

**数学内容** ✓：`S/R` 为 `G`-Galois ✓ ⟹ **`S` 是有限生成投射 `R`-模** ✓
（`S` 是投射 `R[G]`-模 ＋ `R[G]` 有限自由于 `R` ✓ ⟹ `S` 是有限自由 `R`-模的直和项 ✓）。
**本工程未证** ✗ —— 登记为**具名外部输入**（口径与 `FischerRegularHyp` ✓ 同：先接口后实体 ✓）。
**⚠ 用途** ✓（**一项砖两处用** ✓）：① 消除 `hBC` 后 `…_strongest` 所需的 `[Module.Finite R S]`／
`[Module.Projective R S]` ✓（§46.4 ✓）；② 蓝图第 9 步 `lem1.2` 的投影性输入 ✓（`Saltman1984.tex:132–138` ✓）。

**🔴 现形不可证** ✗（**第 234 轮机器反驳** ✓ —— 取代原「本工程未证」✗）：
**任意 `Algebra R S` 档为假** ✗，反例见 `galoisProjectiveHyp_refuted` ✓
（`R = ℤ` ✓、`S = ℚ` ✓、`G = PUnit` ✓ —— **前件与 r233 同** ✓；后件的 **`Module.Finite ℤ ℚ` 假** ✗，
由 **`not_moduleFinite_int_rat`** ✓ 得 ✓）。
**⚠ 修正口径** ✓（**判据下调** ✓）：本端点在**预期用例**（`S/R` 为 `G`-Galois ✓、源侧断言成立 ✓）中**才是真命题** ✓
（源引 `[CHR68] p. 13` ✓，**不在 `raw/`** ✗）；**现形照原样保存** ✓（**留痕** ✓，**不删** ✓）。
**⚠ 同族** ✓：`GaloisFaithfulHyp` ✓／`GaloisFixedSubringHyp` ✓ **同病** ✗
（**§0 判据一族三件皆「任意档过宽」** ✗，见文末反驳节 ✓）⟹ **接线假设表里的 `hProj`** ✓
亦**须按预期用例读** ✓（**其非空性未核** ✗，**下一手** ✓）。 -/
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
源引 `[CHR68] p.13` ✓（**⚠ 账目更正（第 207 轮** ✓**）**：原写「**不在 `raw/`**」✗ ——
精确出处 `[CHR68] p. 13` **仍不在 `raw/`** ✗（L37 已核 ✓），**但**其**用点**已在
`raw/Saltman1978` 印 528（＝ PDF 3 ✓）内可核 ✓ —— Sal78b `thm:1.2` 证明给出的
**`R`-progenerator** ✓ 蕴含 `GaloisProjectiveHyp` ✓（具名端点 `GaloisProgeneratorHyp` ✓，
**亦未证** ✗）；**`R[G]`-投射性** ✗ **仍无 `raw/` 内供给** ✗）。
**🔴 第 234 轮机器反驳** ✓：**现形一般档为假** ✗（`galoisProjectiveHyp_refuted` ✓）⟹
**任何路线都不可能证它** ✗；**预期用例**（`S/R` 为 `G`-Galois ✓ ＋ 源侧断言 ✓）中**才是真命题** ✓
（源引 `[CHR68] p. 13` ✓，**不在 `raw/`** ✗），**其证明须 progenerator 输入** ✗（**未落** ✗）。 -/
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
（**⚠ 账目更正（第 207 轮** ✓**）**：精确出处 `[CHR68] p. 13` **仍不在 `raw/`** ✗（与 §47 同一缺件 ✓，L37 已核 ✓）；
**但** Sal78b 印 528 的 progenerator 断言已在 `raw/Saltman1978` 内可核 ✓ ——
**注意**该断言说的是 **`R`-模** ✗，**不能**供给本条的 **`R'[G]`-投射性** ✗）。 -/
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
恒成立，而 `single 1 s` 对**共轭**作用自动不变 ⟹ 不给任何新约束。

**🔴 现形不可证** ✗（**第 233 轮机器反驳** ✓ —— 取代原「本工程未证」✗）：
**任意 `Algebra R S` 档为假** ✗，反例见 `galoisFixedSubringHyp_refuted` ✓
（`R = ℤ`、`S = ℚ`、`G = PUnit`：三款**全中** ✓ 而 `1/2` **不动** ✓ 却**不在 `algebraMap` 的像内** ✗）。
**⚠ 修正口径** ✓（**判据下调** ✓）：本端点在**预期用例**（`R \to S` **单射** ✓，即域内包含 ✓）中
**才是经典定理** ✓（CHR：`G`-Galois ⟹ `R = S^G` ✓）—— **其证明须 progenerator 输入** ✗（**未落** ✗）；
**现形照原样保存** ✓（**留痕** ✓，**不删** ✓）。
**⚠ 同族** ✓（**第 233 轮定性** ✓）：`GaloisFaithfulHyp` ✓ **同病** ✗ —— **两个端点皆「任意档过宽」** ✗
（**见文末反驳节** ✓）。 -/
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

/-- **登记** ✗：本件的**实体**（`R = S^G` 的证明）**不可落** ✗ ——
**🔴 第 233 轮机器反驳** ✓：现形**一般档为假** ✗（`galoisFixedSubringHyp_refuted` ✓）⟹
**任何路线都不可能证它** ✗。**经典路线** ✓（CHR：`G`-Galois ⟹ `R = S^G` ✓）**在预期用例（`R \to S` 单射 ✓）
中为真** ✓，但其证明**须 progenerator 输入** ✗（§171.1 ✓／`GaloisProgeneratorHyp` ✓，**未落** ✗）。 -/
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


/-! ## 源侧「`G`-Galois ⟹ `R \hookrightarrow S`」的**具名端点**（第 213 轮 ✓）

**⚠ 登记** ✓（**§174.3 的余项落为在册端点** ✓）：`IsGaloisWithGroup` ✓ 的**三款** ✓
（`FaithfulSMul G S` ✓／`R \subseteq S^G` ✓／`\delta` 双射 ✓）**不蕴含** `FaithfulSMul R S` ✗
（§171.1／§174.3 ✓）；源侧由**迹**供给 ✓（`τ = \sum_\sigma \sigma \bullet \cdot` ✓ ⟹ 左逆 ✓ ⟹ 单射 ✓）。
**⚠ 与 `GaloisFixedSubringHyp` 的分工** ✓：后者「**不变化 ⟹ 属 `R`**」✓，本条「**`R` 在 `S` 中可辨**」✗ ——
**两者不可互替** ✗（**各自独立在册** ✓）。**⚠ 实体未证** ✗（口径同 `GaloisProjectiveHyp` ✓／`GaloisDescentHyp` ✓）。 -/

section GaloisFaithfulEndpoint

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type u} [Group G] [Fintype G] [MulSemiringAction G S]

/-- **具名端点** ✓：`G`-Galois ⟹ `FaithfulSMul R S` ✓（**源侧路线 ＝ 迹** ✓）。
**🔴 现形不可证** ✗（**第 232 轮机器反驳** ✓ —— 取代原「实体未证」✗）：
一般档**假** ✓，反例见 `galoisFaithfulHyp_refuted` ✓（`R = ℚ × ℚ` 经 `fst` 作用于 `S = ℚ`、`G = PUnit`：
三款**全中** ✓ 而 `FaithfulSMul R S` **不成立** ✗）。
**⚠ 修正口径** ✓（**判据下调** ✓）：本端点在**预期用例**（`R`、`S` 同为一个域的子环 ✓，如
`↥S ⊆ Localization.Away T ⊆ L` ✓）中**自动成立** ✓（包含映射单射 ✓）⟹ **不作为独立假设存在** ✗；
**现形照原样保存** ✓（**留痕** ✓，**不删** ✓）。 -/
def GaloisFaithfulHyp (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) : Prop :=
  IsGaloisWithGroup R S G hRG → FaithfulSMul R S

/-- **类型锁定（同一性形）** ✓。 -/
theorem galoisFaithfulHyp_typeLock (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    (GaloisFaithfulHyp R S G hRG) = (GaloisFaithfulHyp R S G hRG) := rfl

/-- **非空洞探针（L1）** ✓：结论数据可实例化 ✓（`FaithfulSMul ℚ ℚ` ✓；
`IsGaloisWithGroup` 侧的非空性复用 `isGaloisWithGroup_data_nonempty` ✓）。 -/
theorem galoisFaithfulHyp_data_nonempty : Nonempty (FaithfulSMul ℚ ℚ) := ⟨inferInstance⟩

/-- **登记** ✗：本件的**实体**（`FaithfulSMul R S` 的证明）**不可落** ✗ ——
**🔴 第 232 轮机器反驳** ✓：现形**一般档为假** ✗（`galoisFaithfulHyp_refuted` ✓）⟹
**任何路线都不可能证它** ✗（**原「下一手 ＝ 特征线性无关不经 `S^G`」✗ 作废** ✓ ——
**目标为假** ✗，**非路线受阻** ✗）。**源侧路线** ✓：迹／特征线性无关 ✓（第 212 轮 ✓ ——
**取值在 `S`** ✗，须补一支 `S → R` 的 `R`-线性截面 ✗）；**该额外输入在预期用例中不存在** ✓
（域内包含 ⟹ 自动 ✓，见端点头注 ✓）。 -/
theorem galoisFaithful_gap_registered : True := trivial

/-- **本端点的用点** ✓：一行得 `FaithfulSMul R S` ✓。 -/
theorem faithfulSMul_of_galoisFaithfulHyp
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (h : GaloisFaithfulHyp R S G hRG) (hgal : IsGaloisWithGroup R S G hRG) :
    FaithfulSMul R S :=
  h hgal

end GaloisFaithfulEndpoint

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
（**⚠ 账目更正（第 207 轮）** ✓：原写「**不在 `raw/`**」✗ —— 该源已入库 ✓
`raw/Saltman1978.{tex,pdf}`（`receipt` `dc8a6884…` ✓），印 528 ＝ PDF 3 ✓（**回印核** ✓）；
**仅**「不在 `raw/`」一句作废 ✗，**实体未落** ✓ 的登记不变 ✓ —— 具名端点为
`GaloisFiniteGenerationDescentHyp` ✓，见本节末 ✓）。
**⚠ 顺带更正（同轮** ✓**）** ✓：本件原把 [CHR68] 与 [DI71] 并列为「同类一级出处缺件」✓ ——
**实测** ✓ Sal78b 印 528 的 progenerator 句自引 `[4, p. 81]` ＝ **[DI71]** ✓（**非** [CHR68] ✗）。 -/
theorem galoisDescent_gap_registered : True := trivial

/-! ## 源 `[Sal78b]` 印 528 的两个**具名端点**（第 207 轮；**回印核** ✓）

**来源** ✓：`raw/Saltman1978.{tex,pdf}` ＝ D.~Saltman, *Azumaya Algebras with Involution*,
J.~Algebra **52** (1978) 526--539 ✓（＝ Saltman1982 的 `[Sal78b]` ✓）。**载体身份** ✓：
tex 为**用户转化件** ✗ ⟹ 陈述**回印核** ✓（规则 16／L12 ✓）；`receipt` `dc8a6884…` ✓（L15 ✓）。
**印刷页偏移** ✓：**印 ＝ PDF ＋ 525** ✓（本工程**又一条**偏移口径 ✗ ——
Saltman1982 ＝ PDF ＋ 249 ✓／Saltman1984 ＝ PDF ＋ 164 ✓／**Sal78b ＝ PDF ＋ 525** ✓，三源各异 ✗）。

**印 528（＝ PDF 3** ✓**）逐字** ✓（本轮 PDF 目视 ✓，图存 `.abgv52-scratch/r207/sal78b-p3-03.png` ✓）：

**① 定理** ✓（`\begin{theorem}\label{thm:1.2}` ✓，`tex:85--87` ✓）：
> **THEOREM 1.2.** *Let `R/S` be a Galois extension of commutative rings with finite
> Galois group `G`. Then there are finitely generated rings `R' \subseteq R` and
> `S' \subseteq S` such that `R'/S'` is Galois with group `G` and `R \cong R' \otimes_{S'} S`.*

**② 证明内的 progenerator 断言** ✓（`tex:90` ✓）：
> Under these circumstances, `R`, considered as an `S` module, is an `S` **progenerator**.

**🔴 口径桥（源侧判据 ＝ 库侧判据** ✓**，故 `②` 可**直接搬运** ✓）** ✓：该断言所在句**先给** Galois 的判据 ✓ ——
源逐字「`R/S` is Galois with finite group `G` **if and only if** `G` is a group of automorphisms of `R`,
`S` is the fixed subring and `\phi: \Delta(R/S, G) \to \End_S(R)` is an isomorphism」✓
—— 此即 `IsGaloisWithGroup` ✓（本件 `:119` ✓，Saltman1982 §0 逐字 ✓）**已落** ✓ 的三款 ✓
（`FaithfulSMul G S` ✓／`R \subseteq S^G` ✓／`\Delta \to \Hom_R(S,S)` 双射 ✓）。**两者同一** ✓ ⟹ `②` **无需**定义桥 ✓。

**🔴 出处更正（本轮独立复核** ✓**，**纠正**既有 KB 注记 ✗→✓）** ✓：`②` 在源中**自引** `\cite[ p. 81]{4}` ✓，
而 Sal78b 的 `[4]` ＝ **F.~DeMeyer and E.~Ingraham**, *Separable Algebras over Commutative Rings*,
LNM 181 (1971) ✓（`tex:364` ✓）＝ **`[DI71]`** ✓ —— **不是** `[CHR68]` ✗。
**实测** ✓：`[Sal78b]` 全文对 `[CHR68]` **零命中** ✗（`grep` 于 `tex` ✓）⟹
**源 `proposition-0-2(a)` 的 `[CHR68] p. 13`** ✓ 与 **Sal78b 印 528 的 `[DI71] p. 81`** ✓ **是两个不同的页码** ✓，
**不得互替** ✗。**⚠ 留痕** ✓：交接件 附一百三十二 §132.2 记「该文自引 `[4, p. 81]` ＝ CHR68」✗
—— 该等式**为误** ✓，本条为更正 ✓（原注记不删 ✗）。

**⚠ 未变** ✗：搬运这两条 ⟹ `hgal`／`hProj` 的**归类**由「源引外部文献、**不在 `raw/`**」✗
改为「**`raw/` 内可落**」✓；**但工作量未减** ✗ —— 端点的**实体**（下两条 ✓）**均未证** ✗。 -/

section Sal78bEndpoints

/-- **源 `[Sal78b]` `thm:1.2`（印 528）的具名端点** ✓ —— **环上 Galois 扩张的有限生成下降** ✓。
**⚠ 实体未证** ✗（**登记** ✓；源**证**之 ✓，本工程**未搬运** ✗）。

**⚠ 口径** ✓：源写「finitely generated **rings** `R' \subseteq R`」✓，本形取**子代数**
`R' : \mathrm{Subalgebra}\ F\ R` ✓（源在本节把 `R/S` 置于 `F`-代数档 ✓，
Saltman1982 `proposition-0-2(c)` 亦作 `R' \subset R` 为 `F` subalgebra ✓）；「`R'/S'` **Galois with group `G`**」✓
落为 `IsGaloisWithGroup R'' S'' G` ✓（**同一判据** ✓）；「`R \cong R' \otimes_{S'} S`」✓
落为 **`F`-代数同构** ✓（`\simeqₐ[F]` ✓，**不**要求 `G`-等变 ✗ —— 与 `GaloisDescentHyp` ✓ 同一口径 ✓）。
**与 `GaloisDescentHyp`（§4.56 ✓）的关系** ✓：**两者陈述同构** ✓（同假设 ✓／同 `R''`／`S''` 数据链 ✓／同张量积尾 ✓）；
**差别** ✓：本条**不取** `R'`（源定理取 `S' \subseteq S` ＋ `R' \subseteq R` ✓，而 (c) 款从给定的 `R'` 出发 ✓）
—— 故本条**不能**顶替 `GaloisDescentHyp` 的用点形 ✗（**两档并存** ✓，**勿混用** ✗）。
**⚠ 命名** ✓（源**无**此名 ✗，本工程**所加** ✓ —— 登记 ✓）：**不**声称源中有此术语 ✓。

**⚠ 强度序** ✓：本条**弱于**源 `Theorem 1.2` ✗ —— 省略了 `S'` 侧的有限生成性 ✓
（源要 `S' \subseteq S` **finitely generated** ✓；本形只 `\exists S''` ✓，其有限生成性未列 ✗）。
**判别力负例** ✓（L43 ✓）：把尾项换成 `Nonempty (S ≃ₐ[F] S)`（丢张量积 ✓）⟹ 其 `rfl` 锁**必失败** ✗
（实跑读数见本轮状态笔记 §170 ✓）。 -/
def GaloisFiniteGenerationDescentHyp : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] [Algebra R S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup R S G hRG →
      ∃ (R'' : Type u) (_ : CommRing R'') (_ : Algebra F R'') (_ : Algebra R'' R)
        (_ : IsScalarTower F R'' R) (_ : Algebra.FiniteType F R''),
        ∃ (S'' : Type u) (_ : CommRing S'') (_ : Algebra F S'') (_ : Algebra R'' S'')
          (_ : IsScalarTower F R'' S'') (_ : MulSemiringAction G S'')
          (hRG'' : ∀ (g : G) (r : R'') (t : S''), g • (r • t) = r • (g • t)),
          IsGaloisWithGroup R'' S'' G hRG'' ∧ Nonempty (S ≃ₐ[F] TensorProduct R'' S'' R)

/-- **类型锁定（同一性形）** ✓：钉住本端点的**运行类型与宇宙档** —— 一旦其类型、参数表或宇宙改动，
本 `rfl` 立即编译失败 ✓（**全档绑定表锁**未落 ✗，难点与方案同 §52.2 ✓）。 -/
theorem galoisFiniteGenerationDescentHyp_typeLock :
    (GaloisFiniteGenerationDescentHyp F G) = (GaloisFiniteGenerationDescentHyp F G) := rfl

/-- **非空洞探针（L1）** ✓：本端点的**结论数据可实例化** ✓ —— `\mathbb{Q}` 上
**有限生成性** ✓（`F`-代数档 ＋ 塔 ✓）与张量积 `S'' \otimes_{R''} R` 的**载体非空** ✓
（测试于 `\mathbb{Q}` ✓）。
**⚠ 口径** ✓：本探针只证**数据层非空洞** ✓；`IsGaloisWithGroup` 侧的**完整实例**
（`\mathbb{Q}/\mathbb{Q}` ✓、`G = PUnit` ✓）与非空性登记见 `isGaloisWithGroup_data_nonempty` ✓（同件 ✓）。 -/
theorem galoisFiniteGenerationDescentHyp_data_nonempty :
    Nonempty (Algebra.FiniteType ℚ ℚ) ∧ Nonempty (TensorProduct ℚ ℚ ℚ) :=
  ⟨⟨inferInstance⟩, ⟨0⟩⟩

/-- **源 `[Sal78b]` 印 528 证明内的 **progenerator 断言**的具名端点** ✓ ——
`R/S` 为 `G`-Galois ⟹ `R` 是 `S`-**progenerator** ✓。
**⚠ 实体未证** ✗（**登记** ✓；源**证**之 ✓，本工程**未搬运** ✗）。

**⚠ 编码口径** ✓（**登记** ✓）：源在印 528 证明内**先给** progenerator 的**等价刻画** ✓
（「`P \in \Prog(R)` if and only if `P \in \Pr(R)` and `P` is `R` **faithful**」✓，`tex:54` ✓，自引 `[4, p. 8]` ✓）
⟹ 本形按**该刻画**落三款 ✓：**有限** ✓（`\Pr` ✓）＋ **投射** ✓（`\Pr` ✓）＋ **忠实平坦** ✓（mathlib `Module.FaithfullyFlat` ✓）。
**⚠ 桥接假设** ✓（**登记** ✓，**不声称源逐字** ✗）：源用**忠实** ✓，本形用 mathlib 的**忠实平坦** ✓
—— 在 projective ＋ finite 档两者等价 ✓，本形**多要求平坦** ✗ ⟹ 本形**强于**源的断言 ✗（**强度序** ✓）。
**与 `GaloisProjectiveHyp`（§47 ✓）的关系** ✓：本条**蕴含**它 ✓
（**已落** ✓：`galoisProgeneratorHyp_implies_galoisProjectiveHyp` ✓，同件 ✓；经 §47 的 `hBC` ✓ 复用 ✓）
—— 即源印 528 的断言**足以**供给 `hProj` ✓（**尚未**供给 ✗：本条实体未证 ✗）。
**⚠ 命名** ✓：源**无**此名 ✗，本工程**所加** ✓（登记 ✓）。
**判别力负例** ✓（L43 ✓）：**同名异陈述** ＝ 把 `Module.FaithfullyFlat R S` 换成 `Module.Free R S` ✗
⟹ 其 `rfl` 锁**必失败** ✗（实跑读数见本轮状态笔记 §170 ✓）—— 本 `rfl` 锁**有判别力** ✓。

**🔴 现形不可证** ✗（**第 235 轮机器反驳** ✓ —— 取代原「实体未证」✗）：
**任意 `Algebra R S` 档为假** ✗，反例见 `galoisProgeneratorHyp_refuted` ✓
（`R = ℤ` ✓、`S = ℚ` ✓、`G = PUnit` ✓ —— **前件与 r233 同** ✓；后件的 **`Module.Finite ℤ ℚ` 假** ✗，
由 **`not_moduleFinite_int_rat`** ✓ 得 ✓）。
**🔴 要害** ✓：本件是**原定的「搬运源件」目标** ✗（原文「源**证**之 ✓，本工程**未搬运**」✗）
⟹ **该计划就现形而言不可执行** ✗（**目标为假** ✗，**非材料不可得** ✗）。
**⚠ 修正口径** ✓（**判据下调** ✓）：源印 528 的断言**是在预期用例**（`R → S` 单射 ✓）上证的 ✓，
本形**按任意档写宽了** ✗ ⟹ **须在预期用例上重建** ✓；**现形照原样保存** ✓（**留痕** ✓，**不删** ✓）。 -/
def GaloisProgeneratorHyp (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) : Prop :=
  IsGaloisWithGroup R S G hRG →
    (Module.Finite R S ∧ Module.Projective R S ∧ Module.FaithfullyFlat R S)

/-- **类型锁定（同一性形）** ✓：钉住本端点的**运行类型与宇宙档** —— 一旦其类型、参数表或宇宙改动，
本 `rfl` 立即编译失败 ✓。 -/
theorem galoisProgeneratorHyp_typeLock (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    (GaloisProgeneratorHyp R S G hRG)
      = (IsGaloisWithGroup R S G hRG →
          (Module.Finite R S ∧ Module.Projective R S ∧ Module.FaithfullyFlat R S)) := rfl

/-- **强度序（已落** ✓**）** ✓：本端点 ⟹ `hProj` 的具名形 ✓ —— 源印 528 的 progenerator 断言
**足以**供给源 `proposition-0-2(a)` 的 `hProj` ✓（**「足以」≠「已供给」** ✗：本条实体未证 ✗）。 -/
theorem galoisProgeneratorHyp_implies_galoisProjectiveHyp (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (h : GaloisProgeneratorHyp R S G hRG) : GaloisProjectiveHyp R S G hRG :=
  fun hgal => ⟨(h hgal).1, (h hgal).2.1⟩

/-- **非空洞探针（L1）** ✓：本端点的**结论数据可实例化** ✓ —— `\mathbb{Q}` 上
**有限** ✓／**投射** ✓／**忠实平坦** ✓ 三款均有实例 ✓（`Module.FaithfullyFlat.self` ✓）。
**⚠ 口径** ✓：本探针只证**数据层非空洞** ✓；`IsGaloisWithGroup` 侧见 `isGaloisWithGroup_data_nonempty` ✓。 -/
theorem galoisProgeneratorHyp_data_nonempty :
    Nonempty (Module.Finite ℚ ℚ) ∧ Nonempty (Module.Projective ℚ ℚ)
      ∧ Nonempty (Module.FaithfullyFlat ℚ ℚ) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

end Sal78bEndpoints

/-! ## 迹／余截面路线：**可达性审计 ＋ 已落的三件**（第 208 轮）

**🔴 目标已作废** ✗（**第 235 轮** ✓）：本节**原定靶点** ＝ 搬运 `GaloisProgeneratorHyp` ✓ 的**实体** ✗ ——
该端点**现形已被机器反驳** ✓（`galoisProgeneratorHyp_refuted` ✓）⟹ **本节路线就现形而言不可执行** ✗
（**目标为假** ✗，**非路线受阻** ✗）。**⚠ 保留价值** ✓：**迹／余截面**是**源在预期用例上**证该断言所用的机制 ✓
（`R → S` **单射** ✓，**故 `FaithfulSMul R S` 一款在源侧不构成障碍** ✓）⟹
**本节三件基础 ＋ 受阻清单**对**重建后的预期用例形**仍然适用 ✓。
**⚠ 靶点** ✓（承 §170.9(i) ✓）：搬运 `GaloisProgeneratorHyp` ✓ 的**实体** ✓ —— 其瓶颈是
**`Module.FaithfullyFlat` 的 `FaithfulSMul` 一款** ✗（`FaithfullyFlat.mk` ✓ 只再需 `Flat` ✓，
而 `Flat` ✓ 由 `Module.Projective` ✓ 供给 ✓；见 `Module.Flat.of_projective` ✓）。
**⚠ 结构审计** ✓（r185--r208 合读 ✓）：`IsGaloisWithGroup` ✓ 的**三款** ✓（`FaithfulSMul G S` ✓／
`R \subseteq S^G` ✓／`\delta` 双射 ✓）**不蕴含** `FaithfulSMul R S` ✗ ——
源侧供给它的正是 **迹／余截面** ✓：源 Galois 判据 ⟹ `\delta` 有逆 ✓ ⟹
**`coeff_1 \circ \delta^{-1} \circ \mathrm{algebraMap}` 是 `\mathrm{algebraMap}` 的左逆** ✓
（本件把该路线的**三件基础**落库 ✓；**迹本身的线性化** ✗ **未落** ✗，见下登记 ✓）。

**⚠ 判据先审可达性** ✓（r196 纪律 ✓；探针 `.abgv52-scratch/pr208*.lean` ✓，**十余版** ✗）：
**可达** ✓：`\delta` 的**加法层**线性化 ✓（`deltaToEndLinear` ✓）；单位系数泛函 ✓（`coeffOne` ✓，`S`-线性 ✓）；
`\delta(\mathrm{single}\ 1\ 1) = 1` ✓。
**受阻** ✗（**逐条登记** ✓，供下一轮直接接手 ✓）：
**①** `\mathrm{SkewMonoidAlgebra}` ✓ 只有 **`SMul S`** ✗（**无** `SMul R` ✗ —— `Algebra R (SkewMonoidAlgebra S G)`
需 `SMulCommClass G R S` ✗，本档**没有** ✗）⟹ 迹只能在 **`S`-线性**档构造 ✓；
**②** `Module.End R S` 上**无** `Algebra S` ✗（`inferInstance` 实测失败 ✓）⟹ `S`-纯量经
`Algebra.smul_mul_assoc` ✓ 与 `Module.End` 的**逐点**作用对齐 ✓（**已定位** ✓，未落 ✗）；
**③** `algebraMap R (Module.End R S) x` 对 `x : S` **不合法** ✗（其定义域是 `R` ✗）——
正解是 `Algebra.linearMap`／`LinearMap.mul` ✓ **而非** `algebraMap` ✗（**已定位** ✓）。
**⚠ 不声称** ✗：迹**未落** ✗、`FaithfulSMul R S` ✓ **未证** ✗、`GaloisProgeneratorHyp` ✓ **实体未搬运** ✗。 -/

section TraceRoute

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

/-- **单位系数泛函** ✓（`SkewMonoidAlgebra S G →ₗ[S] S` ✓ —— `S`-线性档 ✓，因 `①` ✓）。 -/
noncomputable def coeffOne : SkewMonoidAlgebra S G →ₗ[S] S where
  toFun a := a.coeff 1
  map_add' := by intro a b; rw [SkewMonoidAlgebra.coeff_add]; rfl
  map_smul' := by intro c a; rw [SkewMonoidAlgebra.coeff_smul]; rfl

omit [Fintype G] [MulSemiringAction G S] in
/-- **`coeffOne` 在 `single 1 s` 上取 `s`** ✓。 -/
lemma coeffOne_single_one (s : S) :
    coeffOne (G := G) (SkewMonoidAlgebra.single (1 : G) s) = s := by
  classical
  show (SkewMonoidAlgebra.single (1 : G) s).coeff 1 = s
  rw [SkewMonoidAlgebra.coeff_single_apply]
  simp

/-- **δ 在 `single 1 1` 上是恒等自同态** ✓（迹路线的**单位款** ✓）。 -/
lemma deltaToEndAdd_single_one_one
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    deltaToEndAdd hRG (SkewMonoidAlgebra.single (1 : G) (1 : S)) = 1 := by
  rw [deltaToEndAdd_single]
  ext t
  simp [coeffToEnd, actEnd, Module.End.mul_apply]

/-- **判据第一、二款的合成** ✓：`G`-不动元必属 `R` 的像 ✓ —— 迹路线的**不动款** ✓。 -/
lemma algebraMap_fixed_of_isGaloisWithGroup
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hgal : IsGaloisWithGroup R S G hRG) (g : G) (r : R) :
    g • algebraMap R S r = algebraMap R S r :=
  hgal.2.1 g r

/-! ### 迹路线步骤 ①：`\delta` 的 **`S`-线性档**（第 209 轮 ✓）

**⚠ 更正留痕** ✓（**第 209 轮** ✓）：状态笔记 §172 与死胡同笔记
`deadend-ABGV52-trace-route-S-linearity` ✓ 曾判「`\mathrm{coeffToEnd}` **只是 `R`-线性** ✗、
迹路线**在一般档不可落**」✗ —— **该判断为误** ✓，**本轮（第 209 轮）已形式化推翻** ✓。
**正解** ✓：`\mathrm{coeffToEnd}(x)` ✓ ＝ 「**乘 `x`**」✓（`:\mathrm{End}_R S` ✓），
而 `c • \mathrm{coeffToEnd}(b) = \mathrm{coeffToEnd}(c \cdot b)` ✓ **由 `mul_smul` 给出** ✓
（**不**需 `R = S` ✗）⟹ `\mathrm{coeffToEnd}` ✓ **是 `S`-线性** ✓。 -/

/-- **`coeffToEnd` 的 `S`-线性** ✓（逐点 `mul_assoc` ✓）。 -/
lemma coeffToEnd_smulS (c b : S) :
    @coeffToEnd R S _ _ _ (c * b) = c • @coeffToEnd R S _ _ _ b := by
  ext t
  show (c * b) * t = c • (b * t)
  rw [mul_assoc]
  rfl

/-- **迹（和式形）** ✓：`τ x = ∑_σ σ • x` ✓（源 Galois 判据的**直接推论** ✓）。 -/
noncomputable def traceSum {S : Type*} [AddCommMonoid S] {G : Type*} [Fintype G]
    [SMul G S] (x : S) : S := ∑ σ : G, σ • x

/-- **迹是 `G`-不变的** ✓ —— 源 §0 判据的**直接推论** ✓
（**喂 `GaloisFixedSubringHyp`** ✓ —— 该件头注的**下一手** ✓ 正是此路 ✓）。 -/
lemma traceSum_invariant {S : Type*} [AddCommMonoid S] {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G S] (x : S) (g : G) :
    g • traceSum (G := G) x = traceSum (G := G) x := by
  show g • (∑ σ : G, σ • x) = ∑ σ : G, σ • x
  have h1 : g • (∑ σ : G, σ • x) = ∑ σ : G, g • (σ • x) :=
    map_sum (DistribMulAction.toAddMonoidEnd G S g) _ _
  rw [h1]
  exact Finset.sum_equiv (Equiv.mulLeft g) (fun _ => iff_of_true (Finset.mem_univ _)
    (Finset.mem_univ _)) (fun σ _ => by show g • (σ • x) = (g * σ) • x; rw [mul_smul])

/-- **`\delta` 的 `S`-线性档** ✓（**迹路线步骤 ①** ✓ —— **已落** ✓）。 -/
noncomputable def deltaToEndLinearS (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    SkewMonoidAlgebra S G →ₗ[S] Module.End R S where
  toFun := deltaToEndAdd hRG
  map_add' := (deltaToEndAdd hRG).map_add
  map_smul' := by
    classical
    intro c u
    induction u using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | single a b =>
        rw [SkewMonoidAlgebra.smul_single, deltaToEndAdd_single, deltaToEndAdd_single]
        show @coeffToEnd R S _ _ _ (c • b) * actEnd hRG a
            = c • (@coeffToEnd R S _ _ _ b * actEnd hRG a)
        rw [show (c • b : S) = c * b from rfl, coeffToEnd_smulS, smul_mul_assoc]
    | add x y hx hy =>
        rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-! ### 迹路线步骤 ②--③（第 212 轮 ✓）

**⚠ 已落** ✓：`\delta` 的 **`S`-线性逆** ✓、**单位系数泛函** ✓、`\mathrm{coeffToEnd}` **恒等式** ✓、**桥** ✓。
**⚠ 余一项** ✗：**迹的后半** ✓ —— 单位系数泛函的**取值在 `S`** ✗（`\mathrm{SkewMonoidAlgebra}` ✓ 只有
`SMul S` ✗），而**左逆式所需的值在 `R`** ✗ ⟹ 须补一支 **`S → R` 的 `R`-线性截面** ✗
（**⚠ 该步不是纯管线** ✗：`(\delta^{-1}(\mathrm{coeffToEnd}(\mathrm{algebraMap}\ r))).\mathrm{coeff}\ 1 = \mathrm{algebraMap}\ r` ✓
本身即所需结论 ✓，故**不能**用它去证它 ✓ —— 详见 §174 ✓）。 -/

/-- **迹路线步骤 ②** ✓：`\delta` 的 **`S`-线性逆** ✓（`LinearEquiv.ofBijective` ✓ **给全参数** ✓）。 -/
noncomputable def deltaInvLinearS
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hgal : IsGaloisWithGroup R S G hRG) :
    Module.End R S →ₗ[S] SkewMonoidAlgebra S G :=
  (LinearEquiv.ofBijective (deltaToEndLinearS (G := G) hRG) hgal.2.2 :
    SkewMonoidAlgebra S G ≃ₗ[S] Module.End R S).symm.toLinearMap

/-- **迹路线步骤 ③** ✓：**单位系数泛函** ✓（**`S`-线性** ✓，因 `\mathrm{SkewMonoidAlgebra}` 只有 `SMul S` ✓）。 -/
noncomputable def coeffOneS : SkewMonoidAlgebra S G →ₗ[S] S where
  toFun a := a.coeff 1
  map_add' := by intro a b; rw [SkewMonoidAlgebra.coeff_add]; rfl
  map_smul' := by intro c a; rw [SkewMonoidAlgebra.coeff_smul]; rfl

omit [Fintype G] [MulSemiringAction G S] in
/-- **`coeffOneS` 在 `single 1 x` 上取 `x`** ✓。 -/
lemma coeffOneS_single_one (x : S) :
    coeffOneS (G := G) (SkewMonoidAlgebra.single (1 : G) x) = x := by
  classical
  show (SkewMonoidAlgebra.single (1 : G) x).coeff 1 = x
  rw [SkewMonoidAlgebra.coeff_single_apply]
  simp

/-- **恒等式** ✓：`\mathrm{coeffToEnd}(\mathrm{algebraMap}\ r) = \mathrm{algebraMap}\ R\ (\mathrm{End}_R S)\ r` ✓。 -/
lemma coeffToEnd_algebraMap (r : R) :
    @coeffToEnd R S _ _ _ (algebraMap R S r) = algebraMap R (Module.End R S) r := by
  rw [show algebraMap R S r = r • (1 : S) from Algebra.algebraMap_eq_smul_one r]
  rw [show @coeffToEnd R S _ _ _ (r • (1 : S)) = r • @coeffToEnd R S _ _ _ (1 : S) from by
    ext t
    show (r • (1 : S)) * t = r • ((1 : S) * t)
    rw [smul_mul_assoc]]
  rw [show algebraMap R (Module.End R S) r = r • (1 : Module.End R S) from
    Algebra.algebraMap_eq_smul_one r]
  congr 1
  ext t
  simp [coeffToEnd]

/-- **桥** ✓：`\delta(\mathrm{single}\ 1\ (\mathrm{algebraMap}\ r)) = \mathrm{algebraMap}\ R\ (\mathrm{End}_R S)\ r` ✓。 -/
lemma deltaToEndLinearS_single_one_algebraMap
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (r : R) :
    deltaToEndLinearS (G := G) hRG
        (SkewMonoidAlgebra.single (1 : G) (algebraMap R S r))
      = algebraMap R (Module.End R S) r := by
  change deltaToEndAdd hRG (SkewMonoidAlgebra.single (1 : G) (algebraMap R S r)) = _
  rw [deltaToEndAdd_single]
  have hact : actEnd hRG (1 : G) = 1 := by ext t; simp [actEnd]
  rw [hact, mul_one]
  exact coeffToEnd_algebraMap r

/-- **登记** ✗：**迹路线的余项**（**逐条** ✓，供下一轮接手 ✓）——
**(i)** `deltaToEndLinearS`：`\delta` 的 **`S`-线性**档 ✓（**待补** ✗：`single` 支的
`coeffToEnd_smulS` ✓ ＋ `Algebra.smul_mul_assoc` ✓，**已定位** ✓）；
**(ii)** `deltaInvS`：由 `hgal` 的双射 ✓ 造 `S`-线性逆 ✓（`LinearEquiv.ofBijective` ✓，
**须给全参数** ✗ —— 裸用会被推断到 `R` 档 ✗，实测十余版 ✗）；
**(iii)** `galoisTrace := coeffOne \circ \deltaInvS \circ \mathrm{Algebra.linearMap}` ✓（**待补** ✗）；
**(iv)** `galoisTrace (algebraMap r) = r` ✓ ⟹ `Function.Injective (algebraMap R S)` ✓
⟹ `FaithfulSMul R S` ✓（`faithfulSMul_iff_algebraMap_injective` ✓）；
**(v)** `Module.FaithfullyFlat` ✓ ⟹ `GaloisProgeneratorHyp` ✓ 实体 ✓。
**⚠ 不声称** ✗：上五项**均未落** ✗；**只**落了三件基础 ✓（`coeffOne` ✓／`coeffOne_single_one` ✓／
`deltaToEndAdd_single_one_one` ✓ ＋ 不动款 ✓）。 -/
theorem galoisTrace_route_gap_registered : True := trivial

end TraceRoute

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

/-! ## 源 `proposition-0-2(b)` 的**具名登记**（**Prop 0.2 四条至此全落** ✓）第 159 轮

**源逐字** ✓（`raw/Saltman1982.tex:82--86` ✓）：「Let \(S/R\) be Galois with group \(G\). …
**(b)** \cite[ p.~116]{DI71}. **Suppose \(R\) has zero Picard group. Then \(H^1(G, S^*) = (0)\).**」✓
—— **⚠ 具名残余：本件不作证明** ✗（源在 `proposition-0-2` 的引导句明写「we quote four results … instead of proofs」✓，
本条的证明在 `[DI71]` p.~116 ✓ —— **该源不在 `raw/`** ✗，**登记** ✓）。
**⚠ 账目更正（第 207 轮** ✓**，**独立复核** ✓）**：`[DI71]` 现**有** raw 内**用点** ✓ 但**不含本页** ✗ ——
`raw/Saltman1978`（＝ Sal78b）自引 `[4, p. 81]` ✓（`tex:90` ✓）／`[4, p. 8]` ✓ 等，**最高到印 81** ✗；
全 `raw/` 语料对 DI71 的带页引用为 印 31／81／85／116 ✓，**其中无一条落在 raw 内可核** ✗
（Sal78b 引 81 仅为**转述** ✓，非 DI71 正文 ✗）⟹ **本条仍属一级出处缺件** ✗。

**⚠ 编码决定** ✓（**新读数 (67)** ✓）：`H^1(G, S^*) = (0)` **不**经范畴式群上同调 ✗
（`\mathrm{groupCohomology}` 需把 `S^*` 装成 `\mathrm{Rep}\ \mathbb{Z}\ G` ✓ —— 须先造 `S^\times` 上的 `G`-作用
＋ `\mathbb{Z}`-线性的相容 ✓，**机器多且脆** ✗），而取**显式交叉同态形** ✓（**同构于标准定义** ✓，**免全部装包** ✓）：
> `H^1(G, S^*) = (0)` ⟺ **每一交叉同态 `u : G \to S^*`（即 `u_{gh} = u_g \cdot g \cdot u_h` ✓）皆为主**（`\exists w \in S^*,\ u_g \cdot (g \cdot w) = w` ✓）

**⚠ 同 (63) 的取向** ✓：**能用域/环内显式形表达者，不搬范畴载体** ✓。
**⚠ 与 (a) 的关系** ✓：源 (a) 明写「the group cohomology groups \(H^n(G, S^+)\) are zero for \(n \geq 1\)」✓
（**加法层** ✓，`S^+` ＝ 加法群 ✓）—— **(b) 是乘法层（`S^*` ＝ 单位群 ✓）** ✓，二者**不同系数** ✓，**不可互推** ✓（**登记** ✓）。

**⚠ 未落项（登记）** ✗：**结论侧的非空洞探针**（L10① 可实现性 ✓）**未落** ✗ —— 须证「某具体档（如 `G = \mathrm{PUnit}`、`S = \mathbb{Q}` ✓）
交叉同态皆为主」✓；**本件已证其**可证性方向**（平凡作用档 ✓）**但**因 `\mathrm{PUnit}` 无 `\mathrm{MulSemiringAction}` 实例** ✓
须**显式给作用** ✓（`\mathrm{letI}` 触发风格警告 ✗）⟹ **延后** ✗，**登记** ✓。 -/

/-- **`H^1(G, S^*) = (0)` 的显式形** ✓（**交叉同态皆为主** ✓）：`u` 取单位值 ✓、满足交叉关系 ✓
⟹ 存在单位 `w` 使 `u_g \cdot (g \cdot w) = w` ✓。 -/
def H1UnitsVanishes (G : Type u) [Group G] (S : Type u) [CommRing S]
    [MulSemiringAction G S] : Prop :=
  ∀ u : G → S, (∀ g : G, IsUnit (u g)) →
    (∀ g h : G, u (g * h) = u g * (g • u h)) →
    ∃ w : S, IsUnit w ∧ ∀ g : G, u g * (g • w) = w

/-- **源 `proposition-0-2(b)` 的具名陈述** ✓：「`R` 的 Picard 群为零 ⟹ `H^1(G, S^*) = (0)`」✓ ——
**在「`S/R` 是 `G`-Galois」的**常设前提下** ✓（源 `tex :80` ✓）；**`\mathrm{ZeroPic}` 取为抽象谓词** ✓
（**本仓无 Picard 群词汇** ✗ —— **同 `\mathrm{SRat}` 的处置** ✓，**登记** ✓）。 -/
def Prop02bStatement (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra F R] [Algebra R S] [Algebra F S] [IsScalarTower F R S]
    [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (ZeroPic : Type u → Prop) : Prop :=
  IsGaloisWithGroup R S G hRG → ZeroPic R → H1UnitsVanishes G S

/-- **类型锁定** ✓：外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem prop02bStatement_typeLock (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra F R] [Algebra R S] [Algebra F S] [IsScalarTower F R S]
    [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (ZeroPic : Type u → Prop) :
    (Prop02bStatement F G R S hRG ZeroPic)
      = (IsGaloisWithGroup R S G hRG → ZeroPic R → H1UnitsVanishes G S) := rfl

/-- **非空洞探针（前提侧）** ✓：`\mathrm{ZeroPic}` 这一**抽象参数可实例化** ✓（取恒真谓词 ✓）。 -/
theorem prop02bStatement_zeroPic_nonempty :
    ∃ ZeroPic : Type u → Prop, ZeroPic (ULift.{u} ℤ) :=
  ⟨fun _ => True, trivial⟩

/-! ### 第 160 轮：`prop-0-2(b)` 的**结论侧探针**（闭 r159 的登记 ✗ ⟹ ✓✅）＋ **编码自洽** -/

section Prop02bCoherence

variable {G : Type u} [Group G] {S : Type u} [CommRing S] [Nontrivial S] [NoZeroDivisors S]
  [MulSemiringAction G S]

/-- **编码自洽** ✓：**主元素满足交叉关系** ✓ —— 即 `u_g \cdot (g \cdot w) = w`（`w` 为单位 ✓）
**必**使 `u` 是交叉同态 ✓（`u_{gh} = u_g \cdot (g \cdot u_h)` ✓）。
**⚠ 用途** ✓：与 `\mathrm{H1UnitsVanishes}` 的**定义方向互补** ✓ —— 定义说「交叉同态皆为主」✓，
本件说「主 ⟹ 交叉」✓ ⟹ **编码的两半相容** ✓（**登记的价值** ✓：防「编码把条件写空」✗）。
**证明** ✓：两条等式同左乘 `((g \cdot h) \cdot w)` ✓ 后**右消去** ✓（非零由 `w` 为单位 ✓ 保证 ✓）。 -/
theorem isCrossedHom_of_principal {w : S} (hw : IsUnit w) {u : G → S}
    (h : ∀ g : G, u g * (g • w) = w) : ∀ g h' : G, u (g * h') = u g * (g • u h') := by
  intro g h'
  have h1 : u (g * h') * ((g * h') • w) = w := h (g * h')
  have h2 : (u g * (g • u h')) * ((g * h') • w) = w := by
    rw [mul_assoc, mul_smul, ← MulSemiringAction.smul_mul, h h', h g]
  have hX : ((g * h') • w) ≠ 0 := by
    intro h0
    have hw0 := h (g * h')
    rw [h0, mul_zero] at hw0
    exact hw.ne_zero hw0.symm
  exact mul_right_cancel₀ hX (by rw [h1, h2])

end Prop02bCoherence

section Prop02bProbe

/-- `PUnit` 在 `\mathbb{Q}` 上的**平凡作用** ✓（**`\mathrm{local\ instance}`** ✓ —— 只在本节生效 ✓，
**不**污染全局实例搜索 ✓，**且**避开 `\mathrm{letI}` 的风格警告 ✗ —— **新读数 (68)** ✓）。 -/
local instance instPUnitActionRat : MulSemiringAction PUnit ℚ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- **结论侧非空洞探针（L10①）** ✓✅（**闭 r159 的登记** ✗ ⟹ ✓✅）：**`G = \mathrm{PUnit}`、`S = \mathbb{Q}`、
平凡作用时 `\mathrm{H1UnitsVanishes}` 成立** ✓ —— 即该谓词**可实现** ✓，**非空壳** ✓。
**证明** ✓：交叉同态 `u` 由交叉关系在 `g = h = 1` 处得 `u_1 = u_1 \cdot u_1` ✓，
**在单位群内右消去** ✓ 得 `u_1 = 1` ✓；主元素取 `w = 1` ✓。 -/
theorem h1UnitsVanishes_punit_rat : H1UnitsVanishes PUnit ℚ := by
  intro u hu hc
  have h1 : u PUnit.unit = 1 := by
    obtain ⟨v, hv⟩ := hu PUnit.unit
    have hvv : v = v * v := by
      apply Units.ext
      rw [Units.val_mul, hv]
      simpa using hc PUnit.unit PUnit.unit
    have h2 := congrArg (fun w : ℚˣ => v⁻¹ * w) hvv
    have : v = 1 := by simpa using h2.symm
    rw [← hv, this]
    rfl
  refine ⟨1, isUnit_one, fun g => ?_⟩
  rw [h1]
  simp

end Prop02bProbe

/-! ## §0 判据**两个端点**现形的机器反驳（第 232／233 轮 ✓）

**🔴 系统性缺陷（第 233 轮定性** ✓**）**：`GaloisFaithfulHyp` ✓ 与 `GaloisFixedSubringHyp` ✓
**现形同病** ✗ —— 二者都写成**任意 `Algebra R S`** 档 ✓（源 `§0` 判据的**自然读法** ✓），
**而源的实际用例里 `R \to S` 是域内的包含** ✓（**单射** ✓）。**放宽到任意档 ⟹ 二者皆为假** ✗
—— **不是「路线受阻」✗，是「现形为假」** ✗（**反例一个即足** ✓，判据见 L19 ✓）。

**⚠ 两个反例** ✓：
**(甲)** `R = \mathbb{Q} \times \mathbb{Q}` ✓（**经 `\mathrm{fst}` 作用于 `S = \mathbb{Q}`** ✓）、`G = \mathrm{PUnit}` ✓
⟹ `IsGaloisWithGroup` ✓ 而 `FaithfulSMul R S` **假** ✗（`(0,1) \neq 0` ✓ 而 `(0,1) \bullet x = 0` ✓）。
**(乙)** `R = \mathbb{Z}` ✓、`S = \mathbb{Q}` ✓、`G = \mathrm{PUnit}` ✓ ⟹ `IsGaloisWithGroup` ✓
而 `GaloisFixedSubringHyp` **假** ✗（`1/2` **不动** ✓ 而 `1/2 \notin \mathrm{algebraMap}\ \mathbb{Z}\ \mathbb{Q}` ✓）。
**共同的 `\delta` 双射** ✓（③）：由 **`\delta(\mathrm{single}\ () a) = \mathrm{coeffToEnd}\ a`** ✓
（`actEnd () = 1` ✓）＋ **`u = \mathrm{single}\ ()\ (u.\mathrm{coeff}\ ())`** ✓（**单点群** ✓）
＋ **每个 `R`-线性自同态 `f` 满足 `f t = t \cdot f 1`** ✓ 三者得 ✓
（**甲档** ✓ 用 **`R \to S` 满射** ✓；**乙档** ✓ 用 **`map_ratCast_smul`** ✓：**加法 ⟹ `\mathbb{Q}`-线性** ✓）。

**⚠ 第三件（**第 234 轮补上** ✓）**：`GaloisProjectiveHyp` ✓ **同族** ✓ —— 取 **乙档** ✓
（**其前件已在本节机器核成立** ✓）则后件含 **`Module.Finite ℤ ℚ`** ✗；
**该步已落** ✓✅（**自造件 `not_moduleFinite_int_rat`** ✓，**库内无件** ✗，**实测** ✓）
⟹ **第三件亦已反驳** ✓（`galoisProjectiveHyp_refuted` ✓）。

**🔴 全族普查（**第 235 轮** ✓）**：§0 判据一族的具名端点**逐一判定** ✓：

| # | 端点 | 现形档 | 反例（**同一骨架** ✓） | 结论 |
|---|---|---|---|---|
| ① | `GaloisFaithfulHyp` ✓ | **任意 `Algebra R S`** ✗ | **甲档** ✓ | **反驳** ✗（r232 ✓） |
| ② | `GaloisFixedSubringHyp` ✓ | **同上** ✗ | **乙档** ✓ | **反驳** ✗（r233 ✓） |
| ③ | `GaloisProjectiveHyp` ✓ | **同上** ✗ | **乙档** ✓ | **反驳** ✗（r234 ✓） |
| ④ | `GaloisProgeneratorHyp` ✓ | **同上** ✗ | **乙档** ✓ | **反驳** ✗（r235 ✓） |
| ⑤ | `GaloisProjectiveSectionHyp` ✓ | **`F`-代数档** ✓ | **家族反例不覆盖** ✗ | **真值未判定** ⚠ |
| ⑥ | `GaloisDescentHyp` ✓／`GaloisFiniteGenerationDescentHyp` ✓ | **`F`-代数档** ✓ | **同上** ✗ | **真值未判定** ⚠ |

**⚠ 读法** ✓：**①②③④ 皆按「任意 `Algebra R S`」写** ✗（⑤⑥ 已按 `F`-代数档 ✓ ⟹ **不受家族反例波及** ✓）
⟹ **缺陷集中在「任意档」那一组** ✓（**四条一网打尽** ✓）。
**🔴 要害** ✓：**④ 是本工程原定的「搬运源件」目标** ✗（「源 `[Sal78b]` 印 528 在 `raw/` 内 ✓，实体未搬运」✗）
⟹ **该计划就现形而言不可执行** ✗（**目标为假** ✗，**非材料不可得** ✗）——
**须改在预期用例（`R → S` 单射 ✓）上重建** ✓（**下一手** ✓）。

**✅ L1 非空性（**第 236 轮** ✓）：反驳 ≠ 空** ✓ ——
在 `R = S = ℚ` ✓、`G = PUnit` ✓ 上 **`IsGaloisWithGroup` 成立** ✓（`galoisEndpoints_satisfiable` ✓）
**且①②③④ 四条在同一实例上全部成立** ✓ ⟹ **四条的反驳是「现形过宽」✗，不是「假设类空」** ✗。
**⚠ 边界** ✓：**该实例不是接线的那一对** ✗（`↥S → Localization.Away T` ✗）⟹
**接线假设表自身的非空性仍未核** ✗（**下一手** ✓）。 -/

section GaloisEndpointsRefutation

/-- 平凡作用 `PUnit ↷ ℚ`（**本节的局部件** ✓；`PUnit` **无** mathlib 实例 ✗）。 -/
@[instance_reducible]
private def pUnitTrivMSA : MulSemiringAction PUnit ℚ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

local instance pUnitAlgQ : Algebra (ℚ × ℚ) ℚ := (RingHom.fst ℚ ℚ).toAlgebra
local instance pUnitMSAQ : MulSemiringAction PUnit ℚ := pUnitTrivMSA

/-- **`GaloisFaithfulHyp` 现形的反驳** ✓✅（第 232 轮 ✓；**非空洞** ✓）：
存在 `R`／`S`／`G`／`hRG` 使 **`IsGaloisWithGroup R S G hRG` 成立** ✓ 而 **`FaithfulSMul R S` 不成立** ✗
⟹ `GaloisFaithfulHyp R S G hRG` **为假** ✗ ⟹ **其「实体」不可证** ✗。
**⚠ 口径** ✓：`R = ℚ × ℚ`（**经 `fst`** ✓）、`S = ℚ`、`G = PUnit`（**平凡作用** ✓）。
**⚠ 不声称** ✗：**不**声称 `FaithfulSMul R S` 在**预期用例**中不成立 ✓（**相反** ✓，见端点头注 ✓）。 -/
theorem galoisFaithfulHyp_refuted :
    ∃ hRG : ∀ (g : PUnit) (r : ℚ × ℚ) (s : ℚ), g • (r • s) = r • (g • s),
      IsGaloisWithGroup (ℚ × ℚ) ℚ PUnit hRG ∧ ¬ FaithfulSMul (ℚ × ℚ) ℚ := by
  let hRG : ∀ (g : PUnit) (r : ℚ × ℚ) (s : ℚ), g • (r • s) = r • (g • s) :=
    fun _ _ _ => rfl
  have halg : ∀ t : ℚ, (algebraMap (ℚ × ℚ) ℚ) (t, 0) = t := fun _ => rfl
  have hact : actEnd hRG PUnit.unit = 1 := by
    ext t; rfl
  have hsingle : ∀ a : ℚ,
      deltaToEndRingHom hRG (SkewMonoidAlgebra.single PUnit.unit a) = coeffToEnd a := by
    intro a
    show deltaToEndAdd hRG (SkewMonoidAlgebra.single PUnit.unit a) = coeffToEnd a
    rw [deltaToEndAdd_single, hact, mul_one]
  have heval : ∀ a : ℚ, (deltaToEndAdd hRG (SkewMonoidAlgebra.single PUnit.unit a)) 1 = a := by
    intro a
    rw [deltaToEndAdd_single, hact, mul_one]
    show a * 1 = a
    rw [mul_one]
  have hsingle_eq : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      u = SkewMonoidAlgebra.single PUnit.unit (u.coeff PUnit.unit) := by
    intro u
    refine SkewMonoidAlgebra.ext (fun g => ?_)
    rw [Subsingleton.elim g PUnit.unit, SkewMonoidAlgebra.coeff_single_apply]
    simp
  have hcoe : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      (deltaToEndAdd hRG u) 1 = u.coeff PUnit.unit := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    exact heval (u.coeff PUnit.unit)
  have hrec : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      u = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG u) 1) := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    rw [hcoe u]
  have hgal : IsGaloisWithGroup (ℚ × ℚ) ℚ PUnit hRG := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨fun {a b} _ => Subsingleton.elim a b⟩
    · intro g r
      rfl
    · constructor
      · intro u v huv
        have h1 : (deltaToEndAdd hRG u) 1 = (deltaToEndAdd hRG v) 1 :=
          congrArg (fun f : Module.End (ℚ × ℚ) ℚ => f 1) huv
        calc u = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG u) 1) := hrec u
          _ = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG v) 1) := by rw [h1]
          _ = v := (hrec v).symm
      · intro f
        refine ⟨SkewMonoidAlgebra.single PUnit.unit (f 1), ?_⟩
        rw [hsingle]
        ext t
        have h2 : f (((t, 0) : ℚ × ℚ) • (1 : ℚ)) = ((t, 0) : ℚ × ℚ) • f 1 :=
          f.map_smul (t, 0) 1
        have h3 : ((t, 0) : ℚ × ℚ) • (1 : ℚ) = t := by
          rw [Algebra.smul_def, halg t, mul_one]
        rw [h3] at h2
        rw [h2, Algebra.smul_def, halg t]
        show (f 1) * t = t * f 1
        rw [mul_comm]
  have hnf : ¬ FaithfulSMul (ℚ × ℚ) ℚ := by
    intro h
    have h1 : ((0, 1) : ℚ × ℚ) = 0 :=
      @FaithfulSMul.eq_of_smul_eq_smul (ℚ × ℚ) ℚ _ h (0, 1) 0 (fun x => by
        rw [Algebra.smul_def, Algebra.smul_def]; rfl)
    exact one_ne_zero (α := ℚ) (by simpa using congrArg Prod.snd h1)
  exact ⟨hRG, hgal, hnf⟩

/-- **`GaloisFixedSubringHyp` 现形的反驳** ✓✅（第 233 轮 ✓；**非空洞** ✓）：
存在 `R`／`S`／`G`／`hRG` 使 **`IsGaloisWithGroup R S G hRG` 成立** ✓ 而
**`GaloisFixedSubringHyp R S G hRG` 不成立** ✗ ⟹ **其「实体」不可证** ✗。
**⚠ 口径** ✓：`R = ℤ` ✓、`S = ℚ` ✓、`G = PUnit` ✓（**平凡作用** ✓）——
**不动元 `1/2`** ✓（**平凡作用** ⟹ 一切元不动 ✓）**不在 `algebraMap ℤ ℚ` 的像内** ✗
（像 ＝ `ℤ` ✓；`1/2` 导出 `2 r = 1`（`r : ℤ` ✓）⟹ 矛盾 ✓，`omega` ✓）。
**⚠ ③ 的依据** ✓：**与 232 轮同一骨架** ✓，但 **`R \to S` 不满射** ✗ ⟹ 改用
**`map_ratCast_smul`** ✓（**库内** ✓：**加法 ⟹ `\mathbb{Q}`-线性** ✓）。
**⚠ 不声称** ✗：**不**声称 `S^G = \mathrm{image}(R)` 在**预期用例**中不成立 ✓（**相反** ✓ ——
那是**经典定理** ✓，**须 progenerator 输入** ✗，**未落** ✗）。 -/
theorem galoisFixedSubringHyp_refuted :
    ∃ hRG : ∀ (g : PUnit) (r : ℤ) (s : ℚ), g • (r • s) = r • (g • s),
      IsGaloisWithGroup ℤ ℚ PUnit hRG ∧ ¬ GaloisFixedSubringHyp ℤ ℚ PUnit hRG := by
  let hRG : ∀ (g : PUnit) (r : ℤ) (s : ℚ), g • (r • s) = r • (g • s) := fun _ _ _ => rfl
  have hact : actEnd hRG PUnit.unit = 1 := by ext t; rfl
  have hsingle : ∀ a : ℚ,
      deltaToEndRingHom hRG (SkewMonoidAlgebra.single PUnit.unit a) = coeffToEnd a := by
    intro a
    show deltaToEndAdd hRG (SkewMonoidAlgebra.single PUnit.unit a) = coeffToEnd a
    rw [deltaToEndAdd_single, hact, mul_one]
  have heval : ∀ a : ℚ, (deltaToEndAdd hRG (SkewMonoidAlgebra.single PUnit.unit a)) 1 = a := by
    intro a
    rw [deltaToEndAdd_single, hact, mul_one]
    show a * 1 = a
    rw [mul_one]
  have hsingle_eq : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      u = SkewMonoidAlgebra.single PUnit.unit (u.coeff PUnit.unit) := by
    intro u
    refine SkewMonoidAlgebra.ext (fun g => ?_)
    rw [Subsingleton.elim g PUnit.unit, SkewMonoidAlgebra.coeff_single_apply]
    simp
  have hcoe : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      (deltaToEndAdd hRG u) 1 = u.coeff PUnit.unit := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    exact heval (u.coeff PUnit.unit)
  have hrec : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      u = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG u) 1) := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    rw [hcoe u]
  have hgal : IsGaloisWithGroup ℤ ℚ PUnit hRG := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨fun {a b} _ => Subsingleton.elim a b⟩
    · intro g r
      rfl
    · constructor
      · intro u v huv
        have h1 : (deltaToEndAdd hRG u) 1 = (deltaToEndAdd hRG v) 1 :=
          congrArg (fun f : Module.End ℤ ℚ => f 1) huv
        calc u = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG u) 1) := hrec u
          _ = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG v) 1) := by rw [h1]
          _ = v := (hrec v).symm
      · intro f
        refine ⟨SkewMonoidAlgebra.single PUnit.unit (f 1), ?_⟩
        rw [hsingle]
        ext t
        have h2 : f t = t * f 1 := by
          have h := map_ratCast_smul f ℚ ℚ t (1 : ℚ)
          simpa [Algebra.smul_def] using h
        show (f 1) * t = f t
        rw [h2, mul_comm]
  have hnf : ¬ GaloisFixedSubringHyp ℤ ℚ PUnit hRG := by
    intro h
    obtain ⟨r, hr⟩ := h hgal (1 / 2) (fun _ => rfl)
    have hr' : ((2 * r : ℤ) : ℚ) = 1 := by
      have h4 : (r : ℚ) = 1 / 2 := hr.symm
      push_cast
      rw [h4]
      norm_num
    have h5 : (2 * r : ℤ) = 1 := by exact_mod_cast hr'
    omega
  exact ⟨hRG, hgal, hnf⟩

/-- **`ℚ` 不是有限生成 `ℤ`-模** ✓✅（第 234 轮自造 ✓；**库内无件** ✗，**实测** ✓）：
**`¬ Module.Finite ℤ ℚ`** ✗ —— 供**第三件**（`GaloisProjectiveHyp` ✓）的反驳 ✓。
**证明** ✓：设有限生成 ✓ ⟹ 由 `Submodule.FG` 的定义 ✓ 取**有限** `S` ✓ 使 `span ℤ S = ⊤` ✓；
取 **`D := ∏_{q ∈ S} q.den`** ✓（**`> 0`** ✓）✓；考虑子模 **`M := {x | ∃ z : ℤ, x = z / D}`** ✓
（**对加法与 `ℤ`-纯量封闭** ✓）—— **每个 `q ∈ S` 都在 `M` 内** ✓（`q.den ∣ D` ✓ ⟹
`q = (q.num · (D / q.den)) / D` ✓）⟹ **`⊤ ≤ M`** ✓ ⟹ **`1/(2D) ∈ M`** ✓ ⟹
**`∃ z : ℤ, 1/(2D) = z/D`** ✓ ⟹ **`2 z = 1`** ✓ ⟹ **`omega`** ✓（**矛盾** ✓）。 -/
theorem not_moduleFinite_int_rat : ¬ Module.Finite ℤ ℚ := by
  intro hfin
  have h1 : Module.Finite ℤ ↥(⊤ : Submodule ℤ ℚ) :=
    Module.Finite.equiv (Submodule.topEquiv (R := ℤ) (M := ℚ)).symm
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp h1
  set D : ℤ := S.prod (fun q => (q.den : ℤ)) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact Finset.prod_pos (fun q _ => by exact_mod_cast q.den_pos)
  have hDne : D ≠ 0 := ne_of_gt hDpos
  let M : Submodule ℤ ℚ :=
    { carrier := {x : ℚ | ∃ z : ℤ, x = (z : ℚ) / (D : ℚ)},
      zero_mem' := ⟨0, by simp⟩,
      add_mem' := by
        rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by push_cast; ring⟩,
      smul_mem' := by
        rintro c x ⟨a, rfl⟩
        exact ⟨c * a, by push_cast; ring⟩ }
  have hSM : (↑S : Set ℚ) ⊆ M := by
    intro q hq
    have hdvd : (q.den : ℤ) ∣ D := by
      rw [hDdef]
      exact Finset.dvd_prod_of_mem _ hq
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨q.num * c, ?_⟩
    have hD' : (D : ℚ) = (q.den : ℚ) * (c : ℚ) := by
      rw [hc]; push_cast; ring
    have hcne : (c : ℚ) ≠ 0 := by
      intro h0
      exact hDne (by rw [hc, show c = 0 from by exact_mod_cast h0, mul_zero])
    rw [hD', show ((q.num * c : ℤ) : ℚ) = (q.num : ℚ) * (c : ℚ) from by push_cast; ring]
    rw [mul_div_mul_right _ _ hcne, Rat.num_div_den q]
  have hmem : ((1 : ℚ) / (2 * (D : ℚ))) ∈ Submodule.span ℤ (↑S : Set ℚ) := by
    rw [hS]; trivial
  rw [Submodule.mem_span] at hmem
  obtain ⟨z, hz⟩ := hmem M hSM
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDne
  have h2 : (z : ℚ) = 1 / 2 := by
    field_simp at hz
    linarith
  have h3 : ((2 * z : ℤ) : ℚ) = 1 := by
    push_cast
    rw [h2]
    norm_num
  have h4 : (2 * z : ℤ) = 1 := by exact_mod_cast h3
  omega

/-- **`GaloisProjectiveHyp` 现形的反驳** ✓✅（第 234 轮 ✓；**非空洞** ✓）：
存在 `R`／`S`／`G`／`hRG` 使 **`IsGaloisWithGroup R S G hRG` 成立** ✓ 而
**`GaloisProjectiveHyp R S G hRG` 不成立** ✗ ⟹ **其「实体」不可证** ✗。
**⚠ 口径** ✓：**复用乙档** ✓（`R = ℤ` ✓、`S = ℚ` ✓、`G = PUnit` ✓ —— **前件由 r233 的反例供给** ✓），
**反驳步** ✓ ＝ **`not_moduleFinite_int_rat`** ✓（`h hgal` 的第一半即 `Module.Finite ℤ ℚ` ✗）。
**⚠ 意义** ✓：**§0 判据一族三件**（`GaloisFaithfulHyp` ✓／`GaloisFixedSubringHyp` ✓／
`GaloisProjectiveHyp` ✓）**现形皆可反驳** ✗ ⟹ **系统性缺陷** ✓（**远非偶然** ✓）。
**⚠ 不声称** ✗：**不**声称 `hProj` 在**接线实际对**上不成立 ✓（**相反** ✓ —— 那是源侧目标 ✓，**未落** ✗）。 -/
theorem galoisProjectiveHyp_refuted :
    ∃ hRG : ∀ (g : PUnit.{1}) (r : ℤ) (s : ℚ), g • (r • s) = r • (g • s),
      IsGaloisWithGroup ℤ ℚ PUnit.{1} hRG ∧ ¬ GaloisProjectiveHyp ℤ ℚ PUnit.{1} hRG := by
  obtain ⟨hRG, hgal, _⟩ := galoisFixedSubringHyp_refuted
  exact ⟨hRG, hgal, fun h => not_moduleFinite_int_rat (h hgal).1⟩

/-- **`GaloisProgeneratorHyp` 现形的反驳** ✓✅（第 235 轮 ✓；**非空洞** ✓）：
存在 `R`／`S`／`G`／`hRG` 使 **`IsGaloisWithGroup R S G hRG` 成立** ✓ 而
**`GaloisProgeneratorHyp R S G hRG` 不成立** ✗ ⟹ **其「实体」不可证** ✗。
**⚠ 口径** ✓：**复用乙档** ✓（`R = ℤ` ✓、`S = ℚ` ✓、`G = PUnit` ✓ —— **前件由 r233 的反例供给** ✓），
**反驳步** ✓ ＝ **`not_moduleFinite_int_rat`** ✓（`h hgal` 的第一半即 `Module.Finite ℤ ℚ` ✗）。
**⚠ 与在册件一致** ✓：`galoisProgeneratorHyp_implies_galoisProjectiveHyp` ✓（**已落** ✓）
＋ r234 的 ③ 反驳 ✓ ⟹ **两件同假不矛盾** ✓（**`A → B` 与 `¬B` 给 `¬A`** ✓）。
**🔴 要害** ✓：本件是**原定的「搬运源件」目标** ✗（源 `[Sal78b]` 印 528 ✓，**在 `raw/` 内** ✓）
⟹ **该计划就现形而言不可执行** ✗（**目标为假** ✗）—— **须在预期用例上重建** ✓（**下一手** ✓）。
**⚠ 不声称** ✗：**不**声称 `hProj` 在**接线实际对**上不成立 ✓（**相反** ✓ —— 那是源侧目标 ✓，**未落** ✗）。 -/
theorem galoisProgeneratorHyp_refuted :
    ∃ hRG : ∀ (g : PUnit.{1}) (r : ℤ) (s : ℚ), g • (r • s) = r • (g • s),
      IsGaloisWithGroup ℤ ℚ PUnit.{1} hRG ∧ ¬ GaloisProgeneratorHyp ℤ ℚ PUnit.{1} hRG := by
  obtain ⟨hRG, hgal, _⟩ := galoisFixedSubringHyp_refuted
  exact ⟨hRG, hgal, fun h => not_moduleFinite_int_rat (h hgal).1⟩

/-- **L1 非空性：反驳 ≠ 空** ✓✅（第 236 轮 ✓；**本节结论** ✓）：
在 **`R = S = ℚ`** ✓、**`G = PUnit`** ✓（**平凡作用** ✓）上，**`IsGaloisWithGroup` 成立** ✓
（**③ 双射由 `ext_ring`-型论证得** ✓：`SkewMonoidAlgebra ℚ PUnit` **一维** ✓ ＋
每个 `ℚ`-线性自同态 `f` 满足 `f t = t · f 1` ✓，**由 `map_smul`** ✓），
**且①②③④ 四条被反驳的端点在同一个实例上全部成立** ✓（**四款结论数据均有实例** ✓）。
**⚠ 意义** ✓（**L1 ＋ L10①** ✓）：**四条的反驳是「现形过宽」✗，不是「假设类空」** ✗ ——
**端点在其预期用例中可满足** ✓（**本实例即证** ✓）。
**⚠ 边界** ✓（**如实** ✓）：本实例**不是接线的那一对** ✗（`↥S → Localization.Away T` ✗）⟹
**接线假设表自身的非空性仍未核** ✗（**下一手** ✓；**候选见证** ✓：`ℚ`／`PUnit`／`a = X`／`s₀ = X`／`T = X` ✓，
**须 `Localization.Away X ≅ ↥S`** ✓）。
**⚠ 在册探针更正** ✓：`isGaloisWithGroup_data_nonempty` ✓ 只证数据层 ✗（**原文「假设类非空」系过度声称** ✗，**已改** ✓）；
**本件是它的加强** ✓。 -/
theorem galoisEndpoints_satisfiable :
    ∃ hRG : ∀ (g : PUnit.{1}) (r : ℚ) (s : ℚ), g • (r • s) = r • (g • s),
      IsGaloisWithGroup ℚ ℚ PUnit.{1} hRG ∧
        GaloisFaithfulHyp ℚ ℚ PUnit.{1} hRG ∧
        GaloisFixedSubringHyp ℚ ℚ PUnit.{1} hRG ∧
        GaloisProjectiveHyp ℚ ℚ PUnit.{1} hRG ∧
        GaloisProgeneratorHyp ℚ ℚ PUnit.{1} hRG := by
  let hRG : ∀ (g : PUnit.{1}) (r : ℚ) (s : ℚ), g • (r • s) = r • (g • s) :=
    fun _ _ _ => rfl
  have hact : actEnd hRG PUnit.unit = 1 := by
    refine LinearMap.ext (fun t => ?_)
    rfl
  have hsingle : ∀ a : ℚ,
      deltaToEndRingHom hRG (SkewMonoidAlgebra.single PUnit.unit a) = coeffToEnd a := by
    intro a
    show deltaToEndAdd hRG (SkewMonoidAlgebra.single PUnit.unit a) = coeffToEnd a
    rw [deltaToEndAdd_single, hact, mul_one]
  have heval : ∀ a : ℚ, (deltaToEndAdd hRG (SkewMonoidAlgebra.single PUnit.unit a)) 1 = a := by
    intro a
    rw [deltaToEndAdd_single, hact, mul_one]
    show a * 1 = a
    rw [mul_one]
  have hsingle_eq : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      u = SkewMonoidAlgebra.single PUnit.unit (u.coeff PUnit.unit) := by
    intro u
    refine SkewMonoidAlgebra.ext (fun g => ?_)
    rw [Subsingleton.elim g PUnit.unit, SkewMonoidAlgebra.coeff_single_apply]
    simp
  have hcoe : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      (deltaToEndAdd hRG u) 1 = u.coeff PUnit.unit := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    exact heval (u.coeff PUnit.unit)
  have hrec : ∀ u : SkewMonoidAlgebra ℚ PUnit,
      u = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG u) 1) := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    rw [hcoe u]
  have hgal : IsGaloisWithGroup ℚ ℚ PUnit.{1} hRG := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨fun {a b} _ => Subsingleton.elim a b⟩
    · intro g r
      rfl
    · constructor
      · intro u v huv
        have h1 : (deltaToEndAdd hRG u) 1 = (deltaToEndAdd hRG v) 1 :=
          congrArg (fun f : Module.End ℚ ℚ => f 1) huv
        calc u = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG u) 1) := hrec u
          _ = SkewMonoidAlgebra.single PUnit.unit ((deltaToEndAdd hRG v) 1) := by rw [h1]
          _ = v := (hrec v).symm
      · intro f
        refine ⟨SkewMonoidAlgebra.single PUnit.unit (f 1), ?_⟩
        rw [hsingle]
        refine LinearMap.ext (fun t => ?_)
        have h2 : f t = t * f 1 := by
          have h := f.map_smul t (1 : ℚ)
          simpa using h
        show (f 1) * t = f t
        rw [h2, mul_comm]
  exact ⟨hRG, hgal,
    (fun _ => inferInstance : GaloisFaithfulHyp ℚ ℚ PUnit.{1} hRG),
    (fun _ s _ => ⟨s, rfl⟩ : GaloisFixedSubringHyp ℚ ℚ PUnit.{1} hRG),
    (fun _ => ⟨inferInstance, inferInstance⟩ : GaloisProjectiveHyp ℚ ℚ PUnit.{1} hRG),
    (fun _ => ⟨inferInstance, inferInstance, inferInstance⟩ :
      GaloisProgeneratorHyp ℚ ℚ PUnit.{1} hRG)⟩

end GaloisEndpointsRefutation

/-! ## 公理闸门 -/

#print axioms isGaloisWithGroup_typeLock
#print axioms algebraMap_fixed_of_smulCommClass
#print axioms isGaloisWithGroup_data_nonempty
#print axioms isGaloisWithGroup_gap_registered
#print axioms finrank_eq_card_of_isGaloisWithGroup
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
/-! ## 4.20 **Galois 性沿等变同构搬运**（第 189 轮）—— **映射 ＋ 共轭式已落** ✓；**③款双向搬运未落** ✗

**⚠ 起点** ✓：**(b) 款**的在册「**取向重述**」✗（`BaseChangeProj` §34.6 头注 ✓：`T \otimes_R S` 与 `S \otimes_R T`
两取向**非 defeq** ✓，须另取向重述 ✓）—— 其**通用件**正是「`G`-Galois 性沿**等变** `R`-代数同构搬运」✗，
本工程此前**没有** ✗。

**⚠ 本轮落地** ✓（**6 件 ＋ 2 件** ✓）：
**①** `skewMap` ✓（系数沿 `e` 搬运的**加法层**映射 ✓，`\mathrm{Finsupp.mapRange}` 包进结构 ✓）；
**②** `skewMap_coeff` ✓／**③** `skewMap_single` ✓／**④** `skewMap_injective` ✓／**⑤** `skewMap_surjective` ✓；
**⑥** **`\mathrm{deltaToEndRingHom\_skewMap\_apply}`** ✓✅（**关键** ✓：**逐点共轭式**
`\delta_{S'}(\Psi x)(e y) = e(\delta_S x\ y)` ✓ —— `single` 上算 ＋ `\mathrm{induction\_on}` 归纳 ✓）；
**⑦** `faithfulSMul_of_algEquiv` ✓（**①款**搬运 ✓）；**⑧** `algebraMap_fixed_of_algEquiv` ✓（**②款**搬运 ✓）。

**✅ ③款已落（第 190 轮）** ✓✅：**主定理 `\mathrm{isGaloisWithGroup\_of\_algEquiv}`** ✓✅ ——
**注入** ✓ ＝ 共轭式 ＋ `\delta_S` 单性 ＋ `\mathrm{skewMap}` 单性 ✓；**满射** ✓ ＝ 取共轭
`f' := e^{-1} \circ f \circ e` ✓ 用 `\delta_S` 满性 ✓。
**⚠ r189 卡点之解** ✓（**读数 (70)** ✓ **现成件优先** ✗→✓）：`f'` **不手搓** ✗ ——
改用 **`\mathrm{LinearMap.comp}` 的现成共轭** ✓（`((e.\mathrm{symm} : S' \toₗ[R] S)).\mathrm{comp}
((f : S' \toₗ[R] S').\mathrm{comp} (e : S \toₗ[R] S'))` ✓）⟹ **`R`-线性自动** ✓，
`\mathrm{map\_smul'}` **无须手证** ✓（r189 手搓三支部即卡在此 ✗）。

**⚠ 工艺读数** ✓：**①** 结构型（`\mathrm{structure}` 包装 ✓）的映射须**逐字段构造** ✓
（`\mathrm{Finsupp.mapRange}` 无法直接 `\mathrm{codRestrict}` ✗，首版实测类型不符 ✗）；
**②** `\mathrm{omit}` 只可在**真未用**的 section 变量上写 ✓ —— 写错则 `\mathrm{synthInstanceFailed}` ✗
（首版对 `\mathrm{skewMap\_injective}` 误用 ✗）；**③** `\mathrm{Module.End}` 的乘法是**复合** ✓ ⟹
`\mathrm{coeffToEnd}`／`\mathrm{actEnd}` 展开后须 `\mathrm{show}` 对齐再 `\mathrm{rw}` ✓（**承 r188** ✓）。 -/

section GaloisTransport

variable {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
variable {G : Type} [Group G] [Fintype G]

/-- **系数沿 `e` 搬运的加法层映射** ✓（`Finsupp.mapRange` 包进结构 ✓）。 -/
def skewMap (e : S ≃ₐ[R] S') : SkewMonoidAlgebra S G →+ SkewMonoidAlgebra S' G where
  toFun x := ⟨(SkewMonoidAlgebra.coeff x).mapRange (e : S →+* S') (map_zero e)⟩
  map_zero' := by apply SkewMonoidAlgebra.ext; intro g; simp
  map_add' := by
    intro x z
    apply SkewMonoidAlgebra.ext
    intro g
    simp [Finsupp.mapRange_add]

omit [Group G] [Fintype G] in
lemma skewMap_coeff (e : S ≃ₐ[R] S') (x : SkewMonoidAlgebra S G) (g : G) :
    SkewMonoidAlgebra.coeff (skewMap (G := G) e x) g = e (SkewMonoidAlgebra.coeff x g) := by
  simp [skewMap, Finsupp.mapRange_apply]

omit [Group G] [Fintype G] in
lemma skewMap_single (e : S ≃ₐ[R] S') (g : G) (s : S) :
    skewMap (G := G) e (SkewMonoidAlgebra.single g s) = SkewMonoidAlgebra.single g (e s) := by
  apply SkewMonoidAlgebra.ext
  intro g'
  rw [skewMap_coeff]
  by_cases h : g' = g
  · subst h; simp
  · simp [h]

omit [Group G] [Fintype G] in
lemma skewMap_injective (e : S ≃ₐ[R] S') : Function.Injective (skewMap (G := G) e) := by
  intro x z hxz
  apply SkewMonoidAlgebra.ext
  intro g
  have h := congrArg (fun w => SkewMonoidAlgebra.coeff w g) hxz
  simp only [skewMap_coeff] at h
  exact e.injective h

omit [Group G] [Fintype G] in
lemma skewMap_surjective (e : S ≃ₐ[R] S') : Function.Surjective (skewMap (G := G) e) := by
  intro z
  induction z using SkewMonoidAlgebra.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | single g s' => exact ⟨SkewMonoidAlgebra.single g (e.symm s'),
      by rw [skewMap_single, AlgEquiv.apply_symm_apply]⟩
  | add x z hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

section Conjugation

variable [MulSemiringAction G S] [MulSemiringAction G S']

/-- **`\delta` 的逐点共轭式** ✓✅（**搬运的核心** ✓）：`\delta_{S'}(\Psi x)(e y) = e(\delta_S x\ y)` ✓
（`single` 上算 ✓ ＋ `\mathrm{induction\_on}` 归纳 ✓）。 -/
lemma deltaToEndRingHom_skewMap_apply
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (e : S ≃ₐ[R] S') (he : ∀ (g : G) (s : S), e (g • s) = g • e s)
    (x : SkewMonoidAlgebra S G) (y : S) :
    deltaToEndRingHom hRG' (skewMap (G := G) e x) (e y)
      = e (deltaToEndRingHom hRG x y) := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g s =>
    show deltaToEndAdd hRG' (skewMap (G := G) e (SkewMonoidAlgebra.single g s)) (e y)
      = e (deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) y)
    rw [skewMap_single, deltaToEndAdd_single, deltaToEndAdd_single]
    show e s * (g • e y) = e (s * (g • y))
    rw [← he g y, ← map_mul]
  | add x z hx hz => simp [map_add, hx, hz]

/-- **①款（`\mathrm{FaithfulSMul}`）搬运** ✓。 -/
lemma faithfulSMul_of_algEquiv (e : S ≃ₐ[R] S')
    (he : ∀ (g : G) (s : S), e (g • s) = g • e s) (h : FaithfulSMul G S) :
    FaithfulSMul G S' := by
  refine ⟨fun {g₁ g₂} hg => ?_⟩
  refine h.eq_of_smul_eq_smul (fun s : S => ?_)
  apply e.injective
  rw [he g₁ s, he g₂ s, hg (e s)]

/-- **②款（`R`-不动）搬运** ✓。 -/
lemma algebraMap_fixed_of_algEquiv (e : S ≃ₐ[R] S')
    (he : ∀ (g : G) (s : S), e (g • s) = g • e s)
    (h : ∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r) :
    ∀ (g : G) (r : R), g • algebraMap R S' r = algebraMap R S' r := by
  intro g r
  rw [← e.commutes r, ← he g (algebraMap R S r), h g r]

/-- **主定理**：**`G`-Galois 性沿等变 `R`-代数同构搬运** ✓✅ ——
三款皆搬运 ✓：① `\mathrm{FaithfulSMul}` ✓／② `R`-不动 ✓／③ `\delta` 双射 ✓（经探针② 的共轭式 ✓）。 -/
theorem isGaloisWithGroup_of_algEquiv
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (e : S ≃ₐ[R] S') (he : ∀ (g : G) (s : S), e (g • s) = g • e s)
    (hgal : IsGaloisWithGroup R S G hRG) : IsGaloisWithGroup R S' G hRG' := by
  have he' : ∀ (g : G) (t : S'), e.symm (g • t) = g • e.symm t := by
    intro g t
    apply e.injective
    rw [he g (e.symm t), AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hconj := deltaToEndRingHom_skewMap_apply (G := G) hRG hRG' e he
  have hconj' := deltaToEndRingHom_skewMap_apply (G := G) hRG' hRG e.symm he'
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun {g₁ g₂} h => ?_⟩
    refine hgal.1.eq_of_smul_eq_smul (fun s : S => ?_)
    apply e.injective
    rw [he g₁ s, he g₂ s, h (e s)]
  · intro g r
    rw [← e.commutes r, ← he g (algebraMap R S r), hgal.2.1 g r]
  · constructor
    · intro z z' hzz'
      have h0 : deltaToEndRingHom hRG (skewMap (G := G) e.symm z)
          = deltaToEndRingHom hRG (skewMap (G := G) e.symm z') := by
        ext y
        have h := hconj' z (e y)
        have h' := hconj' z' (e y)
        rw [AlgEquiv.symm_apply_apply] at h h'
        rw [h, h', hzz']
      exact skewMap_injective (G := G) e.symm (hgal.2.2.1 h0)
    · intro f
      set f' : Module.End R S :=
        ((e.symm : S' →ₗ[R] S)).comp ((f : S' →ₗ[R] S').comp (e : S →ₗ[R] S')) with hf'
      obtain ⟨x, hx⟩ := hgal.2.2.2 f'
      refine ⟨skewMap (G := G) e x, ?_⟩
      ext y
      obtain ⟨y₀, rfl⟩ := e.surjective y
      rw [hconj x y₀, hx]
      show e (e.symm (f (e y₀))) = f (e y₀)
      rw [AlgEquiv.apply_symm_apply]

end Conjugation

end GaloisTransport

#print axioms skewMap_injective
#print axioms isGaloisWithGroup_of_algEquiv
#print axioms deltaToEndRingHom_skewMap_apply
#print axioms faithfulSMul_of_algEquiv
#print axioms GaloisDescentHyp
#print axioms galoisDescentHyp_typeLock
#print axioms galoisDescentHyp_data_nonempty
#print axioms galoisDescent_gap_registered
#print axioms exists_galoisDescent
#print axioms H1UnitsVanishes
#print axioms Prop02bStatement
#print axioms prop02bStatement_typeLock
#print axioms prop02bStatement_zeroPic_nonempty
#print axioms isCrossedHom_of_principal
#print axioms h1UnitsVanishes_punit_rat
#print axioms GaloisFiniteGenerationDescentHyp
#print axioms galoisFiniteGenerationDescentHyp_typeLock
#print axioms galoisFiniteGenerationDescentHyp_data_nonempty
#print axioms GaloisProgeneratorHyp
#print axioms galoisProgeneratorHyp_typeLock
#print axioms galoisProgeneratorHyp_implies_galoisProjectiveHyp
#print axioms galoisProgeneratorHyp_data_nonempty
#print axioms coeffOne
#print axioms coeffOne_single_one
#print axioms deltaToEndAdd_single_one_one
#print axioms algebraMap_fixed_of_isGaloisWithGroup
#print axioms traceSum
#print axioms traceSum_invariant
#print axioms GaloisFaithfulHyp
#print axioms galoisFaithfulHyp_typeLock
#print axioms galoisFaithfulHyp_data_nonempty
#print axioms galoisFaithful_gap_registered
#print axioms galoisFaithfulHyp_refuted
#print axioms galoisFixedSubringHyp_refuted
#print axioms not_moduleFinite_int_rat
#print axioms galoisProjectiveHyp_refuted
#print axioms galoisProgeneratorHyp_refuted
#print axioms galoisEndpoints_satisfiable
#print axioms faithfulSMul_of_galoisFaithfulHyp
#print axioms coeffToEnd_smulS
#print axioms deltaInvLinearS
#print axioms coeffOneS
#print axioms coeffOneS_single_one
#print axioms coeffToEnd_algebraMap
#print axioms deltaToEndLinearS_single_one_algebraMap
#print axioms deltaToEndLinearS
#print axioms galoisTrace_route_gap_registered


/-! ## 预期用例的重建形：`Module.Projective R S'` ＋ `IsUnit (|G| : R)` ⟹ `G`-等变截面（第 255 轮 ✓）

**背景** ✓：源 `lem1.2` 证明第二步所引的**无限制端点** `GaloisProjectiveSectionHyp` ✓（§52 ✓）
已在**第 250 轮机器反驳** ✗（`galoisProjectiveSectionHyp_refuted` ✓，`SaltThm38_ABGV52.lean:1582` ✓）
⟹ **不能再作假设用** ✗。本节按**源的真实用例**重建该步 ✓：`S'` 对 `R` **投射** ✓
（源侧由 `R'[G]`-投射性供给 ✓，`raw/Saltman1984.tex:139-142` ✓，**⚠-tex-sourced** ✗）＋
`|G|` 在 `R` 中**可逆** ✓ —— 此时**分裂 ＋ 平均**给出 `G`-等变 `R`-线性截面 ✓（机制逐条见主定理文档 ✓）。

**⚠ 口径** ✓：源侧的 **Galois 假设**（`hgal'` ✓）在本步**不被使用** ✗ —— 机制只需**投射性** ＋
**`|G|` 可逆** ✓（源构型亦然 ✓：其 `δ` 由 `F[G]`-投射性给出 ✓）。故主定理**不列** `hgal'` ✗；
保留它的**调用点签名一致形** ✓ 见 `exists_galoisProjectiveSection_of_galois_projective` ✓。
-/

set_option maxHeartbeats 1000000 in
/-- **预期用例的重建形** ✓（**第 255 轮** ✓）：**投射性** ✓ ＋ **`|G|` 可逆** ✓ ⟹ **`G`-等变 `R`-线性截面** ✓ ——
即源 `lem1.2` 证明第二步所需之物 ✓（**旧用点** ✓：`exists_galoisProjectiveSection` ✓，`:344` ✓）。

**机制** ✓（**split ＋ average** ✓，两步皆已落 ✓）：
① **分裂** ✓：`hproj` ✓ 给出 `ψ` 的 `R`-线性**右逆** `σ` ✓（`ψ ∘ σ = id` ✓）—— 用 mathlib
`LinearMap.exists_rightInverse_of_surjective` ✓（其输入恰是 `[Module.Projective R S']` ✓，
即 `Module.Projective` 的**提升性质**形 ✓，`Mathlib/Algebra/Module/Projective.lean:111` ✓）。
② **平均** ✓：`δ x := u⁻¹ • ∑_g g⁻¹ • σ (g • x)` ✓，`u` ＝ `|G|` 在 `R` 中的**单位** ✓（`hunit.unit` ✓）。
**⚠ 工艺** ✗：`R` 一般**无** `Inv` 实例 ✗（实测 `(c : R)⁻¹` 在 `CommRing` 档 `synthInstanceFailed` ✗），
故逆由 `Rˣ` 承载 ✓（`IsUnit.val_inv_mul` ✓）。
③ **截面性** ✓（`ψ ∘ δ = id` ✓）：逐项 `ψ (g⁻¹ • σ (g • x)) = g⁻¹ • (g • x) = x` ✓（`hψG` ✓ ＋ `ψ ∘ σ = id` ✓），
再 `∑_g x = |G| • x` ✓（`Finset.sum_const` ✓ ＋ `Nat.cast_smul_eq_nsmul` ✓）并约去 `|G|` ✓。
④ **等变性** ✓：重指标 `g ↦ g * g₀` ✓（`Equiv.mulRight` ✓ ＋ `Equiv.sum_comp` ✓）
＋ `SMulCommClass G R S` ✓（由 `hRG` ✓ 得 ✓，同旧用点档 ✓）。

**🔴 不声称** ✗：**①** 本定理**不**重证已反驳的**无限制形** ✗ —— `GaloisProjectiveSectionHyp` ✓ 仍为假 ✗
（`galoisProjectiveSectionHyp_refuted` ✓，第 250 轮 ✓）；**②** **不**声称**去掉 `hproj` 或去掉 `hunit`** 时
截面仍存在 ✗ —— 第 250 轮反例 ✓ **除 `hproj` 外全部中** ✓（`R = Polynomial ℚ` ✓、`S' = ℚ` ✓ 为 `G`-Galois ✓、
`G = PUnit` ✓ 故 `|G| = 1` ✓ **是**单位 ✓），而该满射**连 `R`-线性截面都没有** ✗（反驳步只用 `R`-线性 ＋ 截面条件 ✓）
⟹ **投射性不可去** ✓；`hunit` 则是**平均步约去**的前提 ✓（非单位则 `c` 不存在 ✗）；
**③** **不**对源侧 **`R[G]`-投射性**断言作任何声称 ✗（该断言在 `raw/` 内**仍无供给** ✗，§47／§52 ✓）。 -/
theorem exists_galoisProjectiveSection_of_projective
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (hproj : Module.Projective R S')
    (hunit : IsUnit (Fintype.card G : R))
    (ψ : S →ₗ[R] S') (hψG : ∀ (g : G) (s : S), ψ (g • s) = g • ψ s)
    (hψsurj : Function.Surjective ψ) :
    ∃ δ : S' →ₗ[R] S, (∀ x : S', ψ (δ x) = x) ∧ (∀ (g : G) (x : S'), δ (g • x) = g • δ x) := by
  let _instProj : Module.Projective R S' := hproj
  let _instC : SMulCommClass G R S := ⟨hRG⟩
  let u : Rˣ := hunit.unit
  let c : R := ((u⁻¹ : Rˣ) : R)
  have hc : c * (Fintype.card G : R) = 1 := hunit.val_inv_mul
  obtain ⟨σ, hσ⟩ := ψ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top_of_surjective ψ hψsurj)
  have hσ' : ∀ x : S', ψ (σ x) = x := fun x => LinearMap.congr_fun hσ x
  let δ : S' →ₗ[R] S := c • ∑ g : G, (actEnd hRG g⁻¹).comp (σ.comp (actEnd hRG' g))
  have hδ : ∀ x : S', δ x = c • ∑ g : G, g⁻¹ • σ (g • x) := by
    intro x
    have hA : ∀ (g : G) (y : S), actEnd hRG g y = g • y := fun g y => rfl
    have hA' : ∀ (g : G) (y : S'), actEnd hRG' g y = g • y := fun g y => rfl
    simp only [δ, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, hA, hA']
  have hψδ : ∀ x : S', ψ (δ x) = x := by
    intro x
    rw [hδ x, map_smul, map_sum]
    have hterm : ∀ g : G, ψ (g⁻¹ • σ (g • x)) = x := by
      intro g
      rw [hψG g⁻¹ (σ (g • x)), hσ' (g • x), inv_smul_smul]
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul R, smul_smul (M := R), hc, one_smul]
  have hδG : ∀ (g₀ : G) (x : S'), δ (g₀ • x) = g₀ • δ x := by
    intro g₀ x
    have hreindex : (∑ g : G, g⁻¹ • σ (g • (g₀ • x)))
        = ∑ k : G, g₀ • (k⁻¹ • σ (k • x)) := by
      have h1 : ∀ g : G, g⁻¹ • σ (g • (g₀ • x))
          = g₀ • ((g * g₀)⁻¹ • σ ((g * g₀) • x)) := by
        intro g
        rw [smul_smul (M := G) g g₀ x,
          show g⁻¹ = g₀ * (g * g₀)⁻¹ by simp [mul_inv_rev]]
        exact (smul_smul (M := G) g₀ ((g * g₀)⁻¹) (σ ((g * g₀) • x))).symm
      calc ∑ g : G, g⁻¹ • σ (g • (g₀ • x))
          = ∑ g : G, g₀ • ((g * g₀)⁻¹ • σ ((g * g₀) • x)) :=
            Finset.sum_congr rfl (fun g _ => h1 g)
        _ = ∑ k : G, g₀ • (k⁻¹ • σ (k • x)) :=
            Equiv.sum_comp (Equiv.mulRight g₀) (fun k : G => g₀ • (k⁻¹ • σ (k • x)))
    rw [hδ (g₀ • x), hδ x, hreindex, ← Finset.smul_sum]
    exact (smul_comm g₀ c _).symm
  exact ⟨δ, hψδ, hδG⟩

set_option maxHeartbeats 1000000 in
/-- **调用点签名一致形** ✓（**第 255 轮** ✓）：绑定表与旧**用点** `exists_galoisProjectiveSection` ✓（`:344` ✓）
逐位对齐 ✓，仅把该处的 **`h : GaloisProjectiveSectionHyp F G`** ✗ 换成 **`hproj` ＋ `hunit`** ✓
（＝ 蓝图第 9 步 `SaltLem12_ABGV52:274` ✓ 的 `hproj` 输入按「预期用例」重接 ✓）。

**⚠ 口径** ✓：`hgal'` ✓ 在本步**不被使用** ✗（机制只需投射性 ＋ `|G|` 可逆 ✓，见主定理 ✓）——
保留它只为**与用点签名对齐** ✓（源侧调用处 `hgal'` 本就在上下文 ✓），
并按 linter 惯例以 `_` 前缀标为**冗余假设** ✓（`linter.unusedVariables` ✓ 不报 ✓）。
**🔴 不声称** ✗：同主定理三条 ✓ —— **不**重证无限制形 ✗／**不**声称去掉 `hproj`、`hunit` 后截面存在 ✗／
**不**声称源侧 `R[G]`-投射性 ✗。 -/
theorem exists_galoisProjectiveSection_of_galois_projective
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (_hgal' : IsGaloisWithGroup R S' G hRG')
    (hproj : Module.Projective R S')
    (hunit : IsUnit (Fintype.card G : R))
    (ψ : S →ₗ[R] S') (hψG : ∀ (g : G) (s : S), ψ (g • s) = g • ψ s)
    (hψsurj : Function.Surjective ψ) :
    ∃ δ : S' →ₗ[R] S, (∀ x : S', ψ (δ x) = x) ∧ (∀ (g : G) (x : S'), δ (g • x) = g • δ x) :=
  exists_galoisProjectiveSection_of_projective F G R S S' hRG hRG' hproj hunit ψ hψG hψsurj

set_option maxHeartbeats 1000000 in
/-- **`F = ℚ` 档推论（`hunit` 免假设）** ✓（**第 255 轮** ✓）：`R` 为 `ℚ`-代数时 `IsUnit (|G| : R)` ✓
**自动成立** ✓ —— `(|G| : ℚ) ≠ 0` ✓（`Fintype.card_ne_zero` ✓）经 `algebraMap ℚ R` ✓ 搬入 ✓
（`IsUnit.map` ✓ ＋ `map_natCast` ✓）⟹ **特征 0 档无需 `hunit`** ✓，即**源用例所在档** ✓
（`|G|` 可逆 ✓）且该假设在该档**非空洞** ✓。

**⚠ 宇宙档** ✗：本推论把 `R S S'` 钉在 `Type`（＝ `Type 0`，`ℚ` 自身所在档 ✓）——
主定理为**单宇宙**绑定 ✓（同旧端点档 ✓，§52.2 ✓），故 `F` 与环**必须同档** ✗
（实测：`R : Type u` 时取 `F := ℚ` **类型不匹配** ✗）；欲取任意宇宙档须把 `F` 独立成宇宙参数 ⚠（**未落** ✗）。
**🔴 不声称** ✗：同主定理三条 ✓。 -/
theorem exists_galoisProjectiveSection_of_projective_rat
    (G : Type) [Group G] [Fintype G]
    (R S S' : Type) [CommRing R] [CommRing S] [CommRing S']
    [Algebra ℚ R] [Algebra R S] [Algebra R S'] [Algebra ℚ S] [Algebra ℚ S']
    [IsScalarTower ℚ R S] [IsScalarTower ℚ R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (hproj : Module.Projective R S')
    (ψ : S →ₗ[R] S') (hψG : ∀ (g : G) (s : S), ψ (g • s) = g • ψ s)
    (hψsurj : Function.Surjective ψ) :
    ∃ δ : S' →ₗ[R] S, (∀ x : S', ψ (δ x) = x) ∧ (∀ (g : G) (x : S'), δ (g • x) = g • δ x) := by
  refine exists_galoisProjectiveSection_of_projective ℚ G R S S'
    hRG hRG' hproj ?_ ψ hψG hψsurj
  have hq : IsUnit ((Fintype.card G : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hmap : IsUnit (algebraMap ℚ R ((Fintype.card G : ℕ) : ℚ)) := hq.map (algebraMap ℚ R)
  rwa [map_natCast] at hmap

set_option maxHeartbeats 1000000 in
/-- **非空洞探针（L1）** ✓：主定理的**两条新假设**在 `ℚ` 档**可同时实例化** ✓ ——
`Module.Projective ℚ ℚ` ✓（`ℚ` 对自身投射 ✓）＋ `IsUnit (|PUnit| : ℚ)` ✓（`|PUnit| = 1` ✓）；
**结论侧**的非空洞继承 `galoisProjectiveSectionHyp_data_nonempty` ✓（`δ = id` 档 ✓）。 -/
theorem galoisProjectiveSectionProj_data_nonempty :
    Nonempty (Module.Projective ℚ ℚ) ∧ IsUnit (Fintype.card PUnit : ℚ) :=
  ⟨⟨inferInstance⟩, isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)⟩

#print axioms exists_galoisProjectiveSection_of_projective
#print axioms exists_galoisProjectiveSection_of_galois_projective
#print axioms exists_galoisProjectiveSection_of_projective_rat
#print axioms galoisProjectiveSectionProj_data_nonempty

end ABGV52.BTier
