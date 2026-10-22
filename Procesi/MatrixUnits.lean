/-
  Procesi —— **S5 `thm:14.15` 的准备层：矩阵单位组**

  **原文（逐字）**：`raw/Saltman1999ch14.tex:303–306`（`thm:14.15` 证明第二段）：
  > Let `e(i,j) ∈ M_n(S)` be the standard matrix units. Set `f_r(i,j) = θ_r(e(i,j))`.
  > By `[saltman1999lectures, 2.11]` we may assume the `f_1(i,j) ∈ M_n(T)` are the standard
  > matrix units and there is an invertible `A ∈ M_n(T)` such that `A⁻¹ f_1(i,j) A = f_2(i,j)`
  > for all `i,j`.

  **L46／L47 内容式检索结论（本件立项依据，勿据"按名搜"推断）**：
  * mathlib 本 pin（`aa35a481`）**无** 矩阵单位概念：`grep -rln "MatrixUnit\|matrixUnit\|matrix unit"`
    ⟹ **0 命中**；`stdBasisMatrix` 亦无（`SLPerfect.lean` 头已记同结论）；
  * `Matrix.unitaryGroup` 是 **star／内积** 意义下的酉群，与本概念**无关**（勿误配）；
  * 本仓已有 `Procesi.single_mul_single`（`SLPerfect.lean:35`，**universe 单态**：
    `{R : Type}`／`{n : Type}`，故本件只对 `Type` 层使用）；
  * mathlib **有** `Matrix.sum_single_one : ∑ i, single i i 1 = 1`
    （`Data/Matrix/Basis.lean:153`）——`stdMU_sum` 直接引用。

  故 `[saltman1999lectures, 2.11]`（矩阵单位组在 `M_n(T)` 中的共轭唯一性）**须自建**；
  本件先给其**对象层**与**共轭不变性**（易方向），唯一性本体在下一轮。
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.Module
import Procesi.SLPerfect

open Matrix

namespace Procesi

/-! ## §1 标准矩阵单位 `e(i,j) = single i j 1` -/

section Std

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

/-- **标准矩阵单位** `e(i,j) = single i j 1`（`M_n(R)` 的矩阵单位；对应原文 `e(i,j) ∈ M_n(S)`）。 -/
def stdMU (i j : n) : Matrix n n R := Matrix.single i j 1

/-- ★ **乘法表**：`e(i,j)·e(k,l) = δ_{jk} e(i,l)`。 -/
lemma stdMU_mul (i j k l : n) :
    stdMU (R := R) i j * stdMU k l = if j = k then stdMU i l else 0 := by
  show Matrix.single i j 1 * Matrix.single k l 1
    = if j = k then Matrix.single i l 1 else 0
  simpa using single_mul_single i j k l (1 : R) (1 : R)

#print axioms stdMU_mul

/-- ★ **完备性**：`∑ i, e(i,i) = 1`（`Matrix.sum_single_one`）。 -/
lemma stdMU_sum : ∑ i, stdMU (R := R) (n := n) i i = 1 := by
  show ∑ i, Matrix.single i i (1 : R) = 1
  exact Matrix.sum_single_one

#print axioms stdMU_sum

end Std

/-! ## §2 矩阵单位组（抽象）与其共轭不变性 -/

section System

variable {R : Type} [Ring R] {n : Type} [Fintype n] [DecidableEq n]

/-- **`n×n` 矩阵单位组**（Saltman 讲义 2.11 的对象）：一组 `f : n → n → R` 满足
`f i j * f k l = δ_{jk} f i l` 且 `∑ i, f i i = 1`。
**注意**：本结构**不是** `Subsingleton`／不假定 `f` 来自 `M_n` 的标准单位——`thm:14.15` 的全部
内容正是"两组这样的 `f` 相差一个单位共轭"。 -/
structure IsMatrixUnitSystem (f : n → n → R) : Prop where
  mul_mem : ∀ i j k l, f i j * f k l = if j = k then f i l else 0
  sum_mem : ∑ i, f i i = 1

/-- 标准矩阵单位构成矩阵单位组。 -/
lemma stdMU_isMatrixUnitSystem {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] :
    IsMatrixUnitSystem (stdMU (R := R) (n := n)) where
  mul_mem := stdMU_mul
  sum_mem := stdMU_sum

#print axioms stdMU_isMatrixUnitSystem

/-- ★★ **单位共轭保矩阵单位组**：若 `f` 是矩阵单位组、`u` 是单位，则 `(i,j) ↦ u·f i j·u⁻¹` 也是。
**用途**：原文 `A⁻¹ f_1(i,j) A = f_2(i,j)` 的两侧都因此是矩阵单位组。 -/
lemma IsMatrixUnitSystem.conj {f : n → n → R} (hf : IsMatrixUnitSystem f) (u : Rˣ) :
    IsMatrixUnitSystem fun i j => u * f i j * ↑u⁻¹ where
  mul_mem i j k l := by
    have hcancel : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
    calc (u * f i j * ↑u⁻¹) * (u * f k l * ↑u⁻¹)
        = u * f i j * ((↑u⁻¹ : R) * u) * f k l * ↑u⁻¹ := by noncomm_ring
      _ = u * f i j * f k l * ↑u⁻¹ := by rw [hcancel]; noncomm_ring
      _ = u * (f i j * f k l) * ↑u⁻¹ := by noncomm_ring
      _ = u * (if j = k then f i l else 0) * ↑u⁻¹ := by rw [hf.mul_mem]
      _ = if j = k then u * f i l * ↑u⁻¹ else 0 := by split_ifs <;> simp
  sum_mem := by
    have h : ∑ i, u * f i i * ↑u⁻¹ = u * (∑ i, f i i) * ↑u⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [h, hf.sum_mem, mul_one, Units.mul_inv]

#print axioms IsMatrixUnitSystem.conj

end System

/-! ## §3 唯一性方向的**易半**：intertwiner 与共轭

`[saltman1999lectures, 2.11]` 的完整内容是"两组矩阵单位组相差一个单位共轭"。本节机检其
**结构性核心**：给定矩阵单位组 `g`（与基点 `b`），
`A := ∑_k g(k,b)·e(b,k)` 满足 `A·e(i,j) = g(i,j)·A`；若 `A` 是单位，则
`A·e(i,j)·A⁻¹ = g(i,j)`——即 `e` 与 `g` 共轭。

**未做（下一轮）**：`A` **可逆性**——古典路线是"局部环上归约到剩余域 ＋ Nakayama"，
或"域上 `Aut(M_n(k)) = PGL_n(k)`（Skolem–Noether）＋ 提升"。这是本件唯一剩下的难点。 -/

section Inter

variable {T : Type} [CommRing T] {n : Type} [Fintype n] [DecidableEq n]

/-- **intertwiner**：`A = ∑_k g(k,b)·e(b,k)`（基点 `b`；对应原文的 `A`）。 -/
noncomputable def mtuIntertwiner (g : n → n → Matrix n n T) (b : n) : Matrix n n T :=
  ∑ k, g k b * stdMU (R := T) b k

/-- ★ **`A · e(i,j) = g(i,b)·e(b,j)`**（左乘：求和只剩 `k = i` 一项）。 -/
lemma mtuIntertwiner_mul_stdMU {g : n → n → Matrix n n T} (b i j : n) :
    mtuIntertwiner g b * stdMU (R := T) i j = g i b * stdMU (R := T) b j := by
  rw [mtuIntertwiner, Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · rw [mul_assoc, stdMU_mul]; simp
  · intro k _ hk
    rw [mul_assoc, stdMU_mul, ite_eq_right hk, mul_zero]
  · intro h; simp at h

#print axioms mtuIntertwiner_mul_stdMU

/-- ★ **`g(i,j) · A = g(i,b)·e(b,j)`**（右乘：用矩阵单位的乘法表，求和只剩 `k = j` 一项）。 -/
lemma mul_mtuIntertwiner {g : n → n → Matrix n n T} (hg : IsMatrixUnitSystem g)
    (b i j : n) :
    g i j * mtuIntertwiner g b = g i b * stdMU (R := T) b j := by
  rw [mtuIntertwiner, Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · rw [← mul_assoc, hg.mul_mem i j j b]; simp
  · intro k _ hk
    rw [← mul_assoc, hg.mul_mem i j k b, ite_eq_right (Ne.symm hk), zero_mul]
  · intro h; simp at h

#print axioms mul_mtuIntertwiner

/-- ★★★ **`A` 把标准矩阵单位组与 `g` 相联**：`A·e(i,j) = g(i,j)·A`。 -/
lemma mtuIntertwiner_intertwines {g : n → n → Matrix n n T} (hg : IsMatrixUnitSystem g)
    (b i j : n) :
    mtuIntertwiner g b * stdMU (R := T) i j = g i j * mtuIntertwiner g b := by
  rw [mtuIntertwiner_mul_stdMU, mul_mtuIntertwiner hg]

#print axioms mtuIntertwiner_intertwines

/-- ★★★★ **若 intertwiner 是单位，则它把标准组共轭成 `g`**：`u·e(i,j)·u⁻¹ = g(i,j)`。
**这是 `[saltman1999lectures, 2.11]` 的结论形式**（原文 `A⁻¹f_1(i,j)A = f_2(i,j)`，符号方向随约定）。 -/
lemma stdMU_conj_of_unit {g : n → n → Matrix n n T} (hg : IsMatrixUnitSystem g) (b : n)
    (u : (Matrix n n T)ˣ) (hu : ((u : Matrix n n T)) = mtuIntertwiner g b) (i j : n) :
    ((u : Matrix n n T)) * stdMU (R := T) i j
        * ((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) = g i j := by
  have hA : ((u : Matrix n n T)) * stdMU (R := T) i j
      = g i j * ((u : Matrix n n T)) := by
    rw [hu, mtuIntertwiner_intertwines hg]
  rw [hA, mul_assoc, show ((u : Matrix n n T)) * ((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) = 1
    from Units.mul_inv u, mul_one]

#print axioms stdMU_conj_of_unit

end Inter

/-! ## §4 **列型** intertwiner `A(w)`：可逆性的正确载体

`§3` 的 `A = ∑_k g(k,b)·e(b,k)` 的列是 `g(j,b)·e_b`——**`A` 可能为 `0`**
（例：`g = P·e·P⁻¹` 且 `P` 的对角元在 `b` 处为 `0` 时 `A = P⁻¹_{bb}·P = 0`），故它**不是**可逆性论证
的正确载体。本节改用"第 `j` 列为 `g(j,b)·w`"的 `A(w)`（`w : n → k` 任意向量）：
**`A(w)` 对一切 `w` 都满足交错性**，且下一节证明**适当选取 `w` 时 `A(w)` 可逆**。

**注（第 151 轮推广）**：本节的 `k` 只需**交换环**（原为域）；交错性 `A(w)·e(i,j) = g(i,j)·A(w)`
的证明只用环公理，故对 `T` 局部的一般情形同样成立——这正是局部环归约要用的形式。 -/

section Col

variable {k : Type} [CommRing k] {n : Type} [Fintype n] [DecidableEq n]

/-- **列型 intertwiner**：第 `j` 列是 `g(j,b) *ᵥ w`。 -/
noncomputable def mtuColMat (g : n → n → Matrix n n k) (b : n) (w : n → k) : Matrix n n k :=
  Matrix.of (fun a j => (g j b *ᵥ w) a)

/-- ★ **`A(w)` 作用在向量上**：`A(w) *ᵥ y = (∑_j y_j • g(j,b)) *ᵥ w`。 -/
lemma mtuColMat_mulVec {g : n → n → Matrix n n k} {b : n} {w y : n → k} :
    mtuColMat g b w *ᵥ y = (∑ j, y j • g j b) *ᵥ w := by
  funext a
  simp only [mtuColMat, Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.sum_mul, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro c _
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

#print axioms mtuColMat_mulVec

/-- ★★★ **`A(w)` 对一切 `w` 都交错**：`A(w)·e(i,j) = g(i,j)·A(w)`。 -/
lemma mtuColMat_intertwines {g : n → n → Matrix n n k} (hg : IsMatrixUnitSystem g)
    (b i j : n) (w : n → k) :
    mtuColMat g b w * stdMU (R := k) i j = g i j * mtuColMat g b w := by
  ext a d
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ c, mtuColMat g b w a c * stdMU (R := k) i j c d
      = if j = d then (g i b *ᵥ w) a else 0 := by
    rw [Finset.sum_eq_single i]
    · simp only [mtuColMat, Matrix.of_apply, stdMU, Matrix.single_apply, true_and]
      split_ifs <;> simp
    · intro c _ hc
      have hic : ¬ (i = c) := fun h => hc h.symm
      simp only [mtuColMat, Matrix.of_apply, stdMU, Matrix.single_apply]
      simp [hic]
    · intro h; simp at h
  have hR : ∑ c, (g i j) a c * mtuColMat g b w c d
      = if j = d then (g i b *ᵥ w) a else 0 := by
    have hmv : ∑ c, (g i j) a c * mtuColMat g b w c d
        = ((g i j) *ᵥ ((g d b) *ᵥ w)) a := rfl
    rw [hmv, Matrix.mulVec_mulVec, hg.mul_mem i j d b]
    split_ifs <;> simp
  rw [hL, hR]

#print axioms mtuColMat_intertwines

end Col

/-! ## §5 **S5（域上）收口**：`M_n(k)` 的两组矩阵单位组总是共轭

本节把 §3–§4 合起来，完成 `[saltman1999lectures, 2.11]` 的**域上**情形：
域 `k` 上任意矩阵单位组 `g` 与标准组 `e` 相差一个单位共轭。

**证明（四步，全部机检）**：
① `∃ b, g b b ≠ 0`（由 `∑_i g i i = 1 ≠ 0`）；
② `∃ w, g b b *ᵥ w ≠ 0`（由 `g b b ≠ 0` 取 `Pi.single c 1`）；
③ `A(w) *ᵥ y = 0 ⟹ y = 0`：先得 `(∑_j y_j • g j b) *ᵥ w = 0`（`mtuColMat_mulVec`），
   左乘 `g(b,k)` 后得 `y_k • (g b b *ᵥ w) = 0`，由 ② 得 `y_k = 0`；
④ 故 `A(w)` 单射 ⟹ `det ≠ 0`（`Matrix.exists_mulVec_eq_zero_iff` 逆否）⟹ `A(w)` 是单位，
   再用 `mtuColMat_intertwines` 与 `A·A⁻¹ = 1` 消去。

**射程（如实登记）**：本节要求 `[Nonempty n]`。这不是人为限制——`n` 为空时
`Matrix n n k` 是**单点集**（`0 = 1` 成立），`IsMatrixUnitSystem` 可满足，但无法取基点 `b`；
此时结论在空指标下平凡成立。Saltman 的 `n > 1` 覆盖本节的射程。
**局部环情形**（原文的 `T` 局部）：由剩余域 ＋ Nakayama 提升，**未做**。 -/

section S5

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- ★★ **对角块不全为零**：`∑_i g i i = 1 ≠ 0` 给出某个 `g b b ≠ 0`。 -/
lemma exists_diag_ne_zero {g : n → n → Matrix n n k} (hg : IsMatrixUnitSystem g) :
    ∃ b, g b b ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := hg.sum_mem
  rw [Finset.sum_eq_zero (fun i _ => h i)] at h1
  exact one_ne_zero h1.symm

#print axioms exists_diag_ne_zero

/-- ★★ **非零矩阵在某向量上非零**：`M ≠ 0` ⟹ `∃ w, M *ᵥ w ≠ 0`（取非零元所在列的单位向量）。 -/
lemma exists_mulVec_ne_zero {M : Matrix n n k} (hM : M ≠ 0) : ∃ w : n → k, M *ᵥ w ≠ 0 := by
  obtain ⟨a, c, hac⟩ : ∃ a c, M a c ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (funext fun a => funext fun c => h a c)
  refine ⟨Pi.single c 1, fun h0 => hac ?_⟩
  have h1 : (M *ᵥ Pi.single c (1 : k)) a = 0 := by rw [h0]; rfl
  rw [show M *ᵥ Pi.single c (1 : k) = M.col c from by
    rw [Matrix.mulVec_single]; simp] at h1
  simpa using h1

#print axioms exists_mulVec_ne_zero

/-- ★★★ **`A(w)` 的核为零**（在 `g b b *ᵥ w ≠ 0` 下）：`A(w) *ᵥ y = 0 ⟹ y = 0`。 -/
lemma mtuColMat_mulVec_eq_zero {g : n → n → Matrix n n k} (hg : IsMatrixUnitSystem g)
    (b : n) {w : n → k} (hw : g b b *ᵥ w ≠ 0) {y : n → k}
    (hy : mtuColMat g b w *ᵥ y = 0) : y = 0 := by
  funext k'
  have hY : (∑ j, y j • g j b) *ᵥ w = 0 := by
    rw [← mtuColMat_mulVec, hy]
  have hG : g b k' * (∑ j, y j • g j b) = y k' • g b b := by
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single k']
    · rw [Matrix.mul_smul, hg.mul_mem b k' k' b]; simp
    · intro j _ hj
      rw [Matrix.mul_smul, hg.mul_mem b k' j b]
      have hkj : ¬ (k' = j) := fun h => hj h.symm
      rw [show (if k' = j then g b b else 0) = 0 from ite_eq_right hkj, smul_zero]
    · intro h; simp at h
  have h1 : (g b k' * (∑ j, y j • g j b)) *ᵥ w = 0 := by
    rw [← Matrix.mulVec_mulVec, hY, Matrix.mulVec_zero]
  rw [hG, Matrix.smul_mulVec] at h1
  rcases smul_eq_zero.mp h1 with h | h
  · exact h
  · exact absurd h hw

#print axioms mtuColMat_mulVec_eq_zero

/-- ★★★ **适当选取 `w` 时 `A(w)` 的行列式非零**（`Matrix.exists_mulVec_eq_zero_iff` 的逆否）。 -/
lemma mtuColMat_det_ne_zero {g : n → n → Matrix n n k} (hg : IsMatrixUnitSystem g)
    (b : n) {w : n → k} (hw : g b b *ᵥ w ≠ 0) : (mtuColMat g b w).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hvne (mtuColMat_mulVec_eq_zero hg b hw hv0)

#print axioms mtuColMat_det_ne_zero

/-- ★★★★★ **S5（域上）收口 ＝ `[saltman1999lectures, 2.11]` 的域上情形**：
域上任意 `n×n` 矩阵单位组与**标准组**相差一个单位共轭。

**这是原文 `thm:14.15` 证明第二段所引 2.11 的核心内容**，也是 (A) 论证层唯一的重型工具。 -/
theorem exists_unit_conj_stdMU {g : n → n → Matrix n n k} (hg : IsMatrixUnitSystem g) :
    ∃ u : (Matrix n n k)ˣ, ∀ i j,
      ((u : Matrix n n k)) * stdMU (R := k) i j
        * ((u⁻¹ : (Matrix n n k)ˣ) : Matrix n n k) = g i j := by
  obtain ⟨b, hb⟩ := exists_diag_ne_zero hg
  obtain ⟨w, hw⟩ := exists_mulVec_ne_zero hb
  have hdet : (mtuColMat g b w).det ≠ 0 := mtuColMat_det_ne_zero hg b hw
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mtuColMat g b w) hdet, fun i j => ?_⟩
  have hA : ((Matrix.GeneralLinearGroup.mkOfDetNeZero (mtuColMat g b w) hdet : Matrix n n k))
      * stdMU (R := k) i j
      = g i j * ((Matrix.GeneralLinearGroup.mkOfDetNeZero (mtuColMat g b w) hdet :
          Matrix n n k)) := by
    rw [show ((Matrix.GeneralLinearGroup.mkOfDetNeZero (mtuColMat g b w) hdet : Matrix n n k))
        = mtuColMat g b w from by simp]
    exact mtuColMat_intertwines hg b i j w
  rw [hA, mul_assoc,
    show ((Matrix.GeneralLinearGroup.mkOfDetNeZero (mtuColMat g b w) hdet : Matrix n n k))
        * (((Matrix.GeneralLinearGroup.mkOfDetNeZero (mtuColMat g b w) hdet)⁻¹ :
            (Matrix n n k)ˣ) : Matrix n n k) = 1 from Units.mul_inv _,
    mul_one]

#print axioms exists_unit_conj_stdMU

end S5

/-! ## §6 沿环同态的运输（局部环归约的第一步）

`thm:14.15` 的原文路线是"任意交换环嵌入局部环之积 ⟹ 可设 `T` 局部"。本节给**归约的代数侧**：
矩阵单位组、标准组、以及共轭关系**都沿环同态 `f : T →+* T'` 运输**。
取 `T' = T ⧸ m`（`T` 局部、`m` 极大理想）即得"模 `m` 归约"这一步。

**局部环情形的库内侦察（L46，本轮实测）**：
* `Mathlib/RingTheory/LocalRing/Module.lean:299` **有**
  `free_of_flat_of_isLocalRing [Module.Finite R P] [Flat R P] : Free R P`
  —— 即"局部环上有限生成平坦模自由"；
* 加 `Module.Flat.of_projective`，即得"局部环上有限生成**投射**模自由"。
⟹ 局部环情形的**模论工具齐备**，路线：矩阵单位组 ⟹ `T^n = ⊕_i P_i`（各 `P_i` 同构、有限投射）
⟹ 各 `P_i` 自由、秩相等、`n = n·r` ⟹ 秩 1 ⟹ 取基即得共轭矩阵。**本体未做**。 -/

section Map

variable {T T' : Type} [CommRing T] [CommRing T'] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★★ **矩阵单位组沿环同态运输**：`f : T →+* T'` 把 `g` 送到 `(i,j) ↦ (g i j).map f`。 -/
lemma IsMatrixUnitSystem.map (f : T →+* T') {g : n → n → Matrix n n T}
    (hg : IsMatrixUnitSystem g) :
    IsMatrixUnitSystem (fun i j => (g i j).map f) where
  mul_mem i j k l := by
    show (g i j).map ⇑f * (g k l).map ⇑f = if j = k then (g i l).map ⇑f else 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      hg.mul_mem i j k l]
    split_ifs
    · rfl
    · simp
  sum_mem := by
    show ∑ i, (g i i).map ⇑f = 1
    simp only [← RingHom.mapMatrix_apply]
    rw [← map_sum, hg.sum_mem, map_one]

#print axioms IsMatrixUnitSystem.map

/-- ★ **标准矩阵单位组沿环同态不变**。 -/
lemma stdMU_map (f : T →+* T') (i j : n) :
    (stdMU (R := T) i j).map ⇑f = stdMU (R := T') i j := by
  show (Matrix.single i j (1 : T)).map ⇑f = Matrix.single i j (1 : T')
  rw [show (Matrix.single i j (1 : T)).map ⇑f
      = Matrix.single i j (f 1) from by ext a b; simp [Matrix.single_apply]]
  simp

#print axioms stdMU_map

/-- ★★★ **共轭的可运输性**：`T` 上的共轭 `u·e·u⁻¹ = g` 沿 `f` 送到 `T'` 上的共轭
（`M_n(f)` 把单位送到单位）。**用途**：局部环归约中把域上的结论搬回模 `m` 的层面。 -/
lemma stdMU_conj_map (f : T →+* T') {g : n → n → Matrix n n T}
    (u : (Matrix n n T)ˣ) (hu : ∀ i j, ((u : Matrix n n T)) * stdMU (R := T) i j
      * ((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) = g i j) (i j : n) :
    ((Units.map f.mapMatrix.toMonoidHom u : (Matrix n n T')ˣ) : Matrix n n T')
        * stdMU (R := T') i j
        * (((Units.map f.mapMatrix.toMonoidHom u)⁻¹ : (Matrix n n T')ˣ) : Matrix n n T')
      = (g i j).map ⇑f := by
  have h1 : ((Units.map f.mapMatrix.toMonoidHom u : (Matrix n n T')ˣ) : Matrix n n T')
      = ((u : Matrix n n T)).map ⇑f := rfl
  have h2 : (((Units.map f.mapMatrix.toMonoidHom u)⁻¹ : (Matrix n n T')ˣ) : Matrix n n T')
      = (((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)).map ⇑f := by
    rw [← map_inv]
    simp [RingHom.mapMatrix_apply]
  rw [h1, h2, ← stdMU_map f i j, ← Matrix.map_mul, ← Matrix.map_mul, hu i j]

#print axioms stdMU_conj_map

end Map

/-! ## §7 `mulVec` 与列型 intertwiner 沿环同态的运输

§6 把矩阵单位组与共轭沿 `f : T →+* T'` 运输；局部环归约还差**载体层**的运输：
`A(w)` 与它的 `mulVec` 作用。本节补齐。
（配合 §4 的推广：`A(w)·e(i,j) = g(i,j)·A(w)` 现对**任意交换环**成立。） -/

section MapVec

variable {T T' : Type} [CommRing T] [CommRing T'] {n : Type} [Fintype n] [DecidableEq n]

/-- ★ **`mulVec` 沿环同态运输**：`(M.map f) *ᵥ (f ∘ v) = f ∘ (M *ᵥ v)`。 -/
lemma map_mulVec (f : T →+* T') (M : Matrix n n T) (v : n → T) :
    M.map ⇑f *ᵥ (fun j => f (v j)) = fun a => f ((M *ᵥ v) a) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

#print axioms map_mulVec

/-- ★★ **列型 intertwiner 沿环同态运输**：`A(w).map f = A_{g.map f}(f ∘ w)`。 -/
lemma mtuColMat_map (f : T →+* T') (g : n → n → Matrix n n T) (b : n) (w : n → T) :
    (mtuColMat g b w).map ⇑f
      = mtuColMat (fun i j => (g i j).map f) b (fun j => f (w j)) := by
  funext a j
  simp only [mtuColMat, Matrix.of_apply, Matrix.map_apply]
  exact (congrFun (map_mulVec f (g j b) w) a).symm

#print axioms mtuColMat_map

end MapVec

/-! ### 局部环情形的路线与库内 API（第 151 轮侦察，下一轮执行）

设 `T` 局部、`k := IsLocalRing.ResidueField T`、`f := IsLocalRing.residue T`。四步：
① `ḡ := g.map f` 是 `k` 上的矩阵单位组（§6.1）；
② 由第 149 轮的域上结果取 `b, w̄` 使 `det (A_k(w̄)) ≠ 0`；
③ 把 `w̄` 提升为 `w`（`IsLocalRing.residue_surjective`），则
   `f (det (A(w))) = det ((A(w)).map f) = det (A_k(w̄)) ≠ 0`（`mtuColMat_map` ＋ `RingHom.map_det`）
   ⟹ `det (A(w))` 是 `T` 的单位（局部环：**单位 ⟺ 剩余域像非零**）；
④ `A(w)` 是单位（`Matrix.isUnit_iff_isUnit_det`），再用 §4 的交错性得共轭。

**已核实的库内 API**（本轮 `#check` 实测）：
`IsLocalRing.residue R : R →+* ResidueField R`、
`IsLocalRing.residue_surjective : Surjective (residue R)`、
`IsLocalRing.residue_eq_zero_iff (x) : residue R x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R`、
`IsUnit.unit`／`IsUnit.unit_spec`（由 `IsUnit` 取单位）、
`Matrix.isUnit_iff_isUnit_det`。
**单位判据**（`IsUnit x ↔ residue x ≠ 0`）库内无直接件，须由
`residue_eq_zero_iff` ＋ `IsLocalRing.nonunits`（非单位即极大理想）与 `IsUnit.map` 组合。 -/

/-! ## §8 **S5（局部环）收口**：`M_n(T)` 的两组矩阵单位组共轭（`T` 局部）

`thm:14.15` 的原文先把它归约到 `T` **局部**（"any commutative ring embeds in a product of
local rings"），**局部情形才是实质**（一般环上结论是假的，见 §6 头的 Picard 论证）。
本节把局部情形机检。

**证明（照第 151 轮登记的路线，五步）**：
① 单位判据 `IsUnit x ↔ residue x ≠ 0`（本节自建：库内无直接件，由 `residue_eq_zero_iff`
   ＋ `IsLocalRing.mem_maximalIdeal` ＝ 非单位 ＋ `IsUnit.map` 组合）；
② `ḡ := g.map (residue T)` 是剩余域 `k` 上的矩阵单位组（§6）；
③ 由第 149 轮**域上收口**取 `b`、`w̄` 使 `det (A_k(w̄)) ≠ 0`；
④ 把 `w̄` 沿 `residue_surjective` 提升为 `w`，则
   `residue (det A(w)) = det (A(w).map residue) = det (A_k(w̄)) ≠ 0`（`RingHom.map_det`
   ＋ `mtuColMat_map`）⟹ `det A(w)` 是 `T` 的单位；
⑤ `A(w)` 是单位（`Matrix.isUnit_iff_isUnit_det`），用 §4 的交错性消去。

**射程（如实登记）**：本节要求 `[IsLocalRing T]` 与 `[Nonempty n]`。
**一般交换环情形**（`thm:14.15` 的 `T`）需"嵌入局部环之积"的归约，**未做**。 -/

section LocalRing

/-- ★★ **局部环的单位判据**：`x` 可逆 ⟺ 其在剩余域中的像非零。
**库内缺件**（本轮 `#check` 实测：无 `IsLocalRing.isUnit_iff`），由三段组合。 -/
lemma isUnit_iff_residue_ne_zero {T : Type} [CommRing T] [IsLocalRing T] (x : T) :
    IsUnit x ↔ IsLocalRing.residue T x ≠ 0 := by
  constructor
  · intro h h0
    have h1 : IsUnit (IsLocalRing.residue T x) := h.map _
    rw [h0] at h1
    exact not_isUnit_zero h1
  · intro h
    by_contra hnu
    exact h ((IsLocalRing.residue_eq_zero_iff x).mpr
      ((IsLocalRing.mem_maximalIdeal x).mpr hnu))

#print axioms isUnit_iff_residue_ne_zero

/-- ★★★★★ **S5（局部环）收口**：`T` 局部时，`M_n(T)` 中任意矩阵单位组与标准组共轭。

**这是 `[saltman1999lectures, 2.11]` 的实质情形**（原文 `thm:14.15` 证明第二段所引），
也是 (A) 论证层唯一的重型工具。 -/
theorem exists_unit_conj_stdMU_of_isLocalRing {T : Type} [CommRing T] [IsLocalRing T]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {g : n → n → Matrix n n T} (hg : IsMatrixUnitSystem g) :
    ∃ u : (Matrix n n T)ˣ, ∀ i j,
      ((u : Matrix n n T)) * stdMU (R := T) i j
        * ((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) = g i j := by
  classical
  set f := IsLocalRing.residue T with hf
  set gbar : n → n → Matrix n n (IsLocalRing.ResidueField T) :=
    fun i j => (g i j).map f with hgdef
  have hg' : IsMatrixUnitSystem gbar := hg.map f
  obtain ⟨b, hb⟩ := exists_diag_ne_zero hg'
  obtain ⟨wbar, hwbar⟩ := exists_mulVec_ne_zero hb
  choose w hw using fun j => IsLocalRing.residue_surjective (wbar j)
  have hAw : (mtuColMat g b w).map f = mtuColMat gbar b wbar := by
    rw [mtuColMat_map]
    congr 1
    funext j
    exact hw j
  have hdet_ne : f (mtuColMat g b w).det ≠ 0 := by
    rw [RingHom.map_det]
    rw [show f.mapMatrix (mtuColMat g b w) = (mtuColMat g b w).map f from rfl, hAw]
    exact mtuColMat_det_ne_zero hg' b hwbar
  have hunitdet : IsUnit (mtuColMat g b w).det := (isUnit_iff_residue_ne_zero _).mpr hdet_ne
  have hunitA : IsUnit (mtuColMat g b w) := (Matrix.isUnit_iff_isUnit_det _).mpr hunitdet
  refine ⟨hunitA.unit, fun i j => ?_⟩
  have hspec : ((hunitA.unit : (Matrix n n T)ˣ) : Matrix n n T) = mtuColMat g b w :=
    IsUnit.unit_spec hunitA
  have hA : ((hunitA.unit : (Matrix n n T)ˣ) : Matrix n n T) * stdMU (R := T) i j
      = g i j * ((hunitA.unit : (Matrix n n T)ˣ) : Matrix n n T) := by
    rw [hspec]
    exact mtuColMat_intertwines hg b i j w
  rw [hA, mul_assoc,
    show ((hunitA.unit : (Matrix n n T)ˣ) : Matrix n n T)
        * (((hunitA.unit)⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) = 1 from Units.mul_inv _,
    mul_one]

#print axioms exists_unit_conj_stdMU_of_isLocalRing

end LocalRing

/-! ## §9 `thm:14.15` 的分类步（G5）：矩阵单位定标量 ＋ 按矩阵单位分解

`thm:14.15` 的证明有一段尚未机检的推理：`θ` 保**标准矩阵单位** ⟹ `θ = M_n(η)`。
其两块代数基础在本节：

* `matrix_eq_sum_smul_stdMU`：任何矩阵按其**标准矩阵单位**分解 `β = ∑_i∑_j (β i j) • e(i,j)`；
* `eq_smul_one_of_comm_stdMU`：与**全部**标准矩阵单位交换的矩阵必须是**纯量矩阵**
  ——这是"`θ(纯量) 是纯量"的依据（`θ` 保矩阵单位 ⟹ `θ(c•1)` 与所有 `e(i,j)` 交换）。

**下一步**（下一轮）：由这两条得 `θ(c•1) = (η c) • 1`，再用分解得 `θ β = β.map η`。 -/

section Decomp

variable {T : Type} [CommRing T] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★ **按标准矩阵单位分解**：`β = ∑_i ∑_j (β i j) • e(i,j)`。 -/
lemma matrix_eq_sum_smul_stdMU (β : Matrix n n T) :
    β = ∑ i, ∑ j, (β i j) • stdMU (R := T) i j := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, stdMU, Matrix.single_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; simp at h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi]
  · intro h; simp at h

#print axioms matrix_eq_sum_smul_stdMU

/-- ★★★ **与全部标准矩阵单位交换的矩阵是纯量矩阵**。

**证明**：把 `M * e(i,j) = e(i,j) * M` 在条目 `(a,b)` 展开得
`M a i * (if j = b then 1 else 0) = (if i = a then M j b else 0)`；
取 `(i,j) = (a,j)`、条目 `(a,j)` 得对角元全相等；取 `(i,j) = (j,j)`、条目 `(j,b)`（`j ≠ b`）
得非对角元为零。 -/
lemma eq_smul_one_of_comm_stdMU {M : Matrix n n T}
    (h : ∀ i j, M * stdMU (R := T) i j = stdMU (R := T) i j * M) (i₀ : n) :
    M = (M i₀ i₀) • (1 : Matrix n n T) := by
  have key : ∀ (i j a b : n),
      M a i * (if j = b then 1 else 0) = (if i = a then M j b else 0) := by
    intro i j a b
    have hij := congrFun (congrFun (h i j) a) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at hij
    have hL : ∑ c, M a c * stdMU (R := T) i j c b
        = M a i * (if j = b then 1 else 0) := by
      rw [Finset.sum_eq_single i]
      · simp [stdMU, Matrix.single_apply]
      · intro c _ hc; simp [stdMU, Matrix.single_apply, Ne.symm hc]
      · intro hh; simp at hh
    have hR : ∑ c, stdMU (R := T) i j a c * M c b
        = (if i = a then M j b else 0) := by
      rw [Finset.sum_eq_single j]
      · simp [stdMU, Matrix.single_apply]
      · intro c _ hc; simp [stdMU, Matrix.single_apply, Ne.symm hc]
      · intro hh; simp at hh
    rw [hL, hR] at hij
    exact hij
  have hdiag : ∀ a j, M j j = M a a := by
    intro a j
    have h1 := key a j a j
    simpa using h1.symm
  have hoff : ∀ j b, j ≠ b → M j b = 0 := by
    intro j b hjb
    have h1 := key j j j b
    simpa [hjb] using h1.symm
  ext a b
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, mul_one]
    exact (hdiag a i₀).symm
  · rw [ite_eq_right hab, mul_zero]
    exact hoff a b hab

#print axioms eq_smul_one_of_comm_stdMU

end Decomp

/-! ## §10 **G5 分类本体**：保标准矩阵单位的环同态必是 `M_n(η)`

**原文（逐字）**：`raw/Saltman1999ch14.tex:308–310`（`thm:14.15` 证明）：
> Since `θ_1` preserves the standard matrix units, `θ_1` has the form `M_n(η_1)` for
> `η_1 : S → T` a commutative ring homomorphism.

本节把它机检（**不需要 PI 理论**，纯环论）：
`θ : M_n(R) →+* M_n(R')` 若在**标准矩阵单位**上与恒等一致，则存在函数 `η : R → R'`
使得 `θ β = β.map η` 对一切 `β` 成立。

**证明**：由 §9 的两条——
① `θ(c • 1)` 与所有 `θ(e(i,j)) = e(i,j)` 交换 ⟹ 由 `eq_smul_one_of_comm_stdMU` 是**纯量**
`(η c) • 1`，其中 `η c := θ(c • 1) i₀ i₀`；
② 由 `matrix_eq_sum_smul_stdMU` 把 `β` 分解为 `∑_i∑_j (β i j) • e(i,j)`，
逐项用 ①：`θ((β i j) • e(i,j)) = ((β i j) • 1 的像) · e(i,j) = (η (β i j)) • e(i,j)`，
故 `θ β = ∑_i∑_j (η (β i j)) • e(i,j) = β.map η`。 -/

section Classify

variable {R R' : Type} [CommRing R] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★★★★ **`θ` 保标准矩阵单位 ⟹ `θ = M_n(η)`**。

**用途**：`thm:14.15` 证明的第二段——`θ_1 = M_n(η_1)`，以及（对 `θ_2^A` 同样）`θ_2^A = M_n(η_2)`。 -/
theorem exists_eta_of_preserves_stdMU [Nonempty n]
    (θ : Matrix n n R →+* Matrix n n R')
    (hθ : ∀ i j, θ (stdMU (R := R) i j) = stdMU (R := R') i j) :
    ∃ η : R → R', ∀ β : Matrix n n R, θ β = β.map η := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty n›
  refine ⟨fun c => θ (c • (1 : Matrix n n R)) i₀ i₀, fun β => ?_⟩
  have hsc : ∀ c : R,
      θ (c • (1 : Matrix n n R))
        = (θ (c • (1 : Matrix n n R)) i₀ i₀) • (1 : Matrix n n R') := by
    intro c
    apply eq_smul_one_of_comm_stdMU _ i₀
    intro i j
    simp only [← hθ i j, ← map_mul, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul]
  have hL : θ β
      = ∑ i, ∑ j, (θ ((β i j) • (1 : Matrix n n R)) i₀ i₀) • stdMU (R := R') i j := by
    conv_lhs => rw [matrix_eq_sum_smul_stdMU β]
    rw [map_sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (β i j) • stdMU (R := R) i j
        = ((β i j) • (1 : Matrix n n R)) * stdMU (R := R) i j from by
      rw [Matrix.smul_mul, one_mul]]
    rw [map_mul, hsc, hθ i j, Matrix.smul_mul, one_mul]
    simp [Matrix.smul_apply]
  rw [hL, matrix_eq_sum_smul_stdMU (β.map fun c => θ (c • (1 : Matrix n n R)) i₀ i₀)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply]

#print axioms exists_eta_of_preserves_stdMU

end Classify

/-! ## §11 分类（§10）的**分块抽取**：纯量性 ＋ "由纯量决定"

§10 的 `exists_eta_of_preserves_stdMU` 证明里有两块被复用价值很高的东西，本节把它们独立成引理：

* `theta_smul_one_eq_scalar`（原 `hsc`）：`θ(c • 1)` **必是纯量矩阵**；
* `theta_eq_map_scalar`（原 `hL` ＋ 末步）：`θ` 完全由它在纯量矩阵上的作用决定，
  即 `θ β = β.map (c ↦ θ(c • 1)_{i₀i₀})`。

**用途**：任何要把 §10 的结论从"函数 `η`"升级为"`RingHom`／`AlgHom`"的后续工作，
都需要这两块（纯量性给出 `η(c·d) = η c · η d`，因为两个纯量矩阵之积仍是纯量）。

**下一轮（已判明卡点）**：升级为 `AlgHom` 的剩余工作是 `map_mul'`／`map_add'` 的**条目计算**：
重写 `hscA` 会**同时命中右侧**的 `θ(a • 1) i₀ i₀` 子项，把目标搅乱；
需要先 `conv` 限定重写位置或先用 `hsm` 把乘积合并成纯量矩阵再取条目。 -/

section AlgHomClassify

variable {F : Type} [Field F] {R R' : Type} [CommRing R] [CommRing R']
  {n : Type} [Fintype n] [DecidableEq n]

/-- ★★★ **`θ(c • 1)` 必是纯量矩阵**（§10 证明里的 `hsc`）。 -/
lemma theta_smul_one_eq_scalar (θ : Matrix n n R →+* Matrix n n R')
    (hθ : ∀ i j, θ (stdMU (R := R) i j) = stdMU (R := R') i j) (i₀ : n) (c : R) :
    θ (c • (1 : Matrix n n R))
      = (θ (c • (1 : Matrix n n R)) i₀ i₀) • (1 : Matrix n n R') := by
  apply eq_smul_one_of_comm_stdMU _ i₀
  intro i j
  simp only [← hθ i j, ← map_mul, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul]

#print axioms theta_smul_one_eq_scalar

/-- ★★★ **`θ` 由纯量决定**：`θ β = β.map (c ↦ θ(c • 1)_{i₀i₀})`。 -/
lemma theta_eq_map_scalar (θ : Matrix n n R →+* Matrix n n R')
    (hθ : ∀ i j, θ (stdMU (R := R) i j) = stdMU (R := R') i j) (i₀ : n)
    (β : Matrix n n R) :
    θ β = β.map (fun c => θ (c • (1 : Matrix n n R)) i₀ i₀) := by
  have hsc := theta_smul_one_eq_scalar θ hθ i₀
  have hL : θ β
      = ∑ i, ∑ j, (θ ((β i j) • (1 : Matrix n n R)) i₀ i₀) • stdMU (R := R') i j := by
    conv_lhs => rw [matrix_eq_sum_smul_stdMU β]
    rw [map_sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (β i j) • stdMU (R := R) i j
        = ((β i j) • (1 : Matrix n n R)) * stdMU (R := R) i j from by
      rw [Matrix.smul_mul, one_mul]]
    rw [map_mul, hsc, hθ i j, Matrix.smul_mul, one_mul]
    simp [Matrix.smul_apply]
  rw [hL, matrix_eq_sum_smul_stdMU (β.map fun c => θ (c • (1 : Matrix n n R)) i₀ i₀)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply]

#print axioms theta_eq_map_scalar

end AlgHomClassify

/-! ## §12 分类的 **`AlgHom` 版**：保标准矩阵单位的 `F`-代数同态必是 `β ↦ β.map η`

`thm:14.15` 的"粘合"需要从 `θ₁`（`M_n(S) →ₐ[F] M_n(T)`）**产出** `η₁ : S →ₐ[F] T`；
而 §10 的 `exists_eta_of_preserves_stdMU` 只给**函数** `η : R → R'`，
无法直接喂给 `etaExt`／`phiAR`（它们要 `AlgHom`）。本节补上这一点。

**证明**：仍取 `η c := θ (c • 1) i₀ i₀`，用 §11 的 `theta_smul_one_eq_scalar` 得纯量性，
再由"两个纯量矩阵之积／和仍纯量"得 `map_mul'`／`map_add'`；
`∀ β, θ β = β.map η` 直接引 §11 的 `theta_eq_map_scalar`。 -/

section AlgHomClassify

variable {F : Type} [Field F] {R R' : Type} [CommRing R] [CommRing R']
  [Algebra F R] [Algebra F R'] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- ★★★★★ **分类的 `AlgHom` 版**：`θ : M_n(R) →ₐ[F] M_n(R')` 保标准矩阵单位 ⟹
存在 `η : R →ₐ[F] R'` 使 `θ β = β.map η` 对一切 `β` 成立。 -/
theorem exists_algHom_of_preserves_stdMU (θ : Matrix n n R →ₐ[F] Matrix n n R')
    (hθ : ∀ i j, θ (stdMU (R := R) i j) = stdMU (R := R') i j) :
    ∃ η : R →ₐ[F] R', ∀ β : Matrix n n R, θ β = β.map η := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hθ' : ∀ i j, (θ : Matrix n n R →+* Matrix n n R') (stdMU (R := R) i j)
      = stdMU (R := R') i j := hθ
  have hscA : ∀ c : R, θ (c • (1 : Matrix n n R))
      = (θ (c • (1 : Matrix n n R)) i₀ i₀) • (1 : Matrix n n R') :=
    fun c => theta_smul_one_eq_scalar (θ : Matrix n n R →+* Matrix n n R') hθ' i₀ c
  refine ⟨{ toFun := fun c => θ (c • (1 : Matrix n n R)) i₀ i₀
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_
            commutes' := ?_ }, fun β => theta_eq_map_scalar _ hθ' i₀ β⟩
  · show θ ((1 : R) • (1 : Matrix n n R)) i₀ i₀ = 1
    rw [one_smul, map_one]
    simp [Matrix.one_apply]
  · intro a b
    set ca := θ (a • (1 : Matrix n n R)) i₀ i₀ with hca
    set cb := θ (b • (1 : Matrix n n R)) i₀ i₀ with hcb
    have hca' : θ (a • (1 : Matrix n n R)) = ca • (1 : Matrix n n R') := hscA a
    have hcb' : θ (b • (1 : Matrix n n R)) = cb • (1 : Matrix n n R') := hscA b
    have key : θ ((a * b) • (1 : Matrix n n R)) = (ca * cb) • (1 : Matrix n n R') := by
      rw [show (a * b) • (1 : Matrix n n R)
          = ((a • (1 : Matrix n n R)) * (b • (1 : Matrix n n R))) from by
        rw [Matrix.smul_mul, one_mul, ← mul_smul], map_mul, hca', hcb',
        Matrix.smul_mul, one_mul, ← mul_smul]
    show θ ((a * b) • (1 : Matrix n n R)) i₀ i₀ = ca * cb
    rw [key, Matrix.smul_apply, Matrix.one_apply, ite_eq_left rfl, smul_eq_mul, mul_one]
  · show θ ((0 : R) • (1 : Matrix n n R)) i₀ i₀ = 0
    rw [zero_smul, map_zero]
    simp
  · intro a b
    set ca := θ (a • (1 : Matrix n n R)) i₀ i₀ with hca
    set cb := θ (b • (1 : Matrix n n R)) i₀ i₀ with hcb
    have hca' : θ (a • (1 : Matrix n n R)) = ca • (1 : Matrix n n R') := hscA a
    have hcb' : θ (b • (1 : Matrix n n R)) = cb • (1 : Matrix n n R') := hscA b
    have key : θ ((a + b) • (1 : Matrix n n R)) = (ca + cb) • (1 : Matrix n n R') := by
      rw [add_smul, map_add, hca', hcb', add_smul]
    show θ ((a + b) • (1 : Matrix n n R)) i₀ i₀ = ca + cb
    rw [key, Matrix.smul_apply, Matrix.one_apply, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro c
    have e1 : θ ((algebraMap F R c) • (1 : Matrix n n R)) = algebraMap F (Matrix n n R') c := by
      rw [← Algebra.algebraMap_eq_smul_one (A := Matrix n n R) (algebraMap F R c),
        ← IsScalarTower.algebraMap_apply F R (Matrix n n R) c, θ.commutes]
    show θ ((algebraMap F R c) • (1 : Matrix n n R)) i₀ i₀ = algebraMap F R' c
    rw [e1]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

#print axioms exists_algHom_of_preserves_stdMU

end AlgHomClassify

end Procesi
