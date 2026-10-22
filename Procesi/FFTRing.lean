/-
  Procesi —— **FFT 环层（缺口 #4 第一件）**：迹单项式与迹代数（第 556 轮）

  缺口 #4（AGPR `thm:12.1.3`）的陈述是**环**陈述：「不变量环由 `tr(单项式)` 生成」。本节给
  「迹单项式」与「迹代数」的**定义载体**（此前仓内 `Matrix.trace` 在 `GenericInv` 中出现 0 次）。

  取值域说明：`genMatKF F r n k : Matrix (Fin n) (Fin n) (SField F r n)`（`GenericInv.lean:2657`），
  故迹落在 `SField F r n = FractionRing (S F r n)`（`KAction.lean:30`）里，而
  `S F r n = MvPolynomial (Fin r × Fin n × Fin n) F`（`PGL.lean:39`）是多项式环。

  **射程**：本节只给**定义与最简成员引理**。迹的不变性、极化／复原、以及「不动点 ⊆ 迹代数」
  （＝ `thm:12.1.3` 的实体）**均未做**；`S'^N ⊆ Z` 未证；H2 仍不是定理。
-/
import Procesi.GenericInv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial

namespace Procesi

variable (F : Type) [Field F] (r n : ℕ)

/-- **迹单项式集合**：`tr(genMat k₁ ⋯ k_m)`，`w : List (Fin r)`（空表给 `tr 1 = n`，与常数迹一致）。 -/
noncomputable def traceMonoSet : Set (SField F r n) :=
  Set.range (fun w : List (Fin r) => (w.map (genMatKF F r n)).prod.trace)

/-- 迹单项式的显式形态。 -/
theorem traceMonoSet_def (w : List (Fin r)) :
    (w.map (genMatKF F r n)).prod.trace ∈ traceMonoSet F r n :=
  ⟨w, rfl⟩

#print axioms traceMonoSet
#print axioms traceMonoSet_def

/-- ★★★★ **迹代数**：由迹单项式生成的 `F`-子代数（缺口 #4 的目标环）。 -/
noncomputable def traceAlg : Subalgebra F (SField F r n) :=
  Algebra.adjoin F (traceMonoSet F r n)

#print axioms traceAlg

/-- 生成元落在迹代数里。 -/
theorem traceMonoSet_subset_traceAlg :
    traceMonoSet F r n ⊆ (traceAlg F r n : Set (SField F r n)) :=
  Algebra.subset_adjoin

#print axioms traceMonoSet_subset_traceAlg

/-- ★★★★★ **迹单项式的乘积矩阵被 `psiK` 逐点固定**（缺口 #4 环层第 2 步）。

`psiK_genericMatrix`（`GenericInv.lean:2661`）给「泛矩阵**逐个**固定」；乘积由 `map_mul` 逐段传递。
**注意**：`psiK` 作用在**矩阵**上（`Matrix … →+* Matrix …`，`GenericInv.lean:2580`），不在标量上——
故不变性的正确陈述在矩阵层；「迹不变」由此直接得到（迹读的是这个被固定的矩阵）。

**射程**：本节只给**矩阵层不变性**。迹代数的**不变性**（`traceAlg ≤ psiK`-不动点，含常数与和／积封闭）、
极化／复原、以及「不动点 ⊆ 迹代数」（＝ `thm:12.1.3` 实体）**均未做**。 -/
theorem psiK_prod_genMat (A : (Matrix (Fin n) (Fin n) F)ˣ) (w : List (Fin r)) :
    psiK F r n A ((w.map (genMatKF F r n)).prod) = (w.map (genMatKF F r n)).prod := by
  induction w with
  | nil => simp
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, psiK_genericMatrix, ih]

#print axioms psiK_prod_genMat

/-! ## 切分第 3 步（Newton 恒等式）的载体：幂迹 `p_k = tr (M^k)`

`H2Final` 的切分计划（`:9628`）把缺口 #4 的下一步定为「Newton 恒等式：`tr(M^k)` 决定特征系数」。
**全库检索读数（第 561 轮）**：`Newton`／`elemSym`／`charCoeff` 在 `Procesi/*.lean` 中**均 0 次命中**
（`charpoly` 一族只被 `GenericInv` 的 `discr` 线用到）⟹ 这一步是**真新件**，须自建。

本节先给该步的**输入载体**（幂迹）与两条 rfl 级定律；Newton 恒等式本身**未做**。 -/

/-- **幂迹**：`p_k(M) := tr (M ^ k)` —— Newton 恒等式的输入。 -/
noncomputable def powTrace (M : Matrix (Fin n) (Fin n) (SField F r n)) (k : ℕ) : SField F r n :=
  (M ^ k).trace

#print axioms powTrace

/-- `p_0 = n`（`tr 1 = n`）。 -/
theorem powTrace_zero (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    powTrace F r n M 0 = (n : SField F r n) := by
  simp [powTrace]

#print axioms powTrace_zero

/-- `p_{k+1} = tr (M^k * M)`。 -/
theorem powTrace_succ (M : Matrix (Fin n) (Fin n) (SField F r n)) (k : ℕ) :
    powTrace F r n M (k + 1) = (M ^ k * M).trace := by
  simp [powTrace, pow_succ]

#print axioms powTrace_succ

/-- 被 `psiK` 固定的矩阵，其任意幂也被固定（`map_pow`）。 -/
theorem psiK_pow_of_fixed (A : (Matrix (Fin n) (Fin n) F)ˣ)
    {M : Matrix (Fin n) (Fin n) (SField F r n)} (h : psiK F r n A M = M) (m : ℕ) :
    psiK F r n A (M ^ m) = M ^ m := by
  rw [map_pow, h]

#print axioms psiK_pow_of_fixed

/-- ★★★★★ **Newton 步的输入封闭性**：字积的任意幂仍被 `psiK` 固定
（故幂迹 `p_m(M_w) = tr(M_w ^ m)` 的输入仍在不变世界里）。

**为何需要**：切分第 3 步的 Newton 恒等式以 `p_m = tr(M^m)` 为输入；对**字积** `M_w` 而言，
`M_w ^ m` 仍是同一批泛矩阵的字积之幂，故其不变性由 §557 逐段传递。 -/
theorem psiK_pow_prod_genMat (A : (Matrix (Fin n) (Fin n) F)ˣ) (w : List (Fin r)) (m : ℕ) :
    psiK F r n A (((w.map (genMatKF F r n)).prod) ^ m)
      = ((w.map (genMatKF F r n)).prod) ^ m :=
  psiK_pow_of_fixed F r n A (psiK_prod_genMat F r n A w) m

#print axioms psiK_pow_prod_genMat

/-- ★★★★★ **Newton 恒等式的 k=1 实例**：`p_1 = tr M = -c_1`（`c_1 = M.charpoly.coeff (n-1)`）。

这是切分第 3 步（Newton）的**第一格**：Mathlib 的 `Matrix.trace_eq_neg_charpoly_coeff` 直接给出
`tr M = -charpoly.coeff (card n - 1)`，此处用 `p_1 = tr (M^1) = tr M` 落成幂迹语言。 -/
theorem powTrace_one (hn : 0 < n) (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    powTrace F r n M 1 = -M.charpoly.coeff (n - 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [powTrace, pow_one, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]

#print axioms powTrace_one

/-- ★★★★ **迹-Cayley–Hamilton**：`tr(aeval M charpoly) = 0` —— Newton 递推的源头。 -/
theorem trace_aeval_self_charpoly (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (Polynomial.aeval M M.charpoly).trace = 0 := by
  rw [Matrix.aeval_self_charpoly, Matrix.trace_zero]

#print axioms trace_aeval_self_charpoly

/-- **带幂的形态**：`tr(aeval M charpoly * M^k) = 0` —— Newton 一般步的左边
（把 `aeval M charpoly = Σ c_j M^j` 展开后即得幂迹递推 `Σ c_j p_{j+k} = 0`）。 -/
theorem trace_aeval_self_charpoly_mul_pow (M : Matrix (Fin n) (Fin n) (SField F r n)) (k : ℕ) :
    ((Polynomial.aeval M M.charpoly) * M ^ k).trace = 0 := by
  rw [Matrix.aeval_self_charpoly, Matrix.zero_mul, Matrix.trace_zero]

#print axioms trace_aeval_self_charpoly_mul_pow

/-- ★★★★★★ **幂迹递推（Newton 一般步的左边）**：
`Σ_j c_j · tr(M^j * M^k) = 0`，其中 `c_j = charpoly.coeff j`。
把 `aeval M charpoly = Σ_j c_j • M^j` 代入迹-Cayley–Hamilton 即得。 -/
theorem charpoly_powTrace_recurrence (M : Matrix (Fin n) (Fin n) (SField F r n)) (k : ℕ) :
    (∑ j ∈ Finset.range (M.charpoly.natDegree + 1),
        M.charpoly.coeff j * (M ^ j * M ^ k).trace) = 0 := by
  have h := trace_aeval_self_charpoly_mul_pow F r n M k
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul] at h
  simpa only [Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using h

#print axioms charpoly_powTrace_recurrence

/-- ★★★★ **Newton 递推的 `k = 0` 形态**（显式 `n+1` 项）：`Σ_{j ≤ n} c_j · p_j = 0`
（`p_j = tr (M^j)`）——三角系统的第一行。 -/
theorem charpoly_powTrace_sum_zero (hn : 0 < n) (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (∑ j ∈ Finset.range (n + 1), M.charpoly.coeff j * powTrace F r n M j) = 0 := by
  have h := charpoly_powTrace_recurrence F r n M 0
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  simpa only [powTrace, pow_zero, mul_one] using h

#print axioms charpoly_powTrace_sum_zero

/-- ★★★★★ **Newton `k=0` 方程的规范形（全程 `trace` 语言，无 `powTrace`）**：
`c_d · tr(M^d) + Σ_{j<d} c_j · tr(M^j) = 0`，`d = natDegree = n`，`c_d = 1`。 -/
theorem charpoly_trace_natDegree_add_sum (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    M.charpoly.coeff M.charpoly.natDegree * (M ^ M.charpoly.natDegree).trace
      + (∑ j ∈ Finset.range M.charpoly.natDegree,
          M.charpoly.coeff j * (M ^ j).trace) = 0 := by
  have h := charpoly_powTrace_recurrence F r n M 0
  rw [Finset.sum_range_succ] at h
  simp only [pow_zero, mul_one] at h
  rw [add_comm] at h
  simpa only [M.charpoly_monic.coeff_natDegree, one_mul] using h

#print axioms charpoly_trace_natDegree_add_sum

/-- `powTrace` 与 `trace` 的桥（**同层语言**的接口件；避免 §568 的展开方向陷阱）。 -/
theorem powTrace_eq_trace_pow (M : Matrix (Fin n) (Fin n) (SField F r n)) (j : ℕ) :
    powTrace F r n M j = (M ^ j).trace := rfl

#print axioms powTrace_eq_trace_pow

/-- **系数消失律**：`j > natDegree` 时 `charpoly.coeff j = 0`
（解决 §567 的 `n ↔ natDegree` 搬运问题的正解：不求搬运指标，而让越界系数归零）。 -/
theorem charpoly_coeff_eq_zero_of_natDegree_lt (M : Matrix (Fin n) (Fin n) (SField F r n))
    {j : ℕ} (h : M.charpoly.natDegree < j) : M.charpoly.coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt h

#print axioms charpoly_coeff_eq_zero_of_natDegree_lt

/-- 两个指标语言的和一致（`range (n+1)` ＝ `range (natDegree+1)`，因 `natDegree = n`）——
三角反解里在两套指标语言之间搬运的接口件。 -/
theorem charpoly_trace_sum_range_congr (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (∑ j ∈ Finset.range (n + 1), M.charpoly.coeff j * (M ^ j).trace)
      = ∑ j ∈ Finset.range (M.charpoly.natDegree + 1),
          M.charpoly.coeff j * (M ^ j).trace := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

#print axioms charpoly_trace_sum_range_congr

/-- ★★★★★ **Newton 恒等式的最低非平凡实例（2×2）**：`2 c₀ = (tr M)² − tr(M²)`。 -/
theorem newton_two (M : Matrix (Fin 2) (Fin 2) (SField F r 2)) :
    2 * M.charpoly.coeff 0 = M.trace ^ 2 - (M ^ 2).trace := by
  have h := charpoly_powTrace_sum_zero F r 2 (by norm_num) M
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have hp0 : powTrace F r 2 M 0 = 2 := by rw [powTrace_zero]; norm_num
  have hp1 : powTrace F r 2 M 1 = M.trace := by rw [powTrace_eq_trace_pow, pow_one]
  have hp2 : powTrace F r 2 M 2 = (M ^ 2).trace := powTrace_eq_trace_pow F r 2 M 2
  have hc2 : M.charpoly.coeff 2 = 1 := by rw [Matrix.charpoly_fin_two]; simp
  have hc1 : M.charpoly.coeff 1 = -M.trace := by
    have h1 := powTrace_one F r 2 (by norm_num) M
    rw [powTrace_eq_trace_pow, pow_one] at h1
    rw [show (2 - 1 : ℕ) = 1 from rfl] at h1
    exact neg_eq_iff_eq_neg.mp h1.symm
  rw [hp0, hp1, hp2, hc2, hc1] at h
  ring_nf at h ⊢
  linear_combination h

#print axioms newton_two

/-- ★★★★★ **一般 `n` 的 Newton 关系（`k=0` 格）**：
`tr(M^d) = -Σ_{j<d} c_j · tr(M^j)`，`d = charpoly.natDegree`（用了首一性 `c_d = 1`）。 -/
theorem powTrace_natDegree_eq_neg_sum (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (M ^ M.charpoly.natDegree).trace
      = -(∑ j ∈ Finset.range M.charpoly.natDegree,
          M.charpoly.coeff j * (M ^ j).trace) := by
  have h := charpoly_trace_natDegree_add_sum F r n M
  rw [M.charpoly_monic.coeff_natDegree, one_mul] at h
  linear_combination h

#print axioms powTrace_natDegree_eq_neg_sum

/-- ★★★★★ **一般 `n` 的 Newton 关系（`k=1` 格）**：
`tr(M^{d+1}) = -Σ_{j<d} c_j · tr(M^{j+1})`。 -/
theorem powTrace_succ_natDegree_eq_neg_sum (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (M ^ (M.charpoly.natDegree + 1)).trace
      = -(∑ j ∈ Finset.range M.charpoly.natDegree,
          M.charpoly.coeff j * (M ^ (j + 1)).trace) := by
  have h := charpoly_powTrace_recurrence F r n M 1
  rw [Finset.sum_range_succ] at h
  simp only [pow_one, ← pow_succ, M.charpoly_monic.coeff_natDegree, one_mul] at h
  linear_combination h

#print axioms powTrace_succ_natDegree_eq_neg_sum

/-- ★★★★★★ **Newton 关系的统一形态**：`tr(M^{d+k}) = -Σ_{j<d} c_j · tr(M^{j+k})`（任意 `k`）。 -/
theorem powTrace_add_natDegree_eq_neg_sum (M : Matrix (Fin n) (Fin n) (SField F r n)) (k : ℕ) :
    (M ^ (M.charpoly.natDegree + k)).trace
      = -(∑ j ∈ Finset.range M.charpoly.natDegree,
          M.charpoly.coeff j * (M ^ (j + k)).trace) := by
  have h := charpoly_powTrace_recurrence F r n M k
  rw [Finset.sum_range_succ] at h
  simp only [← pow_add, M.charpoly_monic.coeff_natDegree, one_mul] at h
  linear_combination h

#print axioms powTrace_add_natDegree_eq_neg_sum

/-- ★★★★ **`p₀ = d`（`natDegree` 语言）**：`tr 1 = charpoly.natDegree`。
消元时 `c₀` 的系数就是它（`c₀·p₀ = d·c₀`）。 -/
theorem trace_one_eq_natDegree (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (1 : Matrix (Fin n) (Fin n) (SField F r n)).trace
      = (M.charpoly.natDegree : SField F r n) := by
  rw [Matrix.trace_one, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

#print axioms trace_one_eq_natDegree

/-- ★★★★★ **Newton 第一恒等式（一般 `n`）**：`c_{n-1} = −p₁ = −tr M`。 -/
theorem charpoly_coeff_pred (hn : 0 < n) (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    M.charpoly.coeff (n - 1) = -M.trace := by
  have h1 := powTrace_one F r n hn M
  rw [powTrace_eq_trace_pow, pow_one] at h1
  exact neg_eq_iff_eq_neg.mp h1.symm

#print axioms charpoly_coeff_pred

/-! ## 切分第 4 步（Cramer 消元）：Newton 关系的 Hankel 系统形态

`thm:14.4.4` 只需**分式域**陈述（AGPR `raw/AGPR2020.tex:16770`：「The field 𝒵 is the field of
fractions of the ring `T`」），故不必做 `e_k` 形式的 Newton 恒等式。取而代之：

* `powTrace_add_natDegree_eq_neg_sum`（第 580 轮）给 `tr(M^{n+k}) = -Σ_{j<n} c_j tr(M^{j+k})`
  （任意 `k`）——这正是 **Hankel 线性系统** `H · c = −p_high`，其中 `H_{jk} = tr(M^{j+k})`
  的每一项都是**迹**。
* 本节给出该系统的载体（`hankelMat`）、矩阵形式（`hankelMat_mulVec_coeff`）、
  伴随形态的 Cramer 消元（`hankel_det_smul_coeff`）与除法形态（`charpoly_coeff_eq_neg_cramer_div`）。

**射程**：本节只做**线性代数**（Cramer），**不**证明 `H.det ≠ 0`（Hankel 非退化，即 `charpoly`
可分性；AGPR `thm:12.1.3` 的下一步），也**不**做向 `Spr` 世界的表述对齐。
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★ **Cramer 法则（伴随形态，不需可逆性）**：`A *ᵥ x = b → A.det • x = A.cramer b`。

数学库只有 `Matrix.mulVec_cramer : A *ᵥ A.cramer b = A.det • b`（**反方向**）与
`Matrix.det_smul_inv_mulVec_eq_cramer`（需 `IsUnit A.det`）；本件给**不需可逆性**的正方向，
代价是左端留 `A.det •` 因子——正是本战役第 ② 步所需的形态。 -/
theorem matrix_det_smul_eq_cramer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (A : Matrix ι ι R) (b x : ι → R) (h : A.mulVec x = b) :
    A.det • x = A.cramer b := by
  calc A.det • x
      = (A.adjugate * A).mulVec x := by
        rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = A.adjugate.mulVec (A.mulVec x) := (Matrix.mulVec_mulVec x A.adjugate A).symm
    _ = A.adjugate.mulVec b := by rw [h]
    _ = A.cramer b := (Matrix.cramer_eq_adjugate_mulVec A b).symm

#print axioms matrix_det_smul_eq_cramer

/-- **Hankel 矩阵**：`H_{jk} = tr(M^{j+k})`。`H` 是迹形式 `(X,Y) ↦ tr(XY)` 在
`1, M, …, M^{n−1}` 上的 Gram 矩阵。 -/
noncomputable def hankelMat (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    Matrix (Fin n) (Fin n) (SField F r n) :=
  Matrix.of fun j k => (M ^ (j.val + k.val)).trace

#print axioms hankelMat

/-- ★★★★★ **Newton 关系的 Hankel 线性系统形态**：`H · c = −p_high`，
即 `Σ_{j<n} c_j tr(M^{j+k}) = − tr(M^{n+k})`（`k = 0..n−1`，`c_j = charpoly.coeff j`）。
由 `powTrace_add_natDegree_eq_neg_sum`（任意 `k`）逐分量读出。 -/
theorem hankelMat_mulVec_coeff (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (hankelMat F r n M).mulVec (fun j : Fin n => M.charpoly.coeff j.val)
      = fun k : Fin n => -(M ^ (M.charpoly.natDegree + k.val)).trace := by
  have hd : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  funext k
  have h := powTrace_add_natDegree_eq_neg_sum F r n M k.val
  rw [hd] at h
  have hmul : (hankelMat F r n M).mulVec (fun j : Fin n => M.charpoly.coeff j.val) k
      = ∑ j : Fin n, (M ^ (k.val + j.val)).trace * M.charpoly.coeff j.val := by
    simp [hankelMat, Matrix.mulVec, dotProduct]
  rw [hmul, hd]
  have h3 : -(M ^ (n + k.val)).trace
      = ∑ j ∈ Finset.range n, M.charpoly.coeff j * (M ^ (j + k.val)).trace := by
    rw [h, neg_neg]
  rw [h3]
  have h2 : (∑ j : Fin n, (M ^ (k.val + j.val)).trace * M.charpoly.coeff j.val)
      = ∑ j ∈ Finset.range n, (M ^ (j + k.val)).trace * M.charpoly.coeff j := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (M ^ (j + k.val)).trace * M.charpoly.coeff j) n]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm k.val j.val]
  rw [h2]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

#print axioms hankelMat_mulVec_coeff

/-- ★★★★★ **Cramer 消元（Hankel 形态）**：`H.det • c = −H.cramer p_high`，
`p_high k = tr(M^{n+k})`。用伴随形态，**不假设 `H.det` 可逆**。 -/
theorem hankel_det_smul_coeff (M : Matrix (Fin n) (Fin n) (SField F r n)) :
    (hankelMat F r n M).det • (fun j : Fin n => M.charpoly.coeff j.val)
      = -((hankelMat F r n M).cramer
          (fun k : Fin n => (M ^ (M.charpoly.natDegree + k.val)).trace)) := by
  have h := matrix_det_smul_eq_cramer (hankelMat F r n M)
    (fun k : Fin n => -(M ^ (M.charpoly.natDegree + k.val)).trace)
    (fun j : Fin n => M.charpoly.coeff j.val)
    (hankelMat_mulVec_coeff F r n M)
  have hneg : (hankelMat F r n M).cramer
      (fun k : Fin n => -(M ^ (M.charpoly.natDegree + k.val)).trace)
      = -((hankelMat F r n M).cramer
          (fun k : Fin n => (M ^ (M.charpoly.natDegree + k.val)).trace)) :=
    map_neg _ _
  rwa [hneg] at h

#print axioms hankel_det_smul_coeff

/-- ★★★★★★ **`c_j` 的 Cramer 表达**：`c_j = −(H.cramer p_high)_j / H.det`。

右端分子与分母的每一项都是 `tr(M^m)`（`H` 的项是 `tr(M^{j+k})`，`p_high` 的项是 `tr(M^{n+k})`，
`H.cramer` 只是行列式），故只要 `H.det ≠ 0`，`c_j` 就是**迹的有理函数**——
这正是 `thm:14.4.4` 分式域陈述所需的形态。 -/
theorem charpoly_coeff_eq_neg_cramer_div
    (M : Matrix (Fin n) (Fin n) (SField F r n)) (hdet : (hankelMat F r n M).det ≠ 0)
    (j : Fin n) :
    M.charpoly.coeff j.val
      = -((hankelMat F r n M).cramer
            (fun k : Fin n => (M ^ (M.charpoly.natDegree + k.val)).trace)) j
          / (hankelMat F r n M).det := by
  have h := hankel_det_smul_coeff F r n M
  have h2 : (hankelMat F r n M).det * M.charpoly.coeff j.val
      = -((hankelMat F r n M).cramer
            (fun k : Fin n => (M ^ (M.charpoly.natDegree + k.val)).trace)) j := by
    have := congrFun h j
    simpa [Pi.smul_apply, smul_eq_mul] using this
  rw [eq_div_iff hdet, mul_comm]
  exact h2

#print axioms charpoly_coeff_eq_neg_cramer_div


open scoped Matrix

/-! ## 切分第 5 步：Hankel **非退化**（第 ① 步收口）＋ `c_j` 的迹代数**分式形态**

第 ②／③ 步（`hankelMat_mulVec_coeff`／`charpoly_coeff_eq_neg_cramer_div`）给出
`c_j = −(H.cramer p_high)_j / H.det`，其中分子与分母的每一项都是迹。还剩**一件**：
`H.det ≠ 0`（＝ `charpoly` 可分，Hankel 非退化）。本节收口它，并把「分子／分母都是迹」
升级为「`H.det` 与 `H.cramer p_high` 的每个分量都落在**迹代数** `traceAlg` 里」，
于是 `c_j` 是迹代数的**分式**（AGPR `thm:14.4.4` 的分式域陈述在环层的分量形态）。

`H.det ≠ 0` 的路线（＝ `GenericInv` §66 `discr_genMatKF_ne_zero` 的**同一路线**，
源文 Saltman `:400`「By choosing `φ` properly」）：
特殊化 `specHom` 把 `x_{ij,k₀}` 送到 `δ_{ij} t_i`、其余变量送到 `0`
（`genericMatrix_map_specHom`），于是 `X_{k₀}` 变成**互异对角**矩阵；其 Hankel 矩阵
`= Vᵀ V`（`V = Matrix.vandermonde d`）⟹ `det = (det V)²`，由
`Matrix.det_vandermonde_ne_zero_iff` 与 `d` 单射得非零。

**射程**：本节只做**环层／分式层**。缺口 #4 的**还剩下**：把 `∈ Frac(traceAlg)` 搬到
`Spr` 世界（沿 `sprToSField`，方向 Spr→S，需单射性回推——**禁止直送**）；
FFT 的「不变量 = 迹代数」整步（极化／复原）；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

-- ============ 件 ①：互异对角元的 Hankel 行列式 ≠ 0（纯域层） ============
/-- ★★★★★ **互异对角元的 Hankel 行列式 ≠ 0**：`det (Σ_i d_i^{j+k}) ≠ 0`。 -/
theorem hankel_of_injective_det_ne_zero {n : ℕ} {K : Type*} [Field K] (d : Fin n → K)
    (hd : Function.Injective d) :
    (Matrix.of fun j k : Fin n => ∑ i : Fin n, d i ^ (j.val + k.val)).det ≠ 0 := by
  have hVV : (Matrix.of fun j k : Fin n => ∑ i : Fin n, d i ^ (j.val + k.val))
      = (Matrix.vandermonde d)ᵀ * Matrix.vandermonde d := by
    ext j k
    simp [Matrix.mul_apply, pow_add]
  rw [hVV, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hd)
    (Matrix.det_vandermonde_ne_zero_iff.mpr hd)

#print axioms hankel_of_injective_det_ne_zero

-- ============ 件 ②：多项式层（S 上）通用矩阵的 Hankel 行列式 ≠ 0 ============
/-- ★★★★★ **`S` 上通用矩阵的 Hankel 行列式 ≠ 0**（第 ① 步的主体）。 -/
theorem det_hankel_genericMatrix_ne_zero (k₀ : Fin r) :
    (Matrix.of fun j k : Fin n =>
        ((genericMatrix F r n k₀) ^ (j.val + k.val)).trace).det ≠ 0 := by
  have hmap : (Matrix.of fun j k : Fin n =>
        ((genericMatrix F r n k₀) ^ (j.val + k.val)).trace).map ⇑(specHom F r n k₀)
      = Matrix.of fun j k : Fin n => ∑ i : Fin n, specDiag F n i ^ (j.val + k.val) := by
    ext j k
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [AddMonoidHom.map_trace (specHom F r n k₀), ← AlgHom.mapMatrix_apply, map_pow,
      AlgHom.mapMatrix_apply, genericMatrix_map_specHom, Matrix.diagonal_pow,
      Matrix.trace_diagonal]
    rfl
  intro h
  have h1 : ((specHom F r n k₀).mapMatrix (Matrix.of fun j k : Fin n =>
      ((genericMatrix F r n k₀) ^ (j.val + k.val)).trace)).det = 0 := by
    rw [← AlgHom.map_det, h, map_zero]
  rw [AlgHom.mapMatrix_apply, hmap] at h1
  exact hankel_of_injective_det_ne_zero (specDiag F n) (specDiag_injective F n) h1

#print axioms det_hankel_genericMatrix_ne_zero

-- ============ 件 ③：SField 层（第 ① 步的终点） ============
/-- ★★★★★★ **`K = SField` 上通用矩阵的 `hankelMat` 行列式 ≠ 0**（第 ① 步收口）。 -/
theorem hankelMat_genMatKF_det_ne_zero (k₀ : Fin r) :
    (hankelMat F r n (genMatKF F r n k₀)).det ≠ 0 := by
  have hmap : (Matrix.of fun j k : Fin n =>
        ((genericMatrix F r n k₀) ^ (j.val + k.val)).trace).map
          ⇑(algebraMap (S F r n) (SField F r n))
      = hankelMat F r n (genMatKF F r n k₀) := by
    ext j k
    simp only [Matrix.map_apply, Matrix.of_apply, hankelMat]
    rw [AddMonoidHom.map_trace (algebraMap (S F r n) (SField F r n)),
      ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply,
      show (genericMatrix F r n k₀).map ⇑(algebraMap (S F r n) (SField F r n))
        = genMatKF F r n k₀ from rfl]
  intro h
  have h1 : algebraMap (S F r n) (SField F r n)
      ((Matrix.of fun j k : Fin n =>
        ((genericMatrix F r n k₀) ^ (j.val + k.val)).trace).det) = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, h]
  exact det_hankel_genericMatrix_ne_zero F r n k₀
    (IsFractionRing.injective (S F r n) (SField F r n) (by rw [h1, map_zero]))

#print axioms hankelMat_genMatKF_det_ne_zero

-- ============ 件 ④：幂迹落在迹代数里 ============
/-- ★★★★★ **`tr(M^m) ∈ traceAlg`**（`M = genMatKF k₀`）：幂迹落在迹代数里
（`M^m` 是「字」`replicate m k₀` 的积）。 -/
theorem trace_pow_genMatKF_mem_traceAlg (k₀ : Fin r) (m : ℕ) :
    ((genMatKF F r n k₀) ^ m).trace ∈ traceAlg F r n := by
  have h : ((List.replicate m k₀).map (genMatKF F r n)).prod
      = (genMatKF F r n k₀) ^ m := by
    rw [List.map_replicate, List.prod_replicate]
  rw [← h]
  exact traceMonoSet_subset_traceAlg F r n (traceMonoSet_def F r n _)

#print axioms trace_pow_genMatKF_mem_traceAlg

-- ============ 件 ⑤：子代数对行列式封闭 ============
/-- ★★★★ **子代数对行列式封闭**：元素都在 `T` 里的矩阵，其行列式也在 `T` 里。 -/
theorem det_mem_subalgebra {T : Subalgebra F (SField F r n)}
    (A : Matrix (Fin n) (Fin n) (SField F r n)) (h : ∀ i j, A i j ∈ T) : A.det ∈ T := by
  set A' : Matrix (Fin n) (Fin n) ↥T := Matrix.of (fun i j => ⟨A i j, h i j⟩) with hA'
  have hmap : A'.map ⇑(algebraMap ↥T (SField F r n)) = A := by
    ext i j
    simp [hA']
  rw [← hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact A'.det.2

#print axioms det_mem_subalgebra

-- ============ 件 ⑥：H.det 与 H.cramer 的迹代数成员性 ============
/-- ★★★★★ **`H.det ∈ traceAlg`**。 -/
theorem hankelMat_det_mem_traceAlg (k₀ : Fin r) :
    (hankelMat F r n (genMatKF F r n k₀)).det ∈ traceAlg F r n :=
  det_mem_subalgebra F r n _ (fun _ _ => trace_pow_genMatKF_mem_traceAlg F r n k₀ _)

#print axioms hankelMat_det_mem_traceAlg

/-- ★★★★★ **`H.cramer p_high` 的每个分量 ∈ traceAlg**。 -/
theorem cramer_powHigh_mem_traceAlg (k₀ : Fin r) (j : Fin n) :
    ((hankelMat F r n (genMatKF F r n k₀)).cramer (fun k : Fin n =>
        ((genMatKF F r n k₀) ^ ((genMatKF F r n k₀).charpoly.natDegree + k.val)).trace)) j
      ∈ traceAlg F r n := by
  rw [Matrix.cramer_apply]
  refine det_mem_subalgebra F r n _ (fun i k' => ?_)
  rw [Matrix.updateCol_apply]
  split
  · exact trace_pow_genMatKF_mem_traceAlg F r n k₀ _
  · exact trace_pow_genMatKF_mem_traceAlg F r n k₀ _

#print axioms cramer_powHigh_mem_traceAlg

-- ============ 件 ⑦：★ 分式域形态（第 ①②步合流） ============
/-- ★★★★★★ **`c_j` 是迹代数的分式**：存在 `a b ∈ traceAlg`、`b ≠ 0`，使 `c_j = a / b`。

这正是 AGPR `thm:14.4.4`（「`𝒵` 是 `T` 的分式域」）在**环层**所需的分量形态：
`c_j ∈ Frac(traceAlg)`。 -/
theorem charpoly_coeff_genMatKF_eq_div (k₀ : Fin r) (j : Fin n) :
    ∃ a b : SField F r n, a ∈ traceAlg F r n ∧ b ∈ traceAlg F r n ∧ b ≠ 0 ∧
      (genMatKF F r n k₀).charpoly.coeff j.val = a / b :=
  ⟨-((hankelMat F r n (genMatKF F r n k₀)).cramer (fun k : Fin n =>
      ((genMatKF F r n k₀) ^ ((genMatKF F r n k₀).charpoly.natDegree + k.val)).trace)) j,
    (hankelMat F r n (genMatKF F r n k₀)).det,
    (traceAlg F r n).neg_mem (cramer_powHigh_mem_traceAlg F r n k₀ j),
    hankelMat_det_mem_traceAlg F r n k₀,
    hankelMat_genMatKF_det_ne_zero F r n k₀,
    charpoly_coeff_eq_neg_cramer_div F r n (genMatKF F r n k₀)
      (hankelMat_genMatKF_det_ne_zero F r n k₀) j⟩

#print axioms charpoly_coeff_genMatKF_eq_div


open scoped Matrix

/-! ## 切分第 6 步：`c_j ∈ Frac(traceAlg)` 的**子域形态**

第 586 轮给了 `∃ a b ∈ traceAlg, b ≠ 0 ∧ c_j = a/b`（分式形态）。本节把它**包装成子域成员**
——`IntermediateField.adjoin F (traceAlg : Set _)`——以便与终局目标
`sprCenterImageField = Frac(κ(C))`（`H2Final`，同一 `IntermediateField` 语言）对位。

**射程**：本节仍只在 `S`（=`SField`）世界。到 `Spr` 世界的搬运（沿 `sprToSField`，方向 Spr→S，
`H2Final` 已有 `sprToSField_injective`）**未做**；FFT「不变量 ⊆ 迹代数」整步**未做**；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **除法包装**：`a, b ∈ T`、`x = a / b` ⟹ `x ∈ Frac(T)`。 -/
theorem mem_adjoin_of_eq_div {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K]
    {T : Set K} {a b x : K} (ha : a ∈ T) (hb : b ∈ T) (hx : x = a / b) :
    x ∈ IntermediateField.adjoin F T := by
  rw [hx, div_eq_mul_inv]
  exact IntermediateField.mul_mem _ (IntermediateField.subset_adjoin F T ha)
    (IntermediateField.inv_mem _ (IntermediateField.subset_adjoin F T hb))

#print axioms mem_adjoin_of_eq_div

/-- ★★★★★★ **`c_j ∈ Frac(traceAlg)`**（`Frac` 用 `IntermediateField.adjoin` 表达）。 -/
theorem charpoly_coeff_genMatKF_mem_traceFraction (k₀ : Fin r) (j : Fin n) :
    (genMatKF F r n k₀).charpoly.coeff j.val
      ∈ IntermediateField.adjoin F (traceAlg F r n : Set (SField F r n)) := by
  obtain ⟨a, b, ha, hb, _, hx⟩ := charpoly_coeff_genMatKF_eq_div F r n k₀ j
  exact mem_adjoin_of_eq_div ha hb hx

#print axioms charpoly_coeff_genMatKF_mem_traceFraction

/-- ★★★★★ **对任意 `j : ℕ`**：`j < n` 用前件；`j > n` 系数归零；`j = n` 系数为首一者的 `1`。 -/
theorem charpoly_coeff_genMatKF_mem_traceFraction_of_le (k₀ : Fin r) (j : ℕ) :
    (genMatKF F r n k₀).charpoly.coeff j
      ∈ IntermediateField.adjoin F (traceAlg F r n : Set (SField F r n)) := by
  by_cases hj : j < n
  · exact charpoly_coeff_genMatKF_mem_traceFraction F r n k₀ ⟨j, hj⟩
  · have hj' : n ≤ j := Nat.le_of_not_lt hj
    rcases lt_or_eq_of_le hj' with hlt | heq
    · rw [charpoly_coeff_eq_zero_of_natDegree_lt F r n _
        (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hlt)]
      exact IntermediateField.zero_mem _
    · have hcoeff : (genMatKF F r n k₀).charpoly.coeff j
          = (genMatKF F r n k₀).charpoly.coeff
              (genMatKF F r n k₀).charpoly.natDegree := by
        congr 1
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        exact heq.symm
      rw [hcoeff, (Matrix.charpoly_monic (genMatKF F r n k₀)).coeff_natDegree]
      exact IntermediateField.one_mem _

#print axioms charpoly_coeff_genMatKF_mem_traceFraction_of_le

/-- ★★★ **幂迹 ∈ `Frac(traceAlg)`**（`traceAlg ⊆ Frac(traceAlg)` 的显式分量）。 -/
theorem trace_pow_genMatKF_mem_traceFraction (k₀ : Fin r) (m : ℕ) :
    ((genMatKF F r n k₀) ^ m).trace
      ∈ IntermediateField.adjoin F (traceAlg F r n : Set (SField F r n)) :=
  IntermediateField.subset_adjoin F (traceAlg F r n : Set (SField F r n))
    (trace_pow_genMatKF_mem_traceAlg F r n k₀ m)

#print axioms trace_pow_genMatKF_mem_traceFraction

/-- ★★★★ **`H.det ∈ Frac(traceAlg)`**（同样只是 `subset_adjoin` 的直接后果）。 -/
theorem hankelMat_det_mem_traceFraction (k₀ : Fin r) :
    (hankelMat F r n (genMatKF F r n k₀)).det
      ∈ IntermediateField.adjoin F (traceAlg F r n : Set (SField F r n)) :=
  IntermediateField.subset_adjoin F (traceAlg F r n : Set (SField F r n))
    (hankelMat_det_mem_traceAlg F r n k₀)

#print axioms hankelMat_det_mem_traceFraction


open scoped Matrix

/-! ## 切分第 7 步：`hZ` 两端的**语言一致**（`K'^N` 升为 `IntermediateField`）＋ (β) 的拉回接口

`hZ`（`H2Final:9310` 的终点假设）是
`∀ x, sprFieldNFixed x → x ∈ sprCenterImageField`；右端已写作 `IntermediateField`
（`sprCenterImageField`，`H2Final:3806`，R258 的理由是 `IntermediateField` **自带**
`Algebra F ↥` 实例），而左端此前只有 `Subalgebra` 版本 `sprNFixedAlg`（`GenericInv:14598`，
其 docstring 明说本 pin 的 `Subfield` 没有 `Algebra F` 实例故只能是 `Subalgebra`）。

本节把左端也升为 `IntermediateField`（`IntermediateField.mk` 只多要一条求逆封闭，
`sprNFixedAlg_inv_mem` 已有）⟹ **`hZ` 变成一条纯子域包含** `sprNFixedField ≤ sprCenterImageField`。

另给 (β) 的**拉回接口** `sprTraceFrac`：把 `S` 侧的迹域
`IntermediateField.adjoin F traceAlg` 沿 `sprToSField`（方向 Spr→S，已机检单射）**取原像**。
取原像使 `x ∈ sprTraceFrac ↔ sprToSField x ∈ Frac(traceAlg)` **按定义成立**——
这是军规 4（禁止 `sprToSField` 直送）的正解形态：不做"直送"，只做 `comap`。

**射程**：本节只给**载体与接口**（无新的数学内容）。`hZ` **未证**；
`sprNFixedField ≤ sprTraceFrac`（需 `S` 侧 FFT 结论）与 `sprTraceFrac ≤ sprCenterImageField`
（`Spr` 侧不变量理论）**均未做**；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★ **`K'^N` 作为 `IntermediateField`**（＝子域，且**自动带 `Algebra F ↥`**实例）。

`sprNFixedAlg`（`GenericInv:14598`）只能是 `Subalgebra`，因为 `V3'` 的 `≃ₐ[F]` 需要两侧都有
`Algebra F` 实例，而本 pin 的 `Subfield` 没有该实例。`IntermediateField` **有**通用实例
（`H2Final` R258 选它作 `sprCenterImageField` 的理由），故 `hZ` 的两端从此**语言一致**。 -/
noncomputable def sprNFixedField : IntermediateField F (SprField F r n) :=
  IntermediateField.mk (sprNFixedAlg F r n)
    (fun _ hx => sprNFixedAlg_inv_mem F r n hx)

#print axioms sprNFixedField

/-- 成员刻画。 -/
theorem mem_sprNFixedField_iff {x : SprField F r n} :
    x ∈ sprNFixedField F r n ↔ sprFieldNFixed F r n x := Iff.rfl

#print axioms mem_sprNFixedField_iff

/-- 与 `Subalgebra` 版本的关系（兼容件）。 -/
theorem sprNFixedField_toSubalgebra :
    (sprNFixedField F r n).toSubalgebra = sprNFixedAlg F r n := rfl

#print axioms sprNFixedField_toSubalgebra

/-- 类型锁：载体一经改动立即编译失败。 -/
theorem sprNFixedField_typeLock :
    (sprNFixedField F r n : Set (SprField F r n)) = {α | sprFieldNFixed F r n α} := rfl

#print axioms sprNFixedField_typeLock

/-! ## 切分第 7b 步：★★★★★ **`Frac(S')^N` 落在 `K'^N` 里**（`K'^N` 分式域层的 `⊇` 半；第 645 轮）

§68 给了 `S'` 的 `N`-固定**子代数** `SprFixed`（`GenericInv`），并把它列的射程留给后续：
「`K'^N` 的**分式域层**（把 `SprFixed` 的分式域嵌进 `K'`）」。本节做这一层的**容易半边**：

```
Frac(SprFixed)  ≤  K'^N          （sprFixedFrac ≤ sprNFixedField）
```

**机制**：`SprFixed` 的每个元经 `algebraMap` 是 `K'` 的 `N`-固定元
（`sprFieldTFixed_algebraMap`／`sprFieldSFixed_algebraMap`，均已机检），
而 `sprNFixedField` 是 `IntermediateField`（对四则运算封闭），故整个分式域落在里面。

**为何只做「容易半边」**：反向 `K'^N ⊆ Frac(SprFixed)` 是 **`lem:14.20` 的分式层**
（`F(M_r) = F(M_r')^T`），源文（`raw/Saltman1999ch14.tex:383–388`）需要
①「`T`-固定 ⟹ `f,g` 是同特征的特征函数」＋ ②Dedekind 独立性 把 `α` 拆成单项式商
＋ ③`(17)`（`φ_B(e(m)) = λ e(m)`，`λ = 1 ⟺ f'(m) = 0`）⟹ `n_j - m_i ∈ ker f'`。
其中 ③ 的**整环层**已机检（`SaltmanT` §2d `torusScale_fixed_iff`），①② 及其分式层装配**未做**。

**射程（诚实边界）**：本节只给 `⊇` 半。`K'^N = Frac(SprFixed)` 的**等式未证**；
`SaltmanZEqNFixed`（`Z = K'^N`）未证；`hZ` 未证；H2 仍不是定理。 -/

/-- `K'` 的 `N`-固定子代数 `SprFixed` 的**分式域**（作为 `SprField` 的子域）。 -/
noncomputable def sprFixedFrac : IntermediateField F (SprField F r n) :=
  IntermediateField.adjoin F
    ((algebraMap (Spr F r n) (SprField F r n)) '' (SprFixed F r n : Set (Spr F r n)))

#print axioms sprFixedFrac

/-- `SprFixed` 的每个元经 `algebraMap` 落在 `K'^N` 里。 -/
theorem algebraMap_mem_sprNFixedField {x : Spr F r n} (hx : x ∈ SprFixed F r n) :
    algebraMap (Spr F r n) (SprField F r n) x ∈ sprNFixedField F r n := by
  rw [mem_sprNFixedField_iff]
  exact ⟨sprFieldTFixed_algebraMap F r n hx.1, sprFieldSFixed_algebraMap F r n hx.2⟩

#print axioms algebraMap_mem_sprNFixedField

/-- ★★★★★★ **`Frac(S')^N` 落在 `K'^N` 里**：`N`-固定子代数的分式域 ⊆ `K'` 的 `N`-固定子域。 -/
theorem sprFixedFrac_le_sprNFixedField : sprFixedFrac F r n ≤ sprNFixedField F r n := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  exact algebraMap_mem_sprNFixedField F r n hx

#print axioms sprFixedFrac_le_sprNFixedField

/-! ## 切分第 7c 步：★★★★★ **`K'^T` 的载体 ＋ `Frac(S')^T ⊆ K'^T`**（`lem:14.20` 分式层的 `⊇` 半；第 648 轮）

`lem:14.20`（`F(M_r) = F(M_r')^T`）在**分式层**的形态需要两个对象：
`K'^T`（环面固定子域）与 `Frac(S')^T`（`S'` 的 `T`-固定多项式的分式域）。§7b 做了 `N` 版本，
本节做 `T` 版本并机检**容易半边** `Frac(S')^T ⊆ K'^T`。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprTFixedField` | `K'^T` 作为 `IntermediateField`（7 条封闭性：`+ − × ÷`、`0 1`、`algebraMap`） |
| `mem_sprTFixedField_iff` | 成员刻画（`rfl`） |
| ★★★★★ `algebraMap_mem_sprTFixedField` | `S'` 的 `T`-固定多项式经 `algebraMap` 落在 `K'^T` |
| ★★★★★ `sprTInvFrac` | `Frac(S')^T`（`T`-固定多项式的分式域，作为 `SprField` 的子域） |
| ★★★★★ `sprTInvFrac_le_sprTFixedField` | **`Frac(S')^T ⊆ K'^T`** |

**工艺**：`sprDiagFieldEquiv` 是 **`RingEquiv`**（不是 `AlgEquiv`），故 `algebraMap_mem'` 不能写
`(sprDiagFieldEquiv b).commutes`（无该字段）；正解是
`IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) c`
→ `sprDiagFieldEquiv_algebraMap` → `(sprDiagHom F r n b).commutes c`（后者**是** `AlgHom`）。

**射程（诚实边界）**：只给 `⊇` 半。反向 `K'^T ⊆ Frac(S')^T`（＝ `lem:14.20` 的正文，
源文 `:383–388`）**未做**——它需要「`α = f/g` T-固定 ⟹ `f, g` 的支撑上单项式权相同」，
本仓已有 `sprDiagHom_fixed_iff`（§86b）可用，但还需 Laurent 记号下的第二次应用。
`K'^N = Frac(SprFixed)` 未证；`SaltmanZEqNFixed` 未证；`hZ` 未证；H2 仍不是定理。 -/

/-- `K'` 的 `T`-固定子域（环面固定点，作为 `IntermediateField`）。 -/
noncomputable def sprTFixedField : IntermediateField F (SprField F r n) where
  carrier := {x | sprFieldTFixed F r n x}
  zero_mem' := by
    intro b
    rw [map_zero]
  one_mem' := by
    intro b
    rw [map_one]
  add_mem' := by
    intro x y hx hy b
    rw [map_add, hx b, hy b]
  mul_mem' := by
    intro x y hx hy b
    rw [map_mul, hx b, hy b]
  inv_mem' := by
    intro x hx b
    rw [map_inv₀, hx b]
  algebraMap_mem' := by
    intro c b
    rw [IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) c,
      sprDiagFieldEquiv_algebraMap, (sprDiagHom F r n b).commutes c]

#print axioms sprTFixedField

/-- 成员刻画。 -/
theorem mem_sprTFixedField_iff {x : SprField F r n} :
    x ∈ sprTFixedField F r n ↔ sprFieldTFixed F r n x := Iff.rfl

#print axioms mem_sprTFixedField_iff

/-- `Spr` 的 `T`-固定多项式经 `algebraMap` 落在 `sprTFixedField` 里。 -/
theorem algebraMap_mem_sprTFixedField {x : Spr F r n}
    (hx : ∀ b : Fin n → Fˣ, sprDiagHom F r n b x = x) :
    algebraMap (Spr F r n) (SprField F r n) x ∈ sprTFixedField F r n :=
  sprFieldTFixed_algebraMap F r n hx

#print axioms algebraMap_mem_sprTFixedField

/-- `Spr` 的 `T`-固定多项式的分式域（作为 `SprField` 的子域）。 -/
noncomputable def sprTInvFrac : IntermediateField F (SprField F r n) :=
  IntermediateField.adjoin F
    ((algebraMap (Spr F r n) (SprField F r n)) ''
      {x : Spr F r n | ∀ b : Fin n → Fˣ, sprDiagHom F r n b x = x})

#print axioms sprTInvFrac

/-- ★★★★★ **`Frac(S')^T ⊆ K'^T`**（`lem:14.20` 分式层的 `⊇` 半）。 -/
theorem sprTInvFrac_le_sprTFixedField : sprTInvFrac F r n ≤ sprTFixedField F r n := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  exact algebraMap_mem_sprTFixedField F r n hx

#print axioms sprTInvFrac_le_sprTFixedField

/-! ## 切分第 7d 步：★★★★★★ **`lem:14.20` 的特征函数分解（`T` 版）**（第 649 轮）

`lem:14.20` 的证明（`raw/Saltman1999ch14.tex:383–388`）第一句是
> "Arguing exactly as in Lemma 14.13, there is a group homomorphism `λ : T → F^*` such that
> `φ_B(f) = λ(B)f` and `φ_B(g) = λ(B)g`."

本节把该步在 `S'`/`T` 世界机检。**做法 = 照抄 `FixedRatio.lean` 的 PGL 版三件**（L48：
有原文/已有证明思路的不自创），只把 `phiA A`／`phiKEquiv A`／`A⁻¹` 换成
`sprDiagHom b`／`sprDiagFieldEquiv b`／`fun i => (b i)⁻¹`：

| 件 | 内容 | PGL 对应件 |
|---|---|---|
| ★★★★★ `sprDiagHom_mul_eq_of_fixed` | 域层固定 ⟹ **交叉相乘** `φ_b(f)·g = f·φ_b(g)` | `phiA_mul_eq_of_fixed` |
| ★★★★★ `sprDiagHom_dvd_of_fixed` | 互素 ＋ 交叉相乘 ⟹ **Euclid 步** `g ∣ φ_b(g)` | `dvd_phiA_of_fixed` |
| ★★★★★★ `sprDiagHom_exists_unit_mul_of_fixed` | 对 `b` 与 `b⁻¹` 各用一次 ⟹ **`φ_b(g) = c·g`，`c` 是单位** | `exists_unit_mul_of_fixed` |

**关键（沿用 PGL 版已登记的工艺）**：`c` 是单位**不**靠次数论证，而靠
「`φ_b(g) = g·h`、`φ_{b⁻¹}(g) = g·k` ⟹ `g = g·k·φ_{b⁻¹}(h)` ⟹ 消去 `g ≠ 0` 得 `k·φ_{b⁻¹}(h) = 1`」
（`isUnit_iff_exists_inv` ＋ `IsUnit.map`）。故**不需要任何 `totalDegree` 引理**。

**用到的现成件**：`sprDiagEquiv`（`Spr` 的 `AlgEquiv`，给单射）、
`sprDiagFieldEquiv_algebraMap`（域层与 `S'` 层的桥）、`sprDiagHom_mul`／`sprDiagHom_one`
（复合律，给 `φ_b ∘ φ_{b⁻¹} = id`）、`map_div₀`（`sprDiagFieldEquiv` 是 `RingEquiv`，仍是
`MonoidWithZeroHomClass`）。

**射程（诚实边界）**：本节只到「`g` 的像是 `g` 的单位倍」。**未做**：
① 由它得「`g`（进而 `f`）支撑上所有单项式权相同」（需一次系数比较，`sprDiagHom_fixed_iff` 的机制可复用）；
② 对 `α_i^{-1}` 再用一次得 `e(n_j − m_i)` 权为 `0`（**需 Laurent 记号**）；
③ 由 ② 得 `K'^T ⊆ Frac(S')^T`（`lem:14.20` 正文）——注意需一个**权为零的单项式** `e(N)`
   清分母（`N(inr (i,j,k)) = M`、`N(inl i) = 0` 即权零，故存在）；
④ `K'^N = Frac(SprFixed)`；`SaltmanZEqNFixed`；`hZ`；H2 仍不是定理。 -/

/-- ★★★★★ **交叉相乘**（`lem:14.20` 证明第一步）：`K'` 中 `f/g` 被 `φ_b` 固定
⟹ `S'` 中 `φ_b(f)·g = f·φ_b(g)`。 -/
theorem sprDiagHom_mul_eq_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n} (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    sprDiagHom F r n b f * g = f * sprDiagHom F r n b g := by
  have hinjA : Function.Injective (sprDiagHom F r n b) := (sprDiagEquiv F r n b).injective
  have hinj : Function.Injective (algebraMap (Spr F r n) (SprField F r n)) :=
    IsFractionRing.injective _ _
  have hφg : sprDiagHom F r n b g ≠ 0 := fun h => hg (hinjA (by simpa using h))
  have h1 : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b f)
        / algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b g) := by
    rw [map_div₀, sprDiagFieldEquiv_algebraMap, sprDiagFieldEquiv_algebraMap]
  rw [h1] at hfix
  have hnum : algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b f)
      * algebraMap (Spr F r n) (SprField F r n) g
      = algebraMap (Spr F r n) (SprField F r n) f
        * algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b g) :=
    (div_eq_div_iff (by simpa using hinj.ne hφg) (by simpa using hinj.ne hg)).mp hfix
  have h2 : algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b f * g)
      = algebraMap (Spr F r n) (SprField F r n) (f * sprDiagHom F r n b g) := by
    rw [map_mul, map_mul]
    exact hnum
  exact hinj h2

#print axioms sprDiagHom_mul_eq_of_fixed

/-- **Euclid 步**：互素 ＋ 交叉相乘 ⟹ `g ∣ φ_b(g)`。 -/
theorem sprDiagHom_dvd_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    g ∣ sprDiagHom F r n b g := by
  have hcross := sprDiagHom_mul_eq_of_fixed F r n b hg hfix
  refine IsRelPrime.dvd_of_dvd_mul_right hcop.symm ⟨sprDiagHom F r n b f, ?_⟩
  rw [mul_comm (sprDiagHom F r n b g) f, mul_comm g (sprDiagHom F r n b f)]
  exact hcross.symm

#print axioms sprDiagHom_dvd_of_fixed

/-- ★★★★★★ **特征函数分解**（`lem:14.20` 证明的关键一步）：`f/g` 被 `φ_b` 与 `φ_{b⁻¹}` 固定、
`f,g` 互素 ⟹ `φ_b(g) = c·g` 且 `c` 是**单位**。 -/
theorem sprDiagHom_exists_unit_mul_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
    (hfixinv : sprDiagFieldEquiv F r n (fun i => (b i)⁻¹)
        (algebraMap (Spr F r n) (SprField F r n) f
          / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ c : Spr F r n, IsUnit c ∧ sprDiagHom F r n b g = c * g := by
  obtain ⟨h, hh⟩ := sprDiagHom_dvd_of_fixed F r n b hcop hg hfix
  obtain ⟨k, hk⟩ := sprDiagHom_dvd_of_fixed F r n (fun i => (b i)⁻¹) hcop hg hfixinv
  have hcomp : ∀ x : Spr F r n,
      sprDiagHom F r n (fun i => (b i)⁻¹) (sprDiagHom F r n b x) = x := by
    intro x
    have h := DFunLike.congr_fun (sprDiagHom_mul F r n (fun i => (b i)⁻¹) b) x
    rw [AlgHom.comp_apply] at h
    have hb : (fun i => (b i)⁻¹ * b i) = (fun _ => 1) := by
      funext i
      exact inv_mul_cancel (b i)
    rw [hb, sprDiagHom_one] at h
    simpa using h
  have hAcomp : ∀ x : Spr F r n,
      sprDiagHom F r n b (sprDiagHom F r n (fun i => (b i)⁻¹) x) = x := by
    intro x
    have h := DFunLike.congr_fun (sprDiagHom_mul F r n b (fun i => (b i)⁻¹)) x
    rw [AlgHom.comp_apply] at h
    have hb : (fun i => b i * (b i)⁻¹) = (fun _ => 1) := by
      funext i
      exact mul_inv_cancel (b i)
    rw [hb, sprDiagHom_one] at h
    simpa using h
  have hkey : g = g * (k * sprDiagHom F r n (fun i => (b i)⁻¹) h) := by
    calc g = sprDiagHom F r n (fun i => (b i)⁻¹) (sprDiagHom F r n b g) := (hcomp g).symm
      _ = sprDiagHom F r n (fun i => (b i)⁻¹) (g * h) := by rw [hh]
      _ = sprDiagHom F r n (fun i => (b i)⁻¹) g
            * sprDiagHom F r n (fun i => (b i)⁻¹) h := map_mul _ _ _
      _ = (g * k) * sprDiagHom F r n (fun i => (b i)⁻¹) h := by rw [hk]
      _ = g * (k * sprDiagHom F r n (fun i => (b i)⁻¹) h) := by rw [mul_assoc]
  have hone : k * sprDiagHom F r n (fun i => (b i)⁻¹) h = 1 := by
    have h1 : g * (k * sprDiagHom F r n (fun i => (b i)⁻¹) h) = g * 1 := by
      rw [mul_one, ← hkey]
    exact mul_left_cancel₀ hg h1
  have hunit_inv : IsUnit (sprDiagHom F r n (fun i => (b i)⁻¹) h) := by
    refine isUnit_iff_exists_inv.mpr ⟨k, ?_⟩
    rw [mul_comm]
    exact hone
  have hunit : IsUnit h := by
    have hm := hunit_inv.map (sprDiagHom F r n b).toRingHom
    simpa [hAcomp h] using hm
  exact ⟨h, hunit, by rw [hh, mul_comm]⟩

#print axioms sprDiagHom_exists_unit_mul_of_fixed

/-! ## 切分第 7e 步：★★★★★★★ **权结论：`f` 与 `g` 的单项式权全相同**（第 650 轮）

§7d 给了「`φ_b(g) = c·g`，`c` 是单位」。本节把它升级为 `lem:14.20` 真正要用的**权结论**：

| 件 | 内容 |
|---|---|
| ★★★★★ `sprDiagHom_eq_C_mul_of_fixed` | **特征值形态**：`φ_b(g) = C u · g`（`u : Fˣ`），由 §7d ＋ `isUnit_iff_eq_C_of_isReduced` |
| ★★★★★★ `sprWt_eq_of_sprDiagHom_eq_C_mul` | **单项式的权 ＝ 特征值**：`φ_b(g) = C u·g` ⟹ `g` 支撑上每个单项式的权都是 `u`（系数比较） |
| ★★★★★★★ `exists_weight_of_fixed_ratio` | **`f` 与 `g` 的单项式权全相同**：由交叉相乘 ＋ `φ_b(g) = C u·g` 得 `φ_b(f) = C u·f`，各用一次上件 |

**机制**：仍用 `MvPolynomial.as_sum` ＋ `map_sum` ＋ `sprDiagHom_monomial_finsupp` ＋
**系数比较**（`coeff_sum` ＋ `Finset.sum_eq_single m` ＋ `coeff_C_mul`／`coeff_monomial`）；
`f` 的特征值得自 `φ_b(f)·g = f·φ_b(g) = C u·f·g` 的右消去（`g ≠ 0`）。

**射程（诚实边界）**：本节只到**「同权」**（源文 `:385` 用 `(17)` 得到的那一步）。**未做**：
① 权为 `0`（源文靠对 `α_i^{-1}` 再用一次同一论证；**需 Laurent 记号** `e(n_j − m_i)`）；
② `K'^T ⊆ Frac(S')^T` 的收口（需用**权零单项式** `e(N)` 清分母，`N(inr (i,j,k)) = M`、`N(inl i) = 0`）；
③ `K'^N = Frac(SprFixed)`；`SaltmanZEqNFixed`；`hZ`；H2 仍不是定理。 -/

/-- ★★★★★ **特征值形态**：互素 ＋ 固定 ⟹ `φ_b(g) = C u · g`（`u` 是**单位**）。 -/
theorem sprDiagHom_eq_C_mul_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
    (hfixinv : sprDiagFieldEquiv F r n (fun i => (b i)⁻¹)
        (algebraMap (Spr F r n) (SprField F r n) f
          / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ u : Fˣ, sprDiagHom F r n b g = MvPolynomial.C ((u : Fˣ) : F) * g := by
  obtain ⟨c, hcunit, hc⟩ := sprDiagHom_exists_unit_mul_of_fixed F r n b hcop hg hfix hfixinv
  obtain ⟨x, hxunit, hx⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hcunit
  obtain ⟨u, rfl⟩ := hxunit
  exact ⟨u, by rw [hc, hx]⟩

#print axioms sprDiagHom_eq_C_mul_of_fixed

/-- ★★★★★★ **单项式的权 ＝ 特征值**：若 `φ_b(g) = C u · g`，则 `g` 支撑上每个单项式的权都是 `u`。 -/
theorem sprWt_eq_of_sprDiagHom_eq_C_mul (b : Fin n → Fˣ) {g : Spr F r n} {u : F}
    (h : sprDiagHom F r n b g = MvPolynomial.C u * g)
    {m : SprIdx r n →₀ ℕ} (hm : m ∈ g.support) :
    m.support.prod (fun v => sprWt F r n b v ^ m v) = u := by
  classical
  set W : (SprIdx r n →₀ ℕ) → F :=
    fun m' => m'.support.prod (fun v => sprWt F r n b v ^ m' v) with hW
  have hsplit : sprDiagHom F r n b g
      = ∑ m' ∈ g.support, MvPolynomial.C (W m') * MvPolynomial.monomial m' (g.coeff m') := by
    conv_lhs => rw [MvPolynomial.as_sum g]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [sprDiagHom_monomial_finsupp]
  have hcoeff : (sprDiagHom F r n b g).coeff m = W m * g.coeff m := by
    rw [hsplit, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single m]
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, ite_eq_left rfl]
    · intro m' _ hmne
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
        ite_eq_right hmne, mul_zero]
    · intro hnot
      exact absurd hm hnot
  have hcoeff2 : (MvPolynomial.C u * g).coeff m = u * g.coeff m := by
    rw [MvPolynomial.coeff_C_mul]
  rw [h, hcoeff2] at hcoeff
  have hc : g.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  exact (mul_right_cancel₀ hc hcoeff).symm

#print axioms sprWt_eq_of_sprDiagHom_eq_C_mul

/-- ★★★★★★★ **`f` 与 `g` 的单项式权全相同**（`lem:14.20` 的权结论）。 -/
theorem exists_weight_of_fixed_ratio (b : Fin n → Fˣ) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
    (hfixinv : sprDiagFieldEquiv F r n (fun i => (b i)⁻¹)
        (algebraMap (Spr F r n) (SprField F r n) f
          / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ u : Fˣ, (∀ m ∈ g.support,
        m.support.prod (fun v => sprWt F r n b v ^ m v) = ((u : Fˣ) : F))
      ∧ (∀ m ∈ f.support,
        m.support.prod (fun v => sprWt F r n b v ^ m v) = ((u : Fˣ) : F)) := by
  obtain ⟨u, hu⟩ := sprDiagHom_eq_C_mul_of_fixed F r n b hcop hg hfix hfixinv
  have hcross := sprDiagHom_mul_eq_of_fixed F r n b hg hfix
  have hf_eigen : sprDiagHom F r n b f = MvPolynomial.C ((u : Fˣ) : F) * f := by
    have h1 : sprDiagHom F r n b f * g = MvPolynomial.C ((u : Fˣ) : F) * f * g := by
      rw [hcross, hu]
      ring
    exact mul_right_cancel₀ hg h1
  exact ⟨u, fun m hm => sprWt_eq_of_sprDiagHom_eq_C_mul F r n b hu hm,
    fun m hm => sprWt_eq_of_sprDiagHom_eq_C_mul F r n b hf_eigen hm⟩

#print axioms exists_weight_of_fixed_ratio

/-- ★★★★★★ **`(β)` 的接口件**：`S` 侧迹域沿 `sprToSField` **拉回** `Spr` 世界。

`sprToSField : SprField →ₐ[F] SField`（方向 Spr→S，`GenericInv:13784`，已机检单射），
故 `x ∈ sprTraceFrac ↔ sprToSField x ∈ Frac(traceAlg)` **按定义**——不需要单射性回推，
也不需要任何"直送"。这是军规 4（禁止 `sprToSField` 直送 (A)-FFT）的**正解形态**。 -/
noncomputable def sprTraceFrac (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    IntermediateField F (SprField F r n) :=
  (IntermediateField.adjoin F (traceAlg F r n : Set (SField F r n))).comap
    (sprToSField F r n k₀ hk₀)

#print axioms sprTraceFrac

/-- 成员刻画（`↔` 按 `comap` 的定义）。 -/
theorem mem_sprTraceFrac_iff {k₀ : Fin r} (hk₀ : k₀.val = 0) {x : SprField F r n} :
    x ∈ sprTraceFrac F r n k₀ hk₀ ↔
      sprToSField F r n k₀ hk₀ x
        ∈ IntermediateField.adjoin F (traceAlg F r n : Set (SField F r n)) :=
  Iff.rfl

#print axioms mem_sprTraceFrac_iff


/-! ## 切分第 8 步：(α) 的**骨架** —— Aronhold 归约命题（AGPR `subsubsec:3.1.1.5`）

`raw/AGPR2020.tex:3062–3068` 的命题（**逐字**）：设 `A, B ⊂ U` 是**对极化 `P` 与复原 `R`
封闭**的两个子空间，则 `A ⊂ B` **当且仅当**多线性部分 `A^mult ⊆ B^mult`。证明三行：
齐次元 `u`（次数 `d`）满足 `u = d! R∘P(u)`，`P(u) ∈ A^mult ⊆ B^mult`，`B` 对 `R` 封闭 ⟹
`d!u ∈ B`，`char 0` ⟹ `u ∈ B`。

`thm:12.1.3` 的证明（`:13901`）正是把它用在 `A = 不变量环`、`B = 迹环` 上。本节把该命题
做成**与具体载体无关**的线性代数定理（`Aronhold` 归约），于是后续只需逐条兑现四个前提：
`hP`（`A` 对极化封闭）／`hAdBd`（两环在多线性元上一致 ＝ `lem:12.1.2` ＋ `eq:12.3`，
**缺口 #2 已机检**）／`hR`（`B` 对复原封闭）／`hcomp`（`R∘P = d!`）。

**射程**：本节只给**归约骨架**（无具体的 `P`／`R` 载体）。`hZ` **未证**；
`Aronhold` 的 `P`／`R` 实现（α1）与四个前提的兑现（α4）**均未做**；`S'^N ⊆ Z` 未证；
H2 仍不是定理。 -/

/-- ★★★★★★ **Aronhold 归约**（`raw/AGPR2020.tex:3062–3068` 的命题，逐行对位）。

三个假设对应原文的三个短语：
* `hP`：`A` **对极化封闭**（`P u` 落在 `A` 的多线性部分 `Ad`）；
* `hAdBd`：两环**在多线性元上一致**（原文 "coincide on multilinear elements"）；
* `hR`：`B` **对复原封闭**（原文 "since `B` is closed under restitution"）；
* `hcomp`：`R (P u) = d! • u`（原文 "we have `u = d! R ∘ P(u)`"，本仓取 `R∘P = d!` 的归一化）；
* `hd`：`char 0`（原文 "since `F` has characteristic 0"）。

结论 `A ≤ B` 即原文的 `A ⊂ B`。 -/
theorem aronhold_reduction
    {U₁ V : Type*} [AddCommGroup U₁] [Module F U₁] [AddCommGroup V] [Module F V]
    (A B : Submodule F U₁) (Ad Bd : Submodule F V)
    (P : U₁ → V) (R : V → U₁) (d : ℕ) (hd : (d.factorial : F) ≠ 0)
    (hP : ∀ u ∈ A, P u ∈ Ad) (hAdBd : Ad ≤ Bd) (hR : ∀ v ∈ Bd, R v ∈ B)
    (hcomp : ∀ u ∈ A, R (P u) = (d.factorial : F) • u) : A ≤ B := by
  intro u hu
  have h1 : (d.factorial : F) • u ∈ B := by
    rw [← hcomp u hu]
    exact hR _ (hAdBd (hP u hu))
  have h2 : u = (d.factorial : F)⁻¹ • ((d.factorial : F) • u) := by
    rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
  rw [h2]
  exact B.smul_mem _ h1

#print axioms aronhold_reduction

/-- ★★★★★ **`char 0` 自动给出 `d! ≠ 0`**（原文 "since `F` has characteristic 0" 的机器形态）。 -/
theorem factorial_ne_zero_of_charZero [CharZero F] (d : ℕ) : (d.factorial : F) ≠ 0 := by
  have h : ((d.factorial : ℕ) : F) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero d
  simpa using h

#print axioms factorial_ne_zero_of_charZero

/-- ★★★★★★ **Aronhold 归约（`char 0` 版）**：`d! ≠ 0` 由 `[CharZero F]` 自动给出。 -/
theorem aronhold_reduction_of_charZero [CharZero F]
    {U₁ V : Type*} [AddCommGroup U₁] [Module F U₁] [AddCommGroup V] [Module F V]
    (A B : Submodule F U₁) (Ad Bd : Submodule F V)
    (P : U₁ → V) (R : V → U₁) (d : ℕ)
    (hP : ∀ u ∈ A, P u ∈ Ad) (hAdBd : Ad ≤ Bd) (hR : ∀ v ∈ Bd, R v ∈ B)
    (hcomp : ∀ u ∈ A, R (P u) = (d.factorial : F) • u) : A ≤ B :=
  aronhold_reduction F A B Ad Bd P R d (factorial_ne_zero_of_charZero F d)
    hP hAdBd hR hcomp

#print axioms aronhold_reduction_of_charZero


/-! ## 切分第 9 步：(α4) 的第一件 —— **`φ_A` 保齐次次数**（不变量环是分次的）

Aronhold 归约（§切分第 8 步）是对**齐次元**陈述的（"If `u ∈ A` is homogeneous of some degree `d`"）。
故要把它用在 `A = 不变量环` 上，先得知道不变量环是**分次**的：`φ_A` 把一个 `d` 次齐次多项式
送到 `d` 次齐次多项式。本节机检之。

**机制**：`φ_A = MvPolynomial.aeval (phiGen …)`，而 `phiGen` 的每个值是**线性形式**
（`x_{ijk} ↦ (A X_k A^{-1})_{ij}`，即 `Σ C(…) · X · C(…)`）；`MvPolynomial.IsHomogeneous.aeval`
（`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:285`）随即给次数 `1 · d = d`。

**射程**：本节只给**分次性**这一件。`hZ` **未证**；Aronhold 的 `P`／`R` 载体（α1）与四个前提的
兑现（α4 其余）**均未做**；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`C c · X t · C c'` 的齐次性**（次数 1）：`φ_A` 在不定元上取值是**线性形式**的零件。 -/
theorem isHomogeneous_alg_mul_X_mul (c c' : F) (t : Fin r × Fin n × Fin n) :
    (algebraMap F (S F r n) c * MvPolynomial.X t * algebraMap F (S F r n) c').IsHomogeneous 1 := by
  have h := ((MvPolynomial.isHomogeneous_C (Fin r × Fin n × Fin n) c).mul
    (MvPolynomial.isHomogeneous_X F t)).mul
    (MvPolynomial.isHomogeneous_C (Fin r × Fin n × Fin n) c')
  simpa using h

#print axioms isHomogeneous_alg_mul_X_mul

/-- ★★★★★ **`φ_A` 在不定元上的取值是 1 次齐次**（`x_{ijk} ↦ (A X_k A^{-1})_{ij}` 是线性形式）。 -/
theorem isHomogeneous_phiGen (A : (Matrix (Fin n) (Fin n) F)ˣ) (e : Fin r × Fin n × Fin n) :
    (phiGen F r n A e).IsHomogeneous 1 := by
  simp only [phiGen, constMat, Matrix.mul_apply, Finset.sum_mul]
  refine MvPolynomial.IsHomogeneous.sum _ _ 1 (fun b _ => ?_)
  refine MvPolynomial.IsHomogeneous.sum _ _ 1 (fun c _ => ?_)
  simp only [Matrix.map_apply, genericMatrix, genericEntry]
  exact isHomogeneous_alg_mul_X_mul F r n _ _ _

#print axioms isHomogeneous_phiGen

/-- ★★★★★★ **`φ_A` 保齐次次数** —— 不变量环是**分次**的（Aronhold 归约可逐次数施用）。 -/
theorem isHomogeneous_phiA {f : S F r n} {d : ℕ} (hf : f.IsHomogeneous d)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) : (phiA F r n A f).IsHomogeneous d := by
  have h := hf.aeval (n := 1) (g := phiGen F r n A)
    (fun i => isHomogeneous_phiGen F r n A i)
  rw [one_mul] at h
  exact h

#print axioms isHomogeneous_phiA


/-! ## 切分第 10 步：(α1) 的**第一块** —— 齐次多项式的「变量缩放律」

Aronhold 的复原步（`R∘P`）在数学上只用一条事实：齐次多项式 `f`（次数 `d`）满足
**`f(a·x) = a^d·f(x)`**——因为在 `d` 个块上做"对角复原"时，
`f((t₁+⋯+t_d)·x) = (t₁+⋯+t_d)^d·f(x)`，而 `(∑ t_j)^d` 中 `∏ t_j` 的系数正是 `d!`。
本节机检前半：**变量缩放律**（多项式层，逐单项式）。

**射程**：本节只给**缩放律**与其单项式引擎。Aronhold 的 `P`／`R` 载体（α1 其余：`d` 块极化的
两层环实现）与 `d!` 系数事实（`(∑ t_j)^d` 的多项式定理）**均未做**；`hZ` **未证**；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

open MvPolynomial

/-- ★★★★ **单项式指数向量的「按 `a` 缩放」**：`∏ (C a · X i)^{s i} = C (a^{deg s}) · ∏ X i^{s i}`。 -/
theorem finsupp_prod_scale {σ : Type*} [Fintype σ] (s : σ →₀ ℕ) (a : F) :
    (s.prod fun i k => (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial σ F) ^ k)
      = MvPolynomial.C (a ^ s.degree) * s.prod (fun i k => MvPolynomial.X i ^ k) := by
  rw [Finsupp.prod_pow, Finsupp.prod_pow, Finsupp.degree_eq_sum]
  have h1 : ∀ i : σ, ((MvPolynomial.C a * MvPolynomial.X i : MvPolynomial σ F) ^ (s i))
      = (MvPolynomial.C a) ^ (s i) * (MvPolynomial.X i) ^ (s i) := fun i => mul_pow _ _ _
  simp only [h1, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]
  simp only [← MvPolynomial.C_pow]
  exact (map_prod (MvPolynomial.C : F →+* MvPolynomial σ F) (fun i => a ^ s i)
    Finset.univ).symm

#print axioms finsupp_prod_scale

/-- ★★★★★ **齐次多项式的「变量缩放」律**（Aronhold 复原步的核心）：

`f` 是 `d` 次齐次 ⟹ `f(a·x) = a^d·f(x)`（把每个不定元 `x_i` 换成 `a x_i`）。 -/
theorem aeval_scale_of_isHomogeneous {σ : Type*} [Fintype σ]
    {f : MvPolynomial σ F} {d : ℕ} (hf : f.IsHomogeneous d) (a : F) :
    MvPolynomial.aeval (fun i => MvPolynomial.C a * MvPolynomial.X i) f
      = MvPolynomial.C (a ^ d) * f := by
  rw [MvPolynomial.as_sum f, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [MvPolynomial.aeval_monomial, finsupp_prod_scale F s a]
  by_cases hc : f.coeff s = 0
  · simp [hc]
  · have hdeg : s.degree = d := by
      by_contra h
      exact hc (hf.coeff_eq_zero h)
    rw [hdeg, MvPolynomial.monomial_eq, ← MvPolynomial.C_eq_algebraMap]
    ring

#print axioms aeval_scale_of_isHomogeneous


/-! ## 切分第 11 步：(α1) 第二、三块 —— **`d!` 系数事实** ＋ **齐次多项式的常数缩放律**

Aronhold 的复原步（`R∘P = d!`）只用两条事实：

1. **齐次缩放律**：`f` 齐次 `d` 次 ⟹ `f(c·y) = c^d · f(y)`（本节 `aeval_const_mul_of_isHomogeneous`，
   是 §切分第 10 步那条 `a=常数` 版本的**一般 `c`／一般 `y` 推广**）；
2. **`d!` 系数事实**：`(∑_j X_j)^d` 中**无平方**单项式 `∏_j X_j` 的系数正是 `d!`
   （本节 `coeff_pow_sum_X_factorial`，经数学库 `MvPolynomial.coeff_sum_X_pow_of_fintype`
   ＋ `Finsupp.multinomial`）。

拼起来：把 `d` 块对角复原（`c = t₁+⋯+t_d`，`y = ` 原变量）代入缩放律得
`f((t₁+⋯+t_d)·x) = (t₁+⋯+t_d)^d·f(x)`；再取 `∏_j t_j` 的系数即 `d!·f(x)`。
⟹ `aronhold_reduction`（§切分第 8 步）的 `hcomp` 前提**已具备两条机理件**。

**射程**：本节只给上述两条机理件（＋ `Finsupp`／`multinomial` 的基件）。**两层环上的
`d` 块极化 `P`／复原 `R` 的载体本身尚未写出**（下一轮）；`hZ` **未证**；`S'^N ⊆ Z` 未证；
H2 仍不是定理。 -/

/-! ### 一、`d!` 系数事实（Aronhold 复原步的 `d!`） -/

/-- **全 1 指数向量**（`Fin d` 上）：`m i = 1` 对一切 `i`。 -/
noncomputable def onesFinsupp (d : ℕ) : Fin d →₀ ℕ :=
  Finsupp.ofSupportFinite (fun _ => 1) (Set.toFinite _)

#print axioms onesFinsupp

theorem onesFinsupp_apply (d : ℕ) (i : Fin d) : onesFinsupp d i = 1 := by
  simp [onesFinsupp]

#print axioms onesFinsupp_apply

theorem onesFinsupp_support (d : ℕ) : (onesFinsupp d).support = Finset.univ := by
  ext i
  simp [Finsupp.mem_support_iff, onesFinsupp_apply]

#print axioms onesFinsupp_support

theorem onesFinsupp_sum (d : ℕ) : (onesFinsupp d).sum (fun _ n => n) = d := by
  rw [Finsupp.sum, onesFinsupp_support]
  simp [onesFinsupp_apply]

#print axioms onesFinsupp_sum

theorem onesFinsupp_multinomial (d : ℕ) : (onesFinsupp d).multinomial = d.factorial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  have hspec := Nat.multinomial_spec (onesFinsupp d).support (fun i => onesFinsupp d i)
  rw [onesFinsupp_support] at hspec
  simp only [onesFinsupp_apply, Nat.factorial_one, Finset.prod_const_one, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hspec
  exact hspec

#print axioms onesFinsupp_multinomial

/-- ★★★★★★ **`d!` 系数事实**：`(∑_j X_j)^d` 中无平方单项式 `∏_j X_j` 的系数正是 `d!`。 -/
theorem coeff_pow_sum_X_factorial {R : Type*} [CommSemiring R] (d : ℕ) :
    ((∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) R)) ^ d).coeff
        (onesFinsupp d) = (d.factorial : R) := by
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype, onesFinsupp_sum]
  simp [onesFinsupp_multinomial]

#print axioms coeff_pow_sum_X_factorial

/-! ### 二、齐次多项式的「常数缩放律」（Aronhold 复原步的机理） -/

/-- ★★★★ **单项式指数向量的常数缩放**：`∏ (c · y i)^{s i} = c^{deg s} · ∏ y i^{s i}`。 -/
theorem finsupp_prod_mul_scale {σ : Type*} [Fintype σ] {M : Type*} [CommMonoid M]
    (s : σ →₀ ℕ) (c : M) (y : σ → M) :
    (s.prod fun i k => (c * y i) ^ k) = c ^ s.degree * s.prod (fun i k => y i ^ k) := by
  rw [Finsupp.prod_pow, Finsupp.prod_pow, Finsupp.degree_eq_sum]
  have h1 : ∀ i : σ, (c * y i) ^ (s i) = c ^ (s i) * (y i) ^ (s i) := fun i => mul_pow _ _ _
  simp only [h1, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]

#print axioms finsupp_prod_mul_scale

/-- ★★★★★★ **齐次多项式的常数缩放律**：`f` 齐次 `d` 次 ⟹ `f(c·y) = c^d·f(y)`。

这是 Aronhold 复原步的**机理件**：把 `d` 块对角复原时取 `c = t₁+⋯+t_d`、`y = ` 原变量，
即得 `f((t₁+⋯+t_d)·x) = (t₁+⋯+t_d)^d·f(x)`；再取 `∏ t_j` 的系数即 `d!·f(x)`。 -/
theorem aeval_const_mul_of_isHomogeneous {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]
    {T : Type*} [CommSemiring T] [Algebra R T]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : T) (y : σ → T) :
    MvPolynomial.aeval (fun i => c * y i) f = c ^ d * MvPolynomial.aeval y f := by
  rw [MvPolynomial.as_sum f]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, finsupp_prod_mul_scale s c y]
  by_cases hc : f.coeff s = 0
  · simp [hc]
  · have hdeg : s.degree = d := by
      by_contra h
      exact hc (hf.coeff_eq_zero h)
    rw [hdeg]
    ring

#print axioms aeval_const_mul_of_isHomogeneous


/-! ## 切分第 12 步：(α1) **收口** —— `d` 块极化 `P` 与复原 `R`，并证 `R∘P = d!`

这一步兑现 `aronhold_reduction`（§切分第 8 步）的 **`hcomp`** 前提：AGPR `:3066` 的
「`u = d! R ∘ P(u)`」。构造（两层环）：

* 块层 `A = F[x^{(j)}_{a}]`（`Fin d × σ` 个变量的多项式环），标量层 `B = A[t_1,…,t_d]`。
* **极化** `polarization f := [t_1⋯t_d] f(∑_j t_j x^{(j)})`（`MvPolynomial.coeff (onesFinsupp d)` 取系数）。
* **复原** `restitution` ：把 `d` 个块并成同一个（`x^{(j)}_a ↦ x_a`）。
* 主定理：`restitution (polarization f) = d! · f`（`f` 齐次 `d` 次）。

**射程**：本节给 Aronhold 的 `P`／`R` 与 `R∘P = d!`。**未做**：`P f` 的**多线性性**
（`Aronhold` 的「`A^mult`」需要它）、`A`／`B` 两环对 `P`／`R` 的封闭性（α4）、
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

variable (F : Type) [Field F] (d : ℕ) (σ : Type)

/-- 复原（在块变量上）：`x^{(j)}_a ↦ x_a`（所有 `d` 个块设成同一个）。 -/
noncomputable def restitution :
    MvPolynomial (Fin d × σ) F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun v : Fin d × σ => MvPolynomial.X v.2)

#print axioms restitution

/-- 极化替换：`x_a ↦ ∑_j t_j · x^{(j)}_a`（落在"`d` 个标量 × `d` 个块"的两层环里）。 -/
noncomputable def polSubst :
    σ → MvPolynomial (Fin d) (MvPolynomial (Fin d × σ) F) :=
  fun a => ∑ j : Fin d, (MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial (Fin d × σ) F))
    * MvPolynomial.C (MvPolynomial.X (j, a))

#print axioms polSubst

/-- ★★★★ **自然性**：`map φ ∘ aeval g = aeval (map φ ∘ g)`（块变量重命名搬进系数层）。 -/
theorem map_restitution_polSubst (f : MvPolynomial σ F) :
    MvPolynomial.map (restitution F d σ : MvPolynomial (Fin d × σ) F →+* MvPolynomial σ F)
        (MvPolynomial.aeval (polSubst F d σ) f)
      = MvPolynomial.aeval (fun a => MvPolynomial.map
          (restitution F d σ : MvPolynomial (Fin d × σ) F →+* MvPolynomial σ F)
          (polSubst F d σ a)) f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, MvPolynomial.aeval_X, hp]

#print axioms map_restitution_polSubst

/-- ★★★★ **`rest (polSubst a) = (t₁+⋯+t_d) · x_a`**（复原把 `t_j` 保留、把块并掉）。 -/
theorem map_restitution_polSubst_apply (a : σ) :
    MvPolynomial.map (restitution F d σ : MvPolynomial (Fin d × σ) F →+* MvPolynomial σ F)
        (polSubst F d σ a)
      = (∑ j : Fin d, (MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial σ F)))
        * MvPolynomial.C (MvPolynomial.X a) := by
  have hval : ∀ j : Fin d, MvPolynomial.aeval (fun v : Fin d × σ => MvPolynomial.X v.2)
      (MvPolynomial.X (j, a) : MvPolynomial (Fin d × σ) F) = (MvPolynomial.X a : MvPolynomial σ F) :=
    fun j => MvPolynomial.aeval_X
      (f := fun v : Fin d × σ => (MvPolynomial.X v.2 : MvPolynomial σ F)) (s := (j, a))
  have hstep : ∀ j : Fin d, MvPolynomial.map
      (restitution F d σ : MvPolynomial (Fin d × σ) F →+* MvPolynomial σ F)
      ((MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial (Fin d × σ) F))
        * MvPolynomial.C (MvPolynomial.X (j, a)))
      = (MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial σ F))
        * MvPolynomial.C (MvPolynomial.X a) := by
    intro j
    rw [map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
    change (MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial σ F)) * MvPolynomial.C
      (MvPolynomial.aeval (fun v : Fin d × σ => MvPolynomial.X v.2)
        (MvPolynomial.X (j, a) : MvPolynomial (Fin d × σ) F))
      = (MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial σ F)) * MvPolynomial.C
        (MvPolynomial.X a : MvPolynomial σ F)
    rw [hval j]
  simp only [polSubst, map_sum, hstep]
  rw [Finset.sum_mul]

#print axioms map_restitution_polSubst_apply

/-- ★★★ **`aeval (C ∘ X) f = C f`**。 -/
theorem aeval_C_X_eq_C (f : MvPolynomial σ F) :
    MvPolynomial.aeval (fun a => MvPolynomial.C (MvPolynomial.X a) :
        σ → MvPolynomial (Fin d) (MvPolynomial σ F)) f
      = MvPolynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, MvPolynomial.aeval_X, hp]

#print axioms aeval_C_X_eq_C

/-- 极化：`[t₁⋯t_d] f(∑_j t_j x^{(j)})`（落在 `d` 个块的多项式环里）。 -/
noncomputable def polarization (f : MvPolynomial σ F) : MvPolynomial (Fin d × σ) F :=
  (MvPolynomial.aeval (polSubst F d σ) f).coeff (onesFinsupp d)

#print axioms polarization

/-- ★★★★★★ **复原∘极化 = `d!`**（Aronhold 的 `R∘P`，AGPR `:3066` 的「`u = d! R∘P(u)`」）。 -/
theorem restitution_polarization [Fintype σ] (f : MvPolynomial σ F)
    (hf : f.IsHomogeneous d) :
    restitution F d σ (polarization F d σ f) = (d.factorial : MvPolynomial σ F) * f := by
  rw [polarization]
  have hcm : (restitution F d σ)
        ((MvPolynomial.aeval (polSubst F d σ) f).coeff (onesFinsupp d))
      = (MvPolynomial.map (restitution F d σ :
            MvPolynomial (Fin d × σ) F →+* MvPolynomial σ F)
          (MvPolynomial.aeval (polSubst F d σ) f)).coeff (onesFinsupp d) :=
    (MvPolynomial.coeff_map (restitution F d σ :
      MvPolynomial (Fin d × σ) F →+* MvPolynomial σ F) _ _).symm
  rw [hcm]
  rw [map_restitution_polSubst F d σ f]
  simp only [map_restitution_polSubst_apply F d σ]
  rw [aeval_const_mul_of_isHomogeneous (f := f) (d := d) hf]
  rw [aeval_C_X_eq_C]
  rw [mul_comm ((∑ j : Fin d, (MvPolynomial.X j : MvPolynomial (Fin d) (MvPolynomial σ F))) ^ d)
    (MvPolynomial.C f)]
  rw [MvPolynomial.coeff_C_mul, coeff_pow_sum_X_factorial (R := MvPolynomial σ F)]
  rw [mul_comm]

#print axioms restitution_polarization

/-! ## 切分第 13 步：(α1) 的**线性性／次数性** —— `polarization` 是线性的且只取次数 `d` 层

Aronhold 归约（§切分第 8 步）把 `P` 当作**线性映射**用在子空间 `A` 上，且要求 `P` 把 `A` 的
齐次部分送到"多线性部分"。本节给这两件事的**线性性与次数筛选**：

* `isHomogeneous_polSubst`／`isHomogeneous_aeval_polSubst`：`aeval (polSubst) f` 在 `t`-变量上
  的次数恰是 `f` 的次数（`polSubst a` 在每个 `t` 上一次）；
* `polarization_eq_zero_of_isHomogeneous_ne`：**`f` 的次数 ≠ `d` ⟹ `P f = 0`**——
  即 `P` 只从次数 `d` 那一层取系数（`onesFinsupp d` 的次数正是 `d`）；
* `polarization_add`／`polarization_smul`：`P` 是 `F`-线性的。

**射程**：本节给线性性与次数筛选。**未做**：`P f` 的**块多线性性**（每个块 `j` 的次数 1，
Aronhold 的 `A^mult` 侧真正需要的）——那需要把"两层环的 `A`-系数"与"块权重"接线；
α4（两环对 `P`／`R` 封闭）、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

theorem onesFinsupp_degree : Finsupp.degree (onesFinsupp d) = d := by
  rw [Finsupp.degree_eq_sum]
  simp [onesFinsupp_apply]

#print axioms onesFinsupp_degree

/-- ★★★★ **`polSubst a` 在 `t`-变量上是一次齐次**（每个 `t_j` 至多出现一次）。 -/
theorem isHomogeneous_polSubst (a : σ) :
    (polSubst F d σ a).IsHomogeneous 1 := by
  refine MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ => ?_)
  exact (MvPolynomial.isHomogeneous_X (MvPolynomial (Fin d × σ) F) j).mul
    (MvPolynomial.isHomogeneous_C _ _)

#print axioms isHomogeneous_polSubst

/-- ★★★★★ **`aeval (polSubst) f` 在 `t`-变量上是 `m` 次齐次**（`f` 齐次 `m` 次）。 -/
theorem isHomogeneous_aeval_polSubst {f : MvPolynomial σ F} {m : ℕ} (hf : f.IsHomogeneous m) :
    (MvPolynomial.aeval (polSubst F d σ) f).IsHomogeneous m := by
  have h := hf.aeval (n := 1) (g := polSubst F d σ) (fun a => isHomogeneous_polSubst F d σ a)
  rw [one_mul] at h
  exact h

#print axioms isHomogeneous_aeval_polSubst

/-- ★★★★★ **`polarization` 只取次数 `d` 的那一层**：`f` 齐次 `m ≠ d` ⟹ `P f = 0`。 -/
theorem polarization_eq_zero_of_isHomogeneous_ne {f : MvPolynomial σ F} {m : ℕ}
    (hf : f.IsHomogeneous m) (hm : m ≠ d) : polarization F d σ f = 0 := by
  rw [polarization]
  exact (isHomogeneous_aeval_polSubst F d σ hf).coeff_eq_zero
    (by rw [onesFinsupp_degree]; exact fun h => hm h.symm)

#print axioms polarization_eq_zero_of_isHomogeneous_ne

/-- ★★★★ **`polarization` 可加**（Aronhold 的 `P` 必须是线性的）。 -/
theorem polarization_add (f g : MvPolynomial σ F) :
    polarization F d σ (f + g) = polarization F d σ f + polarization F d σ g := by
  simp only [polarization, map_add, MvPolynomial.coeff_add]

#print axioms polarization_add

/-- ★★★★ **`polarization` 与纯量相容**（`P (c·f) = c·P f`，`c : F`）。 -/
theorem polarization_smul (c : F) (f : MvPolynomial σ F) :
    polarization F d σ (c • f) = c • polarization F d σ f := by
  simp only [polarization, map_smul, MvPolynomial.coeff_smul]

#print axioms polarization_smul

/-! ## 切分第 14 步：(α1) 的**线性映射载体** ＋ `∏t`-系数的次数筛选

Aronhold 的 `P` 要作为**线性映射**作用在子空间上（`A`／`B` 都是 `F`-子空间），故本节把
`polarization` 打包成 `F`-线性映射 `polarizationLM`，并给系数侧的次数筛选
`coeff_ones_eq_zero_of_isHomogeneous_ne`（齐次次数 ≠ `d` ⟹ `∏t`-系数为 0）。

**诚实记录（rule 24③ 的根因假设，供下轮直接修）**：本轮还尝试了「`t_j ↦ c_j t_j` 把 `∏t`-系数
乘 `∏_j c_j`」这条**缩放判据**（它是"块多重次数 ＝ `(1,…,1)`"的判据），三次未过，根因已定位
（**不是数学问题**）：
① 目标里出现的是 `∏ x, X x ^ s x`（`Finset.univ` 上的积），而 `monomial_eq` 的右端是
   `s.prod (fun n e => X n ^ e)`（`Finsupp.prod`，`support` 上的积）⟹ 须先证
   `∏ x, X x^{s x} = s.prod (fun n e => X n ^ e)`（`Finsupp.prod` 展开 ＋ `Finset.prod_subset`）；
② `MvPolynomial.coeff_monomial` 的实参次序（且目标里已有 `algebraMap a * monomial …` 的形态）；
③ `coeff` 穿过 `Finset.sum` 需显式用 `map_sum`（对 `coeff` 的线性映射形态）。

**射程**：本节只给**线性载体与次数筛选**。**块多重次数 `(1,…,1)`（＝多线性性）仍未证**
（＝上面的缩放判据）；α4、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`∏t`-系数在错误次数的齐次层上消失**。 -/
theorem coeff_ones_eq_zero_of_isHomogeneous_ne {A : Type*} [CommSemiring A]
    {p : MvPolynomial (Fin d) A} {m : ℕ} (hp : p.IsHomogeneous m) (hm : m ≠ d) :
    p.coeff (onesFinsupp d) = 0 :=
  hp.coeff_eq_zero (by rw [onesFinsupp_degree]; exact fun h => hm h.symm)

#print axioms coeff_ones_eq_zero_of_isHomogeneous_ne

/-- ★★★★ **`polarization` 作为 `F`-线性映射**（Aronhold 的 `P` 作用在子空间上）。 -/
noncomputable def polarizationLM :
    MvPolynomial σ F →ₗ[F] MvPolynomial (Fin d × σ) F where
  toFun := polarization F d σ
  map_add' := polarization_add F d σ
  map_smul' := polarization_smul F d σ

#print axioms polarizationLM

/-- 接口：`polarizationLM` 的作用就是 `polarization`。 -/
theorem polarizationLM_apply (f : MvPolynomial σ F) :
    polarizationLM F d σ f = polarization F d σ f := rfl

#print axioms polarizationLM_apply

/-- `P 0 = 0`。 -/
theorem polarization_zero : polarization F d σ (0 : MvPolynomial σ F) = 0 :=
  (polarizationLM F d σ).map_zero

#print axioms polarization_zero

/-! ## 切分第 15 步：**`t`-缩放的 `∏t`-系数判据**（第 597 轮未过件的根因修复）

第 597 轮尝试「`t_j ↦ c_j t_j` 把 `∏_j t_j` 的系数乘以 `∏_j c_j`」三次未过，根因已定位为
**形式层**（不是数学）：目标里的积是 `Finset.univ` 上的 `∏ x, X x^{s x}`，而
`MvPolynomial.monomial_eq` 的右端是 **`Finsupp.prod`**（`support` 上的积）。本节先独立成件
`prod_scale_monomial`（把两者桥起来），再收口判据 `coeff_ones_aeval_scale_t`。

**用途（Aronhold 多线性性）**：该判据是「`P f` 的块多重次数 ＝ `(1,…,1)`」的
**系数层判据**——按块缩放 `x^{(j)} ↦ λ_j x^{(j)}` 应把 `P f` 乘以 `∏_j λ_j`。

**射程**：本节只给**系数层判据**（`t`-方向）。**块缩放律本身**（`x^{(j)} ↦ λ_j x^{(j)}` 作用在
`polarization f` 上）**未证**——它要把本节判据与 `coeff_map`／`comp_aeval` 串起来（下一轮）；
α4、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`t`-变量缩放的单项式形态**：`∏_j (c_j t_j)^{s_j} = monomial s (∏_j c_j^{s_j})`。 -/
theorem prod_scale_monomial {A : Type*} [CommSemiring A] (c : Fin d → A) (s : Fin d →₀ ℕ) :
    (s.prod fun j k => (MvPolynomial.C (c j) * MvPolynomial.X j
      : MvPolynomial (Fin d) A) ^ k)
      = MvPolynomial.monomial s (∏ j, c j ^ s j) := by
  rw [Finsupp.prod_pow]
  rw [Finset.prod_congr rfl
    (fun j _ => mul_pow (MvPolynomial.C (c j)) (MvPolynomial.X j) (s j))]
  have h1 : (∏ x, (MvPolynomial.C (c x) : MvPolynomial (Fin d) A) ^ s x)
      = MvPolynomial.C (∏ j, c j ^ s j) := by
    rw [Finset.prod_congr rfl (fun j _ => (MvPolynomial.C_pow (c j) (s j)).symm)]
    exact (map_prod (MvPolynomial.C : A →+* MvPolynomial (Fin d) A)
      (fun j => c j ^ s j) Finset.univ).symm
  have h2 : (∏ x, (MvPolynomial.X x : MvPolynomial (Fin d) A) ^ s x)
      = s.prod (fun n e => MvPolynomial.X n ^ e) :=
    (Finsupp.prod_pow s (fun x => MvPolynomial.X x)).symm
  rw [Finset.prod_mul_distrib, h1, h2, MvPolynomial.monomial_eq]

#print axioms prod_scale_monomial

/-- ★★★★★ **`t`-缩放下的 `∏t`-系数**：`t_j ↦ c_j t_j` 使 `∏_j t_j` 的系数乘以 `∏_j c_j`。 -/
theorem coeff_ones_aeval_scale_t {A : Type*} [CommSemiring A] (c : Fin d → A)
    (p : MvPolynomial (Fin d) A) :
    (MvPolynomial.aeval (fun j => MvPolynomial.C (c j) * MvPolynomial.X j) p).coeff
        (onesFinsupp d) = (∏ j, c j) * p.coeff (onesFinsupp d) := by
  have hmono : ∀ (s : Fin d →₀ ℕ) (a : A),
      (MvPolynomial.aeval (fun j => MvPolynomial.C (c j) * MvPolynomial.X j)
          (MvPolynomial.monomial s a)).coeff (onesFinsupp d)
        = (∏ j, c j) * (MvPolynomial.monomial s a).coeff (onesFinsupp d) := by
    intro s a
    rw [MvPolynomial.aeval_monomial, prod_scale_monomial, ← MvPolynomial.C_eq_algebraMap]
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h1 _
    · subst h1
      simp only [onesFinsupp_apply, pow_one]
      ring
    all_goals simp_all
  rw [MvPolynomial.as_sum p]
  simp only [map_sum, Finset.mul_sum, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl (fun s _ => hmono s (p.coeff s))

#print axioms coeff_ones_aeval_scale_t

/-! ## 切分第 16 步：**块缩放律的第一块** ＋ **强转分裂的根因修复（教训 47）**

目标：`blockScale λ (P f) = (∏_j λ_j) • P f`（块多重次数 `(1,…,1)` 的判据）。

上一轮（R597）在同一处空转三次、本轮又空转三次后，**根因被定位并修复**：
`blockScale` 若定义成 `AlgHom`（`MvPolynomial.aeval`），则它在目标里以 `↑(f) x`（`FunLike`
强转）出现，与 `rw [show …]`／`simp` 里的形式**不是同一个项** ⟹ 静默不匹配。
**正解**：用 `MvPolynomial.eval₂Hom` 把块缩放定义成 **`RingHom`**（`blockScaleR`），
与 `MvPolynomial.map` 的实参类型一致，`simp`／`rw` 一次通过。
（这是「强转形式不同一」族的**第 4 例**：教训 42／43／46／47；前三例的正解都是"先 `change` 规范化"，
本例给出了**更前置的正解：从一开始就用下游需要的那个强转形态定义对象**。）

本节给：`blockScaleR`（定义）／`blockScaleR_X`（不定元上的值）／
`map_blockScaleR_polSubst_apply`（**逐点**：`blockScaleR` 把 `polSubst a` 变成标量层 `t`-缩放后的形态）。

**射程**：本节只到**逐点**一步。块缩放律的**整体**（自然性 ＋ `coeff_ones_aeval_scale_t` 串接）
**未证**；α4、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- **块缩放**（`RingHom` 形态）：`x^{(j)}_a ↦ λ_j x^{(j)}_a`。

**为何用 `RingHom` 而非 `AlgHom`**（教训 47）：`AlgHom` 与 `RingHom` 的 `FunLike` 强转**不是同一个**，
`rw`／`simp` 在二者混用处会静默不匹配（本轮为此空转 6 次）；`MvPolynomial.eval₂Hom` 返回
`RingHom`，与 `MvPolynomial.map` 的实参类型一致，`simp` 一次通过。 -/
noncomputable def blockScaleR (lam : Fin d → F) :
    MvPolynomial (Fin d × σ) F →+* MvPolynomial (Fin d × σ) F :=
  MvPolynomial.eval₂Hom (algebraMap F (MvPolynomial (Fin d × σ) F))
    (fun v : Fin d × σ => MvPolynomial.C (lam v.1) * MvPolynomial.X v)

#print axioms blockScaleR

/-- `blockScaleR` 在不定元上的值。 -/
theorem blockScaleR_X (lam : Fin d → F) (v : Fin d × σ) :
    blockScaleR F d σ lam (MvPolynomial.X v) = MvPolynomial.C (lam v.1) * MvPolynomial.X v := by
  simp [blockScaleR]

#print axioms blockScaleR_X

/-- ★★★★ **逐点**：`blockScaleR` 把 `polSubst a` 变成 `t`-缩放（标量层）后的形态。 -/
theorem map_blockScaleR_polSubst_apply (lam : Fin d → F) (a : σ) :
    MvPolynomial.map (blockScaleR F d σ lam) (polSubst F d σ a)
      = MvPolynomial.aeval (fun j : Fin d =>
          MvPolynomial.C (algebraMap F (MvPolynomial (Fin d × σ) F) (lam j))
            * MvPolynomial.X j) (polSubst F d σ a) := by
  simp only [polSubst, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [blockScaleR_X, MvPolynomial.C_mul]
  simp only [MvPolynomial.C_eq_algebraMap]
  ring

#print axioms map_blockScaleR_polSubst_apply

/-! ## 切分第 17 步：块缩放律的**机械件**（自然性 ＋ 两个 `RingHom` 缩放 ＋ 常数固定）

块缩放律 `blockScaleR λ (P f) = (∏_j λ_j) • P f` 的链条是：
`coeff_map` → **自然性** → 逐点（§16）→ **`t`-缩放提取** → `smul` 收口。本节把其中的
**机械化零件**全部机检：

* `map_aeval_polSubst_general`：通用自然性 `ψ (aeval (polSubst) f) = aeval (ψ ∘ polSubst) f`
  （`ψ : B →+* B` **固定 `F`-常数**；`RingHom` 形态避开强转分裂，教训 47）；
* `blockScaleB`／`tScaleB`：块缩放搬进标量层、`t`-缩放（均为 `RingHom`）；
* `blockScaleB_base`／`tScaleB_base`：二者**固定 `F`-常数**（自然性前提）；
* `tScaleB_eq_aeval`：`tScaleB` 逐点就是对应 `aeval`（接 R598 的 `coeff_ones_aeval_scale_t`）。

**射程**：本节只给**机械件**。块缩放律的**整体**（把六件串成一条等式）**仍未证**——
剩余障碍已定位（见 log）：① `tScaleB` 在目标里会被 delta 展开成 `eval₂Hom` 形态，
`rw [tScaleB_eq_aeval …]` 不匹配 ⟹ 应**直接把 `hpt` 陈述成 `aeval` 形态**（＝R599 的逐点件）；
② `coeff_ones_aeval_scale_t` 的 `d` 是**显式参数**（须写成 `coeff_ones_aeval_scale_t d c p`）。
α4、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 两层环（标量层）。 -/
abbrev TwoRing (F : Type) [Field F] (d : ℕ) (σ : Type) :=
  MvPolynomial (Fin d) (MvPolynomial (Fin d × σ) F)

#print axioms TwoRing

/-- ★★★★ **自然性（通用 `RingHom` 形态）**：`ψ` 固定 `F`-常数 ⟹
`ψ (aeval (polSubst) f) = aeval (ψ ∘ polSubst) f`。 -/
theorem map_aeval_polSubst_general
    (ψ : TwoRing F d σ →+* TwoRing F d σ)
    (hψ : ∀ r : F, ψ (algebraMap F (TwoRing F d σ) r) = algebraMap F (TwoRing F d σ) r)
    (f : MvPolynomial σ F) :
    ψ (MvPolynomial.aeval (polSubst F d σ) f)
      = MvPolynomial.aeval (fun a => ψ (polSubst F d σ a)) f := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, hψ]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, MvPolynomial.aeval_X, hp]

#print axioms map_aeval_polSubst_general

/-- 块缩放搬进标量层（`RingHom` 形态）。 -/
noncomputable def blockScaleB (lam : Fin d → F) : TwoRing F d σ →+* TwoRing F d σ :=
  MvPolynomial.map (blockScaleR F d σ lam)

#print axioms blockScaleB

/-- `t`-缩放（`RingHom` 形态）。 -/
noncomputable def tScaleB (lam : Fin d → F) : TwoRing F d σ →+* TwoRing F d σ :=
  MvPolynomial.eval₂Hom (algebraMap (MvPolynomial (Fin d × σ) F) (TwoRing F d σ))
    (fun j : Fin d =>
      MvPolynomial.C (algebraMap F (MvPolynomial (Fin d × σ) F) (lam j)) * MvPolynomial.X j)

#print axioms tScaleB

theorem blockScaleB_base (lam : Fin d → F) (r : F) :
    blockScaleB F d σ lam (algebraMap F (TwoRing F d σ) r)
      = algebraMap F (TwoRing F d σ) r := by
  rw [show (algebraMap F (TwoRing F d σ)) r
      = MvPolynomial.C (algebraMap F (MvPolynomial (Fin d × σ) F) r) from by
    rw [MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]]
  rw [blockScaleB, MvPolynomial.map_C]
  congr 1
  simp [blockScaleR]

#print axioms blockScaleB_base

theorem tScaleB_base (lam : Fin d → F) (r : F) :
    tScaleB F d σ lam (algebraMap F (TwoRing F d σ) r)
      = algebraMap F (TwoRing F d σ) r := by
  simp [tScaleB, MvPolynomial.eval₂Hom_C]

#print axioms tScaleB_base

/-- `tScaleB` 逐点就是对应 `aeval`。 -/
theorem tScaleB_eq_aeval (lam : Fin d → F) (p : TwoRing F d σ) :
    tScaleB F d σ lam p
      = MvPolynomial.aeval (R := MvPolynomial (Fin d × σ) F) (fun j : Fin d =>
          MvPolynomial.C (algebraMap F (MvPolynomial (Fin d × σ) F) (lam j))
            * MvPolynomial.X j) p := by
  rw [MvPolynomial.aeval_def]
  rfl

#print axioms tScaleB_eq_aeval

/-! ## 切分第 18 步：★★★★★★ **块缩放律收口** —— `P f` 的块多重次数恒为 `(1,…,1)`

```
blockScaleR λ (P f) = (∏_j λ_j) • P f        （对任意 f）
```

这就是 Aronhold 的「**多线性**」判据的机器形态：极化 `P f` 在 `d` 个块上**各恰好一次**
（按块缩放 `x^{(j)} ↦ λ_j x^{(j)}` 时整体乘 `∏_j λ_j`）。**齐次性不必假设**——`P f = 0`
时两端同为零（由 §14 的次数筛选自动成立）。

链条（全部前提件均已在 §15–§17 机检）：`MvPolynomial.coeff_map`（把 `blockScaleR` 搬进系数）
→ 通用自然性（`map_blockScaleR_aeval`）→ 逐点（§16）→ `t`-缩放自然性（`tScaleB_aeval`）→
R598 的 `coeff_ones_aeval_scale_t`（把 `t_j ↦ λ_j t_j` 的缩放提出）→ `smul` 收口。

**射程**：本节给**块缩放判据**。Aronhold 归约（§切分第 8 步）的 `A^mult` 侧还需把
"多重次数 `(1,…,1)`"翻译成"落在多线性子空间里"（判据 ⟹ 子空间成员，一步线性代数）；
α4（两环对 `P`／`R` 的封闭性）、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 自然性的**块缩放实例**。 -/
theorem map_blockScaleR_aeval (lam : Fin d → F) (f : MvPolynomial σ F) :
    MvPolynomial.map (blockScaleR F d σ lam) (MvPolynomial.aeval (polSubst F d σ) f)
      = MvPolynomial.aeval (fun a : σ =>
          MvPolynomial.map (blockScaleR F d σ lam) (polSubst F d σ a)) f :=
  map_aeval_polSubst_general F d σ (MvPolynomial.map (blockScaleR F d σ lam))
    (blockScaleB_base F d σ lam) f

#print axioms map_blockScaleR_aeval

/-- 自然性的 **`t`-缩放实例**。 -/
theorem tScaleB_aeval (lam : Fin d → F) (f : MvPolynomial σ F) :
    tScaleB F d σ lam (MvPolynomial.aeval (polSubst F d σ) f)
      = MvPolynomial.aeval (fun a : σ => tScaleB F d σ lam (polSubst F d σ a)) f :=
  map_aeval_polSubst_general F d σ (tScaleB F d σ lam) (tScaleB_base F d σ lam) f

#print axioms tScaleB_aeval

/-- ★★★★★★★ **块缩放律**：按块缩放 `x^{(j)} ↦ λ_j x^{(j)}` 把 `P f` 乘以 `∏_j λ_j`
（**对任意 `f` 成立**——`P f = 0` 时两端同为零；齐次性不必假设）。
即 `P f` 的**块多重次数恒为 `(1,…,1)`**：Aronhold 的"多线性"判据。 -/
theorem blockScaleR_polarization [Fintype σ] (lam : Fin d → F) (f : MvPolynomial σ F) :
    blockScaleR F d σ lam (polarization F d σ f) = (∏ j, lam j) • polarization F d σ f := by
  rw [polarization]
  rw [show blockScaleR F d σ lam ((MvPolynomial.aeval (polSubst F d σ) f).coeff (onesFinsupp d))
      = (MvPolynomial.map (blockScaleR F d σ lam) (MvPolynomial.aeval (polSubst F d σ) f)).coeff
          (onesFinsupp d) from (MvPolynomial.coeff_map (blockScaleR F d σ lam) _ _).symm]
  rw [map_blockScaleR_aeval F d σ lam f]
  have hpt : ∀ a : σ, MvPolynomial.map (blockScaleR F d σ lam) (polSubst F d σ a)
      = tScaleB F d σ lam (polSubst F d σ a) := fun a => by
    rw [tScaleB_eq_aeval F d σ lam (polSubst F d σ a)]
    exact map_blockScaleR_polSubst_apply F d σ lam a
  simp only [hpt]
  rw [← tScaleB_aeval F d σ lam f]
  rw [tScaleB_eq_aeval F d σ lam (MvPolynomial.aeval (polSubst F d σ) f)]
  rw [coeff_ones_aeval_scale_t d (fun j => algebraMap F (MvPolynomial (Fin d × σ) F) (lam j))
    (MvPolynomial.aeval (polSubst F d σ) f)]
  rw [show (∏ j, algebraMap F (MvPolynomial (Fin d × σ) F) (lam j))
      = algebraMap F (MvPolynomial (Fin d × σ) F) (∏ j, lam j) from (map_prod _ _ _).symm]
  rw [Algebra.smul_def]

#print axioms blockScaleR_polarization

/-! ## 切分第 19 步：**多线性子模** `A^mult` 的载体 ＋ `P` 落入其中

`aronhold_reduction`（§切分第 8 步）需要两个**子空间** `Ad`／`Bd`（多线性部分）与前提
`hP : ∀ u ∈ A, P u ∈ Ad`。本节给**载体**：

* `IsBlockMultilinear v`：`∀ λ, blockScale λ v = (∏_j λ_j) • v`
  —— 在无限域上**等价于**"所有单项式的块多重次数 ＝ `(1,…,1)`"（§18 已机检该律本身）；
* `multilinearSubmodule`：块多线性元构成的 `F`-子模（零点／加法／数乘三条已机检）；
* **`polarization_mem_multilinearSubmodule`：`P f` 落在其中** —— 即 `hP` 的**多线性半边**
  （另一半"不变量"由 α4 给）。

**射程**：本节给**判据 ⟹ 子模成员**一步。Aronhold 归约的其余前提（`hAdBd`：
多线性不变量 ⊆ 多线性迹；`hR`：复原把多线性迹送回迹环）**未做**；α4、β1、β2 未做；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- `blockScaleR` 固定常数。 -/
theorem blockScaleR_C (lam : Fin d → F) (r : F) :
    blockScaleR F d σ lam (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [blockScaleR]

#print axioms blockScaleR_C

/-- ★★★★★ **块多线性**：按块缩放 `x^{(j)} ↦ λ_j x^{(j)}` 时整体乘 `∏_j λ_j`。
（在无限域上等价于：所有单项式的**块多重次数 ＝ `(1,…,1)`**。） -/
def IsBlockMultilinear (v : MvPolynomial (Fin d × σ) F) : Prop :=
  ∀ lam : Fin d → F, blockScaleR F d σ lam v = (∏ j, lam j) • v

#print axioms IsBlockMultilinear

/-- ★★★★★★★ **`P f` 是块多线性的**（Aronhold 归约的 `A^mult` 侧输入）。 -/
theorem polarization_isBlockMultilinear [Fintype σ] (f : MvPolynomial σ F) :
    IsBlockMultilinear F d σ (polarization F d σ f) :=
  fun lam => blockScaleR_polarization F d σ lam f

#print axioms polarization_isBlockMultilinear

theorem isBlockMultilinear_zero : IsBlockMultilinear F d σ (0 : MvPolynomial (Fin d × σ) F) := by
  intro lam
  rw [map_zero, smul_zero]

#print axioms isBlockMultilinear_zero

theorem isBlockMultilinear_add {v w : MvPolynomial (Fin d × σ) F}
    (hv : IsBlockMultilinear F d σ v) (hw : IsBlockMultilinear F d σ w) :
    IsBlockMultilinear F d σ (v + w) := by
  intro lam
  rw [map_add, hv lam, hw lam, smul_add]

#print axioms isBlockMultilinear_add

theorem isBlockMultilinear_smul (c : F) {v : MvPolynomial (Fin d × σ) F}
    (hv : IsBlockMultilinear F d σ v) : IsBlockMultilinear F d σ (c • v) := by
  intro lam
  rw [MvPolynomial.smul_eq_C_mul, map_mul, blockScaleR_C, hv lam]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  ring

#print axioms isBlockMultilinear_smul

/-- ★★★★ **多线性子模**（Aronhold 的 `A^mult`／`B^mult` 的载体）。 -/
noncomputable def multilinearSubmodule : Submodule F (MvPolynomial (Fin d × σ) F) where
  carrier := {v | IsBlockMultilinear F d σ v}
  zero_mem' := isBlockMultilinear_zero F d σ
  add_mem' := fun hv hw => isBlockMultilinear_add F d σ hv hw
  smul_mem' := fun c _ hv => isBlockMultilinear_smul F d σ c hv

#print axioms multilinearSubmodule

/-- ★★★★★ **`P` 落在多线性子模里**。 -/
theorem polarization_mem_multilinearSubmodule [Fintype σ] (f : MvPolynomial σ F) :
    polarization F d σ f ∈ multilinearSubmodule F d σ :=
  polarization_isBlockMultilinear F d σ f

#print axioms polarization_mem_multilinearSubmodule

/-! ## 切分第 20 步：α4 的**载体** —— `φ_A` 的逐块提升 `phiABlk`

（本节所有声明**自带显式 binder** `(F) [Field F] (r n d)`，不依赖文件级 `variable`——
文件里已有第二处 `variable (F) [Field F] (d) (σ)`，自动绑定次序易混。）

α4 要证「`P` 保持不变量性」。这需把 `φ_A`（作用在 `S = F[x_{k,i,j}]` 上）**提升到块环**
`A = F[x^{(l)}_{k,i,j}]`（逐块做同一个线性替换）。本节给提升的载体，**全部 `RingHom` 形态**（教训 47）：

* `blkMatrix j k`：块 `j` 的第 `k` 个通用矩阵；
* `constMatBlk`：常矩阵的块环版本；
* `phiGenBlk A`：`φ_A` 在块环上的取值（`constMatBlk A⁻¹ * blkMatrix * constMatBlk A`）；
* **`phiABlk A`**：`φ_A` 的逐块提升（`eval₂Hom`）；
* `phiABlk_X`／`phiABlk_C`：在不定元／常数上的值。

**射程**：本节只给**载体**。**交换律**（`map (phiABlk A) (polSubst a) = polSubst (phiGen A a)`，
即 `φ_A` 与极化替换的等变性）与 α4 主定理 `phiABlk A (P u) = P (phiA A u)`**未做**。
`hAdBd`、`hR`、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 块化的不定元矩阵：块 `j` 的第 `k` 个通用矩阵。 -/
noncomputable def blkMatrix (F : Type) [Field F] (r n d : ℕ) (j : Fin d) (k : Fin r) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :=
  fun i l => MvPolynomial.X (j, (k, i, l))

#print axioms blkMatrix

/-- 常矩阵的块环版本（系数嵌入）。 -/
noncomputable def constMatBlk (F : Type) [Field F] (r n d : ℕ) (M : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :=
  M.map (MvPolynomial.C)

#print axioms constMatBlk

/-- `φ_A` 在块环上的取值（逐块提升）。 -/
noncomputable def phiGenBlk (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (v : Fin d × (Fin r × Fin n × Fin n)) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
  (constMatBlk F r n d (↑A⁻¹) * blkMatrix F r n d v.1 v.2.1 * constMatBlk F r n d (↑A))
    v.2.2.1 v.2.2.2

#print axioms phiGenBlk

/-- ★★★★ **`φ_A` 的逐块提升**（`RingHom` 形态）。 -/
noncomputable def phiABlk (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F →+*
      MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
  MvPolynomial.eval₂Hom (algebraMap F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F))
    (phiGenBlk F r n d A)

#print axioms phiABlk

theorem phiABlk_X (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (v : Fin d × (Fin r × Fin n × Fin n)) :
    phiABlk F r n d A (MvPolynomial.X v) = phiGenBlk F r n d A v := by
  simp [phiABlk]

#print axioms phiABlk_X

theorem phiABlk_C (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : F) :
    phiABlk F r n d A (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [phiABlk]

#print axioms phiABlk_C


/-! ## 切分第 21 步：★★★ **不变量环 `T_n`**（`thm:12.1.3` 的左端）

`thm:12.1.3`（AGPR `:13892`）的陈述是「**不变量环**由迹生成」。此前仓内**没有**"不变量环"
这个对象本身（只有 `phiA_trace_word` 一类逐件的不变性引理）。本节把它定义出来：

```
invariantAlg r n := {g : S F r n | ∀ A : GL_n(F), phiA A g = g}
```

（`Subalgebra`：对乘、加、常数封闭；对 `φ_A` 封闭性逐条机检。）
它同时是 Aronhold 归约（§切分第 8 步）里的 **`A`**（`invariantSubmodule`）。

**射程**：本节只给**对象与基本 API**。`thm:12.1.3` 的**内容**（`T_n ⊆ 迹环` 与
`迹环 ⊆ T_n`）**均未证**；α4 的等变性
（`map (phiABlk A) (polSubst a) = polSubst (phiGen A a)`）本轮尝试未过（根因已记录，见 log）；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★ **不变量环 `T_n`**：被所有 `φ_A`（`A ∈ GL_n(F)`）固定的多项式构成的 `F`-子代数
（＝ `thm:12.1.3` 的左端 `T_n = T_n(X)`，AGPR `:13892`）。 -/
noncomputable def invariantAlg (F : Type) [Field F] (r n : ℕ) : Subalgebra F (S F r n) where
  carrier := {g | ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g}
  mul_mem' := by
    intro x y hx hy A
    rw [map_mul, hx A, hy A]
  one_mem' := by
    intro A
    rw [map_one]
  add_mem' := by
    intro x y hx hy A
    rw [map_add, hx A, hy A]
  zero_mem' := by
    intro A
    rw [map_zero]
  algebraMap_mem' := by
    intro c A
    exact (phiA F r n A).commutes c

#print axioms invariantAlg

/-- 成员刻画。 -/
theorem mem_invariantAlg_iff (F : Type) [Field F] (r n : ℕ) {g : S F r n} :
    g ∈ invariantAlg F r n ↔ ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g :=
  Iff.rfl

#print axioms mem_invariantAlg_iff

/-- 不变量环的 `F`-子模形态（Aronhold 的 `A`）。 -/
noncomputable def invariantSubmodule (F : Type) [Field F] (r n : ℕ) : Submodule F (S F r n) :=
  (invariantAlg F r n).toSubmodule

#print axioms invariantSubmodule

/-- 类型锁：载体一经改动立即编译失败。 -/
theorem invariantAlg_typeLock (F : Type) [Field F] (r n : ℕ) :
    (invariantAlg F r n : Set (S F r n))
      = {g | ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g} := rfl

#print axioms invariantAlg_typeLock

/-! ## 切分第 22 步：`phiGen`／`phiGenBlk` 的**显式双和形态**（等变性的重写用件）

α4 的等变性 `map (phiABlk A) (polSubst a) = polSubst (phiGen A a)` 上轮两次未过，
根因是**在 `aeval` 内部做 `conv`**（`Matrix.mul_apply` 第二次失败，报 "function expected" 且附注
"not type-correct under the `implicit` transparency level"——R258 的"defeq 但不同一"族）。

**正解（本轮兑现）**：先把 `phiGen`（`S` 层）与 `phiGenBlk`（块环层）各证成**显式双和**：

```
phiGen A (k,i,l)    = ∑ p ∑ q, C((A⁻¹) i q) · X (k,q,p) · C(A p l)
phiGenBlk A (j,k,i,l) = ∑ p ∑ q, C((A⁻¹) i q) · X (j,(k,q,p)) · C(A p l)
```

于是等变性可在**裸形态**上做（`aeval` 展开 → `polSubst` 展开 → 用 `Finset.sum_comm` 重排索引）。

**射程**：本节只给**双和形态**。等变性**仍未证**——剩余障碍已定位（log）：两侧的索引次序不同
（块指标在一侧最外、另一侧最内），须 `Finset.sum_comm` 两次 ＋ 常数 `algebraMap` 归一。
α4 主定理、`hAdBd`、`hR`、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`phiGen` 的显式双和形态**（供等变性重写用，避免在 `aeval` 内部做 `conv`）。 -/
theorem phiGen_eq (F : Type) [Field F] (r n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (a : Fin r × Fin n × Fin n) :
    phiGen F r n A a
      = ∑ p : Fin n, ∑ q : Fin n,
          algebraMap F (S F r n) ((↑A⁻¹ : Matrix (Fin n) (Fin n) F) a.2.1 q) * MvPolynomial.X (a.1, q, p)
            * algebraMap F (S F r n) ((↑A : Matrix (Fin n) (Fin n) F) p a.2.2) := by
  simp only [phiGen, constMat, Matrix.mul_apply, Matrix.map_apply, genericMatrix, genericEntry,
    Finset.sum_mul]


#print axioms phiGen_eq



/-- ★★★★ **`phiGenBlk` 的显式双和形态**（块环版，供等变性重写用）。 -/
theorem phiGenBlk_eq (F : Type) [Field F] (r n d : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (v : Fin d × (Fin r × Fin n × Fin n)) :
    phiGenBlk F r n d A v
      = ∑ p : Fin n, ∑ q : Fin n,
          algebraMap F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)
              ((↑A⁻¹ : Matrix (Fin n) (Fin n) F) v.2.2.1 q)
            * MvPolynomial.X (v.1, (v.2.1, q, p))
            * algebraMap F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)
              ((↑A : Matrix (Fin n) (Fin n) F) p v.2.2.2) := by
  simp only [phiGenBlk, constMatBlk, blkMatrix, Matrix.mul_apply, Matrix.map_apply,
    Finset.sum_mul, MvPolynomial.C_eq_algebraMap]

#print axioms phiGenBlk_eq

/-! ## 切分第 23 步：双和形态的 **`C`-版本**（等变性最后一个形式障碍的修法）

等变性 `map (phiABlk A) (polSubst a) = polSubst (phiGen A a)` 连续两轮未过。本轮把两侧展开到
**同一骨架**（三重和）后，定位出**最后两个**纯形式障碍：

1. **常数写法不同**：LHS 是 `C (C c)`（`C : F → Ablk` 再 `C : Ablk → B`），RHS 是
   `algebraMap F B c`。二者相等（标量塔），但 `simp` 不自动归一。
2. **索引次序不同**：LHS 的块指标在最外（`Fin d`），RHS 的在最内；中间两维是 `Fin n`。

修法①（本轮机检）：把 `phiGen`／`phiGenBlk` 的双和形态**改用 `C` 写**（`phiGen_eqC`／
`phiGenBlk_eqC`），于是 RHS 的常数也是 `C`-形态 ⟹ `aeval_C` 能直接作用（上一轮用 `algebraMap`
写时 `aeval_C` 报 "unused"）。

**射程**：本节只给 **`C`-形态双和**。**等变性仍未证**——修法②（索引重排）已定：把两侧都摊平到
**乘积型上的单和**（`Fintype.sum_prod_type`），再用 `Equiv.prodComm` 之类统一次序，最后逐项 `ring`。
α4 主定理、`hAdBd`、`hR`、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`phiGen` 的 `C`-形态双和**（等变性重写用；`C`-形态使 `aeval_C` 直接可用，
避免 `algebraMap`／`C` 两种写法混用）。 -/
theorem phiGen_eqC (F : Type) [Field F] (r n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (a : Fin r × Fin n × Fin n) :
    phiGen F r n A a
      = ∑ p : Fin n, ∑ q : Fin n,
          MvPolynomial.C ((↑A⁻¹ : Matrix (Fin n) (Fin n) F) a.2.1 q) * MvPolynomial.X (a.1, q, p)
            * MvPolynomial.C ((↑A : Matrix (Fin n) (Fin n) F) p a.2.2) := by
  rw [phiGen_eq]
  simp only [MvPolynomial.C_eq_algebraMap]

#print axioms phiGen_eqC

/-- ★★★★ **`phiGenBlk` 的 `C`-形态双和**。 -/
theorem phiGenBlk_eqC (F : Type) [Field F] (r n d : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (v : Fin d × (Fin r × Fin n × Fin n)) :
    phiGenBlk F r n d A v
      = ∑ p : Fin n, ∑ q : Fin n,
          MvPolynomial.C ((↑A⁻¹ : Matrix (Fin n) (Fin n) F) v.2.2.1 q)
            * MvPolynomial.X (v.1, (v.2.1, q, p))
            * MvPolynomial.C ((↑A : Matrix (Fin n) (Fin n) F) p v.2.2.2) := by
  rw [phiGenBlk_eq]
  simp only [MvPolynomial.C_eq_algebraMap]

#print axioms phiGenBlk_eqC

/-! ## 切分第 24 步：★★★★★★ **`thm:12.1.3` 的"迹 ⊆ 不变量"半边**

AGPR `:13901`（`thm:12.1.3` 的证明第一句，**逐字**）：
> "The ring of invariants of matrices **contains the ring generated by the traces of monomials**
> and both rings are stable under polarization and restitution, hence …"

本节把该句的**前半**机检（`S` 层，即多项式环层）：

```
traceAlgS r n := adjoin F (range (w ↦ tr(X_{k₁}⋯X_{k_m})))        -- 迹环
invariantAlg r n := {g | ∀ A : GL_n(F), phiA A g = g}              -- 不变量环
traceAlgS r n ≤ invariantAlg r n                                    -- ★ 迹 ⊆ 不变量
```

**机制（与原文的路子一致）**：`φ_A` 作用在字的积上是**共轭** `A⁻¹ W A`
（`map_phiA_wordProd`，由 `phiA_X` 逐因子归纳），而迹在循环置换下不变
（`Matrix.trace_mul_cycle` ＋ `constMat A * constMat A⁻¹ = 1`）⟹ `tr(A⁻¹WA) = tr(W)`。

**射程**：本节只给**半边**。`thm:12.1.3` 的另一半（**不变量 ⊆ 迹环**）**未证**——它正是
(Aronhold) 路线的主体；α4 的等变性、`hAdBd`、`hR`、β1、β2 未做；`hZ` 未证；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 词（`w : List (Fin r)`）的迹（`S` 层）：`tr(X_{k₁}⋯X_{k_m})`。 -/
noncomputable def traceWordS (F : Type) [Field F] (r n : ℕ) (w : List (Fin r)) : S F r n :=
  (w.map (genericMatrix F r n)).prod.trace

#print axioms traceWordS

theorem constMat_mul_inv (F : Type) [Field F] (r n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    constMat F r n (↑A) * constMat F r n (↑A⁻¹) = 1 := by
  rw [← constMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMat_one]

#print axioms constMat_mul_inv

/-- ★★★★ **`φ_A` 作用在字的矩阵积上**：`(X_{k₁}⋯X_{k_m}).map φ_A = A⁻¹ (X_{k₁}⋯X_{k_m}) A`。 -/
theorem map_phiA_wordProd (F : Type) [Field F] (r n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (w : List (Fin r)) :
    ((w.map (genericMatrix F r n)).prod).map (phiA F r n A)
      = constMat F r n (↑A⁻¹) * (w.map (genericMatrix F r n)).prod * constMat F r n (↑A) := by
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil,
      Matrix.map_one (phiA F r n A) (map_zero _) (map_one _), mul_one]
    have h := (constMat_mul_inv F r n A⁻¹).symm
    rwa [inv_inv] at h
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ih, phiA_X]
    calc constMat F r n (↑A⁻¹) * genericMatrix F r n k * constMat F r n (↑A) *
            (constMat F r n (↑A⁻¹) * (w.map (genericMatrix F r n)).prod * constMat F r n (↑A))
        = constMat F r n (↑A⁻¹) * genericMatrix F r n k *
            (constMat F r n (↑A) * constMat F r n (↑A⁻¹)) *
            (w.map (genericMatrix F r n)).prod * constMat F r n (↑A) := by
          noncomm_ring
      _ = constMat F r n (↑A⁻¹) * genericMatrix F r n k *
            (w.map (genericMatrix F r n)).prod * constMat F r n (↑A) := by
          rw [constMat_mul_inv, mul_one]
      _ = constMat F r n (↑A⁻¹) *
            (genericMatrix F r n k * (w.map (genericMatrix F r n)).prod) *
            constMat F r n (↑A) := by
          noncomm_ring

#print axioms map_phiA_wordProd

/-- ★★★★★ **字的迹是不变量**（`thm:12.1.3` 的"迹 ⊆ 不变量"半边）。 -/
theorem phiA_traceWord (F : Type) [Field F] (r n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (w : List (Fin r)) :
    phiA F r n A (traceWordS F r n w) = traceWordS F r n w := by
  rw [traceWordS, AddMonoidHom.map_trace (phiA F r n A), map_phiA_wordProd]
  rw [Matrix.trace_mul_cycle, constMat_mul_inv, one_mul]

#print axioms phiA_traceWord

/-- ★★★★★ **迹代数（`S` 层）**：由字的迹生成的 `F`-子代数（`thm:12.1.3` 的右端）。 -/
noncomputable def traceAlgS (F : Type) [Field F] (r n : ℕ) : Subalgebra F (S F r n) :=
  Algebra.adjoin F (Set.range (traceWordS F r n))

#print axioms traceAlgS

/-- ★★★★★★★ **`thm:12.1.3` 的"迹 ⊆ 不变量"半边**（AGPR `:13901`：The ring of invariants of
matrices **contains** the ring generated by the traces of monomials）。 -/
theorem traceAlgS_le_invariantAlg (F : Type) [Field F] (r n : ℕ) :
    traceAlgS F r n ≤ invariantAlg F r n := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro _ ⟨w, rfl⟩
  show ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A (traceWordS F r n w) = traceWordS F r n w
  exact fun A => phiA_traceWord F r n A w

#print axioms traceAlgS_le_invariantAlg

/-! ## 切分第 25 步：等变性的**常数归一**两件（形式障碍②的修法）

等变性两侧展开到三重和后，最后的差异只剩两条 **常数写法**：

* LHS 的常数呈 `C (C c)`（两层 `C`：`F → Ablk → B`）；
* RHS 的常数呈 `aeval (polSubst) (C c)`（或 `algebraMap F S c`）。

二者都等于 `algebraMap F B c`。本节把这两条**归一引理**机检：

* `aeval_polSubst_algebraMap`：`aeval polSubst (algebraMap F S c) = algebraMap F B c`；
* `C_C_eq_algebraMap`：`C (C c) = algebraMap F B c`（标量塔塌缩）。

**射程**：本节只给**常数归一**。等变性**仍未证**——剩余障碍**只剩索引次序**（块指标在 LHS
最外、RHS 最内），修法已定：两侧用 `Fintype.sum_prod_type` 摊平成乘积型单和 ＋ 一次
`Finset.sum_comm` ↦ 同一乘积型，再逐项 `ring`。α4 主定理、`thm:12.1.3` 另一半、`hAdBd`、
`hR`、β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 常数在 `aeval (polSubst)` 下的像。 -/
theorem aeval_polSubst_algebraMap (F : Type) [Field F] (r n d : ℕ) (c : F) :
    MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n)) (algebraMap F (S F r n) c)
      = algebraMap F (MvPolynomial (Fin d) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)) c := by
  rw [← MvPolynomial.C_eq_algebraMap F (Fin r × Fin n × Fin n)]
  rw [MvPolynomial.aeval_C]

#print axioms aeval_polSubst_algebraMap

/-- 两层 `C` 的塔塌缩：`C (C c) = algebraMap F B c`。 -/
theorem C_C_eq_algebraMap (F : Type) [Field F] (r n d : ℕ) (c : F) :
    MvPolynomial.C (MvPolynomial.C c : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)
      = algebraMap F (MvPolynomial (Fin d) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)) c := by
  rw [MvPolynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)
      (MvPolynomial (Fin d) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)) c]

#print axioms C_C_eq_algebraMap

/-! ## 切分第 26 步：★★★★★★★ **等变性收口 ＋ α4 主定理**（`P` 与 `φ_A` 交换）

连续 3 轮（R604/R606/R608，共 5 次）卡住的等变性，本轮**收口**。修法链：
1. **不在 `aeval` 内部做 `conv`**（R605：改在 `phiGen_eq` 的裸双和上展开）；
2. **常数归一**（R608：`aeval_polSubst_algebraMap` ＋ `C_C_eq_algebraMap`）；
3. **索引重排**（本轮正解）：展开后两侧是 `∑_{Fin d}∑_{Fin n}∑_{Fin n}` 与
   `∑_{Fin n}∑_{Fin n}∑_{Fin d}`；用 **`conv_rhs => enter [2, x]; rw [Finset.sum_comm]`**
   把 RHS 的两次求和调成与 LHS 同序，再 `Finset.sum_congr` 三层 ＋ `ring` 逐项收口。

由此得 **α4 主定理**：
```
phiABlk A (P f) = P (phiA A f)          （P 与 φ_A 交换 ⟹ P 保持不变量性）
```
链条：`coeff_map` → §17 的通用自然性 → 等变性 → `aeval` 复合（`aeval_comp_phiGen`）。

**意义**：Aronhold 归约（§切分第 8 步）的 `hP` 前提的**"不变量"半边**就此具备：
`u ∈ invariantAlg ⟹ P u ∈ invariantAlg`；与 §19 的多线性半边合起来
`P` 把不变量送进 **多线性不变量**子模。

**射程**：本节给等变性与 α4 主定理。`thm:12.1.3` 的另一半（不变量 ⊆ 迹环）、`hAdBd`、`hR`、
β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★★ **等变性**：`φ_A` 的逐块提升与极化替换交换（α4 关键一步）。 -/
theorem map_phiABlk_polSubst (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (a : Fin r × Fin n × Fin n) :
    MvPolynomial.map (phiABlk F r n d A) (polSubst F d (Fin r × Fin n × Fin n) a)
      = MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n)) (phiGen F r n A a) := by
  simp only [polSubst, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, phiABlk_X]
  rw [phiGen_eqC]
  simp only [aeval_polSubst_algebraMap, MvPolynomial.aeval_X, phiGenBlk_eqC, map_sum, map_mul,
    polSubst, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]
  conv_rhs => enter [2, x]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => ?_)))
  ring

#print axioms map_phiABlk_polSubst



/-- `map (phiABlk A)` 固定 `F`-常数（自然性的前提）。 -/
theorem phiABlk_map_base (F : Type) [Field F] (r n d : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (c : F) :
    MvPolynomial.map (phiABlk F r n d A)
        (algebraMap F (MvPolynomial (Fin d) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)) c)
      = algebraMap F (MvPolynomial (Fin d) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)) c := by
  rw [← C_C_eq_algebraMap F r n d c]
  rw [MvPolynomial.map_C, phiABlk_C]

#print axioms phiABlk_map_base



/-- `aeval` 的复合（`aeval polSubst ∘ aeval phiGen`）。 -/
theorem aeval_comp_phiGen (F : Type) [Field F] (r n d : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (f : MvPolynomial (Fin r × Fin n × Fin n) F) :
    MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n)) (MvPolynomial.aeval (phiGen F r n A) f)
      = MvPolynomial.aeval (fun a => MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n))
          (phiGen F r n A a)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p m hp => simp only [map_mul, MvPolynomial.aeval_X, hp]

#print axioms aeval_comp_phiGen

/-- ★★★★★★★ **α4 主定理**：`P` 与 `φ_A` 交换（`P` 保持不变量性）。 -/
theorem polarization_phiA (F : Type) [Field F] (r n d : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (f : MvPolynomial (Fin r × Fin n × Fin n) F) :
    phiABlk F r n d A (polarization F d (Fin r × Fin n × Fin n) f)
      = polarization F d (Fin r × Fin n × Fin n) (phiA F r n A f) := by
  rw [polarization, polarization]
  rw [show phiABlk F r n d A
        ((MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n)) f).coeff (onesFinsupp d))
      = (MvPolynomial.map (phiABlk F r n d A)
          (MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n)) f)).coeff
            (onesFinsupp d) from
    (MvPolynomial.coeff_map (phiABlk F r n d A) _ _).symm]
  rw [map_aeval_polSubst_general F d (Fin r × Fin n × Fin n) (MvPolynomial.map (phiABlk F r n d A))
    (phiABlk_map_base F r n d A) f]
  simp only [map_phiABlk_polSubst]
  show (MvPolynomial.aeval (fun a => MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n))
      (phiGen F r n A a)) f).coeff (onesFinsupp d)
    = (MvPolynomial.aeval (polSubst F d (Fin r × Fin n × Fin n))
        (MvPolynomial.aeval (phiGen F r n A) f)).coeff (onesFinsupp d)
  rw [aeval_comp_phiGen F r n d A f]

#print axioms polarization_phiA

/-! ## 切分第 27 步：★★★ **`hP` 完全打包** —— `P` 把不变量送进「多线性不变量」子模

`aronhold_reduction`（§切分第 8 步）的 **`hP`** 前提：`∀ u ∈ A, P u ∈ Ad`。本节把它完整兑现：

* `IsBlockInvariant`／`blockInvariantSubmodule`：块环上的"被所有 `φ_A` 逐块固定"子模；
* `polarization_isBlockInvariant`：`u` 不变量 ⟹ `P u` 是块不变量（α4 主定理 `polarization_phiA`
  的直接推论）；
* **`polarization_mem_inf`**：`u ∈ invariantAlg ⟹ P u ∈ multilinearSubmodule ⊓ blockInvariantSubmodule`
  —— 即 **`Ad := 多线性 ∩ 块不变量`**，`hP` **完全具备**。

于是 Aronhold 归约的四个前提中，`hP` 与 `hcomp`（`R∘P = d!`，§切分第 12 步）**已机检**，
只剩 `hAdBd`（多线性不变量 ⊆ 多线性迹 —— `lem:12.1.2` 的载体）与 `hR`（复原把多线性迹送回迹环）。

**射程**：本节只给 `hP`。`hAdBd`／`hR`／装配未做；`thm:12.1.3` 另一半未证；β1、β2 未做；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- **块环上的不变量**：被所有 `φ_A` 的逐块提升固定。 -/
def IsBlockInvariant (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) : Prop :=
  ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiABlk F r n d A v = v

#print axioms IsBlockInvariant

/-- ★★★★ **块不变量子模**。 -/
noncomputable def blockInvariantSubmodule (F : Type) [Field F] (r n d : ℕ) :
    Submodule F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) where
  carrier := {v | IsBlockInvariant F r n d v}
  zero_mem' := by
    intro A
    rw [map_zero]
  add_mem' := by
    intro x y hx hy A
    rw [map_add, hx A, hy A]
  smul_mem' := by
    intro c x hx A
    rw [MvPolynomial.smul_eq_C_mul, map_mul, phiABlk_C, hx A]

#print axioms blockInvariantSubmodule

/-- 成员刻画。 -/
theorem mem_blockInvariantSubmodule_iff (F : Type) [Field F] (r n d : ℕ)
    {v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F} :
    v ∈ blockInvariantSubmodule F r n d ↔ IsBlockInvariant F r n d v := Iff.rfl

#print axioms mem_blockInvariantSubmodule_iff

/-- ★★★★★ **`P` 把不变量送进块不变量**（α4 的直接推论）。 -/
theorem polarization_isBlockInvariant {F : Type} [Field F] (r n d : ℕ)
    {f : S F r n} (hf : f ∈ invariantAlg F r n) :
    IsBlockInvariant F r n d (polarization F d (Fin r × Fin n × Fin n) f) := by
  intro A
  rw [polarization_phiA F r n d A f]
  show polarization F d (Fin r × Fin n × Fin n) (phiA F r n A f)
    = polarization F d (Fin r × Fin n × Fin n) f
  rw [hf A]

#print axioms polarization_isBlockInvariant

/-- ★★★★★★★ **`hP` 完全打包**：`u` 不变量 ⟹ `P u` 同时是**块多线性**与**块不变量**。 -/
theorem polarization_mem_inf {F : Type} [Field F] (r n d : ℕ)
    {f : S F r n} (hf : f ∈ invariantAlg F r n) :
    polarization F d (Fin r × Fin n × Fin n) f
      ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ blockInvariantSubmodule F r n d :=
  ⟨polarization_mem_multilinearSubmodule (F := F) (d := d) (σ := Fin r × Fin n × Fin n) f,
    polarization_isBlockInvariant (F := F) r n d hf⟩

#print axioms polarization_mem_inf

/-! ## 切分第 28 步：★★★★ **`hR`** —— 复原把「块字迹」送回「字迹」

`aronhold_reduction`（§切分第 8 步）的 **`hR`** 前提：`∀ v ∈ Bd, R v ∈ B`。本节给出它在
**生成元层**的完整机检：

* `traceWordBlk j w`：**块字迹** `tr(M^{(j)}_{k₁}⋯M^{(j)}_{k_m})`（`M^{(j)}_k` ＝ `blkMatrix j k`）；
* `restitution_X`／`restitution_blkMatrix`：复原把块矩阵送成通用矩阵；
* **`restitution_traceWordBlk`**：`R(块字迹) = 字迹`（`R(tr(∏ M^{(j)})) = tr(∏ X)`）；
* **`restitution_adjoin_traceWordBlk_le`**：复原把**块 `j` 的整个迹代数**送进**迹代数**
  （`adjoin F (range 块字迹) ≤ (traceAlgS).comap R`）。

**射程**：这覆盖了 `hR` 的**单块生成元**情形。`hR` 的完整形态（多块、多线性、乘积闭合）与
`hAdBd`（多线性不变量 ⊆ 多线性迹）**未做**；装配未做；`thm:12.1.3` 另一半未证；β1、β2 未做；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 块环上的**字迹**：块 `j` 里的词积之迹。 -/
noncomputable def traceWordBlk (F : Type) [Field F] (r n d : ℕ) (j : Fin d) (w : List (Fin r)) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
  (w.map (fun k => blkMatrix F r n d j k)).prod.trace

#print axioms traceWordBlk

/-- 复原把块环的不定元送成通用矩阵的不定元。 -/
theorem restitution_X (F : Type) [Field F] (r n d : ℕ) (v : Fin d × (Fin r × Fin n × Fin n)) :
    restitution F d (Fin r × Fin n × Fin n) (MvPolynomial.X v) = MvPolynomial.X v.2 := by
  show MvPolynomial.aeval (fun v : Fin d × (Fin r × Fin n × Fin n) => MvPolynomial.X v.2)
    (MvPolynomial.X v) = MvPolynomial.X v.2
  rw [MvPolynomial.aeval_X]

#print axioms restitution_X

/-- 复原把块矩阵送成通用矩阵。 -/
theorem restitution_blkMatrix (F : Type) [Field F] (r n d : ℕ) (j : Fin d) (k : Fin r) :
    (blkMatrix F r n d j k).map (restitution F d (Fin r × Fin n × Fin n))
      = genericMatrix F r n k := by
  ext i l
  simp [blkMatrix, genericMatrix, genericEntry, restitution_X]

#print axioms restitution_blkMatrix

/-- ★★★★ **`hR` 的第一块**：复原把**块字迹**送回**字迹**（`restitution ∘ P` 的逆向行为）。 -/
theorem restitution_traceWordBlk (F : Type) [Field F] (r n d : ℕ) (j : Fin d)
    (w : List (Fin r)) :
    restitution F d (Fin r × Fin n × Fin n) (traceWordBlk F r n d j w)
      = traceWordS F r n w := by
  rw [traceWordBlk, traceWordS, AddMonoidHom.map_trace]
  congr 1
  induction w with
  | nil => simp
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Matrix.map_mul,
      restitution_blkMatrix, ih]

#print axioms restitution_traceWordBlk



/-- ★★★★★ **`hR` 的子代数形态**：复原把「块 `j` 的迹代数」整体送进「迹代数」。 -/
theorem restitution_adjoin_traceWordBlk_le (F : Type) [Field F] (r n d : ℕ) (j : Fin d) :
    Algebra.adjoin F (Set.range (traceWordBlk F r n d j))
      ≤ (traceAlgS F r n).comap (restitution F d (Fin r × Fin n × Fin n)) := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro _ ⟨w, rfl⟩
  show restitution F d (Fin r × Fin n × Fin n) (traceWordBlk F r n d j w) ∈ traceAlgS F r n
  rw [restitution_traceWordBlk]
  exact Algebra.subset_adjoin ⟨w, rfl⟩

#print axioms restitution_adjoin_traceWordBlk_le

/-! ## 切分第 29 步：★★★★★★ **`hR` 完整收口** —— 混块字迹

§28 的 `traceWordBlk` 只覆盖**单块**字迹；但 `T_σ`（AGPR `eq:12.3`）的迹侧形态是
**混块**字迹 `tr(M^{(j₁)}_{k₁} ⋯ M^{(j_m)}_{k_m})`（一次迹里可以混多个块）。本节把 `hR`
在**完整生成元层**收口：

* `blockTraceWord v`（`v : List (Fin d × Fin r)`）：**混块字迹**；
* `map_blockWordProd`（归纳：矩阵积在复原下逐因子变通用矩阵）；
* **`restitution_blockTraceWord`：`R(混块字迹) = 字迹`**；
* `blockTraceAlg`：**块迹代数**（`Bd` 的迹侧载体）；
* **`restitution_blockTraceAlg_le`：`blockTraceAlg ≤ traceAlgS.comap R`** —— **`hR` 收口**。

于是 Aronhold 归约的四个前提中，**三个已机检**：
`hP`（§27）、`hcomp`（§12）、`hR`（本节）；只剩 **`hAdBd`**（多线性不变量 ⊆ 多线性迹，
即 `lem:12.1.2` 的内容）与最终装配。

**射程**：本节给 `hR` 的完整形态。`hAdBd`／装配未做；`thm:12.1.3` 另一半未证；β1、β2 未做；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **混块字迹**：`tr(M^{(j₁)}_{k₁} ⋯ M^{(j_m)}_{k_m})`（各块可任意混合——
这正是 `T_σ`（`eq:12.3`）的迹侧形态）。 -/
noncomputable def blockTraceWord (F : Type) [Field F] (r n d : ℕ) (v : List (Fin d × Fin r)) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
  (v.map (fun ik => blkMatrix F r n d ik.1 ik.2)).prod.trace

#print axioms blockTraceWord

theorem map_blockWordProd (F : Type) [Field F] (r n d : ℕ) (v : List (Fin d × Fin r)) :
    ((v.map (fun ik => blkMatrix F r n d ik.1 ik.2)).prod).map
        (restitution F d (Fin r × Fin n × Fin n))
      = ((v.map Prod.snd).map (genericMatrix F r n)).prod := by
  induction v with
  | nil => simp
  | cons ik v ih =>
    rw [List.map_cons (f := fun ik : Fin d × Fin r => blkMatrix F r n d ik.1 ik.2),
      List.prod_cons, Matrix.map_mul, restitution_blkMatrix, ih]
    simp only [List.map_cons, List.prod_cons]

#print axioms map_blockWordProd

/-- ★★★★★ **`hR`（完整生成元层）**：复原把**混块字迹**送回**字迹**。 -/
theorem restitution_blockTraceWord (F : Type) [Field F] (r n d : ℕ) (v : List (Fin d × Fin r)) :
    restitution F d (Fin r × Fin n × Fin n) (blockTraceWord F r n d v)
      = traceWordS F r n (v.map Prod.snd) := by
  rw [blockTraceWord, traceWordS, AddMonoidHom.map_trace, map_blockWordProd]

#print axioms restitution_blockTraceWord

/-- ★★★★ **块迹代数**（`Bd` 的迹侧载体）：由混块字迹生成的 `F`-子代数。 -/
noncomputable def blockTraceAlg (F : Type) [Field F] (r n d : ℕ) :
    Subalgebra F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :=
  Algebra.adjoin F (Set.range (blockTraceWord F r n d))

#print axioms blockTraceAlg

/-- ★★★★★★★ **`hR` 的完整子代数形态**：复原把**整个块迹代数**送进**迹代数**。 -/
theorem restitution_blockTraceAlg_le (F : Type) [Field F] (r n d : ℕ) :
    blockTraceAlg F r n d
      ≤ (traceAlgS F r n).comap (restitution F d (Fin r × Fin n × Fin n)) := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro _ ⟨v, rfl⟩
  show restitution F d (Fin r × Fin n × Fin n) (blockTraceWord F r n d v) ∈ traceAlgS F r n
  rw [restitution_blockTraceWord]
  exact Algebra.subset_adjoin ⟨v.map Prod.snd, rfl⟩

#print axioms restitution_blockTraceAlg_le

/-! ## 切分第 30 步：★★★★★★★ **Aronhold 归约的具体化 ＝ FFT 难半只剩** `hAdBd`

```
homogeneous_invariant_mem_traceAlgS_of_adBd :
  (多线性 ∩ 块不变量  ≤  多线性 ∩ 块迹代数)          -- hAdBd
  ⟹ 每个 d 次齐次不变量 ∈ traceAlgS
```

这是本战役的**结构枢纽**：`thm:12.1.3` 的难半（不变量 ⊆ 迹环）从此**只依赖一个输入** `hAdBd`，
其余三个前提全部机检：

| Aronhold 前提 | 机检位置 |
|---|---|
| `hP`（不变量 ⟹ `P u` 多线性 ∩ 块不变量） | §27（`polarization_mem_inf`） |
| `hcomp`（`R ∘ P = d!`） | §12（`restitution_polarization`） |
| `hR`（块迹代数 ⟹ 迹代数） | §29（`restitution_blockTraceAlg_le`） |
| **`hAdBd`** | **本节取作假设** —— 即 `lem:12.1.2` 的内容 |

证明按 AGPR `:13901` 起的 Aronhold 路线逐条对应：`u` 齐次 `d` 次且不变量 ⟹ `P u ∈ Ad`
⟹（`hAdBd`）`P u ∈ Bd` ⟹（`hR`）`R(P u) ∈ traceAlgS` ⟹（`hcomp`）`d! • u ∈ traceAlgS`
⟹（`d! ≠ 0`，`CharZero`）`u ∈ traceAlgS`。

**射程**：本节把缺口**归约到一条**，但 `hAdBd` 本身**未证**（它是 `lem:12.1.2`：多线性不变量
＝ `T_σ` 线性组合 —— 需要 `eq:12.3` 的 `T_σ` 分解）；不变量环**等于**迹环（需要齐次分解）未做；
β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★★★ **Aronhold 归约的具体化**：`thm:12.1.3` 的难半（不变量 ⊆ 迹环）
**只差一个输入**——`hAdBd`（多线性块不变量 ⊆ 多线性块迹），逐齐次次数成立。

即：对任意 `CharZero` 域、任意 `n`、任意 `r`、任意次数 `d`，若
`多线性 ∩ 块不变量 ≤ 多线性 ∩ 块迹代数`，
则每个 `d` 次齐次不变量都是迹多项式。

**证明链**（与 AGPR `:13901` 起的 Aronhold 路线逐条对应）：
`invariantAlg ≤ traceAlgS` ⟸ `hP`（§27）＋ `hcomp`（§12：`R∘P = d!`）＋ `hR`（§29）＋ `hAdBd`。 -/
theorem homogeneous_invariant_mem_traceAlgS_of_adBd (F : Type) [Field F] [CharZero F]
    (r n d : ℕ)
    (hAdBd : multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ blockInvariantSubmodule F r n d
      ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ (blockTraceAlg F r n d).toSubmodule)
    {u : S F r n} (hui : u ∈ invariantAlg F r n) (huh : u.IsHomogeneous d) :
    u ∈ traceAlgS F r n := by
  have hPu : polarization F d (Fin r × Fin n × Fin n) u
      ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ blockInvariantSubmodule F r n d :=
    polarization_mem_inf (F := F) r n d hui
  have hBd : polarization F d (Fin r × Fin n × Fin n) u
      ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ (blockTraceAlg F r n d).toSubmodule :=
    hAdBd hPu
  have hR : restitution F d (Fin r × Fin n × Fin n)
      (polarization F d (Fin r × Fin n × Fin n) u) ∈ traceAlgS F r n :=
    (restitution_blockTraceAlg_le F r n d) hBd.2
  rw [restitution_polarization F d (Fin r × Fin n × Fin n) u huh] at hR
  have hsm : (d.factorial : F) • u ∈ traceAlgS F r n := by
    rw [Algebra.smul_def]
    exact hR
  have hu' : u = (d.factorial : F)⁻¹ • ((d.factorial : F) • u) := by
    rw [smul_smul, inv_mul_cancel₀ (factorial_ne_zero_of_charZero F d), one_smul]
  rw [hu']
  exact (traceAlgS F r n).smul_mem hsm ((d.factorial : F)⁻¹)

#print axioms homogeneous_invariant_mem_traceAlgS_of_adBd



/-- `hAdBd` 的**逐元形态**（下一轮攻它时用这个形状）。 -/
theorem adBd_elementwise (F : Type) [Field F] (r n d : ℕ)
    (hAdBd : multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ blockInvariantSubmodule F r n d
      ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ (blockTraceAlg F r n d).toSubmodule)
    {v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n))
    (hvi : v ∈ blockInvariantSubmodule F r n d) :
    v ∈ blockTraceAlg F r n d :=
  (hAdBd ⟨hv, hvi⟩).2

#print axioms adBd_elementwise

/-! ## 切分第 31 步：★★★★★★★ **`thm:12.1.3` 难半的最终归约**

```
invariantAlg ≤ traceAlgS
  ⟸ ① ∀ d, hAdBd d           （唯一实质缺口：多线性块不变量 ⊆ 多线性块迹代数）
  ⟸ ② hgrade                  （平凡：齐次分量仍是不变量 —— `φ_A` 保次数）
```

证明：`u = ∑_{i ≤ deg u} homogeneousComponent i u`（mathlib 的 `sum_homogeneousComponent`），
逐项套 §30 的 `homogeneous_invariant_mem_traceAlgS_of_adBd`。

至此 `thm:12.1.3` 的**难半**（不变量 ⊆ 迹环）在形式化上已**归约到一个数学命题** `hAdBd`
（`lem:12.1.2`）＋ 一条平凡的分次性；其余全部机检。

**射程**：`hAdBd` **未证**；`hgrade` **未证**（平凡但需"齐次分解唯一性 ＋ `φ_A` 保次数"，
API 已定位：`MvPolynomial.homogeneousComponent_eq_self`／`homogeneousComponent_of_mem`／
`rename_homogeneousComponent`，但 `phiA` 是一般线性替换、非 `rename`，故仍需一层论证）；
`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★★★ **FFT 难半的最终归约**：`thm:12.1.3` 的（不变量 ⊆ 迹环）由两件事推出：
① **`hAdBd`**（每个块数 `d`：多线性块不变量 ⊆ 多线性块迹代数）—— 唯一实质缺口；
② **分次性**（不变量的齐次分量仍是不变量）—— 平凡事实（`φ_A` 保次数）。

证明：`u = ∑_{i ≤ deg u} (homogeneousComponent i u)`，逐项用 §30 的
`homogeneous_invariant_mem_traceAlgS_of_adBd`。 -/
theorem invariantAlg_le_traceAlgS_of_adBd (F : Type) [Field F] [CharZero F] (r n : ℕ)
    (hAdBd : ∀ d : ℕ,
      multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ blockInvariantSubmodule F r n d
        ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ (blockTraceAlg F r n d).toSubmodule)
    (hgrade : ∀ (i : ℕ) {u : S F r n}, u ∈ invariantAlg F r n →
      homogeneousComponent i u ∈ invariantAlg F r n) :
    invariantAlg F r n ≤ traceAlgS F r n := by
  intro u hu
  have hdecomp : u = ∑ i ∈ Finset.range (u.totalDegree + 1), homogeneousComponent i u :=
    (MvPolynomial.sum_homogeneousComponent u).symm
  rw [hdecomp]
  refine Subalgebra.sum_mem _ ?_
  intro i _
  exact homogeneous_invariant_mem_traceAlgS_of_adBd F r n i (hAdBd i) (hgrade i hu)
    (MvPolynomial.homogeneousComponent_isHomogeneous i u)

#print axioms invariantAlg_le_traceAlgS_of_adBd

/-! ## 切分第 32 步：`hgrade` 的**分解唯一性**两件（recon 后照 mathlib API 拼装）

`hgrade`（不变量的齐次分量仍是不变量）需要一个事实：**次数互异的齐次元之和的分解是唯一的**。
本节机检两条（均 `ext` ＋ `coeff` 比较，用 `coeff_homogeneousComponent` 与
`IsHomogeneous.coeff_eq_zero`）：

* **`homogeneousComponent_eq_of_sum`**：若 `p = ∑_{j ∈ s} f_j` 且每个 `f_j` 齐次 `j` 次，
  则 `p` 的 `i` 次齐次分量 = `f i`（`i ∈ s`）；
* `homogeneousComponent_eq_zero_of_sum`：若 `p` 是 `N` 次以下齐次元之和，则 `i ≥ N` 的分量为 0。

**射程**：本节只给分解唯一性。`hgrade` 的**装配**（`phiA` 与 `homogeneousComponent` 交换）未做；
`hAdBd` 未证；`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；
H2 仍不是定理。 -/

/-- ★★★★ **齐次分解的唯一性**：若 `p` 是次数互异的齐次元之和，则 `p` 的 `i` 次齐次分量就是
紧挨 `i` 的那一项。 -/
theorem homogeneousComponent_eq_of_sum {F : Type} [Field F] {σ : Type} {p : MvPolynomial σ F}
    {f : ℕ → MvPolynomial σ F} {s : Finset ℕ} {i : ℕ} (hi : i ∈ s)
    (hsum : p = ∑ j ∈ s, f j) (hf : ∀ j ∈ s, (f j).IsHomogeneous j) :
    homogeneousComponent i p = f i := by
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent, hsum, MvPolynomial.coeff_sum]
  by_cases hd : Finsupp.degree d = i
  · rw [if_pos hd]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j hj hji
      exact MvPolynomial.IsHomogeneous.coeff_eq_zero (hf j hj) (by rw [hd]; exact fun h => hji h.symm)
    · intro hnotin
      exact absurd hi hnotin
  · rw [if_neg hd]
    exact (MvPolynomial.IsHomogeneous.coeff_eq_zero (hf i hi) hd).symm

#print axioms homogeneousComponent_eq_of_sum

/-- 若 `p` 是次数 `< N` 的齐次元之和，则 `p` 的 `i ≥ N` 次齐次分量为零。 -/
theorem homogeneousComponent_eq_zero_of_sum {F : Type} [Field F] {σ : Type}
    {p : MvPolynomial σ F} {f : ℕ → MvPolynomial σ F} {N i : ℕ}
    (hsum : p = ∑ j ∈ Finset.range N, f j)
    (hf : ∀ j ∈ Finset.range N, (f j).IsHomogeneous j) (hi : N ≤ i)
    (hfi : (f i).IsHomogeneous i) :
    homogeneousComponent i p = 0 := by
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent, hsum, MvPolynomial.coeff_sum]
  by_cases hd : Finsupp.degree d = i
  · rw [if_pos hd]
    exact Finset.sum_eq_zero (fun j hj => MvPolynomial.IsHomogeneous.coeff_eq_zero (hf j hj) (by
      have hj' := Finset.mem_range.mp hj
      omega))
  · rw [if_neg hd]
    simp

#print axioms homogeneousComponent_eq_zero_of_sum

/-! ## 切分第 33 步：★★★★★★★ **`hgrade` 收口 ＋ `thm:12.1.3` 难半的 `hAdBd` 单缺口版**

本节把 §32 的分解唯一性与 `φ_A` 保次数拼起来，**收掉 `hgrade`**，于是 `thm:12.1.3`
（AGPR 的 FFT 定理）的难半变成**只有一个数学假设**的定理：

```
invariantAlg_le_traceAlgS_of_hAdBd :
  (∀ d, 多线性 ∩ 块不变量 ≤ 多线性 ∩ 块迹代数)    -- 唯一假设 ＝ AGPR lem:12.1.2
  ⟹ 不变量环 ≤ 迹环
```

三件：
* `homogeneousComponent_phiA`：`φ_A` 与齐次分量**交换**（`i < N` 走 §32 的唯一性，
  `i ≥ N` 走 §32 的零性；`N = max (deg p + 1) (deg (φ_A p) + 1)`）；
* **`homogeneousComponent_mem_invariantAlg`（`hgrade`）**：`φ_A p = p ⟹ φ_A (hc i p) = hc i p`；
* **`invariantAlg_le_traceAlgS_of_hAdBd`**：与 §31 合并，`hgrade` 作为前提被自动提供。

**射程**：`hAdBd` **仍未证**（＝AGPR `lem:12.1.2`，唯一实质缺口）；`invariantAlg = traceAlgS`
（等式）未证；β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★ **`φ_A` 与齐次分量交换**（`hgrade` 的机械核心）。

**工艺（教训 54）**：`∑ j, homogeneousComponent j p` 里 `homogeneousComponent j` 是 `LinearMap`，
`∑` 记法会卡在 `AddCommMonoid ?m`；把它**先包成普通函数** `g : ℕ → S F r n` 即可。 -/
theorem homogeneousComponent_phiA (F : Type) [Field F] (r n : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (i : ℕ) (p : S F r n) :
    homogeneousComponent i (phiA F r n A p) = phiA F r n A (homogeneousComponent i p) := by
  set N := max (p.totalDegree + 1) ((phiA F r n A p).totalDegree + 1) with hN
  have hsum0' : (∑ j ∈ Finset.range N, (fun j => homogeneousComponent j p) j) = p := by
    rw [(Finset.sum_subset (s₁ := Finset.range (p.totalDegree + 1)) (s₂ := Finset.range N)
      (by intro j hj; simp only [Finset.mem_range] at *; omega) (by
        intro j _ hj
        simp only [Finset.mem_range] at hj
        exact MvPolynomial.homogeneousComponent_eq_zero (φ := p) (n := j) (by omega))).symm]
    exact MvPolynomial.sum_homogeneousComponent p
  have hsum0 : p = ∑ j ∈ Finset.range N, (fun j => homogeneousComponent j p) j := hsum0'.symm
  have hsum : phiA F r n A p
      = ∑ j ∈ Finset.range N, phiA F r n A ((fun j => homogeneousComponent j p) j) := by
    conv_lhs => rw [hsum0]
    rw [map_sum]
  have hhom : ∀ j : ℕ, (phiA F r n A (homogeneousComponent j p)).IsHomogeneous j := by
    intro j
    by_cases hj : j < p.totalDegree + 1
    · exact isHomogeneous_phiA (F := F) (r := r) (n := n) (d := j)
        (MvPolynomial.homogeneousComponent_isHomogeneous j p) A
    · have hzero : homogeneousComponent j p = 0 :=
        MvPolynomial.homogeneousComponent_eq_zero (φ := p) (n := j) (by omega)
      rw [hzero, map_zero]
      exact MvPolynomial.isHomogeneous_zero _ _ j
  rcases lt_or_ge i N with hi | hi
  · exact homogeneousComponent_eq_of_sum (s := Finset.range N) (Finset.mem_range.mpr hi) hsum
      (fun j _ => hhom j)
  · rw [homogeneousComponent_eq_zero_of_sum
      (f := fun j => phiA F r n A ((fun j => homogeneousComponent j p) j))
      (N := N) hsum (fun j _ => hhom j) hi (hhom i)]
    have hzero : homogeneousComponent i p = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero (φ := p) (n := i) (by omega)
    rw [hzero, map_zero]

#print axioms homogeneousComponent_phiA



/-- ★★★★★★ **`hgrade`**：不变量的齐次分量仍是不变量。 -/
theorem homogeneousComponent_mem_invariantAlg (F : Type) [Field F] (r n : ℕ) (i : ℕ)
    {u : S F r n} (hu : u ∈ invariantAlg F r n) :
    homogeneousComponent i u ∈ invariantAlg F r n := by
  show ∀ A : (Matrix (Fin n) (Fin n) F)ˣ,
    phiA F r n A (homogeneousComponent i u) = homogeneousComponent i u
  intro A
  rw [← homogeneousComponent_phiA F r n A i u, hu A]

#print axioms homogeneousComponent_mem_invariantAlg

/-- ★★★★★★★ **`thm:12.1.3` 难半（`hAdBd` 单缺口版，无附加假设）**。 -/
theorem invariantAlg_le_traceAlgS_of_hAdBd (F : Type) [Field F] [CharZero F] (r n : ℕ)
    (hAdBd : ∀ d : ℕ,
      multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ blockInvariantSubmodule F r n d
        ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ (blockTraceAlg F r n d).toSubmodule) :
    invariantAlg F r n ≤ traceAlgS F r n :=
  invariantAlg_le_traceAlgS_of_adBd F r n hAdBd
    (fun i _ hu => homogeneousComponent_mem_invariantAlg F r n i hu)

#print axioms invariantAlg_le_traceAlgS_of_hAdBd

/-! ## 切分第 34 步：★★★★★★ **`hAdBd` 的唯一数学内容被隔离出来**

**recon（本轮内容式侦察）**：`Procesi/FFTIdentification.lean:695` 的 `tSigma` 是**张量层**对象
（`tSigma σ x = trace(reindex σ * tensorPowerEndEquiv x)`，`k`-值），(γ) 的机检在那一层；
它**不能直接**喂给 `S` 层的 `hAdBd`。故本节在 `S` 层直接给出 `T_σ` 的**混块迹乘积**形态
（AGPR `eq:12.3`：`T_σ = ∏_i tr(W_i)`）：

* `tSigmaPoly vs`（`vs : List (List (Fin d × Fin r))`）：`T_σ` 型单项；
* **`tSigmaPoly_mem_blockTraceAlg`：`T_σ` ∈ 块迹代数** —— 故 `hAdBd` 的**迹侧自动**；
* `restitution_tSigmaPoly`／`restitution_tSigmaPoly_mem_traceAlgS`：复原把 `T_σ` 送进迹代数；
* `adjoin_tSigmaPoly_le_blockTraceAlg`：`T_σ` 生成的子代数 ≤ 块迹代数；
* **`adBd_of_tSigma`：`hAdBd` ⟸「多线性块不变量 ∈ `T_σ` 生成的子代数」**。

**于是 `hAdBd` 的全部数学内容 = 「多线性不变量 ＝ `T_σ` 的线性组合」（AGPR `lem:12.1.2` 正文）。**

**射程**：该正文**未证**；`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`T_σ` 型单项**：混块字迹的乘积 —— AGPR `eq:12.3` 的迹侧形态
（`T_σ = ∏_i tr(W_i)`；`vs i` 是第 `i` 个迹里的字，字里可混任意块）。 -/
noncomputable def tSigmaPoly (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r))) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
  (vs.map (blockTraceWord F r n d)).prod

#print axioms tSigmaPoly

/-- ★★★★ **`T_σ` 落在块迹代数里**（由 `blockTraceAlg` 的定义即得 ——
故 `hAdBd` 的**迹侧自动**，无需再证）。 -/
theorem tSigmaPoly_mem_blockTraceAlg (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r))) :
    tSigmaPoly F r n d vs ∈ blockTraceAlg F r n d := by
  rw [tSigmaPoly]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons]
    exact (blockTraceAlg F r n d).mul_mem
      (Algebra.subset_adjoin ⟨v, rfl⟩) ih

#print axioms tSigmaPoly_mem_blockTraceAlg

/-- ★★★★★ **复原把 `T_σ` 单项送成「字迹的乘积」**。 -/
theorem restitution_tSigmaPoly (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r))) :
    restitution F d (Fin r × Fin n × Fin n) (tSigmaPoly F r n d vs)
      = (vs.map (fun v => traceWordS F r n (v.map Prod.snd))).prod := by
  rw [tSigmaPoly]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul,
      restitution_blockTraceWord, ih]

#print axioms restitution_tSigmaPoly

/-- ★★★★★★ **复原把 `T_σ` 送进迹代数**（`hR` 在 `T_σ` 上的完整形态）。 -/
theorem restitution_tSigmaPoly_mem_traceAlgS (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r))) :
    restitution F d (Fin r × Fin n × Fin n) (tSigmaPoly F r n d vs) ∈ traceAlgS F r n := by
  rw [restitution_tSigmaPoly]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons]
    exact (traceAlgS F r n).mul_mem (Algebra.subset_adjoin ⟨v.map Prod.snd, rfl⟩) ih

#print axioms restitution_tSigmaPoly_mem_traceAlgS



/-- `T_σ` 单项生成的子代数落在块迹代数里。 -/
theorem adjoin_tSigmaPoly_le_blockTraceAlg (F : Type) [Field F] (r n d : ℕ) :
    Algebra.adjoin F (Set.range (tSigmaPoly F r n d)) ≤ blockTraceAlg F r n d := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro _ ⟨vs, rfl⟩
  exact tSigmaPoly_mem_blockTraceAlg F r n d vs

#print axioms adjoin_tSigmaPoly_le_blockTraceAlg

/-- ★★★★★★★ **`hAdBd` 的唯一数学内容**：只需证「多线性块不变量 ∈ `T_σ` 单项生成的子代数」
（即 AGPR `lem:12.1.2` 的正文）；**迹侧自动**。 -/
theorem adBd_of_tSigma (F : Type) [Field F] (r n d : ℕ)
    (h : ∀ v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F,
      v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n) →
      v ∈ blockInvariantSubmodule F r n d →
      v ∈ Algebra.adjoin F (Set.range (tSigmaPoly F r n d))) :
    multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ blockInvariantSubmodule F r n d
      ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ (blockTraceAlg F r n d).toSubmodule := by
  rintro v ⟨hv, hvi⟩
  exact ⟨hv, adjoin_tSigmaPoly_le_blockTraceAlg F r n d (h v hv hvi)⟩

#print axioms adBd_of_tSigma

/-! ## 切分第 35 步：★★★★★★★ **`hAdBd` 的精确刻画（充要）＋ AGPR `lem:12.1.2` 原文核对**

**原文核对（本轮按用户令回原文）**：`raw/AGPR2020.tex:13862` 的 `lem:12.1.2` 逐字为
> "The space `T_n(m)` of multilinear invariants of `m` matrices is identified with
> `End_{GL(V)}(V^{⊗m})`, and it is linearly spanned by the functions
> `T_σ(X_1,…,X_m) := tr(σ⁻¹ ∘ X_1 ⊗ ⋯ ⊗ X_m)`, `σ ∈ S_m`. If `σ = (i_1⋯i_h)⋯(s_1⋯s_t)` is the
> cycle decomposition, then `T_σ = tr(X_{i_1}⋯X_{i_h})⋯tr(X_{s_1}⋯X_{s_t})`."

**其证明的三步**（`:13874–13890`）：① 对偶 `End(V)^{⊗m}` ≅ `End(V)^{⊗m}`（配对 `tr(A∘B) = ∏tr(A_iB_i)`）；
② 多线性不变量 ↔ `GL(V)`-不变量，**"spanned by the elements of the symmetric group"**；
③ `eq:12.3` 靠多线性 ＋ 秩一化。

**本条（机器）**：`hAdBd` **等价于**「多线性 ∩ 块不变量 ⊆ `T_σ` 单项生成的子代数」，迹侧两向自动：
* `blockTraceWord_eq_tSigmaPoly`：单字 `T_σ` 单项 ＝ 块字迹；
* `blockTraceAlg_le_adjoin_tSigmaPoly`：块迹代数 ≤ `T_σ` 单项生成的子代数；
* **`adBd_iff_tSigma`：`hAdBd ⟺ 多线性 ∩ 块不变量 ⊆ adjoin (range tSigmaPoly)`**。

**射程**：`hAdBd` 的正文未证——其**原文证明的最后一步是 Schur–Weyl 型对偶**
（`End_{GL(V)}(V^{⊗m})` 由 `S_m` 张成）。按规则 23 已做 mathlib 内容式侦察：
`~/mathlib4/Mathlib/RepresentationTheory/` 下**无** Schur–Weyl 件（`grep -rl "SchurWeyl|Schur-Weyl"`
无命中）⟹ 该输入须自建或另寻外部项目（见 log 的侦察记录）。
`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 单字 `T_σ` 单项就是块字迹。 -/
theorem blockTraceWord_eq_tSigmaPoly (F : Type) [Field F] (r n d : ℕ)
    (v : List (Fin d × Fin r)) :
    blockTraceWord F r n d v = tSigmaPoly F r n d [v] := by
  rw [tSigmaPoly, List.map_singleton, List.prod_singleton]

#print axioms blockTraceWord_eq_tSigmaPoly

/-- 块迹代数 ≤ `T_σ` 单项生成的子代数。 -/
theorem blockTraceAlg_le_adjoin_tSigmaPoly (F : Type) [Field F] (r n d : ℕ) :
    blockTraceAlg F r n d ≤ Algebra.adjoin F (Set.range (tSigmaPoly F r n d)) := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro _ ⟨v, rfl⟩
  rw [blockTraceWord_eq_tSigmaPoly]
  exact Algebra.subset_adjoin ⟨[v], rfl⟩

#print axioms blockTraceAlg_le_adjoin_tSigmaPoly

/-- ★★★★★★★ **`hAdBd` 的精确刻画（充要）**：`hAdBd` **等价于**
「多线性块不变量落在 `T_σ` 单项生成的子代数里」——即 AGPR `lem:12.1.2` 的正文。
（迹侧的两个方向都自动：`tSigmaPoly_mem_blockTraceAlg` 与 `blockTraceAlg_le_adjoin_tSigmaPoly`。） -/
theorem adBd_iff_tSigma (F : Type) [Field F] (r n d : ℕ) :
    (multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ blockInvariantSubmodule F r n d
        ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ (blockTraceAlg F r n d).toSubmodule)
      ↔ (∀ v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F,
          v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n) →
          v ∈ blockInvariantSubmodule F r n d →
          v ∈ Algebra.adjoin F (Set.range (tSigmaPoly F r n d))) := by
  constructor
  · rintro h v hv hvi
    exact blockTraceAlg_le_adjoin_tSigmaPoly F r n d (h ⟨hv, hvi⟩).2
  · intro h
    exact adBd_of_tSigma F r n d h

#print axioms adBd_iff_tSigma

/-! ## 切分第 36 步：★★★★★★★ **`thm:12.1.3` 难半的 `T_σ` 最终形态**

**本轮侦察的重大发现**（内容式，仓内）：R619 判"Schur–Weyl 不在 mathlib"属实，但**本仓已用
TauCeti 把它机检在张量层**：
* `Procesi/FFTIdentification.lean:494` `mem_range_permTensorActionAlgHom_of_fixed`
  （共轭固定 ⟹ 落在 TauCeti `permTensorActionAlgHom` 的像里）；
* `:1227` `mem_span_tSigmaVec_of_fixed`（同一事实的 span 形态）；
* 依赖 `TauCeti.permTensorActionAlgHom_eq_sum`
  （`raw/TauCeti/TauCeti/RepresentationTheory/Symmetric/TensorAction/Basic.lean:144`）
  与 TauCeti 的双中心化子结果（见本仓 `FFTIdentification.lean:1198` 的注释）。
⟹ **`hAdBd` 的数学核心（Schur–Weyl 方向）不缺**，缺的是**张量层 → 多项式层（`S` 层）的搬运**。

本节两件：
* **`blockTraceAlg_eq_adjoin_tSigmaPoly`**：块迹代数 ＝ `T_σ` 单项生成的子代数
  （于是 `blockTraceAlg` 就是"`T_σ` 环"本身）；
* **`invariantAlg_le_traceAlgS_of_tSigma`**：若每个块数 `d` 的「多线性块不变量」都落在
  **`T_σ` 环**里（＝ AGPR `lem:12.1.2` 正文），则**不变量环 ⊆ 迹环**。

**射程**：`lem:12.1.2` 正文（`T_σ` 环的成员性）**未证** —— 其证明需把张量层的
`mem_span_tSigmaVec_of_fixed` 搬到 `S` 层；`invariantAlg = traceAlgS` 未证；β1、β2 未做；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★ **块迹代数 ＝ `T_σ` 单项生成的子代数**（两个方向 §34／§35 各一）。
于是 `blockTraceAlg` 就是 `T_σ` 环本身，`hAdBd` 的右端可直接写成 `T_σ` 环。 -/
theorem blockTraceAlg_eq_adjoin_tSigmaPoly (F : Type) [Field F] (r n d : ℕ) :
    blockTraceAlg F r n d = Algebra.adjoin F (Set.range (tSigmaPoly F r n d)) :=
  le_antisymm (blockTraceAlg_le_adjoin_tSigmaPoly F r n d)
    (adjoin_tSigmaPoly_le_blockTraceAlg F r n d)

#print axioms blockTraceAlg_eq_adjoin_tSigmaPoly

/-- ★★★★★★★ **`thm:12.1.3` 难半的最终形态（`T_σ` 版）**：若每个块数 `d` 的
「多线性块不变量」都落在 **`T_σ` 环**（`adjoin (range tSigmaPoly)`）里 —— 这正是 AGPR
`lem:12.1.2` 的正文 —— 则不变量环 ⊆ 迹环。 -/
theorem invariantAlg_le_traceAlgS_of_tSigma (F : Type) [Field F] [CharZero F] (r n : ℕ)
    (h : ∀ (d : ℕ) (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F),
      v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n) →
      v ∈ blockInvariantSubmodule F r n d →
      v ∈ Algebra.adjoin F (Set.range (tSigmaPoly F r n d))) :
    invariantAlg F r n ≤ traceAlgS F r n :=
  invariantAlg_le_traceAlgS_of_hAdBd F r n (fun d => adBd_of_tSigma F r n d (h d))

#print axioms invariantAlg_le_traceAlgS_of_tSigma

/-! ## 切分第 37 步：`T_σ` 记法的**拼接律**（循环分解字典的第一步）

AGPR `eq:12.3`：置换 `σ` 的**循环分解**给出 `T_σ = ∏_循环 tr(…)`。要在形式化里用这条，
需要 `tSigmaPoly`（字表之表）对**拼接**乘性：

* `tSigmaPoly_append`：`tSigmaPoly (vs₁ ++ vs₂) = tSigmaPoly vs₁ * tSigmaPoly vs₂`；
* `tSigmaPoly_singleton`：单字情形与 §34 的 `blockTraceWord` 互转。

**射程**：本节只给记法律。**张量层 → `S` 层的搬运**（`hAdBd` 正文的唯一缺口）未做；
`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★ **`T_σ` 单项对字表拼接是乘性的**（供把置换的**循环分解**翻译成 `tSigmaPoly`：
每个循环给一个 `blockTraceWord`，拼起来即 `T_σ`，见 AGPR `eq:12.3`）。 -/
theorem tSigmaPoly_append (F : Type) [Field F] (r n d : ℕ)
    (vs₁ vs₂ : List (List (Fin d × Fin r))) :
    tSigmaPoly F r n d (vs₁ ++ vs₂)
      = tSigmaPoly F r n d vs₁ * tSigmaPoly F r n d vs₂ := by
  rw [tSigmaPoly, List.map_append, List.prod_append]
  rfl

#print axioms tSigmaPoly_append

/-- 单字 `T_σ` 单项与块字迹互转（§34 的逆向陈述，便于两套记法互换）。 -/
theorem tSigmaPoly_singleton (F : Type) [Field F] (r n d : ℕ)
    (v : List (Fin d × Fin r)) :
    tSigmaPoly F r n d [v] = blockTraceWord F r n d v :=
  (blockTraceWord_eq_tSigmaPoly F r n d v).symm

#print axioms tSigmaPoly_singleton

/-! ## 切分第 38 步：★★★★ **搬运的第一步 —— `S` 层 `T_σ` 的取值语义**

v30 §10 的搬运段 2 要求「把 `S` 层的元**取值**（evaluate）到具体矩阵上」，以便与张量层的
泛函对接。本节就给这条取值语义，并机检 **AGPR `eq:12.3` 的计算内容在 `S` 层成立**：

* `evalBlock X`：块环在矩阵族 `X : Fin d × Fin r → M_n(F)` 上的取值（`MvPolynomial.eval`）；
* `evalBlock_blkMatrix`：块矩阵 ↦ 给定矩阵；
* `evalBlock_blockTraceWord`：**块字迹 ↦ 字积的迹**；
* **`evalBlock_tSigmaPoly`：`T_σ` 多项式 ↦ 迹的乘积**（`eq:12.3` 的取值形态）。

**射程**：本节只给**取值语义**。真正的搬运（张量层 `mem_span_tSigmaVec_of_fixed` → `S` 层
`T_σ` 环成员性）**未做**；`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；
`S'^N ⊆ Z` 未证；H2 仍不是定理 -/

/-- **块环在矩阵族上的取值**：`x^{(j)}_{k,i,l} ↦ (X (j,k))_{i l}`。 -/
noncomputable def evalBlock (F : Type) [Field F] (r n d : ℕ)
    (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F →+* F :=
  MvPolynomial.eval (fun v : Fin d × (Fin r × Fin n × Fin n) =>
    X (v.1, v.2.1) v.2.2.1 v.2.2.2)

#print axioms evalBlock

/-- 块矩阵在取值下就是给定的矩阵。 -/
theorem evalBlock_blkMatrix (F : Type) [Field F] (r n d : ℕ)
    (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) (j : Fin d) (k : Fin r) :
    (blkMatrix F r n d j k).map (evalBlock F r n d X) = X (j, k) := by
  ext i l
  simp [blkMatrix, evalBlock]

#print axioms evalBlock_blkMatrix

/-- ★★★★ **块字迹在取值下就是字积的迹**。 -/
theorem evalBlock_blockTraceWord (F : Type) [Field F] (r n d : ℕ)
    (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) (v : List (Fin d × Fin r)) :
    evalBlock F r n d X (blockTraceWord F r n d v) = (v.map X).prod.trace := by
  rw [blockTraceWord, AddMonoidHom.map_trace]
  congr 1
  induction v with
  | nil => simp
  | cons a v ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Matrix.map_mul,
      evalBlock_blkMatrix, ih]

#print axioms evalBlock_blockTraceWord

/-- ★★★★★ **`T_σ` 多项式取值就是迹的乘积**（AGPR `eq:12.3` 的**计算内容**在 `S` 层成立）。 -/
theorem evalBlock_tSigmaPoly (F : Type) [Field F] (r n d : ℕ)
    (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) (vs : List (List (Fin d × Fin r))) :
    evalBlock F r n d X (tSigmaPoly F r n d vs)
      = (vs.map (fun v => (v.map X).prod.trace)).prod := by
  rw [tSigmaPoly]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul,
      evalBlock_blockTraceWord, ih]

#print axioms evalBlock_tSigmaPoly

/-! ## 切分第 39 步：★★★★ **块不变性的取值形态**（与张量层"共轭固定"对齐）

搬运的关键是把 `S` 层的**块不变量**（`IsBlockInvariant`：被所有 `phiABlk A` 固定）翻成
**张量层的前提**（"被同时共轭固定"，即 `mem_span_tSigmaVec_of_fixed` 的 `hx`）。
本节给这条翻译的**取值形态**：

* `conjFam A X`：共轭后的矩阵族（按显式双和定义，便于与 `phiGenBlk_eqC` 对齐）；
* **`evalBlock_phiABlk`**：`evalBlock X (phiABlk A w) = evalBlock (conjFam A X) w`（取值等变性）；
* **`evalBlock_eq_of_isBlockInvariant`**：`w` 块不变 ⟹ **取值泛函对共轭固定**
  —— 与张量层 `mem_span_tSigmaVec_of_fixed` 的"共轭固定"前提**同一形态**。

**射程**：本节只把**不变性**翻译到取值形态。取值泛函 → 张量层元的**对偶识别**
（段 1／段 2 的其余部分）与 `hAdBd` 正文**未做**；`invariantAlg = traceAlgS` 未证；
β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- 共轭后的矩阵族（按显式双和定义，便于与 `phiGenBlk_eqC` 对齐）。 -/
noncomputable def conjFam (F : Type) [Field F] (r n d : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) :
    Fin d × Fin r → Matrix (Fin n) (Fin n) F :=
  fun jk i l => ∑ p : Fin n, ∑ q : Fin n,
    (↑A⁻¹ : Matrix (Fin n) (Fin n) F) i q * X jk q p * (↑A : Matrix (Fin n) (Fin n) F) p l

#print axioms conjFam

/-- ★★★★ **取值的等变性**：块不变量在取值下 ＝ 共轭矩阵族上的取值。 -/
theorem evalBlock_phiABlk (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F)
    (w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :
    evalBlock F r n d X (phiABlk F r n d A w)
      = evalBlock F r n d (conjFam F r n d A X) w := by
  induction w using MvPolynomial.induction_on with
  | C c => rw [phiABlk_C]; simp [evalBlock]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have hpt : evalBlock F r n d X (phiGenBlk F r n d A v)
        = evalBlock F r n d (conjFam F r n d A X) (MvPolynomial.X v) := by
      rw [phiGenBlk_eqC]
      simp only [map_sum, map_mul, evalBlock, MvPolynomial.eval_C, MvPolynomial.eval_X, conjFam]
    simp only [map_mul, hp, phiABlk_X, hpt]

#print axioms evalBlock_phiABlk



/-- ★★★★★ **块不变 ⟹ 取值泛函对共轭固定**（与张量层 `mem_span_tSigmaVec_of_fixed`
的"共轭固定"前提**同一形态**）。 -/
theorem evalBlock_eq_of_isBlockInvariant (F : Type) [Field F] (r n d : ℕ)
    {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hw : IsBlockInvariant F r n d w) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) :
    evalBlock F r n d X w = evalBlock F r n d (conjFam F r n d A X) w := by
  rw [← evalBlock_phiABlk F r n d A X w, hw A]

#print axioms evalBlock_eq_of_isBlockInvariant

/-! ## 切分第 40 步：★★★★★ **`T_σ` 是块不变量**（`hAdBd` 两侧的相容性检查）

`hAdBd` 断言「多线性 ∩ 块不变量 ⊆ 多线性 ∩ 块迹代数」。其中**块迹代数一侧**的元素
（`T_σ` 单项）**是否满足左侧的"块不变量"条件**，是这条包含关系的**相容性前提**——本节把它机检：

* `phiABlk_blkMatrix`：`phiABlk` 作用在块矩阵上是**共轭**；
* `constMatBlk_mul_inv`：`constMatBlk A * constMatBlk A⁻¹ = 1`；
* `map_phiABlk_blockWordProd`：`phiABlk` 作用在块字积上 ＝ 共轭（同 §24 的 `map_phiA_wordProd`）；
* **`phiABlk_blockTraceWord`：块字迹在 `phiABlk` 下不变**（共轭不改迹，`Matrix.trace_mul_cycle`）；
* **`phiABlk_tSigmaPoly`／`tSigmaPoly_mem_blockInvariantSubmodule`：`T_σ` 单项是块不变量**。

**射程**：本节只给**相容性**。`hAdBd` 正文（多线性块不变量 ⊆ `T_σ` 环）**未证**——尚缺
张量层 → `S` 层的对偶识别；`invariantAlg = traceAlgS` 未证；β1、β2 未做；`hZ` 未证；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- `phiABlk` 作用在块矩阵上是**共轭**。 -/
theorem phiABlk_blkMatrix (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (j : Fin d) (k : Fin r) :
    (blkMatrix F r n d j k).map (phiABlk F r n d A)
      = constMatBlk F r n d (↑A⁻¹) * blkMatrix F r n d j k * constMatBlk F r n d (↑A) := by
  apply Matrix.ext
  intro i l
  show phiABlk F r n d A (MvPolynomial.X (j, (k, i, l)))
      = (constMatBlk F r n d (↑A⁻¹) * blkMatrix F r n d j k * constMatBlk F r n d (↑A)) i l
  rw [phiABlk_X]
  rfl

#print axioms phiABlk_blkMatrix

/-- `constMatBlk A * constMatBlk A⁻¹ = 1`。 -/
theorem constMatBlk_mul_inv (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    constMatBlk F r n d (↑A) * constMatBlk F r n d (↑A⁻¹) = 1 := by
  rw [constMatBlk, constMatBlk, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.map_one (MvPolynomial.C) (map_zero _) (map_one _)]

#print axioms constMatBlk_mul_inv

/-- `phiABlk` 作用在块字积上是**共轭**（同 §24 的 `map_phiA_wordProd`）。 -/
theorem map_phiABlk_blockWordProd (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (v : List (Fin d × Fin r)) :
    ((v.map (fun ik => blkMatrix F r n d ik.1 ik.2)).prod).map (phiABlk F r n d A)
      = constMatBlk F r n d (↑A⁻¹) *
          (v.map (fun ik => blkMatrix F r n d ik.1 ik.2)).prod *
          constMatBlk F r n d (↑A) := by
  induction v with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [Matrix.map_one (phiABlk F r n d A) (map_zero _) (map_one _), mul_one]
    have h := (constMatBlk_mul_inv F r n d A⁻¹).symm
    rwa [inv_inv] at h
  | cons a v ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.map_mul, phiABlk_blkMatrix, ih]
    calc constMatBlk F r n d (↑A⁻¹) * blkMatrix F r n d a.1 a.2 * constMatBlk F r n d (↑A) *
            (constMatBlk F r n d (↑A⁻¹) *
              (List.map (fun ik => blkMatrix F r n d ik.1 ik.2) v).prod *
              constMatBlk F r n d (↑A))
        = constMatBlk F r n d (↑A⁻¹) * blkMatrix F r n d a.1 a.2 *
            (constMatBlk F r n d (↑A) * constMatBlk F r n d (↑A⁻¹)) *
            (List.map (fun ik => blkMatrix F r n d ik.1 ik.2) v).prod *
            constMatBlk F r n d (↑A) := by noncomm_ring
      _ = constMatBlk F r n d (↑A⁻¹) * blkMatrix F r n d a.1 a.2 *
            (List.map (fun ik => blkMatrix F r n d ik.1 ik.2) v).prod *
            constMatBlk F r n d (↑A) := by rw [constMatBlk_mul_inv, mul_one]
      _ = constMatBlk F r n d (↑A⁻¹) *
            (blkMatrix F r n d a.1 a.2 *
              (List.map (fun ik => blkMatrix F r n d ik.1 ik.2) v).prod) *
            constMatBlk F r n d (↑A) := by noncomm_ring

#print axioms map_phiABlk_blockWordProd

/-- ★★★★★ **块字迹在 `phiABlk` 下不变**（共轭不改迹）。 -/
theorem phiABlk_blockTraceWord (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (v : List (Fin d × Fin r)) :
    phiABlk F r n d A (blockTraceWord F r n d v) = blockTraceWord F r n d v := by
  rw [blockTraceWord, AddMonoidHom.map_trace, map_phiABlk_blockWordProd]
  show (constMatBlk F r n d (↑A⁻¹) *
    (v.map (fun ik => blkMatrix F r n d ik.1 ik.2)).prod * constMatBlk F r n d (↑A)).trace = _
  rw [Matrix.trace_mul_cycle, constMatBlk_mul_inv, one_mul]

#print axioms phiABlk_blockTraceWord



/-- ★★★★★ **`T_σ` 单项是块不变量**（乘性）。 -/
theorem phiABlk_tSigmaPoly (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (vs : List (List (Fin d × Fin r))) :
    phiABlk F r n d A (tSigmaPoly F r n d vs) = tSigmaPoly F r n d vs := by
  rw [tSigmaPoly]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, phiABlk_blockTraceWord, ih]

#print axioms phiABlk_tSigmaPoly

/-- ★★★★★ **`T_σ` 落在块不变量子模里**（与 §27 的 `polarization_mem_inf` 同侧）。 -/
theorem tSigmaPoly_mem_blockInvariantSubmodule (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r))) :
    tSigmaPoly F r n d vs ∈ blockInvariantSubmodule F r n d :=
  fun A => phiABlk_tSigmaPoly F r n d A vs

#print axioms tSigmaPoly_mem_blockInvariantSubmodule

/-! ## 切分第 41 步：★★★★★★ **块多线性的单项式判据 ＋ 系数展开 ＋ 标签分裂**
（搬运段 3 的第 1 块；第 626 轮）

`hAdBd` 的正文（AGPR `lem:12.1.2`）经 §33／§35 已化归为
「多线性 ∩ 块不变量 ⊆ `T_σ` 单项生成的子代数」。要把它落地，第一步必须把
**`IsBlockMultilinear`（定义在整体缩放律上）**翻成**单项式形态**：

```
v 块多线性  ⟺  v 的每个单项式在**每个块里恰含一个不定元**
```

本节就机检这条判据，并给出三条推论（它们是后续搬运的三根支柱）：

* **`coeff_blockScaleR`**：块缩放 `λ` 只按「各块次数」缩放系数
  （`coeff m (blockScaleR λ v) = (∏ x, λ x.1 ^ m x) * coeff m v`）；
* **`slotDeg_eq_one_of_isBlockMultilinear`**：非零系数 ⟹ 每块次数 ＝ 1
  （用 `t`-缩放 ＋ 单变量多项式 `X^k - X` 消去次数歧义——**这是"块多线性"唯一的数学内容**）；
* **`isBlockMultilinear_expansion`**：`v = ∑_{g : Fin d → σ} monomial (expOf g) (coeff …)`
  （**系数展开**：块多线性多项式由其"每块一个标签"的系数唯一决定）；
* **`sum_killLabels`**：`v = ∑_g killLabels g v`（**标签分裂**：按每个块的标签把 `v` 分块）。

**为何这是搬运的支柱**：`mem_span_tSigmaVec_of_fixed` 只对 `m = d` 个 `End V` 因子给出张成，
而块环每个块带 `r` 个矩阵标签。**标签分裂把问题化归到"固定标签向量"上**——在每个
固定标签向量里，`r` 个标签只用到 1 个，于是 `m = d` 的 Schur–Weyl 件可直接用。

**射程（诚实边界）**：本节只给**多项式层的判据与分解**。**未做**：由块不变性推出
「固定标签切片的共轭不变性」（＝ §39 的 `killLabels` 交换性 `killLabels ∘ phiABlk`）、
张量层的对偶运输、以及 `hAdBd` 正文本身。`invariantAlg = traceAlgS` 未证；
β1、β2 未做；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `∑ x ∈ s, …` 须写 `∈` 形式（本轮 `∑ x in s` 直接解析失败）；
② `expOf`／`killLabels` 需要 `[DecidableEq σ]`（`if` 的可判定性），`slotDeg` 需要 `[Fintype σ]`；
③ `if_pos`／`if_neg` 在本 pin 已弃用 ⟹ 用 `ite_eq_left`／`ite_eq_right`；
④ `Finsupp.prod` 在目标里可直接 `rw`（本轮未遇 log 记载的"展开后不匹配"）。 -/

/-- 一般指标型上的缩放单项式律。 -/
theorem prod_scale_monomial_gen {A : Type*} [CommSemiring A] {ρ : Type*} [Fintype ρ]
    (c : ρ → A) (s : ρ →₀ ℕ) :
    (s.prod fun v k => (MvPolynomial.C (c v) * MvPolynomial.X v
      : MvPolynomial ρ A) ^ k)
      = MvPolynomial.monomial s (∏ v, c v ^ s v) := by
  rw [Finsupp.prod_pow]
  rw [Finset.prod_congr rfl
    (fun v _ => mul_pow (MvPolynomial.C (c v)) (MvPolynomial.X v) (s v))]
  have h1 : (∏ x, (MvPolynomial.C (c x) : MvPolynomial ρ A) ^ s x)
      = MvPolynomial.C (∏ x, c x ^ s x) := by
    rw [Finset.prod_congr rfl (fun j _ => (MvPolynomial.C_pow (c j) (s j)).symm)]
    exact (map_prod (MvPolynomial.C : A →+* MvPolynomial ρ A)
      (fun j => c j ^ s j) Finset.univ).symm
  have h2 : (∏ x, (MvPolynomial.X x : MvPolynomial ρ A) ^ s x)
      = s.prod (fun n e => MvPolynomial.X n ^ e) :=
    (Finsupp.prod_pow s (fun x => MvPolynomial.X x)).symm
  rw [Finset.prod_mul_distrib, h1, h2, MvPolynomial.monomial_eq]

#print axioms prod_scale_monomial_gen

/-- 块缩放在单项式上的值。 -/
theorem blockScaleR_monomial (d : ℕ) (σ : Type) [Fintype σ]
    (lam : Fin d → F) (s : Fin d × σ →₀ ℕ) (a : F) :
    blockScaleR F d σ lam (MvPolynomial.monomial s a)
      = MvPolynomial.C (a * ∏ v, lam v.1 ^ s v) * MvPolynomial.monomial s 1 := by
  have h := MvPolynomial.eval₂Hom_monomial
    (algebraMap F (MvPolynomial (Fin d × σ) F))
    (fun v : Fin d × σ => MvPolynomial.C (lam v.1) * MvPolynomial.X v) s a
  rw [show blockScaleR F d σ lam (MvPolynomial.monomial s a)
      = (algebraMap F (MvPolynomial (Fin d × σ) F) a)
        * s.prod (fun v k => (MvPolynomial.C (lam v.1) * MvPolynomial.X v
            : MvPolynomial (Fin d × σ) F) ^ k) from h]
  rw [prod_scale_monomial_gen (fun v : Fin d × σ => lam v.1) s]
  rw [← MvPolynomial.C_eq_algebraMap, MvPolynomial.C_mul_monomial,
    MvPolynomial.C_mul_monomial]
  congr 1
  ring

#print axioms blockScaleR_monomial

/-- ★ 系数公式：块缩放只按「各块次数」缩放 `m`-系数。 -/
theorem coeff_blockScaleR (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ]
    (lam : Fin d → F) (m : Fin d × σ →₀ ℕ) (v : MvPolynomial (Fin d × σ) F) :
    (blockScaleR F d σ lam v).coeff m
      = (∏ x, lam x.1 ^ m x) * v.coeff m := by
  conv_lhs => rw [MvPolynomial.as_sum v]
  simp only [map_sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl (g := fun s => if m = s then
      (∏ x, lam x.1 ^ m x) * v.coeff s else 0) ?_]
  · by_cases hm : m ∈ v.support
    · rw [Finset.sum_eq_single m]
      · simp
      · intro s _ hsm
        rw [ite_eq_right (Ne.symm hsm)]
      · intro h
        exact absurd hm h
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
      refine Finset.sum_eq_zero (fun s hs => ?_)
      rw [ite_eq_right]
      intro h
      exact hm (h ▸ hs)
  · intro s _
    rw [blockScaleR_monomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    by_cases h : s = m
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]; ring
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      ring

#print axioms coeff_blockScaleR

/-- 单项式 `e` 在**块 `j`** 里的总次数（＝块 `j` 的标签上的指数和）。 -/
noncomputable def slotDeg {σ : Type} [Fintype σ] (d : ℕ) (j : Fin d)
    (e : Fin d × σ →₀ ℕ) : ℕ :=
  ∑ a : σ, e (j, a)

#print axioms slotDeg

/-- 单块取值：`λ = 1` 除第 `j` 块取 `t`。 -/
theorem prod_ite_slotDeg {σ : Type} [Fintype σ] (d : ℕ) (j : Fin d) (t : F)
    (e : Fin d × σ →₀ ℕ) :
    (∏ x, (if x.1 = j then t else 1) ^ e x) = t ^ slotDeg d j e := by
  classical
  rw [← Finset.univ_product_univ, Finset.prod_product, Finset.prod_eq_single j]
  · rw [show (∏ a : σ, (if (j, a).1 = j then t else 1) ^ e (j, a))
        = ∏ a : σ, t ^ e (j, a) from by simp]
    rw [Finset.prod_pow_eq_pow_sum, slotDeg]
  · intro j' _ hj'
    exact Finset.prod_eq_one (fun a _ => by simp [hj'])
  · intro h
    exact absurd (Finset.mem_univ j) h

#print axioms prod_ite_slotDeg

/-- 单块 `t`-缩放的系数读数。 -/
theorem coeff_blockScaleR_slot (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ]
    (j : Fin d) (t : F) (m : Fin d × σ →₀ ℕ) (v : MvPolynomial (Fin d × σ) F) :
    (blockScaleR F d σ (fun i => if i = j then t else 1) v).coeff m
      = t ^ slotDeg d j m * v.coeff m := by
  rw [coeff_blockScaleR, prod_ite_slotDeg]

#print axioms coeff_blockScaleR_slot

/-- ★★★★★ **块多线性 ⟹ 每块次数 ＝ 1**（在非零系数上）。 -/
theorem slotDeg_eq_one_of_isBlockMultilinear (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ]
    [Infinite F] {v : MvPolynomial (Fin d × σ) F} (hv : IsBlockMultilinear F d σ v)
    {m : Fin d × σ →₀ ℕ} (hm : v.coeff m ≠ 0) (j : Fin d) : slotDeg d j m = 1 := by
  classical
  have hstep : ∀ t : F, t ^ slotDeg d j m = t := by
    intro t
    have h := hv (fun i => if i = j then t else 1)
    have h2 : (blockScaleR F d σ (fun i => if i = j then t else 1) v).coeff m
        = ((∏ i, (if i = j then t else 1)) • v).coeff m := by rw [h]
    rw [coeff_blockScaleR_slot, MvPolynomial.coeff_smul] at h2
    have hprod : (∏ i : Fin d, (if i = j then t else 1)) = t := by
      rw [Finset.prod_eq_single_of_mem j (Finset.mem_univ j) (fun b _ hb => by simp [hb])]
      simp
    rw [hprod] at h2
    exact mul_right_cancel₀ hm h2
  have hp : (Polynomial.X ^ slotDeg d j m - Polynomial.X : Polynomial F) = 0 := by
    apply Polynomial.funext
    intro t
    simp [hstep t, Polynomial.eval_pow]
  have h1 := congrArg (fun p : Polynomial F => p.coeff 1) hp
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_zero, sub_eq_zero] at h1
  split_ifs at h1 with h
  · exact h.symm
  · exact absurd h1 (zero_ne_one (α := F))

#print axioms slotDeg_eq_one_of_isBlockMultilinear

/-- ★★★★★ **单块次数 1 ⟹ 该块恰有一个标签取指数 1**（其余标签指数 0）。 -/
theorem slot_one_of_slotDeg_eq_one {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) (j : Fin d)
    {e : Fin d × σ →₀ ℕ} (he : slotDeg (σ := σ) d j e = 1) :
    ∃ a : σ, e (j, a) = 1 ∧ ∀ b : σ, e (j, b) = if b = a then 1 else 0 := by
  classical
  have hex : ∃ a : σ, e (j, a) ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hzero : slotDeg (σ := σ) d j e = 0 := by
      rw [slotDeg, Finset.sum_eq_zero (fun a _ => h a)]
    omega
  obtain ⟨a₀, ha₀⟩ := hex
  have hle : e (j, a₀) ≤ slotDeg (σ := σ) d j e :=
    Finset.single_le_sum (f := fun a : σ => e (j, a)) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ a₀)
  have h1 : e (j, a₀) = 1 := by omega
  refine ⟨a₀, h1, fun b => ?_⟩
  by_cases hb : b = a₀
  · subst hb; simp [h1]
  · have herase : ∑ a ∈ Finset.univ.erase a₀, e (j, a) = 0 := by
      have h := Finset.add_sum_erase (s := (Finset.univ : Finset σ))
        (f := fun a => e (j, a)) (Finset.mem_univ a₀)
      rw [slotDeg] at he
      omega
    have hb' : e (j, b) ≤ ∑ a ∈ Finset.univ.erase a₀, e (j, a) :=
      Finset.single_le_sum (f := fun a : σ => e (j, a)) (fun i _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
    rw [ite_eq_right hb]
    omega

#print axioms slot_one_of_slotDeg_eq_one

/-- 「每块一个标签」的指数向量：`(j, a) ↦ if a = g j then 1 else 0`。 -/
noncomputable def expOf {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) (g : Fin d → σ) :
    Fin d × σ →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun x : Fin d × σ => if x.2 = g x.1 then 1 else 0)
    (fun x _ => Finset.mem_univ x)

#print axioms expOf

/-- `expOf` 的取值律（定义即得）。 -/
theorem expOf_apply {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) (g : Fin d → σ)
    (j : Fin d) (a : σ) :
    expOf d g (j, a) = if a = g j then 1 else 0 := rfl

#print axioms expOf_apply

/-- `expOf` 是单射（用每个块自己的标签取值即可分离）。 -/
theorem expOf_injective {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) :
    Function.Injective (expOf (σ := σ) d) := by
  intro g g' h
  funext j
  have h1 : expOf d g (j, g j) = expOf d g' (j, g j) := by rw [h]
  rw [expOf_apply, expOf_apply, ite_eq_left rfl] at h1
  by_contra hne
  rw [ite_eq_right hne] at h1
  exact one_ne_zero h1

#print axioms expOf_injective

/-- ★★★★★ **每块次数 1 ⟹ 指数向量恰是「每块一个标签」形态**。 -/
theorem exists_expOf_of_slotDeg_one {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ)
    {e : Fin d × σ →₀ ℕ} (he : ∀ j, slotDeg (σ := σ) d j e = 1) :
    ∃ g : Fin d → σ, e = expOf d g := by
  classical
  choose g hg1 hg2 using fun j => slot_one_of_slotDeg_eq_one (σ := σ) d j (he j)
  refine ⟨g, ?_⟩
  ext x
  obtain ⟨j, a⟩ := x
  rw [hg2 j a, expOf_apply]

#print axioms exists_expOf_of_slotDeg_one

/-- ★★★★★★ **块多线性多项式的系数展开**（每个单项式每块恰一个不定元）。 -/
theorem isBlockMultilinear_expansion (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ]
    [Infinite F] {v : MvPolynomial (Fin d × σ) F} (hv : IsBlockMultilinear F d σ v) :
    v = ∑ g : Fin d → σ,
      MvPolynomial.monomial (expOf d g) (v.coeff (expOf d g)) := by
  classical
  ext e
  rw [MvPolynomial.coeff_sum]
  by_cases hmem : e ∈ v.support
  · obtain ⟨g, rfl⟩ := exists_expOf_of_slotDeg_one (e := e) d
      (fun j => slotDeg_eq_one_of_isBlockMultilinear (F := F) (d := d) (σ := σ)
        (v := v) (m := e) hv (MvPolynomial.mem_support_iff.mp hmem) j)
    rw [Finset.sum_eq_single g]
    · rw [MvPolynomial.coeff_monomial, ite_eq_left rfl]
    · intro g' _ hg'
      rw [MvPolynomial.coeff_monomial, ite_eq_right]
      intro h
      exact hg' (expOf_injective d h)
    · intro h
      exact absurd (Finset.mem_univ g) h
  · rw [MvPolynomial.notMem_support_iff.mp hmem]
    refine (Finset.sum_eq_zero (fun g _ => ?_)).symm
    rw [MvPolynomial.coeff_monomial]
    by_cases h : expOf d g = e
    · rw [ite_eq_left h, h, MvPolynomial.notMem_support_iff.mp hmem]
    · rw [ite_eq_right h]

#print axioms isBlockMultilinear_expansion

/-- **标签截取**：把块 `j` 中标签 ≠ `g j` 的不定元置零（`RingHom` 形态）。 -/
noncomputable def killLabels (d : ℕ) (σ : Type) [DecidableEq σ] (g : Fin d → σ) :
    MvPolynomial (Fin d × σ) F →+* MvPolynomial (Fin d × σ) F :=
  MvPolynomial.eval₂Hom (algebraMap F (MvPolynomial (Fin d × σ) F))
    (fun x : Fin d × σ => if x.2 = g x.1 then MvPolynomial.X x else 0)

#print axioms killLabels

/-- `killLabels` 在不定元上的值。 -/
theorem killLabels_X (d : ℕ) (σ : Type) [DecidableEq σ] (g : Fin d → σ) (x : Fin d × σ) :
    killLabels F d σ g (MvPolynomial.X x)
      = if x.2 = g x.1 then MvPolynomial.X x else 0 := by
  simp [killLabels]

#print axioms killLabels_X

/-- `killLabels` 固定常数。 -/
theorem killLabels_C (d : ℕ) (σ : Type) [DecidableEq σ] (g : Fin d → σ) (a : F) :
    killLabels F d σ g (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [killLabels]

#print axioms killLabels_C

/-- `killLabels` 在不定元幂上的值。 -/
theorem killLabels_X_pow (d : ℕ) (σ : Type) [DecidableEq σ] (g : Fin d → σ)
    (x : Fin d × σ) (n : ℕ) :
    killLabels F d σ g (MvPolynomial.X x ^ n)
      = (if x.2 = g x.1 then MvPolynomial.X x else 0) ^ n := by
  rw [map_pow, killLabels_X]

#print axioms killLabels_X_pow

/-- `expOf` 的支撑上标签一致。 -/
theorem expOf_label_of_mem_support {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ)
    (g : Fin d → σ) {x : Fin d × σ} (hx : x ∈ (expOf d g).support) : x.2 = g x.1 := by
  have h := Finsupp.mem_support_iff.mp hx
  by_contra hc
  rw [expOf_apply, ite_eq_right hc] at h
  exact h rfl

#print axioms expOf_label_of_mem_support

/-- `killLabels` 固定 `expOf g` 的单项式。 -/
theorem killLabels_monomial_expOf_self (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ]
    (g : Fin d → σ) (a : F) :
    killLabels F d σ g (MvPolynomial.monomial (expOf d g) a)
      = MvPolynomial.monomial (expOf d g) a := by
  classical
  rw [killLabels, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq,
    MvPolynomial.C_eq_algebraMap]
  congr 1
  refine Finsupp.prod_congr (fun x hx => ?_)
  rw [ite_eq_left (expOf_label_of_mem_support d g hx)]

#print axioms killLabels_monomial_expOf_self

/-- `killLabels` 杀灭标签不一致的 `expOf` 单项式。 -/
theorem killLabels_monomial_expOf_ne (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ]
    {g g' : Fin d → σ} (h : g ≠ g') (a : F) :
    killLabels F d σ g (MvPolynomial.monomial (expOf d g') a) = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, g' j ≠ g j := by
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    exact h (funext (fun j => (hc j).symm))
  have hx : (j, g' j) ∈ (expOf d g').support := by
    rw [Finsupp.mem_support_iff, expOf_apply, ite_eq_left rfl]
    exact one_ne_zero
  rw [killLabels, MvPolynomial.eval₂Hom_monomial]
  refine mul_eq_zero.mpr (Or.inr ?_)
  rw [Finsupp.prod]
  refine Finset.prod_eq_zero hx ?_
  rw [ite_eq_right hj, zero_pow (Finsupp.mem_support_iff.mp hx)]

#print axioms killLabels_monomial_expOf_ne

/-- ★★★★★★ **标签分裂**：块多线性多项式 ＝ 各标签截取之和。 -/
theorem sum_killLabels (d : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ] [Infinite F]
    {v : MvPolynomial (Fin d × σ) F} (hv : IsBlockMultilinear F d σ v) :
    (∑ g : Fin d → σ, killLabels F d σ g v) = v := by
  classical
  rw [isBlockMultilinear_expansion (F := F) d σ hv]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g' _ => ?_)
  rw [Finset.sum_eq_single g']
  · rw [killLabels_monomial_expOf_self]
  · intro g _ hg
    exact killLabels_monomial_expOf_ne (F := F) (d := d) (σ := σ) (g := g) (g' := g') hg _
  · intro h
    exact absurd (Finset.mem_univ g') h

#print axioms sum_killLabels


/-! ## 切分第 42 步：★★★★★★ **块不变性的矩阵标签切片**（搬运段 3 的第 2 块；第 627 轮）

§41 的标签分裂按**精标签**（槽 `j` 里那一个不定元的完整坐标 `(k,i,l)`）切开，每个切片只是一个
单项式——**太细**（单个单项式不是不变量，无法喂给 Schur–Weyl）。搬运真正需要的是按
**矩阵标签** `k : Fin r` 切开：

```
v = Σ_{g : Fin d → Fin r} killLabelsK g v        （每片只用「每块一个矩阵」）
```

这样每个切片 `v_g` 只依赖 `d` 个矩阵（而非 `d·r` 个），于是 `mem_span_tSigmaVec_of_fixed`
（`m = d` 的 Schur–Weyl 件）**可以直接用**。本节把这条化归机检：

* **`killLabelsK`**：把块 `j` 里矩阵索引 ≠ `g j` 的不定元置零（`RingHom` 形态）；
* `killLabelsK_X/C`／`killLabelsK_monomial{,_ne}`：在不定元与单项式上的值；
* **`sum_killLabelsK`：块多线性 ⟹ `v = Σ_g killLabelsK g v`**（矩阵标签分裂）；
* `isBlockMultilinear_killLabelsK`／`killLabelsK_mem_multilinearSubmodule`：切片仍**块多线性**；
* **`killLabelsK_phiABlk`：`killLabelsK` 与 `φ_A` 的逐块提升交换**
  （⟹ 切片仍**块不变**：`killLabelsK_mem_blockInvariantSubmodule`）。

**为何交换性是真内容**：`phiABlk A` 把 `x^{(j)}_{k,i,l}` 送到 `φ_A` 的**同一个块、同一个矩阵标签**
（`phiGenBlk_eqC` 的显式双和：`x^{(j)}_{k,q,p}` 的和）——块索引与矩阵标签**都不变**，只有行列被混合。
故「杀掉标签 `k ≠ g j`」与「作用 `φ_A`」可交换；反之若 `φ_A` 会混合标签，整条搬运路线就不成立。

**射程（诚实边界）**：本节仍是**多项式层**。**未做**：切片在「压缩到 `d` 个矩阵」后的**张量层对偶运输**
（`MultilinearMap`／`TensorPower` 的构造与不变性转写）与 `tSigmaVec` 张成的应用；
`hAdBd` 正文、`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；
H2 仍不是定理。

**工艺（教训登记）**：① 目标里的 `if` 若出现在 `killLabelsK_X` 之后，其条件形态是
`(j, (k,q,p)).2.1 = g j`，须用 `by simpa using h` 桥接；② `conv_rhs => rw [← …]` 会把**两侧**的
`phiGenBlk` 一起折回（本轮一度因此报"simp made no progress"）⟹ **不要折回**，直接在已展开的
双和上算；③ `phiABlk A 0` 须用 `map_zero`（`simp` 收口），否则 `… * phiABlk A 0` 停住。 -/

/-- 全标签缩放的因式分解：按块分组。 -/
theorem slotFactor_eq_prod_slotDeg {σ : Type} [Fintype σ] (d : ℕ) (lam : Fin d → F)
    (e : Fin d × σ →₀ ℕ) :
    (∏ x, lam x.1 ^ e x) = ∏ j : Fin d, lam j ^ slotDeg d j e := by
  classical
  rw [← Finset.univ_product_univ, Finset.prod_product]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have h : (∏ y : σ, lam (j, y).1 ^ e (j, y)) = ∏ y : σ, lam j ^ e (j, y) := by simp
  rw [h, Finset.prod_pow_eq_pow_sum, slotDeg]

#print axioms slotFactor_eq_prod_slotDeg

/-- 块多线性对有限和封闭。 -/
theorem isBlockMultilinear_sum (d : ℕ) (σ : Type) {ι : Type*} (s : Finset ι)
    {f : ι → MvPolynomial (Fin d × σ) F}
    (hf : ∀ i ∈ s, IsBlockMultilinear F d σ (f i)) :
    IsBlockMultilinear F d σ (∑ i ∈ s, f i) := by
  classical
  intro lam
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi lam)

#print axioms isBlockMultilinear_sum

/-- `expOf` 的块次数恒为 1。 -/
theorem slotDeg_expOf {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) (f : Fin d → σ)
    (j : Fin d) : slotDeg (σ := σ) d j (expOf d f) = 1 := by
  classical
  rw [slotDeg]
  rw [Finset.sum_eq_single (f j)]
  · rw [expOf_apply, ite_eq_left rfl]
  · intro b _ hb
    rw [expOf_apply, ite_eq_right hb]
  · intro h
    exact absurd (Finset.mem_univ (f j)) h

#print axioms slotDeg_expOf

/-- 每块次数 1 的单项式是块多线性的。 -/
theorem isBlockMultilinear_monomial_of_slotDeg (d : ℕ) (σ : Type) [Fintype σ]
    {s : Fin d × σ →₀ ℕ} (hs : ∀ j, slotDeg (σ := σ) d j s = 1) (a : F) :
    IsBlockMultilinear F d σ (MvPolynomial.monomial s a) := by
  intro lam
  rw [blockScaleR_monomial, slotFactor_eq_prod_slotDeg]
  simp only [hs, pow_one]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, MvPolynomial.C_mul_monomial]
  congr 1
  ring

#print axioms isBlockMultilinear_monomial_of_slotDeg

/-- **按矩阵标签截取**：块 `j` 中矩阵索引 ≠ `g j` 的不定元置零。 -/
noncomputable def killLabelsK (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r) :
    MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F →+*
      MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
  MvPolynomial.eval₂Hom (algebraMap F (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F))
    (fun x : Fin d × (Fin r × Fin n × Fin n) =>
      if x.2.1 = g x.1 then MvPolynomial.X x else 0)

#print axioms killLabelsK

theorem killLabelsK_X (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (x : Fin d × (Fin r × Fin n × Fin n)) :
    killLabelsK F r n d g (MvPolynomial.X x)
      = if x.2.1 = g x.1 then MvPolynomial.X x else 0 := by
  simp [killLabelsK]

#print axioms killLabelsK_X

theorem killLabelsK_C (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r) (a : F) :
    killLabelsK F r n d g (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [killLabelsK]

#print axioms killLabelsK_C

/-- 支撑上矩阵标签全匹配 ⟹ `killLabelsK` 固定该单项式。 -/
theorem killLabelsK_monomial (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (s : Fin d × (Fin r × Fin n × Fin n) →₀ ℕ) (a : F)
    (h : ∀ x ∈ s.support, x.2.1 = g x.1) :
    killLabelsK F r n d g (MvPolynomial.monomial s a) = MvPolynomial.monomial s a := by
  classical
  rw [killLabelsK, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq,
    MvPolynomial.C_eq_algebraMap]
  congr 1
  refine Finsupp.prod_congr (fun x hx => ?_)
  rw [ite_eq_left (h x hx)]

#print axioms killLabelsK_monomial

/-- 支撑上有一个矩阵标签不匹配 ⟹ `killLabelsK` 杀灭该单项式。 -/
theorem killLabelsK_monomial_ne (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (s : Fin d × (Fin r × Fin n × Fin n) →₀ ℕ) (a : F)
    {x : Fin d × (Fin r × Fin n × Fin n)} (hx : x ∈ s.support) (hne : x.2.1 ≠ g x.1) :
    killLabelsK F r n d g (MvPolynomial.monomial s a) = 0 := by
  classical
  rw [killLabelsK, MvPolynomial.eval₂Hom_monomial]
  refine mul_eq_zero.mpr (Or.inr ?_)
  rw [Finsupp.prod]
  refine Finset.prod_eq_zero hx ?_
  rw [ite_eq_right hne, zero_pow (Finsupp.mem_support_iff.mp hx)]

#print axioms killLabelsK_monomial_ne

/-- ★★★★★★ **矩阵标签分裂**：块多线性多项式 ＝ 各「每块一个矩阵标签」切片之和。 -/
theorem sum_killLabelsK (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    {v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) v) :
    (∑ g : Fin d → Fin r, killLabelsK F r n d g v) = v := by
  classical
  rw [isBlockMultilinear_expansion (F := F) (d := d) (σ := Fin r × Fin n × Fin n) hv]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.sum_eq_single (fun j => (f j).1)]
  · refine killLabelsK_monomial F r n d (fun j => (f j).1) (expOf d f) _ (fun x hx => ?_)
    rw [expOf_label_of_mem_support d f hx]
  · intro g _ hg
    have hex : ∃ j, (f j).1 ≠ g j := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hg (funext fun j => (hc j).symm)
    obtain ⟨j, hj⟩ := hex
    refine killLabelsK_monomial_ne F r n d g (expOf d f) _ (x := (j, f j)) ?_ ?_
    · rw [Finsupp.mem_support_iff, expOf_apply, ite_eq_left rfl]
      exact one_ne_zero
    · simpa using hj
  · intro h
    exact absurd (Finset.mem_univ (fun j => (f j).1)) h

#print axioms sum_killLabelsK

/-- `killLabelsK` 保持块多线性。 -/
theorem isBlockMultilinear_killLabelsK (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    {v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) v) (g : Fin d → Fin r) :
    IsBlockMultilinear F d (Fin r × Fin n × Fin n) (killLabelsK F r n d g v) := by
  classical
  rw [isBlockMultilinear_expansion (F := F) (d := d) (σ := Fin r × Fin n × Fin n) hv,
    map_sum]
  refine isBlockMultilinear_sum F d _ Finset.univ (fun f _ => ?_)
  by_cases h : ∀ j, (f j).1 = g j
  · rw [killLabelsK_monomial F r n d g (expOf d f) _ (fun x hx => by
      rw [expOf_label_of_mem_support d f hx]; exact h x.1)]
    exact isBlockMultilinear_monomial_of_slotDeg F d _ (fun j => slotDeg_expOf d f j) _
  · have hex : ∃ j, (f j).1 ≠ g j := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact h hc
    obtain ⟨j, hj⟩ := hex
    rw [killLabelsK_monomial_ne F r n d g (expOf d f) _ (x := (j, f j)) ?_ ?_]
    · exact isBlockMultilinear_zero F d _
    · rw [Finsupp.mem_support_iff, expOf_apply, ite_eq_left rfl]
      exact one_ne_zero
    · simpa using hj

#print axioms isBlockMultilinear_killLabelsK

/-- `killLabelsK` 与 `phiGenBlk`：同标签保持，异标签归零。 -/
theorem killLabelsK_phiGenBlk (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (g : Fin d → Fin r)
    (v : Fin d × (Fin r × Fin n × Fin n)) :
    killLabelsK F r n d g (phiGenBlk F r n d A v)
      = if v.2.1 = g v.1 then phiGenBlk F r n d A v else 0 := by
  classical
  rw [phiGenBlk_eqC]
  by_cases hv : v.2.1 = g v.1
  · rw [ite_eq_left hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [map_mul, map_mul, killLabelsK_C, killLabelsK_C, killLabelsK_X,
      ite_eq_left (by simpa using hv)]
  · rw [ite_eq_right hv, map_sum]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [map_mul, map_mul, killLabelsK_C, killLabelsK_C, killLabelsK_X,
      ite_eq_right (by simpa using hv)]
    simp

#print axioms killLabelsK_phiGenBlk

/-- ★★★★★★ **`killLabelsK` 与 `phiABlk` 交换**（块不变性 ⟹ 固定标签切片仍块不变的根）。 -/
theorem killLabelsK_phiABlk (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (g : Fin d → Fin r)
    (w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :
    killLabelsK F r n d g (phiABlk F r n d A w)
      = phiABlk F r n d A (killLabelsK F r n d g w) := by
  classical
  induction w using MvPolynomial.induction_on with
  | C c => rw [phiABlk_C, killLabelsK_C, phiABlk_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
      calc killLabelsK F r n d g (phiABlk F r n d A (p * MvPolynomial.X v))
          = killLabelsK F r n d g
              (phiABlk F r n d A p * phiGenBlk F r n d A v) := by
            rw [map_mul, phiABlk_X]
        _ = killLabelsK F r n d g (phiABlk F r n d A p)
              * killLabelsK F r n d g (phiGenBlk F r n d A v) := by rw [map_mul]
        _ = phiABlk F r n d A (killLabelsK F r n d g p)
              * (if v.2.1 = g v.1 then phiGenBlk F r n d A v else 0) := by
            rw [hp, killLabelsK_phiGenBlk]
        _ = phiABlk F r n d A (killLabelsK F r n d g (p * MvPolynomial.X v)) := by
            by_cases h : v.2.1 = g v.1
            · rw [ite_eq_left h, map_mul, map_mul, killLabelsK_X,
                ite_eq_left (by simpa using h), phiABlk_X]
            · rw [ite_eq_right h, map_mul, map_mul, killLabelsK_X,
                ite_eq_right (by simpa using h)]
              simp

#print axioms killLabelsK_phiABlk

/-- 标签切片仍在**块不变量**里（交换性的直接推论）。 -/
theorem killLabelsK_mem_blockInvariantSubmodule (F : Type) [Field F] (r n d : ℕ)
    {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hw : w ∈ blockInvariantSubmodule F r n d) (g : Fin d → Fin r) :
    killLabelsK F r n d g w ∈ blockInvariantSubmodule F r n d := by
  intro A
  show phiABlk F r n d A (killLabelsK F r n d g w) = killLabelsK F r n d g w
  rw [← killLabelsK_phiABlk, hw A]

#print axioms killLabelsK_mem_blockInvariantSubmodule

/-- 标签切片仍在**多线性子模**里。 -/
theorem killLabelsK_mem_multilinearSubmodule (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    {v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n)) (g : Fin d → Fin r) :
    killLabelsK F r n d g v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n) :=
  isBlockMultilinear_killLabelsK F r n d hv g

#print axioms killLabelsK_mem_multilinearSubmodule


/-! ## 切分第 43 步：★★★★★★ **从块不变切片到多线性泛函**（搬运段 3 的第 3 块；第 628 轮）

§41／§42 把 `v` 分成 `Σ_g killLabelsK g v`，每个切片 `v_g` 只依赖 `d` 个矩阵。
本节把切片送进**多线性泛函**世界（`MultilinearMap F (Fin d → Mat) F`），这是接
`FFTIdentification` 的 `tnm_eq_span`（AGPR `lem:12.1.2` 的**形**级 Schur–Weyl：
`T_n(m) = span{T_σ}`，已在仓内）的唯一入口：

* **`matEntry`**：矩阵元泛函 `M ↦ M i l`；
* **`coordMon f`**：坐标单值多线性映射 `Y ↦ ∏_j (Y j)_{f j}`（`mkPiAlgebra ∘ compLinearMap`）；
* **`sliceForm v g`**：切片的系数泛函 `Σ_f (coeff of 单值单项式) • coordMon f`
  —— 它是**定义即多线性**的（不需要另证多线性！）；
* `sliceForm_apply`：取值律（把 `sliceForm` 展开成显式系数和）；
* `monomial_expOf`：`monomial (expOf h) a = C a * ∏_j X (j, h j)`（每块一个不定元）；
* `zeroFilled`／`unitFam`：带标签的**零填充族**与**矩阵单位族**（都按元素定义 ⟹ 取值律 `rfl`）；
* **`evalBlock_unitFam_expOf`：单位族上的单项式取值** —— 只有"匹配的那一项"存活，
  即 `evalBlock (unitFam g f) (monomial (expOf (g,h)) a) = if h = f then a else 0`。

**为何用 `coordMon` 而不是坐标式地"读出系数"**：`Σ_f c_f • coordMon f` 让 `sliceForm`
**生来就是 `MultilinearMap`**——省掉了"逐槽线性性"的证明（那正是 log 反复记录的 friction 点）；
而 `sliceForm_apply` 把它还原成显式系数和，供下一步与 `evalBlock` 对接。

**射程（诚实边界）**：本节只到**载体构造 ＋ 单位取值**。**未做**：主桥
`sliceForm v g Y = evalBlock (zeroFilled g Y) v`（＝把 §41 的系数展开与本节对接）、
`sliceForm` 的共轭不变性、`tnm` 成员性、以及由 `tnm_eq_span` 回推多项式层的
`hAdBd` 正文。`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；
`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `multilinearMap` 的 `smul_apply` 用的是**根** `smul_apply`
（`LinearMap.smul_apply` **不匹配** `MultilinearMap` 的 smul——本轮为此空转一次）；
② 多线性映射的有限和**不能**用 `Finset.sum_apply`（`MultilinearMap` 不是函数类型）⟹
对 `Finset` 归纳 ＋ `add_apply`；③ `Matrix` 在 `implicit` 透明级别下**不是**函数类型，
故 `simp only [...]` 在含 `Y j (f j).1 (f j).2` 的目标上会报 "not type-correct" ⟹ 改用
`rw` 链（`smul_apply`／`coordMon_apply`／`smul_eq_mul`）；④ 族按**元素**定义
（`Matrix.of`），取值律即 `rfl`——比先按矩阵定义再证取值律省一层。 -/

/-- 矩阵元泛函 `M ↦ M i l`（线性显然）。 -/
noncomputable def matEntry (F : Type) [Field F] (n : ℕ) (i l : Fin n) :
    Matrix (Fin n) (Fin n) F →ₗ[F] F where
  toFun M := M i l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

#print axioms matEntry

/-- 坐标单值多线性映射：`Y ↦ ∏ j, (Y j)_{f j}`。 -/
noncomputable def coordMon (F : Type) [Field F] (n d : ℕ) (f : Fin d → (Fin n × Fin n)) :
    MultilinearMap F (fun _ : Fin d => Matrix (Fin n) (Fin n) F) F :=
  (MultilinearMap.mkPiAlgebra F (ι := Fin d) F).compLinearMap
    (fun j => matEntry F n (f j).1 (f j).2)

#print axioms coordMon

theorem coordMon_apply (F : Type) [Field F] (n d : ℕ) (f : Fin d → (Fin n × Fin n))
    (Y : Fin d → Matrix (Fin n) (Fin n) F) :
    coordMon F n d f Y = ∏ j, Y j (f j).1 (f j).2 := by
  rw [coordMon, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

#print axioms coordMon_apply

/-- `expOf` 的单项式**乘积形态**（每块一个不定元）。 -/
theorem monomial_expOf (F : Type) [Field F] {σ : Type} [Fintype σ] [DecidableEq σ]
    (d : ℕ) (h : Fin d → σ) (a : F) :
    MvPolynomial.monomial (expOf d h) a
      = MvPolynomial.C a * ∏ j : Fin d, MvPolynomial.X (j, h j) := by
  classical
  have hlab : ∀ x ∈ (expOf d h).support, x = (x.1, h x.1) :=
    fun x hx => Prod.ext rfl (expOf_label_of_mem_support d h hx)
  rw [MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod]
  refine Finset.prod_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_univ x.1
  · intro x₁ hx₁ x₂ hx₂ hxx
    rw [hlab x₁ hx₁, hlab x₂ hx₂, hxx]
  · intro j _
    refine ⟨(j, h j), ?_, rfl⟩
    rw [Finsupp.mem_support_iff, expOf_apply, ite_eq_left rfl]
    exact one_ne_zero
  · intro x hx
    rw [hlab x hx]
    have : expOf d h (x.1, h x.1) = 1 := by
      rw [expOf_apply, ite_eq_left rfl]
    rw [this, pow_one]

#print axioms monomial_expOf

/-- **切片泛函**：`g`-标签切片的系数多线性型（`d` 个矩阵）。 -/
noncomputable def sliceForm (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    MultilinearMap F (fun _ : Fin d => Matrix (Fin n) (Fin n) F) F :=
  ∑ f : Fin d → (Fin n × Fin n),
    v.coeff (expOf d (fun j => (g j, f j))) • coordMon F n d f

#print axioms sliceForm

theorem sliceForm_apply (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) :
    sliceForm F r n d v g Y
      = ∑ f : Fin d → (Fin n × Fin n),
          v.coeff (expOf d (fun j => (g j, f j))) * ∏ j, Y j (f j).1 (f j).2 := by
  classical
  have key : ∀ s : Finset (Fin d → (Fin n × Fin n)),
      (∑ f ∈ s, v.coeff (expOf d (fun j => (g j, f j))) • coordMon F n d f) Y
        = ∑ f ∈ s,
            v.coeff (expOf d (fun j => (g j, f j))) * ∏ j, Y j (f j).1 (f j).2 := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih,
          smul_apply, coordMon_apply, smul_eq_mul]
  rw [sliceForm]
  exact key Finset.univ

#print axioms sliceForm_apply

/-- 带标签的零填充矩阵族：块 `j` 只在标签 `g j` 处置 `Y j`（按元素定义，便于取值）。 -/
noncomputable def zeroFilled (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) : Fin d × Fin r → Matrix (Fin n) (Fin n) F :=
  fun jk => Matrix.of (fun i l => if jk.2 = g jk.1 then Y jk.1 i l else 0)

#print axioms zeroFilled

theorem zeroFilled_apply (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) (jk : Fin d × Fin r) (i l : Fin n) :
    zeroFilled F r n d g Y jk i l = if jk.2 = g jk.1 then Y jk.1 i l else 0 := rfl

#print axioms zeroFilled_apply

/-- 带标签的**矩阵单位**族（切片的"单位取值"；按元素定义）。 -/
noncomputable def unitFam (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (f : Fin d → (Fin n × Fin n)) : Fin d × Fin r → Matrix (Fin n) (Fin n) F :=
  fun jk => Matrix.of (fun i l => if jk.2 = g jk.1 ∧ (i, l) = f jk.1 then (1 : F) else 0)

#print axioms unitFam

theorem unitFam_apply (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (f : Fin d → (Fin n × Fin n)) (jk : Fin d × Fin r) (i l : Fin n) :
    unitFam F r n d g f jk i l
      = if jk.2 = g jk.1 ∧ (i, l) = f jk.1 then (1 : F) else 0 := rfl

#print axioms unitFam_apply

/-- ★★★★★ **单位族上的单项式取值**：只有"匹配的每块一个不定元"这一项存活。 -/
theorem evalBlock_unitFam_expOf (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (f h : Fin d → (Fin n × Fin n)) (a : F) :
    evalBlock F r n d (unitFam F r n d g f)
        (MvPolynomial.monomial (expOf d (fun j => (g j, h j))) a)
      = if h = f then a else 0 := by
  classical
  rw [monomial_expOf, map_mul, map_prod]
  have hC : evalBlock F r n d (unitFam F r n d g f) (MvPolynomial.C a) = a := by
    simp [evalBlock]
  rw [hC]
  have hfac : ∀ j : Fin d,
      evalBlock F r n d (unitFam F r n d g f) (MvPolynomial.X (j, (g j, h j)))
        = if h j = f j then (1 : F) else 0 := by
    intro j
    rw [evalBlock, MvPolynomial.eval_X, unitFam_apply]
    by_cases hj : h j = f j
    · rw [ite_eq_left, ite_eq_left hj]
      exact ⟨rfl, by rw [hj]⟩
    · rw [ite_eq_right, ite_eq_right hj]
      intro hcon
      exact hj (by simpa using hcon.2)
  simp only [hfac]
  by_cases hf : h = f
  · rw [ite_eq_left hf, Finset.prod_congr rfl (fun j _ => ite_eq_left (by rw [hf]))]
    simp
  · rw [ite_eq_right hf]
    obtain ⟨j, hj⟩ : ∃ j, h j ≠ f j := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hf (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj), mul_zero]

#print axioms evalBlock_unitFam_expOf


/-! ## 切分第 44 步：★★★★★★ **主桥：切片泛函的取值 ＝ 零填充族上的取值**（第 629 轮）

§43 造出了 `sliceForm`（多线性泛函），但它的取值定义是"系数和"。本节把它与 `S` 层的
**取值语义**（§38 的 `evalBlock`）对接——这是"多项式层 → 泛函层"的唯一桥：

```
sliceForm v g Y = evalBlock (zeroFilled g Y) v        （v 块多线性）
```

**三段机制**：

* `evalBlock_zeroFilled_expOf`：在零填充族上，单项式 `monomial (expOf h) a` 的取值 ＝
  `(∏_j if (h j).1 = g j then (Y j)_{(h j).2} else 0) * a`（**标签不匹配的块给 0 因子**）；
* `sum_label_reindex`：对标签向量求和的**重指标**——只有"每块都匹配 `g`"的项存活，
  其余项因 0 因子而消失，故 `Σ_h (if 匹配 then Φ h) = Σ_f Φ (g 嵌入 f)`；
* **`sliceForm_eq_evalBlock_expansion`**：把 §41 的系数展开代入上面两条即得主桥。

**共轭不变性**（`sliceForm_eq_of_blockInvariant`）：块不变性（`hw : IsBlockInvariant`）经
§39 的 `evalBlock_phiABlk`（`evalBlock X (φ_A w) = evalBlock (conjFam A X) w`）
一条链即得泛函的共轭不变：
```
sliceForm w g (conjMat A ∘ Y) = evalBlock (zeroFilled g (conjMat A ∘ Y)) w
  = evalBlock (conjFam A (zeroFilled g Y)) w       （`conjFam_zeroFilled`）
  = evalBlock (zeroFilled g Y) (phiABlk A w)       （`← evalBlock_phiABlk`）
  = evalBlock (zeroFilled g Y) w = sliceForm w g Y  （`hw A`）
```
**为何先立 `conjMat`**：`conjFam` 的双和与 `A⁻¹ · M · A` 的 `Matrix.mul_apply` 展开只差一次
`Finset.sum_comm`（指标重排），本轮**不碰这个重排**——把 `conjFam` 与 `conjMat` 定义成**同一个双和**
（`conjFam_eq_conjMat` 是 `rfl`），于是 `conjFam_zeroFilled` 变成纯**标签**命题（两行）；
与 `A⁻¹ · M · A` 的桥留到真需要时（`tnm` 运输那一轮）单独做。

**射程（诚实边界）**：本节完成"多项式层 → 泛函层"的单向桥 ＋ 共轭不变性。**未做**：
把 `sliceForm` 沿 `LinearMap.toMatrix` 搬到 `End V` 上、`tnm` 成员性、由 `tnm_eq_span` 得到
`sliceForm = Σ c_σ tSigmaLinear σ`、以及**回推**到多项式层（`hAdBd` 正文的收口）。
`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `rw [expansion]` 会**连带改写 `v.coeff` 里的 `v`**（把系数变成求和！）
⟹ 必须用 `conv_rhs => rw [expansion]` 限定在 RHS；② `sum_label_reindex` 的目标形态要求
summand **带外层 `if`**，而 `evalBlock_zeroFilled_expOf` 给的是"乘积形态" ⟹ 需先用
`hstep`（`Ψ h = if 匹配 then Ψ h else 0`，由「不匹配 ⟹ 某因子为 0」证）转形；
③ `Matrix` 的 `i l` 取值在 `simp only` 下可能不展开（`implicit` 透明级别）⟹ 用 `simp only [conjFam, conjMat, zeroFilled_apply]` 显式展开；
④ 乘积的 `ite` 在 0 因子情形要同时给 `mul_zero` 与 `zero_mul`（外层 `∑, ∑` 再要 `Finset.sum_const_zero`）。 -/

/-- 单位族上的单项式取值（按块标签的比较形态）。 -/
theorem evalBlock_zeroFilled_expOf (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) (h : Fin d → (Fin r × Fin n × Fin n)) (a : F) :
    evalBlock F r n d (zeroFilled F r n d g Y)
        (MvPolynomial.monomial (expOf d h) a)
      = (∏ j, if (h j).1 = g j then Y j (h j).2.1 (h j).2.2 else 0) * a := by
  classical
  rw [monomial_expOf, map_mul]
  have hC : evalBlock F r n d (zeroFilled F r n d g Y) (MvPolynomial.C a) = a := by
    simp [evalBlock]
  have hP : evalBlock F r n d (zeroFilled F r n d g Y)
      (∏ j : Fin d, MvPolynomial.X (j, h j))
      = ∏ j, if (h j).1 = g j then Y j (h j).2.1 (h j).2.2 else 0 := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [evalBlock, MvPolynomial.eval_X, zeroFilled_apply]
  rw [hC, hP, mul_comm]

#print axioms evalBlock_zeroFilled_expOf

/-- **标签重指标**：对标签向量求和，只剩"每块都匹配 `g`"的项。 -/
theorem sum_label_reindex (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (Φ : (Fin d → (Fin r × Fin n × Fin n)) → F) :
    (∑ h : Fin d → (Fin r × Fin n × Fin n),
        (if (∀ j, (h j).1 = g j) then Φ h else 0))
      = ∑ f : Fin d → (Fin n × Fin n), Φ (fun j => (g j, f j)) := by
  classical
  rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin d → (Fin r × Fin n × Fin n))))
    (p := fun h => ∀ j, (h j).1 = g j) (f := Φ)]
  refine Finset.sum_bij (fun h _ => fun j => (h j).2) ?_ ?_ ?_ ?_
  · intro h _
    exact Finset.mem_univ _
  · intro h₁ hh₁ h₂ hh₂ heq
    rw [Finset.mem_filter] at hh₁ hh₂
    funext j
    exact Prod.ext ((hh₁.2 j).trans (hh₂.2 j).symm) (congrFun heq j)
  · intro f _
    exact ⟨fun j => (g j, f j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => rfl⟩, rfl⟩
  · intro h hh
    rw [Finset.mem_filter] at hh
    congr 1
    funext j
    exact Prod.ext (hh.2 j) rfl

#print axioms sum_label_reindex

/-- 主桥：切片泛函的取值 ＝ 零填充族上的取值（`sliceForm` 的 `evalBlock` 语义）。 -/
theorem sliceForm_eq_evalBlock_expansion (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) (Y : Fin d → Matrix (Fin n) (Fin n) F)
    {v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) v) :
    sliceForm F r n d v g Y = evalBlock F r n d (zeroFilled F r n d g Y) v := by
  classical
  rw [sliceForm_apply]
  conv_rhs => rw [isBlockMultilinear_expansion (F := F) (d := d)
    (σ := Fin r × Fin n × Fin n) hv]
  rw [map_sum]
  simp only [evalBlock_zeroFilled_expOf]
  have hstep : ∀ h : Fin d → (Fin r × Fin n × Fin n),
      (∏ j, if (h j).1 = g j then Y j (h j).2.1 (h j).2.2 else 0) * v.coeff (expOf d h)
        = if (∀ j, (h j).1 = g j) then
            (∏ j, if (h j).1 = g j then Y j (h j).2.1 (h j).2.2 else 0)
              * v.coeff (expOf d h)
          else 0 := by
    intro h
    by_cases hp : ∀ j, (h j).1 = g j
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp]
      obtain ⟨j0, hj0⟩ : ∃ j, (h j).1 ≠ g j := by
        by_contra hc
        simp only [not_exists, ne_eq, not_not] at hc
        exact hp hc
      rw [Finset.prod_eq_zero (Finset.mem_univ j0) (ite_eq_right hj0), zero_mul]
  rw [Finset.sum_congr rfl (fun h _ => hstep h),
    sum_label_reindex (F := F) (r := r) (n := n) (d := d) (g := g)
      (Φ := fun h => (∏ j, if (h j).1 = g j then Y j (h j).2.1 (h j).2.2 else 0)
        * v.coeff (expOf d h))]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp [mul_comm]

#print axioms sliceForm_eq_evalBlock_expansion

/-- 矩阵层的共轭（与 `conjFam` 同一个双和）。 -/
noncomputable def conjMat (F : Type) [Field F] (n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i l => ∑ p : Fin n, ∑ q : Fin n,
    (↑A⁻¹ : Matrix (Fin n) (Fin n) F) i q * M q p * (↑A : Matrix (Fin n) (Fin n) F) p l

#print axioms conjMat

theorem conjFam_eq_conjMat (F : Type) [Field F] (r n d : ℕ)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (X : Fin d × Fin r → Matrix (Fin n) (Fin n) F) :
    conjFam F r n d A X = fun jk => conjMat F n A (X jk) := rfl

#print axioms conjFam_eq_conjMat

/-- 共轭与零填充相容：`conjFam A (zeroFilled g Y) = zeroFilled g (conjMat A ∘ Y)`。 -/
theorem conjFam_zeroFilled (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (Y : Fin d → Matrix (Fin n) (Fin n) F) :
    conjFam F r n d A (zeroFilled F r n d g Y)
      = zeroFilled F r n d g (fun j => conjMat F n A (Y j)) := by
  classical
  funext jk i l
  simp only [conjFam, conjMat, zeroFilled_apply]
  by_cases hk : jk.2 = g jk.1
  · simp only [hk, ite_true]
  · simp only [hk, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]

#print axioms conjFam_zeroFilled

/-- ★★★★★ **切片泛函的共轭不变性**（块不变量 ⟹ 泛函在同时共轭下不变）。 -/
theorem sliceForm_eq_of_blockInvariant (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) w)
    (hw : IsBlockInvariant F r n d w) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) :
    sliceForm F r n d w g (fun j => conjMat F n A (Y j)) = sliceForm F r n d w g Y := by
  classical
  rw [sliceForm_eq_evalBlock_expansion (F := F) (r := r) (n := n) (d := d) (g := g)
      (Y := fun j => conjMat F n A (Y j)) (v := w) hv,
    sliceForm_eq_evalBlock_expansion (F := F) (r := r) (n := n) (d := d) (g := g)
      (Y := Y) (v := w) hv,
    ← conjFam_zeroFilled, ← evalBlock_phiABlk, hw A]

#print axioms sliceForm_eq_of_blockInvariant


/-! ## 切分第 47 步：★★★★★ **单位族上的取值 ＝ 系数**（回推的读数层；第 632 轮）

§43 已给「带标签的矩阵单位族」`unitFam`，但在**每块一个标签**的形态下
（`expOf d (fun j => (g j, h j))`）。回推需要**任意** `h : Fin d → (Fin r × Fin n × Fin n)`
的形态，并把它接成一条等式：

```
evalBlock (unitFam g f) p = p.coeff (expOf d (fun j => (g j, f j)))      （p 块多线性）
```

**为何这是回推的核心读数**：`sliceForm p g` 与 `p` 的系数在「单位族」与「系数」之间
**互为逆**——这正是把泛函层等式 `Σ_σ c_σ • T_σ = sliceForm w g` 翻成**多项式层**等式
（`w = Σ_σ c_σ • P_σ`）所需的**忠实性**（下一节）。

本节的件：

* `unitMat`：单个矩阵元 `E_p`（按元素定义）；
* `unitFam_eq_zeroFilled`：`unitFam g f = zeroFilled g (unitMat ∘ f)`（把两族对齐）；
* `sliceForm_add`：`sliceForm` 对**多项式变量线性**；
* **`evalBlock_unitFam_expOf'`**：任意 `h` 的**单位族取值**（只有"完全匹配"的那项存活）；
* **`evalBlock_unitFam_eq_coeff`**：单位族取值 ＝ **系数**（用 §41 展开 ＋ 上一条）。

**射程（诚实边界）**：本节只给**读数层**。**未做**：切片泛函的**忠实性**
（`sliceForm p g = sliceForm q g ⟹ p = q`，需"label-g ⟹ 只含 label-g 单项式"的系数论证）、
`vs(σ,g)` 字表构造、`hAdBd` 正文。`invariantAlg = traceAlgS`、β1、β2 **未证**；
`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `evalBlock_unitFam_expOf`（§43）的**标签形态是特化的**
（`fun j => (g j, h j)`），与 §41 展开给出的**一般** `expOf d h` 不匹配 ⟹ 必须补
`evalBlock_unitFam_expOf'`（本轮为此一度 `simp made no progress`）；
② 乘积 `∏_j (if 匹配 then 1 else 0)` 在 0 因子情形是 `mul_zero`（`a * 0`）而非 `zero_mul`。 -/

/-- 单元素矩阵（单位矩阵元）。 -/
noncomputable def unitMat (F : Type) [Field F] (n : ℕ) (p : Fin n × Fin n) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun i l => if (i, l) = p then (1 : F) else 0)

#print axioms unitMat

theorem unitFam_eq_zeroFilled (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (f : Fin d → (Fin n × Fin n)) :
    unitFam F r n d g f = zeroFilled F r n d g (fun j => unitMat F n (f j)) := by
  funext jk i l
  simp only [unitFam_apply, zeroFilled_apply, unitMat, Matrix.of_apply]
  by_cases hk : jk.2 = g jk.1 <;> simp [hk]

#print axioms unitFam_eq_zeroFilled

/-- `sliceForm` 对多项式变量**线性**（加法）。 -/
theorem sliceForm_add (F : Type) [Field F] (r n d : ℕ)
    (p q : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    sliceForm F r n d (p + q) g = sliceForm F r n d p g + sliceForm F r n d q g := by
  classical
  ext Y
  simp only [sliceForm_apply, add_apply, MvPolynomial.coeff_add, add_mul,
    Finset.sum_add_distrib]

#print axioms sliceForm_add

theorem evalBlock_unitFam_expOf' (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (f : Fin d → (Fin n × Fin n)) (h : Fin d → (Fin r × Fin n × Fin n)) (a : F) :
    evalBlock F r n d (unitFam F r n d g f) (MvPolynomial.monomial (expOf d h) a)
      = if h = (fun j => (g j, f j)) then a else 0 := by
  classical
  rw [monomial_expOf, map_mul]
  have hC : evalBlock F r n d (unitFam F r n d g f) (MvPolynomial.C a) = a := by
    simp [evalBlock]
  have hP : evalBlock F r n d (unitFam F r n d g f) (∏ j : Fin d, MvPolynomial.X (j, h j))
      = ∏ j, if h j = (g j, f j) then (1 : F) else 0 := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [evalBlock, MvPolynomial.eval_X, unitFam_apply]
    by_cases hj : h j = (g j, f j)
    · rw [ite_eq_left, ite_eq_left hj]
      rw [hj]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right, ite_eq_right hj]
      intro hcon
      exact hj (Prod.ext hcon.1 hcon.2)
  rw [hC, hP]
  by_cases hf : h = (fun j => (g j, f j))
  · rw [ite_eq_left hf, Finset.prod_congr rfl (fun j _ => ite_eq_left (by rw [hf]))]
    simp
  · rw [ite_eq_right hf]
    obtain ⟨j, hj⟩ : ∃ j, h j ≠ (g j, f j) := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hf (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj), mul_zero]

#print axioms evalBlock_unitFam_expOf'

/-- ★★★★★ **单位族上的取值 ＝ 系数**（块多线性多项式）。 -/
theorem evalBlock_unitFam_eq_coeff (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    {p : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hp : IsBlockMultilinear F d (Fin r × Fin n × Fin n) p) (g : Fin d → Fin r)
    (f : Fin d → (Fin n × Fin n)) :
    evalBlock F r n d (unitFam F r n d g f) p
      = p.coeff (expOf d (fun j => (g j, f j))) := by
  classical
  conv_lhs => rw [isBlockMultilinear_expansion (F := F) (d := d)
    (σ := Fin r × Fin n × Fin n) hp]
  rw [map_sum]
  simp only [evalBlock_unitFam_expOf']
  rw [Finset.sum_eq_single (fun j => (g j, f j))]
  · rw [ite_eq_left rfl]
  · intro h _ hh
    rw [ite_eq_right]
    intro hc
    exact hh hc
  · intro h
    exact absurd (Finset.mem_univ _) h

#print axioms evalBlock_unitFam_eq_coeff


/-! ## 切分第 48 步：★★★★★★ **切片泛函的忠实性**（回推的最后一块"形式"件；第 633 轮）

要把泛函层等式 `Σ_σ c_σ • T_σ = sliceForm w g` 翻成**多项式层**等式，除读数（§47）外还需
**忠实性**：

```
p, q 块多线性 ＋ label-g（killLabelsK g p = p），sliceForm p g = sliceForm q g  ⟹  p = q
```

本节的链条（三步）：

* **`killLabelsK_monomial_expOf`**：`killLabelsK` 在展开单项式上"按标签向量分情形"
  （匹配 ⟹ 保持，不匹配 ⟹ 杀灭）；
* **`coeff_eq_zero_of_not_label`**：`p` 块多线性且 label-g ⟹ 一切**非** label-g 的
  `expOf`-系数的 **0**（对 §41 展开施 `killLabelsK`，再用上一条 ＋ 过滤求和比较系数）；
* **`sliceForm_eq_zero_of_label_g`**：label-g ＋ 块多线性 ＋ 切片为零 ⟹ `p = 0`
  （label-g 的系数由 §47 的单位族读数 ＋ §44 的主桥给出，非 label-g 的系数由上一件给出）；
* **`sliceForm_faithful`**：把零判定施于 `p - q`（`sliceForm_sub` 给线性）。

**为何这是最后一块"形式"件**：忠实性一旦成立，只需对每个 `σ` 造一个 **label-g 多项式
`P_σ`** 使 `sliceForm P_σ g = T_σ`，则 `w = Σ_σ c_σ • P_σ` 立得。
`P_σ` 的正表示就是 **`σ` 的循环分解对应的字表 `tSigmaPoly (vs(σ,g))`**——其"系数 ＝ 迹字"
正是 AGPR `eq:12.3` 在多项式层的对应物（下一阶段）。

**射程（诚实边界）**：本节只给**忠实性**。**未做**：`vs(σ,g)` 字表构造、
`sliceForm (tSigmaPoly vs(σ,g)) g = T_σ`、`hAdBd` 正文。
`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `(if 匹配 then monomial else 0).coeff m` **不能**直接 `simp only
[coeff_monomial]`（`coeff` 吃的是 `ite` 的整体，`ite_apply` 也只对函数形态有效）⟹
改走"**过滤求和**"：`rw [← Finset.sum_filter]` 把 `Σ if` 变成 `Σ over filter`，
再 `coeff_sum` ＋ 逐项 `coeff_monomial`（本轮为此空转两次）；
② label-g 的系数读数要先把 `h` 写成 `fun j => (g j, (h j).2)`（`Prod.ext (hl j) rfl`），
才能与 §47 的 `expOf (fun j => (g j, f j))` 形态对接。 -/

/-- `killLabelsK` 在展开单项式上的值（按标签向量分情形）。 -/
theorem killLabelsK_monomial_expOf (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (h : Fin d → (Fin r × Fin n × Fin n)) (a : F) :
    killLabelsK F r n d g (MvPolynomial.monomial (expOf d h) a)
      = if (∀ j, (h j).1 = g j) then MvPolynomial.monomial (expOf d h) a else 0 := by
  classical
  have hsupp : ∀ x ∈ (expOf d h).support, x = (x.1, h x.1) :=
    fun x hx => Prod.ext rfl (expOf_label_of_mem_support d h hx)
  by_cases hh : ∀ j, (h j).1 = g j
  · rw [ite_eq_left hh]
    refine killLabelsK_monomial F r n d g (expOf d h) a (fun x hx => ?_)
    rw [hsupp x hx]
    exact hh x.1
  · rw [ite_eq_right hh]
    obtain ⟨j, hj⟩ : ∃ j, (h j).1 ≠ g j := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hh hc
    refine killLabelsK_monomial_ne F r n d g (expOf d h) a (x := (j, h j)) ?_ ?_
    · rw [Finsupp.mem_support_iff, expOf_apply, ite_eq_left rfl]
      exact one_ne_zero
    · simpa using hj

#print axioms killLabelsK_monomial_expOf

/-- ★★★★★ **label-g 的多项式只含 label-g 单项式**（系数形态）。 -/
theorem coeff_eq_zero_of_not_label (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) {p : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hp : IsBlockMultilinear F d (Fin r × Fin n × Fin n) p)
    (hgp : killLabelsK F r n d g p = p)
    {h : Fin d → (Fin r × Fin n × Fin n)} (hh : ¬ ∀ j, (h j).1 = g j) :
    p.coeff (expOf d h) = 0 := by
  classical
  have hexp := isBlockMultilinear_expansion (F := F) (d := d)
    (σ := Fin r × Fin n × Fin n) hp
  have h1 : killLabelsK F r n d g p
      = ∑ h' : Fin d → (Fin r × Fin n × Fin n),
          killLabelsK F r n d g
            (MvPolynomial.monomial (expOf d h') (p.coeff (expOf d h'))) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
  rw [hgp] at h1
  simp only [killLabelsK_monomial_expOf] at h1
  rw [← Finset.sum_filter] at h1
  have h2 := congrArg (fun q : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F =>
    q.coeff (expOf d h)) h1
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_zero] at h2
  · exact h2
  · intro h' hh'
    rw [Finset.mem_filter] at hh'
    rw [MvPolynomial.coeff_monomial, ite_eq_right]
    intro he
    exact hh (expOf_injective d he ▸ hh'.2)

#print axioms coeff_eq_zero_of_not_label
#print axioms coeff_eq_zero_of_not_label
#print axioms coeff_eq_zero_of_not_label

/-- `sliceForm` 对多项式变量**线性**（减法）。 -/
theorem sliceForm_sub (F : Type) [Field F] (r n d : ℕ)
    (p q : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    sliceForm F r n d (p - q) g = sliceForm F r n d p g - sliceForm F r n d q g := by
  classical
  ext Y
  simp only [sliceForm_apply, sub_apply, MvPolynomial.coeff_sub, sub_mul,
    Finset.sum_sub_distrib]

#print axioms sliceForm_sub

/-- ★★★★★ **切片泛函的忠实性（零判定）**：label-g 且块多线性、切片为零 ⟹ 多项式为零。 -/
theorem sliceForm_eq_zero_of_label_g (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) {p : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hp : IsBlockMultilinear F d (Fin r × Fin n × Fin n) p)
    (hgp : killLabelsK F r n d g p = p)
    (h0 : sliceForm F r n d p g = 0) : p = 0 := by
  classical
  have hcoeff : ∀ h : Fin d → (Fin r × Fin n × Fin n), p.coeff (expOf d h) = 0 := by
    intro h
    by_cases hl : ∀ j, (h j).1 = g j
    · have heq : h = fun j => (g j, (h j).2) := by
        funext j
        exact Prod.ext (hl j) rfl
      have h1 : evalBlock F r n d (unitFam F r n d g (fun j => (h j).2)) p
          = p.coeff (expOf d h) := by
        rw [evalBlock_unitFam_eq_coeff F r n d hp g (fun j => (h j).2), heq]
      rw [← h1, unitFam_eq_zeroFilled, ← sliceForm_eq_evalBlock_expansion
        (F := F) (r := r) (n := n) (d := d) (g := g)
        (Y := fun j => unitMat F n ((fun j => (h j).2) j)) (v := p) hp, h0]
      rfl
    · exact coeff_eq_zero_of_not_label F r n d g hp hgp hl
  conv_lhs => rw [isBlockMultilinear_expansion (F := F) (d := d)
    (σ := Fin r × Fin n × Fin n) hp]
  rw [Finset.sum_eq_zero]
  intro h _
  rw [hcoeff h, MvPolynomial.monomial_zero]

#print axioms sliceForm_eq_zero_of_label_g

/-- ★★★★★★ **切片泛函忠实**：label-g ＋ 块多线性的多项式由切片泛函唯一决定。 -/
theorem sliceForm_faithful (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) {p q : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hp : IsBlockMultilinear F d (Fin r × Fin n × Fin n) p)
    (hq : IsBlockMultilinear F d (Fin r × Fin n × Fin n) q)
    (hgp : killLabelsK F r n d g p = p) (hgq : killLabelsK F r n d g q = q)
    (h : sliceForm F r n d p g = sliceForm F r n d q g) : p = q := by
  classical
  have hsub_eq : p - q = p + (-1 : F) • q := by
    rw [neg_one_smul, sub_eq_add_neg]
  have hsub_bm : IsBlockMultilinear F d (Fin r × Fin n × Fin n) (p - q) := by
    rw [hsub_eq]
    exact isBlockMultilinear_add F d _ hp (isBlockMultilinear_smul F d _ (-1) hq)
  have hsub_label : killLabelsK F r n d g (p - q) = p - q := by
    rw [map_sub, hgp, hgq]
  have hsub_zero : sliceForm F r n d (p - q) g = 0 := by
    rw [sliceForm_sub, h, sub_self]
  exact sub_eq_zero.mp (sliceForm_eq_zero_of_label_g F r n d g hsub_bm hsub_label hsub_zero)

#print axioms sliceForm_faithful


/-! ## 切分第 49 步：★★★★ **块字迹的伸缩律**（`tSigmaPoly` 的块多线性基础；第 634 轮）

`vs(σ,g)` 字表字典要把 `tSigmaPoly (vs(σ,g))` 喂进 §48 的**忠实性**，前提是它**块多线性**
（＋ label-g）。而 `tSigmaPoly vs = ∏_w tr(∏_{p∈w} blkMatrix p)` 的块多线性来自
「**每槽恰出现一次**」的伸缩律——本节给它的第一步：

```
blockScaleR λ (blkMatrix j k)   = λ_j • blkMatrix j k
blockScaleR λ (tr(∏ over w))    = (∏_{p∈w} λ_{p.1}) • tr(∏ over w)
```

**机制**：`blockScaleR` 是 `RingHom`，逐元素作用到矩阵上 ⟹ 用 `Matrix.map`；
`(M * N).map f = M.map f * N.map f`（`Matrix.map_mul`）＋ 迹对**标量**线性（`trace (c • M) = c • trace M`，
本文件内证，避免依赖 `Matrix.trace_map` 的 import）。

**射程（诚实边界）**：本节只给**单字**伸缩律。**未做**：把 `vs` 的伸缩因子收成 `∏_j λ_j`
（即 `tSigmaPoly` 的块多线性判据）、`vs(σ,g)` 字表构造、`hAdBd` 正文。
`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `Matrix.trace_map`／`Matrix.trace_smul` **不在** `FFTRing` 的 import 闭包内
（`unknownIdentifier`）⟹ 在文件内自证（`Matrix.trace` 展开成 `∑ i, M.diag i` ＋ `map_sum`）；
② `c • x`（`MvPolynomial` 的标量作用）**不是** `c * x` 的语法形态，`smul_eq_mul` 不匹配 ⟹
用 `MvPolynomial.smul_eq_C_mul` 转成 `C c * x`，再 `Finset.mul_sum`；
③ 归纳里 `List.map_cons`／`List.prod_cons` 会在**两侧**都要用一次（`rw` 只打第一处）。 -/

/-- 块矩阵在块缩放下：`x^{(j)}_{k,i,l} ↦ λ_j x^{(j)}_{k,i,l}`。 -/
theorem blkMatrix_map_blockScaleR (F : Type) [Field F] (r n d : ℕ) (lam : Fin d → F)
    (j : Fin d) (k : Fin r) :
    (blkMatrix F r n d j k).map (blockScaleR F d (Fin r × Fin n × Fin n) lam)
      = lam j • blkMatrix F r n d j k := by
  ext i l
  simp [blkMatrix, blockScaleR_X, MvPolynomial.smul_eq_C_mul]

#print axioms blkMatrix_map_blockScaleR

/-- 块字迹在块缩放下的伸缩律。 -/
theorem blockTraceWord_scale (F : Type) [Field F] (r n d : ℕ) (lam : Fin d → F)
    (v : List (Fin d × Fin r)) :
    blockScaleR F d (Fin r × Fin n × Fin n) lam (blockTraceWord F r n d v)
      = (v.map (fun p => lam p.1)).prod • blockTraceWord F r n d v := by
  classical
  have htrace : ∀ M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F),
      blockScaleR F d (Fin r × Fin n × Fin n) lam M.trace
        = (M.map (blockScaleR F d (Fin r × Fin n × Fin n) lam)).trace := by
    intro M
    simp [Matrix.trace, Matrix.map_apply]
  have hsmul : ∀ (c : F) (M : Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)),
      (c • M).trace = c • M.trace := by
    intro c M
    show (∑ i, (c • M).diag i) = c • ∑ i, M.diag i
    rw [MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      simp [Matrix.diag, Matrix.smul_apply, MvPolynomial.smul_eq_C_mul])
  rw [blockTraceWord, htrace, ← hsmul]
  congr 1
  induction v with
  | nil => simp
  | cons p v ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, blkMatrix_map_blockScaleR, ih,
      smul_mul_assoc, mul_smul_comm, smul_smul, List.map_cons, List.prod_cons]

#print axioms blockTraceWord_scale


/-! ## 切分第 50 步：★★★★★ **`T_σ` 单项的伸缩律**（`tSigmaPoly` 块多线性的最后一步；第 635 轮）

§49 给了**单字迹**的伸缩律；本节把它收成 **`tSigmaPoly`（字表之表）** 的：

```
blockScaleR λ (tSigmaPoly vs) = (∏_w ∏_{p∈w} λ_{p.1}) • tSigmaPoly vs
```

**用途**：`vs(σ,g)` 字表（`σ` 的循环分解）的槽恰覆盖一次，故上式右端的标量
`∏_w ∏_{p∈w} λ_{p.1}` 可化成 `∏_j λ_j`——**这正是 `tSigmaPoly (vs(σ,g))` 块多线性的判据**。

**机制**：`tSigmaPoly = (vs.map blockTraceWord).prod`；`map_list_prod` 把 `blockScaleR` 推进到
每个字，再用 §49 的 `blockTraceWord_scale` 逐字伸缩，最后用**标量收集引理**
`prod_smul_prod : ∏ (c w • t w) = (∏ c w) • ∏ t w`（交换环里 `smul = C·`，
故 `C c * a * (C d * b) = C (c*d) * (a*b)`，`ring` 收口）。

**射程（诚实边界）**：本节只给**伸缩律**。**未做**：把标量化成 `∏_j λ_j`（需"槽覆盖一次"的
列表置换假设）、label-g 判据、`vs(σ,g)` 字表构造、字表主恒等式、`hAdBd` 正文。
`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `prod_smul_prod` 不用 `ring` 收口会在 `C c * (a * (C d * b))` 与
`C c * C d * (a * b)` 之间卡住（`mul_assoc` 方向不够）——**交换环上的标量收集交给 `ring`**；
② `map_list_prod` 之后要 `List.map_map` 摊开 `f ∘ g` 形态，再接 `List.map_congr_left`；
③ **本文件的 section 变量（F, r, n, d, σ）与新声明里的同名显式 binder 会撞**（调用处报
"Field F✝ 无法合成" 或实参错位）⟹ 新件一律写**全显式 binder**（与 §41–§43、§47–§49 一致）。 -/

/-- 标量收集：`∏ (c w • t w) = (∏ c w) • ∏ t w`。 -/
theorem prod_smul_prod (F : Type) [Field F] (r n : ℕ) (d : ℕ) {ι : Type*} (s : List ι)
    (c : ι → F) (t : ι → MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :
    (s.map (fun w => c w • t w)).prod = (s.map c).prod • (s.map t).prod := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, ih, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul]
    ring

#print axioms prod_smul_prod

/-- ★★★★★ **`T_σ` 单项的伸缩律**：按各字的槽标签逐字收集。 -/
theorem tSigmaPoly_scale (F : Type) [Field F] (r n d : ℕ) (lam : Fin d → F)
    (vs : List (List (Fin d × Fin r))) :
    blockScaleR F d (Fin r × Fin n × Fin n) lam (tSigmaPoly F r n d vs)
      = (vs.map (fun w => (w.map (fun p => lam p.1)).prod)).prod • tSigmaPoly F r n d vs := by
  classical
  rw [tSigmaPoly, map_list_prod, List.map_map]
  rw [show List.map ((blockScaleR F d (Fin r × Fin n × Fin n) lam) ∘ blockTraceWord F r n d) vs
      = List.map (fun w => (w.map (fun p => lam p.1)).prod • blockTraceWord F r n d w) vs from
    List.map_congr_left (fun w _ => blockTraceWord_scale F r n d lam w)]
  rw [prod_smul_prod F r n d vs]

#print axioms tSigmaPoly_scale


/-! ## 切分第 51 步：★★★★★ **`tSigmaPoly` 的块多线性判据 ＋ 子代数成员**（第 636 轮）

§50 的伸缩律 `blockScaleR λ (tSigmaPoly vs) = (∏_w ∏_{p∈w} λ_{p.1}) • tSigmaPoly vs`
一旦把标量识别成全积 `∏_j λ_j`（**槽恰覆盖一次**的字表，正是 `vs(σ,g)` 的循环分解），
就得到块多线性：

```
isBlockMultilinear_tSigmaPoly : (∀ λ, ∏_w ∏_{p∈w} λ_{p.1} = ∏_j λ_j) ⟹ IsBlockMultilinear (tSigmaPoly vs)
```

并记下最终装配要用的成员性：`tSigmaPoly vs ∈ adjoin (range tSigmaPoly)`。

**射程（诚实边界）**：本节只给**判据**（把"槽覆盖一次"作为显式假设）＋ 成员性。
**未做**：从 `vs` 的组合结构（列表置换）**推出**该假设、label-g 判据、`vs(σ,g)` 字表构造、
字表主恒等式、`hAdBd` 正文。`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★ **`tSigmaPoly` 的块多线性判据**：若伸缩因子恒为 `∏_j λ_j`（槽恰覆盖一次），则块多线性。 -/
theorem isBlockMultilinear_tSigmaPoly (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r)))
    (h : ∀ lam : Fin d → F,
      (vs.map (fun w => (w.map (fun p => lam p.1)).prod)).prod = ∏ j, lam j) :
    IsBlockMultilinear F d (Fin r × Fin n × Fin n) (tSigmaPoly F r n d vs) := by
  intro lam
  rw [tSigmaPoly_scale, h lam]

#print axioms isBlockMultilinear_tSigmaPoly

/-- `T_σ` 单项落在 `T_σ` 生成的子代数里。 -/
theorem tSigmaPoly_mem_adjoin (F : Type) [Field F] (r n d : ℕ)
    (vs : List (List (Fin d × Fin r))) :
    tSigmaPoly F r n d vs ∈ Algebra.adjoin F (Set.range (tSigmaPoly F r n d)) :=
  Algebra.subset_adjoin ⟨vs, rfl⟩

#print axioms tSigmaPoly_mem_adjoin


/-! ## 切分第 52 步：★★★ **字表伸缩律的基例**（第 637 轮）

字表字典的归纳（把 `tSigmaPoly` 的块多线性/伸缩律按 `vs` 逐字展开）要两个基例：
`tSigmaPoly [] = 1` 与单字表的伸缩律。本节把它们机检（`tSigmaPoly_scale` 的直接特例）。

**射程（诚实边界）**：仅基例。`vs(σ,g)` 字表构造（下一节，`SliceTransport.lean`）、
label-g 判据、字表主恒等式、`hAdBd` 正文**未做**；`hZ` 未证；H2 仍不是定理。 -/

/-- 空字表：`tSigmaPoly [] = 1`（字典归纳的基例）。 -/
theorem tSigmaPoly_nil (F : Type) [Field F] (r n d : ℕ) :
    tSigmaPoly F r n d ([] : List (List (Fin d × Fin r))) = 1 := by
  simp [tSigmaPoly]

#print axioms tSigmaPoly_nil

/-- 单字表的伸缩律（`tSigmaPoly_scale` 的基例形态）。 -/
theorem tSigmaPoly_singleton_scale (F : Type) [Field F] (r n d : ℕ) (lam : Fin d → F)
    (w : List (Fin d × Fin r)) :
    blockScaleR F d (Fin r × Fin n × Fin n) lam (tSigmaPoly F r n d [w])
      = (w.map (fun p => lam p.1)).prod • tSigmaPoly F r n d [w] := by
  rw [tSigmaPoly_scale]
  simp

#print axioms tSigmaPoly_singleton_scale


end Procesi
