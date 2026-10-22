/-
  Procesi —— **(A)+(B) S2b 的准备层：`lem:14.12` 所需的第三个下标**

  **原文（逐字）**：`raw/Saltman1999ch14.tex` `lem:14.12`：
  > Assume `n>1`. Suppose `γ : PGL_n(F) → A` is a group homomorphism into an abelian group
  > `A` (written multiplicatively). Then `γ(α)^n = 1` for all `α ∈ PGL_n(F)`.

  **归约（照原文的"elementary exercise"路线，已在计划件登记）**：对 `n ≥ 3`，`PGL_n = SL_n·T/F^×`
  且 `SL_n` 完美 ⟹ `PGL_n^{ab}` 被 `n` 杀死。`SL_n` 完美的两条标准事实：
  * **(ii) Steinberg 换位子** `E_ij(a) = ⁅E_ik(a), E_kj(1)⁆`（`i, j, k` 互异）——**需要第三下标**，
    这正是本件交付的前提；矩阵层面的等价形式是
    `E_ik(a) * E_kj(b) = E_ij(a*b) * E_kj(b) * E_ik(a)`（`E_ab(c) = 1 + c·single a b`）；
  * **(i) 生成性** `SL_n(F) = ⟨transvections⟩`（`n ≥ 2`；mathlib 的
    `Mathlib/LinearAlgebra/Matrix/Transvection.lean` 只提供 `transvection` 与同下标乘积引理，
    **没有**生成性定理；`ElementaryRowOperations.lean`／`Echelon/Decomposition.lean` 提供行等价与
    阶梯证书，但"行变换矩阵是 transvections 之积"仍需自建）。

  **本件射程**：只有 `fin_third`（(ii) 的纯组合前提）。**(i)/(ii) 本体未做**，
  登记于 `wiki/proj-AB-formalization-plan.md` §2b。
-/
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.Tactic.NoncommRing

open Matrix
open scoped commutatorElement

namespace Procesi

/-- **矩阵单位乘法（库内缺失的构件）**：`single a b x * single c d y`
在 `b = c` 时为 `single a d (x*y)`，否则为 `0`。

**为何自建**：本 pin 的 mathlib **无** `Matrix.single_mul_single`（也无 `stdBasisMatrix`），
而 Steinberg 换位子与 `SL_n` 生成性的全部计算都只用 `1 + c·single` 的乘法 ⟹ 这条是关键工具。 -/
lemma single_mul_single {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (a b c d : n) (x y : R) :
    Matrix.single a b x * Matrix.single c d y
      = if b = c then Matrix.single a d (x * y) else 0 := by
  ext u v
  rw [Matrix.mul_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single b]
    · simp only [Matrix.single_apply]
      by_cases hau : a = u <;> by_cases hdv : d = v <;> simp [hau, hdv]
    · intro j _ hj
      simp only [Matrix.single_apply]
      simp [Ne.symm hj]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z = b
    · simp only [Matrix.single_apply]
      simp [hz, Ne.symm h]
    · simp only [Matrix.single_apply]
      simp [hz, Ne.symm hz]

/-- **第三下标（`3 ≤ n` 时）**：`i ≠ j` 时存在 `k` 与两者都不同。

**用途**：Steinberg 换位子 `E_ij(a) = ⁅E_ik(a), E_kj(1)⁆` 需要 `k ∉ {i, j}`，
而 `n ≥ 3` 保证存在（`n = 2` 时不存在——这正是 `SL_2` 必须另证的原因，
mathlib 用 `SL2.commutator_eq_top` 单独处理）。 -/
theorem fin_third {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (_hij : i ≠ j) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  have hcard : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  have hlt : ({i, j} : Finset (Fin n)).card < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2⟩

#print axioms single_mul_single
#print axioms fin_third

/-- **两条 transvection 的乘积（一般形）**：中间下标相同才留下 `single`-项。 -/
lemma transvection_mul_transvection {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    (a b c d : n) (x y : F) :
    Matrix.transvection a b x * Matrix.transvection c d y
      = 1 + Matrix.single c d y + Matrix.single a b x
        + (if b = c then Matrix.single a d (x * y) else 0) := by
  rw [Matrix.transvection, Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_one, single_mul_single]
  abel

/-- ★★ **Steinberg 换位子（矩阵层，照原文 `lem:14.12` 的"elementary exercise"）**：
`E_ik(a) * E_kj(b) = E_ij(a*b) * E_kj(b) * E_ik(a)`（`i, j, k` 互异）。

**为何是它**：右乘 `E_ik(-a)`、`E_kj(-b)` 即得 `⁅E_ik(a), E_kj(b)⁆ = E_ij(ab)`，
于是 `E_ij(a) ∈ [GL_n, GL_n]`——这是 `lem:14.12` 的 (ii) 步。 -/
lemma steinberg_transvection {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    {i j k : n} (hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k) (a b : F) :
    Matrix.transvection i k a * Matrix.transvection k j b
      = Matrix.transvection i j (a * b) * Matrix.transvection k j b
        * Matrix.transvection i k a := by
  have h3 : Matrix.transvection i k a * Matrix.transvection k j b
      = 1 + Matrix.single k j b + Matrix.single i k a + Matrix.single i j (a * b) := by
    rw [transvection_mul_transvection, if_pos rfl]
  have h1 : Matrix.transvection i j (a * b) * Matrix.transvection k j b
      = 1 + Matrix.single k j b + Matrix.single i j (a * b) := by
    rw [transvection_mul_transvection, if_neg hjk]
    abel
  have h2 : (1 + Matrix.single k j b + Matrix.single i j (a * b))
      * Matrix.transvection i k a
      = 1 + Matrix.single k j b + Matrix.single i k a + Matrix.single i j (a * b) := by
    rw [Matrix.transvection]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_add, Matrix.mul_one, single_mul_single, single_mul_single,
      if_neg (Ne.symm hij), if_neg (Ne.symm hij)]
    abel
  have hR : Matrix.transvection i j (a * b) * Matrix.transvection k j b
      * Matrix.transvection i k a
      = 1 + Matrix.single k j b + Matrix.single i k a + Matrix.single i j (a * b) := by
    rw [h1, h2]
  rw [h3, hR]

#print axioms transvection_mul_transvection
#print axioms steinberg_transvection

/-- **左乘 transvection 保持行列式**（因而 `SL` 在行变换下稳定）——情形 1 的清零步骤要用。 -/
lemma det_transvection_mul {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    {i j : m} (hij : i ≠ j) (c : F) (A : Matrix m m F) :
    (Matrix.transvection i j c * A).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_transvection_of_ne (i := i) (j := j) hij, one_mul]

#print axioms det_transvection_mul

/-- **`diag(B, 1)` 的行列式**：`SL_{n-1} → SL_n` 嵌入（情形 1 的收口件）的行列式基础。 -/
lemma det_fromBlocks_one {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    (B : Matrix m m F) :
    (Matrix.fromBlocks B 0 0 (1 : Matrix (Fin 1) (Fin 1) F)).det = B.det := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

#print axioms det_fromBlocks_one

/-- **情形 2 的前提**：`det = 1`（故可逆）的矩阵**末列非零**。

用途：若 `(n,n)` 元为零，末列必有一个非零元 `A_{j n}`（`j < n`），左乘 `E_{n j}(1)` 即把
`(n,n)` 元变成 `A_{n n} + A_{j n} = A_{j n} ≠ 0`（行作用 `transvection_mul_apply_same`）。 -/
lemma exists_ne_zero_lastCol {F : Type} [Field F] {k : ℕ}
    {A : Matrix (Fin (k + 1)) (Fin (k + 1)) F} (hA : A.det = 1) :
    ∃ i, A i (Fin.last k) ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 : A.det = 0 := Matrix.det_eq_zero_of_column_eq_zero (Fin.last k) (fun i => h i)
  rw [h0] at hA
  exact one_ne_zero hA.symm

#print axioms exists_ne_zero_lastCol

/-- **情形 1 的单步清零**：若 `(n,n)` 元非零，左乘 `E_{i n}(-A_{i n}/A_{n n})` 把 `(i,n)` 元清零，
且不动 `(n,n)` 元。逐行清零即反复用它（`Finset`-积）。 -/
lemma clear_entry {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    {i nn : m} (h : i ≠ nn) (A : Matrix m m F) (hy : A nn nn ≠ 0) :
    (Matrix.transvection i nn (-(A i nn / A nn nn)) * A) i nn = 0 ∧
    (Matrix.transvection i nn (-(A i nn / A nn nn)) * A) nn nn = A nn nn := by
  constructor
  · rw [Matrix.transvection_mul_apply_same (i := i) (j := nn) (b := nn)]
    field_simp
    ring
  · rw [Matrix.transvection_mul_apply_of_ne (i := i) (j := nn) (a := nn) (b := nn) (Ne.symm h)]

#print axioms clear_entry

/-- **清零步互不干扰**：对第 `i` 行已清零的矩阵，再用别的行 `i'` 做行变换，`(i,n)` 元仍为 0。
（`Finset`-积逐行清零时，"后做的步不破坏先做的零"就靠这条。） -/
lemma clear_entry_stable {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    {i i' nn : m} (h : i ≠ i') (c : F) {B : Matrix m m F} (hB : B i nn = 0) :
    (Matrix.transvection i' nn c * B) i nn = 0 := by
  rw [Matrix.transvection_mul_apply_of_ne (i := i') (j := nn) (a := i) (b := nn) h]
  exact hB

#print axioms clear_entry_stable

/-- **情形 1 末行清零的前提**（末列清零的对偶）：`det = 1` 的矩阵**末行非零**。 -/
lemma exists_ne_zero_lastRow {F : Type} [Field F] {k : ℕ}
    {A : Matrix (Fin (k + 1)) (Fin (k + 1)) F} (hA : A.det = 1) :
    ∃ j, A (Fin.last k) j ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 : A.det = 0 := Matrix.det_eq_zero_of_row_eq_zero (Fin.last k) (fun j => h j)
  rw [h0] at hA
  exact one_ne_zero hA.symm

#print axioms exists_ne_zero_lastRow

/-- **两步清零**（`Finset`-积归纳的形状）：先清第 `i` 行，再清第 `i'` 行，前者仍为零。
一步即 `clear_entry_stable` ＋ `clear_entry`；对 `Finset` 的归纳就是用这条做归纳步。 -/
lemma clear_two {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    {i i' nn : m} (hi : i ≠ nn) (hii' : i ≠ i') (A : Matrix m m F) (hy : A nn nn ≠ 0) :
    (Matrix.transvection i' nn (-(A i' nn / A nn nn)) *
      (Matrix.transvection i nn (-(A i nn / A nn nn)) * A)) i nn = 0 :=
  clear_entry_stable hii' _ (clear_entry hi A hy).1

#print axioms clear_two

/-- **另一行不受影响**：对第 `i` 行的行变换不动第 `i'` 行（`i' ≠ i`）。 -/
lemma row_unchanged {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    {i i' nn : m} (h : i' ≠ i) (c : F) (A : Matrix m m F) :
    (Matrix.transvection i nn c * A) i' nn = A i' nn :=
  Matrix.transvection_mul_apply_of_ne (i := i) (j := nn) (a := i') (b := nn) h c A

#print axioms row_unchanged

/-- **两步清零不动 `(n,n)`**：故 `Finset`-积清零后 `(n,n)` 元仍为 `A nn nn`（用 `det = 1` 定末列时要用）。

关键手法：先把中间矩阵 `set M := E*A` 固定，使行不变性与 `(n,n)` 不变性共用**同一个** `M`；
否则三段内联的 `E*A` 书写形式互不匹配（第 96 轮卡点）。 -/
lemma clear_two_nn {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    {i i' nn : m} (hi : i ≠ nn) (hi' : i' ≠ nn) (hii' : i ≠ i')
    (A : Matrix m m F) (hy : A nn nn ≠ 0) :
    (Matrix.transvection i' nn (-(A i' nn / A nn nn)) *
      (Matrix.transvection i nn (-(A i nn / A nn nn)) * A)) nn nn = A nn nn := by
  set M := Matrix.transvection i nn (-(A i nn / A nn nn)) * A with hM
  have hrow : M i' nn = A i' nn := by rw [hM]; exact row_unchanged (Ne.symm hii') _ A
  have hB : M nn nn = A nn nn := by rw [hM]; exact (clear_entry hi A hy).2
  have hy' : M nn nn ≠ 0 := by rw [hB]; exact hy
  rw [← hrow, ← hB]
  exact (clear_entry hi' M hy').2

#print axioms clear_two_nn

/-- ★★★ **收口件（第 99 轮更正后的关键）**：`2×2` 对角块是 **4 个 transvections 之积**：
`diag(t, t⁻¹) = E_12(t-1) · E_21(1) · E_12((1-t)/t) · E_21(-t)`（`t ≠ 0`）。

**手算验证**（第 100 轮登记、第 101 轮落库）：记 `P = E_12(a)E_21(b)E_12(c)`，则
`(1,1)=1+ab`、`(2,2)=1+bc`、`(1,2)=(1+ab)c+a`、`(2,1)=b`；再右乘 `E_21(d)` 得
`(1,1)=1+ab`、`(2,2)=1+bc`、`(1,2)=(1+ab)c+a`、`(2,1)=b+(1+bc)d`。取
`b=1, c=(1-t)/t, a=t-1, d=-t` 即四个非对角元化为 `t, t⁻¹, 0, 0` ✓。
（三因子不可能：需 `b=0` 却又要有 `(2,1)=0` 与对角被缩放。） -/
lemma two_by_two_decomp {F : Type} [Field F] (t : F) (ht : t ≠ 0) :
    Matrix.transvection (0 : Fin 2) 1 (t - 1) * Matrix.transvection (1 : Fin 2) 0 (1 : F)
      * Matrix.transvection (0 : Fin 2) 1 ((1 - t) / t) * Matrix.transvection (1 : Fin 2) 0 (-t)
      = Matrix.diagonal ![t, t⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.transvection, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring_nf <;> simp)

#print axioms two_by_two_decomp

/-- **`diag(t, t⁻¹) ∈ SL_2`**：配合 `two_by_two_decomp` 即得「`SL_2` 的每个对角元可用 transvections 造」。 -/
lemma det_diagonal_pair {F : Type} [Field F] {t : F} (ht : t ≠ 0) :
    (Matrix.diagonal ![t, t⁻¹] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_two, ht]

#print axioms det_diagonal_pair

/-- **对角块矩阵**：`(i,i)` 处 `t`、`(j,j)` 处 `t⁻¹`、其余对角 `1`、非对角 `0`。
（`two_by_two_decomp` 的 `n×n` 推广的目标右端；`reindex` 方案已否，见第 103 轮登记。） -/
def diagBlock {F : Type} [Field F] {n : Type} [DecidableEq n] (i j : n) (t : F) :
    Matrix n n F :=
  Matrix.of fun a b => if a = b then (if a = i then t else if a = j then t⁻¹ else 1) else 0

@[simp] lemma diagBlock_apply {F : Type} [Field F] {n : Type} [DecidableEq n]
    (i j a b : n) (t : F) :
    diagBlock i j t a b = if a = b then (if a = i then t else if a = j then t⁻¹ else 1) else 0 :=
  rfl

#print axioms diagBlock_apply

lemma diagBlock_ii {F : Type} [Field F] {n : Type} [DecidableEq n]
    {i j : n} (hij : i ≠ j) (t : F) : diagBlock i j t i i = t := by
  simp [diagBlock_apply]

lemma diagBlock_jj {F : Type} [Field F] {n : Type} [DecidableEq n]
    {i j : n} (hij : i ≠ j) (t : F) : diagBlock i j t j j = t⁻¹ := by
  simp [diagBlock_apply, Ne.symm hij]

#print axioms diagBlock_ii
#print axioms diagBlock_jj

lemma diagBlock_of_ne {F : Type} [Field F] {n : Type} [DecidableEq n]
    (i j : n) {a b : n} (h : a ≠ b) (t : F) : diagBlock i j t a b = 0 := by
  simp [diagBlock_apply, h]

lemma diagBlock_other {F : Type} [Field F] {n : Type} [DecidableEq n]
    (i j : n) {a : n} (hai : a ≠ i) (haj : a ≠ j) (t : F) : diagBlock i j t a a = 1 := by
  simp [diagBlock_apply, hai, haj]

#print axioms diagBlock_of_ne
#print axioms diagBlock_other

/-- **矩阵单位乘法的「相接」形**（`single_mul_single` 在中间下标相同时的特化）：
`single a b x * single b d y = single a d (x*y)`。四因子展开里的**留下项**全由它产出。 -/
lemma single_mul_single_eq {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    {a b d : n} (x y : F) :
    Matrix.single a b x * Matrix.single b d y = Matrix.single a d (x * y) := by
  rw [single_mul_single, if_pos rfl]

/-- **矩阵单位乘法的「断开」形**：中间下标不同则为 `0`（四因子展开里的**消去项**）。 -/
lemma single_mul_single_ne {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    {a b c d : n} (h : b ≠ c) (x y : F) :
    Matrix.single a b x * Matrix.single c d y = 0 := by
  rw [single_mul_single, if_neg h]

#print axioms single_mul_single_eq
#print axioms single_mul_single_ne

/-- ★★★ **四个 transvection 的乘积（闭式）**：下标序列 `i, j, i, j`（`i ≠ j`）时，
乘积完全落在 `{1, S_ij, S_ji, S_ii, S_jj}` 张成的 5 维子空间里，系数如右端。

**用途**：`diagBlock_mul_transvections` 的全部算术来源。也说明**四个**因子足够
（三个不够：见 `two_by_two_decomp` 的登记：需 `b = 0` 又要 `(2,1) = 0`）。

**证明**：逐步右乘（`h1`／`h2`／`hY`）＋ `single_mul_single_eq`／`_ne` ＋ `abel`；
**不用 `Matrix.mul_apply`**（故 `n` 任意，无 `Finset.univ` 求和）。 -/
lemma four_transvection_mul {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    {i j : n} (hij : i ≠ j) (a b c d : F) :
    Matrix.transvection i j a * Matrix.transvection j i b * Matrix.transvection i j c
      * Matrix.transvection j i d
      = 1 + Matrix.single j i (b + d + b * c * d)
        + Matrix.single i j (a + c + a * b * c)
        + Matrix.single j j (b * c)
        + Matrix.single i i (a * b + c * d + a * d + a * b * c * d) := by
  have hji : j ≠ i := Ne.symm hij
  have h1 : Matrix.transvection i j a * Matrix.transvection j i b
      = 1 + Matrix.single j i b + Matrix.single i j a + Matrix.single i i (a * b) := by
    rw [transvection_mul_transvection, if_pos rfl]
  have hX : (1 + Matrix.single j i b + Matrix.single i j a + Matrix.single i i (a * b))
      * Matrix.single i j c
      = Matrix.single i j c + Matrix.single j j (b * c) + Matrix.single i j (a * b * c) := by
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul,
      single_mul_single_eq, single_mul_single_ne hji, single_mul_single_eq]
    abel
  have h2 : (1 + Matrix.single j i b + Matrix.single i j a + Matrix.single i i (a * b))
      * Matrix.transvection i j c
      = (1 + Matrix.single j i b + Matrix.single i i (a * b) + Matrix.single j j (b * c))
        + Matrix.single i j (a + c + a * b * c) := by
    rw [show Matrix.transvection i j c = 1 + Matrix.single i j c from rfl, Matrix.mul_add,
      Matrix.mul_one, hX]
    simp only [Matrix.single_add]
    abel
  have hcoef : (a + c + a * b * c) * d = a * d + c * d + a * b * c * d := by ring
  have hY : ((1 + Matrix.single j i b + Matrix.single i i (a * b) + Matrix.single j j (b * c))
        + Matrix.single i j (a + c + a * b * c)) * Matrix.transvection j i d
      = ((1 + Matrix.single j i b + Matrix.single i i (a * b) + Matrix.single j j (b * c))
          + Matrix.single i j (a + c + a * b * c))
        + (Matrix.single j i d + Matrix.single j i (b * c * d) + Matrix.single i i (a * d)
          + Matrix.single i i (c * d) + Matrix.single i i (a * b * c * d)) := by
    rw [show Matrix.transvection j i d = 1 + Matrix.single j i d from rfl, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
      Matrix.one_mul, single_mul_single_ne hij, single_mul_single_ne hij,
      single_mul_single_eq, single_mul_single_eq, hcoef]
    simp only [Matrix.single_add]
    abel
  rw [h1, h2, hY]
  simp only [Matrix.single_add]
  abel

#print axioms four_transvection_mul

/-- ★★★ **`n×n` 对角块的 transvection 分解**（`two_by_two_decomp` 的 `n` 维版，
第 105 轮的逐字陈述、第 113 轮机检）：`i ≠ j`、`t ≠ 0` 时，`diagBlock i j t`
（`(i,i)` 处 `t`、`(j,j)` 处 `t⁻¹`、其余对角 `1`、非对角 `0`）是 **4 个 transvection 之积**。

**用途**：`SL_n` 生成性（(i) 步）的"对角收口"——`det = 1` 的对角矩阵拆成
`∏_{k ≥ 1} diagBlock 0 k (d_k⁻¹)`，每块再由本引理化为 transvections。

**证明**：`four_transvection_mul` ＋ 四个系数等式（`field_simp`／`ring`，用 `t ≠ 0`），
再按 `diagBlock` 的四条刻画逐项比对。 -/
lemma diagBlock_mul_transvections {F : Type} [Field F] {n : Type} [Fintype n]
    [DecidableEq n] {i j : n} (hij : i ≠ j) (t : F) (ht : t ≠ 0) :
    Matrix.transvection i j (t - 1) * Matrix.transvection j i (1 : F)
      * Matrix.transvection i j ((1 - t) / t) * Matrix.transvection j i (-t)
      = diagBlock i j t := by
  rw [four_transvection_mul hij (t - 1) (1 : F) ((1 - t) / t) (-t)]
  have hA : (1 : F) + -t + 1 * ((1 - t) / t) * -t = 0 := by
    field_simp
    ring
  have hB : (t - 1) + (1 - t) / t + (t - 1) * 1 * ((1 - t) / t) = 0 := by
    field_simp
    ring
  have hC : (1 : F) * ((1 - t) / t) = t⁻¹ - 1 := by
    field_simp
  have hD : (t - 1) * 1 + (1 - t) / t * -t + (t - 1) * -t
      + (t - 1) * 1 * ((1 - t) / t) * -t = t - 1 := by
    field_simp
    ring
  rw [hA, hB, hD, hC]
  simp only [Matrix.single_zero, add_zero]
  ext p q
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi
      rw [diagBlock_ii hij t]
      simp [Matrix.add_apply, Matrix.single_apply, Ne.symm hij]
    · by_cases hpj : p = j
      · subst hpj
        rw [diagBlock_jj hij t]
        simp [Matrix.add_apply, Matrix.single_apply, hpi, Ne.symm hpi, hij]
      · rw [diagBlock_other i j hpi hpj t]
        simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hpi, hpj,
          Ne.symm hpi, Ne.symm hpj, hij]
  · rw [diagBlock_of_ne i j hpq t]
    have h1 : ¬(i = p ∧ i = q) := by
      rintro ⟨e1, e2⟩
      exact hpq (e1.symm.trans e2)
    have h2 : ¬(j = p ∧ j = q) := by
      rintro ⟨e1, e2⟩
      exact hpq (e1.symm.trans e2)
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hpq, h1, h2]

#print axioms diagBlock_mul_transvections


/-- ★★★ **`lem:14.12` 的 (ii) 步完成**：`n ≥ 3` 时每个 transvection 都在 `GL_n` 的换位子群里
（`E_ij(a) = ⁅E_ik(a), E_kj(1)⁆`，用 `fin_third` 取第三下标）。 -/
theorem transvection_mem_commutator {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j) (a : F) :
    GeneralLinearGroup.transvection i j hij a
      ∈ commutator (Matrix.GeneralLinearGroup (Fin n) F) := by
  obtain ⟨k, hik, hjk⟩ := fin_third hn hij
  have hcancel_ik : Matrix.transvection i k a * Matrix.transvection i k (-a) = 1 := by
    simpa using Matrix.transvection_mul_transvection_same (i := i) (j := k) (Ne.symm hik) a (-a)
  have hcancel_kj : Matrix.transvection k j (1 : F) * Matrix.transvection k j (-1) = 1 := by
    simpa using Matrix.transvection_mul_transvection_same (i := k) (j := j) hjk (1 : F) (-1)
  have hmat : Matrix.transvection i k a * Matrix.transvection k j (1 : F)
      * Matrix.transvection i k (-a) * Matrix.transvection k j (-1)
      = Matrix.transvection i j a := by
    have hs := steinberg_transvection (i := i) (j := j) (k := k) hij (Ne.symm hik) (Ne.symm hjk)
      a (1 : F)
    rw [mul_one] at hs
    calc Matrix.transvection i k a * Matrix.transvection k j (1 : F)
          * Matrix.transvection i k (-a) * Matrix.transvection k j (-1)
        = (Matrix.transvection i j a * Matrix.transvection k j (1 : F)
            * Matrix.transvection i k a) * Matrix.transvection i k (-a)
            * Matrix.transvection k j (-1) := by rw [hs]
      _ = Matrix.transvection i j a * Matrix.transvection k j (1 : F)
            * (Matrix.transvection i k a * Matrix.transvection i k (-a))
            * Matrix.transvection k j (-1) := by noncomm_ring
      _ = Matrix.transvection i j a * Matrix.transvection k j (1 : F)
            * Matrix.transvection k j (-1) := by rw [hcancel_ik, mul_one]
      _ = Matrix.transvection i j a := by rw [Matrix.mul_assoc, hcancel_kj, mul_one]
  have hcomm : ⁅GeneralLinearGroup.transvection i k (Ne.symm hik) a,
      GeneralLinearGroup.transvection k j hjk (1 : F)⁆
      = GeneralLinearGroup.transvection i j hij a := by
    apply Units.ext
    show Matrix.transvection i k a * Matrix.transvection k j (1 : F)
      * Matrix.transvection i k (-a) * Matrix.transvection k j (-1) = Matrix.transvection i j a
    exact hmat
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

#print axioms transvection_mem_commutator

end

 Procesi
