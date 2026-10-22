/-
  Procesi —— **(A)+(B) S2b(i) 收口：`SL_n(F)` 由 transvections 生成，且 `SL_n ⊆ [GL_n, GL_n]`**

  **原文（逐字）**：`raw/Saltman1999ch14.tex` `lem:14.12`（原文只说 "elementary exercise"，不给证明）：
  > Assume `n>1`. Suppose `γ : PGL_n(F) → A` is a group homomorphism into an abelian group
  > `A` (written multiplicatively). Then `γ(α)^n = 1` for all `α ∈ PGL_n(F)`.

  **本件交付**（计划件 §2b 的 (i) 步；两项都用**库内件**，未自建消元归纳 —— L46／L47）：
  * `closure_range_transvection_eq_top`：`n` 非平凡（`n ≥ 2`）时 `SL_n(F)` 由 transvections 生成。
    缺件是**任意下标**的 `diag2n` 分解；本仓 `diagBlock_mul_transvections`（`SLPerfect.lean`）
    恰好给出它，再套 mathlib `SpecialLinearGroup.diagonal_transvection_induction'`
    （`Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:708`）。
    **同一结果的外部件**：TauCeti `Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`
    （`LinearAlgebra/Matrix/SpecialLinearGroup/Transvection.lean:595`，Apache-2.0）——
    其证明结构与本件一致（`diagonal_transvection_induction'` ＋ `diag2n_decompose`）；
    TauCeti 在该 pin 上另证了 `ℤ` 情形，本件不需要。
  * `sl_mem_commutator`：`n ≥ 3` 时 `SL_n(F) ⊆ [GL_n(F), GL_n(F)]`
    （`transvection_mem_commutator`（`SLPerfect.lean`）＋ 上一行，经 `toGL` 的 `comap` 收口）。

  **用途**：`lem:14.12` 的 `γ|_{SL_n} = 1` —— 目标群 `A` 交换 ⟹ 换位子被 `γ` 杀死。
-/
import Procesi.SLPerfect
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.IndexNormal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod

open Matrix
open scoped commutatorElement

namespace Procesi

variable {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]

/-- `diagBlock` 就是 mathlib 的 `diag2n` 的矩阵（`diag2n` 定义里写 `diagonal`，两者是同一个
`Matrix.of`）。把 `diagBlock` 的四条刻画与 `diag2n` 的 SL 性质接起来的桥。 -/
lemma diagBlock_eq_diag2n_coe {i j : n} (hij : i ≠ j) (t : F) (ht : t ≠ 0) :
    diagBlock i j t = (SpecialLinearGroup.diag2n hij t ht).1 := rfl

#print axioms diagBlock_eq_diag2n_coe

/-- **`diagBlock` 的行列式为 `1`**（`t ≠ 0` 时）：直接取 `diag2n` 的 SL 见证。 -/
lemma det_diagBlock {i j : n} (hij : i ≠ j) {t : F} (ht : t ≠ 0) :
    (diagBlock i j t).det = 1 := by
  rw [diagBlock_eq_diag2n_coe hij t ht]
  exact (SpecialLinearGroup.diag2n hij t ht).2

#print axioms det_diagBlock

/-- ★★★ **任意下标的 `diag2n` 是 4 个 SL-transvections 之积**：
mathlib 只有 `Fin 2` 的 `diag2_decompose`（`SpecialLinearGroup.lean:777`），本件补上**任意两个下标**
（`i ≠ j`）——这正是 `SL_n` 生成性所需的那一条。

**证明**：`Subtype.ext` 后在矩阵层用本仓 `diagBlock_mul_transvections`（`SLPerfect.lean`）。 -/
lemma diag2n_decompose {i j : n} (hij : i ≠ j) {t : F} (ht : t ≠ 0) :
    SpecialLinearGroup.diag2n hij t ht
      = SpecialLinearGroup.transvection hij (t - 1)
        * SpecialLinearGroup.transvection (Ne.symm hij) (1 : F)
        * SpecialLinearGroup.transvection hij ((1 - t) / t)
        * SpecialLinearGroup.transvection (Ne.symm hij) (-t) := by
  apply Subtype.ext
  change diagBlock i j t = Matrix.transvection i j (t - 1) * Matrix.transvection j i (1 : F)
    * Matrix.transvection i j ((1 - t) / t) * Matrix.transvection j i (-t)
  exact (diagBlock_mul_transvections hij t ht).symm

#print axioms diag2n_decompose

/-- ★★★ **`SL_n(F)` 由 transvections 生成**（`n` 非平凡；`(i)` 步的收口件）。

**证明**：照 mathlib `diagonal_transvection_induction'` 的三条义务——对角（任意两下标 `diag2n`
归约到 `diag2n_decompose`）、transvection（自身）、乘法（子群封闭）。**零消元归纳**。 -/
theorem closure_range_transvection_eq_top [Nontrivial n] :
    Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct n F → SpecialLinearGroup n F)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  let H : Subgroup (SpecialLinearGroup n F) :=
    Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct n F → SpecialLinearGroup n F))
  have htrans : ∀ {i j : n} (hij : i ≠ j) (c : F),
      SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij c
    exact Subgroup.subset_closure (Set.mem_range_self (⟨i, j, hij, c⟩ : TransvectionStruct n F))
  show g ∈ H
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun x => x ∈ H) g ?_ ?_ ?_
  · intro i j hij c hc
    rw [diag2n_decompose hij hc]
    exact H.mul_mem (H.mul_mem (H.mul_mem (htrans hij (c - 1))
      (htrans (Ne.symm hij) 1)) (htrans hij ((1 - c) / c))) (htrans (Ne.symm hij) (-c))
  · intro i j hij a
    exact htrans hij a
  · intro A B hA hB
    exact H.mul_mem hA hB

#print axioms closure_range_transvection_eq_top

/-- ★★★ **`SL_n(F) ⊆ [GL_n(F), GL_n(F)]`**（`n ≥ 3`）：`lem:14.12` 的 `γ|_{SL_n} = 1` 的全部 Lean 内容。

**证明**：取 `K := (commutator GL).comap toGL`；`K` 含每个 transvection
（`transvection_mem_commutator`，`SLPerfect.lean`）⟹ 含 `closure` ＝ `⊤`（上一行）⟹ 含一切 `A ∈ SL`。 -/
theorem sl_mem_commutator {n : ℕ} (hn : 3 ≤ n) (A : SpecialLinearGroup (Fin n) F) :
    (A : GeneralLinearGroup (Fin n) F) ∈ commutator (GeneralLinearGroup (Fin n) F) := by
  haveI : Nontrivial (Fin n) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  let K : Subgroup (SpecialLinearGroup (Fin n) F) :=
    (commutator (GeneralLinearGroup (Fin n) F)).comap SpecialLinearGroup.toGL
  have hK : (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) ≤ K := by
    rw [← closure_range_transvection_eq_top (F := F) (n := Fin n)]
    refine (Subgroup.closure_le K).2 ?_
    rintro _ ⟨t, rfl⟩
    show SpecialLinearGroup.toGL t.toSpecialLinearGroup ∈ commutator (GeneralLinearGroup (Fin n) F)
    have h : SpecialLinearGroup.toGL t.toSpecialLinearGroup
        = GeneralLinearGroup.transvection t.i t.j t.hij t.c := by
      apply Units.ext
      simp [SpecialLinearGroup.coe_GL_coe_matrix, TransvectionStruct.toSpecialLinearGroup_coe,
        TransvectionStruct.toMatrix, GeneralLinearGroup.transvection]
    rw [h]
    exact transvection_mem_commutator hn t.hij t.c
  exact hK (Subgroup.mem_top A)

#print axioms sl_mem_commutator


/-- ★★ **`n = 2` 的 (ii)（借 mathlib）**：`|F| ≥ 4`（存在 `a ≠ 0`、`a² ≠ 1`）时，`SL(2,F)` 的每个
transvection 都在 `SL(2,F)` 的换位子群内（因此也在 `GL_2` 的换位子群内）。

**用途**：`lem:14.12` 的 `n = 2` 情形（阶段 A，§2b·庚）。mathlib 已有 `Matrix.transvection_mem_commutator`
（`SpecialLinearGroup.lean:769`，按 `fin_cases i` 归约到 `_₀`／`_₁`）。 -/
lemma sl2_transvection_mem_commutator {F : Type} [Field F] {a : F} (ha : a ≠ 0)
    (hasq : a ^ 2 ≠ 1) {i j : Fin 2} (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ∈ commutator (SpecialLinearGroup (Fin 2) F) :=
  Matrix.transvection_mem_commutator ha hasq hij c

#print axioms sl2_transvection_mem_commutator

/-- ★★ **`n = 2`（`|F| ≥ 4`）：`SL_2 ⊆ [GL_2, GL_2]`**。

**技巧（第 124 轮定的改法）**：**绕开 `Subgroup.map`**——用 `Subgroup.commutator_le` 取
`H₃ := (commutator GL).comap toGL`、`H₁ = H₂ = ⊤`，只需 `⁅toGL g₁, toGL g₂⁆ ∈ commutator GL`
（`map_commutatorElement` ＋ `Subgroup.commutator_mem_commutator`）；再由
`closure_range_transvection_eq_top`（`Fin 2` 非平凡）与 `sl2_transvection_mem_commutator` 收口。 -/
theorem sl2_mem_commutator {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1)
    (A : SpecialLinearGroup (Fin 2) F) :
    (A : GeneralLinearGroup (Fin 2) F) ∈ commutator (GeneralLinearGroup (Fin 2) F) := by
  haveI : Nontrivial (Fin 2) := ⟨⟨0, 1, by decide⟩⟩
  set K : Subgroup (SpecialLinearGroup (Fin 2) F) :=
    (commutator (GeneralLinearGroup (Fin 2) F)).comap SpecialLinearGroup.toGL with hK
  have hcomm : commutator (SpecialLinearGroup (Fin 2) F) ≤ K := by
    rw [show commutator (SpecialLinearGroup (Fin 2) F)
      = ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)), ⊤⁆ from rfl, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    show SpecialLinearGroup.toGL ⁅g₁, g₂⁆ ∈ commutator (GeneralLinearGroup (Fin 2) F)
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have htop : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)) ≤ K := by
    rw [← closure_range_transvection_eq_top (F := F) (n := Fin 2)]
    refine (Subgroup.closure_le K).2 ?_
    rintro _ ⟨t, rfl⟩
    exact hcomm (sl2_transvection_mem_commutator ha hasq t.hij t.c)
  exact htop (Subgroup.mem_top A)

#print axioms sl2_mem_commutator


/-- `F₂^×` 平凡（`(ZMod 2)ˣ` 为单点）。**用途**：`n = 2` 阶段 B（`F₂`）——
`PGL_2(F₂) = GL_2(F₂) = SL_2(F₂)`。 -/
lemma zmod_two_units_subsingleton : Subsingleton (ZMod 2)ˣ := by
  have h : Fintype.card (ZMod 2)ˣ = 1 := by decide
  exact Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h)

#print axioms zmod_two_units_subsingleton

/-- ★★ **`GL_2(F₂)` 的行列式恒为 1**：故 `GL_2(F₂) = SL_2(F₂)`（`F₂^×` 平凡），
即 `F₂` 时 `PGL_2`、`GL_2`、`SL_2` 三者相同。**用途**：`n = 2` 阶段 B（`F₂`）。 -/
theorem f2_gl_det_eq_one (g : GeneralLinearGroup (Fin 2) (ZMod 2)) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1 := by
  haveI : Subsingleton (ZMod 2)ˣ := zmod_two_units_subsingleton
  have h : GeneralLinearGroup.det g = 1 := Subsingleton.elim _ 1
  have hv := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h
  simpa using hv

#print axioms f2_gl_det_eq_one


/-- ★★ **`|GL_2(F₂)| = 6`**（`decide` 枚举 16 个矩阵中的可逆者）。**用途**：`n = 2` 阶段 B（`F₂`）。 -/
theorem f2_gl_card : Fintype.card (GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by decide

#print axioms f2_gl_card

/-- ★★ **`GL_2(F₂)` 非交换**（`E₁₂(1)` 与 `E₂₁(1)` 不交换）。配合 `f2_gl_card`：`|G| = 6`、非交换
⟹ `[G,G]` 的阶既非 1 也非 6 ⟹ 由 Lagrange 得 3 ⟹ `[G:G'] = 2` ⟹ `g² ∈ G'`。
**用途**：`n = 2` 阶段 B（`F₂`）。 -/
theorem f2_gl_exists_noncomm :
    ∃ g h : GeneralLinearGroup (Fin 2) (ZMod 2), g * h ≠ h * g :=
  ⟨GeneralLinearGroup.transvection (0 : Fin 2) 1 (by decide) (1 : ZMod 2),
    GeneralLinearGroup.transvection 1 0 (by decide) (1 : ZMod 2), by decide⟩

#print axioms f2_gl_exists_noncomm


/-- ★★ **阶 2 的群指数为 2**：`|H| = 2` ⟹ `x ^ 2 = 1`（`pow_card_eq_one`，即 Lagrange）。
**用途**：`n = 2` 阶段 B —— `F₂` 时 `|GL_2(F₂) ⧸ [G,G]| = 2` ⟹ 商内每元平方为 1 ⟹ `g² ∈ [G,G]`。 -/
theorem sq_eq_one_of_card_eq_two {H : Type*} [Group H] [Fintype H]
    (h : Fintype.card H = 2) (x : H) : x ^ 2 = 1 := by
  rw [← h]
  exact pow_card_eq_one

#print axioms sq_eq_one_of_card_eq_two


/-- ★★ **商群阶 2 ⟹ 平方落入核**：`|M| = 2`、`f : G →* M` ⟹ `g ^ 2 ∈ f.ker`。
**用途**：`n = 2` 阶段 B（`F₂`）：取 `M := GL_2(F₂) ⧸ [G,G]`、`f := QuotientGroup.mk`，
则 `f.ker = [G,G]`，得 `g² ∈ [G,G]`。 -/
theorem sq_mem_ker_of_card_two {G M : Type*} [Group G] [Group M] [Fintype M] (f : G →* M)
    (h : Fintype.card M = 2) (g : G) : g ^ 2 ∈ f.ker := by
  rw [MonoidHom.mem_ker, map_pow, sq_eq_one_of_card_eq_two h (f g)]

#print axioms sq_mem_ker_of_card_two


/-- `Nat.card` 形式的 `|GL_2(F₂)| = 6`（供 `Subgroup.card_mul_index` 使用，该引理用 `Nat.card`）。 -/
theorem f2_gl_natcard : Nat.card (GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card, f2_gl_card]

#print axioms f2_gl_natcard

/-! ### `n = 2` 的情形 B：`F = F₂`（`lem:14.12` 射程的收口）

`GL_2(F₂) ≅ S₃`：`F₂ˣ` 平凡 ⟹ `det` 恒 1 ⟹ `SL_2(F₂) = GL_2(F₂)`，此时
**`SL_2 ⊆ [GL_2, GL_2]` 是假的**（`S₃` 非完美），故 `sl2_mem_commutator`（需 `∃ a ≠ 0, a² ≠ 1`）
的路线在 `F₂` 上原理上不可用。改走**换位子群的指数**路线：

* `|GL_2(F₂)| = 6`（`f2_gl_card`）且非交换（`f2_gl_exists_noncomm`）；
* Cauchy（`exists_prime_orderOf_dvd_card`）给阶 3 的元 `x`，`H := ⟨x⟩` 阶 3、指数 2 ⟹ 正规
  （`Subgroup.normal_of_index_eq_two`）；
* `[G,G] ≤ H`（`commutator_le_of_index_two`，元素层）⟹ `Nat.card [G,G] ∣ 3`；非交换 ⟹ `≠ 1`
  ⟹ `Nat.card [G,G] = 3` ⟹ `[G,G]` 的指数为 2；
* `Subgroup.sq_mem_of_index_two` ⟹ `g² ∈ [G,G]`。

**与 `n ≥ 3` 路线的差别（登记）**：`pgl_pow_n_eq_one` 只用 `γ|_{SL_n} = 1`；
`F₂` 时改用 `γ|_{[G,G]} = 1` 且 `g² ∈ [G,G]` —— 结论 `γ(α)² = 1` 相同，
但**不需要** `SL_2 ⊆ [G,G]`（它在 `F₂` 上不成立）。 -/

/-- ★★ **指数 2 的子群包含换位子群**（元素层：只用 `Subgroup.mul_mem_iff_of_index_two`，
故**不需要**正规性假设）。**用途**：`n = 2` 情形 B（`F₂`）的第 2 步；亦为一般工具件。 -/
theorem commutator_le_of_index_two {G : Type*} [Group G] (H : Subgroup G) (h : H.index = 2) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  have hmul : a * b ∈ H ↔ b * a ∈ H := by
    rw [Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h]
    exact Iff.comm
  rw [show ⁅a, b⁆ = (a * b) * (b * a)⁻¹ by
    rw [commutatorElement_def]
    group]
  by_cases hab : a * b ∈ H
  · exact H.mul_mem hab (H.inv_mem (hmul.mp hab))
  · have hba : b * a ∉ H := fun hh => hab (hmul.mpr hh)
    have hinv : (b * a)⁻¹ ∉ H := fun hh => hba (by simpa using H.inv_mem hh)
    rw [Subgroup.mul_mem_iff_of_index_two h]
    exact ⟨fun hh => absurd hh hab, fun hh => absurd hh hinv⟩

#print axioms commutator_le_of_index_two

/-- ★★ **`GL_2(F₂)` 有阶 3 的元素**（Cauchy 定理；`3 ∣ 6`）。**用途**：`n = 2` 情形 B（`F₂`）。 -/
theorem f2_exists_order_three :
    ∃ x : GeneralLinearGroup (Fin 2) (ZMod 2), orderOf x = 3 := by
  have hdvd : 3 ∣ Fintype.card (GeneralLinearGroup (Fin 2) (ZMod 2)) := by
    rw [← Nat.card_eq_fintype_card, f2_gl_natcard]
    norm_num
  exact exists_prime_orderOf_dvd_card 3 hdvd

#print axioms f2_exists_order_three

/-- ★★ **`GL_2(F₂)` 有指数 2 的正规子群（阶 3）**：取阶 3 的元生成的循环群，用 Lagrange 定指数。
**用途**：`n = 2` 情形 B（`F₂`）—— 指数 2 的子群是换位子群的上界。 -/
theorem f2_exists_index_two_subgroup :
    ∃ H : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 2)),
      H.Normal ∧ H.index = 2 ∧ Nat.card H = 3 := by
  obtain ⟨x, hx⟩ := f2_exists_order_three
  have hcard : Nat.card (GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := f2_gl_natcard
  have hH : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [hH, hcard] at h
    omega
  exact ⟨Subgroup.zpowers x, Subgroup.normal_of_index_eq_two hidx, hidx, hH⟩

#print axioms f2_exists_index_two_subgroup

/-- ★★★ **`n = 2, F = F₂` 的换位子群指数为 2**（`lem:14.12` 射程的收口件）。

**证明**：`[G,G] ≤ H`（`commutator_le_of_index_two`）与 Lagrange 的两层（`GL_2` 内 ＋ `H` 内）
给出 `Nat.card [G,G] * [G,G].relIndex H = 3`（经 `Subgroup.relIndex_mul_index`）；非交换
⟹ `[G,G] ≠ ⊥` ⟹ `Nat.card [G,G] > 1` ⟹ 由 `3` 的素性 `Nat.card [G,G] = 3` ⟹ 指数 2。 -/
theorem f2_commutator_index_two :
    (commutator (GeneralLinearGroup (Fin 2) (ZMod 2))).index = 2 := by
  classical
  obtain ⟨H, _hHn, hHi, _hHc⟩ := f2_exists_index_two_subgroup
  set C : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 2)) :=
    commutator (GeneralLinearGroup (Fin 2) (ZMod 2)) with hC
  have hle : C ≤ H := hC ▸ commutator_le_of_index_two H hHi
  have hcard : Nat.card (GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := f2_gl_natcard
  have hLag : Nat.card C * C.index = 6 := by
    have h := C.card_mul_index
    rw [hcard] at h
    exact h
  have hrel : C.relIndex H * H.index = C.index := Subgroup.relIndex_mul_index hle
  rw [hHi] at hrel
  have h2 : Nat.card C * C.relIndex H * 2 = 6 := by rw [mul_assoc, hrel]; exact hLag
  have h3 : Nat.card C * C.relIndex H = 3 := by omega
  have hdvd : Nat.card C ∣ 3 := ⟨C.relIndex H, h3.symm⟩
  have hne : C ≠ ⊥ := by
    intro hbot
    have hzero : commutator (GeneralLinearGroup (Fin 2) (ZMod 2)) = ⊥ := by
      rw [← hC]; exact hbot
    have hcm : IsMulCommutative (GeneralLinearGroup (Fin 2) (ZMod 2)) :=
      (commutator_eq_bot_iff (G := GeneralLinearGroup (Fin 2) (ZMod 2))).mp hzero
    obtain ⟨g, h, hgh⟩ := f2_gl_exists_noncomm
    exact hgh (isMulCommutative_iff.mp hcm g h)
  have hone : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot (H := C)).mpr hne
  have hC3 : Nat.card C = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  rw [hC3] at hLag
  have hfin : C.index = 2 := by omega
  exact hfin

#print axioms f2_commutator_index_two

/-- ★★★ **`n = 2, F = F₂`：`GL_2(F₂)` 的每一元的平方都落入换位子群**。
**用途**：`pgl_pow_two_eq_one_f2` 的唯一输入（替代 `n ≥ 3` 时的 `SL_n ⊆ [G,G]`）。 -/
theorem f2_sq_mem_commutator (g : GeneralLinearGroup (Fin 2) (ZMod 2)) :
    g ^ 2 ∈ commutator (GeneralLinearGroup (Fin 2) (ZMod 2)) :=
  Subgroup.sq_mem_of_index_two f2_commutator_index_two g

#print axioms f2_sq_mem_commutator

/-! ### `n = 2` 的情形 B'：`F = F₃`（`lem:14.12` 射程的收口）

`F₃ˣ = {1, 2}` 且 `2² = 1`，故数学库中 `Matrix.transvection_mem_commutator` 的假设
`∃ a ≠ 0, a² ≠ 1` 在 `F₃` 上**不成立**，`sl2_mem_commutator`（`|F| ≥ 4`）不可用。
但结论 **`SL_2(F₃) ⊆ [GL_2(F₃), GL_2(F₃)]` 仍然为真**（与 `F₂` 相反 —— 那里 `SL_2 = GL_2 = S₃`
非完美）。本件给出一条不依赖 `a² ≠ 1` 的换位子构造。

**构造**：取 `D = diag(1,2) ∈ GL_2(F₃)`（`det = 2 ≠ 0`，且 `D ∉ SL_2`）。逐项计算给出
`D * E_ij(c) = E_ij(c) * E_ij(c) * D`（`i ≠ j`）：左边在 `(i,j)` 位是 `c·d_i`、右边是 `2c·d_j`，
而 `d = (1,2)` 满足 `d_i = 2·d_j`（在 `F₃` 中 `2·2 = 4 = 1`）。故 `D·E·D⁻¹ = E²`，即
`⁅D, E_ij(c)⁆ = E_ij(c)`：**每个 transvection 都是 `GL_2(F₃)` 中一个具体的换位子**。
再用 `closure_range_transvection_eq_top`（第 114 轮）把 `SL_2(F₃)` 生成出来。

**与 mathlib 的差别（登记）**：mathlib 的 `transvection_mem_commutator₀` 用 `diag2 a⁻¹`
（在 `SL_2` 内）并需 `a² - 1 ≠ 0`；本仓用**不在 `SL_2` 内**的对角元 `diag(1,2)`，
只需 `d - 1 ≠ 0`，故覆盖 `F₃`（以及任何 `|F| ≥ 3` 的域）。 -/

/-- ★★ **`diag(1,2) ∈ GL_2(F₃)`**（`det = 2 ≠ 0`，故不在 `SL_2` 内）。
**用途**：`n = 2` 情形 B'（`F₃`）—— 与 transvection 作换位子。 -/
def f3Diag : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, 2]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    decide)

#print axioms f3Diag

/-- ★★★ **`diag(1,2)` 把 transvection 共轭成它的平方**：`D * E = E * E * D`（`i ≠ j`）。

**证明**：逐项计算（`i, j` 只有 `(0,1)`／`(1,0)` 两种情形，矩阵只有 `2×2` 项）。
`D * E` 与 `E * E * D` 只在 `(i,j)` 位不同：前者是 `c·d_i`、后者是 `2c·d_j`；
`d = (1,2)` 使 `d_i = 2 d_j`（`F₃` 中 `4 = 1`）。 -/
lemma f3Diag_mul_transvection {i j : Fin 2} (hij : i ≠ j) (c : ZMod 3) :
    f3Diag * GeneralLinearGroup.transvection i j hij c
      = GeneralLinearGroup.transvection i j hij c
        * GeneralLinearGroup.transvection i j hij c * f3Diag := by
  have hD : (↑f3Diag : Matrix (Fin 2) (Fin 2) (ZMod 3)) = Matrix.diagonal ![1, 2] := by
    simp [f3Diag]
  have hE : ∀ {i j : Fin 2} (hij : i ≠ j) (c : ZMod 3),
      (↑(GeneralLinearGroup.transvection i j hij c) : Matrix (Fin 2) (Fin 2) (ZMod 3))
        = Matrix.transvection i j c := by
    intro i j hij c
    rfl
  have hne : ∀ {i j : Fin 2}, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  ext a b
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hne hij
  · simp only [GeneralLinearGroup.coe_mul, hD, hE]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection] <;> decide
  · simp only [GeneralLinearGroup.coe_mul, hD, hE]
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection] <;> decide

#print axioms f3Diag_mul_transvection

/-- ★★ **`SL` 的 transvection 与 `GL` 的 transvection 是同一个元**（`toGL` 只忘掉行列式证明）。
**用途**：把 `f3_transvection_mem_commutator`（`GL` 层）搬到 `SL ⊆ GL` 的收口里。 -/
lemma f3_toGL_transvection {i j : Fin 2} (hij : i ≠ j) (c : ZMod 3) :
    (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c) :
      GeneralLinearGroup (Fin 2) (ZMod 3))
      = GeneralLinearGroup.transvection i j hij c := by
  apply Units.ext
  rfl

#print axioms f3_toGL_transvection

/-- ★★★ **`F₃`：每个 transvection 都在 `GL_2(F₃)` 的换位子群内**（`⁅D, E⁆ = E`）。

**证明**：由 `f3Diag_mul_transvection` 得 `D·E·D⁻¹ = E²`，故 `⁅D,E⁆ = D·E·D⁻¹·E⁻¹ = E`。
**这是 `lem:14.12` 在 `F₃` 上的关键替换件**（mathlib 的同名件需 `a² ≠ 1`，`F₃` 上不可用）。 -/
lemma f3_transvection_mem_commutator {i j : Fin 2} (hij : i ≠ j) (c : ZMod 3) :
    GeneralLinearGroup.transvection i j hij c
      ∈ commutator (GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  have hDE := f3Diag_mul_transvection (i := i) (j := j) hij c
  have hconj : f3Diag * GeneralLinearGroup.transvection i j hij c * f3Diag⁻¹
      = GeneralLinearGroup.transvection i j hij c
        * GeneralLinearGroup.transvection i j hij c := by
    rw [hDE]; group
  have hcomm : ⁅f3Diag, GeneralLinearGroup.transvection i j hij c⁆
      = GeneralLinearGroup.transvection i j hij c := by
    rw [commutatorElement_def, hconj]; group
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

#print axioms f3_transvection_mem_commutator

/-- ★★★ **`F₃`：`SL_2(F₃) ⊆ [GL_2(F₃), GL_2(F₃)]`**（`lem:14.12` 的 `γ|_{SL_n} = 1` 在 `F₃` 上的全部内容）。

**证明**：与 `sl2_mem_commutator` 同构，只把 `sl2_transvection_mem_commutator`（需 `a² ≠ 1`）
换成 `f3_transvection_mem_commutator`（用 `diag(1,2)`，无需该假设）；
生成性仍由 `closure_range_transvection_eq_top` 供给。 -/
theorem sl2_mem_commutator_f3 (A : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (A : GeneralLinearGroup (Fin 2) (ZMod 3))
      ∈ commutator (GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  haveI : Nontrivial (Fin 2) := ⟨⟨0, 1, by decide⟩⟩
  set K : Subgroup (SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    (commutator (GeneralLinearGroup (Fin 2) (ZMod 3))).comap SpecialLinearGroup.toGL with hK
  have htop : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) (ZMod 3))) ≤ K := by
    rw [← closure_range_transvection_eq_top (F := ZMod 3) (n := Fin 2)]
    refine (Subgroup.closure_le K).2 ?_
    rintro _ ⟨t, rfl⟩
    show SpecialLinearGroup.toGL (SpecialLinearGroup.transvection t.hij t.c)
      ∈ commutator (GeneralLinearGroup (Fin 2) (ZMod 3))
    rw [f3_toGL_transvection t.hij t.c]
    exact f3_transvection_mem_commutator t.hij t.c
  exact htop (Subgroup.mem_top A)

#print axioms sl2_mem_commutator_f3

end Procesi
