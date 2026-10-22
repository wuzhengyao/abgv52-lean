/-
  Procesi —— **E 计划的一般代数件**（`cor:11.2.7` 的装配骨架）

  **用途（判读见 [[proj-abgv52-frontier-R661]] §103）**：AGPR2020 `cor:11.2.7`
  （"非零双边理想 ∩ 中心 ≠ 0"）在本工程的 `K'` 世界里可以**不用** "`X` 归约到对角"：
  把中心多项式 `G` 的 `X` 槽固定为 `xdiag` 的像（对角、对角元互异），`Y` 槽取理想中元素，
  则每个单项含 `Y` 因子 ⟹ 值落在双边理想里。本件只放**与本工程无关**的两条一般引理：

  1. `MultilinearMap.eq_zero_of_forall_mem_span`（**跨张成**）：多线性映射在 `T`-元组上为零
     ⟹ 在 `span T`-元组上为零。入口 = `Submodule.mem_span_iff_exists_finset_subset`
     （`Finsupp/LinearCombination.lean:458`）＋ `map_sum_finset` ＋ `map_smul_univ`。
  2. `single_eq_smul_single_mul_mul_single` ＋ ★`span_mul_mul_eq_top`（**理想的张成**）：
     `A ⊆ M_n(k)` 且 `span_k A = ⊤`、`I` 是 `A` 的非零**双边**理想 ⟹ `span_k I = ⊤`。
     机制：`E_ij = (a_pq)⁻¹ • (E_ip · a · E_qj)`（任一非零元 `a` 生成全部矩阵单位）＋
     `span_k A = ⊤` ⟹ `span_k I` 对**任意**矩阵左右乘封闭 ⟹ 含全部矩阵单位。

  **范畴约定**：非交换环的双边理想是 `TwoSidedIdeal`（`Ideal` 只对交换环）。
-/

import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.SimpleRing.Basic

namespace Procesi
open Matrix

variable {k : Type*} [Field k]
variable {R : Type*} [CommRing R] [Algebra R k]

/-! ## §1 多线性映射：`T`-元组上为零 ⟹ `span T`-元组上为零 -/

theorem MultilinearMap.eq_zero_of_forall_mem_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Type*} [AddCommGroup M] [Module k M] {M₂ : Type*} [AddCommGroup M₂] [Module k M₂]
    (f : MultilinearMap k (fun _ : ι => M) M₂) {T : Set M}
    (hf : ∀ b : ι → M, (∀ i, b i ∈ T) → f b = 0) :
    ∀ b : ι → M, (∀ i, b i ∈ Submodule.span k T) → f b = 0 := by
  classical
  intro b hb
  choose g tg hgt _ hgsum using fun i =>
    (Submodule.mem_span_iff_exists_finset_subset.mp (hb i))
  have hb' : b = fun i => ∑ a ∈ tg i, g i a • a := by
    funext i
    exact (hgsum i).symm
  rw [hb', MultilinearMap.map_sum_finset]
  refine Finset.sum_eq_zero (fun r hr => ?_)
  rw [MultilinearMap.map_smul_univ]
  have hzero : f (fun i => r i) = 0 := by
    refine hf _ (fun i => ?_)
    exact hgt i ((Fintype.mem_piFinset.mp hr) i)
  rw [hzero, smul_zero]

#print axioms MultilinearMap.eq_zero_of_forall_mem_span

/-! ## §2 矩阵单位由任一非零矩阵生成 -/

/-- `single a b c = c • single a b 1`（本件的局部小件）。 -/
theorem matrix_single_eq_smul_one {n : ℕ} (a b : Fin n) (c : k) :
    Matrix.single a b c = c • Matrix.single a b (1 : k) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

#print axioms matrix_single_eq_smul_one

/-- **矩阵单位生成式**：`E_ij = (a_pq)⁻¹ • (E_ip · a · E_qj)`（`a_pq ≠ 0`）。 -/
theorem single_eq_smul_single_mul_mul_single {n : ℕ} (a : Matrix (Fin n) (Fin n) k)
    {p q : Fin n} (hpq : a p q ≠ 0) (i j : Fin n) :
    Matrix.single i j (1 : k)
      = (a p q)⁻¹ • (Matrix.single i p (1 : k) * a * Matrix.single q j (1 : k)) := by
  rw [Matrix.single_mul_mul_single, one_mul, mul_one]
  conv_rhs => rw [matrix_single_eq_smul_one]
  rw [smul_smul, inv_mul_cancel₀ hpq, one_smul]

#print axioms single_eq_smul_single_mul_mul_single

/-! ## §3 非零双边理想的 `k`-张成 = `⊤` -/

section IdealSpan

variable {n : ℕ}

/-- ★★ **非零双边理想的张成是 `⊤`**：`A ⊆ M_n(k)`、`span_k A = ⊤`、`I ≠ ⊥`（`A` 的双边理想）
⟹ `span_k I = ⊤`。 -/
theorem span_mul_mul_eq_top (A : Subalgebra R (Matrix (Fin n) (Fin n) k))
    (hA : Submodule.span k (A : Set (Matrix (Fin n) (Fin n) k)) = ⊤)
    (I : TwoSidedIdeal A) (hI : I ≠ ⊥) :
    Submodule.span k ((fun x : A => (x : Matrix (Fin n) (Fin n) k)) '' (I : Set A)) = ⊤ := by
  classical
  set S : Submodule k (Matrix (Fin n) (Fin n) k) :=
    Submodule.span k ((fun x : A => (x : Matrix (Fin n) (Fin n) k)) '' (I : Set A)) with hS
  -- `I ≠ ⊥` ⟹ 有非零元
  obtain ⟨a, haI, ha0⟩ : ∃ a : A, a ∈ I ∧ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hI (SetLike.ext fun x => by
      constructor
      · intro hx
        exact h x hx
      · intro hx
        rw [show x = 0 from hx]
        exact I.zero_mem)
  -- ① `S` 对 `A` 的左乘封闭
  have hleft : ∀ (u : A) {x : Matrix (Fin n) (Fin n) k}, x ∈ S →
      (u : Matrix (Fin n) (Fin n) k) * x ∈ S := by
    intro u x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hvI, rfl⟩ := hy
      exact Submodule.subset_span ⟨u * v, I.mul_mem_left (u : A) v hvI, rfl⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem S
    | add y z _ _ hy hz => rw [mul_add]; exact S.add_mem hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact S.smul_mem c hy
  -- ② `S` 对 `A` 的右乘封闭
  have hright : ∀ (u : A) {x : Matrix (Fin n) (Fin n) k}, x ∈ S →
      x * (u : Matrix (Fin n) (Fin n) k) ∈ S := by
    intro u x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hvI, rfl⟩ := hy
      exact Submodule.subset_span ⟨v * u, I.mul_mem_right v (u : A) hvI, rfl⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem S
    | add y z _ _ hy hz => rw [add_mul]; exact S.add_mem hy hz
    | smul c y _ hy => rw [Matrix.smul_mul]; exact S.smul_mem c hy
  -- ③ 对**任意**矩阵的左乘封闭（用 `span A = ⊤`）
  have hleftAll : ∀ (u : Matrix (Fin n) (Fin n) k) {x}, x ∈ S → u * x ∈ S := by
    intro u x hx
    have hu : u ∈ Submodule.span k (A : Set (Matrix (Fin n) (Fin n) k)) := by rw [hA]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy => exact hleft ⟨y, hy⟩ hx
    | zero => rw [zero_mul]; exact Submodule.zero_mem S
    | add y z _ _ hy hz => rw [add_mul]; exact S.add_mem hy hz
    | smul c y _ hy => rw [Matrix.smul_mul]; exact S.smul_mem c hy
  -- ④ 对**任意**矩阵的右乘封闭
  have hrightAll : ∀ (u : Matrix (Fin n) (Fin n) k) {x}, x ∈ S → x * u ∈ S := by
    intro u x hx
    have hu : u ∈ Submodule.span k (A : Set (Matrix (Fin n) (Fin n) k)) := by rw [hA]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy => exact hright ⟨y, hy⟩ hx
    | zero => rw [mul_zero]; exact Submodule.zero_mem S
    | add y z _ _ hy hz => rw [mul_add]; exact S.add_mem hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact S.smul_mem c hy
  -- ⑤ `a ∈ S`
  have haS : (a : Matrix (Fin n) (Fin n) k) ∈ S := Submodule.subset_span ⟨a, haI, rfl⟩
  -- ⑥ 矩阵单位 ⟹ `S = ⊤`
  have hunit : ∀ i j : Fin n, Matrix.single i j (1 : k) ∈ S := by
    rcases isEmpty_or_nonempty (Fin n) with hemp | hne
    · haveI := hemp
      intro i
      exact isEmptyElim i
    · haveI := hne
      have hex : ∃ p q : Fin n, (a : Matrix (Fin n) (Fin n) k) p q ≠ 0 := by
        by_contra h
        push_neg at h
        refine ha0 (Subtype.ext ?_)
        exact Matrix.ext fun p q => by simpa using h p q
      obtain ⟨p, q, hpq⟩ := hex
      intro i j
      have hgen : Matrix.single i j (1 : k)
          = ((a : Matrix (Fin n) (Fin n) k) p q)⁻¹ •
              (Matrix.single i p (1 : k) * (a : Matrix (Fin n) (Fin n) k)
                * Matrix.single q j (1 : k)) :=
        single_eq_smul_single_mul_mul_single (a : Matrix (Fin n) (Fin n) k) hpq i j
      rw [hgen]
      refine S.smul_mem _ ?_
      exact hrightAll _ (hleftAll _ haS)
  rw [Submodule.eq_top_iff']
  intro x
  have hx : (∑ i : Fin n, ∑ j : Fin n, x i j • Matrix.single i j (1 : k)) = x := by
    rw [show (∑ i : Fin n, ∑ j : Fin n, x i j • Matrix.single i j (1 : k))
        = ∑ i : Fin n, ∑ j : Fin n, Matrix.single i j (x i j) from by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      exact (matrix_single_eq_smul_one i j (x i j)).symm]
    exact Matrix.sum_sum_single (fun i j => x i j)
  rw [← hx]
  exact S.sum_mem (fun i _ => S.sum_mem (fun j _ => S.smul_mem _ (hunit i j)))

#print axioms span_mul_mul_eq_top

end IdealSpan

end Procesi
