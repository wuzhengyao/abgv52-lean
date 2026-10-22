/-
  Procesi —— **中心多项式值的理想归属**（`cor:11.2.7` 的代数内核）

  **内容**：`A ⊆ M_N(k)` 子代数、`I` 是 `A` 的**双边**理想、`b_i ∈ I`、`D ∈ A`。则
  `formanekEval`／`formanekGGen` 在 `(D, b)` 上的值 = 某个**落在 `I` 里**的 `A` 元素之像。

  **机制**（三层）：
  1. `gPoly` 的系数是整数（`gPoly_coeff_eq_intCast`：`gPoly k N = map (Int.castRingHom k) (gPoly ℤ N)`）；
  2. 单项 `wordA = ∏ i, D^{n i} * b_i` 再右乘 `D^{n N}`：每个因子 `D^{n i} * b_i ∈ I`
     （`I.mul_mem_left`），列表积在 `I` 里（`listProd_mem_twoSidedIdeal`），右乘 `D^{n N}`
     （`I.mul_mem_right`）；整数系数用 `I` 的加法子群性；
  3. 桥：`Subalgebra.val A : ↥A →+* M_N(k)` 是环同态 ⟹ `↑(wordA) = wordOf`（`map_mul`／`map_pow`／
     `map_list_prod`）⟹ `↑(formanekEvalA) = formanekEval`（`map_sum` ＋ `map_intCast` ＋
     `algebraMap c * W = c • W`）。

  由此得 ★★★`exists_scalar_mem_of_ne_bot`：**非零双边理想含非零纯量**（对角元互异的情形），
  **不需要**"中心多项式对任意 `X` 中心"——这是 v48 判读（[[proj-abgv52-frontier-R661]] §103）的落点。
-/

import Procesi.PI.FormanekEval
import Procesi.PI.IdealSpan

open Matrix

namespace Procesi

variable {k : Type*} [Field k] {N : ℕ}
variable {R : Type*} [CommRing R] [Algebra R k]

/-! ## §1 `gPoly` 的系数是整数 -/

/-- `gPoly` 的系数是整数：`(gPoly k N).coeff m = ((gPoly ℤ N).coeff m : k)`。 -/
theorem gPoly_coeff_eq_intCast (m : Fin (N + 1) →₀ ℕ) :
    (gPoly k N).coeff m = (((gPoly ℤ N).coeff m : ℤ) : k) := by
  have h := gPoly_map (K := ℤ) (L := k) (φ := Int.castRingHom k) N
  rw [← h, MvPolynomial.coeff_map]
  rfl

#print axioms gPoly_coeff_eq_intCast

/-! ## §2 双边理想对列表积／有限和的封闭 -/

/-- 非空列表：元素都在双边理想里 ⟹ 积在理想里。 -/
theorem listProd_mem_twoSidedIdeal {A : Type*} [Ring A] (I : TwoSidedIdeal A) :
    ∀ (L : List A), L ≠ [] → (∀ x ∈ L, x ∈ I) → L.prod ∈ I
  | [], hne, _ => absurd rfl hne
  | a :: L, _, hL => by
      rw [List.prod_cons]
      exact I.mul_mem_right a L.prod (hL a (List.mem_cons_self ..))

#print axioms listProd_mem_twoSidedIdeal

/-- 双边理想的有限和封闭。 -/
theorem sum_mem_twoSidedIdeal {A : Type*} [Ring A] (I : TwoSidedIdeal A) {ι : Type*}
    (s : Finset ι) {f : ι → A} (h : ∀ x ∈ s, f x ∈ I) : ∑ x ∈ s, f x ∈ I := by
  classical
  induction s using Finset.induction with
  | empty => simpa using I.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact I.add_mem (h a (Finset.mem_insert_self ..))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

#print axioms sum_mem_twoSidedIdeal

/-! ## §3 `A` 级单项：`wordA` 落在理想里，且强制到矩阵层 = `wordOf` -/

section WordA

variable (A : Subalgebra R (Matrix (Fin N) (Fin N) k))

/-- `A` 级单项（与 `wordOf` 同形）：`∏ i, D^{n i} * b_i` 再右乘 `D^{n N}`。 -/
noncomputable def wordA (D : ↥A) (b : Fin N → ↥A) (nn : ℕ → ℕ) : ↥A :=
  (List.ofFn (fun i : Fin N => D ^ (nn i) * b i)).prod * D ^ (nn N)

#print axioms wordA

/-- ★ `wordA` 落在双边理想里（`b_i ∈ I`）。 -/
theorem wordA_mem (I : TwoSidedIdeal ↥A) (D : ↥A) {b : Fin N → ↥A} (hb : ∀ i, b i ∈ I)
    [NeZero N] (nn : ℕ → ℕ) : wordA A D b nn ∈ I := by
  have hne : (List.ofFn (fun i : Fin N => D ^ (nn i) * b i)) ≠ [] := by
    intro h
    have hlen := List.length_ofFn (f := fun i : Fin N => D ^ (nn i) * b i)
    rw [h] at hlen
    simp at hlen
    exact NeZero.ne N hlen.symm
  exact I.mul_mem_right _ _ <|
    listProd_mem_twoSidedIdeal I _ hne (fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact I.mul_mem_left _ (b i) (hb i))

#print axioms wordA_mem

/-- ★★ **桥**：`wordA` 强制到矩阵层 = `wordOf`。 -/
theorem coe_wordA (D : ↥A) (b : Fin N → ↥A) (nn : ℕ → ℕ) :
    Subalgebra.val A (wordA A D b nn)
      = wordOf N nn (Subalgebra.val A D) (fun i => Subalgebra.val A (b i)) := by
  rw [wordA, wordOf_eq_ofFn, map_mul, map_pow, map_list_prod]
  rw [List.map_ofFn]
  congr 1

#print axioms coe_wordA

/-! ## §4 `formanekEval` 的值 = 某个**落在理想里**的 `A` 元素 -/

/-- `formanekEval` 的元素级版本（系数取整数）。 -/
noncomputable def formanekEvalA (D : ↥A) (b : Fin N → ↥A) : ↥A :=
  ∑ m ∈ (gPoly k N).support,
    ((((gPoly ℤ N).coeff m : ℤ)) : ↥A) *
      wordA A D b (fun i => if h : i < N + 1 then m ⟨i, h⟩ else 0)

#print axioms formanekEvalA

/-- ★★ **`formanekEvalA` 落在理想里**。 -/
theorem formanekEvalA_mem (I : TwoSidedIdeal ↥A) (D : ↥A) {b : Fin N → ↥A}
    (hb : ∀ i, b i ∈ I) [NeZero N] : formanekEvalA A D b ∈ I :=
  sum_mem_twoSidedIdeal I _ (fun m _ =>
    I.mul_mem_left _ _ (wordA_mem A I D hb (fun i => if h : i < N + 1 then m ⟨i, h⟩ else 0)))

#print axioms formanekEvalA_mem

/-- 标量矩阵与纯量乘的桥：`(c : Matrix) * W = c • W`。 -/
theorem intCast_mul_eq_smul (c : k) (W : Matrix (Fin N) (Fin N) k) :
    (algebraMap k (Matrix (Fin N) (Fin N) k) c) * W = c • W := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]

#print axioms intCast_mul_eq_smul

/-- ★★ **桥**：`formanekEvalA` 强制到矩阵层 = `formanekEval`。 -/
theorem coe_formanekEvalA (D : ↥A) (b : Fin N → ↥A) :
    Subalgebra.val A (formanekEvalA A D b)
      = formanekEval N (gPoly k N) (Subalgebra.val A D)
          (fun i => Subalgebra.val A (b i)) := by
  rw [formanekEvalA, formanekEval, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_mul, map_intCast, coe_wordA, gPoly_coeff_eq_intCast]
  exact intCast_mul_eq_smul _ _

#print axioms coe_formanekEvalA

end WordA



/-!
# R771 探针（E 计划装配，第 3 阶段）：**非零双边理想 ∩ 纯量 ≠ 0**

一般形态（`cor:11.2.7` 的代数内核，**不需要**"`G` 对任意 `X` 中心"）：

```
A ⊆ M_N(k) 子代数, span_k A = ⊤, D ∈ A 是对角元互异的对角矩阵, I ⊴ A 非零
  ⟹ ∃ z ∈ I, z ≠ 0, val z = c • 1, c ≠ 0
```

**证明骨架**（本轮判读的施工图）：
1. 反设 `∀ b ∈ I^N, G(D, val b) = 0`；
2. `G(D,·)` 对 `Y` 多线性 ＋ `span I = ⊤`（`span_mul_mul_eq_top`）⟹ `G(D,·) ≡ 0`
   （`MultilinearMap.eq_zero_of_forall_mem_span`）；
3. 与见证 `formanekGGen_units_ne_zero`（链单位族上 `= vanderAll x • 1 ≠ 0`）矛盾；
4. 取见证 `b`，其值 `z = G(D, val b)` 由 `exists_mem_formanekGGen` 落在 `I` 里且非零；
5. 由 C3 ③（`formanekGGen_diagonal_scalar`）`z = c • 1`，`c ≠ 0`。
-/


variable {k : Type*} [Field k] {N : ℕ}
variable {R : Type*} [CommRing R] [Algebra R k]

/-- ★★ **`formanekGGen` 的值 = 某个落在理想里的 `A` 元素**（对旋转求和）。 -/
theorem exists_mem_formanekGGen (A : Subalgebra R (Matrix (Fin N) (Fin N) k))
    [NeZero N] (I : TwoSidedIdeal ↥A) (D : ↥A) (b : Fin N → ↥A) (hb : ∀ i, b i ∈ I) :
    ∃ z : ↥A, z ∈ I ∧ Subalgebra.val A z
      = formanekGGen N (gPoly k N) (Subalgebra.val A D)
          (fun i => Subalgebra.val A (b i)) := by
  classical
  have hrot : ∀ j : Fin N, formanekEvalA A D (fun i : Fin N => b (i + j)) ∈ I :=
    fun j => formanekEvalA_mem A I D (fun i => hb (i + j))
  refine ⟨∑ j : Fin N, formanekEvalA A D (fun i : Fin N => b (i + j)),
    sum_mem_twoSidedIdeal I _ (fun j _ => hrot j), ?_⟩
  rw [formanekGGen, map_sum]
  exact Finset.sum_congr rfl (fun j _ => coe_formanekEvalA A D (fun i : Fin N => b (i + j)))

#print axioms exists_mem_formanekGGen

/-- ★★★ **E 计划主体**：非零双边理想含非零纯量（对角元互异的情形）。 -/
theorem exists_scalar_mem_of_ne_bot (A : Subalgebra R (Matrix (Fin N) (Fin N) k))
    [NeZero N] (hn : 1 ≤ N) {x : Fin N → k} (hx : Function.Injective x)
    (hspanA : Submodule.span k (A : Set (Matrix (Fin N) (Fin N) k)) = ⊤)
    (D : ↥A) (hD : Subalgebra.val A D = Matrix.diagonal x)
    (I : TwoSidedIdeal ↥A) (hI : I ≠ ⊥) :
    ∃ z : ↥A, z ∈ I ∧ z ≠ 0 ∧ ∃ c : k, c ≠ 0 ∧ Subalgebra.val A z = c • (1 : Matrix (Fin N) (Fin N) k) := by
  classical
  -- ① 反设：`I`-元组上 `G(D,·)` 全为零 ⟹ 处处为零 ⟹ 与见证矛盾
  have key : ∃ b : Fin N → ↥A, (∀ i, b i ∈ I) ∧
      formanekGMap N hn (Matrix.diagonal x) (fun i => Subalgebra.val A (b i)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    -- `span I = ⊤`
    have hspanI : Submodule.span k ((fun y : ↥A => (y : Matrix (Fin N) (Fin N) k)) '' (I : Set ↥A))
        = ⊤ := span_mul_mul_eq_top A hspanA I hI
    -- 跨张成
    have hzero : ∀ c : Fin N → Matrix (Fin N) (Fin N) k,
        (∀ i, c i ∈ Submodule.span k ((fun y : ↥A => (y : Matrix (Fin N) (Fin N) k)) '' (I : Set ↥A)))
          → formanekGMap N hn (Matrix.diagonal x) c = 0 := by
      refine MultilinearMap.eq_zero_of_forall_mem_span (f := formanekGMap N hn (Matrix.diagonal x))
        (T := (fun y : ↥A => (y : Matrix (Fin N) (Fin N) k)) '' (I : Set ↥A)) ?_
      intro c hc
      choose a haI haeq using hc
      have hc' : c = fun i => Subalgebra.val A (a i) := funext (fun i => (haeq i).symm)
      rw [hc']
      exact hcon a haI
    -- 见证
    have hwit := hzero (fun i : Fin N => Matrix.single i (i + 1) (1 : k)) (fun i => by
      rw [hspanI]; trivial)
    have hne : formanekGGen N (gPoly k N) (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single i (i + 1) (1 : k)) ≠ 0 :=
      formanekGGen_units_ne_zero N hn hx
    exact hne hwit
  obtain ⟨b, hb, hbne⟩ := key
  -- ② 值落在 `I` 里
  obtain ⟨z, hzI, hz⟩ : ∃ z : ↥A, z ∈ I ∧ Subalgebra.val A z
      = formanekGGen N (gPoly k N) (Subalgebra.val A D)
          (fun i => Subalgebra.val A (b i)) :=
    exists_mem_formanekGGen A I D b hb
  -- ③ `D` 对角 ⟹ 值是纯量
  obtain ⟨c, hc⟩ := formanekGMap_diagonal_scalar N hn x (fun i => Subalgebra.val A (b i))
  have hzval : Subalgebra.val A z = c • (1 : Matrix (Fin N) (Fin N) k) := by
    rw [hz, hD]
    exact hc
  have hbridge : formanekGMap N hn (Matrix.diagonal x) (fun i => Subalgebra.val A (b i))
      = Subalgebra.val A z := by
    rw [hz, hD]
    rfl
  refine ⟨z, hzI, ?_, c, ?_, hzval⟩
  · -- `z ≠ 0`：其强制值 ≠ 0
    intro hz0
    apply hbne
    rw [hbridge, hz0, map_zero]
  · -- `c ≠ 0`：否则纯量矩阵为 0
    intro hc0
    apply hbne
    rw [hbridge, hzval, hc0, zero_smul]

#print axioms exists_scalar_mem_of_ne_bot



end Procesi
