/-
  Procesi —— **PI 基础设施（S2b-3）：`formanekEval` 在测试族上的值**

  **内容**（AGPR2020 `thm:10.2.4` 证明的第二、三步）：`X = diag x`、`Y_k = E_{p k, p(k+1)}` 时

  ```
  formanekEval g (diag x) Y = E_{p 0, p N} ( g.eval (x ∘ p) )
  ```

  即"交换伴随在测试族上 = 把每个单项的指数代回 `x ∘ p`"；把它对各平移 `j` 求和
  （`formanekG`），在 `p` 周期且前 `N` 项互异时即得 `G = Δ² • 1`
  （`formanekG_eq_smul`，`Δ² = vanderAll x`）。

  **依赖的两条线性律**：`r • E_{ij}(c) = E_{ij}(r * c)`（`smul_single'`）与
  `Σ E_{ij}(f m) = E_{ij}(Σ f m)`（`sum_single'`）；求值侧用 `MvPolynomial.eval_eq'`
  与 `Fin.prod_univ_eq_prod_range`。

  **✓ 载体状态（L12／L39，2026-10-22）**：陈述与证明已回 `raw/AGPR2020.pdf` **目视核**
  （印刷页 270–271 ＝ PDF 页 280–281）：`eq:10.3` 的**两支**（链条件／否则 0）、
  `eq:10.5` 的因子范围 `2≤i≤n`、`2≤i<j≤n`、`thm:10.2.4` 的证明（"`h_1,…,h_n` 互异且 `k_n=h_1`"
  ＋ 各平移项求和）**逐字一致，无截支**。

  **R768 增补（工序 C3 ③）**：
  * **逐坐标线性**：`update_same'`／`update_noteq'`／`ofFn_update_set`／
    `wordOf_update_add`／`wordOf_update_smul`／`formanekEval_update_add`／`formanekEval_update_smul`／
    `rot_update`／`formanekGGen_update_add`／`formanekGGen_update_smul`／
    ★**`formanekGMap`**（`G`（任意 `Y`）作为 `MultilinearMap`）。
  * ★★**`Y` 放开到任意矩阵**（`X` 仍对角）：`matrix_eq_sum_units`／`single_eq_smul_one`／
    `formanekGGen_units_coeff`／`smul_ite_smul_one`／★★**`formanekGMap_diagonal_scalar`** ＋
    `formanekGGen_diagonal_scalar`。
  * ★★**非零性（工序 D 的一半）**：`vanderAll_ne_zero`／
    `formanekGGen_units_eq_vanderAll_of_injective`／**`formanekGGen_units_ne_zero`**
    （`G` 不在 `n×n` 矩阵上是零多项式 ⟹ 中心多项式的"非零"要求，`X` 仍对角）。
  * ★★**共轭协变（工序 C3 ① 的第一块）**：`conjRingHom`（`X ↦ P X P'` 做成 `RingHom`）／
    `conjRingHom_apply`／`conj_pow`／`prod_map_conj`／**`wordOf_conj`**／
    **`formanekEval_conj`**／★★**`formanekGGen_conj`**／`conj_scalar`（纯量性共轭不变）。
  * ★★**系数环同态搬运（基变换）**：`gPoly_map`（`gPoly` 只由 `X` 与算术构成）／
    `wordOf_mapMatrix`／`mapMatrix_smul`（`RingHom` 非 `AlgHom`，无现成 `map_smul`）／
    **`formanekEval_mapMatrix`**／**`formanekGGen_mapMatrix`**。

  **R767 增补（工序 C3 之桥）**：`wordOf_eq_ofFn` —— `wordOf` 的 `List.ofFn` 形式
  （`Fin N` 自然次序的非交换积；为逐坐标线性化铺路）。

  **R766 增补（工序 C2b 收口）**：`neg_one_add`／`chain_all_edges`（端边推导）／
  ★★★**`formanekGGen_units_eq`** —— **`G` 在任意矩阵单位族上的值**
  （全边成立且 `h` 单射 ⟹ `vanderAll x • 1`，否则 `0`）。

  **R765 增补（工序 C2b-2 之运输层）**：`ℕ`-索引旋转序列 `rotH`／`rotK` ＋
  **★`formanekEval_rot`**（`formanekEval` 在旋转单位族上的值 = 链条件成立时的
  `single (h j) (k (j-1)) (g.eval yj)`）＋ 端点／零点／`Fin`-对照小件。

  **R764 增补（工序 C2b-2 之序列层）**：旋转测试序列 `yj`（`Fin (N+1)` 索引：位置 `s` 取
  `x (h (s + j))`，末端取 `x (k (j-1))`）＋ 四条求值律：
  `yj_eq_of_h_eq`（`h` 相等 ⟹ 两位置同值）／`gPoly_eval_yj_eq_zero_of_not_injective`（非单射 ⟹ `0`）／
  `gPoly_eval_yj_eq_zero_of_endpoint_ne`（单射 ＋ 末项不闭合 ⟹ `0`）／
  `gPoly_eval_yj_eq_vanderAll`（单射 ＋ 末项闭合 ⟹ `Δ²`）。

  **R763 增补（工序 C2b-1）**：一般形态 `formanekGGen`（任意 `Y`）＋"全边成立"支：
  `formanekGGen_units_all_edges`（值 = `Δ² • 1` 或 `0`，归约到 `formanekG_eq_ite`）；
  辅助 `fin_val_add_one`。

  **R762 增补（工序 C2a）**：任意矩阵单位的求值（`eq:10.3` 的完整两支）：
  `prod_units_ite`（`m+1` 个任意单位之积 = 链条件成立时的单个单位，否则 `0`）／
  `wordOf_units`／**`formanekEval_units`**（非链 ⟹ `φ = 0`；链支复用 `formanekEval_chain`）。

  **R761 增补（工序 B′）**：非单射分支（"`h_1,…,h_n` 不互异 ⟹ `g = 0`"）：
  `vanderAll_eq_zero_of_not_injective`／`vanderAll_shift_eq_zero_of_not_injective`
  （`p` 周期且非单射）／`formanekG_eq_zero_of_not_injective`，合取形态 `formanekG_eq_ite`。
-/

import Procesi.PI.ChainProd
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Multilinear.Basic

namespace Procesi

open Matrix

variable {K : Type*} [CommRing K] {N : ℕ}

/-- `r • E_{ij}(c) = E_{ij}(r * c)`。 -/
theorem smul_single' (i j : Fin N) (r c : K) :
    r • Matrix.single i j c = Matrix.single i j (r * c) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.single, Matrix.of_apply]
  split_ifs <;> simp

#print axioms smul_single'

/-- `Σ_m E_{ij}(f m) = E_{ij}(Σ_m f m)`。 -/
theorem sum_single' {ι : Type*} (s : Finset ι) (f : ι → K) (i j : Fin N) :
    (∑ m ∈ s, Matrix.single i j (f m)) = Matrix.single i j (∑ m ∈ s, f m) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Matrix.single_add]

#print axioms sum_single'

/-- ★★★★★★★ **`formanekEval` 的链式求值**：`X = diag x`、`Y_k = E_{p k, p(k+1)}`（`N ≥ 1`）时
`formanekEval g = E_{p 0, p N}(g.eval (x ∘ p))`。 -/
theorem formanekEval_chain (hN : 1 ≤ N) (g : MvPolynomial (Fin (N + 1)) K)
    (x : Fin N → K) (p : ℕ → Fin N) :
    formanekEval N g (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single (p i) (p ((i : ℕ) + 1)) 1)
      = Matrix.single (p 0) (p N) ((MvPolynomial.eval (fun i : Fin (N + 1) => x (p i))) g) := by
  rw [formanekEval]
  have hterm : ∀ m ∈ g.support,
      g.coeff m • wordOf (K := K) N (fun k => if h : k < N + 1 then m ⟨k, h⟩ else 0)
        (Matrix.diagonal x) (fun i : Fin N => Matrix.single (p i) (p ((i : ℕ) + 1)) 1)
      = Matrix.single (p 0) (p N) (g.coeff m * ∏ k ∈ Finset.range (N + 1),
          (x (p k)) ^ (if h : k < N + 1 then m ⟨k, h⟩ else 0)) := by
    intro m _
    rw [wordOf_chain N hN (fun k => if h : k < N + 1 then m ⟨k, h⟩ else 0) x p]
    ext a b
    simp only [Matrix.smul_apply, Matrix.single, Matrix.of_apply]
    split_ifs <;> simp [mul_assoc]
  rw [Finset.sum_congr rfl hterm, sum_single']
  congr 1
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  rw [← Fin.prod_univ_eq_prod_range
    (fun k => (x (p k)) ^ (if h : k < N + 1 then m ⟨k, h⟩ else 0)) (N + 1)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi : (⟨(i : ℕ), i.isLt⟩ : Fin (N + 1)) = i := Fin.ext rfl
  simp only [dif_pos i.isLt, hi]

#print axioms formanekEval_chain

/-- **任意矩阵单位之积**：`m+1` 个因子 `E_{h (a+t), k (a+t)}(c (a+t))` 的积
= 若链条件 `k (a+t) = h (a+t+1)`（`t<m`）成立则收敛成 `E_{h a, k (a+m)}(∏ c)`，否则 `0`。 -/
theorem prod_units_ite (h k : ℕ → Fin N) (c : ℕ → K) (a m : ℕ) :
    ((List.range (m + 1)).map (fun t =>
        Matrix.single (h (a + t)) (k (a + t)) (c (a + t)))).prod
      = if (∀ t, t < m → k (a + t) = h (a + t + 1)) then
          Matrix.single (h a) (k (a + m)) (∏ t ∈ Finset.range (m + 1), c (a + t))
        else 0 := by
  induction m generalizing a with
  | zero =>
    simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_singleton, List.prod_singleton]
    by_cases hchain : ∀ t, t < m → k (a + t) = h (a + t + 1)
    · rw [if_pos hchain]
      by_cases hedge : k (a + m) = h (a + m + 1)
      · have hnew : ∀ t, t < m + 1 → k (a + t) = h (a + t + 1) := by
          intro t ht
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
          · exact hchain t h'
          · rw [h']; exact hedge
        have harg : a + (m + 1) = a + m + 1 := by omega
        rw [if_pos hnew, harg, ← hedge, Matrix.single_mul_single_same]
        conv_rhs => rw [Finset.prod_range_succ]
        rw [harg]
      · have hnew : ¬ ∀ t, t < m + 1 → k (a + t) = h (a + t + 1) := by
          intro hc
          exact hedge (hc m (Nat.lt_succ_self m))
        rw [if_neg hnew]
        have hmism : k (a + m) ≠ h (a + (m + 1)) := hedge
        rw [Matrix.single_mul_single_of_ne (h := hmism)]
    · have hnew : ¬ ∀ t, t < m + 1 → k (a + t) = h (a + t + 1) := by
        intro hc
        exact hchain (fun t ht => hc t (Nat.lt_succ_of_lt ht))
      rw [if_neg hnew, if_neg hchain, zero_mul]

#print axioms prod_units_ite

/-- **任意矩阵单位的词求值**（`eq:10.3` 的两支）：`X` 对角、`Y_k = E_{h k, k k}` 时，
`wordOf` = 链条件成立时的单个矩阵单位（系数含两端幂积），否则 `0`。 -/
theorem wordOf_units (N : ℕ) (hN : 1 ≤ N) (n : ℕ → ℕ) (x : Fin N → K)
    (h k : ℕ → Fin N) :
    wordOf (K := K) N n (Matrix.diagonal x) (fun i : Fin N => Matrix.single (h i) (k i) 1)
      = if (∀ t, t < N - 1 → k t = h (t + 1)) then
          Matrix.single (h 0) (k (N - 1))
            (∏ t ∈ Finset.range (N + 1),
              (if t < N then x (h t) else x (k (N - 1))) ^ (n t))
        else 0 := by
  rw [wordOf]
  have hfac : ∀ t ∈ List.range N,
      (if hh : t < N then (Matrix.diagonal x) ^ (n t) *
          (fun i : Fin N => Matrix.single (h i) (k i) 1) ⟨t, hh⟩ else 1)
      = Matrix.single (h t) (k t) ((x (h t)) ^ (n t)) := by
    intro t ht
    have hlt : t < N := List.mem_range.mp ht
    rw [dif_pos hlt, diagonal_pow_mul_single, mul_one]
  rw [List.map_congr_left hfac]
  have hNm : N - 1 + 1 = N := by omega
  have hprod := prod_units_ite (K := K) h k (fun t => (x (h t)) ^ (n t)) 0 (N - 1)
  simp only [Nat.zero_add, hNm] at hprod
  rw [hprod]
  by_cases hch : ∀ t, t < N - 1 → k t = h (t + 1)
  · rw [if_pos hch, if_pos hch]
    have hcoef : (∏ t ∈ Finset.range N, (x (h t)) ^ (n t)) * (x (k (N - 1))) ^ (n N)
        = ∏ t ∈ Finset.range (N + 1),
            (if t < N then x (h t) else x (k (N - 1))) ^ (n t) := by
      rw [Finset.prod_range_succ]
      congr 1
      · exact Finset.prod_congr rfl (fun t ht => by
          rw [if_pos (List.mem_range.mp ht)])
      · rw [if_neg (Nat.lt_irrefl N)]
    rw [single_mul_diagonal_pow, hcoef]
  · rw [if_neg hch, if_neg hch, zero_mul]

#print axioms wordOf_units

/-- **任意矩阵单位的 `formanekEval`**（`eq:10.3`＋`eq:10.4`）：
`X` 对角、`Y_i = E_{h i,k i}` 时，`φ` = 链条件成立时的 `E_{h 0,k(N-1)}(g.eval …)`，否则 `0`。 -/
theorem formanekEval_units (N : ℕ) (hN : 1 ≤ N) (g : MvPolynomial (Fin (N + 1)) K)
    (x : Fin N → K) (h k : ℕ → Fin N) :
    formanekEval N g (Matrix.diagonal x) (fun i : Fin N => Matrix.single (h i) (k i) 1)
      = if (∀ t, t < N - 1 → k t = h (t + 1)) then
          Matrix.single (h 0) (k (N - 1))
            ((MvPolynomial.eval (fun i : Fin (N + 1) =>
              if (i : ℕ) < N then x (h i) else x (k (N - 1)))) g)
        else 0 := by
  by_cases hch : ∀ t, t < N - 1 → k t = h (t + 1)
  · rw [if_pos hch]
    -- 链支：定义 `p`，用 `formanekEval_chain`
    let p : ℕ → Fin N := fun t => if t < N then h t else k (N - 1)
    have hY : (fun i : Fin N => Matrix.single (h i) (k i) (1 : K))
        = fun i : Fin N => Matrix.single (p i) (p ((i : ℕ) + 1)) (1 : K) := by
      funext i
      have hi : (i : ℕ) < N := i.isLt
      have hp : p (i : ℕ) = h i := if_pos hi
      have hp1 : p ((i : ℕ) + 1) = k i := by
        rcases Nat.lt_or_ge ((i : ℕ) + 1) N with hlt | hge
        · have hki : k i = h ((i : ℕ) + 1) := hch i (by omega)
          rw [show p ((i : ℕ) + 1) = h ((i : ℕ) + 1) from if_pos hlt, ← hki]
        · have hie : (i : ℕ) = N - 1 := by omega
          rw [show p ((i : ℕ) + 1) = k (N - 1) from if_neg (by omega), hie]
      rw [hp, hp1]
    rw [hY, formanekEval_chain hN g x p]
    rw [show p 0 = h 0 from if_pos (by omega : 0 < N)]
    rw [show p N = k (N - 1) from if_neg (Nat.lt_irrefl N)]
    have hF : (fun i : Fin (N + 1) => x (p (i : ℕ)))
        = (fun i : Fin (N + 1) =>
            if (i : ℕ) < N then x (h (i : ℕ)) else x (k (N - 1))) := by
      funext i
      simp only [p]
      by_cases hi : (i : ℕ) < N <;> simp [hi]
    rw [hF]
  · rw [if_neg hch]
    rw [formanekEval]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    rw [wordOf_units N hN (fun k' => if hh : k' < N + 1 then m ⟨k', hh⟩ else 0) x h k,
      if_neg hch, smul_zero]

#print axioms formanekEval_units

/-- **置换的对角和**：`Σ_j E_{h j, h j}(c) = c • 1`（`h` 为置换）。 -/
theorem sum_diag_of_perm [NeZero N] (h : Equiv.Perm (Fin N)) (c : K) :
    (∑ j : Fin N, Matrix.single (h j) (h j) c) = c • (1 : Matrix (Fin N) (Fin N) K) := by
  have h1 : (∑ j : Fin N, Matrix.single (h j) (h j) c)
      = ∑ i : Fin N, Matrix.single i i c := by
    refine Finset.sum_bij (fun j _ => h j) ?_ ?_ ?_ ?_
    · intro j _; exact Finset.mem_univ _
    · intro a _ b _ hab; exact h.injective hab
    · intro i _; exact ⟨h.symm i, Finset.mem_univ _, h.apply_symm_apply i⟩
    · intro j _; rfl
  rw [h1, Matrix.sum_single_eq_diagonal]
  ext i j'
  rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

#print axioms sum_diag_of_perm

/-- `Fin N` 上的**加法平移是置换**（`σ_j i := i + j`）。 -/
noncomputable def shiftEquiv (N : ℕ) [NeZero N] (j : Fin N) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (· + j)
    ⟨fun a b h => add_right_cancel h,
     Finite.injective_iff_surjective.mp (fun a b h => add_right_cancel h)⟩

#print axioms shiftEquiv

/-- **`G`（AGPR `thm:10.2.4`）**：`N` 个循环平移的 Formanek 伴随之和。
`p : ℕ → Fin N` 给出链指标；第 `j` 个平移项把 `Y i` 取作 `E_{p (i+j), p (i+j+1)}`。 -/
noncomputable def formanekG (N : ℕ) (g : MvPolynomial (Fin (N + 1)) K)
    (X : Matrix (Fin N) (Fin N) K) (p : ℕ → Fin N) : Matrix (Fin N) (Fin N) K :=
  ∑ j : Fin N, formanekEval N g X
    (fun i : Fin N => Matrix.single (p ((i : ℕ) + (j : ℕ))) (p ((i : ℕ) + (j : ℕ) + 1)) 1)

/-- **`G` 的单项**（工序 B 第一步）：第 `j` 个平移项在测试族上的值。 -/
theorem formanekEval_shift_term (hN : 1 ≤ N) (x : Fin N → K) (p : ℕ → Fin N)
    (hper : ∀ k, p (k + N) = p k) (j : Fin N) :
    formanekEval N (gPoly K N) (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single (p ((i : ℕ) + (j : ℕ))) (p (((i : ℕ) + 1) + (j : ℕ))) 1)
      = Matrix.single (p j) (p j)
          (deltaSq N (fun k : Fin (N + 1) => x (p ((k : ℕ) + (j : ℕ))))) := by
  rw [formanekEval_chain hN (gPoly K N) x (fun k => p (k + (j : ℕ)))]
  -- `q j 0 = p j`，`q j N = p (N + j) = p j`
  have h0 : p (0 + (j : ℕ)) = p j := by rw [Nat.zero_add]
  have hN' : p (N + (j : ℕ)) = p j := by
    rw [Nat.add_comm]; exact hper j
  rw [h0, hN']
  congr 1
  -- `g.eval (x ∘ q_j) = deltaSq`，用端点恒等式（`z N = z 0`）
  rw [gPoly_eval_of_last_eq]
  congr 1
  simp only [Fin.val_last, Fin.val_zero, Nat.zero_add]
  rw [Nat.add_comm N (j : ℕ), hper j]

#print axioms formanekEval_shift_term

/-- 周期函数在模 `N` 处取值不变：`p m = p (m % N)`（`p` 以 `N` 为周期）。 -/
theorem p_eq_mod {N : ℕ} {p : ℕ → Fin N} (hper : ∀ k, p (k + N) = p k) (m : ℕ) :
    p m = p (m % N) :=
  ((show Function.Periodic p N from hper).map_mod_nat m).symm

#print axioms p_eq_mod

/-- **平移不变性**：`p` 周期且在前 `N` 项上单射时，`Vandermonde` 平方在平移 `i ↦ i + j`
下不变（AGPR `thm:10.2.4` 证明的"各平移项同理"一步）。 -/
theorem vanderAll_shift_of_periodic {N : ℕ} [NeZero N] (x : Fin N → K) (p : ℕ → Fin N)
    (hper : ∀ k, p (k + N) = p k) (hinj : Function.Injective fun i : Fin N => p i)
    (j : Fin N) :
    vanderAll N (fun i : Fin N => x (p ((i : ℕ) + (j : ℕ)))) = vanderAll N x := by
  have hσ : ∀ i : Fin N, (((shiftEquiv N j) i : Fin N) : ℕ) = ((i : ℕ) + (j : ℕ)) % N := by
    intro i
    simp only [shiftEquiv]
    exact Fin.val_add i j
  have hfun : (fun i : Fin N => x (p (((shiftEquiv N j) i : Fin N) : ℕ)))
      = (fun i : Fin N => x (p ((i : ℕ) + (j : ℕ)))) := by
    funext i
    rw [hσ i, ← p_eq_mod hper]
  rw [← hfun]
  change vanderAll N (fun i : Fin N => (fun a : Fin N => x (p (a : ℕ))) ((shiftEquiv N j) i))
    = vanderAll N x
  have hperm := vanderAll_comp_perm (N := N) (fun a : Fin N => x (p (a : ℕ))) (shiftEquiv N j)
  rw [hperm]
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective (fun i : Fin N => p i)
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  exact vanderAll_comp_perm N x σ

#print axioms vanderAll_shift_of_periodic

/-- ★ ★ **工序 B 收口**：`G = Δ² • 1` 在测试族（`X` 对角、`Y_i` 沿以 `p` 为指标的周期全循环）。
对应 AGPR `thm:10.2.4` 证明的最后一步：`G ↦ Δ² Σ_h e_{h,h} = Δ² · 1_n`（印刷页 271）。 -/
theorem formanekG_eq_smul [NeZero N] (x : Fin N → K) (p : ℕ → Fin N)
    (hper : ∀ k, p (k + N) = p k) (hinj : Function.Injective fun i : Fin N => p i) :
    formanekG N (gPoly K N) (Matrix.diagonal x) p = vanderAll N x • 1 := by
  have hN : 1 ≤ N := Nat.pos_of_ne_zero NeZero.out
  rw [formanekG]
  have hterm : ∀ j : Fin N, formanekEval N (gPoly K N) (Matrix.diagonal x)
      (fun i : Fin N => Matrix.single (p ((i : ℕ) + (j : ℕ))) (p ((i : ℕ) + (j : ℕ) + 1)) (1 : K))
      = Matrix.single (p j) (p j) (vanderAll N x) := by
    intro j
    have hfam : (fun i : Fin N =>
        Matrix.single (p ((i : ℕ) + (j : ℕ))) (p ((i : ℕ) + (j : ℕ) + 1)) (1 : K))
        = fun i : Fin N =>
          Matrix.single (p ((i : ℕ) + (j : ℕ))) (p (((i : ℕ) + 1) + (j : ℕ))) (1 : K) := by
      funext i
      rw [show ((i : ℕ) + (j : ℕ) + 1) = (((i : ℕ) + 1) + (j : ℕ)) from by omega]
    rw [hfam, formanekEval_shift_term hN x p hper j]
    congr 1
    rw [deltaSq_eq_vanderAll]
    exact vanderAll_shift_of_periodic x p hper hinj j
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective (fun i : Fin N => p i)
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have h := sum_diag_of_perm (K := K) σ (vanderAll N x)
  exact h

#print axioms formanekG_eq_smul

/-- 非单射 ⟹ `vanderAll = 0`（对形式中必有一个因子 `(y i - y j)^2 = 0`）。 -/
theorem vanderAll_eq_zero_of_not_injective {N : ℕ} (y : Fin N → K)
    (h : ¬ Function.Injective y) : vanderAll N y = 0 := by
  rw [vanderAll_eq_pair]
  by_contra hne
  apply h
  intro a b hab
  by_contra hab'
  apply hne
  rcases lt_or_gt_of_ne hab' with hlt | hgt
  · refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ (a, b), hlt⟩) ?_
    rw [hab, sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  · refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ (b, a), hgt⟩) ?_
    rw [← hab, sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0)]

#print axioms vanderAll_eq_zero_of_not_injective

/-- 平移情形：`p` 周期且非单射 ⟹ 平移后的 `vanderAll` 也为 `0`。 -/
theorem vanderAll_shift_eq_zero_of_not_injective {N : ℕ} [NeZero N] (x : Fin N → K)
    (p : ℕ → Fin N) (hper : ∀ k, p (k + N) = p k)
    (hinj : ¬ Function.Injective fun i : Fin N => p i) (j : Fin N) :
    vanderAll N (fun i : Fin N => x (p ((i : ℕ) + (j : ℕ)))) = 0 := by
  have hσ : ∀ i : Fin N, (((shiftEquiv N j) i : Fin N) : ℕ) = ((i : ℕ) + (j : ℕ)) % N := by
    intro i
    simp only [shiftEquiv]
    exact Fin.val_add i j
  have hfun : (fun i : Fin N => x (p (((shiftEquiv N j) i : Fin N) : ℕ)))
      = (fun i : Fin N => x (p ((i : ℕ) + (j : ℕ)))) := by
    funext i
    rw [hσ i, ← p_eq_mod hper]
  rw [← hfun]
  have hperm := vanderAll_comp_perm (N := N) (fun a : Fin N => x (p (a : ℕ))) (shiftEquiv N j)
  rw [hperm]
  refine vanderAll_eq_zero_of_not_injective (fun a : Fin N => x (p (a : ℕ))) ?_
  intro hc
  exact hinj (fun a b hab => hc (congrArg x hab))

#print axioms vanderAll_shift_eq_zero_of_not_injective

/-- **工序 B′（非单射分支）**：`p` 周期但前 `N` 项不互异 ⟹ `G = 0`
（AGPR `thm:10.2.4` 证明："`g = 0` unless `h_1,…,h_n` are all distinct"，印刷页 271）。 -/
theorem formanekG_eq_zero_of_not_injective {N : ℕ} [NeZero N] (x : Fin N → K)
    (p : ℕ → Fin N) (hper : ∀ k, p (k + N) = p k)
    (hinj : ¬ Function.Injective fun i : Fin N => p i) :
    formanekG N (gPoly K N) (Matrix.diagonal x) p = 0 := by
  have hN : 1 ≤ N := Nat.pos_of_ne_zero NeZero.out
  rw [formanekG]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hfam : (fun i : Fin N =>
      Matrix.single (p ((i : ℕ) + (j : ℕ))) (p ((i : ℕ) + (j : ℕ) + 1)) (1 : K))
      = fun i : Fin N =>
        Matrix.single (p ((i : ℕ) + (j : ℕ))) (p (((i : ℕ) + 1) + (j : ℕ))) (1 : K) := by
    funext i
    rw [show ((i : ℕ) + (j : ℕ) + 1) = (((i : ℕ) + 1) + (j : ℕ)) from by omega]
  rw [hfam, formanekEval_shift_term hN x p hper j]
  rw [show deltaSq N (fun k : Fin (N + 1) => x (p ((k : ℕ) + (j : ℕ)))) = 0 from by
    rw [deltaSq_eq_vanderAll]
    exact vanderAll_shift_eq_zero_of_not_injective x p hper hinj j]
  simp

#print axioms formanekG_eq_zero_of_not_injective

/-- ★ ★ **工序 B（合取形态）**：`G` 的测试族值 = 单射时 `Δ² • 1`，否则 `0`
（AGPR `thm:10.2.4` 证明的两分支合并；印刷页 271）。 -/
theorem formanekG_eq_ite {N : ℕ} [NeZero N] (x : Fin N → K) (p : ℕ → Fin N)
    (hper : ∀ k, p (k + N) = p k) :
    formanekG N (gPoly K N) (Matrix.diagonal x) p
      = if Function.Injective (fun i : Fin N => p i) then vanderAll N x • 1 else 0 := by
  split_ifs with h
  · exact formanekG_eq_smul x p hper h
  · exact formanekG_eq_zero_of_not_injective x p hper h

#print axioms formanekG_eq_ite

/-- `Fin N` 里 `(i + 1)` 的值。 -/
theorem fin_val_add_one {N : ℕ} [NeZero N] (i : Fin N) :
    (i + 1 : Fin N).val = ((i : ℕ) + 1) % N := by
  rw [Fin.val_add, Fin.val_one']
  rw [Nat.add_mod (i : ℕ) (1 % N) N, Nat.mod_mod, Nat.add_mod (i : ℕ) 1 N]

#print axioms fin_val_add_one

/-- 一般形态：`G = Σ_j φ∘(Y 的循环平移)`（`Y` 任意）—— AGPR `thm:10.2.4` 的 `G`。 -/
noncomputable def formanekGGen (N : ℕ) [NeZero N] (g : MvPolynomial (Fin (N + 1)) K)
    (X : Matrix (Fin N) (Fin N) K) (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    Matrix (Fin N) (Fin N) K :=
  ∑ j : Fin N, formanekEval N g X (fun i : Fin N => Y (i + j))

#print axioms formanekGGen

/-- **工序 C2b-1（全边成立支）**：`k i = h (i+1)`（含环绕边）时 `formanekGGen` 的任意单位值
= `Δ² • 1`（`h` 单射）／`0`（否则）——归约到 `formanekG_eq_ite`。 -/
theorem formanekGGen_units_all_edges (N : ℕ) [NeZero N] (hN : 1 ≤ N)
    (x : Fin N → K) (h k : Fin N → Fin N)
    (hk : ∀ i : Fin N, k i = h (i + 1)) :
    formanekGGen N (gPoly K N) (Matrix.diagonal x)
        (fun i => Matrix.single (h i) (k i) (1 : K))
      = if Function.Injective h then vanderAll N x • 1 else 0 := by
  classical
  set p : ℕ → Fin N := fun t => h ⟨t % N, Nat.mod_lt _ (NeZero.pos N)⟩ with hp_def
  have hper : ∀ t, p (t + N) = p t := by
    intro t
    rw [hp_def]; simp only
    congr 1
    exact Fin.ext (Nat.add_mod_right t N)
  have hp_eval : ∀ i : Fin N, p (i : ℕ) = h i := by
    intro i
    rw [hp_def]; simp only
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hp_succ : ∀ i : Fin N, p ((i : ℕ) + 1) = k i := by
    intro i
    rw [hk i, hp_def]; simp only
    congr 1
    refine Fin.ext ?_
    rw [fin_val_add_one]
  have hsum : formanekGGen N (gPoly K N) (Matrix.diagonal x)
        (fun i => Matrix.single (h i) (k i) (1 : K))
      = formanekG N (gPoly K N) (Matrix.diagonal x) p := by
    rw [formanekGGen, formanekG]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    funext i
    have h1 : h (i + j) = p ((i : ℕ) + (j : ℕ)) := by
      rw [hp_def]; simp only
      rfl
    have h2 : k (i + j) = p (((i : ℕ) + (j : ℕ)) + 1) := by
      rw [hk (i + j), hp_def]; simp only
      congr 1
      refine Fin.ext ?_
      rw [Fin.val_add, Fin.val_add, Fin.val_one']
      show ((↑i + ↑j) % N + 1 % N) % N = ((↑i + ↑j) + 1) % N
      exact (Nat.add_mod ((i : ℕ) + (j : ℕ)) 1 N).symm
    rw [h1, h2]
  have hiff : Function.Injective (fun i : Fin N => p i) ↔ Function.Injective h := by
    rw [show (fun i : Fin N => p i) = h from funext hp_eval]
  rw [hsum, formanekG_eq_ite (x := x) (p := p) hper]
  by_cases hh : Function.Injective h
  · have hh' : Function.Injective (fun i : Fin N => p i) := hiff.mpr hh
    rw [if_pos hh, if_pos hh']
  · have hh' : ¬ Function.Injective (fun i : Fin N => p i) := fun hc => hh (hiff.mp hc)
    rw [if_neg hh, if_neg hh']

#print axioms formanekGGen_units_all_edges

/-- 旋转 `j` 的测试序列（`Fin (N+1)` 索引）：位置 `s < N` 取 `x (h (s + j))`，末端取 `x (k (j-1))`。 -/
noncomputable def yj {N : ℕ} [NeZero N] (x : Fin N → K) (h k : Fin N → Fin N) (j : Fin N) :
    Fin (N + 1) → K :=
  fun s => if hs : (s : ℕ) < N then x (h (⟨(s : ℕ), hs⟩ + j)) else x (k (j - 1))

/-- `yj` 在 `h a = h b` 处给出相同的值（位置 = `a - j`）。 -/
theorem yj_eq_of_h_eq {N : ℕ} [NeZero N] (x : Fin N → K) (h k : Fin N → Fin N) (j : Fin N)
    {a b : Fin N} (hab : h a = h b) :
    yj x h k j ⟨(a - j).val, Nat.lt_succ_of_lt (a - j).isLt⟩
      = yj x h k j ⟨(b - j).val, Nat.lt_succ_of_lt (b - j).isLt⟩ := by
  have ha : ((a - j : Fin N).val) < N := (a - j).isLt
  have hb : ((b - j : Fin N).val) < N := (b - j).isLt
  have hA : (⟨((a - j : Fin N).val), ha⟩ : Fin N) = a - j := Fin.ext rfl
  have hB : (⟨((b - j : Fin N).val), hb⟩ : Fin N) = b - j := Fin.ext rfl
  simp only [yj, dif_pos ha, dif_pos hb, hA, hB, sub_add_cancel, hab]

#print axioms yj_eq_of_h_eq

/-- **非单射 ⟹ `g.eval yj = 0`**（`h` 非单射时，前 `N` 个位置必有两处相等）。 -/
theorem gPoly_eval_yj_eq_zero_of_not_injective {N : ℕ} [NeZero N] (x : Fin N → K)
    (h k : Fin N → Fin N) (j : Fin N) (hinj : ¬ Function.Injective h) :
    (MvPolynomial.eval (yj x h k j)) (gPoly K N) = 0 := by
  classical
  unfold Function.Injective at hinj
  push_neg at hinj
  obtain ⟨a, b, hab, hne⟩ := hinj
  set ia : Fin (N + 1) := ⟨(a - j).val, Nat.lt_succ_of_lt (a - j).isLt⟩ with hia
  set ib : Fin (N + 1) := ⟨(b - j).val, Nat.lt_succ_of_lt (b - j).isLt⟩ with hib
  have hz : (yj x h k j) ia = (yj x h k j) ib := yj_eq_of_h_eq x h k j hab
  have hia_lt : ia.val < N := (a - j).isLt
  have hib_lt : ib.val < N := (b - j).isLt
  have hia_ne : ia ≠ ib := by
    intro hEq
    have hval : (a - j).val = (b - j).val := by
      have := congrArg Fin.val hEq
      simpa [hia, hib] using this
    have hfin : (a - j : Fin N) = b - j := Fin.ext hval
    have : a - j + j = b - j + j := by rw [hfin]
    rw [sub_add_cancel, sub_add_cancel] at this
    exact hne this
  by_cases h0 : ia.val = 0
  · have hia0 : ia = 0 := Fin.ext h0
    have hib_mem : ib ∈ midSet N := by
      rw [midSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro hz0
        exact hia_ne (by rw [hz0, hia0])
      · intro hz0
        have hv : ib.val = N := by rw [hz0]; rfl
        omega
    refine gPoly_eval_eq_zero_of_left N (yj x h k j) hib_mem ?_
    rw [← hia0]
    exact hz
  · by_cases h0' : ib.val = 0
    · have hib0 : ib = 0 := Fin.ext h0'
      have hia_mem : ia ∈ midSet N := by
        rw [midSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro hz0
          exact hia_ne (by rw [hz0, hib0])
        · intro hz0
          have hv : ia.val = N := by rw [hz0]; rfl
          omega
      refine gPoly_eval_eq_zero_of_left N (yj x h k j) hia_mem ?_
      rw [← hib0]
      exact hz.symm
    · have hia_mem : ia ∈ midSet N := by
        rw [midSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro hz0
          have hv : ia.val = 0 := by rw [hz0]; rfl
          exact h0 hv
        · intro hz0
          have hv : ia.val = N := by rw [hz0]; rfl
          omega
      have hib_mem : ib ∈ midSet N := by
        rw [midSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro hz0
          have hv : ib.val = 0 := by rw [hz0]; rfl
          exact h0' hv
        · intro hz0
          have hv : ib.val = N := by rw [hz0]; rfl
          omega
      rcases lt_or_gt_of_ne hia_ne with hlt | hgt
      · exact gPoly_eval_eq_zero_of_mid N (yj x h k j) hia_mem
          (Finset.mem_filter.mpr ⟨hib_mem, hlt⟩) hz
      · exact gPoly_eval_eq_zero_of_mid N (yj x h k j) hib_mem
          (Finset.mem_filter.mpr ⟨hia_mem, hgt⟩) hz.symm

#print axioms gPoly_eval_yj_eq_zero_of_not_injective

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K]

/-- **单射 ＋ 末项不闭合 ⟹ `g.eval yj = 0`**（`k (j-1) = h t`，`t ≠ j` 给出中间位置与末项相等）。 -/
theorem gPoly_eval_yj_eq_zero_of_endpoint_ne {N : ℕ} [NeZero N] (x : Fin N → K)
    (h k : Fin N → Fin N) (j : Fin N) (hinj : Function.Injective h)
    (hne : k (j - 1) ≠ h j) :
    (MvPolynomial.eval (yj x h k j)) (gPoly K N) = 0 := by
  classical
  have hsurj : Function.Surjective h := Finite.injective_iff_surjective.mp hinj
  obtain ⟨t, ht⟩ := hsurj (k (j - 1))
  have ht_ne : t ≠ j := by
    intro htj
    exact hne (by rw [← ht, htj])
  set s : Fin N := t - j with hs
  have hs_add : s + j = t := sub_add_cancel t j
  have hs_ne : s ≠ 0 := by
    intro hs0
    apply ht_ne
    rw [← hs_add, hs0, zero_add]
  have hs_lt : s.val < N := s.isLt
  set i : Fin (N + 1) := ⟨s.val, Nat.lt_succ_of_lt hs_lt⟩ with hi
  have hi_lt : i.val < N := hs_lt
  have hi_mem : i ∈ midSet N := by
    rw [midSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro hz0
      apply hs_ne
      have : i.val = 0 := by rw [hz0]; rfl
      exact Fin.ext this
    · intro hz0
      have hv : i.val = N := by rw [hz0]; rfl
      omega
  have hzi : (yj x h k j) i = (yj x h k j) (Fin.last N) := by
    have hpos : (i : ℕ) < N := hi_lt
    have hlast : ¬ ((Fin.last N : Fin (N + 1)) : ℕ) < N := by
      simp
    simp only [yj, dif_pos hpos, dif_neg (Nat.lt_irrefl N), Fin.val_last]
    congr 2
    · rw [show (⟨(i : ℕ), hpos⟩ : Fin N) = s from Fin.ext rfl, hs_add, ht]
  refine gPoly_eval_eq_zero_of_right N (yj x h k j) hi_mem ?_
  exact hzi.symm

#print axioms gPoly_eval_yj_eq_zero_of_endpoint_ne

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K]

/-- **单射 ＋ 末项闭合 ⟹ `g.eval yj = Δ²`**（`gPoly_eval_of_last_eq` ＋ 两次置换不变性）。 -/
theorem gPoly_eval_yj_eq_vanderAll {N : ℕ} [NeZero N] (x : Fin N → K)
    (h k : Fin N → Fin N) (j : Fin N) (hinj : Function.Injective h)
    (hclose : k (j - 1) = h j) :
    (MvPolynomial.eval (yj x h k j)) (gPoly K N) = vanderAll N x := by
  have hz0 : (yj x h k j) 0 = x (h j) := by
    show (if hs : (0 : Fin (N+1)).val < N then
        x (h (⟨(0 : Fin (N+1)).val, hs⟩ + j)) else x (k (j - 1))) = x (h j)
    rw [dif_pos (show (0 : Fin (N+1)).val < N from Nat.pos_of_ne_zero NeZero.out)]
    simp
  have hzN : (yj x h k j) (Fin.last N) = x (h j) := by
    show (if hs : ((Fin.last N : Fin (N+1))).val < N then
        x (h (⟨((Fin.last N : Fin (N+1))).val, hs⟩ + j)) else x (k (j - 1)))
      = x (h j)
    rw [dif_neg (show ¬ ((Fin.last N : Fin (N+1))).val < N from by simp), hclose]
  rw [gPoly_eval_of_last_eq N _ (by rw [hzN, hz0]), deltaSq_eq_vanderAll]
  have hfun : (fun i : Fin N => (yj x h k j) i.castSucc) = fun i : Fin N => x (h (i + j)) := by
    funext i
    show (if hs : ((i.castSucc : Fin (N+1))).val < N then
        x (h (⟨((i.castSucc : Fin (N+1))).val, hs⟩ + j)) else x (k (j - 1)))
      = x (h (i + j))
    rw [dif_pos (show ((i.castSucc : Fin (N+1))).val < N from by simpa using i.isLt)]
    simp
  rw [hfun]
  let σh : Equiv.Perm (Fin N) := Equiv.ofBijective h
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have h1 := vanderAll_comp_perm (N := N) (fun a : Fin N => x (h a)) (shiftEquiv N j)
  have h2 := vanderAll_comp_perm (N := N) x σh
  rw [show (fun i : Fin N => x (h (i + j)))
      = fun i : Fin N => (fun a : Fin N => x (h a)) ((shiftEquiv N j) i) from by
    funext i
    congr 1]
  rw [h1]
  exact h2

#print axioms gPoly_eval_yj_eq_vanderAll

/-- 旋转 `j` 的 `h`-序列（`ℕ` 索引）。 -/
noncomputable def rotH {N : ℕ} [NeZero N] (h : Fin N → Fin N) (j : Fin N) : ℕ → Fin N :=
  fun t => h ⟨(t + (j : ℕ)) % N, Nat.mod_lt _ (NeZero.pos N)⟩

/-- 旋转 `j` 的 `k`-序列（`ℕ` 索引）。 -/
noncomputable def rotK {N : ℕ} [NeZero N] (k : Fin N → Fin N) (j : Fin N) : ℕ → Fin N :=
  fun t => k ⟨(t + (j : ℕ)) % N, Nat.mod_lt _ (NeZero.pos N)⟩

/-- `rotH h j` 在 `Fin N` 上与 `h (· + j)` 一致。 -/
theorem rotH_fin {N : ℕ} [NeZero N] (h : Fin N → Fin N) (j : Fin N) (i : Fin N) :
    rotH h j (i : ℕ) = h (i + j) := rfl

#print axioms rotH_fin

/-- `rotK k j` 在 `Fin N` 上与 `k (· + j)` 一致。 -/
theorem rotK_fin {N : ℕ} [NeZero N] (k : Fin N → Fin N) (j : Fin N) (i : Fin N) :
    rotK k j (i : ℕ) = k (i + j) := rfl

#print axioms rotK_fin

theorem rotH_zero {N : ℕ} [NeZero N] (h : Fin N → Fin N) (j : Fin N) :
    rotH h j 0 = h j := by
  show h ⟨(0 + (j : ℕ)) % N, _⟩ = h j
  congr 1
  exact Fin.ext (by
    show (0 + (j : ℕ)) % N = (j : ℕ)
    rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt])

#print axioms rotH_zero

theorem rotK_end {N : ℕ} [NeZero N] (k : Fin N → Fin N) (j : Fin N) :
    rotK k j (N - 1) = k (j - 1) := by
  show k ⟨((N - 1) + (j : ℕ)) % N, _⟩ = k (j - 1)
  congr 1
  refine Fin.ext ?_
  rw [Fin.val_sub]
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) with h1 | h2
  · rcases h1.symm with rfl
    simp
  · have h1val : ((1 : Fin N) : ℕ) = 1 := by
      show (1 : ℕ) % N = 1
      exact Nat.mod_eq_of_lt h2
    rw [h1val]

#print axioms rotK_end

theorem rotH_mid {N : ℕ} [NeZero N] (h : Fin N → Fin N) (j : Fin N) (s : Fin (N + 1))
    (hs : (s : ℕ) < N) : rotH h j (s : ℕ) = h (⟨(s : ℕ), hs⟩ + j) := rfl

#print axioms rotH_mid

theorem rotK_mid {N : ℕ} [NeZero N] (k : Fin N → Fin N) (j : Fin N) (s : Fin (N + 1))
    (hs : (s : ℕ) < N) : rotK k j (s : ℕ) = k (⟨(s : ℕ), hs⟩ + j) := rfl

#print axioms rotK_mid


/-- **旋转运输引理**：`formanekEval` 在旋转单位族上的值（链条件为 `ℕ`-索引形式）。 -/
theorem formanekEval_rot {N : ℕ} [NeZero N] (hN : 1 ≤ N)
    (x : Fin N → K) (h k : Fin N → Fin N) (j : Fin N) :
    formanekEval N (gPoly K N) (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single (h (i + j)) (k (i + j)) (1 : K))
      = if (∀ t : ℕ, t < N - 1 → rotK k j t = rotH h j (t + 1)) then
          Matrix.single (h j) (k (j - 1)) ((MvPolynomial.eval (yj x h k j)) (gPoly K N))
        else 0 := by
  classical
  have hfam : (fun i : Fin N => Matrix.single (h (i + j)) (k (i + j)) (1 : K))
      = fun i : Fin N => Matrix.single (rotH h j i) (rotK k j i) (1 : K) := by
    funext i
    rw [rotH_fin, rotK_fin]
  rw [hfam, formanekEval_units N hN (gPoly K N) x (rotH h j) (rotK k j)]
  by_cases hc : ∀ t : ℕ, t < N - 1 → rotK k j t = rotH h j (t + 1)
  · rw [if_pos hc, if_pos hc, rotH_zero, rotK_end]
    congr 1
  · rw [if_neg hc, if_neg hc]

#print axioms formanekEval_rot

/-- `⟨N-1⟩ + j = j - 1`（`Fin N` 加法群）。 -/
theorem neg_one_add {N : ℕ} [NeZero N] (j : Fin N) :
    (⟨N - 1, by have h := NeZero.pos N; omega⟩ : Fin N) + j = j - 1 := by
  refine Fin.ext ?_
  rw [Fin.val_add, Fin.val_sub]
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) with h1 | h2
  · rcases h1.symm with rfl
    simp
  · have h1val : ((1 : Fin N) : ℕ) = 1 := by
      show (1 : ℕ) % N = 1
      exact Nat.mod_eq_of_lt h2
    rw [h1val]

#print axioms neg_one_add

/-- **端边推导**：`ℕ`-链条件 ＋ 末边闭合 ⟹ 全部循环边成立。 -/
theorem chain_all_edges {N : ℕ} [NeZero N] (h k : Fin N → Fin N) (j : Fin N)
    (hC : ∀ t : ℕ, t < N - 1 → rotK k j t = rotH h j (t + 1))
    (hk_end : k (j - 1) = h j) :
    ∀ i : Fin N, k i = h (i + 1) := by
  intro i
  set t : Fin N := i - j with ht_def
  have ht : t + j = i := sub_add_cancel i j
  by_cases hcase : t.val = N - 1
  · have ht_eq : t = (⟨N - 1, by have h := NeZero.pos N; omega⟩ : Fin N) := Fin.ext hcase
    have hi : i = j - 1 := by
      rw [← ht, ht_eq, neg_one_add]
    rw [hi, hk_end]
    congr 1
    abel
  · have ht_lt : t.val < N - 1 := by
      have := t.isLt
      omega
    have hstep := hC t.val ht_lt
    -- 左端 = k i
    have hleft : rotK k j t.val = k i := by
      rw [rotK_fin k j t, ht]
    -- 右端 = h (i+1)
    have hright : rotH h j (t.val + 1) = h (i + 1) := by
      have hlt1 : t.val + 1 < N := by omega
      rw [rotH_mid h j ⟨t.val + 1, Nat.lt_succ_of_lt hlt1⟩ hlt1]
      congr 1
      have hstep : (⟨t.val + 1, hlt1⟩ : Fin N) = t + 1 := by
        refine Fin.ext ?_
        rw [fin_val_add_one, Nat.mod_eq_of_lt hlt1]
      rw [hstep, ← ht]
      abel
    rw [hleft, hright] at hstep
    exact hstep

#print axioms chain_all_edges

/-- ★★★ **工序 C2b 收口**：`G` 在**任意矩阵单位**族上的值。 -/
theorem formanekGGen_units_eq {N : ℕ} [NeZero N] (hN : 1 ≤ N) (x : Fin N → K)
    (h k : Fin N → Fin N) :
    formanekGGen N (gPoly K N) (Matrix.diagonal x)
        (fun i => Matrix.single (h i) (k i) (1 : K))
      = if (Function.Injective h ∧ ∀ i : Fin N, k i = h (i + 1)) then
          vanderAll N x • 1 else 0 := by
  classical
  by_cases hgood : Function.Injective h ∧ ∀ i : Fin N, k i = h (i + 1)
  · rw [if_pos hgood]
    rw [formanekGGen_units_all_edges N hN x h k hgood.2, if_pos hgood.1]
  · rw [if_neg hgood]
    rw [formanekGGen]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [formanekEval_rot hN x h k j]
    by_cases hC : ∀ t : ℕ, t < N - 1 → rotK k j t = rotH h j (t + 1)
    · rw [if_pos hC]
      by_cases hinj : Function.Injective h
      · by_cases hend : k (j - 1) = h j
        · exact absurd ⟨hinj, chain_all_edges h k j hC hend⟩ hgood
        · rw [gPoly_eval_yj_eq_zero_of_endpoint_ne x h k j hinj hend]
          simp
      · rw [gPoly_eval_yj_eq_zero_of_not_injective x h k j hinj]
        simp
    · rw [if_neg hC]

#print axioms formanekGGen_units_eq

/-- `wordOf` 的 `List.ofFn` 形式（非交换积，按 `Fin N` 的自然次序）。 -/
theorem wordOf_eq_ofFn (N : ℕ) (n : ℕ → ℕ) (X : Matrix (Fin N) (Fin N) K)
    (Z : Fin N → Matrix (Fin N) (Fin N) K) :
    wordOf N n X Z = (List.ofFn (fun k : Fin N => X ^ (n k) * Z k)).prod * X ^ (n N) := by
  rw [wordOf]
  have hlist : (List.range N).map (fun k => if h : k < N then X ^ (n k) * Z ⟨k, h⟩ else 1)
      = List.ofFn (fun k : Fin N => X ^ (n k) * Z k) := by
    refine List.ext_getElem ?_ ?_
    · simp
    · intro j hj1 hj2
      rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      rw [dif_pos (by simpa using hj1)]
  rw [hlist]

#print axioms wordOf_eq_ofFn

/-- `Function.update` 在更新点的值（本 pin 缺 `update_same`）。 -/
theorem update_same' {α β : Type*} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    Function.update f a b a = b := by
  rw [Function.update_apply, if_pos rfl]

#print axioms update_same'

/-- `Function.update` 在非更新点的值（本 pin 缺 `update_noteq`）。 -/
theorem update_noteq' {α β : Type*} [DecidableEq α] (f : α → β) {a a' : α} (b : β) (h : a ≠ a') :
    Function.update f a' b a = f a := by
  rw [Function.update_apply, if_neg h]

#print axioms update_noteq'

/-- 坐标替换与 `List.set` 的相容性。 -/
theorem ofFn_update_set (N : ℕ) (n : ℕ → ℕ) (X : Matrix (Fin N) (Fin N) K)
    (Z : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N) (W : Matrix (Fin N) (Fin N) K) :
    List.ofFn (fun k : Fin N => X ^ (n k) * (Function.update Z i W) k)
      = (List.ofFn (fun k : Fin N => X ^ (n k) * Z k)).set i.val (X ^ (n i) * W) := by
  refine List.ext_getElem ?_ ?_
  · rw [List.length_set, List.length_ofFn, List.length_ofFn]
  · intro j hj1 hj2
    have hjN : j < N := by rw [List.length_ofFn] at hj1; exact hj1
    rw [List.getElem_ofFn, List.getElem_set]
    by_cases hji : i.val = j
    · rw [if_pos hji]
      have hidx : (⟨j, hjN⟩ : Fin N) = i := Fin.ext hji.symm
      rw [hidx, update_same' Z i W]
    · rw [if_neg hji]
      have hneq : (⟨j, hjN⟩ : Fin N) ≠ i := fun hEq => hji (by rw [← hEq])
      rw [List.getElem_ofFn, update_noteq' Z W hneq]

#print axioms ofFn_update_set

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-- `wordOf` 的逐坐标加法性。 -/
theorem wordOf_update_add (N : ℕ) (n : ℕ → ℕ) (X : Matrix (Fin N) (Fin N) K)
    (Z : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N) (A B : Matrix (Fin N) (Fin N) K) :
    wordOf N n X (Function.update Z i (A + B))
      = wordOf N n X (Function.update Z i A) + wordOf N n X (Function.update Z i B) := by
  have hW : ∀ W : Matrix (Fin N) (Fin N) K, wordOf N n X (Function.update Z i W)
      = (((List.ofFn (fun k : Fin N => X ^ (n k) * Z k)).take i.val).prod
          * (X ^ (n i) * W)
          * ((List.ofFn (fun k : Fin N => X ^ (n k) * Z k)).drop (i.val + 1)).prod)
        * X ^ (n N) := by
    intro W
    rw [wordOf_eq_ofFn, ofFn_update_set, List.prod_set]
    rw [if_pos (by rw [List.length_ofFn]; exact i.isLt)]
  rw [hW (A + B), hW A, hW B]
  noncomm_ring

#print axioms wordOf_update_add

/-- `wordOf` 的逐坐标齐次性。 -/
theorem wordOf_update_smul (N : ℕ) (n : ℕ → ℕ) (X : Matrix (Fin N) (Fin N) K)
    (Z : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N) (c : K) (A : Matrix (Fin N) (Fin N) K) :
    wordOf N n X (Function.update Z i (c • A)) = c • wordOf N n X (Function.update Z i A) := by
  have hW : ∀ W : Matrix (Fin N) (Fin N) K, wordOf N n X (Function.update Z i W)
      = (((List.ofFn (fun k : Fin N => X ^ (n k) * Z k)).take i.val).prod
          * (X ^ (n i) * W)
          * ((List.ofFn (fun k : Fin N => X ^ (n k) * Z k)).drop (i.val + 1)).prod)
        * X ^ (n N) := by
    intro W
    rw [wordOf_eq_ofFn, ofFn_update_set, List.prod_set]
    rw [if_pos (by rw [List.length_ofFn]; exact i.isLt)]
  rw [hW (c • A), hW A, Matrix.mul_smul, Matrix.mul_smul, smul_mul_assoc, smul_mul_assoc]

#print axioms wordOf_update_smul

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-- `formanekEval` 的逐坐标加法性。 -/
theorem formanekEval_update_add (N : ℕ) (g : MvPolynomial (Fin (N + 1)) K)
    (X : Matrix (Fin N) (Fin N) K) (Z : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N)
    (A B : Matrix (Fin N) (Fin N) K) :
    formanekEval N g X (Function.update Z i (A + B))
      = formanekEval N g X (Function.update Z i A)
        + formanekEval N g X (Function.update Z i B) := by
  rw [formanekEval, formanekEval, formanekEval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [wordOf_update_add, smul_add]

#print axioms formanekEval_update_add

/-- `formanekEval` 的逐坐标齐次性。 -/
theorem formanekEval_update_smul (N : ℕ) (g : MvPolynomial (Fin (N + 1)) K)
    (X : Matrix (Fin N) (Fin N) K) (Z : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N)
    (c : K) (A : Matrix (Fin N) (Fin N) K) :
    formanekEval N g X (Function.update Z i (c • A))
      = c • formanekEval N g X (Function.update Z i A) := by
  rw [formanekEval, formanekEval, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [wordOf_update_smul, smul_comm]

#print axioms formanekEval_update_smul

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-- 旋转族的坐标替换：在 `Y` 的第 `i` 坐标更新 ⟺ 在旋转族的第 `i - j` 坐标更新。 -/
theorem rot_update [NeZero N] (Y : Fin N → Matrix (Fin N) (Fin N) K) (i j : Fin N)
    (W : Matrix (Fin N) (Fin N) K) :
    (fun i' : Fin N => Function.update Y i W (i' + j))
      = Function.update (fun i' : Fin N => Y (i' + j)) (i - j) W := by
  funext i'
  rw [Function.update_apply, Function.update_apply]
  by_cases h : i' + j = i
  · have hip : i' = i - j := by rw [← h]; abel
    rw [if_pos h, if_pos hip]
  · have hne : ¬ i' = i - j := fun h' => h (by rw [h']; abel)
    rw [if_neg h, if_neg hne]

#print axioms rot_update

/-- `formanekGGen` 的逐坐标加法性。 -/
theorem formanekGGen_update_add (N : ℕ) [NeZero N] (hN : 1 ≤ N)
    (X : Matrix (Fin N) (Fin N) K) (Y : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N)
    (A B : Matrix (Fin N) (Fin N) K) :
    formanekGGen N (gPoly K N) X (Function.update Y i (A + B))
      = formanekGGen N (gPoly K N) X (Function.update Y i A)
        + formanekGGen N (gPoly K N) X (Function.update Y i B) := by
  rw [formanekGGen, formanekGGen, formanekGGen, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [rot_update Y i j (A + B), rot_update Y i j A, rot_update Y i j B]
  exact formanekEval_update_add N (gPoly K N) X _ (i - j) A B

#print axioms formanekGGen_update_add

/-- `formanekGGen` 的逐坐标齐次性。 -/
theorem formanekGGen_update_smul (N : ℕ) [NeZero N] (hN : 1 ≤ N)
    (X : Matrix (Fin N) (Fin N) K) (Y : Fin N → Matrix (Fin N) (Fin N) K) (i : Fin N)
    (c : K) (A : Matrix (Fin N) (Fin N) K) :
    formanekGGen N (gPoly K N) X (Function.update Y i (c • A))
      = c • formanekGGen N (gPoly K N) X (Function.update Y i A) := by
  rw [formanekGGen, formanekGGen, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [rot_update Y i j (c • A), rot_update Y i j A]
  exact formanekEval_update_smul N (gPoly K N) X _ (i - j) c A

#print axioms formanekGGen_update_smul

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-- `G`（任意 `Y`）作为 `MultilinearMap`。 -/
noncomputable def formanekGMap (N : ℕ) [NeZero N] (hN : 1 ≤ N)
    (X : Matrix (Fin N) (Fin N) K) :
    MultilinearMap K (fun _ : Fin N => Matrix (Fin N) (Fin N) K) (Matrix (Fin N) (Fin N) K) :=
  MultilinearMap.mk' (formanekGGen N (gPoly K N) X)
    (fun m i x y => formanekGGen_update_add N hN X m i x y)
    (fun m i c x => formanekGGen_update_smul N hN X m i c x)

#print axioms formanekGMap

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-! ## R768 收口：`lem:10.2.3` 的 ③ 半（`X` 对角、`Y` 任意）

`formanekGGen_units_eq` 只覆盖"`Y` 取矩阵单位族"。本段按 AGPR `lem:10.2.3` 证明的末句
（"since the polynomial is linear in the `Y_i`"）把 `Y` 放开到**任意**矩阵：
矩阵单位展开（`Matrix.sum_sum_single`）＋ `MultilinearMap.map_sum` 展开成元组和
＋ 每个元组用齐次性（`map_smul_univ`）和 `formanekGGen_units_eq` 得纯量值
＋ 求和。 -/

/-- 矩阵单位展开：`M = ∑ p, single p.1 p.2 (M p.1 p.2)`。 -/
theorem matrix_eq_sum_units (M : Matrix (Fin N) (Fin N) K) :
    M = ∑ p : Fin N × Fin N, Matrix.single p.1 p.2 (M p.1 p.2) := by
  rw [Fintype.sum_prod_type]
  exact (Matrix.sum_sum_single (fun a b => M a b)).symm

#print axioms matrix_eq_sum_units

/-- `single a b c = c • single a b 1`。 -/
theorem single_eq_smul_one (a b : Fin N) (c : K) :
    Matrix.single a b c = c • Matrix.single a b (1 : K) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

#print axioms single_eq_smul_one

/-- 系数逐坐标齐次：矩阵单位族上的 `G` 对系数是 `N`-重线性的。 -/
theorem formanekGGen_units_coeff (N : ℕ) [NeZero N] (hN : 1 ≤ N) (x : Fin N → K)
    (h k : Fin N → Fin N) (c : Fin N → K) :
    formanekGGen N (gPoly K N) (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single (h i) (k i) (c i))
      = (∏ i : Fin N, c i) •
          formanekGGen N (gPoly K N) (Matrix.diagonal x)
            (fun i : Fin N => Matrix.single (h i) (k i) (1 : K)) := by
  have hfun : (fun i : Fin N => Matrix.single (h i) (k i) (c i))
      = (fun i : Fin N => c i • Matrix.single (h i) (k i) (1 : K)) := by
    funext i
    rw [single_eq_smul_one]
  rw [hfun]
  show (formanekGMap N hN (Matrix.diagonal x))
      (fun i : Fin N => c i • Matrix.single (h i) (k i) (1 : K)) = _
  rw [MultilinearMap.map_smul_univ]
  rfl

#print axioms formanekGGen_units_coeff

/-- `c • (if p then d • 1 else 0) = (if p then c * d else 0) • 1`（矩阵版）。 -/
theorem smul_ite_smul_one {p : Prop} [Decidable p] (c d : K) :
    c • (if p then d • (1 : Matrix (Fin N) (Fin N) K) else 0)
      = (if p then c * d else 0) • (1 : Matrix (Fin N) (Fin N) K) := by
  split_ifs with h
  · rw [smul_smul]
  · rw [smul_zero, zero_smul]

#print axioms smul_ite_smul_one

/-- ★★ **C3-③ 的"任意 `Y`"半步**（`MultilinearMap` 形态）：`X` 对角、`Y` 任意 ⟹ `G` 取纯量值。 -/
theorem formanekGMap_diagonal_scalar (N : ℕ) [NeZero N] (hN : 1 ≤ N) (x : Fin N → K)
    (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    ∃ c : K, formanekGMap N hN (Matrix.diagonal x) Y
      = c • (1 : Matrix (Fin N) (Fin N) K) := by
  classical
  have hY : ∀ i : Fin N, Y i = ∑ p : Fin N × Fin N, Matrix.single p.1 p.2 (Y i p.1 p.2) :=
    fun i => matrix_eq_sum_units (Y i)
  have hexp : (formanekGMap N hN (Matrix.diagonal x)) Y
      = ∑ r : Fin N → Fin N × Fin N,
          (formanekGMap N hN (Matrix.diagonal x))
            (fun i : Fin N => Matrix.single (r i).1 (r i).2 (Y i (r i).1 (r i).2)) := by
    conv_lhs => rw [show Y = (fun i : Fin N => ∑ p : Fin N × Fin N,
        Matrix.single p.1 p.2 (Y i p.1 p.2)) from funext hY]
    rw [MultilinearMap.map_sum]
  have hterm : ∀ r : Fin N → Fin N × Fin N,
      (formanekGMap N hN (Matrix.diagonal x))
          (fun i : Fin N => Matrix.single (r i).1 (r i).2 (Y i (r i).1 (r i).2))
        = (if Function.Injective (fun i : Fin N => (r i).1) ∧
              ∀ i : Fin N, (fun i : Fin N => (r i).2) i = (fun i : Fin N => (r i).1) (i + 1)
            then (∏ i : Fin N, Y i (r i).1 (r i).2) * vanderAll N x else 0)
          • (1 : Matrix (Fin N) (Fin N) K) := by
    intro r
    show formanekGGen N (gPoly K N) (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single (r i).1 (r i).2 (Y i (r i).1 (r i).2)) = _
    rw [formanekGGen_units_coeff N hN x (fun i : Fin N => (r i).1)
      (fun i : Fin N => (r i).2) (fun i : Fin N => Y i (r i).1 (r i).2)]
    rw [formanekGGen_units_eq hN x (fun i : Fin N => (r i).1) (fun i : Fin N => (r i).2)]
    rw [smul_ite_smul_one]
  refine ⟨∑ r : Fin N → Fin N × Fin N,
      (if Function.Injective (fun i : Fin N => (r i).1) ∧
          ∀ i : Fin N, (fun i : Fin N => (r i).2) i = (fun i : Fin N => (r i).1) (i + 1)
        then (∏ i : Fin N, Y i (r i).1 (r i).2) * vanderAll N x else 0), ?_⟩
  rw [hexp, Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_smul]

#print axioms formanekGMap_diagonal_scalar

/-- ★★ **C3-③ 的"任意 `Y`"半步**（`formanekGGen` 形态）：`X` 对角、`Y` 任意 ⟹ 纯量。 -/
theorem formanekGGen_diagonal_scalar (N : ℕ) [NeZero N] (hN : 1 ≤ N) (x : Fin N → K)
    (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    ∃ c : K, formanekGGen N (gPoly K N) (Matrix.diagonal x) Y
      = c • (1 : Matrix (Fin N) (Fin N) K) :=
  formanekGMap_diagonal_scalar N hN x Y

#print axioms formanekGGen_diagonal_scalar

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-! ## R768 收口：工序 D 的非零性一半（`G` 不是零多项式） -/

/-- `vanderAll` 在单射族上非零（`Δ² ≠ 0` 的行列式形态）。 -/
theorem vanderAll_ne_zero [IsDomain K] (N : ℕ) {x : Fin N → K}
    (hx : Function.Injective x) : vanderAll N x ≠ 0 := by
  rw [vanderAll, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  refine pow_ne_zero 2 ?_
  rw [sub_ne_zero]
  exact fun heq => (ne_of_lt (Finset.mem_filter.mp hj).2) (hx heq)

#print axioms vanderAll_ne_zero

/-- **端边族上的 `G` 值**（`h = id`、`k i = i + 1`）：链条件成立，值 = `Δ² • 1`。 -/
theorem formanekGGen_units_eq_vanderAll_of_injective (N : ℕ) [NeZero N] (hN : 1 ≤ N)
    {x : Fin N → K} (hx : Function.Injective x) :
    formanekGGen N (gPoly K N) (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single i (i + 1) (1 : K)) = vanderAll N x • 1 := by
  rw [formanekGGen_units_eq hN x (fun i : Fin N => i) (fun i : Fin N => i + 1)]
  exact if_pos ⟨fun _ _ hab => hab, fun i => rfl⟩

#print axioms formanekGGen_units_eq_vanderAll_of_injective

/-- ★★★ **工序 D 的非零性一半**：`G` 在 `n×n` 矩阵上**不恒为零**。 -/
theorem formanekGGen_units_ne_zero [IsDomain K] (N : ℕ) [NeZero N] (hN : 1 ≤ N)
    {x : Fin N → K} (hx : Function.Injective x) :
    formanekGGen N (gPoly K N) (Matrix.diagonal x)
      (fun i : Fin N => Matrix.single i (i + 1) (1 : K)) ≠ 0 := by
  rw [formanekGGen_units_eq_vanderAll_of_injective N hN hx]
  intro hzero
  have hc : vanderAll N x = 0 := by
    have h00 := congrArg (fun M : Matrix (Fin N) (Fin N) K => M 0 0) hzero
    simpa [Matrix.smul_apply] using h00
  exact vanderAll_ne_zero N hx hc

#print axioms formanekGGen_units_ne_zero

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-! ## 工序 C3 ① 的第一块：**共轭协变**（AGPR `lem:10.2.3` 的 "invariant under conjugation"）

`G(P X P', (P Y_k P')_k) = P G(X, Y) P'`（`P` 双边可逆）。工艺：把 `X ↦ P * X * P'`
做成 `RingHom`（`conjRingHom`），则 `map_pow`／`map_mul`／`map_list_prod` 的搬运全部免费；
再对 `wordOf`（`ofFn` 形式）／`formanekEval`（`support` 求和）／`formanekGGen`（旋转求和）
逐层搬运。下游用途：把 `G` 在"可对角化 `X`"上的纯量性经由 `P` 回流到原矩阵；
本段**只做搬运**，不含对角化本身。 -/

/-- **共轭环自同构（内自同构的矩阵形态）**：`X ↦ P * X * P'`（`P * P' = 1`、`P' * P = 1`）。 -/
noncomputable def conjRingHom (P P' : Matrix (Fin N) (Fin N) K) (hP : P * P' = 1)
    (hP' : P' * P = 1) : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) K where
  toFun X := P * X * P'
  map_one' := by rw [mul_one, hP]
  map_mul' A B := by
    have h1 : (P * A * P') * (P * B * P') = P * A * (P' * P) * B * P' := by noncomm_ring
    rw [h1, hP']
    noncomm_ring
  map_zero' := by simp
  map_add' A B := by rw [mul_add, add_mul]

#print axioms conjRingHom

/-- `conjRingHom` 的求值式（下游改写用）。 -/
theorem conjRingHom_apply (P P' : Matrix (Fin N) (Fin N) K) (hP : P * P' = 1)
    (hP' : P' * P = 1) (X : Matrix (Fin N) (Fin N) K) :
    conjRingHom P P' hP hP' X = P * X * P' := rfl

#print axioms conjRingHom_apply

/-- 幂在共轭下协变。 -/
theorem conj_pow (X P P' : Matrix (Fin N) (Fin N) K) (hP : P * P' = 1)
    (hP' : P' * P = 1) (m : ℕ) :
    (P * X * P') ^ m = P * X ^ m * P' := by
  rw [← conjRingHom_apply P P' hP hP' X]
  rw [← map_pow (conjRingHom P P' hP hP') X m, conjRingHom_apply]

#print axioms conj_pow

/-- 列表积在共轭下协变。 -/
theorem prod_map_conj (P P' : Matrix (Fin N) (Fin N) K) (hP : P * P' = 1)
    (hP' : P' * P = 1) (L : List (Matrix (Fin N) (Fin N) K)) :
    (L.map (fun M => P * M * P')).prod = P * L.prod * P' := by
  induction L with
  | nil => simp [hP]
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    have h1 : (P * a * P') * (P * L.prod * P') = P * a * (P' * P) * L.prod * P' := by
      noncomm_ring
    rw [h1, hP']
    noncomm_ring

#print axioms prod_map_conj

/-- ★ **`wordOf` 在共轭下协变**（`P` 双边可逆）。 -/
theorem wordOf_conj (N : ℕ) (n : ℕ → ℕ) (X P P' : Matrix (Fin N) (Fin N) K)
    (hP : P * P' = 1) (hP' : P' * P = 1) (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    wordOf N n (P * X * P') (fun k => P * Y k * P') = P * wordOf N n X Y * P' := by
  have hmap : wordOf N n (conjRingHom P P' hP hP' X)
        (fun k => conjRingHom P P' hP hP' (Y k))
      = conjRingHom P P' hP hP' (wordOf N n X Y) := by
    rw [wordOf_eq_ofFn, wordOf_eq_ofFn, map_mul, map_list_prod, map_pow]
    congr 1
    congr 1
    rw [List.map_ofFn, List.ofFn_inj]
    funext k
    rw [Function.comp_apply, map_mul, map_pow]
  exact hmap

#print axioms wordOf_conj

/-- ★ **`formanekEval` 在共轭下协变**。 -/
theorem formanekEval_conj (N : ℕ) (g : MvPolynomial (Fin (N + 1)) K)
    (X P P' : Matrix (Fin N) (Fin N) K) (hP : P * P' = 1) (hP' : P' * P = 1)
    (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    formanekEval N g (P * X * P') (fun k => P * Y k * P') = P * formanekEval N g X Y * P' := by
  rw [formanekEval, formanekEval, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [wordOf_conj N _ X P P' hP hP' Y]
  noncomm_ring

#print axioms formanekEval_conj

/-- ★★ **`formanekGGen` 在共轭下协变**（C3 ① 的核心搬运引理）。 -/
theorem formanekGGen_conj (N : ℕ) [NeZero N] (X P P' : Matrix (Fin N) (Fin N) K)
    (hP : P * P' = 1) (hP' : P' * P = 1) (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    formanekGGen N (gPoly K N) (P * X * P') (fun k => P * Y k * P')
      = P * formanekGGen N (gPoly K N) X Y * P' := by
  rw [formanekGGen, formanekGGen, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact formanekEval_conj N (gPoly K N) X P P' hP hP' (fun k => Y (k + j))

#print axioms formanekGGen_conj

/-- **纯量性在共轭下不变**：`G` 取 `c • 1` ⟹ 共轭后仍取 `c • 1`。 -/
theorem conj_scalar (P P' : Matrix (Fin N) (Fin N) K) (hP : P * P' = 1)
    (hP' : P' * P = 1) (c : K) :
    P * (c • (1 : Matrix (Fin N) (Fin N) K)) * P' = c • (1 : Matrix (Fin N) (Fin N) K) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hP]

#print axioms conj_scalar

end Procesi

namespace Procesi
open Matrix
variable {K : Type*} [CommRing K] {N : ℕ}

/-! ## 系数环同态下的搬运（**基变换**）

`G` 的全部构造（`wordOf`／`formanekEval`／`formanekGGen`）都对系数环同态 `φ : K →+* L` 协变：

```
φ.mapMatrix (formanekGGen N (gPoly K N) X Y)
  = formanekGGen N (gPoly L N) (φ.mapMatrix X) (fun k => φ.mapMatrix (Y k))
```

用途：把 `G` 的值沿 `K → L` 搬运而不重算（"代数闭包上"与"`K[T]` 上的多项式性"两步都用它）。
工艺：`RingHom.mapMatrix`（`Data/Matrix/Basic.lean:600`）已是 `RingHom`，故 `map_mul`／
`map_pow`／`map_list_prod` 全免费；唯一要手写的是 `RingHom` 对 `K`-纯量乘法的搬运
（`RingHom` 不是 `AlgHom`，无现成 `map_smul`）。 -/

/-- `gPoly` 的系数无关性：它只由 `MvPolynomial.X` 与算术构成，故沿任意环同态不变。 -/
theorem gPoly_map {L : Type*} [CommRing L] (φ : K →+* L) (N : ℕ) :
    MvPolynomial.map φ (gPoly K N) = gPoly L N := by
  simp [gPoly]

#print axioms gPoly_map

/-- ★ **`wordOf` 与系数环同态交换。** -/
theorem wordOf_mapMatrix {L : Type*} [CommRing L] (φ : K →+* L) (N : ℕ) (n : ℕ → ℕ)
    (X : Matrix (Fin N) (Fin N) K) (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    φ.mapMatrix (wordOf N n X Y) = wordOf N n (φ.mapMatrix X) (fun k => φ.mapMatrix (Y k)) := by
  rw [wordOf_eq_ofFn, wordOf_eq_ofFn, map_mul, map_list_prod, map_pow]
  congr 1
  congr 1
  rw [List.map_ofFn, List.ofFn_inj]
  funext k
  rw [Function.comp_apply, map_mul, map_pow]

#print axioms wordOf_mapMatrix

/-- 环同态沿 `K`-纯量乘法的搬运（`RingHom` 不是 `AlgHom`，故无现成 `map_smul`）。 -/
theorem mapMatrix_smul {L : Type*} [CommRing L] (φ : K →+* L) (c : K)
    (M : Matrix (Fin N) (Fin N) K) :
    φ.mapMatrix (c • M) = φ c • φ.mapMatrix M := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

#print axioms mapMatrix_smul

/-- ★ **`formanekEval` 与系数环同态交换。** -/
theorem formanekEval_mapMatrix {L : Type*} [CommRing L] (φ : K →+* L) (N : ℕ)
    (g : MvPolynomial (Fin (N + 1)) K) (X : Matrix (Fin N) (Fin N) K)
    (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    φ.mapMatrix (formanekEval N g X Y)
      = formanekEval N (MvPolynomial.map φ g) (φ.mapMatrix X) (fun k => φ.mapMatrix (Y k)) := by
  rw [formanekEval, formanekEval, map_sum]
  simp only [mapMatrix_smul, wordOf_mapMatrix]
  refine (Finset.sum_subset (MvPolynomial.support_map_subset φ g) ?_).symm
  intro m _ hmnot
  have h0 : (MvPolynomial.map φ g).coeff m = 0 := by
    by_contra hne
    exact hmnot (MvPolynomial.mem_support_iff.mpr hne)
  rw [MvPolynomial.coeff_map] at h0
  rw [h0, zero_smul]

#print axioms formanekEval_mapMatrix

/-- ★★ **`formanekGGen` 与系数环同态交换**（基变换引理）。 -/
theorem formanekGGen_mapMatrix {L : Type*} [CommRing L] (φ : K →+* L) (N : ℕ) [NeZero N]
    (X : Matrix (Fin N) (Fin N) K) (Y : Fin N → Matrix (Fin N) (Fin N) K) :
    φ.mapMatrix (formanekGGen N (gPoly K N) X Y)
      = formanekGGen N (gPoly L N) (φ.mapMatrix X) (fun k => φ.mapMatrix (Y k)) := by
  rw [formanekGGen, formanekGGen, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formanekEval_mapMatrix φ N (gPoly K N) X (fun k => Y (k + j)), gPoly_map]

#print axioms formanekGGen_mapMatrix

end Procesi
