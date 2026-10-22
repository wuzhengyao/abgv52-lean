/-
  Procesi —— **PI 基础设施（S2b-1）：链式矩阵单位之积**

  **用途**：AGPR2020 `thm:10.2.4` 的证明要算 `φ` 在「`X` 对角、`Yᵢ` 取矩阵单位 `e_{hᵢ,kᵢ}`」
  上的值（`eq:10.3`）。当单位沿"链"相接（`k_i = h_{i+1}`）时，整条词收敛成一个矩阵单位，
  其系数是各因子的乘积——本件把这步机检。

  **陈述**：`E_{p a,p (a+1)}(c a) ⋯ E_{p (a+m),p (a+m+1)}(c (a+m)) = E_{p a, p (a+m+1)}(∏ c)`。
  （注意 `m` 以 `m+1` 个因子计：空积是单位矩阵，而单个 `e_{ii}(1)` 是秩一投影，两者不同——
  故本件对 `≥1` 个因子陈述，`R741` 的实测教训。）

  **为何 ℕ-索引**：`Fin (N+1)`-索引的归纳会撞上"类型随 `N` 变化"；本件用 `p : ℕ → Fin N`
  与 `c : ℕ → K`，归纳得以在 `ℕ` 上做（`List.range_succ` ＋ `List.prod_append`）。

  **⚠ 载体状态（L12）**：对应 `raw/AGPR2020.tex` `eq:10.3` 的组合内核；印刷页待目视核
  （`⚠-tex-sourced`）。
-/

import Procesi.PI.FormanekG

namespace Procesi

open Matrix

variable {K : Type*} [CommRing K] {N : ℕ}

/-- **链式矩阵单位之积**（`m+1` 个因子）：
`∏_{k≤m} E_{p (a+k), p (a+k+1)}(c (a+k)) = E_{p a, p (a+m+1)}(∏_{k≤m} c (a+k))`。 -/
theorem prod_chain_units (p : ℕ → Fin N) (c : ℕ → K) (a m : ℕ) :
    ((List.range (m + 1)).map (fun k =>
        Matrix.single (p (a + k)) (p (a + k + 1)) (c (a + k)))).prod
      = Matrix.single (p a) (p (a + m + 1)) (∏ k ∈ Finset.range (m + 1), c (a + k)) := by
  induction m generalizing a with
  | zero =>
    simp only [List.range_one, List.map_singleton, List.prod_singleton, Finset.prod_range_one,
      Nat.add_zero, Nat.zero_add]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp only [List.map_singleton, List.prod_singleton, Nat.add_succ]
    rw [Matrix.single_mul_single_same]
    congr 2
    simp only [Nat.succ_eq_add_one, Nat.add_zero]
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    ring

#print axioms prod_chain_units

/-- `a = 0` 的形态（词的链式求值直接用此式）。 -/
theorem word_chain_nat (p : ℕ → Fin N) (c : ℕ → K) (m : ℕ) :
    ((List.range (m + 1)).map (fun k => Matrix.single (p k) (p (k + 1)) (c k))).prod
      = Matrix.single (p 0) (p (m + 1)) (∏ k ∈ Finset.range (m + 1), c k) := by
  have h := prod_chain_units p c 0 m
  simpa using h

#print axioms word_chain_nat

/-- **链式求值**（AGPR `eq:10.3` 的收敛形态）：`X` 对角、`Y_k = E_{p k, p (k+1)}` 时，
整条词收敛成 `E_{p 0, p N}`，系数为各因子乘积（`N ≥ 1`）。 -/
theorem wordOf_chain (N : ℕ) (hN : 1 ≤ N) (n : ℕ → ℕ) (x : Fin N → K) (p : ℕ → Fin N) :
    wordOf (K := K) N n (Matrix.diagonal x)
        (fun i : Fin N => Matrix.single (p i) (p ((i : ℕ) + 1)) 1)
      = Matrix.single (p 0) (p N) (∏ k ∈ Finset.range (N + 1), (x (p k)) ^ (n k)) := by
  rw [wordOf]
  have hfac : ∀ k ∈ List.range N,
      (if h : k < N then
        (Matrix.diagonal x) ^ (n k) *
          (fun i : Fin N => Matrix.single (p i) (p ((i : ℕ) + 1)) 1) ⟨k, h⟩
       else 1)
      = Matrix.single (p k) (p (k + 1)) ((x (p k)) ^ (n k)) := by
    intro k hk
    have hlt : k < N := List.mem_range.mp hk
    rw [dif_pos hlt, diagonal_pow_mul_single, mul_one]
  rw [List.map_congr_left hfac]
  have hNm : N - 1 + 1 = N := by omega
  have hchain := word_chain_nat p (fun k => (x (p k)) ^ (n k)) (N - 1)
  rw [hNm] at hchain
  rw [hchain, single_mul_diagonal_pow]
  congr 2
  rw [Finset.prod_range_succ]

#print axioms wordOf_chain

end Procesi
