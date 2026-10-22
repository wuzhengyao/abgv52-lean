/-
  Procesi —— **PI 基础设施（S2a）：AGPR2020 `eq:10.5` 的 `g` 与端点恒等式**

  **来源（逐字）**：`raw/AGPR2020.tex` §10.2：
  * `eq:10.5`：`g(x_1,…,x_{n+1}) = ∏_{2≤i≤n}(x_1-x_i)(x_{n+1}-x_i) · ∏_{2≤i<j≤n}(x_i-x_j)^2`；
  * `thm:10.2.4` 的证明用它：在链条件成立处 `g` 取值 `= Δ²`（`Δ = ∏_{i<j}(x_i - x_j)`），
    且 `G` 的 `n` 个循环平移之和给出 `Δ²·1_n`。

  **本件（S2a）**：镜像对角律（`single_mul_diagonal`／`_pow`）＋ 指标集 `midSet` ＋
  `gPoly`（`eq:10.5` 的逐字翻译，指标 `Fin (N+1)`，`0` 与 `N` 为"两端"、`1..N-1` 为中间）
  ＋ `deltaSq`（`Δ²`，按 `g` 的因子顺序排列）＋ **端点恒等式** `g.eval z = Δ²`（当 `z N = z 0`）
  ＋ **`Δ² ≠ 0`**（整环上，互异假设）。

  **工艺**：`Δ²` **按 `g` 的因子顺序**定义（split form），端点恒等式遂为
  `z N = z 0` 代入 ＋ `ring`；若改按字典序 `∏_{i<j}(zᵢ-zⱼ)²` 定义则须做一次
  Finset 重排（本节避开）。

  **⚠ 载体状态（L12）**：陈述取自 `raw/AGPR2020.tex`（用户由 PDF 转化）；**印刷页尚未目视核**
  ⟹ `⚠-tex-sourced`，引用定案前回 `raw/AGPR2020.pdf` 核 `eq:10.5`／`thm:10.2.4`。
-/

import Procesi.PI.CentralPoly
import Mathlib.Algebra.MvPolynomial.Eval

namespace Procesi

open Matrix

variable {K : Type*} [CommRing K]

/-- 矩阵单位乘对角：`E_{pq}(r) * diag x = E_{pq}(r * x q)`。 -/
theorem single_mul_diagonal {N : ℕ} (x : Fin N → K) (p q : Fin N) (r : K) :
    Matrix.single p q r * Matrix.diagonal x = Matrix.single p q (r * x q) := by
  ext a b
  simp only [Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne, Matrix.diagonal_apply,
    Matrix.single, Matrix.of_apply]
  by_cases ha : p = a
  · subst ha
    by_cases hb : b = q
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · simp [ha]

#print axioms single_mul_diagonal

/-- 矩阵单位乘对角幂：`E_{pq}(r) * (diag x)^a = E_{pq}(r * (x q)^a)`。 -/
theorem single_mul_diagonal_pow {N : ℕ} (x : Fin N → K) (a : ℕ) (p q : Fin N) (r : K) :
    Matrix.single p q r * Matrix.diagonal x ^ a = Matrix.single p q (r * (x q) ^ a) := by
  induction a generalizing r with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, single_mul_diagonal, mul_assoc, ← pow_succ]

#print axioms single_mul_diagonal_pow

/-- 中间指标集 `{1, …, N-1} ⊆ Fin (N+1)`（`g` 的乘积指标）。 -/
def midSet (N : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun i => i ≠ 0 ∧ i ≠ Fin.last N)

/-- AGPR2020 `eq:10.5` 的 `g`（逐字）：
`g = ∏_{i∈mid} (x_0 - x_i)(x_N - x_i) · ∏_{i<j ∈ mid} (x_i - x_j)^2`。 -/
noncomputable def gPoly (K : Type*) [CommRing K] (N : ℕ) : MvPolynomial (Fin (N + 1)) K :=
  (∏ i ∈ midSet N, ((MvPolynomial.X (0 : Fin (N + 1)) - MvPolynomial.X i) *
      (MvPolynomial.X (Fin.last N) - MvPolynomial.X i))) *
    ∏ i ∈ midSet N, ∏ j ∈ (midSet N).filter (fun j => i < j),
      (MvPolynomial.X i - MvPolynomial.X j) ^ 2

/-- AGPR 的 `Δ²`（Vandermonde 平方，按 `g` 的因子顺序排列）。 -/
noncomputable def deltaSq {K : Type*} [CommRing K] (N : ℕ) (z : Fin (N + 1) → K) : K :=
  (∏ i ∈ midSet N, (z 0 - z i) ^ 2) *
    ∏ i ∈ midSet N, ∏ j ∈ (midSet N).filter (fun j => i < j), (z i - z j) ^ 2

/-- **端点恒等式**：`z` 的最后一个分量等于第 `0` 个时，`g.eval z = Δ²`
（AGPR `thm:10.2.4` 证明的代数内核）。 -/
theorem gPoly_eval_of_last_eq (N : ℕ) (z : Fin (N + 1) → K)
    (hz : z (Fin.last N) = z 0) :
    (MvPolynomial.eval z) (gPoly K N) = deltaSq N z := by
  rw [gPoly, deltaSq]
  simp only [map_mul, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  rw [hz]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)

#print axioms gPoly_eval_of_last_eq

/-- `Δ² ≠ 0`（整环 ＋ 互异假设）。 -/
theorem deltaSq_ne_zero [IsDomain K] (N : ℕ) (z : Fin (N + 1) → K)
    (h0 : ∀ i ∈ midSet N, z 0 ≠ z i)
    (hmid : ∀ i ∈ midSet N, ∀ j ∈ (midSet N).filter (fun j => i < j), z i ≠ z j) :
    deltaSq N z ≠ 0 := by
  rw [deltaSq]
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero 2 (sub_ne_zero.mpr (h0 i hi))
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hmid i hi j hj))

#print axioms deltaSq_ne_zero

/-- **消失性（左端因子）**：`z 0 = z i`（`i` 为中间指标）⟹ `g.eval z = 0`。 -/
theorem gPoly_eval_eq_zero_of_left (N : ℕ) (z : Fin (N + 1) → K)
    {i : Fin (N + 1)} (hi : i ∈ midSet N) (h : z 0 = z i) :
    (MvPolynomial.eval z) (gPoly K N) = 0 := by
  rw [gPoly]
  simp only [map_mul, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  have hz : (∏ i ∈ midSet N, ((z 0 - z i) * (z (Fin.last N) - z i))) = 0 :=
    Finset.prod_eq_zero hi (by rw [h, sub_self, zero_mul])
  rw [hz, zero_mul]

#print axioms gPoly_eval_eq_zero_of_left

/-- **消失性（右端因子）**：`z N = z i`（`i` 为中间指标）⟹ `g.eval z = 0`。 -/
theorem gPoly_eval_eq_zero_of_right (N : ℕ) (z : Fin (N + 1) → K)
    {i : Fin (N + 1)} (hi : i ∈ midSet N) (h : z (Fin.last N) = z i) :
    (MvPolynomial.eval z) (gPoly K N) = 0 := by
  rw [gPoly]
  simp only [map_mul, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  have hz : (∏ i ∈ midSet N, ((z 0 - z i) * (z (Fin.last N) - z i))) = 0 :=
    Finset.prod_eq_zero hi (by rw [h, sub_self, mul_zero])
  rw [hz, zero_mul]

#print axioms gPoly_eval_eq_zero_of_right

/-- **消失性（中间对因子）**：`z i = z j`（`i < j`，均中间）⟹ `g.eval z = 0`。 -/
theorem gPoly_eval_eq_zero_of_mid (N : ℕ) (z : Fin (N + 1) → K)
    {i j : Fin (N + 1)} (hi : i ∈ midSet N) (hj : j ∈ (midSet N).filter (fun j => i < j))
    (h : z i = z j) :
    (MvPolynomial.eval z) (gPoly K N) = 0 := by
  rw [gPoly]
  simp only [map_mul, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  have hz : (∏ i ∈ midSet N, ∏ j ∈ (midSet N).filter (fun j => i < j), (z i - z j) ^ 2) = 0 :=
    Finset.prod_eq_zero hi
      (Finset.prod_eq_zero hj (by rw [h, sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0)]))
  rw [hz, mul_zero]

#print axioms gPoly_eval_eq_zero_of_mid

/-- `Fin N` 上的**全对 Vandermonde 平方**（规范形：与"窗口"选取无关）。 -/
noncomputable def vanderAll (N : ℕ) (y : Fin N → K) : K :=
  ∏ i : Fin N, ∏ j ∈ (Finset.univ.filter (fun j : Fin N => i < j)), (y i - y j) ^ 2

/-- `midSet N`（`g` 的中间指标）与 `Fin N \ {0}` 通过 `castSucc` 一一对应。 -/
theorem midSet_eq_image (N : ℕ) [NeZero N] :
    midSet N = (Finset.univ.erase (0 : Fin N)).image (Fin.castSucc (n := N)) := by
  ext i
  constructor
  · intro hi
    rw [midSet, Finset.mem_filter] at hi
    obtain ⟨-, h0, hlast⟩ := hi
    refine Finset.mem_image.mpr ⟨⟨i.1, ?_⟩, ?_, ?_⟩
    · have : (i : ℕ) ≠ N := by
        intro h; exact hlast (Fin.ext h)
      omega
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      exact h0 (Fin.ext (by simpa using congrArg Fin.val h))
    · exact Fin.ext rfl
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_erase] at hj
    rw [midSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h
      exact hj.1 (Fin.ext (by simpa using congrArg Fin.val h))
    · intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at h2
      omega

#print axioms midSet_eq_image

theorem castSucc_mem_midSet (N : ℕ) [NeZero N] {i : Fin N} (hi : i ≠ 0) :
    Fin.castSucc i ∈ midSet N := by
  rw [midSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro h
    exact hi (Fin.ext (by simpa using congrArg Fin.val h))
  · intro h
    have h2 := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at h2
    omega

theorem filter_zero_lt_eq_erase (N : ℕ) [NeZero N] :
    (Finset.univ.filter (fun j : Fin N => (0 : Fin N) < j)) = Finset.univ.erase (0 : Fin N) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro h
    refine ⟨?_, trivial⟩
    rintro rfl
    rw [Fin.lt_def, Fin.val_zero] at h
    omega
  · rintro ⟨h, -⟩
    rw [Fin.lt_def, Fin.val_zero]
    exact Nat.pos_of_ne_zero (fun h0 => h (Fin.ext (by simpa using h0)))

theorem inner_bij (N : ℕ) [NeZero N] (z : Fin (N + 1) → K) (a : Fin N) :
    (∏ j ∈ (Finset.univ.filter (fun j : Fin N => a < j)),
        (z a.castSucc - z j.castSucc) ^ 2)
      = ∏ b ∈ (midSet N).filter (fun b => Fin.castSucc a < b), (z a.castSucc - z b) ^ 2 := by
  refine Finset.prod_bij (fun j _ => Fin.castSucc j) ?_ ?_ ?_ ?_
  · intro j hj
    have hja : a < j := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨castSucc_mem_midSet N ?_, Fin.castSucc_lt_castSucc_iff.mpr hja⟩
    rintro rfl
    rw [Fin.lt_def, Fin.val_zero] at hja
    omega
  · intro a₁ _ a₂ _ h
    exact Fin.castSucc_injective N h
  · intro b hb
    obtain ⟨hbmid, hblt⟩ := Finset.mem_filter.mp hb
    have hb_lt : b.val < N := by
      have h := b.isLt
      have hb2 : b ≠ Fin.last N := (Finset.mem_filter.mp hbmid).2.2
      by_contra hc
      exact hb2 (Fin.ext (by simp only [Fin.val_last]; omega))
    have hb0 : (⟨b.val, hb_lt⟩ : Fin N) ≠ 0 := by
      rintro h
      have hb2 : b ≠ 0 := (Finset.mem_filter.mp hbmid).2.1
      exact hb2 (Fin.ext (by simpa using congrArg Fin.val h))
    refine ⟨⟨b.val, hb_lt⟩, ?_, Fin.ext rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Fin.castSucc_lt_castSucc_iff.mp hblt⟩
  · intro j _
    rfl

#print axioms inner_bij

/-- 从 `midSet` 元素取出 `Fin N` 的像（`b ≠ last` 给出值界）。 -/
theorem mid_to_fin_val (N : ℕ) [NeZero N] {b : Fin (N + 1)} (hb : b ∈ midSet N) : b.val < N := by
  have h := b.isLt
  have hb2 : b ≠ Fin.last N := (Finset.mem_filter.mp hb).2.2
  by_contra hc
  exact hb2 (Fin.ext (by simp only [Fin.val_last]; omega))

theorem mid_to_fin_ne (N : ℕ) [NeZero N] {b : Fin (N + 1)} (hb : b ∈ midSet N) :
    (⟨b.val, mid_to_fin_val N hb⟩ : Fin N) ≠ 0 := by
  rintro h
  have hb2 : b ≠ 0 := (Finset.mem_filter.mp hb).2.1
  exact hb2 (Fin.ext (by simpa using congrArg Fin.val h))

/-- 外层重索引（第一因子）：`midSet → univ.erase 0`。 -/
theorem h1_bridge (N : ℕ) [NeZero N] (z : Fin (N + 1) → K) :
    (∏ i ∈ midSet N, (z 0 - z i) ^ 2)
      = ∏ a ∈ Finset.univ.erase (0 : Fin N), (z 0 - z a.castSucc) ^ 2 := by
  refine Finset.prod_bij (fun b hb => (⟨b.val, mid_to_fin_val N hb⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_erase.mpr ⟨mid_to_fin_ne N hb, Finset.mem_univ _⟩
  · intro b₁ hb₁ b₂ hb₂ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro a ha
    refine ⟨Fin.castSucc a, castSucc_mem_midSet N (Finset.mem_erase.mp ha).1, ?_⟩
    exact Fin.ext rfl
  · intro b hb
    rfl

#print axioms h1_bridge

/-- 外层重索引（第二因子）：`midSet → univ.erase 0` ＋ 内层 `inner_bij`。 -/
theorem h2_bridge (N : ℕ) [NeZero N] (z : Fin (N + 1) → K) :
    (∏ i ∈ midSet N, ∏ j ∈ (midSet N).filter (fun j => i < j), (z i - z j) ^ 2)
      = ∏ a ∈ Finset.univ.erase (0 : Fin N),
          ∏ j ∈ (Finset.univ.filter (fun j : Fin N => a < j)),
            (z a.castSucc - z j.castSucc) ^ 2 := by
  refine Finset.prod_bij (fun b hb => (⟨b.val, mid_to_fin_val N hb⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_erase.mpr ⟨mid_to_fin_ne N hb, Finset.mem_univ _⟩
  · intro b₁ hb₁ b₂ hb₂ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro a ha
    refine ⟨Fin.castSucc a, castSucc_mem_midSet N (Finset.mem_erase.mp ha).1, ?_⟩
    exact Fin.ext rfl
  · intro b hb
    exact (inner_bij N z (⟨b.val, mid_to_fin_val N hb⟩ : Fin N)).symm

#print axioms h2_bridge

/-- ★ **规范形桥**：`Δ²` 等于前 `N` 个分量的全对 Vandermonde 平方。 -/
theorem deltaSq_eq_vanderAll (N : ℕ) [NeZero N] (z : Fin (N + 1) → K) :
    deltaSq N z = vanderAll N (fun i : Fin N => z i.castSucc) := by
  rw [deltaSq, vanderAll, h1_bridge, h2_bridge]
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin N))
    (fun i => ∏ j ∈ (Finset.univ.filter (fun j : Fin N => i < j)),
      (z i.castSucc - z j.castSucc) ^ 2) (Finset.mem_univ (0 : Fin N))]
  have hF0 : (∏ j ∈ (Finset.univ.filter (fun j : Fin N => (0 : Fin N) < j)),
      (z (0 : Fin N).castSucc - z j.castSucc) ^ 2)
      = ∏ a ∈ Finset.univ.erase (0 : Fin N), (z 0 - z a.castSucc) ^ 2 := by
    rw [filter_zero_lt_eq_erase]
    rfl
  rw [hF0, mul_comm]

#print axioms deltaSq_eq_vanderAll

/-- **嵌套积 ↔ 对积**：`Fin N` 上的嵌套积等于在 `Fin N × Fin N` 上按 `p.1 < p.2` 筛选的对积。 -/
theorem prod_nested_eq_prod_pairs (N : ℕ) (f : Fin N → Fin N → K) :
    (∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j : Fin N => i < j), f i j)
      = ∏ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2), f p.1 p.2 := by
  have h : (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
      = (Finset.univ ×ˢ Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2) := by
    simp
  rw [h, Finset.prod_filter]
  conv_rhs => rw [Finset.prod_product]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_filter]

#print axioms prod_nested_eq_prod_pairs

/-- `vanderAll` 的**对形式**。 -/
theorem vanderAll_eq_pair (N : ℕ) (y : Fin N → K) :
    vanderAll N y
      = ∏ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
          (y p.1 - y p.2) ^ 2 := by
  rw [vanderAll, prod_nested_eq_prod_pairs]

#print axioms vanderAll_eq_pair

/-- ★ **`vanderAll` 的置换不变性**（`prod_bij'`，带显式逆）。 -/
theorem vanderAll_comp_perm (N : ℕ) (y : Fin N → K) (σ : Equiv.Perm (Fin N)) :
    vanderAll N (fun i => y (σ i)) = vanderAll N y := by
  rw [vanderAll_eq_pair, vanderAll_eq_pair]
  refine Finset.prod_bij'
    (fun p _ => if σ p.1 < σ p.2 then (σ p.1, σ p.2) else (σ p.2, σ p.1))
    (fun q _ => if σ.symm q.1 < σ.symm q.2 then (σ.symm q.1, σ.symm q.2)
      else (σ.symm q.2, σ.symm q.1)) ?_ ?_ ?_ ?_ ?_
  · -- hi：像在筛内
    intro p hp
    have hp12 : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
    have hne : σ p.1 ≠ σ p.2 := fun he => hp12 (σ.injective he)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · rw [if_neg (not_lt.mpr (le_of_lt h))]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · -- hj：逆像在筛内
    intro q hq
    have hq12 : q.1 ≠ q.2 := ne_of_lt (Finset.mem_filter.mp hq).2
    have hne : σ.symm q.1 ≠ σ.symm q.2 := fun he => hq12 (σ.symm.injective he)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · rw [if_neg (not_lt.mpr (le_of_lt h))]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · -- left_inv：j (i p) = p
    intro p hp
    have hp2 : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hp12 : p.1 ≠ p.2 := ne_of_lt hp2
    have hne : σ p.1 ≠ σ p.2 := fun he => hp12 (σ.injective he)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h,
        if_pos (by rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact hp2)]
      exact Prod.ext (Equiv.symm_apply_apply σ p.1) (Equiv.symm_apply_apply σ p.2)
    · rw [if_neg (not_lt.mpr (le_of_lt h)),
        if_neg (by rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
                   exact not_lt.mpr (le_of_lt hp2))]
      exact Prod.ext (Equiv.symm_apply_apply σ p.1) (Equiv.symm_apply_apply σ p.2)
  · -- right_inv：i (j q) = q
    intro q hq
    have hq2 : q.1 < q.2 := (Finset.mem_filter.mp hq).2
    have hq12 : q.1 ≠ q.2 := ne_of_lt hq2
    have hne : σ.symm q.1 ≠ σ.symm q.2 := fun he => hq12 (σ.symm.injective he)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h,
        if_pos (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hq2)]
      exact Prod.ext (Equiv.apply_symm_apply σ q.1) (Equiv.apply_symm_apply σ q.2)
    · rw [if_neg (not_lt.mpr (le_of_lt h)),
        if_neg (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
                   exact not_lt.mpr (le_of_lt hq2))]
      exact Prod.ext (Equiv.apply_symm_apply σ q.1) (Equiv.apply_symm_apply σ q.2)
  · -- h：值相容
    intro p hp
    have hp12 : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
    have hne : σ p.1 ≠ σ p.2 := fun he => hp12 (σ.injective he)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h]
    · rw [if_neg (not_lt.mpr (le_of_lt h))]
      ring

#print axioms vanderAll_comp_perm

end Procesi
