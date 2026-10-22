/-
  Procesi —— ★★★★★★★★★★ **非空洞性收口**：`Nonempty (GenericDivisionData F 2 9)` ＋ **非空洞的 H2**

  **本件解决的问题**（L1 在住性，[[deadend-genericCenter-eq-F]] §2–§3）：
  R774 的 `h2_unconditional` 形状是 `∀ D : GenericDivisionData F 2 9, …`，而结构束的
  **可居住性未机检** ⟹ 主定理有**空洞风险**（`∅-vacuous-risk`）。本件把这一条**消掉**。

  **两段**：
  1. ★ `adjoin_genericMatrix_map_eq_top`（`hspan`：`R·K = M_n(K)`，Saltman `lem:14.7` 的张成后果）
     —— 走**矩阵求逆**路线（**不用** `LinearIndependent`：`SField = OreLocalization` 的实例菱形
     会使 mathlib 的 LI 引理与本仓陈述**类型不同**）：
     `det M ≠ 0` ⟹ `M⁻¹ * M = 1` ⟹ `e_b = Σ_j (M⁻¹ b j) • (row_j M)`
     ⟹ 每个矩阵单位 `E_ab ∈ adjoin` ⟹ `X = Σ X a b • E_ab ∈ adjoin`。
  2. ★★ `nonempty_genericDivisionData_two`：`Nonempty (GenericDivisionData F 2 n)`（任意 `n ≥ 1`；
     `CharZero` 只用于 `λ_p = p` 互异）——经 `Cor148.nonempty_genericDivisionData_of_span`。
  3. ★★★★★★★★★★ `h2_unconditional_nonvacuous`：
     `Nonempty (GenericDivisionData F 2 9) ∧ ∀ D k₀ hk₀, ProcesiS9Hyp F ↥(ZCanon F 2 9 D)`。

  **射程（勿夸大）**：仓内已**无具名假设、无空洞风险**；但**论文侧**（`paper/` 的 `\cite`、
  `H2-named-hypothesis.patch` 末句仍写"仍假设 Procesi 定理"）**未对接**；
  Z 半／`M_n(K')^N ⊆ UDK'`／`UDKTensorHypK'` 仍未证（但都不在 H2 关键路径上）。
-/

import Procesi.GenericSpan
import Procesi.Cor148
import Procesi.UDKScalarMem


open Matrix

namespace Procesi

variable (F : Type) [Field F]

/-- `det (phiS.map ι) ≠ 0`（`ι` 单射 ＋ det 转移）。 -/
theorem det_phiS_map_ne_zero [CharZero F] (n : ℕ) :
    ((phiS F n).map (algebraMap (S F 2 n) (SField F 2 n))).det ≠ 0 := by
  have hconv : ((phiS F n).map (algebraMap (S F 2 n) (SField F 2 n))).det
      = algebraMap (S F 2 n) (SField F 2 n) ((phiS F n).det) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hconv]
  refine fun h => det_phiS_ne_zero F n (IsFractionRing.injective (S F 2 n) (SField F 2 n) ?_)
  rw [h, map_zero]

#print axioms det_phiS_map_ne_zero

/-- ★★★★★ **`hspan`：`R·K = M_n(K)`**（Saltman `lem:14.7` 的张成后果）。

机制（避开 `LinearIndependent`，只用矩阵求逆）：`det M ≠ 0` ⟹ `M * M⁻¹ = 1`
⟹ 每个矩阵单位 `E_pq` 是「`M` 的行的 `K`-线性组合」⟹ `E_pq` 落在 `adjoin` 里
⟹ 一切矩阵在 `adjoin` 里（`X = Σ X p q • E_pq`）。 -/
theorem adjoin_genericMatrix_map_eq_top [CharZero F] (n : ℕ) [NeZero n] :
    Algebra.adjoin (SField F 2 n)
      (Set.range (fun k : Fin 2 =>
        (genericMatrix F 2 n k).map (algebraMap (S F 2 n) (SField F 2 n)))) = ⊤ := by
  classical
  set ι : S F 2 n →+* SField F 2 n := algebraMap (S F 2 n) (SField F 2 n)
  set A : Subalgebra (SField F 2 n) (Matrix (Fin n) (Fin n) (SField F 2 n)) :=
    Algebra.adjoin (SField F 2 n)
      (Set.range (fun k : Fin 2 => (genericMatrix F 2 n k).map ι))
  set M : Matrix (Fin n × Fin n) (Fin n × Fin n) (SField F 2 n) := (phiS F n).map ι
  have hdet : M.det ≠ 0 := det_phiS_map_ne_zero F n
  -- (1) 每个词在 `A` 里
  have hrow : ∀ ij : Fin n × Fin n, (wWord F n ij.1 ij.2).map ι ∈ A := by
    intro ij
    have h0 : (genericMatrix F 2 n 0).map ι ∈ A := Algebra.subset_adjoin (Set.mem_range_self 0)
    have h1 : (genericMatrix F 2 n 1).map ι ∈ A := Algebra.subset_adjoin (Set.mem_range_self 1)
    have hp1 : ((genericMatrix F 2 n 0) ^ ij.1.val).map ι
        = ((genericMatrix F 2 n 0).map ι) ^ ij.1.val :=
      Matrix.map_pow (genericMatrix F 2 n 0) ι ij.1.val
    have hp2 : ((genericMatrix F 2 n 0) ^ ij.2.val).map ι
        = ((genericMatrix F 2 n 0).map ι) ^ ij.2.val :=
      Matrix.map_pow (genericMatrix F 2 n 0) ι ij.2.val
    have hmul : (wWord F n ij.1 ij.2).map ι
        = ((genericMatrix F 2 n 0).map ι) ^ ij.1.val * ((genericMatrix F 2 n 1).map ι)
          * ((genericMatrix F 2 n 0).map ι) ^ ij.2.val := by
      simp only [wWord, Matrix.map_mul, hp1, hp2]
    rw [hmul]
    exact A.mul_mem (A.mul_mem (A.pow_mem h0 _) h1) (A.pow_mem h0 _)
  -- (2) 每个矩阵单位在 `A` 里
  have hsingle : ∀ p q : Fin n, Matrix.single p q (1 : SField F 2 n) ∈ A := by
    intro p q
    have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
    have hentry : Matrix.single p q (1 : SField F 2 n)
        = ∑ j : Fin n × Fin n, (M⁻¹ (p, q) j) •
            ((fun p' q' : Fin n => M j (p', q')) : Matrix (Fin n) (Fin n) (SField F 2 n)) := by
      ext p' q'
      have h2 : (∑ j : Fin n × Fin n, (M⁻¹ (p, q) j) * M j (p', q'))
          = (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) (SField F 2 n)) (p, q) (p', q') := by
        rw [← h1, Matrix.mul_apply]
      simp only [Matrix.single_apply, Matrix.smul_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [h2, Matrix.one_apply]
      by_cases h : p = p' ∧ q = q'
      · rw [if_pos h, if_pos (by rw [Prod.mk.injEq]; exact h)]
      · rw [if_neg h, if_neg (fun hh => h ((Prod.mk.injEq p q p' q').mp hh))]
    rw [hentry]
    refine A.sum_mem (fun j _ => A.smul_mem ?_ _)
    have hMj : ((fun p' q' : Fin n => M j (p', q')) : Matrix (Fin n) (Fin n) (SField F 2 n))
        = (wWord F n j.1 j.2).map ι := rfl
    rw [hMj]
    exact hrow j
  -- (3) 一切矩阵在 `A` 里
  refine eq_top_iff.mpr (fun X _ => ?_)
  have hX : X = ∑ p : Fin n, ∑ q : Fin n, X p q • Matrix.single p q (1 : SField F 2 n) := by
    ext p' q'
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply]
    rw [Finset.sum_eq_single p']
    · rw [Finset.sum_eq_single q']
      · simp
      · intro q _ hq; simp [hq]
      · intro h; exact absurd (Finset.mem_univ q') h
    · intro p _ hp
      refine Finset.sum_eq_zero (fun q _ => ?_)
      have hp' : ¬(p = p') := hp
      simp [hp']
    · intro h; exact absurd (Finset.mem_univ p') h
  rw [hX]
  exact A.sum_mem (fun p _ => A.sum_mem (fun q _ => A.smul_mem (hsingle p q) _))

#print axioms adjoin_genericMatrix_map_eq_top



/-! ## 收口：`Nonempty (GenericDivisionData F 2 n)` 与**非空洞的 H2** -/

/-- ★★★ **结构束非空（无条件，任意 `CharZero` 域与维度 `n ≥ 1`）**。 -/
theorem nonempty_genericDivisionData_two [CharZero F] (n : ℕ) [NeZero n] :
    Nonempty (GenericDivisionData F 2 n) :=
  nonempty_genericDivisionData_of_span F (adjoin_genericMatrix_map_eq_top F n)

#print axioms nonempty_genericDivisionData_two

/-- ★★★ `n = 9` 的结构束非空。 -/
theorem nonempty_genericDivisionData_two_nine [CharZero F] :
    Nonempty (GenericDivisionData F 2 9) :=
  nonempty_genericDivisionData_two F 9

#print axioms nonempty_genericDivisionData_two_nine

/-- ★★★★★★★★★★ **H2：非空洞的无条件定理** —— 结构束可居住 ＋ 对每个 `D` 结论成立。 -/
theorem h2_unconditional_nonvacuous [CharZero F] [Nonempty (Fin 9)] :
    Nonempty (GenericDivisionData F 2 9) ∧
      ∀ (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0),
        ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  ⟨nonempty_genericDivisionData_two_nine F,
    fun D k₀ hk₀ => h2_unconditional F D k₀ hk₀⟩

#print axioms h2_unconditional_nonvacuous

end Procesi
