/-
  Procesi —— **库内缺件的补齐件：`MvPolynomial.totalDegree` 在整环上对乘法可加**

  **为何自建（L46／L47 内容式检索结论）**：`mathlib` 的 `MvPolynomial.totalDegree_mul`
  （`Mathlib/Algebra/MvPolynomial/Degrees.lean:503`）只有**不等式** `(a*b).totalDegree ≤ …`；
  而 Saltman `lem:14.13` 的"`φ_A(g)` 与 `g` 同次 ⟹ 商为常数"一步**需要等号**。
  内容式检索（`totalDegree` × `mul` × `eq`／`homogeneousComponent` × `mul`）在 pin `aa35a481`
  无等号版，故本件给出。

  **路线**：`coeff_homogeneousComponent`（`RingTheory/MvPolynomial/Homogeneous.lean:526`）
  证最高次分量可乘 `homogeneousComponent_mul_top`，再由"最高次分量非零 ⟹ 有该次单项式"
  与 `le_totalDegree` 收 `≥`；`≤` 由 mathlib 的 `totalDegree_mul`。

  **用途**：`lem:14.13`（S3）的 §3 次数步；`φ_A` 是线性替换 ⟹ 保总次数。
-/
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Weight

open MvPolynomial

namespace Procesi

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- `totalDegree` 是支撑集上单次数的上确界（`Finsupp.degree` 形态）。 -/
lemma totalDegree_eq_sup (p : MvPolynomial σ R) :
    p.totalDegree = p.support.sup (fun m => m.degree) := by
  rw [totalDegree_eq]
  congr 1
  funext m
  rw [Finsupp.card_toMultiset]
  rfl

#print axioms totalDegree_eq_sup

/-- 非零多项式有达到最高次的不定元单项式。 -/
lemma exists_support_totalDegree {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ d ∈ p.support, d.degree = p.totalDegree := by
  have hne : p.support.Nonempty := by
    simpa [Finset.not_nonempty_iff_eq_empty, support_eq_empty] using hp
  obtain ⟨d, hdmem, hdsup⟩ := Finset.exists_mem_eq_sup p.support hne (fun m => m.degree)
  exact ⟨d, hdmem, by rw [← hdsup, ← totalDegree_eq_sup]⟩

#print axioms exists_support_totalDegree

/-- ★ **非零多项式的最高次分量非零**。 -/
lemma homogeneousComponent_totalDegree_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  obtain ⟨d, hdmem, hddeg⟩ := exists_support_totalDegree hp
  intro h
  have hcoeff : (homogeneousComponent p.totalDegree p).coeff d = p.coeff d := by
    rw [coeff_homogeneousComponent, if_pos hddeg]
  rw [h] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact (mem_support_iff.mp hdmem) hcoeff.symm

#print axioms homogeneousComponent_totalDegree_ne_zero

/-- `homogeneousComponent n φ ≠ 0` ⟹ 有 `n` 次系数非零的单项式。 -/
lemma exists_coeff_of_homogeneousComponent_ne_zero {n : ℕ}
    {φ : MvPolynomial σ R} (h : homogeneousComponent n φ ≠ 0) :
    ∃ d : σ →₀ ℕ, d.degree = n ∧ φ.coeff d ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  ext d
  rw [coeff_homogeneousComponent]
  by_cases hd : d.degree = n
  · simp [hd, hc d hd]
  · simp [hd]

#print axioms exists_coeff_of_homogeneousComponent_ne_zero

/-- ★★★ **`hc` 的最高次分量可乘**：`hc_{a+b}(p*q) = hc_a p * hc_b q`（`a = deg p`, `b = deg q`）。 -/
theorem homogeneousComponent_mul_top [DecidableEq σ] [NoZeroDivisors R]
    (p q : MvPolynomial σ R) :
    homogeneousComponent (p.totalDegree + q.totalDegree) (p * q)
      = homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  simp only [coeff_homogeneousComponent]
  by_cases hd : d.degree = p.totalDegree + q.totalDegree
  · rw [if_pos hd]
    refine Finset.sum_congr rfl ?_
    rintro ⟨e, f⟩ hx
    rw [Finset.mem_antidiagonal] at hx
    have hsum : e.degree + f.degree = d.degree := by rw [← map_add, hx]
    by_cases he : e.degree = p.totalDegree
    · by_cases hf : f.degree = q.totalDegree
      · rw [if_pos he, if_pos hf]
      · rw [if_pos he, if_neg hf, mul_zero]
        by_cases hq : q.coeff f = 0
        · rw [hq, mul_zero]
        · exfalso
          have hf_le : f.degree ≤ q.totalDegree := le_totalDegree (mem_support_iff.mpr hq)
          omega
    · rw [if_neg he, zero_mul]
      by_cases hq : q.coeff f = 0
      · rw [hq, mul_zero]
      · by_cases hp : p.coeff e = 0
        · rw [hp, zero_mul]
        · exfalso
          have hpe : e.degree ≤ p.totalDegree := le_totalDegree (mem_support_iff.mpr hp)
          have hqf : f.degree ≤ q.totalDegree := le_totalDegree (mem_support_iff.mpr hq)
          omega
  · rw [if_neg hd]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨e, f⟩ hx
    rw [Finset.mem_antidiagonal] at hx
    have hsum : e.degree + f.degree = d.degree := by rw [← map_add, hx]
    by_cases he : e.degree = p.totalDegree
    · by_cases hf : f.degree = q.totalDegree
      · omega
      · rw [if_pos he, if_neg hf, mul_zero]
    · rw [if_neg he, zero_mul]

#print axioms homogeneousComponent_mul_top

/-- ★★★ **`totalDegree` 在整环上对乘法可加**（mathlib 只有 `≤`，`Degrees.lean:503`）。 -/
theorem totalDegree_mul_eq [DecidableEq σ] [NoZeroDivisors R] {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).totalDegree = p.totalDegree + q.totalDegree := by
  refine le_antisymm (totalDegree_mul p q) ?_
  have h3 : homogeneousComponent (p.totalDegree + q.totalDegree) (p * q) ≠ 0 := by
    rw [homogeneousComponent_mul_top]
    exact mul_ne_zero (homogeneousComponent_totalDegree_ne_zero hp)
      (homogeneousComponent_totalDegree_ne_zero hq)
  obtain ⟨d, hddeg, hdcoeff⟩ := exists_coeff_of_homogeneousComponent_ne_zero h3
  calc p.totalDegree + q.totalDegree = d.degree := hddeg.symm
    _ ≤ (p * q).totalDegree := le_totalDegree (mem_support_iff.mpr hdcoeff)

#print axioms totalDegree_mul_eq
end Procesi
