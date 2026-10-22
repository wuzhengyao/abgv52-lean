/-
  Procesi —— **(C2) `lem:14.20` 的准备层：Saltman 的 `M_r'`、`f'` 与环面权**

  源（`raw/Saltman1999ch14.tex:365–390`／印刷 p.110，逐字）：
  > Set `M_r' = ⊕_{k=1}^r B ⊕ ℤ[G/H]`. … Define `f' : M_r' → I[G/H]` by `f'(u_i) = 0` and
  > `f'(u_ijk) = u_i − u_j`. Of course, `M_r ⊂ M_r'` is the kernel. …
  > If `B ∈ T_n` is a diagonal matrix with `(b_1,…,b_n)` down the diagonal, then the `i,i`
  > entry of `B^{-1}XB` is `x_ii` again and the `i,j` entry of `B^{-1}Y_kB` is
  > `b_i^{-1}b_j y_ijk`. More generally, if `m ∈ M_r'` and `f'(m) = Σ_i c(i)u_i` then
  > `φ_B(e(m)) = (∏_i b_i^{-c(i)}) e(m)`. …
  > **`lem:14.20`**: `F(M_r) = F(M_r')^T`.

  **本件的射程（`n = 9`, `r = 2`）**：只做**准备层**——把 `M_2'`、`f'`、其核与 `M ⊕ U` 的
  关系、以及环面权 `wt`（含**乘性**）机检。`lem:14.20` 本身（`F(M_2')^T = F(M_2)`）在下一件。

  **索引说明**（见 [[proj-H2-procesi-theorem-skeleton]] §2）：印刷版此处为 `⊕_{k=1}^r B`，
  经用户裁决为**印刷错误**，`raw/Saltman1999ch14.tex` 已更正为 `⊕_{k=2}^r B`（带 `% [KB 勘误]`
  注释，偏差登记于 `raw/Saltman1999ch14.receipt.json`）。故 `r = 2` 时 `M_2' = B ⊕ U`
  （**一份** `B`：份数 ＝ 非对角通用矩阵的个数 `r−1`）；`M_2 = ker f' = ker φ ⊕ U = M ⊕ U`（秩 82）。
-/
import Procesi.Saltman
import ABGV52.D1_ABGV52

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

universe u

/-! ## §1 Saltman 的 `M_2'` 与 `f'`（`n = 9`, `r = 2`） -/

/-- Saltman 的 `M_2' = B ⊕ ℤ[G/H]`（`r = 2`：一份 `B` 对应通用矩阵 `Y_2`）。 -/
abbrev Mprime : Type := BSaltman × ZGH

/-- Saltman 的 `f' : M_2' → I[G/H]`：`f'(u_ij) = u_i − u_j`、`f'(u_i) = 0`。 -/
def fPrime : Mprime →ₗ[ℤ] G.ZOm 3 where
  toFun x := G.phiFun 3 x.1
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

/-- `f'` 只依赖第一分量，且就是 `φ`。 -/
theorem fPrime_apply (x : Mprime) : fPrime x = G.phiFun 3 x.1 := rfl

/-- ★ **`M_2 = ker f' = M ⊕ U`**：`ker f' ≃ₗ M_2`（`M_2` 即本工作区的 `M ⊕ U`）。 -/
def kerFPrimeEquiv : ↥(LinearMap.ker fPrime) ≃ₗ[ℤ] ProcLat.Mp2 3 where
  toFun x := (⟨x.1.1, by
    have h : G.phiFun 3 x.1.1 = 0 := x.2
    simpa [fPrime] using h⟩, x.1.2)
  invFun y := ⟨(y.1.1, y.2), by
    show G.phiFun 3 y.1.1 = 0
    exact y.1.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 核的秩：`rank (M_2') - rank I[G/H] = 90 - 8 = 82`。
（另证：直接由 `kerFPrimeEquiv` ＋ `finrank_Z_Mp2`。） -/
theorem rank_kerFPrime : Module.finrank ℤ ↥(LinearMap.ker fPrime) = 82 := by
  rw [LinearEquiv.finrank_eq kerFPrimeEquiv, finrank_Z_Mp2]

/-! ## §2 环面权（Saltman 的 `∏ b_i^{-c(i)}`） -/

/-- **环面权**：对 `b ∈ T = (Fin 9 → Fˣ)` 与 `z = Σ_i c(i)u_i ∈ ℤ[G/H]`，
`wt b z = ∏_i b_i^{c(i)}`（Saltman 的 `∏ b_i^{-c(i)}` 取逆号不影响核）。 -/
def wt (F : Type u) [Field F] (b : Fin 9 → Fˣ) (z : G.ZOm 3) : Fˣ :=
  ∏ i : G.OmegaP 3, b i ^ (MonoidAlgebra.coeff z i)

/-- 权的单位元：`wt b 0 = 1`。 -/
theorem wt_zero (F : Type u) [Field F] (b : Fin 9 → Fˣ) : wt F b 0 = 1 := by
  simp [wt]

/-- ★ **权是 `ℤ[G/H]` 的加法特征**：`wt b (z + w) = wt b z * wt b w`。 -/
theorem wt_add (F : Type u) [Field F] (b : Fin 9 → Fˣ) (z w : G.ZOm 3) :
    wt F b (z + w) = wt F b z * wt F b w := by
  simp only [wt, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [zpow_add]

/-- 权在 `M_2'` 上的形式：`wt b (f' m)`。 -/
def wtM (F : Type u) [Field F] (b : Fin 9 → Fˣ) (m : Mprime) : Fˣ :=
  wt F b (fPrime m)

/-- `wtM` 对 `M_2'` 的加法**乘性**（这是环面作用的群同态性）。 -/
theorem wtM_add (F : Type u) [Field F] (b : Fin 9 → Fˣ) (m n : Mprime) :
    wtM F b (m + n) = wtM F b m * wtM F b n := by
  simp only [wtM, map_add, wt_add]

/-- **核上的权平凡**：`m ∈ M_2 = ker f'` ⟹ `wtM b m = 1`。 -/
theorem wtM_eq_one_of_mem_ker (F : Type u) [Field F] (b : Fin 9 → Fˣ)
    (m : Mprime) (hm : m ∈ LinearMap.ker fPrime) : wtM F b m = 1 := by
  simp only [wtM, LinearMap.mem_ker] at hm ⊢
  rw [hm, wt_zero]


/-! ## §2b 特征分离（`lem:14.20` 的 `(⊆)` 方向所需）

Saltman 的证明需要「若 `z ≠ 0`，则存在环面元 `b` 使 `wt b z ≠ 1`」（否则不同的权无法分离，
`f/g` 论证与权重分解都失效）。本区给出该分离引理及其算术核心。

核心算术事实：**`char F = 0` 时，`2^c ≠ 1` 对一切非零整数 `c` 成立**——取 `b` 在某个
`z.coeff ≠ 0` 的坐标上为 `2` 即可把该坐标的权打成非平凡。
-/

theorem two_zpow_ne_one (F : Type) [Field F] [CharZero F] {c : ℤ} (hc : c ≠ 0) :
    (2 : F) ^ c ≠ 1 := by
  have h2m : ∀ m : ℕ, (2 : F) ^ m = ((2 ^ m : ℕ) : F) :=
    fun m => (Nat.cast_pow (α := F) 2 m).symm
  have hpow : ∀ m : ℕ, 1 ≤ m → (2 : F) ^ m ≠ 1 := by
    intro m hm1 h
    have h' : ((2 ^ m : ℕ) : F) = 1 := by rw [← h2m m, h]
    have h2' : 2 ^ m = 1 := by exact_mod_cast h'
    have h2'' : 1 < 2 ^ m := Nat.one_lt_pow (n := m) (by omega) (by norm_num)
    omega
  rcases Int.eq_nat_or_neg c with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact hpow m (by omega)
  · have hm1 : 1 ≤ m := by omega
    rw [zpow_neg, zpow_natCast]
    intro h
    exact hpow m hm1 (inv_eq_one.mp h)

theorem exists_wt_ne_one (F : Type) [Field F] [CharZero F] (z : G.ZOm 3) (hz : z ≠ 0) :
    ∃ b : G.OmegaP 3 → Fˣ, wt F b z ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i : G.OmegaP 3, MonoidAlgebra.coeff z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by ext j; simpa using h j)
  set u : Fˣ := Units.mk0 (2 : F) (by norm_num) with hu
  refine ⟨fun j => if j = i then u else 1, ?_⟩
  have hsingle : (Finset.univ.prod fun j : G.OmegaP 3 =>
        (if j = i then u else 1) ^ (MonoidAlgebra.coeff z j))
      = (if i = i then u else 1) ^ (MonoidAlgebra.coeff z i) := by
    refine Finset.prod_eq_single i ?_ ?_
    · intro j _ hj
      simp [hj]
    · intro hM
      exact absurd (Finset.mem_univ i) hM
  have hprod : wt F (fun j => if j = i then u else 1) z
      = u ^ (MonoidAlgebra.coeff z i) := by
    simp only [wt]
    rw [hsingle]
    simp
  rw [hprod]
  intro h1
  have h2 : ((u : Fˣ) : F) ^ (MonoidAlgebra.coeff z i) = 1 := by
    have h3 : (((u ^ (MonoidAlgebra.coeff z i)) : Fˣ) : F) = 1 := by rw [h1]; rfl
    simpa using h3
  exact two_zpow_ne_one F hi h2

#print axioms two_zpow_ne_one
#print axioms exists_wt_ne_one


/-! ## §2c 环面作用与「不动元只含零权单项式」

把 Saltman 的 `φ_B(e(m)) = (∏ b_i^{−c(i)}) e(m)`（(17) 式）做成 `torusScale`：按 `f'(m)` 的特征
缩放单项式。核心结论 **`support_of_torus_fixed`**：凡被**所有**环面元固定的多项式，其支撑里的
单项式的权必为 `0`（即 `m ∈ ker f'`）。这是 `lem:14.20` 在**整环层**的内容。
-/

def chi (F : Type) [Field F] (b : Fin 9 → Fˣ) (m : Multiplicative Mprime) : F :=
  ((wt F b (fPrime (Multiplicative.toAdd m)) : Fˣ) : F)

def torusScale (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) : EM.latticeAlgebra F Mprime :=
  ∑ m ∈ (MonoidAlgebra.coeff x).support,
    MonoidAlgebra.single m (MonoidAlgebra.coeff x m * chi F b m)

lemma torusScale_apply (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) (m : Multiplicative Mprime)
    (hm : m ∈ (MonoidAlgebra.coeff x).support) :
    MonoidAlgebra.coeff (torusScale F b x) m = MonoidAlgebra.coeff x m * chi F b m := by
  have hsum : (MonoidAlgebra.coeff (torusScale F b x)) m
      = ∑ i ∈ (MonoidAlgebra.coeff x).support, (MonoidAlgebra.coeff
          (MonoidAlgebra.single i (MonoidAlgebra.coeff x i * chi F b i)) :
            Multiplicative Mprime →₀ F) m := by
    simp only [torusScale, MonoidAlgebra.coeff_sum]
    exact Finsupp.finsetSum_apply _ _ m
  rw [hsum]
  refine (Finset.sum_eq_single m ?_ ?_).trans ?_
  · intro m' _ hm'
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne (Ne.symm hm')]
  · intro hnot
    exact absurd hm hnot
  · simp [chi]

theorem support_of_torus_fixed (F : Type) [Field F] [CharZero F]
    (x : EM.latticeAlgebra F Mprime)
    (hx : ∀ b : Fin 9 → Fˣ, torusScale F b x = x) :
    ∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = 0 := by
  intro m hm
  by_contra hne
  obtain ⟨b, hb⟩ := exists_wt_ne_one F (fPrime (Multiplicative.toAdd m)) hne
  have h1 := torusScale_apply F b x m hm
  have h2 : MonoidAlgebra.coeff (torusScale F b x) m = MonoidAlgebra.coeff x m := by rw [hx b]
  have hc : MonoidAlgebra.coeff x m ≠ 0 := Finsupp.mem_support_iff.mp hm
  have hchi : chi F b m = 1 := by
    have h3 : MonoidAlgebra.coeff x m * chi F b m = MonoidAlgebra.coeff x m * 1 := by
      rw [← h1, h2, mul_one]
    exact mul_left_cancel₀ hc h3
  have h4 : (wt F b (fPrime (Multiplicative.toAdd m)) : F) = 1 := hchi
  exact hb (Units.ext h4)

#print axioms torusScale_apply
#print axioms support_of_torus_fixed


/-! ## §2d 整环层 `lem:14.20`：`A^T` ＝ 支撑落在 `ker f'` 上的元素

`(⊆)` 已由 `support_of_torus_fixed`（§2c）给出；本区补 `(⊇)` 与合并的双向形。
-/

lemma chi_eq_one_of_mem_ker (F : Type) [Field F] (b : Fin 9 → Fˣ) (m : Multiplicative Mprime)
    (hm : fPrime (Multiplicative.toAdd m) = 0) : chi F b m = 1 := by
  simp only [chi, hm, wt_zero]
  rfl

lemma torusScale_apply_of_notMem (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) (m : Multiplicative Mprime)
    (hm : m ∉ (MonoidAlgebra.coeff x).support) :
    MonoidAlgebra.coeff (torusScale F b x) m = 0 := by
  have hsum : (MonoidAlgebra.coeff (torusScale F b x)) m
      = ∑ i ∈ (MonoidAlgebra.coeff x).support, (MonoidAlgebra.coeff
          (MonoidAlgebra.single i (MonoidAlgebra.coeff x i * chi F b i)) :
            Multiplicative Mprime →₀ F) m := by
    simp only [torusScale, MonoidAlgebra.coeff_sum]
    exact Finsupp.finsetSum_apply _ _ m
  rw [hsum]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [MonoidAlgebra.coeff_single]
  exact Finsupp.single_eq_of_ne (fun h => hm (h ▸ hi))

/-- 支撑落在核格上的元素被环面固定（`lem:14.20` 的 `(⊇)` 方向）。 -/
lemma torusScale_eq_self_of_support (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime)
    (h : ∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = 0) :
    torusScale F b x = x := by
  ext m
  by_cases hm : m ∈ (MonoidAlgebra.coeff x).support
  · rw [torusScale_apply F b x m hm, chi_eq_one_of_mem_ker F b m (h m hm), mul_one]
  · have hzero : MonoidAlgebra.coeff x m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    rw [torusScale_apply_of_notMem F b x m hm, hzero]

/-- ★★ **整环层的 `lem:14.20`**：`x` 被**所有**环面元固定 ⟺ 其支撑落在核格 `ker f'` 上。 -/
theorem torusScale_fixed_iff (F : Type) [Field F] [CharZero F]
    (x : EM.latticeAlgebra F Mprime) :
    (∀ b : Fin 9 → Fˣ, torusScale F b x = x)
      ↔ (∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = 0) :=
  ⟨fun hx => support_of_torus_fixed F x hx,
   fun h b => torusScale_eq_self_of_support F b x h⟩

#print axioms chi_eq_one_of_mem_ker
#print axioms torusScale_apply_of_notMem
#print axioms torusScale_eq_self_of_support
#print axioms torusScale_fixed_iff


/-! ## §2e 权分量（分式层的第一步）

`weightPart w x` 只保留 `f'(m) = w` 的单项式。核心事实：权分量是环面作用的**特征向量**
（`coeff_torusScale_weightPart`）——这正是 Saltman 的 (17) 式在分量层的形式。
-/

noncomputable def weightPart (F : Type) [Field F] (w : G.ZOm 3)
    (x : EM.latticeAlgebra F Mprime) : EM.latticeAlgebra F Mprime :=
  MonoidAlgebra.ofCoeff ((MonoidAlgebra.coeff x).filter
    (fun m => fPrime (Multiplicative.toAdd m) = w))

lemma coeff_weightPart (F : Type) [Field F] (w : G.ZOm 3)
    (x : EM.latticeAlgebra F Mprime) (m : Multiplicative Mprime) :
    MonoidAlgebra.coeff (weightPart F w x) m
      = if fPrime (Multiplicative.toAdd m) = w then MonoidAlgebra.coeff x m else 0 := by
  rw [weightPart, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]

/-- 权（按 `ℤ[G/H]` 的元素索引的版本）。 -/
def chiZ (F : Type) [Field F] (b : Fin 9 → Fˣ) (z : G.ZOm 3) : F :=
  ((wt F b z : Fˣ) : F)

lemma chi_eq_chiZ (F : Type) [Field F] (b : Fin 9 → Fˣ) (m : Multiplicative Mprime) :
    chi F b m = chiZ F b (fPrime (Multiplicative.toAdd m)) := rfl

lemma chi_eq_of_fPrime_eq (F : Type) [Field F] (b : Fin 9 → Fˣ)
    {m : Multiplicative Mprime} {w : G.ZOm 3} (h : fPrime (Multiplicative.toAdd m) = w) :
    chi F b m = chiZ F b w := by
  simp only [chi, chiZ, h]

/-- 权分量是环面作用的**特征向量**。 -/
lemma coeff_torusScale_weightPart (F : Type) [Field F] (b : Fin 9 → Fˣ) (w : G.ZOm 3)
    (x : EM.latticeAlgebra F Mprime) (m : Multiplicative Mprime) :
    MonoidAlgebra.coeff (torusScale F b (weightPart F w x)) m
      = chiZ F b w * MonoidAlgebra.coeff (weightPart F w x) m := by
  classical
  by_cases hmw : fPrime (Multiplicative.toAdd m) = w
  · have hcw : chi F b m = chiZ F b w := chi_eq_of_fPrime_eq F b hmw
    by_cases hsupp : m ∈ (MonoidAlgebra.coeff (weightPart F w x)).support
    · rw [torusScale_apply F b _ m hsupp, coeff_weightPart, if_pos hmw, hcw]
      ring
    · have hzero : MonoidAlgebra.coeff (weightPart F w x) m = 0 := by
        by_contra hne
        exact hsupp (Finsupp.mem_support_iff.mpr hne)
      rw [torusScale_apply_of_notMem F b _ m hsupp, hzero, mul_zero]
  · have hzero : MonoidAlgebra.coeff (weightPart F w x) m = 0 := by
      rw [coeff_weightPart, if_neg hmw]
    have hsupp : m ∉ (MonoidAlgebra.coeff (weightPart F w x)).support := by
      rw [Finsupp.mem_support_iff]
      exact fun h => h hzero
    rw [torusScale_apply_of_notMem F b _ m hsupp, hzero, mul_zero]

#print axioms coeff_weightPart
#print axioms chi_eq_chiZ
#print axioms chi_eq_of_fPrime_eq
#print axioms coeff_torusScale_weightPart


/-! ## §2f 权分解：`x` 是其各权分量之和

这是分式层论证的骨架之一：把任意元按权分群，再从「对所有 `b` 固定」读出每个分量的约束。
-/

/-- 支撑中出现的权集合。 -/
def weightSet (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime) : Finset (G.ZOm 3) :=
  (MonoidAlgebra.coeff x).support.image (fun m => fPrime (Multiplicative.toAdd m))

lemma coeff_sum_weightPart (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime)
    (m : Multiplicative Mprime) :
    MonoidAlgebra.coeff (∑ w ∈ weightSet F x, weightPart F w x) m
      = ∑ w ∈ weightSet F x,
          (MonoidAlgebra.coeff (weightPart F w x) : Multiplicative Mprime →₀ F) m := by
  rw [MonoidAlgebra.coeff_sum]
  exact Finsupp.finsetSum_apply (weightSet F x) (fun w => MonoidAlgebra.coeff (weightPart F w x)) m


theorem sum_weightPart (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime) :
    ∑ w ∈ weightSet F x, weightPart F w x = x := by
  apply MonoidAlgebra.coeff_injective
  ext m
  rw [coeff_sum_weightPart]
  by_cases hm : m ∈ (MonoidAlgebra.coeff x).support
  · have hmem : fPrime (Multiplicative.toAdd m) ∈ weightSet F x :=
      Finset.mem_image.mpr ⟨m, hm, rfl⟩
    refine (Finset.sum_eq_single (fPrime (Multiplicative.toAdd m)) ?_ ?_).trans ?_
    · intro w _ hw
      rw [coeff_weightPart, if_neg (Ne.symm hw)]
    · intro hnot
      exact absurd hmem hnot
    · rw [coeff_weightPart, if_pos rfl]
  · have hzero : MonoidAlgebra.coeff x m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    rw [hzero]
    refine Finset.sum_eq_zero ?_
    intro w _
    rw [coeff_weightPart]
    by_cases h : fPrime (Multiplicative.toAdd m) = w
    · rw [if_pos h, hzero]
    · rw [if_neg h]
#print axioms coeff_sum_weightPart
#print axioms sum_weightPart


/-! ## §2g 固定的分量刻画

由 §2e/§2f 得：`weightPart` 与环面作用交换（按权缩放），从而**被环面固定的元素其非零权分量必为 0**。
这是 `lem:14.20` 分式层论证的关键工具。
-/

/-- 元素级：`weightPart` 与环面作用交换（按权缩放）。 -/
theorem weightPart_torusScale (F : Type) [Field F] (b : Fin 9 → Fˣ) (w : G.ZOm 3)
    (x : EM.latticeAlgebra F Mprime) :
    weightPart F w (torusScale F b x) = chiZ F b w • weightPart F w x := by
  apply MonoidAlgebra.coeff_injective
  ext m
  rw [coeff_weightPart]
  have hsm : MonoidAlgebra.coeff (chiZ F b w • weightPart F w x) m
      = chiZ F b w * MonoidAlgebra.coeff (weightPart F w x) m := by simp
  rw [hsm, coeff_weightPart]
  by_cases hmw : fPrime (Multiplicative.toAdd m) = w
  · rw [if_pos hmw, if_pos hmw]
    by_cases hsupp : m ∈ (MonoidAlgebra.coeff x).support
    · rw [torusScale_apply F b x m hsupp, chi_eq_of_fPrime_eq F b hmw]
      ring
    · have hzero : MonoidAlgebra.coeff x m = 0 := by
        by_contra hne
        exact hsupp (Finsupp.mem_support_iff.mpr hne)
      rw [torusScale_apply_of_notMem F b x m hsupp, hzero, mul_zero]
  · rw [if_neg hmw, if_neg hmw, mul_zero]

/-- 被环面固定的元素，其非零权分量全为 0。 -/
theorem weightPart_eq_zero_of_fixed (F : Type) [Field F] [CharZero F]
    (x : EM.latticeAlgebra F Mprime)
    (hx : ∀ b : Fin 9 → Fˣ, torusScale F b x = x)
    (w : G.ZOm 3) (hw : w ≠ 0) : weightPart F w x = 0 := by
  obtain ⟨b, hb⟩ := exists_wt_ne_one F w hw
  have h1 : weightPart F w (torusScale F b x) = weightPart F w x := by rw [hx b]
  rw [weightPart_torusScale F b w x] at h1
  -- h1 : chiZ b w • weightPart w x = weightPart w x
  have hbF : chiZ F b w ≠ 1 := by
    intro h
    exact hb (Units.ext h)
  set y := weightPart F w x with hy
  -- (chiZ - 1) • y = 0 且 chiZ - 1 ≠ 0 ⟹ y = 0
  have h2 : (chiZ F b w - 1) • y = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hbF)
#print axioms weightPart_torusScale
#print axioms weightPart_eq_zero_of_fixed


/-! ## §2h Dedekind 引理（不同特征线性无关）

`lem:14.20` 分式层论证的最后一环：由 `b•f·g = f·b•g` 展开得
`Σ_w χ_w(b) • (f_w g − f g_w) = 0`（对一切 `b`），需要**特征线性无关**才能逐项得出
`f_w g = f g_w`。这是经典的 Dedekind 引理（`Σ a_i χ_i ≡ 0 ⟹ 所有 a_i = 0`）。

证明（对指标集归纳）：单点时用 `χ` 处处非零；多于一点时，对每个 `i` 取 `t_i` 分离 `χ_i` 与 `χ_{i₀}`，
作差 `Σ_i a_i χ_i(t_i t) − χ_{i₀}(t_i) Σ_i a_i χ_i(t)` **消去 `i₀`**，得指标集更小的关系，
由归纳假设得 `a_i (χ_i t_i − χ_{i₀} t_i) = 0` ⟹ `a_i = 0`；最后由原关系得 `a_{i₀} = 0`。
-/

/-- **Dedekind 引理**：两两不同的（乘法）特征在同一有限指标集上线性无关。

若 `Σ_{i∈s} a_i χ_i(t) = 0` 对一切 `t` 成立，则 `s` 上的所有系数为 `0`。 -/
theorem sum_eq_zero_of_chars {ι T K : Type*} [Field K] [Group T] [DecidableEq ι]
    (χ : ι → T → K)
    (hχ_mul : ∀ (i : ι) (t t' : T), χ i (t * t') = χ i t * χ i t')
    (hχ_ne : ∀ (i : ι) (t : T), χ i t ≠ 0)
    (hχ_sep : ∀ i j : ι, i ≠ j → ∃ t : T, χ i t ≠ χ j t)
    (s : Finset ι) (a : ι → K)
    (h : ∀ t : T, ∑ i ∈ s, a i * χ i t = 0) : ∀ i ∈ s, a i = 0 := by
  induction s using Finset.induction_on generalizing a with
  | empty => intro i hi; simp at hi
  | insert i₀ s' hi₀ ih =>
    intro i hi
    -- 先证 `s'` 上的系数全为 0
    have hsmall : ∀ k ∈ s', a k = 0 := by
      intro k hk
      have hne : k ≠ i₀ := fun hh => hi₀ (hh ▸ hk)
      obtain ⟨t₀, ht₀⟩ := hχ_sep k i₀ hne
      have hrel : ∀ t : T, ∑ j ∈ s', (a j * (χ j t₀ - χ i₀ t₀)) * χ j t = 0 := by
        intro t
        have h1 := h (t₀ * t)
        have h2 := h t
        rw [Finset.sum_insert hi₀] at h1 h2
        have h1' : ∑ j ∈ s', a j * χ j t = -a i₀ * χ i₀ t := by
          simpa only [neg_mul] using eq_neg_of_add_eq_zero_right h2
        have h2' : ∑ j ∈ s', a j * (χ j t₀ * χ j t) = -a i₀ * (χ i₀ t₀ * χ i₀ t) := by
          have h2'' : ∑ j ∈ s', a j * χ j (t₀ * t) = -(a i₀ * χ i₀ (t₀ * t)) :=
            eq_neg_of_add_eq_zero_right h1
          simpa only [hχ_mul, neg_mul] using h2''
        calc ∑ j ∈ s', (a j * (χ j t₀ - χ i₀ t₀)) * χ j t
            = ∑ j ∈ s', (a j * (χ j t₀ * χ j t) - (χ i₀ t₀) * (a j * χ j t)) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
          _ = (∑ j ∈ s', a j * (χ j t₀ * χ j t)) - (χ i₀ t₀) * ∑ j ∈ s', a j * χ j t := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
          _ = -a i₀ * (χ i₀ t₀ * χ i₀ t) - (χ i₀ t₀) * (-a i₀ * χ i₀ t) := by
              rw [h2', h1']
          _ = 0 := by ring
      have hk0 := ih (fun j => a j * (χ j t₀ - χ i₀ t₀)) hrel k hk
      rcases mul_eq_zero.mp hk0 with hz | hz
      · exact hz
      · exact absurd (sub_eq_zero.mp hz) ht₀
    by_cases hi0 : i = i₀
    · rw [hi0]
      have h0 := h 1
      rw [Finset.sum_insert hi₀] at h0
      have hz : ∑ j ∈ s', a j * χ j 1 = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hsmall j hj, zero_mul]
      rw [hz, add_zero] at h0
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact h'
      · exact absurd h' (hχ_ne i₀ 1)
    · apply hsmall i
      rcases Finset.mem_insert.mp hi with h' | h'
      · exact absurd h' hi0
      · exact h'
#print axioms sum_eq_zero_of_chars


/-! ## §2i `chiZ` 是环面特征（Dedekind 引理的实例化前提）

四条：对权可加（`chiZ_add`）、对环面元可乘（`wt_mul`／`chiZ_mul'`）、处处非零（`chiZ_ne_zero'`）、
两两可分离（`chiZ_sep`，由第 3 轮的 `exists_wt_ne_one` 作用于 `w − w'`）。
-/

lemma chiZ_add (F : Type) [Field F] (b : Fin 9 → Fˣ) (w w' : G.ZOm 3) :
    chiZ F b (w + w') = chiZ F b w * chiZ F b w' := by
  simp only [chiZ, wt_add]
  push_cast
  ring

lemma wt_mul (F : Type) [Field F] (b b' : Fin 9 → Fˣ) (w : G.ZOm 3) :
    wt F (b * b') w = wt F b w * wt F b' w := by
  simp only [wt]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact mul_zpow (b i) (b' i) (MonoidAlgebra.coeff w i)

lemma chiZ_mul' (F : Type) [Field F] (b b' : Fin 9 → Fˣ) (w : G.ZOm 3) :
    chiZ F (b * b') w = chiZ F b w * chiZ F b' w := by
  simp only [chiZ, wt_mul]
  push_cast
  ring

lemma chiZ_ne_zero' (F : Type) [Field F] (b : Fin 9 → Fˣ) (w : G.ZOm 3) :
    chiZ F b w ≠ 0 := by
  simp only [chiZ]
  exact Units.ne_zero _

lemma chiZ_sep (F : Type) [Field F] [CharZero F] (w w' : G.ZOm 3) (h : w ≠ w') :
    ∃ b : Fin 9 → Fˣ, chiZ F b w ≠ chiZ F b w' := by
  obtain ⟨b, hb⟩ := exists_wt_ne_one F (w - w') (sub_ne_zero.mpr h)
  refine ⟨b, ?_⟩
  intro heq
  have h1 := chiZ_add F b w' (w - w')
  rw [add_sub_cancel] at h1
  have h4 : chiZ F b w' * 1 = chiZ F b w' * chiZ F b (w - w') := by
    rw [mul_one, ← h1, heq]
  have h3 : 1 = chiZ F b (w - w') := mul_left_cancel₀ (chiZ_ne_zero' F b w') h4
  exact hb (Units.ext h3.symm)
#print axioms chiZ_add
#print axioms wt_mul
#print axioms chiZ_mul'
#print axioms chiZ_ne_zero'
#print axioms chiZ_sep


/-! ## §2j `torusScale` 在 0 与单项式上的值（环自同态性的两块拼图）

`torusScale` 是**线性**的（由 `Finset.sum` 定义）且把单项式送到「同单项式 × 该权的特征」。
这两条是证明它是**环自同态**（进而诱导分式域上的作用）的起点。
-/

lemma torusScale_zero (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    torusScale F b 0 = 0 := by
  simp only [torusScale, MonoidAlgebra.coeff_zero, Finsupp.support_zero, Finset.sum_empty]

lemma torusScale_single (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (m : Multiplicative Mprime) (r : F) :
    torusScale F b (MonoidAlgebra.single m r) = MonoidAlgebra.single m (r * chi F b m) := by
  classical
  by_cases hr : r = 0
  · rw [hr, zero_mul, MonoidAlgebra.single_zero, torusScale_zero]
  · have hsupp : (MonoidAlgebra.coeff (MonoidAlgebra.single m r)).support = {m} := by
      rw [MonoidAlgebra.coeff_single, Finsupp.support_single_ne_zero _ hr]
    rw [torusScale, hsupp, Finset.sum_singleton, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
#print axioms torusScale_zero
#print axioms torusScale_single


/-! ## §2k `torusScale` 是环自同态

由 §2j 的单项式值 ＋ 本区的**加性**（关键手法：用 `Finset.sum_subset` 把和扩到
`supp x ∪ supp y`，让 `if` 完全消失——这解决了第 12 轮两次失败的根因）
＋ **乘性**（对两个变元各用 `MonoidAlgebra.induction_linear`，单项式相乘情形由 `chi_mul` 收口）
＋ **单位**，得 `torusScale b` 是 `F`-代数自同态。这是诱导分式域 `F(M_2')` 上作用的前提。
-/

lemma torusScale_eq_sum_of_support_subset (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) (S : Finset (Multiplicative Mprime))
    (hS : (MonoidAlgebra.coeff x).support ⊆ S) :
    torusScale F b x
      = ∑ m ∈ S, MonoidAlgebra.single m (MonoidAlgebra.coeff x m * chi F b m) := by
  rw [torusScale]
  exact Finset.sum_subset hS (fun m _ hm => by
    have h0 : MonoidAlgebra.coeff x m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    show MonoidAlgebra.single m (MonoidAlgebra.coeff x m * chi F b m) = 0
    rw [h0, zero_mul, MonoidAlgebra.single_zero])

lemma torusScale_add (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x y : EM.latticeAlgebra F Mprime) :
    torusScale F b (x + y) = torusScale F b x + torusScale F b y := by
  classical
  set S := (MonoidAlgebra.coeff x).support ∪ (MonoidAlgebra.coeff y).support with hSdef
  have hxy : MonoidAlgebra.coeff (x + y) = MonoidAlgebra.coeff x + MonoidAlgebra.coeff y := by
    rw [MonoidAlgebra.coeff_add]
  rw [torusScale_eq_sum_of_support_subset F b (x + y) S (by rw [hxy]; exact Finsupp.support_add),
      torusScale_eq_sum_of_support_subset F b x S Finset.subset_union_left,
      torusScale_eq_sum_of_support_subset F b y S Finset.subset_union_right,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
  exact MonoidAlgebra.single_add _ _ _

variable (F : Type) [Field F] (b : Fin 9 → Fˣ)

lemma chi_mul (m n : Multiplicative Mprime) :
    chi F b (m * n) = chi F b m * chi F b n := by
  show chiZ F b (fPrime (Multiplicative.toAdd m + Multiplicative.toAdd n))
      = chiZ F b (fPrime (Multiplicative.toAdd m))
        * chiZ F b (fPrime (Multiplicative.toAdd n))
  rw [map_add, chiZ_add]

lemma torusScale_mul (x y : EM.latticeAlgebra F Mprime) :
    torusScale F b (x * y) = torusScale F b x * torusScale F b y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, torusScale_zero, zero_mul]
  | add x₁ x₂ ih1 ih2 => rw [add_mul, torusScale_add, ih1, ih2, torusScale_add, add_mul]
  | single m r =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, torusScale_zero, mul_zero]
    | add y₁ y₂ ih1 ih2 => rw [mul_add, torusScale_add, ih1, ih2, torusScale_add, mul_add]
    | single n s =>
      rw [MonoidAlgebra.single_mul_single, torusScale_single, torusScale_single,
        torusScale_single, MonoidAlgebra.single_mul_single, chi_mul]
      congr 1
      ring


variable (F : Type) [Field F] (b : Fin 9 → Fˣ)

lemma chi_one : chi F b 1 = 1 := by
  have h : fPrime (Multiplicative.toAdd (1 : Multiplicative Mprime)) = 0 := by
    simp
  simp only [chi, h, wt_zero]
  rfl

lemma torusScale_one : torusScale F b 1 = 1 := by
  have h1 : (1 : EM.latticeAlgebra F Mprime) = MonoidAlgebra.single 1 1 := by
    rw [MonoidAlgebra.one_def]
  rw [h1, torusScale_single, chi_one, mul_one]
#print axioms torusScale_eq_sum_of_support_subset
#print axioms torusScale_add
#print axioms chi_mul
#print axioms torusScale_mul
#print axioms chi_one
#print axioms torusScale_one


/-! ## §2l `torusScale` 的环等价性

`torusScale b` 的逆是 `torusScale b⁻¹`（单项式上 `chi b m * chi b⁻¹ m = 1`）。由此得
**`torusScaleEquiv b : A ≃+* A`**，它是诱导分式域 `F(M_2')` 上作用（`RingEquiv` → `FractionRing`）
的入口。
-/

lemma wt_one (F : Type) [Field F] (w : G.ZOm 3) :
    wt F (fun _ => 1) w = 1 := by
  simp [wt]

lemma chiZ_mul_inv (F : Type) [Field F] (b : Fin 9 → Fˣ) (w : G.ZOm 3) :
    chiZ F b w * chiZ F b⁻¹ w = 1 := by
  have h : b * b⁻¹ = (fun _ => 1 : Fin 9 → Fˣ) := by
    funext i; exact mul_inv_cancel (b i)
  rw [← chiZ_mul', h]
  show ((wt F (fun _ => 1) w : Fˣ) : F) = 1
  rw [wt_one]
  rfl

lemma chi_mul_fun (F : Type) [Field F] (b b' : Fin 9 → Fˣ) (m : Multiplicative Mprime) :
    chi F (b * b') m = chi F b m * chi F b' m := by
  show chiZ F (b * b') (fPrime (Multiplicative.toAdd m))
      = chiZ F b (fPrime (Multiplicative.toAdd m)) * chiZ F b' (fPrime (Multiplicative.toAdd m))
  rw [chiZ_mul']

lemma chi_mul_inv (F : Type) [Field F] (b : Fin 9 → Fˣ) (m : Multiplicative Mprime) :
    chi F b m * chi F b⁻¹ m = 1 := by
  have h : b * b⁻¹ = (fun _ => 1 : Fin 9 → Fˣ) := funext fun i => mul_inv_cancel (b i)
  rw [← chi_mul_fun, h]
  show ((wt F (fun _ => 1) (fPrime (Multiplicative.toAdd m)) : Fˣ) : F) = 1
  rw [wt_one]
  rfl

lemma torusScale_comp (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) :
    torusScale F b⁻¹ (torusScale F b x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [torusScale_zero, torusScale_zero]
  | add x₁ x₂ ih1 ih2 => rw [torusScale_add, torusScale_add, ih1, ih2]
  | single m r =>
    rw [torusScale_single, torusScale_single, mul_assoc, chi_mul_inv, mul_one]

lemma torusScale_comp' (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) :
    torusScale F b (torusScale F b⁻¹ x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [torusScale_zero, torusScale_zero]
  | add x₁ x₂ ih1 ih2 => rw [torusScale_add, torusScale_add, ih1, ih2]
  | single m r =>
    rw [torusScale_single, torusScale_single, mul_assoc, mul_comm (chi F b⁻¹ m), chi_mul_inv, mul_one]

variable (F : Type) [Field F]

noncomputable def torusScaleEquiv (b : Fin 9 → Fˣ) :
    EM.latticeAlgebra F Mprime ≃+* EM.latticeAlgebra F Mprime where
  toFun := torusScale F b
  invFun := torusScale F b⁻¹
  left_inv := torusScale_comp F b
  right_inv := torusScale_comp' F b
  map_add' := torusScale_add F b
  map_mul' := torusScale_mul F b
#print axioms wt_one
#print axioms chi_mul_fun
#print axioms chi_mul_inv
#print axioms torusScale_comp
#print axioms torusScale_comp'
#print axioms torusScaleEquiv


/-! ## §2m 分式域上的环面作用

由 §2l 的 `torusScaleEquiv : A ≃+* A` 经 `IsFractionRing.ringEquivOfRingEquiv` 提升为
`K ≃+* K`（`K = F(M_2')`），并由 `_algebraMap` 规则给出其在单项式上的值。
本区还给出 `lem:14.20` 的 **`(⊇)` 方向**：两个**零权**元素之商被整个环面固定。
-/

noncomputable def torusScaleFieldEquiv (F : Type) [Field F] (b : Fin 9 → Fˣ) :
    EM.latticeFunctionField F Mprime ≃+* EM.latticeFunctionField F Mprime :=
  IsFractionRing.ringEquivOfRingEquiv (torusScaleEquiv F b)

lemma torusScaleFieldEquiv_algebraMap (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) :
    torusScaleFieldEquiv F b (algebraMap _ _ x) = algebraMap _ _ (torusScale F b x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (torusScaleEquiv F b) x

/-- 权重为零的元素的商被环面固定（`lem:14.20` 的 `(⊇)` 方向）。 -/
theorem fraction_fixed_of_weight_zero (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0)
    (hf : ∀ m ∈ (MonoidAlgebra.coeff f).support, fPrime (Multiplicative.toAdd m) = 0)
    (hgg : ∀ m ∈ (MonoidAlgebra.coeff g).support, fPrime (Multiplicative.toAdd m) = 0)
    (b : Fin 9 → Fˣ) :
    torusScaleFieldEquiv F b
        (algebraMap _ _ f / algebraMap _ _ g) = algebraMap _ _ f / algebraMap _ _ g := by
  rw [map_div₀, torusScaleFieldEquiv_algebraMap, torusScaleFieldEquiv_algebraMap,
    torusScale_eq_self_of_support F b f hf, torusScale_eq_self_of_support F b g hgg]
#print axioms torusScaleFieldEquiv
#print axioms torusScaleFieldEquiv_algebraMap
#print axioms fraction_fixed_of_weight_zero

/-! ### §2n **`lem:14.20` 的 `⊆` 半第一步：交叉相乘**（第 653 轮）

`lem:14.20`（`F(M_r) = F(M_r')^T`）的 `⊇` 半已由 §2m 的 `fraction_fixed_of_weight_zero` 机检；
`⊆` 半需要 `FixedRatio` 的三件（交叉相乘 → Euclid 步 → 单位倍）在**本模型**里重做一遍。
本节给第一件。

**工艺**：`algebraMap` 的隐式参数在出现两处以上时必须**写全**
（`algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)`），
否则 `Algebra (EM.latticeAlgebra F Mprime) ?m` 卡住；
`EM.latticeAlgebra` 需 `open ABGV52` 才可解析（`EM` 在 `ABGV52` 命名空间下）。 -/

/-- ★★★★★ **交叉相乘**（`lem:14.20` 第一步，`latticeAlgebra` 版）：`K'` 中 `f/g` 被
`torusScaleFieldEquiv b` 固定 ⟹ `torusScale b f * g = f * torusScale b g`。 -/
theorem torusScale_mul_eq_of_fixed (F : Type) [Field F] (b : Fin 9 → Fˣ)
    {f g : EM.latticeAlgebra F Mprime} (hg : g ≠ 0)
    (hfix : torusScaleFieldEquiv F b
        (algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) f
          / algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) g)
      = algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) f
        / algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) g) :
    torusScale F b f * g = f * torusScale F b g := by
  have hinjA : Function.Injective (torusScale F b) := (torusScaleEquiv F b).injective
  have hinj : Function.Injective
      (algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)) :=
    IsFractionRing.injective (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
  have hφg : torusScale F b g ≠ 0 := fun h => hg (hinjA (by rw [h]; simp [torusScale]))
  have h1 : torusScaleFieldEquiv F b
        (algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) f
          / algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) g)
      = algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
          (torusScale F b f)
        / algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
          (torusScale F b g) := by
    rw [map_div₀, torusScaleFieldEquiv_algebraMap, torusScaleFieldEquiv_algebraMap]
  rw [h1] at hfix
  have hnum : algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
        (torusScale F b f)
      * algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) g
      = algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime) f
        * algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
          (torusScale F b g) :=
    (div_eq_div_iff (by simpa using hinj.ne hφg) (by simpa using hinj.ne hg)).mp hfix
  have h2 : algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
        (torusScale F b f * g)
      = algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
          (f * torusScale F b g) := by
    rw [map_mul, map_mul]
    exact hnum
  exact hinj h2

#print axioms torusScale_mul_eq_of_fixed


/-! ## §2n 交叉相乘判据（`lem:14.20` 的 `(⊆)` 方向第一步）

`α = f/g` 被环面固定 ⟺ 交叉相乘 `φ(f)·g = f·φ(g)`（在整环 `A` 内，无分式）。这把分式层的
固定性问题化归为**多项式层的等式**，从而可以逐权分解并用 Dedekind 收口。
-/

/-- `A = F[M_2'] → K = F(M_2')` 的典范映射。 -/
abbrev iota (F : Type) [Field F] : EM.latticeAlgebra F Mprime →+* EM.latticeFunctionField F Mprime :=
  algebraMap _ _

theorem iota_injective (F : Type) [Field F] : Function.Injective (iota F) :=
  IsFractionRing.injective _ _

theorem fraction_fixed_iff_cross (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0) (b : Fin 9 → Fˣ) :
    torusScaleFieldEquiv F b (iota F f / iota F g) = iota F f / iota F g
      ↔ torusScale F b f * g = f * torusScale F b g := by
  have hinj := iota_injective F
  have hgK : iota F g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hφgK : iota F (torusScale F b g) ≠ 0 := by
    intro h
    have h1 : torusScale F b g = 0 := hinj (by rw [h, map_zero])
    exact hg ((torusScaleEquiv F b).injective (by rw [map_zero]; exact h1))
  rw [map_div₀, torusScaleFieldEquiv_algebraMap, torusScaleFieldEquiv_algebraMap,
    div_eq_div_iff hφgK hgK, ← map_mul, ← map_mul, hinj.eq_iff]
#print axioms iota_injective
#print axioms fraction_fixed_iff_cross


/-! ## §2o 权展开（`lem:14.20` 的 `(⊆)` 方向第二步）

`torusScale` 与有限和交换，且每个权分量被按该权的特征缩放，故
`φ_b(x) = Σ_w χ_w(b) • x_w`。把它代入 §2n 的交叉相乘式，即得
`Σ_w χ_w(b) • (f_w g − f g_w) = 0`，再用 Dedekind（第 9 轮）逐项。
-/

/-- 线性性：`torusScale` 与有限和交换。 -/
lemma torusScale_sum (F : Type) [Field F] (b : Fin 9 → Fˣ) {ι : Type}
    (s : Finset ι) (f : ι → EM.latticeAlgebra F Mprime) :
    torusScale F b (∑ i ∈ s, f i) = ∑ i ∈ s, torusScale F b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, torusScale_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, torusScale_add, ih]

lemma torusScale_weightPart (F : Type) [Field F] (b : Fin 9 → Fˣ) (w : G.ZOm 3)
    (x : EM.latticeAlgebra F Mprime) :
    torusScale F b (weightPart F w x) = chiZ F b w • weightPart F w x := by
  apply MonoidAlgebra.coeff_injective
  ext m
  rw [coeff_torusScale_weightPart]
  have hsm : MonoidAlgebra.coeff (chiZ F b w • weightPart F w x) m
      = chiZ F b w * MonoidAlgebra.coeff (weightPart F w x) m := by simp
  rw [hsm]

/-- ★ **权展开**：`φ_b(x) = Σ_w χ_w(b) • x_w`。 -/
lemma torusScale_eq_sum_weightPart (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) :
    torusScale F b x = ∑ w ∈ weightSet F x, chiZ F b w • weightPart F w x := by
  classical
  conv_lhs => rw [← sum_weightPart F x]
  rw [torusScale_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [torusScale_weightPart]
#print axioms torusScale_sum
#print axioms torusScale_weightPart
#print axioms torusScale_eq_sum_weightPart


/-! ## §2p 任意索引集的权分解与权展开

Dedekind 步需要 `f` 与 `g` 共用**同一个**权索引集（否则 `Σ_w χ_w(b) a_w` 的两半无法合并）。
本区把 §2f／§2o 的分解与展开推广到任意**包含权集**的有限索引集 `S`。
-/

/-- 任意索引集上的和的系数 ＝ 系数之和。 -/
lemma coeff_sum_weightPart_gen (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime)
    (S : Finset (G.ZOm 3)) (m : Multiplicative Mprime) :
    MonoidAlgebra.coeff (∑ w ∈ S, weightPart F w x) m
      = ∑ w ∈ S, (MonoidAlgebra.coeff (weightPart F w x) : Multiplicative Mprime →₀ F) m := by
  rw [MonoidAlgebra.coeff_sum]
  exact Finsupp.finsetSum_apply S (fun w => MonoidAlgebra.coeff (weightPart F w x)) m

/-- `w` 不在权集里 ⟹ 该权分量为 0。 -/
lemma weightPart_eq_zero_of_notMem_weightSet (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime)
    {w : G.ZOm 3} (hw : w ∉ weightSet F x) : weightPart F w x = 0 := by
  rw [weightPart]
  have hempty : (MonoidAlgebra.coeff x).filter
      (fun m => fPrime (Multiplicative.toAdd m) = w) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro m hm
    by_contra hne
    exact hw (by rw [weightSet]
                 exact Finset.mem_image.mpr ⟨m, Finsupp.mem_support_iff.mpr hne, hm⟩)
  rw [hempty, MonoidAlgebra.ofCoeff_zero]

/-- 权分解（任意含权集的索引集版本）。 -/
lemma sum_weightPart_of_subset (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime)
    (S : Finset (G.ZOm 3)) (hS : weightSet F x ⊆ S) :
    ∑ w ∈ S, weightPart F w x = x := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext m
  rw [coeff_sum_weightPart_gen]
  by_cases hm : m ∈ (MonoidAlgebra.coeff x).support
  · have hmem : fPrime (Multiplicative.toAdd m) ∈ S :=
      hS (by rw [weightSet]; exact Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    refine (Finset.sum_eq_single (fPrime (Multiplicative.toAdd m)) ?_ ?_).trans ?_
    · intro w _ hw
      rw [coeff_weightPart, if_neg (Ne.symm hw)]
    · intro hnot
      exact absurd hmem hnot
    · rw [coeff_weightPart, if_pos rfl]
  · have hzero : MonoidAlgebra.coeff x m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    rw [hzero]
    refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [coeff_weightPart]
    by_cases h : fPrime (Multiplicative.toAdd m) = w
    · rw [if_pos h, hzero]
    · rw [if_neg h]


lemma torusScale_eq_sum_weightPart_of_subset (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) (S : Finset (G.ZOm 3)) (hS : weightSet F x ⊆ S) :
    torusScale F b x = ∑ w ∈ S, chiZ F b w • weightPart F w x := by
  conv_lhs => rw [← sum_weightPart_of_subset F x S hS]
  rw [torusScale_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [torusScale_weightPart]
#print axioms coeff_sum_weightPart_gen
#print axioms weightPart_eq_zero_of_notMem_weightSet
#print axioms sum_weightPart_of_subset
#print axioms torusScale_eq_sum_weightPart_of_subset


/-! ## §2q **Dedekind 一击**：固定性 ⟹ 逐权分量等式

`lem:14.20` 的 `(⊆)` 方向的核心：若 `φ_b(f)·g = f·φ_b(g)` 对**一切** `b` 成立，则对每个出现权 `w`
有 `f_w·g = f·g_w`（即 `f` 与 `g` 的各权分量**成比例**）。

证明：把 §2p 的权展开代入，得 `Σ_w χ_w(b) • (f_w g − f g_w) = 0`；推到 `K = F(M_2')` 后
用第 9 轮的 **Dedekind 引理** `sum_eq_zero_of_chars`（前提 `chiZ_mul'`／`chiZ_ne_zero'`／
`chiZ_sep` 见第 10 轮）逐项，再由 `iota` 的单射性回到 `A`。
-/

/-- ★★ 固定性 ⟹ 逐权分量等式（Dedekind 一击）。 -/
theorem weightPart_mul_eq_of_fixed (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0)
    (hfix : ∀ b : Fin 9 → Fˣ, torusScale F b f * g = f * torusScale F b g) :
    ∀ w ∈ weightSet F f ∪ weightSet F g,
      weightPart F w f * g = f * weightPart F w g := by
  classical
  set W := weightSet F f ∪ weightSet F g with hW
  have hfW : weightSet F f ⊆ W := Finset.subset_union_left
  have hgW : weightSet F g ⊆ W := Finset.subset_union_right
  -- 多项式层的恒等式
  have key : ∀ b : Fin 9 → Fˣ,
      ∑ v ∈ W, chiZ F b v • (weightPart F v f * g - f * weightPart F v g) = 0 := by
    intro b
    have h := hfix b
    rw [torusScale_eq_sum_weightPart_of_subset F b f W hfW,
        torusScale_eq_sum_weightPart_of_subset F b g W hgW,
        Finset.sum_mul, Finset.mul_sum] at h
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] at h
    calc ∑ v ∈ W, chiZ F b v • (weightPart F v f * g - f * weightPart F v g)
        = ∑ v ∈ W, (chiZ F b v • (weightPart F v f * g)
            - chiZ F b v • (f * weightPart F v g)) :=
          Finset.sum_congr rfl (fun v _ => smul_sub _ _ _)
      _ = (∑ v ∈ W, chiZ F b v • (weightPart F v f * g))
            - ∑ v ∈ W, chiZ F b v • (f * weightPart F v g) := by
          rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [h, sub_self]
  -- 推到 K
  have hK : ∀ b : Fin 9 → Fˣ,
      ∑ v ∈ W, (iota F (weightPart F v f * g - f * weightPart F v g))
        * (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b v)) = 0 := by
    intro b
    have h := congrArg (iota F) (key b)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
        (EM.latticeFunctionField F Mprime), mul_comm]
  -- Dedekind
  have hsep : ∀ u v : G.ZOm 3, u ≠ v →
      ∃ b : Fin 9 → Fˣ,
        (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b u))
          ≠ (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b v)) := by
    intro u v huv
    obtain ⟨b, hb⟩ := chiZ_sep F u v huv
    exact ⟨b, fun h => hb (FaithfulSMul.algebraMap_injective F _ h)⟩
  have hmul : ∀ (u : G.ZOm 3) (b b' : Fin 9 → Fˣ),
      (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F (b * b') u))
        = (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b u))
          * (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b' u)) := by
    intro u b b'
    rw [chiZ_mul']
    push_cast
    ring
  have hne : ∀ (u : G.ZOm 3) (b : Fin 9 → Fˣ),
      (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b u)) ≠ 0 := by
    intro u b h
    exact chiZ_ne_zero' F b u (FaithfulSMul.algebraMap_injective F _ (by rw [h, map_zero]))
  intro w hw
  have := sum_eq_zero_of_chars
    (χ := fun u (b : Fin 9 → Fˣ) => algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b u))
    hmul hne hsep W
    (fun u => iota F (weightPart F u f * g - f * weightPart F u g)) hK w hw
  apply iota_injective F
  rw [← sub_eq_zero, ← map_sub]
  exact this
#print axioms weightPart_mul_eq_of_fixed


/-! ## §2r 取出非零权分量并把 `α = f/g` 写成**同权**之商

由 §2q 的逐权成比例，取一个非零权分量 `w`（`g ≠ 0` 保证存在），即得
`α = f/g = f_w / g_w`，且 `f_w`、`g_w` 的支撑**都落在权 `w` 上**（同权）。
下一步把它乘以 `e(−m₀)`（`m₀` 任一权 `w` 的单项式）即得**零权**之商。
-/

/-- 非零元素必有某个权分量非零。 -/
lemma exists_weightPart_ne_zero (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime)
    (hx : x ≠ 0) : ∃ w ∈ weightSet F x, weightPart F w x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hx
  rw [← sum_weightPart F x]
  exact Finset.sum_eq_zero (fun w hw => h w hw)

/-- ★★ 固定性 ⟹ 存在非零权分量使 `f` 与 `g` 成比例。 -/
theorem exists_ratio_of_fixed (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0)
    (hfix : ∀ b : Fin 9 → Fˣ, torusScale F b f * g = f * torusScale F b g) :
    ∃ w ∈ weightSet F g,
      weightPart F w f * g = f * weightPart F w g ∧ weightPart F w g ≠ 0 := by
  obtain ⟨w, hwW, hw0⟩ := exists_weightPart_ne_zero F g hg
  have hwU : w ∈ weightSet F f ∪ weightSet F g := Finset.mem_union_right _ hwW
  exact ⟨w, hwW, weightPart_mul_eq_of_fixed F f g hg hfix w hwU, hw0⟩

theorem exists_field_ratio_of_fixed (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0)
    (hfix : ∀ b : Fin 9 → Fˣ, torusScale F b f * g = f * torusScale F b g) :
    ∃ w ∈ weightSet F g,
      (∀ m ∈ (MonoidAlgebra.coeff (weightPart F w f)).support,
        fPrime (Multiplicative.toAdd m) = w)
      ∧ (∀ m ∈ (MonoidAlgebra.coeff (weightPart F w g)).support,
        fPrime (Multiplicative.toAdd m) = w)
      ∧ weightPart F w g ≠ 0
      ∧ iota F f / iota F g = iota F (weightPart F w f) / iota F (weightPart F w g) := by
  obtain ⟨w, hwW, hcross, hw0⟩ := exists_ratio_of_fixed F f g hg hfix
  have hinj := iota_injective F
  have hgK : iota F g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hwK : iota F (weightPart F w g) ≠ 0 := fun h => hw0 (hinj (by rw [h, map_zero]))
  refine ⟨w, hwW, ?_, ?_, hw0, ?_⟩
  · intro m hm
    rw [weightPart, MonoidAlgebra.coeff_ofCoeff, Finsupp.support_filter] at hm
    exact (Finset.mem_filter.mp hm).2
  · intro m hm
    rw [weightPart, MonoidAlgebra.coeff_ofCoeff, Finsupp.support_filter] at hm
    exact (Finset.mem_filter.mp hm).2
  · rw [div_eq_div_iff hgK hwK, ← map_mul, ← map_mul, hcross]
#print axioms exists_weightPart_ne_zero
#print axioms exists_ratio_of_fixed
#print axioms exists_field_ratio_of_fixed


/-! ## §2s **`lem:14.20` 的 `(⊆)`（同权表述）**：被固定 ⟹ 两同权元素之商

权齐次元素是特征向量（`torusScale_eq_smul_of_weight_homog`），故**同权之商必被固定**
（`fraction_fixed_of_same_weight`，即反方向）。与 §2r 合起来得
**`fraction_fixed_imp_same_weight`**：被整个环面固定 ⟹ 是两**同权**元素之商。

**与 Saltman 的 `F(M_r)` 的差别**：Saltman 要的是「**零权**之商」（即落在核格域 `F(M_r)` 内）。
同权之商乘上 `e(−m₀)`（`m₀` 为权 `w` 的任一单项式，在 Laurent 代数里是**单位**）即变零权之商，
故两者生成同一个域；这一步（平移）尚待机检，已登记。
-/

lemma torusScale_eq_smul_of_weight_homog (F : Type) [Field F] (b : Fin 9 → Fˣ)
    (x : EM.latticeAlgebra F Mprime) (w : G.ZOm 3)
    (h : ∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = w) :
    torusScale F b x = chiZ F b w • x := by
  classical
  have hsm : ∀ (c : F) (y : EM.latticeAlgebra F Mprime) (m : Multiplicative Mprime),
      MonoidAlgebra.coeff (c • y) m = c * MonoidAlgebra.coeff y m := by
    intro c y m
    simp
  apply MonoidAlgebra.coeff_injective
  ext m
  by_cases hm : m ∈ (MonoidAlgebra.coeff x).support
  · rw [torusScale_apply F b x m hm, hsm]
    have hchi : chi F b m = chiZ F b w := by
      simp only [chi]
      rw [h m hm]
      rfl
    rw [hchi, mul_comm]
  · have hzero : MonoidAlgebra.coeff x m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    rw [torusScale_apply_of_notMem F b x m hm, hsm, hzero, mul_zero]

/-- 同权之商被整个环面固定。 -/
theorem fraction_fixed_of_same_weight (F : Type) [Field F]
    (f' g' : EM.latticeAlgebra F Mprime) (w : G.ZOm 3)
    (hf : ∀ m ∈ (MonoidAlgebra.coeff f').support, fPrime (Multiplicative.toAdd m) = w)
    (hgg : ∀ m ∈ (MonoidAlgebra.coeff g').support, fPrime (Multiplicative.toAdd m) = w)
    (b : Fin 9 → Fˣ) :
    torusScaleFieldEquiv F b (iota F f' / iota F g') = iota F f' / iota F g' := by
  have hι : ∀ y : EM.latticeAlgebra F Mprime,
      iota F (chiZ F b w • y)
        = (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b w)) * iota F y := by
    intro y
    rw [Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
        (EM.latticeFunctionField F Mprime)]
  have hc : (algebraMap F (EM.latticeFunctionField F Mprime) (chiZ F b w)) ≠ 0 := by
    intro h
    exact chiZ_ne_zero' F b w
      (FaithfulSMul.algebraMap_injective F _ (by rw [h, map_zero]))
  rw [map_div₀, torusScaleFieldEquiv_algebraMap, torusScaleFieldEquiv_algebraMap,
    torusScale_eq_smul_of_weight_homog F b f' w hf,
    torusScale_eq_smul_of_weight_homog F b g' w hgg, hι, hι,
    mul_div_mul_left _ _ hc]


/-- ★★★ **`lem:14.20` 的 `(⊆)`（同权表述）**：被环面固定 ⟹ 是两**同权**元素之商。 -/
theorem fraction_fixed_imp_same_weight (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0)
    (hfix : ∀ b : Fin 9 → Fˣ,
      torusScaleFieldEquiv F b (iota F f / iota F g) = iota F f / iota F g) :
    ∃ w : G.ZOm 3, ∃ f' g' : EM.latticeAlgebra F Mprime,
      (∀ m ∈ (MonoidAlgebra.coeff f').support, fPrime (Multiplicative.toAdd m) = w)
      ∧ (∀ m ∈ (MonoidAlgebra.coeff g').support, fPrime (Multiplicative.toAdd m) = w)
      ∧ g' ≠ 0 ∧ iota F f / iota F g = iota F f' / iota F g' := by
  have hcross : ∀ b : Fin 9 → Fˣ, torusScale F b f * g = f * torusScale F b g :=
    fun b => (fraction_fixed_iff_cross F f g hg b).mp (hfix b)
  obtain ⟨w, _hwW, hf, hgg, hgw, hratio⟩ := exists_field_ratio_of_fixed F f g hg hcross
  exact ⟨w, weightPart F w f, weightPart F w g, hf, hgg, hgw, hratio⟩
#print axioms torusScale_eq_smul_of_weight_homog
#print axioms fraction_fixed_of_same_weight
#print axioms fraction_fixed_imp_same_weight


/-! ## §2t **`lem:14.20` 的 `(⊆)`（Saltman 的零权表述）**：平移步

同权之商 ⟶ 零权之商：乘以单项式 `e(m₀)⁻¹`（`m₀` 是权 `w` 的任一单项式；`e(m₀)` 在
Laurent 代数里是**单位**）。`shift_weight_zero` 给平移后的支撑落在 `f' = 0` 上；
`mul_div_mul_left` 给商不变（`ι e(m₀) ≠ 0`）。
-/

/-- 乘单项式 `e(m₀)⁻¹` 把权 `w` 齐次的元素平移成**零权**。 -/
lemma shift_weight_zero (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime)
    (w : G.ZOm 3) (m₀ : Mprime)
    (hx : ∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = w)
    (hm₀ : fPrime m₀ = w) :
    ∀ m ∈ (MonoidAlgebra.coeff
        (MonoidAlgebra.single (Multiplicative.ofAdd (-m₀)) 1 * x)).support,
      fPrime (Multiplicative.toAdd m) = 0 := by
  intro m hm
  have hinv : (Multiplicative.ofAdd (-m₀) : Multiplicative Mprime)⁻¹
      = Multiplicative.ofAdd m₀ := by
    simp
  have hcoeff : (MonoidAlgebra.single (Multiplicative.ofAdd (-m₀)) 1 * x).coeff m
      = x.coeff (Multiplicative.ofAdd m₀ * m) := by
    rw [MonoidAlgebra.coeff_single_mul_apply, hinv, one_mul]
  have hsupp : Multiplicative.ofAdd m₀ * m ∈ (MonoidAlgebra.coeff x).support :=
    Finsupp.mem_support_iff.mpr (by
      rw [← hcoeff]
      exact Finsupp.mem_support_iff.mp hm)
  have h1 : fPrime (m₀ + Multiplicative.toAdd m) = w := hx _ hsupp
  rw [map_add, hm₀] at h1
  exact add_left_cancel (by rw [add_zero]; exact h1)


/-- ★★★ **`lem:14.20` 的 `(⊆)`（Saltman 的零权表述）**。 -/
theorem fraction_fixed_imp_weight_zero_ratio (F : Type) [Field F] [CharZero F]
    (f g : EM.latticeAlgebra F Mprime) (hg : g ≠ 0)
    (hfix : ∀ b : Fin 9 → Fˣ,
      torusScaleFieldEquiv F b (iota F f / iota F g) = iota F f / iota F g) :
    ∃ f' g' : EM.latticeAlgebra F Mprime,
      (∀ m ∈ (MonoidAlgebra.coeff f').support, fPrime (Multiplicative.toAdd m) = 0)
      ∧ (∀ m ∈ (MonoidAlgebra.coeff g').support, fPrime (Multiplicative.toAdd m) = 0)
      ∧ g' ≠ 0 ∧ iota F f / iota F g = iota F f' / iota F g' := by
  obtain ⟨w, f_w, g_w, hf, hgg, hgw, hratio⟩ := fraction_fixed_imp_same_weight F f g hg hfix
  -- 取 `m₀` 使 `f' m₀ = w`
  have hsupp : (MonoidAlgebra.coeff g_w).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hgw (by
      apply MonoidAlgebra.coeff_injective
      rw [h, MonoidAlgebra.coeff_zero])
  obtain ⟨m, hm⟩ := hsupp
  have hm₀ : fPrime (Multiplicative.toAdd m) = w := hgg m hm
  -- 平移到零权
  set e : EM.latticeAlgebra F Mprime :=
    MonoidAlgebra.single (Multiplicative.ofAdd (-(Multiplicative.toAdd m))) 1 with he
  refine ⟨e * f_w, e * g_w,
    shift_weight_zero F f_w w (Multiplicative.toAdd m) hf hm₀,
    shift_weight_zero F g_w w (Multiplicative.toAdd m) hgg hm₀, ?_, ?_⟩
  · exact mul_ne_zero (MonoidAlgebra.single_ne_zero.mpr one_ne_zero) hgw
  · have he0 : e ≠ 0 := MonoidAlgebra.single_ne_zero.mpr one_ne_zero
    have hιe : iota F e ≠ 0 := fun h => he0 (iota_injective F (by rw [h, map_zero]))
    rw [hratio, map_mul, map_mul, mul_div_mul_left _ _ hιe]
#print axioms shift_weight_zero
#print axioms fraction_fixed_imp_weight_zero_ratio


/-! ## §4 `S_n` 在 `M_2'` 上的作用：第一步（`ℤ[G/H]` 分量）

(C3) 需要 `S_n = Equiv.Perm (Fin 9)` 在 `M_2' = B ⊕ ℤ[G/H]` 上的作用。库内的作用以 `Rep` 形式给出
（`G.U`、`tensorDiagRepr`、`ProcLat.Mp2Rep`），**没有**对应的 `DistribMulAction` 实例。
本区从 `G.U`（`ℤ[Ω]` 上的正则作用）重建 `ℤ[G/H]` 分量的 `DistribMulAction`；
下一步是 `B = ℤ[Ω] ⊗ ℤ[Ω]` 的**对角**作用，最后合成到 `M_2'`。
-/

noncomputable instance snActionU : DistribMulAction (G.Gp 3) (G.ZOm 3) where
  smul g x := (G.U 3).ρ g x
  one_smul x := by
    show (G.U 3).ρ 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    show (G.U 3).ρ (g * h) x = (G.U 3).ρ g ((G.U 3).ρ h x)
    rw [Rep.ρ_mul]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _

lemma snActionU_smul (g : G.Gp 3) (x : G.ZOm 3) : g • x = (G.U 3).ρ g x := rfl


/-! ## §5 `S_n` 在 `M_2'` 上的作用：第二步（`B` 分量的**基级**置换，第三次路线）

`TensorProduct.map` 的作用律两次卡在 API（见 deadend-tensor-distribmulaction）。改走**基级**：
`B = ℤ[Ω] ⊗ ℤ[Ω]` 已有显式基 `tensorBasis : Basis (Ω × Ω) ℤ B`，故直接置换 `Ω × Ω` 的基元，
经 `Basis.repr` ＋ `Finsupp.domLCongr` 搬回 `B`——即 `ABGV52` 的 `latticeAlgebraEquiv` 同一模式，
**完全不碰 `TensorProduct` 的律**。
-/

/-- `Ω × Ω` 上的对角置换。 -/
def permOmega (σ : G.Gp 3) : G.OmegaP 3 × G.OmegaP 3 ≃ G.OmegaP 3 × G.OmegaP 3 :=
  Equiv.prodCongr σ σ

/-- `B = ℤ[Ω] ⊗ ℤ[Ω]` 上的**基级**置换作用（经 `tensorBasis` ＋ `Finsupp.domLCongr`）。 -/
noncomputable def permB (σ : G.Gp 3) :
    (G.ZOm 3 ⊗[ℤ] G.ZOm 3) ≃ₗ[ℤ] (G.ZOm 3 ⊗[ℤ] G.ZOm 3) :=
  (tensorBasis.repr).trans ((Finsupp.domLCongr (permOmega σ)).trans (tensorBasis.repr).symm)

lemma permB_one : permB 1 = LinearEquiv.refl ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3) := by
  simp only [permB, permOmega]
  rw [show Equiv.prodCongr (1 : G.Gp 3) 1 = Equiv.refl _ from rfl]
  simp


/-! ## §5b `permB` 的基值公式与两条实论律

基级路线（§5）的关键：`permB σ` 在基元上的作用就是**基指标置换** `permOmega σ`；
由此 `permB_mul` 只需 `Basis.ext` ＋ `permOmega_mul`。
**注意复合次序**：`LinearEquiv.trans` 的应用是 `(e₁.trans e₂) x = e₂ (e₁ x)`，
故 `permB (σ*τ) = (permB τ).trans (permB σ)`（**反序**写法、正序作用）。
-/

lemma permB_basis (σ : G.Gp 3) (i : G.OmegaP 3 × G.OmegaP 3) :
    permB σ (tensorBasis i) = tensorBasis (permOmega σ i) := by
  simp only [permB, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Finsupp.domLCongr_single, Module.Basis.repr_symm_single, one_smul]


lemma permOmega_mul (σ τ : G.Gp 3) (i : G.OmegaP 3 × G.OmegaP 3) :
    permOmega (σ * τ) i = permOmega σ (permOmega τ i) := by
  obtain ⟨a, b⟩ := i
  refine Prod.ext ?_ ?_
  · rfl
  · rfl

lemma permB_mul (σ τ : G.Gp 3) : permB (σ * τ) = (permB τ).trans (permB σ) := by
  have h : (permB (σ * τ) : G.ZOm 3 ⊗[ℤ] G.ZOm 3 →ₗ[ℤ] G.ZOm 3 ⊗[ℤ] G.ZOm 3)
      = ((permB τ).trans (permB σ) : G.ZOm 3 ⊗[ℤ] G.ZOm 3 →ₗ[ℤ] G.ZOm 3 ⊗[ℤ] G.ZOm 3) := by
    refine tensorBasis.ext (fun i => ?_)
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, permB_basis, LinearEquiv.trans_apply,
      permB_basis, permB_basis, permOmega_mul]
  exact LinearEquiv.toLinearMap_injective h
#print axioms permB_basis
#print axioms permOmega_mul
#print axioms permB_mul


/-! ## §5c `S_n` 在 `M_2' = B ⊕ ℤ[G/H]` 上的合成作用

逐分量：第一分量走 `permB`（基级，§5–§5b），第二分量走 `G.U` 的正则作用。四条实论律齐备
（零、加性、单位、乘法），故 `actM` 是 `M_2'` 上的**加法自同构**——这是把它搬到单项式域
（`permScale`）的前提。
-/

noncomputable def actM (σ : G.Gp 3) : Mprime → Mprime :=
  fun m => (permB σ m.1, (G.U 3).ρ σ m.2)

lemma actM_zero (σ : G.Gp 3) : actM σ 0 = 0 := by
  refine Prod.ext ?_ ?_
  · exact map_zero _
  · exact map_zero _

lemma actM_add (σ : G.Gp 3) (m n : Mprime) : actM σ (m + n) = actM σ m + actM σ n := by
  refine Prod.ext ?_ ?_
  · exact map_add _ _ _
  · exact map_add _ _ _

lemma actM_one (m : Mprime) : actM 1 m = m := by
  refine Prod.ext ?_ ?_
  · show permB 1 m.1 = m.1
    rw [permB_one]
    rfl
  · show (G.U 3).ρ 1 m.2 = m.2
    rw [map_one]
    rfl

lemma actM_mul (σ τ : G.Gp 3) (m : Mprime) : actM (σ * τ) m = actM σ (actM τ m) := by
  refine Prod.ext ?_ ?_
  · show permB (σ * τ) m.1 = permB σ (permB τ m.1)
    rw [permB_mul]
    rfl
  · show (G.U 3).ρ (σ * τ) m.2 = (G.U 3).ρ σ ((G.U 3).ρ τ m.2)
    rw [Rep.ρ_mul]
    rfl
#print axioms actM_zero
#print axioms actM_add
#print axioms actM_one
#print axioms actM_mul


/-! ## §5d `S_n` 在单项式域上的作用：`permScale`

通用**单项式搬运** `monoMap φ`（按 `φ` 搬每个单项式的指数）＋ 其加性／乘性；
取 `φ := ofAdd ∘ actM σ ∘ toAdd` 即得 **`permScale σ`** —— `S_n` 在 `A = F[M_2']` 上的作用。
四条律齐备（零／加／乘／单位），故 `permScale σ` 是 `F`-代数自同态。
-/

/-- **通用的单项式搬运**：按 `φ` 把每个单项式的指数搬走。 -/
noncomputable def monoMap (F : Type) [Field F]
    (φ : Multiplicative Mprime → Multiplicative Mprime)
    (x : EM.latticeAlgebra F Mprime) : EM.latticeAlgebra F Mprime :=
  ∑ m ∈ (MonoidAlgebra.coeff x).support, MonoidAlgebra.single (φ m) (MonoidAlgebra.coeff x m)

lemma monoMap_zero (F : Type) [Field F] (φ : Multiplicative Mprime → Multiplicative Mprime) :
    monoMap F φ (0 : EM.latticeAlgebra F Mprime) = 0 := by
  simp only [monoMap, MonoidAlgebra.coeff_zero, Finsupp.support_zero, Finset.sum_empty]

lemma monoMap_add (F : Type) [Field F] (φ : Multiplicative Mprime → Multiplicative Mprime)
    (x y : EM.latticeAlgebra F Mprime) :
    monoMap F φ (x + y) = monoMap F φ x + monoMap F φ y := by
  classical
  set S := (MonoidAlgebra.coeff x).support ∪ (MonoidAlgebra.coeff y).support with hS
  have hxy : MonoidAlgebra.coeff (x + y) = MonoidAlgebra.coeff x + MonoidAlgebra.coeff y := by
    rw [MonoidAlgebra.coeff_add]
  have e1 : monoMap F φ (x + y)
      = ∑ m ∈ S, MonoidAlgebra.single (φ m) (MonoidAlgebra.coeff (x + y) m) := by
    simp only [monoMap]
    refine Finset.sum_subset ?_ ?_
    · rw [hxy]; exact Finsupp.support_add
    · intro m _ hm
      have h0 : MonoidAlgebra.coeff (x + y) m = 0 := by
        by_contra hne
        exact hm (Finsupp.mem_support_iff.mpr hne)
      rw [h0, MonoidAlgebra.single_zero]
  have e2 : monoMap F φ x = ∑ m ∈ S, MonoidAlgebra.single (φ m) (MonoidAlgebra.coeff x m) := by
    simp only [monoMap]
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro m _ hm
    have h0 : MonoidAlgebra.coeff x m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    rw [h0, MonoidAlgebra.single_zero]
  have e3 : monoMap F φ y = ∑ m ∈ S, MonoidAlgebra.single (φ m) (MonoidAlgebra.coeff y m) := by
    simp only [monoMap]
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro m _ hm
    have h0 : MonoidAlgebra.coeff y m = 0 := by
      by_contra hne
      exact hm (Finsupp.mem_support_iff.mpr hne)
    rw [h0, MonoidAlgebra.single_zero]
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.single_add])
lemma monoMap_single (F : Type) [Field F] (φ : Multiplicative Mprime → Multiplicative Mprime)
    (m : Multiplicative Mprime) (c : F) :
    monoMap F φ (MonoidAlgebra.single m c) = MonoidAlgebra.single (φ m) c := by
  classical
  by_cases hc : c = 0
  · rw [hc, MonoidAlgebra.single_zero, MonoidAlgebra.single_zero, monoMap_zero]
  · have hsupp : (MonoidAlgebra.coeff (MonoidAlgebra.single m c)).support = {m} := by
      rw [MonoidAlgebra.coeff_single, Finsupp.support_single_ne_zero _ hc]
    rw [monoMap, hsupp, Finset.sum_singleton, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]

lemma monoMap_mul (F : Type) [Field F] (φ : Multiplicative Mprime → Multiplicative Mprime)
    (hφ : ∀ m n, φ (m * n) = φ m * φ n)
    (x y : EM.latticeAlgebra F Mprime) :
    monoMap F φ (x * y) = monoMap F φ x * monoMap F φ y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, monoMap_zero, zero_mul]
  | add x₁ x₂ ih1 ih2 => rw [add_mul, monoMap_add, ih1, ih2, monoMap_add, add_mul]
  | single m c =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, monoMap_zero, mul_zero]
    | add y₁ y₂ ih1 ih2 => rw [mul_add, monoMap_add, ih1, ih2, monoMap_add, mul_add]
    | single n d =>
      rw [MonoidAlgebra.single_mul_single, monoMap_single, monoMap_single, monoMap_single,
        hφ, MonoidAlgebra.single_mul_single]

open Procesi

noncomputable def permScale (F : Type) [Field F] (σ : G.Gp 3)
    (x : EM.latticeAlgebra F Mprime) : EM.latticeAlgebra F Mprime :=
  monoMap F (fun m => Multiplicative.ofAdd (actM σ (Multiplicative.toAdd m))) x

lemma permScale_zero (F : Type) [Field F] (σ : G.Gp 3) :
    permScale F σ (0 : EM.latticeAlgebra F Mprime) = 0 :=
  monoMap_zero F _

lemma permScale_add (F : Type) [Field F] (σ : G.Gp 3) (x y : EM.latticeAlgebra F Mprime) :
    permScale F σ (x + y) = permScale F σ x + permScale F σ y :=
  monoMap_add F _ x y

lemma permScale_mul (F : Type) [Field F] (σ : G.Gp 3) (x y : EM.latticeAlgebra F Mprime) :
    permScale F σ (x * y) = permScale F σ x * permScale F σ y := by
  refine monoMap_mul F _ ?_ x y
  intro m n
  show Multiplicative.ofAdd (actM σ (Multiplicative.toAdd (m * n)))
      = Multiplicative.ofAdd (actM σ (Multiplicative.toAdd m))
        * Multiplicative.ofAdd (actM σ (Multiplicative.toAdd n))
  rw [show Multiplicative.toAdd (m * n)
      = Multiplicative.toAdd m + Multiplicative.toAdd n from rfl, actM_add]
  rfl

lemma permScale_one (F : Type) [Field F] (σ : G.Gp 3) :
    permScale F σ (1 : EM.latticeAlgebra F Mprime) = 1 := by
  have h1 : (1 : EM.latticeAlgebra F Mprime) = MonoidAlgebra.single 1 1 :=
    (MonoidAlgebra.one_def).symm
  rw [permScale, h1, monoMap_single]
  have h2 : actM σ (Multiplicative.toAdd (1 : Multiplicative Mprime)) = 0 := by
    have h0 : Multiplicative.toAdd (1 : Multiplicative Mprime) = 0 := rfl
    rw [h0, actM_zero]
  rw [h2]
  rfl

#print axioms monoMap_zero
#print axioms monoMap_add
#print axioms monoMap_single
#print axioms monoMap_mul
#print axioms permScale
#print axioms permScale_zero
#print axioms permScale_add
#print axioms permScale_mul
#print axioms permScale_one


/-! ## §5e `permScale` 的环等价性

逆用 `σ⁻¹`：`actM σ⁻¹ ∘ actM σ = id`（由 `actM_mul` ＋ `actM_one`），故
`permScale σ⁻¹ ∘ permScale σ = id`（单项式归纳），即 **`permScaleEquiv σ : A ≃+* A`**。
下一步沿 `IsFractionRing.ringEquivOfRingEquiv` 提升到 `K = F(M_2')`。
-/

lemma actM_inv_comp (σ : G.Gp 3) (m : Mprime) : actM σ⁻¹ (actM σ m) = m := by
  have h := actM_mul σ⁻¹ σ m
  rw [inv_mul_cancel, actM_one] at h
  exact h.symm

lemma permScale_single (F : Type) [Field F] (σ : G.Gp 3)
    (m : Multiplicative Mprime) (c : F) :
    permScale F σ (MonoidAlgebra.single m c)
      = MonoidAlgebra.single (Multiplicative.ofAdd (actM σ (Multiplicative.toAdd m))) c :=
  monoMap_single F _ m c

lemma permScale_comp (F : Type) [Field F] (σ : G.Gp 3) (x : EM.latticeAlgebra F Mprime) :
    permScale F σ⁻¹ (permScale F σ x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [permScale_zero, permScale_zero]
  | add x₁ x₂ ih1 ih2 => rw [permScale_add, permScale_add, ih1, ih2]
  | single m c =>
    rw [permScale_single, permScale_single]
    show MonoidAlgebra.single
        (Multiplicative.ofAdd (actM σ⁻¹ (actM σ (Multiplicative.toAdd m)))) c
      = MonoidAlgebra.single m c
    rw [actM_inv_comp]
    rfl

noncomputable def permScaleEquiv (F : Type) [Field F] (σ : G.Gp 3) :
    EM.latticeAlgebra F Mprime ≃+* EM.latticeAlgebra F Mprime where
  toFun := permScale F σ
  invFun := permScale F σ⁻¹
  left_inv := permScale_comp F σ
  right_inv := by
    intro x
    exact permScale_comp F σ⁻¹ x
  map_add' := permScale_add F σ
  map_mul' := permScale_mul F σ
#print axioms actM_inv_comp
#print axioms permScale_single
#print axioms permScale_comp
#print axioms permScaleEquiv


/-! ## §5f `K = F(M_2')` 上的 `S_n` 作用 ＋ 不动点塔

由 §5e 的 `permScaleEquiv` 经 `IsFractionRing.ringEquivOfRingEquiv` 提升。
不动点塔：`T`-不变与 `S_n`-不变的合成仍固定（`tower_forward`）；反方向（交集 ＝ `N`-不动点）
需要两条**单位律** `ψ_1 = id`、`φ_1 = id`（已作为假设形式化，证明留待下一步）。
-/

noncomputable def permScaleFieldEquiv (F : Type) [Field F] (σ : G.Gp 3) :
    EM.latticeFunctionField F Mprime ≃+* EM.latticeFunctionField F Mprime :=
  IsFractionRing.ringEquivOfRingEquiv (permScaleEquiv F σ)

lemma permScaleFieldEquiv_algebraMap (F : Type) [Field F] (σ : G.Gp 3)
    (x : EM.latticeAlgebra F Mprime) :
    permScaleFieldEquiv F σ (algebraMap _ _ x) = algebraMap _ _ (permScale F σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (permScaleEquiv F σ) x


/-- `T`-不变（分式域层）。 -/
def TFixed (F : Type) [Field F] (α : EM.latticeFunctionField F Mprime) : Prop :=
  ∀ b : Fin 9 → Fˣ, torusScaleFieldEquiv F b α = α

/-- `S_n`-不变（分式域层）。 -/
def SFixed (F : Type) [Field F] (α : EM.latticeFunctionField F Mprime) : Prop :=
  ∀ σ : G.Gp 3, permScaleFieldEquiv F σ α = α

/-- **不动点塔的 `(⟸)` 方向**：`T`-不变且 `S_n`-不变 ⟹ 被两者的任意合成固定。 -/
theorem tower_forward (F : Type) [Field F] (α : EM.latticeFunctionField F Mprime)
    (h : TFixed F α ∧ SFixed F α) (σ : G.Gp 3) (b : Fin 9 → Fˣ) :
    torusScaleFieldEquiv F b (permScaleFieldEquiv F σ α) = α
      ∧ permScaleFieldEquiv F σ (torusScaleFieldEquiv F b α) = α := by
  obtain ⟨hT, hS⟩ := h
  exact ⟨by rw [hS]; exact hT b, by rw [hT]; exact hS σ⟩

/-- **`T`-不变的交集表述**（`(⟹)` 方向，`(⟸)` 需 `ψ_1 = id` 与 `φ_1 = id`，尚未机检）。 -/
theorem tower_backward_of_units (F : Type) [Field F]
    (hψ1 : ∀ α, permScaleFieldEquiv F 1 α = α)
    (hφ1 : ∀ α, torusScaleFieldEquiv F 1 α = α)
    (α : EM.latticeFunctionField F Mprime)
    (h : ∀ (σ : G.Gp 3) (b : Fin 9 → Fˣ),
      torusScaleFieldEquiv F b (permScaleFieldEquiv F σ α) = α
        ∧ permScaleFieldEquiv F σ (torusScaleFieldEquiv F b α) = α) :
    TFixed F α ∧ SFixed F α := by
  refine ⟨fun b => ?_, fun σ => ?_⟩
  · have h1 := (h 1 b).1
    rwa [hψ1 α] at h1
  · have h1 := (h σ 1).2
    rwa [hφ1 α] at h1
#print axioms permScaleFieldEquiv
#print axioms permScaleFieldEquiv_algebraMap
#print axioms tower_forward
#print axioms tower_backward_of_units


/-! ## §5g `permScale` 的单位律（`A` 层）

`permScale 1 = id`（单项式归纳 ＋ `actM_one`）。`K` 层的对应律
（`permScaleFieldEquiv 1 = 1`）需要 `IsFractionRing.ringHom_ext` 且要绕开 `↑` 强制转换，
尚未机检——登记于下一轮。
-/

lemma permScale_id (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime) :
    permScale F 1 x = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [permScale_zero]
  | add x₁ x₂ ih1 ih2 => rw [permScale_add, ih1, ih2]
  | single m c =>
    rw [permScale_single]
    have h : actM 1 (Multiplicative.toAdd m) = Multiplicative.toAdd m := actM_one _
    rw [h]
    rfl
#print axioms permScale_id


/-! ## §5h 单位律与**不动点塔（完整双向）**

两条 `K` 层单位律（`ψ_1 = id`、`φ_1 = id`）用 `IsFractionRing.div_surjective` 避开
ring-hom 层的 coercion 不匹配：把 `α` 写成 `ι a / ι b`，用 `map_div₀` ＋ 计算律 ＋ `A` 层单位律。
有了它们，塔的反方向（交集 ⟹ `N`-不动点）即可完成 —— **`tower_iff` 双向闭合**。
-/

lemma chi_one_param (F : Type) [Field F] (m : Mprime) : chi F 1 m = 1 := by
  show (↑(wt F (fun _ => 1) (fPrime (Multiplicative.toAdd m))) : F) = 1
  rw [wt_one]
  rfl

lemma torusScale_one_param (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime) :
    torusScale F 1 x = x := by
  apply MonoidAlgebra.coeff_injective
  ext m
  by_cases hm : m ∈ (MonoidAlgebra.coeff x).support
  · rw [torusScale_apply F 1 x m hm, chi_one_param F m, mul_one]
  · rw [torusScale_apply_of_notMem F 1 x m hm, eq_comm]
    by_contra hne
    exact hm (Finsupp.mem_support_iff.mpr hne)


lemma permScaleFieldEquiv_one_apply (F : Type) [Field F]
    (α : EM.latticeFunctionField F Mprime) : permScaleFieldEquiv F 1 α = α := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective
    (EM.latticeAlgebra F Mprime) α
  rw [map_div₀, permScaleFieldEquiv_algebraMap, permScaleFieldEquiv_algebraMap,
    permScale_id, permScale_id]

lemma torusScaleFieldEquiv_one_apply (F : Type) [Field F]
    (α : EM.latticeFunctionField F Mprime) : torusScaleFieldEquiv F 1 α = α := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective
    (EM.latticeAlgebra F Mprime) α
  rw [map_div₀, torusScaleFieldEquiv_algebraMap, torusScaleFieldEquiv_algebraMap,
    torusScale_one_param, torusScale_one_param]


/-- ★★★ **不动点塔（完整双向）**：`N = T ⋊ S_n` 的不动点 ＝ 两者的不动点之交。 -/
theorem tower_iff (F : Type) [Field F] (α : EM.latticeFunctionField F Mprime) :
    (TFixed F α ∧ SFixed F α)
      ↔ (∀ (σ : G.Gp 3) (b : Fin 9 → Fˣ),
          torusScaleFieldEquiv F b (permScaleFieldEquiv F σ α) = α
            ∧ permScaleFieldEquiv F σ (torusScaleFieldEquiv F b α) = α) := by
  constructor
  · rintro ⟨hT, hS⟩ σ b
    exact ⟨by rw [hS]; exact hT b, by rw [hT]; exact hS σ⟩
  · intro h
    refine ⟨fun b => ?_, fun σ => ?_⟩
    · have h1 := (h 1 b).1
      rwa [permScaleFieldEquiv_one_apply] at h1
    · have h1 := (h σ 1).2
      rwa [torusScaleFieldEquiv_one_apply] at h1
#print axioms chi_one_param
#print axioms torusScale_one_param
#print axioms permScaleFieldEquiv_one_apply
#print axioms torusScaleFieldEquiv_one_apply
#print axioms tower_iff


/-! ## §5i 基级↔张量级桥 ＋ `f'` 的 `S_n`-等变性

`tensorBasis (a,b) = e_a ⊗ e_b`，故 `permB σ`（基级置换）恰是 `TensorProduct.map (ρ σ) (ρ σ)`
（对角作用）——**桥** `permB_eq_map`。有了它，库内的 `G.phiFun_equivariant`（张量级）即可
搬到 `M_2'` 上，得 **`fPrime_actM`**：`f'(σ m) = σ(f' m)`。
这是半直积 `T ⋊ S_n` 相容性 `ψ_σ φ_b ψ_σ⁻¹ = φ_{σ·b}` 的关键。
-/

lemma tensorBasis_tmul (a b : G.OmegaP 3) :
    tensorBasis (a, b) = MonoidAlgebra.single a 1 ⊗ₜ[ℤ] MonoidAlgebra.single b 1 := by
  have h := Module.Basis.tensorProduct_apply (MonoidAlgebra.basis (G.OmegaP 3) ℤ)
    (MonoidAlgebra.basis (G.OmegaP 3) ℤ) a b
  simp only [MonoidAlgebra.basis_apply] at h
  exact h

lemma map_tensorBasis (σ : G.Gp 3) (a b : G.OmegaP 3) :
    TensorProduct.map ((G.U 3).ρ σ) ((G.U 3).ρ σ) (tensorBasis (a, b))
      = tensorBasis (permOmega σ (a, b)) := by
  rw [tensorBasis_tmul, TensorProduct.map_tmul, Representation.ofMulAction_single,
    Representation.ofMulAction_single]
  rw [show tensorBasis (permOmega σ (a, b))
      = MonoidAlgebra.single (σ • a) 1 ⊗ₜ[ℤ] MonoidAlgebra.single (σ • b) 1 from
    tensorBasis_tmul (σ • a) (σ • b)]

/-- ★ **基级↔张量级桥**：`permB σ` 就是对角的 `TensorProduct.map`。 -/
lemma permB_eq_map (σ : G.Gp 3) (x : G.ZOm 3 ⊗[ℤ] G.ZOm 3) :
    permB σ x = TensorProduct.map ((G.U 3).ρ σ) ((G.U 3).ρ σ) x := by
  have hmap : (permB σ : G.ZOm 3 ⊗[ℤ] G.ZOm 3 →ₗ[ℤ] G.ZOm 3 ⊗[ℤ] G.ZOm 3)
      = (TensorProduct.map ((G.U 3).ρ σ) ((G.U 3).ρ σ)
        : G.ZOm 3 ⊗[ℤ] G.ZOm 3 →ₗ[ℤ] G.ZOm 3 ⊗[ℤ] G.ZOm 3) := by
    refine Module.Basis.ext (b := tensorBasis) (fun i => ?_)
    rw [LinearEquiv.coe_coe, permB_basis]
    exact (map_tensorBasis σ i.1 i.2).symm
  exact congrArg (fun f => f x) hmap


/-- ★ **`f'` 的 `S_n`-等变性**（库内 `G.phiFun_equivariant` 经基级桥搬到 `M_2'`）。 -/
lemma fPrime_actM (σ : G.Gp 3) (m : Mprime) :
    fPrime (actM σ m) = (G.U 3).ρ σ (fPrime m) := by
  show G.phiFun 3 (permB σ m.1) = (G.U 3).ρ σ (G.phiFun 3 m.1)
  rw [permB_eq_map]
  exact G.phiFun_equivariant 3 σ m.1
#print axioms tensorBasis_tmul
#print axioms map_tensorBasis
#print axioms permB_eq_map
#print axioms fPrime_actM


/-- `M_2'` 上的经典可判定相等（张积无计算型 `DecidableEq`）。 -/
noncomputable instance : DecidableEq (Multiplicative Mprime) := Classical.decEq _

/-! ## §5j `S_n` 保持零权（核格）子域

`thm:14.17` 的最后一块语义：`S_n` 在 `F(M_r')` 上的作用**保持** `F(M_r)`（核格子域）。
机制 = `f'` 的等变性 ＋ `σ 0 = 0`：零权单项式被搬到零权单项式。
技术件：`monoMap` 的支撑落在 `φ` 的像里（`monoMap_support_subset`）。
-/

/-- `monoMap` 的支撑落在 `φ` 的像里。 -/
lemma monoMap_support_subset (F : Type) [Field F]
    (φ : Multiplicative Mprime → Multiplicative Mprime)
    (x : EM.latticeAlgebra F Mprime) :
    (MonoidAlgebra.coeff (monoMap F φ x)).support
      ⊆ (MonoidAlgebra.coeff x).support.image φ := by
  classical
  rw [monoMap]
  induction (MonoidAlgebra.coeff x).support using Finset.induction_on with
  | empty => rw [Finset.sum_empty, MonoidAlgebra.coeff_zero, Finsupp.support_zero]; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, MonoidAlgebra.coeff_add]
    refine (Finsupp.support_add).trans ?_
    rw [Finset.image_insert]
    refine Finset.union_subset ?_ ?_
    · rw [MonoidAlgebra.coeff_single]
      refine Finsupp.support_single_subset.trans ?_
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    · exact ih.trans (Finset.subset_insert _ _)


/-- ★★ **`S_n` 保持零权（核格）子域**：`permScale σ` 把零权元素送到零权元素。 -/
lemma permScale_weight_zero (F : Type) [Field F] (σ : G.Gp 3)
    (x : EM.latticeAlgebra F Mprime)
    (hx : ∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = 0) :
    ∀ m ∈ (MonoidAlgebra.coeff (permScale F σ x)).support,
      fPrime (Multiplicative.toAdd m) = 0 := by
  intro m hm
  have hsub := monoMap_support_subset F
    (fun m => Multiplicative.ofAdd (actM σ (Multiplicative.toAdd m))) x
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp (hsub hm)
  show fPrime (actM σ (Multiplicative.toAdd m₀)) = 0
  rw [fPrime_actM, hx m₀ hm₀, map_zero]
#print axioms monoMap_support_subset
#print axioms permScale_weight_zero


/-! ## §5k **`(C)` 层收口**：`K^T = Frac(F[M_2])` 与 `K^N = F(M_2)^{S_n}`

把 §2t 的 `(⊆)` 与 §2d 的 `(⊇)` 合成一句话：
**`α` 被整个环面固定 ⟺ `α` 是两**零权**（即支撑落在 `ker f'`）元素之比** ——
这正是 Saltman `lem:14.20` 的 `F(M_r')^T = F(M_r)`（`F(M_r)` 的元素就是零权元素之比）。
再加上不动点塔（§5h），即得 `K^N = F(M_2)^{S_n}` —— `thm:14.17` 的 `(C)` 层。
-/

/-- ★★★ **`lem:14.20` 的收口形式**：`K^T = Frac(F[M_2])`（固定 ⟺ 两零权元素之比）。 -/
theorem fixed_iff_weight_zero_ratio (F : Type) [Field F] [CharZero F]
    (α : EM.latticeFunctionField F Mprime) :
    TFixed F α ↔ ∃ f g : EM.latticeAlgebra F Mprime,
      (∀ m ∈ (MonoidAlgebra.coeff f).support, fPrime (Multiplicative.toAdd m) = 0)
      ∧ (∀ m ∈ (MonoidAlgebra.coeff g).support, fPrime (Multiplicative.toAdd m) = 0)
      ∧ g ≠ 0 ∧ α = iota F f / iota F g := by
  constructor
  · intro hT
    obtain ⟨f, g, hg, hfg⟩ := IsFractionRing.div_surjective
      (EM.latticeAlgebra F Mprime) α
    have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
    obtain ⟨f', g', hf', hgg', hg'0, heq⟩ :=
      fraction_fixed_imp_weight_zero_ratio F f g hg0 (by rw [hfg]; exact hT)
    exact ⟨f', g', hf', hgg', hg'0, by rw [← hfg, heq]⟩
  · rintro ⟨f, g, hf, hg, hg0, rfl⟩ b
    exact fraction_fixed_of_weight_zero F f g hg0 hf hg b


/-- ★★ **`thm:14.17` 的 `(C)` 层收口**：`K^N = F(M_2)^{S_n}`（零权之比 ∧ `S_n`-不变）。 -/
theorem N_fixed_iff_weight_zero_ratio (F : Type) [Field F] [CharZero F]
    (α : EM.latticeFunctionField F Mprime) :
    (TFixed F α ∧ SFixed F α) ↔
      (∃ f g : EM.latticeAlgebra F Mprime,
        (∀ m ∈ (MonoidAlgebra.coeff f).support, fPrime (Multiplicative.toAdd m) = 0)
        ∧ (∀ m ∈ (MonoidAlgebra.coeff g).support, fPrime (Multiplicative.toAdd m) = 0)
        ∧ g ≠ 0 ∧ α = iota F f / iota F g) ∧ SFixed F α := by
  rw [fixed_iff_weight_zero_ratio F α]
#print axioms fixed_iff_weight_zero_ratio
#print axioms N_fixed_iff_weight_zero_ratio


/-! ## §6 `(C1)` 第一步：把 `f'` 接到 Saltman 的**印刷定义**

Saltman（`thm:14.17` 的证明，印刷页 113）定义 `f'(u_i) = 0`、`f'(u_{ijk}) = u_i - u_j`。
本区核验本工作区的 `fPrime` 与之一致，并核 `(C1)` 的**计数**：基 = `n` 个 `u_i`
＋ `(r−1)n²` 个 `u_ijk` = `9 + 81 = 90`（与 `M_2' = B ⊕ ℤ[G/H]` 的秩一致）。
-/

/-- Saltman 的 `f'(u_i) = 0`：`ℤ[G/H]` 分量不进入 `f'`。 -/
lemma fPrime_basis_U (i : G.OmegaP 3) :
    fPrime ((0 : G.ZOm 3 ⊗[ℤ] G.ZOm 3), MonoidAlgebra.single i 1) = 0 := by
  show G.phiFun 3 (0 : G.ZOm 3 ⊗[ℤ] G.ZOm 3) = 0
  exact map_zero _

/-- Saltman 的 `f'(u_{ijk}) = u_i - u_j`：张量基元映到差。 -/
lemma fPrime_basis_B (i j : G.OmegaP 3) :
    fPrime ((MonoidAlgebra.single i 1 ⊗ₜ[ℤ] MonoidAlgebra.single j 1), (0 : G.ZOm 3))
      = MonoidAlgebra.single i 1 - MonoidAlgebra.single j 1 := by
  show G.phiFun 3 (MonoidAlgebra.single i 1 ⊗ₜ[ℤ] MonoidAlgebra.single j 1)
      = MonoidAlgebra.single i 1 - MonoidAlgebra.single j 1
  rw [G.phiFun_tmul, G.augF_single, G.augF_single, one_smul, one_smul]


/-- `(C1)` 的计数：`M_2'` 的基 = `n` 个 `u_i` ＋ `(r−1)n²` 个 `u_ijk`，`n = 9`、`r = 2` 时 = **90**。 -/
theorem card_basis_Mprime : Fintype.card (G.OmegaP 3 × G.OmegaP 3) + Fintype.card (G.OmegaP 3)
    = 90 := by
  simp [G.OmegaP, Fintype.card_prod]

/-- Saltman 的计数公式 `n + (r−1)n²`（`n = 9`、`r = 2`）＝ `90`。 -/
theorem card_saltman_formula : 9 + (2 - 1) * 9 ^ 2 = 90 := by norm_num
#print axioms fPrime_basis_U
#print axioms fPrime_basis_B
#print axioms card_basis_Mprime
#print axioms card_saltman_formula


/-! ## §7 `(C1)` 第二步：`M_2'` 的显式 **90 元** `ℤ`-基，及 `f'` 在基上的值

`M_2' = B ⊕ ℤ[G/H]` 的基 = `tensorBasis`（81 个 `u_ij`）＋ 单项式基（9 个 `u_i`），共 **90**。
`f'` 在基上恰是 Saltman 的印刷公式：`u_ijk ↦ u_i − u_j`、`u_i ↦ 0`。
这正是 `(C1)` 所需的**索引集**：`K'` 的生成元 `x_ii`（9 个）与 `y_ijk`（81 个）与这批基一一对应。
-/

/-- ★ **`M_2' = B ⊕ ℤ[G/H]` 的显式 `ℤ`-基**：`81` 个张量基元 ＋ `9` 个单项式基元 = **90** 元。 -/
noncomputable def mprimeBasis :
    Module.Basis (G.OmegaP 3 × G.OmegaP 3 ⊕ G.OmegaP 3) ℤ Mprime :=
  tensorBasis.prod (MonoidAlgebra.basis (G.OmegaP 3) ℤ)

/-- 基的基数：**90**（`(r−1)n² + n`，`n = 9`、`r = 2`）。 -/
theorem card_mprimeBasis :
    Fintype.card (G.OmegaP 3 × G.OmegaP 3 ⊕ G.OmegaP 3) = 90 := by
  rw [Fintype.card_sum, Fintype.card_prod]
  simp [G.OmegaP]

/-- `f'` 在基上的值：`inl (i,j) ↦ u_i − u_j`（Saltman 的 `f'(u_{ijk}) = u_i − u_j`）。 -/
lemma fPrime_mprimeBasis_inl (i j : G.OmegaP 3) :
    fPrime (mprimeBasis (Sum.inl (i, j))) = MonoidAlgebra.single i 1 - MonoidAlgebra.single j 1 := by
  rw [mprimeBasis, Module.Basis.prod_apply]
  simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
  rw [tensorBasis_tmul]
  exact fPrime_basis_B i j

/-- `f'` 在基上的值：`inr i ↦ 0`（Saltman 的 `f'(u_i) = 0`）。 -/
lemma fPrime_mprimeBasis_inr (i : G.OmegaP 3) :
    fPrime (mprimeBasis (Sum.inr i)) = 0 := by
  rw [mprimeBasis, Module.Basis.prod_apply]
  simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply]
  rw [MonoidAlgebra.basis_apply]
  exact fPrime_basis_U i
#print axioms mprimeBasis
#print axioms card_mprimeBasis
#print axioms fPrime_mprimeBasis_inl
#print axioms fPrime_mprimeBasis_inr


/-! ## §8 `(C1)` 第三步：基变换 —— `F(M_2') ≅ F[90 个变量的 Laurent 分数域]`

`M_2'` 是自由 `ℤ`-模（§7 的 `mprimeBasis`，90 元），故对任意自由模 `Idx → ℤ`（同一索引集）
有 `M_2' ≃ₗ Idx → ℤ`，诱导 `F[M_2'] ≃+* F[Idx → ℤ]`（`MonoidAlgebra.mapDomainRingEquiv`），
再诱导分式域同构。**这就是 `(C1)` 中「`K'` 与 `F(M_2')` 是同一个有理函数域」的代数内容**：
`K'` 的 90 个不定元与 `M_2'` 的 90 个基元一一对应。
-/

/-- 索引集：81 个张量基元 ＋ 9 个单项式基元 = 90。 -/
abbrev Idx := G.OmegaP 3 × G.OmegaP 3 ⊕ G.OmegaP 3

/-- 沿 `mprimeBasis` 的 `ℤ`-线性同构 `M_2' ≃ (Idx → ℤ)`。 -/
noncomputable def mprimeEquivFun : Mprime ≃ₗ[ℤ] (Idx → ℤ) :=
  mprimeBasis.equivFun

/-- 对应的 `MulEquiv`（`Multiplicative` 视角）。 -/
noncomputable def mprimeMulEquiv : Multiplicative Mprime ≃* Multiplicative (Idx → ℤ) :=
  mprimeEquivFun.toAddEquiv.toMultiplicative

/-- ★ **基变换**：`F[M_2'] ≅ F[90 个变量]`。 -/
noncomputable def latticeAlgebraBasisEquiv (F : Type) [Field F] :
    EM.latticeAlgebra F Mprime ≃+* EM.latticeAlgebra F (Idx → ℤ) :=
  MonoidAlgebra.mapDomainRingEquiv F mprimeMulEquiv


/-- ★★ **`F(M_2') ≅ F[90 个变量的 Laurent 分数域]`**——`(C1)` 的基变换步。 -/
noncomputable def latticeFunctionFieldBasisEquiv (F : Type) [Field F] :
    EM.latticeFunctionField F Mprime ≃+* EM.latticeFunctionField F (Idx → ℤ) :=
  IsFractionRing.ringEquivOfRingEquiv (latticeAlgebraBasisEquiv F)
#print axioms mprimeEquivFun
#print axioms mprimeMulEquiv
#print axioms latticeAlgebraBasisEquiv
#print axioms latticeFunctionFieldBasisEquiv


/-! ## §9 `(C1)` 第四步：`Idx` 上的 `S_n` 作用与基变换的计算律

`Idx = (Ω × Ω) ⊕ Ω` 上 `S_n` 逐分量作用（`Equiv.sumCongr (permOmega σ) σ`），
故 `mprimeEquivFun` 把 `actM σ` 的基向量送到 `idxPerm σ` 后的索引——`(C1)` 的 `S_n`-等变性
在**基向量层**的全部内容就是这两条计算律。
-/

/-- `Idx` 上的 `S_n` 作用（`Sum` 逐分量：张量分量用 `permOmega`，单项式分量用 `σ` 本身）。 -/
def idxPerm (σ : G.Gp 3) : Idx ≃ Idx := Equiv.sumCongr (permOmega σ) σ

lemma idxPerm_inl (σ : G.Gp 3) (i : G.OmegaP 3 × G.OmegaP 3) :
    idxPerm σ (Sum.inl i) = Sum.inl (permOmega σ i) := rfl

lemma idxPerm_inr (σ : G.Gp 3) (i : G.OmegaP 3) :
    idxPerm σ (Sum.inr i) = Sum.inr (σ i) := rfl



lemma mprimeEquivFun_inl (p q : G.OmegaP 3) :
    mprimeEquivFun ((tensorBasis (p, q), (0 : G.ZOm 3)) : Mprime)
      = Finsupp.single (Sum.inl (p, q)) 1 := by
  have h : ((tensorBasis (p, q), (0 : G.ZOm 3)) : Mprime)
      = mprimeBasis (Sum.inl (p, q)) := by
    rw [mprimeBasis, Module.Basis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
  rw [h, mprimeEquivFun, Module.Basis.equivFun_apply, Module.Basis.repr_self]

lemma mprimeEquivFun_inr (i : G.OmegaP 3) :
    mprimeEquivFun (((0 : G.ZOm 3 ⊗[ℤ] G.ZOm 3), MonoidAlgebra.single i 1) : Mprime)
      = Finsupp.single (Sum.inr i) 1 := by
  have h : (((0 : G.ZOm 3 ⊗[ℤ] G.ZOm 3), MonoidAlgebra.single i 1) : Mprime)
      = mprimeBasis (Sum.inr i) := by
    rw [mprimeBasis, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      MonoidAlgebra.basis_apply]
  rw [h, mprimeEquivFun, Module.Basis.equivFun_apply, Module.Basis.repr_self]
#print axioms idxPerm
#print axioms idxPerm_inl
#print axioms idxPerm_inr
#print axioms mprimeEquivFun_inl
#print axioms mprimeEquivFun_inr


/-! ## §10 `(C1)` 第五步：基向量层的**统一**等式

把 §9 的两条计算律合成一条：**`mprimeEquivFun` 把 `actM σ` 追踪为 `idxPerm σ`**——
对 `M_2'` 的每个基向量 `i`，`mprimeEquivFun (actM σ (mprimeBasis i)) = single (idxPerm σ i) 1`。
（`inl` 分量用 `permB_basis`，`inr` 分量用 `ofMulAction_single`。）
-/

/-- `mprimeBasis` 的两个分量（`inl`）。 -/
lemma mprimeBasis_fst_inl (p q : G.OmegaP 3) :
    (mprimeBasis (Sum.inl (p, q))).1 = tensorBasis (p, q) := by
  rw [mprimeBasis, Module.Basis.prod_apply]
  simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]

lemma mprimeBasis_snd_inl (p q : G.OmegaP 3) :
    (mprimeBasis (Sum.inl (p, q))).2 = 0 := by
  rw [mprimeBasis, Module.Basis.prod_apply]
  simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]

lemma mprimeBasis_fst_inr (i : G.OmegaP 3) :
    (mprimeBasis (Sum.inr i)).1 = 0 := by
  rw [mprimeBasis, Module.Basis.prod_apply]
  simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply]

lemma mprimeBasis_snd_inr (i : G.OmegaP 3) :
    (mprimeBasis (Sum.inr i)).2 = MonoidAlgebra.single i 1 := by
  rw [mprimeBasis, Module.Basis.prod_apply]
  simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
    MonoidAlgebra.basis_apply]

/-- ★★ **基向量层的统一等式**：`mprimeEquivFun` 追踪 `actM σ` 为 `idxPerm σ`。 -/
lemma mprimeEquivFun_actM_basis (σ : G.Gp 3) (i : Idx) :
    mprimeEquivFun (actM σ (mprimeBasis i)) = Finsupp.single (idxPerm σ i) 1 := by
  obtain (⟨p, q⟩ | r) := i
  · rw [show actM σ (mprimeBasis (Sum.inl (p, q)))
        = (tensorBasis (permOmega σ (p, q)), 0) from by
      refine Prod.ext ?_ ?_
      · rw [show (actM σ (mprimeBasis (Sum.inl (p, q)))).1
            = permB σ (mprimeBasis (Sum.inl (p, q))).1 from rfl,
          mprimeBasis_fst_inl, permB_basis]
      · rw [show (actM σ (mprimeBasis (Sum.inl (p, q)))).2
            = (G.U 3).ρ σ (mprimeBasis (Sum.inl (p, q))).2 from rfl,
          mprimeBasis_snd_inl, map_zero]]
    rw [mprimeEquivFun_inl, idxPerm_inl]
  · rw [show actM σ (mprimeBasis (Sum.inr r))
        = (0, MonoidAlgebra.single (σ r) 1) from by
      refine Prod.ext ?_ ?_
      · rw [show (actM σ (mprimeBasis (Sum.inr r))).1
            = permB σ (mprimeBasis (Sum.inr r)).1 from rfl,
          mprimeBasis_fst_inr, map_zero]
      · rw [show (actM σ (mprimeBasis (Sum.inr r))).2
            = (G.U 3).ρ σ (mprimeBasis (Sum.inr r)).2 from rfl,
          mprimeBasis_snd_inr, Representation.ofMulAction_single]
        exact rfl]
    rw [mprimeEquivFun_inr, idxPerm_inr]
#print axioms mprimeBasis_fst_inl
#print axioms mprimeBasis_snd_inl
#print axioms mprimeBasis_fst_inr
#print axioms mprimeBasis_snd_inr
#print axioms mprimeEquivFun_actM_basis


/-! ## §11 `(C1)` 第六步（半）：`actM` 作加法同态 ＋ 基展开

把 `actM σ` 打包成 `AddMonoidHom`，即可用 `map_sum`／`map_zsmul`——**基展开**
`actM σ m = Σ_i (repr m)_i • actM σ (basis i)` 是本区的主要产出，它是「提升到整个代数」的
两半之一。另一半（`Idx → ℤ` 侧的 `Finsupp` 展开）**卡在模型选择上**，见 §12 的登记。
-/

/-- `actM σ` 作为加法同态（便于 `map_sum`／`map_zsmul`）。 -/
noncomputable def actMHom (σ : G.Gp 3) : Mprime →+ Mprime where
  toFun := actM σ
  map_zero' := actM_zero σ
  map_add' := actM_add σ

@[simp] lemma actMHom_apply (σ : G.Gp 3) (m : Mprime) : actMHom σ m = actM σ m := rfl

/-- 基展开后 `actM` 逐项作用。 -/
lemma actM_eq_sum (σ : G.Gp 3) (m : Mprime) :
    actM σ m = ∑ i, mprimeBasis.repr m i • actM σ (mprimeBasis i) := by
  have h : actMHom σ m = ∑ i, mprimeBasis.repr m i • actMHom σ (mprimeBasis i) := by
    conv_lhs => rw [← Module.Basis.sum_repr mprimeBasis m]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_zsmul _ _ _)
  simpa using h
#print axioms actMHom
#print axioms actM_eq_sum


/-! ## §12 `(C1)` 第六步：换模型到 `Idx →₀ ℤ`（`Finsupp` 版）

§8 用 `Basis.equivFun` 取到 `Idx → ℤ`（**函数**），致 `Finsupp.domCongr`／`mapDomain` 无法作用
（见 deadend 追加节）。本区改用 `mprimeBasis.repr : M_2' ≃ₗ (Idx →₀ ℤ)`（**`Finsupp`**），
并补齐基向量层与线性层的全部件：`actMLinear`（`actM σ` 作 `ℤ`-线性映射）＋
`mprimeRepr_actM_basis`（基向量被 `idxPerm` 追踪）。**提升到一般 `m` 尚待**（两半已各自就位：
§11 的 `actM_eq_sum` 与 §44 的 `domCongr` 展开式）。
-/

/-- `repr` 在 `inl` 基向量上的值（`Idx →₀ ℤ` 模型）。 -/
lemma mprimeRepr_inl (p q : G.OmegaP 3) :
    mprimeBasis.repr ((tensorBasis (p, q), (0 : G.ZOm 3)) : Mprime)
      = Finsupp.single (Sum.inl (p, q)) 1 := by
  have h : ((tensorBasis (p, q), (0 : G.ZOm 3)) : Mprime)
      = mprimeBasis (Sum.inl (p, q)) := by
    rw [mprimeBasis, Module.Basis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
  rw [h, Module.Basis.repr_self]

lemma mprimeRepr_inr (i : G.OmegaP 3) :
    mprimeBasis.repr (((0 : G.ZOm 3 ⊗[ℤ] G.ZOm 3), MonoidAlgebra.single i 1) : Mprime)
      = Finsupp.single (Sum.inr i) 1 := by
  have h : (((0 : G.ZOm 3 ⊗[ℤ] G.ZOm 3), MonoidAlgebra.single i 1) : Mprime)
      = mprimeBasis (Sum.inr i) := by
    rw [mprimeBasis, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      MonoidAlgebra.basis_apply]
  rw [h, Module.Basis.repr_self]

/-- `repr` 在 `inl` 基向量上的值（统一形式）。 -/
lemma mprimeRepr_inl_basis (p q : G.OmegaP 3) :
    mprimeBasis.repr (mprimeBasis (Sum.inl (p, q)))
      = Finsupp.single (Sum.inl (p, q)) 1 :=
  Module.Basis.repr_self _ _

/-- `actM σ` 作为 `ℤ`-线性映射。 -/
noncomputable def actMLinear (σ : G.Gp 3) : Mprime →ₗ[ℤ] Mprime where
  toFun := actM σ
  map_add' := actM_add σ
  map_smul' c m := by
    show actM σ (c • m) = c • actM σ m
    exact map_zsmul (actMHom σ) c m


lemma mprimeRepr_actM_basis (σ : G.Gp 3) (i : Idx) :
    mprimeBasis.repr (actM σ (mprimeBasis i)) = Finsupp.single (idxPerm σ i) 1 := by
  obtain (⟨p, q⟩ | r) := i
  · rw [show actM σ (mprimeBasis (Sum.inl (p, q)))
        = (tensorBasis (permOmega σ (p, q)), 0) from by
      refine Prod.ext ?_ ?_
      · rw [show (actM σ (mprimeBasis (Sum.inl (p, q)))).1
            = permB σ (mprimeBasis (Sum.inl (p, q))).1 from rfl,
          mprimeBasis_fst_inl, permB_basis]
      · rw [show (actM σ (mprimeBasis (Sum.inl (p, q)))).2
            = (G.U 3).ρ σ (mprimeBasis (Sum.inl (p, q))).2 from rfl,
          mprimeBasis_snd_inl, map_zero]]
    rw [mprimeRepr_inl, idxPerm_inl]
  · rw [show actM σ (mprimeBasis (Sum.inr r)) = (0, MonoidAlgebra.single (σ r) 1) from by
      refine Prod.ext ?_ ?_
      · rw [show (actM σ (mprimeBasis (Sum.inr r))).1
            = permB σ (mprimeBasis (Sum.inr r)).1 from rfl,
          mprimeBasis_fst_inr, map_zero]
      · rw [show (actM σ (mprimeBasis (Sum.inr r))).2
            = (G.U 3).ρ σ (mprimeBasis (Sum.inr r)).2 from rfl,
          mprimeBasis_snd_inr, Representation.ofMulAction_single]
        exact rfl]
    rw [mprimeRepr_inr, idxPerm_inr]
#print axioms mprimeRepr_inl
#print axioms mprimeRepr_inr
#print axioms mprimeRepr_inl_basis
#print axioms actMLinear
#print axioms mprimeRepr_actM_basis


/-! ## §13 `(C1)` 提升步：`repr (actM σ m)` 的求和展开

把 §11 的基展开（`actM_eq_sum`）经 `repr` 的线性推到系数层：
`repr (actM σ m) = Σ_i (repr m)_i • single (idxPerm σ i) 1`。
这是合并式 `repr (actM σ m) = domCongr (idxPerm σ) (repr m)` 的**左端**；
右端的对应展开与两端的系数比较**尚未机检**（登记于 deadend 笔记的第四次追加）。
-/

/-- `repr (actM σ m)` 的求和展开（`Finsupp` 版）。 -/
lemma mprimeRepr_actM_eq_sum (σ : G.Gp 3) (m : Mprime) :
    mprimeBasis.repr (actM σ m)
      = ∑ i, mprimeBasis.repr m i • Finsupp.single (idxPerm σ i) 1 := by
  conv_lhs => rw [actM_eq_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, mprimeRepr_actM_basis])
#print axioms mprimeRepr_actM_eq_sum


/-! ## §14 `(C1)` 提升步**完成**：`repr` 把 `actM σ` 追踪为 `idxPerm σ`

四次 API 攻坚后（见 deadend 笔记）走通 **系数逐点** 路线：先证
`(repr (actM σ m)) k = (repr m) ((idxPerm σ)⁻¹ k)`（`Finsupp.finsetSum_apply` ＋
`Finset.sum_eq_single` ＋ `single_eq_same`／`single_eq_of_ne`），再用 `Finsupp.ext`
与 `domCongr` 的计算律收口。
**关键旁因**：前几轮的部分失败源于 **`.olean` 陈旧**（`lake env lean` 不刷新供 import 用的产物，
`lake build` 才刷新）——见日志的工艺条。
-/

/-- 系数公式：`(repr (actM σ m)) k = (repr m) ((idxPerm σ)⁻¹ k)`。 -/
lemma mprimeRepr_actM_apply (σ : G.Gp 3) (m : Mprime) (k : Idx) :
    mprimeBasis.repr (actM σ m) k
      = (mprimeBasis.repr m) ((idxPerm σ).symm k) := by
  rw [mprimeRepr_actM_eq_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (M := ℤ) ((idxPerm σ).symm k)]
  · simp only [Finsupp.smul_apply, Equiv.apply_symm_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · intro b _ hb
    have hne : (idxPerm σ) b ≠ k := by
      intro h
      exact hb (by rw [← h, Equiv.symm_apply_apply])
    simp only [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- ★★★ **`(C1)` 的合并式（提升步完成）**：`repr` 把 `actM σ` 追踪为 `idxPerm σ` 的 `Finsupp` 搬运。 -/
lemma mprimeRepr_actM (σ : G.Gp 3) (m : Mprime) :
    mprimeBasis.repr (actM σ m)
      = Finsupp.domCongr (idxPerm σ) (mprimeBasis.repr m) := by
  refine Finsupp.ext (fun k => ?_)
  rw [mprimeRepr_actM_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
#print axioms mprimeRepr_actM_apply
#print axioms mprimeRepr_actM


/-! ## §15 **`(C1)` 的方块（单项式层）**：`permScale` 在 `repr` 下恰是变量置换

Saltman 原文的 `S_n`-不变性依据是「`P_σ X P_σ^{-1}` 的 `i,i` 元是 `x_{σ(i)σ(i)}`」——
即**变量置换**。本区把这句话机检为一条等式：
`latticeAlgebraBasisEquiv (permScale σ (single m c)) = single (ofAdd (mprimeEquivFun m ∘ (idxPerm σ)⁻¹)) c`。
机制 = §14 的 `mprimeRepr_actM`（`repr` 追踪 `actM`）＋ `MonoidAlgebra.mapDomainRingEquiv_single`。
-/

/-- `(C1)` 环同构在单项式上的值。 -/
lemma latticeAlgebraBasisEquiv_single (F : Type) [Field F]
    (m : Multiplicative Mprime) (c : F) :
    latticeAlgebraBasisEquiv F (MonoidAlgebra.single m c)
      = MonoidAlgebra.single (mprimeMulEquiv m) c :=
  MonoidAlgebra.mapDomainRingEquiv_single mprimeMulEquiv c m

/-- `mprimeEquivFun` 与 `repr` 的一致性。 -/
lemma mprimeEquivFun_eq_coe (m : Mprime) :
    mprimeEquivFun m = ⇑(mprimeBasis.repr m) :=
  Module.Basis.equivFun_apply mprimeBasis m

/-- `mprimeMulEquiv` 的 `toAdd` 就是 `mprimeEquivFun`。 -/
lemma mprimeMulEquiv_toAdd (m : Multiplicative Mprime) :
    Multiplicative.toAdd (mprimeMulEquiv m) = mprimeEquivFun (Multiplicative.toAdd m) := rfl

/-- ★★★ **`(C1)` 的方块（单项式层）**：`permScale` 在 `repr` 下恰是 `idxPerm` 的变量置换。 -/
theorem latticeAlgebraBasisEquiv_permScale_single (F : Type) [Field F] (σ : G.Gp 3)
    (m : Multiplicative Mprime) (c : F) :
    latticeAlgebraBasisEquiv F (permScale F σ (MonoidAlgebra.single m c))
      = MonoidAlgebra.single (Multiplicative.ofAdd
          (mprimeEquivFun (Multiplicative.toAdd m) ∘ (idxPerm σ).symm)) c := by
  rw [permScale_single, latticeAlgebraBasisEquiv_single]
  have h : Multiplicative.toAdd
        (mprimeMulEquiv (Multiplicative.ofAdd (actM σ (Multiplicative.toAdd m))))
      = Multiplicative.toAdd (Multiplicative.ofAdd
          (mprimeEquivFun (Multiplicative.toAdd m) ∘ (idxPerm σ).symm)) := by
    rw [mprimeMulEquiv_toAdd]
    show mprimeEquivFun (actM σ (Multiplicative.toAdd m))
      = mprimeEquivFun (Multiplicative.toAdd m) ∘ (idxPerm σ).symm
    rw [mprimeEquivFun_eq_coe, mprimeRepr_actM, mprimeEquivFun_eq_coe,
      Finsupp.domCongr_apply]
    funext k
    rw [Finsupp.equivMapDomain_apply]
    rfl
  rw [Multiplicative.toAdd.injective h]
#print axioms latticeAlgebraBasisEquiv_single
#print axioms mprimeEquivFun_eq_coe
#print axioms mprimeMulEquiv_toAdd
#print axioms latticeAlgebraBasisEquiv_permScale_single


/-! ## §16 **`(C1)` 收口：识别保 `S_n` 作用**

Saltman：「It follows that the identification of `K'` with `F(M_r')` is `S_n` invariant.」
本区把 `S_n` 在 `K'` 侧的作用**沿同构共轭**定义为 `idxScale`／`idxScaleFieldEquiv`，
于是方块**按定义成立**（`rfl` 级）；其**实质内容**在 §15 的单项式公式——
它证明这个共轭作用**就是变量置换**（`x_ii ↦ x_{σ(i)σ(i)}`）。
-/

/-- `Idx` 侧的 `S_n` 作用：把 `permScale` **沿同构共轭**过来。 -/
noncomputable def idxScale (F : Type) [Field F] (σ : G.Gp 3)
    (x : EM.latticeAlgebra F (Idx → ℤ)) : EM.latticeAlgebra F (Idx → ℤ) :=
  latticeAlgebraBasisEquiv F (permScale F σ ((latticeAlgebraBasisEquiv F).symm x))

/-- ★★★ **`(C1)` 的方块（代数层）**：`permScale` 在环同构下**恰是** `idxScale`。 -/
theorem latticeAlgebraBasisEquiv_permScale (F : Type) [Field F] (σ : G.Gp 3)
    (x : EM.latticeAlgebra F Mprime) :
    latticeAlgebraBasisEquiv F (permScale F σ x)
      = idxScale F σ (latticeAlgebraBasisEquiv F x) := by
  simp only [idxScale, RingEquiv.symm_apply_apply]

/-- `idxScale` 在单项式上的值 ＝ §15 的变量置换公式。 -/
theorem idxScale_single (F : Type) [Field F] (σ : G.Gp 3)
    (m : Multiplicative Mprime) (c : F) :
    idxScale F σ (latticeAlgebraBasisEquiv F (MonoidAlgebra.single m c))
      = MonoidAlgebra.single (Multiplicative.ofAdd
          (mprimeEquivFun (Multiplicative.toAdd m) ∘ (idxPerm σ).symm)) c := by
  rw [← latticeAlgebraBasisEquiv_permScale]
  exact latticeAlgebraBasisEquiv_permScale_single F σ m c


/-- `Idx` 侧分式域上的 `S_n` 作用（共轭）。 -/
noncomputable def idxScaleFieldEquiv (F : Type) [Field F] (σ : G.Gp 3) :
    EM.latticeFunctionField F (Idx → ℤ) ≃+* EM.latticeFunctionField F (Idx → ℤ) :=
  (latticeFunctionFieldBasisEquiv F).symm.trans
    ((permScaleFieldEquiv F σ).trans (latticeFunctionFieldBasisEquiv F))

/-- ★★★ **`(C1)` 的方块（分式域层）**：识别**保 `S_n` 作用**。 -/
theorem latticeFunctionFieldBasisEquiv_permScaleFieldEquiv (F : Type) [Field F]
    (σ : G.Gp 3) (α : EM.latticeFunctionField F Mprime) :
    latticeFunctionFieldBasisEquiv F (permScaleFieldEquiv F σ α)
      = idxScaleFieldEquiv F σ (latticeFunctionFieldBasisEquiv F α) := by
  simp only [idxScaleFieldEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
#print axioms idxScale
#print axioms latticeAlgebraBasisEquiv_permScale
#print axioms idxScale_single
#print axioms idxScaleFieldEquiv
#print axioms latticeFunctionFieldBasisEquiv_permScaleFieldEquiv


/-! ## §17 **格桥**（第一步）：`F[ker f'] ≅ F[Lat]`、`F(ker f') ≅ F(Lat)`

H2 主线用的抽象格是 `Lat = ProcLat.Mp2 3 = ker φ × ℤ[G/H]`（**秩 82**）；
本工作区的零权格是**子模** `ker f' ⊆ M_2'`。§1 的 `kerFPrimeEquiv` 早已给出
`ker f' ≃ₗ Lat`，故沿 `MonoidAlgebra.mapDomainRingEquiv` 得环同构，再经
`IsFractionRing.ringEquivOfRingEquiv` 得分式域同构。**这是到 `invariantsField` 的第一层桥。**
-/

/-- 格桥：`ker f' ≃ Lat` 诱导的 `MulEquiv`。 -/
noncomputable def kerFPrimeMulEquiv :
    Multiplicative ↥(LinearMap.ker fPrime) ≃* Multiplicative (ProcLat.Mp2 3) :=
  kerFPrimeEquiv.toAddEquiv.toMultiplicative

/-- ★ **格桥（代数层）**：`F[ker f'] ≅ F[Lat]`。 -/
noncomputable def latticeAlgebraKerEquiv (F : Type) [Field F] :
    EM.latticeAlgebra F ↥(LinearMap.ker fPrime) ≃+* EM.latticeAlgebra F (ProcLat.Mp2 3) :=
  MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv

/-- ★ **格桥（分式域层）**：`F(ker f') ≅ F(Lat)`。 -/
noncomputable def latticeFunctionFieldKerEquiv (F : Type) [Field F] :
    EM.latticeFunctionField F ↥(LinearMap.ker fPrime) ≃+*
      EM.latticeFunctionField F (ProcLat.Mp2 3) :=
  IsFractionRing.ringEquivOfRingEquiv (latticeAlgebraKerEquiv F)
#print axioms kerFPrimeMulEquiv
#print axioms latticeAlgebraKerEquiv
#print axioms latticeFunctionFieldKerEquiv


/-! ## §18 **格桥第二层**：子模包含诱导的环同态，其像落在**零权**元素里

`F[ker f'] →+* F[M_2']`（沿子模包含 `ker f' ⊆ M_2'`），且像落在零权部分
（`f'` 在像是 0——这正是「`ker f'` 的定义在环层的声音」）。这是把 §17 的格桥
接到 §5j／§5k 的零权子域的**那一半**；另一半（像 ＝ 全体零权元素）待做。
-/

/-- 子模包含诱导的 `MonoidHom`（加法群视角）。 -/
def kerInclMonoidHom : Multiplicative ↥(LinearMap.ker fPrime) →* Multiplicative Mprime where
  toFun m := Multiplicative.ofAdd ((Multiplicative.toAdd m : ↥(LinearMap.ker fPrime)) : Mprime)
  map_one' := by
    apply Multiplicative.toAdd.injective
    rfl
  map_mul' m n := by
    apply Multiplicative.toAdd.injective
    rfl

/-- ★ **格桥第二层**：子模包含诱导的环同态 `F[ker f'] → F[M_2']`。 -/
noncomputable def latticeAlgebraIncl (F : Type) [Field F] :
    EM.latticeAlgebra F ↥(LinearMap.ker fPrime) →+* EM.latticeAlgebra F Mprime :=
  MonoidAlgebra.mapDomainRingHom F kerInclMonoidHom


lemma latticeAlgebraIncl_single (F : Type) [Field F]
    (m : Multiplicative ↥(LinearMap.ker fPrime)) (c : F) :
    latticeAlgebraIncl F (MonoidAlgebra.single m c)
      = MonoidAlgebra.single (kerInclMonoidHom m) c :=
  MonoidAlgebra.mapDomain_single

/-- ★★ **格桥第二层的实质**：`F[ker f']` 的像落在**零权**元素里。 -/
lemma latticeAlgebraIncl_weight_zero (F : Type) [Field F]
    (x : EM.latticeAlgebra F ↥(LinearMap.ker fPrime))
    (m : Multiplicative Mprime)
    (hm : m ∈ (MonoidAlgebra.coeff (latticeAlgebraIncl F x)).support) :
    fPrime (Multiplicative.toAdd m) = 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, MonoidAlgebra.coeff_zero] at hm; simp at hm
  | add x₁ x₂ ih1 ih2 =>
    rw [map_add, MonoidAlgebra.coeff_add, Finsupp.mem_support_iff, Finsupp.add_apply] at hm
    by_cases h1 : MonoidAlgebra.coeff (latticeAlgebraIncl F x₁) m = 0
    · exact ih2 (Finsupp.mem_support_iff.mpr (by rw [h1, zero_add] at hm; exact hm))
    · exact ih1 (Finsupp.mem_support_iff.mpr h1)
  | single n c =>
    rw [latticeAlgebraIncl_single, MonoidAlgebra.coeff_single, Finsupp.mem_support_iff] at hm
    have hnm : Finsupp.single (kerInclMonoidHom n) c m ≠ 0 := hm
    have hEq : kerInclMonoidHom n = m := by
      by_contra hne
      exact hnm (Finsupp.single_eq_of_ne (Ne.symm hne))
    rw [← hEq]
    show fPrime ((Multiplicative.toAdd n : ↥(LinearMap.ker fPrime)) : Mprime) = 0
    exact n.2
#print axioms kerInclMonoidHom
#print axioms latticeAlgebraIncl
#print axioms latticeAlgebraIncl_single
#print axioms latticeAlgebraIncl_weight_zero


/-! ## §19 格桥第三层的**实例条件**：`F(ker f')` 是域

`latticeFunctionField F ↥(ker f')` 要成为域，需要 `↥(ker f')` 上的 `UniqueProds`
（`Statement.lean` 为 `↥(ker φ)` 专门写了一条 `uniqueSums_kerPhi`，本区为子模补齐）。
沿子模包含 `ker f' ⊆ M_2'` 单射运输 `UniqueProds` 即可。
-/

/-- 子模包含在 `Multiplicative` 层是单射。 -/
lemma kerInclMonoidHom_injective : Function.Injective kerInclMonoidHom := by
  intro a b h
  apply Multiplicative.toAdd.injective
  exact Subtype.val_injective (Multiplicative.ofAdd.injective h)

/-- 子模包含作为 `MulHom`。 -/
def kerInclMulHom : Multiplicative ↥(LinearMap.ker fPrime) →ₙ* Multiplicative Mprime where
  toFun := kerInclMonoidHom
  map_mul' := kerInclMonoidHom.map_mul

/-- 沿子模包含运输 `UniqueProds`（使 `F(ker f')` 成为域）。 -/
instance uniqueProdsKerFPrime : UniqueProds (Multiplicative ↥(LinearMap.ker fPrime)) :=
  UniqueProds.of_injective_mulHom kerInclMulHom
    (fun a b h => kerInclMonoidHom_injective h) inferInstance
#print axioms kerInclMonoidHom_injective
#print axioms kerInclMulHom
#print axioms uniqueProdsKerFPrime


/-! ## §20 **格桥第三层**：域嵌入 `F(ker f') ↪ K`

`IsFractionRing.lift` 要求**目标域是域**，故须先把 `latticeAlgebraIncl` 复合到 `K`
（`latticeAlgebra F M_2' → K`），再沿分式域提升。**像**（下轮刻画）应恰是 `K^T`
（零权之商），即 §5k 的 `fixed_iff_weight_zero_ratio` 的"域版"。
-/

/-- `F[ker f'] ↪ F[M_2']` 的单射性。 -/
lemma latticeAlgebraIncl_injective (F : Type) [Field F] :
    Function.Injective (latticeAlgebraIncl F) :=
  MonoidAlgebra.mapDomain_injective kerInclMonoidHom_injective

/-- 复合到 `K` 的环同态（`IsFractionRing.lift` 要求目标域是域）。 -/
noncomputable def latticeAlgebraInclToK (F : Type) [Field F] :
    EM.latticeAlgebra F ↥(LinearMap.ker fPrime) →+* EM.latticeFunctionField F Mprime :=
  (algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)).comp
    (latticeAlgebraIncl F)

lemma latticeAlgebraInclToK_injective (F : Type) [Field F] :
    Function.Injective (latticeAlgebraInclToK F) := by
  intro a b h
  exact latticeAlgebraIncl_injective F
    (FaithfulSMul.algebraMap_injective (EM.latticeAlgebra F Mprime)
      (EM.latticeFunctionField F Mprime) h)

/-- ★ **格桥第三层**：域嵌入 `F(ker f') ↪ K`。 -/
noncomputable def latticeFunctionFieldKerToK (F : Type) [Field F] :
    EM.latticeFunctionField F ↥(LinearMap.ker fPrime) →+* EM.latticeFunctionField F Mprime :=
  IsFractionRing.lift (latticeAlgebraInclToK_injective F)

/-- 计算律：在 `F[ker f']` 的像上与 `latticeAlgebraIncl` 一致。 -/
lemma latticeFunctionFieldKerToK_algebraMap (F : Type) [Field F]
    (x : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    latticeFunctionFieldKerToK F (algebraMap _ _ x)
      = algebraMap _ _ (latticeAlgebraIncl F x) := by
  rw [latticeFunctionFieldKerToK,
    IsFractionRing.lift_algebraMap (latticeAlgebraInclToK_injective F) x]
  rfl
#print axioms latticeAlgebraIncl_injective
#print axioms latticeAlgebraInclToK
#print axioms latticeAlgebraInclToK_injective
#print axioms latticeFunctionFieldKerToK
#print axioms latticeFunctionFieldKerToK_algebraMap


/-! ## §21 格桥第三层：**代数层反向包含**（零权元素都来自 `F[ker f']`）

`(⊇)` 方向的代数内核：每个支撑落在 `ker f'` 上的元素都是 `latticeAlgebraIncl` 的像。
两件：
* `sum_single_coeff`（把元素按支集写成单项式之和）；
* `latticeAlgebraIncl_surj_weight_zero`（对支集作 `Finset` 归纳构造原像）。
-/

/-- 按支集把元素写成单项式之和。 -/
lemma sum_single_coeff (F : Type) [Field F] (x : EM.latticeAlgebra F Mprime) :
    ∑ m ∈ (MonoidAlgebra.coeff x).support,
      MonoidAlgebra.single m (MonoidAlgebra.coeff x m) = x := by
  apply MonoidAlgebra.coeff_injective
  ext n
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (M := F) n]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro b _ hb
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro h
    have h0 : MonoidAlgebra.coeff x n = 0 := by
      by_contra hne
      exact h (Finsupp.mem_support_iff.mpr hne)
    rw [h0, MonoidAlgebra.coeff_single, Finsupp.single_eq_same]


/-- 辅助：`s` 上（全零权）的单项式之和都有原像。 -/
lemma latticeAlgebraIncl_surj_aux (F : Type) [Field F] (s : Finset (Multiplicative Mprime))
    (hs : ∀ m ∈ s, fPrime (Multiplicative.toAdd m) = 0) (c : Multiplicative Mprime → F) :
    ∃ y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime),
      latticeAlgebraIncl F y = ∑ m ∈ s, MonoidAlgebra.single m (c m) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨y, hy⟩ := ih (fun m hm => hs m (Finset.mem_insert_of_mem hm))
    refine ⟨MonoidAlgebra.single ⟨a, hs a (Finset.mem_insert_self _ _)⟩ (c a) + y, ?_⟩
    rw [map_add, Finset.sum_insert ha, hy]
    congr 1
    rw [show latticeAlgebraIncl F (MonoidAlgebra.single ⟨a, hs a (Finset.mem_insert_self _ _)⟩ (c a))
        = MonoidAlgebra.single (kerInclMonoidHom ⟨a, hs a (Finset.mem_insert_self _ _)⟩) (c a)
        from latticeAlgebraIncl_single F _ _]
    rfl

/-- ★★ **代数层反向包含**：每个零权元素都来自 `F[ker f']`。 -/
lemma latticeAlgebraIncl_surj_weight_zero (F : Type) [Field F]
    (x : EM.latticeAlgebra F Mprime)
    (hx : ∀ m ∈ (MonoidAlgebra.coeff x).support, fPrime (Multiplicative.toAdd m) = 0) :
    ∃ y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime), latticeAlgebraIncl F y = x := by
  obtain ⟨y, hy⟩ := latticeAlgebraIncl_surj_aux F (MonoidAlgebra.coeff x).support hx
    (MonoidAlgebra.coeff x)
  exact ⟨y, by rw [hy, sum_single_coeff F x]⟩
#print axioms sum_single_coeff
#print axioms latticeAlgebraIncl_surj_aux
#print axioms latticeAlgebraIncl_surj_weight_zero


/-! ## §22 **格桥收口**：`F(ker f') ↪ K` 的像恰是 `K^T`

`(⟸)`：`K^T` 的元素是零权之商（§5k），分子分母都是 `latticeAlgebraIncl` 的像（§21），
故整个商在域嵌入的像里；`(⊆)`：像里的元素是零权元素之商，故 `T`-固定（§2d）。
**这就是「`K^T = F(M_2)`」的域同构形式**——与 §17 的 `F(ker f') ≅ F(Lat)` 合起来，
即把 (C) 层的机检成果接到 H2 陈述层用的 `Lat` 模型上。
-/

/-- ★★★ **格桥收口**：`F(ker f') ↪ K` 的**像恰是 `K^T`**。 -/
theorem latticeFunctionFieldKerToK_range (F : Type) [Field F] [CharZero F]
    (α : EM.latticeFunctionField F Mprime) :
    (∃ β : EM.latticeFunctionField F ↥(LinearMap.ker fPrime),
        latticeFunctionFieldKerToK F β = α) ↔ TFixed F α := by
  constructor
  · rintro ⟨β, rfl⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective
      (EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) β
    rw [map_div₀, latticeFunctionFieldKerToK_algebraMap,
      latticeFunctionFieldKerToK_algebraMap]
    intro t
    exact fraction_fixed_of_weight_zero F _ _
      (fun h => nonZeroDivisors.ne_zero hb (latticeAlgebraIncl_injective F (by rw [h, map_zero])))
      (latticeAlgebraIncl_weight_zero F a) (latticeAlgebraIncl_weight_zero F b) t
  · intro hT
    obtain ⟨f, g, hf, hg, hg0, rfl⟩ := (fixed_iff_weight_zero_ratio F α).mp hT
    obtain ⟨f', hf'⟩ := latticeAlgebraIncl_surj_weight_zero F f hf
    obtain ⟨g', hg'⟩ := latticeAlgebraIncl_surj_weight_zero F g hg
    refine ⟨algebraMap _ _ f' / algebraMap _ _ g', ?_⟩
    rw [map_div₀, latticeFunctionFieldKerToK_algebraMap,
      latticeFunctionFieldKerToK_algebraMap, hf', hg']
#print axioms latticeFunctionFieldKerToK_range


/-! ## §23 最后一步（半）：`actM σ` 保持 `ker f'`

零权条件是 `S_n`-不变的（§5j 的 `fPrime_actM` ＋ `σ 0 = 0`），故 `actM σ` 在子模 `ker f'` 上
给出一个作用——这是把 `SFixed`（`permScale`，`ker f'` 侧）与 `Lat` 侧 `S9` 作用对齐的**前提**。
-/

/-- `actM σ` 保持 `ker f'`（故在子模上有作用）。 -/
noncomputable def actMKer (σ : G.Gp 3) (m : ↥(LinearMap.ker fPrime)) :
    ↥(LinearMap.ker fPrime) :=
  ⟨actM σ m, by
    rw [LinearMap.mem_ker, fPrime_actM, m.2, map_zero]⟩

@[simp] lemma actMKer_coe (σ : G.Gp 3) (m : ↥(LinearMap.ker fPrime)) :
    (actMKer σ m : Mprime) = actM σ m := rfl
#print axioms actMKer
#print axioms actMKer_coe


/-! ## §24 **运输完成**：`kerFPrimeEquiv` 把 `actM` 送到 `Lat` 的 `S_9` 作用

`kerFPrimeEquiv (actMKer σ m) = σ • kerFPrimeEquiv m`——第一分量用 §5i 的桥
（`permB σ = TensorProduct.map (ρ σ) (ρ σ)`，恰是库内 `ker φ` 的作用），第二分量 `rfl`。
**⟹ 两个模型上的 `S_n` 作用已对齐**：`SFixed`（`ker f'` 侧，`permScale`）与 `Lat` 侧
`S9`（`instDistribMulActionMp2`）在 `kerFPrimeEquiv` 下一致。
-/

/-- ★★★ **运输**：`kerFPrimeEquiv` 把 `actM σ` 送到 `Lat` 的 `S_9` 作用。 -/
lemma kerFPrimeEquiv_actMKer (σ : G.Gp 3) (m : ↥(LinearMap.ker fPrime)) :
    kerFPrimeEquiv (actMKer σ m) = σ • (kerFPrimeEquiv m) := by
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    show permB σ ((m : Mprime)).1 = _
    rw [permB_eq_map]
    rfl
  · rfl
#print axioms kerFPrimeEquiv_actMKer


/-! ## §25 通到 H2 陈述层的**成员刻画**

`invariantsField F = EM.latticeInvariantsAlg F S9 Lat` 的成员条件按定义就是 `S_9`-固定
（`FixedPoints.subalgebra`）；本区把它写成一条可消费的 `↔`，并把到 `K` 的对应关系登记如下。

**已机检的三段拼图**（合起来即 `K^N ↔ ↥(invariantsField F)` 的内容）：
1. `latticeFunctionFieldKerEquiv : F(ker f') ≃+* F(Lat)`（§17）；
2. `latticeFunctionFieldKerToK_range`：`KerToK` 的像 ＝ `K^T`（§22）；
3. `kerFPrimeEquiv_actMKer`：两个模型上的 `S_n`／`S_9` 作用一致（§24）。
**剩余唯一机械件**：把「`permScale`-固定」与「`•`-固定」沿 1、3 对齐成一条等式
（即 `KerToK` 与 `S_n` 作用的交换方块）；它需要的单项式公式
`g • single m c = single (g • m) c` 在 mathlib 里现成。
-/

/-- `invariantsField F` 的成员刻画：`S_9`-固定。 -/
theorem mem_invariantsField_iff (F : Type) [Field F]
    (β : EM.latticeFunctionField F (ProcLat.Mp2 3)) :
    β ∈ EM.latticeInvariantsAlg F (G.Gp 3) (ProcLat.Mp2 3) ↔ ∀ σ : G.Gp 3, σ • β = β :=
  Iff.rfl
#print axioms mem_invariantsField_iff


/-! ## §26 **交换方块**：`S_n` 在 `F[ker f']` 上的作用

`permScale` 保持零权元素（§5j），故可沿包含 `F[ker f'] ↪ F[M_2']` **共轭**定义 `kerScale`；
方块 `incl (kerScale σ y) = permScale σ (incl y)` 按定义成立（`choose_spec`）。
由包含的单射性，`kerScale σ` 的**四条环律**随之而来——故它是环同态。
这是把「`permScale`-固定」与 `Lat` 侧 `•`-固定对齐的**代数层**一步。
-/

/-- `F[ker f']` 上的 `S_n` 作用（经包含沿 `permScale` 的共轭）。 -/
noncomputable def kerScale (F : Type) [Field F] (σ : G.Gp 3)
    (y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    EM.latticeAlgebra F ↥(LinearMap.ker fPrime) :=
  Classical.choose (latticeAlgebraIncl_surj_weight_zero F
    (permScale F σ (latticeAlgebraIncl F y))
    (permScale_weight_zero F σ _ (latticeAlgebraIncl_weight_zero F y)))

/-- ★ **交换方块（代数层）**：`kerScale` 在包含下就是 `permScale`。 -/
theorem latticeAlgebraIncl_kerScale (F : Type) [Field F] (σ : G.Gp 3)
    (y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    latticeAlgebraIncl F (kerScale F σ y) = permScale F σ (latticeAlgebraIncl F y) :=
  Classical.choose_spec (latticeAlgebraIncl_surj_weight_zero F
    (permScale F σ (latticeAlgebraIncl F y))
    (permScale_weight_zero F σ _ (latticeAlgebraIncl_weight_zero F y)))


lemma kerScale_zero (F : Type) [Field F] (σ : G.Gp 3) : kerScale F σ 0 = 0 := by
  apply latticeAlgebraIncl_injective F
  rw [latticeAlgebraIncl_kerScale, map_zero, permScale_zero]

lemma kerScale_one (F : Type) [Field F] (σ : G.Gp 3) : kerScale F σ 1 = 1 := by
  apply latticeAlgebraIncl_injective F
  rw [latticeAlgebraIncl_kerScale, map_one, permScale_one]

lemma kerScale_add (F : Type) [Field F] (σ : G.Gp 3)
    (y z : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    kerScale F σ (y + z) = kerScale F σ y + kerScale F σ z := by
  apply latticeAlgebraIncl_injective F
  rw [latticeAlgebraIncl_kerScale, map_add, permScale_add, map_add,
    latticeAlgebraIncl_kerScale, latticeAlgebraIncl_kerScale]

lemma kerScale_mul (F : Type) [Field F] (σ : G.Gp 3)
    (y z : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    kerScale F σ (y * z) = kerScale F σ y * kerScale F σ z := by
  apply latticeAlgebraIncl_injective F
  rw [latticeAlgebraIncl_kerScale, map_mul, permScale_mul, map_mul,
    latticeAlgebraIncl_kerScale, latticeAlgebraIncl_kerScale]
#print axioms kerScale
#print axioms latticeAlgebraIncl_kerScale
#print axioms kerScale_zero
#print axioms kerScale_one
#print axioms kerScale_add
#print axioms kerScale_mul


/-! ## §27 **交换方块（分式域层）**

`kerScale` 是环同态（§26），逆为 `kerScale σ⁻¹`（由方块 ＋ `permScale_comp`）⟹ 环等价
`kerScaleEquiv` ⟹ 沿分式域提升为 `kerScaleFieldEquiv` ⟹ 方块
`KerToK (kerScaleFieldEquiv σ β) = permScaleFieldEquiv σ (KerToK β)`
（`div_surjective` ＋ `map_div₀` ＋ 各计算律 ＋ `latticeAlgebraIncl_kerScale`）。
-/

/-- `kerScale σ⁻¹ ∘ kerScale σ = id`（由方块与 `permScale_comp`）。 -/
lemma kerScale_comp (F : Type) [Field F] (σ : G.Gp 3)
    (y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    kerScale F σ⁻¹ (kerScale F σ y) = y := by
  apply latticeAlgebraIncl_injective F
  rw [latticeAlgebraIncl_kerScale, latticeAlgebraIncl_kerScale, permScale_comp]

/-- `S_n` 在 `F[ker f']` 上的环等价。 -/
noncomputable def kerScaleEquiv (F : Type) [Field F] (σ : G.Gp 3) :
    EM.latticeAlgebra F ↥(LinearMap.ker fPrime) ≃+* EM.latticeAlgebra F ↥(LinearMap.ker fPrime) where
  toFun := kerScale F σ
  invFun := kerScale F σ⁻¹
  left_inv := kerScale_comp F σ
  right_inv y := by
    have h := kerScale_comp F σ⁻¹ y
    rw [inv_inv] at h
    exact h
  map_add' := kerScale_add F σ
  map_mul' := kerScale_mul F σ


/-- `S_n` 在 `F(ker f')` 上的环等价。 -/
noncomputable def kerScaleFieldEquiv (F : Type) [Field F] (σ : G.Gp 3) :
    EM.latticeFunctionField F ↥(LinearMap.ker fPrime) ≃+*
      EM.latticeFunctionField F ↥(LinearMap.ker fPrime) :=
  IsFractionRing.ringEquivOfRingEquiv (kerScaleEquiv F σ)

lemma kerScaleFieldEquiv_algebraMap (F : Type) [Field F] (σ : G.Gp 3)
    (y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    kerScaleFieldEquiv F σ (algebraMap _ _ y) = algebraMap _ _ (kerScale F σ y) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (kerScaleEquiv F σ) y

/-- ★★ **交换方块（分式域层）**：`KerToK` 与 `S_n` 作用交换。 -/
theorem latticeFunctionFieldKerToK_kerScaleFieldEquiv (F : Type) [Field F] (σ : G.Gp 3)
    (β : EM.latticeFunctionField F ↥(LinearMap.ker fPrime)) :
    latticeFunctionFieldKerToK F (kerScaleFieldEquiv F σ β)
      = permScaleFieldEquiv F σ (latticeFunctionFieldKerToK F β) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective
    (EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) β
  simp only [map_div₀, kerScaleFieldEquiv_algebraMap, latticeFunctionFieldKerToK_algebraMap,
    permScaleFieldEquiv_algebraMap, latticeAlgebraIncl_kerScale]
#print axioms kerScale_comp
#print axioms kerScaleEquiv
#print axioms kerScaleFieldEquiv
#print axioms kerScaleFieldEquiv_algebraMap
#print axioms latticeFunctionFieldKerToK_kerScaleFieldEquiv


/-! ## §28 `permScale` ＝ 库内构造（`mapDomainRingEquiv`）

库内 `S_9` 在 `F[Lat]` 上的作用是 `MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G Lat g)`
（见 `ABGV52/D3`）。本区把本工作区的 `permScale` 也写成**同一构造**：
`actMMulEquiv σ`（`actM σ` 的 `MulEquiv` 形态）＋ `mapDomainRingEquiv`。
**⟹ 两个作用自此可以逐点比较**（只需比较指数上的 `MulEquiv`）。
-/

/-- `actM σ` 的 `MulEquiv` 形态。 -/
noncomputable def actMMulEquiv (σ : G.Gp 3) : Multiplicative Mprime ≃* Multiplicative Mprime where
  toFun m := Multiplicative.ofAdd (actM σ (Multiplicative.toAdd m))
  invFun m := Multiplicative.ofAdd (actM σ⁻¹ (Multiplicative.toAdd m))
  left_inv m := by
    apply Multiplicative.toAdd.injective
    exact actM_inv_comp σ (Multiplicative.toAdd m)
  right_inv m := by
    apply Multiplicative.toAdd.injective
    show actM σ (actM σ⁻¹ (Multiplicative.toAdd m)) = Multiplicative.toAdd m
    rw [← actM_mul, mul_inv_cancel, actM_one]
  map_mul' m n := by
    apply Multiplicative.toAdd.injective
    show actM σ (Multiplicative.toAdd m + Multiplicative.toAdd n) = _
    rw [actM_add]
    rfl

/-- ★ **`permScale` 就是单项式搬运的 `mapDomainRingEquiv`**。 -/
lemma permScale_eq_mapDomainRingEquiv (F : Type) [Field F] (σ : G.Gp 3) :
    permScale F σ = MonoidAlgebra.mapDomainRingEquiv F (actMMulEquiv σ) := by
  funext x
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [permScale_zero, map_zero]
  | add x y ih1 ih2 => rw [permScale_add, map_add, ih1, ih2]
  | single m c =>
    show permScale F σ (MonoidAlgebra.single m c)
      = (MonoidAlgebra.mapDomainRingEquiv F (actMMulEquiv σ)) (MonoidAlgebra.single m c)
    rw [permScale_single, MonoidAlgebra.mapDomainRingEquiv_single]
    rfl
#print axioms actMMulEquiv
#print axioms permScale_eq_mapDomainRingEquiv


/-! ## §29 `kerScale` 在单项式上的公式

`kerScale σ (single m c) = single (actMKer σ m) c` —— 由包含的单射性从 §26 的方块推出，
再与 §28 的 `permScale = mapDomainRingEquiv (actMMulEquiv)` 合起来，即知 `kerScale` 也是
`mapDomainRingEquiv` 构造（与库内 `S_9` 作用**同源**）。
-/

/-- ★ **`kerScale` 在单项式上的公式**：`single m c ↦ single (actMKer σ m) c`。 -/
lemma kerScale_single (F : Type) [Field F] (σ : G.Gp 3)
    (m : Multiplicative ↥(LinearMap.ker fPrime)) (c : F) :
    kerScale F σ (MonoidAlgebra.single m c) = MonoidAlgebra.single (actMKer σ m) c := by
  apply latticeAlgebraIncl_injective F
  rw [latticeAlgebraIncl_kerScale, latticeAlgebraIncl_single, permScale_single]
  exact (latticeAlgebraIncl_single F (actMKer σ m) c).symm
#print axioms kerScale_single


/-! ## §30 收口最后一件：`kerScale` 与库内 `S_9` 作用在单项式层一致

`kerFPrimeMulEquiv (kerScale σ (single m c))` 经 `mapDomainRingEquiv` 后等于库内 `σ •`。
所需：`import ABGV52.D1_ABGV52`（`EM.mulEquivOfSMul` 与 `mulEquivOfSMul_apply` 在其中），
以及 `toAdd ∘ kerFPrimeMulEquiv = kerFPrimeEquiv`（`rfl` 级）。
-/

lemma kerFPrimeMulEquiv_kerScale_single (F : Type) [Field F] (σ : G.Gp 3)
    (m : Multiplicative ↥(LinearMap.ker fPrime)) (c : F) :
    MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv (kerScale F σ (MonoidAlgebra.single m c))
      = σ • (MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv
          (MonoidAlgebra.single m c)) := by
  have hkey : kerFPrimeMulEquiv (actMKer σ m)
      = (ABGV52.EM.mulEquivOfSMul (G.Gp 3) (ProcLat.Mp2 3) σ) (kerFPrimeMulEquiv m) := by
    apply Multiplicative.toAdd.injective
    show kerFPrimeEquiv (actMKer σ m) = σ • kerFPrimeEquiv m
    exact kerFPrimeEquiv_actMKer σ m
  rw [show (σ • (MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv
        (MonoidAlgebra.single m c)) : EM.latticeAlgebra F (ProcLat.Mp2 3))
      = MonoidAlgebra.mapDomainRingEquiv F (ABGV52.EM.mulEquivOfSMul (G.Gp 3) (ProcLat.Mp2 3) σ)
          (MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv (MonoidAlgebra.single m c)) from rfl]
  rw [kerScale_single, MonoidAlgebra.mapDomainRingEquiv_single]
  exact (MonoidAlgebra.mapDomainRingEquiv_single _ _ _).trans (by rw [hkey])
    |>.trans (MonoidAlgebra.mapDomainRingEquiv_single _ _ _).symm
#print axioms kerFPrimeMulEquiv_kerScale_single


/-! ## §31 **D2 步骤 1**：单项式层一致性外推到整个代数

由 §30 的单项式情形 ＋ 两侧的加性（`kerScale_add`／库内作用的 `smul_add`）作
`MonoidAlgebra.induction_linear`，得
`mapDomainRingEquiv F kerFPrimeMulEquiv (kerScale σ y) = σ • (mapDomainRingEquiv F kerFPrimeMulEquiv y)`
对**所有** `y : F[ker f']`。
-/

/-- ★★ **D2 步骤 1**：`kerScale` 与库内 `S_9` 作用在**整个代数**上一致。 -/
lemma kerFPrimeMulEquiv_kerScale (F : Type) [Field F] (σ : G.Gp 3)
    (y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv (kerScale F σ y)
      = σ • (MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv y) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp only [kerScale_zero, map_zero, smul_zero]
  | add y₁ y₂ ih1 ih2 => rw [map_add, kerScale_add, map_add, smul_add, ih1, ih2]
  | single m c => exact kerFPrimeMulEquiv_kerScale_single F σ m c
#print axioms kerFPrimeMulEquiv_kerScale


/-! ## §32 **D2 步骤 2**：分式域层的一致性

库内 `S_9` 作用是环自同构（`MulSemiringAction.toRingEquiv`），故与 `algebraMap` 与除法都相容；
配合 §31 的代数层一致性，即得
`latticeFunctionFieldKerEquiv (kerScaleFieldEquiv σ β) = σ • (latticeFunctionFieldKerEquiv β)`。
-/

/-- 库内作用与 `algebraMap` 相容（元素层）。 -/
lemma smul_algebraMap_latticeField (F : Type) [Field F] (σ : G.Gp 3)
    (z : EM.latticeAlgebra F (ProcLat.Mp2 3)) :
    σ • (algebraMap _ _ z : EM.latticeFunctionField F (ProcLat.Mp2 3))
      = algebraMap _ _ (σ • z) := by
  rw [show (σ • (algebraMap (EM.latticeAlgebra F (ProcLat.Mp2 3))
        (EM.latticeFunctionField F (ProcLat.Mp2 3)) z)
      : EM.latticeFunctionField F (ProcLat.Mp2 3))
      = (IsFractionRing.ringEquivOfRingEquiv
          (MulSemiringAction.toRingEquiv (G.Gp 3) (EM.latticeAlgebra F (ProcLat.Mp2 3)) σ))
          (algebraMap _ _ z) from rfl]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl


/-- `latticeFunctionFieldKerEquiv` 在 `algebraMap` 上的计算律。 -/
lemma latticeFunctionFieldKerEquiv_algebraMap (F : Type) [Field F]
    (y : EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) :
    latticeFunctionFieldKerEquiv F (algebraMap _ _ y)
      = algebraMap _ _ (MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv y) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (latticeAlgebraKerEquiv F) y

/-- 库内作用是环自同构，故与除法相容。 -/
lemma smul_div_latticeField (F : Type) [Field F] (σ : G.Gp 3)
    (a b : EM.latticeFunctionField F (ProcLat.Mp2 3)) :
    σ • (a / b) = σ • a / σ • b := by
  show (MulSemiringAction.toRingEquiv (G.Gp 3) (EM.latticeFunctionField F (ProcLat.Mp2 3)) σ) (a / b)
    = (MulSemiringAction.toRingEquiv (G.Gp 3) (EM.latticeFunctionField F (ProcLat.Mp2 3)) σ) a
      / (MulSemiringAction.toRingEquiv (G.Gp 3) (EM.latticeFunctionField F (ProcLat.Mp2 3)) σ) b
  rw [map_div₀]

/-- ★★ **D2 步骤 2**：`kerScaleFieldEquiv` 与库内 `S_9` 作用在**分式域**上一致。 -/
theorem latticeFunctionFieldKerEquiv_kerScaleFieldEquiv (F : Type) [Field F] (σ : G.Gp 3)
    (β : EM.latticeFunctionField F ↥(LinearMap.ker fPrime)) :
    latticeFunctionFieldKerEquiv F (kerScaleFieldEquiv F σ β)
      = σ • (latticeFunctionFieldKerEquiv F β) := by
  obtain ⟨y, z, hz, rfl⟩ := IsFractionRing.div_surjective
    (EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) β
  simp only [map_div₀, smul_div_latticeField, kerScaleFieldEquiv_algebraMap,
    latticeFunctionFieldKerEquiv_algebraMap, smul_algebraMap_latticeField,
    kerFPrimeMulEquiv_kerScale]
#print axioms smul_algebraMap_latticeField
#print axioms smul_div_latticeField
#print axioms latticeFunctionFieldKerEquiv_algebraMap
#print axioms latticeFunctionFieldKerEquiv_kerScaleFieldEquiv


/-! ## §33 `latticeFunctionFieldKerToK` 的单射性

走**核平凡**路线（比交叉相乘便宜得多）：`KerToK β = 0` ⟹ 写成 `β = ι a / ι b` ⟹
`ι(incl a) = 0` ⟹ `incl a = 0` ⟹ `a = 0` ⟹ `β = 0`；再由 `KerToK (x − y) = 0` 得单射。
（交叉相乘路线在本 pin 上**触发 heartbeat 超时**，已弃。）
-/

/-- `KerToK` 的核平凡。 -/
lemma latticeFunctionFieldKerToK_eq_zero (F : Type) [Field F]
    {β : EM.latticeFunctionField F ↥(LinearMap.ker fPrime)}
    (h : latticeFunctionFieldKerToK F β = 0) : β = 0 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective
    (EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) β
  simp only [map_div₀, latticeFunctionFieldKerToK_algebraMap] at h
  have hb0 : algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
      (latticeAlgebraIncl F b) ≠ 0 := by
    intro h0
    have h1 : latticeAlgebraIncl F b = 0 :=
      FaithfulSMul.algebraMap_injective _ _ (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero hb (latticeAlgebraIncl_injective F (by rw [h1, map_zero]))
  have ha0 : algebraMap (EM.latticeAlgebra F Mprime) (EM.latticeFunctionField F Mprime)
      (latticeAlgebraIncl F a) = 0 := by
    rcases div_eq_zero_iff.mp h with h' | h'
    · exact h'
    · exact absurd h' hb0
  have ha : latticeAlgebraIncl F a = 0 :=
    FaithfulSMul.algebraMap_injective _ _ (by rw [ha0, map_zero])
  have : a = 0 := latticeAlgebraIncl_injective F (by rw [ha, map_zero])
  rw [this, map_zero, zero_div]

/-- ★ **`latticeFunctionFieldKerToK` 单射**（核平凡 ⟹ 单射）。 -/
lemma latticeFunctionFieldKerToK_injective (F : Type) [Field F] :
    Function.Injective (latticeFunctionFieldKerToK F) := by
  intro x y h
  have hsub : latticeFunctionFieldKerToK F (x - y) = 0 := by rw [map_sub, h, sub_self]
  have := latticeFunctionFieldKerToK_eq_zero F hsub
  exact sub_eq_zero.mp this
#print axioms latticeFunctionFieldKerToK_eq_zero
#print axioms latticeFunctionFieldKerToK_injective


/-! ## §34 **D2 收口**：`K^N` 与 `↥(invariantsField F)` 内容一致

拼装四条既有件：
* §22 的 `latticeFunctionFieldKerToK_range`（像 ＝ `K^T`）；
* §32 的 `latticeFunctionFieldKerToK_kerScaleFieldEquiv`（`KerToK` 与 `S_n` 作用交换）；
* §32 的 `latticeFunctionFieldKerEquiv_kerScaleFieldEquiv`（`KerEquiv` 与库内 `S_9` 作用交换）；
* §25 的 `mem_invariantsField_iff`（`invariantsField` 成员 ⟺ `S_9`-固定）；
* §33 的 `latticeFunctionFieldKerToK_injective`（把 `KerToK` 的等式降回 `β` 的等式）。

**⟹ 这就是把 Saltman `thm:14.17` 的 (C) 层接到 H2 陈述层的最后一步。**
-/

/-- ★★★ **D2 收口**：`K^N` 与 `invariantsField F` 的内容一致。 -/
theorem N_fixed_iff_invariantsField (F : Type) [Field F] [CharZero F]
    (α : EM.latticeFunctionField F Mprime) :
    (TFixed F α ∧ SFixed F α) ↔
      ∃ β : EM.latticeFunctionField F (ProcLat.Mp2 3),
        β ∈ EM.latticeInvariantsAlg F (G.Gp 3) (ProcLat.Mp2 3) ∧
        latticeFunctionFieldKerToK F ((latticeFunctionFieldKerEquiv F).symm β) = α := by
  constructor
  · rintro ⟨hT, hS⟩
    obtain ⟨β₀, hβ₀⟩ := (latticeFunctionFieldKerToK_range F α).mpr hT
    have hfix : ∀ σ : G.Gp 3, kerScaleFieldEquiv F σ β₀ = β₀ := by
      intro σ
      apply latticeFunctionFieldKerToK_injective F
      rw [latticeFunctionFieldKerToK_kerScaleFieldEquiv, hβ₀, hS σ]
    refine ⟨latticeFunctionFieldKerEquiv F β₀, ?_, ?_⟩
    · rw [mem_invariantsField_iff]
      intro σ
      rw [← latticeFunctionFieldKerEquiv_kerScaleFieldEquiv, hfix σ]
    · rw [RingEquiv.symm_apply_apply]
      exact hβ₀
  · rintro ⟨β, hβ, hα⟩
    have hfixed : ∀ σ : G.Gp 3, σ • β = β := (mem_invariantsField_iff F β).mp hβ
    refine ⟨(latticeFunctionFieldKerToK_range F α).mp ⟨(latticeFunctionFieldKerEquiv F).symm β, hα⟩, ?_⟩
    intro σ
    rw [← hα, ← latticeFunctionFieldKerToK_kerScaleFieldEquiv]
    congr 1
    apply (latticeFunctionFieldKerEquiv F).injective
    rw [latticeFunctionFieldKerEquiv_kerScaleFieldEquiv, RingEquiv.apply_symm_apply, hfixed σ]
#print axioms N_fixed_iff_invariantsField


/-! ## §35 **N1 步骤 A**：`K^N` 作为 `K` 的子域

H2 陈述层用 `↥(invariantsField F)`（一个 `Subalgebra` 的载体），而 D2 的收官件（§34）是
**元素层**的 `↔`。要升成 `≃ₐ[F]`，先给 `K^N = {α | TFixed α ∧ SFixed α}` 一个 **`Subfield`** 结构
（`↥` 上自动有 `Field` 与 `Algebra F`），再与 `↥(invariantsField F)` 造环等价。
`NFixedSubfield` 的六个封闭性全部由「环同态固定 0／1／加／乘／负／逆」直接给出。
-/

/-- `K^N`（`T`-固定 ∧ `S_n`-固定）作为 `K` 的子域。 -/
noncomputable def NFixedSubfield (F : Type) [Field F] [CharZero F] :
    Subfield (EM.latticeFunctionField F Mprime) where
  carrier := {α | TFixed F α ∧ SFixed F α}
  zero_mem' := by
    refine ⟨fun b => ?_, fun σ => ?_⟩ <;> rw [map_zero]
  one_mem' := by
    refine ⟨fun b => ?_, fun σ => ?_⟩ <;> rw [map_one]
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun t => by rw [map_add, ha1 t, hb1 t], fun σ => by rw [map_add, ha2 σ, hb2 σ]⟩
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨fun t => by rw [map_neg, ha1 t], fun σ => by rw [map_neg, ha2 σ]⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun t => by rw [map_mul, ha1 t, hb1 t], fun σ => by rw [map_mul, ha2 σ, hb2 σ]⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨fun t => by rw [map_inv₀, ha1 t], fun σ => by rw [map_inv₀, ha2 σ]⟩

lemma mem_NFixedSubfield (F : Type) [Field F] [CharZero F]
    {α : EM.latticeFunctionField F Mprime} :
    α ∈ NFixedSubfield F ↔ TFixed F α ∧ SFixed F α := Iff.rfl
#print axioms NFixedSubfield
#print axioms mem_NFixedSubfield

/-! ## §36 **N1 达成**：`K^N ≃ₐ[F] ↥(invariantsField F)`（类型层）

§34 的 `N_fixed_iff_invariantsField` 是**元素层**的 `↔`；H2 陈述层（`Statement.lean`）要的是
**类型层**的 `Z ≃ₐ[F] ↥(invariantsField F)`（一个对象）。从命题到对象是**构造**：
本节把 §34 的逐元素对应包装成保结构的子类型等价。

路线（与任务书 §2.1 一致）：
* **步骤 A** `NFixedAlg`：给 `K^N = {α | TFixed α ∧ SFixed α}` 一个 **`Subalgebra F K`**
  （`Subalgebra` 而非 `Subfield`——后者在本 pin 上没有 `Algebra F ↥·` 实例，而 `≃ₐ[F]`
  需要两侧都有 `Algebra F`）。其 `algebraMap_mem'` 由 §36 开头的两条
  `TFixed_algebraMap`／`SFixed_algebraMap` 给出；
* **步骤 B** `nFixedToInv`：`K^N →+* ↥(invariantsField F)`，由 §34 的存在性取（R13）；
* **步骤 C** `invToNFixed`：反方向的**具体**映射；
* **收口** `nFixedRingEquiv`（`≃+*`）→ `nFixedAlgEquiv`（`≃ₐ[F]`）。

**为何先修 `algebraMap` 相容性**：`Subalgebra` 的 `algebraMap` 是「纯量再嵌入」，
而 `K^N` 与 `↥(invariantsField F)` 住在**两个不同的域**里（`K = F(M_2')` 与 `F(Lat)`），
故必须知道格桥（`KerEquiv`、`KerToK`）**保持纯量**——那正是 §36 前四条。
-/

/-- 格桥（代数层）与 `algebraMap` 相容：`F[ker f'] ≅ F[Lat]` 保持纯量。 -/
lemma mapDomainRingEquiv_algebraMap_kerFPrime (F : Type) [Field F] (r : F) :
    MonoidAlgebra.mapDomainRingEquiv F kerFPrimeMulEquiv
      (algebraMap F (EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) r)
      = algebraMap F (EM.latticeAlgebra F (ProcLat.Mp2 3)) r := by
  rw [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.coe_algebraMap]
  simp [MonoidAlgebra.mapDomainRingEquiv_single]

/-- 格桥第二层与 `algebraMap` 相容：沿子模包含的 `F[ker f'] → F[M_2']` 保持纯量。 -/
lemma latticeAlgebraIncl_algebraMap (F : Type) [Field F] (r : F) :
    latticeAlgebraIncl F (algebraMap F (EM.latticeAlgebra F ↥(LinearMap.ker fPrime)) r)
      = algebraMap F (EM.latticeAlgebra F Mprime) r := by
  rw [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.coe_algebraMap]
  simp [latticeAlgebraIncl, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapDomain_single]

/-- 格桥（分式域层）在 `algebraMap` 上的计算律（纯量对应纯量）。 -/
lemma latticeFunctionFieldKerEquiv_algebraMap' (F : Type) [Field F] (r : F) :
    latticeFunctionFieldKerEquiv F
        (algebraMap F (EM.latticeFunctionField F ↥(LinearMap.ker fPrime)) r)
      = algebraMap F (EM.latticeFunctionField F (ProcLat.Mp2 3)) r := by
  rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F ↥(LinearMap.ker fPrime))
    (EM.latticeFunctionField F ↥(LinearMap.ker fPrime))]
  rw [latticeFunctionFieldKerEquiv_algebraMap, mapDomainRingEquiv_algebraMap_kerFPrime]
  rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F (ProcLat.Mp2 3))
    (EM.latticeFunctionField F (ProcLat.Mp2 3))]

/-- 格桥第三层的嵌入 `F(ker f') ↪ K` 在 `algebraMap` 上的计算律。 -/
lemma latticeFunctionFieldKerToK_algebraMap' (F : Type) [Field F] (r : F) :
    latticeFunctionFieldKerToK F
        (algebraMap F (EM.latticeFunctionField F ↥(LinearMap.ker fPrime)) r)
      = algebraMap F (EM.latticeFunctionField F Mprime) r := by
  rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F ↥(LinearMap.ker fPrime))
    (EM.latticeFunctionField F ↥(LinearMap.ker fPrime))]
  rw [latticeFunctionFieldKerToK_algebraMap, latticeAlgebraIncl_algebraMap]
  rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
    (EM.latticeFunctionField F Mprime)]

/-- 纯量被环面固定：`TFixed F (algebraMap F K r)`（`1` 的权为零）。 -/
lemma TFixed_algebraMap (F : Type) [Field F] (r : F) :
    TFixed F (algebraMap F (EM.latticeFunctionField F Mprime) r) := by
  intro b
  rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
    (EM.latticeFunctionField F Mprime)]
  rw [torusScaleFieldEquiv_algebraMap]
  congr 1
  simp [MonoidAlgebra.coe_algebraMap, torusScale_single, chi_one]

/-- 纯量被 `S_n` 作用固定：`SFixed F (algebraMap F K r)`（`actM σ 0 = 0`）。 -/
lemma SFixed_algebraMap (F : Type) [Field F] (r : F) :
    SFixed F (algebraMap F (EM.latticeFunctionField F Mprime) r) := by
  intro σ
  rw [IsScalarTower.algebraMap_apply F (EM.latticeAlgebra F Mprime)
    (EM.latticeFunctionField F Mprime)]
  rw [permScaleFieldEquiv_algebraMap]
  congr 1
  simp [MonoidAlgebra.coe_algebraMap, permScale_single, actM_zero]


/-! ## N1 step A': K^N as a subalgebra -/

/-- ★ **N1 步骤 A**：`K^N = {α | TFixed α ∧ SFixed α}` 作为 `K` 的 **`Subalgebra`**。

**为何用 `Subalgebra` 而不是 `Subfield`**：`subtype` 上的 `Algebra F` 实例由 `Subalgebra`
自动给出，而 mathlib 的 `Subfield` 在本 pin 上**没有** `Algebra F ↥·` 实例
（见 `ABGV52/D3_ABGV52.lean` 的说明）——`≃ₐ[F]` 需要两侧都有 `Algebra F`。 -/
noncomputable def NFixedAlg (F : Type) [Field F] [CharZero F] :
    Subalgebra F (EM.latticeFunctionField F Mprime) where
  carrier := {α | TFixed F α ∧ SFixed F α}
  zero_mem' := by
    refine ⟨fun b => ?_, fun σ => ?_⟩ <;> rw [map_zero]
  one_mem' := by
    refine ⟨fun b => ?_, fun σ => ?_⟩ <;> rw [map_one]
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun t => by rw [map_add, ha1 t, hb1 t], fun σ => by rw [map_add, ha2 σ, hb2 σ]⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun t => by rw [map_mul, ha1 t, hb1 t], fun σ => by rw [map_mul, ha2 σ, hb2 σ]⟩
  algebraMap_mem' r := ⟨TFixed_algebraMap F r, SFixed_algebraMap F r⟩

/-- `NFixedAlg` 的成员刻画（定义展开）。 -/
lemma mem_NFixedAlg (F : Type) [Field F] [CharZero F]
    {α : EM.latticeFunctionField F Mprime} :
    α ∈ NFixedAlg F ↔ TFixed F α ∧ SFixed F α := Iff.rfl

/-- 类型锁：`NFixedAlg` 的载体（一旦改动立即编译失败）。 -/
theorem NFixedAlg_typeLock (F : Type) [Field F] [CharZero F] :
    (NFixedAlg F : Set (EM.latticeFunctionField F Mprime))
      = {α | TFixed F α ∧ SFixed F α} := rfl

/-- 「不变量域 → `K`」的环同态：`β ↦ KerToK (KerEquiv.symm β)`。

即 §17 的格桥与 §20 的域嵌入的复合，把 `↥(invariantsField F)` 的元素送回 `K = F(M_2')`。
**用途**：`N_fixed_iff_invariantsField`（§34）说的正是 `K^N` 恰是这条映射的像。 -/
noncomputable def invFieldToK (F : Type) [Field F] :
    ↥(invariantsField F) →+* EM.latticeFunctionField F Mprime :=
  (latticeFunctionFieldKerToK F).comp
    ((latticeFunctionFieldKerEquiv F).symm.toRingHom.comp
      (Subalgebra.val (invariantsField F)).toRingHom)

/-- `invFieldToK` 的展开式（`rfl`）。 -/
lemma invFieldToK_apply (F : Type) [Field F] (β : ↥(invariantsField F)) :
    invFieldToK F β = latticeFunctionFieldKerToK F
      ((latticeFunctionFieldKerEquiv F).symm β.val) := rfl

/-- `invFieldToK` 单射：由 §20 的嵌入单射性与 `KerEquiv` 的可逆性。 -/
lemma invFieldToK_injective (F : Type) [Field F] :
    Function.Injective (invFieldToK F) := by
  intro x y h
  simp only [invFieldToK_apply] at h
  have h1 : (latticeFunctionFieldKerEquiv F).symm x.val
      = (latticeFunctionFieldKerEquiv F).symm y.val :=
    latticeFunctionFieldKerToK_injective F h
  have h2 := congrArg (latticeFunctionFieldKerEquiv F) h1
  simp only [RingEquiv.apply_symm_apply] at h2
  exact Subtype.ext h2

/-- **N1 步骤 B 的函数层**：`K^N → ↥(invariantsField F)`，由 §34 的存在性取（`choose`）。

**R13 范式**：从存在性定义映射，其**性质由 `choose_spec` 给**（下一条引理）；
环律随后**由单射性从该性质推出**（第 60 轮 `kerScale` 的同一手法）。 -/
noncomputable def nFixedToInvFun (F : Type) [Field F] [CharZero F]
    (α : ↥(NFixedAlg F)) : ↥(invariantsField F) :=
  ⟨Classical.choose ((N_fixed_iff_invariantsField F α.val).mp α.2),
    (Classical.choose_spec ((N_fixed_iff_invariantsField F α.val).mp α.2)).1⟩

/-- 上述映射的**定义性质**：`invFieldToK (nFixedToInvFun α) = α`。 -/
lemma nFixedToInvFun_spec (F : Type) [Field F] [CharZero F] (α : ↥(NFixedAlg F)) :
    invFieldToK F (nFixedToInvFun F α) = α.val :=
  (Classical.choose_spec ((N_fixed_iff_invariantsField F α.val).mp α.2)).2

/-- ★ **N1 步骤 B**：`K^N →+* ↥(invariantsField F)`（环同态）。

四条环律全部**降回 `K`** 用 `invFieldToK` 的单射性证明——两向都是
`invFieldToK (…) = …` 的形状，故 `map_add`／`map_mul` 直接可用。 -/
noncomputable def nFixedToInv (F : Type) [Field F] [CharZero F] :
    ↥(NFixedAlg F) →+* ↥(invariantsField F) where
  toFun := nFixedToInvFun F
  map_one' := by
    apply invFieldToK_injective F
    rw [map_one, nFixedToInvFun_spec]
    simp
  map_zero' := by
    apply invFieldToK_injective F
    rw [map_zero, nFixedToInvFun_spec]
    simp
  map_add' α β := by
    apply invFieldToK_injective F
    rw [map_add, nFixedToInvFun_spec, nFixedToInvFun_spec, nFixedToInvFun_spec]
    rfl
  map_mul' α β := by
    apply invFieldToK_injective F
    rw [map_mul, nFixedToInvFun_spec, nFixedToInvFun_spec, nFixedToInvFun_spec]
    rfl

/-- `nFixedToInv` 的定义性质（与函数层同一条）。 -/
lemma nFixedToInv_spec (F : Type) [Field F] [CharZero F] (α : ↥(NFixedAlg F)) :
    invFieldToK F (nFixedToInv F α) = α.val :=
  nFixedToInvFun_spec F α

/-- ★ **N1 步骤 C**：反方向环同态 `↥(invariantsField F) →+* K^N`。

成员性由 §34 的 `(⟸)` 方向直接给出（无可选取项——`β ↦ KerToK (KerEquiv.symm β)` 是具体的）。 -/
noncomputable def invToNFixed (F : Type) [Field F] [CharZero F] :
    ↥(invariantsField F) →+* ↥(NFixedAlg F) where
  toFun β := ⟨invFieldToK F β,
    ((N_fixed_iff_invariantsField F (invFieldToK F β)).mpr ⟨β.val, β.2, rfl⟩)⟩
  map_one' := by
    apply Subtype.ext
    simp [invFieldToK]
  map_zero' := by
    apply Subtype.ext
    simp [invFieldToK]
  map_add' β γ := by
    apply Subtype.ext
    simp
  map_mul' β γ := by
    apply Subtype.ext
    simp

/-- 右逆：`nFixedToInv ∘ invToNFixed = id`（用 `invFieldToK` 的单射性收口）。 -/
lemma nFixedToInv_invToNFixed (F : Type) [Field F] [CharZero F]
    (β : ↥(invariantsField F)) :
    nFixedToInv F (invToNFixed F β) = β := by
  apply invFieldToK_injective F
  rw [nFixedToInv_spec]
  rfl

/-- ★★ **N1 达成**：环等价 `K^N ≃+* ↥(invariantsField F)`。

由 `RingEquiv.ofBijective` 给出：单射性来自 `invFieldToK` 的单射性 + `nFixedToInv_spec`，
满射性以 `invToNFixed` 为原像（上一条的右逆）。 -/
noncomputable def nFixedRingEquiv (F : Type) [Field F] [CharZero F] :
    ↥(NFixedAlg F) ≃+* ↥(invariantsField F) :=
  RingEquiv.ofBijective (nFixedToInv F) ⟨fun a b h => by
      have hh := congrArg (invFieldToK F) h
      rw [nFixedToInv_spec, nFixedToInv_spec] at hh
      exact Subtype.ext hh,
    fun β => ⟨invToNFixed F β, nFixedToInv_invToNFixed F β⟩⟩

/-- 反方向环同态在 `algebraMap` 上的计算律：纯量对应纯量。

用 §36 开头的两条 `algebraMap` 相容性（`latticeFunctionFieldKerEquiv_algebraMap'`、
`latticeFunctionFieldKerToK_algebraMap'`）。 -/
lemma invToNFixed_algebraMap (F : Type) [Field F] [CharZero F] (r : F) :
    invToNFixed F (algebraMap F ↥(invariantsField F) r)
      = algebraMap F ↥(NFixedAlg F) r := by
  apply Subtype.ext
  show invFieldToK F (algebraMap F ↥(invariantsField F) r)
    = algebraMap F (EM.latticeFunctionField F Mprime) r
  rw [invFieldToK_apply]
  have hval : ((algebraMap F ↥(invariantsField F) r : ↥(invariantsField F))
      : EM.latticeFunctionField F (ProcLat.Mp2 3))
      = algebraMap F (EM.latticeFunctionField F (ProcLat.Mp2 3)) r := rfl
  rw [hval]
  have h1 : (latticeFunctionFieldKerEquiv F).symm
      (algebraMap F (EM.latticeFunctionField F (ProcLat.Mp2 3)) r)
      = algebraMap F (EM.latticeFunctionField F ↥(LinearMap.ker fPrime)) r := by
    rw [← latticeFunctionFieldKerEquiv_algebraMap' F r, RingEquiv.symm_apply_apply]
  rw [h1, latticeFunctionFieldKerToK_algebraMap']

/-- ★★★ **N1 收口（`≃ₐ[F]`）**：`K^N ≃ₐ[F] ↥(invariantsField F)`。

由上面的环等价经 `AlgEquiv.ofRingEquiv` 升格；`commutes'` 用
`invToNFixed_algebraMap`（把 `algebraMap` 认作 `invToNFixed` 的像）＋右逆收口。 -/
noncomputable def nFixedAlgEquiv (F : Type) [Field F] [CharZero F] :
    ↥(NFixedAlg F) ≃ₐ[F] ↥(invariantsField F) :=
  AlgEquiv.ofRingEquiv (f := nFixedRingEquiv F) (fun r => by
    show nFixedToInv F (algebraMap F ↥(NFixedAlg F) r)
      = algebraMap F ↥(invariantsField F) r
    rw [show algebraMap F ↥(NFixedAlg F) r
        = invToNFixed F (algebraMap F ↥(invariantsField F) r)
        from (invToNFixed_algebraMap F r).symm]
    exact nFixedToInv_invToNFixed F (algebraMap F ↥(invariantsField F) r))
#print axioms mapDomainRingEquiv_algebraMap_kerFPrime
#print axioms latticeAlgebraIncl_algebraMap
#print axioms latticeFunctionFieldKerEquiv_algebraMap'
#print axioms latticeFunctionFieldKerToK_algebraMap'
#print axioms TFixed_algebraMap
#print axioms SFixed_algebraMap
#print axioms NFixedAlg
#print axioms mem_NFixedAlg
#print axioms invFieldToK
#print axioms invFieldToK_apply
#print axioms invFieldToK_injective
#print axioms nFixedToInvFun
#print axioms nFixedToInvFun_spec
#print axioms nFixedToInv
#print axioms nFixedToInv_spec
#print axioms invToNFixed
#print axioms nFixedToInv_invToNFixed
#print axioms nFixedRingEquiv
#print axioms invToNFixed_algebraMap
#print axioms nFixedAlgEquiv

/-! ## §37 **N2 交付定理**：`(A)+(B)` 一条具名假设 ⟹ H2

`thm:14.17` 的 **(C) 层**已在 §17–§36 机检（含本轮的**类型层** `≃ₐ[F]`）。剩下
**(A)** `thm:14.16`（`K^{PGL_n} = Z`）与 **(B)** `prop:14.19`（`Z = K'^N`）是**研究级**
（PI 环／Azumaya，`lem:14.13`／`thm:14.15`／`lem:14.21–14.25`），本工作区**不构造** `Z`。
故把它们合成**一个**具名假设 `SaltmanCenterEqNFixed`（中心 ＝ `K^N`）。

**交付形态**：`H2 ＝ (C) 机检 ＋ 一条具名假设`。`procesiS9Hyp_iff_saltmanCenterEqNFixed`
说明在 (C) 已机检的前提下，H2 与那条假设**等价**——即该假设**恰是**剩余的全部内容。

**射程边界（勿夸大）**：`h2_of_saltmanCenterEqNFixed` 是**逻辑传递**，不是对 (A)(B) 的证明。
-/

/-- **(A)+(B) 的唯一具名假设**：中心 `Z` 就是 `K^N`（`T`-固定 ∧ `S_n`-固定 的子域）。

来源：Saltman 1999（`raw/Saltman1999ch14.tex`）`thm:14.16`（(A)）＋ `prop:14.19`（(B)）。
按任务书 §2.3 的裁决**合并**为一条具名假设（拆成小假设会掩盖难度）。
**引用方式**：按 label，不按 `pdf_number`（L41）。 -/
def SaltmanCenterEqNFixed (F : Type) [Field F] [CharZero F] (Z : Type) [Field Z]
    [Algebra F Z] : Prop :=
  Nonempty (Z ≃ₐ[F] ↥(NFixedAlg F))

/-- 类型锁：`SaltmanCenterEqNFixed` 的外形（一旦改动立即编译失败）。 -/
theorem saltmanCenterEqNFixed_typeLock (F : Type) [Field F] [CharZero F] (Z : Type)
    [Field Z] [Algebra F Z] :
    (SaltmanCenterEqNFixed F Z) = (Nonempty (Z ≃ₐ[F] ↥(NFixedAlg F))) := rfl

/-- ★★★ **交付定理（N2）**：`(A)+(B)` ⟹ H2。由 §36 的 `nFixedAlgEquiv` 传递即得。 -/
theorem h2_of_saltmanCenterEqNFixed (F : Type) [Field F] [CharZero F] (Z : Type)
    [Field Z] [Algebra F Z] (h : SaltmanCenterEqNFixed F Z) : ProcesiS9Hyp F Z := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (nFixedAlgEquiv F)⟩

/-- **逻辑地位**：在 (C) 已机检的前提下，H2 **等价于**那条唯一具名假设。 -/
theorem procesiS9Hyp_iff_saltmanCenterEqNFixed (F : Type) [Field F] [CharZero F]
    (Z : Type) [Field Z] [Algebra F Z] :
    ProcesiS9Hyp F Z ↔ SaltmanCenterEqNFixed F Z := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (nFixedAlgEquiv F).symm⟩
  · exact h2_of_saltmanCenterEqNFixed F Z

/-- **L1 非空洞见证**：具名假设**可满足**——取 `Z := ↥(invariantsField F)`，由 §36 的
`≃ₐ[F]` 反向给出。**读法**（L1＋L10①）：这只说明**假设类非空**，**不是**「H2 为真」；
后者要求 `Z` 取真正的中心 `Z_{S_9}(F,9)`（该域在 Lean 内**未构造**，构造它正是 (A)(B) 的内容）。 -/
theorem saltmanCenterEqNFixed_nonempty (F : Type) [Field F] [CharZero F] :
    SaltmanCenterEqNFixed F ↥(invariantsField F) :=
  ⟨(nFixedAlgEquiv F).symm⟩

#print axioms NFixedAlg_typeLock
#print axioms SaltmanCenterEqNFixed
#print axioms saltmanCenterEqNFixed_typeLock
#print axioms h2_of_saltmanCenterEqNFixed
#print axioms procesiS9Hyp_iff_saltmanCenterEqNFixed
#print axioms saltmanCenterEqNFixed_nonempty

/-! ## §3 公理闸门 -/

#print axioms fPrime_apply
#print axioms kerFPrimeEquiv
#print axioms rank_kerFPrime
#print axioms wt_zero
#print axioms wt_add
#print axioms wtM_add
#print axioms wtM_eq_one_of_mem_ker
#print axioms snActionU
#print axioms snActionU_smul
#print axioms permB
#print axioms permB_one
#print axioms permB_basis
#print axioms permOmega_mul
#print axioms permB_mul

end

end Procesi
