/-
  ABGV-5.2 —— C 档 · EM 判据 · **块 1 的子块 1α**（分裂环面 / 自由格）

  1α 的命题：`M = ℤ^n` **自由** ⟹ 格函数域 `F(M)` 是 `F` 上的**有理函数域**。

  证明路线（三条件，收口处用 `FractionRing.algEquiv`）：

    设 `R = F[X₁,…,X_n] = MvPolynomial (Fin n) F`，`A = F[ℤ^n]`，
    `K = F(ℤ^n) = FractionRing A`。

    * `freeSubst : R →ₐ[F] A`：把 `X_i` 送到 Laurnet 单项式 `x_i`（代入同态）。
      它与 `A → K` 复合成 `R → K`，本文件据此**登记一个 `Algebra R A` 实例**
      （`instAlgebraFree`），`R → K` 由上层的 `FractionRing` 机制自动派生。
    * `IsFractionRing R K`（`freeSubst_isFractionRing`）：用 `IsFractionRing.of_field`，
      只需 (a) `Algebra R K` 单射（即 `FaithfulSMul R K`，由 `freeSubst` 单射得），
      (b) **每个 `z ∈ K` 都是 `φ x / φ y`（`x, y ∈ R`）**。
      (b) 是全部工作量所在，见 `freeSubst_clear`：先取 `z = a/b`（`a, b ∈ A`），
      再**清分母**——把每个 Laurent 单项式写成 `X^{正部}/X^{负部}`，
      `a·x^N, b·x^N` 即落在 `R` 的像里（`N` 取够大；加法律用 `freeSubst_mono` 升级）。
    * 收口：`FractionRing R ≃ₐ[R] K` 限制标量到 `F`，取逆即 `K ≃ₐ[F] F(t₁,…,t_n)`。

  **域无特征假设**：结论对任意域 `F` 成立（自由格情形不需要单位根条件——
  后者只出现在 1β 的置换/Fischer 段）。

  与 D1 的关系：用到 D1 的 `latticeAlgebra` / `latticeFunctionField` / `IsRational`；
  命名空间同为 `ABGV52.EM`。
-/
import ABGV52.D1_ABGV52
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Localization.Away.Basic

open scoped Classical

namespace ABGV52

namespace EM

section Free

variable (F : Type*) [Field F]
variable (n : ℕ)

/-! ## 1. 指数向量：非负部分与嵌入 -/

/-- 常数向量 `(N,…,N) : Fin n → ℤ`。 -/
def constInt (N : ℕ) : Fin n → ℤ := fun _ => (N : ℤ)

/-- 整向量逐分量取绝对值，读成 `ℕ`-指数向量（清分母用的「正部」）。 -/
noncomputable def posPart (g : Fin n → ℤ) : Fin n →₀ ℕ :=
  Finset.univ.sum (fun i : Fin n => Finsupp.single i ((g i).natAbs))

lemma posPart_apply (g : Fin n → ℤ) (i : Fin n) : posPart n g i = (g i).natAbs := by
  rw [posPart, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact Finsupp.single_eq_same
  · intro j _ hj; exact Finsupp.single_eq_of_ne hj.symm
  · intro h; exact absurd (Finset.mem_univ i) h

/-- 指数嵌入 `Fin n →₀ ℕ ↪ Fin n → ℤ`（各分量取同值）。 -/
noncomputable def freeEmb : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun s := fun i => (s i : ℤ)
  map_zero' := by ext i; simp
  map_add' s t := by ext i; simp [Finsupp.add_apply, Nat.cast_add]

@[simp] lemma freeEmb_apply (s : Fin n →₀ ℕ) (i : Fin n) : freeEmb n s i = (s i : ℤ) := rfl

lemma freeEmb_injective : Function.Injective (freeEmb n) := by
  intro s t h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

/-- `posPart` 与 `freeEmb` 互逆（在非负锥上）。 -/
lemma freeEmb_posPart (g : Fin n → ℤ) (hg : ∀ i, 0 ≤ g i) :
    freeEmb n (posPart n g) = g := by
  ext i
  rw [freeEmb_apply, posPart_apply]
  exact Int.natAbs_of_nonneg (hg i)

/-! ## 2. 代入同态 `F[X₁,…,X_n] →ₐ[F] F[ℤ^n]` -/

/-- `X_i ↦ x_i`（Laurent 单项式），由 `MvPolynomial` 的自由性给出。 -/
noncomputable def freeSubst :
    MvPolynomial (Fin n) F →ₐ[F] latticeAlgebra F (Fin n → ℤ) :=
  (MonoidAlgebra.mapDomainAlgHom F F (freeEmb n).toMultiplicative).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (Fin n →₀ ℕ)).toAlgHom

lemma freeSubst_apply (p : MvPolynomial (Fin n) F) :
    freeSubst F n p = MonoidAlgebra.mapDomain (⇑(freeEmb n).toMultiplicative)
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (Fin n →₀ ℕ) p) := rfl

/-- 单项式的像：`monomial s c ↦ c · x^{s}`。 -/
theorem freeSubst_monomial (s : Fin n →₀ ℕ) (c : F) :
    freeSubst F n (MvPolynomial.monomial s c)
      = MonoidAlgebra.single (Multiplicative.ofAdd (freeEmb n s)) c := by
  rw [freeSubst_apply, (MvPolynomial.single_eq_monomial s c).symm,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.mapDomain_single,
    AddMonoidHom.toMultiplicative_apply_apply]
  simp

/-- `freeSubst` 单射（指数嵌入单射 ＋ `mapDomain` 保单射）。 -/
theorem freeSubst_injective : Function.Injective (freeSubst F n) := by
  have h1 : Function.Injective (fun p : MvPolynomial (Fin n) F =>
      MonoidAlgebra.mapDomain (⇑(freeEmb n).toMultiplicative)
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (Fin n →₀ ℕ) p)) :=
    (MonoidAlgebra.mapDomain_injective (R := F) (freeEmb_injective n)).comp
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (Fin n →₀ ℕ)).injective
  intro x y h
  exact h1 h

/-! ## 3. 清分母 -/

/-- `x^N = x_1^N ⋯ x_n^N`（清分母用的乘子，是 `A` 中单位）。 -/
noncomputable def freeUnit (N : ℕ) : latticeAlgebra F (Fin n → ℤ) :=
  MonoidAlgebra.single (Multiplicative.ofAdd (constInt n N)) 1

lemma freeUnit_isUnit (N : ℕ) : IsUnit (freeUnit F n N) := by
  rw [freeUnit, ← MonoidAlgebra.of_apply]
  exact (Group.isUnit (Multiplicative.ofAdd (constInt n N))).map
    (MonoidAlgebra.of F (Multiplicative (Fin n → ℤ)))

lemma freeSubst_monomial_const (k : ℕ) :
    freeSubst F n (MvPolynomial.monomial (posPart n (constInt n k)) 1)
      = freeUnit F n k := by
  rw [freeSubst_monomial, freeUnit,
    freeEmb_posPart n (constInt n k) (fun i => by simp [constInt])]

/-- **升级**：把 `a · x^{N₀} ∈ im freeSubst` 升成大乘子 `x^N`（`N₀ ≤ N`）。 -/
lemma freeSubst_clear_mono {a : latticeAlgebra F (Fin n → ℤ)} {N₀ : ℕ}
    {p : MvPolynomial (Fin n) F} (hp : freeSubst F n p = a * freeUnit F n N₀)
    {N : ℕ} (hN : N₀ ≤ N) :
    freeSubst F n (p * MvPolynomial.monomial (posPart n (constInt n (N - N₀))) 1)
      = a * freeUnit F n N := by
  have hv : constInt n N₀ + constInt n (N - N₀) = constInt n N := by
    ext i
    simp only [constInt, Pi.add_apply]
    rw [← Nat.cast_add, Nat.add_sub_cancel' hN]
  rw [map_mul, freeSubst_monomial_const, hp, mul_assoc, freeUnit, freeUnit,
    MonoidAlgebra.single_mul_single, ← ofAdd_add, hv, one_mul, freeUnit]

lemma freeSubst_mono {a : latticeAlgebra F (Fin n → ℤ)} {N₀ : ℕ}
    {p : MvPolynomial (Fin n) F} (hp : freeSubst F n p = a * freeUnit F n N₀)
    (N : ℕ) (hN : N₀ ≤ N) :
    ∃ p' : MvPolynomial (Fin n) F, freeSubst F n p' = a * freeUnit F n N :=
  ⟨p * MvPolynomial.monomial (posPart n (constInt n (N - N₀))) 1,
    freeSubst_clear_mono F n hp hN⟩

/-- **清分母（主引理）**：`A` 的每个元素乘以够大的 `x^N` 都落在 `R` 的像里。

  对 `a` 的系数作线性归纳（`MonoidAlgebra.induction_on`）：
  单项式 `c · x^m` 取 `N = ∑_i |m_i|`，则 `m + N·1 ≥ 0`，
  `monomial (posPart (m + N·1)) c` 即所求；和的情形两乘子取 `max`。 -/
theorem freeSubst_clear (a : latticeAlgebra F (Fin n → ℤ)) :
    ∃ (N : ℕ) (p : MvPolynomial (Fin n) F), freeSubst F n p = a * freeUnit F n N := by
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    set g : Fin n → ℤ := m.toAdd with hg
    set N : ℕ := ∑ i : Fin n, (g i).natAbs with hNdef
    have hN : ∀ i : Fin n, 0 ≤ g i + (N : ℤ) := by
      intro i
      have h1 : (g i).natAbs ≤ N :=
        Finset.single_le_sum (f := fun j : Fin n => (g j).natAbs) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have h2 : -(g i) ≤ ((g i).natAbs : ℤ) := by
        rw [← Int.natAbs_neg (g i)]
        exact Int.le_natAbs
      have h3 : ((g i).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
      linarith
    rw [MonoidAlgebra.of_apply]
    refine ⟨N, MvPolynomial.monomial (posPart n (g + constInt n N)) 1, ?_⟩
    have hm : Multiplicative.ofAdd g = m := by simp [hg]
    rw [freeSubst_monomial, freeEmb_posPart n _ (fun i => by simpa [constInt] using hN i),
      freeUnit, ← hm, MonoidAlgebra.single_mul_single, ← ofAdd_add]
    simp
  | add x y hx hy =>
    obtain ⟨N₁, p₁, hp₁⟩ := hx
    obtain ⟨N₂, p₂, hp₂⟩ := hy
    obtain ⟨p₁', hp₁'⟩ := freeSubst_mono F n hp₁ (max N₁ N₂) (le_max_left _ _)
    obtain ⟨p₂', hp₂'⟩ := freeSubst_mono F n hp₂ (max N₁ N₂) (le_max_right _ _)
    exact ⟨max N₁ N₂, p₁' + p₂', by rw [map_add, hp₁', hp₂', add_mul]⟩
  | smul r x hx =>
    obtain ⟨N, p, hp⟩ := hx
    exact ⟨N, MvPolynomial.C r * p,
      by rw [map_mul, MvPolynomial.C_eq_algebraMap, AlgHom.commutes, hp,
        smul_mul_assoc, Algebra.smul_def]⟩

/-! ## 4. `R`-代数结构与 `IsFractionRing` -/

/-- `F[X₁,…,X_n]` 经代入作用在 `F[ℤ^n]` 上（登记为实例，供 `FractionRing` 派生 `R → K`）。 -/
noncomputable instance instAlgebraFree :
    Algebra (MvPolynomial (Fin n) F) (latticeAlgebra F (Fin n → ℤ)) :=
  (freeSubst F n).toRingHom.toAlgebra

/-- `R → K` 经由 `A` 分解（标量塔）。 -/
lemma algebraMap_freeSubst (p : MvPolynomial (Fin n) F) :
    algebraMap (MvPolynomial (Fin n) F) (latticeFunctionField F (Fin n → ℤ)) p
      = algebraMap (latticeAlgebra F (Fin n → ℤ)) (latticeFunctionField F (Fin n → ℤ))
          (freeSubst F n p) :=
  IsScalarTower.algebraMap_apply _ _ _ p

/-- **主定理**：`F(ℤ^n)` 是 `F[X₁,…,X_n]` 的分式域。 -/
theorem freeSubst_isFractionRing :
    IsFractionRing (MvPolynomial (Fin n) F) (latticeFunctionField F (Fin n → ℤ)) := by
  have hfs : FaithfulSMul (MvPolynomial (Fin n) F)
      (latticeFunctionField F (Fin n → ℤ)) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h : freeSubst F n x = freeSubst F n y := by
      have h' := hxy
      simp only [algebraMap_freeSubst] at h'
      exact IsFractionRing.injective (latticeAlgebra F (Fin n → ℤ))
        (latticeFunctionField F (Fin n → ℤ)) h'
    exact freeSubst_injective F n h
  refine IsFractionRing.of_field _ _ ?_
  intro z
  obtain ⟨⟨a, b⟩, hb⟩ :=
    IsLocalization.surj (nonZeroDivisors (latticeAlgebra F (Fin n → ℤ))) z
  have hb0 : (b : latticeAlgebra F (Fin n → ℤ)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hS : algebraMap (latticeAlgebra F (Fin n → ℤ))
      (latticeFunctionField F (Fin n → ℤ)) (b : latticeAlgebra F (Fin n → ℤ)) ≠ 0 := by
    intro h
    refine hb0 (IsFractionRing.injective (latticeAlgebra F (Fin n → ℤ))
      (latticeFunctionField F (Fin n → ℤ)) ?_)
    rw [h, map_zero]
  have hz : z = algebraMap _ _ a
      / algebraMap (latticeAlgebra F (Fin n → ℤ)) (latticeFunctionField F (Fin n → ℤ))
          (b : latticeAlgebra F (Fin n → ℤ)) :=
    (eq_div_iff hS).mpr hb
  obtain ⟨N₁, p, hp⟩ := freeSubst_clear F n a
  obtain ⟨N₂, q, hq⟩ := freeSubst_clear F n (b : latticeAlgebra F (Fin n → ℤ))
  obtain ⟨p', hp'⟩ := freeSubst_mono F n hp (max N₁ N₂) (le_max_left _ _)
  obtain ⟨q', hq'⟩ := freeSubst_mono F n hq (max N₁ N₂) (le_max_right _ _)
  have hU : algebraMap (latticeAlgebra F (Fin n → ℤ))
      (latticeFunctionField F (Fin n → ℤ)) (freeUnit F n (max N₁ N₂)) ≠ 0 := by
    intro h
    refine (freeUnit_isUnit F n (max N₁ N₂)).ne_zero
      (IsFractionRing.injective (latticeAlgebra F (Fin n → ℤ))
        (latticeFunctionField F (Fin n → ℤ)) ?_)
    rw [h, map_zero]
  have haeq : algebraMap (latticeAlgebra F (Fin n → ℤ))
        (latticeFunctionField F (Fin n → ℤ)) a
      = algebraMap (MvPolynomial (Fin n) F) (latticeFunctionField F (Fin n → ℤ)) p'
        / algebraMap (latticeAlgebra F (Fin n → ℤ))
            (latticeFunctionField F (Fin n → ℤ)) (freeUnit F n (max N₁ N₂)) := by
    rw [eq_div_iff hU, ← map_mul, ← hp', algebraMap_freeSubst]
  have hbeq : algebraMap (latticeAlgebra F (Fin n → ℤ))
        (latticeFunctionField F (Fin n → ℤ)) (b : latticeAlgebra F (Fin n → ℤ))
      = algebraMap (MvPolynomial (Fin n) F) (latticeFunctionField F (Fin n → ℤ)) q'
        / algebraMap (latticeAlgebra F (Fin n → ℤ))
            (latticeFunctionField F (Fin n → ℤ)) (freeUnit F n (max N₁ N₂)) := by
    rw [eq_div_iff hU, ← map_mul, ← hq', algebraMap_freeSubst]
  exact ⟨p', q', by rw [hz, haeq, hbeq, div_div_div_cancel_right₀ hU]⟩

end Free

/-! ## 5. 1α 结论：自由格的函数域有理 -/

/-- **1α**：`M = ℤ^n` 自由 ⟹ `F(M) = F(t₁,…,t_n)`。 -/
theorem isRational_latticeFunctionField_free (F : Type*) [Field F] (n : ℕ) :
    IsRational F (latticeFunctionField F (Fin n → ℤ)) := by
  have := freeSubst_isFractionRing F n
  exact ⟨n, ⟨((FractionRing.algEquiv (MvPolynomial (Fin n) F)
    (latticeFunctionField F (Fin n → ℤ))).restrictScalars F).symm⟩⟩

/-- **非空性对照（L1）**：假设类（域 `F`）非空，且结论在具体实例上可落地。 -/
example : IsRational ℚ (latticeFunctionField ℚ (Fin 2 → ℤ)) :=
  isRational_latticeFunctionField_free ℚ 2

/-! ## 6. 公理闸门 -/

#print axioms freeSubst_monomial
#print axioms freeSubst_injective
#print axioms freeUnit_isUnit
#print axioms freeSubst_monomial_const
#print axioms freeSubst_clear_mono
#print axioms freeSubst_clear
#print axioms freeSubst_isFractionRing
#print axioms isRational_latticeFunctionField_free

end EM

end ABGV52
