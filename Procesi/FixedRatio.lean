/-
  Procesi —— **(A)+(B) S3 的核心：`K^{PGL_n}` 的元素是 `S` 中两个不变元之商**

  **原文（逐字）**：`raw/Saltman1999ch14.tex:275–281`，`lem:14.13`：
  > If `a ∈ K^{PGL_n(F)}`, then `a = f/g` where `f,g ∈ S^{PGL_n(F)}`. …
  > write `a = f/g` where `f,g ∈ S` and `f,g` have no common prime divisors (S is a UFD) …
  > `g` divides `φ_A(g)` … `φ_A(g) = λ(A)g` … `λ(A)^n = 1` … `a = f g^{n-1}/g^n`.

  **本件**（三步中的前两步，第三步 `λ` 在下一件）：
  1. `phiA_mul_eq_of_fixed`：`K` 中的固定性 ⟹ `S` 中的**交叉相乘** `φ_A(f)·g = f·φ_A(g)`
     （`map_div₀` ＋ `phiKEquiv_algebraMap` ＋ `IsFractionRing.injective`）；
  2. `dvd_phiA_of_fixed`：互素 ＋ 交叉相乘 ⟹ **Euclid 步** `g ∣ φ_A(g)`
     （`IsRelPrime.dvd_of_dvd_mul_right`；`MvPolynomial` 的 UFD ⇒ `DecompositionMonoid`）；
  3. ★★★ `exists_unit_mul_of_fixed`：对 `A` 与 `A⁻¹` 各用一次 ②，得 `φ_A(g) = c·g` 且 **`c` 是单位**。

  ★ **与原文的差别（L48 ④ 登记；原文无错，换等价更廉路线）**：原文用"`φ_A` 是线性替换 ⟹
  `φ_A(g)` 与 `g` 同次"定 `λ(A) ∈ F^×`；本件改走**对偶整除 ＋ 整环消去**：
  写 `φ_A(g) = g·h`、`φ_{A⁻¹}(g) = g·k`，则 `g = φ_{A⁻¹}(φ_A(g)) = g·k·φ_{A⁻¹}(h)`，
  消去 `g ≠ 0` 得 `1 = k·φ_{A⁻¹}(h)` ⟹ `h` 是单位。**不需要任何次数论**
  （故第 117 轮的 `totalDegree_mul_eq` 不在此依赖链上）。
-/
import Procesi.KAction
import Mathlib.Algebra.Divisibility.Units
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Procesi.PGLAbelian
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.Localization.NumDen

open Matrix

namespace Procesi

noncomputable section

variable (F : Type) [Field F] (r n : ℕ)

lemma phiA_mul_eq_of_fixed {A : (Matrix (Fin n) (Fin n) F)ˣ} {f g : S F r n}
    (hg : g ≠ 0)
    (hfix : phiKEquiv F r n A (algebraMap (S F r n) (SField F r n) f
      / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) f
        / algebraMap (S F r n) (SField F r n) g) :
    phiA F r n A f * g = f * phiA F r n A g := by
  have hinjA : Function.Injective (phiA F r n A) := (phiAEquiv F r n A).injective
  have hinj : Function.Injective (algebraMap (S F r n) (SField F r n)) :=
    IsFractionRing.injective _ _
  have hφg : phiA F r n A g ≠ 0 := fun h => hg (hinjA (by simpa using h))
  have h1 : phiKEquiv F r n A (algebraMap (S F r n) (SField F r n) f
      / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) (phiA F r n A f)
        / algebraMap (S F r n) (SField F r n) (phiA F r n A g) := by
    rw [map_div₀, phiKEquiv_algebraMap, phiKEquiv_algebraMap]
  rw [h1] at hfix
  have hnum : algebraMap (S F r n) (SField F r n) (phiA F r n A f)
      * algebraMap (S F r n) (SField F r n) g
      = algebraMap (S F r n) (SField F r n) f
        * algebraMap (S F r n) (SField F r n) (phiA F r n A g) :=
    (div_eq_div_iff (by simpa using hinj.ne hφg) (by simpa using hinj.ne hg)).mp hfix
  have h2 : algebraMap (S F r n) (SField F r n) (phiA F r n A f * g)
      = algebraMap (S F r n) (SField F r n) (f * phiA F r n A g) := by
    rw [map_mul, map_mul]
    exact hnum
  exact hinj h2

#print axioms phiA_mul_eq_of_fixed

lemma dvd_phiA_of_fixed {A : (Matrix (Fin n) (Fin n) F)ˣ} {f g : S F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : phiKEquiv F r n A (algebraMap (S F r n) (SField F r n) f
      / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) f
        / algebraMap (S F r n) (SField F r n) g) :
    g ∣ phiA F r n A g := by
  have hcross := phiA_mul_eq_of_fixed F r n (A := A) hg hfix
  refine IsRelPrime.dvd_of_dvd_mul_right hcop.symm ⟨phiA F r n A f, ?_⟩
  rw [mul_comm (phiA F r n A g) f, mul_comm g (phiA F r n A f)]
  exact hcross.symm

#print axioms dvd_phiA_of_fixed

/-- ★★★ **S3 的核心一步（对偶整除 ＋ 消去，替代原文的次数论证）**：
`f/g` 被 `φ_A` 与 `φ_{A⁻¹}` 固定、`f,g` 互素 ⟹ `φ_A(g) = c·g` 且 `c` 是**单位**。 -/

lemma exists_unit_mul_of_fixed {A : (Matrix (Fin n) (Fin n) F)ˣ} {f g : S F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfixA : phiKEquiv F r n A (algebraMap (S F r n) (SField F r n) f
      / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) f
        / algebraMap (S F r n) (SField F r n) g)
    (hfixAinv : phiKEquiv F r n A⁻¹ (algebraMap (S F r n) (SField F r n) f
      / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) f
        / algebraMap (S F r n) (SField F r n) g) :
    ∃ c : S F r n, IsUnit c ∧ phiA F r n A g = c * g := by
  obtain ⟨h, hh⟩ := dvd_phiA_of_fixed F r n hcop hg hfixA
  obtain ⟨k, hk⟩ := dvd_phiA_of_fixed F r n hcop hg hfixAinv
  have hcomp : ∀ x : S F r n, phiA F r n A⁻¹ (phiA F r n A x) = x := by
    intro x
    have h := phiA_comp F r n A A⁻¹
    rw [inv_mul_cancel, phiA_one] at h
    have := congrArg (fun (f : S F r n →ₐ[F] S F r n) => f x) h
    simpa using this
  have hAcomp : ∀ x : S F r n, phiA F r n A (phiA F r n A⁻¹ x) = x := by
    intro x
    have h := phiA_comp F r n A⁻¹ A
    rw [mul_inv_cancel, phiA_one] at h
    have := congrArg (fun (f : S F r n →ₐ[F] S F r n) => f x) h
    simpa using this
  have hkey : g = g * (k * phiA F r n A⁻¹ h) := by
    calc g = phiA F r n A⁻¹ (phiA F r n A g) := (hcomp g).symm
      _ = phiA F r n A⁻¹ (g * h) := by rw [hh]
      _ = phiA F r n A⁻¹ g * phiA F r n A⁻¹ h := map_mul _ _ _
      _ = (g * k) * phiA F r n A⁻¹ h := by rw [hk]
      _ = g * (k * phiA F r n A⁻¹ h) := by rw [mul_assoc]
  have hone : k * phiA F r n A⁻¹ h = 1 := by
    have h1 : g * (k * phiA F r n A⁻¹ h) = g * 1 := by rw [mul_one, ← hkey]
    exact mul_left_cancel₀ hg h1
  have hunit_inv : IsUnit (phiA F r n A⁻¹ h) := by
    refine isUnit_iff_exists_inv.mpr ⟨k, ?_⟩
    rw [mul_comm]
    exact hone
  have hunit : IsUnit h := by
    have hm := hunit_inv.map (phiA F r n A).toRingHom
    simpa [hAcomp h] using hm
  exact ⟨h, hunit, by rw [hh, mul_comm]⟩

#print axioms exists_unit_mul_of_fixed
/-- `φ_A` 固定常数（`AlgHom` 与 `algebraMap` 交换）。 -/
lemma phiA_C (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : F) :
    phiA F r n A (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [phiA, MvPolynomial.aeval_C]
  rfl

#print axioms phiA_C

/-- ★★★ **`λ` 的存在性 ＋ 同态性 ＋ 纯量平凡**（原文 `lem:14.13` 证明的"`λ : PGL_n(F) → F^*`"段）。 -/
theorem exists_lambda_hom {f g : S F r n} (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (ha : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A
      (algebraMap (S F r n) (SField F r n) f / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) f / algebraMap (S F r n) (SField F r n) g) :
    ∃ lam : (Matrix (Fin n) (Fin n) F)ˣ →* Fˣ,
      (∀ A, phiA F r n A g = MvPolynomial.C ((lam A : Fˣ) : F) * g) ∧
      (∀ u : Fˣ, lam (GeneralLinearGroup.scalar (Fin n) u) = 1) := by
  classical
  have hex : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, ∃ u : Fˣ,
      phiA F r n A g = MvPolynomial.C ((u : Fˣ) : F) * g := by
    intro A
    obtain ⟨c, hcunit, hc⟩ := exists_unit_mul_of_fixed F r n hcop hg (ha A) (ha A⁻¹)
    obtain ⟨x, hxunit, hx⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hcunit
    obtain ⟨u, rfl⟩ := hxunit
    exact ⟨u, by rw [hc, hx]⟩
  choose lamFun hlam using hex
  refine ⟨{ toFun := lamFun, map_one' := ?_, map_mul' := ?_ }, fun A => hlam A, ?_⟩
  · have h1 : phiA F r n (1 : (Matrix (Fin n) (Fin n) F)ˣ) g = g := by
      rw [phiA_one]; rfl
    have h := hlam 1
    rw [h1] at h
    have hC : MvPolynomial.C ((lamFun 1 : Fˣ) : F) = 1 :=
      mul_right_cancel₀ hg (by rw [h.symm, one_mul])
    exact Units.ext ((MvPolynomial.C_injective (Fin r × Fin n × Fin n) F) hC)
  · intro A B
    have hAB : phiA F r n (A * B) g
        = MvPolynomial.C ((lamFun B : Fˣ) : F) * MvPolynomial.C ((lamFun A : Fˣ) : F) * g := by
      rw [show phiA F r n (A * B) = (phiA F r n A).comp (phiA F r n B) from
        (phiA_comp F r n B A).symm]
      rw [AlgHom.comp_apply, hlam B, map_mul, phiA_C, hlam A]
      ring
    rw [hlam (A * B)] at hAB
    have hC : MvPolynomial.C ((lamFun (A * B) : Fˣ) : F)
        = MvPolynomial.C ((lamFun B : Fˣ) : F) * MvPolynomial.C ((lamFun A : Fˣ) : F) :=
      mul_right_cancel₀ hg hAB
    rw [← map_mul] at hC
    have h' := (MvPolynomial.C_injective (Fin r × Fin n × Fin n) F) hC
    exact Units.ext (by rw [h', mul_comm, Units.val_mul])
  · intro u
    have h1 : phiA F r n (GeneralLinearGroup.scalar (Fin n) u) g = g := by
      rw [phiA_scalar]; rfl
    have h := hlam (GeneralLinearGroup.scalar (Fin n) u)
    rw [h1] at h
    have hC : MvPolynomial.C ((lamFun (GeneralLinearGroup.scalar (Fin n) u) : Fˣ) : F) = 1 :=
      mul_right_cancel₀ hg (by rw [h.symm, one_mul])
    exact Units.ext ((MvPolynomial.C_injective (Fin r × Fin n × Fin n) F) hC)

#print axioms exists_lambda_hom


/-- ★★ **`lam` 过 `PGL`**：`lam : GL_n(F) →* Fˣ` 在纯量上平凡 ⟹ 诱导 `PGL_n(F) →* Fˣ`。 -/
def lamBar {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    (lam : (Matrix n n F)ˣ →* Fˣ)
    (hscalar : ∀ u : Fˣ, lam (GeneralLinearGroup.scalar n u) = 1) :
    Matrix.ProjGenLinGroup n F →* Fˣ :=
  QuotientGroup.lift (Subgroup.center (GeneralLinearGroup n F)) lam
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      have hx' : x ∈ (GeneralLinearGroup.scalar n).range := by
        rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
      obtain ⟨u, rfl⟩ := hx'
      exact hscalar u)

#print axioms lamBar

lemma lamBar_mk {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    (lam : (Matrix n n F)ˣ →* Fˣ)
    (hscalar : ∀ u : Fˣ, lam (GeneralLinearGroup.scalar n u) = 1)
    (A : (Matrix n n F)ˣ) :
    lamBar lam hscalar (Matrix.ProjGenLinGroup.mk A) = lam A := by
  have hker : Subgroup.center (GeneralLinearGroup n F) ≤ lam.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hx' : x ∈ (GeneralLinearGroup.scalar n).range := by
      rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
    obtain ⟨u, rfl⟩ := hx'
    exact hscalar u
  exact QuotientGroup.lift_mk' (Subgroup.center (GeneralLinearGroup n F)) hker A

#print axioms lamBar_mk

/-- ★★★ **`lam A ^ n = 1`**：`lam` 过 `PGL` 后用 `lem:14.12`（`pgl_pow_n_eq_one`）。 -/
lemma lambda_pow_eq_one {F : Type} [Field F] {k : ℕ} (hk : 3 ≤ k)
    (lam : (Matrix (Fin k) (Fin k) F)ˣ →* Fˣ)
    (hscalar : ∀ u : Fˣ, lam (GeneralLinearGroup.scalar (Fin k) u) = 1)
    (A : (Matrix (Fin k) (Fin k) F)ˣ) : lam A ^ k = 1 := by
  have h := pgl_pow_n_eq_one (F := F) hk (lamBar lam hscalar) (Matrix.ProjGenLinGroup.mk A)
  rwa [lamBar_mk] at h

#print axioms lambda_pow_eq_one

/-- ★★★ **原文 `lem:14.13`**：`K` 中被 `PGL_n(F)` 固定的元素是 `S` 中两个不变元之商。 -/
theorem fixed_eq_ratio {k : ℕ} (hk : 3 ≤ k) (a : SField F r k)
    (ha : ∀ A : (Matrix (Fin k) (Fin k) F)ˣ, phiKEquiv F r k A a = a) :
    ∃ f g : S F r k,
      (∀ A, phiA F r k A f = f) ∧ (∀ A, phiA F r k A g = g) ∧ g ≠ 0 ∧
        a = algebraMap (S F r k) (SField F r k) f
          / algebraMap (S F r k) (SField F r k) g := by
  classical
  set f0 : S F r k := IsFractionRing.num (S F r k) a with hf0def
  set g0 : S F r k := (IsFractionRing.den (S F r k) a : S F r k) with hg0def
  have hmem : g0 ∈ nonZeroDivisors (S F r k) := (IsFractionRing.den (S F r k) a).2
  have hg0K : algebraMap (S F r k) (SField F r k) g0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hmem
  have hg0 : g0 ≠ 0 := fun h => hg0K (by rw [h, map_zero])
  have hcop : IsRelPrime f0 g0 := IsFractionRing.num_den_reduced (S F r k) a
  have hratio : a = algebraMap (S F r k) (SField F r k) f0
      / algebraMap (S F r k) (SField F r k) g0 :=
    (IsFractionRing.mk'_num_den' (S F r k) a).symm
  have ha' : ∀ A : (Matrix (Fin k) (Fin k) F)ˣ,
      phiKEquiv F r k A (algebraMap (S F r k) (SField F r k) f0
        / algebraMap (S F r k) (SField F r k) g0)
      = algebraMap (S F r k) (SField F r k) f0
        / algebraMap (S F r k) (SField F r k) g0 := by
    intro A
    rw [← hratio]
    exact ha A
  obtain ⟨lam, hlam, hscalar⟩ := exists_lambda_hom F r k hcop hg0 ha'
  have hpow : ∀ A : (Matrix (Fin k) (Fin k) F)ˣ, lam A ^ k = 1 :=
    fun A => lambda_pow_eq_one hk lam hscalar A
  have hpC : ∀ A : (Matrix (Fin k) (Fin k) F)ˣ,
      (MvPolynomial.C ((lam A : Fˣ) : F) : S F r k) ^ k = 1 := by
    intro A
    have h1 : ((lam A : Fˣ) : F) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow A]
      rfl
    rw [← map_pow, h1, map_one]
  have hf0 : ∀ A : (Matrix (Fin k) (Fin k) F)ˣ,
      phiA F r k A f0 = MvPolynomial.C ((lam A : Fˣ) : F) * f0 := by
    intro A
    have hcross := phiA_mul_eq_of_fixed F r k (A := A) hg0 (ha' A)
    rw [hlam A] at hcross
    refine mul_right_cancel₀ hg0 ?_
    rw [hcross]
    ring
  refine ⟨f0 * g0 ^ (k - 1), g0 ^ k, ?_, ?_, pow_ne_zero _ hg0, ?_⟩
  · intro A
    have hk1 : k - 1 + 1 = k := by omega
    have hφg : phiA F r k A (g0 ^ (k - 1))
        = (MvPolynomial.C ((lam A : Fˣ) : F) : S F r k) ^ (k - 1) * g0 ^ (k - 1) := by
      rw [map_pow, hlam A, mul_pow]
    rw [map_mul, hf0 A, hφg]
    have hCc : (MvPolynomial.C ((lam A : Fˣ) : F) : S F r k)
        * (MvPolynomial.C ((lam A : Fˣ) : F) : S F r k) ^ (k - 1) = 1 := by
      rw [← pow_succ', hk1, hpC A]
    calc (MvPolynomial.C ((lam A : Fˣ) : F) : S F r k) * f0
          * ((MvPolynomial.C ((lam A : Fˣ) : F) : S F r k) ^ (k - 1) * g0 ^ (k - 1))
        = f0 * ((MvPolynomial.C ((lam A : Fˣ) : F) : S F r k)
            * (MvPolynomial.C ((lam A : Fˣ) : F) : S F r k) ^ (k - 1)) * g0 ^ (k - 1) := by
          ring
      _ = f0 * g0 ^ (k - 1) := by rw [hCc, mul_one]
  · intro A
    rw [map_pow, hlam A, mul_pow, hpC A, one_mul]
  · rw [hratio]
    simp only [map_mul, map_pow]
    have hk1 : k - 1 + 1 = k := by omega
    have hpows : (algebraMap (S F r k) (SField F r k) g0) ^ k
        = (algebraMap (S F r k) (SField F r k) g0) ^ (k - 1)
          * (algebraMap (S F r k) (SField F r k) g0) := by
      set x : SField F r k := algebraMap (S F r k) (SField F r k) g0
      calc x ^ k = x ^ (k - 1 + 1) := congrArg (fun m => x ^ m) hk1.symm
        _ = x ^ (k - 1) * x := pow_succ x (k - 1)
    rw [div_eq_div_iff hg0K (pow_ne_zero _ hg0K), hpows]
    ring

#print axioms fixed_eq_ratio

end

end Procesi
