/-
  ABGV-5.2 · B 档 · M3 —— **局部提升判据**（Saltman 1984 §3，`thm3.9(ii)`／`thm3.8`，2026-10-12）

  **来源** ✓：`raw/Saltman1984.tex:501–517`（label `thm3.8`／`thm3.9` ✓；**⚠-tex-sourced** ✗）逐字：
  > **thm3.8.** Let \(K / F\) be an extension of fields. The following are equivalent:
  > (i) \(K / F\) is retract rational. (ii) \(K\) is the quotient field of an affine \(F\) algebra
  > \(S\) which satisfies the following condition. Suppose \(T\), \(M\) is a local \(F\) algebra,
  > \(L = T / M\), \(\rho : T \to L\) is the canonical map, and \(\phi : S \to L\) is an \(F\)
  > algebra map. Then there is an \(F\) algebra map \(\phi^{\prime}: S \to T\) such that
  > \(\rho \circ \phi^{\prime} = \phi\).
  > **thm3.9.** Let \(\phi : S \to R\) be an \(F\) algebra map between \(F\) algebra domains. TFAE:
  > (i) \(\phi\) factors rationally. (ii) There is a \(0 \neq r \in R\) such that the induced map
  > \(\phi : S \to R(1 / r)\) has the following property. Suppose \(T\), \(M\) is a local \(F\)
  > algebra, \(L = T / M\), \(\rho : T \to L\) is the canonical map, and \(\psi : R(1 / r) \to L\)
  > is any \(F\) algebra map. Then there is an \(F\) algebra map \(\psi^{\prime}: S \to T\) such that
  > \(\rho \circ \psi^{\prime} = \psi \circ \phi\).

  **本件内容** ✓（**M3 的第一块** ✓，蓝图 `wiki/proj-ABGV52-formalize-saltman.md` §1.1 步骤 11 ✓）：
  ① **`HasLocalLifting F S R φ`** ✓ ＝ 源 `thm3.9(ii)` 的**用点形** ✓（局部 `F`-代数取
     **`IsLocalRing T`** ✓；「`L = T/M`」取 **`IsLocalRing.ResidueField T`** ✓；
     「`ρ` 为典范映射」取 **`IsLocalRing.residue T`** ✓）；
  ② **工具** ✓ `isUnit_of_isUnit_residue` ✓ —— 源 `thm3.9` 证明中「`μ(w)` 是单位」一步的**实体** ✓；
  ③ **易方向** ✓✓ `hasLocalLifting_of_factorsRationally` ✓（源 `thm3.9` 的 **(i)⟹(ii)** ✓，**逐句移植** ✓）；
  ④ **登记** ✗：**反方向**（(ii)⟹(i) ✓）与 **`thm3.8`** ✓ —— 见文末 ✓。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import ABGV52.SaltDef_ABGV52
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
open TensorProduct MvPolynomial
open scoped Ring
universe u
noncomputable section

namespace ABGV52

/-! ## 1. 局部提升性质（源 `thm3.9(ii)` 的用点形 ✓） -/

/-- **工具** ✓（源 `thm3.9` 证明中「`μ(w)` 是单位」一步的**实体** ✓）：局部环中
`residue x` 为单位 ⟹ `x` 为单位 ✓。
**证法** ✓：`residue x ≠ 0` ✓（剩余域是**域** ✓）⟹ `x ∉ 𝔪` ✓
（`IsLocalRing.residue_eq_zero_iff` ✓）⟹ `IsUnit x` ✓（`IsLocalRing.notMem_maximalIdeal` ✓）。
**⚠ 意义** ✓：这条**正是**「局部」一词的数学内容 ✓（单元的**反射** ✓，与 §96 的 `IsLocalHom` 同源 ✓）。 -/
lemma isUnit_of_isUnit_residue {T : Type u} [CommRing T] [IsLocalRing T] {x : T}
    (h : IsUnit (IsLocalRing.residue T x)) : IsUnit x := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hx
  have h0 : IsLocalRing.residue T x = 0 := (IsLocalRing.residue_eq_zero_iff x).mpr hx
  rw [h0] at h
  exact not_isUnit_zero h

/-- **源 `thm3.9(ii)`** ✓（**局部提升性质** ✓，**用点形** ✓）：存在 `0 ≠ r : R` 使
「沿局部 `F`-代数 `T` 的剩余域 `L = T/𝔪` 的**典范映射 `ρ = residue`** 的提升总存在」✓ ——
对每个 `ψ : R(1/r) →ₐ[F] L` ✓，存在 `ψ' : S →ₐ[F] T` ✓ 使 `ρ ∘ ψ' = ψ ∘ φ` ✓
（等式逐点写在剩余域里 ✓，避开 `ρ` 的 `AlgHom` 外形问题 ✓）。
**⚠ 宇宙档** ✓：**单宇宙** ✓（与本工程既有的单宇宙接口一致 ✓，§58.4 教训 ✓）。 -/
def HasLocalLifting (F : Type u) [Field F] (S R : Type u) [CommRing S] [CommRing R]
    [Algebra F S] [Algebra F R] (φ : S →ₐ[F] R) : Prop :=
  ∃ r : R, r ≠ 0 ∧
    ∀ (T : Type u) [CommRing T] [Algebra F T] [IsLocalRing T]
      (ψ : Localization.Away r →ₐ[F] IsLocalRing.ResidueField T),
      ∃ ψ' : S →ₐ[F] T, ∀ s : S,
        IsLocalRing.residue T (ψ' s) = ψ (algebraMap R (Localization.Away r) (φ s))

/-- **类型锁定（同一性形）** ✓：钉住本谓词的运行类型与**宇宙档** ✓。 -/
theorem hasLocalLifting_typeLock (F : Type u) [Field F] (S R : Type u) [CommRing S] [CommRing R]
    [Algebra F S] [Algebra F R] (φ : S →ₐ[F] R) :
    (HasLocalLifting F S R φ) = (HasLocalLifting F S R φ) := rfl

/-! ## 2. 非空洞探针（L1 ✓） -/

/-- **非空洞探针（L1）** ✓：`S = R = F`、`φ = AlgHom.id` 档取 `r = 1` ✓ ——
`ψ' := Algebra.ofId F T` ✓，等式由 `IsLocalRing.ResidueField` 的 `F`-代数结构 ✓
（`residue ∘ algebraMap = algebraMap` ✓）与 `AlgHom.commutes` ✓ 收口 ✓。
**⚠ 口径** ✓：本探针只证**假设类非空** ✓（谓词可被满足 ✓）；其**结论的强度**由 §3 ✓ 供给 ✓。 -/
theorem hasLocalLifting_id_data_nonempty (F : Type u) [Field F] :
    HasLocalLifting F F F (AlgHom.id F F) := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro T _ _ _ ψ
  refine ⟨Algebra.ofId F T, fun c => ?_⟩
  show IsLocalRing.residue T (algebraMap F T c)
    = ψ (algebraMap F (Localization.Away (1 : F)) ((AlgHom.id F F) c))
  rw [AlgHom.id_apply, AlgHom.commutes]
  rfl

/-! ## 3. 源 `thm3.9` 的易方向（(i)⟹(ii) ✓） -/

/-- **源 `thm3.9` 的 (i)⟹(ii)** ✓✓✓（**逐句移植** ✓）：`φ : S → R` factors rationally ⟹
`HasLocalLifting` ✓。
**证法** ✓（源 `:522–526` ✓）：取分解 `φ = η ∘ ψ₀` ✓（`FactorsRationally` 的见证 ✓）；
对局部 `T` 与 `ψ : R(1/r) →ₐ[F] L`，命 `a_i := ψ (η (x_i))` ✓、取原像 `b_i` ✓
（**`IsLocalRing.residue_surjective`** ✓），`μ₀ := MvPolynomial.aeval b` ✓；
证 `residue (μ₀ p) = ψ (η (p/1))` ✓（两边都是 `F`-代数同态 ✓，在生成元上由 `b_i` 的取法一致 ✓）；
取 `p := w` ✓ 并用 `w` 在 `F[x](1/w)` 中为单位 ✓ 得 `μ₀ w` 为单位 ✓
（**`isUnit_of_isUnit_residue`** ✓ —— 此处正是「局部」被用到的地方 ✓）；
**`IsLocalization.liftAlgHom`** ✓ 把它下降为 `μ : F[x](1/w) →ₐ[F] T` ✓；
`ψ' := μ ∘ ψ₀` ✓，最后用 **`IsLocalization.algHom_ext`** ✓ 把 `ρ ∘ μ = ψ ∘ η` 化归到
`algebraMap` 的像上 ✓，再用 `hfac` ✓ 收口 ✓。 -/
theorem hasLocalLifting_of_factorsRationally {F S R : Type u} [Field F]
    [CommRing S] [IsDomain S] [Algebra F S]
    [CommRing R] [IsDomain R] [Algebra F R] (φ : S →ₐ[F] R)
    (h : FactorsRationally F S R φ) : HasLocalLifting F S R φ := by
  obtain ⟨n, w, hw, r, hr, ψ₀, η, hfac⟩ := h
  refine ⟨r, hr, ?_⟩
  intro T _ _ _ ψ
  have hsurj : Function.Surjective (IsLocalRing.residue T) := IsLocalRing.residue_surjective
  choose b hb using fun i : Fin n =>
    hsurj (ψ (η (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) (MvPolynomial.X i))))
  let μ₀ : MvPolynomial (Fin n) F →ₐ[F] T := MvPolynomial.aeval b
  have key : ∀ p : MvPolynomial (Fin n) F,
      IsLocalRing.residue T (μ₀ p)
        = ψ (η (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) p)) := by
    intro p
    have h1 : (Algebra.algHom F T (IsLocalRing.ResidueField T)).comp μ₀
        = ψ.comp (η.comp (Algebra.algHom F (MvPolynomial (Fin n) F) (Localization.Away w))) := by
      apply MvPolynomial.algHom_ext
      intro i
      change IsLocalRing.residue T (μ₀ (MvPolynomial.X i))
        = ψ (η (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) (MvPolynomial.X i)))
      rw [show μ₀ (MvPolynomial.X i) = b i from MvPolynomial.aeval_X b i]
      exact hb i
    change (Algebra.algHom F T (IsLocalRing.ResidueField T)) (μ₀ p)
      = ψ (η ((Algebra.algHom F (MvPolynomial (Fin n) F) (Localization.Away w)) p))
    exact congrArg (fun f => f p) h1
  have hunit : IsUnit (μ₀ w) := by
    apply isUnit_of_isUnit_residue
    rw [key w]
    exact ((IsLocalization.Away.algebraMap_isUnit (R := MvPolynomial (Fin n) F)
      (S := Localization.Away w) (x := w)).map η).map ψ
  let μ : Localization.Away w →ₐ[F] T :=
    IsLocalization.liftAlgHom (M := Submonoid.powers w) (S := Localization.Away w) (f := μ₀) (by
      rintro ⟨y, hy⟩
      change IsUnit (μ₀ y)
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff y w).mp hy
      rw [← hk, map_pow]
      exact hunit.pow k)
  have hμ_alg : ∀ p : MvPolynomial (Fin n) F,
      μ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) p) = μ₀ p := by
    intro p
    dsimp only [μ]
    rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
    rfl
  refine ⟨μ.comp ψ₀, ?_⟩
  intro s
  have hcomp : (Algebra.algHom F T (IsLocalRing.ResidueField T)).comp μ = ψ.comp η := by
    apply IsLocalization.algHom_ext (Submonoid.powers w)
    refine AlgHom.ext (fun p => ?_)
    show (Algebra.algHom F T (IsLocalRing.ResidueField T)) (μ (algebraMap _ _ p))
      = ψ (η (algebraMap _ _ p))
    rw [hμ_alg p]
    exact key p
  have hpt := congrArg (fun f => f (ψ₀ s)) hcomp
  simp only [AlgHom.comp_apply] at hpt
  show IsLocalRing.residue T ((μ.comp ψ₀) s) = ψ (algebraMap R (Localization.Away r) (φ s))
  rw [AlgHom.comp_apply]
  change (Algebra.algHom F T (IsLocalRing.ResidueField T)) (μ (ψ₀ s))
    = ψ (algebraMap R (Localization.Away r) (φ s))
  rw [hpt, hfac s]

/-! ## 4. 仿射层（源 `thm3.9` 证明 `:528–531` 的两处**「affine」** ✓） -/

/-- **仿射 ⟹ 多项式环的满射** ✓✓（源逐字：「Since `R(1/r)` is **affine**, there is an `F` algebra
surjection `η : F[x₁,…,xₙ] → R(1/r)`」✓，印版 p.185 ✓）：
`Algebra.FiniteType F R` ⟹ 存在 `n` 与**满射** `η : F[x₁,…,xₙ] →ₐ[F] R` ✓。
**证法** ✓：`Algebra.FiniteType.iff_quotient_mvPolynomial''` ✓（**mathlib 已备** ✓，
`Fin n` 档 ✓，与本工程 `FactorsRationally` 的载体一致 ✓）。 -/
theorem exists_surjective_mvPolynomial_of_finiteType {F R : Type u} [Field F] [CommRing R]
    [Algebra F R] (h : Algebra.FiniteType F R) :
    ∃ (n : ℕ) (η : MvPolynomial (Fin n) F →ₐ[F] R), Function.Surjective η :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h

/-- **反方向** ✓：多项式环有满射落到 `R` ⟹ `R` 仿射 ✓（同一 `iff` 的另一半 ✓）。 -/
theorem finiteType_of_surjective_mvPolynomial {F R : Type u} [Field F] [CommRing R]
    [Algebra F R] {n : ℕ} (η : MvPolynomial (Fin n) F →ₐ[F] R)
    (h : Function.Surjective η) : Algebra.FiniteType F R :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨n, η, h⟩

/-- **用点** ✓（源逐字：「Let `P` be the **kernel** of `η`」✓，印版 p.185 ✓）：仿射**整环** ⟹
存在满射 `η` 且其**核为素理想** ✓（`RingHom.ker_isPrime` ✓ —— 目标为整环 ✓）。 -/
theorem exists_surjective_mvPolynomial_with_prime_ker {F R : Type u} [Field F] [CommRing R]
    [IsDomain R] [Algebra F R] (h : Algebra.FiniteType F R) :
    ∃ (n : ℕ) (η : MvPolynomial (Fin n) F →ₐ[F] R),
      Function.Surjective η ∧ (RingHom.ker η).IsPrime := by
  obtain ⟨n, η, hη⟩ := exists_surjective_mvPolynomial_of_finiteType (F := F) h
  exact ⟨n, η, hη, RingHom.ker_isPrime η⟩

/-- **用点** ✓（源同句 ✓）：该满射给出**同构** `F[x₁,…,xₙ] ⧸ P ≃ₐ[F] R` ✓
（`Ideal.quotientKerAlgEquivOfSurjective` ✓）—— 即源把 `R(1/r)` 认成 `F[x]/P` ✓ 的那一步 ✓。 -/
theorem quotient_ker_algEquiv_of_surjective {F R : Type u} [Field F] [CommRing R] [Algebra F R]
    {n : ℕ} (η : MvPolynomial (Fin n) F →ₐ[F] R) (h : Function.Surjective η) :
    Nonempty ((MvPolynomial (Fin n) F ⧸ RingHom.ker η) ≃ₐ[F] R) :=
  ⟨Ideal.quotientKerAlgEquivOfSurjective h⟩

/-! ## 5. 「域档」推论（源 `thm3.9` 反方向的**第 6 步**实体 ✓） -/

/-- **工具** ✓：**域上 `residue` 单** ✓（`Algebra.algHom` 形 ✓）。
**证法** ✓：`residue x = 0` ⟹ `x ∈ 𝔪` ✓（`IsLocalRing.residue_eq_zero_iff` ✓）
⟹ `x ∈ ⊥` ✓（`IsLocalRing.maximalIdeal_eq_bot` ✓，域 ✓）⟹ `x = 0` ✓。 -/
lemma residue_injective_of_field {F K : Type u} [Field F] [Field K] [Algebra F K] :
    Function.Injective (Algebra.algHom F K (IsLocalRing.ResidueField K)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : IsLocalRing.residue K x = 0 := hx
  have hmem : x ∈ IsLocalRing.maximalIdeal K := (IsLocalRing.residue_eq_zero_iff x).mp hx'
  rw [IsLocalRing.maximalIdeal_eq_bot] at hmem
  simpa using hmem

/-- **源 `thm3.9` 反方向的第 6 步** ✓✓✓（源印版 p.185 逐字：「Applying 3.9(ii) to the inclusion
`i : R(1/r) → K`, we have an `F` algebra map `ψ : S → T` such that `η ∘ ψ = i ∘ φ`」✓）：
**域档**形式 ✓ —— `HasLocalLifting` ⟹ 每个 `F`-代数映射 `R(1/r) → K`（`K` 是**域** ✓）
都可**提升**为 `S → K` 且**等式成立** ✓（不只剩余域里成立 ✓）。
**证法** ✓：域的剩余域是它自己 ✓（`IsLocalRing.maximalIdeal_eq_bot` ✓ ＋
`residue_injective_of_field` ✓）⟹ 把 3.9(ii) 用在 `T := K` 上即可 ✓
（**⚠ 一处实测** ✓：此处 `H` 须以**显式实例**应用 ✓ —— `@H K inferInstance …` ✓，
否则触发 `Algebra ?m K` 僵持 ✗，见 §66.4 同类 ✓）。 -/
theorem exists_lift_to_field_of_hasLocalLifting {F S R : Type u} [Field F]
    [CommRing S] [Algebra F S] [CommRing R] [Algebra F R] (φ : S →ₐ[F] R)
    (h : HasLocalLifting F S R φ) :
    ∃ r : R, r ≠ 0 ∧ ∀ (K : Type u) [Field K] [Algebra F K]
      (ψ : Localization.Away r →ₐ[F] K),
      ∃ ψ' : S →ₐ[F] K, ∀ s : S, ψ' s = ψ (algebraMap R (Localization.Away r) (φ s)) := by
  obtain ⟨r, hr, H⟩ := h
  refine ⟨r, hr, ?_⟩
  intro K _ _ ψ
  obtain ⟨ψ', hψ'⟩ := @H K inferInstance inferInstance inferInstance
    ((Algebra.algHom F K (IsLocalRing.ResidueField K)).comp ψ)
  refine ⟨ψ', fun s => ?_⟩
  exact residue_injective_of_field (F := F) (K := K) (by
    have h1 := hψ' s
    change (Algebra.algHom F K (IsLocalRing.ResidueField K)) (ψ' s)
      = (Algebra.algHom F K (IsLocalRing.ResidueField K))
          (ψ (algebraMap R (Localization.Away r) (φ s))) at h1
    simpa [AlgHom.comp_apply] using h1)

/-! ## 6. `F[x]_P` 及其剩余域（源印版 p.185 的两处命名 ✓） -/

/-- **用点** ✓（源逐字：「form the local ring `F[x₁,…,xₙ]_P` = `T`」✓，印版 p.185 ✓）：
源写的 `F[x₁,…,xₙ]_P` **就是** `Localization.AtPrime P` ✓，且它是**局部环** ✓。 -/
theorem isLocalRing_localization_atPrime {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime] :
    IsLocalRing (Localization.AtPrime P) := inferInstance

/-- **用点** ✓（源逐字：「If `M` is the maximal ideal of `T`, and `K` is the quotient field of `R`,
then `T/M = K`」✓，印版 p.185 ✓）：`T = F[x]_P` 的**剩余域** ＝ 商 `F[x]/P` 的**分式域** ✓
（`Ideal.ResidueField P = IsLocalRing.ResidueField (Localization.AtPrime P)` ✓，
mathlib 已给 `IsFractionRing (A ⧸ P) P.ResidueField` ✓）。 -/
theorem isFractionRing_residueField_atPrime {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime] :
    IsFractionRing (A ⧸ P) (Ideal.ResidueField P) := inferInstance

/-! ## 7. 反方向的**设置**：`F[x]_P` 上的提升（源印版 p.185 中段 ✓） -/

/-- **整环在非零元处的局部化仍是整环** ✓（`IsLocalization.Away.isDomain` ✓）——
源反方向里「`R(1/r)` 是整环」✓（因而 `P = ker η₀` 为素理想 ✓）的**前置** ✓。 -/
theorem isDomain_localization_away {R : Type u} [CommRing R] [IsDomain R] {r : R} (hr : r ≠ 0) :
    IsDomain (Localization.Away r) :=
  IsLocalization.Away.isDomain (Localization.Away r) hr

/-- **源反方向的残差映射** ✓✓（源「`T/M = K`」＋「`η` extends to the map `η : T → K`」✓，印版 p.185 ✓）：
由 §66 的满射 `η₀ : F[x] ↠ R'` ✓、`P := ker η₀` ✓、`T := F[x]_P` ✓ 与 mathlib 的
`IsFractionRing (F[x] ⧸ P) P.ResidueField` ✓ 复合得 `R' →ₐ[F] T/𝔪` ✓ ——
即源里那条 `R(1/r) → K` ✓（本工程**取 `K := P.ResidueField`** ✓，从而**免去** `q(R)` 的识别 ✗）。
**⚠ 载体** ✓：`P` 的素性以**实例参数**承载 ✓（`RingHom.ker_isPrime` ✓ 是定理而非实例 ✗）。 -/
noncomputable def residueMapOfSurjective {F R' : Type u} [Field F] [CommRing R'] [Algebra F R']
    {n : ℕ} (η₀ : MvPolynomial (Fin n) F →ₐ[F] R') (hη₀ : Function.Surjective η₀)
    [(RingHom.ker η₀).IsPrime] :
    R' →ₐ[F] Ideal.ResidueField (RingHom.ker η₀) :=
  (Algebra.algHom F (MvPolynomial (Fin n) F ⧸ RingHom.ker η₀)
      (Ideal.ResidueField (RingHom.ker η₀))).comp
    ((Ideal.quotientKerAlgEquivOfSurjective hη₀).symm : R' →ₐ[F] _)

/-- **源反方向的中段** ✓✓✓（印版 p.185 逐字：「Applying 3.9(ii) … we have an `F` algebra map
`ψ : S → F[x₁,…,xₙ]_P = T` such that `η ∘ ψ = i ∘ φ`」✓）：把 `HasLocalLifting` 用在
**`T := F[x]_P`** 上 ✓ —— 对任一满射 `η₀ : F[x] ↠ R(1/r)` ✓，得 `ψ : S →ₐ[F] T` ✓ 且
**剩余域里有** `ρ (ψ s) = ρR (φ s /1)` ✓。
**⚠ 应用手法** ✓：此处 `H` 须以**显式实例**应用 ✓（`@H T inferInstance …` ✓，§67.4 读数 ✓）。 -/
theorem exists_lift_to_atPrime_of_hasLocalLifting {F S R : Type u} [Field F]
    [CommRing S] [Algebra F S] [CommRing R] [IsDomain R] [Algebra F R] (φ : S →ₐ[F] R)
    (h : HasLocalLifting F S R φ) :
    ∃ r : R, r ≠ 0 ∧ ∀ {n : ℕ} (η₀ : MvPolynomial (Fin n) F →ₐ[F] Localization.Away r)
      (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime],
      ∃ ψ : S →ₐ[F] Localization.AtPrime (RingHom.ker η₀),
        ∀ s : S, IsLocalRing.residue (Localization.AtPrime (RingHom.ker η₀)) (ψ s)
          = residueMapOfSurjective (F := F) η₀ hη₀
              (algebraMap R (Localization.Away r) (φ s)) := by
  obtain ⟨r, hr, H⟩ := h
  refine ⟨r, hr, ?_⟩
  intro n η₀ hη₀ _
  obtain ⟨ψ, hψ⟩ := @H (Localization.AtPrime (RingHom.ker η₀)) inferInstance inferInstance
    inferInstance (residueMapOfSurjective (F := F) η₀ hη₀)
  exact ⟨ψ, hψ⟩

/-! ## 8. 源反方向的**步 ⑤ 工具**（局部化中的公共分母 ✓） -/

/-- **源步 ⑤ 的工具** ✓✓✓（印版 p.185：「**Since `S` is affine**, `ψ(S) ⊂ F[x₁,…,xₙ](1/w)`
for some `w ∉ P`」✓）：局部化 `B = A_M` 中**有限个**元素有**公共分母** ✓ ——
存在 `m ∈ M`，使每个 `x ∈ X` 都满足 `x · (m/1)^k = a/1`（`a ∈ A`，`k` 可随 `x` 变 ✓），
即 `x ∈ A[1/m]` ✓。
**证法** ✓（对 `X` 归纳 ✓，**指数记账**是全部内容 ✓）：单元用 `IsLocalization.surj` ✓ 取分母 ✓；
合并时取 `m := m₁·m₂` ✓，**旧元素的指数升 1** ✓（因 `(m₁m₂)^{k+1}` 含因子 `m₁^{k+1}` ✓
故可用旧式 `x·m₁^k = a` 清分母 ✓）✓。
**⚠ 与 `SaltSwan.exists_localization_ge_adjoin` 的区别** ✓：后者是**分式域**档 ✗
（`S : Subalgebra F K`、`IsFractionRing S K` ✓），**不**覆盖「**局部化**的有限型子代数」✗ —— 故本条须另立 ✓。 -/
theorem exists_mem_localization_ge_finset {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {M : Submonoid A} [IsLocalization M B] (X : Finset B) :
    ∃ m : M, ∀ x ∈ X, ∃ (a : A) (k : ℕ),
      x * (algebraMap A B (m : A)) ^ k = algebraMap A B a := by
  classical
  refine Finset.induction_on (s := X) ?_ ?_
  · exact ⟨1, by simp⟩
  · intro z Z hz ih
    obtain ⟨m₁, h₁⟩ := ih
    obtain ⟨⟨a₀, m₂⟩, hm₂⟩ := IsLocalization.surj M z
    refine ⟨m₁ * m₂, ?_⟩
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxz | hx
    · rw [hxz]
      refine ⟨a₀ * (m₁ : A), 1, ?_⟩
      rw [pow_one, Submonoid.coe_mul, map_mul, map_mul]
      calc z * (algebraMap A B (m₁ : A) * algebraMap A B ((m₂ : M) : A))
          = (z * algebraMap A B ((m₂ : M) : A)) * algebraMap A B (m₁ : A) := by ring
        _ = algebraMap A B a₀ * algebraMap A B (m₁ : A) := by rw [hm₂]
    · obtain ⟨a, k, hk⟩ := h₁ x hx
      refine ⟨a * (m₁ : A) * ((m₂ : M) : A) ^ (k + 1), k + 1, ?_⟩
      have hpow : (algebraMap A B ((m₁ : A) * ((m₂ : M) : A))) ^ (k + 1)
          = (algebraMap A B (m₁ : A)) ^ (k + 1)
            * (algebraMap A B ((m₂ : M) : A)) ^ (k + 1) := by
        rw [map_mul, mul_pow]
      rw [Submonoid.coe_mul, hpow]
      calc x * ((algebraMap A B (m₁ : A)) ^ (k + 1)
            * (algebraMap A B ((m₂ : M) : A)) ^ (k + 1))
          = (x * (algebraMap A B (m₁ : A)) ^ k * algebraMap A B (m₁ : A))
              * (algebraMap A B ((m₂ : M) : A)) ^ (k + 1) := by
              rw [pow_succ]; ring
        _ = (algebraMap A B a * algebraMap A B (m₁ : A))
              * (algebraMap A B ((m₂ : M) : A)) ^ (k + 1) := by rw [hk]
        _ = algebraMap A B (a * (m₁ : A) * ((m₂ : M) : A) ^ (k + 1)) := by
              rw [map_mul, map_mul, map_pow]

/-- **源步 ⑤（有限型子代数档）** ✓✓✓：局部化 `B = A_M` 中由**有限集 `X`** 生成的子代数
`Algebra.adjoin A X` **整体**落在 `A[1/m]` 里 ✓（**同一个 `m`** ✓）。
**证法** ✓：由 §8 的 `exists_mem_localization_ge_finset` ✓ 取公共分母 `m` ✓，
把目标性质**组装成子代数 `D`** ✓（`add`／`mul` 取指数 `k + l` ✓；`algebraMap c`／`0`／`1` 取指数 `0` ✓），
再用 **`Algebra.adjoin_le`** ✓ 收口 ✓。
**⚠ 用途** ✓：这正是源步 ⑤「**Since `S` is affine**, `ψ(S) ⊂ F[x](1/w)`」✓ 的**代数内核** ✓
（取 `X := ψ(生成元集)` ✓）。 -/
theorem exists_mem_localization_ge_adjoin {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {M : Submonoid A} [IsLocalization M B] (X : Finset B) :
    ∃ m : M, ∀ x ∈ Algebra.adjoin A (X : Set B), ∃ (a : A) (k : ℕ),
      x * (algebraMap A B (m : A)) ^ k = algebraMap A B a := by
  classical
  obtain ⟨m, hm⟩ := exists_mem_localization_ge_finset (M := M) X
  refine ⟨m, ?_⟩
  let D : Subalgebra A B :=
    { carrier := {x | ∃ (a : A) (k : ℕ), x * (algebraMap A B (m : A)) ^ k = algebraMap A B a}
      mul_mem' := by
        rintro x y ⟨a, k, ha⟩ ⟨b, l, hb⟩
        refine ⟨a * b, k + l, ?_⟩
        rw [pow_add]
        calc x * y * ((algebraMap A B (m : A)) ^ k * (algebraMap A B (m : A)) ^ l)
            = (x * (algebraMap A B (m : A)) ^ k)
                * (y * (algebraMap A B (m : A)) ^ l) := by ring
          _ = algebraMap A B a * algebraMap A B b := by rw [ha, hb]
          _ = algebraMap A B (a * b) := by rw [map_mul]
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by
        rintro x y ⟨a, k, ha⟩ ⟨b, l, hb⟩
        refine ⟨a * (m : A) ^ l + b * (m : A) ^ k, k + l, ?_⟩
        rw [pow_add, map_add, map_mul, map_mul, map_pow, map_pow]
        calc (x + y) * ((algebraMap A B (m : A)) ^ k * (algebraMap A B (m : A)) ^ l)
            = x * (algebraMap A B (m : A)) ^ k * (algebraMap A B (m : A)) ^ l
              + y * (algebraMap A B (m : A)) ^ l
                * (algebraMap A B (m : A)) ^ k := by ring
          _ = algebraMap A B a * (algebraMap A B (m : A)) ^ l
              + algebraMap A B b * (algebraMap A B (m : A)) ^ k := by rw [ha, hb]
      zero_mem' := ⟨0, 0, by simp⟩
      algebraMap_mem' := fun c => ⟨c, 0, by simp⟩ }
  have hXD : (X : Set B) ⊆ D := fun x hx => hm x hx
  have hsub : Algebra.adjoin A (X : Set B) ≤ D := Algebra.adjoin_le hXD
  intro x hx
  exact hsub hx

/-- **源步 ⑤ 的用点形** ✓✓（**素理想档** ✓）：取 `M := P.primeCompl` ✓ 即源里的「`w ∉ P`」✓ ——
存在 `w ∉ P` 使 `X` 的每个元素都属于 `F[x](1/w)` ✓。 -/
theorem exists_mem_primeCompl_of_finset {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal A) [P.IsPrime] [IsLocalization P.primeCompl B] (X : Finset B) :
    ∃ w : A, w ∉ P ∧ ∀ x ∈ X, ∃ (a : A) (k : ℕ),
      x * (algebraMap A B w) ^ k = algebraMap A B a := by
  obtain ⟨m, hm⟩ := exists_mem_localization_ge_finset (M := P.primeCompl) X
  exact ⟨(m : A), m.2, hm⟩

/-! ## 9. 步 ⑤ 的**接口**：把 `ψ` 核限制到单元局部化（源「`ψ(S) ⊂ F[x](1/w)`」✓） -/

/-- **一般核限制引理** ✓✓✓（本工程自立的接口 ✓）：设 `ι : A[1/w] →ₐ[A] B` **单** ✓ 且
`ψ : S →ₐ[A] B` 的像落在 `ι.range` 里 ✓，则 `ψ` **唯一地**分解为 `ι ∘ ψ'` ✓（`ψ' : S →ₐ[A] A[1/w]` ✓）。
**证法** ✓：`ψ.codRestrict ι.range hψ` ✓ ＋ `AlgEquiv.ofInjective ι hι` ✓ 的**逆向**复合 ✓。
**⚠ 用途** ✓：源步 ⑤ 说 `ψ(S) ⊂ F[x](1/w)` ✓ —— 本条即把该「包含」**兑现**为
「`ψ` 穿过 `F[x](1/w)`」✓（把 `T = F[x]_P` 上的 `ψ` 换成 `F[x](1/w)` 上的 `ψ'` ✓），
供最后组装 `φ = η ∘ ψ'` ✓ 使用 ✓。 -/
theorem exists_factor_through_of_injective {R A B S : Type u} [CommSemiring R] [CommRing A]
    [CommRing B] [CommRing S] [Algebra R A] [Algebra R B] [Algebra R S] (w : A)
    (ι : Localization.Away w →ₐ[R] B)
    (hι : Function.Injective ι) (ψ : S →ₐ[R] B) (hψ : ∀ s : S, ψ s ∈ ι.range) :
    ∃ ψ' : S →ₐ[R] Localization.Away w, ι.comp ψ' = ψ := by
  refine ⟨(((AlgEquiv.ofInjective ι hι).symm : ι.range →ₐ[R] Localization.Away w)).comp
    (ψ.codRestrict ι.range hψ), ?_⟩
  ext s
  exact congrArg Subtype.val (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjective ι hι) _)

/-- **非空洞探针（L1）** ✓：`S = A`、`ι = AlgHom.id`（`B = A[1/1]`）档 ✓ ——
`ψ'` 即 `algebraMap` ✓，故本引理的假设类**非空** ✓。 -/
theorem exists_factor_through_of_injective_probe (A : Type u) [CommRing A] :
    ∃ ψ' : A →ₐ[A] Localization.Away (1 : A),
      ψ' = Algebra.algHom A A (Localization.Away (1 : A)) := by
  obtain ⟨ψ', hψ'⟩ := exists_factor_through_of_injective (R := A) (A := A)
    (B := Localization.Away (1 : A)) (S := A) 1
    (AlgHom.id A (Localization.Away (1 : A))) Function.injective_id
    (Algebra.algHom A A (Localization.Away (1 : A)))
    (fun s => ⟨Algebra.algHom A A (Localization.Away (1 : A)) s, rfl⟩)
  exact ⟨ψ', by simpa using hψ'⟩

/-! ## 10. 步 ⑤ 在 `T = F[x]_P` 上的**典范映射**（源「`F[x](1/w) ⊂ F[x]_P`」✓） -/

/-- **典范映射 `A[1/w] →ₐ[A] A_P`** ✓✓（源里「`F[x₁,…,xₙ](1/w)` 落在 `F[x₁,…,xₙ]_P` 内」✓，
印版 p.185 ✓）：由 `IsLocalization.liftAlgHom` ✓ 造出 ✓（`w ∉ P` ✓ ⟹ `algebraMap A A_P w` 是单位 ✓）。
**⚠ 用途** ✓：§9 的核限制接口需要把它作为 `ι` 供给 ✓（尚缺其**单性** ✗，见文末登记 ✓）。 -/
noncomputable def awayToAtPrime {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime] (w : A)
    (hw : w ∉ P) : Localization.Away w →ₐ[A] Localization.AtPrime P :=
  IsLocalization.liftAlgHom (M := Submonoid.powers w) (S := Localization.Away w)
    (f := Algebra.algHom A A (Localization.AtPrime P)) (by
      rintro ⟨y, hy⟩
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y w).mp hy
      change IsUnit ((algebraMap A (Localization.AtPrime P)) (w ^ n))
      rw [map_pow]
      exact (IsLocalization.map_units (S := Localization.AtPrime P)
        (M := P.primeCompl) ⟨w, hw⟩).pow n)

/-- **`A` 整环时 `algebraMap A A_P` 单** ✓✓（源「取 `K := q(R)`」✓ 一节的代数前置 ✓）：
`P.primeCompl ≤ nonZeroDivisors A` ✓（`A` 整环 ✓ ⟹ `x ∉ P` ⟹ `x ≠ 0` ✓ ⟹ 非零因子 ✓）
后用 `IsLocalization.injective` ✓。 -/
theorem injective_algebraMap_atPrime {A : Type u} [CommRing A] [IsDomain A] (P : Ideal A)
    [P.IsPrime] : Function.Injective (algebraMap A (Localization.AtPrime P)) := by
  refine IsLocalization.injective (M := P.primeCompl) (Localization.AtPrime P) ?_
  intro x hx
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact P.zero_mem)
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun y hy => (eq_zero_or_eq_zero_of_mul_eq_zero hy).resolve_left hx0,
    fun y hy => (eq_zero_or_eq_zero_of_mul_eq_zero hy).resolve_right hx0⟩

/-- **`A[1/w] →ₐ[A] A_P` 单** ✓✓（**第 109 轮落地** ✓；`awayToAtPrime` 的**单性** ✓，
＝ §71.2 登记 ✗ 的卡点 ✓）：`A` 整环 ✓、`P` 素 ✓、`w ∉ P` ✓（⟹ `w ≠ 0` ✓）
⟹ 典范映射**单** ✓。
**证法** ✓（§71.2 的纲要 ✓，两条口径**均已实测更新** ✓）：
① 核内取 `z` ✓，用 `IsLocalization.Away.surj` ✓ 写 `z · (w/1)^n = a/1` ✓；
② 由 `hlift` ✓ 与 §10 下半的 `injective_algebraMap_atPrime` ✓ 得 `a = 0` ✓
⟹ `z · (w/1)^n = 0` ✓；
③ 末步用 `IsUnit.mul_left_eq_zero` ✓（`(w/1)^n` 为单位 ✓）—— **不**经过
`Units.ne_zero` ✓（该引理要 `Nontrivial` 实例 ✗，本引理**无**此要求 ✓）；
④ 一般形由核平凡化 `z - y` ✓ 还原 ✓。
**⚠ 口径更新** ✓：§71.2 的障碍 ② ✗（`Algebra.algHom` 别名目标须 `change` ✗）
**实测无需 `change`** ✓ —— `simp [awayToAtPrime]` ✓（经 `Algebra.ofId_apply` ✓
一族引理 ✓）已把目标摆正 ✓。
**非空洞** ✓（L1 ✓）：探针见下条 ✓。 -/
theorem injective_awayToAtPrime {A : Type u} [CommRing A] [IsDomain A] (P : Ideal A)
    [P.IsPrime] (w : A) (hw : w ∉ P) :
    Function.Injective (awayToAtPrime P w hw) := by
  have hlift : ∀ b : A,
      awayToAtPrime P w hw (algebraMap A (Localization.Away w) b)
        = algebraMap A (Localization.AtPrime P) b := by
    intro b
    simp [awayToAtPrime]
  have hker : ∀ z : Localization.Away w, awayToAtPrime P w hw z = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := Localization.Away w) w z
    have h2 : awayToAtPrime P w hw (algebraMap A (Localization.Away w) a) = 0 := by
      rw [← ha, map_mul, map_pow, hz, zero_mul]
    have ha0 : algebraMap A (Localization.AtPrime P) a = 0 := by
      rw [← hlift a]
      exact h2
    have ha' : a = 0 :=
      injective_algebraMap_atPrime (A := A) P (by rw [ha0, map_zero])
    rw [ha', map_zero] at ha
    exact (IsUnit.mul_left_eq_zero
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away w) w n)).mp ha
  intro z y hy
  exact sub_eq_zero.mp (hker (z - y) (by rw [map_sub, hy, sub_self]))

/-- **非空洞探针（L1）** ✓：`A = ℚ` ✓、`P = ⊥` ✓、`w = 1` ✓ 档 ✓ ——
上条的假设类（整环 ＋ 素理想 ＋ `w ∉ P`）**非空** ✓。 -/
theorem injective_awayToAtPrime_probe :
    Function.Injective (awayToAtPrime (⊥ : Ideal ℚ) (1 : ℚ) (by simp)) :=
  injective_awayToAtPrime _ _ _

/-! ## 11. 最后组装（源 `thm3.9` 的 **(ii)⟹(i)** ✓，印版 p.185 尾段 ✓）

**源逐字** ✓（`pdftoppm` 按页核 ✓，**PDF 页 21 ＝ 印版 185** ✓）：反方向取
`η₀ : F[x] ↠ R(1/r)` ✓（`P = ker η₀` ✓、`T = F[x]_P` ✓）→ §7 得 `ψ : S → T` ✓ →
§8 的公共分母得 `ψ(S) ⊂ F[x](1/w)`（`w ∉ P` ✓）→ §9 把该包含**兑现**为穿过 `A[1/w]` 的 `ψ'` ✓ →
「Also, `η` yields a surjection `η : F[x₁,…,xₙ](1/w) → R(1/rv)` **where `v = η(w)`**」✓ →
「In all, `φ : S → R(1/rv)` is the composition of `ψ` and `η`」✓。

**本节七件** ✓：
① `awayToAwayOfDvd` ✓（「局部化的局部化」✓：`a ∣ b` ⟹ `R(1/a) → R(1/b)` ✓）；
② `localizedEta` ✓（**`η`** ✓：取 `r' := r₀·c` ✓，`c` 由 `IsLocalization.Away.surj` ✓ 给
`η₀ w · (r₀/1)^n = c/1` ✓ 定出 ✓ —— 即印版的 `v = η(w)` ✓）；
③ `residueFieldMap` ✓（**`K'`** ✓：映到**域档** `𝔨(P) := Ideal.ResidueField P` ✓）；
④ 两条识别 ✓（`K' ∘ σ = residueMapOfSurjective` ✓；`K' ∘ η = residue ∘ ι` ✓，
其代数内核是 `residue (algebraMap A A_P a) = algebraMap A 𝔨(P) a` ✓）；
⑤ `injective_residueFieldMap` ✓（**`K'` 单** ✓）；⑥ `finiteType_away_of_field` ✓（L1 探针用 ✓）；
⑦ `factorsRationally_of_hasLocalLifting` ✓（**收口** ＝ `FactorsRationally` ✓）。
**⚠ 结构读数** ✓：`R(1/r') → R(1/r₀)` **不存在** ✗（`c` 在 `R(1/r₀)` 里未必可逆 ✗）
⟹「映回小局部化」的路 **不通** ✗，故 ④⑤ 必须走**域档 `𝔨(P)`** ✓。 -/

/-- **工具** ✓：`A_P` 的剩余域里 `residue ∘ algebraMap = algebraMap A 𝔨(P)` ✓
（`IsLocalRing.ResidueField.algebraMap_eq` ✓ ＋ `IsScalarTower.algebraMap_apply` ✓）。
**⚠ 意义** ✓：这是源「`T/M = K`」✓ 在 `A` 上的**计算形** ✓。 -/
theorem residue_algebraMap_eq_algebraMap {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime]
    (a : A) : IsLocalRing.residue (Localization.AtPrime P) (algebraMap A (Localization.AtPrime P) a)
      = algebraMap A (Ideal.ResidueField P) a := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq (Localization.AtPrime P)]
  exact (IsScalarTower.algebraMap_apply A (Localization.AtPrime P) (Ideal.ResidueField P) a).symm

/-- **件 ①「局部化的局部化」** ✓✓：`a ∣ b` ⟹ 典范 `R(1/a) →ₐ[F] R(1/b)` ✓
（`IsLocalization.Away.liftAlgHom` ✓ ＋ `IsLocalization.Away.isUnit_of_dvd` ✓）。
**⚠ 用途** ✓：把 `η₀` 从 `R(1/r₀)` 推到 `R(1/(r₀·c))` ✓ —— 源里「`R(1/rv)`」✓ 的实体 ✓。 -/
noncomputable def awayToAwayOfDvd {F R : Type u} [Field F] [CommRing R] [Algebra F R]
    {a b : R} (h : a ∣ b) : Localization.Away a →ₐ[F] Localization.Away b :=
  IsLocalization.Away.liftAlgHom (x := a) (f := Algebra.algHom F R (Localization.Away b))
    (show IsUnit ((Algebra.algHom F R (Localization.Away b)) a) from
      IsLocalization.Away.isUnit_of_dvd (S := Localization.Away b) (x := b) h)

theorem awayToAwayOfDvd_algebraMap {F R : Type u} [Field F] [CommRing R] [Algebra F R]
    {a b : R} (h : a ∣ b) (x : R) :
    awayToAwayOfDvd (F := F) h (algebraMap R (Localization.Away a) x)
      = algebraMap R (Localization.Away b) x := by
  rw [awayToAwayOfDvd, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (x := a) _ x]
  rfl

/-- **件 ② 的单位性输入** ✓✓：`(σ ∘ η₀) w` 是单位 ✓ —— 因
`η₀ w · (r₀/1)^n = c/1` ✓ 而 `c` 与 `r₀/1` 在 `R(1/(r₀·c))` 里**都被倒过来** ✓。
**⚠ 口径** ✓：末步**不**用 `Units.ne_zero` ✗（要 `Nontrivial` 实例 ✗）⟹
用 `IsUnit.mul_left_eq_zero` ✓ ＋ `IsUnit.ringInverse` ✓。 -/
theorem isUnit_comp_eta0_at_w {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    {c : R} {w : MvPolynomial (Fin m) F} {n : ℕ}
    (hsurj : η₀ w * (algebraMap R (Localization.Away r₀) r₀) ^ n
      = algebraMap R (Localization.Away r₀) c) :
    IsUnit ((awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩).comp η₀ w) := by
  have hσ : ∀ x : R,
      awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩
          (algebraMap R (Localization.Away r₀) x)
        = algebraMap R (Localization.Away (r₀ * c)) x :=
    fun x => awayToAwayOfDvd_algebraMap (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩ x
  have hkey : awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩ (η₀ w)
      * (awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩
          (algebraMap R (Localization.Away r₀) r₀)) ^ n
      = algebraMap R (Localization.Away (r₀ * c)) c := by
    have h0 := congrArg (awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩) hsurj
    simpa only [map_mul, map_pow, hσ] using h0
  have hcunit : IsUnit (algebraMap R (Localization.Away (r₀ * c)) c) :=
    IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (r₀ * c)) (x := r₀ * c)
      (dvd_mul_left c r₀)
  have huσ : IsUnit (awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩
      (algebraMap R (Localization.Away r₀) r₀)) := by
    rw [hσ r₀]
    exact IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (r₀ * c)) (x := r₀ * c)
      (dvd_mul_right r₀ c)
  have hx : awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩ (η₀ w)
      = algebraMap R (Localization.Away (r₀ * c)) c
        * ((awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩
            (algebraMap R (Localization.Away r₀) r₀)) ^ n)⁻¹ʳ := by
    rw [← hkey, mul_assoc, Ring.mul_inverse_cancel _ ((huσ.pow n)), mul_one]
  rw [AlgHom.comp_apply, hx]
  exact IsUnit.mul hcunit ((huσ.pow n).ringInverse)

/-- **工具** ✓：`algebraMap R (R(1/r))` **单** ✓（`R` 整环、`r ≠ 0` ✓）——
`Submonoid.powers r ≤ nonZeroDivisors R` ✓（`r ≠ 0` ✓ ⟹ `r^n ≠ 0` ✓）。 -/
theorem injective_algebraMap_away {R : Type u} [CommRing R] [IsDomain R] {r : R} (hr : r ≠ 0) :
    Function.Injective (algebraMap R (Localization.Away r)) := by
  refine IsLocalization.injective (M := Submonoid.powers r) (Localization.Away r) ?_
  intro x hx
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x r).mp hx
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun y hy => (eq_zero_or_eq_zero_of_mul_eq_zero hy).resolve_left (pow_ne_zero n hr),
    fun y hy => (eq_zero_or_eq_zero_of_mul_eq_zero hy).resolve_right (pow_ne_zero n hr)⟩

/-- **工具** ✓：`residueMapOfSurjective η₀ hη₀` **单** ✓（它是「商同构 ＋ `A⧸P → 𝔨(P)`」的复合 ✓，
而后者由 `Ideal.injective_algebraMap_quotient_residueField` ✓ 单 ✓）。 -/
theorem injective_residueMapOfSurjective {F R' : Type u} [Field F] [CommRing R']
    [Algebra F R'] {m : ℕ} (η₀ : MvPolynomial (Fin m) F →ₐ[F] R')
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] :
    Function.Injective (residueMapOfSurjective (F := F) η₀ hη₀) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  change algebraMap (MvPolynomial (Fin m) F ⧸ RingHom.ker η₀)
      (Ideal.ResidueField (RingHom.ker η₀))
      ((Ideal.quotientKerAlgEquivOfSurjective hη₀).symm x) = 0 at hx
  have h0 : (Ideal.quotientKerAlgEquivOfSurjective hη₀).symm x = 0 :=
    Ideal.injective_algebraMap_quotient_residueField (I := RingHom.ker η₀)
      (R := MvPolynomial (Fin m) F) (by rw [hx, map_zero])
  simpa using h0

/-- **工具** ✓：`K'` 的**输入映射** `R →ₐ[F] 𝔨(P)` **单** ✓（＝
`residueMapOfSurjective ∘ algebraMap R (R(1/r₀))` ✓，两条都单 ✓）。 -/
theorem injective_residueFieldMap_input {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (hr₀ : r₀ ≠ 0)
    (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] :
    Function.Injective ((residueMapOfSurjective (F := F) η₀ hη₀).comp
      (Algebra.algHom F R (Localization.Away r₀))) := by
  have h2 : Function.Injective ((residueMapOfSurjective (F := F) η₀ hη₀)
      ∘ (algebraMap R (Localization.Away r₀))) :=
    (injective_residueMapOfSurjective (F := F) η₀ hη₀).comp
      (injective_algebraMap_away (R := R) hr₀)
  intro x y hxy
  exact h2 hxy

/-- **件 ② 成品「`η`」** ✓✓✓：`η : F[x](1/w) →ₐ[F] R(1/(r₀·c))` ✓ ——
由 `IsLocalization.Away.liftAlgHom` ✓ 下降 `σ ∘ η₀` ✓（单位性见上条 ✓）。
**⚠ 形态** ✓：`c` 是 `η₀ w` 在 `R(1/r₀)` 里的**分子** ✓ ⟹ 目标 `R(1/(r₀·c))` 正是
印版的 **`R(1/rv)`**（`v = η(w)` ✓）✓。 -/
noncomputable def localizedEta {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    {c : R} {w : MvPolynomial (Fin m) F} {n : ℕ}
    (hsurj : η₀ w * (algebraMap R (Localization.Away r₀) r₀) ^ n
      = algebraMap R (Localization.Away r₀) c) :
    Localization.Away w →ₐ[F] Localization.Away (r₀ * c) :=
  IsLocalization.Away.liftAlgHom (x := w)
    (f := (awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩).comp η₀)
    (isUnit_comp_eta0_at_w (F := F) η₀ hsurj)

theorem localizedEta_algebraMap {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    {c : R} {w : MvPolynomial (Fin m) F} {n : ℕ}
    (hsurj : η₀ w * (algebraMap R (Localization.Away r₀) r₀) ^ n
      = algebraMap R (Localization.Away r₀) c)
    (p : MvPolynomial (Fin m) F) :
    localizedEta (F := F) η₀ hsurj
        (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) p)
      = awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩ (η₀ p) := by
  rw [localizedEta, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (x := w) _ p]
  rfl

/-- **件 ③ 成品「`K'`」** ✓✓✓：`K' : R(1/(r₀·c)) →ₐ[F] 𝔨(P)`（`P = ker η₀` ✓）——
**域档** ✓（源「`T/M = K`」✓ 的实体 ✓）：由 `IsLocalization.Away.liftAlgHom` ✓ 下降
`k := residueMapOfSurjective η₀ hη₀ ∘ algebraMap R (R(1/r₀))` ✓。
**⚠ 单位性** ✓：`k (r₀·c) ≠ 0` ✓（`k` 单 ✓ ＋ `r₀·c ≠ 0` ✓）⟹ 域中为单位 ✓。 -/
noncomputable def residueFieldMap {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (hr₀ : r₀ ≠ 0)
    (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] {c : R} (hc : c ≠ 0) :
    Localization.Away (r₀ * c) →ₐ[F] Ideal.ResidueField (RingHom.ker η₀) :=
  IsLocalization.Away.liftAlgHom (x := r₀ * c)
    (f := (residueMapOfSurjective (F := F) η₀ hη₀).comp (Algebra.algHom F R (Localization.Away r₀)))
    (show IsUnit (((residueMapOfSurjective (F := F) η₀ hη₀).comp
        (Algebra.algHom F R (Localization.Away r₀))) (r₀ * c)) from
      isUnit_iff_ne_zero.mpr (fun hzero => mul_ne_zero hr₀ hc
        (injective_residueFieldMap_input (F := F) hr₀ η₀ hη₀ (by rw [hzero, map_zero]))))

theorem residueFieldMap_algebraMap {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (hr₀ : r₀ ≠ 0)
    (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] {c : R} (hc : c ≠ 0) (x : R) :
    residueFieldMap (F := F) hr₀ η₀ hη₀ hc (algebraMap R (Localization.Away (r₀ * c)) x)
      = (residueMapOfSurjective (F := F) η₀ hη₀) (algebraMap R (Localization.Away r₀) x) := by
  rw [residueFieldMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (x := r₀ * c) _ x]
  rfl

/-- **件 ④ 识别之一** ✓✓：`K' ∘ σ = residueMapOfSurjective η₀ hη₀` ✓
（两条 `R(1/r₀) →ₐ[F] 𝔨(P)` 在 `R` 上一致 ✓ ⟹ `IsLocalization.algHom_ext` ✓）。 -/
theorem residueFieldMap_comp_awayToAway {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (hr₀ : r₀ ≠ 0)
    (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] {c : R} (hc : c ≠ 0) :
    (residueFieldMap (F := F) hr₀ η₀ hη₀ hc).comp
        (awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩)
      = residueMapOfSurjective (F := F) η₀ hη₀ := by
  refine IsLocalization.algHom_ext (A := R) (W := Submonoid.powers r₀) ?_
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply]
  rw [show (Algebra.algHom F R (Localization.Away r₀)) x
      = algebraMap R (Localization.Away r₀) x from rfl]
  rw [awayToAwayOfDvd_algebraMap (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩ x]
  rw [residueFieldMap_algebraMap (F := F) hr₀ η₀ hη₀ hc x]

/-- **工具** ✓：`residueMapOfSurjective (η₀ p)` 与 `algebraMap A 𝔨(P) p` 一致 ✓
（商同构在 `mk p` 上的取值 ✓ ＋ `Ideal.algebraMap_quotient_residueField_mk` ✓）。 -/
theorem residueMap_eta0_eq_algebraMap {F R' : Type u} [Field F] [CommRing R']
    [Algebra F R'] {m : ℕ} (η₀ : MvPolynomial (Fin m) F →ₐ[F] R')
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime]
    (p : MvPolynomial (Fin m) F) :
    (residueMapOfSurjective (F := F) η₀ hη₀) (η₀ p)
      = algebraMap (MvPolynomial (Fin m) F) (Ideal.ResidueField (RingHom.ker η₀)) p := by
  change (Algebra.algHom F (MvPolynomial (Fin m) F ⧸ RingHom.ker η₀)
      (Ideal.ResidueField (RingHom.ker η₀)))
    ((Ideal.quotientKerAlgEquivOfSurjective hη₀).symm (η₀ p)) = _
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  change algebraMap (MvPolynomial (Fin m) F ⧸ RingHom.ker η₀)
      (Ideal.ResidueField (RingHom.ker η₀)) (Ideal.Quotient.mk (RingHom.ker η₀) p)
    = algebraMap (MvPolynomial (Fin m) F) (Ideal.ResidueField (RingHom.ker η₀)) p
  exact (Ideal.algebraMap_quotient_residueField_mk (I := RingHom.ker η₀) p).symm

/-- **工具** ✓：`residue ∘ ι ∘ algebraMap A` ＝ `algebraMap A 𝔨(P)` ✓ —— 即源
「`η extends to the map `η : T → K`」✓ 在 `A` 上的计算形 ✓。 -/
theorem residue_algebraMap_awayToAtPrime {F A : Type u} [Field F] [CommRing A]
    [Algebra F A] (P : Ideal A) [P.IsPrime] (w : A) (hw : w ∉ P) (p : A) :
    (Algebra.algHom F (Localization.AtPrime P) (Ideal.ResidueField P))
        (awayToAtPrime P w hw (algebraMap A (Localization.Away w) p))
      = algebraMap A (Ideal.ResidueField P) p := by
  rw [show awayToAtPrime P w hw (algebraMap A (Localization.Away w) p)
      = algebraMap A (Localization.AtPrime P) p from by simp [awayToAtPrime]]
  change IsLocalRing.residue (Localization.AtPrime P) (algebraMap A (Localization.AtPrime P) p) = _
  exact residue_algebraMap_eq_algebraMap P p

/-- **件 ④ 识别之二** ✓✓✓：`K' ∘ η = residue ∘ ι` ✓ —— 源「`η ∘ ψ = i ∘ φ`」✓ 的实体 ✓。
**证法** ✓：`IsLocalization.algHom_ext (powers w)` ✓，两条在 `A` 上分别落到
`residueMapOfSurjective (η₀ p)` ✓ 与 `residue (algebraMap A A_P p)` ✓，
再由 `residueMap_eta0_eq_algebraMap` ✓ 与 `residue_algebraMap_awayToAtPrime` ✓ 收口 ✓。
**⚠ 载体** ✓：`ι = awayToAtPrime` 是 **`A`-代数**同态 ✓，须经 `AlgHom.restrictScalars F` ✓
方与 `F`-代数侧的 `K' ∘ η` 同台 ✓（实测需 `AlgHom.restrictScalars_apply` ✓ 摆正 ✓）。 -/
theorem residueFieldMap_comp_localizedEta {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (hr₀ : r₀ ≠ 0)
    (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] {c : R} (hc : c ≠ 0)
    {w : MvPolynomial (Fin m) F} {n : ℕ}
    (hsurj : η₀ w * (algebraMap R (Localization.Away r₀) r₀) ^ n
      = algebraMap R (Localization.Away r₀) c)
    (hw : w ∉ RingHom.ker η₀) :
    (residueFieldMap (F := F) hr₀ η₀ hη₀ hc).comp (localizedEta (F := F) η₀ hsurj)
      = (Algebra.algHom F (Localization.AtPrime (RingHom.ker η₀))
          (Ideal.ResidueField (RingHom.ker η₀))).comp
        ((awayToAtPrime (RingHom.ker η₀) w hw).restrictScalars F) := by
  refine IsLocalization.algHom_ext (A := MvPolynomial (Fin m) F) (W := Submonoid.powers w) ?_
  refine AlgHom.ext fun p => ?_
  simp only [AlgHom.comp_apply]
  rw [show (Algebra.algHom F (MvPolynomial (Fin m) F) (Localization.Away w)) p
      = algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) p from rfl]
  rw [localizedEta_algebraMap (F := F) η₀ hsurj p]
  rw [show residueFieldMap (F := F) hr₀ η₀ hη₀ hc
        (awayToAwayOfDvd (F := F) (a := r₀) (b := r₀ * c) ⟨c, rfl⟩ (η₀ p))
      = (residueMapOfSurjective (F := F) η₀ hη₀) (η₀ p)
      from congrArg (fun f => f (η₀ p))
        (residueFieldMap_comp_awayToAway (F := F) hr₀ η₀ hη₀ hc)]
  rw [residueMap_eta0_eq_algebraMap (F := F) η₀ hη₀ p]
  rw [AlgHom.restrictScalars_apply]
  rw [residue_algebraMap_awayToAtPrime (F := F) (RingHom.ker η₀) w hw p]

/-- **件 ⑤「`K'` 单」** ✓✓✓：由输入映射单 ✓ 与 `IsLocalization.injective_iff_map_algebraMap_eq` ✓。 -/
theorem injective_residueFieldMap {F R : Type u} [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] {m : ℕ} {r₀ : R} (hr₀ : r₀ ≠ 0)
    (η₀ : MvPolynomial (Fin m) F →ₐ[F] Localization.Away r₀)
    (hη₀ : Function.Surjective η₀) [(RingHom.ker η₀).IsPrime] {c : R} (hc : c ≠ 0) :
    Function.Injective (residueFieldMap (F := F) hr₀ η₀ hη₀ hc) := by
  refine (IsLocalization.injective_iff_map_algebraMap_eq (M := Submonoid.powers (r₀ * c))
    (f := (residueFieldMap (F := F) hr₀ η₀ hη₀ hc).toRingHom)).mpr ?_
  intro x y
  rw [show (residueFieldMap (F := F) hr₀ η₀ hη₀ hc).toRingHom
        (algebraMap R (Localization.Away (r₀ * c)) x)
      = (residueMapOfSurjective (F := F) η₀ hη₀) (algebraMap R (Localization.Away r₀) x)
      from residueFieldMap_algebraMap (F := F) hr₀ η₀ hη₀ hc x]
  rw [show (residueFieldMap (F := F) hr₀ η₀ hη₀ hc).toRingHom
        (algebraMap R (Localization.Away (r₀ * c)) y)
      = (residueMapOfSurjective (F := F) η₀ hη₀) (algebraMap R (Localization.Away r₀) y)
      from residueFieldMap_algebraMap (F := F) hr₀ η₀ hη₀ hc y]
  constructor
  · intro h
    rw [injective_algebraMap_away (R := R) (mul_ne_zero hr₀ hc) h]
  · intro h
    rw [injective_residueFieldMap_input (F := F) hr₀ η₀ hη₀ h]

/-- **工具（L1 探针用）** ✓：`F` 是域、`r ≠ 0` ⟹ `F(1/r)` 是**有限型** `F`-代数 ✓
（`r` 为单位 ✓ ⟹ `algebraMap F F(1/r)` **满** ✓ ⟹ `Algebra.FiniteType.of_surjective` ✓）。 -/
theorem finiteType_away_of_field {F : Type u} [Field F] (r : F) (hr : r ≠ 0) :
    Algebra.FiniteType F (Localization.Away r) := by
  refine Algebra.FiniteType.of_surjective (Algebra.algHom F F (Localization.Away r)) ?_
  intro y
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := Localization.Away r) r y
  refine ⟨a * (r⁻¹) ^ n, ?_⟩
  rw [map_mul, map_pow]
  have hbc : algebraMap F (Localization.Away r) r * algebraMap F (Localization.Away r) r⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hr, map_one]
  have hpow : (algebraMap F (Localization.Away r) r) ^ n
      * (algebraMap F (Localization.Away r) r⁻¹) ^ n = 1 := by
    rw [← mul_pow, hbc, one_pow]
  change algebraMap F (Localization.Away r) a
      * (algebraMap F (Localization.Away r) r⁻¹) ^ n = y
  rw [← ha, mul_assoc, hpow, mul_one]

set_option linter.style.haveILetI false in
/-- **件 ⑦ ＝ `thm3.9` 的 (ii)⟹(i)（反方向）** ✓✓✓✓：`HasLocalLifting` ⟹ `FactorsRationally` ✓。
**证法** ✓（§72.4 的六件 ✓，逐步对应源印版 p.185 ✓）：
取 `r₀` ✓（`HasLocalLifting` 的见证 ✓）＋ 仿射满射 `η₀ : F[x] ↠ R(1/r₀)` ✓（`hRaff` ✓）
＋ `P := ker η₀` ✓（`R(1/r₀)` 是整环 ✓ ⟹ `P` 素 ✓）→ §7 得 `ψ : S → T = F[x]_P` ✓ →
`S` 仿射 ✓ ⟹ 生成元集 `sf` ✓ ⟹ §8 给公共分母 `w ∉ P` ✓ ⟹ §9 得 `ψ'` ✓ →
`c, n` ✓ 由 `Away.surj` ✓ → `η := localizedEta` ✓、`K' := residueFieldMap` ✓ →
两端映 `K'` ✓ 后用 `hψ` ✓ 与 §11 的两条识别 ✓ 得同一个值 ✓ ⟹ `K'` 单 ✓ ⟹ 收口 ✓。
**⚠ 假设口径** ✓：`Algebra.FiniteType F S` ✓ 与 `∀ r ≠ 0, Algebra.FiniteType F (R(1/r))` ✓
**两件都须显式** ✓（§68 的印版级发现 ✓：源 `thm3.9` 的**陈述**未写仿射性 ✓，
而其**证明**两处都用到 ✓）。
**非空洞** ✓（L1 ✓）：探针见下条 ✓。 -/
theorem factorsRationally_of_hasLocalLifting {F S R : Type u} [Field F]
    [CommRing S] [IsDomain S] [Algebra F S] [CommRing R] [IsDomain R] [Algebra F R]
    (φ : S →ₐ[F] R) (hS : Algebra.FiniteType F S) (hφ : HasLocalLifting F S R φ)
    (hRaff : ∀ r : R, r ≠ 0 → Algebra.FiniteType F (Localization.Away r)) :
    FactorsRationally F S R φ := by
  classical
  obtain ⟨r₀, hr₀, H⟩ := hφ
  obtain ⟨r₀, hr₀, Hlift⟩ := exists_lift_to_atPrime_of_hasLocalLifting (F := F) (φ := φ)
    (show HasLocalLifting F S R φ from ⟨r₀, hr₀, H⟩)
  obtain ⟨m, η₀, hη₀⟩ := exists_surjective_mvPolynomial_of_finiteType (F := F) (hRaff r₀ hr₀)
  haveI : IsDomain (Localization.Away r₀) := isDomain_localization_away (R := R) hr₀
  haveI hP : (RingHom.ker η₀).IsPrime := RingHom.ker_isPrime η₀
  obtain ⟨ψ, hψ⟩ := Hlift η₀ hη₀
  obtain ⟨sf, hsf⟩ := hS.out
  obtain ⟨m₀, hm₀⟩ := exists_mem_localization_ge_adjoin (A := MvPolynomial (Fin m) F)
    (B := Localization.AtPrime (RingHom.ker η₀)) (M := (RingHom.ker η₀).primeCompl) (sf.image ψ)
  let w : MvPolynomial (Fin m) F := (m₀ : MvPolynomial (Fin m) F)
  have hwP : w ∉ RingHom.ker η₀ := m₀.2
  have hw0 : w ≠ 0 := fun h => hwP (by rw [h]; exact (RingHom.mem_ker).mpr (map_zero η₀))
  have hι : ∀ p : MvPolynomial (Fin m) F,
      awayToAtPrime (RingHom.ker η₀) w hwP
          (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) p)
        = algebraMap (MvPolynomial (Fin m) F) (Localization.AtPrime (RingHom.ker η₀)) p := by
    intro p
    simp [awayToAtPrime]
  have hinv : awayToAtPrime (RingHom.ker η₀) w hwP (IsLocalization.Away.invSelf w)
      * algebraMap (MvPolynomial (Fin m) F) (Localization.AtPrime (RingHom.ker η₀)) w = 1 := by
    rw [← hι w, ← map_mul, mul_comm (IsLocalization.Away.invSelf w),
      IsLocalization.Away.mul_invSelf, map_one]
  have hmem_range : ∀ y : Localization.AtPrime (RingHom.ker η₀),
      (∃ (a : MvPolynomial (Fin m) F) (k : ℕ),
        y * (algebraMap (MvPolynomial (Fin m) F) (Localization.AtPrime (RingHom.ker η₀)) w) ^ k
          = algebraMap (MvPolynomial (Fin m) F) (Localization.AtPrime (RingHom.ker η₀)) a)
      → y ∈ ((awayToAtPrime (RingHom.ker η₀) w hwP).restrictScalars F).range := by
    intro y hy
    obtain ⟨a, k, hk⟩ := hy
    have huv : (algebraMap (MvPolynomial (Fin m) F) (Localization.AtPrime (RingHom.ker η₀)) w) ^ k
        * (awayToAtPrime (RingHom.ker η₀) w hwP (IsLocalization.Away.invSelf w)) ^ k = 1 := by
      rw [← mul_pow, mul_comm, hinv, one_pow]
    refine ⟨algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) a
      * (IsLocalization.Away.invSelf w) ^ k, ?_⟩
    show awayToAtPrime (RingHom.ker η₀) w hwP
      (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) a
        * (IsLocalization.Away.invSelf w) ^ k) = y
    rw [map_mul, map_pow, hι a]
    rw [← hk, mul_assoc, huv, mul_one]
  have hgen : ∀ t ∈ sf, ψ t ∈ ((awayToAtPrime (RingHom.ker η₀) w hwP).restrictScalars F).range := by
    intro t ht
    have hmem : ψ t ∈ (sf.image ψ : Set (Localization.AtPrime (RingHom.ker η₀))) :=
      Finset.mem_image.mpr ⟨t, ht, rfl⟩
    exact hmem_range (ψ t) (hm₀ (ψ t) (Algebra.subset_adjoin hmem))
  have hrange : ∀ s : S, ψ s ∈ ((awayToAtPrime (RingHom.ker η₀) w hwP).restrictScalars F).range := by
    intro s
    have hle : (⊤ : Subalgebra F S)
        ≤ (((awayToAtPrime (RingHom.ker η₀) w hwP).restrictScalars F).range).comap ψ := by
      rw [← hsf]
      exact Algebra.adjoin_le (fun t ht => hgen t ht)
    exact (Subalgebra.mem_comap _ ψ s).mp (hle Algebra.mem_top)
  obtain ⟨ψ', hψ'⟩ := exists_factor_through_of_injective (R := F) (A := MvPolynomial (Fin m) F) w
    ((awayToAtPrime (RingHom.ker η₀) w hwP).restrictScalars F)
    (injective_awayToAtPrime (RingHom.ker η₀) w hwP) ψ hrange
  obtain ⟨n, c, hsurj⟩ := IsLocalization.Away.surj (S := Localization.Away r₀) r₀ (η₀ w)
  have hηw : η₀ w ≠ 0 := fun h => hwP h
  have hc0 : algebraMap R (Localization.Away r₀) c ≠ 0 := by
    intro h0
    exact hηw ((IsUnit.mul_left_eq_zero
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away r₀) (x := r₀) n)).mp
        (by rw [hsurj, h0]))
  have hc : c ≠ 0 := fun h0 => hc0 (by rw [h0, map_zero])
  refine ⟨m, w, hw0, r₀ * c, mul_ne_zero hr₀ hc,
    ψ', localizedEta (F := F) η₀ hsurj, ?_⟩
  intro s
  refine injective_residueFieldMap (F := F) hr₀ η₀ hη₀ hc ?_
  rw [residueFieldMap_algebraMap (F := F) hr₀ η₀ hη₀ hc (φ s)]
  rw [← hψ s]
  rw [show residueFieldMap (F := F) hr₀ η₀ hη₀ hc
        (localizedEta (F := F) η₀ hsurj (ψ' s))
      = (Algebra.algHom F (Localization.AtPrime (RingHom.ker η₀))
          (Ideal.ResidueField (RingHom.ker η₀)))
          (awayToAtPrime (RingHom.ker η₀) w hwP (ψ' s))
      from congrArg (fun f => f (ψ' s))
        (residueFieldMap_comp_localizedEta (F := F) hr₀ η₀ hη₀ hc hsurj hwP)]
  rw [show awayToAtPrime (RingHom.ker η₀) w hwP (ψ' s) = ψ s
      from congrArg (fun f => f s) hψ']
  rfl

/-- **非空洞探针（L1）** ✓✅：`F = S = R = ℚ`、`φ = AlgHom.id` 档 ✓ ——
三件假设**同时可满足** ✓（`Algebra.FiniteType ℚ ℚ` ✓ ／ `hasLocalLifting_id_data_nonempty` ✓ ／
`finiteType_away_of_field` ✓），且**结论真的被本条推出** ✓ ⟹
假设类**非空** ✓、结论**非空洞** ✓。 -/
theorem factorsRationally_of_hasLocalLifting_probe :
    FactorsRationally ℚ ℚ ℚ (AlgHom.id ℚ ℚ) :=
  factorsRationally_of_hasLocalLifting (F := ℚ) (AlgHom.id ℚ ℚ) inferInstance
    (hasLocalLifting_id_data_nonempty ℚ) (fun r hr => finiteType_away_of_field r hr)

/-! ## 12. 登记 -/

/-- **登记** ✗（**源陈述缺假设** ✓✓，**印版级已核** ✓；L39 家族 ✓）：源 `thm3.9` 的**陈述**
（**印版 p.184** ✓，逐字）只说「Let `φ : S → R` be an `F` algebra map between `F` algebra
**domains**」✗ —— **未**列**仿射性** ✗；而其**证明**（**印版 p.185** ✓，逐字）两处**都用到** ✓：
「**Since `R(1/r)` is affine**, there is an `F` algebra surjection `η : F[x₁,…,xₙ] → R(1/r)`」✓、
「**Since `S` is affine**, `ψ(S) ⊂ F[x₁,…,xₙ](1/w)` for some `w ∉ P`」✓。
**对照** ✓：同页上方的 `thm3.8` 的陈述**明写**「an **affine** `F` algebra `S`」✓ ⟹
`thm3.9` 的省略是**陈述层面**的 ✓，非术语约定 ✗。
**形式化侧结论** ✓：本工程的反方向**目标形**须**显式**带 `Algebra.FiniteType F S` ✓ 与
`Algebra.FiniteType F (Localization.Away r)` ✓（§4 的仿射层即其前置 ✓）。

**⚠ 本轮细化（第 105 轮 ✓，**同族第二发现** ✓）**：**`R` 仿射推不出 `R(1/r)` 仿射** ✗ ——
实测 ✓：源证法里「`R(1/r)` 是仿射」**不能**由 §4 的满射复合得到 ✗（局部化映射 `R → R(1/r)`
**一般不是满射** ✗）；标准反例 ✓：`R = F[x]`、`r = x` 时 `R(1/r) = F[x,1/x]` **不是**有限生成
`F`-代数 ✗（**⚠ 该反例尚未在库内形式化** ✗，故本条**不作承重** ✓，仅作**目标形**的依据 ✓）。
⟹ 反方向的目标形须**另带** `Algebra.FiniteType F (Localization.Away r)` ✓（而**非**由 `R` 仿射导出 ✗）。
**⚠ 优先级** ✓：该发现与蓝图 §3.3 T3 的「源仅设 `q(S₁)=K` 而证明需 `q(S₂)=K`」**同型** ✓
（`deadend`／勘误候选 ✓）。 -/
theorem thm39_affineness_finding_registered : True := trivial

/-- **登记** ✗：本层**余下一件** ✓（须按 §47／§52 同法先作**来源核验** ✓）：

① **`thm3.9` 的反方向**（(ii)⟹(i) ✓，印版 p.185 ✓）：**✅✅✅ 已落** ✓✓（**第 110 轮** ✓，§11 ✓：
`factorsRationally_of_hasLocalLifting` ✓）。**沿途各段的落点** ✓：**设置** ✓（§7 ✓：
`η₀` ✓／`P = ker η₀` ✓／`T = F[x]_P` ✓／残差映射 ✓／**`ψ : S → T` 取自 `HasLocalLifting`** ✓）；
**步 ⑤ 工具与接口** ✓（§8 ✓／§9 ✓：公共分母 ✓／兑现为穿过 `A[1/w]` ✓）；
**单性** ✓（§10 末 ✓：`injective_awayToAtPrime` ✓，第 109 轮 ✓）；
**最后组装** ✓（§11 ✓：`awayToAwayOfDvd` ✓／`localizedEta` ✓／`residueFieldMap` ✓／
两条识别 ✓／`injective_residueFieldMap` ✓）。
**⚠ 假设口径** ✓：目标形**显式**带 `Algebra.FiniteType F S` ✓ 与
`∀ r ≠ 0, Algebra.FiniteType F (R(1/r))` ✓（**非**由 `R` 仿射导出 ✗，见上条 ✓）。

② **`thm3.8`** ✓（印版 p.184 ✓）：需 ① 的**双向** ✓（**已有** ✓）＋ `lem3.5` ✓
（`SaltCor_ABGV52.lem3_5` ✓ 已有 ✓）⟹ **下一轮** ✓。

**⚠ 与 M3 其余件的关系** ✓：`cor3.10(a)` ✓（印版 p.186 ✓）需要**局部投射对象** ✓ ＋
**densely representing** ✓ ＋ 本件的**双向** ✓ ⟹ 亦在 ① 之后 ✓。 -/
theorem thm39_gap_registered : True := trivial

/-! ## 公理闸门 -/

#print axioms isUnit_of_isUnit_residue
#print axioms HasLocalLifting
#print axioms hasLocalLifting_typeLock
#print axioms hasLocalLifting_id_data_nonempty
#print axioms hasLocalLifting_of_factorsRationally
#print axioms exists_surjective_mvPolynomial_of_finiteType
#print axioms finiteType_of_surjective_mvPolynomial
#print axioms exists_surjective_mvPolynomial_with_prime_ker
#print axioms quotient_ker_algEquiv_of_surjective
#print axioms residue_injective_of_field
#print axioms exists_lift_to_field_of_hasLocalLifting
#print axioms isLocalRing_localization_atPrime
#print axioms isFractionRing_residueField_atPrime
#print axioms isDomain_localization_away
#print axioms residueMapOfSurjective
#print axioms exists_lift_to_atPrime_of_hasLocalLifting
#print axioms exists_mem_localization_ge_finset
#print axioms exists_mem_localization_ge_adjoin
#print axioms exists_mem_primeCompl_of_finset
#print axioms exists_factor_through_of_injective
#print axioms exists_factor_through_of_injective_probe
#print axioms awayToAtPrime
#print axioms injective_algebraMap_atPrime
#print axioms injective_awayToAtPrime
#print axioms injective_awayToAtPrime_probe
#print axioms residue_algebraMap_eq_algebraMap
#print axioms awayToAwayOfDvd
#print axioms awayToAwayOfDvd_algebraMap
#print axioms isUnit_comp_eta0_at_w
#print axioms injective_algebraMap_away
#print axioms injective_residueMapOfSurjective
#print axioms injective_residueFieldMap_input
#print axioms localizedEta
#print axioms localizedEta_algebraMap
#print axioms residueFieldMap
#print axioms residueFieldMap_algebraMap
#print axioms residueFieldMap_comp_awayToAway
#print axioms residueMap_eta0_eq_algebraMap
#print axioms residue_algebraMap_awayToAtPrime
#print axioms residueFieldMap_comp_localizedEta
#print axioms injective_residueFieldMap
#print axioms finiteType_away_of_field
#print axioms factorsRationally_of_hasLocalLifting
#print axioms factorsRationally_of_hasLocalLifting_probe
#print axioms thm39_affineness_finding_registered
#print axioms thm39_gap_registered

end ABGV52
