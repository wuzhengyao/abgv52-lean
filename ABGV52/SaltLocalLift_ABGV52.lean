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
open TensorProduct MvPolynomial
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

/-! ## 7. 登记 -/

/-- **登记** ✗（**源陈述缺假设** ✓✓，**印版级已核** ✓；L39 家族 ✓）：源 `thm3.9` 的**陈述**
（**印版 p.184** ✓，逐字）只说「Let `φ : S → R` be an `F` algebra map between `F` algebra
**domains**」✗ —— **未**列**仿射性** ✗；而其**证明**（**印版 p.185** ✓，逐字）两处**都用到** ✓：
「**Since `R(1/r)` is affine**, there is an `F` algebra surjection `η : F[x₁,…,xₙ] → R(1/r)`」✓、
「**Since `S` is affine**, `ψ(S) ⊂ F[x₁,…,xₙ](1/w)` for some `w ∉ P`」✓。
**对照** ✓：同页上方的 `thm3.8` 的陈述**明写**「an **affine** `F` algebra `S`」✓ ⟹
`thm3.9` 的省略是**陈述层面**的 ✓，非术语约定 ✗。
**形式化侧结论** ✓：本工程的反方向**目标形**须**显式**带 `Algebra.FiniteType F S` ✓ 与
`Algebra.FiniteType F (Localization.Away r)` ✓（§4 ✓ 的仿射层即其前置 ✓）。
**⚠ 优先级** ✓：该发现与蓝图 §3.3 T3 的「源仅设 `q(S₁)=K` 而证明需 `q(S₂)=K`」**同型** ✓
（`deadend`／勘误候选 ✓）。 -/
theorem thm39_affineness_finding_registered : True := trivial

/-- **登记** ✗：本层**未落**的两件 ✓（均须按 §47／§52 同法先作**来源核验** ✓）：

① **`thm3.9` 的反方向**（(ii)⟹(i) ✓，印版 p.185 ✓）：源证明用
「`R(1/r)` **仿射** ⟹ 取 `F[x₁..xₙ] ↠ R(1/r)`」✓（**§4 ✓ 已备** ✓）、
「局部化 `F[x₁..xₙ]_P`（`P = ker η` ✓）」✓、「`η` 延拓到 `T → K`」✓、
「`T/M = K`（`K = q(R)` ✓）」✓、「`ψ(S) ⊆ F[x](1/w)` 对某 `w ∉ P`」✓
（**有限型子代数落在单元局部化中** ✓ —— 本工程 `SaltSwan_ABGV52.exists_localization_ge_adjoin` ✓ **已备** ✓）；
余下的零件 ✓：`Localization.AtPrime` ✓ ＋ `T/M = q(R)` ✓（剩余域 ≅ 分式域 ✓）。

② **`thm3.8`** ✓（印版 p.184 ✓）：需 ① 的**双向** ✓ ＋ `lem3.5` ✓（`SaltCor_ABGV52.lem3_5` ✓ 已有 ✓）。

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
#print axioms thm39_affineness_finding_registered
#print axioms thm39_gap_registered

end ABGV52
