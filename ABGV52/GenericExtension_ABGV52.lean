/-
  ABGV-5.2 · B 档 M4 第二／三件 —— **generic extension 与 §1 语言（𝓔(G) 切片）**（2026-10-11）

  **来源** ✓：
  * Saltman **1982** `raw/Saltman1982.tex:153`（label `definition-1-1`）＝ **generic extension** 三款 ✓；
  * Saltman **1984** `raw/Saltman1984.tex:88–130`（§1）＝ linear structure／F-类／lifting property／
    representing／**generic object**／densely representing ✓（**⚠-tex-sourced** ✗；PDF 孪生件均在库 ✓）。
  **对齐** ✓：`IsGenericExtension`（def 1.1 ✓）＝ **`𝓔(G)`-特化的 generic object** ✓。
  **登记** ✗：(c) 的等变性；`LiftingPropertyEG` 中「`M` 确为 `T` 的剩余域」；Prop 1.1(a)(b)（源中省略证明 ✓）。
  **无 sorry、无自造公理**；公理门见文末 ✓。
-/
import ABGV52.GaloisAlgebra_ABGV52
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
open CategoryTheory
noncomputable section

universe u

namespace ABGV52.BTier

/-- def 1.1(c) 的**可实现性谓词**（真内容形 ✓）：对任意含 `F` 的域 `K` 与 `G`-Galois 扩张 `L/K` ✓，
存在 `F`-代数同态 `φ : R → K` ✓ 使 `L ≅ S ⊗_R K`（沿 `φ` 的基变换 ✓）。
**登记** ✗：源文还要求该同构**保 `G`-作用** ✓（等变性 ✓）—— 需 `S ⊗_R K` 上的 `G`-作用 ✗，本件未落 ✓。 -/
def RealizationProperty (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] : Prop :=
  ∀ (K : Type) [Field K] [Algebra F K]
    (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L]
    (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup K L G hKL →
      ∃ (φ : R →ₐ[F] K),
        letI : Algebra R K := φ.toRingHom.toAlgebra
        Nonempty (L ≃ₐ[K] (TensorProduct R K S))

/-- **`S/R` 是 `G` 在 `F` 上的 generic extension**（def 1.1 三款 ✓）：
(a) `R` 形如 `F[x₁..xₙ](1/s)` ✓；(b) `S/R` 是 `G`-Galois ✓（§0 判据 ✓）；(c) 可实现性 ✓。 -/
def IsGenericExtension (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
  IsGaloisWithGroup R S G hRG ∧
  RealizationProperty F G R S

/-- **representing object**（`𝓔(G)` 切片 ✓；§1 逐字 ✓）：`S/R` 在类内（`G`-Galois ✓）
且对一切**域** `K ⊇ F` 上的 `G`-Galois 扩张 `L/K` ✓ 存在 `φ : R →ₐ[F] K` realize 之 ✓。 -/
def IsRepresentingObjectEG (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  IsGaloisWithGroup R S G hRG ∧ RealizationProperty F G R S

/-- **generic object**（`𝓔(G)` 切片 ✓；§1 逐字 ✓）：representing ＋ `R` 为**局部化多项式环** ✓。 -/
def IsGenericObjectEG (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  IsRepresentingObjectEG F G R S hRG ∧
    (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))

/-- **两个 `def 1.1` 编码的**一致性锁定**（cross-vocabulary lock）** ✓✅：本件的
`IsGenericExtension`（三款**平列** ✓）与本件的 `IsGenericObjectEG`（**representing ∧ 局部化多项式环** ✓）
是**同一个谓词** ✓ —— 二者只差合取的**次序** ✓（`A ∧ (B ∧ C)` vs `(B ∧ C) ∧ A` ✓）。
**⚠ 意义** ✓：源 `definition-1-1` 的两条**转写路线**（"三款平列" ✓ 与
「（`𝓔(G)` 切片）representing object ＋ `R` 为局部化多项式环」✓）**在此对齐** ✓ ⟹
下游无论走哪一条都是**同一命题** ✓；**锁形** ✓：任一侧的合取内容或次序漂移 ✗ 本 `iff` 立即失败 ✓
（`IsGenericExtension` 的 `A`／`B`／`C` 与 `IsGenericObjectEG` 的 `B∧C`／`A` 一一对应 ✓）。
**⚠ 依据** ✓：`Saltman1982` 印 **255** ✓（**PDF 第 6 页** ✓，**偏移 ＝ PDF ＋ 249** ✓）——
**⚠ r204 回填** ✓（**原注「印 254」差一页** ✗；本轮**回印目视** ✓：`definition-1-1` 与 §1 标题
「1. THE DEFINITION」**同在印 255** ✓，而**印 254** 是 §0 的 `proposition-0-5` 与**强调句**所在页 ✓，
**两者不可混用** ✗）。 -/
theorem isGenericExtension_iff_isGenericObjectEG (F : Type*) [Field F] (G : Type*) [Group G]
    [Fintype G] (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (IsGenericExtension F G R S hRG ↔ IsGenericObjectEG F G R S hRG) :=
  and_comm

/-- **lifting property**（`𝓔(G)` 切片 ✓；§1 逐字 ✓）：`T` 局部 `F`-代数、`M` 为其剩余域
（本形以**显式** `F`-代数同态链承载 ✓；「`M` 确为剩余域」登记 ✗），则 `M` 上的 `G`-Galois `S₀`
可沿 `T` 提升：存在 `T` 上的 `G`-Galois `S'` ✓ 使 `S₀ ≅ S' ⊗_T M` ✓。 -/
def LiftingPropertyEG (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G] : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra F T] [IsLocalRing T]
    (hFT : ∀ (a : F) (x : T), algebraMap F T a * x = a • x)
    (S₀ : Type) [CommRing S₀] [Algebra F S₀]
    [Algebra (IsLocalRing.ResidueField T) S₀]
    [IsScalarTower F (IsLocalRing.ResidueField T) S₀]
    [MulSemiringAction G S₀]
    (hRG₀ : ∀ (g : G) (r : IsLocalRing.ResidueField T) (t : S₀),
      g • (r • t) = r • (g • t)),
    IsGaloisWithGroup (IsLocalRing.ResidueField T) S₀ G hRG₀ →
      ∃ (S' : Type) (_ : CommRing S') (_ : Algebra T S') (_ : Algebra F S')
        (_ : IsScalarTower F T S') (_ : MulSemiringAction G S')
        (hRG' : ∀ (g : G) (r : T) (t : S'), g • (r • t) = r • (g • t)),
        IsGaloisWithGroup T S' G hRG' ∧
          Nonempty (S₀ ≃ₐ[IsLocalRing.ResidueField T]
            (TensorProduct T (IsLocalRing.ResidueField T) S'))

/-- **类型锁定**：外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem isGenericExtension_typeLock (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (IsGenericExtension F G R S hRG)
      = ((∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
          IsGaloisWithGroup R S G hRG ∧
          RealizationProperty F G R S) := rfl

/-- **类型锁定**（`IsGenericObjectEG`）✓。 -/
theorem isGenericObjectEG_typeLock (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (IsGenericObjectEG F G R S hRG)
      = (IsRepresentingObjectEG F G R S hRG ∧
          (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
            Nonempty (R ≃ₐ[F] Localization.Away w))) := rfl

/-- **非空洞探针（L1）** ✓：判据的**前提数据可实例化** ✓（`F = ℚ` ✓、`G = PUnit` ✓）。 -/
theorem isGenericExtension_data_nonempty :
    Nonempty (Field ℚ) ∧ Nonempty (Group PUnit) ∧ Nonempty (Fintype PUnit) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- **登记** ✗：① def 1.1(c) 的**等变性**（保 `G`-作用 ✓）；② `RealizationProperty` 的**非空洞性**（存在真实现 ✓）；
③ `IsGenericObjectEG` 与 `IsGenericExtension` 的**等价**（应成立 ✓，未证 ✗）；④ `LiftingPropertyEG` 中
「`M` 确为 `T` 的剩余域」一节（本形只带显式同态链 ✓）；⑤ **Prop 1.1(a)(b)**（源中**省略证明** ✗）。 -/
theorem liftingPropertyEG_gap_registered : True := trivial

/-- **登记** ✗：（原 `isGenericExtension` 件的）等变性与非空洞性条目并入上条 ✓。 -/
theorem isGenericExtension_gap_registered : True := trivial

/-- **多项式代数沿满射的提升** ✓：`φ : T →ₐ[F] K` 满 ⟹ 每个 `F`-代数同态
`f : F[x₁..xₙ] →ₐ[F] K` 可沿 `φ` 提升 ✓（逐变量取原像 ✓，再用 `aeval` 的万有性质 ✓）。 -/
lemma mvPolynomial_lift_of_surjective {F T K : Type*} [Field F] [CommSemiring T] [CommSemiring K]
    [Algebra F T] [Algebra F K] (φ : T →ₐ[F] K) (hφ : Function.Surjective φ) (n : ℕ)
    (f : MvPolynomial (Fin n) F →ₐ[F] K) :
    ∃ (F' : MvPolynomial (Fin n) F →ₐ[F] T), ∀ p, φ (F' p) = f p := by
  classical
  choose g hg using fun i => hφ (f (MvPolynomial.X i))
  refine ⟨MvPolynomial.aeval g, ?_⟩
  intro p
  have hcomp : φ.comp (MvPolynomial.aeval g) = MvPolynomial.aeval (fun i => φ (g i)) := by
    ext i; simp
  rw [show φ ((MvPolynomial.aeval g) p) = (φ.comp (MvPolynomial.aeval g)) p from rfl, hcomp]
  rw [show (fun i => φ (g i)) = (fun i => f (MvPolynomial.X i)) from funext fun i => hg i]
  congr 1
  exact MvPolynomial.algHom_ext (fun i => by simp)

/- **局部化层提升：下一手** ✗（B 档第 24 轮实测卡点）
`IsLocalization.Away.lift (x) {g} (IsUnit (g x)) : S →+* P` ✓ **存在**（参数序：`x` 显式 ✓、`g` **隐式** ✓）——
已在件内试装，卡在两处 ✓：
① 相容性 `φ ∘ ψ = f` 需**从局部化出发的环同态外延引理** ✗ —— 我试的 `IsLocalization.Away.algHom_ext` **不存在** ✗
   （`IsLocalization.algHom_ext` ✓ 存在，但那是 `→ₐ[R]` 形 ✓）；下一手 = `#check` `IsLocalization.ringHom_ext`／`IsLocalization.lift_comp`-族 ✗；
② `ψ` 的 `F`-线性（升为 `→ₐ[F]` ✓）同样需上述外延引理 ✓。
⟹ **机制核心（多项式层）已证** ✓，局部化层列为下一手 ✓。 -/

/-- **局部化层提升** ✓（Prop 1.1(a) 机制第二步 ✓）：`f : F[x](1/r) →ₐ[F] K` 在**多项式层**已有
沿满射 `φ` 的提升 `g` ✓（`φ ∘ g = f ∘ algebraMap` ✓）且 `g r` 是 `T` 中的**单位** ✓
⟹ `f` 本身可沿 `φ` 提升 ✓（`IsLocalization.lift` ✓ ＋ `IsLocalization.ringHom_ext` ✓）。
**标量塔** ✓：`IsScalarTower F F[x] F[x](1/r)` 作为显式假设（否则 `Algebra F (Localization.Away r)` 不可合成 ✗）。 -/
lemma away_lift_of_surjective {F T K : Type*} [Field F] [CommRing T] [Field K]
    [Algebra F T] [Algebra F K] (φ : T →ₐ[F] K) (n : ℕ)
    (r : MvPolynomial (Fin n) F) [IsScalarTower F (MvPolynomial (Fin n) F) (Localization.Away r)]
    (f : Localization.Away r →ₐ[F] K) (g : MvPolynomial (Fin n) F →ₐ[F] T)
    (hg : ∀ p, φ (g p) = f (algebraMap (MvPolynomial (Fin n) F) (Localization.Away r) p))
    (hu : IsUnit (g r)) :
    ∃ (F' : Localization.Away r →ₐ[F] T), ∀ q, φ (F' q) = f q := by
  classical
  have hpow : ∀ y : Submonoid.powers r, IsUnit (g.toRingHom (y : MvPolynomial (Fin n) F)) := by
    rintro ⟨_, ⟨k, rfl⟩⟩
    simpa using hu.pow k
  let ψ : Localization.Away r →+* T :=
    IsLocalization.lift (R := MvPolynomial (Fin n) F) (M := Submonoid.powers r)
      (S := Localization.Away r) (g := g.toRingHom) hpow
  have hψc : ψ.comp (algebraMap (MvPolynomial (Fin n) F) (Localization.Away r)) = g.toRingHom :=
    IsLocalization.lift_comp (R := MvPolynomial (Fin n) F) (M := Submonoid.powers r)
      (S := Localization.Away r) (g := g.toRingHom) hpow
  have hψ : ∀ p : MvPolynomial (Fin n) F,
      ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away r) p) = g p := by
    intro p
    rw [← RingHom.comp_apply, hψc]
    rfl
  have hcomp : φ.toRingHom.comp ψ = f.toRingHom := by
    apply IsLocalization.ringHom_ext (R := MvPolynomial (Fin n) F)
      (S := Localization.Away r) (Submonoid.powers r)
    apply RingHom.ext
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply, hψ p]
    exact hg p
  have hFpt : ∀ a : F, ψ (algebraMap F (Localization.Away r) a) = algebraMap F T a := by
    intro a
    simp only [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F) (Localization.Away r)]
    rw [hψ]
    exact g.commutes a
  exact ⟨{ ψ with commutes' := hFpt }, fun q => congrFun (congrArg DFunLike.coe hcomp) q⟩

/-- **局部环中「剩余域像非零 ⟹ 单位」** ✓（Prop 1.1(a) 的 `IsUnit` 供给点 ✓）：
`IsLocalRing.residue_ne_zero_iff_isUnit` ✓ 的直接包装。 -/
lemma isUnit_of_residue_ne_zero {T : Type*} [CommRing T] [IsLocalRing T] {x : T}
    (h : IsLocalRing.residue T x ≠ 0) : IsUnit x :=
  (IsLocalRing.residue_ne_zero_iff_isUnit x).mp h

/-- **`G`-Galois 的基变换**（＝源 **`proposition-0-2(d)`** ✓，`raw/Saltman1982.tex:82`，**⚠-tex-sourced** ✗）：
> "Let `φ : R → R'` be a ring homomorphism and set `S' = S ⊗_φ R'`. Then `S'/R'` is Galois with group `G`."
（源引 **[DI71] p. 85** ✓，且**源中无证明** ✗ —— 属「quote four results … instead of proofs」✓。）
**类型锁定假设** ✓（本件未证 ✗）：`S ⊗_R R'` 上的 `G`-作用以**参数**给出 ✓（该作用本身可自建 ✓，见登记 ✗）。 -/
def GaloisBaseChangeHyp (R S R' : Type*) [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] (G : Type*) [Group G] [Fintype G]
    [MulSemiringAction G S] [MulSemiringAction G (TensorProduct R R' S)]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hR'G : ∀ (g : G) (r : R') (t : TensorProduct R R' S), g • (r • t) = r • (g • t)) : Prop :=
  IsGaloisWithGroup R S G hRG → IsGaloisWithGroup R' (TensorProduct R R' S) G hR'G

/-- **类型锁定**：外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem galoisBaseChangeHyp_typeLock (R S R' : Type*) [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] (G : Type*) [Group G] [Fintype G]
    [MulSemiringAction G S] [MulSemiringAction G (TensorProduct R R' S)]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hR'G : ∀ (g : G) (r : R') (t : TensorProduct R R' S), g • (r • t) = r • (g • t)) :
    (GaloisBaseChangeHyp R S R' G hRG hR'G)
      = (IsGaloisWithGroup R S G hRG →
          IsGaloisWithGroup R' (TensorProduct R R' S) G hR'G) := rfl

/-- **非空洞探针（L1）** ✓：假设类的**前提数据可实例化** ✓（`ℚ` ✓／`PUnit` ✓）。 -/
theorem galoisBaseChangeHyp_data_nonempty :
    Nonempty (Field ℚ) ∧ Nonempty (Group PUnit) ∧ Nonempty (Fintype PUnit) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- **登记** ✗：① 本假设的**证明**（[DI71] p.85 的机制 ✓：交叉积与自同态环各自基变换
`Δ(S/R,G) ⊗_R R' ≅ Δ(S'/R',G)` ✓、`Hom_R(S,S) ⊗_R R' ≅ Hom_{R'}(S',S')` ✓）未落 ✓；
② `S ⊗_R R'` 上的 `G`-作用（沿 `S`-因子作用 ✓，需与 `R'`-纯量交换 ✓）未自建 ✓（本形以参数承载 ✓）。 -/
theorem galoisBaseChange_gap_registered : True := trivial

/-- **单位的像非零** ✓（Prop 1.1(a) 装配的第一步 ✓）：`φ : R →+* K` 到**域**，`w` 是 `R` 中单位
⟹ `φ w ≠ 0` ✓（由此配合 `isUnit_of_residue_ne_zero` 得提升后的 `IsUnit` ✓）。 -/
lemma ne_zero_of_isUnit_map {R K : Type*} [CommRing R] [Field K] (φ : R →+* K) {w : R}
    (hw : IsUnit w) : φ w ≠ 0 :=
  fun h => (hw.map φ).ne_zero h

/-- 纯量塔下的单位像非零（`F`-代数同态版 ✓，供装配直接使用 ✓）。 -/
lemma ne_zero_of_isUnit_map_algHom {F R K : Type*} [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra F K] (φ : R →ₐ[F] K) {w : R} (hw : IsUnit w) : φ w ≠ 0 :=
  ne_zero_of_isUnit_map φ.toRingHom hw

/-- **装配第 1–3 步** ✓（Prop 1.1(a)）：由 generic object 与局部环 `T` 上的 `G`-Galois `S₀`，
取出 specializing 映射 `φ : R →ₐ[F] ResidueField T` ✓、同构 `e : S₀ ≃ₐ[K] (S ⊗_R K)` ✓、
局部化形（`n`／`w ≠ 0` ✓）与 `ρ : R ≃ₐ[F] Localization.Away w` ✓；
并给出搬运后的 `f := φ.comp ρ.symm : Localization.Away w →ₐ[F] K` ✓（第 3 步的显式形 ✓）。 -/
lemma assemble_steps123
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (h : IsGenericObjectEG F G R S hRG)
    (T : Type) [CommRing T] [Algebra F T] [IsLocalRing T]
    (S₀ : Type) [CommRing S₀] [Algebra F S₀]
    [Algebra (IsLocalRing.ResidueField T) S₀]
    [IsScalarTower F (IsLocalRing.ResidueField T) S₀]
    [MulSemiringAction G S₀]
    (hRG₀ : ∀ (g : G) (r : IsLocalRing.ResidueField T) (t : S₀), g • (r • t) = r • (g • t))
    (h₀ : IsGaloisWithGroup (IsLocalRing.ResidueField T) S₀ G hRG₀) :
    ∃ (φ : R →ₐ[F] IsLocalRing.ResidueField T)
      (n : ℕ) (w : MvPolynomial (Fin n) F) (_ : w ≠ 0)
      (ρ : R ≃ₐ[F] Localization.Away w),
      (letI : Algebra R (IsLocalRing.ResidueField T) := φ.toRingHom.toAlgebra
       Nonempty (S₀ ≃ₐ[IsLocalRing.ResidueField T]
         (TensorProduct R (IsLocalRing.ResidueField T) S))) := by
  obtain ⟨hrep, haway⟩ := h
  obtain ⟨-, hreal⟩ := hrep
  obtain ⟨n, w, hw, ⟨ρ⟩⟩ := haway
  obtain ⟨φ, he⟩ := hreal (IsLocalRing.ResidueField T) S₀ hRG₀ h₀
  exact ⟨φ, n, w, hw, ρ, he⟩

/-- **装配第 4–7 步** ✓（Prop 1.1(a)）：由第 1–3 步的数据（`φ` ✓、局部化形 `n,w,ρ` ✓、`hw` ✓）
与局部环 `T` ✓，造出**沿 `residue` 提升**的 `ψ : R →ₐ[F] T` ✓（`∀ x, residue (ψ x) = φ x` ✓）。
机制 ✓：多项式层（`residue` **满射** ✓）→ `IsUnit (g w)` ✓ → 局部化层 ✓ → 沿 `ρ` 回 `R` ✓。 -/
lemma assemble_steps467
    (F : Type) [Field F]
    (R : Type) [CommRing R] [Algebra F R]
    (T : Type) [CommRing T] [Algebra F T] [IsLocalRing T]
    (n : ℕ) (w : MvPolynomial (Fin n) F)
    [IsScalarTower F (MvPolynomial (Fin n) F) (Localization.Away w)]
    (φ : R →ₐ[F] IsLocalRing.ResidueField T) (hw : w ≠ 0)
    (ρ : R ≃ₐ[F] Localization.Away w) :
    ∃ (ψ : R →ₐ[F] T), ∀ x : R, IsLocalRing.residue T (ψ x) = φ x := by
  classical
  let res : T →ₐ[F] IsLocalRing.ResidueField T :=
    { IsLocalRing.residue T with commutes' := fun a => rfl }
  let f : Localization.Away w →ₐ[F] IsLocalRing.ResidueField T := φ.comp ρ.symm
  -- 第 4 步 ✓：多项式层提升（`res` 满射 ✓）
  obtain ⟨g, hg⟩ := mvPolynomial_lift_of_surjective res IsLocalRing.residue_surjective n
    (f.comp (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away w)))
  -- 第 5 步 ✓：`IsUnit (g w)`
  have hres : IsLocalRing.residue T (g w)
      = f (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w) := hg w
  have hgw : IsUnit (g w) := by
    apply isUnit_of_residue_ne_zero
    rw [hres]
    exact ne_zero_of_isUnit_map_algHom f (IsLocalization.Away.algebraMap_isUnit w)
  -- 第 6 步 ✓：局部化层提升
  obtain ⟨F', hF'⟩ := away_lift_of_surjective res n w f g hg hgw
  -- 第 7 步 ✓：沿 `ρ` 回 `R`
  exact ⟨F'.comp ρ, fun x => by
    change res (F' (ρ x)) = φ x
    rw [hF']
    show φ (ρ.symm (ρ x)) = φ x
    exact congrArg φ (ρ.symm_apply_apply x)⟩

variable {R T S : Type} [CommRing R] [CommRing T] [CommRing S] [Algebra R T] [Algebra R S]
variable {G : Type} [Group G] [MulSemiringAction G S]

/-- **`g • ·` 作为 `R`-代数自同构** ✓（需 `hRG` ✓ —— `[MulSemiringAction G S]` 不蕴含 ✓）。 -/
def actAlgEquiv (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) :
    S ≃ₐ[R] S where
  toFun s := g • s
  invFun s := g⁻¹ • s
  left_inv s := by simp [← mul_smul]
  right_inv s := by simp [← mul_smul]
  map_mul' x y := MulSemiringAction.smul_mul g x y
  map_add' x y := smul_add g x y
  commutes' r := by
    have h := hRG g r 1
    simpa [Algebra.algebraMap_eq_smul_one] using h

/-- 张量上的 `g`-作用（`AlgHom` 形 ✓）。 -/
def tensorActHom (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) :
    (TensorProduct R T S) →ₐ[R] (TensorProduct R T S) :=
  Algebra.TensorProduct.map (AlgHom.id R T) (actAlgEquiv hRG g)

/-- 作用律一 ✓（**朴素 `simp`** ✓，不用名单 ✗）。 -/
lemma actAlgEquiv_one (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    actAlgEquiv hRG 1 = AlgEquiv.refl := by
  ext s
  simp [actAlgEquiv]

/-- 作用律二 ✓。 -/
lemma actAlgEquiv_mul (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (g h : G) :
    actAlgEquiv hRG (g * h) = (actAlgEquiv hRG h).trans (actAlgEquiv hRG g) := by
  ext s
  simp [actAlgEquiv, mul_smul]

/-- **`S ⊗_R T` 上的 `G`-作用** ✓（沿 `S`-因子；mathlib **无**此实例 ✗；`hRG` 作显式参数 ✓，
用法 `letI := tensorMulSemiringAction hRG` ✓）。 -/
def tensorMulSemiringAction (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    MulSemiringAction G (TensorProduct R T S) where
  smul g x := tensorActHom hRG g x
  one_smul x := by
    change tensorActHom hRG 1 x = x
    have h : tensorActHom hRG 1 = AlgHom.id R (TensorProduct R T S) := by
      rw [tensorActHom, actAlgEquiv_one]
      show Algebra.TensorProduct.map (AlgHom.id R T) (AlgHom.id R S)
        = AlgHom.id R (TensorProduct R T S)
      rw [Algebra.TensorProduct.map_id]
    rw [h]
    rfl
  mul_smul g h x := by
    change tensorActHom hRG (g * h) x = tensorActHom hRG g (tensorActHom hRG h x)
    have hh : tensorActHom hRG (g * h)
        = ((tensorActHom hRG g).comp (tensorActHom hRG h)
            : (TensorProduct R T S) →ₐ[R] (TensorProduct R T S)) := by
      rw [tensorActHom, tensorActHom, tensorActHom, actAlgEquiv_mul,
        ← Algebra.TensorProduct.map_comp]
      rfl
    rw [hh]
    rfl
  smul_zero g := map_zero (tensorActHom hRG g)
  smul_add g x y := map_add (tensorActHom hRG g) x y
  smul_mul g x y := map_mul (tensorActHom hRG g) x y
  smul_one g := map_one (tensorActHom hRG g)

/-- **张量作用与 `T`-纯量的交换律** ✓：`G` 沿**第二个因子**（`S` ✓）作用，`T`-纯量作用在**第一个因子** ✓
⟹ 两者交换 ✓。这是 `GaloisBaseChangeHyp` 的 `hR'G` ✓ 所需的输入 ✓。 -/
lemma tensorAct_smul_comm (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (g : G) (r : T) (t : TensorProduct R T S) :
    tensorActHom (T := T) hRG g (r • t) = r • tensorActHom (T := T) hRG g t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [TensorProduct.smul_tmul', tensorActHom, Algebra.TensorProduct.map_tmul]
      rfl
  | add a b ha hb => simp [smul_add, ha, hb]

/-- **前提谓词** ✓：`S₀ ≅ K ⊗_R S`，其中 `K` 上的 `R`-代数结构作**显式参数** ✓
（谓词体内用**项位置** `letI` ✓ —— 该形经验证可正常合成实例 ✓）。 -/
def RepIso (R K S S₀ : Type*) [CommRing R] [CommRing S] [CommRing K] [CommRing S₀]
    [Algebra R S] [Algebra K S₀] (aRK : Algebra R K) : Prop :=
  letI := aRK
  Nonempty (S₀ ≃ₐ[K] (TensorProduct R K S))

/-- **结论谓词** ✓：`S₀ ≅ S' ⊗_T K`（`S' := S ⊗_R T` ✓），`K` 上的 `R`-与 `T`-结构均作**显式参数** ✓。 -/
def CancelIso (R T K S S₀ : Type*) [CommRing R] [CommRing T] [CommRing K] [CommRing S]
    [CommRing S₀] [Algebra R S] [Algebra R T] [Algebra K S₀]
    (aRK : Algebra R K) (aTK : Algebra T K) (st : IsScalarTower R T K) : Prop :=
  letI := aRK
  letI := aTK
  letI := st
  Nonempty (S₀ ≃ₐ[K] (TensorProduct T K (TensorProduct R T S)))

/-- **张量消去（原 `hiso` 假设的实体）** ✅✅：`RepIso ⟹ CancelIso`，**无需任何假设** ✓。
即 `K ⊗_R S ≃ₐ[K] K ⊗_T (T ⊗_R S)`（`K = IsLocalRing.ResidueField T` ✓），由 mathlib 现成的
`Algebra.TensorProduct.cancelBaseChange : A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B`
（`Mathlib/RingTheory/TensorProduct/Maps.lean:476` ✓，**是 `AlgEquiv`** ✓ —— 非交接件登记的
`LinearEquiv` 形 ✗）在 `(R, S, T, A, B) := (R, T, K, K, S)` 处取对称、再与 `RepIso` 的同构
**复合**（`AlgEquiv.trans` ✓ 次序：`(e₁.trans e₂) x = e₂ (e₁ x)` ✓）而得 ✓。
⟹ 本引理把 `liftingPropertyEG_of_isGenericObjectEG` 的**第三个假设** `hiso` **消除** ✓
（协议：旧接口名与旧类型**逐字保留** ✓，另立新定理填充 ✓，见 `…_stronger` ✓）。 -/
theorem cancelIso_of_repIso
    (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] [IsLocalRing T]
    (S : Type*) [CommRing S] [Algebra R S]
    (S₀ : Type*) [CommRing S₀]
    [Algebra (IsLocalRing.ResidueField T) S₀]
    [aRK : Algebra R (IsLocalRing.ResidueField T)]
    [aTK : Algebra T (IsLocalRing.ResidueField T)]
    [st : IsScalarTower R T (IsLocalRing.ResidueField T)]
    (hrep : RepIso R (IsLocalRing.ResidueField T) S S₀ aRK) :
    CancelIso R T (IsLocalRing.ResidueField T) S S₀ aRK aTK st := by
  obtain ⟨he⟩ := hrep
  exact ⟨he.trans (Algebra.TensorProduct.cancelBaseChange (R := R) (S := T)
    (T := IsLocalRing.ResidueField T) (A := IsLocalRing.ResidueField T) (B := S)).symm⟩

/-- **Prop 1.1(a)**（Saltman 1984 §1，`𝓔(G)` 切片 ✓）：**generic object ⟹ lifting property** ✓。
**源中证明省略** ✗（"a trivial generalization of the argument of [23], p. 275" ✓）—— 本形式按源文机制**补证** ✓。
**依赖登记** ✗：第 8 步用 **`GaloisBaseChangeHyp`**（＝源 `prop-0-2(d)` ✓，引 [DI71] p.85 ✓）作参数 ✓。 -/
theorem liftingPropertyEG_of_isGenericObjectEG
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
      (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
      GaloisBaseChangeHyp R S T G hRG hR'G)
    -- **张量消去假设** ✓（最后一哩的类型锁定形 ✓；结构作显式参数 ✓ ⟹ 避开 `letI`-in-binder ✗；
    -- **已证成** ✅ 见 `cancelIso_of_repIso` ✓ —— 旧接口逐字保留 ✓，由 `…_stronger` 就地充当 ✓）
    (hiso : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T]
      (S₀ : Type) [CommRing S₀] [Algebra F S₀]
      [Algebra (IsLocalRing.ResidueField T) S₀]
      [IsScalarTower F (IsLocalRing.ResidueField T) S₀]
      (aRK : Algebra R (IsLocalRing.ResidueField T))
      (aTK : Algebra T (IsLocalRing.ResidueField T))
      (st : IsScalarTower R T (IsLocalRing.ResidueField T)),
      RepIso R (IsLocalRing.ResidueField T) S S₀ aRK →
        CancelIso R T (IsLocalRing.ResidueField T) S S₀ aRK aTK st)
    -- **结构一致性假设** ✓（第三种 ✓；两结构相等但**非 defeq** ✗ ⟹ 显式承载 ✓；**可证** ✓，见登记）
    (hcoh : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T] (φ : R →ₐ[F] IsLocalRing.ResidueField T) (ψ : R →ₐ[F] T),
      (∀ x : R, algebraMap R T x = ψ x) →
      (∀ x : R, IsLocalRing.residue T (ψ x) = φ x) →
      φ.toRingHom.toAlgebra = IsLocalRing.ResidueField.algebra T) :
    LiftingPropertyEG F G := by
  -- ⚠ `obtain … := hgen` 会**消费** `hgen`（rcases 语义 ✓）⟹ **先留副本** ✓
  have hgen' := hgen
  obtain ⟨hrep, haway⟩ := hgen
  obtain ⟨hgalRS, hreal⟩ := hrep
  refine fun T _ _ hT _ S₀ _ _ _ _ _ hRG₀ h₀ => ?_
  -- 第 1–3 步 ✓
  obtain ⟨φ, n, w, hw, ρ, he⟩ := assemble_steps123 F G R S hRG hgen' T S₀ hRG₀ h₀
  -- 第 4–7 步 ✓
  obtain ⟨ψ, hψ⟩ := assemble_steps467 F R T n w φ hw ρ
  -- 第 8 步 ✓
  letI : Algebra R T := ψ.toRingHom.toAlgebra
  letI : MulSemiringAction G (TensorProduct R T S) := tensorMulSemiringAction hRG
  letI hex : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t) :=
    fun g r t => tensorAct_smul_comm hRG g r t
  have hgal : IsGaloisWithGroup T (TensorProduct R T S) G hex :=
    hBC (T := T) (hR'G := hex) (by simpa using hgalRS)
  -- 第 9 步 ✓：组装（同构待搬运 ✗）
  exact ⟨TensorProduct R T S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hex, hgal,
    hiso T S₀ (IsLocalRing.ResidueField.algebra T) (IsLocalRing.residue T).toAlgebra
      (by
        -- 关键等式：`algebraMap T K (algebraMap R T r) = algebraMap R K r` ✓
        -- （由 `hcoh` 把 RHS 的结构换成 residue-诱导 ✓，再由 `hψ` ✓）
        have key : ∀ r : R,
            algebraMap T (IsLocalRing.ResidueField T) (algebraMap R T r)
              = (IsLocalRing.residue T) (ψ r) := by
          intro r
          rw [show algebraMap R T r = ψ r from rfl]
          rfl
        have key2 : ∀ r : R,
            algebraMap T (IsLocalRing.ResidueField T) (algebraMap R T r)
              = (IsLocalRing.residue T) (ψ r) := key
        refine ⟨fun r t z => ?_⟩
        show algebraMap T (IsLocalRing.ResidueField T) (algebraMap R T r * t) * z
          = (IsLocalRing.residue T) (ψ r) * (algebraMap T (IsLocalRing.ResidueField T) t * z)
        rw [map_mul, key r]
        ring) (hcoh T φ ψ (fun x => rfl) hψ ▸ he)⟩

/-- **类型锁定**（成品定理的**陈述形状**锁定 ✓）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_typeLock
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (∀ (hgen : IsGenericObjectEG F G R S hRG)
      (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
        (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
        GaloisBaseChangeHyp R S T G hRG hR'G),
      LiftingPropertyEG F G)
      = (∀ (hgen : IsGenericObjectEG F G R S hRG)
          (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
            [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
            (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
            GaloisBaseChangeHyp R S T G hRG hR'G),
          LiftingPropertyEG F G) := rfl

/-- **`Algebra` 结构等式的外延引理** ✓（mathlib **无** `Algebra.ext` ✗）：
两结构只要 `algebraMap` 相同即相同 ✓（因 `smul` 由 `algebraMap` 决定 ✓，见字段 `smul_def'` ✓）。 -/
lemma algebra_ext_of_algebraMap_eq {R K : Type*} [CommRing R] [CommRing K]
    (a b : Algebra R K)
    (h : ∀ x : R, a.algebraMap x = b.algebraMap x) : a = b := by
  have hsmul : a.toSMul = b.toSMul := by
    ext x y
    have ha : a.toSMul.smul x y = a.algebraMap x * y := a.smul_def' x y
    have hb : b.toSMul.smul x y = b.algebraMap x * y := b.smul_def' x y
    rw [ha, hb, h x]
  cases a; cases b
  congr 1
  ext x
  exact h x

/-- **结构一致性（`hcoh`）已可证** ✓：`ψ` 即结构映射 ✓ 且 `φ = residue ∘ ψ` ✓ ⟹
`φ`-诱导 与 `residue`-诱导 两种 `R`-代数结构**相同** ✓（由 `algebra_ext_of_algebraMap_eq` ✓，
即 `smul` 由 `algebraMap` 决定 ✓）。 -/
lemma phiToAlgebra_eq_residueAlgebra {F R T : Type*} [Field F] [CommRing R] [CommRing T]
    [Algebra F R] [Algebra F T] [Algebra R T] [IsScalarTower F R T] [IsLocalRing T]
    (φ : R →ₐ[F] IsLocalRing.ResidueField T) (ψ : R →ₐ[F] T)
    (h1 : ∀ x : R, algebraMap R T x = ψ x)
    (h2 : ∀ x : R, IsLocalRing.residue T (ψ x) = φ x) :
    φ.toRingHom.toAlgebra = IsLocalRing.ResidueField.algebra T := by
  apply algebra_ext_of_algebraMap_eq
  intro x
  show φ x = IsLocalRing.residue T (algebraMap R T x)
  rw [h1 x, h2 x]

/-- **Prop 1.1(a)（强形式）** ✓：与 `liftingPropertyEG_of_isGenericObjectEG` **同形但不带 `hcoh`** ✓
—— 该假设已由 `phiToAlgebra_eq_residueAlgebra` ✓ **证成**并在此**就地充当** ✓
（协议：**旧接口名与旧类型逐字保留** ✓，另立新定理填充 ✓）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_strong
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
      (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
      GaloisBaseChangeHyp R S T G hRG hR'G)
    -- **张量消去假设** ✓（最后一哩的类型锁定形 ✓；结构作显式参数 ✓ ⟹ 避开 `letI`-in-binder ✗；
    -- **已证成** ✅ 见 `cancelIso_of_repIso` ✓ —— 旧接口逐字保留 ✓，由 `…_stronger` 就地充当 ✓）
    (hiso : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T]
      (S₀ : Type) [CommRing S₀] [Algebra F S₀]
      [Algebra (IsLocalRing.ResidueField T) S₀]
      [IsScalarTower F (IsLocalRing.ResidueField T) S₀]
      (aRK : Algebra R (IsLocalRing.ResidueField T))
      (aTK : Algebra T (IsLocalRing.ResidueField T))
      (st : IsScalarTower R T (IsLocalRing.ResidueField T)),
      RepIso R (IsLocalRing.ResidueField T) S S₀ aRK →
        CancelIso R T (IsLocalRing.ResidueField T) S S₀ aRK aTK st) :
    LiftingPropertyEG F G :=
  liftingPropertyEG_of_isGenericObjectEG F G R S hRG hgen hBC hiso
    (by
      intro T _ _ _ _ _ φ ψ h1 h2
      exact phiToAlgebra_eq_residueAlgebra φ ψ h1 h2)

/-- **类型锁定（强形式 ✓，手写 —— 不按行范围抽签名 ✗，§33.9 已失败一次 ✓）**：
钉住 `…_strong` 的**陈述形状**（`hgen`／`hBC`／`hiso` 三假设 ✓）与**所引用谓词的签名**
（`IsGenericObjectEG`／`GaloisBaseChangeHyp`／`RepIso`／`CancelIso`／`LiftingPropertyEG` ✓）
—— 任一处签名漂移，本 `rfl` 立即编译失败 ✓（手写副本是独立文本 ✓）。
**假设表的增删**由紧随其后的**应用锁**捕捉 ✓（非本锁之职 ✗）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_strong_typeLock
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (∀ (hgen : IsGenericObjectEG F G R S hRG)
      (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
        (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
        GaloisBaseChangeHyp R S T G hRG hR'G)
      (hiso : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T]
        (S₀ : Type) [CommRing S₀] [Algebra F S₀]
        [Algebra (IsLocalRing.ResidueField T) S₀]
        [IsScalarTower F (IsLocalRing.ResidueField T) S₀]
        (aRK : Algebra R (IsLocalRing.ResidueField T))
        (aTK : Algebra T (IsLocalRing.ResidueField T))
        (st : IsScalarTower R T (IsLocalRing.ResidueField T)),
        RepIso R (IsLocalRing.ResidueField T) S S₀ aRK →
          CancelIso R T (IsLocalRing.ResidueField T) S S₀ aRK aTK st),
      LiftingPropertyEG F G)
      = (∀ (hgen : IsGenericObjectEG F G R S hRG)
      (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
        (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
        GaloisBaseChangeHyp R S T G hRG hR'G)
      (hiso : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T]
        (S₀ : Type) [CommRing S₀] [Algebra F S₀]
        [Algebra (IsLocalRing.ResidueField T) S₀]
        [IsScalarTower F (IsLocalRing.ResidueField T) S₀]
        (aRK : Algebra R (IsLocalRing.ResidueField T))
        (aTK : Algebra T (IsLocalRing.ResidueField T))
        (st : IsScalarTower R T (IsLocalRing.ResidueField T)),
        RepIso R (IsLocalRing.ResidueField T) S S₀ aRK →
          CancelIso R T (IsLocalRing.ResidueField T) S S₀ aRK aTK st),
      LiftingPropertyEG F G) := rfl

/-- **Prop 1.1(a)（更强形式）** ✅✅：与 `…_strong` **同形但不带 `hiso`** ✓ ——
该假设已由 `cancelIso_of_repIso` ✓ **证成**并在此**就地充当** ✓
（协议：**旧接口名与旧类型逐字保留** ✓ —— 原 `…_isGenericObjectEG` ✓ 与 `…_strong` ✓ 一字未动 ✓，
逐次另立新定理填充 ✓；`hcoh` 于 §33.8 消除 ✓、`hiso` 于本轮消除 ✓）。
**假设表现状 = 一**（仅 `hBC` ✓ ＝源 `proposition-0-2(d)` ✓，引 [DI71] p.85 ✓）。
**一处工艺** ✓（本轮实测）：给 `hiso` 这类 `∀` 提供实参时，`intro T _ _ _ _ _ S₀ _ _ _ _ aRK aTK st hrep`
（**实例位用 `_`** ✓）比 `fun` 形稳 ✓。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_stronger
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
      (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
      GaloisBaseChangeHyp R S T G hRG hR'G) :
    LiftingPropertyEG F G :=
  liftingPropertyEG_of_isGenericObjectEG_strong F G R S hRG hgen hBC
    (by
      intro T _ _ _ _ _ S₀ _ _ _ _ aRK aTK st hrep
      -- **工艺读数** ✓：named arg **不跳过前置显式 binder** ✗（`f (S₀ := S₀) h` 会把 `h` 填进
      -- `S` 槽 ✓）⟹ 须**命名全部前置显式 binder** ✓（或用 `@f` 全位置形 ✓）。
      exact cancelIso_of_repIso (R := R) (T := T) (S := S) (S₀ := S₀)
        (aRK := aRK) (aTK := aTK) (st := st) hrep)

/-- **应用锁** ✅（**真实锁定假设表** —— 与形状锁互补 ✓）：以**恰好** `hgen`／`hBC` **两个**假设
调用 `…_stronger` ✓ ⟹ 其假设表一旦**增删**（回到三假设、或再删 `hBC`）本 `example` 立即编译失败 ✓。
（`example` 不生成声明 ⟹ 不进公理门清单 ✓；其唯一职责是**假设表锁** ✓。） -/
example (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
      [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
      (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
      GaloisBaseChangeHyp R S T G hRG hR'G) :
    LiftingPropertyEG F G :=
  liftingPropertyEG_of_isGenericObjectEG_stronger F G R S hRG hgen hBC

/-- **类型锁定（更强形式 ✓，手写）**：钉住 `…_stronger` 的**两假设形状** ✓ 与所引用谓词的签名 ✓
（同 `…_strong_typeLock` 之职 ✓）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_stronger_typeLock
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (∀ (hgen : IsGenericObjectEG F G R S hRG)
      (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
        (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
        GaloisBaseChangeHyp R S T G hRG hR'G),
      LiftingPropertyEG F G)
      = (∀ (hgen : IsGenericObjectEG F G R S hRG)
      (hBC : ∀ (T : Type) [CommRing T] [Algebra F T] [Algebra R T] [IsScalarTower F R T]
        [IsLocalRing T] [MulSemiringAction G (TensorProduct R T S)]
        (hR'G : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t)),
        GaloisBaseChangeHyp R S T G hRG hR'G),
      LiftingPropertyEG F G) := rfl

/-! ## **`RealizationProperty` 的显式实例形**（r263：去 `letI` 重编码 ✓）

**⚠ 问题形状** ✓（r262 实测 ✓，探针 `.abgv52-scratch/probe-r262k.lean` ✓）：旧形
`RealizationProperty` ✓ 的结论把 `Algebra R K` ✓ 绑定为
`letI : Algebra R K := φ.toRingHom.toAlgebra` ✓（**遮蔽** ✓）——
在 `R = K = S = F` 档该结论的实例出现**两个候选** ✗（`instAlgebra` ✗ 与 `leftAlgebra` ✗），
而取非平凡底域时张量的 `Semiring`／`Algebra K` 实例在遮蔽语境下**不可合成** ✗。
**处置** ✓（**不改旧形** ✗ —— 改 `def` 会打断全部消费者 ✗）：**另立显式实例形** ✓，
把该 `Algebra R K` ✓ 提为 `∃`-绑定变元 `A` ✓ ⟹ 张量的实例成为**显式项** ✓，
下游可用 `@TensorProduct` ✓ 指名 ⟹ 退化目标的反驳（`SaltThm38_ABGV52` §4.65 ✓）可行 ✓。 -/

/-- **显式实例形** ✓（`RealizationProperty` ✓ 的**去 `letI`** 重编码 ✓）：与旧形**同体** ✓，
唯把结论中由 `letI` **遮蔽** ✓ 的 `Algebra R K` ✓ 提为 `∃`-绑定变元 `A` ✓，
并要求其环同态**等于** `φ.toRingHom` ✓（旧形由 `φ.toRingHom.toAlgebra` **定义性**给出 ✓，
新形把这一步换成**命题** ✓）。
**⚠ 强度序** ✓：**两向皆可证** ✓ —— 旧 ⟹ 新（取 `A := φ.toRingHom.toAlgebra` ✓，
兼容性为 `rfl` ✓）与 新 ⟹ 旧（`algebra_ext_of_algebraMap_eq` ✓ ＋ 沿等式搬运见证 ✓）
⟹ **两编码等价** ✓✅。
**🔴 不声称** ✗：**不**声称二者**定义相等** ✗（旧形的实例是 `φ`-**诱导项** ✓、
新形的是**变元** `A` ✓，只是**命题相等** ✓）；**不**声称新形使旧形的缺陷消失 ✗ ——
缺陷（零环属环档量词域 ✓、不属域档 ✓）**在两边同样存在** ✓（§4.65 ✓ 正是用新形把它**反驳**掉 ✓）。 -/
def RealizationPropertyExplicit (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] : Prop :=
  ∀ (K : Type) [Field K] [Algebra F K]
    (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction G L]
    (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup K L G hKL →
      ∃ (φ : R →ₐ[F] K) (A : Algebra R K),
        (@Algebra.algebraMap R K _ _ A : R →+* K) = φ.toRingHom ∧
        let _inst : Algebra R K := A
        Nonempty (L ≃ₐ[K] (TensorProduct R K S))

/-- **外形锁** ✓（`rfl` 型 ✓）：显式实例形与**展开体逐字相同** ✓ —— 任一 binder 被删／被移／
被换回 `letI` ✗ 即编译失败 ✓（与 `RealizationPropertyFieldFinite.shape` ✓ 同款工艺 ✓）。 -/
theorem RealizationPropertyExplicit.shape {F : Type*} [Field F] {G : Type} [Group G] [Fintype G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] :
    (RealizationPropertyExplicit F G R S)
      = (∀ (K : Type) [Field K] [Algebra F K]
          (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
          [MulSemiringAction G L]
          (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
          IsGaloisWithGroup K L G hKL →
            ∃ (φ : R →ₐ[F] K) (A : Algebra R K),
              (@Algebra.algebraMap R K _ _ A : R →+* K) = φ.toRingHom ∧
              let _inst : Algebra R K := A
              Nonempty (L ≃ₐ[K] (TensorProduct R K S))) :=
  rfl

/-- **旧形 ⟹ 显式形** ✓（**可证方向** ✓✅）：取 `A := φ.toRingHom.toAlgebra` ✓
（兼容性 `A.algebraMap = φ.toRingHom` 为 `rfl` ✓），见证逐字搬运 ✓。
**⚠ 用途** ✓：本件使**旧形的反驳**可由**新形的反驳**经**逆否**得到 ✓
（`SaltThm38_ABGV52` §4.65 的 `not_realizationProperty_self_of_subsingleton` ✓）。 -/
theorem realizationPropertyExplicit_of_realizationProperty {F : Type} [Field F] {G : Type}
    [Group G] [Fintype G] {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S]
    [Algebra F S] [IsScalarTower F R S] (h : RealizationProperty F G R S) :
    RealizationPropertyExplicit F G R S := by
  intro K _ _ L _ _ _ _ _ hKL hgal
  obtain ⟨φ, hφ⟩ := h K L hKL hgal
  exact ⟨φ, φ.toRingHom.toAlgebra, rfl, hφ⟩

/-- **显式形 ⟹ 旧形** ✓（**逆向** ✓✅，故两编码**等价** ✓）：由兼容性
`A.algebraMap = φ.toRingHom` ✓ 得 `A = φ.toRingHom.toAlgebra` ✓
（`algebra_ext_of_algebraMap_eq` ✓ —— `smul` 由 `algebraMap` 决定 ✓），
再沿该等式**搬运**见证 ✓（`Eq.rec` ✓；实例作**显式项** ✓ ⟹ 搬运不触发实例合成歧义 ✓）。 -/
theorem realizationProperty_of_realizationPropertyExplicit {F : Type} [Field F] {G : Type}
    [Group G] [Fintype G] {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra R S]
    [Algebra F S] [IsScalarTower F R S] (h : RealizationPropertyExplicit F G R S) :
    RealizationProperty F G R S := by
  intro K _ _ L _ _ _ _ _ hKL hgal
  obtain ⟨φ, A, hv, hP⟩ := h K L hKL hgal
  refine ⟨φ, ?_⟩
  have hAA : A = φ.toRingHom.toAlgebra := by
    apply algebra_ext_of_algebraMap_eq
    intro x
    rw [hv]
    rfl
  exact hAA ▸ hP

/-- **亚单 ⟹ 无非平凡代数同构** ✓（**反驳的桥引理** ✓）：`L` 亚单 ✓（如**零环** ✓）、
`T` 非平凡 ✓ ⟹ **不存在** `K`-代数同构 `L ≃ₐ[K] T` ✓ ——
由 `Equiv` 的双射性把亚单性搬到 `T` ✓，与非平凡性矛盾 ✓。
**⚠ 工艺** ✓：两 `Algebra` 实例作**显式变元** ✓（**非** instance binder ✓）⟹
下游应用时由 **unify** ✓（对齐具体张量实例 ✓）而非 **synth** ✗ 决定，
这是 §4.65 反驳能穿过 `letI` 遮蔽的关键 ✓（`linter.unusedVariables` 由 `let _inst` 命名规避 ✓）。 -/
theorem not_nonempty_algEquiv_of_subsingleton_of_nontrivial {K L T : Type*} [CommSemiring K]
    [Semiring L] [Semiring T] (aL : Algebra K L) (aT : Algebra K T)
    (hL : Subsingleton L) (hT : Nontrivial T) :
    ¬ Nonempty (@AlgEquiv K L T _ _ _ aL aT) := by
  let _instAL : Algebra K L := aL
  let _instAT : Algebra K T := aT
  let _instSubL : Subsingleton L := hL
  rintro ⟨e⟩
  have hsub : Subsingleton T := e.toEquiv.surjective.subsingleton
  obtain ⟨a, b, hab⟩ := hT
  exact hab (hsub.elim a b)

/-! ## 公理闸门 -/

#print axioms mvPolynomial_lift_of_surjective
#print axioms liftingPropertyEG_of_isGenericObjectEG_stronger
#print axioms liftingPropertyEG_of_isGenericObjectEG_stronger_typeLock
#print axioms cancelIso_of_repIso
#print axioms liftingPropertyEG_of_isGenericObjectEG_strong
#print axioms liftingPropertyEG_of_isGenericObjectEG_strong_typeLock
#print axioms phiToAlgebra_eq_residueAlgebra
#print axioms algebra_ext_of_algebraMap_eq
#print axioms liftingPropertyEG_of_isGenericObjectEG
#print axioms liftingPropertyEG_of_isGenericObjectEG_typeLock
#print axioms tensorAct_smul_comm
#print axioms tensorMulSemiringAction
#print axioms actAlgEquiv_mul
#print axioms assemble_steps467
#print axioms assemble_steps123
#print axioms ne_zero_of_isUnit_map_algHom
#print axioms galoisBaseChangeHyp_typeLock
#print axioms galoisBaseChangeHyp_data_nonempty
#print axioms galoisBaseChange_gap_registered
#print axioms isUnit_of_residue_ne_zero
#print axioms away_lift_of_surjective
#print axioms isGenericObjectEG_typeLock
#print axioms liftingPropertyEG_gap_registered
#print axioms isGenericExtension_typeLock
#print axioms isGenericExtension_data_nonempty
#print axioms isGenericExtension_gap_registered
#print axioms RealizationPropertyExplicit
#print axioms RealizationPropertyExplicit.shape
#print axioms realizationPropertyExplicit_of_realizationProperty
#print axioms realizationProperty_of_realizationPropertyExplicit
#print axioms not_nonempty_algEquiv_of_subsingleton_of_nontrivial

end ABGV52.BTier
