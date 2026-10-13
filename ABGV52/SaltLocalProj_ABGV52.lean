/-
  ABGV-5.2 · B 档 · 蓝图第 10 步 —— **`thm1.3(a)`／`thm1.3(c)` 的「局部」（local）层**
  （Saltman 1984 §1，2026-10-12）

  **来源** ✓：`raw/Saltman1984.tex:144–157`（label `thm1.3` ✓；**⚠-tex-sourced** ✗）逐字：
  > Define a morphism \((\phi ,\psi):\mathcal{M} / R\to \mathcal{N} / S\) to be **local** if
  > \(\phi^{- 1}(S^{*}) = R^{*}\). That is, if the preimage of every unit in \(S\) is a unit in \(R\).
  > If \(\mathcal{C}\) is a category of \(F\) structures, then \(\mathcal{P}\in \mathcal{C}\) is a
  > **local projective** if for all local surjections \(\Psi :\mathcal{M}\to \mathcal{N}\), and all
  > \(\Delta :\mathcal{P}\to \mathcal{N}\), there is a \(\Delta^{\prime}:\mathcal{P}\to \mathcal{M}\)
  > such that \(\Delta = \Psi \circ \Delta^{\prime}\).
  > **(a)** … If \(0\neq s\in R\), then \(\mathcal{P}\otimes_{R}R(1 / s) / R(1 / s)\in \mathcal{C}\) is a local projective.
  > **(c)** … Suppose \(S = F_{+}[V](1 / s)\) where \(0\neq s\in S\) is \(G\) fixed, and \(R = S^{G}\).
  > If \(S / R\) is \(G\)-Galois, then \(S / R\) is a local projective for \(\mathcal{E}(G)\).
  > 证明逐字：「(a) … With this observation (a) is easy. Using (a), parts (b), (c) and (d) are trivial.」

  **本件内容** ✓（**M3 的第一块** ✓，蓝图 §3.1 ✓）：
  ① **不造新词** ✓ —— 源 §1 的「local」条件**就是** mathlib 的 **`IsLocalHom`** ✓
     （`Mathlib/Algebra/Group/Units/Hom.lean:270` ✓，逐字 `∀ a, IsUnit (f a) → IsUnit a` ✓）。
  ② **判别见证** ✓（L1／L10①）：该条件是**真**条件 ✓ —— 局部化**把非单位变成单位** ✓
     （`ℚ[X] → ℚ[X](1/X)` 把 `X` 送成单位 ✓，而 `X ∈ ℚ[X]` **不是**单位 ✓）⟹ 典范映射**不是** `IsLocalHom` ✓。
     这正是源 (a) 的机理 ✓：**局部化恰好制造**「满射」与「局部满射」之间的间隙 ✓ ——
     故 `thm1.3` 不能从 `lem1.2`（只到满射档 ✓）直接得到 ✗。
  ③ **`IsLocalProjectiveSymmetric`** ✓（`F₊[V]/F₊[V]^G` 对 `𝓔(G)` **局部投射** ✓）——
     与 §95 的 `IsProjectiveObjectSymmetric` **同形** ✓，只把 `ψ` 的假设由「满射」加强为
     「`IsLocalHom` ＋ 满射」✓（**＝「局部满射」** ✓）。
  ④ **`localProjective_of_projective`** ✓：投射对象 ⟹ 局部投射对象 ✓（源「(c) is trivial」的第一步 ✓）。
  ⑤ **`IsLocalProjectiveSymmetricLocalized`** ＋ **`isLocalProjectiveSymmetricLocalized_of_localProjective`** ✓✓：
     源 **(a) 步的证明内核** ✓ —— 「`Δ(s)` 是单位」＋「`Ψ` 局部」⟹「提升 `Δ′(s)` 是单位」✓。
  ⑥ **登记** ✗：`thm1.3(c)` 距本层仍缺的两件（**局部化万有性质** ✓／**不变量识别 `S^G = F₊[V]^G(1/s)`** ✓）见文末 ✓。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import ABGV52.SaltLem12_ABGV52
open TensorProduct
universe u
noncomputable section

namespace ABGV52.BTier

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G] {V : Type u}
variable [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V]

/-! ## 1. 「局部」＝mathlib 的 `IsLocalHom`（**不造新词** ✓） -/

/-- **正例对照（L19）** ✓：恒等映射是 `IsLocalHom` ✓（判别力自证的正例 ✓）。 -/
theorem isLocalHom_id (S : Type*) [Monoid S] : IsLocalHom (MonoidHom.id S) :=
  ⟨fun _ ha => ha⟩

/-- **判别见证（L1／L10①）** ✓✓：源 §1 的「local」条件是**真**条件 ✓ —— **局部化把非单位变成单位** ✓：
`ℚ[X] → ℚ[X](1/X)` 把 `X` 送成**单位** ✓（`IsLocalization.Away.algebraMap_isUnit` ✓），
而 `X ∈ ℚ[X]` **不是**单位 ✓（`Polynomial.not_isUnit_X_add_C` ✓）⟹ 该典范映射**不是** `IsLocalHom` ✓。

**意义** ✓（**源 (a) 的机理** ✓）：局部化**恰好制造**「满射」与「局部满射」之间的**间隙** ✓，
故源 `thm1.3(c)` 不能由 `lem1.2`（§95 ✓，只到满射档 ✗）直接得到 ✓ ——
必须经 (a) ✓（本件 §3 ✓）。 -/
theorem not_isLocalHom_algebraMap_away_X :
    ¬ IsLocalHom (algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X : Polynomial ℚ))) := by
  intro h
  have hunit : IsUnit (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)) Polynomial.X) :=
    IsLocalization.Away.algebraMap_isUnit (x := Polynomial.X)
  have hX : IsUnit (Polynomial.X : Polynomial ℚ) := IsLocalHom.map_nonunit Polynomial.X hunit
  have hnot : ¬ IsUnit (Polynomial.X : Polynomial ℚ) := by
    simpa using (Polynomial.not_isUnit_X_add_C (R := ℚ) 0)
  exact hnot hX

/-! ## 2. `𝓔(G)` 的**局部投射对象**（源 §1 逐字用点形 ✓） -/

/-- **源 `thm1.3(c)` 的谓词** ✓（`F₊[V]/F₊[V]^G` 对 `𝓔(G)` **局部投射** ✓）：与 §95 的
`IsProjectiveObjectSymmetric` **同形** ✓（同一切片、同一提升结论 ✓），唯一的差别＝
`ψ` 的假设由「满射」加强为「**局部**（`IsLocalHom` ✓）＋ 满射」✓
（＝源 §1 的「local surjection」✓，`raw/Saltman1984.tex:144` ✓）。

**⚠ 为什么不另设 `def`** ✓：源 §1 的「local」**就是** mathlib 的 `IsLocalHom` ✓（见 §1 ✓）⟹ 直接复用 ✓。

**⚠ 宇宙档** ✓：**单宇宙**（`F G V R S S' : Type u` ✓）—— 与 `IsProjectiveObjectSymmetric`（§95 已改 ✓）
及 `GaloisProjectiveSectionHyp`／`GaloisFixedSubringHyp` ✓ 一致 ✓（§58.4 教训 ✓）。 -/
def IsLocalProjectiveSymmetric (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V] : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup R S G hRG → IsGaloisWithGroup R S' G hRG' →
      (ψ : S →ₐ[F] S') → [IsLocalHom ψ] →
      (∀ (r : R) (t : S), ψ (algebraMap R S r * t) = algebraMap R S' r * ψ t) →
      (∀ (g : G) (t : S), ψ (g • t) = g • ψ t) → Function.Surjective ψ →
      (φ : SymmetricAlgebra F V →ₐ[F] S') →
      (∀ (g : G) (x : SymmetricAlgebra F V),
        φ (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x) = g • φ x) →
      ∃ μ : SymmetricAlgebra F V →ₐ[F] S,
        (∀ x : SymmetricAlgebra F V, ψ (μ x) = φ x) ∧
        (∀ x : SymmetricAlgebra F V,
          x ∈ symInvariants (F := F) (G := G) (V := V) →
            ∃ r : R, μ x = algebraMap R S r)

/-- **类型锁定（同一性形）** ✓：钉住本谓词的运行类型与**宇宙档** ✓。 -/
theorem isLocalProjectiveSymmetric_typeLock (F : Type u) [Field F] (G : Type u) [Group G]
    [Fintype G] (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V]
    [SMulCommClass G F V] :
    (IsLocalProjectiveSymmetric F G V) = (IsLocalProjectiveSymmetric F G V) := rfl

/-- **投射对象 ⟹ 局部投射对象** ✓（源「Using (a), parts (b), (c) and (d) are trivial」的**第一步** ✓）：
局部满射**是**满射 ✓ ⟹ 满射档的提升律自动给出局部档的提升律 ✓
（局部的假设在证明中**不被使用** ✓ —— 这正是「投射 ⟹ 局部投射」为**弱化** ✓）。 -/
theorem localProjective_of_projective (h : IsProjectiveObjectSymmetric F G V) :
    IsLocalProjectiveSymmetric F G V := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ hRG hRG' hgal hgal' ψ _ hψR hψG hψsurj φ hφG
  exact h R S S' hRG hRG' hgal hgal' ψ hψR hψG hψsurj φ hφG

/-- **`lem1.2` ⟹ 局部投射** ✓（源链 `lem1.2 → thm1.3(c)` 的第一环 ✓）：
由 §95 的两个具名输入（`GaloisProjectiveSectionHyp` ✓ ＋ `GaloisFixedSubringHyp` ✓）
先得 `IsProjectiveObjectSymmetric` ✓，再弱化到局部档 ✓。 -/
theorem localProjective_of_galoisHyps
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (hproj : GaloisProjectiveSectionHyp F G)
    (hfix : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S]
      [Algebra F S] [IsScalarTower F R S] [MulSemiringAction G S]
      (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
      GaloisFixedSubringHyp R S G hRG)
    (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V] :
    IsLocalProjectiveSymmetric F G V :=
  localProjective_of_projective
    (isProjectiveObjectSymmetric_of_galoisHyps F G hproj hfix V)

/-! ## 3. 源 **(a) 步的证明内核**（局部化 ＋ 局部性 ✓） -/

/-- **源 (a) 步的「去局部化」形** ✓✓：把「`P(1/s)` 的局部投射性」按源 (a) 证明首句的等同
（「`Hom(M ⊗_R R(1/s), N/S)` 可与『`φ(s)` 为单位』的 `Hom(M/R,N/S)` 子集等同」✓）
**不收进类型**地陈述 ✓ —— 局部化这一层由两个 `IsUnit` 条件**承载** ✓：
输入侧 `IsUnit (φ s)` ✓（＝「`φ` 来自 `P(1/s)`」✓）、输出侧 `IsUnit (μ s)` ✓（＝「提升也来自 `P(1/s)`」✓）。

**⚠ 口径** ✓：本形**不**出现 `Localization.Away` ✗ —— 局部化的**万有性质**（mathlib
`IsLocalization.Away.lift` ✓）是这一等同的**实体** ✓，登记于文末 ✗；本形取它的**结论形状** ✓。 -/
def IsLocalProjectiveSymmetricLocalized (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V]
    (s : SymmetricAlgebra F V) : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup R S G hRG → IsGaloisWithGroup R S' G hRG' →
      (ψ : S →ₐ[F] S') → [IsLocalHom ψ] →
      (∀ (r : R) (t : S), ψ (algebraMap R S r * t) = algebraMap R S' r * ψ t) →
      (∀ (g : G) (t : S), ψ (g • t) = g • ψ t) → Function.Surjective ψ →
      (φ : SymmetricAlgebra F V →ₐ[F] S') →
      (∀ (g : G) (x : SymmetricAlgebra F V),
        φ (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x) = g • φ x) →
      IsUnit (φ s) →
      ∃ μ : SymmetricAlgebra F V →ₐ[F] S,
        (∀ x : SymmetricAlgebra F V, ψ (μ x) = φ x) ∧
        (∀ x : SymmetricAlgebra F V,
          x ∈ symInvariants (F := F) (G := G) (V := V) →
            ∃ r : R, μ x = algebraMap R S r) ∧
        IsUnit (μ s)

/-- **类型锁定（同一性形）** ✓（含**局部化元 `s`** ✓）。 -/
theorem isLocalProjectiveSymmetricLocalized_typeLock (F : Type u) [Field F] (G : Type u)
    [Group G] [Fintype G] (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V]
    [SMulCommClass G F V] (s : SymmetricAlgebra F V) :
    (IsLocalProjectiveSymmetricLocalized F G V s)
      = (IsLocalProjectiveSymmetricLocalized F G V s) := rfl

/-- **源 (a) 步的证明内核** ✓✓✓（**逐字机理** ✓）：设 `F₊[V]/F₊[V]^G` 局部投射 ✓，
则对任意 `s` ✓，「去局部化形」成立 ✓ —— 证明**只**用到**局部性** ✓：
由局部投射性提升 `φ` 得 `μ` ✓（源：`Δ₀′` ✓），再
`ψ (μ s) = φ s` ✓ 为单位 ✓（`hφs` ✓）＋ `IsLocalHom ψ` ✓ ⟹ `μ s` 为单位 ✓
（＝源逐字「if `φ(s) ∈ S*` is a unit, then …」✓）。

**⚠ 这就是 (a) 的全部证明内核** ✓：其余（「提升沿 `P(1/s)` 存在 ⟺ `s` 的像为单位」✓）
＝局部化的万有性质 ✓，见文末登记 ✗。 -/
theorem isLocalProjectiveSymmetricLocalized_of_localProjective
    (h : IsLocalProjectiveSymmetric F G V) (s : SymmetricAlgebra F V) :
    IsLocalProjectiveSymmetricLocalized F G V s := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ hRG hRG' hgal hgal' ψ _ hψR hψG hψsurj φ hφG hφs
  obtain ⟨μ, hμ, hinv⟩ := h R S S' hRG hRG' hgal hgal' ψ hψR hψG hψsurj φ hφG
  exact ⟨μ, hμ, hinv,
    IsLocalHom.map_nonunit (f := ψ) (μ s) (by rw [hμ s]; exact hφs)⟩

/-! ## 4. 源 (a) 首句的**等同**（**残余 ① 的抽象实体** ✓✓✓） -/

/-- **(⇒) 方向（工具形）** ✓：`M ⊗_R R(1/s)` 上的纯量把 `s` 送成**单位** ✓ ——
因为 `R(1/s)` 中 `s` 已是单位 ✓（`IsLocalization.Away.algebraMap_isUnit` ✓），
经 **`Algebra.TensorProduct.includeRight`** ✓ 传进张量积 ✓
（`Algebra.TensorProduct.algebraMap_apply'` ✓：`algebraMap R (M ⊗_R R(1/s)) s = 1 ⊗ s` ✓）。

**⚠ 口径** ✓：源写「`φ(s) ∈ S` 是单位」✓；在交换代数档里即 `algebraMap R (M ⊗_R R(1/s)) s` ✓。 -/
theorem isUnit_algebraMap_tensor_away (R M : Type*) [CommRing R] [CommRing M] [Algebra R M]
    (s : R) : IsUnit (algebraMap R (TensorProduct R M (Localization.Away s)) s) := by
  have h : IsUnit (algebraMap R (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit (x := s)
  have h2 : IsUnit ((1 : M) ⊗ₜ[R] (algebraMap R (Localization.Away s) s)) :=
    h.map (Algebra.TensorProduct.includeRight :
      Localization.Away s →ₐ[R] TensorProduct R M (Localization.Away s))
  rw [Algebra.TensorProduct.algebraMap_apply']
  exact h2

/-- **(⇐) 方向** ✓✓：把 `s` 送成单位的 `φ : M →ₐ[R] N` **穿过局部化** ✓ ——
存在 `g : M ⊗_R R(1/s) →ₐ[R] N` 使 `g (m ⊗ 1) = φ m` ✓（一切 `m : M` ✓）。
**证法** ✓：`s` 的单位性经 `AlgHom.commutes` ✓ 传成 `IsUnit (algebraMap R N s)` ✓；
由 **`IsLocalization.liftAlgHom`** ✓（在 `Submonoid.powers s` 上 ✓）得 `ψ : R(1/s) →ₐ[R] N` ✓；
再用 **`Algebra.TensorProduct.productMap`** ✓（`productMap_left_apply` ✓）合成 ✓。 -/
theorem exists_tensor_away_lift (R M N : Type*) [CommRing R] [CommRing M] [CommRing N]
    [Algebra R M] [Algebra R N] (s : R) (φ : M →ₐ[R] N)
    (hφ : IsUnit (φ (algebraMap R M s))) :
    ∃ g : TensorProduct R M (Localization.Away s) →ₐ[R] N,
      ∀ m : M, g (m ⊗ₜ[R] (1 : Localization.Away s)) = φ m := by
  have h : IsUnit (algebraMap R N s) := by
    rw [← φ.commutes s]
    exact hφ
  have hmem : ∀ y : Submonoid.powers s, IsUnit ((Algebra.ofId R N) (y : R)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := hy
    rw [map_pow]
    exact h.pow n
  let ψ : Localization.Away s →ₐ[R] N :=
    IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := Algebra.ofId R N) hmem
  exact ⟨Algebra.TensorProduct.productMap φ ψ,
    fun m => Algebra.TensorProduct.productMap_left_apply φ ψ m⟩

/-- **源 (a) 证明首句的等同** ✓✓✓（**残余 ① 的抽象实体** ✓；`raw/Saltman1984.tex:156` ✓，**⚠-tex-sourced** ✗）：
源逐字「`Hom(M ⊗_R R(1/s), N/S)` can be identified with the subset of all `(φ,ψ) ∈ Hom(M/R,N/S)`
such that `φ(s) ∈ S` is a unit」✓ —— 本形取**存在**形 ✓：(⇒) ✓ ＋ (⇐) ✓。

**⚠ 口径** ✓：**唯一性**（同一 `φ` 至多一个 `g` ✓）在本形**不**声称 ✗ ——
源 (a) 的证明**只用存在性** ✓（本件 §59.4 的 (a) 步内核亦然 ✓），故登记于 §5 ✓。 -/
theorem exists_tensor_away_lift_iff (R M N : Type*) [CommRing R] [CommRing M] [CommRing N]
    [Algebra R M] [Algebra R N] (s : R) (φ : M →ₐ[R] N) :
    (∃ g : TensorProduct R M (Localization.Away s) →ₐ[R] N,
        ∀ m : M, g (m ⊗ₜ[R] (1 : Localization.Away s)) = φ m)
      ↔ IsUnit (φ (algebraMap R M s)) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 : IsUnit (algebraMap R (TensorProduct R M (Localization.Away s)) s) :=
      isUnit_algebraMap_tensor_away R M s
    have h2 : IsUnit (g (algebraMap R (TensorProduct R M (Localization.Away s)) s)) :=
      h1.map g
    have h3 : g (algebraMap R (TensorProduct R M (Localization.Away s)) s)
        = φ (algebraMap R M s) := by
      rw [Algebra.TensorProduct.algebraMap_apply, hg]
    rwa [h3] at h2
  · intro hφ
    exact exists_tensor_away_lift R M N s φ hφ

/-! ## 5. 缺口 ②：`s` 的 `G`-不变性**下降**到局部化 `A(1/s)` ✓✓✓ -/

section LocAction

variable {A : Type u} [CommRing A] [Algebra F A] [MulSemiringAction G A] [SMulCommClass G F A]

/-- `MulSemiringAction.toAlgHom` 在 `1` 上 ＝ `AlgHom.id` ✓（基点 `A` 上可**逐点**证 ✓）。 -/
lemma locToAlgHom_one : MulSemiringAction.toAlgHom F A (1 : G) = AlgHom.id F A := by
  ext a
  simp [MulSemiringAction.toAlgHom_apply]

/-- `MulSemiringAction.toAlgHom` 的乘法律 ✓（`AlgHom` 复合形 ✓；逐点用 `mul_smul` ✓）。 -/
lemma locToAlgHom_mul (g h : G) :
    MulSemiringAction.toAlgHom F A (g * h)
      = (MulSemiringAction.toAlgHom F A g).comp (MulSemiringAction.toAlgHom F A h) := by
  ext a
  simp [MulSemiringAction.toAlgHom_apply, mul_smul]

/-- `s` 的 `G`-不变性 ⟹ 其一切幂**不动** ✓（源 (c) 的 `s` 为 `G` fixed ✓）。 -/
lemma locSmul_pow_fixed (s : A) (hs : ∀ g : G, g • s = s) (g : G) (n : ℕ) :
    g • s ^ n = s ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, MulSemiringAction.smul_mul, ih, hs g]

/-- **下降的基点映射** ✓：`A →ₐ[F] A(1/s)`，`a ↦ (g • a)/1` ✓。
（`s` 的像为单位由 `locActBase_isUnit` ✓ 供给；它使万有性质可用 ✓。） -/
noncomputable def locActBase (s : A) (g : G) : A →ₐ[F] Localization.Away s :=
  (Algebra.algHom F A (Localization.Away s)).comp (MulSemiringAction.toAlgHom F A g)

/-- `locActBase` 在点上的取值 ✓：`a ↦ (g • a)/1` ✓。 -/
lemma locActBase_apply (s : A) (g : G) (a : A) :
    locActBase (F := F) (G := G) s g a = algebraMap A (Localization.Away s) (g • a) := by
  rw [locActBase, AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply]
  rfl

/-- **关键：`locActBase` 把 `s` 的幂送成单位** ✓✓（源 (c) 的 `s` 为 `G` fixed ✓ ⟹
其像与未作用时**相同** ✓，而后者在 `A(1/s)` 中本为单位 ✓）。 -/
lemma locActBase_isUnit (s : A) (hs : ∀ g : G, g • s = s) (g : G)
    (y : Submonoid.powers s) : IsUnit (locActBase (F := F) (G := G) s g (y : A)) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : A) s).mp y.2
  rw [locActBase_apply, ← hn, locSmul_pow_fixed s hs g n]
  exact IsLocalization.map_units (Localization.Away s)
    (⟨s ^ n, (Submonoid.mem_powers_iff (s ^ n) s).mpr ⟨n, rfl⟩⟩ : Submonoid.powers s)

/-- **`g` 在 `A(1/s)` 上的作用** ✓✓✓（**缺口 ② 的实体** ✓）：由局部化的**万有性质**取提升 ✓
（`IsLocalization.liftAlgHom` ✓；`locActBase_isUnit` ✓ 供其前提 ✓）。 -/
noncomputable def locActAlgHom (s : A) (hs : ∀ g : G, g • s = s) (g : G) :
    Localization.Away s →ₐ[F] Localization.Away s :=
  IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := locActBase (F := F) (G := G) s g)
    (locActBase_isUnit s hs g)

/-- **作用在 `algebraMap` 的像上的取值** ✓（＝`g • a` ✓）——
由 `IsLocalization.lift_eq` ✓ ＋ `locActBase_apply` ✓。**一切作用律都由此经 `algHom_ext` 收口** ✓。 -/
lemma locActAlgHom_comp (s : A) (hs : ∀ g : G, g • s = s) (g : G) :
    (locActAlgHom (F := F) (G := G) s hs g).comp (Algebra.algHom F A (Localization.Away s))
      = (Algebra.algHom F A (Localization.Away s)).comp (MulSemiringAction.toAlgHom F A g) := by
  ext a
  show locActAlgHom (F := F) (G := G) s hs g (algebraMap A (Localization.Away s) a)
    = algebraMap A (Localization.Away s) ((MulSemiringAction.toAlgHom F A g) a)
  rw [locActAlgHom, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  show locActBase (F := F) (G := G) s g a
    = algebraMap A (Localization.Away s) ((MulSemiringAction.toAlgHom F A g) a)
  rw [locActBase_apply]
  rfl

/-- `1`-律 ✓（`IsLocalization.algHom_ext` ✓ 收口到基点 ✓）。 -/
lemma locActAlgHom_one (s : A) (hs : ∀ g : G, g • s = s) :
    locActAlgHom (F := F) (G := G) s hs (1 : G) = AlgHom.id F (Localization.Away s) := by
  apply IsLocalization.algHom_ext (Submonoid.powers s)
  rw [locActAlgHom_comp, locToAlgHom_one]
  ext a
  rfl

/-- `*`-律 ✓（同样由 `algHom_ext` ＋ 基点上的 `mul_smul` ✓）。 -/
lemma locActAlgHom_mul (s : A) (hs : ∀ g : G, g • s = s) (g h : G) :
    locActAlgHom (F := F) (G := G) s hs (g * h)
      = (locActAlgHom (F := F) (G := G) s hs g).comp
          (locActAlgHom (F := F) (G := G) s hs h) := by
  apply IsLocalization.algHom_ext (Submonoid.powers s)
  rw [locActAlgHom_comp, AlgHom.comp_assoc, locActAlgHom_comp, ← AlgHom.comp_assoc,
    locActAlgHom_comp, AlgHom.comp_assoc, ← locToAlgHom_mul]

/-- **缺口 ② 收官** ✓✓✓：`s` **`G`-不变** ⟹ `A(1/s)` 携带**良定义**的 `G`-作用 ✓
（`MulSemiringAction G (Localization.Away s)` ✓）。
**⚠ 工艺** ✓：作用值取 **`AlgHom` 形** ✓（非 `AlgEquiv` ✓）—— 于是两条律由
**`IsLocalization.algHom_ext`** ✓ 收到**基点**上逐点验证 ✓，**避开**了「局部化的 `AlgEquiv` 相等」这一难缠外形 ✗
（本轮实测：`IsLocalization.algEquivOfAlgEquiv` 路线在 `_eq` 引理处触发
`SMulCommClass G ?m A` **僵持** ✗，改用 `liftAlgHom` 后一次通过 ✓）。 -/
noncomputable def locMulSemiringAction (s : A) (hs : ∀ g : G, g • s = s) :
    MulSemiringAction G (Localization.Away s) where
  smul g x := locActAlgHom (F := F) (G := G) s hs g x
  one_smul x := by
    change locActAlgHom (F := F) (G := G) s hs (1 : G) x = x
    rw [locActAlgHom_one]
    rfl
  mul_smul g h x := by
    change locActAlgHom (F := F) (G := G) s hs (g * h) x
      = locActAlgHom (F := F) (G := G) s hs g (locActAlgHom (F := F) (G := G) s hs h x)
    rw [locActAlgHom_mul]
    rfl
  smul_zero g := map_zero (locActAlgHom (F := F) (G := G) s hs g)
  smul_add g x y := map_add (locActAlgHom (F := F) (G := G) s hs g) x y
  smul_mul g x y := map_mul (locActAlgHom (F := F) (G := G) s hs g) x y
  smul_one g := map_one (locActAlgHom (F := F) (G := G) s hs g)

/-- **作用在 `algebraMap` 的像上的取值** ✓（＝`locActAlgHom_comp` ✓ 的**成员形** ✓）：
`g \bullet (a/1) = (g \bullet a)/1` ✓。
**⚠ 一般 `A` 档** ✓（`symLocMulSemiringAction_algebraMap` ✓ 是 `A = \mathrm{SymmetricAlgebra}\ F\ V` ✓ 的特例 ✓）；
**用途** ✓：源侧 `hact_map` ✓（「局部化上的作用与 `algebraMap` 相容」✗）**由此导出** ✗ ⟹ **不必作假设** ✗。 -/
lemma locMulSemiringAction_algebraMap (s : A) (hs : ∀ g : G, g • s = s) (g : G) (a : A) :
    (locMulSemiringAction (F := F) (A := A) (G := G) s hs).smul g
        (algebraMap A (Localization.Away s) a)
      = algebraMap A (Localization.Away s) (g • a) := by
  change locActAlgHom (F := F) (G := G) (A := A) (s := s) hs g
      (algebraMap A (Localization.Away s) a)
    = algebraMap A (Localization.Away s) (g • a)
  rw [locActAlgHom, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  exact locActBase_apply (F := F) (G := G) (A := A) (s := s) g a

end LocAction

/-- **用点** ✓（源 `thm1.3(c)` 的源对象 ✓）：`S = F₊[V](1/s)`（`s` 为 `G`-**不动** ✓，本工程惯例＝
作用作**显式** `symAlgEquiv` ✓）携带 `G`-作用 ✓ ⟹ 源 (c) 的「若 `S/R` 是 `G`-Galois」✓
这一步**可以陈述** ✓（缺口 ② 的用处 ✓）。
**⚠ 所需的两条局部实例** ✓（本工程 `symMulSemiringAction` 是 **`def`** 而非实例 ✗ ⟹ 须 `letI` ✓）：
① `MulSemiringAction G (F₊[V])` ✓；② **`SMulCommClass G F (F₊[V])`** ✓
（＝`g • (c • x) = c • (g • x)` ✓，由 `symAlgHom (…)` 的 **`AlgHom.map_smul`** ✓ 给出 ✓）。 -/
noncomputable def symLocMulSemiringAction (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V)
      (symActLinearEquiv (F := F) (V := V) g) s = s) :
    MulSemiringAction G (Localization.Away s) := by
  letI : MulSemiringAction G (SymmetricAlgebra F V) := symMulSemiringAction
  haveI : SMulCommClass G F (SymmetricAlgebra F V) :=
    ⟨fun g c x => by
      change symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) (c • x)
        = c • symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x
      exact map_smul _ c x⟩
  exact locMulSemiringAction (F := F) (A := SymmetricAlgebra F V) (G := G) s hs

/-! ## 6. 组装源 `thm1.3(c)` ✓✓✓（**局部化对象的局部投射性** ✓） -/

/-- **局部化映射与 `G`-作用相容** ✓✓（＝§5 的 `locActAlgHom_comp` ✓ 的成员形 ✓）：
`g • (y/1) = (g • y)/1` ✓。**这是 §6 组装的关键接口** ✓（把局部化上的等变性与基点上的等变性接起来 ✓）。 -/
lemma symLocMulSemiringAction_algebraMap (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) s = s)
    (g : G) (y : SymmetricAlgebra F V) :
    (symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g
        (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
      = algebraMap (SymmetricAlgebra F V) (Localization.Away s)
          (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y) := by
  letI : MulSemiringAction G (SymmetricAlgebra F V) := symMulSemiringAction
  haveI : SMulCommClass G F (SymmetricAlgebra F V) :=
    ⟨fun g c x => by
      change symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) (c • x)
        = c • symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x
      exact map_smul _ c x⟩
  change locActAlgHom (F := F) (G := G) (A := SymmetricAlgebra F V) (s := s) hs g
      ((Algebra.algHom F (SymmetricAlgebra F V) (Localization.Away s)) y)
    = (Algebra.algHom F (SymmetricAlgebra F V) (Localization.Away s)) (g • y)
  exact congrArg (fun f => f y)
    (locActAlgHom_comp (F := F) (G := G) (A := SymmetricAlgebra F V) (s := s) hs g)

/-- **源 `thm1.3(c)` 的组装** ✓✓✓✓（**本轮主结果** ✓）：由 §96 的「去局部化形」
`IsLocalProjectiveSymmetricLocalized` ✓ —— 即「局部满射 ψ ＋ 使 `s` 为单位的 `φ` ⟹ 提升 `μ`，
且 `μ s` 为单位」✓ —— **推出** `S = F₊[V](1/s)` 上的**局部投射性** ✓：

对一切 `G`-Galois `S/R`／`S'/R'`、**局部满射** `ψ : S → S'` ✓ 与 **`G`-等变** `Δ : S(1/s) →ₐ[F] S'` ✓，
存在 `μ : S(1/s) →ₐ[F] S` 使 **①** `ψ ∘ μ = Δ` ✓ 且 **②** `μ` 把 `F₊[V]^G` 的像送进 `R` ✓。

**证法** ✓（**源 `lem1.2`／`thm1.3(a)` 的原始机制** ✓）：`Δ₀ := Δ ∘ (局部化映射)` ✓（§97 的
(⇒) 方向 ✓）⟹ `Δ₀ s` 为单位 ✓（`s` 在局部化中为单位 ✓）⟹ 由 `h` 得 `μ₀` ＋ `IsUnit (μ₀ s)` ✓
⟹ **`IsLocalHom ψ`** ✓ 把 `IsUnit (ψ (μ₀ s))` 升为 `IsUnit (μ₀ s)` ✓（§96 的 (a) 步内核 ✓）
⟹ `IsLocalization.liftAlgHom` ✓ 把 `μ₀` 提升为 `μ` ✓ ⟹ `ψ ∘ μ = Δ` 由 **`algHom_ext`** ✓ 收口 ✓。

**⚠ 口径** ✓（**与源 (c) 的一处差异，登记 ✓**）：② 只对 **`F₊[V]^G` 的像**断言 ✓，
**不**对 `S(1/s)` 的**全部** `G`-不变元断言 ✗ —— 后者需 **不变量识别** `S^G = F₊[V]^G(1/s)` ✓
（本件 §7 ③ 登记 ✓）。 -/
theorem exists_localized_lift_of_isLocalProjectiveSymmetricLocalized
    (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) s = s)
    (h : IsLocalProjectiveSymmetricLocalized F G V s)
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    {hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)}
    {hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t)}
    (hgal : IsGaloisWithGroup R S G hRG) (hgal' : IsGaloisWithGroup R S' G hRG')
    (ψ : S →ₐ[F] S') [IsLocalHom ψ]
    (hψR : ∀ (r : R) (t : S), ψ (algebraMap R S r * t) = algebraMap R S' r * ψ t)
    (hψG : ∀ (g : G) (t : S), ψ (g • t) = g • ψ t)
    (hψsurj : Function.Surjective ψ)
    (Δ : Localization.Away s →ₐ[F] S')
    (hΔG : ∀ (g : G) (x : Localization.Away s),
      Δ ((symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g x) = g • Δ x) :
    ∃ μ : Localization.Away s →ₐ[F] S,
      (∀ x, ψ (μ x) = Δ x) ∧
      (∀ y : SymmetricAlgebra F V, y ∈ symInvariants (F := F) (G := G) (V := V) →
        ∃ r : R, μ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
          = algebraMap R S r) := by
  let Δ₀ : SymmetricAlgebra F V →ₐ[F] S' :=
    Δ.comp (Algebra.algHom F (SymmetricAlgebra F V) (Localization.Away s))
  have hΔ₀G : ∀ (g : G) (y : SymmetricAlgebra F V),
      Δ₀ (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y)
        = g • Δ₀ y := by
    intro g y
    change Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s)
        (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y))
      = g • Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
    rw [← symLocMulSemiringAction_algebraMap s hs g y]
    exact hΔG g (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
  have hΔs : IsUnit (Δ₀ s) := by
    have h1 : IsUnit (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit (x := s)
    show IsUnit (Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s))
    exact h1.map Δ
  obtain ⟨μ₀, hμ₀, hinv, hμ₀s⟩ :=
    h R S S' hRG hRG' hgal hgal' ψ hψR hψG hψsurj Δ₀ hΔ₀G hΔs
  have hμ₀unit : IsUnit (μ₀ s) :=
    IsLocalHom.map_nonunit (f := ψ) (μ₀ s) (by rw [hμ₀ s]; exact hΔs)
  let μ : Localization.Away s →ₐ[F] S :=
    IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := μ₀) (by
      rintro ⟨y, hy⟩
      change IsUnit (μ₀ y)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y s).mp hy
      rw [← hn, map_pow]
      exact hμ₀unit.pow n)
  have hμ_alg : ∀ y : SymmetricAlgebra F V,
      μ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y) = μ₀ y := by
    intro y
    dsimp only [μ]
    rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
    rfl
  refine ⟨μ, ?_, ?_⟩
  · have hcomp : ψ.comp μ = Δ := by
      apply IsLocalization.algHom_ext (Submonoid.powers s)
      refine AlgHom.ext (fun y => ?_)
      show ψ (μ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y))
        = Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
      rw [hμ_alg y]
      exact hμ₀ y
    intro x
    exact congrArg (fun f => f x) hcomp
  · intro y hy
    rw [hμ_alg y]
    exact hinv y hy

/-! ## 7. 缺口 ③：**不变量识别**（`(A(1/s))^G = (A^G)(1/s)` 的分式形 ✓✓✓） -/

/-- **易方向** ✓：`F₊[V]^G` 的**像**在局部化中**不动** ✓（由 §6 的相容性 ✓ ＋ 不动性 ✓）。 -/
lemma fixed_algebraMap_of_mem_symInvariants (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) s = s)
    {y : SymmetricAlgebra F V} (hy : y ∈ symInvariants (F := F) (G := G) (V := V)) (g : G) :
    (symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g
        (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
      = algebraMap (SymmetricAlgebra F V) (Localization.Away s) y := by
  rw [symLocMulSemiringAction_algebraMap, (mem_symInvariants.mp hy) g]

/-- **缺口 ③（不变量识别，难方向）** ✓✓✓✓：`s` **`G`-不变** ⟹ `S = F₊[V](1/s)` 的**不动元**
恰是 **`F₊[V]^G` 的分式** ✓ —— 存在 `y, t ∈ F₊[V]^G` 使 `x * (t/1) = y/1` ✓。

**⚠ 口径** ✓：结论**不是**「`x = y/1`」✗（那一般**假** ✗：`1/s` 本身通常不在 `algebraMap` 的像里 ✗），
而是「**分母也取自 `F₊[V]^G`**」的**分式形** ✓ —— 这正是 `(A_s)^G = (A^G)_s` 的正确读法 ✓。

**证法** ✓（**五步，不用 Galois 假设** ✓）：① `IsLocalization.Away.surj` ✓ 写 `x * (s^n/1) = a/1` ✓；
② 对该式作用 `g` ✓ 并用 `hx` ✓ 与 §6 的相容性 ✓ 得 `(g•a)/1 = a/1` ✓；
③ `IsLocalization.map_eq_zero_iff` ✓ 给 `s^{k_g} * (g•a - a) = 0` ✓ —— **`k_g` 依赖 `g`** ✗，
故取 **`N := sup_g k_g`** ✓（**此处用 `Fintype G`** ✓，源的有限性在此进入 ✓）；
④ `b := s^N * a` ✓ 由 `s^N * (g•a) = s^N * a` ✓ 得 `b ∈ F₊[V]^G` ✓；
⑤ `x * ((s^{N+n})/1) = b/1` ✓ ⟹ 取 `y := b` ✓、`t := s^{N+n} ∈ F₊[V]^G` ✓。

**⚠ 与源的对照** ✓：源 (c) 取 `R = S^G` ✓；本条即 `S^G = (F₊[V]^G)(1/s)` ✓。
**⚠ 载体** ✓：作用以**实例参数**承载 ✓（`[MulSemiringAction G (Localization.Away s)]` ＋ 相容性 `hact` ✓）
—— 因为「局部化上的 `•`」与「具名 `def` 的 `.smul`」**句法不同** ✗（§6 实测 ✓），
作实例参数后所有 `rw` 才可句法匹配 ✓。 -/
theorem exists_symInvariants_fraction_of_fixed (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) s = s)
    [MulSemiringAction G (Localization.Away s)]
    (hact : ∀ (g : G) (y : SymmetricAlgebra F V),
      g • (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
        = algebraMap (SymmetricAlgebra F V) (Localization.Away s)
            (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y))
    {x : Localization.Away s} (hx : ∀ g : G, g • x = x) :
    ∃ y : SymmetricAlgebra F V, y ∈ symInvariants (F := F) (G := G) (V := V) ∧
      ∃ t : SymmetricAlgebra F V, t ∈ symInvariants (F := F) (G := G) (V := V) ∧
        x * algebraMap (SymmetricAlgebra F V) (Localization.Away s) t
          = algebraMap (SymmetricAlgebra F V) (Localization.Away s) y := by
  letI : MulSemiringAction G (SymmetricAlgebra F V) := symMulSemiringAction
  haveI : SMulCommClass G F (SymmetricAlgebra F V) :=
    ⟨fun g c x => by
      change symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) (c • x)
        = c • symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x
      exact map_smul _ c x⟩
  have hs' : ∀ g : G, g • s = s := fun g => hs g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (x := s) x
  have key : ∀ g : G, algebraMap (SymmetricAlgebra F V) (Localization.Away s) (g • a)
      = algebraMap (SymmetricAlgebra F V) (Localization.Away s) a := by
    intro g
    change algebraMap (SymmetricAlgebra F V) (Localization.Away s)
        ((symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g)) a)
      = algebraMap (SymmetricAlgebra F V) (Localization.Away s) a
    rw [← hact g a]
    calc g • algebraMap (SymmetricAlgebra F V) (Localization.Away s) a
        = g • (x * algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ n) := by rw [← ha]
      _ = (g • x) * (g • (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ n)) := by
            rw [MulSemiringAction.smul_mul]
      _ = x * (g • (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ n)) := by
            rw [hx g]
      _ = x * (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ n) := by
            congr 1
            rw [smul_pow', hact g s, hs g]
      _ = algebraMap (SymmetricAlgebra F V) (Localization.Away s) a := ha
  have hk : ∀ g : G, ∃ k : ℕ, s ^ k * (g • a - a) = 0 := by
    intro g
    have h0 : algebraMap (SymmetricAlgebra F V) (Localization.Away s) (g • a - a) = 0 := by
      rw [map_sub, key g, sub_self]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (M := Submonoid.powers s)
      (S := Localization.Away s) (g • a - a)).mp h0
    obtain ⟨k, hk'⟩ := (Submonoid.mem_powers_iff (m : SymmetricAlgebra F V) s).mp m.2
    exact ⟨k, by rw [← hk'] at hm; exact hm⟩
  choose k hk using hk
  let N := Finset.univ.sup k
  have hN : ∀ g : G, s ^ N * (g • a - a) = 0 := by
    intro g
    have hle : k g ≤ N := Finset.le_sup (Finset.mem_univ g)
    rw [← Nat.add_sub_of_le hle, pow_add, mul_assoc,
      mul_comm (s ^ (N - k g)) (g • a - a), ← mul_assoc, hk g, zero_mul]
  have hb : s ^ N * a ∈ symInvariants (F := F) (G := G) (V := V) := by
    rw [mem_symInvariants]
    intro g
    change g • (s ^ N * a) = s ^ N * a
    rw [MulSemiringAction.smul_mul, smul_pow', hs' g]
    have h2 : s ^ N * (g • a) = s ^ N * a := by
      have h3 := hN g
      rw [mul_sub, sub_eq_zero] at h3
      exact h3
    rw [h2]
  refine ⟨s ^ N * a, hb, s ^ (N + n), ?_, ?_⟩
  · rw [mem_symInvariants]
    intro g
    change g • s ^ (N + n) = s ^ (N + n)
    rw [smul_pow', hs' g]
  · rw [map_mul, map_pow, map_pow, pow_add]
    calc x * (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ N
          * algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ n)
        = x * algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ n
            * algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ N := by ring
      _ = algebraMap (SymmetricAlgebra F V) (Localization.Away s) a
            * algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ N := by rw [ha]
      _ = algebraMap (SymmetricAlgebra F V) (Localization.Away s) s ^ N
            * algebraMap (SymmetricAlgebra F V) (Localization.Away s) a := by ring

/-- **用点** ✓：把 §7 的难方向落到 §5 的 `symLocMulSemiringAction` ✓（**相容性由 §6 供给** ✓）。 -/
theorem exists_symInvariants_fraction_of_fixed_away (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) s = s)
    {x : Localization.Away s}
    (hx : ∀ g : G, (symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g x = x) :
    ∃ y : SymmetricAlgebra F V, y ∈ symInvariants (F := F) (G := G) (V := V) ∧
      ∃ t : SymmetricAlgebra F V, t ∈ symInvariants (F := F) (G := G) (V := V) ∧
        x * algebraMap (SymmetricAlgebra F V) (Localization.Away s) t
          = algebraMap (SymmetricAlgebra F V) (Localization.Away s) y := by
  letI : MulSemiringAction G (Localization.Away s) := symLocMulSemiringAction s hs
  exact exists_symInvariants_fraction_of_fixed s hs
    (fun g y => symLocMulSemiringAction_algebraMap s hs g y) hx

/-! ## 9. 源 `thm1.3(c)` 的**等变组装** ✓✓✓✓（**两处口径同时收官** ✓） -/

/-- **源 `thm1.3(c)` 的等变组装** ✓✓✓✓（**本轮主结果** ✓）：由两个**具名输入** ✓ 直接得
`S = F₊[V](1/s)` 上的**局部投射性**，且提升 `μ` 是 **`G`-等变**的 ✓、其 ② 半覆盖**全部**
`G`-不动元 ✓ —— 即 §62 组装的两处口径（等变性 ✗／全不变量档 ✗）**同时**收口 ✓。

**⚠ 前置** ✓：局部化上的 `G`-作用以**实例参数**承载 ✓（`[MulSemiringAction G (Localization.Away s)]`
＋ `[SMulCommClass G F (Localization.Away s)]` ✓ ＋ 与 `algebraMap` 的相容性 `hact` ✓）；
`s` 的 `G`-不变性**不出现在假设里** ✓ —— 它只在**构造**该作用时（§5 ✓）用得到 ✓。

**证法** ✓（**§62 的组装 ＋ 等变性** ✓）：
① `hSF`（`S` 上作用与 `F`-纯量交换 ✓）由 `hgal` 的**第 ② 条款** ✓ ＋ `IsScalarTower` ✓ 得 ✓；
② `Δ₀ := Δ ∘ 局部化` ✓ 等变 ✓ 且 `Δ₀ s` 为单位 ✓；
③ `exists_galoisProjectiveSection` ✓ 取 **`G`-等变截面 `δ`** ✓；
④ **`symLift_core_equivariant`** ✓（§95 ✓）⟹ **等变提升 `μ₀`** ✓ —— **这是与 §62 的关键差别**
（§62 用的是「去局部化形」的存在性假设 ✗，不含等变性 ✗）；
⑤ `IsLocalization.liftAlgHom` ✓ 提升为 `μ` ✓，`ψ ∘ μ = Δ` 由 `algHom_ext` ✓；
⑥ **`μ` 的等变性** ✓：两边都是 `Localization.Away s →ₐ[F] S` 的 `AlgHom` ✓（右侧用
`MulSemiringAction.toAlgHom F S g` ✓，**需 `hSF` 作实例** ✓），在 `algebraMap` 的像上一致 ✓
（`hact` ✓ ＋ `μ₀` 的等变性 ✓）；
⑦ **全不变量档** ✓：`x` 不动 ⟹ `μ x` 不动 ✓（由 ⑥ ✓）⟹ `exists_algebraMap_of_invariant` ✓
（**需 `GaloisFixedSubringHyp R S G hRG`** ✓，即第二个具名输入 ✓）⟹ `μ x ∈ R` ✓。 -/
theorem exists_localized_lift_equivariant_of_galoisHyps
    (hproj : GaloisProjectiveSectionHyp F G)
    (hfixAll : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S]
      [Algebra F S] [IsScalarTower F R S] [MulSemiringAction G S]
      (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
      GaloisFixedSubringHyp R S G hRG)
    (s : SymmetricAlgebra F V)
    [MulSemiringAction G (Localization.Away s)]
    [SMulCommClass G F (Localization.Away s)]
    (hact : ∀ (g : G) (y : SymmetricAlgebra F V),
      g • (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
        = algebraMap (SymmetricAlgebra F V) (Localization.Away s)
            (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y))
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    {hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)}
    {hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t)}
    (hgal : IsGaloisWithGroup R S G hRG) (hgal' : IsGaloisWithGroup R S' G hRG')
    (ψ : S →ₐ[F] S') [IsLocalHom ψ]
    (hψR : ∀ (r : R) (t : S), ψ (algebraMap R S r * t) = algebraMap R S' r * ψ t)
    (hψG : ∀ (g : G) (t : S), ψ (g • t) = g • ψ t)
    (hψsurj : Function.Surjective ψ)
    (Δ : Localization.Away s →ₐ[F] S')
    (hΔG : ∀ (g : G) (x : Localization.Away s), Δ (g • x) = g • Δ x) :
    ∃ μ : Localization.Away s →ₐ[F] S,
      (∀ x, ψ (μ x) = Δ x) ∧
      (∀ (g : G) (x : Localization.Away s), μ (g • x) = g • μ x) ∧
      (∀ x : Localization.Away s, (∀ g : G, g • x = x) → ∃ r : R, μ x = algebraMap R S r) := by
  have hfixF : ∀ (g : G) (c : F), g • algebraMap F S c = algebraMap F S c := by
    intro g c
    rw [IsScalarTower.algebraMap_apply F R S]
    exact hgal.2.1 g (algebraMap F R c)
  have hSF : ∀ (g : G) (c : F) (t : S), g • (c • t) = c • (g • t) := by
    intro g c t
    conv_lhs => rw [Algebra.smul_def]
    rw [MulSemiringAction.smul_mul, hfixF g c, Algebra.smul_def]
  let Δ₀ : SymmetricAlgebra F V →ₐ[F] S' :=
    Δ.comp (Algebra.algHom F (SymmetricAlgebra F V) (Localization.Away s))
  have hΔ₀G : ∀ (g : G) (y : SymmetricAlgebra F V),
      Δ₀ (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y)
        = g • Δ₀ y := by
    intro g y
    change Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s)
        (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) y))
      = g • Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
    rw [← hact g y]
    exact hΔG g (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
  have hΔs : IsUnit (Δ₀ s) := by
    have h1 : IsUnit (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit (x := s)
    show IsUnit (Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) s))
    exact h1.map Δ
  let ψR : S →ₗ[R] S' :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r t
        rw [Algebra.smul_def, Algebra.smul_def]
        exact hψR r t }
  obtain ⟨δ, hδψ, hδG⟩ :=
    exists_galoisProjectiveSection F G hproj R S S' hRG hRG' hgal' ψR hψG hψsurj
  obtain ⟨μ₀, hμ₀, hμ₀G⟩ := symLift_core_equivariant (F := F) (G := G) (V := V)
    S S' hSF ψ (δ.restrictScalars F) hδψ hδG Δ₀ hΔ₀G
  have hμ₀unit : IsUnit (μ₀ s) :=
    IsLocalHom.map_nonunit (f := ψ) (μ₀ s) (by rw [hμ₀ s]; exact hΔs)
  let μ : Localization.Away s →ₐ[F] S :=
    IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := μ₀) (by
      rintro ⟨y, hy⟩
      change IsUnit (μ₀ y)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y s).mp hy
      rw [← hn, map_pow]
      exact hμ₀unit.pow n)
  have hμ_alg : ∀ y : SymmetricAlgebra F V,
      μ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y) = μ₀ y := by
    intro y
    dsimp only [μ]
    rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
    rfl
  haveI : SMulCommClass G F S := ⟨hSF⟩
  have hμG : ∀ (g : G) (x : Localization.Away s), μ (g • x) = g • μ x := by
    intro g x
    have hmain : μ.comp (MulSemiringAction.toAlgHom F (Localization.Away s) g)
        = (MulSemiringAction.toAlgHom F S g).comp μ := by
      apply IsLocalization.algHom_ext (Submonoid.powers s)
      refine AlgHom.ext (fun y => ?_)
      show μ (g • algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
        = g • μ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
      rw [hact g y, hμ_alg, hμ_alg]
      exact hμ₀G g y
    have hpt := congrArg (fun f => f x) hmain
    simpa [AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply] using hpt
  refine ⟨μ, ?_, hμG, ?_⟩
  · have hcomp : ψ.comp μ = Δ := by
      apply IsLocalization.algHom_ext (Submonoid.powers s)
      refine AlgHom.ext (fun y => ?_)
      show ψ (μ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y))
        = Δ (algebraMap (SymmetricAlgebra F V) (Localization.Away s) y)
      rw [hμ_alg y]
      exact hμ₀ y
    intro x
    exact congrArg (fun f => f x) hcomp
  · intro x hx
    exact exists_algebraMap_of_invariant (hfixAll R S hRG) hgal (fun g => by
      rw [← hμG g x, hx g])

/-- **用点** ✓：把 §9 的等变组装落到 §5 的具体作用 `symLocMulSemiringAction` 上 ✓
（两条局部实例：作用本身 ✓ ＋ `SMulCommClass` ✓（由 `locActAlgHom` 的 `AlgHom.map_smul` ✓）；
相容性由 §6 的 `symLocMulSemiringAction_algebraMap` ✓ 供给 ✓）。 -/
theorem exists_localized_lift_equivariant_of_galoisHyps_away
    (hproj : GaloisProjectiveSectionHyp F G)
    (hfixAll : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S]
      [Algebra F S] [IsScalarTower F R S] [MulSemiringAction G S]
      (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
      GaloisFixedSubringHyp R S G hRG)
    (s : SymmetricAlgebra F V)
    (hs : ∀ g : G, symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) s = s)
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    {hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)}
    {hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t)}
    (hgal : IsGaloisWithGroup R S G hRG) (hgal' : IsGaloisWithGroup R S' G hRG')
    (ψ : S →ₐ[F] S') [IsLocalHom ψ]
    (hψR : ∀ (r : R) (t : S), ψ (algebraMap R S r * t) = algebraMap R S' r * ψ t)
    (hψG : ∀ (g : G) (t : S), ψ (g • t) = g • ψ t)
    (hψsurj : Function.Surjective ψ)
    (Δ : Localization.Away s →ₐ[F] S')
    (hΔG : ∀ (g : G) (x : Localization.Away s),
      Δ ((symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g x) = g • Δ x) :
    ∃ μ : Localization.Away s →ₐ[F] S,
      (∀ x, ψ (μ x) = Δ x) ∧
      (∀ (g : G) (x : Localization.Away s),
        μ ((symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g x) = g • μ x) ∧
      (∀ x : Localization.Away s,
        (∀ g : G, (symLocMulSemiringAction (F := F) (G := G) (V := V) s hs).smul g x = x) →
          ∃ r : R, μ x = algebraMap R S r) := by
  letI : MulSemiringAction G (SymmetricAlgebra F V) := symMulSemiringAction
  haveI : SMulCommClass G F (SymmetricAlgebra F V) :=
    ⟨fun g c x => by
      change symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) (c • x)
        = c • symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x
      exact map_smul _ c x⟩
  have hs' : ∀ g : G, g • s = s := fun g => hs g
  letI : MulSemiringAction G (Localization.Away s) := symLocMulSemiringAction s hs
  haveI : SMulCommClass G F (Localization.Away s) :=
    ⟨fun g c x => by
      change locActAlgHom (F := F) (G := G) (A := SymmetricAlgebra F V) (s := s) hs' g (c • x)
        = c • locActAlgHom (F := F) (G := G) (A := SymmetricAlgebra F V) (s := s) hs' g x
      exact map_smul _ c x⟩
  exact exists_localized_lift_equivariant_of_galoisHyps hproj hfixAll s
    (fun g y => symLocMulSemiringAction_algebraMap s hs g y) hgal hgal' ψ hψR hψG hψsurj Δ hΔG

/-! ## 10. 登记（`thm1.3(c)`：**缺口与口径均已收** ✓） -/

/-- **登记** ✓：**三缺口全闭** ✓（本件 §4 ✓／§5 ✓／§7 ✓）＋ **两口径亦收** ✓（本件 §9 ✓）：

① **局部化万有性质** ✓ —— ✅ §4 ✓（**唯一性**不声称 ✗，源 (a) 的证明不用它 ✓）；
② **局部化对象的 `𝓔(G)` 归属** ✓ —— ✅ §5 ✓；
③ **不变量识别** `S^G = (F₊[V]^G)(1/s)` ✓ —— ✅ §7 ✓（**分式形** ✓）；
(a) 口径：§6 的 ② 半只到**基的像**档 ✓ —— ✅ §9 ✓ 给**全不变量档** ✓（用 §9 ⑥ 的等变性 ✓
＋ `GaloisFixedSubringHyp` ✓）；
(b) 口径：§6 的组装**未**断言 `μ` 等变 ✓ —— ✅ §9 ✓ 断言了 ✓（**改用
`symLift_core_equivariant`** ✓ 而非「去局部化形」的存在性假设 ✓）。

**⚠ 仍**✗**（本层之外的两条，登记）**：
(i) §7 的分式形**未**用于 §9 的 ② 半 ✗ —— §9 用的是**等变性**路线 ✓（更短 ✓）；
故 §7 目前是**独立的经典事实** ✓（其用处：把源对象的不变量**认成** `F₊[V]^G(1/s)` ✓，供**陈述**用 ✓）；
(ii) **§9 的两个具名输入仍未证** ✗（`GaloisProjectiveSectionHyp` ✓／`GaloisFixedSubringHyp` ✓，
源侧为 `[CHR68]` p.13 ✓ ＋ 经典 Galois 理论 ✓ —— **⚠ 账目更正（第 207 轮** ✓**）**：
`[CHR68]` p.13 的**精确出处仍不在 `raw/`** ✗，**但**其**用点**已在 `raw/Saltman1978` 印 528（＝ PDF 3 ✓）
内可核 ✓（同页证明给 **progenerator** ✓，端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）。

**✅ 端到端链** ✓：§95（投射性 ✓）⟹ §96（⟹ 局部 ⟹ 去局部化形 ✓）⟹ §62（组装 ✓）⟹
§7（③ ✓）⟹ **§9（等变 ＋ 全不变量 ✓）** ＝ 源 `thm1.3(c)` ✓，除两个具名外部输入外**无缺口** ✓。 -/
theorem thm13c_gap_registered : True := trivial

/-! ## 公理闸门 -/

#print axioms isLocalHom_id
#print axioms not_isLocalHom_algebraMap_away_X
#print axioms IsLocalProjectiveSymmetric
#print axioms isLocalProjectiveSymmetric_typeLock
#print axioms localProjective_of_projective
#print axioms localProjective_of_galoisHyps
#print axioms IsLocalProjectiveSymmetricLocalized
#print axioms isLocalProjectiveSymmetricLocalized_typeLock
#print axioms isLocalProjectiveSymmetricLocalized_of_localProjective
#print axioms isUnit_algebraMap_tensor_away
#print axioms exists_tensor_away_lift
#print axioms exists_tensor_away_lift_iff
#print axioms locToAlgHom_one
#print axioms locToAlgHom_mul
#print axioms locSmul_pow_fixed
#print axioms locActBase
#print axioms locActBase_apply
#print axioms locActBase_isUnit
#print axioms locActAlgHom
#print axioms locActAlgHom_comp
#print axioms locActAlgHom_one
#print axioms locActAlgHom_mul
#print axioms locMulSemiringAction
#print axioms locMulSemiringAction_algebraMap
#print axioms symLocMulSemiringAction
#print axioms symLocMulSemiringAction_algebraMap
#print axioms exists_localized_lift_of_isLocalProjectiveSymmetricLocalized
#print axioms fixed_algebraMap_of_mem_symInvariants
#print axioms exists_symInvariants_fraction_of_fixed
#print axioms exists_symInvariants_fraction_of_fixed_away
#print axioms exists_localized_lift_equivariant_of_galoisHyps
#print axioms exists_localized_lift_equivariant_of_galoisHyps_away
#print axioms thm13c_gap_registered

end ABGV52.BTier
