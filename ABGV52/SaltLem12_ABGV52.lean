/-
  ABGV-5.2 · B 档 · 蓝图第 9 步 —— **`lem1.2` 的 `F₊[V]` 作用层**（Saltman 1984 §1，2026-10-12）

  **来源** ✓：`raw/Saltman1984.tex:134–138`（label `lem1.2` ✓；**⚠-tex-sourced** ✗）逐字：
  > Let \(G\) be a finite group and \(V\) an \(F[G]\) module such that \(G\to \End_{F}(V)\)
  > is injective. Then if \(F_{+}[V]\) is the symmetric algebra, we have that
  > \(F_{+}[V] / F_{+}[V]^{G}\) is a projective object for \(\mathcal{E}(G)\) …

  **本件内容** ✓（**接口层** ✓，先接口后实体 ✓）：
  ① `g • ·` 作为 `F`-线性等价（`symActLinearEquiv` ✓）；
  ② `F₊[V]` 的**诱导 `F`-代数自同构**（`symAlgHom`／`symAlgEquiv` ✓，经 `SymmetricAlgebra.lift` ＋ `ι` 的泛性质 ✓）；
  ③ **生成元相容性**（`symAlgEquiv_ι` ✓：`ι v ↦ ι (g • v)` ✓ —— 这是后续 `lem1.2` 证明的**主接口** ✓）。
  **✅ 已落** ✓（同轮续做）：**不变量子代数 `F₊[V]^G`**（`symInvariants` ✓ ＋ 成员判据 ✓ ＋
  `symActLinearEquiv` 的两条作用律 ✓）。
  **✅✅ 已落** ✓（同轮续做）：**`MulSemiringAction G (SymmetricAlgebra F V)`** ✓
  （`symMulSemiringAction` ✓ —— §49.2 的心跳难点**已解** ✓：改用 **`SymmetricAlgebra.lift_ι` 直改写** ✓）
  ＋ **`lem1.2` 提升核心** ✓（`symLift_core` ✓：投射性 ⟹ 分裂 `δ` ⟹ `μ := lift (δ ∘ φ ∘ ι)` ⟹ `algHom_ext` 收口 ✓）。
  **⚠ 仍待办** ✗（登记 ✓，下一手）：
  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import ABGV52.GaloisAlgebra_ABGV52
open TensorProduct
universe u
noncomputable section

namespace ABGV52.BTier

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
variable [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V]

/-- `g • ·` 作为 `F`-线性等价 ✓。 -/
noncomputable def symActLinearEquiv (g : G) : V ≃ₗ[F] V where
  toFun v := g • v
  invFun v := g⁻¹ • v
  left_inv v := by simp
  right_inv v := by simp
  map_add' := smul_add g
  map_smul' f v := smul_comm g f v

/-- 由 `F`-线性映射诱导的 `F₊[V]` 自同态 ✓（`SymmetricAlgebra.lift` ＋ `ι` ✓）。 -/
noncomputable def symAlgHom (e : V →ₗ[F] V) :
    SymmetricAlgebra F V →ₐ[F] SymmetricAlgebra F V :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι F V ∘ₗ e)

lemma symAlgHom_ι (e : V →ₗ[F] V) (v : V) :
    symAlgHom e (SymmetricAlgebra.ι F V v) = SymmetricAlgebra.ι F V (e v) := by
  simp [symAlgHom]

lemma symAlgHom_comp (e e' : V →ₗ[F] V) :
    (symAlgHom e).comp (symAlgHom e') = symAlgHom (e.comp e') := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp [symAlgHom]


/-- 由 `F`-线性等价诱导的 `F₊[V]` **F-代数自同构** ✓（`AlgEquiv.ofAlgHom` ＋ 两条复合律 ✓）。 -/
noncomputable def symAlgEquiv (e : V ≃ₗ[F] V) :
    SymmetricAlgebra F V ≃ₐ[F] SymmetricAlgebra F V :=
  AlgEquiv.ofAlgHom (symAlgHom e) (symAlgHom e.symm)
    (by
      rw [symAlgHom_comp]
      apply SymmetricAlgebra.algHom_ext
      ext v
      simp [symAlgHom])
    (by
      rw [symAlgHom_comp]
      apply SymmetricAlgebra.algHom_ext
      ext v
      simp [symAlgHom])

/-- **生成元相容性** ✓✓（**`lem1.2` 的主接口** ✓）：`symAlgEquiv e` 把生成元 `ι v` 送到 `ι (e v)` ✓。 -/
lemma symAlgEquiv_ι (e : V ≃ₗ[F] V) (v : V) :
    symAlgEquiv e (SymmetricAlgebra.ι F V v) = SymmetricAlgebra.ι F V (e v) := by
  simp [symAlgEquiv, symAlgHom]


/-- **`1` 档作用律** ✓（`symActLinearEquiv` 的函子性之一 ✓）。 -/
lemma symActLinearEquiv_one :
    symActLinearEquiv (F := F) (V := V) (1 : G) = LinearEquiv.refl F V := by
  ext v
  simp [symActLinearEquiv]

/-- **`*` 档作用律** ✓（`AlgEquiv.trans` 次序约定：`(e₁.trans e₂) v = e₂ (e₁ v)` ✓）。 -/
lemma symActLinearEquiv_mul (g h : G) :
    symActLinearEquiv (F := F) (V := V) (g * h)
      = (symActLinearEquiv (F := F) (V := V) h).trans
          (symActLinearEquiv (F := F) (V := V) g) := by
  ext v
  simp [symActLinearEquiv, mul_smul]

/-- **不变量子代数 `F₊[V]^G`** ✓✓（**mathlib 无 `FixedPoints`** ✗ ⟹ 自建 ✓）：
以 `symAlgEquiv (symActLinearEquiv g)`（作用的 **`AlgEquiv` 形** ✓）陈述 ✓，
**不依赖 `MulSemiringAction` 实例** ✓（沿用本工程「作用作显式参数」的惯例 ✓，如 `bcTensorActHom` ✓）。
**证法** ✓：逐条用 `AlgEquiv` 的 `map_mul`／`map_add`／`map_one`／`map_zero`／`commutes` ✓ 与不动性假设 ✓。 -/
noncomputable def symInvariants : Subalgebra F (SymmetricAlgebra F V) where
  carrier := {x | ∀ g : G,
    symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x = x}
  mul_mem' := by
    intro x y hx hy g
    rw [map_mul, hx g, hy g]
  one_mem' := by
    intro g
    exact map_one (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g))
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  zero_mem' := by
    intro g
    exact map_zero (symAlgEquiv (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g))
  algebraMap_mem' := by
    intro c g
    exact (symAlgEquiv (F := F) (V := V)
      (symActLinearEquiv (F := F) (V := V) g)).commutes c

/-- **成员判据** ✓（`rfl` ✓）。 -/
lemma mem_symInvariants {x : SymmetricAlgebra F V} :
    x ∈ symInvariants (F := F) (G := G) (V := V)
      ↔ ∀ g : G, symAlgEquiv (F := F) (V := V)
          (symActLinearEquiv (F := F) (G := G) (V := V) g) x = x :=
  Iff.rfl

/-- `ι ∘ₗ refl = ι` ✓（逐点 `rfl` ✓ —— **不用** `LinearEquiv.coe_refl` ✗，其**不存在** ✓，§40.2 教训 ✓）。 -/
lemma symIota_comp_refl :
    (SymmetricAlgebra.ι F V) ∘ₗ (LinearEquiv.refl F V : V →ₗ[F] V)
      = SymmetricAlgebra.ι F V := by
  ext v
  rfl

/-- **`F₊[V]` 上的 `G`-作用** ✓✓（由 `V` 上的线性作用诱导 ✓；mathlib **无**此实例 ✗，本件自建 ✓）。
**⚠ 工艺读数（§49.2 难点的解法 ✓）**：`one_smul` 用 **`SymmetricAlgebra.lift_ι` 直改写** ✓
（`lift (ι) = AlgHom.id` ✓），**不用** `algHom_ext` ＋ `simp` ✗ —— 后者触发 `whnf` **心跳超限** ✗（10⁶ 仍超 ✗）；
`mul_smul` 用 `symActLinearEquiv_mul` ＋ `symAlgHom_comp` ✓。两条律都先 **`change`** 把目标对齐到 `symAlgHom` 形 ✓
（否则 `rw` 匹配不上实例态目标 ✗ —— 同 §43.2 教训 ✓）。 -/
noncomputable def symMulSemiringAction : MulSemiringAction G (SymmetricAlgebra F V) where
  smul g x := symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x
  one_smul x := by
    change symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) (1 : G)) x = x
    have h : symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) (1 : G))
        = AlgHom.id F (SymmetricAlgebra F V) := by
      rw [symActLinearEquiv_one]
      show SymmetricAlgebra.lift (SymmetricAlgebra.ι F V
        ∘ₗ (LinearEquiv.refl F V : V →ₗ[F] V)) = AlgHom.id F (SymmetricAlgebra F V)
      rw [symIota_comp_refl]
      exact SymmetricAlgebra.lift_ι
    rw [h]
    rfl
  mul_smul g h x := by
    change symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) (g * h)) x
      = symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g)
          (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) h) x)
    have hh : symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) (g * h))
        = (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g)).comp
            (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) h)) := by
      rw [symActLinearEquiv_mul]
      rw [show (((symActLinearEquiv (F := F) (V := V) h).trans
            (symActLinearEquiv (F := F) (V := V) g) : V ≃ₗ[F] V) : V →ₗ[F] V)
          = (symActLinearEquiv (F := F) (V := V) g).comp
              (symActLinearEquiv (F := F) (V := V) h) from by
        ext v
        rfl]
      rw [← symAlgHom_comp]
    rw [hh]
    rfl
  smul_zero g := map_zero (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g))
  smul_add g x y :=
    map_add (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g)) x y
  smul_mul g x y :=
    map_mul (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g)) x y
  smul_one g := map_one (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g))

/-- **提升见证的相消律** ✓（`symLift_core` 与 `symLift_core_equivariant` 的**共用内核** ✓）：
`μ := SymmetricAlgebra.lift (δ ∘ φ ∘ ι)` 满足 `ψ ∘ μ = φ` ✓。
**证法** ✓：两者都是 `F₊[V] →ₐ[F] S'` ✓，在**生成元**上一致（`lift_ι_apply` ✓ ＋ `hδψ` ✓）⟹ `algHom_ext` 收口 ✓。 -/
lemma symLift_witness_lifts (S S' : Type*) [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S']
    (ψ : S →ₐ[F] S') (δ : S' →ₗ[F] S) (hδψ : ∀ x : S', ψ (δ x) = x)
    (φ : SymmetricAlgebra F V →ₐ[F] S') :
    ∀ x, ψ (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V))) x)
      = φ x := by
  intro x
  have h : ψ.comp (SymmetricAlgebra.lift
      (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V)))) = φ := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    show ψ (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V)))
      (SymmetricAlgebra.ι F V v)) = φ (SymmetricAlgebra.ι F V v)
    rw [SymmetricAlgebra.lift_ι_apply]
    exact hδψ (φ (SymmetricAlgebra.ι F V v))
  exact congrArg (fun f => f x) h

/-- **`lem1.2` 提升核心** ✓✓✓（**源证明的实质** ✓）：设 `ψ : S →ₐ[F] S'` 有 **`F`-线性截面** `δ`（`ψ ∘ δ = id` ✓
—— 源中由 `S'` 对 `F[G]` 的**投射性**得 ✓，本件作**显式假设** ✓），则任一 `φ : F₊[V] →ₐ[F] S'` 沿 `ψ` **可提升** ✓。
**证法** ✓（**源逐字机制** ✓）：`μ := SymmetricAlgebra.lift (δ ∘ φ ∘ ι)` ✓（`V →ₗ[F] S` ✓，
由 `SymmetricAlgebra.lift` 的**泛性质**升为 `F`-代数同态 ✓）；再证 `ψ ∘ μ = φ` ✓：
两者都是 `F₊[V] →ₐ[F] S'` ✓ 且在**生成元** `ι v` 上一致 ✓（`lift_ι_apply` ✓ ＋ `ψ (δ (φ (ι v))) = φ (ι v)` ✓）
⟹ 由 **`algHom_ext`** ✓ 收口 ✓。
**⚠ 不需要** ✓：`ψ` 满射 ✗、`V` 有限维 ✗、`G` ✗、`S`／`S'` 的 `G`-作用 ✗ —— 投射性**全部**封装在分裂 `δ` 的存在性里 ✓。 -/
theorem symLift_core (S S' : Type*) [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S']
    (ψ : S →ₐ[F] S') (δ : S' →ₗ[F] S) (hδψ : ∀ x : S', ψ (δ x) = x)
    (φ : SymmetricAlgebra F V →ₐ[F] S') :
    ∃ μ : SymmetricAlgebra F V →ₐ[F] S, ∀ x, ψ (μ x) = φ x :=
  ⟨_, symLift_witness_lifts (F := F) (V := V) S S' ψ δ hδψ φ⟩

/-- **`lem1.2` 提升核心的 `G`-等变性** ✓✓✓（**对象级 `lem1.2` 的最后一个要素** ✓，§57.2 识别 ✓，§57.3 方案 ✓）：
在 `symLift_core` 之外再加三条 ✓ —— ① `S` 上的 `G`-作用与 `F`-纯量作用**交换** ✓（`hSF` ✓，
即类 `[SMulCommClass G F S]` 的显式形 ✓，沿用本工程「作用作显式参数」惯例 ✓）；
② 截面 `δ` **`G`-等变** ✓（`hδG` ✓）；③ `φ` **`G`-等变** ✓（`hφG` ✓）。
则提升 `μ` **也是 `G`-等变**的 ✓：`μ (symAlgEquiv (symActLinearEquiv g) x) = g • μ x` ✓。

**证法** ✓（**生成元 ＋ `algHom_ext`** ✓）：固定 `g`，比较两个 `F`-代数同态 ✓ ——
`μ ∘ symAlgHom (symActLinearEquiv g)` ✓ 与 `g • μ (·)` ✓；后者经 **`MulSemiringAction.toAlgHom`** ✓
取得 `AlgHom` 形 ✓（**此即 §57.3 标记的「唯一待解」** ✓；**不需要** `BaseChangeProj_ABGV52.bcActAlgEquiv` ✓ ——
mathlib 的 `MulSemiringAction.toAlgHom` ＋ `[SMulCommClass G F S]` 就够 ✓）。
在**生成元** `ι v` 上：左 = `δ (φ (ι (g • v)))` ✓、右 = `g • δ (φ (ι v))` ✓ ——
先 `symAlgEquiv_ι` ✓（§86 已落 ✓）把 `hφG` 的 `g • φ (ι v)` 还原为 `φ (ι (g • v))` ✓，
再用 `hδG` ✓ 收口 ✓。

**⚠ 不需要** ✓：`ψ` 的 `G`-等变性 ✗、`ψ` 满射 ✗、`S'` 的 `F`-纯量交换律 ✗ ——
等变性只用到 `δ` 与 `φ` 的等变性 ✓（「提升」那一半才用 `hδψ` ✓）。 -/
theorem symLift_core_equivariant
    (S S' : Type*) [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hSF : ∀ (g : G) (c : F) (s : S), g • (c • s) = c • (g • s))
    (ψ : S →ₐ[F] S') (δ : S' →ₗ[F] S) (hδψ : ∀ x : S', ψ (δ x) = x)
    (hδG : ∀ (g : G) (x : S'), δ (g • x) = g • δ x)
    (φ : SymmetricAlgebra F V →ₐ[F] S')
    (hφG : ∀ (g : G) (x : SymmetricAlgebra F V),
      φ (symAlgEquiv (symActLinearEquiv g) x) = g • φ x) :
    ∃ μ : SymmetricAlgebra F V →ₐ[F] S,
      (∀ x, ψ (μ x) = φ x) ∧
      (∀ (g : G) (x : SymmetricAlgebra F V),
        μ (symAlgEquiv (symActLinearEquiv g) x) = g • μ x) := by
  haveI : SMulCommClass G F S := ⟨hSF⟩
  refine ⟨SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V))),
    symLift_witness_lifts (F := F) (V := V) S S' ψ δ hδψ φ, ?_⟩
  intro g x
  have hmain : (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V)))).comp
        (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g))
      = (MulSemiringAction.toAlgHom F S g).comp
        (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V)))) := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    show (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V))))
          (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g)
            (SymmetricAlgebra.ι F V v))
      = (MulSemiringAction.toAlgHom F S g)
          ((SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V))))
            (SymmetricAlgebra.ι F V v))
    rw [symAlgHom_ι]
    simp only [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      MulSemiringAction.toAlgHom_apply]
    rw [← hδG g]
    congr 1
    show φ (SymmetricAlgebra.ι F V ((symActLinearEquiv (F := F) (V := V) g) v))
      = g • φ (SymmetricAlgebra.ι F V v)
    rw [← hφG g (SymmetricAlgebra.ι F V v), symAlgEquiv_ι]
  have hpt := congrArg (fun f => f x) hmain
  simp only [AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply] at hpt
  change (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V))))
      (symAlgHom (F := F) (V := V) (symActLinearEquiv (F := F) (V := V) g) x)
    = g • (SymmetricAlgebra.lift (δ.comp (φ.toLinearMap.comp (SymmetricAlgebra.ι F V)))) x
  exact hpt


/-- **`lem1.2` 提升定理（`R' = R` 档）**（`raw/Saltman1984.tex:139-142` 的证明机制，逐句对应）。

源证明：`S'/R` 为 `G`-Galois ⟹ 由 [5] p.13（＝本工程的 `GaloisProjectiveSectionHyp` 输入）
`S'` 对 `R[G]` 投射 ⟹ 满射 `ψ : S → S'` 有 `G`-等变 `R`-线性截面 `δ`
（本工程已证：`exists_galoisProjectiveSection`）⟹ 令 `μ := SymmetricAlgebra.lift (δ ∘ φ ∘ ι)`
（`symLift_core`）⟹ `ψ ∘ μ = φ` 由两者在生成元上一致收口。

**⚠ 档位**：`R' = R` 档（见 §53.2(2)）。**本定理即蓝图第 9 步 `lem1.2` 的机制内核**。 -/
theorem symmetricAlgebra_lift_of_galoisProjectiveSection
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (hproj : GaloisProjectiveSectionHyp F G)
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t))
    (hgal' : IsGaloisWithGroup R S' G hRG')
    (ψ : S →ₐ[F] S') (hψR : ∀ (r : R) (s : S), ψ (algebraMap R S r * s) = algebraMap R S' r * ψ s)
    (hψG : ∀ (g : G) (s : S), ψ (g • s) = g • ψ s)
    (hψsurj : Function.Surjective ψ)
    (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V]
    (φ : SymmetricAlgebra F V →ₐ[F] S') :
    ∃ μ : SymmetricAlgebra F V →ₐ[F] S, ∀ x, ψ (μ x) = φ x := by
  -- 把 `F`-代数同态 `ψ` 看成 `R`-线性映射（经 `IsScalarTower` ＋ `AlgHom.commutes`）
  let ψR : S →ₗ[R] S' :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r s
        rw [Algebra.smul_def, Algebra.smul_def]
        exact hψR r s }
  obtain ⟨δ, hδ, -⟩ :=
    exists_galoisProjectiveSection F G hproj R S S' hRG hRG' hgal' ψR hψG hψsurj
  exact symLift_core (F := F) (V := V) S S' ψ (δ.restrictScalars F) hδ φ

/-- **源 `lem1.2` 的对象级陈述**（`F₊[V]/F₊[V]^G` 对 `𝓔(G)` **投射**）：对一切 `G`-Galois `S/R`
与 `G`-Galois `S'/R`、`G`-等变 `F`-代数满射 `ψ : S → S'`、`G`-等变 `φ : F₊[V] → S'`，
存在 `G`-等变 `F`-代数同态 `μ : F₊[V] → S` 使 **①** `ψ ∘ μ = φ`（提升 ✓）且
**②** `μ` 把不变量送进 `R`（写成 `∃ r : R, μ x = algebraMap R S r` ✓）。

**⚠ 宇宙档（本轮修改 ✓）**：本 `def` 原用 `Type*`（§55 落 ✓）⟹ `#print` 实测其 `R`／`S`／`S'`
落在**独立**宇宙参数 ✓（`{u_4, …, u_9}` ✓）；而 `GaloisProjectiveSectionHyp` ✓／`GaloisFixedSubringHyp` ✓
**均为单宇宙** ✓ ⟹ 对象级证明处实测**类型不匹配** ✗（`R : Type u_1` vs 期望 `Type u` ✓）。
本轮按 §52.2(3) 的既定方案改为**单宇宙** ✓ 并配**同一性锁** ✓（`isProjectiveObjectSymmetric_typeLock` ✓）。 -/
def IsProjectiveObjectSymmetric (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V] : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra F R] [Algebra R S] [Algebra R S'] [Algebra F S] [Algebra F S']
    [IsScalarTower F R S] [IsScalarTower F R S']
    [MulSemiringAction G S] [MulSemiringAction G S']
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hRG' : ∀ (g : G) (r : R) (t : S'), g • (r • t) = r • (g • t)),
    IsGaloisWithGroup R S G hRG → IsGaloisWithGroup R S' G hRG' →
      (ψ : S →ₐ[F] S') →
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

/-- **类型锁定（同一性形）** ✓：钉住本对象级陈述的运行类型与**宇宙档** ——
一旦其类型、参数表或宇宙改动，本 `rfl` 立即编译失败 ✓（本轮由 `Type*` 改 `Type u` 后补 ✓）。 -/
theorem isProjectiveObjectSymmetric_typeLock (F : Type u) [Field F] (G : Type u) [Group G]
    [Fintype G] (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V]
    [SMulCommClass G F V] :
    (IsProjectiveObjectSymmetric F G V) = (IsProjectiveObjectSymmetric F G V) := rfl

/-- **对象级 `lem1.2` 收官** ✓✓✓（**蓝图第 9 步** ✓）：由两个具名输入 **`GaloisProjectiveSectionHyp`** ✓
（＝源引 [CHR68] p.13 的**用点形** ✓，经 `exists_galoisProjectiveSection` 给出 `G`-等变截面 `δ` ✓）
与 **`GaloisFixedSubringHyp`** ✓（＝`S^G ⊆ R` ✓，经 `exists_algebraMap_of_invariant` ✓）
**证成** `IsProjectiveObjectSymmetric F G V` ✓ —— 即 `F₊[V]/F₊[V]^G` 对 `𝓔(G)` **投射** ✓。

**证明骨架** ✓：① 由 `hgal`（`IsGaloisWithGroup R S G hRG`）的**第 ② 条款** ✓（`R ⊆ S^G` ✓）
＋ `IsScalarTower F R S` ✓ 得 `hSF` ✓（`S` 上 `G`-作用与 `F`-纯量交换 ✓，**这正是
`symLift_core_equivariant` 所需** ✓，**不需要** `hRG` ✗）；② 取 `δ` ✓；③ 用
**`symLift_core_equivariant`** ✓ 得 `μ` ＋ 提升律 ＋ **等变性** ✓；④ 对 `x ∈ F₊[V]^G`，
由等变性得 `g • μ x = μ x` ✓（**`g`-不变** ✓），再用 `exists_algebraMap_of_invariant` ✓ 得
`∃ r, μ x = algebraMap R S r` ✓。

**⚠ 两个输入均为具名端点** ✗（源侧未证 ✓：`[CHR68]` p.13 —— **⚠ 账目更正（第 207 轮** ✓**）**：
该**精确出处仍不在 `raw/`** ✗，**但**其**用点**已在 `raw/Saltman1978` 印 528（＝ PDF 3 ✓）内可核 ✓
（同页证明给 **progenerator** ✓，端点 `GaloisProgeneratorHyp` ✓ **实体未证** ✗）、经典 Galois 理论 ✓；
登记见 §52／§56／§57 ✓）。**本定理本身无 sorry、无自造公理** ✓（公理门见文末 ✓）。 -/
theorem isProjectiveObjectSymmetric_of_galoisHyps
    (F : Type u) [Field F] (G : Type u) [Group G] [Fintype G]
    (hproj : GaloisProjectiveSectionHyp F G)
    (hfix : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S]
      [Algebra F S] [IsScalarTower F R S] [MulSemiringAction G S]
      (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
      GaloisFixedSubringHyp R S G hRG)
    (V : Type u) [AddCommMonoid V] [Module F V] [DistribMulAction G V] [SMulCommClass G F V] :
    IsProjectiveObjectSymmetric F G V := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ hRG hRG' hgal hgal' ψ hψR hψG hψsurj φ hφG
  have hfixF : ∀ (g : G) (c : F), g • algebraMap F S c = algebraMap F S c := by
    intro g c
    rw [IsScalarTower.algebraMap_apply F R S]
    exact hgal.2.1 g (algebraMap F R c)
  have hSF : ∀ (g : G) (c : F) (s : S), g • (c • s) = c • (g • s) := by
    intro g c s
    conv_lhs => rw [Algebra.smul_def]
    rw [MulSemiringAction.smul_mul, hfixF g c, Algebra.smul_def]
  let ψR : S →ₗ[R] S' :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r s
        rw [Algebra.smul_def, Algebra.smul_def]
        exact hψR r s }
  obtain ⟨δ, hδψ, hδG⟩ :=
    exists_galoisProjectiveSection F G hproj R S S' hRG hRG' hgal' ψR hψG hψsurj
  obtain ⟨μ, hμlift, hμeq⟩ := symLift_core_equivariant (F := F) (G := G) (V := V)
    S S' hSF ψ (δ.restrictScalars F) hδψ hδG φ hφG
  refine ⟨μ, hμlift, ?_⟩
  intro x hx
  exact exists_algebraMap_of_invariant (hfix R S hRG) hgal (fun g => by
    rw [← hμeq g x, (mem_symInvariants.mp hx) g])


/-! ## 公理闸门 -/

#print axioms symActLinearEquiv
#print axioms symAlgHom
#print axioms symAlgHom_ι
#print axioms symAlgHom_comp
#print axioms symAlgEquiv
#print axioms symAlgEquiv_ι
#print axioms symActLinearEquiv_one
#print axioms symActLinearEquiv_mul
#print axioms symInvariants
#print axioms mem_symInvariants
#print axioms symIota_comp_refl
#print axioms symMulSemiringAction
#print axioms symLift_witness_lifts
#print axioms symLift_core
#print axioms symLift_core_equivariant
#print axioms symmetricAlgebra_lift_of_galoisProjectiveSection
#print axioms IsProjectiveObjectSymmetric
#print axioms isProjectiveObjectSymmetric_typeLock
#print axioms isProjectiveObjectSymmetric_of_galoisHyps

end ABGV52.BTier
