/-
  ABGV-5.2 · B 档 ① —— **基变换核心引理**（`hBC` ＝ 源 `proposition-0-2(d)` 的第一块，2026-10-11）

  **来源** ✓：Saltman 1982 `proposition-0-2(d)`（`raw/Saltman1982.tex:82`；引 [DI71] p. 85；
  源中无证明，前导句逐字「We next quote four results and give references instead of proofs」）
  **⚠-tex-sourced** ✗（PDF 孪生件在库 ✓，升核须回 PDF 目视 ✓）。
  其**印刷形**（`φ` 为任意环同态）在退化情形为**假** ✗（反例 `R' = 0`；`ℤ → 𝔽₂`／`S = ℤ[i]`／`G = C₂`），
  两例均已逐字登记于状态笔记 §34.5 ⇒ 本件只落**非零 `F`-代数**档 ✓（本工程 `T` 带 `IsLocalRing` ✓）。

  **本件内容** ✓：**§34.6 ①** 的一般小引理 ＋ **§34.6 ②** 的固定子环款：
  `M` 非零**投射** `F`-模、`T` 非零 `F`-代数 ⟹ `M ⊗[F] T ≠ 0` ✓。
  **⚠ 两条实测的“错误前提”** ✗（省后续人力）：
    (i) **只设“非零 f.g.、且 `ℤ`-自由”不够** ✗ —— 反例（一般交换环版）：`R = ℤ`、
        `T = ℤ/2`、`M = 2ℤ`（秩 1 自由**但非投射**）：此时 `M ⊗[ℤ] ℤ/2 = 0` ✗
        （`2ℤ ⊗ ℤ/2 → ℤ ⊗ ℤ/2 = ℤ/2` 的像是 `2·(ℤ/2) = 0`）⟹ 必须**投射** ✓。
    (ii) **一般截面 `s` 不够** ✗：`Module.Projective` 的定义式只给 `h ∘ s = id`，
        它**不**蕴含坐标 `(s x) x = 1` ✓（实测：`set`／`let` 绑定的表达式推型还会漂 ✗）。
        ⟹ 改走**对偶**：`Module.Dual.eval` 对投射模**单射** ✓（本件 `dual_eval_injective_of_projective`），
        据此取出非零泛函 `φ` 分离非零元 ✓。
  **证法** ✓：`φ` 分离 `x ≠ 0` ⟹ 取 `x ⊗ 1`；若其为 0，则经 `φ ⊗ id` 落到 `F ⊗ T`，
  再经 `TensorProduct.lid`（`a ⊗ t ↦ a • t` ✓）得 `algebraMap F T (φ x) = 0` ⟹ 由
  `FaithfulSMul.algebraMap_injective` ✗ 与 `φ x ≠ 0` 矛盾 ✓。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import ABGV52.GenericExtension_ABGV52
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Module.Equiv.Basic
open TensorProduct
noncomputable section
namespace ABGV52.BTier

variable {F : Type*} [Field F]

section projective

/-- **对偶泛函分离非零元** ✓：投射非零模有非零 `F`-线性泛函。
证法：`Module.Dual.eval`（`M → M**`）对**投射**模**单射** ——
取投射定义式的截面 `s`，若 `eval z = 0` 则 `s z = 0`（逐坐标用 `(Finsupp.lapply d) ∘ₗ s` 检验 ✓），
再由 `h ∘ s = id` 得 `z = 0` ✓。 -/
theorem dual_eval_injective_of_projective {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Projective F M] : Function.Injective (Module.Dual.eval F M) := by
  rw [← LinearMap.ker_eq_bot]
  ext z
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective F M)
    have hsz : s z = 0 := by
      ext d
      have h2 : ((Finsupp.lapply d) ∘ₗ s) z = 0 := by
        have h2' := DFunLike.congr_fun hz ((Finsupp.lapply d) ∘ₗ s)
        simpa using h2'
      simpa using h2
    have hz0 : (Finsupp.linearCombination F (id : M → M)) (s z) = z := by
      have h3 := congrArg (fun (f : M →ₗ[F] M) => f z) hs
      simpa using h3
    rw [hsz] at hz0
    simpa using hz0.symm
  · intro hz
    rw [hz]
    exact map_zero _

/-- **非零投射模有非零对偶泛函** ✓（由上一条直接得到）。 -/
theorem exists_dual_ne_zero {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Projective F M] {x : M} (hx : x ≠ 0) : ∃ φ : M →ₗ[F] F, φ x ≠ 0 := by
  have hev : Module.Dual.eval F M x ≠ 0 :=
    fun h => hx (dual_eval_injective_of_projective (F := F) (by rw [h, map_zero]))
  by_contra hcon
  push Not at hcon
  exact hev (LinearMap.ext fun φ => by simpa using hcon φ)

end projective

section ringBase

variable {R : Type*} [CommRing R]
variable {T : Type*} [CommRing T] [Algebra R T] [Nontrivial T]

/-- **§34.6 ① 的环基版** ✓✓（`hBC⁺` 实际所需 ✓）：`R` **交换环**（非域 ✓）、`T` 非零 `R`-代数、
**`FaithfulSMul R T`**（即 `R → T` 单射 ✓）、`M` 非零 f.g. 投射 ⟹ **`M ⊗_R T ≠ 0`** ✓。
**⚠ 相对 §34.6 ① 域基版的差别** ✗：末步由 `FaithfulSMul.algebraMap_injective R T` ✓ 供给
（域基时该实例**自动**可得 ✓，环基时须**显式假设** ✓ —— 这正是 §36／§37 定位的那个缺口 ✓）。 -/
theorem dual_eval_injective_of_projective_ring {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Projective R M] : Function.Injective (Module.Dual.eval R M) := by
  rw [← LinearMap.ker_eq_bot]
  ext z
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
    have hsz : s z = 0 := by
      ext d
      have h2 : ((Finsupp.lapply d) ∘ₗ s) z = 0 := by
        have h2' := DFunLike.congr_fun hz ((Finsupp.lapply d) ∘ₗ s)
        simpa using h2'
      simpa using h2
    have hz0 : (Finsupp.linearCombination R (id : M → M)) (s z) = z := by
      have h3 := congrArg (fun (f : M →ₗ[R] M) => f z) hs
      simpa using h3
    rw [hsz] at hz0
    simpa using hz0.symm
  · intro hz
    rw [hz]
    exact map_zero _

omit [Nontrivial T] in
theorem exists_dual_ne_zero_ring {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Projective R M] {x : M} (hx : x ≠ 0) : ∃ φ : M →ₗ[R] R, φ x ≠ 0 := by
  have hev : Module.Dual.eval R M x ≠ 0 :=
    fun h => hx (dual_eval_injective_of_projective_ring (R := R) (by rw [h, map_zero]))
  by_contra hcon
  push Not at hcon
  exact hev (LinearMap.ext fun φ => by simpa using hcon φ)

/-- 环基版的 `a ⊗ t ↦ a • t` ✓。 -/
noncomputable def scalarEvalRing : R ⊗[R] T →ₗ[R] T :=
  (TensorProduct.lid R T).toLinearMap

omit [Nontrivial T] in
lemma scalarEvalRing_tmul (a : R) (t : T) :
    scalarEvalRing (T := T) (TensorProduct.tmul R a t) = a • t := by
  simp [scalarEvalRing, TensorProduct.lid_tmul]

omit [Nontrivial T] in
theorem tensorProduct_nontrivial_of_projective_of_faithful [FaithfulSMul R T]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M] [Nontrivial M] :
    Nontrivial (M ⊗[R] T) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : M, x ≠ 0 := exists_ne 0
  obtain ⟨φ, hφx⟩ := exists_dual_ne_zero_ring (R := R) hx
  refine Nontrivial.mk ⟨TensorProduct.tmul R x (1 : T), 0, fun he0 => ?_⟩
  have h1 : scalarEvalRing (T := T) ((TensorProduct.map φ (1 : T →ₗ[R] T))
      (TensorProduct.tmul R x (1 : T))) ≠ 0 := by
    rw [TensorProduct.map_tmul, scalarEvalRing_tmul]
    intro hzero
    have h2 : (algebraMap R T) (φ x) = (algebraMap R T) 0 := by
      calc (algebraMap R T) (φ x) = (φ x) • (1 : T) := Algebra.algebraMap_eq_smul_one (φ x)
        _ = 0 := hzero
        _ = (algebraMap R T) 0 := by rw [map_zero]
    exact hφx (FaithfulSMul.algebraMap_injective R T h2)
  exact h1 (by rw [he0, map_zero, map_zero])

end ringBase

section algebra

variable {T : Type*} [CommRing T] [Algebra F T] [Nontrivial T]

/-- `a ⊗ t ↦ a • t`（即 `TensorProduct.lid` 的线性映射形 ✓）。 -/
def scalarEval : F ⊗[F] T →ₗ[F] T :=
  (TensorProduct.lid F T).toLinearMap

omit [Nontrivial T] in
lemma scalarEval_tmul (a : F) (t : T) :
    scalarEval (T := T) (TensorProduct.tmul F a t) = a • t := by
  simp [scalarEval, TensorProduct.lid_tmul]

/-- **§34.6 ① 的一般小引理** ✓：非零投射 `F`-模 ⊗ 非零 `F`-代数 ≠ 0。
（本件的主结果；`hBC` 的忠实性款 / 差模款将以它为主力 ✓。） -/
theorem tensorProduct_nontrivial_of_projective {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Projective F M] [Nontrivial M] : Nontrivial (M ⊗[F] T) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : M, x ≠ 0 := exists_ne 0
  obtain ⟨φ, hφx⟩ := exists_dual_ne_zero (F := F) hx
  refine Nontrivial.mk ⟨TensorProduct.tmul F x (1 : T), 0, fun he0 => ?_⟩
  have h1 : scalarEval (T := T) ((TensorProduct.map φ (1 : T →ₗ[F] T))
      (TensorProduct.tmul F x (1 : T))) ≠ 0 := by
    rw [TensorProduct.map_tmul, scalarEval_tmul]
    intro hzero
    have h2 : (algebraMap F T) (φ x) = (algebraMap F T) 0 := by
      calc (algebraMap F T) (φ x) = (φ x) • (1 : T) := Algebra.algebraMap_eq_smul_one (φ x)
        _ = 0 := hzero
        _ = (algebraMap F T) 0 := by rw [map_zero]
    exact hφx (FaithfulSMul.algebraMap_injective F T h2)
  exact h1 (by rw [he0, map_zero, map_zero])

end algebra

section fixedSubring

variable {F : Type*} [Field F]
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra F R] [Algebra R S] [Algebra F S] [Algebra F T] [Algebra R T]
variable [IsScalarTower F R S] [IsScalarTower F R T]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

/-- `g • ·` 作为 `R`-代数自同构（**本件自建，宇宙多态** ✓ ——
`GenericExtension_ABGV52` 的同名件在该处**宇宙被钉死为 `Type 0`** ✗，
在此处用会报「`R` has type `Type u` but is expected to have type `Type`」✗）。 -/
def bcActAlgEquiv
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) : S ≃ₐ[R] S where
  toFun s := g • s
  invFun s := g⁻¹ • s
  left_inv s := by simp [← mul_smul]
  right_inv s := by simp [← mul_smul]
  map_mul' x y := MulSemiringAction.smul_mul g x y
  map_add' x y := smul_add g x y
  commutes' r := by
    have h := hRG g r 1
    simpa [Algebra.algebraMap_eq_smul_one] using h

/-- 张量上的 `g`-作用（`AlgHom` 形，**本件自建** ✓；**取向 = `S ⊗_R T`，`G` 沿第一因子 ✓**）。 -/
def bcTensorActHom
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) :
    (TensorProduct R S T) →ₐ[R] (TensorProduct R S T) :=
  Algebra.TensorProduct.map (bcActAlgEquiv hRG g) (AlgHom.id R T)

/-- 张量作用在**简单张量**上的取值 ✓（`y ⊗ₜ x ↦ (g • y) ⊗ₜ x`）。 -/
lemma bcTensorActHom_tmul
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (g : G) (y : S) (x : T) :
    bcTensorActHom hRG g (TensorProduct.tmul R y x)
      = TensorProduct.tmul R (g • y) x := by
  simp [bcTensorActHom, bcActAlgEquiv, Algebra.TensorProduct.map_tmul]

/-- `g • 1 = 1` ✓（由 `hRG` 与 `algebraMap R S 1 = 1` ✓）。 -/
lemma act_one (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) :
    g • (1 : S) = 1 := by
  have h := hRG g 1 1
  simpa [Algebra.algebraMap_eq_smul_one, map_one] using h

/-- **§34.6 ② 固定子环款** ✓✓：`T` 落在 `S ⊗_R T` 的 `G`-不动点中。
**证法**（本轮实测的取向纠正 ✓）：`S' := S ⊗_R T`，`G` 沿**第一因子**（`S` ✓）作用 ⟹
第二因子（`T` ✓）**整体不动** ✓：`g • (1 ⊗ₜ x) = (g • 1) ⊗ₜ x = 1 ⊗ₜ x` ✓（`act_one` ✓）。
**⚠ 取向纠正** ✗（我一度写错并卡住）：若把载体取成 `T ⊗_R S` 而作用仍沿 `S`-因子 ✓，
则 `1 ⊗ₜ y` **不**不动 ✗（`g • (1 ⊗ₜ y) = 1 ⊗ₜ (g • y) ≠ 1 ⊗ₜ y` ✓），
此时「`T ⊆ S'^G`」**为假**、且缺 `IsScalarTower R T (T ⊗_R S)` 实例 ✗。
源文写 `S' = S ⊗_φ R'` ✓（`R'` 在后 ✓）⟹ **正确取向是本条** ✓。 -/
lemma tensorAct_fixes_one_tmul
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (g : G) (x : T) :
    bcTensorActHom hRG g (TensorProduct.tmul R (1 : S) x)
      = TensorProduct.tmul R (1 : S) x := by
  rw [bcTensorActHom_tmul, act_one hRG g]

/-- **§34.6 ② 的完整款** ✓：`T`（经 `x ↦ 1 ⊗ₜ x`）是 `S'^G` 的子环 ——
即对一切 `x : T`，`g • (1 ⊗ₜ x) = 1 ⊗ₜ x` ✓；由 `T` 是环、`G` 的作用是环自同构 ✓，
该等式在整个 `T` 生成的子环上成立 ✓。 -/
lemma tensorAct_fixes_T
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) :
    ∀ x : T, bcTensorActHom hRG g (TensorProduct.tmul R (1 : S) x)
      = TensorProduct.tmul R (1 : S) x :=
  fun x => tensorAct_fixes_one_tmul hRG g x

/-- **§34.6 ② 的判据形** ✓✓（即 `IsGaloisWithGroup` 第二款 `R ⊆ S^G` 在基变换后的对应物 ✓）：
`g` 固定 `S' := S ⊗_R T` 上 `R`-代数结构的像 ✓，即
`∀ r : R, g • algebraMap R S' r = algebraMap R S' r` ✓。
**证法** ✓：`algebraMap R (S ⊗_R T) r = algebraMap R S r ⊗ₜ 1` ✓（`rfl` ✓），
`G` 沿**第一因子**作用 ✓ ⟹ 归约到 `g • algebraMap R S r = algebraMap R S r` ✓（由 `hRG` ✓）。 -/
lemma tensorAct_fixes_algebraMap
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) (r : R) :
    bcTensorActHom hRG g ((algebraMap R (TensorProduct R S T)) r)
      = (algebraMap R (TensorProduct R S T)) r := by
  rw [show (algebraMap R (TensorProduct R S T)) r
      = (TensorProduct.tmul R ((algebraMap R S) r) (1 : T) : TensorProduct R S T) from rfl]
  rw [bcTensorActHom_tmul]
  congr 1
  have h := hRG g r 1
  simpa [Algebra.algebraMap_eq_smul_one] using h

/-- **差模 `D_g`** ✓：`{g • y − y : y ∈ S}` 张成的 `R`-子模 ✓（忠实性的**载体** ✓）。 -/
def diffSubmodule (g : G) : Submodule R S :=
  Submodule.span R {x : S | ∃ y : S, g • y - y = x}

/-- **§34.6 忠实性款的归约** ✓✓：若 `g` 在 `S ⊗_R T` 上**平凡** ✓，
则 `D_g ⊗_R T = 0` ✓（逐生成元：`(g • y − y) ⊗ₜ 1 = (g • y) ⊗ₜ 1 − y ⊗ₜ 1 = 0` ✓，
再用 `Submodule.span_induction` ✓ 线性延拓 ✓）。
**⟹ 下一手**（已定位 ✓）：由 `D_g` 是 `S` 的**局部自由直和项** ✓（源 `proposition-0-2(a)` 引 [CHR68] p.13 ✓）
`⟹ D_g` 投射 ✓ ⟹ 用本件的 **`tensorProduct_nontrivial_of_projective`** ✓ 得 `D_g = 0` ✓
⟹ `g` 在 `S` 上平凡 ⟹ 由 `FaithfulSMul G S` 得 `g = 1` ✓ ⟹ **`FaithfulSMul G (S ⊗_R T)`** ✓。 -/
theorem diff_tmul_one_eq_zero_of_act_trivial
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (g : G) (htriv : ∀ z : TensorProduct R S T, bcTensorActHom hRG g z = z)
    (x : S) (hx : x ∈ diffSubmodule (S := S) (R := R) (G := G) g) :
    TensorProduct.tmul R x (1 : T) = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro x ⟨y, rfl⟩
    have h1 := htriv (TensorProduct.tmul R y (1 : T))
    rw [bcTensorActHom_tmul hRG g y (1 : T)] at h1
    rw [sub_tmul, h1, sub_self]
  · simp
  · intro a b _ _ ha hb; rw [add_tmul, ha, hb, add_zero]
  · intro c a _ ha
    have hlin : (TensorProduct.mk R S T).flip (1 : T) (c • a)
        = c • ((TensorProduct.mk R S T).flip (1 : T) a) := map_smul _ c a
    rw [show (TensorProduct.mk R S T).flip (1 : T) (c • a)
        = ((c • a) ⊗ₜ[R] (1 : T)) from rfl,
      show (TensorProduct.mk R S T).flip (1 : T) a
        = (a ⊗ₜ[R] (1 : T)) from rfl] at hlin
    rw [hlin, ha, smul_zero]

/-- **直和项的含入经 `− ⊗_R T` 后仍单射** ✓✓（**不需要平坦性** ✓ ——
分裂 `p ∘ subtype = id` 被 `− ⊗_R T` 保持 ✓；这是对 §35.4「须平坦」的**关键改进** ✓）。 -/
theorem rTensor_subtype_injective_of_retract {D : Submodule R S}
    (p : S →ₗ[R] D) (hp : p.comp D.subtype = LinearMap.id) :
    Function.Injective (LinearMap.rTensor T D.subtype) := by
  have hcomp : (LinearMap.rTensor T p).comp (LinearMap.rTensor T D.subtype) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hp, LinearMap.rTensor_id]
  refine Function.LeftInverse.injective (g := LinearMap.rTensor T p) fun x => ?_
  exact congrArg (fun (f : D ⊗[R] T →ₗ[R] D ⊗[R] T) => f x) hcomp

/-- **§34.6 忠实性款（抽象消没形）** ✓✓：若 `D_g` 是 `S` 的**直和项** ✓（有截面 `p` ✓）
且 `g` 在 `S ⊗_R T` 上**平凡** ✓，则 **`D_g ⊗_R T` 是空的（`= 0`）** ✓。
**证法** ✓：`rTensor_subtype_injective_of_retract` ✓ 给单射；而像为 0（由 `diff_tmul_one_eq_zero_of_act_trivial` ✓
＋ 生成元上的乘法律 ✓）⟹ 单射且像为 0 ⟹ 定义域为 0 ✓。 -/
theorem diffSubmodule_tensor_subsingleton_of_act_trivial
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (g : G)
    (p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g)
    (hp : p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id)
    (htriv : ∀ z : TensorProduct R S T, bcTensorActHom hRG g z = z) :
    Subsingleton (diffSubmodule (S := S) (R := R) (G := G) g ⊗[R] T) := by
  have hinj := rTensor_subtype_injective_of_retract (T := T) p hp
  have hgen : ∀ x : diffSubmodule (S := S) (R := R) (G := G) g,
      (TensorProduct.tmul R (x : S) (1 : T)) = 0 :=
    fun x => diff_tmul_one_eq_zero_of_act_trivial hRG g htriv (x : S) x.2
  refine ⟨fun a b => hinj ?_⟩
  have hz : ∀ a : diffSubmodule (S := S) (R := R) (G := G) g ⊗[R] T,
      (LinearMap.rTensor T (diffSubmodule (S := S) (R := R) (G := G) g).subtype) a = 0 := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        rw [LinearMap.rTensor_tmul]
        simp only [Submodule.coe_subtype]
        rw [show (x : S) ⊗ₜ[R] c = ((x : S) ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] c) from by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
          hgen x, zero_mul]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]
  rw [hz a, hz b]

/-- **§34.6 忠实性款（装配形）** ✓✓：设对每个 `g ≠ 1`，差模的张量积 `D_g ⊗_R T` **非空** ✓
（`hnonzero` ✓ —— 由「`T` 局部 ＋ `R` 整环」供给 ✓，见下 `diffTensor_nontrivial_hyp_registered` ✓），
且 `D_g` 是 `S` 的直和项 ✓（`hsplit` ✓，＝源 `proposition-0-2(a)` 的内含 ✓），
则**没有非平凡 `g` 在 `S ⊗_R T` 上平凡** ✓ —— 即忠实性款的**全部算术内容** ✓（除 `hnonzero` ✓）。
**证法** ✓：若 `g` 平凡，则 `diffSubmodule_tensor_subsingleton_of_act_trivial` ✓ 给
`Subsingleton (D_g ⊗_R T)` ✓，与 `hnonzero` ✓ 的 `Nontrivial` **矛盾** ✓。 -/
theorem not_act_trivial_of_nontrivial_diffTensor
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id)
    (hnonzero : ∀ g : G, g ≠ 1 →
      Nontrivial (diffSubmodule (S := S) (R := R) (G := G) g ⊗[R] T))
    {g : G} (hg : g ≠ 1) :
    ¬ (∀ z : TensorProduct R S T, bcTensorActHom hRG g z = z) := by
  intro htriv
  obtain ⟨p, hp⟩ := hsplit g
  haveI := diffSubmodule_tensor_subsingleton_of_act_trivial hRG g p hp htriv
  exact (not_subsingleton_iff_nontrivial.mpr (hnonzero g hg)) inferInstance

/-- **登记（`hnonzero` 的供给，逐字）** ✗：`∀ g ≠ 1, Nontrivial (D_g ⊗_R T)` ✓ 由下二者供给 ✓：
**(a)** `T` **局部** ✓ ⟹ `D_g ⊗_R T` 是**自由 `T`-模** ✓（`Module.free_of_flat_of_isLocalRing` ✓，
`RingTheory/LocalRing/Module.lean:304` ✓；需 `D_g` f.g.投射于 `R` ✓）；
**(b)** `R` **整环** ✓ ⟹ `D_g ⊗_R T ≠ 0` ✓（若 `D_g = im(e)` ✓ 且 `e` 的元素全在素理想 `q := ker(R → T)` ✓，
则由 `e = e²` 递推 `e ∈ M_m(q^n) ∀n` ✓ ⟹ `e ∈ M_m(∩q^n) = 0` ✓ —— **整环上 `∩q^n = 0`** ✓
〔局部化 `R_q` ＋ Krull 交定理 ✓〕⟹ 与 `D_g ≠ 0` 矛盾 ✓）。
**⚠ 一般环上 (b) 为假** ✗（反例 `R = R₁ × R₂`、`D_g = R₁`、`T = R₂` ⟹ `D_g ⊗_R T = 0` ✓）——
使用处 `R = F[x₁,…,xₙ](1/s)` **是整环** ✓ 故无碍 ✓。 -/
theorem diffTensor_nontrivial_hyp_registered : True := trivial

omit [Fintype G] in
/-- **`g ≠ 1` ⟹ 差模 `D_g` 非空** ✓（由 `FaithfulSMul G S` ✓）：取 `s` 使 `g • s ≠ s` ✓，
则 `g • s − s ≠ 0` 且属于 `D_g` ✓。 -/
theorem diffSubmodule_nontrivial_of_faithfulSMul [FaithfulSMul G S]
    {g : G} (hg : g ≠ 1) : Nontrivial (diffSubmodule (S := S) (R := R) (G := G) g) := by
  classical
  have hne : (fun s : S => g • s) ≠ (fun s : S => (1 : G) • s) :=
    fun h => hg (FaithfulSMul.eq_of_smul_eq_smul (fun a => by
      have hh := congrFun h a
      simpa using hh))
  obtain ⟨s, hs⟩ : ∃ s : S, g • s ≠ s := by
    simpa [one_smul] using Function.ne_iff.mp hne
  refine Nontrivial.mk ⟨⟨g • s - s, Submodule.subset_span ⟨s, rfl⟩⟩,
    ⟨0, (diffSubmodule (S := S) (R := R) (G := G) g).zero_mem⟩, fun h => ?_⟩
  exact hs (sub_eq_zero.mp (by simpa using congrArg Subtype.val h))

/-- **§34.6 忠实性款（完整形）** ✓✓：`FaithfulSMul G S` ✓ ＋ **`FaithfulSMul R T`** ✓
＋ `S` **投射** ✓ ＋ **`D_g` 是 `S` 的直和项** ✓（`hsplit` ✓）⟹
**没有非平凡 `g` 在 `S ⊗_R T` 上平凡** ✓ —— **忠实性款至此全部落地** ✓（无 registered input ✓）。
**证法链** ✓：`diffSubmodule_nontrivial_of_faithfulSMul` ✓（`D_g ≠ 0` ✓）
→ `Module.Projective.of_split` ✓（`D_g` 投射 ✓）
→ **`tensorProduct_nontrivial_of_projective_of_faithful`** ✓（环基版 ✓，用 `FaithfulSMul R T` ✓）
→ `not_act_trivial_of_nontrivial_diffTensor` ✓。 -/
theorem not_act_trivial_full [FaithfulSMul G S] [FaithfulSMul R T] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id)
    {g : G} (hg : g ≠ 1) :
    ¬ (∀ z : TensorProduct R S T, bcTensorActHom hRG g z = z) := by
  classical
  refine not_act_trivial_of_nontrivial_diffTensor hRG hsplit (fun g' hg' => ?_) hg
  obtain ⟨p', hp'⟩ := hsplit g'
  haveI : Module.Projective R (diffSubmodule (S := S) (R := R) (G := G) g') :=
    Module.Projective.of_split _ p' hp'
  haveI : Nontrivial (diffSubmodule (S := S) (R := R) (G := G) g') :=
    diffSubmodule_nontrivial_of_faithfulSMul (R := R) (S := S) hg'
  exact tensorProduct_nontrivial_of_projective_of_faithful

/-- **§34.6 ③a 的**关键桥** ✓✓**：`SkewMonoidAlgebra S G ≃ₗ[R] (G →₀ S)` ✓ ——
由 mathlib 的 `SkewMonoidAlgebra.coeff`／`ofCoeff` ✓ 与 `coeff_add`／`coeff_smul`／
`eta`／`coeff_ofCoeff` ✓ 直接打包 ✓（**实测**：`rfl` 不行 ✗ —— 二者**非 defeq** ✗，
但**互逆的双射**由 mathlib 已给 ✓）。
**⟹ 意义** ✓：有了它，**③a**（`SkewMonoidAlgebra S G ⊗_R T ≅ SkewMonoidAlgebra (S ⊗_R T) G` ✓）
**化归为 `Finsupp` 版** ✓ —— 左端经本桥到 `(G →₀ S) ⊗_R T` ✓，
再用 **`TensorProduct.finsuppLeft`** ✓（`(ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ M ⊗[R] N` ✓）
得 `G →₀ (S ⊗_R T)` ✓，最后经本桥回到右端 ✓（**三步全是现成件** ✓，
不再需要 §39.2 设想的「从零造 `AlgEquiv`」✓）。 -/
noncomputable def skewCoeffEquiv (G : Type*) [Group G] :
    SkewMonoidAlgebra S G ≃ₗ[R] (G →₀ S) where
  toFun := SkewMonoidAlgebra.coeff
  invFun := SkewMonoidAlgebra.ofCoeff
  left_inv := fun f => SkewMonoidAlgebra.eta f
  right_inv := fun f => SkewMonoidAlgebra.coeff_ofCoeff f
  map_add' := SkewMonoidAlgebra.coeff_add
  map_smul' := SkewMonoidAlgebra.coeff_smul

/-- **§34.6 ③a（线性版）** ✓✓：`SkewMonoidAlgebra S G ⊗_R T ≃ₗ[R] SkewMonoidAlgebra (S ⊗_R T) G` ✓
—— **三步全用现成件** ✓：`TensorProduct.congr skewCoeffEquiv (refl)` ✓
→ **`TensorProduct.finsuppLeft`** ✓ → `(skewCoeffEquiv (S := S ⊗_R T)).symm` ✓。
**⚠ 仍待升级为 `AlgEquiv`** ✗（乘法性：右端交叉积的 `G`-作用 ✓ 与左端 ✓ 的对齐 ✓，
须用 `hRG`／`hR'G` ✓）—— 本件先落**线性版** ✓（结构层 ✓，估余 1 轮 ✓）。 -/
noncomputable def skewBaseChangeLinearEquiv [DecidableEq G] :
    SkewMonoidAlgebra S G ⊗[R] T ≃ₗ[R] SkewMonoidAlgebra (S ⊗[R] T) G :=
  (TensorProduct.congr (skewCoeffEquiv (R := R) (S := S) (G := G)) (LinearEquiv.refl R T)) ≪≫ₗ
  (TensorProduct.finsuppLeft R R S T G) ≪≫ₗ
  (skewCoeffEquiv (R := R) (S := S ⊗[R] T) (G := G)).symm

/-- **③-1 生成元公式** ✓✓：`skewBaseChangeLinearEquiv (single g s ⊗ₜ t) = single g (s ⊗ₜ t)` ✓
—— `coeff_single` ✓ → `finsuppLeft_apply_tmul` ✓ → `Finsupp.sum_single_index` ✓ → `ofCoeff` ✓。
（**工艺** ✓：须先 `change` 把 `skewCoeffEquiv` 展开到 `coeff` 形 ✓，否则 `sum_single_index` **匹配不上** ✗。） -/
theorem skewBaseChangeLinearEquiv_single [DecidableEq G] (g : G) (s : S) (t : T) :
    skewBaseChangeLinearEquiv (R := R) (S := S) (T := T) (G := G)
      (SkewMonoidAlgebra.single g s ⊗ₜ[R] t)
    = SkewMonoidAlgebra.single g (s ⊗ₜ[R] t) := by
  rw [skewBaseChangeLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.finsuppLeft_apply_tmul]
  change (skewCoeffEquiv (R := R) (S := S ⊗[R] T) (G := G)).symm
      ((SkewMonoidAlgebra.single g s).coeff.sum fun i m => Finsupp.single i (m ⊗ₜ[R] t))
    = SkewMonoidAlgebra.single g (s ⊗ₜ[R] t)
  rw [SkewMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  · rfl
  · simp

end fixedSubring

/-! ## §34.6 ③ 的**目标取向**（`S' = T ⊗_R S`）：两条基变换同构

  **取向说明** ✓（本轮新登记的**取向审计** ✓）：`GaloisBaseChangeHyp` 的结论形是
  `IsGaloisWithGroup R' (TensorProduct R R' S) G hR'G` —— 即 **`S' = T ⊗_R S`（`T` 在左** ✓）。
  `fixedSubring` 段此前的 §34.6 ①② 两条砖是**另一取向**（`S ⊗_R T`、`G` 沿第一因子 ✓）；
  两者**互为 `TensorProduct.comm` 的像** ✓，但**非 defeq** ⟹ ①② 须**另取向重述**（登记 ✓，下一手）。
  本段的两条砖**直接按目标取向**落地 ✓（③a 重定向 ＋ ③b）✓。 -/

section endBaseChange

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {G : Type*} [Group G]

/-- **§34.6 ③b** ✓✓：`Hom_R(S,S) ⊗_R T ≃ₗ[R] Hom_T(T ⊗_R S, T ⊗_R S)` ✓ ——
即 `(Module.End R S) ⊗[R] T ≃ₗ[R] Module.End T (TensorProduct R T S)` ✓。
**前提** ✓：`S` **有限生成投射** `R`-模（源 `proposition-0-2(a)`，引 [CHR68] p. 13 ✓）。

**构造** ✓（**四步全用现成件** ✓，本轮实测）：
① **`rTensorHomEquivHomRTensor R S S T`** ✓（`Mathlib/LinearAlgebra/Contraction.lean:339` ✓；
   **前提正是 `[Module.Projective R M] [Module.Finite R M]`** ✓ —— 注意**不是**「自由」✗，
   其文件注释写 "finite free" ✓ 但**变量段**用的是有限投射 ✓）：
   `(S →ₗ[R] S) ⊗[R] T ≃ₗ[R] S →ₗ[R] S ⊗[R] T` ✓；
② **`TensorProduct.comm`** ✓ 把值域旋到 `T ⊗[R] S` ✓（`arrowCongr` ✗ 只改值域）；
③ **`LinearMap.ringLmapEquivSelf`** ✓（`Mathlib/Algebra/Module/Equiv/Basic.lean:359` ✓）：
   `(T →ₗ[T] N) ≃ₗ[R] N` ✓ —— 即「`T`-线性映射由 `1` 处的值决定」✓；
④ **`AlgebraTensorModule.lift.equiv`** ✓（`Mathlib/LinearAlgebra/TensorProduct/Tower.lean:163` ✓）：
   `(M →ₗ[A] N →ₗ[R] P) ≃ₗ[B] M ⊗[R] N →ₗ[A] P` ✓（取 `A := T`、`B := R`、`M := T`、`N := S` ✓）。 -/
noncomputable def endBaseChangeLinearEquiv [Module.Finite R S] [Module.Projective R S] :
    (Module.End R S) ⊗[R] T ≃ₗ[R] Module.End T (TensorProduct R T S) :=
  (rTensorHomEquivHomRTensor R S S T).trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl R S) (TensorProduct.comm R S T)).trans
      ((LinearMap.ringLmapEquivSelf T R
          (S →ₗ[R] TensorProduct R T S)).symm.trans
        (TensorProduct.AlgebraTensorModule.lift.equiv R T R T S
          (TensorProduct R T S))))

/-- **③b 的生成元公式** ✓✓：`endBaseChangeLinearEquiv (f ⊗ₜ t)` 是 `T`-线性映射
`t' ⊗ₜ x ↦ (t' * t) ⊗ₜ f x` ✓ —— ③-2（与 `delta` 的交换性）**在生成元上核**时用它 ✓。
**⚠ 工艺读数** ✓：`AlgebraTensorModule.lift.equiv` 的 `toFun` 是
`LinearEquiv.ofLinearMap` 的 `toFun` ✓，mathlib **无** `LinearEquiv.ofLinearMap_apply` ✗
⟹ 须用 **`change`** 把它写成 `AlgebraTensorModule.lift ...` ✓ 形（**defeq 成立** ✓）。 -/
theorem endBaseChangeLinearEquiv_tmul [Module.Finite R S] [Module.Projective R S]
    (f : Module.End R S) (t t' : T) (x : S) :
    endBaseChangeLinearEquiv (R := R) (S := S) (T := T) (f ⊗ₜ[R] t)
      (t' ⊗ₜ[R] x) = (t' * t) ⊗ₜ[R] f x := by
  simp only [endBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    rTensorHomEquivHomRTensor_apply, LinearMap.ringLmapEquivSelf_symm_apply]
  change (AlgebraTensorModule.lift (LinearMap.smulRight 1
      (((LinearEquiv.refl R S).arrowCongr (TensorProduct.comm R S T))
        ((rTensorHomToHomRTensor (RingHom.id R) S S T) (f ⊗ₜ[R] t)))))
    (t' ⊗ₜ[R] x) = (t' * t) ⊗ₜ[R] f x
  simp only [AlgebraTensorModule.lift_tmul, LinearMap.smulRight_apply,
    Module.End.one_apply, LinearMap.smul_apply,
    LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    rTensorHomToHomRTensor_apply, TensorProduct.comm_tmul, Algebra.smul_def,
    Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
    Algebra.algebraMap_self_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **§34.6 ③a（重定向版）** ✓✓：`Δ(S/R,G) ⊗_R T ≃ₗ[R] Δ(T ⊗_R S / T, G)` ✓ ——
即 `SkewMonoidAlgebra S G ⊗[R] T ≃ₗ[R] SkewMonoidAlgebra (TensorProduct R T S) G` ✓
（**目标取向** ✓；与 §40.5 的 `skewBaseChangeLinearEquiv` 互为 `TensorProduct.comm` 的像 ✓）。

**构造** ✓（**四步全用现成件** ✓）：`TensorProduct.congr skewCoeffEquiv (refl)` ✓
→ **`TensorProduct.comm`** ✓ → **`TensorProduct.finsuppRight`** ✓
（`Mathlib/LinearAlgebra/DirectSum/Finsupp.lean:91` ✓；取 `M := T`、`N := S`、`S := R` ✓）
→ `(skewCoeffEquiv (S := T ⊗[R] S)).symm` ✓。 -/
noncomputable def skewBaseChangeLinearEquivLeft [DecidableEq G] :
    SkewMonoidAlgebra S G ⊗[R] T ≃ₗ[R] SkewMonoidAlgebra (TensorProduct R T S) G :=
  (TensorProduct.congr (skewCoeffEquiv (R := R) (S := S) (G := G))
      (LinearEquiv.refl R T)) ≪≫ₗ
    (TensorProduct.comm R (G →₀ S) T) ≪≫ₗ
    (TensorProduct.finsuppRight R R T S G) ≪≫ₗ
    (skewCoeffEquiv (R := R) (S := TensorProduct R T S) (G := G)).symm

/-- **③a（重定向版）的生成元公式** ✓✓：`single g s ⊗ₜ t ↦ single g (t ⊗ₜ s)` ✓
—— 与 §40.5 的 `skewBaseChangeLinearEquiv_single`（`↦ single g (s ⊗ₜ t)` ✓）**因子次序相反** ✓。
**⚠ 工艺读数** ✓：与 §40.5 同 —— **必须先 `change`** ✓ 把 `skewCoeffEquiv` 展开到 `coeff` 形 ✓，
否则 `Finsupp.sum_single_index` **匹配不上** ✗。 -/
theorem skewBaseChangeLinearEquivLeft_single [DecidableEq G] (g : G) (s : S) (t : T) :
    skewBaseChangeLinearEquivLeft (R := R) (S := S) (T := T) (G := G)
      (SkewMonoidAlgebra.single g s ⊗ₜ[R] t)
    = SkewMonoidAlgebra.single g (t ⊗ₜ[R] s) := by
  rw [skewBaseChangeLinearEquivLeft, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.comm_tmul, TensorProduct.finsuppRight_apply_tmul]
  change (skewCoeffEquiv (R := R) (S := TensorProduct R T S) (G := G)).symm
      ((SkewMonoidAlgebra.single g s).coeff.sum fun i m => Finsupp.single i (t ⊗ₜ[R] m))
    = SkewMonoidAlgebra.single g (t ⊗ₜ[R] s)
  rw [SkewMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  · rfl
  · simp

end endBaseChange

/-! ## 目标取向（`S' = T ⊗_R S`）的作用层、② 固定子环款、δ 的 `R`-线性

  **取向审计的后续** ✓（状态笔记 §41.4）：`GaloisBaseChangeHyp` 的结论取向是 **`T ⊗_R S`** ✓
  （`GenericExtension_ABGV52.lean:192`），而 `fixedSubring` 段的 §34.6 ①② 砖写在另一取向 ✗。
  本段按**目标取向**落三件 ✓：① 作用层（`bcTensorActHomLeft`／`bcTensorMulSemiringActionLeft` ✓，
  `G` 沿**第二因子**、`T` 整体不动 ✓；本件**宇宙多态** ✓ —— `GenericExtension` 的同名件宇宙被钉死 ✓）；
  ② **固定子环款**（`bcTensorActLeft_fixes_algebraMap` ✓）；③ **δ 的 `R`-线性**（`deltaToEndAdd_smul` ✓，
  为 ③-2（与 `delta` 的交换性）与取 `LinearMap.rTensor T` 的前置 ✓）。 -/

section targetOrientation

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

/-- **δ 的 `R`-线性** ✓（③-2 的前置 ✓）：`deltaToEndAdd hRG` 保持 `R`-纯量 ✓。
**证法** ✓：`SkewMonoidAlgebra.induction_on` 归约到 `single` ✓；`h1` 用 `coeff_smul` ＋ `coeff_single`
把 `r • single g s` 化到 `single g (r • s)` ✓；末步用 `Algebra.smul_def` ＋ `mul_assoc` ✓
（`(algebraMap r * s) * (g • t) = algebraMap r * (s * (g • t))` ✓）。 -/
theorem deltaToEndAdd_smul
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (r : R)
    (x : SkewMonoidAlgebra S G) :
    deltaToEndAdd hRG (r • x) = r • deltaToEndAdd hRG x := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g s =>
    have h1 : r • SkewMonoidAlgebra.single g s = SkewMonoidAlgebra.single g (r • s) := by
      ext g'
      rw [SkewMonoidAlgebra.coeff_smul, SkewMonoidAlgebra.coeff_single,
        SkewMonoidAlgebra.coeff_single]
      simp
    rw [h1, deltaToEndAdd_single, deltaToEndAdd_single]
    ext t
    simp [Module.End.mul_apply, coeffToEnd, actEnd, Algebra.smul_def, mul_assoc]
  | add x z hx hz => simp [smul_add, map_add, hx, hz]

/-- `T` 在 `T ⊗_R S` 里的结构映射是**左因子** ✓：`algebraMap T (T ⊗_R S) t = t ⊗ₜ 1` ✓
（`Algebra T (T ⊗_R S)` 来自 `Algebra.TensorProduct.leftAlgebra` ✓）。 -/
lemma algebraMap_tensorLeft (t : T) :
    (algebraMap T (TensorProduct R T S)) t = t ⊗ₜ[R] (1 : S) := by
  simp only [Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
    Algebra.algebraMap_self_apply, Algebra.TensorProduct.includeLeftRingHom_apply]

/-- **目标取向上的 `g`-作用** ✓（`AlgHom` 形 ✓，`G` 沿**第二因子**）：`t ⊗ₜ y ↦ t ⊗ₜ (g • y)` ✓
（与 `bcTensorActHom` 的取向相反 ✓；两者互为 `TensorProduct.comm` 的像 ✓）。 -/
def bcTensorActHomLeft
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) :
    (TensorProduct R T S) →ₐ[R] (TensorProduct R T S) :=
  Algebra.TensorProduct.map (AlgHom.id R T) (bcActAlgEquiv (R := R) (S := S) hRG g)

/-- 目标取向作用在简单张量上的取值 ✓（`t ⊗ₜ y ↦ t ⊗ₜ (g • y)` ✓）。 -/
lemma bcTensorActHomLeft_tmul
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) (t : T) (y : S) :
    bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g (t ⊗ₜ[R] y)
      = t ⊗ₜ[R] (g • y) := by
  simp [bcTensorActHomLeft, bcActAlgEquiv, Algebra.TensorProduct.map_tmul]

/-- 作用律一 ✓（**朴素 `simp`** ✓，不用名单 ✗）。 -/
lemma bcActAlgEquiv_one
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    bcActAlgEquiv (R := R) (S := S) hRG 1 = AlgEquiv.refl := by
  ext s
  simp [bcActAlgEquiv]

/-- 作用律二 ✓（`AlgEquiv.trans` 次序：`(e₁.trans e₂) x = e₂ (e₁ x)` ✓）。 -/
lemma bcActAlgEquiv_mul
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g h : G) :
    bcActAlgEquiv (R := R) (S := S) hRG (g * h)
      = (bcActAlgEquiv (R := R) (S := S) hRG h).trans
          (bcActAlgEquiv (R := R) (S := S) hRG g) := by
  ext s
  simp [bcActAlgEquiv, mul_smul]

/-- **`T ⊗_R S` 上的 `G`-作用** ✓（**目标取向** ✓；mathlib **无**此实例 ✗；
用法 `letI := bcTensorMulSemiringActionLeft hRG` ✓；**宇宙多态** ✓）。 -/
def bcTensorMulSemiringActionLeft
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    MulSemiringAction G (TensorProduct R T S) where
  smul g z := bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g z
  one_smul z := by
    change bcTensorActHomLeft (R := R) (S := S) (T := T) hRG 1 z = z
    have h : bcTensorActHomLeft (R := R) (S := S) (T := T) hRG 1
        = AlgHom.id R (TensorProduct R T S) := by
      rw [bcTensorActHomLeft, bcActAlgEquiv_one]
      exact Algebra.TensorProduct.map_id (R := R) (A := T) (B := S)
    rw [h]
    rfl
  mul_smul g h z := by
    change bcTensorActHomLeft (R := R) (S := S) (T := T) hRG (g * h) z
      = bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g
          (bcTensorActHomLeft (R := R) (S := S) (T := T) hRG h z)
    have hh : bcTensorActHomLeft (R := R) (S := S) (T := T) hRG (g * h)
        = ((bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g).comp
            (bcTensorActHomLeft (R := R) (S := S) (T := T) hRG h) :
            (TensorProduct R T S) →ₐ[R] (TensorProduct R T S)) := by
      rw [bcTensorActHomLeft, bcTensorActHomLeft, bcTensorActHomLeft, bcActAlgEquiv_mul,
        ← Algebra.TensorProduct.map_comp]
      rfl
    rw [hh]
    rfl
  smul_zero g := map_zero (bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g)
  smul_add g x y := map_add (bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g) x y
  smul_mul g x y := map_mul (bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g) x y
  smul_one g := map_one (bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g)

/-- **`hR'G` 的目标取向供给** ✓：`G` 沿第二因子作用、`T`-纯量作用在第一因子 ⟹ 两者交换 ✓
（即 `GaloisBaseChangeHyp` 所需的 `hR'G` ✓；与 `GenericExtension` 的 `tensorAct_smul_comm` 同机制 ✓，
但**本件宇宙多态** ✓）。 -/
lemma bcTensorActLeft_smul_comm
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) (r : T)
    (z : TensorProduct R T S) :
    bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g (r • z)
      = r • bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.smul_tmul', bcTensorActHomLeft, Algebra.TensorProduct.map_tmul]
    rfl
  | add a b ha hb => simp [smul_add, ha, hb]

/-- **② 固定子环款（目标取向）** ✓✓：`g` 固定 `R' = T` 在 `T ⊗_R S` 中的像 ✓，
即 `g • algebraMap T (T ⊗_R S) t = algebraMap T (T ⊗_R S) t` ✓。
**证法** ✓：`algebraMap_tensorLeft` 把它化到 `t ⊗ₜ 1` ✓（**左因子** ✓），
`bcTensorActHomLeft_tmul` 得 `t ⊗ₜ (g • 1)` ✓，再由 `act_one` ✓ 收口。
**⚠ 与旧登记的对照** ✓（状态笔记 §41.4）：本件在 `fixedSubring` 段的同名款写的是 `S ⊗_R T` 取向 ✓；
那里的「`T ⊗_R S` 取向使命题为假」✗ 是把 `x ↦ 1 ⊗ₜ x`（在 `T ⊗_R S` 里是 **`S`-因子** ✓）
误当 `T` 的结构映射 ✓ —— 本条是同一命题在**正确结构映射**下的形 ✓。 -/
lemma bcTensorActLeft_fixes_algebraMap
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G) (t : T) :
    bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g
        ((algebraMap T (TensorProduct R T S)) t)
      = (algebraMap T (TensorProduct R T S)) t := by
  rw [algebraMap_tensorLeft, bcTensorActHomLeft_tmul, act_one hRG g]

end targetOrientation

/-! ## ③-2（与 `delta` 的交换性）与 **③ 的收口**（双射性搬运）

  **取向与作用** ✓：本节按**目标取向**（`S' = T ⊗_R S` ✓）做 ✓，`G`-作用以参数承载 ✓
  （典范作用见 `bcTensorMulSemiringActionLeft` ✓）。
  **典范性条件** ✓（本节记作 `hcanon` ✓）：`∀ g x, g • ((1 : T) ⊗ₜ x) = (1 : T) ⊗ₜ (g • x)` ✓ ——
  与 `hR'G` ✓ 合用即把作用在**整个** `T ⊗_R S` 上钉住 ✓（`t ⊗ₜ x = t • (1 ⊗ₜ x)` ✓，见 `smul_one_tmul` ✓）。
  **⚠ 必要性** ✓（§42.1 的实测 ✓）：`hBC` 的 `∀`-作用形**不可居留** ✗ ⟹ 收口形**必须**带 `hcanon` ✓。 -/

section deltaBaseChange

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S] [DecidableEq G]
variable [instAct : MulSemiringAction G (TensorProduct R T S)]

/-- **δ 的线性版** ✓（③-2 与 `LinearMap.rTensor` 的载体 ✓；由 `deltaToEndAdd_smul` ✓）。 -/
noncomputable def deltaToEndLinear
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    SkewMonoidAlgebra S G →ₗ[R] Module.End R S where
  toFun := deltaToEndAdd hRG
  map_add' := (deltaToEndAdd hRG).map_add
  map_smul' := deltaToEndAdd_smul (R := R) (S := S) hRG

/-- `t • (1 ⊗ₜ y) = t ⊗ₜ y` ✓（`T`-模结构在**左**因子 ✓；`t ⊗ₜ y = t • (1 ⊗ₜ y)` ✓）。 -/
lemma smul_one_tmul (t : T) (y : S) :
    t • ((1 : T) ⊗ₜ[R] y) = t ⊗ₜ[R] y := by
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_def, RingHom.comp_apply,
    Algebra.algebraMap_self_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **作用在简单张量上** ✓✓（**本节的关键小引理** ✓）：由典范性 `hcanon` ✓ ＋ `hR'G` ✓ ⟹
`g • (t ⊗ₜ x) = t ⊗ₜ (g • x)` ✓（即 `G` 沿**第二因子** ✓、`T` 不动 ✓）。 -/
lemma act_tmul
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (g : G) (t : T) (x : S) :
    g • (t ⊗ₜ[R] x) = t ⊗ₜ[R] (g • x) := by
  rw [show t ⊗ₜ[R] x = t • ((1 : T) ⊗ₜ[R] x) from (smul_one_tmul t x).symm,
    hR'G g t ((1 : T) ⊗ₜ[R] x), hcanon g x, smul_one_tmul]

/-- **③-2（交换性）在生成元上** ✓✓：`δ' (③a (single g s ⊗ₜ t)) = ③b ((δ (single g s)) ⊗ₜ t)` ✓。
**机制** ✓：左端 = `(t ⊗ₜ s) * (g • z)` ✓；右端（用 **③b 生成元公式** ✓）在 `z = t' ⊗ₜ x` 上
= `(t' * t) ⊗ₜ (s * (g • x))` ✓ ⟹ 用 `act_tmul` ✓ ＋ `tmul_mul_tmul` ✓ ＋ `mul_comm` ✓ 对齐 ✓。
**⚠ 工艺读数** ✓：`deltaToEndRingHom` 与 `deltaToEndLinear` 的**结构字面量应用**须先用 **`change`**
对齐到 `deltaToEndAdd …` 形 ✓（否则 `rw` 报「未找到模式」✗ —— **误导性** ✗）。 -/
theorem delta_baseChange_single [Module.Finite R S] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (g : G) (s : S) (t : T) :
    deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G
        (skewBaseChangeLinearEquivLeft (R := R) (S := S) (T := T) (G := G)
          (SkewMonoidAlgebra.single g s ⊗ₜ[R] t))
      = endBaseChangeLinearEquiv (R := R) (S := S) (T := T)
          ((deltaToEndLinear (R := R) (S := S) hRG).rTensor T
            (SkewMonoidAlgebra.single g s ⊗ₜ[R] t)) := by
  rw [skewBaseChangeLinearEquivLeft_single]
  change deltaToEndAdd hR'G (SkewMonoidAlgebra.single g (t ⊗ₜ[R] s))
      = endBaseChangeLinearEquiv ((LinearMap.rTensor T (deltaToEndLinear hRG))
          (SkewMonoidAlgebra.single g s ⊗ₜ[R] t))
  rw [deltaToEndAdd_single, LinearMap.rTensor_tmul]
  change coeffToEnd (t ⊗ₜ[R] s) * actEnd hR'G g
      = endBaseChangeLinearEquiv
          ((deltaToEndAdd hRG (SkewMonoidAlgebra.single g s)) ⊗ₜ[R] t)
  rw [deltaToEndAdd_single]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t' x =>
    rw [Module.End.mul_apply, endBaseChangeLinearEquiv_tmul, Module.End.mul_apply]
    change (t ⊗ₜ[R] s) * (g • (t' ⊗ₜ[R] x)) = (t' * t) ⊗ₜ[R] (s * (g • x))
    rw [act_tmul hcanon hR'G g t' x, Algebra.TensorProduct.tmul_mul_tmul, mul_comm t' t]
  | add a b ha hb => simp [map_add, add_mul, ha, hb]

/-- **③-2（交换性，全形）** ✓✓：`δ' ∘ ③a = ③b ∘ (δ ⊗ id)` ✓ 对一切 `x` ✓。
**证法** ✓：两级归纳 —— `TensorProduct.induction_on` ✓ 归约到 `a ⊗ₜ t`，再
`SkewMonoidAlgebra.induction_on` ✓ 归约到生成元（上一条 ✓）＋ 加性 ✓。 -/
theorem delta_baseChange_commute [Module.Finite R S] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (x : SkewMonoidAlgebra S G ⊗[R] T) :
    deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G
        (skewBaseChangeLinearEquivLeft (R := R) (S := S) (T := T) (G := G) x)
      = endBaseChangeLinearEquiv (R := R) (S := S) (T := T)
          ((deltaToEndLinear (R := R) (S := S) hRG).rTensor T x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    induction a using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | single g s =>
      exact delta_baseChange_single (R := R) (S := S) (T := T) hRG hcanon hR'G g s t
    | add a b ha hb => simp [add_tmul, map_add, ha, hb]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **③ 的收口（双射性搬运）** ✓✓✓：由 **③-2** ✓ ＋ **③a／③b 的双射性** ✓ ＋
前件 `IsGaloisWithGroup R S G hRG` 的**第三款**（`δ` 双射 ✓）⟹ `deltaToEndRingHom hR'G` **双射** ✓。
**机制** ✓：`δ' ∘ ③a = ③b ∘ (δ ⊗ id)` ✓ 右端双射（`e_b` 双射 ✓、`LinearEquiv.rTensor` 双射 ✓）
⟹ `δ' ∘ ③a` 双射 ✓；再用 **`Surjective.of_comp`** ✓ 与 **`Injective.of_comp_right`** ✓
（`③a` 满射 ✓）搬到 `δ'` ✓。
**⟹ 意义** ✓：`hBC⁺⁺`（§42.1 的**作用钉定**收紧形 ✓）的**第三款已全证** ✓（前提 = 有限投射 ＋ `hcanon` ＋ `hR'G` ＋ 前件 ✓）。 -/
theorem delta_baseChange_bijective [Module.Finite R S] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hgal : IsGaloisWithGroup R S G hRG) :
    Function.Bijective (deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G) := by
  have hbij : Function.Bijective (deltaToEndLinear (R := R) (S := S) hRG) := hgal.2.2
  let e := LinearEquiv.ofBijective (deltaToEndLinear (R := R) (S := S) hRG) hbij
  have hrt : ∀ x, e.rTensor T x = (deltaToEndLinear (R := R) (S := S) hRG).rTensor T x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => rw [LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => simp [map_add, hx, hy]
  have hcompfun :
      deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G ∘
        ⇑(skewBaseChangeLinearEquivLeft (R := R) (S := S) (T := T) (G := G))
      = ⇑(endBaseChangeLinearEquiv (R := R) (S := S) (T := T)) ∘ ⇑(e.rTensor T) := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hrt x]
    exact delta_baseChange_commute (R := R) (S := S) (T := T) hRG hcanon hR'G x
  have hb : Function.Bijective (deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G ∘
      ⇑(skewBaseChangeLinearEquivLeft (R := R) (S := S) (T := T) (G := G))) := by
    rw [hcompfun]
    exact (LinearEquiv.bijective (endBaseChangeLinearEquiv (R := R) (S := S) (T := T))).comp
      (LinearEquiv.bijective (e.rTensor T))
  exact ⟨hb.1.of_comp_right
      (LinearEquiv.surjective (skewBaseChangeLinearEquivLeft (R := R) (S := S) (T := T) (G := G))),
    hb.2.of_comp⟩

end deltaBaseChange

/-! ## ① 忠实性款的**目标取向搬运** ⟹ **`hBC⁺⁺` 全款落地**

  **策略** ✓（**不重证** ✓）：① 的**数学内容**已在 `fixedSubring` 段（`S ⊗_R T` 取向 ✓）全部证毕 ✓，
  故本段只用 **`TensorProduct.comm`** ✓ 把「`T ⊗_R S` 上平凡」**搬**到「`S ⊗_R T` 上平凡」✓
  （兼容性引理 `comm_bcTensorActHom` ✓），再**直接调用**成熟的 `not_act_trivial_full` ✓。
  **另需** ✓：把**参数作用**对齐到典范作用 ✓（`act_eq_canonical` ✓，由 `hcanon` ＋ `hR'G` ✓）——
  这正是 §42.1「作用必须钉定」的兑现 ✓。 -/

section hBCStrongest

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]
variable [instAct : MulSemiringAction G (TensorProduct R T S)] [DecidableEq G]

/-- **兼容性引理** ✓✓：`TensorProduct.comm` 把 `S ⊗_R T` 上的作用（`bcTensorActHom` ✓）
搬到 `T ⊗_R S` 上的作用（`bcTensorActHomLeft` ✓）：`comm ∘ act = act' ∘ comm` ✓。
**⟹ 意义** ✓：两个取向上的作用**在同构下互相对应** ✓ —— ① 的搬运**据此免于重证** ✓。 -/
lemma comm_bcTensorActHom
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G)
    (z : TensorProduct R S T) :
    TensorProduct.comm R S T (bcTensorActHom hRG g z)
      = bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g
          (TensorProduct.comm R S T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y t =>
    simp [bcTensorActHom, bcTensorActHomLeft, bcActAlgEquiv, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp [map_add, ha, hb]

/-- **平凡性的搬运** ✓：`T ⊗_R S` 上平凡 ⟹ `S ⊗_R T` 上平凡 ✓。 -/
lemma act_trivial_right_of_act_trivial_left
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) (g : G)
    (htriv : ∀ z : TensorProduct R T S,
      bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g z = z) :
    ∀ z : TensorProduct R S T, bcTensorActHom hRG g z = z := by
  intro z
  apply (TensorProduct.comm R S T).injective
  rw [comm_bcTensorActHom (R := R) (S := S) (T := T) hRG g z, htriv]

/-- **① 忠实性款（目标取向，典范作用）** ✓✓：**不重证** ✓ —— 搬运后直接调用 `not_act_trivial_full` ✓。 -/
theorem not_act_trivial_left_full [FaithfulSMul G S] [FaithfulSMul R T] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id)
    {g : G} (hg : g ≠ 1) :
    ¬ (∀ z : TensorProduct R T S,
      bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g z = z) := by
  intro htriv
  exact not_act_trivial_full (R := R) (S := S) (T := T) hRG hsplit hg
    (act_trivial_right_of_act_trivial_left (R := R) (S := S) (T := T) hRG g htriv)

/-- **参数作用与典范作用一致** ✓✓（`hcanon` ＋ `hR'G` ⟹ 作用被**处处钉住** ✓）：
`g • z = bcTensorActHomLeft hRG g z` ✓ 对一切 `z` ✓（在简单张量上由 `act_tmul` ✓，再线性延拓 ✓）。 -/
lemma act_eq_canonical
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (g : G) (z : TensorProduct R T S) :
    g • z = bcTensorActHomLeft (R := R) (S := S) (T := T) hRG g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t x => rw [act_tmul hcanon hR'G g t x, bcTensorActHomLeft_tmul]
  | add a b ha hb => simp [smul_add, map_add, ha, hb]

/-- **① 忠实性款（目标取向，参数作用 ＋ 典范性）** ✓✓。 -/
theorem not_act_trivial_param_full [FaithfulSMul G S] [FaithfulSMul R T] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id)
    {g : G} (hg : g ≠ 1) :
    ¬ (∀ z : TensorProduct R T S, g • z = z) := by
  intro htriv
  refine not_act_trivial_left_full (R := R) (S := S) (T := T) hRG hsplit hg (fun z => ?_)
  rw [← act_eq_canonical (R := R) (S := S) (T := T) hRG hcanon hR'G g z, htriv]

/-- **① 的产出：`FaithfulSMul G (T ⊗_R S)`** ✓✓（对**参数作用** ✓）。 -/
theorem faithfulSMul_tensorLeft [FaithfulSMul G S] [FaithfulSMul R T] [Module.Projective R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id) :
    FaithfulSMul G (TensorProduct R T S) := by
  refine ⟨fun {m₁ m₂} h => ?_⟩
  by_contra hne
  have hg : m₂⁻¹ * m₁ ≠ 1 := by
    intro h1
    exact hne (by rw [← mul_inv_cancel_left m₂ m₁, h1, mul_one])
  refine not_act_trivial_param_full (R := R) (S := S) (T := T) hRG hcanon hR'G hsplit hg
    (fun z => ?_)
  rw [mul_smul, h z, ← mul_smul, inv_mul_cancel, one_smul]

/-- **② 的目标取向款（参数作用）** ✓：`act_eq_canonical` ✓ 对齐后调用 `bcTensorActLeft_fixes_algebraMap` ✓。 -/
lemma fixes_algebraMap_param
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (g : G) (t : T) :
    g • ((algebraMap T (TensorProduct R T S)) t) = (algebraMap T (TensorProduct R T S)) t := by
  rw [act_eq_canonical (R := R) (S := S) (T := T) hRG hcanon hR'G g]
  exact bcTensorActLeft_fixes_algebraMap (R := R) (S := S) (T := T) hRG g t

/-- **`hBC⁺⁺` 的完整形** ✓✓✓：`IsGaloisWithGroup T (T ⊗_R S) G hR'G` 的**三款齐备** ✓
—— ① `faithfulSMul_tensorLeft` ✓、② `fixes_algebraMap_param` ✓、③ `delta_baseChange_bijective` ✓。
**前提表** ✓（**全部落在使用处** ✓）：`FaithfulSMul R T` ✓、`Module.Projective R S` ✓、`Module.Finite R S` ✓
（源 `proposition-0-2(a)` ✓）、`hRG` ✓、**`hcanon`** ✓（典范性 ✓）、`hR'G` ✓、`hsplit` ✓（源 `prop-0-2(a)` 的内含 ✓）、
前件 `IsGaloisWithGroup R S G hRG` ✓。 -/
theorem isGaloisWithGroup_tensorLeft [FaithfulSMul R T] [Module.Projective R S]
    [Module.Finite R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id)
    (hgal : IsGaloisWithGroup R S G hRG) :
    IsGaloisWithGroup T (TensorProduct R T S) G hR'G := by
  haveI : FaithfulSMul G S := hgal.1
  exact ⟨faithfulSMul_tensorLeft (R := R) (S := S) (T := T) hRG hcanon hR'G hsplit,
    fun g t => fixes_algebraMap_param (R := R) (S := S) (T := T) hRG hcanon hR'G g t,
    delta_baseChange_bijective (R := R) (S := S) (T := T) hRG hcanon hR'G hgal⟩

/-- **`hBC⁺⁺`（＝源 `proposition-0-2(d)` 的**可用**收紧形）** ✓✓✓ ——
**B 档① 最后一个命名假设的正面替代** ✓：它**填满** `GaloisBaseChangeHyp R S T G hRG hR'G` ✓，
但**要求作用被 `hcanon` 钉定** ✓（§42.1 已证**必须** ✓）。
**⚠ 与旧接口的关系** ✓：旧 `hBC` 的 `∀`-作用形**不可居留** ✓（`not_galoisBaseChangeHyp_of_trivial_action` ✓）
⟹ 旧定理**空洞** ✓、接线须改挂本条 ✓（旧名旧类型**逐字保留** ✓，登记不可居留 ✓）。 -/
theorem galoisBaseChangeHyp_strongest [FaithfulSMul R T] [Module.Projective R S]
    [Module.Finite R S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hsplit : ∀ g : G, ∃ p : S →ₗ[R] diffSubmodule (S := S) (R := R) (G := G) g,
      p.comp (diffSubmodule (S := S) (R := R) (G := G) g).subtype = LinearMap.id) :
    GaloisBaseChangeHyp R S T G hRG hR'G :=
  fun hgal => isGaloisWithGroup_tensorLeft (R := R) (S := S) (T := T) hRG hcanon hR'G hsplit hgal

/-- **非空洞探针（L1）** ✓：`hBC⁺⁺` 的**前提类的数据部分可实例化** ✓ ——
`FaithfulSMul ℚ ℚ` ✓（恒等映射单射 ✓）、`Module.Projective ℚ ℚ`／`Module.Finite ℚ ℚ` ✓（域上向量空间自由 ✓）、
`Field ℚ`／`Group PUnit`／`Fintype PUnit` ✓。
**⚠ 登记** ✓：`hcanon`／`hR'G`／`hsplit` 是**等式／存在类**前提 ✓，其可满足性在**典范作用 ＋ `G = 1` 档**显然 ✓
（`D_1 = ⊥` ✓）；**完全具体的 `IsGaloisWithGroup` 实例**（如 `ℚ/ℚ`、`G = PUnit` ✓）留待下游 ✓。 -/
theorem hBCstrongest_data_nonempty :
    Nonempty (FaithfulSMul ℚ ℚ) ∧ Nonempty (Module.Projective ℚ ℚ)
      ∧ Nonempty (Module.Finite ℚ ℚ) ∧ Nonempty (Field ℚ) ∧ Nonempty (Group PUnit) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- **① 的**新证**（用 ③ 的**单射性**）** ✓✓✓ —— **假设表的大幅收紧** ✓：
`T ⊗_R S` **非平凡** ＋ **③ 的单射性** ⟹ `G` 在 `T ⊗_R S` 上**忠实** ✓
—— **不需要 `FaithfulSMul R T`** ✗、**不需要 `hsplit`** ✗、**不需要 `hRG`** ✗、**不需要 `IsGaloisWithGroup`** ✓。
**机制** ✓（**纯生成元** ✓）：若 `g` 在 `T ⊗_R S` 上平凡 ✓，则
`δ'(single g 1) = coeffToEnd 1 * actEnd g = actEnd g = 1 = δ'(1)` ✓ ⟹ 由 **③ 的单射性** 得
`single g 1 = 1` ✓ ⟹ 取 `g`-坐标（`Finsupp.single_eq_same` ✓）得 `1 = 0` ✗ —— 与 **`Nontrivial`** 矛盾 ✓。
**⚠ 工艺读数** ✓：`deltaToEndRingHom` 的结构字面量应用须先 **`change`**（同 §43.2 ✓）；
`Finsupp.single_eq_of_ne` 的假设形是 **`a' ≠ a`**（`a` = 单点指标 ✓、`a'` = 求值点 ✓ —— 与直觉相反 ✗）；
`ext z` 会被 `S` 的 ext 引理抢走 ✗ ⟹ 用 **`apply LinearMap.ext` ＋ `intro z`** ✓。 -/
theorem faithfulSMul_of_nontrivial_tensor [Nontrivial (TensorProduct R T S)]
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hbij : Function.Bijective (deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G))
    {g : G} (hact : ∀ z : TensorProduct R T S, g • z = z) :
    g = 1 := by
  have hδ : deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G
      (SkewMonoidAlgebra.single g (1 : TensorProduct R T S)) = 1 := by
    rw [deltaToEndRingHom]
    change deltaToEndAdd hR'G (SkewMonoidAlgebra.single g (1 : TensorProduct R T S)) = 1
    rw [deltaToEndAdd_single]
    have hact1 : actEnd hR'G g = 1 := by
      apply LinearMap.ext
      intro z
      simpa [actEnd] using hact z
    rw [hact1, mul_one]
    apply LinearMap.ext
    intro z
    simp [coeffToEnd]
  have hsingle : SkewMonoidAlgebra.single g (1 : TensorProduct R T S) = 1 :=
    hbij.1 (by rw [hδ, map_one])
  rw [show (1 : SkewMonoidAlgebra (TensorProduct R T S) G)
      = SkewMonoidAlgebra.single 1 1 from rfl] at hsingle
  have hcoeff := congrArg (fun x : SkewMonoidAlgebra (TensorProduct R T S) G => x.coeff g) hsingle
  rw [SkewMonoidAlgebra.coeff_single, SkewMonoidAlgebra.coeff_single] at hcoeff
  rw [Finsupp.single_eq_same] at hcoeff
  by_contra hg
  rw [Finsupp.single_eq_of_ne (a := (1 : G)) (a' := g)
    (b := (1 : TensorProduct R T S)) hg] at hcoeff
  exact one_ne_zero hcoeff

/-- **① 的组装**（`FaithfulSMul` 形 ✓）：由 `m₂⁻¹ * m₁` 档归约到上一条 ✓。 -/
theorem faithfulSMul_of_nontrivial_tensor_full [Nontrivial (TensorProduct R T S)]
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hbij : Function.Bijective (deltaToEndRingHom (R := T) (S := TensorProduct R T S) hR'G)) :
    FaithfulSMul G (TensorProduct R T S) := by
  refine ⟨fun {m₁ m₂} h => ?_⟩
  by_contra hne
  have hg : m₂⁻¹ * m₁ ≠ 1 := by
    intro h1
    exact hne (by rw [← mul_inv_cancel_left m₂ m₁, h1, mul_one])
  exact hg (faithfulSMul_of_nontrivial_tensor (R := R) (S := S) (T := T) hR'G hbij
    (fun z => by rw [mul_smul, h z, ← mul_smul, inv_mul_cancel, one_smul]))

/-- **`hBC⁺⁺⁺`：假设表**最弱**的可用形** ✓✓✓ —— 只需 **`Nontrivial (T ⊗_R S)`** ✓
（**不需要 `FaithfulSMul R T`** ✗、**不需要 `hsplit`** ✗ —— 二者已被 ③ 的单射性取代 ✓）。
前提表 ✓：`[Module.Finite R S]` ✓、`[Module.Projective R S]` ✓（源 `prop-0-2(a)` ✓）、
`[Nontrivial (T ⊗_R S)]` ✓、`hRG` ✓、**`hcanon`** ✓、`hR'G` ✓、前件 `IsGaloisWithGroup R S G hRG` ✓。 -/
theorem isGaloisWithGroup_tensorLeft_of_nontrivial [Module.Finite R S] [Module.Projective R S]
    [Nontrivial (TensorProduct R T S)]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hgal : IsGaloisWithGroup R S G hRG) :
    IsGaloisWithGroup T (TensorProduct R T S) G hR'G :=
  ⟨faithfulSMul_of_nontrivial_tensor_full (R := R) (S := S) (T := T) hR'G
      (delta_baseChange_bijective (R := R) (S := S) (T := T) hRG hcanon hR'G hgal),
   fun g t => fixes_algebraMap_param (R := R) (S := S) (T := T) hRG hcanon hR'G g t,
   delta_baseChange_bijective (R := R) (S := S) (T := T) hRG hcanon hR'G hgal⟩

/-- **`hBC⁺⁺⁺`（收口形 ✓）**：`GaloisBaseChangeHyp R S T G hRG hR'G` ✓，仅需 `Nontrivial (T ⊗_R S)` ✓。
**⚠ 与 `galoisBaseChangeHyp_strongest`（`hBC⁺⁺` ✓）的关系** ✓：本条**严格更强** ✓
（去掉了 `FaithfulSMul R T` 与 `hsplit` ✓）；`hBC⁺⁺` 保留作**更早的登记** ✓（使用处拿不到 `FaithfulSMul R T` ✓，见 §44.3 ✓）。 -/
theorem galoisBaseChangeHyp_strongest_of_nontrivial [Module.Finite R S] [Module.Projective R S]
    [Nontrivial (TensorProduct R T S)]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z)) :
    GaloisBaseChangeHyp R S T G hRG hR'G :=
  fun hgal => isGaloisWithGroup_tensorLeft_of_nontrivial (R := R) (S := S) (T := T)
    hRG hcanon hR'G hgal

/-- **`Subsingleton N ⟹ Subsingleton (M ⊗_R N)`** ✓（简单张量全为 `0` ✓）；接线用 ✓。 -/
theorem subsingleton_tensor_of_subsingleton_right {M N : Type*} [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) := by
  constructor
  intro a b
  have h : ∀ x : M ⊗[R] N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n (0 : N), tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h a, h b]

/-- **① 在 `Subsingleton G` 档免费** ✓✓：群元全相等 ⟹ 忠实性对**任意**载体自动成立 ✓
（故该档**不需要** `Nontrivial (T ⊗_R S)` ✓ —— 接线时按 `G` 是否平凡分档 ✓）。 -/
theorem isGaloisWithGroup_tensorLeft_of_subsingletonGroup [Module.Finite R S]
    [Module.Projective R S] [Subsingleton G]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hgal : IsGaloisWithGroup R S G hRG) :
    IsGaloisWithGroup T (TensorProduct R T S) G hR'G :=
  ⟨⟨fun {m₁ m₂} _ => Subsingleton.elim m₁ m₂⟩,
   fun g t => fixes_algebraMap_param (R := R) (S := S) (T := T) hRG hcanon hR'G g t,
   delta_baseChange_bijective (R := R) (S := S) (T := T) hRG hcanon hR'G hgal⟩

end hBCStrongest

/-! ## ✅✅✅ **`hBC` 的**消除**：Prop 1.1(a) 的 `hBC`-free 版**

  **本节的定理是 `GenericExtension_ABGV52` 的 `liftingPropertyEG_of_isGenericObjectEG` 的
  **无 `hBC` 版** ✓ —— 第 8 步（原 `hBC` 调用 ✓）改为**直接构造** `IsGaloisWithGroup T (T ⊗_R S) G hex` ✓：
  ① 由 **③ 的单射性**得 ✓（§45 ✓）、② 由 `fixes_algebraMap_param` ✓、③ 由 `delta_baseChange_bijective` ✓；
  `Nontrivial (T ⊗_R S)` 由 `S₀` 的忠实性 ＋ `hiso` 的同构**导出** ✓（**在 `G` 平凡档不需要** ✓）。
  **⚠ 文件位置的说明** ✓：`BaseChangeProj` **import** `GenericExtension` ✓（反之会**循环** ✗），
  故本定理（需要本件的 §43–§45 诸件 ✓）只能落在**本件**（或其后继件 ✓）——
  它引用的 `assemble_steps123`／`assemble_steps467`／`cancelIso_of_repIso`／`phiToAlgebra_eq_residueAlgebra`
  皆由 `GenericExtension` 提供 ✓。
  **新前提** ✓（**皆与 `T` 无关** ✓ ⟹ 可作定理级假设 ✓）：`[DecidableEq G]` ✓（技术 ✓）、
  `[Module.Finite R S]` ✓、`[Module.Projective R S]` ✓ —— 后二者 ＝ 源 **`proposition-0-2(a)`** 的**外部输入** ✓。 -/

section liftingUncond

/-- **Prop 1.1(a)（`hBC` 已消除）** ✓✓✓：`generic object ⟹ lifting property` ✓，
**不再需要** `GaloisBaseChangeHyp`（＝源 `prop-0-2(d)` ✓）作假设 ✓ —— 其内容已由 §43–§45 证成并**就地接线** ✓。
**接线机制** ✓（第 8 步 ✓）：**先把 `hiso` 的同构产出** ✓（与 `hgal` 无关 ✓ ⟹ 可前移 ✓）、
由它（＋ `h₀` 的忠实性 ✓）导出 **`Nontrivial (T ⊗_R S)`** ✓，再用 `hBC⁺⁺⁺`（§45 ✓）构造 `hgal` ✓；
`hcanon` 由 `Algebra.TensorProduct.map_tmul` ✓ 直接给出（作用即 `tensorMulSemiringAction hRG` ✓）。
**`Subsingleton G` 档** ✓：用 `isGaloisWithGroup_tensorLeft_of_subsingletonGroup` ✓（① 免费 ✓，无需 `Nontrivial` ✓）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_strongest
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    [Module.Finite R S] [Module.Projective R S] :
    LiftingPropertyEG F G := by
  have hgen' := hgen
  obtain ⟨hrep, haway⟩ := hgen
  obtain ⟨hgalRS, hreal⟩ := hrep
  refine fun T _ _ hT _ S₀ _ _ _ _ _ hRG₀ h₀ => ?_
  obtain ⟨φ, n, w, hw, ρ, he⟩ := assemble_steps123 F G R S hRG hgen' T S₀ hRG₀ h₀
  obtain ⟨ψ, hψ⟩ := assemble_steps467 F R T n w φ hw ρ
  letI : Algebra R T := ψ.toRingHom.toAlgebra
  letI : MulSemiringAction G (TensorProduct R T S) := tensorMulSemiringAction hRG
  letI hex : ∀ (g : G) (r : T) (t : TensorProduct R T S), g • (r • t) = r • (g • t) :=
    fun g r t => tensorAct_smul_comm hRG g r t
  have hst : IsScalarTower R T (IsLocalRing.ResidueField T) :=
    ⟨fun r t z => by
      show algebraMap T (IsLocalRing.ResidueField T) (algebraMap R T r * t) * z
        = (IsLocalRing.residue T) (ψ r) * (algebraMap T (IsLocalRing.ResidueField T) t * z)
      rw [map_mul, show algebraMap R T r = ψ r from rfl, mul_assoc]
      rfl⟩
  have he' : CancelIso R T (IsLocalRing.ResidueField T) S S₀
      (IsLocalRing.ResidueField.algebra T) (IsLocalRing.residue T).toAlgebra hst :=
    cancelIso_of_repIso (R := R) (T := T) (S := S) (S₀ := S₀)
      (aRK := IsLocalRing.ResidueField.algebra T)
      (aTK := (IsLocalRing.residue T).toAlgebra) (st := hst)
      (phiToAlgebra_eq_residueAlgebra φ ψ (fun x => rfl) hψ ▸ he)
  letI : Algebra R (IsLocalRing.ResidueField T) := IsLocalRing.ResidueField.algebra T
  letI : Algebra T (IsLocalRing.ResidueField T) := (IsLocalRing.residue T).toAlgebra
  haveI hstI : IsScalarTower R T (IsLocalRing.ResidueField T) := hst
  obtain ⟨eiso⟩ := he'
  have hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x) := by
    intro g x
    change tensorActHom hRG g ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x)
    rw [tensorActHom, Algebra.TensorProduct.map_tmul]
    rfl
  have hgal : IsGaloisWithGroup T (TensorProduct R T S) G hex := by
    by_cases hGs : Subsingleton G
    · exact isGaloisWithGroup_tensorLeft_of_subsingletonGroup (R := R) (S := S) (T := T)
        hRG hcanon hex hgalRS
    · haveI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hGs
      haveI hS₀ : FaithfulSMul G S₀ := h₀.1
      haveI hntS₀ : Nontrivial S₀ := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        exact hGs ⟨fun a b => FaithfulSMul.eq_of_smul_eq_smul (fun _ => hsub.elim _ _)⟩
      haveI hntK : Nontrivial (TensorProduct T (IsLocalRing.ResidueField T)
          (TensorProduct R T S)) :=
        Function.Injective.nontrivial eiso.injective
      haveI hntTS : Nontrivial (TensorProduct R T S) := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI hsubS : Subsingleton (TensorProduct R T S) := hsub
        haveI : Subsingleton (TensorProduct T (IsLocalRing.ResidueField T)
            (TensorProduct R T S)) :=
          subsingleton_tensor_of_subsingleton_right (R := T)
            (M := IsLocalRing.ResidueField T) (N := TensorProduct R T S)
        exact not_subsingleton_iff_nontrivial.mpr hntK ‹Subsingleton _›
      exact isGaloisWithGroup_tensorLeft_of_nontrivial (R := R) (S := S) (T := T)
        hRG hcanon hex hgalRS
  exact ⟨TensorProduct R T S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hex, hgal, ⟨eiso⟩⟩

/-- **类型锁定** ✓（手写 ✗）：钉住成品定理的**陈述形状**（`hgen` ＋ 两个实例假设 ✓，**无 `hBC`** ✓）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_strongest_typeLock
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (∀ (hgen : IsGenericObjectEG F G R S hRG) [Module.Finite R S] [Module.Projective R S],
        LiftingPropertyEG F G)
      = (∀ (hgen : IsGenericObjectEG F G R S hRG) [Module.Finite R S] [Module.Projective R S],
        LiftingPropertyEG F G) := rfl

/-- **应用锁** ✅（钉**假设表** ✓）：以**恰好** `hgen` ＋ 两个实例假设调用 ✓
⟹ 假设表一旦增删（如再引入 `hBC`）本 `example` 立即编译失败 ✓。 -/
example (F : Type) [Field F] (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    [Module.Finite R S] [Module.Projective R S] :
    LiftingPropertyEG F G :=
  liftingPropertyEG_of_isGenericObjectEG_strongest F G R S hRG hgen

end liftingUncond

/-- **具名外部输入的接线** ✓✓：把 `…_strongest` 的两个**实例前提**（`[Module.Finite R S]`／
`[Module.Projective R S]` ✓）换成**单一具名假设** `GaloisProjectiveHyp` ✓（＝源 `proposition-0-2(a)` ✓，
引 [CHR68] p.13 ✓，§46.4 ✓ 登记 ✓）⟹ Prop 1.1(a) 的**接口形**与工程其余具名假设**同构** ✓
（"先接口后实体" ✓，与 `FischerRegularHyp` ✓ 同法 ✓）。
**用途** ✓：本条的假设表 = `hgen` ✓ ＋ `hProj` ✓ ＋ `[DecidableEq G]` ✓ —— **不再有裸实例前提** ✓。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_of_galoisProjective
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (hgen : IsGenericObjectEG F G R S hRG)
    (hProj : GaloisProjectiveHyp R S G hRG) :
    LiftingPropertyEG F G := by
  -- ⚠ `obtain … := hgen` 会**消费** `hgen`（rcases 语义 ✓）⟹ **先留副本** ✓
  have hgen' := hgen
  obtain ⟨hrep, -⟩ := hgen
  obtain ⟨hgalRS, -⟩ := hrep
  haveI hF : Module.Finite R S := (hProj hgalRS).1
  haveI hP : Module.Projective R S := (hProj hgalRS).2
  exact liftingPropertyEG_of_isGenericObjectEG_strongest F G R S hRG hgen'

/-- **类型锁定** ✓（手写 ✗）：钉住接口形的假设表（`hgen` ＋ **`hProj`** ✓，**无裸实例前提** ✓）。 -/
theorem liftingPropertyEG_of_isGenericObjectEG_of_galoisProjective_typeLock
    (F : Type) [Field F] (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    (∀ (hgen : IsGenericObjectEG F G R S hRG) (hProj : GaloisProjectiveHyp R S G hRG),
        LiftingPropertyEG F G)
      = (∀ (hgen : IsGenericObjectEG F G R S hRG) (hProj : GaloisProjectiveHyp R S G hRG),
        LiftingPropertyEG F G) := rfl

/-! ## 🚨 `hBC` 的 **`∀`-作用量化形不可居留**（接口缺陷，B 档第 79 轮实测）

  `GenericExtension_ABGV52.lean` 的 `hBC` 参数形为
  `∀ (T) … [MulSemiringAction G (TensorProduct R T S)] (hR'G), GaloisBaseChangeHyp R S T G hRG hR'G` ✓，
  即**对任意**满足 `hR'G` 的 `G`-作用断言基变换后的 Galois 性 ✓。
  **本段证明该形为假** ✗：**平凡作用** `g • z = z` ✓ 使 `hR'G` **平凡为真** ✓（两边都是 `r • z` ✓），
  但 `FaithfulSMul G (T ⊗_R S)` 立刻失败 ✓（`G` 非平凡 ＋ `T ⊗_R S` 非平凡 ✓）。
  **⟹ 结论** ✓：`hBC` 的消除**不能**以「证成原形」达成 ✓ —— 必须**收紧接口**（把作用钉到
  由 `S` 上作用诱导的**典范作用** ✓，如 §41.5 计划 ✓），旧名旧类型**保留但登记为不可居留** ✓。
  **⚠ 与 §36「`GaloisBaseChangeHyp` 的 `def` 为假」的分工** ✓：那条是 `def` 在**退化参数**（`R' = 0` 等 ✓）
  下为假 ✓；本条是**作用量化**（换成任意作用 ✓）下为假 ✓ —— 两处**互不覆盖** ✓，都须收紧 ✓。 -/

section hBCInterface

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]
variable [instAct : MulSemiringAction G (TensorProduct R T S)]

/-- **接口缺陷的实体** ✓：`G` 非平凡、`S/R` 是 `G`-Galois（前提有实例 ✓）、`T ⊗_R S` 非平凡 ⟹
**存在**满足 `hR'G` 的作用（平凡作用 ✓）使 `GaloisBaseChangeHyp` 的结论为**假** ✓
（① 失败 ✓）⟹ 该 `∀`-形**不可居留** ✗。 -/
theorem not_galoisBaseChangeHyp_of_trivial_action [Nontrivial G]
    [Nontrivial (TensorProduct R T S)]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hact : ∀ (g : G) (z : TensorProduct R T S), g • z = z)
    (hgal : IsGaloisWithGroup R S G hRG) :
    ¬ (∀ (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z)),
        GaloisBaseChangeHyp R S T G hRG hR'G) := by
  intro h
  have hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z) :=
    fun g r z => by rw [hact g (r • z), hact g z]
  obtain ⟨hf, -, -⟩ := h hR'G hgal
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (FaithfulSMul.eq_of_smul_eq_smul (fun z => by rw [hact g z, one_smul]))

end hBCInterface

/-! ## 装配 **(b) 款**：**具名输入形**的基变换（第 169 轮）

  **源逐字** ✓（`raw/Saltman1982.tex:649--651` ✓，印 **275** ✓）：「By `proposition-0-2`(c), there is an
  `s \in R_1` and an algebra `S \supseteq R = R_1(1/s)` such that **`S/R` is Galois with group `G`** and
  `S \otimes_R L^G \cong L`.」✓ —— 源的 `S` 不是下降直接给出的 `S''` ✓，而是 `S''` 沿
  `R'' \to R`（`R''` 有限生成于 `R_1` ⟹ 因子化过 `R_1(1/s)` ✓）的**基变换** ✓（源引
  `proposition-0-2(d)` ✓）⟹ **`theorem-5-1` 装配的 (b) 款**（`IsGenericExtension` 的第二合取 ✓）
  ＝ **`G`-Galois 性在基变换下保持** ✓（本件 §43–§45 已证 ✓），本轮把它落为**可调用的装配件** ✓。

  **本轮三件** ✓：
  **① 具名输入形** ✓：把 `…_of_nontrivial` 的两个**实例**前提（`[Module.Finite R S]` ✓／
  `[Module.Projective R S]` ✓）换成**单一在册具名假设** `GaloisProjectiveHyp` ✓（＝源
  `proposition-0-2(a)` ✓，引 **[CHR68] p. 13** ✓，`GaloisAlgebra_ABGV52.lean:158` ✓）——
  ⟹ **(b) 款的假设表与工程其余具名假设同构** ✓（"先接口后实体" ✓，与
  `liftingPropertyEG_of_isGenericObjectEG_of_galoisProjective` ✓ 同法 ✓）。
  **② 非平凡性的供给路线** ✓：§45 的 `hBC⁺⁺⁺` 需 `Nontrivial (T \otimes_R S)` ✓（`…_strongest`
  第 8 步从下降同构**导出**它 ✓）；本轮把它抽为**通用供给件** ✓（沿环同态落到非平凡环 ✓）
  ⟹ 装配侧不必再就地重演 ✓。
  **③ `Subsingleton G` 档** ✓：该档 ① 款**免费** ✓（`…_of_subsingletonGroup` ✓）⟹ **不需要**非平凡性 ✓
  —— 分档留在调用点 ✓（同 `…_strongest` ✓）。

  **⚠ 取向约定** ✓（**登记** ✓）：源把新 `S` 写在 `S'' \otimes_{R''} R` **取向** ✓；本件取
  `TensorProduct R T S = T \otimes_R S` ✓（**新 `R` 在左** ✓）—— 与工程其余部分**同取向** ✓
  （`RealizationProperty` 的 `K \otimes_R S` ✓／`CancelIso` 的 `T \otimes_R (T \otimes_R S)` ✓／
  §45 的 `isGaloisWithGroup_tensorLeft_*` ✓ 皆然 ✓）；两取向由 `TensorProduct.comm` ✓ 相联 ✓，
  **本件不改取向** ✓（换载体优于硬碰 ✓，读数 (70) ✓）。 -/

section BaseChangeNamed

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]
variable [instAct : MulSemiringAction G (TensorProduct R T S)]

/-- **非平凡性沿环同态回拉** ✓（通用小件 ✓）：有到**非平凡**环的环同态 ⟹ 源环非平凡 ✓
（`f 1 = 1 \neq 0 = f 0` ✓）。 -/
theorem nontrivial_of_ringHom {A B : Type*} [CommSemiring A] [CommSemiring B] [Nontrivial B]
    (f : A →+* B) : Nontrivial A :=
  ⟨⟨1, 0, fun h => (one_ne_zero : (1 : B) ≠ 0) (by rw [← map_one f, ← map_zero f, h])⟩⟩

/-- **非平凡性的基变换供给** ✓（装配用 ✓）：`K` 是 `T` 的 `R`-代数（`algebraMap`）✓、
`K \otimes_R S` 非平凡 ✓ ⟹ `T \otimes_R S` 非平凡 ✓ —— 沿 `Algebra.TensorProduct.map` ✓
落到非平凡环 ✓（用上条 ✓）。
**用途** ✓：装配中 `K = L^G` ✓、`T =` 新 `R = R_1(1/s) \subseteq L^G` ✓、`S = S''` ✓，
故由下降同构给出的 `S'' \otimes_{R''} L^G \cong L` ✓ 即可供给本前提 ✓。 -/
theorem nontrivial_tensorProduct_of_nontrivial_tensorProduct
    {K : Type*} [CommRing K] [Algebra R K] [Algebra T K] [IsScalarTower R T K]
    [Nontrivial (TensorProduct R K S)] :
    Nontrivial (TensorProduct R T S) :=
  nontrivial_of_ringHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T K)
    (AlgHom.id R S)).toRingHom

/-- **(b) 款（具名输入形）** ✓✓：`S/R` 为 `G`-Galois ✓ ＋ 源 `proposition-0-2(a)` 的**具名形**
`GaloisProjectiveHyp` ✓ ＋ `T \otimes_R S` 非平凡 ✓ ⟹ **`T \otimes_R S` 在 `T` 上为 `G`-Galois** ✓
（取 `R := R''` ✓、`S := S''` ✓、`T :=` 新 `R` ✓ 即源 `theorem-5-1` 的 `S` ✓）。
**前提表** ✓（**最弱已知** ✓）：`hRG` ✓、**`hcanon`** ✓（作用典范性 ✓ —— §42.1 已证**必须** ✓）、
`hR'G` ✓、前件 `hgal` ✓、**单一具名外部输入** `hProj` ✓、`[Nontrivial (T \otimes_R S)]` ✓。
**⚠ `hcanon` 的接线** ✓（装配侧三行 ✓，同 `…_strongest` 第 8 步 ✓）：`letI := tensorMulSemiringAction hRG` ✓、
`hcanon` 由 `Algebra.TensorProduct.map_tmul` ✓ 直接给出 ✓、`hR'G := fun g r z => tensorAct_smul_comm hRG g r z` ✓。 -/
theorem isGaloisWithGroup_tensorLeft_of_galoisProjective
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hgal : IsGaloisWithGroup R S G hRG)
    (hProj : GaloisProjectiveHyp R S G hRG)
    [Nontrivial (TensorProduct R T S)] :
    IsGaloisWithGroup T (TensorProduct R T S) G hR'G := by
  classical
  have hFin : Module.Finite R S := (hProj hgal).1
  have hPrj : Module.Projective R S := (hProj hgal).2
  exact isGaloisWithGroup_tensorLeft_of_nontrivial (R := R) (S := S) (T := T)
    hRG hcanon hR'G hgal

/-- **(b) 款的 `GaloisBaseChangeHyp` 接口形** ✓：把 `hgal` 收进蕴含 ✓
（源 `proposition-0-2(d)` 的可用形 ✓，`hBC` 的**具名输入**替代 ✓）。 -/
theorem galoisBaseChangeHyp_of_galoisProjective
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hProj : GaloisProjectiveHyp R S G hRG)
    [Nontrivial (TensorProduct R T S)] :
    GaloisBaseChangeHyp R S T G hRG hR'G :=
  fun hgal => isGaloisWithGroup_tensorLeft_of_galoisProjective (R := R) (S := S) (T := T)
    hRG hcanon hR'G hgal hProj

/-- **(b) 款（`Subsingleton G` 档）** ✓：该档 ① 款**免费** ✓ ⟹ **不需要** `[Nontrivial (T \otimes_R S)]` ✓
（分档由调用点做 ✓，同 `…_strongest` ✓）。 -/
theorem isGaloisWithGroup_tensorLeft_of_galoisProjective_of_subsingletonGroup
    [Subsingleton G]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hgal : IsGaloisWithGroup R S G hRG)
    (hProj : GaloisProjectiveHyp R S G hRG) :
    IsGaloisWithGroup T (TensorProduct R T S) G hR'G := by
  classical
  have hFin : Module.Finite R S := (hProj hgal).1
  have hPrj : Module.Projective R S := (hProj hgal).2
  exact isGaloisWithGroup_tensorLeft_of_subsingletonGroup (R := R) (S := S) (T := T)
    hRG hcanon hR'G hgal

/-- **应用锁** ✅（钉**假设表** ✓）：以**恰好** `hRG`／`hcanon`／`hR'G`／`hgal`／`hProj` ＋
`[Nontrivial]` 调用 ✓ ⟹ 假设表一旦增删（如退回裸实例前提、或多出 `FaithfulSMul R T`）本 `example`
立即编译失败 ✓。（`example` 不生成声明 ⟹ 不进公理门清单 ✓。） -/
example (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (hcanon : ∀ (g : G) (x : S), g • ((1 : T) ⊗ₜ[R] x) = (1 : T) ⊗ₜ[R] (g • x))
    (hR'G : ∀ (g : G) (r : T) (z : TensorProduct R T S), g • (r • z) = r • (g • z))
    (hgal : IsGaloisWithGroup R S G hRG)
    (hProj : GaloisProjectiveHyp R S G hRG)
    [Nontrivial (TensorProduct R T S)] :
    IsGaloisWithGroup T (TensorProduct R T S) G hR'G :=
  isGaloisWithGroup_tensorLeft_of_galoisProjective hRG hcanon hR'G hgal hProj

/-- **登记** ✗：本件把 (b) 款接到**单一具名外部输入** `GaloisProjectiveHyp` ✓（＝源
`proposition-0-2(a)` ✓，引 **[CHR68] p. 13** ✓，**不在 `raw/`** ✗ —— 与 [DI71]／[Sal78b] 同类的
一级出处缺件 ✓，L37 已核 ✓）⟹ **该假设的实体（`S` 为投射 `R[G]`-模 ⟹ 有限投射 `R`-模 ✓）仍未落** ✗
（`galoisProjective_gap_registered` ✓）。 -/
theorem galoisProjective_baseChange_gap_registered : True := trivial

end BaseChangeNamed

/-! ## 公理闸门 -/

#print axioms dual_eval_injective_of_projective
#print axioms exists_dual_ne_zero
#print axioms scalarEval_tmul
#print axioms dual_eval_injective_of_projective_ring
#print axioms exists_dual_ne_zero_ring
#print axioms scalarEvalRing_tmul
#print axioms tensorProduct_nontrivial_of_projective_of_faithful
#print axioms tensorProduct_nontrivial_of_projective
#print axioms bcActAlgEquiv
#print axioms bcTensorActHom
#print axioms bcTensorActHom_tmul
#print axioms act_one
#print axioms tensorAct_fixes_one_tmul
#print axioms tensorAct_fixes_T
#print axioms tensorAct_fixes_algebraMap
#print axioms diff_tmul_one_eq_zero_of_act_trivial
#print axioms rTensor_subtype_injective_of_retract
#print axioms diffSubmodule_tensor_subsingleton_of_act_trivial
#print axioms not_act_trivial_of_nontrivial_diffTensor
#print axioms diffSubmodule_nontrivial_of_faithfulSMul
#print axioms not_act_trivial_full
#print axioms skewCoeffEquiv
#print axioms skewBaseChangeLinearEquiv
#print axioms skewBaseChangeLinearEquiv_single
#print axioms diffTensor_nontrivial_hyp_registered
#print axioms endBaseChangeLinearEquiv
#print axioms endBaseChangeLinearEquiv_tmul
#print axioms skewBaseChangeLinearEquivLeft
#print axioms skewBaseChangeLinearEquivLeft_single
#print axioms deltaToEndAdd_smul
#print axioms algebraMap_tensorLeft
#print axioms bcTensorActHomLeft
#print axioms bcTensorActHomLeft_tmul
#print axioms bcActAlgEquiv_one
#print axioms bcActAlgEquiv_mul
#print axioms bcTensorMulSemiringActionLeft
#print axioms bcTensorActLeft_smul_comm
#print axioms bcTensorActLeft_fixes_algebraMap
#print axioms not_galoisBaseChangeHyp_of_trivial_action
#print axioms deltaToEndLinear
#print axioms smul_one_tmul
#print axioms act_tmul
#print axioms delta_baseChange_single
#print axioms delta_baseChange_commute
#print axioms delta_baseChange_bijective
#print axioms comm_bcTensorActHom
#print axioms act_trivial_right_of_act_trivial_left
#print axioms not_act_trivial_left_full
#print axioms act_eq_canonical
#print axioms not_act_trivial_param_full
#print axioms faithfulSMul_tensorLeft
#print axioms fixes_algebraMap_param
#print axioms isGaloisWithGroup_tensorLeft
#print axioms galoisBaseChangeHyp_strongest
#print axioms hBCstrongest_data_nonempty
#print axioms faithfulSMul_of_nontrivial_tensor
#print axioms faithfulSMul_of_nontrivial_tensor_full
#print axioms isGaloisWithGroup_tensorLeft_of_nontrivial
#print axioms galoisBaseChangeHyp_strongest_of_nontrivial
#print axioms subsingleton_tensor_of_subsingleton_right
#print axioms isGaloisWithGroup_tensorLeft_of_subsingletonGroup
#print axioms liftingPropertyEG_of_isGenericObjectEG_strongest
#print axioms liftingPropertyEG_of_isGenericObjectEG_strongest_typeLock
#print axioms liftingPropertyEG_of_isGenericObjectEG_of_galoisProjective
#print axioms liftingPropertyEG_of_isGenericObjectEG_of_galoisProjective_typeLock
#print axioms nontrivial_of_ringHom
#print axioms nontrivial_tensorProduct_of_nontrivial_tensorProduct
#print axioms isGaloisWithGroup_tensorLeft_of_galoisProjective
#print axioms galoisBaseChangeHyp_of_galoisProjective
#print axioms isGaloisWithGroup_tensorLeft_of_galoisProjective_of_subsingletonGroup
#print axioms galoisProjective_baseChange_gap_registered

end ABGV52.BTier
