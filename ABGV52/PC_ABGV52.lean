/-
  ABGV-5.2 —— (2) 两条目 · **条目 2：`lem:perm-class`**

  论文 `raw/ABGV-5.2-resolution.tex` `:831–891`（⚠-tex-sourced，L12/L16）：
    设 `P` 为置换 `ℤ[H]`-格且 `P ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ`，则 `P ≅ 8·ℤ[H] ⊕ ℤ`，
    其中 `H = C_3 × C_3`（`ABGV52.H`）。

  载体约定（与论文的翻译，须随读数一并引用）
  ==========================================
  * 本库 `IsPermutationLattice`（`Hyp_ABGV52`）定义在 **H-集 `X`** 上：`P = ℤ[X]`
    （有限 H-集是其轨道无交并，轨道 ≅ `H/K`，故与「同构于 `⊕_K m_K ℤ[H/K]`」等价）；
    本件 consequently 以 `X` 表述主定理。
  * 论文假设 `P ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ` 在 ℚ-侧 = `ℚ[X] ≅ ℚ[(Fin 8 × H) ⊔ PUnit]`：
    右端是 `8·ℚ[H] ⊕ ℚ` 的**置换模模型**（`(Fin 8 × H) ⊔ PUnit` 的置换模，
    其底层集 = 8 个正则块 ⊔ 单点，模块层 = `8·ℚ[H] ⊕ ℚ`）。`ℤ[X] ⊗ ℚ ≅ ℚ[X]` 的
    换基管道自建于 `MH_ABGV52`（本件不使用）。
  * 结论 `P ≅ 8·ℤ[H] ⊕ ℤ` 同形表为 `ℤ[X] ≅ ℤ[(Fin 8 × H) ⊔ PUnit]`（`Rep ℤ H` 同构）。

  数学路线（论文特征标论证的等价初等化；论文的「特征标」在此实现为**迹**）
  ==========================================================
  §1 置换映射的迹 = 不动点数（基 `single x 1` 下是置换矩阵）；Rep 同构两端迹相等。
  §2 由假设抽出：`#X = 73` 且 `∀ g ≠ 1`，`g` 恰有一个不动点。
  §3 计数核（不用方程组）：`g ≠ 1` 的唯一不动点 `x_g` 的**轨道**整个被 `g` 固定
     （关键：`H` 交换）⟹ 轨道 ⊆ Fix(g) = {x_g} ⟹ `x_g` 是 H-不动点 ⟹
     H-不动点唯一（记 `x₀`）且其余点稳定子平凡（自由）。
  §4 自由部 `Y = {自由点}` ≃ `Fin 8 × H`（轨道代表元 ＋ 自由性；Burnside 给出轨道数 8），
     装配等变双射 `X ≅ (Fin 8 × H) ⊕ PUnit`（`mainEquiv`／`mainEquiv_smul`）。
  §5 `Rep ℤ H` 层结论（`MonoidAlgebra.mapDomainLinearEquiv` 沿等变双射搬运）。

  本件为**补全覆盖表**性质（§3ao：两条目不在关键路径，唯一下游 `prop:M_H-not-permutation`
  经论文自评「strictly weaker」）。
-/
import ABGV52.Hyp_ABGV52
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Prime.Basic

open CategoryTheory

namespace ABGV52.PC

/-! ## 0. 模型 H-集 `(Fin 8 × H) ⊔ PUnit` -/

/-- `Fin 8 × H` 上的 `H`-作用：作用在第二坐标（8 个正则块）。 -/
noncomputable instance instMulActionFinProd : MulAction H (Fin 8 × H) where
  smul g p := (p.1, g * p.2)
  one_smul p := by
    show (p.1, 1 * p.2) = p
    rw [one_mul]
  mul_smul g₁ g₂ p := by
    show (p.1, (g₁ * g₂) * p.2) = (p.1, g₁ * (g₂ * p.2))
    rw [mul_assoc]

/-- 模型集：`(Fin 8 × H) ⊔ PUnit`（= 8 个正则块 ⊔ 单点）。 -/
abbrev ModelPH : Type := (Fin 8 × H) ⊕ PUnit

/-- 模型集上的 `H`-作用：`Fin 8 × H` 部分按 §0，`PUnit` 部分不动。 -/
noncomputable instance instMulActionModelPH : MulAction H ModelPH where
  smul g x := Sum.map (fun p : Fin 8 × H => (p.1, g * p.2)) id x
  one_smul x := by
    cases x with
    | inl p =>
      show Sum.inl (p.1, 1 * p.2) = Sum.inl p
      rw [one_mul]
    | inr u => rfl
  mul_smul g₁ g₂ x := by
    cases x with
    | inl p =>
      show Sum.inl (p.1, (g₁ * g₂) * p.2) = Sum.inl (p.1, g₁ * (g₂ * p.2))
      rw [mul_assoc]
    | inr u => rfl

/-- `|H| = 9`。 -/
lemma card_H : Fintype.card H = 9 := by
  simp [H, C3, ZMod.card]

/-- 模型基数 `73 = 8·9 + 1`。 -/
lemma card_modelPH : Fintype.card ModelPH = 73 := by
  simp [ModelPH, card_H]

/-! ## 1. 迹 ＝ 不动点数（置换映射） -/

/-- 置换映射 `lmapDomain σ` 的迹 = `σ` 的不动点数。 -/
theorem trace_lmapDomain {X : Type*} [Fintype X] [DecidableEq X] (σ : X → X) :
    LinearMap.trace ℚ (X →₀ ℚ) (Finsupp.lmapDomain ℚ ℚ σ)
      = ((Finset.univ.filter (fun x : X => σ x = x)).card : ℚ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℚ Finsupp.basisSingleOne, Matrix.trace,
    ← Finset.sum_boole (fun x : X => σ x = x) Finset.univ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  show (Finsupp.lmapDomain ℚ ℚ σ (Finsupp.single x 1) : X →₀ ℚ) x = if σ x = x then 1 else 0
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply]

/-- 系数层：群环上的作用经 `coeffLinearEquiv` 共轭即 `lmapDomain`（照 S4 `coeff_rho`）。 -/
theorem coeff_rho (X : Type*) [MulAction H X] (g : H) (w : MonoidAlgebra ℚ X) :
    (MonoidAlgebra.coeffLinearEquiv ℚ) ((Rep.ofMulAction ℚ H X).ρ g w)
      = Finsupp.lmapDomain ℚ ℚ (g • ·) ((MonoidAlgebra.coeffLinearEquiv ℚ) w) := by
  rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- `ρ g` 共轭到 `lmapDomain`。 -/
theorem conj_rho (X : Type*) [MulAction H X] (g : H) :
    (MonoidAlgebra.coeffLinearEquiv ℚ).conj ((Rep.ofMulAction ℚ H X).ρ g)
      = Finsupp.lmapDomain ℚ ℚ (g • ·) := by
  apply LinearMap.ext
  intro t
  change (MonoidAlgebra.coeffLinearEquiv ℚ)
    ((Rep.ofMulAction ℚ H X).ρ g ((MonoidAlgebra.coeffLinearEquiv ℚ).symm t))
      = (Finsupp.lmapDomain ℚ ℚ (g • ·)) t
  rw [coeff_rho X g ((MonoidAlgebra.coeffLinearEquiv ℚ).symm t),
    LinearEquiv.apply_symm_apply]

/-- **`ρ g` 的迹 = `g` 的不动点数**。 -/
theorem trace_rho (X : Type*) [Fintype X] [DecidableEq X] [MulAction H X] (g : H) :
    LinearMap.trace ℚ (MonoidAlgebra ℚ X) ((Rep.ofMulAction ℚ H X).ρ g)
      = ((Finset.univ.filter (fun x : X => g • x = x)).card : ℚ) := by
  rw [← LinearMap.trace_conj' ((Rep.ofMulAction ℚ H X).ρ g)
    (MonoidAlgebra.coeffLinearEquiv ℚ), conj_rho X g, trace_lmapDomain]

/-- **Rep 同构两端迹相等**（经 `isIntertwining'` 字段 ＋ `trace_conj'`）。 -/
theorem trace_eq_of_iso (A B : Rep ℚ H) (e : A ≅ B) (g : H) :
    LinearMap.trace ℚ B.V (B.ρ g) = LinearMap.trace ℚ A.V (A.ρ g) := by
  set F : A.V ≃ₗ[ℚ] B.V := (Representation.equivOfIso e).toLinearEquiv with hF
  have h2 : F.toLinearMap.comp (A.ρ g) = (B.ρ g).comp F.toLinearMap :=
    (Representation.equivOfIso e).isIntertwining' g
  have h : B.ρ g = F.conj (A.ρ g) := by
    rw [LinearEquiv.conj_apply, h2]
    ext v
    simp [LinearMap.comp_apply]
  rw [h, LinearMap.trace_conj']

/-! ## 2. 模型读数与假设抽取 -/

/-- 群中 `g * h = h ⟹ g = 1`。 -/
lemma mul_eq_self_imp (g h : H) (hg : g * h = h) : g = 1 := by
  have h1 : g * h = 1 * h := by rw [one_mul]; exact hg
  exact mul_right_cancel h1

/-- 单位元处：不动点数 = 全基数。 -/
lemma fixCount_one (X : Type*) [Fintype X] [DecidableEq X] [MulAction H X] :
    (Finset.univ.filter (fun x : X => (1 : H) • x = x)).card = Fintype.card X := by
  rw [show (Finset.univ.filter (fun x : X => (1 : H) • x = x)) = Finset.univ from
    Finset.filter_true_of_mem fun x _ => one_smul H x]
  exact Finset.card_univ

/-- 非单位元在 `Fin 8 × H` 部分无不动点。 -/
lemma smul_inl_ne_inl (g : H) (hg : g ≠ 1) (p : Fin 8 × H) :
    g • Sum.inl p ≠ (Sum.inl p : ModelPH) := by
  intro hcon
  have h' : (p.1, g * p.2) = p := Sum.inl.inj hcon
  exact hg (mul_eq_self_imp g p.2 (congrArg Prod.snd h'))

/-- 模型上非单位元恰有一个不动点（`PUnit` 的唯一点）。 -/
lemma fixCount_modelPH (g : H) (hg : g ≠ 1) :
    (Finset.univ.filter (fun x : ModelPH => g • x = x)).card = 1 := by
  have hset : (Finset.univ.filter (fun x : ModelPH => g • x = x)) = {Sum.inr PUnit.unit} := by
    ext x
    rcases x with p | u
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun hcon => absurd hcon (smul_inl_ne_inl g hg p)
      · exact fun hcon => absurd hcon (by simp)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have h1 : g • (Sum.inr u : ModelPH) = Sum.inr u := by
        show Sum.map (fun p : Fin 8 × H => (p.1, g * p.2)) id (Sum.inr u) = Sum.inr u
        rfl
      have h2 : (Sum.inr u : ModelPH) = Sum.inr PUnit.unit :=
        congrArg Sum.inr (Subsingleton.elim u PUnit.unit)
      rw [h1, h2]
      simp
  rw [hset, Finset.card_singleton]

/-- 模型上单位元的不动点数 = 73。 -/
lemma fixCount_modelPH_one :
    (Finset.univ.filter (fun x : ModelPH => (1 : H) • x = x)).card = 73 := by
  rw [fixCount_one ModelPH, card_modelPH]

/-- **由 Rep 同构抽出 `#X = 73`**（迹在 `g = 1` 处 = 维数）。 -/
theorem card_eq_of_repIso (X : Type) [Fintype X] [DecidableEq X] [MulAction H X]
    (h : Nonempty (Rep.ofMulAction ℚ H X ≅ Rep.ofMulAction ℚ H ModelPH)) :
    Fintype.card X = 73 := by
  obtain ⟨e⟩ := h
  have hmain : ((Finset.univ.filter (fun x : ModelPH => (1 : H) • x = x)).card : ℚ)
      = ((Finset.univ.filter (fun x : X => (1 : H) • x = x)).card : ℚ) :=
    (trace_rho ModelPH 1).symm.trans ((trace_eq_of_iso _ _ e 1).trans (trace_rho X 1))
  rw [fixCount_modelPH_one, fixCount_one X] at hmain
  exact Nat.cast_injective hmain.symm

/-- **由 Rep 同构抽出：`∀ g ≠ 1`，`g` 恰一个不动点**。 -/
theorem fixCount_eq_of_repIso (X : Type) [Fintype X] [DecidableEq X] [MulAction H X]
    (h : Nonempty (Rep.ofMulAction ℚ H X ≅ Rep.ofMulAction ℚ H ModelPH))
    (g : H) (hg : g ≠ 1) :
    (Finset.univ.filter (fun x : X => g • x = x)).card = 1 := by
  obtain ⟨e⟩ := h
  have hmain : ((Finset.univ.filter (fun x : ModelPH => g • x = x)).card : ℚ)
      = ((Finset.univ.filter (fun x : X => g • x = x)).card : ℚ) :=
    (trace_rho ModelPH g).symm.trans ((trace_eq_of_iso _ _ e g).trans (trace_rho X g))
  rw [fixCount_modelPH g hg] at hmain
  exact Nat.cast_injective hmain.symm

/-! ## 3. 计数核：唯一 H-不动点 ＋ 其余自由

  路线（比论文的 Burnside/方程组更直接，等价的初等论证）：
  * 每个 `g ≠ 1` 的唯一不动点 `x_g`：其轨道整个被 `g` 固定（H 交换）⟹
    轨道 ⊆ Fix(g) = {x_g} ⟹ `x_g` 是 H-不动点；
  * 由此 H-不动点唯一（任意 H-不动点被 `g` 固定 ⟹ 等于 `x_g`）；
  * 其余点的稳定子平凡（若 `g y = y` 且 `y ≠ x₀` 则 `y = x_g = x₀`，矛盾）。 -/

section Kernel

variable {X : Type} [Fintype X] [DecidableEq X] [MulAction H X]

/-- `g ≠ 1` 的唯一不动点存在唯一。 -/
lemma existsUnique_fixed (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (g : H) (hg : g ≠ 1) : ∃! x : X, g • x = x := by
  have hcard1 : Fintype.card (MulAction.fixedBy X g) = 1 := hfix g hg
  have hsub : Subsingleton (MulAction.fixedBy X g) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard1)
  have hne : Nonempty (MulAction.fixedBy X g) :=
    Fintype.card_pos_iff.mp (by rw [hcard1]; norm_num)
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, MulAction.mem_fixedBy.mp hx, fun y hy => ?_⟩
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨y, MulAction.mem_fixedBy.mpr hy⟩ : MulAction.fixedBy X g) ⟨x, hx⟩)

/-- 唯一不动点的轨道是单点 ⟹ 它是 H-不动点（关键：`H` 交换）。 -/
lemma forall_smul_eq_of_fixed (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (g : H) (hg : g ≠ 1) {x : X} (hx : g • x = x) : ∀ k : H, k • x = x := by
  have hcard1 : Fintype.card (MulAction.fixedBy X g) = 1 := hfix g hg
  have hsub : Subsingleton (MulAction.fixedBy X g) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard1)
  intro k
  have hmem : k • x ∈ MulAction.fixedBy X g := by
    rw [MulAction.mem_fixedBy]
    calc g • (k • x) = (g * k) • x := (mul_smul g k x).symm
      _ = (k * g) • x := by rw [mul_comm]
      _ = k • (g • x) := mul_smul k g x
      _ = k • x := by rw [hx]
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨k • x, hmem⟩ : MulAction.fixedBy X g) ⟨x, MulAction.mem_fixedBy.mpr hx⟩)

/-- 一个具体的非单位元。 -/
def g0 : H := (Multiplicative.ofAdd (1 : ZMod 3), 1)

lemma g0_ne_one : g0 ≠ 1 := by decide

/-- **H-不动点存在唯一**。 -/
lemma existsUnique_fixed_all
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1) :
    ∃! x₀ : X, ∀ g : H, g • x₀ = x₀ := by
  obtain ⟨x₀, hx₀, huniq⟩ := existsUnique_fixed hfix g0 g0_ne_one
  have hx₀all : ∀ g : H, g • x₀ = x₀ := by
    intro g
    by_cases hg : g = 1
    · rw [hg, one_smul]
    · obtain ⟨xg, hxg, _⟩ := existsUnique_fixed hfix g hg
      have hg0xg : g0 • xg = xg := forall_smul_eq_of_fixed hfix g hg hxg g0
      rw [← huniq xg hg0xg]
      exact hxg
  exact ⟨x₀, hx₀all, fun y hy => huniq y (hy g0)⟩

/-- 非不动点自由：稳定子平凡。 -/
lemma free_of_ne (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    {x₀ : X} (hx₀ : ∀ g : H, g • x₀ = x₀) {y : X} (hy : y ≠ x₀)
    {g : H} (hgy : g • y = y) : g = 1 := by
  by_contra hg1
  have hyall : ∀ k : H, k • y = y := forall_smul_eq_of_fixed hfix g hg1 hgy
  obtain ⟨w, hw, huniq⟩ := existsUnique_fixed_all hfix
  exact hy ((huniq y hyall).trans (huniq x₀ hx₀).symm)

/-! ## 4. 自由部 ≃ `Fin 8 × H`，装配 H-集同构 -/

section Assembly

-- 自由点谓词是 `∀`-型：本段内一律用经典可判定性（文件整体 noncomputable）。
attribute [local instance] Classical.propDecidable

variable {hcardA : Fintype.card X = 73}
variable {hfixA : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1}
variable {x₀A : X}

/-- 自由点：稳定子平凡。 -/
def IsFreePt (y : X) : Prop := ∀ g : H, g • y = y → g = 1

/-- 自由点集（作用的不变子集）。 -/
abbrev FreePart (X : Type) [MulAction H X] : Type := {y : X // IsFreePt y}

/-- 自由性是作用不变的 ⟹ `Y` 是 H-集。 -/
noncomputable instance instMulActionFreePart : MulAction H (FreePart X) where
  smul g y := ⟨g • y.1, by
    intro k hk
    have h1 : (g⁻¹ * k * g) • y.1 = y.1 := by
      calc (g⁻¹ * k * g) • y.1 = g⁻¹ • (k • (g • y.1)) := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • y.1) := by rw [hk]
        _ = y.1 := by rw [← mul_smul, inv_mul_cancel, one_smul]
    calc k = g * (g⁻¹ * k * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [y.2 _ h1]
      _ = 1 := by group⟩
  one_smul y := Subtype.ext (one_smul H y.1)
  mul_smul a b y := Subtype.ext (mul_smul a b y.1)

/-- `Y` 上作用是自由的：`a • z = b • z → a = b`。 -/
lemma smul_inj_of_free {z : (FreePart X)} (a b : H) (h : a • z = b • z) : a = b := by
  have hz : (b⁻¹ * a) • z = z := by
    rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have h1 : b⁻¹ * a = 1 := z.2 (b⁻¹ * a) (Subtype.ext_iff.mp hz)
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [h1, mul_one]

/-- 非自由 ⟺ `= x₀`（唯一非自由点）。 -/
lemma not_free_iff (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) (y : X) : ¬ IsFreePt y ↔ y = x₀A := by
  constructor
  · intro h
    rw [IsFreePt] at h
    push Not at h
    obtain ⟨g, hgy, hg1⟩ := h
    have hyall : ∀ k : H, k • y = y := forall_smul_eq_of_fixed hfix g hg1 hgy
    obtain ⟨w, hw, huniq⟩ := existsUnique_fixed_all hfix
    exact (huniq y hyall).trans (huniq x₀A hx₀).symm
  · intro h hfree
    rw [IsFreePt] at hfree
    exact g0_ne_one (hfree g0 (by rw [h]; exact hx₀ g0))

/-- `|Y| = 72`。 -/
lemma card_freePart (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) : Fintype.card (FreePart X) = 72 := by
  have hiff : ∀ y : X, IsFreePt y ↔ y ≠ x₀A := by
    intro y
    constructor
    · intro hfree hy
      exact (not_free_iff hfix hx₀ y).mpr hy hfree
    · intro hy
      by_contra hnf
      exact hy ((not_free_iff hfix hx₀ y).mp hnf)
  have h1 : Fintype.card (FreePart X) = Fintype.card {y : X // y ≠ x₀A} :=
    Fintype.card_congr (Equiv.subtypeEquivRight hiff)
  have h2 : Fintype.card {y : X // y ≠ x₀A} = Fintype.card X - 1 := by
    rw [Fintype.card_subtype (fun y : X => y ≠ x₀A), Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ x₀A), Finset.card_univ]
  rw [h1, h2, hcard]

/-- Burnside：`Y` 自由 ⟹ 轨道商基数 `8`。 -/
lemma card_quotient_free (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) :
    Nat.card (MulAction.orbitRel.Quotient H (FreePart X)) = 8 := by
  haveI : Fintype (MulAction.orbitRel.Quotient H (FreePart X)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H (FreePart X)
  have hterm : ∀ g ∈ (Finset.univ : Finset H),
      Fintype.card (MulAction.fixedBy (FreePart X) g) = if g = 1 then 72 else 0 := by
    intro g _
    by_cases hg : g = 1
    · subst hg
      have h1 : MulAction.fixedBy (FreePart X) (1 : H) = Set.univ := by
        ext y
        simp [MulAction.mem_fixedBy]
      rw [if_pos rfl]
      exact (Fintype.card_congr (Equiv.setCongr h1)).trans
        ((Fintype.card_congr (Equiv.Set.univ _)).trans (card_freePart hcard hfix hx₀))
    · rw [if_neg hg, Fintype.card_eq_zero_iff]
      exact ⟨fun z => hg (z.1.2 g (Subtype.ext_iff.mp z.2))⟩
  have hsum : (∑ g : H, Fintype.card (MulAction.fixedBy (FreePart X) g)) = 72 :=
    (Finset.sum_congr rfl hterm).trans (by rw [Finset.sum_ite_eq']; simp)
  have h72 : Nat.card (MulAction.orbitRel.Quotient H (FreePart X)) * 9 = 72 := by
    have h := hB.symm.trans hsum
    rw [← Nat.card_eq_fintype_card, card_H] at h
    exact h
  omega

variable (hcard : Fintype.card X = 73)
variable (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
variable (hx₀ : ∀ g : H, g • x₀A = x₀A)

/-- 代表元。 -/
noncomputable def repY (q : MulAction.orbitRel.Quotient H (FreePart X)) : (FreePart X) :=
  Quotient.out q

/-- 轨道商中的像。 -/
noncomputable abbrev orb (y : (FreePart X)) : MulAction.orbitRel.Quotient H (FreePart X) :=
  Quotient.mk'' y

lemma repY_spec (q : MulAction.orbitRel.Quotient H (FreePart X)) :
    Quotient.mk'' (repY q) = q := Quotient.out_eq' q

/-- 同轨 ⟹ 存在 `h`。 -/
lemma exists_smul_repY (y : (FreePart X)) :
    ∃ h : H, h • repY (orb y) = y := by
  have hq : orb (repY (orb y)) = orb y := repY_spec (orb y)
  have hrel : MulAction.orbitRel H (FreePart X) y (repY (orb y)) :=
    Quotient.exact' hq.symm
  rw [MulAction.orbitRel_apply] at hrel
  exact MulAction.mem_orbit_iff.mp hrel

/-- 唯一性（代表元处自由）。 -/
lemma repY_unique (y : (FreePart X)) {h : H}
    (hh : h • repY (orb y) = y) :
    h = Classical.choose (exists_smul_repY y) :=
  smul_inj_of_free (a := h) (b := Classical.choose (exists_smul_repY y))
    (by rw [hh, Classical.choose_spec (exists_smul_repY y)])

/-- `mk'' (h • repY q) = q`。 -/
lemma mk_smul_repY (q : MulAction.orbitRel.Quotient H (FreePart X)) (h : H) :
    orb (h • repY q) = q := by
  have h1 : orb (h • repY q) = orb (repY q) := by
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨h, rfl⟩
  rw [h1]
  exact repY_spec q

/-- `Ω ≃ Fin 8`。 -/
noncomputable def eΩY (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) :
    MulAction.orbitRel.Quotient H (FreePart X) ≃ Fin 8 := by
  haveI : Fintype (MulAction.orbitRel.Quotient H (FreePart X)) := Fintype.ofFinite _
  refine Fintype.equivFinOfCardEq ?_
  rw [← Nat.card_eq_fintype_card]
  exact card_quotient_free hcard hfix hx₀

/-- **自由部 ≃ `Fin 8 × H`**。 -/
noncomputable def freeEquiv (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) : (FreePart X) ≃ Fin 8 × H where
  toFun y := (eΩY hcard hfix hx₀ (orb y), Classical.choose (exists_smul_repY y))
  invFun p := p.2 • repY ((eΩY hcard hfix hx₀).symm p.1)
  left_inv y := by
    change Classical.choose (exists_smul_repY y) •
      repY ((eΩY hcard hfix hx₀).symm ((eΩY hcard hfix hx₀) (orb y))) = y
    rw [Equiv.symm_apply_apply, Classical.choose_spec (exists_smul_repY y)]
  right_inv p := by
    obtain ⟨i, h⟩ := p
    have hmk := mk_smul_repY ((eΩY hcard hfix hx₀).symm i) h
    have hrep : Classical.choose (exists_smul_repY
        (h • repY ((eΩY hcard hfix hx₀).symm i))) = h :=
      (repY_unique _ (by rw [hmk])).symm
    have h1 : (eΩY hcard hfix hx₀) (orb (h • repY ((eΩY hcard hfix hx₀).symm i))) = i := by
      rw [hmk, Equiv.apply_symm_apply]
    exact Prod.ext h1 hrep

/-- `freeEquiv` 的等变性。 -/
lemma freeEquiv_smul (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) (g : H) (y : (FreePart X)) :
    freeEquiv hcard hfix hx₀ (g • y)
      = (eΩY hcard hfix hx₀ (Quotient.mk'' y), g * Classical.choose (exists_smul_repY y)) := by
  have hmk : orb (g • y) = orb y := by
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩
  have hrep : g * Classical.choose (exists_smul_repY y)
      = Classical.choose (exists_smul_repY (g • y)) := by
    refine smul_inj_of_free
      (a := g * Classical.choose (exists_smul_repY y))
      (b := Classical.choose (exists_smul_repY (g • y)))
      (z := repY (orb (g • y))) ?_
    calc (g * Classical.choose (exists_smul_repY y)) • repY (orb (g • y))
        = g • (Classical.choose (exists_smul_repY y) • repY (orb (g • y))) := by
          rw [mul_smul]
      _ = g • (Classical.choose (exists_smul_repY y) • repY (orb y)) := by rw [hmk]
      _ = g • y := by rw [Classical.choose_spec (exists_smul_repY y)]
      _ = Classical.choose (exists_smul_repY (g • y)) • repY (orb (g • y)) :=
          (Classical.choose_spec (exists_smul_repY (g • y))).symm
  have h1 : (eΩY hcard hfix hx₀) (orb (g • y)) = (eΩY hcard hfix hx₀) (orb y) := by
    rw [hmk]
  show (eΩY hcard hfix hx₀ (orb (g • y)), Classical.choose (exists_smul_repY (g • y)))
    = (eΩY hcard hfix hx₀ (orb y), g * Classical.choose (exists_smul_repY y))
  exact (Prod.mk.injEq _ _ _ _).mpr ⟨h1, hrep.symm⟩

/-- 非自由部是单点。 -/
noncomputable def singEquiv (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) :
    {y : X // ¬ IsFreePt y} ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨x₀A, (not_free_iff hfix hx₀ x₀A).mpr rfl⟩
  left_inv z := Subtype.ext ((not_free_iff hfix hx₀ z.1).mp z.2).symm
  right_inv u := by cases u; rfl

/-- **装配：`X ≃ (Fin 8 × H) ⊕ PUnit`**。 -/
noncomputable def mainEquiv (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) : X ≃ ModelPH where
  toFun x := if hx : IsFreePt x
    then Sum.inl (freeEquiv hcard hfix hx₀ ⟨x, hx⟩)
    else Sum.inr PUnit.unit
  invFun p := p.elim (fun p' => ((freeEquiv hcard hfix hx₀).symm p').1) (fun _ => x₀A)
  left_inv x := by
    by_cases hx : IsFreePt x
    · simp only [dif_pos hx]
      exact congrArg Subtype.val ((freeEquiv hcard hfix hx₀).symm_apply_apply ⟨x, hx⟩)
    · simp only [dif_neg hx]
      exact ((not_free_iff hfix hx₀ x).mp hx).symm
  right_inv p := by
    rcases p with i | u
    · have hfree : IsFreePt ((freeEquiv hcard hfix hx₀).symm i).1 :=
        ((freeEquiv hcard hfix hx₀).symm i).2
      show (if h : IsFreePt ((freeEquiv hcard hfix hx₀).symm i).1 then
        Sum.inl (freeEquiv hcard hfix hx₀ ⟨((freeEquiv hcard hfix hx₀).symm i).1, h⟩)
        else Sum.inr PUnit.unit) = Sum.inl i
      rw [dif_pos hfree]
      exact congrArg Sum.inl ((freeEquiv hcard hfix hx₀).apply_symm_apply i)
    · cases u
      show (if hx : IsFreePt x₀A then Sum.inl (freeEquiv hcard hfix hx₀ ⟨x₀A, hx⟩)
        else Sum.inr PUnit.unit) = Sum.inr PUnit.unit
      rw [dif_neg ((not_free_iff hfix hx₀ x₀A).mpr rfl)]

/-- **`mainEquiv` 的等变性**。 -/
theorem mainEquiv_smul (hcard : Fintype.card X = 73)
    (hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1)
    (hx₀ : ∀ g : H, g • x₀A = x₀A) (g : H) (x : X) :
    mainEquiv hcard hfix hx₀ (g • x) = g • mainEquiv hcard hfix hx₀ x := by
  by_cases hx : IsFreePt x
  · have hgx : IsFreePt (g • x) := (g • (⟨x, hx⟩ : (FreePart X))).2
    have hstep : (⟨g • x, hgx⟩ : (FreePart X)) = g • (⟨x, hx⟩ : (FreePart X)) :=
      Subtype.ext rfl
    show (if hx' : IsFreePt (g • x) then
        Sum.inl (freeEquiv hcard hfix hx₀ ⟨g • x, hx'⟩) else Sum.inr PUnit.unit)
      = g • (if hx' : IsFreePt x then
        Sum.inl (freeEquiv hcard hfix hx₀ ⟨x, hx'⟩) else Sum.inr PUnit.unit)
    rw [dif_pos hgx, dif_pos hx]
    show Sum.inl (freeEquiv hcard hfix hx₀ ⟨g • x, hgx⟩)
      = Sum.inl ((freeEquiv hcard hfix hx₀ ⟨x, hx⟩).1,
          g * (freeEquiv hcard hfix hx₀ ⟨x, hx⟩).2)
    rw [hstep]
    exact congrArg Sum.inl (freeEquiv_smul hcard hfix hx₀ g ⟨x, hx⟩)
  · have hxeq : x = x₀A := (not_free_iff hfix hx₀ x).mp hx
    have hgx_not : ¬ IsFreePt (g • x) := by
      rw [not_free_iff hfix hx₀, hxeq, hx₀ g]
    show (if hx' : IsFreePt (g • x) then
        Sum.inl (freeEquiv hcard hfix hx₀ ⟨g • x, hx'⟩) else Sum.inr PUnit.unit)
      = g • (if hx' : IsFreePt x then
        Sum.inl (freeEquiv hcard hfix hx₀ ⟨x, hx'⟩) else Sum.inr PUnit.unit)
    rw [dif_neg hgx_not, dif_neg hx]
    rfl

end Assembly

/-! ## 5. `Rep ℤ H` 层：主定理 -/

/-- `fixedBy` 的基数 = 不动点过滤器基数。 -/
lemma fixedBy_card_eq_filter {X : Type} [Fintype X] [DecidableEq X] [MulAction H X] (g : H) :
    Fintype.card (MulAction.fixedBy X g)
      = (Finset.univ.filter (fun x : X => g • x = x)).card :=
  Fintype.card_subtype _

/-- 系数层（`ℤ`）：群环作用 ↦ `lmapDomain`。 -/
lemma coeff_rho_Z {X : Type*} [MulAction H X] (g : H) (w : MonoidAlgebra ℤ X) :
    ((Rep.ofMulAction ℤ H X).ρ g w).coeff
      = Finsupp.lmapDomain ℤ ℤ (g • ·) w.coeff := by
  show (MonoidAlgebra.coeffLinearEquiv ℤ) ((Rep.ofMulAction ℤ H X).ρ g w)
      = Finsupp.lmapDomain ℤ ℤ (g • ·) ((MonoidAlgebra.coeffLinearEquiv ℤ) w)
  rw [Representation.ofMulAction_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- `Finsupp` 层：等变双射搬运 `lmapDomain`。 -/
lemma equivMapDomain_lmapDomain' {X Y : Type} [MulAction H X] [MulAction H Y]
    (e : X ≃ Y) (he : ∀ (g : H) (x : X), e (g • x) = g • e x) (g : H) (f : X →₀ ℤ) :
    Finsupp.equivMapDomain e (Finsupp.lmapDomain ℤ ℤ (fun x => g • x) f)
      = Finsupp.lmapDomain ℤ ℤ (fun y => g • y) (Finsupp.equivMapDomain e f) := by
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr (fun x _ => he g x)

/-- 等变双射 ⟹ 置换模同构（系数层计算）。 -/
theorem mapDomainLinearEquiv_equivariant {X Y : Type} [MulAction H X] [MulAction H Y]
    [DecidableEq X] [DecidableEq Y] (e : X ≃ Y)
    (he : ∀ (g : H) (x : X), e (g • x) = g • e x) (g : H) (z : MonoidAlgebra ℤ X) :
    MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ e ((Rep.ofMulAction ℤ H X).ρ g z)
      = (Rep.ofMulAction ℤ H Y).ρ g (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ e z) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_mapDomainLinearEquiv]
  rw [coeff_rho_Z, coeff_rho_Z, MonoidAlgebra.coeff_mapDomainLinearEquiv]
  exact equivMapDomain_lmapDomain' e he g z.coeff

/-- `H`-集之间的等变双射。 -/
structure HSetEquiv (X Y : Type*) [MulAction H X] [MulAction H Y] where
  toEquiv : X ≃ Y
  map_smul' : ∀ (g : H) (x : X), toEquiv (g • x) = g • toEquiv x

/-- **`lem:perm-class`（H-集层）**：由 Rep 同构假设得等变双射 `X ≃ (Fin 8 × H) ⊕ PUnit`。 -/
theorem permClass_HSet (X : Type) [Fintype X] [DecidableEq X] [MulAction H X]
    (h : Nonempty (Rep.ofMulAction ℚ H X ≅ Rep.ofMulAction ℚ H ModelPH)) :
    Nonempty (HSetEquiv X ModelPH) := by
  have hcard : Fintype.card X = 73 := card_eq_of_repIso X h
  have hfix : ∀ g : H, g ≠ 1 → Fintype.card (MulAction.fixedBy X g) = 1 := fun g hg => by
    rw [fixedBy_card_eq_filter, fixCount_eq_of_repIso X h g hg]
  obtain ⟨x₀, hx₀, -⟩ := existsUnique_fixed_all hfix
  exact ⟨⟨mainEquiv hcard hfix hx₀, mainEquiv_smul hcard hfix hx₀⟩⟩

/-- **`lem:perm-class`（主定理，`Rep ℤ H` 层，论文形）**：
设 `X` 为有限 `H`-集且 `ℚ[X] ≅ 8·ℚ[H] ⊕ ℚ`（置换模模型形），则
`ℤ[X] ≅ 8·ℤ[H] ⊕ ℤ`（置换模模型形）。 -/
theorem permClass (X : Type) [Fintype X] [DecidableEq X] [MulAction H X]
    (h : Nonempty (Rep.ofMulAction ℚ H X ≅ Rep.ofMulAction ℚ H ModelPH)) :
    Nonempty (Rep.ofMulAction ℤ H X ≅ Rep.ofMulAction ℤ H ModelPH) := by
  obtain ⟨⟨e, he⟩⟩ := permClass_HSet X h
  refine ⟨Rep.mkIso (Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ e)
    (fun g => LinearMap.ext (fun z => mapDomainLinearEquiv_equivariant e he g z)))⟩

/-- **装配件**：`mainEquiv` 在 `Rep` 层的搬运（陈述用）。 -/
theorem permClass_reprIso (X : Type) [Fintype X] [DecidableEq X] [MulAction H X]
    (h : Nonempty (Rep.ofMulAction ℚ H X ≅ Rep.ofMulAction ℚ H ModelPH)) :
    ∃ (e : X ≃ ModelPH) (_ : ∀ (g : H) (x : X), e (g • x) = g • e x),
      Nonempty (Rep.ofMulAction ℤ H X ≅ Rep.ofMulAction ℤ H ModelPH) := by
  obtain ⟨⟨e, he⟩⟩ := permClass_HSet X h
  exact ⟨e, he, ⟨Rep.mkIso (Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ e)
    (fun g => LinearMap.ext (fun z => mapDomainLinearEquiv_equivariant e he g z)))⟩⟩

end Kernel

/-\! ## 6. 公理闸门（无 sorry、无自造公理） -/

#print axioms card_eq_of_repIso
#print axioms fixCount_eq_of_repIso
#print axioms existsUnique_fixed_all
#print axioms card_quotient_free
#print axioms freeEquiv_smul
#print axioms mainEquiv_smul
#print axioms mapDomainLinearEquiv_equivariant
#print axioms permClass_HSet
#print axioms permClass

end ABGV52.PC
