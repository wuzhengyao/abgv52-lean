/-
  Procesi —— **`lem:14.24`（`K'`-世界）的装配**：`ThetaAgreeHypK'` 成为定理

  R727 在 `KPrimeLem1424` §19 机检了 `lem:14.24` 的 `K'`-世界一般形态
  （`sprLem1424_generalK'`：`T` 任意、判别式非零因子）。本节把它接到 `prop:14.19`
  的装配上——这正是 §7.18 判读里 `(乙)` 的**目的**：

  > `ThetaAgreeHypK'`（＝ `lem:14.24` 的 `K'`-世界结论）**不再是具名假设**。

  **本件的射程（勿夸大）**：`ThetaAgreeHypK'` 现在**条件于 `UDKTensorHypK'`**（PI 输入，
  即 `udkTensorToMatrix` 的双射性）成立。`ZEqNFixed`、中心化、**H2** 仍未证。
-/

import Procesi.H2Final
import Procesi.KPrimeLem1424
import Procesi.SimpleTensor

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin
open scoped TensorProduct

namespace Procesi

variable (F : Type) [Field F] (r n : ℕ)

/-! ## §1 ★★★★★★★★ **`ThetaAgreeHypK'` 是定理**（条件于 PI 输入）

源文 `prop:14.19` 的末段：`θ₁(α) = θ₂(α)`（`lem:14.24`）。R727 把 `lem:14.24` 的
`K'`-世界一般形态机检成定理 ⟹ 本件把它实例化到 `thetaSpr1/2` 上：

* `hX`／`hY`：`thetaSpr_agree_on_xdiag`／`_on_ymat`（`H2Final` §64，已机检）；
* `hΔ`：`sprDiscrNonZeroDiv_thetaSpr1S`（`H2Final` §62，已机检）＋ 纯量矩阵的搬运；
* 其余（`hα : sprMatNFixed α`）就是 `ThetaAgreeHypK'` 的假设。 -/

/-- ★★★★★★★★ **`ThetaAgreeHypK'` 是定理**（条件于 PI 输入 `UDKTensorHypK'`）。

**这是 §7.18 判读中 `(乙)` 路线的**终点**：`lem:14.24` 的 `K'`-世界结论不再需要具名。 -/
theorem thetaAgreeHypK'_unconditional [Nonempty (Fin n)] [NeZero n] [Infinite F]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    ThetaAgreeHypK' F r n D k₀ hk₀ h := by
  intro α hα
  -- 纯量矩阵：`K'`-世界与 `S'`-世界的桥
  have hmap : (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))
      (Matrix.scalar (Fin n) (sprDiscr F (r := r) (n := n)))
      = Matrix.scalar (Fin n)
          (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F (r := r) (n := n))) := by
    rw [AlgHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _)]
    rfl
  refine sprLem1424_generalK' (F := F) (r := r) (n := n)
    (T := sprTensorK F r n D k₀ hk₀) α hα
    ((thetaSpr1 F r n D k₀ hk₀ h).restrictScalars F)
    ((thetaSpr2 F r n D k₀ hk₀ h).restrictScalars F) ?_ ?_ ?_
  · exact thetaSpr_agree_on_xdiag F r n D k₀ hk₀ h
  · intro k
    exact thetaSpr_agree_on_ymat F r n D k₀ hk₀ h k
  · obtain ⟨x, hx, hnd⟩ := sprDiscrNonZeroDiv_thetaSpr1S F r n D k₀ hk₀ h
    refine ⟨x, ?_, hnd⟩
    rw [← hmap]
    exact hx

#print axioms thetaAgreeHypK'_unconditional

/-! ## §2 **`hZ` 与终点**：由 `lem:14.24`（`K'`）直接得 `Z` 半，再接终点链

`ThetaAgreeHypK' ⟺ hZ`（`thetaAgreeHypK'_iff_zHalf`，三路等价）＋ 本轮 §1 ⟹ `hZ` 是定理
（条件于 PI 输入）。再套 `h2_of_zHalf_routeB`（`H2Final:14066`）即得 **H2**。 -/

/-- ★★★★★★★★ **`hZ`（`Z` 半）是定理**（条件于 PI 输入）。 -/
theorem hZ_unconditional [Nonempty (Fin n)] [NeZero n] [Infinite F]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F r n D k₀ hk₀) {k : Fin r} (hk : k ≠ k₀) :
    sprNFixedField F r n ≤ sprCenterImageField F r n D k₀ hk₀ :=
  (hZ_iff_sprNFixedField_le (F := F) (r := r) (n := n) D k₀ hk₀).mp
    ((thetaAgreeHypK'_iff_zHalf (F := F) (r := r) (n := n) D k₀ hk₀ hPI (k₁ := k₀) (k₂ := k)
      (sprXiBasisHypK' (F := F) (r := r) (n := n) k₀ hk₀ hk)).mp
      (thetaAgreeHypK'_unconditional (F := F) (r := r) (n := n) D k₀ hk₀ hPI))

#print axioms hZ_unconditional

/-- ★★★★★★★★★★ **H2**（`ProcesiS9Hyp`），**模 PI 输入 `UDKTensorHypK'`**。

这是本工程的终点：`(乙)` 路线（R702–R727）＋ 三路等价 ＋ 终点链。 -/
theorem h2_modulo_UDKTensor (F : Type) [Field F] [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hPI : UDKTensorHypK' F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) := by
  haveI : Infinite F := infinite_of_charZero F
  exact h2_of_zHalf_routeB F D k₀ hk₀
    (hZ_unconditional (F := F) (r := 2) (n := 9) D k₀ hk₀ hPI
      (k := ⟨1, by omega⟩) (by
        intro hc
        have hval := congrArg Fin.val hc
        rw [show (⟨1, by omega⟩ : Fin 2).val = 1 from rfl, hk₀] at hval
        omega))

#print axioms h2_modulo_UDKTensor

/-! ## §3 **PI 输入的精确剩余 = 单射半**（供后续攻击）

`UDKTensorHypK'` ＝ `udkTensorToMatrix` 的双射性。**满射半已机检**
（`udkTensorToMatrix_surjective_of_xiSpanK'`，由 `XiSpanHypK'`；而 `XiSpanHypK'` 由
`sprXiSpanHypK'` 供给）。本节把剩余部分**精确**写成单射性：

**数学内容**：单射 ⟺ `dim_↥Z UDK' = n²` ⟺ Amitsur 的 `dim_Z UD(F,n,r) = n²`
（源文 `:456` 的 "`M_n(K') = K' ⊗_Z UD(F,n,r)`" 是**引用**的 PI 事实，非源文所证）。
⟹ **这是本工程唯一的剩余外部输入**，与 `(乙)` 路线（R702–R727）无关。 -/

/-- ★★★★★ **PI 输入 ⟺ 单射性**（满射半已机检）。 -/
theorem udkTensorHypK'_iff_injective [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k₁ k₂ : Fin r}
    (hB : XiBasisHypK' F r n k₀ hk₀ k₁ k₂) :
    UDKTensorHypK' F r n D k₀ hk₀
      ↔ Function.Injective (udkTensorToMatrix F r n D k₀ hk₀) := by
  have hsurj : Function.Surjective (udkTensorToMatrix F r n D k₀ hk₀) :=
    udkTensorToMatrix_surjective_of_xiSpanK' F r n D k₀ hk₀
      (xiSpanHypK'_of_xiBasisHypK' F r n hB)
  constructor
  · intro h
    exact h.1
  · intro hinj
    exact ⟨hinj, hsurj⟩

#print axioms udkTensorHypK'_iff_injective

/-! ## §4 ★★★★★★★★ **PI 输入的线性代数归约**（Step 1：`Ξ` 张成 `UDK'` ⟹ 单射）

**动机**（v44 §15.4 Step 1）：`UDKTensorHypK'` 的**满射半**已机检（§3 ＋ `sprXiSpanHypK'`），
剩余的是**单射半**。本节把它**精确归约**为一条纯张成性陈述，**不需要任何 PI 理论**：

```
hspan : ∀ a : ↥(UDK'), a ∈ Submodule.span ↥Z (range Ξ)      （Ξ = X_{k₀}^i X_k^j，n² 个）
⟹ Function.Injective (udkTensorToMatrix …)          （udkTensorToMatrix_injective_of_span）
⟹ UDKTensorHypK'                                     （udkTensorHypK'_of_span）
⟹ ProcesiS9Hyp F ↥(ZCanon F 2 9 D)                   （h2_unconditional_of_span）
```

**证明骨架**（与 PI 无关，纯张量代数）：
① 每个 `t : UDK' ⊗_Z K'` 都能写成 `∑ p, Ξ_p ⊗ c p`（对张量归纳 ＋ `hspan` 的系数搬移
`(z • Ξ) ⊗ b = Ξ ⊗ (algebraMap z * b)`）；② `udkTensorToMatrix` 把 `Ξ_p ⊗ c p` 送到
`c p • Ξ_p`（`udkTensorToMatrix_tmul` ＋ `mul_scalar_eq_smul`）；③ `Ξ` 的 `K'`-线性无关性
`sprXi_linearIndependent` 收口。

**射程（勿夸大）**：本节**不证明** `hspan`。`hspan` 的数学内容是 Amitsur 的
`dim_↥Z UD(F,n,r) = n²`（源文 `:185`／`:222`；AGPR2020 `thm:11.3.1`（2)(3)），
是**唯一剩余的 PI 输入**。`h2_unconditional_of_span` 因此**仍不是无条件 H2**。 -/

variable [NeZero n] [Nonempty (Fin n)]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-- ★★★★★★★ **`Ξ` 张成 `UDK'`（`↥Z`-上）⟹ 求值映射单射**（Step 1 的主件，纯线性代数）。 -/
theorem udkTensorToMatrix_injective_of_span
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀)
    (hspan : ∀ a : ↥(UDK' F r n D k₀ hk₀),
      a ∈ Submodule.span ↥(sprCenterImageField F r n D k₀ hk₀)
        (Set.range (fun p : Fin n × Fin n =>
          (⟨xiSprK F r n k₀ hk₀ k₀ k p.1 p.2,
            xiSprK_mem_UDK' F r n D k₀ hk₀ k₀ k p.1 p.2⟩ :
              ↥(UDK' F r n D k₀ hk₀))))) :
    Function.Injective (udkTensorToMatrix F r n D k₀ hk₀) := by
  classical
  have hli := sprXi_linearIndependent F r n k₀ hk₀ hk
  rw [Fintype.linearIndependent_iff] at hli
  have hex : ∀ t : TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀)
        ↥(UDK' F r n D k₀ hk₀) (SprField F r n),
      ∃ c : Fin n × Fin n → SprField F r n,
        t = ∑ p, (⟨xiSprK F r n k₀ hk₀ k₀ k p.1 p.2,
            xiSprK_mem_UDK' F r n D k₀ hk₀ k₀ k p.1 p.2⟩ :
              ↥(UDK' F r n D k₀ hk₀))
          ⊗ₜ[↥(sprCenterImageField F r n D k₀ hk₀)] (c p) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have ha := hspan a
      rw [Submodule.mem_span_range_iff_exists_fun] at ha
      obtain ⟨c, hc⟩ := ha
      refine ⟨fun p => algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
        (SprField F r n) (c p) * b, ?_⟩
      rw [← hc, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [TensorProduct.smul_tmul]
      simp only [Algebra.smul_def]
    | add x y hx hy =>
      obtain ⟨cx, hx'⟩ := hx
      obtain ⟨cy, hy'⟩ := hy
      refine ⟨cx + cy, ?_⟩
      rw [hx', hy', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Pi.add_apply, TensorProduct.tmul_add]
  have hzero : ∀ t : TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀)
        ↥(UDK' F r n D k₀ hk₀) (SprField F r n),
      udkTensorToMatrix F r n D k₀ hk₀ t = 0 → t = 0 := by
    intro t ht
    obtain ⟨c, hc⟩ := hex t
    have hcoef : ∀ p : Fin n × Fin n, c p = 0 := by
      apply hli c
      have hmap : udkTensorToMatrix F r n D k₀ hk₀ t
          = ∑ p, c p • xiSprK F r n k₀ hk₀ k₀ k p.1 p.2 := by
        rw [hc, map_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [udkTensorToMatrix_tmul, mul_scalar_eq_smul]
      rw [hmap] at ht
      exact ht
    rw [hc]
    simp [hcoef]
  intro t₁ t₂ h12
  have hsub : udkTensorToMatrix F r n D k₀ hk₀ (t₁ - t₂) = 0 := by
    rw [map_sub, h12, sub_self]
  exact sub_eq_zero.mp (hzero (t₁ - t₂) hsub)

#print axioms udkTensorToMatrix_injective_of_span

/-- ★★★★★★★★ **`Ξ` 张成 ⟹ PI 输入 `UDKTensorHypK'`**（满射半由 `sprXiSpanHypK'` 供给）。 -/
theorem udkTensorHypK'_of_span
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀)
    (hspan : ∀ a : ↥(UDK' F r n D k₀ hk₀),
      a ∈ Submodule.span ↥(sprCenterImageField F r n D k₀ hk₀)
        (Set.range (fun p : Fin n × Fin n =>
          (⟨xiSprK F r n k₀ hk₀ k₀ k p.1 p.2,
            xiSprK_mem_UDK' F r n D k₀ hk₀ k₀ k p.1 p.2⟩ :
              ↥(UDK' F r n D k₀ hk₀))))) :
    UDKTensorHypK' F r n D k₀ hk₀ :=
  ⟨udkTensorToMatrix_injective_of_span F r n D k₀ hk₀ hk hspan,
    udkTensorToMatrix_surjective_of_xiSpanK' F r n D k₀ hk₀
      (sprXiSpanHypK' F r n k₀ hk₀ hk)⟩

#print axioms udkTensorHypK'_of_span

/-- ★★★★★★★★★ **H2 的**唯一**剩余（张成形）＝ `Ξ` 在 `↥Z`-上张成 `UDK'`**（v44 §15.4 Step 3）。 -/
theorem h2_unconditional_of_span (F : Type) [Field F] [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hspan : ∀ a : ↥(UDK' F 2 9 D k₀ hk₀),
      a ∈ Submodule.span ↥(sprCenterImageField F 2 9 D k₀ hk₀)
        (Set.range (fun p : Fin 9 × Fin 9 =>
          (⟨xiSprK F 2 9 k₀ hk₀ k₀ ⟨1, by omega⟩ p.1 p.2,
            xiSprK_mem_UDK' F 2 9 D k₀ hk₀ k₀ ⟨1, by omega⟩ p.1 p.2⟩ :
              ↥(UDK' F 2 9 D k₀ hk₀))))) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_modulo_UDKTensor F D k₀ hk₀
    (udkTensorHypK'_of_span F 2 9 D k₀ hk₀ (k := ⟨1, by omega⟩) (by
      intro hc
      have hval := congrArg Fin.val hc
      rw [show (⟨1, by omega⟩ : Fin 2).val = 1 from rfl, hk₀] at hval
      omega) hspan)

#print axioms h2_unconditional_of_span

/-! ## §5 ★★★★★★★★ **PI 输入的文献形态**：`UDK' ⊗_Z K'` 是单环（Rowen p.64）

源文 `raw/Saltman1999ch14.tex:185` 对 PI 输入的原话是：

> "On the other hand, by e.g. `[rowen1980polynomial, p.~64]`, `UD(F,n,r) ⊗_Z K` is a
> **simple ring** and so `UD(F,n,r) ⊗_Z K ≅ M_n(K)`."

本节把 `UDKTensorHypK'`（一个**维数/双射性**陈述）换成**结构陈述**
`IsSimpleRing (UDK' ⊗_Z K')`，并机检二者**等价**。⟹ 剩余 PI 输入从此按**已发表定理**
（Rowen p.64；AGPR2020 `prop:11.2.5`／`thm:11.2.6` Posner；`lem:1.1.16`）记账。

**数学**：单环 ＋ 到非平凡环的环同态 ⟹ 单射（`RingHom.injective`，
mathlib `RingTheory/SimpleRing/Basic.lean`）；反之 `UDK' ⊗_Z K' ≅ M_n(K')` 而
`M_n(K')` 单（`IsSimpleRing.matrix` ＋ `DivisionRing.isSimpleRing`）。

**射程（勿夸大）**：`UDKTensorSimpleHypK'` **未证**。它只是把**同一份** PI 输入
（Amitsur `dim = n²`）重述成文献直接引用的形态，**不减少**数学内容。 -/

/-- ★★★★★★★ **PI 输入的文献形态**：`UDK' ⊗_Z K'` 是单环（Rowen p.64 的原话）。 -/
def UDKTensorSimpleHypK'
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) : Prop :=
  IsSimpleRing (TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀)
    ↥(UDK' F r n D k₀ hk₀) (SprField F r n))

#print axioms UDKTensorSimpleHypK'

/-- ★★★★★★★★★ **单环形态 ⟹ PI 输入**（`RingHom.injective` 一行）。 -/
theorem udkTensorHypK'_of_simple
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀)
    (h : UDKTensorSimpleHypK' F r n D k₀ hk₀) :
    UDKTensorHypK' F r n D k₀ hk₀ := by
  haveI : IsSimpleRing (TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀)
      ↥(UDK' F r n D k₀ hk₀) (SprField F r n)) := h
  refine ⟨fun x y hxy => RingHom.injective
    (udkTensorToMatrix F r n D k₀ hk₀).toRingHom hxy, ?_⟩
  exact udkTensorToMatrix_surjective_of_xiSpanK' F r n D k₀ hk₀
    (sprXiSpanHypK' F r n k₀ hk₀ hk)

#print axioms udkTensorHypK'_of_simple

/-- ★★★★★★★ **PI 输入 ⟹ 单环形态**（`A ⊗_Z K' ≅ M_n(K')` 而 `M_n` 单）。 -/
theorem udkTensorSimpleHypK'_of_udkTensorHypK'
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (h : UDKTensorHypK' F r n D k₀ hk₀) :
    UDKTensorSimpleHypK' F r n D k₀ hk₀ := by
  haveI hnt : Nontrivial (TensorProduct ↥(sprCenterImageField F r n D k₀ hk₀)
      ↥(UDK' F r n D k₀ hk₀) (SprField F r n)) := by
    refine ⟨0, 1, fun hz => ?_⟩
    have h1 := congrArg (udkTensorToMatrix F r n D k₀ hk₀) hz
    simp only [map_zero, map_one] at h1
    exact zero_ne_one h1
  haveI : IsSimpleRing (Matrix (Fin n) (Fin n) (SprField F r n)) :=
    IsSimpleRing.matrix (Fin n) (SprField F r n)
  refine (IsSimpleRing.iff_injective_ringHom (TensorProduct
    ↥(sprCenterImageField F r n D k₀ hk₀) ↥(UDK' F r n D k₀ hk₀)
    (SprField F r n))).mpr ?_
  intro S _ hS f
  haveI : Nontrivial S := hS
  intro x y hxy
  have ha : (udkTensorEquivK' F r n D k₀ hk₀ h) x
      = (udkTensorEquivK' F r n D k₀ hk₀ h) y := by
    refine RingHom.injective
      (f.comp (udkTensorEquivK' F r n D k₀ hk₀ h).symm.toRingHom) ?_
    simpa using hxy
  exact (udkTensorEquivK' F r n D k₀ hk₀ h).injective ha

#print axioms udkTensorSimpleHypK'_of_udkTensorHypK'

/-- ★★★★★★★★★ **H2 的文献形态剩余**：`UDK' ⊗_Z K'` 单 ⟹ `ProcesiS9Hyp`。 -/
theorem h2_unconditional_of_simple (F : Type) [Field F] [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (h : UDKTensorSimpleHypK' F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_modulo_UDKTensor F D k₀ hk₀
    (udkTensorHypK'_of_simple F 2 9 D k₀ hk₀ (k := ⟨1, by omega⟩) (by
      intro hc
      have hval := congrArg Fin.val hc
      rw [show (⟨1, by omega⟩ : Fin 2).val = 1 from rfl, hk₀] at hval
      omega) h)

#print axioms h2_unconditional_of_simple

/-! ## §6 ★★★★★★★★ **PI 输入的最后两块**：`UDK'` 单 ＋ 中心 ＝ `↥Z` ⟹ 单环形态

AGPR2020 `lem:1.1.16` 已在 `Procesi/SimpleTensor.lean` 机检（一般代数，无 PI）。
本节把它实例化到 `S = ↥(UDK')`、`F = ↥Z`、`K = K' = SprField`：

```
IsSimpleRing ↥(UDK')  ＋  Subalgebra.center ↥Z ↥(UDK') = ⊥
  ⟹ IsSimpleRing (UDK' ⊗_Z K')        （＝ UDKTensorSimpleHypK'）
  ⟹ UDKTensorHypK'                    （§5）
  ⟹ ProcesiS9Hyp F ↥(ZCanon F 2 9 D)  （§2）
```

**⟹ 剩余 PI 输入**（两条，均**已发表**）：

* `IsSimpleRing ↥(UDK')` ＝ AGPR2020 `prop:11.2.5`（非零双边理想 ∩ 中心 ≠ 0：其证明用
  **中心多项式**）＋ Saltman `thm:14.6`（照 Rowen p.29）；
* `Subalgebra.center ↥Z ↥(UDK') = ⊥` ＝ Saltman `cor:14.8`(a)（`C(F,n,r) ⊂ S`）。

**射程（勿夸大）**：本节**不证**那两条。`UDK'` 单与中心刻画的数学内容 ＝
Amitsur `dim_↥Z UD = n²` 的同一份（Posner／中心多项式层），**H2 仍不是无条件定理**。 -/

/-- ★★★★★★★ **PI 输入（单环形态）⟸ `UDK'` 单 ＋ 中心 ＝ `↥Z`**（AGPR `lem:1.1.16` 的实例）。 -/
theorem udkTensorSimpleHypK'_of_isSimpleRing
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hS : IsSimpleRing ↥(UDK' F r n D k₀ hk₀))
    (hZ : Subalgebra.center ↥(sprCenterImageField F r n D k₀ hk₀)
      ↥(UDK' F r n D k₀ hk₀) = ⊥) :
    UDKTensorSimpleHypK' F r n D k₀ hk₀ :=
  isSimpleRing_tensorProduct_of_center_eq_bot (F := ↥(sprCenterImageField F r n D k₀ hk₀))
    (S := ↥(UDK' F r n D k₀ hk₀)) (K := SprField F r n) hZ

#print axioms udkTensorSimpleHypK'_of_isSimpleRing

/-- ★★★★★★★★★ **H2 的最后两块**：`UDK'` 单 ＋ 中心 ＝ `↥Z` ⟹ `ProcesiS9Hyp`。 -/
theorem h2_unconditional_of_isSimpleRing (F : Type) [Field F] [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hS : IsSimpleRing ↥(UDK' F 2 9 D k₀ hk₀))
    (hZ : Subalgebra.center ↥(sprCenterImageField F 2 9 D k₀ hk₀)
      ↥(UDK' F 2 9 D k₀ hk₀) = ⊥) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_unconditional_of_simple F D k₀ hk₀
    (udkTensorSimpleHypK'_of_isSimpleRing F 2 9 D k₀ hk₀ hS hZ)

#print axioms h2_unconditional_of_isSimpleRing

/-! ## §7 ★★★★★★★★ **中心半的无条件归约**：中心元 = 标量矩阵，且 ⟺ 标量交 ⊆ `Z`

源文 `prop:14.19` 的"取中心"步（`Z = K'^N` 的手段）在 R728 起由 `H2Final` §60 的
`center_UDK'_eq` 供给，但**条件于 PI 输入** `UDKTensorHypK'`（循环）。本节把它**无条件化**：

```
Ξ 张成 M_n(K')（sprXiSpanHypK'，已机检）
  ⟹ K'·UDK' = M_n(K')                                 （span_UDK'_eq_top，无条件）
  ⟹ 中心元是标量矩阵                                   （center_mem_scalar，无条件；
      用 Matrix.center_eq_range 与"与全体矩阵交换 ⟹ 纯量"）
  ⟹ 中心 ＝ ↥Z ⟺ 标量交 ⊆ Z                            （center_eq_bot_of_scalar_mem_Z）
```

**⟹ 剩余 PI 输入从两块变成两块，但形式更sharp**：
`IsSimpleRing ↥UDK'`（真墙）＋ `ScalarMemZHypK'`（标量交 ⊆ `Z`，＝ Saltman 的
"M_n(S) ∩ K = S" 形态，其证明走中心定理 `C(F,n,r)` 的那条线）。

**射程（勿夸大）**：`ScalarMemZHypK'` **未证**；`IsSimpleRing ↥UDK'` **未证**；
`H2Final` §60 的 `center_UDK'_eq`（条件于 `hPI`）**未删**——本节给的是它的**无条件替代**
（在 `ScalarMemZHypK'` 前提下），旧件保留以备交叉核对。**H2 仍不是无条件定理**。 -/

/-- ★★★★★★ `Ξ` 张成 ⟹ `K'`-张成 `UDK' = M_n(K')`（无条件）。 -/
theorem span_UDK'_eq_top (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀) :
    Submodule.span (SprField F r n)
      (UDK' F r n D k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n))) = ⊤ := by
  classical
  have h := sprXiSpanHypK' F r n k₀ hk₀ hk
  rw [XiSpanHypK'] at h
  rw [eq_top_iff, ← h]
  exact Submodule.span_mono (by
    rintro _ ⟨p, rfl⟩
    exact xiSprK_mem_UDK' F r n D k₀ hk₀ k₀ k p.1 p.2)

#print axioms span_UDK'_eq_top

/-- ★★★★★★★ **中心元是标量矩阵**（只用满射半 `sprXiSpanHypK'`，**无条件**）。 -/
theorem center_mem_scalar (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀)
    {x : ↥(UDK' F r n D k₀ hk₀)}
    (hx : ∀ y : ↥(UDK' F r n D k₀ hk₀), x * y = y * x) :
    ∃ c : SprField F r n,
      (x : Matrix (Fin n) (Fin n) (SprField F r n)) = Matrix.scalar (Fin n) c := by
  classical
  have hcomm : ∀ y ∈ (UDK' F r n D k₀ hk₀ :
      Set (Matrix (Fin n) (Fin n) (SprField F r n))),
      y * (x : Matrix (Fin n) (Fin n) (SprField F r n))
        = (x : Matrix (Fin n) (Fin n) (SprField F r n)) * y := by
    intro y hy
    have h := hx ⟨y, hy⟩
    simpa using (congrArg Subtype.val h).symm
  have hcent : (x : Matrix (Fin n) (Fin n) (SprField F r n))
      ∈ Set.center (Matrix (Fin n) (Fin n) (SprField F r n)) := by
    rw [Semigroup.mem_center_iff]
    intro M
    have hM : M ∈ Submodule.span (SprField F r n)
        (UDK' F r n D k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n))) := by
      rw [span_UDK'_eq_top F r n D k₀ hk₀ hk]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun N (_ : N ∈ Submodule.span (SprField F r n)
        (UDK' F r n D k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n)))) =>
          N * (x : Matrix (Fin n) (Fin n) (SprField F r n))
            = (x : Matrix (Fin n) (Fin n) (SprField F r n)) * N)
      ?_ ?_ ?_ ?_ hM
    · intro y hy
      exact hcomm y hy
    · simp
    · intro a b _ _ ha hb
      rw [add_mul, mul_add, ha, hb]
    · intro c a _ ha
      rw [smul_mul_assoc, mul_smul_comm, ha]
  rw [Matrix.center_eq_range] at hcent
  obtain ⟨c, hc⟩ := hcent
  exact ⟨c, hc.symm⟩

#print axioms center_mem_scalar

/-- ★★★★★★★★ **「标量交 ⊆ `Z`」⟹ 中心 = `↥Z`**（`center_UDK'_eq` 的**无条件**版）。 -/
theorem center_eq_bot_of_scalar_mem_Z (D : GenericDivisionData F r n) (k₀ : Fin r)
    (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hscal : ∀ c : SprField F r n,
      Matrix.scalar (Fin n) c ∈ UDK' F r n D k₀ hk₀ →
        c ∈ sprCenterImageField F r n D k₀ hk₀) :
    Subalgebra.center ↥(sprCenterImageField F r n D k₀ hk₀)
      ↥(UDK' F r n D k₀ hk₀) = ⊥ := by
  classical
  refine le_antisymm ?_ bot_le
  intro x hx
  have hx' : ∀ y : ↥(UDK' F r n D k₀ hk₀), x * y = y * x := by
    intro y
    exact (Subalgebra.mem_center_iff.mp hx y).symm
  obtain ⟨c, hc⟩ := center_mem_scalar F r n D k₀ hk₀ hk hx'
  have hmem : Matrix.scalar (Fin n) c ∈ UDK' F r n D k₀ hk₀ := hc ▸ x.2
  have hcZ := hscal c hmem
  rw [Algebra.mem_bot]
  refine ⟨⟨c, hcZ⟩, ?_⟩
  apply Subtype.ext
  have h1 : algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n))
        (⟨c, hcZ⟩ : ↥(sprCenterImageField F r n D k₀ hk₀))
      = Matrix.scalar (Fin n) c := by
    rw [Matrix.algebraMap_eq_diagonal]
    rfl
  have hcoe : ((algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
      ↥(UDK' F r n D k₀ hk₀) ⟨c, hcZ⟩ : ↥(UDK' F r n D k₀ hk₀)) :
        Matrix (Fin n) (Fin n) (SprField F r n))
      = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
          (Matrix (Fin n) (Fin n) (SprField F r n)) ⟨c, hcZ⟩ := rfl
  rw [hcoe, h1, ← hc]

#print axioms center_eq_bot_of_scalar_mem_Z

/-- ★★★★★★★ **具名假设：`UDK'` 里的标量矩阵，其标量在 `Z` 里**（＝ Saltman 的
"M_n(S) ∩ K = S" 形态；中心定理的一个面）。 -/
def ScalarMemZHypK' (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) : Prop :=
  ∀ c : SprField F r n, Matrix.scalar (Fin n) c ∈ UDK' F r n D k₀ hk₀ →
    c ∈ sprCenterImageField F r n D k₀ hk₀

#print axioms ScalarMemZHypK'

/-- ★★★★★★★ **PI 输入 ⟸ `UDK'` 单 ＋ 标量交 ⊆ `Z`**（中心半现无条件）。 -/
theorem udkTensorSimpleHypK'_of_isSimpleRing_of_scalar
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀)
    (hS : IsSimpleRing ↥(UDK' F r n D k₀ hk₀))
    (hscal : ScalarMemZHypK' F r n D k₀ hk₀) :
    UDKTensorSimpleHypK' F r n D k₀ hk₀ :=
  udkTensorSimpleHypK'_of_isSimpleRing F r n D k₀ hk₀ hS
    (center_eq_bot_of_scalar_mem_Z F r n D k₀ hk₀ hk hscal)

#print axioms udkTensorSimpleHypK'_of_isSimpleRing_of_scalar

/-- ★★★★★★★★★ **H2 ⟸ `UDK'` 单 ＋ 标量交 ⊆ `Z`**（剩余两块，均按已发表定理记账）。 -/
theorem h2_unconditional_of_simple_and_scalar (F : Type) [Field F] [CharZero F]
    [Nonempty (Fin 9)] (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hS : IsSimpleRing ↥(UDK' F 2 9 D k₀ hk₀))
    (hscal : ScalarMemZHypK' F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_unconditional_of_isSimpleRing F D k₀ hk₀ hS
    (center_eq_bot_of_scalar_mem_Z F 2 9 D k₀ hk₀ (k := ⟨1, by omega⟩) (by
      intro hc
      have hval := congrArg Fin.val hc
      rw [show (⟨1, by omega⟩ : Fin 2).val = 1 from rfl, hk₀] at hval
      omega) hscal)

#print axioms h2_unconditional_of_simple_and_scalar

/-! ## §8 ★★★★★★★ **剩余 PI 输入的 mathlib 惯用形**：`IsSimpleRing ∧ Algebra.IsCentral`（＝中心单）

R733 的两条剩余输入是 `IsSimpleRing ↥UDK'` 与 `ScalarMemZHypK'`（标量交 ⊆ `Z`）。
后者与 mathlib 的 `Algebra.IsCentral ↥Z ↥UDK'`（中心 ＝ 基环；`Algebra/Central/*`）
**等价**（`center_eq_bot_of_scalar_mem_Z` 给 ⟸；`IsCentral.center_eq_bot` 给 ⟹）。

⟹ 剩余输入可**只用 mathlib 术语**陈述为一句：

```
「`UDK'` 是 `↥Z` 上的**中心单代数**」  ≡  IsSimpleRing ↥UDK'  ∧  Algebra.IsCentral ↥Z ↥UDK'
```

这正是 AGPR2020 `thm:11.3.1`(2)／Saltman `thm:14.5` 的结论（`UD` 是中心 `Z` 上除代数
⟹ 中心单），也是 Saltman `thm:14.6` 末句的结论。**⟹ 引用记账可与文献逐句对齐。**

**射程（勿夸大）**：仍**未证**；本节只做术语对齐（并用 `IsCentral.center_eq_bot`）。
**H2 仍不是无条件定理**。 -/

/-- ★★★★★★★ **PI 输入（单环形态）⟸ 「`UDK'` 是 `↥Z` 上中心单代数」**（mathlib 术语）。 -/
theorem udkTensorSimpleHypK'_of_isCentral
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hS : IsSimpleRing ↥(UDK' F r n D k₀ hk₀))
    (hZ : Algebra.IsCentral ↥(sprCenterImageField F r n D k₀ hk₀) ↥(UDK' F r n D k₀ hk₀)) :
    UDKTensorSimpleHypK' F r n D k₀ hk₀ :=
  udkTensorSimpleHypK'_of_isSimpleRing F r n D k₀ hk₀ hS hZ.center_eq_bot

#print axioms udkTensorSimpleHypK'_of_isCentral

/-- ★★★★★★★★★ **H2 ⟸ 「`UDK'` 是 `↥Z` 上中心单代数」**（AGPR `thm:11.3.1`(2)／Saltman `thm:14.5` 的结论）。 -/
theorem h2_unconditional_of_centralSimple (F : Type) [Field F] [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hS : IsSimpleRing ↥(UDK' F 2 9 D k₀ hk₀))
    (hZ : Algebra.IsCentral ↥(sprCenterImageField F 2 9 D k₀ hk₀) ↥(UDK' F 2 9 D k₀ hk₀)) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_unconditional_of_simple F D k₀ hk₀
    (udkTensorSimpleHypK'_of_isCentral F 2 9 D k₀ hk₀ hS hZ)

#print axioms h2_unconditional_of_centralSimple

end Procesi
