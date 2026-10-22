/-
  Procesi —— ★★★★★★★ **E 计划收口：`IsSimpleRing ↥UDK'` ⟸ `ScalarMemZHypK'`**（H2 的最后一块）

  **链**（v48 判读的落点，[[proj-abgv52-frontier-R661]] §103）：

  ```
  H2 = ProcesiS9Hyp F ↥(ZCanon F 2 9 D)
    ⟸ h2_unconditional_of_simple_and_scalar（KPrime1424Assembly:537）
        = IsSimpleRing ↥UDK' ＋ ScalarMemZHypK'
    ⟸ 【本件】IsSimpleRing ↥UDK' ⟸ ScalarMemZHypK'
    ⟸ ★ 单一具名输入 = ScalarMemZHypK'
  ```

  **机制**（AGPR2020 `cor:11.2.7` 的自足版，**不用**"中心多项式对任意 `X` 中心"）：
  1. `udk'_ideal_inf_scalars`：`UDK'` 的非零双边理想 `I` 含非零纯量 `c • 1`（`c ≠ 0`）——
     用见证元 `D = (xdiag).map (algebraMap)`（对角、对角元互异，`sprDiagVal_injective`）、
     `PI/CentralIdeal.lean` 的 `exists_scalar_mem_of_ne_bot`、`UDKIdeal.lean` 的
     `udk'_span_eq_top` 与 `formanekGGen_witness_ne_zero`；
  2. `isSimpleRing_UDK'_of_scalarMem`：`ScalarMemZHypK'` 给 `c ∈ Z`，`Z` 是域 ⟹ `c⁻¹ • 1 ∈ UDK'`
     ⟹ 理想含单位 ⟹ `I = ⊤`；
  3. `h2_of_scalarMem`：与现成的 `h2_unconditional_of_simple_and_scalar` 复合。
-/

import Procesi.H2Final
import Procesi.UDKIdeal
import Procesi.PI.CentralIdeal
import Procesi.KPrime1424Assembly

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Procesi

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable (F : Type) [Field F] (r n : ℕ)

set_option maxHeartbeats 1000000 in
/-- ★★★★ **非零双边理想含非零纯量**（`UDK'` 侧；对角见证元 `xdiag`）。 -/
theorem udk'_ideal_inf_scalars [NeZero n] [Nonempty (Fin n)] (hn : 1 ≤ n)
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (I : TwoSidedIdeal ↥(UDK' F r n D k₀ hk₀)) (hI : I ≠ ⊥) :
    ∃ z : ↥(UDK' F r n D k₀ hk₀), z ∈ I ∧ z ≠ 0 ∧
      ∃ c : SprField F r n, c ≠ 0 ∧
        (Subalgebra.val (UDK' F r n D k₀ hk₀) z) = c • (1 : Matrix (Fin n) (Fin n) (SprField F r n)) := by
  have hspanA := udk'_span_eq_top F r n D k₀ hk₀ hk
  refine exists_scalar_mem_of_ne_bot (A := UDK' F r n D k₀ hk₀) (k := SprField F r n) (N := n)
    (x := sprDiagVal F r n) hn (sprDiagVal_injective F r n) hspanA
    ⟨(xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)), xdiag_map_mem_UDK' F r n D k₀ hk₀⟩
    (xdiag_map_eq_diagonal_sprDiagVal F r n) I hI

#print axioms udk'_ideal_inf_scalars

set_option maxHeartbeats 1000000 in
/-- ★★★★★★★ **`IsSimpleRing ↥UDK'` ⟸ `ScalarMemZHypK'`**（E 计划的收口）。 -/
theorem isSimpleRing_UDK'_of_scalarMem [NeZero n] [Nonempty (Fin n)] (hn : 1 ≤ n)
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) (k : Fin r) (hk : k ≠ k₀)
    (hscal : ScalarMemZHypK' F r n D k₀ hk₀) :
    IsSimpleRing ↥(UDK' F r n D k₀ hk₀) := by
  classical
  haveI : Nontrivial ↥(UDK' F r n D k₀ hk₀) := by
    refine ⟨1, 0, fun h => ?_⟩
    have h1 : Subalgebra.val (UDK' F r n D k₀ hk₀) (1 : ↥(UDK' F r n D k₀ hk₀))
        = Subalgebra.val (UDK' F r n D k₀ hk₀) (0 : ↥(UDK' F r n D k₀ hk₀)) := by rw [h]
    rw [map_one, map_zero] at h1
    exact one_ne_zero h1
  refine IsSimpleRing.of_eq_bot_or_eq_top (fun I => ?_)
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    obtain ⟨z, hzI, hz0, c, hc0, hzval⟩ := udk'_ideal_inf_scalars F r n hn D k₀ hk₀ hk I hI
    -- `c ∈ Z`（`ScalarMemZHypK'`）
    have hscal' : Matrix.scalar (Fin n) c ∈ UDK' F r n D k₀ hk₀ := by
      have hscalar : Matrix.scalar (Fin n) c
          = c • (1 : Matrix (Fin n) (Fin n) (SprField F r n)) := by
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, hij]
      rw [hscalar, ← hzval]
      exact z.2
    have hcZ : c ∈ sprCenterImageField F r n D k₀ hk₀ := hscal c hscal'
    -- 逆元（`c⁻¹ • 1 ∈ A`，因为 `A` 是 `Z`-子代数）
    have hcZinv : c⁻¹ ∈ sprCenterImageField F r n D k₀ hk₀ :=
      (sprCenterImageField F r n D k₀ hk₀).inv_mem hcZ
    have hmem' : c⁻¹ • (1 : Matrix (Fin n) (Fin n) (SprField F r n))
        ∈ UDK' F r n D k₀ hk₀ := by
      have h := Subalgebra.algebraMap_mem (UDK' F r n D k₀ hk₀)
        (⟨c⁻¹, hcZinv⟩ : ↥(sprCenterImageField F r n D k₀ hk₀))
      rwa [Algebra.algebraMap_eq_smul_one] at h
    obtain ⟨z', hz'⟩ : ∃ w : ↥(UDK' F r n D k₀ hk₀),
        Subalgebra.val (UDK' F r n D k₀ hk₀) w
          = c⁻¹ • (1 : Matrix (Fin n) (Fin n) (SprField F r n)) :=
      ⟨⟨_, hmem'⟩, rfl⟩
    -- 单位 ⟹ `1 ∈ I`
    have hunit : z * z' = 1 := by
      apply Subtype.ext
      show Subalgebra.val (UDK' F r n D k₀ hk₀) (z * z') = 1
      rw [map_mul, hzval, hz', Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        mul_inv_cancel₀ hc0, one_smul]
    have h1mem : (1 : ↥(UDK' F r n D k₀ hk₀)) ∈ I := by
      rw [← hunit]
      exact I.mul_mem_right z z' hzI
    exact (TwoSidedIdeal.one_mem_iff I).mp h1mem

#print axioms isSimpleRing_UDK'_of_scalarMem

set_option maxHeartbeats 1000000 in
/-- ★★★★★★★★★★ **H2 ⟸ `ScalarMemZHypK'`**（R769 起的目标：单一具名输入）。 -/
theorem h2_of_scalarMem [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hscal : ScalarMemZHypK' F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_unconditional_of_simple_and_scalar F D k₀ hk₀
    (isSimpleRing_UDK'_of_scalarMem F 2 9 (by norm_num) D k₀ hk₀ ⟨1, by norm_num⟩ (by
      intro hc
      have hval := congrArg Fin.val hc
      rw [show (⟨1, by norm_num⟩ : Fin 2).val = 1 from rfl, hk₀] at hval
      omega) hscal)
    hscal

#print axioms h2_of_scalarMem


end Procesi
