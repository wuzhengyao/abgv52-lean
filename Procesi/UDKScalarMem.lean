/-
  Procesi —— ★★★★★★★★★★ **`ScalarMemZHypK'` 关闭 ⟹ H2 无条件**（旁路第 4 步）

  **目标**（[[proj-abgv52-frontier-R661]] §105 第 4 步）：证 `ScalarMemZHypK'`——
  `UDK'` 里的纯量矩阵，其标量在 `Z = sprCenterImageField` 里（＝ Saltman `cor:14.8(a)`
  的 `K'` 形态，也是中心定理的一个面）。

  **数学**：`UDK'` 按定义就是 `Algebra.adjoin F (sprAlgebraK 的生成元)`，故直接对
  `Algebra.adjoin_induction` 归纳（**无需**先证 `UDK' = Z • R'_K`；该 span 恒等式
  `mem_span_sprAlgebraK_iff` 已独立机检，但本证明不消费它）。于是

  ```
  c • 1 ∈ UDK'
    ⟹ 取 0 ≠ s ∈ R_C 清分母（exists_clear_den，第 2 步）：s • (c • 1) ∈ R'_K
    ⟹ 取出 R'_K 的原像 M ∈ sprAlgebra（mem_sprAlgebraK_iff）
    ⟹ s c = ι(κ c₀)（第 1 步 mem_centerImage_of_map_eq_scalar）
    ⟹ s c ∈ R_C ⊆ Z，又 s ∈ R_C ⊆ Z、s ≠ 0、Z 是域 ⟹ c = (s c)/s ∈ Z
  ```

  **关键引理**（本件 §1）：`R'_K` 是 `R_C`-子模——
  `r ∈ R_C ⟹ scalar r ∈ R'_K`。生成元 `scalar (ι (κ c)) = ι (ψ c)` 由
  `psiSpr_center_scalar` ＋ `ψ c ∈ sprAlgebra` 给出，其余由 `R'_K` 是子代数（`Subring.closure_induction`）。

  **射程**：`ScalarMemZHypK'` **无条件**（只需 `[Field F]`）；`IsSimpleRing ↥UDK'` 与
  **`ProcesiS9Hyp F ↥(ZCanon F 2 9 D)`（H2）** 随之**无条件**。
-/

import Procesi.UDKSpan
import Procesi.UDKSimple

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Procesi

set_option synthInstance.maxHeartbeats 1000000

variable (F : Type) [Field F] (r n : ℕ)

/-! ## §1 `R_C`-纯量稳定性（`R'_K` 是 `R_C`-子模） -/

/-- `Matrix.scalar x = x • 1`。 -/
theorem scalar_eq_smul_one (x : SprField F r n) :
    Matrix.scalar (Fin n) x = x • (1 : Matrix (Fin n) (Fin n) (SprField F r n)) := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.smul_apply, hij]

#print axioms scalar_eq_smul_one

/-- `R_C ⊆ Z`。 -/
theorem sprCenterImageSubring_le_field [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (sprCenterImageSubring F r n D k₀ hk₀ : Set (SprField F r n))
      ⊆ (sprCenterImageField F r n D k₀ hk₀ : Set (SprField F r n)) := by
  intro x hx
  rw [sprCenterImageField_eq_adjoin_subring]
  exact IntermediateField.subset_adjoin F _ hx

#print axioms sprCenterImageSubring_le_field

/-- `algebraMap ↥Z (Matrix) z = scalar z`。 -/
theorem algebraMap_Z_eq_scalar [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(sprCenterImageField F r n D k₀ hk₀)) :
    algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
        (Matrix (Fin n) (Fin n) (SprField F r n)) z
      = Matrix.scalar (Fin n) (z : SprField F r n) := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  rfl

#print axioms algebraMap_Z_eq_scalar

/-- ★ **`r ∈ R_C ⟹ scalar r ∈ R'_K`**（生成元 `scalar (ι(κ c)) = ι(ψ c)`）。 -/
theorem scalar_mem_sprAlgebraK_of_mem_subring [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {x : SprField F r n} (hx : x ∈ sprCenterImageSubring F r n D k₀ hk₀) :
    Matrix.scalar (Fin n) x ∈ sprAlgebraK F r n k₀ hk₀ := by
  classical
  obtain ⟨L, hFld, hAlg, θ, hθinj, d, hθ⟩ := exists_algHom_diagonal_genMatKF F r n k₀
  letI : Field L := hFld
  letI : Algebra (SField F r n) L := hAlg
  letI : Algebra F L :=
    (algebraMap (SField F r n) L).comp (algebraMap F (SField F r n)) |>.toAlgebra
  haveI : IsScalarTower F (SField F r n) L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  rw [sprCenterImageSubring] at hx
  refine Subring.closure_induction (p := fun y _ =>
    Matrix.scalar (Fin n) y ∈ sprAlgebraK F r n k₀ hk₀) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro y ⟨c, rfl⟩
    refine (mem_sprAlgebraK_iff F r n k₀ hk₀).mpr
      ⟨psiSpr F r n k₀ hk₀ (c : ↥(genericMatrixAlgebra F r n)),
        psiSpr_mem_sprAlgebra F r n k₀ hk₀ θ hθ _, ?_⟩
    exact psiSpr_center_scalar F r n D k₀ hk₀ c
  · rw [RingHom.map_zero (Matrix.scalar (Fin n))]
    exact (sprAlgebraK F r n k₀ hk₀).zero_mem
  · rw [RingHom.map_one (Matrix.scalar (Fin n))]
    exact (sprAlgebraK F r n k₀ hk₀).one_mem
  · intro y z _ _ ihy ihz
    rw [RingHom.map_add (Matrix.scalar (Fin n))]
    exact (sprAlgebraK F r n k₀ hk₀).add_mem ihy ihz
  · intro y _ ihy
    have hneg : Matrix.scalar (Fin n) (-y) = -(Matrix.scalar (Fin n) y) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [hneg]
    exact (sprAlgebraK F r n k₀ hk₀).neg_mem ihy
  · intro y z _ _ ihy ihz
    rw [RingHom.map_mul (Matrix.scalar (Fin n))]
    exact (sprAlgebraK F r n k₀ hk₀).mul_mem ihy ihz

#print axioms scalar_mem_sprAlgebraK_of_mem_subring

/-- ★ **`R_C`-纯量乘不动 `R'_K`**。 -/
theorem smul_mem_sprAlgebraK_of_mem_subring [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (z : ↥(sprCenterImageField F r n D k₀ hk₀))
    (hz : (z : SprField F r n) ∈ sprCenterImageSubring F r n D k₀ hk₀)
    (a : Matrix (Fin n) (Fin n) (SprField F r n))
    (ha : a ∈ sprAlgebraK F r n k₀ hk₀) :
    z • a ∈ sprAlgebraK F r n k₀ hk₀ := by
  have h1 := algebraMap_Z_eq_scalar F r n D k₀ hk₀ z
  have h2 : z • a = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n)) z * a := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
  rw [h2, h1]
  exact (sprAlgebraK F r n k₀ hk₀).mul_mem
    (scalar_mem_sprAlgebraK_of_mem_subring F r n D k₀ hk₀ hz) ha

#print axioms smul_mem_sprAlgebraK_of_mem_subring

/-! ## §2 清分母 ＋ 装配：`ScalarMemZHypK'` -/

/-- ★★★★ **旁路第 4 步**：`UDK'` 里的纯量矩阵，其标量在 `Z` 里。 -/
theorem scalarMemZHypK' [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ScalarMemZHypK' F r n D k₀ hk₀ := by
  classical
  intro c hc
  have hc1 : c • (1 : Matrix (Fin n) (Fin n) (SprField F r n))
      ∈ UDK' F r n D k₀ hk₀ := by
    rw [← scalar_eq_smul_one]
    exact hc
  -- 清分母：`∃ 0 ≠ s ∈ R_C, s • x ∈ R'_K`
  have key : ∀ x ∈ Algebra.adjoin ↥(sprCenterImageField F r n D k₀ hk₀)
      (Set.range (fun k : Fin r =>
        (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
          (algebraMap (Spr F r n) (SprField F r n)))),
      ∃ s : ↥(sprCenterImageField F r n D k₀ hk₀),
        (s : SprField F r n) ∈ sprCenterImageSubring F r n D k₀ hk₀ ∧
        (s : SprField F r n) ≠ 0 ∧ s • x ∈ sprAlgebraK F r n k₀ hk₀ := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ =>
      ∃ s : ↥(sprCenterImageField F r n D k₀ hk₀),
        (s : SprField F r n) ∈ sprCenterImageSubring F r n D k₀ hk₀ ∧
        (s : SprField F r n) ≠ 0 ∧ s • x ∈ sprAlgebraK F r n k₀ hk₀) ?_ ?_ ?_ ?_ hx
    · rintro a ⟨k, rfl⟩
      exact ⟨1, (sprCenterImageSubring F r n D k₀ hk₀).one_mem, one_ne_zero,
        by simpa using gen_mem_sprAlgebraK F r n k₀ hk₀ k⟩
    · intro z
      obtain ⟨t, htRC, ht0, htz⟩ := exists_clear_den F r n D k₀ hk₀ z.2
      have hZt : t ∈ (sprCenterImageField F r n D k₀ hk₀ : Set (SprField F r n)) :=
        sprCenterImageSubring_le_field F r n D k₀ hk₀ htRC
      refine ⟨⟨t, hZt⟩, htRC, ht0, ?_⟩
      have h1 : (⟨t, hZt⟩ : ↥(sprCenterImageField F r n D k₀ hk₀)) •
          algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
            (Matrix (Fin n) (Fin n) (SprField F r n)) z
          = Matrix.scalar (Fin n) (t * (z : SprField F r n)) := by
        rw [Algebra.smul_def, ← map_mul, algebraMap_Z_eq_scalar]
        rfl
      rw [h1]
      exact scalar_mem_sprAlgebraK_of_mem_subring F r n D k₀ hk₀ htz
    · intro a b _ _ iha ihb
      obtain ⟨s, hs, hs0, h1⟩ := iha
      obtain ⟨t, ht, ht0, h2⟩ := ihb
      refine ⟨s * t, ?_, ?_, ?_⟩
      · show (s : SprField F r n) * (t : SprField F r n)
          ∈ sprCenterImageSubring F r n D k₀ hk₀
        exact (sprCenterImageSubring F r n D k₀ hk₀).mul_mem hs ht
      · show (s : SprField F r n) * (t : SprField F r n) ≠ 0
        exact mul_ne_zero hs0 ht0
      · have heq : (s * t) • (a + b) = t • (s • a) + s • (t • b) := by
          rw [smul_add, ← smul_smul, ← smul_smul, smul_comm s t a]
        rw [heq]
        exact (sprAlgebraK F r n k₀ hk₀).add_mem
          (smul_mem_sprAlgebraK_of_mem_subring F r n D k₀ hk₀ t ht (s • a) h1)
          (smul_mem_sprAlgebraK_of_mem_subring F r n D k₀ hk₀ s hs (t • b) h2)
    · intro a b _ _ iha ihb
      obtain ⟨s, hs, hs0, h1⟩ := iha
      obtain ⟨t, ht, ht0, h2⟩ := ihb
      refine ⟨s * t, ?_, ?_, ?_⟩
      · show (s : SprField F r n) * (t : SprField F r n)
          ∈ sprCenterImageSubring F r n D k₀ hk₀
        exact (sprCenterImageSubring F r n D k₀ hk₀).mul_mem hs ht
      · show (s : SprField F r n) * (t : SprField F r n) ≠ 0
        exact mul_ne_zero hs0 ht0
      · have heq : (s * t) • (a * b) = (s • a) * (t • b) := by
          rw [← smul_smul s t (a * b), ← Matrix.mul_smul a t b,
            ← Matrix.smul_mul s a (t • b)]
        rw [heq]
        exact (sprAlgebraK F r n k₀ hk₀).mul_mem h1 h2
  have hmem : c • (1 : Matrix (Fin n) (Fin n) (SprField F r n))
      ∈ Algebra.adjoin ↥(sprCenterImageField F r n D k₀ hk₀)
        (Set.range (fun k : Fin r =>
          (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
            (algebraMap (Spr F r n) (SprField F r n)))) := hc1
  obtain ⟨s, hsRC, hs0, hsmem⟩ := key _ hmem
  have hsc : s • (c • (1 : Matrix (Fin n) (Fin n) (SprField F r n)))
      = Matrix.scalar (Fin n) ((s : SprField F r n) * c) := by
    have htower : s • (c • (1 : Matrix (Fin n) (Fin n) (SprField F r n)))
        = (s : SprField F r n) • (c • (1 : Matrix (Fin n) (Fin n) (SprField F r n))) :=
      (IsScalarTower.algebraMap_smul (R := ↥(sprCenterImageField F r n D k₀ hk₀))
        (A := SprField F r n) s _).symm
    rw [htower, smul_smul, ← scalar_eq_smul_one]
  obtain ⟨M, hM, hMι⟩ := (mem_sprAlgebraK_iff F r n k₀ hk₀).mp hsmem
  have hMeq : M.map (algebraMap (Spr F r n) (SprField F r n))
      = Matrix.scalar (Fin n) ((s : SprField F r n) * c) := by
    rw [hMι, hsc]
  obtain ⟨c₀, hc₀⟩ := mem_centerImage_of_map_eq_scalar F r n D k₀ hk₀ hM hMeq
  have hscZ : (s : SprField F r n) * c ∈ sprCenterImageField F r n D k₀ hk₀ := by
    rw [hc₀]
    exact sprCenterK_mem_sprCenterImageField F r n D k₀ hk₀ c₀
  have hsZ : (s : SprField F r n) ∈ sprCenterImageField F r n D k₀ hk₀ :=
    sprCenterImageSubring_le_field F r n D k₀ hk₀ hsRC
  have hceq : (s : SprField F r n) * c * (s : SprField F r n)⁻¹ = c := by
    rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  rw [← hceq]
  exact mul_mem hscZ (inv_mem hsZ)

#print axioms scalarMemZHypK'

/-! ## §3 收口：`IsSimpleRing ↥UDK'` 与 **H2** 无条件 -/

/-- ★★★★★★★★ **`IsSimpleRing ↥UDK'` 无条件**（`ScalarMemZHypK'` 已关闭）。 -/
theorem isSimpleRing_UDK' [Nonempty (Fin n)] [NeZero n]
    (hn : 1 ≤ n) (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (k : Fin r) (hk : k ≠ k₀) :
    IsSimpleRing ↥(UDK' F r n D k₀ hk₀) :=
  isSimpleRing_UDK'_of_scalarMem F r n hn D k₀ hk₀ k hk
    (scalarMemZHypK' F r n D k₀ hk₀)

#print axioms isSimpleRing_UDK'

/-- ★★★★★★★★★★ **H2 无条件**：`ProcesiS9Hyp F ↥(ZCanon F 2 9 D)`。

`ScalarMemZHypK'` 已无条件（本件 `scalarMemZHypK'`），故 `h2_of_scalarMem` 直接给出。
源文口径：`Procesi` 定理在 `n = 9`、`r = 2`、ABGV 的 `S_9`-格下的特化。 -/
theorem h2_unconditional [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_of_scalarMem F D k₀ hk₀ (scalarMemZHypK' F 2 9 D k₀ hk₀)

#print axioms h2_unconditional

end Procesi
