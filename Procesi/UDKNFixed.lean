/-
  Procesi —— ★★★★★ **H2 ⟸ "Z 半"**（`sprNFixedField ≤ sprCenterImageField`）：单一**域论**输入

  **链**（R770 之后的新台阶）：

  ```
  H2
    ⟸ IsSimpleRing ↥UDK' ＋ ScalarMemZHypK'        （h2_unconditional_of_simple_and_scalar）
    ⟸ ScalarMemZHypK'                              （R770：isSimpleRing_UDK'_of_scalarMem）
    ⟸ sprNFixedField ≤ Z                          ★【本件】scalarMemZHypK'_of_nfixed_le
  ```

  **机制**（本件的四件）：
  1. `sprFieldNFixed_of_scalar_mem_UDK'`：`UDK' ⊆ M_n(K')^N`（`UDK'_le_sprMatNFixedAlg`，机检）
     ＋ 作用在纯量矩阵上只作用在标量上（`sprPsiDK_scalar`／`sprPsiSK_scalar`）
     ⟹ `c • 1 ∈ UDK'` ⟹ `c` 被 `T` 与 `S_n` 都固定 ⟹ `sprFieldNFixed c`；
  2. `scalarMemZHypK'_of_nfixed_le`：再套 `mem_sprNFixedField_iff` ＋ 假设 `sprNFixedField ≤ Z`；
  3-4. `isSimpleRing_UDK'_of_nfixed_le`／**`h2_of_nfixed_le`**：与 R770 的两件复合。

  **⟹ 输入清单收缩**：`hS`／`ScalarMemZHypK'` 都不再是具名输入；H2 只余**一个域论命题**
  "`K'` 的 `N`-固定点都在 `Z = Frac(κ(C))` 里"（本仓 `sprNFixedField` 一族机器的主攻目标）。
-/

import Procesi.H2Final
import Procesi.UDKSimple

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Procesi

set_option synthInstance.maxHeartbeats 1000000

variable (F : Type) [Field F] (r n : ℕ)

set_option maxHeartbeats 1000000 in
/-- ★★★★ **`UDK'` 里的纯量矩阵，其标量是 `N`-固定的**。 -/
theorem sprFieldNFixed_of_scalar_mem_UDK' [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {c : SprField F r n} (hc : Matrix.scalar (Fin n) c ∈ UDK' F r n D k₀ hk₀) :
    sprFieldNFixed F r n c := by
  classical
  -- 纯量矩阵 `N`-固定
  have hN : sprMatNFixed F r n (Matrix.scalar (Fin n) c) :=
    UDK'_le_sprMatNFixedAlg F r n D k₀ hk₀ hc
  constructor
  · -- `T` 部分
    intro b
    have h1 := hN.1 b
    rw [sprPsiDK_scalar] at h1
    -- `scalar (φ_b c) = scalar c` ⟹ `φ_b c = c`
    exact Matrix.scalar_inj.mp h1
  · -- `S_n` 部分
    intro σ
    have h2 := hN.2 σ
    rw [sprPsiSK_scalar] at h2
    exact Matrix.scalar_inj.mp h2

#print axioms sprFieldNFixed_of_scalar_mem_UDK'

set_option maxHeartbeats 1000000 in
/-- ★★★★ **`ScalarMemZHypK'` ⟸ Z 半**（`sprNFixedField ≤ sprCenterImageField`）。 -/
theorem scalarMemZHypK'_of_nfixed_le [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F r n ≤ sprCenterImageField F r n D k₀ hk₀) :
    ScalarMemZHypK' F r n D k₀ hk₀ := by
  intro c hc
  exact hZ ((mem_sprNFixedField_iff (F := F) (r := r) (n := n)).mpr
    (sprFieldNFixed_of_scalar_mem_UDK' F r n D k₀ hk₀ hc))

#print axioms scalarMemZHypK'_of_nfixed_le

set_option maxHeartbeats 1000000 in
/-- ★★★★★★ **`IsSimpleRing ↥UDK'` ⟸ Z 半**。 -/
theorem isSimpleRing_UDK'_of_nfixed_le [NeZero n] [Nonempty (Fin n)] (hn : 1 ≤ n)
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hZ : sprNFixedField F r n ≤ sprCenterImageField F r n D k₀ hk₀) :
    IsSimpleRing ↥(UDK' F r n D k₀ hk₀) :=
  isSimpleRing_UDK'_of_scalarMem F r n hn D k₀ hk₀ k hk
    (scalarMemZHypK'_of_nfixed_le F r n D k₀ hk₀ hZ)

#print axioms isSimpleRing_UDK'_of_nfixed_le

set_option maxHeartbeats 1000000 in
/-- ★★★★★★★★★★ **H2 ⟸ Z 半**（`∀ x, sprFieldNFixed x → x ∈ Z`）：单一**域论**输入。 -/
theorem h2_of_nfixed_le [CharZero F] [Nonempty (Fin 9)]
    (D : GenericDivisionData F 2 9) (k₀ : Fin 2) (hk₀ : k₀.val = 0)
    (hZ : sprNFixedField F 2 9 ≤ sprCenterImageField F 2 9 D k₀ hk₀) :
    ProcesiS9Hyp F ↥(ZCanon F 2 9 D) :=
  h2_unconditional_of_simple_and_scalar F D k₀ hk₀
    (isSimpleRing_UDK'_of_nfixed_le F 2 9 (by norm_num) D k₀ hk₀
      (k := ⟨1, by norm_num⟩) (by
        intro hc
        have hval := congrArg Fin.val hc
        rw [show (⟨1, by norm_num⟩ : Fin 2).val = 1 from rfl, hk₀] at hval
        omega)
      hZ)
    (scalarMemZHypK'_of_nfixed_le F 2 9 D k₀ hk₀ hZ)

#print axioms h2_of_nfixed_le


end Procesi
