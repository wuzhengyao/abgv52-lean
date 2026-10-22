/-
  Procesi —— **`UDK'` 侧的 E 计划夹具**（`span = ⊤` ＋ 对角见证元）

  三件（AGPR2020 `cor:11.2.7` 在本工程的 `K'` 世界所需）：
  1. `udk'_span_eq_top`：`UDK'` 的 `K'`-张成 = `⊤`（`sprXiSpanHypK'`（`H2Final` §98，**定理**）
     ＋ `xiSprK_mem_UDK'`）；
  2. `xdiag_map_mem_UDK'` ＋ `xdiag_map_eq_diagonal_sprDiagVal`：见证元 `D = (xdiag).map (algebraMap)`
     在 `UDK'` 里且 `= Matrix.diagonal (sprDiagVal)`（对角元互异：`sprDiagVal_injective`）；
  3. `formanekGGen_witness_ne_zero`：`G(D, 链单位族) ≠ 0`（非零性的见证）。
-/

import Procesi.H2Final
import Procesi.PI.CentralIdeal

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Procesi

variable (F : Type) [Field F] (r n : ℕ)

set_option maxHeartbeats 1000000 in
/-- ★★★★★ **`UDK'` 的 `K'`-张成是 `⊤`**（`Ξ` 张成 ⟹ 生成元所在的子代数张成）。 -/
theorem udk'_span_eq_top [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {k : Fin r} (hk : k ≠ k₀) :
    Submodule.span (SprField F r n)
      (UDK' F r n D k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n))) = ⊤ := by
  have hspan := sprXiSpanHypK' (F := F) (r := r) (n := n) k₀ hk₀ hk
  unfold XiSpanHypK' at hspan
  have hle : Submodule.span (SprField F r n)
        (Set.range (fun p : Fin n × Fin n => xiSprK F r n k₀ hk₀ k₀ k p.1 p.2))
      ≤ Submodule.span (SprField F r n)
        (UDK' F r n D k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n))) :=
    Submodule.span_mono (by
      rintro x ⟨p, rfl⟩
      exact xiSprK_mem_UDK' F r n D k₀ hk₀ k₀ k p.1 p.2)
  rw [hspan] at hle
  exact top_le_iff.mp hle

#print axioms udk'_span_eq_top

/-- ★★★ **对角见证元在 `UDK'` 里**：`(xdiag).map (algebraMap) ∈ UDK'`。 -/
theorem xdiag_map_mem_UDK' [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n)) ∈ UDK' F r n D k₀ hk₀ := by
  have h := psiSpr_mem_UDK' F r n D k₀ hk₀ k₀
  rw [psiSpr_genMat_self (F := F) (r := r) (n := n) k₀ hk₀] at h
  exact h

#print axioms xdiag_map_mem_UDK'

/-- `(xdiag).map (algebraMap)` 就是 `Matrix.diagonal (sprDiagVal)`（对角元 = `sprDiagVal`）。 -/
theorem xdiag_map_eq_diagonal_sprDiagVal :
    (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n))
      = Matrix.diagonal (sprDiagVal F r n) := by
  rw [xdiag, Matrix.diagonal_map (map_zero _)]
  rfl

#print axioms xdiag_map_eq_diagonal_sprDiagVal

/-- ★★★★ **见证值非零**：`G(D, 链单位族) ≠ 0`（`D` 的对角元互异）。 -/
theorem formanekGGen_witness_ne_zero [NeZero n] (hn : 1 ≤ n) :
    formanekGGen n (gPoly (SprField F r n) n)
        (Matrix.diagonal (sprDiagVal F r n))
        (fun i : Fin n => Matrix.single i (i + 1) (1 : SprField F r n)) ≠ 0 := by
  have : IsDomain (SprField F r n) := inferInstance
  exact formanekGGen_units_ne_zero (K := SprField F r n) n hn
    (x := sprDiagVal F r n) (sprDiagVal_injective F r n)

#print axioms formanekGGen_witness_ne_zero


end Procesi
