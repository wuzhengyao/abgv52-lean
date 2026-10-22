/-
  Procesi —— **`Ω = S₉/S₈` 的 `S₉`-集同构**（提示词 §2.1 第 1 项的最后一块）

  论文 `raw/ABGV-5.2-resolution.pre44.tex:668–672` 逐字：
  > Let `n = 9` and let `Ω = S₉/S₈` be the set of left cosets of `S₈` in `S₉`.
  > Then `|Ω| = 9` and `S₉` acts on `Ω` by left multiplication.

  工程侧的 `Ω` 是 `G.OmegaP 3 = Fin 9`（带 `Equiv.Perm (Fin 9)` 的自然作用）。本件机检
  **两者是同一个 `S₉`-集**：

    `S₈ := MulAction.stabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9)`（＝固定一点的置换，
    即论文的 `S_{n-1}`）；`S₉` 在 `Fin 9` 上传递（`perm_transitive`）⟹
    轨道-稳定子给出 `S₉`-集同构 `Fin 9 ≃ S₉ ⧸ S₈`（`omegaEquivQuotient`），
    且显式等变：`φ (h • x) = h • φ x`（`omegaEquivQuotient_smul`）。

  **⟹ 提示词 §2.1 第 1 项"`Ω = S_9/S_8`"在集合层机检闭合**；`Rep` 层的搬运
  （`ℤ[Fin 9] ≅ ℤ[S₉⧸S₈]` 作为 `Rep ℤ S₉`）是沿本同构的 Finsupp 搬运，登记为后续件。
-/
import Procesi.Lattice

open ABGV52

namespace Procesi

noncomputable section

/-- **`S₈ ⊆ S₉`**：`S₉` 中固定 `0 : Fin 9` 的稳定子（＝论文的 `S_{n-1}`）。 -/
def S8 : Subgroup (Equiv.Perm (Fin 9)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9)

/-- `S₉` 在 `Fin 9` 上**传递**（`swap` 把一个点送到任一点）。 -/
theorem perm_transitive (x : Fin 9) : ∃ g : Equiv.Perm (Fin 9), g • (0 : Fin 9) = x := by
  by_cases h : x = 0
  · exact ⟨1, by rw [h]; simp⟩
  · refine ⟨Equiv.swap (0 : Fin 9) x, ?_⟩
    show Equiv.swap (0 : Fin 9) x 0 = x
    rw [Equiv.swap_apply_left]

/-- `0` 的轨道是全集（传递性的等价形）。 -/
theorem orbit_eq_top : MulAction.orbit (Equiv.Perm (Fin 9)) (0 : Fin 9) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [MulAction.mem_orbit_iff]
  exact perm_transitive x

/-- ★ **`Ω = S₉/S₈`（集合层）**：`Fin 9 ≃ S₉ ⧸ S₈`（轨道-稳定子 ＋ 轨道为全集）。 -/
def omegaEquivQuotient : Fin 9 ≃ (Equiv.Perm (Fin 9) ⧸ S8) where
  toFun x := MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9)
    ⟨x, by rw [orbit_eq_top]; trivial⟩
  invFun q := ((MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9))
    (0 : Fin 9)).symm q).1
  left_inv x := by
    show ((MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9)).symm
      ((MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9))
        ⟨x, by rw [orbit_eq_top]; trivial⟩)).1 = x
    rw [Equiv.symm_apply_apply]
  right_inv q := by
    show MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9) _ = q
    exact Equiv.apply_symm_apply _ q

/-- 显式公式：`φ (g • 0) = ⟦g⟧`。 -/
theorem omegaEquivQuotient_smul_zero (g : Equiv.Perm (Fin 9)) :
    omegaEquivQuotient (g • (0 : Fin 9)) = QuotientGroup.mk g := by
  have h1 : (MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9)).symm
      (QuotientGroup.mk g) = ⟨g • (0 : Fin 9), by rw [orbit_eq_top]; trivial⟩ :=
    Subtype.ext (MulAction.orbitEquivQuotientStabilizer_symm_apply
      (Equiv.Perm (Fin 9)) (0 : Fin 9) g)
  show (MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9))
      ⟨g • (0 : Fin 9), by rw [orbit_eq_top]; trivial⟩ = QuotientGroup.mk g
  rw [← h1, Equiv.apply_symm_apply]

/-- ★★ **`Ω = S₉/S₈` 是 `S₉`-集同构**（论文 `sec:procesi` 段）：`φ (h • x) = h • φ x`。

**用途**：这是把论文的 `Ω = S₉/S₈`（左陪集空间）与工程的 `Ω = Fin 9`
（`Equiv.Perm (Fin 9)` 的自然作用）**同一**的机检依据；`U = ℤ[Ω]` 的两种写法
沿此同构是同一个 `Rep ℤ S₉`（`Rep` 层搬运见后续件）。 -/
theorem omegaEquivQuotient_smul (h : Equiv.Perm (Fin 9)) (x : Fin 9) :
    omegaEquivQuotient (h • x) = h • omegaEquivQuotient x := by
  obtain ⟨g, rfl⟩ := perm_transitive x
  rw [← mul_smul, omegaEquivQuotient_smul_zero, omegaEquivQuotient_smul_zero]
  rfl

/-- 类型锁：`S8` 就是 `0 : Fin 9` 的稳定子（论文 `S₈ = S_{n-1}` 的机器形式）。 -/
theorem S8_typeLock :
    (S8 : Subgroup (Equiv.Perm (Fin 9))) =
      MulAction.stabilizer (Equiv.Perm (Fin 9)) (0 : Fin 9) := rfl

/-! ## 公理闸门 -/

#print axioms S8_typeLock
#print axioms perm_transitive
#print axioms orbit_eq_top
#print axioms omegaEquivQuotient
#print axioms omegaEquivQuotient_smul_zero
#print axioms omegaEquivQuotient_smul

end

end Procesi
