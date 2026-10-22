/-
  Procesi —— **(A)+(B) S2b 的终点：`lem:14.12` 机检**

  **原文（逐字）**：`raw/Saltman1999ch14.tex` `lem:14.12`：
  > Assume `n>1`. Suppose `γ : PGL_n(F) → A` is a group homomorphism into an abelian group
  > `A` (written multiplicatively). Then `γ(α)^n = 1` for all `α ∈ PGL_n(F)`.

  **本件**：`pgl_pow_n_eq_one`（`n ≥ 3`；见下"射程"）。

  **证明结构**（三步，全部用库内件，零消元归纳）：
  1. `gT := γ ∘ mk`（`mk : GL_n(F) →* PGL_n(F)`）在**换位子群**上平凡：
     `A` 交换 ⟹ `map gT ⁅⊤,⊤⁆ = ⁅⊤,⊤⁆ = ⊥`（`Subgroup.map_commutator`
     ＋ `Subgroup.commutator_self_eq_bot_iff`）；
  2. `gT` 在**纯量**上平凡（`ProjGenLinGroup.mk_scalar`）且在 `SL_n` 上平凡
     （`SLGen.lean` 的 `sl_mem_commutator`：`SL_n ⊆ [GL_n,GL_n]`）；
  3. `g^n = (det g • 1) * s`（`s ∈ SL_n`，因两者行列式同为 `(det g)^n`）⟹
     `γ(α)^n = gT(g^n) = gT(det g • 1) * gT(s) = 1`。

  **射程（如实登记）**：本件要求 `n ≥ 3`（`sl_mem_commutator` 需第三下标 `k ∉ {i,j}`）；
  原文的 `n > 1` 中 **`n = 2` 尚未机检**——`SL_2 ⊆ [GL_2,GL_2]` 在 `|F| ≤ 3` 时失效
  （mathlib 的 `SL2.commutator_eq_top` 需 `∃ a, a ≠ 0 ∧ a² ≠ 1`），`F₂`／`F₃` 须另证；
  已登记于 `wiki/proj-AB-formalization-plan.md` §2b·丁。本战役（Saltman Ch.14 的 (A)+(B)）
  的用法只经 `lem:14.13` 的 `λ^n = 1`，`n ≥ 3` 的情形覆盖 `n = 9`（ABGV-5.2／H2 所需）。
-/
import Procesi.SLGen
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

open Matrix
open scoped commutatorElement

namespace Procesi

variable {F : Type} [Field F]

/-- ★★★ **`lem:14.12`（Saltman 1999）**：`n ≥ 3` 时，从 `PGL_n(F)` 到**交换群** `A` 的
任何群同态 `γ` 都满足 `γ(α)^n = 1`。

**证明**：见文件头的三步。关键引理是 `sl_mem_commutator`（`SL_n ⊆ [GL_n, GL_n]`，
`SLGen.lean`）——它正是原文所谓 "elementary exercise" 的全部内容。 -/
theorem pgl_pow_n_eq_one {A : Type*} [CommGroup A] {n : ℕ} (hn : 3 ≤ n)
    (γ : Matrix.ProjGenLinGroup (Fin n) F →* A) (α : Matrix.ProjGenLinGroup (Fin n) F) :
    γ α ^ n = 1 := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective α
  let gT : GeneralLinearGroup (Fin n) F →* A := γ.comp Matrix.ProjGenLinGroup.mk
  have hkills : ∀ x ∈ commutator (GeneralLinearGroup (Fin n) F), gT x = 1 := by
    intro x hx
    have hmap : Subgroup.map gT (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin n) F)), ⊤⁆) = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.commutator_self_eq_bot_iff]
      infer_instance
    have hmem : gT x ∈ Subgroup.map gT (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin n) F)), ⊤⁆) :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hmem
    simpa using hmem
  set u : Fˣ := GeneralLinearGroup.det g with hu
  set z : GeneralLinearGroup (Fin n) F := GeneralLinearGroup.scalar (Fin n) u with hz
  have hzpow : GeneralLinearGroup.det z = u ^ n := by
    rw [hz, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hgrange : z⁻¹ * g ^ n ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →*
      GeneralLinearGroup (Fin n) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hzpow, map_pow, hu, inv_mul_cancel]
  obtain ⟨s, hs⟩ := hgrange
  have hgpow : g ^ n = z * (s : GeneralLinearGroup (Fin n) F) := by
    rw [hs]
    group
  have hkey : gT (g ^ n) = 1 := by
    rw [hgpow, map_mul]
    have hz1 : gT z = 1 := by
      show γ (Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin n) u)) = 1
      rw [Matrix.ProjGenLinGroup.mk_scalar u, map_one]
    have hs1 : gT (s : GeneralLinearGroup (Fin n) F) = 1 :=
      hkills _ (sl_mem_commutator hn s)
    rw [hz1, hs1, one_mul]
  rw [← map_pow]
  rw [show (Matrix.ProjGenLinGroup.mk g) ^ n = Matrix.ProjGenLinGroup.mk (g ^ n) from
    (map_pow _ g n).symm]
  exact hkey

#print axioms pgl_pow_n_eq_one

/-- ★★★ **`lem:14.12` 的 `n = 2` 情形（`|F| ≥ 4`）**：`γ : PGL_2(F) →* A`（`A` 交换）⟹ `γ(α)^2 = 1`。

**证明**：与 `pgl_pow_n_eq_one` 同构，只把 `sl_mem_commutator`（需 `3 ≤ n`）换成 `sl2_mem_commutator`
（需 `∃ a, a ≠ 0 ∧ a² ≠ 1`），末步 `g² = (det g • 1)·s` 完全一致。 -/
theorem pgl_pow_two_eq_one {A : Type*} [CommGroup A] {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F →* A) (α : Matrix.ProjGenLinGroup (Fin 2) F) :
    γ α ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective α
  let gT : GeneralLinearGroup (Fin 2) F →* A := γ.comp Matrix.ProjGenLinGroup.mk
  have hkills : ∀ x ∈ commutator (GeneralLinearGroup (Fin 2) F), gT x = 1 := by
    intro x hx
    have hmap : Subgroup.map gT (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)), ⊤⁆) = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.commutator_self_eq_bot_iff]
      infer_instance
    have hmem : gT x ∈ Subgroup.map gT (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)), ⊤⁆) :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hmem
    simpa using hmem
  set u : Fˣ := GeneralLinearGroup.det g with hu
  set z : GeneralLinearGroup (Fin 2) F := GeneralLinearGroup.scalar (Fin 2) u with hz
  have hzpow : GeneralLinearGroup.det z = u ^ 2 := by
    rw [hz, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hgrange : z⁻¹ * g ^ 2 ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →*
      GeneralLinearGroup (Fin 2) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hzpow, map_pow, hu, inv_mul_cancel]
  obtain ⟨s, hs⟩ := hgrange
  have hgpow : g ^ 2 = z * (s : GeneralLinearGroup (Fin 2) F) := by
    rw [hs]
    group
  have hkey : gT (g ^ 2) = 1 := by
    rw [hgpow, map_mul]
    have hz1 : gT z = 1 := by
      show γ (Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 2) u)) = 1
      rw [Matrix.ProjGenLinGroup.mk_scalar u, map_one]
    have hs1 : gT (s : GeneralLinearGroup (Fin 2) F) = 1 :=
      hkills _ (sl2_mem_commutator ha hasq s)
    rw [hz1, hs1, one_mul]
  rw [← map_pow]
  rw [show (Matrix.ProjGenLinGroup.mk g) ^ 2 = Matrix.ProjGenLinGroup.mk (g ^ 2) from
    (map_pow _ g 2).symm]
  exact hkey

#print axioms pgl_pow_two_eq_one

/-- ★★★ **`lem:14.12` 的 `n = 2`、`F = F₂` 情形**：`γ : PGL_2(F₂) →* A`（`A` 交换）⟹ `γ(α)^2 = 1`。

**证明**：与 `pgl_pow_two_eq_one` 同构，但把输入 `sl2_mem_commutator`（`SL_2 ⊆ [G,G]`，
在 `F₂` 上不成立）换成 `f2_sq_mem_commutator`（`g² ∈ [G,G]`）：末步只需 `g² ∈ [G,G]`，
因为 `γ(mk ·)` 在 `[G,G]` 上平凡，故 `γ(α)² = γ(mk (g²)) = 1`。 -/
theorem pgl_pow_two_eq_one_f2 {A : Type*} [CommGroup A]
    (γ : Matrix.ProjGenLinGroup (Fin 2) (ZMod 2) →* A)
    (α : Matrix.ProjGenLinGroup (Fin 2) (ZMod 2)) : γ α ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective α
  let gT : GeneralLinearGroup (Fin 2) (ZMod 2) →* A := γ.comp Matrix.ProjGenLinGroup.mk
  have hkills : ∀ x ∈ commutator (GeneralLinearGroup (Fin 2) (ZMod 2)), gT x = 1 := by
    intro x hx
    have hmap : Subgroup.map gT (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 2))), ⊤⁆)
        = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.commutator_self_eq_bot_iff]
      infer_instance
    have hmem : gT x ∈ Subgroup.map gT
        (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 2))), ⊤⁆) :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hmem
    simpa using hmem
  have hkey : gT (g ^ 2) = 1 := hkills _ (f2_sq_mem_commutator g)
  rw [← map_pow]
  rw [show (Matrix.ProjGenLinGroup.mk g) ^ 2 = Matrix.ProjGenLinGroup.mk (g ^ 2) from
    (map_pow _ g 2).symm]
  exact hkey

#print axioms pgl_pow_two_eq_one_f2

/-- ★★★ **`lem:14.12` 的 `n = 2`、`F = F₃` 情形**：`γ : PGL_2(F₃) →* A`（`A` 交换）⟹ `γ(α)^2 = 1`。

**证明**：与 `pgl_pow_two_eq_one` 逐行同构（末步 `g² = (det g • 1)·s`，`s ∈ SL_2`，
`gT` 在纯量与在 `SL_2` 上都平凡），唯一改动是把输入 `sl2_mem_commutator`（需 `∃ a ≠ 0, a² ≠ 1`，
`F₃` 上不成立）换成 `sl2_mem_commutator_f3`（用 `diag(1,2)` 作换位子，无需该假设）。 -/
theorem pgl_pow_two_eq_one_f3 {A : Type*} [CommGroup A]
    (γ : Matrix.ProjGenLinGroup (Fin 2) (ZMod 3) →* A)
    (α : Matrix.ProjGenLinGroup (Fin 2) (ZMod 3)) : γ α ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective α
  let gT : GeneralLinearGroup (Fin 2) (ZMod 3) →* A := γ.comp Matrix.ProjGenLinGroup.mk
  have hkills : ∀ x ∈ commutator (GeneralLinearGroup (Fin 2) (ZMod 3)), gT x = 1 := by
    intro x hx
    have hmap : Subgroup.map gT (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 3))), ⊤⁆)
        = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.commutator_self_eq_bot_iff]
      infer_instance
    have hmem : gT x ∈ Subgroup.map gT
        (⁅(⊤ : Subgroup (GeneralLinearGroup (Fin 2) (ZMod 3))), ⊤⁆) :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hmem
    simpa using hmem
  set u : (ZMod 3)ˣ := GeneralLinearGroup.det g with hu
  set z : GeneralLinearGroup (Fin 2) (ZMod 3) := GeneralLinearGroup.scalar (Fin 2) u with hz
  have hzpow : GeneralLinearGroup.det z = u ^ 2 := by
    rw [hz, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hgrange : z⁻¹ * g ^ 2 ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) (ZMod 3) →*
      GeneralLinearGroup (Fin 2) (ZMod 3)).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hzpow, map_pow, hu, inv_mul_cancel]
  obtain ⟨s, hs⟩ := hgrange
  have hgpow : g ^ 2 = z * (s : GeneralLinearGroup (Fin 2) (ZMod 3)) := by
    rw [hs]
    group
  have hkey : gT (g ^ 2) = 1 := by
    rw [hgpow, map_mul]
    have hz1 : gT z = 1 := by
      show γ (Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 2) u)) = 1
      rw [Matrix.ProjGenLinGroup.mk_scalar u, map_one]
    have hs1 : gT (s : GeneralLinearGroup (Fin 2) (ZMod 3)) = 1 :=
      hkills _ (sl2_mem_commutator_f3 s)
    rw [hz1, hs1, one_mul]
  rw [← map_pow]
  rw [show (Matrix.ProjGenLinGroup.mk g) ^ 2 = Matrix.ProjGenLinGroup.mk (g ^ 2) from
    (map_pow _ g 2).symm]
  exact hkey

#print axioms pgl_pow_two_eq_one_f3

end Procesi
