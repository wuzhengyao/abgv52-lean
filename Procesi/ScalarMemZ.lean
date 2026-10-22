/-
  Procesi —— ★★ **`ScalarMemZHypK'` 的两块拼图**（旁路：绕开 Z 半，直接证纯量性）

  **目标**（[[proj-abgv52-frontier-R661]] §105 的第 1、2 步）：
  `c • 1 ∈ UDK' ⟹ c ∈ Z`（＝`ScalarMemZHypK'`）。本件落两块：

  * **§1（旁路第 1 步）`mem_centerImage_of_map_eq_scalar`**：`sprAlgebra`（`S'`-世界的
    `⟨X,Y_k⟩`）里的纯量矩阵，其标量 ∈ `κ(C)` 的像。机制：`psiSpr_sprAlgebra_surj` 给
    原像 `a ∈ R`；`ψ a` 的像中心 ⟹ `ψ a` 中心（`Matrix.map_injective` ＋ ψ 单射）⟹ `a ∈ C`
    （`mem_genericCenter_iff`）；再套 `psiSpr_center_scalar`。
  * **§2（旁路第 2 步）`Z = Frac(R_C)`**：`R_C := Subring.closure (κ(C) 的像)`
    （`sprCenterImageSubring`），`Z = IntermediateField.adjoin F R_C`；
    ★`exists_clear_den`：`z ∈ Z` ⟹ 存在 `0 ≠ s ∈ R_C` 使 `s * z ∈ R_C`
    （`IntermediateField.adjoin_induction` 五情形：mem／algebraMap（`F ⊆ R_C`）／add／inv／mul）。

  **⟹ 后续（旁路第 3、4 步，已完成）**：`A = Z • R'_K`（`R'_K = sprAlgebra` 的 `K'`-像）＋ 装配：
  `c•1 ∈ A` ⟹ 取 `s` 清分母 ⟹ `s·c•1 ∈ R'_K` ⟹（§1）`s c ∈ R_C ⊆ Z` ⟹ `c ∈ Z`。
-/

import Procesi.H2Final
import Procesi.UDKNFixed
import Procesi.PI.CentralIdeal

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Procesi

variable (F : Type) [Field F] (r n : ℕ)

set_option maxHeartbeats 1000000 in
/-- ★★★★ **`sprAlgebra` 里的纯量矩阵，其标量 ∈ `κ(C)` 的像**（`ScalarMemZHypK'` 旁路第 1 步）。 -/
theorem mem_centerImage_of_map_eq_scalar [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {M : Matrix (Fin n) (Fin n) (Spr F r n)} (hM : M ∈ sprAlgebra F r n k₀ hk₀)
    {t : SprField F r n}
    (ht : M.map (algebraMap (Spr F r n) (SprField F r n)) = Matrix.scalar (Fin n) t) :
    ∃ c : ↥(genericCenter F r n),
      t = algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c) := by
  classical
  -- 取 `θ`（`ψ` 的满性需要它）
  obtain ⟨L, hFld, hAlg, θ, hθinj, d, hθ⟩ := exists_algHom_diagonal_genMatKF F r n k₀
  letI : Field L := hFld
  letI : Algebra (SField F r n) L := hAlg
  letI : Algebra F L :=
    (algebraMap (SField F r n) L).comp (algebraMap F (SField F r n)) |>.toAlgebra
  haveI : IsScalarTower F (SField F r n) L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : NeZero n := ‹NeZero n›
  -- `ψ` 单射
  have hψinj : Function.Injective (psiSpr F r n k₀ hk₀) :=
    psiSpr_injective F r n k₀ hk₀ θ hθ hθinj
  -- `ι`（`algebraMap (Spr) (SprField)`）单射
  have hιinj : Function.Injective (algebraMap (Spr F r n) (SprField F r n)) :=
    IsFractionRing.injective (Spr F r n) (SprField F r n)
  -- 满性：`M = ψ a`
  have hMsurj : ∃ a : ↥(genericMatrixAlgebra F r n),
      psiSpr F r n k₀ hk₀ a = M :=
    psiSpr_sprAlgebra_surj F r n k₀ hk₀ θ hθ ⟨M, hM⟩
  obtain ⟨a, ha⟩ := hMsurj
  -- `ψ a` 的像是纯量 ⟹ `a` 中心
  have hcentral : a ∈ genericCenter F r n := by
    rw [mem_genericCenter_iff]
    intro b
    -- 在 `K'` 层比较：`(ψ a).map ι` 是纯量 ⟹ 与 `(ψ b).map ι` 交换
    have hMk : (psiSpr F r n k₀ hk₀ a).map (algebraMap (Spr F r n) (SprField F r n))
        = Matrix.scalar (Fin n) t := by rw [ha]; exact ht
    have hscalar_mul : ∀ X : Matrix (Fin n) (Fin n) (SprField F r n),
        Matrix.scalar (Fin n) t * X = X * Matrix.scalar (Fin n) t := by
      intro X
      have h1 : Matrix.scalar (Fin n) t
          = t • (1 : Matrix (Fin n) (Fin n) (SprField F r n)) := by
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.scalar_apply, Matrix.smul_apply, hij]
      rw [h1, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    have h1 : (psiSpr F r n k₀ hk₀ a).map (algebraMap (Spr F r n) (SprField F r n))
          * (psiSpr F r n k₀ hk₀ b).map (algebraMap (Spr F r n) (SprField F r n))
        = (psiSpr F r n k₀ hk₀ b).map (algebraMap (Spr F r n) (SprField F r n))
          * (psiSpr F r n k₀ hk₀ a).map (algebraMap (Spr F r n) (SprField F r n)) := by
      rw [hMk]
      exact hscalar_mul _
    rw [← Matrix.map_mul, ← Matrix.map_mul] at h1
    have h2 : psiSpr F r n k₀ hk₀ a * psiSpr F r n k₀ hk₀ b
        = psiSpr F r n k₀ hk₀ b * psiSpr F r n k₀ hk₀ a :=
      Matrix.map_injective hιinj h1
    rw [← map_mul, ← map_mul] at h2
    exact hψinj h2.symm
  -- 结论：`t = κ(a)`
  refine ⟨⟨a, hcentral⟩, ?_⟩
  have hc := psiSpr_center_scalar F r n D k₀ hk₀ ⟨a, hcentral⟩
  rw [ha, ht] at hc
  exact Matrix.scalar_inj.mp hc

#print axioms mem_centerImage_of_map_eq_scalar

/-- `R_C := κ(C)` 在 `K'` 里生成的子环。 -/
noncomputable def sprCenterImageSubring [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Subring (SprField F r n) :=
  Subring.closure (Set.range (fun c : ↥(genericCenter F r n) =>
    algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)))

#print axioms sprCenterImageSubring

/-- `κ(C)` 的像落在 `R_C` 里。 -/
theorem algebraMap_sprCenterK_mem_subring [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (c : ↥(genericCenter F r n)) :
    algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)
      ∈ sprCenterImageSubring F r n D k₀ hk₀ :=
  Subring.subset_closure ⟨c, rfl⟩

#print axioms algebraMap_sprCenterK_mem_subring

/-- `Z` 就是 `F` 与 `R_C` 生成的中间域。 -/
theorem sprCenterImageField_eq_adjoin_subring [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    sprCenterImageField F r n D k₀ hk₀
      = IntermediateField.adjoin F (sprCenterImageSubring F r n D k₀ hk₀ : Set (SprField F r n)) := by
  rw [sprCenterImageField, sprCenterImageSubring]
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    exact IntermediateField.subset_adjoin F _ (Subring.subset_closure ⟨c, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    refine Subring.closure_le.mpr ?_ hx
    intro y hy
    obtain ⟨c, rfl⟩ := hy
    exact IntermediateField.subset_adjoin F _ ⟨c, rfl⟩

#print axioms sprCenterImageField_eq_adjoin_subring

/-- `algebraMap F (Matrix)` 就是纯量矩阵。 -/
theorem algebraMap_eq_scalar_matrix (f : F) :
    algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) f
      = Matrix.scalar (Fin n) (algebraMap F (S F r n) f) := by
  rw [Matrix.algebraMap_eq_diagonal]
  rfl

#print axioms algebraMap_eq_scalar_matrix

/-- `F` 的像落在 `R_C` 里（取中心元 `f • 1`）。 -/
theorem algebraMap_mem_subring [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) (f : F) :
    algebraMap F (SprField F r n) f ∈ sprCenterImageSubring F r n D k₀ hk₀ := by
  classical
  set c : ↥(genericCenter F r n) :=
    ⟨algebraMap F ↥(genericMatrixAlgebra F r n) f, Subalgebra.algebraMap_mem _ f⟩
  have hmem : algebraMap (Spr F r n) (SprField F r n) (sprCenterK F r n k₀ hk₀ D c)
      ∈ sprCenterImageSubring F r n D k₀ hk₀ :=
    algebraMap_sprCenterK_mem_subring F r n D k₀ hk₀ c
  have hκ : sprCenterK F r n k₀ hk₀ D c = algebraMap F (Spr F r n) f := by
    have hspec := sprCenterPolyK_spec F r n D c
    have hc : ((c : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
        = Matrix.scalar (Fin n) (algebraMap F (S F r n) f) := by
      have h1 : ((c : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n))
          = algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) f := rfl
      rw [h1, algebraMap_eq_scalar_matrix]
    rw [hc] at hspec
    have hpoly : sprCenterPolyK F r n D c = algebraMap F (S F r n) f :=
      Matrix.scalar_inj.mp hspec.symm
    show (evSpr F r n k₀ hk₀) (sprCenterPolyK F r n D c) = algebraMap F (Spr F r n) f
    rw [hpoly]
    exact (evSpr F r n k₀ hk₀).commutes f
  rw [hκ] at hmem
  rwa [← IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n)] at hmem

#print axioms algebraMap_mem_subring

set_option maxHeartbeats 1000000 in
/-- ★★★ **清分母**：`z ∈ Z` ⟹ 存在 `0 ≠ s ∈ R_C` 使 `s * z ∈ R_C`。 -/
theorem exists_clear_den [Nonempty (Fin n)] [NeZero n]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {z : SprField F r n} (hz : z ∈ sprCenterImageField F r n D k₀ hk₀) :
    ∃ s ∈ sprCenterImageSubring F r n D k₀ hk₀,
      s ≠ 0 ∧ s * z ∈ sprCenterImageSubring F r n D k₀ hk₀ := by
  classical
  rw [sprCenterImageField_eq_adjoin_subring] at hz
  have key : ∀ x ∈ IntermediateField.adjoin F
        ((sprCenterImageSubring F r n D k₀ hk₀ : Subring (SprField F r n)) :
          Set (SprField F r n)),
      ∃ s ∈ sprCenterImageSubring F r n D k₀ hk₀,
        s ≠ 0 ∧ s * x ∈ sprCenterImageSubring F r n D k₀ hk₀ := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      exact ⟨1, (sprCenterImageSubring F r n D k₀ hk₀).one_mem, one_ne_zero, by simpa using hy⟩
    | algebraMap f =>
      exact ⟨1, (sprCenterImageSubring F r n D k₀ hk₀).one_mem, one_ne_zero,
        by simpa using algebraMap_mem_subring F r n D k₀ hk₀ f⟩
    | add y w _ _ ihy ihw =>
      obtain ⟨s₁, hs₁, hs₁0, h1⟩ := ihy
      obtain ⟨s₂, hs₂, hs₂0, h2⟩ := ihw
      refine ⟨s₁ * s₂, (sprCenterImageSubring F r n D k₀ hk₀).mul_mem hs₁ hs₂,
        mul_ne_zero hs₁0 hs₂0, ?_⟩
      have hrw : s₁ * s₂ * (y + w) = s₂ * (s₁ * y) + s₁ * (s₂ * w) := by ring
      rw [hrw]
      exact (sprCenterImageSubring F r n D k₀ hk₀).add_mem
        ((sprCenterImageSubring F r n D k₀ hk₀).mul_mem hs₂ h1)
        ((sprCenterImageSubring F r n D k₀ hk₀).mul_mem hs₁ h2)
    | inv y _ ihy =>
      obtain ⟨s, hs, hs0, h1⟩ := ihy
      by_cases hy0 : y = 0
      · subst hy0
        exact ⟨1, (sprCenterImageSubring F r n D k₀ hk₀).one_mem, one_ne_zero, by simp⟩
      · refine ⟨s * y, h1, mul_ne_zero hs0 hy0, ?_⟩
        have hsq : (s * y) * y⁻¹ = s := by
          rw [mul_assoc, mul_inv_cancel₀ hy0, mul_one]
        rw [hsq]
        exact hs
    | mul y w _ _ ihy ihw =>
      obtain ⟨s₁, hs₁, hs₁0, h1⟩ := ihy
      obtain ⟨s₂, hs₂, hs₂0, h2⟩ := ihw
      refine ⟨s₁ * s₂, (sprCenterImageSubring F r n D k₀ hk₀).mul_mem hs₁ hs₂,
        mul_ne_zero hs₁0 hs₂0, ?_⟩
      have hrw : s₁ * s₂ * (y * w) = (s₁ * y) * (s₂ * w) := by ring
      rw [hrw]
      exact (sprCenterImageSubring F r n D k₀ hk₀).mul_mem h1 h2
  exact key z hz

#print axioms exists_clear_den


end Procesi
