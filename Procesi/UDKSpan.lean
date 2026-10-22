/-
  Procesi —— ★★★ **`UDK' = Z • R'_K` 的前半**（旁路第 3 步的地基）

  `R'_K := sprAlgebra` 沿 `algebraMap (Spr) (SprField)` 的像（`sprAlgebraK`）。
  本件两件（**已机检**）：
  * `mem_sprAlgebraK_iff`：`N ∈ R'_K ↔ ∃ M ∈ sprAlgebra, M.map ι = N`；
  * ★`map_mem_UDK'_of_mem_sprAlgebra`：`sprAlgebra` 的像落在 `UDK'` 里。
    工艺：不用 `Algebra.adjoin_induction`（motive 的证明项在 `rw` 后失配），而用
    **`F`-子代数构造** `S := {M | φ M ∈ UDK'}`（`φ := RingHom.mapMatrix (algebraMap …)`），
    再 `Algebra.adjoin_le`；`φ` 是 `RingHom` ⟹ `map_add`／`map_mul`／`map_zero` 全免费。

  **R774 新增（★ 第 3 步反向已闭合）**：
  * `closure_sprAlgebraK_subset_span`：`↑(Submonoid.closure ↑R'_K) ⊆ ↑(span_Z ↑R'_K)`；
  * `mem_adjoin_sprAlgebraK_iff`：`x ∈ adjoin_Z ↑R'_K ↔ x ∈ span_Z ↑R'_K`
    （走 mathlib 的 `Algebra.adjoin_eq_span_of_subset`——**不需要**对 `span` 做乘法封闭的
    嵌套归纳：`R'_K` 本身是子代数 ⟹ `Submonoid.closure ↑R'_K = ↑R'_K ⊆ span`）；
  * ★★★★ `mem_span_sprAlgebraK_iff`：**`UDK' = span_Z R'_K`**（＝文档 `A = Z • R'_K`），
    反向由 `Algebra.adjoin_mono`（生成元 `ι(sprGen k) ∈ ↑R'_K`）＋ 上式一步得出。

  **⟹ 后续（已完成）**：装配（`scalarMemZHypK'`）于 R774 在 `UDKScalarMem` 机检。
  **注**：`mem_span_sprAlgebraK_iff` 本身**不在最终证明路径上**——`scalarMemZHypK'` 改用
  `Algebra.adjoin_induction` 直接对 `UDK'`（本身即 `Algebra.adjoin`）归纳；
  该恒等式作为**已验证的中间结果**保留（见 `dag/README.md` 的说明 2）。
-/

import Procesi.H2Final
import Procesi.ScalarMemZ
import Procesi.UDKNFixed

open Matrix
open ABGV52
open scoped IntermediateField.algebraAdjoinAdjoin

set_option synthInstance.maxHeartbeats 1000000

namespace Procesi

set_option synthInstance.maxHeartbeats 1000000

variable (F : Type) [Field F] (r n : ℕ)

/-- `R'_K`：`sprAlgebra`（`S'`-世界）沿 `algebraMap (Spr) (SprField)` 的像。 -/
noncomputable def sprAlgebraK [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Subalgebra F (Matrix (Fin n) (Fin n) (SprField F r n)) :=
  (sprAlgebra F r n k₀ hk₀).map
    (AlgHom.mapMatrix (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))

#print axioms sprAlgebraK

/-- `sprAlgebraK` 的成员刻画。 -/
theorem mem_sprAlgebraK_iff [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {N : Matrix (Fin n) (Fin n) (SprField F r n)} :
    N ∈ sprAlgebraK F r n k₀ hk₀ ↔
      ∃ M ∈ sprAlgebra F r n k₀ hk₀, M.map (algebraMap (Spr F r n) (SprField F r n)) = N := by
  constructor
  · intro hN
    obtain ⟨M, hM, hMN⟩ := Subalgebra.mem_map.mp hN
    exact ⟨M, hM, hMN⟩
  · rintro ⟨M, hM, rfl⟩
    exact Subalgebra.mem_map.mpr ⟨M, hM, rfl⟩

#print axioms mem_sprAlgebraK_iff

/-- `sprAlgebra` 沿 `algebraMap` 的像落在 `UDK'` 里。 -/
theorem map_mem_UDK'_of_mem_sprAlgebra [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {M : Matrix (Fin n) (Fin n) (Spr F r n)} (hM : M ∈ sprAlgebra F r n k₀ hk₀) :
    M.map (algebraMap (Spr F r n) (SprField F r n)) ∈ UDK' F r n D k₀ hk₀ := by
  classical
  -- 逐项搬运用的环同态
  let φ : Matrix (Fin n) (Fin n) (Spr F r n) →+*
      Matrix (Fin n) (Fin n) (SprField F r n) :=
    RingHom.mapMatrix (algebraMap (Spr F r n) (SprField F r n))
  have hφ : ∀ M, φ M = M.map (algebraMap (Spr F r n) (SprField F r n)) := fun M => rfl
  -- `F`-子代数：其像是 `UDK'` 的元素
  let S : Subalgebra F (Matrix (Fin n) (Fin n) (Spr F r n)) :=
    { carrier := {M | φ M ∈ UDK' F r n D k₀ hk₀}
      zero_mem' := by
        show φ 0 ∈ UDK' F r n D k₀ hk₀
        rw [map_zero]
        exact (UDK' F r n D k₀ hk₀).zero_mem
      add_mem' := by
        intro a b ha hb
        show φ (a + b) ∈ UDK' F r n D k₀ hk₀
        rw [map_add]
        exact (UDK' F r n D k₀ hk₀).add_mem ha hb
      mul_mem' := by
        intro a b ha hb
        show φ (a * b) ∈ UDK' F r n D k₀ hk₀
        rw [map_mul]
        exact (UDK' F r n D k₀ hk₀).mul_mem ha hb
      algebraMap_mem' := by
        intro f
        show φ (algebraMap F (Matrix (Fin n) (Fin n) (Spr F r n)) f)
          ∈ UDK' F r n D k₀ hk₀
        have h1 : φ (algebraMap F (Matrix (Fin n) (Fin n) (Spr F r n)) f)
            = algebraMap F (Matrix (Fin n) (Fin n) (SprField F r n)) f := by
          rw [hφ, Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal,
            Matrix.diagonal_map (map_zero _)]
          exact congrArg Matrix.diagonal (funext (fun i =>
            IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) f))
        rw [h1]
        have h2 : algebraMap F (Matrix (Fin n) (Fin n) (SprField F r n)) f
            = algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
                (Matrix (Fin n) (Fin n) (SprField F r n))
                (algebraMap F ↥(sprCenterImageField F r n D k₀ hk₀) f) := by
          rw [← IsScalarTower.algebraMap_apply F ↥(sprCenterImageField F r n D k₀ hk₀)
            (Matrix (Fin n) (Fin n) (SprField F r n))]
        rw [h2]
        exact algebraMap_mem (UDK' F r n D k₀ hk₀) _ }
  have hle : sprAlgebra F r n k₀ hk₀ ≤ S := by
    rw [sprAlgebra]
    refine Algebra.adjoin_le ?_
    rintro x ⟨k, rfl⟩
    show φ (sprGen F r n k₀ hk₀ k) ∈ UDK' F r n D k₀ hk₀
    rw [hφ]
    have h := psiSpr_mem_UDK' F r n D k₀ hk₀ k
    rwa [psiSpr_sprGen] at h
  exact hle hM

#print axioms map_mem_UDK'_of_mem_sprAlgebra


/-! ## 旁路第 3 步反向：`UDK' = span_Z R'_K`（R774） -/

/-- `UDK'` 的生成元（`ι (sprGen k)`）在 `R'_K` 里。 -/
theorem gen_mem_sprAlgebraK [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0) (k : Fin r) :
    (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
      (algebraMap (Spr F r n) (SprField F r n)) ∈ sprAlgebraK F r n k₀ hk₀ := by
  simp only [psiSpr_sprGen]
  exact Subalgebra.mem_map.mpr
    ⟨sprGen F r n k₀ hk₀ k, Algebra.subset_adjoin (Set.mem_range_self k), rfl⟩

#print axioms gen_mem_sprAlgebraK

/-- `R'_K` 是子代数 ⟹ `Submonoid.closure ↑R'_K ⊆ ↑(span_Z ↑R'_K)`。 -/
theorem closure_sprAlgebraK_subset_span [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (↑(Submonoid.closure
        (↑(sprAlgebraK F r n k₀ hk₀) : Set (Matrix (Fin n) (Fin n) (SprField F r n)))) :
        Set (Matrix (Fin n) (Fin n) (SprField F r n)))
      ⊆ (Submodule.span ↥(sprCenterImageField F r n D k₀ hk₀)
          (↑(sprAlgebraK F r n k₀ hk₀) :
            Set (Matrix (Fin n) (Fin n) (SprField F r n))) :
          Set (Matrix (Fin n) (Fin n) (SprField F r n))) := by
  intro y hy
  refine Submodule.subset_span ?_
  exact Submonoid.closure_induction (motive := fun y _ =>
      y ∈ (sprAlgebraK F r n k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n))))
    (fun x hx => hx) (sprAlgebraK F r n k₀ hk₀).one_mem
    (fun a b _ _ ha hb => (sprAlgebraK F r n k₀ hk₀).mul_mem ha hb) hy

#print axioms closure_sprAlgebraK_subset_span

/-- `x ∈ adjoin_Z ↑R'_K ↔ x ∈ span_Z ↑R'_K`（`Algebra.adjoin_eq_span_of_subset`）。 -/
theorem mem_adjoin_sprAlgebraK_iff [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {x : Matrix (Fin n) (Fin n) (SprField F r n)} :
    x ∈ Algebra.adjoin ↥(sprCenterImageField F r n D k₀ hk₀)
        (↑(sprAlgebraK F r n k₀ hk₀) :
          Set (Matrix (Fin n) (Fin n) (SprField F r n)))
      ↔ x ∈ Submodule.span ↥(sprCenterImageField F r n D k₀ hk₀)
          (↑(sprAlgebraK F r n k₀ hk₀) :
            Set (Matrix (Fin n) (Fin n) (SprField F r n))) := by
  have h := Algebra.adjoin_eq_span_of_subset
    (R := ↥(sprCenterImageField F r n D k₀ hk₀))
    (closure_sprAlgebraK_subset_span F r n D k₀ hk₀)
  have h' := congrArg (fun (p : Submodule ↥(sprCenterImageField F r n D k₀ hk₀)
      (Matrix (Fin n) (Fin n) (SprField F r n))) => x ∈ p) h
  simpa using h'

#print axioms mem_adjoin_sprAlgebraK_iff

/-- ★★★★ **`UDK' = Z • R'_K`**（`Z`-张成；文档 `A = Z • R'_K`）。 -/
theorem mem_span_sprAlgebraK_iff [NeZero n] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0)
    {x : Matrix (Fin n) (Fin n) (SprField F r n)} :
    x ∈ Submodule.span ↥(sprCenterImageField F r n D k₀ hk₀)
        ((sprAlgebraK F r n k₀ hk₀ : Subalgebra F (Matrix (Fin n) (Fin n) (SprField F r n))) :
          Set (Matrix (Fin n) (Fin n) (SprField F r n)))
      ↔ x ∈ UDK' F r n D k₀ hk₀ := by
  classical
  refine ⟨?_, ?_⟩
  · intro hN
    induction hN using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨M, hM, rfl⟩ := (mem_sprAlgebraK_iff F r n k₀ hk₀).mp ha
      exact map_mem_UDK'_of_mem_sprAlgebra F r n D k₀ hk₀ hM
    | zero => exact (UDK' F r n D k₀ hk₀).zero_mem
    | add a b _ _ iha ihb => exact (UDK' F r n D k₀ hk₀).add_mem iha ihb
    | smul z a _ iha =>
      have h : algebraMap ↥(sprCenterImageField F r n D k₀ hk₀)
          (Matrix (Fin n) (Fin n) (SprField F r n)) z * a = z • a := by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
      rw [← h]
      exact mul_mem (algebraMap_mem (UDK' F r n D k₀ hk₀) z) iha
  · intro hx
    have hgen : Set.range (fun k : Fin r =>
        (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩).map
          (algebraMap (Spr F r n) (SprField F r n)))
        ⊆ (↑(sprAlgebraK F r n k₀ hk₀) :
            Set (Matrix (Fin n) (Fin n) (SprField F r n))) := by
      rintro _ ⟨k, rfl⟩
      exact gen_mem_sprAlgebraK F r n k₀ hk₀ k
    have hx' : x ∈ Algebra.adjoin ↥(sprCenterImageField F r n D k₀ hk₀)
        (↑(sprAlgebraK F r n k₀ hk₀) :
          Set (Matrix (Fin n) (Fin n) (SprField F r n))) :=
      Algebra.adjoin_mono hgen hx
    exact (mem_adjoin_sprAlgebraK_iff F r n D k₀ hk₀).mp hx'

#print axioms mem_span_sprAlgebraK_iff

end Procesi
