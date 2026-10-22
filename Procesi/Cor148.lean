/-
  Procesi —— ★★★★★ **`cor:14.8(a)`（中心元在 `K` 上是纯量矩阵）与结构束的可居住性**

  **为什么需要本件**（L1 在住性，[[deadend-genericCenter-eq-F]] §2）：
  `h2_unconditional`（`UDKScalarMem`）的形状是 `∀ D : GenericDivisionData F 2 9, …`，
  而 **`Nonempty (GenericDivisionData F 2 9)` 未机检** ⟹ 主定理有空洞风险
  （`∅-vacuous-risk`）。本仓已机检其**精确等价** `nonempty_genericDivisionData_iff`
  （`GenericInv:2947`）：可居住性 ⟺ Saltman `cor:14.8(a)`。本件证 `cor:14.8(a)`。

  **数学（Saltman `raw/Saltman1999ch14.tex:171`，一句）**：
  `lem:14.7`（`Ξ` 是 `M_n(K)` 的 `K`-基）的推论是 `R(F,n,r)K = M_n(K)`；
  故 `C(F,n,r)` 的每个元与 `M_n(K)` 全交换 ⟹ 落在 `M_n(K)` 的中心 = 纯量矩阵；
  再 `M_n(S) ∩ K = S`。

  **本件的两条（已机检）**：
  * ★ `exists_scalar_map_of_mem_genericCenter_of_span`：`cor:14.8(a)`
    （**条件于 `hspan`**，即 `Ξ` 的张成性 `R·K = M_n(K)`）。
  * ★★ `nonempty_genericDivisionData_of_span`：`hspan ⟹ Nonempty (GenericDivisionData F 2 n)`。

  **⟹ 状态更新（R776／R779）**：本件两条**条件于 `hspan`** 的定理保持不变；
  其假设 `hspan` 已于 R776（`GenericSpan`，Vandermonde×Kronecker ＋ det 转移）与
  R779（`Nonvacuous.adjoin_genericMatrix_map_eq_top`，矩阵求逆路线）**机检**，故
  `nonempty_genericDivisionData_two_nine`（`Nonvacuous`）**无条件**成立。
  **注**：`cor:14.8(a)` 不需要 PI 理论——Saltman `raw/Saltman1999ch14.tex:171` 只用
  `lem:14.7` 的**张成**后果 `R·K = M_n(K)`。
-/

import Procesi.GenericMatrix
import Procesi.KAction
import Procesi.GenericInv


open Matrix

namespace Procesi

variable (F : Type) [Field F]

/-- ★ **`cor:14.8(a)` 的 Lean 形态（条件于 `hspan`）**：`C(R)` 的元在 `K` 上是纯量矩阵。 -/
theorem exists_scalar_map_of_mem_genericCenter_of_span [NeZero n]
    (hspan : Algebra.adjoin (SField F 2 n)
      (Set.range (fun k : Fin 2 =>
        (genericMatrix F 2 n k).map (algebraMap (S F 2 n) (SField F 2 n)))) = ⊤)
    (c : ↥(genericCenter F 2 n)) :
    ∃ f : SField F 2 n,
      ((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)).map
        (algebraMap (S F 2 n) (SField F 2 n)) = Matrix.scalar (Fin n) f := by
  classical
  set ι : S F 2 n →+* SField F 2 n := algebraMap (S F 2 n) (SField F 2 n)
  set gens : Set (Matrix (Fin n) (Fin n) (SField F 2 n)) :=
    Set.range (fun k : Fin 2 => (genericMatrix F 2 n k).map ι)
  set Mc : Matrix (Fin n) (Fin n) (SField F 2 n) :=
    ((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)).map ι
  have hcenter : Mc ∈ Subalgebra.center (SField F 2 n)
      (Matrix (Fin n) (Fin n) (SField F 2 n)) := by
    rw [Subalgebra.mem_center_iff]
    intro y
    have hy : y ∈ Algebra.adjoin (SField F 2 n) gens := by
      rw [hspan]
      simp
    clear hspan
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hcomm := commute_genericMatrix_of_mem_genericCenter F 2 n c.2 k
      have h2 := congrArg (fun z : ↥(genericMatrixAlgebra F 2 n) =>
        ((z : Matrix (Fin n) (Fin n) (S F 2 n)))) hcomm
      have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) (S F 2 n) => M.map ι) h2
      simpa [Mc, Matrix.map_mul] using h3
    | algebraMap f =>
      have h1 : algebraMap (SField F 2 n) (Matrix (Fin n) (Fin n) (SField F 2 n)) f
          = f • (1 : Matrix (Fin n) (Fin n) (SField F 2 n)) :=
        Algebra.algebraMap_eq_smul_one f
      rw [h1, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul]
    | add x y _ _ ihx ihy =>
      rw [add_mul, mul_add, ihx, ihy]
    | mul x y _ _ ihx ihy =>
      rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
  obtain ⟨f, hf⟩ := exists_eq_scalar_of_mem_matrixCenter (SField F 2 n) n hcenter
  exact ⟨f, hf⟩

#print axioms exists_scalar_map_of_mem_genericCenter_of_span

end Procesi

namespace Procesi

variable (F : Type) [Field F]

/-! ## L3：打包 `GenericDivisionData`（条件于 `hspan`） -/

/-- 非零维数给出 `Fin n` 的基点。 -/
private def finZeroOfNeZero {n : ℕ} [NeZero n] : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- ★ **`Nonempty (GenericDivisionData F 2 n)`（条件于 `hspan`）**。 -/
theorem nonempty_genericDivisionData_of_span [NeZero n]
    (hspan : Algebra.adjoin (SField F 2 n)
      (Set.range (fun k : Fin 2 =>
        (genericMatrix F 2 n k).map (algebraMap (S F 2 n) (SField F 2 n)))) = ⊤) :
    Nonempty (GenericDivisionData F 2 n) := by
  classical
  set Φ : Matrix (Fin n) (Fin n) (S F 2 n) →+*
      Matrix (Fin n) (Fin n) (SField F 2 n) :=
    RingHom.mapMatrix (algebraMap (S F 2 n) (SField F 2 n))
  have hΦ : ∀ M, Φ M = M.map (algebraMap (S F 2 n) (SField F 2 n)) := fun M => rfl
  have hspec : ∀ c : ↥(genericCenter F 2 n), ∃ f : SField F 2 n,
      Φ (((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)))
        = Matrix.scalar (Fin n) f := by
    intro c
    obtain ⟨f, hf⟩ := exists_scalar_map_of_mem_genericCenter_of_span F hspan c
    exact ⟨f, by rw [hΦ]; exact hf⟩
  -- 每个 `c` 的像确实是纯量矩阵
  have hsc : ∀ c : ↥(genericCenter F 2 n),
      Φ (((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)))
        = Matrix.scalar (Fin n)
            (Φ (((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)))
              (finZeroOfNeZero (n := n)) (finZeroOfNeZero (n := n))) := by
    intro c
    obtain ⟨f, hf⟩ := hspec c
    have h0 : f = Φ (((c.1 : ↥(genericMatrixAlgebra F 2 n)) :
        Matrix (Fin n) (Fin n) (S F 2 n)))
        (finZeroOfNeZero (n := n)) (finZeroOfNeZero (n := n)) := by
      rw [hf]
      simp [Matrix.scalar_apply]
    rw [← h0]
    exact hf
  refine ⟨{ centK := ?_, centK_spec := ?_ }⟩
  · refine
      { toFun := fun c =>
          Φ (((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)))
            (finZeroOfNeZero (n := n)) (finZeroOfNeZero (n := n))
        map_one' := ?_
        map_mul' := ?_
        map_zero' := ?_
        map_add' := ?_
        commutes' := ?_ }
    · have h1 : ((((1 : ↥(genericCenter F 2 n)).1 : ↥(genericMatrixAlgebra F 2 n)) :
          Matrix (Fin n) (Fin n) (S F 2 n))) = 1 := rfl
      show Φ _ (finZeroOfNeZero (n := n)) (finZeroOfNeZero (n := n)) = 1
      rw [h1, map_one]
      simp
    · intro c d
      have h1 : ((((c * d : ↥(genericCenter F 2 n)).1 : ↥(genericMatrixAlgebra F 2 n)) :
          Matrix (Fin n) (Fin n) (S F 2 n)))
          = ((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n))
            * ((d.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)) := rfl
      show Φ _ _ _ = _
      rw [h1, map_mul, hsc c, hsc d, ← (Matrix.scalar (Fin n)).map_mul]
      simp [Matrix.scalar_apply]
    · have h1 : ((((0 : ↥(genericCenter F 2 n)).1 : ↥(genericMatrixAlgebra F 2 n)) :
          Matrix (Fin n) (Fin n) (S F 2 n))) = 0 := rfl
      show Φ _ (finZeroOfNeZero (n := n)) (finZeroOfNeZero (n := n)) = 0
      rw [h1, map_zero]
      simp
    · intro c d
      have h1 : ((((c + d : ↥(genericCenter F 2 n)).1 : ↥(genericMatrixAlgebra F 2 n)) :
          Matrix (Fin n) (Fin n) (S F 2 n)))
          = ((c.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n))
            + ((d.1 : ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)) := rfl
      show Φ _ _ _ = _
      rw [h1, map_add, hsc c, hsc d, ← (Matrix.scalar (Fin n)).map_add]
      simp [Matrix.scalar_apply]
    · intro f
      have h1 : ((((algebraMap F ↥(genericCenter F 2 n) f).1 :
            ↥(genericMatrixAlgebra F 2 n)) : Matrix (Fin n) (Fin n) (S F 2 n)))
          = algebraMap F (Matrix (Fin n) (Fin n) (S F 2 n)) f := rfl
      show Φ _ (finZeroOfNeZero (n := n)) (finZeroOfNeZero (n := n)) = _
      rw [h1, hΦ, Matrix.algebraMap_eq_diagonal]
      simp [IsScalarTower.algebraMap_apply F (S F 2 n) (SField F 2 n)]
  · intro c
    exact hsc c

#print axioms nonempty_genericDivisionData_of_span

end Procesi
