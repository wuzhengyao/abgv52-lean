/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-vii：度数收口（第二环）· 对角分次路线的 `K` 侧机件**

  目标：**`F(Y) = F(M)^A`**，即 `diagSubfield F A = latticeInvariants F A (A → ℤ)`（⊇ 为难点）。

  路线（探针 `Probe52`–`Probe54` 定案；本件落 §3 的第一块）：

    * **`phiDiag`（Φ₀）**：对角模型 → `K`，`z^m ↦ diagMono m`（逆 DFT 在 `K` 侧的像）；
    * **`phiDiag_zMono`**：单项式层的取值；
    * **`phiDiag_mem_diagSubfield_of_span`**：`Y`-单项式张成中元素的 `Φ₀`-像落在 `F(Y)` 中。

  **余下（见 wiki §3k）**：① 逆 DFT `ψ`（`latticeAlgebra → diagFrac`，按 `u_a = |A|⁻¹∑_χ χ(a) z_χ`）
  ＋ 恒等式 `ψ ∘ Φ₀ = algebraMap` ⟹ `Φ₀` 单射；② `Φ₀` 的分式域上延 `Φ`（`IsFractionRing.liftAlgHom`）
  ＋ 双射性 ＋ 等变性（`Probe54.probe_frac_equivariance`）；③ 汇编：不变元 `z` ⟹ `Φ⁻¹z` 不变
  ⟹ `Probe54.probe_step2` ⟹ `z ∈ diagSubfield`。
-/
import ABGV52.D9_ABGV52

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

section PhiDiag

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- `diagMono 0 = 1`（`diagMono` 是单项式乘积）。 -/
lemma diagMono_zero : diagMono F A (0 : expVector F A) = 1 :=
  Finsupp.prod_zero_index

/-- **Φ₀**：对角模型 `F[z_χ^{±}]` → `K`，`z^m ↦ diagMono m`（逆 DFT 在 `K` 侧的像）。

（与 D7 的 `diagMonoidHom` 同构型：由 `diagMono_add` 保证乘性、`diagMono_zero` 保证幺元。） -/
noncomputable def phiDiag : diagAlgebra F A →ₐ[F] latticeFunctionField F (A → ℤ) :=
  MonoidAlgebra.lift F (latticeFunctionField F (A → ℤ))
    (Multiplicative (MulChar A F →₀ ℤ))
    { toFun := fun n => diagMono F A n.toAdd
      map_one' := by
        show diagMono F A (1 : Multiplicative (MulChar A F →₀ ℤ)).toAdd = 1
        rw [show (1 : Multiplicative (MulChar A F →₀ ℤ)).toAdd = 0 from rfl]
        exact diagMono_zero F A
      map_mul' := fun m n => by
        show diagMono F A (m * n).toAdd = diagMono F A m.toAdd * diagMono F A n.toAdd
        rw [show (m * n).toAdd = m.toAdd + n.toAdd from rfl, diagMono_add] }

/-- `Φ₀` 在单项式上的取值。 -/
lemma phiDiag_zMono (m : expVector F A) :
    phiDiag F A (zMono F A m) = diagMono F A m := by
  show MonoidAlgebra.lift F (latticeFunctionField F (A → ℤ))
      (Multiplicative (MulChar A F →₀ ℤ)) _
      (MonoidAlgebra.single (Multiplicative.ofAdd m) 1) = diagMono F A m
  rw [MonoidAlgebra.lift_single, one_smul]
  rfl

/-- **目标集（`K` 侧）**：`F`-纯量 ∪ 不变单项式 —— 这正是 `diagSubfield` 的生成集。 -/
noncomputable def targetSetK : Set (latticeFunctionField F (A → ℤ)) :=
  Set.range (algebraMap F (latticeFunctionField F (A → ℤ))) ∪
    Set.range fun m : ↥(kernelLattice F A) => diagMono F A (m : expVector F A)

/-- **闭包推送**：`Y`-单项式张成中的元素，其 `Φ₀`-像落在 `F(Y)`（`= diagSubfield`）中。 -/
lemma phiDiag_mem_diagSubfield_of_span {y : diagAlgebra F A}
    (hy : y ∈ Submodule.span F
      (Set.range fun m : ↥(kernelLattice F A) => zMono F A (m : expVector F A))) :
    phiDiag F A y ∈ diagSubfield F A := by
  refine Submodule.span_induction
    (p := fun y _ => phiDiag F A y ∈ diagSubfield F A) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨m, rfl⟩
    rw [phiDiag_zMono]
    exact Subfield.subset_closure (Or.inr ⟨m, rfl⟩)
  · rw [map_zero]
    exact Subfield.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Subfield.add_mem _ hx hy
  · intro c x _ hx
    rw [Algebra.smul_def, map_mul, AlgHom.commutes (phiDiag F A) c]
    exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inl ⟨c, rfl⟩)) hx

end PhiDiag

/-! ## 公理闸门 -/

#print axioms diagMono_zero
#print axioms phiDiag
#print axioms phiDiag_zMono
#print axioms phiDiag_mem_diagSubfield_of_span

end

end EM

end ABGV52
