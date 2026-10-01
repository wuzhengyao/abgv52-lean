/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-vi：③ 的度数收口（第一环）**

  目标：**`F(Y) = F(M)^A`**（`F(Y)` := 由 `diagMono m`（`m ∈ Y`）生成的子域）。

  **⚠ 本轮实际交付面（如实登记，不含 sorry）**：本件**只落第一环** ——

    * `repMono`：**陪集代表单项式** `z^χ := diagMono (single χ 1)`（待 1β-vii 的陪集展开用）；
    * **`diagSubfield := F(Y)`**：`F(Y)` 的子域定义；
    * **`diagSubfield_le_invariants`**：**`F(Y) ⊆ F(M)^A`**（逐生成元用 D6 的 `diagMono_mem_invariants`）。

  **未做（余量，见 wiki §3j）**：
    ① **陪集分解恒等式** `m = single (charOf m) 1 + μ`（`μ ∈ Y`）⟹ `diagMono m = repMono (charOf m) · diagMono μ`
       —— 草稿已写，末步 `abel` 未过编译，本轮**撤下**（不留 sorry）；
    ② `F(Y)`-张成 `repSpan` ＋ **有限维整环 ⟹ 域** ⟹ `[F(M) : F(Y)] ≤ |A|`（span 机件，API 摩擦未清）；
    ③ `Subfield.relfinrank` 塔 ⟹ `F(Y) = F(M)^A`；
    ④ `IsRational F ↥(latticeInvariantsAlg F A (A → ℤ))`（需 `Y ≅ ℤ^{|A|}` 的显式基；
       `Submodule.basisOfPid` 在库，接线未做）。
-/
import ABGV52.D8_ABGV52

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

section Diag

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **陪集代表单项式** `z^χ := diagMono (single χ 1)`（`χ` 跑特征群，恰为陪集代表系）。 -/
noncomputable def repMono (χ : MulChar A F) : latticeFunctionField F (A → ℤ) :=
  diagMono F A (Finsupp.single χ 1)

/-- **`F(Y)`**：由 `diagMono m`（`m ∈ Y`）**与 `F`-纯量**生成的子域（Fischer 证明中的 `k(Y)`）。

**注**：`F`-纯量必须显式入生成集 —— `Subfield.closure` 不含 `F` 的像（`Algebra F ↥·` 无实例），
而收口链要靠 `F`-纯量送进张成（见 D10）。 -/
noncomputable def diagSubfield : Subfield (latticeFunctionField F (A → ℤ)) :=
  Subfield.closure (Set.range (algebraMap F (latticeFunctionField F (A → ℤ))) ∪
    Set.range fun m : ↥(kernelLattice F A) => diagMono F A (m : expVector F A))

/-- **`F(Y) ⊆ F(M)^A`**（D6 的 `diagMono_mem_invariants` 升到子域层）。 -/
theorem diagSubfield_le_invariants :
    diagSubfield F A ≤ latticeInvariants F A (A → ℤ) := by
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨c, rfl⟩ | ⟨m, rfl⟩)
  · rw [latticeInvariants_carrier_eq]
    change algebraMap F (latticeFunctionField F (A → ℤ)) c ∈ latticeInvariantsAlg F A (A → ℤ)
    rw [mem_latticeInvariantsAlg_iff]
    intro g
    exact smul_algebraMap_latticeFunctionField F A (A → ℤ) g c
  · rw [latticeInvariants_carrier_eq]
    exact diagMono_mem_invariants F A m.2

end Diag

/-\! ## 公理闸门 -/

#print axioms repMono
#print axioms diagSubfield
#print axioms diagSubfield_le_invariants

end

end EM

end ABGV52
