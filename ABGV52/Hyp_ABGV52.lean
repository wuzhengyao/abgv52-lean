/-
  ABGV-5.2 —— B 档（T2 陈述锁定）· 定义层（**无 sorry、无自造公理**）

  设计原则（用户 2026-09-29 口径：「数学界讲究无 sorry」）
  ====================================================
  * **无 `sorry`**；
  * **无自造 `axiom`／`opaque`**：本文件声明的谓词一律**具体定义**；
  * 论文中 mathlib 无对应物的概念（有理性、retract 有理性、不变域），
    一律作**定理的显式参数**（不是公理）。

  与论文的对应
  ============
  H = C_3 × C_3；Z[H] = 群环；置换格 = 有限 H-集的置换模（= ⊕ Z[H/K_i]）；
  稳定置换 = L ⊕ P ≅ Q（P、Q 置换）；coh^q(H,−) = 整数群上同调。
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic

namespace ABGV52

/-- `C_3`（乘法写法）。 -/
abbrev C3 : Type := Multiplicative (ZMod 3)

/-- 论文的群 `H = C_3 × C_3`。 -/
abbrev H : Type := C3 × C3

example : Group H := inferInstance
example : Fintype H := inferInstance

/-! ## 1. 置换格与稳定置换格（**具体定义**，非接口） -/

/-- **置换 `Z[H]`-格**（论文 `def:lattice`）：同构于某个**有限 `H`-集** `X` 的置换模
`Z[X]`。这与「同构于有限直和 `⊕ Z[H/K_i]`」等价：有限 `H`-集是其轨道的无交并，
而轨道同构于 `H/K`。 -/
def IsPermutationLattice (P : Rep ℤ H) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : MulAction H X),
    Nonempty (P ≅ Rep.ofMulAction ℤ H X)

/-- **稳定置换格**（论文 `def:lattice`）：`∃ P Q` 置换，`L ⊕ P ≅ Q`。 -/
def IsStablyPermutation (L : Rep ℤ H) : Prop :=
  ∃ (P Q : Rep ℤ H), IsPermutationLattice P ∧ IsPermutationLattice Q ∧
    Nonempty (L ⊞ P ≅ Q)

/-- **quasi-permutation 格**（论文 `def:lattice` 第三项；第四十二改修正序列形）：
存在短正合列 `0 → M → P → Q → 0`（`P`、`Q` 置换格）。⊕-形一般陈述为假
（`EMCounter_ABGV52.lean`）；本定义与 `EMQuasi_ABGV52.lean` 的
`EM.IsQuasiPermutation H` 定义级同体（桥 `EM.isQuasiPermutation_iff`，`Iff.rfl`）。 -/
def IsQuasiPermutation (M : Rep ℤ H) : Prop :=
  ∃ (P Q : Rep ℤ H) (f : M ⟶ P) (g : P ⟶ Q),
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    IsPermutationLattice P ∧ IsPermutationLattice Q

/-! ## 2. 上同调读数（形态即论文结论的形态） -/

/-- `coh^q(H, M)` 作为 `Z`-模。 -/
noncomputable abbrev coh (M : Rep ℤ H) (q : ℕ) : Type :=
  (groupCohomology M q : Type)

/-- 论文 `lem:H2-MH`：`coh^2(H,M) ≅ C_9`（`ZMod 9` 具体表述）。 -/
noncomputable def Coh2IsoC9 (M : Rep ℤ H) : Prop :=
  Nonempty (groupCohomology M 2 ≃ₗ[ℤ] ZMod 9)

/-- 论文 `prop:perm-exponent` 的结论形态：`exp coh^2(H,M) ∣ 3`。 -/
noncomputable def Coh2ExpDvd3 (M : Rep ℤ H) : Prop :=
  ∀ x : coh M 2, (3 : ℤ) • x = 0

/-\! ## 公理闸门（定义层亦须过闸） -/

#print axioms IsPermutationLattice
#print axioms IsStablyPermutation
#print axioms IsQuasiPermutation
#print axioms Coh2IsoC9

end ABGV52
