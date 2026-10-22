/-
  Procesi —— **外部件（移植）：`TauCeti/TensorProduct/Mul.lean`**

  来源（Apache-2.0）：仓库 `https://github.com/TauCetiProject/TauCeti`，本地全库快照
  `raw/TauCeti/`（pin `7d75b962595a1a981ef8687e261d9436b4adc7a2`，登记于
  `scripts/lean-recon-roster.tsv`）；原文件 `raw/TauCeti/TauCeti/TensorProduct/Mul.lean`。
  TauCeti 侧 mathlib pin 为 `ccbef15e…`，本工作区为 `aa35a481…`；本件实测在本 pin 上编译通过。

  **移植改动（逐项列全）**：① 去 Lean `module` 标记；② `public import` → `import`；
  ③ 删 `public section`；④ TauCeti 内部 import 路径改为本工程 vendored 件
  （`TauCeti.Algebra.*` → `Procesi.External.*`，见下）；⑤ 本头注与末尾 `#print axioms`
  由本工作区追加。**数学与陈述无任何改动。**

  **为何移植（用户令 2026-10-22「已有 `lem:1.1.16` 的等价物就先用已有的」）**：
  本件给 `IsSimpleRing (A ⊗[K] B)`（`A` 中心单、`B` 单）——即 AGPR2020 `lem:1.1.16`
  的等价物。R732 曾自建同一引理（`Procesi/SimpleTensor.lean` 原 265 行证明，已按用户令
  **撤下**，改为消费本件）。见 [[proj-lean-external-recon-protocol]] §11.2。
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Multiplying pure tensors in `A ⊗[K] B`

Multiplication formulas and anticommutation criteria for `A ⊗[K] B` over a commutative
semiring. The anticommutation criteria need only nonunital, nonassociative semirings whose
multiplication is bilinear over `K`. The formulas for multiplication by `a ⊗ₜ 1` use a
`K`-algebra `A` and a possibly nonassociative semiring `B` with `K`-bilinear multiplication.

## Main results

* `Algebra.TensorProduct.tmul_one_mul_eq_smul`: multiplying on the left by `a ⊗ₜ 1` is the left
  `A`-module action on `A ⊗[K] B`.
* `Algebra.TensorProduct.basis_repr_mul_tmul_one`: multiplying on the right by `a ⊗ₜ 1` multiplies
  each coordinate against `Algebra.TensorProduct.basis` by `a` on the right.
* `Algebra.TensorProduct.tmul_anticommute_of_left` and
  `Algebra.TensorProduct.tmul_anticommute_of_right`: pure tensors anticommute when the factors
  on one side anticommute and the factors on the other side commute.
-/


open scoped TensorProduct

namespace Algebra.TensorProduct

variable {K A B ι : Type*} [CommSemiring K]

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring A] [Module K A] [SMulCommClass K A A] [IsScalarTower K A A]
  [NonUnitalNonAssocSemiring B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]

/-- Pure tensors anticommute when their left factors anticommute and right factors commute. -/
theorem tmul_anticommute_of_left {x x' : A} {y y' : B}
    (hx : x * x' + x' * x = 0) (hy : Commute y y') :
    x ⊗ₜ[K] y * x' ⊗ₜ y' + x' ⊗ₜ y' * x ⊗ₜ y = 0 := by
  simp only [tmul_mul_tmul, hy.eq, ← TensorProduct.add_tmul, hx, TensorProduct.zero_tmul]

/-- Pure tensors anticommute when their left factors commute and right factors anticommute. -/
theorem tmul_anticommute_of_right {x x' : A} {y y' : B}
    (hx : Commute x x') (hy : y * y' + y' * y = 0) :
    x ⊗ₜ[K] y * x' ⊗ₜ y' + x' ⊗ₜ y' * x ⊗ₜ y = 0 := by
  simp only [tmul_mul_tmul, hx.eq, ← TensorProduct.tmul_add, hy, TensorProduct.tmul_zero]

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring A] [Algebra K A]
  [NonAssocSemiring B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]

/-- Left multiplication by `a ⊗ₜ 1` on `A ⊗[K] B` is the left `A`-module action, the one that
`Algebra.TensorProduct.basis` is a basis for. This identifies `a ⊗ₜ 1` with `a • 1` in
`smul_one_mul`, and does not require `A` to be commutative. -/
@[simp]
theorem tmul_one_mul_eq_smul (a : A) (x : A ⊗[K] B) :
    (a ⊗ₜ[K] (1 : B)) * x = a • x := by
  simpa [one_def, TensorProduct.smul_tmul'] using smul_one_mul a x

variable (𝓑 : Module.Basis ι K B)

/-- Multiplying by `a ⊗ₜ 1` on the right multiplies each coordinate of `x` by `a` on the right.

Unlike the left-handed `Algebra.TensorProduct.tmul_one_mul_eq_smul` this is not an instance of the
generic scalar-action API, since right multiplication is not the module action
`Algebra.TensorProduct.basis` is a basis for. -/
@[simp]
theorem basis_repr_mul_tmul_one (a : A) (x : A ⊗[K] B) (j : ι) :
    (basis A 𝓑).repr (x * (a ⊗ₜ[K] (1 : B))) j = (basis A 𝓑).repr x j * a := by
  induction x using TensorProduct.inductionOn with
  | tmul a' b => simp [mul_assoc, ← Algebra.commutes]
  | add x y hx hy => simp [add_mul, hx, hy]

end Semiring

end Algebra.TensorProduct

