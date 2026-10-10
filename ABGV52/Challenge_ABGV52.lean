/-
  ABGV-5.2 —— B 档 · **独立重写**（challenge file）

  硬纪律
  ======
  * **不** import `ABGV52.Thm_ABGV52`（主陈述文件）；
  * **不** import `ABGV52.Hyp_ABGV52`（定义层）—— 否则两份文件共享同一套定义与
    锁定机制，独立重写的意义被折扣；
  * 只允许 mathlib 的四个 import（表示论 / 群上同调 / 群环 / ZMod）。

  目的：**全文件一致的替换**（例如把 `ZMod 9` 一律改成 `ZMod 3`）在主文件里照样
  编译通过；只有第二份**独立转录**能与之对照。交叉核对见
  `scripts/abgv52-lean-crosscheck.py`（含判别力自证）。

  同样**无 sorry、无自造公理**。
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic

namespace ABGV52Challenge

/-- 三阶循环群（乘法写法）。 -/
abbrev C3 : Type := Multiplicative (ZMod 3)

/-- 论文的群 `H = C_3 × C_3`。 -/
abbrev Grp9 : Type := C3 × C3

/-- 置换格：同构于某个有限 `H`-集的置换模 `Z[X]`。 -/
def PermLattice (P : Rep ℤ Grp9) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : MulAction Grp9 X),
    Nonempty (P ≅ Rep.ofMulAction ℤ Grp9 X)

/-- 稳定置换格：`L ⊕ P ≅ Q`，`P, Q` 置换。 -/
def StablyPerm (L : Rep ℤ Grp9) : Prop :=
  ∃ (P Q : Rep ℤ Grp9), PermLattice P ∧ PermLattice Q ∧ Nonempty (L ⊞ P ≅ Q)

/-- quasi-permutation（修正序列形）：存在 `0 → M → P → Q → 0`，`P`、`Q` 置换。 -/
def QuasiPerm (M : Rep ℤ Grp9) : Prop :=
  ∃ (P Q : Rep ℤ Grp9) (f : M ⟶ P) (g : P ⟶ Q),
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    PermLattice P ∧ PermLattice Q

/-- `coh^2(H, M) ≅ C_9`。 -/
noncomputable def Coh2IsNine (M : Rep ℤ Grp9) : Prop :=
  Nonempty ((groupCohomology M 2 : Type) ≃ₗ[ℤ] ZMod 9)

/-- `3` 消没 `coh^2(H, M)`（指数整除 3 的形态）。 -/
noncomputable def Coh2ExpThree (M : Rep ℤ Grp9) : Prop :=
  ∀ y : (groupCohomology M 2 : Type), (3 : ℤ) • y = 0

/-- 算术内核的另一半：`ZMod 9` 中 `3 ≠ 0`。 -/
theorem three_ne_zero_in_zmod9 : (3 : ZMod 9) ≠ 0 := by decide

/-- 算术内核：`C_9` 排除「指数整除 3」。 -/
theorem nine_excludes_exp_three (M : Rep ℤ Grp9) (h : Coh2IsNine M) :
    ¬ Coh2ExpThree M := by
  obtain ⟨e⟩ := h
  intro hexp
  have hx : e ((3 : ℤ) • e.symm 1) = e 0 := by rw [hexp (e.symm 1)]
  rw [map_zsmul, map_zero, e.apply_symm_apply, Int.smul_one_eq_cast] at hx
  exact three_ne_zero_in_zmod9 hx

/-- 判别对：`C_9` 且指数不整除 3。 -/
theorem discriminant (M : Rep ℤ Grp9) (h9 : Coh2IsNine M) :
    Coh2IsNine M ∧ ¬ Coh2ExpThree M :=
  ⟨h9, nine_excludes_exp_three M h9⟩

/-- 主链：稳定置换的指数整除性（显式假设）＋ `C_9` ⟹ 非稳定置换。 -/
theorem not_stably_perm (M : Rep ℤ Grp9)
    (exp_bound : ∀ L : Rep ℤ Grp9, StablyPerm L → Coh2ExpThree L)
    (h9 : Coh2IsNine M) : ¬ StablyPerm M :=
  fun hSP => nine_excludes_exp_three M h9 (exp_bound M hSP)

/-- 有理性侧（修正判据，序列形）：判据（`SRat K → QuasiPerm M`）＋ 非 quasi-permutation
⟹ 非稳定有理。 -/
theorem not_stably_rational (M : Rep ℤ Grp9) (K : Type) (SRat : Type → Prop)
    (hEM : SRat K → QuasiPerm M)
    (hnq : ¬ QuasiPerm M) : ¬ SRat K :=
  fun hK => hnq (hEM hK)

/-- 非空性见证：平凡表示是置换格。 -/
theorem perm_nonempty : PermLattice (Rep.ofMulAction ℤ Grp9 PUnit) :=
  ⟨PUnit, inferInstance, inferInstance, ⟨CategoryTheory.Iso.refl _⟩⟩

#print axioms three_ne_zero_in_zmod9
#print axioms nine_excludes_exp_three
#print axioms not_stably_perm
#print axioms not_stably_rational

end ABGV52Challenge
