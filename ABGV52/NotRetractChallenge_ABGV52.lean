/-
  ABGV-5.2 —— 独立重写件（**零 import 主链**，仿 `Challenge_ABGV52.lean`）：
  论文 2026-10-11 版 §2／§4 新命题的**陈述与接线**的独立复述。

  口径
  ====
  * 本文件**不** import 工程内任何文件（只 import Mathlib）：全部谓词与接口在此
    **独立复述**（命名与主链一致，便于逐条比对，但定义体独立写出）。
  * 复述范围（与主链 `Flasque_ABGV52`／`RetractCrit_ABGV52`／`NotRetract_ABGV52` 对应）：
      `def:flasque-coflasque`（flasque／coflasque）、`def:flasque-class`（相似／可逆）、
      `prop:flasque-resolution` 的外形与具名假设、`lem:invertible-coflasque`（2.6，
      顶层形与全子群形的**前提接口**）、`thm:retract-criterion`（4.12 具名假设）、
      `thm:not-retract-rational`（4.13）的**装配骨架**。
  * **与主链的差别（诚实登记）**：4.13 中依赖工程既有重对象的部分
    （`M_H_rep`、`EM.latticeInvariants`、`ProcHyp.ProcesiHypExact`、LES 机器）
    无法在零 import 下复述，故此处只独立复述**逻辑骨架**：把「非 coflasque ⟹
    `ρ` 不可逆 ⟹ 由 4.12 非 retract rational ⟹ 沿 `≃ₐ[F]` 搬运到 `Z`」这条链的
    每一步写成独立定理，其中的数学输入以**显式前提**给出（不假装已证）。
  * **无 sorry、无自造公理**（与 `Challenge_ABGV52` 用 `sorry` 作陈述锁的做法不同：
    本波硬约束要求新文件 sorry 计数为 0，故陈述锁改由 `Prop` 值定义 ＋ 可证接线承担）。
-/
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Algebra.Equiv

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## §1 独立复述：群、格、上同调读数 -/

/-- `C_3`（乘法写法）。 -/
abbrev C3 : Type := Multiplicative (ZMod 3)

/-- 论文的群 `H = C_3 × C_3`。 -/
abbrev H : Type := C3 × C3

/-- `coh^q(G, M)`。 -/
noncomputable abbrev coh (G : Type) [Group G] (M : Rep ℤ G) (q : ℕ) : Type :=
  (groupCohomology M q : Type)

/-- **置换 `ℤ[G]`-格**（一般群）。 -/
def IsPermutationLattice (G : Type*) [Group G] (P : Rep ℤ G) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : MulAction G X),
    Nonempty (P ≅ Rep.ofMulAction ℤ G X)

/-- **flasque**（论文 `def:flasque-coflasque`）：`Ĥ^{-1}(K,M) = 0` 对一切 `K ≤ G`。 -/
def IsFlasque (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∀ K : Subgroup G,
    Subsingleton ↥(@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K)
      (Rep.res K.subtype M) (-1))

/-- **coflasque**（论文 `def:flasque-coflasque`）：`coh¹(K,M) = 0` 对一切 `K ≤ G`。 -/
def IsCoflasque (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∀ K : Subgroup G, Subsingleton ↥(groupCohomology (Rep.res K.subtype M) 1)

/-- **相似**（论文 `def:flasque-class`）。 -/
def IsSimilar (G : Type) [Group G] (M N : Rep.{0,0,0} ℤ G) : Prop :=
  ∃ (S₁ S₂ : Rep.{0,0,0} ℤ G),
    IsPermutationLattice G S₁ ∧ IsPermutationLattice G S₂ ∧
      Nonempty (M ⊞ S₁ ≅ N ⊞ S₂)

/-- **可逆**（论文 `def:flasque-class`）：置换格的直和项。 -/
def IsInvertible (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∃ (N P : Rep.{0,0,0} ℤ G), IsPermutationLattice G P ∧ Nonempty (M ⊞ N ≅ P)

/-- **flasque 消解**（论文 `prop:flasque-resolution`）。 -/
structure FlasqueResolution (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) where
  /-- 消解右端 `F`（其相似类即 `ρ(M)`）。 -/
  F : Rep.{0,0,0} ℤ G
  /-- 消解中间项 `P`（置换格）。 -/
  P : Rep.{0,0,0} ℤ G
  /-- `M ↪ P`。 -/
  iota : M ⟶ P
  /-- `P ↠ F`。 -/
  pi : P ⟶ F
  /-- `ι` 单射。 -/
  injective_iota : Function.Injective iota
  /-- `ι`、`π` 正合。 -/
  exact : Function.Exact iota pi
  /-- `π` 满射。 -/
  surjective_pi : Function.Surjective pi
  /-- `P` 置换。 -/
  perm : IsPermutationLattice G P
  /-- `F` flasque。 -/
  flasque : IsFlasque G F

/-! ## §2 独立复述：retract rationality（Saltman def3.1 形）与 4.12 的具名假设 -/

/-- **retract rational**（Saltman def3.1 的独立副本）。 -/
def IsRetractRational (F K : Type u) [Field F] [Field K] [Algebra F K] : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra F S)
    (_ : Algebra S K) (_ : IsScalarTower F S K) (_ : IsFractionRing S K),
    ∃ (n : ℕ) (w : MvPolynomial (Fin n) F) (_ : w ≠ 0),
      ∃ (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S),
        ψ.comp φ = AlgHom.id F S

/-- **`thm:retract-criterion`（4.12）的具名假设**（独立副本）。 -/
def RetractCriterionHyp (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) (RRat : Type → Prop) : Prop :=
  RRat K ↔ IsInvertible H R.F

/-! ## §3 独立复述：装配骨架（每一步都可证／以显式前提给出） -/

/-- **4.12 负方向接线**（独立副本；4.13 实际使用的方向）。 -/
theorem retractCriterion_not {M : Rep.{0,0,0} ℤ H} {R : FlasqueResolution H M}
    {K : Type} {RRat : Type → Prop} (h : RetractCriterionHyp M R K RRat)
    (hInv : ¬ IsInvertible H R.F) : ¬ RRat K :=
  fun hRR => hInv (h.mp hRR)

/-- **2.6 的逆否用法**（独立副本）：若「可逆 ⟹ 顶层 `coh¹` 消没」成立，则
顶层 `coh¹` 不消没 ⟹ `ρ(M)` 不可逆。 -/
theorem not_isInvertible_of_not_subsingleton {M : Rep.{0,0,0} ℤ H}
    (h26 : IsInvertible H M → Subsingleton ↥(groupCohomology M 1))
    (h : ¬ Subsingleton ↥(groupCohomology M 1)) : ¬ IsInvertible H M :=
  fun hInv => h (h26 hInv)

/-- **4.13 的收口（独立副本）**：`K ≅ L` 且 `L` retract
rational ⟹ `K` retract rational。主链该步已真证（`SaltT2_ABGV52.IsRetractRational.of_algEquiv`）；
本件在零 import 下把它作为**显式前提** `htrans` 接入（不假装已证）。 -/
theorem not_retractRational_of_algEquiv {F K Z : Type} [Field F] [Field K] [Field Z]
    [Algebra F K] [Algebra F Z] (e : Z ≃ₐ[F] K)
    (htrans : IsRetractRational F Z → IsRetractRational F K)
    (h : ¬ IsRetractRational F K) : ¬ IsRetractRational F Z :=
  fun hZ => h (htrans hZ)

/-- **独立陈述锁（2.6）**：论文 `lem:invertible-coflasque` 的逐字形（全子群）。 -/
def InvertibleCoflasqueStatement (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ M : Rep.{0,0,0} ℤ G, IsInvertible G M → IsCoflasque G M

/-- **独立陈述锁（4.13）**：论文 `thm:not-retract-rational` 的装配骨架形
（LES 侧否定结论 ＋ 4.12 具名假设 ＋ 几何识别 ⟹ 结论）。 -/
def NotRetractRationalStatement (F K Z : Type) [Field F] [Field K] [Field Z]
    [Algebra F K] [Algebra F Z] : Prop :=
  ∀ (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M),
    (¬ IsInvertible H R.F) → RetractCriterionHyp M R K (fun _ => IsRetractRational F K) →
      (Z ≃ₐ[F] K) → ¬ IsRetractRational F Z

/-- **陈述锁点火**：`NotRetractRationalStatement` 可由本件的装配定理**直接推出**
（非空洞：该 `Prop` 不是无法使用的形状）。 -/
theorem notRetractRationalStatement_holds (F K Z : Type) [Field F] [Field K] [Field Z]
    [Algebra F K] [Algebra F Z]
    (htrans : IsRetractRational F Z → IsRetractRational F K) :
    NotRetractRationalStatement F K Z :=
  fun M R hInv hCrit hgeo =>
    not_retractRational_of_algEquiv hgeo htrans
      (retractCriterion_not (M := M) hCrit hInv)

/-- **非空洞探针（L1）**：4.12 具名假设类非空（`RRat := fun _ => IsInvertible H R.F`）。 -/
theorem retractCriterionHyp_satisfiable (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) : RetractCriterionHyp M R K (fun _ => IsInvertible H R.F) :=
  Iff.rfl

/-! ## §4 公理闸门 -/

#print axioms retractCriterion_not
#print axioms not_isInvertible_of_not_subsingleton
#print axioms not_retractRational_of_algEquiv
#print axioms notRetractRationalStatement_holds
#print axioms retractCriterionHyp_satisfiable

end ABGV52
