/-
  ABGV-5.2 · B 档 W1a —— **Fischer 接口（正则表示场档）**（2026-10-11）

  **来源** ✓：Gille–Szamuely 2017，label `thm-fischer`（`raw/GilleSzamuely2017.tex:9016–9021`
  逐字核验 ✓；**⚠-tex-sourced** ✗ —— PDF 孪生件在库 ✓，升核须回 PDF 目视 ✓）。
  **射程** ✓：只落**正则表示场** `V = F[A]` 档（论文合法 Cor 3.13 实例所需 ✓，ProcConsume 顶横幅 ✓）；
  **不**声称一般 `V` 档 ✓，**不**声称 Fischer 已被证明 ✓（落成**类型锁定假设** ✓）。
  **载体口径** ✓：定义一律 `[Group A]`（`[CommGroup A]` 报 `cannot coerce to sort` ✗）；分式域上的作用**不需要** ✗
  （不变量域取「不变量环的分式域」✓，其 `Algebra F` 由**手工实例**供给 ✓，绕开 `SMulCommClass` 心跳爆炸 ✗）。
  **无 sorry、无自造公理** ✓；公理门见文末 ✓。
-/
import ABGV52.TateLayer_ABGV52
import ABGV52.SaltDef_ABGV52
import ABGV52.SaltT2_ABGV52
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.FractionRing
open CategoryTheory
noncomputable section

universe u

namespace ABGV52.BTier

variable {F : Type*} [Field F]
variable {A : Type*} [Group A] [Fintype A]

/-- 正则表示：`A` 左乘置换基 ⟹ 多项式环上的换元自同构 ✓。 -/
def regRename (a : A) : MvPolynomial A F ≃ₐ[F] MvPolynomial A F :=
  MvPolynomial.renameEquiv F (Equiv.mulLeft a)

/-- `A →* Aut_F F[x_a]` ✓。 -/
def regRenameHom : A →* (MvPolynomial A F ≃ₐ[F] MvPolynomial A F) where
  toFun := regRename
  map_one' := by ext p : 1; simp [regRename]
  map_mul' := by intro a b; ext p : 1; simp [regRename, Equiv.mulLeft_mul]

/-- **多项式环上的正则换元作用**（六字段全证 ✓）。 -/
instance : MulSemiringAction A (MvPolynomial A F) where
  smul a p := regRename a p
  one_smul p := by show regRename 1 p = p; simp [regRename]
  mul_smul a b p := by
    show regRename (a * b) p = regRename a (regRename b p); simp [regRename, Equiv.mulLeft_mul]
  smul_zero a := map_zero (regRename a)
  smul_add a p q := map_add (regRename a) p q
  smul_mul a p q := map_mul (regRename a) p q
  smul_one a := map_one (regRename a)

/-- 不变量**子环** ✓。 -/
def regInvariantSubring : Subring (MvPolynomial A F) :=
  FixedPoints.subring (MvPolynomial A F) A

/-- 换元的 `F`-线性 ✓（手工 `Algebra` 实例的引擎 ✓）。 -/
lemma regRename_smul (a : A) (f : F) (p : MvPolynomial A F) :
    regRename a (f • p) = f • regRename a p := map_smul (regRename a) f p

/-- **不变量子环上的 `F`-代数结构**（**手工** ✓，绕开 `SMulCommClass` 的心跳爆炸 ✗）。 -/
instance : Algebra F ↥(regInvariantSubring (F := F) (A := A)) where
  smul f x := ⟨f • (x : MvPolynomial A F), by
    show ∀ a : A, regRename a (f • (x : MvPolynomial A F)) = f • (x : MvPolynomial A F)
    intro a
    rw [regRename_smul]
    exact congrArg (fun p => f • p) (x.2 a)⟩
  algebraMap := (algebraMap F (MvPolynomial A F)).codRestrict regInvariantSubring (by
    intro f
    show ∀ a : A, regRename a (algebraMap F (MvPolynomial A F) f) = algebraMap F (MvPolynomial A F) f
    intro a
    rw [show (algebraMap F (MvPolynomial A F)) f = f • (1 : MvPolynomial A F) from by
      rw [Algebra.smul_def]; simp]
    rw [map_smul, map_one])
  commutes' := by intro f x; ext m; ring_nf
  smul_def' := by
    intro f x
    apply Subtype.ext
    show f • (x : MvPolynomial A F) = ((algebraMap F (MvPolynomial A F)) f) * (x : MvPolynomial A F)
    rw [MvPolynomial.smul_eq_C_mul]
    rfl

/-- **正则表示场的不变量域**（载体 ✓）：不变量子环的**分式域** ✓（`Algebra F` 由上面的手工实例供给 ✓）。 -/
abbrev regInvariantFieldAlt :=
  FractionRing ↥(regInvariantSubring (F := F) (A := A))

/-- **Fischer 型输入**（正则档，**类型锁定假设** ✓）：`F` 特征 0、`A` 有限**交换**（`[CommGroup A]` ✓）
按正则表示忠实线性作用 ⟹ 不变量域有理（源结论更强：**纯超越** ✓）。
**⚠-tex-sourced** ✗（label `thm-fischer` ✓）。 -/
def FischerRegularHyp (F : Type*) [Field F] [CharZero F]
    (A : Type*) [CommGroup A] [Fintype A] : Prop :=
  EM.IsRational F (regInvariantFieldAlt (F := F) (A := A))

/-- **类型锁定**：外形一旦改动，本 `rfl` 立即编译失败 ✓。 -/
theorem fischerRegularHyp_typeLock (F : Type*) [Field F] [CharZero F]
    (A : Type*) [CommGroup A] [Fintype A] :
    (FischerRegularHyp F A) = EM.IsRational F (regInvariantFieldAlt (F := F) (A := A)) := rfl

/-- **非空洞探针（L1）** ✓：假设类非空 —— `ℚ`（`CharZero` ✓）、`PUnit`（交换有限 ✓）可实例化 ✓。 -/
theorem fischerRegularHyp_data_nonempty :
    Nonempty (CharZero ℚ) ∧ Nonempty (CommGroup PUnit) ∧ Nonempty (Fintype PUnit) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- **接线** ✓（**新定理**，旧接口 `SaltmanHyp` **一字未动** ✗）：Fischer（正则档 ✓）给出 \(F(V)^A\) 有理 ⟹
经 T2 桥 `isRetractRational_of_isRational` ✓ 得 **retract rational** —— 即论文**合法 Cor 3.13 实例**
（正则表示场 ✓）的**结论位** ✓（`RRet` 位在此取 `IsRetractRational F` ✓）。
**注** ✗：本定理**不**声称 `SaltmanHyp` 本身成立 ✗（后者另含 `M_H_rep.ρ` 单射前提与 Saltman 1982 §1 泛对象残块 ✗）。 -/
theorem isRetractRational_regularInvariants_of_fischer (F : Type u) [Field F] [CharZero F]
    (A : Type u) [CommGroup A] [Fintype A] (h : FischerRegularHyp F A) :
    IsRetractRational F (regInvariantFieldAlt (F := F) (A := A)) :=
  isRetractRational_of_isRational h

/-- **登记的桥** ✗：`Frac(R^G) = Frac(R)^G`（有限群按自同构作用 ✓，标准事实 ✓）——本件未证 ✗。 -/
theorem fracInvariants_bridge_gap_registered : True := trivial

/-! ## 公理闸门 -/

#print axioms isRetractRational_regularInvariants_of_fischer
#print axioms fischerRegularHyp_typeLock
#print axioms fischerRegularHyp_data_nonempty
#print axioms fracInvariants_bridge_gap_registered

end ABGV52.BTier
