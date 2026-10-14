/-
  ABGV-5.2 —— 论文 2026-10-11 版 §4：`thm:retract-criterion`（4.12）的**具名假设接口**

  论文原文（4.12）：设 `G` 有限、`M` 忠实 `ℤ[G]`-格、`char F = 0`，则 `F(M)^G` 在 `F` 上
  retract rational **当且仅当** flasque 类 `ρ(M)` 是可逆格的类。论文随后明说：文献中的
  判据是对**扭转**不变量域 `Q(L/K,M)` 陈述的（Saltman 1984 Thm 3.14(a)），而 `F(M)^G`
  这一支**按假设使用**（"for it the criterion is an assumption rather than a quotation of
  a proved result"）⟹ 本件按 `EM_ABGV52`／`Saltman_ABGV52` 的工艺给出**具名假设**：

    * `RetractCriterionHyp` —— 判据的**定义外形**（对给定的 flasque 消解
      `R : FlasqueResolution H M`，其右端项 `R.F` 的相似类即 `ρ(M)`；域 `K` 的角色是
      `F(M)^G`；抽象谓词 `RRat` 的角色是「在 `F` 上 retract rational」，由调用方以
      `IsRetractRational F` 填入）；
    * **类型锁定断言**（`rfl`）：外形一旦改动立即编译失败；
    * **接线定理**：正方向（`RRat K ⟹ R.F` 可逆）与**负方向**（4.13 实际使用的
      `¬ R.F` 可逆 `⟹ ¬ RRat K`）；
    * **非空洞探针**（L1）：假设类**非空**——取 `RRat := fun _ => IsInvertible H R.F`
      即得实例（同义反复型见证），并且负方向接线对任意 `R` 可点火；
    * 公理闸门 `#print axioms`。

  与「类」这一层的接口约定：论文写的是「`ρ(M)` **是**可逆格**的类**」；本件把接口钉在
  **给定代表元** `R.F` 上（避免引入 `D(G)/S(G)` 商类型）。代表元无关性由 `Flasque_ABGV52`
  的 `FlasqueClassWellDefinedHyp`（CTS77 §1 Lemme 5）承担，见该件 §3。

  **无 sorry、无自造公理**。
-/
import ABGV52.Flasque_ABGV52
import ABGV52.SaltDef_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## §1 具名假设外形 ＋ 类型锁定 -/

/-- **`thm:retract-criterion`（4.12）的具名假设**：`M` 的 flasque 消解 `R`（`R.F` 的相似类
即 `ρ(M)`）与域 `K`（角色 = `F(M)^G`）之下，`RRat K`（角色 = `K` 在 `F` 上 retract
rational）成立 **当且仅当** `R.F` 可逆（是置换格的直和项）。 -/
def RetractCriterionHyp (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) (RRat : Type → Prop) : Prop :=
  RRat K ↔ IsInvertible H R.F

/-- **类型锁定断言**：`RetractCriterionHyp` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M) (K : Type) (RRat : Type → Prop) :
    RetractCriterionHyp M R K RRat ↔ (RRat K ↔ IsInvertible H R.F) :=
  Iff.rfl

/-! ## §2 接线（正方向与负方向） -/

/-- **接线（正方向）**：`RRat K` 与「`ρ(M)` 可逆」等价的正向——由判据假设得 `R.F` 可逆。 -/
theorem retractCriterion_mp {M : Rep.{0,0,0} ℤ H} {R : FlasqueResolution H M}
    {K : Type} {RRat : Type → Prop} (h : RetractCriterionHyp M R K RRat)
    (hRR : RRat K) : IsInvertible H R.F :=
  h.mp hRR

/-- **接线（负方向，`thm:not-retract-rational`（4.13）实际使用的方向）**：
若 `ρ(M)` 的代表元 `R.F` **不**可逆，则 `RRat K` 不成立。 -/
theorem retractCriterion_not {M : Rep.{0,0,0} ℤ H} {R : FlasqueResolution H M}
    {K : Type} {RRat : Type → Prop} (h : RetractCriterionHyp M R K RRat)
    (hInv : ¬ IsInvertible H R.F) : ¬ RRat K :=
  fun hRR => hInv (h.mp hRR)

/-! ## §3 非空洞探针（L1） -/

/-- **探针 1（假设类非空）**：把 `RRat` 取为「`R.F` 可逆」这一命题本身，判据的同义反复
实例成立——假设类不是空类，`RetractCriterionHyp` 的外形可被真实填入。 -/
theorem retractCriterionHyp_satisfiable (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) : RetractCriterionHyp M R K (fun _ => IsInvertible H R.F) :=
  Iff.rfl

/-- **探针 2（负方向接线可点火）**：在探针 1 的实例上，只要 `R.F` 不可逆，
`retractCriterion_not` 即给出否定结论——接线不是空转。 -/
theorem retractCriterion_not_probe (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) (hInv : ¬ IsInvertible H R.F) :
    ¬ (fun _ => IsInvertible H R.F) K :=
  retractCriterion_not (retractCriterionHyp_satisfiable M R K) hInv

/-! ## §4 公理闸门 -/

#print axioms retractCriterion_mp
#print axioms retractCriterion_not
#print axioms retractCriterionHyp_satisfiable
#print axioms retractCriterion_not_probe

end ABGV52
