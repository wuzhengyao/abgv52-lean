/-
  ABGV-5.2 —— **格前提与受限形**（A 档，2026-10-11）

  **动机**：`FlasqueResolutionHyp` 按现形为假（见 `HypRefute_ABGV52`），根因是它把 `M`
  取成**任意** `ℤ[G]`-模。本件（**不改旧 `def`** ✗）新增**格谓词**，并给出可立即证成的
  受限形，把真正的卡点逐字登记。

  **无 sorry、无自造公理**；公理门见 §3。
-/
import ABGV52.HypRefute_ABGV52

namespace ABGV52

open CategoryTheory

/-! ## §1 格谓词（新增；旧接口不动 ✗） -/

/-- **格**（lattice，CTS77 语境的 `ℤ[G]`-格）：无挠 `ℤ`-模。本件取「无挠」为核心性质
（有限生成性在本工程各用例中另由具体构造给出）。 -/
def IsLattice (G : Type) [Group G] (M : Rep.{0, 0, 0} ℤ G) : Prop :=
  Module.IsTorsionFree ℤ ↥M

/-- **类型锁定断言**：`IsLattice` 外形一旦改动，本 `Iff.rfl` 立即编译失败。 -/
example (G : Type) [Group G] (M : Rep.{0, 0, 0} ℤ G) :
    IsLattice G M ↔ Module.IsTorsionFree ℤ ↥M := Iff.rfl

/-- **非空洞对照（L1）** ✓：置换格是格（`Module.IsTorsionFree` 实例可直接合成，
已在 `HypRefute_ABGV52` 的证明中用到 ✓）——故 `IsLattice` 不是空类。 -/
theorem isLattice_ofMulAction (G : Type) [Group G] (X : Type) [Fintype X] [MulAction G X] :
    IsLattice G (Rep.ofMulAction ℤ G X) :=
  (inferInstance : Module.IsTorsionFree ℤ ↥(Rep.ofMulAction ℤ G X))

/-- **登记（未证）** ✗：`EM.IsPermutationLattice G M → IsLattice G M`（置换格无挠）——
需把置换模的无挠性沿 `Rep` 同构**搬运**到 `M`；本轮实测的障碍与 `HypRefute` 同源：
`↑(Rep.ofMulAction ℤ G X)` 与 `X →₀ ℤ` **不是** definitionally 相等 ✗，且 `Rep` iso 的
线性等价桥（`Module.IsTorsionFree` 沿 `≃ₛₗ` 搬运）尚未打通 ✗。**本件不假装证明** ✗。 -/
theorem isLattice_of_isPermutationLattice_gap_registered : True := trivial

/-! ## §2 **格版受限形**（论文 `prop:flasque-resolution` 的对应物 ✓）

**背景** ✓（2026-10-11 用户问答后确立的区分）：论文 `wiki/ABGV-5.2-resolution.tex:529` 的
`prop:flasque-resolution` 断言的是「**`ℤ[G]`-格** \(M\) 有 flasque 消解」（引 CTS77 §1 Lemme 3 ✓），
而工程原先把接口写成**无格前提**的 `FlasqueResolutionHyp` ✗ —— 后者已被**形式证伪** ✓
（`HypRefute_ABGV52.not_flasqueResolutionHyp` ✓，实案 \(M=\mathbb{Z}/2\)、平凡群）。
本节的受限形即**接口收窄**后的版本 ✓。 -/

/-- **格版受限形** ✓：**格**（无挠 `ℤ[G]`-模）有 flasque 消解 —— 即论文的 `prop:flasque-resolution` 前半 ✓。 -/
def FlasqueResolutionLatticeHyp (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ M : Rep.{0,0,0} ℤ G, IsLattice G M → Nonempty (FlasqueResolution G M)

/-- **类型锁定断言**（`FlasqueResolutionLatticeHyp`）：外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem flasqueResolutionLatticeHyp_typeLock (G : Type) [Group G] [Fintype G] :
    (FlasqueResolutionLatticeHyp G)
      = (∀ M : Rep.{0,0,0} ℤ G, IsLattice G M → Nonempty (FlasqueResolution G M)) := rfl

/-- **收窄关系** ✓：放宽版 ⟹ 受限版（格前提只是多一个假设 ✓）。
⚠ 注意本蕴含**前件为假** ✗（`not_flasqueResolutionHyp` ✓），故它是**空洞真** ✓ ——
它的作用是把「**放宽版比论文所需更强**」这件事形式化 ✓。 -/
theorem flasqueResolutionLatticeHyp_of_hyp (G : Type) [Group G] [Fintype G]
    (h : FlasqueResolutionHyp G) : FlasqueResolutionLatticeHyp G :=
  fun _ _ => h _

/-- **登记（未证）** ✗：`FlasqueResolutionLatticeHyp` 本身（＝ CTS77 §1 Lemme 3 的格版 ✓）——
当前域类内**无** mathlib 支撑：需 flasque 类的双有理不变性（B 档 ✓）或直接引用 CTS77 ✓。
**非空洞性** ✓ 由 `isLattice_ofMulAction`（§1 ✓，置换格是格）保证假设类非空 ✓。 -/
theorem flasqueResolutionLatticeHyp_gap_registered : True := trivial

/-- **登记（未证）** ✗：正例对照（某非空格确有消解）—— 需要**零对象**
（`F` 端取零模）；本轮实测：`Rep.{0,0,0} ℤ G` **无可直接用 `Zero` 实例** ✗
（`0 : Rep ℤ G` 报 `failed to synthesize OfNat`），且 `Rep.ofMulAction ℤ G PEmpty` 的
底层类型不可 defeq 展开（同族障碍 ✗）。 -/
theorem positive_control_gap_registered : True := trivial

/-! ## §3 公理闸门 -/

#print axioms isLattice_ofMulAction
#print axioms isLattice_of_isPermutationLattice_gap_registered
#print axioms isLattice_ofMulAction
#print axioms flasqueResolutionLatticeHyp_of_hyp
#print axioms flasqueResolutionLatticeHyp_gap_registered
#print axioms positive_control_gap_registered

end ABGV52
