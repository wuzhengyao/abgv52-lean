/-
  Procesi —— **H2（Procesi 几何识别）陈述层**（T2 陈述锁定）

  源（只读；`raw/` 不得编辑）：
    * `raw/ABGV-5.2-resolution.pre44.tex:734–760`（`rem:procesi-geometric`，逐字）；
    * `raw/AGPR2020.tex` §14.4.1（label `thm:14.4.4`、`cor:14.4.5`）——中心 = 不变量环的
      分式域 ＋ trdeg 公式 `(m-1)n²+1`；
    * 论文 §"The Procesi Lattice"（`:664–733`）：`U = ℤ[Ω]`、`M = ker φ`、`M ⊕ U` 秩 82。

  本件**只锁陈述**，不证定理。三段：
    §1 AGPR2020 的 trdeg 公式 ＋ 与格层秩账的**机器核对**（82 = 82）；
    §2 载体与类型锁（`U`／`M`／`M ⊕ U`／不变量域）；
    §3 H2 的两个形态（`S_9` 层忠实形／任意子群形）＋ L1 非空洞见证。

  口径：locator 一律写 **label**（`pdf_number` 不作主锚，L41）。
  格层构造本身**不复刻**：它是 `ABGV52.ProcLat`／`ABGV52.G` 的机检资产（同 pin 工具链，
  见 `wiki/log.md` 2026-10-18 条目），本工作区按 L47「库内已有优先于自建」直接消费。

  ## 缺口登记（诚实口径；这些**不是**机检内容）
  1. **`Z_H(F,9)` 未在 Lean 内构造**（构造它正是第三层／Procesi 定理的内容）⟹
     `ProcesiS9Hyp`／`ProcesiSubgroupHyp` 中的 `Z` 是**抽象域参数**，两谓词是**模式**
     （schema）；H2 只是其一点实例。
  2. ~~**`Ω = S_9/S_8` 与 Lean 的 `Fin 9` 之间的 `S_9`-集同构未机检**~~ → **已机检**
     （2026-10-18，`Procesi/Omega.lean`）：`S8 := stabilizer (0 : Fin 9)`，
     `omegaEquivQuotient : Fin 9 ≃ S₉ ⧸ S8`（轨道-稳定子 ＋ 传递性），
     `omegaEquivQuotient_smul : φ (h • x) = h • φ x`。**余留**：`Rep` 层的搬运
     （`ℤ[Fin 9] ≅ ℤ[S₉⧸S8]` 作为 `Rep ℤ S₉`）尚未做（沿该同构的 Finsupp 搬运）。
  3. **`trdegCenter` 的 `m = 2` 是反推**：`AGPR2020` 的 `m` 是通用矩阵的**个数**，
     而本工作区的格层没有 `m` 参数；取 `m = 2` 是按 `(m-1)n²+1 = n²+1 = 82` 反推的
     **一致化**，不是从 Procesi 构造中读出的。
-/
import ABGV52.ProcLat_ABGV52
import ABGV52.G2p_ABGV52
import ABGV52.GThm_ABGV52
import ABGV52.EMTrans_ABGV52

open scoped TensorProduct
open ABGV52

namespace Procesi

noncomputable section

universe u

/-! ## §1 AGPR2020 的 trdeg 公式（label `cor:14.4.5`） -/

/-- AGPR2020 `cor:14.4.5`（印刷 §14.4.1）的**超越次数公式**：`m` 个 `n × n` 通用矩阵的中心
（＝分式域 `𝒵`）满足 `trdeg = (m-1)·n² + 1`（`m > 1`）。

**逐字锚**：`raw/AGPR2020.tex` 的 `cor:14.4.5` —— "the Gelfand-Kirillov dimension … is
`(m-1)n²+1` as soon as `m > 1`"；同书 `thm:14.4.4` 给出「`𝒵` 是 `GL(n,F)` 在 `M_n(F)^m` 上
不变量环 `T` 的分式域」——本工作区把后者用作 H2 的**同型母版**（§3 的
`IsInvariantFieldModel`），把前者用作**秩账的外部核对**（下面的 `trdegCenter_eq_latticeRank`）。

**⚠ 这是 `AGPR2020` 的陈述，不是我们的定理**：本工作区不对它作任何论证，
只把它**登记为数值基准**，再用格层（自建、机检）的秩去对表。 -/
def trdegCenter (m n : ℕ) : ℕ := (m - 1) * n ^ 2 + 1

/-- `m = 2`、`n = 9` 时的读数：`(2-1)·81 + 1 = 82`（论文 `rem:procesi-geometric` 的 `82`）。 -/
theorem trdegCenter_two_nine : trdegCenter 2 9 = 82 := by decide

/-- ★ **AGPR2020 公式 × 格层秩账的机器核对**：`AGPR2020` 的 `(m-1)n²+1`（`m=2, n=9`）
与**自建格层**的 `M ⊕ U` 之秩（`finrank ℚ (Mp2 3 ⊗[ℤ] ℚ)`）相等（皆 82）。

**读法**：这是本工作区对「`M ⊕ U` 确实是中心所对应的那个格」的**第一道一致性证据**
（必要不充分）——`AGPR2020` 侧给公式，格层侧给构造，两者数值闭合。 -/
theorem trdegCenter_eq_latticeRank :
    trdegCenter 2 9 = Module.finrank ℚ (ProcLat.Mp2 3 ⊗[ℤ] ℚ) := by
  rw [trdegCenter_two_nine, ProcLat.finrank_Mp2_three]

/-! ## §2 载体与类型锁 -/

/-- `S_9`（`Ω = S_9/S_8` 上的置换群，与 `Equiv.Perm (Fin 9)` 同构）。 -/
abbrev S9 : Type := G.Gp 3

/-- `Ω = S_9/S_8`（以 `Fin 9` 承载，基数 9）。 -/
abbrev Omega : Type := G.OmegaP 3

/-- `U = ℤ[Ω]`（秩 9；`eq:procesi-S9` 的中项左端）。 -/
abbrev U : Rep ℤ S9 := G.U 3

/-- `M = ker φ`（秩 73；Procesi 格）。 -/
abbrev M : Rep ℤ S9 := G.MRep 3

/-- **`M ⊕ U`**（秩 82，＝中心所对应的格；`AGPR2020` `cor:14.4.5` 的 `n²+1`）。 -/
abbrev Lat : Type := ProcLat.Mp2 3

/-- `M ⊕ U` 的 `Rep` 包装。 -/
abbrev LatRep : Rep ℤ S9 := ProcLat.Mp2Rep 3

/-- 类型锁：`U` 就是 `G.U 3`（外形一旦改动，本 `rfl` 立即编译失败）。 -/
theorem u_typeLock : (U : Rep ℤ S9) = G.U 3 := rfl

/-- 类型锁：`M` 就是 `G.MRep 3`。 -/
theorem m_typeLock : (M : Rep ℤ S9) = G.MRep 3 := rfl

/-- 类型锁：`M ⊕ U` 的载体就是 `ker φ × ℤ[Ω]`。 -/
theorem lat_typeLock : (Lat : Type) = (↥(LinearMap.ker (G.phiFun 3)) × G.ZOm 3) := rfl

/-- `ker φ` 的唯一和（沿子模包含拉回到 `ℤ[Ω] ⊗ ℤ[Ω]`；`latticeInvariantsAlg` 的实例前提）。 -/
instance uniqueSums_kerPhi : UniqueSums ↥(LinearMap.ker (G.phiFun 3)) :=
  UniqueSums.of_injective_addHom
    { toFun := fun z => (z.1 : G.ZOm 3 ⊗[ℤ] G.ZOm 3), map_add' := fun _ _ => rfl }
    Subtype.val_injective inferInstance

/-- **`F(M ⊕ U)^{S_9}`** —— `M ⊕ U` 的纯超越扩张 `F(M ⊕ U)` 在 `S_9` 作用下的不变量域
（论文 `rem:procesi-geometric` 逐字的右端）。 -/
noncomputable abbrev invariantsField (F : Type u) [Field F] :
    Subalgebra F (EM.latticeFunctionField F Lat) :=
  EM.latticeInvariantsAlg F S9 Lat

/-- 类型锁：`invariantsField F` 是「`S_9` 在 `F(M⊕U)` 上的不动点代数」。 -/
theorem invariantsField_typeLock (F : Type u) [Field F] :
    (invariantsField F) = EM.latticeInvariantsAlg F S9 Lat := rfl

/-! ## §3 H2 的两个形态 -/

/-- ★★ **H2（`S_9` 层忠实形）** —— 论文 `rem:procesi-geometric` 的**逐字**陈述：

> Procesi `[AGPR2020]` proved that the center of the generic matrix algebra satisfies
> `Z_{S_9}(F,9) ≅ F(M ⊕ U)^{S_9}` … This identification holds over any field `F`
> of characteristic 0.

`Z` = 中心 `Z_{S_9}(F,9)`（以 `[Field Z] [Algebra F Z]` 传入，**不**在 Lean 内构造——
构造它正是本假设的内容之一）；右端 = §2 的 `invariantsField F`。 -/
def ProcesiS9Hyp (F : Type u) [Field F] (Z : Type u) [Field Z] [Algebra F Z] : Prop :=
  Nonempty (Z ≃ₐ[F] ↥(invariantsField F))

/-- 类型锁：`ProcesiS9Hyp` 的外形一旦改动，本 `rfl` 立即编译失败。 -/
theorem procesiS9Hyp_typeLock (F : Type u) [Field F] (Z : Type u) [Field Z] [Algebra F Z] :
    (ProcesiS9Hyp F Z) = (Nonempty (Z ≃ₐ[F] ↥(invariantsField F))) := rfl

/-- ★★ **H2（任意子群形）** —— 论文同段的下降式：

> For any subgroup `H ⊆ S_9`, taking `H`-invariants gives `Z_H(F,9) = F((M ⊕ U)|_H)^H`.

`V` 传入「限制后的格」`(M ⊕ U)|_H`（由 `H ↪ S_9` 沿 `Rep` 拉回；本工作区第二层施工）。
**为何参数化**：`H` 的传递嵌入有基点自由度（`eq:U-restrict` 的 `ω₀`），
`prop:U-restrict-canonical` 说的正是"换基点只差 `ℤ[H]`-自同构、不变量域不变"——
故陈述对 `V` 参数化、对该自由度不敏感。 -/
def ProcesiSubgroupHyp (F : Type u) [Field F] (H : Type) [Group H]
    (V : Type) [AddCommGroup V] [Module ℤ V] [DistribMulAction H V]
    [SMulCommClass H ℤ V] [UniqueProds (Multiplicative V)]
    (Z : Type u) [Field Z] [Algebra F Z] : Prop :=
  Nonempty (Z ≃ₐ[F] ↥(EM.latticeInvariantsAlg F H V))

/-- 类型锁：`ProcesiSubgroupHyp` 的外形。 -/
theorem procesiSubgroupHyp_typeLock (F : Type u) [Field F] (H : Type) [Group H]
    (V : Type) [AddCommGroup V] [Module ℤ V] [DistribMulAction H V]
    [SMulCommClass H ℤ V] [UniqueProds (Multiplicative V)]
    (Z : Type u) [Field Z] [Algebra F Z] :
    (ProcesiSubgroupHyp F H V Z)
      = (Nonempty (Z ≃ₐ[F] ↥(EM.latticeInvariantsAlg F H V))) := rfl

/-- **抽象识别形（形状类比，不是某条已发表定理的忠实转录）**：`Z` 同构于某个
「有限群在格函数域上的不变量域」。

**⚠ 声称边界（2026-10-18 修正）**：本谓词**只是形状**——它极弱（几乎任何不变量域都满足），
**不得**读作 `AGPR2020` `thm:14.4.4` 的内容。`thm:14.4.4` 说的是「中心 `𝒵` 是 `GL(n,F)`
在 `M_n(F)^m` 上不变量环 `T` 的分式域」，其**忠实形式**（`GL(n,F)`、`M_n(F)^m`、`T`）本工作区
**未形式化**。此处仅保留"`Z` 是某不变量域"这一**必要的形状条件**，用于把具名假设接到一个
可陈述的抽象谓词上；`isInvariantFieldModel_of_procesiS9` 因此只是**形状层**接线，
**不是**"H2 的内容 = `thm:14.4.4`"。 -/
def IsInvariantFieldModel (F : Type u) [Field F] (Z : Type u) [Field Z] [Algebra F Z] : Prop :=
  ∃ (H : Type) (_ : Group H) (V : Type) (_ : AddCommGroup V) (_ : Module ℤ V)
    (_ : DistribMulAction H V) (_ : SMulCommClass H ℤ V)
    (_ : UniqueProds (Multiplicative V)),
    Nonempty (Z ≃ₐ[F] ↥(EM.latticeInvariantsAlg F H V))

/-- 类型锁：抽象识别形。 -/
theorem isInvariantFieldModel_typeLock (F : Type u) [Field F] (Z : Type u) [Field Z]
    [Algebra F Z] :
    (IsInvariantFieldModel F Z)
      = (∃ (H : Type) (_ : Group H) (V : Type) (_ : AddCommGroup V) (_ : Module ℤ V)
          (_ : DistribMulAction H V) (_ : SMulCommClass H ℤ V)
          (_ : UniqueProds (Multiplicative V)),
          Nonempty (Z ≃ₐ[F] ↥(EM.latticeInvariantsAlg F H V))) := rfl

/-- ★ **接线：`S_9` 层 H2 ⟹ 抽象识别形（形状层）**。

**这件的意义（限定）**：把一个**具体的**识别断言接到一个**抽象形状**上，便于下游以最小
接口消费。**它不证明** `AGPR2020` `thm:14.4.4`，也**不等于**"H2 的内容 = 那条定理"——
形状谓词太弱，不足以承载那层内容（见 `IsInvariantFieldModel` 的声称边界）。 -/
theorem isInvariantFieldModel_of_procesiS9 (F : Type u) [Field F] (Z : Type u) [Field Z]
    [Algebra F Z] (h : ProcesiS9Hyp F Z) : IsInvariantFieldModel F Z := by
  obtain ⟨e⟩ := h
  exact ⟨S9, inferInstance, Lat, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨e⟩⟩

/-- **L1 非空洞见证**：`ProcesiS9Hyp` 的假设类**非空**——取 `Z := F(M⊕U)^{S_9}` 本身，
恒等同构即实例。

**读法**（L1＋L10① 纪律）：这只说明**陈述可满足**（不是空类上的空洞真），
与「H2 为真」是两件事：后者要求 `Z` 取**真正的中心** `Z_{S_9}(F,9)`。 -/
theorem procesiS9Hyp_nonempty (F : Type u) [Field F] :
    ProcesiS9Hyp F ↥(invariantsField F) :=
  ⟨AlgEquiv.refl⟩

/-- **L1 非空洞见证（被消费的谓词）**：`ProcesiSubgroupHyp` 在 `Z := ` 右端时**可满足**
（恒等同构）。**用途**：`Main.lean` 的 `zH_rational_of_procesi` 消费的是本谓词，
故须对其（不只是对 `ProcesiS9Hyp`）给出非空洞见证——这是 L10①「可实现性」的最低要求。

**限定**：这只是"陈述可满足"，**不是**"H2 为真"；后者要求 `Z` 取真正的 `Z_H(F,9)`
（该域在 Lean 内**未构造**，见头部缺口登记 1）。 -/
theorem procesiSubgroupHyp_nonempty (F : Type u) [Field F] (H : Type) [Group H]
    (V : Type) [AddCommGroup V] [Module ℤ V] [DistribMulAction H V]
    [SMulCommClass H ℤ V] [UniqueProds (Multiplicative V)] :
    ProcesiSubgroupHyp F H V ↥(EM.latticeInvariantsAlg F H V) :=
  ⟨AlgEquiv.refl⟩

/-! ## §4 公理闸门 -/

#print axioms trdegCenter_two_nine
#print axioms trdegCenter_eq_latticeRank
#print axioms uniqueSums_kerPhi
#print axioms invariantsField
#print axioms procesiS9Hyp_typeLock
#print axioms procesiSubgroupHyp_typeLock
#print axioms isInvariantFieldModel_of_procesiS9
#print axioms procesiS9Hyp_nonempty
#print axioms procesiSubgroupHyp_nonempty

end

end Procesi
