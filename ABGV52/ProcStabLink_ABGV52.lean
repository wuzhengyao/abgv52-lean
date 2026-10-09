/-
  ABGV-5.2 —— **C 轨续作（T5 接线）：EM 轨 T1 环境同构 ⟹ `TwoStepInterface` 消解**

  目标。`ProcStab_ABGV52.lean` 的目标 2（`TwoStepInterface`，对象层二步识别
  `F(M₂)^H ≅ F(M₂|_H)^H` 的环同构形）此前只按「未证明者具名注册 ＋ 接线定理」
  落盘，其接线定理 `twoStepInterface_of_ambient` 的假设 = 等变环境同构

    Φ : semiFunctionField F M P ≃+* latticeFunctionField F (M₂)

  （`M := ↥(ker φ)`、`P := ℤ[Ω]`、`M₂ = ProcLat.Mp2 p`）。本件把 **EM 轨 T1
  （`EMBridge_ABGV52.lean`）已交付的绝对识别** `beta1`（§6）实例化到 Procesi 数据上，
  给出该假设的**具体见证**，从而：

    ① 主接线（本件 §1–§2）：`TwoStepInterface` 的 **inhabitant**
       `twoStepInterface_unconditional`——**无条件**（仅 `[Field F]` ＋ `[Fact p.Prime]`）；
    ② 收口（本件 §3）：`ProcesiHypExact → ProcesiHypStable` 的**无条件**版
       `procesiHypStable_of_exact_unconditional`（经 `m3_of_twoStep` ＋
       `procesiHypStable_of_exact_of_twoStep` 链；此前该链的 M3 假设已由 `ProcStab` §4
       消解、目标 2 假设由本件消解）。

  接口偏差登记（逐条实测）：
    ① `EM.Bridge.beta1` 的**类型不含 `G`**（实测 `#check`：其参数仅
       `F, M, P` ＋ 三实例；`semiFunctionField`／`latticeFunctionField` 均不提及 `G`）。
       本件消费它取 `≃+*` 形（`AlgEquiv.toRingEquiv`，`TwoStepInterface` 的外形
       即 `≃+*`——F-代数相容性被弃）。
    ② `G`-相干性唯一入口 = `EM.Bridge.beta1_equivariant`（`[Group G] [Fintype G]`），
       在 `G := Hp p` 消费；其所需分量实例 `DistribMulAction (Hp p) ↥(ker φ)`
       （G1c）／`(Hp p) (ZOm p)`（`ProcStab` 新装 `instDistribMulActionHpZOm`）与
       `SMulCommClass (Hp p) ℤ`（两侧，经 `AddGroup.int_smulCommClass'`）实测齐备。
    ③ **实测残余**（`ProbePS2_ABGV52.lean` 逐条）：乘积载体上的
       `SMulCommClass (Hp p) ℤ (ProcLat.Mp2 p)`（及对偶序）**不能**由实例搜索合成
       ——本接线**不需要**它（`TwoStepInterface` 侧只需 `MulSemiringAction`），
       故不构成缺口；登记以供后续消费点参考（凡需在 `Mp2` 上直接用
       `SMulCommClass` 的件须另装）。
    ④ `twoStepInterface_unconditional` 取 `def`（非 `theorem`）：`theorem` 在 Lean 4
       为不透明，`rfl` 型接线锁（§2）需 delta 展开，故沿 `ProcStab`／`ProcHyp` 的
       `def …: Prop` 风格。

  **无 sorry、无自造公理**；`#print axioms` 闸门见 §4。
-/
import ABGV52.ProcStab_ABGV52
import ABGV52.EMBridge_ABGV52

open ABGV52.P (Hp)

namespace ABGV52.ProcStab

variable (p : ℕ) [Fact p.Prime]

noncomputable section

/-! ## 1. β₁ 在 Procesi 数据上的实例化

  `EM.Bridge.beta1`（绝对识别 `semi ≃ₐ[F] F(M × P)`）在
  `M := ↥(ker φ)`、`P := ZOm p` 上的实例化；`ProcLat.Mp2 p` 是 `↥(ker φ) × ZOm p`
  的 `abbrev`（两侧 `latticeFunctionField` 的 defeq 由 `betaProc` 的定义类型检查
  见证，亦见 `ProbePS2` 末条的 `rfl` 读数）。 -/

/-- **β（Procesi 数据）**：绝对识别的环同构形
`semiFunctionField F ↥(ker φ) ℤ[Ω] ≃+* latticeFunctionField F (Mp2 p)`。 -/
def betaProc (F : Type*) [Field F] :
    EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p))) (P := G.ZOm p) ≃+*
      EM.latticeFunctionField F (ProcLat.Mp2 p) :=
  (EM.Bridge.beta1 (F := F) (M := ↥(LinearMap.ker (G.phiFun p))) (P := G.ZOm p)).toRingEquiv

/-- **类型锁定（β）**：外形一旦被改动，本 `rfl` 立即编译失败。 -/
theorem betaProc_typeLock (F : Type*) [Field F] :
    betaProc p F
      = (EM.Bridge.beta1 (F := F) (M := ↥(LinearMap.ker (G.phiFun p)))
          (P := G.ZOm p)).toRingEquiv := rfl

/-- **等变性**：`β (σ • x) = σ • β x`（`Hp p`-作用两侧；经 T1 的 `beta1_equivariant`）。 -/
theorem betaProc_equivariant (F : Type*) [Field F] (σ : Hp p)
    (x : EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun p))) (P := G.ZOm p)) :
    betaProc p F (σ • x) = σ • betaProc p F x :=
  EM.Bridge.beta1_equivariant (F := F) (G := Hp p) (M := ↥(LinearMap.ker (G.phiFun p)))
    (P := G.ZOm p) σ x

/-! ## 2. 主接线：`TwoStepInterface` 的 inhabitant（无条件） -/

set_option linter.defProp false in
/-- **主接线（目标 2 消解）**：`TwoStepInterface` 无条件成立——
左端 `↥(F(M₂)^H)`（`latticeInvariants F (Hp p) (Mp2 p)`）与右端机器的
`↥(l(N)^H)`（`FixedPoints.subfield (Hp p) (semiFunctionField …)`）同构，
见证 = `twoStepInterface_of_ambient` 消费 `betaProc` ＋ `betaProc_equivariant`。
`def`（非 `theorem`）以使 §2 的 `rfl` 接线锁可展开（故关 `linter.defProp`）。 -/
def twoStepInterface_unconditional (F : Type*) [Field F] :
    TwoStepInterface (p := p) F :=
  twoStepInterface_of_ambient (p := p) F (betaProc p F) (betaProc_equivariant p F)

/-- **接线锁（`rfl`）**：本件产出的 inhabitant 逐字 = 接线定理对 `betaProc` 的应用；
一旦 `TwoStepInterface` 外形或接线路径被改动，本 `rfl` 立即编译失败。 -/
theorem twoStepInterface_unconditional_eq_wiring (F : Type*) [Field F] :
    twoStepInterface_unconditional p F
      = twoStepInterface_of_ambient (p := p) F (betaProc p F) (betaProc_equivariant p F) :=
  rfl

/-! ## 3. 收口：`ProcesiHypExact → ProcesiHypStable` 无条件 -/

/-- **M3（无条件）**：`↥(l(M₂)^H) ≃+* K(t₁,…,t_k)`（`K = ↥(F(M|_H)^H)`）——
目标 1（`exists_ratOver_semiInvariants`，无条件）经目标 2 具名件（本件已消解）的合流。 -/
theorem m3_unconditional (F : Type*) [Field F] :
    ∃ k : ℕ, Nonempty (↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))) k) :=
  m3_of_twoStep p F (twoStepInterface_unconditional p F)

/-- **收口（无条件）**：`ProcesiHypExact ⟹ ProcesiHypStable`（桥 (c) 的两条假设
——M3 与目标 2——均已在本轨消解；本定理不再带任何非 `[Field]` 类假设）。 -/
theorem procesiHypStable_of_exact_unconditional (F : Type*) [Field F] (Z : Type*) [Field Z]
    (hExact : ProcHyp.ProcesiHypExact (p := p) F Z) :
    ProcHyp.ProcesiHypStable (p := p) F Z :=
  procesiHypStable_of_exact_of_twoStep p F Z hExact (twoStepInterface_unconditional p F)

/-- **非空洞探针（L1）**：把收口链作用到 C′ 的满足实例
（`procesiHypExact_satisfiable`）上——假设类非空且整链在消费端可实例化。 -/
theorem procesiHypStable_probe (F : Type*) [Field F] :
    ProcHyp.ProcesiHypStable (p := p) F
      ↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) :=
  procesiHypStable_of_exact_unconditional p F _
    (ProcHyp.procesiHypExact_satisfiable p F)

/-! ## 4. 公理闸门 -/

#print axioms betaProc
#print axioms betaProc_typeLock
#print axioms betaProc_equivariant
#print axioms twoStepInterface_unconditional
#print axioms twoStepInterface_unconditional_eq_wiring
#print axioms m3_unconditional
#print axioms procesiHypStable_of_exact_unconditional
#print axioms procesiHypStable_probe

end

end ABGV52.ProcStab
