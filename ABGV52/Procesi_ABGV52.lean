/-
  ABGV-5.2 —— **具名假设档 3/3**：几何等同 Z_H(F,p²) ≅ F(M|_θ)^H（Procesi 1967）

  口径（用户 2026-10-07 指令「ABGV5.2 还有 3 处需要形式化」之第三项）
  ================================================================
  论文 `rem:procesi-geometric`：Z_H(F,p²) ≅ F(M|_H)^H（**Procesi 1967**，char 0）。
  G 档已交付：`ABGV52.G.ProcesiHyp`（具名假设外形）＋ 其 `rfl` 类型锁定
  （`GThm_ABGV52` §3）＋ 装配定理 `gThm_geometric_identification`（**匿名参数**
  `hProcesi`）＋ 独立重写件（`GChallenge_ABGV52`；经交叉核对 [3c]）。
  本件补齐**具名假设的消费面**（与 EM／Saltman 两档工艺一致）：

    * `gThm_geometric_identification_named`：以 `ProcesiHyp`（**具名假设**，
      而非匿名同型参数）为输入，经子群步（G2p 的 `ZH_iso`）得
      `Z ≅ F(M_rep)^H`；
    * **非空洞探针**（L1）：`ProcesiHyp` 的假设类**非空**——取
      `Z := F(M|_θ)^H` 本身，恒等同构即实例；
    * 公理闸门。

  注（为何不并入 `GThm_ABGV52`）：`GThm` 与 `GChallenge` 是**已过 [3c] 交叉核对**
  的陈述对（4 条对 4 条）；向其追加新定理会使两侧陈述集不同步。另立本件则
  零触碰既有核对对，并保持「一档一文件」的具名假设批式结构。

  **无 sorry、无自造公理**。
-/
import ABGV52.GThm_ABGV52

open CategoryTheory

open ABGV52.P (Hp)

namespace ABGV52.G

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 具名假设的消费 -/

/-- **几何等同（具名假设版）**：由 `ProcesiHyp`（Procesi 1967，带名假设
`Z_H(F,p²) ≅ F(M|_θ)^H`）经子群步得 `Z ≅ F(M_rep)^H`（论文 `rem:procesi-geometric`
＋ G2 子群步；即 `gThm_geometric_identification` 的具名假设改写）。 -/
theorem gThm_geometric_identification_named (F : Type*) [Field F]
    (Z : Type*) [Field Z] (hProcesi : ProcesiHyp (p := p) F Z) :
    Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (Hp p)
      ↥(LinearMap.ker (ABGV52.P.pi p)))) :=
  gThm_geometric_identification p F Z hProcesi

/-! ## 2. 非空洞探针（L1：假设类非空） -/

/-- 探针：取 `Z := F(M|_θ)^H` 本身，恒等同构即 `ProcesiHyp` 的实例
（假设类非空，结论非空洞）。 -/
theorem ProcesiHyp_satisfiable (F : Type*) [Field F] :
    ProcesiHyp (p := p) F ↥(ABGV52.EM.latticeInvariants F (Hp p)
      ↥(LinearMap.ker (phiFun p))) :=
  ⟨RingEquiv.refl _⟩

/-! ## 3. 公理闸门 -/

#print axioms gThm_geometric_identification_named
#print axioms ProcesiHyp_satisfiable

end ABGV52.G
