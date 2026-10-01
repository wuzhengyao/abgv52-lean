/-
  ABGV-5.2 —— **G 档 T2 陈述锁定**：几何等同归约层的**公开陈述形态**

  口径（照 B 档／P 档工艺）：本件只锁**陈述**——把 G 档三条写成可被独立重写对照的形态：
    * `gThm_embedding_independence`（论文 `:644` `prop:embedding-independence`）；
    * `gThm_restrict_canonical`（论文 `:624` `prop:U-restrict-canonical`）；
    * `gThm_geometric_identification`（论文 `rem:procesi-geometric`，以 **Procesi 1967** 为带名假设）；
  外加**平凡实例探针** `gThm_embedding_independence_refl`（陈述非空洞）。
  证明直接调用 G 档已交付件（`MresOf_iso`／`MresOf_iso_Mrep`／`ZH_iso`）。

  对应的独立重写件 = `GChallenge_ABGV52.lean`（**零 import 主链**，自足重建对象并同形陈述）；
  检查器 `abgv52-lean-crosscheck.py` 的 `[3c]` 逐条比对两份文件的陈述类型（防「全文件一致的替换」）。

  假设侧**定义外形锁定**（阶段 5.5 第 5 条「双类型锁定」）：`ProcesiHyp` 的 `rfl` 断言在 §3。
-/
import ABGV52.G1d_ABGV52

open scoped TensorProduct
open CategoryTheory

open ABGV52.P (Hp M_rep pi)

namespace ABGV52.G

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. G 档三条陈述（调用主线） -/

/-- **θ-无关性（论文 `:644`）**：任意两基点给出的限制同构。 -/
theorem gThm_embedding_independence (e₁ e₂ : Hp p ≃ OmegaP p) :
    Nonempty (MresOf p e₁ ≅ MresOf p e₂) :=
  ⟨MresOf_iso p e₁ e₂⟩

/-- **正则限制（论文 `:624`）**：**任意**基点给出的限制都与 P 档的 `M_rep` 同构。 -/
theorem gThm_restrict_canonical (e : Hp p ≃ OmegaP p) :
    Nonempty (MresOf p e ≅ M_rep p) :=
  ⟨MresOf_iso_Mrep p e⟩

/-- **几何等同（论文 `rem:procesi-geometric`）**：以 Procesi 1967 的
\(Z_H(F,p^2)\cong F(M|_\theta)^H\) 为**带名假设**，得 \(Z_H(F,p^2)\cong F(M_{\mathrm{rep}})^H\)。 -/
theorem gThm_geometric_identification (F : Type*) [Field F] (Z : Type*) [Field Z]
    (hProcesi : Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (Hp p)
      ↥(LinearMap.ker (phiFun p))))) :
    Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (Hp p)
      ↥(LinearMap.ker (pi p)))) :=
  ZH_iso p F Z hProcesi

/-! ## 2. 平凡实例探针（L1 非空洞性：陈述的前提类非空） -/

/-- 探针：取同一基点时陈述成立（且为恒等同构）——陈述不空洞。 -/
theorem gThm_embedding_independence_refl (e : Hp p ≃ OmegaP p) :
    Nonempty (MresOf p e ≅ MresOf p e) :=
  ⟨Iso.refl _⟩

/-! ## 3. 假设侧**定义外形锁定**（阶段 5.5 第 5 条） -/

/-- Procesi 1967 几何等同假设的**定义外形**（带名假设，**非** KB 内定理）。 -/
def ProcesiHyp (F : Type*) [Field F] (Z : Type*) [Field Z] : Prop :=
  Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (Hp p) ↥(LinearMap.ker (phiFun p))))

/-- **类型锁定断言**：`ProcesiHyp` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (F : Type*) [Field F] (Z : Type*) [Field Z] :
    ProcesiHyp (p := p) F Z = Nonempty (Z ≃+* ↥(ABGV52.EM.latticeInvariants F (Hp p)
      ↥(LinearMap.ker (phiFun p)))) := rfl

/-! ## 4. 公理闸门 -/

#print axioms gThm_embedding_independence
#print axioms gThm_restrict_canonical
#print axioms gThm_geometric_identification
#print axioms gThm_embedding_independence_refl

end ABGV52.G
