/-
  Procesi —— **第二层：Lenstra 层**（论文 `rem:procesi-geometric` 的"有理性"半）

  源（`raw/Lenstra1974.tex`，label `prop:1.4` ≡ 论文引作 `[Proposition 1.4]{Lenstra1974}`）：
    "Let `N` be a finitely generated permutation module over `π`. Then `l(N)^π` is
     rational over `l^π`."
  源证明：取 `N` 的 `π`-置换 `ℤ`-基 `{x_i}`，`W := Σ l·x_i`；对 `W` 用 (1.3)（Speiser）得
  `y_1..y_r ∈ W^π` `l`-张满 `W`；于是 `l(N) = l(y_i)` 且 `l(N)^π = l^π(y_i)`。

  论文的应用形（`raw/ABGV-5.2-resolution.pre44.tex:756–760` 逐字）：对 `ℤ[H]`-置换模
  `U|_H` 在基域 `F(M|_H)` 上用 Lenstra 1.4，前提是 `H` 在 `F(M|_H)` 上**忠实**
  （`prop:faithful-MH`）。

  **本件 = 前提件**：`prop:faithful-MH` 的机器形——`FaithfulSMul H ↥(M|_H)`。
  证明**照原文**（论文第三十三改的障碍论证，`ABGV52/FaithfulMH_ABGV52.lean` 的坐标模型）：
  设 `h` 在 `M|_H = ker(π|_H)` 上平凡；取 `g ∉ {1, h, h⁻¹}`（`|H| = 9 > 3`）；
  `x₁ = g ⊗ δ₁` 与 `x₂ = −(1 ⊗ δ_g)` 都映到 `g − 1`；以 `z := x₁ − x₂` 作输入，
  在坐标 `b' = hg` 处求值得 `h = 0` 矛盾。
  **本件的贡献 = 把坐标模型接到真格 `ker φ`**（经 `kerEquiv`，`G1c` 的
  `Φ : ker φ ≅ ker π`），使 `FaithfulMH.faithfulMH_obstruction` 可用于 `M|_H`。

  续（下一件）：`ABGV52.EMRouteS.s2Interface_of_data'`（置换基 ＋ 忠实性 ⟹
  `IsRational ↥K0 ↥(F(M⊕U)^H)`）＋ `ABGV52.EMBridge` 的
  `semiFunctionField ≅ latticeFunctionField (M × P)` —— 二者已机检，本层只做组装。

  **⚠ L47 更正（2026-10-18，外审 B 检出）**：`ABGV52/ProcStabLink_ABGV52.lean` **早已**给出
  一般素数 `p` 的无条件版 `twoStepInterface_unconditional`（`:91`）与 `m3_unconditional`
  （`:105`），且经 `EMBridge.beta1` 消解 `TwoStepInterface`（与 §4 的路径**逐字相同**）。
  本文件 §4 的 `twoStepInterface_procesi`／`m3_procesi` 因此**不是新结果**，只是
  `p = 3` 的**特化重述**；按库内优先（L47）与不夸大归因，本文件改为**直接消费**库内定理
  （见 §4 的现行版本），并保留特化名以作论文 `p = 9`（`p² = 9`?）口径的接口。
-/
import ABGV52.G1c_ABGV52
import ABGV52.FaithfulMH_ABGV52
import ABGV52.ProcStab_ABGV52
import ABGV52.ProcStabLink_ABGV52
import ABGV52.EMBridge_ABGV52

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

/-! ## §1 `kerEquiv` 与 `H`-作用交换（`DistribMulAction` 层） -/

/-- **`Φ` 等变**（`DistribMulAction` 口径）：`G1c` 的 `kerEquiv_comm` 是 `Rep.ρ` 版本的；
本件给出**子型作用**版本，供 `H`-作用直接消费。 -/
theorem kerEquiv_smul (h : P.Hp 3) (x : ↥(LinearMap.ker (G.phiFun 3))) :
    ((G.kerEquiv 3) (h • x) : ↥(LinearMap.ker (P.pi 3))) =
      h • ((G.kerEquiv 3) x) := by
  apply Subtype.ext
  show G.PhiLM 3 (TensorProduct.map ((G.UH 3).ρ h) ((G.UH 3).ρ h) x.1)
      = P.act 3 h (G.PhiLM 3 x.1)
  exact G.PhiLM_equivariant 3 h x.1

/-- **坐标模型与真模型同一映射**：`FaithfulMH.piH`（`AddMonoidHom`，坐标模型）
与 `P.pi`（`LinearMap`，Procesi 映射）在函数层相同。 -/
theorem piH_eq_pi (m : P.Vp 3) : FaithfulMH.piH (G := P.Hp 3) m = P.pi 3 m := by
  rw [G.pi_apply]
  show (∑ b : P.Hp 3, (m b - (FaithfulMH.aug (m b)) • MonoidAlgebra.single b 1))
      = ∑ b : P.Hp 3, (m b - (P.aug 3 (m b)) • MonoidAlgebra.single b 1)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [P.aug_eq_sum_coeff]
  rfl

/-! ## §2 `prop:faithful-MH`：`H` 在 `M|_H` 上忠实 -/

/-- ★★ **`prop:faithful-MH`（障碍论证，机器形）**：若 `h : H` 在 `M|_H = ker φ` 上
平凡，则 `h = 1`。

**证明路线（照原文）**：① 经 `kerEquiv` 把平凡性传到 `ker π`（`kerEquiv_smul`）；
② 取 `g ∉ {1, h, h⁻¹}`（`Finset.exists_mem_notMem_of_card_lt_card`，`|H| = 9 > 3`）；
③ 用 `FaithfulMH.faithfulMH_obstruction`（= 坐标模型的障碍论证）收口。 -/
theorem faithful_kerPhi (h : P.Hp 3)
    (htriv : ∀ x : ↥(LinearMap.ker (G.phiFun 3)), h • x = x) : h = 1 := by
  classical
  -- ① 平凡性传到 `ker π`（`act` 形）
  have hkerPi : ∀ m : P.Vp 3, P.pi 3 m = 0 → P.act 3 h m = m := by
    intro m hm
    have hx : h • ((G.kerEquiv 3).symm ⟨m, hm⟩) = (G.kerEquiv 3).symm ⟨m, hm⟩ :=
      htriv _
    have h2 := kerEquiv_smul h ((G.kerEquiv 3).symm ⟨m, hm⟩)
    rw [hx, LinearEquiv.apply_symm_apply] at h2
    exact congrArg Subtype.val h2.symm
  -- ② `|H| = 9 > 3` ⟹ 存在 `g ∉ {1, h, h⁻¹}`
  have hcard : Fintype.card (P.Hp 3) = 9 := by
    rw [P.card_Hp]
  have hs : ({1, h, h⁻¹} : Finset (P.Hp 3)).card ≤ 3 := by
    have h1 : ({1, h, h⁻¹} : Finset (P.Hp 3)).card
        ≤ ({h, h⁻¹} : Finset (P.Hp 3)).card + 1 := Finset.card_insert_le _ _
    have h2 : ({h, h⁻¹} : Finset (P.Hp 3)).card
        ≤ ({h⁻¹} : Finset (P.Hp 3)).card + 1 := Finset.card_insert_le _ _
    have h3 : ({h⁻¹} : Finset (P.Hp 3)).card = 1 := by simp
    omega
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, h, h⁻¹} : Finset (P.Hp 3))) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard]; omega)
  have hg1 : g ≠ 1 := fun e => hg (by rw [e]; simp)
  have hgh : g ≠ h := fun e => hg (by rw [e]; simp)
  have hgh' : g ≠ h⁻¹ := fun e => hg (by rw [e]; simp)
  -- ③ 障碍论证（坐标模型）
  refine FaithfulMH.faithfulMH_obstruction h g hg1 hgh hgh' (fun m hm => ?_)
  have h1 := hkerPi m (by rw [← piH_eq_pi]; exact hm)
  funext i
  exact congrFun h1 i

/-- ★ **`prop:faithful-MH`（`FaithfulSMul` 实例形）**：`H` 在 `M|_H` 上**忠实作用**。

**用途**：这是 Lenstra 1.4 的前提（`ABGV52.EMRouteS.s2Interface_of_data'` 的 `hfaith`），
也是论文 `rem:procesi-geometric` 里 "on which `H` acts faithfully" 的机器对应。 -/
instance faithfulSMul_kerPhi :
    FaithfulSMul (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)) := by
  rw [faithfulSMul_iff]
  exact faithful_kerPhi

/-- 类型锁：忠实性陈述的外形（一旦改动立即编译失败）。 -/
theorem faithfulSMul_kerPhi_typeLock :
    FaithfulSMul (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)) :=
  inferInstance

/-! ## §4 二步识别与 M3 —— **消费库内已有的无条件定理**（L47）

  `ABGV52.ProcStab`（文件 `ProcStabLink_ABGV52.lean`）已给一般素数 `p` 的无条件版：`twoStepInterface_unconditional`
  与 `m3_unconditional`。本节的 `p = 3` 版本只是**特化重述**（供本工作区的类型锁与
  下游 `Main.lean` 消费），**不声称**是新结果。 -/

/-- **`TwoStepInterface`（`p = 3` 特化）**：库内 `ProcStab.twoStepInterface_unconditional`
的无条件版在 `p = 3` 处的实例（消解机制 = `EMBridge.beta1` 的等变环境同构）。 -/
theorem twoStepInterface_procesi (F : Type) [Field F] :
    ProcStab.TwoStepInterface (p := 3) F :=
  ProcStab.twoStepInterface_unconditional (p := 3) F

/-- ★ **M3（`p = 3` 特化，无条件）**：`F((M⊕U)|_H)^H` 于 `F(M|_H)^H` 有理
（`≃+*` 形；＝库内 `ProcStab.m3_unconditional` 的 `p = 3` 实例）。

逐字对照论文 `rem:procesi-geometric`：
> The field `Z_H(F,9)` … is *rational* over `F(M|_H)^H`: apply `[Proposition 1.4]{Lenstra1974}`
> to the permutation `Z[H]`-module `U|_H` over the base field `F(M|_H)`.

**源锚**：`raw/Lenstra1974.tex` 的 label `prop:1.4`。

**形态注（如实登记）**：本式是 `≃+*` 形——与库内 `m3_unconditional` **同形**。库的消费者
（`ProcConsume.ProcesiHypStableK`）要 `≃ₐ[K]` 形；该升级由 `Procesi/Alg.lean` 的典范包含
＋ 待完成的 `isRational_procesi` 承担（`wiki/log.md` 有登记）。 -/
theorem m3_procesi (F : Type) [Field F] :
    ∃ k : ℕ, Nonempty (↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3)) ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (P.Hp 3)
        ↥(LinearMap.ker (G.phiFun 3))) k) :=
  ProcStab.m3_unconditional (p := 3) F

/-- 类型锁：二步识别（`p = 3`）的外形。 -/
theorem twoStepInterface_procesi_typeLock (F : Type) [Field F] :
    ProcStab.TwoStepInterface (p := 3) F :=
  twoStepInterface_procesi F

/-! ## §5 公理闸门 -/

#print axioms kerEquiv_smul
#print axioms piH_eq_pi
#print axioms faithful_kerPhi
#print axioms faithfulSMul_kerPhi
#print axioms faithfulSMul_kerPhi_typeLock
#print axioms twoStepInterface_procesi
#print axioms twoStepInterface_procesi_typeLock
#print axioms m3_procesi

end

end Procesi
