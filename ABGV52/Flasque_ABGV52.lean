/-
  ABGV-5.2 —— 论文 2026-10-11 版 §2 新块（p.5–6）：flasque／coflasque 与 flasque 消解

  覆盖的论文 label
  ================
    * `def:flasque-coflasque`（2.3）：flasque（`Ĥ^{-1}(K,M)=0` 对一切子群 `K ≤ G`）／
      coflasque（`coh¹(K,M)=0` 对一切子群 `K ≤ G`）——**具体定义**（非接口）：
      flasque 侧取 mathlib 的 Tate 上同调 `tateCohomology _ (-1)`（= `Ĥ^{-1}`），
      coflasque 侧取 `groupCohomology _ 1`；子群一侧一律经 `Rep.res K.subtype`（mathlib
      `RepresentationTheory.Rep.Res`）限制。
    * `def:flasque-class`（2.4）：相似 `M ∼ N`（存在置换格 `S₁ S₂` 使 `M ⊕ S₁ ≅ N ⊕ S₂`）、
      可逆（置换格的直和项）。
    * `prop:flasque-resolution`（2.5）：flasque 消解 `0 → M → P → F → 0`（`P` 置换、`F`
      flasque）与 flasque 类 `ρ(M)`。
    * **`lem:invertible-coflasque`（2.6）**：可逆 ⟹ coflasque。

  本件「真证 vs 接口」的分界（**逐条登记，不掩盖**）
  ==============================================
    * **coflasque 一侧（2.6）**：本件**真证**。已证部分：
        - `subsingleton_cohomology_one_of_retract`：`coh¹` 沿收缩拉回（一般群 `G`）；
        - `coflasque_top_of_isInvertible`：**可逆 ⟹ 顶层群上 `coh¹(H,M)=0`**
          （论文 2.6 证明中被 4.13 实际使用的那一步：4.13 的非 coflasque 见证取
          `K = H` 本身；见论文 4.13 证明末段「`coh¹(H,E) ≠ 0`，`E` 不是 coflasque」）。
          证明照论文结构：`M ⊕ M' ≅ P`（`P` 置换）⟹ `coh¹(H,M)` 是 `coh¹(H,P)` 的
          收缩 ⟹ 归约到置换格情形，后者由本工程既有 `subsingleton_perm_coh1` 给出
          （该定理内部即论文所引的 **Shapiro 引理 ＋ `coh¹(K,ℤ)=0`**：`subsingleton_permHK`
          ＋ `subsingleton_coh1_TZ`）。
        - `isCoflasque_of_isInvertible`：**全子群形**（论文 2.6 的逐字结论），
          **已无前提、已证**（第 2 轮闭合——见下「缺口闭合」）。
    * **缺口闭合（2026-10-11 第 2 轮）**：上一轮登记的卡点 `SubgroupPermCoh1Hyp`
      （「置换格限制到**任意子群** `K ≤ H` 后 `coh¹(K, ·) = 0`」）现由
      `SubgroupPerm_ABGV52.lean` **证成**：该件把 Shapiro 桥 `ℤ[G/K] ⟶ Coind_K^G(ℤ)`
      （S3 的 `H`-专用构造）与轨道幂等分解（S4／EMQuasi §4b 的 `H`-专用机器）
      **逐条推广到任意有限群 `G`**，得 `subsingleton_permCosetG`／`subsingleton_ofMulAction_coh1G`
      ／`subsingleton_perm_coh1G`，并证「置换格沿子群限制仍是置换格」
      （`isPermutationLattice_res`），最终给出 `subsingleton_coh1_res_of_permutation`
      ＝ 本件 `subgroupPermCoh1Hyp`。
      **`SubgroupPermCoh1Hyp` 的旧接口名与旧类型逐字保留**（下游接线不破坏），
      但它现在是**定理的陈述**而非假设：`theorem subgroupPermCoh1Hyp : SubgroupPermCoh1Hyp`。
    * **flasque 一侧仅作接口**（用户口径允许）：`IsFlasque` 是**具体定义**（非公理），
      但本件不给出非平凡的 `IsFlasque` 实例——`Ĥ^{-1}` 侧的 Shapiro（`Ĥ^{-1}(K,ℤ[K]^n)=0`）
      未在工程内建立；`FlasqueResolutionHyp`（CTS77 §1 Lemme 3 的存在性）与
      `FlasqueClassWellDefinedHyp`（同 §1 Lemme 5 的 `[F]` 良定义）按 `EM_ABGV52`／
      `Saltman_ABGV52` 的**具名假设接口**工艺给出（类型锁 ＋ 接线 ＋ 非空洞探针）。
    * **相似关系的传递性已闭合（第 2 轮）**：论文 2.4 的「这是等价关系」第三支
      `isSimilar_trans` 已证——(i) 置换格对 `⊞` 封闭由
      `SubgroupPerm_ABGV52.isPermutationLattice_biprod`（核心同构
      `ℤ[X] ⊞ ℤ[Y] ≅ ℤ[X ⊕ Y]`）给出，(ii) 拼接走 `biprod.associator`
      （结合）＋ `biprod.braiding`（交换）＋ `biprod.mapIso`（函子性）。
      于是 `IsSimilar` 是真正的等价关系（`refl`／`symm`／`trans` 三支齐备）。

  **无 sorry、无自造公理**；`#print axioms` 门见 §5。
-/
import ABGV52.EMQuasi_ABGV52
import ABGV52.SubgroupPerm_ABGV52
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

open CategoryTheory CategoryTheory.Limits

-- 与 `EMQuasi_ABGV52` 同款：本件多处 `haveI := …` 是命题层的实例登记，风格 lint 关闭。
set_option linter.style.haveILetI false

-- `ℤ` 上 `AddCommGroup.toIntModule` 与 `Rep.hV2` 争用 `Module ℤ ↥X`（同 EMQuasi §0 的处理，
-- 见 `EMQuasi_ABGV52.lean` 的 `attribute [local instance 1500] Rep.hV2`）。
attribute [local instance 1500] Rep.hV2

namespace ABGV52

/-! ## §1 `def:flasque-coflasque`（2.3）：具体定义 -/

/-- **`Ĥ^{-1}(K, M)`（Tate 上同调负一次，子群形）**：mathlib 的
`tateCohomology _ (-1)` 需要 `[Fintype ↥K]`，而有限群 `G` 的**子群**在 mathlib 里只有
`Finite` 实例——故在此以 `Fintype.ofFinite` 显式供给（`Finite ↥K` 由 `Fintype G` 实例搜索
得到；`Fintype ↥K` 本身**无**实例，实测登记于本件开发探针）。 -/
noncomputable abbrev tateHMinusOneSub (G : Type) [Group G] [Fintype G] (K : Subgroup G)
    (M : Rep.{0,0,0} ℤ G) : Type :=
  ↥(@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K) (Rep.res K.subtype M) (-1))

/-- **flasque**（论文 `def:flasque-coflasque`，CTS77 §1）：有限群 `G` 的 `ℤ[G]`-格 `M`
**flasque** ⟺ 对一切子群 `K ≤ G` 有 `Ĥ^{-1}(K, M) = 0`。

「为零」在 `ModuleCat ℤ` 上取 `Subsingleton ↥−`（= 该 `ℤ`-模只有一个元素）；
`Ĥ^{-1}` 取 mathlib 的 Tate 上同调 `tateCohomology _ (-1)`
（`Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`），子群形见
`tateHMinusOneSub`。 -/
def IsFlasque (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∀ K : Subgroup G, Subsingleton (tateHMinusOneSub G K M)

/-- **coflasque**（论文 `def:flasque-coflasque`，CTS77 §1）：对一切子群 `K ≤ G` 有
`coh¹(K, M) = 0`。子群一侧经 `Rep.res K.subtype` 限制。 -/
def IsCoflasque (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∀ K : Subgroup G, Subsingleton ↥(groupCohomology (Rep.res K.subtype M) 1)

/-- **类型锁定断言**（`IsFlasque`）：定义外形一旦被改动，本 `Iff.rfl` 立即编译失败。 -/
example (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) :
    IsFlasque G M ↔ ∀ K : Subgroup G, Subsingleton (tateHMinusOneSub G K M) :=
  Iff.rfl

/-- **类型锁定断言**（`IsCoflasque`）。 -/
example (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) :
    IsCoflasque G M ↔
      ∀ K : Subgroup G, Subsingleton ↥(groupCohomology (Rep.res K.subtype M) 1) :=
  Iff.rfl

/-! ## §2 `def:flasque-class`（2.4）：相似、可逆 -/

/-- **相似**（论文 `def:flasque-class`）：`M ∼ N` ⟺ 存在置换格 `S₁`、`S₂` 使
`M ⊕ S₁ ≅ N ⊕ S₂`。置换格谓词取一般群版 `EM.IsPermutationLattice`（`D1_ABGV52.lean`）。 -/
def IsSimilar (G : Type) [Group G] (M N : Rep.{0,0,0} ℤ G) : Prop :=
  ∃ (S₁ S₂ : Rep.{0,0,0} ℤ G),
    EM.IsPermutationLattice G S₁ ∧ EM.IsPermutationLattice G S₂ ∧
      Nonempty (M ⊞ S₁ ≅ N ⊞ S₂)

/-- **相似类的自反性**（论文 2.4 的「这是等价关系」之自反支）：取 `S₁ = S₂ = ℤ[G]`
（正则置换格，`D1` 的 `isPermutationLattice_trivial` 给出单点情形；此处直接用
`Rep.ofMulAction ℤ G PUnit`），同构取恒等。 -/
theorem isSimilar_refl (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) : IsSimilar G M M :=
  ⟨Rep.ofMulAction ℤ G PUnit, Rep.ofMulAction ℤ G PUnit,
    EM.isPermutationLattice_trivial G, EM.isPermutationLattice_trivial G,
    ⟨Iso.refl _⟩⟩

/-- **相似类的对称性**（论文 2.4 的「这是等价关系」之对称支）。 -/
theorem isSimilar_symm {G : Type} [Group G] {M N : Rep.{0,0,0} ℤ G}
    (h : IsSimilar G M N) : IsSimilar G N M := by
  obtain ⟨S₁, S₂, h₁, h₂, ⟨e⟩⟩ := h
  exact ⟨S₂, S₁, h₂, h₁, ⟨e.symm⟩⟩

/-- **相似关系的传递性**（论文 2.4 的「这是等价关系」之传递支）：
置换格对 `⊞` 封闭（`isPermutationLattice_biprod`）＋ `biprod` 结合／交换同构与
`biprod.mapIso` 的拼接。

链：`M ⊞ (S₁ ⊞ T₁) ≅ (M ⊞ S₁) ⊞ T₁ ≅ (N ⊞ S₂) ⊞ T₁ ≅ N ⊞ (S₂ ⊞ T₁)
≅ N ⊞ (T₁ ⊞ S₂) ≅ (N ⊞ T₁) ⊞ S₂ ≅ (L ⊞ T₂) ⊞ S₂ ≅ L ⊞ (T₂ ⊞ S₂)`。 -/
theorem isSimilar_trans {G : Type} [Group G] {M N L : Rep.{0,0,0} ℤ G}
    (h₁ : IsSimilar G M N) (h₂ : IsSimilar G N L) : IsSimilar G M L := by
  obtain ⟨S₁, S₂, hS₁, hS₂, ⟨e₁⟩⟩ := h₁
  obtain ⟨T₁, T₂, hT₁, hT₂, ⟨e₂⟩⟩ := h₂
  refine ⟨S₁ ⊞ T₁, T₂ ⊞ S₂, isPermutationLattice_biprod hS₁ hT₁,
    isPermutationLattice_biprod hT₂ hS₂, ⟨?_⟩⟩
  exact (biprod.associator M S₁ T₁).symm ≪≫ biprod.mapIso e₁ (Iso.refl T₁) ≪≫
    biprod.associator N S₂ T₁ ≪≫ biprod.mapIso (Iso.refl N) (biprod.braiding S₂ T₁) ≪≫
    (biprod.associator N T₁ S₂).symm ≪≫ biprod.mapIso e₂ (Iso.refl S₂) ≪≫
    biprod.associator L T₂ S₂

/-- **`IsSimilar` 是等价关系**（论文 2.4 的「这是等价关系」全句）：自反支
`isSimilar_refl` ＋ 对称支 `isSimilar_symm` ＋ 传递支 `isSimilar_trans`。 -/
theorem isSimilar_equivalence (G : Type) [Group G] : Equivalence (IsSimilar G) :=
  ⟨fun M => isSimilar_refl G M, fun h => isSimilar_symm h, fun h₁ h₂ => isSimilar_trans h₁ h₂⟩

/-- **可逆**（论文 `def:flasque-class`）：`M` 是某置换格的**直和项**——
即存在 `N` 与置换格 `P` 使 `M ⊕ N ≅ P`。 -/
def IsInvertible (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∃ (N P : Rep.{0,0,0} ℤ G), EM.IsPermutationLattice G P ∧ Nonempty (M ⊞ N ≅ P)

/-- **类型锁定断言**（`IsInvertible`）。 -/
example (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) :
    IsInvertible G M ↔
      ∃ (N P : Rep.{0,0,0} ℤ G),
        EM.IsPermutationLattice G P ∧ Nonempty (M ⊞ N ≅ P) :=
  Iff.rfl

/-! ## §3 `prop:flasque-resolution`（2.5）：flasque 消解与 flasque 类

论文 2.5 的存在性出自 CTS77 §1 Lemme 3、`[F]` 只依赖 `M` 出自同 §1 Lemme 5——
两者都是**外部输入**（与 `EMHyp`／`SaltmanHyp` 同款工艺：命名假设 ＋ 类型锁 ＋
接线 ＋ 非空洞探针），本件不假装证明。 -/

/-- **flasque 消解**（论文 `prop:flasque-resolution`）：短正合列
`0 → M --ι--> P --π--> F → 0`，其中 `P` 置换、`F` flasque。

`ι`、`π` 的正合性用 `Function.Injective`／`Function.Exact`／`Function.Surjective`
（与 `Hyp_ABGV52.IsQuasiPermutation` 同形）。 -/
structure FlasqueResolution (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) where
  /-- 消解的右端 `F`（flasque 格；其相似类即 `ρ(M)`）。 -/
  F : Rep.{0,0,0} ℤ G
  /-- 消解的中间项 `P`（置换格）。 -/
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
  /-- `P` 是置换格。 -/
  perm : EM.IsPermutationLattice G P
  /-- `F` 是 flasque 格。 -/
  flasque : IsFlasque G F

/-- **`prop:flasque-resolution` 的存在性（具名假设，CTS77 §1 Lemme 3）**：
每个 `ℤ[G]`-**格**都有 flasque 消解。

⚠ **本形按现形为假（2026-10-11 机器证伪）** ✗：本 `def` 把 `M` 取成**任意** `ℤ[G]`-模
（含挠模），而消解要求 `M ↪ P`、`P` 置换格（`ℤ`-模无挠）⟹ 取 `M = ℤ/2` 即无消解
（见 `HypRefute_ABGV52.not_flasqueResolutionHyp`，任意 `G`）✓。
**论文真正用到的是「格（无挠）上」的受限形** ✓（CTS77 的 Lemme 3 本就在格范畴）。
⚠ 另：全工程**无任何定理**由本假设推出实质结论（消费者只有 `flasqueResolution_of_hyp` 的
拆包）⟹ 不存在「以假前提得空洞真」的污染 ✓（主循环核实，见假设状态笔记 §6）。 -/
def FlasqueResolutionHyp (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ M : Rep.{0,0,0} ℤ G, Nonempty (FlasqueResolution G M)

/-- **类型锁定断言**（`FlasqueResolutionHyp`）。 -/
example (G : Type) [Group G] [Fintype G] :
    FlasqueResolutionHyp G ↔ ∀ M : Rep.{0,0,0} ℤ G, Nonempty (FlasqueResolution G M) :=
  Iff.rfl

/-- **接线**：由具名假设取出给定 `M` 的一条 flasque 消解。 -/
theorem flasqueResolution_of_hyp {G : Type} [Group G] [Fintype G]
    (h : FlasqueResolutionHyp G) (M : Rep.{0,0,0} ℤ G) : Nonempty (FlasqueResolution G M) :=
  h M

/-- **`ρ(M)` 的良定义性（具名假设，CTS77 §1 Lemme 5）**：flasque 消解的右端项的
**相似类只依赖 `M`**——相似的两个格，其任意两条 flasque 消解的右端项相似。

⚠ **同族问题（2026-10-11）**：与 `FlasqueResolutionHyp` 同源——本形对 `M` 未加格前提；
在**平凡群**档可用 `0 → ℤ --×2--> ℤ → ℤ/2 → 0` 与 `0 → ℤ --id--> ℤ → 0 → 0` 两条合法消解
给出 `ℤ/2 ≁ 0` 的反例（**机器核验待补** ✗，卡点见 `[[proj-ABGV52-hypA-blockers]]`）。
全工程**无消费者** ✓（主循环核实），故无空洞真污染 ✓。

（论文记 `ρ(M) := [F]`；本件把「类」这一层留给本假设，避免引入商类型。） -/
def FlasqueClassWellDefinedHyp (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ (M M' : Rep.{0,0,0} ℤ G) (R : FlasqueResolution G M) (R' : FlasqueResolution G M'),
    IsSimilar G M M' → IsSimilar G R.F R'.F

/-- **类型锁定断言**（`FlasqueClassWellDefinedHyp`）。 -/
example (G : Type) [Group G] [Fintype G] :
    FlasqueClassWellDefinedHyp G ↔
      ∀ (M M' : Rep.{0,0,0} ℤ G) (R : FlasqueResolution G M) (R' : FlasqueResolution G M'),
        IsSimilar G M M' → IsSimilar G R.F R'.F :=
  Iff.rfl

/-- **非空洞性对照（L1）**：具名假设的**结论类非空**——取同一 `M`、同一条消解，
`M ∼ M` 时结论 `R.F ∼ R.F` 由自反性成立（即该假设不是空类上的断言）。 -/
theorem flasqueClassWellDefined_conclusion_satisfiable {G : Type} [Group G] [Fintype G]
    (M : Rep.{0,0,0} ℤ G) (R : FlasqueResolution G M) :
    IsSimilar G R.F R.F :=
  isSimilar_refl G R.F

/-! ## §4 `lem:invertible-coflasque`（2.6）：真证明 -/

/-- **`coh¹` 沿收缩拉回**（一般群 `G` 版；`EMQuasi_ABGV52.subsingleton_coh1_of_retract`
的泛化）：若 `γ ≫ δ = 𝟙 A` 且 `coh¹(B) = 0`，则 `coh¹(A) = 0`。

（论文 2.6 证明的第一句「上同调可加 ⟹ `coh¹(G,M)` 是 `coh¹(G,P)` 的直和项」的
形式化：直和项的收缩数据即 `(γ, δ, h)`。） -/
theorem subsingleton_cohomology_one_of_retract {G : Type} [Group G]
    {A B : Rep.{0,0,0} ℤ G} (γ : A ⟶ B) (δ : B ⟶ A) (h : γ ≫ δ = 𝟙 A)
    (hB : Subsingleton ↥(groupCohomology B 1)) :
    Subsingleton ↥(groupCohomology A 1) := by
  haveI := hB
  have hid : ∀ z : ↥(groupCohomology A 1),
      (groupCohomology.map (MonoidHom.id G) δ 1).hom
        ((groupCohomology.map (MonoidHom.id G) γ 1).hom z) = z := by
    intro z
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, h, groupCohomology.map_id]
    rfl
  refine ⟨fun x y => ?_⟩
  calc x = (groupCohomology.map (MonoidHom.id G) δ 1).hom
        ((groupCohomology.map (MonoidHom.id G) γ 1).hom x) := (hid x).symm
    _ = (groupCohomology.map (MonoidHom.id G) δ 1).hom
        ((groupCohomology.map (MonoidHom.id G) γ 1).hom y) := by
        rw [Subsingleton.elim ((groupCohomology.map (MonoidHom.id G) γ 1).hom x)
          ((groupCohomology.map (MonoidHom.id G) γ 1).hom y)]
    _ = y := hid y

/-- **`Subsingleton` 沿 `LinearEquiv` 拉回**（工程内 `EMQuasi` 同名件的本文件副本，
避免依赖其导入面；证明一行）。 -/
theorem subsingleton_of_linearEquiv' {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : Subsingleton W) :
    Subsingleton V := by
  haveI := h
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- **`lem:invertible-coflasque`（2.6），顶层群形（本件真证的定理）**：
`H` 的 `ℤ[H]`-格 `M` 若是置换格的直和项，则 `coh¹(H, M) = 0`。

证明照论文：`M ⊕ M' ≅ P`（`P` 置换）⟹ `coh¹(H,M)` 是 `coh¹(H,P)` 的收缩
（`γ := biprod.inl ≫ e.hom`、`δ := e.inv ≫ biprod.fst`）⟹ 由
`EMQuasi_ABGV52.subsingleton_perm_coh1`（其内部即论文所引 Shapiro ＋ `coh¹(K,ℤ)=0`）
得 `coh¹(H,P) = 0` ⟹ 收缩拉回。 -/
theorem coflasque_top_of_isInvertible (M : Rep.{0,0,0} ℤ H) (h : IsInvertible H M) :
    Subsingleton (coh M 1) := by
  obtain ⟨N, P, hP, ⟨e⟩⟩ := h
  have hP' : _root_.ABGV52.IsPermutationLattice P := (EM.isPermutationLattice_iff P).mp hP
  haveI hP1 : Subsingleton (coh P 1) := subsingleton_perm_coh1 P hP'
  refine subsingleton_cohomology_one_of_retract (A := M) (B := P)
    (biprod.inl (X := M) (Y := N) ≫ e.hom) (e.inv ≫ biprod.fst (X := M) (Y := N)) ?_ hP1
  calc (biprod.inl (X := M) (Y := N) ≫ e.hom) ≫ (e.inv ≫ biprod.fst (X := M) (Y := N))
      = (biprod.inl ≫ (e.hom ≫ e.inv)) ≫ biprod.fst := by simp only [Category.assoc]
    _ = (biprod.inl ≫ 𝟙 (M ⊞ N)) ≫ biprod.fst := by rw [Iso.hom_inv_id]
    _ = biprod.inl ≫ biprod.fst := by rw [Category.comp_id]
    _ = 𝟙 M := biprod.inl_fst

/-- **2.6 全子群形的关键前提（第 2 轮已证——接口名与类型逐字保留）**：
置换 `ℤ[H]`-格限制到任意子群 `K ≤ H` 后 `coh¹` 消没。

论文的证明此步 = Shapiro 引理 `ℤ[H/K] ≅ Ind_K^H(ℤ)` ⟹ `coh¹(H,ℤ[H/K]) ≅ coh¹(K,ℤ)`
＋ `coh¹(K,ℤ) ≅ Hom(K,ℤ) = 0`。第 1 轮此处是**登记的缺口**（工程内的
`subsingleton_permHK`／`subsingleton_perm_coh1` 固定顶层群 `H`）；第 2 轮由
`SubgroupPerm_ABGV52.lean` 在**任意有限群**上重建该层后证成，见下 `subgroupPermCoh1Hyp`。 -/
def SubgroupPermCoh1Hyp : Prop :=
  ∀ (K : Subgroup H) (P : Rep.{0,0,0} ℤ H),
    _root_.ABGV52.IsPermutationLattice P →
      Subsingleton ↥(groupCohomology (Rep.res K.subtype P) 1)

/-- **类型锁定断言**（`SubgroupPermCoh1Hyp`）。 -/
example : SubgroupPermCoh1Hyp ↔
    ∀ (K : Subgroup H) (P : Rep.{0,0,0} ℤ H),
      _root_.ABGV52.IsPermutationLattice P →
        Subsingleton ↥(groupCohomology (Rep.res K.subtype P) 1) :=
  Iff.rfl

/-- **`SubgroupPermCoh1Hyp` 的证明（缺口 1 闭合）**：即
`SubgroupPerm_ABGV52.subsingleton_coh1_res_of_permutation`
（置换格沿子群限制仍是置换格 ＋ 任意有限群上置换格的 `coh¹` 消没）。 -/
theorem subgroupPermCoh1Hyp : SubgroupPermCoh1Hyp :=
  fun K P hP => subsingleton_coh1_res_of_permutation K P hP

/-- **`lem:invertible-coflasque`（2.6），全子群形**（**保留第 1 轮的接线形状**：
显式接受 `SubgroupPermCoh1Hyp` 前提；旧调用点无需改动，`hgap` 现由
`subgroupPermCoh1Hyp` 填充）：可逆 `ℤ[H]`-格 `M` 是 **coflasque**。

归约本件真证：对任意 `K ≤ H`，`M|_K` 是 `P|_K` 的直和项，故 `coh¹(K, M|_K)` 是
`coh¹(K, P|_K)` 的收缩（收缩引理取 `γ := Rep.res K.subtype (biprod.inl ≫ e.hom)` 等），
后者由前提为零。 -/
theorem isCoflasque_of_isInvertible_of_hyp (hgap : SubgroupPermCoh1Hyp)
    (M : Rep.{0,0,0} ℤ H) (h : IsInvertible H M) : IsCoflasque H M := by
  obtain ⟨N, P, hP, ⟨e⟩⟩ := h
  have hP' : _root_.ABGV52.IsPermutationLattice P := (EM.isPermutationLattice_iff P).mp hP
  intro K
  -- `M|_K` 是 `P|_K` 的直和项：收缩数据取 `Rep.res K.subtype` 下的像
  have hres : Subsingleton ↥(groupCohomology (Rep.res K.subtype P) 1) := hgap K P hP'
  haveI := hres
  refine subsingleton_cohomology_one_of_retract
    (G := ↥K) (A := Rep.res K.subtype M) (B := Rep.res K.subtype P)
    ((Rep.resFunctor K.subtype).map (biprod.inl (X := M) (Y := N) ≫ e.hom))
    ((Rep.resFunctor K.subtype).map (e.inv ≫ biprod.fst (X := M) (Y := N)))
    ?_ hres
  -- 收缩恒等式在 `M` 层先证，再沿 `Rep.res` 搬运（函子性）
  have hcomp : (biprod.inl (X := M) (Y := N) ≫ e.hom)
      ≫ (e.inv ≫ biprod.fst (X := M) (Y := N)) = 𝟙 M := by
    calc (biprod.inl (X := M) (Y := N) ≫ e.hom) ≫ (e.inv ≫ biprod.fst (X := M) (Y := N))
        = (biprod.inl ≫ (e.hom ≫ e.inv)) ≫ biprod.fst := by simp only [Category.assoc]
      _ = (biprod.inl ≫ 𝟙 (M ⊞ N)) ≫ biprod.fst := by rw [Iso.hom_inv_id]
      _ = biprod.inl ≫ biprod.fst := by rw [Category.comp_id]
      _ = 𝟙 M := biprod.inl_fst
  rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro x
  simpa [Rep.comp_apply, Rep.id_apply, Rep.resMap_hom_apply, Iso.hom_inv_id_apply] using
    EM.biprod_inl_fst_apply M N x

/-- **`lem:invertible-coflasque`（2.6），全子群形——无前提**：可逆 `ℤ[H]`-格 `M` 是
**coflasque**（`IsCoflasque`，即论文 2.6 的逐字结论）。前提由第 2 轮证成的
`subgroupPermCoh1Hyp` 填充。 -/
theorem isCoflasque_of_isInvertible
    (M : Rep.{0,0,0} ℤ H) (h : IsInvertible H M) : IsCoflasque H M :=
  isCoflasque_of_isInvertible_of_hyp subgroupPermCoh1Hyp M h

/-! ## §4.5 M5（**B 档②**）的具名残余：**flasque 类的双有理不变性** ✓（源印 189 ✓ **第 136 轮读图逐字核** ✓） -/

/-- **flasque 类的双有理不变性**（M5／B 档② 的**具名残余** ✓）。

**源逐字** ✓（`raw/Saltman1984.{tex,pdf}` ✓，**印 189** ＝ PDF 25 ✓，**印刷页 = PDF + 164** ✓）：
「Also, `Q(L/F,M)` is stably isomorphic to `Q(L/F,N)` over `F` **if and only if** `ρ(M) = ρ(N)`.
In particular, `Q(L/F,M)` is **stably rational if and only if** `ρ(M) = 0`」✓；
同页给出 `ρ` 的定义 ✓：「if `0 → M → P → E → 0` is a **flasque resolution** of `M`, then `ρ(M)` is defined
to be the **similarity class** of `E`」✓。

**用点形** ✓（状态笔记 §5.2 ✓：「`EMHyp` **只需其 H 档特例**」✓）：取「**`⟹`**」方向 ✓ ＋
**抽象稳定有理性谓词** `SRat` ✓（与 `EMHyp` ✓ **同款工艺** ✓ —— `K` 即 `Q(L/F,M)` ✓、`SRat K` 即「`K` 稳定有理」✓）。

**⚠ 三处登记** ✗：
① **具名残余** ✓：本件**不作证明** ✗（源把该行作为**观察**给出 ✓，其证明见所引 `[6]`／`[27]` 等 ✗ ——
**本仓未摄** ✗）；
② **编码** ✓（**一处须精确** ✓）：源 `ρ(M) = 0` 的**字面**编码是 **`IsSimilar G M 0`** ✓
（直接对照源对 `ρ` 的 `similarity class` 定义 ✓）—— 但 `Rep.{0,0,0} ℤ G` **无直接可用的 `Zero` 实例** ✗
（**已在册** ✓，状态笔记 §9 的 `positive_control_gap_registered` ✓；**⚠ 其障碍已于第 137 轮查明并解除** ✓ ——
见 **§4.6** ✓）⟹ 本件取工程**既有**编码
**`IsInvertible G M`** ✓（＝「`M` 是某置换格的直和项」✓，本件 `:153` ✓ —— 与 `RetractCriterionHyp` ✓ 语境
及 `NotRetract` ✓ 用法一致 ✓）。**⚠ 两者关系** ✓：**正向** ＝ **第 137 轮已证** ✓✅
（`isInvertible_of_isSimilar_zero` ✓，见 **§4.6** ✓；第 136 轮原记「未证」✗ —— **留痕** ✓）：
`IsSimilar G M 0 → IsInvertible G M` **已证** ✓；**⚠ 其逆**一般**不**成立 ✗（`IsInvertible` 的补项 `N`
**任意** ✗，**弱于** `IsSimilar G M 0` 的「置换补项」✓）⟹ 本件用的是**较弱**的结论 ✓（**证之仍证源** ✓）—— **登记** ✓；
③ **抽象化** ✓：`K` 与 `SRat` 是**抽象**的 ✗ ⟹ 本陈述**不含**「`K = Q(L/F,M)`」的识别 ✓
（该识别**未建** ✗，与 `EMHyp` ✓ 同一取舍 ✓）。 -/
def BirationalInvarianceStatement (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G)
    (K : Type) (SRat : Type → Prop) : Prop :=
  SRat K → IsInvertible G M

/-- **外形锁定** ✓：`BirationalInvarianceStatement` 的两段（**前提** `SRat K` ✓／**结论** `IsInvertible G M` ✓）
逐字可取 ✓ —— 前提被吞或结论改形即失败 ✓。 -/
example (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G) (K : Type) (SRat : Type → Prop) :
    BirationalInvarianceStatement G M K SRat = (SRat K → IsInvertible G M) := rfl

/-- **L1 探针（非空洞）** ✓：结论成立时本陈述成立 ✓ ⟹ 假设类**非空** ✓（**不是**空类上的空洞结论 ✓）。 -/
theorem birationalInvarianceStatement_of_isInvertible (G : Type) [Group G]
    (M : Rep.{0,0,0} ℤ G) (K : Type) (SRat : Type → Prop) (h : IsInvertible G M) :
    BirationalInvarianceStatement G M K SRat :=
  fun _ => h

/-- **L19 判别力（非退化）** ✓：取 `SRat := fun _ => True` ✓ 时本陈述**恰等于** `IsInvertible G M` ✓
（＝ `ρ(M) = 0` 本身 ✓）⟹ 本陈述**不是**恒真 ✓、**不是**空壳 ✓（把它改弱成 `True` ✗ 即失败 ✓）。 -/
theorem birationalInvarianceStatement_iff_isInvertible (G : Type) [Group G]
    (M : Rep.{0,0,0} ℤ G) (K : Type) :
    BirationalInvarianceStatement G M K (fun _ => True) ↔ IsInvertible G M :=
  ⟨fun h => h trivial, fun h _ => h⟩

/-! ## §4.6 M5 的**编码桥**：`IsSimilar G M 0 ⟹ IsInvertible G M` ✓（第 137 轮；**解 §9 的零对象登记** ✓）

**⚠ 工艺读数 ㊴** ✓：**「无 `Zero` 实例」≠「零对象不可得」** ✗ —— mathlib 的 `HasZeroObject.zero'`
（即 `Zero C` 实例 ✓）**故意**注册为 **`scoped[ZeroObject]`** ✗（`CategoryTheory/Limits/Shapes/ZeroObjects.lean`
逐字：「This **cannot** be a global instance as it will trigger for every `Zero C` typeclass search」✓）⟹
**`open scoped ZeroObject`** ✓ 即得 `(0 : Rep.{0,0,0} ℤ G)` ✓（**实测** ✓）。**§9** 的
`positive_control_gap_registered`（逐字：「`Rep.{0,0,0} ℤ G` **无可直接用 `Zero` 实例**」✗）**其障碍即此** ✓。
**同族** ✓：**㊲**（`synthInstanceFailed` ≠ 不可得 ✓）—— 两者同形状 ＝ **把「我没找到」误读为「不存在」** ✗；
**本条多一层** ✓：**找到了，但没打开作用域** ✗（`scoped` 实例**不在**全局搜索里 ✓）。 -/

section EncodingBridge

open scoped ZeroObject

/-- **M5 编码桥** ✓（**第 136 轮**所登记「`IsSimilar G M 0` 与 `IsInvertible G M` 关系未证」✗ 的**正向** ✓）：
`M ∼ 0` ⟹ `M` 可逆 ✓ —— 即源 `ρ(M) = 0` 的**字面形** ✓ ⟹ 工程编码 `IsInvertible G M` ✓。

**证明** ✓：`IsSimilar G M 0` 展开为 `∃ S₁ S₂, 置换 S₁ ∧ 置换 S₂ ∧ Nonempty (M ⊞ S₁ ≅ 0 ⊞ S₂)` ✓；
取 `N := S₁` ✓、`P := S₂` ✓，并用 `isoZeroBiprod` ✓（`Y ≅ 0 ⊞ Y` ✓，取 `symm` ✓）把 `0 ⊞ S₂` 换成 `S₂` ✓
⟹ `IsInvertible G M` ✓（**无需**任何新 import ✓）。 -/
theorem isInvertible_of_isSimilar_zero (G : Type) [Group G] (M : Rep.{0,0,0} ℤ G)
    (h : IsSimilar G M 0) : IsInvertible G M := by
  obtain ⟨S₁, S₂, _h₁, h₂, ⟨e⟩⟩ := h
  exact ⟨S₁, S₂, h₂, ⟨e ≪≫ (isoZeroBiprod (isZero_zero (Rep.{0,0,0} ℤ G))).symm⟩⟩

/-- **L1 探针（`IsInvertible` 非空）** ✓（**本件首条见证** ✓）：**零模可逆** ✓ —— 由 `isSimilar_refl` ✓
（`0 ∼ 0` ✓）与 `isInvertible_of_isSimilar_zero` ✓ 立得 ✓ ⟹ `IsInvertible` 的**类非空** ✓
（**登记** ✓：本件在**本条之前**无任何 `IsInvertible` 的见证 ✗，见 §4.6 说明 ✓）。 -/
theorem isInvertible_zero (G : Type) [Group G] : IsInvertible G (0 : Rep.{0,0,0} ℤ G) :=
  isInvertible_of_isSimilar_zero G 0 (isSimilar_refl G 0)

end EncodingBridge

/-! ## §5 公理闸门 -/

#print axioms isSimilar_refl
#print axioms isSimilar_symm
#print axioms isSimilar_trans
#print axioms isSimilar_equivalence
#print axioms isPermutationLattice_biprod
#print axioms flasqueResolution_of_hyp
#print axioms flasqueClassWellDefined_conclusion_satisfiable
#print axioms subsingleton_cohomology_one_of_retract
#print axioms coflasque_top_of_isInvertible
#print axioms subgroupPermCoh1Hyp
#print axioms isCoflasque_of_isInvertible
#print axioms isCoflasque_of_isInvertible_of_hyp
#print axioms BirationalInvarianceStatement
#print axioms birationalInvarianceStatement_of_isInvertible
#print axioms birationalInvarianceStatement_iff_isInvertible
#print axioms isInvertible_of_isSimilar_zero
#print axioms isInvertible_zero

end ABGV52
