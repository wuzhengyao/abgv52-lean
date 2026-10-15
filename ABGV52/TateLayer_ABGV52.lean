/-
  ABGV-5.2 —— **Tate 上同调层**（2026-10-11）：`Ĥ^{-1}` 侧的第一批**真证实例**，
  以及「置换格 ⟹ flasque」的**具名缺口接口**。

  本件填的缺口（背景）
  ====================
  `Flasque_ABGV52.lean` 把论文 `def:flasque-coflasque`（2.3）的 flasque 侧
  `IsFlasque G M := ∀ K : Subgroup G, Subsingleton (tateHMinusOneSub G K M)`
  给成**具体定义**（非公理），但全工程此前**没有任何 `IsFlasque` 实例**：
  coflasque（`coh¹`）侧有 Shapiro 桥（`SubgroupPerm_ABGV52.lean`），
  `Ĥ^{-1}`（Tate 负一次）侧完全空白。本件补两个**基例**，二者都是真证：

    * **T1（平凡群基例）**：`IsFlasque PUnit M`，对**一切** `M : Rep.{0,0,0} ℤ PUnit` ✓。
      数学：`G = 1` ⟹ `tateNorm = ρ(1) = id` ⟹ `ker(tateNorm) = 0` ⟹ 该处同调为 `0`。
    * **T2b（平凡模 `ℤ` 基例，一切有限群）**：`IsFlasque G (Rep.trivial ℤ G ℤ)` ✓。
      数学：`M = ℤ` 平凡作用 ⟹ `tateNorm = ×|G|`；`ℤ` 无挠且 `|G| ≠ 0` ⟹ 单 ⟹ 同调为 `0`。
      这是全工程**第一个非平凡群上的非平凡 flasque 实例**（`G` 任意有限群）。

  本件**未**证的（T2 主体，逐字登记，见 §4）
  =========================================
  「置换格 ⟹ flasque」（`EM.IsPermutationLattice G P → IsFlasque G P`）**未证**。
  其三步骨架为 ① 限制的陪集分解 `ℤ[G/K₀]|_K ≅ ⨁_{陪集} ℤ[K/L_i]`、
  ② Shapiro 型 `Ĥ^{-1}(K, ℤ[K/L]) ≅ Ĥ^{-1}(L, ℤ)`、③ 基例 `Ĥ^{-1}(L, ℤ) = 0`。
  本件已完成 **③**（即 T2b）；**① 与 ② 未完成**。卡点逐字：
    * mathlib `Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean`
      （246 行）**无 Shapiro 引理、无 coind 构造、无任何具体计算引理**；
      其仅有的两座「可算桥」`isoGroupCohomology (n) [NeZero n]`／
      `isoGroupHomology (m) (n) (hmn : m = -(n+1)) [NeZero n]` 在 `n = 0`
      （即 `m = -1`，正是 `Ĥ^{-1}`）处**均不适用** ⟹ `Ĥ^{-1}` 是唯一没有现成
      群同调/同调桥的指标 ✗。
    * 故本件对 T2 主体按工程 `EM_ABGV52`／`Saltman_ABGV52` 的**具名假设工艺**给出：
      类型锁 ＋ 接线 ＋ 非空洞探针（§4），并把「平凡群档已落实」作为一致性探针
      （`permLatticeFlasqueHyp_punit`，由 T1 直接填出）✓。

  **无 sorry、无自造公理**；`#print axioms` 门见 §5。
-/
import ABGV52.Flasque_ABGV52
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

open CategoryTheory CategoryTheory.Limits

-- 与 `EMQuasi_ABGV52`／`Flasque_ABGV52` 同款：`ℤ` 上 `AddCommGroup.toIntModule`
-- 与 `Rep.hV2` 争用 `Module ℤ ↥X`。
set_option linter.style.haveILetI false

namespace ABGV52

attribute [local instance 1500] Rep.hV2

/-! ## §1 一般砖：`tateNorm` 单 ⟹ `Ĥ^{-1}` 消没 -/

/-- **一般砖（本件所有实例的共同引擎）**：若 `M.tateNorm` 单，则 `Ĥ^{-1}(G,M) = 0`。

证明：`Ĥ^{-1}` 是 Tate 复形在 `-1` 处的同调，即短复形
`M_1 --d_{-2,-1}--> M_0 --tateNorm--> M^G` 的同调。`tateNorm` 单（mathlib 记
`Rep.tateNorm_comp_d`／`Rep.d_comp_tateNorm` 已保证复形条件）⟹ `S.f = 0`
（`cancel_mono`）⟹ 由 `ShortComplex.exact_iff_mono` 得 `S.Exact` ⟹
`HomologicalComplex.ExactAt.isZero_homology` 给该处同调为零 ⟹
`ModuleCat.subsingleton_of_isZero`。 -/
theorem subsingleton_tateCohomology_neg_one_of_mono_tateNorm (G : Type) [Group G] [Fintype G]
    (M : Rep.{0,0,0} ℤ G) (h : Mono M.tateNorm) :
    Subsingleton ↥(tateCohomology M (-1)) := by
  have hmono' : Mono ((tateComplex M).d (-1) 0) := h
  have hex : (tateComplex M).ExactAt (-1) := by
    rw [HomologicalComplex.exactAt_iff' (K := tateComplex M) (i := -2) (j := -1) (k := 0)
      (by simp) (by simp)]
    have hg : ((tateComplex M).sc' (-2) (-1) 0).g = (tateComplex M).d (-1) 0 := rfl
    haveI : Mono ((tateComplex M).sc' (-2) (-1) 0).g := by rw [hg]; exact hmono'
    have hf : ((tateComplex M).sc' (-2) (-1) 0).f = 0 :=
      (cancel_mono _).mp (by rw [ShortComplex.zero, zero_comp])
    exact (ShortComplex.exact_iff_mono _ hf).mpr inferInstance
  exact ModuleCat.subsingleton_of_isZero (HomologicalComplex.ExactAt.isZero_homology hex)

/-- **一般砖**：`M.norm` 单 ⟹ `M.tateNorm` 单。

`Rep.tateNorm = chainsIso₀ ≫ M.norm.asHom.toModuleCatHom ≫ cochainsIso₀.inv`（mathlib 定义），
两端是 `≅ M` 的同构 ⟹ 单性只取决于中间的 `M.norm`。 -/
theorem mono_tateNorm_of_mono_norm (G : Type) [Group G] [Fintype G]
    (M : Rep.{0,0,0} ℤ G) (h : Mono M.norm.asHom.toModuleCatHom) : Mono M.tateNorm := by
  haveI := h
  show Mono ((groupHomology.chainsIso₀ M).hom ≫ M.norm.asHom.toModuleCatHom ≫
    (groupCohomology.cochainsIso₀ M).inv)
  infer_instance

/-- **一般砖**：`IsFlasque` 沿同构搬运（T2 的接线必需——`IsPermutationLattice` 是
「同构于某个 `ℤ[X]`」的**存在**形）。 -/
theorem isFlasque_of_iso (G : Type) [Group G] [Fintype G] {M N : Rep.{0,0,0} ℤ G}
    (e : M ≅ N) (h : IsFlasque G M) : IsFlasque G N := by
  intro K
  haveI hK : Subsingleton (tateHMinusOneSub G K M) := h K
  have hz : IsZero (@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K)
      (Rep.res K.subtype M) (-1)) := ModuleCat.isZero_of_subsingleton _
  have hiso : (@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K) (Rep.res K.subtype M) (-1))
      ≅ (@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K) (Rep.res K.subtype N) (-1)) :=
    (@tateCohomologyFunctor ℤ ↥K _ _ (Fintype.ofFinite ↥K) (-1)).mapIso
      ((Rep.resFunctor K.subtype).mapIso e)
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso hiso.symm)

/-! ## §2 T1：平凡群基例 `IsFlasque PUnit M`（对一切 `M`） -/

/-- **T1 第一步**：平凡群上的范数映射是恒等。
`Representation.norm ρ = ∑ g, ρ g`，而 `Subsingleton G` ⟹ 全部 `g = 1`
（`Finset.sum_eq_single 1`）⟹ 和 = `ρ 1 = 1`。 -/
theorem norm_eq_one_of_subsingleton (G : Type) [Group G] [Fintype G] [Subsingleton G]
    (M : Rep.{0,0,0} ℤ G) : M.ρ.norm = 1 := by
  rw [Representation.norm]
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro b _ hb; exact absurd (Subsingleton.elim b 1) hb
  · intro h; exact absurd (Finset.mem_univ 1) h

/-- **T1 第二步**：平凡群上 `M.norm = 𝟙 M`（逐元素经 `Rep.norm_apply`）。 -/
theorem norm_eq_id_of_subsingleton (G : Type) [Group G] [Fintype G] [Subsingleton G]
    (M : Rep.{0,0,0} ℤ G) : M.norm = 1 := by
  have h0 : M.ρ.norm = 1 := norm_eq_one_of_subsingleton G M
  apply End.ext
  rw [End.one_asHom, Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro x
  change (M.norm.asHom.hom) x = x
  simp [Rep.norm_apply, h0]

/-- **T1 第三步**：平凡群上 `tateNorm` 是恒等（复合两个同构与 `𝟙`）⟹ 单。 -/
theorem mono_tateNorm_of_subsingleton (G : Type) [Group G] [Fintype G] [Subsingleton G]
    (M : Rep.{0,0,0} ℤ G) : Mono M.tateNorm := by
  apply mono_tateNorm_of_mono_norm
  rw [show M.norm.asHom.toModuleCatHom = 𝟙 (ModuleCat.of ℤ M.V) from by
    rw [norm_eq_id_of_subsingleton G M]; rfl]
  infer_instance

/-- **T1（主计算）**：平凡群上 `Ĥ^{-1}(G,M) = 0`，对一切 `M`。 -/
theorem subsingleton_tateCohomology_neg_one_of_subsingleton (G : Type) [Group G] [Fintype G]
    [Subsingleton G] (M : Rep.{0,0,0} ℤ G) :
    Subsingleton ↥(tateCohomology M (-1)) :=
  subsingleton_tateCohomology_neg_one_of_mono_tateNorm G M
    (mono_tateNorm_of_subsingleton G M)

/-- **T1（flasque 形，任意平凡群）**：`IsFlasque G M` 对一切 `M`（`G` 平凡）。

子群 `K ≤ G` 自动平凡（`↥K` 是 `PUnit` 的子类型），故把
`subsingleton_tateCohomology_neg_one_of_subsingleton` 用在 `↥K` 与 `M|_K` 上。 -/
theorem isFlasque_of_subsingleton (G : Type) [Group G] [Fintype G] [Subsingleton G]
    (M : Rep.{0,0,0} ℤ G) : IsFlasque G M := by
  intro K
  haveI hsub : Subsingleton ↥K := ⟨fun a b => Subtype.ext (Subsingleton.elim (a : G) (b : G))⟩
  exact @subsingleton_tateCohomology_neg_one_of_subsingleton ↥K _ (Fintype.ofFinite ↥K) hsub
    (Rep.res K.subtype M)

/-- **T1（逐点子群形，接线形状）**：`PUnit` 的每个子群上 `Ĥ^{-1}` 消没
（旧接口 `tateHMinusOneSub` 的逐点读数，供下游直接引用）。 -/
theorem subsingleton_tateHMinusOneSub_punit (M : Rep.{0,0,0} ℤ PUnit)
    (K : Subgroup PUnit) : Subsingleton (tateHMinusOneSub PUnit K M) :=
  isFlasque_of_subsingleton PUnit M K

/-- **T1（本件主结论）**：`IsFlasque PUnit M` 对**一切** `M : Rep.{0,0,0} ℤ PUnit`。 -/
theorem isFlasque_punit (M : Rep.{0,0,0} ℤ PUnit) : IsFlasque PUnit M :=
  isFlasque_of_subsingleton PUnit M

/-- **类型锁定断言**（T1）：结论外形一旦被改动，本 `Iff.rfl` 立即编译失败。 -/
example (M : Rep.{0,0,0} ℤ PUnit) :
    IsFlasque PUnit M ↔ ∀ K : Subgroup PUnit, Subsingleton (tateHMinusOneSub PUnit K M) :=
  Iff.rfl

/-! ## §3 T2b：平凡模 `ℤ` 基例（一切有限群） -/

/-- **T2b 第一步**：平凡表示上 `norm = |G| • id`。 -/
theorem norm_trivialRep_eq_card_nsmul (G : Type) [Group G] [Fintype G] :
    (Rep.trivial ℤ G ℤ).ρ.norm = Fintype.card G • (LinearMap.id : Module.End ℤ ℤ) := by
  rw [Representation.norm]
  ext v
  simp [Finset.sum_const, Finset.card_univ, Representation.trivial_apply]

/-- **T2b 第二步**：`(M.norm).toModuleCatHom = ×|G|`，在 `ℤ` 上单（无挠 ＋ `|G| ≠ 0`）。 -/
theorem mono_norm_toModuleCatHom_trivialRep (G : Type) [Group G] [Fintype G] :
    Mono (Rep.trivial ℤ G ℤ).norm.asHom.toModuleCatHom := by
  rw [show (Rep.trivial ℤ G ℤ).norm.asHom.toModuleCatHom
      = ModuleCat.ofHom ((Rep.trivial ℤ G ℤ).ρ.norm) from rfl,
    norm_trivialRep_eq_card_nsmul G, ModuleCat.mono_iff_injective]
  intro a b hab
  refine mul_left_cancel₀ (b := a) (c := b)
    (Int.natCast_ne_zero.mpr (Fintype.card_ne_zero (α := G))) ?_
  simpa [nsmul_eq_mul] using hab

/-- **T2b 第三步**：`tateNorm` 单。 -/
theorem mono_tateNorm_trivialRep (G : Type) [Group G] [Fintype G] :
    Mono (Rep.trivial ℤ G ℤ).tateNorm :=
  mono_tateNorm_of_mono_norm G _ (mono_norm_toModuleCatHom_trivialRep G)

/-- **T2b（主计算）**：`Ĥ^{-1}(G, ℤ) = 0`，对一切有限群 `G`（平凡作用）。 -/
theorem subsingleton_tateCohomology_neg_one_trivialRep (G : Type) [Group G] [Fintype G] :
    Subsingleton ↥(tateCohomology (Rep.trivial ℤ G ℤ) (-1)) :=
  subsingleton_tateCohomology_neg_one_of_mono_tateNorm G _
    (mono_tateNorm_trivialRep G)

/-- **T2b 第四步（限制到子群仍是平凡模）**：`(Rep.trivial ℤ G ℤ)|_K = Rep.trivial ℤ ↥K ℤ`
（对象相等，非仅同构）——故 T2b 的基例可对一切子群 `K` 直接复用。 -/
theorem res_trivialRep_eq (G : Type) [Group G] [Fintype G] (K : Subgroup G) :
    Rep.res K.subtype (Rep.trivial ℤ G ℤ) = Rep.trivial ℤ ↥K ℤ := by
  show Rep.of (X := ℤ) ((Rep.trivial ℤ G ℤ).ρ.comp K.subtype)
    = Rep.of (X := ℤ) (Representation.trivial ℤ ↥K ℤ)
  rw [show (Rep.trivial ℤ G ℤ).ρ = Representation.trivial ℤ G ℤ from rfl,
    show Representation.trivial ℤ G ℤ = (1 : Representation ℤ G ℤ) from rfl,
    MonoidHom.one_comp,
    show (1 : Representation ℤ ↥K ℤ) = Representation.trivial ℤ ↥K ℤ from rfl]

/-- **T2b（flasque 形，本件第二个主结论）**：平凡格 `ℤ` 是 **flasque**，对一切有限群 `G`。

这是全工程**第一个非平凡群上的 flasque 实例**：`IsFlasque` 此前只有定义没有实例。 -/
theorem isFlasque_trivialRep (G : Type) [Group G] [Fintype G] :
    IsFlasque G (Rep.trivial ℤ G ℤ) := by
  intro K
  rw [show tateHMinusOneSub G K (Rep.trivial ℤ G ℤ)
    = ↥(@tateCohomology ℤ ↥K _ _ (Fintype.ofFinite ↥K)
        (Rep.res K.subtype (Rep.trivial ℤ G ℤ)) (-1)) from rfl,
    res_trivialRep_eq G K]
  exact @subsingleton_tateCohomology_neg_one_trivialRep ↥K _ (Fintype.ofFinite ↥K)

/-- **类型锁定断言**（T2b）。 -/
example (G : Type) [Group G] [Fintype G] :
    IsFlasque G (Rep.trivial ℤ G ℤ) ↔
      ∀ K : Subgroup G, Subsingleton
        (tateHMinusOneSub G K (Rep.trivial ℤ G ℤ)) :=
  Iff.rfl

/-! ## §4 T2c：「置换格 ⟹ flasque」的具名缺口

论文 2.5（`prop:flasque-resolution`）的证明用到「置换格是 flasque」。本工程
`Flasque_ABGV52.lean` 的 `IsFlasque` 是具体定义，但该结论**未证**（卡点见文件头）。
按 `EM_ABGV52`／`Saltman_ABGV52` 的具名假设工艺给出接口。 -/

/-- **「置换格 ⟹ flasque」（具名假设，论文 2.5 证明所用）**：
置换 `ℤ[G]`-格都是 flasque。

三步骨架与各自现状：
  ① `ℤ[G/K₀]|_K ≅ ⨁_{陪集} ℤ[K/L_i]`——**未证**（工程内 `SubgroupPerm_ABGV52` 的
     陪集轨道幂等分解是 `coh¹` 侧机器，未移植到 Tate 侧）；
  ② Shapiro 型 `Ĥ^{-1}(K, ℤ[K/L]) ≅ Ĥ^{-1}(L, ℤ)`——**未证**（mathlib 无 Tate 侧 Shapiro）；
  ③ 基例 `Ĥ^{-1}(L, ℤ) = 0`——**已证**，即本件 §3 的
     `subsingleton_tateCohomology_neg_one_trivialRep` ✓。 -/
def PermutationLatticeFlasqueHyp (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ P : Rep.{0,0,0} ℤ G, EM.IsPermutationLattice G P → IsFlasque G P

/-- **类型锁定断言**（`PermutationLatticeFlasqueHyp`）。 -/
example (G : Type) [Group G] [Fintype G] :
    PermutationLatticeFlasqueHyp G ↔
      ∀ P : Rep.{0,0,0} ℤ G, EM.IsPermutationLattice G P → IsFlasque G P :=
  Iff.rfl

/-- **接线**：由具名假设取出「置换格 ⟹ flasque」。 -/
theorem isFlasque_of_permutationLattice_of_hyp {G : Type} [Group G] [Fintype G]
    (h : PermutationLatticeFlasqueHyp G) (P : Rep.{0,0,0} ℤ G)
    (hP : EM.IsPermutationLattice G P) : IsFlasque G P :=
  h P hP

/-- **T2 结论非空（本件对 T2 的实质贡献）**：**存在**既是置换格又是 flasque 的 `ℤ[G]`-模
——取单点 `G`-集 `PUnit` 的置换模 `ℤ[PUnit]`（由 mathlib
`Rep.ofMulActionSubsingletonIsoTrivial` 同构于平凡格 `ℤ`，再用 §3 的 `isFlasque_trivialRep`）。

这把 T2 的缺口定位得更准：**结论不是空类**（已有实证对象），缺的是
「一切置换格都如此」的**一般机制**（陪集分解 ＋ Shapiro，见文件头）。 -/
theorem isFlasque_ofMulAction_punit (G : Type) [Group G] [Fintype G] :
    IsFlasque G (Rep.ofMulAction ℤ G PUnit) :=
  isFlasque_of_iso G (M := Rep.trivial ℤ G ℤ)
    (Rep.ofMulActionSubsingletonIsoTrivial (k := ℤ) (G := G) PUnit).symm
    (isFlasque_trivialRep G)

/-- **T2 结论非空（存在形）**：存在置换格 `P` 使 `IsFlasque G P`。 -/
theorem exists_flasque_permutationLattice (G : Type) [Group G] [Fintype G] :
    ∃ P : Rep.{0,0,0} ℤ G, EM.IsPermutationLattice G P ∧ IsFlasque G P :=
  ⟨Rep.ofMulAction ℤ G PUnit, EM.isPermutationLattice_trivial G,
    isFlasque_ofMulAction_punit G⟩

/-- **一致性探针（非空洞性，L1）**：平凡群档的具名假设**已被 T1 填出**——
即 `PermutationLatticeFlasqueHyp` 的结论在 `G = PUnit` 时对**一切** `P` 成立
（不只是置换格），故此假设**不是**空类上的断言。 -/
theorem permLatticeFlasqueHyp_punit : PermutationLatticeFlasqueHyp PUnit :=
  fun P _ => isFlasque_punit P

/-- **前提类非空探针（L10①）**：置换格类非空——正则置换格 `ℤ[G]` 是置换格
（工程既有 `EM.isPermutationLattice_trivial`）。与上一条合起来说明本假设的
前提与结论两侧都有实证对象。 -/
example (G : Type) [Group G] :
    EM.IsPermutationLattice G (Rep.ofMulAction ℤ G PUnit) :=
  EM.isPermutationLattice_trivial G

/-! ## §5 公理闸门 -/

#print axioms subsingleton_tateCohomology_neg_one_of_mono_tateNorm
#print axioms mono_tateNorm_of_mono_norm
#print axioms isFlasque_of_iso
#print axioms norm_eq_one_of_subsingleton
#print axioms norm_eq_id_of_subsingleton
#print axioms mono_tateNorm_of_subsingleton
#print axioms subsingleton_tateCohomology_neg_one_of_subsingleton
#print axioms isFlasque_of_subsingleton
#print axioms subsingleton_tateHMinusOneSub_punit
#print axioms isFlasque_punit
#print axioms norm_trivialRep_eq_card_nsmul
#print axioms mono_norm_toModuleCatHom_trivialRep
#print axioms mono_tateNorm_trivialRep
#print axioms subsingleton_tateCohomology_neg_one_trivialRep
#print axioms res_trivialRep_eq
#print axioms isFlasque_trivialRep
#print axioms isFlasque_of_permutationLattice_of_hyp
#print axioms isFlasque_ofMulAction_punit
#print axioms exists_flasque_permutationLattice
#print axioms permLatticeFlasqueHyp_punit

end ABGV52
