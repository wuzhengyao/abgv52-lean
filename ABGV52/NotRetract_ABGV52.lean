/-
  ABGV-5.2 —— 论文 2026-10-11 版 §4：`thm:not-retract-rational`（4.13）主定理

  论文 4.13：`H = C₃ × C₃`、`char F = 0` ⟹ `Z_H(F,9) = F(M|_H)^H` **非** retract rational。

  证明三块与本件落点
  ================
    (a) **有限指数置换超格分类**（`P ⊇ M|_H` 有限指数、`P` 置换 ⟹
        `P ≅ ℤ[H]^{⊕8} ⊕ ℤ`）：落点为 `Superlattice_ABGV52.lean`（重数方程的算术核心
        真证 + 格层分类作具名接口）。**本件的主定理不使用 (a)**：LES 步骤只需要
        「置换格上 `exp(coh²) ∣ 3`」这一条（论文 4.13 第 (b) 段的结论），而它由本工程
        既有的 `S4.perm_exp`（`Coh2ExpDvd3`，对**任意**置换格成立）直接给出——(a) 在论文
        中的用途是 `coh²(H,P) ≅ C₃×C₃` 的**同构识别**，而 LES 步骤只用指数整除 3。
        此点已逐字登记于 `§0 实现注记`。
    (b) `coh²(H,P)` 指数整除 3（`S4.perm_exp` ＋ `EM` 的 Shapiro 层）＋
        `coh²(H, M|_H) ≅ C₉`（`C8b.discriminant_pair_M_H_rep`）。
    (c) **度 1→2 LES 步骤**（本件 §1 真证）：`0 → M|_H → P → E → 0` 诱导
        `Ext¹(ℤtriv, E) → Ext²(ℤtriv, M|_H) --α--> Ext²(ℤtriv, P)`；若 `coh¹(H,E) = 0`
        则 `Ext¹(ℤtriv,E) = 0`，于是 `α` 单射，但 `Ext²(ℤtriv,P)` 上 `z+z+z = 0`
        而 `Ext²(ℤtriv, M|_H)` 有 `3`-不消没元（判别对）⟹ 矛盾 ⟹ `coh¹(H,E) ≠ 0`，
        `E` 不是 coflasque。
    最后：对 flasque 消解 `0 → M|_H → P → F → 0` 用 (c) ⟹ `coh¹(H,F) ≠ 0` ⟹
    `ρ(M|_H) = [F]` 不可逆（由 `Flasque_ABGV52.coflasque_top_of_isInvertible`（2.6 的
    顶层形）的逆否）⟹ 由 4.12 的具名假设（`RetractCrit_ABGV52.RetractCriterionHyp`）
    得非 retract rational。

  §0 实现注记（诚实登记，不掩盖）
  ============================
    * **2.6 的用法**：主定理的非 coflasque 见证取 `K = H` 本身（论文 4.13 末段
      `coh¹(H,E) ≠ 0`），故只需 2.6 的**顶层群形**——本件用
      `Flasque_ABGV52.coflasque_top_of_isInvertible`（真证），不需要 2.6 的全子群形
      （后者在 `Flasque_ABGV52` 中由 `SubgroupPermCoh1Hyp` 归约，缺口已逐字登记）。
    * **几何识别**：`Z_H(F,9) ≅ F(M|_H)^H` 在本件取 **`F`-代数同构**
      `Z ≃ₐ[F] ↥(EM.latticeInvariants F H (ker pi))` 形（搬运经 `SaltT2` 的
      `IsRetractRational.of_algEquiv`，真证）。工程的具名假设取 **C′ 修正形**
      `ProcHyp.ProcesiHypExact`（2026-10-10 第 44 改后；旧 `G.ProcesiHyp` 的核只取
      `ker φ`，已由 `ProcConsume` 头注 ⑥ 登记为假形状，本件不引用），它给出的是
      **环同构** `Z ≃+* F(Mp2)^H`；本件另给 `algEquiv_of_ringEquiv_linear`
      （环同构 ＋ `F`-线性 ⟹ `F`-代数同构，经 `AlgEquiv.ofRingEquiv`）以从该形态接入，
      并给 `thm_not_retract_rational_procesi`（吃 `ProcesiHypExact` ＋ 全称 `F`-线性假设）。
    * **`Hp 3 = H`**：`Hp p := Cp p × Cp p`、`Cp p := Multiplicative (ZMod p)`、
      `H := C3 × C3`、`C3 := Multiplicative (ZMod 3)`，故 `p = 3` 时定义级同体。

  **无 sorry、无自造公理**；`#print axioms` 门见 §5。
-/
import ABGV52.Flasque_ABGV52
import ABGV52.RetractCrit_ABGV52
import ABGV52.C8b_ABGV52
import ABGV52.SaltT2_ABGV52
import ABGV52.ProcHyp_ABGV52

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

-- 同 `EMQuasi_ABGV52`：`ℤ` 上 `AddCommGroup.toIntModule` 与 `Rep.hV2` 争用 `Module ℤ ↥X`；
-- 以及 `haveI`/`rcases` 风格 lint。
attribute [local instance 1500] Rep.hV2
set_option linter.style.haveILetI false
set_option linter.unusedRCasesPattern false

namespace ABGV52

/-! ## §1 度 1→2 LES 步骤（论文 4.13 证明 (c)）：真证明 -/

/-- **LES 步骤（论文 4.13 证明 (c) 的核心）**：设 `0 → M --f--> P --g--> E → 0` 是
`Rep ℤ H` 的短正合列（`f` 单射、`f`/`g` 正合、`g` 满射）、`P` 是置换格，且
`coh²(H,M)` 有 `3`-不消没元；则 `coh¹(H, E) ≠ 0`（即 `E` 在顶层群上不 coflasque）。

路线（与 `EMQuasi_ABGV52.not_isQuasiPermutation_M_H_rep` 同款机器）：
`Ext²(ℤtriv, P)` 上 `z+z+z = 0`（`perm_exp` ＋ `extTwoTriv_add_three_eq_zero`），
度 1→2 连接同态 `Ext.covariant_sequence_exact₁` 把 `Ext¹(ℤtriv, E)` 打到
`3y`（`y` = `x₂` 沿 `Ext²(ℤtriv,·) ≅ coh²` 的搬像）；若 `coh¹(H,E) = 0`
则 `Ext¹(ℤtriv,E) = 0`（`subsingleton_ext_one_triv`）⟹ `3y = 0` ⟹ `3x₂ = 0`，矛盾。 -/
theorem not_subsingleton_coh1_of_perm_superlattice
    (M P E : Rep.{0,0,0} ℤ H) (f : M ⟶ P) (g : P ⟶ E)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hP : _root_.ABGV52.IsPermutationLattice P)
    (h9 : ∃ x : coh M 2, (3 : ℤ) • x ≠ 0) :
    ¬ Subsingleton (coh E 1) := by
  intro hE
  -- 短复形 `0 → M → P → E → 0`（正合性经遗忘函子反射，同 EMQuasi §6）
  let S : CategoryTheory.ShortComplex (Rep ℤ H) :=
    CategoryTheory.ShortComplex.mk f g (by
      ext m
      show g (f m) = 0
      exact hfg.apply_apply_eq_zero m)
  have hSmap : (S.map (forget₂ (Rep ℤ H) (ModuleCat ℤ))).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨x₁, hx₁⟩ := (hfg x).mp hx
    exact ⟨x₁, hx₁⟩
  have hSex : S.Exact :=
    (S.exact_map_iff_of_faithful (forget₂ (Rep ℤ H) (ModuleCat ℤ))).mp hSmap
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' hSex ((Rep.mono_iff_injective f).mpr hf)
      ((Rep.epi_iff_surjective g).mpr hg)
  -- `P` 置换 ⟹ `Ext²(ℤtriv, P)` 的三倍消没
  have hPkill : ∀ z : Ext trivRep P 2, z + z + z = 0 :=
    extTwoTriv_add_three_eq_zero P (perm_exp P hP)
  -- `coh²(H,M)` 的 `3`-不消没元
  obtain ⟨x₂, hx₂⟩ := h9
  have hx₂' : x₂ + x₂ + x₂ ≠ 0 :=
    fun h => hx₂ ((three_smul_coh_eq_add_three M x₂).trans h)
  -- 经桥搬到 Ext² 侧
  let e := extTwoTriv_addEquiv_coh2 M
  let y : Ext trivRep M 2 := e.symm x₂
  have hey : e y = x₂ := AddEquiv.apply_symm_apply e x₂
  have hφ : (y + y + y).comp (Ext.mk₀ S.f) (add_zero 2) = 0 := by
    rw [Ext.add_comp, Ext.add_comp]
    exact hPkill (y.comp (Ext.mk₀ S.f) (add_zero 2))
  -- 度 1→2 LES：连接同态打到 `y + y + y`
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (X := trivRep) (S := S) (hS := hS)
    (x₁ := y + y + y) (hx₁ := hφ) (n₀ := 1) (hn₀ := rfl)
  -- `coh¹(H,E) = 0` ⟹ `Ext¹(ℤtriv,E) = 0` ⟹ `x₃ = 0`
  haveI : Subsingleton (Ext trivRep E 1) := subsingleton_ext_one_triv E hE
  have h3y : y + y + y = 0 := by
    have hx₃0 : x₃ = 0 := Subsingleton.elim x₃ 0
    rw [← hx₃, hx₃0]
    simp
  have : x₂ + x₂ + x₂ = 0 := by
    have h1 : e (y + y + y) = e y + e y + e y := by rw [map_add, map_add]
    rw [hey, h3y, map_zero] at h1
    exact h1.symm
  exact hx₂' this

/-! ## §2 flasque 消解的右端项不是 coflasque（论文 4.13 末段） -/

/-- **`coh¹(H, F) ≠ 0`**：flasque 消解 `R : 0 → M|_H → P → F → 0` 的右端项 `F`
在顶层群上 coh¹ 不消没（论文 4.13「`F` is not coflasque」的机器核形）。

输入 `3`-不消没元取自 `C8b.discriminant_pair_M_H_rep` 的第二支
（`¬ Coh2ExpDvd3 M_H_rep`，即判别对）。 -/
theorem not_subsingleton_coh1_flasqueTerm (R : FlasqueResolution H M_H_rep) :
    ¬ Subsingleton (coh R.F 1) :=
  not_subsingleton_coh1_of_perm_superlattice M_H_rep R.P R.F R.iota R.pi
    R.injective_iota R.exact R.surjective_pi
    ((EM.isPermutationLattice_iff R.P).mp R.perm)
    (by
      by_contra h
      exact discriminant_pair_M_H_rep.2 (fun x => by
        by_contra hx
        exact h ⟨x, hx⟩))

/-- **`ρ(M|_H)` 不可逆**（论文 4.13 倒数第二句）：flasque 消解的右端项不是置换格的
直和项。由 2.6 的顶层形（`Flasque_ABGV52.coflasque_top_of_isInvertible`）的**逆否**
得：若 `R.F` 可逆则 `coh¹(H,R.F) = 0`，与 §2 首条矛盾。 -/
theorem not_isInvertible_flasqueTerm (R : FlasqueResolution H M_H_rep) :
    ¬ IsInvertible H R.F :=
  fun hInv => not_subsingleton_coh1_flasqueTerm R (coflasque_top_of_isInvertible R.F hInv)

/-! ## §3 4.13 的代数侧：`F(M|_H)^H` 非 retract rational -/

/-- **论文 4.13 的代数侧**：设 `K` 是 `M|_H` 的不变量域 `F(M|_H)^H` 的替身（抽象类型，
`Field` ＋ `F`-代数），`R` 是 `M|_H` 的一条 flasque 消解，`hCrit` 是 4.12 的具名假设
（`RRat K ↔ R.F 可逆`），则 `K` 在 `F` 上**非** retract rational。

证明：`¬ R.F 可逆`（§2）＋ 4.12 的负方向接线（`retractCriterion_not`）。 -/
theorem not_retractRational_invariants (F : Type) [Field F]
    (K : Type) [Field K] [Algebra F K]
    (R : FlasqueResolution H M_H_rep)
    (hCrit : RetractCriterionHyp M_H_rep R K (fun _ => IsRetractRational F K)) :
    ¬ IsRetractRational F K :=
  retractCriterion_not hCrit (not_isInvertible_flasqueTerm R)

/-! ## §4 主定理 4.13（论文形状） -/

/-- **由「环同构 ＋ `F`-线性」构造 `F`-代数同构**（供 `G.ProcesiHyp` 的
`Z ≃+* F(M|_H)^H` 形态接入；`AlgEquiv.ofRingEquiv` 的一行包装）。 -/
noncomputable def algEquiv_of_ringEquiv_linear {F K L : Type} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] (e : K ≃+* L)
    (hlin : ∀ c : F, e (algebraMap F K c) = algebraMap F L c) : K ≃ₐ[F] L :=
  AlgEquiv.ofRingEquiv (f := e) hlin

/-- **`thm:not-retract-rational`（4.13）**：设 `Z` 是 `Z_H(F,9)` 的替身、`K` 是
`F(M|_H)^H` 的替身，且 `hgeo : Z ≃ₐ[F] K` 是论文 `rem:procesi-geometric` 的几何识别
（`F`-代数同构形），`R` 是 `M|_H` 的一条 flasque 消解，`hCrit` 是 4.12 的具名假设；
则 `Z` 在 `F` 上**非** retract rational。

搬运：`SaltT2.IsRetractRational.of_algEquiv`（retract rationality 沿 `≃ₐ[F]` 不变，
真证）——`hgeo.symm` 把 `Z` 侧的 retract rationality 搬到不变量域侧，与 §3 矛盾。 -/
theorem thm_not_retract_rational (F : Type) [Field F]
    (Z : Type) [Field Z] [Algebra F Z]
    (K : Type) [Field K] [Algebra F K]
    (R : FlasqueResolution H M_H_rep)
    (hCrit : RetractCriterionHyp M_H_rep R K (fun _ => IsRetractRational F K))
    (hgeo : Z ≃ₐ[F] K) :
    ¬ IsRetractRational F Z :=
  fun hZ => not_retractRational_invariants F K R hCrit
    (IsRetractRational.of_algEquiv hgeo.symm hZ)

/-- **`thm:not-retract-rational`（4.13），经既有具名假设消费**：几何识别取工程 C′
修正形（2026-10-10 第 44 改后；`ProcHyp_ABGV52.lean` 的 `ProcesiHypExact`——
旧 `G.ProcesiHyp` 的核只取 `ker φ`、已登记为假形状，见 `ProcConsume` 头注 ⑥）：
`hProcesi : Nonempty (Z ≃+* F(Mp2)^H)` 给出**环同构**支，`hlin` 断言该同构 `F`-线性
（几何识别是 `F`-代数同构），于是 `algEquiv_of_ringEquiv_linear` 给出 `≃ₐ[F]` 形态并
归约到上一条。

注（登记的接线输入）：`F(Mp2)^H`（C′ 修正形的不变量域）与本件 LES 侧所用
`M_H_rep = ker π`（秩 73）之间的分解关系是工程既有件 `ProcLat_ABGV52` 的内容
（`Mp2 = ker φ × ℤ[Ω]`、秩账 `finrank_Mp2`），本件不重证该分解。 -/
theorem thm_not_retract_rational_procesi (F : Type) [Field F]
    (Z : Type) [Field Z] [Algebra F Z]
    (R : FlasqueResolution H M_H_rep)
    [Algebra F ↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3))]
    (hCrit : RetractCriterionHyp M_H_rep R
      ↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3))
      (fun _ => IsRetractRational F ↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3))))
    (hProcesi : ProcHyp.ProcesiHypExact (p := 3) F Z)
    (hlin : ∀ e : Z ≃+* ↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3)),
      ∀ c : F, e (algebraMap F Z c)
        = algebraMap F ↥(EM.latticeInvariants F (P.Hp 3) (ProcLat.Mp2 3)) c) :
    ¬ IsRetractRational F Z :=
  thm_not_retract_rational F Z _ R hCrit
    (algEquiv_of_ringEquiv_linear (Classical.choice hProcesi) (hlin _))

/-- **非空洞探针（L1）**：4.13 的假设类非空——取 `R` 为任一 flasque 消解、
`hCrit` 取 `RetractCrit_ABGV52.retractCriterionHyp_satisfiable` 的实例
（`RRat := fun _ => IsInvertible H R.F`），则 §3 给出该实例下的否定结论
（接线对真实数据可点火，不是空转）。 -/
theorem not_retractRational_probe (F : Type) [Field F]
    (K : Type) [Field K] [Algebra F K]
    (R : FlasqueResolution H M_H_rep) :
    ¬ (fun _ => IsInvertible H R.F) K :=
  retractCriterion_not (retractCriterionHyp_satisfiable M_H_rep R K)
    (not_isInvertible_flasqueTerm R)

/-! ## §5 公理闸门 -/

#print axioms not_subsingleton_coh1_of_perm_superlattice
#print axioms not_subsingleton_coh1_flasqueTerm
#print axioms not_isInvertible_flasqueTerm
#print axioms not_retractRational_invariants
#print axioms algEquiv_of_ringEquiv_linear
#print axioms thm_not_retract_rational
#print axioms thm_not_retract_rational_procesi
#print axioms not_retractRational_probe

end ABGV52
