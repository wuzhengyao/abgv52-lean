/-
  ABGV-5.2 —— `thm:not-retract-rational`（4.13）第一步的**格层分类**：接口化收口（第 3 轮）

  目标（逐字）：`P` 为置换 `ℤ[H]`-格、`P ⊇ M|_H` 有限指数 ⟹ `P ≅ ℤ[H]^{⊕8} ⊕ ℤ`。

  第 1 轮（`Superlattice_ABGV52.lean`）已证**重数算术**：`MultiplicityDatum` 的三条方程
  `m_⊥ = 8`／`Σ_K m_K = 9`／`Σ_K m_K [H:K] = 73` 强制支撑为 `8·δ_⊥ + δ_⊤`
  （`multiplicity_support`）。本件把该算术**接到格层**：

    * §1 **重数索引的轨道和 H-集** `orbitSumSet m = Σ_{K : m K ≠ 0} Fin (m K) × (H ⧸ K)`
      ——「重数函数 `m` 的置换格」的底层 H-集（`orbitSumRep m := ℤ[orbitSumSet m]`）；
    * §2 **接口（具名）** `HasOrbitMultiplicities P m`：`P ≅ ℤ[orbitSumSet m]`
      —— 这是缺口 2 的 (i)（轨道分解为陪集模的直和）＋ (ii)（由 `P ⊗ ℚ` 读出 `m`）的
      **合并登记点**；配类型锁 ＋ 自反非空洞探针（`orbitSumRep m` 自身满足之）；
    * §3 **接线（真证）**：`MultiplicityDatum` ⟹ `m = classifiedMultiplicity`（函数等式）
      ⟹ 接口把 `P` 的轨道型**完全钉死**为 `8·δ_⊥ + δ_⊤`（`classified_of_orbitMultiplicities`）；
    * §4 **接口 ⟹ 置换格**（真证）：`HasOrbitMultiplicities P m ⟹ IsPermutationLattice P`；
    * §5 **闭合第 1 轮的未闭合项**：`classifiedMultiplicity` 满足三条方程
      （`classifiedMultiplicityDatum`），即第 1 轮登记的 `classifiedMultiplicityDatumUnchecked`
      现为**已证**；并给出整个链的**非空洞探针**（L1）；
    * §6 **逐字登记剩余卡点**：(i) 的**集合层纤维分解**（把 `Σ_{K} m_K·ℤ[H/K]` 写成
      忠实于论文的 `ℤ[H]^{⊕8} ⊕ ℤ` 双积形）与 (ii) 的 ℚ-侧重数提取。

  说明（对主定理的射程）：4.13 的 LES 步骤**不需要**本分类（`exp(coh²) ∣ 3` 由既有
  `S4.perm_exp` 直接给出），故本件是**收口登记**而非主定理的必需件。

  **无 sorry、无自造公理**；`#print axioms` 门见 §7。
-/
import ABGV52.Superlattice_ABGV52
import ABGV52.D1_ABGV52

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

namespace ABGV52

/-! ## §0 三个局部实例（`Superlattice_ABGV52` 的 `local instance` 不导出，此处重声明） -/

noncomputable local instance subgroupFintype3 : Fintype (Subgroup H) :=
  Fintype.ofInjective (fun K : Subgroup H => (K : Set H))
    (fun K K' h => Subgroup.ext (fun x => by
      have hx := congrArg (fun S : Set H => x ∈ S) h
      simpa using hx))

noncomputable local instance subgroupDecEq3 : DecidableEq (Subgroup H) := Classical.decEq _

/-- 陪集空间的 `Fintype`（`Quotient.finite` ＋ `H` 有限）。 -/
noncomputable local instance fintypeQuotH3 (K : Subgroup H) : Fintype (H ⧸ K) :=
  Fintype.ofFinite _

/-! ## §1 重数索引的轨道和 H-集 -/

/-- **重数函数 `m` 的轨道和 H-集**：`Σ_{K : m K ≠ 0} Fin (m K) × (H ⧸ K)`。
即「`m_K` 份陪集模 `ℤ[H/K]`」的置换格的底层 H-集（`Fin` 方向平凡作用、
陪集方向左乘作用）。 -/
def orbitSumSet (m : Subgroup H → ℕ) : Type :=
  Σ K : {K : Subgroup H // m K ≠ 0}, Fin (m K.1) × (H ⧸ K.1)

noncomputable instance orbitSumSetFintype (m : Subgroup H → ℕ) : Fintype (orbitSumSet m) := by
  classical
  unfold orbitSumSet
  infer_instance

instance orbitSumSetMulAction (m : Subgroup H → ℕ) : MulAction H (orbitSumSet m) where
  smul g x := ⟨x.1, x.2.1, g • x.2.2⟩
  one_smul x := by
    obtain ⟨K, i, q⟩ := x
    show (⟨K, i, (1 : H) • q⟩ : orbitSumSet m) = ⟨K, i, q⟩
    rw [one_smul]
  mul_smul g h x := by
    obtain ⟨K, i, q⟩ := x
    show (⟨K, i, (g * h) • q⟩ : orbitSumSet m) = ⟨K, i, g • (h • q)⟩
    rw [mul_smul]

/-- **重数函数 `m` 的置换格** `ℤ[orbitSumSet m]`（即「`⊕_K m_K·ℤ[H/K]`」的具体模型）。 -/
noncomputable def orbitSumRep (m : Subgroup H → ℕ) : Rep.{0,0,0} ℤ H :=
  Rep.ofMulAction ℤ H (orbitSumSet m)

/-! ## §2 接口（具名）：轨道重数数据

**(i)＋(ii) 的合并登记点**：`P` 的轨道分解为陪集模的直和、且重数函数为 `m`。
（(ii) 的「由 `P ⊗_ℤ ℚ` 读出 `m`」正是给出此接口的那个映射；本件不构造它。） -/

/-- **接口**：`P` 的轨道型恰为「`m_K` 份 `ℤ[H/K]`」。 -/
def HasOrbitMultiplicities (P : Rep.{0,0,0} ℤ H) (m : Subgroup H → ℕ) : Prop :=
  Nonempty (P ≅ orbitSumRep m)

/-- **类型锁定断言**（`HasOrbitMultiplicities`）。 -/
example (P : Rep.{0,0,0} ℤ H) (m : Subgroup H → ℕ) :
    HasOrbitMultiplicities P m ↔ Nonempty (P ≅ orbitSumRep m) :=
  Iff.rfl

/-- **非空洞探针（L1）**：接口类非空——`orbitSumRep m` 自身以恒等同构满足之。 -/
theorem hasOrbitMultiplicities_self (m : Subgroup H → ℕ) :
    HasOrbitMultiplicities (orbitSumRep m) m :=
  ⟨Iso.refl _⟩

/-! ## §3 接线：重数数据 ⟹ 轨道型被完全钉死 -/

/-- **重数数据的函数形态**（真证）：三条方程 ⟹ `m = 8·δ_⊥ + δ_⊤`。

（`MultiplicityDatum` 的三条方程已经把 `m` 在 `⊥`、`⊤` 处的值定死，且在其余处为零
——见 `multiplicity_support`。） -/
theorem eq_classifiedMultiplicity (d : MultiplicityDatum) :
    d.m = classifiedMultiplicity := by
  funext K
  rcases (multiplicity_support d) with ⟨_, hsupp, htop, _⟩
  by_cases hbot : K = ⊥
  · rw [hbot, d.regular]
    simp [classifiedMultiplicity]
  · by_cases htop' : K = ⊤
    · rw [htop', htop]
      simp [classifiedMultiplicity, hbot]
    · rw [hsupp K hbot htop']
      simp [classifiedMultiplicity, hbot, htop']

/-- **格层分类（接口形，真证）**：若 `P` 的重数数据为 `d.m`（`d : MultiplicityDatum`），
则 `P` 的轨道型**就是**分类后的型 `8·δ_⊥ + δ_⊤`——即
`P ≅ ℤ[Σ_{K ∈ {⊥,⊤}} m_K 份 H/K]`，论文的 `P ≅ ℤ[H]^{⊕8} ⊕ ℤ` 的轨道型内容。 -/
theorem classified_of_orbitMultiplicities (d : MultiplicityDatum)
    {P : Rep.{0,0,0} ℤ H} (h : HasOrbitMultiplicities P d.m) :
    HasOrbitMultiplicities P classifiedMultiplicity := by
  rw [eq_classifiedMultiplicity d] at h
  exact h

/-- 同上，写成「与分类后的置换格同构」的显式形状。 -/
theorem iso_orbitSumRep_classified (d : MultiplicityDatum) {P : Rep.{0,0,0} ℤ H}
    (h : HasOrbitMultiplicities P d.m) : Nonempty (P ≅ orbitSumRep classifiedMultiplicity) :=
  classified_of_orbitMultiplicities d h

/-! ## §4 接口 ⟹ 置换格 -/

/-- **接口蕴含置换性**（真证）：轨道分解的存在形即 `IsPermutationLattice`（一般群版）。 -/
theorem isPermutationLattice_of_hasOrbitMultiplicities {P : Rep.{0,0,0} ℤ H}
    {m : Subgroup H → ℕ} (h : HasOrbitMultiplicities P m) :
    EM.IsPermutationLattice H P := by
  obtain ⟨e⟩ := h
  exact ⟨orbitSumSet m, orbitSumSetFintype m, orbitSumSetMulAction m, ⟨e⟩⟩

/-- 同上，`H`-专用谓词形（与论文其余部分的记号一致）。 -/
theorem root_isPermutationLattice_of_hasOrbitMultiplicities {P : Rep.{0,0,0} ℤ H}
    {m : Subgroup H → ℕ} (h : HasOrbitMultiplicities P m) :
    _root_.ABGV52.IsPermutationLattice P :=
  isPermutationLattice_of_hasOrbitMultiplicities h

/-! ## §5 探针：分类后的重数函数满足三条方程（闭合第 1 轮的未闭合项）

第 1 轮把 `Σ_K m₀ K = 9`／`Σ_K m₀ K [H:K] = 73`／`m₀ ⊥ = 8` 的**完整读数**登记为未闭合项
（`classifiedMultiplicityDatumUnchecked`）。此处把它**证完**：`m₀ = 8·δ_⊥ + δ_⊤`
在 `⊥`、`⊤` 两点取值、其余项求和为零。 -/

theorem classifiedMultiplicity_bot : classifiedMultiplicity (⊥ : Subgroup H) = 8 := by
  simp [classifiedMultiplicity]

theorem classifiedMultiplicity_top : classifiedMultiplicity (⊤ : Subgroup H) = 1 := by
  simp [classifiedMultiplicity, top_ne_bot_H]

/-- `Σ_K m₀ K = 8 + 1 = 9`（把和式剥离为 `⊥` 项与其余项，其余项只剩 `⊤`）。 -/
theorem classifiedMultiplicity_total :
    (∑ K : Subgroup H, classifiedMultiplicity K) = 9 := by
  classical
  rw [sum_eq_bot_add classifiedMultiplicity, classifiedMultiplicity_bot]
  have hrest : (∑ K ∈ Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥),
      classifiedMultiplicity K) = 1 := by
    have h := Finset.sum_eq_single
      (s := Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥))
      (f := fun K : Subgroup H => classifiedMultiplicity K) (⊤ : Subgroup H)
      (fun K hK hKne => by
        have hKbot : K ≠ ⊥ := (Finset.mem_filter.mp hK).2
        simp [classifiedMultiplicity, hKbot, hKne])
      (fun hnot =>
        absurd (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, top_ne_bot_H⟩) hnot)
    rw [h]
    exact classifiedMultiplicity_top
  rw [hrest]

/-- `Σ_K m₀ K · [H:K] = 8·9 + 1·1 = 73`。 -/
theorem classifiedMultiplicity_rank :
    (∑ K : Subgroup H, classifiedMultiplicity K * K.index) = 73 := by
  classical
  rw [sum_eq_bot_add (fun K : Subgroup H => classifiedMultiplicity K * K.index),
    classifiedMultiplicity_bot, index_bot_H]
  have hrest : (∑ K ∈ Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥),
      classifiedMultiplicity K * K.index) = 1 := by
    have h := Finset.sum_eq_single
      (s := Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥))
      (f := fun K : Subgroup H => classifiedMultiplicity K * K.index) (⊤ : Subgroup H)
      (fun K hK hKne => by
        have hKbot : K ≠ ⊥ := (Finset.mem_filter.mp hK).2
        simp [classifiedMultiplicity, hKbot, hKne])
      (fun hnot =>
        absurd (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, top_ne_bot_H⟩) hnot)
    rw [h, classifiedMultiplicity_top, Subgroup.index_top]
  rw [hrest]

/-- **第 1 轮的未闭合项现已证**：`classifiedMultiplicityDatumUnchecked` 的三条读数。 -/
theorem classifiedMultiplicityDatumUnchecked_proved :
    classifiedMultiplicity (⊥ : Subgroup H) = 8 ∧
      (∑ K : Subgroup H, classifiedMultiplicity K) = 9 ∧
      (∑ K : Subgroup H, classifiedMultiplicity K * K.index) = 73 :=
  ⟨classifiedMultiplicity_bot, classifiedMultiplicity_total, classifiedMultiplicity_rank⟩

/-- **分类后的重数是合法的重数数据**（把三条读数打包成 `MultiplicityDatum`）。 -/
noncomputable def classifiedMultiplicityDatum : MultiplicityDatum where
  m := classifiedMultiplicity
  regular := classifiedMultiplicity_bot
  total := classifiedMultiplicity_total
  rank := classifiedMultiplicity_rank

/-- **探针（L1：整条链非空洞）**：分类后的型既是合法的重数数据，又确实实现接口
（取 `P := orbitSumRep classifiedMultiplicity` 即得），并且由 §3 它还是**唯一**可能的型
（任何满足重数数据的 `P` 都同构于它）。 -/
theorem classification_chain_nonvacuous :
    classifiedMultiplicityDatum.m = classifiedMultiplicity ∧
      HasOrbitMultiplicities (orbitSumRep classifiedMultiplicity) classifiedMultiplicity ∧
      (∀ (P : Rep.{0,0,0} ℤ H),
        HasOrbitMultiplicities P classifiedMultiplicityDatum.m →
          Nonempty (P ≅ orbitSumRep classifiedMultiplicity)) :=
  ⟨rfl, hasOrbitMultiplicities_self classifiedMultiplicity,
    fun P h => iso_orbitSumRep_classified classifiedMultiplicityDatum h⟩

/-! ## §6 登记：剩余卡点（逐字）

  本件把分类的**重数层**与**接口层**全部落地；仍未闭合的是两件，均为「把已证内容改写为
  论文的逐字形状」所需的**集合层**工作：

  (i) **纤维分解**（把 `orbitSumSet m` 写成论文的双积形 `ℤ[H]^{⊕8} ⊕ ℤ` 的底层 H-集）：
      需要 H-集等价 `Σ_{K : m K ≠ 0} Fin (m K) × (H ⧸ K) ≃ Fin 8 × (H ⧸ ⊥) ⊔ Fin 1 × (H ⧸ ⊤)`
      （在 `m = 8·δ_⊥ + δ_⊤` 下）。mathlib 的可用件已核实：
      `Equiv.sigmaFiberEquiv`（纤维分解）、`Fintype.equivFin`（纤维基数）、
      `Equiv.sigmaCongrLeft`／`Equiv.sigmaSumDistrib` 型重指标；
      未做的是沿 `orbStab` 的**依赖型搬运**（`Fin (m K) ≃ {ω // Stab ω = K}` 与
      `H ⧸ K` 的换元）。
  (ii) **ℚ-侧重数提取**：由 `P ⊗_ℤ ℚ` 的 `ℚ[H]`-模结构读出 `m_K`（等价地，构造本件 §2
      接口的实例）。工程内 `BR_ABGV52.bridge_MH_char` 只覆盖 `M|_H ⊗ ℚ` 一侧；
      `ℚ[H/K]` 在 `ℚ[H]` 上的分解在工程内与 mathlib 中均无。

  另：论文结论里 `ℤ[H]^{⊕8}` 的**有限双积**写法（`⊞_{Fin 8} ℤ[H]`）亦未做——本件把
  「8 份正则格」写成置换格 `ℤ[Fin 8 × H]`（与 `⊕_{Fin 8} ℤ[H]` 同构，后者需有限双积 API）。
-/

/-- **登记卡点**（与 `Superlattice_ABGV52.superlattice_class_gap_registered` 同款：
只登记，不写成断言）。 -/
theorem orbit_fiber_decomposition_gap_registered : True := trivial

/-! ## §7 公理闸门 -/

#print axioms hasOrbitMultiplicities_self
#print axioms eq_classifiedMultiplicity
#print axioms classified_of_orbitMultiplicities
#print axioms isPermutationLattice_of_hasOrbitMultiplicities
#print axioms classifiedMultiplicity_total
#print axioms classifiedMultiplicity_rank
#print axioms classifiedMultiplicityDatumUnchecked_proved
#print axioms classification_chain_nonvacuous
#print axioms orbit_fiber_decomposition_gap_registered

end ABGV52
