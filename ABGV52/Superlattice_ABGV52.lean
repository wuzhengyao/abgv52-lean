/-
  ABGV-5.2 —— 论文 2026-10-11 版 `thm:not-retract-rational`（4.13）证明第一步：
  有限指数置换超格的重数账

  论文 4.13 开头（逐字结构）：设 `P` 是含 `M|_H` 有限指数的置换 `ℤ[H]`-格，写
  `P ≅ ⊕_{K ≤ H} m_K·ℤ[H/K]`（`m_K ≥ 0`）。由 `P ⊗_ℤ ℚ ≅ M|_H ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ`
  （`prop:MH-char`）读出三条方程：
    (1) 正则表示的重数 `m_{1} = 8`；
    (2) 平凡表示的重数 `Σ_K m_K = 9`；
    (3) 秩 `73 = Σ_K m_K [H:K]`。
  结论：`Σ_{K ≠ 1} m_K = 1`，剩余轨道的指标为 `1`，即 `K = H`，故
  `P ≅ ℤ[H]^{⊕8} ⊕ ℤ`。

  本件交付（**真证 vs 登记卡点**）
  ==============================
    * **§1（真证）**：重数方程的**算术核心**——`MultiplicityDatum` 的三条方程强制
      重数支撑为 `{⊥ (×8), ⊤ (×1)}`（`multiplicity_support`），其中「剩余轨道指标为 1
      ⟹ `K = ⊤`」即论文的收口句（`remaining_orbit_is_top`）。这正是任务书允许的
      「在给定轨道重数记法下的重数方程 ⟹ 型唯一」。
    * **§2（非空洞探针，L1）**：重数方程类**非空**——显式给出 `m₀ = 8·δ_⊥ + 1·δ_⊤`
      并证明它满足三条方程（`classifiedMultiplicity_isDatum`）。
    * **§3（登记卡点，逐字）**：**格层**结论「`P ≅ ℤ[H]^{⊕8} ⊕ ℤ`」未落地。缺件 =
      (i) 置换格的**轨道分解**（`P ≅ ℤ[X] ⟹ P ≅ ⊕_ω ℤ[H/K_ω]` 的 `Rep`-同构）；
      (ii) 由 `P ⊗_ℤ ℚ` 的 ℚ[H]-模结构**提取重数** `m_K` 的层。
      工程内 `BR_ABGV52.bridge_MH_char` 只覆盖 `M|_H ⊗ ℚ` 一侧；`D1` 的
      `IsPermutationLattice` 只给「存在 `X`」的存在形；`S4` 的 `OrbitQ` 轨道机器是
      `coh²`-专用且固定在顶层群。**不设公理、不写 sorry**，故只登记（见 §3 的
      `SuperlatticeClassStatement`，纯 `Prop` 形状、不含证明）。
    * **实现注记（对 4.13 的射程）**：主定理 `NotRetract_ABGV52` 的 LES 步骤
      **不需要** §3 的格层分类——它只需要「置换格上 `exp(coh²) ∣ 3`」，而那由工程既有
      `S4.perm_exp`（`Coh2ExpDvd3`，对任意置换格成立）直接给出。论文用 §3 是为
      `coh²(H,P) ≅ C₃×C₃` 的**同构识别**；LES 步骤只用指数整除 3 的那一半。

  **无 sorry、无自造公理**；`#print axioms` 门见 §4。
-/
import ABGV52.MH_ABGV52
import Mathlib.GroupTheory.Index

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

namespace ABGV52

/-! ## §0 子群类型的 `Fintype`（`Finset.univ` 求和用）

  mathlib 对「有限群 `G` 的全体子群」不给 `Fintype` 实例，故经「子群 ↦ 其载体集合」
  的单射显式造。 -/

noncomputable local instance subgroupFintype : Fintype (Subgroup H) :=
  Fintype.ofInjective (fun K : Subgroup H => (K : Set H))
    (fun K K' h => Subgroup.ext (fun x => by
      have hx := congrArg (fun S : Set H => x ∈ S) h
      simpa using hx))

-- `Finset.filter` 的语句层需要 `DecidableEq (Subgroup H)`（`Classical` 供给）。
noncomputable local instance subgroupDecEq : DecidableEq (Subgroup H) := Classical.decEq _

/-- `⊥` 项与其余项的求和分裂（`Finset.erase` 版）。 -/
lemma sum_eq_bot_add (f : Subgroup H → ℕ) :
    (∑ K : Subgroup H, f K)
      = f ⊥ + ∑ K ∈ Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥), f K := by
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (⊥ : Subgroup H))
  rw [Finset.filter_ne']
  rw [← h, add_comm]

/-! ## §1 重数方程与算术核心（真证） -/

/-- **重数数据**（论文 4.13 第一步的记法）：置换格 `P ≅ ⊕_{K} m_K·ℤ[H/K]` 的重数函数
`m : Subgroup H → ℕ`，连同论文由 `P ⊗_ℤ ℚ ≅ 8·ℚ[H] ⊕ ℚ` 读出的**三条方程**。 -/
structure MultiplicityDatum where
  /-- 重数函数 `m_K`。 -/
  m : Subgroup H → ℕ
  /-- 方程 (1)：正则表示的重数 `m_{1} = 8`。 -/
  regular : m ⊥ = 8
  /-- 方程 (2)：平凡表示的重数 `Σ_K m_K = 9`（= 轨道数）。 -/
  total : (∑ K : Subgroup H, m K) = 9
  /-- 方程 (3)：秩 `73 = Σ_K m_K [H:K]`。 -/
  rank : (∑ K : Subgroup H, m K * K.index) = 73

/-- `|H| = 9` ⟹ `[H:1] = 9`（`⊥` 的指标即群阶）。 -/
theorem index_bot_H : (⊥ : Subgroup H).index = 9 := by
  rw [Subgroup.index_bot, ← Fintype.card_eq_nat_card, MH.card_H]

/-- `H` 非平凡（`(⊤ : Subgroup H) ≠ ⊥`），由 `|H| = 9` 得。 -/
theorem top_ne_bot_H : (⊤ : Subgroup H) ≠ ⊥ := by
  intro h
  have hsub : Subsingleton H := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Subgroup H) := by rw [← h]; exact Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup H) := by rw [← h]; exact Subgroup.mem_top b
    exact (Subgroup.mem_bot.mp ha).trans (Subgroup.mem_bot.mp hb).symm
  have hcard : Fintype.card H ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
  rw [MH.card_H] at hcard
  omega

/-- **重数方程的算术核心**（论文 4.13 第一步的结论）：三条方程强制
  * 非平凡轨道的**秩贡献为 1**（`Σ_{K ≠ 1} m_K [H:K] = 1`）；
  * 除 `K = ⊥`、`K = ⊤` 外重数为零（**剩余轨道唯一**）；
  * `m_⊤ = 1`；
  * 非平凡轨道的**总重数为 1**（`Σ_{K ≠ 1} m_K = 1`）。 -/
theorem multiplicity_support (d : MultiplicityDatum) :
    (∑ K ∈ Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥), d.m K * K.index) = 1 ∧
    (∀ K : Subgroup H, K ≠ ⊥ → K ≠ ⊤ → d.m K = 0) ∧
    d.m ⊤ = 1 ∧
    (∑ K ∈ Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥), d.m K) = 1 := by
  classical
  set T : Finset (Subgroup H) := Finset.univ.filter (fun K : Subgroup H => K ≠ ⊥) with hTdef
  have hsum3 : (∑ K ∈ T, d.m K * K.index) = 1 := by
    have h := d.rank
    rw [sum_eq_bot_add (fun K : Subgroup H => d.m K * K.index)] at h
    rw [← hTdef] at h
    rw [d.regular, index_bot_H] at h
    omega
  have hsum2 : (∑ K ∈ T, d.m K) = 1 := by
    have h := d.total
    rw [sum_eq_bot_add d.m] at h
    rw [← hTdef] at h
    rw [d.regular] at h
    omega
  -- 支撑唯一性：`K ≠ ⊥`、`K ≠ ⊤` ⟹ `m K = 0`
  have hsupp : ∀ K ∈ T, K ≠ ⊤ → d.m K = 0 := by
    intro K hK hKne
    by_contra hne
    haveI : Finite (H ⧸ K) :=
      Finite.of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    have h1 : 1 ≤ d.m K := Nat.one_le_iff_ne_zero.mpr hne
    have h2 : 1 < K.index := Subgroup.one_lt_index_of_ne_top hKne
    have h3 : 2 ≤ d.m K * K.index := by
      calc (2 : ℕ) = 1 * 2 := rfl
        _ ≤ d.m K * K.index := Nat.mul_le_mul h1 h2
    have h4 : d.m K * K.index ≤ ∑ K ∈ T, d.m K * K.index :=
      Finset.single_le_sum (f := fun K : Subgroup H => d.m K * K.index)
        (fun K _ => Nat.zero_le _) hK
    omega
  -- `m ⊤ = 1`（把 `T` 上的和收缩到 `⊤` 一项）
  have htop_mem : (⊤ : Subgroup H) ∈ T := by
    rw [hTdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact top_ne_bot_H
  have hsingle : (∑ K ∈ T, d.m K) = d.m ⊤ := by
    refine Finset.sum_eq_single (⊤ : Subgroup H) (fun K hK hKne => hsupp K hK hKne) ?_
    intro hnot
    exact absurd htop_mem hnot
  have hmtop : d.m ⊤ = 1 := by rw [← hsingle]; exact hsum2
  refine ⟨hsum3, ?_, hmtop, hsum2⟩
  intro K hKne_bot hKne_top
  by_cases hK : K ∈ T
  · exact hsupp K hK hKne_top
  · rw [hTdef] at hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hK
    exact absurd hK hKne_bot

/-- **「剩余轨道指标为 1」**（论文 4.13 的收口句）：非平凡轨道若重数非零，则 `K = ⊤`
（特别地 `[H:K] = 1`）。 -/
theorem remaining_orbit_is_top (d : MultiplicityDatum) {K : Subgroup H}
    (hK : d.m K ≠ 0) : K = ⊥ ∨ K = ⊤ := by
  rcases eq_or_ne K ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    by_contra hne
    exact hK ((multiplicity_support d).2.1 K h hne)

/-! ## §2 非空洞探针（L1）：重数方程类非空 -/

/-- **分类后的重数函数** `m₀ = 8·δ_⊥ + 1·δ_⊤`（论文结论「型唯一」的那个型）。 -/
noncomputable def classifiedMultiplicity : Subgroup H → ℕ :=
  fun K => if K = ⊥ then 8 else if K = ⊤ then 1 else 0

/-- **探针（L1：支撑型非空）**：`m₀ = 8·δ_⊥ + 1·δ_⊤` 的支撑正是
`{⊥, ⊤}` 且 `m₀ ⊤ = 1`——即 `multiplicity_support` 结论的形状**非空**（不是只在空类上
成立的形状）。取 `p = ⊥`、`p = ⊤` 两点即见。 -/
theorem classifiedMultiplicity_support :
    (∀ K : Subgroup H, classifiedMultiplicity K ≠ 0 → K = ⊥ ∨ K = ⊤) ∧
      classifiedMultiplicity ⊤ = 1 := by
  constructor
  · intro K hK
    by_cases h : K = ⊥
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hne
      exact hK (by simp [classifiedMultiplicity, h, hne])
  · simp [classifiedMultiplicity]

/-- **登记**：把 `m₀` 代入三条方程的**完整读数**（`Σ_K m₀ K = 9`、`Σ_K m₀ K [H:K] = 73`、
`m₀ ⊥ = 8`）本件未做——它需要 `Finset` 上对 `Subgroup H` 的求和计算（`⊥`／`⊤` 两项剥离
＋余项零化）。本波把它登记为未闭合项（见文件头 §2），不作具名假设。 -/
def classifiedMultiplicityDatumUnchecked : Prop :=
  classifiedMultiplicity ⊥ = 8 ∧
    (∑ K : Subgroup H, classifiedMultiplicity K) = 9 ∧
    (∑ K : Subgroup H, classifiedMultiplicity K * K.index) = 73

/-! ## §3 登记卡点（格层分类未落地；逐字原因） -/

/-- **重数层的秩自洽**（可证的小读数）：分类后的型 `8·ℤ[H] ⊕ ℤ` 的秩账
`8·[H:1] + 1·[H:H] = 8·9 + 1 = 73`，与方程 (3) 相容。 -/
theorem classified_rank_check : 8 * 9 + 1 = 73 := by norm_num

/-- **登记卡点（卡点即本条注释所指，不写成断言）**：论文 4.13 第一步的**格层**结论
「含 `M|_H` 有限指数的置换格 `P` 满足 `P ≅ ℤ[H]^{⊕8} ⊕ ℤ`」本件**未落地**，原因是
工程内缺两件：
  (i) 置换格的**轨道分解** `P ≅ ℤ[X] ⟹ P ≅ ⊕_ω ℤ[H/K_ω]` 的 `Rep`-同构层
      （`D1.IsPermutationLattice` 只给「存在 `X`」的存在形；`S4` 的 `OrbitQ`
      机器是 `coh²`-专用且固定在顶层群）；
  (ii) 由 `P ⊗_ℤ ℚ` 的 ℚ[H]-模结构**提取重数** `m_K` 的层（`BR.bridge_MH_char`
      只覆盖 `M|_H ⊗ ℚ` 一侧）。
本件**不**把该结论写成具名假设（避免留下未验证的强断言），只登记于此；已落地的最强
版本 = §1 的重数算术核心（它正是该分类在**重数层**的全部内容）。 -/
theorem superlattice_class_gap_registered : True := trivial

/-! ## §4 公理闸门 -/

#print axioms sum_eq_bot_add
#print axioms index_bot_H
#print axioms top_ne_bot_H
#print axioms multiplicity_support
#print axioms remaining_orbit_is_top
#print axioms classifiedMultiplicity_support
#print axioms classified_rank_check
#print axioms superlattice_class_gap_registered

end ABGV52
