/-
  ABGV-5.2 —— **本体形式化 B · T3：Swan 引理（Saltman 1984, Lemma 3.3）**

  蓝图（`wiki/proj-ABGV52-formalize-saltman.md` §3.3 T3）：`SaltSwan_ABGV52.lean`
  —— lem3.3 移植（M2 Swan 层的第一块：lem3.3 → cor3.4 → lem3.5）。

  源（逐字，`raw/Saltman1984.tex:412–422`，label `lem3.3`，印刷页 181，
  PDF 页 17，偏移 PDF+164）：
  "Let \(F\subseteq K\) be fields, and let \(S_1,S_2\subset K\) be affine \(F\)
  subalgebras such that \(q(S_1) = K\). Then there are \(0\neq s_1\in S_1\) and
  \(0\neq s_2\in S_2\) such that \(S_1(1/s_1) = S_2(1/s_2)\)."
  证明（源文，三步）：(i) S₁ 有限生成 ⟹ ∃ 0≠s₂′∈S₂，S₁ ⊆ S₂(1/s₂′)；
  (ii) S₂(1/s₂′) 有限生成 ⟹ ∃ s₁∈S₁，S₂(1/s₂′) ⊆ S₁(1/s₁)；
  再由 s₁ = t/(s₂′)ⁿ（t∈S₂）组装，取 s₂ = s₂′t 得两向包含。

  形式化约定（与源陈述的偏差，逐条登记）
  =====================================
  * "affine" → `Algebra.FiniteType F S`（mathlib 无 "affine algebra" 一词）。
  * "q(S)=K" → `IsFractionRing S K`。**偏差（加性收紧）**：源仅设 q(S₁)=K；
    但其证明步骤 (i)（S₁ ⊆ S₂(1/s₂′)）需要 S₁ 的生成元都是 S₂ 的分式，即需要
    q(S₂)=K。形式化对 S₁、S₂ **皆设** `IsFractionRing`。若仅设 q(S₁)=K 而不
    约束 q(S₂)，陈述为假：K = F(x,y)、S₁ = F[x,y]、S₂ = F[y] 时 x ∈ S₁(1/s₁)
    而 S₂(1/s₂) ⊆ F(y)。故按证明实际所需假设录入（收紧，非放宽）。
  * "S(1/s)" → `Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})`——源中 S(1/s)
    指 K 内由 S 与 1/s 生成的 F-子代数，即子代数范畴的局部化读法。
  * 源用 "S₁,S₂ ⊂ K" 的**子集**写法；形式化为 `S₁ S₂ : Subalgebra F K`。
  * `Algebra.adjoin`（本 mathlib 无 `Subalgebra.adjoin`）。
  * 源文步骤 (ii) 有一处排版错误（"⊆ S₂(1/s₁)" 应为 "⊆ S₁(1/s₁)"）；
    形式化按正确读法（`hT₂'T₁` 的方向）展开，两向包含在证明中闭合。

  证明结构（三条引理 + 组装）
  ==========================
  1. `exists_finset_adjoin_eq`：有限型 ⟹ 生成元表（Finset K）；
     `adjoin_image` + `map_top` + `range_val` 搬运。
  2. `exists_localization_ge_adjoin`（单边引理，源步 (i)/(ii) 的公共核）：
     X 有限 ⟹ ∃ 0≠s∈S，adjoin F X ≤ adjoin F (S ∪ {s⁻¹})；对 X 归纳，
     每步用 `IsFractionRing.div_surjective` 提取分母、增量并入单元素。
  3. `fraction_extraction`：x ∈ adjoin F (S ∪ {s⁻¹}) ⟹ ∃ n t∈S，x·sⁿ = t；
     对 adjoin 归纳（mem/algebraMap/add/mul），逐层清分母。
  4. `swan_localization_common` = 源步 (i) + 步 (ii) + 抽取（s₁(s₂′)ⁿ = t）
     + 四个域恒等式 + 两向包含，取 s₂ := s₂′·t。

  **无 sorry、无自造公理**。
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower

universe u

namespace ABGV52

/-! ## 1. 生成元搬运：有限型子代数由有限个 K 的元素生成 -/

/-- **生成元搬运**：`S : Subalgebra F K` 在 `F` 上有限型 ⟹ 存在 `Finset K`
（子代数元素的提升）使 `Algebra.adjoin F t = S`。 -/
theorem exists_finset_adjoin_eq {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S : Subalgebra F K) [Algebra.FiniteType F S] :
    ∃ t : Finset K, Algebra.adjoin F (t : Set K) = S := by
  classical
  obtain ⟨t, ht⟩ := (inferInstance : Algebra.FiniteType F S).out
  refine ⟨t.image (fun a : S => (a : K)), ?_⟩
  rw [Finset.coe_image]
  have hmap : Algebra.adjoin F ((fun a : S => (a : K)) '' (↑t : Set S))
      = (Algebra.adjoin F (↑t : Set S)).map (Subalgebra.val S) :=
    Algebra.adjoin_image F (Subalgebra.val S) (↑t : Set S)
  rw [hmap, ht, Algebra.map_top]
  exact Subalgebra.range_val S

/-! ## 2. 单边局部化引理（源步 (i)/(ii) 的公共核） -/

/-- **单边局部化引理**：`S` 是 `K` 的分式域，`X : Finset K` 有限，则存在
`0 ≠ s ∈ S` 使 `Algebra.adjoin F X ≤ Algebra.adjoin F (S ∪ {s⁻¹})`。

对 `X` 归纳：每个新元素 `x` 经 `IsFractionRing.div_surjective` 写成 `p/q`
（`p q ∈ S`），分母 `q` 并入 `s`（新分母 `s₀ q`）；`1/q` 与 `1/s₀` 均用
`(s₀ q)⁻¹` 表出（两条域恒等式）。 -/
theorem exists_localization_ge_adjoin {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S : Subalgebra F K) (hS : IsFractionRing S K) (X : Finset K) :
    ∃ s : S, s ≠ 0 ∧ Algebra.adjoin F (X : Set K) ≤
      Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹}) := by
  classical
  induction X using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      rw [Finset.coe_empty, Algebra.adjoin_empty]
      exact bot_le
  | insert x X _ ih =>
      obtain ⟨s₀, hs₀, hle₀⟩ := ih
      obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective S x
      have hpq' : (p : K) / (q : K) = x := hpq
      have hqS : q ≠ 0 := fun h => one_ne_zero (hq.1 1 (by rw [h, zero_mul]))
      have hqK : (q : K) ≠ 0 := fun h => hqS ((Subalgebra.coe_eq_zero S).mp h)
      have hs₀K : (s₀ : K) ≠ 0 := fun h => hs₀ ((Subalgebra.coe_eq_zero S).mp h)
      refine ⟨s₀ * q, mul_ne_zero hs₀ hqS, ?_⟩
      have hden : ((q : K))⁻¹ = (s₀ : K) * (((s₀ * q : S) : K))⁻¹ := by
        rw [Subalgebra.coe_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs₀K, one_mul]
      have hs₀inv : (s₀ : K)⁻¹ = (q : K) * (((s₀ * q : S) : K))⁻¹ := by
        rw [Subalgebra.coe_mul, mul_inv, ← mul_assoc, mul_comm (q : K) ((s₀ : K)⁻¹),
          mul_assoc, mul_inv_cancel₀ hqK, mul_one]
      have hsub : Algebra.adjoin F ((S : Set K) ∪ {((s₀ : K))⁻¹}) ≤
          Algebra.adjoin F ((S : Set K) ∪ {(((s₀ * q : S) : K))⁻¹}) := by
        rw [Algebra.adjoin_le_iff]
        intro c hc
        rcases hc with hcS | hcs
        · exact Algebra.subset_adjoin (Set.mem_union_left _ hcS)
        · rw [Set.mem_singleton_iff.mp hcs, hs₀inv]
          exact mul_mem (Algebra.subset_adjoin (Set.mem_union_left _ q.2))
            (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _)))
      have hxT : x ∈ Algebra.adjoin F ((S : Set K) ∪ {(((s₀ * q : S) : K))⁻¹}) := by
        rw [← hpq', div_eq_mul_inv, hden]
        exact mul_mem (Algebra.subset_adjoin (Set.mem_union_left _ p.2))
          (mul_mem (Algebra.subset_adjoin (Set.mem_union_left _ s₀.2))
            (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))))
      rw [Finset.coe_insert, Algebra.adjoin_le_iff]
      intro y hy
      rcases hy with rfl | hyX
      · exact hxT
      · exact hsub (hle₀ (Algebra.subset_adjoin hyX))

/-! ## 3. 分式抽取引理（清分母） -/

/-- **分式抽取**：`x ∈ Algebra.adjoin F (S ∪ {s⁻¹})`（`0 ≠ s ∈ S`）⟹ 存在
`n : ℕ` 与 `t ∈ S` 使 `x * sⁿ = t`（在 `K` 中）。

对 `Algebra.adjoin_induction` 归纳：`mem` 层取 `n = 0`（S 的元素）或 `n = 1`
（`s⁻¹` 的情形，用 `inv_mul_cancel₀`）；`add`/`mul` 层取指数相加、
分子按 `s^n₁ + n₂ = s^n₁ · s^n₂` 通分（`pow_add`）。 -/
theorem fraction_extraction {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S : Subalgebra F K) {s : S} (hs : s ≠ 0) {x : K}
    (hx : x ∈ Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) :
    ∃ (n : ℕ) (t : S), x * (s : K) ^ n = (t : K) := by
  have hsK : (s : K) ≠ 0 := fun h => hs ((Subalgebra.coe_eq_zero S).mp h)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      rcases hy with hyS | hys
      · exact ⟨0, ⟨y, hyS⟩, by simp⟩
      · rw [Set.mem_singleton_iff.mp hys]
        exact ⟨1, 1, by rw [pow_one]; exact inv_mul_cancel₀ hsK⟩
  | algebraMap r =>
      exact ⟨0, algebraMap F S r, by
        rw [pow_zero, mul_one, IsScalarTower.algebraMap_apply F S K r,
          Subalgebra.algebraMap_apply]⟩
  | add y z _ _ hy hz =>
      obtain ⟨n₁, t₁, h₁⟩ := hy
      obtain ⟨n₂, t₂, h₂⟩ := hz
      refine ⟨n₁ + n₂, t₁ * s ^ n₂ + t₂ * s ^ n₁, ?_⟩
      have h₁' : y * (s : K) ^ (n₁ + n₂) = (t₁ : K) * (s : K) ^ n₂ := by
        rw [pow_add, ← mul_assoc]
        exact congrArg (· * (s : K) ^ n₂) h₁
      have h₂' : z * (s : K) ^ (n₁ + n₂) = (t₂ : K) * (s : K) ^ n₁ := by
        rw [pow_add, mul_comm ((s : K) ^ n₁) ((s : K) ^ n₂), ← mul_assoc]
        exact congrArg (· * (s : K) ^ n₁) h₂
      rw [add_mul, h₁', h₂']
      simp
  | mul y z _ _ hy hz =>
      obtain ⟨n₁, t₁, h₁⟩ := hy
      obtain ⟨n₂, t₂, h₂⟩ := hz
      refine ⟨n₁ + n₂, t₁ * t₂, ?_⟩
      have h₁' : (y * z) * (s : K) ^ (n₁ + n₂)
          = (y * (s : K) ^ n₁) * (z * (s : K) ^ n₂) := by
        rw [pow_add]; ring
      rw [h₁', h₁, h₂]
      simp

/-! ## 4. 主定理（Swan 引理，Saltman 1984 lem3.3） -/

/-- **Swan 引理（lem3.3）**：`F ⊆ K` 域，`S₁ S₂ ⊆ K` 为仿射 `F`-子代数
（`Algebra.FiniteType`），且二者均以 `K` 为分式域（`IsFractionRing`）。
则存在 `0 ≠ s₁ ∈ S₁` 与 `0 ≠ s₂ ∈ S₂` 使
`S₁(1/s₁) = S₂(1/s₂)`（子代数范畴的局部化：`Algebra.adjoin F (Sᵢ ∪ {sᵢ⁻¹})`）。

证明 = 单边引理两次（源步 (i)、(ii)）+ 分式抽取引理 + 取 `s₂ := s₂′ · t`。 -/
theorem swan_localization_common {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S₁ S₂ : Subalgebra F K) [Algebra.FiniteType F S₁] [Algebra.FiniteType F S₂]
    (h₁ : IsFractionRing S₁ K) (h₂ : IsFractionRing S₂ K) :
    ∃ (s₁ : S₁) (s₂ : S₂), s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      Algebra.adjoin F ((S₁ : Set K) ∪ {((s₁ : K))⁻¹})
        = Algebra.adjoin F ((S₂ : Set K) ∪ {((s₂ : K))⁻¹}) := by
  classical
  obtain ⟨t₁, ht₁⟩ := exists_finset_adjoin_eq S₁
  obtain ⟨t₂, ht₂⟩ := exists_finset_adjoin_eq S₂
  -- 步骤 (i)：S₁ 的生成元全部落入 S₂(1/s₂′)
  obtain ⟨s₂', hs₂', hle⟩ := exists_localization_ge_adjoin S₂ h₂ t₁
  have hS₁T₂' : S₁ ≤ Algebra.adjoin F ((S₂ : Set K) ∪ {((s₂' : K))⁻¹}) := by
    rw [← ht₁]; exact hle
  -- 步骤 (ii)：把 S₂(1/s₂′) 的生成元落入 S₁(1/s₁)
  obtain ⟨s₁, hs₁, hle₁⟩ :=
    exists_localization_ge_adjoin S₁ h₁ (insert ((s₂' : K))⁻¹ t₂)
  have hunion : Algebra.adjoin F ((S₂ : Set K) ∪ {((s₂' : K))⁻¹})
      = Algebra.adjoin F (((insert ((s₂' : K))⁻¹ t₂ : Finset K)) : Set K) := by
    have h1 : (S₂ : Set K) ∪ {((s₂' : K))⁻¹}
        = insert ((s₂' : K))⁻¹ (S₂ : Set K) := by
      rw [Set.insert_eq, Set.union_comm]
    have h2 : ((S₂ : Set K)) = (↑(Algebra.adjoin F (t₂ : Set K)) : Set K) :=
      congrArg (fun T : Subalgebra F K => (T : Set K)) ht₂.symm
    rw [h1, h2, Algebra.adjoin_insert_adjoin, Finset.coe_insert]
  have hT₂'T₁ : Algebra.adjoin F ((S₂ : Set K) ∪ {((s₂' : K))⁻¹})
      ≤ Algebra.adjoin F ((S₁ : Set K) ∪ {((s₁ : K))⁻¹}) := by
    rw [hunion]; exact hle₁
  -- 抽取：s₁ · (s₂′)ⁿ = t，t ∈ S₂
  obtain ⟨n, t, ht⟩ := fraction_extraction S₂ hs₂' (hS₁T₂' s₁.2)
  have ht'K : (s₂' : K) ≠ 0 := fun h => hs₂' ((Subalgebra.coe_eq_zero S₂).mp h)
  have htK : (t : K) ≠ 0 := by
    rw [← ht]
    exact mul_ne_zero (fun h => hs₁ ((Subalgebra.coe_eq_zero S₁).mp h))
      (pow_ne_zero n ht'K)
  have ht0 : t ≠ 0 := fun h => htK ((Subalgebra.coe_eq_zero S₂).mpr h)
  have hA : (s₂' : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ ht'K
  have hpow : (s₁ : K) * (s₂' : K) ^ (n + 1) = (((s₂' * t) : S₂) : K) := by
    have h1 : (s₁ : K) * (s₂' : K) ^ (n + 1)
        = ((s₁ : K) * (s₂' : K) ^ n) * (s₂' : K) := by
      rw [pow_succ]; ring
    rw [h1, ht, Subalgebra.coe_mul]
    exact mul_comm (t : K) (s₂' : K)
  -- 四个域恒等式（把 s₁、s₂′、t、(s₂′t) 的逆互相表出）
  have hs₁eq : (s₁ : K) = (((s₂' * t) : S₂) : K) * ((s₂' : K) ^ (n + 1))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hA]
    exact hpow
  have hs₁inv : (s₁ : K)⁻¹ = (s₂' : K) ^ (n + 1) * (((s₂' * t) : S₂) : K)⁻¹ := by
    rw [hs₁eq, mul_inv, inv_inv]
    exact mul_comm _ _
  have h2 : (s₂' : K)⁻¹ = (t : K) * (((s₂' * t) : S₂) : K)⁻¹ := by
    rw [Subalgebra.coe_mul, mul_inv, ← mul_assoc, mul_comm (t : K) ((s₂' : K)⁻¹),
      mul_assoc, mul_inv_cancel₀ htK, mul_one]
  have ht_inv : (t : K)⁻¹ = (s₁ : K)⁻¹ * ((s₂' : K)⁻¹) ^ n := by
    rw [← ht, mul_inv, ← inv_pow]
  have hz_inv : (((s₂' * t) : S₂) : K)⁻¹
      = (s₂' : K)⁻¹ * ((s₁ : K)⁻¹ * ((s₂' : K)⁻¹) ^ n) := by
    rw [Subalgebra.coe_mul, mul_inv, ht_inv]
  -- 两向包含
  have hT₂'le : Algebra.adjoin F ((S₂ : Set K) ∪ {((s₂' : K))⁻¹})
      ≤ Algebra.adjoin F ((S₂ : Set K) ∪ {(((s₂' * t) : S₂) : K)⁻¹}) := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rcases hy with hyS | hys
    · exact Algebra.subset_adjoin (Set.mem_union_left _ hyS)
    · rw [Set.mem_singleton_iff.mp hys, h2]
      exact mul_mem (Algebra.subset_adjoin (Set.mem_union_left _ t.2))
        (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _)))
  have hS₁le : S₁ ≤ Algebra.adjoin F ((S₂ : Set K) ∪ {(((s₂' * t) : S₂) : K)⁻¹}) :=
    hS₁T₂'.trans hT₂'le
  have hS₂'T₁ : S₂ ≤ Algebra.adjoin F ((S₁ : Set K) ∪ {((s₁ : K))⁻¹}) :=
    fun z hz => hT₂'T₁ (Algebra.subset_adjoin (Set.mem_union_left _ hz))
  have h_s₂'inv_T₁ : ((s₂' : K))⁻¹ ∈
      Algebra.adjoin F ((S₁ : Set K) ∪ {((s₁ : K))⁻¹}) :=
    hT₂'T₁ (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _)))
  have h_s₁'inv_T₁ : ((s₁ : K))⁻¹ ∈
      Algebra.adjoin F ((S₁ : Set K) ∪ {((s₁ : K))⁻¹}) :=
    Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
  refine ⟨s₁, s₂' * t, hs₁, mul_ne_zero hs₂' ht0, le_antisymm ?_ ?_⟩
  · rw [Algebra.adjoin_le_iff]
    intro y hy
    rcases hy with hyS | hys
    · exact hS₁le hyS
    · rw [Set.mem_singleton_iff.mp hys, hs₁inv]
      exact mul_mem
        (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_union_left _ s₂'.2))
          (n + 1))
        (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _)))
  · rw [Algebra.adjoin_le_iff]
    intro y hy
    rcases hy with hyS | hys
    · exact hS₂'T₁ hyS
    · rw [Set.mem_singleton_iff.mp hys, hz_inv]
      exact mul_mem h_s₂'inv_T₁
        (mul_mem h_s₁'inv_T₁ (Subalgebra.pow_mem _ h_s₂'inv_T₁ n))

/-! ## 5. 非空洞探针（L1） -/

/-- 探针件：`↥(⊤ : Subalgebra F F)` 在 `F` 上有限型。 -/
theorem finiteType_top_self (F : Type u) [Field F] :
    Algebra.FiniteType F ↥(⊤ : Subalgebra F F) :=
  ⟨(Subalgebra.fg_top (⊤ : Subalgebra F F)).mpr
    ⟨{(1 : F)}, by
      rw [Finset.coe_singleton, Algebra.adjoin_singleton_one]
      exact le_antisymm bot_le fun x _ => Algebra.mem_bot.mpr ⟨x, rfl⟩⟩⟩

/-- 探针件：`↥(⊤ : Subalgebra F F)` 以 `F` 为分式域（`q = id` 沿双射）。 -/
theorem isFractionRing_top_self (F : Type u) [Field F] :
    IsFractionRing ↥(⊤ : Subalgebra F F) F :=
  IsLocalization.of_le_isUnit_of_bijective
    (M := nonZeroDivisors ↥(⊤ : Subalgebra F F))
    (by
      rintro y ⟨n, hn, rfl⟩
      refine IsUnit.mk0 _ (fun h0 => one_ne_zero (hn.1 1 ?_))
      apply Subtype.ext
      simpa using h0)
    ⟨fun a b hab => Subtype.ext hab, fun x => ⟨⟨x, trivial⟩, rfl⟩⟩

/-- **端到端探针（L1）**：主定理在 `S₁ = S₂ = ⊤`（`K = F`）的实例非空洞——
假设类（有限型 + 分式域）由两条探针件满足，结论显式给出。 -/
theorem swan_localization_common_self (F : Type u) [Field F] :
    ∃ (s₁ s₂ : ↥(⊤ : Subalgebra F F)), s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      Algebra.adjoin F (((⊤ : Subalgebra F F) : Set F) ∪ {((s₁ : F))⁻¹})
        = Algebra.adjoin F (((⊤ : Subalgebra F F) : Set F) ∪ {((s₂ : F))⁻¹}) :=
  @swan_localization_common F F _ _ _ (⊤ : Subalgebra F F) (⊤ : Subalgebra F F)
    (finiteType_top_self F) (finiteType_top_self F)
    (isFractionRing_top_self F) (isFractionRing_top_self F)

/-! ## 6. 公理闸门 -/

#print axioms exists_finset_adjoin_eq
#print axioms exists_localization_ge_adjoin
#print axioms fraction_extraction
#print axioms swan_localization_common
#print axioms finiteType_top_self
#print axioms isFractionRing_top_self
#print axioms swan_localization_common_self

end ABGV52
