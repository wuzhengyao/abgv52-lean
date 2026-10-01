/-
  ABGV-5.2 —— PC2 件：论文 `lem:perm-char`（特征标公式）与其「唯一性半」的反例

  论文 `lem:perm-char`（`raw/ABGV-5.2-resolution.tex:436–455`）有两半：
    (a) 置换模 ℚ[H/K] 的特征标 = 不动点数：= [H:K]（g ∈ K）／0（g ∉ K）；
    (b) 「H 交换时，置换格 P ≅ ⊕_K m_K·ℤ[H/K] 的重数 m_K 由 P ⊗ ℚ 的特征标唯一决定」。

  本件
  ====
    §A 形式化 (a)（对 H = C₃×C₃；此时各子群自动正规——**注意**：(a) 的一般群断言
       实需 K 正规，见报告；论文行文未点明）。
    §B **机器核反例推翻 (b)**：两个显式 H-集
          X₁ = 3 个不动点 ⊔ 正则（重数：⊤ 型 3、⊥ 型 1），
          X₂ = 四个 C₃-型轨道（重数：C₃ 型各 1），
        **字符函数逐元素相等**（∀ g，#Fix 相同——两栏都是 12（g=1）／3（g≠1）），
        但**平凡轨道重数 3 ≠ 0** ⟹ 重数不被特征标决定。
      另：X₁ ≇ X₂（H-不动点数不同）——同字符的置换模可以来自不同 H-集。
      附注（报告详述）：(b) 所引 Curtis-Reiner Example 10.4 实为「诱导模 ≅ 置换模」的
      识别，不含唯一性断言——**引文亦不成立**。

  与主线的关系（诚实边界）
  ====================
    `PC_ABGV52`（lem:perm-class）**不依赖 (b)**：论文自己的论证在非负整数性下解方程即
    锁唯一解（本库路线更绕开方程直接计数），故 (b) 为假**不影响论文主线**；但论文由 (b)
    处引出的两句行文（lem:perm-char 第二半 ＋ lem:perm-class 证明首段）需要修正。
-/
import ABGV52.PC_ABGV52

namespace ABGV52.PC

/-! ## §A 特征标公式（第一半；H 交换 ⟹ 子群正规，两分支公式成立） -/

/-- **商集 H/K 上的不动点计数**：`g` 在 `H ⧸ K` 上的不动点数
= `[H:K]`（`g ∈ K`）／`0`（`g ∉ K`）。 -/
theorem fixCount_quotient (K : Subgroup H) [DecidablePred (· ∈ K)] (g : H) :
    Nat.card (MulAction.fixedBy (H ⧸ K) g)
      = if g ∈ K then Nat.card (H ⧸ K) else 0 := by
  have key : ∀ h : H, (g * h)⁻¹ * h ∈ K ↔ g ∈ K := by
    intro h
    have h1 : (g * h)⁻¹ * h = g⁻¹ := by
      rw [mul_inv_rev]
      calc h⁻¹ * g⁻¹ * h = g⁻¹ * (h⁻¹ * h) := by rw [mul_comm h⁻¹ g⁻¹, mul_assoc]
        _ = g⁻¹ := by rw [inv_mul_cancel, mul_one]
    rw [h1, Subgroup.inv_mem_iff]
  by_cases hg : g ∈ K
  · rw [if_pos hg]
    have hall : MulAction.fixedBy (H ⧸ K) g = Set.univ := by
      ext x
      rw [MulAction.mem_fixedBy]
      refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
      induction x using Quotient.inductionOn with
      | h h =>
        change g • (QuotientGroup.mk h : H ⧸ K) = QuotientGroup.mk h
        rw [show g • (QuotientGroup.mk h : H ⧸ K)
              = QuotientGroup.mk (g * h) from rfl]
        exact QuotientGroup.eq.mpr ((key h).mpr hg)
    rw [hall]
    exact Nat.card_congr (Equiv.Set.univ _)
  · rw [if_neg hg]
    have hempty : MulAction.fixedBy (H ⧸ K) g = ∅ := by
      ext x
      rw [Set.mem_empty_iff_false, iff_false, MulAction.mem_fixedBy]
      induction x using Quotient.inductionOn with
      | h h =>
        intro heq
        have h2 := QuotientGroup.eq.mp heq
        exact hg ((key h).mp h2)
    rw [hempty]
    simp

/-- 与论文 `[H:K]` 对齐：`Nat.card (H ⧸ K) = K.index`。 -/
theorem card_quotient_eq_index (K : Subgroup H) : Nat.card (H ⧸ K) = K.index :=
  (Subgroup.index_eq_card K).symm

/-- **特征标公式（迹形式）**：`ρ(g)` 在 `ℚ[H/K]` 上的迹 = 不动点数 = `[H:K]`／`0`。 -/
theorem trace_quotient (K : Subgroup H) [DecidablePred (· ∈ K)] (g : H) :
    LinearMap.trace ℚ (MonoidAlgebra ℚ (H ⧸ K)) ((Rep.ofMulAction ℚ H (H ⧸ K)).ρ g)
      = if g ∈ K then (K.index : ℚ) else 0 := by
  haveI : Fintype (H ⧸ K) := Fintype.ofFinite _
  haveI : DecidableEq (H ⧸ K) := Classical.decEq _
  rw [trace_rho (H ⧸ K) g]
  have hbridge : (Finset.univ.filter (fun x : H ⧸ K => g • x = x)).card
      = Nat.card (MulAction.fixedBy (H ⧸ K) g) := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  rw [hbridge, fixCount_quotient K g]
  split
  · rw [card_quotient_eq_index]
  · simp

/-! ## §B 「唯一性半」的反例（机器核） -/

/-- 反例用 H-集 X₁：3 个不动点 ⊔ 正则（H 自由左乘）。 -/
abbrev X1 : Type := Fin 3 ⊕ H

noncomputable instance instMulActionX1 : MulAction H X1 where
  smul g x := match x with
    | Sum.inl i => Sum.inl i
    | Sum.inr h => Sum.inr (g * h)
  one_smul := by
    intro x
    cases x with
    | inl i => rfl
    | inr h =>
      show Sum.inr ((1 : H) * h) = Sum.inr h
      rw [one_mul]
  mul_smul := by
    intro a b x
    cases x with
    | inl i => rfl
    | inr h =>
      show Sum.inr ((a * b) * h) = Sum.inr (a * (b * h))
      rw [mul_assoc]

/-- 反例用 H-集 X₂：四个 C₃-型轨道（`ZMod 3` 平移；
φ₀ = y、φ₁ = x、φ₂ = y − x、φ₃ = y + x，其中 `x = toAdd g.1`、`y = toAdd g.2`）。 -/
abbrev X2 : Type := ZMod 3 × Fin 4

noncomputable def phi (g : H) : Fin 4 → ZMod 3 :=
  ![Multiplicative.toAdd g.2, Multiplicative.toAdd g.1,
    Multiplicative.toAdd g.2 - Multiplicative.toAdd g.1,
    Multiplicative.toAdd g.2 + Multiplicative.toAdd g.1]

lemma phi_add (a b : H) : phi (a * b) = phi a + phi b := by
  funext i
  fin_cases i <;>
    simp [phi, toAdd_mul] <;>
    ring

lemma phi_one : phi (1 : H) = 0 := by
  funext i
  fin_cases i <;> simp [phi]

noncomputable instance instMulActionX2 : MulAction H X2 where
  smul g p := (p.1 + phi g p.2, p.2)
  one_smul := by
    intro p
    show (p.1 + phi (1 : H) p.2, p.2) = p
    rw [phi_one, Pi.zero_apply, add_zero]
  mul_smul := by
    intro a b p
    show (p.1 + phi (a * b) p.2, p.2) = (p.1 + phi b p.2 + phi a p.2, p.2)
    rw [phi_add, Pi.add_apply]
    congr 1
    abel

/-- **字符相同**：X₁ 与 X₂ 的不动点数函数逐元素相等（＝「特征标」相同）。 -/
theorem char_eq (g : H) :
    Fintype.card (MulAction.fixedBy X1 g) = Fintype.card (MulAction.fixedBy X2 g) := by
  fin_cases g <;> decide

/-- X₁ 的 H-不动点数 = 3（3 个单点）。 -/
theorem X1_triv_fixed : Fintype.card {x : X1 // ∀ h : H, h • x = x} = 3 := by
  decide

/-- X₂ 的 H-不动点数 = 0（四个 C₃-型轨道无不动点）。 -/
theorem X2_triv_fixed : Fintype.card {x : X2 // ∀ h : H, h • x = x} = 0 := by
  decide

/-- **重数不同**：两集的（平凡轨道）重数 3 ≠ 0。 -/
theorem mult_ne :
    Fintype.card {x : X1 // ∀ h : H, h • x = x}
      ≠ Fintype.card {x : X2 // ∀ h : H, h • x = x} := by
  rw [X1_triv_fixed, X2_triv_fixed]
  decide

/-- **X₁ ≇ X₂ 作为 H-集**（H-不动点数不同）。 -/
theorem not_iso : ¬ ∃ e : X1 ≃ X2, ∀ (g : H) (x : X1), e (g • x) = g • e x := by
  rintro ⟨e, he⟩
  have hcard : Fintype.card {x : X1 // ∀ h : H, h • x = x}
      = Fintype.card {x : X2 // ∀ h : H, h • x = x} :=
    Fintype.card_congr (e.subtypeEquiv (fun a => ⟨
      fun ha h => by rw [← he h a, ha h],
      fun ha h => e.injective (by rw [he h a, ha h])⟩))
  rw [X1_triv_fixed, X2_triv_fixed] at hcard
  exact absurd hcard (by decide)

/-- ℚ-模层面：两个置换模的特征标（迹）逐元素相等。 -/
theorem trace_eq_X1_X2 (g : H) :
    LinearMap.trace ℚ (MonoidAlgebra ℚ X1) ((Rep.ofMulAction ℚ H X1).ρ g)
      = LinearMap.trace ℚ (MonoidAlgebra ℚ X2) ((Rep.ofMulAction ℚ H X2).ρ g) := by
  rw [trace_rho X1 g, trace_rho X2 g]
  have b1 : (Finset.univ.filter (fun x : X1 => g • x = x)).card
      = Fintype.card (MulAction.fixedBy X1 g) :=
    (Fintype.card_subtype _).symm
  have b2 : (Finset.univ.filter (fun x : X2 => g • x = x)).card
      = Fintype.card (MulAction.fixedBy X2 g) :=
    (Fintype.card_subtype _).symm
  rw [b1, b2]
  exact_mod_cast char_eq g

/-- **反例（`lem:perm-char` 第二半为假）**：同字符、异重数。 -/
theorem permChar_uniqueness_false :
    (∀ g : H, Fintype.card (MulAction.fixedBy X1 g)
      = Fintype.card (MulAction.fixedBy X2 g))
    ∧ Fintype.card {x : X1 // ∀ h : H, h • x = x}
      ≠ Fintype.card {x : X2 // ∀ h : H, h • x = x} :=
  ⟨char_eq, mult_ne⟩

/-! ## 公理闸门 -/

#print axioms fixCount_quotient
#print axioms trace_quotient
#print axioms char_eq
#print axioms mult_ne
#print axioms not_iso
#print axioms trace_eq_X1_X2
#print axioms permChar_uniqueness_false

end ABGV52.PC
