/-
  ABGV-5.2 —— **命名假设的反例**（A 档，2026-10-11）

  **背景**：`FlasqueResolutionHyp`（「∀ 模 `M`，存在 flasque 消解」）把 `M` 取成
  **任意** `ℤ[G]`-模；而消解要求 `M ↪ P`（`injective_iota`），`P` 置换格
  ⟹ `P` 作为 `ℤ`-模**无挠**（本件用 `Module.IsTorsionFree` 直接取实例）。
  取 `M = ℤ/2`（挠）即得反例 ⟹ **该假设按现形为假** ✓。

  **结论**：论文真正用到的是**格（无挠）上**的受限形（见 `Flasque_ABGV52` 头注警示与
  主循环笔记 `[[proj-ABGV52-hypA-blockers]]`）。

  **无 sorry、无自造公理**；公理门见 §3。
-/
import ABGV52.Flasque_ABGV52

namespace ABGV52

open CategoryTheory CategoryTheory.Limits

/-! ## §1 核心：`ℤ/2` 不能单射进置换格 -/

/-- **`ℤ/2` 不能单射进置换格**（任意群 `G`；工程用的 `EM.IsPermutationLattice` 是 `G` 版 ✓）。
论证只用**加法**（避开 `smul` 的实例摩擦 ✗）：`1 + 1 = 0` 于 `ℤ/2` ⟹ `v + v = 0`；
沿置换模同构推到 `Q = ℤ[X]`（`Module.IsTorsionFree` 实例可直接合成 ✓）得 `v = 0`；
再回推 `1 = 0` 矛盾 ✓。 -/
theorem zmod_two_no_injective_into_perm (G : Type) [Group G]
    (P : Rep.{0, 0, 0} ℤ G) (hP : EM.IsPermutationLattice G P) :
    ¬ ∃ f : Rep.trivial ℤ G (ZMod 2) ⟶ P, Function.Injective f := by
  rintro ⟨f, hf⟩
  obtain ⟨X, hXf, hXa, ⟨e⟩⟩ := hP
  -- `1 + 1 = 0` 于 `ℤ/2`
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  -- 像点 `v := f 1` 满足 `v + v = 0`
  have hv : f.hom (1 : ZMod 2) + f.hom (1 : ZMod 2) = 0 := by
    rw [← map_add f.hom, htwo, map_zero]
  -- 推到置换模（无挠）
  have hw : e.hom.hom (f.hom (1 : ZMod 2)) + e.hom.hom (f.hom (1 : ZMod 2)) = 0 := by
    rw [← map_add e.hom.hom, hv, map_zero]
  have hw0 : e.hom.hom (f.hom (1 : ZMod 2)) = 0 := by
    have h2 : (2 : ℤ) • (e.hom.hom (f.hom (1 : ZMod 2))) = 0 := by
      rw [two_smul]; exact hw
    rcases (smul_eq_zero.mp h2) with h3 | h3
    · norm_num at h3
    · exact h3
  -- `e.hom.hom` 单射 ⟹ 回推 `f 1 = 0`
  have hv0 : f.hom (1 : ZMod 2) = 0 := by
    have h1 : e.inv.hom (e.hom.hom (f.hom (1 : ZMod 2))) = f.hom (1 : ZMod 2) := by
      have hcomp := congrArg (fun (g : P ⟶ P) => g.hom (f.hom (1 : ZMod 2))) e.hom_inv_id
      simpa using hcomp
    rw [hw0, map_zero] at h1
    exact h1.symm
  -- 与单射 `f` 及 `1 ≠ 0` 矛盾
  exact one_ne_zero (hf (by rw [hv0, map_zero]))

/-! ## §2 反例 (a)：`FlasqueResolutionHyp` 按现形为假 -/

/-- **`FlasqueResolutionHyp G` 为假**（任意群 `G`）：消解蕴含单射 `ℤ/2 ↪ P`（`P` 置换），
与 §1 矛盾 ✓。**旧接口名与类型逐字保留** ✗（本件只加反例，不改 `def`）。 -/
theorem not_flasqueResolutionHyp (G : Type) [Group G] [Fintype G] :
    ¬ FlasqueResolutionHyp G := by
  intro h
  obtain ⟨R⟩ := h (Rep.trivial ℤ G (ZMod 2))
  exact zmod_two_no_injective_into_perm G R.P R.perm ⟨R.iota, R.injective_iota⟩



attribute [local instance 1500] Rep.hV2

/-! ## §3 反例 (b) 的**半边**：`ℤ/2 ≁ ℤ`（挠 vs 无挠，**已证** ✓） -/


/-- 从 `ℤ/2`（平凡作用）到「无 2-挠」模的任何 `Rep` 态射都是 0 ✓（元素级，不涉双积分解）。 -/
theorem hom_zmodTwo_eq_zero_of_no_two_torsion {G : Type} [Group G] (N : Rep.{0,0,0} ℤ G)
    (hN : ∀ x : ↥N, x + x = 0 → x = 0) (f : Rep.trivial ℤ G (ZMod 2) ⟶ N) : f = 0 := by
  apply Rep.hom_ext
  ext x
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  have h2 : f.hom (1 : ZMod 2) + f.hom (1 : ZMod 2) = 0 := by
    rw [← map_add f.hom, htwo, map_zero]
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with hx | hx
  · rw [hx, map_zero]; rfl
  · rw [hx]; exact hN _ h2

/-- 置换模**无 2-挠** ✓（沿置换同构搬到 `ℤ[Y]` 再回推）。 -/
theorem perm_no_two_torsion {G : Type} [Group G] (Q : Rep.{0,0,0} ℤ G)
    (hQ : EM.IsPermutationLattice G Q) : ∀ x : ↥Q, x + x = 0 → x = 0 := by
  intro x hx
  obtain ⟨Y, hYf, hYa, ⟨eQ⟩⟩ := hQ
  have h1 : eQ.hom.hom x + eQ.hom.hom x = 0 := by
    rw [← map_add eQ.hom.hom, hx, map_zero]
  have h2 : eQ.hom.hom x = 0 := by
    have h3 : (2 : ℤ) • (eQ.hom.hom x) = 0 := by rw [two_smul]; exact h1
    rcases (smul_eq_zero.mp h3) with h4 | h4
    · norm_num at h4
    · exact h4
  have hb : eQ.inv.hom (eQ.hom.hom x) = x := by
    have hc := congrArg (fun (g : Q ⟶ Q) => g.hom x) eQ.hom_inv_id
    simpa using hc
  rw [h2, map_zero] at hb
  exact hb.symm

/-- **挠半边主定理** ✓：`ℤ/2`（平凡作用）与 `ℤ` 不相似。 -/
theorem zmodTwo_not_similar_int :
    ¬ IsSimilar PUnit (Rep.trivial ℤ PUnit (ZMod 2)) (Rep.trivial ℤ PUnit ℤ) := by
  rintro ⟨S₁, S₂, h₁, h₂, ⟨e⟩⟩
  let φ : Rep.trivial ℤ PUnit (ZMod 2) ⟶ (Rep.trivial ℤ PUnit ℤ) ⊞ S₂ :=
    (biprod.inl : Rep.trivial ℤ PUnit (ZMod 2) ⟶
      (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁) ≫ e.hom
  have hfst : φ ≫ (biprod.fst : (Rep.trivial ℤ PUnit ℤ) ⊞ S₂ ⟶ Rep.trivial ℤ PUnit ℤ) = 0 :=
    hom_zmodTwo_eq_zero_of_no_two_torsion (Rep.trivial ℤ PUnit ℤ)
      (fun x hx => add_self_eq_zero.mp hx)
      (φ ≫ (biprod.fst : (Rep.trivial ℤ PUnit ℤ) ⊞ S₂ ⟶ Rep.trivial ℤ PUnit ℤ))
  have hsnd : φ ≫ (biprod.snd : (Rep.trivial ℤ PUnit ℤ) ⊞ S₂ ⟶ S₂) = 0 :=
    hom_zmodTwo_eq_zero_of_no_two_torsion S₂ (perm_no_two_torsion S₂ h₂)
      (φ ≫ (biprod.snd : (Rep.trivial ℤ PUnit ℤ) ⊞ S₂ ⟶ S₂))
  have hφ : φ = 0 := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [hfst, zero_comp]
    · rw [hsnd, zero_comp]
  have hne : φ.hom (1 : ZMod 2) ≠ 0 := by
    intro h
    have hcomp : φ.hom (1 : ZMod 2) = e.hom.hom
        (((biprod.inl : Rep.trivial ℤ PUnit (ZMod 2) ⟶
          (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁)).hom (1 : ZMod 2)) := rfl
    have h1 : ((biprod.inl : Rep.trivial ℤ PUnit (ZMod 2) ⟶
        (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁)).hom (1 : ZMod 2) = 0 := by
      have hcc : e.inv.hom (e.hom.hom (((biprod.inl : Rep.trivial ℤ PUnit (ZMod 2) ⟶
          (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁)).hom (1 : ZMod 2)))
          = ((biprod.inl : Rep.trivial ℤ PUnit (ZMod 2) ⟶
          (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁)).hom (1 : ZMod 2) := by
        have hcid := congrArg (fun (g : (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁ ⟶
            (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁) =>
            g.hom (((biprod.inl : Rep.trivial ℤ PUnit (ZMod 2) ⟶
              (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁)).hom (1 : ZMod 2))) e.hom_inv_id
        simpa using hcid
      rw [← hcomp, h, map_zero] at hcc
      exact hcc.symm
    have h2 := congrArg (fun w => ((biprod.fst : (Rep.trivial ℤ PUnit (ZMod 2)) ⊞ S₁ ⟶
        Rep.trivial ℤ PUnit (ZMod 2))).hom w) h1
    -- `biprod.inl ≫ biprod.fst = 𝟙 X`（`biprod.inl_fst` ✓）⟹ `fst (inl 1) = 1`
    rw [← CategoryTheory.comp_apply,
      biprod.inl_fst (X := Rep.trivial ℤ PUnit (ZMod 2)) (Y := S₁)] at h2
    simp at h2
  rw [hφ] at hne
  exact hne rfl


/-! ## §4 登记的未闭合项（不假装证明 ✗）

**正例对照（未证）** ✗：`M = 0` 的合法消解（「无消解不是恒真读数」的对照）—— 卡点：
`Rep.{0,0,0} ℤ G` 在本版 mathlib 下**没有可直接用的 `Zero` 实例**（`0 : Rep ℤ G` 报
`failed to synthesize OfNat`）⟹ 需先构造零对象，或改用 `Rep.ofMulAction ℤ G PEmpty`
显式给出 ✓。

**格上受限形（未证）** ✗：`IsLattice M → Nonempty (FlasqueResolution G M)`（CTS77 §1 Lemme 3
的构造性证明：嵌入置换格 ＋ 对偶步 ＋ 归约）—— 见 [[proj-ABGV52-hypA-blockers]] §3。
-/

/-! ## §5 公理闸门 -/

#print axioms zmod_two_no_injective_into_perm
#print axioms not_flasqueResolutionHyp
#print axioms hom_zmodTwo_eq_zero_of_no_two_torsion
#print axioms perm_no_two_torsion
#print axioms zmodTwo_not_similar_int

end ABGV52
